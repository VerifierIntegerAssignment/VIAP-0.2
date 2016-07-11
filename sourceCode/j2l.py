# February 20, 2016
# February 29, 2016: 1. change axioms for if1 and if2 to make all axioms of the form x = ... 2. add last label as an output of translate0
# March 10 - April 27: a new translation for while-loop that parameterizes loop input variables and replaces smallest macros by inductive definition. Also a small correction to simplify()
# April 29: combining the two translations (c2l.py.old3 and c2l.py.old4): keep the old translation for program variables but use a new way to inductively define smallest macro: 
# N(x,y) = if C(x,y) then 0 else C(f(x),g(x)), where f and g is the new value of x and y, respectively, after one iteration
# in c2l.py.old4, f and g are the output functions for the body, here we parameterize f and g first, and use f(1,x) and g(1,y) to replace f(x) and g(y), respectively
# A translator from Java to FOL in python 
# update on May 21 ,2016 remaned function expr to expres by Pritom Rajkhowa
#example run: translate1(fact,vfact,1) or translate1(fact,vfact,2)

"""
Assumptions:
1. Program variables:
  - can be any word \w+
  - cannot be _x\d*, _n\d*, _N\d*,_y\d* 
    (these are reserved for general variables,
    natural number variables, and smallest macro constants
    in our axioms)
  - for a variable, its temporary variants are constructed 
    by adding to it TEMP+number
    and its output values after a labeled statement are 
    constructed by adding to it LABEL+number.
    (Currently, TEMP is empty and LABEL is '_'.) 
    This menas that if V is a variable, then
    V+TEMP+\d+ and V+LABEL+\d+ are not allowed to be variables 
    (right now it means that
    V1,V2,... and V_1,V_2,... cannot be variables).
  - smallest is a reserved word so cannot be a variable
"""

import re
import random
#add by Pritom Rajkhowa
import wolframalpha
import sys
import plyj.parser
import plyj.model as m
import subprocess
from sympy import *
import regex
import os
import copy
import time
import datetime
from pyparsing import *
from sympy.core.relational import Relational
ParserElement.enablePackrat()

# base language (non dynamic, not changed by the program)
TIMEOUT=60000
_base = ['=','==','!=','<','<=','>','>=','*','**','!','+','-','/', '%', 'ite', 'and', 'or', 'not', 'implies', 'all', 'some', 'null']
_infix_op = ['=','==','!=','<','<=','>','>=','*','**','+','-','/', '%', 'implies']
def isvariable(x):
    if x.startswith('_x') or  x.startswith('_y') or  x.startswith('_n'):
        return True
    else:
        return False


current_milli_time = lambda: int(round(time.time() * 1000))

"""
#Get timestap
"""

def getTimeStamp():
	ts = time.time()
	st = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
	return "\n***********************\n"+str(st)+"\n***********************\n"




"""
Temporary function names are constructed as: 
variable-name + TEMP + TC
Output function names are: 
variable-name + LABEL + LC 
for those with label. for those without label: 
variable-name + OUT + LC for those with label.
 TC: TempCount, a global counter for naming temporary variables
 LC: LoopCount, a global counter for naming loop constants and variables
"""

#OUT='Z' #so don't name variables xZ, yZ...
OUT='1' #so don't name variables x1, y1...
#TEMP = 'T' #so if x is a variable, then don't name variables xT, 
TEMP = '' #so if x is a variable, then don't name variables x2,x3,... (temp starts at 2)
LABEL = '_' #so if x is a variable, then don't name variables x_1,x_2, 
TC = 1  # for generating temporary functions to yield xt1,xt2,...
LC = 0  # for generating smallest macro constants in a loop _N1, _N2,... as well as
               # natural number variables _n1,_n2,...
"""
 Expressions: (f e1 ... ek) is represented as [f,e1,...,ek].
 Example: a+1 is ['+', ['a'],['1']]; constant a is ['a']; 
 sum(i+1,j) is ['sum', ['+', ['i'], ['1']], ['j']]
"""

#constructor: functor - a string like '+', '*', 'and', 
# or constants like '1', 'x'; args - a list of expres
def expres(functor,args=[]):
    return [functor]+args

#accessor
def expr_op(e):
    return e[0]
def expr_args(e):
    return e[1:]

#prefix printing
def expr2string(e):
    if len(e)==1:
        return e[0]
    else:
        return '(' + e[0] +' '+ ' '.join(list(expr2string(x) for x in e[1:]))+ ')'

#normal infix printing
def expr2string1(e):
    args=expr_args(e)
    
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2string1(args[0])
            else:
                return '('+ ' '+op+' '.join(list(expr2string1(x) for x in args))+ ')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2string1(args[0])
        elif op=='implies' and len(args)==2:
            return expr2string1(args[0])+ ' -> '+expr2string1(args[1])
        elif op in _infix_op and len(args)==2:
            return '(' + expr2string1(args[0])+ op+expr2string1(args[1])+')'
        else:
            return op +'('+ ','.join(list(trim_p(expr2string1(x)) for x in args))+ ')'
           

#expression to z3 constraint
def expr2z3(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2z3(args[0],var_cstr_map)
            else:
                return '('+ ' '+op+' '.join(list(expr2z3(x,var_cstr_map) for x in args))+ ')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2z3(args[0],var_cstr_map)
        elif op=='implies' and len(args)==2:
            
            if len(var_cstr_map)==0:
            	return 'Implies('+expr2z3(args[0],var_cstr_map)+ ','+expr2z3(args[1],var_cstr_map)+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			list_constrn="And("+expr2z3(args[0],var_cstr_map)+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	return 'Implies('+list_constrn+ ','+expr2z3(args[1],var_cstr_map)+')'
        elif op in _infix_op and len(args)==2:
            return '(' + expr2z3(args[0],var_cstr_map)+ op+expr2z3(args[1],var_cstr_map)+')'
        else:
            return op +'('+ ','.join(list(trim_p(expr2z3(x,var_cstr_map)) for x in args))+ ')'


#get variable
def expr2varlist(e,variable_list):
    args=expr_args(e)    
    op=expr_op(e)
    if len(args)==0:
    	if '_n' not in op and is_number(op)==False:
    		variable_list.append(op)
    else:
        if op=='and' or op=='or':
            if len(args)==1:
               expr2varlist(args[0],variable_list)
            else:
            	expr2varlist(x)
        elif op=='not' and len(args)==1:
            expr2varlist(args[0],variable_list)
        elif op=='implies' and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        elif op in _infix_op and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        else:
        	expr2varlist(x,variable_list)



#return the list of functors in an expression that are not in the base language

def expr_func(e): #e - expres
    ret = []
    f = expr_op(e)
    if not (f in _base or isvariable(f) or is_number(f)):
        ret.append(f)
    for e1 in expr_args(e):
        ret = ret + expr_func(e1)
    return ret

#substitution of functors: in e, replace functor n1 by n2
def expr_sub(e,n1,n2): # e - expres; n1,n2 - strings
    e1=list(expr_sub(x,n1,n2) for x in e[1:])
    if e[0]==n1:
        return [n2]+e1
    else:
        return e[:1]+e1

#substitution of functors in a set: in e, for all x in v1 but not in v2, replace x+n1 by x+n2
def expr_sub_set(e,n1,n2,v1,v2): #e - expres; n1,n2 - strings, v1, v2 - sets of strings
    e1 = list(expr_sub_set(e2,n1,n2,v1,v2) for e2 in e[1:])
    if e[0].endswith(n1):
        x = e[0][:len(e[0])-len(n1)]
        if (x in v1) and (not x in v2):
            return [x+n2]+e1
        else:
            return e[:1]+e1
    else:
        return e[:1]+e1

# expr_replace(e,e1,e2): replace all subterm e1 in e by e2

def expr_replace(e,e1,e2): #e,e1,e2: expres
    if e==e1:
        return e2
    else:
        return e[:1]+list(expr_replace(x,e1,e2) for x in expr_args(e))

# expr_sub_dict(e,d): d is a dictonary of substitutions: functor 'f' to e1=d['f'] so that in e, each f term f(t1,...,tk) is replaced by e1(_x1/t1,...,_xk/tk)

def expr_sub_dict(e,d):
    args = expr_args(e)
    args1 = list(expr_sub_dict(x,d) for x in args)
    if expr_op(e) in d:
        return expr_sub_var_list(d[expr_op(e)],list(expres('_x'+str(i+1)) for i in range(len(args))),args1)
    else:
        return expres(expr_op(e),args1)

# expr_sub_var_list(e,l1,l2): in e, replace all terms in l1 by the corresponding terms in l2

def expr_sub_var_list(e,l1,l2): #e: expres, l1,l2: lists of the same length of expres
    for i,x in enumerate(l1):
        if e==x:
            return l2[i]
    return e[:1]+list(expr_sub_var_list(y,l1,l2) for y in expr_args(e))


# compute E[n] extend(e,n,excl). n is an expres like ['_n1'], excl is a container of strings that are not to be extended
def extend(e,n,excl):
    op = expr_op(e)
    x = [n] if not (op in _base or isvariable(e[0]) or is_number(e[0]) or op in excl)  else []
    return expres(op, list(extend(e1,n,excl) for e1 in expr_args(e)) + x)

#A dictionary of dependencies para is such that, if x is an input variable, then para[x] is a list whose first element is 1 and the second element is the variable's parameter name; otherwise, para[x] is the list of input variables that x is depended on. 
#example: para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'], ['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function depending on X and Y whose corresponding parameters are '_y1' and '_y2', respectively.
#So after parameterization, X11(a,X) will become X11(a,_y1,_y1,_y2)

def parameterize_expr(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return para[e[0]][1]+list(parameterize_expr(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expr(x,para) for x in e[1:])+para[e[0]][1]
    else:
        return e[:1]+list(parameterize_expr(x,para) for x in e[1:])


#parameterize non-input functions then restore the input variables to its name
#given above para, X11(a,X) will become X11(a,X,X,Y), assuming that _y2 corresponds to Y

def parameterize_expr_sub(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return [e[0]]+list(parameterize_expr_sub(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expr_sub(x,para) for x in e[1:])+para[e[0]][2]
    else:
        return e[:1]+list(parameterize_expr_sub(x,para) for x in e[1:])


def is_number(s):
    try:
        float(s) # for int, long and float
    except ValueError:
        try:
            complex(s) # for complex
        except ValueError:
            return False
    return True

"""
 Formulas:
 1. equations f(x) = e: ['e',e1,e2], 
    where e1 is expression for f(x) and e2 for e
 2. inductive definition:
 - base case f(x1,...,xk,0,...,xm)=e: ['i0',k,e1,e2] 
   where e1 is Expr for f(x1,...,xk,0,...,xm) and e2 the Expr for e
 - inductive case f(x1,...,xk,n+1,...,xm)=e: ['i1',k,'n',e1,e2] 
    where e1 is Expr for f(x1,...,xk,n+1,...,xm) and e2 the Expr for e
 3. inductive definition for functions that return natural numbers 
    (like N in smallest macro):
 - base case f(x) = 0 iff C: ['d0',e,c] 
   where e is the Expr for f(x) and c an expression for condition C
 - inductive case f(x) = n+1 iff C(n): ['d1','n',e,c] 
   where e is the Expr for f(x) and c an Expr for condition C
 4. any other axioms: A: ['a',e], where e is the Expr for A

 Examples: a' = a+1: ['e', ['a\''], ['+',['a'],['1']]]
 N(x) = 0 if x<I else N(x-1)+1 is divided into two axioms:
 N(x) = 0 iff x<I:  
 ['d0', ['N',['x']], ['<', ['x'],['I']]] and
 N(x) = n+1 iff n=N(x-1): 
 ['d1','n', ['N',['x']], ['=',['n'], ['N', ['-', ['x'],['1']]]]]
"""

# constructors
def wff_e(e1,e2): #e1,e2: expres
    return ['e',e1,e2]

def wff_i0(k,e1,e2): #k: int; e1,e2: expres
    return ['i0',k,e1,e2]

def wff_i1(k,v,e1,e2): #k: int; v: string; e1,e2: expres
    return ['i1',k,v,e1,e2]

def wff_d0(e,c): #e: expr; c: expres
    return ['d0',e,c]

def wff_d1(v,e,c): #v: string, e and c: expres
    return ['d1',v,e,c]

def wff_s0(e): #e: expres
    return ['s0',e]

def wff_s1(e): #e: expres
    return ['s1',e]

def wff_a(e): #e: expres
    return ['a',e]

#print in prefix notation
def wff2string(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            return '(= '+expr2string(w[-2])+' '+expr2string(w[-1]) +')'
        elif w[0] == 'd0':
            return '(iff (= '+expr2string(w[1])+' 0) '+ expr2string(w[2])+')'
        elif w[0] == 'd1':
            return '(iff (= '+expr2string(w[2])+' (+ '+w[1]+' 1)) '+expr2string(w[3])+')'
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            return expr2string(w[1])

#print in normal infix notation
def wff2string1(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            return expr2string1(w[-2])+' = '+ expr2string1(w[-1])
        elif w[0] == 'd0':
            return expr2string1(w[1])+'=0 <=> '+ expr2string1(w[2])
        elif w[0] == 'd1':
            return expr2string1(w[2])+'='+w[1]+'+1 <=> '+expr2string1(w[3])
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' :
            return expr2string1(w[1])
            
#convert wff to z3 constraint
def wff2z3(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            lhs=expr2z3(w[-2],var_cstr_map)
            rhs=expr2z3(w[-1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
                else:
                	return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[1],var_cstr_map)
            rhs=expr2z3(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))"
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(w[1]+'+1'))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))"
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if 'Implies' in expression:
                arg_list=extract_args(expression)
                constr=simplify(arg_list[0])
                axms=str(constr).split('<')
                axms[0]=axms[0].strip()
                axms[1]=axms[1].strip()
                var_cstr_map_mod={}
                for x in var_cstr_map.keys():
                    if x!=axms[0]:
                        var_cstr_map_mod[x]=var_cstr_map[x]
                list_var_str=qualifier_list(var_cstr_map_mod.keys())
                list_cstr_str=cstr_list(var_cstr_map_mod.values())
                arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                if list_var_str is not None and list_cstr_str is not None:
                    return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                    #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                else:
                    return arg_list[1]
            else:
                return None
        else:
            return expression

  

#convert wff to z3 constraint
def wff2z3Stronger(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            lhs=expr2z3(w[-2],var_cstr_map)
            rhs=expr2z3(w[-1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
                else:
                	return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[1],var_cstr_map)
            rhs=expr2z3(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))"
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(w[1]+'+1'))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))"
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str_new=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str_new=cstr_list(var_cstr_map_mod.values())
                    old_arg_list=arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        equations.append('ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))')
                        return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        equations.append(arg_list[1])
                        return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'

        else:
            return expression





#convert wff to z3 constraint
def wff2z3Ins(w,vm):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            lhs=expr2z3(w[-2],var_cstr_map)
            rhs=expr2z3(w[-1],var_cstr_map)
            for x in vm.keys():
            	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
            for x in vm:
            	lhs=lhs.replace(x,vm[x])
            	rhs=rhs.replace(x,vm[x])
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
                else:
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[1],var_cstr_map)
            rhs=expr2z3(w[2],var_cstr_map)
            for x in vm.keys():
	    	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
            for x in vm:
	    	lhs=lhs.replace(x,vm[x])
            	rhs=rhs.replace(x,vm[x])
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))"
                #return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            for x in vm.keys():
	    	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            for x in vm:
	    	lhs=lhs.replace(x,vm[x])
            	rhs=rhs.replace(x,vm[x])
            lhs=convert_pow_op_fun(simplify_expand_sympy(w[1]+'+1'))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))"
                #return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
	    for x in vm.keys():
	    	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
	    for x in vm:
	    	expression=expression.replace(x,vm[x])
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    return 'ForAll(['+list_var_str+'],Implies('+'And('+arg_list[0]+','+list_cstr_str+'),'+arg_list[1]+'))'
                    #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
            else:
                return expression



#convert wff to z3 constraint
def wff2z3InsExpand(w,vm):
	
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            equations=[]
            lhs=expr2z3(w[-2],var_cstr_map)
            rhs=expr2z3(w[-1],var_cstr_map)
            lhs_org=lhs
            rhs_org=rhs
            for x in vm.keys():
            	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
            for x in vm:
            	lhs=lhs.replace(x,vm[x])
            	rhs=rhs.replace(x,vm[x])
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	#return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
                	equations.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))") 
			if is_number(str(vm[x]))==True:
				for i in range(0,int(vm[x])):
					lhs1=lhs_org.replace(x,str(i))
					rhs1=rhs_org.replace(x,str(i))         	
            				equations.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs1+' == '+ rhs1+"))")  
                	return equations
                else:
                  	equations.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))") 
                	return equations
            else:
            	if w[0] == 'i1':
                	equations.append(lhs+' == '+ rhs)
                	if is_number(str(vm[x]))==True:
            			for i in range(0,int(vm[x])):
            				lhs1=lhs_org.replace(x,str(i))
            				rhs1=rhs_org.replace(x,str(i))         	
            				equations.append(lhs1+' == '+ rhs1)            		 
                	return equations
                else:
                	equations.append(lhs+' == '+ rhs) 
                	return equations
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
            equations=[]
	    lhs=expr2z3(w[1],var_cstr_map)
            rhs=expr2z3(w[2],var_cstr_map)
            for x in vm.keys():
	    	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
            for x in vm:
	    	lhs=lhs.replace(x,vm[x])
            	rhs=rhs.replace(x,vm[x])
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))"
                #return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
                equations.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))")
                return equations
            else:
            	equations.append(lhs+'=0 == '+ rhs)
                return equations
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
            equations=[]
	    lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            for x in vm.keys():
	    	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            for x in vm:
	    	lhs=lhs.replace(x,vm[x])
            	rhs=rhs.replace(x,vm[x])
            lhs=convert_pow_op_fun(simplify_expand_sympy(w[1]+'+1'))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))"
                equations.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))")
                return equations
            else:
                equations.append(lhs+' == '+rhs)
                return equations
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3(w[1],var_cstr_map)
	    for x in vm.keys():
	    	if x in var_cstr_map.keys():
            		del var_cstr_map[x]
	    for x in vm:
	    	expression=expression.replace(x,vm[x])
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    #return 'ForAll(['+list_var_str+'],Implies('+'And('+arg_list[0]+','+list_cstr_str+'),'+arg_list[1]+'))'
                    #'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    equations.append('ForAll(['+list_var_str+'],Implies('+'And('+arg_list[0]+','+list_cstr_str+'),'+arg_list[1]+'))')
                    return equations
                else:
                    #return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
                    equations.append('ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))')
                    return equations
                   
            else:
            	equations=[]
            	equations.append(expression)
                return equations



#convert wff to z3 constraint
def wff2z3SimpleSmall(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            lhs=expr2z3(w[-2],var_cstr_map)
            rhs=expr2z3(w[-1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	#return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
                else:
                	return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[1],var_cstr_map)
            rhs=expr2z3(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+'=0 == '+ rhs+"))"
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3(w[2],var_cstr_map)
            rhs=expr2z3(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=convert_pow_op_fun(simplify_expand_sympy(w[1]+'+1'))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                #return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+rhs+"))"
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
	    expression=expr2z3(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if list_var_str is not None and list_cstr_str is not None:
                if 'Implies' in expression:
                    arg_list=extract_args(expression)
                    constr=simplify(arg_list[0])
                    axms=str(constr).split('<')
                    axms[0]=axms[0].strip()
                    axms[1]=axms[1].strip()
                    var_cstr_map_mod={}
                    for x in var_cstr_map.keys():
                        if x!=axms[0]:
                            var_cstr_map_mod[x]=var_cstr_map[x]
                    list_var_str=qualifier_list(var_cstr_map_mod.keys())
                    list_cstr_str=cstr_list(var_cstr_map_mod.values())
                    arg_list[1]='Or('+axms[1]+'==0,'+arg_list[1].replace(axms[0],'('+axms[1]+'-1)')+')'
                    if list_var_str is not None and list_cstr_str is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies('+str(list_cstr_str)+','+arg_list[1]+'))'
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'

        else:
            return expression




#print in normal infix notation
def wff2subslist(w):
        if w[0] == 'e':
            return expr2string1(w[-2]),expr2string1(w[-1])
 


#construct constraints for qualified variables
        
def qualifier_list(list_var):
    if len(list_var)==0:
        return None;
    else:
        var=list_var[-1]
        del list_var[-1]
        list_var_str=qualifier_list(list_var)
        if list_var_str is None:
            return var
        else:
            return var+","+list_var_str

#construct constraints for qualified variables

def cstr_list(list_cstr):
    if len(list_cstr)==0:
        return None;
    else:
        var=list_cstr[-1]
        del list_cstr[-1]
        list_cstr_str=cstr_list(list_cstr)
        if list_cstr_str is None:
            return var
        else:
            return "And("+var+","+list_cstr_str+")"



#strip '(' at the beginning and matching ')' in the end of a string
def trim_p(s):
    if s.startswith('(') and s.endswith(')'):
        return trim_p(s[1:-1])
    else:
        return s

#for a formula w, compute w[n]
def wff_extend(w,n,excl): #w: wff, n: expres, excl: container of strings
    if w[0]=='e': #['e',e1,e2]
        return ['e',extend(w[1],n,excl),extend(w[2],n,excl)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],extend(w[2],n,excl),extend(w[3],n,excl)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],extend(w[3],n,excl),extend(w[4],n,excl)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',extend(w[1],n,excl),extend(w[2],n,excl)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],extend(w[2],n,excl),extend(w[3],n,excl)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],extend(w[1],n,excl)]
    else:
        print('Not a wff')
        return

#for a formula w, replace functor old by new
def wff_sub(w,old,new): #w - wff; old, new - string
    if w[0]=='e': #['e',e1,e2]
        return ['e',expr_sub(w[1],old,new),expr_sub(w[2],old,new)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],expr_sub(w[2],old,new),expr_sub(w[3],old,new)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],expr_sub(w[3],old,new),expr_sub(w[4],old,new)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',expr_sub(w[1],old,new),expr_sub(w[2],old,new)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],expr_sub(w[2],old,new),expr_sub(w[3],old,new)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub(w[1],old,new)]
    else:
        print('Not a wff')
        return

#for a formula w, replace functor x+old by x+new for those in v1 but not in v2
def wff_sub_set(w,old,new,v1,v2): #w - wff; old, new - string; v1,v2: sets
    if w[0]=='e': #['e',e1,e2]
        return ['e',expr_sub_set(w[1],old,new,v1,v2),expr_sub_set(w[2],old,new,v1,v2)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],expr_sub_set(w[2],old,new,v1,v2),expr_sub_set(w[3],old,new,v1,v2)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],expr_sub_set(w[3],old,new,v1,v2),expr_sub_set(w[4],old,new,v1,v2)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',expr_sub_set(w[1],old,new,v1,v2),expr_sub_set(w[2],old,new,v1,v2)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],expr_sub_set(w[2],old,new,v1,v2),expr_sub_set(w[3],old,new,v1,v2)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_set(w[1],old,new,v1,v2)]
    else:
        print('Not a wff')
        return

#like expr_sub_dict(e,d) but on wffs

def wff_sub_dict(w,d): #w - wff; d - a dictionary as in expr_sub_dict(e,d)
    if w[0]=='e': #['e',e1,e2]
        return w[:2]+[expr_sub_dict(w[2],d)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return w[:3]+[expr_sub_dict(w[3],d)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return w[:4]+[expr_sub_dict(w[4],d)]
    elif w[0]=='d0': #['d0',e,c]
        return w[:2]+[expr_sub_dict(w[2],d)]
    elif w[0]=='d1': #['d1',v,e,c]
        return w[:3]+[expr_sub_dict(w[3],d)]
    elif w[0]=='a'or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_dict(w[1],d)]
    else:
        print('Not a wff')
        return

#parameterize a set of axioms by making program functions as input variables
#para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function taking two new parameters '_y1','_y2'
#X11(a,X)=X11(a+b,1) will become X11(a,_y1,_y1,_y2)=X11(a+b,1,_y1,_y2)
 
def parameterize_wff(ax,para):
    if ax[0] != 'a' or w[0]=='s0' or w[0]=='s1':
        e1 = parameterize_expr(ax[-2],para)
        e2 = parameterize_expr(ax[-1],para)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expr(ax[-1],para)
        return [ax[0],e2]

    

def eqset2string(d):
    for x in d:
        print wff2string(d[x])
def eqset2string1(d):
    for x in d:
        print wff2string1(d[x])
def eqset2constraintlist(d):
    equation_list=[]
    for x in d:
        equation_list.append(wff2z3(d[x]))
    return equation_list
def eqset2subs_list(d):
    subs_list={}
    for x in d:
        lhs,rhs=wff2subslist(d[x])
        if 'ite' not in rhs:
        	subs_list[simplify(lhs)]=simplify_sympy(rhs)
    return subs_list
def eqset2subs_list_ind(d):
    subs_list={}
    for x in d:
        if x[0]=='i1':
            lhs=expr2string1(x[-2])
            rhs=expr2string1(x[-1])
            lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            subs_list[lhs]=rhs
    return subs_list

"""
 A program variable has the attributes: its name, its type, 
 and its corresponding logical variable when parameterized. 
 A set of program variables is represented by a dictionary 
 with variable names as keys.
 examples: { 'X':['_y1','init','int','char'], 'I':['_y2','int'] }
 This set contains two program variables: 
 constant I of int value and function X from int*int to char
 Notice that the arity of a variable x in a set d is len(d[x])-2

 Program representations:
1. an assignment (l is the label, l='-1' means no label)
 l: left = right
 by [l,'=',e1,e2], 
 where e1,e2 are expressions representing left and right, respectively
2. a sequence
 p1; p2
 by ['-1','seq',p1,p2]
 where p1 and p2 are programs
3. if-then:
 l: if C then P
by [l,'if1', c,p], where c is the expression for C and p a program for P
4. if-then-else
 l: if c then p1 else p2
by [l,'if2', c,p1,p2], 
where c is Expr, p1 and p2 are Prog
5. while loop
 l: while c {b} by
[l,'while', c,b], 
where c is Expr, b is Prog
"""

# for testing flag=1 (original translation), flag=2 (inductive definition for smallest N)
def translate1(p,v,flag):
    global TC
    global LC
    TC=0
    LC=0
    f,o,a,l = translate0(p,v,flag)
    #Add by Pritom Rajkhowa 10 June 2016
    f,o,a,cm = rec_solver(f,o,a)
    print('Output in prefix notation:')
    print('1. Frame axioms:')
    eqset2string(f)
    print('\n2. Output equations:')
    eqset2string(o)
    print('\n3. Other axioms:')
    for x in a: 
        print wff2string(x)
    print('\nOutput in normal notation:')
    print('1. Frame axioms:')
    eqset2string1(f)
    print('\n2. Output equations:')
    eqset2string1(o)
    print('\n3. Other axioms:')
    for x in a: 
        print wff2string1(x)
    #Updated by Pritom Rajkhowa
    return f,o,a,cm

# translate0(program,set of program variables) returns a dictionary of frame axioms, output equations, a list of other axioms and a label

def translate0(p,v,flag):
    if p[1]=='while':
        return translateWhile(p,v,flag)
    if p[1]=='seq':
        return translateSeq(p,v,flag)
    if p[1]=='if1':
        return translateIf1(p,v,flag)
    if p[1]=='if2':
        return translateIf2(p,v,flag)
    if p[1]=='=':
        return translateAssign(p,v,flag)


# assignment translation: p a program and v a set of program variables

def translateAssign(p,v,flag): #p=[l,'=',left,right]
    if p[1] != '=':
        print('Not an assignment')
        return
    left = p[2] #left side of the assigment
    op = left[0] #the functor in left
    arity = len(left)-1 #arity of op
    right = p[3] #right side of the assignment
    out=OUT if p[0] == '-1' else LABEL+p[0]
    out_axioms = {}
    frame_axioms = {}
    for x in v:
        if x == op:
            args = list(expres('_x'+str(i+1)) for i in range(arity))
            cond = expres('=',[expres('_x1'),left[1]]) if arity==1 else \
                   expres('and', list(expres('=', [expres('_x'+str(i2+1)),y]) for \
                                    i2,y in zip(range(arity),left[1:])))
            if arity == 0:
                out_axioms[x]=wff_e(expres(op+out),right)
            else:
                out_axioms[x]=wff_e(expres(op+out,args), expres('ite',[cond,right,expres(op,args)]))
        else:
            args = list(expres('_x'+str(i+1)) for i in range(len(v[x])-2))
            frame_axioms[x]=wff_e(expres(x+out,args), expres(x,args))
    return frame_axioms, out_axioms, [], p[0]

def translateIf1(p,v,flag): # p=[l,'if1',c,e]
    if p[1] != 'if1':
        print('Not an if-then')
        return
    global TC
    frame_axioms,out_axioms,axioms,llabel = translate0(p[3],v,flag)
    old_out = OUT if llabel=='-1' else LABEL+llabel
    out=OUT if p[0] == '-1' else LABEL+p[0]
    if llabel=='-1': # body has no final label
        TC += 1
    body_out = TEMP+str(TC) if llabel=='-1' else LABEL+llabel
    for x in v:
        if x in frame_axioms: 
            ax = frame_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
        else:
            ax = out_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            out_axioms[x] = wff_e(expres(x+out, ax[1][1:]),
                                  expres('ite', [p[2], ax[2], expres(x,ax[1][1:])]))
    return frame_axioms, out_axioms, axioms, p[0]
            
def translateIf2(p,v,flag): # p=[l,'if2',c,e1,e2]
    if p[1] != 'if2':
        print('Not an if-then-else')
        return
    global TC
    frame_axioms0,out_axioms0,axioms0,llabel0 = translate0(p[3],v,flag)
    frame_axioms1,out_axioms1,axioms1,llabel1 = translate0(p[4],v,flag)
    axioms = axioms0+axioms1
    old_out0 = OUT if llabel0=='-1' else LABEL+llabel0
    old_out1 = OUT if llabel1=='-1' else LABEL+llabel1
    out=OUT if p[0] == '-1' else LABEL+p[0]
    if llabel0=='-1': # if body has no final label
        TC += 1
    body_out0 = TEMP+str(TC) if llabel0=='-1' else LABEL+llabel0 # if body new out
    if llabel1=='-1': # else body has no final label
        TC += 1
    body_out1 = TEMP+str(TC) if llabel1=='-1' else LABEL+llabel1 # else body new out
    frame_axioms = {}
    out_axioms = {}
    for x in v:
        if x in frame_axioms0 and x in frame_axioms1: 
            ax0 = frame_axioms0[x] #ax0 = ['e',e1,e2]
            ax1 = frame_axioms1[x] #ax1 = ['e',e1,e2]
            if llabel0 != '-1': #if body has label: keep axioms about it
                axioms.append(ax0)
            if llabel1 != '-1': #else body has label: keep axioms about it
                axioms.append(ax1)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax0[1],x+old_out0,x+out), ax0[2])
        else:
            if x in frame_axioms0:
                ax0=frame_axioms0[x]
            else:
                ax0=out_axioms0[x]
            if x in frame_axioms1:
                ax1=frame_axioms1[x]
            else:
                ax1=out_axioms1[x]
            if llabel0 != '-1': #if body has label: keep axioms about it
                axioms.append(ax0)
            if llabel1 != '-1': #else body has label: keep axioms about it
                axioms.append(ax1)
            out_axioms[x] = wff_e(expres(x+out, ax0[1][1:]),
                                  expres('ite', [p[2], ax0[2], ax1[2]]))
    return frame_axioms, out_axioms, axioms, p[0]
            
def translateSeq(p,v,flag): # p=['-1','seq',p1,p2]
    if p[1] != 'seq':
        print('Not a sequence')
        return
    global TC
    frame_axioms0,out_axioms0,axioms0,llabel0 = translate0(p[2],v,flag)
    frame_axioms1,out_axioms1,axioms1,llabel1 = translate0(p[3],v,flag)
    old_out0 = OUT if llabel0=='-1' else LABEL+llabel0
    if llabel0=='-1': # if p1 has no final label
        TC += 1
    new_out0 = TEMP+str(TC) if llabel0=='-1' else LABEL+llabel0 # p1 new out
    frame_axioms = {}
    out_axioms = {}
    para = {} #a dictonary of substitution: para[x] is the expression to replace x(t) in p2's axioms
    for x in v:
        if x in frame_axioms0 and x in frame_axioms1:
            if llabel0 !='-1': #p1 has label, keep its axioms
                axioms0.append(frame_axioms0[x])
            frame_axioms[x]=frame_axioms1[x]
        else:
            if x in frame_axioms0:
                ax0=frame_axioms0[x] #ax0=['e',e1,e2]
            else:
                ax0=out_axioms0[x]
            if llabel0 != '-1': #p1 has label: keep equations about it
                axioms0.append(ax0)
            para[x]=ax0[2]
    for i,ax in enumerate(axioms1): #substituting p1's output into p2's input in p2's axioms
        axioms1[i] = wff_sub_dict(ax,para)
    for x in v: #do the same for the p2's output equations and frame axioms
        if not x in frame_axioms:
            if x in frame_axioms1:
                out_axioms[x] = frame_axioms1[x][:2]+[expr_sub_dict(frame_axioms1[x][2],para)]
            else:
                out_axioms[x] = out_axioms1[x][:2]+[expr_sub_dict(out_axioms1[x][2],para)]
    return frame_axioms, out_axioms, axioms0+axioms1, llabel1

def translateWhile(p,v,flag): #p=[l, 'while', c, b]
    if p[1] != 'while':
        print('Not a while statement')
        return
    global LC
    global TC
    frame_axioms, out_axioms0, axioms,llabel = translate0(p[3],v,flag) # axioms and output labels for the body of the loop
    LC += 1
    if llabel=='-1': # if body has no final label
        TC += 1
    loop_var = expres('_n'+str(LC)) #a new natural number variable for the loop
    smallest = expres('_N'+str(LC)) #a new natural number variable for the loop
    init=TEMP+str(TC) if llabel=='-1' else LABEL+llabel #iterating functions
    old_out=OUT if llabel=='-1' else LABEL+llabel #original output functions in body
    out=OUT if p[0]=='-1' else LABEL+p[0] #new output functions for the loop
    for i0, ax0 in enumerate(axioms): #extend the axioms with [n]
        ax0 = wff_sub_set(ax0,'',init,v,frame_axioms)
        axioms[i0]=wff_extend(ax0, loop_var, frame_axioms)
    for x in v:
        if x in frame_axioms:
            ax = frame_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
        else:
            ax = out_axioms0[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            ax = wff_sub_set(ax,old_out,init,v,frame_axioms)
            ax = wff_sub_set(ax,'',init,v,frame_axioms)
            e1=extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms)
            e2=extend(ax[2],loop_var,frame_axioms)
            axioms.append(wff_i1(len(ax[1][-1]),expr_op(loop_var),e1,e2))
    #base case
    for x in v:
        if not x in frame_axioms:
            arity = len(v[x])-2
            args = list(expres('_x'+str(i+1)) for i in range(arity))
            axioms.append(wff_i0(arity,expres(x+init,args+[expres('0')]), expres(x,args)))
    c=p[2] #loop condition
    c=expr_sub_set(c,'',init,v,frame_axioms)
    c = extend(c,loop_var,frame_axioms) #add the smallest macro
    #Add by pritom
    cc = copy.deepcopy(c)
    axioms.append(wff_s0(expr_sub(expr_complement(cc),expr_op(loop_var),expr_op(smallest))))
    #axioms.append(wff_a(expres('not',[expr_sub(c,expr_op(loop_var),expr_op(smallest))])))
    axioms.append(wff_s1(expres('implies',
                             [expres('<', [loop_var, smallest]),c])))
    

    out_axioms = {}
    for x in v: # generate out_axioms
        if not x in frame_axioms:
            args = list(expres('_x'+str(i+1)) for i in range(len(v[x])-2))
            e1=expres(x+out,args)
            args.append(smallest)
            e2=expres(x+init,args)
            out_axioms[x]=wff_e(e1,e2)
    if flag==2:
        g = graph(axioms) #construct dependency graph
        for x in expr_func(p[2]):
            if not ['_N'+str(LC), x] in g:
                g.append(['_N'+str(LC), x])
                g.append(['_N'+str(LC), x+init])
        #build a dictionary para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y'],...} 
        #meaning 'X' is an input variable parameterized as '_y1' and 
        #'X11' is a function taking two new parameters '_y1' and '_y2' which correspond 
        # to 'X' and 'Y', respectively
        para={} 
        for x in reach_set(['_N'+str(LC)],g): #compute the dependency set of N
            if x in v and not x in frame_axioms:
                para[x] = [1,[v[x][0]]]
            else:
                if not x in para and not x in frame_axioms:
                    t=[]
                    t1=[]
                    for y in reach_set([x],g):
                        if y in v and (not y in t1) and (not y in frame_axioms):
                            t.append(expres(v[y][0]))
                            t1.append(expres(y))
                    if t != []:
                        para[x] = [0,t,t1]
        #parameterize input variables that N depends on and all associated functions
        for i,ax in enumerate(axioms):
            axioms[i] = parameterize_wff(ax,para)
        #construct inductive definition for N
        s_args = para['_N'+str(LC)][1]
        smallest1=expres('_N'+str(LC), s_args)
        next_args=[]
        for i,y in enumerate(s_args):
            x=expr_op(para['_N'+str(LC)][2][i])
            next_args.append(parameterize_expr(out_axioms0[x][2],para))
        #axioms.append(['d0',smallest1, parameterize_expr(p[2],para)])
        axioms.append(['d0',smallest1, parameterize_expr(expr('not',[p[2]]),para)])
        axioms.append(['d1','_n'+str(LC), smallest1, 
                       expres('=',[loop_var,expres('_N'+str(LC),next_args)])])
        #parameterize output axioms
        for x in out_axioms:
            out_axioms[x]=out_axioms[x][:2]+[parameterize_expr_sub(out_axioms[x][2],para)]
    #Recurrence Solver Code Add by Pritom
    constant='_N'+str(LC)
    equation_map={}
    base_map={}
    for axiom in axioms:
    	if axiom[0]=='i1':
    		lefthandstmt=expr2string1(axiom[3])
    		lefthandstmt=lefthandstmt.strip()
    		equation_map[str(simplify(lefthandstmt))]=axiom
    	if axiom[0]=='i0':
    		lefthandstmt=expr2string1(axiom[2])
    		lefthandstmt=lefthandstmt.strip()
    		base_map[str(simplify(lefthandstmt))]=axiom
    while True:
    	solution_map={} 
    	for equation in equation_map:
    		e1=equation_map[equation]
    		equation_base=str(simplify(equation).subs(str(e1[2])+"+1",0))
    		e2=base_map[equation_base]
    		result=solve_rec(e1,e2)
    		if result is not None:
    			axioms.remove(base_map[equation_base])
    			del base_map[equation_base]
    			solution_map[equation]=result
    	for equation in solution_map:
    		axioms.remove(equation_map[equation])
    		del equation_map[equation]
    		e=solution_map[equation]
    		e1=copy.deepcopy(e)
    		variable=e[2]
    		axioms=solnsubstitution(axioms,e[3],e[4])
    		e1[3]=expr_replace_const(e1[3],variable,constant)
    		e1[4]=expr_replace_const(e1[4],variable,constant)
    		axioms=solnsubstitution(axioms,e1[3],e1[4])
    		for x in out_axioms:
			stmt=out_axioms[x]
    			stmt[2]=expr_replace(stmt[2],e1[3],e1[4])
    	if len(equation_map)==0 or len(solution_map)==0:
    		break
    updated_axioms=[]
    for ax in axioms:
    	if ax[0]=='a':
    		expression=expr2string1(ax[1])
    		if '->' not in expression and constant in expression:
    			if '>=' in expression and 'and' not in expression and 'or' not in expression:
				expression=normal_form_constant(expression, constant)
				pp = getParser()
				tree = pp.parse_expression(str(expression))			 
				ax=construct_expression_normal(tree)
				updated_axioms.append(ax)
    			elif '<=' in expression and 'and' not in expression and 'or' not in expression:
				expression=normal_form_constant(expression, constant)
				pp = getParser()
				tree = pp.parse_expression(str(expression))		 
				ax=construct_expression_normal(tree)
				updated_axioms.append(ax)
			else:
				updated_axioms.append(ax)
		else:
			updated_axioms.append(ax)
		
	else:
		updated_axioms.append(ax)
	    	
    #return frame_axioms, out_axioms, axioms, p[0]
    return frame_axioms, out_axioms, updated_axioms, p[0]
   


#construct a graph of dependency relation in a set of equations axioms 
def graph(axioms):
    ret = []
    for ax in axioms:
        if ax[0]=='e' or ax[0]=='i0' or ax[0]=='i1' or ax[0]=='d0' or ax[0]=='d1':
            op=expr_op(ax[-2])
            for x in expr_func(ax[-1]):
                if not [op,x] in ret:
                    ret.append([op,x])
    return ret

#given a list s of nodes, return the list of nodes that are reachable from the nodes in s
def reach_set(s,g):
    s1=[]
    for [n1,n2] in g:
        if (n1 in s) and not (n2 in s):
            s1.append(n2)
    if s1==[]:
        return s
    else:
        return reach_set(s+s1,g)

                            
# testing examples. 
x=expres('x')
y=expres('y')
ex1 = ['-1','=',x, expres('+',[y,['1']])] #x=y+1
ex2 = ['-1','=',y, ['+',y,['1']]] #y=y+1
ex21 = ['1','=',y, ['+',y,['1']]] #1: y=y+1
ex22 = ['-1','if1',['>', y,['1']],ex2] # if y>1 then y=y+1
ex23 = ['-1','if1',['>', y,['1']],ex21] # if y>1 then l: y=y+1
ex24 = ['-1','if2',['>', y,['1']],ex21,ex1] # if y>1 then l: y=y+1 else x=y+1
ex3 = ['-1','seq',ex1,ex2]  #x=y+1; y=y+1
v1 = {'x':['_y1','int'], 'y':['_y2','int']}
ex4 = ['-1', '=', ['t',x], ['+', ['+', ['z', x, ['t', x]], ['1']], x]]
ex42 = ['-1', '=', ['z',x,y], ['+', ['+', ['z', x, ['t', x]], ['1']], x]]
v2 = {'x':['_y1','int'], 'y':['_y2','int'], 't':['_y3','int','int'], 'z':['_y4','int','int','int']}
ex41 = ['-1','if1',['>', y,['1']],ex4] # if y>1 then ex4

ex25 = ['-1','if2',['>', y,['1']],ex1,ex4] 

ex5 = ['-1','if2',expres('and', [expres('=', [expres('x'),expres('t',[expres('1')])]), expres('<', [expres('y'), expres('z',[expres('x'),expres('y')])])]), ex1, ex4]

ex6 = ['-1','while',expres('<',[expres('x'),expres('y')]),ex4]

#translate1(ex3,v1,1)
#translate1(ex4,v2,1)
#translate1(ex5,v2,1)

# factorial function
"""
i=1;
F=1;
while(i <= X) {
 F=F*i;
 i=i+1;
}
"""
i=expres('i')
F=expres('F')
X=expres('X')
fact0 = ['-1','seq',['-1','=',i,['1']],['-1','=',F,['1']]]
fact1 = ['-1','seq',['-1','=',F,['*',F,i]],['-1','=',i,['+',i,['1']]]]
fact2 = ['-1','while', ['<=',i,X], fact1]
fact = ['-1','seq',fact0,fact2]
vfact = {'i':['_y1','int'], 'X':['_y2','int'], 'F':['_x3','int']}
#translate1(fact,vfact)

# in-place list reversing - see Lin and Yang 2015
"""
J = null;
while I != null do {
    K = next(I);
    next(I) = J;
    J=I;
    I=K;
}
I=J;
"""

lr6 = ['-1','=',['I'],['K']]
lr5 = ['-1','seq',['-1','=',['J'],['I']], lr6]
lr4 = ['-1','seq',['-1','=', ['next', ['I']],['J']], lr5]
lr3 = ['-1','seq',['-1','=',['K'],['next',['I']]], lr4]
lr2 = ['-1','while',['!=', ['I'], ['null']], lr3]
lr1 = ['-1','seq',lr2,['-1','=',['I'],['J']]]
lr = ['-1','seq',['-1','=',['J'],['null']], lr1]
vlr = {'J':['_y1','list'],'I':['_y2','list'],'K':['_y3','list'],'next':['_y4','list','list']}

#Cohen's division algorithm
"""
//XandYaretwoinputintegers;Y>0 
Q=0; // quotient
R=X; // remainder
while (R >= Y) do {
    A=1; // A and B are some that at any time for
    B=Y; // some n, A=2^n and B=2^n*Y
    while (R >= 2*B) do {
       A = 2*A;
       B = 2*B; }
    R = R-B;
    Q = Q+A }
//
return Q = X/Y;
"""

"""
A=expres('A')
B=expres('B')
R=expres('R')
Q=expres('Q')
Y=expres('Y')
A2=expres('*',[expres('2'),A]) #2*A
B2=expres('*',[expres('2'),B]) #2*B
RB=expres('-',[R,B]) #R-B
QA=expres('+',[Q,A]) #Q+A
c1=expres('>=',[R,B2]) #R>=2*B
c2=expres('>=',[R,Y]) #R >= Y

cohen9=['-1','seq',['-1','=',A,A2],['-1','=',B,B2]]
cohen8=['-1','seq',['-1','=',R,RB],['-1','=',Q,QA]]
cohen7=['-1','while',c1, cohen9]
cohen6=['-1','seq',cohen7,cohen8]
cohen1=['-1','=',Q,['0']]
cohen5=['-1','seq',['-1','=',B,Y],cohen6]
cohen4=['-1','seq',['-1','=',A,['1']],cohen5]
cohen3=['-1','while',c2, cohen4]
cohen2=['-1','seq',['-1','=',R,X],cohen3]
cohen = ['-1', 'seq', cohen1,cohen2]
vcohen={'X':['_y1','int'],'Y':['_y2','int'],'Q':['_y3','int'],'R':['_y4','int'],'A':['_y5','int'],'B':['_y6','int']}
"""


#product of two integers
"""
Z = 0;
while( Y!=0 ) {
 if ( Y % 2 ==1 ) {
     Z = Z+X;
     Y =(Y-1);
  }
  X = 2*X;
  Y = Y/2;
}
"""
#Z=expres('Z')
#prod1=['-1','seq',['-1','=',Z,expres('+',[Z,X])],['-1','=',Y,expres('-',[Y,['1']])]]
#prod2=['-1','seq',['-1','=',X,expres('*',[['2'],X])],['-1','=',Y,expres('/',[Y,['2']])]]
#prod3=['-1', 'if1', expres('=',[expres('%',[Y,['2']]), ['1']]), prod1]
#prod4=['-1','seq',prod3,prod2]
#prod5=['-1','while',expres('!=',[Y,['0']]),prod4]
#prod = ['-1','seq',['-1','=',Z,['0']],prod5]
#vprod = {'X':['_y1','int'],'Y':['_y2','int'],'Z':['_y3','int']}

#array sum array represented as a reference, and element represented by at predicate
"""
i=0;
sum=0;
while (i<size(A)) {
 sum=at(A,i)+sum
 i=i+1
}
"""
#sum3=['-1','while',expres('<',[i,expres('size',[A])]),['-1','seq',['-1','=',['sum'],expres('+',[expres('at',[A,i]),['sum']])],['-1','=',i,expres('+',[i,['1']])]]]
#sum2=['-1','seq',['-1','=',['sum'],['0']],sum3]
#sum1=['-1','seq',['-1','=',i,['0']],sum2]
#vsum = {'i':['_y1','int'],'sum':['_y2','int'],'size':['_y3','array','int'],'A':['_y4','array'],'at':['_y5','array','int','int']}


"""
class Expr(object):

    def __init__(self, op, chld=[]):
        self.op = op
        self.chld = chld

    def __repr__(self):
        if self.chld == []:
            return self.op
        else:
            return '(' + self.op +' '+ ' '.join(list(x.__repr__() for x in self.chld))+ ')'

    @classmethod #read in an expression in list format ['+',['a'],['1']] (a+1)
    def fromlist(cls,lst):
        if lst==[]:
            print('empty term')
        else:
            return cls(lst[0],list(cls.fromlist(x) for x in lst[1:]))

    # checking if an expr is a constant
    def const(self):
        if self.chld==[]:
            return True
        else:
            return False    

    # rename a function name in an expression a.rename('x1','x2') replaces every x1 in a by x2
    def rename(self,old,new):
        return Expr(new if self.op == old else self.op,
                 list(x.rename(old,new) for x in self.chld))

    # checking if two expressions are equal
    def equal(self,other):
        if (self.op != other.op) or (len(self.chld) != len(other.chld)):
            return False
        else:
            for x,y in zip(self.chld,other.chld):
                if not x.equal(y):
                    return False
            return True

    # replace every occurrence of e1 by e2 in self
    def replace(self,e1,e2):
        if self.equal(e1):
            return e2.copy()
        else:
            return Expr(self.op,list(x.replace(e1,e2) for x in self.chld))

    # compute E[n] extend(self,n). n is an E like Expr('_n1'). side effect
    def extend(self,n):
        for x in self.chld:
            x.extend(n)
        if (not self.op in _base) and (not isvariable(self.op)):
            if self.chld==[]:
                self.chld=[n.copy()]
            else:
                self.chld.append(n.copy())

    # make a deep copy
    def copy(self):
        return Expr(self.op, list(x.copy() for x in self.chld))

#string2term(s) - convert a string to term

def string2term(s):
    s=s.strip()


# Wff - for formulas, a node with types (normal equation, inductive equation,...) and  
#equations f(x) = e: Wff('e',[e1,e2]), e1 is Expr for f(x) and e2 is Expr for e
#inductive definition:
# - base case f(x1,...,xk,0,...,xm)=e: Wff('i0',[k,e1,e2]) where e1 is Expr for f(x1,...,xk,0,...,xm) and e2 the Expr for e
# - inductive case f(x1,...,xk,n+1,...,xm)=e: Wff('i1',[k,'n',e1,e2]) where e1 is Expr for f(x1,...,xk,n+1,...,xm) and e2 the Expr for e
#inductive definition for natural number function:
# - base case f(x) = 0 iff C: Wff('d0',[e,c]) where e is the Expr for f(x) and c the Wff for C
# - inductive case f(x) = n+1 iff C(n): Wff('d1',['n',e,c]) where e is the Expr for f(x) and c the Wff for C
#any other axioms: A: Wff('a',[e]), where e is the Expr for A


class Wff(object):
    def __init__(self,typ,chld):
        self.typ = typ
        self.chld = chld

    def __repr__(self):
        if self.typ == 'e' or self.typ == 'i0' or self.typ == 'i1':
            return '(= '+self.chld[0].__repr__()+' '+self.chld[1].__repr__() +')'
        elif self.typ == 'd0':
            return '(iff (='+self.chld[0].__repr__()+' 0) '+self.chld[1].__repr__()+')'
        elif self.typ == 'd1':
            return '(iff (='+self.chld[1].__repr__()+' (+ '+self.chld[0]+' 1)) '+self.chld[2].__repr__()+')'
        elif self.typ=='a':
            return self.chld[0].__repr__()


# Pv - program variables Pv('X',['init','int','char'],'_y1') creates a Pv object representing prorgam varibale X of type int*int -> char, and represented by variable _y1 when parameterized.

class Pv(object):
    def __init__(self,name,typ,var):
        self.name = name
        self.typ = typ
        self.var = var

    def __repr__(self):
        return [self.name, self.typ, self.var]

    def arity(self):
        return len(self.typ)-1

# Program - for programs, with label, type, and list which depends on type
# l: e1 = e2: Prog(l,'=',[e1,e2]), e1,e2 are Expr
# l: if c then p: Prog(l,'if1', [c,p]), c is Expr and p is Prog
# l: if c then p1 else p2: Prog(l,'if2', [c,p1,p2]), c is Expr, p1 and p2 are Prog
# l: while c {b}: Prog(l,'while', [c,b]), c is Expr, b is Prog

class Prog(object):
    def __init__(self,label,typ,chld):
        self.label=label # '-1' if no label
        self.typ=typ
        self.chld=chld
            
"""

"""

Construction Parser

"""
p = plyj.parser.Parser()

def getParser():
	global p
	return p


"""
Expanding algebraic powers
"""

def pow_to_mul(expression):
    """
    Convert integer powers in an expression to Muls, like a**2 => a*a(Only for Squre).
    """
    #expression=simplify(expression).expand(basic=True)
    #expression=simplify(expression)
    pows=list(expression.atoms(Pow))
    if any(not e.is_Integer for b, e in (i.as_base_exp() for i in pows)):
    	#A power contains a non-integer exponent
    	return expression
    repl=None
    for b,e in (i.as_base_exp() for i in pows):
    	if e==2:
    		repl = zip(pows,((Mul(*[b]*e,evaluate=False)) for b,e in (i.as_base_exp() for i in pows)))
    if repl is not None:
    	return expression.subs(repl)
    else:
    	return expression

"""
Convert Inequality to Normal Form

"""


def normal_form_constant(expression, constant):
    mult_by_minus_one_map = {
    	None: '==',
    	'>=': '<=',
    	'<=': '>=',
    	'>': '<',
    	'<': '>',
	}
    ineq=simplify(expression)
    l = ineq.lhs
    r = ineq.rhs
    op = ineq.rel_op
    all_on_left = l - r
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    new_rhs = sympify(0)
    for s in var_types:
    	if s != simplify(constant):
    		factor=s.coeff(simplify(constant))
        	if factor==0:
            		all_on_left = (all_on_left - (coeff_dict[s]*s))
            		new_rhs = (new_rhs - (coeff_dict[s]*s))
    all_on_left=all_on_left.expand(basic=True)
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    if len(var_types)==1:
    	for s in var_types:
    		if coeff_dict[s]<0:
    			all_on_left = all_on_left * -1
        		new_rhs = new_rhs * -1
        		op = mult_by_minus_one_map[op]	
    	factor=all_on_left.coeff(simplify(constant))
    	if factor!=0:
		all_on_left=all_on_left/factor
    		new_rhs=new_rhs/factor
    else:
    	all_on_left=simplify(all_on_left)
    	new_rhs=simplify(new_rhs)
    	coeff_dict = all_on_left.as_coefficients_dict()
    	var_types = coeff_dict.keys()
    	if len(var_types)==1:
	 	for s in var_types:
	 		if coeff_dict[s]<0:
	    			all_on_left = all_on_left * -1
	        		new_rhs = new_rhs * -1
        			op = mult_by_minus_one_map[op]	
    return Relational(all_on_left,new_rhs,op)





#To construct vfact
def wff2fvact(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            return expr2string1(w[-2])
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            return expr2string1(w[1])
            
"""
Construct vfact by analysis translated equation equation 
"""

def getVariFunDetails(f,o,a,variableMapIp,variableMapOp):
	constaints=[]
	loopvariablesMap={}
	functionMap={}
	vfacts=""
	for variable in variableMapIp:
            values=variableMapIp[variable]
	    if values=='int':	
                vfact="['"+variable+"',0,['int']]"
	    elif values=='float':
                vfact="['"+variable+"',0,['int']]"
	    elif values=='double':
		vfact="['"+variable+"',0,['int']]"
            if vfacts=="":
                vfacts=vfact
            else:
                if vfact!="":
                    vfacts+=","+vfact
	for variable in variableMapOp:
            values=variableMapOp[variable]
	    if values[1]=='int':	
                vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='float':
                vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='double':
		vfact="['"+variable+"',0,['int']]"
            if vfacts=="":
                vfacts=vfact
            else:
                if vfact!="":
                    vfacts+=","+vfact
	equations=[]
        for x in a: 
        	equations.append(wff2fvact(x))
            
	for equation in equations:
		if '->' not in equation and '>' not in equation and '<' not in equation and '=' not in equation :
			loopvariables=extract_args(equation)
			equation=equation.strip()
			vfact=""
			if len(loopvariables)==0:	
				if equation not in variableMapOp.keys():
					values=variableMapIp[equation]
					if values[1]=='int':	
						vfact="['"+equation+"',0,['int']]"
					elif values[1]=='float':
						vfact="['"+equation+"',0,['int']]"
					elif values[1]=='double':
						vfact="['"+equation+"',0,['int']]"
				
			else:
				function_name=getFunctionName(str(equation),loopvariables )
				if function_name not in functionMap.keys():
					functionMap[function_name]=function_name
					fact="['int'"
					for x in xrange(len(loopvariables)):
						fact+=",'int'"
					fact+="]"
					vfact="['"+function_name+"',"+str(len(loopvariables))+","+fact+"]"	
			if vfacts=="":
				vfacts=vfact
			else:
				if vfact!="":
					vfacts+=","+vfact
		elif '->' in equation:
			axiomes=equation.split('->')
			axiomes[0]=simplify(str(axiomes[0]))
			variables=str(axiomes[0]).split('<')
			variables[0]=variables[0].strip()
			variables[1]=variables[1].strip()
			loopvariables=extract_args(variables[1])
			loopvariablesMap[variables[0]]=variables[0]
			parameter=""
			for variable in  loopvariables:
				variable=variable.strip()
				if parameter=="":
					parameter="["+variable
				else:
					parameter+=" ,"+variable
					loopvariablesMap[variable]=variable
			if parameter=="":
				constaint=variables[1]+">=0"
			else:
				parameter+="]"
				constaint="ForAll("+parameter+","+variables[1]+">=0)"
			constaints.append(constaint)
			vfact=""
			if len(loopvariables)==0:	
				vfact="['"+variables[1]+"',0,['int']]"			
			else:
				fact="['int'"
				for x in xrange(len(loopvariables)):
					fact+=",'int'"
				fact+="]"
				vfact="['"+getFunctionName(str(variables[1]),loopvariables )+"',"+str(len(loopvariables))+","+fact+"]"	
			if vfacts=="":
				vfacts=vfact
			else:
				if vfact!="":
					vfacts+=","+vfact
	for loopvariable in loopvariablesMap:
		if vfacts=="":
			vfacts="['"+loopvariable+"',0,['int']]"
		else:
		 	vfacts+=","+"['"+loopvariable+"',0,['int']]"
	
	vfacts=eval("["+vfacts+"]")
	return vfacts,constaints


"""
Recurrences Solving Module
#Add by Pritom Rajkhowa
#June 8

Test cases

Test Case 1

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['+', ['a3', ['_n1']], ['1']]]
#e2=['i0', 0, ['a3', ['0']], ['0']]

Test Case 2

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['+', ['_n1'], ['1']]]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

Test Case 3

#e1=['i1', 2, '_n1', ['t3', ['+', ['_n1'], ['1']]], ['+', ['t3', ['_n1']], ['2']]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

Test Case 4

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['2']]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

"""
def solve_rec(e1,e2):
	lefthandstmt=None
	righthandstmt=None
	righthandstmt_d=None
	lefthandstmt_base=None
	righthandstmt_base=None
	righthandstmt_base_d=None
	variable=None
	closed_form_soln=None
	if e1[0]=='i1':
		lefthandstmt=expr2string1(e1[3])
		righthandstmt=expr2string1(e1[4])
		lefthandstmt=lefthandstmt.strip()
		righthandstmt=righthandstmt.strip()
		variable=e1[2]
		if 'ite' not in righthandstmt: 
		    	lefthandstmt=simplify(lefthandstmt)
		    	righthandstmt=simplify(righthandstmt)
		    	variable=simplify(variable)
		else:
			lefthandstmt=None
			righthandstmt=None
			variable=None
	if e2[0]=='i0':
		lefthandstmt_base=expr2string1(e2[2])
		righthandstmt_base=expr2string1(e2[3])
		variable_list=[]
		expr2varlist(e2[3],variable_list)
		lefthandstmt_base=lefthandstmt_base.strip()
		righthandstmt_base=righthandstmt_base.strip()
		lefthandstmt_base=simplify(lefthandstmt_base)
		righthandstmt_base=simplify(righthandstmt_base)
	if variable is not None and lefthandstmt is not None and righthandstmt is not None and lefthandstmt_base is not None and righthandstmt_base is not None:
		righthandstmt_d=righthandstmt
		righthandstmt_base_d=righthandstmt_base
		term1=lefthandstmt.subs(str(variable)+"+1","0")
		term2=lefthandstmt.subs(str(variable)+"+1",variable)
		if term1==lefthandstmt_base and  str(term2) in str(righthandstmt):
			righthandstmt=simplify(righthandstmt).subs({simplify(term2):simplify('T(n)'),simplify(variable):simplify('n')})
			result=None
			#Try to solve recurrences
			try:
				#result=recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list)
				result=recurreSolver_sympy(righthandstmt,righthandstmt_base)
				if result is None:
					#result=recurreSolver_sympy(righthandstmt,righthandstmt_base)
					result=recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list)
			except ValueError:
				result=None
			if result is not None:
				result=substituteValue(simplify_sympy(result),simplify('n'),simplify(variable))
				writeLogFile( "j2llogs.logs" , "\nOriginal Axoims \n"+str(lefthandstmt)+"="+str(righthandstmt_d)+","+str(lefthandstmt_base)+"="+str(righthandstmt_base_d)+"\n Closed Form Solution\n"+str(result)+"\n" )
				if "**" in str(result):
					result=translatepowerToFun(str(result))
				expression=str(str(term2)+"="+str(result))
				p = getParser()
				tree = p.parse_expression(expression)
				closed_form_soln=construct_expression(tree,e1[1],e1[2])
			
	return closed_form_soln


"""
#Code Add by Pritom Rajkhowa
#Following Code will Translate Java Program to a Array of Statements 
"""
"""
Recurrence Solver After Translation
"""
def rec_solver(f,o,a):
    constant_fun_map={}
    equation_map={}
    base_map={}
    for axiom in a:
        if axiom[0]=='i1':
             lefthandstmt=expr2string1(axiom[3])
	     lefthandstmt=lefthandstmt.strip()
             equation_map[str(simplify(lefthandstmt))]=axiom
	if axiom[0]=='i0':
	     lefthandstmt=expr2string1(axiom[2])
	     lefthandstmt=lefthandstmt.strip()
	     base_map[str(simplify(lefthandstmt))]=axiom
	if axiom[0]=='s1':
	     equ=expr2string1(axiom[1])
	     if '->' in equ:
                 axiomes=equ.split('->')
		 axiomes[0]=simplify(str(axiomes[0]))
		 variables=str(axiomes[0]).split('<')
		 variables[0]=variables[0].strip()
		 variables[1]=variables[1].strip()
		 constant_fun_map[variables[0]]=variables[1]
    while True:
        solution_map={} 
	for equation in equation_map:
            e1=equation_map[equation]
	    equation_base=str(simplify(equation).subs(str(e1[2])+"+1",0))
	    e2=base_map[equation_base]
	    result=solve_rec(e1,e2)
	    if result is not None:
                a.remove(base_map[equation_base])
		del base_map[equation_base]
		solution_map[equation]=result
	for equation in solution_map:
            a.remove(equation_map[equation])
	    del equation_map[equation]
	    e=solution_map[equation]
	    e1=copy.deepcopy(e)
	    variable=e[2]
	    a=solnsubstitution(a,e[3],e[4])
	    constant=constant_fun_map[variable]
	    e1[3]=expr_replace_const(e1[3],variable,constant)
	    e1[4]=expr_replace_const(e1[4],variable,constant)
	    a=solnsubstitution(a,e1[3],e1[4])
	    for x in o:
                stmt=o[x]
		stmt[2]=expr_replace(stmt[2],e1[3],e1[4])
	if len(equation_map)==0 or len(solution_map)==0:
            break
    return f,o,a,constant_fun_map
    

"""
#Function to Simplify and Expand an expression using sympy
"""
def simplify_expand_sympy(expression):
    if 'Implies' not in expression and 'ite' not in expression and '==' not in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
    	return str(simplify_sympy(expression))
    elif 'Implies' in expression :
        axioms=extract_args(expression)
        #return 'Implies('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+')'
        return 'Implies('+axioms[0]+','+simplify_expand_sympy(axioms[1])+')'
    elif 'ite' in expression:
        axioms=extract_args(expression)
        return 'If('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+','+simplify_expand_sympy(axioms[2])+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('==')
        if left is not None and right is not None:
        	if '%' in axioms[0]:
        		leftin =None
			rightin =None
        		leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
        		axm=axioms[0].split('%')
        		if left is not None and right is not None:
        			expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
        		else:
        			expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right
        	
        	else:
        		expression=left+str(simplify_sympy(axioms[0]))+'=='+str(simplify_sympy(axioms[1]))+right
        		#expression=left+str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(powsimp(pow_to_mul(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	if '%' in axioms[0]:
			leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if left is not None and right is not None:
				expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
			else:
				expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right
		        	
        	else:
        		expression=str(simplify_sympy(axioms[0]))+'=='+str(simplify_sympy(axioms[1]))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('!=')
        if left is not None and right is not None:
              	if '%' in axioms[0]:
	        	leftin =None
			rightin =None
	        	leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
	        	axm=axioms[0].split('%')
	        	if leftin is not None and rightin is not None:
	        		expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
	        	else:
        			expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right
        	else:
        		expression=left+str(simplify_sympy(axioms[0]))+'!='+str(simplify_sympy(axioms[1]))+right
        		#expression=left+str(powsimp(pow_to_mul(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	 if '%' in axioms[0]:
		 	leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if leftin is not None and rightin is not None:
				expression=left+leftin+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+rightin+'=='+str(simplify_sympy(axioms[1]))+right
			else:
		        	expression=left+str(simplify_sympy(axm[0]))+'%'+str(simplify_sympy(axm[1]))+'=='+str(simplify_sympy(axioms[1]))+right

        	 else:
        		expression=str(simplify_sympy(axioms[0]))+'!='+str(simplify_sympy(axioms[1]))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    else:
        return  expression

"""
#convert all power operator to power function
"""

def convert_pow_op_fun(expression):
    if 'Implies' not in expression and 'ite' not in expression and 'If' not in expression and '==' not in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        return  translatepowerToFun(expression)
    elif 'Implies' in expression:
        axioms=extract_args(expression)
        return 'Implies('+convert_pow_op_fun(axioms[0])+','+convert_pow_op_fun(axioms[1])+')'
    elif 'ite' in expression:
        axioms=extract_args(expression)
        return 'If('+convert_pow_op_fun(axioms[0])+','+convert_pow_op_fun(axioms[1])+','+convert_pow_op_fun(axioms[2])+')'
    elif 'If' in expression:
        axioms=extract_args(expression)
        return 'If('+convert_pow_op_fun(axioms[0])+','+convert_pow_op_fun(axioms[1])+','+convert_pow_op_fun(axioms[2])+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        expression=translatepowerToFun(expression)
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression:
        expression=translatepowerToFun(expression)
        return expression
    else:
        return  translatepowerToFun(expression)


def simplify_sympy(expression):
	expression_mod=powsimp(expression)
	if '/' not in str(expression_mod):
		expression=expression_mod
	if '/' in str(expression):
		no,deno=fraction(together(expression))
		no=sympify(no).expand(basic=True)
		deno=sympify(deno).expand(basic=True)
		if deno==1:
			return pow_to_mul(powsimp(no))
		else:
                 	return Mul(pow_to_mul(powsimp(no)), Pow(pow_to_mul(powsimp(deno)), -1), evaluate=False)
	
	else:
		#return str(sympify(expression).expand(basic=True))
		return pow_to_mul(powsimp(sympify(expression).expand(basic=True)))
	

def substituteValue(expression,key,value):
	if '/' in str(expression):
		#no,deno=fraction(together(expression))
		no,deno=fraction(expression)
		no=sympify(no).expand(basic=True)
		no=no.subs(key,value)
		deno=deno.subs(key,value)
		if deno==1:
			return powsimp(no)
		else:
                 	return Mul(powsimp(no), Pow(powsimp(deno), -1), evaluate=False)
	
	else:
		return expression.subs(key,value)



"""
#Function to Simplify and Expand an expression using sympy
"""
def sub_ind_def(expression,variable,constant):
    if 'Implies' not in expression and 'ite' not in expression and '==' not in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
    	return expression.replace(variable,constant)
    elif 'Implies' in expression :
        axioms=extract_args(expression)
        #return 'Implies('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+')'
        return 'Implies('+axioms[0]+','+sub_ind_def(axioms[1],variable,constant)+')'
    elif 'ite' in expression:
        axioms=extract_args(expression)
        return 'If('+sub_ind_def(axioms[0],variable,constant)+','+sub_ind_def(axioms[1],variable,constant)+','+sub_ind_def(axioms[2],variable,constant)+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('==')
        if left is not None and right is not None:
        	if '%' in axioms[0]:
        		leftin =None
			rightin =None
        		leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
        		axm=axioms[0].split('%')
        		if left is not None and right is not None:
        			expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
        		else:
        			expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
        	
        	else:
        		expression=left+str(sub_ind_def(axioms[0]))+'=='+str(sub_ind_def(axioms[1]))+right
        		#expression=left+str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(powsimp(pow_to_mul(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	if '%' in axioms[0]:
			leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if left is not None and right is not None:
				expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
			else:
				expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
		        	
        	else:
        		expression=str(simplify_sympy(axioms[0]))+'=='+str(simplify_sympy(axioms[1]))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('!=')
        if left is not None and right is not None:
              	if '%' in axioms[0]:
	        	leftin =None
			rightin =None
	        	leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
	        	axm=axioms[0].split('%')
	        	if leftin is not None and rightin is not None:
	        		expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
	        	else:
        			expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
        	else:
        		expression=left+str(sub_ind_def(axioms[0],variable,constant))+'!='+str(sub_ind_def(axioms[1],variable,constant))+right
        		#expression=left+str(powsimp(pow_to_mul(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	 if '%' in axioms[0]:
		 	leftin =None
			rightin =None
			leftin,rightin,axioms[0]=parenthesesOrganizer( axioms[0] ,left ,right)
			axm=axioms[0].split('%')
			if leftin is not None and rightin is not None:
				expression=left+leftin+str(sub_ind_def(axm[0],variable,constant))+'%'+str(simplify_sympy(axm[1],variable,constant))+rightin+'=='+str(sub_ind_def(axioms[1],variable,constant))+right
			else:
		        	expression=left+str(sub_ind_def(axm[0],variable,constant))+'%'+str(sub_ind_def(axm[1],variable,constant))+'=='+str(sub_ind_def(axioms[1],variable,constant))+right

        	 else:
        		expression=str(sub_ind_def(axioms[0],variable,constant))+'!='+str(sub_ind_def(axioms[1],variable,constant))
        		#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    else:
        return  expression

		

"""
#Function to Simplify and Expand an expression using sympy
"""
def simplify_expand_for_int(expression):
    if 'Implies' not in expression and 'ite' not in expression and '==' not in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression and '<' not in  expression and '>' not in  expression:
        #return  str(pow_to_mul(powsimp(sympify(expression)).expand(basic=True)))
        exp=str(simplify_sympy(expression))
        if '/' in exp:
            no,deno=fraction(simplify(exp))
            no=powsimp(sympify(no).expand(basic=True))
            if deno==1:
                return "("+str(no)+")"
            else:
                return str(Mul(no, Pow(deno, -1), evaluate=False))
        else:
            return str(expression)
    elif 'Implies' in expression :
        axioms=extract_args(expression)
        return 'Implies('+simplify_expand_for_int(axioms[0])+','+simplify_expand_for_int(axioms[1])+')'
    elif 'ite' in expression:
        axioms=extract_args(expression)
        return 'If('+simplify_expand_for_int(axioms[0])+','+simplify_expand_for_int(axioms[1])+','+simplify_expand_for_int(axioms[2])+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('==')
        if left is not None and right is not None:
        	expression=left+str(simplify_expand_for_int(axioms[0]))+'=='+str(simplify_expand_for_int(axioms[1]))+right
        	#expression=left+str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(powsimp(pow_to_mul(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	expression=str(simplify_expand_for_int(axioms[0]))+'=='+str(simplify_expand_for_int(axioms[1]))
        	#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'=='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression:
        left =None
        right =None
        left,right,expression=parenthesesOrganizer( expression ,left ,right)
        axioms=expression.split('!=')
        if left is not None and right is not None:
        	expression=left+str(simplify_expand_for_int(axioms[0]))+'!='+str(simplify_expand_for_int(axioms[1]))+right
        	#expression=left+str(powsimp(pow_to_mul(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))+right
        else:
        	expression=str(simplify_expand_for_int(axioms[0]))+'!='+str(simplify_expand_for_int(axioms[1]))
        	#expression=str(pow_to_mul(powsimp(sympify(axioms[0])).expand(basic=True)))+'!='+str(pow_to_mul(powsimp(sympify(axioms[1])).expand(basic=True)))
        return expression
    else:
        return  expression

#Flag for Strategy Solving Recurrence Relations 

flag_stg_re_soln=0

constant_fun_map={}


# expr_replace(e,e1,e2): replace all subterm e1 in e by e2

#e=['a', ['implies', ['<', ['_n1'], ['_N1']], ['<', ['x2', ['_n1']], ['y2', ['_n1']]]]]

#e=['a', ['<', ['x2', ['_N1']], ['y2', ['_N1']]]]

def expr_complement(e): #e,e1,e2: expres
    if e[:1]==['<']:
    	e[:1]=['>=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['>']:
    	e[:1]=['<=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['>=']:
        e[:1]=['<']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['<=']:
        e[:1]=['>']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['==']:
        e[:1]=['!=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['!=']:
        e[:1]=['==']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['&&']:
        e[:1]=['||']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['||']:
        e[:1]=['&&']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['and']:
        e[:1]=['or']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['or']:
        e[:1]=['and']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    else:
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
""" 
#Function to replace variable by constant
#Test Case
#e=['a', ['<', ['x2', ['_n1']], ['y2', ['_n1']]]]
#variable='_n1'
#constant='_N1'
#expr_replace_const(e,variable,constant)
"""

def expr_replace_const(e,variable,constant):
	if e[:1]==expres(variable):
		e[:1]=expres(constant)
	return e[:1]+list(expr_replace_const(x,variable,constant) for x in expr_args(e))


#substituting close form solution in rest of the axiomes
def solnsubstitution(axioms,key,substituter):
	update_axioms=[]
    	for axiom in axioms:
    		if axiom[0]!='i0' and axiom[0]!='i1':
               		update_axioms.append(expr_replace(axiom,key,substituter))
    		else:
                        if axiom[0]=='i1':
                            axiom[4]=expr_replace(axiom[4],key,substituter)
                            update_axioms.append(axiom)
                        elif axiom[0]=='i0':
                            axiom[3]=expr_replace(axiom[3],key,substituter)
                            update_axioms.append(axiom)
                        else:
                            update_axioms.append(axiom)
    	return update_axioms

"""
#substituting key in substitutor by substitutor
"""

		
def substitution(key,substituter, substitutor):
	if 'ite' not in str(substituter) and 'ite' not in str(substitutor) :
		t=sympify(substitutor) 
		#Substituting 
		substitutor=t.subs(key, substituter)
		return substitutor
		
		
"""
Substituting key by substituter in substitutor

Example 1:

key="X1(n1)"

substituter="X+Y"

substitutor="X1(n1)+X+Y"


Example 1:

key="X1(n1)"

substituter="X+Y"

substitutor="X1(n1)>2&&(Y>=0||X>0)"


Example 2:

key="X1(n1)"

substituter="X+Y"

substitutor="X1(n1)>2&&((Y>=0||X>0))"


"""

def splitingExpressionForSub(key,substituter,substitutor):
	if '&&' in str(substitutor):
		substitutor=substitutor.strip()
		left=None
		right=None
		left,right,substitutor=parenthesesOrganizer(substitutor,left,right)
		tokens=substitutor.split('&&')
		expression=""
		for token in tokens:
			expression=splitingExpressionForSub(key,substituter,token)
		if left is not None:
			expression=left+expression
		if right is not None:
			expression=expression+right
		return expression
	elif '||' in str(substitutor):
		substitutor=substitutor.strip()
		left=None
		right=None
		left,right,substitutor=parenthesesOrganizer(substitutor,left,right)
		tokens=substitutor.split('||')
		expression=""
		for token in tokens:
			expression=splitingExpressionForSub(key,substituter,token)
		if left is not None:
			expression=left+expression
		if right is not None:
			expression=expression+right
		return expression
	else:
		substitutor=substitution(key,substituter, substitutor)
		return str(substitutor)

#Simplify set of axioms using a Expression (Without vfact )
"""
#Test Case 1
#axioms=['y1=Y','x1=X','y2=y1+1','x2=x1+3','y3=y2*3','x3=x2+1','x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))']
#expression='y1=Y'
#Test Case 2
#axioms=['y1=Y','x1=X','y2=y1+1','x2=x1+3','y3=y2*3','x3=x2+1','x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))']
#expression='x3=Y'
#Test Case 3
#axioms=['y1=Y','x1=X','y2=y1+1','x2=x1+3','y3=y2*3','x3=x2+1','x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))']
#expression='x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))'
"""
def fullySimplifyAxioms(expression,axioms):
	try:
		modifiedaxioms=[]
		if '=' in expression and '<' not in  expression and '>' not in expression and 'ite' not in expression:
			exp=expression.split('=')
			modifiedaxioms.append(expression)
			for axiom in axioms:
				if axiom != expression:
					if '=' in  str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '!' not in str(axiom) and '==' not in str(axiom) and 'ite' not in str(axiom):
						axm=axiom.split('=')
						#Substituting 
						axm[1]=splitingExpressionForSub(exp[0],exp[1],axm[1])
						modifiedaxioms.append(axm[0].strip()+" = "+str(axm[1]))
					elif '==' in  str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '!' not in str(axiom) and 'ite' not in str(axiom):
						axm=axiom.split('==')
						#Substituting 
						axm[1]=splitingExpressionForSub(exp[0],exp[1],axm[1])
						modifiedaxioms.append(axm[0].strip()+" == "+str(axm[1]))
					elif '!=' in  str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and 'ite' not in str(axiom):
						axm=axiom.split('!=')
						#Substituting 
						axm[1]=splitingExpressionForSub(exp[0],exp[1],axm[1])
						modifiedaxioms.append(axm[0].strip()+" != "+str(axm[1]))
					elif 'ite' in  str(axiom):					
						left_side_stmt_suber=tokzr_left_hand_stmt(axiom)
						equation=axiom.replace(left_side_stmt_suber,"")
						equation=equation.strip()
						equation=equation[equation.index('=')+1:len(equation)]
						eq_cond_map={}
						new_eq_cond_map={}
						ConvertITEToMap(equation,eq_cond_map)
						for condition in eq_cond_map:
							if condition is not None:
								tempcond=str(condition)
								temp=str(eq_cond_map[condition])
								#Substituting 
								tempcond=splitingExpressionForSub(exp[0],exp[1],tempcond)
								temp=splitingExpressionForSub(exp[0],exp[1],temp)
								new_eq_cond_map[tempcond]=temp
						temp=str(eq_cond_map[None])
						temp=splitingExpressionForSub(exp[0],exp[1],temp)
						new_eq_cond_map[None]=temp
						equation1=ConvertMapToITE(new_eq_cond_map)
						modifiedaxioms.append(left_side_stmt_suber.strip()+" = "+str(equation1))
						
					else:
						temp=sympify(axiom) 
						#Substituting 
						axiom=temp.subs(str(exp[0]),str(exp[1]))
						modifiedaxioms.append(axiom)
		else:
			for axiom in axioms:
				if axiom != expression:
					modifiedaxioms.append(axiom)
			modifiedaxioms.append(expression)
		return modifiedaxioms
	except ValueError:
		return ""
    
 


#Simplify Expression using a set of axioms (Without vfact )



def fullySimplifyExpression(expression,axioms):
	try:
		#exp = expression.split('=')
		for axiom in axioms:
			if '=' in axiom and '<' not in  axiom and '>' not in axiom and '!' not in axiom and 'ite' not in axiom:
				axm = axiom.split('=')
				temp=sympify(expression) 
				#Substituting 
				expression=splitingExpressionForSub(axm[0], axm[1],temp)
		return expression
	except ValueError:
                return ""




#Simplify set of axioms using a Expression (Without vfact )
"""
#Test Case 1
#axioms=['y1=Y','x1=X','y2=y1+1','x2=x1+3','y3=y2*3','x3=x2+1','x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))']
#expression='y1=Y'
#Test Case 2
#axioms=['y1=Y','x1=X','y2=y1+1','x2=x1+3','y3=y2*3','x3=x2+1','x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))']
#expression='x3=Y'
#Test Case 3
#axioms=['y1=Y','x1=X','y2=y1+1','x2=x1+3','y3=y2*3','x3=x2+1','x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))']
#expression='x4=ite(x3>10,x3**1,ite(x3>5,x3**y3,ite(x3>2,x3**2,x3**5)))'
"""
def fullySimplifyExpandAxioms(expression,axioms):
	try:
		modifiedaxioms=[]
		if '=' in expression and '<' not in  expression and '>' not in expression and 'ite' not in expression and '->' not in expression:
			exp=expression.split('=')
			modifiedaxioms.append(expression)
			for axiom in axioms:
				if axiom != expression:
					if '=' in  str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '!' not in str(axiom) and '==' not in str(axiom) and '->' not in str(axiom) and 'ite' not in str(axiom):
						axm=axiom.split('=')
						#Substituting 
						axm[1]=splitingExpressionForSub(exp[0],exp[1],axm[1])
						axm[1]=sympify(axm[1]).expand(basic=True)
						modifiedaxioms.append(axm[0].strip()+" = "+str(axm[1]))
					elif '==' in  str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '!' not in str(axiom) and '->' not in str(axiom) and 'ite' not in str(axiom):
						axm=axiom.split('==')
						#Substituting 
						axm[1]=splitingExpressionForSub(exp[0],exp[1],axm[1])
						axm[1]=sympify(axm[1]).expand(basic=True)
						modifiedaxioms.append(axm[0].strip()+" == "+str(axm[1]))
					elif '!=' in  str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '->' not in str(axiom) and 'ite' not in str(axiom):
						axm=axiom.split('!=')
						#Substituting 
						axm[1]=splitingExpressionForSub(exp[0],exp[1],axm[1])
						axm[1]=sympify(axm[1]).expand(basic=True)
						modifiedaxioms.append(axm[0].strip()+" != "+str(axm[1]))
					elif 'ite' in  str(axiom) and '->' not in str(axiom):					
						left_side_stmt_suber=tokzr_left_hand_stmt(axiom)
						equation=axiom.replace(left_side_stmt_suber,"")
						equation=equation.strip()
						equation=equation[equation.index('=')+1:len(equation)]
						eq_cond_map={}
						new_eq_cond_map={}
						ConvertITEToMap(equation,eq_cond_map)
						for condition in eq_cond_map:
							if condition is not None:
								tempcond=str(condition)
								temp=str(eq_cond_map[condition])
								#Substituting 
								tempcond=splitingExpressionForSub(exp[0],exp[1],tempcond)
								tempcond=sympify(tempcond).expand(basic=True)
								temp=splitingExpressionForSub(exp[0],exp[1],temp)
								temp=sympify(temp).expand(basic=True)
								new_eq_cond_map[tempcond]=temp
						temp=str(eq_cond_map[None])
						temp=splitingExpressionForSub(exp[0],exp[1],temp)
						temp=sympify(temp).expand(basic=True)
						new_eq_cond_map[None]=temp
						equation1=ConvertMapToITE(new_eq_cond_map)
						modifiedaxioms.append(left_side_stmt_suber.strip()+" = "+str(equation1))
					elif '->' in str(axiom):
						axms=axiom.split('->')
						#Substituting 
						axms[1]=splitingExpressionForSub(exp[0],exp[1],axms[1])
						axms[1]=sympify(axms[1]).expand(basic=True)
						modifiedaxioms.append(axms[0].strip()+" -> "+str(axms[1]))
					else:
						temp=sympify(axiom) 
						#Substituting 
						axiom=splitingExpressionForSub(exp[0],exp[1],temp)
						axiom=sympify(axiom).expand(basic=True)
						modifiedaxioms.append(axiom)
		else:
			for axiom in axioms:
				if axiom != expression:
					modifiedaxioms.append(axiom)
			modifiedaxioms.append(expression)
		return modifiedaxioms
	except ValueError:
		return ""
    
 

"""
Function to Take care of the parentheses During 

"""
def parenthesesOrganizer( substitutor ,left ,right):
	if left is None:
		left=""
	if right is None:
		right=""
	if substitutor[0]=="(":
		left=left+"("
		substitutor=substitutor[1:len(substitutor)]
		if substitutor[len(substitutor)-1]==")":
			right=right+")"
			substitutor=substitutor[0:len(substitutor)-1]
			#left,right,substitutor=parenthesesOrganizer(substitutor,left ,right)
		else:
			substitutor="("+substitutor
			left=left[0:len(left)-1]
	return left,right,substitutor



#Simplify Expression using a set of axioms (Without vfact )



def fullySimplifyExpandExpression(expression,axioms):
	try:
		#exp = expression.split('=')
		for axiom in axioms:
			if '=' in str(axiom) and '==' not in str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '!' not in str(axiom) and 'ite' not in str(axiom):
				axm = axiom.split('=')
				#Substituting
				if '==' in str(expression) and '<' not in  str(expression) and '>' not in str(expression) and '!' not in str(expression) and 'ite' not in str(expression):
                                    exp=str(expression).split('==')
                                    exp[0]=splitingExpressionForSub(axm[0], axm[1],exp[0])
                                    exp[0]=sympify(exp[0]).expand(basic=True)
                                    exp[1]=splitingExpressionForSub(axm[0], axm[1],exp[1])
                                    exp[1]=sympify(exp[1]).expand(basic=True)
                                    expression=str(exp[0])+"=="+str(exp[1])
                                else:
                                    if 'ite' not in str(expression):
                                        expression=splitingExpressionForSub(axm[0], axm[1],expression)
                                        expression=sympify(expression).expand(basic=True)
                        elif '==' in str(axiom) and '<' not in  str(axiom) and '>' not in str(axiom) and '!' not in str(axiom) and 'ite' not in str(axiom):
                                left=None
                                right=None
                                left,right,axiom=parenthesesOrganizer(axiom,left,right)
				axm = axiom.split('==')
				print axm[0]
				print axm[1]
				#Substituting
				if '==' in str(expression) and '<' not in  str(expression) and '>' not in str(expression) and '!' not in str(expression) and 'ite' not in str(expression):
                                    exp=str(expression).split('==')
                                    exp[0]=splitingExpressionForSub(axm[0], axm[1],exp[0])
                                    exp[0]=sympify(exp[0]).expand(basic=True)
                                    exp[1]=splitingExpressionForSub(axm[0], axm[1],exp[1])
                                    exp[1]=sympify(exp[1]).expand(basic=True)
                                    expression=str(exp[0])+"=="+str(exp[1])
                                    print expression
                                else:
                                    if 'ite' not in str(expression):
                                        expression=splitingExpressionForSub(axm[0], axm[1],expression)
                                        expression=sympify(expression).expand(basic=True)
                                
                return expression
	except ValueError:
                print "Ram"
                return ""



"""

#Organize Condition Map for Case analysis

"""
def organizeCondition(condition_map,unconditional_eq,vfact,inputmap):
        final_condition={}
	for condition in condition_map:
		if len(final_condition)==0:
			final_condition[condition]=condition_map[condition]
		else:
			status=False
			for update_condition in final_condition:
				equations1=[]
				equations2=[]
				for equation in unconditional_eq:
					equations1.append(equation)
					equations2.append(equation)

				equations1.append(update_condition)
				equations2.append(final_condition[update_condition])
				result_Status1=strategy1(equations1,condition,vfact,inputmap)
				result_Status2=strategy1(equations2,condition,vfact,inputmap)

                                if "Successfully Proved" in result_Status1 or "Successfully Proved" in result_Status2 :
                                    status=True
				
			if status==False:
				final_condition[condition]=condition_map[condition]
	return final_condition



"""
Parese a expression

#Example 1:
#expression="(((X > Y) || (Z <= Y)))"
#parseExpression(expression)
#['(', '(', '(', 'X', ' ', '>', ' ', 'Y', ')', ' ', '||', ' ', '(', 'Z', ' ', '<=', ' ', 'Y', ')', ')', ')']


"""

def parseExpression(expression):
	new_expression=[]
	operator=['!','=','<','>','&','|']
	token=""
	for ch in expression:
		if ch in operator:
			token+=ch
		else:
			if token!="":
				new_expression.append(token)
				token=""
			new_expression.append(ch)
	return new_expression


"""
Complement of The Expression

#expression="(((X > Y) || (Z <= Y)))"
#complementOfExpression(expression)
#(((X <= Y) && (Z > Y)))

"""

def complementOfExpression(expression):
	new_tokens=[]
	new_expression=""
	if expression !="" and expression is not None:
		tokens=parseExpression(expression)
		if len(tokens)!=0:
			for token in tokens:
				if token.strip()=='<=':
					new_tokens.append('>')
				elif token.strip()=='<':
					new_tokens.append('>=')
				elif token.strip()=='>=':
					new_tokens.append('<')
				elif token.strip()=='>':
					new_tokens.append('<=')
				elif token.strip()=='==':
					new_tokens.append('!=')
				elif token.strip()=='!=':
					new_tokens.append('==')
				elif token.strip()=='&&':
					new_tokens.append('||')
				elif token.strip()=='||':
					new_tokens.append('&&')
				else:
					new_tokens.append(token)
		if len(new_tokens)!=0:
			for token in new_tokens:
				if new_expression=="":
					new_expression=token
				else:
					new_expression+=token
		
	return new_expression

"""

#Get Complement of the operator

"""

def getOperatorCmpl(operator):
	if operator.strip()=='<=':
		return '>'
	elif operator.strip()=='<':
		return '>='
	elif operator.strip()=='>=':
		return '<'
	elif operator.strip()=='>':
		return '<='
	elif operator.strip()=='==':
		return '!='
	elif operator.strip()=='!=':
		return '=='
	elif operator.strip()=='&&':
		return '||'
	elif operator.strip()=='||':
		return '&&'
	else:
		return operator



"""
#Axiom Class
#Plain Python object to store Information about a Axiom
"""
class axiomclass(object):
 	def __init__(self, frame_axioms , output_equations , other_axioms, inputvariable, vfact, constraints, const_var_map):
        	self.frame_axioms = frame_axioms
        	self.output_equations = output_equations
        	self.other_axioms = other_axioms
        	self.inputvariable = inputvariable
        	self.vfact = vfact
        	self.constraints = constraints
        	self.const_var_map = const_var_map
        def getFrame_axioms(self):
        	return self.frame_axioms
        def getOutput_equations(self):
        	return self.output_equations
        def getOther_axioms(self):
        	return self.other_axioms
        def getInputvariable(self):
        	return self.inputvariable
        def getVfact(self):
        	return self.vfact
        def getConstraints(self):
        	return self.constraints
        def getConst_var_map(self):
        	return self.const_var_map


"""
#Sort Class
#Plain Python object to store Information about a Java  Class 
"""
class sortclass(object):
 	def __init__(self, sortname , varmap):
        	self.sortname = sortname
        	self.varmap = varmap
        def getSortname(self):
        	return self.sortname
        def getVarmap(self):
        	return self.varmap
        
        
"""

#Member Method Class
#Plain Python object to store Information about Member Method of a Java Class 
"""
class membermethodclass(object):
 	def __init__(self, methodname, returnType , inputvar, localvar):
        	self.methodname = methodname
        	self.inputvar = inputvar
        	self.returnType = returnType
        	self.localvar = localvar
        def getMethodname(self):
        	return self.methodname
        def getreturnType(self):
        	return self.returnType
        def getInputvar(self):
        	return self.inputvar
        def getLocalvar(self):
        	return self.localvar
        	
"""

#Expression Class
#Plain Python object to store Information about Java Expression 
"""
class expressionclass(object):
 	def __init__(self, expression, serialNo, isPrime, degree):
        	self.expression = expression
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpression(self):
        	return self.expression
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpression(self, expression):
		self.expression=expression
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
	def setDegree(self, degree):
		self.degree=degree


"""

#Block Class
#Plain Python object to store Information about Block of Java Expression 
"""
class blockclass(object):
 	def __init__(self, expression, predicate, serialNo ,isPrime ,degree):
        	self.expression = expression
        	self.predicate = predicate
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpression(self):
        	return self.expression
        def getPredicate(self):
        	return self.predicate
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpression(self, expression):
		self.expression=expression
	def setPredicate(self, predicate):
		self.predicate=predicate
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
       	def setDegree(self, degree):
		self.degree=degree


"""

#Block Class
#Plain Python object to store Information about if else Java Loop 
"""
class Ifclass(object):
 	def __init__(self, predicate, expressionif, expressionelse, serialNo ,isPrime ,degree):
        	self.predicate = predicate
        	self.expressionif = expressionif
        	self.expressionelse = expressionelse
        	self.serialNo = serialNo
        	self.isPrime = isPrime
        	self.degree = degree
        def getExpressionif(self):
        	return self.expressionif
        def getExpressionelse(self):
        	return self.expressionelse
        def getPredicate(self):
        	return self.predicate
        def getSerialNo(self):
        	return self.serialNo
        def getIsPrime(self):
        	return self.isPrime
        def getDegree(self):
        	return self.degree
        def setExpressionif(self, expressionif):
		self.expressionif=expressionif
	def setExpressionelse(self, expressionelse):
		self.expressionelse=expressionelse
	def setPredicate(self, predicate):
		self.predicate=predicate
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
	def setIsPrime(self, isPrime):
		self.isPrime=isPrime
       	def setDegree(self, degree):
		self.degree=degree


"""

Organization of AST 

"""
               
def organizeStatementToObject(statements):
	count=0
	degree=0
	expressions=[]
	for statement in statements:
		if type(statement) is m.Assignment:
			count=count+1
			expression=expressionclass(statement, count, True,degree)
			expressions.append(expression)
		elif type(statement) is m.While:
			if type(statement.predicate) is m.Unary:
				if type(statement.predicate.expression) is m.ConditionalOr:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate.expression) is m.ConditionalAnd:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate.expression) is m.Relational:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate.expression) is m.Equality:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
			elif type(statement.predicate) is m.ConditionalAnd:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
			elif type(statement.predicate) is m.ConditionalOr:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
			elif type(statement.predicate) is m.Relational:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
			elif type(statement.predicate) is m.Equality:
				blockexpressions=[]
				if statement.body is not None:
					degree=degree+1
					count,blockexpressions=blockToExpressions(statement.body, degree, count)
					degree=degree-1
				block=blockclass( blockexpressions, statement.predicate, count , True, degree)
				expressions.append(block)
		else:
			if type(statement) is m.IfThenElse:
				count,ifclass=ifclassCreator(statement, degree, count)
				expressions.append(ifclass)
					
     	return expressions		

"""

#Finding last expression or block inside a block

"""

def primeStatement(expressions):
	previous=None
	if type(expressions) is Ifclass:
		primeStatement(expressions.getExpressionif())
		primeStatement(expressions.getExpressionelse())
		previous=expressions
        else:
         	for expression in expressions:
	 		if previous is not None:
	 			previous.setIsPrime(False)
	 		if type(expression) is blockclass:
	 			primeStatement(expression.getExpression())
	 		if type(expression) is Ifclass:
	 			primeStatement(expression.getExpressionif())
	 			if expression.getExpressionelse() is not None:
	 				primeStatement(expression.getExpressionelse())
			previous=expression

"""

Converting code block,while loop ,conditional expression and expression to corresponding Classes

"""

def blockToExpressions(body, degree, count):
	expressions=[]
	if body is not None:
		for statement in body:
			if type(statement) is m.Assignment:
				count=count+1
				expression=expressionclass(statement, count, True,degree)
				expressions.append(expression)
			elif type(statement) is m.While:
				if type(statement.predicate) is m.Relational:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
				elif type(statement.predicate) is m.Equality:
					blockexpressions=[]
					if statement.body is not None:
						degree=degree+1
						count,blockexpressions=blockToExpressions(statement.body, degree, count)
						degree=degree-1
					block=blockclass( blockexpressions, statement.predicate, count , True, degree)
					expressions.append(block)
			else:
				if type(statement) is m.IfThenElse:
					count,ifclass=ifclassCreator(statement, degree, count)
					expressions.append(ifclass)
	return count,expressions



"""

Block of Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefination(expressions, allvariable):
	programsstart=""
	programsend=""
	statements=""
	for expression in expressions:
		if type(expression) is expressionclass:
			if type(expression.getExpression()) is m.Assignment:
				if type(expression.getExpression().lhs) is m.Name:
					var=expression.getExpression().lhs.value
					if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend="]"
						else:
							programsstart+=",['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend+="]"
					else:
                                                if programsstart=="":
                                                     programsstart+="['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                                                else:
                                                    programsstart+=",['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
		elif type(expression) is blockclass:
			predicatestmt="['-1','while',"+predicateCreator(expression.predicate)+","+programToinductiveDefination( expression.getExpression(), allvariable)+"]"
			if expression.getIsPrime()==False:
				if programsstart=="":
					programsstart="['-1','seq',"+predicatestmt
					programsend="]"
				else:
					programsstart+=",['-1','seq',"+predicatestmt
					programsend+="]"
			else:
				programsstart+=","+predicatestmt+programsend
		elif type(expression) is Ifclass:
			condition=predicateCreator(expression.predicate)
			expressionif=None
			expressionelse=None
			predicatestmt=""
			if expression.getExpressionif() is not None:
				expressionif=programToinductiveDefination( expression.getExpressionif(), allvariable)
			if expression.getExpressionelse() is not None:
				if type(expression.getExpressionelse()) is Ifclass:
					#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
					expressionelse=programToinductiveDefinationIfElse( expression.getExpressionelse(), allvariable)
				else:
					expressionelse=programToinductiveDefination( expression.getExpressionelse(), allvariable)
			if expressionif is not None and expressionelse is not None:
                          	predicatestmt="['-1','if2',"+condition+","+expressionif+","+expressionelse+"]"
			elif expressionif is not None and expressionelse is None:
				predicatestmt="['-1','if1',"+condition+","+expressionif+"]"
			if expression.getIsPrime()==False:
				if programsstart=="":
					programsstart="['-1','seq',"+predicatestmt
					programsend="]"
				else:
					programsstart+=",['-1','seq',"+predicatestmt
					programsend+="]"
			else:
				if programsstart=="":
					programsstart=predicatestmt+programsend
				else:
					programsstart+=","+predicatestmt+programsend
	return programsstart		


"""

IfElse Block Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefinationIfElse(expression, allvariable):
	programsstart=""
	programsend=""
	statements=""
	if type(expression) is expressionclass:
		if type(expression.getExpression()) is m.Assignment:
			if type(expression.getExpression().lhs) is m.Name:
				var=expression.getExpression().lhs.value
				if expression.getIsPrime()==False:
					if programsstart=="":
						programsstart="['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend="]"
					else:
						programsstart+=",['-1','seq',['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend+="]"
				else:
                                	if programsstart=="":
                                        	programsstart+="['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                                        else:
                                               	programsstart+=",['-1','=',expres('"+str(var)+"'),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
	elif type(expression) is blockclass:
		predicatestmt="['-1','while',"+predicateCreator(expression.predicate)+","+programToinductiveDefination( expression.getExpression(), allvariable)+"]"
		if expression.getIsPrime()==False:
			if programsstart=="":
				programsstart="['-1','seq',"+predicatestmt
				programsend="]"
			else:
				programsstart+=",['-1','seq',"+predicatestmt
				programsend+="]"
		else:
			if programsstart=="":
				programsstart+=","+predicatestmt+programsend
			
	elif type(expression) is Ifclass:
		condition=predicateCreator(expression.predicate)
		expressionif=None
		expressionelse=None
		predicatestmt=""
		if expression.getExpressionif() is not None:
			expressionif=programToinductiveDefination( expression.getExpressionif(), allvariable)
		if expression.getExpressionelse() is not None:
			if type(expression.getExpressionelse()) is Ifclass:
				#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
				expressionelse=programToinductiveDefinationIfElse( expression.getExpressionelse(), allvariable)
			else:
				expressionelse=programToinductiveDefination( expression.getExpressionelse(), allvariable)
		if expressionif is not None and expressionelse is not None:
                	predicatestmt="['-1','if2',"+condition+","+expressionif+","+expressionelse+"]"
		elif expressionif is not None and expressionelse is None:
			predicatestmt="['-1','if1',"+condition+","+expressionif+"]"
		if expression.getIsPrime()==False:
			if programsstart=="":
				programsstart="['-1','seq',"+predicatestmt
				programsend="]"
			else:
				programsstart+=",['-1','seq',"+predicatestmt
				programsend+="]"
		else:
			if programsstart=="":
				programsstart=predicatestmt+programsend
			else:
				programsstart+=","+predicatestmt+programsend
 	return programsstart
"""

Conditionl Expression of If Loop or While Loop to a Array of Statement Compatible to Translator Program 

"""
    
def predicateCreator(statement):
	expression=""
	if type(statement) is m.Unary:
		if type(statement.expression) is m.Relational:
			if type(statement.expression.lhs) is m.Name:
		    		expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
		    	elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.Equality:
			if type(statement.expression.lhs) is m.Name:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
			elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+getOperatorCmpl(statement.expression.operator)+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
    		elif type(statement.expression) is m.ConditionalOr:    
			expression+="['and',"+predicateCreatorCmpl(statement.expression.lhs)+","+predicateCreatorCmpl(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.ConditionalAnd:    
	    		expression+="['or',"+predicateCreatorCmpl(statement.expression.lhs)+","+predicateCreatorCmpl(statement.expression.rhs)+"]"
	elif type(statement) is m.Relational:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
    			expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    		else:
    			expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    	elif type(statement) is m.Equality:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+statement.operator+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
		    	expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
		else:
    			expression+="['"+statement.operator+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
	elif type(statement) is m.ConditionalOr:    
	    	expression+="['or',"+predicateCreator(statement.lhs)+","+predicateCreator(statement.rhs)+"]"
	elif type(statement) is m.ConditionalAnd:    
	    	expression+="['and',"+predicateCreator(statement.lhs)+","+predicateCreator(statement.rhs)+"]"
	return expression
	


"""

Program Expression to a Array of Statement Compatible to Translator Program 

"""

def expressionCreator(statement):
    expression=""
    if type(statement) is m.Name:
    	expression+="expres('"+statement.value+"')"
    elif type(statement) is m.Literal:
    	expression+="expres('"+statement.value+"')"
    elif type(statement) is m.MethodInvocation:
    	function=""
    	parameter=""
    	for argument in statement.arguments:
    		if parameter=="":
    			parameter=expressionCreator(argument)
    		else:
    			parameter+=","+expressionCreator(argument)
    	if "power"==statement.name:
    		function="['**',"+parameter+"]"
    	else:
		function="['"+statement.name+"',"+parameter+"]"
    	expression+=function
    elif type(statement) is m.Unary:
    	expression+="['-',"+expressionCreator(statement.expression)+"]"
    else:
    	if type(statement.lhs) is m.Name:
        	expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
    	elif type(statement.lhs) is m.Literal:
    		expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
    	else:
        	if type(statement.lhs) is m.Additive:
            		expression+="expres('"+statement.operator+"',["+expressionCreator(statement.lhs)
        	else :
            		expression+="expres('"+statement.operator+"',["+expressionCreator(statement.lhs)
    	if type(statement.rhs) is m.Name:
        	expression+=",expres('"+statement.rhs.value+"')])"
    	elif type(statement.rhs) is m.Literal:
        	expression+=",expres('"+statement.rhs.value+"')])"
    	else:
        	if type(statement.rhs) is m.Additive:
        		expression+=","+expressionCreator(statement.rhs)+"])"
        	else :
        		expression+=","+expressionCreator(statement.rhs)+"])"
    return expression
    
 


"""
 
Program Expression to Collect literal parameters
 
"""
 
def expressionCollectConstant(statement,fun_parameter):
     expression=""
     if type(statement) is m.Name:
     	expression+=statement.value
     elif type(statement) is m.Literal:
     	expression+=statement.value
     elif type(statement) is m.MethodInvocation:
     	function=""
     	parameter=""
     	key=None
     	if "power"==statement.name:
		function="['**',"+parameter+"]"
	else:
		key=statement.name
 		function="['"+statement.name+"',"+parameter+"]"
     	parameterlist=[]
     	for argument in statement.arguments:
     		if parameter=="":
     			parameter=expressionCollectConstant(argument,fun_parameter)
     			if '_n' not in parameter:
     				parameterlist.append(parameter)     				
     		else:
     			parameterstr=expressionCollectConstant(argument,fun_parameter)
     			parameter+=","+expressionCollectConstant(argument,fun_parameter)
     			if '_n' not in parameterstr:
     				parameterlist.append(parameterstr)
     				
     	if key is not None:
     		fun_parameter[key]=parameterlist
     	expression+=function
     elif type(statement) is m.Unary:
     	expression+="['-',"+expressionCollectConstant(statement.expression,fun_parameter)+"]"
     else:
     	if type(statement.lhs) is m.Name:
         	expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
     	elif type(statement.lhs) is m.Literal:
     		expression+="expres('"+statement.operator+"',[expres('"+statement.lhs.value+"')"
     	else:
         	if type(statement.lhs) is m.Additive:
             		expression+="expres('"+statement.operator+"',["+expressionCollectConstant(statement.lhs,fun_parameter)
         	else :
             		expression+="expres('"+statement.operator+"',["+expressionCollectConstant(statement.lhs,fun_parameter)
     	if type(statement.rhs) is m.Name:
         	expression+=",expres('"+statement.rhs.value+"')])"
     	elif type(statement.rhs) is m.Literal:
         	expression+=",expres('"+statement.rhs.value+"')])"
     	else:
         	if type(statement.rhs) is m.Additive:
         		expression+=","+expressionCollectConstant(statement.rhs,fun_parameter)+"])"
         	else :
         		expression+=","+expressionCollectConstant(statement.rhs,fun_parameter)+"])"
     return expression
   


	
"""

Complement of Conditionl Expression of If Loop or While Loop to a Array of Statement Compatible to Translator Program 

"""
    
def predicateCreatorCmpl(statement):
	expression=""
	if type(statement) is m.Unary:
		if type(statement.expression) is m.Relational:
			if type(statement.expression.lhs) is m.Name:
		    		expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
		    	elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
    		if type(statement.expression) is m.Equality:
			if type(statement.expression.lhs) is m.Name:
				expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
			elif type(statement.expression.lhs) is m.Literal:
    				expression+="['"+statement.expression.operator+"',expres('"+statement.expression.lhs.value+"'),"+expressionCreator(statement.expression.rhs)+"]"
    			elif type(statement.expression.lhs) is m.Additive:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
			else:
				expression+="['"+statement.expression.operator+"',"+expressionCreator(statement.expression.lhs)+","+expressionCreator(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.ConditionalOr:    
			expression+="['and',"+predicateCreator(statement.expression.lhs)+","+predicateCreator(statement.expression.rhs)+"]"
		elif type(statement.expression) is m.ConditionalAnd:    
	    		expression+="['or',"+predicateCreator(statement.expression.lhs)+","+predicateCreator(statement.expression.rhs)+"]"
	elif type(statement) is m.Relational:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
		    	expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
		else:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    	elif type(statement) is m.Equality:    
    		if type(statement.lhs) is m.Name:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Literal:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',expres('"+statement.lhs.value+"'),"+expressionCreator(statement.rhs)+"]"
    		elif type(statement.lhs) is m.Additive:
			expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
		else:
    			expression+="['"+getOperatorCmpl(statement.operator)+"',"+expressionCreator(statement.lhs)+","+expressionCreator(statement.rhs)+"]"
    	elif type(statement) is m.ConditionalOr:    
		expression+="['and',"+predicateCreatorCmpl(statement.lhs)+","+predicateCreatorCmpl(statement.rhs)+"]"
	elif type(statement) is m.ConditionalAnd:    
		expression+="['or',"+predicateCreatorCmpl(statement.lhs)+","+predicateCreatorCmpl(statement.rhs)+"]"
	
	return expression



"""

Conditionl Loop to a Array of Statement Compatible to Translator Program 
IfClass Creator

"""

def ifclassCreator(statement, degree, count):
	if type(statement.predicate) is m.Relational:
		predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.Equality:
            	predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.ConditionalOr:
	        predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.ConditionalAnd:
		predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	elif type(statement.predicate) is m.Unary:
		predicate=statement.predicate
		blockexpressions1=None
		blockexpressions2=None
		if type(statement.if_true) is m.Block:
			count,blockexpressions1=blockToExpressions(statement.if_true, degree, count)
		if type(statement.if_false) is m.Block:
			count,blockexpressions2=blockToExpressions(statement.if_false, degree, count)
		elif type(statement.if_false) is m.IfThenElse:
			count,blockexpressions2=ifclassCreator(statement.if_false, degree, count)
	ifclass=Ifclass(predicate, blockexpressions1, blockexpressions2, count ,True ,degree)
	return count,ifclass
	
	

"""

Convert Program to Logic 

"""
  
def convertToAST():
	p = getParser()
	#tree = p.parse_file("lcm2.java")ge
	#tree = p.parse_file("testp/lcm2.java")
	#tree = p.parse_file("sqrt.java")
	#tree = p.parse_file("Utils5.java")
	#tree = p.parse_file("benchmark/cubes_Cohen.java")
	tree = p.parse_file("benchmark/cohendiv.java")
	#tree = p.parse_file("TestCases/cohendiv.java")

	
	sort=None
	if tree is None:
		print "Error present in code. Please verify you input file"
		return

	for type_decl in tree.type_declarations:
                #sort=sortclass(type_decl.name)
                #print type_decl.name
                if type_decl.extends is not None:
                        print(' -> extending ' + type_decl.extends.name.value)
                menbermap={}
                menbermethods=[]
                returnType=None
                for field_decl in [decl for decl in type_decl.body if type(decl) is m.FieldDeclaration]:
                        for var_decl in field_decl.variable_declarators:
                                if type(field_decl.type) is str:
                                        type_name = field_decl.type
                                else:
                                        type_name = field_decl.type.name.value
                                menbermap[var_decl.variable.name]=type_name
                for method_decl in [decl for decl in type_decl.body if type(decl) is m.MethodDeclaration]:
                        parametermap={}
                        returnType=None
                        localvarmap={}
                        statements=[]
                        if type(method_decl.return_type) is str:
                                returnType=method_decl.return_type
                        else:
                                returnType=method_decl.return_type.name.value
                        
                        for param in method_decl.parameters:
                                if type(param.type) is str:
                                        parametermap[param.variable.name]=param.type
                                else:
                                        parametermap[param.type.name.value]=param.type
                        if method_decl.body is not None:
                                for statement in method_decl.body:
                                # note that this misses variables in inner blocks such as for loops
                                # see symbols_visitor.py for a better way of handling this
                                        if type(statement) is m.VariableDeclaration:
                                                for var_decl in statement.variable_declarators:
                                                        if type(statement.type) is str:
                                                                type_name = statement.type
                                                        else:
                                                                type_name = statement.type.name.value
                                                        localvarmap[var_decl.variable.name]=type_name
                                        else:
                                        	statements.append(statement)
                        membermethod=membermethodclass(method_decl.name,returnType,parametermap,localvarmap)
                        menbermethods.append(membermethod)
                allvariable={}
                sort=sortclass(type_decl.name, menbermap)
                if sort is not None:
			print " Class Name:"
			print sort.getSortname()
			print " Class Variables:"
			print sort.getVarmap()
			for membermethod in menbermethods:
				print "Method Name:"
		        	print membermethod.getMethodname()
		        	print "Return Type:"
		                print membermethod.getreturnType()
		                print "Input Variables:"
		                print membermethod.getInputvar()
		                print "Local Variables:"
                                print membermethod.getLocalvar()
                                for x in membermethod.getInputvar():
                                	allvariable[x]=membermethod.getInputvar()[x]
                                for x in membermethod.getLocalvar():
                                	allvariable[x]=membermethod.getLocalvar()[x]
                if validationOfInput(allvariable)==True:
          		print "Please Rename variable Name {S,Q} to other Name"
          		return               	
                print "All Variables:"
                print allvariable
                expressions=organizeStatementToObject(statements)
                primeStatement(expressions)
                variablesarray={}
                opvariablesarray={}
                count=0
                for variable in allvariable:
                	count+=1
                	variablesarray[variable]=eval("['_y"+str(count)+"','"+allvariable[variable]+"']")
                	opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+allvariable[variable]+"']")
                program=eval(programToinductiveDefination(expressions , allvariable))
                print ""
                print "Output of The Translator Written By Prof Lin"
                print ""
                print "Inputs to Translator"
                print "Parameter One:"
                print program
                print "Parameter Two:"
                print variablesarray
                print "Parameter Two Three:"
                print 1
                f,o,a=translate1(program,variablesarray,1)
               	frame_axioms=eqset2constraintlist(f)
		out_axioms=eqset2constraintlist(o)
		other_out_axioms=[]
		for x in a: 
        		other_out_axioms.append(wff2z3(x))
                for x in frame_axioms:
                    print x
                for x in out_axioms:
                    print x
                for x in other_out_axioms:
                    print x



"""

Translate Program to Logic 

#file_name='Utils7.java'

#file_name='cohendiv.java'

#file_name='sample3.java'

#file_name='benchmark/sqrt.java'

#flag=1

#file_name='benchmark/Utils1.java'

#file_name='TestCases/cubes_Cohen.java'

flag=2

#file_name='sqrt.java'

#file_name='benchmark/cohendiv.java'

#axiom=translate(file_name)

"""
  
def translate(file_name):
	if not(os.path.exists(file_name)): 
		print "File not exits"
		return

	start_time=current_milli_time()
	p = getParser()
	#tree = p.parse_file("Utils7.java")
	tree = p.parse_file(file_name)
	writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Translate \n"+"\nParameters--\n File Name--"+file_name+"\n")
	if tree is None:
		print "Error present in code. Please verify you input file"
		return
	sort=None
	for type_decl in tree.type_declarations:
                #sort=sortclass(type_decl.name)
                print type_decl.name
                if type_decl.extends is not None:
                        print(' -> extending ' + type_decl.extends.name.value)
                menbermap={}
                menbermethods=[]
                returnType=None
                for field_decl in [decl for decl in type_decl.body if type(decl) is m.FieldDeclaration]:
                        for var_decl in field_decl.variable_declarators:
                                if type(field_decl.type) is str:
                                        type_name = field_decl.type
                                else:
                                        type_name = field_decl.type.name.value
                                menbermap[var_decl.variable.name]=type_name
                for method_decl in [decl for decl in type_decl.body if type(decl) is m.MethodDeclaration]:
                        parametermap={}
                        returnType=None
                        localvarmap={}
                        statements=[]
                        if type(method_decl.return_type) is str:
                                returnType=method_decl.return_type
                        else:
                                returnType=method_decl.return_type.name.value
                        
                        for param in method_decl.parameters:
                                if type(param.type) is str:
                                        parametermap[param.variable.name]=param.type
                                else:
                                        parametermap[param.type.name.value]=param.type
                        if method_decl.body is not None:
                                for statement in method_decl.body:
                                # note that this misses variables in inner blocks such as for loops
                                # see symbols_visitor.py for a better way of handling this
                                        if type(statement) is m.VariableDeclaration:
                                                for var_decl in statement.variable_declarators:
                                                        if type(statement.type) is str:
                                                                type_name = statement.type
                                                        else:
                                                                type_name = statement.type.name.value
                                                        localvarmap[var_decl.variable.name]=type_name
                                        else:
                                        	statements.append(statement)
                        membermethod=membermethodclass(method_decl.name,returnType,parametermap,localvarmap)
                        menbermethods.append(membermethod)
                allvariable={}
                sort=sortclass(type_decl.name, menbermap)
                if sort is not None:
			print " Class Name:"
			print sort.getSortname()
			print " Class Variables:"
			print sort.getVarmap()
			for membermethod in menbermethods:
				print "Method Name:"
		        	print membermethod.getMethodname()
		        	print "Return Type:"
		                print membermethod.getreturnType()
		                print "Input Variables:"
		                print membermethod.getInputvar()
		                print "Local Variables:"
                                print membermethod.getLocalvar()
                                for x in membermethod.getInputvar():
                                	allvariable[x]=membermethod.getInputvar()[x]
                                for x in membermethod.getLocalvar():
                                	allvariable[x]=membermethod.getLocalvar()[x]
                                	
          	if validationOfInput(allvariable)==True:
          		print "Please Rename variable Name {S,Q} to other Name"
          		return
                print "All Variables:"
                print allvariable
                expressions=organizeStatementToObject(statements)
                primeStatement(expressions)
                variablesarray={}
                opvariablesarray={}
                count=0
                for variable in allvariable:
                	count+=1
                	variablesarray[variable]=eval("['_y"+str(count)+"','"+allvariable[variable]+"']")
                	opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+allvariable[variable]+"']")
                program=eval(programToinductiveDefination(expressions , allvariable))
                print ""
                print "Output of The Translator Written By Prof Lin"
                print ""
                print "Inputs to Translator"
                print "Parameter One:"
                print program
                print "Parameter Two:"
                print variablesarray
                print "Parameter Two Three:"
                print 1             
                f,o,a,cm=translate1(program,variablesarray,1)
                vfacts,constraints=getVariFunDetails(f,o,a,allvariable,opvariablesarray)
                end_time=current_milli_time()
                print "Times to Translate"
                print end_time-start_time
                writeLogFile( "j2llogs.logs" , getTimeStamp()+"\n End of Translation\n")
                axiom=axiomclass(f,o,a,membermethod.getInputvar(), vfacts, constraints,cm)
                return axiom

 
"""
Prove command used to prove post condition of a program 
#Input 1--source code file name(file_name) 
#Input 2--precondition for program to prove (pre_condition) 
#Input 3--postcondition of program (post_condition) 
#Input 4--Flag to choose strategy used to prove  post condition using z3(flag) 
	#flag=1 represent the strategy in which system will directly translate program and pass to z3 to prove conclusion (waiting times for result 6000 ms)
	#flag=2 represent the strategy in which system will directly translate program and change all the occurrences  of power operator by power function and pass to z3 to prove conclusion
	#flag=3 represent the strategy in which system simplify each translate equation and conlusion by using sympy and pass to z3 to prove conclusion
	#flag=4 represent the strategy in which system will directly translate program and pass to z3 to prove conclusion using tactic 'qfnra-nlsat'

file_name='Utils7.java'
pre_condition=['a>0']
post_condition=['a>0']
flag=1
#Test Case -- prove(file_name,pre_condition,post_condition,flag)
file_name='sample.java'
pre_condition=['a>0']
post_condition=['z1==2*a+5']
flag=1

file_name='sample2.java'
pre_condition=['a>0']
post_condition=['a>0']
flag=1


file_name='benchmark/cohendiv.java'
pre_condition=['X>0']
post_condition=['X>0']
flag=1


pre_condition=['X>=0','Y>0']
post_condition=['X==Y*q1+r1']
flag=2
prove(axiom,pre_condition,post_condition,flag)

"""


def prove(axiom,pre_condition,post_condition,flag):
	if len(post_condition)==0:
		print "Nothing To Prove"
		return
	if axiom is not None and post_condition is not None and flag>0 and flag<5:
	        if flag==1:
	        	writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Direct")
                	start_time=current_milli_time()
                	tactic1(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints())
                	end_time=current_milli_time()
                	print "Times to Get Result"
                	print end_time-start_time
                elif flag==2:
                	writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Induction")
                	start_time=current_milli_time()
			tactic2(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
			end_time=current_milli_time()
			print "Times to Get Result"
                	print end_time-start_time
                elif flag==3:
		        writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Induction")
		        start_time=current_milli_time()
			tactic3(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
			end_time=current_milli_time()
			print "Times to Get Result"
                	print end_time-start_time
                elif flag==4:
			writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Induction")
			start_time=current_milli_time()
			tactic4(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
			end_time=current_milli_time()
			print "Times to Get Result"
                	print end_time-start_time
                writeLogFile( "j2llogs.logs" , getTimeStamp()+"\n End of Proof\n")
              





"""

Strategy 2  ----> 1.Directly translate axoimes to z3 constraint 2.Change  exponential operator ** to power function

"""
def query2z3(constraint_list,conclusion,vfact,inputmap):
	pythonProgram="from z3 import *\n"
	pythonProgram+="set_param(proof=True)\n"
	pythonProgram+="_p1=Int('_p1')\n"
	pythonProgram+="_p2=Int('_p2')\n"
	status=""
	for [x,k,l] in vfact:
		if k==0:
			if l[0]=="int":
				if '_N' in x:
					pythonProgram+=x+"=Const(\'"+x+"\',IntSort())\n"
				else:				
					pythonProgram+=x+"=Int(\'"+x+"\')\n"
			elif l[0]=="double":
				pythonProgram+=x+"=Real(\'"+x+"\')\n"
			elif l[0]=="float":
				pythonProgram+=x+"=Real(\'"+x+"\')\n"
			elif l[0]=="constant":
				pythonProgram+=x+"=Const(\'"+x+"\',IntSort())\n"
			else:
				pythonProgram+=x+"=Bool(\'"+x+"\')\n"
		else:
			pythonProgram+=x+"=Function(\'"+x+"\'"
			for e in l:
				if e=="int":
					pythonProgram+=",IntSort()"
				else:
					pythonProgram+=",RealSort()"
			pythonProgram+=")\n"
	pythonProgram+="power=Function(\'power\',IntSort(),IntSort(),IntSort())\n"
	pythonProgram+="_s=Solver()\n"
	#pythonProgram+="_s.add(ForAll(x,Implies(x>0,power(x, 0)==1)))\n"
	#pythonProgram+="_s.add(ForAll([x,y],Implies(And(x>0,y>0),power(x, y)==power(x, y-1)*x)))\n"
	#pythonProgram+="_s.set(mbqi=True)\n"
        pythonProgram+="_s.add(ForAll([_p1],Implies(_p1>=0, power(0,_p1)==0)))\n"
        pythonProgram+="_s.add(ForAll([_p1,_p2],Implies(power(_p2,_p1)==0,_p2==0)))\n"
        pythonProgram+="_s.add(ForAll([_p1],Implies(_p1>0, power(_p1,0)==1)))\n"
        pythonProgram+="_s.add(ForAll([_p1,_p2],Implies(power(_p1,_p2)==1,Or(_p1==1,_p2==0))))\n"
        pythonProgram+="_s.add(ForAll([_p1,_p2],Implies(And(_p1>0,_p2>=0), power(_p1,_p2+1)==power(_p1,_p2)*_p1)))\n"      


	pythonProgram+="_s.set(\"timeout\","+str(TIMEOUT)+")\n"
	for equation in constraint_list:
		pythonProgram+="_s.add("+str(equation)+")\n"
	finalProgram=pythonProgram
	finalProgram+="_s.add(Not("+str(translatepowerToFun(conclusion))+"))\n"
	finalProgram+="if sat==_s.check():\n"+"\tprint \"Counter Example\"\n"+"\tprint _s.model()\n"+"elif unsat==_s.check():\n"+"\t_s.check()\n"+"\tif os.path.isfile(\'j2llogs.logs\'):\n"+"\t\tfile = open(\'j2llogs.logs\', \'a\')\n"+"\t\tfile.write(\"\\n**************\\nProof Details\\n**************\\n\"+str(_s.proof().children())+\"\\n\")\n"+"\t\tfile.close()\n"+"\telse:\n"+"\t\tfile = open(\'j2llogs.logs\', \'w\')\n"+"\t\tfile.write(\"\\n**************\\nProof Details\\n**************\\n\"+str(_s.proof().children())+\"\\n\")\n"+"\t\tfile.close()\n"+"\tprint \"Successfully Proved\"\n"+"else:\n"+"\tprint \"Failed To Prove\""
	#finalProgram+="if sat==_s.check():\n"+"\tprint \"Counter Example\"\n"+"\tprint _s.model()\n"+"elif unsat==_s.check():\n"+"\t_s.check()\n"+"\tprint \"Successfully Proved\"\n"+"else:\n"+"\tprint \"Failed To Prove\""
	#print finalProgram
	writtingFile( "z3query.py" , finalProgram )
	writeLogFile( "j2llogs.logs" , "\nQuery to z3 \n"+str(finalProgram)+"\n" )
	proc = subprocess.Popen('python z3query.py', stdout=subprocess.PIPE,shell=True)
	output = proc.stdout.read()
	status=output
	return status




"""

Tactic 1  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove conclusion 3.waited for 6000

"""
def tactic1(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints):
	constraint_list=[]
	frame_axioms=eqset2constraintlist(f)
	for x in frame_axioms:
		constraint_list.append(x)
	out_axioms=eqset2constraintlist(o)
	subs_list=eqset2subs_list(o)
	for x in out_axioms:
		constraint_list.append(x)
	for x in a: 
            constraint_list.append(wff2z3(x))
	for x in constaints:
		constraint_list.append(x)
	for x in pre_condition:
        	constraint_list.append(x)
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		conclusion=simplify_conclusion(conclusion,subs_list)	
		if "factorial" in conclusion:
			cfact=eval("['factorial',1,['int','int']]")
			vfact.append(cfact)
		
		status=query2z3(constraint_list,conclusion,vfact,inputmap)
		writeLogFile( "j2llogs.logs" ,"\nResult \n"+str(status)+"\n" )
		if "Successfully Proved" in status:
			print "Successfully Proved"			
		elif "Counter Example" in status:
			tactic4(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints)			
		else:
			print "Failed to Prove"
			



"""

Tactic 2  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove using induction on loop variable 

"""
def tactic2(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints,const_var_map):
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		subs_list=eqset2subs_list(o)
		conclusion=simplify_conclusion(conclusion,subs_list)
		variable=None
		constant=None
		const_map={}
		var_const_map={}
		count=0
		for cm in const_var_map:
			if const_var_map[cm] in conclusion:
				count=count+1
				const_map[const_var_map[cm]]=cm
				var_const_map[cm]="_k"+str(count)
		constraint_list=[]
		frame_axioms=eqset2constraintlist(f)
		for x in frame_axioms:
			constraint_list.append(x)
		out_axioms=eqset2constraintlist(o)
		
		for x in out_axioms:
			constraint_list.append(x)
		for x in a: 
			constraint_list.append(wff2z3(x))
		for x in constaints:
			constraint_list.append(x)
		for x in pre_condition:
        		constraint_list.append(x)
		update_vfact=[]
		for [x,k,l] in vfact:
			if x in const_map.values():
				if k==0:
					ul=['constant']
					update_vfact.append([var_const_map[x],k,ul])
					update_vfact.append([x,k,l])
				else:
					update_vfact.append([var_const_map[x],k,l])
					update_vfact.append([x,k,l])
			else:
				update_vfact.append([x,k,l])
		
	
		for x in const_map:
			variable=var_const_map[const_map[x]]			
			constant=x
			loop_var=const_map[x]
			if '==' in str(conclusion) and '<' not in  str(conclusion) and '>' not in str(conclusion) and '!' not in str(conclusion) and 'ite' not in str(conclusion):
				exp=str(conclusion).split('==')
				invariantstmtdisplay=str(simplify(exp[0]).subs(constant,const_map[x]))+"=="+str(simplify(exp[1]).subs(constant,const_map[x]))
				exp[0]=simplify(exp[0]).subs(constant,variable)
				exp[1]=simplify(exp[1]).subs(constant,variable)
				invariantstmt=str(exp[0])+"=="+str(exp[1])
				exp[0]=simplify(exp[0]).subs(variable,0)
				exp[1]=simplify(exp[1]).subs(variable,0)
				basecasestmt=str(exp[0])+"=="+str(exp[1])
			else:
				invariantstmt=simplify(conclusion).subs(constant,variable)
				invariantstmtdisplay=simplify(conclusion).subs(constant,const_map[x])
				basecasestmt=simplify(invariantstmt).subs(variable,0)
			print " Try to prove following using induction on "+const_map[x]
			print "ForAll("+const_map[x]+","+str(invariantstmtdisplay)+")"
			print "Base Case"
			if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt):
				exp=str(invariantstmt).split('==')
				exp[0]=simplify(exp[0]).subs(variable,0)
				exp[1]=simplify(exp[1]).subs(variable,0)
				basecasestmt=str(exp[0])+"=="+str(exp[1])
			else:
				basecasestmt=simplify(invariantstmt).subs(variable,0)
			print basecasestmt
			writeLogFile( "j2llogs.logs" , "\nBase Case \n"+str(basecasestmt)+"\n" )
			status=query2z3(constraint_list,str(basecasestmt),update_vfact,inputmap)
			#status=query2z3(constraint_list,str(basecasestmt),vfact,inputmap)
			writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
			if "Successfully Proved" in status:
				print "Successfully Proved"
				print "Inductive Step"
				print "Inductive Assumption"
				print invariantstmt
				updated_equation=[]
				updated_vfact=[]
				if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt):
					exp=str(invariantstmt).split('==')
					lexp=simplify(exp[0])
					rexp=simplify(exp[1])
					inductiveassum=str(lexp)+"=="+str(rexp)
					lexp=simplify(exp[0]).subs(variable,variable+"+1")
					rexp=simplify(exp[1]).subs(variable,variable+"+1")
					ind_def_map=eqset2subs_list_ind(a)
					for i_e in ind_def_map:
                                            lexp=sub_ind_def(str(lexp),sub_ind_def(str(i_e),loop_var,variable),'('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')')
                                            rexp=sub_ind_def(str(rexp),sub_ind_def(str(i_e),loop_var,variable),'('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')')
					inductivestep='Implies('+str(inductiveassum)+','+str(lexp)+"=="+str(rexp)+')'
				else:
					inductiveassum=simplify(invariantstmt)
					inductivestep=simplify(invariantstmt).subs(variable,variable+"+1")
					ind_def_map=eqset2subs_list_ind(a)
					temp_inductivestep=str(inductivestep)
					for i_e in ind_def_map:
						temp_inductivestep=sub_ind_def(temp_inductivestep,sub_ind_def(str(i_e),loop_var,variable),sub_ind_def(str(ind_def_map[i_e]),loop_var,variable))
					inductivestep='Implies('+str(inductiveassum)+','+temp_inductivestep+')'
				for equation in constraint_list:
					updated_equation.append(equation)
				updated_equation.append(variable+">=0")
				#updated_equation.append(inductiveassum)
				writeLogFile( "j2llogs.logs" ,"\nInductive Step \n"+str(inductivestep)+"\n" )
				status=query2z3(updated_equation,str(inductivestep),update_vfact,inputmap)
				#status=query2z3(updated_equation,str(inductivestep),vfact,inputmap)
				writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
				if "Successfully Proved" in status:
					print "Successfully Proved"
					return 
				elif "Counter Example" in status:
					constraint_list=[]
					frame_axioms=eqset2constraintlist(f)
					for x in frame_axioms:
						constraint_list.append(x)
					out_axioms=eqset2constraintlist(o)
					for x in out_axioms:
						constraint_list.append(x)
					for x in a:
						 equations=wff2z3Stronger(x)
						 if type(equations) is list:
						 	for equation in equations:                    
						        	constraint_list.append(equation)
						 elif type(equations) is str:
                					constraint_list.append(equations)
					for x in constaints:
						constraint_list.append(x)
					for x in pre_condition:
						constraint_list.append(x)
					constraint_list.append(variable+">=0")
					writeLogFile( "j2llogs.logs" ,"\nInductive Step \n"+str(inductivestep)+"\n" )
					status=query2z3(constraint_list,str(inductivestep),update_vfact,inputmap)
					writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
					if "Successfully Proved" in status:
						print "Successfully Proved"
						return 
					elif "Counter Example" in status:
						print status
					else:
						print "Failed to Prove"
				else:
					print "Failed to Prove"
			elif "Counter Example" in status:
				print status
			else:
				print "Failed to Prove"



"""

Tactic 3  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove conclusion 3.waited for 6000

"""
def tactic3(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints,const_var_map):
        for conclusion in conclusions:
        	fun_map1=getCollectConstant(conclusion)
        	fun_map2={}
        	parameter_constant_map={}
        	constraint_list=[]
		frame_axioms=eqset2constraintlist(f)
		for x in frame_axioms:
			constraint_list.append(x)
		out_axioms=eqset2constraintlist(o)
		subs_list=eqset2subs_list(o)
		for x in out_axioms:
			constraint_list.append(x)
		for x in a:
			if x[0]=='i1':
				key=None
				parameterlist=[]
				for i in range(0, len(x[3])):
					if i==0: 
						key=x[3][0]
					else:
						if len(x[3][i])==1:
							parameterlist.append(x[3][i])
						else:
							parameterlist.append(x[2])
				if key is not None:
					fun_map2[key]=parameterlist

		if len(fun_map2)!=0 and len(fun_map1)!=0:
			for x in fun_map1:
				for i in range(0, len(fun_map2[x])):
					if is_number(str(fun_map1[x][i]))==False:
						const_vfact=[]
						const_vfact.append(str(fun_map1[x][i]))
						const_vfact.append(0)
						ul=['constant']
						const_vfact.append(ul)
						vfact.append(const_vfact)
						parameter_constant_map[fun_map2[x][i]]=str(fun_map1[x][i])+"-1"
					else:
						parameter_constant_map[fun_map2[x][i]]=str(int(fun_map1[x][i])-1)
			for x in a:
				equations=wff2z3InsExpand(x,parameter_constant_map)
				for equation in equations:
					constraint_list.append(equation)	
			for x in constaints:
				constraint_list.append(x)
			for x in pre_condition:
        			constraint_list.append(x)
        		conclusion=simplify_conclusion(conclusion,subs_list)	
			if "factorial" in conclusion:
				cfact=eval("['factorial',1,['int','int']]")
				vfact.append(cfact)
			status=query2z3(constraint_list,conclusion,vfact,inputmap)
			writeLogFile( "j2llogs.logs" ,"\nResult \n"+str(status)+"\n" )
			if "Successfully Proved" in status:
				print "Successfully Proved"					
			elif "Counter Example" in status:
				print status
			else:
				print "Failed to Prove"
		else:
			print "Failed to Prove"
        	
def tactic4(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints):
        constraint_list=[]
	frame_axioms=eqset2constraintlist(f)
	for x in frame_axioms:
		constraint_list.append(x)
	out_axioms=eqset2constraintlist(o)
	subs_list=eqset2subs_list(o)
	for x in out_axioms:
		constraint_list.append(x)
	for x in a: 
		#constraint_list.append(wff2z3(x))
            equations=wff2z3Stronger(x)
            if type(equations) is list:
                for equation in equations:                    
                    constraint_list.append(equation)
            elif type(equations) is str:
                constraint_list.append(equations)
	for x in constaints:
		constraint_list.append(x)
	for x in pre_condition:
        	constraint_list.append(x)
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		conclusion=simplify_conclusion(conclusion,subs_list)	
		if "factorial" in conclusion:
			cfact=eval("['factorial',1,['int','int']]")
			vfact.append(cfact)
		
		status=query2z3(constraint_list,conclusion,vfact,inputmap)
		writeLogFile( "j2llogs.logs" ,"\nResult \n"+str(status)+"\n" )
		if "Successfully Proved" in status:
			print "Successfully Proved"
			
		elif "Counter Example" in status:
			print status
			
		else:
			print "Failed to Prove"


"""

#equation='X==q7(5)*Y+r7(5)'

#equation='r7(5)>=0'

"""
def getCollectConstant(equation):
	if equation is not None:
		fun_parameter={}
		if '==' in str(equation):
			polys=str(equation).split('==')
			polys[0]=polys[0].strip()
			polys[1]=polys[1].strip()
			if "**" in str(polys[1]):
				polys[1]=translatepowerToFun(str(polys[1]))
			expression=str(str(polys[0])+"="+str(polys[1]))
			p = getParser()
			tree = p.parse_expression(expression)
			if type(tree) is m.Assignment:
				expressionCollectConstant(tree.lhs,fun_parameter)
				expressionCollectConstant(tree.rhs,fun_parameter)
				return fun_parameter
		else:
			if "**" in str(equation):
				equation=translatepowerToFun(str(equation))
			p = getParser()
			tree = p.parse_expression(str(equation))
			if type(tree) is m.Relational:
				expressionCollectConstant(tree,fun_parameter)
				return fun_parameter





"""

equations=['Y1 = Y','X1 = X','A1 = A7(_N2)','q1 = q7(_N2)','r1 = r7(_N2)','B1 = B7(_N2)','(r7(_n2)<(2*((2**_N1(_n2))*Y)))','(_n1<_N1(_n2)) -> (r7(_n2)>=(2*((2**_n1)','A7(_n2+1) = ((2**_N1(_n2))*1)','B7(_n2+1) = ((2**_N1(_n2))*Y)','q7(_n2+1) = (q7(_n2)+((2**_N1(_n2))*1))','r7(_n2+1) = (r7(_n2)-((2**_N1(_n2))*Y))','A7(0) = A','B7(0) = B','q7(0) = 0','r7(0) = X','(r7(_N2)<Y)','(_n2<_N2) -> (r7(_n2)>=Y)']

"""
def toZ3(equations):
	for equation in equations:
		if '>' not in equation and '<' not in equation and '->' not in equation:
			polys=equation.split('=')
			polys[0]=polys[0].strip()
			polys[1]=polys[1].strip()
			if "**" in str(polys[1]):
				polys[1]=translatepowerToFun(str(polys[1]))
			expression=str(str(polys[0])+"="+str(polys[1]))
			p = getParser()
			tree = p.parse_expression(expression)
			wff_equation=construct_expression(tree,2,'_n2')
			print wff_equation















"""

#Simplify conclusion 

"""


def simplify_conclusion(conclusion,subs_list):
	if conclusion is not None and conclusion!='':
		if 'ForAll' in conclusion:
			arg_list=extract_args(conclusion)
			return 'ForAll('+arg_list[0]+','+simplify_conclusion(arg_list[1],subs_list)+')'
		elif 'Exists' in conclusion:
			arg_list=extract_args(conclusion)
			return 'Exists('+arg_list[0]+','+simplify_conclusion(arg_list[1],subs_list)+')'
		else:
			if '==' not in conclusion:
				conclusion=str(pow_to_mul(powsimp(simplify_sympy(conclusion).subs(subs_list))))
				return conclusion
			else:
				axm=conclusion.split('==')
				conclusion=str(simplify_sympy(axm[0]).subs(subs_list))+'=='+str(simplify_sympy(axm[1]).subs(subs_list))
				return conclusion

"""

Validation of Variables

"""

def validationOfInput(allvariable):
	for variable in allvariable:
		if variable=='S' or variable=='Q':
			return True
	return False


"""

Function Display Axioms

"""

def displayAxioms(axiom):
	if axiom is not None:
	    print('1. Frame axioms:')
	    eqset2string1(axiom.getFrame_axioms())
	    print('\n2. Output equations:')
	    eqset2string1(axiom.getOutput_equations())
	    print('\n3. Other axioms:')
	    for x in axiom.getOther_axioms(): 
            	print wff2string1(x)
            

"""

Function Display Vfact

"""

def displayVfact(axiom):
	if axiom is not None:
	    print axiom.getVfact()
	    
	   
"""

Function Display Input Variable

"""

def displayInputVariables(axiom):
	if axiom is not None:
	    print axiom.getInputvariable()



"""
#Test Case 1
equations=['(_n1<_N1) -> ((_n1+1)**2)>X','((_N1+1)**2)<=X','X1= X','a1= _N1','su1=((_N1+1)**2)','t1=(2*_N1+1)']
vfacts=[['X',0,['int']],['_n1',0,['int']],['_N1',0,['int']],['X1',0,['int']],['a1',0,['int']],['su1',0,['int']],['t1',0,['int']]]
pre_condition=['X>=0']
post_condition=['(a1**2)>X']
flag=1
inputmap={'X': 'int'}

#Example-1
# post_condition=['X==q1*Y+r1','r(n1)>=0']
# post_condition=['X==q1*Y+r1']
# pre_condition=['X>=0','Y>0']
# equations=['_N1>=0','q(0)=0 ','r(0)=X ','(_n1 <_N1) -> r(_n1)>=Y','r(_N1)<Y','(_n2<_N11(_n1)) -> r(_n1)>=2*2**_n2*Y','r(_n1)<2*2**_N11(_n1)*Y','q(_n1+1)=q(_n1)+2**(_N11(_n1))','r(_n1+1)=r(_n1)-Y*2**(_N11(_n1))','r1=r(_N1)','q1=q(_N1)']
# vfacts=[['X',0,['int']],['Y',0,['int']],['r1',0,['int']],['q1',0,['int']],['q',1,['int','int']],['r',1,['int','int']],['_N1',0,['int']],['_n1',0,['int']],['_N11',1,['int','int']],['_n2',0,['int']]]
# inputmap={'X': 'int','Y': 'int'}
# flag=5


#Example-2
# post_condition=['X==q(n1)*Y+r(n1)','r(n1)>=0']
# post_condition=['X==q(n1)*Y+r(n1)']
# pre_condition=['X>=0','Y>0']
# equations=['_N1>=0','_N2>=0','q(0)=0 ','r(0)=X ','(_n1 <_N1) -> X>=2**n1*Y','X<2**_N1*Y','(_n1 <_N2) -> (2**(_N1-n1))!=1','(2**(_N1-_N2))==1','q(n1+1)=ite(r(n1)>=((Y *2**(_N1-n1))/2),q(n1)+((2**(_N1-n1))/2),q(n1))','r(n1+1)=ite(r(n1)>=((Y*2**(_N1-n1))/2),(r(n1)-((Y*2**(_N1-n1))/2)),r(n1))']
# equations=['X>=0','Y>0','q(0)=0 ','r(0)=X ','smallest(n1,_N1,X<2**n1*Y)','smallest(n1,_N2,(2**(_N1-n1))==1)','q(n1+1)=If r(n1)>=((Y *2**(_N1-n1))/2) Then q(n1)+((2**(_N1-n1))/2) Else  q(n1)','r(n1+1)=If r(n1)>=((Y*2**(_N1-n1))/2) Then (r(n1)-((Y*2**(_N1-n1))/2)) Else  r(n1)']
# vfact=[['X',0,['int']],['Y',0,['int']],['q',1,['int','int']],['r',1,['int','int']],['_N1',0,['int']],['_n1',0,['int']],['_N2',0,['int']],['k1',0,['int']]]
# inputmap={'X': 'int','Y': 'int'}

#Example-3
#post_condition=['z1 = (a/5)']
#pre_condition=['a>0']
#equations=['y1 = ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a*2)+1,a*2)+2,ite(a<5,(a*2)+1,a*2))','x1 = ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,a+1,a)+3,ite(a<5,a+1,a))','z1 = (a/5)']
#vfact=[['a',0,['int']],['x1',0,['int']],['y1',1,['int','int']],['z1',1,['int','int']]]
#inputmap={'a': 'int'}

#Example-3
#post_condition=['z1 = (a/5)']
#pre_condition=['a>0']
#equations=['y1 = ite(ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a*2)+1,a*2)+2,ite(a<5,(a*2)+1,a*2))<7,ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a*2)+1,a*2)+2,ite(a<5,(a*2)+1,a*2))+2,ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a*2)+1,a*2)+2,ite(a<5,(a*2)+1,a*2)))','x1 = ite(ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a*2)+1,a*2)+2,ite(a<5,(a*2)+1,a*2))<7,ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,a+1,a)+3,ite(a<5,a+1,a))+3,ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,a+1,a)+3,ite(a<5,a+1,a)))','z1 = ite(ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a*2)+1,a*2)+2,ite(a<5,(a*2)+1,a*2))<7,ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a/5)+1,a/5)+2,ite(a<5,(a/5)+1,a/5))+3,ite(ite(a<5,(a*2)+1,a*2)>10,ite(a<5,(a/5)+1,a/5)+2,ite(a<5,(a/5)+1,a/5)))']
#vfact=[['a',0,['int']],['x1',0,['int']],['y1',1,['int','int']],['z1',1,['int','int']]]
#inputmap={'a': 'int'}

#Example-3
#post_condition=['z1 = (a/5)']
#pre_condition=['a>0']
#equations=['y1 = ite(a<10,2a+1,ite(a>5,a+1,ite(a>2,a+2,a)))','y1 = ite(a<10,2a+1,ite(a>5,a+1,ite(a>2,a+2,a)))','z1 = ite(a<10,2a+1,ite(a>5,a+1,ite(a>2,a+2,a)))']
#equations=['y1 = ite(a<10,2a+1,ite(a>=10,a+1,ite(a>2,a+2,a)))','y1 = ite(a<10,2a+1,ite(a>=10,a+1,ite(a>2,a+2,a)))','z1 = ite(a<10,2a+1,ite(a>=10,a+1,ite(a>2,a+2,a)))']
#equations=['y1 = ite(a<b,2a+1,ite(a>=b,a+1,ite(a>c,a+2,ite(a<=c,a*2,a))))','y1 = ite(a<b,2a+1,ite(a>=b,a+1,ite(a>c,a+2,ite(a<=c,a*2,a))))','z1 = ite(a<b,2a+1,ite(a>=b,a+1,ite(a>c,a+2,ite(a<=c,a*2,a))))']
#vfact=[['a',0,['int']],['b',0,['int']],['c',0,['int']],['x1',0,['int']],['y1',1,['int','int']],['z1',1,['int','int']]]
#inputmap={'a': 'int','b': 'int','c': 'int'}

#Example-4
#post_condition=['z1 = (a/5)']
#pre_condition=['a>0']
#equations=['y1 = ite(a<b,2a+1,ite(a>c,a+2,a))','y1 = ite(a<b,2a+1,ite(a>c,a+2,a))','z1 = ite(a<b,2a+1,ite(a>c,a+2,a))']
#vfact=[['a',0,['int']],['b',0,['int']],['c',0,['int']],['x1',0,['int']],['y1',1,['int','int']],['z1',1,['int','int']]]
#inputmap={'a': 'int','b': 'int','c': 'int'}
"""



def proveTest(equations,pre_condition,post_condition,vfacts,flag,inputmap):
	update_equation=[]
	for equation in equations:
        	update_equation.append(equation)
	for equation in pre_condition:
        	update_equation.append(equation)
       	if flag==1:
        	tactic1(update_equation,post_condition,vfacts,inputmap)
        elif flag==2:
        	tactic2(update_equation,post_condition,vfacts,inputmap)
        elif flag==3:
        	tactic3(update_equation,post_condition,vfacts,inputmap)
        elif flag==4:
		tactic4(update_equation,post_condition,vfacts,inputmap)
	elif flag==5:
		tactic5(update_equation,post_condition,vfacts,inputmap)
	elif flag==6:
		tactic6(update_equation,post_condition,vfacts,inputmap)


"""

#Solving Recurrences 

# Test Case 1
# equations=[['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['+', ['a3', ['_n1']], ['1']]],['i1', 2, '_n1', ['t3', ['+', ['_n1'], ['1']]], ['+', ['t3', ['_n1']], ['2']]],['i1', 3, '_n1', ['su3', ['+', ['_n1'], ['1']]], ['+', ['su3', ['_n1']], ['+',['t3', ['_n1']], ['2']]]], ['i0', 0, ['a3', ['0']], ['0']], ['i0', 0, ['t3', ['0']], ['1']], ['i0', 0, ['su3', ['0']], ['1']]]
# organize_recursive_relation(equations,constant)
# constant='_N1'
# Test Case 2
# equations=[['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['2']]],['i0', 0, ['a3', ['0']], ['1']]]
# organize_recursive_relation(equations)


# Test Case 3
# equations=[['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['+', ['a3', ['_n1']], ['s3', ['_n1']]]],['i0', 0, ['a3', ['0']], ['1']],['i1', 2, '_n1', ['s3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['s3', ['_n1']]]],['i0', 0, ['s3', ['0']], ['1']]]
# organize_recursive_relation(equations,constant)

# Test Case 4
# equations=[['i1', 2, '_n1', ['y2', ['+', ['_n1'], ['1']]], ['+', ['y2', ['_n1']], ['1']]],['i1', 2, '_n1', ['x2', ['+', ['_n1'], ['1']]], ['+', ['x2', ['_n1']], ['2']]],['i0', 0, ['y2', ['0']], ['y']],['i0', 0, ['x2', ['0']], ['x']]]
# organize_recursive_relation(equations,constant)
# solution=[['i1', 2, '_n1', ['x2', [['_n1']]], ['+', ['*', ['2'], ['_n1']], ['x']]], ['i1', 2, '_n1', ['y2', [['_n1']]], ['+', ['_n1'], ['y']]]]
# constant='_N1'
"""





def construct_expression(tree,postion,variable):
	expression=""
	if type(tree) is m.Assignment:
		expression="['i2',"+str(postion)+",'"+variable+"',"+expressionCreator(tree.lhs)+","+expressionCreator(tree.rhs)+"]"
	return eval(expression)
	
def construct_expression_normal(tree):
	expression=""
	if type(tree) is m.Relational:
		expression="['a',"+expressionCreator(tree)+"]"
	return eval(expression)
				

"""

#Solving Recurrences using wolframalpha

"""

def recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list):
    var=None
    query1="T(n+1)="+str(righthandstmt)
    var_map={}
    count=1
    #print query1
   
   
    if is_number(str(righthandstmt_base))==False:
    	if len(str(righthandstmt_base))>1:
    		var=righthandstmt_base
    		query2="T(0)=N_1"
    	else:
    		for x in variable_list:
    			righthandstmt_base=righthandstmt_base.replace(x,'N_'+str(count))
    			var_map[x]='N_'+str(count)
    			count=count+1
    		query2="T(0)="+str(righthandstmt_base)
    		
    else:
    	query2="T(0)="+str(righthandstmt_base)
    query1=transferToFunctionSyntax(str(query1))
    query2=transferToFunctionSyntax(str(query2))
    query1=query1.replace('T[n+1]','T(n+1)')
    query1=query1.replace('T[n]','T(n)')
    query2=query2.replace('T[0]','T(0)')
    query=query2+","+query1
    if '[' in query1:
    	return None
    if query is not None:
        query=query.replace('_N','m_1')
    finalResult=None
    #app_id="YRL93R-5AYL87GHRY"
    app_id="TQT2K7-5AK3PPJYVX"
    client = wolframalpha.Client(app_id)
    res = client.query(query)
    for pod in res.pods:
	if 'Recurrence equation solution' in pod.title:
            result=pod.text
            flag=False
            flag=isConstInResult( result )
            if flag==False and ')_' not in result and 'Gamma' not in result and 'Pochhammer' not in result and 'Beta' not in result and 'zeta' not in result and 'alpha' not in result :
            	results=result.split('=')
	    	results[1]=results[1].strip()
	    	results[1]=results[1].replace(' ','*')
	    	results[1]=results[1].replace('^','**')
	    	results[1]=results[1].replace('m_1','_N')
	    	if var is not None:
	    		results[1]=results[1].replace('N_1',str(var))
	    	for x in var_map.keys():
	    		results[1]=results[1].replace(var_map[x],x)	
	    	try:

	    		finalResult=str(simplify_expand_sympy(results[1]))
	    		writeLogFile( "j2llogs.logs" , "\nEquation Pass to Wolfram Mathematica  \n"+str(query1)+"------Base Case---"+str(query2)+"\n" )
	    		writeLogFile( "j2llogs.logs" , "\nClosed form solution return by Wolfram Mathematica \n"+str(finalResult)+"\n" )
	    	except ValueError:
			finalResult=None
			#writeLogFile( "j2llogs.logs" , "\nFailed to find close form solution\n" )
	    else:
                finalResult=None
                #writeLogFile( "j2llogs.logs" , "\nFailed to find close form solution\n" )
    
    return finalResult
 

"""
 
#Solving Recurrences using sympy
 
"""
def recurreSolver_sympy(righthandstmt,righthandstmt_base):
	expression="T(n+1)-("+str(righthandstmt)+")"
	#print expression
	f=simplify(expression)
	#Register n as Symbol
	n=Symbol('n')
	#Register T as Function
	T=Function('T')
	result=None
	#Converting String to Sympy Expression
	terminationList={sympify("T(0)"):righthandstmt_base}
	#Try to solve recurrences
	try:
		result=rsolve(f, T(n), terminationList)
		flag=False
            	flag=isConstInResult( str(result) )
		if flag==False and result is not None and 'RisingFactorial' not in str(result) and 'binomial' not in str(result) and 'gamma' not in str(result) and 'rgamma' not in str(result) and 'gammaprod' not in str(result) and 'loggamma' not in str(result) and 'beta' not in str(result) and 'superfac' not in str(result) and 'barnesg' not in str(result):
			result=simplify(result)
			writeLogFile( "j2llogs.logs" ,"\nEquation Pass to sympy\n"+str(expression)+"=0"+"------"+"Base Case--T(0)="+str(righthandstmt_base)+"\n" )
			writeLogFile( "j2llogs.logs" ,"\nClosed form solution return by sympy \n"+str(result)+"\n" )
		else:
                    result=None
                    #writeLogFile( "j2llogs.logs" , "\nFailed to find close form solution\n" )
	except ValueError:
		result=None
		#writeLogFile( "j2llogs.logs" , "\nFailed to find close form solution\n" )

	return result






#Parsing Method Starts

# define some basic operand expressions
number = Regex(r'\d+(\.\d*)?([Ee][+-]?\d+)?')
ident = Word(alphas+'_', alphanums+'_')
#fn_call = ident + '(' + Optional(delimited_list(expr)) + ')'

# forward declare our overall expression, since a slice could 
# contain an arithmetic expression
expr = Forward()
#slice_ref = '[' + expr + ']'

slice_ref = '[' + expr + ZeroOrMore("," + expr) + ']'

# define our arithmetic operand
operand = number | Combine(ident + Optional(slice_ref))
#operand = number | fn_call | Combine(ident + Optional(slice_ref))
inequalities = oneOf("< > >= <= = == !=")

# parse actions to convert parsed items
def convert_to_pow(tokens):
    tmp = tokens[0][:]
    ret = tmp.pop(-1)
    tmp.pop(-1)
    while tmp:
        base = tmp.pop(-1)
        # hack to handle '**' precedence ahead of '-'
        if base.startswith('-'):
            ret = '-power(%s,%s)' % (base[1:], ret)
        else:
            ret = 'power(%s,%s)' % (base, ret)
        if tmp:
            tmp.pop(-1)
    return ret

def unary_as_is(tokens):
    return '(%s)' % ''.join(tokens[0])

def as_is(tokens):
    return '%s' % ''.join(tokens[0])


# simplest infixNotation - may need to add a few more operators, but start with this for now
arith_expr = infixNotation( operand,
    [
    ('-', 1, opAssoc.RIGHT, as_is),
    ('**', 2, opAssoc.LEFT, convert_to_pow),
    ('-', 1, opAssoc.RIGHT, unary_as_is),
    ((inequalities,inequalities), 3, opAssoc.LEFT, as_is),
    (inequalities, 2, opAssoc.LEFT, as_is),
    (oneOf("* /"), 2, opAssoc.LEFT, as_is),
    (oneOf("+ -"), 2, opAssoc.LEFT, as_is),
    (oneOf('and or'), 2, opAssoc.LEFT, as_is),
    ])
#('-', 1, opAssoc.RIGHT, as_is),
# now assign into forward-declared expr
expr <<= arith_expr.setParseAction(lambda t: '(%s)' % ''.join(t))

"""
#expression="2**3"
#expression="2**-3"
#expression="2**3**x5"
#expression="2**-3**x6[-1]"
#expression="2**-3**x5+1"
#expression="(a+1)**2"
#expression="((a+b)*c)**2"
#expression="B**2"
#expression="-B**2"
#expression"(-B)**2"
#expression="B**-2"
#expression="B**(-2)"
#expression="((Z**(_N1+1)-1)/(Z-1))*(Z-1))"
#expression="((_N1+1)**2)<=X"
#expression="_n2*_n3*_N1(_n2, _n3)**2/2"
#translatepowerToFun(expression)

"""

def translatepowerToFun(expression):
    if "**" in expression:
	if "<" in  expression or ">" in  expression:
            expression=simplify(expression)
    	expression=transferToFunctionSyntax(str(expression))
    	xform = expr.transformString(expression)[1:-1]
    	xform=xform.replace('[','(')
    	expression=xform.replace(']',')')
    return expression
 

"""
Example 1:
>>> expression="x(n)+(y(n)+1)*n"
>>> transferToMathematicaSyntax(expression)
'x[n]+(y[n]+1)*n'

Example 2:

>>> expression="x(n(a,b),a,b)+2^(y(_N1(a,b),a,b)+1)"
>>> transferToMathematicaSyntax(expression)
'x[n[a,b],a,b]+2^(y[_N1[a,b],a,b]+1)'

Example 3:

>>> expression="x(n)+(y(n)/(_N1(n)))"
>>> transferToMathematicaSyntax(expression)
'x[n]+(y[n]/(_N1(n)))'

"""

#Changing function of the formate f(n) to f[n]. It assist the pasring 

def transferToFunctionSyntax(expression):
	if "(" in expression and ")" in expression:
		p = regex.compile(r'\b[a-zA-Z_]\w*(\((?>[^()]|(?1))*\))')
		result=(p.sub(lambda m: m.group().replace("(", "[").replace(")", "]"), expression))
	else:
		result=expression
	return result


#Parsing Method Ends


"""
Reading the contain of the file 
"""
def readingFile( filename ):
	content=None
	with open(filename) as f:
    		content = f.readlines()
    	return content
 
"""
Wrtitting the contain on file 
"""
def writtingFile( filename , content ):
	file = open(filename, "w")
	file.write(str(content))
	file.close()

"""
Appending the contain on file 
"""
def appendingFile( filename , content ):
	file = open(filename, "a")
	file.write(str(content))
	file.close()

"""

write logs

"""
def writeLogFile(filename , content):
	if os.path.isfile(filename):
    		appendingFile( filename , content )
	else:
    		writtingFile( filename , content )



"""
split statement using "=" as delimiter 
Example 1 :

>>> txt="x(n+1)=x(n)-y(n)"
>>> tokzr_left_hand_stmt(txt)
'x(n+1)'


Example 2 : 

>>> txt="x(n+1) = ite(x(n)>y(n),x(n)-y(n),x(n))"
>>> tokzr_left_hand_stmt(txt)
'x(n+1)'


"""

def tokzr_left_hand_stmt(txt): 
	tokens=txt.split("=")
	return tokens[0]
	


#Function Get list of parameters 

def find_between( s, first, last ):
    try:
        start = s.index( first ) + len( first )
        end = s.index( last, start )
        return s[start:end]
    except ValueError:
        return ""
        
#Get the parameter 

def getParameter( parameterlist ):
	try:
	 	parameters=parameterlist.split(',')
		for index, parameter  in enumerate(parameters):
			if '+1' in parameter:
				return parameter.replace("\n","").strip()
	except ValueError:
        	return ""

"""

#Get Function Name 
#This can be done using Regular expression ...Need to update
"""
def getFunctionName(function,parameters ):
	for parameter in parameters:
		function=function.replace(parameter,"")
	blanklist=find_between( function,'(',')')
	function=function.replace("("+str(blanklist)+")","")
	return function

"""

#Convert ite expression to a condition expression map

"""
def ConvertITEToMap(expression,map):
	if 'ite' in expression:
		parameters=extract_args(expression)
		map[parameters[0]]=parameters[1]
		if 'ite' in parameters[2]:
			ConvertITEToMap(parameters[2],map)
		else:
			map[None]=parameters[2]


"""

#Convert a condition expression map to ite expression

"""
def ConvertMapToITE(map):
	expression=""
	expressionEnd=""
	for condition in map:
		if condition is not None:
			if expression=="":
				expression="ite("+condition+","+map[condition]
				expressionEnd=")"
			else:
				expression+=",ite("+condition+","+map[condition]
				expressionEnd+=")"	
	expression+=","+map[None]+expressionEnd
	return expression


"""
#Extract arguments from smallest function

#Example 1: expr="smallest(n,_N1,su(n)>X(n))"
#extract_args(expr):

"""
def extract_args(expr):
    paren = 0
    start = 0
    ret = []
    for i, c in enumerate(expr):
        if c=='(':
            paren+=1
            if paren==1:
                start=i+1
        elif c==')':
            if paren==1 and start:
                ret.append(expr[start: i]) 
            paren-=1
        elif c==',' and paren==1:
            ret.append(expr[start:i])
            start=i+1
    return ret


"""

axiomes to Z3 statements

"""


"""
#Test Case 1
#variable="n1"

#Test Case 2
#variable="_n1"

"""


def isLoopvariable( variable ):
	status=False
	find=regex.compile(r'[_]n\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


"""
#Test Case 1
#variable="C1"

#Test Case 2
#variable="C0"

"""


def isConstInResult( variable ):
	status=False
	find=regex.compile(r'C\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status



	








	



"""

Strategy 1  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove conclusion 3.waited for 6000

"""
def strategy6(equations,conclusion,vfact,inputmap):
	pythonProgram="from z3 import *\n"
	status=""
	for [x,k,l] in vfact:
		if k==0:
			if l[0]=="int":
				pythonProgram+=x+"=Int(\'"+x+"\')\n"
			elif l[0]=="double":
				pythonProgram+=x+"=Real(\'"+x+"\')\n"
			elif l[0]=="float":
				pythonProgram+=x+"=Real(\'"+x+"\')\n"
			else:
				pythonProgram+=x+"=Bool(\'"+x+"\')\n"
		else:
			pythonProgram+=x+"=Function(\'"+x+"\'"
			for e in l:
				if e=="int":
					pythonProgram+=",IntSort()"
				else:
					pythonProgram+=",RealSort()"
			pythonProgram+=")\n"
	pythonProgram+="s=Solver()\n"
	pythonProgram+="s.set(\"timeout\", 60000)\n"

	equations=axiomestoZ3SS(equations,inputmap)
	for equation in equations:
		pythonProgram+="s.add("+str(equation)+")\n"
	finalProgram=pythonProgram
	finalProgram+="s.add(Not("+str(conclusion)+"))\n"
	finalProgram+="if sat==s.check():\n"+"\tprint \"Counter Example\"\n"+"\tprint s.model()\n"+"elif unsat==s.check():\n"+"\ts.check()\n"+"\tprint \"Successfully Proved\"\n"+"else:\n"+"\tprint \"Failed To Prove\""
		#print finalProgram		
	writtingFile( "z3query.py" , finalProgram )
	proc = subprocess.Popen('python z3query.py', stdout=subprocess.PIPE,shell=True)
	output = proc.stdout.read()
	status=output
	return status



"""
get All the conditions in equations 

"""

def getConditios(equation):
	conditions_map={}
	if 'ite' in equation: 
		terms=extract_args(equation)
		if 'ite' in terms[0]:
			condition_map=getConditios(terms[0])
			for condition in condition_map:
				conditions_map[condition]=condition_map[condition]
		else:
			conditions_map[terms[0]]=complementOfExpression(terms[0])
		if 'ite' in terms[1]:
			condition_map=getConditios(terms[1])
			for condition in condition_map:
				conditions_map[condition]=condition_map[condition]
		if 'ite' in terms[2]:
			condition_map=getConditios(terms[2])
			for condition in condition_map:
				conditions_map[condition]=condition_map[condition]
	return conditions_map

"""

get All the conditions in equations 

"""

def getAxiomesForCondition(conditions_list,equations,vfact,inputmap):
    updated_equations=[]
    for equation in equations:
        	if 'ite' in equation:
                    left_side_stmt_suber=tokzr_left_hand_stmt(equation)
                    left_side_stmt_suber=left_side_stmt_suber.strip()
		    loopvariables=extract_args(left_side_stmt_suber)
		    equation=equation.replace(left_side_stmt_suber,"")
		    equation=equation.strip()
		    equation=equation[equation.index('=')+1:len(equation)]
		    stmt_map_equation=map_consturct_stmt(equation)
		    temp_equations=[]
		    selected_equation={}
		    for cond in stmt_map_equation:
                        if cond is not None:
                            equations1=[]
                            for equ in conditions_list:
                                equations1.append(equ)
                            result_Status1=strategy1(equations1,cond,vfact,inputmap)
                            if "Successfully Proved" in result_Status1:
                                selected_equation[cond]=stmt_map_equation[cond]
                    if len(selected_equation)==0:
                        updated_equations.append(left_side_stmt_suber+"="+stmt_map_equation[None])
                    elif len(selected_equation)==1:
                        for cond in selected_equation:
                            updated_equations.append(left_side_stmt_suber+"="+selected_equation[cond])
                    else:
                        expression=""
                        expressionend=""
                        for cond in selected_equation:
                            if expression=="":
                                expression="ite("+cond+","+selected_equation[cond]
                                expressionend=")"
                            else:
                                expression=",ite("+cond+","+selected_equation[cond]
                                expressionend+=")"
                            expression=expression+","+stmt_map_equation[None]+expressionend
                        updated_equations.append(left_side_stmt_suber+"="+expression)
                else:
                    updated_equations.append(equation)
    return updated_equations



def map_consturct_stmt(equation):
    terms=extract_args(equation)
    conditions_map={}
    conditions_map[terms[0]]=terms[1]
    if 'ite' in terms[2]:
        condition_map=map_consturct_stmt(terms[2])
	for condition in condition_map:
            conditions_map[condition]=condition_map[condition]
    else:
        conditions_map[None]=terms[2]
    return conditions_map		
	



			
"""

Tactic 5  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove using induction on loop variable 

"""
def tactic6(equations,conclusions,vfact,inputmap):
	const_var_map={}
	for equation in equations:
		if '->' in equation:
			axiomes=equation.split('->')
			axiomes[0]=simplify(str(axiomes[0]))
			variables=str(axiomes[0]).split('<')
			variables[0]=variables[0].strip()
			variables[1]=variables[1].strip()
			const_var_map[simplify(variables[1])]=simplify(variables[0])
	for conclusion in conclusions:
		conclusion=fullySimplifyExpandExpression(conclusion,equations)
		variable=None
		constant=None
		print conclusion
		for const in const_var_map:
			if str(const) in str(conclusion):
				variable=const_var_map[const]
				constant=const
				if '==' in str(conclusion) and '<' not in  str(conclusion) and '>' not in str(conclusion) and '!' not in str(conclusion) and 'ite' not in str(conclusion):
					exp=str(conclusion).split('==')
					exp[0]=simplify(exp[0]).subs(constant,variable)
					exp[1]=simplify(exp[1]).subs(constant,variable)
					invariantstmt=str(exp[0])+"=="+str(exp[1])
				else:
					invariantstmt=simplify(conclusion).subs(constant,variable)
				basecasestmt=simplify(invariantstmt).subs(variable,0)
				print " Try to prove following using induction on "+str(variable)
				print "ForAll("+str(variable)+","+str(invariantstmt)+")"
				print "Base Case"
				if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt):
					exp=str(invariantstmt).split('==')
					exp[0]=simplify(exp[0]).subs(variable,0)
					exp[1]=simplify(exp[1]).subs(variable,0)
					basecasestmt=str(exp[0])+"=="+str(exp[1])
				else:
					basecasestmt=simplify(invariantstmt).subs(variable,0)
				print basecasestmt
				status=strategy1(equations,basecasestmt,vfact,inputmap)
				if "Successfully Proved" in status:
					print "	Successfully Proved Base Case"
					print "Inductive Step"
					updated_equation=[]
					updated_vfact=[]
					if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt):
						exp=str(invariantstmt).split('==')
						lexp=simplify(exp[0]).subs(variable,"_k1")
						rexp=simplify(exp[1]).subs(variable,"_k1")
						inductiveassum=str(lexp)+"=="+str(rexp)
						lexp=simplify(exp[0]).subs(variable,"_k1+1")
						rexp=simplify(exp[1]).subs(variable,"_k1+1")
						inductivestep=str(lexp)+"=="+str(rexp)
					else:
						inductiveassum=simplify(invariantstmt).subs(variable,"_k1")
						inductivestep=simplify(invariantstmt).subs(variable,"_k1+1")
					for equation in equations:
						updated_equation.append(equation)
					for fact in vfact:
						updated_vfact.append(fact)
					cfact=eval("['_k1',0,['int']]")
					updated_vfact.append(cfact)
					updated_equation.append("_k1>0")
					updated_equation.append(inductiveassum)
					status=strategy1(updated_equation,inductivestep,updated_vfact,inputmap)
					if "Successfully Proved" in status:
						print "	Successfully Proved Induction Step "
					else:
						print "Failed To Prove Induction Step "
				else:
					print "Failed To Prove Base Case"


"""

Tactic 6  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove using induction on loop variable 

"""
def tactic7(equations,conclusions,vfact,inputmap):
	const_var_map={}
	for equation in equations:
		if '->' in equation:
			axiomes=equation.split('->')
			axiomes[0]=simplify(str(axiomes[0]))
			variables=str(axiomes[0]).split('<')
			variables[0]=variables[0].strip()
			variables[1]=variables[1].strip()
			const_var_map[simplify(variables[1])]=simplify(variables[0])
	for conclusion in conclusions:
		conclusion=fullySimplifyExpandExpression(conclusion,equations)
		variable=None
		constant=None
		for const in const_var_map:
			if str(const) in str(conclusion):
				variable=const_var_map[const]
				constant=const
				if '==' in str(conclusion) and '<' not in  str(conclusion) and '>' not in str(conclusion) and '!' not in str(conclusion) and 'ite' not in str(conclusion):
					exp=str(conclusion).split('==')
					exp[0]=simplify(exp[0]).subs(constant,variable)
					exp[1]=simplify(exp[1]).subs(constant,variable)
					invariantstmt=str(exp[0])+"=="+str(exp[1])
				else:
					invariantstmt=simplify(conclusion).subs(constant,variable)
				basecasestmt=simplify(invariantstmt).subs(variable,0)
				print " Try to prove following using induction on "+str(variable)
				print "ForAll("+str(variable)+","+str(invariantstmt)+")"
				print "Base Case"
				if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt):
					exp=str(invariantstmt).split('==')
					exp[0]=simplify(exp[0]).subs(variable,0)
					exp[1]=simplify(exp[1]).subs(variable,0)

					basecasestmt=str(exp[0])+"=="+str(exp[1])
				else:
					basecasestmt=simplify(invariantstmt).subs(variable,0)
				print basecasestmt
				status=strategy1(equations,basecasestmt,vfact,inputmap)
				if "Successfully Proved" in status:
					print "	Successfully Proved Base Case"
					print "Inductive Step"
					updated_equation=[]
					updated_vfact=[]
					if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt):
						exp=str(invariantstmt).split('==')
						lexp=simplify(exp[0]).subs(variable,"_k1")
						rexp=simplify(exp[1]).subs(variable,"_k1")
						inductiveassum=str(lexp)+"=="+str(rexp)
						lexp=simplify(exp[0]).subs(variable,"_k1+1")
						rexp=simplify(exp[1]).subs(variable,"_k1+1")
						inductivestep=str(lexp)+"=="+str(rexp)
					else:
						inductiveassum=simplify(invariantstmt).subs(variable,"_k1")
						inductivestep=simplify(invariantstmt).subs(variable,"_k1+1")
					for equation in equations:
						updated_equation.append(equation)
					for fact in vfact:
						updated_vfact.append(fact)
					cfact=eval("['_k1',0,['int']]")
					updated_vfact.append(cfact)
					updated_equation.append("_k1>0")
					updated_equation.append(inductiveassum)
					status=strategy4(updated_equation,inductivestep,updated_vfact,inputmap)
					if "Successfully Proved" in status:
						print "	Successfully Proved Induction Step "
					else:
						print "Failed To Prove Induction Step "
				else:
					print "Failed To Prove Base Case"
"""

Tactic 7  ----> Conditional Analysis

"""
def tactic8(equations,conclusions,vfact,inputmap):

	for conclusion in conclusions:
		status=strategy4(equations,conclusion,vfact,inputmap)
		if status==True:
			print "	Successfully Proved "
		else:
			print "Failed To Prove "


    
"""

"""	
def testing(f,o,a,inputvar,opvariablesarray):
	functionMap={}
	functInputMap={}
	funOfSmallMacro={}
	subs_map={}
	con_res_map={}
	res_map={}
	for x in a: 
	    if x[0]=='i1':
                parametes=[]
                parametes.append(x[2])
                parametes.append(wff2string1(x))
		functionMap[x[3][0]]=parametes
	for x in a:
            if x[0]=='a':
                expression=wff2string1(x)
                for fun in functionMap:
                    if fun in expression:
                        funOfSmallMacro[fun]=functionMap[fun]
        for x in a: 
	    if x[0]=='i0':
                if x[2][0] in funOfSmallMacro.keys():
                    parametes=funOfSmallMacro[x[2][0]]
                    stmt_zero=wff2string1(x)
                    parametes.append(stmt_zero)
                    stmt=stmt_zero.split('=')
                    subs_map[simplify(stmt[0])]=simplify(stmt[1])
                    equation=expr2string1(x[3])
                    functInputMap[x[2][0]]=equation
	for fun in funOfSmallMacro:
            equation=funOfSmallMacro[fun][1]
            cmpl_cond=""
            if 'ite' in equation:
                left_side_stmt=tokzr_left_hand_stmt(equation)
                left_side_stmt=left_side_stmt.strip()
                equation=equation.replace(left_side_stmt,"")
                equation=equation.strip()
                equation=equation[equation.index('=')+1:len(equation)]
                stmt_map_equation=map_consturct_stmt(equation)
                for cond in stmt_map_equation:
                    if cond is not None:
                    	modified_cmpl_cond=complementOfExpression(cond)
                    	modified_cmpl_cond=simplify(modified_cmpl_cond).subs(simplify(funOfSmallMacro[fun][0]),0)
                        modified_cmpl_cond=modified_cmpl_cond.subs(subs_map)
                        modified_cond=simplify(cond).subs(simplify(funOfSmallMacro[fun][0]),0)
                        modified_cond=modified_cond.subs(subs_map)
                        modified_eq=simplify(stmt_map_equation[cond]).subs(simplify(funOfSmallMacro[fun][0]),0)
                        modified_eq=modified_eq.subs(subs_map)
                        if cmpl_cond=="":
                        	cmpl_cond=str(modified_cmpl_cond)
                        else:
                        	cmpl_cond+=" and "+str(modified_cmpl_cond)
                        
                        if str(modified_cond) in con_res_map.keys():
                        	value_to_value_map=con_res_map[str(modified_cond)]
                        	if value_to_value_map is not None:
                        		value_to_value_map[str(functInputMap[fun])]=str(modified_eq)
                        		con_res_map[str(modified_cond)]=value_to_value_map
                        	else:
                        		value_to_value_map={}
					value_to_value_map[str(functInputMap[fun])]=str(modified_eq)
                        		con_res_map[str(modified_cond)]=value_to_value_map
                        else:
                        	value_to_value_map={}
                                value_to_value_map[str(functInputMap[fun])]=str(modified_eq)
                        	con_res_map[str(modified_cond)]=value_to_value_map      

                modified_eq=simplify(stmt_map_equation[None]).subs(simplify(funOfSmallMacro[fun][0]),0)
                modified_eq=modified_eq.subs(subs_map)
                if str(cmpl_cond) in con_res_map.keys():
		 	value_to_value_map=con_res_map[str(cmpl_cond)]
		        if value_to_value_map is not None:
		        	value_to_value_map[str(functInputMap[fun])]=str(modified_eq)
		        	con_res_map[str(cmpl_cond)]=value_to_value_map
			else:
		                value_to_value_map={}
				value_to_value_map[str(functInputMap[fun])]=str(modified_eq)
		                con_res_map[str(cmpl_cond)]=value_to_value_map	
		else:
			value_to_value_map={}
			value_to_value_map[str(functInputMap[fun])]=str(modified_eq)
                	con_res_map[str(cmpl_cond)]=value_to_value_map
            else:
                stmt=equation.split('=')
                modified_eq=simplify(stmt[1]).subs(simplify(funOfSmallMacro[fun][0]),0)
                modified_eq=modified_eq.subs(subs_map)
                res_map[str(functInputMap[fun])]=str(modified_eq)
        if not con_res_map:
        	print "***************"
		print res_map
        	print "***************"
        else:
        	print "***************"
		print con_res_map
        	print "***************"

"""
conclusion="ForAll(n,R(n)+1>0)"
subs_list={simplify('R(n,m)'):simplify('R(n,m,n,m)')}
conclusion="ForAll(n,Exists(m,R(n,m)+1>0))"

"""

						

