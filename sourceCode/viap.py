# February 20, 2016

# February 29, 2016: 1. change axioms for if1 and if2 to make all axioms of the form x = ... 2. add last label as an output of translate0

# March 10 - April 27: a new translation for while-loop that parameterizes loop input variables and replaces smallest macros by inductive definition. Also a small correction to simplify()

# April 29: combining the two translations (c2l.py.old3 and c2l.py.old4): keep the old translation for program variables but use a new way to inductively define smallest macro: 
# N(x,y) = if C(x,y) then 0 else C(f(x),g(x)), where f and g is the new value of x and y, respectively, after one iteration
# in c2l.py.old4, f and g are the output functions for the body, here we parameterize f and g first, and use f(1,x) and g(1,y) to replace f(x) and g(y), respectively

# May 18: (not done yet) making functions first-order objects by using "+": f+[t1,...,tk,v] stands for the
# function f1 such that forall x1,...,xk: 
# f1(x1,...,xk) = ite(x1=t1 & ... & xk=tk, v, f(x1,...,xk))
# A translator from C to FOL in python 

# June 18: add solve_rec() by Pritom to solve recurrences in translating while-loop
# assume that the only dynamic functions are the program variables given by v and the system generated temporary functions including big N (is_program_var())
# this makes _base redundant

# August 30: add function definitions and function calls and define program as a sequence of functions. See program definitions just before translate1()

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
import ConfigParser
from pyparsing import *
from sympy.core.relational import Relational
from pycparser import parse_file,c_parser, c_ast, c_generator
ParserElement.enablePackrat()




def is_number(s):
    if s=='j':
    	return False
    try:
        float(s) # for int, long and float
    except ValueError:
        try:
            complex(s) # for complex
        except ValueError:
            return False
    return True

def is_hex(input_string):
        flag=True
        try:
            flag=int(input_string, 16)
        except ValueError:
            return None
	if flag:
		if '0x' in input_string:
    			return str(int(input_string, 16))
    		else:
    			return None
	else:
    		return None



config = ConfigParser.RawConfigParser()
config.read('config.properties')
timeout=config.get('ConfigurationSection', 'timeout');
app_id=config.get('ConfigurationSection', 'app_id');



#Time Out 
if timeout.strip()!='' and timeout.strip()!='None' and is_number(timeout.strip())!=False:
	TIMEOUT=timeout.strip()
else:
	TIMEOUT=60000

if app_id.strip()!='' and app_id.strip()!='None':
	Mathematica_id=app_id.strip()
else:
	Mathematica_id=None


# base language (non dynamic, not changed by the program)
# do not use name with number in the end
# these names are not supposed to be used as prorgam variables

_base = ['=','==','!=','<','<=','>','>=','*','**','!','+','-','/', '%', 'ite', 'and', 'or', 'not', 'implies', 'all', 'some', 'null']
_infix_op = ['=','==','!=','<','<=','>','>=','*','**','+','-','/', '%', 'implies']

# variables introduced in the translation

def isvariable(x):
    if x.startswith('_x') or  x.startswith('_y') or  x.startswith('_n'):
        return True
    else:
        return False



# program variables and temporary program variables and big N

def is_program_var(x,v):
    if x.startswith('_N'):
        return True
    for y in v:
        if x==y or x.startswith(y+OUT) or (x.startswith(y+TEMP) and 
                                           x[len(y+TEMP):].isdigit()) or x.startswith(y+LABEL):
            return True
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
RET for return value of a function
Temporary function names are constructed as: 
variable-name + TEMP + TC
Output function names are: 
variable-name + LABEL
for those with label, or
variable-name + OUT
for those without label.
 TC: TempCount, a global counter for naming temporary variables
 LC: LoopCount, a global counter for naming loop constants and variables
"""

RET='RET'
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
# or constants like '1', 'x'; args - a list of exprs
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
                return '('+(' '+op+' ').join(list(expr2string1(x) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2string1(args[0])
        elif op=='implies' and len(args)==2:
            return expr2string1(args[0])+ ' -> '+expr2string1(args[1])
        elif op in _infix_op and len(args)==2:
            return '(' + expr2string1(args[0])+ op+expr2string1(args[1])+')'
        else:
            return op +'('+ ','.join(list(expr2string1(x) for x in args))+ ')'



def expr2stringvfact(e,var_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2stringvfact(args[0],var_map)
            else:
                return '('+(' '+op+' ').join(list(expr2stringvfact(x,var_map) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2stringvfact(args[0],var_map)
        elif op=='implies' and len(args)==2:
            return expr2stringvfact(args[0],var_map)+ ' -> '+expr2stringvfact(args[1],var_map)
        elif op in _infix_op and len(args)==2:
            t1=args[0][0]
            if t1 not in _base and is_number(t1)==False:
            	parameter=[]
            	
            	for x in range(0, len(args[0])):
            		parameter.append('int')
            	var_map[t1]=parameter
            t2=args[1][0]
            if t2 not in _base and is_number(t2)==False:
            	parameter=[]
            	
            	for x in range(0, len(args[1])):
            		parameter.append('int')
            		
            	var_map[t2]=parameter
            return '(' + expr2stringvfact(args[0],var_map)+ op+expr2stringvfact(args[1],var_map)+')'
        else:
            if isArrayFunction(op)==True:
            	count=0
            	for parameter in args:
            	
            		if len(parameter)==1:
            			name=expr2stringvfact(parameter,var_map)
            			if is_number(name)==False:
            				type_list=[]
            				if count==0:
            					type_list.append('array')
            				else:
            					type_list.append('int')
            				count=count+1
            			
            				var_map[name]=type_list
            			
            return op +'('+ ','.join(list(expr2stringvfact(x,var_map) for x in args))+ ')'






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
                parameter1=None
                parameter2=None
                for x in args:
                    if parameter1==None:
                    	parameter1=expr2z3(x,var_cstr_map)
                    else:
                    	parameter2=expr2z3(x,var_cstr_map)
                if op=='or':
                	return 'Or('+parameter1+','+parameter2+')'
                else:
                	if op=='and':
                		return 'And('+parameter1+','+parameter2+')'
                #return '('+(' '+op+' ').join(list(expr2z3(x,var_cstr_map) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'Not('+expr2z3(args[0],var_cstr_map)+')'
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





#expression to z3 constraint

#e=['or', ['or', ['or', ['<=', ['B'], ['0']], ['<=', ['A'], ['0']]], ['<=', ['+', ['A'], ['B']], ['B']]], ['<=', ['+',['A'], ['B']], ['A']]]

#e=['+', ['*', ['*', ['/', ['B'], ['']], ['/', ['A'], ['C']]], ['+', ['+', ['A'], ['B']], ['B']]], ['-', ['+',['A'], ['B']], ['A']]]

#e=['Y3', ['+', ['_n1'], ['1']], ['A'], ['B']], ['ite', ['>', ['A'], ['B']], ['Y3', ['_n1'], ['A'], ['B']], ['+', ['A'], ['*', ['2'], ['B']]]]

#e=['ite', ['>', ['A'], ['B']], ['Y3', ['_n1'], ['A'], ['B']], ['+', ['A'], ['*', ['2'], ['B']]]]

#var_cstr_map={}

def expr2z3_update(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
            	expression=expr2z3_update(args[0],var_cstr_map)
            	if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'If' not in expression and 'Implies' not in expression:
            		expression=simplify_expand_sympy(expression)
                return expression
            else:
                parameter1=None
                parameter2=None
                for x in args:
                    if parameter1==None:
                    	parameter1=expr2z3_update(x,var_cstr_map)
                    	if '/' not in parameter1 and 'Or' not in parameter1 and '==' not in parameter1 and 'And' not in parameter1 and 'If' not in parameter1 and 'Implies' not in parameter1:
                    		parameter1=convert_pow_op_fun(simplify_expand_sympy(parameter1))
                    	elif 'Or' not in parameter1 and 'And' not in parameter1 and 'If' not in parameter1 and 'Implies' not in parameter1:
                    		parameter1=convert_pow_op_fun(parameter1)
                    else:
                    	parameter2=expr2z3_update(x,var_cstr_map)
                    	if '/' not in parameter2 and 'Or' not in parameter2 and '==' not in parameter2 and 'And' not in parameter2 and 'If' not in parameter2 and 'Implies' not in parameter2:
                    		parameter2=convert_pow_op_fun(simplify_expand_sympy(parameter2))
                    	elif 'Or' not in parameter2 and 'And' not in parameter2 and 'If' not in parameter2 and 'Implies' not in parameter2:
                    		parameter2=convert_pow_op_fun(parameter2)
                    	
                if op=='or':
                	return 'Or('+parameter1+','+parameter2+')'
                else:
                	if op=='and':
                		return 'And('+parameter1+','+parameter2+')'
        elif op=='not' and len(args)==1:
            expression=expr2z3_update(args[0],var_cstr_map)
            if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'If' not in expression and 'Implies' not in expression:
            	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            elif 'Or' not in expression and 'And' not in expression and 'If' not in expression and 'Implies' not in expression:
            	expression=convert_pow_op_fun(expression)
            return 'Not('+expression+')'
        elif op=='implies' and len(args)==2:
            if len(var_cstr_map)==0:
            	expression1=expr2z3_update(args[0],var_cstr_map)
            	expression2=expr2z3_update(args[1],var_cstr_map)
            	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
            		expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            	elif 'Or' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
			expression1=convert_pow_op_fun(expression1)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
            		expression2=convert_pow_op_fun(simplify_expand_sympy(expression2))
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+expression1+ ','+expression2+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			expression1=expr2z3_update(args[0],var_cstr_map)
            			if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
            				expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            			elif 'Or' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
					expression1=convert_pow_op_fun(expression1)
            			list_constrn="And("+expression1+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	expression2=expr2z3_update(args[1],var_cstr_map)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
            		expression1=simplify_expand_sympy(expression2)
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+list_constrn+ ','+expression2+')'
        elif op in _infix_op and len(args)==2:
        	expression1=expr2z3_update(args[0],var_cstr_map)
        	expression2=expr2z3_update(args[1],var_cstr_map)
        	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'If' not in expression1 and 'Implies' not in expression1:
        		expression1=simplify_expand_sympy(expression1)
        	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'If' not in expression2 and 'Implies' not in expression2:
        		expression2=simplify_expand_sympy(expression2)
        	if op=='/':
        		return '(' + expression1+ op+expression2+')'
        	elif op=='=':
        		return '(' + expression1+ '=='+expression2+')'
        	else:
        		expression='(' + expression1+ op+expression2+')'
        		if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression:
        			return simplify_expand_sympy(expression)
        		else:
        			return expression
        else:
            if op=='ite':
            	return 'If('+ ','.join(list(trim_p(conditionSimplifyPower(expr2z3_update(x,var_cstr_map))) for x in args))+ ')'
            else:
            	if isArrayFunction(op)==True:
            		parameter_list=[]
            		defineDetailtemp=[]
            		defineDetailtemp.append(op)
            		parameter_list.append('array')
            		for x in range(0, len(args)):
            			parameter_list.append('int')
            		defineDetailtemp.append(len(args))
            		defineDetailtemp.append(parameter_list)
            		defineDetaillist.append(defineDetailtemp)
            	return op +'('+ ','.join(list(trim_p(expr2z3_update(x,var_cstr_map)) for x in args))+ ')'




def expr2z3_update_postCond(e,var_cstr_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        if isvariable(op)==True:
    		var_cstr_map[op]=op+">=0"
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
            	expression=expr2z3_update_postCond(args[0],var_cstr_map)
            	if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
            		expression=simplify_expand_sympy(expression)
                return expression
            else:
                parameter1=None
                parameter2=None
                for x in args:
                    if parameter1==None:
                    	parameter1=expr2z3_update_postCond(x,var_cstr_map)
                    	if '/' not in parameter1 and 'Or' not in parameter1 and '==' not in parameter1 and 'And' not in parameter1 and 'Implies' not in parameter1 and 'If' not in parameter1:
                    		parameter1=convert_pow_op_fun(simplify_expand_sympy(parameter1))
                    	elif 'Or' not in parameter1 and 'And' not in parameter1 and 'If' not in parameter1 and 'Implies' not in parameter1 and 'If' not in parameter1:
                    		parameter1=convert_pow_op_fun(parameter1)
                    else:
                    	parameter2=expr2z3_update_postCond(x,var_cstr_map)
                    	if '/' not in parameter2 and 'Or' not in parameter2 and '==' not in parameter2 and 'And' not in parameter2 and 'Implies' not in parameter2 and 'If' not in parameter2:
                    		parameter2=convert_pow_op_fun(simplify_expand_sympy(parameter2))
                    	elif 'Or' not in parameter2 and 'And' not in parameter2 and 'If' not in parameter2 and 'Implies' not in parameter2 and 'If' not in parameter2:
                    		parameter2=convert_pow_op_fun(parameter2)
                if op=='or':
                	return 'Or('+parameter1+','+parameter2+')'
                else:
                	if op=='and':
                		return 'And('+parameter1+','+parameter2+')'
        elif op=='not' and len(args)==1:
            expression=expr2z3_update_postCond(args[0],var_cstr_map)
            if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
            	expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            elif 'Or' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
            	expression=convert_pow_op_fun(expression)
            return 'Not('+expression+')'
        elif op=='implies' and len(args)==2:
            if len(var_cstr_map)==0:
            	expression1=expr2z3_update_postCond(args[0],var_cstr_map)
            	expression2=expr2z3_update_postCond(args[1],var_cstr_map)
            	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
            		expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            	elif 'Or' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
			expression1=convert_pow_op_fun(expression1)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
            		expression2=convert_pow_op_fun(simplify_expand_sympy(expression2))
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+expression1+ ','+expression2+')'
            else:
            	list_constrn=""
                for x in var_cstr_map:
            		if list_constrn=="":
            			expression1=expr2z3_update_postCond(args[0],var_cstr_map)
            			if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
            				expression1=convert_pow_op_fun(simplify_expand_sympy(expression1))
            			elif 'Or' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
					expression1=convert_pow_op_fun(expression1)
            			list_constrn="And("+expression1+","+var_cstr_map[x]+")"
            		else:
            			list_constrn="And("+list_constrn+","+var_cstr_map[x]+")"
            	expression2=expr2z3_update_postCond(args[1],var_cstr_map)
            	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
            		expression1=simplify_expand_sympy(expression2)
            	elif 'Or' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
			expression2=convert_pow_op_fun(expression2)
            	return 'Implies('+list_constrn+ ','+expression2+')'
        elif op in _infix_op and len(args)==2:
        	expression1=expr2z3_update_postCond(args[0],var_cstr_map)
        	expression2=expr2z3_update_postCond(args[1],var_cstr_map)
        	if '/' not in expression1 and 'Or' not in expression1 and '==' not in expression1 and 'And' not in expression1 and 'Implies' not in expression1 and 'If' not in expression1:
        		expression1=simplify_expand_sympy(expression1)
        	if '/' not in expression2 and 'Or' not in expression2 and '==' not in expression2 and 'And' not in expression2 and 'Implies' not in expression2 and 'If' not in expression2:
        		expression2=simplify_expand_sympy(expression2)
        	if op=='/':
        		return '(' + expression1+ op+expression2+')'
        	elif op=='=':
        		return '(' + expression1+ '=='+expression2+')'
        	else:
        		expression='(' + expression1+ op+expression2+')'
        		if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'Implies' not in expression and 'If' not in expression:
        			return simplify_expand_sympy(expression)
        		else:
        			return expression
        else:
            if op=='ite':
            	stmt_list=[]
            	final_stmt=''
            	for x in args:
            		stmt=conditionSimplifyPower(expr2z3_update_postCond(x,var_cstr_map))
            		if str(trim_p(stmt))!='0':
            			stmt_list.append(trim_p(stmt))
            	if len(stmt_list)==2:
            		final_stmt='Implies('+final_stmt+','.join(stmt_list)+')'
            	else:
            		final_stmt='If('+final_stmt+','.join(stmt_list)+')'
            	return final_stmt
            else:
                if isArrayFunction(op)==True:
	        	parameter_list=[]
	                defineDetailtemp=[]
	                defineDetailtemp.append(op)
	                parameter_list.append('array')
	                for x in range(0, len(args)):
	                	parameter_list.append('int')
	                defineDetailtemp.append(len(args))
	                defineDetailtemp.append(parameter_list)
            		defineDetaillist.append(defineDetailtemp)
            	return op +'('+ ','.join(list(trim_p(expr2z3_update_postCond(x,var_cstr_map)) for x in args))+ ')'









def conditionSimplifyPower(expression):
	if '/' not in expression and 'Or' not in expression and '==' not in expression and 'And' not in expression and 'If' not in expression and 'char(' not in expression and 'Implies' not in expression:
		return convert_pow_op_fun(simplify_expand_sympy(expression))
	elif 'Or' not in expression and 'And' not in expression and 'If' not in expression and 'char(' not in expression and 'Implies' not in expression:
		return convert_pow_op_fun(expression)
	else:
		return expression

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
                for x in args:
                    expr2varlist(x,variable_list)
        elif op=='not' and len(args)==1:
            expr2varlist(args[0],variable_list)
        elif op=='implies' and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        elif op in _infix_op and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        else:
            for x in args:
        	expr2varlist(x,variable_list)


#return the list of program variables in an expression 

def expr_func(e,v): #e - expr
    ret = []
    f = expr_op(e)
    if is_program_var(f,v):
        ret.append(f)
    for e1 in expr_args(e):
        ret = ret + expr_func(e1,v)
    return ret
    

#substitution of functors: in e, replace functor n1 by n2
def expr_sub(e,n1,n2): # e - expr; n1,n2 - strings
    e1=list(expr_sub(x,n1,n2) for x in e[1:])
    if e[0]==n1:
        return [n2]+e1
    else:
        return e[:1]+e1
        

#substitution of functors in a set: in e, for all x in v1 but not in v2, replace x+n1 by x+n2
def expr_sub_set(e,n1,n2,v1,v2): #e - expr; n1,n2 - strings, v1, v2 - sets of strings
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

def expr_replace(e,e1,e2): #e,e1,e2: expr
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

def expr_sub_var_list(e,l1,l2): #e: expr, l1,l2: lists of the same length of exprs
    for i,x in enumerate(l1):
        if e==x:
            return l2[i]
    return e[:1]+list(expr_sub_var_list(y,l1,l2) for y in expr_args(e))


# compute E[n] extend(e,n,excl,v). n is an expr like ['_n1'], excl is a container of strings that are not to be extended
def extend(e,n,excl,v):
    op = expr_op(e)
    x = [n] if is_program_var(op,v) and not (op in excl) else []
    return expres(op, list(extend(e1,n,excl,v) for e1 in expr_args(e)) + x)


#A dictionary of dependencies para is such that, if x is an input variable, then para[x] is a list whose first element is 1 and the second element is the variable's parameter name; otherwise, para[x] is the list of input variables that x is depended on. 
#example: para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'], ['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function depending on X and Y whose corresponding parameters are '_y1' and '_y2', respectively.
#So after parameterization, X11(a,X) will become X11(a,_y1,_y1,_y2)

def parameterize_expres(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return para[e[0]][1]+list(parameterize_expres(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expres(x,para) for x in e[1:])+para[e[0]][1]
    else:
        return e[:1]+list(parameterize_expres(x,para) for x in e[1:])


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
 5. constraints from smallest macro smallest(N,n,e):
    ['s0', e(N)] 
    ['s1', forall n<N -> not e]

 Examples: a' = a+1: ['e', ['a\''], ['+',['a'],['1']]]
 N(x) = 0 if x<I else N(x-1)+1 is divided into two axioms:
 N(x) = 0 iff x<I:  
 ['d0', ['N',['x']], ['<', ['x'],['I']]] and
 N(x) = n+1 iff n=N(x-1): 
 ['d1','n', ['N',['x']], ['=',['n'], ['N', ['-', ['x'],['1']]]]]
"""


# constructors
def wff_e(e1,e2): #e1,e2: expr
    return ['e',e1,e2]

def wff_i0(k,e1,e2): #k: int; e1,e2: expr
    return ['i0',k,e1,e2]

def wff_i1(k,v,e1,e2): #k: int; v: string; e1,e2: expr
    return ['i1',k,v,e1,e2]

def wff_d0(e,c): #e: expr; c: expr
    return ['d0',e,c]

def wff_d1(v,e,c): #v: string, e and c: expr
    return ['d1',v,e,c]

def wff_a(e): #e: expr
    return ['a',e]

def wff_s0(e):
    return ['s0',e]
def wff_s1(e):
    return ['s1',e]
    
    
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
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            return expr2string1(w[1])
            
#print in normal infix notation
def wff2stringvfact(w,var_map):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            return expr2stringvfact(w[-2],var_map)+' = '+ expr2stringvfact(w[-1],var_map)
        elif w[0] == 'd0':
            return expr2stringvfact(w[1],var_map)+'=0 <=> '+ expr2stringvfact(w[2],var_map)
        elif w[0] == 'd1':
            return expr2stringvfact(w[2],var_map)+'='+w[1]+'+1 <=> '+expr2stringvfact(w[3],var_map)
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1':
            return expr2stringvfact(w[1],var_map)

#strip '(' at the beginning and matching ')' in the end of a string
def trim_p(s):
    if s.startswith('(') and s.endswith(')'):
        return trim_p(s[1:-1])
    else:
        return s


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
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        #equations.append('ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))')
                        #return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        #equations.append(arg_list[1])
                        #return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'

        else:
            return expression







#convert wff to z3 constraint
def wff2z3_update(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update(w[-2],var_cstr_map)
            rhs=expr2z3_update(w[-1],var_cstr_map)           
            list_var_str=qualifier_list(var_cstr_map.keys())
            if isArrayFunction(w[-2][0])==True:
            	del var_cstr_map['_x1']
            	flag_constr=True
            	
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                	else:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[1],var_cstr_map)
            rhs=expr2z3_update(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update(w[2],var_cstr_map)
            rhs=expr2z3_update(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
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
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
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

                    new_w = copy.deepcopy(w)
                    for element in var_cstr_map.keys():
                    	fun=[]
                    	fun.append('_f')
                    	parameter=[]
                    	parameter.append(element)
                    	fun.append(parameter)
                    	sub=[]
                    	sub.append(element)
                    	new_w[1]=expr_replace(new_w[1],sub,fun) #expr_replace_const(new_w[1],element,fun)
		    new_expression=expr2z3_update(new_w[1],var_cstr_map)
		    new_arg_list=extract_args(new_expression)
                    
                    #old_arg_list=arg_list[1]
                    old_arg_list=new_arg_list[1]
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        else:
            return expression





#convert wff to z3 constraint
def wff2z3_update_postCond(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
            var_cstr_map={}
            flag_constr=False
            lhs=expr2z3_update_postCond(w[-2],var_cstr_map)
            rhs=expr2z3_update_postCond(w[-1],var_cstr_map)

            list_var_str=qualifier_list(var_cstr_map.keys())
            
            if isArrayFunction(w[-2][0])==True:
	    	del var_cstr_map['_x1']
            	flag_constr=True
            
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
            	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
            if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
            	if w[0] == 'i1':
                	return "ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+lhs+' == '+ rhs+"))"
                else:
                	if flag_constr==True:
                		return 'ForAll(['+list_var_str+'],'+lhs+' == '+ rhs+")"
            else:
                return lhs+' == '+ rhs
        elif w[0] == 'd0': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update_postCond(w[1],var_cstr_map)
            rhs=expr2z3_update_postCond(w[2],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return 'ForAll(['+list_var_str+'],'+lhs+'=0 == '+ rhs+")"
            else:
                return lhs+'=0 == '+ rhs
        elif w[0] == 'd1': # Bi-implications are represented using equality == in z3py
            var_cstr_map={}
	    lhs=expr2z3_update_postCond(w[2],var_cstr_map)
            rhs=expr2z3_update_postCond(w[3],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            lhs=w[1]+'+1'
            if 'Or' not in lhs and 'And' not in lhs and 'If' not in lhs and '/' not in lhs:
	    	lhs=convert_pow_op_fun(simplify_expand_sympy(lhs))
	    if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
            	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
            if list_var_str is not None and list_cstr_str is not None:
                return "ForAll(["+list_var_str+"],"+lhs+' == '+rhs+")"
            else:
                return lhs+' == '+rhs
        elif w[0]=='a' or w[0]=='s0':
            var_cstr_map={}
	    expression=expr2z3_update_postCond(w[1],var_cstr_map)
            list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
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
                    else:
                        return arg_list[1]
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    
            else:
                return expression
        elif w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update_postCond(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression:
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
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                    else:
                    	return 'ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'

        else:
            return expression






#convert wff to z3 constraint(Special Case N=0 V E(n/(N-1)))
def wff2z3SC_update(w):
	if w[0]=='s1':
            var_cstr_map={}
            equations=[]
	    expression=expr2z3_update(w[1],var_cstr_map)
	    list_var_str=qualifier_list(var_cstr_map.keys())
            list_cstr_str=cstr_list(var_cstr_map.values())
            #expression=convert_pow_op_fun(simplify_expand_sympy(expression))
            if 'Or' not in expression and 'And' not in expression and 'If' not in expression and '/' not in expression and 'Implies' not in expression:
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
                    
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        return 'ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))'
                        #return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        return arg_list[1]
                        #return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'
                    
                    
                    
#convert wff to z3 constraint(Special Case N=0 V E(n/(N-1)))
def wff2z3SC(w):
	if w[0]=='s1':
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
                    arg_list[1]='Or('+axms[1]+'==0,'+simplify_expand_sympy(arg_list[1].replace(axms[0],'('+axms[1]+'-1)'))+')'
                    if list_var_str_new is not None and list_cstr_str_new is not None:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))'
                        return 'ForAll(['+str(list_var_str_new)+'],Implies('+str(list_cstr_str_new)+','+arg_list[1]+'))'
                        #return equations
                        #return 'ForAll(['+list_var_str+'],Implies('+arg_list[0]+','+arg_list[1]+'))'
                    else:
                        #equations.append('ForAll(['+str(list_var_str)+'],Implies(And('+arg_list[0]+','+str(list_cstr_str)+'),'+old_arg_list+'))')
                        return arg_list[1]
                        #return equations
                else:
                    return 'ForAll(['+list_var_str+'],Implies('+list_cstr_str+','+expression+'))'
                    #return 'ForAll(['+list_var_str+'],'+expression+')'



#Function Collect Condition From All Recursive  Formulas

def getAllCondtion(w,condition_map):
	if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1':
		var_cstr_map={}
	        lhs=expr2z3(w[-2],var_cstr_map)
	        rhs=expr2z3(w[-1],var_cstr_map)
	        if 'ite' not in str(rhs):
	        	rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
	        extract_conditions(rhs,condition_map)

def extract_conditions(expression,condition_map):
	if 'If' in expression:
		axioms=extract_args(expression)
	        condition_map[axioms[0]]=axioms[0]
	        if 'If' in axioms[1]:
			extract_conditions(axioms[1],condition_map)
		if 'If' in axioms[2]:
			extract_conditions(axioms[2],condition_map)


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
def wff_extend(w,n,excl,v): #w: wff, n: expr, excl: container of strings
    if w[0]=='e': #['e',e1,e2]
        return ['e',extend(w[1],n,excl,v),extend(w[2],n,excl,v)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],extend(w[2],n,excl,v),extend(w[3],n,excl,v)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],extend(w[3],n,excl,v),extend(w[4],n,excl,v)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',extend(w[1],n,excl,v),extend(w[2],n,excl,v)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],extend(w[2],n,excl,v),extend(w[3],n,excl,v)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': 
        return [w[0], extend(w[1],n,excl,v)]
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
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_dict(w[1],d)]
    else:
        print('Not a wff')
        return

#parameterize a set of axioms by making program functions as input variables
#para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function taking two new parameters '_y1','_y2'
#X11(a,X)=X11(a+b,1) will become X11(a,_y1,_y1,_y2)=X11(a+b,1,_y1,_y2)
 
def parameterize_wff(ax,para):
    if not (ax[0] == 'a' or ax[0]=='s0' or ax[0]=='s1'):
        e1 = parameterize_expres(ax[-2],para)
        e2 = parameterize_expres(ax[-1],para)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expres(ax[-1],para)
        return [ax[0],e2]
        

#for all x in dep_set, add dep_set[x] as arguments, except when x is RET+OUT,
#replace it by foo()

def parameterize_axioms_fun(axioms,dep_set):
    for x in axioms:
        parameterize_wff_fun(x,dep_set)

def parameterize_wff_fun(ax,dep_set):
    if not (ax[0] == 'a' or ax[0]=='s0' or ax[0]=='s1'):
        e1 = parameterize_expres_fun(ax[-2],dep_set)
        e2 = parameterize_expres_fun(ax[-1],dep_set)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expres_fun(ax[-1],dep_set)
        return [ax[0],e2]

def parameterize_expres_fun(e,dep_set): 
    if e[0]==RET+OUT:
        if len(e) != 1:
            print 'Something is wrong '+RET+OUT+' should not have arguments'
            return
        else:
            return dep_set[RET+OUT]
    elif e[0] in dep_set:
        return expres(e[0],list(parameterize_expres_fun(x,dep_set) for x in e[1:])+dep_set[e[0]])
    else:
        return expres(e[0],list(parameterize_expres_fun(x,dep_set) for x in e[1:]))
        
        
    

def eqset2string(d):
    for x in d:
        print wff2string(d[x])
def eqset2string1(d):
    for x in d:
        print wff2string1(d[x])
 
def eqset2stringvfact(d,var_map):
    for x in d:
        wff2stringvfact(d[x],var_map)
        
def eqset2constraintlist(d):
    equation_list=[]
    for x in d:
        equation_list.append(wff2z3(d[x]))
    return equation_list
    

def eqset2constraintlist_update(d):
    equation_list=[]
    for x in d:
        equation_list.append(wff2z3_update(d[x]))
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
 We assume no local function definitions, so the p in 'if b then p else p'
 'while b do p', 'foo(x,...,y) {b}' is a normal body of program statements.

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
6. function definition
 foo(x,...,y) { B }
['-1','fun',['foo','x',..,'y'], b]
where 'foo' is the name of the function, 'x',...,'y' parameters, and
b the Prog representing B. We assume that B has no local function, i.e.
a normal body of statements. 
We assume a unique string 'RET' representing return
value because we do not have a special return statement.
Instead, a return statement
 l: return E
is represented as a normal assignment
 l: RET = e
We expect this will be the last statement of the body b
7. sequence of functions
 foo1(...) {B1}, ..., fook(...) {Bk}
['-1', 'prog', [f1,...,fk]]
where fi is the program representation of fooi(...) {Bi}. For this, the list
of variables v needs to be a dictionary indexed by the function names 
'foo1',...,'fook' whose value v['foo'] is the list of variables used in the function

"""



# for testing flag=1 (original translation), flag=2 (inductive definition for smallest N)
def translate1(p,v,flag):
    global TC
    global LC
    TC=0
    LC=0
    if p[1]=='prog':
        f_map={}
        a_map={}
        o_map={}
        cm_map={}
        assert_list_map={}
        assume_list_map={}
        res = translate0(p,v,flag)
        for fn in res:
            x,f,o,a,l = res[fn]
            #print f
	    #print o
            #print a
            #print '--------------------'
            print('Output for '+fn+':')
            f,o,a,cm = rec_solver(f,o,a)          
            #print f
            #print o
            #print a
            
            
            f,o,a,cm = getDummyFunction(f,o,a,cm)
    
            f,o,a,assert_list,assume_list=getAssertAssume(f,o,a,cm)
            
            #assert_list=[]
            
            #assume_list=[]
            

            f_map[fn]=f
	    o_map[fn]=o
	    a_map[fn]=a
            cm_map[fn]=cm
            
            assert_list_map[fn]=assert_list
            assume_list_map[fn]=assume_list
            
            output_axioms_fn(f,o,a)
            print('\n4. Assumption :')
            for x in assume_list:
            	if x[0]=='i1':
			print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
		else:
			if x[0]!='i0':
                    		print wff2string1(x)
            print('\n5. Assertion :')
            for x in assert_list:
                if x[0]=='i1':
                    print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
                else:
                	if x[0]!='i0':
                    		print wff2string1(x)
        return f_map,o_map,a_map,cm_map,assert_list_map,assume_list_map
        
    elif p[1]=='fun':
        fn,f,o,a,l = translate0(p,v,flag)
        print('Output for ')
        print(fn)
        f,o,a,cm = rec_solver(f,o,a)
        f,o,a,cm = getDummyFunction(f,o,a,cm)
        f,o,a,assert_list,assume_list=getAssertAssume(f,o,a,cm)
        output_axioms_fn(f,o,a)
    	print('\n4. Assumption :')
	for x in assume_list:
        	if x[0]=='i1':
			print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
		else:
			if x[0]!='i0':
                    		print wff2string1(x)
    	print('\n5. Assertion :')
	for x in assert_list:
                if x[0]=='i1':
                    print 'ForAll '+x[2]+' ( '+ expr2string1(x[4]) +' ) '
                else:
                	if x[0]!='i0':
                    		print wff2string1(x)
        return f,o,a,cm,assert_list,assume_list
    else:
        f,o,a,l = translate0(p,v,flag)
        #Add by Pritom Rajkhowa 10 June 2016
    	f,o,a,cm = rec_solver(f,o,a)
    	f,o,a,cm = getDummyFunction(f,o,a,cm)
    	f,o,a,assert_list,assume_list=getAssertAssume(f,o,a,cm)
    	output_axioms_fn(f,o,a)
    	print('\n4. Assumption :')
	for x in assume_list:
	         if x[0]=='i1':
	         	print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
	         else:
	                if x[0]!='i0':
                    		print wff2string1(x)
    	print('\n5. Assertion :')
	for x in assert_list:
                if x[0]=='i1':
                    print 'ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) '
                else:
                	if x[0]!='i0':
                    		print wff2string1(x)
    	return f,o,a,cm,assert_list,assume_list




def output_axioms_fn(f,o,a):
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
    if p[1]=='fun':
        return translateFun(p,v,flag)
    if p[1]=='prog':
        return translateProgram(p,v,flag)
     
     
# function definition
def translateFun(p,v,flag): #p=['-1','fun',['foo','x',..,'y'], b]
    global TC
    global LC
    TC=0
    LC=0
    f,o,a,l = translate0(p[-1],v,flag)
    axioms=a
    for x in f:
        axioms=axioms+[f[x]]
    for x in o:
        axioms=axioms+[o[x]]
    g = graph(axioms,v) #construct dependency graph
    param = list(expres(a) for a in p[-2][1:]) #parameters of the function
    dep_set = {} #dependency set for each variables in the axiom
    dep_set[RET+OUT]=expres(p[-2][0],param) #initialize it to the return function
    for (x,y) in g:
        if (not x in dep_set) and (not expres(x) in param):
            dep = []
            for x1 in reach_set([x],g):
                if (expres(x1) in param) and not (expres(x1) in dep):
                    dep.append(expres(x1))
            dep_set[x] = dep
    
    
    for x in f:
        f[x]=parameterize_wff_fun(f[x],dep_set)
    for x in o:
        o[x]=parameterize_wff_fun(o[x],dep_set)
    for i,ax in enumerate(a):
        a[i]=parameterize_wff_fun(ax,dep_set)
    return [dep_set[RET+OUT],f,o,a,l]
    
      
    
    
# program: a set of functions   
#p=['-1','prog',[f1,...,fk]] 
#for each fi, v[fi] is the list of variables used in the function fi
def translateProgram(p,v,flag): 
    result = {}
    for x in p[-1]:
        funcName = x[2][0]
        result[funcName] = translate0(x,v[funcName],flag)
    return result


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
        axioms[i0]=wff_extend(ax0, loop_var, frame_axioms,v)
    for x in frame_axioms:
        ax = frame_axioms[x] #ax = ['e',e1,e2]
        if llabel != '-1': #body has label: keep axioms about it
            axioms.append(ax)
        #generate the new frame axiom
        frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
    out_axioms00={}
    for x in out_axioms0: 
        ax = out_axioms0[x] #ax = ['e',e1,e2]
        #change output and input variable names to loop and extend e2[loop_var]
        ax = wff_sub_set(ax,old_out,init,v,frame_axioms)
        ax = wff_sub_set(ax,'',init,v,frame_axioms)
        out_axioms00[x]=ax[:2]+[extend(ax[2],loop_var,frame_axioms,v)]
    # using Pritom's solve_rec() to try to get closed-form solution
    found_solution=True
    variable=None
    while found_solution:
        found1=False
        for x in out_axioms00.keys():
            ax=out_axioms00[x]
            if expr_func(ax[2],v)==[]:
                found1=True
                e=extend(ax[1],loop_var,frame_axioms,v)
                axioms.append(wff_e(e,ax[2]))
                del out_axioms00[x]
                for y in out_axioms00:
                    ax1= out_axioms00[y]
                    out_axioms00[y]=ax1[:2]+[expr_sub_dict(ax1[2],{expr_op(ax[1]):ax[2]})]
            else:
                e1=wff_i1(0,expr_op(loop_var),extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms,v),ax[2])
                e2=wff_i0(0,extend(ax[1],expres('0'),frame_axioms,v),expres(x,expr_args(ax[1])))
                res=solve_rec(e1,e2)
                if res != None: #res = ['i2',k,n,e1,e2]
                    found1=True
                    variable=res[2] # Variable add by Pritom Rajkhowa
                    axioms.append(wff_e(res[3],res[4]))
                    del out_axioms00[x]
                    for y in out_axioms00:
                        ax1= out_axioms00[y]
                        out_axioms00[y]=ax1[:2]+[expr_sub_dict(ax1[2],{expr_op(res[3]):res[4]})]
        if not found1:
            found_solution=False

    for x in out_axioms00:
        ax = out_axioms00[x] #ax = ['e',e1,e2]
        e1=extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms,v)
        e2=ax[2]
        axioms.append(wff_i1(len(expr_args(e1))-1,expr_op(loop_var),e1,e2))
    
    #base case
    for x in out_axioms00:
        arity = len(v[x])-2
        args = list(expres('_x'+str(i+1)) for i in range(arity))
        axioms.append(wff_i0(arity,expres(x+init,args+[expres('0')]), expres(x,args)))
    c=p[2] #loop condition
    c=expr_sub_set(c,'',init,v,frame_axioms)
    c = extend(c,loop_var,frame_axioms,v) #add the smallest macro
     #Add by pritom
    cc = copy.deepcopy(c)
    axioms.append(wff_s0(expr_sub(expr_complement(cc),expr_op(loop_var),expr_op(smallest))))  
    #axioms.append(wff_s0(expres('not',[expr_sub(c,expr_op(loop_var),expr_op(smallest))])))
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
    #substitution of closed form solution by pritom rajkhowa
    constant='_N'+str(LC)
    variable='_n'+str(LC)
    update_axioms=[]
    equations=[]

    for ax in axioms:
    	if ax[0]=='e':
    		equations.append(ax)
    	else:
    		update_axioms.append(ax)
    
    for equation in equations:
    	equation1=copy.deepcopy(equation)
    	update_axioms=solnsubstitution(update_axioms,equation[1],equation[2])
    	equation1[1]=expr_replace_const(equation1[1],variable,constant)
    	equation1[2]=expr_replace_const(equation1[2],variable,constant)
    	update_axioms=solnsubstitution(update_axioms,equation1[1],equation1[2])
    	for x in out_axioms:
		stmt=out_axioms[x]
    		stmt[2]=expr_replace(stmt[2],equation1[1],equation1[2])
    axioms=update_axioms
    updated_axioms=[]
    for ax in axioms:
    	if ax[0]=='s0':
        	expression=expr2string1(ax[1])
        	if '->' not in expression and constant in expression:
        		if '>=' in expression and 'and' not in expression and 'or' not in expression:
    				expression=normal_form_constant(expression, constant)
    				pp = getParser()
    				tree = pp.parse_expression(str(expression))			 
    				axupdate=construct_expression_normal(tree)
    				if axupdate is not None:
    					updated_axioms.append(axupdate)
    				else:
    					updated_axioms.append(ax)
        		elif '<=' in expression and 'and' not in expression and 'or' not in expression:
    				expression=normal_form_constant(expression, constant)
    				pp = getParser()
    				tree = pp.parse_expression(str(expression))		 
    				axupdate=construct_expression_normal(tree)
    				if axupdate is not None:
    					updated_axioms.append(axupdate)
    				else:
    					updated_axioms.append(ax)
    			else:
    				updated_axioms.append(ax)
    		else:
    			updated_axioms.append(ax)
    		
    	else:
     		updated_axioms.append(ax)
    axioms=[]
    for ax in updated_axioms:
    	axioms.append(ax)
    
    #substitution of closed form solution by pritom rajkhowa  
    if flag==2:
        g = graph(axioms,v) #construct dependency graph
        for x in expr_func(p[2],v):
            if not ['_N'+str(LC), x] in g:
                g.append(['_N'+str(LC), x])
                g.append(['_N'+str(LC), x+init])
        for x in out_axioms00:
            if not [x+init,x] in g:
                g.append([x+init,x])
            if not [x,x+init] in g:
                g.append([x,x+init])
            for y in expr_func(out_axioms00[x][2],v):
                if not [x,y] in g:
                    g.append([x,y])
        #build a dictionary para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y'],...} 
        #meaning 'X' is an input variable parameterized as '_y1' and 
        #'X11' is a function taking two new parameters '_y1' and '_y2' which correspond 
        # to 'X' and 'Y', respectively
        para={} 
        for [x,x1] in g: #compute the dependency sets
            if x in v and not x in frame_axioms:
                para[x] = [1,[v[x][0]]]
            else:
                if not x in para and not x in frame_axioms:
                    t=[]
                    t1=[]
                    for y in reach_set([x],g):
                        if y in v and (not expres(y) in t1) and (not y in frame_axioms):
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
            next_args.append(parameterize_expres(out_axioms0[x][2],para))
        axioms.append(['d0',smallest1, parameterize_expres(expres('not',[p[2]]),para)])
        axioms.append(['d1','_n'+str(LC), smallest1, 
                       expres('=',[loop_var,expres('_N'+str(LC),next_args)])])
        #parameterize output axioms
        for x in out_axioms:
            out_axioms[x]=out_axioms[x][:2]+[parameterize_expr_sub(out_axioms[x][2],para)]
        new_axioms = [] #for creating new inductive definitions
        for ax in axioms:
            if ax[0]=='i1':
                x=expr_op(ax[3])
                if x.endswith(init) and x[:len(x)-len(init)] in v:
                    next_args=[]
                    for k,arg in enumerate(expr_args(ax[3])):
                        if k==ax[1]:
                            next_args.append(expres(ax[2]))
                        else:
                            a=expr_op(arg)
                            if a.startswith('_y'):
                                for b in v:
                                    if v[b][0]==a:
                                        next_args.append(parameterize_expres(out_axioms0[b][2],para))
                            else:
                                next_args.append(arg)
                    new_axioms.append(ax[0:4]+[expres(x,next_args)])
        axioms=axioms+new_axioms
    return frame_axioms, out_axioms, axioms, p[0]






#construct a graph of dependency relation in a set of equations axioms 
def graph(axioms,v):
    ret = []
    for ax in axioms:
        if ax[0]=='e' or ax[0]=='i0' or ax[0]=='i1' or ax[0]=='d0' or ax[0]=='d1':
            op=expr_op(ax[-2])
            for x in expr_func(ax[-1],v):
                if not [op,x] in ret:
                    ret.append([op,x])
        elif ax[0]=='s1':
            op=expr_op(expr_args(expr_args(ax[1])[0])[1])
            for x in expr_func(expr_args(ax[1])[1],v):
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
vfact = {'i':['_y1','int'], 'X':['_y2','int'], 'F':['_y3','int'],RET:['_y0','int']}
#translate1(fact,vfact)

#factorial as a function: return F
fact3 = ['-1','=',expres(RET),F]
funfact = ['-1','fun',['factorial', 'X'],['-1','seq',fact,fact3]]
#a main() that uses factorial
# main1() { X=factorial(2) }
main1 = ['-1','fun',['main1'],['-1','=',X,expres('factorial',[expres('2')])]]
# variable list for main1()
man1v = {'X':['_y1','int']}
# variable lists for main1p, one for each function
main1pv = {'main1':man1v,'factorial':vfact}
main1p = ['-1','prog',[funfact,main1]]
# translate1(main1p, main1pv,1)

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
Z=expres('Z')
prod1=['-1','seq',['-1','=',Z,expres('+',[Z,X])],['-1','=',Y,expres('-',[Y,['1']])]]
prod2=['-1','seq',['-1','=',X,expres('*',[['2'],X])],['-1','=',Y,expres('/',[Y,['2']])]]
prod3=['-1', 'if1', expres('=',[expres('%',[Y,['2']]), ['1']]), prod1]
prod4=['-1','seq',prod3,prod2]
prod5=['-1','while',expres('!=',[Y,['0']]),prod4]
prod = ['-1','seq',['-1','=',Z,['0']],prod5]
vprod = {'X':['_y1','int'],'Y':['_y2','int'],'Z':['_y3','int']}

#array sum array represented as a reference, and element represented by at predicate
"""
i=0;
sum=0;
while (i<size(A)) {
 sum=at(A,i)+sum
 i=i+1
}
"""
sum3=['-1','while',expres('<',[i,expres('size',[A])]),['-1','seq',['-1','=',['sum'],expres('+',[expres('at',[A,i]),['sum']])],['-1','=',i,expres('+',[i,['1']])]]]
sum2=['-1','seq',['-1','=',['sum'],['0']],sum3]
sum1=['-1','seq',['-1','=',i,['0']],sum2]
vsum = {'i':['_y1','int'],'sum':['_y2','int'],'size':['_y3','array','int'],'A':['_y4','array'],'at':['_y5','array','int','int']}

#Dijkstra's LCM algorithm
"""
X=A;  Y=B;  U=B;  V=A;
while (X!=Y) { 
  if (X>Y) {X=X-Y; V=V+U;} 
      else {Y=Y-X; U=U+V;}
}
"""

A=expres('A')
B=expres('B')
X=expres('X')
V=expres('V')
U=expres('U')
XY=expres('-',[X,Y])
YX=expres('-',[Y,X])
UV=expres('+',[U,V])
lcm1=['-1','seq',['-1','=',X,A],['-1','=',Y,B]]
lcm2=['-1','seq',lcm1,['-1','=',U,B]]
lcm3=['-1','seq',lcm2,['-1','=',V,A]]
lcm4=['-1','seq',['-1','=',X,XY],['-1','=',V,UV]]
lcm5=['-1','seq',['-1','=',Y,YX],['-1','=',U,UV]]
c1=expres('>',[X,Y])
lcm6=['-1', 'if2', c1, lcm4,lcm5]
c2=expres('!=',[X,Y])
lcm7=['-1','while',c2,lcm6]
lcm = ['-1','seq',lcm3,lcm7]
vlcm={'A':['_y1','int'],'B':['_y2','int'],'X':['_y3','int'],'Y':['_y4','int'],'U':['_y5','int'],'V':['_y6','int']}

"""
matrix multiplication from verifythis-2016 competition

int[][] matrixMultiply(int[][] A, int[][] B) {
	int n = A.length;

	// initialise C
	int[][] C = new int[n][n];

	for (int i = 0; i < n; i++) {
   		for (int k = 0; k < n; k++) {
       			for (int j = 0; j < n; j++) {
           			C[i][j] += A[i][k] * B[k][j];
       			}
   		}
	}
	return C;
 }
"""
def less(x,y):
    return expres('<',[x,y])
def passign(l,le,ri):
    return [l,'=',le,ri]
def initialize_array2(x,i,j,m,n):
    a=passign('-1',expres('d2array',[x,i,j]),expres('0')) #d2array(x,i,j)=0
    a1=passign('-1',i,expres('+',[i,expres('1')])) #i++
    a2=passign('-1',j,expres('+',[j,expres('1')])) #j++
    while1 = ['-1','while', less(j,n), ['-1','seq',a,a2]]
    body1 = ['-1','seq',while1,a1]
    body2 = ['-1','seq',passign('-1',j,expres('0')),body1]
    while2 = ['-1','while', less(i,m), body2]
    return ['-1','seq',passign('-1',i,expres('0')),while2]

mM1 = ['-1','seq',passign('-1',expres('n'),expres('length',[expres('a')])),
       initialize_array2(expres('c'),expres('i'),expres('j'),expres('n'),expres('n'))]
mM = ['-1','seq',mM1,passign('-1',expres(RET),expres('c'))]
# for now matrixMuliply only initializes C
matrixMultipy = ['-1','fun', ['matrixMultiply','a','b'],mM]
mMv = {'a':['_y1','array'],'b':['_y2','array'],'c':['_y3','array'],RET:['_y0','array'],'i':['_y4','int'],'j':['_y5','int'],'k':['_y6','int'],'n':['_y7','int'],'d2array':['_y7','array','int','int','int']}

# translate1(matrixMultipy,mMv,1)

"""

#Add by Pritom 

"""


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
Function to Take care of the parentheses During 

#substitutor='(X2(_N1(B,A),A,B)'
#left=None
#right=None

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
			leftin=None
			rightin=None
			leftin,rightin,substitutor_update=parenthesesOrganizer(substitutor,leftin ,rightin)
			if leftin is not None and leftin is not None:
				substitutor=leftin+substitutor_update+leftin
		else:
			substitutor="("+substitutor
			left=left[0:len(left)-1]
	return left,right,substitutor


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


#Test Case 1
#variable="d1array4"

#Test Case 2
#variable="d1ar4"	
	
def isArrayFunction( variable ):
	status=False
	find=regex.compile(r'([d]\d[a][r][r][a][y]\d|[d]\d[a][r][r][a][y])')
	group = find.search(variable)
	if group is not None:
		status=True
	return status

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
Convert Inequality to Normal Form

"""


def normal_form_constant(expression, constant):
    #print "*************"
    #print expression
    #print "*************"
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
    
    #print "*************"
    #print all_on_left
    #print new_rhs
    #print "*************"
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
            if values.getDimensions()>0:
            	vfact="['"+variable+"',0,['array']]"
	    else:
	    	if values.getVariableType()=='int':	
		        vfact="['"+variable+"',0,['int']]"
		elif values.getVariableType()=='unsigned':	
		        vfact="['"+variable+"',0,['int']]"
		elif values.getVariableType()=='float':
		        vfact="['"+variable+"',0,['float']]"
		elif values.getVariableType()=='double':
			vfact="['"+variable+"',0,['double']]"
                elif values.getVariableType()=='_Bool':
			vfact="['"+variable+"',0,['Bool']]"
		elif values.getVariableType()=='array':
			vfact="['"+variable+"',0,['array']]"
            if vfacts=="":
            	#vfact=''
                vfacts=vfact
            else:
                if vfact!="":
                    vfacts+=","+vfact
	
	
	for variable in variableMapOp:
            values=variableMapOp[variable]
	    if values[1]=='int':	
                vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='unsigned':	
		vfact="['"+variable+"',0,['int']]"
	    elif values[1]=='float':
                vfact="['"+variable+"',0,['float']]"
	    elif values[1]=='double':
		vfact="['"+variable+"',0,['double']]"
	    elif values[1]=='array':
	    	vfact="['"+variable+"',0,['array']]"
	    elif values[1]=='unsigned':
	    	vfact="['"+variable+"',0,['int']]"
            elif values[1]=='_Bool':
	    	vfact="['"+variable+"',0,['Bool']]"
	    elif values[1]=='array':
	    	vfact="['"+variable+"',0,['array']]"
            if vfacts=="":
                vfacts=vfact
            else:
                if vfact!="":
                    vfacts+=","+vfact
	
	equations=[]
        for x in a: 
        	equations.append(wff2fvact(x))
            
	for equation in equations:
		if equation is not None and '->' not in equation and '>' not in equation and '<' not in equation and '=' not in equation :
			loopvariables=extract_args(equation)
			equation=equation.strip()
			vfact=""
			if len(loopvariables)==0:	
				if equation not in variableMapOp.keys():
					if equation in variableMapIp.keys():
						values=variableMapIp[equation]
						if values[1]=='int':	
							vfact="['"+equation+"',0,['int']]"
						elif values[1]=='unsigned':	
							vfact="['"+equation+"',0,['int']]"
						elif values[1]=='float':
							vfact="['"+equation+"',0,['float']]"
						elif values[1]=='double':
							vfact="['"+equation+"',0,['double']]"
                                                elif values[1]=='_Bool':
							vfact="['"+equation+"',0,['Bool']]"
					else:
						vfact="['"+equation+"',0,['int']]"
				
			else:
				function_name=getFunctionName(str(equation),loopvariables )
				if function_name not in functionMap.keys() and isArrayFunction(function_name)==False:
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
		elif equation is not None and '->' in equation:
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
				function_name=getFunctionName(str(variables[1]),loopvariables )
				if isArrayFunction(function_name)==False:
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
#Function to Simplify and Expand an expression using sympy
"""
def simplify_expand_sympy(expression):
    if 'If' in str(expression) or '%' in str(expression):
    	return expression
    if 'Implies' not in expression and 'ite' not in expression and '==' not in  expression and '!=' not in  expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
    	return str(simplify_sympy(expression))
    elif 'Implies' in expression :
        axioms=extract_args(expression)
        #return 'Implies('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+')'
        return 'Implies('+axioms[0]+','+simplify_expand_sympy(axioms[1])+')'
    elif 'ite' in expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
        axioms=extract_args(expression)
        return 'If('+simplify_expand_sympy(axioms[0])+','+simplify_expand_sympy(axioms[1])+','+simplify_expand_sympy(axioms[2])+')'
    elif '==' in  expression and '!=' not in  expression and 'and' not in  expression and 'or' not in  expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
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
    elif '!=' in  expression and 'and' not in  expression and 'or' not in  expression and 'And' not in  expression and 'Or' not in  expression and 'Not' not in  expression and 'ForAll' and 'Exists' not in  expression and 'Implies' not in expression:
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
        #if '/' in str(expression) and '>' not in str(expression) and '<' not in str(expression) and '=' not in str(expression):
        if sympify(expression)==True or sympify(expression)==False:
		return expression        
        if '/' in str(expression):
        	expression,flag=expressionChecking(expression)
        	if flag==True:
        		expression_mod=expression 
        	else:
        		expression_mod=powsimp(expression)
        else:
            expression_mod=powsimp(expression)
            
	if '/' not in str(expression_mod):
		expression=expression_mod
	if '/' in str(expression):
		no,deno=fraction(together(expression))
		no=sympify(no).expand(basic=True)
		deno=sympify(deno).expand(basic=True)
		if deno==1:
			expression,flag=expressionChecking(expression)
			if flag==True:
				return expression
				#return pow_to_mul(powsimp(expression))
			else:
				return pow_to_mul(powsimp(expression))
			#return pow_to_mul(powsimp(no))
		else:
                 	return Mul(pow_to_mul(powsimp(no)), Pow(pow_to_mul(powsimp(deno)), -1), evaluate=False)
	
	else:
		#return str(sympify(expression).expand(basic=True))
		#print expression
                #print '############3'
		
		expressiontemp=sympify(expression).expand(basic=True)
		
		if '/' in str(expressiontemp):
			return pow_to_mul(powsimp(sympify(expression)))
		else:
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
		if lefthandstmt.find('_PROVE')>0:
			return None
		elif lefthandstmt.find('_ASSUME')>0:
        		return None
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
		if 'ite' in righthandstmt_base: 
			return None
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

#Solving Recurrences using wolframalpha

"""

def recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list):
    var=None
    query1="T(n+1)="+str(righthandstmt)
    var_map={}
    count=1
    #print query1
    if Mathematica_id is None:
    	return None
   
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
    #app_id="TQT2K7-5AK3PPJYVX"
    app_id=Mathematica_id
    try:
        client = wolframalpha.Client(app_id)
    	res = client.query(query)
    except ValueError:
    	return None
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
			temp=simplify(results[1])
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




"""
#Axiom Class
#Plain Python object to store Information about a Axiom
"""
class axiomclass(object):
 	def __init__(self, frame_axioms , output_equations , other_axioms, inputvariable, vfact, constraints, const_var_map, asserts, assumes):
        	self.frame_axioms = frame_axioms
        	self.output_equations = output_equations
        	self.other_axioms = other_axioms
        	self.inputvariable = inputvariable
        	self.vfact = vfact
        	self.constraints = constraints
        	self.const_var_map = const_var_map
        	self.asserts = asserts
        	self.assumes = assumes
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
        def getAsserts(self):
    	        return self.asserts
    	def getAssumes(self):
        	return self.assumes


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
 	def __init__(self, methodname, returnType , inputvar, localvar, body, usedCounter, serialNo):
        	self.methodname = methodname
        	self.inputvar = inputvar
        	self.returnType = returnType
        	self.localvar = localvar
        	self.body = body
        	self.usedCounter = usedCounter
        	self.serialNo = serialNo
        def getMethodname(self):
        	return self.methodname
        def getreturnType(self):
        	return self.returnType
        def getInputvar(self):
        	return self.inputvar
        def getLocalvar(self):
        	return self.localvar
        def getBody(self):
		return self.body
	def getUsedCounter(self):
		return self.usedCounter
	def getSerialNo(self):
		return self.serialNo
	def setInputvar(self, inputvar):
	        self.inputvar=inputvar
	def setLocalvar(self, localvar):
	        self.localvar=localvar
	def setBody(self, body):
		self.body=body
	def setUsedCounter(self, usedCounter):
		self.usedCounter=usedCounter
	def setSerialNo(self, serialNo):
		self.serialNo=serialNo
"""

#Variable Class 

#Plain Python Object to store information about variable

"""
class variableclass(object):
	def __init__(self, variablename, variableType, modifiers, dimensions, initialvalue):
        	self.variablename = variablename
        	self.variableType = variableType
        	self.modifiers = modifiers
        	self.dimensions = dimensions
        	self.initialvalue = initialvalue
	def getVariablename(self):
		return self.variablename
	def getVariableType(self):
		return self.variableType
	def getModifiers(self):
		return self.modifiers
	def getDimensions(self):
		return self.dimensions
	def getInitialvalue(self):
		return self.initialvalue


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
         	if expressions is not None:
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
                                else:
                                	stmt=createArrayList(expression.getExpression().lhs)
                                	#var="'gt"+str(stmt.count(','))+"',["+stmt+"]"
                                	var="'gt"+"',["+stmt+"]"
					if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend="]"
						else:
							programsstart+=",['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
							programsend+="]"
					else:
				                if programsstart=="":
				                        programsstart+="['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
				                else:
				                        programsstart+=",['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend

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
	if programsstart[0]==',':
		programsstart=programsstart[1:]	
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
                        else:
                                stmt=createArrayList(expression.getExpression().lhs)
			        #var="'gt"+str(stmt.count(','))+"',["+stmt+"]"
			        var="'gt"+"',["+stmt+"]"
				if expression.getIsPrime()==False:
					if programsstart=="":
						programsstart="['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend="]"
					else:
						programsstart+=",['-1','seq',['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"
						programsend+="]"
				else:
					if programsstart=="":
						programsstart+="['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
					else:
						programsstart+=",['-1','=',expres("+str(var)+"),"+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend

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
    	if '.length' in statement.value:
    		axm=statement.value.split('.')
    		expression+="expres('length',["+axm[0]+"])"
    	else:
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
    elif type(statement) is m.ArrayAccess:
    	stmt=createArrayList(statement)
    	#expression+="expres('at"+str(stmt.count(','))+"',["+stmt+"])"
    	expression+="expres('at"+"',["+stmt+"])"
    else:
    	if type(statement.lhs) is m.Name:
    		if '.length' in statement.lhs.value:
    		    	axm=statement.lhs.value.split('.')
    			expression+="expres('length',["+axm[0]+"])"
    		else:
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
    	elif type(statement.rhs) is m.ArrayAccess:
    		stmt=createArrayList(statement.rhs)
    		#expression+="expres('at"+str(stmt.count(','))+"',["+stmt+"])"
    		expression+="expres('at"+"',["+stmt+"])"
    	else:
        	if type(statement.rhs) is m.Additive:
        		expression+=","+expressionCreator(statement.rhs)+"])"
        	else :
        		expression+=","+expressionCreator(statement.rhs)+"])"
    return expression
    
"""

Construct Array List

"""
def createArrayList(statement):
	if type(statement) is m.ArrayAccess:
		stmt=''
		if type(statement) is m.ArrayAccess:
			stmt=createArrayList(statement.target)
		stmt+=",expres('"+statement.index.value+"')"
		return stmt
	else:
		return "expres('"+statement.value+"')"







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

Validation of Variables

"""

def validationOfInput(allvariable):
	for variable in allvariable.keys():
		if variable=='S' or variable=='Q' or variable=='N' or variable=='in' or variable=='is':
			return True
	return False


"""

Translate Program to Logic 

"""


#def translate(file_name):
#	if not(os.path.exists(file_name)): 
#		print "File not exits"
#		return
#	filename, file_extension = os.path.splitext(file_name)
#	if file_extension=='.java' or file_extension=='.Java' or file_extension=='.JAVA':
#		return translate_Java(file_name)
#	elif file_extension=='.c' or file_extension=='.C' :
#		return translate_C(file_name)
#	else:
#		return None
#	print file_extension

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

#file_name='cohendiv.java'

"""
  
def translate_Java(file_name):
	if not(os.path.exists(file_name)): 
		print "File not exits"
		return
	#if flag<1 and flag>3: 
	#	print "Invalid"
	#	return

	start_time=current_milli_time()
	p = getParser()
	#tree = p.parse_file("Utils7.java")
	tree = p.parse_file(file_name)
	#print tree
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
                                	variable=variableclass(param.variable.name, param.type,param.modifiers,param.variable.dimensions,None)
                                	parametermap[param.variable.name]=variable
                                        #parametermap[param.variable.name]=param.type         
                                else:
                                	#variable=variableclass(param.type.name.value, param.type,param.modifiers,param.variable.dimensions,None)
                                        variable=variableclass(param.variable.name, param.type.name,param.modifiers,param.variable.dimensions,None)
                                        parametermap[param.variable.name]=variable
                                        #parametermap[param.type.name.value]=param.type
                        if method_decl.body is not None:
                                for statement in method_decl.body:
                                # note that this misses variables in inner blocks such as for loops
                                # see symbols_visitor.py for a better way of handling this
                                        if type(statement) is m.VariableDeclaration:
                                                for var_decl in statement.variable_declarators:
                                                        if type(statement.type) is str:
                                                        	variable=variableclass(var_decl.variable.name, statement.type,None,var_decl.variable.dimensions,var_decl.initializer)
                                                                #type_name = statement.type
                                                        else:
                                                        	variable=variableclass(var_decl.variable.name, statement.type.name,None,statement.type.dimensions,var_decl.initializer)
                                                                #type_name = statement.type.name.value
                                                        #localvarmap[var_decl.variable.name]=type_name
                                                        localvarmap[var_decl.variable.name]=variable
                                        else:
                                        	statements.append(statement)
                        membermethod=membermethodclass(method_decl.name,returnType,parametermap,localvarmap)
                        menbermethods.append(membermethod)
                allvariable={}
                sort=sortclass(type_decl.name, menbermap)
                program_dec_start=""
                program_dec_end=""
                for lvap in localvarmap:
                	var=localvarmap[lvap]
                	if var is not None and var.getInitialvalue() is not None and type(var.getInitialvalue()) is not m.ArrayCreation:
                		if program_dec_start=="":
                			program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue().value)+"')]"
                			program_dec_end="]"
                		else:
                	        	program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue().value)+"')]"
                			program_dec_end+="]"

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
		                var_list="{"
		                for x in membermethod.getInputvar():
		                	if membermethod.getInputvar()[x].getDimensions()>0:
		                		var_list+=' '+x+':array'
		                	else:
		                		var_list+=' '+x+':'+membermethod.getInputvar()[x].getVariableType()
		                var_list+='}'
                                print var_list
		                print "Local Variables:"
		                var_list="{"
		                for x in membermethod.getLocalvar():
		                	if membermethod.getLocalvar()[x].getDimensions()>0:
						var_list+=' '+x+':array'
					else:
		                		var_list+=' '+x+':'+membermethod.getLocalvar()[x].getVariableType()
                                var_list+='}'
                                print var_list
                                for x in membermethod.getInputvar():
                                	allvariable[x]=membermethod.getInputvar()[x]
                                for x in membermethod.getLocalvar():
                                	allvariable[x]=membermethod.getLocalvar()[x]
                                	
          	if validationOfInput(allvariable)==True:
          		print "Please Rename variable Name {S,Q,N,in,is} to other Name"
          		return
                print "All Variables:"
                var_list="{"
             	for x in allvariable:
			if allvariable[x].getDimensions()>0:
				var_list+=' '+x+':array'
			else:
		        	var_list+=' '+x+':'+allvariable[x].getVariableType()
                var_list+='}'
                print var_list
                expressions=organizeStatementToObject(statements)
                primeStatement(expressions)
                variablesarray={}
                opvariablesarray={}
                count=0
                arrayFlag=False
                for variable in allvariable:
                	count+=1
                	if allvariable[variable].getDimensions()>0:
                		variablesarray[variable]=eval("['_y"+str(count)+"','array']")
                		opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','array']")
                		list_parameter="'array'"
                		for i in range(0, allvariable[variable].getDimensions()):
                			if list_parameter=='':
                				list_parameter="'int'"
                			else:
                				list_parameter+=",'int'"
                		list_parameter+=",'"+allvariable[variable].getVariableType()+"'"
                		#key1='at'+str(allvariable[variable].getDimensions())
                		#key2='gt'+str(allvariable[variable].getDimensions())
                		key1='at'
                		key2='gt'
                		arrayFlag=True
                		if key1 not in variablesarray.keys():
                			count+=1
                			variablesarray[key1]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                			opvariablesarray[key1+"1"]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                		if key2 not in variablesarray.keys():
                			count+=1
                			variablesarray[key2]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                			opvariablesarray[key2+"1"]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                	else:
                		variablesarray[variable]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
                		opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
                if arrayFlag==True:
                	count+=1
                	variablesarray['length']=eval("['_y"+str(count)+"','array','int']")
                	opvariablesarray['length1']=eval("['_y"+str(count)+"','array','int']")
                
                #print "#################1"
		#print variablesarray
		#print opvariablesarray
                #print "#################1"
                if program_dec_start=="":
                	str_program=programToinductiveDefination(expressions , allvariable)
                else:
                	str_program=program_dec_start+','+programToinductiveDefination(expressions , allvariable)+program_dec_end

                print str_program
                program=eval(str_program)
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
                #f,o,a,cm=translate1(program,variablesarray,2)
                vfacts,constraints=getVariFunDetails(f,o,a,allvariable,opvariablesarray)
                end_time=current_milli_time()
                print "Times to Translate"
                print end_time-start_time
                writeLogFile( "j2llogs.logs" , getTimeStamp()+"\n End of Translation\n")
                axiom=axiomclass(f,o,a,membermethod.getInputvar(), vfacts, constraints,cm)
                return axiom








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
	if ("<" in  expression or ">" in  expression) and '/' not in expression :
            expression=simplify(expression)
    	expression=transferToFunctionSyntax(str(expression))
    	xform = expr.transformString(expression)[1:-1]
    	xform=xform.replace('[','(')
    	expression=xform.replace(']',')')
   	#print expression
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

def isConstInResult( variable ):
	status=False
	find=regex.compile(r'C\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status

"""

Construction Parser

"""
p = plyj.parser.Parser()

def getParser():
	global p
	return p


def construct_expression(tree,postion,variable):
	expression=""
	if type(tree) is m.Assignment:
		expression="['i2',"+str(postion)+",'"+variable+"',"+expressionCreator(tree.lhs)+","+expressionCreator(tree.rhs)+"]"
	return eval(expression)
	
def construct_expression_normal(tree):
	if tree is not None:
		expression=""
		if type(tree) is m.Relational:
			expression="['s0',"+expressionCreator(tree)+"]"
		return eval(expression)
	else:
		return None




"""

#Simplify conclusion 

"""


def simplify_conclusion(conclusion,subs_list):
	if conclusion is not None and conclusion!='':
		term=isFunction(conclusion)
		if term is None:
			return None
		if 'ForAll' in conclusion and term=='ForAll':
			arg_list=extract_args(conclusion)
			result=simplify_conclusion(arg_list[1],subs_list)
			if result is not None:
				return 'ForAll('+arg_list[0]+','+result+')'
			else:
				return None
		elif 'Or' in conclusion and term=='Or':
			arg_list=extract_args(conclusion)
			result1=simplify_conclusion(arg_list[0],subs_list)
			result2=simplify_conclusion(arg_list[1],subs_list)
			if result1 is not None and result2 is not None:
				return 'Or('+result1+','+result2+')'
			else:
				return None
		elif 'And' in conclusion and term=='And':
			arg_list=extract_args(conclusion)
			result1=simplify_conclusion(arg_list[0],subs_list)
			result2=simplify_conclusion(arg_list[1],subs_list)
			if result1 is not None and result2 is not None:
				return 'And('+result1+','+result2+')'
			else:
				return None
		elif 'Exists' in conclusion and term=='Exists':
			arg_list=extract_args(conclusion)
			result=simplify_conclusion(arg_list[1],subs_list) 
			if result is not None:
				return 'Exists('+arg_list[0]+','+result+')'
			else:
				return None
		elif 'Not' in conclusion and term=='Not':
			arg_list=extract_args(conclusion)
			result=simplify_conclusion(arg_list[1],subs_list) 
			if result is not None:
				return 'Not('+result+')'
			else:
				return None
		elif 'Implies' in conclusion and term=='Implies':
			arg_list=extract_args(conclusion)
			result1=simplify_conclusion(arg_list[0],subs_list)
			result2=simplify_conclusion(arg_list[1],subs_list)
			if result1 is not None and result2 is not None:
				return 'Implies('+result1+','+result2+')'
			else:
				return None

		else:
			if '==' not in conclusion and '!=' not in conclusion:
				modified_conclusion=conclusion
				for element in subs_list.keys():
					modified_conclusion=str(modified_conclusion).replace(str(element),str(subs_list[element]))
				if '/' in modified_conclusion:
					conclusion=modified_conclusion
				else:
					conclusion=str(pow_to_mul(powsimp(simplify_sympy(conclusion).subs(subs_list))))
				return conclusion
			elif '!=' in conclusion:
				axm=conclusion.split('!=')
				left_side=None
				right_side=None
				conclusion=None
				if isinstance(simplify_sympy(axm[0]), (str, unicode)) or isinstance(simplify_sympy(axm[1]), (str, unicode)):
					left_side=str(simplify_sympy(axm[0]))
					for element in subs_list.keys():
						left_side=left_side.replace(str(element),str(subs_list[element]))
					right_side=str(simplify_sympy(axm[1]))
					for element in subs_list.keys():
						right_side=right_side.replace(str(element),str(subs_list[element]))
				else:
					left_side=str(simplify_sympy(axm[0]))
					for element in subs_list.keys():
						left_side=left_side.replace(str(element),str(subs_list[element]))
					right_side=str(simplify_sympy(axm[1]))
					for element in subs_list.keys():
						right_side=right_side.replace(str(element),str(subs_list[element]))
					#left_side=str(simplify_sympy(axm[0]).subs(subs_list))
					#right_side=str(simplify_sympy(axm[1]).subs(subs_list))
				if left_side is not None and right_side is not None:
					conclusion=left_side+'!='+right_side
				return conclusion
			
			else:
				axm=conclusion.split('==')
				left_side=None
				right_side=None
				conclusion=None
				leftin=None
				rightin=None
				leftin,rightin,axm[0]=parenthesesOrganizer( axm[0] ,leftin ,rightin)
				if leftin is not None and rightin is not None:
					axm[0]=leftin+axm[0]+rightin
				leftin=None
				rightin=None
				leftin,rightin,axm[1]=parenthesesOrganizer( axm[1] ,leftin ,rightin)
				if leftin is not None and rightin is not None:
					axm[1]=leftin+axm[1]+rightin
				if isinstance(simplify_sympy(axm[0]), (str, unicode)) or isinstance(simplify_sympy(axm[1]), (str, unicode)):
					left_side=str(simplify_sympy(axm[0]))
					for element in subs_list.keys():
						left_side=left_side.replace(str(element),str(subs_list[element]))
					right_side=str(simplify_sympy(axm[1]))
					for element in subs_list.keys():
						right_side=right_side.replace(str(element),str(subs_list[element]))
				else:
					left_side=str(simplify_sympy(axm[0]))
					for element in subs_list.keys():
						left_side=left_side.replace(str(element),str(subs_list[element]))
					right_side=str(simplify_sympy(axm[1]))
					for element in subs_list.keys():
						right_side=right_side.replace(str(element),str(subs_list[element]))
					#left_side=str(simplify_sympy(axm[0]).subs(subs_list))
					#right_side=str(simplify_sympy(axm[1]).subs(subs_list))
				if left_side is not None and right_side is not None:
					conclusion=left_side+'=='+right_side
				return conclusion




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
Prove command used to prove post condition of a program 

"""


def prove1(axiom,pre_condition,post_condition,flag):
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
			#tactic2(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
			end_time=current_milli_time()
			print "Times to Get Result"
                	print end_time-start_time
                writeLogFile( "j2llogs.logs" , getTimeStamp()+"\n End of Proof\n")


"""
Prove command used to prove post condition of a program 

"""


def prove(axiom,pre_condition,post_condition):
	if len(post_condition)==0:
		print "Nothing To Prove"
		return
	if axiom is not None and post_condition is not None:
		start_time=current_milli_time()
		writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Direct")
		status=tactic1(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints())
		if "Successfully Proved" in status:
			print "Successfully Proved"			
		elif "Counter Example" in status:
			print status		
		else:
			status=tactic2(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
		
			if "Successfully Proved" in status:
				print "Successfully Proved"			
			elif "Counter Example" in status:
				print status		
			else:
				print "Failed to Prove"
		end_time=current_milli_time()
		print end_time-start_time
	
	
# Test Case

#function_name='main'
#pre_condition=[]
#post_condition=['Z1 == 230']

#function_name='product'
#pre_condition=['a>=0','b>=0']
#post_condition=['RET1 == a*b']

#function_name='add'
#pre_condition=['a>=0','b>=0']
#post_condition=['RET1 == a+b']


def prove_auto_process(program):
	if program is None:
		print "Something is Wrong"
		return
	if program is not None:
		print '\n----Proving Process----\n'
		for name in program.getAxiomeMap():
			print
			print 'Function Name--'+name
			axiom=program.getAxiomeMap()[name]
			witnessXml=program.getWitnessXmlMap()[name]
			start_time=current_milli_time()
			#writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Direct")
			status=prove_assert_tactic1(axiom,witnessXml)
			if "Successfully Proved" in status:
				print "Successfully Proved"			
			elif "Counter Example" in status:
				print status
			elif "Nothing To Prove" in status:
				print 'No Assertion to Prove'
			else:
				#status=prove_assert_tactic2(axiom,witnessXml)
		
				if "Successfully Proved" in status:
					print "Successfully Proved"			
				elif "Counter Example" in status:
					print status		
				else:
					print "Failed to Prove"
		end_time=current_milli_time()
		print end_time-start_time
			





def prove_assert_tactic1(axiom,witnessXml):
	pre_condition=[]
	post_condition=[]
	for w in axiom.getAsserts():
		if w[0]=='i1':
			var_cstr_map={}
			rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
			list_var_str=qualifier_list(var_cstr_map.keys())
			list_cstr_str=cstr_list(var_cstr_map.values())
			if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
				rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
			if list_var_str is not None and list_cstr_str is not None:
				if w[0] == 'i1':
					post_condition.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))")
				else:
					post_condition.append('ForAll(['+list_var_str+'],'+rhs+")")
			else:
                		post_condition.append(rhs)
		else:
			if w[0]!='i0':
				var_cstr_map={}
				rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
				list_var_str=qualifier_list(var_cstr_map.keys())
				list_cstr_str=cstr_list(var_cstr_map.values())
				if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
					rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
				if list_var_str is not None and list_cstr_str is not None:
					if w[0] == 'i1':
						post_condition.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))")
					else:
						post_condition.append('ForAll(['+list_var_str+'],'+rhs+")")
				else:
                			post_condition.append(rhs)
			
	for w in axiom.getAssumes():
		if w[0]=='i1':
			var_cstr_map={}
			rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
			list_var_str=qualifier_list(var_cstr_map.keys())
			list_cstr_str=cstr_list(var_cstr_map.values())
			if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in lhs:
				rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
			if list_var_str is not None and list_cstr_str is not None:
				if w[0] == 'i1':
					pre_condition.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))")
				else:
					pre_condition.append('ForAll(['+list_var_str+'],'+rhs+")")
			else:
                		pre_condition.append(rhs)
		else:
			if w[0]!='i0':
				var_cstr_map={}
				rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
				list_var_str=qualifier_list(var_cstr_map.keys())
				list_cstr_str=cstr_list(var_cstr_map.values())
				if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
					rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
				if list_var_str is not None and list_cstr_str is not None:
					if w[0] == 'i1':
						pre_condition.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))")
					else:
					        pre_condition.append('ForAll(['+list_var_str+'],'+rhs+")")
				else:
                			pre_condition.append(rhs)
			
			
	for x in post_condition:
		print('\nAssertion To Prove:'+x)
		temp_post_condition=[]
		temp_post_condition.append(x)
		if post_condition is not None:
			start_time=current_milli_time()
			writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(x)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Direct")
			status=tactic1_update(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,temp_post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),witnessXml)
			#status=tactic2_update(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,temp_post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
			if "Successfully Proved" in status:
				return "Successfully Proved"			
			elif "Counter Example" in status:
				return status
			else:
				return "Failed to Prove"
	return "Nothing To Prove"



def prove_assert_tactic2(axiom,witnessXml):
	pre_condition=[]
	post_condition={}
	
	
	for w in axiom.getAssumes():
		if w[0]=='i1':
			var_cstr_map={}
			rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
			list_var_str=qualifier_list(var_cstr_map.keys())
			list_cstr_str=cstr_list(var_cstr_map.values())
			if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in lhs:
				rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
			if list_var_str is not None and list_cstr_str is not None:
				if w[0] == 'i1':
					pre_condition.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))")
				else:
					pre_condition.append('ForAll(['+list_var_str+'],'+rhs+")")
			else:
	                	pre_condition.append(rhs)
		else:
			if w[0]!='i0':
				var_cstr_map={}
				rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
				list_var_str=qualifier_list(var_cstr_map.keys())
				list_cstr_str=cstr_list(var_cstr_map.values())
				if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
					rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
				if list_var_str is not None and list_cstr_str is not None:
					if w[0] == 'i1':
						pre_condition.append("ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))")
					else:
						pre_condition.append('ForAll(['+list_var_str+'],'+rhs+")")
				else:
                			pre_condition.append(rhs)
	
	
	
	
	
	for w in axiom.getAsserts():
		if w[0]=='i1':
			var_cstr_map={}
			rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
			list_var_str=qualifier_list(var_cstr_map.keys())
			list_cstr_str=cstr_list(var_cstr_map.values())
			if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
				rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
			if list_var_str is not None and list_cstr_str is not None:
				if w[0] == 'i1':
					post_condition["ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))"]=w
				else:
					post_condition['ForAll(['+list_var_str+'],'+rhs+")"]=w
			else:
                		post_condition[rhs]=w
		else:
			if w[0]!='i0':
				var_cstr_map={}
				rhs=expr2z3_update_postCond(w[-1],var_cstr_map)
				list_var_str=qualifier_list(var_cstr_map.keys())
				list_cstr_str=cstr_list(var_cstr_map.values())
				if 'Or' not in rhs and 'And' not in rhs and 'If' not in rhs and '/' not in rhs:
					rhs=convert_pow_op_fun(simplify_expand_sympy(rhs))
				if list_var_str is not None and list_cstr_str is not None:
					if w[0] == 'i1':
						post_condition["ForAll(["+list_var_str+"],Implies("+list_cstr_str+","+rhs+"))"]=w
					else:
						post_condition['ForAll(['+list_var_str+'],'+rhs+")"]=w
				else:
                			post_condition[rhs]=w

	

	for conclusion in post_condition.keys():
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		if conclusion is None:
			return "Failed to Prove"
		variable=None
		constant=None
		const_map={}
		var_const_map={}
		count=0
		
		for cm in axiom.getConst_var_map():
			if axiom.getConst_var_map()[cm] in conclusion:
				count=count+1
				const_map[axiom.getConst_var_map()[cm]]=cm
				var_const_map[cm]="_k"+str(count)
		constraint_list=[]
		condition_map={}
		frame_axioms=eqset2constraintlist_update(axiom.getFrame_axioms())
		for x in frame_axioms:
			constraint_list.append(x)
		out_axioms=eqset2constraintlist_update(axiom.getOutput_equations())
				
		for x in out_axioms:
			constraint_list.append(x)
		for x in axiom.getOther_axioms(): 
			equations=wff2z3_update(x)
		        getAllCondtion(x,condition_map)
		        equations_sp=None	
		        constraint_list.append(equations)
		        if x[0]=='s1':
		        	equations_sp=wff2z3SC_update(x)
		        if equations_sp is not None:
		        	constraint_list.append(equations_sp)
		for x in axiom.getConstraints():
			constraint_list.append(x)
		for x in pre_condition:
		        constraint_list.append(x)
		update_vfact=[]
		for [x,k,l] in axiom.getVfact():
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
			w=post_condition[conclusion]
			e_in_step=w[1]
			e_base=w[1]
			e_assume=w[1]
			
			t=[]
			t.append('+')
			t1=[]
			t2=[]
			t1.append(loop_var)
			t2.append('1')
			t.append(t1)
			t.append(t2)
			t3=[]
			t3.append(x)
			e_in_step=expr_replace(e_in_step,t3,t)
			invariantstmtdisplay=expr2z3_update_postCond(e_in_step,{})
			for x in axiom.getOther_axioms():
				if x[0]=='i1':
					e_in_step=expr_replace(e_in_step,x[3],x[4])
				else:
					if x[0]=='i0':
						e_in_step=expr_replace(e_in_step,x[2],x[3])
			t1=[]
			t2=[]
			t1.append(loop_var)
			t2.append(variable)
			e_in_step=expr_replace(e_in_step,t1,t2)
			e_assume=expr_replace(e_assume,t3,t2)
			t1=[]
			t1.append('0')
			e_base=expr_replace(e_base,t3,t1)
			w1=[]
			w1.append('s0')
			w1.append(e_base)
			w2=[]
			w2.append('s0')
			w2.append(e_assume)
			w3=[]
			w3.append('s0')
			w3.append(e_in_step)
			basecasestmt=wff2z3_update_postCond(w1)
			#invariantstmt=wff2z3_update_postCond(w2)
			inductiveassum=wff2z3_update_postCond(w2)
			print " Try to prove following using induction on "+loop_var
			print "ForAll("+loop_var+","+str(invariantstmtdisplay)+")"
			print "Base Case"
			writeLogFile( "j2llogs.logs" , "\nBase Case \n"+str(basecasestmt)+"\n" )
			status=query2z3(constraint_list,str(basecasestmt),update_vfact,axiom.getInputvariable(),witnessXml)
			writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
			if "Successfully Proved" in status:
				case_list=[]
				case_temp_inductivestep=None
				if len(condition_map)==1:
					for key in condition_map.keys():
						case_list.append(key.replace(loop_var,variable))
						case_list.append('Not('+key.replace(loop_var,variable)+')')
				print "Successfully Proved"
				print "Inductive Step"
				print "Inductive Assumption"
				#print invariantstmt
				print inductiveassum
				updated_equation=[]
				updated_vfact=[]
				for equation in constraint_list:
					updated_equation.append(equation)
				updated_equation.append(variable+">=0")
				inductivestep='Implies('+str(inductiveassum)+','+wff2z3_update_postCond(w3)+')'
				writeLogFile( "j2llogs.logs" ,"\nInductive Step \n"+str(inductivestep)+"\n" )
				status=query2z3(updated_equation,str(inductivestep),update_vfact,axiom.getInputvariable(),witnessXml)
				writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
				if "Successfully Proved" in status:
					#print "Successfully Proved"
					return "Successfully Proved"
				elif "Counter Example" in status:
					return status
				else:
					if len(case_list)>0:
						case_status=False
						for case in case_list:
							inductivestep='Implies(And('+str(inductiveassum)+','+case+'),'+inductivestep+')'
							#status=query2z3(updated_equation,str(inductivestep),update_vfact,axiom.getInputvariable(),witnessXml)
							status="Failed to Prove"
							if "Successfully Proved" in status:
								case_status=True
							else:
								case_status=False
								break
										
									
						if case_status==True:
				                	writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
							return "Successfully Proved"
						else:
							return "Failed to Prove"
					else:
						return "Failed to Prove"
			elif "Counter Example" in status:
				return status
			else:
				return "Failed to Prove"
	return "Nothing To Prove"






		
def prove_Ext(program,function_name,pre_condition,post_condition):
	if len(post_condition)==0:
		print "Nothing To Prove"
		return
		
	axiomeMap=program.getAxiomeMap()
	
	if axiomeMap is None:
		print "Something Wrong in Translation"
		return
	
	axiom=axiomeMap[function_name]
	
	if axiomeMap is None:
		print "Something Wrong in Translation"
		return	
	
	if axiom is not None and post_condition is not None:
		start_time=current_milli_time()
		writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Prove \n"+"\nParameters--\n"+"\n Pre Condition--"+str(pre_condition)+"\n Post Condition--"+str(post_condition)+"\n Strategy--Direct")
		status=tactic1(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints())
		
		if "Successfully Proved" in status:
			print "Successfully Proved"			
		elif "Counter Example" in status:
			print status		
		else:
			status=tactic2(axiom.getFrame_axioms(),axiom.getOutput_equations(),axiom.getOther_axioms(),pre_condition,post_condition,axiom.getVfact(),axiom.getInputvariable(),axiom.getConstraints(),axiom.getConst_var_map())
		
			if "Successfully Proved" in status:
				print "Successfully Proved"			
			elif "Counter Example" in status:
				print status		
			else:
				print "Failed to Prove"
		end_time=current_milli_time()
		print end_time-start_time


"""

1.Directly translate axoimes to z3 constraint 2.Change  exponential operator ** to power function

"""
def query2z3(constraint_list,conclusion,vfact,inputmap,witnessXml):
	pythonProgram="from z3 import *\n"
	pythonProgram+="set_param(proof=True)\n"
	pythonProgram+="_p1=Int('_p1')\n"
	pythonProgram+="_p2=Int('_p2')\n"
	pythonProgram+="_n=Int('_n')\n"
	pythonProgram+="arraySort = DeclareSort('arraySort')\n"
	pythonProgram+="_f=Function('_f',IntSort(),IntSort())\n"

	status=""
	for [x,k,l] in vfact:
		if k==0:
			if '_PROVE' not in x or '_ASSUME' not in x:
				if l[0]=="int":
					if '_N' in x:
						pythonProgram+=x+"=Const(\'"+x+"\',IntSort())\n"
					else:				
						pythonProgram+=x+"=Int(\'"+x+"\')\n"
				elif l[0]=="double":
					pythonProgram+=x+"=Real(\'"+x+"\')\n"
				elif l[0]=="float":
					pythonProgram+=x+"=Real(\'"+x+"\')\n"
                        	elif l[0]=="Bool":
					pythonProgram+=x+"=Bool(\'"+x+"\')\n"
				elif l[0]=="constant":
					pythonProgram+=x+"=Const(\'"+x+"\',IntSort())\n"
				elif l[0]=="array":
					pythonProgram+=x+"=Const(\'"+x+"\',arraySort)\n"
				else:
					pythonProgram+=x+"=Bool(\'"+x+"\')\n"
		else:
			if '_PROVE' not in x or '_ASSUME' not in x:
				pythonProgram+=x+"=Function(\'"+x+"\'"
				for e in l:
					if e=="int":
						pythonProgram+=",IntSort()"
					elif e=="array":
						pythonProgram+=",arraySort"
					else:
						pythonProgram+=",RealSort()"
			pythonProgram+=")\n"
	power_flag=False
	for equation in constraint_list:
		if '**' in equation or 'power' in equation:
			power_flag=True
	if '**' in conclusion or 'power' in conclusion:
		power_flag=True
	if power_flag==True:		
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
        else:
        	pythonProgram+="_s=Solver()\n"

	pythonProgram+="_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))\n"
	pythonProgram+="_s.set(\"timeout\","+str(TIMEOUT)+")\n"
	for equation in constraint_list:
		pythonProgram+="_s.add("+str(equation)+")\n"
	finalProgram=pythonProgram
	#finalProgram+="_s.add(Not("+str(transferToFunctionRec(conclusion))+"))\n"
	finalProgram+="_s.add(Not("+str(conclusion)+"))\n"
	finalProgram+="if sat==_s.check():\n"+"\tprint \"Counter Example\"\n"+"\tprint _s.model()\n"+"\twitnessXmlStr="+str(witnessXml)+"\n"+"\tmiddle=''\n"+"\tfor element in _s.model():\n"+"\t\tif str(element)==witnessXmlStr[2]:\n"+"\t\t\tmiddle+='<data key=\"assumption\">'+'\\\\'+'result=='+str(_s.model()[element])+'</data>'\n"+"\tfile = open(witnessXmlStr[3]+'_witness.graphml', 'w')\n"+"\tfile.write(witnessXmlStr[0]+middle+witnessXmlStr[1])\n"+"\tfile.close()\n"+"elif unsat==_s.check():\n"+"\t_s.check()\n"+"\tif os.path.isfile(\'j2llogs.logs\'):\n"+"\t\tfile = open(\'j2llogs.logs\', \'a\')\n"+"\t\tfile.write(\"\\n**************\\nProof Details\\n**************\\n\"+str(_s.proof().children())+\"\\n\")\n"+"\t\tfile.close()\n"+"\telse:\n"+"\t\tfile = open(\'j2llogs.logs\', \'w\')\n"+"\t\tfile.write(\"\\n**************\\nProof Details\\n**************\\n\"+str(_s.proof().children())+\"\\n\")\n"+"\t\tfile.close()\n"+"\tprint \"Successfully Proved\"\n"+"else:\n"+"\tprint \"Failed To Prove\""
	#finalProgram+="if sat==_s.check():\n"+"\tprint \"Counter Example\"\n"+"\tprint _s.model()\n"+"\twitnessXmlStr="+str(witnessXml)+"\n"+"\tmiddle=''\n"+"\tfor element in _s.model():\n"+"\t\tif str(element)!=witnessXmlStr[2]:\n"+"\t\t\tmiddle+='<data key=\"assumption\">'+str(element)[:-1]+'=='+str(_s.model()[element])+'</data>'\n"+"\t\telse:\n"+"\t\t\tmiddle+='<data key=\"assumption\">'+'\\\\'+'result=='+str(_s.model()[element])+'</data>'\n"+"\tfile = open(witnessXmlStr[3]+'_witness.graphml', 'w')\n"+"\tfile.write(witnessXmlStr[0]+middle+witnessXmlStr[1])\n"+"\tfile.close()\n"+"elif unsat==_s.check():\n"+"\t_s.check()\n"+"\tif os.path.isfile(\'j2llogs.logs\'):\n"+"\t\tfile = open(\'j2llogs.logs\', \'a\')\n"+"\t\tfile.write(\"\\n**************\\nProof Details\\n**************\\n\"+str(_s.proof().children())+\"\\n\")\n"+"\t\tfile.close()\n"+"\telse:\n"+"\t\tfile = open(\'j2llogs.logs\', \'w\')\n"+"\t\tfile.write(\"\\n**************\\nProof Details\\n**************\\n\"+str(_s.proof().children())+\"\\n\")\n"+"\t\tfile.close()\n"+"\tprint \"Successfully Proved\"\n"+"else:\n"+"\tprint \"Failed To Prove\""
	#finalProgram+="if sat==_s.check():\n"+"\tprint \"Counter Example\"\n"+"\tprint _s.model()\n"+"elif unsat==_s.check():\n"+"\t_s.check()\n"+"\tprint \"Successfully Proved\"\n"+"else:\n"+"\tprint \"Failed To Prove\""
	#print finalProgram
	writtingFile( "z3query.py" , finalProgram )
	writeLogFile( "j2llogs.logs" , "\nQuery to z3 \n"+str(finalProgram)+"\n" )
	try :
		proc = subprocess.Popen('python z3query.py', stdout=subprocess.PIPE,shell=True)
		output = proc.stdout.read()
		status=output
	except OSError  as err:
		print 'dharilo1'
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
        	#equations=wff2z3(x)
        	equations=wff2z3_update(x)
        	
        	equations_sp=None
                constraint_list.append(equations)
                if x[0]=='s1':
        		equations_sp=wff2z3SC(x)
        		if equations_sp is not None:
        			constraint_list.append(equations_sp)        		
	for x in constaints:
		constraint_list.append(x)
	for x in pre_condition:
        	constraint_list.append(x)
        	       
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		if conclusion is None:
			return "Failed to Prove"
		if "factorial" in conclusion:
			cfact=eval("['factorial',1,['int','int']]")
			vfact.append(cfact)
		status=query2z3(constraint_list,conclusion,vfact,inputmap)
		writeLogFile( "j2llogs.logs" ,"\nResult \n"+str(status)+"\n" )
		if "Successfully Proved" in status:
			return "Successfully Proved"			
		elif "Counter Example" in status:
			return 	status		
		else:
			return "Failed to Prove"


def tactic1_update(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints,witnessXml):
	global defineDetaillist
	defineDetaillist=[]
	constraint_list=[]
	frame_axioms=eqset2constraintlist_update(f)
	for x in frame_axioms:
		constraint_list.append(x)
	out_axioms=eqset2constraintlist_update(o)
	subs_list=eqset2subs_list(o)
	
	
	for x in out_axioms:
		constraint_list.append(x)
	for x in a: 
        	equations=wff2z3_update(x)
        	
        	equations_sp=None
                constraint_list.append(equations)
                if x[0]=='s1':
        		equations_sp=wff2z3SC_update(x)
        		if equations_sp is not None:
        			constraint_list.append(equations_sp)        		
	for x in constaints:
		constraint_list.append(x)
	for x in pre_condition:
        	constraint_list.append(x)
        filter_map={}
        for element in defineDetaillist:
        	if element[0] not in filter_map.keys():
        		filter_map[element[0]]=element[0]
        		vfact.append(element)
	defineDetaillist=[]
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		if conclusion is None:
			return "Failed to Prove"
		if "factorial" in conclusion:
			cfact=eval("['factorial',1,['int','int']]")
			vfact.append(cfact)
		status=query2z3(constraint_list,conclusion,vfact,inputmap,witnessXml)
		writeLogFile( "j2llogs.logs" ,"\nResult \n"+str(status)+"\n" )
		if "Successfully Proved" in status:
			return "Successfully Proved"			
		elif "Counter Example" in status:
			return 	status		
		else:
			return "Failed to Prove"













"""

Tactic 2  ----> 1.Directly translate axoimes to z3 constraint 2.try to prove using induction on loop variable 

"""
def tactic2(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints,const_var_map,witnessXml):
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		subs_list=eqset2subs_list(o)
		conclusion=simplify_conclusion(conclusion,subs_list)
		if conclusion is None:
			return "Failed to Prove"
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
		condition_map={}
		frame_axioms=eqset2constraintlist(f)
		for x in frame_axioms:
			constraint_list.append(x)
		out_axioms=eqset2constraintlist(o)
		
		for x in out_axioms:
			constraint_list.append(x)
		for x in a: 
        		equations=wff2z3(x)
        		getAllCondtion(x,condition_map)
        		equations_sp=None	
                	constraint_list.append(equations)
                	if x[0]=='s1':
        			equations_sp=wff2z3SC(x)
        			if equations_sp is not None:
        				constraint_list.append(equations_sp)
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

		if 'ForAll(' in conclusion or 'Exits' in conclusion:
			return "Failed to Prove"
		
		for x in const_map:
			variable=var_const_map[const_map[x]]			
			constant=x
			loop_var=const_map[x]
			if 'Not(' in conclusion:
				arg_list=extract_args(conclusion)
				conclusion=arg_list[0]
				#conclusion=conclusion.replace('==','!=')

			
			if '==' in str(conclusion) and '<' not in  str(conclusion) and '>' not in str(conclusion) and '!' not in str(conclusion) and 'ite' not in str(conclusion) and 'And(' not in str(conclusion) and 'Or(' not in str(conclusion):
				exp=str(conclusion).split('==')
				invariantstmtdisplay_left=None
				invariantstmtdisplay_right=None
				if '/' in str(exp[0]):
					invariantstmtdisplay_left=exp[0].replace(constant,const_map[x])
					exp[0]=exp[0].replace(constant,variable)
				else:
					invariantstmtdisplay_left=str(simplify(exp[0]).subs(constant,const_map[x]))
					exp[0]=simplify(exp[0]).subs(constant,variable)
				if '/' in str(exp[1]):
					invariantstmtdisplay_right=exp[1].replace(constant,const_map[x])
					exp[1]=exp[1].replace(constant,variable)
				else:
					invariantstmtdisplay_right=str(simplify(exp[1]).subs(constant,const_map[x]))
					exp[1]=simplify(exp[1]).subs(constant,variable)
				
			
				invariantstmtdisplay=invariantstmtdisplay_left+"=="+invariantstmtdisplay_right				
				invariantstmt=str(exp[0])+"=="+str(exp[1])
				if '/' in str(exp[0]):
					exp[0]=exp[0].replace(variable,'0')
				else:
					exp[0]=simplify(exp[0]).subs(variable,0)
					
				if '/' in str(exp[1]):
					exp[1]=exp[1].replace(variable,'0')
				else:
					exp[1]=simplify(exp[1]).subs(variable,0)
					
				basecasestmt=str(exp[0])+"=="+str(exp[1])
			elif '!=' in str(conclusion) and '<' not in  str(conclusion) and '>' not in str(conclusion) and 'ite' not in str(conclusion) and 'And(' not in str(conclusion) and 'Or(' not in str(conclusion):
				exp=str(conclusion).split('!=')
				invariantstmtdisplay_left=None
				invariantstmtdisplay_right=None
				if '/' in str(exp[0]):
					invariantstmtdisplay_left=exp[0].replace(constant,const_map[x])
					exp[0]=exp[0].replace(constant,variable)
				else:
					invariantstmtdisplay_left=str(simplify(exp[0]).subs(constant,const_map[x]))
					exp[0]=simplify(exp[0]).subs(constant,variable)
				if '/' in str(exp[1]):
					invariantstmtdisplay_right=exp[1].replace(constant,const_map[x])
					exp[1]=exp[1].replace(constant,variable)
				else:
					invariantstmtdisplay_right=str(simplify(exp[1]).subs(constant,const_map[x]))
					exp[1]=simplify(exp[1]).subs(constant,variable)
							
				invariantstmtdisplay=invariantstmtdisplay_left+"!="+invariantstmtdisplay_right			
				invariantstmt=str(exp[0])+"!="+str(exp[1])
				if '/' in str(exp[0]):
					exp[0]=exp[0].replace(variable,'0')
				else:
					exp[0]=simplify(exp[0]).subs(variable,0)
				if '/' in str(exp[1]):
					exp[1]=exp[1].replace(variable,'0')
				else:
					exp[1]=simplify(exp[1]).subs(variable,0)
								
				basecasestmt=str(exp[0])+"!="+str(exp[1])
			elif 'And(' in str(conclusion) or 'Or(' in str(conclusion):
				sub_list={}
				sub_list[constant]=variable
				invariantstmt=simplify_conclusion(conclusion,sub_list)
				sub_list={}
				sub_list[constant]=const_map[x]	
				invariantstmt=simplify_conclusion(invariantstmt,sub_list)
				invariantstmtdisplay=simplify_conclusion(conclusion,sub_list)
				sub_list={}
				sub_list[variable]='0'
				basecasestmt=simplify_conclusion(conclusion,sub_list)
			
			else:
				
				if '/' in str(conclusion):
					invariantstmt=conclusion.replace(constant,variable)
					invariantstmtdisplay=conclusion.replace(constant,const_map[x])
					basecasestmt=invariantstmt.replace(variable,'0')
				else:
					invariantstmt=simplify(conclusion).subs(constant,variable)
					invariantstmtdisplay=simplify(conclusion).subs(constant,const_map[x])
					basecasestmt=simplify(invariantstmt).subs(variable,0)
					
			print " Try to prove following using induction on "+const_map[x]
			print "ForAll("+const_map[x]+","+str(invariantstmtdisplay)+")"
			print "Base Case"
			if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt) and 'And(' not in str(invariantstmt) and 'Or(' not in str(invariantstmt):
				exp=str(invariantstmt).split('==')
				if '/' in str(exp[0]):
					exp[0]=exp[0].replace(variable,'0')
				else:
					exp[0]=simplify(exp[0]).subs(variable,0)
					
				if '/' in str(exp[1]):
					exp[1]=exp[1].replace(variable,'0')
				else:
					exp[1]=simplify(exp[1]).subs(variable,0)
				basecasestmt=str(exp[0])+"=="+str(exp[1])
			
			elif '!=' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and 'ite' not in str(invariantstmt) and 'And(' not in str(invariantstmt) and 'Or(' not in str(invariantstmt):
				exp=str(invariantstmt).split('!=')
				if '/' in str(exp[0]):
					exp[0]=exp[0].replace(variable,'0')
				else:
					exp[0]=simplify(exp[0]).subs(variable,0)
								
				if '/' in str(exp[1]):
					exp[1]=exp[1].replace(variable,'0')
				else:
					exp[1]=simplify(exp[1]).subs(variable,0)
				basecasestmt=str(exp[0])+"!="+str(exp[1])
			elif 'And(' in str(invariantstmt) or 'Or(' in str(invariantstmt):
				sub_list={}
				sub_list[variable]='0'
				basecasestmt=simplify_conclusion(invariantstmt,sub_list)			
			else:
				if '/' in str(basecasestmt):
					basecasestmt=invariantstmt.replace(variable,'0')
				else:
					basecasestmt=simplify(invariantstmt).subs(variable,0)
			print basecasestmt
			writeLogFile( "j2llogs.logs" , "\nBase Case \n"+str(basecasestmt)+"\n" )
			status=query2z3(constraint_list,str(basecasestmt),update_vfact,inputmap)
			#status=query2z3(constraint_list,str(basecasestmt),vfact,inputmap)
			writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
			if "Successfully Proved" in status:
				case_list=[]
				case_temp_inductivestep=None
				if len(condition_map)==1:
					for key in condition_map.keys():
						case_list.append(key.replace(loop_var,variable))
						case_list.append('Not('+key.replace(loop_var,variable)+')')
				print "Successfully Proved"
				print "Inductive Step"
				print "Inductive Assumption"
				print invariantstmt
				updated_equation=[]
				updated_vfact=[]
				if '==' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt) and '!' not in str(invariantstmt) and 'ite' not in str(invariantstmt) and 'And(' not in str(invariantstmt) and 'Or(' not in str(invariantstmt):
					exp=str(invariantstmt).split('==')
					
					lexp=None
					rexp=None
					if '/' not in str(exp[0]):
						lexp=simplify(exp[0])
					else:
						lexp=exp[0]
					if '/' not in str(exp[1]):
						rexp=simplify(exp[1])
					else:
						rexp=exp[1]
					inductiveassum=str(lexp)+"=="+str(rexp)
					
					
					if '/' not in str(exp[0]):
						lexp=simplify(exp[0]).subs(variable,variable+"+1")
					else:
						lexp=exp[0].replace(variable,variable+"+1")
						
					if '/' not in str(exp[1]):
						rexp=simplify(exp[1]).subs(variable,variable+"+1")
					else:
						rexp=exp[1].replace(variable,variable+"+1")				
					
					ind_def_map=eqset2subs_list_ind(a)
					for i_e in ind_def_map:
                                            lexp=sub_ind_def(str(lexp),sub_ind_def(str(i_e),loop_var,variable),'('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')')
                                            rexp=sub_ind_def(str(rexp),sub_ind_def(str(i_e),loop_var,variable),'('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')')
					case_temp_inductivestep=str(lexp)+"=="+str(rexp)
					inductivestep='Implies('+str(inductiveassum)+','+str(lexp)+"=="+str(rexp)+')'
				
				elif '!=' in str(invariantstmt) and '<' not in  str(invariantstmt) and '>' not in str(invariantstmt)  and 'ite' not in str(invariantstmt) and 'And(' not in str(invariantstmt) and 'Or(' not in str(invariantstmt):
					exp=str(invariantstmt).split('==')
					
					lexp=None
					rexp=None
					if '/' not in str(exp[0]):
						lexp=simplify(exp[0])
					else:
						lexp=exp[0]
					if '/' not in str(exp[1]):
						rexp=simplify(exp[1])
					else:
						rexp=exp[1]
					inductiveassum=str(lexp)+"!="+str(rexp)
					
					
					if '/' not in str(exp[0]):
						lexp=simplify(exp[0]).subs(variable,variable+"+1")
					else:
						lexp=exp[0].replace(variable,variable+"+1")
						
					if '/' not in str(exp[1]):
						rexp=simplify(exp[1]).subs(variable,variable+"+1")
					else:
						rexp=exp[1].replace(variable,variable+"+1")				
					
					ind_def_map=eqset2subs_list_ind(a)
					for i_e in ind_def_map:
                                            lexp=sub_ind_def(str(lexp),sub_ind_def(str(i_e),loop_var,variable),'('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')')
                                            rexp=sub_ind_def(str(rexp),sub_ind_def(str(i_e),loop_var,variable),'('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')')
					case_temp_inductivestep=str(lexp)+"!="+str(rexp)
					inductivestep='Implies('+str(inductiveassum)+','+str(lexp)+"=="+str(rexp)+')'
				
				elif 'And(' in str(invariantstmt) or 'Or(' in str(invariantstmt):					
					inductiveassum=invariantstmt
					sub_list={}
					for i_e in ind_def_map:
						sub_list[sub_ind_def(str(i_e),loop_var,variable)]='('+sub_ind_def(str(ind_def_map[i_e]),loop_var,variable)+')'
					inductivestep=simplify_conclusion(invariantstmt,sub_list)
				
				else:
					if '/' in str(invariantstmt):
						inductiveassum=simplify_sympy(invariantstmt)
						inductivestep=simplify_sympy(invariantstmt).replace(variable,variable+"+1")
						ind_def_map=eqset2subs_list_ind(a)
						temp_inductivestep=str(inductivestep)
						for i_e in ind_def_map:
							temp_inductivestep=sub_ind_def(temp_inductivestep,sub_ind_def(str(i_e),loop_var,variable),sub_ind_def(str(ind_def_map[i_e]),loop_var,variable))
						case_temp_inductivestep=temp_inductivestep
						inductivestep='Implies('+str(inductiveassum)+','+temp_inductivestep+')'
					else:
						inductiveassum=simplify(invariantstmt)
						inductivestep=simplify(invariantstmt).subs(variable,variable+"+1")
						ind_def_map=eqset2subs_list_ind(a)
						temp_inductivestep=str(inductivestep)
						for i_e in ind_def_map:
							temp_inductivestep=sub_ind_def(temp_inductivestep,sub_ind_def(str(i_e),loop_var,variable),sub_ind_def(str(ind_def_map[i_e]),loop_var,variable))
						case_temp_inductivestep=temp_inductivestep
						inductivestep='Implies('+str(inductiveassum)+','+temp_inductivestep+')'

					
					
				for equation in constraint_list:
					updated_equation.append(equation)
				updated_equation.append(variable+">=0")
				#updated_equation.append(inductiveassum)
				writeLogFile( "j2llogs.logs" ,"\nInductive Step \n"+str(inductivestep)+"\n" )
				status=query2z3(updated_equation,str(inductivestep),update_vfact,inputmap)
				###status=query2z3(updated_equation,str(inductivestep),vfact,inputmap)
				writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
				if "Successfully Proved" in status:
					#print "Successfully Proved"
					return "Successfully Proved"
				elif "Counter Example" in status:
					return status
				else:
					if len(case_list)>0:
						case_status=False
						for case in case_list:

							inductivestep='Implies(And('+str(inductiveassum)+','+case+'),'+case_temp_inductivestep+')'
							status=query2z3(updated_equation,str(inductivestep),update_vfact,inputmap)
							if "Successfully Proved" in status:
								case_status=True
							else:
								case_status=False
								break
						
					
						if case_status==True:
                                                        writeLogFile( "j2llogs.logs" , "\nResult \n"+str(status)+"\n" )
							return "Successfully Proved"
						else:

							return "Failed to Prove"
					else:
						return "Failed to Prove"
			elif "Counter Example" in status:
				return status
			else:
				return "Failed to Prove"
		return "Failed to Prove"



def tactic2_update(f,o,a,pre_condition,conclusions,vfact,inputmap,constaints,const_var_map,witnessXml):
	for conclusion in conclusions:
		writeLogFile( "j2llogs.logs" , "\nSystem try to prove \n"+str(conclusion)+"\n" )
		if conclusion is None:
			return "Failed to Prove"
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
		condition_map={}
		frame_axioms=eqset2constraintlist_update(f)
		for x in frame_axioms:
			constraint_list.append(x)
		out_axioms=eqset2constraintlist_update(o)
		
		for x in out_axioms:
			constraint_list.append(x)
		for x in a: 
        		equations=wff2z3_update(x)
        		getAllCondtion(x,condition_map)
        		equations_sp=None	
                	constraint_list.append(equations)
                	if x[0]=='s1':
        			equations_sp=wff2z3SC_update(x)
        			if equations_sp is not None:
        				constraint_list.append(equations_sp)
		for x in constaints:
			constraint_list.append(x)
		for x in pre_condition:
        		constraint_list.append(x)
		
		filter_map={}
		for element in defineDetaillist:
			if element[0] not in filter_map.keys():
		        	filter_map[element[0]]=element[0]
		        	vfact.append(element)
		defineDetaillist=[]
		
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
			#print x
			#print variable
	return None















#Recursive Function to ** to power Function

def transferToFunctionRec(expression):

	term=isFunction(expression)
	
	if term is None:
		return None

	if 'ForAll' in expression and term=='ForAll':
		arg_list=extract_args(expression)
		result=transferToFunctionRec(arg_list[1])
		if result is not None:
			return 'ForAll('+arg_list[0]+','+result+')'
		else:
			return None
	elif 'Or' in expression and term=='Or':
		arg_list=extract_args(expression)
		result1=transferToFunctionRec(arg_list[0])
		result2=transferToFunctionRec(arg_list[1])
		if result1 is not None and result2 is not None:
			return 'Or('+result1+','+result2+')'
		else:
			return None
	elif 'And' in expression and term=='And':
		arg_list=extract_args(expression)

		result1=transferToFunctionRec(arg_list[0])
		result2=transferToFunctionRec(arg_list[1])
		if result1 is not None and result2 is not None:
			return 'And('+result1+','+result2+')'
		else:
			return None
	elif 'Implies' in expression and term=='Implies':
		arg_list=extract_args(expression)
		result1=transferToFunctionRec(arg_list[0])
		result2=transferToFunctionRec(arg_list[1])
		if result1 is not None and result2 is not None:
			return 'Implies('+result1+','+result2+')'
		else:
			return None
	elif 'Exists' in expression and term=='Exists':
		arg_list=extract_args(expression)
		result=transferToFunctionRec(arg_list[1])
		if result is not None:
			return 'Exists('+arg_list[0]+','+result+')'
		else:
			return None
	elif 'Not' in expression and term=='Not':
		arg_list=extract_args(expression)
		result=transferToFunctionRec(arg_list[0])
		if result is not None:
			return 'Not('+transferToFunctionRec(arg_list[0])+')'
		else:
			return None
	else:
		return translatepowerToFun(expression)
		
		
#Stack Implementaion 

class Stack:
     def __init__(self):
         self.items = []

     def isEmpty(self):
         return self.items == []

     def push(self, item):
         self.items.append(item)

     def pop(self):
         return self.items.pop()

     def peek(self):
         return self.items[len(self.items)-1]

     def size(self):
         return len(self.items)


def translatepowerToFunCheck(expression):
    if "**" in expression:
    	expression=transferToFunctionSyntax(str(expression))
    	xform = expr.transformString(expression)[1:-1]
    	xform=xform.replace('[','(')
    	expression=xform.replace(']',')')
   	#print expression
    return expression

#expression="(A+B+((Z**(K)-1)/(Z-1))*(Z-1))"
expression="((Z**(K)-1)/(Z-1))*(Z-1)"
expression="(Z/2)*6<=Z"
expression="r6(_n2)>=(((2**-(_n2))*((2**_N1)*B))/2)"
#expressionChecking(expression)
def expressionChecking(expression):
	if '(((((((' not in str(expression):
		if "**" in str(expression):
			expression=translatepowerToFunCheck(str(expression))
		p = getParser()
		tree = p.parse_expression(expression)
		expr_wff=eval(expressionCreator(tree)) 
		flag=False
		return expr2simplified(expr_wff,flag)
	else:
		return str(expression),False



#wff to Simplified Expression
def expr2simplified(e,flag):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op,flag
    else:
	if op in _infix_op and len(args)==2:
	    expr1,flag=expr2simplified(args[0],flag)
	    if flag==True:
	    	expr2,flag=expr2simplified(args[1],flag)
	    	flag=True
	    else:
	    	expr2,flag=expr2simplified(args[1],flag)
	    if op=='*' and expr_op(args[0])=='/':
	    	n,d=fraction(expr1)
	    	if gcd(d,expr2)!=1:
	    		flag=True
	    elif op=='/' and expr_op(args[0])=='*':
	    	n,d=fraction(expr2)
	    	if gcd(expr1,d)!=1:
	    		flag=True
            if flag==True:
            	expression= '(' + expr1+ op + expr2 +')' 
            else:
            	expression= '((' + str(pow_to_mul(powsimp(expr1)))+ ')'+ op + '('+ str(pow_to_mul(powsimp(expr2)))+'))' 
            return expression,flag
        else:
            return op +'('+ ','.join(list(trim_p(expr2string1(x)) for x in args))+ ')',flag
        	

#Is Function and Return the name

#expression="(A+B+((Z**(K)-1)/(Z-1))*(Z-1))"
#expression="((((Z**(K)-1)/(Z-1))*(Z-1)))"

#expression="ForAll(Y+1,Exits(X==Y))"

#expression="(X<(Y+y))"
#expression="Rest(Z,Exists(K,((((Z**(K)-1)/(Z-1))*(Z-1)))))"
#expression="m1==((((Z**(K)-1)/(Z-1))*(Z-1)))"

def isFunction(expression):
	function=['ForAll','Or','And','Exists','Implies','Not']

	operators=['==','<=','>=','>','<','!=']
	if 'ForAll' in expression or 'Or' in expression or 'And' in expression or 'Exists' in  expression or 'Implies' in expression or 'Not' in expression:
		arg_list=extract_args(expression)
		arglist=""
		for arg in arg_list:
			if arglist=="":
				arglist='('+arg
			else:
				arglist+=','+arg
		arglist+=")"
		
		
		tem_expression=expression.replace(arglist,'')
		tem_expression=tem_expression.strip()
		
		if tem_expression in function:
			return tem_expression
		else:
			return None
	else:
		arg_list=extract_args(expression)
		arglist=""
		for arg in arg_list:
			if arglist=="":
				arglist='('+arg
			else:
				arglist+=','+arg
		arglist+=")"
		tem_expression=expression.replace(arglist,'')
		tem_expression=tem_expression.strip()
		if tem_expression=='':
			return expression
		else:
			status=False
			for operator in operators:
				if operator in tem_expression:
					status=True
			if status==True:
				return expression
			else:
				return None


#C parsing Function


"""

#C Function Class
#Plain Python object to store Information about Function
"""
class cFunctionclass(object):
 	def __init__(self, functionname, returnType , inputvar, localvar):
        	self.functionname = functionname
        	self.inputvar = inputvar
        	self.returnType = returnType
        	self.localvar = localvar
        def getFunctionname(self):
        	return self.methodname
        def getreturnType(self):
        	return self.returnType
        def getInputvar(self):
        	return self.inputvar
        def getLocalvar(self):
        	return self.localvar



def programTransformation(function_body):

    generator = c_generator.CGenerator()   
   
    global break_count
    global continue_count
    global new_variable
    global dummyCount
    
    new_variable={}
        
    #Handling Pointer
    
    statements= handlingPointer(function_body.block_items)
        
    #Syntax translation of the function body
    
    #print '#######1'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######1'
        
    statements=syntaxTranslate(statements)


    statements=arrangeEmptyStatement(statements)
    #print '#######1'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######1'
   
    #Convert Initiation to assignments   
    
    statements=construct_program(statements)
    
    #print '#######2'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######2'

    #print(generator.visit(c_ast.Compound(block_items=statements)))
    
    #Reconstruct Program by Removing assert,assume,error
    
    statements=reconstructPreDefinedFun(statements)
    
    #print '#######3'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######3'
        
    #Replace return by goto statement
        
    statements=remove_return(statements)
    
    #print '#######4'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######4'
    
        
    #Replace goto structured statement
        
    statements=gotoremoval(statements)
    
    #print '#######5'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######5'
        
    update_statements=[]
        
    #Add new variable
        
    for var in new_variable.keys():
    	temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
    	update_statements.append(temp)
        	
    for statement in statements:
    	update_statements.append(statement)
        	
    #print '#######6'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######6' 
      
      
    #Remove Empty If Loops  
    
    update_statements=removeEmptyIfLoop(update_statements)
        
    #Remove Dead Code
    
    #print '#######6'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######6'
    
    
    update_statements=removeDeadCode(update_statements)
    
    
    #print '#######7'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######7'
        
    #Simplify Conditions
        
    statements=simplifyProgram(update_statements)
    
    
    #print '#######8'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######8'
    
    #Add Break Removal Modules
    
    
    break_map={}
    break_count=0
    continue_count=0
    
    statements=getBreakStmt(statements,break_map)
    
    #print '#######9'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######9'
    
    
    statements=changeConditionProgram(statements)
    
        
    update_statements=[]
    
    for var in new_variable.keys():
    	temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
       	update_statements.append(temp)
        	
    for statement in statements:
    	update_statements.append(statement)
    
    dummyCount=0
    
    #print '#######10'
    #print(generator.visit(c_ast.Compound(block_items=update_statements)))
    #print '#######10'
    
    
    statements=functionToAssignment(update_statements)
    
    
    statements=change_var_name(statements)
    
    
    #print '#######11'
    #print(generator.visit(c_ast.Compound(block_items=statements)))
    #print '#######11'
       
    update_statements=[]
    
    if dummyCount>0:
    	for x in range(0, dummyCount):
    		temp=c_ast.Decl(name='_'+str(x+1)+'DUMMY', quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname='_'+str(x+1)+'DUMMY', quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
       		update_statements.append(temp)
    for statement in statements:
    	update_statements.append(statement)

    return update_statements










#file_name='functionTest2.c'

#file_name='functionTest4.c'

#file_name='mcmillan2006_true_unreach_call.c'

def translate(file_name):
	if not(os.path.exists(file_name)): 
        	print "File not exits"
		return

	start_time=current_milli_time()
	content=None
	global new_variable
	global fail_count
	global error_count
	global assume_count
        global assert_count
        global defineMap
        global defineDetaillist
        fail_count=0
        error_count=0
        assume_count=0
        assert_count=0
	with open(file_name) as f:
		content = f.read()
	content=comment_remover_file(content)
	content=content.replace('\r','')
	defineMap={}
	content,defineMap=preProcessorHandling(content)
	text = r""" """+content
	parser = c_parser.CParser()
	#ast = parse_file(file_name, use_cpp=True)
	ast = parser.parse(text)
	#Type defination replacement
	getAllTypeDef(ast)
	generator = c_generator.CGenerator()
	writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Translate \n"+"\nParameters--\n File Name--"+file_name+"\n")
	if ast is None:
		print "Error present in code. Please verify you input file"
	       	return
	if len(ast.ext)==0:
		print "Error present in code. Please verify you input file"
	        return
    	externalvarmap={}
	functionvarmap={}
	memberfunctionmap={}
	axiomeMap={}
	addition_array_map={}
	function_vfact_map={}
	pointer_map={}
	array_map={}
    	counter=0   
    	   	
    	
    	
    	for e in ast.ext:
    		pointer_list=[]
    		if type(e) is c_ast.Decl:
    			if type(e.type) is c_ast.FuncDecl:
    				parametermap={}
    				new_e,pointer_list,array_list=pointerHandlingParameter(e)
    				if new_e is None:
					function_decl=e
				else:
					function_decl=new_e
				if function_decl.type.args is not None:
					for param_decl in function_decl.type.args.params:
						if param_decl.name is not None:
				    			if type(param_decl.type) is c_ast.ArrayDecl:
				    	    			degree=0
				    	    			data_type,degree=getArrayDetails(param_decl,degree)
								variable=variableclass(param_decl.name, data_type,None,degree,None)
							else:
								variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
        						parametermap[param_decl.name]=variable

				membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,None,None,0,0)
				functionvarmap[membermethod.getMethodname()]=membermethod
    			elif type(e.type) is c_ast.TypeDecl:
            			var_type=None
            			initial_value=None
            			for child in e.children():
                			if type(child[1].type) is c_ast.IdentifierType:
                    				var_type=child[1].type.names[0]
					else:
                    				initial_value=child[1].value
            			variable=variableclass(e.name, var_type,None,None,initial_value)
            			externalvarmap[e.name]=variable
    		else:
    			if type(e) is c_ast.FuncDef:
    				parametermap={}
    				new_e,pointer_list,array_list=pointerHandlingParameter(e)
    				if new_e is None:
					function_decl=e
				else:
					function_decl=new_e
    				function_body = e.body
    				function_body=pointerHandlingDecl(function_body,pointer_list,array_list)
    				localvarmap=getVariables(function_body)
    				counter=counter+1
    				if function_decl.type.args is not None:
					for param_decl in function_decl.type.args.params:
						if param_decl.name is not None:
							if type(param_decl.type) is c_ast.ArrayDecl:
								#print param_decl.show()
								degree=0
								data_type,degree=getArrayDetails(param_decl,degree)
								variable=variableclass(param_decl.name, data_type,None,degree,None)
							elif type(param_decl.type) is c_ast.PtrDecl:
								stmt=pointerToArray(param_decl)
								#print stmt.show()
								if stmt is not None and type(stmt.type) is c_ast.ArrayDecl:
									degree=0
									data_type,degree=getArrayDetails(param_decl,degree)
									variable=variableclass(stmt.name, data_type,None,degree,None)
							
									
							else:				
								variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
			    				parametermap[param_decl.name]=variable
    				if function_decl.name in functionvarmap.keys():
					membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,counter)
					functionvarmap[function_decl.name]=membermethod
				else:
					if function_decl.type.args is not None:
						for param_decl in function_decl.type.args.params:
							if param_decl.name is not None:
								if type(param_decl.type) is c_ast.ArrayDecl:
									degree=0
									data_type,degree=getArrayDetails(param_decl,degree)
									variable=variableclass(param_decl.name, data_type,None,degree,None)
								elif type(param_decl.type) is c_ast.PtrDecl:
									stmt=pointerToArray(param_decl)
									if stmt is not None and type(stmt.type) is c_ast.ArrayDecl:
										degree=0
										data_type,degree=getArrayDetails(param_decl,degree)
										variable=variableclass(stmt.name, data_type,None,degree,None)
								
								else:	
									variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
								parametermap[param_decl.name]=variable
					membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,counter)
					functionvarmap[membermethod.getMethodname()]=membermethod
					pointer_map[membermethod.getMethodname()]=pointer_list
					array_map[membermethod.getMethodname()]=array_list

   	
    	for medthod in functionvarmap.keys():
    	
                membermethod=functionvarmap[medthod]
    		body=membermethod.getBody()
    		
    		if body is not None:                            
                    statements=programTransformation(body)
                    pointer_list=pointer_map[medthod]
                    array_list=array_map[medthod]
                    statements=pointerHandling(statements,pointer_list,array_list)
                    body_comp = c_ast.Compound(block_items=statements)
    		    membermethod.setBody(body_comp)
    		    localvarmap=getVariables(body_comp)
    		    membermethod.setLocalvar(localvarmap)
    		else:
		    membermethod.setBody(None)
    		    membermethod.setLocalvar(None)
                    
    	#program in intermediate form
    	programeIF=[]

    	programeIF.append('-1')
    			
    	programeIF.append('prog')

    	programe_array=[]

    	variables_list_map={}

    	for medthod in functionvarmap.keys():
    		membermethod=functionvarmap[medthod]
    		body=membermethod.getBody()
    		if body is not None:
    			new_variable={}
    			update_statements=[]
    			   		
	    		body_comp=body
	    		
	    		statements=body.block_items
	    		
    			membermethod.setBody(body_comp)
    			
    			localvarmap=getVariables(body_comp)
    			
    			membermethod.setLocalvar(localvarmap)
    			membermethod=functionvarmap[medthod]
    			    			
    			function=[]
    			
    			function.append('-1')
    			
    			function.append('fun')    			
    			
    			functionName=[]
    			
    			allvariable={}
    			
    			for x in membermethod.getInputvar():
				allvariable[x]=membermethod.getInputvar()[x]
			for x in membermethod.getLocalvar():
        			allvariable[x]=membermethod.getLocalvar()[x]
    			if validationOfInput(allvariable)==True:
				print "Please Rename variable Name {S,Q,N,in,is} to other Name"
          			return
    
    			program,variablesarray,fname,iputmap,opvariablesarray=translate2IntForm(membermethod.getMethodname(),membermethod.getreturnType(),membermethod.getBody(),membermethod.getInputvar())
			
		
			functionName.append(fname)
			
			for var in iputmap:
				functionName.append(str(var))
				
			function.append(functionName)
			
			function.append(program)

			programe_array.append(function)
		
			variables_list_map[fname]=variablesarray
			
			addition_array=[]
			
			addition_array.append(iputmap)
			
			addition_array.append(allvariable)
			
			addition_array.append(opvariablesarray)
			

			
			addition_array_map[fname]=addition_array
			
			memberfunctionmap[fname]=membermethod
			
			function_vfact_list=[]
			function_vfact=[]
			function_vfact.append(fname)
			function_vfact.append(len(iputmap))
			parameters_type=[]
			parameters_type.append(membermethod.getreturnType())
			for x in defineDetaillist:
				#print x
				function_vfact_list.append(x)
			defineDetaillist=[]
			for element in iputmap.keys():
				variable=iputmap[element]
				if variable is not None:
					parameters_type.append(variable.getVariableType())
			function_vfact.append(parameters_type)
			function_vfact_list.append(function_vfact)
			function_vfact_map[fname]=function_vfact_list	


        programeIF.append(programe_array)
        
                      
        f_map,o_map,a_map,cm_map,assert_map,assume_map=translate1(programeIF,variables_list_map,1)
        
        if type(f_map) is dict and type(o_map) is dict and type(a_map) is dict and type(cm_map) is dict:
                for key in f_map.keys():
        		f=f_map[key]
        		o=o_map[key]
        		a=a_map[key]
        		cm=cm_map[key]
        		assert_list=assert_map[key]
        		assume_list=assume_map[key]
        		addition_array=addition_array_map[key]
        		vfacts,constraints=getVariFunDetails(f,o,a,addition_array[1],addition_array[2])
        		


        		var_map={}
			eqset2stringvfact(f,var_map)
			eqset2stringvfact(o,var_map)
			for x in a: 
        			wff2stringvfact(x,var_map)
        		for x in assert_list:
        			wff2stringvfact(x,var_map)
        		for x in assume_list:
        			wff2stringvfact(x,var_map)

        		
        		for element1 in  var_map.keys():
        			flag=False
        			for element2 in vfacts:
        				if element2[0]==element1:
        					flag=True
				if flag==False:
					vfact=[]
					vfact.append(element1)
					vfact.append(len(var_map[element1])-1)
					vfact.append(var_map[element1])
					vfacts.append(vfact)
       		
        		

        		
        		
        		for element in function_vfact_map.keys():
        		
        			function_vfact_list=function_vfact_map[element]
        			for x in function_vfact_list:
        				vfacts.append(x)
          		
          		
        		
        		axiom=axiomclass(f,o,a,membermethod.getInputvar(), vfacts, constraints,cm,assert_list,assume_list)
        		axiomeMap[key]=axiom
                program=programclass(file_name, memberfunctionmap , externalvarmap, axiomeMap)
                return program
        else:
        	return None

			    









def prove_auto(file_name):
	if not(os.path.exists(file_name)): 
        	print "File not exits"
		return

	start_time=current_milli_time()
	content=None
	global new_variable
	global fail_count
	global error_count
	global assume_count
        global assert_count
        global defineMap
        global defineDetaillist
        fail_count=0
        error_count=0
        assume_count=0
        assert_count=0
	with open(file_name) as f:
		content = f.read()
	content=comment_remover_file(content)
	content=content.replace('\r','')
	defineMap={}
	content,defineMap=preProcessorHandling(content)
	text = r""" """+content
	parser = c_parser.CParser()
	#ast = parse_file(file_name, use_cpp=True)
	ast = parser.parse(text)
        #ast.show()
	generator = c_generator.CGenerator()
	writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Translate \n"+"\nParameters--\n File Name--"+file_name+"\n")
	if ast is None:
		print "Error present in code. Please verify you input file"
	       	return
	if len(ast.ext)==0:
		print "Error present in code. Please verify you input file"
	        return
    	externalvarmap={}
	functionvarmap={}
	memberfunctionmap={}
	axiomeMap={}
	addition_array_map={}
	function_vfact_map={}
	witnessXml_map={}
	
    	counter=0        
    	
    	for e in ast.ext:
    		if type(e) is c_ast.Decl:
    			if type(e.type) is c_ast.FuncDecl:
    				parametermap={}
				function_decl=e
				if function_decl.type.args is not None:
					for param_decl in function_decl.type.args.params:
						if param_decl.name is not None:
				    			if type(param_decl.type) is c_ast.ArrayDecl:
				    	    			degree=0
				    	    			data_type,degree=getArrayDetails(param_decl,degree)
								variable=variableclass(param_decl.name, data_type,None,degree,None)
							else:
								variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
        						parametermap[param_decl.name]=variable

				membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,None,None,0,0)
				functionvarmap[membermethod.getMethodname()]=membermethod

    			elif type(e.type) is c_ast.TypeDecl:
            			var_type=None
            			initial_value=None
            			for child in e.children():
                			if type(child[1].type) is c_ast.IdentifierType:
                    				var_type=child[1].type.names[0]
					else:
                    				initial_value=child[1].value
            			variable=variableclass(e.name, var_type,None,None,initial_value)
            			externalvarmap[e.name]=variable
    		else:
    			if type(e) is c_ast.FuncDef:
    				parametermap={}
    				function_decl=e.decl
    				function_body = e.body
    				statements=function_body.block_items
    				statements=change_var_name(statements)
    				function_body= c_ast.Compound(block_items=statements)
    				localvarmap=getVariables(function_body)
    				counter=counter+1
    				if function_decl.type.args is not None:
					for param_decl in function_decl.type.args.params:
						if param_decl.name is not None:
							if type(param_decl.type) is c_ast.ArrayDecl:
								#print param_decl.show()
								degree=0
								data_type,degree=getArrayDetails(param_decl,degree)
								variable=variableclass(param_decl.name, data_type,None,degree,None)
							elif type(param_decl.type) is c_ast.PtrDecl:
								stmt=pointerToArray(param_decl)
								#print stmt.show()
								if stmt is not None and type(stmt.type) is c_ast.ArrayDecl:
									degree=0
									data_type,degree=getArrayDetails(param_decl,degree)
									variable=variableclass(stmt.name, data_type,None,degree,None)
							
									
							else:				
								variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
			    				parametermap[param_decl.name]=variable
    				if function_decl.name in functionvarmap.keys():
					membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,counter)
					functionvarmap[function_decl.name]=membermethod
				else:
					if function_decl.type.args is not None:
						for param_decl in function_decl.type.args.params:
							if param_decl.name is not None:
								if type(param_decl.type) is c_ast.ArrayDecl:
									degree=0
									data_type,degree=getArrayDetails(param_decl,degree)
									variable=variableclass(param_decl.name, data_type,None,degree,None)
								elif type(param_decl.type) is c_ast.PtrDecl:
									stmt=pointerToArray(param_decl)
									if stmt is not None and type(stmt.type) is c_ast.ArrayDecl:
										degree=0
										data_type,degree=getArrayDetails(param_decl,degree)
										variable=variableclass(stmt.name, data_type,None,degree,None)
								
								else:	
									variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
								parametermap[param_decl.name]=variable
					membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,counter)
					functionvarmap[membermethod.getMethodname()]=membermethod

    	
    	for medthod in functionvarmap.keys():
                membermethod=functionvarmap[medthod]
    		body=membermethod.getBody()

    		if body is not None:                            
                    statements=programTransformation(body)
    		    body_comp = c_ast.Compound(block_items=statements)
    		    localvarmap=getVariables(body_comp)
    		    statements,localvarmap=addAllExtVariables(statements,externalvarmap,localvarmap)
    		    
   		    
    		    body_comp = c_ast.Compound(block_items=statements)
    		    membermethod.setBody(body_comp)
    		    membermethod.setLocalvar(localvarmap)
    		else:
		    membermethod.setBody(None)
    		    membermethod.setLocalvar(None)
                    
    	#program in intermediate form
    	programeIF=[]

    	programeIF.append('-1')
    			
    	programeIF.append('prog')

    	programe_array=[]

    	variables_list_map={}

    	for medthod in functionvarmap.keys():
    		membermethod=functionvarmap[medthod]
    		body=membermethod.getBody()
    		if body is not None:
    			new_variable={}
    			update_statements=[]
    			   		
	    		body_comp=body
	    		
	    		statements=body.block_items
	    		
    			membermethod.setBody(body_comp)
    			
    			localvarmap=getVariables(body_comp)
    			
    			for var in externalvarmap.keys():
				variable=externalvarmap[var]
				localvarmap[var]=variable
    			
    			membermethod.setLocalvar(localvarmap)
    			membermethod=functionvarmap[medthod]
    			    			
    			function=[]
    			
    			function.append('-1')
    			
    			function.append('fun')    			
    			
    			functionName=[]
    			
    			allvariable={}
    			
    			for x in membermethod.getInputvar():
				allvariable[x]=membermethod.getInputvar()[x]
			for x in membermethod.getLocalvar():
        			allvariable[x]=membermethod.getLocalvar()[x]
    			if validationOfInput(allvariable)==True:
				print "Please Rename variable Name {S,Q,N,in,is} to other Name"
          			return
    
    			program,variablesarray,fname,iputmap,opvariablesarray=translate2IntForm(membermethod.getMethodname(),membermethod.getreturnType(),membermethod.getBody(),membermethod.getInputvar())

		
			functionName.append(fname)
			
			for var in iputmap:
				functionName.append(str(var))
				
			function.append(functionName)
			
			function.append(program)

			programe_array.append(function)
		
			variables_list_map[fname]=variablesarray
			
			addition_array=[]
			
			addition_array.append(iputmap)
			
			addition_array.append(allvariable)
			
			addition_array.append(opvariablesarray)
			
			addition_array_map[fname]=addition_array
			
			memberfunctionmap[fname]=membermethod
                        
                        
			
			function_vfact_list=[]
			function_vfact=[]
			function_vfact.append(fname)
			function_vfact.append(len(iputmap))
			parameters_type=[]
			parameters_type.append(membermethod.getreturnType())
			for x in defineDetaillist:
				#print x
				function_vfact_list.append(x)
					
			
			defineDetaillist=[]
			for element in iputmap.keys():
				variable=iputmap[element]
				if variable is not None:
					parameters_type.append(variable.getVariableType())
			function_vfact.append(parameters_type)
			function_vfact_list.append(function_vfact)
			function_vfact_map[fname]=function_vfact_list	
                        
                        resultfunction='__VERIFIER_nondet_int'
                        
                        filename=file_name
                        functionname=functionName
                        
                        witnessXml=getWitness(filename,fname,resultfunction)
                        witnessXml_map[fname]= witnessXml      	
      
        
        programeIF.append(programe_array)
        #print '##################' 
        #print programe_array
        #print '##################' 
        #print variables_list_map
        #print '##################'               
        f_map,o_map,a_map,cm_map,assert_map,assume_map=translate1(programeIF,variables_list_map,1)
        
        if type(f_map) is dict and type(o_map) is dict and type(a_map) is dict and type(cm_map) is dict:
                for key in f_map.keys():
        		f=f_map[key]
        		o=o_map[key]
        		a=a_map[key]
        		cm=cm_map[key]
        		assert_list=assert_map[key]
        		assume_list=assume_map[key]
        		addition_array=addition_array_map[key]
        		vfacts,constraints=getVariFunDetails(f,o,a,addition_array[1],addition_array[2])
        		
		
        		var_map={}
			eqset2stringvfact(f,var_map)
			eqset2stringvfact(o,var_map)
			for x in a: 
        			wff2stringvfact(x,var_map)
        		for x in assert_list:
        			wff2stringvfact(x,var_map)
        		for x in assume_list:
        			wff2stringvfact(x,var_map)
        		for element1 in  var_map.keys():
        			flag=False
        			for element2 in vfacts:
        				if element2[0]==element1:
        					flag=True
				if flag==False and isArrayFunction( element1 )==False:
					vfact=[]
					if element1=='_x1':
						var_arr_list=[]
						var_arr_list.append('array')
						vfact.append(element1)
						vfact.append(len(var_map[element1])-1)
						vfact.append(var_arr_list)
						vfacts.append(vfact)
					
					else:
						vfact.append(element1)
						vfact.append(len(var_map[element1])-1)
						vfact.append(var_map[element1])
						vfacts.append(vfact)
       			
        		
        		for element in function_vfact_map.keys():
        			function_vfact_list=function_vfact_map[element]
        			for x in function_vfact_list:
        				vfacts.append(x)
        		
			
        		axiom=axiomclass(f,o,a,membermethod.getInputvar(), vfacts, constraints,cm,assert_list,assume_list)
        		axiomeMap[key]=axiom
                program=programclass(file_name, memberfunctionmap , externalvarmap, axiomeMap, witnessXml_map)              
         
                prove_auto_process(program)
                #return program
        else:
        	print 'Error in  Translation'








def translate2IntForm(function_name,function_type,function_body,parametermap):
    if function_body is None: 
        print "Empty Body"
	return None
        
    start_time=current_milli_time()
    
    statements=function_body.block_items
       
    localvarmap=getVariables(function_body)
    
    
    print 'Program Body'
    
    generator = c_generator.CGenerator()
    
    
    print(generator.visit(function_body))

    membermethod=membermethodclass(function_name,function_type,parametermap,localvarmap,function_body,0,0)
    print "Function Name:"
    print membermethod.getMethodname()
    print "Return Type:"
    print membermethod.getreturnType()
    print "Input Variables:"
    var_list="{"
    for x in membermethod.getInputvar():
        if membermethod.getInputvar()[x].getDimensions()>0:
            var_list+=' '+x+':array'
	else:
	    var_list+=' '+x+':'+membermethod.getInputvar()[x].getVariableType()
    var_list+='}'
    print var_list
    print "Local Variables:"
    var_list="{"
    for x in membermethod.getLocalvar():
        if membermethod.getLocalvar()[x].getDimensions()>0:
            var_list+=' '+x+':array'
	else:
            var_list+=' '+x+':'+membermethod.getLocalvar()[x].getVariableType()
    var_list+='}'
    print var_list
    allvariable={}
    program_dec_start=""
    program_dec_end=""
    for lvap in localvarmap:
        var=localvarmap[lvap]
        if var is not None and var.getInitialvalue() is not None:
	    if type(var.getInitialvalue()) is not c_ast.BinaryOp and '__VERIFIER_nondet' in var.getInitialvalue():
	    	defineDetailtemp=[]
	    	parameter_list=[]
	    	parameter_list.append('int')
		defineDetailtemp.append(var.getInitialvalue())
		defineDetailtemp.append(0)
		defineDetailtemp.append(parameter_list)
		defineDetaillist.append(defineDetailtemp)
            if program_dec_start=="":
            	if type(var.getInitialvalue()) is c_ast.BinaryOp:
            	        program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+expressionCreator_C(var.getInitialvalue())+"]"
                	program_dec_end="]"
            	else:
            		if is_hex(str(var.getInitialvalue())) is not None:
                		program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+is_hex(str(var.getInitialvalue()))+"')]"
                	else:
                		program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue())+"')]"
                	program_dec_end="]"
            else:
            	if type(var.getInitialvalue()) is c_ast.BinaryOp:
            	        program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+expressionCreator_C(var.getInitialvalue())+"]"
                	program_dec_end+="]"
            	else:
            		if is_hex(str(var.getInitialvalue())) is not None:
                		program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+is_hex(str(var.getInitialvalue()))+"')]"
                	else:
                		program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue())+"')]"
                	program_dec_end+="]"
    for x in membermethod.getInputvar():
        allvariable[x]=membermethod.getInputvar()[x]
    for x in membermethod.getLocalvar():
        allvariable[x]=membermethod.getLocalvar()[x]
    


       
    expressions=organizeStatementToObject_C(statements)
    
    primeStatement(expressions)
    variablesarray={}
    opvariablesarray={}
    count=0
    arrayFlag=False
    for variable in allvariable:
        count+=1
        if allvariable[variable].getDimensions()>0:
            variablesarray[variable]=eval("['_y"+str(count)+"','array']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','array']")
            list_parameter="'array'"
            for i in range(0, allvariable[variable].getDimensions()):
                if list_parameter=='':
                    list_parameter="'int'"
                else:
                    list_parameter+=",'int'"
            list_parameter+=",'"+allvariable[variable].getVariableType()+"'"
            #key1=str(allvariable[variable].getDimensions())+'array'
            key1='d'+str(allvariable[variable].getDimensions())+'array'
            arrayFlag=True
            if key1 not in variablesarray.keys():
             	count+=1
                variablesarray[key1]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                opvariablesarray[key1+"1"]=eval("['_y"+str(count)+"',"+list_parameter+"]")
        else:
            variablesarray[variable]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
    if program_dec_start=="":
        str_program=programToinductiveDefination_C(expressions , allvariable)
    else:
        str_program=program_dec_start+','+programToinductiveDefination_C(expressions , allvariable)+program_dec_end
    
    program=eval(str_program)
    return program,variablesarray,membermethod.getMethodname(),membermethod.getInputvar(),opvariablesarray





defineDetaillist=[] 


def translate_C(file_name):
    if not(os.path.exists(file_name)): 
        print "File not exits"
	return
    #Global Variables
    global break_count
    global continue_count
    global new_variable
    
    
    start_time=current_milli_time()
    content=None
    with open(file_name) as f:
    	content = f.read()
    content=content.replace('\r','')
    text = r""" """+content
    parser = c_parser.CParser()
    #ast = parse_file(file_name, use_cpp=True)
    ast = parser.parse(text)
    generator = c_generator.CGenerator()
    writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Translate \n"+"\nParameters--\n File Name--"+file_name+"\n")
    if ast is None:
        print "Error present in code. Please verify you input file"
        return
    if len(ast.ext)==0:
        print "Error present in code. Please verify you input file"
        return
    generator = c_generator.CGenerator()
    function_decl = ast.ext[0].decl
    
    parametermap={}
    if function_decl.type.args is not None:
    	for param_decl in function_decl.type.args.params:
    		if type(param_decl.type) is c_ast.ArrayDecl:
    	    		degree=0
    	    		data_type,degree=getArrayDetails(param_decl,degree)
			variable=variableclass(param_decl.name, data_type,None,degree,None)
		else:
			variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None)
        	parametermap[param_decl.name]=variable
    function_body = ast.ext[0].body
    
    
    new_variable={}
    
    
        
    defineMap={}
    
    defineDetaillist=[]
   
        
    statements=function_body.block_items
       
    localvarmap=getVariables(function_body)

    membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,0)
    print "Function Name:"
    print membermethod.getMethodname()
    print "Return Type:"
    print membermethod.getreturnType()
    print "Input Variables:"
    var_list="{"
    for x in membermethod.getInputvar():
        if membermethod.getInputvar()[x].getDimensions()>0:
            var_list+=' '+x+':array'
	else:
	    var_list+=' '+x+':'+membermethod.getInputvar()[x].getVariableType()
    var_list+='}'
    print var_list
    print "Local Variables:"
    var_list="{"
    for x in membermethod.getLocalvar():
        if membermethod.getLocalvar()[x].getDimensions()>0:
            var_list+=' '+x+':array'
	else:
            var_list+=' '+x+':'+membermethod.getLocalvar()[x].getVariableType()
    var_list+='}'
    print var_list
    allvariable={}
    program_dec_start=""
    program_dec_end=""
    for lvap in localvarmap:
        var=localvarmap[lvap]
        if var is not None and var.getInitialvalue() is not None:
            if program_dec_start=="":
                program_dec_start="['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue())+"')]"
                program_dec_end="]"
            else:
                program_dec_start+=",['-1','seq',['-1','=',expres('"+str(var.getVariablename())+"'),"+"expres('"+str(var.getInitialvalue())+"')]"
                program_dec_end+="]"
    for x in membermethod.getInputvar():
        allvariable[x]=membermethod.getInputvar()[x]
    for x in membermethod.getLocalvar():
        allvariable[x]=membermethod.getLocalvar()[x]
        
    #print getBody(function_body)
       
    expressions=organizeStatementToObject_C(statements)
    
    primeStatement(expressions)
    variablesarray={}
    opvariablesarray={}
    count=0
    arrayFlag=False
    for variable in allvariable:
        count+=1
        if allvariable[variable].getDimensions()>0:
            variablesarray[variable]=eval("['_y"+str(count)+"','array']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','array']")
            list_parameter="'array'"
            for i in range(0, allvariable[variable].getDimensions()):
                if list_parameter=='':
                    list_parameter="'int'"
                else:
                    list_parameter+=",'int'"
                list_parameter+=",'"+allvariable[variable].getVariableType()+"'"
                #key1=str(allvariable[variable].getDimensions())+'array'
                key1='d'+str(allvariable[variable].getDimensions())+'array'
                arrayFlag=True
                if key1 not in variablesarray.keys():
                    count+=1
                    variablesarray[key1]=eval("['_y"+str(count)+"',"+list_parameter+"]")
                    opvariablesarray[key1+"1"]=eval("['_y"+str(count)+"',"+list_parameter+"]")
        else:
            variablesarray[variable]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
            opvariablesarray[variable+"1"]=eval("['_y"+str(count)+"','"+allvariable[variable].getVariableType()+"']")
    if program_dec_start=="":
        str_program=programToinductiveDefination_C(expressions , allvariable)
    else:
        str_program=program_dec_start+','+programToinductiveDefination_C(expressions , allvariable)+program_dec_end
    
    program=eval(str_program)
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
    #f,o,a,cm=translate1(program,variablesarray,2)
    vfacts,constraints=getVariFunDetails(f,o,a,allvariable,opvariablesarray)
    end_time=current_milli_time()
    print "Times to Translate"
    print end_time-start_time
    writeLogFile( "j2llogs.logs" , getTimeStamp()+"\n End of Translation\n")
    axiom=axiomclass(f,o,a,membermethod.getInputvar(), vfacts, constraints,cm)
    return axiom
 
 
 
 
    
def getArrayDetails(statement,degree):
	if type(statement.type) is c_ast.ArrayDecl:
		degree=degree+1
		return getArrayDetails(statement.type,degree)
	elif type(statement.type) is c_ast.PtrDecl:
		degree=degree+1
		return getArrayDetails(statement.type,degree)
	else:
		return statement.type.type.names[0],degree


#Get All Variables


def getVariables(function_body):
    localvarmap={}
    statements=handlingPointer(function_body.block_items)
    #for decl in function_body.block_items:
    for decl in statements:
        if type(decl) is c_ast.Decl:
            var_type=None
            initial_value=None
            if type(decl.type) is c_ast.ArrayDecl:
                if is_number(decl.type.type.declname[-1])==True :
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=c_ast.ArrayDecl(type=c_ast.TypeDecl(declname=decl.type.type.declname+'_var', quals=decl.type.type.quals, type=decl.type.type.type), dim=decl.type.dim, dim_quals=decl.type.dim_quals), init=decl.init, bitsize=decl.bitsize)
            else:
                if is_number(decl.type.declname[-1])==True :
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=c_ast.TypeDecl(declname=decl.type.declname+'_var', quals=decl.type.quals, type=decl.type.type), init=decl.init, bitsize=decl.bitsize)



            if type(decl.type) is c_ast.ArrayDecl:
            	degree=0
	    	var_type,degree=getArrayDetails(decl,degree)
		variable=variableclass(decl.name, var_type,None,degree,initial_value)
	    else:
            	for child in decl.children():
            		if type(child[1]) is c_ast.TypeDecl:
                		if type(child[1].type) is c_ast.IdentifierType:
                    			var_type=child[1].type.names[0]
				else:
                    			initial_value=child[1].value
                    	else:
                    		if type(child[1]) is c_ast.FuncCall:
			    		parameter=''
					if child[1].args is not None:
			    			for param in child[1].args.exprs:
			    				if type(param) is c_ast.ID:
			    					if parameter=='':
					        			parameter = "expres('"+param.name+"')"
					        		else:
					        			parameter += ",expres('"+param.name+"')"
			    				elif type(param) is c_ast.Constant:
			    		    			if parameter=='':
									parameter = "expres('"+param.value+"')"
								else:
					        			parameter += ",expres('"+param.value+"')"
							else:
								if type(statement) is c_ast.ArrayRef:
									degree=0
									stmt,degree=createArrayList_C(statement,degree)
								    	if parameter=='':
										parameter = "expres('d"+str(degree)+'array'+"',["+stmt+"])"
									else:
		        							parameter += ","+"expres('d"+str(degree)+'array'+"',["+stmt+"])"
						#initial_value="['"+child[1].name.name+"',"+parameter+"]"
						initial_value="['"+child[1].name.name+"',"+parameter+"]"
					else:
						#initial_value="expres('"+child[1].name.name+"'"+")"
						initial_value=child[1].name.name
				else:
					if type(child[1]) is c_ast.Constant:
						initial_value=child[1].value
                                        elif type(child[1]) is c_ast.ID:
						initial_value=child[1].name
					else:
                                                print expressionCreator_C(child[1])
						initial_value=child[1]
            	variable=variableclass(decl.name, var_type,None,None,initial_value)
            localvarmap[decl.name]=variable
    return localvarmap





"""

Organization of AST 

"""
               
def organizeStatementToObject_C(statements):
	count=0
	degree=0
	expressions=[]
	for statement in statements:
                if type(statement) is c_ast.Assignment:
			count=count+1
			expression=expressionclass(statement, count, True,degree)
			expressions.append(expression)
                elif type(statement) is c_ast.While:
                    blockexpressions=[]
                    if statement.stmt is not None:
                        degree=degree+1
			count,blockexpressions=blockToExpressions_C(statement.stmt.block_items, degree, count)
			degree=degree-1
		    block=blockclass( blockexpressions, statement.cond, count , True, degree)
		    expressions.append(block)
		else:
			if type(statement) is c_ast.If:
				count,ifclass=ifclassCreator_C(statement, degree, count)
				expressions.append(ifclass)
			else:
				count=count+1
				expression=expressionclass(statement, count, True,degree)
				expressions.append(expression)
					
     	return expressions



"""

Conditionl Loop to a Array of Statement Compatible to Translator Program 
IfClass Creator

"""

def ifclassCreator_C(statement, degree, count):
        blockexpressions1=None
	blockexpressions2=None
	predicate=statement.cond
	#print statement.iftrue.show()
	#print statement.iffalse.show()
        if statement.iftrue is not None:
        	if type(statement.iftrue) is c_ast.Compound:
            		count,blockexpressions1=blockToExpressions_C(statement.iftrue.block_items, degree, count)
            	else:
            		new_block_items=[]
            		new_block_items.append(statement.iftrue)
            		count,blockexpressions1=blockToExpressions_C(new_block_items, degree, count)
        if statement.iffalse is not None and type(statement.iffalse) is c_ast.If:
        	count,blockexpressions2=ifclassCreator_C(statement.iffalse, degree, count)
        else:
        	if statement.iffalse is not None:
        		if type(statement.iffalse) is c_ast.Compound:
        			count,blockexpressions2=blockToExpressions_C(statement.iffalse.block_items, degree, count)
        		else:
        			new_block_items=[]
        			new_block_items.append(statement.iffalse)
            			count,blockexpressions2=blockToExpressions_C(new_block_items, degree, count)
	ifclass=Ifclass(predicate, blockexpressions1, blockexpressions2, count ,True ,degree)
	return count,ifclass



"""

Converting code block,while loop ,conditional expression and expression to corresponding Classes

"""

def blockToExpressions_C(body, degree, count):
	expressions=[]
	if body is not None:
		for statement in body:
                    if type(statement) is c_ast.Assignment:
			count=count+1
			expression=expressionclass(statement, count, True,degree)
			expressions.append(expression)
                    elif type(statement) is c_ast.While:
                        blockexpressions=[]
                        if statement.stmt is not None:
                            degree=degree+1
                            count,blockexpressions=blockToExpressions_C(statement.stmt.block_items, degree, count)
                            degree=degree-1
                        block=blockclass( blockexpressions, statement.cond, count , True, degree)
                        expressions.append(block)
                    else:
			if type(statement) is c_ast.If:
				count,ifclass=ifclassCreator_C(statement, degree, count)
				expressions.append(ifclass)
	return count,expressions




"""

Block of Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefination_C(expressions, allvariable):
	programsstart=""
	programsend=""
	statements=""
	for expression in expressions:
		if type(expression) is expressionclass:
			if type(expression.getExpression()) is c_ast.Assignment:
                                var=None
                                if type(expression.getExpression().lvalue) is c_ast.ID:
                                    var="expres('"+str(expression.getExpression().lvalue.name)+"')"
                                elif type(expression.getExpression().lvalue) is c_ast.Constant:
                                    var="expres('"+str(expression.getExpression().lvalue.value)+"')" 
                                elif type(expression.getExpression().lvalue) is c_ast.ArrayRef:
                                    degree=0
       				    stmt,degree=createArrayList_C(expression.getExpression().lvalue,degree)
                                    var="expres('d"+str(degree)+'array'+"',["+stmt+"])"
                                elif type(expression.getExpression().lvalue) is c_ast.FuncCall:
                                	parameter=''
				        statement=expression.getExpression().lvalue
					if statement.args is not None:
						for param in statement.args.exprs:
							if type(param) is c_ast.ID:
								if parameter=='':
									parameter = "expres('"+param.name+"')"
								else:
									parameter += ",expres('"+param.name+"')"
							elif type(param) is c_ast.Constant:
								if parameter=='':
									parameter = "expres('"+param.value+"')"
								else:
									parameter += ",expres('"+param.value+"')"
							elif type(param) is c_ast.BinaryOp:
							    	if parameter=='':
									parameter =expressionCreator_C(param)
								else:
					        			parameter += ","+expressionCreator_C(param)
					var="['"+statement.name.name+"',"+parameter+"]"
		
                                
				if expression.getIsPrime()==False:
                                    if programsstart=="":
                                        programsstart="['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"
                                        programsend="]"
				    else:
					programsstart+=",['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"
					programsend+="]"
				else:
                                    if programsstart=="":
                                        programsstart="['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"+programsend
                                    else:
                                        programsstart+=",['-1','=',"+str(var)+","+str(expressionCreator_C(expression.getExpression().rvalue))+"]"+programsend
                        elif type(expression.getExpression()) is c_ast.FuncCall:
                        	parameter=''
                        	statement=expression.getExpression()
				if statement.args is not None:
			    		for param in statement.args.exprs:
			    			if type(param) is c_ast.ID:
			    				if parameter=='':
					        		parameter = "expres('"+param.name+"')"
					        	else:
					        		parameter += ",expres('"+param.name+"')"
			    			elif type(param) is c_ast.Constant:
			    		    		if parameter=='':
								parameter = "expres('"+param.value+"')"
							else:
					        		parameter += ",expres('"+param.value+"')"
						elif type(param) is c_ast.BinaryOp:
			    		    		if parameter=='':
								parameter =expressionCreator_C(param)
							else:
					        		parameter += ","+expressionCreator_C(param)
					
                                        if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"
					                programsend="]"
						else:
							programsstart+=","+"['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"
							programsend+="]"
					else:
						if programsstart=="":
					        	programsstart="['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"+programsend
					        else:
                                        		programsstart+=","+"['-1','seq',"+"['"+statement.name.name+"',"+parameter+"]"+programsend
				else:
  					if expression.getIsPrime()==False:
						if programsstart=="":
							programsstart="['-1','seq',"+"expres('"+statement.name.name+"'"+")"
							programsend="]"
						else:
							programsstart+=","+"['-1','seq',"+"expres('"+statement.name.name+"'"+")"
							programsend+="]"
					else:
						if programsstart=="":
							programsstart="['-1','seq',"+"expres('"+statement.name.name+"'"+")"+programsend
						else:
                                        		programsstart+=","+"['-1','seq',"+"expres('"+statement.name.name+"'"+")"+programsend
		elif type(expression) is blockclass:
			predicatestmt="['-1','while',"+expressionCreator_C(expression.predicate)+","+programToinductiveDefination_C( expression.getExpression(), allvariable)+"]"
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
			condition=expressionCreator_C(expression.predicate)
			expressionif=None
			expressionelse=None
			predicatestmt=""
			if expression.getExpressionif() is not None:
				expressionif=programToinductiveDefination_C( expression.getExpressionif(), allvariable)
			if expression.getExpressionelse() is not None:
				if type(expression.getExpressionelse()) is Ifclass:
					#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
					expressionelse=programToinductiveDefinationIfElse_C( expression.getExpressionelse(), allvariable)
				else:
					expressionelse=programToinductiveDefination_C( expression.getExpressionelse(), allvariable)
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
		
	if programsstart[0]==',':
		programsstart=programsstart[1:]	
	return programsstart





"""

IfElse Block Statement to Array of Statement Compatible to Translator Program 

"""
def programToinductiveDefinationIfElse_C(expression, allvariable):
	programsstart=""
	programsend=""
	statements=""
	if type(expression) is expressionclass:
		if type(expression.getExpression()) is c_ast.Assignment:
                        var=None
                        if type(expression.getExpression().lvalue) is c_ast.ID:
                            var="expres('"+str(expression.getExpression().lvalue.name)+"')"
                        elif type(expression.getExpression().lvalue) is c_ast.Constant:
                            var="expres('"+str(expression.getExpression().lvalue.value)+"')"
                        elif type(expression.getExpression().lvalue) is c_ast.ArrayRef:
			    	degree=0
			       	stmt,degree=createArrayList_C(expression.getExpression().lvalue,degree)
    				var="expres('d"+str(degree)+'array'+"',["+stmt+"])"
			if expression.getIsPrime()==False:
                            if programsstart=="":
                                programsstart="['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"
                                programsend="]"
			    else:
                                programsstart+=",['-1','seq',['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"
                                programsend+="]"
                        else:
                            if programsstart=="":
                                programsstart+="['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend
                            else:
                                programsstart+=",['-1','=',"+str(var)+","+str(expressionCreator(expression.getExpression().rhs))+"]"+programsend

	elif type(expression) is blockclass:
		predicatestmt="['-1','while',"+expressionCreator_C(expression.predicate)+","+programToinductiveDefination_C( expression.getExpression(), allvariable)+"]"
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
		condition=expressionCreator_C(expression.predicate)
		expressionif=None
		expressionelse=None
		predicatestmt=""
		if expression.getExpressionif() is not None:
			expressionif=programToinductiveDefination_C( expression.getExpressionif(), allvariable)
		if expression.getExpressionelse() is not None:
			if type(expression.getExpressionelse()) is Ifclass:
				#expressionelse=programToinductiveDefination( expression.getExpressionelse().getExpressionif(), allvariable)
				expressionelse=programToinductiveDefinationIfElse_C( expression.getExpressionelse(), allvariable)
			else:
				expressionelse=programToinductiveDefination_C( expression.getExpressionelse(), allvariable)
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

Program Expression to a Array of Statement Compatible to Translator Program 

"""

def expressionCreator_C(statement):
    expression=""
    global defineMap
    global defineDetaillist
    if type(statement) is c_ast.ID:
    	if statement.name in defineMap.keys():
    		value = defineMap[statement.name]
    		return "expres('"+value+"')"
    	else:
        	return "expres('"+statement.name+"')"
    elif type(statement) is c_ast.Constant:
    	if statement.type=='char':
		return "['char',expres("+statement.value+")]"
    	else:
        	if is_hex(statement.value) is not None:
        		return "expres('"+is_hex(statement.value)+"')"
        	else:
        		return "expres('"+statement.value+"')"
    elif type(statement) is c_ast.FuncCall:
    	parameter=''
    	parameter_list=[]
    	defineDetaillist=[]
    	defineDetailtemp=[]
    	parameter_list.append('int')
	if statement.args is not None:
    		for param in statement.args.exprs:
    			if type(param) is c_ast.ID:
    				parameter_list.append('int')
    				if param.name in defineMap.keys():
    					param.name = defineMap[param.name]
    				if parameter=='':
		        		parameter = "expres('"+param.name+"')"
		        	else:
		        		parameter += ",expres('"+param.name+"')"
    			elif type(param) is c_ast.Constant:
    				parameter_list.append('int')
    		    		if parameter=='':
					if is_hex(param.value) is not None:
						parameter = "expres('"+is_hex(param.value)+"')"
					else:
						parameter = "expres('"+param.value+"')"
				else:
		        		if is_hex(param.value) is not None:
		        			parameter += ",expres('"+is_hex(param.value)+"')"
		        		else:
		        			parameter += ",expres('"+param.value+"')"
			else:
				if type(statement) is c_ast.ArrayRef:
					parameter_list.append('int')
				    	degree=0
				       	stmt,degree=createArrayList_C(statement,degree)
    					if parameter=='':
						parameter = "expres('d"+str(degree)+'array'+"',["+stmt+"])"
					else:
		        			parameter += ","+"expres('d"+str(degree)+'array'+"',["+stmt+"])"
				
				#print '@@@@@@@@@@@RamRam'
				#print param.show()
				#print '@@@@@@@@@@@'
		defineDetailtemp.append(statement.name.name)
		defineDetailtemp.append(len(parameter_list)-1)
		defineDetailtemp.append(parameter_list)
		defineDetaillist.append(defineDetailtemp)
	
		
		return "['"+statement.name.name+"',"+parameter+"]"
	else:
		defineDetailtemp.append(statement.name.name)
		defineDetailtemp.append(len(parameter_list)-1)
		defineDetailtemp.append(parameter_list)
		defineDetaillist.append(defineDetailtemp)
		defineDetaillist
	
		return "expres('"+statement.name.name+"'"+")"
    elif type(statement) is c_ast.ArrayRef:
    	degree=0
       	stmt,degree=createArrayList_C(statement,degree)
    	return "expres('d"+str(degree)+'array'+"',["+stmt+"])"
    else:
        if statement.op in ['+','-','*','/','%']:
            expression="expres('"
            expression+=statement.op
            if type(statement) is c_ast.BinaryOp:
            	expression+="',["+expressionCreator_C(statement.left)
           	expression+=','+expressionCreator_C(statement.right)
            else:
            	expression+="',["+expressionCreator_C(statement.expr)
            expression+='])'
            return expression
        else:
            #if statement.op == '!=':
            #    statement=c_ast.UnaryOp(op='!', expr=c_ast.BinaryOp(op='==',left=statement.left, right=statement.right))

            expression="['"
            if statement.op == '&&':
                expression+='and'
            elif statement.op == '||':
                expression+='or'
            elif statement.op == '!':
                expression+='not'
            else:
                expression+=statement.op
            if type(statement) is c_ast.BinaryOp:
            	expression+="',"+expressionCreator_C(statement.left)
            	expression+=','+expressionCreator_C(statement.right)
            	expression+=']'
            else:
            	expression="expres('"
            	if statement.op == '!':
                	expression+='not'
                else:
                	expression+=statement.op
            	expression+="',["+expressionCreator_C(statement.expr)+"]"
            	expression+=')'
            return expression




"""

Construct Array List

"""
def createArrayList_C(statement,degree):
	if type(statement) is c_ast.ArrayRef:
		degree=degree+1
		stmt=''
		if type(statement.name) is c_ast.ArrayRef:
			stmt,degree=createArrayList_C(statement.name,degree)
			if type(statement.subscript) is c_ast.ID:
				stmt+=",expres('"+statement.subscript.name+"')"
			else:
				stmt+=",expres('"+statement.subscript.value+"')"
			return stmt,degree
		else:
			if type(statement.name) is c_ast.ID:
				if type(statement.subscript) is c_ast.ID:
					stmt+="expres('"+statement.name.name+"')"+",expres('"+statement.subscript.name+"')"
					return stmt,degree
				elif type(statement.subscript) is c_ast.BinaryOp:
					stmt+="expres('"+statement.name.name+"')"+","+expressionCreator_C(statement.subscript)
					return stmt,degree
				else:
					stmt+="expres('"+statement.name.name+"')"+",expres('"+statement.subscript.value+"')"
					return stmt,degree
			else:
				stmt+="expres('"+statement.name.value+"')"+",expres('"+statement.subscript.value+"')"
				return stmt,degree
	else:
		return "expres('"+statement.name+"')",degree


    
"""
 
Translate Syntax Code 
 
"""
 

"""

Syntax translation module

"""



def syntaxTranslate(statements):
        update_statements=[]
        for statement in statements:
                if type(statement) is c_ast.UnaryOp:
                        if statement.op=='++' or statement.op=='p++':
                                update_statements.append(c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='+',left=statement.expr, right=c_ast.Constant('int','1'))))
                        elif statement.op=='--' or statement.op=='p--':
                                update_statements.append(c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='-',left=statement.expr, right=c_ast.Constant('int','1'))))
                        else:
                                update_statements.append(statement)
                elif type(statement) is c_ast.For:
                        update_statements.append(statement.init)
                        if type(statement.stmt) is c_ast.Compound:
                        	new_block_items=statement.stmt.block_items
                        	if new_block_items is None:
                                    new_block_items=[]
                        	new_block_items.append(statement.next)
                        	new_block_items=syntaxTranslate(new_block_items)
                        	new_stmt=c_ast.Compound(block_items=new_block_items)
                        	update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                        else:
                        	new_block_items=[]
                        	new_block_items.append(statement.stmt)
                        	new_block_items.append(statement.next)
				new_block_items=syntaxTranslate(new_block_items)
				new_stmt=c_ast.Compound(block_items=new_block_items)
				update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                elif type(statement) is c_ast.DoWhile:
                	if type(statement.stmt) is c_ast.Compound:
		        	new_block_items=statement.stmt.block_items
		        	if new_block_items is None:
                                    new_block_items=[]
		        	for item in new_block_items:
		        		update_statements.append(item)
		        	new_block_items=syntaxTranslate(new_block_items)
		        	new_stmt=c_ast.Compound(block_items=new_block_items)
		        	update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                        else:
                        	new_block_items=[]
                        	new_block_items.append(statement.stmt)
                        	for item in new_block_items:
					update_statements.append(item)
				new_block_items=syntaxTranslate(new_block_items)
				new_stmt=c_ast.Compound(block_items=new_block_items)
				update_while=c_ast.While(statement.cond,new_stmt)
                        	update_statements.append(update_while)
                elif type(statement) is c_ast.Switch:
                	stmts=statement.stmt.block_items
                	statement=convertToIfElse(stmts,statement.cond)
                	update_statements.append(statement)
                elif type(statement) is c_ast.While:
                	if type(statement.stmt) is c_ast.Compound:
                		update_statements.append(c_ast.While(cond=syntaxTranslateStmt(statement.cond),stmt=c_ast.Compound(block_items=syntaxTranslate(statement.stmt.block_items))))
                	else:
                		new_block_items=[]
				new_block_items.append(statement.stmt)
				update_statements.append(c_ast.While(cond=syntaxTranslateStmt(statement.cond),stmt=c_ast.Compound(block_items=syntaxTranslate(new_block_items))))
                elif type(statement) is c_ast.If:
                	update_statements.append(syntaxTranslateIf(statement))
                elif type(statement) is c_ast.Assignment:
                	if statement.op=='+=':
                		update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='+', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                	elif statement.op=='-=':
                		update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='-', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                	elif statement.op=='/=':
                		update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='/', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                	elif statement.op=='%=':
                		update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=c_ast.BinaryOp(op='%', left=c_ast.ID(name=statement.lvalue.name), right=statement.rvalue)))
                	else:
                		if type(statement.rvalue) is c_ast.Assignment:
                			stmts=[]
                			separateAllAssignment(statement,stmts)
                			for stmt in stmts:
                				update_statements.append(stmt)
                		else:
                			update_statements.append(c_ast.Assignment(op=statement.op, lvalue=statement.lvalue, rvalue=statement.rvalue))
                
                elif type(statement) is c_ast.ExprList:
                    statement=syntaxTranslate(statement.exprs)
                    for exp_stmt in statement:
                         update_statements.append(exp_stmt)
                elif type(statement) is c_ast.Label:
			update_statements.append(c_ast.Label(name=statement.name, stmt=None))
			if type(statement.stmt) is c_ast.Compound:
				new_block_items=syntaxTranslate(statement.stmt.block_items)
				for item in new_block_items:
					update_statements.append(item)	
			else:
				if statement.stmt is not None:
					new_block_items=[]
					new_block_items.append(statement.stmt)
					new_block_items=syntaxTranslate(new_block_items)
					for item in new_block_items:
						update_statements.append(item)

                else:
                        update_statements.append(statement)
        return update_statements



def syntaxTranslateIf(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=syntaxTranslate(statement.iftrue.block_items))
			else:
				new_iftrue=c_ast.Compound(block_items=[])
		else:
			if type(statement) is c_ast.UnaryOp:
				new_iftrue=syntaxTranslateStmt(statement.iftrue)
			elif type(statement) is c_ast.BinaryOp:
				new_iftrue=syntaxTranslateStmt(statement.iftrue)
			else:
				new_blocks=[]
				new_blocks.append(statement.iftrue)
				new_iftrue=c_ast.Compound(block_items=syntaxTranslate(new_blocks))
				
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=syntaxTranslate(statement.iffalse.block_items))
			else:
				new_iffalse=c_ast.Compound(block_items=[])
		else:
			if type(statement.iffalse) is c_ast.If:
				new_iffalse=syntaxTranslateIf(statement.iffalse)
			else:
				if type(statement) is c_ast.UnaryOp:
					new_iffalse=syntaxTranslateStmt(statement.iffalse)
				elif type(statement) is c_ast.BinaryOp:
					new_iffalse=syntaxTranslateStmt(statement.iffalse)
				else:
					new_blocks=[]
					new_blocks.append(statement.iffalse)
					new_iffalse=c_ast.Compound(block_items=syntaxTranslate(new_blocks))
	return c_ast.If(cond=syntaxTranslateStmt(statement.cond), iftrue=new_iftrue, iffalse=new_iffalse)


#
# Change Assignment statement to a list of Assignment statements
#


def separateAllAssignment(statement,stmts):
	if type(statement) is c_ast.Assignment:
		if type(statement.rvalue) is c_ast.Assignment:
			value=separateAllAssignment(statement.rvalue,stmts)
			stmts.append(c_ast.Assignment(op=statement.op, lvalue=statement.lvalue, rvalue=value))
			return value
		else:
			stmts.append(c_ast.Assignment(op=statement.op, lvalue=statement.lvalue, rvalue=statement.rvalue))
			return statement.rvalue
	return None
	



	

"""

Covert Switch Case to If-Else-If loop

"""



def convertToIfElse(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		if type(statement) is not c_ast.Default:
			new_condition_left=constructCondition(statements,condition)
			new_condition_right,new_block_items,statements,is_break=constructBody(statements,condition)
			new_compund_left=c_ast.Compound(block_items=new_block_items)
			
			if new_condition_left is not None:
				new_Else_stmt=convertToIfElse(statements,condition)
				new_If_stmt=c_ast.If(cond=c_ast.BinaryOp(op='||', left=new_condition_left, right=new_condition_right),iftrue=new_compund_left,iffalse=new_Else_stmt)
				return new_If_stmt
			else:
				new_Else_stmt=convertToIfElse(statements,condition)
				new_If_stmt=c_ast.If(cond=new_condition_right,iftrue=new_compund_left,iffalse=new_Else_stmt)
				return new_If_stmt
		else:
			update_stmts=[]
			for stmt in statement.stmts:
				if type(stmt) is not c_ast.Break:
					update_stmts.append(stmt)
			return c_ast.Compound(block_items=update_stmts)
		

	return None


def syntaxTranslateStmt(statement):
	if type(statement) is c_ast.UnaryOp:
		if statement.op=='++' or statement.op=='p++':
	        	return c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='+',left=statement.expr, right=c_ast.Constant('int','1')))
		elif statement.op=='--' or statement.op=='p--':
	        	return c_ast.Assignment(op='=',lvalue=statement.expr, rvalue=c_ast.BinaryOp(op='-',left=statement.expr, right=c_ast.Constant('int','1')))
	        else:
                        return statement
	else:
		if type(statement) is c_ast.BinaryOp:
			return c_ast.BinaryOp(op=statement.op,left=syntaxTranslateStmt(statement.left),right=syntaxTranslateStmt(statement.right))
		else:
			return statement



"""

Covert Switch Case to If-Else-If loop

"""

	
def constructCondition(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		if type(statement) is not c_ast.Default:
			if len(statement.stmts)==0:
				new_condition_left=c_ast.BinaryOp(op='==', left=condition, right=statement.expr)
				new_condition_right=constructCondition(statements[1:],condition)
				if new_condition_right is None:
					return new_condition_left
				else:
					return c_ast.BinaryOp(op='||', left=new_condition_left, right=new_condition_right)
			else:
				return None
		else:
			return None
	return None


"""

Covert Switch Case to If-Else-If loop

"""


def constructBody(statements,condition):
	if statements is not None and len(statements)>0:
		statement=statements[0]
		if type(statement) is not c_ast.Default:
			if len(statement.stmts)>0:
				update_stmts=[]
				new_condition=c_ast.BinaryOp(op='==', left=condition, right=statement.expr)
				is_break=False
				for stmt in statement.stmts:
					if type(stmt) is c_ast.Break:
						is_break=True;
					else:
						update_stmts.append(stmt)
				return new_condition,update_stmts,statements[1:],is_break
			else:
				return constructBody(statements[1:],condition)
		else:
			return None,None,None,False
	return None,None,None,False



			    
"""
 
Goto removal Modules Start

"""

new_variable={}

break_count=0

continue_count=0



def remove_return(statements):
	end_label_map={}
	statements=returnReplacement(statements,end_label_map)
	update_statements=[]
	temp=c_ast.Decl(name='RET', quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname='RET', quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
	update_statements.append(temp)
	for statement in statements:
		update_statements.append(statement)
	for label in end_label_map.keys():
    		update_statements.append(c_ast.Label(name=label, stmt=None))
    	return update_statements








"""

Method for simplification of Condition

"""

def simplifyCondition(statement):
	if type(statement) is c_ast.UnaryOp:
		if statement.op=='!':
			if type(statement.expr) is c_ast.ID:
				return statement
			elif type(statement.expr) is c_ast.Constant:
				return statement
			else:
				return getComplement(statement.expr)
		else:
			return c_ast.UnaryOp(op=statement.op,expr=simplifyCondition(statement.expr))
	elif type(statement) is c_ast.BinaryOp:
		return c_ast.BinaryOp(op=statement.op,left=simplifyCondition(statement.left), right=simplifyCondition(statement.right))
	else:
		return statement

"""

Method for Generate  Complement of Condition

"""


def getComplement(statement):
	if type(statement) is c_ast.UnaryOp:
		if statement.op=='!': 
			return simplifyCondition(statement.expr)
		else:
			return c_ast.UnaryOp(op=statement.op,expr=simplifyCondition(statement.expr))
	
	elif type(statement) is c_ast.BinaryOp:
		if statement.op=='<':
			return c_ast.BinaryOp(op='>=',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='>':
			return c_ast.BinaryOp(op='<=',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='<=':
			return c_ast.BinaryOp(op='>',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='>=':
			return c_ast.BinaryOp(op='<',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='!=':
			return c_ast.BinaryOp(op='==',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='==':
			return c_ast.BinaryOp(op='!=',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='&&':
			return c_ast.BinaryOp(op='||',left=getComplement(statement.left), right=getComplement(statement.right))
		elif statement.op=='||':
			return c_ast.BinaryOp(op='&&',left=getComplement(statement.left), right=getComplement(statement.right))
		else:
			return c_ast.BinaryOp(op=statement.op,left=getComplement(statement.left), right=getComplement(statement.right))


	else:
		return statement




"""

For Whole program

"""

def changeCondition(statement):
	if type(statement) is c_ast.ID:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.Constant:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.FuncCall:
		return c_ast.BinaryOp(op='>',left=statement,right=c_ast.Constant(type='int', value='0'))
	elif type(statement) is c_ast.UnaryOp:
		if statement.op=='!':
			if type(statement.expr) is c_ast.ID:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			elif type(statement.expr) is c_ast.Constant:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			elif type(statement.expr) is c_ast.FuncCall:
				return c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			else:
				return statement
		else:
			return statement
	elif type(statement) is c_ast.BinaryOp:
                left_stmt=None
                right_stmt=None
                if statement.op=='||':
                    if type(statement.left) is c_ast.ID:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.Constant:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.FuncCall:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    else:
                        left_stmt=changeCondition(statement.left)
                        
                    if type(statement.right) is c_ast.ID:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.Constant:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.FuncCall:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    else:
                        right_stmt=changeCondition(statement.right)
                    return c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
                elif statement.op=='&&':
                    if type(statement.left) is c_ast.ID:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.Constant:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.left) is c_ast.FuncCall:
                        left_stmt=c_ast.BinaryOp(op='>',left=statement.left,right=c_ast.Constant(type='int', value='0'))
                    else:
                        left_stmt=changeCondition(statement.left)
                        
                    if type(statement.right) is c_ast.ID:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.Constant:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    elif type(statement.right) is c_ast.FuncCall:
                        right_stmt=c_ast.BinaryOp(op='>',left=statement.right,right=c_ast.Constant(type='int', value='0'))
                    else:
                        right_stmt=changeCondition(statement.right)
                    return c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
                else:
                 	return statement
                        
		
	else:
		return statement




def modificationOfCondition(statement):
	if type(statement) is c_ast.ID:
		return True,statement
	elif type(statement) is c_ast.Constant:
		return True,statement
	elif type(statement) is c_ast.FuncCall:
		return True,statement
	elif type(statement) is c_ast.UnaryOp:
		if statement.op=='!':
			status,statement.expr=modificationOfCondition(statement.expr)
			if status==True:
				return False,c_ast.BinaryOp(op='<=',left=statement.expr,right=c_ast.Constant(type='int', value='0'))
			else:
				return True,statement
		else:
			return True,statement
	elif type(statement) is c_ast.BinaryOp:
		left_stmt=None
                right_stmt=None
		if statement.op=='||':
			status,left_stmt=modificationOfCondition(statement.left)
			if status==True:
				left_stmt=c_ast.BinaryOp(op='>',left=left_stmt,right=c_ast.Constant(type='int', value='0'))
			status=False
			status,right_stmt=modificationOfCondition(statement.right)
			if status==True:
				right_stmt=c_ast.BinaryOp(op='>',left=right_stmt,right=c_ast.Constant(type='int', value='0'))
			return False,c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
		elif statement.op=='&&':
			status,left_stmt=modificationOfCondition(statement.left)
			if status==True:
				left_stmt=c_ast.BinaryOp(op='>',left=left_stmt,right=c_ast.Constant(type='int', value='0'))
			status=False
			status,right_stmt=modificationOfCondition(statement.left)
			if status==True:
				right_stmt=c_ast.BinaryOp(op='>',left=right_stmt,right=c_ast.Constant(type='int', value='0'))
			return False,c_ast.BinaryOp(op=statement.op,left=left_stmt, right=right_stmt)
		elif statement.op=='>':
			return False,statement
		elif statement.op=='<':
			return False,statement
		elif statement.op=='>=':
			return False,statement
		elif statement.op=='<=':
			return False,statement
		elif statement.op=='=':
			return False,statement
		elif statement.op=='==':
			return False,statement
		elif statement.op=='!=':
			return False,statement
		else:
			status1,left_stmt=modificationOfCondition(statement.left)
			status2,right_stmt=modificationOfCondition(statement.right)
			if status1==True and status2==True:
				return True,c_ast.BinaryOp(op=statement.op,left=left_stmt,right=right_stmt)
			else:
				return False,c_ast.BinaryOp(op=statement.op,left=left_stmt,right=right_stmt)
			
	else:
		return False,statement
		


def changeConditionProgram(statements):
	if statements is not None:
		update_statements=[]
		for statement in statements:
			if type(statement) is c_ast.If:
				update_statements.append(changeConditionProgramIf(statement))
			elif type(statement) is c_ast.While:
				update_statements.append(c_ast.While(cond=changeCondition(statement.cond),stmt=c_ast.Compound(block_items=changeConditionProgram(statement.stmt.block_items))))
			else:
				update_statements.append(statement)
		return update_statements			
	return None



def changeConditionProgramIf(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=changeConditionProgram(statement.iftrue.block_items))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=changeConditionProgram(statement.iffalse.block_items))
			else:
				new_iftrue=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=changeConditionProgramIf(statement.iffalse)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=changeCondition(statement.cond),iftrue=new_iftrue,iffalse=new_iffalse)




def simplifyProgram(statements):
	if statements is not None:
		update_statements=[]
		for statement in statements:
			if type(statement) is c_ast.If:
				update_statements.append(simplifyProgram_If(statement))
			elif type(statement) is c_ast.While:
				update_statements.append(c_ast.While(cond=simplifyCondition(statement.cond),stmt=c_ast.Compound(block_items=simplifyProgram(statement.stmt.block_items))))
			else:
				update_statements.append(statement)
		return update_statements			
	return None



def simplifyProgram_If(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=simplifyProgram(statement.iftrue.block_items))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=simplifyProgram(statement.iffalse.block_items))
			else:
				new_iftrue=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=simplifyProgram_If(statement.iffalse)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=simplifyCondition(statement.cond),iftrue=new_iftrue,iffalse=new_iffalse)



def removeDeadCode(statements):
	update_statements=[]
	flag=False
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.Goto:
				flag=True
			elif type(statement) is c_ast.Label:
				flag=False
				stmts=statement.stmt
				if stmts is not None:
					for stmt in stmts:
						update_statements.append(stmt)
			else:
				if flag==False:
					update_statements.append(statement)
	return update_statements


def gotoremoval(statements):
	if statements is not None:
		label_map=constructLabelTable(statements,0,0,0)
		updateLabelTable(statements,0,0,0,label_map)
		keys=label_map.keys()
		
		for key in keys:
			labelMap={}
			listL=label_map[key]
			if len(listL[3])>1:
		    		statements=removeMultipleLabel(statements,key,labelMap)
		    		statements=addMultipleLabel(statements,key,labelMap)
		    		label_map=constructLabelTable(statements,0,0,0)
    				updateLabelTable(statements,0,0,0,label_map)
    			else:
    				if len(listL[3])==0:
					statements=removeOrphanLabel(statements,key)
					label_map=constructLabelTable(statements,0,0,0)
    					updateLabelTable(statements,0,0,0,label_map)
    			
    		#print '#################RamRam'
    		#body_comp = c_ast.Compound(block_items=statements)
    		#generator = c_generator.CGenerator()   
    	 	#print(generator.visit(body_comp))
    	 	#print '#################RamRam'
		label_map=constructLabelTable(statements,0,0,0)
    		updateLabelTable(statements,0,0,0,label_map)

		keys=label_map.keys()
		if len(keys)>0:
			item=keys[0]
			element = label_map[item]
    			lists = element[3]
    			
    			for list in lists:
    				if element[0]>=list[0] and element[1]>=list[1]:
        				statements=goto_finder(statements,item)
    					statements=go_block_finder(statements,item)
    					statements=gotoremoval(statements)
    				else:
    					statements=label_finder(statements,item)
    					statements=go_block_finder(statements,item)
    					statements=gotoremoval(statements)
    	return statements





#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label


def go_block_finder(statements,label):
	if statements is not None:
		flag_block_label=check_label_block(statements,label)  
		flag_block_goto=check_goto_block_Sp(statements,label)
		if flag_block_label==True and flag_block_goto==True:
			return remove_goto_block(statements,label)
		else:
			update_statements=[]
			for statement in statements:
				if type(statement) is c_ast.If:
					update_statements.append(go_block_finder_if(statement,label))
				elif type(statement) is c_ast.While:
					update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=go_block_finder(statement.stmt.block_items,label))))
				else:
					update_statements.append(statement)
		return update_statements
	return statements
				


#Finding Goto in a If Block to Call gotomovein
#Parameter pass statement 
#Label

def go_block_finder_if(statement,label):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=go_block_finder(statement.iftrue.block_items,label))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=go_block_finder(statement.iffalse.block_items,label))
			else:
				new_iftrue=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=go_block_finder_if(statement.iffalse,label)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond,iftrue=new_iftrue,iffalse=new_iffalse)






#Method to Remove Goto 


def remove_goto_block(statements,label): 
	flag_block_label=check_label_block(statements,label)  
	flag_block_goto=check_goto_block_Sp(statements,label)
	flag_block2,condition=check_goto(statements,label)
	flag_label=False
	flag_goto=False
	new_statements1=[]
	new_statements2=[]
	if flag_block_label==True and flag_block_goto==True:
		for statement in statements:
			#print type(statement)
			#print flag_label
			#print flag_goto
			if type(statement) is c_ast.Label:
				if label==statement.name:
					if flag_goto==True:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2),iffalse=None))
						if type(statement.stmt) is c_ast.Assignment:
							new_statements1.append(statement.stmt)
						elif type(statement.stmt) is c_ast.Compound:
							if statement.stmt is not None and statement.stmt.block_items is not None:
								for stmt in statement.stmt.block_items:
									new_statements1.append(stmt)
						else:
							new_statements1.append(statement.stmt)
						flag_label=False
						flag_goto=False
					else:
						if type(statement.stmt) is c_ast.Assignment:
							new_statements2.append(statement.stmt)
						elif type(statement.stmt) is c_ast.Compound:
							if statement.stmt is not None and statement.stmt.block_items is not None:
								for stmt in statement.stmt.block_items:
									new_statements2.append(stmt)
						flag_label=True
				else:
					if flag_goto==True or flag_label==True:
						
						if type(statement.stmt) is c_ast.Assignment:
							new_statements2.append(statement.stmt)
						elif type(statement.stmt) is c_ast.Compound:
							if statement.stmt is not None and statement.stmt.block_items is not None:
								for stmt in statement.stmt.block_items:
									new_statements2.append(stmt)
					else:
						new_statements1.append(statement)
			elif type(statement) is c_ast.If:
				flag_block_goto=check_goto_block_If(statement,label)
				if flag_block_goto:
					if flag_label==True:
						statement=getRidOfGoto(statement,label)
						for stmt in new_statements2:
							new_statements1.append(stmt)
						new_statements1.append(statement)
						
						new_break_map={}
						new_statements2=reOrganizeBreaks(new_statements2,new_break_map)

						new_statements1.append(c_ast.While(cond=condition, stmt=c_ast.Compound(block_items=new_statements2)))
						new_statements1=addingBreakVariables(new_statements1,new_break_map)
						flag_label=False
						flag_goto=False
					else:
						statement=getRidOfGoto(statement,label)
						new_statements1.append(statement)
						flag_goto=True
				else:
					if flag_goto==True or flag_label==True:
						new_statements2.append(statement)
					else:
						new_statements1.append(statement)
			else:
				if flag_goto==True or flag_label==True:
					new_statements2.append(statement)
				else:
					new_statements1.append(statement)
	
	return new_statements1
				
				



    
    
def constructLabelTable(statements,level,block,lineCount):
	label_map={}
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.If:
				label_map_temp=constructLabelTable_If(statement,level,block,lineCount)
	            		for item in label_map_temp:
            				label_map[item]=label_map_temp[item]
			elif type(statement) is c_ast.Label:
				lineCount=lineCount+1
			        info=[]
			        info.append(level)
	            		info.append(block)
	            		info.append(lineCount)
	            		info.append([])
				label_map[statement.name]=info
	        	else:
	        		if type(statement) is c_ast.While:
	        			level=level+1
	            			label_map_temp=constructLabelTable(statement.stmt.block_items,level,block,lineCount)
	            			for item in label_map_temp:
            					label_map[item]=label_map_temp[item]
            				level=level-1
            			else:
            				lineCount=lineCount+1
	return label_map




def constructLabelTable_If(statement,level,block,lineCount):
	label_map={}
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append([])
				label_map[statement.iftrue.name]=info
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
							lineCount=lineCount+1	            				
	            					info=[]
	            					info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append([])
	            					label_map[element.name]=info
	            				elif type(element) is c_ast.If:
	            					block=block+1
							label_map_temp=constructLabelTable_If(element,level,block,lineCount)
							for item in label_map_temp:
            							label_map[item]=label_map_temp[item]
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	label_map_temp=constructLabelTable(element.stmt.block_items,level,block,lineCount)
						        	for item in label_map_temp:
					            			label_map[item]=label_map_temp[item]
            							level=level-1
            						else:
            							lineCount=lineCount+1
	
			if type(statement.iffalse) is c_ast.Label:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append([])
				label_map[statement.iffalse.name]=statement.iffalse.name
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					lineCount=lineCount+1
	            					info=[]
							info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append([])
	            					label_map[element.name]=info
	            				elif type(element) is c_ast.If:
	            					block=block+1
							label_map_temp=constructLabelTable_If(element,level,block,lineCount)
							for item in label_map_temp:
            							label_map[item]=label_map_temp[item]
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	label_map_temp=constructLabelTable(element.stmt.block_items,level,block,lineCount)
						        	for item in label_map_temp:
					            			label_map[item]=label_map_temp[item]
            							level=level-1
            						else:
            							lineCount=lineCount+1
				else:
					if type(statement.iffalse) is c_ast.If:
						label_map_temp=constructLabelTable_If(statement.iffalse,level,block,lineCount)
						for item in label_map_temp:
							label_map[item]=label_map_temp[item]
	return label_map

    
    

def updateLabelTable(statements,level,block,lineCount,label_map):
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.If:
				updateLabelTable_If(statement,level,block,lineCount,label_map)
	        	else:
	        		if type(statement) is c_ast.While:
	        			level=level+1
	            			updateLabelTable(statement.stmt.block_items,level,block,lineCount,label_map)
            				level=level-1
            			else:
            				lineCount=lineCount+1





def updateLabelTable_If(statement,level,block,lineCount,label_map):
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Goto:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append(statement.cond)
				if statement.iftrue.name in label_map.keys():
					info_update=label_map[statement.iftrue.name]
				        list=info_update[3]
				        list.append(info)		

			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Goto:
							lineCount=lineCount+1	            				
	            					info=[]
	            					info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append(statement.cond)
	            					if element.name in label_map.keys():
	            						info_update=label_map[element.name]
	            						list=info_update[3]
	            						list.append(info)
	            				elif type(element) is c_ast.If:
	            					block=block+1
							updateLabelTable_If(element,level,block,lineCount,label_map)
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	updateLabelTable(element.stmt.block_items,level,block,lineCount,label_map)
            							level=level-1
            						else:
            							lineCount=lineCount+1
	
			if type(statement.iffalse) is c_ast.Goto:
				lineCount=lineCount+1	            				
				info=[]
				info.append(level)
				info.append(block)
				info.append(lineCount)
				info.append(statement.cond)
				if statement.iffalse.name in label_map.keys():
					info_update=label_map[statement.iffalse.name]
					list=info_update[3]
					list.append(info)
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Goto:
	            					lineCount=lineCount+1
	            					info=[]
							info.append(level)
	            					info.append(block)
	            					info.append(lineCount)
	            					info.append(statement.cond)
	            					if element.name in label_map.keys():
	            						info_update=label_map[element.name]
	            						list=info_update[3]
	            						list.append(info)
	            				elif type(element) is c_ast.If:
	            					block=block+1
							updateLabelTable_If(element,level,block,lineCount,label_map)
            						block=block-1
						else:
							if type(element) is c_ast.While:
								level=level+1
						        	updateLabelTable(element.stmt.block_items,level,block,lineCount,label_map)
            							level=level-1
            						else:
            							lineCount=lineCount+1
				else:
					if type(statement.iffalse) is c_ast.If:
						updateLabelTable_If(statement.iffalse,level,block,lineCount,label_map)
					
					
#Check a label in a block of statement


def check_label_block(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status=check_label_block_If(statement,label)
                        if temp_status==True:
                               status=True 
		elif type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	return status
	



def check_label_block_sp(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	return status

#Check a label in the blocks of statement of if loop
	
def check_label_block_If(statement,label):
        status=False
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				if statement.iftrue.name==label:
                                        status = True
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
                                                        if element.name==label:
                                                                status = True
                                                                
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                        status = True
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					if element.name==label:
                                                                status = True
				else:
					if type(statement.iffalse) is c_ast.If:
						temp_status = check_label_block_If(statement.iffalse,label)
						if temp_status==True:
                                                	status=True
	return status



#Check a label in statement


def check_label(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status=check_label_If(statement,label)
                        if temp_status==True:
                               status=True 
		elif type(statement) is c_ast.Label:
                        if statement.name==label:
                                status = True
	        else:
	        	if type(statement) is c_ast.While:
	            		temp_status= check_label(statement.stmt.block_items,label)
	            		if temp_status==True:
                                        status=True
	return status




#Check a label in statement of if loop

def check_label_If(statement,label):
        status=False
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Label:
				if statement.iftrue.name==label:
                                        status = True
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Label:
                                                        if element.name==label:
                                                                status = True
	            				elif type(element) is c_ast.If:
							temp_status = check_label_If(element,label)
							if temp_status==True:
                                                               status=True
						else:
							if type(element) is c_ast.While:
						        	temp_status = check_label(element.stmt.block_items,label)
						        	if temp_status==True:
                                                                        status=True
	
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                        status = True
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Label:
	            					if element.name==label:
                                                                status = True
	            				elif type(element) is c_ast.If:
                                                        temp_status = check_label_If(element,label)
                                                        if temp_status==True:
                                                                status=True
						else:
							if type(element) is c_ast.While:
								temp_status = check_label(element.stmt.block_items,label)
								if temp_status==True:
                                                                        status=True

				else:
					temp_status = check_label_If(statement.iffalse,label)
					if temp_status==True:
                                                status=True
	return status





#Check a goto-label in a block of statement


def check_goto_block(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.Goto:
                        if statement.name==label:
                                status = True

	return status


def check_goto_block_Sp(statements,label):
        status=False
	for statement in statements:
		if type(statement) is c_ast.Goto:
                        if statement.name==label:
                                status = True
               	elif type(statement) is c_ast.If:
                	temp_status=check_goto_block_If(statement,label)
                	if temp_status==True:
                		status=True
	return status
	
	

#Check a label in the blocks of statement of if loop
	
def check_goto_block_If(statement,label):
        status=False
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Goto:
				if statement.iftrue.name==label:
                                        status = True
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Goto:
                                                        if element.name==label:
                                                                status = True
			if type(statement.iffalse) is c_ast.Label:
                                if statement.iffalse.name==label:
                                        status = True
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Goto:
	            					if element.name==label:
                                                                status = True
				else:
					if type(statement.iffalse) is c_ast.If:
						temp_status = check_goto_block_If(statement.iffalse,label)
						if temp_status==True:
                                                	status=True
	return status



#Check a label in statement


def check_goto(statements,label):
        status=False
        condition=None
	for statement in statements:
		if type(statement) is c_ast.If:
                        temp_status,temp_cond=check_goto_If(statement,label)
                        if temp_status==True:
                               status=True
                               condition=temp_cond
		elif type(statement) is c_ast.Goto:
                        if statement.name==label:
                                status = True
	        else:
	        	if type(statement) is c_ast.While:
	            		temp_status,temp_cond= check_goto(statement.stmt.block_items,label)
	            		if temp_status==True:
                                        status=True
                                        condition=temp_cond
	return status,condition




#Check a label in statement of if loop

def check_goto_If(statement,label):
        status=False
        condition=None
	if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Goto:
				if statement.iftrue.name==label:
                                        status = True
                                        condition=statement.cond
			else:
	            		if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
	            			for element in statement.iftrue.block_items:
	            				if type(element) is c_ast.Goto:
                                                        if element.name==label:
                                                                status = True
                                                                condition=statement.cond
	            				elif type(element) is c_ast.If:
							temp_status,temp_cond = check_goto_If(element,label)
							if temp_status==True:
                                                               status=True
                                                               #condition=temp_cond
                                                               condition=c_ast.BinaryOp(op='&&', left=temp_cond, right=statement.cond)
						else:
							if type(element) is c_ast.While:
						        	temp_status,temp_cond = check_goto(element.stmt.block_items,label)
						        	if temp_status==True:
                                                                        status=True
                                                                        condition=temp_cond
	
			if type(statement.iffalse) is c_ast.Goto:
                                if statement.iffalse.name==label:
                                        status = True
                                        condition = c_ast.UnaryOp(op='!', expr=statement.cond)
			else:
				if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
	            			for element in statement.iffalse.block_items:
	            				if type(element) is c_ast.Goto:
	            					if element.name==label:
                                                                status = True
                                                                condition = c_ast.UnaryOp(op='!', expr=statement.cond)
	            				elif type(element) is c_ast.If:
                                                        temp_status,temp_cond = check_goto_If(element,label)
                                                        if temp_status==True:
                                                                status=True
                                                                #condition=temp_cond
                                                                condition=c_ast.BinaryOp(op='&&', left=temp_cond, right=c_ast.UnaryOp(op='!', expr=statement.cond))
						else:
							if type(element) is c_ast.While:
								temp_status,temp_cond = check_goto(element.stmt.block_items,label)
								if temp_status==True:
                                                                        status=True
                                                                        condition=temp_cond

				else:
					temp_status,temp_cond = check_goto_If(statement.iffalse,label)
					if temp_status==True:
                                                status=True
                                                #condition=temp_cond
                                                condition=c_ast.BinaryOp(op='&&', left=temp_cond, right=c_ast.UnaryOp(op='!', expr=statement.cond))
	return status,condition






#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label


def label_finder(statements,label):
	if statements is not None:
		flag_block1=check_label_block(statements,label)
		if flag_block1==True:
			return gotomoveout(statements,label)
		else:
			update_statements=[]
			if statements is not None:
				for statement in statements:
					if type(statement) is c_ast.If:
						update_statements.append(label_finder_if(statement,label))
					elif type(statement) is c_ast.While:
						update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=label_finder(statement.stmt.block_items,label))))
					else:
						update_statements.append(statement)
				return update_statements
			return statements
	return statements
				


#Finding Goto in a If Block to Call gotomovein
#Parameter pass statement 
#Label

def label_finder_if(statement,label):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if statement.iftrue.block_items is not None:
				new_iftrue=c_ast.Compound(block_items=label_finder(statement.iftrue.block_items,label))
			else:
				new_iftrue=statement.iftrue
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			if statement.iffalse.block_items is not None:
				new_iffalse=c_ast.Compound(block_items=label_finder(statement.iffalse.block_items,label))	
			else:
				new_iffalse=statement.iffalse
		elif type(statement.iffalse) is c_ast.If:
			new_iffalse=label_finder_if(statement.iffalse,label)
		else:
			new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond,iftrue=new_iftrue,iffalse=new_iffalse)






#Method to Move Goto Outside
#Parameter pass statement 
#Label


def gotomoveout(statements,label):
	flag_block1=check_label_block(statements,label)
	update_statements=[]
	condition=None
	if flag_block1==True:
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_block2,condition=check_goto_If(statement,label)
				flag_stmt2=check_goto_block_If(statement,label)
				if flag_block2==True and flag_stmt2==False:
					statement=gotomoveoutrec_if(statement,label)
			                update_statements.append(statement)
			                update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
				elif flag_block2==True and flag_stmt2==True:
					statement=getRidOfGoto(statement,label)
			                if statement is not None:
			                	update_statements.append(statement)
			                	update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			        else:
					update_statements.append(statement)
			
			elif type(statement) is c_ast.While:
				flag_block2,condition=check_goto(statement.stmt.block_items,label)
				flag_stmt2=check_goto_block(statement.stmt.block_items,label)
				if flag_block2==True and flag_stmt2==False:
					stmts=gotomoveoutrec(statement.stmt.block_items,label)
					stmts.append(c_ast.If(cond=condition, iftrue=c_ast.Break(), iffalse=None))
					statement=c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmts))
					update_statements.append(statement)
					update_statements.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
				elif flag_block2==True and flag_stmt2==True:
			                update_statements.append(statement)
			        else:
					update_statements.append(statement)
			                       
			else:
				update_statements.append(statement)
                                
		return update_statements



#Method to Move Goto Outside Recursive
#Parameter pass statement 
#Label

def gotomoveoutrec(statements,label):
	new_statements1=[]
	new_statements2=[]
	flag=False
	condition=None
	for statement in statements:
		if type(statement) is c_ast.If:
			flag_block2,condition_new=check_goto_If(statement,label)
			flag_stmt2=check_goto_block_If(statement,label)
			if condition_new is not None:
				condition=condition_new
			if flag_block2==True and flag_stmt2==False:
				statement=gotomoveoutrec_if(statement,label)
                        	new_statements1.append(statement)
                        	flag=True
			elif flag_block2==True and flag_stmt2==True:
				statement=getRidOfGoto(statement,label)
                                flag=True
                                if statement is not None:
                                	new_statements1.append(statement)
                        else:
                        	if flag==True:
					new_statements2.append(statement)
				else:
                        		new_statements1.append(statement)

		elif type(statement) is c_ast.While:
			flag_block2,condition_new=check_goto(statement.stmt.block_items,label)
			flag_stmt2=check_goto_block(statement.stmt.block_items,label)
			if condition_new is not None:
				condition=condition_new
			if flag_block2==True and flag_stmt2==False:
				stmts=gotomoveoutrec(statement.stmt.block_items,label)
				stmts.append(c_ast.If(cond=condition, iftrue=c_ast.Break(), iffalse=None))
				statement=c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmts))
				new_statements1.append(statement)
			elif flag_block2==True and flag_stmt2==True:
                                flag=True
                                new_statements1.append(statement)
                        else:
                        	if flag==True:
					new_statements2.append(statement)
				else:
                        		new_statements1.append(statement)
                       
                else:
                	if flag==True:
				new_statements2.append(statement)
			else:
                        	new_statements1.append(statement)
	if condition is not None:
                if len(new_statements2)>0:
                	new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
        	statements=new_statements1

        return statements



#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label
				
				
def gotomoveoutrec_if(statement,label):
	#print statement.show()
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
	                	status = True
		else:
		        if type(statement.iftrue) is c_ast.Compound and statement.iftrue.block_items is not None:
		        	flag_block2,condition=check_goto(statement.iftrue.block_items,label)
				flag_stmt2=check_goto_block(statement.iftrue.block_items,label)
				if flag_block2==True and flag_stmt2==False:
					statement.iftrue.block_items=gotomoveoutrec(statement.iftrue.block_items,label)
					statement.iftrue=c_ast.Compound(block_items=statement.iftrue.block_items)
				elif flag_block2==True and flag_stmt2==True:
					statement.iftrue=c_ast.Compound(block_items=statement.iftrue.block_items)
	                                                                
		if type(statement.iffalse) is c_ast.Label:
	        	if statement.iffalse.name==label:
	                	status = True
		else:
			if type(statement.iffalse) is c_ast.Compound and statement.iffalse.block_items is not None:
				flag_block2,condition=check_goto(statement.iffalse.block_items,label)
				flag_stmt2=check_goto_block(statement.iffalse.block_items,label)
				if flag_block2==True and flag_stmt2==False:
					statement.iffalse.block_items=gotomoveoutrec(statement.iffalse.block_items,label)
					statement.iffalse=c_ast.Compound(block_items=statement.iffalse.block_items)
				elif flag_block2==True and flag_stmt2==True:
					statement.iffalse=c_ast.Compound(block_items=statement.iffalse.block_items)
			else:
				if type(statement.iffalse) is c_ast.If: 
					gotomoveoutrec_if(statement.iffalse,label)
	#print statement.show()
	return c_ast.If(cond=statement.cond, iftrue=statement.iftrue, iffalse=statement.iffalse)
				



#Updating Each If Else for Goto
#Parameter pass statement 
#Label
		
	
def getRidOfGoto(statement,label):
	generator = c_generator.CGenerator()
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
	                	new_iftrue=None
		else:
		        if type(statement.iftrue) is c_ast.Compound:
		        	new_block=[]
				for stmt in statement.iftrue.block_items:
					if type(stmt) is c_ast.Goto:
						if stmt.name!=label:
							new_block.append(stmt)
					else:
						new_block.append(stmt)
				new_iftrue=c_ast.Compound(block_items=new_block)
                                     
		
		if type(statement.iffalse) is c_ast.Label:
	        	if statement.iffalse.name==label:
	                	new_iffalse=None
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=[]
				for stmt in statement.iffalse.block_items:
					if type(stmt) is c_ast.Goto:
						if stmt.name!=label:
							new_block.append(stmt)
					else:
						new_block.append(stmt)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=getRidOfGoto(statement.iffalse,label)
	if new_iftrue is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	else:
		return None





#Finding Goto in a Block to Call gotomovein
#Parameter pass block of statement 
#Label


def goto_finder(statements,label):
	flag_block1=check_goto_block_Sp(statements,label)
	if flag_block1==True:
		flag_block1=check_label_block_sp(statements,label)
		if flag_block1==True:
			return statements
		else:
			return gotomovein(statements,label)
	else:
		update_statements=[]
		for statement in statements:
			if type(statement) is c_ast.If:
				update_statements.append(goto_finder_if(statement,label))
			elif type(statement) is c_ast.While:
				update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=goto_finder(statement.stmt.block_items,label))))
			else:
				update_statements.append(statement)
		return update_statements


#Finding Goto in a If Block to Call gotomovein
#Parameter pass statement 
#Label

def goto_finder_if(statement,label):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement) is c_ast.If:
			if type(statement.iftrue) is c_ast.Compound:
				if statement.iftrue.block_items is not None:
					new_iftrue=c_ast.Compound(block_items=goto_finder(statement.iftrue.block_items,label))
				else:
					new_iftrue=statement.iftrue				
			else:
				new_iftrue=statement.iftrue
			if type(statement.iffalse) is c_ast.Compound:
				if statement.iffalse.block_items is not None:
					new_iffalse=c_ast.Compound(block_items=goto_finder(statement.iffalse.block_items,label))
				else:
					new_iffalse=statement.iffalse
			elif type(statement.iffalse) is c_ast.If:
				new_iffalse=goto_finder_if(statement.iffalse,label)
			else:
				new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond,iftrue=new_iftrue,iffalse=new_iffalse)




#Method to Move Goto Inside
#Parameter pass statement 
#Label

def gotomovein(statements,label):
	flag_block1=check_goto_block_Sp(statements,label)
	new_statements1=[]
	new_statements2=[]
	flag=False
	if flag_block1==True:
		flag_block1,condition=check_goto(statements,label)
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_stmt3=check_goto_block_If(statement,label)				
				flag_block2=check_label_If(statement,label)
				flag_stmt2=check_label_block_If(statement,label)
				if flag_stmt3==True:
					if flag_block2==True and flag_stmt2==True:
						new_statements1.append(statement)
					else:
						new_statement=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='go_'+label), rvalue=condition)
						new_variable['go_'+label]='go_'+label
						condition=c_ast.BinaryOp(op='>', left=c_ast.ID(name='go_'+label), right=c_ast.Constant(type='int', value='0'))
						new_statements1.append(new_statement)
						flag=True
				else:
					if flag_block2==True and flag_stmt2==False:
						flag=False
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
						new_statements1.append(updateIfBlock(statement,label,condition))

						new_statements2=[]
					else:
						if flag_block2==True and flag_stmt2==True:
							flag=False
							new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
							new_statements1.append(updateIfBlock(statement,label,condition))
							new_statements2=[]
						else:
							if flag==False:
								new_statements1.append(statement)
							else:
								new_statements2.append(statement)
			elif type(statement) is c_ast.While:
				flag_block2=check_label(statement.stmt.block_items,label)
				#flag_stmt2=check_label_block(statement.stmt.block_items,label)
				flag_stmt2=check_label_block_sp(statement.stmt.block_items,label)			
				if flag_block2==False and flag_stmt2==False:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				elif flag_block2==True and flag_stmt2==True:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				elif flag_block2==True and flag_stmt2==False:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					new_blocks=gotomoveinrec(new_blocks,label,condition)
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				else:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
			else:
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
		return new_statements1
	else:
		return statements



#Method to Move Goto Inside Recursive 
#Parameter pass statement 
#Label


def gotomoveinrec(statements,label,condition):
	flag_block1,condition=check_goto(statements,label)
	new_statements1=[]
	new_statements2=[]
	flag=False
	if flag_block1==True:
		for statement in statements:
			if type(statement) is c_ast.If:
				flag_stmt3=check_goto_block_If(statement,label)				
				flag_block2=check_label_If(statement,label)
				flag_stmt2=check_label_block_If(statement,label)
				if flag_stmt3==True:
					if flag_block2==True and flag_stmt2==True:
						new_statements1.append(statement)
					else:
						flag=True
				else:
					if flag_block2==True and flag_stmt2==False:
						flag=False
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
						new_statements1.append(updateIfBlock(statement,label,condition))

						new_statements2=[]
					else:
						if flag_block2==True and flag_stmt2==True:
							flag=False
							if len(new_statements2)>0:
								new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
							new_statements1.append(updateIfBlock(statement,label,condition))
							new_statements2=[]
						else:
							if flag==False:
								new_statements1.append(statement)
							else:
								new_statements2.append(statement)
			elif type(statement) is c_ast.While:
				flag_block2=check_label(statement.stmt.block_items,label)
				#flag_stmt2=check_label_block(statement.stmt.block_items,label)
				flag_stmt2=check_label_block_sp(statement.stmt.block_items,label)
				if flag_block2==False and flag_stmt2==False:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				elif flag_block2==True and flag_stmt2==True:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				elif flag_block2==True and flag_stmt2==False:
					if len(new_statements2)>0:
						new_statements1.append(c_ast.If(cond=c_ast.UnaryOp(op='!', expr=condition), iftrue=c_ast.Compound(block_items=new_statements2), iffalse=None))
					new_cond=c_ast.BinaryOp(op='||', left=condition, right=statement.cond)
					new_blocks=[]
					new_blocks.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.stmt.block_items:
						new_blocks.append(stmt)
					new_blocks.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='go_'+label) , rvalue= c_ast.Constant(type='int', value='0')))
					new_blocks=gotomoveinrec(new_blocks,label,condition)
					statement=c_ast.While(cond=new_cond, stmt=c_ast.Compound(block_items=new_blocks))
					flag=False
					new_statements2=[]
				else:
					statement=c_ast.While(cond=statement.cond, stmt=statement.stmt)
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
			else:
				if flag==False:
					new_statements1.append(statement)
				else:
					new_statements2.append(statement)
		return new_statements1
	else:
		return statements




#Updating Each If Else for Goto
#Parameter pass statement 
#Label

def updateIfBlock(statement,label,condition):
	new_iftrue=None
	new_iffalse=None
	new_condtion=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Goto:
			if statement.iftrue.name==label:
				new_block=[]
				new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
				new_block.append(statement.iftrue)
		        	new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				flag_stmt=check_label(statement.iftrue.block_items,label)
				flag_stmt_block=check_label_block_sp(statement.iftrue.block_items,label)
			        if flag_stmt==True:
			        	new_block=[]
			        	new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.iftrue.block_items:
						new_block.append(stmt)
					if flag_stmt_block==False:
						new_block=gotomoveinrec(new_block,label,condition)
					new_iftrue=c_ast.Compound(block_items=new_block)
				else:
					new_condtion=c_ast.BinaryOp(op='&&', left=c_ast.UnaryOp(op='!', expr=condition), right=statement.cond)
					new_iftrue=statement.iftrue
                         
			
		if type(statement.iffalse) is c_ast.Label:
			new_block=[]
			new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
			new_block.append(statement.iffalse)
		        new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				flag_stmt=check_label(statement.iffalse.block_items,label)
				flag_stmt_block=check_label_block_sp(statement.iffalse.block_items,label)
				if flag_stmt==True:
			        	new_block=[]
			        	new_block.append(c_ast.If(cond=condition, iftrue=c_ast.Goto(name=label), iffalse=None))
					for stmt in statement.iffalse.block_items:
						new_block.append(stmt)
					if flag_stmt_block==False:
						new_block=gotomoveinrec(new_block,label,condition)
					new_iffalse=c_ast.Compound(block_items=new_block)
				else:
					new_condtion=c_ast.BinaryOp(op='&&', left=c_ast.UnaryOp(op='!', expr=condition), right=statement.cond)
					new_iffalse=statement.iffalse
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=updateIfBlock(statement.iffalse,label,condition)
	if new_condtion is not None:
		return c_ast.If(cond=new_condtion, iftrue=new_iftrue, iffalse=new_iffalse)
	else:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	
	
	

def reOrganizeBreaks(statements,new_break_map):
	update_statement=[]
	if statements is not None:
		for statement in statements:
			if type(statement) is c_ast.If:
				statement=reOrganizeBreaksIf(statement,new_break_map)
				update_statement.append(statement)
			elif type(statement) is c_ast.Break:
				update_statement.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='do_break'+str(len(new_break_map.keys())+1)), rvalue=c_ast.Constant(type='int', value='1')))
				new_break_map['do_break'+str(len(new_break_map.keys())+1)]='do_break'+str(len(new_break_map.keys())+1)
				update_statement.append(statement)
			else:
				update_statement.append(statement)
		return update_statement
	else:
		return None


def reOrganizeBreaksIf(statement,new_break_map):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Break:
			new_block=[]
			new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='do_break'+str(len(new_break_map.keys())+1)), rvalue=c_ast.Constant(type='int', value='1')))
			new_break_map['do_break'+str(len(new_break_map.keys())+1)]='do_break'+str(len(new_break_map.keys())+1)
			new_block.append(statement.iftrue)
			new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				new_block=reOrganizeBreaks(statement.iftrue.block_items,new_break_map)
				new_iftrue=c_ast.Compound(block_items=new_block)
		
		if type(statement.iffalse) is c_ast.Break:
			new_block=[]
			new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='do_break'+str(len(new_break_map.keys())+1)), rvalue=c_ast.Constant(type='int', value='1')))
			new_break_map['do_break'+str(len(new_break_map.keys())+1)]='do_break'+str(len(new_break_map.keys())+1)
			new_block.append(statement.iffalse)
			new_iffalse=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=reOrganizeBreaks(statement.iffalse.block_items,new_break_map)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=reOrganizeBreaksIf(statement.iffalse,new_break_map)
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
		
		
		
def addingBreakVariables(statements,new_break_map):
	for variable in new_break_map.keys():
		global new_variable
		new_variable[variable]=variable
		new_block=[]
		new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=variable), rvalue=c_ast.Constant(type='int', value='0')))
		new_block.append(c_ast.Break())
		new_iftrue=c_ast.Compound(block_items=new_block)
		statements.append(c_ast.If(cond=c_ast.BinaryOp(op='==', left=c_ast.ID(name=variable), right=c_ast.Constant(type='int', value='1')), iftrue=new_iftrue, iffalse=None))
	return statements
	
	

def removeEmptyIfLoop(statements):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.If:
			statement=removeEmptyIfLoop_If(statement)
			if statement is not None:
				update_statements.append(statement)
		elif type(statement) is c_ast.While:
			new_block_items=removeEmptyIfLoop(statement.stmt.block_items)
			update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items)))
		else:
			if statement is not None:
				if type(statement) is not c_ast.EmptyStatement:
					update_statements.append(statement)
	return update_statements
			
			
			
def removeEmptyIfLoop_If(statement):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			if len(statement.iftrue.block_items)==0:
				new_iftrue=None
			else:
				new_block=removeEmptyIfLoop(statement.iftrue.block_items)
				if len(new_block)==0:
					new_iftrue=None
				else:
					new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.EmptyStatement:
				new_iftrue=None
			else:
				new_iftrue=statement.iftrue
				
		if type(statement.iffalse) is c_ast.Compound:
			if len(statement.iffalse.block_items)==0:
				new_iffalse=None
			else:
				new_block=removeEmptyIfLoop(statement.iffalse.block_items)
				if len(new_block)==0:
					new_iffalse=None 
				else:
					new_iffalse=c_ast.Compound(block_items=new_block) 
		elif type(statement.iffalse) is c_ast.If:
			result=removeEmptyIfLoop_If(statement.iffalse)
			if result is not None:
				new_iffalse=result
		else:
			if type(statement.iffalse) is c_ast.EmptyStatement:
				new_iftrue=None
			else:
				new_iffalse=statement.iffalse
	
	
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None

		
		
def returnReplacement(statements,end_label_map):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.If:
			statement=returnReplacementIf(statement,end_label_map)
			if statement is not None:
				update_statements.append(statement)
		elif type(statement) is c_ast.While:
			new_block_items=returnReplacement(statement.stmt.block_items,end_label_map)
			update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items)))
		elif type(statement) is c_ast.Return:
			if statement.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.expr))
				update_statements.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				update_statements.append(c_ast.Goto(name=label))
				end_label_map[label]=label
		elif type(statement) is c_ast.Label:
			update_statements.append(c_ast.Label(name=statement.name, stmt=None))
			if type(statement.stmt) is c_ast.Return:
				if statement.stmt.expr is not None:
					label='Label'+str(len(end_label_map.keys())+1)
					update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.stmt.expr))
					update_statements.append(c_ast.Goto(name=label))
					end_label_map[label]=label
				else:
					label='Label'+str(len(end_label_map.keys())+1)
					update_statements.append(c_ast.Goto(name=label))
					end_label_map[label]=label
			else:
				if statement.stmt is not None:
					update_statements.append(statement.stmt)
			
		else:
			update_statements.append(statement)
	return update_statements
	
	
	
	
	
	
def returnReplacementIf(statement,end_label_map):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Return:
			new_block=[]
			if statement.iftrue.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.iftrue.expr))
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			new_iftrue=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iftrue) is c_ast.Compound:
				new_block=returnReplacement(statement.iftrue.block_items,end_label_map)
				new_iftrue=c_ast.Compound(block_items=new_block)
			else:
                                new_iftrue=statement.iftrue
			
		if type(statement.iffalse) is c_ast.Return:
			new_block=[]
			if statement.iffalse.expr is not None:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='RET'), rvalue=statement.iffalse.expr))
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			else:
				label='Label'+str(len(end_label_map.keys())+1)
				new_block.append(c_ast.Goto(name=label))
				end_label_map[label]=label
			new_iffalse=c_ast.Compound(block_items=new_block)
		else:
			if type(statement.iffalse) is c_ast.Compound:
				new_block=returnReplacement(statement.iffalse.block_items,end_label_map)
				new_iffalse=c_ast.Compound(block_items=new_block)
			else:
				if type(statement.iffalse) is c_ast.If:
					new_iffalse=returnReplacementIf(statement.iffalse,end_label_map)
				else:
                                        new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)









"""
 
Goto removal Modules End 

"""


break_count=0

continue_count=0	
	


def getBreakStmt(statements,break_map):
	update_statement1=[]
	update_statement2=[]
	flag=False
	global break_count
	global continue_count
        global new_variable
	for statement in statements:
		if type(statement) is c_ast.If:
			if flag==False:
				break_map_temp={}
				statement=getBreakStmtIf(statement,break_map_temp)
				for e_break in break_map_temp.keys():
					break_map[e_break]=break_map_temp[e_break]
				update_statement1.append(statement)
				if len(break_map_temp.keys())>0:
					flag=True
			else:
				update_statement2.append(statement)
		elif type(statement) is c_ast.While:
			break_map_temp={}
			new_block_items1=getBreakStmt(statement.stmt.block_items,break_map_temp)
			new_block_items2=[]
			new_condtion=statement.cond
			if len(break_map_temp.keys())>0:
				for var_name in break_map_temp.keys():
                                        new_block_items2.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='0')))
					if break_map_temp[var_name]=='Break':
						temp_new_condition=c_ast.BinaryOp(op='&&', left=new_condtion, right=c_ast.BinaryOp(op='==', left=c_ast.ID(name=var_name), right=c_ast.Constant(type='int', value='0')))
						new_condtion=temp_new_condition
			
                        for item in new_block_items1:
                            new_block_items2.append(item)
			if flag==False:
				update_statement1.append(c_ast.While(cond=new_condtion, stmt=c_ast.Compound(block_items=new_block_items2)))
			else:
				update_statement2.append(c_ast.While(cond=new_condtion, stmt=c_ast.Compound(block_items=new_block_items2)))
		elif type(statement) is c_ast.Break:
                        break_count=break_count+1
                        var_name='break_'+str(break_count)+'_flag'
                        new_variable[var_name]=var_name
                        update_statement1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Break'
		elif type(statement) is c_ast.Continue:
		        continue_count=continue_count+1
		       	var_name='continue_'+str(continue_count)+'_flag'
		        new_variable[var_name]=var_name
		        update_statement1.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Continue'
		else:
			if flag==False:
				update_statement1.append(statement)
			else:
				update_statement2.append(statement)
	if flag==True:
		update_condition=None
		for var_name in break_map.keys():
			if update_condition is None:
				update_condition=c_ast.BinaryOp(op='==', left=c_ast.ID(name=var_name), right=c_ast.Constant(type='int', value='0'))
			else:
				update_condition=c_ast.BinaryOp(op='&&', left=update_condition, right=c_ast.BinaryOp(op='==', left=c_ast.ID(name=var_name), right=c_ast.Constant(type='int', value='0')))
		if len(update_statement2)>0:
			update_statement1.append(c_ast.If(cond=update_condition, iftrue=c_ast.Compound(block_items=update_statement2), iffalse=None))
		
		return getBreakStmt(update_statement1,break_map)
	else:
		return update_statement1
			
		




def getBreakStmtIf(statement,break_map):
	new_iftrue=None
	new_iffalse=None
	global break_count
	global new_variable
	global continue_count
	if type(statement) is c_ast.If:
			
		if type(statement.iftrue) is c_ast.Break:
                        new_block_items=[]
                        break_count=break_count+1
                        var_name='break_'+str(break_count)+'_flag'
                        new_variable[var_name]=var_name
                        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Break'
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		elif type(statement.iftrue) is c_ast.Continue:
		        new_block_items=[]
		        break_count=break_count+1
		        var_name='continue_'+str(continue_count)+'_flag'
		        new_variable[var_name]=var_name
		        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Continue'
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		elif type(statement.iftrue) is c_ast.Compound:
			new_block_items=getBreakStmt(statement.iftrue.block_items,break_map)
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		else:
			new_iftrue=statement.iftrue
			
		if type(statement.iffalse) is c_ast.Break:
                        new_block_items=[]
                        break_count=break_count+1
                        var_name='break_'+str(break_count)+'_flag'
                        new_variable[var_name]=var_name
                        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Break'
			new_iffalse=c_ast.Compound(block_items=new_block_items)
		elif type(statement.iffalse) is c_ast.Continue:
		        new_block_items=[]
		        continue_count=continue_count+1
		        var_name='continue_'+str(continue_count)+'_flag'
		        new_variable[var_name]=var_name
		        new_block_items.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var_name), rvalue=c_ast.Constant(type='int', value='1')))
			break_map[var_name]='Continue'
			new_iffalse=c_ast.Compound(block_items=new_block_items)	
		elif type(statement.iffalse) is c_ast.Compound:
			new_block_items=getBreakStmt(statement.iffalse.block_items,break_map)
			new_iffalse=c_ast.Compound(block_items=new_block_items)
		else:
			if type(statement.iffalse) is c_ast.If:
				new_iffalse=getBreakStmtIf(statement.iffalse,break_map)
			else:
				new_iffalse=statement.iffalse
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None
		
		


"""

#Program Class
#Plain Python object to store Information about Member Method of a Java Class 
"""
class programclass(object):
 	def __init__(self, filename, functionMap , variableMap, axiomeMap, witnessXmlMap):
        	self.filename = filename
        	self.functionMap = functionMap
        	self.variableMap = variableMap
        	self.axiomeMap = axiomeMap
        	self.witnessXmlMap = witnessXmlMap
        def getFilename(self):
        	return self.filename
        def getFunctionMap(self):
        	return self.functionMap
        def getVariableMap(self):
        	return self.variableMap
        def getAxiomeMap(self):
        	return self.axiomeMap
        def getWitnessXmlMap(self):
        	return self.witnessXmlMap
	def setFilename(self, filename):
	        self.filename=filename
	def setFunctionMap(self, functionMap):
		self.functionMap=functionMap
	def setVariableMap(self, variableMap):
		self.variableMap=variableMap
	def setAxiomeMap(self, axiomeMap):
		self.axiomeMap=axiomeMap
	def setWitnessXmlMap(self, witnessXmlMap):
		self.witnessXmlMap=witnessXmlMap


"""


#Function Substitution Modules


"""

def substituteFunBlock(statements,functionvarmap):
	update_statements=[]
	global new_variable
	for statement in statements:
		if type(statement) is c_ast.FuncCall:
			membermethod=functionvarmap[statement.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)

			for x in range(0, len(statement.args.exprs)):
				arg=statement.args.exprs
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
		
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
			        	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
			        else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
			
			for stmt in new_blocks:
				update_statements.append(stmt)
		elif type(statement) is c_ast.Assignment:
			new_statement,new_block=substituteFun(statement.rvalue,functionvarmap)
			if new_block is not None and len(new_block)>0:
				for stmt in new_block:
					update_statements.append(stmt)
			update_statements.append(c_ast.Assignment(op='=',lvalue=statement.lvalue,rvalue=new_statement))
		elif type(statement) is c_ast.While:
			statement.cond,new_block=substituteFun(statement.cond,functionvarmap)
			if new_block is not None and len(new_block)>0:
				for stmt in new_block:
					update_statements.append(stmt)
			temp_new_block=substituteFunBlock(statement.stmt.block_items,functionvarmap)
			for stmt in new_block:
				temp_new_block.append(stmt)
			update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=temp_new_block)))	
		elif type(statement) is c_ast.If:
			statement,new_block=substituteFunBlockIf(statement,functionvarmap)
			if new_block is not None and len(new_block)>0:
				for stmt in new_block:
					update_statements.append(stmt)
			update_statements.append(statement)
		else:
			update_statements.append(statement)
	return update_statements



def substituteFunBlockIf(statement,functionvarmap):
	new_iftrue=None
	new_iffalse=None
	update_statements=None
	if type(statement) is c_ast.If:
		statement.cond,new_block=substituteFun(statement.cond,functionvarmap)
		if new_block is not None and len(new_block)>0:
			update_statements=[]
			for stmt in new_block:
				update_statements.append(stmt)
		if type(statement.iftrue) is c_ast.Compound:
			new_iftrue=c_ast.Compound(block_items=substituteFunBlock(statement.iftrue.block_items,functionvarmap))
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			new_iffalse=c_ast.Compound(block_items=substituteFunBlock(statement.iffalse.block_items,functionvarmap))
		else:
			if type(statement.iffalse) is c_ast.If:
				statement.iffalse,new_block =substituteFunBlockIf(statement.iffalse,functionvarmap)
				if new_block is not None and len(new_block)>0:
					if update_statements is None:
						update_statements=[]
					for stmt in new_block:
						update_statements.append(stmt)
				new_iffalse=statement.iffalse
	return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse),update_statements



def substituteFun(statement,functionvarmap):
	new_block=None
	
	global new_variable
	
	if type(statement) is c_ast.ID:
                return c_ast.ID(name=statement.name),new_block
        elif type(statement) is c_ast.Constant:
                return c_ast.Constant(type='int',value=statement.value),new_block
        elif type(statement) is c_ast.FuncCall:
                update_statements=[]
 		membermethod=functionvarmap[statement.name.name]
		in_var_map=membermethod.getInputvar().keys()
		count=membermethod.getUsedCounter()
		count=count+1
		membermethod.setUsedCounter(count)
		for x in range(0, len(statement.args.exprs)):
                        arg=statement.args.exprs
			update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
		new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar())
		
		for x in membermethod.getInputvar():
			if membermethod.getInputvar()[x].getDimensions()>0:
				new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
			else:
                                new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
		for x in membermethod.getLocalvar():
			if membermethod.getLocalvar()[x].getDimensions()>0:
				new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
			else:
                                new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
		
		
		for stmt in new_blocks:
			update_statements.append(stmt)
 		
 		return c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+'result'),update_statements	
 	elif type(statement) is c_ast.BinaryOp:
 		if type(statement.left) is c_ast.ID and type(statement.right) is c_ast.ID:
 		
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right),new_block
 			
 		elif type(statement.left) is c_ast.ID and type(statement.right) is c_ast.BinaryOp:
                                               
                        stmt_right,new_block=substituteFun(statement.right,functionvarmap)

 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=stmt_right),new_block
 			
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.ID:
 			
                        stmt_left,new_block=substituteFun(statement.left,functionvarmap)
                        
 			return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=statement.right),new_block
 			
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.Constant:
 		
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right),new_block
 			
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.ID:

 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right),new_block
 			
 		elif type(statement.left) is c_ast.ID and type(statement.right) is c_ast.Constant:
 		
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right),new_block
 			
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.BinaryOp:

                        stmt_right,new_block=substituteFun(statement.right,functionvarmap)
                        
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=stmt_right),new_block
 			
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.Constant:

                        stmt_left,new_block=substituteFun(statement.left,functionvarmap)
 		
 			return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=statement.right),new_block
 			
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.BinaryOp:

                        stmt_left,new_block1=substituteFun(statement.left,functionvarmap)

                        stmt_right,new_block2=substituteFun(statement.right,functionvarmap)

                        if new_block1 is not None and new_block2 is None:
 		
                                return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=stmt_right),new_block1

                        elif new_block1 is None and new_block2 is not None:

                                return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=stmt_right),new_block2
                        else:
                                new_block=[]
                                for stmt in new_blocks1:
                                        new_block.append(stmt)
                                for stmt in new_blocks2:
                                        new_block.append(stmt)
                                return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=stmt_right),new_block
 		
  		elif type(statement.left) is c_ast.FuncCall and type(statement.right) is c_ast.BinaryOp:
 		 	update_statements=[]
		 	membermethod=functionvarmap[statement.left.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.left.args.exprs)):
				arg=statement.left.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			for stmt in new_blocks:
				update_statements.append(stmt)
				
				
				
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
					
			
			
			
			
			stmt_right,new_block1=substituteFun(statement.right,functionvarmap)
			if new_block1 is not None:
				for stmt in new_block1:
					update_statements.append(stmt)
				
 			return c_ast.BinaryOp(op=statement.op,left=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET'), right=stmt_right),update_statements			
 		
 		
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.FuncCall:
 		 	update_statements=[]
		 	stmt_left,new_block1=substituteFun(statement.left,functionvarmap)
		 	if new_block1 is not None:
		 		for stmt in new_block1:
					update_statements.append(stmt)
		 	membermethod=functionvarmap[statement.right.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.right.args.exprs)):
				arg=statement.right.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
					
			
			for stmt in new_blocks:
				update_statements.append(stmt)
 			return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET')),update_statements	
 			
 		elif type(statement.left) is c_ast.ID and type(statement.right) is c_ast.FuncCall:
 			update_statements=[]
 			membermethod=functionvarmap[statement.right.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.right.args.exprs)):
				arg=statement.right.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
								
			
			for stmt in new_blocks:
				update_statements.append(stmt)
 		
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET')),update_statements	
 		
 		elif type(statement.left) is c_ast.FuncCall and type(statement.right) is c_ast.ID :
			update_statements=[]
		 	membermethod=functionvarmap[statement.left.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.left.args.exprs)):
				arg=statement.left.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
					
			
			for stmt in new_blocks:
				update_statements.append(stmt)
		 		
 			return c_ast.BinaryOp(op=statement.op,left=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET'), right=statement.right),update_statements	
 		
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.FuncCall:
		 	update_statements=[]
		 	membermethod=functionvarmap[statement.right.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.right.args.exprs)):
				arg=statement.right.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
					
			
			for stmt in new_blocks:
				update_statements.append(stmt)
		 		
		 	return c_ast.BinaryOp(op=statement.op,left=statement.left, right=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET')),update_statements	
		 		
		elif type(statement.left) is c_ast.FuncCall and type(statement.right) is c_ast.Constant :
			update_statements=[]
			membermethod=functionvarmap[statement.left.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.left.args.exprs)):
				arg=statement.left.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
					
			
			for stmt in new_blocks:
				update_statements.append(stmt)
				 		
 			return c_ast.BinaryOp(op=statement.op,left=c_ast.ID(name='t_'+str(count)+'_RET'), right=statement.right),update_statements	
 		
 		elif type(statement.left) is c_ast.FuncCall and type(statement.right) is c_ast.FuncCall:
		 	update_statements=[]
		 	membermethod=functionvarmap[statement.left.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.left.args.exprs)):
				arg=statement.left.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			
			
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
					
			
			for stmt in new_blocks:
				update_statements.append(stmt)
		 	
		 	stmt_left=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET')
		 	
		 	membermethod=functionvarmap[statement.right.name.name]
			in_var_map=membermethod.getInputvar().keys()
			count=membermethod.getUsedCounter()
			count=count+1
			membermethod.setUsedCounter(count)
			for x in range(0, len(statement.right.args.exprs)):
				arg=statement.right.args.exprs
				#update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+arg[x].name),rvalue=c_ast.ID(name=in_var_map[x])))
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+in_var_map[x]),rvalue=c_ast.ID(name=arg[x].name)))
			
			
			
			new_blocks=reconstructStmtBlock(membermethod.getBody().block_items,count,membermethod.getLocalvar(),membermethod.getInputvar(),membermethod.getSerialNo())
			
			
			for x in membermethod.getInputvar():
				if membermethod.getInputvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getInputvar()[x].getVariableType()
				
			for x in membermethod.getLocalvar():
				if membermethod.getLocalvar()[x].getDimensions()>0:
					new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]='array'
				else:
                                	new_variable['f'+str(membermethod.getSerialNo())+'_'+str(count)+'_'+x]=membermethod.getLocalvar()[x].getVariableType()
						
		
		
			for stmt in new_blocks:
				update_statements.append(stmt)
		 	
		 	stmt_right=c_ast.ID(name='f'+str(membermethod.getSerialNo())+'_'+str(count)+'_RET')
		 	
		 	return c_ast.BinaryOp(op=statement.op,left=stmt_left, right=stmt_right),update_statements	
	
 		else:
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right),new_block
 	return None




    		

def reconstructStmtBlock(statements,count,var_map,in_var_map,fun_count):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Assignment:
			if type(statement.lvalue) is c_ast.ID:
				if statement.lvalue.name in var_map.keys() or statement.lvalue.name in in_var_map.keys():
					update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='f'+str(fun_count)+'_'+str(count)+'_'+statement.lvalue.name), rvalue=reconstructStmt(statement.rvalue,count,var_map,in_var_map,fun_count)))
				else:
					update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=statement.lvalue.name), rvalue=reconstructStmt(statement.rvalue,count,var_map,in_var_map,fun_count)))
			else:
				update_statements.append(c_ast.Assignment(op='=', lvalue=statement.lvalue, rvalue=reconstructStmt(statement.rvalue,count,var_map,in_var_map)))
		elif type(statement) is c_ast.While:
			update_statements.append(reconstructStmt(c_ast.While(cond=reconstructStmt(statement.cond,count,var_map,in_var_map,fun_count),stmt=c_ast.Compound(block_items=reconstructStmtBlock(statement.cond.block_items,count,var_map,in_var_map,fun_count)))))
		elif type(statement) is c_ast.If:
			update_statements.append(reconstructStmtIf(statement,count,var_map,in_var_map,fun_count))
		else:
			if type(statement) is c_ast.FuncCall:
				update_statements.append(statement)
			else:
                                if type(statement) is c_ast.Decl:
                                        var_type=None
                                        initial_value=None
                                        for child in statement.children():
                                                if type(child[1].type) is c_ast.IdentifierType:
                                                        var_type=child[1].type.names[0]
                                                else:
                                                        initial_value=child[1]
                                        if initial_value is not None:
                                        	if statement.name in var_map.keys() or statement.name in in_var_map.keys():
                                        		update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='f'+str(fun_count)+'_'+str(count)+'_'+statement.name), rvalue=initial_value))
                                        	else:
                                                	update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name=statement.name), rvalue=initial_value))
                                else:
                                        update_statements.append(statement)
	return update_statements





def reconstructStmtIf(statement,count,var_map,in_var_map,fun_count):
	new_iftrue=None
	new_iffalse=None
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Compound:
			new_iftrue=c_ast.Compound(block_items=reconstructStmtBlock(statement.iftrue.block_items,count,var_map,in_var_map,fun_count))
		else:
			new_iftrue=statement.iftrue
		if type(statement.iffalse) is c_ast.Compound:
			new_iffalse=c_ast.Compound(block_items=reconstructStmtBlock(statement.iffalse.block_items,count,var_map,in_var_map,fun_count))
		else:
			if type(statement.iffalse) is c_ast.If:
				new_iffalse=reconstructStmtIf(statement.iffalse,count,var_map,in_var_map)
	return c_ast.If(cond==reconstructStmt(statement.cond,count,var_map,in_var_map,fun_count), iftrue=new_iftrue, iffalse=new_iffalse)






def reconstructStmt(statement,count,var_map,in_var_map,fun_count):
	if type(statement) is c_ast.ID:
		if statement.name in var_map.keys() or statement.name in in_var_map.keys():
			new_ID='f'+str(fun_count)+'_'+str(count)+'_'+statement.name
			return c_ast.ID(name=new_ID)
		else:
			return c_ast.ID(name=statement.name)
 	elif type(statement) is c_ast.BinaryOp:
 		if type(statement.left) is c_ast.ID and type(statement.right) is c_ast.ID:
 			stmt_left=None
 			stmt_right=None
 			
 			if statement.left.name in var_map.keys() or statement.left.name in in_var_map.keys():
 				stmt_left='f'+str(fun_count)+'_'+str(count)+'_'+statement.left.name
 			else:
 				stmt_left=statement.left.name
 				
 			if statement.right.name in var_map.keys() or statement.right.name in in_var_map.keys():
				stmt_right='f'+str(fun_count)+'_'+str(count)+'_'+statement.right.name
			else:
 				stmt_right=statement.right.name
 				
 			return c_ast.BinaryOp(op=statement.op,left=c_ast.ID(name=stmt_left), right=c_ast.ID(name=stmt_right))
 		elif type(statement.left) is c_ast.ID and type(statement.right) is c_ast.BinaryOp:
 			stmt_left=None
 			
 			if statement.left.name in var_map.keys() or statement.left.name in in_var_map.keys():
				stmt_left='f'+str(fun_count)+'_'+str(count)+'_'+statement.left.name
			else:
 				stmt_left=statement.left.name
 				
 			return c_ast.BinaryOp(op=statement.op,left=c_ast.ID(name=stmt_left), right=reconstructStmt(statement.right,count,var_map,in_var_map,fun_count))
 			
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.ID:
 			stmt_right=None
 			
 			if statement.right.name in var_map.keys() or statement.right.name in in_var_map.keys():
				stmt_right='f'+str(fun_count)+'_'+str(count)+statement.right.name
			else:
 				stmt_right=statement.right.name
 			
 			return c_ast.BinaryOp(op=statement.op,left=reconstructStmt(statement.left,count,var_map,in_var_map,fun_count), right=c_ast.ID(name=stmt_right))
 			
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.Constant:
 		
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right)
 			
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.ID:
 			stmt_right=None
  			
			if statement.right.name in var_map.keys() or statement.right.name in in_var_map.keys():
				stmt_right='f'+str(fun_count)+'_'+str(count)+'_'+statement.right.name
			else:
 				stmt_right=statement.right.name
 				
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=c_ast.ID(name=stmt_right))
 			
 		elif type(statement.left) is c_ast.ID and type(statement.right) is c_ast.Constant:
 			stmt_left=None
 			
 		 	if statement.left.name in var_map.keys() or statement.left.name in in_var_map.keys():
				stmt_left='f'+str(fun_count)+'_'+str(count)+'_'+statement.left.name
			else:
 				stmt_left=statement.left.name
 				
 			return c_ast.BinaryOp(op=statement.op,left=c_ast.ID(name=stmt_left), right=statement.right)
 		elif type(statement.left) is c_ast.Constant and type(statement.right) is c_ast.BinaryOp:
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=reconstructStmt(statement.right,count,var_map,in_var_map,fun_count))
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.Constant:
 			return c_ast.BinaryOp(op=statement.op,left=reconstructStmt(statement.left,count,var_map,in_var_map,fun_count), right=statement.right)
 		elif type(statement.left) is c_ast.BinaryOp and type(statement.right) is c_ast.BinaryOp:
 			return c_ast.BinaryOp(op=statement.op,left=reconstructStmt(statement.left,count,var_map,in_var_map,fun_count), right=reconstructStmt(statement.right,count,var_map,in_var_map,fun_count))
 		else:
 			return c_ast.BinaryOp(op=statement.op,left=statement.left, right=statement.right)
 	else:
 		return statement
 	return None
	







#
#Reconstruct Program by Removing assert,assume,error
#

def reconstructPreDefinedFun(statements):
	global fail_count
	global error_count
	global assume_count
	global assert_count
	global new_variable
	statements=getPreDefinedFun(statements)
    	update_statements=[]
    	for var in new_variable.keys():
    		temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
    		update_statements.append(temp)
    	for statement in statements:
    		update_statements.append(statement)
    	new_variable={}
    	return update_statements





def getPreDefinedFun(statements):
	update_statements=[]
	global fail_count
	global error_count
	global assume_count
	global assert_count
	global new_variable
	for statement in statements:
		if type(statement) is c_ast.If:
			stmt=getPreDefinedFunIf(statement)
			if stmt is not None:
				update_statements.append(stmt)
		elif type(statement) is c_ast.While:
			new_block_items1=getPreDefinedFun(statement.stmt.block_items)
			update_statements.append(c_ast.While(cond=statement.cond, stmt=c_ast.Compound(block_items=new_block_items1)))
		elif type(statement) is c_ast.Label:
			if statement.name=='ERROR':
				fail_count=fail_count+1
				update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1')))
				new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
				
			else:
				update_statements.append(statement)
		elif type(statement) is c_ast.FuncCall:
			parameters=[]
			if statement.args is not None:
				for param in statement.args.exprs:
					if type(param) is c_ast.ID:
						parameters.append(param)
					elif type(param) is c_ast.Constant:
						parameters.append(param)
					elif type(param) is c_ast.BinaryOp:
						parameters.append(param)
					elif type(param) is c_ast.FuncCall:
						parameters.append(param)
					else:
						parameters.append(param)
			if statement.name.name=='__VERIFIER_assert':
				new_statement=None
				for parameter in parameters:
					if new_statement is None:
						assert_count=assert_count+1
						status,parameter=modificationOfCondition(parameter)
						if status==True:
							parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
						
						new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter)
						new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
					else:
						assert_count=assert_count+1
						status,stmt=modificationOfCondition(parameter)
						if status==True:
							parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
						new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='PROVE'+str(assert_count)), rvalue=parameter), right=new_statement)
						new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
				update_statements.append(new_statement)
			elif statement.name.name=='__VERIFIER_assume':
				new_statement=None
				for parameter in parameters:
					if new_statement is None:
						assume_count=assume_count+1
						new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter)
						new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
					else:
						assume_count=assume_count+1
						new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter), right=new_statement)
						new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
				update_statements.append(new_statement)
			else:
				update_statements.append(statement)
		
		else:
			update_statements.append(statement)
	return update_statements
	
#
#Reconstruct Program by Removing assert,assume,error
#

def getPreDefinedFunIf(statement):
	new_iftrue=None
	new_iffalse=None
	global fail_count
	global error_count
	global assume_count
	global assert_count
	global new_variable
	if type(statement) is c_ast.If:
		if type(statement.iftrue) is c_ast.Label:
			if statement.iftrue.name=='ERROR':
				fail_count=fail_count+1
				new_iftrue=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1'))
				new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
			elif type(statement.iftrue) is c_ast.FuncCall:
				parameters=[]
				if statement.iftrue.args is not None:
					for param in statement.iftrue.args.exprs:
						if type(param) is c_ast.ID:
							parameters.append(param)
						elif type(param) is c_ast.Constant:
							parameters.append(param)
						elif type(param) is c_ast.BinaryOp:
							parameters.append(param)
						elif type(param) is c_ast.FuncCall:
							parameters.append(param)
						else:
							parameters.append(param)
				if statement.name.name=='__VERIFIER_assert':
					new_statement=None
					for parameter in parameters:
						if new_statement is None:
							assert_count=assert_count+1
							status,parameter=modificationOfCondition(parameter)
							if status==True:
								parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
							new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter)
							new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
						else:
							assert_count=assert_count+1
							status,parameter=modificationOfCondition(parameter)
							if status==True:
								parameter=c_ast.BinaryOp(op='>',left=parameter,right=c_ast.Constant(type='int', value='0'))
							new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter), right=new_statement)
							new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
					new_iftrue=new_statement
				elif statement.name.name=='__VERIFIER_assume':
					new_statement=None
					for parameter in parameters:
						if new_statement is None:
							assume_count=assume_count+1
							new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter)
							new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
						else:
							assume_count=assume_count+1
							new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter), right=new_statement)
							new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
					new_iftrue=new_statement
				else:
					new_iftrue=statement.iftrue
			else:
				new_iftrue=statement.iftrue
		elif type(statement.iftrue) is c_ast.Compound:
			new_block_items=getPreDefinedFun(statement.iftrue.block_items)
			new_iftrue=c_ast.Compound(block_items=new_block_items)
		else:
			
			new_iftrue=statement.iftrue
			
		if type(statement.iffalse) is c_ast.Label:
			if statement.iffalse.name=='ERROR':
				fail_count=fail_count+1
				new_iftrue=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(fail_count)+'_'+'FAILED'), rvalue=c_ast.Constant(type='int', value='1'))
				new_variable['_'+str(fail_count)+'_'+'FAILED']='_'+str(fail_count)+'_'+'FAILED'
			elif type(statement.iffalse) is c_ast.FuncCall:
				parameters=[]
				if statement.iffalse.args is not None:
					for param in statement.iftrue.args.exprs:
						if type(param) is c_ast.ID:
							parameters.append(param)
						elif type(param) is c_ast.Constant:
							parameters.append(param)
						elif type(param) is c_ast.BinaryOp:
							parameters.append(param)
					if statement.name.name=='__VERIFIER_assert':
						new_statement=None
						for parameter in parameters:
							if new_statement is None:
								assert_count=assert_count+1
								new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter)
								new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
							else:
								assert_count=assert_count+1
								new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assert_count)+'_'+'PROVE'), rvalue=parameter), right=new_statement)
								new_variable['_'+str(assert_count)+'_'+'PROVE']='_'+str(assert_count)+'_'+'PROVE'
						new_iffalse=new_statement
					elif statement.name.name=='__VERIFIER_assume':
						new_statement=None
						for parameter in parameters:
							if new_statement is None:
								assume_count=assume_count+1
								new_statement= c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter)
								new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
							else:
								assume_count=assume_count+1
								new_statement=c_ast.BinaryOp(op='&&', left=c_ast.Assignment(op='=', lvalue=c_ast.ID(name='_'+str(assume_count)+'_'+'ASSUME'), rvalue=parameter), right=new_statement)
								new_variable['_'+str(assume_count)+'_'+'ASSUME']='_'+str(assume_count)+'_'+'ASSUME'
						new_iffalse=new_statement
					else:
						new_iffalse=statement.iffalse
			else:
				new_iffalse=statement.iffalse
		elif type(statement.iffalse) is c_ast.Compound:
			new_block_items=getPreDefinedFun(statement.iffalse.block_items)
			new_iffalse=c_ast.Compound(block_items=new_block_items)
		else:
			if type(statement.iffalse) is c_ast.If:
				new_iffalse=getPreDefinedFunIf(statement.iffalse)
			else:
				new_iffalse=statement.iffalse
				
	if new_iftrue is not None and new_iffalse is None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
	elif new_iftrue is not None and new_iffalse is not None:
		return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
		return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
	elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
		return new_iffalse
	else:
		return None


#
#Convert Initiation to assignments   
#

def construct_program(statements):
    update_statements=[]
    for statement in statements:
    	if type(statement) is c_ast.Decl:
    		if type(statement.type) is c_ast.ArrayDecl:
                        if statement.init is not None:
                        	program=''                        	
			        d_list=[]
			        a_list=[]
			        
			        if statement.type.dim is None:
			        	d_list_update,a_list_update=getDimesnion4Init(statement.init)
			        	for x1 in d_list_update:
			        		d_list.append('initial_value'+x1)
			        	for x1 in a_list_update:
			        		a_list.append(x1)
			        else:
			        	for x in range(0, int(statement.type.dim.value)):
			        		d_list.append('initial_value.exprs['+str(x)+']')
			                	a_list.append('['+str(x)+']') 
			        	d_list,a_list=getDimesnion(statement.type,d_list,a_list)
                        	initial_value=statement.init
                        	for x1 in range(0, len(d_list)):
                            		program=program+statement.name+a_list[x1]+'='+str(eval(d_list[x1]+'.value'))+';'
                        	
                        	program='int main{'+program+'}'
                        	parser = c_parser.CParser()
                        	ast1 = parser.parse(program)
                        	function_body = ast1.ext[0].body                        	
                        	statement.init=None
                        	update_statements.append(statement)
                        	for new_statement in function_body.block_items:
                        		update_statements.append(new_statement)
                        else:
                        	update_statements.append(statement)
                        
                else:
                	update_statements.append(statement)
        else:
        	update_statements.append(statement)
    return update_statements


def getDimesnion(statement,d_list,a_list):
    if type(statement.type) is c_ast.ArrayDecl:
        d_list_update=[]
        a_list_update=[]
        for x1 in range(0, len(d_list)):
            for x2 in range(0, int(statement.type.dim.value)):
                d_list_update.append(d_list[x1]+'.exprs['+str(x2)+']')
                a_list_update.append(a_list[x1]+'['+str(x2)+']')
        return getDimesnion(statement.type,d_list_update,a_list_update)
    else:
        return d_list,a_list
        

def getDimesnion4Init(statement):
	d_list_update=[]
       	a_list_update=[]
	if type(statement) is c_ast.InitList:
		count=0
		for x in statement.exprs:
			if type(x) is c_ast.InitList:
				new_d_list_update,new_a_list_update=getDimesnion4Init(x)
				for x1 in new_d_list_update:
					d_list_update.append('.exprs['+str(count)+']'+x1)
				for x1 in new_a_list_update:
					a_list_update.append('['+str(count)+']'+x1)
			else:
				d_list_update.append('.exprs['+str(count)+']')
				a_list_update.append('['+str(count)+']')
			count=count+1
	return d_list_update,a_list_update

			


#
#Remove C and C++ comments
# 
#

text='a=a+1;// test test'

def comment_remover(text):
    text=text.replace('extern void __VERIFIER_error() __attribute__ ((__noreturn__));','')
    def replacer(match):
        s = match.group(0)
        if s.startswith('/'):
            return " " # note: a space and not an empty string
        else:
            return s
    pattern = regex.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        regex.DOTALL | regex.MULTILINE
    )
    return regex.sub(pattern, replacer, text)
    

#
#text='#include "assert.h"'
#

def include_remover(text):
	status=False
	find=regex.compile(r'\#(\s+)include|\#include')
	group = find.search(text)
	if group is not None:
		status=True
	return status
    
#
#content='   /**   * Constructor, which takes the output of a toStringFull() and converts it back   * into an Id.  Should not normally be used.   *   * @param hex The hexadeciaml representation from the toStringFull()   *//*  public static Id build(char[] chars, int offset, int length) {    int[] array = new int[nlen];        for (int i=0; i<nlen; i++)       for (int j=0; j<8; j++)         array[nlen-1-i] =(array[nlen-1-i] << 4) | trans(chars[offset + 8*i + j]);        return build(array);  }  */int main() {  int offset, length, nlen = __VERIFIER_nondet_int();  i'
#
def comment_remover_file(content):
	new_content=content.replace('/*','\n/*').replace('*/','\n*/')        
	lines = new_content.splitlines()
	new_lines=[]
	for line in lines:
		if line is not None and include_remover( line )==False:
			new_lines.append(comment_remover(line))
	content = ''.join(new_lines)
	content=comment_remover_update(content)
	return content


def comment_remover_update(text):
	for x in regex.findall(r'("[^\n]*"(?!\\))|(//[^\n]*$|/(?!\\)\*[\s\S]*?\*(?!\\)/)',text,8):text=text.replace(x[1],'')
 	return text


#
#Pre-Processig of Pre-Processor
#content='#include "assert.h #define LIMIT 1000000 #define LIMIT1 1000000'
#

def preProcessorHandling(content):
	new_content=content.replace(';',';\n').replace('}','}\n').replace('#','\n#').replace('int','\nint').replace('void','\nvoid').replace('void','\nvoid').replace('extern','\nextern ').replace('unsigned','\nunsigned').replace('Char','\nChar')   
	lines = new_content.splitlines()
	new_lines=[]
	defineMap={}
	for line in lines:
		definematch = regex.match("#define\\s+(\\w+)\\s+(.*)",line)
		if definematch:
			#deal with define statements by saving it in a dict
			#definedict[match.group(1)] = definedict[match.group(2)]
			defineMap[definematch.group(1)]=str(simplify(definematch.group(2)))
			new_lines.append(line)
	for line in new_lines:
		content=content.replace(line,'')
	return content,defineMap







#text='_PROVE'

def isAssertion(text):
	status=False
	find=regex.compile(r'\_PROVE')
	#find=regex.compile(r'(.+?)PROVE1')
	group = find.search(text)
	if group is not None:
		status=True
	return status


def getAssertAssume(f,o,a,cm):
	new_o={}
	new_a=[]
	assert_list=[]
	assume_list=[]
	for x in o:
		if x.find('_PROVE')>0:
        		assert_list.append(o[x])
                elif x.find('_ASSUME')>0:
        		assume_list.append(o[x])
        	else:
        		new_o[x]=o[x]
        
        for x in a:
        	if x[0]=='i1':
        		if x[3][0].find('_PROVE')>0:
        			#for var in cm.keys():
        			#	x[4]=expr_sub(x[4],cm[var],var)
        			assert_list.append(x)
        		elif x[3][0].find('_ASSUME')>0:
                                assume_list.append(x)
        		else:
        			new_a.append(x)
        	elif x[0]=='i0':
        		if x[2][0].find('_PROVE')>0:
        			assert_list.append(x)
        		elif x[2][0].find('_ASSUME')>0:
                                assume_list.append(x)
        		else:
        			new_a.append(x)
        	else:
			new_a.append(x)
      	        	
        return f,new_o,new_a,extractAssert(assert_list,cm),extractAssume(assume_list,cm)
        



        
def extractAssert(assert_list,cm):
	update_assert_stmts=[]
	for stmt in assert_list:
		if stmt[0]=='e':
			update_stmt=[]
			update_stmt.append('s0')
			update_stmt.append(stmt[2])
			key=wff2string1(update_stmt)
			for iteam in cm:
				key=key.replace(cm[iteam],iteam+'+1')
			flag=False
			for temp_stmt in assert_list:
				if temp_stmt[0]=='i1':
					lefthandstmt=expr2string1(temp_stmt[3])
					if 'and' not in str(key) and 'or' not in str(key):
						if simplify(key)==simplify(lefthandstmt):
							flag=True
			if flag==False:
				if update_stmt[0]=='s0':
					temp=expr2string1(update_stmt[1])
					if '<' in temp or '>' in temp or '=' in temp:
						update_assert_stmts.append(update_stmt)
				else:
					update_assert_stmts.append(update_stmt)
		else:
			if stmt[0]=='s0':
				temp=expr2string1(stmt[1])
				if '<' in temp or '>' in temp or '=' in temp:
					update_assert_stmts.append(stmt)
			else:
				update_assert_stmts.append(stmt)
			
	return update_assert_stmts
	


def extractAssume(assume_list,cm):
	update_assume_stmts=[]
	for stmt in assume_list:
		if stmt[0]=='e':
			update_stmt=[]
			update_stmt.append('s0')
			update_stmt.append(stmt[2])
			key=wff2string1(update_stmt)
			for iteam in cm:
				key=key.replace(cm[iteam],iteam+'+1')
			flag=False
			for temp_stmt in assume_list:
				if temp_stmt[0]=='i1':
					lefthandstmt=expr2string1(temp_stmt[3])
					if 'and' not in str(key) and 'or' not in str(key):
						if simplify(key)==simplify(lefthandstmt):
							flag=True
			if flag==False:
				if update_stmt[0]=='s0':
					temp=expr2string1(update_stmt[1])
					if '<' in temp or '>' in temp or '=' in temp:
						update_assume_stmts.append(update_stmt)
				else:
					update_assume_stmts.append(update_stmt)
		else:
			if stmt[0]=='s0':
				temp=expr2string1(stmt[1])
				if '<' in temp or '>' in temp or '=' in temp:
					update_assume_stmts.append(stmt)
			else:
				update_assume_stmts.append(stmt)
	return update_assume_stmts
	

        
        

#
#Module to handle pointer 
#


def handlingPointer(statements):
	update_statements=[]
	for statement in statements:
    		if type(statement) is c_ast.Decl:
    			dimesnsion=0
    			d_map={}
    			flag_pointer=False
    			type_name,dimesnsion,flag_pointer=getTypeNameDimension(statement,dimesnsion,flag_pointer)
    			if flag_pointer==True:
    				getDimension4mMalloc(statement,d_map)
       				temp_program=type_name+' '+statement.name
    				for x in range(0, len(d_map.keys())):
    					if 'parameter'+str(x) in d_map.keys():
    						temp_program+='['+d_map['parameter'+str(x)]+']'
    				temp_program+=';'
    				parser = c_parser.CParser()
    				print '@@@@@@@'
    				print temp_program
    				print '@@@@@@@'
    				ast = parser.parse(temp_program)
    				update_statements.append(ast.ext[0])
    			else:
    				update_statements.append(statement)
    		else:
    			update_statements.append(statement)
    	return update_statements



def getTypeNameDimension(statement,dimesnsion,flag_pointer):
	if type(statement.type) is c_ast.PtrDecl:
		dimesnsion=dimesnsion+1;
		flag_pointer=True
		return getTypeNameDimension(statement.type,dimesnsion,flag_pointer)
	elif type(statement.type) is c_ast.ArrayDecl:
		dimesnsion=dimesnsion+1;
		return getTypeNameDimension(statement.type,dimesnsion,flag_pointer)
	else:
		if type(statement.type) is c_ast.TypeDecl:
			if type(statement.type.type) is c_ast.IdentifierType:
				if len(statement.type.type.names)>1:
					return statement.type.type.names[1],dimesnsion,flag_pointer
				else:
					return statement.type.type.names[0],dimesnsion,flag_pointer
				

def getDimension4mMalloc(statement,d_map):
	for child in statement.children():
		if type(child[1]) is c_ast.FuncCall:
			for param in child[1].args.exprs:
				extractDimesion(param,d_map)
		else:
			getDimension4mMalloc(child[1],d_map)


def extractDimesion(param,d_map):
	if type(param) is c_ast.BinaryOp:
		if type(param.left) is c_ast.ID and  type(param.right) is c_ast.UnaryOp:
			d_map['parameter'+str(len(d_map.keys()))]=param.left.name
		elif type(param.right) is c_ast.ID and  type(param.left) is c_ast.UnaryOp:
			d_map['parameter'+str(len(d_map.keys()))]=param.right.name
		elif type(param.left) is c_ast.ID and  type(param.right) is c_ast.BinaryOp:
			d_map['parameter'+str(len(d_map.keys()))]=param.left.name
		elif type(param.right) is c_ast.ID and  type(param.left) is c_ast.BinaryOp:
			d_map['parameter'+str(len(d_map.keys()))]=param.right.name
		elif type(param.right) is c_ast.BinaryOp and  type(param.left) is c_ast.BinaryOp:
			extractDimesion(param.right,d_map)
			extractDimesion(param.left,d_map)


def pointerToArray(statement):
	if type(statement) is c_ast.Decl:
    		dimesnsion=0
    		d_map={}
    		flag_pointer=False
    		type_name,dimesnsion,flag_pointer=getTypeNameDimension(statement,dimesnsion,flag_pointer)
    		if flag_pointer==True:
    			getDimension4mMalloc(statement,d_map)
       			temp_program=type_name+' '+statement.name
    			for x in range(0, len(d_map.keys())):
    				if 'parameter'+str(x) in d_map.keys():
    					temp_program+='['+d_map['parameter'+str(x)]+']'
    			temp_program+=';'
    			parser = c_parser.CParser()
    			ast = parser.parse(temp_program)
    			return ast.ext[0]
    		else:
    			return statement
  			



def arrangeEmptyStatement(statements):
    update_statements=[]
    for statement in statements:
        if type(statement) is c_ast.If:
            stmt=arrangeEmptyStatementIf(statement)
            if stmt is not None:
            	update_statements.append(stmt)
        elif type(statement) is c_ast.While:
            if type(statement.stmt) is c_ast.EmptyStatement:
                update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=[])))
            elif statement.stmt.block_items is not None:
            	stmt=arrangeEmptyStatement(statement.stmt.block_items)
            	if stmt is not None:
                	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=stmt)))
                else:
                	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=[])))
            else:
                update_statements.append(statement)
        else:
            update_statements.append(statement)
    return update_statements
           

    


def arrangeEmptyStatementIf(statement):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.EmptyStatement:
            if type(statement.iffalse) is c_ast.Compound:
                return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=statement.iffalse, iffalse=None)
            else:
                return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=statement.iffalse, iffalse=None)
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=arrangeEmptyStatement(statement.iftrue.block_items)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
            
        if type(statement.iffalse) is c_ast.Compound:
            if statement.iffalse.block_items is not None:
                new_block_items=arrangeEmptyStatement(statement.iffalse.block_items)
                new_iffalse=c_ast.Compound(block_items=new_block_items)
            else:
                new_iffalse=statement.iffalse
        elif type(statement.iffalse) is c_ast.If:
            new_iffalse=arrangeEmptyStatementIf(statement.iffalse)
        else:
            new_iffalse=statement.iffalse
            
    if new_iftrue is not None and new_iffalse is None:
        return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=None)
    elif new_iftrue is not None and new_iffalse is not None:
        return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
    elif new_iffalse is not None and type(new_iffalse) is c_ast.Compound:
	return c_ast.If(cond=c_ast.UnaryOp(op='!', expr=statement.cond), iftrue=new_iffalse, iffalse=None)
    elif new_iffalse is not None and type(new_iffalse) is c_ast.If:
	return new_iffalse
    else:
	return None







#filename='gototest.c'

def remove_empty_statement(filename):
    content=None
    with open(filename) as f:
        content = f.read()
    content=content.replace('\r','')
    text = r""" """+content
    parser = c_parser.CParser()
    ast = parser.parse(text)
    #print ast.show()
    function_decl = ast.ext[0].decl
    function_param = function_decl
    function_body = ast.ext[0].body
    statements=function_body.block_items
    
    statements=programTransformation(function_body)
    
    
    body_comp = c_ast.Compound(block_items=statements)
    generator = c_generator.CGenerator()   
    print(generator.visit(body_comp))

    


	
	
	
	
def removeMultipleLabel(statements,label,labelMap):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Goto:
                        if statement.name==label:
                        	new_label=label+str(len(labelMap.keys())+1)
                        	labelMap[new_label]=new_label
                        	update_statements.append(c_ast.Goto(name=new_label)) 
                        else:
                        	update_statements.append(statement) 
                elif type(statement) is c_ast.If:
                	update_statements.append(removeMultipleLabelIf(statement,label,labelMap))
                elif type(statement) is c_ast.While:
                	if statement.stmt.block_items is not None:
                		update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=removeMultipleLabel(statement.stmt.block_items,label,labelMap))))
			elif type(statement.stmt) is c_ast.Goto:
				if statement.stmt.name==label:
			        	new_label=label+str(len(labelMap.keys())+1)
			        	labelMap[new_label]=new_label
			        	new_block=[]
			        	new_block.append(c_ast.Goto(name=new_label))
			        	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))
			        else:
			        	new_block=[]
			        	new_block.append(statement.stmt)
			        	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))
			else:
                        	update_statements.append(statement)	
		                	
		else:
                	update_statements.append(statement)
        return update_statements




def removeMultipleLabelIf(statement,label,labelMap):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Goto:
        	if statement.iftrue.name==label:
	        	new_label=label+str(len(labelMap.keys())+1)
	        	labelMap[new_label]=new_label
                        new_iftrue=c_ast.Goto(name=new_label)
                else:
                   	new_iftrue=statement.iftrue
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=removeMultipleLabel(statement.iftrue.block_items,label,labelMap)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Goto:
		if statement.iffalse.name==label:
			new_label=label+str(len(labelMap.keys())+1)
			labelMap[new_label]=new_label
	                new_iffalse=c_ast.Goto(name=new_label)
	        else:
	        	new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=removeMultipleLabel(statement.iffalse.block_items,label,labelMap)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=removeMultipleLabelIf(statement.iffalse,label,labelMap)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)


    



def addMultipleLabel(statements,label,labelMap):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Label:
                        if statement.name==label:
                        	for item in labelMap.keys():
                        		update_statements.append(c_ast.Label(name=item, stmt=None))
                        	if statement.stmt is not None:
                        		update_statements.append(statement.stmt)
                        else:
                        	update_statements.append(statement) 
                elif type(statement) is c_ast.If:
                	update_statements.append(addMultipleLabelIf(statement,label,labelMap))
                elif type(statement) is c_ast.While:
                	if statement.stmt.block_items is not None:
                		update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=addMultipleLabel(statement.stmt.block_items,label,labelMap))))
			elif type(statement.stmt) is c_ast.Goto:
				if statement.stmt.name==label:
					new_block=[]
					for item in labelMap.keys():
						new_block.append(c_ast.Label(name=item, stmt=None))
					if statement.stmt is not None:
						new_block.append(statement.stmt)
			        	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))
			        else:
			        	new_block=[]
			        	new_block.append(statement.stmt)
			        	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))
			else:
                        	update_statements.append(statement)	
		                	
		else:
                	update_statements.append(statement)
        return update_statements




def addMultipleLabelIf(statement,label,labelMap):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Label:
        	if statement.iftrue.name==label:
			new_block=[]
			for item in labelMap.keys():
				new_block.append(c_ast.Label(name=item, stmt=None))
			if statement.iftrue.stmt is not None:
				new_block.append(statement.stmt)
			new_iftrue=c_ast.Compound(block_items=new_block)
                else:
                   	new_iftrue=statement.iftrue
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=addMultipleLabel(statement.iftrue.block_items,label,labelMap)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Label:
		if statement.iffalse.name==label:
			new_block=[]
			for item in labelMap.keys():
				new_block.append(c_ast.Label(name=item, stmt=None))
			if statement.iffalse.stmt is not None:
				new_block.append(statement.stmt)
			new_iffalse=c_ast.Compound(block_items=new_block)
	        else:
	        	new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=addMultipleLabel(statement.iffalse.block_items,label,labelMap)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=addMultipleLabelIf(statement.iffalse,label,labelMap)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)







def removeOrphanLabel(statements,label):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Label:
                        if statement.name!=label:
				update_statements.append(statement) 
                elif type(statement) is c_ast.If:
                	update_statements.append(removeOrphanLabelIf(statement,label))
                elif type(statement) is c_ast.While:
                	if statement.stmt.block_items is not None:
                		update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=removeOrphanLabel(statement.stmt.block_items,label))))
			elif type(statement.stmt) is c_ast.Goto:
				if statement.stmt.name!=label:
					new_block=[]
			        	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))
			        else:
			        	new_block=[]
			        	new_block.append(statement.stmt)
			        	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))
			else:
                        	update_statements.append(statement)	
		                	
		else:
                	update_statements.append(statement)
        return update_statements




def removeOrphanLabelIf(statement,label):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Label:
        	if statement.iftrue.name==label:
			new_block=[]
			if statement.iftrue.stmt is not None:
				new_block.append(statement.stmt)
			new_iftrue=c_ast.Compound(block_items=new_block)
                else:
                   	new_iftrue=statement.iftrue
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=removeOrphanLabel(statement.iftrue.block_items,label)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Label:
		if statement.iffalse.name==label:
			new_block=[]
			if statement.iffalse.stmt is not None:
				new_block.append(statement.stmt)
			new_iffalse=c_ast.Compound(block_items=new_block)
	        else:
	        	new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=removeOrphanLabel(statement.iffalse.block_items,label)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=removeOrphanLabelIf(statement.iffalse,label)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
    
   
 
dummyCount=0
    
def functionToAssignment(statements):
 	global dummyCount
 	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.FuncCall:
			if  '__VERIFIER' not in statement.name.name:
				dummyCount=dummyCount+1
				update_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name='_'+str(dummyCount)+'DUMMY'), rvalue=statement))
			else:
				update_statements.append(statement)
		elif type(statement) is c_ast.If:
	                	update_statements.append(functionToAssignmentIf(statement))
	        elif type(statement) is c_ast.While:
	        	if type(statement.stmt) is c_ast.Compound:
	                	update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=functionToAssignment(statement.stmt.block_items))))
			else:
				if statement.stmt is not None:
					if type(statement) is c_ast.EmptyStatement:
						new_block=[]
						update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=new_block)))	
					else:
						new_block=[]
						new_block.append(statement.stmt)
						update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=functionToAssignment(new_block))))
				else:
			        	update_statements.append(statement)
		else:
                	update_statements.append(statement)
        return update_statements
                	
                	
                	
def functionToAssignmentIf(statement):
      new_iftrue=None
      new_iffalse=None
      global dummyCount
      if type(statement) is c_ast.If:
          if type(statement.iftrue) is c_ast.Compound:
	  	new_block_items=functionToAssignment(statement.iftrue.block_items)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
          elif type(statement.iftrue) is c_ast.FuncCall:
          	if  '__VERIFIER' not in statement.iftrue.name.name:
	  		dummyCount=dummyCount+1
	  		new_iftrue=c_ast.Assignment(op='=',lvalue=c_ast.ID(name='_'+str(dummyCount)+'DUMMY'), rvalue=statement.iftrue)
	  	else:
	  		new_iftrue=statement.iftrue
          else:
               new_iftrue=statement.iftrue
              
          if type(statement.iffalse) is c_ast.Compound:
              if statement.iffalse.block_items is not None:
                  new_block_items=functionToAssignment(statement.iffalse.block_items)
                  new_iffalse=c_ast.Compound(block_items=new_block_items)
              else:
                  new_iffalse=statement.iffalse
          elif type(statement.iffalse) is c_ast.FuncCall:
          	if  '__VERIFIER' not in statement.iffalse.name.name:
	      		dummyCount=dummyCount+1
	      		new_iffalse=c_ast.Assignment(op='=',lvalue=c_ast.ID(name='_'+str(dummyCount)+'DUMMY'), rvalue=statement.iffalse)
	      	else:
	      		new_iffalse=statement.iffalse
          elif type(statement.iffalse) is c_ast.If:
              new_iffalse=functionToAssignmentIf(statement.iffalse)
          else:
              new_iffalse=statement.iffalse
      return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
      
      


def getDummyFunction(f,o,a,cm):
	new_o={}
	for eq in o.keys():
		if o[eq][0]=='e':
			lefthandstmt=expr2string1(o[eq][1])
			if 'DUMMY' in lefthandstmt:
				new_eq=[]
				new_eq.append('s0')
				new_eq.append(o[eq][2])
				new_o[eq]=new_eq
			else:
				new_o[eq]=o[eq]
		else:
			new_o[eq]=o[eq]
	#return f,new_o,a,cm
	return f,o,a,cm



#Get all typedefination

typedef_map={}

def getAllTypeDef(ast):
	global typedef_map
	typedef_map={}
	generator = c_generator.CGenerator()
	for element in ast.ext:
		if type(element) is c_ast.Typedef: 
			if type(element.type.type) is c_ast.Struct:
				program_temp="struct "+ast.ext[0].type.type.name+";"
				temp_ast = parser.parse(program_temp)
				typedef_map[element.name]=generator.visit(temp_ast.ext[0])
			else:
				typedef_map[element.name]=generator.visit(element.type)	
				
				
				
				
				
def updateTypeDef(statement):
	global typedef_map
	parser = c_parser.CParser()
	pointer=None
	array=None
	if type(statement) is c_ast.Decl:
		if type(statement.type) is c_ast.PtrDecl:
			degree=0
    			type_stmt,degree=getArrayDetails(statement,degree)
    			if degree==1:
    				if type_stmt in typedef_map.keys():
    					type_stmt=typedef_map[type_stmt]
    				program_temp=type_stmt+' '+ statement.name
    				pointer=statement.name
    			else:
    			    	if type_stmt in typedef_map.keys():
			    		type_stmt=typedef_map[type_stmt]
			    	program_temp=type_stmt+' '+ statement.name
			    	for x in range(0,degree):
    					program_temp+='[]'
    				pointer=statement.name
    			program_temp+=';'
    			temp_ast = parser.parse(program_temp)
    			return temp_ast.ext[0],pointer,array
    		elif type(statement.type) is c_ast.ArrayDecl:
			degree=0
    			type_stmt,degree=getArrayDetails(statement,degree)
			if type_stmt in typedef_map.keys():
				type_stmt=typedef_map[type_stmt]
			program_temp=type_stmt+' '+statement.name
			for x in range(0,degree):
				program_temp+='[]'
			program_temp+=';'
			array=statement.name
			temp_ast = parser.parse(program_temp)
    			return temp_ast.ext[0],pointer,array
    		else:
    			type_stmt= statement.type.type.names[0]
    			if type_stmt in typedef_map.keys():
				type_stmt=typedef_map[type_stmt]
			program_temp=type_stmt+' '+ statement.name
			program_temp+=';'
			temp_ast = parser.parse(program_temp)
    			return temp_ast.ext[0],pointer,array
	return None,pointer,array


def pointerHandlingParameter(ast):

	if type(ast) is c_ast.FuncDef:
		pointer_list=[]
		array_list=[]
		new_stmts=[]
		new_parameters=''
		generator = c_generator.CGenerator()
		parser = c_parser.CParser()
		if ast.decl.type.args is not None:
			parameters=ast.decl.type.args.params
			if parameters is not None:
				for parameter in parameters:
					if new_parameters=='':
						type_decl,pointer,array=updateTypeDef(parameter)
						if pointer is not None:
							pointer_list.append(pointer)
						if array is not None:
							array_list.append(array)
						new_parameters=generator.visit(type_decl)
					else:
						type_decl,pointer,array=updateTypeDef(parameter)
						if pointer is not None:
							pointer_list.append(pointer)
						if array is not None:
							array_list.append(array)
						new_parameters+=','+generator.visit(type_decl)
		return_type=generator.visit(ast.decl.type.type)
		function_name=ast.decl.name
    		new_fun=return_type+' '+ function_name+'('+ new_parameters +'){}'
    		new_fun=parser.parse(new_fun)
    		return new_fun.ext[0].decl,pointer_list,array_list
	else:
		return None,[],[]


def pointerHandlingDecl(function_body,pointer_list,array_list):
	update_statements=[]
	statements=function_body.block_items
	for statement in statements:
		if type(statement) is c_ast.Decl:
			new_statement,pointer,array=updateTypeDef(statement)
			new_stmt=None
			if pointer is not None:
				if statement.init is not None:
					if type(statement.init) is c_ast.InitList:
						new_statement=None
						new_stmt=None
					else:
						new_stmt=c_ast.Assignment(op='=', lvalue=c_ast.ID(name=pointer), rvalue=ref2function(statement.init))
				pointer_list.append(pointer)
			if array is not None:
				array_list.append(array)
			if new_statement is not None:
				update_statements.append(new_statement)
				if new_stmt is not None:
					update_statements.append(new_stmt)
			else:
				update_statements.append(statement)
		else:
			update_statements.append(statement)
	fun_body=c_ast.Compound(block_items=update_statements)
	return fun_body
	




def pointerHandling(statements,pointer_list,array_list):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Decl:
			new_statement,pointer,array=updateTypeDef(statement)
			if pointer is not None:
				pointer_list.append(pointer)
			if array is not None:
				array_list.append(array)
			if new_statement is not None:
				update_statements.append(new_statement)
			else:
				update_statements.append(statement)
		elif type(statement) is c_ast.If:
			update_statements.append(pointerHandlingIf(statement,pointer_list,array_list))
		elif type(statement) is c_ast.While:
			if statement.stmt.block_items is not None:
                		update_statements.append(c_ast.While(cond=statement.cond,stmt=c_ast.Compound(block_items=pointerHandling(statement.stmt.block_items,pointer_list,array_list))))
		elif type(statement) is c_ast.Assignment:
			update_statements.append(c_ast.Assignment(op=statement.op,lvalue=defref2function(statement.lvalue,pointer_list,array_list),rvalue=defref2function(statement.rvalue,pointer_list,array_list)))
		else:
			update_statements.append(statement)
	return update_statements
	


	
def pointerHandlingIf(statement,pointer_list,array_list):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Assignment:
        	new_iftrue=c_ast.Assignment(op=statement.iftrue.op,lvalue=defref2function(statement.iftrue.lvalue,pointer_list,array_list),rvalue=defref2function(statement.iftrue.rvalue,pointer_list,array_list))
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=pointerHandling(statement.iftrue.block_items,pointer_list,array_list)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Assignment:
		new_iftrue=c_ast.Assignment(op=statement.iffalse.op,lvalue=defref2function(statement.iffalse.lvalue,pointer_list,array_list),rvalue=defref2function(statement.iffalse.rvalue,pointer_list,array_list))
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=pointerHandling(statement.iffalse.block_items,pointer_list,array_list)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=pointerHandlingIf(statement.iffalse,pointer_list)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond=statement.cond, iftrue=new_iftrue, iffalse=new_iffalse)
    
    
def defref2function(statement,pointer_list,array_list):
	if type(statement) is c_ast.UnaryOp:
		parameter=[]
		if statement.op=='*' and statement.expr.name in pointer_list:
			parameter.append(statement.expr)
			return c_ast.FuncCall(name=c_ast.ID(name='_data'), args=c_ast.ExprList(exprs=parameter))
		elif statement.op=='*' and statement.expr.name in array_list:
			return c_ast.ArrayRef(name=statement.expr, subscript=c_ast.Constant(type='int', value='0'))
			#return c_ast.FuncCall(name=c_ast.ID(name='_data'), args=c_ast.ExprList(exprs=parameter))
		elif statement.op=='&' and statement.expr.name in pointer_list:
			parameter.append(statement.expr)
			return c_ast.FuncCall(name=c_ast.ID(name='_address'), args=c_ast.ExprList(exprs=parameter))
		else:
			return c_ast.UnaryOp(op=statement.op, expr=defref2function(statement.expr,pointer_list,array_list))
	elif type(statement) is c_ast.BinaryOp:
		return c_ast.BinaryOp(op=statement.op,left=defref2function(statement.left,pointer_list,array_list),right=defref2function(statement.right,pointer_list,array_list))
	else:
		return statement
		
		
def ref2function(statement):
	if type(statement) is c_ast.UnaryOp:
		parameter=[]
		if statement.op=='&':
			parameter.append(statement.expr)
			return c_ast.FuncCall(name=c_ast.ID(name='_address'), args=c_ast.ExprList(exprs=parameter))
		else:
			return c_ast.UnaryOp(op=statement.op, expr=ref2function(statement.expr))
	elif type(statement) is c_ast.BinaryOp:
		return c_ast.BinaryOp(op=statement.op,left=ref2function(statement.left),right=ref2function(statement.right))
	else:
		return statement





def change_var_name(statements):
	update_statements=[]
	for statement in statements:
		if type(statement) is c_ast.Decl:
			if type(statement.type) is c_ast.ArrayDecl:
				if is_number(statement.type.type.declname[-1])==True:
					statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.ArrayDecl(type=c_ast.TypeDecl(declname=statement.type.type.declname+'_var', quals=statement.type.type.quals, type=statement.type.type.type), dim=statement.type.dim, dim_quals=statement.type.dim_quals), init=statement.init, bitsize=statement.bitsize)
				elif statement.type.type.declname in ['S','Q','N','in','is']:
					statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.ArrayDecl(type=c_ast.TypeDecl(declname=statement.type.type.declname+'_var', quals=statement.type.type.quals, type=statement.type.type.type), dim=statement.type.dim, dim_quals=statement.type.dim_quals), init=statement.init, bitsize=statement.bitsize)
			else:
				if is_number(statement.type.declname[-1])==True:
					statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.TypeDecl(declname=statement.type.declname+'_var', quals=statement.type.quals, type=statement.type.type), init=statement.init, bitsize=statement.bitsize)
				elif statement.type.declname in ['S','Q','N','in','is']:
					statement=c_ast.Decl(name=statement.name+'_var', quals=statement.quals, storage=statement.storage, funcspec=statement.funcspec, type=c_ast.TypeDecl(declname=statement.type.declname+'_var', quals=statement.type.quals, type=statement.type.type), init=statement.init, bitsize=statement.bitsize)
			update_statements.append(statement)
		elif type(statement) is c_ast.If:
			update_statements.append(change_var_nameIf(statement))
		elif type(statement) is c_ast.While:
			if statement.stmt.block_items is not None:
				update_statements.append(c_ast.While(cond=change_var_name_stmt(statement.cond),stmt=c_ast.Compound(block_items=change_var_name(statement.stmt.block_items))))	
			else:
				update_statements.append(c_ast.While(cond=change_var_name_stmt(statement.cond),stmt=c_ast.Compound(block_items=statement.stmt.block_items)))	
		elif type(statement) is c_ast.Assignment:
			update_statements.append(c_ast.Assignment(op=statement.op,lvalue=change_var_name_stmt(statement.lvalue),rvalue=change_var_name_stmt(statement.rvalue)))
		else:
			update_statements.append(statement)
	return update_statements
	


	
def change_var_nameIf(statement):
    new_iftrue=None
    new_iffalse=None
    if type(statement) is c_ast.If:
        if type(statement.iftrue) is c_ast.Assignment:
        	new_iftrue=c_ast.Assignment(op=statement.iftrue.op,lvalue=change_var_name_stmt(statement.iftrue.lvalue),rvalue=change_var_name_stmt(statement.iftrue.rvalue))
        elif type(statement.iftrue) is c_ast.Compound:
            if statement.iftrue.block_items is not None:
                new_block_items=change_var_name(statement.iftrue.block_items)
                new_iftrue=c_ast.Compound(block_items=new_block_items)
            else:
                new_iftrue=statement.iftrue
        else:
            new_iftrue=statement.iftrue
       
       
        if type(statement.iffalse) is c_ast.Assignment:
		new_iftrue=c_ast.Assignment(op=statement.iffalse.op,lvalue=change_var_name_stmt(statement.iffalse.lvalue),rvalue=change_var_name_stmt(statement.iffalse.rvalue))
	elif type(statement.iffalse) is c_ast.Compound:
		if statement.iffalse.block_items is not None:
	        	new_block_items=change_var_name(statement.iffalse.block_items)
	                new_iffalse=c_ast.Compound(block_items=new_block_items)
	        else:
	                new_iffalse=statement.iffalse
	elif type(statement.iffalse) is c_ast.If:
		new_iffalse=change_var_nameIf(statement.iffalse)
	else:
        	new_iffalse=statement.iffalse
        	
    return c_ast.If(cond= change_var_name_stmt(statement.cond), iftrue=new_iftrue, iffalse=new_iffalse)


def change_var_name_stmt(statement):
	if type(statement) is c_ast.BinaryOp:
		if type(statement.left) is c_ast.ID:
			if is_number(statement.left.name[-1])==True:
				stmt_left=c_ast.ID(name=statement.left.name+'_var')
			elif statement.left.name in ['S','Q','N','in','is']:
				stmt_left=c_ast.ID(name=statement.left.name+'_var')
			else:
				stmt_left=change_var_name_stmt(statement.left)
		else:
			stmt_left=change_var_name_stmt(statement.left)
		
		if type(statement.right) is c_ast.ID:
			if is_number(statement.right.name[-1])==True:
				stmt_right=c_ast.ID(name=statement.right.name+'_var')
			elif statement.right.name in ['S','Q','N','in','is']:
				stmt_right=c_ast.ID(name=statement.right.name+'_var')
			else:
				stmt_right=change_var_name_stmt(statement.right)
		else:
			stmt_right=change_var_name_stmt(statement.right)
		return c_ast.BinaryOp(op=statement.op, left=stmt_left, right=stmt_right)
	elif type(statement) is c_ast.UnaryOp:
		if type(statement.expr) is c_ast.ID:
			if is_number(statement.expr.name[-1])==True:
				stmt=c_ast.ID(name=statement.expr.name+'_var')
			elif statement.expr.name in ['S','Q','N','in','is']:
				stmt=c_ast.ID(name=statement.expr.name+'_var')
			else:
				stmt=change_var_name_stmt(statement.expr)
		else:
			stmt=change_var_name_stmt(statement.expr)
		return c_ast.UnaryOp(op=statement.op, expr=stmt)
	elif type(statement) is c_ast.ID:
		if is_number(statement.name[-1])==True:
			return c_ast.ID(name=statement.name+'_var')
		elif statement.name in ['S','Q','N','in','is']:
			return c_ast.ID(name=statement.name+'_var')
		else:
			return statement
	else:
		return statement




#filename='veris.c_NetBSD-libc__loop_true-unreach-call_true-termination.c'
filename='sv-benchmarks/loops/trex04_true-unreach-call_false-termination1.i'
def changeTest(filename):
    content=None
    global new_variable
    with open(filename) as f:
        content = f.read()
    content=content.replace('\r','')
    text = r""" """+content
    parser = c_parser.CParser()
    ast = parser.parse(text)
    stmts=ast.ext[0].body.block_items
    statements=change_var_name(stmts)
    body=c_ast.Compound(block_items=statements)
    #body.show()
    generator = c_generator.CGenerator()
    print generator.visit(body)
    
		

#Add External Variables


def addAllExtVariables(statements,externalvariables,localvarmap):
	update_statements=[]
	for var in externalvariables.keys():
		variable=externalvariables[var]
		localvarmap[var]=variable
		if variable.getInitialvalue() is not None:
			update_statements.append(c_ast.Assignment(op='=', lvalue=c_ast.ID(name=var), rvalue=c_ast.Constant(type='int', value=variable.getInitialvalue())))
	for element in statements:
		update_statements.append(element)
	return update_statements,localvarmap
	

def getWitness(filename,functionname,resultfunction):
	witnessXml=[]
	#witnessXml1='<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n'+'<graphml xmlns="http:\/\/graphml.graphdrawing.org\/xmlns" xmlns:xsi="http:\/\/www.w3.org\/2001\/XMLSchema-instance">'+'\t<key attr.name="isEntryNode" attr.type="boolean" for="node" id="entry">\n'+'\t\t<default>false<\/default>\n'+'\t<\/key>\n'+'\t<key attr.name="witness-type" attr.type="string" for="graph" id="witness-type"\/>\n'+'\t<key attr.name="sourcecodelang" attr.type="string" for="graph" id="sourcecodelang"\/>'+'\t<key attr.name="producer" attr.type="string" for="graph" id="producer"\/>\n'+'\t<key attr.name="specification" attr.type="string" for="graph" id="specification"\/>\n'+'\t<key attr.name="programFile" attr.type="string" for="graph" id="programfile"\/>\n'+'\t<key attr.name="programHash" attr.type="string" for="graph" id="programhash"\/>\n'+'\t<key attr.name="memoryModel" attr.type="string" for="graph" id="memorymodel"\/>\n'+'\t<key attr.name="architecture" attr.type="string" for="graph" id="architecture"\/>\n'+'\t<key attr.name="startline" attr.type="int" for="edge" id="startline"\/>\n'+'\t<key attr.name="assumption" attr.type="string" for="edge" id="assumption"\/>\n'+'\t<key attr.name="assumption.scope" attr.type="string" for="edge" id="assumption.scope"\/>\n'+'\t<key attr.name="assumption.resultfunction" attr.type="string" for="edge" id="assumption.resultfunction"\/>\n'+'\t<graph edgedefault="directed">\n'+'\t\t<data key="witness-type">violation_witness<\/data>\n'+'\t\t<data key="sourcecodelang">C<\/data>\n'+'\t\t<data key="producer">CPAchecker 1.6.1-svn<\/data>\n'+'\t\t<data key="specification">CHECK( init(main()), LTL(G ! call(__VERIFIER_assume)) )<\/data>\n'+'\t\t<data key="programfile">'+filename+'<\/data>\n'+'\t\t<data key="programhash">1776ed2413d170f227b69d8c79ba700d31db6f75<\/data>\n'+'\t\t<data key="memorymodel">precise<\/data>\n'+'\t\t<data key="memorymodel">precise<\/data>\n'+'\t\t<node id="entry">\n'+'\t\t\t<data key="entry">true<\/data>\n'+'\t\t</node>\n'+'\t\t<node id="error">\n'+'\t\t\t<data key="violation">true<\/data>\n'+'\t\t<\/node>\n'+'\t\t<edge source="entry" target="error">\n'+'\t\t\t<data key="startline">5<\/data>\n'+'\t\t\t<data key="assumption">\\result == 0<\/data>\n'
	#witnessXml1='<?xml version="1.0" encoding="UTF-8" standalone="no"?>\n'+'<graphml xmlns="http:\/\/graphml.graphdrawing.org\/xmlns" xmlns:xsi="http:\/\/www.w3.org\/2001\/XMLSchema-instance">'+'\t<key attr.name="isEntryNode" attr.type="boolean" for="node" id="entry">\n'+'\t\t<default>false<\/default>\n'+'\t<\/key>\n'+'\t<key attr.name="witness-type" attr.type="string" for="graph" id="witness-type"\/>\n'+'\t<key attr.name="sourcecodelang" attr.type="string" for="graph" id="sourcecodelang"\/>'+'\t<key attr.name="producer" attr.type="string" for="graph" id="producer"\/>\n'+'\t<key attr.name="specification" attr.type="string" for="graph" id="specification"\/>\n'+'\t<key attr.name="programFile" attr.type="string" for="graph" id="programfile"\/>\n'+'\t<key attr.name="programHash" attr.type="string" for="graph" id="programhash"\/>\n'+'\t<key attr.name="memoryModel" attr.type="string" for="graph" id="memorymodel"\/>\n'+'\t<key attr.name="architecture" attr.type="string" for="graph" id="architecture"\/>\n'+'\t<key attr.name="startline" attr.type="int" for="edge" id="startline"\/>\n'+'\t<key attr.name="assumption" attr.type="string" for="edge" id="assumption"\/>\n'+'\t<key attr.name="assumption.scope" attr.type="string" for="edge" id="assumption.scope"\/>\n'+'\t<key attr.name="assumption.resultfunction" attr.type="string" for="edge" id="assumption.resultfunction"\/>\n'+'\t<graph edgedefault="directed">\n'+'\t\t<data key="witness-type">violation_witness<\/data>\n'+'\t\t<data key="sourcecodelang">C<\/data>\n'+'\t\t<data key="producer">CPAchecker 1.6.1-svn<\/data>\n'+'\t\t<data key="specification">CHECK( init(main()), LTL(G ! call(__VERIFIER_assume)) )<\/data>\n'+'\t\t<data key="programfile">'+filename+'<\/data>\n'+'\t\t<data key="programhash">1776ed2413d170f227b69d8c79ba700d31db6f75<\/data>\n'+'\t\t<data key="memorymodel">precise<\/data>\n'+'\t\t<data key="memorymodel">precise<\/data>\n'+'\t\t<node id="entry">\n'+'\t\t\t<data key="entry">true<\/data>\n'+'\t\t</node>\n'+'\t\t<node id="error">\n'+'\t\t\t<data key="violation">true<\/data>\n'+'\t\t<\/node>\n'+'\t\t<edge source="entry" target="error">\n'
	witnessXml1='<?xml version="1.0" encoding="UTF-8" standalone="no"?>'+'<graphml xmlns="http://graphml.graphdrawing.org/xmlns" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"><key attr.name="isEntryNode" attr.type="boolean" for="node" id="entry"><default>false</default></key><key attr.name="isViolationNode" attr.type="boolean" for="node" id="violation"><default>false</default></key><key attr.name="witness-type" attr.type="string" for="graph" id="witness-type"/><key attr.name="sourcecodelang" attr.type="string" for="graph" id="sourcecodelang"/><key attr.name="producer" attr.type="string" for="graph" id="producer"/><key attr.name="specification" attr.type="string" for="graph" id="specification"/><key attr.name="programFile" attr.type="string" for="graph" id="programfile"/><key attr.name="programHash" attr.type="string" for="graph" id="programhash"/><key attr.name="memoryModel" attr.type="string" for="graph" id="memorymodel"/><key attr.name="architecture" attr.type="string" for="graph" id="architecture"/><key attr.name="startline" attr.type="int" for="edge" id="startline"/><key attr.name="assumption" attr.type="string" for="edge" id="assumption"/><key attr.name="assumption.scope" attr.type="string" for="edge" id="assumption.scope"/><key attr.name="assumption.resultfunction" attr.type="string" for="edge" id="assumption.resultfunction"/><graph edgedefault="directed"><data key="witness-type">violation_witness</data><data key="sourcecodelang">C</data><data key="producer">CPAchecker 1.6.1-svn</data><data key="specification">CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )</data><data key="programfile">'+filename+'</data><data key="programhash">1776ed2413d170f227b69d8c79ba700d31db6f75</data><data key="memorymodel">precise</data><data key="architecture">32bit</data><node id="entry"><data key="entry">true</data></node><node id="error"><data key="violation">true</data></node><edge source="entry" target="error">'
	witnessXml.append(witnessXml1)
	#witnessXml2='\t\t\t<data key="assumption.scope">'+functionname+'<\/data>\n'+'\t\t\t<data key="assumption.resultfunction">'+resultfunction+'<\/data>\n'+'\t\t</edge>\n'+'\t</graph>\n'+'</graphml>\n'
	witnessXml2='<data key="assumption.scope">'+functionname+'</data><data key="assumption.resultfunction">'+resultfunction+'</data></edge></graph></graphml>'
	witnessXml.append(witnessXml2)
	witnessXml.append(functionname)
	witnessXml.append(filename)
	return witnessXml
	

	
 
 


 
 

 
 
 
 
 
 

   
   
   
   
   
   
   
   
   
    
   
   
    
   
   
    
    
    
    
   
  

		
		