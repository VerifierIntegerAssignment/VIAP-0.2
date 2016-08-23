from z3 import *
set_param(proof=True)
_p1=Int('_p1')
_p2=Int('_p2')
a=Int('a')
X=Int('X')
t=Int('t')
su=Int('su')
a1=Int('a1')
X1=Int('X1')
su1=Int('su1')
t1=Int('t1')
_N1=Const('_N1',IntSort())
_n1=Int('_n1')
power=Function('power',IntSort(),IntSort(),IntSort())
_s=Solver()
_s.add(ForAll([_p1],Implies(_p1>=0, power(0,_p1)==0)))
_s.add(ForAll([_p1,_p2],Implies(power(_p2,_p1)==0,_p2==0)))
_s.add(ForAll([_p1],Implies(_p1>0, power(_p1,0)==1)))
_s.add(ForAll([_p1,_p2],Implies(power(_p1,_p2)==1,Or(_p1==1,_p2==0))))
_s.add(ForAll([_p1,_p2],Implies(And(_p1>0,_p2>=0), power(_p1,_p2+1)==power(_p1,_p2)*_p1)))
_s.set("timeout",60000)
_s.add(X1 == X)
_s.add(a1 == _N1)
_s.add(t1 == 2*_N1 + 1)
_s.add(su1 == _N1*_N1 + 2*_N1 + 1)
_s.add(_N1*_N1 + 2*_N1 + 1 > X)
_s.add(ForAll([_n1],Implies(And((_n1<_N1),_n1>=0),_n1*_n1 + 2*_n1 + 1 <= X)))
_s.add(Or(_N1==0,_N1*_N1 <= X))
_s.add(_N1>=0)
_s.add(X>=0)
_s.add(Not(_N1*_N1 <= X))
if sat==_s.check():
	print "Counter Example"
	print _s.model()
elif unsat==_s.check():
	_s.check()
	if os.path.isfile('j2llogs.logs'):
		file = open('j2llogs.logs', 'a')
		file.write("\n**************\nProof Details\n**************\n"+str(_s.proof().children())+"\n")
		file.close()
	else:
		file = open('j2llogs.logs', 'w')
		file.write("\n**************\nProof Details\n**************\n"+str(_s.proof().children())+"\n")
		file.close()
	print "Successfully Proved"
else:
	print "Failed To Prove"