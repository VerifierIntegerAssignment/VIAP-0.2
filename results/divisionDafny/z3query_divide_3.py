from z3 import *
set_param(proof=True)
_p1=Int('_p1')
_p2=Int('_p2')
Y=Int('Y')
X=Int('X')
r=Int('r')
q=Int('q')
Y1=Int('Y1')
q1=Int('q1')
X1=Int('X1')
r1=Int('r1')
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
_s.add(Y1 == Y)
_s.add(X1 == X)
_s.add(q1 == _N1)
_s.add(r1 == X - Y*_N1)
_s.add(X - Y*_N1 < Y)
_s.add(Or(_N1==0,X - Y*(_N1-1) >= Y))
_s.add(_N1>=0)
_s.add(X>=0)
_s.add(Y>0)
_s.add(Not(X - Y*_N1 < Y))
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