#Factorial
file_name='benchmark/fact.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['F1==factorial(X)']
prove(axiom,pre_condition,post_condition)


#Example from Leon Paper

file_name='benchmark/abs.java'
axiom=translate(file_name)
pre_condition=[]
post_condition=['a1>=0']
prove(axiom,pre_condition,post_condition)


#VSTTE 2008

file_name='benchmark/addDafny.java'
axiom=translate(file_name)
pre_condition=[]
post_condition=['r1==X+Y']
prove(axiom,pre_condition,post_condition)

#Cohen Cube

file_name='benchmark/cubeCohen.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['m1==X**3']
prove(axiom,pre_condition,post_condition)


#cohendivision

file_name='benchmark/divCohen.java'
axiom=translate(file_name)

pre_condition=['X>=0','Y>0']
post_condition=['X==Y*q1+r1']
prove(axiom,pre_condition,post_condition)

post_condition=['r1<Y']
prove(axiom,pre_condition,post_condition)

post_condition=['r1>=0']
prove(axiom,pre_condition,post_condition)


#VSTTE 2008 Dafny


file_name='benchmark/divDafny.java'
axiom=translate(file_name)
pre_condition=['X>=0','Y>0']
post_condition=['X==Y*q1+r1']
prove(axiom,pre_condition,post_condition)

post_condition=['r1>=0']
prove(axiom,pre_condition,post_condition)

post_condition=['r1<Y']
prove(axiom,pre_condition,post_condition)

# divisionbyKaldewaij

file_name='benchmark/divKaldewaij.java'
axiom=translate(file_name)
pre_condition=['A>=0','B>0']
post_condition=['r1>=0']
prove(axiom,pre_condition,post_condition)

# geometric series 1

file_name='benchmark/geoReihe1.java'
axiom=translate(file_name)
pre_condition=['K>0','Z>1']
post_condition=['m1==((Z**(K)-1)/(Z-1))*(Z-1)']
prove(axiom,pre_condition,post_condition)



# geometric series 2

file_name='benchmark/geoReihe2.java'
axiom=translate(file_name)
pre_condition=['K>0','Z>1']
post_condition=['m1==((Z**(K)-1)/(Z-1))*(Z-1)']
prove(axiom,pre_condition,post_condition)

# geometric series 3

file_name='benchmark/geoReihe3.java'
axiom=translate(file_name)
pre_condition=['K>0','Z>1','a']
post_condition=['m1==((Z**(K)-1)/(Z-1))*a']
prove(axiom,pre_condition,post_condition)

# Tower of Hanoi Moves

file_name='benchmark\hanoi.java'
axiom=translate(file_name)
pre_condition=['x>0']
post_condition=['h1==2**x-1']
prove(axiom,pre_condition,post_condition)


#Hardware Division

file_name='benchmark/divHard.java'
axiom=translate(file_name)

pre_condition=['X>=0','Y>0']
post_condition=['X==Y*q1+r1']
prove(axiom,pre_condition,post_condition)

post_condition=['r1>=0']
prove(axiom,pre_condition,post_condition)


#exponential

file_name='benchmark\power.java'
axiom=translate(file_name)
pre_condition=['a>=0','b>=0']
post_condition=['P1==a**b']
prove(axiom,pre_condition,post_condition)

#Product of two numbers

file_name='benchmark\product.java'
axiom=translate(file_name)
pre_condition=['a>=0','b>=0']
post_condition=['A1==a*b']
prove(axiom,pre_condition,post_condition)


#Series 1+2+3+....

file_name='benchmark/potSumm1.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==X*(X+1)/2']
prove(axiom,pre_condition,post_condition)

#Series 1^2+2^2+3^2+....

file_name='benchmark/potSumm2.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==X*(X+1)*(2*X+1)/6']
prove(axiom,pre_condition,post_condition)

#Series 1^3+2^3+3^3+....

file_name='benchmark/potSumm3.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==X*(X+1)*X*(X+1)/4']
prove(axiom,pre_condition,post_condition)

#Series 1^4+2^4+3^4+....

file_name='benchmark/potSumm4.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(6*X**5+15*X**4+10*X**3-X)/30']
prove(axiom,pre_condition,post_condition)

#Series 1^5+2^5+3^5+....

file_name='benchmark/potSumm5.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(2*X**6+6*X**5+5*X**4-X**2)/12']
prove(axiom,pre_condition,post_condition)


#Series 1^6+2^6+3^6+....

file_name='benchmark/potSumm6.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(6*X**7+21*X**6+21*X**5-7*X**3+X)/42']
prove(axiom,pre_condition,post_condition)


#Series 1^7+2^7+3^7+....

file_name='benchmark/potSumm7.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(3*X**8+12*X**7+14*X**6-7*X**4+2*X**2)/24']
prove(axiom,pre_condition,post_condition)

#Series 1^8+2^8+3^8+....

file_name='benchmark/potSumm8.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(10*X**9+45*X**8+60*X**7-42*X**5+20*X**3-3*X)/90']
prove(axiom,pre_condition,post_condition)


#Series 1^9+2^9+3^9+....

file_name='benchmark/potSumm9.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(2*X**10+10*X**9+15*X**8-14*X**6+10*X**4-3*X**2)/20']
prove(axiom,pre_condition,post_condition)

#Series 1^10+2^10+3^10+....

file_name='benchmark/potSumm10.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==(6*X**11+33*X**10+55*X**9-66*X**7+66*X**5-33*X**3+5*X)/66']
prove(axiom,pre_condition,post_condition)


#Square of a number

file_name='benchmark\square.java'
axiom=translate(file_name)

pre_condition=['M>=0']
post_condition=['s1==M*M']
prove(axiom,pre_condition,post_condition)


#Square Root of Integer

file_name='benchmark/sqrt.java'
axiom=translate(file_name)

pre_condition=['X>=0']
post_condition=['(a1+1)**2>X']
prove(axiom,pre_condition,post_condition)

post_condition=['a1**2<=X']
prove(axiom,pre_condition,post_condition)

#Sum of Even Number 


file_name='benchmark/sumOfEven.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==X*(X+1)']
prove(axiom,pre_condition,post_condition)

#Sum of Sum of odd Number 

file_name='benchmark/sumOfOdd.java'
axiom=translate(file_name)
pre_condition=['X>=0']
post_condition=['sum1==X*X']
prove(axiom,pre_condition,post_condition)
