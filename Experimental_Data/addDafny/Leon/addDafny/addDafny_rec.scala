import leon.lang._

object addDafny {

 def addDafny(x : BigInt, y : BigInt): BigInt = ({
     require(x >= 0 && y>=0)
     if (y == 0)  x else if (x == 0)  y else addDafny(x,y-1)+1
  }) ensuring(res=> res == x+y)

}
