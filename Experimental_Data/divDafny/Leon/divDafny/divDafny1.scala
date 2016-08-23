import leon.lang._

object divDafny {

def divDafny(x: BigInt, y: BigInt): (BigInt, BigInt) = {
    require(x >= 0 && y > 0)
    var r = x
    var q = BigInt(0)
    (while(r >= y) {
      r = r - y
      q = q + 1
    }) 
    (q, r)
  } ensuring(res => x == y*res._1 + res._2) 

}
