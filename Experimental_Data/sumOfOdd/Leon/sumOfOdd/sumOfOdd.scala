import leon.lang._

object sumOfOdd {

  def sumOfOdd(X: BigInt): BigInt = {
    require(X >= 0)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*2+1
    }) 
    sum
  } ensuring(_ == X*(X+2))

}
