import leon.lang._

object sumOfEven {

  def sumOfEven(X: BigInt): BigInt = {
    require(X >= 0)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*2
    }) 
    sum
  } ensuring(_ == X*(X+1))

}
