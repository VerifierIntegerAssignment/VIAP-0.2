import leon.lang._

object potSumm2 {

  def NSeries(X: BigInt): BigInt = {
    require(X >= 0 && X<500)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i
    }) 
    sum
  } ensuring(_ == X*(X+1)*(2*X+1)/6)

}
