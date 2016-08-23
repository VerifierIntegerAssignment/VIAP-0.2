import leon.lang._

object potSumm5 {

  def potSumm5(X: BigInt): BigInt = {
    require(X >= 0 && X<20)
    var sum: BigInt = 0
    var i: BigInt = 0
    while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i*i
    }
    sum
  } ensuring(_ == (2*X*X*X*X*X*X+6*X*X*X*X*X+5*X*X*X*X-X*X)/12)

}
