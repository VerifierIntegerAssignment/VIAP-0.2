import leon.lang._

object potSumm7 {

  def potSumm7(X: BigInt): BigInt = {
    require(X >= 0 && X<20)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i*i*i*i
    }) 
    sum
  } ensuring(_ == (3*X*X*X*X*X*X*X*X+12*X*X*X*X*X*X*X+14*X*X*X*X*X*X-7*X*X*X*X+2*X*X)/24)

}
