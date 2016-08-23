import leon.lang._

object potSumm6 {

  def NSeries(X: BigInt): BigInt = {
    require(X >= 0 && X<20)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i*i*i
    }) 
    sum
  } ensuring(_ == (6*X*X*X*X*X*X*X+21*X*X*X*X*X*X+21*X*X*X*X*X-7*X*X*X+X)/42)

}
