import leon.lang._

object potSumm9 {

  def potSumm9(X: BigInt): BigInt = {
    require(X >= 0 && X<20)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i*i*i*i*i*i
    }) 
    sum
  } ensuring(_ == (2*X*X*X*X*X*X*X*X*X*X+10*X*X*X*X*X*X*X*X*X+15*X*X*X*X*X*X*X*X-14*X*X*X*X*X*X+10*X*X*X*X-3*X*X)/20)

}
