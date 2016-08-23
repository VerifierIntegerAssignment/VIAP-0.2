import leon.lang._

object potSumm8 {

  def potSumm8(X: BigInt): BigInt = {
    require(X >= 0 && X<20)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i*i*i*i*i
    }) 
    sum
  } ensuring(_ == (10*X*X*X*X*X*X*X*X*X+45*X*X*X*X*X*X*X*X+60*X*X*X*X*X*X*X-42*X*X*X*X*X+20*X*X*X-3*X)/90)

}
