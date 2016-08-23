import leon.lang._

object potSumm4 {

  def potSumm4(X: BigInt): BigInt = {
    require(X >= 0 && X<50)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i
    }) 
    sum
  } ensuring(_ == (6*X*X*X*X*X+15*X*X*X*X+10*X*X*X-X)/30)

}
