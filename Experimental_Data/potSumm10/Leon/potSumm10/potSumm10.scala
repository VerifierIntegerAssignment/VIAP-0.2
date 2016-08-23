import leon.lang._

object potSumm10 {

  def potSumm10(X: BigInt): BigInt = {
    require(X >= 0&& X<10)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i*i*i*i*i*i*i*i
    }) 
    sum
  } ensuring(_ == (6*X*X*X*X*X*X*X*X*X*X*X+33*X*X*X*X*X*X*X*X*X*X+55*X*X*X*X*X*X*X*X*X-66*X*X*X*X*X*X*X+66*X*X*X*X*X-33*X*X*X+5*X)/66)

}
