import leon.lang._

object potSumm3 {

  def potSumm3(X: BigInt): BigInt = {
    require(X >= 0 && X<200)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i*i*i
    }) 
    sum
  } ensuring(_ == X*(X+1)*X*(X+1)/4)

}
