import leon.lang._

object potSumm1 {

  def potSumm1(X: BigInt): BigInt = {
    require(X >= 0)
    var sum: BigInt = 0
    var i: BigInt = 0
    (while(i < X) {
      i = i + 1
      sum = sum + i
    }) 
    sum
  } ensuring(_ == ((X+1)*X)/2)

}
