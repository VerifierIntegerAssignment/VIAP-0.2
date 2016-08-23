import leon.lang._

object sqrt {

  def sqrt(X: Int): Int = {
    require(X >= 0)
    var a: Int = 0
    var su: Int = 1
    var t: Int = 1
    (while ( su <= X ){
        a=a+1
        t=t+2
        su=su+t
        }) 
    a
  } ensuring(res => X>=(res)*(res))

}


