import leon.lang._

object divCohen {

    def divCohen(X: Int,Y: Int): (Int,Int)=({
	require(X >= 0 && Y > 0)
        var q = 0
        var r = X
        while(r>=Y) {
            var A = 1
            var B = Y
            while(r>=2*B) {
                
                A=2*A
                B=2*B
            }
            r=r-B
            q=q+A
      }
      (r,q)
    })ensuring(res =>res._1 >= 0) 

}
