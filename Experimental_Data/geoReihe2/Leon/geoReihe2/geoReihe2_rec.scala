import leon.lang._

object geoReihe2 {

    def geoReihe2(Z: Int,K: Int): Int=({
        require(Z > 0 && K > 0)
        if (K == 0) (Z-1)
        else    geoReihe2(Z,K-1)+(Z-1)*power(Z,K)
    })ensuring(_ == ((power(Z,K)-1)/(Z-1))*(Z-1)) 


     def power(a: Int,b: Int): Int = { 
        require(a >= 0 && b >= 0)
        if (b == 0) 1
        else    power(a,b-1)*a
    }

}



