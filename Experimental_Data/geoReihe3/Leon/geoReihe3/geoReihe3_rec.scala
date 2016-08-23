import leon.lang._

object geoReihe3 {

    def geoReihe3(Z: Int,K: Int,a: Int): Int=({
        require(Z > 1 && K > 0 && a > 0)
        if (K == 1) a
        else    geoReihe3(Z,K-1,a)+a*power(Z,K)
    })ensuring(_ == ((power(Z,K)-1)/(Z-1))*a) 


     def power(a: Int,b: Int): Int = { 
        require(a >= 0 && b >= 0)
        if (a == 0) 0
        else if (b == 0) 1
        else    power(a,b-1)*a
    }

}



