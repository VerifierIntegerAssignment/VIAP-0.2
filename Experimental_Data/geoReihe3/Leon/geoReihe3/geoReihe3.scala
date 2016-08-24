import leon.lang._

object geoReihe3 {

    def geoReihe3(Z: Int,K: Int,a: Int): Int=({
	require(Z > 0 && K>0 && a>0)
        var m: Int = a
        var l: Int = 1
        var c: Int = 1
	while (c < K){
	    c = c + 1
	    m = m*Z + a
	    l = l*Z
	 }
	
  		m = m *(Z -1);
      m
    })ensuring(_ == ((power(Z,K)-1)/(Z-1))*a) 


 def power(a: Int,b: Int): Int = { 
        require(a >= 0 && b >= 0)
        if (a == 0 && b>0) 0
        else if (b == 0) 1
        else    power(a,b-1)*a
    }

}


