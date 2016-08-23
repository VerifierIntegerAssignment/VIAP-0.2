import leon.lang._

object power {

    def powerloop(a: Int,b: Int): Int=({
	require(a >= 0 && b>=0)
        var A: Int = 1
        var J: Int = 0
	while (J<b)
	{
	     A = A * a
	     J = J + 1
        }
      A
    })ensuring(_ == power(a,b)) 


     def power(a: Int,b: Int): Int = ({ 
        require(a >= 0 && b >= 0)
        if (a == 0) 0 else if (b == 0) 1 else power(a,b-1)*a
    })

}

