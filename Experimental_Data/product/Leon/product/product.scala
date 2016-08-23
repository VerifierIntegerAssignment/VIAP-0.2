import leon.lang._

object product {

    def product(a: Int,b: Int): Int=({
	require(a >= 0 && b>=0)
        var A: Int = 0
        var J: Int = 0
	while (J<b)
	{
	     A = A + a
	     J = J + 1
        }
      A
    })ensuring(_ == a*b) 


}

