import leon.lang._

object square {

    def square(M: Int): Int=({
	require(M >= 0)
        var s: Int = 0
        var i: Int = 0
	while(i<M)
	{
		s=s+M;
		i=i+1;
			
	}
      s
    })ensuring(_ == M*M) 

}


