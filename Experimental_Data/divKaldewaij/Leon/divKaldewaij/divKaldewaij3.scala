import leon.lang._

object divKaldewaij {

    def divKaldewaij(A: Int,B: Int): (Int,Int)=({
	require(A >= 0 && B > 0)
        var q = 0
        var r = A
        var b=B 
   	while(r>=b)
       	{
       		b=2*b
        } 
    	while(b!=B)
        {
        	q=2*q
        	b=b/2
        	if (r>=b) 
            	{
            		q=q+1;
            		r=r-b;
            	}

        }
      (r,q)
    })ensuring(res => res._1 < B) 

}
