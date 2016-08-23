import leon.lang._

object hardintdiv {

    def hardintdiv(X: Int,Y: Int): (Int,Int)=({
	require(X >= 0 && Y > 0)
        var q = 0
        var r = X
        var p=1 
        var ds=Y 
	while ( r>= ds )
	{
	    ds=2*ds
	    p=2*p
	}
	
	while ( p!=1 )
	{
	    ds=ds/2
	    p=p/2
	
	    if ( r>=ds ) 
	    {
	             r=r-ds
	             q=q+p
	    }
         }
      (r,q)
    })ensuring(res =>res._1 < Y) 

}

