method cohendiv(X: int,Y: int) returns (r: int, q: int)
requires X>=0
requires Y>0
ensures r>=0;
{
  
    r:= 0;
    q:= X;
    var A: int;
    var B: int ;
    while(r >= Y)
    {
    	A:=1;
    	B:=Y;
    
    	while(r >= 2*B)
    	{
    		A:=2*A;
    		B:=2*B;
    	}
    	r:=r-B;
    	q:=q+A;
    			
   }

}
	

		
		
