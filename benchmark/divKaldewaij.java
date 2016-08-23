
public class divKaldewaij{

	
	public static void divKaldewaij(int A,int B) {

	    int q;
	    int r;
	    int b;    
	    

	    q=0;
	    r=A;
	    b=B;

    
   	 while(r>=b)
       	 {
       		 b=2*b;
         }

    
    	while(b!=B)
        {
        q=2*q;
        b=b/2;

        if (r>=b) 
            {
            q=q+1;
            r=r-b;
            }

        }
	}
	

}
