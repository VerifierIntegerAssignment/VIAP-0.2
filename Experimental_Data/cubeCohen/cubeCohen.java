
public class cubeCohen{


	public void cubeCohen(int X) {

	
		 int i,m,y,z;
		i=1;
 		m=0;   
		y=1;   
		z=6;
   
    	while( i<=X )
        {
               	i=i+1;
        	m=m+y;
        	y=y+z;
        	z=z+6;
        }
		
	}

}
