
public class cohendiv {

	/**
	 * @param args
	 */
	public static void cohendiv(int X,int Y) {
		// TODO Auto-generated method stub
		
		int q;
		int r;
		int A;
		int B;

		q=0;
		r=X;	

		
		while(r >= Y)
		{
			A=1;
			B=Y;

			while(r >= 2*B)
				{
					A=2*A;
					B=2*B;
				}
		r=r-B;
		q=q+A;
			
		}
			

		
		
	}

}
