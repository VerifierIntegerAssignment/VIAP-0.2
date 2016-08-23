
public class geoReihe3{


	public void geoReihe3(int Z,int K,int a) {

		int m;
  		int l;
  		int c;
		m = a;
  		l = 1;
  		c = 1;

  		while (c < K){
    			 c = c + 1;
    			 m = m*Z + a;
    			 l = l*Z;
  		}

	}

}
