
public class geoReihe2{


	public void geoReihe2(int Z,int K) {

		int m;
  		int l;
  		int c;
		m = 1;
  		l = 1;
  		c = 1;

  		while (c < K){
    			 c = c + 1;
    			 m = m*Z + 1;
    			 l = l*Z;
  		}

  		m = m *(Z -1);
	}

}
