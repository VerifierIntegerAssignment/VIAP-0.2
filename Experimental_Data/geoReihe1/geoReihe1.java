
public class geoReihe1{


	public void geoReihe1(int Z,int K) {

		int m ;
  		int l;
  		int k;
		m = 1;
  		l = Z;
  		k = 1;

  		while (k < K){
    			k = k + 1;
    			m = m*Z + 1;
    			l = Z*l;
  		}

  		m = m *(Z -1);
	}

}
