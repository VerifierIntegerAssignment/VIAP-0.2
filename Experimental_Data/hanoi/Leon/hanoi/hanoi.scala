import leon.lang._

object hanoi {

    def hanoi(x: Int): Int=({
	require(x > 0)
        var i: Int = 1
        var h: Int = 1
  	while (i < x) {

    		h=2*h+1
    		i=i+1     
  	}
      h
    })ensuring(_ == power(2,x)-1) 


def power(a: Int,b: Int): Int = { 
        require(a >= 0 && b >= 0)
        if (a == 0 && b>0) 0
        else if (b == 0) 1
        else    power(a,b-1)*a
    }

}


	
