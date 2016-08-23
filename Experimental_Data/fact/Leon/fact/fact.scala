import leon.lang._

object fact {

    def fact(X: Int): Int=({
	require(X >= 0)
        var i: Int = 1
        var F: Int = 1
  	while (i <= X) {

    		F=F*i
    		i=i+1     
  	}
      F
    })ensuring(res=>res ==factorial(X)) 


     def factorial(n: Int): Int = { 
        require(n >= 0)
        if (n == 0) 1
        else    factorial(n-1)*n
    }

}


	
