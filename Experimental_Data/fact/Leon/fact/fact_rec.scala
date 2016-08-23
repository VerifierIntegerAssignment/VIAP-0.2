import leon.lang._

object fact {

   def fact(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 1
        else    fact(X-1)*X
    })ensuring(res=>res ==fact(X)) 


}



