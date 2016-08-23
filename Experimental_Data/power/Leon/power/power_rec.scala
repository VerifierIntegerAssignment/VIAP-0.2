import leon.lang._

object power {

     def power(a: Int,b: Int): Int = ({ 
        require(a >= 0 && b >= 0)
        if (a == 0) 0
        else if (b == 0) 1 else  power(a,b-1)*a
    })ensuring(_ >=0) 

}



