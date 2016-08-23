import leon.lang._

object product {

     def product(a: Int,b: Int): Int = ({ 
        require(a >= 0 && b >= 0)
        if (b == 0) 0
        else    product(a,b-1)+a
    })ensuring(_ == a*b) 


}



