import leon.lang._

object hanoi {

    def hanoi(x: Int): Int=({
        require(x > 0)
        if (x == 1) 1
        else    2*hanoi(x-1)+1
    })ensuring(_ == power(2,x)-1) 


     def power(a: Int,b: Int): Int = { 
        require(a >= 0 && b >= 0)
        if (b == 0) 1
        else    power(a,b-1)*a
    }

}



