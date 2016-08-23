import leon.lang._

object squre {

     def squre(M: Int): Int = ({ 
        require(M >= 0)
        
        squareM(M,M)
        
    })ensuring(_ == M*M) 

       def squareM(M: Int,N: Int): Int = { 
           require(M >= 0 && N >= 0)
           if (N == 0) 0
           else    squareM(M,N-1)+M
    }

}



