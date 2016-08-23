object sumodd {
        
     def sumodd(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 0
        else    sumodd(X-1)+X*2+1
    })ensuring(_ == X*(X+2))
     
     }
