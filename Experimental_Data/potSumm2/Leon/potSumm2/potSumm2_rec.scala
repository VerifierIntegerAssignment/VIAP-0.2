object potSumm2 {
        
     def potSumm2(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 0
        else    potSumm2(X-1)+X*X
    })ensuring(_ == X*(X+1)*(2*X+1)/6)
     
     }
