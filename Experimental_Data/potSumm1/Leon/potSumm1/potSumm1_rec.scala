object potSumm1 {
        
     def potSumm1(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 0
        else    potSumm1(X-1)+X
    })ensuring(_ == X*(X+1)/2)
     
     }
