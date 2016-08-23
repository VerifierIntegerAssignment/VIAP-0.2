object potSumm3 {
        
     def potSumm3(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 0
        else    potSumm3(X-1)+X*X*X
    })ensuring(_ == X*(X+1)*X*(X+1)/4)
     
     }
