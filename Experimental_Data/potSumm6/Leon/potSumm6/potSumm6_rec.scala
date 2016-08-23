object potSumm6 {
        
     def potSumm6(X: Int): Int = ({ 
        require(X >= 0 && X<20)
        if (X == 0) 0
        else    potSumm6(X-1)+X*X*X*X*X*X
    })ensuring(_ == (6*X*X*X*X*X*X*X+21*X*X*X*X*X*X+21*X*X*X*X*X-7*X*X*X+X)/42)
     
     }
