object potSumm4 {
        
     def potSumm4(X: Int): Int = ({ 
        require(X >= 0 && X<=50)
        if (X == 0) 0
        else    potSumm4(X-1)+X*X*X*X
    })ensuring(_ == (6*X*X*X*X*X+15*X*X*X*X+10*X*X*X-X)/30)
     
     }
