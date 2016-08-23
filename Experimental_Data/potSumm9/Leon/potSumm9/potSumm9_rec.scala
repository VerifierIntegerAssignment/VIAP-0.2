object potSumm9 {
        
     def potSumm9(X: Int): Int = ({ 
        require(X >= 0 && X<=20)
        if (X == 0) 0
        else    potSumm9(X-1)+X*X*X*X*X*X*X*X*X
    })ensuring(_ == (2*X*X*X*X*X*X*X*X*X*X+10*X*X*X*X*X*X*X*X*X+15*X*X*X*X*X*X*X*X-14*X*X*X*X*X*X+10*X*X*X*X-3*X*X)/20)
     
     }
