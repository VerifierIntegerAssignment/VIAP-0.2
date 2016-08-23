object potSumm7 {
        
     def potSumm7(X: Int): Int = ({ 
        require(X >= 0 && X<=20)
        if (X == 0) 0
        else    potSumm7(X-1)+X*X*X*X*X*X*X
    })ensuring(_ == (3*X*X*X*X*X*X*X*X+12*X*X*X*X*X*X*X+14*X*X*X*X*X*X-7*X*X*X*X+2*X*X)/24)
     
     }
