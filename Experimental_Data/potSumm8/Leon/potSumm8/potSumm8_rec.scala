object potSumm8 {
        
     def potSumm8(X: Int): Int = ({ 
        require(X >= 0 && X<=20)
        if (X == 0) 0
        else    potSumm8(X-1)+X*X*X*X*X*X*X*X
    })ensuring(_ == (10*X*X*X*X*X*X*X*X*X+45*X*X*X*X*X*X*X*X+60*X*X*X*X*X*X*X-42*X*X*X*X*X+20*X*X*X-3*X)/90)
     
     }
