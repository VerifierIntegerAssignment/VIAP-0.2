object potSumm10 {
        
     def potSumm10(X: Int): Int = ({ 
        require(X >= 0 && X<10)
        if (X == 0) 0
        else    potSumm10(X-1)+X*X*X*X*X*X*X*X*X*X
    })ensuring(_ == (6*X*X*X*X*X*X*X*X*X*X*X+33*X*X*X*X*X*X*X*X*X*X+55*X*X*X*X*X*X*X*X*X-66*X*X*X*X*X*X*X+66*X*X*X*X*X-33*X*X*X+5*X)/66)
     
     }
