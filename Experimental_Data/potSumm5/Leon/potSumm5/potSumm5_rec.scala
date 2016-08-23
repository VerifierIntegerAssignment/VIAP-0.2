object potSumm5 {
        
     def potSumm5(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 0
        else    potSumm5(X-1)+X*X*X*X*X
    })ensuring(_ == (2*X*X*X*X*X*X+6*X*X*X*X*X+5*X*X*X*X-X*X)/12)
     
     }
