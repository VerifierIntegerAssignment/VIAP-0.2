object sumEven {
        
     def sumOfEven(X: Int): Int = ({ 
        require(X >= 0)
        if (X == 0) 0
        else    sumOfEven(X-1)+X*2
    })ensuring(_ == X*(X+1))
     
     }
