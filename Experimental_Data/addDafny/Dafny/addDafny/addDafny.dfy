method addDafny(X: int,Y: int) returns (r: int)
requires X>=0
requires Y>=0
ensures r == X+Y;
{
    r := X;    
    var l: int := 1;
    if(Y < 0) 
    {
           l := Y;
           while(l != 0) 
          {
            	r := r - 1;
            	l := l + 1;
          }
     } 
     else 
     {
          l := Y;
          while(l != 0) {
            r := r + 1;
            l := l - 1;
          }
     }
}

