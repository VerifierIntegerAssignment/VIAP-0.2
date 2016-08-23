method divDafny(X: int,Y:int) returns (r: int,q:int)
requires X>=0 && Y>0
ensures X==Y*q+r;
{
       
    r:= X;
    q:= 0;
    while(r >= Y) {
      	r := r - Y;
      	q := q + 1;
    }
}
