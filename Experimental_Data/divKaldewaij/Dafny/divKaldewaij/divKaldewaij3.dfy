method divKaldewaij(A: int,B: int) returns (q: int,r: int)
requires A>=0 && B>0
ensures r<B;
{
    q := 0;
    r := A;
    var b: int := B;
    while(r>=b)
    {
       b:=2*b;
    }
 
    while(b!=B)
    {
        q:=2*q;
        b:=b/2;

        if (r>=b) 
        {
            q:=q+1;
            r:=r-b;
        }

     }
}
