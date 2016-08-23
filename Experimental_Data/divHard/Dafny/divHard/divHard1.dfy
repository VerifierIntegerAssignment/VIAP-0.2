method divHard(X: int,Y: int) returns (q: int,r: int)
requires X>=0
ensures X==Y*q+r;
{
    q := 0;
    r := X;
    var p: int := 1;
    var ds: int := Y;
    while ( r>= ds )
    {
        ds:=2*ds;
        p:=2*p;
    }
    
    while ( p!=1 )
    {
        ds:=ds/2;
        p:=p/2;
    
       if ( r>=ds ) 
       {
          r:=r-ds;
          q:=q+p;
       }
    }
}

