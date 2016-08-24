method geoReihe2(Z: int,K:int) returns (m: int)
requires Z>1 && K>0
ensures m == ((power(Z,K)-1)/(Z-1));
{
    m := 1;    
    var l: int := 1;
    var c: int := 1;
    while (c < K)
    {
    			 c := c + 1;
    			 m := m*Z + 1;
    			 l := l*Z;
    }
   
}

function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
            if (a == 0&&b>0) then 0 else if (b == 0) then 1 else power(a,b-1)*a
}

	
