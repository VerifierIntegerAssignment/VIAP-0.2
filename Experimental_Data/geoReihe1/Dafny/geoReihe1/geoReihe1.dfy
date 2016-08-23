method geoReihe1(Z: int,K: int) returns (m: int)
requires Z>1 && K>0
ensures m == ((power(Z,K)-1)/(Z-1))*(Z-1);
{
    m := 1;    
    var l: int := Z;
    var k: int := 1;
    while (k < K)
    {
        k := k + 1;
        m := m*Z + 1;
    	l := Z*l;
    }
    m := m *(Z -1);
}

function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (a == 0) then 0 else if (b == 0) then 1 else power(a,b-1)*a
}	
