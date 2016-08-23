function geoReihe3(a: int,Z: int,K: int) : int
requires a>0
requires Z>1
requires K>0
ensures geoReihe3(a,Z,K) == ((power(Z,K)-1)/(Z-1))*a;
{
        if (K == 1) then a else geoReihe3(a,Z,K-1)+a*power(Z,K)
}
function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (a == 0) then 0 else if (b == 0) then 1 else power(a,b-1)*a
}
