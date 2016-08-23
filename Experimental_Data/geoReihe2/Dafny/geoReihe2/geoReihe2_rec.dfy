function geoReihe2(Z: int,K: int) : int
requires Z>1
requires K>0
ensures geoReihe2(Z,K) == ((power(Z,K)-1)/(Z-1))*(Z-1);
{
        if (K == 1) then (Z-1) else geoReihe2(Z,K-1)+(Z-1)*power(Z,K)
}
function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (a == 0) then 0 else if (b == 0) then 1 else power(a,b-1)*a
}
