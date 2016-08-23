function power(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (a == 0) then 0 else if (b == 0) then 1 else power(a,b-1)*a
}
lemma powerLemma(a: int,b: int)
requires a>=0
requires b>=0
ensures power(a,b) >=0;
{
}
