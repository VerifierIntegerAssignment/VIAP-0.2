function product(a: int,b: int) : int
requires a>=0
requires b>=0
{
        if (b == 0) then 0 else product(a,b-1)+a
}
lemma factLemma(a: int,b: int)
requires a>=0
requires b>=0
ensures product(a,b) ==a*b;
{
}
