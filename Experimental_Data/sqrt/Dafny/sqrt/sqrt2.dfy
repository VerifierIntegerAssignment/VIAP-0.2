method sqrt(X: int) returns (a: int)
requires X>=0
ensures a*a<=X;
{

    a := 0;
    var su: int := 1;
    var t: int := 1;
    while (su <= X)
    {
     a := a + 1; t := t + 2; su := su + 2;
    }
}


