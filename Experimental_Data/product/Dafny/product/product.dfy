method product(a: int,b: int) returns (A: int)
requires a>=0
requires b>=0
ensures A == a*b;
{
    A := 0;    
    var J: int := 0;
    while (J<b)
    {
     A := A + a; J := J + 1;
    }
}


