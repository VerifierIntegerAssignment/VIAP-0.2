method abs(X: int) returns (a: int)
ensures a >= 0;
{
	if (X<=0) { a:=-X;}
        else {a:=X;}
}


