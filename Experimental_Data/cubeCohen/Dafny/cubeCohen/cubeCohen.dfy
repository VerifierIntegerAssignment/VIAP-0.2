method cubeCohen(X: int) returns (m: int)
requires X>=0
ensures m==X*X*X;
{
    m := 0;    
    var i: int := 1;
    var y: int := 1;
    var z: int := 6;
    while (i<=X)
    {
               	i:=i+1;
        	m:=m+y;
        	y:=y+z;
        	z:=z+6;
    }
}
