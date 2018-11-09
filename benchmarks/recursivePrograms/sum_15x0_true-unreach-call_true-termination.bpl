/*
function {:existential true} {:inline} Req(n: int, m: int) : bool {
  true
}
function {:existential true} {:inline} Ens(n: int, m: int, result: int) : bool{
  result == m + n
}
*/
function {:existential true} {:inline} Req(n: int, m: int) : bool;
function {:existential true} {:inline} Ens(x: int, y: int) : bool;

procedure sum(n: int, m: int) returns (result: int)
requires Req(n, m);
ensures Ens(m + n - result, result - m - n); 
{
	var temp_result: int;
	
	if (n <= 0) {	
	
		result := m + n;

	} else {	
	
	
		call result := sum(n - 1, m + 1);
		
	}
}  	

procedure main ()
{
	var a: int;
	
	var b: int;
	
	var result: int;
	
	a := 15;
	
	b := 0;
	
	call result := sum(a, b);
	
	assert (result == a + b); 
	
}

