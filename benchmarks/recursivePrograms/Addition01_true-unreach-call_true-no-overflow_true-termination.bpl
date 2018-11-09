function {:existential true} {:inline} Req(m: int, n: int) : bool;
function {:existential true} {:inline} Ens(m: int, n: int) : bool;

procedure addition (m: int, n: int) returns (result: int)
requires Req(m, n);
ensures Ens(m + n - result, result - m - n); 
{

	if (n == 0) {	
	
		result := m;

		assert  Ens(0, 0);
	
	} else if (n > 0) {        	
	
		call result := addition(m + 1, n - 1);
	
	} else  if (n < 0) {
	
		call result := addition(m - 1, n + 1);
	}
}

procedure main ()
{
	var m, n, result: int;

	havoc m;
	
	havoc n;
	
	assume (!(m < 0 || m > 1073741823));
	
	assume (!(n < 0 || n > 1073741823));
	
	call result := addition(m, n);
	
	assert (result == m + n); 
}

