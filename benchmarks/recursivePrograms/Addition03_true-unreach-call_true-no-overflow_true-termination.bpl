/*  comment */

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

procedure main (m: int, n: int)
{
	var result: int;
	
	call result := addition(m, n);
	
	assert (m < 100 || n < 100 || result >= 200); 
}

