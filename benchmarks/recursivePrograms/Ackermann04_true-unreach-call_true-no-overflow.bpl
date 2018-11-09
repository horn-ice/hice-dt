/*

					-------- Proof learned by HornDt---------------

function {:existential true} {:inline} Req(m: int, n: int) : bool
{
  m - n <= 0 || (0 < m - n && m <= 0 && m <= -1) || (0 < m - n && 0 < m)
}
function {:existential true} {:inline} Ens(m: int, n: int, result: int) : bool
{
  0 < result
}


*/

function {:existential true} {:inline} Req(m: int, n: int) : bool;
function {:existential true} {:inline} Ens(m: int, n: int, result: int) : bool;

procedure ackermann (m: int, n: int) returns (result: int)
requires Req(m, n);
ensures Ens(m, n, result); 
{
	var temp_result: int;

	if (m == 0) {	

		result := n + 1;
	
	} else if (n == 0) {

        	call result := ackermann(m - 1, 1); 

    	} else {

		call temp_result := ackermann(m, n - 1);

		call result := ackermann(m - 1, temp_result);
	}
}

procedure main ()
{
	var m, n, result: int;

	havoc m;
	
	havoc n;
	
	assume (!(m < 0 || m > 3));
	
	assume (!(n < 0 || n > 23));

	call result := ackermann(m, n);

	assert (m < 2 || n < 2 || result >= 7);
}








