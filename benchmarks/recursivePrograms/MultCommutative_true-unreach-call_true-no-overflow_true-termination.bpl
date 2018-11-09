/*
 * Recursive implementation multiplyiplication by repeated addition
 * Check that this multiplyiplication is commutative
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

function {:existential true} {:inline} Req_multiply (n: int, m: int) : bool;

function {:existential true} {:inline} Ens_multiply (n: int, m: int) : bool;

// multiplyiplies two integers n and m
procedure multiply (n: int, m: int) returns (result: int)
requires Req_multiply (n, m);
ensures Ens_multiply ((n*m) - result, result - (m*n)); 
{
	if (m < 0) {
	
		call result := multiply (n, - m);
	
	} else if (m == 0) {

        	result := 0; 

    	} else {

		call result := multiply (n, m - 1);

		result := result + n;
	}
}

procedure main ()
{
	var m, n, res1, res2: int;

	havoc m;
	
	havoc n;
	
	assume (!(m < 0 || m > 46340));
	
	assume (!(n < 0 || n > 46340));

    	call res1 := multiply (m, n);
    
	call res2 := multiply (n, m);

	assert (!(res1 != res2 && m > 0 && n > 0));
}
