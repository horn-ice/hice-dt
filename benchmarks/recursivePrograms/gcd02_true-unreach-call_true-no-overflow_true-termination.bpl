/*
 * Recursive implementation of the greatest common denominator
 * using Euclid's algorithm
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */


function {:existential true} {:inline} Req_gcd (y1: int, y2: int) : bool;

function {:existential true} {:inline} Ens_gcd (y1: int, y2: int, result: int) : bool;

function {:existential true} {:inline} Req_divides (n: int, m: int) : bool;

function {:existential true} {:inline} Ens_divides (n: int, m: int, result: int) : bool;

// Compute the greatest common denominator using Euclid's algorithm
procedure gcd (y1: int, y2: int) returns (result: int)
requires Req_gcd (y1, y2);
ensures Ens_gcd (y1, y2, result); 
{
	if (y1 <= 0 || y2 <= 0) {
	
		assert false;
	
	} else if (y1 == y2) {

        	result := y1; 

		assert (Ens_gcd (y1, y1, y1));

    	} else if (y1 > y2) {

        	call result := gcd (y1 - y2, y2);

    	} else {

		call result := gcd (y1, y2 - y1);
	}
}

// Compute the greatest common denominator using Euclid's algorithm
procedure divides (n: int, m: int) returns (result: int)
requires Req_divides (n, m);
ensures Ens_divides (n, m, result); 
{
	if (m == 0) {
	
		result := 1; 

		assert (Ens_divides (n, 0, 1));
	
	} else if (n > m) {

        	result := 0; 

		assert (Ens_divides (n, m, 0));

    	} else {

		call result := divides (n, m - n);
	}
}

procedure main ()
{
	var m, n, z, d: int;

	havoc m;
	
	havoc n;
	
	assume (!(m <= 0 || m > 2147483647));
	
	assume (!(n <= 0 || n > 2147483647));
	
	assume (m > 0 && n > 0);

	call z := gcd (m, n);
	
	call d := divides (z, m);

	assert (d != 0);
}

