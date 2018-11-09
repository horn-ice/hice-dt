
function {:existential true} {:inline} Req(y1: int, y2: int) : bool;

function {:existential true} {:inline} Ens(y1: int, y2: int, result: int) : bool;

/*
 * Recursive implementation of the greatest common denominator
 * using Euclid's algorithm
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

// Compute the greatest common denominator using Euclid's algorithm
procedure gcd (y1: int, y2: int) returns (result: int)
requires Req(y1, y2);
ensures Ens(y1, y2, result); 
{
	if (y1 <= 0 || y2 <= 0) {	

		result := 0;

		assert (Ens(y1, y2, 0));
	
	} else if (y1 == y2) {

        	result := y1; 

		assert (Ens(y1, y1, y1));

    	} else if (y1 > y2) {

        	call result := gcd (y1 - y2, y2);

    	} else {

		call result := gcd (y1, y2 - y1);
	}
}

procedure main ()
{
	var m, n, z: int;

	havoc m;
	
	havoc n;
	
	assume (!(m <= 0 || m > 2147483647));
	
	assume (!(n <= 0 || n > 2147483647));

	call z := gcd (m, n);

	assert (!(z < 1 && m > 0 && n > 0));
}

