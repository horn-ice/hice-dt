/*
 * Recursive implementation integer addition.
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */
function {:existential true} {:inline} Req_Even(n: int) : bool;
function {:existential true} {:inline} Ens_Even(n: int, result: int) : bool;


function {:existential true} {:inline} Req_Odd(n: int) : bool;
function {:existential true} {:inline} Ens_Odd(n: int, result: int) : bool;


procedure isOdd (n: int) returns (result: int)
requires Req_Odd(n);
ensures Ens_Odd(n, result); 
{

	if (n == 0) {	

		result := 0;

		assert Ens_Odd(0, 0);
	
	} else if (n == 1) {

        	result := 1;

		assert Ens_Odd(1, 1);

    	} else {

		call result := isEven(n - 1);
	}
}

procedure isEven (n: int) returns (result: int)
requires Req_Even(n);
ensures Ens_Even(n, result); 
{

	if (n == 0) {	

		result := 1;

		assert Ens_Even(0, 1);
	
	} else if (n == 1) {

        	result := 0;

		assert Ens_Even(1, 0);

    	} else {

		call result := isOdd(n - 1);
	}
}

procedure main ()
{
	var n, modVal, result: int;
	
	havoc n;
	
	assume (!(n < 0));

	call result := isOdd(n);

	modVal := n mod 2;

	assert (result < 0 || result == modVal);
}

