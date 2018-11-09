/*
 * Recursive implementation of prime number test
 * (Sieve of Eratosthenes)
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

function {:existential true} {:inline} Req_multiply (n: int, m: int) : bool;

function {:existential true} {:inline} Ens_multiply (n: int, m: int, result: int) : bool;

function {:existential true} {:inline} Req_multiple_of (n: int, m: int) : bool;

function {:existential true} {:inline} Ens_multiple_of (n: int, m: int, result: int) : bool;

function {:existential true} {:inline} Req_is_prime_ (n: int, m: int) : bool;

function {:existential true} {:inline} Ens_is_prime_ (n: int, m: int, result: int) : bool;

function {:existential true} {:inline} Req_is_prime (n: int) : bool;

function {:existential true} {:inline} Ens_is_prime (n: int, result: int) : bool;

// multiplyiplies two integers n and m
procedure multiply (n: int, m: int) returns (result: int)
requires Req_multiply (n, m);
ensures Ens_multiply (n, m, result); 
{
	if (m < 0) {
	
		call result := multiply (n, - m);
	
	} else if (m == 0) {

        	result := 0; 

		assert (Ens_multiply (n, 0, 0));

    	} else if (m == 1) {

        	result := 1; 

		assert (Ens_multiply (n, 1, 1));

    	} else {

		call result := multiply (n, m - 1);

		result := result + n;
	}
}

// Is n a multiplyiple of m?
procedure multiple_of (n: int, m: int) returns (result: int)
requires Req_multiple_of (n, m);
ensures Ens_multiple_of (n, m, result); 
{
	if (m < 0) {
	
		call result := multiple_of (n, -m);
	
	} else if (n < 0) {
	
		call result := multiple_of (-n, m);
	
	} else if (m == 0) {

        	result := 0; 

		assert (Ens_multiple_of (n, 0, 0));

    	} else if (n == 0) {

        	result := 1; 

		assert (Ens_multiple_of (0, m, 1));

    	} else {

		call result := multiple_of(n - m, m);
	}
}


// Is n prime?
procedure is_prime (n: int) returns (result: int)
requires Req_is_prime (n);
ensures Ens_is_prime (n, result); 
{
	call result := is_prime_ (n, n - 1);
}


procedure is_prime_ (n: int, m: int) returns (result: int)
requires Req_is_prime_ (n, m);
ensures Ens_is_prime_ (n, m, result); 
{
	var temp_result: int;

	if (n <= 1) {
	
		result := 0; 

		assert (Ens_is_prime_ (n, m, 0));
	
	} else if (n == 2) {

        	result := 1; 

		assert (Ens_is_prime_ (2, m, 1));

    	} else if (n > 2) {
        
		if (m <= 1) {
            
			result := 1; 

			assert (Ens_is_prime_ (n, m, 1));
        	
		} else {

			call temp_result := multiple_of(n - m, m);
            
			if (temp_result == 0) {
                
				result := 0; 

				assert (Ens_is_prime_ (n, m, 0));
            		}

			call result := is_prime_(n, m - 1);
        	}
	}
}

procedure main ()
{
	var f1, f2, n, result, result_multiply: int;
	
	havoc n;

	havoc f1;

	havoc f2;
	
	assume (!(n < 1 || n > 46340));
	
	assume (!(f1 < 1 || f1 > 46340));
	
	assume (!(f2 < 1 || f2 > 46340));

    	call result := is_prime(n);

	call result_multiply := multiply(f1, f2);

	assert (!(result == 1 && result_multiply == n && f1 > 1 && f2 > 1));
}

