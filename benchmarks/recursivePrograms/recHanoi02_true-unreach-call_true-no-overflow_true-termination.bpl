/*
 * recHanoi.c
 *
 *  Created on: 17.07.2013
 *      Author: Stefan Wissert
 *
 * Copied from c/termination-numeric/recHanoi02_true-termination.c
 */

function {:existential true} {:inline} Req_hanoi (n: int) : bool;

function {:existential true} {:inline} Ens_hanoi (n: int, result: int) : bool;

/*
 * This function returns the optimal amount of steps,
 * needed to solve the problem for n-disks
 */

procedure hanoi (n: int) returns (result: int)
requires Req_hanoi (n);
ensures Ens_hanoi (n, result); 
{
	if (n == 1) {

        	result := 1; 

		assert (Ens_hanoi (1, 1));

    	} else {

		call result := hanoi (n - 1);

		result := 2 * result + 1;
	}
}

procedure main ()
{
	var n, result: int;
	
	havoc n;
	
	assume (!(n < 1 || n > 31));

    	call result := hanoi(n);

	assert (result >= 0);
}
