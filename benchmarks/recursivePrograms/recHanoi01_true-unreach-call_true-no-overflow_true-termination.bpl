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

function {:existential true} {:inline} Req_applyHanoi (n: int, counter: int) : bool;

function {:existential true} {:inline} Ens_applyHanoi (n: int, old_counter: int, counter: int) : bool;

/*
 * This function returns the optimal amount of steps,
 * needed to solve the problem for n-disks
 */

var counter: int;

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

procedure applyHanoi (n: int, from: int, to: int, via: int)
modifies counter;
requires Req_applyHanoi (n, counter);
ensures Ens_applyHanoi (n, old(counter), counter);
{
	if (n != 0) {

		counter := counter + 1;

		call applyHanoi (n - 1, from, via, to);

		call applyHanoi (n - 1, via, to, from);
	}
}

procedure main ()
modifies counter;
{
	var n, result: int;
	
	havoc n;
	
	assume (!(n < 1 || n > 31));

	counter := 0;
	
	call applyHanoi(n, 1, 3, 2);

    	call result := hanoi(n);

	assert (result == counter);
}
