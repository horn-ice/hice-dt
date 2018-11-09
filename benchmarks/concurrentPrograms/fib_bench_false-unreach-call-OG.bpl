/*


				Pre := {(i == 1)&&(j == 1)}

			
	S1		k_1 := 0;						k_2 := 0;
		P0:						Q0:		
	s2		while (k_1 < 1) {					while (k_2 < 1) {
		P2:						Q2:
	S3			i := i + j;						j := j + i;
				k_1 := k_1 + 1;						k_2 := k_2 + 1;
		
			}							}				
		P5:						Q5:

				Post:= (i >= 2 && j >= 2)



function {:existential true} {:inline} P0(i: int, j: int, k_1: int, k_2: int) : bool {
	(i == 1)&&(j == 1)&&(k_1 == 0)&&(k_2 == 0)
}
function {:existential true} {:inline} P1(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 1)&&(k_1 == 0)&&(k_2 >= 0)) || ((i >= 2)&&(j >= 1)&&(k_1 >= 1)&&(k_2 >= 0))
}
function {:existential true} {:inline} P2(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 1)&&(k_1 == 0)&&(k_2 >= 0))
}
function {:existential true} {:inline} P3(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 2)&&(j >= 1)&&(k_1 >= 0)&&(k_2 >= 0))
}
function {:existential true} {:inline} P4(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 2)&&(j >= 1)&&(k_1 >= 1)&&(k_2 >= 0))
}
function {:existential true} {:inline} P5(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 2)&&(j >= 1)&&(k_1 >= 1)&&(k_2 >= 0))
}


function {:existential true} {:inline} Q0(i: int, j: int, k_1: int, k_2: int) : bool {
	(i == 1)&&(j == 1)&&(k_1 == 0)&&(k_2 == 0)
}
function {:existential true} {:inline} Q1(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 1)&&(k_1 >= 0)&&(k_2 == 0)) || ((i >= 1)&&(j >= 2)&&(k_1 >= 0)&&(k_2 >= 1))
}
function {:existential true} {:inline} Q2(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 1)&&(k_1 >= 0)&&(k_2 == 0))
}
function {:existential true} {:inline} Q3(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 2)&&(k_1 >= 0)&&(k_2 >= 0))
}
function {:existential true} {:inline} Q4(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 2)&&(k_1 >= 0)&&(k_2 >= 1))
}
function {:existential true} {:inline} Q5(i: int, j: int, k_1: int, k_2: int) : bool {
	((i >= 1)&&(j >= 2)&&(k_1 >= 0)&&(k_2 >= 1))
}

*/

function {:existential true} {:inline} P0(i: int, j: int, k_1: int) : bool;
function {:existential true} {:inline} P2(i: int, j: int, k_1: int) : bool;
function {:existential true} {:inline} P5(i: int, j: int, k_1: int) : bool;
function {:existential true} {:inline} Q0(i: int, j: int, k_2: int) : bool;
function {:existential true} {:inline} Q2(i: int, j: int, k_2: int) : bool;
function {:existential true} {:inline} Q5(i: int, j: int, k_2: int) : bool;

var i: int;
var j: int;
var k_1: int;
var k_2: int;

procedure pre_condition()
modifies k_1;
modifies k_2;
requires i == 1 && j == 1;
{ 
	k_1 := 0;
	k_2 := 0;
	assert P0(i, j, k_1);
  	assert Q0(i, j, k_2);
}

procedure post_condition()
requires P5(i, j, k_1);
requires Q5(i, j, k_2);
{ 
  	assert (i >= 2 && j >= 2);
}


procedure t1_transition_s2_entry()
requires P0(i, j, k_1);
{ 
	if (k_1 < 1) {
		assert P2(i, j, k_1);
	} else {
		assert P5(i, j, k_1);
	}
} 


procedure t1_transition_s3()
modifies i; 
modifies k_1; 
requires P2(i, j, k_1);
ensures P5(i, j, k_1);
{ 
	i := i + j;
	k_1 := k_1 + 1;
}

procedure t2_transition_s2_entry()
requires Q0(i, j, k_2);
{ 
	if (k_2 < 1) {
		assert Q2(i, j, k_2);
	} else {
		assert Q5(i, j, k_2);
	}
} 
 

procedure t2_transition_s3()
modifies j; 
modifies k_2; 
requires Q2(i, j, k_2);
ensures Q5(i, j, k_2);
{ 
	j := j + i;
	k_2 := k_2 + 1;
}



procedure P0_stable_t2_s3() 
modifies j; 
requires P0(i, j, k_1);
requires Q2(i, j, k_2);
requires P0(i, j, k_1);
{ 
	j := j + i;
}

procedure P2_stable_t2_s3() 
modifies j; 
requires P2(i, j, k_1);
requires Q2(i, j, k_2);
requires P2(i, j, k_1);
{ 
	j := j + i;
}

procedure P5_stable_t2_s3() 
modifies j; 
requires P5(i, j, k_1);
requires Q2(i, j, k_2);
requires P5(i, j, k_1);
{ 
	j := j + i;
}

procedure Q0_stable_t1_s3() 
modifies i; 
requires Q0(i, j, k_1);
requires P2(i, j, k_2);
requires Q0(i, j, k_1);
{ 
	i := i + j;
}

procedure Q2_stable_t1_s3() 
modifies i; 
requires Q2(i, j, k_1);
requires P2(i, j, k_2);
requires Q2(i, j, k_1);
{ 
	i := i + j;
}


procedure Q5_stable_t1_s3() 
modifies i; 
requires Q5(i, j, k_1);
requires P2(i, j, k_2);
requires Q5(i, j, k_1);
{ 
	i := i + j;
}
