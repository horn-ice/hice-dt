/*
    		T1                                                       T2

					Pre:= {x == 0, y == 0}
	P0							Q0
            	S1:    while (*) {                			S1:    while (*) {
	P1							Q1
           	S2:        if (x < y) {                    		S2:        if (y < 4) {
	P2							Q2
		S3:            x := x + 1                          	S3:            y := y + 3               
		     	   }                                       	           }
	P3							Q3
		       }                                                       }
	P4							Q4
					 
                                    	Post:= {x <= y}

*/

var x: int;
var y: int;

function {:existential true} {:inline} P0(x: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, y: int) : bool;
function {:existential true} {:inline} P2(x: int, y: int) : bool;
function {:existential true} {:inline} P3(x: int, y: int) : bool;
function {:existential true} {:inline} P4(x: int, y: int) : bool;

function {:existential true} {:inline} Q0(x: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, y: int) : bool;
function {:existential true} {:inline} Q3(x: int, y: int) : bool;
function {:existential true} {:inline} Q4(x: int, y: int) : bool;

procedure pre_condition()
requires x == 0 && y == 0;
{ 
	assert P0(x, y);
  	assert Q0(x, y);
}

procedure post_condition()
requires P4(x, y);
requires Q4(x, y);
{ 
  	assert (x <= y);
}

procedure t1_transition_s3()
modifies x;
requires P2(x, y);
ensures P3(x, y);
{ 
	x := x + 1;
}

procedure t1_transition_s2()
requires P1(x, y);
{ 
	if(x < y) {
		assert P2(x, y);
	} else {
		assert P3(x, y);
	} 
}


procedure t1_transition_s1_entry() 
requires P0(x, y);
{ 
	if(*) {
		assert P1(x, y);
	} else {
		assert P4(x, y);
	} 
}

procedure t1_transition_s1_body()
requires P3(x, y);
{ 
	assert P0(x, y);
}

procedure t2_transition_s3()
modifies y;
requires Q2(x, y);
ensures Q3(x, y);
{ 
	y := y + 3;
}

procedure t2_transition_s2()
requires Q1(x, y);
{ 
	if(y < 4) {
		assert Q2(x, y);
	} else {
		assert Q3(x, y);
	} 
}


procedure t2_transition_s1_entry() 
requires Q0(x, y);
{ 
	if(*) {
		assert Q1(x, y);
	} else {
		assert Q4(x, y);
	} 
}

procedure t2_transition_s1_body()
requires Q3(x, y);
{ 
	assert Q0(x, y);
}


procedure P0_Stable_t2_s3()
modifies y; 
requires P0(x, y);
requires Q2(x, y);
ensures P0(x, y);
{ 
	y := y + 3;
}

procedure P1_Stable_t2_s3()
modifies y; 
requires P1(x, y);
requires Q2(x, y);
ensures P1(x, y);
{ 
	y := y + 3;
}

procedure P2_Stable_t2_s3()
modifies y; 
requires P2(x, y);
requires Q2(x, y);
ensures P2(x, y);
{ 
	y := y + 3;
}

procedure P3_Stable_t2_s3()
modifies y; 
requires P3(x, y);
requires Q2(x, y);
ensures P3(x, y);
{ 
	y := y + 3;
}

procedure P4_Stable_t2_s3()
modifies y; 
requires P4(x, y);
requires Q2(x, y);
ensures P4(x, y);
{ 
	y := y + 3;
}

procedure Q0_Stable_t1_s3()
modifies x; 
requires Q0(x, y);
requires P2(x, y);
ensures Q0(x, y);
{ 
	x := x + 1;
}

procedure Q1_Stable_t1_s3()
modifies x; 
requires Q1(x, y);
requires P2(x, y);
ensures Q1(x, y);
{ 
	x := x + 1;
}

procedure Q2_Stable_t1_s3()
modifies x; 
requires Q2(x, y);
requires P2(x, y);
ensures Q2(x, y);
{ 
	x := x + 1;
}

procedure Q3_Stable_t1_s3()
modifies x; 
requires Q3(x, y);
requires P2(x, y);
ensures Q3(x, y);
{ 
	x := x + 1;
}

procedure Q4_Stable_t1_s3()
modifies x; 
requires Q4(x, y);
requires P2(x, y);
ensures Q4(x, y);
{ 
	x := x + 1;
}

