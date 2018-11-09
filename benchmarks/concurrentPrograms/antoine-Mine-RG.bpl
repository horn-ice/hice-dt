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
var new_x: int;
var new_y: int;

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

function {:existential true} {:inline} G_t1(x: int, y: int, new_x: int, new_y: int) : bool;
function {:existential true} {:inline} G_t2(x: int, y: int, new_x: int, new_y: int) : bool;

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
ensures G_t1(old(x), old(y), x, y);
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
ensures G_t2(old(x), old(y), x, y);
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


procedure P0_Stable_G_t2()
requires P0(x, y);
requires G_t2(x, y, new_x, new_y);
{ 
	assert P0(new_x, new_y);
}

procedure P1_Stable_G_t2()
requires P1(x, y);
requires G_t2(x, y, new_x, new_y);
{ 
	assert P1(new_x, new_y);
}

procedure P2_Stable_G_t2()
requires P2(x, y);
requires G_t2(x, y, new_x, new_y);
{ 
	assert P2(new_x, new_y);
}

procedure P3_Stable_G_t2()
requires P3(x, y);
requires G_t2(x, y, new_x, new_y);
{ 
	assert P3(new_x, new_y);
}

procedure P4_Stable_G_t2()
requires P4(x, y);
requires G_t2(x, y, new_x, new_y);
{ 
	assert P4(new_x, new_y);
}

procedure Q0_Stable_G_t1()
requires Q0(x, y);
requires G_t1(x, y, new_x, new_y);
{ 
	assert Q0(new_x, new_y);
}

procedure Q1_Stable_G_t1()
requires Q1(x, y);
requires G_t1(x, y, new_x, new_y);
{ 
	assert Q1(new_x, new_y);
}

procedure Q2_Stable_G_t1()
requires Q2(x, y);
requires G_t1(x, y, new_x, new_y);
{ 
	assert Q2(new_x, new_y);
}

procedure Q3_Stable_G_t1()
requires Q3(x, y);
requires G_t1(x, y, new_x, new_y);
{ 
	assert Q3(new_x, new_y);
}

procedure Q4_Stable_G_t1()
requires Q4(x, y);
requires G_t1(x, y, new_x, new_y);
{ 
	assert Q4(new_x, new_y);
}


