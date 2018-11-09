/*
				T1							T2
					Pre := {data1 == 0, data2 == 2}					
					
		P0							Q0

((data1 == 0)||(data1 == 2))&&((data2 == 2)||(data2 == 0))		((data1 == 0)||(data1 == 1))&&((data2 == 2)||(data2 == 3))


		  	s1:	data1 := data1 + 1;					data1 := data1 + 2;
		P1							Q1

((data1 == 1)||(data1 == 3))&&((data2 == 2)||(data2 == 0))		((data1 == 2)||(data1 == 3))&&((data2 == 2)||(data2 == 3))


			s2:	data2 := data2 + 1;					data2 := data2 - 2;
		P2							Q2

((data1 == 1)||(data1 == 3))&&((data2 == 3)||(data2 == 1))		((data1 == 2)||(data1 == 3))&&((data2 == 0)||(data2 == 1))

					Post := {data1 == 3, data2 == 1}




function {:existential true} {:inline} P0(data1: int, data2: int) : bool {
  ((data1 == 0)||(data1 == 2))&&((data2 == 2)||(data2 == 0))
}
function {:existential true} {:inline} P1(data1: int, data2: int) : bool {
  ((data1 == 1)||(data1 == 3))&&((data2 == 2)||(data2 == 0))
}
function {:existential true} {:inline} P2(data1: int, data2: int) : bool {
  ((data1 == 1)||(data1 == 3))&&((data2 == 3)||(data2 == 1))
}
function {:existential true} {:inline} Q0(data1: int, data2: int) : bool {
  ((data1 == 0)||(data1 == 1))&&((data2 == 2)||(data2 == 3))  
}
function {:existential true} {:inline} Q1(data1: int, data2: int) : bool {
  ((data1 == 2)||(data1 == 3))&&((data2 == 2)||(data2 == 3))
}
function {:existential true} {:inline} Q2(data1: int, data2: int) : bool {
  ((data1 == 2)||(data1 == 3))&&((data2 == 0)||(data2 == 1))  
}
	
*/

var data1: int;
var data2: int;

function {:existential true} {:inline} P0(data1: int, data2: int) : bool;
function {:existential true} {:inline} P1(data1: int, data2: int) : bool;
function {:existential true} {:inline} P2(data1: int, data2: int) : bool;
function {:existential true} {:inline} Q0(data1: int, data2: int) : bool;
function {:existential true} {:inline} Q1(data1: int, data2: int) : bool;
function {:existential true} {:inline} Q2(data1: int, data2: int) : bool;

procedure pre_condition()
requires data1 == 0&&data2 == 2;
{ 
	assert P0(data1, data2);
  	assert Q0(data1, data2);
}

procedure post_condition()
requires P2(data1, data2);
requires Q2(data1, data2);
{ 
  	assert data1 == 3 && data2 == 1;
}


procedure t1_transition_s1()
modifies data1; 
requires P0(data1, data2);
ensures P1(data1, data2);
{ 
	data1 := data1 + 1;
}

procedure t1_transition_s2()
modifies data2; 
requires P1(data1, data2);
ensures P2(data1, data2);
{ 
	data2 := data2 + 1;
}

procedure t2_transition_s1()
modifies data1; 
requires Q0(data1, data2);
ensures Q1(data1, data2);
{ 
	data1 := data1 + 2;
}

procedure t2_transition_s2()
modifies data2; 
requires Q1(data1, data2);
ensures Q2(data1, data2);
{ 
	data2 := data2 - 2;
}

procedure P0_Stable_t2_s1()
modifies data1; 
requires P0(data1, data2);
requires Q0(data1, data2);
ensures P0(data1, data2);
{ 
	data1 := data1 + 2;
}

procedure P1_Stable_t2_s1()
modifies data1; 
requires P1(data1, data2);
requires Q0(data1, data2);
ensures P1(data1, data2);
{ 
	data1 := data1 + 2;
}

procedure P2_Stable_t2_s1()
modifies data1; 
requires P2(data1, data2);
requires Q0(data1, data2);
ensures P2(data1, data2);
{ 
	data1 := data1 + 2;
}

procedure P0_Stable_t2_s2()
modifies data2; 
requires P0(data1, data2);
requires Q1(data1, data2);
ensures P0(data1, data2);
{ 
	data2 := data2 - 2;
}

procedure P1_Stable_t2_s2()
modifies data2; 
requires P1(data1, data2);
requires Q1(data1, data2);
ensures P1(data1, data2);
{ 
	data2 := data2 - 2;
}

procedure P2_Stable_t2_s2()
modifies data2; 
requires P2(data1, data2);
requires Q1(data1, data2);
ensures P2(data1, data2);
{ 
	data2 := data2 - 2;
}

procedure Q0_Stable_t1_s1()
modifies data1; 
requires P0(data1, data2);
requires Q0(data1, data2);
ensures Q0(data1, data2);
{ 
	data1 := data1 + 1;
}

procedure Q1_Stable_t1_s1()
modifies data1; 
requires P0(data1, data2);
requires Q1(data1, data2);
ensures Q1(data1, data2);
{ 
	data1 := data1 + 1;
}

procedure Q2_Stable_t1_s1()
modifies data1; 
requires P0(data1, data2);
requires Q2(data1, data2);
ensures Q2(data1, data2);
{ 
	data1 := data1 + 1;
}

procedure Q0_Stable_t1_s2()
modifies data2; 
requires P1(data1, data2);
requires Q0(data1, data2);
ensures Q0(data1, data2);
{ 
	data2 := data2 + 1;
}

procedure Q1_Stable_t1_s2()
modifies data2; 
requires P1(data1, data2);
requires Q1(data1, data2);
ensures Q1(data1, data2);
{ 
	data2 := data2 + 1;
}


procedure Q2_Stable_t1_s2()
modifies data2; 
requires P1(data1, data2);
requires Q2(data1, data2);
ensures Q2(data1, data2);
{ 
	data2 := data2 + 1;
}
