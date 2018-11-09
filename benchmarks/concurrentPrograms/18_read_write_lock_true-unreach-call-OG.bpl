/*

			T1									T2


				Pre := {w == 0, r == 0}

P0:								Q0:
	w == 0 && (r == 0 || r == 1)					(w == 0 || w == 1) && r == 0

		assume(w == 0);							assume(w == 0);
	s1:	assume(r == 0);							r := r + 1;
		w := 1;
P1:								Q1:
	w == 1 && r == 0						w == 0 && r == 1

	s2:	x := 3;								y := x;
P2:								Q2:	assert(y == x);	

	w == 1 && r == 0						w == 0 && r == 1 && (x == y)
		
	s3:	w := 0;								r := r - 1;
P3:								Q3:
	w == 0 && (r == 0 || r == 1)					(w == 0 || w == 1) && r == 0


function {:existential true} {:inline} P0(w: int, r: int) : bool {
	w == 0 && (r == 0 || r == 1)
}
function {:existential true} {:inline} P1(w: int, r: int) : bool {
	w == 1 && r == 0
}
function {:existential true} {:inline} P2(w: int, r: int) : bool {
	w == 1 && r == 0
}
function {:existential true} {:inline} P3(w: int, r: int) : bool {
	w == 0 && (r == 0 || r == 1)
}

function {:existential true} {:inline} Q0(w: int, r: int) : bool {
	(w == 0 || w == 1) && r == 0
}
function {:existential true} {:inline} Q1(w: int, r: int) : bool {
	w == 0 && r == 1
}
function {:existential true} {:inline} Q2(w: int, r: int, x: int, y: int) : bool {
	w == 0 && r == 1 && (x == y)
}
function {:existential true} {:inline} Q3(w: int, r: int) : bool {
	(w == 0 || w == 1) && r == 0
}

*/

var w: int;
var r: int;
var x: int;
var y: int;

function {:existential true} {:inline} P0(w: int, r: int) : bool;
function {:existential true} {:inline} P1(w: int, r: int) : bool;
function {:existential true} {:inline} P2(w: int, r: int) : bool;
function {:existential true} {:inline} P3(w: int, r: int) : bool;

function {:existential true} {:inline} Q0(w: int, r: int) : bool;
function {:existential true} {:inline} Q1(w: int, r: int) : bool;
function {:existential true} {:inline} Q2(w: int, r: int, x: int, y: int) : bool;
function {:existential true} {:inline} Q3(w: int, r: int) : bool;

procedure pre_condition()
modifies x;
modifies y;
requires w == 0 && r == 0;
{ 
  	havoc x;
  	havoc y;
	assert P0(w, r);
  	assert Q0(w, r);
}

procedure assert_at_Q2()
requires Q2(w, r, x, y);
{ 
  	assert x == y;
}

procedure t1_transition_s1()
modifies w; 
requires P0(w, r);
ensures P1(w, r);
{ 
	assume (w == 0);
	assume (r == 0);
	w := 1;
}


procedure t1_transition_s2()
modifies x; 
requires P1(w, r);
ensures P2(w, r);
{ 
	x := 3;
}

procedure t1_transition_s3()
modifies w; 
requires P2(w, r);
ensures P3(w, r);
{ 
	w := 0;
}



procedure t2_transition_s1()
modifies r; 
requires Q0(w, r);
ensures Q1(w, r);
{ 
	assume (w == 0);
	r := r + 1;
}


procedure t2_transition_s2()
modifies y; 
requires Q1(w, r);
ensures Q2(w, r, x, y);
{ 
	y := x;
}

procedure t2_transition_s3()
modifies r; 
requires Q2(w, r, x, y);
ensures Q3(w, r);
{ 
	r := r - 1;
}

procedure P0_stable_t2_s1()
modifies r; 
requires P0(w, r);
requires Q0(w, r);
ensures P0(w, r);
{ 
	assume (w == 0);
	r := r + 1;
}

procedure P0_stable_t2_s2()
modifies y; 
requires P0(w, r);
requires Q1(w, r);
ensures P0(w, r);
{ 
	y := x;
}


procedure P0_stable_t2_s3()
modifies r; 
requires P0(w, r);
requires Q2(w, r, x, y);
ensures P0(w, r);
{ 
	r := r - 1;
}

procedure P1_stable_t2_s1()
modifies r; 
requires P1(w, r);
requires Q0(w, r);
ensures P1(w, r);
{ 
	assume (w == 0);
	r := r + 1;
}

procedure P1_stable_t2_s2()
modifies y; 
requires P1(w, r);
requires Q1(w, r);
ensures P1(w, r);
{ 
	y := x;
}


procedure P1_stable_t2_s3()
modifies r; 
requires P1(w, r);
requires Q2(w, r, x, y);
ensures P1(w, r);
{ 
	r := r - 1;
}

procedure P2_stable_t2_s1()
modifies r; 
requires P2(w, r);
requires Q0(w, r);
ensures P2(w, r);
{ 
	assume (w == 0);
	r := r + 1;
}

procedure P2_stable_t2_s2()
modifies y; 
requires P2(w, r);
requires Q1(w, r);
ensures P2(w, r);
{ 
	y := x;
}


procedure P2_stable_t2_s3()
modifies r; 
requires P2(w, r);
requires Q2(w, r, x, y);
ensures P2(w, r);
{ 
	r := r - 1;
}

procedure P3_stable_t2_s1()
modifies r; 
requires P3(w, r);
requires Q0(w, r);
ensures P3(w, r);
{ 
	assume (w == 0);
	r := r + 1;
}

procedure P3_stable_t2_s2()
modifies y; 
requires P3(w, r);
requires Q1(w, r);
ensures P3(w, r);
{ 
	y := x;
}


procedure P3_stable_t2_s3()
modifies r; 
requires P3(w, r);
requires Q2(w, r, x, y);
ensures P3(w, r);
{ 
	r := r - 1;
}

procedure Q0_stable_t1_s1()
modifies w; 
requires Q0(w, r);
requires P0(w, r);
ensures Q0(w, r);
{ 
	assume (w == 0);
	assume (r == 0);
	w := 1;
}

procedure Q0_stable_t1_s2()
modifies x; 
requires Q0(w, r);
requires P1(w, r);
ensures Q0(w, r);
{ 
	x := 3;
}


procedure Q0_stable_t1_s3()
modifies w; 
requires Q0(w, r);
requires P2(w, r);
ensures Q0(w, r);
{ 
	w := 0;
}

procedure Q1_stable_t1_s1()
modifies w; 
requires Q1(w, r);
requires P0(w, r);
ensures Q1(w, r);
{ 
	assume (w == 0);
	assume (r == 0);
	w := 1;
}

procedure Q1_stable_t1_s2()
modifies x; 
requires Q1(w, r);
requires P1(w, r);
ensures Q1(w, r);
{ 
	x := 3;
}


procedure Q1_stable_t1_s3()
modifies w; 
requires Q1(w, r);
requires P2(w, r);
ensures Q1(w, r);
{ 
	w := 0;
}

procedure Q2_stable_t1_s1()
modifies w; 
requires Q2(w, r, x, y);
requires P0(w, r);
ensures Q2(w, r, x, y);
{ 
	assume (w == 0);
	assume (r == 0);
	w := 1;
}

procedure Q2_stable_t1_s2()
modifies x; 
requires Q2(w, r, x, y);
requires P1(w, r);
ensures Q2(w, r, x, y);
{ 
	x := 3;
}


procedure Q2_stable_t1_s3()
modifies w; 
requires Q2(w, r, x, y);
requires P2(w, r);
ensures Q2(w, r, x, y);
{ 
	w := 0;
}


procedure Q3_stable_t1_s1()
modifies w; 
requires Q3(w, r);
requires P0(w, r);
ensures Q3(w, r);
{ 
	assume (w == 0);
	assume (r == 0);
	w := 1;
}

procedure Q3_stable_t1_s2()
modifies x; 
requires Q3(w, r);
requires P1(w, r);
ensures Q3(w, r);
{ 
	x := 3;
}


procedure Q3_stable_t1_s3()
modifies w; 
requires Q3(w, r);
requires P2(w, r);
ensures Q3(w, r);
{ 
	w := 0;
}

