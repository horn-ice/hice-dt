var h: int;
var c: int;
var t: int;
var l: int;
var new_h: int;
var new_c: int;
var new_t: int;
var new_l: int;

function {:existential true} {:inline} P0(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} P1(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} P2(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} P3(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} P4(h: int, c: int, t: int, l: int) : bool;

function {:existential true} {:inline} Q0(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} Q1(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} Q2(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} Q3(h: int, c: int, t: int, l: int) : bool;

function {:existential true} {:inline} R0(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} R1(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} R2(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} R3(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} R4(h: int, c: int, t: int, l: int) : bool;
function {:existential true} {:inline} R5(h: int, c: int, t: int, l: int) : bool;

function {:existential true} {:inline} R_t1(h: int, c: int, t: int, l: int, new_h: int, new_c: int, new_t: int, new_l: int) : bool;
function {:existential true} {:inline} R_t2(h: int, c: int, t: int, l: int, new_h: int, new_c: int, new_t: int, new_l: int) : bool;
function {:existential true} {:inline} R_t3(h: int, c: int, t: int, l: int, new_h: int, new_c: int, new_t: int, new_l: int) : bool;

procedure pre_condition()
requires h == 0 && c == 0 && t == 0 && l == 0;
{ 
	assert P0(h, c, t, l);
  	assert Q0(h, c, t, l);
	assert R0(h, c, t, l);
}

procedure post_condition()
requires P4(h, c, t, l);
requires Q3(h, c, t, l);
requires R5(h, c, t, l);
{ 
  	assert (t <= l && l <= c && c <= h);
}

procedure t1_transition_s1()
requires P0(h, c, t, l);
{ 
	if (*) {
		assert P1(h, c, t, l);
	} else {
		assert P4(h, c, t, l);
	}
}

procedure t1_transition_s2()
requires P1(h, c, t, l);
{ 
	if (h < 2) {
		assert P2(h, c, t, l);
	} else {
		assert P3(h, c, t, l);
	}
}

procedure t1_transition_s3()
modifies h;
requires P2(h, c, t, l);
ensures P3(h, c, t, l);
ensures R_t2(old(h), old(c), old(t), old(l), h, c, t, l);
ensures R_t3(old(h), old(c), old(t), old(l), h, c, t, l);
{ 
	h := h + 1;
}

procedure t1_transition_s4()
requires P3(h, c, t, l);
{ 
	assert P0(h, c, t, l);
}

procedure t2_transition_s1()
requires Q0(h, c, t, l);
{ 
	if (*) {
		assert Q1(h, c, t, l);
	} else {
		assert Q3(h, c, t, l);
	}
}

procedure t2_transition_s2()
modifies c;
requires Q1(h, c, t, l);
ensures Q2(h, c, t, l);
ensures R_t1(old(h), old(c), old(t), old(l), h, c, t, l);
ensures R_t3(old(h), old(c), old(t), old(l), h, c, t, l);
{ 
	c := h;
}

procedure t3_transition_s1()
requires R0(h, c, t, l);
{ 
	if (*) {
		assert R1(h, c, t, l);
	} else {
		assert R5(h, c, t, l);
	}
}

procedure t3_transition_s2()
requires R1(h, c, t, l);
{ 
	if (*) {
		assert R2(h, c, t, l);
	} else {
		assert R3(h, c, t, l);
	}
}

procedure t3_transition_s3()
modifies t;
requires R2(h, c, t, l);
ensures R4(h, c, t, l);
ensures R_t2(old(h), old(c), old(t), old(l), h, c, t, l);
ensures R_t1(old(h), old(c), old(t), old(l), h, c, t, l);
{ 
	t := 0;
}

procedure t3_transition_s4()
modifies t;
requires R3(h, c, t, l);
ensures R4(h, c, t, l);
ensures R_t2(old(h), old(c), old(t), old(l), h, c, t, l);
ensures R_t1(old(h), old(c), old(t), old(l), h, c, t, l);
{
	t := t + c;
	t := t - l;
}

procedure t3_transition_s5()
modifies l;
requires R4(h, c, t, l);
ensures R0(h, c, t, l);
ensures R_t2(old(h), old(c), old(t), old(l), h, c, t, l);
ensures R_t1(old(h), old(c), old(t), old(l), h, c, t, l);
{
	l := c;
}

procedure P0_Stable_R_t1()
requires P0(h, c, t, l);
requires R_t1(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert P0(new_h, new_c, new_t, new_l);
}

procedure P1_Stable_R_t1()
requires P1(h, c, t, l);
requires R_t1(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert P1(new_h, new_c, new_t, new_l);
}


procedure P2_Stable_R_t1()
requires P2(h, c, t, l);
requires R_t1(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert P2(new_h, new_c, new_t, new_l);
}

procedure P3_Stable_R_t1()
requires P3(h, c, t, l);
requires R_t1(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert P3(new_h, new_c, new_t, new_l);
}


procedure P4_Stable_R_t1()
requires P4(h, c, t, l);
requires R_t1(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert P4(new_h, new_c, new_t, new_l);
}

procedure Q0_Stable_R_t2()
requires Q0(h, c, t, l);
requires R_t2(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert Q0(new_h, new_c, new_t, new_l);
}

procedure Q1_Stable_R_t2()
requires Q1(h, c, t, l);
requires R_t2(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert Q1(new_h, new_c, new_t, new_l);
}


procedure Q2_Stable_R_t2()
requires Q2(h, c, t, l);
requires R_t2(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert Q2(new_h, new_c, new_t, new_l);
}

procedure Q3_Stable_R_t2()
requires Q3(h, c, t, l);
requires R_t2(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert Q3(new_h, new_c, new_t, new_l);
}

procedure R0_Stable_R_t3()
requires R0(h, c, t, l);
requires R_t3(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert R0(new_h, new_c, new_t, new_l);
}

procedure R1_Stable_R_t3()
requires R1(h, c, t, l);
requires R_t3(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert R1(new_h, new_c, new_t, new_l);
}


procedure R2_Stable_R_t3()
requires R2(h, c, t, l);
requires R_t3(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert R2(new_h, new_c, new_t, new_l);
}

procedure R3_Stable_R_t3()
requires R3(h, c, t, l);
requires R_t3(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert R3(new_h, new_c, new_t, new_l);
}


procedure R4_Stable_R_t3()
requires R4(h, c, t, l);
requires R_t3(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert R4(new_h, new_c, new_t, new_l);
}


procedure R5_Stable_R_t3()
requires R5(h, c, t, l);
requires R_t3(h, c, t, l, new_h, new_c, new_t, new_l);
{ 
	assert R5(new_h, new_c, new_t, new_l);
}

