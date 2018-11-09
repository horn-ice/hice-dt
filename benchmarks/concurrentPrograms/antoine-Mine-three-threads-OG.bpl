/*

						Pre := {h==0, c==0, t==0, l==0}

			T1					T2					T3
	P0					Q0					R0
		h <= 10					c <= h					l <= c && t <= l && l >= 0

s1		while (*) {				while (*) {				while (*) {
	P1					Q1					R1
		h <= 10					c <= h					l <= c && t <= l && l >= 0

s2			if (h < 10) {				c := h;					if (*) {
	P2						}				R2
		h < 10				Q2						l <= c && t <= l && l >= 0

s3				h := h + 1;		c <= h							t := 0;
			}										} else {
		}									R3
	P3											l <= c && t <= l && l >= 0
		h <= 10
s4														t := t + (c - l);
													}
	
											R4	l <= c && t <= c && l >= 0 
		
s5													l := c;
												}

											R5	l <= c	&& t <= l && l >= 0	
						Post := {t <= l <= c <= h}


function {:existential true} {:inline} P0(h: int) : bool {
  h <= 10
}
function {:existential true} {:inline} P1(h: int) : bool {
  h <= 10
}
function {:existential true} {:inline} P2(h: int) : bool {
  h < 10
}
function {:existential true} {:inline} P3(h: int) : bool {
  h <= 10
}

function {:existential true} {:inline} Q0(h: int, c: int) : bool {
  c <= h
}
function {:existential true} {:inline} Q1(h: int, c: int) : bool {
  c <= h
}
function {:existential true} {:inline} Q2(h: int, c: int) : bool {
  c <= h
}

function {:existential true} {:inline} R0(t: int, l: int, c: int) : bool {
  l <= c && t <= l && l >= 0
}
function {:existential true} {:inline} R1(t: int, l: int, c: int) : bool {
  l <= c && t <= l && l >= 0
}
function {:existential true} {:inline} R2(t: int, l: int, c: int) : bool {
  l <= c && t <= l && l >= 0
}
function {:existential true} {:inline} R3(t: int, l: int, c: int) : bool {
  l <= c && t <= l && l >= 0
}
function {:existential true} {:inline} R4(t: int, l: int, c: int) : bool {
  l <= c && t <= c && l >= 0
}
function {:existential true} {:inline} R5(t: int, l: int, c: int) : bool {
  l <= c && t <= l && l >= 0
}


*/

var h: int;
var c: int;
var t: int;
var l: int;
var new_h: int;
var new_c: int;
var new_t: int;
var new_l: int;

function {:existential true} {:inline} P0(h: int) : bool;
function {:existential true} {:inline} P1(h: int) : bool;
function {:existential true} {:inline} P2(h: int) : bool;
function {:existential true} {:inline} P3(h: int) : bool;

function {:existential true} {:inline} Q0(h: int, c: int) : bool;
function {:existential true} {:inline} Q1(h: int, c: int) : bool;
function {:existential true} {:inline} Q2(h: int, c: int) : bool;

function {:existential true} {:inline} R0(t: int, l: int, c: int) : bool;
function {:existential true} {:inline} R1(t: int, l: int, c: int) : bool;
function {:existential true} {:inline} R2(t: int, l: int, c: int) : bool;
function {:existential true} {:inline} R3(t: int, l: int, c: int) : bool;
function {:existential true} {:inline} R4(t: int, l: int, c: int) : bool;
function {:existential true} {:inline} R5(t: int, l: int, c: int) : bool;

procedure pre_condition()
requires h == 0 && c == 0 && t == 0 && l == 0;
{ 
	assert P0(h);
  	assert Q0(h, c);
	assert R0(t, l, c);
}

procedure post_condition()
requires P3(h);
requires Q2(h, c);
requires R5(t, l, c);
{ 
  	assert (t <= l && l <= c && c <= h);
}

procedure t1_transition_s1()
requires P0(h);
{ 
	if (*) {
		assert P1(h);
	} else {
		assert P3(h);
	}
}

procedure t1_transition_s2()
requires P1(h);
{ 
	if (h < 2) {
		assert P2(h);
	} else {
		assert P0(h);
	}
}

procedure t1_transition_s3()
modifies h;
requires P2(h);
ensures P0(h);
{ 
	h := h + 1;
}


procedure t2_transition_s1()
requires Q0(h, c);
{ 
	if (*) {
		assert Q1(h, c);
	} else {
		assert Q2(h, c);
	}
}

procedure t2_transition_s2()
modifies c;
requires Q1(h, c);
ensures Q0(h, c);
{ 
	c := h;
}

procedure t3_transition_s1()
requires R0(t, l, c);
{ 
	if (*) {
		assert R1(t, l, c);
	} else {
		assert R5(t, l, c);
	}
}

procedure t3_transition_s2()
requires R1(t, l, c);
{ 
	if (*) {
		assert R2(t, l, c);
	} else {
		assert R3(t, l, c);
	}
}

procedure t3_transition_s3()
modifies t;
requires R2(t, l, c);
ensures R4(t, l, c);
{ 
	t := 0;
}

procedure t3_transition_s4()
modifies t;
requires R3(t, l, c);
ensures R4(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure t3_transition_s5()
modifies l;
requires R4(t, l, c);
ensures R0(t, l, c);
{
	l := c;
}


procedure R0_stable_t1_s3()
modifies h;
requires P2(h);
requires R0(t, l, c);
ensures R0(t, l, c);
{
	h := h + 1;
}

procedure R1_stable_t1_s3()
modifies h;
requires P2(h);
requires R1(t, l, c);
ensures R1(t, l, c);
{
	h := h + 1;
}

procedure R2_stable_t1_s3()
modifies h;
requires P2(h);
requires R2(t, l, c);
ensures R2(t, l, c);
{
	h := h + 1;
}

procedure R3_stable_t1_s3()
modifies h;
requires P2(h);
requires R3(t, l, c);
ensures R3(t, l, c);
{
	h := h + 1;
}

procedure R4_stable_t1_s3()
modifies h;
requires P2(h);
requires R4(t, l, c);
ensures R4(t, l, c);
{
	h := h + 1;
}

procedure R5_stable_t1_s3()
modifies h;
requires P2(h);
requires R5(t, l, c);
ensures R5(t, l, c);
{
	h := h + 1;
}



procedure R0_stable_t2_s2()
modifies c;
requires Q1(h, c);
requires R0(t, l, c);
ensures R0(t, l, c);
{
	c := h;
}

procedure R1_stable_t2_s2()
modifies c;
requires Q1(h, c);
requires R1(t, l, c);
ensures R1(t, l, c);
{
	c := h;
}

procedure R2_stable_t2_s2()
modifies c;
requires Q1(h, c);
requires R2(t, l, c);
ensures R2(t, l, c);
{
	c := h;
}

procedure R3_stable_t2_s2()
modifies c;
requires Q1(h, c);
requires R3(t, l, c);
ensures R3(t, l, c);
{
	c := h;
}

procedure R4_stable_t2_s2()
modifies c;
requires Q1(h, c);
requires R4(t, l, c);
ensures R4(t, l, c);
{
	c := h;
}

procedure R5_stable_t2_s2()
modifies c;
requires Q1(h, c);
requires R5(t, l, c);
ensures R5(t, l, c);
{
	c := h;
}

procedure Q0_stable_t1_s3()
modifies h;
requires P2(h);
requires Q0(h, c);
ensures Q0(h, c);
{
	h := h + 1;
}

procedure Q1_stable_t1_s3()
modifies h;
requires P2(h);
requires Q1(h, c);
ensures Q1(h, c);
{
	h := h + 1;
}

procedure Q2_stable_t1_s3()
modifies h;
requires P2(h);
requires Q2(h, c);
ensures Q2(h, c);
{
	h := h + 1;
}

procedure Q0_stable_t3_s3()
modifies t;
requires Q0(h, c);
ensures Q0(h, c);
requires R2(t, l, c);
{
	t := 0;
}

procedure Q1_stable_t3_s3()
modifies t;
requires Q1(h, c);
ensures Q1(h, c);
requires R2(t, l, c);
{
	t := 0;
}

procedure Q2_stable_t3_s3()
modifies t;
requires Q2(h, c);
ensures Q2(h, c);
requires R2(t, l, c);
{
	t := 0;
}

procedure Q0_stable_t3_s4()
modifies t;
requires Q0(h, c);
ensures Q0(h, c);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure Q1_stable_t3_s4()
modifies t;
requires Q1(h, c);
ensures Q1(h, c);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}


procedure Q2_stable_t3_s4()
modifies t;
requires Q2(h, c);
ensures Q2(h, c);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure Q0_stable_t3_s5()
modifies l;
requires Q0(h, c);
ensures Q0(h, c);
requires R4(t, l, c);
{
	l := c;
}

procedure Q1_stable_t3_s5()
modifies l;
requires Q1(h, c);
ensures Q1(h, c);
requires R4(t, l, c);
{
	l := c;
}

procedure Q2_stable_t3_s5()
modifies l;
requires Q2(h, c);
ensures Q2(h, c);
requires R4(t, l, c);
{
	l := c;
}


procedure P0_stable_t2_s2()
modifies c;
requires P0(h);
requires Q1(h, c);
ensures P0(h);
{
	c := h;
}

procedure P1_stable_t2_s2()
modifies c;
requires P1(h);
requires Q1(h, c);
ensures P1(h);
{
	c := h;
}

procedure P2_stable_t2_s2()
modifies c;
requires P2(h);
requires Q1(h, c);
ensures P2(h);
{
	c := h;
}

procedure P3_stable_t2_s2()
modifies c;
requires P3(h);
requires Q1(h, c);
ensures P3(h);
{
	c := h;
}


procedure P0_stable_t3_s5()
modifies l;
requires P0(h);
ensures P0(h);
requires R4(t, l, c);
{
	l := c;
}

procedure P1_stable_t3_s5()
modifies l;
requires P1(h);
ensures P1(h);
requires R4(t, l, c);
{
	l := c;
}

procedure P2_stable_t3_s5()
modifies l;
requires P2(h);
ensures P2(h);
requires R4(t, l, c);
{
	l := c;
}

procedure P3_stable_t3_s5()
modifies l;
requires P3(h);
ensures P3(h);
requires R4(t, l, c);
{
	l := c;
}

procedure P0_stable_t3_s4()
modifies t;
requires P0(h);
ensures P0(h);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure P1_stable_t3_s4()
modifies t;
requires P1(h);
ensures P1(h);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure P2_stable_t3_s4()
modifies t;
requires P2(h);
ensures P2(h);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure P3_stable_t3_s4()
modifies t;
requires P3(h);
ensures P3(h);
requires R3(t, l, c);
{
	t := t + c;
	t := t - l;
}

procedure P0_stable_t3_s3()
modifies t;
requires P0(h);
ensures P0(h);
requires R2(t, l, c);
{
	t := 0;
}

procedure P1_stable_t3_s3()
modifies t;
requires P1(h);
ensures P1(h);
requires R2(t, l, c);
{
	t := 0;
}


procedure P2_stable_t3_s3()
modifies t;
requires P2(h);
ensures P2(h);
requires R2(t, l, c);
{
	t := 0;
}

procedure P3_stable_t3_s3()
modifies t;
requires P3(h);
ensures P3(h);
requires R2(t, l, c);
{
	t := 0;
}







