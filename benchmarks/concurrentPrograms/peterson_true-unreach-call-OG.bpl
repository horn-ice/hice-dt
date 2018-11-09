function {:existential true} {:inline} P0 (x: int, turn: int, flag1: int, flag2: int) : bool;
function {:existential true} {:inline} P1 (x: int, turn: int, flag1: int, flag2: int) : bool;
function {:existential true} {:inline} P2 (x: int, turn: int, flag1: int, flag2: int) : bool;
function {:existential true} {:inline} P3 (x: int, turn: int, flag1: int, flag2: int) : bool;

function {:existential true} {:inline} Q0 (x: int, turn: int, flag1: int, flag2: int) : bool;
function {:existential true} {:inline} Q1 (x: int, turn: int, flag1: int, flag2: int) : bool;
function {:existential true} {:inline} Q2 (x: int, turn: int, flag1: int, flag2: int) : bool;
function {:existential true} {:inline} Q3 (x: int, turn: int, flag1: int, flag2: int) : bool;

/*

function {:existential true} {:inline} P0 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag1 == 0 && ((turn == 1 && flag2 == 1) || ((turn == 0 || turn == 1) && flag2 == 0))
}
function {:existential true} {:inline} P1 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag1 == 1 && ((turn == 2 && flag2 == 0) || ((turn == 1 || turn == 2) && flag2 == 1))
}
function {:existential true} {:inline} P2 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag1 == 1 && x == 1 && ((turn == 1 && flag2 == 1) || (turn == 2 && flag2 == 0))
}
function {:existential true} {:inline} P3 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag1 == 0
}

function {:existential true} {:inline} Q0 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag2 == 0 && ((flag1 == 0 && (turn == 0 || turn == 2)) || (turn == 2 && flag1 == 1))
}
function {:existential true} {:inline} Q1 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag2 == 1 && ((flag1 == 0 && turn == 1) || ((turn == 2 || turn == 1) && flag1 == 1))
}
function {:existential true} {:inline} Q2 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag2 == 1 && x == 0 && ((turn == 2 && flag1 == 1) || (turn == 1 && flag1 == 0))
}
function {:existential true} {:inline} Q3 (x: int, turn: int, flag1: int, flag2: int) : bool {
	flag2 == 0
}

						T1						T2

	P0: 							Q0: 	
		flag1 == 0 && ((turn == 1 && flag2 == 1) || ((turn == 0 || turn == 1) && flag2 == 0))

					flag2 == 0 && ((flag1 == 0 && (turn == 0 || turn == 2)) || (turn == 2 && flag1 == 1))
						

		S1		flag1 := 1					flag2 := 1
				turn := 2					turn := 1
	P1:							Q1:

		flag1 == 1 && ((turn == 2 && flag2 == 0) || ((turn == 1 || turn == 2) && flag2 == 1))

						flag2 == 1 && ((flag1 == 0 && turn == 1) || ((turn == 2 || turn == 1) && flag1 == 1))
				
						

				while ((flag2 == 1)&&(turn == 2)) 		while ((flag1 == 1)&&(turn == 1)) 
				{						{
	
				}
										}	
	P'\ P' in P1 ^ !((flag2 == 1)&&(turn == 2))


		S2		x := 1						x := 0
	P2:							Q2:

		flag1 == 1 && x == 1 && ((turn == 1 && flag2 == 1) || (turn == 2 && flag2 == 0))			

						flag2 == 1 && x == 0 && ((turn == 2 && flag1 == 1) || (turn == 1 && flag1 == 0))

				assert (x >= 1)					assert (x <= 0)

		S3	  	flag1 := 0					flag2 := 0	
	P3:							Q3:	

		flag1 == 0							flag2 == 0



function {:existential true} {:inline} P0(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} P1(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	(x <= -1 && 0 < flag1) || (-1 < x && 0 < flag1)

	0 < flag1
}
function {:existential true} {:inline} P2(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	(0 < flag1 && flag1 <= 1 && 0 < x && x - flag1 <= 0 && turn - flag1 <= 0) || 
	(0 < flag1 && flag1 <= 1 && 0 < x && x - flag1 <= 0 && 0 < turn - flag1 && flag2 <= 0) || 
	(0 < flag1 && 1 < flag1 && 0 < x && x <= 1 && flag2 <= 0) || 
	(0 < flag1 && 1 < flag1 && 0 < x && x <= 1 && 0 < flag2 && turn <= 1)


	(x == 1) &&
	((flag1 == 1 && turn <= 1) ||
	(flag1 == 1 && 1 < turn && flag2 <= 0) ||
	(1 < flag1 && flag2 <= 0) ||
	(1 < flag1 && 0 < flag2 && turn <= 1) ||
		)

}
function {:existential true} {:inline} P3(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} Q0(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} Q1(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	0 < flag2
}
function {:existential true} {:inline} Q2(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	(turn <= 0 && flag1 <= 0 && -1 < flag1 && flag1 - flag2 <= -1 && x <= 0 && -1 < x) || 
	(0 < turn && 0 < flag2 && x <= 0 && -1 < x && turn <= 1 && flag1 <= 0) || 
	(0 < turn && 0 < flag2 && x <= 0 && -1 < x && 1 < turn)
	
	(x == 0) &&
	((1 <= flag2 && flag1 == 0 && turn <= 0) ||
	(0 < flag2 && flag1 <= 0 && turn == 1) ||
	(0 < flag2 && 1 < turn)) 

}
function {:existential true} {:inline} Q3(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}

-------------------------------------------------------

function {:existential true} {:inline} P0(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} P1(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	(x <= -1 && 0 < flag1 && flag1 <= 1 && 0 < turn && turn - flag1 <= 1) || 
	(-1 < x && flag1 <= 1 && 0 < flag1 && 0 < turn && turn - flag1 <= 1)

	flag1 == 1 && (turn == 1 || turn == 2)

}
function {:existential true} {:inline} P2(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	(0 < flag1 && flag1 <= 1 && 0 < x && x - flag1 <= 0 && flag2 <= 0) || 
	(0 < flag1 && flag1 <= 1 && 0 < x && x - flag1 <= 0 && 0 < flag2 && flag2 <= 1 && turn - flag1 <= 0 && 0 < turn) || 
	(0 < flag1 && flag1 <= 1 && 0 < x && x - flag1 <= 0 && 0 < flag2 && 1 < flag2)


	(flag1 == 1 && x == 1) &&
	( flag2 <= 0 || 1 < flag2 || (flag2 == 1 && turn == 1)
	 
}
function {:existential true} {:inline} P3(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} Q0(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} Q1(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	0 < flag2 && flag2 <= 1

	flag2 == 1
}
function {:existential true} {:inline} Q2(x: int, turn: int, flag1: int, flag2: int) : bool
{
  	(x <= 0 && x - flag1 <= 1 && -1 < x && flag2 <= 1 && -1 < flag2 && 0 < flag2 && flag1 <= 0) || 
	(x <= 0 && x - flag1 <= 1 && -1 < x && flag2 <= 1 && -1 < flag2 && 0 < flag2 && 0 < flag1 && flag1 - flag2 <= 0 && turn <= 0) || 
	(x <= 0 && x - flag1 <= 1 && -1 < x && flag2 <= 1 && -1 < flag2 && 0 < flag2 && 0 < flag1 && flag1 - flag2 <= 0 && 0 < turn && 0 < turn - flag1) || (x <= 0 && x - flag1 <= 1 && -1 < x && flag2 <= 1 && -1 < flag2 && 0 < flag2 && 0 < flag1 && 0 < flag1 - flag2) || 
	(x <= 0 && 1 < x - flag1 && 0 < x + flag2 && flag2 <= 1)


	(x == 0 && flag2 == 1) && 
	(flag1 <= 0 || flag1 == 1 && (turn <= 0 || 1 < turn)
	

}
function {:existential true} {:inline} Q3(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}

----------------------

function {:existential true} {:inline} P0(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} P1(x: int, turn: int, flag1: int, flag2: int) : bool
{
  (x <= -1 && 0 < flag1 && flag1 <= 1) || (-1 < x && 0 < flag1 && flag1 <= 1)
}
function {:existential true} {:inline} P2(x: int, turn: int, flag1: int, flag2: int) : bool
{
  (0 < flag1 && -1 < x - flag1 && x <= 1 && turn - flag1 <= 0) || (0 < flag1 && -1 < x - flag1 && x <= 1 && 0 < turn - flag1 && turn - flag1 <= 1 && flag2 <= 0) || (0 < flag1 && -1 < x - flag1 && x <= 1 && 0 < turn - flag1 && turn - flag1 <= 1 && 0 < flag2 && turn - flag2 <= 0) || (0 < flag1 && -1 < x - flag1 && x <= 1 && 0 < turn - flag1 && 1 < turn - flag1)
}
function {:existential true} {:inline} P3(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} Q0(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}
function {:existential true} {:inline} Q1(x: int, turn: int, flag1: int, flag2: int) : bool
{
  flag2 <= 1 && 0 < flag2 && 0 < turn && turn - flag2 <= 1
}
function {:existential true} {:inline} Q2(x: int, turn: int, flag1: int, flag2: int) : bool
{
  (x - turn <= -1 && flag2 <= 1 && turn - flag2 <= 1 && 0 < flag2 && -1 < x + turn && x <= 0 && turn - flag2 <= 0 && flag1 <= 0) || (x - turn <= -1 && flag2 <= 1 && turn - flag2 <= 1 && 0 < flag2 && -1 < x + turn && x <= 0 && turn - flag2 <= 0 && 0 < flag1 && 0 < flag1 - flag2) || (x - turn <= -1 && flag2 <= 1 && turn - flag2 <= 1 && 0 < flag2 && -1 < x + turn && x <= 0 && 0 < turn - flag2)
}
function {:existential true} {:inline} Q3(x: int, turn: int, flag1: int, flag2: int) : bool
{
  true
}






*/


var x: int;
var turn: int;
var flag1: int;
var flag2: int;

procedure pre() 
requires flag1 == 0 && flag2 == 0 && turn == 0;
{
	assert P0 (x, turn, flag1, flag2);
	assert Q0 (x, turn, flag1, flag2);
}


procedure assert_t1() 
requires P2 (x, turn, flag1, flag2);
{
	assert x >= 1;
}

procedure assert_t2() 
requires Q2 (x, turn, flag1, flag2);
{
	assert x <= 0;
}


procedure atomic_t1_transition_s1() 
modifies flag1;
modifies turn;
requires P0 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	flag1 := 1;
	turn := 2;
}

procedure atomic_t1_transition_s2() 
modifies x;
requires flag2 != 1 || turn != 2;
requires P1 (x, turn, flag1, flag2);
ensures P2 (x, turn, flag1, flag2);
{
	x := 1;
}

procedure atomic_t1_transition_s3() 
modifies flag1;
requires P2 (x, turn, flag1, flag2);
ensures P3 (x, turn, flag1, flag2);
{
	flag1 := 0;
}

procedure atomic_t2_transition_s1() 
modifies flag2;
modifies turn;
requires Q0 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	flag2 := 1;
	turn := 1;
}

procedure atomic_t2_transition_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires Q1 (x, turn, flag1, flag2);
ensures Q2 (x, turn, flag1, flag2);
{
	x := 0;
}

procedure atomic_t2_transition_s3() 
modifies flag2;
requires Q2 (x, turn, flag1, flag2);
ensures Q3 (x, turn, flag1, flag2);
{
	flag2 := 0;
}


procedure P0_stable_t2_s1() 
modifies flag2;
modifies turn;
requires P0 (x, turn, flag1, flag2);
requires Q0 (x, turn, flag1, flag2);
ensures P0 (x, turn, flag1, flag2);
{
	flag2 := 1;
	turn := 1;
}

procedure P1_stable_t2_s1() 
modifies flag2;
modifies turn;
requires P1 (x, turn, flag1, flag2);
requires Q0 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	flag2 := 1;
	turn := 1;
}

procedure P2_stable_t2_s1() 
modifies flag2;
modifies turn;
requires P2 (x, turn, flag1, flag2);
requires Q0 (x, turn, flag1, flag2);
ensures P2 (x, turn, flag1, flag2);
{
	flag2 := 1;
	turn := 1;
}

procedure P3_stable_t2_s1() 
modifies flag2;
modifies turn;
requires P3 (x, turn, flag1, flag2);
requires Q0 (x, turn, flag1, flag2);
ensures P3 (x, turn, flag1, flag2);
{
	flag2 := 1;
	turn := 1;
}


procedure P0_stable_t2_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires P0 (x, turn, flag1, flag2);
requires Q1 (x, turn, flag1, flag2);
ensures P0 (x, turn, flag1, flag2);
{
	x := 0;
}

procedure P1_stable_t2_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires P1 (x, turn, flag1, flag2);
requires Q1 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	x := 0;
}

procedure P2_stable_t2_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires P2 (x, turn, flag1, flag2);
requires Q1 (x, turn, flag1, flag2);
ensures P2 (x, turn, flag1, flag2);
{
	x := 0;
}

procedure P3_stable_t2_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires P3 (x, turn, flag1, flag2);
requires Q1 (x, turn, flag1, flag2);
ensures P3 (x, turn, flag1, flag2);
{
	x := 0;
}


procedure P0_stable_t2_s3() 
modifies flag2;
requires P0 (x, turn, flag1, flag2);
requires Q2 (x, turn, flag1, flag2);
ensures P0 (x, turn, flag1, flag2);
{
	flag2 := 0;
}

procedure P1_stable_t2_s3() 
modifies flag2;
requires P1 (x, turn, flag1, flag2);
requires Q2 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	flag2 := 0;
}

procedure P2_stable_t2_s3() 
modifies flag2;
requires P2 (x, turn, flag1, flag2);
requires Q2 (x, turn, flag1, flag2);
ensures P2 (x, turn, flag1, flag2);
{
	flag2 := 0;
}

procedure P3_stable_t2_s3() 
modifies flag2;
requires P3 (x, turn, flag1, flag2);
requires Q2 (x, turn, flag1, flag2);
ensures P3 (x, turn, flag1, flag2);
{
	flag2 := 0;
}


procedure Q0_stable_t1_s1() 
modifies flag1;
modifies turn;
requires Q0 (x, turn, flag1, flag2);
requires P0 (x, turn, flag1, flag2);
ensures Q0 (x, turn, flag1, flag2);
{
	flag1 := 1;
	turn := 2;
}


procedure Q1_stable_t1_s1() 
modifies flag1;
modifies turn;
requires Q1 (x, turn, flag1, flag2);
requires P0 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	flag1 := 1;
	turn := 2;
}


procedure Q2_stable_t1_s1() 
modifies flag1;
modifies turn;
requires Q2 (x, turn, flag1, flag2);
requires P0 (x, turn, flag1, flag2);
ensures Q2 (x, turn, flag1, flag2);
{
	flag1 := 1;
	turn := 2;
}


procedure Q3_stable_t1_s1() 
modifies flag1;
modifies turn;
requires Q3 (x, turn, flag1, flag2);
requires P0 (x, turn, flag1, flag2);
ensures Q3 (x, turn, flag1, flag2);
{
	flag1 := 1;
	turn := 2;
}


procedure Q0_stable_t1_s2() 
modifies x;
requires flag2 != 1 || turn != 2;
requires Q0 (x, turn, flag1, flag2);
requires P1 (x, turn, flag1, flag2);
ensures Q0 (x, turn, flag1, flag2);
{
	x := 1;
}

procedure Q1_stable_t1_s2() 
modifies x;
requires flag2 != 1 || turn != 2;
requires Q1 (x, turn, flag1, flag2);
requires P1 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	x := 1;
}

procedure Q2_stable_t1_s2() 
modifies x;
requires flag2 != 1 || turn != 2;
requires Q2 (x, turn, flag1, flag2);
requires P1 (x, turn, flag1, flag2);
ensures Q2 (x, turn, flag1, flag2);
{
	x := 1;
}

procedure Q3_stable_t1_s2() 
modifies x;
requires flag2 != 1 || turn != 2;
requires Q3 (x, turn, flag1, flag2);
requires P1 (x, turn, flag1, flag2);
ensures Q3 (x, turn, flag1, flag2);
{
	x := 1;
}

procedure Q0_stable_t1_s3() 
modifies flag1;
requires Q0 (x, turn, flag1, flag2);
requires P2 (x, turn, flag1, flag2);
ensures Q0 (x, turn, flag1, flag2);
{
	flag1 := 0;
}

procedure Q1_stable_t1_s3() 
modifies flag1;
requires Q1 (x, turn, flag1, flag2);
requires P2 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	flag1 := 0;
}

procedure Q2_stable_t1_s3() 
modifies flag1;
requires Q2 (x, turn, flag1, flag2);
requires P2 (x, turn, flag1, flag2);
ensures Q2 (x, turn, flag1, flag2);
{
	flag1 := 0;
}

procedure Q3_stable_t1_s3() 
modifies flag1;
requires Q3 (x, turn, flag1, flag2);
requires P2 (x, turn, flag1, flag2);
ensures Q3 (x, turn, flag1, flag2);
{
	flag1 := 0;
}


procedure not_Q1_stable_t1_s1() 
modifies flag1;
modifies turn;
requires flag1 != 1 || turn != 1;
requires Q1 (x, turn, flag1, flag2);
requires P0 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	flag1 := 1;
	turn := 2;
	assert (flag1 != 1 || turn != 1);
}

procedure not_Q1_stable_t1_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires flag2 != 1 || turn != 2;
requires Q1 (x, turn, flag1, flag2);
requires P1 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	x := 1;
	assert (flag1 != 1 || turn != 1);
}

procedure not_Q1_stable_t1_s3() 
modifies flag1;
requires flag1 != 1 || turn != 1;
requires Q1 (x, turn, flag1, flag2);
requires P2 (x, turn, flag1, flag2);
ensures Q1 (x, turn, flag1, flag2);
{
	flag1 := 0;
	assert (flag1 != 1 || turn != 1);
}

procedure not_P1_stable_t2_s1() 
modifies flag2;
modifies turn;
requires flag2 != 1 || turn != 2;
requires P1 (x, turn, flag1, flag2);
requires Q0 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	flag2 := 1;
	turn := 1;
	assert (flag2 != 1 || turn != 2);
}

procedure not_P1_stable_t2_s2() 
modifies x;
requires flag1 != 1 || turn != 1;
requires flag2 != 1 || turn != 2;
requires P1 (x, turn, flag1, flag2);
requires Q1 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	x := 0;
	assert (flag2 != 1 || turn != 2);
}

procedure not_P1_stable_t2_s3() 
modifies flag2;
requires flag2 != 1 || turn != 2;
requires P1 (x, turn, flag1, flag2);
requires Q2 (x, turn, flag1, flag2);
ensures P1 (x, turn, flag1, flag2);
{
	flag2 := 0;
	assert (flag2 != 1 || turn != 2);
}



