/*
				Pre = {producer_finished == 0, queue_size == 0}

		T1: Producer							T2: Consumer

P0:	true						Q0:	queue_size >= 0

	s1:	while (producer_finished == 0) {			while (producer_finished == 0 || queue_size > 0) {

P1:	producer_finished == 0 				Q1:	queue_size >= 0
		
	s2:		queue_size++;	// Increment size			if (queue_size > 0) {

P2:	true						Q2:	queue_size > 0
			if (*) {							
											
	s3:			producer_finished := 1;					queue_size--; // Decrement size
			}							}									
		}							}
								
P3:	producer_finished != 0 				Q3:	producer_finished != 0 && queue_size == 0	
									
				Post = {producer_finished != 0, queue_size == 0}

	***Manual Proof***

function {:existential true} {:inline} P0(producer_finished: int, queue_size: int) : bool {
	true
}
function {:existential true} {:inline} P1(producer_finished: int, queue_size: int) : bool {
	producer_finished == 0
}
function {:existential true} {:inline} P2(producer_finished: int, queue_size: int) : bool {
	true
}
function {:existential true} {:inline} P3(producer_finished: int, queue_size: int) : bool {
	producer_finished != 0
}

function {:existential true} {:inline} Q0(producer_finished: int, queue_size: int) : bool {
	queue_size >= 0
}
function {:existential true} {:inline} Q1(producer_finished: int, queue_size: int) : bool {
	queue_size >= 0
}
function {:existential true} {:inline} Q2(producer_finished: int, queue_size: int) : bool {
	queue_size > 0
}
function {:existential true} {:inline} Q3(producer_finished: int, queue_size: int) : bool {
	producer_finished != 0 && queue_size == 0
}

	***Proof Computed by the learner***

function {:existential true} {:inline} P0(producer_finished: int, queue_size: int) : bool
{
  true
}
function {:existential true} {:inline} P1(producer_finished: int, queue_size: int) : bool
{
  queue_size <= -2 || (-2 < queue_size && producer_finished <= 0)
}
function {:existential true} {:inline} P2(producer_finished: int, queue_size: int) : bool
{
  true
}
function {:existential true} {:inline} P3(producer_finished: int, queue_size: int) : bool
{
  true
}
function {:existential true} {:inline} Q0(producer_finished: int, queue_size: int) : bool
{
  0 <= queue_size 
}
function {:existential true} {:inline} Q1(producer_finished: int, queue_size: int) : bool
{
  0 <= queue_size
}
function {:existential true} {:inline} Q2(producer_finished: int, queue_size: int) : bool
{
  0 < queue_size
}
function {:existential true} {:inline} Q3(producer_finished: int, queue_size: int) : bool
{
  0 < producer_finished && producer_finished <= 1 && -1 < queue_size && queue_size <= 0
}


*/

var producer_finished: int;
var queue_size: int;

function {:existential true} {:inline} P0(producer_finished: int, queue_size: int) : bool;
function {:existential true} {:inline} P1(producer_finished: int, queue_size: int) : bool;
function {:existential true} {:inline} P2(producer_finished: int, queue_size: int) : bool;
function {:existential true} {:inline} P3(producer_finished: int, queue_size: int) : bool;

function {:existential true} {:inline} Q0(producer_finished: int, queue_size: int) : bool;
function {:existential true} {:inline} Q1(producer_finished: int, queue_size: int) : bool;
function {:existential true} {:inline} Q2(producer_finished: int, queue_size: int) : bool;
function {:existential true} {:inline} Q3(producer_finished: int, queue_size: int) : bool;

procedure pre_condition()
requires producer_finished == 0 && queue_size == 0;
{ 
	assert P0(producer_finished, queue_size);
  	assert Q0(producer_finished, queue_size);
}

procedure post_condition()
requires P3(producer_finished, queue_size);
requires Q3(producer_finished, queue_size);
{ 
  	assert (queue_size == 0 && producer_finished == 1);
}

procedure t1_transition_s1() 
requires P0(producer_finished, queue_size);
{ 
	if (producer_finished == 0) {
		assert P1(producer_finished, queue_size);
	} else {
		assert P3(producer_finished, queue_size);
	}
}

procedure t1_transition_s2() 
modifies queue_size;
requires P1(producer_finished, queue_size);
ensures P2(producer_finished, queue_size);
{ 
	queue_size := queue_size + 1;
}

procedure t1_transition_s3() 
modifies producer_finished;
requires P2(producer_finished, queue_size);
ensures P0(producer_finished, queue_size);
{ 
	if (*) {
		producer_finished := 1;	
	}	
}

procedure t2_transition_s1() 
requires Q0(producer_finished, queue_size);
{ 
	if (producer_finished == 0 || queue_size > 0) {
		assert Q1(producer_finished, queue_size);
	} else {
		assert Q3(producer_finished, queue_size);
	}
}

procedure t2_transition_s2() 
requires Q1(producer_finished, queue_size);
{ 
	if (queue_size > 0) {
		assert Q2(producer_finished, queue_size);
	} else {
		assert Q0(producer_finished, queue_size);
	}
}

procedure t2_transition_s3() 
modifies queue_size;
requires Q2(producer_finished, queue_size);
ensures Q0(producer_finished, queue_size);
{ 
	queue_size := queue_size - 1;	
}

procedure Q0_stable_t1_s3()
modifies producer_finished; 
requires Q0(producer_finished, queue_size);
requires P2(producer_finished, queue_size);
ensures Q0(producer_finished, queue_size);
{ 
	if (*) {
		producer_finished := 1;
	}
}

procedure Q1_stable_t1_s3()
modifies producer_finished; 
requires Q1(producer_finished, queue_size);
requires P2(producer_finished, queue_size);
ensures Q1(producer_finished, queue_size);
{ 
	if (*) {
		producer_finished := 1;
	}
}

procedure Q2_stable_t1_s3()
modifies producer_finished; 
requires Q2(producer_finished, queue_size);
requires P2(producer_finished, queue_size);
ensures Q2(producer_finished, queue_size);
{ 
	if (*) {
		producer_finished := 1;
	}
}

procedure Q3_stable_t1_s3()
modifies producer_finished; 
requires Q3(producer_finished, queue_size);
requires P2(producer_finished, queue_size);
ensures Q3(producer_finished, queue_size);
{ 
	if (*) {
		producer_finished := 1;
	}
}

procedure Q0_stable_t1_s2()
modifies queue_size; 
requires Q0(producer_finished, queue_size);
requires P1(producer_finished, queue_size);
ensures Q0(producer_finished, queue_size);
{ 
	queue_size := queue_size + 1;
}

procedure Q1_stable_t1_s2()
modifies queue_size; 
requires Q1(producer_finished, queue_size);
requires P1(producer_finished, queue_size);
ensures Q1(producer_finished, queue_size);
{ 
	queue_size := queue_size + 1;
}

procedure Q2_stable_t1_s2()
modifies queue_size; 
requires Q2(producer_finished, queue_size);
requires P1(producer_finished, queue_size);
ensures Q2(producer_finished, queue_size);
{ 
	queue_size := queue_size + 1;
}

procedure Q3_stable_t1_s2()
modifies queue_size; 
requires Q3(producer_finished, queue_size);
requires P1(producer_finished, queue_size);
ensures Q3(producer_finished, queue_size);
{ 
	queue_size := queue_size + 1;
}

procedure P0_stable_t2_s3()
modifies queue_size; 
requires P0(producer_finished, queue_size);
requires Q2(producer_finished, queue_size);
ensures P0(producer_finished, queue_size);
{ 
	queue_size := queue_size - 1;
}

procedure P1_stable_t2_s3()
modifies queue_size; 
requires P1(producer_finished, queue_size);
requires Q2(producer_finished, queue_size);
ensures P1(producer_finished, queue_size);
{ 
	queue_size := queue_size - 1;
}

procedure P2_stable_t2_s3()
modifies queue_size; 
requires P2(producer_finished, queue_size);
requires Q2(producer_finished, queue_size);
ensures P2(producer_finished, queue_size);
{ 
	queue_size := queue_size - 1;
}

procedure P3_stable_t2_s3()
modifies queue_size; 
requires P3(producer_finished, queue_size);
requires Q2(producer_finished, queue_size);
ensures P3(producer_finished, queue_size);
{ 
	queue_size := queue_size - 1;
}
