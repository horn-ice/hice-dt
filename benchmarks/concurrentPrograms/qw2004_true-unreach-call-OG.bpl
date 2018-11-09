var status: int;
var stopped: int;
var pendingIo: int;
var pending_t1: int;
var pending_t2: int;
var stoppingFlag: int;
var stoppingEvent: int;

function {:existential true} {:inline} P0(stopped: int, stoppingEvent: int) : bool;
function {:existential true} {:inline} P1(stoppingEvent: int) : bool;
function {:existential true} {:inline} P2(stoppingEvent: int) : bool;
function {:existential true} {:inline} P3(stoppingEvent: int) : bool;
function {:existential true} {:inline} P4(stoppingEvent: int) : bool;
function {:existential true} {:inline} P5(stoppingEvent: int) : bool;

function {:existential true} {:inline} Q0(stopped: int, stoppingFlag: int, stoppingEvent: int) : bool;
function {:existential true} {:inline} Q1(status: int, stopped: int, stoppingFlag: int, stoppingEvent: int) : bool;
function {:existential true} {:inline} Q2(stopped: int, stoppingEvent: int) : bool;
function {:existential true} {:inline} Q3(stopped: int) : bool;
function {:existential true} {:inline} Q4(stopped: int) : bool;
function {:existential true} {:inline} Q5(stopped: int) : bool;
function {:existential true} {:inline} Q6(stopped: int) : bool;

/*
			T1								T2

		(pendingIo == 1)&&(stoppingFlag == 0)&&(stoppingEvent == 0)&&(stopped == 0)

	P0:							Q0:

		stoppingEvent <= 1					(stoppingFlag == 0 && stopped == 0)||
									(stoppingFlag == 1 && stopped >= 0)


		stoppingFlag := 1;							if (stoppingFlag) {
												status := -1;
											} else {
												pendingIo := pendingIo + 1;
												status := 0;
											}

	P1:							Q1:

		stoppingEvent <= 1				(stoppingFlag == 0 && stopped == 0 && status == 0)||
								(stoppingFlag == 1 && stopped >= 0)

		pendingIo := pendingIo - 1;						if (status == 0) {
		pending_t1 := pendingIo;
	P2:							Q2:	assert(!stopped);

		stoppingEvent <= 1					stopped == 0
	
		if (pending_t1 == 0) {							}
	P3:							Q3:	
		stoppingEvent <= 1					stopped >= 0
								

			stoppingEvent := 1;						pendingIo := pendingIo - 1;	
		}									pending_t2 := pendingIo;
	P4:							Q4:
		stoppingEvent <= 1					stopped >= 0
		
		assume (stoppingEvent);							if (pending_t2 == 0) {
		stopped := 1;
	P5:							Q5:
		stoppingEvent <= 1					stopped >= 0			
												stoppingEvent := 1;
											}
								Q6:
									stopped >= 0


function {:existential true} {:inline} P0(stopped: int, stoppingEvent: int) : bool {
	stoppingEvent <= 1 && stopped == 0
}
function {:existential true} {:inline} P1(stoppingEvent: int) : bool {
	stoppingEvent <= 1
}
function {:existential true} {:inline} P2(stoppingEvent: int) : bool {
	stoppingEvent <= 1
}
function {:existential true} {:inline} P3(stoppingEvent: int) : bool {
	stoppingEvent <= 1
}
function {:existential true} {:inline} P4(stoppingEvent: int) : bool {
	stoppingEvent <= 1
}
function {:existential true} {:inline} P5(stoppingEvent: int) : bool {
	stoppingEvent <= 1
}

function {:existential true} {:inline} Q0(stopped: int, stoppingFlag: int, stoppingEvent: int) : bool {
	(stoppingFlag == 0 && stopped == 0 && stoppingEvent == 0)||(stoppingFlag == 1 && stopped >= 0)
}
function {:existential true} {:inline} Q1(status: int, stopped: int, stoppingFlag: int, stoppingEvent: int) : bool {
	(stoppingFlag >= 0 && stopped == 0 && status == 0 && stoppingEvent == 0)||(stoppingFlag == 1 && stopped >= 0  && status <= -1)
}
function {:existential true} {:inline} Q2(stopped: int, stoppingEvent: int) : bool {
	stopped == 0 && stoppingEvent == 0
}
function {:existential true} {:inline} Q3(stopped: int) : bool {
	stopped >= 0
}
function {:existential true} {:inline} Q4(stopped: int) : bool {
	stopped >= 0
}
function {:existential true} {:inline} Q5(stopped: int) : bool {
	stopped >= 0
}
function {:existential true} {:inline} Q6(stopped: int) : bool {
	stopped >= 0
}

*/

procedure pre_condition()
requires (pendingIo == 1)&&(stoppingFlag == 0)&&(stoppingEvent == 0)&&(stopped == 0);
{ 
	assert P0(stopped, stoppingEvent);
  	assert Q0(stopped, stoppingFlag,stoppingEvent );
}

procedure assert_at_Q2()
requires Q2(stopped, stoppingEvent);
{ 
  	assert stopped == 0;
}

procedure t1_transition_s1()
modifies stoppingFlag; 
requires P0(stopped, stoppingEvent);
ensures P1(stoppingEvent);
{ 
	stoppingFlag := 1;
}

procedure t1_transition_s2()
modifies pendingIo;
modifies pending_t1;  
requires P1(stoppingEvent);
ensures P2(stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure t1_transition_s3() 
requires P2(stoppingEvent);
{ 
	if (pending_t1 == 0) {
		assert P3(stoppingEvent);
	} else {
		assert P4(stoppingEvent);
	}
}

procedure t1_transition_s4()
modifies stoppingEvent;  
requires P3(stoppingEvent);
ensures P4(stoppingEvent);
{ 
	stoppingEvent := 1;
}

procedure t1_transition_s5()
modifies stopped;  
requires P4(stoppingEvent);
ensures P5(stoppingEvent);
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}

procedure t2_transition_s1()
modifies status;  
modifies pendingIo;
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures Q1(status, stopped, stoppingFlag,stoppingEvent );
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure t2_transition_s2()
requires Q1(status, stopped, stoppingFlag,stoppingEvent );
{ 
	if (status == 0) {
		assert Q2(stopped, stoppingEvent);
	} else {
		assert Q3(stopped);
	}
}

procedure t2_transition_s3()
requires Q2(stopped, stoppingEvent);
{ 
	assert Q3(stopped);
}

procedure t2_transition_s4()
modifies pendingIo;  
modifies pending_t2;
requires Q3(stopped);
ensures Q4(stopped);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure t2_transition_s5()
requires Q4(stopped);
{ 
	if (pending_t2 == 0) {
		assert Q5(stopped);
	} else {
		assert Q6(stopped);
	}
}

procedure t2_transition_s6()
modifies stoppingEvent;
requires Q5(stopped);
ensures Q6(stopped);
{ 
	stoppingEvent := 1;
}

procedure P0_stable_t2_s1()
modifies status;
modifies pendingIo; 
requires P0(stopped, stoppingEvent);
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures P0(stopped, stoppingEvent);
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure P0_stable_t2_s3()
modifies pendingIo;
modifies pending_t2;  
requires P0(stopped, stoppingEvent);
requires Q3(stopped);
ensures P0(stopped, stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure P0_stable_t2_s5()
modifies stoppingEvent;  
requires P0(stopped, stoppingEvent);
requires Q5(stopped);
ensures P0(stopped, stoppingEvent);
{ 
	stoppingEvent := 1;
}

procedure P1_stable_t2_s1()
modifies status; 
modifies pendingIo;
requires P1(stoppingEvent);
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures P1(stoppingEvent);
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure P1_stable_t2_s3()
modifies pendingIo;
modifies pending_t2;  
requires P1(stoppingEvent);
requires Q3(stopped);
ensures P1(stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure P1_stable_t2_s5()
modifies stoppingEvent;  
requires P1(stoppingEvent);
requires Q5(stopped);
ensures P1(stoppingEvent);
{ 
	stoppingEvent := 1;
}

procedure P2_stable_t2_s1()
modifies status; 
modifies pendingIo;
requires P2(stoppingEvent);
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures P2(stoppingEvent);
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure P2_stable_t2_s3()
modifies pendingIo;
modifies pending_t2;  
requires P2(stoppingEvent);
requires Q3(stopped);
ensures P2(stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure P2_stable_t2_s5()
modifies stoppingEvent;  
requires P2(stoppingEvent);
requires Q5(stopped);
ensures P2(stoppingEvent);
{ 
	stoppingEvent := 1;
}

procedure P3_stable_t2_s1()
modifies status; 
modifies pendingIo;
requires P3(stoppingEvent);
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures P3(stoppingEvent);
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure P3_stable_t2_s3()
modifies pendingIo;
modifies pending_t2;  
requires P3(stoppingEvent);
requires Q3(stopped);
ensures P3(stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure P3_stable_t2_s5()
modifies stoppingEvent;  
requires P3(stoppingEvent);
requires Q5(stopped);
ensures P3(stoppingEvent);
{ 
	stoppingEvent := 1;
}


procedure P4_stable_t2_s1()
modifies status; 
modifies pendingIo;
requires P4(stoppingEvent);
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures P4(stoppingEvent);
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure P4_stable_t2_s3()
modifies pendingIo;
modifies pending_t2;  
requires P4(stoppingEvent);
requires Q3(stopped);
ensures P4(stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure P4_stable_t2_s5()
modifies stoppingEvent;  
requires P4(stoppingEvent);
requires Q5(stopped);
ensures P4(stoppingEvent);
{ 
	stoppingEvent := 1;
}


procedure P5_stable_t2_s1()
modifies status; 
modifies pendingIo;
requires P5(stoppingEvent);
requires Q0(stopped, stoppingFlag,stoppingEvent );
ensures P5(stoppingEvent);
{ 
	if (stoppingFlag == 1) {
		status := -1;
	} else {
		pendingIo := pendingIo + 1;
		status := 0;
	}
}

procedure P5_stable_t2_s3()
modifies pendingIo;
modifies pending_t2;  
requires P5(stoppingEvent);
requires Q3(stopped);
ensures P5(stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t2 := pendingIo;
}

procedure P5_stable_t2_s5()
modifies stoppingEvent;  
requires P5(stoppingEvent);
requires Q5(stopped);
ensures P5(stoppingEvent);
{ 
	stoppingEvent := 1;
}

procedure Q0_stable_t1_s1()
modifies stoppingFlag;
requires Q0(stopped, stoppingFlag,stoppingEvent );
requires P0(stopped, stoppingEvent);
ensures Q0(stopped, stoppingFlag,stoppingEvent );
{ 
	stoppingFlag := 1;
}

procedure Q0_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q0(stopped, stoppingFlag,stoppingEvent );
requires P1(stoppingEvent);
ensures Q0(stopped, stoppingFlag,stoppingEvent );
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q0_stable_t1_s4()
modifies stoppingEvent;
requires (stoppingEvent == 1);	
requires Q0(stopped, stoppingFlag,stoppingEvent );
requires P3(stoppingEvent);
ensures Q0(stopped, stoppingFlag,stoppingEvent );
{ 
	stoppingEvent := 1;
}

procedure Q0_stable_t1_s5()
modifies stopped;
requires Q0(stopped, stoppingFlag,stoppingEvent );
requires P4(stoppingEvent);
ensures Q0(stopped, stoppingFlag,stoppingEvent );
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}

procedure Q1_stable_t1_s1()
modifies stoppingFlag;
requires Q1(status, stopped, stoppingFlag,stoppingEvent );
requires P0(stopped, stoppingEvent);
ensures Q1(status, stopped, stoppingFlag,stoppingEvent );
{ 
	stoppingFlag := 1;
}

procedure Q1_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q1(status, stopped, stoppingFlag,stoppingEvent );
requires P1(stoppingEvent);
ensures Q1(status, stopped, stoppingFlag,stoppingEvent );
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q1_stable_t1_s4()
modifies stoppingEvent;
requires (stoppingEvent == 1);	
requires Q1(status, stopped, stoppingFlag,stoppingEvent );
requires P3(stoppingEvent);
ensures Q1(status, stopped, stoppingFlag,stoppingEvent );
{ 
	stoppingEvent := 1;
}

procedure Q1_stable_t1_s5()
modifies stopped;
requires Q1(status, stopped, stoppingFlag,stoppingEvent );
requires P4(stoppingEvent);
ensures Q1(status, stopped, stoppingFlag,stoppingEvent );
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}



procedure Q2_stable_t1_s1()
modifies stoppingFlag;
requires Q2(stopped, stoppingEvent);
requires P0(stopped, stoppingEvent);
ensures Q2(stopped, stoppingEvent);
{ 
	stoppingFlag := 1;
}

procedure Q2_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q2(stopped, stoppingEvent);
requires P1(stoppingEvent);
ensures Q2(stopped, stoppingEvent);
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q2_stable_t1_s4()
modifies stoppingEvent;
requires (stoppingEvent == 1);	
requires Q2(stopped, stoppingEvent);
requires P3(stoppingEvent);
ensures Q2(stopped, stoppingEvent);
{ 
	stoppingEvent := 1;
}

procedure Q2_stable_t1_s5()
modifies stopped;
requires Q2(stopped, stoppingEvent);
requires P4(stoppingEvent);
ensures Q2(stopped, stoppingEvent);
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}




procedure Q3_stable_t1_s1()
modifies stoppingFlag;
requires Q3(stopped);
requires P0(stopped, stoppingEvent);
ensures Q3(stopped);
{ 
	stoppingFlag := 1;
}

procedure Q3_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q3(stopped);
requires P1(stoppingEvent);
ensures Q3(stopped);
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q3_stable_t1_s4()
modifies stoppingEvent;
requires Q3(stopped);
requires P3(stoppingEvent);
ensures Q3(stopped);
{ 
	stoppingEvent := 1;
}

procedure Q3_stable_t1_s5()
modifies stopped;
requires Q3(stopped);
requires P4(stoppingEvent);
ensures Q3(stopped);
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}




procedure Q4_stable_t1_s1()
modifies stoppingFlag;
requires Q4(stopped);
requires P0(stopped, stoppingEvent);
ensures Q4(stopped);
{ 
	stoppingFlag := 1;
}

procedure Q4_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q4(stopped);
requires P1(stoppingEvent);
ensures Q4(stopped);
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q4_stable_t1_s4()
modifies stoppingEvent;
requires Q4(stopped);
requires P3(stoppingEvent);
ensures Q4(stopped);
{ 
	stoppingEvent := 1;
}

procedure Q4_stable_t1_s5()
modifies stopped;
requires Q4(stopped);
requires P4(stoppingEvent);
ensures Q4(stopped);
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}




procedure Q5_stable_t1_s1()
modifies stoppingFlag;
requires Q5(stopped);
requires P0(stopped, stoppingEvent);
ensures Q5(stopped);
{ 
	stoppingFlag := 1;
}

procedure Q5_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q5(stopped);
requires P1(stoppingEvent);
ensures Q5(stopped);
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q5_stable_t1_s4()
modifies stoppingEvent;
requires Q5(stopped);
requires P3(stoppingEvent);
ensures Q5(stopped);
{ 
	stoppingEvent := 1;
}

procedure Q5_stable_t1_s5()
modifies stopped;
requires Q5(stopped);
requires P4(stoppingEvent);
ensures Q5(stopped);
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}




procedure Q6_stable_t1_s1()
modifies stoppingFlag;
requires Q6(stopped);
requires P0(stopped, stoppingEvent);
ensures Q6(stopped);
{ 
	stoppingFlag := 1;
}

procedure Q6_stable_t1_s2()
modifies pendingIo;
modifies pending_t1;  
requires Q6(stopped);
requires P1(stoppingEvent);
ensures Q6(stopped);
{ 
	pendingIo := pendingIo - 1;
	pending_t1 := pendingIo;
}

procedure Q6_stable_t1_s4()
modifies stoppingEvent;
requires Q6(stopped);
requires P3(stoppingEvent);
ensures Q6(stopped);
{ 
	stoppingEvent := 1;
}

procedure Q6_stable_t1_s5()
modifies stopped;
requires Q6(stopped);
requires P4(stoppingEvent);
ensures Q6(stopped);
{ 
	assume (stoppingEvent == 1);
	stopped := 1;
}

