/*
					{hours == 0, Morning == 1, Evening == 0} 

	while (1) {						while (1) {

	P0:							Q0:
	
	(hours <= 12 && Morning == 0 && Evening == 1) ||	(hours <= 12 && Morning == 1 && Evening == 0) ||
	(hours == 0 && Morning == 1 && Evening == 0)		(hours == 0 && Morning == 0 && Evening == 1)

s1:		while (Morning != 1) {					while (Evening != 1) {
	P'							Q'
			;							;	
		}							}


	P1:							Q1:

	(hours <= 12 && Morning == 1 && Evening == 0) 		(hours <= 12 && Morning == 0 && Evening == 1)
					

		while (Morning == 1 && hours < 12) {			while (Evening == 1 && hours < 12) {
s2:			hours := hours + 1;					hours := hours + 1;
		}							}

		hours := 0;						hours := 0;
		Morning := 0;						Morning := 1;
s3:		Evening := 1;						Evening := 0;

	P2:							Q2:

	(hours <= 12 && Morning == 0 && Evening == 1) ||	(hours <= 12 && Morning == 1 && Evening == 0) ||
	(hours == 0 && Morning == 1 && Evening == 0)		(hours == 0 && Morning == 0 && Evening == 1)

	}							}

function {:existential true} {:inline} Invariant (hours: int, Morning: int, Evening: int) : bool {
   ((hours <= 12) && ((Morning == 1 && Evening == 0) || (Morning == 0 && Evening == 1)))
}
*/

var hours: int;
var Morning: int;
var Evening: int;

function {:existential true} {:inline} Invariant (hours: int, Morning: int, Evening: int) : bool;

procedure init() 
requires hours == 0 && ((Morning == 1 && Evening == 0) || (Morning == 0 && Evening == 1));
{
	assert Invariant (hours, Morning, Evening);
}

procedure post() 
requires Invariant (hours, Morning, Evening);
{
	assert Morning != Evening;
}

procedure t1_serial() 
modifies hours;
modifies Morning;
modifies Evening;
requires Invariant (hours, Morning, Evening);
{
	if (*) {
		call A_2();
	}
	if (Morning == 1 && hours < 12) {
		hours := hours + 1;
	}
	assert Invariant (hours, Morning, Evening);

	if (*) {
		call A_2();
	}
	if (Morning == 1 && hours >= 12) {
		hours := 0;
		Morning := 1;
		Evening := 0;
	}
	assert Invariant (hours, Morning, Evening);

	if (*) {
		call A_2();
	}
}


procedure t2_serial() 
modifies hours;
modifies Morning;
modifies Evening;
requires Invariant (hours, Morning, Evening);
{
	if (*) {
		call A_1();
	}
	if (Evening == 1 && hours < 12) {
		hours := hours + 1;
	}
	assert Invariant (hours, Morning, Evening);

	if (*) {
		call A_1();
	}
	if (Evening == 1 && hours >= 12) {
		hours := 0;
		Morning := 1;
		Evening := 0;
	}
	assert Invariant (hours, Morning, Evening);

	if (*) {
		call A_2();
	}
}


procedure A_2() 
modifies hours;
modifies Morning;
modifies Evening;
requires Invariant (hours, Morning, Evening);
ensures Invariant (hours, Morning, Evening);
{
	if (*) {
		if (Evening == 1 && hours < 12) {
			hours := hours + 1;
		}
		
	} 	
	if (*) {
		if (Evening == 1 && hours >= 12) {
			hours := 0;
			Morning := 1;
			Evening := 0;
		}
	}
}

procedure A_1() 
modifies hours;
modifies Morning;
modifies Evening;
requires Invariant (hours, Morning, Evening);
ensures Invariant (hours, Morning, Evening);
{
	if (*) {
		if (Morning == 1 && hours < 12) {
			hours := hours + 1;
		}
		
	} 
	if (*) {
		if (Morning == 1 && hours >= 12) {
			hours := 0;
			Morning := 1;
			Evening := 0;
		}
	}
}
