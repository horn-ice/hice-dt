/*Manual Invarinat*/

function {:existential true} {:inline} Req_id (x: int) : bool;

function {:existential true} {:inline} Ens_id (x: int, ret: int) : bool;

function {:existential true} {:inline} Req_id2 (x: int) : bool;

function {:existential true} {:inline} Ens_id2 (x: int, ret: int) : bool;

procedure id (x: int) returns (ret: int)

requires Req_id(x);

ensures Ens_id(x, ret);

{
	var temp_ret: int;

	if (x == 0) {

		ret := 0;

	} else {

		call temp_ret := id2 (x - 1);

		temp_ret := temp_ret + 1;

		if (temp_ret > 2) {

			ret := 2;
		
		} else {

			ret := temp_ret;
		}
	}
}

procedure id2 (x: int) returns (ret: int)

requires Req_id2 (x);

ensures Ens_id2 (x, ret);

{
	var temp_ret: int;

	if (x == 0) {

		ret := 0;
	
	} else {

		call temp_ret := id (x - 1);

		temp_ret := temp_ret + 1;	

		if (temp_ret > 2) {

			ret := 2;

		} else {

			ret := temp_ret;

		}	
	} 
}

procedure main() {

	var ret, input: int;

	havoc input;

  	call ret := id(input);

	assert ret != 3;
}
