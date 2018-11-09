/*Manual Invarinat*/

function {:existential true} {:inline} Req_id (x: int) : bool;

function {:existential true} {:inline} Ens_id (x: int, ret: int) : bool;

procedure id (x: int) returns (ret: int)

requires Req_id(x);

ensures Ens_id(x, ret);

{
	var temp_ret: int;

	if (x == 0) {

		ret := 0;

	} else {

		call temp_ret := id (x - 1);

		ret := temp_ret + 1;

	}
}


procedure main() {

	var ret, input: int;

	input := 5;

  	call ret := id(input);

	assert ret == 5;
}
