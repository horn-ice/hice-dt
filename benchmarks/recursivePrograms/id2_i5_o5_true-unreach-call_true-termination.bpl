function {:existential true} {:inline} Req_id (x: int) : bool;
function {:existential true} {:inline} Ens_id (x: int, result: int) : bool;
function {:existential true} {:inline} Req_id2 (x: int) : bool;
function {:existential true} {:inline} Ens_id2 (x: int, result: int) : bool;

procedure id (x: int) returns (result: int)
requires Req_id(x);
ensures Ens_id(x, result);
{
	var temp_result: int;
	if (x == 0) {
		result := 0;
		assert Ens_id (0, 0);
	} else {
		call temp_result := id2 (x - 1);
		result := temp_result + 1;
	}	
}

procedure id2 (x: int) returns (result: int)
requires Req_id2 (x);
ensures Ens_id2 (x, result);
{
	var temp_result: int;
	if (x == 0) {
		result := 0;
		assert Ens_id2 (0, 0);
	} else {
		call temp_result := id (x - 1);
		result := temp_result + 1;
	}	
}

procedure main() {
	var result: int;
  	call result := id(5);
	assert result == 5;
}
