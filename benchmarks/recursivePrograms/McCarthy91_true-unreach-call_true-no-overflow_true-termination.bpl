/* function {:existential true} {:inline} Req (x: int) : bool {
  true
}
function {:existential true} {:inline} Ens (x: int, result: int) : bool {
  (result == 91) || ((x > 101) && (result == (x - 10)))
} 

function {:existential true} {:inline} Req (x: int) : bool;
requires Req(x);

*/

function {:existential true} {:inline} Ens (x: int, y: int) : bool;

procedure f91 (x: int) returns (result: int)

ensures Ens(result, x);
{
	var temp_result: int;

	if (x > 100) {

		result := x - 10;

	} else {

		call temp_result := f91(x + 11);

		call result := f91(temp_result);
	}
}

procedure main() {

	var x: int;

	var result: int;

	havoc x;

  	call result := f91(x);

	assert ((result == 91) || ((x > 101) && (result == (x - 10))));
}












