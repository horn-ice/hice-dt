
function {:existential true} {:inline} Req_f(n: int) : bool;
function {:existential true} {:inline} Ens_f(n: int) : bool;
function {:existential true} {:inline} Req_f2(n: int) : bool;
function {:existential true} {:inline} Ens_f2(n: int) : bool;


procedure f(n: int)
requires Req_f(n);
ensures Ens_f(n);
{
	var temp_n: int;
	if (n < 3) {
	} else {
		temp_n := n - 1;
		call f2(temp_n);
		assert true;
	}
}

procedure f2(n: int)
requires Req_f2(n);
ensures Ens_f2(n);
{
	var temp_n: int;	
	if (n < 3) {
	} else {
		temp_n := n - 1;
		call f(temp_n);
		assert true;
	}
}
 
procedure main() {
  	call f(2);
}
