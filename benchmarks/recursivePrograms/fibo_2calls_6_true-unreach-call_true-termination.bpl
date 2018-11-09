function {:existential true} {:inline} Req1(n: int) : bool;
function {:existential true} {:inline} Ens1(n: int, result: int) : bool;
function {:existential true} {:inline} Req2(n: int) : bool;
function {:existential true} {:inline} Ens2(n: int, result: int) : bool;

procedure fibo1(n: int) returns (result: int)
//requires Req1(n);
ensures Ens1(n, result);
{
	var fibo_n_1: int;
	var fibo_n_2: int;
    	if (n < 1) {
        	result := 0;
    	} else if (n == 1) {
        	result := 1;
		assert Ens1(1, 1);
    	} else {
		call fibo_n_1 := fibo2(n - 1);
		call fibo_n_2 := fibo2(n - 2);
        	result := fibo_n_1 + fibo_n_2;
    	}
}

procedure fibo2(n: int) returns (result: int)
//requires Req2(n);
ensures Ens2(n, result);
{
	var fibo_n_1: int;
	var fibo_n_2: int;
    	if (n < 1) {
        	result := 0;
    	} else if (n == 1) {
        	result := 1;
		assert Ens2(1, 1);
    	} else {
		call fibo_n_1 := fibo1(n - 1);
		call fibo_n_2 := fibo1(n - 2);
        	result := fibo_n_1 + fibo_n_2;
    	}
}

procedure main() {
	var result: int;
	call result := fibo1(6);
	assert (result == 8);
}
