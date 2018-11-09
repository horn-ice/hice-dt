function {:existential true} {:inline} Req(n: int) : bool;
function {:existential true} {:inline} Ens(n: int, result: int) : bool;

procedure fibo(n: int) returns (result: int)
requires Req(n);
ensures Ens(n, result);

//ensures (n == -2 ==> result == 0) && (n == -1 ==> result == 0) && (n == 0 ==> result == 0) && (n == 1 ==> result == 1) && 
//(n == 2 ==> result == 1) && (n == 3 ==> result == 2) && (n == 4 ==> result == 3) && (n == 5 ==> result == 5);

{
	var fibo_n_1: int;
	var fibo_n_2: int;
    	if (n < 1) {
        	result := 0;
    	} else if (n == 1) {
        	result := 1;
		assert Ens(1, 1);
    	} else {
		call fibo_n_1 := fibo(n - 1);
		call fibo_n_2 := fibo(n - 2);
        	result := fibo_n_1 + fibo_n_2;
    	}
}

procedure main() {
	var result: int;
	call result := fibo(5);
	//assert (result == 5);
	assert (result > 2);
}
