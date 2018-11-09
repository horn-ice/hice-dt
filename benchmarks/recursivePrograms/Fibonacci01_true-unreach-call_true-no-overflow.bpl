function {:existential true} {:inline} Req(n: int) : bool;
function {:existential true} {:inline} Ens(n: int, result: int) : bool;

procedure fibo(n: int) returns (result: int)
requires Req(n);
ensures Ens(n, result);
{
	var fibo_n_1: int;
	var fibo_n_2: int;
    	if (n < 1) {
        	result := 0;
		assert Ens(n, 1);
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
	var x, result: int;
	havoc x;
	assume (!(x > 46 || x == -2147483648));
	call result := fibo(x);
	assert (result >= (x - 1));
}
