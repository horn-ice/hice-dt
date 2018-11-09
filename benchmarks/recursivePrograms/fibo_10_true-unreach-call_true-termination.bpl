//function {:existential true} {:inline} Req(n: int) : bool;

function {:existential true} {:inline} Ens(n: int, result: int, result_aux: int) : bool;

procedure fibo(n: int) returns (result: int)

//requires Req(n);

ensures Ens(n, result, result + 1);
{
	var fibo_n_1: int;

	var fibo_n_2: int;

    	if (n < 1) {

        	result := 0;

		assert Ens(n, 0, 1);

    	} else if (n == 1) {

        	result := 1;

		assert Ens(1, 1, 2);

    	} else {

		call fibo_n_1 := fibo(n - 1);

		//assert Ens(n - 1, 1 - n, fibo_n_1);

		call fibo_n_2 := fibo(n - 2);

		//assert Ens(n - 2, 2 - n, fibo_n_2);

        	result := fibo_n_1 + fibo_n_2;
    	}
}

procedure main() {

	var result: int;

	call result := fibo(10);

	assert (result == 55);
}
