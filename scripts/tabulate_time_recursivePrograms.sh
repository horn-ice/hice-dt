#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/recursivePrograms

elapsed() {

	grep "," $1 | cut -d\  -f3
}

tabulate_test_time() {
	
	FileNames=$(ls $path/*.statistics)

	echo "Benchmark program, Rounds, Positive, Negative, Horn, Prover Time(s), Total Time (s)"> tabulated_recursiveProgramResult.csv
	
	for file_name in $FileNames; do

		echo  $(elapsed $file_name) >> tabulated_recursiveProgramResult.csv
	done

	echo "Tabulations of recursive programs completed successfully."
}

tabulate_test_time
