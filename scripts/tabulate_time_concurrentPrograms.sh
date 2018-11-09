#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/concurrentPrograms

elapsed() {

	grep "," $1 | cut -d\  -f3
}

tabulate_test_time() {
	
	FileNames=$(ls $path/*.statistics)

	echo "Benchmark program, Rounds, Positive, Negative, Horn, Prover Time(s), Total Time (s)"> tabulated_concurrentProgramResult.csv
	
	for file_name in $FileNames; do

		echo  $(elapsed $file_name) >> tabulated_concurrentProgramResult.csv
	done

	echo "Tabulations of concurrent programs completed successfully."
}

tabulate_test_time
