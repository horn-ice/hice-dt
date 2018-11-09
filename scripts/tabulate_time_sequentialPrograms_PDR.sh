#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/sequentialPrograms

elapsed(){

	grep "Total time:" $1 | cut -d\  -f4

}

tabulate_test_time(){

	FileNames=$(ls $path/*.time)

	echo "Benchmark name, Time in seconds"> tabulated_sequentialProgramResult_PDR.csv

	for file_name in $FileNames; do

		echo  $(basename $file_name), $(elapsed $file_name) >> tabulated_sequentialProgramResult_PDR.csv
	done

	echo "Tabulations of sequential programs using z3 completed successfully."
}

tabulate_test_time
