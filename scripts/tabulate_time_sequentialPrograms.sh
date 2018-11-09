#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/sequentialPrograms

elapsed(){
	grep "Total time:" $1 | cut -d\  -f3

}

tabulate_test_time(){
	
	FileNames=$(ls $path/*.time)
	echo "Benchmark name, Time in seconds"> tabulated_sequentialProgramResult.csv
	for file_name in $FileNames; do
		echo  $(basename $file_name), $(elapsed $file_name) >> tabulated_sequentialProgramResult.csv
	done
	echo "Tabulations of sequential programs completed successfully."
}

tabulate_test_time
