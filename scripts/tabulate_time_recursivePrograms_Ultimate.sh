#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/recursivePrograms

elapsed(){

	grep "Total time:" $1 | cut -d\  -f4

}

tabulate_test_time(){

	FileNames=$(ls $path/*.time_ultimate)

	echo "Benchmark name, Time in seconds"> tabulated_recursiveProgramResult_Ultimate.csv

	for file_name in $FileNames; do

		echo  $(basename $file_name), $(elapsed $file_name) >> tabulated_recursiveProgramResult_Ultimate.csv
	done

	echo "Tabulations of recursive programs using Ultimate is completed successfully."
}

tabulate_test_time
