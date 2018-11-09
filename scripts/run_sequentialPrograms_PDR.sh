#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/sequentialPrograms

run_the_test() {

	FileNames=$(ls $path/*.smt2)

	for file_name in $FileNames; do

		echo $file_name

		START=$(date +%s.%N)

                timeout 600 ../z3-4.7.1/build/z3 $file_name

		DIFF=$(echo "$(date +%s.%N) - $START" | bc)

		echo $file_name "Total time:" $DIFF > $file_name.time
	done

	echo "Test of sequential benchmark programs using z3 is finished successfully."
}

run_the_test






