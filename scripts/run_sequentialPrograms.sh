#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/sequentialPrograms

run_the_test() {

	FileNames=$(ls $path/*.smt2)

	for file_name in $FileNames; do

		echo "Verifying:" $(basename $file_name) "..."

		timeout 600 ../chc_verifier/src/chc_verifier -b -h $file_name > $file_name.time
	done

	echo "Test of sequential benchmark programs finished successfully."
}

run_the_test
