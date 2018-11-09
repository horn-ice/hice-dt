#! /bin/bash

path="$(dirname "$PWD")"/benchmarks/recursivePrograms

run_the_test() {

	FileNames=$(ls $path/*.bpl)

	for file_name in $FileNames; do

		echo "Verifying:" $(basename $file_name) "..."

		timeout 600 mono ../Boogie/Binaries/Boogie.exe -nologo -noinfer -contractInfer -mlHoudini:../Boogie/Binaries/hice-dt -learnerOptions:"-b -h" -printAssignment -z3opt:sat.random_seed=111111 -trace $file_name > $file_name.time

	done

	echo "Test of recursive benchmark programs finished successfully."
}

run_the_test
