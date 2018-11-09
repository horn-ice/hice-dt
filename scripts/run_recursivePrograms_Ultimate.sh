#! /bin/bash

# Timeout
TIMEOUT=600

# Path to Ultimate.py
ULTIMATE_PATH=${1?Path to Ultimate.py not specified (use first command line argument)}

path="$(dirname "$PWD")"/benchmarks/recursivePrograms

run_the_test() {

	FileNames=$(ls $path/*.c)

	for file_name in $FileNames; do

		echo $file_name

		START=$(date +%s.%N)

		echo "Verifying: $file_name ..."
		
                timeout $TIMEOUT $ULTIMATE_PATH/Ultimate.py --spec ./ReachSafety.prp --file $file_name --architecture 64bit > $file_name.output_ultimate

		DIFF=$(echo "$(date +%s.%N) - $START" | bc)

		echo $file_name "Total time:" $DIFF > $file_name.time_ultimate

	done

	echo "Test of recursive benchmark programs using ULTIMATE is finished successfully."
}


# Generate Ultimate Automizer property file
echo "CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )" > ReachSafety.prp

run_the_test

# Remove property file
rm ReachSafety.prp
