Horn-ICE Verification Toolkit
=============================

This documents describes how to build and use the Horn-ICE verification toolkit described in the paper ["Horn-ICE Learning for Synthesizing Invariants and Contracts"](https://doi.org/10.1145/3276501).

This toolkit consists of two different verifiers, both using the Horn-ICE Decision Tree Learning Algorithm:

1. A verifier built on top of Microsoft [Boogie](https://github.com/boogie-org/boogie), which verifies programs given in the Boogie verification language
2. A verifier for Constrained Horn Clauses built on top of Microsoft [Z3](https://github.com/Z3Prover/z3), which verifies constrained Horn clauses in the SMTLib2 datalog format (e.g., as produced by [SeaHorn](http://seahorn.github.io/))

Getting Started
---------------

The following instructions assume a recent Linux operating system (e.g., Ubuntu 16.04). If you are running another operating system, such as Windows or MacOS, we recommend using a virtual machine with Ubuntu 16.04 guest operating system.

The Horn-ICE verification toolkit is portable and can be compiled on MacOS and Windows (e.g., using mingw and MSYS). However, the instructions in this document need to be modified accordingly.


### Requirements
The Horn-ICE verification toolkit requires the following software installed:

- [GNU make](https://www.gnu.org/software/make/)
- [GNU compiler collection](https://gcc.gnu.org/) (specifically `g++` version 5.4 or newer, including support for [OpenMP](https://www.openmp.org))
- [Mono](https://www.mono-project.com/) (version 4.2.1 or newer)
- [Python](https://www.python.org/) (2.7 or newer)

Use the following commands to install the required software in Ubuntu 16.04 (or consult the documentation of your Linux distribution):

- `sudo apt-get install build-essential`
- `sudo apt-get install mono-complete`
- `sudo apt-get install python`


### Building the Toolkit

The build process is automated. To build the Horn-ICE verification toolkit, simply execute the command

    make

in the folder you have extracted the archive to. This will build the following three components (in this order):

1. Boogie
2. Z3
3. The Horn-ICE decision tree learning algorithm
4. The verifier for constrained Horn clauses (which requires Z3 to be built first)

After building has completed, the compiled binaries of the Boogie-based verifier are located in `./Boogie/Binaries/`, while the binaries of the verifier for constraint Horn clauses are located in `./chc_verifier/src/`.

You can test whether the build process was successful by following the instructions in the section *Running a Single Benchmark*.

If you seek to modify any of the components, the remainder of this section explains how to build each in detail. You can also refer to the `Makefile` for more information.

#### Building Boogie

To compile Boogie, change into `./Boogie/Source/` and execute the command

    xbuild /p:TargetFrameworkVersion="v4.5" /p:TargetFrameworkProfile="" /p:WarningLevel=1 Boogie.sln

The additional options `/p:TargetFrameworkVersion="v4.5"` and `/p:TargetFrameworkProfile=""` are not necessary in general, but are sometimes required in order to fix a specific problem with Mono on Ubuntu 16.04. Warning messages produced during compilation are safe to ignore. The option `/p:WarningLevel=1` sets the warning level to a value that suppresses trivial warnings.

After a successful compilation, the binaries are located in `./Boogie/Binaries/`.

#### Building Z3

Z3 4.7.1 is shipped with this toolkit and is located in the folder `./z3-4.7.1/`. To build Z3, please follow the instructions in `README.md` or on the [Z3 website](https://github.com/Z3Prover/z3).

Once Z3 has successfully been compiled, copy the file `z3` in the folder `./z3-4.7.1/` to `./Boogie/Binaries/` and rename it to `z3.exe`. Alternatively, you can specify the file name and location of the Z3 binary using the option `-z3exe:` when running Boogie.

The verifier for constrained Horn clauses requires a static library of Z3 to link against. In order to create such a library, change into the directory `./z3-4.7.1/build/` and execute the following command

    find . -name '*.o' | xargs ar rs ./z3.a

This creates a file named `z3.a` inside `./z3-4.7.1/build/`.

#### Building the Horn-ICE Decision Tree Learning Algorithm

To compile the Horn-ICE Decision Tree Learning Algorithm, change into the directory `./hice-dt/src/` and execute the command

    make

After successful compilation, the binaries are located inside `./hice-dt/src/`. Copy the file `hice-dt` (or `hice-dt.exe`on Windows) to `./Boogie/Binaries/`.

#### Building the Verifier for Constrained Horn Clauses

To compile the Verifier for Constrained Horn Clauses, change into the directory `./chc_verifier/src/` and execute the command

    make

After successful compilation, the binary is located inside `./chc_verifier/src/`.


### Running a Single Benchmark

The following instructions show how to run a single benchmark using the Boogie-based verifier and the verifier for constrained Horn clauses.

**Note:** Benchmarks can be found in `./benchmarks/`.

#### The Boogie-Based Verifier

All binaries of the Boogie-based verifier should be present in `./Boogie/Binaries/`.

**Note:** It is easiest to run Boogie from inside the `./Boogie/Binaries/` directory.

To verify a Boogie `.bpl` program, execute the following command inside the `./Boogie/Binaries/` directory:

    mono Boogie.exe -trace -nologo -noinfer -contractInfer -mlHoudini:./hice-dt -learnerOptions:"-b -h" my_benchmark.bpl

The given options have the following effect:

- `-trace` (optional): prints intermediate results and status information
- `-nologo` (optional): suppresses the printing of the Boogie version at start-up
- `-noinfer` (required): disables some of Boogie's internal static analysis techniques, which interfere with our invariant synthesis approach
- `-contractInfer` (required): enables automatic invariant synthesis
- `-mlHoudini:arg` (required): `arg` specifies the binary of the Horn-ICE learning algorithm (`./hice-dt` in our case since we are executing Boogie from the same directory the file `hice-dt` is located in)
- `-learnerOptions:"options"` (optional): `options` specifies options that get passed through to the Horn-ICE learning algorithm as if it were called from the command line (in our case, we run a bounded version `-b` and use a Houdini pre-phase `-h`); multiple options need to be enclosed by quotes

Our extension of Boogie supports most of Boogie's command line options. Please refer to the manual for more information.

**Note:** The way options are specified differs between Windows and Linux. Use `"-"` on Linux and `"/"` on Windows.

**Note:** On Windows, the Horn-ICE Decision Tree Learning Algorithm might have the file extension `.exe`. To account for this, use the full file name `hice-dt.exe` when giving the option `-mlHoudini:`.

**Note:** If you do not want to run Boogie from inside `./Boogie/Binaries/`, the option `-mlHoudini:` needs to point to the location of the binary of the Horn-ICE learning algorithm. It is best to specify an absolute path.

**Note:** Boogie generates many temporary files to communicate with the Horn-ICE learning algorithm. These file are safe to remove after a successful verification. Should you be interested in reading these files, the header `./hice-dt/include/boogie_io.h` contains descriptions of their format.

#### Verifier for Constrained Horn Clauses

All binaries of the verifier for constrained Horn clauses should be present in `./chc_verifier/src/`.

To verify a constrained Horn clause, execute the following command inside the `./chc_verifier/src/` directory:

    ./chc_verifier my_benchmark.smt2

Like the Horn-ICE Decision Tree Learning Algorithm, the Verifier for Constrained Horn Clauses takes two options, which are optional and can be used in any combination:
- `-b`: runs the bounded version of the decision tree learner
- `-h`: runs the Houdini pre-phase

**Note:** The verifier for constrained Horn clauses does not have special library dependencies and can be moved to any other location if desired.


Running the Benchmark Suits
---------------------------

The following instructions describe how the benchmarks can be run on a machine that has the Horn-ICE verification toolkit installed as described above. We provide three different types of benchmarks:

1. recursive programs,
2. concurrent programs, and
3. sequential programs.

The benchmarks are located in the `./benchmarks/` directory.

### Running the Entire Benchmark Suite

The entire benchmark suite can be executed using the following command from inside the `./scripts/` directory:

    sh runAll.sh

**Note:** Running the entire benchmark suite takes around 7 hours on an Intel Core i3-6006U CPU @ 2 GHz. 

The `runAll.sh` script will generate three log files, as described below. The first two files result from the Boogie-based verifier, while the third file from the verifier for Constrained Horn Clauses.

1. `tabulated_recursiveProgramResult.csv` lists all the recursive benchmark programs along with the execution details. The execution details includes number of rounds between teacher and learner, number of Positive, Negative and Horn samples, the time taken by the learner and the verification process. Table-1 in the paper contains these details. We have compared the Boogie-based verifier with Ultimate Automizer in Figure 5 using the data from the above mentioned file.

2. `tabulated_concurrentProgramResult.csv` lists all the concurrent benchmark programs along with the execution details. The execution details includes number of rounds between teacher and learner, number of Positive, Negative and Horn samples, the time taken by the learner and the verification process. Table 2 in the paper contains these details. 

3. `tabulated_sequentialProgramResult.csv` lists all the sequential benchmark programs along with the execution time. Table 3 in the Paper contain these details. We have compared the verifier for Constrained Horn Clauses with PDR in Figure 6 using the data from the above mentioned file.

### Running an Individual Benchmark Set

The `./scripts/` directory contains scripts to execute individual sets of benchmarks and to tabulate their results:

- The recursive programs can be verified and their results tabulated using the command

      sh run_recursivePrograms.sh; sh tabulate_time_recursivePrograms.sh 

- The concurrent programs can be verified and their results tabulated using the command

      sh run_concurrentPrograms.sh; sh tabulate_time_concurrentPrograms.sh 
    
- The sequential programs can be verified and their results tabulated using the command

      sh run_sequentialPrograms.sh; sh tabulate_time_sequentialPrograms.sh 


Comparing Horn-ICE to Other Tools
---------------------------------

The remainder of this document explains how we compared Horn-ICE to other tools.

### Experimental Results Mentioned in the Paper

The experimental results described in the paper *"Horn-ICE Learning for Synthesizing Invariants and Contracts"* can be reproduced as follows:

1. Table 1 to 3 can be produced using the following command inside the `./scripts/` directory

        sh runAll.sh
    
2. Figure 5 and 6 have been constructed using the above data along with the experimental results obtained by running the verification tools *Ultimate Automizer* and *PDR* on the same environment. For more details, see the information below.

###  Verification using Ultimate Automizer

Download Ultimate Automizer form https://github.com/ultimate-pa/ultimate/releases. 

If you want to build Ultimate Automizer yourself, follow the instructions in the file `README`. Otherwise, you can use a pre-compiled package.

#### Running the Entire Recursive Programs using Ultimate Automizer

The entire recursive program benchmarks can be verified using the following command inside the `./scripts/` directory:

    sh run_recursivePrograms_Ultimate.sh path_to_Ultimate.py; sh tabulate_time_recursivePrograms_Ultimate.sh

**Note:** The script `run_recursivePrograms_Ultimate.sh` takes one mandatory argument, the path to `Ultimate.py` (where the Ultimate Automizer binaries are located).

**Note:** Z3 needs to be accessible from inside `./scripts/` (e.g., copy it there).

The above command will produce a file named `tabulated_recursiveProgramResult_Ultimate.csv`, which lists all recursive benchmarks together with the time taken to verify them.

###  Verification of Constrained Horn Clauses (Sequential Program) using PDR

The default CHC verification engine of `Z3 4.7.1` is PDR. The following command inside the `./z3-4.7.1/build/` directory can be used to verify the Constrained Horn Clauses using PDR:

    ./z3 CHC_file_Name.smt2

#### Running the Entire Sequential Benchmark Set using PDR

The entire set of sequential programs (in form of Constrained Horn Clauses) can be verified using the following command inside the `./scripts/` directory:

    sh run_sequentialPrograms_PDR.sh; sh tabulate_time_sequentialPrograms_PDR.sh

**Note:** Z3 needs to be accessible from inside `./scripts/` (e.g., copy it there).
	
The above command produces a file named `tabulated_sequentialProgramResult_PDR.csv`, which lists all the sequential benchmarks together with the time taken to verify them.