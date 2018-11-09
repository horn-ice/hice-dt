.PHONY: all boogie chc_verifier hice-dt z3 clean

all: boogie z3 hice-dt chc_verifier
	cp ./z3-4.7.1/build/z3 ./Boogie/Binaries/z3.exe
	cp ./hice-dt/src/hice-dt ./Boogie/Binaries/

boogie:
	xbuild /p:TargetFrameworkVersion="v4.5" /p:TargetFrameworkProfile="" /p:WarningLevel=1 ./Boogie/Source/Boogie.sln

hice-dt:
	make -C ./hice-dt/src/

chc_verifier: z3
	make -C ./chc_verifier/src/

z3:
	cd ./z3-4.7.1; \
	python scripts/mk_make.py
	make -C ./z3-4.7.1/build
	find ./z3-4.7.1/build -name '*.o' | xargs ar rs ./z3-4.7.1/build/z3.a

clean:
	xbuild /t:clean ./Boogie/Source/Boogie.sln
	make -C hice-dt/src/ clean
	make -C chc_verifier/src/ clean
	rm -rf ./Boogie/Binaries
	rm -rf ./z3-4.7.1/build/
