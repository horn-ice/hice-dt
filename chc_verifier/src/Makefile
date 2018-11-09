.PHONY: clear

OBJS =  boogie_io.o \
	decision_tree.o \
        horn_constraint.o \
        output_visitor.o \
       	pretty_print_visitor.o \
        horn_solver.o \
        datapoint.o \
        job.o 

CPPFLAGS += -I ../include
CPPFLAGS += -I ../../hice-dt/include
CPPFLAGS += -I ../../z3-4.7.1/src/api
CPPFLAGS += -I ../../z3-4.7.1/src/api/c++
CPPFLAGS += -L ../../z3-4.7.1/build
CPPFLAGS += -std=c++14 -Ofast

all: chc_verifier

chc_verifier: $(OBJS)
	$(CXX) $(CPPFLAGS) $(LDFLAGS) -fopenmp -o chc_verifier chc_verifier.cpp $(OBJS) ../../z3-4.7.1/build/z3.a

%.o: %.cpp
	$(CXX) $(CPPFLAGS) -c $< -o $@
   
clean:
	rm -f *.o
	rm -f *.exe
	rm -f chc_verifier
