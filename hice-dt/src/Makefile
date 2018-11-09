.PHONY: clear

OBJS = boogie_io.o \
       decision_tree.o \
       output_visitor.o \
       pretty_print_visitor.o \
       horn_constraint.o \
       horn_solver.o \
       datapoint.o \
       job.o \
       json_visitor.o

CPPFLAGS += -I ../include
CPPFLAGS += -std=c++14 -Ofast

all: hice-dt

hice-dt: $(OBJS)
	$(CXX) $(CPPFLAGS) $(LDFLAGS) -o hice-dt hice-dt.cpp $(OBJS)
	
%.o: %.cpp
	$(CXX) $(CPPFLAGS) -c $< -o $@
   
clean:
	rm -f *.o
	rm -f *.exe
	rm -f hice-dt
