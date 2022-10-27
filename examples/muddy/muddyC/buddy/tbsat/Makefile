CC=gcc
CXX=g++
OPT=-O2
#OPT=-O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11
INC=-I../../include
LDIR = ../../lib
TLIB = $(LDIR)/tbuddy.a
DEST = ../../bin
PROG = tbsat

all: $(DEST)/$(PROG)

$(DEST)/$(PROG): clause.cpp clause.h teval.cpp bsat.cpp 
	$(CXX) $(CFLAGS) $(INC) -o $(PROG) clause.cpp teval.cpp bsat.cpp $(TLIB)
	mv $(PROG) $(DEST)

clean:
	rm -f  *~
	rm -rf *.dSYM
	rm -f $(DEST)/$(PROG)


