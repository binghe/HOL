CC=gcc
CFLAGS= -O2 -g -std=c99 -Wno-nullability-completeness
DEST = ../../bin
PROG = lrat-check

all: $(DEST)/$(PROG)

$(DEST)/$(PROG): lrat-check.c
	$(CC) lrat-check.c $(CFLAGS) -o $(PROG)
	mv $(PROG) $(DEST)

clean:
	rm -rf *~ *.dSYM
	rm -f $(DEST)/$(PROG)
