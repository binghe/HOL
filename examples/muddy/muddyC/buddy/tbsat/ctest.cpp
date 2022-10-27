#include <iostream>
#include "clause.h"

// Simple test of clause reading and writing

int main(int argc, char *argv[]) {
  FILE *infile = stdin;
  if (argc >= 2) {
    if (strcmp(argv[1], "-h") == 0) {
      std::cerr << "Usage: " << argv[0] << " [[infile.cnf] [outfile.cnf]]" << std::endl;
      exit(1);
    }
    infile = fopen(argv[1], "r");
    if (infile == NULL) {
      std::cerr << "Couldn't open file " << argv[1] << std::endl;
      exit(1);
    }
  }
  CNF cset = CNF(infile);
  if (cset.failed()) {
    std::cout << "Aborted" << std::endl;
    exit(1);
  }
  if (argc >= 3) {
    std::ofstream outstream;
    outstream.open(argv[2]);
    cset.show(outstream);
  } else 
    cset.show();
}
