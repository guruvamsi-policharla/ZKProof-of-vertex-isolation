# ZKProof-of-vertex-isolation
Work done at Hiroshima University in collaboration with Prof. Toru Nakanishi and Yoshino Hiromi. An implementation of a Zero Knowledge proof of vertex isolation using accumulators and a few bilinear pairing operations.

Download the forked version of the pbcwrapper from this repo: https://github.com/guruvamsi-policharla/pbcwrapper
Follow the instructions to build the C++ wrapper for PBC built by Aniket Kate then move libPBC.a to the working directory along with all .h files or provide the path for it when compiling your programs:

Compile with: 

$ g++ -g -o main main.cpp libPBC.a -lpbc -lgmpxx -lgmp

-lpbc to link pbc library
-lgmpxx, -lgmp to link gmp library

Can remove -g if debugging info is not needed.
