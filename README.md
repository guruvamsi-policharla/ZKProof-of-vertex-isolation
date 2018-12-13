# ZKProof-of-vertex-isolation
Work done at Hiroshima University in collaboration with Prof. Toru Nakanishi and Yoshino Hiromi. An implementation of a Zero Knowledge proof of vertex isolation using accumulators and a few bilinear pairing operations.

Use: $ gcc -o foo foo.c -I ~/.local/include/pbc -L ~/.local/lib -Wl,-rpath ~/.local/lib  -l pbc -l gmp -lm

If using the C++ wrapper by Aniket Kate use:

$ g++ -g -o main main.cpp libPBC.a -lpbc -lgmpxx -lgmp
