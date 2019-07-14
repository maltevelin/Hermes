Hermes to C compiler written in [Moscow ML](https://mosml.org/) as part of my bachelor project.
Hermes is designed by Torben Ægidius Mogensen and specified in *Hermes: A
Reversible Language for Writing Encryption Algorithms*.

## Instructions
Clone the repository and build the compiler:
```
git clone git@github.com:maltevelin/Hermes.git
cd Hermes
make
```
Clone and compile the [Blowfish](https://github.com/maltevelin/Blowfish) implementation:
```
git clone git@github.com:maltevelin/Blowfish.git
bin/hc -O Blowfish/blowfish
```
The resulting C file, located in the programs directory, can be compiled using any old C compiler and executed
backwards with the `-r` option. `-O` and `-Z` flags enable optimizations and adds annotations to C code for compilation with [Zerostack](https://github.com/lmrs2/zerostack), respectively.
