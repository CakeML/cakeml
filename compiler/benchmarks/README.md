Two benchmark suites for the CakeML compiler.

Requirements
---
To run all the benchmarks, you will need the following compilers.
If you do not want to install all these compilers, you can modify the
default benchmarking scripts to remove them.

1) A bootstrapped copy of the CakeML compiler.

   This can be built yourself, or by downloading a pre-built copy from:
   https://cakeml.org/download.html

   Extract a copy of cake.S and basis_ffi.c to:
   cakeml_benchmarks/cakeml
   mlton_benchmarks/cakeml

2) OCaml (tested: 4.02.3)
3) Poly/ML + a copy with --enable-intinf-as-int (tested: v5.7)
4) MLton (tested: 20171211)
5) SML/NJ (tested: v110.78)
6) Moscow ML (tested: version 2.10)

For running the benchmarks and plotting, we use:
7) Python with numpy (and matplotlib for mlton_benchmarks)
8) For cakeml_benchmarks, we also need gnuplot

cakeml_benchmarks
---
The cakeml_benchmarks/ folder consists of a set of micro-benchmarks written in
CakeML, SML and OCaml.

To run these benchmarks, enter the cakeml_benchmarks directory and run:
./run_all.sh

By default, this produces a single plot (benchmarks2.eps)
comparing OCaml, SML/NJ, MLton and Poly/ML

mlton_benchmarks
---
The mlton_benchmarks/ folder consists of a set of benchmarks taken from the
MLton benchmark suite.

To run these benchmarks, first compile them for CakeML:

cd cakeml
./make_all.sh
cd ..

Next, compile them for the other MLs:

cd sml
make
cd ..

Now, update benchmark.py with the appropriate paths to the ML compilers, then:

python benchmark.py

By default, this produces two plots comparing CakeML against SML/NJ, Poly/ML,
MLton, and Moscow ML. It also produces a plot comparing CakeML at different
optimisation levels

The Makefile can also be configured to:
1) Run and time the GC
   To compile these, uncomment the GC-related lines in cakeml/make_all.sh

2) Compile to different targets
   To compile these, uncomment the related lines in cakeml/make_all.sh
   For arm6 support, you will need the 32-bit version of the bootstrapped compiler.
   (renamed to cake32.S)
