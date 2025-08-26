Contains programs to test the verified Dafny compiler.

## Instructions
Running the examples consists of multiple parts:
- the CakeML binary, found [here](https://github.com/CakeML/cakeml/releases)
- a Dafny fork that generates the S-expressions, found [here](https://github.com/dnezam/dafny/tree/feat-sexp)
- the HOL repository, found [here](https://github.com/HOL-Theorem-Prover/HOL/tree/master)
- the CakeML repository (this is where you currently are)

### CakeML binary
Note that printing is done via calls through the empty FFI, which requires changes to `basis_ffi.c`.
The easiest way to achieve this is by simply replacing the definition of `ffi` with:
```c
/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
    for (long i = 0; i < clen; i++) {
        putc(c[i], stdout);
    }
}
```

### Dafny
You can build the fork linked above by following the [official instructions for building Dafny](https://github.com/dafny-lang/dafny/wiki/INSTALL#building-and-developing-from-source-code).

Assuming you cloned the repo in your home directory, you can turn a Dafny file into an S-expression using the `bake` command:
```sh
~/dafny/Scripts/dafny bake foo.sexp foo.dfy
```

### HOL
Follow the [instructions on the official website](https://hol-theorem-prover.org/#get).
**Make sure to checkout master before building.**

### CakeML repository
Once you have done the previous steps, you can run the tests by executing
```sh
./run_tests.sh ~/dafny/Scripts/dafny ~/cake-x64-64/ ~/HOL/bin/Holmake
```
from this directory.

