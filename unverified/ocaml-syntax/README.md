OCaml to CakeML translator
==========================
Possibly translates type-correct OCaml files to equivalent CakeML files. Multi-file programs should be supported eventually, but aren't now.

Installation
------------
Requires `ocamlfind`:
```sh
make
```

Usage
-----
```sh
./formatted <<< 'Some (OCaml code)'
```
will write the translation of `Some (OCaml code)` to stdout. (`Some (OCaml code)` will fail because `OCaml` and `code` are not defined.)

```sh
./ocaml2cakeml myCode.ml
```
will write the translation of the contents of `myCode.ml` prefixed with the contents of the files in `lib/`. Currently, this gives translated programs access to translations of OCaml's `Pervasives`, `List`, and `Array` modules.

Running tests
-------------
Edit the `CAKE` variable in `tests/Makefile` to reflect the location of your CakeML interpreter. Then run:
```sh
cd tests
make
make test
```

Translation failures are shown in the output of `make`, and begin with “Error:”. Errors from the CakeML interpreter are shown in the output of `make test`, and look like either “<parse error>” or “<type error>”. In the absence of these, “Success” will be printed. The full output of the interpreter is written to the relevant .out files. The binary file produced by `make` is a byproduct of the OCaml compiler.
