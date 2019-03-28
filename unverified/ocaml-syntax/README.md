An OCaml to CakeML translator. Attempts to translate type-correct OCaml files
to equivalent CakeML files. Multi-file programs should be supported eventually,
but are not currently.

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

The output `.cml` files can be patched after translation. File `a.cml` is fed to `a-patch`. See `boyer-patch` (which uses `boyer-patch.sed`) for an example. Current patches:
* boyer – avoid falling to the value restriction. The OCaml file has type annotations (e.g `ref ([] : head list)`), which can't be used in CakeML.

countGraphs currently fails due to trying to match against the pattern `Ok (newPacc, acc)`, where `Ok` is a unary constructor and `(newPacc, acc)` is supposed to be a tuple pattern. This is a known issue with CakeML, so fixing this doesn't seem necessary. boyer currently fails because I've botched the translation from SML (or maybe I've hit a problem with OCaml equality between references).
