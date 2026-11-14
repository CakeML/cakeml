Native builds of the standalone Pancake compiler for x64, ARM8 and RISC-V64.

The archives `pancake-x64.tar.gz`, `pancake-arm8.tar.gz` and
`pancake-riscv.tar.gz` contain the assembly, FFI source, Makefile and README
needed to build each executable independently of the CakeML checkout.

For example, on x64 Linux:

```
tar -xzf pancake-x64.tar.gz
cd pancake-x64
make pancake
```

Use the corresponding archive on ARM8 or RISC-V64 Linux. A C compiler and
make are required; `CC` can be set to a cross compiler.

To generate an archive from a CakeML checkout, run `Holmake pancake-x64.tar.gz`
in `x64/`, or the corresponding target in `arm8/` or `riscv/`.

The compiler reads Pancake source from standard input and writes assembly
to standard output:

```
./pancake < input.pnk > output.S
```

Use `--help` to see the options. The default target is the native
architecture; `--target=T` selects any of the supported compiler targets.
