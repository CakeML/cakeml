# Pancake Quickstart

This document outlines the quickest path to write, build and run a Pancake "Hello, world" program, including its supporting C file.
This may be used as a starting point for other Pancake programs.

See the [Pancake how-to](/pancake/how-to.md) for a more detailed guide on how to use Pancake.

## File setup

### Pancake file

Create a file named `hello.pnk` with the following contents:
```c
fun 1 main() {
    // Pointer to store "Hello, world!\n"
    var 1 msg_ptr = @base;

    // Store each character
    st8 msg_ptr, 72;        // 'H'
    st8 msg_ptr + 1, 101;   // 'e'
    st8 msg_ptr + 2, 108;   // 'l'
    st8 msg_ptr + 3, 108;   // 'l'
    st8 msg_ptr + 4, 111;   // 'o'
    st8 msg_ptr + 5, 44;    // ','
    st8 msg_ptr + 6, 32;    // ' '
    st8 msg_ptr + 7, 119;   // 'W'
    st8 msg_ptr + 8, 111;   // 'o'
    st8 msg_ptr + 9, 114;   // 'r'
    st8 msg_ptr + 10, 108;  // 'l'
    st8 msg_ptr + 11, 100;  // 'd'
    st8 msg_ptr + 12, 33;   // '!'
    st8 msg_ptr + 13, 10;   // '\n'

    // Ask C to print each character
    @print_chars(msg_ptr, 14, 0, 0);

    return 1;
}
```

Pancake does not have a notion of characters, strings or printing.
Instead, this program uses FFI calls to print using C code.

### C file

Obtain the compiler's [accompanying C file](/basis/basis_ffi.c), named `basis_ffi.c`.

Add the following definition for our program to use:
```c
void ffiprint_chars (unsigned char *c, long clen, unsigned char *a, long alen)
{
    for (long i = 0; i < clen; i++) {
        putchar(c[i]);
    }
}
```

The call to `cml_main` in the C main function is what runs the Pancake code.

## Compiling

### Pancake

Obtain the CakeML compiler binary, which is also used by Pancake.
Download the compiler according to [CakeML how-to](/how-to.md).
Build the compiler by running `make` to obtain a `cake` binary.

Compile the Pancake file with the following command:
```sh
$ cake --pancake < hello.pnk > hello.S
```

You will need to provide the `--target=[<target>]` option if not using an x86-64 architecture.
Reference `cake --help` if needed.

If you do not capitalise the `.S` extension, the next step may fail.

### Program binary

Link and compile the overall binary with the following command:
```sh
$ gcc hello.S basis_ffi.c -o hello
```

Substitute your C compiler as required.

If using `qemu`, the `-static` and `-Wno-format` options are recommended.
If compiling to MIPS64, the `-fPIC` option may be required.

## Running

Your program should now be runnable:
```
$ ./empty
Hello, world!
```

Modify the command to use the appropriate `qemu` version if required.

## Makefile

If referencing the CakeML compiler's `Makefile`, the `-DEVAL` option is not necessary for Pancake and may not work on some architectures.

A general Makefile for Pancake programs is in progress.

## Customising the files

### Pancake file

See the [Pancake syntax reference](/pancake/syntax.md) for a summary of Pancake syntax.

The file MUST have at least one top-level declaration.
A default `main` function that does nothing will be added if one is not provided.

If using the multiple entry points function, include the `--main_return=true` option during compilation to prevent the program from exiting after `cml_main`.

### C file

Please avoid the filename `basis_ffi.c`, as this only makes sense for CakeML programs.

The compiler output expects the following to exist within the C file:
- `extern` declarations:
  - `void cml_main(void)`
  - `void* cml_heap`
  - `void* cml_stack`
  - `void* cml_stackend`
- `cml_*` functions (copying the definitions in `basis_ffi.c` should be sufficient in most cases):
  - `cml_exit(int arg)`
  - `cml_err(int arg)`
  - `cml_clear()`
- memory allocation for stack and heap, with pointers in the matching `extern` variables. See `basis_ffi.c` implementation for size constrains
- a call to `cml_main()`

C file requirements outside of this will depend on what your file needs.

For new FFI function definitions, reference the existing definition signatures and naming.

For exported function declarations (multiple entry points feature), declare with `extern` like `cml_main` and call similarly.
Unlike `cml_main`, these functions can have up to 4 arguments and a return value, all single words.
Ensure `cml_main` is called before any exported functions, and exported functions are not called within FFI calls.

The `-lm` flag can be removed during compilation if you remove the `math.h` usages in the C file.
Add other options as required.

