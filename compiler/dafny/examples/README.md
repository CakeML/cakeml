Contains programs to test the Dafny compiler.

Note that printing is done via calls through the empty FFI.
This requires changes to `basis_ffi.c`.
The easiest way to achieve this is by simply replacing the definition of `ffi` with:
```c
/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
    for (long i = 0; i < clen; i++) {
        putc(c[i], stdout);
    }
}
```

