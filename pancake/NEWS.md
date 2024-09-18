Pancake changelog
======================================

User-facing changes to the Pancake language and compiler are
documented here when they are merged into `master`.

September 15th 2024
-------------------

A parser bug that caused struct field accesses to be ordered
incorrectly is now fixed. That is, the value of the expression

    <<1,2>,<3,4>>.0.1

is now `2`, whereas previously it was `3`.

August 29th 2024
-------------------

`st` has replaced the former `stw` operator for storing shapes. As the
new name indicates, this operator can store not just words but
arbitrary shapes.

The precedence of load expressions (`lds` and `ld8`) has also been
changed to be between that of comparisons and bitwise operators.

August 26th 2024
-------------------

A new keyword, `@biw` (bytes in word), has been added. `@biw` is a
constant expression whose value is `8` on 64-bit architectures and `4`
on 32-bit architectures. Its purpose is to make portable code easier
to write.

August 25th 2024
-------------------

### 32-bit shared memory loads and stores ###

32-bit shared memory loads and stores have now been added. These are
primarily intended for reading and writing to device registers for 32-bit
devices. The syntax is as follows:

    !st32 1000, v; // store 32 bits from variable v (12) to shared memory address 1000
    !ld32 v, 1000 + 12; // load 32 bits from shared memory address 1012 to v

### Annotation comments ###

The parser now supports a special comment format called *annotations*,
which are any comments of the form `/*@ ... @*/`.  These are retained
by the parser in the form of `Annot` nodes and are made visible in
explorer output; they can be used to convey information to tools that
consume Pancake abstract syntax produced by the explorer.

Location information is also retained in the AST in the form of
such `Annot` nodes.

August 24th 2024
-------------------

The compiler flag `--main_return=true` now passes the return value
from the Pancake main function to the caller via `cml_main`.


July 29th 2024
-------------------

The precedence of bitwise operators (`&`, `^` and `|`) is now higher
than comparison operators. For example, `1 & 2 != 0` will now parse as
`(1 & 2) != 0` instead of `1 & (2 != 0)`.

July 28th 2024
-------------------

The compiler now supports the `--explore` command line parameter when
compiling Pancake programs. It can be used to output the various
intermediate representations produced during compilation as text.

July 1st 2024
-------------------

Pancake now supports multiple entry points, to simplify interaction
between Pancake and other languages (usually C).  Functions that
should be callable from outside Pancake should be prefixed with the
`export` keyword, as follows:

    export fun my_function(<args>) {
      <body>
    }

Exported functions can take at most four arguments, and the arguments
must have shape `1`. Calling any exported function before the initial
call to `cml_main()` results in a runtime error. `main` cannot be
explicitly exported.

The Pancake `main` function (that gets invoked via `cml_main`) is
now taken to be the function named `main` if one exists; previously,
the first function was taken to be the `main` function regardless of
name. If no function named `main` exists, a default `main` function is
used:

    fun main() { return 1; }

The new compiler flag `main_return` can be used to return control to
the caller, instead of exiting, after the main function has finished
executing. By default, this flag is set to `false`.

June 26th 2024
-------------------

Signed word comparison operators `<+`, `<=+`, `>=+` and `>+` have been added.

June 9th 2024
-------------------

The operators `&&` (logical AND) and `||` (logical OR) have been added.

June 5th 2024
-------------------

### Negation syntax ###

`!` in expressions now denotes boolean negation. `!` was previously
used for obtaining the address of a function; `&` now serves this
role instead.

### Shared memory syntax ###

The argument order of shared memory stores has been changed so that it
agrees with local memory stores. For example, instead of
`!st8 <payload>, <address>` the order is now `!st8 <address>, <payload>`.

The first argument to a shared memory store can now be an arbitrary
expression; previously, it had to be a variable.

May 19th 2024
-------------------

Function calls now have different syntax. Previously, two kinds of
function calls were allowed:

     fun f() {
       var x = 5;
       g(); // tail call, causes f() to return
       x = g(); // assigning call (formerly and confusingly known as "returning call")
       return 0;
     }

In the new style, we allow four forms of function calls:

    fun f() {
      var 1 x = g(); // declaring call
      g(); // stand-alone call, does not cause f() to return
      x = g(); // assigning call
      return g(); // tail call, causes f() to return
    }

Declaring calls need a shape annotation on the variable, because in
general the shape of the return value is not statically known.

May 8th 2024
-------------------

Line number reporting in error messages now accounts for comments
correctly.

April 12th 2024
-------------------

Rudimentary line number reporting has been added to parse errors.

March 24th 2024
-------------------

The Pancake compiler now checks that all variable and function names
used in a program are declared and scoped correctly, and reports a
compiler error otherwise. Previously, the compiler would happily
generate nonsense.

March 23rd 2024
-------------------

Shared memory load and store operators have been added to
Pancake. These are intended for reading and writing to memory outside
the local Pancake heap, such as shared memory pages or device
registers.  Unlike local memory accesses, these cannot be optimised
away or reordered by the compiler, similarly to `volatile` in C.

The keywords for local loads and stores have been changed: `st8`, `stw`,
`ld8` instead of `strb`, `str`, and `ldb`.

Shared memory operations are prefixed with `!`, so `!st8` stores a
byte to shared memory and `!ldw` stores a word to shared memory. Note
that shared memory loads are statements, whereas local memory loads
are expressions; this is to retain the side-effect freedom of
expressions.

Foreign function names are now written `@name` instead of `#name`.

August 27th 2023
-------------------

Not-equals is now `!=` instead of `<>`, and function calls can now be
written simply `f(<args>)` instead of `!f(<args>)`.

June 3rd 2023
-------------------

Three new syntax elements have been added to Pancake: infix `*` for
unsigned word multiplication, and `true` and `false` as keywords
denoting `1` and `0`, respectively.

May 29th 2023
-------------------

Syntax for function declarations has now been added. Previously, only
statements was implemented.

March 20th 2023
-------------------

Support for compiling Pancake source programs has been added to the
CakeML compiler binary. Use the compiler flag `--pancake` to indicate
that the source is a Pancake program.

Only statement parsing is implemented currently; the expected input is
a semicolon-separated list of statements, which is interpreted as the
body of the `main` function.
