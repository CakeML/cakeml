Make sure to have built the Brack binary from the compilation directory.

Because of limited printing functionality, these examples do not print numbers directly,
but instead check that they match the expected result and print the result of the check.

Run `make [name].cake` to compile a file `[name].scm` into an executable.

Note that, to add lists, one should use `(lambda x x)` passed arguments to form a list.

`fib.scm` - classic inefficient recursive Fibonacci implementation (Larceny)
`tailfib.scm` - tail-recursive accumulator Fibonacci implementation (Larceny)
`fibimp.scm` - imperative accumulator Fibonacci implementation using `call/cc` (Brack)

`list.scm` - list operations

`nondet.scm` - example of non-determinism to find solution from lists

`chez.scm` - program with inconsistent behaviour due to underspecification in Chez Scheme.
To run with Chez Scheme, wrap in a `display` call and run `scheme --script` on the source file.
Valid behaviour is to produce the result 4, but Chez Scheme produces 9. In particular, Chez
Scheme produces 9 if the function is present in both branches of the if expression, but
produces the correct 4 if the function is only present in one branch (last commented line).

Letrec reinitialisation is categorised as undefined behaviour, which means that the final
result of the calculation is different depending on how many times a call to that function
exists in the program. If you swap the commenting of the last two lines, Chez Scheme gives
a different result, but Brack gives a consistent one (which also agrees with Chicken and
Racket.)
