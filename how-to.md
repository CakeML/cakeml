CakeML How To
=============

This document introduces how to use the CakeML compiler, providing in
particular:

- a description of how to invoke the CakeML compiler,
- a list of how CakeML differs from SML and OCaml, and,
- a number of small CakeML code examples.

This document is not meant to be an introduction to how to program in
an ML-style language. For such a text, please refer to "ML for the
Working Programmer" by L. C. Paulson, University of Cambridge.

This document is about using the verified CakeML compiler outside of
the logic of a theorem prover. Readers interested in using CakeML to
construct verified programs should [develop their programs inside the
logic of a theorem prover](https://cakeml.org/itp18-short.pdf).

Running the CakeML compiler
---------------------------

The bootstrapped CakeML compiler can be downloaded from the CakeML
website: https://cakeml.org/download.html. Download the `tar.gz` file
which contains among other things:

- `cake.S` — the machine code for the bootstrapped CakeML compiler
- `basis_ffi.c` — C code connecting the CakeML basis library to the OS
- `Makefile` — for convenience of building binaries

Now let's run the compiler. Suppose you have a file called `hello.cml`
which contains:

    print "Hello world!\n";

The simplest way to compile and run this CakeML program, on GNU/Linux and
macOS, is to type `make hello.cake` and then `./hello.cake` on the
command line as follows. On Windows, one types `make hello.cake.exe`.

    $ make hello.cake
    $ ./hello.cake

The last line will print `Hello world!` on standard output.

By looking at what the `make` does, you'll see that on the first run
it builds the CakeML compiler `cake`, then it runs the CakeML compiler
on the input program. The CakeML compiler produces `.S` files that
consist mostly of hex for machine code but also some wrapper code. We
use the system's C compiler to build `basis_ffi.c` and to connect the
CakeML generated machine code with the C code that is accessed through
CakeML's foreign function interface (FFI).

A simple but complete program
-----------------------------

The program above is too simple to be interesting. Below is a slightly
more interesting program: this produces output based on command-line
input, and prints a usage message if invoked incorrectly.

    fun fac n = if n = 0 then 1 else fac (n-1) * n;

    fun main () =
      let
        val arg = List.hd (CommandLine.arguments())
        val n = Option.valOf (Int.fromString arg)
      in
        print_int (fac n) ; print "\n"
      end
      handle _ =>
        TextIO.print_err ("usage: " ^ CommandLine.name() ^ " <n>\n");

    main ();

If the code above is in a file called `fac.cml`, then it can be
compiled and run as follows:

    $ make fac.cake
    $ ./fac.cake
    usage: ./fac.cake <n>
    $ ./fac.cake 5
    120
    $ ./fac.cake 50
    30414093201713378043612608166064768844377641568960512000000000000

The last run illustrates that CakeML's integer type is the unbounded
mathematical integers (arbitrary precision integers).

How CakeML differs from SML and OCaml
-------------------------------------

The CakeML language is heavily based on Standard ML (SML), but CakeML
differs in some aspects and takes inspiration from OCaml and
Haskell. Below is a list of differences between CakeML and SML.

### Syntactic differences

- CakeML has curried Haskell-style constructor syntax (see below)
- constructors in CakeML must begin with an uppercase letter
- constructors must be fully applied
- alpha-numeric variable and function names begin with a lowercase letter
- CakeML lacks SML's records, functors, open and (at present) signatures
- CakeML capitalises `True`, `False` and `Ref`

### Semantic differences

- CakeML has right-to-left evaluation order
- CakeML has no equality types
- the semantics of equality in CakeML differs from those in SML and OCaml
- CakeML does not support let-polymorphism

### Differences in conventions

- CakeML programmers should curry multi-argument functions

### Basis library

The CakeML basis library is still developing and not aligned with SML
or OCaml's standard libraries. To list the contents of the CakeML
basis library, execute the following on the command line:

    $ echo "" | ./cake --types

By invoking the compiler using `./cake --types`, one makes it run type
inference and then print the name and type of every top-level binding.
By supplying the compiler with the empty program, the top-level
bindings are only those from the basis library.

Expressions, literals and comments in CakeML
--------------------------------------------

CakeML expressions are very similar to SML expressions. CakeML has the
same list syntax and same syntax for integers and booleans. Comments
are written inside `(* ... *)` and can be nested. Below are some
examples. Note how `Some` and `None` differ from SML.

    (* boolean literals *)
    True;
    False;
    (2 < 2) orelse (1 <= 1);

    (* some numbers *)
    0;
    1;
    5000;
    ~5000;  (* a negative number *)

    (* some functions *)
    (fn x => x + 5);
    List.length;
    (let
       fun fib n = if n < 2 then n else fib (n-1) + fib (n-2)
     in
       fib
     end);

    (* lists *)
    [];
    [1,2,3,4,5];
    [1,2] @ [3,4,5];
    1 :: 2 :: [3,4,5];

    (* options *)
    None;
    Some 4;

    (* strings *)
    "hi there";
    String.concat ["hi"," ","there"];
    ("hi" ^ " " ^ "there");
    Int.toString 5;

    (* words *)
    Word64.fromInt 5;
    Word64.xorb (Word64.fromInt 2) (Word64.fromInt 3);

    (* vectors *)
    Vector.tabulate 50 (fn n => 2 * n);
    Vector.sub (Vector.fromList [1,2,3]) 2;

    (* exceptions *)
    (print "Hi"; raise Bind; print " there") handle Bind => print " Ho!";

Declarations in CakeML
----------------------

CakeML supports declarations such as `val`, `fun`, `datatype`, `type`,
`exception`, `structure` and `local`.

    structure RoseTree =
      struct
        datatype 'a tree = Branch 'a ('a tree list);
      end;

    exception ErrorMsg string;

    type int_rose = int RoseTree.tree;

    local
      fun fail_with_message msg = raise ErrorMsg msg;
      fun make_tree x n =
        if n < 0 then fail_with_message "negative depth" else
        if n = 0 then RoseTree.Branch x [] else
          let
            val t = make_tree x (n-1)
          in
            RoseTree.Branch x (List.tabulate n (fn x => t))
          end;
    in
      val tree5 = make_tree 5 5;
    end;

Datatypes and pattern matching
------------------------------

CakeML differs from SML in its use of Haskell-inspired datatype and
constructor syntax.

CakeML requires that all constructor names and module names start with
a uppercase letter. All alpha-numeric variable names and function
names must start with a lowercase letter. This rule makes it easy to
see which names are variables and which are constructors in patterns.

Below is an example with a mutually recursive datatype and a function
definition illustrating the `fun ... and ...` syntax for mutually
recursive functions.

    datatype foo = A int | B (bar list)
         and bar = C | D foo bar;

    fun foo_toString x =
          case x of
            A i => "A" ^ Int.toString i
          | B bs => "B" ^ String.concat (List.map bar_toString bs)
    and bar_toString x =
          case x of
            C => "C"
          | D f b => "D" ^ foo_toString f ^ bar_toString b;

    print (foo_toString (B [C, C, D (A 4) C]));

Note that CakeML requires that constructors are fully applied. This
means that `List.map Some xs` is not allowed; instead one can write
`List.map (fn x => Some x) xs`.

Exceptions are defined in a similar style and can be used as normal
constructors in patterns:

    exception ErrorMsgWithLoc string int int;

    (fn e => case e of ErrorMsgWithLoc msg l1 l2 => print msg);

Like SML, anonymous functions `fn` can have a pattern:

    (fn Some x => x);

Pattern matching can be done through references, as the following
example shows. This example uses references to build a circular list.
Note how the pattern treats `Ref` as a constructor.

    datatype 'a clist = Nil | Cons 'a (('a clist) ref);

    (* build a simple list with two elements *)
    val zs = Cons 1 (Ref (Cons 2 (Ref Nil)));

    (* update the end of the list to point at the start of the list *)
    case zs of Cons _ (Ref (Cons _ r)) => (r := zs);

    (* a function that extracts a normal List.list from a clist *)
    fun take n xs =
      case (n,xs) of
        (0, _) => []
      | (_, Nil) => []
      | (_, Cons x (Ref ys)) => x :: take (n-1) ys;

    print_int (List.length (take 10 zs));   (* prints 10 *)

CakeML has a strict call-by-value semantics. However, one can
implement lazy lists in CakeML. Here is a datatype that can be used
for lazy lists and a `take` function:

    datatype 'a llist = Nil | Cons 'a (unit -> 'a llist);

    fun take n xs =
      case (n,xs) of
        (0, _) => []
      | (_, Nil) => []
      | (_, Cons x ys) => x :: take (n-1) (ys());

Evaluation order
----------------

CakeML has a well-defined evaluation order: it is right-to-left. The
evaluation order is visible when the code has side effects. Example:
the following code builds a list using expressions that cause printing
at each content expression.

    [print_int 1, print_int 2, print_int 3];

The example above prints `321`.

We recommend that users use `let`-expressions to force their own
evaluation order. The following prints `123`.

    let
      val u1 = print_int 1
      val u2 = print_int 2
      val u3 = print_int 3
    in
      [u1, u2, u3]
    end;

Stateful features
-----------------

Most CakeML programs ought to keep mostly to the pure functional subset of
CakeML. However, CakeML provides stateful features such as references `Ref`
and arrays `Array.array` that can enhance performance significantly in
certain applications.

The circular list example above already showed the use of `Ref`. The
next example illustrates the use of arrays in a naive sieve-based
primarily test. Here `Array.array` creates an array and we use `;` for
sequencing. The final return value is what is stored in the nth
element of the array, i.e., `Array.sub a n`.

    fun is_prime n =
      if n < 0 then False else
      let
        val a = Array.array (n+1) True
        fun set_steps i k =
          if Array.length a <= i then () else
            (Array.update a i False; set_steps (i+k) k)
        fun set_each i =
          if n <= i then () else
            (set_steps i i; set_each (i+1))
      in
        (set_each 2; Array.sub a n)
      end;

    fun print_is_prime n =
      if is_prime n then print (Int.toString n ^ " is prime.\n")
                    else print (Int.toString n ^ " is not prime.\n");

    print_is_prime 5;
    print_is_prime 700;
    print_is_prime 701;

Semantics of equality
---------------------

Like SML and OCaml, CakeML includes a polymorphic equality test.
However, the semantics of CakeML's polymorphic equality test differs from
those of SML and OCaml. SML uses equality types to ensure that one cannot
test equality of function closures. In contrast, OCaml raises an exception
in case closures are part of the compared values.

In CakeML, we did not want to have equality types, and we do not want
to search for closures in pointer-equal values. For this reason,
CakeML allows comparison of closure values: all closures are equal
under the polymorphic equality test in CakeML.

    fun plus2 n = n + 2;
    fun plus3 n = n + 3;

    (* the following succeeds and prints True *)
    if plus2 = plus3 then print "True\n" else print "False\n";

Arguably, it does not make sense to compare functions. Thus we took
the freedom to pick a semantics that is both well defined and leads to
a good implementation for the common case, i.e., no closures.

Lack of let-polymorphism
------------------------

CakeML does not support let-polymorphism. The following is an example
of a program that type checks in SML, but not in CakeML. It fails to
type check in CakeML because the let-bound `x` must, at its uses, be
instantiated to `int list` and `string list`.

```
let
  val x = []
in
  (1::x, "hi"::x)
end;
```

However, CakeML supports polymorphism and `local` which means that the
following version works:

    local
      val x = []
    in
      val y = (1::x, "hi"::x)
    end;

What next?
----------

The definitive definition of the syntax and semantics of CakeML can be
found at: https://code.cakeml.org/tree/master/semantics

The CakeML team aims to be open and accessible. Feel free to join the
CakeML Slack channel using the invitation link at https://cakeml.org.
Ask questions and contribute to the project or build your own project
based on CakeML.
