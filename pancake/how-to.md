Pancake How To
=============

Pancake is a programming language for low-level imperative programming, with a verified compiler built on CakeML backend. This document is meant as:

- an introduction to Pancake programming, 
- a description of how to use the Pancake compiler, and,
- a description of some of its current limitations and pitfalls.

Note that Pancake is still in development, and thus everything in this document is subject to change.

Running the compiler
---------------------------

To compile Pancake programs, you use the same compiler binary as CakeML does. To download and build the compiler, follow the instructions in the [CakeML how-to](/how-to.md) until you obtain a `cake` binary.

Now let's run the compiler. Suppose you have a file called `test.🥞`
which contains the simplest valid Pancake program:

    fun main() {
      return 0;
    }

To invoke the Pancake compiler on this program, run the following (assuming `cake` is in your `$PATH`; if not use relative paths):

    $ cake --pancake < test.🥞 > test.S

The `--pancake` compiler flag indicates that we want to compile Pancake code; by default, `cake` assumes you want to compile CakeML, regardless of file extension). The compiler accepts Pancake source code on `stdin`, and outputs the compiled assembly template to `stdout`. We pipe these to and from the desired files.

TODO: explain how to run the `.S` file.

TODO
----------

TODO: more stuff :)
