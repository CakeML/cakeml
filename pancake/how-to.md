# Pancake How-To

Pancake is a programming language for low-level imperative programming, with a verified compiler built on CakeML backend. This document is meant as:

- an introduction to Pancake programming, 
- a description of how to use the Pancake compiler, and,
- a description of some of its current limitations and pitfalls.

Note that Pancake is still in development, and thus everything in this document is subject to change.

## Using the compiler

### Obtaining the compiler

To compile Pancake programs, you use the same compiler binary as CakeML does. To download the compiler, follow the instructions in the [CakeML how-to](/how-to.md). To build it, run `make` to obtain a `cake` binary.

### Running the compiler

Now let's run the compiler. Suppose you have a file called `test.🥞`
which contains the simplest valid Pancake program:

    fun main() {
      return 0;
    }

To invoke the Pancake compiler on this program, run the following (assuming `cake` is in your `$PATH`; if not use relative paths):

    $ cake --pancake < test.🥞 > test.S

The `--pancake` compiler flag indicates that we want to compile Pancake code; by default, `cake` assumes you want to compile CakeML, regardless of file extension). The compiler accepts Pancake source code on `stdin`, and outputs the compiled assembly template to `stdout`. We pipe these to and from the desired files.

### Running the compiler output

TODO: linking and running `.S` file, including sample minimum c file

## Writing the Pancake file

### Shapes?

TODO: existing shape stuff, maybe the shape annotation stuff later?

### Heap usage

TODO: @base, local vs shared mem, etc + bitmap store issue

### Syntax

TODO: key structures and quirks, link to separate syntax ref sheet

## Using the C file

### C file requirements

TODO: memory alloc, cml_exit, etc

### Calling C from Pancake code

TODO: putchar example or something

### Calling Pancake from C code

TODO: mep example + argument number limit

## Limitations

TODO: where does single file compilation go? is "known issues" better as "unintentional limitations"?

### Intentional limitations

TODO: globals, dynamic alloc

### Known issues

TODO: empty loops, bitmap store, 

### Planned features

TODO: shape annotations, continuations?

## Bonus content

### The C preprocessor and Pancake

TODO: you can use it

### Compiler output details

TODO: cml_main and friends

# (other tasks)

TODO: separate syntax ref sheet  
TODO: example programs