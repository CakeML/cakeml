# Pancake Syntax Reference

See the [Pancake how-to](/pancake/how-to.md) for a guide on how to use Pancake.

## Top-Level Declarations

| Feature | Syntax | Notes |
| --- | --- | --- |
| Function declaration | `MODIFIERS fun RETSHAPE FNAME ( ARGS ) { BODY }` | `MODIFIERS` and/or `ARGS` may be empty. See [Function modifiers](#function-modifiers) for possible modifiers. Each argument expects both a shape and an identifier, and are comma separated, eg `1 x, {1,2} y`. `BODY` must include a function return in all execution branches. All functions are callable (ie. in scope) from all function bodies |
| Global variable declaration | `var SHAPE VNAME = EXP;` | Globals cannot be initialised with a function call. Globals are in scope for all function bodies and for any globals declared after them. Beware of shadowing |
| Named struct declaration | `struct SNAME { FIELDS }` | `FIELDS` may NOT be empty. Each field expects both a shape and an identifier, and are comma separated, eg `1 x, {1,2} y`. Named structs are in scope for all functions and globals, and for any named structs declared after them |

## Function modifiers

| Feature | Syntax | Notes |
| --- | --- | --- |
| Inline function | `inline fun RETSHAPE FNAME ( ARGS ) { BODY }` | Enables function inlining. Has no effect on functions with recursion or returns within loops |
| Exported function | `export fun RETSHAPE FNAME ( ARGS ) { BODY }` | Enables multiple entry points feature. Must use 4 arguments or less. Must not use non-`1` shapes for arguments or return value |
| Multiple modifiers | eg. `inline export fun ...` | `inline` and `export` modifiers may be combined, in that order |

## Structures

| Feature | Syntax | Notes |
| --- | --- | --- |
| Block scope | `{ BODY };` | Must have semicolon after right brace. `BODY` may be empty |
| Conditional statement | `if CONDITION { BODY } else { BODY }` | `else` and second body optional. `CONDITION` need not be enclosed in brackets, is considered false if equal to 0 and true otherwise. `BODY` may be empty. `else if` is NOT supported syntax, and such behaviour can be achieved through nesting |
| Loop | `while CONDITION { BODY }` | `CONDITION` need not be enclosed in brackets, is considered false if equal to 0 and true otherwise. `BODY` may be empty |

## Statements

| Feature | Syntax | Notes |
| --- | --- | --- |
| Local variable declaration | `var SHAPE VNAME = EXP;`, `var SHAPE VNAME = FNAME(ARGS);` | Beware of shadowing |
| Assignment | `VNAME = EXP;`, `VNAME = FNAME(ARGS);` | Variable assignment only; no struct field assignment yet |
| Stand-alone function call | `FNAME(ARGS);` | |
| Function return | `return EXP;`, `return FNAME(ARGS);` | |
| FFI function call | `@FNAME(PTR1, LEN1, PTR2, LEN2);` | `PTR1` should be the array of function inputs and `LEN1` its length; `PTR2` and `LEN2` are similarly for function outputs. Should be declared as `ffiFNAME` in C file |
| Memory store | `st ADDR, VAR;`, `st8 ADDR, VAR;`, `st32 ADDR, VAR;` | |
| Shared memory store | `!stw ADDR, VAR;`, `!st8 ADDR, VAR;`, `!st32 ADDR, VAR;` | |
| Shared memory load | `!ldw VAR, ADDR;`, `!ld8 VAR, ADDR;`, `!ld32 VAR, ADDR;` | Note that shared memory loads are statements, unlike local loads |

## Operators

| Feature | Syntax | Notes |
| --- | --- | --- |
| Arithmetic | `+`, `-`, `*` | Addition, subtraction, multiplication. No division |
| Bitwise | `&`, `\|`, `^`, `<<`, `>>>`, `>>`, `#>>` | And, or, xor, logical left shift, logical right shift, arithmetic right shift, circular right shift |
| Logical | `!`, `&&`, `\|\|` | Not, and, or |
| Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=`, `<+`, `>+`, `<=+`, `>=+`| Equal, not equal, less than, greater than, less or equal, greater or equal, signed less than, signed greater than, signed less or equal, signed greater or equal |
| Memory load | `lds SHAPE ADDR`, `ld8 ADDR`, `ld32 ADDR` | Note that local memory loads are expressions, unlike shared loads. For loading a single word, use `lds 1 ADDR` — default shape is NOT supported for local loads |

## Shapes and Structs

| Feature | Syntax | Notes |
| --- | --- | --- |
| Word shape | `1` | `1` and `{1}` are distinct |
| Unnamed struct shape | eg. `{1,2,{1}}`| Tuple-like. Can be nested with either struct option. `1` and `{1}` are distinct |
| Named struct shape | eg. `my_struct`| C-like structs. Can be nested with either struct option. `{1}` and `my_struct { 1 x }` are distinct |
| Repeated shape | `N` | Equivalent to an unnamed struct of N words, ie. `{1,1,...,1}` where 1 appears N times |
| Default shape | eg. `var x = 1;` | Any omitted shape before an identifier where it is expected will be assumed to use the default of `1`. This is NOT inference |
| Unnamed struct value | eg. `< 1, <2, 3>, <4> >` | Can be nested with either struct option, but all angle brackets must be separated by (at least) whitespace to parse, eg. after `4` in the example |
| Named struct value | eg. `my_struct < x = 1, y = <2, 3>, z = <4> >` | Explicit struct and field names are required. Can be nested with either struct option, but all angle brackets must be separated by (at least) whitespace to parse, eg. after `4` in the example |
| Unnamed struct field access | `STRUCT.INDEX` | 0-indexed. `STRUCT` can be an expression. `INDEX` must be a (non-negative) number. Can be nested with either struct option |
| Named struct field access | `STRUCT.FIELDNAME` | `STRUCT` can be an expression. Can be nested with either struct option |

## Specials

| Feature | Syntax | Notes |
| --- | --- | --- |
| Base pointer | `@base` | Points to the base of the user memory |
| Top pointer | `@top` | Points to the top of the user memory |
| Bytes in word | `@biw` | Number of bytes in a word; 8 for 64bit targets, 4 for 32bit targets |
| Single line comments | `// COMMENT` | |
| Block comments | `/* COMMENT */` | Non-recursive |
| Annotation comments | `/@ COMMENT @/` | Non-recursive. For adding tool-specific annotations in the underlying code representation; the same as block comments otherwise. Will not be ignored by CPP |
| Booleans | `true`/`false` | Equivalent to `1`/`0`, respectively |