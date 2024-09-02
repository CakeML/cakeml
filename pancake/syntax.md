# Pancake Syntax Reference

See the [Pancake how-to](/pancake/how-to.md) for a guide on how to use Pancake.

## Structures

| Feature | Syntax | Notes |
| --- | --- | --- |
| Function declaration | `fun FNAME ( ARGS ) { BODY }` | `ARGS` may be empty; each argument must have both shape and identifier, eg `1 x, {1,2} y`. `BODY` must include a function return in all execution branches. Optionally, add `export` keyword before `fun` for multiple entry points feature |
| Block scope | `{ BODY };` | Must have semicolon after right brace. For "empty" `BODY`, use `skip;` |
| Conditional statement | `if CONDITION { BODY } else { BODY }` | `else` and second body optional. For "empty" `BODY`, use `skip;` |
| Loop | `while CONDITION { BODY }` | For "empty" `BODY`, use `skip;` |

## Statements

| Feature | Syntax | Notes |
| --- | --- | --- |
| Variable declaration | `var VNAME = EXP;`, `var SHAPE VNAME = FUNC(ARGS);` | Note that declaration via function call needs shape annotation. `FUNC` can be an expression <!-- !TODO: remove former note after shape annotations added --> |
| Assignment | `VNAME = EXP;`, `VNAM = FUNC(ARGS);` | Variable assignment only; no struct field assignment yet. `FUNC` can be an expression |
| Memory store | `st ADDR, VAR;`, `st8 ADDR, VAR;` |  |
| Shared memory store | `!stw ADDR, VAR;`, `!st8 ADDR, VAR;`, `!st32 ADDR, VAR;` | |
| Shared memory load | `!ldw VAR, ADDR;`, `!ld8 VAR, ADDR;`, `!ld32 VAR, ADDR;` | Note that shared memory loads are statements, unlike local loads |
| Stand-alone function call | `FUNC(ARGS);` | `FUNC` can be an expression |
| Function return | `return EXP;`, `return FUNC(ARGS);` | `FUNC` can be an expression |

## Operators

| Feature | Syntax | Notes |
| --- | --- | --- |
| Arithmetic | `+`, `-`, `*` | Addition, subtraction, multiplication. No division |
| Bitwise | `&`, `\|`, `^`, `<<`, `>>>`, `>>`, `#>>` | And, or, xor, logical left shift, logical right shift, arithmetic right shift, circular right shift |
| Logical | `!`, `&&`, `\|\|` | Not, and, or |
| Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=`, `<+`, `>+`, `<=+`, `>=+`| Equal, not equal, less than, greater than, less or equal, greater or equal, signed less than, signed greater than, signed less or equal, signed greater or equal |
| Pointer | `&`, `*` | Get function pointer, dereference function pointer |
| Memory load | `lds SHAPE ADDR`, `ld8 ADDR` | Note that local memory loads are expressions, unlike shared loads. For loading a single word, use `lds 1 ADDR` |

## Shapes and Structs

| Feature | Syntax | Notes |
| --- | --- | --- |
| Word shape | `1` | `1` and `{1}` are distinct |
| Repeated shape | `N` | Equivalent to struct of N words, ie. `{1,1,...,1}` where 1 appears N times |
| Struct shape | eg. `{1,2,{1}}`| `1` and `{1}` are distinct |
| Struct value | eg. `<1,<2,3>,<4>>` | |
| Struct field access | `STRUCT.INDEX` | 0-indexed. `STRUCT` can be an expression |

## Specials

| Feature | Syntax | Notes |
| --- | --- | --- |
| Base pointer | `@base` | Points to the base of the heap |
| Bytes in word | `@biw` | Number of bytes in a word; 8 for 64bit targets, 4 for 32bit targets |
| Single line comments | `// COMMENT` | |
| Block comments | `/* COMMENT */` | Non-recursive |
| Annotation comments | `/*@ COMMENT @*/` | For adding tool-specific annotations in the underlying code representation; the same as block comments otherwise. Non-recursive |
| Booleans | `true`/`false`| Equivalent to `1`/`0`, respectively |