# Pancake Syntax Reference

See the [Pancake how-to](/pancake/how-to.md) for a guide on how to use Pancake.

## Structures

| Feature | Syntax | Notes |
| --- | --- | --- |
| Function declaration | `fun FNAME ( ARGS ) { BODY }` | Must include a return statement. Optionally, add `export` keyword before `fun` for multiple entry points feature |
| Block scope | `{ BODY }` | |
| Conditional statement | `if CONDITION { BODY } else { BODY }` | `else` and second body optional. For an empty body, use `skip;` |
| Loop | `while CONDITION { BODY }` | For an empty body, use `skip;` |

## Statements

| Feature | Syntax | Notes |
| --- | --- | --- |
| Variable creation | `var NAME = EXP;` | |
| Assignment | `NAME = EXP;` | No struct field assignment yet |
| Memory store | `st ADDR, VAR`, `st8 ADDR, VAR;` | <!--!TODO: Hey should we rename stw to sts?--> |
| Shared memory store | `!stw VAR, ADDR`, `!st8 VAR, ADDR;`, `!st32 VAR, ADDR;` | |
| Shared memory load | `!ldw VAR, ADDR`, `!ld8 VAR, ADDR;`, `!ld32 VAR, ADDR;` | |
| Function calls | `var SHAPE VAR = FUNC(ARGS);`, `FUNC(ARGS);`, `VAR = FUNC(ARGS);`, `return FUNC(ARGS);` | Declaring call, stand-alone call, assigning call, tail call. Function can be identifier or dereferenced function pointer. Calls can NOT be used as expressions |
| Return | `return EXP;` | |

## Operators

| Feature | Syntax | Notes |
| --- | --- | --- |
| Arithmetic | `+`, `-`, `*` | Addition, subtraction, multiplication. No division |
| Bitwise | `&`, `\|`, `^`, `<<`, `>>>`, `>>`, `#>>` | And, or, xor, logical left shift, logical right shift, arithmetic right shift, circular right shift <!--!TODO: Confirm these--> |
| Logical | `!`, `&&`, `\|\|` | Not, and, or |
| Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=`, `<+`, `>+`, `<=+`, `>=+`| Equal, not equal, less than, greater than, less or equal, greater or equal, signed less than, signed greater than, signed less or equal, signed greater or equal |
| Pointer | `&`, `*` | Get function pointer, dereference function pointer |
| Memory load | `lds SHAPE ADDR`,`ld8 ADDR` | |

## Shapes and Structs

| Feature | Syntax | Notes |
| --- | --- | --- |
| Word shape | `1` | `1` and `{1}` are distinct |
| Repeated shape | `N` | Equivalent to struct of N words, ie. {1,1,...,1} where 1 appears N times |
| Struct shape | eg. `{1,2,{1}}`| `1` and `{1}` are distinct |
| Struct value | eg. `<1,<2,3>,<4>>` | |
| Struct field access | `STRUCT.INDEX` | 0-indexed. Struct can be a literal or a variable |

## Specials

| Feature | Syntax | Notes |
| --- | --- | --- |
| Base pointer | `@base` | Points to the base of the heap |
| Bytes in word | `@biw` | Number of bytes in a word; 8 for 64bit targets, 4 for 32bit targets |
| Single line comments | `// COMMENT` | |
| Block comments | `/* COMMENT */` | Non-recursive |
| Annotation comments | `/*@ COMMENT @*/` | <!--!TODO: Explain what theyre used for--> |
| Booleans | `true`/`false`| Equivalent to `1`/`0`, respectively |