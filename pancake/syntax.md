# Pancake Syntax Reference

See the [Pancake how-to](/pancake/how-to.md) for a guide on how to use Pancake.

## Structures

| Feature | Syntax | Notes |
| --- | --- | --- |
| Function declaration | `fun FNAME ( ARGS ) { BODY }` | Optionally, add `export` keyword before `fun` for multiple entry points feature |
| Block scope | `{ BODY }` | |
| Conditional statement | `if CONDITION { BODY } else { BODY }` | `else` and second body optional |
| Loop | `while CONDITION { BODY }` | |

## Statements

| Feature | Syntax | Notes |
| --- | --- | --- |
| Variable creation | `var NAME = EXP;` | |
| Assignment | `NAME = EXP;` | No struct field assignment |
| Memory store | `stw VAR, ADDR`, `st8 VAR, ADDR` | |
| Shared memory store | `!stw VAR, ADDR`, `!st8 VAR, ADDR` | |
| Shared memory load | `!ldw VAR, ADDR`, `!ld8 VAR, ADDR` | |
| Calls (!!) | | |
| Return | | |

## Operators

| Feature | Syntax | Notes |
| --- | --- | --- |
| Arithmetic | `+`, `-`, `*` | |
| Bitwise | `&`, `\|`, `^`, `<<`, `>>>`, `>>`, `#>>` | |
| Logical | `!`, | |
| Comparison | `==`, `!=`, `<`, `>`, `<=`, `>=`, `<+`, `>+`, `<=+`, `>=+`| |
| Pointer | `&`, `*`| |
| Memory load | `lds SHAPE ADDR`,`ld8 ADDR` | |

## Shapes and Structs

| Feature | Syntax | Notes |
| --- | --- | --- |
| Word shape | `1` | |
| Struct shape | `<a,b,<c>>`| |
| Repeated shape | `n` | |
| Struct value | `{1,2,{3}}` | |
| Struct field access | `x.0`, `<1,2>.1` | 0-indexed |

## Specials

| Feature | Syntax | Notes |
| --- | --- | --- |
| Base pointer | `@base` | Points to the base of the heap |
| Single line comments | `// comment content` | |
| Block comments | `/* comment content */` | Non-recursive |
| Booleans | `true`/`false`| Equivalent to `1`/`0`, respectively |