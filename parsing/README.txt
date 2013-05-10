# Notes on Verified Parsing for mini ML.

The ultimate objective is to create functions of the general type

       :token list -> (some_ast_type # token list) option

The main function for user use is likely to be one that targets the type `Elab$ast_prog`.

In any case, the basic approach involves three(!) phases:

1. Use a PEG-based parser to parse the token list. The output type for this phase is a parse-tree that conforms to the context-free grammar specified in `semantics/gramTheory`.

2. Because this "concrete syntax tree" will preserve the original tokens at its leaves, it can then be checked as valid by evaluating (maybe even with `EVAL`) the truth of

           valid_ptree mmlG ptree

3. The parse tree can be converted to a value in the appropriate `ast` type by using one of the functions with a name like `ptree_`*someType*.
For example, `ptree_Expr` takes a parse-tree meant to correspond to an expression and generates an `ast_exp` value (strictly, an option type). The appropriate function for the REPL is ptree_REPLPhrase.

## Verifiability

As already discussed, this is enough to show that we have a "sound" parser because we can check whether or not we have parsed to a tree that really does match up with the original input.
It's not yet clear to me quite what we should say when it comes to the `ptree_Expr` phase of things.

<!-- Local variables: -->
<!-- mode: markdown -->
<!-- flyspell-mode: nil -->
<!-- smart-quotes-mode: nil -->
<!-- end: -->
