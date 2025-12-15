(*
  Temporary file for extra AST definition
*)
Theory ast_temp
Ancestors
  integer[qualified] words[qualified] string[qualified] namespace
  location[qualified]

Datatype:
  arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
End
