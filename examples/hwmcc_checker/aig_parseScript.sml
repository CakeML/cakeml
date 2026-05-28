(*
  Parser for the AIGER format.
*)
Theory aig_parse
Ancestors
  mlstring
Libs
  preamble

Definition parse_aig_def:
  parse_aig str = INL «not implemented»
End

val model = mlstringSyntax.mlstring_from_file "./examples/01_model.aig";
val aig = EVAL “parse_aig ^model” |> concl |> rhs;
