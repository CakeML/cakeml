open intLib;
open mmlParseTheory lexer_implTheory Print_astTheory ElabTheory;
open terminationTheory Print_astTerminationTheory;

val _ = computeLib.add_funs [tree_to_list_def, tok_list_to_string_def];
val _ = computeLib.add_funs [elab_p_def, elab_e_def];

fun test_printer d =
let val str = (rhs o concl o EVAL) ``dec_to_sml_string ^d``;
    val toks = (rhs o concl o EVAL) ``(option_map FST o lex_until_toplevel_semicolon) ^str``;
    val ast1 = (rhs o concl o EVAL) ``(OPTION_JOIN o option_map parse_top) ^toks``;
    val ast2 = (rhs o concl o EVAL) ``(option_map (SND o SND o elab_top [] [])) ^ast1``;
    val res = (rhs o concl o EVAL) ``case ^ast2 of SOME (Tdec d) => d = ^d | NONE => F``;
in
  res
end

fun validate_print d =
  EVAL ``let d = ^d in
         case ((option_map (SND o SND o elab_top [] [])) o
               (OPTION_JOIN o option_map parse_top) o
               (option_map FST o lex_until_toplevel_semicolon) o
               dec_to_sml_string)
              d of
          SOME (Tdec d') => d' = d | NONE => F``;

val p1 = validate_print ``Dlet (Pvar "fST")
  (Fun "v3"
     (Mat (Var (Short "v3"))
        [(Pcon (Short "Pair") [Pvar "v2"; Pvar "v1"],
          Var (Short "v2"))]))``;

val p2 = validate_print ``Dlet (Pvar "FST")
  (Fun "v3"
     (Mat (Var (Short "v3"))
        [(Pcon (Short "Pair") [Pvar "v2"; Pvar "v1"],
          Var (Short "v2"))]))``;
