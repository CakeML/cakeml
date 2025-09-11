(*
  Concrete examples demonstrating the wp calculus.
*)
Theory dafny_vcg_example
Ancestors
  dafny_semanticPrimitives
  dafny_freshen
  dafny_wp_calc
Libs
  preamble

Definition list_to_conj_def:
  list_to_conj [] = T ∧
  list_to_conj (x::xs) = (x ∧ list_to_conj xs)
End

fun eval_freshen prog = EVAL “freshen_program $ ^prog” |> concl |> rhs;
fun eval_vcg prog = EVAL “vcg ^prog” |> concl |> rhs |> rand;
fun valid_vcg_prop vcgs =
  EVAL “list_to_conj $ MAP (λ(var,prop). forall var prop) ^vcgs” |> concl |> rhs;

val plus_one = eval_freshen
  “Program
   [Method «PlusOne» [(«n»,IntT)] [] [int_lt (Var «n») (Var «r»)] []
     [Var «n»] [(«r»,IntT)] []
     (Then
        (Assign [(VarLhs «r»,ExpRhs (BinOp Add (Var «n») (int_lit 1)))])
        Return)]”;

val plus_one_vcg = eval_vcg plus_one;

val plus_one_valid_prop = valid_vcg_prop plus_one_vcg;

Theorem plus_one_correct:
  ^plus_one_valid_prop
Proof
  rpt strip_tac
  \\ last_x_assum $ qspecl_then [‘«v0»’, ‘IntT’] assume_tac \\ gvs []
  \\ gvs [all_values_def]
  \\ gvs [REV_DEF, state_component_equality]
QED
