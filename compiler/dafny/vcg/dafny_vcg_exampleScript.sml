(*
  Concrete examples demonstrating the wp calculus.
*)
Theory dafny_vcg_example
Ancestors
  dafny_semanticPrimitives
  dafny_evaluate
  dafny_eval_rel
  dafny_freshen
  dafny_wp_calc
Libs
  preamble

Definition list_to_conj_def:
  list_to_conj [] = T ∧
  list_to_conj (x::xs) = (x ∧ list_to_conj xs)
End

(* Stop EVAL from deep-frying the statement in valid_vcg_prop *)
val _ = computeLib.del_funs [forall_def, eval_true_def];

fun eval_freshen prog = EVAL “freshen_program $ ^prog” |> concl |> rhs;
fun eval_vcg prog = EVAL “vcg ^prog” |> concl |> rhs |> rand;
fun valid_vcg_prop vcgs =
  EVAL “list_to_conj $ MAP (λ(var,prop). forall var prop) ^vcgs” |> concl |> rhs;

(* Example 1: Adding one to an integer ensures that it is strictly larger *)

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
  simp [forall_def, strict_locals_ok_def, state_inv_def, eval_true_def,
        eval_exp_def, all_values_def]
  \\ rpt strip_tac
  \\ simp [Ntimes evaluate_exp_def 2]
  \\ simp [do_sc_def]
  \\ ‘ALOOKUP st.locals_old «v0» = SOME (SOME val)’ by (gvs [])
  \\ simp [evaluate_exp_def, read_local_def, do_sc_def, do_bop_def]
  \\ simp [push_locals_def, use_old_def, unuse_old_def, pop_locals_def,
           safe_drop_def]
  \\ simp [state_component_equality]
QED
