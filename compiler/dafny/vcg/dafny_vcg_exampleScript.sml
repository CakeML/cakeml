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

(* Stop EVAL from deep-frying the statement in valid_vcg_prop *)
val _ = computeLib.del_funs [forall_def, eval_true_def];

(* Freshen pass: Make variable names unique and start with v *)
fun eval_freshen prog = EVAL “freshen_program $ ^prog” |> concl |> rhs;

(* Generate VCG for all methods *)
fun eval_vcg prog = EVAL “vcg ^prog” |> concl |> rhs |> rand;

(* Quantify over the given (free) variables, and turn the list of conditions
   into a single condition using conjunction *)
Definition list_to_conj_def:
  list_to_conj [] = T ∧
  list_to_conj (x::xs) = (x ∧ list_to_conj xs)
End

fun valid_vcg_prop vcgs =
  EVAL “list_to_conj $ MAP (λ(var,prop). forall var prop) ^vcgs” |> concl |> rhs;

(** Example 1: Adding one to an integer ensures that it is strictly larger ****)

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
  \\ ‘ALOOKUP st.locals_old «v0» = SOME (SOME val)’ by (gvs [])

  \\ simp [Ntimes evaluate_exp_def 2]
  \\ simp [do_sc_def]

  \\ simp [evaluate_exp_def, read_local_def, do_sc_def, do_bop_def]
  \\ simp [push_locals_def, use_old_def, unuse_old_def, pop_locals_def,
           safe_drop_def]
  \\ simp [state_component_equality]
QED

(** Example 2: McCarthy's 91 function *****************************************)

val mccarthy = eval_freshen
  “Program
     [Method «M» [(«n»,IntT)] []
       [dfy_eq (Var «r»)
          (If (int_le (Var «n») (int_lit 100)) (int_lit 91)
             (BinOp Sub (Var «n») (int_lit 10)))] []
       [BinOp Sub (int_lit 111) (Var «n»)] [(«r»,IntT)] []
         (Then
            (If (int_le (Var «n») (int_lit 100))
               (Dec («tmp»,IntT)
                  (Then
                   (MetCall [VarLhs «tmp»] «M»
                      [BinOp Add (Var «n») (int_lit 11)])
                   (MetCall [VarLhs «r»] «M» [Var «tmp»])))
               (Assign
                  [(VarLhs «r»,ExpRhs (BinOp Sub (Var «n») (int_lit 10)))]))
            Return)]”;

val mccarthy_vcg = eval_vcg mccarthy;

val mccarthy_valid_prop = valid_vcg_prop mccarthy_vcg;

(* Make goals actually readable *)
val _ = max_print_depth := 20;

Theorem mccarthy_correct:
  ^mccarthy_valid_prop
Proof
  simp [forall_def, strict_locals_ok_def, state_inv_def, eval_true_def,
        eval_exp_def, all_values_def]
  \\ rpt strip_tac
  \\ ‘ALOOKUP st.locals_old «v0» = SOME (SOME val)’ by (gvs [])

  \\ simp [Ntimes evaluate_exp_def 2, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 5, read_local_def, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 1]
  \\ simp [Ntimes evaluate_exp_def 3, read_local_def, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 1]
  \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, do_bop_def]

  \\ IF_CASES_TAC \\ simp []
  >- (* i > 100 *)
   (simp [evaluate_exp_def, read_local_def, do_sc_def, do_bop_def,
          do_uop_def, push_locals_def, use_old_def, do_cond_def,
          unuse_old_def, pop_locals_def, safe_drop_def]
    \\ simp [state_component_equality])

  \\ simp [Ntimes evaluate_exp_def 5, read_local_def, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 2, push_locals_def, pop_locals_def,
           safe_drop_def]
  \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 7, read_local_def, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 4, read_local_def, push_locals_def,
           pop_locals_def, safe_drop_def, do_bop_def, do_sc_def]

  \\ IF_CASES_TAC \\ gvs [] >- (intLib.COOPER_TAC)
  \\ cheat

QED
