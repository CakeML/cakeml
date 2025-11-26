(*
  Concrete examples demonstrating the wp calculus.
*)
Theory dafny_vcg_example
(* For mccarthy_appreturns *)
Ancestors[ignore_grammar]
  ml_translator
  ml_prog
Ancestors
  ast
  semanticPrimitives
  evaluate
  dafny_to_cakemlProof
  namespace
  (* -- *)
  dafny_semanticPrimitives
  dafny_evaluate
  dafny_eval_rel
  dafny_freshen
  dafny_wp_calc (* For forall_def *)
  dafny_vcg
  (* For vc_ok_imp *)
  result_monad
  dafny_compilerProof
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

val mccarthy_prog = eval_freshen
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

val mccarthy = EVAL
  “case ^mccarthy_prog of
   | Program [method] => method
   | _ => ARB”
  |> concl |> rhs;

Definition mccarthy_def:
  mccarthy = ^mccarthy
End

val mccarthy_body = EVAL
  “case mccarthy of
   | Method _ _ _ _ _ _ _ _ body => body
   | _ => ARB”
  |> concl |> rhs;

Definition mccarthy_body_def:
  mccarthy_body = ^mccarthy_body
End

val mccarthy_prog_vcg = eval_vcg mccarthy_prog;

val mccarthy_prog_valid_prop = valid_vcg_prop mccarthy_prog_vcg;

(* Make the goal actually readable *)
val _ = max_print_depth := 20;

Theorem eval_forall_True[local]:
  (∀v. v ∈ dom ⇒ SND (eval v) = Rval (BoolV T)) ⇒
  eval_forall dom eval = Rval (BoolV T)
Proof
  rpt strip_tac
  \\ gvs [eval_forall_def, AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
QED

Theorem mccarthy_prog_correct:
  ^mccarthy_prog_valid_prop
Proof
  (* TODO Combine simps; the main thing that probably needs some care is that
     the parts around "qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’" keep
     working. *)
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
  \\ simp [Ntimes evaluate_exp_def 3, do_sc_def]
  \\ simp [Ntimes evaluate_exp_def 1, use_old_def]
  \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, read_local_def,
           unuse_old_def]
  \\ IF_CASES_TAC \\ gvs [] >- (intLib.COOPER_TAC)
  \\ simp [Ntimes evaluate_exp_def 1, use_old_def]
  \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 5, do_sc_def, do_bop_def, read_local_def]
  \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, push_locals_def,
           pop_locals_def, safe_drop_def, read_local_def]
  \\ simp [Ntimes evaluate_exp_def 4, do_sc_def, do_bop_def, read_local_def,
           do_cond_def, use_old_def, unuse_old_def]
  \\ IF_CASES_TAC \\ simp []
  >- (spose_not_then kall_tac \\ intLib.COOPER_TAC)
  \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def]
  \\ simp [Ntimes evaluate_exp_def 4, do_sc_def, do_bop_def, read_local_def]
  \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, push_locals_def,
           pop_locals_def, safe_drop_def, read_local_def]
  \\ simp [Ntimes evaluate_exp_def 4, do_sc_def, do_bop_def, read_local_def,
           do_cond_def, use_old_def, unuse_old_def]
  \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
  \\ simp [Ntimes evaluate_exp_def 2, set_prev_def, get_locs_def]
  \\ qexists ‘111’ \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
  \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
    (irule eval_forall_True
     \\ rpt strip_tac
     \\ unabbrev_all_tac
     \\ simp [Ntimes evaluate_exp_def 1]
     \\ irule eval_forall_True
     \\ simp [all_values_def]
     \\ rpt strip_tac \\ simp []
     \\ simp [push_local_def]
     \\ simp [Ntimes evaluate_exp_def 4, use_prev_def]
     \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, read_local_def,
              unuse_prev_def]
     \\ simp [Ntimes evaluate_exp_def 3, read_local_def]
     \\ simp [push_locals_def]
     \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, read_local_def]
     \\ simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, read_local_def]
     \\ simp [do_cond_def]
     \\ reverse IF_CASES_TAC \\ simp []
     >- (* ¬(i + 11 ≤ 100) *)
      (simp [Ntimes evaluate_exp_def 3, do_sc_def, do_bop_def, read_local_def,
             pop_locals_def, safe_drop_def]
       \\ IF_CASES_TAC \\ simp []
       \\ simp [Ntimes evaluate_exp_def 5, read_local_def, do_sc_def, do_bop_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def, unuse_old_def]
       \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def, unuse_old_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def, unuse_old_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def, unuse_old_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                unuse_old_def, do_cond_def]
       \\ IF_CASES_TAC \\ simp [] >- (spose_not_then kall_tac \\ intLib.COOPER_TAC)
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                unuse_old_def, do_cond_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                unuse_old_def, do_cond_def]
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                unuse_old_def, do_cond_def]
       \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
       \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                unuse_old_def, do_cond_def, get_locs_def, set_prev_def]
       \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
       \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
         (irule eval_forall_True
          \\ rpt strip_tac
          \\ unabbrev_all_tac
          \\ simp [Ntimes evaluate_exp_def 1]
          \\ irule eval_forall_True
          \\ simp [all_values_def]
          \\ rpt strip_tac
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ IF_CASES_TAC \\ simp []
          >- (* ≤ 100 *)
           (simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                  push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                  unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                  push_local_def, unuse_prev_def]
            \\ IF_CASES_TAC \\ simp []
            \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                     push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                     unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                     push_local_def, unuse_prev_def]
            \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
            \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                     push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                     unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                     push_local_def, unuse_prev_def])
           (* ¬ ≤ 100*)
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ IF_CASES_TAC \\ simp []
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
          \\ strip_tac \\ intLib.COOPER_TAC)
       \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                unuse_old_def, do_cond_def, get_locs_def, set_prev_def]
       \\ strip_tac >- (intLib.COOPER_TAC))
     (* i + 11 ≤ 100 *)
     \\ simp [Ntimes evaluate_exp_def 1]
     \\ gvs [value_same_type_def, all_values_def]
     \\ simp [pop_locals_def, safe_drop_def]
     \\ IF_CASES_TAC >- (simp [])
     \\ simp []
     \\ simp [Ntimes evaluate_exp_def 6, read_local_def, push_locals_def,
              pop_locals_def, safe_drop_def, do_sc_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
              push_locals_def, pop_locals_def, safe_drop_def]
     \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 1, use_old_def]
     \\ simp [Ntimes evaluate_exp_def 1, read_local_def]
     \\ simp [unuse_old_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
              push_locals_def, pop_locals_def, safe_drop_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
              use_old_def]
     \\ simp [do_cond_def, unuse_old_def]
     \\ IF_CASES_TAC \\ simp [] >- (spose_not_then kall_tac \\ intLib.COOPER_TAC)
     \\ simp [Ntimes evaluate_exp_def 5, read_local_def, do_sc_def, do_bop_def]
     \\ simp [Ntimes evaluate_exp_def 5, push_locals_def, pop_locals_def,
              safe_drop_def, read_local_def, do_sc_def, do_bop_def]
     \\ simp [use_old_def]
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def]
     \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
     \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
     \\ simp [get_locs_def, set_prev_def, unuse_old_def]
     \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
     \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
       (irule eval_forall_True
          \\ rpt strip_tac
          \\ unabbrev_all_tac
          \\ simp [Ntimes evaluate_exp_def 1]
          \\ irule eval_forall_True
          \\ simp [all_values_def]
          \\ rpt strip_tac
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ IF_CASES_TAC \\ simp []
          >- (* ≤ 100 *)
           (simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                  push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                  unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                  push_local_def, unuse_prev_def]
            \\ IF_CASES_TAC \\ simp []
            \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                     push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                     unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                     push_local_def, unuse_prev_def]
            \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
            \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                     push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                     unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                     push_local_def, unuse_prev_def])
           (* ¬ ≤ 100*)
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ IF_CASES_TAC \\ simp []
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
                   push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
                   unuse_old_def, do_cond_def, get_locs_def, set_prev_def, use_prev_def,
                   push_local_def, unuse_prev_def]
          \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
          \\ strip_tac \\ intLib.COOPER_TAC)
     \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
              push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
              unuse_old_def, do_cond_def, get_locs_def, set_prev_def]
     \\ strip_tac >- (intLib.COOPER_TAC))
  \\ simp []
  \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
  \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
           push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
           unuse_old_def, do_cond_def, get_locs_def, set_prev_def, unset_prev_def]
  \\ simp [Ntimes evaluate_exp_def 4, read_local_def, do_sc_def, do_bop_def,
           push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
           unuse_old_def, do_cond_def, get_locs_def, set_prev_def, unset_prev_def,
           do_uop_def]
  \\ simp [state_component_equality]
QED

Theorem vc_ok_mccarthy_prog:
  vc_ok ^mccarthy_prog
Proof
  simp [vc_ok_def] \\ EVAL_TAC \\ simp [mccarthy_prog_correct]
QED

Definition mccarthy_env_def:
  mccarthy_env = <| prog := ^mccarthy_prog |>
End

Definition compile_stmt_def:
  compile_stmt stmt = from_stmt (remove_assert_stmt stmt) 0
End

Theorem vc_ok_mccarthy_imp:
  ALOOKUP s.locals «v0» = SOME (SOME (IntV n)) ∧
  compile_stmt mccarthy_body = INR mccarthy_body_cml ∧
  (* more "technical" conditions *)
  state_rel m l s (t: 'ffi cml_state) env_cml ∧
  base_at_most base t.refs l ∧
  env_rel mccarthy_env env_cml ∧
  state_ok s [] [(«v1»,IntT)] ∧ ¬MEM «v2» (MAP FST s.locals)
  ⇒
  ∃s' ck t' m' ck'.
    eval_stmt s mccarthy_env mccarthy_body s' (Rstop Sret) ∧
    ALOOKUP s'.locals «v1» = SOME (SOME (IntV if n <= 100 then 91 else n - 10)) ∧
    evaluate (t with clock := ck) env_cml [mccarthy_body_cml] =
      (t', Rerr (Rraise (Conv (SOME ret_stamp) []))) ∧
    state_rel m' l (s' with clock := ck') t' env_cml ∧
    store_preserve (FRANGE m) base t.refs t'.refs ∧
    m ⊑ m' ∧ is_extension t.refs m m' ∧
    cml_state_preserved t t'
Proof
  rpt strip_tac
  \\ qspecl_then [‘mccarthy_env’, ‘«M»’] mp_tac vc_ok_imp
  \\ gvs [mccarthy_env_def]
  \\ simp [vc_ok_mccarthy_prog, get_member_def, get_member_aux_def]
  (* lvl doesn't matter as we don't have loops *)
  \\ disch_then $
       qspecl_then [‘s’, ‘0’, ‘mccarthy_body_cml’, ‘m’,
                    ‘l’, ‘t’, ‘env_cml’, ‘[]’, ‘[]’, ‘base’] mp_tac
  \\ ‘state_ok s [(«v0»,IntT)] [(«v1»,IntT)]’ by
    (gvs [state_ok_def, strict_locals_ok_def, all_values_def])
  \\ impl_tac >-
   (rpt strip_tac
    >- (EVAL_TAC)
    >- (simp [] \\ EVAL_TAC)
    >- (simp [])
    >- (EVAL_TAC)
    >- (simp [])
    >- (EVAL_TAC)
    >- (EVAL_TAC \\ simp [])
    >- (simp [])
    >- (simp []))
  \\ rpt strip_tac
  \\ simp [mccarthy_body_def] \\ first_assum $ irule_at (Pos hd)
  \\ first_assum $ irule_at (Pos last)
  \\ first_assum $ irule_at (Pos last)
  \\ first_assum $ irule_at (Pos last)
  \\ first_assum $ irule_at (Pos last)
  \\ drule_then assume_tac eval_stmt_const
  \\ rename [‘eval_stmt _ _ _ s' _’]
  \\ ‘s'.locals_old = s.locals’ by (gvs [state_ok_def])
  \\ gvs []
  \\ qpat_x_assum ‘conditions_hold _ _ _’ mp_tac
  \\ gvs [conditions_hold_def, eval_true_def, wrap_Old_def,
          eval_exp_def, evaluate_exp_def, read_local_def]
  \\ ntac 2 CASE_TAC \\ gvs []
  \\ simp [do_sc_def, use_old_def, do_bop_def, do_cond_def, unuse_old_def]
  \\ IF_CASES_TAC >-
   (simp [evaluate_exp_def]
    \\ simp [oneline value_same_type_def] \\ CASE_TAC \\ gvs []
    \\ rpt strip_tac \\ gvs []
    \\ first_assum $ irule_at (Pos hd)
    \\ first_assum $ irule_at (Pos hd))
  \\ simp [evaluate_exp_def, read_local_def, use_old_def, do_sc_def, do_bop_def]
  \\ simp [oneline value_same_type_def] \\ CASE_TAC \\ gvs []
  \\ simp [unuse_old_def]
  \\ rpt strip_tac \\ gvs []
  \\ first_assum $ irule_at (Pos hd)
  \\ first_assum $ irule_at (Pos hd)
QED

(* Manually adding what we need from ml_translator to our grammar: *)
Overload "AppReturns"[local] = “ml_translator$AppReturns”
Overload "INT"[local] = “ml_translator$INT”
Overload "eval_rel"[local] = “ml_prog$eval_rel”
Overload "empty_state"[local] = “ml_translator$empty_state”

Definition compile_member_def:
  compile_member member = from_member_decl $ remove_assert_member member
End

Definition clos_env_ok_def:
  clos_env_ok clos_env ⇔
    has_cons clos_env.c ∧
    (∃clos_env'.
       nsLookup clos_env.v (Short "int_to_string") =
         SOME (cml_int_to_string_clos clos_env') ∧
       int_to_string_env clos_env')
End

Theorem get_member_mccarthy_imp[local]:
  get_member name mccarthy_env.prog = SOME member ⇒
  name = «M» ∧ member = mccarthy
Proof
  EVAL_TAC \\ IF_CASES_TAC \\ simp []
QED

Theorem mccarthy_appreturns[local]:
  compile_member mccarthy = INR mccarthy_cml ∧
  clos_env_ok clos_env
  ⇒
  AppReturns (INT n) (Recclosure clos_env [mccarthy_cml] "dfy_M")
    (INT (if n <= 100 then 91 else n - 10))
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘compile_member _ = _’ $
       assume_tac o GSYM o CONV_RULE EVAL
  \\ simp [AppReturns_def]
  \\ rpt strip_tac
  \\ simp [do_opapp_def, find_recfun_def, eval_rel_def, empty_state_def,
           PULL_EXISTS]
  \\ simp [Ntimes evaluate_def 3, do_app_def, store_alloc_def]
  \\ simp [Ntimes evaluate_def 3, do_app_def, store_alloc_def]
  \\ simp [Ntimes evaluate_def 1]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ env_cml’
  \\ ‘env_rel mccarthy_env env_cml’ by
    (simp [env_rel_def]
     \\ rpt strip_tac
     >- (* has_cons *)
      (gvs [clos_env_ok_def, has_cons_def]
       \\ unabbrev_all_tac \\ gvs [])
     >- (* int_to_string available *)
      (gvs [clos_env_ok_def, has_cons_def]
       \\ unabbrev_all_tac
       \\ simp [nsOptBind_def, build_rec_env_def]
       \\ first_assum $ irule_at (Pos last) \\ simp [])
     >- (* is_fresh_member *)
      (imp_res_tac get_member_mccarthy_imp
       \\ gvs [] \\ EVAL_TAC)
     >- (* no_shadow_method *)
      (imp_res_tac get_member_mccarthy_imp
       \\ gvs [] \\ EVAL_TAC)
     >- (* no_assert_member *)
      (imp_res_tac get_member_mccarthy_imp
       \\ gvs [] \\ EVAL_TAC)
     >- (* callable_rel *)
      (imp_res_tac get_member_mccarthy_imp \\ gvs []
       \\ unabbrev_all_tac
       \\ gvs [nsOptBind_def, build_rec_env_def, mccarthy_env_def]
       \\ drule callable_rel_rules \\ simp []
       \\ disch_then irule \\ gvs []
       \\ gvs [clos_env_ok_def]
       \\ conj_tac
       >- (first_assum $ irule_at (Pos hd) \\ simp [])
       \\ EVAL_TAC))
  \\ qabbrev_tac
     ‘t =
      <| clock := 42;  (* clock shouldn't matter *)
         refs := refs ++ [Refv v] ++ [Refv (Litv (IntLit 0))];
         ffi := initial_ffi_state ARB (); next_type_stamp := 0;
         next_exn_stamp := 0; eval_state := NONE|>’
  \\ ‘∃l s.
        ALOOKUP s.locals «v0» = SOME (SOME (IntV n)) ∧
        state_ok s [] [(«v1»,IntT)] ∧ ¬MEM «v2» (MAP FST s.locals) ∧
        state_rel FEMPTY l s t env_cml ∧ base_at_most (LENGTH refs) t.refs l’ by
    (qexists ‘FEMPTY |++ [(«v0», LENGTH refs); («v1», LENGTH refs + 1)]’
     \\ qexists
        ‘<| clock := t.clock;
            locals := [(«v0», SOME (IntV n)); («v1», NONE)];
            heap := [];
            locals_old := [(«v0», SOME (IntV n)); («v1», NONE)];
            heap_old := [];
            locals_prev := []; heap_prev := [] |>’
     \\ simp []
     \\ rpt conj_tac
     \\ gvs [Abbr ‘t’, Abbr ‘env_cml’]
     >- (* state_ok *)
      (simp [state_ok_def, state_inv_def, locals_inv_def, strict_locals_ok_def,
             value_inv_def, heap_inv_def, locals_ok_def, LLOOKUP_def])
     >- (* state_rel *)
      (simp [state_rel_def, array_rel_def, LLOOKUP_def]
       \\ simp [dafny_to_cakemlProofTheory.locals_rel_def]
       \\ rpt strip_tac
       >- (EVAL_TAC \\ gvs [INJ_DEF] \\ rpt strip_tac \\ gvs [])
       >- (dxrule_then assume_tac (SRULE [SUBSET_DEF] FRANGE_FUPDATE_LIST_SUBSET)
           \\ gvs [])
       >- (gvs [AllCaseEqs()]
           >-
            (qexists ‘LENGTH refs’ \\ EVAL_TAC
             \\ simp [LENGTH_APPEND, EL_APPEND]
             \\ gvs [INT_def]
             \\ gvs [Abbr ‘env_cml’, nsOptBind_def])
           >-
            (qexists ‘LENGTH refs + 1’ \\ EVAL_TAC
             \\ simp [LENGTH_APPEND, EL_APPEND]
             \\ gvs [INT_def]
             \\ gvs [nsOptBind_def])))
     >- (simp [base_at_most_def]
         \\ rpt strip_tac
         \\ dxrule_then assume_tac (SRULE [SUBSET_DEF] FRANGE_FUPDATE_LIST_SUBSET)
         \\ gvs []))
  \\ drule $ INST_TYPE [“:'ffi” |-> “:unit”] vc_ok_mccarthy_imp \\ simp []
  \\ disch_then $ drule_at (Pos last)
  \\ disch_then $ drule_at (Pos last)
  \\ disch_then $ drule_at (Pos last)
  \\ assume_tac $ EVAL “compile_stmt mccarthy_body” \\ simp []
  \\ disch_then $ qx_choosel_then [‘s'’, ‘ck’, ‘t'’, ‘m'’, ‘ck'’] assume_tac
  \\ fs []
  \\ qrefinel [‘_’, ‘_’, ‘ck’]
  \\ gvs [Abbr ‘t’]
  \\ simp [can_pmatch_all_def, pmatch_def]
  \\ gvs [clos_env_ok_def, has_cons_def]
  \\ simp [same_type_def, ret_stamp_def, same_ctor_def]
  \\ simp [evaluate_match_def, pat_bindings_def, pmatch_def, Abbr ‘env_cml’]
  \\ simp [same_type_def, ret_stamp_def, same_ctor_def]
  \\ simp [evaluate_def, nsOptBind_def, do_app_def]
  \\ ‘store_lookup (LENGTH refs + 1) t'.refs =
        SOME (Refv (Litv (IntLit (if n ≤ 100 then 91 else n − 10))))’ by
    (gvs [state_rel_def, dafny_to_cakemlProofTheory.locals_rel_def]
     \\ first_x_assum $ drule
     \\ impl_tac >- (EVAL_TAC)
     \\ simp [nsOptBind_def])
  \\ simp [INT_def]
  \\ qexistsl [‘DROP (LENGTH refs) t'.refs’, ‘t'.clock’]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ gvs [cml_state_preserved_def]
  (* refs *)
  \\ gvs [store_preserve_def, store_lookup_def]
  \\ irule LIST_EQ \\ gvs []
  \\ rpt strip_tac
  \\ gvs [EL_APPEND]
  \\ IF_CASES_TAC
  \\ gvs [EL_DROP]
QED

(** Example 3: Swapping elements in an array **********************************)

val swap = eval_freshen
  “Program
      [Method «Swap» [(«a»,ArrT IntT); («i»,IntT); («j»,IntT)]
         [BinOp And (int_le (int_lit 0) (Var «i»))
            (int_lt (Var «i») (ArrLen (Var «a»)));
          BinOp And (int_le (int_lit 0) (Var «j»))
            (int_lt (Var «j») (ArrLen (Var «a»)))]
         [dfy_eq (ArrSel (Var «a») (Var «i»))
            (OldHeap (ArrSel (Var «a») (Var «j»)));
          dfy_eq (ArrSel (Var «a») (Var «j»))
            (OldHeap (ArrSel (Var «a») (Var «i»)))] []
         [Var «a»; Var «i»; Var «j»] [] [Var «a»]
         (Dec («temp»,IntT)
            (Then
               (Assign [(VarLhs «temp»,ExpRhs (ArrSel (Var «a») (Var «i»)))])
               (Then
                  (Assign
                     [(ArrSelLhs (Var «a») (Var «i»),
                       ExpRhs (ArrSel (Var «a») (Var «j»)))])
                  (Then
                     (Assign
                        [(ArrSelLhs (Var «a») (Var «j»),ExpRhs (Var «temp»))])
                     Return))))]”;

val swap_vcg = eval_vcg swap;

val swap_valid_prop = valid_vcg_prop swap_vcg;

val _ = max_print_depth := 20;

(* Unrolls a few definitions to make a bit of progress. *)
fun step n =
  simp [Ntimes evaluate_exp_def n, read_local_def, do_sc_def, do_bop_def,
        push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
        unuse_old_def, do_cond_def, get_locs_def, set_prev_def, unset_prev_def,
        do_uop_def, get_array_len_def, index_array_def, val_to_num_def,
        dafny_semanticPrimitivesTheory.get_loc_def, use_prev_def,
        unuse_prev_def, push_local_def, use_prev_heap_def, use_old_heap_def,
        unuse_old_heap_def];

Theorem IMP_SND_evaluate_exp_imp[local]:
  evaluate_exp st env b = (st, Rval (BoolV bv)) ∧
  (bv ⇒ evaluate_exp st env a = (st, Rval (BoolV T)))
  ⇒
  SND (evaluate_exp st env (imp b a)) = Rval (BoolV T)
Proof
  rpt strip_tac
  \\ gvs [evaluate_exp_def, do_sc_def, do_bop_def]
  \\ Cases_on ‘bv’ \\ gvs []
QED

Theorem swap_correct:
  ^swap_valid_prop
Proof
  simp [forall_def, strict_locals_ok_def, state_inv_def]
  \\ rpt strip_tac
  \\ last_assum $ qspecl_then [‘«v0»’, ‘ArrT IntT’] assume_tac
  \\ last_assum $ qspecl_then [‘«v1»’, ‘IntT’] assume_tac
  \\ last_x_assum $ qspecl_then [‘«v2»’, ‘IntT’] assume_tac
  \\ gvs [all_values_def]
  \\ pop_assum mp_tac
  \\ rename [‘ALOOKUP _ _ = SOME (SOME (IntV idx_i))’]
  \\ strip_tac
  \\ rename [‘ALOOKUP _ _ = SOME (SOME (IntV idx_j))’]
  \\ simp [eval_true_def, eval_exp_def]
  (* Clock shouldn't matter since there are no loops or calls *)
  \\ qexistsl [‘st.clock’, ‘st.clock’] \\ gvs []
  \\ step 6
  \\ IF_CASES_TAC \\ gvs []
  \\ step 4
  \\ IF_CASES_TAC \\ gvs []
  \\ step 4
  \\ IF_CASES_TAC \\ gvs []
  \\ step 4
  \\ IF_CASES_TAC \\ gvs []
  \\ step 6
  \\ IF_CASES_TAC \\ gvs [] >- (intLib.COOPER_TAC)
  \\ rename [‘ALOOKUP _ _ = SOME (SOME (ArrV len loc _))’]
  \\ ‘value_inv st.heap_old (ArrV len loc IntT)’ by
    (gvs [locals_inv_def]
     \\ rev_drule_then assume_tac ALOOKUP_MEM
     \\ gvs [EVERY_MEM]
     \\ last_assum drule \\ simp [])
  \\ gvs [value_inv_def]
  \\ CASE_TAC \\ gvs []
  >- (gvs [oEL_THM] \\ intLib.COOPER_TAC)
  \\ rename [‘LLOOKUP _ (Num _) = SOME v’]
  \\ ‘∃val_i. v = IntV val_i’ by
    (gvs [heap_inv_def]
     \\ last_x_assum drule_all
     \\ Cases_on ‘v’ \\ gvs [value_has_type_def])
  \\ step 14
  \\ IF_CASES_TAC \\ gvs [] >- (intLib.COOPER_TAC)
  \\ CASE_TAC \\ gvs []
  >- (gvs [oEL_THM] \\ intLib.COOPER_TAC)
  \\ rename [‘LLOOKUP _ (Num _) = SOME v’]
  \\ ‘∃val_j. v = IntV val_j’ by
    (gvs [heap_inv_def]
     \\ last_x_assum drule_all
     \\ Cases_on ‘v’ \\ gvs [value_has_type_def])
  \\ step 7
  (* Now evaluating SetPrev $ ForallHeap ... *)
  \\ step 5
  \\ simp [get_loc_def]
  \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
  \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
    (irule eval_forall_True
     \\ rpt strip_tac
     \\ unabbrev_all_tac \\ gvs []
     \\ irule IMP_SND_evaluate_exp_imp
     \\ gvs [IN_DEF, valid_mod_def]
     \\ first_x_assum $ drule_then assume_tac \\ gvs []
     \\ step 10
     \\ CASE_TAC \\ gvs []
     >- (gvs [oEL_THM])
     \\ step 1
     \\ rename [‘LLOOKUP _ (Num _) = SOME v’]
     \\ ‘∃ix. v = IntV ix’ by
       (gvs [heap_inv_def]
        \\ first_x_assum drule_all
        \\ Cases_on ‘v’ \\ gvs [value_has_type_def])
     \\ gvs []
     \\ Cases_on ‘ix = val_j’ \\ simp []
     \\ pop_assum SUBST_ALL_TAC
     \\ step 5
     \\ rename [‘LLOOKUP arr₁ _ = _’]
     \\ qexists
          ‘∀i. i ≠ idx_i ∧ 0 ≤ i ∧ idx_i < &LENGTH arr₁ ⇒
               LLOOKUP arr₁ (Num i) = LLOOKUP arr (Num i)’
     \\ conj_tac
     >-
      (qmatch_goalsub_abbrev_tac ‘eval_forall _ evalf’
       \\ gvs [eval_forall_def, all_values_def]
       \\ ‘∀i. SND (evalf (IntV i)) = Rval (BoolV (
             i ≠ idx_i ∧ 0 ≤ i ⇒ LLOOKUP arr₁ (Num i) = LLOOKUP arr (Num i)))’
         by
         (strip_tac
          \\ unabbrev_all_tac \\ gvs []
          \\ step 6
          \\ IF_CASES_TAC \\ gvs []
          \\ step 4
          \\ IF_CASES_TAC \\ gvs []
          \\ step 4
          \\ IF_CASES_TAC \\ gvs []
          >-
           (gvs [oEL_THM]
            \\ IF_CASES_TAC \\ gvs []
            \\ spose_not_then kall_tac \\ intLib.COOPER_TAC)
          \\ step 4
          \\ IF_CASES_TAC \\ gvs []
          >- (intLib.COOPER_TAC)
          \\ CASE_TAC \\ gvs []
          >- (gvs [oEL_THM] \\ intLib.COOPER_TAC)
          \\ step 4
          \\ CASE_TAC \\ gvs []
          >- (gvs [oEL_THM] \\ intLib.COOPER_TAC)
          \\ gvs [heap_inv_def]
          \\ first_x_assum $ drule_all_then assume_tac
          \\ last_x_assum $ drule_all_then assume_tac
          \\ rename [‘value_has_type _ x’]
          \\ Cases_on ‘x’ \\ gvs [value_has_type_def]
          \\ rename [‘value_has_type _ x’]
          \\ Cases_on ‘x’ \\ gvs [value_has_type_def])
       \\ IF_CASES_TAC \\ gvs []
       \\ IF_CASES_TAC \\ gvs []
       \\ IF_CASES_TAC \\ gvs []
       \\ first_assum $ irule_at (Pos last) \\ gvs [])
     \\ strip_tac
     \\ step 22
     \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
     \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
       (irule eval_forall_True
        \\ rpt strip_tac
        \\ unabbrev_all_tac \\ gvs []
        \\ irule IMP_SND_evaluate_exp_imp
        \\ gvs [IN_DEF, valid_mod_def]
        \\ step 6
        \\ first_x_assum $ drule_then assume_tac \\ gvs []
        \\ CASE_TAC \\ gvs []
        >- (gvs [oEL_THM])
        \\ rename [‘LLOOKUP arr₂ _ = _’]
        \\ step 3
        \\ rename [‘LLOOKUP _ (Num _) = SOME v’]
        \\ ‘∃iy. v = IntV iy’ by
          (gvs [heap_inv_def]
           \\ first_x_assum drule_all
           \\ Cases_on ‘v’ \\ gvs [value_has_type_def])
        \\ gvs []
        \\ Cases_on ‘iy = val_i’ \\ simp []
        \\ pop_assum SUBST_ALL_TAC
        \\ step 5
        \\ qexists
           ‘∀i. i ≠ idx_j ∧ 0 ≤ i ∧ idx_j < &LENGTH arr ⇒
                LLOOKUP arr₂ (Num i) = LLOOKUP arr₁ (Num i)’
        \\ conj_tac
        >-
         (qmatch_goalsub_abbrev_tac ‘eval_forall _ evalf’
          \\ gvs [eval_forall_def, all_values_def]

          \\ ‘∀i. SND (evalf (IntV i)) = Rval (BoolV (
                i ≠ idx_j ∧ 0 ≤ i ⇒ LLOOKUP arr₂ (Num i) = LLOOKUP arr₁ (Num i)))’
            by
            (strip_tac
             \\ unabbrev_all_tac \\ gvs []
             \\ step 6
             \\ IF_CASES_TAC \\ gvs []
             \\ step 4
             \\ IF_CASES_TAC \\ gvs []
             \\ step 4
             \\ IF_CASES_TAC \\ gvs []
             >-
              (gvs [oEL_THM]
               \\ IF_CASES_TAC \\ gvs []
               \\ spose_not_then kall_tac \\ intLib.COOPER_TAC)
             \\ step 4
             \\ IF_CASES_TAC \\ gvs []
             >- (intLib.COOPER_TAC)
             \\ CASE_TAC \\ gvs []
             >- (gvs [oEL_THM] \\ intLib.COOPER_TAC)
             \\ step 4
             \\ CASE_TAC \\ gvs []
             >- (gvs [oEL_THM] \\ intLib.COOPER_TAC)
             \\ gvs [heap_inv_def]
             \\ first_x_assum $ drule_all_then assume_tac
             \\ first_x_assum $ drule_all_then assume_tac
             \\ gvs []
             \\ rename [‘value_has_type _ x’]
             \\ Cases_on ‘x’ \\ gvs [value_has_type_def]
             \\ rename [‘value_has_type _ x’]
             \\ Cases_on ‘x’ \\ gvs [value_has_type_def])
          \\ IF_CASES_TAC \\ gvs []
          \\ IF_CASES_TAC \\ gvs []
          \\ IF_CASES_TAC \\ gvs []
          \\ first_assum $ irule_at (Pos last) \\ gvs [])
        \\ strip_tac
        \\ step 7
        \\ CASE_TAC \\ gvs []
        >- (gvs [oEL_THM])
        \\ step 7
        \\ Cases_on ‘idx_i = idx_j’ \\ gvs []
        \\ step 11
        \\ step 11)
     \\ gvs [])
  \\ simp [state_component_equality]
QED
