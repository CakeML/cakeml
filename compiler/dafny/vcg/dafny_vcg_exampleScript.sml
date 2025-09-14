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

(* Make the goal actually readable *)
val _ = max_print_depth := 20;

Triviality eval_forall_True:
  (∀v. v ∈ dom ⇒ SND (eval v) = Rval (BoolV T)) ⇒
  eval_forall dom eval = Rval (BoolV T)
Proof
  rpt strip_tac
  \\ gvs [eval_forall_def, AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
QED

Theorem mccarthy_correct:
  ^mccarthy_valid_prop
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
        unuse_prev_def, push_local_def, use_prev_heap_def];

Triviality IMP_SND_evaluate_exp_imp:
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
     \\ IF_CASES_TAC \\ gvs []
     \\ step 5
     \\ rename [‘LLOOKUP arr' _ = _’]
     \\ qexists
          ‘∀i. i ≠ idx_i ∧ 0 ≤ i ∧ idx_i < &LENGTH arr ⇒
               LLOOKUP arr' (Num i) = LLOOKUP arr (Num i)’
     \\ conj_tac

     >- (cheat)
     \\ strip_tac
     \\ step 22
     \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
     \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
       (irule eval_forall_True
        \\ rpt strip_tac
        \\ unabbrev_all_tac \\ gvs []
        \\ irule IMP_SND_evaluate_exp_imp
        \\ gvs [IN_DEF, valid_mod_def]

        \\ cheat)
     \\ gvs [])
  \\ simp [state_component_equality]
QED
