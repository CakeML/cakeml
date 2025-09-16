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

(* Unrolls a few definitions to make a bit of progress. *)
fun step n =
  simp [Ntimes evaluate_exp_def n, read_local_def, do_sc_def, do_bop_def,
        push_locals_def, pop_locals_def, safe_drop_def, use_old_def,
        unuse_old_def, do_cond_def, get_locs_def, do_uop_def, get_array_len_def,
        index_array_def, val_to_num_def,
        dafny_semanticPrimitivesTheory.get_loc_def, push_local_def];

Theorem plus_one_correct:
  ^plus_one_valid_prop
Proof
  simp [forall_def, strict_locals_ok_def, state_inv_def, eval_true_def,
        eval_exp_def, all_values_def]
  \\ rpt strip_tac
  \\ ‘ALOOKUP st.locals_old «v0» = SOME (SOME val)’ by (gvs [])
  \\ step 20
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
  \\ step 20
  \\ IF_CASES_TAC \\ simp []
  >- (* i > 100 *)
   (step 40 \\ simp [state_component_equality])
  \\ step 30
  \\ IF_CASES_TAC \\ gvs [] >- (intLib.COOPER_TAC)
  \\ step 20
  \\ IF_CASES_TAC \\ gvs [] >- (intLib.COOPER_TAC)
  \\ step 20
  \\ IF_CASES_TAC \\ simp []
  >- (spose_not_then kall_tac \\ intLib.COOPER_TAC)
  \\ step 15
  \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
  \\ qexists ‘111’ \\ simp []
  \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
  \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
    (irule eval_forall_True
     \\ rpt strip_tac
     \\ unabbrev_all_tac
     \\ gvs [all_values_def]
     \\ IF_CASES_TAC \\ simp []
     >- (* ¬(i + 11 ≤ 100) *)
      (step 10
       \\ IF_CASES_TAC \\ simp []
       \\ step 10
       \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
       \\ step 20
       \\ IF_CASES_TAC \\ simp [] >- (spose_not_then kall_tac \\ intLib.COOPER_TAC)
       \\ step 20
       \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
       \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
       \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
       \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
         (irule eval_forall_True
          \\ rpt strip_tac
          \\ unabbrev_all_tac
          \\ gvs [all_values_def]
          \\ step 30
          \\ IF_CASES_TAC \\ simp [])
       \\ simp []
       \\ strip_tac >- (intLib.COOPER_TAC))
     (* i + 11 ≤ 100 *)
     \\ step 5
     \\ gvs [value_same_type_def, all_values_def]
     \\ simp [pop_locals_def, safe_drop_def]
     \\ IF_CASES_TAC >- (simp [])
     \\ step 20
     \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
     \\ step 20
     \\ IF_CASES_TAC \\ simp [] >- (spose_not_then kall_tac \\ intLib.COOPER_TAC)
     \\ step 20
     \\ IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
     \\ reverse IF_CASES_TAC \\ simp [] >- (intLib.COOPER_TAC)
     \\ qmatch_goalsub_abbrev_tac ‘eval_forall dom evalf’
     \\ ‘eval_forall dom evalf = Rval (BoolV T)’ by
       (irule eval_forall_True
        \\ rpt strip_tac
        \\ unabbrev_all_tac
        \\ gvs [all_values_def]
        \\ step 20
        \\ IF_CASES_TAC \\ simp []
          >- (* ≤ 100 *)
           (step 5
            \\ IF_CASES_TAC \\ simp []
            \\ step 10
            \\ IF_CASES_TAC \\ simp []
            \\ IF_CASES_TAC \\ simp []
            \\ intLib.COOPER_TAC)
        \\ step 10
        \\ IF_CASES_TAC \\ simp []
        \\ IF_CASES_TAC \\ simp []
        \\ intLib.COOPER_TAC)
     \\ simp []
     \\ intLib.COOPER_TAC)
  (* ¬ ≤ 100*)
  \\ step 20
  \\ IF_CASES_TAC \\ simp []
  \\ simp [state_component_equality]
  \\ intLib.COOPER_TAC
QED
