(*
  Kernel types and functions.
 *)

open preamble;
open ml_translatorTheory ml_translatorLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     ast_extrasTheory finite_mapTheory pred_setTheory;
open basisFunctionsLib;

val _ = new_theory "kernel";

(* -------------------------------------------------------------------------
 * Propositional calculus
 * ------------------------------------------------------------------------- *)

Datatype:
  term = And term term
       | Or term term
       | Imp term term
       | Not term
       | Atom num
       | Bot
End

Inductive proves:
[~AndI:]
  (∀H p q.
     proves H p ∧
     proves H q  ⇒
       proves H (And p q)) ∧
[~AndE1:]
  (∀H p q.
     proves H (And p q) ⇒
       proves H p) ∧
[~AndE2:]
  (∀H p q.
     proves H (And p q) ⇒
       proves H q) ∧
[~OrI1:]
  (∀H p q.
     proves H p ⇒
       proves H (Or p q)) ∧
[~OrI2:]
  (∀H p q.
     proves H q ⇒
       proves H (Or p q)) ∧
[~OrE:]
  (∀H p q r.
     proves H (Or p q) ∧
     proves (H ∪ {p}) r ∧
     proves (H ∪ {q}) r ⇒
       proves H r) ∧
[~ImpI:]
  (∀H p q.
     proves (H ∪ {p}) q ⇒
       proves H (Imp p q)) ∧
[~ImpE:]
  (∀H p q.
     proves H p ∧
     proves H (Imp p q) ⇒
       proves H q) ∧
[~NotI:]
  (∀H p.
     proves (H ∪ {p}) Bot ⇒
       proves H (Not p)) ∧
[~NotE:]
  (∀H p.
     proves H p ∧
     proves H (Not p) ⇒
       proves H Bot) ∧
[~BotE:]
  (∀H p.
     proves H Bot ⇒
       proves H p) ∧
[~NotNotE:]
  (∀H p.
     proves H (Not (Not p)) ⇒
       proves H p) ∧
[~Weaken:]
  (∀H p q.
     proves H p ⇒
       proves (H ∪ {q}) p) ∧
[~Assume:]
  (∀H p.
     proves (H ∪ {p}) p)
End

Definition atoms_def:
  atoms (And s t) = (atoms s ∪ atoms t) ∧
  atoms (Or s t) = (atoms s ∪ atoms t) ∧
  atoms (Imp s t) = (atoms s ∪ atoms t) ∧
  atoms (Not t) = atoms t ∧
  atoms (Atom x) = {x} ∧
  atoms Bot = EMPTY
End

(* -------------------------------------------------------------------------
 * Sequents
 * ------------------------------------------------------------------------- *)

Datatype:
  thm = Thm (term list) term
End

Definition list_union_def:
  list_union [] ys = ys ∧
  list_union (x::xs) ys =
    if MEM x xs then list_union xs ys else x::list_union xs ys
End

Definition conj_def:
  conj (Thm h p) (Thm j q) = Thm (list_union h j) (And p q)
End

Definition disj1_def:
  disj1 (Thm h p) q = Thm h (Or p q)
End

Definition imp_def:
  imp (Thm h p) (Thm j q) = Thm (list_union h j) (Imp p q)
End

Definition not_not_def:
  not_not (Thm h p) = Thm h (Not (Not p))
End

Definition TERM_def:
  TERM ctxt tm ⇔ atoms tm ⊆ ctxt
End

Definition THM_def:
  THM ctxt (Thm hyps tm) ⇔
    EVERY (TERM ctxt) hyps ∧
    TERM ctxt tm ∧
    proves (set hyps) tm
End

(* -------------------------------------------------------------------------
 * Translation
 * ------------------------------------------------------------------------- *)

Definition thm2str_def:
  thm2str (Thm h p) = implode "<Thm>"
End

Definition thm2bytes_def:
  thm2bytes th : word8 list = MAP (n2w o ORD) (explode (thm2str th))
End

Definition kernel_ffi_def:
  kernel_ffi = "kernel_ffi"
End

val ffi_print_decl_tm = ``
  [Dletrec unknown_loc
     [("ffi_print", "th",
         Let (SOME "a") (App Opapp [Var (Short "thm2str"); Var (Short "th")])
           (Let (SOME "b") (App Aw8alloc [Lit (IntLit 0); Lit (Word8 0w)])
             (App (FFI kernel_ffi)
               [Var (Short "a"); Var (Short "b")])))]]
  ``;

val _ = use_full_type_names := false;

val _ = register_type “:'a option”;
val _ = register_type “:'a list”;
val _ = translate MEMBER_def;

val _ = ml_prog_update ml_progLib.open_local_block;

val _ = register_type “:term”;
val _ = register_type “:thm”;

val _ = translate (REWRITE_RULE [MEMBER_INTRO] list_union_def);

val _ = ml_prog_update ml_progLib.open_local_in_block;

Theorem conj_v_thm = translate conj_def;
Theorem disj1_v_thm = translate disj1_def;
Theorem imp_v_thm = translate imp_def;
Theorem not_not_v_thm = translate not_not_def;

val _ = ml_prog_update (ml_progLib.add_dec
  “Dtabbrev unknown_loc [] "term" (Atapp [] (Short "term"))” I);
val _ = ml_prog_update (ml_progLib.add_dec
  “Dtabbrev unknown_loc [] "thm" (Atapp [] (Short "thm"))” I);

val _ = ml_prog_update ml_progLib.close_local_block;

val _ = append_prog ffi_print_decl_tm;

val TERM_TYPE_def = fetch "-" "TERM_TYPE_def";
val THM_TYPE_def = fetch "-" "THM_TYPE_def";

(* -------------------------------------------------------------------------
 * Correctness
 * ------------------------------------------------------------------------- *)

Theorem EVERY_list_union:
  EVERY P xs ∧
  EVERY P ys ⇒
    EVERY P (list_union xs ys)
Proof
  Induct_on ‘xs’ \\ rw [list_union_def]
QED

Theorem conj_thm:
  THM ctxt th1 ∧
  THM ctxt th2 ⇒
    THM ctxt (conj th1 th2)
Proof
  Cases_on ‘th1’ \\ Cases_on ‘th2’
  \\ rw [THM_def, conj_def, TERM_def, atoms_def, EVERY_list_union]
  \\ irule proves_AndI
  \\ cheat
QED

(* -------------------------------------------------------------------------
 * 'inferred' relation
 * ------------------------------------------------------------------------- *)

Definition kernel_funs_def:
  kernel_funs = {
    conj_v;
    disj1_v;
    imp_v;
    not_not_v;
    }
End

Definition kernel_locs_def:
  kernel_locs = EMPTY
End

Definition kernel_types_def:
  kernel_types: num set = {3; 4}
End

Inductive inferred:
[~KernelFuns:]
  (∀ctxt f.
     f ∈ kernel_funs ⇒
       inferred ctxt f) ∧
[~TERM:]
  (∀ctxt tm v.
     TERM ctxt tm ∧
     TERM_TYPE tm v ⇒
       inferred ctxt v) ∧
[~THM:]
  (∀ctxt th v.
     THM ctxt th ∧
     THM_TYPE th v ⇒
       inferred ctxt v)
End

Definition ok_event_def:
  ok_event ctxt (IO_event n out y) ⇔
    n = kernel_ffi ⇒
      ∃th v. THM ctxt th ∧
             THM_TYPE th v ∧
             thm2bytes th = out
End

(* -------------------------------------------------------------------------
 * Versions of TERM, THM that only match the outermost structure
 * ------------------------------------------------------------------------- *)

Definition TERM_TYPE_HEAD_def:
  TERM_TYPE_HEAD v ⇔
    ∃vs. v = Conv (SOME (TypeStamp "Term" 3)) vs
End

Definition THM_TYPE_HEAD_def:
  THM_TYPE_HEAD v ⇔
    ∃vs. v = Conv (SOME (TypeStamp "Thm" 4)) vs
End

(* -------------------------------------------------------------------------
 * THM, TERM lemmas
 * ------------------------------------------------------------------------- *)

Theorem EqualityType_TERM_TYPE = EqualityType_rule [] “:term”;

Theorem EqualityType_LIST_TYPE_TERM_TYPE = EqualityType_rule [] “:term list”;

Theorem EqualityType_THM_TYPE = EqualityType_rule [] “:thm”;

Theorem EqualityType_LIST_TYPE_THM_TYPE = EqualityType_rule [] “:thm list”;

val conj_v_def = definition "conj_v_def";
val disj1_v_def = definition "disj1_v_def";
val imp_v_def = definition "imp_v_def";
val not_not_v_def = definition "not_not_v_def";

Theorem kernel_funs_inferred[simp]:
  (∀tm. v ∈ kernel_funs ⇒ ¬TERM_TYPE tm v) ∧
  (∀th. v ∈ kernel_funs ⇒ ¬THM_TYPE th v)
Proof
  conj_tac \\ Cases
  \\ rw [kernel_funs_def, conj_v_def, disj1_v_def, imp_v_def, not_not_v_def,
         TERM_TYPE_def, THM_TYPE_def]
QED

Theorem TERM_from_TERM_TYPE:
  inferred ctxt v ∧
  TERM_TYPE tm v ⇒
    TERM ctxt tm
Proof
  rw [Once inferred_cases] \\ gs []
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def]
    \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ assume_tac EqualityType_TERM_TYPE
  \\ gs [EqualityType_def]
  \\ qpat_x_assum ‘∀a b c d. _ ⇒ (_ ⇔ _)’ (dxrule_then drule) \\ gs []
QED

Theorem THM_from_THM_TYPE:
  inferred ctxt v ∧
  THM_TYPE th v ⇒
    THM ctxt th
Proof
  rw [Once inferred_cases] \\ gs []
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def]
    \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ assume_tac EqualityType_THM_TYPE
  \\ gs [EqualityType_def]
  \\ qpat_x_assum ‘∀a b c d. _ ⇒ (_ ⇔ _)’ (dxrule_then drule) \\ gs []
QED

(* -------------------------------------------------------------------------
 * Theorems about partial application of values in kernel_funs.
 *
 * Hopefully we can stuff some forcing code (i.e. Seq) into the kernel
 * functions to make these theorems easier to prove.
 * ------------------------------------------------------------------------- *)

Theorem conj_v_alt:
  do_partial_app conj_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧
    THM_TYPE_HEAD w
Proof
  simp [conj_v_def, do_partial_app_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
  \\ gvs [LENGTH_EQ_NUM_compute, pmatch_def]
  \\ simp [ml_progTheory.nsLookup_Short_def,
           ml_progTheory.nsLookup_nsBind_compute]
  \\ Cases_on ‘w’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
QED

Theorem disj1_v_alt:
  do_partial_app disj1_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧
    TERM_TYPE_HEAD w
Proof
  simp [disj1_v_def, do_partial_app_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
  \\ gvs [LENGTH_EQ_NUM_compute, pmatch_def]
  \\ simp [ml_progTheory.nsLookup_Short_def,
           ml_progTheory.nsLookup_nsBind_compute]
  \\ simp [do_con_check_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ strip_tac \\ gvs []
  \\ cheat (* disj1 does not examine the constructor of its second argument *)
QED

Theorem imp_v_alt:
  do_partial_app imp_v v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v ∧
    THM_TYPE_HEAD w
Proof
  simp [imp_v_def, do_partial_app_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
  \\ gvs [LENGTH_EQ_NUM_compute, pmatch_def]
  \\ simp [ml_progTheory.nsLookup_Short_def,
           ml_progTheory.nsLookup_nsBind_compute]
  \\ Cases_on ‘w’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
QED

Theorem not_not_v_alt:
  do_opapp [not_not_v; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    (s = s' ∧ res = Rerr (Rabort Rtype_error)) ∨
    (s = s' ∧ res = Rerr (Rraise bind_exn_v)) ∨
    (s = s' ∧ res = Rerr (Rabort Rtimeout_error)) ∨
    THM_TYPE_HEAD v
Proof
  simp [not_not_v_def, do_opapp_def, evaluate_def]
  \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ Cases_on ‘v’ \\ gs [evaluate_def, pmatch_def]
  \\ rename1 ‘Conv opt’ \\ Cases_on ‘opt’ \\ gs [pmatch_def]
  \\ gs [can_pmatch_all_def, astTheory.pat_bindings_def, pmatch_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ Cases_on ‘x’ \\ simp [same_type_def, same_ctor_def]
  \\ IF_CASES_TAC \\ gs [] \\ gs [CaseEq "bool"]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [THM_TYPE_HEAD_def]
QED

val _ = export_theory ();

