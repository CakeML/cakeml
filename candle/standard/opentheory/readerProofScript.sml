(*
  Correctness proofs about the OpenTheory article checker's CakeML
  implementation. In particular, anything the article checker proves
  follows by logical inference in Candle's version of the HOL logic.
*)
open preamble ml_monadBaseTheory
     holKernelTheory holKernelProofTheory
     holSyntaxTheory holSyntaxExtraTheory
     readerTheory reader_initTheory
     TextIOProgTheory

val _ = new_theory"readerProof";

Overload monad_bind[local] = “st_ex_bind”
Overload monad_unitbind[local] = “λx y. st_ex_bind x (λ z. y)”
Overload monad_ignore_bind[local] = “λx y. st_ex_bind x (λz. y)”
Overload return[local] = “st_ex_return”
Overload failwith[local] = “raise_Fail”
val _ = temp_add_monadsyntax()

val case_eq_thms =
  CaseEqs ["prod", "exc", "hol_exn", "term", "thm",
           "object", "option", "list", "update",
           "mlstring", "state", "type", "sum",
           "hol_refs", "command"]

(* TODO move *)

Theorem new_axiom_not_clash[simp]:
  new_axiom ax s ≠ (Failure (Clash tm), t)
Proof
  strip_tac
  \\ fs [new_axiom_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
         case_eq_thms, bool_case_eq, COND_RATOR, get_the_axioms_def,
         set_the_axioms_def] \\ rw [] \\ fs []
QED

Theorem new_constant_not_clash[simp]:
  new_constant (a,b) s ≠ (Failure (Clash tm), t)
Proof
  rw [new_constant_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem new_type_not_clash[simp]:
  new_type (a,b) s ≠ (Failure (Clash tm), t)
Proof
  rw [new_type_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem dest_abs_not_clash[simp]:
  dest_abs x s ≠ (Failure (Clash tm), t)
Proof
  EVAL_TAC \\ PURE_CASE_TAC \\ fs []
QED

(* -------------------------------------------------------------------------
 * Reader does not raise Clash
 * ------------------------------------------------------------------------- *)

Theorem find_axiom_not_clash[simp]:
  find_axiom (a,b) c ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `a`
  \\ rw [find_axiom_def, st_ex_bind_def, raise_Fail_def, st_ex_return_def,
         case_eq_thms, axioms_def, get_the_axioms_def, bool_case_eq]
  \\ PURE_CASE_TAC \\ fs []
QED

Theorem pop_not_clash[simp]:
  pop x y ≠ (Failure (Clash tm),refs)
Proof
  EVAL_TAC \\ rw[] \\ EVAL_TAC
QED

Theorem peek_not_clash[simp]:
  peek x y ≠ (Failure (Clash tm),refs)
Proof
  EVAL_TAC \\ rw [] \\ EVAL_TAC
QED

Theorem getNum_not_clash[simp]:
  getNum x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getVar_not_clash[simp]:
  getVar x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getTerm_not_clash[simp]:
  getTerm x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getThm_not_clash[simp]:
  getThm x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getType_not_clash[simp]:
  getType x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getName_not_clash[simp]:
  getName x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
  \\ fs [st_ex_return_def] \\ CASE_TAC \\ fs []
QED

Theorem getConst_not_clash[simp]:
  getConst x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getList_not_clash[simp]:
  getList x y ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `x` \\ EVAL_TAC
QED

Theorem getTypeOp_not_clash[simp]:
  getTypeOp a b ≠ (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ EVAL_TAC
QED

Theorem getPair_not_clash[simp]:
  getPair a b ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC
  \\ Cases_on `t` \\ EVAL_TAC \\ Cases_on `t'` \\ EVAL_TAC
QED

Theorem getCns_not_clash[simp]:
  getCns a b ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs []
QED

Theorem getNvs_not_clash[simp]:
  getNvs a b ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs []
QED

Theorem getTms_not_clash[simp]:
  getTms a b ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs []
QED

Theorem getTys_not_clash[simp]:
  getTys a b ≠ (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs []
QED

Theorem BETA_CONV_not_clash[simp]:
  BETA_CONV t s ≠ (Failure (Clash tm),r)
Proof
  rw [BETA_CONV_def, handle_Fail_def, st_ex_bind_def, raise_Fail_def]
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs []
QED

Theorem readLine_not_clash[simp]:
  ∀c. readLine s c refs ≠ (Failure (Clash tm),refs')
Proof
  Cases
  \\ simp [readLine_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
           handle_Clash_def, handle_Fail_def, ELIM_UNCURRY]
  \\ strip_tac
  \\ fs [case_eq_thms, map_not_clash_thm]
  \\ rveq \\ fs []
  \\ pop_assum mp_tac \\ fs []
  \\ rpt (PURE_CASE_TAC \\ fs [])
QED

Theorem readLines_not_clash[simp]:
  ∀s ls refs tm refs'. readLines s ls refs ≠ (Failure (Clash tm),refs')
Proof
  recInduct readLines_ind
  \\ strip_tac
  \\ Cases \\ simp []
  >- simp [readLines_def, st_ex_return_def]
  \\ strip_tac
  \\ simp [Once readLines_def]
  \\ rw [handle_Fail_def, st_ex_bind_def, raise_Fail_def]
  \\ fsrw_tac [SATISFY_ss, DNF_ss] [case_eq_thms]
QED

(* -------------------------------------------------------------------------
 * reader_init does not raise Clash
 * ------------------------------------------------------------------------- *)

Theorem mk_true_not_clash[simp]:
  mk_true () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_true_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_univ_not_clash[simp]:
  mk_univ ty refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_univ_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_forall_not_clash[simp]:
  mk_forall (v,p) refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_forall_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_eta_ax_not_clash[simp]:
  mk_eta_ax () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_eta_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_conj_const_not_clash[simp]:
  mk_conj_const () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_conj_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_conj_not_clash[simp]:
  mk_conj (p,q) refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_conj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_imp_const_not_clash[simp]:
  mk_imp_const () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_imp_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_imp_not_clash[simp]:
  mk_imp (p,q) refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_imp_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_select_ax_not_clash[simp]:
  mk_select_ax () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_select_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_ex_not_clash[simp]:
  mk_ex ty refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_ex_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_exists_not_clash[simp]:
  mk_exists (v,p) refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_exists_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_surj_not_clash[simp]:
  mk_surj f a b refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_surj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_inj_not_clash[simp]:
  mk_inj f a refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_inj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_false_not_clash[simp]:
  mk_false () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_false_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_neg_const_not_clash[simp]:
  mk_neg_const () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_neg_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_neg_not_clash[simp]:
  mk_neg p refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_neg_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_infinity_ax_not_clash[simp]:
  mk_infinity_ax () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [mk_infinity_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem init_reader_not_clash[simp]:
  init_reader () refs ≠ (Failure (Clash tm), refs')
Proof
  rw [init_reader_def, st_ex_bind_def, st_ex_return_def, case_eq_thms,
      select_sym_def, ind_type_def]
QED

(* -------------------------------------------------------------------------
 * Refinement invariants
 * ------------------------------------------------------------------------- *)

(* Refinement invariant for objects *)
Definition OBJ_def:
  (OBJ defs (List xs)     ⇔ EVERY (OBJ defs) xs) ∧
  (OBJ defs (Type ty)     ⇔ TYPE defs ty) ∧
  (OBJ defs (Var (n, ty)) ⇔ TERM defs (Var n ty) ∧ TYPE defs ty) ∧
  (OBJ defs (Term tm)     ⇔ TERM defs tm) ∧
  (OBJ defs (Thm th)      ⇔ THM defs th) ∧
  (OBJ defs _             ⇔ T)
Termination
  WF_REL_TAC ‘measure (object_size o SND)’
  \\ Induct \\ rw [object_size_def]
  \\ res_tac \\ fs []
End

Theorem OBJ_APPEND_EXTEND:
  ∀defs obj d.
    STATE (ds ++ defs) refs ∧
    (∀th. THM defs th ⇒ THM (ds ++ defs) th) ∧
    OBJ defs obj ⇒
      OBJ (ds ++ defs) obj
Proof
  recInduct OBJ_ind
  \\ srw_tac [SATISFY_ss]
   [OBJ_def, EVERY_MEM, TERM_APPEND_EXTEND, TYPE_APPEND_EXTEND]
QED

Definition READER_STATE_def:
  READER_STATE defs st ⇔
    EVERY (THM defs) st.thms ∧
    EVERY (OBJ defs) st.stack ∧
    (∀n obj.
       lookup (Num n) st.dict = SOME obj ⇒
         OBJ defs obj)
End

Theorem READER_STATE_EXTEND:
  READER_STATE defs st ∧
  THM defs th ⇒
    READER_STATE defs (st with thms := th::st.thms)
Proof
   rw [READER_STATE_def]
QED

Theorem READER_STATE_APPEND_EXTEND:
  STATE (ds ++ defs) refs ∧
  READER_STATE defs st ∧
  (∀th. THM defs th ⇒ THM (ds ++ defs) th) ⇒
    READER_STATE (ds ++ defs) st
Proof
  srw_tac [SATISFY_ss]
   [READER_STATE_def, OBJ_APPEND_EXTEND, EVERY_MEM]
QED

Theorem READER_STATE_CONS_EXTEND =
  READER_STATE_APPEND_EXTEND
  |> Q.INST [`ds`|->`[d]`]
  |> SIMP_RULE list_ss [];

(* -------------------------------------------------------------------------
 * Kernel function support theorems (TODO: move)
 * ------------------------------------------------------------------------- *)

Theorem first_EVERY:
  ∀Q xs x. EVERY P xs ∧ first Q xs = SOME x ⇒ P x
Proof
  recInduct first_ind \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [first_def]
  \\ rw [case_eq_thms, PULL_EXISTS, bool_case_eq] \\ fs []
QED

(* TODO move to holKernelProof *)
Theorem axioms_thm:
  axioms () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀axs. res = Success axs ⇒ EVERY (THM defs) axs
Proof
  rw [axioms_def, get_the_axioms_def, STATE_def]
  \\ fs [EVERY_MAP, lift_tm_def, CONTEXT_def, EVERY_MEM, MEM_MAP] \\ rw []
  \\ fs [THM_def]
  \\ (FIRST o map irule o rev o CONJUNCTS) proves_rules
  \\ fsrw_tac [SATISFY_ss, DNF_ss]
    [extends_theory_ok, init_theory_ok, MEM_FLAT, MEM_MAP]
QED

Theorem find_axiom_thm:
  find_axiom (ls, tm) refs = (res, refs') ∧
  STATE defs refs ∧
  EVERY (TERM defs) ls ∧
  TERM defs tm ⇒
    refs = refs' ∧
    ∀thm. res = Success thm ⇒ THM defs thm
Proof
  rw [find_axiom_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
      case_eq_thms, PULL_EXISTS]
  \\ dxrule_all axioms_thm \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rveq
  \\ dxrule_all first_EVERY \\ rw []
QED

Theorem assoc_thm:
  ∀l s refs res refs'.
    assoc s l refs = (res, refs') ⇒
      refs = refs' ∧
      ∀t. res = Success t ⇒ ALOOKUP l s = SOME t
Proof
  Induct
  \\ simp [Once assoc_def, FORALL_PROD, raise_Fail_def, st_ex_return_def]
  \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem assoc_state_thm:
  ∀l s refs res refs'.
    assoc s l refs = (res, refs') ⇒
      refs = refs'
Proof
  srw_tac [SATISFY_ss] [assoc_thm]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem assoc_ty_thm:
  ∀l s refs res refs'.
    assoc s l refs = (res, refs') ∧
    EVERY (TYPE defs o SND) l ⇒
      ∀ty. res = Success ty ⇒ TYPE defs ty
Proof
  Induct
  \\ simp [Once assoc_def, FORALL_PROD, raise_Fail_def, st_ex_return_def]
  \\ rw []
  \\ pop_assum mp_tac
  \\ rw [Once assoc_def]
  \\ fsrw_tac [SATISFY_ss] [bool_case_eq, COND_RATOR, st_ex_return_def]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem type_of_thm:
  ∀tm refs res refs'.
    type_of tm refs = (res, refs') ∧
    STATE defs refs ∧
    TERM defs tm ⇒
      refs = refs' ∧
      ∀ty. res = Success ty ⇒ TYPE defs ty ∧ welltyped tm
Proof
  Induct
  \\ rpt gen_tac
  \\ strip_tac
  \\ qhdtm_x_assum `type_of` mp_tac
  \\ simp [Once type_of_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def,
           dest_type_def]
  \\ fs [TERM_def, TYPE_def, type_ok_def, term_ok_def]
  \\ rw [] \\ fs []
  \\ fs [case_eq_thms, type_ok_def, mk_fun_ty_def, mk_type_def, st_ex_bind_def,
         st_ex_return_def, raise_Fail_def, try_def, otherwise_def,
         get_type_arity_def, get_the_type_constants_def]
  \\ every_case_tac \\ fs [] \\ rveq
  \\ first_x_assum drule_all \\ rw []
  \\ fs [type_ok_def]
  \\ drule_all assoc_thm \\ rw []
  \\ rfs [STATE_def, CONTEXT_def]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem mk_comb_thm:
  mk_comb (f, a) refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs f ∧
  TERM defs a ⇒
    refs = refs' ∧
    ∀fa. res = Success fa ⇒ TERM defs fa
Proof
  simp [mk_comb_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ rw [] \\ fs []
  \\ imp_res_tac type_of_thm
  \\ imp_res_tac type_of_has_type
  \\ fs [TERM_def, TYPE_def, type_ok_def, term_ok_def]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem get_const_type_thm:
  get_const_type n refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀ty. res = Success ty ⇒ TYPE defs ty
Proof
  rw [get_const_type_def, st_ex_bind_def, st_ex_return_def,
      get_the_term_constants_def]
  \\ imp_res_tac the_term_constants_TYPE
  \\ fs [ELIM_UNCURRY, GSYM o_DEF]
  \\ drule_all assoc_state_thm \\ rw []
  \\ drule assoc_ty_thm
  \\ disch_then drule \\ simp []
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem tymatch_thm:
  ∀tys1 tys2 sids.
    tymatch tys1 tys2 sids = SOME (tys, _) ∧
    EVERY (TYPE defs) tys1 ∧
    EVERY (TYPE defs) tys2 ∧
    EVERY (λ(t1,t2). TYPE defs t1 ∧ TYPE defs t2) (FST sids) ⇒
      EVERY (λ(t1,t2). TYPE defs t1 ∧ TYPE defs t2) tys
Proof
  recInduct tymatch_ind
  \\ simp [FORALL_PROD] \\ rw []
  \\ qhdtm_x_assum `tymatch` mp_tac
  \\ rw [Once tymatch_def] \\ fs []
  \\ pop_assum irule
  \\ fsrw_tac [SATISFY_ss] [TYPE_def, type_ok_def, EVERY_MEM]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem match_type_thm:
  match_type ty1 ty2 = SOME tys ∧
  TYPE defs ty1 ∧
  TYPE defs ty2 ⇒
    EVERY (λ(t1,t2). TYPE defs t1 ∧ TYPE defs t2) tys
Proof
  rw [holSyntaxExtraTheory.match_type_def]
  \\ PairCases_on ‘z’ \\ fs []
  \\ imp_res_tac tymatch_thm \\ rfs []
QED

(* TODO proven elsewhere *)
Theorem TERM_Comb:
  TERM defs (Comb a b) ⇒
    TERM defs a ∧
    TERM defs b
Proof
  rw [TERM_def, term_ok_def]
QED

Theorem TERM_Abs:
  TERM defs (Abs v e) ⇒
    TERM defs v ∧
    TERM defs e
Proof
  rw [TERM_def] \\ fs [term_ok_def]
QED

(* ------------------------------------------------------------------------- *)
(* Reader operations preserve invariants                                     *)
(* ------------------------------------------------------------------------- *)

Theorem next_line_thm:
  READER_STATE defs s ⇒
    READER_STATE defs (next_line s)
Proof
  rw [READER_STATE_def, next_line_def]
QED

Theorem getNum_thm:
  getNum obj refs = (res, refs') ⇒
    refs = refs'
Proof
  Cases_on ‘obj’
  \\ rw [getNum_def, raise_Fail_def, st_ex_return_def]
  \\ fs []
QED

Theorem getName_thm:
  getName obj refs = (res, refs') ⇒
    refs = refs'
Proof
  Cases_on ‘obj’
  \\ rw [getName_def, raise_Fail_def, st_ex_return_def]
  \\ fs []
QED

Theorem getList_thm:
  getList obj refs = (res, refs') ∧
  OBJ defs obj ⇒
    refs = refs' ∧
    ∀ls. res = Success ls ⇒ EVERY (OBJ defs) ls
Proof
  Cases_on ‘obj’
  \\ rw [getList_def, raise_Fail_def, st_ex_return_def, OBJ_def]
  \\ fsrw_tac [ETA_ss] [OBJ_def]
QED

Theorem getTypeOp_thm:
  getTypeOp obj refs = (res, refs') ⇒
    refs = refs'
Proof
  Cases_on ‘obj’
  \\ rw [getTypeOp_def, raise_Fail_def, st_ex_return_def]
  \\ fs []
QED

Theorem getType_thm:
  getType obj refs = (res, refs') ∧
  OBJ defs obj ⇒
    refs = refs' ∧
    ∀ty. res = Success ty ⇒ TYPE defs ty
Proof
  Cases_on ‘obj’
  \\ rw [getType_def, raise_Fail_def, st_ex_return_def]
  \\ fs [OBJ_def]
QED

Theorem map_getType_thm:
  ∀xs refs res refs'.
    map getType xs refs = (res, refs') ∧
    EVERY (OBJ defs) xs ⇒
      refs = refs' ∧
      ∀tys. res = Success tys ⇒ EVERY (TYPE defs) tys
Proof
  Induct
  \\ rw [Once map_def, st_ex_return_def, st_ex_bind_def]
  \\ fs [case_eq_thms] \\ rveq
  \\ drule_all getType_thm \\ rw []
  \\ first_x_assum drule_all \\ rw []
QED

Theorem getConst_thm:
  getConst obj refs = (res, refs') ⇒
    refs = refs'
Proof
  Cases_on ‘obj’
  \\ rw [getConst_def, raise_Fail_def, st_ex_return_def]
  \\ fs []
QED

Theorem getVar_thm:
  getVar obj refs = (res, refs') ∧
  OBJ defs obj ⇒
    refs = refs' ∧
    ∀n ty.
      res = Success (n, ty) ⇒
        TERM defs (Var n ty) ∧
        TYPE defs ty
Proof
  Cases_on ‘obj’
  \\ rw [getVar_def, raise_Fail_def, st_ex_return_def]
  \\ fs [OBJ_def]
QED

Theorem getTerm_thm:
  getTerm obj refs = (res, refs') ∧
  OBJ defs obj ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  Cases_on ‘obj’
  \\ rw [getTerm_def, raise_Fail_def, st_ex_return_def] \\ fs []
  \\ fs [OBJ_def]
QED

Theorem map_getTerm_thm:
  ∀xs refs res refs'.
    map getTerm xs refs = (res, refs') ∧
    EVERY (OBJ defs) xs ⇒
      refs = refs' ∧
      ∀tms. res = Success tms ⇒ EVERY (TERM defs) tms
Proof
  Induct
  \\ rw [Once map_def, st_ex_return_def, st_ex_bind_def, case_eq_thms]
  \\ fs []
  \\ drule_all getTerm_thm \\ rw []
  \\ first_x_assum drule_all \\ rw []
QED

Theorem getThm_thm:
  getThm obj refs = (res, refs') ∧
  OBJ defs obj ⇒
    refs = refs' ∧
    ∀thm. res = Success thm ⇒ THM defs thm
Proof
  Cases_on ‘obj’
  \\ rw [getThm_def, raise_Fail_def, st_ex_return_def]
  \\ fs [OBJ_def]
QED

Theorem pop_thm:
  pop st refs = (res, refs') ∧
  READER_STATE defs st ⇒
    refs = refs' ∧
    ∀a st'.
      res = Success (a, st') ⇒
        OBJ defs a ∧
        READER_STATE defs st'
Proof
  rw [pop_def, raise_Fail_def, st_ex_return_def]
  \\ Cases_on `st.stack`
  \\ fsrw_tac [SATISFY_ss] [READER_STATE_def, state_component_equality]
  \\ rfs []
QED

Theorem peek_thm:
  peek st refs = (res, refs') ∧
  READER_STATE defs st ⇒
    refs = refs' ∧
    ∀obj. res = Success obj ⇒ OBJ defs obj
Proof
  rw [peek_def, raise_Fail_def, st_ex_return_def]
  \\ Cases_on `st.stack`
  \\ fs [READER_STATE_def]
  \\ rw []
QED

Theorem push_thm:
  READER_STATE defs st ∧
  OBJ defs obj ⇒
    READER_STATE defs (push obj st)
Proof
  rw [push_def, READER_STATE_def]
QED

Theorem push_push_thm:
  READER_STATE defs st ∧
  OBJ defs obj1 ∧
  OBJ defs obj2 ⇒
    READER_STATE defs (push obj1 (push obj2 st))
Proof
  rw [push_def, READER_STATE_def]
QED

Theorem insert_dict_thm:
  READER_STATE defs st ∧
  OBJ defs obj ⇒
    READER_STATE defs (insert_dict (Num n) obj st)
Proof
  rw [insert_dict_def, READER_STATE_def, lookup_insert]
  \\ pop_assum mp_tac
  \\ IF_CASES_TAC \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem delete_dict_thm:
  READER_STATE defs st ⇒
    READER_STATE defs (delete_dict (Num n) st)
Proof
  rw [delete_dict_def, READER_STATE_def, lookup_delete]
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem getPair_thm:
  ∀obj refs res refs'.
    getPair obj refs = (res, refs') ∧
    OBJ defs obj ⇒
      refs = refs' ∧
      ∀a b.
        res = Success (a, b) ⇒
          OBJ defs a ∧
          OBJ defs b
Proof
  ho_match_mp_tac getPair_ind
  \\ simp [getPair_def, raise_Fail_def, st_ex_return_def, OBJ_def]
QED

(* TODO
 * The original theorem takes ‘defs’ in a very special shape;
 * replace by this.
 *)

Theorem mk_vartype_thm:
  STATE defs refs ⇒
    TYPE defs (mk_vartype nm)
Proof
  rw [TYPE_def, mk_vartype_def, type_ok_def]
QED

Theorem getTys_thm:
  ∀obj refs res refs'.
    getTys obj refs = (res, refs') ∧
    STATE defs refs ∧
    OBJ defs obj ⇒
      refs = refs' ∧
      ∀t ty.
        res = Success (t, ty) ⇒
          TYPE defs t ∧
          TYPE defs ty
Proof
  ho_match_mp_tac getPair_ind
  \\ simp [getPair_def, raise_Fail_def, st_ex_return_def, OBJ_def,
           getTys_def, st_ex_bind_def, case_eq_thms]
  \\ rw []
  \\ drule_all getName_thm \\ rw []
  \\ drule_all getType_thm \\ rw []
  \\ irule mk_vartype_thm
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem map_getTys_thm:
  ∀xs refs res refs'.
    map getTys xs refs = (res, refs') ∧
    STATE defs refs ∧
    EVERY (OBJ defs) xs ⇒
      refs = refs' ∧
      ∀tys.
        res = Success tys ⇒
        EVERY (λ(ty1,ty2). TYPE defs ty1 ∧ TYPE defs ty2) tys
Proof
  Induct \\ rw []
  \\ qhdtm_x_assum `map` mp_tac
  \\ rw [Once map_def, st_ex_bind_def, st_ex_return_def] \\ fs []
  \\ fs [case_eq_thms] \\ rw []
  \\ drule_all getTys_thm \\ rw []
  \\ fs [quantHeuristicsTheory.PAIR_EQ_EXPAND, UNCURRY]
  \\ first_x_assum drule_all \\ rw []
QED

Theorem getTms_thm:
  ∀obj refs res refs'.
    getTms obj refs = (res, refs') ∧
    STATE defs refs ∧
    OBJ defs obj ⇒
      refs = refs' ∧
      ∀tm var.
        res = Success (tm, var) ⇒
          TERM defs tm ∧
          TERM defs var
Proof
  Cases
  \\ simp [getTms_def, LAMBDA_PROD, st_ex_return_def, st_ex_bind_def,
           raise_Fail_def, getPair_def, case_eq_thms, EXISTS_PROD]
  \\ rw []
  \\ drule_all getPair_thm \\ rw []
  \\ drule_all getVar_thm \\ rw []
  \\ drule_all getTerm_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm]
QED

Theorem map_getTms_thm:
  ∀xs refs res refs'.
    map getTms xs refs = (res, refs') ∧
    STATE defs refs ∧
    EVERY (OBJ defs) xs ⇒
      refs = refs' ∧
      ∀tmvs.
        res = Success tmvs ⇒
          EVERY (λ(tm1,tm2). TERM defs tm1 ∧ TERM defs tm2) tmvs
Proof
  Induct \\ rw []
  \\ qhdtm_x_assum `map` mp_tac
  \\ simp [Once map_def, LAMBDA_PROD, st_ex_bind_def, st_ex_return_def,
           case_eq_thms, EXISTS_PROD]
  \\ rw []
  \\ drule_all getTms_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem getNvs_thm:
  getNvs obj refs = (res, refs') ∧
  STATE defs refs ∧
  OBJ defs obj ⇒
    refs = refs' ∧
    ∀tm1 tm2.
      res = Success (tm1, tm2) ⇒
        TERM defs tm1 ∧
        TERM defs tm2
Proof
  Cases_on ‘obj’
  \\ simp [getNvs_def, LAMBDA_PROD, st_ex_bind_def, st_ex_return_def,
           raise_Fail_def, getPair_def, case_eq_thms, EXISTS_PROD]
  \\ rw []
  \\ drule_all getPair_thm \\ rw []
  \\ drule_all getName_thm \\ rw []
  \\ drule_all getVar_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm]
QED

Theorem map_getNvs_thm:
  ∀xs refs res refs'.
    map getNvs xs refs = (res, refs') ∧
    STATE defs refs ∧
    EVERY (OBJ defs) xs ⇒
      refs = refs' ∧
      ∀ts.
        res = Success ts ⇒
          EVERY (λ(t1,t2). TERM defs t1 ∧ TERM defs t2) ts
Proof
  Induct
  \\ simp [Once map_def, LAMBDA_PROD, st_ex_return_def, st_ex_bind_def,
           case_eq_thms, EXISTS_PROD]
  \\ rw []
  \\ drule_all getNvs_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem getCns_thm:
  getCns (tm, _) refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs tm ⇒
    refs = refs' ∧
    ∀a. res = Success a ⇒ OBJ defs a
Proof
  rw [getCns_def, st_ex_bind_def, st_ex_return_def, UNCURRY, case_eq_thms]
  \\ fsrw_tac [SATISFY_ss] [dest_var_thm, OBJ_def]
QED

Theorem map_getCns_thm:
  ∀xs refs res refs'.
    map getCns xs refs = (res, refs') ∧
    STATE defs refs ∧
    EVERY (TERM defs o FST) xs ⇒
      refs = refs' ∧
      ∀xs. res = Success xs ⇒ EVERY (OBJ defs) xs
Proof
  Induct
  \\ simp [Once map_def, LAMBDA_PROD, st_ex_return_def, st_ex_bind_def,
           case_eq_thms, FORALL_PROD]
  \\ rw []
  \\ drule_all getCns_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
QED

(* TODO Fix in holKernelProofTheory *)
Theorem BETA_thm:
  BETA tm s = (res, s') ∧
  STATE defs s ∧
  TERM defs tm ⇒
    s' = s ∧
    ∀th. res = Success th ⇒ THM defs th
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [BETA_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem INST_thm:
  INST theta th1 s = (res, s') ∧
  STATE defs s ∧
  EVERY (λ(t1, t2). TERM defs t1 ∧ TERM defs t2) theta ∧
  THM defs th1 ⇒
    s' = s ∧
    ∀th. res = Success th ⇒ THM defs th
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [INST_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem mk_abs_thm:
  mk_abs (bvar, bod) s = (res, s1) ∧
  TERM defs bvar ∧
  TERM defs bod ⇒
    s1 = s ∧
    ∀t.
      res = Success t ⇒
        TERM defs t ∧
        t = Abs bvar bod
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [mk_abs_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem ABS_thm:
  ABS tm th1 s = (res, s') ∧
  TERM defs tm ∧
  THM defs th1 ∧
  STATE defs s ⇒
    s' = s ∧
    ∀th. res = Success th ⇒ THM defs th
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [ABS_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem ASSUME_thm:
  ASSUME tm s = (res, s') ∧
  TERM defs tm ∧
  STATE defs s ⇒
    s' = s ∧
    ∀th. res = Success th ⇒ THM defs th
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [ASSUME_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem mk_const_thm:
  ∀name theta s z s'.
    mk_const (name, theta) s = (z, s') ∧
    STATE defs s ∧
    EVERY (λ(t1, t2). TYPE defs t1 ∧ TYPE defs t2) theta ⇒
      s' = s ∧
      ∀tm. z = Success tm ⇒ TERM defs tm
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [mk_const_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem mk_eq_thm:
  mk_eq (x, y) s = (res, s') ∧
  TERM defs x ∧
  TERM defs y ∧
  STATE defs s ⇒
    s' = s ∧
    (∀t. res = Failure t ⇒ term_type x ≠ term_type y) ∧
    ∀t.
      res = Success t ⇒
        t = Comb (Comb (Equal (term_type x)) x) y ∧
        TERM defs t
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [mk_eq_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem dest_eq_thm:
  dest_eq tm s = (res, s') ∧
  TERM defs tm ∧
  STATE defs s ⇒
    s' = s ∧
    ∀t1 t2.
      res = Success (t1, t2) ⇒
        TERM defs t1 ∧
        TERM defs t2 ∧
        tm = Comb (Comb (Equal (typeof t1)) t1) t2
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [dest_eq_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem dest_comb_thm:
  dest_comb v s = (res, s') ∧
  TERM defs v ∧
  STATE defs s ⇒
    s' = s ∧
    ∀x y.
      res = Success (x, y) ⇒
        TERM defs x ∧
        TERM defs y
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [dest_comb_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem SYM_thm:
  SYM th s = (res, s') ∧
  THM defs th ∧
  STATE defs s ⇒
    s' = s ∧
    ∀th. res = Success th ⇒ THM defs th
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [SYM_thm]
QED

(* TODO Fix in holKernelProofTheory *)
Theorem mk_type_thm:
  mk_type (tyop,args) s = (z, s') ∧
  EVERY (TYPE defs) args ∧
  STATE defs s ⇒
    s' = s ∧
    (tyop = «fun» ∧ LENGTH args = 2 ⇒ ∃i. z = Success i) ∧
    ∀i.
      z = Success i ⇒
        TYPE defs i ∧
        i = Tyapp tyop args
Proof
  rw []
  \\ fsrw_tac [SATISFY_ss] [mk_type_thm]
QED

Theorem BETA_CONV_thm:
  ∀tm refs res refs'.
    BETA_CONV tm refs = (res, refs') ∧
    STATE defs refs ∧
    TERM defs tm ⇒
      refs = refs' ∧
      ∀thm. res = Success thm ⇒ THM defs thm
Proof
  Cases
  \\ simp [BETA_CONV_def, LAMBDA_PROD, handle_Fail_def, raise_Fail_def,
           st_ex_bind_def, st_ex_return_def, case_eq_thms, dest_comb_def,
           dest_abs_def, EXISTS_PROD]
  \\ rw []
  \\ dxrule_then drule_all BETA_thm \\ rw []
  \\ Cases_on `t` \\ fs [] \\ rveq
  \\ drule TERM_Comb \\ rw []
  \\ drule TERM_Abs \\ rw []
  \\ drule_all mk_comb_thm \\ rw []
  \\ drule_all BETA_thm \\ rw []
  \\ drule INST_thm \\ simp []
  \\ disch_then drule \\ rw []
QED

(* ------------------------------------------------------------------------- *)
(* Reader preserves invariants                                               *)
(* ------------------------------------------------------------------------- *)

Theorem PROP_APPEND_EXISTS[local] =
  METIS_PROVE [APPEND] “P x y ⇒ ∃z. P (z ++ x) y”

Theorem PROP_APPEND_EXISTS2[local] =
  METIS_PROVE [APPEND] “P x y ∧ Q x w ⇒ ∃z. P (z ++ x) y ∧ Q (z ++ x) w”

fun fsp ths =
  fsrw_tac [SATISFY_ss]
           (PROP_APPEND_EXISTS::
            PROP_APPEND_EXISTS2::ths);

Theorem readLine_thm:
  readLine st cmd refs = (res, refs') ∧
  STATE defs refs ∧
  READER_STATE defs st ⇒
    ∃ds.
      STATE (ds ++ defs) refs' ∧
      ∀st'. res = Success st' ⇒ READER_STATE (ds ++ defs) st'
Proof
  simp [readLine_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
        LAMBDA_PROD, EXISTS_PROD, FORALL_PROD]
  \\ Cases_on ‘cmd = version’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getNum_thm \\ rw [] \\ fsp [])
  \\ Cases_on ‘cmd = absTerm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getVar_thm \\ rw [] \\ fsp []
    \\ dxrule_then (qspec_then `defs` mp_tac) mk_abs_thm
    \\ imp_res_tac mk_var_thm \\ fsp [] \\ rw []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = absThm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getVar_thm \\ rw [] \\ fsp []
    \\ drule_then (qspec_then `defs` mp_tac) ABS_thm
    \\ imp_res_tac mk_var_thm \\ fsp [] \\ rw []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = appTerm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all mk_comb_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = appThm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all MK_COMB_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = assume’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all ASSUME_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = axiom’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getList_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all map_getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all find_axiom_thm \\ rw [] \\ fsp []
    \\ fsp [OBJ_def, push_thm])
  \\ Cases_on ‘cmd = betaConv’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all BETA_CONV_thm \\ rw [] \\ fsp []
    \\ fsp [OBJ_def, push_thm])
  \\ Cases_on `cmd = cons` \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getList_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ qexists_tac ‘[]’ \\ simp []
    \\ irule push_thm
    \\ fsrw_tac [ETA_ss] [OBJ_def])
  \\ Cases_on ‘cmd = const’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = constTerm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ TRY FULL_CASE_TAC \\ fs []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getType_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getConst_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all get_const_type_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all match_type_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all mk_const_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = deductAntisym’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ drule_then drule_all DEDUCT_ANTISYM_RULE_thm \\ rw [] \\ fsp []
    \\ fsp [OBJ_def, push_thm])
  \\ Cases_on ‘cmd = def’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ Cases_on `n < 0` \\ fs []
    \\ dxrule_all getNum_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all peek_thm \\ rw [] \\ fsp []
    \\ fsp [insert_dict_thm, OBJ_def])
  \\ Cases_on ‘cmd = defineConst’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ drule_all type_of_thm \\ rw [] \\ fsp []
    \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_eq_thm \\ fsp [mk_var_thm]
    \\ rw []
    \\ drule_all new_basic_definition_thm \\ rw [] \\ fsp []
    \\ qexists_tac ‘[d]’ \\ simp []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule READER_STATE_CONS_EXTEND \\ fsp [])
  \\ Cases_on ‘cmd = defineConstList’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getList_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all map_getNvs_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all INST_thm \\ rw [] \\ fsp []
    \\ drule_all new_specification_thm \\ rw [] \\ fsp []
    \\ dxrule_then (qspec_then `d::defs` mp_tac) map_getCns_thm \\ fsp []
    \\ fsrw_tac [SATISFY_ss, DNF_ss]
        [EVERY_MEM, LAMBDA_PROD, FORALL_PROD, TERM_CONS_EXTEND]
    \\ rw []
    \\ qexists_tac ‘[d]’ \\ fs []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fsrw_tac [ETA_ss] [OBJ_def, EVERY_MEM]
    \\ irule READER_STATE_CONS_EXTEND \\ fsp [])
  \\ Cases_on ‘cmd = defineTypeOp’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getList_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ drule_all new_basic_type_definition_thm
    \\ disch_then (qspecl_then [‘nm’, ‘rep’, ‘abs’] mp_tac) \\ rw [] \\ fsp []
    \\ last_assum (mp_then Any dxrule dest_eq_thm)
    \\ imp_res_tac concl_thm \\ rw [] \\ fsp []
    \\ last_x_assum (mp_then Any dxrule ABS_thm) \\ rw [] \\ fsp []
    \\ dxrule_then drule_all SYM_thm \\ rw [] \\ fsp []
    \\ dxrule_then (qspec_then ‘ds ++ defs’ mp_tac) dest_eq_thm \\ rw []
    \\ fsp []
    \\ dxrule_then drule_all dest_comb_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all ABS_thm \\ rw [] \\ fs []
    \\ qexists_tac ‘ds’ \\ simp []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule READER_STATE_APPEND_EXTEND \\ fsp [])
  \\ Cases_on ‘cmd = eqMp’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ drule_all EQ_MP_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, READER_STATE_APPEND_EXTEND, OBJ_def])
  \\ Cases_on ‘cmd = hdTl’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getList_thm \\ rw [] \\ fsp []
    \\ Cases_on ‘ls’ \\ fs []
    \\ rveq \\ fsp []
    \\ qexists_tac ‘[]’ \\ simp []
    \\ irule push_thm \\ fsrw_tac [ETA_ss] [OBJ_def]
    \\ irule push_thm \\ fsrw_tac [ETA_ss] [OBJ_def])
  \\ Cases_on ‘cmd = nil’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = opType’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getList_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all map_getType_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getTypeOp_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all mk_type_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def, READER_STATE_APPEND_EXTEND])
  \\ Cases_on ‘cmd = popc’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp [])
  \\ Cases_on ‘cmd = pragma’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD, handle_Fail_def]
    \\ fs [bool_case_eq, COND_RATOR] \\ rveq
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp [])
  \\ Cases_on ‘cmd = proveHyp’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all getThm_thm \\ rw [] \\ fsp []
    \\ drule_all PROVE_HYP_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = ref’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ every_case_tac \\ fs [] \\ rveq
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getNum_thm \\ rw [] \\ fsp []
    \\ qexists_tac ‘[]’ \\ simp []
    \\ irule push_thm
    \\ fsrw_tac [SATISFY_ss] [EVERY_MEM, READER_STATE_def])
  \\ Cases_on ‘cmd = refl’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getTerm_thm \\ rw [] \\ fsp []
    \\ drule_all REFL_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = remove’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ every_case_tac \\ fs [] \\ rveq
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getNum_thm \\ rw [] \\ fsp []
    \\ qexists_tac ‘[]’ \\ simp []
    \\ DEP_REWRITE_TAC [push_thm, delete_dict_thm]
    \\ fsrw_tac [SATISFY_ss] [EVERY_MEM, READER_STATE_def])
  \\ Cases_on ‘cmd = subst’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD, handle_Clash_def]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getPair_thm \\ rw [] \\ fsp []
    \\ dxrule_all getList_thm \\ rw [] \\ fsp []
    \\ TRY (dxrule_all getList_thm) \\ rw [] \\ fsp []
    \\ dxrule_then drule_all map_getTys_thm \\ rw [] \\ fsp []
    \\ drule_all INST_TYPE_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all map_getTms_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all INST_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = sym’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all SYM_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = thm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getList_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all map_getTerm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getThm_thm \\ rw [] \\ fsp []
    \\ drule_all ALPHA_THM_thm \\ rw [] \\ fsp []
    \\ fsp [READER_STATE_def])
  \\ Cases_on ‘cmd = trans’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getThm_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getThm_thm \\ rw [] \\ fsp []
    \\ drule_all TRANS_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = typeOp’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def])
  \\ Cases_on ‘cmd = var’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getType_thm \\ rw [] \\ fsp []
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def, TERM_def, TYPE_def, term_ok_def])
  \\ Cases_on ‘cmd = varTerm’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getVar_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def, mk_var_thm, TERM_def, TYPE_def, term_ok_def])
  \\ Cases_on ‘cmd = varType’ \\ simp []
  >-
   (rw [case_eq_thms, LAMBDA_PROD, EXISTS_PROD]
    \\ dxrule_then drule_all pop_thm \\ rw [] \\ fsp []
    \\ dxrule_all getName_thm \\ rw [] \\ fsp []
    \\ fsp [push_thm, OBJ_def, mk_vartype_thm, TERM_def, TYPE_def, term_ok_def])
  \\ Cases_on ‘cmd’ \\ fs []
  \\ rw []
  \\ fsp [OBJ_def, push_thm]
QED

Theorem readLines_thm:
   ∀st lines res refs refs' defs.
     readLines st lines refs = (res, refs') ∧
     STATE defs refs ∧
     READER_STATE defs st ⇒
     ∃ds.
       STATE (ds ++ defs) refs' ∧
       ∀st' n. res = Success (st', n) ⇒ READER_STATE (ds ++ defs) st'
Proof
  recInduct readLines_ind
  \\ gen_tac \\ Cases \\ rw []
  \\ qhdtm_x_assum `readLines` mp_tac
  \\ rw [Once readLines_def, st_ex_return_def, st_ex_bind_def, handle_Fail_def,
         case_eq_thms, raise_Fail_def]
  \\ fsp [next_line_thm]
  \\ drule_all readLine_thm
  \\ rw [] \\ fs []
  \\ first_x_assum (drule_then (qspec_then ‘ds ++ defs’ mp_tac)) \\ simp []
  \\ impl_tac
  >- fsrw_tac [SATISFY_ss] [next_line_def, READER_STATE_def]
  \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* Axiom cooking                                                             *)
(* ------------------------------------------------------------------------- *)

Theorem STATE_lemma:
  STATE defs refs ⇒
    (∀a b. TYPE defs a ∧ TYPE defs b ⇒ TYPE defs (Fun a b)) ∧
    TYPE defs Bool
Proof
  simp [STATE_def, CONTEXT_def]
  \\ strip_tac
  \\ sg `theory_ok (thyof refs.the_context)`
  >- metis_tac [init_theory_ok, extends_theory_ok]
  \\ fs [theory_ok_def, is_std_sig_def]
  \\ rw [TYPE_def, type_ok_def]
QED

Theorem mk_true_thm:
  mk_true () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_true_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ rw []
  \\ drule_then (qspec_then ‘defs’ mp_tac) mk_abs_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm]
  \\ rw []
  \\ drule_then (qspec_then ‘defs’ mp_tac) mk_eq_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm]
QED

Theorem mk_univ_thm:
  mk_univ ty refs = (res, refs') ∧
  STATE defs refs ∧
  TYPE defs ty ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_univ_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ rw []
  \\ dxrule_then drule_all mk_true_thm \\ rw [] \\ fs []
  \\ last_assum (mp_then Any dxrule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_eq_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_abs_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm]
QED

Theorem mk_forall_thm:
  mk_forall (t1, t2) refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs t2 ∧
  TERM defs t1 ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_forall_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ dxrule_then drule_all type_of_thm \\ rw [] \\ fs []
  \\ dxrule_then drule_all mk_univ_thm \\ rw [] \\ fs []
  \\ dxrule_then drule_all mk_abs_thm \\ rw [] \\ fs []
  \\ dxrule_then drule_all mk_comb_thm \\ rw [] \\ fs []
QED

Theorem mk_eta_ax_thm:
  mk_eta_ax () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_eta_ax_def, st_ex_bind_def, case_eq_thms, st_ex_return_def, mk_var_def]
  \\ drule STATE_lemma \\ rw []
  \\ qabbrev_tac ‘A = Tyvar «A»’
  \\ qabbrev_tac ‘B = Tyvar «B»’
  \\ ‘TYPE defs A ∧ TYPE defs B’
    by fs [TYPE_def, type_ok_def, Abbr ‘A’, Abbr ‘B’]
  \\ first_x_assum (qspecl_then [‘A’, ‘B’] mp_tac) \\ rw []
  \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_comb_thm
  \\ ‘TERM defs (Var «x» A) ∧ TERM defs (Var «t» (Fun A B))’
    by fs [TERM_def, TYPE_def, term_ok_def]
  \\ rw []
  \\ dxrule_then drule_all mk_abs_thm \\ rw []
  \\ dxrule_then drule_all mk_eq_thm \\ rw []
  \\ dxrule_then drule_all mk_forall_thm \\ rw []
QED

Theorem mk_conj_const_thm:
  mk_conj_const () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_conj_const_def, st_ex_bind_def, st_ex_return_def]
  \\ fs [case_eq_thms]
  \\ rveq \\ fs []
  \\ drule STATE_lemma \\ strip_tac
  \\ first_assum (qspecl_then [‘Bool’, ‘Bool’] mp_tac)
  \\ first_x_assum (qspecl_then [‘Bool’, ‘Fun Bool Bool’] mp_tac)
  \\ rw [] \\ fs []
  \\ dxrule_then drule_all mk_true_thm \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm) \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_eq_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_conj_thm:
  mk_conj (t1, t2) refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs t2 ∧
  TERM defs t1 ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_conj_def, st_ex_bind_def, case_eq_thms]
  \\ dxrule_then drule_all mk_conj_const_thm \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm) \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm) \\ rw []
QED

Theorem mk_imp_const_thm:
  mk_imp_const () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_imp_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_conj_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_eq_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ dxrule_then (qspec_then ‘defs’ mp_tac) mk_abs_thm
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_imp_thm:
  mk_imp (t1, t2) refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs t2 ∧
  TERM defs t1 ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_imp_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ dxrule_then drule_all mk_imp_const_thm \\ rw []
  \\ dxrule_then drule_all mk_comb_thm \\ rw []
  \\ dxrule_then drule_all mk_comb_thm \\ rw []
QED

Theorem mk_select_ax_thm:
  mk_select_ax () refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs select_const ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_select_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ qabbrev_tac ‘A = Tyvar «A»’
  \\ ‘TYPE defs A’
    by fs [Abbr ‘A’, TYPE_def, type_ok_def]
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ dxrule_then drule_all mk_imp_thm \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_ex_thm:
  mk_ex ty refs = (res, refs') ∧
  STATE defs refs ∧
  TYPE defs ty ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_ex_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_imp_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_imp_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_exists_thm:
  mk_exists (t1, t2) refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs t2 ∧
  TERM defs t1 ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_exists_def, st_ex_bind_def, case_eq_thms]
  \\ dxrule_then drule_all type_of_thm \\ rw []
  \\ dxrule_then drule_all mk_ex_thm \\ rw []
  \\ dxrule_then drule_all mk_abs_thm \\ rw []
  \\ dxrule_then drule_all mk_comb_thm \\ rw []
QED

Theorem mk_surj_thm:
  mk_surj f d c refs = (res, refs') ∧
  STATE defs refs ∧
  TYPE defs d ∧
  TYPE defs c ∧
  TERM defs f ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_surj_def, st_ex_bind_def, case_eq_thms, st_ex_return_def]
  \\ dxrule_then drule_all type_of_thm \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_assum (mp_then Any drule mk_eq_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_exists_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_inj_thm:
  mk_inj f d refs = (res, refs') ∧
  STATE defs refs ∧
  TYPE defs d ∧
  TERM defs f ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_inj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ dxrule_then drule_all type_of_thm \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_comb_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_eq_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_assum (mp_then Any dxrule mk_eq_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_imp_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_false_thm:
  mk_false () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_false_def, st_ex_bind_def, st_ex_return_def]
  \\ drule STATE_lemma \\ strip_tac
  \\ last_x_assum (mp_then Any drule mk_forall_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm]
QED

Theorem mk_neg_const_thm:
  mk_neg_const () refs = (res, refs') ∧
  STATE defs refs ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_neg_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ dxrule_then drule_all mk_false_thm \\ rw []
  \\ last_x_assum (mp_then Any drule mk_imp_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_abs_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem mk_neg_thm:
  mk_neg p refs = (res, refs') ∧
  STATE defs refs ∧
  TERM defs p ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_neg_def, st_ex_bind_def, case_eq_thms]
  \\ dxrule_then drule_all mk_neg_const_thm \\ rw []
  \\ dxrule_then drule_all mk_comb_thm \\ rw []
QED

Theorem mk_infinity_ax_thm:
  mk_infinity_ax () refs = (res, refs') ∧
  STATE defs refs ∧
  TYPE defs Ind ⇒
    refs = refs' ∧
    ∀tm. res = Success tm ⇒ TERM defs tm
Proof
  rw [mk_infinity_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ last_x_assum (mp_then Any drule mk_surj_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_inj_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_neg_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_conj_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
  \\ last_x_assum (mp_then Any drule mk_exists_thm)
  \\ fsrw_tac [SATISFY_ss] [mk_var_thm] \\ rw []
QED

Theorem init_reader_success:
  init_reader () init_refs = (res, refs) ⇒
    res = Success ()
Proof
  EVAL_TAC \\ fs []
QED

Theorem init_reader_ok:
  init_reader () init_refs = (res, refs) ⇒
    res = Success () ∧
    ∃defs. STATE defs refs
Proof
  simp_tac std_ss [init_reader_success]
  \\ sg ‘STATE init_refs.the_context init_refs’
  >- (EVAL_TAC \\ rw [])
  \\ rw [init_reader_def, st_ex_bind_def, ind_type_def, select_sym_def,
         st_ex_return_def]
  \\ fs [case_eq_thms] \\ rveq
  \\ qpat_x_assum ‘_ = mk_eta_ax _ _’ (assume_tac o SYM)
  \\ dxrule_then drule_all mk_eta_ax_thm
  \\ strip_tac \\ rveq \\ fs []
  \\ drule STATE_lemma \\ strip_tac
  \\ qabbrev_tac ‘A = Tyvar «A»’
  \\ ‘TYPE defs A’
    by fs [Abbr ‘A’, TYPE_def, type_ok_def]
  \\ fsrw_tac [SATISFY_ss] []
  \\ last_assum (mp_then Any drule new_axiom_thm) \\ rw []
  \\ qpat_x_assum ‘new_axiom ax init_refs = _’ kall_tac
  \\ ‘TYPE (d::init_refs.the_context) A’
    by fs [TYPE_def, type_ok_def, Abbr ‘A’]
  \\ drule STATE_lemma
  \\ strip_tac \\ fsrw_tac [SATISFY_ss] []
  \\ ‘TYPE (d::init_refs.the_context) (Fun (Fun A Bool) A)’
    by fsrw_tac [SATISFY_ss] []
  \\ drule_all_then (qspec_then ‘«@»’ mp_tac) new_constant_thm
  \\ srw_tac [SATISFY_ss] []
  \\ drule STATE_lemma
  \\ strip_tac \\ fsrw_tac [SATISFY_ss] []
  \\ ‘TYPE (d'::d::init_refs.the_context) (Fun (Fun A Bool) A)’
    by (first_assum irule
        \\ conj_asm2_tac
        >- fsrw_tac [SATISFY_ss] []
        \\ fs [TYPE_def, type_ok_def, Abbr ‘A’])
  \\ fsrw_tac [SATISFY_ss] []
  \\ ‘TERM (d'::d::init_refs.the_context) select_const’
    by (fs [new_constant_def, add_constants_def, get_the_term_constants_def,
            set_the_term_constants_def, raise_Fail_def, case_eq_thms,
            st_ex_bind_def, add_def_def]
        \\ FULL_CASE_TAC \\ rw []
        \\ fs [get_the_context_def, set_the_context_def] \\ rw []
        \\ fs [STATE_def, TERM_def] \\ rw [select_const_def]
        \\ fs [term_ok_def, FLOOKUP_DEF, CONTEXT_def, TYPE_def])
  \\ last_assum (mp_then Any drule mk_select_ax_thm) \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
  \\ drule_all new_axiom_thm \\ rw []
  \\ drule_all_then (qspecl_then [‘«ind»’, ‘0’] mp_tac) new_type_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
  \\ last_x_assum (mp_then Any drule mk_infinity_ax_thm)
  \\ (impl_tac >-
   (fs [new_type_def, st_ex_bind_def, add_type_def, st_ex_return_def,
        raise_Fail_def, case_eq_thms, bool_case_eq, COND_RATOR, can_def,
        otherwise_def, get_type_arity_def, get_the_type_constants_def,
        set_the_type_constants_def, add_def_def, get_the_context_def,
        set_the_context_def] \\ rw []
    \\ qpat_x_assum `STATE _ _` mp_tac
    \\ simp [STATE_def, TYPE_def, CONTEXT_def, extends_def, Once RTC_CASES1]
    \\ rw []
    >- fs [init_ctxt_def]
    \\ fs [STATE_def, CONTEXT_def] \\ rw []
    \\ fs [type_ok_def, FLOOKUP_DEF]))
  \\ rw []
  \\ drule_all new_axiom_thm \\ rw []
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem readLines_init_state_thm:
  readLines init_state lines ax_refs = (res, refs) ∧
  init_reader () init_refs = (r, ax_refs) ⇒
    ∃defs.
      STATE defs refs ∧
      ∀st n. res = Success (st, n) ⇒ READER_STATE defs st
Proof
  strip_tac
  \\ drule init_reader_ok
  \\ strip_tac \\ rveq
  \\ ‘READER_STATE defs init_state’
    by fs [init_state_def, READER_STATE_def, lookup_def]
  \\ drule_all readLines_thm \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs []
QED

(* -------------------------------------------------------------------------
 * Program specification (shared)
 * ------------------------------------------------------------------------- *)

Definition read_stdin_def:
  read_stdin fs refs =
    let fs' = fastForwardFD fs 0;
        stdin = UStream «stdin» in
      case readLines init_state
          (MAP (tokenize o str_prefix) (all_lines_inode fs stdin)) refs of
        (Success (s, _), refs) =>
          (add_stdout fs' (msg_success s refs.the_context), refs, SOME s)
      | (Failure (Fail e), refs) =>
          (add_stderr fs' e, refs, NONE)
End

(*
 * Almost like the one above. I'm keeping both for the sake of
 * benchmarking. Eventually the non-buffered version can go.
 *)

Definition read_file_def:
  read_file fs refs fnm =
    (if inFS_fname fs fnm then
       (case readLines init_state
             (FLAT (MAP (MAP tokenize o tokens is_newline)
                   (all_lines fs fnm))) refs of
        | (Success (s,_), refs) =>
            (add_stdout fs (msg_success s refs.the_context), refs, SOME s)
        | (Failure (Fail e), refs) =>
            (add_stderr fs e, refs, NONE))
     else
       (add_stderr fs (msg_bad_name fnm), refs, NONE))
End


Definition reader_main_def:
  reader_main fs refs cl =
    let refs = SND (init_reader () refs) in
      case cl of
        [] => read_stdin fs refs
      | [fnm] => read_file fs refs fnm
      | _ => (add_stderr fs msg_usage, refs, NONE)
End

(* ------------------------------------------------------------------------- *)
(* Specs imply that invariants are preserved.                                *)
(* ------------------------------------------------------------------------- *)

Theorem READER_STATE_init_state:
  READER_STATE defs init_state
Proof
  rw [READER_STATE_def, init_state_def, STATE_def, lookup_def]
QED

Definition flush_stdin_def:
  flush_stdin cl fs =
    case cl of
      [] => fastForwardFD fs 0
    | _ => fs
End

val _ = export_rewrites ["flush_stdin_def"];

Theorem reader_proves:
  reader_main fs init_refs cl = (outp,refs,SOME s) ⇒
  (∀asl c.
     MEM (Sequent asl c) s.thms ⇒
       (thyof refs.the_context, asl) |- c) ∧
  outp = add_stdout (flush_stdin cl fs) (msg_success s refs.the_context) ∧
  refs.the_context extends init_ctxt
Proof
  rw [reader_main_def, case_eq_thms, read_stdin_def, read_file_def,
      bool_case_eq, PULL_EXISTS]
  \\ Cases_on `init_reader () init_refs`
  \\ drule init_reader_ok \\ rw []
  \\ ‘READER_STATE defs init_state’
    by fs [READER_STATE_init_state]
  \\ drule readLines_thm \\ simp []
  \\ disch_then drule \\ rw []
  \\ fs [READER_STATE_def, EVERY_MEM, STATE_def, CONTEXT_def] \\ rveq
  \\ metis_tac [THM_def]
QED

(* -------------------------------------------------------------------------
 * Some things useful for the top-level soundness theorem, for instance:
 * if there was no output on stderr, then reader_main processed all commands
 * in the article without errors.
 * ------------------------------------------------------------------------- *)

Definition input_exists_def:
  input_exists fs cl =
    case TL cl of
      [] => ∃inp. stdin fs inp 0
    | _ => hasFreeFD fs
End

val _ = export_rewrites ["input_exists_def"];

Theorem readLines_Fail_not_empty:
  ∀st ls refs err refs'.
    readLines st ls refs = (Failure (Fail err), refs') ⇒
      err <> «»
Proof
  recInduct readLines_ind
  \\ gen_tac
  \\ Cases
  >- simp [Once readLines_def, st_ex_return_def]
  \\ rw []
  \\ simp [Once readLines_def]
  \\ rw [st_ex_return_def, st_ex_bind_def, handle_Fail_def, raise_Fail_def,
         case_eq_thms, line_Fail_def, mlstringTheory.concat_def]
QED

Definition no_errors_def:
  no_errors fs fs' ⇔
    get_file_content fs 2 = get_file_content fs' 2
End

Theorem reader_success_stderr:
  reader_main fs refs (TL cl) = (fs', refs', s) ∧
  input_exists fs cl ∧
  STD_streams fs ∧
  no_errors fs fs' ⇒
    ∃st. s = SOME st
Proof
  rw [reader_main_def, read_stdin_def, read_file_def, case_eq_thms,
      no_errors_def, msg_bad_name_def, msg_usage_def]
  \\ rfs []
  \\ fs [case_eq_thms, bool_case_eq] \\ rw [] \\ fs []
  \\ drule TextIOProofTheory.STD_streams_stderr \\ strip_tac
  \\ qpat_x_assum ‘_ = _ ’ mp_tac
  \\ fs [TextIOProofTheory.add_stdo_def, TextIOProofTheory.stdo_def,
         TextIOProofTheory.up_stdo_def, fsFFITheory.fsupdate_def,
         fsFFITheory.get_file_content_def,
         fsFFIPropsTheory.fastForwardFD_def, TextIOProofTheory.stdin_def]
  \\ fs [libTheory.the_def, UNCURRY, AFUPDKEY_ALOOKUP, case_eq_thms,
         bool_case_eq]
  \\ fs [mlstringTheory.concat_thm, msg_bad_name_def]
  \\ SELECT_ELIM_TAC \\ fs []
  \\ rpt strip_tac
  \\ drule readLines_Fail_not_empty
  \\ Cases_on `e` \\ fs []
QED

val _ = export_theory();

