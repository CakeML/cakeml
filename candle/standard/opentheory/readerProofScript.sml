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

val case_eqs =
  CaseEqs ["exc", "hol_exn", "term", "thm", "object",
           "option", "list", "update", "mlstring",
           "state", "type", "sum", "hol_refs"]

val case_eq_thms = save_thm ("case_eq_thms",
  CONJ pair_case_eq case_eqs);

(* TODO move *)

Theorem new_axiom_not_clash[simp]:
   new_axiom ax s <> (Failure (Clash tm), t)
Proof
  strip_tac
  \\ fs [new_axiom_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
         case_eq_thms, bool_case_eq, COND_RATOR, get_the_axioms_def,
         set_the_axioms_def] \\ rw [] \\ fs []
QED

Theorem new_constant_not_clash[simp]:
   new_constant (a,b) s <> (Failure (Clash tm), t)
Proof
  rw [new_constant_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem new_type_not_clash[simp]:
   new_type (a,b) s <> (Failure (Clash tm), t)
Proof
  rw [new_type_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem dest_abs_not_clash[simp]:
   dest_abs x s <> (Failure (Clash tm), t)
Proof
  EVAL_TAC \\ PURE_CASE_TAC \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* Reader does not raise Clash                                               *)
(* ------------------------------------------------------------------------- *)

Theorem find_axiom_not_clash[simp]:
   find_axiom (a,b) c <> (Failure (Clash tm),refs)
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
   peek x y <> (Failure (Clash tm),refs)
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
   getType x y <> (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getName_not_clash[simp]:
   getName x y <> (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
  \\ fs [st_ex_return_def] \\ CASE_TAC \\ fs []
QED

Theorem getConst_not_clash[simp]:
   getConst x y <> (Failure (Clash tm),refs)
Proof
  Cases_on`x` \\ EVAL_TAC
QED

Theorem getList_not_clash[simp]:
   getList x y <> (Failure (Clash tm),refs)
Proof
  Cases_on `x` \\ EVAL_TAC
QED

Theorem getTypeOp_not_clash[simp]:
   getTypeOp a b <> (Failure (Clash tm),refs)
Proof
  Cases_on`a` \\ EVAL_TAC
QED

Theorem getPair_not_clash[simp]:
   getPair a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC
  \\ Cases_on `t` \\ EVAL_TAC \\ Cases_on `t'` \\ EVAL_TAC
QED

Theorem getCns_not_clash[simp]:
   getCns a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs []
QED

Theorem getNvs_not_clash[simp]:
   getNvs a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs []
QED

Theorem getTms_not_clash[simp]:
   getTms a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs []
QED

Theorem getTys_not_clash[simp]:
   getTys a b <> (Failure (Clash tm),refs)
Proof
  Cases_on `a` \\ EVAL_TAC
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs []
QED

Theorem BETA_CONV_not_clash[simp]:
   BETA_CONV t s <> (Failure (Clash tm),r)
Proof
  rw [BETA_CONV_def, handle_Fail_def, st_ex_bind_def, raise_Fail_def]
  \\ PURE_CASE_TAC \\ rw [case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs []
QED

Theorem readLine_not_clash[simp]:
   readLine x y z ≠ (Failure (Clash tm),refs)
Proof
  rw [readLine_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
      handle_Clash_def, handle_Fail_def, case_eq_thms, UNCURRY]
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ fs [case_eq_thms, map_not_clash_thm]
  \\ pop_assum mp_tac \\ fs []
  \\ rpt (PURE_CASE_TAC \\ fs [])
QED

Theorem readLines_not_clash[simp]:
   ∀ls x y tm refs. readLines ls x y ≠ (Failure (Clash tm),refs)
Proof
  recInduct readLines_ind \\ rw[]
  \\ rw [Once readLines_def, case_eq_thms, st_ex_bind_def, st_ex_return_def,
         handle_Fail_def, raise_Fail_def]
  \\ PURE_CASE_TAC \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs [] \\ metis_tac []
QED

(* ------------------------------------------------------------------------- *)
(* reader_init does not raise Clash                                          *)
(* ------------------------------------------------------------------------- *)

Theorem mk_true_not_clash[simp]:
   mk_true () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_true_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_univ_not_clash[simp]:
   mk_univ ty refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_univ_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_forall_not_clash[simp]:
   mk_forall (v,p) refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_forall_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_eta_ax_not_clash[simp]:
   mk_eta_ax () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_eta_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_conj_const_not_clash[simp]:
   mk_conj_const () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_conj_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_conj_not_clash[simp]:
   mk_conj (p,q) refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_conj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_imp_const_not_clash[simp]:
   mk_imp_const () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_imp_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_imp_not_clash[simp]:
   mk_imp (p,q) refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_imp_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_select_ax_not_clash[simp]:
   mk_select_ax () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_select_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_ex_not_clash[simp]:
   mk_ex ty refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_ex_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_exists_not_clash[simp]:
   mk_exists (v,p) refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_exists_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_surj_not_clash[simp]:
   mk_surj f a b refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_surj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_inj_not_clash[simp]:
   mk_inj f a refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_inj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_false_not_clash[simp]:
   mk_false () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_false_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_neg_const_not_clash[simp]:
   mk_neg_const () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_neg_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_neg_not_clash[simp]:
   mk_neg p refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_neg_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem mk_infinity_ax_not_clash[simp]:
   mk_infinity_ax () refs <> (Failure (Clash tm), refs')
Proof
  rw [mk_infinity_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
QED

Theorem init_reader_not_clash[simp]:
   init_reader () refs <> (Failure (Clash tm), refs')
Proof
  rw [init_reader_def, st_ex_bind_def, st_ex_return_def, case_eq_thms,
      select_sym_def, ind_type_def]
QED

(* ------------------------------------------------------------------------- *)
(* Refinement invariants                                                     *)
(* ------------------------------------------------------------------------- *)

(* Refinement invariant for objects *)
val OBJ_def = tDefine "OBJ" `
  (OBJ defs (List xs)     <=> EVERY (OBJ defs) xs) /\
  (OBJ defs (Type ty)     <=> TYPE defs ty) /\
  (OBJ defs (Var (n, ty)) <=> TERM defs (Var n ty) /\ TYPE defs ty) /\
  (OBJ defs (Term tm)     <=> TERM defs tm) /\
  (OBJ defs (Thm thm)     <=> THM defs thm) /\
  (OBJ defs _             <=> T)`
  (WF_REL_TAC `measure (object_size o SND)`
   \\ Induct \\ rw [object_size_def]
   \\ res_tac \\ fs []);

Theorem OBJ_APPEND_EXTEND:
   !defs obj d.
     STATE (ds ++ defs) refs /\
     (!th. THM defs th ==> THM (ds ++ defs) th) /\
     OBJ defs obj
     ==>
     OBJ (ds++defs) obj
Proof
  recInduct (theorem"OBJ_ind") \\ rw [] \\ fs [OBJ_def, EVERY_MEM]
  \\ metis_tac [TERM_APPEND_EXTEND, TYPE_APPEND_EXTEND]
QED

val READER_STATE_def = Define `
  READER_STATE defs st <=>
    EVERY (THM defs) st.thms /\
    EVERY (OBJ defs) st.stack /\
    (!n obj. lookup (Num n) st.dict = SOME obj ==> OBJ defs obj)`

Theorem READER_STATE_EXTEND:
   READER_STATE defs st /\
   THM defs th
   ==>
   READER_STATE defs (st with thms := th::st.thms)
Proof
   rw [READER_STATE_def]
QED

Theorem READER_STATE_APPEND_EXTEND:
   STATE (ds++defs) refs /\
   READER_STATE defs st /\
   (!th. THM defs th ==> THM (ds++defs) th)
   ==>
   READER_STATE (ds++defs) st
Proof
  rw [READER_STATE_def] \\ metis_tac [OBJ_APPEND_EXTEND, EVERY_MEM]
QED

val READER_STATE_CONS_EXTEND = save_thm ("READER_STATE_CONS_EXTEND",
  READER_STATE_APPEND_EXTEND
  |> Q.INST [`ds`|->`[d]`]
  |> SIMP_RULE(srw_ss())[]);

(* ------------------------------------------------------------------------- *)
(* Kernel function support theorems (TODO: move)                             *)
(* ------------------------------------------------------------------------- *)

Theorem first_EVERY:
   !Q xs x. EVERY P xs /\ first Q xs = SOME x ==> P x
Proof
  recInduct first_ind \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [first_def]
  \\ rw [case_eq_thms, PULL_EXISTS, bool_case_eq] \\ fs []
QED

(* TODO move to holKernelProof *)
Theorem axioms_thm:
   STATE defs refs /\
   axioms () refs = (res, refs')
   ==>
   refs = refs' /\
   !axs. res = Success axs ==> EVERY (THM defs) axs
Proof
  rw [axioms_def, get_the_axioms_def, STATE_def]
  \\ fs [EVERY_MAP, lift_tm_def, CONTEXT_def, EVERY_MEM, MEM_MAP] \\ rw []
  \\ fs [THM_def]
  \\ match_mp_tac (last (CONJUNCTS proves_rules))
  \\ conj_tac >- metis_tac [extends_theory_ok, init_theory_ok]
  \\ EVAL_TAC \\ fs [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  \\ metis_tac []
QED

Theorem find_axiom_thm:
   STATE defs refs /\
   EVERY (TERM defs) ls /\
   TERM defs tm /\
   find_axiom (ls, tm) refs = (res, refs')
   ==>
   refs = refs' /\ !thm. res = Success thm ==> THM defs thm
Proof
  rw [find_axiom_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def,
      case_eq_thms, PULL_EXISTS]
  \\ TRY PURE_FULL_CASE_TAC \\ fs [] \\ rw []
  \\ metis_tac [axioms_thm, first_EVERY]
QED

Theorem assoc_thm:
   !s l refs res refs'.
     assoc s l refs = (res, refs')
     ==>
     refs = refs' /\
     !t. res = Success t ==> ALOOKUP l s = SOME t
Proof
   Induct_on `l` \\ once_rewrite_tac [assoc_def]
   \\ fs [raise_Fail_def, st_ex_return_def]
   \\ Cases \\ fs [] \\ rw [] \\ fs []
   \\ res_tac \\ fs []
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem assoc_state_thm:
   !s l refs res refs'. assoc s l refs = (res, refs') ==> refs = refs'
Proof
   Induct_on `l` \\ rw [] \\ pop_assum mp_tac
   \\ rw [Once assoc_def, raise_Fail_def, st_ex_return_def, case_eq_thms,
          pair_CASE_def]
   \\ res_tac
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem assoc_ty_thm:
   !s l refs res refs'.
     EVERY (TYPE defs o SND) l /\
     assoc s l refs = (res, refs')
     ==>
     !ty. res = Success ty ==> TYPE defs ty
Proof
  Induct_on `l` \\ rw [] \\ pop_assum mp_tac
  \\ rw [Once assoc_def, raise_Fail_def, st_ex_return_def, pair_CASE_def]
  \\ res_tac \\ fs []
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem type_of_thm:
   !tm refs res refs'.
     STATE defs refs /\
     TERM defs tm /\
     type_of tm refs = (res, refs')
     ==>
     refs = refs' /\
     !ty. res = Success ty ==> TYPE defs ty /\ welltyped tm
Proof
  Induct \\ rw []
  \\ pop_assum mp_tac
  \\ rw [Once type_of_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def,
         dest_type_def]
  \\ fs [TERM_def, TYPE_def, holSyntaxTheory.term_ok_def,
         case_eq_thms, mk_fun_ty_def, mk_type_def, st_ex_bind_def,
         st_ex_return_def, raise_Fail_def, try_def, otherwise_def,
         get_type_arity_def, get_the_type_constants_def] \\ rw []
  \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ imp_res_tac assoc_thm
  \\ rfs [term_ok_def, type_ok_def, STATE_def, CONTEXT_def] \\ fs []
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem mk_comb_thm:
   STATE defs refs /\
   TERM defs f /\
   TERM defs a /\
   mk_comb (f, a) refs = (res, refs')
   ==>
   refs = refs' /\ !fa. res = Success fa ==> TERM defs fa
Proof
  rw [mk_comb_def, st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ rpt (PURE_FULL_CASE_TAC \\ fs [])
  \\ rw [] \\ fs []
  \\ imp_res_tac type_of_thm \\ fs [] \\ rfs []
  \\ imp_res_tac type_of_has_type
  \\ fs [TERM_def, TYPE_def, type_ok_def, term_ok_def]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem get_const_type_thm:
   STATE defs refs /\
   get_const_type n refs = (res, refs')
   ==>
   refs = refs' /\ !ty. res = Success ty ==> TYPE defs ty
Proof
  rw [get_const_type_def, st_ex_bind_def, st_ex_return_def,
      get_the_term_constants_def]
  \\ imp_res_tac the_term_constants_TYPE \\ fs [ELIM_UNCURRY, GSYM o_DEF]
  \\ metis_tac [assoc_state_thm, assoc_ty_thm]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem tymatch_thm:
   !tys1 tys2 sids.
     EVERY (TYPE defs) tys1 /\
     EVERY (TYPE defs) tys2 /\
     EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) (FST sids) /\
     tymatch tys1 tys2 sids = SOME (tys, _)
     ==>
     EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) tys
Proof
  recInduct holSyntaxExtraTheory.tymatch_ind \\ rw []
  \\ pop_assum mp_tac
  \\ rw [Once tymatch_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [case_eq_thms, bool_case_eq] \\ rw []
  \\ metis_tac [TYPE_def, type_ok_def]
QED

(* TODO holKernelProof - move, or already exists? *)
Theorem match_type_thm:
   TYPE defs ty1 /\
   TYPE defs ty2 /\
   match_type ty1 ty2 = SOME tys
   ==>
   EVERY (\(t1,t2). TYPE defs t1 /\ TYPE defs t2) tys
Proof
  rw [holSyntaxExtraTheory.match_type_def]
  \\ PairCases_on `z` \\ fs []
  \\ imp_res_tac tymatch_thm \\ rfs []
QED

(* TODO proven elsewhere *)
Theorem TERM_Comb:
   TERM defs (Comb a b) ==> TERM defs a /\ TERM defs b
Proof
  rw [TERM_def, term_ok_def]
QED

Theorem TERM_Abs:
   TERM defs (Abs v e) ==> TERM defs v /\ TERM defs e
Proof
  rw [TERM_def] \\ fs [term_ok_def]
QED

(* ------------------------------------------------------------------------- *)
(* Reader operations preserve invariants                                     *)
(* ------------------------------------------------------------------------- *)

Theorem next_line_thm:
   READER_STATE defs s ==> READER_STATE defs (next_line s)
Proof
  rw [READER_STATE_def, next_line_def]
QED

Theorem getNum_thm:
   getNum obj refs = (res, refs') ==> refs = refs'
Proof
   Cases_on `obj` \\ rw [getNum_def, raise_Fail_def, st_ex_return_def]
   \\ fs []
QED

Theorem getName_thm:
   getName obj refs = (res, refs') ==> refs = refs'
Proof
   Cases_on `obj` \\ rw [getName_def, raise_Fail_def, st_ex_return_def]
   \\ fs []
QED

Theorem getList_thm:
   OBJ defs obj /\
   getList obj refs = (res, refs')
   ==>
   refs = refs' /\ !ls. res = Success ls ==> EVERY (OBJ defs) ls
Proof
   Cases_on `obj` \\ rw [getList_def, raise_Fail_def, st_ex_return_def]
   \\ fs []
   \\ metis_tac [OBJ_def]
QED

Theorem getTypeOp_thm:
   getTypeOp obj refs = (res, refs') ==> refs = refs'
Proof
   Cases_on `obj` \\ rw [getTypeOp_def, raise_Fail_def, st_ex_return_def]
   \\ fs []
QED

Theorem getType_thm:
   OBJ defs obj /\
   getType obj refs = (res, refs')
   ==>
   refs = refs' /\ !ty. res = Success ty ==> TYPE defs ty
Proof
   Cases_on `obj` \\ rw [getType_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]
QED

Theorem map_getType_thm:
   !xs refs res refs'.
     EVERY (OBJ defs) xs /\
     map getType xs refs = (res, refs')
     ==>
     refs = refs' /\ !tys. res = Success tys ==> EVERY (TYPE defs) tys
Proof
  Induct \\ rw [Once map_def, st_ex_return_def, st_ex_bind_def] \\ fs []
  \\ fs [case_eq_thms] \\ rw []
  \\ imp_res_tac getType_thm \\ fs []
  \\ res_tac \\ fs []
QED

Theorem getConst_thm:
   getConst obj refs = (res, refs') ==> refs = refs'
Proof
   Cases_on `obj` \\ rw [getConst_def, raise_Fail_def, st_ex_return_def]
   \\ fs []
QED

Theorem getVar_thm:
   OBJ defs obj /\
   getVar obj refs = (res, refs')
   ==>
   refs = refs' /\
   !n ty. res = Success (n, ty) ==> TERM defs (Var n ty) /\ TYPE defs ty
Proof
   Cases_on `obj` \\ rw [getVar_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]
QED

Theorem getTerm_thm:
   OBJ defs obj /\
   getTerm obj refs = (res, refs')
   ==>
   refs = refs' /\ !tm. res = Success tm ==> TERM defs tm
Proof
   Cases_on `obj` \\ rw [getTerm_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ fs [OBJ_def]
QED

Theorem map_getTerm_thm:
   !xs refs res refs'.
     EVERY (OBJ defs) xs /\
     map getTerm xs refs = (res, refs')
     ==>
     refs = refs' /\ !tms. res = Success tms ==> EVERY (TERM defs) tms
Proof
  Induct \\ rw [Once map_def, st_ex_return_def, st_ex_bind_def, case_eq_thms]
  \\ fs []
  \\ imp_res_tac getTerm_thm \\ fs []
  \\ res_tac \\ fs []
QED

Theorem getThm_thm:
   OBJ defs obj /\
   getThm obj refs = (res, refs')
   ==>
   refs = refs' /\ !thm. res = Success thm ==> THM defs thm
Proof
   Cases_on `obj` \\ rw [getThm_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]
QED

Theorem pop_thm:
   READER_STATE defs st /\
   pop st refs = (res, refs')
   ==>
   refs = refs' /\
   !a st'. res = Success (a, st') ==> OBJ defs a /\ READER_STATE defs st'
Proof
   rw [pop_def, raise_Fail_def, st_ex_return_def]
   \\ PURE_FULL_CASE_TAC \\ fs [] \\ rw []
   \\ fs [READER_STATE_def, state_component_equality]
   \\ rw [] \\ res_tac
QED

Theorem peek_thm:
   READER_STATE defs st /\
   peek st refs = (res, refs')
   ==>
   refs = refs' /\ !obj. res = Success obj ==> OBJ defs obj
Proof
   rw [peek_def, raise_Fail_def, st_ex_return_def]
   \\ PURE_FULL_CASE_TAC \\ fs [READER_STATE_def]
QED

Theorem push_thm:
   READER_STATE defs st /\
   OBJ defs obj
   ==>
   READER_STATE defs (push obj st)
Proof
  rw [push_def, READER_STATE_def]
QED

Theorem push_push_thm:
   READER_STATE defs st /\
   OBJ defs obj1 /\
   OBJ defs obj2
   ==>
   READER_STATE defs (push obj1 (push obj2 st))
Proof
  rw [push_def, READER_STATE_def]
QED

Theorem insert_dict_thm:
   READER_STATE defs st /\
   OBJ defs obj
   ==>
   READER_STATE defs (insert_dict (Num n) obj st)
Proof
  rw [insert_dict_def, READER_STATE_def, lookup_insert]
  \\ PURE_FULL_CASE_TAC \\ fs []
  \\ res_tac
QED

Theorem delete_dict_thm:
   READER_STATE defs st
   ==>
   READER_STATE defs (delete_dict (Num n) st)
Proof
  rw [delete_dict_def, READER_STATE_def, lookup_delete]
  \\ res_tac
QED

Theorem getPair_thm:
   OBJ defs obj /\
   getPair obj refs = (res, refs')
   ==>
   refs = refs' /\ !a b. res = Success (a, b) ==> OBJ defs a /\ OBJ defs b
Proof
  Cases_on `obj` \\ EVAL_TAC \\ rw [] \\ pop_assum mp_tac
  \\ Cases_on `l` \\ EVAL_TAC \\ rw [] \\ pop_assum mp_tac
  \\ Cases_on `t` \\ EVAL_TAC \\ rw [] \\ pop_assum mp_tac
  \\ Cases_on `t'` \\ EVAL_TAC \\ rw [] \\ fs []
QED

Theorem getTys_thm:
   STATE defs refs /\
   OBJ defs obj /\
   getTys obj refs = (res, refs')
   ==>
   refs = refs' /\ !t ty. res = Success (t, ty)
   ==>
   TYPE defs t /\ TYPE defs ty
Proof
  Cases_on `obj`
  \\ rw [getTys_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY,
         case_eq_thms, getPair_def]
  \\ map_every imp_res_tac [getPair_thm, getType_thm, getName_thm,
                            mk_vartype_thm] \\ fs [] \\ rw []
  \\ metis_tac [mk_vartype_thm, STATE_def, SND, FST, PAIR]
QED

Theorem map_getTys_thm:
   !xs refs res refs'.
     STATE defs refs /\
     EVERY (OBJ defs) xs /\
     map getTys xs refs = (res, refs')
     ==>
     refs = refs' /\
     !tys.
       res = Success tys
       ==>
       EVERY (\(ty1,ty2). TYPE defs ty1 /\ TYPE defs ty2) tys
Proof
  Induct \\ rw [] \\ pop_assum mp_tac
  \\ rw [Once map_def, st_ex_bind_def, st_ex_return_def] \\ fs []
  \\ fs [case_eq_thms] \\ rw []
  \\ imp_res_tac getTys_thm \\ fs []
  \\ rename1 `xx = _ ==> _` \\ PairCases_on `xx` \\ fs []
  \\ metis_tac []
QED

Theorem getTms_thm:
   STATE defs refs /\
   OBJ defs obj /\
   getTms obj refs = (res, refs')
   ==>
   refs = refs' /\
   !tm var. res = Success (tm, var) ==> TERM defs tm /\ TERM defs var
Proof
  Cases_on `obj`
  \\ fs [getTms_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY,
         case_eq_thms, PULL_EXISTS, getPair_def] \\ rw []
  \\ map_every imp_res_tac [getPair_thm, getTerm_thm, getVar_thm, mk_var_thm]
  \\ fs []
  \\ metis_tac [FST, SND, PAIR]
QED

Theorem map_getTms_thm:
   !xs refs res refs'.
     STATE defs refs /\
     EVERY (OBJ defs) xs /\
     map getTms xs refs = (res, refs')
     ==>
     refs = refs' /\
     !tmvs.
       res = Success tmvs
       ==>
       EVERY (\(tm1,tm2). TERM defs tm1 /\ TERM defs tm2) tmvs
Proof
  Induct \\ rw [] \\ pop_assum mp_tac
  \\ rw [Once map_def, st_ex_bind_def, st_ex_return_def, case_eq_thms] \\ fs []
  \\ imp_res_tac getTms_thm \\ fs [ELIM_UNCURRY]
  \\ metis_tac [FST, SND, PAIR, UNCURRY]
QED

Theorem getNvs_thm:
   STATE defs refs /\
   OBJ defs obj /\
   getNvs obj refs = (res, refs')
   ==>
   refs = refs' /\
   !tm1 tm2. res = Success (tm1, tm2) ==> TERM defs tm1 /\ TERM defs tm2
Proof
  Cases_on `obj`
  \\ rw [getNvs_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY,
         getPair_def, case_eq_thms]
  \\ map_every imp_res_tac [getPair_thm, getName_thm, getVar_thm, mk_var_thm]
  \\ metis_tac [FST, SND, PAIR]
QED

Theorem map_getNvs_thm:
   !xs refs res refs'.
     STATE defs refs /\
     EVERY (OBJ defs) xs /\
     map getNvs xs refs = (res, refs')
     ==>
     refs = refs' /\
     !ts. res = Success ts ==>
         EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) ts
Proof
  Induct
  \\ rw [Once map_def, st_ex_return_def, st_ex_bind_def, case_eq_thms] \\ fs []
  \\ imp_res_tac getNvs_thm \\ fs [ELIM_UNCURRY]
  \\ metis_tac [FST, SND, PAIR]
QED

Theorem getCns_thm:
   STATE defs refs /\
   TERM defs tm /\
   getCns (tm, _) refs = (res, refs')
   ==>
   refs = refs' /\ !a. res = Success a ==> OBJ defs a
Proof
  rw [getCns_def, st_ex_bind_def, st_ex_return_def, UNCURRY, case_eq_thms]
  \\ imp_res_tac dest_var_thm \\ fs [OBJ_def]
QED

Theorem map_getCns_thm:
   !xs refs res refs'.
     STATE defs refs /\
     EVERY (TERM defs o FST) xs /\
     map getCns xs refs = (res, refs')
     ==>
     refs = refs' /\ !xs. res = Success xs ==> EVERY (OBJ defs) xs
Proof
  Induct \\ rw [Once map_def, st_ex_return_def, st_ex_bind_def, case_eq_thms]
  \\ imp_res_tac getCns_thm \\ fs [ELIM_UNCURRY]
  \\ metis_tac [FST, SND, PAIR]
QED

(* imp_res_tac is not useful when the monadic functions are too deep *)
fun drule_or_nil thm =
  (drule (GEN_ALL thm) \\ rpt (disch_then drule \\ fs []) \\ rw []) ORELSE
  (qexists_tac `[]` \\ fs [] \\ metis_tac [])

(* TODO clean *)
Theorem BETA_CONV_thm:
   STATE defs refs /\
   TERM defs tm /\
   BETA_CONV tm refs = (res, refs')
   ==>
   refs = refs' /\
   !thm. res = Success thm ==> THM defs thm
Proof
  Cases_on `tm`
  \\ rw [BETA_CONV_def, handle_Fail_def, raise_Fail_def, st_ex_bind_def,
        st_ex_return_def, case_eq_thms, UNCURRY, dest_comb_def, dest_abs_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (metis_tac [BETA_thm])
  \\ imp_res_tac TERM_Comb \\ fs []
  \\ imp_res_tac TERM_Abs \\ fs []
  \\ qmatch_asmsub_abbrev_tac `BETA tm1 refs`
  \\ qpat_x_assum `TERM defs tm1` assume_tac
  \\ drule_or_nil BETA_thm
  \\ qmatch_asmsub_abbrev_tac `mk_comb (a, b)`
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then (mp_tac o Q.SPECL [`b`,`a`] o
                 (CONV_RULE (RESORT_FORALL_CONV rev))) \\ fs [] \\ rw []
  \\ drule_or_nil BETA_thm
  \\ `EVERY (\(t1,t2). TERM defs t1 /\ TERM defs t2) [(t0,b)]` by fs []
  \\ drule_or_nil INST_thm
QED

(* ------------------------------------------------------------------------- *)
(* Reader preserves invariants                                               *)
(* ------------------------------------------------------------------------- *)

Theorem readLine_thm:
   STATE defs refs /\
   READER_STATE defs st /\
   readLine line st refs = (res, refs')
   ==>
   ?ds.
     STATE (ds ++ defs) refs' /\
     !st'. res = Success st' ==> READER_STATE (ds ++ defs) st'
Proof
  fs [readLine_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ IF_CASES_TAC \\ fs []
  >- (* version *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ fs []
    \\ metis_tac [pop_thm, getNum_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* absTerm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (rename1 `mk_var v1` \\ Cases_on `v1` \\ fs [mk_var_def])
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getVar_thm, mk_abs_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* absThm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (rename1 `mk_var v1` \\ Cases_on `v1` \\ fs [mk_var_def])
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm, getVar_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [ABS_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* appTerm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getVar_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [mk_comb_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* appThm *)
   (fs [case_eq_thms] \\ rw  []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms]
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [MK_COMB_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* assume *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [ASSUME_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* axiom *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getList_thm, map_getTerm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def]) \\ rw []
    \\ metis_tac [find_axiom_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* betaConv *)
   (fs [case_eq_thms, handle_Fail_def] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, BETA_CONV_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* cons *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* const *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* constTerm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getType_thm, getConst_thm, match_type_thm, get_const_type_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [mk_const_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* deductAntysim *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [DEDUCT_ANTISYM_RULE_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* def *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ qexists_tac `[]` \\ rw []
    \\ map_every imp_res_tac [pop_thm, peek_thm, getNum_thm] \\ fs []
    \\ fs [insert_dict_thm]
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineConst *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getName_thm, type_of_thm] \\ fs []
    \\ res_tac \\ fs [] \\ rveq
    \\ imp_res_tac type_of_thm \\ fs [] \\ rveq
    \\ TRY (* For a new definition added to defs *)
     (drule (GEN_ALL mk_var_thm)
      \\ disch_then (qspecl_then [`n`,`ty`] mp_tac) \\ rw []
      \\ drule (GEN_ALL mk_eq_thm)
      \\ disch_then (qspec_then `tm` mp_tac)
      \\ rpt (disch_then drule \\ fs []) \\ rw []
      \\ drule (GEN_ALL new_basic_definition_thm)
      \\ disch_then drule \\ fs [] \\ rw []
      \\ qexists_tac `[d]` \\ rw []
      \\ `OBJ (d::defs) (Thm th)` by rw [OBJ_def])
    \\ TRY
      (irule push_push_thm \\ simp [OBJ_def]
       \\ irule READER_STATE_CONS_EXTEND \\ fs []
       \\ asm_exists_tac \\ fs [])
    \\ qexists_tac `[]` \\ fs []
    \\ drule (GEN_ALL mk_var_thm)
    \\ disch_then (qspecl_then [`n`,`ty`] mp_tac) \\ rw []
    \\ drule (GEN_ALL mk_eq_thm)
    \\ disch_then (qspec_then `tm` mp_tac)
    \\ rpt (disch_then drule \\ fs []) \\ rw []
    \\ drule (GEN_ALL new_basic_definition_thm)
    \\ disch_then drule \\ fs [] \\ rw [])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineConstList *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every drule_or_nil
      [pop_thm, getThm_thm, pop_thm, getList_thm, map_getNvs_thm, INST_thm]
    \\ TRY
     (drule_or_nil new_specification_thm
      \\ drule (GEN_ALL TERM_CONS_EXTEND) \\ rw []
      \\ `EVERY (TERM (d::defs) o FST) ls'` by fs [EVERY_MEM, ELIM_UNCURRY]
      \\ Q.ISPEC_THEN `ls'` mp_tac (Q.INST [`defs`|->`d::defs`] map_getCns_thm)
      \\ disch_then drule \\ rw [])
    \\ TRY
     (qexists_tac `[]` \\ fs []
      \\ drule (GEN_ALL new_specification_thm)
      \\ disch_then drule \\ fs []
      \\ rw []
      \\ NO_TAC)
    \\ qexists_tac `[d]` \\ fs []
    \\ irule push_push_thm \\ fs [OBJ_def]
    \\ fsrw_tac [ETA_ss] []
    \\ irule READER_STATE_CONS_EXTEND \\ fs []
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineTypeOp *)
   (fs [case_eq_thms] \\ rw []
    \\ rpt (CHANGED_TAC (TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []))
    \\ map_every drule_or_nil [pop_thm, getThm_thm, pop_thm, getList_thm, pop_thm]
    \\ imp_res_tac getName_thm \\ fs [] \\ rveq
    \\ drule_or_nil pop_thm
    \\ TRY (qexists_tac `[]` \\ fs [] \\ metis_tac [])
    \\ drule_or_nil pop_thm
    \\ TRY
     (drule (GEN_ALL new_basic_type_definition_thm)
      \\ disch_then (qspec_then `nm` drule)
      \\ disch_then (qspecl_then [`rep`,`abs`] mp_tac) \\ rw [])
    \\ TRY (`TERM (ds ++ defs) (concl th1)` by metis_tac [concl_thm])
    \\ drule_or_nil dest_eq_thm
    \\ drule (GEN_ALL ABS_thm)
    \\ disch_then (qspec_then `th1` mp_tac)
    \\ rpt (disch_then drule) \\ rw []
    \\ qspec_then `th2` mp_tac (GEN_ALL SYM_thm)
    \\ rpt (disch_then drule) \\ rw []
    \\ TRY (`TERM (ds ++ defs) (concl th2')` by metis_tac [concl_thm])
    \\ drule_or_nil dest_eq_thm
    \\ drule_or_nil dest_comb_thm
    \\ drule_or_nil ABS_thm
    \\ qexists_tac `ds` \\ fs []
    \\ irule push_push_thm \\ fs [OBJ_def]
    \\ irule push_push_thm \\ fs [OBJ_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ irule READER_STATE_APPEND_EXTEND \\ fs []
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* eqMp *)
   (fs [case_eq_thms, handle_Fail_def] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm]
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [EQ_MP_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* hdTl *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* nil *)
   (fs [case_eq_thms] \\ rw [] \\ fs []
    \\ qexists_tac `[]` \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* opType *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm, getTypeOp_thm, map_getType_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [mk_type_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* pop *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ imp_res_tac pop_thm \\ fs []
    \\ qexists_tac `[]` \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* pragma *)
   (fs [case_eq_thms, handle_Fail_def] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ imp_res_tac pop_thm \\ fs [bool_case_eq, COND_RATOR]
    \\ imp_res_tac getName_thm
    \\ qexists_tac `[]` \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* proveHyp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [PROVE_HYP_thm, pop_thm, getThm_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* ref *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getNum_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ metis_tac [READER_STATE_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* refl *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, REFL_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* remove *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getNum_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ metis_tac [READER_STATE_def, delete_dict_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* subst *)
   (fs [case_eq_thms, handle_Clash_def] \\ rw []
    \\ rpt (CHANGED_TAC
      (TRY (pairarg_tac \\ fs [])
       \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []))
    \\ map_every drule_or_nil [pop_thm, getThm_thm]
    \\ map_every drule_or_nil [pop_thm, getPair_thm]
    \\ qpat_x_assum `_ _ tys` assume_tac
    \\ map_every drule_or_nil [getList_thm, map_getTys_thm, INST_TYPE_thm]
    \\ qpat_x_assum `_ _ tms` assume_tac
    \\ map_every drule_or_nil [getList_thm, map_getTms_thm, INST_thm]
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* sym *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [SYM_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* thm *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, getList_thm, getThm_thm, map_getTerm_thm] \\ fs []
    \\ metis_tac [ALPHA_THM_thm, READER_STATE_EXTEND])
  \\ IF_CASES_TAC \\ fs []
  >- (* trans *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [TRANS_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* typeOp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* var *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm, getType_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ fs [TYPE_def, TERM_def, holSyntaxTheory.term_ok_def]
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >-
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ drule_or_nil pop_thm
    \\ drule_or_nil getVar_thm
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ rename1 `mk_var v1` \\ PairCases_on `v1` \\ fs [mk_var_def, TERM_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* varType *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ qexists_tac `[]` \\ fs [] \\ rw []
    \\ irule push_thm \\ fs []
    \\ fs [OBJ_def, STATE_def]
    \\ irule mk_vartype_thm
    \\ metis_tac [STATE_def, CONTEXT_def])
     (* digits *)
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ qexists_tac `[]` \\ fs [] \\ rw []
  \\ irule push_thm \\ fs [OBJ_def]
QED

Theorem readLines_thm:
   !lines st res refs refs' defs.
     STATE defs refs /\
     READER_STATE defs st /\
     readLines lines st refs = (res, refs')
     ==>
     ?ds.
       STATE (ds ++ defs) refs' /\
       !st' n. res = Success (st', n) ==> READER_STATE (ds ++ defs) st'
Proof
  recInduct readLines_ind \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [readLines_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ CASE_TAC \\ fs []
  >- (rw [] \\ qexists_tac `[]` \\ fs [])
  \\ fs [case_eq_thms, PULL_EXISTS, handle_Fail_def, raise_Fail_def]
  \\ rw [] \\ fs [case_eq_thms] \\ rw [] \\ fs []
  \\ drule (GEN_ALL readLine_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ first_x_assum drule
  >- (fs [next_line_def, READER_STATE_def] \\ metis_tac [])
  \\ imp_res_tac next_line_thm
  \\ disch_then drule \\ rw []
  \\ asm_exists_tac \\ fs []
QED

(* ------------------------------------------------------------------------- *)
(* Axiom cooking                                                             *)
(* ------------------------------------------------------------------------- *)

Theorem STATE_lemma:
   STATE defs refs
   ==>
   (!a b. TYPE defs a /\ TYPE defs b ==> TYPE defs (Fun a b)) /\
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
   STATE defs refs /\
   mk_true () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_true_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ qmatch_asmsub_abbrev_tac `mk_abs (v,_)`
  \\ drule STATE_lemma \\ strip_tac
  \\ `TERM defs v` by fs [TERM_def, Abbr`v`, term_ok_def, mk_var_def, TYPE_def]
  \\ drule (GEN_ALL mk_abs_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_eq_thm)
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_univ_thm:
   STATE defs refs /\
   TYPE defs ty /\
   mk_univ ty refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_univ_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ first_x_assum (qspecl_then [`ty`, `Bool`] assume_tac) \\ rfs []
  \\ drule (GEN_ALL mk_true_thm)
  \\ disch_then drule \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_abs (v,tru)`
  \\ `TERM defs v` by fs [TERM_def, Abbr`v`, term_ok_def, mk_var_def, TYPE_def]
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs tru` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_eq (p,_)`
  \\ `TERM defs p` by fs [TERM_def, Abbr`p`, term_ok_def, mk_var_def, TYPE_def]
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs (Abs _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs p` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs (Comb _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_forall_thm:
   STATE defs refs /\
   TERM defs t2 /\
   TERM defs t1 /\
   mk_forall (t1, t2) refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_forall_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule (GEN_ALL type_of_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_univ_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs t1` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs t2` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs all'` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs (Abs _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_eta_ax_thm:
   STATE defs refs /\
   mk_eta_ax () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_eta_ax_def, st_ex_bind_def, case_eq_thms, st_ex_return_def, mk_var_def]
  \\ qmatch_asmsub_abbrev_tac `mk_comb (t1, t2)`
  \\ drule STATE_lemma \\ strip_tac
  \\ qabbrev_tac `A = Tyvar (strlit"A")`
  \\ qabbrev_tac `B = Tyvar (strlit"B")`
  \\ `TYPE defs A /\ TYPE defs B` by fs [TYPE_def, type_ok_def, Abbr`A`, Abbr`B`]
  \\ first_x_assum (qspecl_then [`A`,`B`] assume_tac) \\ rfs []
  \\ `TERM defs t1` by fs [TERM_def, term_ok_def, TYPE_def, type_ok_def, Abbr`t1`]
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs t2` by fs [TERM_def, Abbr`t2`, term_ok_def, TYPE_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs t2` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs body` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs t1` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac [mk_forall_thm]
QED

Theorem mk_conj_const_thm:
   STATE defs refs /\
   mk_conj_const () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_conj_const_def, st_ex_bind_def, st_ex_return_def]
  \\ reverse (fs [case_eq_thms])
  \\ drule STATE_lemma \\ strip_tac
  \\ first_assum (qspecl_then [`Bool`, `Bool`] assume_tac)
  \\ first_x_assum (qspecl_then [`Bool`, `Fun Bool Bool`] assume_tac) \\ rfs []
  \\ drule (GEN_ALL mk_true_thm)
  \\ disch_then drule \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (fv, t) refs`
  \\ `TERM defs fv` by
    fs [Abbr`fv`, mk_var_def, TERM_def, term_ok_def, TYPE_def]
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs t` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs ft` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs t` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (fv, pv)`
  \\ qpat_x_assum `TERM defs fv` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs pv` by fs [Abbr`pv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (fp, qv)`
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs qv` by fs [Abbr`qv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs fv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs fpq` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs fv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs ftt` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs (Abs _ fpq)` assume_tac
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs (Abs _ ftt)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs qv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs (Comb _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs (Abs _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_conj_thm:
   STATE defs refs /\
   TERM defs t2 /\
   TERM defs t1 /\
   mk_conj (t1, t2) refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_conj_def, st_ex_bind_def, case_eq_thms]
  \\ drule (GEN_ALL mk_conj_const_thm)
  \\ disch_then drule \\ rw []
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs c` kall_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac [mk_comb_thm]
QED

Theorem mk_imp_const_thm:
   STATE defs refs /\
   mk_imp_const () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_imp_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `mk_conj (pv, qv)`
  \\ `TERM defs qv /\ TERM defs pv` by
    fs [Abbr`pv`, Abbr`qv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ qpat_x_assum `TERM defs qv` assume_tac
  \\ drule (GEN_ALL mk_conj_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs qv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs (Comb _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs (Abs _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_imp_thm:
   STATE defs refs /\
   TERM defs t2 /\
   TERM defs t1 /\
   mk_imp (t1, t2) refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_imp_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule (GEN_ALL mk_imp_const_thm)
  \\ disch_then drule \\ rw []
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs imp` kall_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac [mk_comb_thm]
QED

Theorem mk_select_ax_thm:
   STATE defs refs /\
   TERM defs select_const /\
   mk_select_ax () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_select_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ qmatch_asmsub_abbrev_tac `mk_comb (pv, xv) refs`
  \\ drule STATE_lemma \\ strip_tac
  \\ qabbrev_tac `A = Tyvar (strlit"A")`
  \\ `TYPE defs A` by fs [Abbr`A`, TYPE_def, type_ok_def]
  \\ first_x_assum (qspecl_then [`A`,`Bool`] assume_tac) \\ rfs []
  \\ `TERM defs xv /\ TERM defs pv` by
    fs [Abbr`pv`, Abbr`xv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs xv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs select_const` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs sp` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_imp_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs px` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs xv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_ex_thm:
   STATE defs refs /\
   TYPE defs ty /\
   mk_ex ty refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_ex_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ first_x_assum (qspecl_then [`ty`,`Bool`] assume_tac) \\ rfs []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (pv, xv) refs`
  \\ `TERM defs pv`
    by fs [Abbr`pv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs xv`
    by fs [Abbr`xv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_imp (px, qv) refs`
  \\ `TERM defs qv`
    by fs [Abbr`qv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ drule (GEN_ALL mk_imp_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs px` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs xv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs qv` assume_tac
  \\ drule (GEN_ALL mk_imp_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs l` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs qv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs pv` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs all'` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED


Theorem mk_exists_thm:
   STATE defs refs /\
   TERM defs t2 /\
   TERM defs t1 /\
   mk_exists (t1, t2) refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_exists_def, st_ex_bind_def, case_eq_thms]
  \\ drule (GEN_ALL type_of_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_ex_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs t1` assume_tac
  \\ drule (GEN_ALL mk_abs_thm)
  \\ qpat_x_assum `TERM defs t2` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs ex` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs (Abs _ _)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_surj_thm:
   STATE defs refs /\
   TYPE defs d /\
   TYPE defs c /\
   TERM defs f /\
   mk_surj f d c refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_surj_def, st_ex_bind_def, case_eq_thms, st_ex_return_def]
  \\ drule (GEN_ALL type_of_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (f, xv) refs`
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs xv`
    by fs [Abbr`xv`, mk_var_def, TERM_def, TYPE_def, term_ok_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_eq (yv, fx) refs`
  \\ `TERM defs yv`
    by fs [Abbr`yv`, mk_var_def, TERM_def, TYPE_def, term_ok_def]
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs fx` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_exists_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs xv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs yv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_inj_thm:
   STATE defs refs /\
   TYPE defs d /\
   TERM defs f /\
   mk_inj f d refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_inj_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule (GEN_ALL type_of_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (f, xv) refs`
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs xv`
    by fs [Abbr`xv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_comb (f, yv) refs`
  \\ qpat_x_assum `TERM defs f` assume_tac
  \\ drule (GEN_ALL mk_comb_thm)
  \\ disch_then drule
  \\ `TERM defs yv`
    by fs [Abbr`yv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs fx` assume_tac
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs fy` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs xv` assume_tac
  \\ drule (GEN_ALL mk_eq_thm)
  \\ qpat_x_assum `TERM defs yv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_imp_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs (Comb _ fy)` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs yv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_forall_thm)
  \\ disch_then drule
  \\ qpat_x_assum `TERM defs xv` assume_tac
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_false_thm:
   STATE defs refs /\
   mk_false () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_false_def, st_ex_bind_def, st_ex_return_def]
  \\ drule STATE_lemma \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `mk_forall (p,_)`
  \\ `TERM defs p` by fs [Abbr`p`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ drule (GEN_ALL mk_forall_thm)
  \\ rpt (disch_then drule) \\ rw []
QED

Theorem mk_neg_const_thm:
   STATE defs refs /\
   mk_neg_const () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_neg_const_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ drule (GEN_ALL mk_false_thm)
  \\ disch_then drule \\ rw []
  \\ qmatch_asmsub_abbrev_tac `mk_imp (pv, f)`
  \\ drule (GEN_ALL mk_imp_thm)
  \\ disch_then drule
  \\ `TERM defs pv`
    by fs [Abbr`pv`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac [mk_abs_thm]
QED

Theorem mk_neg_thm:
   STATE defs refs /\
   TERM defs p /\
   mk_neg p refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_neg_def, st_ex_bind_def, case_eq_thms]
  \\ metis_tac [mk_neg_const_thm, mk_comb_thm]
QED

Theorem mk_infinity_ax_thm:
   STATE defs refs /\
   TYPE defs Ind /\
   mk_infinity_ax () refs = (res, refs')
   ==>
   refs = refs' /\
   !tm. res = Success tm ==> TERM defs tm
Proof
  rw [mk_infinity_ax_def, st_ex_bind_def, st_ex_return_def, case_eq_thms]
  \\ drule STATE_lemma \\ strip_tac
  \\ first_x_assum (qspecl_then [`Ind`,`Ind`] assume_tac) \\ rfs []
  \\ qmatch_asmsub_abbrev_tac `mk_surj f`
  \\ drule (GEN_ALL mk_surj_thm)
  \\ qpat_x_assum `TYPE defs Ind` assume_tac
  \\ `TERM defs f` by fs [Abbr`f`, TERM_def, TYPE_def, term_ok_def, mk_var_def]
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs f` assume_tac
  \\ drule (GEN_ALL mk_inj_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ qpat_x_assum `TERM defs surj` assume_tac
  \\ drule (GEN_ALL mk_neg_thm)
  \\ rpt (disch_then drule) \\ rw []
  \\ drule (GEN_ALL mk_conj_thm)
  \\ disch_then drule
  \\ ntac 2 (pop_assum kall_tac)
  \\ rpt (disch_then drule) \\ rw []
  \\ metis_tac [mk_exists_thm]
QED

Theorem init_reader_success:
   init_reader () init_refs = (res, refs) ==> res = Success ()
Proof
  EVAL_TAC \\ fs []
QED

Theorem init_reader_ok:
   init_reader () init_refs = (res, refs)
   ==>
   res = Success () /\
   ?defs. STATE defs refs
Proof
  simp [init_reader_success]
  \\ sg `STATE init_refs.the_context init_refs`
  >- (EVAL_TAC \\ rw [])
  \\ qmatch_asmsub_abbrev_tac `STATE defs`
  \\ rw [init_reader_def, st_ex_bind_def, ind_type_def, select_sym_def]
  \\ reverse (fs [case_eq_thms]) \\ rw [] \\ fs []
  \\ drule (GEN_ALL mk_eta_ax_thm)
  \\ disch_then drule \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ drule (GEN_ALL new_axiom_thm)
  \\ disch_then drule \\ fs [] \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ qpat_x_assum `mk_eta_ax () _ = _` kall_tac
  \\ qpat_x_assum `new_axiom _ init_refs = _` kall_tac
  \\ qmatch_asmsub_abbrev_tac `new_constant (nm1, ty)`
  \\ `TYPE (d::defs) ty` by
    (unabbrev_all_tac
     \\ fs [TYPE_def, STATE_def, CONTEXT_def, type_ok_def, init_refs_def]
     \\ fs [ml_hol_kernelProgTheory.init_context_def] \\ rfs [] \\ rveq
     \\ fs [init_ctxt_def, extends_def]
     \\ qpat_x_assum `_ = s.the_context` (assume_tac o GSYM) \\ fs []
     \\ fs [Once RTC_CASES1, ALOOKUP_APPEND, case_eq_thms]
     \\ fs [updates_cases])
  \\ drule (GEN_ALL new_constant_thm)
  \\ disch_then drule
  \\ disch_then (qspec_then `nm1` mp_tac) \\ fs [] \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ `TYPE (d'::d::defs) ty` by
   (drule STATE_lemma \\ strip_tac
    \\ qabbrev_tac `A = Tyvar (strlit"A")`
    \\ first_assum (qspecl_then [`Fun A Bool`, `A`] assume_tac)
    \\ first_x_assum (qspecl_then [`A`, `Bool`] assume_tac) \\ rfs []
    \\ fs [Abbr`A`, TYPE_def, type_ok_def])
  \\ `TERM (d'::d::defs) select_const` by
   (fs [new_constant_def, add_constants_def, get_the_term_constants_def,
        set_the_term_constants_def, raise_Fail_def, case_eq_thms,
        st_ex_bind_def, add_def_def]
    \\ FULL_CASE_TAC \\ rw []
    \\ fs [get_the_context_def, set_the_context_def] \\ rw []
    \\ fs [STATE_def, TERM_def] \\ rw [select_const_def]
    \\ fs [term_ok_def, FLOOKUP_DEF, CONTEXT_def, TYPE_def])
  \\ drule (GEN_ALL mk_select_ax_thm)
  \\ disch_then drule \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ drule (GEN_ALL new_axiom_thm)
  \\ disch_then drule \\ fs [] \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ qpat_x_assum `new_constant _ _ = _` kall_tac
  \\ qpat_x_assum `mk_select_ax _ _ = _` kall_tac
  \\ qmatch_asmsub_abbrev_tac `new_type (nm, ar)`
  \\ drule (GEN_ALL new_type_thm)
  \\ disch_then (qspecl_then [`nm`,`ar`] mp_tac) \\ fs [] \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ `TYPE (d'''::d''::d'::d::defs) Ind` by
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
    \\ fs [type_ok_def, FLOOKUP_DEF])
  \\ drule (GEN_ALL mk_infinity_ax_thm)
  \\ disch_then drule \\ rw []
  >- (asm_exists_tac \\ fs [])
  \\ drule (GEN_ALL new_axiom_thm)
  \\ disch_then drule \\ fs [] \\ rw []
  \\ fs [st_ex_return_def] \\ rw []
  \\ asm_exists_tac \\ fs []
QED

Theorem readLines_init_state_thm:
   init_reader () init_refs = (r, ax_refs) /\
   readLines lines init_state ax_refs = (res, refs)
   ==>
   ?defs.
     STATE defs refs /\
     !st n . res = Success (st, n) ==> READER_STATE defs st
Proof
  strip_tac
  \\ imp_res_tac init_reader_ok
  \\ sg `READER_STATE defs init_state`
  >- fs [init_state_def, READER_STATE_def, lookup_def]
  \\ metis_tac [readLines_thm]
QED

(* ------------------------------------------------------------------------- *)
(* Program specification (shared)                                            *)
(* ------------------------------------------------------------------------- *)

val process_line_def = Define`
  process_line st refs ln =
    if invalid_line ln then (INL st, refs) else
    case readLine (unescape_ml (fix_fun_typ (str_prefix ln))) st refs
    of (Success st, refs) => (INL st, refs)
     | (Failure (Fail s), refs) => (INR s, refs)`;

val process_lines_def = Define`
  (process_lines fd st refs fs [] =
    STDIO (add_stdout (fastForwardFD fs fd) (msg_success st refs.the_context)) *
    HOL_STORE refs) ∧
  (process_lines fd st refs fs (ln::ls) =
   case process_line st refs ln of
   | (INL st,refs) =>
       process_lines fd (next_line st) refs (lineForwardFD fs fd) ls
   | (INR e,refs)  =>
       STDIO (add_stderr (lineForwardFD fs fd) (line_Fail st e)) *
       HOL_STORE refs)`;

val process_list_def = Define `
  (process_list fs s refs [] =
     STDIO (add_stdout fs (msg_success s refs.the_context)) *
     HOL_STORE refs) /\
  (process_list fs s refs (l::ls) =
     case process_line s refs l of
       (INL s, refs) => process_list fs (next_line s) refs ls
     | (INR e, refs) => STDIO (add_stderr fs (line_Fail s e)) *
                        HOL_STORE refs)`;

val read_stdin_def = Define `
  read_stdin fs refs =
    let fs' = fastForwardFD fs 0 in
      case readLines (all_lines_inode fs (UStream (strlit"stdin"))) init_state refs of
        (Success (s, _), refs) =>
          (add_stdout fs' (msg_success s refs.the_context), refs, SOME s)
      | (Failure (Fail e), refs) => (add_stderr fs' e, refs, NONE)`;

val read_file_def = Define`
  read_file fs refs fnm =
    (if inFS_fname fs fnm then
       (case readLines (all_lines fs fnm) init_state refs of
        | (Success (s,_), refs) =>
            (add_stdout fs (msg_success s refs.the_context), refs, SOME s)
        | (Failure (Fail e), refs) => (add_stderr fs e, refs, NONE))
     else
       (add_stderr fs (msg_bad_name fnm), refs, NONE))`;

val reader_main_def = Define `
   reader_main fs refs cl =
     let refs = SND (init_reader () refs) in
       case cl of
         [] => read_stdin fs refs
       | [fnm] => read_file fs refs fnm
       | _ => (add_stderr fs msg_usage, refs, NONE)`;

(* ------------------------------------------------------------------------- *)
(* Specs imply that invariants are preserved.                                *)
(* ------------------------------------------------------------------------- *)

Theorem READER_STATE_init_state:
   READER_STATE defs init_state
Proof
  rw [READER_STATE_def, init_state_def, STATE_def, lookup_def]
QED

Theorem process_line_inv:
   STATE defs refs /\
   READER_STATE defs st /\
   process_line st refs ln = (res, refs')
   ==>
   ?ds.
     STATE (ds++defs) refs' /\
     !s. res = INL s ==> READER_STATE (ds++defs) s
Proof
   rw [process_line_def]
   >- (qexists_tac `[]` \\ fs [])
   \\ fs [case_eq_thms] \\ rw [] \\ fs []
   \\ drule (GEN_ALL readLine_thm)
   \\ rpt (disch_then drule) \\ rw []
QED

val flush_stdin_def = Define `
  flush_stdin cl fs =
   case cl of
      [] => fastForwardFD fs 0
    | _ => fs
  `;

val _ = export_rewrites ["flush_stdin_def"];

Theorem reader_proves:
   reader_main fs init_refs cl = (outp,refs,SOME s)
   ==>
   (!asl c.
      MEM (Sequent asl c) s.thms
      ==>
      (thyof refs.the_context, asl) |- c) /\
   outp = add_stdout (flush_stdin cl fs) (msg_success s refs.the_context) /\
   refs.the_context extends init_ctxt
Proof
  rw [reader_main_def, case_eq_thms, read_file_def, read_stdin_def,
      bool_case_eq, PULL_EXISTS]
  \\ Cases_on `init_reader () init_refs` \\ fs []
  \\ imp_res_tac init_reader_ok \\ rw []
  \\ `READER_STATE defs init_state` by fs [READER_STATE_init_state]
  \\ drule readLines_thm
  \\ rpt (disch_then drule) \\ rw []
  \\ fs [READER_STATE_def, EVERY_MEM]
  \\ first_x_assum (assume_tac o REWRITE_RULE [THM_def] o
                    Q.GENL [`a`,`b`] o Q.SPEC `Sequent a b`)
  \\ fs [STATE_def, CONTEXT_def] \\ rveq
  \\ fs [EQ_SYM_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Some things useful for the top-level soundness theorem, for instance:     *)
(* if there was no output on stderr, then reader_main processed all commands *)
(* in the article without errors.                                            *)
(* ------------------------------------------------------------------------- *)

val input_exists_def = Define `
  input_exists fs cl =
    case TL cl of
      [] => ?inp. stdin fs inp 0
    | _ => hasFreeFD fs
  `;

val _ = export_rewrites ["input_exists_def"];

Theorem readLines_Fail_not_empty:
   !ls st refs err refs'.
     readLines ls st refs = (Failure (Fail err), refs')
     ==>
     err <> strlit""
Proof
 recInduct readLines_ind
  \\ Cases >- rw [Once readLines_def, st_ex_return_def]
  \\ rw []
  \\ simp [Once readLines_def]
  \\ rw [st_ex_return_def, st_ex_bind_def, handle_Fail_def, raise_Fail_def,
         case_eq_thms, line_Fail_def, mlstringTheory.concat_def]
QED

val no_errors_def = Define `
  no_errors fs fs' <=>
    get_file_content fs 2 = get_file_content fs' 2`;

Theorem reader_success_stderr:
   input_exists fs cl /\
   STD_streams fs /\
   reader_main fs refs (TL cl) = (fs', refs', s) /\
   no_errors fs fs'
   ==>
   ?st. s = SOME st
Proof
 rw [reader_main_def, read_stdin_def, read_file_def, case_eq_thms,
      no_errors_def, msg_bad_name_def, msg_usage_def]
  \\ pop_assum mp_tac
  \\ fs [case_eq_thms, bool_case_eq] \\ rw [] \\ fs []
  \\ imp_res_tac TextIOProofTheory.STD_streams_stderr
  \\ fs [TextIOProofTheory.add_stdo_def, TextIOProofTheory.stdo_def,
         TextIOProofTheory.up_stdo_def, fsFFITheory.fsupdate_def,
         fsFFITheory.get_file_content_def,
         fsFFIPropsTheory.fastForwardFD_def, TextIOProofTheory.stdin_def]
  \\ fs [libTheory.the_def, UNCURRY, AFUPDKEY_ALOOKUP, case_eq_thms,
         bool_case_eq]
  \\ fs [mlstringTheory.concat_thm, msg_bad_name_def]
  \\ SELECT_ELIM_TAC \\ fs []
  \\ imp_res_tac readLines_Fail_not_empty
  \\ Cases_on `e` \\ fs []
QED

val _ = export_theory();

