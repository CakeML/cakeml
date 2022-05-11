(*
  Implementation of the compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holKernelTheory
     holKernelProofTheory ml_monadBaseTheory;
open computeSyntaxTheory;

val _ = new_theory "compute";

val _ = numLib.prefer_num ();

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = SOME “raise_Failure”,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

Overload return[local] = “st_ex_return”;
Overload failwith[local] = “raise_Failure”;
Overload handle[local] = “handle_Failure”;

(* -------------------------------------------------------------------------
 * Destructuring
 * ------------------------------------------------------------------------- *)

Definition dest_num_def:
  dest_num tm =
    case tm of
      Const n t => if tm = _0 then SOME 0 else NONE
    | Comb (Const nm t) r =>
        (case dest_num r of
        | NONE => NONE
        | SOME n => if Const nm t = _BIT0_TM then SOME (2 * n)
                    else if Const nm t = _BIT1_TM then SOME (2 * n + 1)
                    else NONE)
    | _ => NONE
End

Definition dest_numeral_def:
  dest_numeral tm =
    case tm of
      Comb (Const n t) r =>
        if Const n t = _NUMERAL_TM then
          case dest_num r of
          | NONE => failwith «dest_numeral»
          | SOME n => return n
        else
          failwith «dest_numeral»
    | _ => failwith «dest_numeral»
End

Definition dest_numeral_opt_def:
  dest_numeral_opt tm =
    case tm of
      Comb (Const n t) r =>
        if Const n t = _NUMERAL_TM then
          case dest_num r of
          | NONE => NONE
          | SOME n => SOME n
        else
          NONE
    | _ => NONE
End

Definition dest_cval_def:
  dest_cval tm =
    case tm of
      Comb (Const n t) r =>
        if Const n t = _CVAL_NUM_TM then
          case dest_numeral_opt r of
          | NONE => NONE
          | SOME n => SOME (Num n)
        else if Const n t = _CVAL_FST_TM then
          case dest_cval r of
          | NONE => NONE
          | SOME p => SOME (Fst p)
        else if Const n t = _CVAL_SND_TM then
          case dest_cval r of
          | NONE => NONE
          | SOME p => SOME (Snd p)
        else
          NONE
    | Comb (Comb (Const n t) l) r =>
        if Const n t = _CVAL_PAIR_TM then
          case dest_cval l of
          | NONE => NONE
          | SOME p =>
              case dest_cval r of
              | NONE => NONE
              | SOME q => SOME (Pair p q)
        else if Const n t = _CVAL_ADD_TM then
          case dest_cval l of
          | NONE => NONE
          | SOME p =>
              case dest_cval r of
              | NONE => NONE
              | SOME q => SOME (Add p q)
        else
          NONE
    | _ => NONE
End

Definition dest_binary_def:
  dest_binary tm' tm =
    case tm of
      Comb (Comb (Const n t) l) r =>
        if tm' = Const n t then return (l, r)
        else failwith «dest_binary»
    | _ => failwith «dest_binary»
End

Theorem dest_binary_thm:
  STATE ctxt s ∧
  TERM ctxt tm ∧
  TERM ctxt tm' ⇒
  dest_binary tm' tm s = (res,s') ⇒
    s' = s ∧
    ∀l r. res = M_success (l,r) ⇒
          TERM ctxt l ∧ TERM ctxt r ∧
          tm = Comb (Comb tm' l) r
Proof
  simp [dest_binary_def, raise_Failure_def, st_ex_return_def]
  \\ strip_tac
  \\ rpt CASE_TAC \\ gs []
  \\ rw [] \\ gs [TERM_def, term_ok_def]
QED

Theorem dest_numeral_thm:
  STATE ctxt s ∧
  TERM ctxt tm ⇒
  dest_numeral tm s = (res,s') ⇒
    s' = s ∧
    ∀n. res = M_success n ⇒
        (numeral_thy_ok (thyof ctxt) ⇒ typeof tm = num_ty) ∧
        ∃tm'. tm = _NUMERAL tm' ∧ dest_num tm' = SOME n
Proof
  simp [dest_numeral_def, raise_Failure_def, st_ex_return_def]
  \\ strip_tac
  \\ rpt CASE_TAC \\ gs []
  \\ rw [SF SFY_ss]
QED

Theorem num2bit_thm:
  numeral_thy_ok (thyof ctxt) ⇒
    TERM ctxt (num2bit x)
Proof
  strip_tac \\ qid_spec_tac ‘x’
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ gs [numeral_thy_ok_def]
  \\ rw [Once num2bit_def] \\ gs []
  \\ fs [TERM_def] \\ simp [Once term_ok_def]
QED

Theorem dest_num_num2bit:
  numeral_thy_ok thy ⇒
  ∀x y.
    dest_num x = SOME y ⇒
      (thy,[]) |- num2bit y === x
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ ‘theory_ok thy’
    by fs [numeral_thy_ok_def]
  \\ ho_match_mp_tac dest_num_ind \\ rw []
  \\ qpat_x_assum ‘dest_num _ = _’ mp_tac
  \\ simp [Once dest_num_def]
  \\ rw [CaseEqs ["term", "option", "bool"]]
  \\ simp [Once num2bit_def, proves_REFL] \\ gs []
  \\ rw [] \\ simp [MK_COMB_simple, proves_REFL]
  \\ gs [Once num2bit_def]
  \\ irule trans_equation_simple
  \\ qexists_tac ‘_BIT0 _0’
  \\ simp [sym_equation, BIT0_0, numeral_thy_ok_def]
  \\ irule MK_COMB_simple \\ simp [proves_REFL]
QED

Theorem num2bit_dest_numeral:
  dest_numeral (_NUMERAL x) s = (M_success y, s') ∧
  numeral_thy_ok (thyof s.the_context) ⇒
    s = s' ∧ (thyof s.the_context,[]) |- num2bit y === x
Proof
  simp [dest_numeral_def, st_ex_return_def, raise_Failure_def]
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ drule_all dest_num_num2bit \\ rw []
QED

Theorem cval2term_dest_numeral_opt:
  dest_numeral_opt x = SOME y ∧
  compute_thy_ok thy ⇒
    (thy,[]) |- cval2term (Num y) === _CVAL_NUM x
Proof
  simp [dest_numeral_opt_def]
  \\ CASE_TAC \\ gs []
  \\ TOP_CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ ‘numeral_thy_ok thy’
    by gs [compute_thy_ok_def]
  \\ drule_all dest_num_num2bit \\ rw [cval2term_def]
  \\ drule_then assume_tac num2bit_term_ok
  \\ irule replaceR2 \\ fs []
  \\ irule_at Any sym_equation
  \\ irule_at Any NUMERAL_eqn
  \\ simp [compute_thy_ok_terms_ok]
  \\ ‘term_ok (sigof thy) t0 ∧ t0 has_type num_ty’
    by (drule proves_term_ok
        \\ fs [equation_def, term_ok_def, numeral_thy_ok_terms_ok]
        \\ rw [] \\ fs [WELLTYPED])
  \\ simp [term_ok_welltyped, WELLTYPED_LEMMA, Once term_ok_def,
           welltyped_def, numeral_thy_ok_terms_ok, SF SFY_ss]
  \\ irule MK_COMB_simple
  \\ simp [proves_REFL, term_ok_welltyped, WELLTYPED_LEMMA, Once term_ok_def,
           welltyped_def, compute_thy_ok_terms_ok, SF SFY_ss]
  \\ irule trans_equation_simple
  \\ irule_at Any sym_equation
  \\ first_x_assum (irule_at Any)
  \\ rw [NUMERAL_eqn, sym_equation]
QED

Theorem dest_cval_thm:
  compute_thy_ok thy ⇒
    ∀x y. dest_cval x = SOME y ⇒
          (thy,[]) |- cval2term y === x ∧
          typeof x = cval_ty
Proof
  strip_tac
  \\ ho_match_mp_tac dest_cval_ind \\ ntac 3 strip_tac
  \\ simp [Once dest_cval_def]
  \\ CASE_TAC \\ gs []
  \\ rpt TOP_CASE_TAC \\ gs []
  \\ rw [] \\ gvs [CaseEqs ["option"], cval2term_def,
                   cval2term_dest_numeral_opt, MK_COMB_simple, proves_REFL,
                   compute_thy_ok_terms_ok]
QED

(* -------------------------------------------------------------------------
 * Theory initialization
 * ------------------------------------------------------------------------- *)

Definition compute_thms_def:
  compute_thms = MAP (Sequent []) [
    (* T_DEF      *) _T === (Abs _X _X === Abs _X _X);
    (* FORALL_DEF *) _FORALL_TM === Abs _P (_P === Abs _X _T);
    (* NUMERAL    *) _NUMERAL _N === _N;
    (* BIT0       *) _BIT0 _N === _ADD _N _N;
    (* BIT1       *) _BIT1 _N === _SUC (_ADD _N _N);
    (* ADD        *) _ADD _0 _M === _M;
    (* ADD        *) _ADD (_SUC _N) _M === _SUC (_ADD _N _M);
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_ADD _M _N);
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM _M;
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM _N;
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_FST   *) _CVAL_FST (_CVAL_PAIR _P1 _Q1) === _P1;
    (* CVAL_FST   *) _CVAL_FST (_CVAL_NUM _N) === _CVAL_NUM (_NUMERAL _0);
    (* CVAL_SND   *) _CVAL_SND (_CVAL_PAIR _P1 _Q1) === _Q1;
    (* CVAL_SND   *) _CVAL_SND (_CVAL_NUM _N) === _CVAL_NUM (_NUMERAL _0);
  ]
End

Theorem compute_thms_def = SIMP_RULE list_ss [] compute_thms_def;

Definition compute_init_def:
  compute_init ths = EVERY (λth. MEM th ths) compute_thms
End

Theorem init_thm:
  compute_init ths ∧
  EVERY (THM ctxt) ths ⇒
    EVERY (THM ctxt) compute_thms
Proof
  rw [compute_init_def, EVERY_MEM]
QED

Theorem compute_init_thy_ok:
  compute_init ths ∧
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ⇒
    compute_thy_ok (thyof ctxt) ∧
    bool_thy_ok (thyof ctxt)
Proof
  strip_tac
  \\ drule_all_then assume_tac init_thm
  \\ gs [compute_thms_def, compute_thy_ok_def, numeral_thy_ok_def,
         bool_thy_ok_def, STATE_def, CONTEXT_def, THM_def, extends_theory_ok,
         init_theory_ok, SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * compute_add
 * ------------------------------------------------------------------------- *)

Definition compute_add_def:
  compute_add ths tm =
    if ¬ (compute_init ths) then failwith «compute_add: no init» else
    do (l,r) <- dest_binary _ADD_TM tm;
       x <- dest_numeral l;
       y <- dest_numeral r;
       res <<- num2bit (x + y);
       c <- mk_eq (tm,_NUMERAL res);
       return (Sequent [] c)
    od ++ failwith «compute_add»
End

Theorem compute_add_thm:
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ∧
  TERM ctxt tm ⇒
  compute_add ths tm s = (res, s') ⇒
    s' = s ∧
    (∀th. res = M_success th ⇒ THM ctxt th) ∧
    (∀tm. res ≠ M_failure (Clash tm))
Proof
  simp [compute_add_def, raise_Failure_def]
  \\ IF_CASES_TAC \\ gs [] \\ strip_tac
  \\ drule_all_then strip_assume_tac compute_init_thy_ok
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ ‘theory_ok (thyof ctxt) ∧ numeral_thy_ok (thyof ctxt)’
    by fs [compute_thy_ok_def, numeral_thy_ok_def]
  \\ simp [Once st_ex_bind_def, otherwise_def]
  \\ CASE_TAC \\ gs []
  \\ ‘TERM ctxt _ADD_TM’
    by gs [TERM_def]
  \\ drule_all_then strip_assume_tac dest_binary_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_numeral_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_numeral_thm \\ gvs []
  \\ CASE_TAC \\ gvs []
  \\ simp [Once st_ex_bind_def, st_ex_return_def] \\ CASE_TAC \\ gs []
  \\ rename [‘num2bit (x + y)’,
             ‘dest_binary _ (_ADD (_NUMERAL l) (_NUMERAL r)) s’]
  \\ ‘TERM ctxt (_NUMERAL (num2bit (x + y)))’
    by (‘TERM ctxt (num2bit (x + y))’
          suffices_by rw [TERM_def, term_ok_def]
        \\ simp [num2bit_thm])
  \\ drule_then (qspec_then ‘ctxt’ mp_tac) mk_eq_thm
  \\ impl_tac >- fs []
  \\ strip_tac \\ rveq
  \\ CASE_TAC \\ fs []
  \\ rw [] \\ rw [THM_def]
  \\ ‘term_type (_ADD (_NUMERAL l) (_NUMERAL r)) = num_ty’
    by (fs [STATE_def]
        \\ qpat_x_assum ‘TERM _ (_ADD _ _)’ assume_tac
        \\ drule_all term_type \\ gs [])
  \\ gvs []
  \\ fs [STATE_def]
  \\ dxrule num2bit_dest_numeral \\ fs [] \\ strip_tac
  \\ dxrule num2bit_dest_numeral \\ fs [] \\ strip_tac
  \\ gvs []
  \\ qmatch_asmsub_abbrev_tac ‘TERM ctxt _’
  \\ ‘TERM ctxt l ∧ TERM ctxt r’
    by gs [TERM_def, term_ok_def]
  \\ ‘l has_type num_ty ∧ r has_type num_ty’
    by gs [TERM_def, term_ok_def, WELLTYPED]
  \\ ‘(thyof ctxt,[]) |- _NUMERAL l === l’
    by (gs [numeral_thy_ok_def, TERM_def]
        \\ qpat_x_assum ‘_ |- _NUMERAL _N === _’ assume_tac
        \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[l,_N]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, holSyntaxLibTheory.REV_ASSOCD, equation_def])
  \\ ‘(thyof ctxt,[]) |- _NUMERAL r === r’
    by (gs [numeral_thy_ok_def, TERM_def]
        \\ qpat_x_assum ‘_ |- _NUMERAL _N === _’ assume_tac
        \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[r,_N]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, holSyntaxLibTheory.REV_ASSOCD, equation_def])
  \\ ‘(thyof ctxt,[]) |- _NUMERAL l === num2bit x ∧
      (thyof ctxt,[]) |- _NUMERAL r === num2bit y’
    by (irule_at Any trans_equation_simple
        \\ first_x_assum (irule_at Any)
        \\ irule_at (Pos last) trans_equation_simple
        \\ first_x_assum (irule_at Any)
        \\ gs [num2bit_dest_numeral, STATE_def, sym_equation])
  \\ ‘(thyof ctxt,[]) |- _ADD (_NUMERAL l) (_NUMERAL r) ===
                         _NUMERAL (num2bit (x + y))’
    suffices_by rw [equation_def]
  \\ drule_then assume_tac num2bit_term_ok
  \\ ‘(thyof ctxt,[]) |- num2bit (x + y) === _NUMERAL (num2bit (x + y))’
    by (gs [numeral_thy_ok_def, TERM_def]
        \\ qpat_x_assum ‘_ |- _NUMERAL _N === _’ assume_tac
        \\ dxrule_at_then (Pos (el 2))
                          (qspec_then ‘[num2bit (x + y),_N]’ mp_tac)
                          proves_INST
        \\ simp [VSUBST_def, holSyntaxLibTheory.REV_ASSOCD, equation_def,
                 sym_equation])
  \\ irule trans_equation_simple
  \\ first_x_assum (irule_at Any)
  \\ irule replaceL1 \\ fs []
  \\ qexists_tac ‘Comb _ADD_TM (num2bit x)’
  \\ simp [term_ok_def] \\ fs [TERM_def]
  \\ imp_res_tac term_ok_welltyped \\ fs []
  \\ simp [MK_COMB_simple, proves_REFL, sym_equation]
  \\ irule replaceL2 \\ fs []
  \\ qexists_tac ‘num2bit y’
  \\ simp [term_ok_def] \\ fs []
  \\ simp [MK_COMB_simple, proves_REFL, sym_equation, ADD_num2bit]
QED

(* -------------------------------------------------------------------------
 * numpair eval
 * ------------------------------------------------------------------------- *)

Definition compute_def:
  compute ths tm =
    if ¬ compute_init ths then failwith «Kernel.compute: no init» else
    case dest_cval tm of
    | NONE => failwith «Kernel.compute: term is not a compute_val»
    | SOME cval =>
        do
          res <<- cval2term (compute_eval cval);
          c <- mk_eq (tm, res);
          return (Sequent [] c)
        od
End

Theorem compute_thm:
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ∧
  TERM ctxt tm ⇒
  compute ths tm s = (res, s') ⇒
    s' = s ∧
    (∀th. res = M_success th ⇒ THM ctxt th) ∧
    (∀tm. res ≠ M_failure (Clash tm))
Proof
  strip_tac
  \\ simp [compute_def, raise_Failure_def]
  \\ IF_CASES_TAC \\ gs []
  \\ drule_all_then strip_assume_tac compute_init_thy_ok
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ ‘theory_ok (thyof ctxt) ∧ numeral_thy_ok (thyof ctxt)’
    by fs [compute_thy_ok_def, numeral_thy_ok_def]
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def, st_ex_return_def]
  \\ CASE_TAC \\ gs []
  \\ rename [‘compute_eval np’]
  \\ ‘TERM ctxt (cval2term (compute_eval np))’
    by (drule cval2term_term_ok \\ simp [TERM_def])
  \\ drule_all_then strip_assume_tac mk_eq_thm \\ gvs []
  \\ rename [‘mk_eq _ _ = (res,_)’]
  \\ ‘∀tm. res ≠ M_failure (Clash tm)’
    by (rpt strip_tac \\ fs [])
  \\ CASE_TAC \\ strip_tac \\ rveq \\ fs []
  \\ drule_all_then strip_assume_tac dest_cval_thm
  \\ ‘term_type tm = cval_ty’
    by (fs [STATE_def]
        \\ qpat_x_assum ‘TERM ctxt tm’ assume_tac
        \\ drule_all term_type \\ gs [])
  \\ ‘(thyof ctxt,[]) |- tm === cval2term (compute_eval np)’
    suffices_by rw [equation_def, THM_def]
  \\ irule trans_equation_simple
  \\ irule_at (Pos last) sym_equation
  \\ irule_at Any compute_eval_thm
  \\ gs [sym_equation]
QED

val _ = export_theory ();

