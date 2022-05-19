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
 * Theory initialization
 * ------------------------------------------------------------------------- *)

Definition compute_thms_def:
  compute_thms = MAP (Sequent []) [
    (* NUMERAL    *) _NUMERAL _N === _N;
    (* BIT0       *) _BIT0 _N === _ADD _N _N;
    (* BIT1       *) _BIT1 _N === _SUC (_ADD _N _N);
    (* ADD        *) _ADD (_NUMERAL _0) _N === _N;
    (* ADD        *) _ADD (_SUC _M) _N === _SUC (_ADD _M _N);
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                     _CVAL_NUM (_ADD _M _N);
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                     _CVAL_NUM _M;
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                     _CVAL_NUM _N;
    (* CVAL_ADD   *) _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                     _CVAL_NUM (_NUMERAL _0);
    (* CVAL_IF    *) _CVAL_IF (_CVAL_NUM (_SUC _M)) _P1 _Q1 === _P1;
    (* CVAL_IF    *) _CVAL_IF (_CVAL_PAIR _P2 _Q2) _P1 _Q1 === _P1;
    (* CVAL_IF    *) _CVAL_IF (_CVAL_NUM (_NUMERAL _0)) _P1 _Q1 === _Q1
  ]
End

Theorem compute_thms_def = SIMP_RULE list_ss [] compute_thms_def;

(*
Definition compute_init_def:
  compute_init ths = EVERY (λth. MEM th ths) compute_thms
End
 *)

Definition compute_init_def:
  compute_init ths ⇔ ths = compute_thms
End

Theorem compute_init_thy_ok:
  compute_init ths ∧
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ⇒
    compute_thy_ok (thyof ctxt)
Proof
  strip_tac
  \\ gvs [compute_init_def]
  \\ gs [compute_thms_def, compute_thy_ok_def, numeral_thy_ok_def, STATE_def,
         CONTEXT_def, THM_def, extends_theory_ok, init_theory_ok, SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * compute_add
 * ------------------------------------------------------------------------- *)

Definition compute_add_def:
  compute_add ths tm =
    if ¬ (compute_init ths) then
      failwith «compute_add: wrong theorems provided for initialization»
    else
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
  \\ ‘theory_ok (thyof ctxt) ∧ numeral_thy_ok (thyof ctxt)’ by fs []
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
    by gs [NUMERAL_eqn, TERM_def]
  \\ ‘(thyof ctxt,[]) |- _NUMERAL r === r’
    by gs [NUMERAL_eqn, TERM_def]
  \\ ‘(thyof ctxt,[]) |- _ADD (_NUMERAL l) (_NUMERAL r) ===
                         _NUMERAL (num2bit (x + y))’
    suffices_by rw [equation_def]
  \\ resolve_then Any irule sym_equation replaceL1
  \\ first_x_assum (irule_at Any)
  \\ resolve_then Any irule sym_equation replaceL2
  \\ first_x_assum (irule_at Any)
  \\ irule replaceL1 \\ first_x_assum (irule_at Any)
  \\ irule replaceL2 \\ first_x_assum (irule_at Any)
  \\ ‘numeral_thy_ok (thyof ctxt)’ by fs []
  \\ dxrule_then assume_tac num2bit_term_ok \\ fs []
  \\ resolve_then Any irule trans_equation_simple sym_equation
  \\ irule_at Any NUMERAL_eqn \\ rw [num2bit_ADD]
QED

(* -------------------------------------------------------------------------
 * compute
 * ------------------------------------------------------------------------- *)

Definition const_list_def:
  const_list (Var n) = [] ∧
  const_list (Num n) = [] ∧
  const_list (Pair x y) = const_list x ++ const_list y ∧
  const_list (Add x y) = const_list x ++ const_list y ∧
  const_list (If x y z) = const_list x ++ const_list y ++ const_list z ∧
  const_list (App s xs) = (s,LENGTH xs)::FLAT (MAP const_list xs)
Termination
  wf_rel_tac ‘measure compute_val_size’
End

Theorem const_list_ok[local]:
  ∀vs. set (const_list vs) = cval_consts vs
Proof
  ho_match_mp_tac const_list_ind
  \\ rw [const_list_def, cval_consts_def]
  \\ simp [Once EXTENSION]
  \\ rw [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  \\ eq_tac \\ rw [DISJ_EQ_IMP] \\ gs []
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum (irule_at Any) \\ gs []
QED

Definition var_list_def:
  var_list (Var n) = [n] ∧
  var_list (Num n) = [] ∧
  var_list (Pair x y) = var_list x ++ var_list y ∧
  var_list (Add x y) = var_list x ++ var_list y ∧
  var_list (If x y z) = var_list x ++ var_list y ++ var_list z ∧
  var_list (App s xs) = FLAT (MAP var_list xs)
Termination
  wf_rel_tac ‘measure compute_val_size’
End

Theorem var_list_ok[local]:
  ∀vs. set (var_list vs) = cval_vars vs
Proof
  ho_match_mp_tac var_list_ind
  \\ rw [var_list_def, cval_vars_def]
  \\ simp [Once EXTENSION]
  \\ rw [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  \\ eq_tac \\ rw [DISJ_EQ_IMP] \\ gs []
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum (irule_at Any) \\ gs []
QED

(* A valid equation is:
 *   [] |- const var1 ... varN = expr
 * where:
 * - var1 ... varN all have type cval_ty
 * - expr contains only the variables var1 ... varN, and has type cval_ty
 *)

Definition check_var_def:
  check_var (Var s ty) =
    (if ty = cval_ty then return s else
      failwith («Kernel.compute: ill-typed variable: » ^ s)) ∧
  check_var _ =
    failwith «Kernel.compute: non-variable argument on lhs of equation»
End

Definition check_eqn_def:
  check_eqn (Sequent h c) =
      do
        if h = [] then return () else
          failwith «Kernel.compute: non-empty hypotheses in equation»;
        (ls,r) <- dest_eq c;
        (f,vs) <- case list_dest_comb [] ls of
                  | f::vs => return (f,vs)
                  | _ => failwith «»;
        (nm,ty) <- dest_const f ++
                failwith «Kernel.compute: not a constant being applied on lhs»;
        args <- map check_var vs;
        case dest_cval r of
        | NONE => failwith «Kernel.compute: rhs is not a cval»
        | SOME cv =>
            do
              if EVERY (λv. MEM v args) (var_list cv) then return () else
                failwith «Kernel.compute: rhs contains free variable»;
              return (nm,args,cv)
            od
      od
End

Definition compute_default_clock:
  compute_default_clock = 1000000000
End

Definition check_consts_def:
  check_consts ars fn rhs =
    if EVERY (λ(c,n). MEM (c,n) ars) (const_list rhs) then return () else
    failwith («Kernel.compute: rhs of » ^ fn ^ « has a constant » ^
              «with no equation associated to it.»)
End

Definition compute_def:
  compute ths ceqs tm =
    flip handle_Clash (λe. failwith «impossible» ) $
    if ¬compute_init ths then
      failwith «Kernel.compute: wrong theorems provided for initialization»
    else
    case dest_cval tm of
    | NONE => failwith «Kernel.compute: term is not a compute_val»
    | SOME cval =>
        do
          ceqs <- map check_eqn ceqs;
          ars <<- MAP (λ(f,(n,r)). (f,LENGTH n)) ceqs;
          map (λ(f,(n,r)). check_consts ars f r) ceqs;
          case compute_eval_run compute_default_clock ceqs cval of
          | M_failure _ => failwith «Kernel.compute: timeout»
          | M_success res =>
              do
                c <- mk_eq (tm, cval2term res);
                return (Sequent [] c)
              od
        od
End

Theorem map_check_var_thm:
  ∀tms s res s'.
    STATE ctxt s ∧
    EVERY (TERM ctxt) tms ∧
    map check_var tms s = (res, s') ⇒
      s = s' ∧
      (∀tm. res ≠ M_failure (Clash tm)) ∧
      ∀ns.
        res = M_success ns ⇒
        LIST_REL (λtm n. tm = Var n cval_ty) tms ns
Proof
  Induct \\ simp [map_def, st_ex_return_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum ‘_ = (res,_)’ mp_tac
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ reverse CASE_TAC \\ gs []
  >- (
    strip_tac \\ gvs []
    \\ Cases_on ‘h’ \\ gs [check_var_def, raise_Failure_def, st_ex_return_def]
    \\ gvs [COND_RATOR, CaseEq "bool"])
  \\ Cases_on ‘h’ \\ gs [check_var_def, raise_Failure_def, st_ex_return_def]
  \\ gvs [COND_RATOR, CaseEq "bool"]
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ first_x_assum drule_all \\ rw []
  \\ gvs [CaseEq "exc"]
QED

Theorem check_eqn_thm:
  compute_thy_ok (thyof ctxt) ∧
  STATE ctxt s ∧
  THM ctxt th ∧
  check_eqn th s = (res, s') ⇒
    s = s' ∧
    (∀tm. res ≠ M_failure (Clash tm)) ∧
    ∀f vs r.
      res = M_success (f,vs,cv) ⇒
      ∃l r. th = Sequent [] (l === r) ∧
            list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                                  (MAP (λs. Var s cval_ty) vs) ∧
            dest_cval r = SOME cv ∧
            ∀v. v ∈ cval_vars cv ⇒ MEM v vs
Proof
  strip_tac
  \\ qpat_x_assum ‘check_eqn _ _ = _’ mp_tac
  \\ Cases_on ‘th’ \\ gvs [check_eqn_def]
  \\ simp [st_ex_return_def, raise_Failure_def, st_ex_ignore_bind_def]
  \\ IF_CASES_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ ‘TERM ctxt t’
    by (fs [THM_def, TERM_def]
        \\ drule proves_term_ok \\ rw [])
  \\ drule_all_then strip_assume_tac dest_eq_thm \\ gvs []
  \\ reverse CASE_TAC \\ gs [] >- (rw [] \\ strip_tac \\ gs [])
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ simp [otherwise_def, Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
  \\ ‘TERM ctxt h ∧ EVERY (TERM ctxt) t’
    by (fs [TERM_def]
        \\ drule_then strip_assume_tac term_ok_FOLDL_Comb
        \\ fs [EVERY_MEM, TERM_def])
  \\ drule_all_then strip_assume_tac dest_const_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def]
  \\ TOP_CASE_TAC
  \\ drule_all_then strip_assume_tac map_check_var_thm \\ gvs []
  \\ reverse TOP_CASE_TAC \\ gs [] >- (rpt strip_tac \\ gs [])
  \\ TOP_CASE_TAC \\ gs []
  \\ drule_then drule dest_cval_thm
  \\ impl_tac >- fs [TERM_def]
  \\ strip_tac
  \\ IF_CASES_TAC \\ gs [GSYM equation_def] \\ rw []
  \\ simp [equation_def]
  \\ irule_at Any LIST_EQ \\ gvs [LIST_REL_EL_EQN, EL_MAP]
  \\ gvs [EVERY_MEM, var_list_ok]
  \\ rename [‘tm = Const f (app_type (LENGTH tms))’]
  \\ qpat_x_assum ‘dest_const tm _ = _’ mp_tac
  \\ simp [dest_const_def, raise_Failure_def, st_ex_return_def]
  \\ CASE_TAC \\ gs [] \\ rw []
  \\ rename [‘FOLDL _ (Const f ty) xs’]
  \\ ‘LENGTH tms = LENGTH xs’
    by fs [map_LENGTH, SF SFY_ss]
  \\ gs [TERM_def]
  \\ ‘typeof (FOLDL Comb (Const f ty) xs) = cval_ty’
    by fs [term_ok_def, equation_def]
  \\ ‘∀tm.
        term_ok (sigof ctxt) tm ∧
        (∀x. MEM x xs ⇒ term_ok (sigof ctxt) x ∧ typeof x = cval_ty) ∧
        term_ok (sigof ctxt) (FOLDL Comb tm xs) ∧
        typeof (FOLDL Comb tm xs) = cval_ty ⇒
          typeof tm = app_type (LENGTH xs)’
    suffices_by (
      rw []
      \\ first_x_assum (qspec_then ‘Const f ty’ assume_tac)
      \\ gs [MEM_EL, PULL_EXISTS, SF SFY_ss])
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on ‘xs’ \\ simp [app_type]
  \\ rw [] \\ gs [SF DNF_ss]
  \\ drule_then strip_assume_tac term_ok_FOLDL_Comb
  \\ first_x_assum drule \\ gs [term_ok_def]
QED

Theorem map_check_eqn_thm:
  compute_thy_ok (thyof ctxt) ⇒
  ∀ceqs s res s'.
    STATE ctxt s ∧
    EVERY (THM ctxt) ceqs ∧
    map check_eqn ceqs s = (res, s') ⇒
      s = s' ∧
      (∀tm. res ≠ M_failure (Clash tm)) ∧
      ∀eqs. res = M_success eqs ⇒
        ∀n. n < LENGTH eqs ⇒
            ∃f vs cv l r.
              EL n eqs = (f,vs,cv) ∧
              EL n ceqs = Sequent [] (l === r) ∧
              list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                                    (MAP (λs. Var s cval_ty) vs) ∧
              dest_cval r = SOME cv ∧
              ∀v. v ∈ cval_vars cv ⇒ MEM v vs
Proof
  strip_tac
  \\ Induct \\ simp [map_def, st_ex_return_def, raise_Failure_def]
  \\ qx_gen_tac ‘th’
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘_ = (res,s')’ mp_tac
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac check_eqn_thm \\ gvs []
  \\ reverse CASE_TAC \\ gs [] >- (strip_tac \\ gvs [])
  \\ rename [‘check_eqn _ _ = (M_success p, _)’]
  \\ PairCases_on ‘p’ \\ fs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gvs []
  \\ CASE_TAC \\ gs [] \\ strip_tac \\ gvs []
  \\ Cases \\ gs []
QED

Theorem map_check_consts_thm:
  ∀ceqs s res s'.
    STATE ctxt s ∧
    map (λ(f,(n,r)). check_consts ars f r) ceqs s = (res, s') ⇒
      s = s' ∧
      (∀tm. res ≠ M_failure (Clash tm)) ∧
      ∀u. res = M_success u ⇒
        ∀f vs cv.
          MEM (f,vs,cv) ceqs ⇒ EVERY (λ(c,n). MEM (c,n) ars) (const_list cv)
Proof
  Induct \\ fs [map_def, check_consts_def, st_ex_return_def, raise_Failure_def]
  \\ qx_gen_tac ‘h’ \\ PairCases_on ‘h’
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘_ = (res,s')’ mp_tac
  \\ simp [Once st_ex_bind_def]
  \\ reverse IF_CASES_TAC \\ gs [] >- rw []
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ first_x_assum drule_all
  \\ strip_tac \\ gvs []
  \\ reverse CASE_TAC \\ gs [] \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem compute_thm:
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ∧
  EVERY (THM ctxt) ceqs ∧
  TERM ctxt tm ⇒
  compute ths ceqs tm s = (res, s') ⇒
    s' = s ∧
    (∀th. res = M_success th ⇒ THM ctxt th) ∧
    (∀tm. res ≠ M_failure (Clash tm))
Proof
  strip_tac
  \\ simp [compute_def, handle_Clash_def, raise_Failure_def, st_ex_return_def]
  \\ IF_CASES_TAC \\ gs []
  \\ gs []
  \\ drule_all_then strip_assume_tac compute_init_thy_ok
  \\ ‘theory_ok (thyof ctxt) ∧ numeral_thy_ok (thyof ctxt)’
    by fs []
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac map_check_eqn_thm \\ gvs []
  \\ reverse CASE_TAC \\ gs [] >- (CASE_TAC \\ gs [] \\ rw [])
  \\ simp [st_ex_ignore_bind_def]
  \\ qmatch_goalsub_abbrev_tac ‘map g a r’
  \\ Cases_on ‘map g a r’ \\ gs []
  \\ unabbrev_all_tac \\ gs []
  \\ drule_all_then strip_assume_tac map_check_consts_thm \\ gvs []
  \\ rename [‘map _ a r = (res,r)’]
  \\ reverse (Cases_on ‘res’) \\ gs [] >- (CASE_TAC \\ gs [] \\ rw [])
  \\ rename [‘compute_eval_run _ eqs cv’]
  \\ CASE_TAC \\ gs []
  \\ rename [‘compute_eval_run _ _ _ = M_success tm'’]
  \\ ‘term_ok (sigof (thyof ctxt)) tm’
    by fs [TERM_def]
  \\ drule_all_then strip_assume_tac dest_cval_thm
  \\ gs [EVERY_MEM, MEM_EL, PULL_EXISTS]
  \\ drule_then drule compute_eval_run_thm
  \\ impl_tac
  >- (cheat (* TODO *) (*
    rw []
    \\ imp_res_tac map_LENGTH \\ gs []
    \\ last_x_assum (drule_then strip_assume_tac) \\ gs []
    \\ last_x_assum (drule_then strip_assume_tac) \\ gs []
    \\ gs [THM_def, MEM_EL, SF SFY_ss] *))
  \\ strip_tac \\ gvs []
  \\ ‘TERM ctxt (cval2term tm')’
    by (drule cval2term_term_ok \\ simp [TERM_def])
  \\ simp [Once st_ex_bind_def]
  \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac mk_eq_thm \\ gvs []
  \\ reverse CASE_TAC >- (CASE_TAC \\ gs [] \\ rw [])
  \\ rw []
  \\ ‘term_type tm = cval_ty’
    by (fs [STATE_def]
        \\ qpat_x_assum ‘TERM ctxt tm’ assume_tac
        \\ drule_all term_type \\ gs [])
  \\ ‘(thyof ctxt,[]) |- tm === cval2term tm'’
    suffices_by rw [equation_def, THM_def]
  \\ resolve_then Any irule trans_equation_simple sym_equation
  \\ first_x_assum (irule_at Any) \\ gs [sym_equation]
QED

val _ = export_theory ();

