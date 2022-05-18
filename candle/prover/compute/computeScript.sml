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

Definition list_dest_comb_def:
  list_dest_comb sofar (Comb f x) = list_dest_comb (x::sofar) f ∧
  list_dest_comb sofar tm = tm::sofar
End

(*
EVAL “list_dest_comb [] (Comb (Comb (Comb (Const n t) b) c) d)”
 *)

Theorem list_dest_comb_not_nil[simp]:
  ∀sofar tm. list_dest_comb sofar tm ≠ []
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def]
QED

Theorem list_dest_comb_sing:
  ∀s x y. list_dest_comb s x = [y] ⇒ s = [] ∧ x = y
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def]
QED

Theorem list_dest_comb_unary:
  ∀s x y z.
    list_dest_comb s x = [y; z] ⇒
      (s = [z] ∧ x = y) ∨ (s = [] ∧ x = Comb y z)
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def]
QED

Theorem list_dest_comb_binary:
  ∀s x y z w.
    list_dest_comb s x = [y; z; w] ⇒
      (s = [] ∧ x = Comb (Comb y z) w) ∨
      (s = [w] ∧ x = Comb y z) ∨
      (s = [z; w] ∧ x = y)
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def] \\ gs [SF SFY_ss]
QED

Theorem list_dest_comb_ternary:
  ∀s x y z w v.
    list_dest_comb s x = [y; z; w; v] ⇒
      (s = [] ∧ x = Comb (Comb (Comb y z) w) v) ∨
      (s = [v] ∧ x = Comb (Comb y z) w) ∨
      (s = [w; v] ∧ x = Comb y z) ∨
      (s = [z; w; v] ∧ x = y)
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def] \\ gs [SF SFY_ss]
QED


Definition term_size_alt_def:
  term_size_alt (Comb s t) = term_size_alt s + term_size_alt t ∧
  term_size_alt (Abs s t) = term_size_alt s + term_size_alt t ∧
  term_size_alt _ = 1
End

Definition list_term_size_alt_def:
  list_term_size_alt [] = 0 ∧
  list_term_size_alt (x::xs) = term_size_alt x + list_term_size_alt xs
End

Theorem list_dest_comb_term_size[local]:
  ∀sofar tm res.
    list_dest_comb sofar tm = res ⇒
      list_term_size_alt res = list_term_size_alt sofar + term_size_alt tm
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def] \\ gs [list_term_size_alt_def, term_size_alt_def]
QED

Theorem list_term_size_MEM[local]:
  MEM x xs ⇒ term_size_alt x ≤ list_term_size_alt xs
Proof
  Induct_on ‘xs’
  \\ rw [list_term_size_alt_def] \\ fs []
QED

Definition mapOption_def:
  mapOption f [] = SOME [] ∧
  mapOption f (x::xs) =
    case f x of
    | NONE => NONE
    | SOME y =>
        case mapOption f xs of
        | NONE => NONE
        | SOME ys => SOME (y::ys)
End

Theorem mapOption_CONG[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      mapOption f xs = mapOption g ys
Proof
  Induct \\ rw [] \\ rw [mapOption_def]
  \\ TOP_CASE_TAC \\ gs [SF DNF_ss]
  \\ first_x_assum drule_all \\ rw []
QED

Definition dest_cval_def:
  dest_cval tm =
    case list_dest_comb [] tm of
    | [Var n ty] => if ty = cval_ty then SOME (Var n) else NONE
    | Const n ty :: args =>
        (case args of
        | [arg] =>
           if Const n ty = _CVAL_NUM_TM then
             case dest_numeral_opt arg of
             | NONE => NONE
             | SOME n => SOME (Num n)
           else if ty = Fun cval_ty cval_ty then
             case dest_cval arg of
             | NONE => NONE
             | SOME cv => SOME (App n [cv])
           else
             NONE
        | [l; r] =>
            (case dest_cval l of
            | NONE => NONE
            | SOME p =>
                case dest_cval r of
                | NONE => NONE
                | SOME q =>
                    if Const n ty = _CVAL_PAIR_TM then
                      SOME (Pair p q)
                    else if Const n ty = _CVAL_ADD_TM then
                       SOME (Add p q)
                    else if ty = Fun cval_ty (Fun cval_ty cval_ty) then
                      SOME (App n [p; q])
                    else
                      NONE)
        | [i; t; e] =>
            (case dest_cval i of
            | NONE => NONE
            | SOME p =>
                case dest_cval t of
                | NONE => NONE
                | SOME q =>
                    case dest_cval e of
                    | NONE => NONE
                    | SOME r =>
                        if Const n ty = _CVAL_IF_TM then
                          SOME (If p q r)
                        else if ty = Fun cval_ty
                                         (Fun cval_ty (Fun cval_ty cval_ty))
                             then SOME (App n [p; q; r])
                        else
                          NONE)
        | _ =>
            (case mapOption dest_cval args of
            | NONE => NONE
            | SOME cvs =>
                if ty = app_type (LENGTH cvs) then
                  SOME (App n cvs)
                else NONE))
    | _ => NONE
Termination
  wf_rel_tac ‘measure term_size_alt’ \\ rw []
  \\ drule_then assume_tac list_dest_comb_term_size
  \\ gs [list_term_size_alt_def, term_size_alt_def]
  \\ drule_then assume_tac list_term_size_MEM \\ gs []
End

(* TODO use term_size and list_size as measure instead *)

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

Theorem list_dest_comb_folds_back:
  ∀sofar tm h t.
    list_dest_comb sofar tm = h::t ⇒
      ∃xs. t = xs ++ sofar ∧
           FOLDL Comb h xs = tm
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def] \\ gvs [FOLDL_APPEND]
QED

Theorem dest_cval_thm:
  compute_thy_ok thy ⇒
    ∀tm cv.
      dest_cval tm = SOME cv ⇒
      (∀c n.
        (c,n) ∈ cval_consts cv ⇒
          term_ok (sigof thy) (Const c (app_type n))) ⇒
        (thy,[]) |- cval2term cv === tm ∧
        typeof tm = cval_ty
Proof
  strip_tac
  \\ ho_match_mp_tac dest_cval_ind
  \\ ntac 3 strip_tac \\ simp [Once dest_cval_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  >- ((* variable *)
    fs [CaseEqs ["list", "option"]]
    \\ strip_tac \\ gvs []
    \\ drule_then strip_assume_tac list_dest_comb_sing
    \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ fs [cval2term_def, proves_REFL, term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* 0-ary *)
    simp [mapOption_def]
    \\ strip_tac \\ fs []
    \\ drule_then strip_assume_tac list_dest_comb_sing
    \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ strip_tac
    \\ gvs [cval2term_def, cval_consts_def, app_type, proves_REFL])
  \\ TOP_CASE_TAC
  >- ((* unary: num or app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ strip_tac \\ gvs []
    \\ drule_then strip_assume_tac list_dest_comb_unary \\ gvs []
    \\ gvs [cval2term_dest_numeral_opt] \\ gvs [cval2term_def]
    \\ strip_tac
    \\ gvs [cval_consts_def, app_type_def, SF DNF_ss]
    \\ irule MK_COMB_simple \\ simp [proves_REFL])
  \\ TOP_CASE_TAC
  >- ((* binary: add, pair, app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ strip_tac \\ gvs []
    \\ drule_then strip_assume_tac list_dest_comb_binary \\ gvs []
    \\ gvs [cval2term_def, MK_COMB_simple, proves_REFL,
            compute_thy_ok_terms_ok]
    \\ strip_tac \\ gvs [SF DNF_ss, cval_consts_def, app_type_def]
    \\ irule MK_COMB_simple \\ gs [numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL \\ simp [compute_thy_ok_terms_ok])
  \\ TOP_CASE_TAC
  >- ((* ternary: if *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ strip_tac \\ gvs []
    \\ drule_then strip_assume_tac list_dest_comb_ternary \\ gvs []
    \\ gvs [cval2term_def]
    \\ strip_tac \\ gvs [cval_consts_def, app_type_def, SF DNF_ss]
    \\ irule MK_COMB_simple \\ fs [numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ fs []
    \\ irule MK_COMB_simple \\ fs [compute_thy_ok_terms_ok, proves_REFL])
      (* n-ary: app *)
  \\ fs [CaseEqs ["list", "option", "bool"], SF ETA_ss]
  \\ strip_tac \\ gvs []
  \\ qmatch_asmsub_abbrev_tac ‘mapOption _ tms’
  \\ rename [‘tms = a::b::c::d::e’]
  \\ ‘∀tm. tm = a ∨ tm = b ∨ tm = c ∨ tm = d ∨ MEM tm e ⇔ MEM tm tms’
    by gs [Abbr ‘tms’]
  \\ fs []
  \\ ntac 2 (pop_assum kall_tac)
  \\ strip_tac
  \\ gvs [cval_consts_def, MEM_MAP, SF DNF_ss]
  \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
  \\ simp [cval2term_def,FOLDL_MAP]
  \\ cheat (* Annoying FOLDL case *)
QED

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

Definition compute_default_clock:
  compute_default_clock = 1000000000
End

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
        (* TODO: check that r only contains variables in args *)
        case dest_cval r of
        | NONE => failwith «Kernel.compute: rhs is not a cval»
        | SOME cv => return (nm,args,cv)
      od
End

Definition compute_def:
  compute ths ceqs tm =
    if ¬compute_init ths then
      failwith «Kernel.compute: wrong theorems provided for initialization»
    else
    case dest_cval tm of
    | NONE => failwith «Kernel.compute: term is not a compute_val»
    | SOME cval =>
        do
          ceqs <- map check_eqn ceqs;
          case compute_eval_run compute_default_clock ceqs cval of
          | M_failure _ => failwith «Kernel.compute: timeout»
          | M_success res =>
              do
                c <- mk_eq (tm, cval2term res);
                return (Sequent [] c)
              od
        od
End

(* TODO *)

(*
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
    by fs []
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
  \\ resolve_then Any irule trans_equation_simple sym_equation
  \\ irule_at Any compute_eval_thm \\ rw []
QED
 *)

val _ = export_theory ();

