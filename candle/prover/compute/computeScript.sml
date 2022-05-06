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
          | NONE => raise_Failure «dest_numeral»
          | SOME n => st_ex_return n
        else
          raise_Failure «dest_numeral»
    | _ => raise_Failure «dest_numeral»
End

Definition num_thms_def:
  num_thms = MAP (Sequent []) [
    (* T_DEF      *) _T === (Abs _X _X === Abs _X _X);
    (* FORALL_DEF *) _FORALL_TM === Abs _P (_P === Abs _X _T);
    (* NUMERAL    *) _NUMERAL _N === _N;
    (* BIT0       *) _BIT0 _N === _ADD _N _N;
    (* BIT1       *) _BIT1 _N === _SUC (_ADD _N _N);
    (* ADD        *) _ADD _0 _M === _M;
    (* ADD        *) _ADD (_SUC _N) _M === _SUC (_ADD _N _M);
  ]
End

Theorem num_thms = SIMP_RULE list_ss [] num_thms_def;

Definition init_def:
  init ths = EVERY (λth. MEM th ths) num_thms
End

Definition dest_binary_def:
  dest_binary tm' tm =
    case tm of
      Comb (Comb (Const n t) l) r =>
        if tm' = Const n t then return (l, r)
        else failwith «dest_binary»
    | _ => failwith «dest_binary»
End

Definition compute_add_def:
  compute_add ths tm =
    if ¬ (init ths) then failwith «compute_add: no init» else
    do (l,r) <- dest_binary _ADD_TM tm;
       x <- dest_numeral l;
       y <- dest_numeral r;
       res <<- num2bit (x + y);
       c <- mk_eq (tm,_NUMERAL res);
       return (Sequent [] c)
    od ++ failwith «compute_add»
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
  >- (
    IF_CASES_TAC \\ gs []
    >- (
      gs [Once num2bit_def, numeral_thy_ok_def]
      \\ cheat (* _0 === r ⇒ _0 === _BIT0 r *)
    )
    >- (
      cheat (* proves_MK_COMB *)
      )
  )
  \\ cheat (* proves_MK_COMB *)
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

Theorem init_thm:
  init ths ∧
  EVERY (THM ctxt) ths ⇒
    EVERY (THM ctxt) num_thms
Proof
  rw [init_def, EVERY_MEM]
QED

Theorem init_thy_ok:
  init ths ∧
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ⇒
    numeral_thy_ok (thyof ctxt) ∧
    bool_thy_ok (thyof ctxt)
Proof
  strip_tac
  \\ drule_all_then assume_tac init_thm
  \\ gs [num_thms_def, numeral_thy_ok_def, bool_thy_ok_def, STATE_def,
         CONTEXT_def, THM_def, extends_theory_ok, init_theory_ok, SF SFY_ss]
QED

Theorem compute_add_thm:
  STATE ctxt s ∧
  EVERY (THM ctxt) ths ∧
  TERM ctxt tm ⇒
  compute_add ths tm s = (res, s') ⇒
    s' = s ∧
    ∀th. res = M_success th ⇒ THM ctxt th
Proof
  simp [compute_add_def, raise_Failure_def]
  \\ IF_CASES_TAC \\ gs [] \\ strip_tac
  \\ drule_all_then strip_assume_tac init_thy_ok
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
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
  \\ ‘(thyof ctxt,[]) |- _NUMERAL l === num2bit x ∧
      (thyof ctxt,[]) |- _NUMERAL r === num2bit y’
    by (‘(thyof ctxt,[]) |- l === num2bit x ∧ (thyof ctxt,[]) |- r === num2bit y’
          suffices_by cheat (* TODO trans *)
        \\ gs [num2bit_dest_numeral, STATE_def, sym_equation])
  \\ ‘(thyof ctxt,[]) |- _ADD (_NUMERAL l) (_NUMERAL r) ===
                         _NUMERAL (num2bit (x + y))’
    suffices_by rw [equation_def]
  \\ ‘(thyof ctxt,[]) |- _ADD (num2bit x) (_NUMERAL r) ===
                         _NUMERAL (num2bit (x + y))’
    suffices_by cheat (* TODO replacement *)
  \\ ‘(thyof ctxt,[]) |- _ADD (num2bit x) (num2bit y) ===
                         _NUMERAL (num2bit (x + y))’
    suffices_by cheat (* TODO replacement *)
  \\ ‘(thyof ctxt,[]) |- _ADD (num2bit x) (num2bit y) ===
                         num2bit (x + y)’
    suffices_by cheat (* TODO replacement, _NUMERAL x === x *)
  \\ irule ADD_num2bit \\ gs []
QED

val _ = export_theory ();

