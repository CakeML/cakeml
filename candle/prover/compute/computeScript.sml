(*
  Implementation of the compute primitive.
 *)

open preamble holSyntaxTheory holKernelTheory holKernelProofTheory
     ml_monadBaseTheory;
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
      Const n t => if n = «_0» then SOME 0 else NONE
    | Comb (Const nm t) r =>
        (case dest_num r of
        | NONE => NONE
        | SOME n => if nm = «BIT0» then SOME (2 * n)
                    else if nm = «BIT1» then SOME (2 * n + 1)
                    else NONE)
    | _ => NONE
End

Definition dest_numeral_def:
  dest_numeral tm =
    case tm of
      Comb (Const n t) r =>
        if n = «NUMERAL» then
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
    (* BIT0       *) _BIT0 _N === _ADD _N _N;
    (* BIT1       *) _BIT1 _N === _SUC (_ADD _N _N);
    (* ADD        *) _ADD _0 _M === _M;
    (* ADD        *) _ADD (_SUC _N) _M === _SUC (_ADD _N _M);
  ]
End

Theorem num_thms = SIMP_RULE list_ss [] num_thms_def;

Definition init_def:
  init ths =
    case ths of
      [] => T
    | h::t => EXISTS (aconv (concl h) o concl) num_thms ∧
              init t
End

Definition dest_binary_def:
  dest_binary nm tm =
    case tm of
      Comb (Comb (Const n t) l) r =>
        if n = nm then return (l, r)
        else failwith «dest_binary»
    | _ => failwith «dest_binary»
End

Definition compute_add_def:
  compute_add ths tm =
    if ¬ (init ths) then failwith «compute_add: no init» else
    do (l,r) <- dest_binary «+» tm;
       x <- dest_numeral l;
       y <- dest_numeral r;
       res <<- num2bit (x + y);
       c <- mk_eq (tm,res);
       return (Sequent [] c)
    od ++ failwith «compute_add»
End

Theorem dest_binary_thm:
  STATE ctxt s ∧
  TERM ctxt tm ⇒
  dest_binary nm tm s = (res,s') ⇒
    s' = s ∧
    ∀l r. res = M_success (l,r) ⇒
          TERM ctxt l ∧ TERM ctxt r
Proof
  rw [dest_binary_def, raise_Failure_def, st_ex_return_def]
  \\ every_case_tac \\ gs []
  \\ gs [TERM_def, term_ok_def]
QED

Theorem dest_numeral_thm:
  STATE ctxt s ∧
  TERM ctxt tm ⇒
  dest_numeral tm s = (res,s') ⇒
    s' = s
Proof
  rw [dest_numeral_def, raise_Failure_def, st_ex_return_def]
  \\ every_case_tac \\ gs []
QED

Theorem num2bit_thm:
  numeral_thy_ok (sigof ctxt, axsof ctxt) ⇒
    TERM ctxt (num2bit x)
Proof
  strip_tac \\ qid_spec_tac ‘x’
  \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ gs [numeral_thy_ok_def]
  \\ rw [Once num2bit_def] \\ gs []
  \\ fs [TERM_def] \\ simp [Once term_ok_def]
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
  \\ simp [Once st_ex_bind_def, otherwise_def]
  \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_binary_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ pairarg_tac \\ gvs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_numeral_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_all_then strip_assume_tac dest_numeral_thm \\ gvs []
  \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
  \\ drule_then (qspec_then ‘ctxt’ mp_tac) mk_eq_thm \\ gs []
  \\ impl_keep_tac
  >- (
    irule num2bit_thm
    \\ cheat (* init ths and EVERY (THM ctxt) ths means numeral_thy_ok.
                probably.
              *))
  \\ strip_tac \\ gvs []
  \\ rename [‘num2bit (x + y)’, ‘dest_binary _ _ s = (M_success(l,r), _)’]
  \\ CASE_TAC \\ fs [st_ex_return_def]
  \\ rw [] \\ rw [THM_def]
  \\ ‘tm = _ADD l r’
    by (qpat_x_assum ‘dest_binary _ tm _ = _’ mp_tac
        \\ simp [dest_binary_def, raise_Failure_def, st_ex_return_def]
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs []
        \\ IF_CASES_TAC \\ gs [] \\ rw []
        \\ cheat (* The term tm isn't type checked, but it contains a constant
                    named «+» and they have to have the same type. *))
  \\ gvs []
  \\ ‘term_type (_ADD l r) = num_ty’
    by (fs [STATE_def]
        \\ qpat_x_assum ‘TERM _ (_ADD _ _)’ assume_tac
        \\ drule_all term_type \\ gs [])
  \\ gvs []
  \\ ‘l = num2bit x ∧ r = num2bit y’
    by cheat (* Theorem relating dest_numeral and num2bit *)
  \\ gs []
  \\ irule (SIMP_RULE (srw_ss()) [equation_def] ADD_num2bit)
  \\ cheat (* numeral_thy_ok again *)
QED

val _ = export_theory ();

