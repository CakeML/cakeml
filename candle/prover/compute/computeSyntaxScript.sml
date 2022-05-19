(*
   Definitions of term embeddings for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory;
open ml_monadBaseTheory ml_monadBaseLib;

val _ = new_theory "computeSyntax";

val _ = numLib.prefer_num ();

fun SIMPR ths = SIMP_RULE (srw_ss()) ths;
fun SIMPC ths = SIMP_CONV (srw_ss()) ths;

(* Numbers *)

Overload num_ty = “Tyapp «num» []”;
Overload "_0" = “Const «_0» num_ty”;
Overload "_SUC_TM" = “Const «SUC» (Fun num_ty num_ty)”;
Overload "_SUC" = “λtm. Comb _SUC_TM tm”;
Overload "_BIT0_TM" = “Const «BIT0» (Fun num_ty num_ty)”;
Overload "_BIT0" = “λtm. Comb _BIT0_TM tm”;
Overload "_BIT1_TM" = “Const «BIT1» (Fun num_ty num_ty)”;
Overload "_BIT1" = “λtm. Comb _BIT1_TM tm”;
Overload "_N" = “Var «n» num_ty”;
Overload "_M" = “Var «m» num_ty”;
Overload "_ADD_TM" = “Const «+» (Fun num_ty (Fun num_ty num_ty))”;
Overload "_ADD" = “λt1 t2. Comb (Comb _ADD_TM t1) t2”;
Overload "_NUMERAL_TM" = “Const «NUMERAL» (Fun num_ty num_ty)”;
Overload "_NUMERAL" = “λtm. Comb _NUMERAL_TM tm”;

(* Pairs *)

Overload cval_ty = “Tyapp «cval» []”;
Overload cval_list_ty = “Tyapp «list» [cval_ty]”;
Overload "_P1" = “Var «p1» cval_ty”;
Overload "_P2" = “Var «p2» cval_ty”;
Overload "_Q1" = “Var «q1» cval_ty”;
Overload "_Q2" = “Var «q2» cval_ty”;
Overload "_CS" = “Var «cs» cval_list_ty”;
Overload "_CVAL_NIL_TM" = “Const «[]» cval_list_ty”;
Overload "_CVAL_CONS_TM" =
  “Const «::» (Fun cval_ty (Fun cval_list_ty cval_list_ty))”;
Overload "_CVAL_CONS" = “λt1 t2. Comb (Comb _CVAL_CONS_TM t1) t2”;
Overload "_CVAL_NUM_TM" = “Const «cval_num» (Fun num_ty cval_ty)”;
Overload "_CVAL_NUM" = “λtm. Comb _CVAL_NUM_TM tm”;
Overload "_CVAL_PAIR_TM" =
  “Const «cval_pair» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_PAIR" = “λt1 t2. Comb (Comb _CVAL_PAIR_TM t1) t2”;
Overload "_CVAL_VAR_TM" = “Const «cval_var» (Fun string_ty cval_ty)”
Overload "_CVAL_VAR" = “λtm. Comb _CVAL_VAR_TM tm”
Overload "_CVAL_ADD_TM" =
  “Const «cval_add» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_ADD" = “λt1 t2. Comb (Comb _CVAL_ADD_TM t1) t2”;
Overload "_CVAL_APP_TM" =
  “Const «cval_app» (Fun string_ty (Fun cval_list_ty cval_ty))”;
Overload "_CVAL_APP" = “λt1 t2. Comb (Comb _CVAL_APP_TM t1) t2”;
Overload "_CVAL_IF_TM" =
  “Const «cval_if» (Fun cval_ty (Fun cval_ty (Fun cval_ty cval_ty)))”;
Overload "_CVAL_IF" = “λt1 t2 t3. Comb (Comb (Comb _CVAL_IF_TM t1) t2) t3”;

(* -------------------------------------------------------------------------
 * Support
 * ------------------------------------------------------------------------- *)

Theorem trans_equation_simple:
  (thy,[]) |- a === b ∧
  (thy,[]) |- b === c ⇒
    (thy,[]) |- a === c
Proof
  rw []
  \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
  \\ simp [ACONV_REFL, SF SFY_ss]
QED

Theorem MK_COMB_simple =
  Q.SPECL [‘[]’,‘[]’] proves_MK_COMB |> SIMPR [PULL_EXISTS];

Theorem replaceL1:
  (thy,[]) |- x === y ∧
  (thy,[]) |- Comb (Comb f x) r === z ⇒
    (thy,[]) |- Comb (Comb f y) r === z
Proof
  rw []
  \\ ‘theory_ok thy ∧
      EVERY (term_ok (sigof thy)) [f;x;y;r;z] ∧
      typeof x = typeof y ∧
      (∃ty. typeof f = Fun (typeof y) (Fun (typeof r) ty))’
    by (imp_res_tac proves_term_ok
        \\ imp_res_tac proves_theory_ok
        \\ gs [term_ok_def, equation_def])
  \\ irule trans_equation_simple \\ fs []
  \\ first_x_assum (irule_at Any)
  \\ simp [MK_COMB_simple, Once sym_equation, term_ok_welltyped, proves_REFL,
           SF SFY_ss]
QED

Theorem replaceL2:
  (thy,[]) |- x === y ∧
  (thy,[]) |- Comb f x === z ⇒
    (thy,[]) |- Comb f y === z
Proof
  rw []
  \\ ‘theory_ok thy ∧
      EVERY (term_ok (sigof thy)) [f;x;y;z] ∧
      typeof x = typeof y ∧
      (∃ty. typeof f = Fun (typeof y) ty)’
    by (imp_res_tac proves_term_ok
        \\ imp_res_tac proves_theory_ok
        \\ gs [term_ok_def, equation_def])
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any) \\ fs []
  \\ simp [MK_COMB_simple, term_ok_welltyped, proves_REFL, sym_equation,
           SF SFY_ss]
QED

Theorem replaceL3:
  (thy,[]) |- x === y ∧
  (thy,[]) |- Comb (Comb (Comb f x) s) t === z ⇒
    (thy,[]) |- Comb (Comb (Comb f y) s) t === z
Proof
  rw []
  \\ ‘theory_ok thy ∧
      EVERY (term_ok (sigof thy)) [f;x;y;z;s;t] ∧
      typeof x = typeof y ∧
      (∃ty. typeof f = Fun (typeof y) (Fun (typeof s) (Fun (typeof t) ty)))’
    by (imp_res_tac proves_term_ok
        \\ imp_res_tac proves_theory_ok
        \\ gs [term_ok_def, equation_def])
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any) \\ fs []
  \\ simp [MK_COMB_simple, term_ok_welltyped, proves_REFL, sym_equation,
           SF SFY_ss]
QED

Theorem replaceR1 =
  UNDISCH_ALL replaceL1 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR2 =
  UNDISCH_ALL replaceL2 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR3 =
  UNDISCH_ALL replaceL3 |> MATCH_MP sym_equation |> DISCH_ALL;

(* -------------------------------------------------------------------------
 * Natural numbers
 * ------------------------------------------------------------------------- *)

(* All the necessary constants defined with the right types and
 * with the right defining equations (and some lemmas).
 *)

Definition numeral_thy_ok_def:
  numeral_thy_ok thy ⇔
    (* NUMERAL *)
    (thy,[]) |- _NUMERAL _N === _N ∧
    (* BIT0, BIT1 *)
    (thy,[]) |- _BIT0 _N === _ADD _N _N ∧
    (thy,[]) |- _BIT1 _N === _SUC (_ADD _N _N) ∧
    (* ADD *)
    (thy,[]) |- _ADD (_NUMERAL _0) _N === _N ∧
    (thy,[]) |- _ADD (_SUC _M) _N === _SUC (_ADD _M _N)
End

Theorem numeral_thy_ok_theory_ok[simp]:
  numeral_thy_ok thy ⇒ theory_ok thy
Proof
  rw [numeral_thy_ok_def]
  \\ drule proves_theory_ok \\ simp []
QED

Theorem numeral_thy_ok_terms_ok:
  numeral_thy_ok thy ⇒
    term_ok (sigof thy) _ADD_TM ∧
    term_ok (sigof thy) _0 ∧
    term_ok (sigof thy) _SUC_TM ∧
    term_ok (sigof thy) _BIT0_TM ∧
    term_ok (sigof thy) _BIT1_TM ∧
    term_ok (sigof thy) _NUMERAL_TM
Proof
  simp [numeral_thy_ok_def] \\ strip_tac
  \\ pop_assum kall_tac
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ fs [equation_def, term_ok_def, SF SFY_ss]
QED

(* The numeral_thy_ok theorems with object variables replaced with meta
   variables.
 *)

Theorem NUMERAL_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type num_ty ⇒
    (thy,[]) |- _NUMERAL n === n
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _NUMERAL x === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem BIT0_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type num_ty ⇒
    (thy,[]) |- _BIT0 n === _ADD n n
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _BIT0 x === _ADD x x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem BIT1_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type num_ty ⇒
    (thy,[]) |- _BIT1 n === _SUC (_ADD n n)
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _BIT1 _ === _SUC _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem ADD_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type num_ty ∧ n has_type num_ty ⇒
    (thy,[]) |- _ADD (_NUMERAL _0) n === n ∧
    (thy,[]) |- _ADD (_SUC m) n === _SUC (_ADD m n)
Proof
  rw [numeral_thy_ok_def]
  >- (
    qpat_x_assum ‘_ |- _ADD (_NUMERAL _) _ === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def])
  \\ qpat_x_assum ‘_ |- _ADD (_SUC _) _ === _SUC _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M; n,_N]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem BIT0_0:
  numeral_thy_ok thy ⇒
    (thy,[]) |- _BIT0 _0 === _0
Proof
  strip_tac
  \\ ‘term_ok (sigof thy) _0 ∧ _0 has_type num_ty’
    by gs [numeral_thy_ok_terms_ok, term_ok_def, has_type_rules]
  \\ drule_all_then assume_tac BIT0_eqn
  \\ irule trans_equation_simple
  \\ first_x_assum (irule_at Any)
  \\ drule_all_then assume_tac (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL ADD_eqn)))
  \\ irule replaceL1
  \\ irule_at Any NUMERAL_eqn \\ simp []
QED

Definition num2term_def:
  num2term 0 = _0 ∧
  num2term (SUC n) = _SUC (num2term n)
End

Theorem num2term_typeof[local,simp]:
  typeof (num2term n) = num_ty
Proof
  Induct_on ‘n’ \\ simp [num2term_def]
QED

Theorem num2term_has_type[local,simp]:
  num2term n has_type num_ty
Proof
  Induct_on ‘n’ \\ rw [num2term_def]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
QED

Theorem num2term_welltyped[local,simp]:
  welltyped (num2term n)
Proof
  rw [welltyped_def, num2term_has_type, SF SFY_ss]
QED

Theorem num2term_term_ok[local]:
  numeral_thy_ok thy ⇒ term_ok (sigof thy) (num2term n)
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ Induct_on ‘n’ \\ rw [numeral_thy_ok_def, term_ok_def, num2term_def]
QED

Theorem num2term_VSUBST[local,simp]:
  ∀n. VSUBST is (num2term n) = num2term n
Proof
  Induct \\ rw [num2term_def, VSUBST_def]
QED

Definition num2bit_def:
  num2bit n =
    if n = 0 then _0 else
    Comb (if n MOD 2 = 0 then _BIT0_TM else _BIT1_TM) (num2bit (n DIV 2))
Termination
  wf_rel_tac ‘$<’ \\ intLib.ARITH_TAC
End

Theorem num2bit_typeof[simp]:
  ∀n. typeof (num2bit n) = num_ty
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def]
QED

Theorem num2bit_has_type[simp]:
  ∀n. num2bit n has_type num_ty
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def]
  \\ rw [Ntimes has_type_cases 3]
QED

Theorem num2bit_welltyped[simp]:
  ∀n. welltyped (num2bit n)
Proof
  rw [welltyped_def, num2bit_has_type, SF SFY_ss]
QED

Theorem num2bit_term_ok:
  numeral_thy_ok thy ⇒ term_ok (sigof thy) (num2bit n)
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ qid_spec_tac ‘n’
  \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def, term_ok_def]
QED

Theorem num2bit_VSUBST[simp]:
  ∀n. VSUBST is (num2bit n) = num2bit n
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ once_rewrite_tac [num2bit_def]
  \\ rw [VSUBST_def]
QED

Theorem num2term_ADD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2term (m + n) === _ADD (num2term m) (num2term n)
Proof
  strip_tac \\ irule sym_equation \\ qid_spec_tac ‘m’
  \\ Induct \\ simp []
  >- (
    rw [num2term_def]
    \\ qabbrev_tac ‘M = num2term n’
    \\ irule replaceL1
    \\ irule_at Any NUMERAL_eqn
    \\ simp [numeral_thy_ok_terms_ok, has_type_rules]
    \\ ‘term_ok (sigof thy) M ∧ M has_type num_ty’
      by fs [Abbr ‘M’, num2term_term_ok]
    \\ rw [ADD_eqn, SF SFY_ss])
  \\ rw [ADD_CLAUSES, num2term_def] \\ fs []
  \\ qmatch_goalsub_abbrev_tac ‘_ADD (_SUC N) M’
  \\ ‘term_ok (sigof thy) M ∧ M has_type num_ty ∧
      term_ok (sigof thy) N ∧ N has_type num_ty’
      by fs [Abbr ‘M’, Abbr ‘N’, num2term_term_ok]
  \\ irule replaceR2
  \\ first_x_assum (irule_at Any)
  \\ csimp [numeral_thy_ok_terms_ok, term_ok_def, term_ok_welltyped,
            num2term_term_ok, WELLTYPED_LEMMA, SF SFY_ss]
  \\ rw [ADD_eqn, sym_equation, SF SFY_ss]
QED

Theorem ADD_num2term =
  UNDISCH_ALL num2term_ADD |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2bit_num2term:
  numeral_thy_ok thy ⇒
    ∀n. (thy,[]) |- num2bit n === num2term n
Proof
  strip_tac \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ ‘term_ok (sigof thy) _0 ∧ _0 has_type num_ty’
    by fs [numeral_thy_ok_terms_ok, has_type_rules]
  \\ rw [num2term_def, Once num2bit_def, proves_REFL]
  >- (
    qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘term_ok (sigof thy) N ∧ N has_type num_ty’
      by fs [Abbr ‘N’, num2term_term_ok]
    \\ ‘(thy,[]) |- _BIT0 (num2bit (n DIV 2)) === _BIT0 N’
      by rw [MK_COMB_simple, proves_REFL, numeral_thy_ok_terms_ok]
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ ‘(thy,[]) |- _ADD N N === num2term n’
      suffices_by (
        strip_tac
        \\ irule trans_equation_simple
        \\ first_x_assum (irule_at Any)
        \\ simp [BIT0_eqn])
    \\ fs [Abbr ‘N’]
    \\ ‘num2term n = num2term (n DIV 2 + n DIV 2)’
      by (AP_TERM_TAC \\ intLib.ARITH_TAC)
    \\ pop_assum SUBST1_TAC
    \\ irule_at Any ADD_num2term \\ fs [])
  >- (
    qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘term_ok (sigof thy) N ∧ N has_type num_ty’
      by fs [Abbr ‘N’, num2term_term_ok]
    \\ ‘(thy,[]) |- _BIT1 (num2bit (n DIV 2)) === _BIT1 N’
      by rw [MK_COMB_simple, proves_REFL, numeral_thy_ok_terms_ok]
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ ‘(thy,[]) |- _SUC (_ADD N N) === num2term n’
      suffices_by (
        strip_tac
        \\ irule trans_equation_simple
        \\ first_x_assum (irule_at Any)
        \\ simp [BIT1_eqn])
    \\ ‘num2term n = _SUC (num2term (2 * (n DIV 2)))’
      by (‘n = SUC (n DIV 2 + n DIV 2)’ by intLib.ARITH_TAC
          \\ pop_assum (fn th => simp [SimpLHS, Once th])
          \\ simp [num2term_def])
    \\ pop_assum SUBST1_TAC
    \\ irule MK_COMB_simple
    \\ simp [term_ok_welltyped, WELLTYPED_LEMMA, proves_REFL,
             numeral_thy_ok_terms_ok, SF SFY_ss]
    \\ qunabbrev_tac ‘N’
    \\ ‘2 * (n DIV 2) = n DIV 2 + n DIV 2’
      by rw []
    \\ pop_assum SUBST1_TAC
    \\ rw [ADD_num2term])
QED

Theorem num2bit_ADD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m + n) === _ADD (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ irule trans_equation_simple
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceR1 \\ irule_at Any sym_equation
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceL2
  \\ irule_at Any sym_equation \\ irule_at Any num2bit_num2term
  \\ fs [ADD_num2term]
QED

Theorem ADD_num2bit =
  UNDISCH_ALL num2bit_ADD |> MATCH_MP sym_equation |> DISCH_ALL;

(* -------------------------------------------------------------------------
 * Compute values
 * ------------------------------------------------------------------------- *)

Datatype:
  compute_val = Pair compute_val compute_val
              | Num num
              | Var mlstring
              | App mlstring (compute_val list)
              | If compute_val compute_val compute_val
                (* operations that rely on host-language features *)
              | Add compute_val compute_val
End

(* The semantics of 'ill-typed' operations on the compute_val type is to
 * return the number 0 (i.e. Num 0n).
 *)

Definition compute_thy_ok_def:
  compute_thy_ok thy ⇔
    numeral_thy_ok thy ∧
    (* cval_add *)
    (thy,[]) |- _CVAL_ADD (_CVAL_NUM _M) (_CVAL_NUM _N) ===
                _CVAL_NUM (_ADD _M _N) ∧
    (thy,[]) |- _CVAL_ADD (_CVAL_NUM _M) (_CVAL_PAIR _P1 _Q1) ===
                _CVAL_NUM _M ∧
    (thy,[]) |- _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_NUM _N) ===
                _CVAL_NUM _N ∧
    (thy,[]) |- _CVAL_ADD (_CVAL_PAIR _P1 _Q1) (_CVAL_PAIR _P2 _Q2) ===
                _CVAL_NUM (_NUMERAL _0) ∧
    (* if-then-else *)
    (thy,[]) |- _CVAL_IF (_CVAL_NUM (_SUC _M)) _P1 _Q1 === _P1 ∧
    (thy,[]) |- _CVAL_IF (_CVAL_PAIR _P2 _Q2) _P1 _Q1 === _P1 ∧
    (thy,[]) |- _CVAL_IF (_CVAL_NUM (_NUMERAL _0)) _P1 _Q1 === _Q1
End

Theorem CVAL_IF_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type num_ty ∧ p1 has_type cval_ty ∧ q1 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_IF (_CVAL_NUM (_SUC m)) p1 q1 === p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_IF (_CVAL_NUM (_SUC _)) _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_IF_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type cval_ty ∧ q1 has_type cval_ty ∧
  p2 has_type cval_ty ∧ q2 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_IF (_CVAL_PAIR p2 q2) p1 q1 === p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_IF (_CVAL_PAIR _ _ ) _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_IF_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type cval_ty ∧ q1 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_IF (_CVAL_NUM (_NUMERAL _0)) p1 q1 === q1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_IF (_CVAL_NUM (_NUMERAL _)) _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_ADD_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type num_ty ∧ n has_type num_ty ⇒
    (thy,[]) |- _CVAL_ADD (_CVAL_NUM m) (_CVAL_NUM n) === _CVAL_NUM (_ADD m n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_ADD _ _ === _CVAL_NUM (_ADD _ _)’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_ADD_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type num_ty ∧ p1 has_type cval_ty ∧ q1 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_ADD (_CVAL_NUM m) (_CVAL_PAIR p1 q1) === _CVAL_NUM m
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_ADD x _ === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_ADD_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type num_ty ∧ p1 has_type cval_ty ∧ q1 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_ADD (_CVAL_PAIR p1 q1) (_CVAL_NUM n) === _CVAL_NUM n
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_ADD _ x === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_ADD_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type cval_ty ∧ q1 has_type cval_ty ∧
  p2 has_type cval_ty ∧ q2 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_ADD (_CVAL_PAIR p1 q1) (_CVAL_PAIR p2 q2) ===
                _CVAL_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_ADD _ _ === _CVAL_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem compute_thy_ok_terms_ok:
  compute_thy_ok thy ⇒
    (* nums *)
    term_ok (sigof thy) _ADD_TM ∧
    term_ok (sigof thy) _0 ∧
    term_ok (sigof thy) _SUC_TM ∧
    term_ok (sigof thy) _BIT0_TM ∧
    term_ok (sigof thy) _BIT1_TM ∧
    term_ok (sigof thy) _NUMERAL_TM ∧
    (* cvals *)
    term_ok (sigof thy) _CVAL_ADD_TM ∧
    term_ok (sigof thy) _CVAL_NUM_TM ∧
    term_ok (sigof thy) _CVAL_IF_TM ∧
    term_ok (sigof thy) _CVAL_PAIR_TM ∧
    (* types *)
    type_ok (tysof thy) cval_ty
Proof
  simp [compute_thy_ok_def] \\ strip_tac
  \\ dxrule_then strip_assume_tac numeral_thy_ok_terms_ok \\ fs []
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ fs [equation_def, term_ok_def, SF SFY_ss]
QED

Theorem compute_thy_ok_theory_ok[simp]:
  compute_thy_ok thy ⇒ theory_ok thy
Proof
  rw [compute_thy_ok_def]
QED

Theorem compute_thy_ok_numeral_thy_ok[simp]:
  compute_thy_ok thy ⇒ numeral_thy_ok thy
Proof
  rw [compute_thy_ok_def]
QED

Definition app_type_def:
  app_type arity = FUNPOW (Fun cval_ty) arity cval_ty
End

Theorem app_type:
  app_type 0 = cval_ty ∧
  app_type (SUC n) = Fun cval_ty (app_type n)
Proof
  rw [app_type_def, FUNPOW_SUC]
QED

Definition cval2term_def:
  cval2term (Num n) = _CVAL_NUM (_NUMERAL (num2bit n)) ∧
  cval2term (Pair p q) = _CVAL_PAIR (cval2term p) (cval2term q) ∧
  cval2term (Add p q) = _CVAL_ADD (cval2term p) (cval2term q) ∧
  cval2term (If p q r) = _CVAL_IF (cval2term p) (cval2term q) (cval2term r) ∧
  cval2term (Var s) = Var s cval_ty ∧
  cval2term (App s cs) =
    FOLDL Comb (Const s (app_type (LENGTH cs))) (MAP cval2term cs)
Termination
  wf_rel_tac ‘measure compute_val_size’
End

Definition cval_consts_def:
  cval_consts (Num n) = {} ∧
  cval_consts (Var s) = {} ∧
  cval_consts (Pair p q) = cval_consts p ∪ cval_consts q ∧
  cval_consts (Add p q) = cval_consts p ∪ cval_consts q ∧
  cval_consts (If p q r) =  cval_consts p ∪ cval_consts q ∪ cval_consts r ∧
  cval_consts (App s cs) = {s, LENGTH cs} ∪ BIGUNION (set (MAP cval_consts cs))
Termination
  wf_rel_tac ‘measure compute_val_size’
End

Definition cval_vars_def:
  cval_vars (Num n) = {} ∧
  cval_vars (Var s) = {s} ∧
  cval_vars (Pair p q) = cval_vars p ∪ cval_vars q ∧
  cval_vars (Add p q) = cval_vars p ∪ cval_vars q ∧
  cval_vars (If p q r) =  cval_vars p ∪ cval_vars q ∪ cval_vars r ∧
  cval_vars (App s cs) = BIGUNION (set (MAP cval_vars cs))
Termination
  wf_rel_tac ‘measure compute_val_size’
End

Theorem cval2term_typeof[simp]:
  ∀cv. typeof (cval2term cv) = cval_ty
Proof
  ho_match_mp_tac cval2term_ind \\ rw []
  \\ simp [cval2term_def, FOLDL_MAP]
  \\ pop_assum mp_tac
  \\ ‘∀tm.
        typeof tm = app_type (LENGTH cs) ⇒
          typeof (FOLDL (λx y. Comb x (cval2term y)) tm cs) = cval_ty ’
    suffices_by rw [SF SFY_ss]
  \\ Induct_on ‘cs’
  \\ simp [app_type]
QED

Theorem cval2term_has_type[simp]:
  ∀cv. cval2term cv has_type cval_ty
Proof
  ho_match_mp_tac cval2term_ind \\ rw [] \\ simp [cval2term_def]
  >~ [‘_CVAL_NUM _’] >- (
    rw [Ntimes has_type_cases 3]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘_CVAL_PAIR _ _’] >- (
    rw [Ntimes has_type_cases 3])
  >~ [‘_CVAL_ADD _ _’] >- (
    rw [Ntimes has_type_cases 3])
  >~ [‘_CVAL_IF _ _ _’] >- (
    rw [Ntimes has_type_cases 3]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘Var _’] >- (
    rw [has_type_rules])
  \\ simp [FOLDL_MAP]
  \\ ‘∀tm.
        tm has_type app_type (LENGTH cs) ⇒
          FOLDL (λx y. Comb x (cval2term y)) tm cs has_type cval_ty ’
    suffices_by rw [has_type_rules, SF SFY_ss]
  \\ Induct_on ‘cs’ \\ rw [app_type]
  \\ gs [has_type_rules, SF SFY_ss, SF DNF_ss]
QED

Theorem cval2term_welltyped[simp]:
  ∀cv. welltyped (cval2term cv)
Proof
  rw [welltyped_def, cval2term_has_type, SF SFY_ss]
QED

Theorem cval2term_term_ok:
  compute_thy_ok thy ⇒
    ∀cv.
      (∀c n.
        (c,n) ∈ cval_consts cv ⇒
          term_ok (sigof thy) (Const c (app_type n))) ⇒
        term_ok (sigof thy) (cval2term cv)
Proof
  strip_tac
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ ho_match_mp_tac cval2term_ind \\ rw []
  \\ gs [cval2term_def, cval_consts_def]
  >~ [‘Var s _’] >- (
    simp [term_ok_def])
  >~ [‘_CVAL_NUM _’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  >~ [‘_CVAL_PAIR _ _ ’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  >~ [‘_CVAL_ADD _ _ ’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  >~ [‘_CVAL_IF _ _ _ ’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  \\ gvs [FOLDL_MAP, MEM_MAP, SF SFY_ss, SF DNF_ss]
  \\ ‘∀tm.
        term_ok (sigof thy) tm ∧
        tm has_type (app_type (LENGTH cs)) ⇒
          term_ok (sigof thy) (FOLDL (λx y. Comb x (cval2term y)) tm cs)’
    suffices_by rw [term_ok_def, has_type_rules]
  \\ rpt (qpat_x_assum ‘term_ok _ _’ kall_tac)
  \\ Induct_on ‘cs’
  \\ rw [app_type, SF SFY_ss, SF DNF_ss]
  \\ first_x_assum irule \\ fs [SF SFY_ss]
  \\ simp [has_type_rules, cval2term_has_type, SF SFY_ss]
  \\ simp [term_ok_def, term_ok_welltyped, SF SFY_ss]
  \\ irule_at Any WELLTYPED_LEMMA \\ fs [SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * Monadic interpreter
 * ------------------------------------------------------------------------- *)

Datatype:
  cv_state = <| dummy : int; |>
End

Datatype:
  cv_exn = Timeout | Type_error
End

val [("dummy", get_dummy_def, set_dummy_def)] =
  define_monad_access_funs “:cv_state”;

val [(raise_Timeout_def, handle_Timeout_def),
     (raise_Type_error_def, handle_Type_error_def)] =
  define_monad_exception_functions “:cv_exn” “:cv_state”;

val st_ex_monadinfo : monadinfo = {
  bind = “st_ex_bind”,
  ignorebind = SOME “st_ex_ignore_bind”,
  unit = “st_ex_return”,
  fail = NONE,
  choice = SOME “$otherwise”,
  guard = NONE
  };

val _ = declare_monad ("st_ex", st_ex_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "st_ex";

(* cv_state / cv_exn monad *)

Overload return[local] = “st_ex_return”;
Overload timeout[local] = “raise_Timeout”;
Overload error[local] = “raise_Type_error”;

(* Candle monad *)

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

Definition dest_binary_def:
  dest_binary tm' tm =
    case tm of
      Comb (Comb (Const n t) l) r =>
        if tm' = Const n t then return (l, r)
        else failwith «dest_binary»
    | _ => failwith «dest_binary»
End

Definition list_dest_comb_def:
  list_dest_comb sofar (Comb f x) = list_dest_comb (x::sofar) f ∧
  list_dest_comb sofar tm = tm::sofar
End

Theorem list_dest_comb_not_nil[simp]:
  ∀sofar tm. list_dest_comb sofar tm ≠ []
Proof
  ho_match_mp_tac list_dest_comb_ind
  \\ rw [list_dest_comb_def]
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

Theorem mapOption_LENGTH:
  ∀xs ys. mapOption f xs = SOME ys ⇒ LENGTH xs = LENGTH ys
Proof
  Induct \\ rw [mapOption_def]
  \\ gvs [CaseEq "option"]
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

Definition do_add_def:
  do_add (Num m) (Num n) = return (Num (m + n)) ∧
  do_add (Num m) _ = return (Num m) ∧
  do_add _ (Num n) = return (Num n) ∧
  do_add _ _ = return (Num 0)
End

Definition map_def:
  map f [] = return [] ∧
  map f (x::xs) =
    do y <- f x;
       ys <- map f xs;
       return (y::ys)
    od
End

Theorem map_CONG[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      map f xs = map g ys
Proof
  simp [FUN_EQ_THM] \\ Induct \\ rw [map_def]
  \\ once_rewrite_tac [st_ex_bind_def] \\ gs []
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
  \\ ‘map f ys = map g ys’
    suffices_by rw []
  \\ rw [FUN_EQ_THM]
QED

Theorem map_LENGTH:
  ∀xs f ys s s'.
    map f xs s = (M_success ys, s') ⇒
      LENGTH xs = LENGTH ys
Proof
  Induct \\ simp [map_def, st_ex_return_def]
  \\ rpt gen_tac
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ rw [] \\ fs [SF SFY_ss]
QED

Theorem map_MEM:
  ∀xs f ys s s'.
    map f xs s = (M_success ys, s') ⇒
      ∀y. MEM y ys ⇒ ∃x r r'. MEM x xs ∧ f x r = (M_success y, r')
Proof
  Induct \\ simp [map_def, st_ex_return_def]
  \\ rpt gen_tac
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
  \\ strip_tac \\ gvs [SF SFY_ss, SF DNF_ss]
QED

(* -------------------------------------------------------------------------
 * Interpreter for compute values
 * ------------------------------------------------------------------------- *)

Definition check_def:
  check P = if P then return () else error
End

Definition option_def:
  option f x = case f x of SOME r => return r | _ => error
End

Definition compute_eval_def:
  compute_eval ck ceqs env cv =
    case cv of
    | Var s => option (ALOOKUP env) s
    | Num n => return (Num n)
    | Pair p q =>
        do
          x <- compute_eval ck ceqs env p;
          y <- compute_eval ck ceqs env q;
          return (Pair x y)
        od
    | Add p q =>
        do
          x <- compute_eval ck ceqs env p;
          y <- compute_eval ck ceqs env q;
          do_add x y
        od
    | App f cs =>
        if ck = 0 then timeout else
          do
            (args,exp) <- option (ALOOKUP ceqs) f;
            check (LENGTH args = LENGTH cs);
            cs <- map (compute_eval ck ceqs env) cs;
            compute_eval (ck - 1) ceqs (ZIP (args,cs)) exp
          od
    | If p q r =>
        do
          x <- compute_eval ck ceqs env p;
          case x of
          | Num 0 => compute_eval ck ceqs env r
          | Num _ => compute_eval ck ceqs env q
          | Pair _ _ => compute_eval ck ceqs env q
          | _ => error
        od
Termination
  wf_rel_tac ‘inv_image ($< LEX $<) (λ(ck,_,_,cv). (ck, compute_val_size cv))’
End

Definition compute_init_state_def:
  compute_init_state = <| dummy := 0 |>
End

Definition compute_eval_run_def:
  compute_eval_run ck ceqs cv =
    run (compute_eval ck ceqs [] cv) compute_init_state
End

Definition cval_value_def[simp]:
  cval_value (Num n) = T ∧
  cval_value (Pair p q) = (cval_value p ∧ cval_value q) ∧
  cval_value _ = F
End

Theorem do_add_thm:
  ∀x y s res s'.
    do_add x y s = (res, s') ⇒ s = s'
Proof
  ho_match_mp_tac do_add_ind \\ rw [do_add_def, st_ex_return_def]
QED

Theorem do_add_value:
  ∀x y s z s'.
    do_add x y s = (M_success z, s') ⇒ cval_value z
Proof
  ho_match_mp_tac do_add_ind \\ rw [do_add_def, st_ex_return_def] \\ fs []
QED

Theorem compute_eval_value:
  ∀ck ceqs env cv s x s'.
    EVERY cval_value (MAP SND env) ∧
    compute_eval ck ceqs env cv s = (M_success x, s') ⇒ cval_value x
Proof
  ho_match_mp_tac compute_eval_ind \\ rw []
  \\ qpat_x_assum ‘compute_eval _ _ _ _ _ = _’ mp_tac
  \\ simp [Once compute_eval_def]
  \\ TOP_CASE_TAC \\ gs []
  >- ((* Pair *)
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [st_ex_return_def]
    \\ rw [] \\ fs [SF SFY_ss])
  >- ((* Num *)
    rw [st_ex_return_def] \\ fs [])
  >- ((* Var *)
   simp [option_def, st_ex_return_def, raise_Type_error_def]
   \\ CASE_TAC \\ rw [] \\ gs [EVERY_MEM]
   \\ first_x_assum irule
   \\ drule_then assume_tac ALOOKUP_MEM
   \\ gs [MEM_MAP, EXISTS_PROD, SF SFY_ss])
  >- ((* App *)
    IF_CASES_TAC \\ gs [raise_Timeout_def]
    \\ simp [option_def, raise_Type_error_def]
    \\ simp [Once st_ex_bind_def, st_ex_return_def]
    \\ CASE_TAC \\ gs [] \\ pairarg_tac \\ gvs []
    \\ simp [check_def, raise_Type_error_def, st_ex_return_def,
             st_ex_ignore_bind_def]
    \\ IF_CASES_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [] \\ rw []
    \\ last_x_assum irule
    \\ first_x_assum (irule_at Any)
    \\ rename [‘map _ _ _ = (M_success ys, _)’]
    \\ ‘LENGTH args = LENGTH ys’
      by (drule map_LENGTH \\ simp [])
    \\ drule_then (qspecl_then [‘I’,‘I’] mp_tac) MAP_ZIP
    \\ rw [combinTheory.I_o_ID, EVERY_MEM]
    \\ drule_all_then strip_assume_tac map_MEM \\ gs [SF SFY_ss])
  >- ((* If *)
    simp [Once st_ex_bind_def, raise_Type_error_def]
    \\ TOP_CASE_TAC \\ gs [] \\ TOP_CASE_TAC \\ gs []
    \\ TOP_CASE_TAC \\ gs [SF SFY_ss]
    \\ TOP_CASE_TAC \\ gs [SF SFY_ss])
  >- ((* Add *)
    simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ rw [] \\ drule do_add_value \\ rw [])
QED

Theorem term_ok_FOLDL_Comb:
  ∀tms tm.
    term_ok sig (FOLDL Comb tm tms) ⇒
      term_ok sig tm ∧
      EVERY (term_ok sig) tms
Proof
  Induct \\ rw [term_ok_def]
  \\ first_x_assum drule \\ rw [term_ok_def]
QED

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
    ∀tm cv.
      dest_cval tm = SOME cv ⇒
      term_ok (sigof thy) tm ⇒
        (thy,[]) |- cval2term cv === tm ∧
        typeof tm = cval_ty
Proof
  strip_tac
  \\ ho_match_mp_tac dest_cval_ind
  \\ ntac 3 strip_tac \\ simp [Once dest_cval_def]
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  >- ((* variable *)
    fs [CaseEqs ["list", "option"]] \\ rw []
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ fs [cval2term_def, proves_REFL, term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* 0-ary *)
    simp [mapOption_def]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [app_type]
    \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
    \\ gvs [cval2term_def, cval_consts_def, app_type, proves_REFL])
  \\ TOP_CASE_TAC
  >- ((* unary: num or app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ gvs [cval2term_dest_numeral_opt] \\ gvs [cval2term_def]
    \\ rename [‘term_ok (sigof thy) tm ⇒ _’]
    \\ ‘term_ok (sigof thy) tm’
      by fs [term_ok_def]
    \\ gvs [app_type_def]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL \\ fs [term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* binary: add, pair, app *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ rename [‘term_ok _ (Comb (Comb _ x) y)’]
    \\ ‘term_ok (sigof thy) x ∧ term_ok (sigof thy) y’
      by fs [term_ok_def]
    \\ gvs [cval2term_def, MK_COMB_simple, proves_REFL, compute_thy_ok_terms_ok]
    \\ simp [app_type_def, numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp []
    \\ irule proves_REFL
    \\ fs [term_ok_def, SF SFY_ss])
  \\ TOP_CASE_TAC
  >- ((* ternary: if *)
    fs [CaseEqs ["list", "option", "bool"]]
    \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
    \\ rw [] \\ fs []
    \\ rename [‘term_ok _ (Comb (Comb (Comb _ x) y) z)’]
    \\ ‘term_ok (sigof thy) x ∧ term_ok (sigof thy) y ∧ term_ok (sigof thy) z’
      by fs [term_ok_def]
    \\ gvs [cval2term_def, app_type_def, numeralTheory.numeral_funpow]
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple \\ simp []
    \\ irule MK_COMB_simple
    \\ fs [compute_thy_ok_terms_ok, term_ok_def, proves_REFL, SF SFY_ss])
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
  \\ drule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
  \\ simp [cval2term_def, FOLDL_MAP]
  \\ ‘∀tm tm'.
        typeof tm = app_type (LENGTH tms) ∧
        term_ok (sigof thy) tm ∧
        (thy,[]) |- tm === tm' ⇒
          (thy,[]) |- FOLDL (λx y. Comb x (cval2term y)) tm' cvs ===
                      FOLDL Comb tm tms ∧
          typeof (FOLDL Comb tm tms) = cval_ty’
    suffices_by (
      disch_then irule
      \\ drule_then assume_tac mapOption_LENGTH \\ gs []
      \\ irule_at Any proves_REFL \\ fs []
      \\ drule term_ok_FOLDL_Comb \\ rw [])
  \\ qpat_x_assum ‘list_dest_comb _ _ = _’ kall_tac
  \\ dxrule_then strip_assume_tac term_ok_FOLDL_Comb
  \\ qpat_x_assum ‘term_ok _ (Const _ _)’ kall_tac
  \\ ntac 3 (pop_assum mp_tac)
  \\ qid_spec_tac ‘tms’
  \\ qid_spec_tac ‘cvs’
  \\ Induct \\ Cases_on ‘tms’ \\ simp [mapOption_def, app_type, proves_REFL,
                                       CaseEq "option", Once sym_equation]
  \\ ntac 7 strip_tac
  \\ rename [‘mapOption dest_cval tms’]
  \\ first_x_assum (qspec_then ‘tms’ assume_tac)
  \\ gs [SF SFY_ss] \\ first_x_assum irule \\ gs [SF DNF_ss]
  \\ conj_asm1_tac
  >- (
    qpat_x_assum ‘_ |- cval2term _ === _’ assume_tac
    \\ drule proves_term_ok
    \\ simp [term_ok_def, term_ok_welltyped, equation_def, SF SFY_ss])
  \\ irule MK_COMB_simple
  \\ pop_assum mp_tac
  \\ simp [proves_term_ok, term_ok_welltyped, term_ok_def, sym_equation]
QED

Definition subst_def:
  subst env (Var n) =
    (case ALOOKUP env n of
     | NONE => Var n
     | SOME cv => cv) ∧
  subst env (Num n) = Num n ∧
  subst env (Pair p q) = Pair (subst env p) (subst env q) ∧
  subst env (Add p q) = Add (subst env p) (subst env q) ∧
  subst env (App f cs) = App f (MAP (subst env) cs) ∧
  subst env (If p q r) = If (subst env p) (subst env q) (subst env r)
Termination
  wf_rel_tac ‘measure (compute_val_size o SND)’
End

Theorem subst_empty[simp]:
  subst [] x = x
Proof
  ‘∀xs x. xs = [] ⇒ subst xs x = x’
    suffices_by rw []
  \\ ho_match_mp_tac subst_ind
  \\ rw [subst_def]
  \\ irule LIST_EQ
  \\ gs [MEM_EL, PULL_EXISTS, EL_MAP]
QED

Theorem subst_term_ok:
  ∀env cv.
    term_ok ctxt (cval2term cv) ∧
    EVERY (term_ok ctxt o cval2term) (MAP SND env) ⇒
      term_ok ctxt (cval2term (subst env cv))
Proof
  ho_match_mp_tac subst_ind
  \\ rw [] \\ gs [subst_def, cval2term_def]
  \\ TRY CASE_TAC \\ imp_res_tac ALOOKUP_MEM
  \\ gvs [cval2term_def, EVERY_MEM, MEM_MAP, PULL_EXISTS,
          EXISTS_PROD, term_ok_def, SF SFY_ss]
  \\ ‘∀tm tms.
        term_ok ctxt tm ∧
        tm has_type (app_type (LENGTH tms)) ∧
        EVERY (term_ok ctxt) tms ∧
        EVERY (λtm. tm has_type cval_ty) tms ⇒
          term_ok ctxt (FOLDL Comb tm tms)’
    suffices_by (
      disch_then irule
      \\ drule_then strip_assume_tac term_ok_FOLDL_Comb
      \\ gs [EVERY_MAP, EVERY_MEM, has_type_rules, SF SFY_ss])
  \\ Induct_on ‘tms’ \\ rw [] \\ gs []
  \\ first_x_assum irule
  \\ gs [term_ok_def, term_ok_welltyped, SF SFY_ss]
  \\ imp_res_tac WELLTYPED_LEMMA
  \\ gs [has_type_rules, app_type, SF SFY_ss]
QED

Theorem compute_eval_thm:
  compute_thy_ok thy ⇒
    ∀ck eqs env cv s cv' s' tm.
      compute_eval ck eqs env cv s = (M_success cv', s') ∧
      (* cval_consts cv ⊆ set (MAP (λ(f,vs,_). (f,LENGTH vs)) eqs) ∧ *)
      term_ok (sigof thy) (cval2term cv) ∧
      EVERY cval_value (MAP SND env) ∧
      EVERY (term_ok (sigof thy) o cval2term) (MAP SND env) ∧
      EVERY (λcv. cval_consts cv = {}) (MAP SND env) ∧
      (* EVERY (λcv. cval_vars cv = {}) (MAP SND env) ∧ *)
      EVERY (λ(f,vs,cv). ∃l r.
        (thy,[]) |- l === r ∧
        list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                              MAP (λs. Var s cval_ty) vs ∧
        dest_cval r = SOME cv (*∧ ∀v. v ∈ cval_vars cv ⇒ MEM v vs*)) eqs ⇒
        (thy,[]) |- cval2term (subst env cv) === cval2term cv' ∧
        cval_consts cv' = {}
Proof
  strip_tac \\ fs []
  \\ ho_match_mp_tac compute_eval_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘compute_eval _ _ _ _ _ = _’ mp_tac
  \\ simp_tac std_ss [Once compute_eval_def, st_ex_return_def]
  \\ Cases_on ‘∃p q. cv = Pair p q’
  >- (
    pop_assum (qx_choosel_then [‘p’, ‘q’] SUBST_ALL_TAC) \\ fs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ strip_tac \\ gvs [term_ok_def, cval_consts_def, subst_def]
    \\ fs [cval2term_def, term_ok_def, MK_COMB_simple, proves_REFL, SF SFY_ss])
  \\ Cases_on ‘∃n. cv = Num n’
  >- (
    pop_assum (CHOOSE_THEN SUBST_ALL_TAC) \\ fs []
    \\ strip_tac \\ gvs [subst_def]
    \\ simp [compute_eval_def, proves_REFL, cval2term_term_ok, cval_consts_def,
             cval_vars_def, SF SFY_ss])
  \\ Cases_on ‘∃s. cv = Var s’
  >- (
    pop_assum (CHOOSE_THEN SUBST_ALL_TAC) \\ fs []
    \\ simp [option_def, st_ex_return_def, raise_Type_error_def]
    \\ CASE_TAC \\ strip_tac \\ gvs [subst_def]
    \\ dxrule_then assume_tac ALOOKUP_MEM
    \\ gs [EVERY_MEM, MEM_MAP, PULL_EXISTS, EXISTS_PROD, FORALL_PROD, SF SFY_ss]
    \\ irule proves_REFL \\ gs []
    \\ irule cval2term_term_ok \\ rw [] \\ gs [SF SFY_ss])
  \\ Cases_on ‘∃p q r. cv = If p q r’
  >- (
    pop_assum (qx_choosel_then [‘p’, ‘q’, ‘r’] SUBST_ALL_TAC)
    \\ simp_tac (srw_ss()) [Once st_ex_bind_def, raise_Type_error_def]
    \\ CASE_TAC \\ CASE_TAC
    \\ rename [‘compute_eval _ _ _ _ _ = (M_success cv', _)’]
    \\ Cases_on ‘cv' = Num 0’
    >- (
      pop_assum SUBST_ALL_TAC \\ simp_tac (srw_ss()) []
      \\ strip_tac
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gs []
      \\ gs [cval2term_def, cval_consts_def, subst_def, term_ok_def] \\ rw []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_assum (irule_at Any)
      \\ simp [cval2term_def, Once num2bit_def]
      \\ irule_at Any CVAL_IF_eqn3 \\ gs []
      \\ drule_then assume_tac proves_term_ok
      \\ fs [equation_def, term_ok_def, subst_term_ok])
    \\ Cases_on ‘∃x y. cv' = Pair x y’
    >- (
      pop_assum (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))
      \\ simp_tac (srw_ss()) [] \\ strip_tac
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gs []
      \\ fs [cval2term_def, cval_consts_def, subst_def]
      \\ fs [term_ok_def] \\ rw []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_assum (irule_at Any)
      \\ fs [cval2term_def, cval_consts_def, cval_vars_def]
      \\ irule_at Any CVAL_IF_eqn2 \\ gs []
      \\ imp_res_tac proves_term_ok
      \\ fs [equation_def, term_ok_def, subst_term_ok])
    \\ Cases_on ‘∃n. cv' = Num (SUC n)’
    >- (
      pop_assum (CHOOSE_THEN SUBST_ALL_TAC)
      \\ simp_tac (srw_ss()) [] \\ strip_tac
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ first_x_assum (drule o SIMPR [])
      \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac) \\ gs []
      \\ fs [cval2term_def, cval_consts_def, subst_def]
      \\ fs [term_ok_def] \\ rw []
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_assum (irule_at Any)
      \\ fs [cval2term_def]
      \\ irule replaceL3 \\ Q.REFINE_EXISTS_TAC ‘_CVAL_NUM x’
      \\ irule_at Any MK_COMB_simple
      \\ simp [proves_REFL, compute_thy_ok_terms_ok]
      \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
      \\ simp [num2bit_term_ok, compute_thy_ok_def, compute_thy_ok_terms_ok,
               proves_REFL]
      \\ irule replaceL3 \\ Q.REFINE_EXISTS_TAC ‘_CVAL_NUM x’
      \\ irule_at Any MK_COMB_simple
      \\ resolve_then Any (irule_at Any) num2bit_num2term sym_equation
      \\ simp [num2bit_term_ok, compute_thy_ok_def, compute_thy_ok_terms_ok,
               proves_REFL]
      \\ simp [num2term_def]
      \\ irule CVAL_IF_eqn1 \\ fs [num2term_term_ok]
      \\ imp_res_tac proves_term_ok
      \\ fs [equation_def, term_ok_def, subst_term_ok])
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [])
  \\ Cases_on ‘∃p q. cv = Add p q’
  >- (
    pop_assum (qx_choosel_then [‘p’, ‘q’] SUBST_ALL_TAC) \\ fs []
    \\ fs [cval2term_def, term_ok_def]
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ simp [Once st_ex_bind_def] \\ CASE_TAC \\ gs [] \\ CASE_TAC \\ gs []
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ gs [subst_def, cval_consts_def]
    \\ rename [‘do_add x y s’] \\ strip_tac
    \\ Cases_on ‘∃m. x = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. y = Num n’ \\ fs []
      >- (
        gvs [do_add_def, st_ex_return_def, cval_consts_def, cval2term_def]
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cval2term (subst env p) === A’
        \\ qmatch_asmsub_abbrev_tac ‘_ |- cval2term (subst env q) === B’
        \\ ‘(thy,[]) |- _CVAL_NUM (_NUMERAL (num2bit (m + n))) ===
                        _CVAL_ADD A B’
          suffices_by (
            rw [Abbr ‘A’, Abbr ‘B’]
            \\ resolve_then Any irule sym_equation replaceL2
            \\ first_x_assum (irule_at Any)
            \\ resolve_then Any irule sym_equation replaceL1
            \\ first_x_assum (irule_at Any)
            \\ fs [cval2term_def, sym_equation])
        \\ unabbrev_all_tac
        \\ ‘(thy,[]) |- _CVAL_ADD (_CVAL_NUM (num2bit m))
                                  (_CVAL_NUM (num2bit n)) ===
                        _CVAL_NUM (num2bit (m + n))’
          suffices_by (
            strip_tac
            \\ irule_at Any replaceL2
            \\ resolve_then Any (irule_at Any) NUMERAL_eqn sym_equation
            \\ fs [num2bit_term_ok]
            \\ resolve_then Any irule trans_equation_simple sym_equation
            \\ first_x_assum (irule_at Any)
            \\ irule MK_COMB_simple \\ simp []
            \\ irule_at Any MK_COMB_simple
            \\ simp [proves_REFL, compute_thy_ok_terms_ok, sym_equation,
                     cval2term_def]
            \\ DEP_REWRITE_TAC [MK_COMB_simple]
            \\ rw [compute_thy_ok_terms_ok, proves_REFL, NUMERAL_eqn,
                   sym_equation, num2bit_term_ok])
        \\ irule replaceR2
        \\ irule_at Any ADD_num2bit
        \\ rw [CVAL_ADD_eqn1, sym_equation, compute_thy_ok_def,
               num2bit_term_ok])
      \\ ‘cval_value y’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. y = Pair p1 q1’
        by (Cases_on ‘y’ \\ fs [])
      \\ gvs [cval2term_def, do_add_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_ADD_eqn2, cval2term_term_ok, num2bit_term_ok, NUMERAL_eqn,
             compute_thy_ok_terms_ok, term_ok_def, Ntimes has_type_cases 2])
    \\ Cases_on ‘∃n. y = Num n’ \\ gs []
    >- (
      gvs [cval2term_def, do_add_def, st_ex_return_def]
      \\ ‘cval_value x’
        by rw [compute_eval_value, SF SFY_ss]
      \\ ‘∃p1 q1. x = Pair p1 q1’
        by (Cases_on ‘x’ \\ fs [])
      \\ gvs [cval2term_def, do_add_def, st_ex_return_def]
      \\ ‘term_ok (sigof thy) (cval2term p1) ∧
          term_ok (sigof thy) (cval2term q1)’
        by (qpat_x_assum ‘_ |- _ === _CVAL_PAIR _ _’ assume_tac
            \\ drule_then assume_tac proves_term_ok
            \\ gs [term_ok_def, equation_def])
      \\ resolve_then Any irule sym_equation replaceL2
      \\ first_x_assum (irule_at Any)
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_ADD_eqn3, cval2term_term_ok, num2bit_term_ok, NUMERAL_eqn,
             num2bit_term_ok, compute_thy_ok_terms_ok, term_ok_def,
             Ntimes has_type_cases 2])
    \\ gvs [cval2term_def, do_add_def, st_ex_return_def]
    \\ ‘cval_value x’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p1 q1. x = Pair p1 q1’
      by (Cases_on ‘x’ \\ fs [])
    \\ ‘cval_value y’
      by rw [compute_eval_value, SF SFY_ss]
    \\ ‘∃p2 q2. y = Pair p2 q2’
      by (Cases_on ‘y’ \\ fs [])
    \\ gvs [cval2term_def, do_add_def, st_ex_return_def]
    \\ simp [Once num2bit_def, cval_consts_def, cval_vars_def]
    \\ ‘EVERY (term_ok (sigof thy) o cval2term) [p1;q1;p2;q2]’
      by (imp_res_tac proves_term_ok
          \\ gs [term_ok_def, equation_def])
    \\ resolve_then Any irule sym_equation replaceL2
    \\ first_x_assum (irule_at Any)
    \\ resolve_then Any irule sym_equation replaceL1
    \\ first_x_assum (irule_at Any)
    \\ fs [] \\ rw [CVAL_ADD_eqn4, cval2term_term_ok, compute_thy_ok_terms_ok])
  \\ Cases_on ‘∃f cs. cv = App f cs’
  >- (
    pop_assum (qx_choosel_then [‘f’, ‘cs’] SUBST_ALL_TAC)
    \\ simp_tac (srw_ss()) [raise_Timeout_def]
    \\ IF_CASES_TAC \\ simp_tac (srw_ss()) []
    \\ simp_tac (srw_ss()) [option_def, Once st_ex_bind_def,
                            raise_Type_error_def, st_ex_return_def]
    \\ CASE_TAC
    \\ pairarg_tac \\ pop_assum SUBST_ALL_TAC
    \\ simp_tac (srw_ss()) [check_def, raise_Type_error_def, st_ex_return_def,
                            Once st_ex_ignore_bind_def]
    \\ IF_CASES_TAC \\ simp_tac (srw_ss()) []
    \\ simp_tac (srw_ss()) [Once st_ex_bind_def]
    \\ CASE_TAC \\ CASE_TAC \\ strip_tac
    \\ first_x_assum (drule o SIMPR [])
    \\ first_x_assum (drule o SIMPR [])
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ strip_tac \\ gvs [subst_def]
    \\ disch_then (drule_at Any) \\ gs []
    \\ impl_keep_tac
    >- (
      drule_then assume_tac ALOOKUP_MEM
      \\ rgs [EVERY_MEM, SF SFY_ss]
      \\ drule_then assume_tac map_LENGTH \\ gs [MAP_ZIP]
      \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
      \\ dxrule_then strip_assume_tac list_dest_comb_folds_back \\ gvs []
      \\ qmatch_asmsub_abbrev_tac ‘_ |- lhs === rhs’
      \\ ‘term_ok (sigof thy) lhs ∧ term_ok (sigof thy) rhs’
        by (gs [Abbr ‘lhs’, Abbr ‘rhs’]
            \\ drule_then assume_tac proves_term_ok
            \\ gs [equation_def, term_ok_def])
      \\ drule_all_then strip_assume_tac dest_cval_thm
      \\ unabbrev_all_tac
      \\ drule_then assume_tac proves_term_ok
      \\ fs [equation_def, term_ok_def]
      \\ drule_then assume_tac map_MEM \\ fs []
      \\ rw [] \\ first_x_assum (drule_then strip_assume_tac)
      >- (
        irule compute_eval_value
        \\ first_x_assum (irule_at Any)
        \\ gs [EVERY_MEM, MEM_MAP, PULL_EXISTS])
      \\ first_x_assum (drule_then drule)
      \\ (impl_tac >- (
            gs [term_ok_def, cval2term_def]
            \\ imp_res_tac term_ok_FOLDL_Comb
            \\ gs [EVERY_MAP, EVERY_MEM]))
      \\ rw []
      \\ imp_res_tac proves_term_ok \\ gs [term_ok_def])
    \\ rw [cval2term_def]
    \\ cheat (* FOLDL *))
  \\ Cases_on ‘cv’ \\ fs []
QED

Theorem compute_eval_run_thm:
  compute_thy_ok thy ⇒
    compute_eval_run ck eqs cv = M_success cv' ∧
    (* cval_consts cv ⊆ set (MAP (λ(f,vs,_). (f,LENGTH vs)) eqs) ∧ *)
    term_ok (sigof thy) (cval2term cv) ∧
    EVERY (λ(f,vs,cv). ∃l r.
      (thy,[]) |- l === r ∧
      list_dest_comb [] l = Const f (app_type (LENGTH vs))::
                            MAP (λs. Var s cval_ty) vs ∧
      dest_cval r = SOME cv (* ∧ ∀v. v ∈ cval_vars cv ⇒ MEM v vs *)) eqs ⇒
      cval_consts cv' = {} ∧
      (thy,[]) |- cval2term cv === cval2term cv'
Proof
  simp [compute_eval_run_def, run_def]
  \\ strip_tac \\ strip_tac
  \\ gs [FST_EQ_EQUIV]
  \\ drule compute_eval_thm
  \\ disch_then drule \\ simp []
QED

val _ = export_theory ();

