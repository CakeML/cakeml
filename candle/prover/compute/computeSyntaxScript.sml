(*
   Definitions of term embeddings for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory;

val _ = new_theory "computeSyntax";

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

(* Bools *)

Overload "_A" = “Tyvar «A»”;
Overload "_FORALL_TM" = “Const «!» (Fun (Fun _A Bool) Bool)”;
Overload "_p" = “Var «p» (Fun _A Bool)”;
Overload "_P" = “Var «P» (Fun _A Bool)”;
Overload "_x" = “Var «x» _A”;
Overload "_T" = “Const «T» Bool”;

(* Pairs *)

Overload cval_ty = “Tyapp «cval» []”;
Overload "_P1" = “Var «p1» cval_ty”;
Overload "_P2" = “Var «p2» cval_ty”;
Overload "_Q1" = “Var «q1» cval_ty”;
Overload "_Q2" = “Var «q2» cval_ty”;
Overload "_CVAL_NUM_TM" = “Const «cval_num» (Fun num_ty cval_ty)”;
Overload "_CVAL_PAIR_TM" =
  “Const «cval_pair» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_NUM" = “λtm. Comb _CVAL_NUM_TM tm”;
Overload "_CVAL_PAIR" = “λt1 t2. Comb (Comb _CVAL_PAIR_TM t1) t2”;
Overload "_CVAL_ADD_TM" =
  “Const «cval_add» (Fun cval_ty (Fun cval_ty cval_ty))”;
Overload "_CVAL_ADD" = “λt1 t2. Comb (Comb _CVAL_ADD_TM t1) t2”;
Overload "_CVAL_FST_TM" = “Const «cval_fst» (Fun cval_ty cval_ty)”;
Overload "_CVAL_FST" = “λtm. Comb _CVAL_FST_TM tm”;
Overload "_CVAL_SND_TM" = “Const «cval_snd» (Fun cval_ty cval_ty)”;
Overload "_CVAL_SND" = “λtm. Comb _CVAL_SND_TM tm”;

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

Theorem replaceR1 =
  UNDISCH_ALL replaceL1 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR2 =
  UNDISCH_ALL replaceL2 |> MATCH_MP sym_equation |> DISCH_ALL;

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
 * Bools
 * ------------------------------------------------------------------------- *)

Definition bool_thy_ok_def:
  bool_thy_ok thy ⇔
    (thy,[]) |- _T === (Abs _p _p === Abs _p _p) ∧
    (thy,[]) |- _FORALL_TM === Abs _P (_P === Abs _x _T)
End

Theorem bool_thy_ok_terms_ok:
  bool_thy_ok thy ⇒
    term_ok (sigof thy) _T ∧
    term_ok (sigof thy) _FORALL_TM
Proof
  simp [bool_thy_ok_def] \\ strip_tac
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ fs [equation_def, term_ok_def, SF SFY_ss]
QED

Theorem bool_thy_ok_theory_ok[simp]:
  bool_thy_ok thy ⇒ theory_ok thy
Proof
  rw [bool_thy_ok_def]
  \\ drule proves_theory_ok \\ fs []
QED

(* -------------------------------------------------------------------------
 * Compute values
 * ------------------------------------------------------------------------- *)

Datatype:
  compute_val = Pair compute_val compute_val
              | Num num
              | Fst compute_val
              | Snd compute_val
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
    (* cval_fst *)
    (thy,[]) |- _CVAL_FST (_CVAL_PAIR _P1 _Q1) === _P1 ∧
    (thy,[]) |- _CVAL_FST (_CVAL_NUM _M) === _CVAL_NUM (_NUMERAL _0) ∧
    (* cval_snd *)
    (thy,[]) |- _CVAL_SND (_CVAL_PAIR _P1 _Q1) === _Q1 ∧
    (thy,[]) |- _CVAL_SND (_CVAL_NUM _M) === _CVAL_NUM (_NUMERAL _0)
End

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

Theorem CVAL_FST_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type cval_ty ∧ q1 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_FST (_CVAL_PAIR p1 q1) === p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_FST (_CVAL_PAIR x _) === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_FST_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type num_ty ⇒
    (thy,[]) |- _CVAL_FST (_CVAL_NUM m) === _CVAL_NUM (_NUMERAL_0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_FST _ === _CVAL_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_SND_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type cval_ty ∧ q1 has_type cval_ty ⇒
    (thy,[]) |- _CVAL_SND (_CVAL_PAIR p1 q1) === q1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_SND (_CVAL_PAIR _ x) === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CVAL_SND_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type num_ty ⇒
    (thy,[]) |- _CVAL_SND (_CVAL_NUM m) === _CVAL_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CVAL_SND _ === _CVAL_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac)
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
    term_ok (sigof thy) _CVAL_FST_TM ∧
    term_ok (sigof thy) _CVAL_SND_TM ∧
    term_ok (sigof thy) _CVAL_NUM_TM ∧
    term_ok (sigof thy) _CVAL_PAIR_TM
Proof
  simp [compute_thy_ok_def] \\ strip_tac
  \\ dxrule_then strip_assume_tac numeral_thy_ok_terms_ok \\ gs []
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ fs [equation_def, term_ok_def, SF SFY_ss]
QED

Theorem compute_thy_ok_theory_ok[simp]:
  compute_thy_ok thy ⇒ theory_ok thy
Proof
  rw [compute_thy_ok_def]
QED

Definition cval2term_def:
  cval2term (Num n) = _CVAL_NUM (_NUMERAL (num2bit n)) ∧
  cval2term (Pair p q) = _CVAL_PAIR (cval2term p) (cval2term q) ∧
  cval2term (Fst p) = _CVAL_FST (cval2term p) ∧
  cval2term (Snd p) = _CVAL_SND (cval2term p) ∧
  cval2term (Add p q) = _CVAL_ADD (cval2term p) (cval2term q)
End

Theorem cval2term_typeof[simp]:
  typeof (cval2term np) = cval_ty
Proof
  Induct_on ‘np’ \\ simp [cval2term_def]
QED

Theorem cval2term_has_type[simp]:
  cval2term np has_type cval_ty
Proof
  Induct_on ‘np’ \\ rw [cval2term_def]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
QED

Theorem cval2term_welltyped[simp]:
  welltyped (cval2term np)
Proof
  rw [welltyped_def, cval2term_has_type, SF SFY_ss]
QED

Theorem cval2term_term_ok:
  compute_thy_ok thy ⇒ term_ok (sigof thy) (cval2term np)
Proof
  strip_tac
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ Induct_on ‘np’ \\ rw [term_ok_def, cval2term_def]
  \\ fs [compute_thy_ok_def, num2bit_term_ok, SF SFY_ss]
QED

Theorem cval2term_VSUBST[simp]:
  ∀np. VSUBST is (cval2term np) = cval2term np
Proof
  Induct \\ rw [cval2term_def, VSUBST_def]
QED

Definition compute_eval_def:
  compute_eval (Num n) = Num n ∧
  compute_eval (Pair p q) = Pair (compute_eval p) (compute_eval q) ∧
  compute_eval (Add p q) =
    (case compute_eval p, compute_eval q of
    | Num m, Num n => Num (m + n)
    | Num m, _ => Num m
    | _, Num n => Num n
    | _ => Num 0) ∧
  compute_eval (Fst p) =
    (case compute_eval p of
    | Pair p q => p
    | _ => Num 0) ∧
  compute_eval (Snd p) =
    (case compute_eval p of
    | Pair p q => q
    | _ => Num 0)
End

Definition cval_ground_def[simp]:
  cval_ground (Num n) = T ∧
  cval_ground (Pair p q) = (cval_ground p ∧ cval_ground q) ∧
  cval_ground _ = F
End

Theorem compute_eval_ground:
  cval_ground (compute_eval np)
Proof
  Induct_on ‘np’ \\ simp [compute_eval_def]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
QED

Theorem compute_thy_ok_numeral_thy_ok[simp]:
  compute_thy_ok thy ⇒ numeral_thy_ok thy
Proof
  rw [compute_thy_ok_def]
QED

Theorem compute_eval_thm:
  compute_thy_ok thy ⇒
    (thy,[]) |- cval2term (compute_eval np) === cval2term np
Proof
  strip_tac \\ fs []
  \\ Induct_on ‘np’ \\ rpt gen_tac
  >~ [‘Pair p q’] >- (
    simp [compute_eval_def, cval2term_def, MK_COMB_simple, proves_REFL,
          compute_thy_ok_terms_ok])
  >~ [‘Num n’] >- (
    simp [compute_eval_def, proves_REFL, cval2term_term_ok, SF SFY_ss])
  >~ [‘Fst p’] >- (
    simp [compute_eval_def]
    \\ ‘cval_ground (compute_eval p)’
      by irule compute_eval_ground
    \\ Cases_on ‘∃p1 q1. compute_eval p = Pair p1 q1’ \\ gs []
    >- (
      gvs [cval2term_def]
      \\ irule replaceR2 \\ first_x_assum (irule_at Any)
      \\ simp [compute_thy_ok_terms_ok, cval2term_term_ok, term_ok_def]
      \\ rw [CVAL_FST_eqn1, cval2term_term_ok])
    \\ ‘∃n. compute_eval p = Num n’
      by (Cases_on ‘compute_eval p’ \\ gs [])
    \\ gvs [cval2term_def] \\ simp [Once num2bit_def]
    \\ irule replaceR2 \\ first_x_assum (irule_at Any)
    \\ rw [CVAL_FST_eqn2, compute_thy_ok_terms_ok, term_ok_def,
           Ntimes has_type_cases 2, num2bit_term_ok])
  >~ [‘Snd p’] >- (
    simp [compute_eval_def]
    \\ ‘cval_ground (compute_eval p)’
      by irule compute_eval_ground
    \\ Cases_on ‘∃p1 q1. compute_eval p = Pair p1 q1’ \\ gs []
    >- (
      gvs [cval2term_def]
      \\ irule replaceR2 \\ first_x_assum (irule_at Any)
      \\ simp [compute_thy_ok_terms_ok, cval2term_term_ok, term_ok_def]
      \\ rw [CVAL_SND_eqn1, cval2term_term_ok])
    \\ ‘∃n. compute_eval p = Num n’
      by (Cases_on ‘compute_eval p’ \\ gs [])
    \\ gvs [cval2term_def] \\ simp [Once num2bit_def]
    \\ irule replaceR2 \\ first_x_assum (irule_at Any)
    \\ rw [CVAL_SND_eqn2, compute_thy_ok_terms_ok, term_ok_def,
           Ntimes has_type_cases 2, num2bit_term_ok])
  >~ [‘Add p q’] >- (
    simp [compute_eval_def]
    \\ Cases_on ‘∃m. compute_eval p = Num m’ \\ fs []
    >- (
      Cases_on ‘∃n. compute_eval q = Num n’ \\ fs []
      >- (
        gvs [cval2term_def]
        \\ qmatch_asmsub_abbrev_tac ‘_ |- A === cval2term p’
        \\ qmatch_asmsub_abbrev_tac ‘_ |- B === cval2term q’
        \\ ‘(thy,[]) |- _CVAL_NUM (_NUMERAL (num2bit (m + n))) ===
                        _CVAL_ADD A B’
          suffices_by (
            rw [Abbr ‘A’, Abbr ‘B’]
            \\ irule replaceR2 \\ first_x_assum (irule_at Any)
            \\ irule replaceL1 \\ simp []
            \\ first_x_assum (irule_at Any)
            \\ rw [Once sym_equation])
        \\ unabbrev_all_tac
        \\ ‘(thy,[]) |- _CVAL_ADD (_CVAL_NUM (num2bit m))
                                  (_CVAL_NUM (num2bit n)) ===
                        _CVAL_NUM (num2bit (m + n))’
          suffices_by (
            strip_tac
            \\ irule replaceL2 \\ irule_at Any sym_equation
            \\ irule_at Any NUMERAL_eqn \\ fs [num2bit_term_ok]
            \\ irule trans_equation_simple \\ irule_at Any sym_equation
            \\ first_x_assum (irule_at Any)
            \\ irule MK_COMB_simple \\ simp []
            \\ irule_at Any MK_COMB_simple
            \\ simp [proves_REFL, compute_thy_ok_terms_ok, sym_equation]
            \\ DEP_REWRITE_TAC [MK_COMB_simple]
            \\ rw [compute_thy_ok_terms_ok, proves_REFL, NUMERAL_eqn,
                   sym_equation, num2bit_term_ok])
        \\ irule replaceR2
        \\ irule_at Any ADD_num2bit
        \\ rw [CVAL_ADD_eqn1, sym_equation, compute_thy_ok_def,
               num2bit_term_ok])
      \\ ‘cval_ground (compute_eval q)’
        by irule compute_eval_ground
      \\ ‘∃p1 q1. compute_eval q = Pair p1 q1’
        by (Cases_on ‘compute_eval q’ \\ fs [])
      \\ gvs [cval2term_def]
      \\ irule replaceR2 \\ first_x_assum (irule_at Any)
      \\ irule replaceL1 \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_ADD_eqn2, cval2term_term_ok, num2bit_term_ok, NUMERAL_eqn,
             compute_thy_ok_terms_ok, term_ok_def, Ntimes has_type_cases 2])
    \\ Cases_on ‘∃n. compute_eval q = Num n’ \\ gs []
    >- (
      ‘cval_ground (compute_eval p)’
        by irule compute_eval_ground
      \\ ‘∃p1 q1. compute_eval p = Pair p1 q1’
        by (Cases_on ‘compute_eval p’ \\ fs [])
      \\ gvs [cval2term_def]
      \\ ‘numeral_thy_ok thy’
        by rfs [compute_thy_ok_def]
      \\ drule_then assume_tac num2bit_term_ok
      \\ irule replaceR2 \\ first_x_assum (irule_at Any)
      \\ irule replaceL1 \\ first_x_assum (irule_at Any)
      \\ rw [CVAL_ADD_eqn3, cval2term_term_ok, num2bit_term_ok, NUMERAL_eqn,
             compute_thy_ok_terms_ok, term_ok_def, Ntimes has_type_cases 2])
    \\ ‘cval_ground (compute_eval p)’
      by irule compute_eval_ground
    \\ ‘∃p1 q1. compute_eval p = Pair p1 q1’
      by (Cases_on ‘compute_eval p’ \\ fs [])
    \\ ‘cval_ground (compute_eval q)’
      by irule compute_eval_ground
    \\ ‘∃p2 q2. compute_eval q = Pair p2 q2’
      by (Cases_on ‘compute_eval q’ \\ fs [])
    \\ gvs [cval2term_def] \\ simp [Once num2bit_def]
    \\ irule replaceR2 \\ first_x_assum (irule_at Any)
    \\ irule replaceL1 \\ first_x_assum (irule_at Any)
    \\ rw [CVAL_ADD_eqn4, cval2term_term_ok, compute_thy_ok_terms_ok])
QED

val _ = export_theory ();

