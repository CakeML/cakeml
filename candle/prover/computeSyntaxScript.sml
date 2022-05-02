(*
  Definitions of term embeddings for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory;

val _ = new_theory "computeSyntax";

fun SIMPR ths = SIMP_RULE (srw_ss()) ths;
fun SIMPC ths = SIMP_CONV (srw_ss()) ths;

Overload num_ty = “Tyapp «num» []”;
Overload "_0" = “Const «0» num_ty”
Overload "_SUC" = “Const «SUC» (Fun num_ty num_ty)”;
Overload "_BIT0" = “Const «BIT0» (Fun num_ty num_ty)”;
Overload "_BIT1" = “Const «BIT1» (Fun num_ty num_ty)”;
Overload "_N" = “Var «n» num_ty”;
Overload "_M" = “Var «m» num_ty”;
Overload "_ADD" = “Const «+» (Fun num_ty (Fun num_ty num_ty))”;

(* All the necessary constants defined with the right types and
 * with the right defining equations (and some lemmas).
 *)

Definition numeral_thy_ok_def:
  numeral_thy_ok thy ⇔
    theory_ok thy ∧
    (* Constants defined *)
    term_ok (sigof thy) _BIT0 ∧
    term_ok (sigof thy) _BIT1 ∧
    term_ok (sigof thy) _0 ∧
    term_ok (sigof thy) _SUC ∧
    term_ok (sigof thy) _ADD ∧
    (* BIT0, BIT1 *)
    (thy,[]) |- Comb _BIT0 _N === Comb (Comb _ADD _N) _N ∧
    (thy,[]) |- Comb _BIT1 _N === Comb _SUC (Comb _BIT0 _N) ∧
    (* ADD *)
    (thy,[]) |- Comb (Comb _ADD _0) _M === _M ∧
    (thy,[]) |- Comb (Comb _ADD (Comb _SUC _N)) _M ===
                Comb _SUC (Comb (Comb _ADD _N) _M)
End

Definition num2term_def:
  num2term 0 = _0 ∧
  num2term (SUC n) = Comb _SUC (num2term n)
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

Theorem num2term_term_ok[local,simp]:
  numeral_thy_ok thy ⇒ term_ok (sigof thy) (num2term n)
Proof
  Induct_on ‘n’ \\ rw [numeral_thy_ok_def, term_ok_def, num2term_def]
QED

Theorem num2term_VSUBST[local,simp]:
  ∀n. VSUBST is (num2term n) = num2term n
Proof
  Induct \\ rw [num2term_def, VSUBST_def]
QED

Definition num2bit_def:
  num2bit n =
    if n = 0 then
      Comb _BIT0 _0
    else
      Comb (if n MOD 2 = 0 then _BIT0 else _BIT1) (num2bit (n DIV 2))
Termination
  wf_rel_tac ‘$<’ \\ intLib.ARITH_TAC
End

Theorem num2bit_typeof[local,simp]:
  ∀n. typeof (num2bit n) = num_ty
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def]
QED

Theorem num2bit_has_type[local,simp]:
  ∀n. num2bit n has_type num_ty
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
QED

Theorem num2bit_welltyped[local,simp]:
  ∀n. welltyped (num2bit n)
Proof
  rw [welltyped_def, num2bit_has_type, SF SFY_ss]
QED

Theorem num2bit_term_ok[local,simp]:
  numeral_thy_ok thy ⇒ term_ok (sigof thy) (num2bit n)
Proof
  rw [numeral_thy_ok_def]
  \\ qid_spec_tac ‘n’
  \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def, term_ok_def]
QED

Theorem num2bit_VSUBST[local,simp]:
  ∀n. VSUBST is (num2bit n) = num2bit n
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ once_rewrite_tac [num2bit_def]
  \\ rw [VSUBST_def]
QED

Theorem trans_equation_simple[local]:
  (thy,[]) |- a === b ∧
  (thy,[]) |- b === c ⇒
    (thy,[]) |- a === c
Proof
  rw []
  \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
  \\ simp [ACONV_REFL, SF SFY_ss]
QED

Theorem MK_COMB_simple[local] =
  Q.SPECL [‘[]’,‘[]’] proves_MK_COMB |> SIMPR [PULL_EXISTS];

Theorem replaceL1[local]:
  theory_ok thy ∧
  EVERY (term_ok (sigof thy)) [f; g; x] ∧
  typeof f = Fun (typeof x) ty ∧
  typeof g = Fun (typeof x) ty ⇒
    (thy,[]) |- f === g ∧
    (thy,[]) |- Comb f x === z ⇒
      (thy,[]) |- Comb g x === z
Proof
  rw []
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any)
  \\ simp [MK_COMB_simple, term_ok_welltyped, proves_REFL, sym_equation,
           SF SFY_ss]
QED

Theorem replaceL2[local]:
  theory_ok thy ∧
  EVERY (term_ok (sigof thy)) [f;x;y] ∧
  typeof f = Fun (typeof x) ty ∧
  typeof x = typeof y ∧
  (thy,[]) |- x === y ∧
  (thy,[]) |- Comb f x === z ⇒
    (thy,[]) |- Comb f y === z
Proof
  rw []
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any)
  \\ simp [MK_COMB_simple, term_ok_welltyped, proves_REFL, sym_equation,
           SF SFY_ss]
QED

Theorem replaceR1 =
  UNDISCH_ALL replaceL1 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR2 =
  UNDISCH_ALL replaceL2 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2term_ADD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2term (m + n) === Comb (Comb _ADD (num2term m)) (num2term n)
Proof
  strip_tac \\ qid_spec_tac ‘m’
  \\ gs [numeral_thy_ok_def]
  \\ Induct \\ simp []
  >- (
    rw [num2term_def]
    \\ qabbrev_tac ‘M = num2term n’
    \\ qpat_x_assum ‘_ |- _ (Comb _ADD _0) _M === _M’ assume_tac
    \\ drule_at_then (Pos (el 2)) (qspec_then ‘[M,_M]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Abbr ‘M’, term_ok_def,
             num2term_term_ok, numeral_thy_ok_def, sym_equation])
  \\ rw [ADD_CLAUSES, num2term_def] \\ fs []
  \\ qmatch_goalsub_abbrev_tac ‘Comb (Comb _ADD (Comb _SUC N)) M’
  \\ ‘(thy,[]) |- Comb (Comb _ADD (Comb _SUC N)) _M ===
                  Comb _SUC (Comb (Comb _ADD N) _M)’
    by (qpat_x_assum ‘_ |- Comb (Comb _ADD _) _ === _’ assume_tac
        \\ drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘N’,
                 num2term_term_ok, numeral_thy_ok_def])
  \\ ‘(thy,[]) |- Comb (Comb _ADD (Comb _SUC N)) M ===
                  Comb _SUC (Comb (Comb _ADD N) M)’
    by (drule_at_then (Pos (el 2)) (qspec_then ‘[M,_M]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘M’,
                 num2term_term_ok, numeral_thy_ok_def, Abbr ‘N’])
  \\ irule trans_equation_simple
  \\ irule_at (Pos last) sym_equation
  \\ first_assum (irule_at Any)
  \\ simp [MK_COMB_simple, proves_REFL]
QED

Theorem ADD_num2term =
  UNDISCH_ALL num2term_ADD |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2bit_num2term:
  numeral_thy_ok thy ⇒
    ∀n. (thy,[]) |- num2bit n === num2term n
Proof
  strip_tac \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ gs [numeral_thy_ok_def]
  \\ rw [num2term_def, Once num2bit_def]
  >- (
    qpat_assum ‘_ |- Comb _BIT0 _N === _’ assume_tac
    \\ ‘(thy,[]) |- Comb _BIT0 _0 === Comb (Comb _ADD _0) _0’
      by (drule_at_then (Pos (el 2)) (qspec_then ‘[_0,_N]’ mp_tac) proves_INST
          \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Once has_type_rules])
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ qpat_assum ‘_ |- Comb (Comb _ADD _0) _ === _’ assume_tac
    \\ drule_at_then (Pos (el 2)) (qspec_then ‘[_0,_M]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Once has_type_rules])
  >- (
    qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘(thy,[]) |- Comb _BIT0 (num2bit (n DIV 2)) === Comb _BIT0 N’
      by rw [MK_COMB_simple, proves_REFL]
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ qpat_x_assum ‘_ |- Comb _BIT0 _N === _’ assume_tac
    \\ ‘(thy,[]) |- Comb _BIT0 N === Comb (Comb _ADD N) N’
      by (drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
          \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘N’,
                   num2term_term_ok, numeral_thy_ok_def])
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ fs [Abbr ‘N’]
    \\ qspecl_then [‘thy’,‘n DIV 2’,‘n DIV 2’] mp_tac (GEN_ALL ADD_num2term)
    \\ gs [numeral_thy_ok_def]
    \\ ‘2 * (n DIV 2) = n’ by intLib.ARITH_TAC \\ gs [])
  >- (
    qpat_assum ‘_ |- Comb _BIT1 _N === _’ assume_tac
    \\ qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘(thy,[]) |- Comb _BIT1 (num2bit (n DIV 2)) === Comb _BIT1 N’
      by rw [MK_COMB_simple, proves_REFL]
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ ‘(thy,[]) |- Comb _BIT1 N === Comb _SUC (Comb _BIT0 N)’
      by (drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
          \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Once has_type_rules,
                   num2term_term_ok, numeral_thy_ok_def, Abbr ‘N’])
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ ‘n = SUC (n DIV 2 + n DIV 2)’ by intLib.ARITH_TAC
    \\ pop_assum (fn th => simp [SimpR “(===)”, Once th])
    \\ simp [num2term_def]
    \\ irule MK_COMB_simple
    \\ ‘welltyped N ∧ typeof N = num_ty’
      by gs [Abbr ‘N’]
    \\ simp [proves_REFL]
    \\ ‘2 * (n DIV 2) = n DIV 2 + n DIV 2’
      by rw []
    \\ pop_assum SUBST1_TAC
    \\ irule trans_equation_simple
    \\ irule_at Any ADD_num2term
    \\ simp [numeral_thy_ok_def]
    \\ qpat_x_assum ‘_ |- Comb _BIT0 _N === _’ assume_tac
    \\ drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘N’,
             num2term_term_ok, numeral_thy_ok_def, sym_equation])
QED

Theorem num2bit_ADD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m + n) === Comb (Comb _ADD (num2bit m)) (num2bit n)
Proof
  strip_tac
  \\ drule_then assume_tac num2bit_num2term
  \\ first_assum (qspec_then ‘n’ assume_tac)
  \\ first_assum (qspec_then ‘m’ assume_tac)
  \\ first_x_assum (qspec_then ‘m + n’ assume_tac)
  \\ gs [numeral_thy_ok_def]
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any)
  \\ irule trans_equation_simple
  \\ qexists_tac ‘Comb (Comb _ADD (num2term m)) (num2term n)’
  \\ simp [num2term_ADD, numeral_thy_ok_def, MK_COMB_simple, proves_REFL,
           sym_equation]
QED

val _ = export_theory ();

