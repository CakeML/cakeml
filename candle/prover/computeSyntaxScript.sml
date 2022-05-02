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
    (thy,[]) |- Comb _BIT0 _0 === _0 ∧
    (thy,[]) |- Comb _BIT0 (Comb _SUC _N) ===
                 Comb _SUC (Comb _SUC (Comb _BIT0 _N)) ∧
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

Definition num2bit_def:
  num2bit n = if n = 0 then
                Comb _BIT0 _0
              else if n MOD 2 = 0 then
                Comb _BIT0 (num2bit (n DIV 2))
              else
                Comb _BIT1 (num2bit (n DIV 2))
Termination
  wf_rel_tac ‘$<’ \\ intLib.ARITH_TAC
End

(*
Theorem num2bit2:
  ∀n.
    (num2bit (2 * n) = Comb _BIT0 (if n = 0 then _0 else num2bit n)) ∧
    (num2bit (SUC (2 * n)) = Comb _BIT1 (num2bit n))
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def]
  \\ gs [DIV_EQ_0, DECIDE “∀n. n < 2n ⇔ n = 0 ∨ n = 1”, ADD1]
QED
 *)

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

Theorem replaceL1:
  theory_ok thy ∧
  term_ok (sigof thy) f ∧ welltyped f ∧
  term_ok (sigof thy) x ∧ welltyped x ∧
  term_ok (sigof thy) g ∧ welltyped g ∧
  typeof f = Fun (typeof x) ty ∧
  typeof g = Fun (typeof x) ty ∧
  (thy,[]) |- f === g ∧
  (thy,[]) |- Comb f x === z ⇒
    (thy,[]) |- Comb g x === z
Proof
  strip_tac
  \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
  \\ irule_at Any ACONV_REFL
  \\ first_assum (irule_at Any)
  \\ qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
  \\ simp [sym_equation, proves_REFL]
QED

Theorem replaceL2:
  theory_ok thy ∧
  term_ok (sigof thy) f ∧ welltyped f ∧
  term_ok (sigof thy) x ∧ welltyped x ∧
  typeof f = Fun (typeof x) ty ∧
  typeof x = typeof y ∧ welltyped y ∧
  (thy,[]) |- x === y ∧
  (thy,[]) |- Comb f x === z ⇒
    (thy,[]) |- Comb f y === z
Proof
  strip_tac
  \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
  \\ irule_at Any ACONV_REFL
  \\ first_assum (irule_at Any)
  \\ qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
  \\ simp [sym_equation, proves_REFL]
QED

Theorem replaceR1 =
  UNDISCH_ALL replaceL1 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR2 =
  UNDISCH_ALL replaceL2 |> MATCH_MP sym_equation |> DISCH_ALL;

(*
Theorem subst1:
  theory_ok thy ∧
  term_ok (sigof thy) x ∧ welltyped x ∧ x has_type ty ∧
  typeof f' = typeof f ∧ typeof f = Fun ty rty ∧
  VSUBST [x,Var n ty] f' = f ∧
  VSUBST [x,Var n ty] g' = g ∧
  (thy,[]) |- Comb f' (Var n ty) === Comb g' (Var n ty) ⇒
    (thy,[]) |- Comb f x === Comb g x
Proof
  strip_tac
  \\ drule_at_then (Pos (el 2)) (qspec_then ‘[x,Var n ty]’ mp_tac)
                   proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD]
QED
 *)

(*
Theorem const_subst_idem[local]:
  VSUBST is _BIT0 = _BIT0 ∧
  VSUBST is _BIT1 = _BIT1 ∧
  VSUBST is _SUC = _SUC ∧
  VSUBST is _0 = _0
Proof
  rw [VSUBST_def]
QED

val [VSUBST_BIT0,VSUBST_BIT1,VSUBST_SUC,VSUBST_0] =
  CONJUNCTS const_subst_idem;
 *)

Theorem num2term_BIT0:
  numeral_thy_ok thy ⇒
    ∀n. (thy,[]) |- Comb _BIT0 (num2term (SUC n DIV 2)) === num2term n
Proof
  cheat
QED

Theorem num2bit_num2term:
  numeral_thy_ok thy ⇒
    ∀n. (thy,[]) |- num2bit n === num2term n
Proof
  strip_tac \\ ho_match_mp_tac num2bit_ind
  \\ Cases \\ rw [num2term_def, Once num2bit_def]
  \\ gs [numeral_thy_ok_def]
  \\ rename [‘SUC n’]
  \\ ‘∀n. typeof (num2bit n) = num_ty ∧
          welltyped (num2bit n) ∧
          num2bit n has_type num_ty ∧
          term_ok (sigof thy) (num2bit n)’
    by cheat (* TODO *)
  \\ ‘∀n. typeof (num2term n) = num_ty ∧
          welltyped (num2term n) ∧
          num2term n has_type num_ty ∧
          term_ok (sigof thy) (num2term n)’
    by cheat (* TODO *)
  \\ qabbrev_tac ‘N = Comb _BIT0 _0’
  \\ ‘N has_type num_ty ∧ welltyped N’
    by metis_tac [has_type_rules, welltyped_def]
  \\ ‘typeof N = num_ty ∧ term_ok (sigof thy) N’
    by simp [term_ok_def, typeof_def, Abbr ‘N’]
  >- (
    gvs [DIV_EQ_0, DECIDE “n < 2n ⇔ n = 0 ∨ n = 1”]
    \\ rw [Once num2bit_def, num2term_def] \\ rw [Once num2bit_def]
    \\ gs [Once num2bit_def]
    \\ irule replaceR2 \\ gs []
    \\ first_assum (irule_at Any) \\ simp []
    \\ irule sym_equation
    \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
    \\ irule_at Any ACONV_REFL
    \\ ‘(thy,[]) |- Comb _BIT1 N === Comb _SUC (Comb _BIT0 N)’
      by (qpat_x_assum ‘_ |- Comb _BIT1 _ === _’ assume_tac
          \\ drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
          \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Abbr ‘N’, term_ok_def]
          \\ disch_then irule
          \\ simp [Abbr ‘N’, term_ok_def])
    \\ pop_assum (irule_at Any)
    \\ qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
    \\ simp [typeof_def, proves_REFL]
    \\ ‘(thy,[]) |- Comb _BIT0 N === Comb _BIT0 _0’
      by (qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
          \\ simp [typeof_def, proves_REFL])
    \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
    \\ irule_at Any ACONV_REFL
    \\ first_assum (irule_at Any)
    \\ simp [proves_REFL])
  >- (
    cheat (*
    Cases_on ‘SUC n MOD 2 = 0’ \\ gs []
    >- (
      rgs [Once MOD_EQ_0_DIVISOR] \\ gvs []
      \\ simp [num2bit2]
      \\ ‘(thy,[]) |- Comb _BIT0 (num2bit d) === Comb _BIT0 (num2term d)’
        by (qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
            \\ simp [proves_REFL])
      \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
      \\ irule_at Any ACONV_REFL
      \\ first_assum (irule_at Any)
      \\ ‘∃e. d = SUC e’ by intLib.ARITH_TAC \\ gvs []
      \\ ‘n = SUC (2 * e)’ by intLib.ARITH_TAC \\ gvs []
      \\ simp [num2term_def]
      \\ cheat (* TODO bleh *))
    \\ rgs [MOD_EQ_0_DIVISOR] \\ gvs []
    \\ ‘SUC n = SUC (2 * (2 * d))’ by intLib.ARITH_TAC
    \\ pop_assum SUBST1_TAC \\ simp [num2bit2]
    \\ qabbrev_tac ‘M = Comb _BIT0 (num2bit d)’
    \\ ‘M has_type num_ty ∧ term_ok (sigof thy) M’
      by cheat (* TODO *)
    \\ ‘(thy,[]) |- Comb _BIT1 M === Comb _SUC (Comb _BIT0 M)’
      by (qpat_x_assum ‘_ |- Comb _BIT1 _ === _’ assume_tac
          \\ drule_at_then (Pos (el 2)) (qspec_then ‘[M,_N]’ mp_tac) proves_INST
          \\ simp [VSUBST_def, REV_ASSOCD, equation_def])
    \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
    \\ irule_at Any ACONV_REFL
    \\ first_assum (irule_at Any)
    \\ qunabbrev_tac ‘M’
    \\ qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
    \\ simp [proves_REFL]
    \\ ‘(thy,[]) |- Comb _BIT0 (num2term (2 * d)) === num2term n’
      suffices_by (
        strip_tac
        \\ irule replaceL2 \\ gs []
        \\ irule_at Any sym_equation
        \\ first_assum (irule_at Any)
        \\ simp [proves_REFL])
    \\ qpat_assum ‘_ = 2 * d ’ (SUBST1_TAC o SYM)
    \\ irule num2term_BIT0 \\ gs []) *))
  >- (
    cheat (* bleh *))
QED

Theorem num2term_hom:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2term (m + n) === Comb (Comb _ADD (num2term m)) (num2term n)
Proof
  strip_tac
  \\ qid_spec_tac ‘m’
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
    by (
        qpat_x_assum ‘_ |- Comb (Comb _ADD _) _ === _’ assume_tac
        \\ drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘N’,
                 num2term_term_ok, numeral_thy_ok_def])
  \\ ‘∀is. VSUBST is N = N’
    by cheat (* TODO *)
  \\ ‘(thy,[]) |- Comb (Comb _ADD (Comb _SUC N)) M ===
                  Comb _SUC (Comb (Comb _ADD N) M)’
    by (drule_at_then (Pos (el 2)) (qspec_then ‘[M,_M]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘M’,
                 num2term_term_ok, numeral_thy_ok_def])
  \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule o SIMPR []) trans_equation
  \\ irule_at Any ACONV_REFL
  \\ irule_at (Pos last) sym_equation
  \\ first_assum (irule_at Any)
  \\ qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
  \\ simp [proves_REFL]
QED

Theorem num2bit_hom:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m + n) === Comb (Comb _ADD (num2bit m)) (num2bit n)
Proof
  strip_tac
  \\ drule_then assume_tac num2bit_num2term
  \\ gs [numeral_thy_ok_def]
  \\ ‘(thy,[]) |- Comb _ADD (num2term m) === Comb _ADD (num2bit m)’
    by (qspecl_then [‘[]’,‘[]’] (irule o SIMPR []) proves_MK_COMB
        \\ simp [proves_REFL, sym_equation])
  \\ irule replaceR1
  \\ first_x_assum (irule_at Any)
  \\ simp [term_ok_def, num2bit_term_ok, num2term_term_ok, numeral_thy_ok_def]
  \\ irule replaceL2 \\ simp [num2term_term_ok, numeral_thy_ok_def, term_ok_def]
  \\ qspecl_then [‘t’,‘[]’,‘[]’] (irule_at (Pos last) o SIMPR []) trans_equation
  \\ irule_at Any ACONV_REFL
  \\ irule_at (Pos last) sym_equation
  \\ first_assum (irule_at Any)
  \\ irule_at (Pos hd) sym_equation
  \\ first_assum (irule_at Any) \\ simp [num2term_term_ok, numeral_thy_ok_def]
  \\ irule sym_equation
  \\ gs [numeral_thy_ok_def, num2term_hom]
QED

val _ = export_theory ();

