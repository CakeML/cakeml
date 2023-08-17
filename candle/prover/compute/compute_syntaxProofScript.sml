(*
   Proofs related to term embeddings for the Candle compute primitive.
 *)

open preamble holSyntaxTheory holSyntaxExtraTheory holSyntaxLibTheory
     holKernelTheory holKernelProofTheory compute_syntaxTheory;

val _ = new_theory "compute_syntaxProof";

val _ = numLib.prefer_num ();

fun SIMPR ths = SIMP_RULE (srw_ss()) ths;
fun SIMPC ths = SIMP_CONV (srw_ss()) ths;

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

Theorem replaceL_eq1:
  (thy,[]) |- (x === x') ∧
  (thy,[]) |- (x === y) === r ⇒
    (thy,[]) |- (x' === y) === r
Proof
  rw []
  \\ ‘theory_ok thy ∧
      EVERY (term_ok (sigof thy)) [x;x';y;r] ∧
      typeof x = typeof y ∧
      typeof x' = typeof x ∧
      typeof r = Bool ∧
      type_ok (tysof thy) (typeof y)’
    by (imp_res_tac proves_term_ok
        \\ imp_res_tac proves_theory_ok
        \\ gs [term_ok_def, equation_def, type_ok_def])
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any) \\ fs []
  \\ CONV_TAC (PATH_CONV "rl" (SIMPC [equation_def]))
  \\ CONV_TAC (PATH_CONV "rr" (SIMPC [equation_def]))
  \\ irule MK_COMB_simple \\ gs [proves_REFL, term_ok_welltyped, SF SFY_ss]
  \\ irule MK_COMB_simple \\ gs [proves_REFL, term_ok_welltyped, SF SFY_ss]
  \\ rw [sym_equation] \\ irule proves_REFL \\ gs []
  \\ gs [theory_ok_def, term_ok_clauses]
QED

Theorem replaceL_eq2:
  (thy,[]) |- (x === x') ∧
  (thy,[]) |- (y === x) === r ⇒
    (thy,[]) |- (y === x') === r
Proof
  rw []
  \\ ‘theory_ok thy ∧
      EVERY (term_ok (sigof thy)) [x;x';y;r] ∧
      typeof x = typeof y ∧
      typeof x' = typeof x ∧
      typeof r = Bool ∧
      type_ok (tysof thy) (typeof y)’
    by (imp_res_tac proves_term_ok
        \\ imp_res_tac proves_theory_ok
        \\ gs [term_ok_def, equation_def, type_ok_def])
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any) \\ fs []
  \\ CONV_TAC (PATH_CONV "rl" (SIMPC [equation_def]))
  \\ CONV_TAC (PATH_CONV "rr" (SIMPC [equation_def]))
  \\ irule MK_COMB_simple \\ gs [proves_REFL, term_ok_welltyped, SF SFY_ss]
  \\ rw [sym_equation]
  \\ irule proves_REFL \\ gs []
  \\ gs [theory_ok_def, term_ok_clauses, term_ok_welltyped, SF SFY_ss]
QED

Theorem replaceR1 =
  UNDISCH_ALL replaceL1 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR2 =
  UNDISCH_ALL replaceL2 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR3 =
  UNDISCH_ALL replaceL3 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR_eq1 =
  UNDISCH_ALL replaceL_eq1 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem replaceR_eq2 =
  UNDISCH_ALL replaceL_eq2 |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem DEDUCT_ANTISYM_simple:
  (thy,[]) |- a ∧ (thy,[]) |- b ⇒ (thy,[]) |- a === b
Proof
  qspecl_then [‘a’,‘b’,‘[]’,‘[]’] (assume_tac o SIMPR [ACONV_REFL])
                                  proves_DEDUCT_ANTISYM
  \\ gs []
QED

(* -------------------------------------------------------------------------
 * Booleans
 * ------------------------------------------------------------------------- *)

Definition bool_thy_ok_def:
  bool_thy_ok thy ⇔
    theory_ok thy ∧
    (* COND *)
    (thy,[]) |- _COND _TRUE _M _N === _M ∧
    (thy,[]) |- _COND _FALSE _M _N === _N ∧
    (thy,[]) |- _IF _TRUE _X _Y === _X ∧
    (thy,[]) |- _IF _FALSE _X _Y === _Y
End

Theorem bool_thy_ok_terms_ok:
  bool_thy_ok thy ⇒
    term_ok (sigof thy) _TRUE ∧
    term_ok (sigof thy) _FALSE ∧
    term_ok (sigof thy) _COND_TM ∧
    term_ok (sigof thy) _IF_TM
Proof
  simp [bool_thy_ok_def] \\ strip_tac
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ gs [theory_ok_def, term_ok_clauses]
QED

Theorem bool_thy_ok_theory_ok[simp]:
  bool_thy_ok thy ⇒ theory_ok thy
Proof
  rw [bool_thy_ok_def]
QED

(* -------------------------------------------------------------------------
 * Natural numbers
 * ------------------------------------------------------------------------- *)

(* All the necessary constants defined with the right types and
 * with the right defining equations (and some lemmas).
 *)

Definition numeral_thy_ok_def:
  numeral_thy_ok thy ⇔
    bool_thy_ok thy ∧
    (* NUMERAL *)
    (thy,[]) |- _NUMERAL _N === _N ∧
    (* BIT0, BIT1 *)
    (thy,[]) |- _BIT0 _N === _ADD _N _N ∧
    (thy,[]) |- _BIT1 _N === _SUC (_ADD _N _N) ∧
    (* ADD *)
    (thy,[]) |- _ADD (_NUMERAL _0) _N === _N ∧
    (thy,[]) |- _ADD (_SUC _M) _N === _SUC (_ADD _M _N) ∧
    (* SUB *)
    (thy,[]) |- _SUB (_NUMERAL _0) _N === _NUMERAL _0 ∧
    (thy,[]) |- _SUB _M (_NUMERAL _0) === _M ∧
    (thy,[]) |- _SUB (_SUC _M) (_SUC _N) === _SUB _M _N ∧
    (* MUL *)
    (thy,[]) |- _MUL (_NUMERAL _0) _N === _NUMERAL _0 ∧
    (thy,[]) |- _MUL (_SUC _M) _N === _ADD _N (_MUL _M _N) ∧
    (* DIV, MOD *)
    (thy,[]) |- _DIV _M _N ===
                _COND (_N === _NUMERAL _0) (_NUMERAL _0)
                      (_COND (_LESS _M _N) (_NUMERAL _0)
                             (_SUC (_DIV (_SUB _M _N) _N))) ∧
    (thy,[]) |- _MOD _M _N ===
                _COND (_N === _NUMERAL _0) _M
                      (_COND (_LESS _M _N) _M
                             (_MOD (_SUB _M _N) _N)) ∧
    (* LESS *)
    (thy,[]) |- _LESS _M (_NUMERAL _0) === _FALSE ∧
    (thy,[]) |- _LESS (_NUMERAL _0) (_SUC _N) === _TRUE ∧
    (thy,[]) |- _LESS (_SUC _M) (_SUC _N) === _LESS _M _N ∧
    (* EQ *)
    (thy,[]) |- (_NUMERAL _0 === _NUMERAL _0) === _TRUE ∧
    (thy,[]) |- (_NUMERAL _0 === _SUC _N) === _FALSE ∧
    (thy,[]) |- (_SUC _M === _NUMERAL _0) === _FALSE ∧
    (thy,[]) |- (_SUC _M === _SUC _N) === (_M === _N)
End

Theorem numeral_thy_ok_theory_ok[simp]:
  numeral_thy_ok thy ⇒ theory_ok thy
Proof
  rw [numeral_thy_ok_def]
  \\ drule proves_theory_ok \\ simp []
QED

Theorem numeral_thy_ok_bool_thy_ok[simp]:
  numeral_thy_ok thy ⇒ bool_thy_ok thy
Proof
  rw [numeral_thy_ok_def]
QED

Theorem numeral_thy_ok_terms_ok:
  numeral_thy_ok thy ⇒
    term_ok (sigof thy) _TRUE ∧
    term_ok (sigof thy) _FALSE ∧
    term_ok (sigof thy) _COND_TM ∧
    term_ok (sigof thy) _IF_TM ∧
    term_ok (sigof thy) _ADD_TM ∧
    term_ok (sigof thy) _SUB_TM ∧
    term_ok (sigof thy) _MUL_TM ∧
    term_ok (sigof thy) _DIV_TM ∧
    term_ok (sigof thy) _MOD_TM ∧
    term_ok (sigof thy) _LESS_TM ∧
    term_ok (sigof thy) _0 ∧
    term_ok (sigof thy) _SUC_TM ∧
    term_ok (sigof thy) _BIT0_TM ∧
    term_ok (sigof thy) _BIT1_TM ∧
    term_ok (sigof thy) _NUMERAL_TM
Proof
  simp [numeral_thy_ok_def] \\ strip_tac
  \\ dxrule_then assume_tac bool_thy_ok_terms_ok \\ gs []
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ fs [equation_def, term_ok_def, SF SFY_ss]
QED

Theorem term_ok_NUMERAL[simp]:
  numeral_thy_ok thy ⇒
    term_ok (sigof thy) (_NUMERAL N) = (term_ok (sigof thy) N ∧
                                        N has_type Num)
Proof
  rw [EQ_IMP_THM]
  \\ gs [numeral_thy_ok_terms_ok, term_ok_def, term_ok_welltyped,
         WELLTYPED_LEMMA, SF SFY_ss]
  \\ drule_then (Lib.C (resolve_then Any mp_tac) (iffLR WELLTYPED))
                term_ok_welltyped
  \\ gs []
QED

Theorem NUMERAL_has_type[simp]:
  _NUMERAL N has_type Num ⇔ N has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

Theorem has_type_0[simp]:
  _0 has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

Theorem term_ok_SUC[simp]:
  numeral_thy_ok thy ⇒
    term_ok (sigof thy) (_SUC N) = (term_ok (sigof thy) N ∧ N has_type Num)
Proof
  rw [EQ_IMP_THM]
  \\ gs [numeral_thy_ok_terms_ok, term_ok_def, term_ok_welltyped,
         WELLTYPED_LEMMA, SF SFY_ss]
  \\ drule_then (Lib.C (resolve_then Any mp_tac) (iffLR WELLTYPED))
                term_ok_welltyped
  \\ gs []
QED

Theorem SUC_has_type[simp]:
  _SUC N has_type Num ⇔ N has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

(* The numeral_thy_ok theorems with object variables replaced with meta
   variables.
 *)

Theorem NUMERAL_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type Num ⇒
    (thy,[]) |- _NUMERAL n === n
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _NUMERAL x === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem BIT0_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type Num ⇒
    (thy,[]) |- _BIT0 n === _ADD n n
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _BIT0 x === _ADD x x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem BIT1_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type Num ⇒
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
  m has_type Num ∧ n has_type Num ⇒
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

Theorem SUB_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _SUB (_NUMERAL _0) n === _NUMERAL _0 ∧
    (thy,[]) |- _SUB m (_NUMERAL _0) === m ∧
    (thy,[]) |- _SUB (_SUC m) (_SUC n) === _SUB m n
Proof
  rw [numeral_thy_ok_def]
  >- (
    qpat_x_assum ‘_ |- _SUB (_NUMERAL _) _ === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def])
  >- (
    qpat_x_assum ‘_ |- _SUB _ (_NUMERAL _) === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def])
  \\ qpat_x_assum ‘_ |- _SUB (_SUC _) _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M; n,_N]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem MUL_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _MUL (_NUMERAL _0) n === _NUMERAL _0 ∧
    (thy,[]) |- _MUL (_SUC m) n === _ADD n (_MUL m n)
Proof
  rw [numeral_thy_ok_def]
  >- (
    qpat_x_assum ‘_ |- _MUL (_NUMERAL _) _ === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def])
  \\ qpat_x_assum ‘_ |- _MUL (_SUC _) _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M; n,_N]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem LESS_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _LESS m (_NUMERAL _0) === _FALSE ∧
    (thy,[]) |- _LESS (_NUMERAL _0) (_SUC n) === _TRUE ∧
    (thy,[]) |- _LESS (_SUC m) (_SUC n) === _LESS m n
Proof
  rw [numeral_thy_ok_def]
  >- (
    qpat_x_assum ‘_ |- _LESS _ (_NUMERAL _) === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def])
  >- (
    qpat_x_assum ‘_ |- _LESS (_NUMERAL _) _ === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def])
  \\ qpat_x_assum ‘_ |- _LESS (_SUC _) _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M; n,_N]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem EQ_eqn1:
  numeral_thy_ok thy ⇒
    (thy,[]) |- (_NUMERAL _0 === _NUMERAL _0) === _TRUE
Proof
  rw [numeral_thy_ok_def]
QED

Theorem EQ_eqn2:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type Num ⇒
    (thy,[]) |- (_NUMERAL _0 === _SUC n) === _FALSE
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_NUMERAL _ === _SUC _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem EQ_eqn3:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- (_SUC m === _NUMERAL _0) === _FALSE
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_SUC _ === _NUMERAL _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem EQ_eqn4:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- (_SUC m === _SUC n) === (m === n)
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_SUC _ === _SUC _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M;n,_N]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
  \\ ‘Equal (typeof (_SUC m)) = Equal Num’ by gs []
  \\ pop_assum (SUBST1_TAC o SYM) \\ simp [GSYM equation_def]
  \\ ‘Equal (typeof m) = Equal Num’ by gs [WELLTYPED_LEMMA]
  \\ pop_assum (SUBST1_TAC o SYM) \\ simp [GSYM equation_def]
QED

Theorem COND_eqn:
  bool_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _COND _TRUE m n === m ∧
    (thy,[]) |- _COND _FALSE m n === n
Proof
  rw [bool_thy_ok_def]
  >- (
    qpat_x_assum ‘_ |- _COND _TRUE _ _ === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M; n,_N]’ mp_tac)
                      proves_INST
    \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def])
  \\ qpat_x_assum ‘_ |- _COND _FALSE _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem IF_eqn:
  bool_thy_ok thy ∧
  term_ok (sigof thy) x ∧ term_ok (sigof thy) y ∧
  x has_type Bool ∧ y has_type Bool ⇒
    (thy,[]) |- _IF _TRUE x y === x ∧
    (thy,[]) |- _IF _FALSE x y === y
Proof
  rw [bool_thy_ok_def]
  >- (
    qpat_x_assum ‘_ |- _IF _TRUE _ _ === _’ assume_tac
    \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[x,_X; y,_Y]’ mp_tac)
                      proves_INST
    \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def])
  \\ qpat_x_assum ‘_ |- _IF _FALSE _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[x,_X; y,_Y]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem DIV_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _DIV m n ===
                _COND (n === _NUMERAL _0) (_NUMERAL _0)
                      (_COND (_LESS m n) (_NUMERAL _0)
                             (_SUC (_DIV (_SUB m n) n)))
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _DIV _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N;m,_M]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def, SF DNF_ss]
  \\ drule_then assume_tac WELLTYPED_LEMMA \\ gs []
QED

Theorem MOD_eqn:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _MOD m n ===
                _COND (n === _NUMERAL _0) m
                      (_COND (_LESS m n) m
                             (_MOD (_SUB m n) n))
Proof
  rw [numeral_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _MOD _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N;m,_M]’ mp_tac) proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def, SF DNF_ss]
  \\ drule_then assume_tac WELLTYPED_LEMMA \\ gs []
QED

(* TODO Move *)
Theorem COND_has_type[simp]:
  _COND p m n has_type Num ⇔
  p has_type Bool ∧ m has_type Num ∧ n has_type Num
Proof
  rw [Ntimes has_type_cases 3]
  \\ rw [Ntimes has_type_cases 3]
QED

(* TODO Move *)
Theorem LESS_has_type[simp]:
  _LESS m n has_type Bool ⇔ m has_type Num ∧ n has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

(* TODO Move *)
Theorem SUB_has_type[simp]:
  _SUB m n has_type Num ⇔ m has_type Num ∧ n has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

(* TODO Move *)
Theorem MOD_has_type[simp]:
  _MOD m n has_type Num ⇔ m has_type Num ∧ n has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

(* TODO Move *)
Theorem DIV_has_type[simp]:
  _DIV m n has_type Num ⇔ m has_type Num ∧ n has_type Num
Proof
  rw [Ntimes has_type_cases 3]
QED

Theorem MOD_eqn1:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- _MOD m (_NUMERAL _0) === m
Proof
  rw []
  \\ irule trans_equation_simple
  \\ drule_then (qspecl_then [‘_NUMERAL _0’,‘m’] mp_tac) MOD_eqn
  \\ simp [numeral_thy_ok_terms_ok]
  \\ disch_then (irule_at Any)
  \\ resolve_then Any irule sym_equation replaceL3
  \\ qexists_tac ‘_TRUE’
  \\ conj_tac >- fs [numeral_thy_ok_def]
  \\ irule (COND_eqn |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL) \\ gs []
  \\ simp [term_ok_def, numeral_thy_ok_terms_ok, term_ok_welltyped,
           WELLTYPED_LEMMA, SF SFY_ss]
QED

Theorem DIV_eqn1:
  numeral_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- _DIV m (_NUMERAL _0) === _NUMERAL _0
Proof
  rw []
  \\ irule trans_equation_simple
  \\ drule_then (qspecl_then [‘_NUMERAL _0’,‘m’] mp_tac) DIV_eqn
  \\ simp [numeral_thy_ok_terms_ok]
  \\ disch_then (irule_at Any)
  \\ resolve_then Any irule sym_equation replaceL3
  \\ qexists_tac ‘_TRUE’
  \\ conj_tac >- fs [numeral_thy_ok_def]
  \\ irule (COND_eqn |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL) \\ gs []
  \\ simp [term_ok_def, numeral_thy_ok_terms_ok, term_ok_welltyped,
           WELLTYPED_LEMMA, SF SFY_ss]
QED

Theorem BIT0_0:
  numeral_thy_ok thy ⇒
    (thy,[]) |- _BIT0 _0 === _0
Proof
  strip_tac
  \\ ‘term_ok (sigof thy) _0 ∧ _0 has_type Num’
    by gs [numeral_thy_ok_terms_ok, term_ok_def, has_type_rules]
  \\ drule_all_then assume_tac BIT0_eqn
  \\ irule trans_equation_simple
  \\ first_x_assum (irule_at Any)
  \\ drule_all_then assume_tac (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL ADD_eqn)))
  \\ irule replaceL1
  \\ irule_at Any NUMERAL_eqn \\ simp []
QED

(* -------------------------------------------------------------------------
 * num2term, num2bit
 * ------------------------------------------------------------------------- *)

Theorem num2term_typeof[simp]:
  typeof (num2term n) = Num
Proof
  Induct_on ‘n’ \\ simp [num2term_def]
QED

Theorem num2term_has_type[simp]:
  num2term n has_type Num
Proof
  Induct_on ‘n’ \\ rw [num2term_def]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
QED

Theorem num2term_welltyped[simp]:
  welltyped (num2term n)
Proof
  rw [welltyped_def, num2term_has_type, SF SFY_ss]
QED

Theorem num2term_term_ok:
  numeral_thy_ok thy ⇒ term_ok (sigof thy) (num2term n)
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ Induct_on ‘n’ \\ rw [numeral_thy_ok_def, term_ok_def, num2term_def]
QED

Theorem num2term_VSUBST[simp]:
  ∀n. VSUBST is (num2term n) = num2term n
Proof
  Induct \\ rw [num2term_def, VSUBST_def]
QED

Theorem num2bit_typeof[simp]:
  ∀n. typeof (num2bit n) = Num
Proof
  ho_match_mp_tac num2bit_ind \\ rw []
  \\ rw [Once num2bit_def]
QED

Theorem num2bit_has_type[simp]:
  ∀n. num2bit n has_type Num
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
    \\ ‘term_ok (sigof thy) M ∧ M has_type Num’
      by fs [Abbr ‘M’, num2term_term_ok]
    \\ rw [ADD_eqn, SF SFY_ss])
  \\ rw [ADD_CLAUSES, num2term_def] \\ fs []
  \\ qmatch_goalsub_abbrev_tac ‘_ADD (_SUC N) M’
  \\ ‘term_ok (sigof thy) M ∧ M has_type Num ∧
      term_ok (sigof thy) N ∧ N has_type Num’
      by fs [Abbr ‘M’, Abbr ‘N’, num2term_term_ok]
  \\ irule replaceR2
  \\ first_x_assum (irule_at Any)
  \\ csimp [numeral_thy_ok_terms_ok, term_ok_def, term_ok_welltyped,
            num2term_term_ok, WELLTYPED_LEMMA, SF SFY_ss]
  \\ rw [ADD_eqn, sym_equation, SF SFY_ss]
QED

Theorem ADD_num2term =
  UNDISCH_ALL num2term_ADD |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2term_SUB:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2term (m - n) === _SUB (num2term m) (num2term n)
Proof
  strip_tac
  \\ ‘∀m n. (thy,[]) |-  _SUB (num2term m) (num2term n) === num2term (m - n)’
    suffices_by rw [sym_equation]
  \\ Induct \\ simp []
  >- (
    rw [num2term_def]
    \\ qabbrev_tac ‘M = num2term n’
    \\ irule replaceL1
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ irule trans_equation_simple
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ ‘term_ok (sigof thy) M ∧ M has_type Num’
      by fs [Abbr ‘M’, num2term_term_ok, numeral_thy_ok_terms_ok]
    \\ rw [SUB_eqn, SF SFY_ss])
  \\ Cases \\ gs [num2term_def]
  >- (
    qabbrev_tac ‘M = _SUC (num2term m)’
    \\ irule replaceL2
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ ‘term_ok (sigof thy) M ∧ M has_type Num’
      by fs [Abbr ‘M’, num2term_term_ok, numeral_thy_ok_terms_ok]
    \\ rw [SUB_eqn, SF SFY_ss])
  \\ rename [‘m - n’]
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
  \\ resolve_then Any irule sym_equation trans_equation_simple
  \\ first_x_assum (irule_at Any)
  \\ simp [SUB_eqn, sym_equation, num2term_term_ok]
QED

Theorem SUB_num2term =
  UNDISCH_ALL num2term_SUB |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2term_MUL:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2term (m * n) === _MUL (num2term m) (num2term n)
Proof
  strip_tac
  \\ ‘∀m. (thy,[]) |-  _MUL (num2term m) (num2term n) === num2term (m * n)’
    suffices_by rw [sym_equation]
  \\ Induct \\ simp []
  >- (
    rw [num2term_def]
    \\ qabbrev_tac ‘M = num2term n’
    \\ irule replaceL1
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ irule trans_equation_simple
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ ‘term_ok (sigof thy) M ∧ M has_type Num’
      by fs [Abbr ‘M’, num2term_term_ok, numeral_thy_ok_terms_ok]
    \\ rw [MUL_eqn, SF SFY_ss])
  \\ rw [MULT_SUC, num2term_def]
  \\ irule trans_equation_simple \\ irule_at Any ADD_num2term \\ gs []
  \\ irule replaceR2 \\ first_x_assum (irule_at Any)
  \\ rw [MUL_eqn, sym_equation, num2term_term_ok]
QED

Theorem MUL_num2term =
  UNDISCH_ALL num2term_MUL |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem bool2term_LESS_num2term:
  numeral_thy_ok thy ⇒
    (thy,[]) |- bool2term (m < n) === _LESS (num2term m) (num2term n)
Proof
  strip_tac
  \\ ‘∀m n. (thy,[]) |-  _LESS (num2term m) (num2term n) === bool2term (m < n)’
    suffices_by rw [sym_equation]
  \\ Induct \\ simp []
  >- (
    Cases \\ rw [num2term_def, bool2term_def]
    >- (
      irule replaceL2 \\ irule_at Any NUMERAL_eqn
      \\ irule_at Any (CONJUNCT1 (SIMPR [IMP_CONJ_THM, SF DNF_ss] LESS_eqn))
      \\ qexists_tac ‘_0’ \\ gs [numeral_thy_ok_terms_ok])
    \\ qmatch_goalsub_abbrev_tac ‘_SUC M’
    \\ irule replaceL1
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ ‘term_ok (sigof thy) M ∧ M has_type Num’
      by fs [Abbr ‘M’, num2term_term_ok, numeral_thy_ok_terms_ok]
    \\ rw [LESS_eqn, SF SFY_ss])
  \\ Cases \\ gs [num2term_def, bool2term_def]
  >- (
    qmatch_goalsub_abbrev_tac ‘_LESS M _’
    \\ irule replaceL2
    \\ irule_at Any NUMERAL_eqn \\ simp [numeral_thy_ok_terms_ok]
    \\ ‘term_ok (sigof thy) M ∧ M has_type Num’
      by fs [Abbr ‘M’, num2term_term_ok, numeral_thy_ok_terms_ok]
    \\ rw [LESS_eqn, SF SFY_ss])
  \\ rename [‘m < n’]
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
  \\ resolve_then Any irule sym_equation trans_equation_simple
  \\ first_x_assum (irule_at Any)
  \\ simp [LESS_eqn, sym_equation, num2term_term_ok]
QED

Theorem LESS_bool2term_num2term =
  UNDISCH_ALL bool2term_LESS_num2term |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem bool2term_EQ_num2term:
  numeral_thy_ok thy ⇒
    (thy,[]) |- bool2term (m = n) === (num2term m === num2term n)
Proof
  strip_tac
  \\ ‘∀m n. (thy,[]) |-  (num2term m === num2term n) === bool2term (m = n)’
    suffices_by rw [sym_equation]
  \\ Induct \\ simp []
  >- (
    Cases \\ rw [num2term_def, bool2term_def]
    >- (
      irule replaceL_eq1 \\ irule_at Any NUMERAL_eqn
      \\ irule_at Any replaceL_eq2 \\ irule_at Any NUMERAL_eqn
      \\ gs [numeral_thy_ok_terms_ok, EQ_eqn1])
    \\ irule replaceL_eq1 \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any EQ_eqn2 \\ gs [num2term_term_ok, numeral_thy_ok_terms_ok])
  \\ Cases \\ gs [num2term_def, bool2term_def]
  >- (
    irule replaceL_eq2 \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any EQ_eqn3 \\ gs [num2term_term_ok, numeral_thy_ok_terms_ok])
  \\ rename [‘m = n’]
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
  \\ irule trans_equation_simple \\ first_x_assum (irule_at Any)
  \\ irule EQ_eqn4 \\ gs [num2term_term_ok]
QED

Theorem EQ_bool2term_num2term =
  UNDISCH_ALL bool2term_EQ_num2term |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem SUB_DIV:
  ∀m n. 0 < n ∧ n ≤ m ⇒ SUC ((m - n) DIV n) = m DIV n
Proof
  rw [LESS_OR_EQ] \\ gs [DIVMOD_ID, ZERO_DIV]
  \\ qspecl_then [‘1’,‘n’,‘m’] assume_tac (GEN_ALL DIV_SUB) \\ gs []
  \\ ‘SUC (PRE (m DIV n)) = m DIV n’
    suffices_by rw [prim_recTheory.PRE, ADD1]
  \\ irule (iffLR SUC_PRE)
  \\ gs [X_LT_DIV]
QED

Theorem DIV_num2term:
  numeral_thy_ok thy ⇒
    (thy,[]) |-_DIV (num2term m) (num2term n) === num2term (m SAFEDIV n)
Proof
  strip_tac
  \\ qid_spec_tac ‘n’ \\ qid_spec_tac ‘m’
  \\ completeInduct_on ‘m’ \\ gen_tac
  \\ Cases_on ‘m’
  >- ((* m = 0 *)
    gs [num2term_def, SAFEDIV_def]
    \\ irule replaceL1 \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any trans_equation_simple \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any trans_equation_simple \\ irule_at Any DIV_eqn
    \\ simp [term_ok_def, numeral_thy_ok_terms_ok, num2term_term_ok]
    \\ Cases_on ‘n’ \\ gs [num2term_def]
    >- (
      ‘(thy,[]) |- (_0 === _NUMERAL _0) === (_NUMERAL _0 === _NUMERAL _0)’
        by simp [DEDUCT_ANTISYM_simple, proves_REFL, NUMERAL_eqn, sym_equation,
                 numeral_thy_ok_terms_ok]
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any)
      \\ irule replaceL3
      \\ irule_at Any sym_equation
      \\ qexists_tac ‘_TRUE’
      \\ conj_tac >- fs [numeral_thy_ok_def]
      \\ irule trans_equation_simple
      \\ irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn)))
      \\ gs [numeral_thy_ok_terms_ok, term_ok_def, proves_REFL])
    \\ irule replaceL3
    \\ qexists_tac ‘_FALSE’
    \\ conj_tac
    >- (
      irule sym_equation
      \\ irule EQ_eqn3 \\ gs [num2term_term_ok])
    \\ irule trans_equation_simple
    \\ irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
    \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL]
    \\ resolve_then Any irule sym_equation replaceL3
    \\ qexists_tac ‘_TRUE’
    \\ irule_at Any (DISCH_ALL (cj 2 (UNDISCH_ALL LESS_eqn)))
    \\ qexists_tac ‘_0’ \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok]
    \\ irule trans_equation_simple
    \\ irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn)))
    \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL,
           num2term_def, ZERO_DIV])
  \\ rename [‘SUC m’]
  \\ gs [SAFEDIV_def]
  \\ IF_CASES_TAC \\ gs [num2term_def]
  >- ((* n = 0 *)
    irule replaceL2 \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any trans_equation_simple \\ irule_at Any NUMERAL_eqn
    \\ gs [numeral_thy_ok_terms_ok, DIV_eqn1, num2term_term_ok])
  \\ irule trans_equation_simple \\ irule_at Any DIV_eqn
  \\ gs [num2term_term_ok]
  \\ Cases_on ‘n’ \\ gs [num2term_def] \\ rename [‘_SUC (num2term n)’]
  \\ irule replaceL3
  \\ qexists_tac ‘_FALSE’
  \\ conj_tac
  >- (
    irule sym_equation
    \\ irule EQ_eqn3 \\ gs [num2term_term_ok])
  \\ irule trans_equation_simple
  \\ irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
  \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL]
  \\ drule_then (qspecl_then [‘SUC n’,‘SUC m’] assume_tac)
                bool2term_LESS_num2term
  \\ Cases_on ‘m < n’ \\ gs [bool2term_def, num2term_def]
  >- (
    irule replaceL3 \\ first_x_assum (irule_at Any)
    \\ irule trans_equation_simple
    \\ irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn)))
    \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL,
           LESS_DIV_EQ_ZERO, num2term_def, NUMERAL_eqn])
  \\ irule replaceL3 \\ first_x_assum (irule_at Any)
  \\ irule trans_equation_simple
  \\ irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
  \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL,
         num2term_def]
  \\ simp [Q.SPECL [‘SUC m’,‘SUC n’] SUB_DIV |> SIMPR [SUB] |> GSYM,
           proves_REFL, num2term_term_ok, num2term_def]
  \\ irule MK_COMB_simple \\ gs [proves_REFL, numeral_thy_ok_terms_ok]
  \\ resolve_then Any irule sym_equation replaceL1
  \\ irule_at Any (DISCH_ALL (cj 3 (UNDISCH_ALL SUB_eqn)))
  \\ gs [num2term_term_ok]
  \\ resolve_then Any irule sym_equation replaceL1
  \\ irule_at Any SUB_num2term \\ gs [PULL_FORALL]
  \\ first_x_assum (qspecl_then [‘SUC m - SUC n’,‘SUC n’] assume_tac)
  \\ gs [num2term_def]
QED

Theorem num2term_DIV =
  UNDISCH_ALL DIV_num2term |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem MOD_num2term:
  numeral_thy_ok thy ⇒
    (thy,[]) |-_MOD (num2term m) (num2term n) === num2term (m SAFEMOD n)
Proof
  strip_tac
  \\ qid_spec_tac ‘n’ \\ qid_spec_tac ‘m’
  \\ completeInduct_on ‘m’ \\ gen_tac
  \\ Cases_on ‘m’
  >- ((* m = 0 *)
    simp [num2term_def, SAFEMOD_def]
    \\ irule replaceL1 \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any trans_equation_simple \\ irule_at Any NUMERAL_eqn
    \\ irule_at Any trans_equation_simple \\ irule_at Any MOD_eqn
    \\ simp [term_ok_def, numeral_thy_ok_terms_ok, num2term_term_ok]
    \\ Cases_on ‘n’ \\ gs [num2term_def]
    >- (
      ‘(thy,[]) |- (_0 === _NUMERAL _0) === (_NUMERAL _0 === _NUMERAL _0)’
        by simp [DEDUCT_ANTISYM_simple, proves_REFL, NUMERAL_eqn, sym_equation,
                 numeral_thy_ok_terms_ok]
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any)
      \\ irule replaceL3
      \\ irule_at Any sym_equation
      \\ qexists_tac ‘_TRUE’
      \\ conj_tac >- fs [numeral_thy_ok_def]
      \\ irule trans_equation_simple
      \\ irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn)))
      \\ gs [numeral_thy_ok_terms_ok, term_ok_def, proves_REFL])
    \\ irule replaceL3
    \\ qexists_tac ‘_FALSE’
    \\ conj_tac
    >- (
      irule sym_equation
      \\ irule EQ_eqn3 \\ gs [num2term_term_ok])
    \\ irule trans_equation_simple
    \\ irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
    \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL]
    \\ resolve_then Any irule sym_equation replaceL3
    \\ qexists_tac ‘_TRUE’
    \\ irule_at Any (DISCH_ALL (cj 2 (UNDISCH_ALL LESS_eqn)))
    \\ qexists_tac ‘_0’ \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok]
    \\ irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn)))
    \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL])
  \\ rename [‘SUC m’]
  \\ gs [SAFEMOD_def]
  \\ IF_CASES_TAC \\ gs [num2term_def]
  >- ((* n = 0 *)
    irule replaceL2 \\ irule_at Any NUMERAL_eqn
    \\ gs [numeral_thy_ok_terms_ok, MOD_eqn1, num2term_term_ok])
  \\ irule trans_equation_simple \\ irule_at Any MOD_eqn
  \\ gs [num2term_term_ok]
  \\ Cases_on ‘n’ \\ gs [num2term_def] \\ rename [‘_SUC (num2term n)’]
  \\ irule replaceL3
  \\ qexists_tac ‘_FALSE’
  \\ conj_tac
  >- (
    irule sym_equation
    \\ irule EQ_eqn3 \\ gs [num2term_term_ok])
  \\ irule trans_equation_simple
  \\ irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
  \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL]
  \\ drule_then (qspecl_then [‘SUC n’,‘SUC m’] assume_tac)
                bool2term_LESS_num2term
  \\ Cases_on ‘m < n’ \\ gs [bool2term_def, num2term_def]
  >- (
    irule replaceL3 \\ first_x_assum (irule_at Any)
    \\ irule trans_equation_simple
    \\ irule_at Any (DISCH_ALL (CONJUNCT1 (UNDISCH_ALL COND_eqn)))
    \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL,
           num2term_def])
  \\ irule replaceL3 \\ first_x_assum (irule_at Any)
  \\ irule trans_equation_simple
  \\ irule_at Any (DISCH_ALL (CONJUNCT2 (UNDISCH_ALL COND_eqn)))
  \\ gs [numeral_thy_ok_terms_ok, num2term_term_ok, term_ok_def, proves_REFL,
         num2term_def]
  \\ simp [Q.SPECL [‘SUC m’,‘SUC n’] SUB_MOD |> SIMPR [SUB] |> GSYM,
           proves_REFL, num2term_term_ok]
  \\ resolve_then Any irule sym_equation replaceL1
  \\ irule_at Any (DISCH_ALL (cj 3 (UNDISCH_ALL SUB_eqn)))
  \\ gs [num2term_term_ok]
  \\ resolve_then Any irule sym_equation replaceL1
  \\ irule_at Any SUB_num2term \\ gs [PULL_FORALL]
  \\ first_x_assum (qspecl_then [‘SUC m - SUC n’,‘SUC n’] assume_tac)
  \\ gs [num2term_def]
QED

Theorem num2term_MOD =
  UNDISCH_ALL MOD_num2term |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2bit_num2term:
  numeral_thy_ok thy ⇒
    ∀n. (thy,[]) |- num2bit n === num2term n
Proof
  strip_tac \\ ho_match_mp_tac num2bit_ind \\ rw []
  \\ ‘term_ok (sigof thy) _0 ∧ _0 has_type Num’
    by fs [numeral_thy_ok_terms_ok, has_type_rules]
  \\ rw [num2term_def, Once num2bit_def, proves_REFL]
  >- (
    qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘term_ok (sigof thy) N ∧ N has_type Num’
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
    \\ ‘term_ok (sigof thy) N ∧ N has_type Num’
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

Theorem num2bit_SUB:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m - n) === _SUB (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ irule trans_equation_simple
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceR1 \\ irule_at Any sym_equation
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceL2
  \\ irule_at Any sym_equation \\ irule_at Any num2bit_num2term
  \\ fs [SUB_num2term]
QED

Theorem SUB_num2bit =
  UNDISCH_ALL num2bit_SUB |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2bit_MUL:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m * n) === _MUL (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ irule trans_equation_simple
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceR1 \\ irule_at Any sym_equation
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceL2
  \\ irule_at Any sym_equation \\ irule_at Any num2bit_num2term
  \\ fs [MUL_num2term]
QED

Theorem MUL_num2bit =
  UNDISCH_ALL num2bit_MUL |> MATCH_MP sym_equation |> DISCH_ALL;


Theorem num2bit_DIV:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m SAFEDIV n) === _DIV (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ irule trans_equation_simple
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceR1 \\ irule_at Any sym_equation
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceL2
  \\ irule_at Any sym_equation \\ irule_at Any num2bit_num2term
  \\ fs [DIV_num2term]
QED

Theorem DIV_num2bit =
  UNDISCH_ALL num2bit_DIV |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem num2bit_MOD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m SAFEMOD n) === _MOD (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ irule trans_equation_simple
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceR1 \\ irule_at Any sym_equation
  \\ irule_at Any num2bit_num2term
  \\ irule_at Any replaceL2
  \\ irule_at Any sym_equation \\ irule_at Any num2bit_num2term
  \\ fs [MOD_num2term]
QED

Theorem MOD_num2bit =
  UNDISCH_ALL num2bit_MOD |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem bool2term_LESS_num2bit:
  numeral_thy_ok thy ⇒
    (thy,[]) |- bool2term (m < n) === _LESS (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ resolve_then Any irule sym_equation replaceR1
  \\ irule_at Any num2bit_num2term \\ gs []
  \\ resolve_then Any irule sym_equation replaceL2
  \\ irule_at Any num2bit_num2term \\ gs []
  \\ fs [LESS_bool2term_num2term]
QED

Theorem LESS_bool2term_num2bit =
  UNDISCH_ALL bool2term_LESS_num2bit |> MATCH_MP sym_equation |> DISCH_ALL;

Theorem bool2term_EQ_num2bit:
  numeral_thy_ok thy ⇒
    (thy,[]) |- bool2term (m = n) === (num2bit m === num2bit n)
Proof
  strip_tac
  \\ resolve_then Any irule sym_equation replaceR_eq1
  \\ irule_at Any num2bit_num2term \\ gs []
  \\ resolve_then Any irule sym_equation replaceL_eq2
  \\ irule_at Any num2bit_num2term \\ gs []
  \\ fs [EQ_bool2term_num2term]
QED

Theorem EQ_bool2term_num2bit =
  UNDISCH_ALL bool2term_EQ_num2bit |> MATCH_MP sym_equation |> DISCH_ALL;

(* -------------------------------------------------------------------------
 * Compute values
 * ------------------------------------------------------------------------- *)

Definition cexp_consts_def:
  cexp_consts (Num n) = {} ∧
  cexp_consts (Var s) = {} ∧
  cexp_consts (Pair p q) = cexp_consts p ∪ cexp_consts q ∧
  cexp_consts (Uop uop p) = cexp_consts p ∧
  cexp_consts (Binop bop p q) = cexp_consts p ∪ cexp_consts q ∧
  cexp_consts (If p q r) =  cexp_consts p ∪ cexp_consts q ∪ cexp_consts r ∧
  cexp_consts (Let s p q) = cexp_consts p ∪ cexp_consts q ∧
  cexp_consts (App s cs) = {s, LENGTH cs} ∪ BIGUNION (set (MAP cexp_consts cs))
Termination
  wf_rel_tac ‘measure compute_exp_size’
End

Definition cexp_vars_def:
  cexp_vars (Num n) = {} ∧
  cexp_vars (Var s) = {s} ∧
  cexp_vars (Pair p q) = cexp_vars p ∪ cexp_vars q ∧
  cexp_vars (Uop uop p) = cexp_vars p ∧
  cexp_vars (Binop bop p q) = cexp_vars p ∪ cexp_vars q ∧
  cexp_vars (If p q r) =  cexp_vars p ∪ cexp_vars q ∪ cexp_vars r ∧
  cexp_vars (Let s p q) = cexp_vars p ∪ (cexp_vars q DIFF {s}) ∧
  cexp_vars (App s cs) = BIGUNION (set (MAP cexp_vars cs))
Termination
  wf_rel_tac ‘measure compute_exp_size’
End

(* The semantics of 'ill-typed' operations on the compute_exp type is to
 * return the number 0 (i.e. Num 0n).
 *)

Definition compute_thy_ok_def:
  compute_thy_ok thy ⇔
    numeral_thy_ok thy ∧
    (* Cexp_add *)
    (thy,[]) |- _CEXP_ADD (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                _CEXP_NUM (_ADD _M _N) ∧
    (thy,[]) |- _CEXP_ADD (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM _M ∧
    (thy,[]) |- _CEXP_ADD (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                _CEXP_NUM _N ∧
    (thy,[]) |- _CEXP_ADD (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_sub *)
    (thy,[]) |- _CEXP_SUB (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                _CEXP_NUM (_SUB _M _N) ∧
    (thy,[]) |- _CEXP_SUB (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM _M ∧
    (thy,[]) |- _CEXP_SUB (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_SUB (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_mul *)
    (thy,[]) |- _CEXP_MUL (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                _CEXP_NUM (_MUL _M _N) ∧
    (thy,[]) |- _CEXP_MUL (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_MUL (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_MUL (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_div *)
    (thy,[]) |- _CEXP_DIV (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                _CEXP_NUM (_DIV _M _N) ∧
    (thy,[]) |- _CEXP_DIV (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_DIV (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_DIV (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_mod *)
    (thy,[]) |- _CEXP_MOD (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                _CEXP_NUM (_MOD _M _N) ∧
    (thy,[]) |- _CEXP_MOD (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM _M ∧
    (thy,[]) |- _CEXP_MOD (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_MOD (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_less *)
    (thy,[]) |- _CEXP_LESS (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                _CEXP_NUM (_COND (_LESS _M _N) (_SUC (_NUMERAL _0))
                                               (_NUMERAL _0)) ∧
    (thy,[]) |- _CEXP_LESS (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_LESS (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_LESS (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_if *)
    (thy,[]) |- _CEXP_IF (_CEXP_NUM (_SUC _M)) _P1 _Q1 === _P1 ∧
    (thy,[]) |- _CEXP_IF (_CEXP_PAIR _P2 _Q2) _P1 _Q1 === _P1 ∧
    (thy,[]) |- _CEXP_IF (_CEXP_NUM (_NUMERAL _0)) _P1 _Q1 === _Q1 ∧
    (* Cexp_fst, Cexp_snd *)
    (thy,[]) |- _CEXP_FST (_CEXP_PAIR _P1 _Q1) === _P1 ∧
    (thy,[]) |- _CEXP_FST (_CEXP_NUM _M) === _CEXP_NUM (_NUMERAL _0) ∧
    (thy,[]) |- _CEXP_SND (_CEXP_PAIR _P1 _Q1) === _Q1 ∧
    (thy,[]) |- _CEXP_SND (_CEXP_NUM _M) === _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_ispair *)
    (thy,[]) |- _CEXP_ISPAIR (_CEXP_PAIR _P1 _Q1) ===
                _CEXP_NUM (_SUC (_NUMERAL _0)) ∧
    (thy,[]) |- _CEXP_ISPAIR (_CEXP_NUM _M) ===
                _CEXP_NUM (_NUMERAL _0) ∧
    (* Cexp_eq *)
    (thy,[]) |- _CEXP_EQ _P1 _Q1 ===
                _CEXP_NUM (_COND (_P1 === _Q1)(_SUC (_NUMERAL _0))
                                              (_NUMERAL _0)) ∧
    (thy,[]) |- (_CEXP_PAIR _P1 _Q1 === _CEXP_PAIR _P2 _Q2) ===
                (_IF (_P1 === _P2) (_Q1 === _Q2) _FALSE) ∧
    (thy,[]) |- (_CEXP_NUM _M === _CEXP_NUM _N) === (_M === _N) ∧
    (thy,[]) |- (_CEXP_NUM _M === _CEXP_PAIR _P1 _Q1) === _FALSE ∧
    (thy,[]) |- (_CEXP_PAIR _P1 _Q1 === _CEXP_NUM _N) === _FALSE ∧
    (* Let *)
    (thy,[]) |- _LET _F _P1 === Comb _F _P1
End

Theorem LET_eqn:
  compute_thy_ok thy ∧
  term_ok (sigof thy) f ∧ term_ok (sigof thy) p1 ∧
  f has_type (Fun Cexp Cexp) ∧ p1 has_type Cexp ⇒
    (thy,[]) |- _LET f p1 === Comb f p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _LET _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; f,_F]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_IF_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_IF (_CEXP_NUM (_SUC m)) p1 q1 === p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_IF (_CEXP_NUM (_SUC _)) _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_IF_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_IF (_CEXP_PAIR p2 q2) p1 q1 === p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_IF (_CEXP_PAIR _ _ ) _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_IF_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_IF (_CEXP_NUM (_NUMERAL _0)) p1 q1 === q1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_IF (_CEXP_NUM (_NUMERAL _)) _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_ADD_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _CEXP_ADD (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_ADD m n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_ADD _ _ === _CEXP_NUM (_ADD _ _)’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_ADD_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_ADD (_CEXP_NUM m) (_CEXP_PAIR p1 q1) === _CEXP_NUM m
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_ADD x _ === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_ADD_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_ADD (_CEXP_PAIR p1 q1) (_CEXP_NUM n) === _CEXP_NUM n
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_ADD _ x === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_ADD_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_ADD (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_ADD _ _ === _CEXP_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_SUB_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _CEXP_SUB (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_SUB m n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_SUB _ _ === _CEXP_NUM (_SUB _ _)’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_SUB_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_SUB (_CEXP_NUM m) (_CEXP_PAIR p1 q1) === _CEXP_NUM m
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_SUB x _ === x’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_SUB_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_SUB (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_SUB (_CEXP_PAIR _ _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_SUB_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_SUB (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_SUB (_CEXP_PAIR _ _) (_CEXP_PAIR _ _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MUL_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _CEXP_MUL (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_MUL m n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MUL (_CEXP_NUM _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MUL_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_MUL (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MUL (_CEXP_NUM _) (_CEXP_PAIR _ _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MUL_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_MUL (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MUL (_CEXP_PAIR _ _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MUL_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_MUL (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MUL (_CEXP_PAIR _ _) (_CEXP_PAIR _ _) ===
                        _CEXP_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_DIV_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _CEXP_DIV (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_DIV m n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_DIV (_CEXP_NUM _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_DIV_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_DIV (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_DIV (_CEXP_NUM _) (_CEXP_PAIR _ _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_DIV_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_DIV (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_DIV (_CEXP_PAIR _ _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_DIV_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_DIV (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_DIV (_CEXP_PAIR _ _) (_CEXP_PAIR _ _) ===
                        _CEXP_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MOD_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _CEXP_MOD (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_MOD m n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MOD (_CEXP_NUM _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MOD_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_MOD (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
                _CEXP_NUM m
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MOD (_CEXP_NUM _) (_CEXP_PAIR _ _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MOD_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_MOD (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MOD (_CEXP_PAIR _ _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_MOD_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_MOD (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_MOD (_CEXP_PAIR _ _) (_CEXP_PAIR _ _) ===
                        _CEXP_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_LESS_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) n ∧
  m has_type Num ∧ n has_type Num ⇒
    (thy,[]) |- _CEXP_LESS (_CEXP_NUM m) (_CEXP_NUM n) ===
                _CEXP_NUM (_COND (_LESS m n) (_SUC (_NUMERAL _0))
                                             (_NUMERAL _0))
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_LESS _ _ === _CEXP_NUM (_COND _ _ _)’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_LESS_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  m has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_LESS (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_LESS (_CEXP_NUM _) (_CEXP_PAIR _ _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_LESS_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  n has_type Num ∧ p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_LESS (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_LESS (_CEXP_PAIR _ _) (_CEXP_NUM _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1; n,_N]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_LESS_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  term_ok (sigof thy) p2 ∧ term_ok (sigof thy) q2 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ∧
  p2 has_type Cexp ∧ q2 has_type Cexp ⇒
    (thy,[]) |- _CEXP_LESS (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
                _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_LESS (_CEXP_PAIR _ _) (_CEXP_PAIR _ _) ===
                        _CEXP_NUM (_NUMERAL _0)’ assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_FST_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_FST (_CEXP_PAIR p1 q1) === p1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_FST (_CEXP_PAIR _ _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_FST_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- _CEXP_FST (_CEXP_NUM m) === _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_FST (_CEXP_NUM _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_SND_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_SND (_CEXP_PAIR p1 q1) === q1
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_SND (_CEXP_PAIR _ _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_SND_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- _CEXP_SND (_CEXP_NUM m) === _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_SND (_CEXP_NUM _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_ISPAIR_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ term_ok (sigof thy) q1 ∧
  p1 has_type Cexp ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_ISPAIR (_CEXP_PAIR p1 q1) ===
                _CEXP_NUM (_SUC (_NUMERAL _0))
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_ISPAIR (_CEXP_PAIR _ _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1; q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_ISPAIR_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- _CEXP_ISPAIR (_CEXP_NUM m) === _CEXP_NUM (_NUMERAL _0)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_ISPAIR (_CEXP_NUM _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_def, equation_def, REV_ASSOCD_def]
QED

Theorem CEXP_EQ_eqn1:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ p1 has_type Cexp ∧
  term_ok (sigof thy) q1 ∧ q1 has_type Cexp ⇒
    (thy,[]) |- _CEXP_EQ p1 q1 ===
                _CEXP_NUM (_COND (p1 === q1)(_SUC (_NUMERAL _0))
                                            (_NUMERAL _0))
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- _CEXP_EQ _ _ === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[p1,_P1;q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def]
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ simp []
QED

Theorem CEXP_EQ_eqn2:
  compute_thy_ok thy ∧
  term_ok (sigof thy) p1 ∧ p1 has_type Cexp ∧
  term_ok (sigof thy) q1 ∧ q1 has_type Cexp ∧
  term_ok (sigof thy) p2 ∧ p2 has_type Cexp ∧
  term_ok (sigof thy) q2 ∧ q2 has_type Cexp ⇒
    (thy,[]) |- (_CEXP_PAIR p1 q1 === _CEXP_PAIR p2 q2) ===
                (_IF (p1 === p2) (q1 === q2) _FALSE)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_CEXP_PAIR _ _ === _CEXP_PAIR _ _) === _’
                  assume_tac
  \\ dxrule_at_then (Pos (el 2))
                    (qspec_then ‘[p1,_P1;q1,_Q1;p2,_P2;q2,_Q2]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def]
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ simp []
QED

Theorem CEXP_EQ_eqn3:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type Num ∧
  term_ok (sigof thy) m ∧ m has_type Num ⇒
    (thy,[]) |- (_CEXP_NUM m === _CEXP_NUM n) === (m === n)
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_CEXP_NUM _ === _CEXP_NUM _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N;m,_M]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def]
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ simp []
QED

Theorem CEXP_EQ_eqn4:
  compute_thy_ok thy ∧
  term_ok (sigof thy) m ∧ m has_type Num ∧
  term_ok (sigof thy) p1 ∧ p1 has_type Cexp ∧
  term_ok (sigof thy) q1 ∧ q1 has_type Cexp ⇒
    (thy,[]) |- (_CEXP_NUM m === _CEXP_PAIR p1 q1) === _FALSE
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_CEXP_NUM _ === _CEXP_PAIR _ _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[m,_M;p1,_P1;q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def]
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ simp []
QED

Theorem CEXP_EQ_eqn5:
  compute_thy_ok thy ∧
  term_ok (sigof thy) n ∧ n has_type Num ∧
  term_ok (sigof thy) p1 ∧ p1 has_type Cexp ∧
  term_ok (sigof thy) q1 ∧ q1 has_type Cexp ⇒
    (thy,[]) |- (_CEXP_PAIR p1 q1 === _CEXP_NUM n) === _FALSE
Proof
  rw [compute_thy_ok_def]
  \\ qpat_x_assum ‘_ |- (_CEXP_PAIR _ _ === _CEXP_NUM _) === _’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[n,_N;p1,_P1;q1,_Q1]’ mp_tac)
                    proves_INST
  \\ dsimp [VSUBST_thm, equation_def, REV_ASSOCD_def]
  \\ dxrule WELLTYPED_LEMMA
  \\ dxrule WELLTYPED_LEMMA
  \\ simp []
QED

Theorem compute_thy_ok_terms_ok:
  compute_thy_ok thy ⇒
    (* bools *)
    term_ok (sigof thy) _TRUE ∧
    term_ok (sigof thy) _FALSE ∧
    term_ok (sigof thy) _COND_TM ∧
    term_ok (sigof thy) _IF_TM ∧
    (* nums *)
    term_ok (sigof thy) _ADD_TM ∧
    term_ok (sigof thy) _SUB_TM ∧
    term_ok (sigof thy) _MUL_TM ∧
    term_ok (sigof thy) _DIV_TM ∧
    term_ok (sigof thy) _MOD_TM ∧
    term_ok (sigof thy) _LESS_TM ∧
    term_ok (sigof thy) _0 ∧
    term_ok (sigof thy) _SUC_TM ∧
    term_ok (sigof thy) _BIT0_TM ∧
    term_ok (sigof thy) _BIT1_TM ∧
    term_ok (sigof thy) _NUMERAL_TM ∧
    (* cexps *)
    term_ok (sigof thy) _CEXP_ADD_TM ∧
    term_ok (sigof thy) _CEXP_SUB_TM ∧
    term_ok (sigof thy) _CEXP_MUL_TM ∧
    term_ok (sigof thy) _CEXP_DIV_TM ∧
    term_ok (sigof thy) _CEXP_MOD_TM ∧
    term_ok (sigof thy) _CEXP_LESS_TM ∧
    term_ok (sigof thy) _CEXP_NUM_TM ∧
    term_ok (sigof thy) _CEXP_IF_TM ∧
    term_ok (sigof thy) _CEXP_PAIR_TM ∧
    term_ok (sigof thy) _CEXP_FST_TM ∧
    term_ok (sigof thy) _CEXP_SND_TM ∧
    term_ok (sigof thy) _CEXP_ISPAIR_TM ∧
    term_ok (sigof thy) _CEXP_EQ_TM ∧
    (* let *)
    term_ok (sigof thy) _LET_TM ∧
    (* types *)
    type_ok (tysof thy) Cexp
Proof
  simp [compute_thy_ok_def] \\ strip_tac
  \\ dxrule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ rpt (first_x_assum (irule_at Any))
  \\ rpt (dxrule_then strip_assume_tac proves_term_ok) \\ rfs []
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

Theorem compute_thy_ok_bool_thy_ok[simp]:
  compute_thy_ok thy ⇒ bool_thy_ok thy
Proof
  rw [compute_thy_ok_def]
QED

Theorem cexp2term_typeof[simp]:
  ∀cv. typeof (cexp2term cv) = Cexp
Proof
  ho_match_mp_tac cexp2term_ind \\ rw []
  \\ simp [cexp2term_def, FOLDL_MAP]
  >~ [‘bop2term _’] >- (
    Cases_on ‘bop’ \\ gs [bop2term_def])
  >~ [‘uop2term _’] >- (
    Cases_on ‘uop’ \\ gs [uop2term_def])
  \\ pop_assum mp_tac
  \\ ‘∀tm.
        typeof tm = app_type (LENGTH cs) ⇒
          typeof (FOLDL (λx y. Comb x (cexp2term y)) tm cs) = Cexp ’
    suffices_by rw [SF SFY_ss]
  \\ Induct_on ‘cs’
  \\ simp [app_type]
QED

Theorem cexp2term_has_type[simp]:
  ∀cv. cexp2term cv has_type Cexp
Proof
  ho_match_mp_tac cexp2term_ind \\ rw [] \\ simp [cexp2term_def]
  >~ [‘_CEXP_NUM _’] >- (
    rw [Ntimes has_type_cases 3]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘uop2term _’] >- (
    Cases_on ‘uop’ \\ simp [uop2term_def]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘_CEXP_PAIR _ _’] >- (
    rw [Ntimes has_type_cases 3])
  >~ [‘_CEXP_IF _ _ _’] >- (
    rw [Ntimes has_type_cases 3]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘bop2term _ _ _’] >- (
    Cases_on ‘bop’ \\ simp [bop2term_def]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘_LET _ _’] >- (
    rw [Ntimes has_type_cases 3]
    \\ rw [Ntimes has_type_cases 3])
  >~ [‘Var _’] >- (
    rw [has_type_rules])
  \\ simp [FOLDL_MAP]
  \\ ‘∀tm.
        tm has_type app_type (LENGTH cs) ⇒
          FOLDL (λx y. Comb x (cexp2term y)) tm cs has_type Cexp ’
    suffices_by rw [has_type_rules, SF SFY_ss]
  \\ Induct_on ‘cs’ \\ rw [app_type]
  \\ gs [has_type_rules, SF SFY_ss, SF DNF_ss]
QED

Theorem cexp2term_welltyped[simp]:
  ∀cv. welltyped (cexp2term cv)
Proof
  rw [welltyped_def, cexp2term_has_type, SF SFY_ss]
QED

Theorem bop2term_term_ok:
  compute_thy_ok thy ⇒
    typeof tm1 = Cexp ∧ typeof tm2 = Cexp ∧
    term_ok (sigof thy) tm1 ∧ term_ok (sigof thy) tm2 ⇒
      term_ok (sigof thy) (bop2term bop tm1 tm2)
Proof
  rw []
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ Cases_on ‘bop’ \\ gs [bop2term_def]
  \\ simp [term_ok_def, term_ok_welltyped, SF SFY_ss]
QED

Theorem uop2term_term_ok:
  compute_thy_ok thy ⇒
    typeof tm = Cexp ∧
    term_ok (sigof thy) tm ⇒
      term_ok (sigof thy) (uop2term uop tm)
Proof
  rw []
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ Cases_on ‘uop’ \\ gs [uop2term_def]
  \\ simp [term_ok_def, term_ok_welltyped, SF SFY_ss]
QED

Theorem cexp2term_term_ok:
  compute_thy_ok thy ⇒
    ∀cv.
      (∀c n.
        (c,n) ∈ cexp_consts cv ⇒
          term_ok (sigof thy) (Const c (app_type n))) ⇒
        term_ok (sigof thy) (cexp2term cv)
Proof
  strip_tac
  \\ drule_then strip_assume_tac compute_thy_ok_terms_ok
  \\ ho_match_mp_tac cexp2term_ind \\ rw []
  \\ gs [cexp2term_def, cexp_consts_def]
  >~ [‘_CEXP_NUM _’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  >~ [‘uop2term _’] >- (
    irule uop2term_term_ok \\ gs [])
  >~ [‘_CEXP_PAIR _ _ ’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  >~ [‘bop2term _ _ _ ’] >- (
    irule bop2term_term_ok \\ gs [])
  >~ [‘_CEXP_IF _ _ _ ’] >- (
    simp [term_ok_def, compute_thy_ok_def, num2bit_term_ok, SF SFY_ss])
  >~ [‘_LET _ _’] >- (
    simp [term_ok_def])
  >~ [‘Var s _’] >- (
    simp [term_ok_def])
  \\ gvs [FOLDL_MAP, MEM_MAP, SF SFY_ss, SF DNF_ss]
  \\ ‘∀tm.
        term_ok (sigof thy) tm ∧
        tm has_type (app_type (LENGTH cs)) ⇒
          term_ok (sigof thy) (FOLDL (λx y. Comb x (cexp2term y)) tm cs)’
    suffices_by rw [term_ok_def, has_type_rules]
  \\ rpt (qpat_x_assum ‘term_ok _ _’ kall_tac)
  \\ Induct_on ‘cs’
  \\ rw [app_type, SF SFY_ss, SF DNF_ss]
  \\ first_x_assum irule \\ fs [SF SFY_ss]
  \\ simp [has_type_rules, cexp2term_has_type, SF SFY_ss]
  \\ simp [term_ok_def, term_ok_welltyped, SF SFY_ss]
  \\ irule_at Any WELLTYPED_LEMMA \\ fs [SF SFY_ss]
QED

(* TODO move *)
Theorem bool2term_term_ok[simp]:
  bool_thy_ok thy ⇒
    term_ok (sigof thy) (bool2term b)
Proof
  Cases_on ‘b’ \\ rw [bool2term_def]
  \\ gs [bool_thy_ok_terms_ok]
QED

Theorem cexp_value_no_consts:
  ∀v. cexp_value v ⇒ cexp_consts v = {}
Proof
  ho_match_mp_tac cexp_value_ind
  \\ rw [cexp_value_def, cexp_consts_def]
QED

Theorem bool2term_EQ_cexpterm:
  compute_thy_ok thy ⇒
    cexp_value p ∧ cexp_value q ⇒
    (thy,[]) |- bool2term (p = q) === (cexp2term p === cexp2term q)
Proof
  strip_tac
  \\ ‘∀p q. cexp_value p ∧ cexp_value q ⇒
              (thy,[]) |-  (cexp2term p === cexp2term q) === bool2term (p = q)’
    suffices_by rw [sym_equation]
  \\ ho_match_mp_tac cexp2term_ind \\ rw []
  >~ [‘Num n’] >- (
    rw [cexp2term_def]
    \\ Cases_on ‘q = Num n’ \\ gvs [bool2term_def, cexp2term_def]
    >- (
      irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn3
      \\ gs [num2bit_term_ok]
      \\ resolve_then Any irule sym_equation replaceL_eq1
      \\ irule_at Any NUMERAL_eqn
      \\ resolve_then Any (irule_at Any) sym_equation replaceL_eq2
      \\ irule_at Any NUMERAL_eqn
      \\ irule_at Any trans_equation_simple
      \\ irule_at Any EQ_bool2term_num2bit
      \\ simp [bool2term_def, proves_REFL, num2bit_term_ok,
               bool_thy_ok_terms_ok])
    \\ Cases_on ‘∃m. q = Num m’ \\ gvs [cexp2term_def]
    >- (
      irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn3
      \\ gs [num2bit_term_ok]
      \\ resolve_then Any irule sym_equation replaceL_eq1
      \\ irule_at Any NUMERAL_eqn
      \\ resolve_then Any (irule_at Any) sym_equation replaceL_eq2
      \\ irule_at Any NUMERAL_eqn
      \\ irule_at Any trans_equation_simple
      \\ irule_at Any EQ_bool2term_num2bit
      \\ simp [bool2term_def, proves_REFL, num2bit_term_ok,
               bool_thy_ok_terms_ok])
    \\ ‘∃p1 q1. q = Pair p1 q1’
      by (Cases_on ‘q’ \\ gs [])
    \\ gvs [cexp2term_def]
    \\ irule CEXP_EQ_eqn4
    \\ gs [num2bit_term_ok, cexp_value_no_consts, cexp2term_term_ok])
  >~ [‘Pair p1 q1’] >- (
    gs [cexp2term_def]
    \\ Cases_on ‘q = Pair p1 q1’ \\ gvs [bool2term_def, cexp2term_def]
    >- (
      irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn2
      \\ gs [cexp2term_term_ok, cexp_value_no_consts]
      \\ qpat_x_assum ‘cexp_value q1’ assume_tac
      \\ first_x_assum (drule_then assume_tac)
      \\ qpat_x_assum ‘cexp_value p1’ assume_tac
      \\ first_x_assum (drule_then assume_tac)
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any) \\ simp [bool2term_def]
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any) \\ simp [bool2term_def]
      \\ gs [numeral_thy_ok_terms_ok, has_type_rules, IF_eqn])
    \\ Cases_on ‘∃p2 q2. q = Pair p2 q2’ \\ gvs [cexp2term_def]
    >- (
      first_x_assum (qspec_then ‘q2’ assume_tac)
      \\ first_x_assum (qspec_then ‘p2’ assume_tac) \\ gs []
      \\ irule trans_equation_simple \\ irule_at Any CEXP_EQ_eqn2
      \\ gs [cexp2term_term_ok, cexp_value_no_consts]
      \\ resolve_then Any irule sym_equation replaceL3
      \\ first_x_assum (irule_at Any) \\ simp []
      \\ resolve_then Any irule sym_equation replaceL1
      \\ first_x_assum (irule_at Any) \\ simp []
      \\ Cases_on ‘p2 = p1’ \\ Cases_on ‘q2 = q1’
      \\ gs [numeral_thy_ok_terms_ok, bool2term_term_ok, has_type_rules,
             IF_eqn, bool2term_def])
    \\ ‘∃n. q = Num n’
      by (Cases_on ‘q’ \\ gs [])
    \\ gvs [cexp2term_def]
    \\ irule CEXP_EQ_eqn5
    \\ gs [num2bit_term_ok, cexp_value_no_consts, cexp2term_term_ok])
QED

Theorem EQ_bool2term_cexpterm:
  compute_thy_ok thy ⇒
    cexp_value p ∧ cexp_value q ⇒
    (thy,[]) |- (cexp2term p === cexp2term q) === bool2term (p = q)
Proof
  rw [] \\ irule sym_equation
  \\ rw [bool2term_EQ_cexpterm]
QED

val _ = export_theory ();

