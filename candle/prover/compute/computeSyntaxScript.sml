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

(* Lists *)

Overload list_ty = “λty. Tyapp «list» [ty]”;
Overload "_NIL" = “λty. Const «[]» (list_ty ty)”;
Overload "_CONS_TM" = “λty. Const «::» (Fun ty (Fun (list_ty ty) (list_ty ty)))”;
Overload "_CONS" = “λty h t. Comb (Comb (_CONS_TM ty) h) t”;
Overload "_H" = “λty. Var «h» ty”;
Overload "_T" = “λty. Var «t» (list_ty ty)”;

(* Bools *)

Overload "_A" = “Tyvar «A»”;
Overload "_B" = “Tyvar «B»”;
Overload "_FORALL_TM" = “Const «!» (Fun (Fun _A Bool) Bool)”;
Overload "_FORALL" = “λv b. Comb _FORALL_TM (Abs v b)”;
Overload "_P" = “Var «P» (Fun _A Bool)”;
Overload "_Q" = “Var «Q» Bool”;
Overload "_X" = “Var «x» _A”;
Overload "_T" = “Const «T» Bool”;

(* Pairs *)

Overload pair_ty = “Tyapp «#» [_A; _B]”;
Overload npr_ty = “Tyapp «npr» []”;
Overload "_P1" = “Var «P1» pair_ty”;
Overload "_P2" = “Var «P2» pair_ty”;
Overload "_Q1" = “Var «Q1» pair_ty”;
Overload "_Q2" = “Var «Q2» pair_ty”;
Overload "_NPR_NUM_TM" = “Const «Npr_num» (Fun num_ty npr_ty)”;
Overload "_NPR_PAIR_TM" = “Const «Npr_pair» (Fun npr_ty (Fun npr_ty npr_ty))”;
Overload "_NPR_NUM" = “λtm. Comb _NPR_NUM_TM tm”;
Overload "_NPR_PAIR" = “λt1 t2. Comb (Comb _NPR_PAIR_TM t1) t2”;
Overload "_NPR_ADD_TM" = “Const «npr_add» (Fun npr_ty (Fun npr_ty npr_ty))”;
Overload "_NPR_ADD" = “λt1 t2. Comb (Comb _NPR_ADD_TM t1) t2”;
Overload "_NPR_FST_TM" = “Const «npr_fst» (Fun npr_ty npr_ty)”;
Overload "_NPR_FST" = “λtm. Comb _NPR_FST_TM tm”;
Overload "_NPR_SND_TM" = “Const «npr_snd» (Fun npr_ty npr_ty)”;
Overload "_NPR_SND" = “λtm. Comb _NPR_SND_TM tm”;

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

Theorem replaceL2:
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

(* -------------------------------------------------------------------------
 * Natural numbers
 * ------------------------------------------------------------------------- *)

(* All the necessary constants defined with the right types and
 * with the right defining equations (and some lemmas).
 *)

Definition numeral_thy_ok_def:
  numeral_thy_ok thy ⇔
    theory_ok thy ∧
    (* NUMERAL *)
    (thy,[]) |- _NUMERAL _N === _N ∧
    (* BIT0, BIT1 *)
    (thy,[]) |- _BIT0 _N === _ADD _N _N ∧
    (thy,[]) |- _BIT1 _N === _SUC (_ADD _N _N) ∧
    (* ADD *)
    (thy,[]) |- _ADD _0 _M === _M ∧
    (thy,[]) |- _ADD (_SUC _N) _M === _SUC (_ADD _N _M)
End

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
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
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

Theorem BIT0_0:
  numeral_thy_ok thy ⇒
    (thy,[]) |- _BIT0 _0 === _0
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ gs [numeral_thy_ok_def]
  \\ ‘(thy,[]) |- _BIT0 _0 === _ADD _0 _0’
    by (qpat_x_assum ‘_ |- _BIT0 _N === _’ assume_tac
        \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[_0,_N]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Once has_type_cases])
  \\ irule trans_equation_simple
  \\ first_x_assum (irule_at Any)
  \\ qpat_x_assum ‘_ |- _ADD _0 _M === _M’ assume_tac
  \\ dxrule_at_then (Pos (el 2)) (qspec_then ‘[_0,_M]’ mp_tac) proves_INST
  \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Once has_type_cases]
QED

Theorem num2term_ADD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2term (m + n) === _ADD (num2term m) (num2term n)
Proof
  strip_tac \\ qid_spec_tac ‘m’
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ gs [numeral_thy_ok_def]
  \\ Induct \\ simp []
  >- (
    rw [num2term_def]
    \\ qabbrev_tac ‘M = num2term n’
    \\ qpat_x_assum ‘_ |- _ADD _0 _M === _M’ assume_tac
    \\ drule_at_then (Pos (el 2)) (qspec_then ‘[M,_M]’ mp_tac) proves_INST
    \\ simp [VSUBST_def, REV_ASSOCD, equation_def, Abbr ‘M’, term_ok_def,
             num2term_term_ok, numeral_thy_ok_def, sym_equation])
  \\ rw [ADD_CLAUSES, num2term_def] \\ fs []
  \\ qmatch_goalsub_abbrev_tac ‘_ADD (_SUC N) M’
  \\ ‘(thy,[]) |- _ADD (_SUC N) _M === _SUC (_ADD N _M)’
    by (qpat_x_assum ‘_ |- _ADD _ _ === _’ assume_tac
        \\ drule_at_then (Pos (el 2)) (qspec_then ‘[N,_N]’ mp_tac) proves_INST
        \\ simp [VSUBST_def, REV_ASSOCD, equation_def, term_ok_def, Abbr ‘N’,
                 num2term_term_ok, numeral_thy_ok_def])
  \\ ‘(thy,[]) |- _ADD (_SUC N) M === _SUC (_ADD N M)’
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
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ gs [numeral_thy_ok_def]
  \\ rw [num2term_def, Once num2bit_def, proves_REFL]
  >- (
    qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘(thy,[]) |- _BIT0 (num2bit (n DIV 2)) === _BIT0 N’
      by rw [MK_COMB_simple, proves_REFL]
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ qpat_x_assum ‘_ |- _BIT0 _N === _’ assume_tac
    \\ ‘(thy,[]) |- _BIT0 N === _ADD N N’
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
    qpat_x_assum ‘_ |- _BIT1 _N === _’ assume_tac
    \\ qabbrev_tac ‘N = num2term (n DIV 2)’
    \\ ‘(thy,[]) |- _BIT1 (num2bit (n DIV 2)) === _BIT1 N’
      by rw [MK_COMB_simple, proves_REFL]
    \\ irule trans_equation_simple
    \\ first_x_assum (irule_at Any)
    \\ ‘(thy,[]) |- _BIT1 N === _SUC (_ADD N N)’
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
    \\ simp [proves_REFL, term_ok_def, Abbr ‘N’, num2term_term_ok,
             numeral_thy_ok_def])
QED

Theorem num2bit_ADD:
  numeral_thy_ok thy ⇒
    (thy,[]) |- num2bit (m + n) === _ADD (num2bit m) (num2bit n)
Proof
  strip_tac
  \\ drule_then strip_assume_tac numeral_thy_ok_terms_ok
  \\ drule_then assume_tac num2bit_num2term
  \\ first_assum (qspec_then ‘n’ assume_tac)
  \\ first_assum (qspec_then ‘m’ assume_tac)
  \\ first_x_assum (qspec_then ‘m + n’ assume_tac)
  \\ gs [numeral_thy_ok_def]
  \\ irule trans_equation_simple
  \\ first_assum (irule_at Any)
  \\ irule trans_equation_simple
  \\ qexists_tac ‘_ADD (num2term m) (num2term n)’
  \\ simp [num2term_ADD, numeral_thy_ok_def, MK_COMB_simple, proves_REFL,
           sym_equation]
QED

Theorem ADD_num2bit =
  UNDISCH_ALL num2bit_ADD |> MATCH_MP sym_equation |> DISCH_ALL;

(* -------------------------------------------------------------------------
 * Lists
 * ------------------------------------------------------------------------- *)

Definition list_thy_ok_def:
  list_thy_ok thy ⇔
    theory_ok thy ∧
    (∀ty. type_ok (tysof thy) ty ⇒ term_ok (sigof thy) (_NIL ty)) ∧
    (∀ty. type_ok (tysof thy) ty ⇒ term_ok (sigof thy) (_CONS_TM ty))
End

Definition list2term_def:
  list2term f ty [] = _NIL ty ∧
  list2term f ty (h::t) = _CONS ty (f h) (list2term f ty t)
End

Theorem list2term_typeof[local,simp]:
  (∀x. MEM x xs ⇒ typeof (f x) = ty) ⇒
    typeof (list2term f ty xs) = list_ty ty
Proof
  Induct_on ‘xs’ \\ rw [list2term_def]
QED

Theorem list2term_has_type[local,simp]:
  (∀x. MEM x xs ⇒ f x has_type ty) ⇒
    list2term f ty xs has_type list_ty ty
Proof
  Induct_on ‘xs’ \\ rw [list2term_def]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
QED

Theorem list2term_welltyped[local,simp]:
  (∀x. MEM x xs ⇒ f x has_type ty) ⇒
    welltyped (list2term f ty xs)
Proof
  rw [welltyped_def]
  \\ irule_at Any list2term_has_type \\ gs []
QED

Theorem list2term_term_ok[local]:
  list_thy_ok thy ⇒
  type_ok (tysof thy) ty ∧
  (∀x. MEM x xs ⇒ term_ok (sigof thy) (f x) ∧ typeof (f x) = ty) ⇒
    term_ok (sigof thy) (list2term f ty xs)
Proof
  strip_tac \\ fs [list_thy_ok_def]
  \\ Induct_on ‘xs’ \\ rw [list2term_def]
  \\ rw [term_ok_def] \\ gs [term_ok_welltyped, SF SFY_ss, SF DNF_ss]
QED

(* -------------------------------------------------------------------------
 * Bools
 * ------------------------------------------------------------------------- *)

Definition bool_thy_ok_def:
  bool_thy_ok thy ⇔
    theory_ok thy ∧
    (thy,[]) |- _T === (Abs _X _X === Abs _X _X) ∧
    (thy,[]) |- _FORALL_TM === Abs _P (_P === Abs _X _T)
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

(*
Theorem FORALL_SPEC:
  bool_thy_ok thy ⇒
    (thy,[]) |- _FORALL _X _Q ⇒ (thy,[]) |- _Q
Proof
  cheat
QED
 *)

(* -------------------------------------------------------------------------
 * Pairs
 * ------------------------------------------------------------------------- *)

Datatype:
  num_pair = Pair num_pair num_pair
           | Num num
           | Fst num_pair
           | Snd num_pair
           | Add num_pair num_pair
End

(* The semantics of 'ill-typed' operations on the num_pair type is as follows:
 * return the number 0 (i.e. Num 0n).
 *
 *)

Definition num_pair_thy_ok_def:
  num_pair_thy_ok thy ⇔
    numeral_thy_ok thy ∧
    (* npr_add *)
    (thy,[]) |- _NPR_ADD (_NPR_NUM _N) (_NPR_NUM _M) === _NPR_NUM (_ADD _N _M) ∧
    (thy,[]) |- _NPR_ADD (_NPR_NUM _N) (_NPR_PAIR _P1 _Q1) === _NPR_NUM _N ∧
    (thy,[]) |- _NPR_ADD (_NPR_PAIR _P1 _Q1) (_NPR_NUM _M) === _NPR_NUM _M ∧
    (thy,[]) |- _NPR_ADD (_NPR_PAIR _P1 _Q1) (_NPR_PAIR _P2 _Q2) ===
                _NPR_NUM _0 ∧
    (* npr_fst *)
    (thy,[]) |- _NPR_FST (_NPR_PAIR _P1 _Q1) === _P1 ∧
    (thy,[]) |- _NPR_FST (_NPR_NUM _N) === _NPR_NUM _0 ∧
    (* npr_snd *)
    (thy,[]) |- _NPR_SND (_NPR_PAIR _P1 _Q1) === _Q1 ∧
    (thy,[]) |- _NPR_SND (_NPR_NUM _N) === _NPR_NUM _0
End

Theorem num_pair_thy_ok_terms_ok:
  num_pair_thy_ok thy ⇒
    (* nums *)
    term_ok (sigof thy) _ADD_TM ∧
    term_ok (sigof thy) _0 ∧
    term_ok (sigof thy) _SUC_TM ∧
    term_ok (sigof thy) _BIT0_TM ∧
    term_ok (sigof thy) _BIT1_TM ∧
    term_ok (sigof thy) _NUMERAL_TM ∧
    (* nprs *)
    term_ok (sigof thy) _NPR_ADD_TM ∧
    term_ok (sigof thy) _NPR_FST_TM ∧
    term_ok (sigof thy) _NPR_SND_TM ∧
    term_ok (sigof thy) _NPR_NUM_TM ∧
    term_ok (sigof thy) _NPR_PAIR_TM
Proof
  simp [num_pair_thy_ok_def] \\ strip_tac
  \\ dxrule_then strip_assume_tac numeral_thy_ok_terms_ok \\ gs []
  \\ rpt (dxrule_then assume_tac proves_term_ok) \\ rfs []
  \\ fs [equation_def, term_ok_def, SF SFY_ss]
QED

Definition npr2term_def:
  npr2term (Num n) = _NPR_NUM (_NUMERAL (num2bit n)) ∧
  npr2term (Pair p q) = _NPR_PAIR (npr2term p) (npr2term q) ∧
  npr2term (Fst p) = _NPR_FST (npr2term p) ∧
  npr2term (Snd p) = _NPR_SND (npr2term p) ∧
  npr2term (Add p q) = _NPR_ADD (npr2term p) (npr2term q)
End

Theorem npr2term_typeof[local,simp]:
  typeof (npr2term np) = npr_ty
Proof
  Induct_on ‘np’ \\ simp [npr2term_def]
QED

Theorem npr2term_has_type[local,simp]:
  npr2term np has_type npr_ty
Proof
  Induct_on ‘np’ \\ rw [npr2term_def]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
  \\ rw [Once has_type_cases]
QED

Theorem npr2term_welltyped[local,simp]:
  welltyped (npr2term np)
Proof
  rw [welltyped_def, npr2term_has_type, SF SFY_ss]
QED

Theorem npr2term_term_ok[local]:
  num_pair_thy_ok thy ⇒ term_ok (sigof thy) (npr2term np)
Proof
  strip_tac
  \\ drule_then strip_assume_tac num_pair_thy_ok_terms_ok
  \\ Induct_on ‘np’ \\ rw [term_ok_def, npr2term_def]
  \\ fs [num_pair_thy_ok_def, num2bit_term_ok, SF SFY_ss]
QED

Theorem npr2term_VSUBST[local,simp]:
  ∀np. VSUBST is (npr2term np) = npr2term np
Proof
  Induct \\ rw [npr2term_def, VSUBST_def]
QED

val _ = export_theory ();

