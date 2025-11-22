(*
  Implementation of a concrete CP-to-ILP phase
*)
Theory cp_to_ilpImpl
Libs
  preamble
Ancestors
  pbc ilp cp_to_ilp mlstring

(*
  In this file, we will prove encodings from
  mlstring-variabled CP constraints.

  mlstring constraint

  into

  (mlstring option # (mlstring, cvar) iconstraint)

  where cvar is mlstring reif + num

  The mlstring option is an annotation.
*)

(**
WEI-LIN:
ciconstraint has the form
(int, mlstring-named integer variable) list,
(int, cvar-named Boolean variable) list,
RHS

a "concrete" ILP constraint consists of an optional annotation
and a ciconstraint
 **)
Type cvar = ``:(mlstring reif + num)``
Type ciconstraint = ``:(mlstring, cvar) iconstraint``

(* TODO: replace ge/eq with faster representations. *)
(**
WEI-LIN:
encoding configuration is a record in which
ge has the form
(var "X≥1", var "X≥-3", ...)
eq has the form
(var "Y=9", var "Y=-100", ...)
 **)
Datatype:
  enc_conf =
    <|
       fresh : num (* The next fresh var names for flags *)
     ; ge : (mlstring # int list) list
     ; eq : (mlstring # int list) list
    |>
End

Definition next_fresh_def:
  next_fresh ec =
  let f = ec.fresh in
  (f, ec with fresh := f+1)
End

(***
  Semantic tools
***)

(* TODO *)
(**
WEI-LIN:
wb is an assignment for (mlstring+flag)-named variables,
wbf is an assignment for cvar-named variables.
A flag can be associated with multiple num-named variables,
fl is a mapping from num-named variables to flags.
 **)
Definition agree_on_fl_def:
  agree_on_fl fl wb wbf ⇔
  (∀x. wb (INL x) = wbf (INL x)) ∧
  (∀x y.
    ALOOKUP fl y = SOME x ⇒
    wb (INR x) = wbf (INR y))
End

Definition mods_fl_def:
  mods_fl fl (n:num) m ⇔
  ∀x. x ∈ set (MAP FST fl) ⇒
    n ≤ x ∧ x < m
End

Theorem mods_fl_nil[simp]:
  mods_fl [] a b
Proof
  rw[mods_fl_def]
QED

Theorem mods_fl_sing[simp]:
  mods_fl [(f, v)] f (f+1)
Proof
  rw[mods_fl_def]
QED

(* lookup for when the given ge for a variable has been encoded *)
(**
WEI-LIN:
The next two definitions check whether the reification variables
"Y≥n" and "Y=n", respectively, have been encoded
 **)
Definition has_ge_def:
  has_ge Y n ec =
  case ALOOKUP ec.ge Y of
    NONE => F
  | SOME ls => MEM n ls
End

Definition has_eq_def:
  has_eq Y n ec =
  case ALOOKUP ec.eq Y of
    NONE => F
  | SOME ls => MEM n ls
End

(**
WEI-LIN:
wbf, wi and ec are "consistent"
 **)
Definition good_reif_def:
  good_reif wbf wi ec ⇔
  (∀Y n. has_ge Y n ec ⇒ (wbf (INL (Ge Y n)) ⇔ wi Y ≥ n)) ∧
  (∀Y n. has_eq Y n ec ⇒ (wbf (INL (Eq Y n)) ⇔ wi Y = n))
End

(**
WEI-LIN:
fresh from ec is irrelevant to good_reif_def
 **)
Theorem good_reif_with_fresh[simp]:
  good_reif wbf wi (ec with fresh := f) =
  good_reif wbf wi ec
Proof
  rw[good_reif_def,has_ge_def,has_eq_def]
QED

(* enc_rel, just a shorthand *)
(**
WEI-LIN:
es:  an app_list of optionally annotated "concrete" ILP constraints
     encoding a CP constraint
es': a list of "abstract" ILP constraints encoding the same CP constraint
ec:  old encoding configuration, before encoding the CP constraint
ec': new encoding configuration, after encoding the CP constraint
fl:  lookup table for the incremental (num, mlstring flag) from ec to ec'
wi:  assignment for mlstring-named integer variables
 **)
Definition enc_rel_def:
  enc_rel fl wi es es' ec ec' ⇔
  mods_fl fl ec.fresh ec'.fresh ∧
  ec.fresh ≤ ec'.fresh ∧
  (∀wbf.
    EVERY (λx. iconstraint_sem (SND x) (wi,wbf)) (append es) ∧
    good_reif wbf wi ec ⇒
    agree_on_fl fl
      (λx. case x of INL v => wbf (INL v) | INR v => reify_flag wi v) wbf ∧
    good_reif wbf wi ec') ∧
  ∀wb wbf.
  agree_on_fl fl wb wbf ∧
  good_reif wbf wi ec ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) es' ⇔
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf))
    (append es))
End

Theorem enc_rel_Nil:
  enc_rel [] wi Nil [] ec ec
Proof
  rw[enc_rel_def,agree_on_fl_def]
QED

Theorem agree_on_fl_mods_fl_append:
  mods_fl fl1 f1 f1' ∧
  mods_fl fl2 f1' f2 ⇒
  (agree_on_fl (fl1++fl2)
    (wb:mlstring reif + mlstring flag -> bool)
    (wbf:mlstring reif + num -> bool) ⇔
    agree_on_fl fl1 wb wbf ∧
    agree_on_fl fl2 wb wbf)
Proof
  rw[mods_fl_def,agree_on_fl_def,ALOOKUP_APPEND]>>
  iff_tac>>rw[]
  >- (
    first_x_assum irule>>
    drule ALOOKUP_MEM>>
    CCONTR_TAC>>gvs[AllCaseEqs(),ALOOKUP_NONE]>>
    first_x_assum drule>>
    gvs[MEM_MAP,PULL_EXISTS]>>
    first_x_assum drule>>
    simp[])>>
  gvs[AllCaseEqs()]
QED

Theorem enc_rel_Append:
  enc_rel fl wi es xs ec ec' ∧
  enc_rel fl' wi es' xs' ec' ec'' ⇒
  enc_rel (fl++fl') wi (Append es es') (xs++xs') ec ec''
Proof
  rw[]>>
  fs[enc_rel_def]>>
  CONJ_TAC >- (
    fs[mods_fl_def]>>rw[]>>
    first_x_assum drule>>rw[])>>
  drule_all agree_on_fl_mods_fl_append>>
  rw[]>>
  metis_tac[]
QED

(***
  Dealing with ge / eq
***)
(**
WEI-LIN:
the next two defintions may introduce duplicates?
Not a problem for cencode_ge as it does membership check
before adding a ge
 **)
Definition add_ge_def:
  add_ge Y n ec =
  let tt =
    (case ALOOKUP ec.ge Y of
      NONE => []
    | SOME ls => ls) in
  ec with ge := (Y,n::tt)::ec.ge
End

Definition add_eq_def:
  add_eq Y n ec =
  let tt =
    (case ALOOKUP ec.eq Y of
      NONE => []
    | SOME ls => ls) in
  ec with eq := (Y,n::tt)::ec.eq
End

Theorem add_ge_fresh[simp]:
  (add_ge Y n ec).fresh = ec.fresh
Proof
  rw[add_ge_def]
QED

Theorem add_eq_fresh[simp]:
  (add_eq Y n ec).fresh = ec.fresh
Proof
  rw[add_eq_def]
QED

Theorem has_ge_add_ge[simp]:
  has_ge X n (add_ge Y m ec) ⇔
  X = Y ∧ n = m ∨
  has_ge X n ec
Proof
  rw[has_ge_def,add_ge_def]>>every_case_tac>>simp[]
QED

Theorem has_ge_add_eq[simp]:
  has_ge X n (add_eq Y m ec) ⇔
  has_ge X n ec
Proof
  rw[has_ge_def,add_eq_def]>>every_case_tac>>simp[]
QED

Theorem has_eq_add_eq[simp]:
  has_eq X n (add_eq Y m ec) ⇔
  X = Y ∧ n = m ∨
  has_eq X n ec
Proof
  rw[has_eq_def,add_eq_def]>>every_case_tac>>simp[]
QED

Theorem has_eq_add_ge[simp]:
  has_eq X n (add_ge Y m ec) ⇔
  has_eq X n ec
Proof
  rw[has_eq_def,add_ge_def]>>every_case_tac>>simp[]
QED

(**
WEI-LIN:
cencode has this format
(app_list of "concrete" ILP constraints, enc_conf)
 **)

(* TODO: what annotation should we use? *)
(**
WEI-LIN:
the provisional optional annotation currently is NONE
 **)
Definition cencode_ge_def:
  cencode_ge bnd Y n ec =
  if has_ge Y n ec
  then (Nil, ec)
  else
    let ec = add_ge Y n ec in
    (List (MAP (\x. (NONE,x)) (encode_ge bnd Y n)), ec)
End

(***
  NotEquals
***)

Definition cencode_not_equals_def:
  cencode_not_equals bnd X Y pref ec =
  let (f,ec) = next_fresh ec in
  (
    List
    [
      (SOME (pref ^ strlit "_le"),
        bits_imply bnd [Pos (INR f)]
          (mk_constraint_ge 1 X (-1) Y 1));
      (SOME (pref ^ strlit "_ge"),
        (bits_imply bnd [Neg (INR f)]
          (mk_constraint_ge 1 Y (-1) X 1)):ciconstraint)
    ],
    ec
  )
End

Theorem cencode_not_equals_sem:
  valid_assignment bnd wi ∧
  cencode_not_equals bnd X Y pref ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_not_equals bnd X Y) ec ec'
Proof
  rw[cencode_not_equals_def,encode_not_equals_def]>>
  gvs[UNCURRY_EQ,next_fresh_def]>>
  qexists_tac`[(ec.fresh, Ne X Y)]`>>
  rw[enc_rel_def,agree_on_fl_def,reify_flag_def]>>
  rename1`_ ⇔ b`>>Cases_on`b`>>
  intLib.ARITH_TAC
QED

(***
  AllDifferent
***)

Definition cencode_different_row_def:
  (cencode_different_row bnd X [] pref ec = (Nil,ec)) ∧
  (cencode_different_row bnd X (Y::Ys) pref ec =
    let
      (f,ec') = cencode_not_equals bnd X Y pref ec;
      (fs,ec'') = cencode_different_row bnd X Ys pref ec'
    in
      (Append f fs,ec''))
End

Theorem cencode_different_row_sem:
  ∀Ys ec es ec'.
  valid_assignment bnd wi ∧
  cencode_different_row bnd X Ys pref ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_different_row bnd X Ys) ec ec'
Proof
  Induct
  >- (
    rw[cencode_different_row_def,encode_different_row_def]>>
    metis_tac[enc_rel_Nil])>>
  rw[cencode_different_row_def,encode_different_row_def]>>
  gvs[UNCURRY_EQ]>>
  drule_all cencode_not_equals_sem>>
  first_x_assum drule>>rw[]>>
  metis_tac[enc_rel_Append]
QED

Definition cencode_all_different_def:
  (cencode_all_different bnd [] pref ec = (Nil,ec)) ∧
  (cencode_all_different bnd (A::As) pref ec =
    let
      (f,ec') = cencode_different_row bnd A As pref ec;
      (fs,ec'') = cencode_all_different bnd As pref ec'
    in
      (Append f fs,ec''))
End

Theorem cencode_all_different_sem:
  ∀As ec es.
  valid_assignment bnd wi ∧
  cencode_all_different bnd As pref ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_all_different bnd As) ec ec'
Proof
  Induct_on ‘As’>>
  rw[encode_all_different_alt,cencode_all_different_def]
  >- metis_tac[enc_rel_Nil]>>
  gvs[UNCURRY_EQ]>>
  drule_all cencode_different_row_sem>>
  first_x_assum drule_all>>
  rw[]>>
  metis_tac[enc_rel_Append]
QED

(***
  Abs
***)

Definition cencode_abs_var_def:
  cencode_abs_var bnd X Y pref ec =
  let (es,ec) = cencode_ge bnd Y 0 ec in
  (Append es
  (List (MAP (\x. (NONE,x)) (encode_abs_var_body bnd X Y))), ec)
End

Theorem cencode_abs_var_sem:
  valid_assignment bnd wi ∧
  cencode_abs_var bnd X Y pref ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_abs_var bnd X Y) ec ec'
Proof
  rw[encode_abs_var_def,cencode_abs_var_def,cencode_ge_def]>>
  qexists_tac`[]`>>
  gvs[UNCURRY_EQ,AllCaseEqs()]>>
  rw[enc_rel_def,agree_on_fl_def,EVERY_MAP]>>
  fs[good_reif_def]>>
  simp[encode_abs_var_body_def]>>
  metis_tac[]
QED

Definition cencode_abs_def:
  cencode_abs bnd X Y pref ec =
  case Y of
    INL vY => cencode_abs_var bnd X vY pref ec
  | INR cY => (List (MAP (\x. (NONE,x)) (encode_abs_const X cY)), ec)
End

Theorem cencode_abs_sem:
  valid_assignment bnd wi ∧
  cencode_abs bnd X Y pref ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_abs bnd X Y) ec ec'
Proof
  rw[cencode_abs_def,encode_abs_def]>>
  gvs[AllCaseEqs()]
  >- metis_tac[cencode_abs_var_sem]>>
  qexists_tac`[]`>>
  simp[enc_rel_def,agree_on_fl_def,EVERY_MAP,encode_abs_const_sem]
QED

Definition cencode_cp_one_def:
  cencode_cp_one bnd c n ec =
  case c of
    NotEquals X Y =>
    let pref = strlit "not_equals" ^ toString n in
    cencode_not_equals bnd X Y pref ec
  | AllDifferent As =>
    let pref = strlit "all_different" ^ toString n in
    cencode_all_different bnd As pref ec
  | Abs X Y =>
    let pref = strlit "abs" ^ toString n in
    cencode_abs bnd X Y pref ec
  | _ => ARB
End

Theorem cencode_cp_one_sem:
  valid_assignment bnd wi ∧
  cencode_cp_one bnd c n ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_cp_one bnd c) ec ec'
Proof
  rw[encode_cp_one_def,cencode_cp_one_def]>>
  gvs[AllCaseEqs()]
  >- metis_tac[cencode_not_equals_sem]
  >- metis_tac[cencode_all_different_sem]
  >- cheat
  >- cheat
  >- metis_tac[cencode_abs_sem]
  >>
    cheat
QED

Definition cencode_cp_all_def:
  (cencode_cp_all bnd [] n ec = (Nil,ec)) ∧
  (cencode_cp_all bnd (c::cs) n ec =
   let (es,ec') = cencode_cp_one bnd c n ec in
   let (ess,ec'') = cencode_cp_all bnd cs (n+1) ec' in
   (Append es ess, ec''))
End

Theorem cencode_cp_all_sem:
  ∀cs n ec es ec'.
  valid_assignment bnd wi ∧
  cencode_cp_all bnd cs n ec = (es,ec') ⇒
  ∃fl.
  enc_rel fl wi es (encode_cp_all bnd cs) ec ec'
Proof
  Induct>>
  rw[]>>
  gvs[cencode_cp_all_def,encode_cp_all_def]
  >- metis_tac[enc_rel_Nil]>>
  gvs[UNCURRY_EQ]>>
  drule_all cencode_cp_one_sem>>
  first_x_assum drule_all>>
  rw[]>>
  metis_tac[enc_rel_Append]
QED

Definition init_ec_def:
  init_ec = <| fresh := 1; ge := []; eq := [] |>
End

Theorem cencode_cp_all_thm_1:
  valid_assignment bnd wi ∧
  cencode_cp_all bnd cs n init_ec = (es,ec') ∧
  EVERY (λc. constraint_sem c wi) cs ⇒
  ∃wbf.
  EVERY (λx. iconstraint_sem x (wi,wbf))
    (MAP SND (append es))
Proof
  rw[EVERY_MAP]>>
  drule_all encode_cp_all_sem_1>>
  strip_tac>>
  drule cencode_cp_all_sem>>
  disch_then drule>>
  rw[]>>
  rename1`(wi,wb)`>>
  qexists_tac`λy.
    case y of INL v => wb (INL v)
    | INR v =>
      case ALOOKUP fl v of SOME x => wb (INR x) | _ => F`>>
  fs[enc_rel_def]>>
  pop_assum (fn th => DEP_REWRITE_TAC [GSYM th])>>
  simp[agree_on_fl_def,good_reif_def,init_ec_def,has_ge_def,has_eq_def]
QED

Theorem cencode_cp_all_thm_2:
  valid_assignment bnd wi ∧
  cencode_cp_all bnd cs n init_ec = (es,ec') ∧
  EVERY (λx. iconstraint_sem x (wi,wbf)) (MAP SND (append es)) ⇒
  EVERY (λc. constraint_sem c wi) cs
Proof
  rw[EVERY_MAP]>>
  irule encode_cp_all_sem_2>>
  first_assum (irule_at Any)>>
  drule_all cencode_cp_all_sem>>
  rw[enc_rel_def]>>
  first_x_assum drule>>
  impl_keep_tac >-
    simp[good_reif_def,init_ec_def,has_ge_def,has_eq_def]>>
  strip_tac>>
  first_x_assum drule>>
  metis_tac[]
QED

(* === Examples ===

EVAL ``cencode_cp_one (λX. (-10,10)) (NotEquals (INL x) (INL Y)) 0 init_ec``

*)
