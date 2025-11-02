(*
  Implementation of a concrete CP-to-ILP phase
*)
Theory cp_to_ilpImpl
Libs
  preamble
Ancestors
  ilp cp_to_ilp

(*
  In this file, we will prove encodings from
  string-variabled CP constraints.

  string constraint

  into

  (string option # (string, cvar) iconstraint)

  where cvar is string reif + num

  The string option is an annotation.
*)

Type cvar = ``:(string reif + num)``
Type ciconstraint = ``:(string, cvar) iconstraint``

(* TODO: replace ge/eq with faster representations. *)
Datatype:
  enc_conf =
    <|
       fresh : num (* The next fresh var names for flags *)
     ; ge : (string # num) list
     ; eq : (string # num) list
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

Theorem mods_fl_sing[simp]:
  mods_fl [(f, v)] f (f+1)
Proof
  rw[mods_fl_def]
QED

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
  mods_fl fl ec.fresh ec'.fresh ∧
  ec.fresh ≤ ec'.fresh ∧
  (∀wbf.
    EVERY (λx. iconstraint_sem (SND x) (wi,wbf)) (append es) ⇒
    agree_on_fl fl
      (λx. case x of INL v => wbf (INL v) | INR v => reify_flag wi v) wbf) ∧
  ∀wb wbf.
  agree_on_fl fl wb wbf ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_not_equals bnd X Y) ⇔
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf))
    (append es))
Proof
  rw[cencode_not_equals_def,encode_not_equals_def]>>
  gvs[UNCURRY_EQ,next_fresh_def]>>
  qexists_tac`[(ec.fresh, Ne X Y)]`>>
  rw[agree_on_fl_def,reify_flag_def]>>
  rename1`_ ⇔ b`>>Cases_on`b`>>
  intLib.ARITH_TAC
QED

(***
  AllDifferent
***)

Definition cencode_all_different_def:
  cencode_all_different bnd As pref ec =
  (ARB: (mlstring option # ciconstraint) app_list # enc_conf)
End

Theorem cencode_all_different_sem:
  valid_assignment bnd wi ∧
  cencode_all_different bnd As pref ec = (es,ec') ⇒
  ∃fl.
  mods_fl fl ec.fresh ec'.fresh ∧
  ec.fresh ≤ ec'.fresh ∧
  (∀wbf.
    EVERY (λx. iconstraint_sem (SND x) (wi,wbf)) (append es) ⇒
    agree_on_fl fl
      (λx. case x of INL v => wbf (INL v) | INR v => reify_flag wi v) wbf) ∧
  ∀wb wbf.
  agree_on_fl fl wb wbf ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different bnd As) ⇔
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf))
    (append es))
Proof
  cheat
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
  | _ => ARB
End

Theorem cencode_cp_one_sem:
  valid_assignment bnd wi ∧
  cencode_cp_one bnd c n ec = (es,ec') ⇒
  ∃fl.
  mods_fl fl ec.fresh ec'.fresh ∧
  ec.fresh ≤ ec'.fresh ∧
  (∀wbf.
    EVERY (λx. iconstraint_sem (SND x) (wi,wbf)) (append es) ⇒
    agree_on_fl fl
      (λx. case x of INL v => wbf (INL v) | INR v => reify_flag wi v) wbf) ∧
  ∀wb wbf.
  agree_on_fl fl wb wbf ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_cp_one bnd c) ⇔
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf))
    (append es))
Proof
  rw[encode_cp_one_def,cencode_cp_one_def]>>
  gvs[AllCaseEqs()]
  >- metis_tac[cencode_not_equals_sem]
  >- metis_tac[cencode_all_different_sem]
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

Theorem agree_on_fl_mods_fl_append:
  mods_fl fl1 f1 f1' ∧
  mods_fl fl2 f1' f2 ⇒
  (agree_on_fl (fl1++fl2)
    (wb:string reif + string flag -> bool)
    (wbf:string reif + num -> bool) ⇔
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

Theorem cencode_cp_all_sem:
  ∀cs n ec es ec'.
  valid_assignment bnd wi ∧
  cencode_cp_all bnd cs n ec = (es,ec') ⇒
  ∃fl.
  mods_fl fl ec.fresh ec'.fresh ∧
  ec.fresh ≤ ec'.fresh ∧
  (∀wbf.
    EVERY (λx. iconstraint_sem (SND x) (wi,wbf)) (append es) ⇒
    agree_on_fl fl
      (λx. case x of INL v => wbf (INL v) | INR v => reify_flag wi v) wbf) ∧
  ∀wb wbf.
  agree_on_fl fl wb wbf ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_cp_all bnd cs) ⇔
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf))
    (append es))
Proof
  Induct>>
  rw[cencode_cp_all_def,encode_cp_all_def]
  >- (qexists_tac`[]`>>simp[mods_fl_def,agree_on_fl_def])>>
  gvs[UNCURRY_EQ]>>
  drule_all cencode_cp_one_sem>>rw[]>>
  rename1`mods_fl fl1 ec.fresh ec1.fresh`>>
  first_x_assum drule>>rw[]>>
  rename1`mods_fl fl2 ec1.fresh ec2.fresh`>>
  qexists_tac`fl1 ++ fl2`>>
  CONJ_TAC >- (
    fs[mods_fl_def]>>rw[]>>
    first_x_assum drule>>rw[])>>
  drule_all agree_on_fl_mods_fl_append>>
  rw[]>>
  metis_tac[encode_cp_all_def]
QED

Theorem cencode_cp_all_thm_1:
  valid_assignment bnd wi ∧
  cencode_cp_all bnd cs n ec = (es,ec') ∧
  EVERY (λc. constraint_sem c wi) cs ⇒
  ∃wbf.
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf))
    (append es)
Proof
  rw[]>>
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
  pop_assum (fn th => DEP_REWRITE_TAC [GSYM th])>>
  simp[agree_on_fl_def]
QED

Theorem cencode_cp_all_thm_2:
  valid_assignment bnd wi ∧
  cencode_cp_all bnd cs n ec = (es,ec') ∧
  EVERY (λx. iconstraint_sem (SND x) (wi,wbf)) (append es) ⇒
  EVERY (λc. constraint_sem c wi) cs
Proof
  rw[]>>
  irule encode_cp_all_sem_2>>
  first_assum (irule_at Any)>>
  drule_all cencode_cp_all_sem>>
  rw[]>>
  first_x_assum drule>>
  strip_tac>>
  first_x_assum drule>>
  metis_tac[]
QED

(* === Examples ===

val ec = ``<| fresh:= 1; ge:=[]; eq:=[ ] |>``

EVAL ``cencode_cp_one (λX. (-10,10)) (NotEquals (INL x) (INL Y)) 0 ^(ec)``

*)
