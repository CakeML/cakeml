(*
  Multi-objective semantics for npbc and the pbc to npbc bridge
*)
Theory npbc_mo
Ancestors
  pbc_mo pbc npbc pbc_normalise
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*** Multi-objective semantics ***)

Definition obj_vecs_def:
  obj_vecs (objs:((int # var) list # int) list) w =
    MAP (λob. eval_obj (SOME ob) w) objs
End

Definition obj_img_def:
  obj_img (npbf:npbc set) objs =
    IMAGE (obj_vecs objs) {w | satisfies w npbf}
End

Definition nondom_set_def:
  nondom_set ord (npbf:npbc set) objs =
    min_set (ord_le ord) (obj_img npbf objs)
End

Theorem in_obj_img:
  v ∈ obj_img npbf objs ⇔
  ∃w. satisfies w npbf ∧ obj_vecs objs w = v
Proof
  rw[obj_img_def]>>
  metis_tac[]
QED

Theorem in_nondom_set:
  v ∈ nondom_set ord npbf objs ⇔
  (∃w. satisfies w npbf ∧ obj_vecs objs w = v) ∧
  (∀w. satisfies w npbf ∧ ord_le ord (obj_vecs objs w) v ⇒
    obj_vecs objs w = v)
Proof
  rw[nondom_set_def,min_set_def,in_obj_img]>>
  metis_tac[]
QED

Theorem vec_le_obj_vecs:
  vec_le (obj_vecs objs w) (obj_vecs objs w') ⇔
  EVERY (λob. eval_obj (SOME ob) w ≤ eval_obj (SOME ob) w') objs
Proof
  rw[obj_vecs_def,vec_le_MAP]
QED

(*** Normalising a list of objectives ***)

Definition normalise_objs_def:
  normalise_objs objs = MAP (λob. THE (normalise_obj (SOME ob))) objs
End

Theorem normalise_obj_SOME:
  ∀ob. ∃ob'. normalise_obj (SOME ob) = SOME ob'
Proof
  Cases>>
  rw[normalise_obj_def]>>
  rpt (pairarg_tac>>gvs[])
QED

Theorem eval_obj_THE_normalise_obj:
  ∀ob w.
  eval_obj (SOME (THE (normalise_obj (SOME ob)))) w = eval_obj (SOME ob) w
Proof
  rw[]>>
  qspec_then`ob` strip_assume_tac normalise_obj_SOME>>
  `eval_obj (normalise_obj (SOME ob)) w = eval_obj (SOME ob) w` by
    metis_tac[eval_obj_normalise_obj]>>
  gvs[]
QED

Theorem obj_vecs_normalise_objs:
  npbc_mo$obj_vecs (normalise_objs objs) = pbc_mo$obj_vecs objs
Proof
  rw[FUN_EQ_THM,normalise_objs_def,obj_vecs_def,
    pbc_moTheory.obj_vecs_def,MAP_MAP_o,o_DEF,
    eval_obj_THE_normalise_obj]
QED

Theorem nondom_set_normalise:
  pbc_mo$nondom_set ord (set pbf) objs =
  npbc_mo$nondom_set ord (set (normalise pbf)) (normalise_objs objs)
Proof
  rw[nondom_set_def,pbc_moTheory.nondom_set_def]>>
  AP_TERM_TAC>>
  rw[obj_img_def,pbc_moTheory.obj_img_def,
    obj_vecs_normalise_objs,normalise_thm]
QED

(*** Renaming the variables of a list of objectives ***)

Definition name_to_num_objs_def:
  (name_to_num_objs [] s = ([],s)) ∧
  (name_to_num_objs (ob::obs) s =
    let (ob',s') = name_to_num_obj (SOME ob) s in
    let (obs',s'') = name_to_num_objs obs s' in
      ((case ob' of NONE => obs' | SOME ob'' => ob''::obs'), s''))
End

Theorem map_lin_term_lookup_index_stable:
  (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
  set (MAP (lit_var o SND) xs) ⊆ {i | lookup_index s i ≠ NONE} ⇒
  map_lin_term (THE o lookup_index s) xs =
  map_lin_term (THE o lookup_index t) xs
Proof
  rw[map_lin_term_def]>>
  irule MAP_map_lin_term_cong>>
  rw[]>>
  gvs[SUBSET_DEF]>>
  res_tac>>
  namedCases_on`lookup_index s x` ["","v"]>>gvs[]>>
  qpat_x_assum`∀i n. lookup_index s i = SOME n ⇒ _`
    $ qspecl_then [`x`,`v`] mp_tac>>
  fs[]
QED

Theorem name_to_num_objs_thm:
  ∀objs (s:'a name_to_num_state) objs' t.
    name_to_num_objs objs s = (objs',t) ∧
    name_to_num_state_ok s ⇒
    name_to_num_state_ok t ∧
    objs' = map_objs (THE o lookup_index t) objs ∧
    (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
    objs_vars objs ⊆ {i | lookup_index t i ≠ NONE}
Proof
  Induct>>
  gvs[FORALL_PROD,name_to_num_objs_def,name_to_num_obj_def,map_objs_def]>>
  rpt gen_tac>>strip_tac>>
  rpt (pairarg_tac>>gvs[])>>
  drule name_to_num_lin_term>>
  disch_then (qspec_then`[]` mp_tac)>>
  simp[map_lin_term_def]>>
  strip_tac>>gvs[]>>
  last_x_assum drule_all>>
  strip_tac>>gvs[]>>
  CONJ_TAC >- (
    simp[GSYM map_lin_term_def]>>
    irule map_lin_term_lookup_index_stable>>
    gvs[])>>
  gvs[obj_vars_def]>>
  metis_tac[SUBSET_TRANS,lookup_index_mono]
QED

(* Once every variable of objs is registered, the partial map
  THE o lookup_index agrees with any total extension of it *)
Theorem map_objs_lookup_index_total[local]:
  (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
  objs_vars objs ⊆ {i | lookup_index s i ≠ NONE} ⇒
  map_objs (THE o lookup_index s) objs =
  map_objs (λx. case lookup_index t x of NONE => d | SOME v => v) objs
Proof
  strip_tac>>
  `∀x. x ∈ objs_vars objs ⇒
    THE (lookup_index s x) =
    (case lookup_index t x of NONE => d | SOME v => v)` by (
    rw[]>>
    `lookup_index s x ≠ NONE` by gvs[SUBSET_DEF]>>
    namedCases_on`lookup_index s x` ["","v"]>>gvs[]>>
    first_x_assum drule>>
    simp[])>>
  rw[map_objs_def,MAP_EQ_f,FORALL_PROD]>>
  irule map_lit_cong>>
  simp[o_DEF]>>
  first_x_assum irule>>
  simp[objs_vars_def,MEM_MAP,PULL_EXISTS,obj_vars_def]>>
  rpt (first_x_assum (irule_at Any))>>
  simp[obj_vars_def,MEM_MAP]>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Definition name_to_num_mo_prob_def:
  name_to_num_mo_prob (objs,fml) s =
  let (objs',s') = name_to_num_objs objs s in
  let (fml',s'') = name_to_num_pbf fml s' [] in
    ((objs',fml'),s'')
End

Theorem name_to_num_mo_prob_nondom_set:
  name_to_num_mo_prob (objs,fml) s = ((objs',fml'),t) ∧
  name_to_num_state_ok s ⇒
  pbc_mo$nondom_set ord (set fml) objs =
  pbc_mo$nondom_set ord (set fml') objs'
Proof
  rw[name_to_num_mo_prob_def]>>
  rpt (pairarg_tac>>gvs[])>>
  drule_all name_to_num_objs_thm>>
  strip_tac>>
  drule_then drule name_to_num_pbf_rec>>
  simp[]>>
  impl_tac >- fs[pbf_vars_def]>>
  strip_tac>>gvs[MAP_REVERSE]>>
  rename1`name_to_num_objs objs s = (_,sobj)`>>
  rename1`name_to_num_pbf fml sobj [] = (_,sfin)`>>
  qabbrev_tac`f = λx.
    (case lookup_index sfin x of NONE => sfin.next_num | SOME v => v)`>>
  `map_objs (THE o lookup_index sobj) objs = map_objs f objs` by (
    simp[Abbr`f`]>>
    irule map_objs_lookup_index_total>>
    simp[]>>
    metis_tac[])>>
  `MAP (map_pbc (THE o lookup_index sfin)) fml = MAP (map_pbc f) fml` by (
    rw[MAP_EQ_f]>>
    irule map_pbc_cong>>
    rw[]>>
    gvs[Abbr`f`,SUBSET_DEF,pbf_vars_def,PULL_EXISTS]>>
    first_x_assum drule>>
    disch_then drule>>
    TOP_CASE_TAC>>gvs[])>>
  simp[]>>
  PURE_ONCE_REWRITE_TAC[LIST_TO_SET_MAP]>>
  irule nondom_set_INJ>>
  `objs_vars objs ⊆ {i | lookup_index sfin i ≠ NONE}` by
    metis_tac[SUBSET_TRANS,lookup_index_mono]>>
  qmatch_goalsub_abbrev_tac`INJ f vs`>>
  `∀x. x ∈ vs ⇒ lookup_index sfin x ≠ NONE` by (
    gvs[Abbr`vs`,SUBSET_DEF]>>
    metis_tac[])>>
  `∀x. lookup_index sfin x ≠ NONE ⇒ lookup_index sfin x = SOME (f x)` by (
    rw[Abbr`f`]>>
    TOP_CASE_TAC>>gvs[])>>
  gvs[INJ_DEF]>>
  rw[]>>
  irule lookup_index_inj>>
  qexists_tac`f x`>>
  qexists_tac`sfin`>>
  metis_tac[]
QED

Definition normalise_mo_prob_def:
  normalise_mo_prob (objs,fml) =
    (normalise_objs objs, normalise fml)
End

Theorem full_normalise_mo_nondom:
  name_to_num_mo_prob (objs,fml) s = ((objs1,fml1),t) ∧
  name_to_num_state_ok s ∧
  normalise_mo_prob (objs1,fml1) = (objs2,fml2) ⇒
  pbc_mo$nondom_set ord (set fml) objs =
  npbc_mo$nondom_set ord (set fml2) objs2
Proof
  rw[normalise_mo_prob_def]>>
  drule_all name_to_num_mo_prob_nondom_set>>
  simp[nondom_set_normalise]
QED
