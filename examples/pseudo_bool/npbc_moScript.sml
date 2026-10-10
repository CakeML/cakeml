(*
  Multi-objective semantics for npbc, the pbc to npbc bridge, and the
  recognition of loaded orders that refine an objective ordering
*)
Theory npbc_mo
Ancestors
  pbc_mo pbc npbc pbc_normalise npbc_check
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
  (∀w. satisfies w npbf ⇒ ¬ord_lt ord (obj_vecs objs w) v)
Proof
  rw[nondom_set_def,in_min_set_ord,in_obj_img]>>
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

(*** Recognising loaded orders: the Pareto reference ***)

(* The variables occurring in a list of objectives *)
Definition mo_obj_vars_def:
  mo_obj_vars objs = FLAT (MAP (λ(f,c). MAP SND f) objs)
End

(* Order objective terms by variable *)
Definition var_le_def[simp]:
  var_le ((_:int),u:num) ((_:int),v:num) ⇔ u ≤ v
End

(* Rename the variables of an objective through rn, restoring the order by
  variable that obj_constraint's add_lists (npbcScript.sml) requires *)
Definition rename_obj_def:
  rename_obj rn ((f,c):((int # var) list # int)) =
    (sort var_le
      (MAP (λ(a,v). (a, case sptree$lookup v rn of NONE => v | SOME u => u)) f), c)
End

(* The substitution described by su *)
Definition vs_to_us_def:
  vs_to_us su v =
    case sptree$lookup v su of
      NONE => NONE
    | SOME u => SOME (INR (Pos u))
End

(* One constraint per objective, each saying O(us) ≤ O(vs) *)
Definition pareto_constrs_def:
  pareto_constrs objs xvars us vs =
    let su = list_list_insert vs us in
    let rn = list_list_insert xvars vs in
      MAP (λob. obj_constraint (vs_to_us su) (rename_obj rn ob)) objs
End

(* Some constraint in cs implies c *)
Definition check_imp_any_def:
  check_imp_any c cs =
    EXISTS (λd. imp d c) cs
End

(* Renaming an objective and evaluating agrees with the original *)
Theorem eval_obj_rename_obj:
  (∀v. MEM v (MAP SND (FST ob)) ⇒
     B (case sptree$lookup v rn of NONE => v | SOME u => u) = w v) ⇒
  eval_obj (SOME (rename_obj rn ob)) B = eval_obj (SOME ob) w
Proof
  PairCases_on`ob`>>
  rw[rename_obj_def,eval_obj_def]>>
  `SUM (MAP (eval_term B) (sort var_le
     (MAP (λ(a,v). (a, case sptree$lookup v rn of NONE => v | SOME u => u)) ob0))) =
   SUM (MAP (eval_term B)
     (MAP (λ(a,v). (a, case sptree$lookup v rn of NONE => v | SOME u => u)) ob0))` by (
    irule PERM_SUM>>
    irule PERM_MAP>>
    metis_tac[mllistTheory.sort_PERM,PERM_SYM])>>
  pop_assum SUBST_ALL_TAC>>
  simp[MAP_MAP_o]>>
  AP_TERM_TAC>>
  rw[MAP_EQ_f,FORALL_PROD]>>
  gvs[MEM_MAP,PULL_EXISTS]>>
  first_x_assum drule>>
  simp[]
QED

(* The ambient assignment of the order reads off w1 on us and w2 on vs *)
Theorem assign_ord_EL[local]:
  ∀us vs xs w1 w2 ww j.
  ALL_DISTINCT (us ++ vs) ∧
  LENGTH us = LENGTH xs ∧ LENGTH vs = LENGTH xs ∧
  EVERY SND xs ∧ j < LENGTH xs ⇒
  assign (ALOOKUP
    (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww (EL j us) =
    w1 (EL j (MAP FST xs)) ∧
  assign (ALOOKUP
    (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww (EL j vs) =
    w2 (EL j (MAP FST xs))
Proof
  rpt gen_tac>>strip_tac>>
  gvs[ALL_DISTINCT_APPEND]>>
  `ALOOKUP (ZIP (us,xs)) (EL j us) = SOME (EL j xs)` by
    (irule ALOOKUP_ALL_DISTINCT_EL_IMP>>simp[])>>
  `ALOOKUP (ZIP (us,xs)) (EL j vs) = NONE` by
    (irule IMP_ALOOKUP_NONE>>
    simp[]>>
    metis_tac[MEM_EL])>>
  `ALOOKUP (ZIP (vs,xs)) (EL j vs) = SOME (EL j xs)` by
    (irule ALOOKUP_ALL_DISTINCT_EL_IMP>>simp[])>>
  `SND (EL j xs)` by metis_tac[EVERY_EL]>>
  simp[ALOOKUP_APPEND,assign_def,get_bits_def,EL_MAP]
QED

Theorem ALOOKUP_ZIP_index[local]:
  ∀v xvars ys.
  MEM v xvars ∧ LENGTH xvars = LENGTH ys ⇒
  ∃k. k < LENGTH ys ∧ EL k xvars = v ∧
      ALOOKUP (ZIP (xvars,ys)) v = SOME (EL k ys)
Proof
  rw[]>>
  `ALOOKUP (ZIP (xvars,ys)) v ≠ NONE` by
    simp[ALOOKUP_NONE,MAP_ZIP]>>
  Cases_on`ALOOKUP (ZIP (xvars,ys)) v`>>gvs[]>>
  drule ALOOKUP_MEM>>
  simp[MEM_ZIP]>>
  rw[]>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Theorem MEM_mo_obj_vars:
  MEM ob objs ∧ MEM v (MAP SND (FST ob)) ⇒
  MEM v (mo_obj_vars objs)
Proof
  rw[mo_obj_vars_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
  qexists_tac`ob`>>
  PairCases_on`ob`>>gvs[MEM_MAP]>>
  metis_tac[]
QED


(* Each objective variable is read off the us side as w1 and the vs side as w2 *)
Theorem ord_lookup_vals[local]:
  ∀vs us xs A w1 w2 v.
  ALL_DISTINCT vs ⇒
  LENGTH us = LENGTH vs ⇒
  LENGTH vs = LENGTH xs ⇒
  (∀j. j < LENGTH xs ⇒
     A (EL j us) = w1 (EL j (MAP FST xs)) ∧
     A (EL j vs) = w2 (EL j (MAP FST xs))) ⇒
  MEM v (MAP FST xs) ⇒
  A (case sptree$lookup v (list_list_insert (MAP FST xs) vs) of
       NONE => v | SOME u => u) = w2 v ∧
  assign (vs_to_us (list_list_insert vs us)) A
    (case sptree$lookup v (list_list_insert (MAP FST xs) vs) of
       NONE => v | SOME u => u) = w1 v
Proof
  rpt gen_tac>>rpt strip_tac>>
  rewrite_tac[lookup_list_list_insert]>>
  `∃k. k < LENGTH vs ∧ EL k (MAP FST xs) = v ∧
     ALOOKUP (ZIP (MAP FST xs,vs)) v = SOME (EL k vs)` by
    metis_tac[ALOOKUP_ZIP_index,LENGTH_MAP]>>
  gvs[]>>
  `ALOOKUP (ZIP (vs,us)) (EL k vs) = SOME (EL k us)` by
    (irule ALOOKUP_ALL_DISTINCT_EL_IMP>>simp[])>>
  first_x_assum drule>>
  simp[vs_to_us_def,assign_def,lookup_list_list_insert]
QED

(* Each objective variable is read off the side ys as w, when ys and the
  order variables line up *)
Theorem rename_lookup_val:
  LENGTH ys = LENGTH xs ∧
  (∀j. j < LENGTH xs ⇒ A (EL j ys) = w (EL j (MAP FST xs))) ∧
  MEM v (MAP FST xs) ⇒
  A (case sptree$lookup v (list_list_insert (MAP FST xs) ys) of
       NONE => v | SOME u => u) = w v
Proof
  rw[lookup_list_list_insert]>>
  `∃k. k < LENGTH ys ∧ EL k (MAP FST xs) = v ∧
     ALOOKUP (ZIP (MAP FST xs,ys)) v = SOME (EL k ys)` by
    metis_tac[ALOOKUP_ZIP_index,LENGTH_MAP]>>
  gvs[]
QED

(* An accepted pair of assignments yields one assignment of the order
  variables that satisfies f and g, reading w1 on us and w2 on vs *)
Theorem po_of_aspo_assign:
  good_aspo ((f,g,us,vs,as),xs) ∧ EVERY SND xs ∧
  po_of_aspo ((f,g,us,vs,as),xs) w1 w2 ⇒
  ∃A. npbc$satisfies A (set f) ∧ npbc$satisfies A (set g) ∧
    ∀j. j < LENGTH xs ⇒
      A (EL j us) = w1 (EL j (MAP FST xs)) ∧
      A (EL j vs) = w2 (EL j (MAP FST xs))
Proof
  rw[po_of_aspo_def,the_spec_def,good_aspo_def,good_aord_def]>>
  qmatch_asmsub_abbrev_tac`assign al (assign ss ww)`>>
  qexists_tac`assign al (assign ss ww)`>>
  simp[]>>
  rpt gen_tac>>strip_tac>>
  `MEM (EL j us) us ∧ MEM (EL j vs) vs` by simp[EL_MEM]>>
  `al (EL j us) = NONE ∧ al (EL j vs) = NONE` by (
    gvs[Abbr`al`,ALL_DISTINCT_APPEND]>>
    conj_tac>>
    irule IMP_ALOOKUP_NONE>>
    metis_tac[LENGTH_MAP])>>
  `∀x. al x = NONE ⇒ assign al (assign ss ww) x = assign ss ww x` by
    simp[Once assign_def]>>
  simp[]>>
  qspecl_then [`us`,`vs`,`xs`,`w1`,`w2`,`ww`,`j`] mp_tac assign_ord_EL>>
  gvs[Abbr`ss`,ALL_DISTINCT_APPEND]
QED

(* The Pareto reference constraints, under an assignment reading w1 on us
  and w2 on vs, give componentwise dominance *)
Theorem pareto_core_sound:
  npbc$satisfies A
    (set (pareto_constrs objs (MAP FST (xs:(num # bool) list)) us vs)) ∧
  ALL_DISTINCT vs ∧ LENGTH us = LENGTH xs ∧ LENGTH vs = LENGTH xs ∧
  EVERY (λv. MEM v (MAP FST xs)) (mo_obj_vars objs) ∧
  (∀j. j < LENGTH xs ⇒
     A (EL j us) = w1 (EL j (MAP FST xs)) ∧
     A (EL j vs) = w2 (EL j (MAP FST xs))) ⇒
  vec_le (obj_vecs objs w1) (obj_vecs objs w2)
Proof
  rw[vec_le_obj_vecs,EVERY_MEM]>>
  `satisfies_npbc A (obj_constraint (vs_to_us (list_list_insert vs us))
     (rename_obj (list_list_insert (MAP FST xs) vs) ob))` by
    gvs[npbcTheory.satisfies_def,pareto_constrs_def,MEM_MAP,PULL_EXISTS]>>
  pop_assum mp_tac>>
  rewrite_tac[satisfies_npbc_obj_constraint]>>
  strip_tac>>
  `∀u. MEM u (MAP SND (FST ob)) ⇒ MEM u (MAP FST xs)` by
    metis_tac[MEM_mo_obj_vars]>>
  `LENGTH us = LENGTH vs` by simp[]>>
  `eval_obj (SOME (rename_obj (list_list_insert (MAP FST xs) vs) ob)) A =
     eval_obj (SOME ob) w2 ∧
   eval_obj (SOME (rename_obj (list_list_insert (MAP FST xs) vs) ob))
     (assign (vs_to_us (list_list_insert vs us)) A) = eval_obj (SOME ob) w1` by (
    conj_tac>>
    irule eval_obj_rename_obj>>
    rw[]>>
    first_x_assum drule>>
    strip_tac>>
    drule_all ord_lookup_vals>>
    simp[])>>
  qpat_x_assum`eval_obj _ (assign _ _) ≤ _` mp_tac>>
  asm_rewrite_tac[]
QED

(* An objective depends only on its own variables *)
Theorem eval_obj_vars_cong:
  (∀v. MEM v (MAP SND (FST ob)) ⇒ (w1 v ⇔ w2 v)) ⇒
  eval_obj (SOME ob) w1 = eval_obj (SOME ob) w2
Proof
  Cases_on`ob`>>
  rw[eval_obj_def]>>
  AP_TERM_TAC>>
  irule MAP_CONG>>
  rw[]>>
  rename1`MEM cv _`>>
  PairCases_on`cv`>>
  gvs[eval_lit_def]>>
  `w1 cv1 ⇔ w2 cv1` by (
    first_x_assum irule>>
    simp[MEM_MAP]>>
    qexists_tac`(cv0,cv1)`>>
    simp[])>>
  simp[]
QED

(*** Recognising loaded orders: references with auxiliaries ***)

(*
  The reference encoding of Leximax is a list of surface constraints over the
  order variables us (left), vs (right) and the auxiliaries as, which are
  identified by their position in as. With p objectives and the threshold
  values V = v_0 < ... < v_(m-1), the positions are, in order:
    left thresholds o[i,k] (i < p outer, k < m inner), left sorted columns
    l[j,k], right thresholds, right sorted columns, the comparison variables
    s[0], g[0], ..., s[p-1], g[p-1], and the output r.
  o[i,k] holds iff objective i is at least v_k; column k of l is column k
  of o sorted with its true entries first, so row j of l counts the values
  v_k at most the j-th largest objective value. s[t] and g[t] compare row t
  of the two sides, and r, which the order requires, holds only if the rows
  compare lexicographically.
  The pieces (thresholds, sorting, lexicographic or componentwise comparison
  of rows) are stated for any rows, so that other orderings can be assembled
  from them.
*)

(* An npbc term list as a surface linear term *)
Definition npbc_lin_def:
  npbc_lin (xs:(int # num) list) : num lin_term =
    MAP (λ(c,v). if c < 0 then (-c,Neg v) else (c,Pos v)) xs
End

(* A sum of variables, each with coefficient c *)
Definition var_sum_def:
  var_sum (c:int) (xs:num list) : num lin_term = MAP (λx. (c,Pos x)) xs
End

(* ov i k holds iff objective i is at least the k-th value *)
Definition thr_core_def:
  thr_core (objs:((int # num) list # int) list) rn
    (ov:num -> num -> num) (vals:int list) : num pbc list =
    FLAT (MAPi (λi ob.
      MAPi (λk v.
        (Iff (Pos (ov i k)) GreaterEqual,
          npbc_lin (FST (rename_obj rn ob)), v - SND ob)) vals) objs)
End

(* Column k of lv holds as many true entries as column k of ov, true
  entries first *)
Definition sort_core_def:
  sort_core p m (ov:num -> num -> num) (lv:num -> num -> num)
    : num pbc list =
    FLAT (GENLIST (λk.
      (PEq,
        var_sum 1 (GENLIST (λi. ov i k) p) ++
        var_sum (-1) (GENLIST (λj. lv j k) p), 0) ::
      FLAT (GENLIST (λj.
        if j + 1 < p then
          [(Fwd [Pos (lv (j + 1) k)] (RIneq GreaterEqual),
            var_sum 1 [lv j k], 1)]
        else []) p)) m)
End

(* The output r requires each left row to be lexicographically at most the
  matching right row, counting the true variables of a row *)
Definition lex_cmp_core_def:
  lex_cmp_core (lrows:num list list) rrows (s:num -> num) (g:num -> num)
    (r:num) : num pbc list =
    (PGe, var_sum 1 [r], 1) ::
    FLAT (MAPi (λt lrow.
      [(Fwd [Pos (s t)] (RIneq GreaterEqual),
         var_sum 1 (any_el t rrows []) ++ var_sum (-1) lrow, 0);
       (Bwd (Pos (g t)) GreaterEqual,
         var_sum 1 lrow ++ var_sum (-1) (any_el t rrows []), 0);
       (Fwd [Pos r] (RIneq GreaterEqual),
         (1,Pos (s t)) ::
           FLAT (GENLIST (λu. [(1,Neg (s u)); (1,Neg (g u))]) t), 1)])
      lrows)
End

(* The output r requires each left row to count at most the matching right
  row *)
Definition vec_cmp_core_def:
  vec_cmp_core (lrows:num list list) rrows (s:num -> num) (r:num)
    : num pbc list =
    (PGe, var_sum 1 [r], 1) ::
    FLAT (MAPi (λt lrow.
      [(Fwd [Pos (s t)] (RIneq GreaterEqual),
         var_sum 1 (any_el t rrows []) ++ var_sum (-1) lrow, 0);
       (Fwd [Pos r] (RIneq GreaterEqual), var_sum 1 [s t], 1)])
      lrows)
End

(* The number of auxiliaries of the Leximax reference *)
Definition leximax_aux_len_def:
  leximax_aux_len p m = 4 * p * m + 2 * p + 1
End

(* The Leximax reference, in the layout described above. Every position read
  is below leximax_aux_len p m, and ref_core uses this only when as has
  exactly that many entries *)
Definition leximax_constrs_def:
  leximax_constrs objs xvars us vs (as:num list) vals : num pbc list =
  let p = LENGTH objs in
  let m = LENGTH vals in
  let ax = (λn. any_el n as 0) in
  let lo = (λi k. ax (i * m + k)) in
  let ll = (λj k. ax (p * m + j * m + k)) in
  let ro = (λi k. ax (2 * p * m + i * m + k)) in
  let rl = (λj k. ax (3 * p * m + j * m + k)) in
  let c = 4 * p * m in
    thr_core objs (list_list_insert xvars us) lo vals ++ sort_core p m lo ll ++
    thr_core objs (list_list_insert xvars vs) ro vals ++ sort_core p m ro rl ++
    lex_cmp_core
      (MAP (λj. GENLIST (ll j) m) (GENLIST I p))
      (MAP (λj. GENLIST (rl j) m) (GENLIST I p))
      (λt. ax (c + 2 * t)) (λt. ax (c + 2 * t + 1)) (ax (c + 2 * p))
End

(* The sums of |c| over the subsets of the terms *)
Definition subset_sums_def:
  (subset_sums [] = insert 0 () LN) ∧
  (subset_sums ((c:int,v:num)::xs) =
    let s = subset_sums xs in
      union s (fromAList (MAP (λ(n,u). (n + Num (ABS c),u)) (toAList s))))
End

Definition dedup_sorted_def:
  (dedup_sorted (x::y::xs) =
    if x = y then dedup_sorted (y::xs) else x :: dedup_sorted (y::xs)) ∧
  (dedup_sorted xs = xs)
End

(* The values each objective can take, ascending and without duplicates *)
Definition mo_vals_def:
  mo_vals (objs:((int # num) list # int) list) =
    dedup_sorted (mllist$sort (λx y. x ≤ y)
      (FLAT (MAP (λ(f,c). MAP (λ(n,u). &n + c) (toAList (subset_sums f)))
        objs)))
End

(* The reference for an ordering. For Leximax the threshold values are
  chosen by the number of auxiliaries: all values of the objectives, or all
  but the least *)
Definition ref_core_def:
  ref_core ord objs xvars us vs as =
  case ord of
    Pareto =>
      if NULL as then SOME (pareto_constrs objs xvars us vs) else NONE
  | Leximax =>
      let p = LENGTH objs in
      let vf = mo_vals objs in
      let V =
        if LENGTH as = leximax_aux_len p (LENGTH vf) then vf else DROP 1 vf in
      if LENGTH as = leximax_aux_len p (LENGTH V) then
        SOME (normalise (leximax_constrs objs xvars us vs as V))
      else NONE
End

(* A loaded order is accepted for an ordering when its variables cover the
  objectives and each reference constraint follows from one of its
  constraints *)
Definition ref_ord_ok_def:
  ref_ord_ok ord objs (((f,g,us,vs,as),asv):aord_s) xs ⇔
    EVERY SND xs ∧
    (let xsv = list_to_num_set (MAP FST xs) in
      EVERY (λv. sptree$lookup v xsv ≠ NONE) (mo_obj_vars objs)) ∧
    case ref_core ord objs (MAP FST xs) us vs as of
      NONE => F
    | SOME cs => let fg = f ++ g in EVERY (λc. check_imp_any c fg) cs
End

(*** Soundness of the reference encodings ***)

(* The number of values in V that are at most x *)
Definition val_rank_def:
  val_rank (V:int list) x = LENGTH (FILTER (λv. v ≤ x) V)
End

(* V contains every value of an objective that exceeds another value of
  some objective *)
Definition vals_ok_def:
  vals_ok (objs:((int # num) list # int) list) V ⇔
  ∀ob ob' w w'.
    MEM ob objs ∧ MEM ob' objs ∧
    eval_obj (SOME ob) w < eval_obj (SOME ob') w' ⇒
    MEM (eval_obj (SOME ob') w') V
End

Theorem eval_lin_term_npbc_lin:
  eval_lin_term w (npbc_lin xs) = &SUM (MAP (npbc$eval_term w) xs)
Proof
  Induct_on`xs`>>
  fs[npbc_lin_def,eval_lin_term_def,iSUM_def]>>
  rpt gen_tac>>
  PairCases_on`h`>>
  rw[]>>
  `&Num (ABS h0) = ABS h0` by simp[integerTheory.INT_OF_NUM]>>
  Cases_on`w h1`>>
  gvs[integerTheory.INT_ABS]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_var_sum:
  eval_lin_term w (var_sum c xs) = c * &LENGTH (FILTER w xs)
Proof
  Induct_on`xs`>>
  fs[var_sum_def,eval_lin_term_def,iSUM_def]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem thr_core_sat:
  pbc$satisfies A (set (thr_core objs rn ov V)) ∧
  LENGTH a = LENGTH objs ∧
  (∀i. i < LENGTH objs ⇒
    eval_lin_term A (npbc_lin (FST (rename_obj rn (EL i objs)))) +
      SND (EL i objs) = EL i a) ⇒
  ∀i k. i < LENGTH objs ∧ k < LENGTH V ⇒ (A (ov i k) ⇔ EL k V ≤ EL i a)
Proof
  rw[pbcTheory.satisfies_def]>>
  first_x_assum (qspec_then `(Iff (Pos (ov i k)) GreaterEqual,
    npbc_lin (FST (rename_obj rn (EL i objs))), EL k V - SND (EL i objs))`
    mp_tac)>>
  impl_tac >- (
    simp[thr_core_def,MEM_FLAT,indexedListsTheory.MEM_MAPi,PULL_EXISTS]>>
    metis_tac[])>>
  first_x_assum drule>>
  rw[satisfies_pbc_def]>>
  intLib.ARITH_TAC
QED

(* A down-closed predicate that holds at p holds below p *)
Theorem down_closed_le[local]:
  ∀d. (∀j. j < p ∧ c (j + 1) ⇒ c j) ∧ c p ∧ d ≤ p ⇒ c (p - d)
Proof
  Induct
  >- simp[]>>
  rw[]>>
  `d ≤ p ∧ p - SUC d < p ∧ p - SUC d + 1 = p - d` by decide_tac>>
  `c (p - d)` by metis_tac[]>>
  qpat_x_assum `∀j. _` (qspec_then `p - SUC d` mp_tac)>>
  simp[]
QED

(* A down-closed predicate on 0..p-1 holds exactly below its count *)
Theorem down_closed_count:
  ∀c p. (∀j. j + 1 < p ∧ c (j + 1) ⇒ c j) ⇒
  ∀j. j < p ⇒ (c j ⇔ j < LENGTH (FILTER c (GENLIST I p)))
Proof
  gen_tac>>
  Induct>>
  rw[GENLIST,FILTER_SNOC]
  >- (
    `∀j. j < p ∧ c (j + 1) ⇒ c j` by (
      rw[]>>
      first_x_assum irule>>
      simp[])>>
    `∀i. i ≤ p ⇒ c i` by (
      rw[]>>
      `p - (p - i) = i ∧ p - i ≤ p` by decide_tac>>
      metis_tac[down_closed_le])>>
    `FILTER c (GENLIST I p) = GENLIST I p` by
      simp[FILTER_EQ_ID,EVERY_GENLIST]>>
    simp[])>>
  qpat_x_assum `(∀j. _) ⇒ _` mp_tac>>
  impl_tac >- (
    rw[]>>
    first_x_assum irule>>
    simp[])>>
  strip_tac>>
  Cases_on`j < p`
  >- simp[]>>
  `j = p` by simp[]>>
  `LENGTH (FILTER c (GENLIST I p)) ≤ p` by
    metis_tac[LENGTH_FILTER_LEQ,LENGTH_GENLIST]>>
  gvs[]
QED

(* Counting the entries of two generated lists that satisfy predicates
  agreeing position by position *)
Theorem LENGTH_FILTER_GENLIST_cong:
  ∀n. (∀i. i < n ⇒ (P (f i) ⇔ Q (g i))) ⇒
  LENGTH (FILTER P (GENLIST f n)) = LENGTH (FILTER Q (GENLIST g n))
Proof
  Induct>>
  rw[GENLIST,FILTER_SNOC]>>
  gvs[]
QED

(* Counting a list's entries by their positions *)
Theorem LENGTH_FILTER_EL:
  ∀l. LENGTH (FILTER P l) =
    LENGTH (FILTER (λi. P (EL i l)) (GENLIST I (LENGTH l)))
Proof
  Induct>>
  rw[GENLIST_CONS]>>
  irule LENGTH_FILTER_GENLIST_cong>>
  simp[]
QED

Theorem count_ge_GENLIST:
  count_ge t a = LENGTH (FILTER (λi. t ≤ EL i a) (GENLIST I (LENGTH a)))
Proof
  simp[count_ge_def,Once LENGTH_FILTER_EL]
QED

(* Each sorted column has its true entries first *)
Theorem sort_core_chain:
  pbc$satisfies A (set (sort_core p m ov lv)) ∧
  j + 1 < p ∧ k < m ∧ A (lv (j + 1) k) ⇒ A (lv j k)
Proof
  rw[pbcTheory.satisfies_def]>>
  first_x_assum (qspec_then `(Fwd [Pos (lv (j + 1) k)] (RIneq GreaterEqual),
    var_sum 1 [lv j k], 1)` mp_tac)>>
  impl_tac >- (
    simp[sort_core_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]>>
    qexistsl_tac[`k`,`j`]>>
    simp[])>>
  simp[satisfies_pbc_def,eval_lin_term_var_sum]>>
  Cases_on`A (lv j k)`>>simp[]
QED

Theorem sort_core_sat:
  pbc$satisfies A (set (sort_core (LENGTH a) (LENGTH V) ov lv)) ∧
  (∀i k. i < LENGTH a ∧ k < LENGTH V ⇒ (A (ov i k) ⇔ EL k V ≤ EL i a)) ⇒
  ∀j k. j < LENGTH a ∧ k < LENGTH V ⇒
    (A (lv j k) ⇔ EL k V ≤ EL j (sort_desc a))
Proof
  rpt strip_tac>>
  `∀j. j + 1 < LENGTH a ∧ A (lv (j + 1) k) ⇒ A (lv j k)` by
    metis_tac[sort_core_chain]>>
  fs[pbcTheory.satisfies_def]>>
  `LENGTH (FILTER A (GENLIST (λi. ov i k) (LENGTH a))) =
   LENGTH (FILTER A (GENLIST (λj. lv j k) (LENGTH a)))` by (
    first_x_assum (qspec_then `(PEq,
      var_sum 1 (GENLIST (λi. ov i k) (LENGTH a)) ++
      var_sum (-1) (GENLIST (λj. lv j k) (LENGTH a)), 0)` mp_tac)>>
    impl_tac >- (
      simp[sort_core_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]>>
      metis_tac[])>>
    simp[satisfies_pbc_def,eval_lin_term_var_sum]>>
    intLib.ARITH_TAC)>>
  `LENGTH (FILTER A (GENLIST (λi. ov i k) (LENGTH a))) =
   count_ge (EL k V) a` by (
    rewrite_tac[count_ge_GENLIST]>>
    irule LENGTH_FILTER_GENLIST_cong>>
    simp[])>>
  `LENGTH (FILTER (λj. A (lv j k)) (GENLIST I (LENGTH a))) =
   LENGTH (FILTER A (GENLIST (λj. lv j k) (LENGTH a)))` by (
    irule LENGTH_FILTER_GENLIST_cong>>
    simp[])>>
  qspecl_then [`λj. A (lv j k)`,`LENGTH a`] mp_tac down_closed_count>>
  simp[]>>
  disch_then (qspec_then `j` mp_tac)>>
  simp[EL_sort_desc]
QED

Theorem val_rank_GENLIST:
  val_rank V x = LENGTH (FILTER (λk. EL k V ≤ x) (GENLIST I (LENGTH V)))
Proof
  simp[val_rank_def,Once LENGTH_FILTER_EL]
QED

Theorem count_row:
  (∀k. k < LENGTH V ⇒ (A (f k) ⇔ EL k V ≤ x)) ⇒
  LENGTH (FILTER A (GENLIST f (LENGTH V))) = val_rank V x
Proof
  rw[val_rank_GENLIST]>>
  irule LENGTH_FILTER_GENLIST_cong>>
  simp[]
QED

(* Position by position: a comparison sl t requires the left value to be
  at most the right one, an equality at t makes gl t hold, and position t
  is compared unless an earlier position already decided *)
Theorem lex_le_positions:
  ∀ls rs sl gl.
    LENGTH ls = LENGTH rs ∧
    (∀t. t < LENGTH ls ⇒
      (sl t ⇒ EL t ls ≤ EL t rs) ∧ (EL t rs ≤ EL t ls ⇒ gl t) ∧
      (sl t ∨ ∃u. u < t ∧ (¬sl u ∨ ¬gl u))) ⇒
    lex_le ls rs
Proof
  Induct
  >- simp[lex_le_def]>>
  rpt gen_tac>>
  Cases_on`rs`
  >- simp[]>>
  qmatch_goalsub_rename_tac`lex_le (x::xs) (y::ys)`>>
  rw[lex_le_def]>>
  first_assum (qspec_then`0` mp_tac)>>
  simp_tac (srw_ss()) []>>
  strip_tac>>
  `x ≤ y` by metis_tac[]>>
  Cases_on`x < y`>>simp[]>>
  `x = y` by intLib.ARITH_TAC>>
  gvs[]>>
  `gl 0` by (
    first_assum (qspec_then`0` mp_tac)>>
    simp_tac (srw_ss()) [])>>
  last_x_assum irule>>
  rewrite_tac[]>>
  qexistsl_tac[`λt. gl (t + 1)`,`λt. sl (t + 1)`]>>
  rpt gen_tac>>strip_tac>>
  first_x_assum (qspec_then`SUC t` mp_tac)>>
  simp[GSYM ADD1]>>
  strip_tac>>
  simp[]>>
  disj2_tac>>
  namedCases_on`u` ["","n"]>>
  gvs[]>>
  qexists_tac`n`>>
  simp[]
QED

(* The guards of the comparisons before t contribute nothing when every
  earlier comparison holds with equality *)
Theorem eval_lin_term_prefix_guards:
  (∀u. u < t ⇒ A (s u) ∧ A (g u)) ⇒
  eval_lin_term A (FLAT (GENLIST (λu. [(1,Neg (s u)); (1,Neg (g u))]) t)) = 0
Proof
  Induct_on`t`>>
  rw[GENLIST,FLAT_SNOC]
QED

Theorem lex_cmp_core_sat:
  pbc$satisfies A (set (lex_cmp_core lrows rrows s g r)) ∧
  LENGTH lrows = LENGTH rrows ⇒
  lex_le (MAP (λrow. &LENGTH (FILTER A row)) lrows)
    (MAP (λrow. &LENGTH (FILTER A row)) rrows)
Proof
  rw[pbcTheory.satisfies_def]>>
  `satisfies_pbc A (PGe, var_sum 1 [r], 1)` by (
    first_assum irule>>
    simp[lex_cmp_core_def])>>
  `A r` by (
    gvs[satisfies_pbc_def,eval_lin_term_var_sum]>>
    Cases_on`A r`>>gvs[])>>
  irule lex_le_positions>>
  simp[]>>
  qexistsl_tac[`λt. A (g t)`,`λt. A (s t)`]>>
  rpt gen_tac>>strip_tac>>
  simp[EL_MAP]>>
  `satisfies_pbc A (Fwd [Pos (s t)] (RIneq GreaterEqual),
     var_sum 1 (EL t rrows) ++ var_sum (-1) (EL t lrows), 0) ∧
   satisfies_pbc A (Bwd (Pos (g t)) GreaterEqual,
     var_sum 1 (EL t lrows) ++ var_sum (-1) (EL t rrows), 0) ∧
   satisfies_pbc A (Fwd [Pos r] (RIneq GreaterEqual),
     (1,Pos (s t)) ::
       FLAT (GENLIST (λu. [(1,Neg (s u)); (1,Neg (g u))]) t), 1)` by (
    rpt conj_tac>>
    first_assum irule>>
    simp[lex_cmp_core_def,MEM_FLAT,indexedListsTheory.MEM_MAPi,PULL_EXISTS]>>
    qexists_tac`t`>>
    simp[any_el_ALT])>>
  gvs[satisfies_pbc_def,eval_lin_term_var_sum]>>
  rpt conj_tac
  >- (
    strip_tac>>
    gvs[]>>
    intLib.ARITH_TAC)
  >- (
    strip_tac>>
    first_x_assum irule>>
    intLib.ARITH_TAC)>>
  spose_not_then strip_assume_tac>>
  gvs[]>>
  `eval_lin_term A
     (FLAT (GENLIST (λu. [(1,Neg (s u)); (1,Neg (g u))]) t)) = 0` by (
    irule eval_lin_term_prefix_guards>>
    metis_tac[])>>
  gvs[]
QED

Theorem vec_cmp_core_sat:
  pbc$satisfies A (set (vec_cmp_core lrows rrows s r)) ∧
  LENGTH lrows = LENGTH rrows ⇒
  vec_le (MAP (λrow. &LENGTH (FILTER A row)) lrows)
    (MAP (λrow. &LENGTH (FILTER A row)) rrows)
Proof
  rw[pbcTheory.satisfies_def]>>
  `satisfies_pbc A (PGe, var_sum 1 [r], 1)` by (
    first_assum irule>>
    simp[vec_cmp_core_def])>>
  `A r` by (
    gvs[satisfies_pbc_def,eval_lin_term_var_sum]>>
    Cases_on`A r`>>gvs[])>>
  simp[vec_le_def,LIST_REL_EL_EQN,EL_MAP]>>
  rw[]>>
  `satisfies_pbc A (Fwd [Pos (s n)] (RIneq GreaterEqual),
     var_sum 1 (EL n rrows) ++ var_sum (-1) (EL n lrows), 0) ∧
   satisfies_pbc A (Fwd [Pos r] (RIneq GreaterEqual), var_sum 1 [s n], 1)` by (
    rpt conj_tac>>
    first_assum irule>>
    simp[vec_cmp_core_def,MEM_FLAT,indexedListsTheory.MEM_MAPi,PULL_EXISTS]>>
    qexists_tac`n`>>
    simp[any_el_ALT])>>
  gvs[satisfies_pbc_def,eval_lin_term_var_sum]>>
  Cases_on`A (s n)`>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem val_rank_mono:
  x ≤ y ⇒ val_rank V x ≤ val_rank V y
Proof
  rw[val_rank_def]>>
  irule LENGTH_FILTER_LEQ_MONO>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem val_rank_strict:
  MEM y V ∧ x < y ⇒ val_rank V x < val_rank V y
Proof
  Induct_on`V`>>
  rw[val_rank_def]>>
  gvs[GSYM val_rank_def]
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC>>
  irule arithmeticTheory.LESS_EQ_IMP_LESS_SUC>>
  irule val_rank_mono>>
  intLib.ARITH_TAC
QED

(* A value above another is in V, so ranks reflect the order *)
Theorem val_rank_le_imp:
  (y < x ⇒ MEM x V) ∧ val_rank V x ≤ val_rank V y ⇒ x ≤ y
Proof
  rw[]>>
  spose_not_then assume_tac>>
  `y < x` by intLib.ARITH_TAC>>
  `val_rank V y < val_rank V x` by metis_tac[val_rank_strict]>>
  intLib.ARITH_TAC
QED

(* Comparing ranks compares the values, when V contains each value that
  exceeds another *)
Theorem lex_le_val_rank:
  ∀xs ys.
    (∀x y. MEM x (xs ++ ys) ∧ MEM y (xs ++ ys) ∧ x < y ⇒ MEM y V) ∧
    lex_le (MAP (λx. &val_rank V x) xs) (MAP (λx. &val_rank V x) ys) ⇒
    lex_le xs ys
Proof
  Induct
  >- simp[lex_le_def]>>
  rpt gen_tac>>
  Cases_on`ys`
  >- simp[lex_le_def]>>
  qmatch_goalsub_rename_tac`lex_le (x::xs) (y::ys)`>>
  rw[lex_le_def]
  >- (
    disj1_tac>>
    spose_not_then assume_tac>>
    `val_rank V y ≤ val_rank V x` by
      (irule val_rank_mono>>intLib.ARITH_TAC)>>
    intLib.ARITH_TAC)>>
  `x ≤ y ∧ y ≤ x` by (
    conj_tac>>
    irule val_rank_le_imp>>
    qexists_tac`V`>>
    simp[]>>
    metis_tac[])>>
  `x = y` by intLib.ARITH_TAC>>
  gvs[]>>
  qpat_x_assum `∀ys. _` irule>>
  simp[]>>
  metis_tac[]
QED

Theorem vec_le_val_rank:
  ∀xs ys.
    (∀x y. MEM x (xs ++ ys) ∧ MEM y (xs ++ ys) ∧ x < y ⇒ MEM y V) ∧
    vec_le (MAP (λx. &val_rank V x) xs) (MAP (λx. &val_rank V x) ys) ⇒
    vec_le xs ys
Proof
  Induct
  >- simp[vec_le_def]>>
  rpt gen_tac>>
  Cases_on`ys`
  >- simp[vec_le_def]>>
  qmatch_goalsub_rename_tac`vec_le (x::xs) (y::ys)`>>
  rw[vec_le_def]
  >- (
    irule val_rank_le_imp>>
    qexists_tac`V`>>
    simp[]>>
    metis_tac[])>>
  qpat_x_assum `∀ys. _` (irule o REWRITE_RULE[vec_le_def])>>
  simp[]>>
  metis_tac[]
QED

(* The counts of the compared rows are the ranks of the selected values *)
Theorem rows_count:
  (∀j k. j < LENGTH L ∧ k < LENGTH V ⇒ (A (lv j k) ⇔ EL k V ≤ EL j L)) ∧
  (∀j. MEM j ps ⇒ j < LENGTH L) ⇒
  MAP (λrow. &LENGTH (FILTER A row)) (MAP (λj. GENLIST (lv j) (LENGTH V)) ps) =
  MAP (λx. &val_rank V x) (MAP (λj. EL j L) ps)
Proof
  rw[MAP_MAP_o,MAP_EQ_f]>>
  irule count_row>>
  metis_tac[]
QED

(* The references that sort the objective values, for any positions of
  their variables *)
Theorem sorted_ref_sound:
  pbc$satisfies A (set (thr_core objs rnl lo V)) ∧
  pbc$satisfies A (set (sort_core (LENGTH objs) (LENGTH V) lo ll)) ∧
  pbc$satisfies A (set (thr_core objs rnr ro V)) ∧
  pbc$satisfies A (set (sort_core (LENGTH objs) (LENGTH V) ro rl)) ∧
  LENGTH a = LENGTH objs ∧ LENGTH b = LENGTH objs ∧
  (∀i. i < LENGTH objs ⇒
    eval_lin_term A (npbc_lin (FST (rename_obj rnl (EL i objs)))) +
      SND (EL i objs) = EL i a ∧
    eval_lin_term A (npbc_lin (FST (rename_obj rnr (EL i objs)))) +
      SND (EL i objs) = EL i b) ∧
  (∀j. MEM j ps ⇒ j < LENGTH objs) ⇒
  MAP (λrow. &LENGTH (FILTER A row))
    (MAP (λj. GENLIST (ll j) (LENGTH V)) ps) =
  MAP (λx. &val_rank V x) (MAP (λj. EL j (sort_desc a)) ps) ∧
  MAP (λrow. &LENGTH (FILTER A row))
    (MAP (λj. GENLIST (rl j) (LENGTH V)) ps) =
  MAP (λx. &val_rank V x) (MAP (λj. EL j (sort_desc b)) ps)
Proof
  strip_tac>>
  `∀i k. i < LENGTH objs ∧ k < LENGTH V ⇒
     (A (lo i k) ⇔ EL k V ≤ EL i a) ∧ (A (ro i k) ⇔ EL k V ≤ EL i b)` by (
    rpt strip_tac>>
    irule thr_core_sat>>
    metis_tac[])>>
  `∀j k. j < LENGTH objs ∧ k < LENGTH V ⇒
     (A (ll j k) ⇔ EL k V ≤ EL j (sort_desc a)) ∧
     (A (rl j k) ⇔ EL k V ≤ EL j (sort_desc b))` by (
    rpt strip_tac>>
    irule sort_core_sat>>
    gvs[]>>
    metis_tac[])>>
  conj_tac>>
  irule rows_count>>
  simp[]
QED

Theorem sorted_lex_ref_sound:
  pbc$satisfies A (set (thr_core objs rnl lo V)) ∧
  pbc$satisfies A (set (sort_core (LENGTH objs) (LENGTH V) lo ll)) ∧
  pbc$satisfies A (set (thr_core objs rnr ro V)) ∧
  pbc$satisfies A (set (sort_core (LENGTH objs) (LENGTH V) ro rl)) ∧
  pbc$satisfies A (set (lex_cmp_core
    (MAP (λj. GENLIST (ll j) (LENGTH V)) ps)
    (MAP (λj. GENLIST (rl j) (LENGTH V)) ps) s g r)) ∧
  LENGTH a = LENGTH objs ∧ LENGTH b = LENGTH objs ∧
  (∀i. i < LENGTH objs ⇒
    eval_lin_term A (npbc_lin (FST (rename_obj rnl (EL i objs)))) +
      SND (EL i objs) = EL i a ∧
    eval_lin_term A (npbc_lin (FST (rename_obj rnr (EL i objs)))) +
      SND (EL i objs) = EL i b) ∧
  (∀j. MEM j ps ⇒ j < LENGTH objs) ∧
  (∀x y. MEM x (sort_desc a ++ sort_desc b) ∧
    MEM y (sort_desc a ++ sort_desc b) ∧ x < y ⇒ MEM y V) ⇒
  lex_le (MAP (λj. EL j (sort_desc a)) ps) (MAP (λj. EL j (sort_desc b)) ps)
Proof
  strip_tac>>
  drule_all sorted_ref_sound>>
  strip_tac>>
  drule lex_cmp_core_sat>>
  simp[]>>
  strip_tac>>
  irule lex_le_val_rank>>
  qexists_tac`V`>>
  simp[]>>
  rw[MEM_MAP]>>
  qpat_x_assum `∀x y. MEM x (sort_desc a ++ _) ∧ _ ⇒ _` irule>>
  simp[]>>
  metis_tac[EL_MEM,LENGTH_sort_desc]
QED

(* The Leximax reference forces the objective vectors of the two sides to be
  in leximax order *)
Theorem leximax_constrs_sound:
  pbc$satisfies A (set (leximax_constrs objs xvars us vs as V)) ∧
  (∀ob. MEM ob objs ⇒
    eval_lin_term A (npbc_lin (FST (rename_obj (list_list_insert xvars us) ob)))
      + SND ob = eval_obj (SOME ob) w1 ∧
    eval_lin_term A (npbc_lin (FST (rename_obj (list_list_insert xvars vs) ob)))
      + SND ob = eval_obj (SOME ob) w2) ∧
  vals_ok objs V ⇒
  ord_le Leximax (obj_vecs objs w1) (obj_vecs objs w2)
Proof
  strip_tac>>
  qabbrev_tac`a = obj_vecs objs w1`>>
  qabbrev_tac`b = obj_vecs objs w2`>>
  `LENGTH a = LENGTH objs ∧ LENGTH b = LENGTH objs` by
    simp[Abbr`a`,Abbr`b`,obj_vecs_def]>>
  `∀x y. MEM x (a ++ b) ∧ MEM y (a ++ b) ∧ x < y ⇒ MEM y V` by (
    gvs[vals_ok_def,Abbr`a`,Abbr`b`,obj_vecs_def,MEM_MAP]>>
    metis_tac[])>>
  `∀x y. MEM x (sort_desc a ++ sort_desc b) ∧
     MEM y (sort_desc a ++ sort_desc b) ∧ x < y ⇒ MEM y V` by
    metis_tac[PERM_sort_desc,PERM_MEM_EQ,MEM_APPEND]>>
  `∀i. i < LENGTH objs ⇒
    eval_lin_term A
      (npbc_lin (FST (rename_obj (list_list_insert xvars us) (EL i objs)))) +
      SND (EL i objs) = EL i a ∧
    eval_lin_term A
      (npbc_lin (FST (rename_obj (list_list_insert xvars vs) (EL i objs)))) +
      SND (EL i objs) = EL i b` by (
    rw[Abbr`a`,Abbr`b`,obj_vecs_def,EL_MAP]>>
    metis_tac[EL_MEM])>>
  `∀L:int list. LENGTH L = LENGTH objs ⇒
     MAP (λj. EL j L) (GENLIST I (LENGTH objs)) = L` by (
    rw[MAP_GENLIST]>>
    irule GENLIST_EL>>
    simp[])>>
  gvs[leximax_constrs_def,ord_le_def]>>
  `lex_le (MAP (λj. EL j (sort_desc a)) (GENLIST I (LENGTH objs)))
     (MAP (λj. EL j (sort_desc b)) (GENLIST I (LENGTH objs)))` suffices_by
    simp[]>>
  irule sorted_lex_ref_sound>>
  qpat_assum `satisfies A (set (thr_core _ (list_list_insert xvars us) _ _))`
    (irule_at Any)>>
  qpat_assum `satisfies A (set (thr_core _ (list_list_insert xvars vs) _ _))`
    (irule_at Any)>>
  qpat_x_assum `satisfies A (set (sort_core _ _ _ _))` (irule_at Any)>>
  qpat_x_assum `satisfies A (set (sort_core _ _ _ _))` (irule_at Any)>>
  simp[]>>
  qpat_assum `satisfies A (set (lex_cmp_core _ _ _ _ _))` (irule_at Any)>>
  simp[MEM_GENLIST,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem lookup_subset_sums:
  ∀f. lookup (SUM (MAP (npbc$eval_term w) f)) (subset_sums f) ≠ NONE
Proof
  Induct>>
  simp[subset_sums_def]>>
  rpt gen_tac>>
  PairCases_on`h`>>
  simp[subset_sums_def,lookup_union,lookup_fromAList]>>
  qmatch_asmsub_abbrev_tac`lookup ssum _ ≠ NONE`>>
  `∃u. lookup ssum (subset_sums f) = SOME u` by
    (Cases_on`lookup ssum (subset_sums f)`>>gvs[])>>
  Cases_on`w h1`>>
  rw[]>>
  TOP_CASE_TAC>>
  simp[ALOOKUP_NONE,MEM_MAP,EXISTS_PROD,MEM_toAList]
QED

Theorem MEM_dedup_sorted[simp]:
  ∀l. MEM x (dedup_sorted l) ⇔ MEM x l
Proof
  ho_match_mp_tac dedup_sorted_ind>>
  rw[dedup_sorted_def]>>
  metis_tac[]
QED

Theorem HD_dedup_sorted:
  ∀l. l ≠ [] ⇒ HD (dedup_sorted l) = HD l
Proof
  ho_match_mp_tac dedup_sorted_ind>>
  rw[dedup_sorted_def]
QED

Theorem MEM_mo_vals:
  MEM ob objs ⇒ MEM (eval_obj (SOME ob) w) (mo_vals objs)
Proof
  PairCases_on`ob`>>
  rw[mo_vals_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD,MEM_toAList,
    npbcTheory.eval_obj_def]>>
  mp_tac (Q.SPEC `ob0` lookup_subset_sums)>>
  Cases_on`lookup (SUM (MAP (eval_term w) ob0)) (subset_sums ob0)`>>
  rw[]>>
  qexistsl_tac[`ob0`,`ob1`,`SUM (MAP (eval_term w) ob0)`]>>
  rename1`SOME u`>>
  Cases_on`u`>>
  simp[]
QED

(* The first value is the least *)
Theorem HD_mo_vals:
  MEM z (mo_vals objs) ⇒ HD (mo_vals objs) ≤ z
Proof
  rw[mo_vals_def]>>
  qmatch_goalsub_abbrev_tac`dedup_sorted l`>>
  `transitive (λx y:int. x ≤ y)` by
    (simp[relationTheory.transitive_def]>>intLib.ARITH_TAC)>>
  `SORTED (λx y. x ≤ y) l` by (
    simp[Abbr`l`]>>
    irule mllistTheory.sort_SORTED>>
    simp[relationTheory.total_def]>>
    intLib.ARITH_TAC)>>
  gvs[]>>
  Cases_on`l`>>
  gvs[HD_dedup_sorted,SORTED_EQ]>>
  metis_tac[integerTheory.INT_LE_REFL,mllistTheory.sort_MEM,MEM]
QED

Theorem vals_ok_mo_vals:
  vals_ok objs (mo_vals objs) ∧ vals_ok objs (DROP 1 (mo_vals objs))
Proof
  rw[vals_ok_def]
  >- metis_tac[MEM_mo_vals]>>
  `MEM (eval_obj (SOME ob) w) (mo_vals objs) ∧
   MEM (eval_obj (SOME ob') w') (mo_vals objs)` by metis_tac[MEM_mo_vals]>>
  `HD (mo_vals objs) ≤ eval_obj (SOME ob) w` by metis_tac[HD_mo_vals]>>
  Cases_on`mo_vals objs`>>
  gvs[]>>
  `F` by intLib.ARITH_TAC
QED

(* Under an assignment reading w on ys, a renamed objective evaluates as the
  objective under w *)
Theorem eval_ref_obj:
  LENGTH ys = LENGTH xs ∧
  (∀j. j < LENGTH xs ⇒ A (EL j ys) = w (EL j (MAP FST xs))) ∧
  EVERY (λv. MEM v (MAP FST xs)) (mo_obj_vars objs) ∧ MEM ob objs ⇒
  eval_lin_term A
    (npbc_lin (FST (rename_obj (list_list_insert (MAP FST xs) ys) ob))) +
    SND ob = eval_obj (SOME ob) w
Proof
  rw[eval_lin_term_npbc_lin]>>
  `eval_obj (SOME (rename_obj (list_list_insert (MAP FST xs) ys) ob)) A =
   eval_obj (SOME ob) w` by (
    irule eval_obj_rename_obj>>
    rw[]>>
    irule rename_lookup_val>>
    gvs[EVERY_MEM]>>
    metis_tac[MEM_mo_obj_vars])>>
  PairCases_on`ob`>>
  gvs[rename_obj_def,npbcTheory.eval_obj_def]
QED

Theorem ref_ord_ok_sound:
  ref_ord_ok ord objs (((f,g,us,vs,as),asv):aord_s) xs ∧
  good_aspo ((f,g,us,vs,as),xs) ∧
  po_of_aspo ((f,g,us,vs,as),xs) w1 w2 ⇒
  ord_le ord (obj_vecs objs w1) (obj_vecs objs w2)
Proof
  rw[ref_ord_ok_def,lookup_list_to_num_set]>>
  Cases_on`ref_core ord objs (MAP FST xs) us vs as`>>
  gvs[]>>
  rename1`ref_core _ _ _ _ _ _ = SOME cs`>>
  drule_all po_of_aspo_assign>>
  strip_tac>>
  `npbc$satisfies A (set cs)` by (
    gvs[EVERY_MEM,check_imp_any_def,EXISTS_MEM,npbcTheory.satisfies_def]>>
    metis_tac[imp_thm,MEM_APPEND])>>
  gvs[good_aspo_def,good_aord_def,ALL_DISTINCT_APPEND]>>
  Cases_on`ord`
  >- (
    gvs[ref_core_def,ord_le_def]>>
    irule pareto_core_sound>>
    qexistsl_tac[`A`,`us`,`vs`,`xs`]>>
    simp[])>>
  gvs[ref_core_def,normalise_thm]>>
  irule leximax_constrs_sound>>
  qpat_assum `satisfies A (set (leximax_constrs _ _ _ _ _ _))` (irule_at Any)>>
  rw[vals_ok_mo_vals]>>
  irule eval_ref_obj>>
  simp[]>>
  metis_tac[]
QED
