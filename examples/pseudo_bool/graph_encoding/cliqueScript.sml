(*
  Formalization of the max clique problem
*)
Theory clique
Ancestors
  pbc graph_basic pbc_normalise
Libs
  preamble

Definition is_clique_def:
  is_clique vs (v,e) ⇔
  vs ⊆ count v ∧
  (∀x y. x ∈ vs ∧ y ∈ vs ∧ x ≠ y ⇒
    is_edge e x y)
End

Definition max_clique_size_def:
  max_clique_size g =
  MAX_SET ({CARD vs | is_clique vs g})
End

Theorem CARD_clique_bound:
  is_clique vs g ⇒
  CARD vs ≤ FST g
Proof
  Cases_on`g`>>rw[is_clique_def]>>
  (drule_at Any) CARD_SUBSET>>
  simp[]
QED

Type annot = ``:(num # num)``;

(* annotated *)
Definition mk_constraint_def:
  mk_constraint e x y =
  if y ≤ x ∨ is_edge e x y then []
  else
    [((x,y),(GreaterEqual,[(1,Neg x);(1,Neg y)], 1)):(annot # num pbc)]
End

(* Encoding *)
Definition encode_def:
  encode (v,e) =
    FLAT (GENLIST (λx.
    FLAT (GENLIST (λy.
          mk_constraint e x y) v)) v):(annot # num pbc) list
End

(* Objective is to minimize the number of negated variables *)
Definition clique_obj_def:
  clique_obj v =
  SOME((GENLIST (λb. (1, Neg b)) v), 0)
    : ((num lin_term # int) option)
End

Theorem iSUM_SNOC:
  ∀ls.
  iSUM (SNOC x ls) = x + iSUM ls
Proof
  Induct>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_GENLIST_inter:
  iSUM (GENLIST (λb. b2i (b ∉ w)) v) =
  iSUM (GENLIST (λb. b2i (b ∉ (w ∩ count v))) v)
Proof
  AP_TERM_TAC>>
  fs[GENLIST_FUN_EQ]
QED

Theorem iSUM_GENLIST_eq_k:
  ∀vp vs.
  vs ⊆ count vp ⇒
  iSUM (GENLIST (λb. b2i (b ∉ vs)) vp) = &vp - &CARD vs
Proof
  Induct>>rw[iSUM_def]>>
  reverse (Cases_on`vp ∈ vs`>>fs[GENLIST,iSUM_SNOC])
  >- (
    first_x_assum(qspec_then`vs` mp_tac)>>
    impl_tac>- (
      fs[SUBSET_DEF]>>
      rw[]>>
      first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
      metis_tac[])>>
    rw[]>>
    intLib.ARITH_TAC)>>
  first_x_assum(qspecl_then[`vs DIFF{vp}`] mp_tac)>>
  impl_tac>- (
    fs[SUBSET_DEF]>>rw[]>>
    first_x_assum drule>>fs[prim_recTheory.LESS_THM])>>
  rw[]>>
  `(GENLIST (λb. b2i (b ∉ vs ∨ b = vp)) vp) =
   (GENLIST (λb. b2i (b ∉ vs)) vp)` by
    (match_mp_tac GENLIST_CONG>>fs[])>>
  gvs[] >>
  `FINITE vs` by (
    match_mp_tac SUBSET_FINITE_I>>
    qexists_tac`count (SUC vp)`>>
    fs[SUBSET_DEF])>>
  `CARD (vs DIFF {vp}) = CARD vs - 1` by
    (DEP_REWRITE_TAC[CARD_DIFF]>>
    `vs ∩ {vp} = {vp}` by
      (simp[EXTENSION]>>metis_tac[])>>
    simp[])>>
  rw[]>>
  `CARD vs > 0` by
    (Cases_on`vs`>>rw[]>>gvs[EXTENSION])>>
  Cases_on`CARD vs`>>fs[]>>
  intLib.ARITH_TAC
QED

Theorem MEM_if:
  MEM x (if P then A else B) ⇔
  if P then MEM x A else MEM x B
Proof
  rw[]
QED

Theorem b2i_rewrite[simp]:
  1 − b2i (vs b) = b2i (b ∉ vs)
Proof
  Cases_on`vs b`>>fs[IN_APP]
QED

Theorem encode_correct:
  good_graph (v,e) ∧
  encode (v,e) = constraints ⇒
  (
    (∃vs.
      is_clique vs (v,e) ∧
      CARD vs = k) ⇔
    (∃w.
      pbc$satisfies w (set (MAP SND constraints)) ∧
      eval_obj (clique_obj v) w = &v - &k)
  )
Proof
  rw[EQ_IMP_THM]
  >- (
    qexists_tac`vs`>>
    rw[encode_def]
    >- (
      simp[satisfies_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,mk_constraint_def,MEM_MAP]>>
      rw[]>>
      gvs[satisfies_pbc_def,eval_lin_term_def,is_clique_def,iSUM_def]>>
      rename1`is_edge e x y`>>
      `¬(x ∈ vs ∧ y ∈ vs)` by
        (CCONTR_TAC>>fs[]>>
        first_x_assum(qspecl_then[`x`,`y`] mp_tac)>>
        gvs[])>>
      fs[]
      >- (Cases_on`y ∈ vs`>>fs[])
      >- (Cases_on`x ∈ vs`>>fs[]))
    >- (
      simp[eval_obj_def,clique_obj_def,eval_lin_term_def,MAP_GENLIST,o_DEF]>>
      simp[]>>
      MATCH_MP_TAC iSUM_GENLIST_eq_k>>
      fs[is_clique_def]))
  >- (
    qexists_tac`w ∩ count v`>>
    rw[is_clique_def]
    >- (
      fs[satisfies_def,encode_def,MEM_FLAT,PULL_EXISTS,MEM_GENLIST,mk_constraint_def,MEM_MAP]>>
      rename1`is_edge e x y`>>
      wlog_tac `x < y` [`x`,`y`]
      >- (
        first_x_assum(qspecl_then[`y`,`x`] mp_tac)>>
        fs[good_graph_def,is_edge_thm])>>
      fs[MEM_if]>>
      CCONTR_TAC>>
      res_tac>>fs[satisfies_pbc_def,eval_lin_term_def,IN_APP]>>
      ntac 2 (last_x_assum kall_tac)>>
      rfs[iSUM_def])>>
    pop_assum mp_tac>>
    simp[eval_obj_def,clique_obj_def,eval_lin_term_def,MAP_GENLIST,o_DEF]>>
    REWRITE_TAC [Once iSUM_GENLIST_inter]>>
    DEP_REWRITE_TAC [iSUM_GENLIST_eq_k]>>
    simp[]>>
    intLib.ARITH_TAC)
QED

(* Encode the variables as strings
  and normalize to ≥ only *)
Definition enc_string_def:
  (enc_string x =
    concat [strlit"x";toString (x+1)])
End

Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  rw [INJ_DEF]
  \\ fs [enc_string_def]
  \\ fs [mlstringTheory.concat_def]
  \\ every_case_tac \\ gvs []
  \\ pop_assum sym_sub_tac
  \\ fs [mlintTheory.num_to_str_11]
QED

Definition annot_string_def:
  annot_string ((x,y):annot) = SOME (concat[strlit"nonadj"; toString (x+1) ; strlit"_" ; toString (y+1)])
End

Definition full_encode_def:
  full_encode g =
  (map_obj enc_string
    (clique_obj (FST g)),
  MAP (annot_string ## map_pbc enc_string) (encode g))
End

(* Convert minimization to maximization and add default 0 lb *)
Definition conv_concl_def:
  (conv_concl n (OBounds lbi ubi) =
  let ubg =
    case lbi of NONE => 0 (* Dummy impossible value *)
    | SOME lb =>
      if lb ≤ 0 then n else n - Num lb in
  let lbg =
    case ubi of NONE => (0:num)
    | SOME ub => (n - Num (ABS ub)) in
    SOME (lbg,ubg)) ∧
  (conv_concl _ _ = NONE)
End

Theorem is_clique_exists:
  is_clique {} g
Proof
  Cases_on`g`>>
  simp[is_clique_def]
QED

Theorem is_clique_CARD:
  is_clique vs g ⇒
  CARD vs ≤ FST g
Proof
  Cases_on`g`>>
  rw[is_clique_def]>>
  `FINITE (count q)` by
    fs[]>>
  drule CARD_SUBSET>>
  disch_then drule>>
  simp[]
QED

Theorem b2i_geq_zero[simp]:
  b2i b ≥ 0
Proof
  Cases_on`b`>>
  simp[]
QED

Theorem iSUM_zero:
  (∀x. MEM x ls ⇒ x ≥ 0) ⇒
  iSUM ls ≥ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_sub_b2i_geq_0':
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  iSUM ls ≤ &(LENGTH ls)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[ADD1]>>
  intLib.ARITH_TAC
QED

Theorem eval_obj_clique_obj_bounds:
  eval_obj (clique_obj q) w ≥ 0 ∧
  eval_obj (clique_obj q) w ≤ &q
Proof
  fs[clique_obj_def,eval_obj_def,eval_lin_term_def]>>
  CONJ_ASM1_TAC
  >- (
    match_mp_tac iSUM_zero>>
    simp[MEM_MAP,MEM_GENLIST,PULL_EXISTS])>>
  qmatch_goalsub_abbrev_tac`iSUM ls`>>
  `q = LENGTH ls` by
    fs[Abbr`ls`]>>
  rw[]>>
  DEP_REWRITE_TAC[iSUM_sub_b2i_geq_0']>>
  simp[Abbr`ls`,MEM_MAP,MEM_GENLIST,PULL_EXISTS]>>rw[]>>
  qexists_tac`b ∈ w`>>
  Cases_on` b ∈ w`>>fs[IN_APP]
QED

Theorem full_encode_sem_concl:
  good_graph g ∧
  full_encode g = (obj,pbf) ∧
  sem_concl (set (MAP SND pbf)) obj concl ∧
  conv_concl (FST g) concl = SOME (lbg, ubg) ⇒
  (∀vs. is_clique vs g ⇒ CARD vs ≤ ubg) ∧
  (∃vs. is_clique vs g ∧ lbg ≤ CARD vs)
Proof
  strip_tac>>
  gvs[full_encode_def]>>
  qpat_x_assum`sem_concl _ _ _` mp_tac>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE]>>
  simp[GSYM IMAGE_IMAGE, GSYM (Once LIST_TO_SET_MAP)]>>
  DEP_REWRITE_TAC[GSYM concl_INJ_iff]>>
  CONJ_TAC >- (
    assume_tac enc_string_INJ>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  Cases_on`concl`>>fs[conv_concl_def]>>
  rename1`OBounds lbi ubi`>>
  simp[sem_concl_def]>>
  Cases_on`g`>>
  drule encode_correct>>
  rw[]
  >- ( (* Lower bound optimization *)
    Cases_on`lbi`>>fs[unsatisfiable_def,satisfiable_def]
    >- (
      (* the formula is always satisfiable, so INF lower bound
         is impossible *)
      `F` by
        metis_tac[is_clique_exists])>>
    fs[SF DNF_ss,EQ_IMP_THM]>>
    first_x_assum drule>> strip_tac>>
    drule is_clique_CARD>>simp[]>>rw[]>>
    first_x_assum drule_all>>rw[]>>
    intLib.ARITH_TAC)>>
  (* Upper bound optimization *)
  Cases_on`ubi`>>
  fs[SF DNF_ss,EQ_IMP_THM]
  >-
    metis_tac[is_clique_exists]>>
  `eval_obj (clique_obj q) w ≥ 0` by
    (fs[clique_obj_def,eval_obj_def,eval_lin_term_def]>>
    match_mp_tac iSUM_zero>>
    simp[MEM_MAP,MEM_GENLIST,PULL_EXISTS])>>
  first_x_assum drule>>
  disch_then(qspec_then`q - Num (eval_obj (clique_obj q) w)` mp_tac)>>
  impl_tac >- (
    DEP_REWRITE_TAC[GSYM integerTheory.INT_SUB]>>
    mp_tac eval_obj_clique_obj_bounds>>
    intLib.ARITH_TAC)>>
  rw[]>>
  asm_exists_tac>>simp[]>>
  intLib.ARITH_TAC
QED

Theorem MAX_SET_eq_intro:
  FINITE s ∧
  (∀x. x ∈ s ⇒ x ≤ n) ∧
  n ∈ s ⇒
  MAX_SET s = n
Proof
  rw[]>>
  DEEP_INTRO_TAC MAX_SET_ELIM>>
  simp[]>>
  rw[]>>
  fs[]>>
  res_tac>>fs[]
QED

Theorem full_encode_sem_concl_check:
  good_graph g ∧
  full_encode g = (obj,pbf) ∧
  sem_concl (set (MAP SND pbf)) obj concl ∧
  conv_concl (FST g) concl = SOME (mc,mc) ⇒
  max_clique_size g = mc
Proof
  rw[]>>
  drule_all  full_encode_sem_concl>>
  simp[max_clique_size_def]>>
  rw[]>>
  match_mp_tac MAX_SET_eq_intro>>
  CONJ_TAC >- (
    `FINITE (count (FST g + 1))` by fs[]>>
    drule_then match_mp_tac SUBSET_FINITE>>
    rw[SUBSET_DEF]>>
    drule CARD_clique_bound>>
    simp[])>>
  rw[]
  >-
    metis_tac[]>>
  first_assum drule>>
  strip_tac>>
  first_x_assum (irule_at Any)>>
  fs[]
QED

Theorem full_encode_eq =
  full_encode_def
  |> SIMP_RULE (srw_ss()) [FORALL_PROD,encode_def]
  |> SIMP_RULE (srw_ss()) [mk_constraint_def]
  |> SIMP_RULE (srw_ss()) [MAP_FLAT,MAP_GENLIST,MAP_APPEND,o_DEF,MAP_MAP_o,pbc_ge_def,map_pbc_def,FLAT_FLAT,FLAT_MAP_SING,map_lit_def,MAP_if]
  |> SIMP_RULE (srw_ss()) [FLAT_GENLIST_FOLDN,FOLDN_APPEND_op]
  |> PURE_ONCE_REWRITE_RULE [APPEND_OP_DEF]
  |> SIMP_RULE (srw_ss()) [if_APPEND];

