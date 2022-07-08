(*
  Formalization of the subgraph isomorphism problem
*)
open preamble pb_preconstraintTheory;

val _ = new_theory "subgraph_iso";

(* Graph: num (number of vertices)
          (num,num) list (edges) *)

Type graph = ``:num # (num#num) list``;

(* Maybe need more constraints *)
Definition good_graph_def:
  good_graph ((v,e):graph) ⇔
  (∀a b. MEM (a,b) e ⇒ a < v ∧ b < v ∧ MEM (b,a) e)
End

Definition has_subgraph_iso_def:
  has_subgraph_iso ((vp,ep):graph) ((vt,et):graph) ⇔
  ∃f.
    INJ f (count vp) (count vt) ∧
    (∀a b. MEM (a,b) ep ⇒ MEM (f a, f b) et)
End

Definition index_def:
  index (vt:num) xp xt =
  xp*vt + xt
End

Definition neighbours_def:
  neighbours v e =
  MAP FST (FILTER (λ(x,y). y=v) e)
End

(* a in vp *)
Definition has_mapping_def:
  has_mapping a vt =
  Equal (GENLIST (λv. (1, Pos (index vt a v))) vt) 1
End

Definition all_has_mapping_def:
  all_has_mapping vp vt =
  GENLIST (λa. has_mapping a vt) vp
End

Definition one_one_def:
  one_one u vp vt =
  GreaterEqual (GENLIST (λb. (1, Neg (index vt b u))) vp) (&vp-1)
End

Definition all_one_one_def:
  all_one_one vp vt =
  GENLIST (λu. one_one u vp vt) vt
End

Definition edge_map_def:
  edge_map (a,b) u vt et =
  GreaterEqual ( (1,Neg(index vt a u)) :: MAP (λv. (1,Pos(index vt b v))) (neighbours u et) ) 1
End

Definition all_edge_map_def:
  all_edge_map (vp,ep) (vt,et) =
  FLAT (GENLIST (λu. MAP (λ(a,b). edge_map (a,b) u vt et) ep) vt)
End

Definition encode_def:
  encode (vp,ep) (vt,et) =
  all_has_mapping vp vt ++ all_one_one vp vt ++ all_edge_map (vp,ep) (vt,et)
End

(* move to pb_preconstraint *)
Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

Definition unindex_def:
  unindex n vt =
  (n DIV vt, n MOD vt)
End

Theorem unindex_index:
  v < vt ⇒
  unindex (index vt a v) vt = (a,v)
Proof
  rw[index_def,unindex_def]>>
  REWRITE_TAC[Once ADD_COMM]>>
  metis_tac [DIV_MULT]
QED

Theorem GENLIST_if:
  GENLIST f k = GENLIST (λn. if n < k then f n else ARB) k
Proof
  simp[LIST_EQ]
QED

Theorem b2i_eq_1[simp]:
  b2i b = 1 ⇔ b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_eq_0[simp]:
  b2i b = 0 ⇔ ¬b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_geq_zero[simp]:
  b2i b ≥ 0
Proof
  Cases_on`b`>>simp[]
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

Theorem iSUM_geq:
  ∀ls.
  (∀x. MEM x ls ⇒ x ≥ 0) ∧
  (∃x. MEM x ls ∧ x ≥ n)
  ⇒
  iSUM ls ≥ n
Proof
  Induct>>rw[iSUM_def]
  >- (
    `iSUM ls ≥ 0` by
      (irule iSUM_zero>>
      metis_tac[])>>
    intLib.ARITH_TAC)>>
  gs[]>>
  last_x_assum mp_tac>>
  impl_tac >- metis_tac[]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem b2i_iSUM_eq_0:
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
  (iSUM ls = 0 ⇔
  ∀j. j < LENGTH ls ⇒ EL j ls = 0)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]
  >- (
    `iSUM ls ≥ 0` by (
      match_mp_tac iSUM_zero>>
      rw[]>>res_tac>>
      rw[])>>
    rw[EQ_IMP_THM]
    >- (
      last_x_assum kall_tac>>
      intLib.COOPER_TAC)>>
    pop_assum(qspec_then`0` mp_tac)>>simp[])
  >>
  rw[EQ_IMP_THM]
  >-
    (Cases_on`j`>>fs[])>>
  first_x_assum (qspec_then`SUC j` mp_tac)>>fs[]
QED

Theorem iSUM_geq_1:
  iSUM ls ≥ 1 /\
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
    ∃i. i < LENGTH ls ∧ EL i ls  = 1
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[]
  >- (qexists_tac`0`>>rw[])>>
  qexists_tac`SUC i`>>rw[]
QED

Theorem iSUM_eq_1:
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
  (iSUM ls = 1 ⇔
  ∃i. i < LENGTH ls ∧ EL i ls  = 1 ∧
  ∀j. i ≠ j ∧ j < LENGTH ls ⇒ EL j ls = 0)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[]
  >-(
    DEP_REWRITE_TAC[b2i_iSUM_eq_0]>>
    CONJ_TAC >- metis_tac[]>>
    rw[EQ_IMP_THM]
    >- (
      qexists_tac`0`>>rw[]>>
      Cases_on`j`>>fs[])>>
    `i = 0` by
      (CCONTR_TAC>>
      first_x_assum drule>>fs[])>>
    first_x_assum(qspec_then`SUC j` assume_tac)>>rfs[]>>
    Cases_on`i`>>fs[])
  >>
  rw[EQ_IMP_THM]
  >- (
    qexists_tac`SUC i`>>rw[]>>
    Cases_on`j`>>fs[])>>
  Cases_on`i`>>fs[]>>
  qexists_tac`n`>>rw[]>>
  first_x_assum(qspec_then`SUC j` assume_tac)>>fs[]
QED

Theorem iSUM_sub_b2i_geq_0:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  iSUM ls ≤ &(LENGTH ls)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[ADD1]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_sub_b2i_geq_0:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  (iSUM ls ≥ &(LENGTH ls) ⇔
   ∀i. i < LENGTH ls ⇒ EL i ls = 1)
Proof
  Induct_on`ls`>>
  fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]
  >- (
    `iSUM ls ≤ &(LENGTH ls)` by
      metis_tac[iSUM_sub_b2i_geq_0]>>
    rw[EQ_IMP_THM]
    >-
      (last_x_assum kall_tac>>intLib.ARITH_TAC)>>
    first_x_assum(qspec_then`0` assume_tac)>>fs[])>>
  simp[ADD1,GSYM integerTheory.INT_ADD,intLib.COOPER_PROVE``!n:int. 1 + n ≥ m + 1 ⇔ n ≥ m``]>>
  rw[EQ_IMP_THM]
  >-
    (Cases_on`i`>>fs[])>>
  first_x_assum(qspec_then`SUC i` assume_tac)>>fs[]
QED

Theorem iSUM_sub_b2i_geq:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  (iSUM ls ≥ &(LENGTH ls) − 1 ⇔
   ∀i. i < LENGTH ls ∧ EL i ls = 0 ⇒
   ∀j. i ≠ j ∧ j < LENGTH ls ⇒ EL j ls = 1)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  simp[ADD1]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[GSYM integerTheory.INT_ADD,intLib.COOPER_PROVE``!n:int. n +1 -1 = n``]
  >- (
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq_0] >>
    CONJ_TAC >- metis_tac[]>>
    rw[EQ_IMP_THM]
    >- (
      Cases_on`j`>>fs[]>>
      Cases_on`i`>>fs[ADD1]>>
      first_x_assum drule>>fs[])>>
    first_x_assum(qspec_then`0` assume_tac)>>gs[]>>
    first_x_assum(qspec_then`SUC i` assume_tac)>>gs[])>>
  simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ m ⇔ n ≥ m - 1``]>>
  rw[EQ_IMP_THM]
  >- (
    Cases_on`i`>>fs[ADD1]>>
    first_x_assum drule>>simp[]>>
    Cases_on`j`>>fs[])>>
  first_x_assum(qspec_then`SUC i` assume_tac)>>gs[]>>
  first_x_assum(qspec_then`SUC j` assume_tac)>>gs[]
QED

Theorem encode_correct:
  good_graph (vp,ep) ∧
  good_graph (vt,et) ∧
  encode (vp,ep) (vt,et) = constraints ⇒
  (has_subgraph_iso (vp,ep) (vt,et) ⇔ satisfiable (set constraints))
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[has_subgraph_iso_def]>>
    simp[satisfiable_def]>>
    qexists_tac` λn. let (a,u) = unindex n vt in f a = u` >>
    rw[encode_def]
    >- (
      rename1`all_has_mapping`>>
      simp[all_has_mapping_def,satisfies_def,MEM_GENLIST,has_mapping_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF]>>
      simp[Once GENLIST_if,unindex_index]>>
      simp[GSYM GENLIST_if]>>
      res_tac>>
      DEP_REWRITE_TAC[iSUM_eq_1]>>
      CONJ_TAC>-
        (simp[MEM_GENLIST]>>metis_tac[])>>
      qexists_tac`f a`>>
      CONJ_ASM1_TAC>>fs[EL_GENLIST,INJ_DEF])
    >- (
      rename1`all_one_one`>>
      simp[all_one_one_def,satisfies_def,MEM_GENLIST,one_one_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF]>>
      simp[Once GENLIST_if,unindex_index]>>
      simp[GSYM GENLIST_if]>>
      fs[INJ_DEF]>>
      qmatch_goalsub_abbrev_tac`iSUM ls`>>
      `vp = LENGTH ls` by
        simp[Abbr`ls`]>>
      simp[]>>
      DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
      simp[Abbr`ls`]>>
      CONJ_TAC>- (
        simp[MEM_GENLIST]>>
        metis_tac[])>>
      rw[]>>
      gs[EL_GENLIST]>>
      `(f j ≠ u)` by
        metis_tac[]>>
      simp[])
    >- (
      rename1`all_edge_map`>>
      (* all_edge_map *)
      simp[all_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def]>>
      rw[]>>
      gvs[MEM_MAP]>>
      simp[neighbours_def,MAP_MAP_o,o_DEF]>>
      Cases_on`y`>>
      simp[satisfies_pbc_def,MAP_MAP_o,o_DEF]>>
      simp[unindex_index]>>
      reverse (Cases_on`f q = u`>>rw[]>>simp[iSUM_def])
      >- (
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP]>>
        rw[]>>
        simp[])>>
      res_tac>>
      fs[good_graph_def]>>
      simp[LAMBDA_PROD]>>
      match_mp_tac iSUM_geq>>rw[]
      >-
        (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
      simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD]>>
      qexists_tac`f r`>>simp[]>>
      DEP_REWRITE_TAC[unindex_index]>>simp[]>>
      metis_tac[]))>>
  fs[satisfiable_def,has_subgraph_iso_def]>>
  qexists_tac`λn. @m. m < vt ∧ w (index vt n m)`>>
  fs[satisfies_def,encode_def,SF DNF_ss]>>
  `∀n. n < vp ⇒
    ∃m. m < vt ∧ w (index vt n m) ∧
    ∀m'. m' < vt ∧ w (index vt n m') ⇔ m = m'` by (
    fs[all_has_mapping_def,MEM_GENLIST,has_mapping_def,PULL_EXISTS]>>
    rw[]>>
    first_x_assum drule>>
    simp[satisfies_pbc_def,MAP_GENLIST,o_DEF]>>
    DEP_REWRITE_TAC[iSUM_eq_1]>>
    CONJ_TAC>-
      (simp[MEM_GENLIST]>>metis_tac[])>>
    rw[]>>gs[EL_GENLIST]>>
    asm_exists_tac>>fs[]>>
    CCONTR_TAC>>gs[]>>
    Cases_on`i=m'`>>gs[]>>
    first_x_assum drule>>
    fs[])>>
  rw[]
  >- (
    rw[INJ_DEF]
    >- (
      first_x_assum drule>>strip_tac>>
      fs[])>>
    fs[all_one_one_def,MEM_GENLIST,PULL_EXISTS,one_one_def]>>
    res_tac>>
    gvs[]>>
    last_x_assum drule>>
    simp[satisfies_pbc_def,MAP_GENLIST,o_DEF]>>
    qmatch_goalsub_abbrev_tac`iSUM ls`>>
    `vp = LENGTH ls` by
      simp[Abbr`ls`]>>
    simp[]>>
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
    simp[Abbr`ls`]>>
    CONJ_TAC>- (
      simp[MEM_GENLIST]>>
      metis_tac[])>>
    rw[]>>
    first_x_assum drule>>
    simp[EL_GENLIST]>>
    disch_then(qspec_then`n` mp_tac)>>
    simp[])>>
  fs[good_graph_def]>>
  res_tac>>
  res_tac>>
  gvs[]>>
  fs[all_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def,PULL_EXISTS,MEM_MAP,FORALL_PROD]>>
  qpat_x_assum`MEM _ _ ` assume_tac>>
  first_x_assum (drule_at (Pos (el 2)))>>
  disch_then (qspec_then`m` mp_tac)>>
  simp[neighbours_def,satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
  strip_tac>>
  drule iSUM_geq_1>>
  simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
  impl_tac >- metis_tac[]>>
  strip_tac>>
  gs[EL_MAP]>>
  qmatch_asmsub_abbrev_tac`_ ee = 1`>>
  `MEM ee et` by
    (unabbrev_all_tac>>
    metis_tac[EL_MEM,MEM_FILTER])>>
  pairarg_tac>>fs[]>>
  `p2 = m` by (
    unabbrev_all_tac>>
    imp_res_tac EL_MEM>>
    gs[MEM_FILTER])>>
  fs[]>>
  metis_tac[]
QED

val _ = export_theory();
