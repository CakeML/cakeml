(*
  Formalization of the maximum common induced subgraph problem
*)
open preamble pb_preconstraintTheory;

val _ = new_theory "max_common_induced_subgraph";

(* Graph: (V : num , E : (num list) num_map)
  V number of vertices
  E edge list representation *)

Type graph = ``:num # (num list) num_map``;

(* Edge from a -> b in edge list representation e *)
Definition is_edge_def:
  is_edge e a b ⇔
  ∃ns.
  lookup a e = SOME ns ∧ MEM b ns
End

(* Well-formed, undirected *)
Definition good_graph_def:
  good_graph ((v,e):graph) ⇔
  ∀a ns.
    lookup a e = SOME ns ⇒ a < v ∧
    ∀b. is_edge e a b ⇒ is_edge e b a
End

(*
  Given graphs G_p := (vp,ep) , G_t := (vt,et)
  f is an injective partial map from v_p to v_t
  - dom f = vs (vs is the set of mapped vertices)
  - |vs| ≥ k (i.e., at least k vertices are mapped)
  - preserving adjacency and non-adjacency
*)
Definition injective_partial_map_def:
  injective_partial_map f vs k ((vp,ep):graph) ((vt,et):graph) ⇔
  vs ⊆ count vp ∧ CARD vs ≥ k ∧
  INJ f vs (count vt) ∧
  (∀a b. a ∈ vs ∧ b ∈ vs ∧ is_edge ep a b ⇒ is_edge et (f a) (f b)) ∧
  (∀a b. a ∈ vs ∧ b ∈ vs ∧ ¬(is_edge ep a b) ⇒ ¬ is_edge et (f a) (f b))
End

Definition is_path_def:
  (is_path ep [] ⇔ T) ∧
  (is_path ep [p] ⇔ T) ∧
  (is_path ep (x::y::ps) ⇔
    is_edge ep x y ∧ is_path ep (y::ps))
End

(* The vertex subset vs is connected *)
Definition connected_subgraph_def:
  connected_subgraph vs ep ⇔
  ∀a b. a ∈ vs ∧ b ∈ vs ⇒
  ∃path.
    set path ⊆ vs ∧
    is_path ep path
End

Definition index_def:
  index (vp:num) xp xt_opt =
  case xt_opt of
    NONE => xp
  | SOME xt => (xt+1)*vp + xp
End

Definition unindex_def:
  unindex n vp =
  if n < vp then (n, NONE)
  else
    (n MOD vp, SOME (n DIV vp - 1))
End

Theorem unindex_index:
  xp < vp ⇒
  unindex (index vp xp xt_opt) vp = (xp,xt_opt)
Proof
  rw[index_def,unindex_def]>>
  every_case_tac>>fs[]>>
  REWRITE_TAC[Once ADD_COMM, Once MULT_COMM]>>
  DEP_REWRITE_TAC[DIV_MULT]>>
  simp[]
QED

(* For each a in vp, either a is unassigned or a is assigned to exactly one vertex
  v in vt *)
Definition has_mapping_def:
  has_mapping a vp vt =
  Equal (
    (1, Pos (index vp a NONE)) ::
    GENLIST (λv. (1, Pos (index vp a (SOME v)))) vt) 1
End

Definition all_has_mapping_def:
  all_has_mapping vp vt =
  GENLIST (λa. has_mapping a vp vt) vp
End

Definition one_one_def:
  one_one u vp vt =
  GreaterEqual (GENLIST (λb. (1, Neg (index vp b (SOME u)))) vp) (&vp-1)
End

Definition all_one_one_def:
  all_one_one vp vt =
  GENLIST (λu. one_one u vp vt) vt
End

Definition neighbours_def:
  neighbours v e =
  case lookup v e of NONE => [] | SOME ns => ns
End

Definition not_neighbours_def:
  not_neighbours (v:num) e vs =
  let n = neighbours v e in
  FILTER (λu. ¬ MEM u n) (COUNT_LIST vs)
End

Definition edge_map_def:
  edge_map (a,b) u vp vt et =
  GreaterEqual (
    (1,Neg(index vp a (SOME u))) ::
    (1,Pos(index vp b NONE)) ::
    MAP (λv. (1,Pos(index vp b (SOME v)))) (neighbours u et) ) 1
End

Definition all_edge_map_def:
  all_edge_map (vp,ep) (vt,et) =
  FLAT (GENLIST (λu.
    FLAT (GENLIST (λa.
      MAP (λb. edge_map (a,b) u vp vt et) (neighbours a ep)) vp)) vt)
End

Definition not_edge_map_def:
  not_edge_map (a,b) u vp vt et =
  GreaterEqual (
    (1,Neg(index vp a (SOME u))) ::
    (1,Pos(index vp b NONE)) ::
    MAP (λv. (1,Pos(index vp b (SOME v)))) (not_neighbours u et vt) ) 1
End

Definition all_not_edge_map_def:
  all_not_edge_map (vp,ep) (vt,et) =
  FLAT (GENLIST (λu.
    FLAT (GENLIST (λa.
      MAP (λb. not_edge_map (a,b) u vp vt et) (not_neighbours a ep vp)) vp)) vt)
End

Definition k_size_def:
  k_size vp k =
  GreaterEqual (GENLIST (λb. (1, Neg (index vp b NONE))) vp) &k
End

Definition encode_def:
  encode (vp,ep) (vt,et) k =
  k_size vp k ::
  all_has_mapping vp vt ++
  all_one_one vp vt ++
  all_edge_map (vp,ep) (vt,et) ++
  all_not_edge_map (vp,ep) (vt,et)
End

(* move to pb_preconstraint *)
Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

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

Theorem iSUM_GENLIST_const:
  ∀vt c.
  iSUM (GENLIST (λv. c) vt) = c * &vt
Proof
  Induct>>simp[iSUM_def,GENLIST_CONS,o_DEF]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_const:
  ∀ls c. iSUM (MAP (λv. c) ls) = c * &(LENGTH ls)
Proof
  Induct>>simp[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem MEM_neighbours:
  MEM b (neighbours a ep) ⇔
  is_edge ep a b
Proof
  rw[neighbours_def,is_edge_def]>>
  every_case_tac>>fs[]
QED

Theorem MEM_not_neighbours:
  MEM b (not_neighbours a ep vp) ⇔
  b < vp ∧
  ¬is_edge ep a b
Proof
  rw[not_neighbours_def,MEM_FILTER,is_edge_def,neighbours_def]>>
  every_case_tac>>fs[MEM_COUNT_LIST]>>
  metis_tac[]
QED

Theorem iSUM_SNOC:
  ∀ls.
  iSUM (SNOC x ls) = x + iSUM ls
Proof
  Induct>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_GENLIST_geq_k:
  ∀vp vs k.
  vs ⊆ count vp ∧
  iSUM (GENLIST (λb. b2i (b ∈ vs)) vp) ≥ &k ⇒
  CARD vs ≥ k
Proof
  Induct>>rw[iSUM_def]
  >- intLib.ARITH_TAC>>
  fs[GENLIST,SUBSET_DEF]>>
  reverse (Cases_on`vp ∈ vs`>>fs[iSUM_SNOC])
  >- (
    first_x_assum match_mp_tac>>simp[]>>
    rw[]>>
    first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
    metis_tac[])>>
  first_x_assum(qspecl_then[`vs DIFF{vp}`,`k-1`] mp_tac)>>
  impl_tac>- (
    rw[]
    >- (
      first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
      metis_tac[]) >>
    Cases_on`k`>>fs[]
    >- (
      Cases_on`vp`>>simp[iSUM_def]>>
      match_mp_tac iSUM_geq>>simp[MEM_GENLIST]>>rw[]>>
      simp[PULL_EXISTS]>>
      qexists_tac`n`>>simp[])>>
    fs[ADD1,intLib.COOPER_PROVE``!n:int. 1 + n ≥ &(k+1) ⇔ n ≥ &k``]>>
    qmatch_asmsub_abbrev_tac`iSUM ls1`>>
    qmatch_goalsub_abbrev_tac`iSUM ls2`>>
    `ls1 = ls2` by
      (unabbrev_all_tac>>simp[LIST_EQ])>>
    fs[])>>
  DEP_REWRITE_TAC[CARD_DIFF]>>
  `vs ∩ {vp} = {vp}` by
    (simp[EXTENSION]>>metis_tac[])>>
  simp[]>>
  `FINITE vs` by (
    match_mp_tac SUBSET_FINITE_I>>
    qexists_tac`count (SUC vp)`>>
    fs[SUBSET_DEF])>>
  Cases_on`vs`>>fs[]
QED

Theorem iSUM_GENLIST_geq_k_rev:
  ∀vp vs k.
  vs ⊆ count vp ∧
  CARD vs ≥ k ⇒
  iSUM (GENLIST (λb. b2i (b ∈ vs)) vp) ≥ &k
Proof
  Induct>>rw[iSUM_def]>>fs[]
  >- intLib.ARITH_TAC>>
  fs[GENLIST,SUBSET_DEF]>>
  reverse (Cases_on`vp ∈ vs`>>fs[iSUM_SNOC])
  >- (
    first_x_assum match_mp_tac>>simp[]>>
    rw[]>>
    first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
    metis_tac[])>>
  first_x_assum(qspecl_then[`vs DIFF{vp}`,`k-1`] mp_tac)>>
  impl_tac>- (
    rw[]
    >- (
      first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
      metis_tac[]) >>
    Cases_on`k`>>fs[]>>
    DEP_REWRITE_TAC[CARD_DIFF]>>
    `vs ∩ {vp} = {vp}` by
      (simp[EXTENSION]>>metis_tac[])>>
    simp[]>>
    `FINITE vs` by (
      match_mp_tac SUBSET_FINITE_I>>
      qexists_tac`count (SUC vp)`>>
      fs[SUBSET_DEF])>>
    Cases_on`vs`>>fs[])>>
  Cases_on`k`
  >- (
    simp[]>>strip_tac>>
    match_mp_tac (intLib.COOPER_PROVE``!n:int. n ≥ 0 ⇒ 1 + n ≥ 0``)>>
    Cases_on`vp`>>simp[iSUM_def]>>
    match_mp_tac iSUM_geq>>simp[MEM_GENLIST]>>rw[]>>
    simp[PULL_EXISTS]>>
    qexists_tac`n`>>simp[])>>
  simp[ADD1]>>
  fs[ADD1,intLib.COOPER_PROVE``!n:int. 1 + n ≥ &(k+1) ⇔ n ≥ &k``]>>
  qmatch_goalsub_abbrev_tac`iSUM ls1 ≥ _`>>
  strip_tac>>
  qmatch_goalsub_abbrev_tac`iSUM ls2 ≥ _`>>
  `ls1 = ls2` by
    (unabbrev_all_tac>>simp[LIST_EQ])>>
  fs[]
QED

Theorem neg_b2i:
  1 - b2i p = b2i (~ p)
Proof
  Cases_on`p`>>simp[]
QED

Theorem encode_correct:
  good_graph (vp,ep) ∧
  good_graph (vt,et) ∧
  encode (vp,ep) (vt,et) k = constraints ⇒
  (
    (∃f vs.
      injective_partial_map f vs k (vp,ep) (vt,et)) ⇔
    satisfiable (set constraints)
  )
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[injective_partial_map_def]>>
    simp[satisfiable_def]>>
    qexists_tac`λn. let (a,u_opt) = unindex n vp in
      case u_opt of
        NONE => a ∉ vs
      | SOME u => a ∈ vs ∧ f a = u` >>
    rw[encode_def]
    >- (
      rename1`k_size`>>
      simp[k_size_def,satisfies_pbc_def,MAP_GENLIST, o_DEF]>>
      simp[Once GENLIST_if,unindex_index]>>
      simp[GSYM GENLIST_if]>>
      simp[neg_b2i]>>
      metis_tac[iSUM_GENLIST_geq_k_rev])
    >- (
      rename1`all_has_mapping`>>
      simp[all_has_mapping_def,satisfies_def,MEM_GENLIST,has_mapping_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF]>>
      simp[Once GENLIST_if,unindex_index]>>
      simp[GSYM GENLIST_if]>>
      simp[iSUM_def]>>
      Cases_on`a ∈ vs`>>simp[]
      >- ( (* a ∈ vs *)
        DEP_REWRITE_TAC[iSUM_eq_1]>>
        CONJ_TAC>-
          (simp[MEM_GENLIST]>>metis_tac[])>>
        qexists_tac`f a`>>
        CONJ_ASM1_TAC>>fs[EL_GENLIST,INJ_DEF]) >>
      simp[iSUM_GENLIST_const])
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
      Cases_on`j ∈ vs`>>fs[]>>
      `(f j ≠ u)` by
        metis_tac[]>>
      simp[])
    >- (
      rename1`all_edge_map`>>
      simp[all_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def]>>
      rw[]>>
      gvs[MEM_FLAT,MEM_GENLIST,MEM_MAP]>>
      fs[MEM_neighbours]>>
      simp[satisfies_pbc_def,MAP_MAP_o,o_DEF]>>
      `b < vp` by
        (fs[good_graph_def,is_edge_def]>>
        metis_tac[])>>
      simp[unindex_index]>>
      reverse (Cases_on`b ∈ vs`)>>fs[]
      >- (
        simp[iSUM_def,iSUM_MAP_const]>>
        Cases_on`a ∈ vs ∧ f a = u`>>simp[])>>
      reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
      >- (
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_neighbours]>>
        rw[]>>
        simp[])>>
      Cases_on`a ∈ vs`>>fs[]
      >- (
        match_mp_tac iSUM_geq>>
        rw[]
        >-
          (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
        simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD,MEM_neighbours]>>
        qexists_tac`f b`>>simp[]>>
        fs[INJ_DEF])>>
      simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
      match_mp_tac iSUM_zero>>
      simp[MEM_MAP,MEM_neighbours]>>
      rw[]>>
      simp[])
    >- (
      rename1`all_not_edge_map`>>
      simp[all_not_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,not_edge_map_def]>>
      rw[]>>
      gvs[MEM_FLAT,MEM_GENLIST,MEM_MAP]>>
      fs[MEM_not_neighbours]>>
      simp[satisfies_pbc_def,MAP_MAP_o,o_DEF]>>
      simp[unindex_index]>>
      reverse (Cases_on`b ∈ vs`)>>fs[]
      >- (
        simp[iSUM_def,iSUM_MAP_const]>>
        Cases_on`a ∈ vs ∧ f a = u`>>simp[])>>
      reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
      >- (
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_not_neighbours]>>
        rw[]>>
        simp[])>>
      Cases_on`a ∈ vs`>>fs[]
      >- (
        match_mp_tac iSUM_geq>>
        rw[]
        >-
          (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
        simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD,MEM_not_neighbours]>>
        qexists_tac`f b`>>simp[]>>
        fs[INJ_DEF])>>
      simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
      match_mp_tac iSUM_zero>>
      simp[MEM_MAP,MEM_not_neighbours]>>
      rw[]>>
      simp[]))>>
  fs[satisfiable_def,injective_partial_map_def]>>
  qexists_tac`λn. @m. m < vt ∧ w (index vp n (SOME m))`>>
  qabbrev_tac`dom = {n | n < vp ∧ ¬ w (index vp n NONE)}`>>
  qexists_tac `dom`>>
  simp[]>>
  CONJ_TAC>-
    simp[Abbr`dom`,SUBSET_DEF]>>
  fs[satisfies_def,encode_def,SF DNF_ss]>>
  CONJ_TAC>- (
    fs[k_size_def,satisfies_pbc_def,MAP_GENLIST,o_DEF,neg_b2i]>>
    match_mp_tac iSUM_GENLIST_geq_k>>
    qexists_tac`vp`>>fs[Abbr`dom`,SUBSET_DEF]>>
    qmatch_asmsub_abbrev_tac`iSUM ls1`>>
    qmatch_goalsub_abbrev_tac`iSUM ls2`>>
    `ls1 = ls2` by
      (unabbrev_all_tac>>simp[LIST_EQ])>>
    fs[])>>
  `∀n. n < vp ∧ ¬w (index vp n NONE) ⇒
   ∃m. m < vt ∧ w (index vp n (SOME m)) ∧
   ∀m'. m' < vt ∧ w (index vp n (SOME m')) ⇔ m = m'` by (
     fs[all_has_mapping_def,MEM_GENLIST,has_mapping_def,PULL_EXISTS]>>
     rw[]>>
     first_x_assum drule>>
     simp[satisfies_pbc_def,MAP_GENLIST,o_DEF]>>
     simp[iSUM_def]>>
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
    fs[Abbr`dom`]>>
    rw[INJ_DEF]
    >- (
      first_x_assum drule>>strip_tac>>
      rfs[])>>
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
    simp[])
  >- (
    fs[Abbr`dom`,good_graph_def]>>
    first_assum(qspec_then`a` mp_tac)>>
    first_x_assum(qspec_then`b` drule)>>
    simp[]>>
    rw[]>>
    gvs[]>>
    fs[all_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def,PULL_EXISTS,MEM_MAP,FORALL_PROD]>>
    `is_edge ep b a` by
      fs[is_edge_def]>>
    first_x_assum (drule_at (Pos (el 2)))>>
    disch_then (qspec_then`m` mp_tac)>>
    simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,MEM_neighbours]>>
    disch_then drule>>
    strip_tac>>
    gs[]>>
    drule iSUM_geq_1>>
    simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    gs[EL_MAP]>>
    qmatch_asmsub_abbrev_tac`index _ _ (SOME ee)`>>
    `m' = ee` by (
      unabbrev_all_tac>>
      metis_tac[MEM_EL,MEM_neighbours,is_edge_def])>>
    rw[]>>
    `MEM ee (neighbours m et)` by
      metis_tac[EL_MEM,Abbr`ee`]>>
    fs[MEM_neighbours]>>
    metis_tac[is_edge_def])
  >- (
    fs[Abbr`dom`,good_graph_def]>>
    first_assum(qspec_then`a` mp_tac)>>
    first_x_assum(qspec_then`b` drule)>>
    simp[]>>
    rw[]>>
    gvs[]>>
    fs[all_not_edge_map_def,satisfies_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,MEM_MAP,MEM_not_neighbours,not_edge_map_def]>>
    first_x_assum (drule_at (Pos (el 4)))>>
    disch_then (qspec_then`m'` mp_tac)>>
    simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
    strip_tac>>
    drule iSUM_geq_1>>
    simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    gs[EL_MAP]>>
    qmatch_asmsub_abbrev_tac`index _ _ (SOME ee)`>>
    ` m = ee` by (
      unabbrev_all_tac>>
      metis_tac[MEM_EL,MEM_not_neighbours])>>
    rw[]>>
    `MEM ee (not_neighbours m' et vt)` by
      metis_tac[EL_MEM,Abbr`ee`]>>
    fs[MEM_not_neighbours])
QED

val _ = export_theory();
