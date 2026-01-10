(*
  Formalization of the CP to ILP phase (counting constraints)
*)
Theory cp_to_ilp_counting
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition neiv_def[simp]:
  neiv name (i:num) j =
    INR (name, Indices [i;j] NONE)
End

(* AllDifferent: All variables must take distinct values
   For n variables, this requires O(n^2) pairwise inequality constraints *)
Definition encode_all_different_def:
  encode_all_different bnd Xs name =
  FLAT (MAPi (λi X.
    FLAT (MAPi (λj Y.
      if i < j then
        [
          bits_imply bnd [Pos (neiv name i j)] (mk_gt X Y);
          bits_imply bnd [Neg (neiv name i j)] (mk_gt Y X)
        ]
      else []) Xs)) Xs)
End

Theorem encode_all_different_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (AllDifferent Xs)) ∧
  all_different_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_all_different bnd Xs name)
Proof
  rw[encode_all_different_def,all_different_sem_def,EVERY_MEM]>>
  gs[MEM_FLAT,MEM_MAPi]>>
  Cases_on ‘i < j’>>
  gs[reify_avar_def,reify_flag_def]
  >- intLib.ARITH_TAC>>
  rw[]>>
  fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
  first_x_assum $ qspecl_then [‘i’,‘j’] assume_tac>>
  intLib.ARITH_TAC
QED

Theorem all_different_sem_aux:
  (∀i j. i < j ∧ j < LENGTH Xs ⇒
    let X = EL i Xs in
    let Y = EL j Xs in
    if wb (neiv name i j)
    then varc wi X > varc wi Y
    else varc wi Y > varc wi X) ⇒
  all_different_sem Xs wi
Proof
  rw[all_different_sem_def,EL_ALL_DISTINCT_EL_EQ]>>
  Cases_on`n1 = n2`>>simp[]>>
  wlog_tac `n1 < n2` [`n1`,`n2`]
  >- (
    `n2 < n1` by fs[]>>
    first_x_assum drule_all>>
    simp[])>>
  first_x_assum drule>>
  rw[EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_all_different_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different bnd Xs name) ⇒
  all_different_sem Xs wi
Proof
  strip_tac>>
  irule all_different_sem_aux>>
  gs[EVERY_MEM,encode_all_different_def,MEM_FLAT,MEM_MAPi,PULL_EXISTS]>>
  qexistsl [‘name’,‘wb’]>>
  ntac 3 strip_tac>>
  ‘i < LENGTH Xs’ by fs[]>>
  first_x_assum $ drule_then rev_drule>>
  simp[SF DNF_ss]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* domain of X given by bnd (as a list) *)
Definition domlist_def:
  domlist bnd (X:'a varc) =
  case X of
    INL vX =>
      (let
        (lb, ub) = bnd vX
      in
        if ub < lb
        then []
        else GENLIST (λn. &n + lb) (Num (ub - lb) + 1))
  | INR cX => [cX]
End

Theorem MEM_domlist:
  valid_assignment bnd wi ⇒
  MEM (varc wi X) (domlist bnd X)
Proof
  Cases_on ‘X’>>
  rw[domlist_def,valid_assignment_def,varc_def]>>
  rename1 ‘bnd x’>>
  Cases_on ‘bnd x’>>
  rw[MEM_GENLIST]>>
  res_tac
  >-intLib.ARITH_TAC>>
  qexists ‘Num (wi x - q)’>>
  intLib.ARITH_TAC
QED

(* bijection 0, -1, 1, -2, 2,... ⇔ 0, 1, 2, 3, 4,... and its inverse next *)
Definition intnum_def:
  intnum (n: int) =
  if n < 0 then 2 * Num (-n) - 1
  else 2 * Num n
End

Definition numint_def:
  numint (n: num): int =
  if EVEN n then &((n + 1) DIV 2)
  else -&((n + 1) DIV 2)
End

Theorem numint_inj:
  numint m = numint n ⇒ m = n
Proof
  simp[numint_def]>>
  intLib.ARITH_TAC
QED

Theorem numint_intnum:
  numint (intnum x) = x
Proof
  simp[intnum_def,numint_def]>>
  intLib.ARITH_TAC
QED

Theorem intnum_numint:
  intnum (numint x) = x
Proof
  simp[intnum_def,numint_def]>>
  intLib.ARITH_TAC
QED

Definition numset_to_intlist_def:
  numset_to_intlist t = MAP (numint o FST) $ toSortedAList t
End

Theorem ALL_DISTINCT_numset_to_intlist:
  ALL_DISTINCT $ numset_to_intlist t
Proof
  simp[numset_to_intlist_def,GSYM MAP_MAP_o]>>
  irule ALL_DISTINCT_MAP_INJ>>
  simp[ALL_DISTINCT_MAP_FST_toSortedAList,numint_inj]
QED

(* Union of all int values in domains of Xs *)
Definition union_dom_def:
  union_dom bnd Xs =
  numset_to_intlist $ FOLDL union LN $
    MAP (λX. list_to_num_set $ MAP intnum $ domlist bnd X) Xs
End

Theorem MEM_numset_to_intlist:
  MEM x (numset_to_intlist ns) ⇔
  intnum x ∈ domain ns
Proof
  rw[numset_to_intlist_def,GSYM MAP_MAP_o,MEM_MAP,EXISTS_PROD,
    MEM_toSortedAList,domain_lookup]>>
  metis_tac[intnum_numint,numint_intnum]
QED

Theorem domain_FOLDL_union:
  ∀ls t.
  x ∈ domain (FOLDL union t ls) ⇔
  x ∈ domain t ∨ ∃ns. ns ∈ set ls ∧ x ∈ domain ns
Proof
  Induct>>rw[]>>
  metis_tac[]
QED

Theorem EVERY_MEM_union_dom:
  valid_assignment bnd wi ⇒
  EVERY (λX. MEM (varc wi X) (union_dom bnd Xs)) Xs
Proof
  rw[EVERY_MEM,union_dom_def,MEM_numset_to_intlist,domain_FOLDL_union]>>
  simp[MEM_MAP,PULL_EXISTS,domain_list_to_num_set]>>
  metis_tac[MEM_domlist]
QED

Theorem ALL_DISTINCT_union_dom:
  ALL_DISTINCT $ union_dom bnd Xs
Proof
  simp[union_dom_def,ALL_DISTINCT_numset_to_intlist]
QED

Definition elm_def[simp]:
  elm name (v:int) =
  INR (name, Values [v] NONE)
End

(* encodes fnvalue_v ⇔ some X = v *)
Definition encode_some_eq_def:
  encode_some_eq bnd Xs (v: int) name =
    bimply_bits bnd [Pos (elm name v)]
      ([], MAP (λX. (1i, Pos (INL (Eq X v)))) Xs, 1i)
End

Theorem iSUM_ge_0:
  (∀x. MEM x ls ⇒ x ≥ 0) ⇒
  iSUM ls ≥ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem b2i_alt:
  b2i b = if b then 1 else 0
Proof
  rw[]
QED

Theorem eval_lin_term_ge_1:
  eval_lin_term wb (MAP (λe. (1, f e)) ls) ≥ 1 ⇔
  ∃e. MEM e ls ∧ lit wb (f e)
Proof
  rw[eval_lin_term_def]>>
  Induct_on ‘ls’>>
  rw[iSUM_def,b2i_alt]
  >-(
    simp[SF DNF_ss]>>
    qmatch_goalsub_abbrev_tac`_ + iSUM lss ≥ _`>>
    `iSUM lss ≥ 0` by (
      irule iSUM_ge_0>>
      simp[Abbr`lss`,MEM_MAP,PULL_EXISTS,b2i_alt]>>
      rw[])>>
    intLib.ARITH_TAC)
  >- metis_tac[]
QED

Theorem encode_some_eq_sem:
  valid_assignment bnd wi ∧
  EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_some_eq bnd Xs v name) =
  (wb (elm name v) ⇔ ∃X. MEM X Xs ∧ wb (INL (Eq X v))))
Proof
  rw[encode_some_eq_def,iconstraint_sem_def,eval_lin_term_ge_1]>>
  metis_tac[]
QED

Definition reify_some_eq_def:
  reify_some_eq bnd Xs v name =
  let
    ges = FLAT $ MAP (λX. encode_ge bnd X v ++ encode_ge bnd X (v + 1)) Xs;
    eqs = FLAT $ MAP (λX. encode_eq bnd X v) Xs
  in
    ges ++ eqs ++ encode_some_eq bnd Xs v name
End

Theorem FORALL_IMP_EQ[local] = METIS_PROVE []
  ``(∀x. P x ⇒ (Q x ⇔ R x)) ⇒ ((∀x. P x ⇒ Q x) ⇔ (∀x. P x ⇒ R x))``;

Theorem reify_some_eq_sem:
  valid_assignment bnd wi ⇒ (
  EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT (MAP (λv. reify_some_eq bnd Xs v name)
    (union_dom bnd Xs))) ⇔
  ∀v. MEM v (union_dom bnd Xs) ⇒
      EVERY (λX. wb (INL (Ge X v)) ⇔ varc wi X ≥ v) Xs ∧
      EVERY (λX. wb (INL (Ge X (v + 1))) ⇔ varc wi X ≥ v + 1) Xs ∧
      EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ∧
      (wb (elm name v) ⇔ ∃X. MEM X Xs ∧ wb (INL (Eq X v))))
Proof
  rw[reify_some_eq_def,EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_MEM,Once $ GSYM CONJ_ASSOC]>>
  ho_match_mp_tac FORALL_IMP_EQ>>
  rw[EVERY_CONJ,GSYM CONJ_ASSOC]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (irule EVERY_CONG>>simp[encode_ge_sem])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (irule EVERY_CONG>>simp[encode_ge_sem])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (
    irule EVERY_CONG>>
    rw[]>>
    irule encode_eq_sem>>
    fs[EVERY_MEM])>>
  simp[encode_some_eq_sem]
QED

(* encodes (sum of the bitlist Bs) = Y *)
Definition encode_bitsum_def:
  encode_bitsum Bs Y =
  case Y of
    INL vY => [
      ([(-1i, vY)], MAP (λb. (1i, Pos b)) Bs, 0i);
      ([(1i, vY)], MAP (λb. (-1i, Pos b)) Bs, 0i)]
  | INR cY => [
      ([], MAP (λb. (1i, Pos b)) Bs, cY);
      ([], MAP (λb. (-1i, Pos b)) Bs, -cY)]
End

Theorem iSUM_MAP_lin:
  ∀ls a f b. iSUM (MAP (λx. a * f x + b) ls) = a * iSUM (MAP (λx. f x) ls) + b * &LENGTH ls
Proof
  Induct>>
  simp[iSUM_def,MAP,LENGTH]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_lin_const = iSUM_MAP_lin |> CONV_RULE (RESORT_FORALL_CONV List.rev) |> Q.SPEC `0` |> SRULE [] |> SPEC_ALL;

Theorem encode_bitsum_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_bitsum Bs Y) ⇔
  iSUM $ MAP (b2i o wb) Bs = varc wi Y)
Proof
  rw[encode_bitsum_def]>>
  CASE_TAC>>
  simp[varc_def,iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,
    eval_iterm_def,eval_term_def,iSUM_def,MAP_MAP_o,combinTheory.o_ABS_R,
    iSUM_MAP_lin_const]>>
  simp[GSYM combinTheory.o_ABS_R,GSYM combinTheory.I_EQ_IDABS]>>
  intLib.ARITH_TAC
QED

Theorem encode_n_value_sem_aux:
  valid_assignment bnd wi ∧
  (∀v. MEM v (union_dom bnd Xs) ⇒
    EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ∧
    (wb (elm name v) ⇔ ∃X. MEM X Xs ∧ wb (INL (Eq X v)))) ⇒
  ∀v. MEM v (MAP (varc wi) Xs) ⇔ MEM v (FILTER (λv. wb (elm name v)) (union_dom bnd Xs))
Proof
  rw[MEM_FILTER,MEM_MAP]>>
  iff_tac>>
  strip_tac
  >-(
    CONJ_ASM2_TAC
    >- (
      gvs[EVERY_MEM]>>
      metis_tac[])>>
    drule_then assume_tac EVERY_MEM_union_dom>>
    fs[EVERY_MEM])>>
  gvs[EVERY_MEM]>>
  metis_tac[]
QED

Theorem list_set_eq:
  ∀ls1 ls2. (∀v. MEM v ls1 ⇔ MEM v ls2) ⇔ set ls1 = set ls2
Proof
  rw[SET_EQ_SUBSET]>>
  simp[GSYM SUBSET_DIFF_EMPTY,list_to_set_diff,GSYM NULL_EQ,NULL_FILTER]>>
  metis_tac[]
QED

(* NValue: Y equals the number of distinct values in Xs
   This is very complex and requires auxiliary variables *)
Definition encode_n_value_def:
  encode_n_value bnd Xs Y name =
  let
    vals = union_dom bnd Xs
  in
    (FLAT $ MAP (λv. reify_some_eq bnd Xs v name) vals) ++
    encode_bitsum (MAP (elm name) vals) Y
End

Theorem subset_varc_union_dom:
  valid_assignment bnd wi ⇒
  set $ MAP (varc wi) Xs ⊆ set $ union_dom bnd Xs
Proof
  strip_tac>>
  drule EVERY_MEM_union_dom>>
  rw[EVERY_MEM,SUBSET_DEF]>>
  gs[MEM_MAP]
QED

Theorem LENGTH_FILTER_subset:
  set ls1 ⊆ set ls2 ∧ ALL_DISTINCT ls2 ⇒
  LENGTH (FILTER (λv. MEM v ls1) ls2) = CARD (set ls1)
Proof
  rw[SUBSET_DEF]>>
  drule_then (qspec_then ‘(λv. MEM v ls1)’ assume_tac) FILTER_ALL_DISTINCT>>
  drule_then (fn thm => simp[thm]) $ GSYM ALL_DISTINCT_CARD_LIST_TO_SET>>
  irule $ METIS_PROVE[] “s1 = s2 ⇒ CARD s1 = CARD s2”>>
  rw[GSYM list_set_eq,MEM_FILTER]>>
  metis_tac[]
QED

Theorem encode_n_value_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (NValue Xs Y)) ∧
  n_value_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_n_value bnd Xs Y name)
Proof
  rw[encode_n_value_def,n_value_sem_def]
  >-(
    rw[reify_some_eq_sem,reify_avar_def,reify_reif_def,reify_flag_def,MEM_MAP]>>
    metis_tac[])>>
  DEP_REWRITE_TAC[encode_bitsum_sem]>>
  simp[MAP_MAP_o]>>
  simp[o_DEF,iSUM_FILTER,reify_avar_def,reify_flag_def]>>
  DEP_REWRITE_TAC[subset_varc_union_dom,LENGTH_FILTER_subset]>>
  DEP_REWRITE_TAC[EVERY_MEM_union_dom,LENGTH_FILTER_subset]>>
  simp[]>>
  CONJ_TAC
  >-simp[GSYM ALL_DISTINCT_CARD_LIST_TO_SET,ALL_DISTINCT_union_dom]>>
  intLib.ARITH_TAC
QED

Theorem encode_n_value_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_n_value bnd Xs Y name) ⇒
  n_value_sem Xs Y wi
Proof
  strip_tac>>
  pop_assum mp_tac>>
  simp[encode_n_value_def,reify_some_eq_sem]>>
  DEP_REWRITE_TAC[encode_bitsum_sem]>>
  simp[MAP_MAP_o]>>
  rw[iSUM_FILTER,EVERY_MEM,
    METIS_PROVE[] “(∀x. P x ⇒ (Q x ∧ R x)) ⇔ (∀x. P x ⇒ Q x) ∧ (∀x. P x ⇒ R x)”]>>
  simp[n_value_sem_def]>>
  ‘LENGTH (FILTER (wb o elm name) (union_dom bnd Xs)) =
   CARD (set (MAP (varc wi) Xs))’ suffices_by intLib.ARITH_TAC>>
  DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]>>
  CONJ_TAC
  >-(
    irule FILTER_ALL_DISTINCT>>
    simp[ALL_DISTINCT_union_dom])>>
  CONG_TAC (SOME 1)>>
  simp[GSYM list_set_eq,MEM_FILTER,MEM_MAP]>>
  strip_tac>>
  iff_tac
  >-metis_tac[]>>
  strip_tac>>
  pure_rewrite_tac[Once $ METIS_PROVE[] “Q ∧ P ⇔ P ∧ (P ⇒ Q)”]>>
  CONJ_TAC
  >-(
    drule_then assume_tac EVERY_MEM_union_dom>>
    gs[EVERY_MEM])>>
  metis_tac[]
QED

Definition eqi_def[simp]:
  eqi name (i:num) ann =
    INR (name, Indices [i] (SOME ann))
End

Definition encode_count_def:
  encode_count bnd Xs (Y:'a varc) (Z:'a varc) name =
  FLAT (MAPi
    (λi X.
      let
        ge = eqi name i (strlit"ge");
        le = eqi name i (strlit"le");
        eq = eqi name i (strlit"eq")
      in
        bimply_bit bnd (Pos ge) (mk_ge X Y) ++
        bimply_bit bnd (Pos le) (mk_le X Y) ++
        bimply_bit bnd (Pos eq) ([],[(1i,Pos ge);(1i,Pos le)],2i)
    ) Xs) ++
  encode_bitsum (GENLIST (λi. eqi name i (strlit"eq")) (LENGTH Xs)) Z
End

Theorem encode_count_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (Count Xs Y Z)) ∧
  count_sem Xs Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_count bnd Xs Y Z name)
Proof
  rw[encode_count_def,count_sem_def]
  >-(
  rw[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,EVERY_APPEND]>>
  simp[iconstraint_sem_def,reify_avar_def,reify_flag_def]>>
  intLib.ARITH_TAC
  )>>
  drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
  cong_tac NONE>>
  simp[MAP_GENLIST,o_ABS_R,reify_avar_def,reify_flag_def,GENLIST_EL_MAP]
QED

(* unused theorems
Theorem iSUM_SNOC:
  ∀init last. iSUM (SNOC last init) = last + iSUM init
Proof
  Induct>>
  rw[iSUM_def,SNOC]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_GENLIST_lin_const:
  ∀n a. iSUM (GENLIST (λi. a * f i) n) = a * iSUM (GENLIST f n)
Proof
  Induct>>
  rw[iSUM_def,GENLIST,iSUM_SNOC]>>
  intLib.ARITH_TAC
QED
*)

Theorem encode_count_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_count bnd Xs Y Z name) ⇒
  count_sem Xs Y Z wi
Proof
  rw[encode_count_def,EVERY_FLAT]>>
  gs[Once EVERY_MEM,MEM_MAPi,SF DNF_ss,iconstraint_sem_def]>>
  drule_then (fn thm => gs[thm]) encode_bitsum_sem>>
  gs[MAP_GENLIST,o_ABS_R,count_sem_def]>>
  qmatch_asmsub_abbrev_tac ‘s1 = varc wi Z’>>
  qmatch_goalsub_abbrev_tac ‘varc wi Z = s2’>>
  ‘s1 = s2’ suffices_by simp[]>>
  unabbrev_all_tac>>
  cong_tac NONE>>
  rw[GENLIST_eq_MAP]>>
  cong_tac NONE>>
  res_tac>>
  cheat
QED

Definition eqij_def[simp]:
  eqij name (i:num) (j:num) ann =
    INR (name, Indices [i;j] (SOME ann))
End

(* Among: Y equals the number of times values from iS appear in Xs
   Y = Sum_i [Xs[i] ∈ iS] *)
Definition encode_among_def:
  encode_among bnd (Xs:'a varc list) (iS:int list) (Y:'a varc) name =
  FLAT (MAPi
    (λi X.
      FLAT (MAPi
        (λj v.
          let
            ge = eqij name i j (strlit"ge");
            le = eqij name i j (strlit"le");
            eq = eqij name i j (strlit"eq")
          in
            [
              bits_imply bnd [Pos ge] $ mk_ge X (INR v);
              bits_imply bnd [Neg ge] $ mk_lt X (INR v);
              bits_imply bnd [Pos le] $ mk_le X (INR v);
              bits_imply bnd [Neg le] $ mk_gt X (INR v);
              bits_imply bnd [Pos eq] ([],[(1i,Pos ge);(1i,Pos le)],2);
              bits_imply bnd [Neg eq] ([],[(1i,Neg ge);(1i,Neg le)],1)
            ]
        ) iS) ++
      let
        al1 = eqi name i (strlit"al1")
      in
        [
          bits_imply bnd [Pos al1]
            ([],MAPi (λj v. (1i,Pos $ eqij name i j (strlit"eq"))) iS,1);
          bits_imply bnd [Neg al1]
            ([],MAPi (λj v. (-1i,Pos $ eqij name i j (strlit"eq"))) iS,0)
        ]
    ) Xs) ++
  case Y of
    INL vY =>
      [
        ([(-1i,vY)],MAPi (λi X. (1i,Pos $ eqi name i (strlit"al1"))) Xs,0);
        ([(1i,vY)],MAPi (λi X. (-1i,Pos $ eqi name i (strlit"al1"))) Xs,0)
      ]
  | INR cY =>
      [
        ([],MAPi (λi X. (1i,Pos $ eqi name i (strlit"al1"))) Xs,cY);
        ([],MAPi (λi X. (-1i,Pos $ eqi name i (strlit"al1"))) Xs,-cY)
      ]
End

Theorem MAPi_EL_MAP[local]:
  ∀ls. MAPi (λi X. f $ EL i ls) ls = MAP f ls
Proof
  Induct>>
  rw[MAPi_def,MAP,o_ABS_L]
QED

Theorem encode_among_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (Among Xs iS Y)) ∧
  among_sem Xs iS Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_among bnd Xs iS Y name)
Proof
  rw[encode_among_def,among_sem_def,EVERY_MEM]>>
  gs[MEM_FLAT,MEM_MAPi,iconstraint_sem_def,
     reify_avar_def,reify_flag_def,varc_def,eval_lin_term_def,o_ABS_R]>>
  rpt intLib.ARITH_TAC
  >-(
    simp[b2i_alt]>>
    intLib.ARITH_TAC)
  >-(
    strip_tac>>
    irule pbc_encodeTheory.iSUM_ge_gen>>
    CONJ_TAC
    >-(
      rw[MEM_MAPi]>>
      simp[pbc_encodeTheory.b2i_ge_0])
    >-(
      rw[MEM_MAPi]>>
      gs[MEM_EL,PULL_EXISTS]>>
      rename1 ‘n < LENGTH iS’>>
      qexists ‘n’>>
      simp[b2i_def]))
  >-(
    strip_tac>>
    irule pbc_encodeTheory.iSUM_ge_0>>
    rw[MEM_MAPi]>>
    gs[MEM_EL,METIS_PROVE[] “P ⇒ ¬Q ⇔ Q ⇒ ¬P”])>>
  Cases_on ‘Y’>>
  gs[iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,
    iSUM_def,o_ABS_R,reify_avar_def,reify_flag_def,varc_def]>>
  simp[MAPi_EL_MAP,iSUM_MAP_lin_const]>>
  intLib.ARITH_TAC
QED

Theorem encode_among_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_among bnd Xs iS Y name) ⇒
  among_sem Xs iS Y wi
Proof
  rw[encode_among_def,EVERY_MEM,MEM_FLAT,MEM_MAPi,PULL_EXISTS,SF DNF_ss,
    bits_imply_sem]>>
  gs[iconstraint_sem_def]>>
  cheat
QED

Definition encode_counting_constr_def:
  encode_counting_constr bnd c name =
  case c of
    AllDifferent Xs => encode_all_different bnd Xs name
  | NValue Xs Y => encode_n_value bnd Xs Y name
  | Count Xs Y Z => encode_count bnd Xs Y Z name
  | Among Xs iS Y => encode_among bnd Xs iS Y name
End

Theorem encode_counting_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting c) ∧
  counting_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_counting_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_different_sem_1]
  >- metis_tac[encode_n_value_sem_1]
  >- metis_tac[encode_count_sem_1]
  >- metis_tac[encode_among_sem_1]
QED

Theorem encode_counting_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_counting_constr bnd c name) ⇒
  counting_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_different_sem_2]
  >- metis_tac[encode_n_value_sem_2]
  >- metis_tac[encode_count_sem_2]
  >- metis_tac[encode_among_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_counting_constr_def:
  cencode_counting_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_counting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_counting_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_counting_constr bnd c name) ec ec'
Proof
  cheat
QED
