(*
   General-purpose list lemmas (LIST_REL, EVERY, ALOOKUP, MAP, FILTER,
   GENLIST, ZIP, LUPDATE, DROP/TAKE, SNOC, FLAT, REPLICATE, SORTED,
   PERM, enumerate, find_index, etc.) used throughout the CakeML development.
*)
Theory listLemmas
Ancestors
  arithLemmas alist bag container list rich_list indexedLists sorting
  arithmetic pred_set pair option combin relation string sptree finite_map
Libs
  boolSimps mp_then dep_rewrite BasicProvers

val _ = numLib.temp_prefer_num();

Theorem DROP_NIL:
  ∀n xs. DROP n xs = [] ⇔ LENGTH xs ≤ n
Proof
  Induct \\ Cases_on `xs` \\ fs [DROP_def]
QED

Theorem revdroprev:
   ∀l n.
     n ≤ LENGTH l ⇒ (REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH l - n) l)
Proof
  fs [GSYM BUTLASTN_def,BUTLASTN_TAKE]
QED

Theorem revtakerev:
   ∀n l. n ≤ LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l
Proof
  Induct >> simp[DROP_LENGTH_NIL] >>
  qx_gen_tac `l` >>
  `l = [] ∨ ∃f e. l = SNOC e f` by metis_tac[SNOC_CASES] >> simp[] >>
  simp[DROP_APPEND1]
QED

(* instant derivation from LIST_EQ_REWRITE *)
Theorem GENLIST_eq_MAP:
   GENLIST f n = MAP g ls ⇔
   LENGTH ls = n ∧ ∀m. m < n ⇒ f m = g (EL m ls)
Proof
  srw_tac[][LIST_EQ_REWRITE,EQ_IMP_THM,EL_MAP]
QED

(* TODO - already in HOL as ZIP_GENLIST *)
Theorem ZIP_GENLIST1:
   ∀l f n. LENGTH l = n ⇒ ZIP (GENLIST f n,l) = GENLIST (λx. (f x, EL x l)) n
Proof
  Induct \\ rw[] \\ rw[GENLIST_CONS,o_DEF]
QED

(* MAP3 never used *)
Definition MAP3_def[simp]:
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)
End

val MAP3_ind = theorem"MAP3_ind";

Theorem LENGTH_MAP3[simp]:
   ∀f l1 l2 l3. LENGTH l1 = LENGTH l3 /\ LENGTH l2 = LENGTH l3 ⇒ LENGTH (MAP3 f l1 l2 l3) = LENGTH l3
Proof
  ho_match_mp_tac MAP3_ind \\ rw[]
QED

Theorem EL_MAP3:
   ∀f l1 l2 l3 n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ n < LENGTH l3 ⇒
    EL n (MAP3 f l1 l2 l3) = f (EL n l1) (EL n l2) (EL n l3)
Proof
  ho_match_mp_tac MAP3_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]
QED

(* used once *)
Theorem MAP_REVERSE_STEP:
   ∀x f. x ≠ [] ⇒ MAP f (REVERSE x) = f (LAST x) :: MAP f (REVERSE (FRONT x))
Proof
  recInduct SNOC_INDUCT
  \\ rw [FRONT_APPEND]
QED

Theorem LENGTH_TAKE_EQ_MIN:
   !n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)
Proof
  simp[LENGTH_TAKE_EQ] \\ full_simp_tac(srw_ss())[MIN_DEF] \\ decide_tac
QED

(* should be switched in orientation *)
Theorem LIST_REL_MEM:
   !xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys
Proof
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]
QED

(* only used in theorem immediately below *)
Theorem LIST_REL_GENLIST_I:
   !xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)
Proof
  simp[LIST_REL_EL_EQN]
QED

(* only used in bvi_to_dataProof *)
Theorem LIST_REL_lookup_fromList:
   LIST_REL (\v x. lookup v (fromList args) = SOME x)
     (GENLIST I (LENGTH args)) args
Proof
  SIMP_TAC std_ss [lookup_fromList,LIST_REL_GENLIST_I]
QED

Theorem LIST_REL_lookup_fromList_MAP:
   LIST_REL (λv x. ∃z. lookup v (fromList args) = SOME z ∧ x = f z)
    (GENLIST I (LENGTH args)) (MAP f args)
Proof
  fs [LIST_REL_MAP2,LIST_REL_GENLIST_I,lookup_fromList]
QED

(* only used in examples/stackProg; oriented badly *)
Theorem LIST_REL_FRONT_LAST:
   l1 <> [] /\ l2 <> [] ==>
    (LIST_REL A l1 l2 <=>
     LIST_REL A (FRONT l1) (FRONT l2) /\ A (LAST l1) (LAST l2))
Proof
  map_every
    (fn q => Q.ISPEC_THEN q FULL_STRUCT_CASES_TAC SNOC_CASES >>
             fs[LIST_REL_SNOC])
    [`l1`,`l2`]
QED

Theorem SPLIT_LIST:
   !xs.
      ?ys zs. (xs = ys ++ zs) /\
              (LENGTH xs DIV 2 = LENGTH ys)
Proof
  REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`TAKE (LENGTH xs DIV 2) xs`,`DROP (LENGTH xs DIV 2) xs`]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[TAKE_DROP]
  \\ MATCH_MP_TAC (GSYM LENGTH_TAKE)
  \\ full_simp_tac(srw_ss())[DIV_LE_X] \\ DECIDE_TAC
QED

Theorem EXISTS_ZIP:
   !l f. EXISTS (\(x,y). f x) l = EXISTS f (MAP FST l)
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []
QED

Theorem EVERY_ZIP:
   !l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []
QED

Theorem every_zip_split:
   !l1 l2 P Q.
    LENGTH l1 = LENGTH l2 ⇒
    (EVERY (\(x,y). P x ∧ Q y) (ZIP (l1, l2)) ⇔ EVERY P l1 ∧ EVERY Q l2)
Proof
 Induct_on `l1`
 >> simp []
 >> Cases_on `l2`
 >> rw []
 >> metis_tac []
QED

Theorem every_shim:
 !l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)
Proof
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw []
QED

Theorem every_shim2:
 !l P Q. EVERY (\(x,y). P x ∧ Q y) l = (EVERY (\x. P (FST x)) l ∧ EVERY (\x. Q (SND x)) l)
Proof
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw [] >>
metis_tac []
QED

Theorem MEM_ZIP2:
    ∀l1 l2 x.
  MEM x (ZIP (l1,l2)) ⇒
  ∃n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ x = (EL n l1,EL n l2)
Proof
  Induct>>fs[ZIP_def]>>
  Cases_on`l2`>>fs[ZIP_def]>>
  rw[]
  >-
    (qexists_tac`0n`>>fs[])
  >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))>>
    rw[]>>
    qexists_tac`SUC n`>>fs[]
QED

Theorem ZIP_MAP_FST_SND_EQ:
   ∀ls. ZIP (MAP FST ls,MAP SND ls) = ls
Proof
  Induct>>full_simp_tac(srw_ss())[]
QED

Theorem MAP_FST_I_PAIR_MAP[simp]:
   !xs. MAP FST (MAP (I ## f) xs) = MAP FST xs
Proof
  Induct \\ fs [FORALL_PROD]
QED

Theorem EVERY_FST_SND:
   EVERY (λ(a,b). P a ∧ Q b) ls ⇔ EVERY P (MAP FST ls) ∧ EVERY Q (MAP SND ls)
Proof
  rw[EVERY_MEM,MEM_MAP,UNCURRY,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac[]
QED

(*TODO upstream*)
Theorem MAX_LIST_APPEND[simp]:
   MAX_LIST (xs++ys) = MAX (MAX_LIST xs) (MAX_LIST ys)
Proof
  Induct_on `xs` >> simp[AC MAX_COMM MAX_ASSOC]
QED

(*Or should it be MAX x (MAX_LIST xs)*)
Theorem MAX_LIST_SNOC[simp]:
   MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x
Proof
  simp[SNOC_APPEND]
QED

Theorem MAX_LIST_intro:
  ∀ls.
  P 0 ∧ EVERY P ls ⇒ P (MAX_LIST ls)
Proof
  Induct>>rpt strip_tac >>
  full_simp_tac(srw_ss())[MAX_DEF,COND_RAND]
QED

Theorem MAX_LIST_max:
  ∀ls. EVERY (λx. x ≤ MAX_LIST ls) ls
Proof
  rw[EVERY_MEM] >> irule MAX_LIST_PROPERTY >> fs[]
QED

Theorem FOLDR_MAX_0_MAX_LIST:
  ∀ls. FOLDR MAX 0 ls = MAX_LIST ls
Proof
  Induct \\ rw[MAX_DEF]
QED

(* never used *)
Definition list_inter_def:
  list_inter xs ys = FILTER (\y. MEM y xs) ys
End

Theorem ALOOKUP_SNOC:
   ∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE
Proof
  Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][]
QED

Theorem ALOOKUP_GENLIST:
   ∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE
Proof
  gen_tac >> Induct >> simp[GENLIST] >> srw_tac[][] >> full_simp_tac(srw_ss())[ALOOKUP_SNOC] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][]
QED

Theorem ALOOKUP_ZIP_FAIL:
   ∀A B x.
  LENGTH A = LENGTH B ⇒
  (ALOOKUP (ZIP (A,B)) x = NONE ⇔ ¬MEM x A)
Proof
  srw_tac[][]>>Q.ISPECL_THEN [`ZIP(A,B)`,`x`] assume_tac ALOOKUP_NONE >>
  full_simp_tac(srw_ss())[MAP_ZIP]
QED

Theorem MEM_ALOOKUP:
   !xs x v.
      ALL_DISTINCT (MAP FST xs) ==>
      (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ eq_tac \\ rw [] \\ rfs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []
QED

(* TODO - candidate for move to HOL, but in simpler form without accumulator *)
(* only used in inferProg *)
Definition anub_def:
  (anub [] acc = []) ∧
  (anub ((k,v)::ls) acc =
   if MEM k acc then anub ls acc else
   (k,v)::(anub ls (k::acc)))
End

val anub_ind = theorem"anub_ind"

Theorem EVERY_anub_imp:
   ∀ls acc x y.
      EVERY P (anub ((x,y)::ls) acc) ∧ x ∉ set acc
      ⇒
      P (x,y) ∧ EVERY P (anub ls (x::acc))
Proof
  ho_match_mp_tac anub_ind >> srw_tac[][anub_def] >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
QED

(* terrible rewrite *)
Theorem ALOOKUP_anub:
   ALOOKUP (anub ls acc) k =
    if MEM k acc then ALOOKUP (anub ls acc) k
    else ALOOKUP ls k
Proof
  qid_spec_tac`acc` >>
  Induct_on`ls` >>
  srw_tac[][anub_def] >>
  Cases_on`h`>>srw_tac[][anub_def]>>full_simp_tac(srw_ss())[] >- (
    first_x_assum(qspec_then`acc`mp_tac) >>
    srw_tac[][] ) >>
  first_x_assum(qspec_then`q::acc`mp_tac) >>
  srw_tac[][]
QED

Theorem anub_eq_nil:
   anub x y = [] ⇔ EVERY (combin$C MEM y) (MAP FST x)
Proof
  qid_spec_tac`y` >>
  Induct_on`x`>>srw_tac[][anub_def]>>
  Cases_on`h`>>srw_tac[][anub_def]
QED

Theorem EVERY_anub_suff:
   ∀ls acc.
    (∀x. ¬MEM x acc ⇒ case ALOOKUP ls x of SOME v => P (x,v) | NONE => T)
    ⇒ EVERY P (anub ls acc)
Proof
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >- (
    first_x_assum(match_mp_tac) >>
    srw_tac[][] >>
    res_tac >>
    pop_assum mp_tac >> IF_CASES_TAC >> full_simp_tac(srw_ss())[] )
  >- (
    res_tac >> full_simp_tac(srw_ss())[] ) >>
  first_x_assum match_mp_tac >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  `q ≠ x` by full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[]
QED

Theorem anub_notin_acc:
   ∀ls acc. MEM x acc ⇒ ¬MEM x (MAP FST (anub ls acc))
Proof
  Induct >> simp[anub_def] >>
  Cases >> simp[anub_def] >> srw_tac[][] >>
  metis_tac[]
QED

Theorem anub_tl_anub:
   ∀x y h t. anub x y = h::t ⇒ ∃a b. t = anub a b ∧ set a ⊆ set x ∧ set b ⊆ set ((FST h)::y)
Proof
  Induct >> srw_tac[][anub_def] >>
  Cases_on`h`>>full_simp_tac(srw_ss())[anub_def] >>
  pop_assum mp_tac  >> srw_tac[][] >>
  res_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[SUBSET_DEF] >>
  metis_tac[MEM]
QED

Theorem anub_all_distinct_keys:
   ∀ls acc.
    ALL_DISTINCT acc ⇒
    ALL_DISTINCT ((MAP FST (anub ls acc)) ++ acc)
Proof
  Induct>>srw_tac[][anub_def]>>PairCases_on`h`>>full_simp_tac(srw_ss())[anub_def]>>
  srw_tac[][]>>
  `ALL_DISTINCT (h0::acc)` by full_simp_tac(srw_ss())[ALL_DISTINCT]>>res_tac>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_APPEND]>>
  metis_tac[]
QED

Theorem MEM_anub_ALOOKUP:
   MEM (k,v) (anub ls []) ⇒
    ALOOKUP ls k = SOME v
Proof
  srw_tac[][]>>
  Q.ISPECL_THEN[`ls`,`[]`] assume_tac anub_all_distinct_keys>>
  Q.ISPECL_THEN [`ls`,`k`,`[]`] assume_tac (GEN_ALL ALOOKUP_anub)>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM]
QED

Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
val _ = Parse.add_infix("=++",500,Parse.LEFT)

Overload "=++" = ``UPDATE_LIST``

Theorem UPDATE_LIST_THM:
   ∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)
Proof
  srw_tac[][UPDATE_LIST_def,pairTheory.UNCURRY]
QED

Theorem APPLY_UPDATE_LIST_ALOOKUP:
   ∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y
Proof
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  srw_tac[][] >> BasicProvers.CASE_TAC
QED

(* should be using indexedLists$findi, or INDEX_OF *)
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End

Theorem INDEX_FIND_CONS_EQ_SOME:
   (INDEX_FIND n f (x::xs) = SOME y) <=>
    (f x /\ (y = (n,x))) \/
    (~f x /\ (INDEX_FIND (n+1) f xs = SOME y))
Proof
  fs [INDEX_FIND_def] \\ rw [] \\ Cases_on `y` \\ fs [ADD1] \\ metis_tac []
QED

Theorem find_index_INDEX_FIND:
   ∀y xs n. find_index y xs n = OPTION_MAP FST (INDEX_FIND n ($= y) xs)
Proof
  Induct_on`xs` \\ rw[find_index_def]
  \\ rw[Once INDEX_FIND_def,ADD1]
QED

Theorem find_index_INDEX_OF:
   find_index y xs 0 = INDEX_OF y xs
Proof
  rw[INDEX_OF_def,find_index_INDEX_FIND]
QED

Theorem find_index_NOT_MEM:
   ∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)
Proof
  Induct >> srw_tac[][find_index_def]>>
  metis_tac[]
QED

Theorem find_index_MEM:
   !ls x n. MEM x ls ==> ?i. (find_index x ls n = SOME (n+i)) /\ i < LENGTH ls /\ (EL i ls = x)
Proof
  Induct >> srw_tac[][find_index_def] >>
  first_x_assum(qspecl_then[`x`,`n+1`]mp_tac) >>
  srw_tac[][]>>qexists_tac`SUC i`>>srw_tac[ARITH_ss][ADD1]
QED

Theorem find_index_LEAST_EL:
   ∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE
Proof
  Induct >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>full_simp_tac(srw_ss())[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> srw_tac[][]) >>
    Cases >> srw_tac[][] >>
    qexists_tac`0` >>simp[])>>
  srw_tac[][] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[MEM_EL,MEM] >>
  srw_tac[][] >>
  Cases_on`n`>>full_simp_tac(srw_ss())[ADD1] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  srw_tac[][] >>
  qmatch_rename_tac`m = n` >>
  Cases_on`m < n` >- (res_tac >> full_simp_tac(srw_ss())[]) >>
  Cases_on`n < m` >- (
    `n + 1 < m + 1` by DECIDE_TAC >>
    res_tac >> full_simp_tac(srw_ss())[GSYM ADD1] ) >>
  DECIDE_TAC
QED

Theorem find_index_LESS_LENGTH:
 ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)
Proof
Induct >> srw_tac[][find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1]
QED

Theorem ALOOKUP_find_index_NONE:
   (ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)
Proof
  srw_tac[][ALOOKUP_FAILS] >>
  srw_tac[][GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD]
QED

val ALOOKUP_find_index_SOME = Q.prove(
  `∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >>
  srw_tac[][find_index_def] >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]

Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))
Proof
  srw_tac[][] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> full_simp_tac(srw_ss())[EL_MAP]
QED

Theorem find_index_ALL_DISTINCT_EL[simp]:
 ∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))
Proof
Induct >- srw_tac[][] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL]
QED

Theorem find_index_ALL_DISTINCT_EL_eq:
   ∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)
Proof
  srw_tac[][EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    full_simp_tac(srw_ss())[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    full_simp_tac(srw_ss())[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL]
QED

Theorem find_index_APPEND_same:
   !l1 n m i l2. (find_index n l1 m = SOME i) ==> (find_index n (l1 ++ l2) m = SOME i)
Proof
  Induct >> srw_tac[][find_index_def]
QED

Theorem find_index_ALL_DISTINCT_REVERSE:
   ∀ls x m j. ALL_DISTINCT ls ∧ (find_index x ls m = SOME j) ⇒ (find_index x (REVERSE ls) m = SOME (m + LENGTH ls + m - j - 1))
Proof
  srw_tac[][] >> imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
  `ALL_DISTINCT (REVERSE ls)` by srw_tac[][ALL_DISTINCT_REVERSE] >>
  simp[find_index_ALL_DISTINCT_EL_eq] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >> srw_tac[][] >>
  qmatch_assum_rename_tac`z < LENGTH ls` >>
  qexists_tac`LENGTH ls - z - 1` >>
  lrw[EL_REVERSE,PRE_SUB1]
QED

Theorem THE_find_index_suff:
   ∀P x ls n. (∀m. m < LENGTH ls ⇒ P (m + n)) ∧ MEM x ls ⇒
    P (THE (find_index x ls n))
Proof
  srw_tac[][] >>
  imp_res_tac find_index_MEM >>
  pop_assum(qspec_then`n`mp_tac) >>
  srw_tac[DNF_ss,ARITH_ss][]
QED

Theorem find_index_APPEND1:
   ∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (i < m+LENGTH l1) ⇒ (find_index n l1 m = SOME i)
Proof
  Induct >> simp[find_index_def] >- (
    spose_not_then strip_assume_tac >>
    imp_res_tac find_index_LESS_LENGTH >>
    DECIDE_TAC ) >>
  srw_tac[][] >> res_tac >>
  first_x_assum match_mp_tac >>
  simp[]
QED

Theorem find_index_APPEND2:
   ∀l1 n l2 m i. (find_index n (l1 ++ l2) m = SOME i) ∧ (m + LENGTH l1 ≤ i) ⇒ (find_index n l2 (m+LENGTH l1) = SOME i)
Proof
  Induct >> simp[find_index_def] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1]
QED

Theorem find_index_is_MEM:
   ∀x ls n j. (find_index x ls n = SOME j) ⇒ MEM x ls
Proof
  metis_tac[find_index_NOT_MEM,optionTheory.NOT_SOME_NONE]
QED

Theorem find_index_MAP_inj:
   ∀ls x n f. (∀y. MEM y ls ⇒ (f x = f y) ⇒ x = y) ⇒ (find_index (f x) (MAP f ls) n = find_index x ls n)
Proof
  Induct >- simp[find_index_def] >>
  srw_tac[][] >> srw_tac[][find_index_def] >>
  metis_tac[]
QED

Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)
Proof
  Induct >> simp_tac(srw_ss())[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x` >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] ) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[] >>
  strip_tac >>
  first_assum(qspecl_then[`x`,`k+1`]mp_tac) >>
  first_x_assum(qspecl_then[`x`,`1`]mp_tac) >>
  srw_tac[][] >>
  Cases_on`find_index x ls 0`>>srw_tac[][] >>
  simp[]
QED

Theorem find_index_shift:
   ∀ls x k j. (find_index x ls k = SOME j) ⇒ j ≥ k ∧ ∀n. find_index x ls n = SOME (j-k+n)
Proof
  Induct >> simp[find_index_def] >> srw_tac[][] >> res_tac >> fsrw_tac[ARITH_ss][]
QED

Theorem find_index_APPEND:
   ∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x
Proof
  Induct >> simp[find_index_def] >> srw_tac[][] >>
  BasicProvers.CASE_TAC >>
  simp[arithmeticTheory.ADD1]
QED

Theorem find_index_in_FILTER_ZIP_EQ:
   ∀P l1 l2 x n1 n2 v1 j1 j2.
      (LENGTH l1 = LENGTH v1) ∧
      (FILTER (P o FST) (ZIP(l1,v1)) = l2) ∧
      (find_index x l1 n1 = SOME (n1+j1)) ∧
      (find_index x (MAP FST l2) n2 = SOME (n2+j2)) ∧
      P x
      ⇒
      j1 < LENGTH l1 ∧ j2 < LENGTH l2 ∧
      (EL j1 (ZIP(l1,v1)) = EL j2 l2)
Proof
  gen_tac >> Induct >> simp[find_index_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >- (
    strip_tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`j1`>>fsrw_tac[ARITH_ss][]>>
    full_simp_tac(srw_ss())[find_index_def] >>
    Cases_on`j2`>>fsrw_tac[ARITH_ss][] >>
    Cases_on`v1`>>fsrw_tac[ARITH_ss][find_index_def]) >>
  strip_tac >>
  Cases_on`v1`>>full_simp_tac(srw_ss())[] >>
  Cases_on`P h`>>full_simp_tac(srw_ss())[find_index_def] >- (
    rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`n2+1`,`t`]mp_tac) >> simp[] >>
    Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`j2=0`>>fsrw_tac[ARITH_ss][]>>
    disch_then(qspecl_then[`PRE j1`,`PRE j2`]mp_tac) >>
    simp[rich_listTheory.EL_CONS] ) >>
  first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`n2`,`t`]mp_tac) >> simp[] >>
  imp_res_tac find_index_LESS_LENGTH >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
  disch_then(qspec_then`PRE j1`mp_tac) >>
  simp[rich_listTheory.EL_CONS]
QED

Theorem ALL_DISTINCT_PERM_ALOOKUP_ZIP:
   ∀l1 l2 l3. ALL_DISTINCT (MAP FST l1) ∧ PERM (MAP FST l1) l2
    ⇒ (set l1 = set (ZIP (l2, MAP (THE o ALOOKUP (l1 ++ l3)) l2)))
Proof
  srw_tac[][EXTENSION,FORALL_PROD,EQ_IMP_THM] >- (
    qmatch_assum_rename_tac`MEM (x,y) l1` >>
    imp_res_tac PERM_LENGTH >> full_simp_tac(srw_ss())[] >>
    simp[MEM_ZIP] >>
    imp_res_tac MEM_PERM >>
    full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD] >>
    `MEM x l2` by metis_tac[] >>
    `∃m. m < LENGTH l2 ∧ (x = EL m l2)` by metis_tac[MEM_EL] >>
    qexists_tac`m`>>simp[]>>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
    srw_tac[][ALOOKUP_APPEND] ) >>
  qmatch_rename_tac`MEM (x,y) l1` >>
  imp_res_tac PERM_LENGTH >>
  full_simp_tac(srw_ss())[MEM_ZIP] >>
  simp[EL_MAP] >>
  imp_res_tac MEM_PERM >>
  full_simp_tac(srw_ss())[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  impl_tac >- simp[] >>
  disch_then(Q.X_CHOOSE_THEN`m`strip_assume_tac) >>
  qexists_tac`m` >>
  simp[EL_MAP] >>
  Cases_on`EL m l1`>>simp[ALOOKUP_APPEND] >>
  BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_FAILS >>
    metis_tac[MEM_EL] ) >>
  metis_tac[MEM_EL,ALOOKUP_ALL_DISTINCT_MEM,optionTheory.THE_DEF]
QED

(* surely better with UNZIP rather than ZIP *)
Theorem PERM_ZIP:
   ∀l1 l2. PERM l1 l2 ⇒ ∀a b c d. (l1 = ZIP(a,b)) ∧ (l2 = ZIP(c,d)) ∧ (LENGTH a = LENGTH b) ∧ (LENGTH c = LENGTH d) ⇒
    PERM a c ∧ PERM b d
Proof
  ho_match_mp_tac PERM_IND >>
  conj_tac >- (
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] >>
    Cases >> simp[LENGTH_NIL_SYM] ) >>
  conj_tac >- (
    Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    metis_tac[PERM_MONO]) >>
  conj_tac >- (
    ntac 2 Cases >> rpt gen_tac >> strip_tac >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    Cases>>simp[LENGTH_NIL_SYM] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_rename_tac`LENGTH a = LENGTH b` >>
    pop_assum mp_tac >>
    qmatch_assum_rename_tac`LENGTH c = LENGTH d` >>
    strip_tac >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`b`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`c`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    Cases_on`d`>>full_simp_tac(srw_ss())[LENGTH_NIL_SYM]>>
    metis_tac[PERM_SWAP_AT_FRONT] ) >>
  assume_tac (GSYM ZIP_MAP_FST_SND_EQ)>>
  gen_tac >> qx_gen_tac`ll` >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`a`,`b`,`MAP FST ll`,`MAP SND ll`]mp_tac) >>
  simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`MAP FST ll`,`MAP SND ll`,`c`,`d`]mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[PERM_TRANS]
QED

Theorem PERM_PART:
   ∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)
Proof
  GEN_TAC THEN Induct >>
  simp[PART_DEF] >> srw_tac[][] >- (
    first_x_assum(qspecl_then[`h::l1`,`l2`,`p`,`q`]mp_tac) >>
    simp[] >>
    REWRITE_TAC[Once CONS_APPEND] >>
    strip_tac >>
    REWRITE_TAC[Once CONS_APPEND] >>
    full_simp_tac std_ss [APPEND_ASSOC] >>
    metis_tac[PERM_REWR,PERM_APPEND] ) >>
  first_x_assum(qspecl_then[`l1`,`h::l2`,`p`,`q`]mp_tac) >>
  simp[] >>
  REWRITE_TAC[Once CONS_APPEND] >>
  strip_tac >>
  REWRITE_TAC[Once CONS_APPEND] >>
  full_simp_tac std_ss [APPEND_ASSOC] >>
  metis_tac[PERM_REWR,PERM_APPEND,APPEND_ASSOC]
QED

Theorem PERM_PARTITION:
   ∀P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)
Proof
  METIS_TAC[PERM_PART,PARTITION_DEF,APPEND_NIL]
QED

Theorem option_case_NONE_F:
   (case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)
Proof
  Cases_on`X`>>srw_tac[][]
QED

Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)
Proof
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] )
QED

Theorem EVERY2_RC_same[simp]:
   EVERY2 (RC R) l l
Proof
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF]
QED

(* used twice, and only in source_to_flatProof *)
Theorem FOLDL_invariant:
   !P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)
Proof
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][]
QED

(* never used *)
Theorem FOLDL_invariant_rest:
   ∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)
Proof
  ntac 2 gen_tac >>
  Induct >> srw_tac[][] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> srw_tac[][] ) >>
  srw_tac[][] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> srw_tac[][]
QED

(* Re-expressing folds *)

(* only used in flat_elimProof *)
Theorem FOLDR_CONS_triple:
 !f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a
Proof
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][]
QED

(* never used *)
Theorem FOLDR_CONS_5tup:
 !f ls a. FOLDR (\(c,d,x,y,z) w. f c d x y z :: w) a ls = (MAP (\(c,d,x,y,z). f c d x y z) ls)++a
Proof
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][]
QED

(* never used *)
Theorem FOLDR_transitive_property:
 !P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)
Proof
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][]
QED

(* Re-expressing curried lambdas *)

Theorem FST_triple:
 (λ(n,ns,b). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem FST_5tup:
 (λ(n,ns,b,x,y). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_triple:
 (λ(n,ns,b). f ns b) = UNCURRY f o SND
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

Theorem FST_pair:
 (λ(n,v). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_pair:
 (λ(n,v). v) = SND
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_FST_pair:
 (λ((n,m),c).m) = SND o FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem MAP_ZIP_SND_triple:
 (LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)
Proof
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC)
QED

Theorem MAP_EQ_ID:
 !f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))
Proof
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM]
QED

Theorem map_fst:
 !l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l
Proof
Induct_on `l` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[]
QED

(* use INJ_MAP_EQ_IFF and INJ_DEF *)
Theorem map_some_eq:
 !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2)
Proof
 Induct_on `l1` >>
 srw_tac[][] >>
 Cases_on `l2` >>
 srw_tac[][]
QED

(* never used *)
Theorem map_some_eq_append:
 !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3)
Proof
metis_tac [map_some_eq, MAP_APPEND]
QED

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];

Theorem LASTN_LEMMA:
   (LASTN (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LASTN (LENGTH xs + 1) (x::xs) = x::xs)
Proof
  MP_TAC (Q.SPEC `x::y::xs` LASTN_LENGTH_ID)
  \\ MP_TAC (Q.SPEC `x::xs` LASTN_LENGTH_ID) \\ full_simp_tac(srw_ss())[ADD1]
QED

Theorem LASTN_TL =
  LASTN_CONS |> Q.SPECL[`n+1`,`xs`]
  |> C MP (DECIDE``n < LENGTH xs ⇒ n + 1 ≤ LENGTH xs`` |> UNDISCH)
  |> SPEC_ALL |> DISCH_ALL

Theorem LASTN_LENGTH_LESS_EQ:
   !xs n. LENGTH xs <= n ==> LASTN n xs = xs
Proof
  full_simp_tac(srw_ss())[LASTN_def] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [listTheory.TAKE_LENGTH_TOO_LONG] \\ full_simp_tac(srw_ss())[]
QED

Theorem LASTN_ALT:
   (LASTN n [] = []) /\
    (LASTN n (x::xs) = if LENGTH (x::xs) <= n then x::xs else LASTN n xs)
Proof
  srw_tac[][] THEN1 (full_simp_tac(srw_ss())[LASTN_def])
  THEN1 (match_mp_tac LASTN_LENGTH_LESS_EQ \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[LASTN_def] \\ REPEAT STRIP_TAC
  \\ `n <= LENGTH (REVERSE xs)` by (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ imp_res_tac TAKE_APPEND1 \\ full_simp_tac(srw_ss())[]
QED

Theorem LENGTH_LASTN_LESS:
   !xs n. LENGTH (LASTN n xs) <= LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `n` assume_tac)
  \\ decide_tac
QED

Theorem MAP_EQ_MAP_IMP:
   !xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys)
Proof
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [MAP] \\ METIS_TAC []
QED

Theorem INJ_MAP_EQ_2:
   ∀f l1 l2.
   (∀x y. x ∈ set l1 ∧ y ∈ set l2 ∧ f x = f y ⇒ x = y) ∧
   MAP f l1 = MAP f l2 ⇒
   l1 = l2
Proof
  gen_tac \\ Induct \\ rw[]
  \\ Cases_on`l2` \\ pop_assum mp_tac \\ rw[]
QED

Theorem LENGTH_EQ_FILTER_FILTER:
   !xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))
Proof
  Induct \\ SIMP_TAC std_ss [LENGTH,FILTER,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_CLAUSES]
QED

Theorem LIST_REL_MAP_FILTER_NEQ:
   ∀P f1 f2 z1 z2 l1 l2.
      LIST_REL P (MAP f1 l1) (MAP f2 l2) ∧
      (∀y1 y2. MEM (y1,y2) (ZIP(l1,l2)) ⇒ (SND y1 ≠ z1 ⇔ SND y2 ≠ z2) ∧ (P (f1 y1) (f2 y2)))
      ⇒
      LIST_REL P (MAP f1 (FILTER (λ(x,y). y ≠ z1) l1)) (MAP f2 (FILTER (λ(x,y). y ≠ z2) l2))
Proof
  ntac 5 gen_tac >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases >> simp[] >>
  strip_tac >>
  Cases_on`h`>>fs[] >> rw[] >>
  METIS_TAC[SND]
QED

Theorem EVERY_LAST:
   !P l. l ≠ [] /\ EVERY P l ==> P (LAST l)
Proof
  rw [LAST_EL, EVERY_EL, NOT_NIL_EQ_LENGTH_NOT_0]
QED

Theorem MAPi_ID[simp]:
   MAPi (\x y. y) = I
Proof
  fs [FUN_EQ_THM] \\ Induct \\ fs [o_DEF]
QED

(* TODO - candidate for move to HOL *)
Definition enumerate_def:
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)
End

(* TODO - candidate for move to HOL *)
Theorem LENGTH_enumerate:
    ∀xs k. LENGTH (enumerate k xs) = LENGTH xs
Proof
  Induct>>fs[enumerate_def]
QED

Theorem EL_enumerate:
    ∀xs n k.
  n < LENGTH xs ⇒
  EL n (enumerate k xs) = (n+k,EL n xs)
Proof
  Induct>>fs[enumerate_def]>>rw[]>>
  Cases_on`n`>>fs[]
QED

Theorem MAP_enumerate_MAPi:
    ∀f xs.
  MAP f (enumerate 0 xs) = MAPi (λn e. f (n,e)) xs
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate]
QED

Theorem MAPi_enumerate_MAP:
    ∀f xs.
  MAPi f xs = MAP (λi,e. f i e) (enumerate 0 xs)
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate]
QED

Theorem MEM_enumerate:
    ∀xs i e.
  i < LENGTH xs ⇒
  (MEM (i,e) (enumerate 0 xs) ⇔ EL i xs = e)
Proof
  fs[MEM_EL]>>rw[]>>eq_tac>>rw[LENGTH_enumerate]>>
  imp_res_tac EL_enumerate>>fs[]>>
  qexists_tac`i`>>fs[]
QED

Theorem MEM_enumerate_IMP:
  ∀ls k.
  MEM (i,e) (enumerate k ls) ⇒ MEM e ls
Proof
  Induct_on`ls`>>fs[enumerate_def]>>rw[]>>
  metis_tac[]
QED

Theorem MAP_FST_enumerate:
  MAP FST (enumerate k ls) = GENLIST ($+ k) (LENGTH ls)
Proof
  rw[LIST_EQ_REWRITE,LENGTH_enumerate]>>
  simp[EL_MAP,LENGTH_enumerate,EL_enumerate]
QED

Theorem ALL_DISTINCT_MAP_FST_enumerate:
  ALL_DISTINCT (MAP FST (enumerate k ls))
Proof
  simp[MAP_FST_enumerate,ALL_DISTINCT_GENLIST]
QED

Theorem ALOOKUP_enumerate:
  ∀ls k x.
  ALOOKUP (enumerate k ls) x =
  if k ≤ x ∧ x < LENGTH ls + k then SOME (EL (x-k) ls) else NONE
Proof
  Induct>>rw[enumerate_def]>>
  `x-k = SUC(x-(k+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem SUM_MAP_LENGTH_REPLICATE:
   ∀n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls
Proof
  Induct >> simp[REPLICATE,MULT]
QED

Theorem SUM_MAP_COUNT_LIST:
   !n k. SUM (MAP ($+ k) (COUNT_LIST n)) = (n * (2 * k + n - 1)) DIV 2
Proof
  Induct \\ rw [COUNT_LIST_def]
  \\ `!xs. MAP SUC xs = MAP ($+ 1) xs` by (Induct \\ rw [])
  \\ pop_assum (qspec_then `COUNT_LIST n` SUBST1_TAC)
  \\ pop_assum (qspec_then `k + 1` mp_tac)
  \\ simp [MAP_MAP_o, o_DEF]
  \\ `$+ (k + 1) = \x. k + (x + 1)` by fs [FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC \\ rw [ADD1]
  \\ fs [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
  \\ metis_tac [ADD_DIV_ADD_DIV, MULT_COMM, DECIDE ``0n < 2``]
QED

Theorem SUM_REPLICATE:
   ∀n m. SUM (REPLICATE n m) = n * m
Proof
  Induct \\ simp[REPLICATE,ADD1]
QED

Theorem SUM_MAP_BOUND:
    (∀x. f x ≤ c) ⇒ (SUM (MAP f ls) ≤ LENGTH ls * c)
Proof
  rw[]>> Induct_on`ls` >>rw[MULT_SUC]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  DECIDE_TAC
QED

Theorem SUM_MOD:
    k > 0 ⇒
  (SUM ls MOD k = (SUM (MAP (λn. n MOD k) ls)) MOD k)
Proof
  Induct_on`ls`>>rw[]>>
  DEP_ONCE_REWRITE_TAC[GSYM MOD_PLUS]>>fs[]
QED

Theorem FLAT_REPLICATE_NIL:
   !n. FLAT (REPLICATE n []) = []
Proof
  Induct \\ fs [REPLICATE]
QED

Theorem MEM_REPLICATE_EQ:
   !n x y. MEM x (REPLICATE n y) <=> x = y /\ n <> 0
Proof
  Induct \\ fs [REPLICATE] \\ rw [] \\ eq_tac \\ rw []
QED

Theorem FLAT_MAP_SING:
   ∀ls. FLAT (MAP (λx. [f x]) ls) = MAP f ls
Proof
  Induct \\ simp[]
QED

Theorem FLAT_MAP_NIL:
   FLAT (MAP (λx. []) ls) = []
Proof
  rw[FLAT_EQ_NIL,EVERY_MAP]
QED

Theorem UPDATE_LIST_NOT_MEM:
   ∀ls f x. ¬MEM x(MAP FST ls) ⇒ (f =++ ls) x = f x
Proof
  Induct >> simp[UPDATE_LIST_THM,combinTheory.APPLY_UPDATE_THM]
QED

Theorem MAP_ZIP_UPDATE_LIST_ALL_DISTINCT_same:
   ∀ks vs f. LENGTH ks = LENGTH vs ∧ ALL_DISTINCT ks ⇒ (MAP (f =++ ZIP (ks,vs)) ks = vs)
Proof
  Induct >> simp[LENGTH_NIL_SYM] >>
  gen_tac >> Cases >> simp[UPDATE_LIST_THM] >>
  simp[UPDATE_LIST_NOT_MEM,MAP_ZIP,combinTheory.APPLY_UPDATE_THM]
QED

Theorem flookup_update_list_none:
 !x m l.
  (FLOOKUP (m |++ l) x = NONE)
  =
  ((FLOOKUP m x = NONE) ∧ (ALOOKUP l x = NONE))
Proof
 rw [flookup_fupdate_list] >>
 every_case_tac >>
 fs [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 metis_tac []
QED

Theorem flookup_update_list_some:
 !x m l y.
  (FLOOKUP (m |++ l) x = SOME y)
  =
  ((ALOOKUP (REVERSE l) x = SOME y) ∨
   ((ALOOKUP l x = NONE) ∧ (FLOOKUP m x = SOME y)))
Proof
 rw [flookup_fupdate_list] >>
 every_case_tac >>
 fs [flookup_thm, ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 fs [] >>
 metis_tac []
QED

Theorem PERM_MAP_BIJ:
   ∀f l1 l2.
    BIJ f UNIV UNIV ⇒
    (PERM l1 l2 ⇔ PERM (MAP f l1) (MAP f l2))
Proof
  rw[BIJ_IFF_INV] >>
  EQ_TAC >- rw[sortingTheory.PERM_MAP] >>
  `∀l. MEM l [l1;l2] ⇒ l = MAP g (MAP f l)` by (
    rw[MAP_MAP_o,combinTheory.o_DEF] ) >>
  fs[] >>
  metis_tac[sortingTheory.PERM_MAP]
QED

Theorem UNCURRY_eq_pair:
   UNCURRY f v = z ⇔ ∃a b. v = (a,b) ∧ f a b = z
Proof
  Cases_on`v`\\ rw[UNCURRY]
QED

Theorem FST_UNZIP_MAPi:
   ∀l f. FST (UNZIP (MAPi f l)) = MAPi ((o) ((o) FST) f) l
Proof
  Induct >> simp[]
QED

Theorem SND_UNZIP_MAPi:
   ∀l f. SND (UNZIP (MAPi f l)) = MAPi ((o) ((o) SND) f) l
Proof
  Induct >> simp[]
QED

Theorem ALL_DISTINCT_FLAT:
   ∀l. ALL_DISTINCT (FLAT l) ⇔
        (∀l0. MEM l0 l ⇒ ALL_DISTINCT l0) ∧
        (∀i j. i < j ∧ j < LENGTH l ⇒
               ∀e. MEM e (EL i l) ⇒ ¬MEM e (EL j l))
Proof
  Induct >> dsimp[ALL_DISTINCT_APPEND, LT_SUC, MEM_FLAT] >>
  metis_tac[MEM_EL]
QED

Theorem ALL_DISTINCT_FLAT_EVERY:
   ∀ls. ALL_DISTINCT (FLAT ls) ⇒ EVERY ALL_DISTINCT ls
Proof
  Induct \\ simp[ALL_DISTINCT_APPEND]
QED

Theorem ALL_DISTINCT_APPEND_APPEND_IMP:
   ALL_DISTINCT (xs ++ ys ++ zs) ==>
    ALL_DISTINCT (xs ++ ys) /\ ALL_DISTINCT (xs ++ zs) /\ ALL_DISTINCT (ys ++ zs)
Proof
  fs [ALL_DISTINCT_APPEND]
QED

(* TODO - candidate for move to HOL *)
Theorem o_PAIR_MAP:
   FST o (f ## g) = f o FST ∧
   SND o (f ## g) = g o SND
Proof
  simp[FUN_EQ_THM]
QED

Theorem ALOOKUP_EXISTS_IFF:
   (∃v. ALOOKUP alist k = SOME v) ⇔ (∃v. MEM (k,v) alist)
Proof
  Induct_on `alist` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]
QED

Theorem LUPDATE_commutes:
   ∀m n e1 e2 l.
    m ≠ n ⇒
    LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)
Proof
  Induct_on `l` >> simp[LUPDATE_def] >>
  Cases_on `m` >> simp[LUPDATE_def] >> rpt strip_tac >>
  rename[`LUPDATE _ nn (_ :: _)`] >>
  Cases_on `nn` >> fs[LUPDATE_def]
QED

Theorem LUPDATE_APPEND:
   !xs n ys x.
      LUPDATE x n (xs ++ ys) =
      if n < LENGTH xs then LUPDATE x n xs ++ ys
                       else xs ++ LUPDATE x (n - LENGTH xs) ys
Proof
  Induct \\ fs [] \\ Cases_on `n` \\ fs [LUPDATE_def] \\ rw [] \\ fs []
QED

Theorem FILTER_EL_EQ:
   ∀l1 l2. LENGTH l1 = LENGTH l2 ∧
   (∀n. n < LENGTH l1 ∧ (P (EL n l1) ∨ P (EL n l2)) ⇒ (EL n l1 = EL n l2))
   ⇒
   FILTER P l1 = FILTER P l2
Proof
  Induct \\ rw[] \\ Cases_on`l2` \\ fs[]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac (srw_ss())[] \\ simp[]
  \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ rw[]
  \\ first_x_assum(qspec_then`SUC n`mp_tac) \\ rw[]
QED

Theorem FST_EL_AFUPDKEY:
   ∀n. n < LENGTH ls ⇒ FST (EL n (AFUPDKEY k f ls)) = FST (EL n ls)
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ rw[AFUPDKEY_def]
  \\ Cases_on`n` \\ fs[]
QED

Theorem EL_AFUPDKEY_unchanged:
   ∀n. n < LENGTH ls ∧ FST (EL n ls) ≠ k ⇒ EL n (AFUPDKEY k f ls) = EL n ls
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ simp[AFUPDKEY_def]
  \\ Cases \\ simp[]
  \\ IF_CASES_TAC \\ rpt BasicProvers.VAR_EQ_TAC \\ rw[]
QED

Theorem findi_APPEND:
   ∀l1 l2 x.
      findi x (l1 ++ l2) =
        let n0 = findi x l1
        in
          if n0 = LENGTH l1 then n0 + findi x l2
          else n0
Proof
  Induct >> simp[findi_def] >> rw[] >> fs[]
QED

Theorem NOT_MEM_findi_IFF:
   ¬MEM e l ⇔ findi e l = LENGTH l
Proof
  Induct_on `l` >> simp[findi_def, bool_case_eq, ADD1] >> metis_tac[]
QED

Theorem NOT_MEM_findi =
  NOT_MEM_findi_IFF |> EQ_IMP_RULE |> #1

Theorem HD_LUPDATE:
   0 < LENGTH l ⇒ HD (LUPDATE x p l) = if p = 0 then x else HD l
Proof
  Cases_on `l` >> rw[LUPDATE_def] >> Cases_on `p` >> fs[LUPDATE_def]
QED

Theorem DROP_LUPDATE:
   !n x m l. n ≤ m ⇒ DROP n (LUPDATE x m l) = LUPDATE x (m - n) (DROP n l)
Proof
  rw [LIST_EQ_REWRITE, EL_DROP, EL_LUPDATE] >>
  rw [] >>
  fs []
QED

Theorem MAP_K_REPLICATE:
   MAP (K x) ls = REPLICATE (LENGTH ls) x
Proof
  Induct_on`ls` \\ rw[REPLICATE]
QED

Theorem SPLITP_CONS_IMP:
   ∀ls l' r. (SPLITP P ls = (l', r)) /\ (r <> []) ==> (EXISTS P ls)
Proof
  rw[] \\ imp_res_tac SPLITP_IMP \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on `r` \\ rfs[NULL_EQ, EXISTS_DEF, HD]
QED

Theorem LAST_CONS_alt:
   P x ==> ((ls <> [] ==> P (LAST ls)) <=> (P (LAST (CONS x ls))))
Proof
  Cases_on`ls` \\ rw[]
QED

Theorem EL_CONS_IF:
  EL n (x :: xs) = (if n = 0 then x else EL (PRE n) xs)
Proof    Cases_on `n` \\ fs []
QED

Theorem EVERY_TOKENS:
   ∀P ls. EVERY (EVERY ($~ o P)) (TOKENS P ls)
Proof
  recInduct TOKENS_ind
  \\ rw[TOKENS_def]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ IF_CASES_TAC \\ fs[]
  \\ imp_res_tac SPLITP_IMP
QED

Theorem TOKENS_START:
  !l a. TOKENS (\x. x = a) (a::l) = TOKENS (\x. x = a) l
Proof
  gen_tac \\ Induct_on `l` \\ rw[TOKENS_def] \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[]
  >-(imp_res_tac SPLITP_NIL_FST_IMP \\ fs[] \\ rw[TOKENS_def])
  >-(fs[SPLITP])
  >-(pairarg_tac \\ fs[NULL_EQ] \\ rw[]
    \\ imp_res_tac SPLITP_NIL_FST_IMP
    \\ imp_res_tac SPLITP_IMP \\ rfs[]
    \\ simp[TOKENS_def] \\ rw[NULL_EQ])
  >-(pairarg_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[SPLITP])
QED

Theorem TOKENS_END:
   !l a.
      TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l
Proof
    rw[]
    \\ `TOKENS (\x. x = a) (l ++ [a]) = TOKENS (\x. x = a) l ++ TOKENS (\x. x = a) ""` by fs[TOKENS_APPEND]
    \\ fs[TOKENS_def] \\ rw[]
QED

Theorem TOKENS_LENGTH_END:
   !l a.
      LENGTH (TOKENS (\x. x = a) (l ++ [a])) = LENGTH (TOKENS (\x. x = a) l)
Proof
  rw[] \\ AP_TERM_TAC \\ rw[TOKENS_END]
QED

Theorem TOKENS_LENGTH_START:
   !l a.
      LENGTH (TOKENS (\x. x = a) (a::l)) = LENGTH (TOKENS (\x. x= a) l)
Proof
  rw[] \\ AP_TERM_TAC \\ rw[TOKENS_START]
QED

Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
Proof
    Induct \\ rw[DROP]
    \\ Cases_on `n > LENGTH ls` \\ fs[]
    \\ `n < LENGTH (h::ls)` by fs[]
    \\ fs[DROP_EL_CONS]
QED

Theorem TL_DROP_SUC:
   ∀x ls. x < LENGTH ls ⇒ TL (DROP x ls) = DROP (SUC x) ls
Proof
  Induct \\ rw[] \\ Cases_on`ls` \\ fs[]
QED

Theorem DROP_IMP_LESS_LENGTH:
   !xs n y ys. DROP n xs = y::ys ==> n < LENGTH xs
Proof
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ decide_tac
QED

Theorem DROP_EQ_CONS_IMP_DROP_SUC:
   !xs n y ys. DROP n xs = y::ys ==> DROP (SUC n) xs = ys
Proof
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ `n - 1 + 1 = n` by decide_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem DROP_IMP_EL:
   !xs n h t. DROP n xs = h::t ==> (EL n xs = h)
Proof
  Induct \\ fs [DROP_def] \\ Cases_on `n` \\ fs []
QED

Theorem LENGTH_FIELDS:
   ∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[] \\ fs[] \\ rw[ADD1]
  \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_NIL_FST_IMP
  \\ imp_res_tac SPLITP_NIL_SND_EVERY
  \\ imp_res_tac SPLITP_IMP
  \\ fs[NULL_EQ]
  \\ fs[SPLITP] \\ rfs[] \\ rw[]
  >- (`FILTER P t = []` by (simp[FILTER_EQ_NIL] \\ fs[EVERY_MEM])
      \\ simp[])
  \\ first_x_assum(qspec_then`LENGTH t`mp_tac) \\ simp[]
  \\ disch_then(qspec_then`t`mp_tac)
  \\ Cases_on`t` \\ rw[FIELDS_def]
  \\ fs[SPLITP] \\ rfs[]
  \\ rfs[NULL_EQ]
QED

Theorem FIELDS_NEQ_NIL[simp]:
   FIELDS P ls ≠ []
Proof
  disch_then(assume_tac o Q.AP_TERM`LENGTH`)
  \\ fs[LENGTH_FIELDS]
QED

Theorem CONCAT_FIELDS:
   ∀ls. CONCAT (FIELDS P ls) = FILTER ($~ o P) ls
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ simp[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ fs[Once SPLITP]
  \\ Cases_on`P h` \\ fs[] \\ rpt BasicProvers.VAR_EQ_TAC \\ simp[]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`NULL r` \\ fs[NULL_EQ]
  >- (
    imp_res_tac SPLITP_NIL_SND_EVERY
    \\ fs[FILTER_EQ_ID] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ simp[FILTER_APPEND]
  \\ fs[GSYM FILTER_EQ_ID]
  \\ Cases_on`r` \\ fs[]
QED

Theorem FIELDS_next:
   ∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 ∧
   (∃c. l1 ++ [c] ≼ ls ∧ P c)
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[]
  \\ imp_res_tac SPLITP_NIL_FST_IMP \\ fs[]
  \\ imp_res_tac SPLITP_IMP \\ fs[]
  \\ imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[]
  \\ rfs[PULL_FORALL,NULL_EQ]
  \\ fs[SPLITP]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ fs[SPLITP]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`SPLITP P q` \\ fs[]
  \\ rw[]
  \\ `FIELDS P t = q::FIELDS P (TL r)`
  by (
    Cases_on`t` \\ fs[]
    \\ rw[FIELDS_def,NULL_EQ] )
  \\ first_x_assum(qspecl_then[`t`,`q`,`FIELDS P (TL r)`]mp_tac)
  \\ simp[]
QED

Theorem FIELDS_full:
   ∀P ls l1 l2.
   FIELDS P ls = l1::l2 ∧ LENGTH ls ≤ LENGTH l1 ⇒
   l1 = ls ∧ l2 = []
Proof
  ntac 2 gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ simp_tac(srw_ss()++LET_ss)[FIELDS_def]
  \\ pairarg_tac \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
  \\ strip_tac
  \\ IF_CASES_TAC
  >-
   (simp_tac(srw_ss())[]
    \\ Cases_on `l1 = ""` \\simp[])
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_SND_EVERY )
  \\ simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
  \\ qspec_then`h::t`mp_tac(GSYM SPLITP_LENGTH)
  \\ last_x_assum kall_tac
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ `LENGTH r = 0` by decide_tac
  \\ fs[LENGTH_NIL]
QED

Theorem FLAT_MAP_TOKENS_FIELDS:
   ∀P' ls P.
    (∀x. P' x ⇒ P x) ⇒
     FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
     TOKENS P ls
Proof
  Induct_on`FIELDS P' ls` \\ rw[] \\
  qpat_x_assum`_ = FIELDS _ _`(assume_tac o SYM) \\
  imp_res_tac FIELDS_next \\
  Cases_on`LENGTH ls ≤ LENGTH h` >- (
    imp_res_tac FIELDS_full \\ fs[] ) \\
  fs[] \\ rw[] \\
  fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] \\
  `h ++ [c] ++ l  = h ++ (c::l)` by simp[] \\ pop_assum SUBST_ALL_TAC \\
  asm_simp_tac std_ss [TOKENS_APPEND]
QED

Definition splitlines_def:
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines
End

Theorem splitlines_next:
   splitlines ls = ln::lns ⇒
   splitlines (DROP (SUC (LENGTH ln)) ls) = lns ∧
   ln ≼ ls ∧ (LENGTH ln < LENGTH ls ⇒ ln ++ "\n" ≼ ls)
Proof
  simp[splitlines_def]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ Cases_on`LENGTH h < LENGTH ls`
  >- (
    imp_res_tac FIELDS_next
    \\ strip_tac
    \\ `ln = h`
    by (
      pop_assum mp_tac \\ rw[]
      \\ fs[FRONT_DEF] )
    \\ fs[]
    \\ fs[LAST_DEF,NULL_EQ]
    \\ Cases_on`t = []` \\ fs[]
    \\ fs[FRONT_DEF]
    \\ IF_CASES_TAC \\ fs[]
    \\ fs[IS_PREFIX_APPEND])
  \\ fs[NOT_LESS]
  \\ imp_res_tac FIELDS_full \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ strip_tac \\ rpt BasicProvers.VAR_EQ_TAC \\ fs[]
  \\ simp[DROP_LENGTH_TOO_LONG,FIELDS_def]
QED

Theorem splitlines_nil[simp] = EVAL``splitlines ""``

Theorem splitlines_eq_nil[simp]:
   splitlines ls = [] ⇔ (ls = [])
Proof
  rw[EQ_IMP_THM]
  \\ fs[splitlines_def]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ fs[LAST_DEF] \\ rfs[NULL_EQ]
  \\ Cases_on`LENGTH "" < LENGTH ls`
  >- ( imp_res_tac FIELDS_next \\ fs[] )
  \\ fs[LENGTH_NIL]
QED

Theorem splitlines_CONS_FST_SPLITP:
   splitlines ls = ln::lns ⇒ FST (SPLITP ($= #"\n") ls) = ln
Proof
  rw[splitlines_def]
  \\ Cases_on`ls` \\ fs[FIELDS_def]
  \\ TRY pairarg_tac \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ fs[NULL_EQ, FIELDS_def]
  \\ qmatch_assum_abbrev_tac`FRONT (x::y) = _`
  \\ Cases_on`y` \\ fs[]
QED

Definition CONCAT_WITH_aux_def:
    (CONCAT_WITH_aux [] l fl = REVERSE fl ++ FLAT l) /\
    (CONCAT_WITH_aux (h::t) [] fl = REVERSE fl) /\
    (CONCAT_WITH_aux (h::t) ((h1::t1)::ls) fl = CONCAT_WITH_aux (h::t) (t1::ls) (h1::fl)) /\
    (CONCAT_WITH_aux (h::t) ([]::[]) fl = REVERSE fl) /\
    (CONCAT_WITH_aux (h::t) ([]::(h'::t')) fl = CONCAT_WITH_aux (h::t) (h'::t') (REVERSE(h::t) ++ fl))
End

val CONCAT_WITH_AUX_ind = theorem"CONCAT_WITH_aux_ind";

Definition CONCAT_WITH_def:
    CONCAT_WITH s l = CONCAT_WITH_aux s l []
End

Theorem MEM_REPLICATE_IMP:
   MEM x (REPLICATE n y) ==> x = y
Proof
  Induct_on`n` \\ rw[REPLICATE] \\ fs[]
QED

(* used once *)
Theorem SUM_COUNT_LIST =
  SUM_MAP_COUNT_LIST |> Q.SPECL [`n`,`0`] |> SIMP_RULE (srw_ss()) []

Theorem TAKE_FLAT_REPLICATE_LEQ:
   ∀j k ls len.
    len = LENGTH ls ∧ k ≤ j ⇒
    TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k ls)
Proof
  Induct \\ simp[REPLICATE]
  \\ Cases \\ simp[REPLICATE]
  \\ simp[TAKE_APPEND2] \\ rw[] \\ fs[]
  \\ simp[MULT_SUC]
QED

(* should be set l1 ⊆ set l2 *)
Definition list_subset_def:
  list_subset l1 l2 = EVERY (\x. MEM x l2) l1
End

Definition list_set_eq_def:
  list_set_eq l1 l2 ⇔ list_subset l1 l2 ∧ list_subset l2 l1
End

Theorem list_subset_LENGTH:
    !l1 l2.ALL_DISTINCT l1 ∧
  list_subset l1 l2 ⇒
  LENGTH l1 ≤ LENGTH l2
Proof
  fs[list_subset_def,EVERY_MEM]>>
  Induct>>rw[]>>
  first_x_assum(qspec_then`FILTER ($~ o $= h) l2` assume_tac)>>
  rfs[MEM_FILTER]>>
  `LENGTH (FILTER ($~ o $= h) l2) < LENGTH l2` by
    (match_mp_tac LENGTH_FILTER_LESS>>
    fs[EXISTS_MEM])>>
  fs[]
QED

Theorem SPLITP_TAKE_DROP:
  !P i l. EVERY ($~ ∘ P) (TAKE i l) ==>
  P (EL i l) ==>
  SPLITP P l = (TAKE i l, DROP i l)
Proof
  Induct_on`l` >> rw[SPLITP] >> Cases_on`i` >> fs[] >>
  res_tac >> fs[FST,SND]
QED

Theorem SND_SPLITP_DROP:
  !P n l. EVERY ($~ o P) (TAKE n l) ==>
   SND (SPLITP P (DROP n l)) = SND (SPLITP P l)
Proof
 Induct_on`n` >> rw[SPLITP] >> Cases_on`l` >> fs[SPLITP]
QED

Theorem FST_SPLITP_DROP:
  !P n l. EVERY ($~ o P) (TAKE n l) ==>
   FST (SPLITP P l) = (TAKE n l) ++ FST (SPLITP P (DROP n l))
Proof
 Induct_on`n` >> rw[SPLITP] >> Cases_on`l` >>
 PURE_REWRITE_TAC[DROP_def,TAKE_def,APPEND] >> simp[] >>
 fs[SPLITP]
QED

Theorem TAKE_DROP_SUBLIST:
   ll ≼ (DROP n ls) ∧ n < LENGTH ls ∧ (nlll = n + LENGTH ll) ⇒
   (TAKE n ls ++ ll ++ DROP nlll ls = ls)
Proof
  rw[IS_PREFIX_APPEND, LIST_EQ_REWRITE, LENGTH_TAKE_EQ, EL_APPEND_EQN, EL_DROP]
  \\ rw[] \\ fs[EL_TAKE]
  \\ fs[NOT_LESS, LESS_EQ_EXISTS]
QED

Theorem SUM_MAP_K:
   ∀f ls c. (∀x. f x = c) ⇒ SUM (MAP f ls) = LENGTH ls * c
Proof
  rw[] \\ Induct_on`ls` \\ rw[MULT_SUC]
QED

Theorem LAST_FLAT:
   ∀ls. ~NULL (FLAT ls) ==> (LAST (FLAT ls) = LAST (LAST (FILTER ($~ o NULL) ls)))
Proof
  ho_match_mp_tac SNOC_INDUCT \\ rw[]
  \\ fs[FLAT_SNOC,FILTER_SNOC]
  \\ Cases_on`x` \\ fs[]
QED

Theorem TOKENS_unchanged:
  EVERY ($~ o P) ls ==> TOKENS P ls = if NULL ls then [] else [ls]
Proof
  Induct_on`ls` \\ rw[TOKENS_def] \\ fs[]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on`r=[]` \\ fs[]
  >- ( imp_res_tac SPLITP_NIL_FST_IMP \\ rpt BasicProvers.VAR_EQ_TAC \\ fs[TOKENS_NIL] )
  \\ rw[]
  >- (
    imp_res_tac SPLITP_NIL_FST_IMP
    \\ imp_res_tac SPLITP_IMP
    \\ rfs[] \\ rpt BasicProvers.VAR_EQ_TAC \\ fs[] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ fs[EVERY_MEM]
  \\ `MEM (HD r) (l ++ r)` by (Cases_on`r` \\ fs[])
  \\ Cases_on`MEM (HD r) l` \\ fs[] >- metis_tac[]
  \\ `MEM (HD r) (h::ls)` by metis_tac[MEM_APPEND]
  \\ fs[] \\ rw[] \\ metis_tac[]
QED

Theorem TOKENS_FLAT_MAP_SNOC:
   EVERY (EVERY ((<>) x)) ls ∧ EVERY ($~ o NULL) ls ==>
   TOKENS ((=) x) (FLAT (MAP (SNOC x) ls)) = ls
Proof
  Induct_on`ls` \\ rw[TOKENS_NIL]
  \\ rewrite_tac[GSYM APPEND_ASSOC,SNOC_APPEND,APPEND]
  \\ DEP_REWRITE_TAC[TOKENS_APPEND] \\ rw[]
  \\ DEP_REWRITE_TAC[TOKENS_unchanged]
  \\ fs[EVERY_MEM]
QED

(* insert a string (l1) at specified index (n) in a list (l2) *)
Definition insert_atI_def:
  insert_atI l1 n l2 =
    TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2
End

Theorem insert_atI_NIL:
   ∀n l.insert_atI [] n l = l
Proof
  simp[insert_atI_def]
QED

Theorem insert_atI_CONS:
   ∀n l h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (h::t) n l = LUPDATE h n (insert_atI t (n + 1) l)
Proof
  simp[insert_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[ADD1, LUPDATE_def]) >>
  Cases_on `l` >> simp[ADD1] >> fs[ADD1] >>
  simp[GSYM ADD1, LUPDATE_def]
QED

Theorem LENGTH_insert_atI:
   p + LENGTH l1 <= LENGTH l2 ⇒ LENGTH (insert_atI l1 p l2) = LENGTH l2
Proof
  simp[insert_atI_def]
QED

Theorem insert_atI_app:
   ∀n l c1 c2.  n + LENGTH c1 + LENGTH c2 <= LENGTH l ==>
     insert_atI (c1 ++ c2) n l =
     insert_atI c1 n (insert_atI c2 (n + LENGTH c1) l)
Proof
  Induct_on`c1` >> fs[insert_atI_NIL,insert_atI_CONS,LENGTH_insert_atI,ADD1]
QED

Theorem insert_atI_end:
   insert_atI l1 (LENGTH l2) l2 = l2 ++ l1
Proof
  simp[insert_atI_def,DROP_LENGTH_TOO_LONG]
QED

Theorem insert_atI_insert_atI:
   pos2 = pos1 + LENGTH c1 ==>
    insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (c1 ++ c2) pos1 l
Proof
    rw[insert_atI_def,TAKE_SUM,TAKE_APPEND,LENGTH_TAKE_EQ,LENGTH_DROP,
       GSYM DROP_DROP_T,DROP_LENGTH_TOO_LONG,DROP_LENGTH_NIL_rwt]
    >> fs[DROP_LENGTH_NIL_rwt,LENGTH_TAKE,DROP_APPEND1,TAKE_APPEND,TAKE_TAKE,
       DROP_DROP_T,DROP_APPEND2,TAKE_LENGTH_TOO_LONG,TAKE_SUM,LENGTH_DROP]
QED

Theorem LUPDATE_insert_commute:
   ∀ws pos1 pos2 a w.
     pos2 < pos1 ∧ pos1 + LENGTH ws <= LENGTH a ⇒
     insert_atI ws pos1 (LUPDATE w pos2 a) =
       LUPDATE w pos2 (insert_atI ws pos1 a)
Proof
  Induct >> simp[insert_atI_NIL,insert_atI_CONS, LUPDATE_commutes]
QED

Theorem LESS_EQ_LENGTH:
   !xs k. k <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = k)
Proof
  Induct \\ Cases_on `k` \\ full_simp_tac std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss []
  \\ qexists_tac `h::ys1` \\ full_simp_tac std_ss [LENGTH,APPEND]
  \\ srw_tac [] [ADD1]
QED

Theorem LESS_LENGTH:
   !xs k. k < LENGTH xs ==>
           ?ys1 y ys2. (xs = ys1 ++ y::ys2) /\ (LENGTH ys1 = k)
Proof
  Induct \\ Cases_on `k` \\ full_simp_tac std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss [CONS_11]
  \\ qexists_tac `h::ys1` \\ full_simp_tac std_ss [LENGTH,APPEND]
  \\ srw_tac [] [ADD1]
QED

Theorem BAG_ALL_DISTINCT_FOLDR_BAG_UNION:
   ∀ls b0.
   BAG_ALL_DISTINCT (FOLDR BAG_UNION b0 ls) ⇔
   BAG_ALL_DISTINCT b0 ∧
   (∀n. n < LENGTH ls ⇒
        BAG_DISJOINT (EL n ls) b0 ∧ BAG_ALL_DISTINCT (EL n ls) ∧
        (∀m. m < n ⇒ BAG_DISJOINT (EL n ls) (EL m ls)))
Proof
  Induct \\ rw[]
  \\ rw[BAG_ALL_DISTINCT_BAG_UNION]
  \\ simp[Once FORALL_NUM, SimpRHS]
  \\ Cases_on`BAG_ALL_DISTINCT h` \\ simp[]
  \\ Cases_on`BAG_ALL_DISTINCT b0` \\ simp[]
  \\ simp[BAG_DISJOINT_FOLDR_BAG_UNION, EVERY_MEM, MEM_EL, PULL_EXISTS]
  \\ CONV_TAC(PATH_CONV"rrrarrr"(HO_REWR_CONV FORALL_NUM))
  \\ simp[]
  \\ rw[EQ_IMP_THM] \\ fs[]
  \\ metis_tac[BAG_DISJOINT_SYM]
QED

(* TODO - candidate for move to HOL *)
Definition is_subseq_def:
  (is_subseq ls [] ⇔ T) ∧
  (is_subseq [] (x::xs) ⇔ F) ∧
  (is_subseq (y::ys) (x::xs) ⇔
   (x = y ∧ is_subseq ys xs) ∨
   (is_subseq ys (x::xs)))
End

val is_subseq_ind = theorem"is_subseq_ind";

Theorem is_subseq_refl[simp]:
   ∀ls. is_subseq ls ls
Proof
Induct \\ rw[is_subseq_def]
QED

Theorem is_subseq_nil[simp]:
   is_subseq [] ls ⇔ ls = []
Proof
  Cases_on`ls` \\ rw[is_subseq_def]
QED

Theorem is_subseq_cons:
   ∀l1 l2 x. is_subseq l1 l2 ⇒ is_subseq (x::l1) l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
QED

Theorem is_subseq_snoc:
   ∀l1 l2 x. is_subseq l1 l2 ⇒ is_subseq (SNOC x l1) l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def] \\ fs[]
QED

Theorem is_subseq_append1:
   ∀l3 l1 l2. is_subseq l1 l2 ⇒ is_subseq (l3 ++ l1) l2
Proof
  Induct
  \\ rw[is_subseq_def] \\ fs[]
  \\ metis_tac[is_subseq_cons]
QED

Theorem is_subseq_append2:
   ∀l4 l1 l2. is_subseq l1 l2 ⇒ is_subseq (l1 ++ l4) l2
Proof
  ho_match_mp_tac SNOC_INDUCT
  \\ rw[is_subseq_def] \\ fs[]
  \\ metis_tac[is_subseq_snoc, SNOC_APPEND, APPEND_ASSOC]
QED

Theorem is_subseq_IS_SUBLIST:
   is_subseq l1 l2 ∧ IS_SUBLIST l3 l1 ⇒ is_subseq l3 l2
Proof
  rw[IS_SUBLIST_APPEND]
  \\ metis_tac[is_subseq_append1, is_subseq_append2]
QED

Theorem is_subseq_MEM:
   ∀l1 l2 x. is_subseq l1 l2 ∧ MEM x l2 ⇒ MEM x l1
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
  \\ metis_tac[]
QED

Theorem IS_PREFIX_is_subseq:
   ∀l1 l2. IS_PREFIX l1 l2 ⇒ is_subseq l1 l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
  \\ fs[IS_PREFIX_NIL]
QED

Theorem IS_SUBLIST_is_subseq:
   ∀l1 l2. IS_SUBLIST l1 l2 ⇒ is_subseq l1 l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def, IS_SUBLIST]
  \\ simp[IS_PREFIX_is_subseq]
QED

Theorem is_subseq_ALL_DISTINCT:
   ∀l1 l2. ALL_DISTINCT l1 ∧ is_subseq l1 l2 ⇒ ALL_DISTINCT l2
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def] \\ fs[] \\ rfs[]
  \\ metis_tac[is_subseq_MEM]
QED

Theorem is_subseq_append_suff:
   ∀l1 l3 l2 l4.
   is_subseq l1 l3 ∧ is_subseq l2 l4 ⇒
   is_subseq (l1 ++ l2) (l3 ++ l4)
Proof
  recInduct is_subseq_ind
  \\ rw[is_subseq_def]
  \\ metis_tac[is_subseq_append1]
QED

Theorem is_subseq_FLAT_suff:
   ∀ls1 ls2. LIST_REL is_subseq ls1 ls2 ⇒ is_subseq (FLAT ls1) (FLAT ls2)
Proof
  ho_match_mp_tac LIST_REL_ind
  \\ rw[is_subseq_append_suff]
QED

Theorem LIST_REL_IMP_LAST:
   !P xs ys.
      LIST_REL P xs ys /\ (xs <> [] \/ ys <> []) ==> P (LAST xs) (LAST ys)
Proof
  rpt gen_tac
  \\ Cases_on `xs = []` \\ fs [] \\ Cases_on `ys = []` \\ fs []
  \\ `?x1 x2. xs = SNOC x1 x2` by metis_tac [SNOC_CASES]
  \\ `?y1 y2. ys = SNOC y1 y2` by metis_tac [SNOC_CASES]
  \\ asm_rewrite_tac [LAST_SNOC] \\ fs [LIST_REL_SNOC]
QED

Theorem ALOOKUP_MAP_FST_INJ_SOME:
   ∀ls x y.
    ALOOKUP ls x = SOME y ∧ (∀x'. IS_SOME (ALOOKUP ls x') ∧ f x' = f x ⇒ x = x') ⇒
    ALOOKUP (MAP (f ## g) ls) (f x) = SOME (g y)
Proof
  Induct \\ simp[]
  \\ Cases \\ rw[]
  >- metis_tac[IS_SOME_EXISTS]
  \\ first_x_assum irule
  \\ rw[]
  \\ first_x_assum irule
  \\ rw[]
QED

Theorem ALL_DISTINCT_alist_to_fmap_REVERSE:
   ALL_DISTINCT (MAP FST ls) ⇒ alist_to_fmap (REVERSE ls) = alist_to_fmap ls
Proof
  Induct_on`ls` \\ simp[FORALL_PROD] \\ rw[] \\ rw[FUNION_FUPDATE_2]
QED

Theorem FUPDATE_LIST_alist_to_fmap:
 ∀ls fm. fm |++ ls = alist_to_fmap (REVERSE ls) ⊌ fm
Proof
 metis_tac [FUNION_alist_to_fmap, REVERSE_REVERSE]
QED

Theorem DISTINCT_FUPDATE_LIST_UNION:
   ALL_DISTINCT (MAP FST ls) /\
   DISJOINT (FDOM f) (set(MAP FST ls)) ==>
   f |++ ls = FUNION f (alist_to_fmap ls)
Proof
  rw[FUPDATE_LIST_alist_to_fmap,ALL_DISTINCT_alist_to_fmap_REVERSE]
  \\ match_mp_tac FUNION_COMM \\ rw[DISJOINT_SYM]
QED

(* --- LIST_REL lemmas --- *)

Theorem LIST_REL_EL:
  !xs ys r.
    LIST_REL r xs ys <=>
    (LENGTH xs = LENGTH ys) /\
    !n. n < LENGTH ys ==> r (EL n xs) (EL n ys)
Proof
  Induct \\ Cases_on `ys` \\ fs [] \\ rw [] \\ eq_tac \\ rw []
  THEN1 (Cases_on `n` \\ fs [])
  THEN1 (first_x_assum (qspec_then `0` mp_tac) \\ fs [])
  \\ first_x_assum (qspec_then `SUC n` mp_tac) \\ fs []
QED

Theorem LIST_REL_IMP_EL2:
  !P xs ys. LIST_REL P xs ys ==> !i. i < LENGTH ys ==> P (EL i xs) (EL i ys)
Proof
  Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ Cases_on `i` \\ fs []
QED

Theorem LIST_REL_IMP_EL:
  !P xs ys. LIST_REL P xs ys ==> !i. i < LENGTH xs ==> P (EL i xs) (EL i ys)
Proof
  Induct_on `xs` \\ fs [PULL_EXISTS] \\ rw [] \\ Cases_on `i` \\ fs []
QED

Theorem LIST_REL_ALOOKUP_OPTREL:
  !xs ys. LIST_REL R xs ys /\
  (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==>
    FST x = FST y /\ R2 (SND x) (SND y))
  ==> OPTREL R2 (ALOOKUP xs v) (ALOOKUP ys v)
Proof
  Induct \\ rpt (Cases ORELSE gen_tac)
  \\ simp [optionTheory.OPTREL_def]
  \\ qmatch_goalsub_abbrev_tac `ALOOKUP (pair :: _)`
  \\ Cases_on `pair`
  \\ simp []
  \\ rpt strip_tac
  \\ last_x_assum drule
  \\ impl_tac >- metis_tac []
  \\ simp []
  \\ strip_tac
  \\ first_x_assum drule
  \\ rw []
  \\ fs [optionTheory.OPTREL_def]
QED

Theorem LIST_REL_ALOOKUP:
  !xs ys. LIST_REL R xs ys /\
  (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==> x = y)
  ==> ALOOKUP xs v = ALOOKUP ys v
Proof
  REWRITE_TAC [GSYM optionTheory.OPTREL_eq]
  \\ rpt strip_tac
  \\ drule_then irule LIST_REL_ALOOKUP_OPTREL
  \\ metis_tac []
QED

Theorem LIST_REL_FILTER_MONO:
  !xs ys. LIST_REL R (FILTER P1 xs) (FILTER P2 ys) /\
  (!x. MEM x xs /\ P3 x ==> P1 x) /\
  (!y. MEM y ys /\ P4 y ==> P2 y) /\
  (!x y. MEM x xs /\ MEM y ys /\ R x y ==> P3 x = P4 y)
  ==> LIST_REL R (FILTER P3 xs) (FILTER P4 ys)
Proof
  Induct
  >- (
    simp [FILTER_EQ_NIL, EVERY_MEM]
    \\ metis_tac []
  )
  \\ gen_tac
  \\ simp []
  \\ reverse CASE_TAC
  >- (
    CASE_TAC
    >- metis_tac []
    \\ rw []
  )
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [FILTER_EQ_CONS]
  \\ rename [`_ = ys_pre ++ [y] ++ ys_post`]
  \\ rpt BasicProvers.VAR_EQ_TAC \\ fs []
  \\ fs [FILTER_APPEND]
  \\ first_x_assum drule
  \\ simp []
  \\ disch_tac
  \\ `FILTER P4 ys_pre = []` by (fs [FILTER_EQ_NIL, EVERY_MEM] \\ metis_tac [])
  \\ rw []
  \\ metis_tac []
QED

(* --- APPEND / LASTN / LAST lemmas --- *)

Theorem APPEND_LENGTH_EQ:
  !xs xs'. LENGTH xs = LENGTH xs' ==>
  (xs ++ ys = xs' ++ ys' <=> xs = xs' /\ ys = ys')
Proof
  Induct
  \\ rw []
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_COMPARE_SUC]
  \\ metis_tac []
QED

Theorem LESS_EQ_IMP_APPEND_ALT:
  !n xs. n <= LENGTH xs ==> ?ys zs. xs = ys ++ zs /\ LENGTH zs = n
Proof
  Induct \\ fs [LENGTH_NIL] \\ Cases_on `xs` \\ fs []
  \\ rw [] \\ res_tac \\ rpt BasicProvers.VAR_EQ_TAC
  \\ Cases_on `ys` \\ fs [] THEN1 (qexists_tac `[]` \\ fs [])
  \\ qexists_tac `BUTLAST (h::h'::t)` \\ fs []
  \\ qexists_tac `LAST (h::h'::t) :: zs` \\ fs []
  \\ fs [APPEND_FRONT_LAST]
QED

Theorem LASTN_CONS_IMP_LENGTH:
  !xs n y ys.
     n <= LENGTH xs ==>
     (LASTN n xs = y::ys) ==> LENGTH (y::ys) = n
Proof
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT]
  \\ srw_tac[][] THEN1 decide_tac \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]
QED

Theorem LASTN_IMP_APPEND:
  !xs n ys.
     n <= LENGTH xs /\ (LASTN n xs = ys) ==>
     ?zs. xs = zs ++ ys /\ LENGTH ys = n
Proof
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][] THEN1 decide_tac
  \\ `n <= LENGTH xs` by decide_tac \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `xs = zs ++ LASTN n xs` (fn th => simp [Once th])
QED

Theorem NOT_NIL_IMP_LAST:
  !xs x. xs <> [] ==> LAST (x::xs) = LAST xs
Proof
  Cases \\ full_simp_tac(srw_ss())[]
QED

(* --- MAPi --- *)

Theorem MAPi_SNOC:
  !xs x f. MAPi f (SNOC x xs) = SNOC (f (LENGTH xs) x) (MAPi f xs)
Proof
  Induct \\ fs [SNOC,SNOC_APPEND]
QED

(* --- ALOOKUP --- *)

Theorem ALOOKUP_MAP_3:
  (!x. MEM x xs ==> FST (f x) = FST x) ==>
  ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x, y))) (ALOOKUP xs x)
Proof
  Induct_on `xs` \\ rw []
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ Cases_on `f h`
  \\ Cases_on `h`
  \\ rw []
  \\ fs []
QED

(* --- ZIP / EVERY2 / REPLICATE lemmas --- *)

Theorem ZIP_REPLICATE:
  !n. ZIP (REPLICATE n x, REPLICATE n y) = REPLICATE n (x,y)
Proof
  Induct \\ fs [REPLICATE]
QED

Theorem EVERY2_IMP_EVERY:
  !xs ys. EVERY2 P xs ys ==> EVERY (\(x,y). P y x) (ZIP(ys,xs))
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[]
QED

Theorem EVERY2_IMP_EVERY2:
  !xs ys P1 P2.
     (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
     EVERY2 P1 xs ys ==> EVERY2 P2 xs ys
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac \\ metis_tac []
QED
