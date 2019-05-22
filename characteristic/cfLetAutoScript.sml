(*
  Definitions and lemmas that support the implementation of the
  xlet_auto tactic.
*)
open preamble ml_translatorTheory cfTacticsLib set_sepTheory cfHeapsBaseTheory cfStoreTheory Satisfy

val _ = new_theory "cfLetAuto";

(* Rewrite rules for the int_of_num & operator*)
Theorem INT_OF_NUM_ADD:
 !(x:num) (y:num).(&x) + &y = &(x+y)
Proof
rw[] >> intLib.ARITH_TAC
QED
Theorem INT_OF_NUM_TIMES:
 !(x:num) (y:num).(&x) * &y = &(x*y)
Proof
rw[] >> intLib.ARITH_TAC
QED
Theorem INT_OF_NUM_LE:
 !(x:num) (y:num). (&x <= (&y):int) = (x <= y)
Proof
rw[]
QED
Theorem INT_OF_NUM_LESS:
 !(x:num) (y:num). (&x < (&y):int) = (x < y)
Proof
rw[]
QED
Theorem INT_OF_NUM_GE:
 !(x:num) (y:num). (&x >= (&y):int) = (x >= y)
Proof
rw[] >> intLib.ARITH_TAC
QED
Theorem INT_OF_NUM_GREAT:
 !(x:num) (y:num). (&x > (&y):int) = (x > y)
Proof
rw[] >> intLib.ARITH_TAC
QED
Theorem INT_OF_NUM_EQ:
 !(x:num) (y:num). (&x = (&y):int) = (x = y)
Proof
rw[] >> intLib.ARITH_TAC
QED
Theorem INT_OF_NUM_SUBS:
 !(x:num) (y:num) (z:num). (&x - (&y):int = &z) <=> (x - y = z) /\ y <= x
Proof
rw[] >> intLib.ARITH_TAC
QED
Theorem INT_OF_NUM_SUBS_2:
 !(x:num) (y:num). y <= x ==> (&x - (&y):int = &(x - y))
Proof
rw[] >> fs[int_arithTheory.INT_NUM_SUB]
QED

(* TODO: move that *)
Theorem SPLIT_SUBSET:
 SPLIT s (u, v) ==> u SUBSET s /\ v SUBSET s
Proof
rw[SPLIT_def] >> fs[SUBSET_UNION]
QED

(* Predicate stating that a heap is valid *)
val HEAP_FROM_STATE_def =
    Define `HEAP_FROM_STATE s = ?(f : ffi ffi_proj) st. s = (st2heap f st)`;

val VALID_HEAP_def =
    Define `VALID_HEAP s = ?(f : ffi ffi_proj) st. s SUBSET (st2heap f st)`;

Theorem VALID_HEAP_SUBSET:
 VALID_HEAP s1 ==> s2 SUBSET s1 ==> VALID_HEAP s2
Proof
rw[VALID_HEAP_def] >> metis_tac[SUBSET_TRANS]
QED

(* A theorem to remove the pure facts from the heap predicates *)
Theorem HCOND_EXTRACT:
 ((&A * H) s <=> A /\ H s) /\ ((H * &A) s <=> H s /\ A) /\ ((H * &A * H') s <=> (H * H') s /\ A)
Proof
rw[] >-(fs[STAR_def, STAR_def, cond_def, SPLIT_def])
>-(fs[STAR_def, STAR_def, cond_def, SPLIT_def]) >>
fs[STAR_def, STAR_def, cond_def, SPLIT_def] >> EQ_TAC >-(rw [] >-(instantiate) >> rw[]) >> rw[]
QED

(* Definitions and theorems used to compare two heap conditions *)
val HPROP_INJ_def = Define `HPROP_INJ H1 H2 PF <=>
!s. VALID_HEAP s ==> !G1 G2. (H1 * G1) s ==> ((H2 * G2) s <=> (&PF * H1 * G2) s)`;

(* TODO: use that *)
(* val HPROP_FRAME_IMP_def = Define `HPROP_FRAME_IMP H1 H2 Frame <=>
?s. VALID_HEAP s /\ H1 s /\ (H2 * Frame) s`;

Theorem HPROP_FRAME_HCOND:
 HPROP_FRAME_IMP H1 (&PF * H2) Frame <=> PF /\ HPROP_FRAME_IMP H1 H2 Frame
Proof
rw[HPROP_FRAME_IMP_def, GSYM STAR_ASSOC, HCOND_EXTRACT, GSYM RIGHT_EXISTS_AND_THM] >>
metis_tac[]
QED *)

(* The following lemmas aim to prove that a valid heap can not have one pointer pointing to two different values *)
val PTR_MEM_LEM = Q.prove(`!s l xv H. (l ~~>> xv * H) s ==> Mem l xv IN s`,
rw[STAR_def, SPLIT_def, cell_def, one_def] >> fs[]);

(* Intermediate lemma to reason on subsets of heaps *)
val HEAP_SUBSET_GC = Q.prove(`!s s' H. s SUBSET s' ==> H s ==> (H * GC) s'`,
rw[STAR_def] >>
instantiate >>
fs[SPLIT_EQ, GC_def, SEP_EXISTS] >>
qexists_tac `\x. T` >>
rw[]);

(* UNIQUE_PTRS property for a heap converted from a state *)
val UNIQUE_PTRS_HFS = Q.prove(
`!s. HEAP_FROM_STATE s ==> !l xv xv' H H'. (l ~~>> xv * H) s /\ (l ~~>> xv' * H') s ==> xv' = xv`,
rw[HEAP_FROM_STATE_def] >>
fs[st2heap_def] >>
IMP_RES_TAC PTR_MEM_LEM >>
fs[UNION_DEF]
>-(IMP_RES_TAC store2heap_IN_unique_key)>>
IMP_RES_TAC Mem_NOT_IN_ffi2heap);

Theorem UNIQUE_PTRS:
 !s. VALID_HEAP s ==> !l xv xv' H H'. (l ~~>> xv * H) s /\ (l ~~>> xv' * H') s ==> xv' = xv
Proof
rw[VALID_HEAP_def] >>
IMP_RES_TAC HEAP_SUBSET_GC >>
fs[GSYM STAR_ASSOC] >>
metis_tac[HEAP_FROM_STATE_def, UNIQUE_PTRS_HFS]
QED

Theorem PTR_IN_HEAP:
 !l xv H s. (REF (Loc l) xv * H) s ==> Mem l (Refv xv) IN s
Proof
fs[STAR_def, SPLIT_def] >>
fs[REF_def, SEP_EXISTS] >>
fs[HCOND_EXTRACT] >>
fs[cell_def, one_def] >>
rw[] >>
last_x_assum (fn x => rw[GSYM x])
QED

fun prove_hprop_inj_tac thm = rw[HPROP_INJ_def, SEP_CLAUSES, GSYM STAR_ASSOC, HCOND_EXTRACT] >>
                                metis_tac[thm];

Theorem PTR_HPROP_INJ:
 !l xv xv'. HPROP_INJ (l ~~>> xv) (l ~~>> xv') (xv' = xv)
Proof
prove_hprop_inj_tac UNIQUE_PTRS
QED

(* Unicity results for pointers *)
val solve_unique_refs = (rw[] >> qspec_then `s:heap` ASSUME_TAC UNIQUE_PTRS >>
    fs[REF_def, ARRAY_def, W8ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
    `!A H1 H2. (&A * H1 * H2) s <=> A /\ (H1 * H2) s` by metis_tac[HCOND_EXTRACT, STAR_COMM] >>
    POP_ASSUM (fn x => fs[x]) >> rw[] >> POP_ASSUM IMP_RES_TAC >> fs[]);

Theorem UNIQUE_REFS:
 !s r xv xv' H H'. VALID_HEAP s ==> (r ~~> xv * H) s /\ (r ~~> xv' * H') s ==> xv' = xv
Proof
solve_unique_refs
QED

Theorem UNIQUE_ARRAYS:
 !s a av av' H H'. VALID_HEAP s ==> (ARRAY a av * H) s /\ (ARRAY a av' * H') s ==> av' = av
Proof
solve_unique_refs
QED

Theorem UNIQUE_W8ARRAYS:
 !s a av av' H H'. VALID_HEAP s ==> (W8ARRAY a av * H) s /\ (W8ARRAY a av' * H') s ==> av' = av
Proof
solve_unique_refs
QED

Theorem REF_HPROP_INJ:
 !r xv xv'. HPROP_INJ (REF r xv) (REF r xv') (xv' = xv)
Proof
prove_hprop_inj_tac UNIQUE_REFS
QED

Theorem ARRAY_HPROP_INJ:
 !a av av'. HPROP_INJ (ARRAY a av) (ARRAY a av') (av' = av)
Proof
prove_hprop_inj_tac UNIQUE_ARRAYS
QED

Theorem W8ARRAY_HPROP_INJ:
 !a av av'. HPROP_INJ (W8ARRAY a av) (W8ARRAY a av') (av' = av)
Proof
prove_hprop_inj_tac UNIQUE_W8ARRAYS
QED

(* A valid heap must have proper ffi partitions *)
val NON_OVERLAP_FFI_PART_HFS = Q.prove(
`!s. HEAP_FROM_STATE s ==>
!s1 u1 ns1 ts1 s2 u2 ns2 ts2. FFI_part s1 u1 ns1 ts1 IN s /\ FFI_part s2 u2 ns2 ts2 IN s /\ (?p. MEM p ns1 /\ MEM p ns2) ==>
s2 = s1 /\ u2 = u1 /\ ns2 = ns1 /\ ts2 = ts1`,
rpt (FIRST[GEN_TAC, DISCH_TAC]) >>
fs[HEAP_FROM_STATE_def, st2heap_def, UNION_DEF] >>
`FFI_part s1 u1 ns1 ts1 ∈ ffi2heap f st.ffi` by (rw[] >> fs[FFI_part_NOT_IN_store2heap]) >>
`FFI_part s2 u2 ns2 ts2 ∈ ffi2heap f st.ffi` by (rw[] >> fs[FFI_part_NOT_IN_store2heap]) >>
Cases_on `f` >>
Q.RENAME_TAC [`(q, r)`, `(proj, parts)`] >>
fs[ffi2heap_def] >>
Cases_on `parts_ok st.ffi (proj, parts)`
>-(
    fs[] >>
    fs[parts_ok_def] >>
    sg `ns2 = ns1`
    >-(
       `MEM ns1 (MAP FST parts)` by
       (
           `?n. n < LENGTH parts /\ (ns1, u1) = EL n parts` by (IMP_RES_TAC MEM_EL >> SATISFY_TAC) >>
           `FST (EL n parts) = ns1` by FIRST_ASSUM (fn x => fs[GSYM x, FST]) >>
           `n < LENGTH (MAP FST parts)` by fs[LENGTH_MAP] >>
           `EL n (MAP FST parts) = FST (EL n parts)` by fs[EL_MAP] >>
           metis_tac[GSYM MEM_EL]
       ) >>
       `MEM ns2 (MAP FST parts)` by
       (
           `?n. n < LENGTH parts /\ (ns2, u2) = EL n parts` by (IMP_RES_TAC MEM_EL >> SATISFY_TAC) >>
           `FST (EL n parts) = ns2` by FIRST_ASSUM (fn x => fs[GSYM x, FST]) >>
           `n < LENGTH (MAP FST parts)` by fs[LENGTH_MAP] >>
           `EL n (MAP FST parts) = FST (EL n parts)` by fs[EL_MAP] >>
           metis_tac[GSYM MEM_EL]
       ) >>
       metis_tac[cfTheory.ALL_DISTINCT_FLAT_MEM_IMP]
    ) >>
    (* Simplify the goal *)
    fs[] >>

    (* s2 = s1 *)
    `FLOOKUP (proj st.ffi.ffi_state) p = SOME s1` by metis_tac[] >>
    `FLOOKUP (proj st.ffi.ffi_state) p = SOME s2` by metis_tac[] >>
    fs[] >>

    (* u2 = u1 *)
    IMP_RES_TAC ALL_DISTINCT_FLAT_FST_IMP
) >>
fs[]);

Theorem NON_OVERLAP_FFI_PART:
 !s. VALID_HEAP s ==>
!s1 u1 ns1 ts1 s2 u2 ns2 ts2. FFI_part s1 u1 ns1 ts1 IN s /\ FFI_part s2 u2 ns2 ts2 IN s /\ (?p. MEM p ns1 /\ MEM p ns2) ==>
s2 = s1 /\ u2 = u1 /\ ns2 = ns1 /\ ts2 = ts1
Proof
rpt (FIRST[GEN_TAC, DISCH_TAC]) >>
fs[VALID_HEAP_def] >>
`HEAP_FROM_STATE (st2heap f st)` by metis_tac[GSYM HEAP_FROM_STATE_def] >>
IMP_RES_TAC SUBSET_DEF >>
IMP_RES_TAC NON_OVERLAP_FFI_PART_HFS >>
rw[]
QED

(* A minor lemma *)
val FFI_PORT_IN_HEAP_LEM = Q.prove(
`!s u ns events H h. (one (FFI_part s u ns events) * H) h ==> FFI_part s u ns events IN h`,
rw[one_def, STAR_def, SPLIT_def, IN_DEF, UNION_DEF] >> rw[]);

(* Another important theorem *)
Theorem FRAME_UNIQUE_IO:
 !s. VALID_HEAP s ==>
!s1 u1 ns1 s2 u2 ns2 H1 H2.
(IO s1 u1 ns1 * H1) s /\ (IO s2 u2 ns2 * H2) s ==>
(?pn. MEM pn ns1 /\ MEM pn ns2) ==>
s2 = s1 /\ u2 = u1 /\ ns2 = ns1
Proof
rpt (FIRST[GEN_TAC, DISCH_TAC]) >>
fs[IO_def, SEP_CLAUSES, SEP_EXISTS_THM] >>
full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] >>
IMP_RES_TAC FFI_PORT_IN_HEAP_LEM >>
IMP_RES_TAC NON_OVERLAP_FFI_PART >>
fs[]
QED

Theorem IO_HPROP_INJ:
 !s1 u1 ns1 s2 u2 ns2 H1 H2. (?pn. MEM pn ns1 /\ MEM pn ns2) ==>
HPROP_INJ (IO s1 u1 ns1) (IO s2 u2 ns2) (s2 = s1 /\ u2 = u1 /\ ns2 = ns1)
Proof
rw[HPROP_INJ_def] >>
fs[IO_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM, HCOND_EXTRACT] >>
metis_tac[FFI_PORT_IN_HEAP_LEM, NON_OVERLAP_FFI_PART]
QED

(* Theorems and rewrites for REPLICATE and LIST_REL *)
Theorem APPEND_LENGTH_INEQ:
 !l1 l2. LENGTH(l1) <= LENGTH(l1++l2) /\ LENGTH(l2) <= LENGTH(l1++l2)
Proof
Induct >-(strip_tac >> rw[]) >> rw[]
QED

val REPLICATE_APPEND_RIGHT = Q.prove(
`a++b = REPLICATE n x ==> b = REPLICATE (LENGTH b) x`,
strip_tac >>
`b = DROP (LENGTH a) (a++b)` by simp[GSYM DROP_LENGTH_APPEND] >>
`b = DROP (LENGTH a) (REPLICATE n x)` by POP_ASSUM (fn thm => metis_tac[thm]) >>
`b = REPLICATE (n - (LENGTH a)) x` by POP_ASSUM (fn thm => metis_tac[thm, DROP_REPLICATE]) >>
fs[LENGTH_REPLICATE]);

val REPLICATE_APPEND_LEFT = Q.prove(
`a++b = REPLICATE n x ==> a = REPLICATE (LENGTH a) x`,
strip_tac >> `b = REPLICATE (LENGTH b) x` by metis_tac[REPLICATE_APPEND_RIGHT] >>
`LENGTH b <= n` by metis_tac[APPEND_LENGTH_INEQ, LENGTH_REPLICATE] >>
`REPLICATE n x = REPLICATE (n-(LENGTH b)) x ++ REPLICATE (LENGTH b) x` by simp[REPLICATE_APPEND] >>
POP_ASSUM (fn x => fs[x]) >> POP_ASSUM (fn x => ALL_TAC) >>
`a ++ REPLICATE (LENGTH b) x = REPLICATE (n − LENGTH b) x ++ REPLICATE (LENGTH b) x` by metis_tac[] >>
fs[LENGTH_REPLICATE]);

Theorem REPLICATE_APPEND_DECOMPOSE:
 a ++ b = REPLICATE n x <=>
a = REPLICATE (LENGTH a) x /\ b = REPLICATE (LENGTH b) x /\ LENGTH a + LENGTH b = n
Proof
EQ_TAC >-(rw[] >-(metis_tac[REPLICATE_APPEND_LEFT]) >-(metis_tac[REPLICATE_APPEND_RIGHT]) >> metis_tac [LENGTH_REPLICATE, LENGTH_APPEND]) >> metis_tac[REPLICATE_APPEND]
QED

val REPLICATE_APPEND_DECOMPOSE_SYM = save_thm("REPLICATE_APPEND_DECOMPOSE_SYM",
CONV_RULE(PATH_CONV "lr" SYM_CONV) REPLICATE_APPEND_DECOMPOSE);

Theorem REPLICATE_PLUS_ONE:
 REPLICATE (n + 1) x = x::REPLICATE n x
Proof
`n+1 = SUC n` by rw[] >> rw[REPLICATE]
QED

val LIST_REL_DECOMPOSE_RIGHT_recip = Q.prove(
`!R. LIST_REL R (a ++ b) x ==> LIST_REL R a (TAKE (LENGTH a) x) /\ LIST_REL R b (DROP (LENGTH a) x)`,
strip_tac >> strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
`LENGTH (a ++ b) = LENGTH x` by (MATCH_MP_TAC LIST_REL_LENGTH >> rw[]) >>
POP_ASSUM (fn x => CONV_RULE (SIMP_CONV list_ss []) x |> ASSUME_TAC) >>
`LENGTH a <= LENGTH x` by bossLib.DECIDE_TAC >>
metis_tac[LENGTH_TAKE, LIST_REL_APPEND_IMP]);

val LIST_REL_DECOMPOSE_RIGHT_imp = Q.prove(
`!R. LIST_REL R a (TAKE (LENGTH a) x) /\ LIST_REL R b (DROP (LENGTH a) x) ==> LIST_REL R (a ++ b) x`,
rpt strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

Theorem LIST_REL_DECOMPOSE_RIGHT:
 !R. LIST_REL R (a ++ b) x <=> LIST_REL R a (TAKE (LENGTH a) x) /\ LIST_REL R b (DROP (LENGTH a) x)
Proof
strip_tac >> metis_tac[LIST_REL_DECOMPOSE_RIGHT_recip, LIST_REL_DECOMPOSE_RIGHT_imp]
QED

val LIST_REL_DECOMPOSE_LEFT_recip = Q.prove(
`!R. LIST_REL R x (a ++ b) ==> LIST_REL R (TAKE (LENGTH a) x) a /\ LIST_REL R (DROP (LENGTH a) x) b`,
strip_tac >> strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
`LENGTH x = LENGTH (a ++ b)` by (MATCH_MP_TAC LIST_REL_LENGTH >> rw[]) >>
POP_ASSUM (fn x => CONV_RULE (SIMP_CONV list_ss []) x |> ASSUME_TAC) >>
`LENGTH a <= LENGTH x` by bossLib.DECIDE_TAC >>
metis_tac[LENGTH_TAKE, LIST_REL_APPEND_IMP]);

val LIST_REL_DECOMPOSE_LEFT_imp = Q.prove(
`!R. LIST_REL R (TAKE (LENGTH a) x) a /\ LIST_REL R (DROP (LENGTH a) x) b ==> LIST_REL R x (a ++ b)`,
rpt strip_tac >>
`x = TAKE (LENGTH a) x ++ DROP (LENGTH a) x` by rw[TAKE_DROP] >>
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

Theorem LIST_REL_DECOMPOSE_LEFT:
 !R. LIST_REL R x (a ++ b) <=> LIST_REL R (TAKE (LENGTH a) x) a /\ LIST_REL R (DROP (LENGTH a) x) b
Proof
strip_tac >> metis_tac[LIST_REL_DECOMPOSE_LEFT_recip, LIST_REL_DECOMPOSE_LEFT_imp]
QED

Theorem HEAD_TAIL:
 l <> [] ==> HD l :: TL l = l
Proof
Cases_on `l:'a list` >> rw[listTheory.TL, listTheory.HD]
QED

Theorem HEAD_TAIL_DECOMPOSE_RIGHT:
 x::a = b <=> b <> [] /\ x = HD b /\ a = TL b
Proof
rw[] >> EQ_TAC
>-(Cases_on `b:'a list` >-(rw[]) >>  rw[listTheory.TL, listTheory.HD, HEAD_TAIL]) >>
rw[HEAD_TAIL]
QED

Theorem HEAD_TAIL_DECOMPOSE_LEFT:
 b = x::a <=> b <> [] /\ x = HD b /\ a = TL b
Proof
rw[] >> EQ_TAC
>-(Cases_on `b:'a list` >-(rw[]) >>  rw[listTheory.TL, listTheory.HD, HEAD_TAIL]) >>
rw[HEAD_TAIL]
QED

val _ = hide "abs";

(* Theorems used as rewrites for the refinement invariants *)
fun eqtype_unicity_thm_tac x =
  let
      val assum = MP (SPEC ``abs:'a -> v -> bool`` EqualityType_def |> EQ_IMP_RULE |> fst) x
  in
      MP_TAC assum
  end;

Theorem EQTYPE_UNICITY_R:
 !abs x y1 y2. EqualityType abs ==> abs x y1 ==> (abs x y2 <=> y2 = y1)
Proof
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]
QED

Theorem EQTYPE_UNICITY_L:
 !abs x1 x2 y. EqualityType abs ==> abs x1 y ==> (abs x2 y <=> x2 = x1)
Proof
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]
QED

(* Theorems to use LIST_REL A "as a" refinement invariant *)
val InjectiveRel_def = Define `
InjectiveRel A = !x1 y1 x2 y2. A x1 y1 /\ A x2 y2 ==> (x1 = x2 <=> y1 = y2)`;

val EQTYPE_INJECTIVEREL = Q.prove(`EqualityType A ==> InjectiveRel A`,
rw[InjectiveRel_def, EqualityType_def]);

Theorem LIST_REL_INJECTIVE_REL:
 !A. InjectiveRel A ==> InjectiveRel (LIST_REL A)
Proof
rpt strip_tac >> SIMP_TAC list_ss [InjectiveRel_def] >> Induct_on `x1`
>-(
    rpt strip_tac >>
    fs[LIST_REL_NIL] >>
    EQ_TAC >>
    rw[LIST_REL_NIL] >>
    fs[LIST_REL_NIL]
) >>
rpt strip_tac >> fs[LIST_REL_def] >>
Cases_on `x2` >-(fs[LIST_REL_NIL]) >>
Cases_on `y2` >-(fs[LIST_REL_NIL]) >>
rw[] >> fs[LIST_REL_def] >>
EQ_TAC >> (rw[] >-(metis_tac[InjectiveRel_def]) >> metis_tac[])
QED

Theorem LIST_REL_INJECTIVE_EQTYPE:
 !A. EqualityType A ==> InjectiveRel (LIST_REL A)
Proof
metis_tac[EQTYPE_INJECTIVEREL, LIST_REL_INJECTIVE_REL]
QED

Theorem LIST_REL_UNICITY_RIGHT:
 EqualityType A ==> LIST_REL A a b ==> (LIST_REL A a b' <=> b' = b)
Proof
metis_tac[EQTYPE_INJECTIVEREL, LIST_REL_INJECTIVE_EQTYPE, InjectiveRel_def]
QED

Theorem LIST_REL_UNICITY_LEFT:
 EqualityType A ==> LIST_REL A a b ==> (LIST_REL A a' b <=> a' = a)
Proof
metis_tac[EQTYPE_INJECTIVEREL, LIST_REL_INJECTIVE_EQTYPE, InjectiveRel_def]
QED

(* EqualityType proofs *)
Theorem EqualityType_PAIR_TYPE:
 EqualityType A ==> EqualityType B ==> EqualityType (PAIR_TYPE A B)
Proof
rw[EqualityType_def]
>-(
    Cases_on `x1` >>
    fs[PAIR_TYPE_def, no_closures_def] >>
    metis_tac[]
) >>
Cases_on `x1` >>
Cases_on `x2` >>
fs[PAIR_TYPE_def, types_match_def, semanticPrimitivesTheory.ctor_same_type_def] >>
metis_tac[]
QED

val LIST_TYPE_no_closure = Q.prove(
`!A x xv. EqualityType A ==> LIST_TYPE A x xv ==> no_closures xv`,
Induct_on `x`
>-(fs[LIST_TYPE_def, no_closures_def]) >>
rw[LIST_TYPE_def] >>
rw[no_closures_def]
>-(metis_tac[EqualityType_def]) >>
last_assum IMP_RES_TAC);

val LIST_TYPE_inj = Q.prove(
`!A x1 x2 v1 v2. EqualityType A ==> LIST_TYPE A x1 v1 ==> LIST_TYPE A x2 v2 ==>
(v1 = v2 <=> x1 = x2)`,
Induct_on `x1`
>-(
    Cases_on `x2` >>
    rw[LIST_TYPE_def, EqualityType_def]
) >>
Cases_on `x2` >-(rw[LIST_TYPE_def]) >>
rw[LIST_TYPE_def] >>
last_x_assum IMP_RES_TAC >>
rw[] >>
fs[EqualityType_def] >>
metis_tac[]);

val types_match_tac = rpt (CHANGED_TAC (rw[LIST_TYPE_def, types_match_def, semanticPrimitivesTheory.ctor_same_type_def]));
val LIST_TYPE_types_match = Q.prove(
`!A x1 x2 v1 v2. EqualityType A ==> LIST_TYPE A x1 v1 ==> LIST_TYPE A x2 v2 ==>
types_match v1 v2`,
Induct_on `x1`
>-(
    Cases_on `x2` >>
    types_match_tac >>
    EVAL_TAC
) >>
Cases_on `x2`
>-(types_match_tac >> EVAL_TAC)>>
types_match_tac
>-(metis_tac[EqualityType_def])>>
last_assum IMP_RES_TAC);

Theorem EqualityType_LIST_TYPE:
 EqualityType A ==> EqualityType (LIST_TYPE A)
Proof
DISCH_TAC >> rw[EqualityType_def]
>-(IMP_RES_TAC LIST_TYPE_no_closure)
>-(IMP_RES_TAC LIST_TYPE_inj) >>
IMP_RES_TAC LIST_TYPE_types_match
QED

(* Some theorems for rewrite rules with the refinement invariants *)

(* Need to write the expand and retract theorems for UNIT_TYPE by hand - otherwise the retract theorem might introduce a variable, for example *)
Theorem UNIT_TYPE_RETRACT:
 !v. v = Conv NONE [] <=> UNIT_TYPE () v
Proof
rw[UNIT_TYPE_def]
QED

Theorem UNIT_TYPE_EXPAND:
 !u v. UNIT_TYPE u v <=> u = () /\ v = Conv NONE []
Proof
rw[UNIT_TYPE_def]
QED

Theorem NUM_INT_EQ:
 (!x y v. INT x v ==> (NUM y v <=> x = &y)) /\
(!x y v. NUM y v ==> (INT x v <=> x = &y)) /\
(!x v w. INT (&x) v ==> (NUM x w <=> w = v)) /\
(!x v w. NUM x v ==> (INT (&x) w <=> w = v))
Proof
fs[INT_def, NUM_def] >> metis_tac[]
QED

(* Some rules used to simplify arithmetic equations (not happy with that: write a conversion instead? *)

val NUM_EQ_lem = Q.prove(`!(a1:num) (a2:num) (b:num). b <= a1 ==> b <= a2 ==> (a1 = a2 <=> a1 - b = a2 - b)`, rw[]);

Theorem NUM_EQ_SIMP1:
 a1 + (NUMERAL n1)*b = a2 + (NUMERAL n2)*b <=>
a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b = a2 + (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b
Proof
  rw[MIN_DEF]
>-(
   `b*NUMERAL n1 <= a1 + b*NUMERAL n1` by rw[] >>
   `b*NUMERAL n1 <= a2 + b*NUMERAL n2` by (
      rw[] >>
      `b*NUMERAL n2 <= a2 + b*NUMERAL n2` by rw[] >>
      `b*NUMERAL n1 <= b*NUMERAL n2` by rw[] >>
      bossLib.DECIDE_TAC
   ) >>
   qspecl_then [`a1 + b * NUMERAL n1`, `a2 + b * NUMERAL n2`, `b * NUMERAL n1`] assume_tac NUM_EQ_lem >>
   POP_ASSUM (fn x => rw[x]) >>
   `b * (NUMERAL n2 - NUMERAL n1) = b * NUMERAL n2 - b * NUMERAL n1` by rw[] >>
   POP_ASSUM (fn x => rw[x]) >>
   `b*NUMERAL n1 <= b* NUMERAL n2` by rw[] >>
   bossLib.DECIDE_TAC
) >>
  `b*NUMERAL n1 <= a2 + b*NUMERAL n1` by rw[] >>
  `b*NUMERAL n2 <= b*NUMERAL n1` by rw[] >>
  `b*NUMERAL n2 <= a1 + b*NUMERAL n1` by rw[] >>
  `b*NUMERAL n2 <= a2 + b*NUMERAL n2` by rw[] >>
  qspecl_then[`a1 + b * NUMERAL n1`, `a2 + b * NUMERAL n2`, `b * NUMERAL n2`]assume_tac NUM_EQ_lem >>
  POP_ASSUM (fn x => rw[x])
QED

Theorem NUM_EQ_SIMP2:
 (NUMERAL n1)*b + a1 = (NUMERAL n2)*b + a2 <=>
(NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a1 = (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP1]
QED

Theorem NUM_EQ_SIMP3:
 a1 + (NUMERAL n1)*b = (NUMERAL n2)*b + a2 <=>
a1 + (NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b = (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP1]
QED

Theorem NUM_EQ_SIMP4:
 (NUMERAL n1)*b + a1 = a2 + (NUMERAL n2)*b <=>
(NUMERAL n1 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a1 = (NUMERAL n2 - (MIN (NUMERAL n1) (NUMERAL n2)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP1]
QED

Theorem NUM_EQ_SIMP5:
 a1 + b = a2 + (NUMERAL n2)*b <=>
a1 + (1 - (MIN 1 (NUMERAL n2)))*b = a2 + (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b
Proof
`a1 + b = a1 + 1*b` by rw[] >>
POP_ASSUM (fn x => PURE_REWRITE_TAC [x]) >>
metis_tac[NUM_EQ_SIMP1]
QED

Theorem NUM_EQ_SIMP6:
 a1 + (NUMERAL n1)*b = a2 + b <=>
a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b = a2 + (1 - (MIN 1 (NUMERAL n1)))*b
Proof
`a2 + b = a2 + 1*b` by rw[] >>
POP_ASSUM (fn x => PURE_REWRITE_TAC [x]) >>
metis_tac[NUM_EQ_SIMP1]
QED

Theorem NUM_EQ_SIMP7:
 b + a1 = (NUMERAL n2)*b + a2 <=>
(1 - (MIN 1 (NUMERAL n2)))*b + a1 = (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP5]
QED

Theorem NUM_EQ_SIMP8:
 (NUMERAL n1)*b + a1 = b + a2 <=>
(NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b + a1 = (1 - (MIN 1 (NUMERAL n1)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP6]
QED

Theorem NUM_EQ_SIMP9:
 a1 + b = (NUMERAL n2)*b + a2 <=>
a1 + (1 - (MIN 1 (NUMERAL n2)))*b = (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP5]
QED

Theorem NUM_EQ_SIMP10:
 b + a1 = a2 + (NUMERAL n2)*b <=>
(1 - (MIN 1 (NUMERAL n2)))*b + a1 = a2 + (NUMERAL n2 - (MIN 1 (NUMERAL n2)))*b
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP5]
QED

Theorem NUM_EQ_SIMP11:
 a1 + (NUMERAL n1)*b = b + a2 <=>
a1 + (NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b = (1 - (MIN 1 (NUMERAL n1)))*b + a2
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP6]
QED

Theorem NUM_EQ_SIMP12:
 (NUMERAL n1)*b + a1 = a2 + b <=>
(NUMERAL n1 - (MIN 1 (NUMERAL n1)))*b + a1 = a2 + (1 - (MIN 1 (NUMERAL n1)))*b
Proof
rw[CONV_RULE (SIMP_CONV arith_ss []) NUM_EQ_SIMP6]
QED

val _ = export_theory();
