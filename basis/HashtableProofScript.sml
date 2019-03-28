(*
  Proofs about the Array module.
  load "cfLib";
  load "HashtableProgTheory";
  load "ArrayProofTheory";
*)

open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory ArrayProgTheory ArrayProofTheory ListProgTheory
     MapProgTheory HashtableProgTheory
     comparisonTheory;

val _ = new_theory"HashtableProof";

val _ = translation_extends "HashtableProg";

val hashtable_st = get_ml_prog_state();

(*  ----------------------------------- *)

(* the union of each bucket is the heap *)
(* the vlv list contains the buckets *)
(* each bucket only contains keys that hash there *)

val hash_key_set_def = Define`
  hash_key_set hf length idx  = { k' | hf k' MOD length = idx }`;

val bucket_ok_def = Define `
bucket_ok b hf idx length  = !k v.
      (mlmap$lookup b k = SOME v ==> k ∈ (hash_key_set hf length idx))`;

val buckets_empty_def = Define `
  buckets_empty bs = (MAP mlmap$to_fmap bs = (REPLICATE (LENGTH bs) FEMPTY))`;


val buckets_to_fmap_def = Define `
  buckets_to_fmap xs = alist_to_fmap (FLAT (MAP mlmap$toAscList xs))`;

val list_union_def = Define `
  list_union [x] = x /\
  list_union (x::xs) = mlmap$union x (list_union xs)`;

val buckets_ok_def = Define `
   buckets_ok bs hf =
     !i. i < LENGTH bs ==>
       bucket_ok (EL i bs) hf i (LENGTH bs)`;

val hashtable_inv_def = Define `
  hashtable_inv a b hf cmp (h:('a|->'b)) vlv =
    ?buckets.
      h = to_fmap (list_union buckets) /\
      buckets_ok buckets hf /\
      0 <> (LENGTH vlv)  /\
      LIST_REL (MAP_TYPE a b) buckets vlv /\
      EVERY mlmap$map_ok buckets /\
      EVERY (\t. mlmap$cmp_of t = cmp) buckets`;



val REF_NUM_def = Define `
  REF_NUM loc n =
    SEP_EXISTS v. REF loc v * & (NUM n v)`;

val REF_ARRAY_def = Define `
  REF_ARRAY loc arr content = REF loc arr * ARRAY arr content`;



val HASHTABLE_def = Define
 `HASHTABLE a b hf cmp h v =
    SEP_EXISTS ur ar hfv vlv arr cmpv heuristic_size.
      &(v = (Conv (SOME (TypeStamp "Hashtable" 8)) [ur; ar; hfv; cmpv]) /\
        (a --> NUM) hf hfv /\
        (a --> a --> ORDERING_TYPE) cmp cmpv /\
        TotOrd cmp /\
        hashtable_inv a b hf cmp h vlv) *
      REF_NUM ur heuristic_size *
      REF_ARRAY ar arr vlv`;

Theorem hashtable_initBuckets_spec
 `!a b n nv cmp cmpv.
    (a --> a --> ORDERING_TYPE) cmp cmpv /\
    NUM n nv ==>
      app (p:'ffi ffi_proj) Hashtable_initBuckets_v [nv; cmpv]
      emp
      (POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE n mpv))`
  (xcf_with_def "Hashtable.initBuckets" Hashtable_initBuckets_v_def
  \\ xlet `POSTv r1. & (MAP_TYPE a b (mlmap$empty cmp) r1)`
    >-(xapp
    \\ simp[])
  \\ xapp_spec array_alloc_spec
  \\ xsimpl
  \\ asm_exists_tac
  \\ simp[]
  \\ asm_exists_tac
  \\ simp[]);

Theorem buckets_ok_empty
  `!n cmp hf. TotOrd cmp ==>
      buckets_ok (REPLICATE n (mlmap$empty cmp)) hf`
(rpt strip_tac
\\fs[EL_REPLICATE,TotOrder_imp_good_cmp,buckets_ok_def, bucket_ok_def,
  mlmapTheory.empty_thm,balanced_mapTheory.empty_thm,
  mlmapTheory.lookup_thm, balanced_mapTheory.lookup_thm,flookup_thm]);

Theorem list_union_cmp_of
  `!cmp h t.
    (h::t) <> [] /\
    EVERY (\t. cmp_of t = cmp) (h::t) /\
    EVERY map_ok (h::t) ==>
      cmp_of (list_union (h::t)) = cmp`
  (rpt strip_tac
  \\ Induct_on `(h::t)`
     >-(simp[])
     >-(rpt strip_tac
       \\Cases_on `t`
       >-(fs[list_union_def])
       >-(fs[list_union_def]
          \\ Cases_on `h'`
          \\ Cases_on `list_union (h''::t')`
          \\ fs[EVERY_DEF, mlmapTheory.union_def, mlmapTheory.cmp_of_def])));

Theorem list_union_map_ok
  `!cmp h t.
    (h::t) <> [] /\
    EVERY (\t. cmp_of t = cmp) (h::t) /\
    EVERY map_ok (h::t) ==>
      map_ok (list_union (h::t))`
  (rpt strip_tac
  \\ Induct_on `(h::t)`
     >-(simp[])
     >-(rpt strip_tac
       \\ Cases_on `t = []`
       \\ rw[]
       \\ fs[EVERY_DEF, list_union_def]
       >-(Cases_on `t`
          >-(fs[])
          >-(simp[list_union_def]
            \\imp_res_tac list_union_cmp_of
            \\rfs[]
            \\imp_res_tac mlmapTheory.union_thm
            \\rfs[]))));

Theorem list_union_thm
  `!cmp.
    (h::t) <> [] /\
    EVERY (\t. cmp_of t = cmp) (h::t) /\
    EVERY map_ok (h::t) ==>
      map_ok (list_union (h::t)) /\
      cmp_of (list_union (h::t)) = cmp /\
      (t = [] ==> to_fmap (list_union (h::t)) = to_fmap h ) /\
      (t <> [] ==> to_fmap (list_union (h::t)) = to_fmap h ⊌ to_fmap (list_union t))`
  (rpt strip_tac
  >-(fs[EVERY_DEF,list_union_map_ok])
  >-(fs[EVERY_DEF, list_union_cmp_of])
  >-(rw[]
    \\ fs[list_union_def])
  \\ Cases_on `t`
     >-(fs[])
     >-(simp[list_union_def]
       \\ imp_res_tac list_union_cmp_of
       \\ imp_res_tac list_union_map_ok
       \\ imp_res_tac mlmapTheory.union_thm
       \\ rfs[]
       \\ Cases_on `h`
       \\ Cases_on `list_union (h'::t')`
       \\ rfs[mlmapTheory.union_thm]));

Theorem list_union_empty_maps
  `!cmp.
    (h::t) <> [] /\
    EVERY ($=(mlmap$empty cmp)) (h::t) /\
    EVERY (\t. cmp_of t = cmp) (h::t) /\
    EVERY map_ok (h::t) ==>
      mlmap$to_fmap (list_union (h::t)) = FEMPTY`
  (rpt strip_tac
  \\ Induct_on `(h::t)`
  >-(simp[])
  >-(rpt strip_tac
    \\ Cases_on `t=[]`
    >-(rw[]
      \\ fs[EVERY_DEF, list_union_def]
      \\ ntac 2 (pop_assum kall_tac)
      \\ rveq
      \\ simp[mlmapTheory.empty_thm])
    >-(imp_res_tac list_union_thm
      \\rfs[]
      \\Cases_on `t`
      >-(fs[])
      >-(rfs[]
        \\ fs[EVERY_DEF]
        \\ ntac 12 (pop_assum kall_tac)
        \\ rveq
        \\ simp[mlmapTheory.empty_thm]))));

Theorem lookup_union_left_none
 `!m1 m2.
   map_ok m1 /\
   map_ok m2 /\
   cmp_of m1 = cmp_of m2 /\
   mlmap$lookup m1 k = NONE ==>
     mlmap$lookup m2 k = mlmap$lookup (mlmap$union m1 m2) k`
 (cases_on `m1`
 \\ cases_on `m2`
 \\ strip_tac
 \\ imp_res_tac mlmapTheory.union_thm
 \\ imp_res_tac mlmapTheory.lookup_thm
 \\ res_tac
 \\ fs[mlmapTheory.lookup_thm]
 \\ fs[FLOOKUP_FUNION]);

Theorem lookup_union_right_none
 `!m1 m2.
   map_ok m1 /\
   map_ok m2 /\
   cmp_of m1 = cmp_of m2 /\
   mlmap$lookup m2 k = NONE ==>
     mlmap$lookup m1 k = mlmap$lookup (mlmap$union m1 m2) k`
 (cases_on `m2`
 \\ cases_on `m1`
 \\ strip_tac
 \\ `map_ok (union (Map f' b') (Map f b))` by (imp_res_tac mlmapTheory.union_thm)
 \\ `to_fmap (union (Map f' b') (Map f b)) =
     to_fmap (Map f' b') ⊌ to_fmap (Map f b)`
        by (imp_res_tac mlmapTheory.union_thm \\ fs[])
 \\ fs[mlmapTheory.lookup_thm]
 \\ fs[FLOOKUP_FUNION]
 \\ CASE_TAC
 \\ imp_res_tac mlmapTheory.lookup_thm
 \\ res_tac
 \\ fs[] );

Theorem lookup_list_union_none
  `!xs.
    EVERY (\m. lookup m k = NONE) xs  /\ xs <> [] /\
    EVERY map_ok xs /\
    EVERY (\t. cmp_of t = cmp) xs ==>
      lookup (list_union xs) k = NONE`
  (Induct
  >-(fs[])
  >-(rpt strip_tac
    \\imp_res_tac list_union_thm
    \\simp[mlmapTheory.lookup_thm]
    \\Cases_on `xs=[]`
    >-(rfs[]
      \\fs[mlmapTheory.lookup_thm])
    >-(rfs[]
      \\res_tac
      \\Cases_on `xs`
      >-(fs[])
      >-( `map_ok (list_union (h'::t))` by (rw[] \\imp_res_tac list_union_thm
                                            \\rfs[LENGTH_NIL])
        \\imp_res_tac mlmapTheory.lookup_thm
        \\simp[FLOOKUP_FUNION]
        \\Cases_on `FLOOKUP (to_fmap h) k = NONE`
        >-(fs[])
        >-(fs[])
    ))));


Theorem to_fmap_list_union_APPEND
 `!xs ys. xs <> [] /\ ys <> [] /\
   EVERY map_ok (xs++ys) /\
   EVERY (\t. cmp_of t = cmp) (xs++ys) ==>
     mlmap$to_fmap (list_union (xs++ys)) =
     FUNION (mlmap$to_fmap (list_union xs)) (to_fmap (list_union ys))`
  (Induct
    >-(fs[])
  \\rpt strip_tac
  \\ cases_on `xs`
  \\fs[]
     >- (cases_on `ys`
         >- (fs[])
         >- (`map_ok (list_union (h'::t))` by fs[list_union_map_ok]
           \\`cmp_of (list_union (h'::t)) = cmp` by fs[list_union_cmp_of]
           \\fs[list_union_def, mlmapTheory.union_thm]))
     >- (fs[list_union_def]
       \\`map_ok (list_union (h'::t))` by fs[list_union_map_ok]
       \\`cmp_of (list_union (h'::t)) = cmp` by fs[list_union_cmp_of]
       \\`map_ok (list_union (h'::(t ++ ys)))` by fs[list_union_map_ok]
       \\`cmp_of (list_union (h'::(t ++ ys))) = cmp` by fs[list_union_cmp_of]
       \\fs[mlmapTheory.union_thm, FUNION_ASSOC]));

Theorem lookup_list_union_append_eq_right
 `!xs ys cmp.
   EVERY map_ok (xs++ys) /\
   EVERY (\t. cmp_of t = cmp) (xs++ys) /\
   EVERY (\m. lookup m k = NONE) xs /\ ys <> [] ==>
   lookup (list_union (xs ++ ys)) k = lookup (list_union ys) k`
 (  Induct
 \\ rpt strip_tac
   >- (simp[])
 \\ rpt strip_tac
 \\ fs[list_union_def]
 \\ cases_on `xs`
   >- (res_tac
     \\ fs[] \\ rw[]
     \\ cases_on `ys`
       >- ( fs[] )
       >- ( fs[list_union_def]
           \\ rw[]
           \\ `EVERY (\t. cmp_of t = cmp_of h) (h'::t)`
             by (imp_res_tac EVERY_DEF \\ fs[])
           \\ `EVERY map_ok (h'::t)`  by (imp_res_tac EVERY_DEF)
           \\ `cmp_of (list_union (h'::t)) = cmp_of h`
               by (imp_res_tac list_union_cmp_of \\ fs[])
           \\ `map_ok (list_union (h'::t))` by (imp_res_tac list_union_map_ok \\ fs[])
           \\ fs[lookup_union_left_none]))
   >- (fs[list_union_def]
     \\ rw[]
     \\ cases_on `ys`
       >- ( fs[])
       >- (
         `lookup (list_union (h'::(t ++ h''::t'))) k =
          lookup (list_union (h''::t')) k` by res_tac
         \\ rw[]
         \\ `EVERY (\t. cmp_of t = cmp_of h) (h'::(t ++ h''::t'))`
           by (imp_res_tac EVERY_DEF \\ fs[EVERY_APPEND])
         \\ `EVERY map_ok (h'::(t ++ h''::t'))` by (imp_res_tac EVERY_DEF \\ fs[EVERY_APPEND])

         \\ `cmp_of (list_union (h'::(t ++ h''::t'))) = cmp_of h`
             by (imp_res_tac list_union_cmp_of \\ fs[])
         \\ `map_ok (list_union (h'::(t ++ h''::t')))`
           by (imp_res_tac list_union_map_ok \\ fs[])
         \\ Cases_on `list_union (h'::(t ++ h''::t'))`
         \\ imp_res_tac lookup_union_left_none
         \\ rfs[])));

Theorem lookup_list_union_append_eq_left
 `!xs ys cmp.
   EVERY map_ok (xs++ys) /\
   EVERY (\t. cmp_of t = cmp) (xs++ys) /\
   EVERY (\m. lookup m k = NONE) ys /\ xs <> [] ==>
   lookup (list_union (xs ++ ys)) k = lookup (list_union xs) k`
 (rpt strip_tac
 \\ fs[]
 \\ `EVERY (λt. cmp_of t = cmp) (xs ++ ys)` by fs[EVERY_APPEND]
 \\ `EVERY map_ok (xs ++ ys)` by fs[EVERY_APPEND]
 \\ `map_ok (list_union xs)`
     by (cases_on `xs` >- (fs[]) >- (fs[list_union_map_ok]))
 \\ `cmp_of (list_union xs) = cmp`
     by (cases_on `xs` >- (fs[]) >- (fs[list_union_cmp_of]))
 \\ `map_ok (list_union (xs++ys))`
     by(cases_on `xs++ys` >- (fs[]) >- (imp_res_tac list_union_map_ok \\ fs[]))
 \\ fs[mlmapTheory.lookup_thm] \\ rw[]
 \\ cases_on `ys`
   >- (fs[])
   >- (
     fs[to_fmap_list_union_APPEND]
     \\ cases_on `FLOOKUP (to_fmap (list_union xs)) k`
       >- (fs[FLOOKUP_FUNION]
         \\ `map_ok (list_union (h::t))` by fs[list_union_map_ok]
         \\ fs[GSYM mlmapTheory.lookup_thm]
         \\ fs[lookup_list_union_none]
       )
       >- (fs[FLOOKUP_FUNION])));

Theorem lookup_list_union_append_eq_mid
  `!xs ys cmp.
    EVERY map_ok (xs++[b]++ys) /\
    EVERY (\t. cmp_of t = cmp) (xs++[b]++ys) /\
    EVERY (\m. lookup m k = NONE) ys /\
    EVERY (\m. lookup m k = NONE) xs ==>
     lookup (list_union (xs ++ [b] ++ ys)) k = lookup b k`
  (fs[lookup_list_union_append_eq_left, lookup_list_union_append_eq_right,
    list_union_def]);

Theorem lookup_wrong_hash_none
  `!(bs : ('a,'b) map list) i.
   i <> (hf k) MOD (LENGTH bs) /\
   buckets_ok bs hf /\
   i < LENGTH bs ==>
     (lookup (EL i bs) k = NONE)`
  (rpt strip_tac
  \\cases_on `lookup (EL i bs) k`
    >- (fs[])
    >- (fs[buckets_ok_def, hash_key_set_def, bucket_ok_def]
      \\res_tac
      \\fs[]));

Theorem lookup_left_right_none
  `!bs.
    0 < LENGTH bs /\
    i = (hf k) MOD (LENGTH bs) /\
    buckets_ok bs hf ==>
      EVERY (\m. lookup m k = NONE) (TAKE i bs) /\
      EVERY (\m. lookup m k = NONE) (DROP (i+1) bs)`
  (strip_tac \\ strip_tac
  \\`i < LENGTH bs` by fs[MOD_LESS]
  \\`!j. j < (i :num) ==> (mlmap$lookup (EL j (TAKE i bs)) (k:'a)) = NONE`
      by (simp[EL_TAKE]
        \\ assume_tac lookup_wrong_hash_none
        \\ res_tac
        \\ fs[])
  \\`!j. j < LENGTH bs − (i + 1) ==> (lookup (EL j (DROP (i+1) bs)) (k:'a)) = NONE`
      by ( fs[EL_DROP] \\ assume_tac lookup_wrong_hash_none \\ fs[])
  \\simp[EVERY_EL]);

Theorem lookup_list_union
  `!bs k i cmp hf.
    bs <> [] /\
    i = hf k MOD LENGTH bs /\
    buckets_ok bs hf /\
    EVERY map_ok bs /\
    EVERY (\b. cmp_of b = cmp) bs ==>
      mlmap$lookup (list_union bs) k = mlmap$lookup (EL i bs) k`
  (rpt strip_tac
  \\ `0 < LENGTH bs` by fs[NOT_NIL_EQ_LENGTH_NOT_0]
  \\ `i < LENGTH bs` by fs[MOD_LESS]
  \\ `i+1 <= LENGTH bs` by fs[MOD_LESS]
  \\ `?xs ys.
      (xs ++ [EL i bs] ++ ys) = bs /\
       EVERY map_ok (xs ++ [EL i bs] ++ ys) /\
       EVERY (\m. cmp_of m = cmp) (xs++[EL i bs]++ys) /\
       EVERY (\m. lookup m k = NONE) xs /\
       EVERY (\m. lookup m k = NONE) ys`
      by (qexists_tac `TAKE i bs`
        \\qexists_tac `DROP (i+1) bs`
        \\ conj_tac >- (imp_res_tac TAKE_SEG_DROP \\ rfs[SEG1])
        \\ imp_res_tac lookup_left_right_none
        \\ simp[]
        \\ simp[EVERY_EL, EVERY_DEF, EVERY_TAKE, EVERY_DROP, EVERY_APPEND]
        \\ rfs[EVERY_EL])
  \\ `bs = xs ++ [EL i bs] ++ ys` by simp[]
  \\ `lookup (list_union (xs++[EL i bs]++ys)) k = lookup (EL i bs) k`
      by imp_res_tac lookup_list_union_append_eq_mid
  \\ rfs[]);

Theorem replicate_every_same
  `(REPLICATE n e) = xs ==>
    EVERY ($=e) xs`
  (strip_tac
  \\rw[]
  \\fs[EVERY_REPLICATE]
  );

Theorem replicate_empty_map_thm
  `!cmp.
    TotOrd cmp /\
    (REPLICATE n (mlmap$empty cmp)) = xs ==>
      EVERY ($=(mlmap$empty cmp)) xs /\
      EVERY (mlmap$map_ok) xs /\
      EVERY (\t. mlmap$cmp_of t = cmp) xs`
  (rpt strip_tac
  >-(imp_res_tac replicate_every_same)
  >-(imp_res_tac replicate_every_same
    \\rw[]
    \\fs[EVERY_REPLICATE, mlmapTheory.empty_thm])
  >-(imp_res_tac replicate_every_same
    \\rw[]
    \\fs[EVERY_REPLICATE, mlmapTheory.cmp_of_def]));


Theorem hashtable_empty_spec
  `!a b hf hfv cmp cmpv size sizev ar.
      NUM size sizev /\
      (a --> NUM) hf hfv /\
      (a --> a --> ORDERING_TYPE) cmp cmpv /\
      TotOrd cmp ==>
      app (p:'ffi ffi_proj) Hashtable_empty_v [sizev; hfv; cmpv]
        emp
        (POSTv htv. HASHTABLE a b hf cmp FEMPTY htv)`
  (xcf_with_def "Hashtable.empty" Hashtable_empty_v_def
  \\xlet_auto
    >-(xsimpl)
  THEN1 (xlet `POSTv v. &(NUM 1 v \/ (NUM size' v /\ BOOL F bv))`
    THEN1 (xif
    \\ xlit
    \\ xsimpl
    \\ fs[BOOL_def])
  (*size > 1*)
  THEN1 (xlet `POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE 1 mpv)`
    >-(xapp
    \\ simp[])
  THEN1 (xlet `POSTv loc. SEP_EXISTS addr arr. &(addr = loc) * REF_ARRAY loc arr (REPLICATE 1 mpv)`
      >-(xref
      \\ fs[REF_ARRAY_def,REF_NUM_def]
      \\ xsimpl)
  THEN1 (xlet `POSTv loc. SEP_EXISTS arr. REF_NUM loc 0 * REF_ARRAY addr arr (REPLICATE 1 mpv)`
      >-(xref
      \\ fs[REF_ARRAY_def, REF_NUM_def]
      \\ xsimpl)
  \\ xcon
  \\ fs[HASHTABLE_def]
  \\ xsimpl
  \\ qexists_tac `(REPLICATE 1 mpv)`
  \\ qexists_tac `arr`
  \\ qexists_tac `0`
  \\ xsimpl
  \\ fs[hashtable_inv_def]
  \\ qexists_tac `(REPLICATE 1 (mlmap$empty cmp))`
  \\ rpt conj_tac
  THEN1(simp[REPLICATE_GENLIST, GENLIST_CONS, list_union_def, mlmapTheory.empty_thm])
  THEN1(simp[buckets_ok_empty])
  THEN1(simp[REPLICATE_NIL])
  THEN1(simp[LIST_REL_REPLICATE_same])
  THEN1(fs[EVERY_EL,HD, REPLICATE_GENLIST, GENLIST_CONS, mlmapTheory.empty_thm, balanced_mapTheory.empty_thm])
  \\fs[EVERY_EL,HD, REPLICATE_GENLIST, GENLIST_CONS, mlmapTheory.cmp_of_def])))
  (*size > 1*)
  THEN1 (xlet `POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE size' mpv)`
      >-(xapp
      \\ simp[])
  THEN1 (xlet `POSTv loc. SEP_EXISTS addr arr. &(addr = loc) * REF_ARRAY loc arr (REPLICATE size' mpv)`
      >-(xref
        \\fs[REF_ARRAY_def,REF_NUM_def]
        \\ xsimpl)
  THEN1 (xlet `POSTv loc. SEP_EXISTS arr. REF_NUM loc 0 * REF_ARRAY addr arr (REPLICATE size' mpv)`
      >-(xref
      \\ fs[REF_ARRAY_def, REF_NUM_def]
      \\ xsimpl)
  \\ xcon
  \\ fs[HASHTABLE_def]
  \\ xsimpl
  \\ qexists_tac `(REPLICATE size' mpv)`
  \\ qexists_tac `arr`
  \\ qexists_tac `0`
  \\ xsimpl
  \\ fs[hashtable_inv_def]
  \\ qexists_tac `(REPLICATE size' (mlmap$empty cmp))`
  \\ rpt conj_tac
  THEN1 (Cases_on `REPLICATE size' (mlmap$empty cmp)`
      >-(fs[BOOL_def, REPLICATE_NIL])
        \\imp_res_tac replicate_empty_map_thm
        \\fs[list_union_empty_maps])
  THEN1 (simp[buckets_ok_empty])
  THEN1 (fs[BOOL_def, REPLICATE_NIL])
  THEN1 (simp[LIST_REL_REPLICATE_same])
  THEN1 (Cases_on `REPLICATE size' (mlmap$empty cmp)`
      >-(fs[BOOL_def, REPLICATE_NIL])
        \\ imp_res_tac replicate_empty_map_thm)
  THEN1 (Cases_on `REPLICATE size' (mlmap$empty cmp)`
      >-(fs[BOOL_def, REPLICATE_NIL])
        \\imp_res_tac replicate_empty_map_thm))))));


Theorem buckets_ok_insert
  `!buckets hf idx k v.
      EVERY map_ok buckets /\
      buckets_ok buckets hf /\
      idx = hf k MOD LENGTH buckets ==>
        buckets_ok
          (LUPDATE (mlmap$insert (EL idx buckets) k v)
            idx buckets) hf`
  (rpt strip_tac
  \\fs[EVERY_EL,EL_LUPDATE,buckets_ok_def, bucket_ok_def, hash_key_set_def]
  \\ntac 4 strip_tac
  \\Cases_on `i = hf k MOD LENGTH buckets`
  \\fs[mlmapTheory.lookup_insert]
  \\Cases_on `k=k'`
  \\ntac 3 (simp[]));

Theorem buckets_ok_delete:
  !buckets hf idx k v.
      EVERY map_ok buckets /\
      buckets_ok buckets hf /\
      idx = hf k MOD LENGTH buckets ==>
        buckets_ok
          (LUPDATE (mlmap$delete (EL idx buckets) k)
            idx buckets) hf
Proof
  rpt strip_tac
  \\fs[EVERY_EL,EL_LUPDATE,buckets_ok_def, bucket_ok_def, hash_key_set_def]
  \\ntac 4 strip_tac
  \\Cases_on `i = hf k MOD LENGTH buckets`
  \\fs[mlmapTheory.lookup_delete]
  \\Cases_on `k=k'`
  \\ntac 3 (simp[])
QED;

Theorem insert_not_empty
  `!a b (mp:('a,'b) map) k v.
      mlmap$map_ok mp ==>
        to_fmap (mlmap$insert mp k v) <> FEMPTY`
  (fs[mlmapTheory.insert_thm, mlmapTheory.to_fmap_def,
      balanced_mapTheory.insert_thm,
      balanced_mapTheory.to_fmap_def, FEMPTY_FUPDATE_EQ]);


Theorem list_rel_insert
  `
      LIST_REL (MAP_TYPE a b) buckets vlv /\
      MAP_TYPE a b (mlmap$insert (EL idx buckets) k v) updMap /\
      EVERY map_ok buckets /\
      idx < LENGTH buckets  ==>
        LIST_REL (MAP_TYPE a b)
          (LUPDATE (mlmap$insert (EL idx buckets) k v) idx buckets)
            (LUPDATE updMap idx vlv)`
  (rpt strip_tac
  \\ fs[EVERY_EL,LIST_REL_EL_EQN, EL_LUPDATE]
  \\ strip_tac
  \\ strip_tac
  \\ Cases_on `n = idx`
  \\ fs[mlmapTheory.insert_thm]
  \\ simp[]);

Theorem list_rel_delete:
    LIST_REL (MAP_TYPE a b) buckets vlv /\
    MAP_TYPE a b (mlmap$delete (EL idx buckets) k) updMap /\
    EVERY map_ok buckets /\
    idx < LENGTH buckets  ==>
      LIST_REL (MAP_TYPE a b)
        (LUPDATE (mlmap$delete (EL idx buckets) k) idx buckets)
          (LUPDATE updMap idx vlv)
Proof
  rpt strip_tac
  \\ fs[EVERY_EL,LIST_REL_EL_EQN, EL_LUPDATE]
  \\ strip_tac
  \\ strip_tac
  \\ Cases_on `n = idx`
  \\ fs[mlmapTheory.delete_thm]
  \\ simp[]
QED;

Theorem every_map_ok_insert
  `!buckets idx k v.
      EVERY map_ok buckets /\
      idx < LENGTH buckets  ==>
        EVERY map_ok (LUPDATE (insert (EL idx buckets) k v) idx buckets)`
  (rpt strip_tac
  \\ fs[EVERY_EL,EL_LUPDATE]
  \\ strip_tac
  \\ strip_tac
  \\ Cases_on `n=idx`
  \\ fs[mlmapTheory.insert_thm]
  \\ simp[]);

Theorem every_map_ok_delete:
  !buckets idx k v.
      EVERY map_ok buckets /\
      idx < LENGTH buckets  ==>
        EVERY map_ok (LUPDATE (mlmap$delete (EL idx buckets) k) idx buckets)
Proof
  rpt strip_tac
  \\ fs[EVERY_EL,EL_LUPDATE]
  \\ strip_tac
  \\ strip_tac
  \\ Cases_on `n=idx`
  \\ fs[mlmapTheory.delete_thm]
  \\ simp[]
QED;

Theorem list_union_lupdate_insert
  `bs <> [] /\
   buckets_ok bs hf /\
   EVERY map_ok bs /\
   EVERY (\m. cmp_of m = cmp) bs ==>
    to_fmap (list_union bs) |+ (k,v) =
      to_fmap (list_union (LUPDATE (insert (EL (hf k MOD LENGTH bs) bs) k v)
                              (hf k MOD LENGTH bs) bs))`
  (rpt strip_tac
  \\ rfs[fmap_eq_flookup] \\ strip_tac
  \\ `?i. i = hf k MOD LENGTH bs` by simp[]
  \\ `?j. j = hf x MOD LENGTH bs` by simp[]
  \\ `0 < LENGTH bs` by fs[NOT_NIL_EQ_LENGTH_NOT_0]
  \\ `i < (LENGTH bs)` by fs[MOD_LESS]
  \\ `map_ok (list_union bs)`
      by (cases_on `bs` >- (fs[]) >- (imp_res_tac list_union_map_ok))
  \\ `map_ok (EL i bs) /\ cmp_of (EL i bs) = cmp` by fs[EVERY_EL]
  \\ `map_ok (insert (EL i bs) k v)` by fs[mlmapTheory.insert_thm]
  \\ `cmp_of (insert (EL i bs) k v) = cmp` by fs[mlmapTheory.cmp_of_insert]
  \\ `EVERY map_ok (LUPDATE (insert (EL i bs) k v) i bs) /\
      EVERY (\m. cmp_of m = cmp) (LUPDATE (insert (EL i bs) k v) i bs)`
      by fs[IMP_EVERY_LUPDATE]
  \\ `map_ok (list_union(LUPDATE (insert (EL i bs) k v) i bs))`
      by (cases_on `LUPDATE (insert (EL i bs) k v) i bs`
            >- (fs[])
            >- (imp_res_tac list_union_map_ok \\ fs[]))
  \\ `buckets_ok (LUPDATE (insert (EL i bs) k v) i bs) hf` by fs[buckets_ok_insert]
  \\ `lookup (list_union (LUPDATE (insert (EL i bs) k v) i bs)) x
      = lookup (EL j (LUPDATE (insert (EL i bs) k v) i (bs : ('a,'b) map list))) x`
      by (`(LUPDATE (insert (EL i bs) k v) i bs) <> []`
            by fs[LENGTH_LUPDATE, NOT_NIL_EQ_LENGTH_NOT_0]
        \\ `j = hf (x:'a) MOD (LENGTH (LUPDATE (insert (EL i bs) k v) i bs))`
            by fs[LENGTH_LUPDATE]
        \\ imp_res_tac lookup_list_union)
  \\ rfs[GSYM mlmapTheory.lookup_thm]
  \\ cases_on `x=k`
      >- (fs[EL_LUPDATE, mlmapTheory.lookup_insert, FLOOKUP_UPDATE])
      >- (fs[FLOOKUP_UPDATE]
        \\simp[GSYM mlmapTheory.lookup_thm,EL_LUPDATE]
        \\CASE_TAC
          >-(simp[mlmapTheory.lookup_insert]
            \\`?j'. j' = hf x MOD LENGTH bs` by simp[]
            \\imp_res_tac lookup_list_union
            \\simp[])
          >-(imp_res_tac lookup_list_union \\ simp[])));

Theorem list_union_lupdate_delete:
   bs <> [] /\
   buckets_ok bs hf /\
   EVERY map_ok bs /\
   EVERY (\m. cmp_of m = cmp) bs ==>
    to_fmap (list_union bs) \\ k =
      to_fmap (list_union (LUPDATE (mlmap$delete
                            (EL (hf k MOD LENGTH bs) bs) k)
                              (hf k MOD LENGTH bs) bs))
Proof
  rpt strip_tac
  \\ rfs[fmap_eq_flookup] \\ strip_tac
  \\ `?i. i = hf k MOD LENGTH bs` by simp[]
  \\ `?j. j = hf x MOD LENGTH bs` by simp[]
  \\ `0 < LENGTH bs` by fs[NOT_NIL_EQ_LENGTH_NOT_0]
  \\ `i < (LENGTH bs)` by fs[MOD_LESS]
  \\ `map_ok (list_union bs)`
      by (cases_on `bs` >- (fs[]) >- (imp_res_tac list_union_map_ok))
  \\ `map_ok (EL i bs) /\ cmp_of (EL i bs) = cmp` by fs[EVERY_EL]
  \\ `map_ok (delete (EL i bs) k)` by fs[mlmapTheory.delete_thm]
  \\ `cmp_of (delete (EL i bs) k) = cmp` by fs[mlmapTheory.cmp_of_delete]
  \\ `EVERY map_ok (LUPDATE (delete (EL i bs) k) i bs) /\
      EVERY (\m. cmp_of m = cmp) (LUPDATE (delete (EL i bs) k) i bs)`
      by fs[IMP_EVERY_LUPDATE]
  \\ `map_ok (list_union(LUPDATE (delete (EL i bs) k) i bs))`
      by (cases_on `LUPDATE (delete (EL i bs) k) i bs`
            >- (fs[])
            >- (imp_res_tac list_union_map_ok \\ fs[]))
  \\ `buckets_ok (LUPDATE (delete (EL i bs) k) i bs) hf` by fs[buckets_ok_delete]
  \\ `lookup (list_union (LUPDATE (delete (EL i bs) k) i bs)) x
      = lookup (EL j (LUPDATE (delete (EL i bs) k) i (bs : ('a,'b) map list))) x`
      by (`(LUPDATE (delete (EL i bs) k) i bs) <> []`
            by fs[LENGTH_LUPDATE, NOT_NIL_EQ_LENGTH_NOT_0]
        \\ `j = hf (x:'a) MOD (LENGTH (LUPDATE (delete (EL i bs) k) i bs))`
            by fs[LENGTH_LUPDATE]
        \\ imp_res_tac lookup_list_union)
  \\ rfs[GSYM mlmapTheory.lookup_thm]
  \\ cases_on `x=k`
      >- (fs[EL_LUPDATE, mlmapTheory.lookup_delete, DOMSUB_FLOOKUP_THM])
      >- (fs[DOMSUB_FLOOKUP_THM]
        \\simp[GSYM mlmapTheory.lookup_thm,EL_LUPDATE]
        \\CASE_TAC
          >-(simp[mlmapTheory.lookup_delete]
            \\`?j'. j' = hf x MOD LENGTH bs` by simp[]
            \\imp_res_tac lookup_list_union
            \\simp[])
          >-(imp_res_tac lookup_list_union \\ simp[]))
QED;

Theorem every_cmp_of_insert
  `!buckets idx k v.
      EVERY (λt. cmp_of t = cmp) buckets /\
      idx < LENGTH buckets  ==>
        EVERY (λt. cmp_of t = cmp) (LUPDATE (insert (EL idx buckets) k v) idx buckets)`
  (rpt strip_tac
  \\ fs[EVERY_EL,EL_LUPDATE]
  \\ strip_tac
  \\ strip_tac
  \\ Cases_on `n=idx`
  \\ fs[mlmapTheory.insert_thm]
  \\ simp[]);

Theorem every_cmp_of_delete:
  !buckets idx k v.
    EVERY (λt. cmp_of t = cmp) buckets /\
    idx < LENGTH buckets  ==>
    EVERY (λt. cmp_of t = cmp)
      (LUPDATE (mlmap$delete
        (EL idx buckets) k) idx buckets)
Proof
  rpt strip_tac
  \\ fs[EVERY_EL,EL_LUPDATE]
  \\ strip_tac
  \\ strip_tac
  \\ Cases_on `n=idx`
  \\ fs[mlmapTheory.delete_thm]
  \\ simp[]
QED;

Theorem hashtable_staticInsert_spec
  `!a b hf cmp k kv v vv htv.
      a k kv /\
      b v vv  ==>
      app (p:'ffi ffi_proj) Hashtable_staticInsert_v [htv; kv; vv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) * HASHTABLE a b hf cmp (h|+(k,v)) htv)`
(xcf_with_def "Hashtable.staticInsert" Hashtable_staticInsert_v_def
\\ fs[HASHTABLE_def]
\\ xpull
\\ xmatch
\\ fs[hashtable_inv_def]
\\ xlet `POSTv arr. SEP_EXISTS aRef arr2 avl uRef uv uvv.
    &(aRef = ar /\ arr2 = arr /\ avl = vlv /\ uRef = ur /\ uv = heuristic_size) *
    REF_ARRAY ar arr vlv * REF ur uvv * & (NUM heuristic_size uvv)`
  >-(xapp
    \\qexists_tac `ARRAY arr vlv * REF_NUM ur heuristic_size`
    \\qexists_tac `arr`
    \\fs[REF_ARRAY_def, REF_NUM_def]
    \\xsimpl)
\\ xlet `POSTv v. SEP_EXISTS length. &(length = LENGTH vlv /\ NUM length v) * REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
  >-(xapp
    \\qexists_tac `aRef ~~> arr2 * REF_NUM uRef uv`
    \\qexists_tac `avl`
    \\fs[REF_ARRAY_def,REF_NUM_def]
    \\xsimpl)
\\ xlet `POSTv v. SEP_EXISTS hashval. &(hashval = (hf k) /\ NUM hashval v) * REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
  >-(xapp
    \\qexists_tac `REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
    \\qexists_tac `k`
    \\qexists_tac `hf`
    \\conj_tac
     >-(qexists_tac `a`
      \\simp[])
    \\xsimpl)
\\ xlet `POSTv v. SEP_EXISTS idx. &(idx = (hashval MOD length') /\ NUM idx v /\
    idx < LENGTH avl /\ idx < LENGTH buckets /\ LENGTH buckets = LENGTH avl) * REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
  >-(xapp
    \\qexists_tac `REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
    \\qexists_tac `&length'`
    \\qexists_tac `&hashval`
    \\fs[NOT_NIL_EQ_LENGTH_NOT_0,X_MOD_Y_EQ_X,LENGTH_NIL_SYM,NUM_def, hashtable_inv_def, LIST_REL_LENGTH]
    \\xsimpl
    \\EVAL_TAC
    \\fs[LIST_REL_LENGTH,NOT_NIL_EQ_LENGTH_NOT_0,LIST_REL_EL_EQN, X_MOD_Y_EQ_X])
\\ xlet `POSTv mp. SEP_EXISTS oldMap. &(oldMap = mp /\ MAP_TYPE a b (EL idx buckets) mp) * REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
 >-(xapp
    \\qexists_tac `aRef ~~> arr2 * REF_NUM uRef uv`
    \\qexists_tac `idx`
    \\qexists_tac `vlv`
    \\fs[hashtable_inv_def,NOT_NIL_EQ_LENGTH_NOT_0,LIST_REL_EL_EQN, X_MOD_Y_EQ_X,REF_ARRAY_def]
    \\xsimpl)
\\ xlet `POSTv retv. SEP_EXISTS newMp.
      &(newMp = retv /\  MAP_TYPE a b (mlmap$insert (EL idx buckets)  k v) retv) * REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
 >-(xapp
    \\qexists_tac `REF_ARRAY aRef arr2 avl * REF_NUM uRef uv`
    \\qexists_tac `v`
    \\qexists_tac `k`
    \\qexists_tac `EL idx buckets`
    \\qexists_tac `b`
    \\qexists_tac `a`
    \\fs[LIST_REL_EL_EQN]
    \\xsimpl)
\\ xlet `POSTv unitv. SEP_EXISTS newBuckets.
    &(UNIT_TYPE () unitv /\ newBuckets = (LUPDATE newMp idx avl)) *
    REF_ARRAY aRef arr2 newBuckets * REF_NUM uRef uv`
  >-(xapp
    \\qexists_tac `aRef ~~> arr2 * REF_NUM uRef uv`
    \\qexists_tac `idx`
    \\qexists_tac `vlv`
    \\fs[REF_ARRAY_def]
    \\xsimpl)
\\ xlet `POSTv b. &(BOOL (mlmap$null (EL idx buckets)) b) * REF_ARRAY aRef arr2 newBuckets * REF_NUM uRef uv`
  >-(xapp
    \\qexists_tac `REF_ARRAY aRef arr2 newBuckets * REF_NUM uRef uv`
    \\qexists_tac `EL idx buckets`
    \\xsimpl
    \\qexists_tac `a`
    \\qexists_tac `b`
    \\fs[])
THEN1 (xif
THEN1 (xlet `POSTv usedv. &(NUM uv usedv) * REF_ARRAY aRef arr2 newBuckets * REF_NUM uRef uv`
  >-(xapp
    \\qexists_tac `REF_ARRAY aRef arr2 newBuckets`
    \\qexists_tac `uvv`
    \\fs[REF_NUM_def, NUM_def, INT_def]
    \\xsimpl)
\\ xlet_auto
  >-(qexists_tac `REF_ARRAY aRef arr2 newBuckets * REF_NUM uRef uv`
    \\xsimpl)
  THEN1( xapp
  \\qexists_tac `REF_ARRAY aRef arr2 newBuckets`
  \\qexists_tac `usedv`
  \\fs[REF_NUM_def, NUM_def, INT_def]
  \\xsimpl
  \\strip_tac
  \\strip_tac
  \\qexists_tac `uRef`
  \\qexists_tac `aRef`
  \\qexists_tac `hfv`
  \\qexists_tac `newBuckets`
  \\qexists_tac `arr2`
  \\qexists_tac `cmpv`
  \\qexists_tac `heuristic_size + 1`
  \\xsimpl
  \\qexists_tac `LUPDATE (mlmap$insert (EL (hf k MOD LENGTH buckets) buckets) k v) (hf k MOD LENGTH buckets) buckets`
  \\`buckets <> []` by simp[NOT_NIL_EQ_LENGTH_NOT_0]
  \\ imp_res_tac list_union_lupdate_insert
  \\ simp[]
  \\fs[every_cmp_of_insert, buckets_ok_insert, list_rel_insert, every_map_ok_insert]))
  \\xcon
  \\xsimpl
  \\qexists_tac `uRef`
  \\qexists_tac `aRef`
  \\qexists_tac `hfv`
  \\qexists_tac `newBuckets`
  \\qexists_tac `arr2`
  \\qexists_tac `cmpv`
  \\qexists_tac `heuristic_size`
  \\xsimpl
  \\qexists_tac `LUPDATE (mlmap$insert (EL (hf k MOD LENGTH buckets) buckets) k v) (hf k MOD LENGTH buckets) buckets`
  \\`buckets <> []` by simp[NOT_NIL_EQ_LENGTH_NOT_0]
  \\ imp_res_tac list_union_lupdate_insert
  \\ simp[]
  \\fs[every_cmp_of_insert, buckets_ok_insert, list_rel_insert, every_map_ok_insert]));

Theorem list_app_pairs_spec
 `∀a b l start lv.
  LIST_TYPE (PAIR_TYPE a b) l lv /\
  (!n xv. n < LENGTH l ∧ (PAIR_TYPE a b) (EL n l) xv ==>
    app p fv [xv] (eff (start+n)) (POSTv v. &UNIT_TYPE () v * (eff (start+n+1))))
  ==>
  app (p:'ffi ffi_proj) List_app_v [fv; lv] (eff start)
    (POSTv v. &UNIT_TYPE () v * (eff (start + (LENGTH l))))`
 (Induct_on `l` \\ rw[LIST_TYPE_def]
 >- ( xcf_with_def "List.app" List_app_v_def \\ xmatch \\ xcon \\ xsimpl )
 \\ xcf_with_def "List.app" List_app_v_def
 \\ xmatch
 \\ xlet`POSTv v. &UNIT_TYPE () v * eff (start+1)`
 >- (
   xapp
   \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n"]))
   \\ qexists_tac`0` \\ xsimpl )
 \\ first_x_assum drule
 \\ disch_then(qspec_then`start+1`mp_tac)
 \\ simp[ADD1]
 \\ impl_tac
 >- (
   rw[]
   \\ first_x_assum(qspec_then`n+1`mp_tac)
   \\ simp[EL_CONS,PRE_SUB1] )
 \\ strip_tac \\ xapp);

Theorem fupdate_list_take_el
  `n < LENGTH l ==>
    fm|++ ((TAKE (n+1) l)) =
    (fm|++ (TAKE n l)) |+ EL n l`
  (strip_tac
  \\fs[TAKE_EL_SNOC]
  \\fs[SNOC_APPEND]
  \\fs[FUPDATE_LIST_APPEND]
  \\fs[FUPDATE_LIST_THM]);

Theorem hashtable_insertList_spec
  `!a b hf cmp  htv l lv.
      LIST_TYPE (PAIR_TYPE a b) l lv ==>
      app (p:'ffi ffi_proj) Hashtable_insertList_v [htv;lv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) *
          HASHTABLE a b hf cmp (h|++l) htv)`
  (xcf_with_def "Hashtable.insertList" Hashtable_insertList_v_def
  \\xfun_spec `f`
   `!k v pv h' n.
      n < LENGTH l /\
      (PAIR_TYPE a b) (EL n l) pv ==>
      app (p:'ffi ffi_proj) f [pv]
        (HASHTABLE a b hf cmp (h'|++TAKE n l) htv)
        (POSTv uv. &(UNIT_TYPE () uv) *
          HASHTABLE a b hf cmp ((h'|++TAKE n l)|+EL n l) htv)`
    >-(rpt strip_tac
      \\Cases_on `(EL n l)`
      \\fs[PAIR_TYPE_def]
      \\xapp
      \\xmatch
      \\rw[PAIR_TYPE_def]
      >-(xapp
        \\rfs[]))
  >-(xapp_spec list_app_pairs_spec
    \\CONV_TAC(RESORT_EXISTS_CONV(sort_vars["l'", "start", "eff"]))
    \\qexists_tac `l`
    \\qexists_tac `0`
    \\qexists_tac `(λn1.  HASHTABLE a b hf cmp (h |++ (TAKE n1 l)) htv)`
    \\xsimpl
    \\CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\xsimpl
    \\qexists_tac `b`
    \\qexists_tac `a`
    \\simp[FUPDATE_LIST_THM]
    \\xsimpl
    \\rpt strip_tac
    >-(xapp
      \\CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n'", "h'"]))
      \\qexists_tac `n`
      \\qexists_tac `h`
      \\xsimpl
      \\fs[fupdate_list_take_el]
      \\xsimpl)));


Theorem foldr_list_union_eq:
  !bs.
    bs <> [] ==>
     FOLDR mlmap$union (mlmap$empty cmp) bs = list_union bs
Proof
  Induct \\ strip_tac
  >- (fs[])
   \\rpt strip_tac
   \\cases_on `bs`
     >- (cases_on `h` \\ cases_on `mlmap$empty cmp` \\ cases_on `b'` \\ cases_on `b`
         >-(fs[list_union_def,mlmapTheory.union_def,balanced_mapTheory.union_def])
         >-(fs[list_union_def,mlmapTheory.union_def,balanced_mapTheory.union_def])
         >-(fs[mlmapTheory.empty_def, balanced_mapTheory.empty_def])
         >-(fs[mlmapTheory.empty_def, balanced_mapTheory.empty_def]))
   \\fs[list_union_def]
QED

Theorem fupdate_list_fempty_toAsclist_eq_to_fmap:
  !m.
    map_ok m ==>
      FEMPTY |++ mlmap$toAscList m = to_fmap m
Proof
  rpt strip_tac
  \\fs[EQ_FDOM_SUBMAP]
  \\fs[FDOM_FUPDATE_LIST]
  \\fs[mlmapTheory.MAP_FST_toAscList]
  \\fs[SUBMAP_DEF]
  \\rpt strip_tac
  >-(fs[FUPDATE_LIST_alist_to_fmap]
    \\imp_res_tac mlmapTheory.MAP_FST_toAscList
    \\fs[MEM_MAP]
    \\qexists_tac `y`
    \\Cases_on `y`
    \\fs[FDOM_FLOOKUP])
  >-(`MEM x (MAP FST (REVERSE (toAscList m)))`
        by fs[FUPDATE_LIST_alist_to_fmap]
    \\fs[MEM_MAP]
    \\`ALL_DISTINCT (MAP FST (toAscList m))`
        by (imp_res_tac mlmapTheory.MAP_FST_toAscList)
    \\Cases_on `y`
    \\imp_res_tac mlmapTheory.MEM_toAscList
    \\imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
    \\imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME
    \\rw[]
    \\rfs[FUPDATE_LIST_ALL_DISTINCT_REVERSE]
    \\fs[FLOOKUP_DEF])
QED

Theorem hashtable_toAscList_spec:
  !a b hf cmp h htv.
    app (p:'ffi ffi_proj) Hashtable_toAscList_v [htv]
      (HASHTABLE a b hf cmp h htv)
      (* TODO: more meaningful postcondition? *)
      (POSTv listv. SEP_EXISTS bsalist asclist.
        &(LIST_TYPE (PAIR_TYPE a b) bsalist listv /\
          (FEMPTY |++ bsalist = h))
        * HASHTABLE a b hf cmp h htv)
Proof
  xcf_with_def "Hashtable.toAscList" Hashtable_toAscList_v_def
  \\fs[HASHTABLE_def]
  \\xpull
  \\fs[hashtable_inv_def]
  \\xmatch
  \\xlet `POSTv bsv. REF_ARRAY ar bsv vlv * REF_NUM ur heuristic_size`
    >-( xapp
      \\qexists_tac `ARRAY arr vlv * REF_NUM ur heuristic_size`
      \\qexists_tac `arr`
      \\fs[REF_ARRAY_def, REF_NUM_def] \\xsimpl)
  \\xlet `POSTv ackv. SEP_EXISTS ack. & (MAP_TYPE a b ack ackv /\
            ack = mlmap$empty cmp) * REF_ARRAY ar bsv vlv
            * REF_NUM ur heuristic_size`
    >-( xapp
      \\qexists_tac `REF_ARRAY ar bsv vlv * REF_NUM ur heuristic_size`
      \\asm_exists_tac \\qexists_tac `b`
      \\fs[REF_ARRAY_def, REF_NUM_def] \\ xsimpl)
  \\xlet `POSTv bigmapv.
          &(MAP_TYPE a b (FOLDR mlmap$union ack buckets) bigmapv)
          * REF_ARRAY ar bsv vlv * REF_NUM ur heuristic_size`
    >-( xapp_spec (INST_TYPE
        [``:'a``|->``:(α, β) map``, ``:'b``|->``:(α, β) map``]
        ArrayProofTheory.array_foldr_spec)
      \\qexists_tac `ar ~~> bsv  * REF_NUM ur heuristic_size`
      \\qexists_tac `vlv`
      \\asm_exists_tac
      \\qexists_tac `mlmap$union`
      \\qexists_tac `buckets`
      \\xsimpl
      \\qexists_tac `MAP_TYPE a b`
      \\fs[REF_ARRAY_def, REF_NUM_def, union_1_v_thm] \\xsimpl)
  \\xapp
  \\qexists_tac `REF_ARRAY ar bsv vlv * REF_NUM ur heuristic_size`
  \\asm_exists_tac
  \\xsimpl
  \\rpt strip_tac
  \\qexists_tac `toAscList (FOLDR union (empty cmp) buckets)`
  \\MAP_EVERY qexists_tac [`ur`, `ar`, `hfv`, `vlv`, `bsv`, `cmpv`, `heuristic_size`]
  \\xsimpl
  \\qexists_tac `buckets`
  \\xsimpl
  \\imp_res_tac LIST_REL_LENGTH
  \\`buckets <> []` by fs[LIST_REL_LENGTH, NOT_NIL_EQ_LENGTH_NOT_0]
  \\fs[foldr_list_union_eq,LIST_REL_LENGTH]
  \\Cases_on `buckets`
  >-(fs[])
  >-(`map_ok (list_union (h'::t))` by (imp_res_tac list_union_map_ok)
    \\fs[fupdate_list_fempty_toAsclist_eq_to_fmap])
QED;


Theorem hashtable_doubleCapacity_spec:
   !a b hf cmp  htv.
      app (p:'ffi ffi_proj) Hashtable_doubleCapacity_v [htv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) *
          HASHTABLE a b hf cmp h htv)
Proof
  xcf_with_def "Hashtable.doubleCapacity" Hashtable_doubleCapacity_v_def
  \\ fs[HASHTABLE_def]
  \\ xpull
  \\ xmatch
  \\ xlet `POSTv oldArr. &(oldArr = arr) *
                         REF_ARRAY ar arr vlv *
                         REF_NUM ur heuristic_size`
  >-(xapp
    \\qexists_tac `ARRAY arr vlv * REF_NUM ur heuristic_size`
    \\qexists_tac `arr`
    \\fs[REF_ARRAY_def]
    \\xsimpl)
  \\ xlet `POSTv av. &(NUM (LENGTH vlv) av) *
                     REF_ARRAY ar arr vlv * REF_NUM ur heuristic_size`
  >- (xapp \\ fs [REF_ARRAY_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\xlet `POSTv listv. SEP_EXISTS l.
                        &(LIST_TYPE (PAIR_TYPE a b) l listv /\
                          (FEMPTY |++ l = h)) *
                        HASHTABLE a b hf cmp h htv`
  >-(
    xapp
    \\MAP_EVERY qexists_tac [`emp`,`hf`, `h`, `cmp`, `b`, `a`]
    \\xsimpl
    \\fs[HASHTABLE_def]
    \\xsimpl
    \\MAP_EVERY qexists_tac [`vlv`,`arr`, `heuristic_size`]
    \\ xsimpl)
  \\ fs[HASHTABLE_def,REF_NUM_def]
  \\ xpull
  \\ rename [`REF_ARRAY ar arr1 vlv1`]
  \\ rveq
  \\ xlet_auto >- xsimpl
  \\ xlet `POSTv ar1. SEP_EXISTS mpv buckets2.
             ur ~~> Litv (IntLit 0) *
             &(MAP_TYPE a b (mlmap$empty cmp) mpv) *
             REF ar arr1 * ARRAY ar1 (REPLICATE (2 * LENGTH vlv) mpv)`
  >- (xapp
    \\ xsimpl
    \\ rpt (asm_exists_tac \\ fs [])
    \\ qexists_tac `b` \\ fs []
    \\ rw []
    \\ rpt (asm_exists_tac \\ fs [])
    \\ fs [REF_ARRAY_def] \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ asm_exists_tac \\ fs []
  \\ fs [HASHTABLE_def,REF_NUM_def,REF_ARRAY_def]
  \\ xsimpl
  \\ fs [PULL_EXISTS]
  \\ rpt (asm_exists_tac \\ fs [])
  \\ qexists_tac `FEMPTY`
  \\ conj_tac
  >-(fs[hashtable_inv_def]
    \\qexists_tac `REPLICATE (2*LENGTH vlv)  (mlmap$empty cmp)`
    \\fs[buckets_ok_empty, REPLICATE_NIL, LIST_REL_REPLICATE_same]
    \\`EVERY ($= (mlmap$empty cmp)) (REPLICATE (2 * LENGTH vlv) (mlmap$empty cmp))`
            by (imp_res_tac replicate_empty_map_thm \\ fs[EVERY_DEF])
    \\`EVERY map_ok (REPLICATE (2 * LENGTH vlv) (mlmap$empty cmp))`
            by (imp_res_tac replicate_empty_map_thm \\ fs[EVERY_DEF])
    \\`EVERY (λt. cmp_of t = cmp) (REPLICATE (2 * LENGTH vlv) (mlmap$empty cmp))`
            by (imp_res_tac replicate_empty_map_thm \\ fs[EVERY_DEF])
    \\Cases_on `REPLICATE (2 * LENGTH vlv) (mlmap$empty cmp)`
    >-(fs[REPLICATE_NIL])
    >-(fs[list_union_empty_maps]))
  \\ rw []
  \\ asm_exists_tac \\ fs []
QED;


Theorem hashtable_insert_spec:
   !a b hf cmp  htv k v kv vv.
      a k kv /\ b v vv ==>
      app (p:'ffi ffi_proj) Hashtable_insert_v [htv;kv;vv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) *
          HASHTABLE a b hf cmp (h|+(k,v)) htv)
Proof
     xcf_with_def "Hashtable.insert" Hashtable_insert_v_def
  \\ fs[HASHTABLE_def]
  \\ fs[REF_ARRAY_def]
  \\ xpull
  \\ xmatch
  \\ xlet_auto
  >-(CONV_TAC(RESORT_EXISTS_CONV List.rev)
     \\ qexists_tac `arr` \\ xsimpl)
  \\ xlet `POSTv dv. &(NUM (LENGTH vlv) dv) *
                    REF_ARRAY ar arr vlv *
                    REF_NUM ur heuristic_size`
  >-( fs[REF_ARRAY_def] \\ xapp
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `vlv` \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ fs[REF_NUM_def]
  \\ xpull
  \\ xlet_auto >- xsimpl
  \\ fs[REF_NUM_def]
  \\ xlet `POSTv bv. &(NUM (4*heuristic_size) bv) *
                    REF_ARRAY ar arr vlv *
                    REF_NUM ur heuristic_size`
  >-(fs[REF_NUM_def] \\ xapp \\ xsimpl
    \\ fs[NUM_def] \\asm_exists_tac \\fs[])
  \\ xlet_auto >- xsimpl
  \\fs[REF_NUM_def]
  \\xpull
  >-(xif
    >-(fs[REF_ARRAY_def] \\ xapp \\ fs[HASHTABLE_def, REF_NUM_def] \\ xsimpl
      \\ fs[PULL_EXISTS]
      \\CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ rpt (asm_exists_tac \\ fs[]) \\ xsimpl
      \\ fs[REF_ARRAY_def] \\ xsimpl
      \\ rpt strip_tac
      \\ asm_exists_tac \\ fs[])
    >-( fs[REF_ARRAY_def]
      \\xlet `POSTv uv. HASHTABLE a b hf cmp h htv`
      >-( xapp \\ xsimpl
        \\ fs[HASHTABLE_def, REF_ARRAY_def, REF_NUM_def] \\ xsimpl
        \\ fs[PULL_EXISTS]
        \\ rpt (asm_exists_tac \\ fs[]) \\ xsimpl
        \\ rpt strip_tac
        \\ asm_exists_tac \\ fs[])
      >-(  fs[HASHTABLE_def, REF_NUM_def, REF_ARRAY_def]
        \\ xpull
        \\ xapp
        \\ fs[HASHTABLE_def, REF_ARRAY_def, REF_NUM_def]
        \\ xsimpl
        \\ fs[PULL_EXISTS]
        \\ rpt (asm_exists_tac \\ fs[]) \\ xsimpl
        \\ rpt strip_tac
        \\ asm_exists_tac \\ fs[])))
QED;

Theorem hashtable_lookup_spec:
     !a b hf cmp htv k kv.
      a k kv  ==>
      app (p:'ffi ffi_proj) Hashtable_lookup_v [htv;kv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv v. &(OPTION_TYPE b (FLOOKUP h k) v) *
                    HASHTABLE a b hf cmp h htv)
Proof
  xcf_with_def "Hashtable.lookup" Hashtable_lookup_v_def
  \\ fs[HASHTABLE_def, REF_ARRAY_def]
  \\ xpull
  \\ xmatch
  \\ xlet_auto
  >-(CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `arr` \\ xsimpl)
  \\ xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (fs[hashtable_inv_def] \\ xsimpl)
  \\ fs[hashtable_inv_def]
  \\ xlet_auto
  >-(xsimpl \\ fs[NOT_NIL_EQ_LENGTH_NOT_0, MOD_LESS] )
  >-(xapp_spec (INST_TYPE [alpha|->beta, beta|->alpha] lookup_1_v_thm)
    \\ fs[PULL_EXISTS]
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ MAP_EVERY qexists_tac [`a`, `b`,
          `EL (hf k MOD LENGTH vlv) buckets`, `k`]
    \\ xsimpl \\ `LENGTH buckets = LENGTH vlv` by (imp_res_tac LIST_REL_LENGTH)
    \\ `(hf k MOD LENGTH vlv) < LENGTH buckets`
          by fs[LENGTH_NIL,NOT_NIL_EQ_LENGTH_NOT_0, MOD_LESS]
    \\ `MAP_TYPE a b (EL (hf k MOD LENGTH vlv) buckets)
          (EL (hf k MOD LENGTH vlv) vlv)` by fs[LIST_REL_EL_EQN] \\ simp[]
    \\ ntac 2 strip_tac
    \\ MAP_EVERY qexists_tac [`ur`,`ar`,`hfv`,`vlv`,`arr`,
                              `cmpv`,`heuristic_size`]
    \\`buckets <> []` by (imp_res_tac LIST_REL_LENGTH
                        \\ fs[NOT_NIL_EQ_LENGTH_NOT_0])
    \\ `map_ok (list_union buckets)`
          by (Cases_on `buckets` >- (fs[]) >- imp_res_tac list_union_map_ok)
    \\`lookup (EL (hf k MOD LENGTH vlv) buckets) k =
        FLOOKUP (to_fmap (list_union buckets)) k`
          by (imp_res_tac lookup_list_union \\ rfs[mlmapTheory.lookup_thm])
    \\fs[] \\ xsimpl \\ qexists_tac `buckets` \\ fs[LIST_REL_EL_EQN])
QED;


Theorem hashtable_delete_spec:
  !a b hf cmp k kv htv.
      a k kv ==>
      app (p:'ffi ffi_proj) Hashtable_delete_v [htv; kv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) * HASHTABLE a b hf cmp (h \\ k) htv)
Proof
  xcf_with_def "Hashtable.delete" Hashtable_delete_v_def
  \\ fs[HASHTABLE_def, REF_ARRAY_def, hashtable_inv_def]
  \\ xpull
  \\ xmatch
  \\ xlet_auto
  >-(CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `arr` \\ xsimpl)
  \\ xlet `POSTv bv. &(NUM (LENGTH vlv) bv) *
                    REF_ARRAY ar arr vlv *
                    REF_NUM ur heuristic_size`
  >-( fs[REF_ARRAY_def] \\ xapp
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `vlv` \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs[REF_ARRAY_def]
  \\ xlet_auto >-( xsimpl \\ fs[LENGTH_NIL,NOT_NIL_EQ_LENGTH_NOT_0, MOD_LESS])
  \\ `LENGTH buckets = LENGTH vlv` by (imp_res_tac LIST_REL_LENGTH)
  \\ `hf k MOD LENGTH vlv < LENGTH buckets`
        by fs[LENGTH_NIL,NOT_NIL_EQ_LENGTH_NOT_0, MOD_LESS]
  \\ `MAP_TYPE a b (EL (hf k MOD LENGTH vlv) buckets)
          (EL (hf k MOD LENGTH vlv) vlv)`
        by fs[LIST_REL_EL_EQN]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xlet `POSTv fv.
            &(BOOL (¬(mlmap$null (EL (hf k MOD LENGTH vlv) buckets)) /\ mlmap$null
                (mlmap$delete (EL (hf k MOD LENGTH vlv) buckets) k)) fv) *
            ARRAY yv (LUPDATE v' (hf k MOD LENGTH vlv) vlv) * ar ~~> yv *
            REF_NUM ur heuristic_size`
  >-(xlog
    \\CASE_TAC
    >-(xapp \\ fs[PULL_EXISTS]
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\ MAP_EVERY qexists_tac [`b`, `a`,
            `(delete (EL (hf k MOD LENGTH vlv) buckets) k)`]
      \\xsimpl)
    >-(xsimpl))
  \\xlet `POSTv jv.
            &(BOOL (¬(mlmap$null (EL (hf k MOD LENGTH vlv) buckets)) /\
                      mlmap$null (mlmap$delete (EL (hf k MOD LENGTH vlv)
                        buckets) k) /\
                      0 < heuristic_size) jv) *
            ARRAY yv (LUPDATE v' (hf k MOD LENGTH vlv) vlv) * ar ~~> yv *
            REF_NUM ur heuristic_size`
  >-(xlog
    \\ CASE_TAC
    >-(fs[REF_NUM_def] \\ xpull \\ xlet_auto >-(xsimpl)
    >-(xapp \\ fs[PULL_EXISTS]
      \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
      \\qexists_tac `&heuristic_size`
      \\xsimpl \\ fs[NUM_def]))
    >-(xsimpl \\ fs[NUM_def]))
  >-(xif
    >-(fs[REF_NUM_def] \\ xpull \\ xlet_auto >- xsimpl
    >-(fs[NUM_def] \\ xlet_auto >- xsimpl
      >-(xapp \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
        \\qexists_tac `yv'` \\ xsimpl
        \\ ntac 2 strip_tac
        \\ MAP_EVERY qexists_tac
            [`ur`, `ar`, `hfv`, `(LUPDATE v' (hf k MOD LENGTH vlv) vlv)`,
            `yv`, `cmpv`, `heuristic_size - 1`, `iv`] \\ xsimpl
        \\ qexists_tac `(LUPDATE (mlmap$delete (EL (hf k MOD LENGTH vlv) buckets) k)
                           (hf k MOD LENGTH vlv) buckets)`
        \\ `buckets <> []` by (imp_res_tac LIST_REL_LENGTH
                              \\ fs[NOT_NIL_EQ_LENGTH_NOT_0])
        \\imp_res_tac list_union_lupdate_delete \\ rfs[]
        \\fs[buckets_ok_delete, every_map_ok_delete,
             every_cmp_of_delete, list_rel_delete]
        \\ fs[INT_def] \\ fs[int_arithTheory.INT_NUM_SUB])))
  \\ xcon \\ xsimpl
  \\ MAP_EVERY qexists_tac
      [`ur`, `ar`, `hfv`, `(LUPDATE v' (hf k MOD LENGTH vlv) vlv)`,
       `yv`, `cmpv`, `heuristic_size `] \\ xsimpl
  \\qexists_tac `(LUPDATE (mlmap$delete (EL (hf k MOD LENGTH vlv) buckets) k)
                    (hf k MOD LENGTH vlv) buckets)`
  \\ `buckets <> []` by (imp_res_tac LIST_REL_LENGTH
                        \\ fs[NOT_NIL_EQ_LENGTH_NOT_0])
  \\imp_res_tac list_union_lupdate_delete \\ rfs[]
  \\fs[buckets_ok_delete, every_map_ok_delete,
       every_cmp_of_delete, list_rel_delete])
QED;

Theorem hashtable_clear_spec:
  !a b hf cmp htv.
      a k kv ==>
      app (p:'ffi ffi_proj) Hashtable_clear_v [htv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) * HASHTABLE a b hf cmp FEMPTY htv)
Proof
  xcf_with_def "Hashtable.clear" Hashtable_clear_v_def
  \\ fs[HASHTABLE_def, REF_ARRAY_def, hashtable_inv_def]
  \\ xpull
  \\ xmatch
  \\ xlet_auto
  >-(CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `arr` \\ xsimpl)
  \\ xlet `POSTv bv. &(NUM (LENGTH vlv) bv) *
                    REF_ARRAY ar arr vlv *
                    REF_NUM ur heuristic_size`
  >-(fs[REF_ARRAY_def] \\ xapp
    \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `vlv` \\ xsimpl)
  \\ fs[REF_NUM_def] \\ xpull
  \\ xlet `POSTv cv. SEP_EXISTS em.
                     &(MAP_TYPE a b (mlmap$empty cmp) em) *
                     REF_ARRAY ar arr vlv *
                     ARRAY cv (REPLICATE (LENGTH vlv) em) *
                     REF_NUM ur heuristic_size`
  >-(fs[REF_ARRAY_def, REF_NUM_def] \\ xapp
    \\ asm_exists_tac \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ MAP_EVERY qexists_tac [`a`, `b`, `cmp`] \\ xsimpl
    \\ rpt strip_tac \\ qexists_tac `x` \\ fs[])
  \\ fs[REF_ARRAY_def, REF_NUM_def] \\ xpull
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs[NUM_def] \\ xlet_auto >- xsimpl
  >-(xapp \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
    \\ qexists_tac `v'` \\ xsimpl
    \\ ntac 2 strip_tac \\ MAP_EVERY qexists_tac
            [`ur`, `ar`, `hfv`, `REPLICATE (LENGTH vlv) em`,
            `cv`, `cmpv`, `&0`, `nv`] \\ fs[NUM_def] \\ xsimpl
    \\ qexists_tac `REPLICATE (LENGTH vlv) (mlmap$empty cmp)`
    \\ imp_res_tac replicate_empty_map_thm
    \\ fs[buckets_ok_empty, LIST_REL_REPLICATE_same, NOT_NIL_EQ_LENGTH_NOT_0]
    \\Cases_on `REPLICATE (LENGTH vlv) (mlmap$empty cmp)` >- fs[REPLICATE_NIL]
    >-(`h'::t <> []` by fs[NOT_NIL_EQ_LENGTH_NOT_0]
      \\ imp_res_tac replicate_empty_map_thm
      \\ fs[list_union_empty_maps]))
QED;


val _ = export_theory();
