(*
  Proofs about the Array module.
  load "cfLib";
  load "HashtableProgTheory";
  load "ArrayProofTheory";
*)

open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory ArrayProgTheory ArrayProofTheory MapProgTheory HashtableProgTheory
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
  THEN1 (Cases_on `REPLICATE size' (empty cmp)`
      >-(fs[BOOL_def, REPLICATE_NIL])
        \\imp_res_tac replicate_empty_map_thm
        \\fs[list_union_empty_maps])
  THEN1 (simp[buckets_ok_empty])
  THEN1 (fs[BOOL_def, REPLICATE_NIL])
  THEN1 (simp[LIST_REL_REPLICATE_same])
  THEN1 (Cases_on `REPLICATE size' (empty cmp)`
      >-(fs[BOOL_def, REPLICATE_NIL])
        \\ imp_res_tac replicate_empty_map_thm)
  THEN1 (Cases_on `REPLICATE size' (empty cmp)`
      >-(fs[BOOL_def, REPLICATE_NIL])
        \\imp_res_tac replicate_empty_map_thm))))));

(*
Theorem lupdate_fupdate_insert
  `!buckets idx k v.
      EVERY map_ok buckets /\
      idx < LENGTH buckets ==>
      LUPDATE (mlmap$to_fmap (EL idx buckets) |+ (k,v)) idx (MAP mlmap$to_fmap buckets) =
        MAP mlmap$to_fmap (LUPDATE (mlmap$insert (EL idx buckets) k v) idx buckets)`
(fs[EVERY_EL,LIST_REL_EL_EQN,LUPDATE_MAP,mlmapTheory.insert_thm]);*)

Theorem buckets_ok_insert
  `!buckets hf idx k v.
      EVERY map_ok buckets /\
      buckets_ok buckets hf /\
      idx < LENGTH buckets /\
      idx = hf k MOD LENGTH buckets ==>
        buckets_ok
          (LUPDATE (mlmap$insert (EL idx buckets) k v)
            idx buckets) hf`
  (rpt strip_tac
  \\fs[EVERY_EL,EL_LUPDATE,buckets_ok_def, bucket_ok_def, hash_key_set_def]
  \\strip_tac
  \\strip_tac
  \\strip_tac
  \\strip_tac
  \\Cases_on ` i = hf k MOD LENGTH buckets`
  \\fs[mlmapTheory.lookup_insert]
  \\Cases_on `k=k'`
  \\simp[]
  \\simp[]
  \\simp[]);


Theorem insert_not_empty
  `!a b (mp:('a,'b) map) k v.
      mlmap$map_ok mp ==>
        to_fmap (mlmap$insert mp k v) <> FEMPTY`
  (fs[mlmapTheory.insert_thm, mlmapTheory.to_fmap_def,
      balanced_mapTheory.insert_thm,
      balanced_mapTheory.to_fmap_def, FEMPTY_FUPDATE_EQ]);


Theorem list_rel_insert
  `!a b buckets updMap vlv idx k v.
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

(*
Theorem hashtable_staticInsert_spec
  `!a b hf hfv cmp cmpv k kv v vv htv used.
      a k kv /\
      b v vv  ==>
      app (p:'ffi ffi_proj) Hashtable_staticInsert_v [htv; kv; vv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) *
          HASHTABLE a b hf cmp (h|+(k,v)) htv)`
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
  \\fs[lupdate_fupdate_insert, buckets_ok_insert, list_rel_insert, every_map_ok_insert]
  \\Cases_on `to_fmap (EL (hf k MOD LENGTH vlv) buckets) = FEMPTY`
  \\simp[]
  \\Cases_on `(EL (hf k MOD LENGTH vlv) buckets)`
  \\Induct_on `b''`
  \\fs[mlmapTheory.null_def,balanced_mapTheory.null_def, balanced_mapTheory.null_thm, mlmapTheory.to_fmap_def]))

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
  \\fs[lupdate_fupdate_insert, buckets_ok_insert, list_rel_insert, every_map_ok_insert]
  \\Cases_on `(EL (hf k MOD LENGTH vlv) buckets)`
  \\simp[]
  \\Induct_on `b''`
  \\fs[mlmapTheory.null_def,balanced_mapTheory.null_def, balanced_mapTheory.null_thm, mlmapTheory.to_fmap_def]
  \\fs[mlmapTheory.null_def,balanced_mapTheory.null_def, balanced_mapTheory.null_thm, mlmapTheory.to_fmap_def]));
*)

val _ = export_theory();
