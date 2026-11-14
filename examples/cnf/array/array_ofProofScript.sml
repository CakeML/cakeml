(*
  A generic heap predicate for an array whose elements refine the list xs
  through the refinement A, with its CF specifications
*)
Theory array_ofProof
Ancestors
  ArrayProof UnsafeProof
Libs
  preamble basis

val _ = translation_extends "UnsafeProg";

Definition ARRAY_OF_def:
  ARRAY_OF A av xs = SEP_EXISTS vs. ARRAY av vs * &LIST_REL A xs vs
End

Theorem ARRAY_OF_refl:
  (ARRAY_OF A av xs ==>> ARRAY_OF A av xs) ∧
  (ARRAY_OF A av xs ==>> ARRAY_OF A av xs * GC)
Proof
  xsimpl
QED

Theorem ARRAY_OF_alloc_spec:
  ∀A n nv x v.
  NUM n nv ∧ A x v ⇒
  app (p:'ffi ffi_proj) Array_array_v
    [nv; v]
    emp (POSTv av. ARRAY_OF A av (REPLICATE n x))
Proof
  rw[ARRAY_OF_def]>>
  xapp_spec array_alloc_spec>>xsimpl>>
  qexists_tac`n`>>
  simp[LIST_REL_REPLICATE_same]
QED

Theorem ARRAY_OF_length_spec:
  ∀A xs av.
  app (p:'ffi ffi_proj) Array_length_v
    [av]
    (ARRAY_OF A av xs)
    (POSTv v. &NUM (LENGTH xs) v * ARRAY_OF A av xs)
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  xapp_spec array_length_spec>>xsimpl>>
  imp_res_tac LIST_REL_LENGTH>>
  simp[]
QED

Theorem ARRAY_OF_sub_spec:
  ∀A xs av n nv.
  NUM n nv ∧ n < LENGTH xs ⇒
  app (p:'ffi ffi_proj) Array_sub_v
    [av; nv]
    (ARRAY_OF A av xs)
    (POSTv v. &A (EL n xs) v * ARRAY_OF A av xs)
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp_spec array_sub_spec>>xsimpl>>
  qexists_tac`n`>>
  gvs[LIST_REL_EL_EQN]
QED

Theorem ARRAY_OF_update_spec:
  ∀A xs av n nv x v.
  NUM n nv ∧ n < LENGTH xs ∧ A x v ⇒
  app (p:'ffi ffi_proj) Array_update_v
    [av; nv; v]
    (ARRAY_OF A av xs)
    (POSTv uv. &UNIT_TYPE () uv * ARRAY_OF A av (LUPDATE x n xs))
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp_spec array_update_spec>>xsimpl>>
  qexists_tac`n`>>
  simp[EVERY2_LUPDATE_same]
QED

Theorem ARRAY_OF_unsafe_sub_spec:
  ∀A xs av n nv.
  NUM n nv ∧ n < LENGTH xs ⇒
  app (p:'ffi ffi_proj) Unsafe_sub_v
    [av; nv]
    (ARRAY_OF A av xs)
    (POSTv v. &A (EL n xs) v * ARRAY_OF A av xs)
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp_spec unsafe_array_sub_spec>>xsimpl>>
  qexists_tac`n`>>
  gvs[LIST_REL_EL_EQN]
QED

Theorem ARRAY_OF_unsafe_update_spec:
  ∀A xs av n nv x v.
  NUM n nv ∧ n < LENGTH xs ∧ A x v ⇒
  app (p:'ffi ffi_proj) Unsafe_update_v
    [av; nv; v]
    (ARRAY_OF A av xs)
    (POSTv uv. &UNIT_TYPE () uv * ARRAY_OF A av (LUPDATE x n xs))
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp_spec unsafe_array_update_spec>>xsimpl>>
  qexists_tac`n`>>
  simp[EVERY2_LUPDATE_same]
QED

Theorem LIST_REL_update_resize:
  LIST_REL R a b ∧ R a1 b1 ∧ R a2 b2 ⇒
  LIST_REL R (update_resize a a1 a2 n) (update_resize b b1 b2 n)
Proof
  rw[update_resize_def]
  >- (
    match_mp_tac EVERY2_LUPDATE_same>>
    fs[])
  >- fs[LIST_REL_EL_EQN]
  >- fs[LIST_REL_EL_EQN]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[]>>
  match_mp_tac EVERY2_APPEND_suff>>
  fs[LIST_REL_EL_EQN]>>rw[]>>
  fs[EL_REPLICATE]
QED

Theorem ARRAY_OF_updateResize_spec:
  ∀A xs av d dv n nv x v.
  NUM n nv ∧ A d dv ∧ A x v ⇒
  app (p:'ffi ffi_proj) Array_updateResize_v
    [av; dv; nv; v]
    (ARRAY_OF A av xs)
    (POSTv av'. ARRAY_OF A av' (update_resize xs d x n))
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  xapp_spec array_updateResize_spec>>xsimpl>>
  metis_tac[LIST_REL_update_resize]
QED

(* Copies all of src into dst from index LENGTH bfr *)
Theorem ARRAY_OF_copy_spec:
  ∀A src srcv bfr mid afr dstv di div.
  NUM di div ∧ LENGTH src = LENGTH mid ∧ di = LENGTH bfr ⇒
  app (p:'ffi ffi_proj) Array_copy_v
    [srcv; dstv; div]
    (ARRAY_OF A srcv src * ARRAY_OF A dstv (bfr ++ mid ++ afr))
    (POSTv uv. ARRAY_OF A srcv src * ARRAY_OF A dstv (bfr ++ src ++ afr))
Proof
  rw[ARRAY_OF_def]>>
  xpull>>
  gvs[LIST_REL_SPLIT1]>>
  imp_res_tac LIST_REL_LENGTH>>
  xapp_spec array_copy_spec>>xsimpl>>
  qexistsl_tac[`ys2'`,`ys1'`,`ys2`]>>
  simp[]>>
  conj_tac >- gvs[]>>
  qexistsl_tac[`ys2`,`ys1'`,`vs`]>>
  simp[]
QED

Theorem LIST_REL_unique:
  (∀x y v. A x v ∧ A y v ⇒ x = y) ⇒
  ∀xs ys vs. LIST_REL A xs vs ∧ LIST_REL A ys vs ⇒ xs = ys
Proof
  strip_tac>>
  Induct>>rw[]>>
  Cases_on`ys`>>gvs[]>>
  metis_tac[]
QED

(* For an injective refinement, the array's pointer determines its list *)
Theorem ARRAY_OF_HPROP_INJ:
  (∀x y v. A x v ∧ A y v ⇒ x = y) ⇒
  HPROP_INJ (ARRAY_OF A av xs) (ARRAY_OF A av xs') (xs' = xs)
Proof
  rw[cfLetAutoTheory.HPROP_INJ_def,ARRAY_OF_def,SEP_CLAUSES,SEP_EXISTS_THM]>>
  gvs[cfLetAutoTheory.HCOND_EXTRACT,GSYM STAR_ASSOC]>>
  simp[STAR_ASSOC,cfLetAutoTheory.HCOND_EXTRACT]>>
  eq_tac>>rw[]
  >- (
    `vs' = vs` by metis_tac[cfLetAutoTheory.UNIQUE_ARRAYS]>>
    gvs[]>>
    metis_tac[LIST_REL_unique])>>
  metis_tac[]
QED

Theorem ARRAY_OF_NUM_HPROP_INJ[hprop_inj]:
  HPROP_INJ (ARRAY_OF NUM av xs) (ARRAY_OF NUM av xs') (xs' = xs)
Proof
  irule ARRAY_OF_HPROP_INJ>>
  rw[NUM_def,INT_def]
QED

(* The array bounds the witnessed operations of Unsafe.Arith, as a plain
  array does *)
Theorem index_witness_array_of:
  index_witness_heap p (ARRAY_OF A av xs) av (256 * LENGTH xs)
Proof
  rw[index_witness_heap_def,ARRAY_OF_def,SEP_EXISTS_THM,cond_STAR]>>
  imp_res_tac LIST_REL_LENGTH>>
  `index_witness_heap p (ARRAY av vs) av (256 * LENGTH vs)`
    by simp[index_witness_array]>>
  gvs[index_witness_heap_def]>>
  metis_tac[]
QED
