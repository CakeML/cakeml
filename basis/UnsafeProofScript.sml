(*
  Proofs about the Unsafe module.
*)
Theory UnsafeProof
Ancestors
  ml_translator mlbasicsProg UnsafeProg
Libs
  preamble ml_translatorLib cfLib

val _ = translation_extends "UnsafeProg";

(* Unsafe.Array *)

fun prove_array_spec v_def =
  rpt strip_tac \\
  xcf_with_def v_def \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_empty_def, cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def, REPLICATE] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

Theorem unsafe_array_sub_spec:
   !a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_sub_v [av; nv]
       (ARRAY av a) (POSTv v. cond (v = EL n a) * ARRAY av a)
Proof
  prove_array_spec Unsafe_sub_v_def
QED

Theorem unsafe_array_update_spec:
   !a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_update_v
       [av; nv; v]
       (ARRAY av a)
       (POSTv uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))
Proof
  prove_array_spec Unsafe_update_v_def
QED

(* Unsafe.Word8Array *)

fun prove_array_spec v_def =
  rpt strip_tac \\
  xcf_with_def v_def \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_copyaw8aw8_def, cf_aalloc_def, cf_asub_def, cf_alength_def,
      cf_aupdate_def, cf_copystraw8_def, cf_copyaw8str_def,
      cf_xoraw8str_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def,
      app_copyaw8aw8_def, app_copystraw8_def, app_copyaw8str_def,
      app_xoraw8str_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def,STRING_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) []) \\
  TRY (
    qmatch_assum_rename_tac`STRING_TYPE s sv`
    \\ Cases_on`s` \\ fs[STRING_TYPE_def]
    \\ fs[mlstringTheory.substring_def, SEG_TAKE_DROP] )

Theorem w8array_sub_spec:
   !a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_w8sub_v [av; nv]
       (W8ARRAY av a) (POSTv v. cond (WORD (EL n a) v) * W8ARRAY av a)
Proof
  prove_array_spec Unsafe_w8sub_v_def
QED

Theorem w8array_update_spec:
   !a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) Unsafe_w8update_v
       [av; nv; wv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))
Proof
  prove_array_spec Unsafe_w8update_v_def
QED

Theorem w8xor_str_spec:
   !s sv n nv xor_res a.
     STRING_TYPE s sv /\ LENGTH (explode s) ≤ LENGTH a ==>
     app (p:'ffi ffi_proj) Unsafe_w8xor_str_v [av; sv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) *
         W8ARRAY av (THE (xor_bytes (MAP (n2w o ORD) (explode s)) a)))
Proof
  Cases \\ simp [] \\ prove_array_spec Unsafe_w8xor_str_v_def
QED

