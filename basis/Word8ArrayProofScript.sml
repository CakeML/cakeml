(*
  Proof about the code in the byte-array module Word8Array.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib cfLib
     Word8ArrayProgTheory

val _ = new_theory "Word8ArrayProof";

val _ = translation_extends "Word8ArrayProg";

val basis_st = get_ml_prog_state;

fun prove_array_spec op_name =
  xcf op_name (basis_st()) \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_copyaw8aw8_def, cf_aalloc_def, cf_asub_def, cf_alength_def,
      cf_aupdate_def, cf_copystraw8_def, cf_copyaw8str_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def,
      app_copyaw8aw8_def, app_copystraw8_def, app_copyaw8str_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) []) \\
  TRY (
    qmatch_assum_rename_tac`STRING_TYPE s sv`
    \\ Cases_on`s` \\ fs[STRING_TYPE_def]
    \\ fs[mlstringTheory.substring_def, SEG_TAKE_DROP] )

Theorem w8array_alloc_spec:
   !n nv w wv.
     NUM n nv /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.array" (basis_st())) [nv; wv]
       emp (POSTv v. W8ARRAY v (REPLICATE n w))
Proof
  prove_array_spec "Word8Array.array"
QED

Theorem w8array_sub_spec:
   !a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.sub" (basis_st())) [av; nv]
       (W8ARRAY av a) (POSTv v. cond (WORD (EL n a) v) * W8ARRAY av a)
Proof
  prove_array_spec "Word8Array.sub"
QED

Theorem w8array_length_spec:
   !a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.length" (basis_st())) [av]
       (W8ARRAY av a) (POSTv v. cond (NUM (LENGTH a) v) * W8ARRAY av a)
Proof
  prove_array_spec "Word8Array.length"
QED

Theorem w8array_update_spec:
   !a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.update" (basis_st()))
       [av; nv; wv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))
Proof
  prove_array_spec "Word8Array.update"
QED

Theorem w8array_copy_spec:
   !src srcv srcoff srcoffv len lenv dst dstv dstoff dstoffv.
     NUM srcoff srcoffv /\ NUM dstoff dstoffv /\ NUM len lenv /\
     srcoff + len <= LENGTH src /\
     dstoff + len <= LENGTH dst ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.copy" (basis_st()))
       [srcv; srcoffv; lenv; dstv; dstoffv]
       (W8ARRAY srcv src * W8ARRAY dstv dst)
       (POSTv v. &(UNIT_TYPE () v) * W8ARRAY srcv src *
                 W8ARRAY dstv (TAKE dstoff dst ⧺
                               TAKE len (DROP srcoff src) ⧺
                               DROP (dstoff + len) dst) )
Proof
  prove_array_spec "Word8Array.copy"
QED

Theorem w8array_copyVec_spec:
   !src srcv srcoff srcoffv len lenv dst dstv dstoff dstoffv.
     NUM srcoff srcoffv /\ NUM dstoff dstoffv /\ NUM len lenv /\ STRING_TYPE src srcv /\
     srcoff + len <= strlen src /\
     dstoff + len <= LENGTH dst ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.copyVec" (basis_st()))
       [srcv; srcoffv; lenv; dstv; dstoffv]
       (W8ARRAY dstv dst)
       (POSTv v. &(UNIT_TYPE () v) *
                 W8ARRAY dstv (TAKE dstoff dst ⧺
                               MAP (n2w o ORD) (explode (mlstring$substring src srcoff len)) ⧺
                               DROP (dstoff + len) dst) )
Proof
  prove_array_spec "Word8Array.copyVec"
QED

Theorem w8array_substring_spec:
   !src srcv srcoff srcoffv len lenv.
     NUM srcoff srcoffv /\ NUM len lenv /\
     srcoff + len <= LENGTH src ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.substring" (basis_st()))
       [srcv; srcoffv; lenv]
       (W8ARRAY srcv src)
       (POSTv v. &(STRING_TYPE (strlit (MAP (CHR o w2n) (TAKE len (DROP srcoff src)))) v) *
                 W8ARRAY srcv src)
Proof
  prove_array_spec "Word8Array.substring"
QED

val firsti_def = Define `
  firsti f [] = NONE /\
  firsti f (x::xs) =
    if (f x) then SOME (0:num) else
    case firsti f xs of
      |NONE => NONE
      |SOME n => SOME (n + 1)`;

Theorem firsti_spec:
  ! f arr i.
  firsti f arr = SOME i ==>
    f (EL i arr) /\ (! m. m < i ==> ~ f (EL m arr)) /\ i < LENGTH(arr)
Proof
  Induct_on `arr` \\ fs[Once firsti_def]
  \\ ntac 4 strip_tac
  \\ fs[Once firsti_def]
  \\ Cases_on `f h` \\ fs[]
  >- (rveq \\ fs[])
  \\ Cases_on `firsti f arr` \\ fs[]
  \\ rveq
  \\ res_tac \\ fs[GSYM ADD1]
  \\ rpt strip_tac \\ res_tac
  \\ Cases_on `m` \\ fs[]
  \\ res_tac
QED

Theorem w8aray_find_aux_spec:
  !f fv arr arrv av n nv.
    firsti f old = NONE /\
    (WORD8 --> BOOL) f fv /\ NUM (LENGTH arr + LENGTH old) av /\ NUM (LENGTH old) nv ==>
    app (p:'ffi ffi_proj) Word8Array_find_aux_v
      [fv; arrv; av; nv]
      (W8ARRAY arrv (old ++ arr))
      (POSTv v. W8ARRAY arrv (old ++ arr) *
          cond (OPTION_TYPE NUM (firsti f (old ++ arr)) v))
Proof
  (* INDUCTION HERE *)
  xcf_with_def "Word8Array.find_aux" Word8Array_find_aux_v_def
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (xcon \\ xsimpl
      \\ `arr = []`
        by (Cases_on `arr` \\ fs[])
      \\ rveq \\ fs[std_preludeTheory.OPTION_TYPE_def])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (xlet_auto >- xsimpl
      \\ xcon \\ xsimpl
      \\ fs[std_preludeTheory.OPTION_TYPE_def]
      \\ cheat)
  \\ xlet_auto >- xsimpl
  \\ cheat
QED

Theorem w8array_find_spec:
  !f fv arr arrv.
    (WORD8 --> BOOL) f fv ==>
    app (p:'ffi ffi_proj) Word8Array_find_v [fv; arrv]
      (W8ARRAY arrv arr)
      (POSTv v. W8ARRAY arrv arr *
          cond (OPTION_TYPE NUM (firsti f arr) v))
Proof
  xcf_with_def "Word8Array.find" Word8Array_find_v_def
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl \\  fs[firsti_def] \\ asm_exists_tac \\ fs[]
QED

val _ = export_theory()
