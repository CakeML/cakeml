(*
  Proof about the code in the byte-array module Word8Array.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib cfLib
     Word8ArrayProgTheory
     bitstring_extraTheory
     (* TODO^ move? *)

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
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def,Litv_WORD_def] \\
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

val findi_def = Define `
  findi f [] = NONE /\
  findi f (x::xs) =
    if (f x) then SOME (0:num, x) else
    case findi f xs of
      |NONE => NONE
      |SOME (n,x) => SOME (n + 1, x)`;

Theorem findi_spec_SOME:
  ! f arr i.
  findi f arr = SOME (i, x) ==>
    EL i arr = x /\
    f (EL i arr) /\ (! m. m < i ==> ~ f (EL m arr)) /\ i < LENGTH(arr)
Proof
  Induct_on `arr` \\ fs[Once findi_def]
  \\ ntac 4 strip_tac
  \\ fs[Once findi_def]
  \\ Cases_on `f h` \\ fs[]
  >- (rveq \\ fs[])
  \\ Cases_on `findi f arr` \\ fs[]
  \\ rename [`findi f arr = SOME p`] \\ PairCases_on `p` \\ fs[]
  \\ rveq
  \\ res_tac \\ fs[GSYM ADD1]
  \\ rpt strip_tac \\ rveq \\ res_tac
  \\ Cases_on `m` \\ fs[]
  \\ res_tac
QED

Theorem findi_spec_SOME_rev:
  ! i arr f.
    EL i arr = x /\
    i < LENGTH (arr) /\ f (EL i arr) /\ (! m. m < i ==> ~ f (EL m arr)) ==>
    findi f arr = SOME (i, x)
Proof
  Induct_on `i` \\ fs[Once findi_def]
  >- (rpt strip_tac \\ Cases_on `arr` \\ fs[findi_def])
  \\ rpt strip_tac
  \\ Cases_on `arr` \\ fs[]
  \\ `~ f (EL 0 (h :: t))` by (first_x_assum (qspec_then `0` assume_tac) \\ fs[])
  \\ fs[Once findi_def]
  \\ `!m. m < i ==> ~ f (EL m t)`
      by (rpt strip_tac
          \\ first_x_assum (qspec_then `SUC m` assume_tac) \\ fs[]
          \\ res_tac)
  \\ res_tac \\ fs[]
QED

Theorem findi_spec_NONE:
  ! f arr i.
  findi f arr = NONE ==>
    (! i. i < LENGTH arr ==> ~ f (EL i arr))
Proof
  Induct_on `arr` \\ fs[Once findi_def]
  \\ ntac 2 strip_tac
  \\ Cases_on `f h` \\ fs[]
  \\ reverse (Cases_on `findi f arr`)
  >- (rename [`findi f arr = SOME p`] \\ PairCases_on `p` \\ fs[])
  \\ res_tac \\ fs[GSYM ADD1]
  \\ rpt strip_tac \\ res_tac
  \\ Cases_on `i` \\ fs[]
  \\ res_tac
QED

Theorem findi_spec_NONE_rev:
  ! f arr i.
    (! i. i < LENGTH arr ==> ~ f (EL i arr)) ==>
    findi f arr = NONE
Proof
  Induct_on `arr` \\ fs[Once findi_def]
  \\ rpt strip_tac
  \\ Cases_on `f h` \\ fs[]
  >- (first_x_assum (qspec_then `0` assume_tac) \\ fs[])
  \\ `findi f arr = NONE`
      by (first_x_assum irule \\ rpt strip_tac
          \\ first_x_assum (qspec_then `SUC i` assume_tac) \\ fs[]
          \\ res_tac)
  \\ fs[]
QED

Theorem w8array_find_aux_spec:
  ! arr arrv f fv av n nv old p.
    findi f old = NONE /\
    (WORD8 --> BOOL) f fv /\ NUM (LENGTH arr + LENGTH old) av /\ NUM (LENGTH old) nv ==>
    app (p:'ffi ffi_proj) Word8Array_findi_aux_v
      [fv; arrv; av; nv]
      (W8ARRAY arrv (old ++ arr))
      (POSTv v. W8ARRAY arrv (old ++ arr) *
          cond (OPTION_TYPE (PAIR_TYPE NUM WORD8) (findi f (old ++ arr)) v))
Proof
  Induct_on `arr`
  \\ xcf_with_def "Word8Array.findi_aux" Word8Array_findi_aux_v_def
  (* Base case *)
  >- (xlet_auto
      >- (xsimpl \\ fs[NUM_def, INT_def])
      \\ xif \\ qexists_tac `T` \\ conj_tac \\ fs[]
      \\ xcon \\ xsimpl \\ fs[std_preludeTheory.OPTION_TYPE_def])
  \\ xlet_auto >- xsimpl
  \\ xif \\ qexists_tac `F` \\ conj_tac \\ fs[]
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (xlet_auto >- xsimpl
      \\ xlet_auto
      >- (xcon \\ xsimpl)
      \\ xcon \\ xsimpl
      \\ `findi f (old ++ h::arr) = SOME (LENGTH old, h)`
          by (irule findi_spec_SOME_rev \\ fs[]
              \\ imp_res_tac findi_spec_NONE
              \\ rpt strip_tac
              >- (`~ f (EL m old)` by (res_tac)
                  \\ `EL m old = EL m (old ++ h::arr)`
                  by (irule (GSYM rich_listTheory.EL_APPEND1) \\ fs[])
                  \\ fs[])
              \\ `old ++ h::arr = old ++ [h] ++ arr` by (fs[Once CONS_APPEND])
              \\ pop_assum (fn thm => fs[thm])
              \\ fs[el_append3])
      \\ `old ++ h::arr = old ++ [h] ++ arr` by (fs[Once CONS_APPEND])
      \\ pop_assum (fn thm => fs[thm])
      \\ fs[std_preludeTheory.OPTION_TYPE_def, PAIR_TYPE_def, el_append3])
  \\ xlet_auto >- xsimpl
  \\ `old ++ h :: arr = (old ++ [h]) ++ arr` by (fs[])
  \\ pop_assum (fn thm => fs[thm])
  \\ `findi f (old ++ [h]) = NONE`
      by (irule findi_spec_NONE_rev
          \\ imp_res_tac findi_spec_NONE
          \\ rpt strip_tac
          \\ Cases_on `i < LENGTH old`
          >- (`EL i (old ++ [h]) = EL i old`
              by (irule rich_listTheory.EL_APPEND1 \\ fs[])
              \\ pop_assum (fn thm => fs[thm]) \\ res_tac)
          \\ `i = LENGTH old` by (fs[])
          \\ rveq \\ fs[]
          \\ `EL (LENGTH old) (old ++ [h] ++ arr) = EL (LENGTH old) (old ++ [h])`
              by (irule rich_listTheory.EL_APPEND1 \\ fs[])
          \\ pop_assum (fn thm => fs[thm]))
  \\ qpat_x_assum `findi _ old = NONE` kall_tac
  \\ first_x_assum drule \\ disch_then drule \\ fs[]
  \\ disch_then (qspecl_then [`arrv`, `av`, `nv1`, `p`] assume_tac)
  \\ xapp
  \\ conj_tac \\ fs[]
  \\ `LENGTH arr + (LENGTH old + 1) = LENGTH old + SUC (LENGTH arr)`
      suffices_by (metis_tac[])
  \\ rewrite_tac [GSYM ADD1] \\ rewrite_tac [GSYM ADD_SUC] \\ fs[]
QED

Theorem w8array_find_spec:
  !f fv arr arrv.
    (WORD8 --> BOOL) f fv ==>
    app (p:'ffi ffi_proj) Word8Array_findi_v [fv; arrv]
      (W8ARRAY arrv arr)
      (POSTv v. W8ARRAY arrv arr *
          cond (OPTION_TYPE (PAIR_TYPE NUM WORD8) (findi f arr) v))
Proof
  xcf_with_def "Word8Array.findi" Word8Array_findi_v_def
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl \\  fs[findi_def] \\ asm_exists_tac \\ fs[]
QED

val _ = export_theory()
