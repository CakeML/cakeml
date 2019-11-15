(*
  Explicit construction of mini-basis, to support CF reasoning.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib ml_translatorTheory
     Word64ProgTheory (* TODO: can presumably get away with much less dependencies *)

val _ = new_theory "miniBasisProg";

val _ = reset_translation();

(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

(* to/from int *)
val _ = trans "fromInt" ``n2w:num->word8``;

val sigs = module_signatures ["fromInt"];

val _ = ml_prog_update (close_module (SOME sigs));

(* String *)

val _ = ml_prog_update (open_module "String");

val _ = trans "implode" mlstringSyntax.implode_tm;

val sigs = module_signatures ["implode"];

val _ = ml_prog_update (close_module (SOME sigs));

(* Word8Array *)

val _ = ml_prog_update (open_module "Word8Array");

val _ = append_decs ``[mk_binop "array" Aw8alloc]``

val _ = ml_prog_update (close_module NONE);


(* Word8 prog state *)

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

val _ = export_theory()
