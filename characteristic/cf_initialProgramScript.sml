open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory ConseqConv
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfAppTheory cfTheory
open cfTacticsTheory cfTacticsBaseLib cfTacticsLib

val _ = new_theory "cf_initialProgram"

val basis_prog = EVAL ``basis_program`` |> concl |> rand
val basis_st = ml_progLib.add_prog basis_prog pick_name ml_progLib.init_state

val basis_prog_state = save_thm ("basis_prog_state",
  ml_progLib.pack_ml_prog_state basis_st
)

fun prove_opn_opb_spec op_name =
  xcf op_name basis_st \\
  fs [cf_opn_def, cf_opb_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_opn_def, app_opb_def] \\ xsimpl \\
  fs [INT_def, BOOL_def, opn_lookup_def, opb_lookup_def]

val plus_spec = store_thm ("plus_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op +" basis_st) [av; bv]
       emp (\v. cond (INT (a + b) v))``,
  prove_opn_opb_spec "op +"
)

val minus_spec = store_thm ("minus_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op -" basis_st) [av; bv]
       emp (\v. cond (INT (a - b) v))``,
  prove_opn_opb_spec "op -"
)

val times_spec = store_thm ("times_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op *" basis_st) [av; bv]
       emp (\v. cond (INT (a * b) v))``,
  prove_opn_opb_spec "op *"
)

val div_spec = store_thm ("div_spec",
  ``!a b av bv.
     INT a av /\ INT b bv /\ b <> 0 ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op div" basis_st) [av; bv]
       emp (\v. cond (INT (a / b) v))``,
  prove_opn_opb_spec "op div"
)

val mod_spec = store_thm ("mod_spec",
  ``!a b av bv.
     INT a av /\ INT b bv /\ b <> 0 ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op mod" basis_st) [av; bv]
       emp (\v. cond (INT (a % b) v))``,
  prove_opn_opb_spec "op mod"
)

val lt_spec = store_thm ("lt_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op <" basis_st) [av; bv]
       emp (\v. cond (BOOL (a < b) v))``,
  prove_opn_opb_spec "op <"
)

val gt_spec = store_thm ("gt_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op >" basis_st) [av; bv]
       emp (\v. cond (BOOL (a > b) v))``,
  prove_opn_opb_spec "op >"
)

val le_spec = store_thm ("le_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op <=" basis_st) [av; bv]
       emp (\v. cond (BOOL (a <= b) v))``,
  prove_opn_opb_spec "op <="
)

val ge_spec = store_thm ("ge_spec",
  ``!a b av bv.
     INT a av /\ INT b bv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op >=" basis_st) [av; bv]
       emp (\v. cond (BOOL (a >= b) v))``,
  prove_opn_opb_spec "op >="
)

(* todo: eq *)

val uminus_spec = store_thm ("uminus_spec",
  ``!a av.
     INT a av ==>
     app (p:'ffi ffi_proj) ^(fetch_v "op ~" basis_st) [av]
       emp (\v. cond (INT (~a) v))``,
  prove_opn_opb_spec "op ~"
)

fun prove_ref_spec op_name =
  xcf op_name basis_st \\
  fs [cf_ref_def, cf_deref_def, cf_assign_def] \\ irule local_elim \\
  reduce_tac \\ fs [app_ref_def, app_deref_def, app_assign_def] \\
  xsimpl \\ fs [UNIT_TYPE_def]

val ref_spec = store_thm ("ref_spec",
  ``!xv. app (p:'ffi ffi_proj) ^(fetch_v "op ref" basis_st) [xv]
          emp (\rv. rv ~~> xv)``,
  prove_ref_spec "op ref"
)

val deref_spec = store_thm ("deref_spec",
  ``!xv. app (p:'ffi ffi_proj) ^(fetch_v "op !" basis_st) [rv]
          (rv ~~> xv) (\yv. cond (xv = yv) * rv ~~> xv)``,
  prove_ref_spec "op !"
)

val assign_spec = store_thm ("assign_spec",
  ``!rv xv yv.
     app (p:'ffi ffi_proj) ^(fetch_v "op :=" basis_st) [rv; yv]
       (rv ~~> xv) (\v. cond (UNIT_TYPE () v) * rv ~~> yv)``,
  prove_ref_spec "op :="
)

fun prove_array_spec op_name =
  xcf op_name basis_st \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

val w8array_alloc = store_thm ("w8array_alloc",
  ``!n nv w wv.
     NUM n nv /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.array" basis_st) [nv; wv]
       emp (\v. W8ARRAY v (REPLICATE n w))``,
  prove_array_spec "Word8Array.array"
)

val w8array_sub = store_thm ("w8array_sub",
  ``!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.sub" basis_st) [av; nv]
       (W8ARRAY av a) (\v. cond (WORD (EL n a) v) * W8ARRAY av a)``,
  prove_array_spec "Word8Array.sub"
)

val w8array_length = store_thm ("w8array_length",
  ``!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.length" basis_st) [av]
       (W8ARRAY av a) (\v. cond (NUM (LENGTH a) v) * W8ARRAY av a)``,
  prove_array_spec "Word8Array.length"
)

val w8array_update = store_thm ("w8array_update",
  ``!a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.update" basis_st)
       [av; nv; wv]
       (W8ARRAY av a)
       (\v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))``,
  prove_array_spec "Word8Array.update"
)

val array_alloc = store_thm ("array_alloc",
  ``!n nv v.
     NUM n nv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.array" basis_st) [nv; v]
       emp (\av. ARRAY av (REPLICATE n v))``,
  prove_array_spec "Array.array"
)

val array_sub = store_thm ("array_sub",
  ``!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.sub" basis_st) [av; nv]
       (ARRAY av a) (\v. cond (v = EL n a) * ARRAY av a)``,
  prove_array_spec "Array.sub"
)

val array_length = store_thm ("array_length",
  ``!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Array.length" basis_st) [av]
       (ARRAY av a)
       (\v. cond (NUM (LENGTH a) v) * ARRAY av a)``,
  prove_array_spec "Array.length"
)

val array_update = store_thm ("array_update",
  ``!a av n nv v.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Array.update" basis_st)
       [av; nv; v]
       (ARRAY av a)
       (\uv. cond (UNIT_TYPE () uv) * ARRAY av (LUPDATE v n a))``,
  prove_array_spec "Array.update"
)

(* todo: vector, char, string *)

val _ = export_theory ()
