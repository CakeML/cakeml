(*
  Examples of non-termination.
*)
open preamble basis
open integerTheory cfDivTheory cfDivLib

val _ = new_theory "div";

val _ = translation_extends "basisProg";

(* A simple pure non-terminating loop without repeat *)

val _ = process_topdecs `
  fun pureloop x = pureloop x;
  ` |> append_prog

val st = ml_translatorLib.get_ml_prog_state();

Theorem pureloop_spec:
  !xv s u ns.
    limited_parts ns p ==>
    app (p:'ffi ffi_proj) ^(fetch_v "pureloop" st) [xv]
      (one (FFI_part s u ns [])) (POSTd io. io = [||])
Proof
  xcf_div "pureloop" st
  \\ MAP_EVERY qexists_tac [`K emp`, `K []`, `K xv`, `K s`, `u`]
  \\ xsimpl \\ rw [lprefix_lub_def]
  \\ xvar \\ xsimpl
QED

(* Lemma needed for examples with integers *)

val eq_v_INT_thm = Q.prove(`(INT --> INT --> BOOL) $= eq_v`,
 metis_tac[DISCH_ALL mlbasicsProgTheory.eq_v_thm,EqualityType_NUM_BOOL]);

(* A conditionally terminating loop *)

val _ = process_topdecs `
  fun condloop x = if x = 0 then 0 else condloop (x - 1);
  ` |> append_prog

val st = ml_translatorLib.get_ml_prog_state();

Theorem condloop_spec:
  !x xv s u ns.
    limited_parts ns p /\ INT x xv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "condloop" st) [xv]
      (one (FFI_part s u ns []))
      (POSTvd
        (\v. &(0 <= x /\ INT 0 v) * one (FFI_part s u ns []))
        (\io. x < 0 /\ io = [||]))
Proof
  strip_tac \\ Cases_on `x`
  THEN1 (
    pop_assum (K ALL_TAC) \\ qid_spec_tac `n`
    \\ Induct_on `n`
    THEN1 (
      xcf "condloop" st
      \\ xlet_auto THEN1 xsimpl
      \\ xif \\ instantiate
      \\ xlit \\ xsimpl)
    \\ xcf "condloop" st
    \\ xlet_auto THEN1 xsimpl
    \\ xif \\ instantiate
    \\ xlet_auto THEN1 xsimpl
    \\ xapp
    \\ MAP_EVERY qexists_tac [`emp`, `u`, `s`, `ns`]
    \\ xsimpl \\ fs [INT_def] \\ intLib.COOPER_TAC)
  THEN1 (
    fs [SEP_CLAUSES] \\ fs [SEP_F_to_cond, POSTvd_def, GSYM POSTd_def]
    \\ xcf_div "condloop" st
    \\ MAP_EVERY qexists_tac
      [`K emp`, `K []`, `\i. Litv (IntLit (-&n - &i))`, `K s`, `u`]
    \\ xsimpl \\ rw [lprefix_lub_def]
    THEN1 fs [INT_def]
    \\ xlet `POSTv v. &BOOL F v * one (FFI_part s u ns [])`
    THEN1 (xapp_spec eq_v_INT_thm \\ xsimpl)
    \\ xif \\ instantiate
    \\ xlet `POSTv v. &INT (-&n - &i - 1) v * one (FFI_part s u ns [])`
    THEN1 (xapp \\ xsimpl)
    \\ xvar \\ xsimpl \\ fs [INT_def] \\ intLib.COOPER_TAC)
  \\ xcf "condloop" st
  \\ xlet_auto THEN1 xsimpl
  \\ xif \\ instantiate
  \\ xlit \\ xsimpl
QED

(* Another conditionally terminating loop, using FFI_full *)

val _ = process_topdecs `
  fun oddloop x = if x = 0 then () else oddloop(x-2);
  ` |> append_prog

val st = ml_translatorLib.get_ml_prog_state();

Theorem oddloop_spec:
  !i iv.
    INT i iv /\ ¬(2 int_divides i) ==>
    app (p:'ffi ffi_proj) ^(fetch_v "oddloop" st) [iv]
      (one (FFI_full [])) (POSTd io. io = [||])
Proof
  xcf_div_FFI_full "oddloop" st
  \\ MAP_EVERY qexists_tac [`K emp`,`K []`,`(\n. Litv(IntLit(i - 2 * &n)))`]
  \\ simp[lprefix_lub_def]
  \\ conj_tac >- (fs[ml_translatorTheory.INT_def])
  \\ conj_tac >- xsimpl
  \\ fs[SEP_CLAUSES]
  \\ strip_tac
  \\ rename1 `2 * SUC j`
  \\ xlet `POSTv bv. &BOOL F bv * one(FFI_full [])`
  >- (xapp_spec eq_v_INT_thm \\ xsimpl
      \\ fs[ml_translatorTheory.BOOL_def,semanticPrimitivesTheory.Boolv_def]
      \\ rw[] \\ intLib.COOPER_TAC)
  \\ xif
  \\ asm_exists_tac \\ simp[]
  \\ xlet `POSTv iv2. &INT (i − &(2 * SUC j)) iv2 * one(FFI_full [])`
  >- (xapp \\ xsimpl \\ fs[ml_translatorTheory.INT_def]
      \\ intLib.COOPER_TAC)
  \\ xvar \\ xsimpl \\ fs[ml_translatorTheory.INT_def]
QED

val _ = export_theory();
