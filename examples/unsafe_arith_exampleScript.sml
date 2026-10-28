(*
  Circular-buffer index arithmetic with and without size witnesses.
*)
Theory unsafe_arith_example
Ancestors
  semanticPrimitives ml_translator UnsafeProg UnsafeProof
Libs
  preamble ml_translatorLib ml_progLib cfLib basisFunctionsLib

val _ = translation_extends "UnsafeProg";

Quote add_cakeml:
  fun next_index i limit =
    let val next = Unsafe.Arith.+ i 1 in
      if Unsafe.Arith.< next limit then next else 0
    end

  fun next_index_witness witness i limit =
    let val next = Unsafe.Arith.addWitness i 1 witness in
      if Unsafe.Arith.ltWitness next limit witness then next else 0
    end
End

val st = get_ml_prog_state ();

Theorem next_index_spec:
  INT i iv /\ INT limit lv /\ 0 <= i /\ i < limit /\ limit < 2 ** 30 ==>
  app (p:'ffi ffi_proj) ^(fetch_v "next_index" st) [iv;lv]
    emp (POSTv v. &INT (if i + 1 < limit then i + 1 else 0) v)
Proof
  rpt strip_tac
  \\ xcf "next_index" st
  \\ xlet_auto_spec (SOME unsafe_arith_add_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xlet_auto_spec (SOME unsafe_arith_lt_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xif \\ xret \\ xsimpl \\ fs []
QED

Theorem next_index_vector_spec:
  VECTOR_TYPE a xs witness /\ INT i iv /\ INT (&length xs) lv /\
  0 <= i /\ i < &length xs ==>
  app (p:'ffi ffi_proj) ^(fetch_v "next_index_witness" st) [witness;iv;lv]
    emp (POSTv v. &INT (if i + 1 < &length xs then i + 1 else 0) v)
Proof
  rpt strip_tac
  \\ xcf "next_index_witness" st
  \\ xlet_auto_spec (SOME unsafe_arith_add_vector_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xlet_auto_spec (SOME unsafe_arith_lt_vector_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xif \\ xret \\ xsimpl \\ fs []
QED

Theorem next_index_array_spec:
  INT i iv /\ INT (&LENGTH xs) lv /\ 0 <= i /\ i < &LENGTH xs ==>
  app (p:'ffi ffi_proj) ^(fetch_v "next_index_witness" st) [witness;iv;lv]
    (ARRAY witness xs)
    (POSTv v. &INT (if i + 1 < &LENGTH xs then i + 1 else 0) v * ARRAY witness xs)
Proof
  rpt strip_tac
  \\ xcf "next_index_witness" st
  \\ xlet_auto_spec (SOME unsafe_arith_add_array_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xlet_auto_spec (SOME unsafe_arith_lt_array_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xif \\ xret \\ xsimpl \\ fs []
QED

Theorem next_index_w8array_spec:
  INT i iv /\ INT (&LENGTH xs) lv /\ 0 <= i /\ i < &LENGTH xs ==>
  app (p:'ffi ffi_proj) ^(fetch_v "next_index_witness" st) [witness;iv;lv]
    (W8ARRAY witness xs)
    (POSTv v. &INT (if i + 1 < &LENGTH xs then i + 1 else 0) v * W8ARRAY witness xs)
Proof
  rpt strip_tac
  \\ xcf "next_index_witness" st
  \\ xlet_auto_spec (SOME unsafe_arith_add_w8array_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xlet_auto_spec (SOME unsafe_arith_lt_w8array_spec)
  >- (
    xsimpl \\ fs [index_in_bounds_def] \\ intLib.ARITH_TAC)
  \\ xif \\ xret \\ xsimpl \\ fs []
QED
