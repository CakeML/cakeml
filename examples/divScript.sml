(*
  Examples of non-termination.
*)
open preamble basis
open integerTheory cfDivTheory cfDivLib

val _ = new_theory "div";

val _ = translation_extends "basisProg";

(* A simple pure non-terminating loop *)

val _ = process_topdecs `
  fun pureLoop x = pureLoop x;
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem pureLoop_spec:
  !xv s u ns.
    limited_parts ns p ==>
    app (p:'ffi ffi_proj) ^(fetch_v "pureLoop" st) [xv]
      (one (FFI_part s u ns [])) (POSTd io. io = [||])
Proof
  xcf_div "pureLoop" st
  \\ MAP_EVERY qexists_tac [`K emp`, `K []`, `K($= xv)`, `K s`, `u`]
  \\ xsimpl \\ rw [lprefix_lub_def]
  \\ xvar \\ xsimpl
QED

(* Lemma needed for examples with integers *)

val eq_v_INT_thm = Q.prove(`(INT --> INT --> BOOL) $= eq_v`,
  metis_tac[DISCH_ALL mlbasicsProgTheory.eq_v_thm,EqualityType_NUM_BOOL]);

(* A conditionally terminating loop *)

val _ = process_topdecs `
  fun condLoop x = if x = 0 then 0 else condLoop (x - 1);
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem condLoop_spec:
  !x xv s u ns.
    limited_parts ns p /\ INT x xv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "condLoop" st) [xv]
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
      xcf "condLoop" st
      \\ xlet_auto THEN1 xsimpl
      \\ xif \\ instantiate
      \\ xlit \\ xsimpl)
    \\ xcf "condLoop" st
    \\ xlet_auto THEN1 xsimpl
    \\ xif \\ instantiate
    \\ xlet_auto THEN1 xsimpl
    \\ xapp
    \\ MAP_EVERY qexists_tac [`emp`, `u`, `s`, `ns`]
    \\ xsimpl \\ fs [INT_def] \\ intLib.COOPER_TAC)
  THEN1 (
    fs [SEP_CLAUSES] \\ fs [SEP_F_to_cond, POSTvd_def, GSYM POSTd_def]
    \\ xcf_div "condLoop" st
    \\ MAP_EVERY qexists_tac
      [`K emp`, `K []`, `\i. $= (Litv (IntLit (-&n - &i)))`, `K s`, `u`]
    \\ xsimpl \\ rw [lprefix_lub_def]
    THEN1 fs [INT_def]
    \\ xlet `POSTv v. &BOOL F v * one (FFI_part s u ns [])`
    THEN1 (xapp_spec eq_v_INT_thm \\ xsimpl)
    \\ xif \\ instantiate
    \\ xlet `POSTv v. &INT (-&n - &i - 1) v * one (FFI_part s u ns [])`
    THEN1 (xapp \\ xsimpl)
    \\ xvar \\ xsimpl \\ fs [INT_def] \\ intLib.COOPER_TAC)
  \\ xcf "condLoop" st
  \\ xlet_auto THEN1 xsimpl
  \\ xif \\ instantiate
  \\ xlit \\ xsimpl
QED

(* Another conditionally terminating loop, using FFI_full *)

val _ = process_topdecs `
  fun oddLoop x = if x = 0 then () else oddLoop(x-2);
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem oddLoop_spec:
  !i iv.
    INT i iv /\ ¬(2 int_divides i) ==>
    app (p:'ffi ffi_proj) ^(fetch_v "oddLoop" st) [iv]
      (one (FFI_full [])) (POSTd io. io = [||])
Proof
  xcf_div_FFI_full "oddLoop" st
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

(* A small IO model needed for IO examples *)

val names_def = Define `names = ["put_char"]`;

val put_char_event_def = Define `
  put_char_event c = IO_event "put_char" [n2w (ORD c)] []`;

val update_def = Define `
  update "put_char" [c] [] s = case destStr s of
    | NONE     => NONE
    | SOME out => SOME (FFIreturn [] (Str (SNOC (CHR (w2n c)) out)))`

val SIO_def = Define `
  SIO out events = one (FFI_part (Str out) update names events)`

val _ = process_topdecs `
  fun put_char c = let
      val s = String.implode [c]
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val _ = #(put_char) s a
    in () end
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem put_char_spec:
  !c cv s events.
  limited_parts names p /\ CHAR c cv ==>
  app (p:'ffi ffi_proj) ^(fetch_v "put_char" st) [cv]
    (SIO s events)
    (POSTv v. &UNIT_TYPE () v *
              SIO (SNOC c s) (SNOC (put_char_event c) events))
Proof
  xcf "put_char" st
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet `POSTv v. &STRING_TYPE (implode [c]) v * SIO s events`
  THEN1 (xapp \\ xsimpl \\ qexists_tac `[c]` \\ fs [LIST_TYPE_def])
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 xsimpl
  \\ rename1 `W8ARRAY av`
  \\ xlet `POSTv v. &UNIT_TYPE () v * W8ARRAY av [] *
                    SIO (SNOC c s) (SNOC (put_char_event c) events)`
  THEN1 (
    xffi \\ xsimpl
    \\ MAP_EVERY qexists_tac
      [`[n2w (ORD c)]`, `emp`, `Str s`, `update`, `names`, `events`]
    \\ fs [SIO_def, update_def, put_char_event_def, names_def,
           SNOC_APPEND, implode_def, STRING_TYPE_def] \\ xsimpl)
  \\ xcon \\ xsimpl
QED

(* Useful definitions *)

val REPLICATE_def = Define `
  (!l. REPLICATE l 0 = []) /\
  (!l n. REPLICATE l (SUC n) = REPLICATE l n ++ l)`

(* Useful lemmas *)

Theorem REPLICATE_SNOC:
  !x n. SNOC x (REPLICATE [x] n) = REPLICATE [x] (SUC n)
Proof
  rw [REPLICATE_def]
QED

Theorem REPLICATE_APPEND:
  !xs n. REPLICATE xs n ++ xs = REPLICATE xs (SUC n)
Proof
  rw [REPLICATE_def]
QED

Theorem REPLICATE_APPEND_SYM:
  !xs n. REPLICATE xs n ++ xs = xs ++ REPLICATE xs n
Proof
  strip_tac \\ Induct_on `n` \\ fs [REPLICATE_def]
QED

Theorem LPREFIX_REPLICATE_LREPEAT:
  !xs n. LPREFIX (fromList (REPLICATE xs n)) (LREPEAT xs)
Proof
  strip_tac \\ Induct_on `n`
  \\ fs [REPLICATE_def, REPLICATE_APPEND_SYM, GSYM LAPPEND_fromList]
  \\ rw [Once LREPEAT_thm] \\ fs [LPREFIX_APPEND]
  \\ qexists_tac `ll` \\ fs [LAPPEND_ASSOC]
QED

(* A non-terminating loop with side effects *)

val _ = process_topdecs `
  fun printLoop c = (put_char c; printLoop c);
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem printLoop_spec:
  !c cv.
    limited_parts names p /\ CHAR c cv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "printLoop" st) [cv]
      (SIO "" []) (POSTd io. io = LREPEAT [put_char_event c])
Proof
  xcf_div "printLoop" st
  \\ MAP_EVERY qexists_tac
    [`K emp`, `\i. REPLICATE [put_char_event c] i`, `K($= cv)`,
     `\i. Str (REPLICATE [c] i)`, `update`]
  \\ fs [GSYM SIO_def, REPLICATE_def]
  \\ xsimpl \\ rw [lprefix_lub_def]
  THEN1 (
    xlet `POSTv v. &UNIT_TYPE () v *
                   SIO (REPLICATE [c] (SUC i))
                       (REPLICATE [put_char_event c] (SUC i))`
    THEN1 (
      xapp
      \\ MAP_EVERY qexists_tac
        [`emp`, `REPLICATE [c] i`, `REPLICATE [put_char_event c] i`, `c`]
      \\ fs [REPLICATE_SNOC] \\ xsimpl)
    \\ xvar \\ fs [REPLICATE_APPEND] \\ xsimpl)
  THEN1 fs [LPREFIX_REPLICATE_LREPEAT]
  \\ qmatch_goalsub_abbrev_tac `LPREFIX a1 a2`
  \\ `a1 = a2` suffices_by simp[]
  \\ unabbrev_all_tac
  \\ PURE_ONCE_REWRITE_TAC [LLIST_BISIMULATION]
  \\ qexists_tac `\x y. x = LREPEAT [put_char_event c] /\ y = ub`
  \\ simp[]
  \\ conj_tac
  THEN1 (
    fs[PULL_EXISTS]
    \\ first_x_assum(qspec_then `1` mp_tac)
    \\ PURE_REWRITE_TAC[REPLICATE_def,ONE]
    \\ rw[LPREFIX_LCONS,LHD_LCONS] \\ rw[LHD_LCONS])
  \\ fs[PULL_EXISTS]
  \\ PURE_ONCE_REWRITE_TAC [LLIST_BISIMULATION]
  \\ qexists_tac `\y z. (!x. LPREFIX (fromList (REPLICATE [put_char_event c] x)) z) /\ y = THE(LTL z)`
  \\ rw[]
  \\ match_mp_tac OR_INTRO_THM2
  \\ conj_tac
  THEN1 (
    first_x_assum(qspec_then `SUC(SUC 0)` mp_tac)
    \\ PURE_REWRITE_TAC[REPLICATE_def]
    \\ rw[LPREFIX_LCONS,LHD_LCONS,LTL_LCONS]
    \\ rw[LTL_LCONS])
  \\ strip_tac
  \\ first_x_assum(qspec_then `SUC x` mp_tac)
  \\ simp[GSYM REPLICATE_APPEND,REPLICATE_APPEND_SYM]
  \\ simp[LPREFIX_LCONS]
  \\ rw[]
  \\ rw[LTL_LCONS]
QED

val _ = export_theory();
