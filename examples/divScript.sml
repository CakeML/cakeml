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

val names_def = Define `names = ["put_char"; "get_char"]`;

val put_char_event_def = Define `
  put_char_event c = IO_event "put_char" [n2w (ORD c)] []`;

val get_char_event_def = Define `
  get_char_event c = IO_event "get_char" [] [0w, 1w; 0w, n2w (ORD c)]`;

val get_char_eof_event_def = Define `
  get_char_eof_event = IO_event "get_char" [] [0w, 0w; 0w, 0w]`;

val update_def = Define `
  (update "put_char" [c] [] s = case destCons s of
     | NONE                 => NONE
     | SOME (input, output) => case destStr output of
       | NONE   => NONE
       | SOME l => SOME (FFIreturn []
         (Cons input (Str (SNOC (CHR (w2n c)) l))))) /\
  (update "get_char" [] [0w; 0w] s = case destCons s of
     | NONE                 => NONE
     | SOME (input, output) => case destStream input of
       | NONE    => NONE
       | SOME ll => if ll = [||] then
           SOME (FFIreturn [0w; 0w] s)
         else
           SOME (FFIreturn [1w; n2w (THE (LHD ll))]
                           (Cons (Stream (THE (LTL ll))) output)))`

val State_def = Define `
  State input output = Cons (Stream (LMAP ORD input)) (Str output)`

val SIO_def = Define `
  SIO input output events =
    one (FFI_part (State input output) update names events)`

val _ = process_topdecs `
  fun put_char c = let
      val s = String.implode [c]
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val _ = #(put_char) s a
    in () end
  ` |> append_prog;

val _ = process_topdecs `
  fun get_char (u:unit) = let
      val a = Word8Array.array 2 (Word8.fromInt 0)
      val _ = #(get_char) "" a
    in if Word8Array.sub a 0 = Word8.fromInt 1 then
        Some (Char.chr (Word8.toInt (Word8Array.sub a 1)))
      else
        None
    end
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem put_char_spec:
  !c cv input output events.
  limited_parts names p /\ CHAR c cv ==>
  app (p:'ffi ffi_proj) ^(fetch_v "put_char" st) [cv]
    (SIO input output events)
    (POSTv v. &UNIT_TYPE () v *
              SIO input (SNOC c output) (SNOC (put_char_event c) events))
Proof
  xcf "put_char" st
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet
    `POSTv v. &STRING_TYPE (implode [c]) v * SIO input output events`
  THEN1 (xapp \\ xsimpl \\ qexists_tac `[c]` \\ fs [LIST_TYPE_def])
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 xsimpl
  \\ rename1 `W8ARRAY av`
  \\ xlet
    `POSTv v. &UNIT_TYPE () v * W8ARRAY av [] *
              SIO input (SNOC c output) (SNOC (put_char_event c) events)`
  THEN1 (
    xffi \\ xsimpl \\ fs [SIO_def]
    \\ MAP_EVERY qexists_tac
      [`[n2w (ORD c)]`, `emp`, `State input output`, `update`, `names`,
       `events`]
    \\ fs [update_def, put_char_event_def, names_def, SNOC_APPEND,
           implode_def, STRING_TYPE_def, State_def]
    \\ xsimpl)
  \\ xcon \\ xsimpl
QED

Theorem get_char_spec:
  !uv c input output events.
  limited_parts names p /\ UNIT_TYPE () uv ==>
  app (p:'ffi ffi_proj) ^(fetch_v "get_char" st) [uv]
    (SIO input output events)
    (POSTv v. &OPTION_TYPE CHAR (LHD input) v *
              if input = [||] then
                SIO input output (SNOC (get_char_eof_event) events)
              else
                SIO (THE (LTL input)) output
                    (SNOC (get_char_event (THE (LHD input))) events))
Proof
  xcf "get_char" st
  \\ qmatch_goalsub_abbrev_tac `_ * sio`
  \\ qabbrev_tac `a:word8 list = if input = [||] then
                                   [0w; 0w]
                                 else
                                   [1w; n2w (ORD (THE (LHD input)))]`
  \\ xmatch \\ rpt (xlet_auto THEN1 xsimpl)
  \\ Cases_on `input` \\ (
    fs [] \\ rename1 `W8ARRAY av`
    \\ xlet `POSTv v. &UNIT_TYPE () v * W8ARRAY av a * sio`
    THEN1 (
      xffi \\ xsimpl \\ fs [SIO_def]
      \\ qpat_abbrev_tac `s = State _ _`
      \\ MAP_EVERY qexists_tac [`emp`, `s`, `update`, `names`, `events`]
      \\ unabbrev_all_tac
      \\ fs [update_def, get_char_event_def, get_char_eof_event_def,
             names_def, SNOC_APPEND, EVAL ``REPLICATE 2 0w``, State_def]
      \\ xsimpl)
    \\ rpt (xlet_auto THEN1 xsimpl)
    \\ xlet_auto THEN1 (xsimpl \\ fs [WORD_def])
    \\ xif \\ instantiate
    \\ rpt (xlet_auto THEN1 xsimpl)
    \\ xcon \\ xsimpl \\ fs [OPTION_TYPE_def, CHR_ORD, ORD_BOUND])
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
      (SIO [||] "" []) (POSTd io. io = LREPEAT [put_char_event c])
Proof
  xcf_div "printLoop" st
  \\ MAP_EVERY qexists_tac
    [`K emp`, `\i. REPLICATE [put_char_event c] i`, `K ($= cv)`,
     `\i. State [||] (REPLICATE [c] i)`, `update`]
  \\ fs [GSYM SIO_def, REPLICATE_def]
  \\ xsimpl \\ rw [lprefix_lub_def]
  THEN1 (
    xlet `POSTv v. &UNIT_TYPE () v *
                   SIO [||] (REPLICATE [c] (SUC i))
                       (REPLICATE [put_char_event c] (SUC i))`
    THEN1 (
      xapp
      \\ MAP_EVERY qexists_tac
        [`emp`, `REPLICATE [c] i`, `[||]`,
         `REPLICATE [put_char_event c] i`, `c`]
      \\ fs [REPLICATE_SNOC] \\ xsimpl)
    \\ xvar \\ fs [REPLICATE_APPEND] \\ xsimpl)
  THEN1 fs [LPREFIX_REPLICATE_LREPEAT]

(* alternative version using REPLICATE_LREPEAT
  \\ fs [PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac `LPREFIX ll`
  \\ `ub = ll` suffices_by simp []
  \\ unabbrev_all_tac
  \\ irule REPLICATE_LREPEAT
  \\ fs []
*)

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

(* An IO-conditional loop with side effects *)

val _ = process_topdecs `
  fun echoLoop (u:unit) = case get_char () of
      None   => ()
    | Some c => (put_char c; echoLoop ());
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

val echo_def = Define `
  echo l = FLAT (MAP (\c. [get_char_event c; put_char_event c]) l)`

val lecho_def = Define `
  lecho ll = LFLATTEN (LMAP (\c. fromList [get_char_event c;
                                          put_char_event c]) ll)`

Theorem lecho_LTAKE_SUC:
  !ll c n.
    LNTH n ll = SOME c ==>
    THE (LTAKE (2 * SUC n) (lecho ll)) =
      THE (LTAKE (2 * n) (lecho ll)) ++
        [get_char_event c; put_char_event c]
Proof
  cheat
QED

Theorem echoLoop_spec:
  !uv input.
    limited_parts names p /\ UNIT_TYPE () uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "echoLoop" st) [uv]
      (SIO input "" []) (POSTvd
        (\v. &(LFINITE input /\ UNIT_TYPE () v) *
             SIO [||] (THE (toList input))
                 (SNOC get_char_eof_event (echo (THE (toList input)))))
        (\io. ~LFINITE input /\ io = lecho input))
Proof
  rw [] \\ Cases_on `LFINITE input` \\ fs [POSTvd_def, SEP_CLAUSES]
  \\ fs [SEP_F_to_cond, GSYM POSTv_def, GSYM POSTd_def]
  THEN1 (
    reverse (sg `
      (\input.
         !uv output events.
           app p echoLoop_v [uv] (SIO input output events)
             (POSTv v. &UNIT_TYPE () v *
                       SIO [||] (output ++ THE (toList input))
                           (events ++ SNOC get_char_eof_event
                                           (echo (THE (toList input))))))
        input`)
    THEN1 (
      fs [] \\ pop_assum (qspecl_then [`uv`, `[]`, `[]`] mp_tac) \\ fs [])
    \\ irule LFINITE_STRONG_INDUCTION \\ rw []
    THEN1 (
      xcf "echoLoop" st
      \\ xmatch
      \\ xlet_auto THEN1 (xcon \\ xsimpl)
      \\ xlet `POSTv v. &OPTION_TYPE CHAR NONE v *
                        SIO [||] output
                            (SNOC (get_char_eof_event) events)`
      THEN1 (
        xapp
        \\ MAP_EVERY qexists_tac [`emp`, `output`, `[||]`, `events`]
        \\ xsimpl)
      \\ xmatch \\ fs [OPTION_TYPE_def]
      \\ reverse (rw []) THEN1 EVAL_TAC
      \\ xcon \\ fs [toList, echo_def, SNOC_APPEND] \\ xsimpl)
    \\ xcf "echoLoop" st
    \\ xmatch
    \\ xlet_auto THEN1 (xcon \\ xsimpl)
    \\ xlet `POSTv v. &OPTION_TYPE CHAR (SOME h) v *
                      SIO t output (SNOC (get_char_event h) events)`
    THEN1 (
      xapp
      \\ MAP_EVERY qexists_tac [`emp`, `output`, `h ::: t`, `events`]
      \\ xsimpl)
    \\ xmatch \\ fs [OPTION_TYPE_def] \\ reverse (rpt strip_tac)
    THEN1 EVAL_TAC THEN1 EVAL_TAC
    \\ xlet `POSTv v. &UNIT_TYPE () v *
                      SIO t (SNOC h output)
                          (SNOC (put_char_event h)
                                (SNOC (get_char_event h) events))`
    THEN1 (xapp \\ fs [])
    \\ xlet_auto THEN1 (xcon \\ xsimpl)
    \\ qmatch_goalsub_abbrev_tac `SIO _ output1 events1`
    \\ qmatch_goalsub_abbrev_tac `_ * SIO _ output2 events2`
    \\ `output2 = output1 ++ THE (toList t)` by (
      unabbrev_all_tac \\ drule LFINITE_HAS_LENGTH \\ strip_tac
      \\ drule LTAKE_LLENGTH_SOME \\ strip_tac \\ fs [toList])
    \\ `events2 = events1 ++ SNOC get_char_eof_event
                                  (echo (THE (toList t)))` by (
      unabbrev_all_tac \\ fs [SNOC_APPEND, echo_def])
    \\ xapp
    \\ MAP_EVERY qexists_tac [`emp`, `output1`, `events1`]
    \\ xsimpl)
  \\ xcf_div "echoLoop" st
  \\ MAP_EVERY qexists_tac
    [`K emp`, `\i. THE (LTAKE (2 * i) (lecho input))`, `K ($= uv)`,
     `\i. State (THE (LDROP i input)) (THE (LTAKE i input))`, `update`]
  \\ fs [GSYM SIO_def] \\ xsimpl \\ rw [lprefix_lub_def]
  THEN1 (
    qmatch_goalsub_abbrev_tac `SIO input1 output1 events1`
    \\ qmatch_goalsub_abbrev_tac `&_ * _ * SIO input2 output2 events2`
    \\ Cases_on `LNTH i input` THEN1 metis_tac [LFINITE_LNTH_NONE]
    \\ rename1 `LNTH _ _ = SOME c`
    \\ `input1 = c ::: input2` by (
      Cases_on `LDROP i input` \\ Cases_on `LDROP (SUC i) input`
      \\ TRY (metis_tac [LDROP_NONE_LFINITE])
      \\ unabbrev_all_tac \\ qabbrev_tac `input2 = LDROP (SUC i) input`
      \\ drule NOT_LFINITE_DROP_LFINITE \\ disch_then drule
      \\ drule LNTH_LDROP \\ fs []
      \\ rpt strip_tac \\ unabbrev_all_tac \\ rename1 `ll = _`
      \\ Cases_on `ll` \\ fs [SUC_ONE_ADD, LDROP_ADD] \\ rfs [])
    \\ `output2 = SNOC c output1` by (
      Cases_on `LTAKE i input` \\ Cases_on `LTAKE (SUC i) input`
      \\ TRY (metis_tac [LFINITE])
      \\ unabbrev_all_tac
      \\ drule LTAKE_LNTH_EL \\ disch_then (qspec_then `i` mp_tac)
      \\ strip_tac \\ fs [LTAKE_SNOC_LNTH] \\ rfs [])
    \\ xmatch
    \\ xlet_auto THEN1 (xcon \\ xsimpl)
    \\ xlet `POSTv v. &OPTION_TYPE CHAR (SOME c) v *
                      SIO input2 output1
                          (SNOC (get_char_event c) events1)`
    THEN1 (
      xapp
      \\ MAP_EVERY qexists_tac [`emp`, `output1`, `input1`, `events1`]
      \\ xsimpl)
    \\ xmatch \\ fs [OPTION_TYPE_def] \\ reverse (rpt strip_tac)
    THEN1 EVAL_TAC THEN1 EVAL_TAC
    \\ xlet `POSTv v. &UNIT_TYPE () v * SIO input2 output2 events2`
    THEN1 (
      xapp
      \\ MAP_EVERY qexists_tac [`emp`, `output1`, `input2`,
                                `SNOC (get_char_event c) events1`, `c`]
      \\ qmatch_goalsub_abbrev_tac `&_ * SIO _ _ events'`
      \\ `events' = events2` by (
        unabbrev_all_tac \\ fs [SNOC_APPEND, lecho_LTAKE_SUC])
      \\ fs [SNOC_APPEND] \\ xsimpl)
    \\ xlet_auto THEN1 (xcon \\ xsimpl)
    \\ xvar \\ fs [SNOC_APPEND, UNIT_TYPE_def] \\ xsimpl)
  THEN1 cheat
  \\ cheat
QED

val _ = export_theory();
