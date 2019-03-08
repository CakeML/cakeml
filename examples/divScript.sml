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

Theorem lecho_LCONS:
  !h t. lecho (h ::: t) = LAPPEND (fromList [get_char_event h;
                                             put_char_event h]) (lecho t)
Proof
  rw [lecho_def]
QED

(* TODO: move LFINITE_LFLATTEN and every_LNTH to llistTheory or similar *)

Theorem LFINITE_LFLATTEN:
  !lll:'a llist llist.
    every (\ll. LFINITE ll /\ ll <> LNIL) lll ==>
    LFINITE (LFLATTEN lll) = LFINITE lll
Proof
  `!lll.
      LFINITE lll ==> llist$every (\ll. LFINITE ll /\ ll <> LNIL) lll ==>
      LFINITE (LFLATTEN lll)` by (ho_match_mp_tac LFINITE_ind \\ fs [LFINITE_APPEND])
  \\ qsuff_tac `!x.
      LFINITE x ==>
      !lll. x = LFLATTEN lll /\ llist$every (\ll. LFINITE ll /\ ll <> LNIL) lll ==>
      LFINITE lll` THEN1 (metis_tac [])
  \\ ho_match_mp_tac LFINITE_ind
  \\ fs [PULL_FORALL] \\ rw []
  THEN1 (Cases_on `lll` \\ fs [])
  \\ rename [`_ = LFLATTEN lll2`]
  \\ Cases_on `lll2` \\ fs []
  \\ rename [`h2 <> _`]
  \\ Cases_on `h2` \\ fs [] \\ rw []
  \\ rename [`LAPPEND t2`]
  \\ Cases_on `t2` \\ fs []
  \\ rename [`LAPPEND t1`]
  \\ first_x_assum (qspec_then `(h:::t1) ::: t` mp_tac) \\ fs []
QED

Theorem every_LNTH:
  !P ll. every P ll <=> !n e. LNTH n ll = SOME e ==> P e
Proof
  fs [every_def,exists_LNTH] \\ metis_tac []
QED

Theorem lecho_LFINITE:
  !ll. LFINITE ll <=> LFINITE (lecho ll)
Proof
  rw [lecho_def] \\ qmatch_goalsub_abbrev_tac `LFLATTEN ll'`
  \\ `LFINITE (LFLATTEN ll') <=> LFINITE ll'`
    suffices_by (unabbrev_all_tac \\ fs [LFINITE_MAP])
  \\ irule LFINITE_LFLATTEN
  \\ rw [every_LNTH] \\ unabbrev_all_tac \\ fs []
QED

Theorem lecho_LTAKE_SUC:
  !ll c n.
    ~LFINITE ll /\ LNTH n ll = SOME c ==>
    THE (LTAKE (2 * SUC n) (lecho ll)) =
      THE (LTAKE (2 * n) (lecho ll)) ++
        [get_char_event c; put_char_event c]
Proof
  Induct_on `n` \\ rw []
  \\ qmatch_goalsub_abbrev_tac `[g; p]`
  THEN1 (
    Cases_on `ll` \\ fs [lecho_LCONS] \\ rveq
    \\ `2 = LENGTH [g; p]` by EVAL_TAC
    \\ `IS_SOME (LTAKE (LENGTH [g; p]) (fromList [g; p]))`
      by fs [LTAKE_fromList]
    \\ drule LTAKE_LAPPEND1
    \\ disch_then (qspec_then `lecho t` mp_tac) \\ strip_tac
    \\ fs [LTAKE_fromList])
  \\ Cases_on `ll` \\ fs [lecho_LCONS]
  \\ qmatch_goalsub_abbrev_tac `g' ::: p' ::: _`
  \\ `2 * SUC n = SUC (SUC (2 * n))` by fs [MULT_CLAUSES]
  \\ `2 * SUC (SUC n) = SUC (SUC (2 * SUC n))` by fs [MULT_CLAUSES]
  \\ rw [] \\ fs []
  \\ `SUC (SUC (2 * n)) = 2 * SUC n` by fs [MULT_CLAUSES]
  \\ rw [] \\ fs [lecho_LFINITE]
  \\ drule NOT_LFINITE_TAKE \\ strip_tac
  \\ first_assum (qspec_then `2 * SUC n` mp_tac)
  \\ first_x_assum (qspec_then `2 * n` mp_tac)
  \\ rpt strip_tac \\ rw []
  \\ first_x_assum (qspecl_then [`t`, `c`] drule)
  \\ disch_then drule \\ fs []
QED

Theorem LPREFIX_LTAKE:
  !ll1 ll2.
    ~LFINITE ll1 /\ (!n. LPREFIX (fromList (THE (LTAKE n ll1))) ll2) ==>
    ll1 = ll2
Proof
  rw [LTAKE_EQ]
  \\ Cases_on `toList ll2`
  THEN1 (
    drule NOT_LFINITE_TAKE
    \\ disch_then (qspec_then `n` mp_tac) \\ strip_tac
    \\ drule LTAKE_LENGTH \\ strip_tac
    \\ first_x_assum (qspec_then `n` mp_tac) \\ strip_tac
    \\ fs [LPREFIX_fromList] \\ rfs [])
  \\ rename1 `SOME l`
  \\ first_x_assum (qspec_then `SUC (LENGTH l)` mp_tac) \\ strip_tac
  \\ fs [LPREFIX_fromList] \\ rfs []
  \\ drule NOT_LFINITE_TAKE
  \\ disch_then (qspec_then `SUC (LENGTH l)` mp_tac) \\ strip_tac
  \\ drule LTAKE_LENGTH \\ strip_tac \\ fs []
  \\ drule IS_PREFIX_LENGTH \\ strip_tac \\ fs []
QED

Theorem IS_PREFIX_TAKE:
  !l n. TAKE n l ≼ l
Proof
  Induct_on `l` \\ Cases_on `n` \\ rw []
QED

Theorem LPREFIX_LTAKE_MULT:
  !ll1 ll2 m.
    0 < m /\ ~LFINITE ll1 /\
    (!n. LPREFIX (fromList (THE (LTAKE (m * n) ll1))) ll2) ==>
    (!n. LPREFIX (fromList (THE (LTAKE n ll1))) ll2)
Proof
  rw []
  \\ first_x_assum (qspec_then `n` mp_tac) \\ strip_tac
  \\ irule LPREFIX_TRANS \\ instantiate
  \\ fs [LPREFIX_fromList_fromList]
  \\ drule NOT_LFINITE_TAKE
  \\ disch_then (qspec_then `m * n` mp_tac) \\ strip_tac
  \\ `n <= m * n` by simp []
  \\ drule (GEN_ALL LTAKE_TAKE_LESS)
  \\ disch_then drule \\ rw [IS_PREFIX_TAKE]
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
    qsuff_tac `
      (\input.
         !uv output events.
           app p echoLoop_v [uv] (SIO input output events)
             (POSTv v. &UNIT_TYPE () v *
                       SIO [||] (output ++ THE (toList input))
                           (events ++ SNOC get_char_eof_event
                                           (echo (THE (toList input))))))
        input`
    THEN1 (
      rw [] \\ pop_assum (qspecl_then [`uv`, `[]`, `[]`] mp_tac) \\ fs [])
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
  THEN1 (
    rw [LPREFIX_fromList, toList] \\ fs [lecho_LFINITE]
    \\ drule NOT_LFINITE_TAKE
    \\ disch_then (qspec_then `2 * x` mp_tac) \\ strip_tac \\ fs []
    \\ `LENGTH y = 2 * x` by (drule LTAKE_LENGTH \\ fs []) \\ fs [])
  \\ `lecho input = ub` suffices_by fs []
  \\ irule LPREFIX_LTAKE \\ fs [lecho_LFINITE]
  \\ irule LPREFIX_LTAKE_MULT \\ fs []
  \\ qexists_tac `2` \\ fs [PULL_EXISTS]
QED

(* Infinite lists encoded as cyclic pointer structures in the heap *)

val REF_LIST_def = Define `
 (REF_LIST rv [] A [] = SEP_EXISTS loc. cond(rv=Loc loc))
 /\
 (REF_LIST rv (rv2::rvs) A (x::l) =
  (SEP_EXISTS loc v1.
    cond(rv = Loc loc)
    * cell loc (Refv(Conv NONE [v1;rv2]))
    * cond(A x v1)
    * REF_LIST rv2 rvs A l
  ) /\
  (REF_LIST _ _ _ _ = &F)
 )
`

Theorem REF_LIST_extend:
  !rv rvs A l x v1.
   (REF_LIST rv rvs A l *
    SEP_EXISTS v1 loc loc'.
     cond(LAST(rv::rvs) = Loc loc)
     * cell loc (Refv(Conv NONE [v1;rv2]))
     * cond(rv2 = Loc loc')
     * cond(A x v1))
   = (REF_LIST rv (SNOC rv2 rvs) A (SNOC x l))
Proof
  PURE_ONCE_REWRITE_TAC[FUN_EQ_THM] >>
  ho_match_mp_tac (fetch "-" "REF_LIST_ind") >>
  rpt strip_tac >-
    (simp[REF_LIST_def] >>
     simp[SEP_CLAUSES] >>
     simp[AC STAR_COMM STAR_ASSOC] >>
     simp[SEP_EXISTS,cond_STAR] >>
     metis_tac[]) >-
    (pop_assum(assume_tac o REWRITE_RULE[GSYM FUN_EQ_THM] o GSYM) >>
     simp[REF_LIST_def] >>
     simp[SEP_CLAUSES] >>
     simp[AC STAR_COMM STAR_ASSOC] >>
     simp[SEP_EXISTS,cond_STAR]) >-
    (simp[REF_LIST_def,SNOC_APPEND] >>
     rename1 `REF_LIST _ (a1 ++ _)` >>
     Cases_on `a1` >> simp[REF_LIST_def,SEP_CLAUSES]) >-
    (simp[REF_LIST_def,SNOC_APPEND] >>
     rename1 `REF_LIST _ _ _ (a1 ++ _)` >>
     Cases_on `a1` >> simp[REF_LIST_def,SEP_CLAUSES])
QED

(* TODO: lots of these lemmas should probably live in characteristic/ or llistTheory *)

val (llist_upto_rules,llist_upto_ind,llist_upto_case) =
Hol_reln `
  (llist_upto R x x) /\
  (R x y ==> llist_upto R x y) /\
  (llist_upto R x y /\ llist_upto R y z ==> llist_upto R x z) /\
  (llist_upto R x y ==> llist_upto R (LAPPEND z x) (LAPPEND z y))
  `

val [llist_upto_eq,llist_upto_rel,llist_upto_trans,llist_upto_context] =
  llist_upto_rules |> SPEC_ALL |> CONJUNCTS |> map GEN_ALL
  |> curry (ListPair.map save_thm)
    ["llist_upto_eq","llist_upto_rel",
     "llist_upto_trans","llist_upto_context"]

Theorem LLIST_BISIM_UPTO:
  ∀ll1 ll2 R.
    R ll1 ll2 ∧
    (∀ll3 ll4.
      R ll3 ll4 ⇒
      ll3 = [||] ∧ ll4 = [||] ∨
      LHD ll3 = LHD ll4 ∧
      llist_upto R (THE (LTL ll3)) (THE (LTL ll4)))
  ==> ll1 = ll2
Proof
  rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[LLIST_BISIMULATION]
  >> qexists_tac `llist_upto R`
  >> conj_tac >- rw[llist_upto_rules]
  >> ho_match_mp_tac llist_upto_ind
  >> rpt conj_tac
  >- rw[llist_upto_rules]
  >- first_x_assum ACCEPT_TAC
  >- (rw[]
      >> match_mp_tac OR_INTRO_THM2
      >> conj_tac >- simp[]
      >> metis_tac[llist_upto_rules])
  >- (rw[llist_upto_rules]
      >> Cases_on `ll3 = [||]`
      >- (Cases_on `ll4` >> fs[llist_upto_rules])
      >> match_mp_tac OR_INTRO_THM2
      >> conj_tac
      >- (Cases_on `z` >> simp[])
      >> Cases_on `z` >- simp[]
      >> simp[]
      >> Cases_on `ll3` >> Cases_on `ll4`
      >> fs[] >> rveq
      >> CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM(CONJUNCT1 LAPPEND)]))))
      >> CONV_TAC(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM(CONJUNCT1 LAPPEND)])))))
      >> PURE_ONCE_REWRITE_TAC[GSYM(CONJUNCT2 LAPPEND)]
      >> simp[GSYM LAPPEND_ASSOC]
      >> metis_tac[llist_upto_rules])
QED

Theorem REF_cell_eq:
  loc ~~>> Refv v = Loc loc ~~> v
Proof
  rw[FUN_EQ_THM,cell_def,REF_def,SEP_EXISTS,cond_STAR]
QED

val LTAKE_LNTH_EQ = Q.prove(
  `!x ll y. LTAKE (LENGTH x) ll = SOME x
   /\ y < LENGTH x
   ==> LNTH y ll = SOME(EL y x)`,
  Induct_on `x` >> rw[LTAKE] >>
  Cases_on `ll` >> fs[] >>
  PURE_FULL_CASE_TAC >> fs[] >> rveq >>
  Cases_on `y` >> fs[]);

Theorem LTAKE_LPREFIX:
  !x ll.
   ~LFINITE ll ==> ?l. LTAKE x ll = SOME l /\
   LPREFIX (fromList l) ll
Proof
  Induct >> rw[] >>
  Cases_on `ll` >> fs[] >>
  first_x_assum(drule_then strip_assume_tac) >>
  fs[LPREFIX_LCONS]
QED

Theorem LMAP_fromList:
  LMAP f (fromList l) = fromList(MAP f l)
Proof
  Induct_on `l` >> fs[]
QED

Theorem LTAKE_LMAP:
  !n f ll. LTAKE n (LMAP f ll) =
   OPTION_MAP (MAP f) (LTAKE n ll)
Proof
  Induct_on `n` >> rw[] >>
  Cases_on `ll` >> fs[OPTION_MAP_COMPOSE,o_DEF]
QED

Theorem LNTH_LREPEAT:
  !i x l.
  LNTH i (LREPEAT l) = SOME x
  ==> x = EL (i MOD LENGTH l) l
Proof
  Induct_on `i DIV LENGTH l` >> rw[]
  >- (Cases_on `l = []`
      >> fs[Once LREPEAT_thm]
      >> fs[LNTH_LAPPEND]
      >> `0 < LENGTH l` by(Cases_on `l` >> fs[])
      >> qpat_x_assum `0 = _` (assume_tac o GSYM)
      >> rfs[RatProgTheory.DIV_EQ_0]
      >> fs[LNTH_fromList])
  >> fs[ADD1]
  >> `LENGTH l <= i`
       by(CCONTR_TAC >> fs[LESS_DIV_EQ_ZERO])
  >> `0 < LENGTH l` by(Cases_on `l` >> fs[])
  >> `v = (i - LENGTH l) DIV LENGTH l`
       by(fs[Q.INST[`q`|->`1`] DIV_SUB |> REWRITE_RULE [MULT_CLAUSES]])
  >> first_x_assum drule
  >> drule lnth_some_down_closed
  >> disch_then(qspec_then `i - LENGTH l` mp_tac)
  >> impl_tac >- simp[]
  >> strip_tac
  >> disch_then drule
  >> strip_tac
  >> rveq
  >> qpat_x_assum `LNTH (_ - _) _ = _`
       (fn thm => qpat_x_assum `LNTH _ _ = _` mp_tac >> assume_tac thm)
  >> simp[Once LREPEAT_thm]
  >> fs[LNTH_LAPPEND]
  >> fs[SUB_MOD]
QED

Theorem REF_LIST_is_loc:
  !rv rvs A l h. REF_LIST rv rvs A l h ==> ?loc. rv = Loc loc
Proof
  ho_match_mp_tac (fetch "-" "REF_LIST_ind") >>
  rw[REF_LIST_def,SEP_CLAUSES,SEP_F_def,STAR_def,SEP_EXISTS,cond_def]
QED

Theorem REF_LIST_LENGTH:
  !rv rvs A l h. REF_LIST rv rvs A l h ==> LENGTH rvs = LENGTH l
Proof
  ho_match_mp_tac (fetch "-" "REF_LIST_ind") >>
  rw[REF_LIST_def,SEP_CLAUSES,SEP_F_def,STAR_def,SEP_EXISTS,cond_def] >>
  metis_tac[]
QED

Theorem REF_LIST_rotate_1:
  REF_LIST rv (SNOC rv (rv2::rvs)) A (x::l) =
  REF_LIST rv2 (SNOC rv2 (SNOC rv rvs)) A (SNOC x l)
Proof
  rw[FUN_EQ_THM] >>
  simp[REF_LIST_def,GSYM REF_LIST_extend,Once LAST_DEF] >>
  simp[SEP_CLAUSES,AC STAR_COMM STAR_ASSOC] >>
  simp[SEP_EXISTS,cond_STAR] >>
  rw[EQ_IMP_THM] >-
    (asm_exists_tac >> simp[] >>
     fs[STAR_def] >> Cases_on `l` >>
     fs[REF_LIST_def] >> metis_tac[REF_LIST_is_loc]) >>
  metis_tac[]
QED

val push_cond = Q.prove(`
   m ~~>> v * (&C * B) = cond C * (m ~~>> v * B)
/\ m ~~>> v * &C = &C * m ~~>> v
/\ REF_LIST rv rvs A l * (&C * B) = cond C * (REF_LIST rv rvs A l * B)
/\ REF_LIST rv rvs A l * &C = &C * REF_LIST rv rvs A l
`,
  simp[AC STAR_COMM STAR_ASSOC]);

val EL_LENGTH_TAKE = Q.prove(
  `!h e. EL (LENGTH l) (h::TAKE (LENGTH l) (e::l))
   = EL(LENGTH l) (h::e::l)`,
 Induct_on `l` >> fs[]);

val EL_LENGTH_TAKE2 = Q.prove(
  `!h e l. n < LENGTH l ==>
   EL n (h::TAKE n (e::l))
   = EL n (h::e::l)`,
 Induct_on `n` >> rw[] >>
 Cases_on `l` >> fs[]);

val PRE_SUB = Q.prove(
  `!n. n <> 0 ==> PRE n = n - 1`,
  Cases >> simp[]);

Theorem REF_LIST_rv_loc:
  REF_LIST rv rvs n l h ==> ?loc. rv = Loc loc
Proof
  rpt strip_tac >>
  imp_res_tac REF_LIST_LENGTH >>
  Cases_on `l` >>
  Cases_on `rvs` >>
  fs[REF_LIST_def,SEP_EXISTS,cond_STAR,cond_def,STAR_def]
QED

Theorem REF_LIST_rotate_n:
  !n rv rvs A l.
  n < LENGTH l ==>
  REF_LIST rv (SNOC rv rvs) A l =
    REF_LIST (EL n (rv::rvs))
             (DROP n (SNOC rv rvs)
               ++
              TAKE n (SNOC rv rvs)
             )
           A (DROP n l ++ TAKE n l)
Proof
  rpt gen_tac >>
  reverse(Cases_on `LENGTH l = LENGTH rvs + 1`) >-
    (rw[FUN_EQ_THM,EQ_IMP_THM] >>
     imp_res_tac REF_LIST_LENGTH >>
     fs[LENGTH_TAKE_EQ]) >>
  simp[FUN_EQ_THM] >>
  rpt(pop_assum mp_tac) >>
  Induct_on `n` >- rw[REF_LIST_def] >>
  rpt strip_tac >>
  first_x_assum(drule) >>
  disch_then(qspec_then `x` mp_tac) >>
  impl_tac >- fs[] >>
  strip_tac >> fs[ADD1] >>
  Cases_on `l` >> fs[ADD1] >>
  Cases_on `n` >-
    (Cases_on `rvs` >> fs[REF_LIST_def,GSYM SNOC_APPEND] >>
     fs[GSYM REF_LIST_rotate_1] >> fs[REF_LIST_def]) >>
  Cases_on `rvs` >>
  fs[DROP_SNOC,TAKE_SNOC] >>
  fs[DROP_CONS_EL] >>
  fs[ADD1,REF_LIST_def] >>
  fs[TAKE_EL_SNOC] >>
  Cases_on `n' + 1 = LENGTH t'` >-
    (fs[DROP_LENGTH_NIL] >>
     PURE_REWRITE_TAC[GSYM SNOC] >>
     PURE_REWRITE_TAC[REF_LIST_rotate_1] >>
     fs[DROP_LENGTH_TOO_LONG,REF_LIST_def,GSYM REF_LIST_extend] >>
     fs[SEP_CLAUSES,AC STAR_COMM STAR_ASSOC] >>
     fs[LAST_EL] >> fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
     rveq >> fs[] >> rveq >> fs[cond_CONJ] >>
     rw[SEP_EXISTS] >>
     simp[push_cond] >>
     simp[STAR_ASSOC,GSYM cond_CONJ] >>
     simp[GSYM STAR_ASSOC,cond_STAR] >>
     fs[AC CONJ_ASSOC CONJ_SYM] >>
     rw[EL_LENGTH_TAKE,SNOC_APPEND,EL_APPEND_EQN,EL_LENGTH_TAKE] >>
     fs[AC CONJ_ASSOC CONJ_SYM] >>
     rw[EQ_IMP_THM] >>
     rpt(asm_exists_tac >> simp[]) >>
     metis_tac[STAR_ASSOC, STAR_COMM]) >>
  `SUC n' < LENGTH t'` by simp[] >>
  fs[ADD1,DROP_CONS_EL] >>
  PURE_REWRITE_TAC[GSYM SNOC,Once APPEND_SNOC] >>
  PURE_REWRITE_TAC[REF_LIST_rotate_1] >>
  fs[REF_LIST_def,GSYM REF_LIST_extend] >>
  PURE_REWRITE_TAC[GSYM SNOC,APPEND_SNOC,GSYM REF_LIST_extend] >>
  fs[SEP_CLAUSES,AC STAR_COMM STAR_ASSOC] >>
  fs[LAST_EL] >> fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
  rveq >> fs[] >> rveq >> fs[cond_CONJ] >>
  rw[SEP_EXISTS] >>
  simp[push_cond] >>
  simp[STAR_ASSOC,GSYM cond_CONJ] >>
  simp[GSYM STAR_ASSOC,cond_STAR] >>
  fs[AC CONJ_ASSOC CONJ_SYM,ADD1] >>
  rw[EL_LENGTH_TAKE,SNOC_APPEND,EL_APPEND_EQN,EL_LENGTH_TAKE] >>
  fs[AC CONJ_ASSOC CONJ_SYM] >>
  rw[EQ_IMP_THM] >>
  rpt(asm_exists_tac >> simp[]) >>
  rename1 `y1 ~~>> _ * (_ ~~>> Refv (Conv NONE [y2; _]) * _)` >>
  MAP_EVERY qexists_tac [`y1`,`y2`] >>
  rfs[] >>
  rw[EL_CONS_IF] >> fs[] >>
  Cases_on `t'` >> fs[] >>
  rw[EL_APPEND_EQN] >> fs[] >>
  fs[ADD1,EL_LENGTH_TAKE2,REWRITE_RULE [ADD1] EL] >>
  fs[STAR_def] >>
  fs[EL_APPEND_EQN] >> rfs[] >>
  fs[EL_CONS_IF,EL_APPEND_EQN,EL_LENGTH_TAKE2] >> rw[] >> fs[] >> rfs[] >>
  fs[PRE_SUB] >> rfs[PRE_SUB] >>
  fs[EL_TAKE] >> imp_res_tac REF_LIST_rv_loc >>
  simp[]
QED

val highly_specific_MOD_lemma = Q.prove(
  `!n a. n < a
   ==> (n + 2) MOD (a + 1)
    = if n + 1 = a then 0 else (n + 1) MOD a + 1`,
  rw[] >> rw[]);

val highly_specific_MOD_lemma2 = Q.prove(
 `0 < LENGTH l
  ==>
  EL ((i+1) MOD LENGTH l) (CONS (LAST l) (FRONT l))
  = EL (i MOD LENGTH l) l`,
strip_tac >>
Cases_on `1 < LENGTH l` >-
  (Cases_on `i MOD LENGTH l = LENGTH l - 1` >-
     (drule(GSYM MOD_PLUS) >>
      disch_then(qspecl_then[`i`,`1`] mp_tac) >>
      disch_then(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
      pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
      simp[ONE_MOD] >>
      Q.ISPEC_THEN `l` assume_tac SNOC_CASES >>
      fs[] >> rveq >> fs[EL_APPEND2]) >>
   drule(GSYM MOD_PLUS) >>
   disch_then(qspecl_then[`i`,`1`] mp_tac) >>
   disch_then(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
   drule ONE_MOD >>
   disch_then(fn thm => PURE_ONCE_REWRITE_TAC [thm]) >>
   `i MOD LENGTH l < LENGTH l - 1`
     by(drule_then(qspec_then `i` mp_tac) MOD_LESS >>
        intLib.COOPER_TAC) >>
   `i MOD LENGTH l + 1 < LENGTH l` by simp[] >>
   simp[LESS_MOD] >>
   simp[REWRITE_RULE [ADD1] EL_CONS] >>
   simp[DECIDE ``!n. PRE(n+1) = n``] >>
   match_mp_tac EL_FRONT >>
   Q.ISPEC_THEN `l` assume_tac SNOC_CASES >>
   fs[] >> rveq >> fs[FRONT_APPEND]) >>
  Cases_on `l` >> fs[] >> Cases_on `t` >> fs[]);

Theorem LIST_ROTATE_CONS_NEXT:
  !n l. n < LENGTH l ==> ?l'.
   DROP n l ++ TAKE n l = (EL ((n + 1) MOD LENGTH l) (LAST l :: BUTLAST l))::l'
Proof
  Induct_on `n` >> Cases >> fs[] >> rw[]
  >- (Cases_on `t` >> fs[])
  >> fs[RIGHT_EXISTS_IMP_THM] >> rw []
  >> first_x_assum(drule_then strip_assume_tac)
  >> fs[]
  >> fs[APPEND_EQ_APPEND_MID,APPEND_EQ_APPEND]
  >> fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)]
  >> rveq >> fs[]
  >> fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)]
  >> fs[DROP_NIL]
  >> fs[ADD1,highly_specific_MOD_lemma]
  >> rw[]
  >- (Cases_on `t` >> fs[])
  >> PURE_REWRITE_TAC[EL,GSYM ADD1,TL]
  >> rw[Once EL_CONS_IF]
  >> simp[DECIDE ``PRE(n+2) = SUC n``]
  >> Cases_on `t` >> fs[]
QED

val LNTH_LREPEAT_ub = Q.prove(
  `!n l.
    (l <> []
    /\
    ∀x.
    LPREFIX
    (fromList (THE (LTAKE x (LMAP put_char_event (LREPEAT l)))))
    ub)
    ==>
    LNTH n ub
    =
    LNTH n (LAPPEND (fromList (MAP put_char_event l)) ub)
  `,
  rpt strip_tac >>
  `~LFINITE(LREPEAT l)`
    by(rw[LFINITE_LLENGTH,LLENGTH_MAP,LLENGTH_LREPEAT,NULL_EQ] >>
       CCONTR_TAC >> fs[]) >>
  `!y. LNTH y ub = SOME(put_char_event(EL (y MOD LENGTH l) l))`
    by(strip_tac >>
       first_x_assum(qspec_then `SUC y` mp_tac) >>
       strip_tac >>
       fs[LPREFIX_APPEND,LTAKE_LMAP] >>
       drule NOT_LFINITE_TAKE >>
       disch_then(qspec_then `SUC y` strip_assume_tac) >>
       fs[] >>
       imp_res_tac LTAKE_LENGTH >>
       fs[LNTH_LAPPEND] >>
       rename1 `SUC y = STRLEN z` >>
       `y < LENGTH(MAP put_char_event z)` by simp[] >>
       imp_res_tac lnth_fromList_some >>
       simp[] >>
       drule LTAKE_LNTH_EQ >>
       disch_then(qspec_then `y` mp_tac) >>
       impl_tac >- simp[] >>
       strip_tac >>
       drule_then(assume_tac o GSYM) LNTH_LREPEAT >>
       fs[EL_MAP]) >>
  `~LFINITE ub`
    by(simp[LFINITE_LLENGTH]
       >> CCONTR_TAC >> fs[]
       >> rename1 `LLENGTH ub = SOME ul`
       >> qpat_x_assum `!x. LPREFIX _ _` (qspec_then `SUC ul` assume_tac)
       >> fs[LPREFIX_APPEND]
       >> rveq
       >> fs[LLENGTH_APPEND]
       >> `~LFINITE(LMAP put_char_event (LREPEAT l))` by simp[LFINITE_MAP]
       >> drule_then(qspec_then `SUC ul` strip_assume_tac) LTAKE_LPREFIX
       >> imp_res_tac LTAKE_LENGTH
       >> fs[]) >>
  simp[LNTH_LAPPEND,LLENGTH_MAP,LNTH_fromList] >>
  simp[EL_MAP] >>
  IF_CASES_TAC >- simp[] >>
  `0 < LENGTH l` by(Cases_on `l` >> fs[]) >>
  simp[SUB_MOD]);

val LPREFIX_ub_LAPPEND = Q.prove(
  `l <> [] /\
   (∀x.
    LPREFIX
     (fromList (THE (LTAKE x (LMAP put_char_event (LREPEAT l)))))
     ub
   )
   ==> ub = LAPPEND (fromList(MAP put_char_event l)) ub`,
  rpt strip_tac >>
  simp[LTAKE_EQ,PULL_FORALL] >>
  Induct_on `n` >> rw[] >>
  fs[LTAKE_SNOC_LNTH] >>
  metis_tac[LNTH_LREPEAT_ub]);

val _ = process_topdecs `
  fun pointerLoop c = (
    case !c of
     (a,b) => (put_char a; pointerLoop b));
  ` |> append_prog;

val st = ml_translatorLib.get_ml_prog_state();

Theorem pointerLoop_spec:
  !c cv rv.
    limited_parts names p ==>
    app (p:'ffi ffi_proj) ^(fetch_v "pointerLoop" st) [rv]
      (SIO [||] "" [] * REF_LIST rv (SNOC rv rvs) CHAR l)
      (POSTd io. io = LMAP put_char_event (LREPEAT l))
Proof
  reverse(Cases_on `LENGTH l = SUC(LENGTH rvs)`)
  THEN1 (
    rw[app_def,app_basic_def,STAR_def] >>
    imp_res_tac REF_LIST_LENGTH >> fs[])
  \\ xcf_div "pointerLoop" st
  \\ MAP_EVERY qexists_tac
    [`K(REF_LIST rv (SNOC rv rvs) CHAR l)`, `\i. THE(LTAKE i (LMAP put_char_event (LREPEAT l)))`,
     `\i. $= (EL (i MOD (LENGTH rvs + 1)) (rv::rvs))`,
     `\i. State [||] (THE(LTAKE i (LREPEAT l)))`,`update`]
  \\ fs [GSYM SIO_def, REPLICATE_def]
  \\ xsimpl \\ rw [lprefix_lub_def]
  THEN1 (
    xlet `POSTv v. SEP_EXISTS cv lv.
          &(v = Conv NONE[cv;lv]) *
          &(CHAR (EL (i MOD (LENGTH rvs + 1)) l) cv) *
          &(lv = EL ((i+1) MOD (LENGTH rvs + 1)) (rv::rvs)) *
          REF_LIST rv (SNOC rv rvs) CHAR l *
          SIO [||] (THE (LTAKE i (LREPEAT l)))
           (THE (LTAKE i (LMAP put_char_event (LREPEAT l))))`
    THEN1 (
      `i MOD (LENGTH rvs + 1) < LENGTH rvs + 1`
        by(match_mp_tac MOD_LESS \\ simp[])
      \\ `i MOD (LENGTH rvs + 1) < LENGTH l`
        by simp[]
      \\ drule_then(qspecl_then[`rv`,`rvs`,`CHAR`] assume_tac) REF_LIST_rotate_n
      \\ drule LIST_ROTATE_CONS_NEXT \\ strip_tac
      \\ FULL_SIMP_TAC std_ss []
      \\ `i MOD (LENGTH rvs + 1) < LENGTH(SNOC rv rvs)` by simp[]
      \\ drule LIST_ROTATE_CONS_NEXT \\ strip_tac
      \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC]
      \\ simp[REF_LIST_def]
      \\ xpull
      \\ xapp
      \\ xsimpl
      \\ CONV_TAC SWAP_EXISTS_CONV
      \\ qmatch_goalsub_abbrev_tac `Refv a1` \\ qexists_tac `a1` \\ qunabbrev_tac `a1`
      \\ simp[REF_cell_eq]
      \\ simp[GSYM STAR_ASSOC]
      \\ qmatch_goalsub_abbrev_tac `_ ~~> _ * a1` \\ qexists_tac `a1` \\ qunabbrev_tac `a1`
      \\ simp[SEP_IMP_REFL]
      \\ rename1 `CHAR _ v1`
      \\ qexists_tac `v1`
      \\ xsimpl
      \\ simp[ADD1]
      \\ qpat_x_assum `CHAR _ _` mp_tac
      \\ simp[ADD1]
      \\ qpat_x_assum `LENGTH _ = _` (assume_tac o REWRITE_RULE[ADD1] o GSYM)
      \\ simp[highly_specific_MOD_lemma2])
    \\ xmatch
    \\ xlet `POSTv v. &UNIT_TYPE () v * SEP_EXISTS cv lv.
             REF_LIST rv (SNOC rv rvs) CHAR l *
             SIO [||] (THE (LTAKE (SUC i) (LREPEAT l)))
               (THE (LTAKE (SUC i) (LMAP put_char_event (LREPEAT l))))`
    THEN1 (
      xapp
      \\ xsimpl
      \\ asm_exists_tac
      \\ simp[]
      \\ qexists_tac `REF_LIST rv (SNOC rv rvs) CHAR l * GC`
      \\ xsimpl
      \\ qmatch_goalsub_abbrev_tac `SIO [||] a1 a2`
      \\ MAP_EVERY qexists_tac [`a1`,`[||]`,`a2`]
      \\ MAP_EVERY qunabbrev_tac [`a1`,`a2`]
      \\ xsimpl
      \\ fs[LTAKE_LMAP]
      \\ `~LFINITE(LREPEAT l)`
         by(rw[LFINITE_LLENGTH,LLENGTH_MAP,LLENGTH_LREPEAT,NULL_EQ] >>
            CCONTR_TAC >> fs[])
      \\ drule NOT_LFINITE_TAKE
      \\ disch_then(qspec_then `i` strip_assume_tac)
      \\ fs[]
      \\ fs[]
      \\ fs[LTAKE_SNOC_LNTH]
      \\ imp_res_tac infinite_lnth_some
      \\ pop_assum(qspec_then `i` strip_assume_tac)
      \\ fs[SNOC_APPEND]
      \\ qpat_x_assum `LENGTH _ = SUC _` (assume_tac o REWRITE_RULE[ADD1] o GSYM)
      \\ fs[]
      \\ drule LNTH_LREPEAT
      \\ strip_tac
      \\ rveq
      \\ simp[SEP_IMP_REFL])
    \\ xvar \\ xsimpl \\ simp[ADD1])
  THEN1 (
    `~LFINITE(LMAP put_char_event (LREPEAT l))`
      by(rw[LFINITE_LLENGTH,LLENGTH_MAP,LLENGTH_LREPEAT,NULL_EQ] >>
         CCONTR_TAC >> fs[])
    \\ drule_then(qspec_then `x` strip_assume_tac) LTAKE_LPREFIX
    \\ fs[])
  \\ qmatch_goalsub_abbrev_tac `LPREFIX a1 a2`
  \\ `a1 = a2` suffices_by simp[]
  \\ unabbrev_all_tac
  \\ match_mp_tac LLIST_BISIM_UPTO
  \\ qexists_tac `\x y. x = LMAP put_char_event (LREPEAT l) /\ y = ub`
  \\ conj_tac >- simp[]
  \\ rw[]
  \\ match_mp_tac OR_INTRO_THM2
  \\ conj_tac
  THEN1 (
    simp[Once LREPEAT_thm]
    \\ Cases_on `l`
    \\ fs[PULL_EXISTS]
    \\ first_x_assum(qspec_then `1` mp_tac)
    \\ simp[Once LREPEAT_thm]
    \\ simp_tac bool_ss [ONE,LTAKE_THM]
    \\ rw[LPREFIX_APPEND]
    \\ simp[LHD_LCONS])
  \\ fs[PULL_EXISTS]
  \\ `l <> []` by(CCONTR_TAC >> fs[])
  \\ drule_then drule (GEN_ALL LPREFIX_ub_LAPPEND)
  \\ disch_then(fn thm => CONV_TAC(RAND_CONV(PURE_ONCE_REWRITE_CONV [thm])))
  \\ CONV_TAC(RATOR_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [LREPEAT_thm])))
  \\ Cases_on `l` \\ fs[LMAP_APPEND,LMAP_fromList]
  \\ match_mp_tac llist_upto_context
  \\ match_mp_tac llist_upto_rel
  \\ simp[]
QED

val _ = export_theory();
