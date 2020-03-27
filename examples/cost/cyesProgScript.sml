(*
  A data-cost example of a non-terminating function (cyes)
  that prints a character indefinitely
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open miniBasisProgTheory;
open x64_configProofTheory;

val _ = new_theory "cyesProg"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

(* ************************** *)
(* * cyes (with mini-basis) * *)
(* ************************** *)

val _ = translation_extends "miniBasisProg";

val whole_prog = whole_prog ()

val _ = (append_prog o process_topdecs) `
  fun put_char c = let
        val s = String.implode [c]
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val _ = #(put_char) s a
        in () end;
  `

val _ = (append_prog o process_topdecs) `
  fun printLoop c = (put_char c; printLoop c);
  `

val maincall = process_topdecs `val _ = printLoop #"a"`

local
  val prog = get_prog(get_ml_prog_state())
in
  val cyes = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

(* A small IO model *)
open cfDivTheory;

val names_def = Define `names = ["put_char"]`;

val put_char_event_def = Define `
  put_char_event c = IO_event "put_char" [n2w (ORD c)] []`;

val put_str_event_def = Define `
  put_str_event cs = IO_event "put_char" (MAP (n2w o ORD) cs) []`;

val update_def = Define `
  (update "put_char" cs l s = SOME (FFIreturn l s))`

val State_def = Define `
  State = Stream [||]`

val SIO_def = Define `
  SIO events =
    one (FFI_part (State) update names events)`

val st = ml_translatorLib.get_ml_prog_state();

Theorem put_char_spec:
  !c cv events.
  limited_parts names p /\ CHAR c cv ==>
  app (p:'ffi ffi_proj) ^(fetch_v "put_char" st) [cv]
    (SIO events)
    (POSTv v. &UNIT_TYPE () v *
              SIO (SNOC (put_char_event c) events))
Proof
  xcf "put_char" st
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet
    `POSTv v. &STRING_TYPE (implode [c]) v * SIO events`
  THEN1 (xapp \\ xsimpl \\ qexists_tac `[c]` \\ fs [LIST_TYPE_def])
  \\ xlet `POSTv v. &WORD8 0w v * SIO events` THEN1 (xapp \\ xsimpl)
  \\ xlet `POSTv v. W8ARRAY v [] * SIO events` THEN1 (xapp \\ xsimpl \\ goal_assum drule)
  \\ rename1 `W8ARRAY av`
  \\ xlet
    `POSTv v. &UNIT_TYPE () v * W8ARRAY av [] *
              SIO (SNOC (put_char_event c) events)`
  THEN1 (
    xffi \\ xsimpl \\ fs [SIO_def]
    \\ MAP_EVERY qexists_tac
      [`[n2w (ORD c)]`, `emp`, `State`, `update`, `names`, `events`]
    \\ fs [update_def, put_char_event_def, names_def, SNOC_APPEND,
           implode_def, STRING_TYPE_def, State_def]
    \\ xsimpl)
  \\ xcon \\ xsimpl
QED

(* TODO: Move REPLICATE_LIST and lemmas to an appropriate theory;
         this is copypasted from divScript *)

val REPLICATE_LIST_def = Define `
  (!l. REPLICATE_LIST l 0 = []) /\
  (!l n. REPLICATE_LIST l (SUC n) = REPLICATE_LIST l n ++ l)`

Theorem REPLICATE_LIST_SNOC:
  !x n. SNOC x (REPLICATE_LIST [x] n) = REPLICATE_LIST [x] (SUC n)
Proof
  rw [REPLICATE_LIST_def]
QED

Theorem REPLICATE_LIST_APPEND:
  !l n. REPLICATE_LIST l n ++ l = REPLICATE_LIST l (SUC n)
Proof
  rw [REPLICATE_LIST_def]
QED

Theorem REPLICATE_LIST_APPEND_SYM:
  !l n. REPLICATE_LIST l n ++ l = l ++ REPLICATE_LIST l n
Proof
  strip_tac \\ Induct_on `n` \\ fs [REPLICATE_LIST_def]
QED

Theorem REPLICATE_LIST_LENGTH:
  !l n. LENGTH (REPLICATE_LIST l n) = LENGTH l * n
Proof
  Induct_on `n` THEN1 (EVAL_TAC \\ fs [])
  \\ rw [REPLICATE_LIST_def, MULT_CLAUSES]
QED

Theorem LPREFIX_REPLICATE_LIST_LREPEAT:
  !l n. LPREFIX (fromList (REPLICATE_LIST l n)) (LREPEAT l)
Proof
  strip_tac \\ Induct_on `n`
  \\ fs [REPLICATE_LIST_def, REPLICATE_LIST_APPEND_SYM, GSYM LAPPEND_fromList]
  \\ rw [Once LREPEAT_thm] \\ fs [LPREFIX_APPEND]
  \\ qexists_tac `ll` \\ fs [LAPPEND_ASSOC]
QED

Theorem LTAKE_EQ_MULT:
  !ll1 ll2 m.
    0 < m /\ ~LFINITE ll1 /\
    (!n. LTAKE (m * n) ll1 = LTAKE (m * n) ll2) ==>
    (!n. LTAKE n ll1 = LTAKE n ll2)
Proof
  rw []
  \\ first_x_assum (qspec_then `n` mp_tac) \\ strip_tac
  \\ drule NOT_LFINITE_TAKE
  \\ disch_then (qspec_then `m * n` mp_tac) \\ strip_tac \\ fs []
  \\ rename1 `SOME l`
  \\ `n <= m * n` by fs []
  \\ `LTAKE n ll1 = SOME (TAKE n l)` by (
    irule LTAKE_TAKE_LESS \\ qexists_tac `m * n` \\ fs [])
  \\ `LTAKE n ll2 = SOME (TAKE n l)` by (
    irule LTAKE_TAKE_LESS \\ qexists_tac `m * n` \\ fs [])
  \\ fs []
QED

Theorem LTAKE_LAPPEND_fromList:
  !ll l n.
    LTAKE (n + LENGTH l) (LAPPEND (fromList l) ll) =
      OPTION_MAP (APPEND l) (LTAKE n ll)
Proof
  rw [] \\ Cases_on `LTAKE n ll` \\ fs []
  THEN1 (
    `LFINITE ll` by (fs [LFINITE] \\ instantiate)
    \\ drule LFINITE_HAS_LENGTH \\ strip_tac \\ rename1 `SOME m`
    \\ irule LTAKE_LLENGTH_NONE
    \\ qexists_tac `m + LENGTH l` \\ rw []
    THEN1 (
      drule LTAKE_LLENGTH_SOME \\ strip_tac
      \\ Cases_on `n ≤ m` \\ fs []
      \\ drule (GEN_ALL LTAKE_TAKE_LESS)
      \\ disch_then drule \\ fs [])
    \\ fs [LLENGTH_APPEND, LFINITE_fromList])
  \\ Induct_on `l` \\ rw []
  \\ fs [LTAKE_CONS_EQ_SOME]
  \\ instantiate
QED

Theorem REPLICATE_LIST_LREPEAT:
  !l ll.
    l <> [] /\ (!n. LPREFIX (fromList (REPLICATE_LIST l n)) ll) ==>
    (ll = LREPEAT l)
Proof
  rw [LTAKE_EQ]
  \\ Cases_on `toList ll`
  THEN1 (
    irule LTAKE_EQ_MULT
    \\ `~LFINITE ll` by fs [LFINITE_toList_SOME] \\ fs []
    \\ qexists_tac `LENGTH l`
    \\ `0 < LENGTH l` by (Cases_on `l` \\ fs []) \\ rw []
    \\ rpt (pop_assum mp_tac) \\ qid_spec_tac `ll`
    \\ Induct_on `n` \\ rw []
    \\ `?ll1. ll = LAPPEND (fromList l) ll1` by (
      first_x_assum (qspec_then `1` mp_tac) \\ strip_tac
      \\ fs [LPREFIX_APPEND, EVAL ``REPLICATE_LIST l 1``]
      \\ rename1 `LAPPEND _ ll1`
      \\ qexists_tac `ll1` \\ fs [])
    \\ `~LFINITE ll1` by fs [LFINITE_APPEND, LFINITE_fromList]
    \\ `toList ll1 = NONE` by fs [LFINITE_toList_SOME]
    \\ `!n. LPREFIX (fromList (REPLICATE_LIST l n)) ll1` by (
      strip_tac \\ rename1 `REPLICATE_LIST _ n1`
      \\ first_x_assum (qspec_then `SUC n1` mp_tac) \\ strip_tac
      \\ fs [LPREFIX_fromList] \\ rfs []
      \\ fs [REPLICATE_LIST_LENGTH, MULT_CLAUSES]
      \\ qspecl_then [`ll1`, `l`, `n1 * LENGTH l`] mp_tac
                     LTAKE_LAPPEND_fromList \\ strip_tac
      \\ fs [REPLICATE_LIST_def, REPLICATE_LIST_APPEND_SYM])
    \\ first_x_assum (qspec_then `ll1` drule)
    \\ rpt (disch_then drule) \\ strip_tac \\ rveq
    \\ `LENGTH l * SUC n = LENGTH l * n + LENGTH l` by fs [MULT_CLAUSES]
    \\ qspecl_then [`ll1`, `l`, `LENGTH l * n`] mp_tac
                   LTAKE_LAPPEND_fromList \\ strip_tac
    \\ rw [Once LREPEAT_thm]
    \\ qspecl_then [`LREPEAT l`, `l`, `LENGTH l * n`] mp_tac
                   LTAKE_LAPPEND_fromList \\ strip_tac
    \\ fs [])
  \\ first_x_assum (qspec_then `SUC (LENGTH x)` mp_tac) \\ strip_tac
  \\ fs [LPREFIX_fromList] \\ rfs []
  \\ drule IS_PREFIX_LENGTH \\ strip_tac
  \\ fs [REPLICATE_LIST_LENGTH]
  \\ Cases_on `l` \\ Cases_on `LENGTH x` \\ fs [MULT_CLAUSES]
QED

Theorem printLoop_spec:
  !c cv.
    limited_parts names p /\ CHAR c cv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "printLoop" st) [cv]
      (SIO []) (POSTd io. io = LREPEAT [put_char_event c])
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "printLoop" st
  \\ MAP_EVERY qexists_tac
    [`K emp`, `\i. if i = 0 then [] else [put_char_event c]`, `K ($= cv)`,
     `K State`, `update`]
  \\ SIMP_TAC std_ss [LFLATTEN_LGENLIST_REPEAT,o_DEF,K_DEF,Once LGENLIST_NONE_UNFOLD,
                      LFLATTEN_THM, CONJUNCT1 llistTheory.fromList_def]
  \\ fs [GSYM SIO_def, REPLICATE_LIST_def]
  \\ xsimpl
  \\ xlet `POSTv v. &UNIT_TYPE () v *
                    SIO [put_char_event c]`
  THEN1 (
    xapp
    \\ MAP_EVERY qexists_tac [`emp`, `[]`, `c`]
    \\ xsimpl)
  \\ xvar \\ xsimpl
QED

val sio_oracle = Define `
  (sio_oracle:unit oracle) port st conf bytes =
  if port = "put_char" then
    Oracle_return st bytes
  else Oracle_final FFI_failed
`

val encode_oracle_state_def = Define `
  encode_oracle_state(st:unit) =
      State`

val decode_oracle_state_def = Define `
  decode_oracle_state(st:ffi) = ()`

Theorem decode_encode_oracle_state_11:
  !ffi_st. decode_oracle_state(encode_oracle_state ffi_st) = ffi_st
Proof
  rw[encode_oracle_state_def,decode_oracle_state_def]
QED

val sio_proj1_def = Define `
  sio_proj1 = (λffi.
    FEMPTY |++ (mk_proj1 (encode_oracle_state,decode_oracle_state,
                          [("put_char", sio_oracle "put_char")]) ffi))`;

val sio_proj2 = Define `sio_proj2 =
  [(["put_char"],update)]`

Theorem limited_parts_proj:
  limited_parts ["put_char"] (sio_proj1,sio_proj2)
Proof
  rw[limited_parts_def,sio_proj2]
QED

val sio_ffi_state_def = Define `sio_ffi_state =
  <|oracle:=sio_oracle; ffi_state := (); io_events := []|>`;

Theorem parts_ok_filter:
  parts_ok sio_ffi_state (sio_proj1,sio_proj2)
Proof
  rw[cfStoreTheory.parts_ok_def,sio_proj1_def,sio_proj2,sio_ffi_state_def,
     cfStoreTheory.ffi_has_index_in_def,mk_proj1_def,FLOOKUP_UPDATE,
     FUPDATE_LIST_THM,FAPPLY_FUPDATE_THM,decode_encode_oracle_state_11,
     sio_oracle,update_def]
QED

Theorem semantics_prog_thm:
 semantics_prog ((^(get_state st)) with ffi:= sio_ffi_state) ^(get_env st)
  (^maincall)
  (Diverge(LREPEAT [put_char_event #"a"]))
Proof
  rpt strip_tac >>
  `nsLookup ^(get_env st).v (Short "printLoop") = SOME printLoop_v`
    by(unabbrev_all_tac >> EVAL_TAC) >>
  assume_tac limited_parts_proj >>
  FULL_SIMP_TAC bool_ss [GSYM names_def] >>
  drule printLoop_spec >>
  disch_then(qspec_then `#"a"` mp_tac) >>
  disch_then(qspec_then `Litv(Char #"a")` mp_tac) >>
  simp[app_def,app_basic_def] >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev)) >>
  qmatch_goalsub_abbrev_tac `semantics_prog st` >>
  disch_then(qspec_then `st` mp_tac) >>
  unabbrev_all_tac >>
  simp[cfStoreTheory.st2heap_def,cfStoreTheory.store2heap_append,cfStoreTheory.ffi2heap_def,
       miniBasisProg_st_def,parts_ok_filter] >>
  qmatch_goalsub_abbrev_tac `FFI_split INSERT FFIset` >>
  `FFIset = {FFI_part (encode_oracle_state ()) update
                      ["put_char"] []}`
    by(unabbrev_all_tac >> rw[FUN_EQ_THM,EQ_IMP_THM] >-
        (pairarg_tac >> fs[sio_proj2] >> rveq >>
         fs[] >>
         fs[sio_proj1_def,mk_proj1_def] >>
         fs[FLOOKUP_UPDATE,FUPDATE_LIST_THM,sio_ffi_state_def]) >>
       Q.REFINE_EXISTS_TAC `(s,u,ns,ts)` >>
       rw[sio_proj2,sio_ffi_state_def,sio_proj1_def,mk_proj1_def,
          FLOOKUP_UPDATE,FUPDATE_LIST_THM]) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  qmatch_goalsub_abbrev_tac `junk ∪ {_;FFIpart}` >>
  disch_then(qspecl_then [`FFI_split INSERT junk`,
                          `{FFIpart}`]
                         mp_tac) >>
  impl_tac >-
    (rw[SPLIT_def] >> unabbrev_all_tac >> simp[] >-
       (rw[FUN_EQ_THM,EQ_IMP_THM] >> rw[]) >-
       (simp[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux,
             cfStoreTheory.store2heap_def])
    ) >>
  impl_tac >- (simp[SIO_def,Abbr `FFIpart`,one_def,encode_oracle_state_def,names_def]) >>
  strip_tac >>
  Cases_on `r` >> fs[cond_def] >> rveq >>
  fs[evaluate_to_heap_def,semanticsTheory.semantics_prog_def] >>
  rpt strip_tac >-
    (simp[semanticsTheory.evaluate_prog_with_clock_def,
          terminationTheory.evaluate_decs_def,
          astTheory.pat_bindings_def] >>
     simp[terminationTheory.evaluate_def] >>
     simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
     rw[evaluateTheory.dec_clock_def] >>
     fs[evaluate_ck_def] >>
     first_x_assum(qspec_then `k - 1` strip_assume_tac) >>
     fs[]) >>
  fs[] >>
  match_mp_tac(GEN_ALL lprefix_lub_subset) >>
  goal_assum drule >> simp[] >> conj_tac >-
    (rw[IMAGE_DEF,SUBSET_DEF] >>
     qexists_tac `SUC ck` >>
     simp[semanticsTheory.evaluate_prog_with_clock_def,
          terminationTheory.evaluate_decs_def,
          astTheory.pat_bindings_def
         ] >>
     simp[terminationTheory.evaluate_def] >>
     simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
     rw[evaluateTheory.dec_clock_def] >>
     fs[evaluate_ck_def] >>
     rpt(PURE_TOP_CASE_TAC >> rveq >> fs[])) >>
  rw[PULL_EXISTS] >>
  simp[LPREFIX_fromList_fromList] >>
  simp[semanticsTheory.evaluate_prog_with_clock_def,
       terminationTheory.evaluate_decs_def,
       astTheory.pat_bindings_def
      ] >>
  simp[terminationTheory.evaluate_def] >>
  simp[semanticPrimitivesTheory.do_con_check_def,semanticPrimitivesTheory.build_conv_def] >>
  rw[evaluateTheory.dec_clock_def] >>
  fs[evaluate_ck_def] >>
  first_x_assum(qspec_then `k - 1` strip_assume_tac) >>
  fs[] >-
    (qexists_tac `ARB` >>
     qmatch_goalsub_abbrev_tac `evaluate st` >>
     Q.ISPEC_THEN `st` mp_tac
       (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono
        |> SIMP_RULE std_ss [evaluatePropsTheory.io_events_mono_def]) >>
     simp[Abbr `st`]) >>
  qexists_tac `k - 1` >>
  every_case_tac >> fs[]
QED

Theorem cyes_prog_def = mk_abbrev "cyes_prog" cyes;

(* TODO: this proof is slow and also an abomination. We should really make proper
   whole_prog_thm automation for Diverge.
 *)
Theorem cyes_semantics_prog_Diverge:
  let (s,env) = THE (prim_sem_env sio_ffi_state)
  in semantics_prog s env cyes_prog (Diverge (LREPEAT [put_char_event #"a"]))
Proof
  rw[] >>
  mp_tac semantics_prog_thm >>
  disch_then (mp_tac o CONV_RULE((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) >>
  disch_then (mp_tac o CONV_RULE((RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) >>
  CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV EVAL))) >>
  fs[cyes_prog_def,ml_progTheory.init_env_def] >>
  (* TODO: can we avoid referring explicitly to these generated env defs in a cleaner way? *)
  FULL_SIMP_TAC std_ss
    (case st of ML_code (sts,envs,vs,_) => sts @ envs @ vs) >>
  qabbrev_tac `maincall = ^maincall` >>
  fs[semanticsTheory.semantics_prog_def,semanticsTheory.evaluate_prog_with_clock_def,
     terminationTheory.evaluate_def,terminationTheory.evaluate_decs_def,
     semanticPrimitivesTheory.check_dup_ctors_def,
     astTheory.pat_bindings_def,
     semanticPrimitivesTheory.combine_dec_result_def,
     terminationTheory.pmatch_def,
     semanticPrimitivesTheory.extend_dec_env_def,
     semanticPrimitivesTheory.build_tdefs_def,
     semanticPrimitivesTheory.build_constrs_def,
     evaluatePropsTheory.evaluate_decs_cons,
     ml_progTheory.write_def,
     ml_progTheory.write_mod_def,
     ml_progTheory.write_cons_def
    ] >>
  qmatch_goalsub_abbrev_tac `aa1  /\ aa2 ==> ab1 /\ ab2` >>
  qsuff_tac `(aa1 = ab1) /\ (aa2 = ab2)` >-
    (rpt(pop_assum kall_tac) >> metis_tac[]) >>
  conj_tac >>
  unabbrev_all_tac >>
  CHANGED_TAC(rpt(AP_THM_TAC ORELSE AP_TERM_TAC)) >>
  rw[FUN_EQ_THM,ELIM_UNCURRY] >>
  qmatch_goalsub_abbrev_tac `evaluate_decs a1 a2` >>
  qpat_abbrev_tac `aa1 = evaluate_decs a1 a2` >>
  qmatch_goalsub_abbrev_tac `evaluate_decs a3 a4` >>
  `a1 = a3`
    by(unabbrev_all_tac >> simp[semanticPrimitivesTheory.state_component_equality]) >>
  `a2 = a4`
    by(unabbrev_all_tac >> EVAL_TAC) >>
  simp[Abbr `aa1`] >>
  Cases_on `evaluate_decs a3 a4 ^maincall` >> rw[] >>
  rw[CaseEq"semanticPrimitives$result",CaseEq"prod"]
QED

val _ = intermediate_prog_prefix := "cyes_";
Theorem cyes_thm = compile_x64 1000 1000 "cyes" (REFL cyes);
val _ = intermediate_prog_prefix := "";

val cyes_data_code_def       = definition"cyes_data_prog_def"
val cyes_to_data_thm         = theorem"cyes_to_data_thm"
val cyes_config_def          = definition"cyes_config_def"
val cyes_x64_conf            = (rand o rator o lhs o concl) cyes_thm
Theorem cyes_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) cyes_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) cyes_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem cyes_data_code_def = cyes_data_code_def;

val _ = export_theory();
