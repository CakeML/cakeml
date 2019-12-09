(*
  A data-cost example of a non-terminating function (cyes)
  that prints a character indefinitely

*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open miniBasisProgTheory;

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

val cyes2 =
  let val prog = process_topdecs `
      fun put_char c = let
        val a = Word8Array.array 0 (Word8.fromInt 0)
        val s = String.implode [c]
        val _ = #(put_char) s a
        in () end;

      fun printLoop c = (printLoop c; put_char c);

      val _ = printLoop #"a"`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

val cyes2_thm = compile_to_data (compilation_compset())
                               x64_backend_config_def
                               (REFL cyes2)
                               "cyes2_data_prog"

val cyes2_data_code_def       = definition"cyes2_data_prog_def"


val _ = intermediate_prog_prefix := "cyes_"
val cyes_thm = compile_x64 1000 1000 "cyes" (REFL cyes)
val _ = intermediate_prog_prefix := ""

val cyes_data_code_def       = definition"cyes_data_prog_def"
val cyes_to_data_thm         = theorem"cyes_to_data_thm"
val cyes_config_def          = definition"cyes_config_def"
val cyes_x64_conf            = (rand o rator o lhs o concl) cyes_thm
val cyes_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) cyes_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) cyes_thm)
  |> SIMP_RULE (srw_ss()) []


val f_diff = diff_codes cyes_data_code_def cyes2_data_code_def

val (f11,f12) = hd f_diff
val (f21,f22) = (hd o tl) f_diff

Theorem data_safe_cyes_code:
  ∀s ts smax sstack lsize.
   s.safe_for_space ∧
   wf s.refs ∧
   (s.stack_frame_sizes = cyes_config.word_conf.stack_frame_size) ∧
   (s.stack_max = SOME smax) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (s.locals_size = SOME lsize) ∧
   (sstack + 103 < s.limits.stack_limit) ∧
   (sstack + lsize + 100 < s.limits.stack_limit) ∧
   (smax < s.limits.stack_limit) ∧
   s.limits.arch_64_bit ∧
   closed_ptrs (stack_to_vs s) s.refs ∧
   size_of_heap s + 6 ≤ s.limits.heap_limit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (lookup 0 s.locals = SOME (Number 97)) ∧
   (s.code = fromAList cyes_data_prog)
   ⇒ data_safe (evaluate ((SND o SND) ^f21, s))
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList cyes_data_prog`
                         cyes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `cyes_config.word_conf.stack_frame_size`
                         cyes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
  in
  measureInduct_on `^s.clock`
  \\ fs [ to_shallow_thm
        , to_shallow_def
        , initial_state_def ]
  \\ rw []
  \\ strip_call
  \\ `small_num s.limits.arch_64_bit 97` by (rw[] >> EVAL_TAC)
  \\ `1 < 2 ** s.limits.length_limit`
     by (irule LESS_TRANS \\ qexists_tac `s.limits.length_limit` \\ fs [])
  (* Make safe_for_space sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe) _`
  \\ `safe` by (fs [Abbr `safe`, size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 6))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Useful simplification through the proof *)
  \\ `toListA [] (inter s.locals (LS ())) = [Number 97]`
     by (Cases_on `s.locals` \\ fs [lookup_def,inter_def,toListA_def])
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ simp []
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  (* strip_assign *)
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ ntac 3 (strip_assign \\ fs [])
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , flush_state_def
          , size_of_stack_frame_def]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_stack_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [MAX_DEF,GREATER_DEF,libTheory.the_def]
     \\ `n ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ irule LESS_EQ_TRANS \\ qexists_tac `n' + 3` \\ rw [])
  \\ simp []
  \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 4 strip_assign
  (* open_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ Cases_on `ts`
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def]
     \\ `n1''''' ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ Cases_on `lookup (SUC n) seen1'''''` \\ fs [] \\ rveq \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  (* strip_assign *)
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call2 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , flush_state_def
          , size_of_stack_frame_def]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ Cases_on `ts` \\ fs [size_of_def,lookup_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def]
     \\ rveq
     \\ `n1''' ≤ n'` by
        (irule size_of_le_APPEND
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ Cases_on `lookup (SUC n) seen1'''` \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 12))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 3 strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 97 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 97` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ ntac 4 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ `lookup p1 s.refs = NONE` by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  (* Prove we are safe for space up to this point *)
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ rw[small_num_def]
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ rw[small_num_def]
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ `closed_ptrs (b ++ c) s.refs` by fs [closed_ptrs_APPEND]
     (* \\ map_every  Q.UNABBREV_TAC [`a`,`b`,`c`] *)
     \\ drule size_of_insert \\ disch_then drule
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p1`] mp_tac)
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ Cases_on `size_of s.limits (b ++ c) s.refs LN` \\ Cases_on `r`
     \\ disch_then drule \\ fs []
     \\ disch_then (qspec_then `x` assume_tac)
     \\ fs [] \\ rveq \\ rfs []
     \\ Q.UNABBREV_TAC `x`
     \\ fs [] \\ rveq \\ fs [small_num_def]
     \\ `n1''' ≤ n'` by
        (irule size_of_le_APPEND
        \\ pop_assum kall_tac
        \\ asm_exists_tac \\ fs []
        \\ asm_exists_tac \\ fs [])
     \\ fs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 12))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call2`
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ strip_assign
  \\ fs [lookup_insert]
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ fs []
  \\ `lookup p2 (insert p1 (ByteArray T [97w]) s.refs) = NONE` by
     (fs [lookup_insert]
     \\ rw [Abbr `p2`, least_from_def]
     >- (Cases_on `p1 = 0` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `wf (insert p1 (ByteArray T [97w]) s.refs)` by fs [wf_insert]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ qmatch_asmsub_abbrev_tac `insert p2 y (insert p1 x s.refs)`
     \\ rveq \\ fs []
     \\ drule size_of_insert
     \\ disch_then (qspecl_then
          [`s.limits`,`b ++ c`,`LN`,`p2`,`y`,`n1''`,`refs1''`,`seen1''`] mp_tac)
     \\ impl_tac
     >- (fs [closed_ptrs_APPEND] \\ rw []
        \\ ho_match_mp_tac closed_ptrs_insert \\ fs []
        \\ Q.UNABBREV_TAC `x` \\ ho_match_mp_tac closed_ptrs_refs_insert
        \\ fs [closed_ptrs_def])
     \\ rw [] \\ fs []
     \\ (qpat_x_assum `wf (insert _ _ _)` kall_tac
        \\ drule size_of_insert
        \\ Cases_on `size_of s.limits (b ++ c) s.refs LN` \\ Cases_on `r`
        \\ qmatch_asmsub_rename_tac `size_of s.limits (b ++ c) s.refs LN = (n8,refs8,seen8)`
        \\ disch_then (qspecl_then [`s.limits`,`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
        \\ impl_tac
        >- fs [closed_ptrs_APPEND]
        \\ rw [] \\ Cases_on `lookup ts seen1'` \\ fs [] \\ rveq
        \\ map_every Q.UNABBREV_TAC [`x`,`y`] \\ fs [] \\ rveq
        \\ fs [lookup_delete,lookup_insert] \\ rfs [] \\ rveq \\ fs []
        \\ rw[arch_size_def]
        \\ `n1' ≤ n''` suffices_by fs []
        \\ ho_match_mp_tac size_of_le_APPEND
        \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
        \\ asm_exists_tac \\ fs []))
  \\ simp[] \\ ntac 2 (pop_assum kall_tac) \\ fs []
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [97w] []` \\ fs [])
  >- (fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ rw[arch_size_def]
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ rveq \\ fs []
     \\ qpat_x_assum `wf (insert _ _ _)` kall_tac
     \\ drule size_of_insert
     \\ Cases_on `size_of s.limits (b ++ c) s.refs LN` \\ Cases_on `r`
     \\ qmatch_asmsub_rename_tac `size_of s.limits (b ++ c) s.refs LN = (n8,refs8,seen8)`
     \\ disch_then (qspecl_then
          [`s.limits`,`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
     \\ fs [closed_ptrs_APPEND]
     \\ rw [] \\ fs []
     \\ Q.UNABBREV_TAC `x` \\ fs [] \\ rveq
     \\ `n1 ≤ n'` suffices_by fs []
     \\ ho_match_mp_tac size_of_le_APPEND
     \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ Q.UNABBREV_TAC `rest_call`
  \\ rveq \\ fs [flush_state_def]
  (* strip tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter,frame_lookup]
  \\ IF_CASES_TAC
  >- fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ ho_match_mp_tac data_safe_res
  \\ reverse conj_tac >- (rw [] \\ pairarg_tac \\ rw [])
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 12))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac `data_safe (_ s0)`
  \\ first_x_assum (qspec_then `s0` assume_tac)
  \\ `s0.clock < s.clock` by (UNABBREV_ALL_TAC \\ rw [])
  \\ first_x_assum (drule_then irule) \\ Q.UNABBREV_TAC `s0` \\  fs []
  \\ simp [ size_of_heap_def,size_of_Number_head,stack_to_vs_def
          , lookup_def,toList_def,toListA_def
          , wf_insert, wf_delete ]
  \\ rw []
  >- fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
  >- fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
  >- (pairarg_tac \\ fs []
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ qmatch_asmsub_abbrev_tac `closed_ptrs (a ++ b ++ c)`
     \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
     \\ qmatch_asmsub_abbrev_tac `insert p2 y (insert p1 x s.refs)`
     \\ rveq \\ fs []
     \\ drule size_of_insert
     \\ disch_then (qspecl_then
          [`s.limits`,`b ++ c`,`LN`,`p2`,`y`,`n1''`,`refs1''`,`seen1''`] mp_tac)
     \\ impl_tac
     >- (fs [closed_ptrs_APPEND] \\ rw []
        \\ ho_match_mp_tac closed_ptrs_insert \\ fs []
        \\ Q.UNABBREV_TAC `x` \\ ho_match_mp_tac closed_ptrs_refs_insert
        \\ fs [closed_ptrs_def])
     \\ rw [] \\ fs [size_of_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [size_of_Number_head]
     \\ qpat_x_assum `wf (insert _ _ _)` kall_tac
     \\ drule size_of_insert
     \\ qmatch_asmsub_rename_tac `size_of s.limits (b ++ c) s.refs LN = (n8,refs8,seen8)`
     \\ disch_then (qspecl_then [`s.limits`,`b ++ c`,`LN`,`p1`,`x`,`n8`,`refs8`,`seen8`] mp_tac)
     \\ impl_tac >- fs [closed_ptrs_APPEND]
     \\ rveq \\ rw [] \\ Cases_on `lookup ts _` \\ fs [] \\ rveq
     \\ map_every Q.UNABBREV_TAC [`x`,`y`] \\ fs [] \\ rveq
     \\ fs [lookup_delete,lookup_insert] \\ rfs [] \\ rveq \\ fs []
     \\ `n' ≤ n''` suffices_by fs []
     \\ ho_match_mp_tac size_of_le_APPEND
     \\ map_every qexists_tac [`a`,`b ++ c`] \\ fs []
     \\ asm_exists_tac \\ fs [])
   \\ ho_match_mp_tac closed_ptrs_insert
   \\ fs [] \\ reverse conj_tac
   >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs []
      \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs []
      \\ fs [closed_ptrs_def])
   \\ ho_match_mp_tac closed_ptrs_insert
   \\ fs [] \\ reverse conj_tac
   >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [closed_ptrs_def])
   \\ ONCE_REWRITE_TAC [closed_ptrs_cons]
   \\ conj_tac >- fs [closed_ptrs_APPEND,stack_to_vs_def]
   \\ fs [closed_ptrs_def,closed_ptrs_list_def]
  end
QED

Theorem data_safe_cyes_code_shallow[local] =
  data_safe_cyes_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_cyes_code_abort:
 ∀s ts.
   (lookup 0 s.locals = SOME (Number 97)) ∧
   2 ≤ s.limits.length_limit ∧
   (s.stack_frame_sizes = cyes_config.word_conf.stack_frame_size) ∧
   s.limits.arch_64_bit ∧
   (s.tstamps = SOME ts) ∧
   (s.code = fromAList cyes_data_prog)
   ⇒ ∃s' e. evaluate ((SND o SND) ^f21, s) =
       (SOME (Rerr (Rabort e)),s')
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList cyes_data_prog`
                         cyes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `cyes_config.word_conf.stack_frame_size`
                         cyes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
  measureInduct_on `^s.clock`
  \\ rw [to_shallow_def,to_shallow_thm]
  \\ strip_call
  \\ `(inter s.locals (LS ())) = LS (Number 97)`
     by (Cases_on `s.locals` \\ fs [lookup_def,inter_def])
  \\ strip_makespace
  \\ ntac 6 strip_assign
  \\ strip_call
  \\ strip_assign
  \\ make_if
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  (* strip_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ IF_CASES_TAC
  >- simp []
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call_1`
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  (* strip_call *)
  \\ qmatch_goalsub_abbrev_tac (`bind _ rest_call_1 _`)
  \\ ONCE_REWRITE_TAC [bind_def]
  (* open_call *)
  \\ simp [ call_def     , find_code_def  , push_env_def
          , get_vars_def , call_env_def   , dec_clock_def
          , cut_env_def  , domain_def     , data_safe_def
          , EMPTY_SUBSET , get_var_def    , size_of_stack_def
          , lookup_def   , domain_IS_SOME , frame_lookup
          , code_lookup  , lookup_def     , domain_IS_SOME
          , lookup_insert, flush_state_def
          , size_of_stack_frame_def]
  \\ IF_CASES_TAC >- simp []
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 97 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 97` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  (* strip_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup,lookup_inter]
  \\ IF_CASES_TAC
  >- simp []
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp[LET_THM]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call_1`
  \\ ntac 3 strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ `lookup p1 s.refs = NONE` by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ IF_CASES_TAC \\ fs []
     \\ IF_CASES_TAC \\ fs []
     >- (numLib.LEAST_ELIM_TAC \\ metis_tac [])
     \\ numLib.LEAST_ELIM_TAC
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw [] >- metis_tac []
        \\ CCONTR_TAC \\ fs [lookup_insert])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
        \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
        \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
        \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
     \\ CCONTR_TAC \\ fs [lookup_insert])
  \\ strip_assign \\ fs [lookup_insert]
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [97w] []`) >- simp []
  \\ strip_assign \\ strip_assign
  \\ rw [return_def,lookup_def]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ Q.UNABBREV_TAC `rest_call`
  (*  make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter
          ,frame_lookup]
  \\ IF_CASES_TAC
  >- simp []
  \\ eval_goalsub_tac ``dataSem$call_env _ _``
  \\ qmatch_goalsub_abbrev_tac `evaluate (p0,s0)`
  \\ `s0.clock < s.clock` by fs [Abbr `s0`,dec_clock_def]
  \\ first_x_assum (drule_then (qspec_then `ts + 1` mp_tac))
  \\ impl_tac >- (fs [Abbr `s0`] \\ EVAL_TAC \\ fs [])
  \\ rw [] \\ fs []
  end
QED

Theorem data_safe_cyes_code_abort_shallow[local] =
  data_safe_cyes_code_abort |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_cyes:
 ∀ffi.
  backend_config_ok ^cyes_x64_conf
  ⇒ is_safe_for_space ffi
      ^cyes_x64_conf
      ^cyes
      (1000,1000)
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList cyes_data_prog`
                         cyes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `cyes_config.word_conf.stack_frame_size`
                         cyes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ conj_tac >- EVAL_TAC
 \\ assume_tac cyes_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac cyes_to_data_updated_thm
 \\ fs [data_lang_safe_for_space_def]
 \\ strip_tac
 \\ qmatch_goalsub_abbrev_tac `_ v0`
 \\ `data_safe v0` suffices_by
    (Cases_on `v0` \\ fs [data_safe_def])
 \\ UNABBREV_ALL_TAC
 \\ qmatch_goalsub_abbrev_tac `is_64_bits c0`
 \\ `is_64_bits c0` by (UNABBREV_ALL_TAC \\ EVAL_TAC)
 \\ fs []
 \\ rpt (pop_assum kall_tac)
 (* start data_safe proof *)
 \\ REWRITE_TAC [ to_shallow_thm
                , to_shallow_def
                , initial_state_def
                , bvl_to_bviTheory.InitGlobals_location_eq]
  (* Make first call *)
 \\ rpt strip_tac
 \\ make_tailcall
 (* Bootcode *)
 \\ ntac 7 strip_assign
 \\ ho_match_mp_tac data_safe_bind_return
 (* Yet another call *)
 \\ make_call
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ UNABBREV_ALL_TAC
 (* Continues after call *)
 \\ strip_makespace
 \\ ntac 49 strip_assign
 \\ make_tailcall
 \\ ntac 5
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
  \\ strip_call
  \\ ntac 9 strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ntac 6
     (open_tailcall
     \\ ntac 4 strip_assign
     \\ make_if
     \\ ntac 2 strip_assign)
  \\ open_tailcall
  \\ ntac 4 strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call`
  \\ ntac 3 strip_assign
  \\ make_tailcall
  \\ ntac 5
     (strip_makespace
     \\ ntac 7 strip_assign
     \\ make_tailcall)
  \\ strip_assign
  \\ ho_match_mp_tac data_safe_bind_some
  \\ open_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ `∃s' e'. f s = (SOME (Rerr (Rabort e')),s')`
     by (UNABBREV_ALL_TAC
        \\ ho_match_mp_tac data_safe_cyes_code_abort_shallow
        \\ fs [] \\ EVAL_TAC)
  \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac data_safe_cyes_code_shallow
  \\ rw [lookup_def,lookup_fromList,code_lookup]
  \\ EVAL_TAC
  \\ qexists_tac `10` \\ fs []
  end
QED

Theorem cyes_x64_conf_def = mk_abbrev "cyes_x64_conf" cyes_x64_conf;
Theorem cyes_s_def = mk_abbrev"cyes_s"
                      ((rand o rand o rhs o concl) primSemEnvTheory.prim_sem_env_eq)

Definition cyes_env_def:
  cyes_env ffi = FST (THE (prim_sem_env sio_ffi_state))
End

Theorem prim_sem_env_cyes:
  THE (prim_sem_env sio_ffi_state) = (cyes_env ffi,cyes_s)
Proof
EVAL_TAC \\ rw [cyes_s_def]
QED

(* TODO *)
Theorem backend_config_ok_cyes:
  backend_config_ok cyes_x64_conf
Proof
 cheat
QED

Theorem cyes_semantics_prog_not_Fail:
  let (s,env) = THE (prim_sem_env sio_ffi_state)
  in ¬semantics_prog s env cyes_prog Fail
Proof
  assume_tac cyes_semantics_prog_Diverge
  \\ fs [] \\ pairarg_tac \\  fs []
  \\ CCONTR_TAC \\ fs []
  \\ drule semanticsPropsTheory.semantics_prog_deterministic
  \\ pop_assum kall_tac
  \\ disch_then drule
  \\ fs []
QED

Theorem IMP_IMP_TRANS_THM:
  ∀W P R Q. (W ⇒ Q) ⇒ (P ⇒ R ⇒ W) ⇒ P ⇒ R ⇒ Q
Proof
 rw []
QED

Theorem machine_sem_eq_semantics_prog:
semantics_prog s env prog (Diverge io_trace) ⇒
  (machine_sem mc (ffi:'ffi ffi_state) ms = semantics_prog s env prog) ⇒
     machine_sem mc ffi ms (Diverge io_trace)
Proof
  rw []
QED

Theorem machine_sem_eq_semantics_prog_ex:
(∃io_trace. semantics_prog s env prog (Diverge io_trace)) ⇒
  (machine_sem mc (ffi:'ffi ffi_state) ms = semantics_prog s env prog) ⇒
     (∃io_trace. machine_sem mc ffi ms (Diverge io_trace))
Proof
  rw []
QED

val cyes_safe_thm =
    let
      val ffi = ``sio_ffi_state``
      val is_safe = data_safe_cyes
                    |> REWRITE_RULE [GSYM cyes_prog_def
                                    ,GSYM cyes_x64_conf_def]
                    |> ISPEC ffi
      val not_fail = cyes_semantics_prog_not_Fail
                     |> SIMP_RULE std_ss [LET_DEF,prim_sem_env_cyes
                                         ,ELIM_UNCURRY]
      val is_corr = MATCH_MP compile_correct_is_safe_for_space cyes_thm
                    |> REWRITE_RULE [GSYM cyes_prog_def
                                    ,GSYM cyes_x64_conf_def]
                    |> Q.INST [`stack_limit` |-> `1000`
                              ,`heap_limit` |-> `1000`]
                    |> INST_TYPE [``:'ffi`` |-> ``:unit``]
                    |> Q.INST [`ffi` |-> `sio_ffi_state`]
                    |> SIMP_RULE std_ss [prim_sem_env_cyes,LET_DEF,not_fail,ELIM_UNCURRY]
      val machine_eq = MATCH_MP (machine_sem_eq_semantics_prog |> INST_TYPE [``:'ffi`` |-> ``:unit``])
                                (cyes_semantics_prog_Diverge
                                   |> SIMP_RULE std_ss [LET_DEF,prim_sem_env_cyes,ELIM_UNCURRY])
      val safe_thm_aux = MATCH_MP (IMP_TRANS is_safe is_corr) backend_config_ok_cyes
    in MATCH_MP (MATCH_MP IMP_IMP_TRANS_THM machine_eq)
                (safe_thm_aux |> SIMP_RULE std_ss [prim_sem_env_cyes,LET_DEF,ELIM_UNCURRY])
    end

Theorem cyes_safe = cyes_safe_thm

val _ = export_theory();
