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

val _ = new_theory "yesProg"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``

val _ = monadsyntax.temp_add_monadsyntax()

(* ************************** *)
(* * yes (with mini-basis) * *)
(* ************************** *)

val _ = translation_extends "miniBasisProg";

val whole_prog = whole_prog ()

val _ = (append_prog o process_topdecs) `
  fun put_line l = let
      val s = String.strcat l "\n"
      val a = Word8Array.array 0 (Word8.fromInt 0)
      val _ = #(put_char) s a
    in () end;
  `

val _ = (append_prog o process_topdecs) `
  fun printLoop l = (put_line l; printLoop l);
  `

val maincall = process_topdecs `val _ = printLoop "y"`

local
  val prog = get_prog(get_ml_prog_state())
in
  val yes = (rhs o concl o EVAL) ``^prog ++ ^maincall``
end

Theorem yes_prog_def = mk_abbrev "yes_prog" yes;

val yes2 =
  let val prog = process_topdecs `
      fun put_line l = let
          val s = String.strcat l "\n"
          val a = Word8Array.array 0 (Word8.fromInt 0)
          val _ = #(put_char) s a
        in () end;

      fun printLoop c = (printLoop c; put_line c);

      val _ = printLoop "y"`
  in (rhs o concl o EVAL) ``^whole_prog ++ ^prog``
  end

(* A small IO model *)
open cfDivTheory;

val names_def = Define `names = ["put_char"]`;

val put_char_event_def = Define `
  put_char_event c = IO_event "put_char" [n2w (ORD c)] []`;

val put_str_event_def = Define `
  put_str_event cs = IO_event "put_char" (MAP (n2w o ORD) (explode cs)) []`;

val update_def = Define `
  (update "put_char" cs l s = SOME (FFIreturn l s))`

val State_def = Define `
  State = Stream [||]`

val SIO_def = Define `
  SIO events =
    one (FFI_part (State) update names events)`

val st = ml_translatorLib.get_ml_prog_state();

Theorem put_line_spec:
  !s sv events.
  limited_parts names p /\ STRING_TYPE s sv ==>
  app (p:'ffi ffi_proj) ^(fetch_v "put_line" st) [sv]
    (SIO events)
    (POSTv v. &UNIT_TYPE () v *
              SIO (SNOC (put_str_event (s ^ strlit "\n")) events))
Proof
  xcf "put_line" st
  \\ xlet `POSTv v. &STRING_TYPE (strcat s (strlit "\n")) v * SIO events`
  THEN1 (xapp \\ xsimpl \\ goal_assum drule \\ rw[])
  \\ xlet `POSTv v. &WORD8 0w v * SIO events` THEN1 (xapp \\ xsimpl)
  \\ xlet `POSTv v. W8ARRAY v [] * SIO events` THEN1 (xapp \\ xsimpl \\ goal_assum drule)
  \\ rename1 `W8ARRAY av`
  \\ xlet
    `POSTv v. &UNIT_TYPE () v * W8ARRAY av [] *
              SIO (SNOC (put_str_event (s ^ strlit "\n")) events)`
  THEN1 (
    xffi \\ xsimpl \\ fs [SIO_def]
    \\ MAP_EVERY qexists_tac
      [`MAP (n2w o ORD) (explode(s ^ strlit "\n"))`, `emp`, `State`, `update`, `names`, `events`]
    \\ fs [update_def, put_str_event_def, names_def, SNOC_APPEND,
           implode_def, STRING_TYPE_def, State_def,strcat_thm,concat_thm,
           MAP_MAP_o,CHR_w2n_n2w_ORD]
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
  !s sv.
    limited_parts names p /\ STRING_TYPE s sv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "printLoop" st) [sv]
      (SIO []) (POSTd io. io = LREPEAT [put_str_event(s ^ strlit "\n")])
Proof
  xcf_div_rule IMP_app_POSTd_one_FFI_part_FLATTEN "printLoop" st
  \\ MAP_EVERY qexists_tac
    [`K emp`, `\i. if i = 0 then [] else [put_str_event(s ^ strlit "\n")]`, `K ($= sv)`,
     `K State`, `update`]
  \\ SIMP_TAC std_ss [LFLATTEN_LGENLIST_REPEAT,o_DEF,K_DEF,Once LGENLIST_NONE_UNFOLD,
                      LFLATTEN_THM, CONJUNCT1 llistTheory.fromList_def]
  \\ fs [GSYM SIO_def, REPLICATE_LIST_def]
  \\ xsimpl
  \\ xlet `POSTv v. &UNIT_TYPE () v *
                    SIO [put_str_event(s ^ strlit "\n")]`
  THEN1 (
    xapp
    \\ MAP_EVERY qexists_tac [`emp`, `s`, `[]`]
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
  (Diverge(LREPEAT [put_str_event(strlit "y\n")]))
Proof
  rpt strip_tac >>
  `nsLookup ^(get_env st).v (Short "printLoop") = SOME printLoop_v`
    by(unabbrev_all_tac >> EVAL_TAC) >>
  assume_tac limited_parts_proj >>
  FULL_SIMP_TAC bool_ss [GSYM names_def] >>
  drule printLoop_spec >>
  disch_then(qspec_then `strlit "y"` mp_tac) >>
  disch_then(qspec_then `Litv(StrLit "y")` mp_tac) >>
  simp[app_def,app_basic_def] >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev)) >>
  qmatch_goalsub_abbrev_tac `semantics_prog st` >>
  disch_then(qspec_then `st` mp_tac) >>
  unabbrev_all_tac >>
  simp[cfStoreTheory.st2heap_def,cfStoreTheory.store2heap_append,cfStoreTheory.ffi2heap_def,
       miniBasisProg_st_def,parts_ok_filter,strcat_thm,implode_def] >>
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

(* TODO: this proof is slow and also an abomination. We should really make proper
   whole_prog_thm automation for Diverge.
 *)
Theorem yes_semantics_prog_Diverge:
  let (s,env) = THE (prim_sem_env sio_ffi_state)
  in semantics_prog s env yes_prog (Diverge (LREPEAT [put_str_event(strlit "y\n")]))
Proof
  rw[] >>
  mp_tac semantics_prog_thm >>
  disch_then (mp_tac o CONV_RULE((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) >>
  disch_then (mp_tac o CONV_RULE((RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) >>
  CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV EVAL))) >>
  fs[yes_prog_def,ml_progTheory.init_env_def] >>
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

val yes2_thm = compile_to_data (compilation_compset())
                               x64_backend_config_def
                               (REFL yes2)
                               "yes2_data_prog"

val yes2_data_code_def       = definition"yes2_data_prog_def"

val _ = intermediate_prog_prefix := "yes_"
val yes_thm = compile_x64 1000 1000 "yes" (REFL yes)
val _ = intermediate_prog_prefix := ""

val yes_data_code_def       = definition"yes_data_prog_def"
val yes_to_data_thm         = theorem"yes_to_data_thm"
val yes_config_def          = definition"yes_config_def"
val yes_x64_conf            = (rand o rator o lhs o concl) yes_thm
val yes_x64_conf_def        = mk_abbrev"yes_x64_conf" yes_x64_conf
val yes_to_data_updated_thm =
  MATCH_MP (GEN_ALL  to_data_change_config) yes_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) yes_thm)
  |> SIMP_RULE (srw_ss()) []

val f_diff = diff_codes yes_data_code_def yes2_data_code_def

(* val (f11,f12) = hd f_diff *)
val (f21,f22) = hd f_diff

Theorem data_safe_yes_code:
  ∀s ts smax sstack lsize.
   s.safe_for_space ∧
   wf s.refs ∧
   (s.stack_frame_sizes = yes_config.word_conf.stack_frame_size) ∧
   (s.stack_max = SOME smax) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (s.locals_size = SOME lsize) ∧
   (sstack + 17 < s.limits.stack_limit) ∧
   (sstack + lsize + 14 < s.limits.stack_limit) ∧
   (smax < s.limits.stack_limit) ∧
   s.limits.arch_64_bit ∧
   closed_ptrs (stack_to_vs s) s.refs ∧
   size_of_heap s + 11 ≤ s.limits.heap_limit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (s.locals = fromList [RefPtr 2]) ∧
   (lookup 2 s.refs = SOME (ByteArray T [121w])) ∧
   (s.code = fromAList yes_data_prog)
   ⇒ data_safe (evaluate ((SND o SND) ^f21, s))
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList yes_data_prog`
                         yes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `yes_config.word_conf.stack_frame_size`
                         yes_config_def
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
  \\ rw [] \\ fs [fromList_def]
  \\ strip_call
  \\ `1 < 2 ** s.limits.length_limit`
     by (irule LESS_TRANS \\ qexists_tac `s.limits.length_limit` \\ fs [])
  (* Make safe_for_space sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe) _`
  \\ `safe` by (fs [Abbr `safe`, size_of_stack_def,GREATER_DEF] \\ EVAL_TAC)
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 6))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* strip_assign *)
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp1) _`
  \\ `pp1 = p1`  by
     (UNABBREV_ALL_TAC \\ fs [least_from_def]
     \\ Cases_on `lookup 0 s.refs` \\ fs []
     >- (numLib.LEAST_ELIM_TAC
        \\ conj_tac >- (asm_exists_tac \\ fs [])
        \\ rw [] \\ Cases_on `n` \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (qexists_tac `ptr` \\ fs [])
     \\ rw [] \\ CCONTR_TAC
     \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [])
     \\ fs [NOT_LESS] \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  (* Make safe_for_space sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_stack_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [MAX_DEF,GREATER_DEF,libTheory.the_def,small_num_def]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ _ _ _ = (_,refs'',seen'')`
     \\ drule size_of_RefPtr_head
     \\ eval_goalsub_tac ``sptree$lookup _ _``
     \\ rw [] \\ fs [])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ simp []
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ Q.ABBREV_TAC `pred = ∃w. 10 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 10` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 6 (strip_assign \\ fs [])
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
  \\ `lookup p1 s.refs = NONE`  by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ 2` by (CCONTR_TAC  \\ fs [])
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_stack_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [MAX_DEF,GREATER_DEF,libTheory.the_def]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq
     \\ drule_then drule wf_size_of
     \\ strip_tac
     \\ drule_then (qspecl_then [`p1`,`ByteArray T [0w]`] mp_tac) delete_insert_eq
     \\ impl_tac
     >- (drule_then drule size_of_lookup_NONE \\ fs [])
     \\ drule size_of_RefPtr_head
     \\ eval_goalsub_tac ``sptree$lookup _ _``
     \\ rw [] \\ fs [])
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
  \\ ntac 6 strip_assign
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
     (* \\ Cases_on `ts` *)
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ _ s.refs LN = (_,_,seen0)`
     \\ Cases_on `IS_SOME (lookup (ts + 1) seen0)` \\ fs []
     >- (rveq \\ fs [] \\ rveq \\ fs []
        \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs []
        \\ rveq \\ rw[arch_size_def])
     \\ rveq \\ fs []
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs []
     >- (fs [] \\ rveq
        \\ Cases_on `IS_SOME (lookup ts seen')` \\ fs []
        \\ rveq \\ fs [lookup_insert] \\ rfs []
        \\ drule size_of_RefPtr_head
        \\ strip_tac \\ fs []
        \\ rveq \\ fs []
        \\ rveq \\ fs []
        \\ rw[arch_size_def])
     \\ rveq \\ fs [lookup_delete,lookup_insert] \\ rfs []
     \\ drule size_of_RefPtr_head
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_delete]
     \\ rw[arch_size_def])
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
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 11))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
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
     (* \\ Cases_on `ts` *)
     \\ fs [size_of_def,lookup_def,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ _ s.refs LN = (_,_,seen0)`
     \\ Cases_on `IS_SOME (lookup (ts + 1) seen0)` \\ fs []
     \\ rveq \\ fs []
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [lookup_delete]
     >- (rveq \\ fs [lookup_insert] \\ rfs []
        \\ drule size_of_RefPtr_head
        \\ strip_tac \\ fs [])
     \\ rveq \\ fs [lookup_delete,lookup_insert] \\ rfs []
     \\ drule size_of_RefPtr_head
     \\ strip_tac \\ fs []
     \\ rw[arch_size_def]
     )
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
     \\ fs [size_of_def,lookup_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,GREATER_DEF,libTheory.the_def
           ,size_of_stack_def,insert_shadow]
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ drule size_of_insert
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rveq \\ fs []
     \\ qmatch_asmsub_rename_tac `size_of _ _ s.refs LN = (_,_,seen0)`
     \\ Cases_on `IS_SOME (lookup (ts + 1) seen0)` \\ fs []
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [lookup_delete]
     >- (rveq \\ fs [lookup_insert] \\ rfs []
        \\ drule size_of_RefPtr_head
        \\ strip_tac \\ fs [])
     \\ rveq \\ fs [lookup_delete,lookup_insert] \\ rfs []
     \\ drule size_of_RefPtr_head
     \\ strip_tac \\ fs []
     \\ rw[arch_size_def])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p2 _ _)) _`
  \\ fs [insert_shadow]
  \\ `lookup p2 s.refs = NONE` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ `p1 ≠ p2` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  (* Prove we are safe for space up to this point *)
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ qmatch_asmsub_rename_tac `size_of _ _ _ LN = (n'',_,seen0)`
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [] \\ rveq
     \\ fs [lookup_insert,lookup_delete] \\ rfs []
     \\ rw [arch_size_def])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
     (fs [Abbr `max0`,size_of_stack_def,GREATER_DEF,MAX_DEF])
  \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  (* Prove we are safe for space up to this point *)
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ qmatch_asmsub_rename_tac `size_of _ _ _ LN = (n'',_,seen0)`
     \\ Cases_on `IS_SOME (lookup ts seen0)` \\ fs [] \\ rveq
     \\ fs [lookup_insert,lookup_delete] \\ rfs [])
  \\ simp [] \\ ntac 2 (pop_assum kall_tac)
  (* Make stack_max sane to look at *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
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
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p3 _ _)) _`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp3) _`
  \\ `pp3 = p3` by
     (rw [Abbr`pp3`,Abbr`p3`,least_from_def]
     >- (Cases_on `0 = p2` \\ fs []
        \\ Cases_on `0 = p1` \\ fs []
        \\ numLib.LEAST_ELIM_TAC
        \\ rw []
        >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
           \\ rw [] \\ pop_assum (qspec_then `domain ((insert p2 ARB (insert p1 ARB s.refs)))` assume_tac)
           \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
           \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ Cases_on `x = p2` \\ fs [lookup_insert])
        \\ CCONTR_TAC \\ `0 < n` by rw []
        \\ first_x_assum drule \\ rw [])
     \\ fs [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [] \\ Cases_on `n'` \\ fs [])
     \\ fs [NOT_LESS]
     \\ CCONTR_TAC
     \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ `p3 ≠ p2` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `p3 ≠ p1` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [] \\ rfs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `lookup p3 s.refs = NONE` by
     (Q.UNABBREV_TAC `p3`
     \\ rw [least_from_def]
     >- (Cases_on `0 = p2` \\ Cases_on `0 = p1` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p2`
        \\ Cases_on `ptr = p1`
        \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p3` by (CCONTR_TAC  \\ fs [])
  \\ strip_assign
  \\ fs [lookup_insert]
  (* Prove we are safe for space up to this point *)
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ `safe` by
     (Q.UNABBREV_TAC `safe`
     \\ fs [GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ pop_assum (qspec_then `ByteArray T [121w; 10w]` assume_tac)
     \\ `wf (insert p2 (ByteArray T [121w; 10w])
              (insert p1 (ByteArray T [10w]) s.refs))` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p2` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [121w; 10w]` mp_tac)
     \\ fs [lookup_insert]
     \\ impl_tac
     >- (irule closed_ptrs_refs_insert \\ fs [closed_ptrs_def,lookup_insert])
     \\ strip_tac
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p3`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq
     \\ fs [lookup_delete]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq)
  \\ simp[] \\ ntac 2 (pop_assum kall_tac) \\ fs []
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [121w; 10w] []`
             \\ fs [])
  >- (fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
     \\ simp [data_safe_def,size_of_def,size_of_Number_head]
     \\ fs [size_of_heap_def,stack_to_vs_def,size_of_Number_head]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ fs [size_of_Number_head,insert_shadow] \\ rveq
     \\ fs [Once insert_def,toList_def,toListA_def]
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ simp [])
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ rveq \\ fs [flush_state_def]
  \\ Q.UNABBREV_TAC `rest_call`
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
  \\ `max0 = SOME (MAX smax (lsize + sstack + 14))` by
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
     \\ fs [Once insert_def,toList_def,toListA_def]
     \\ rveq \\ fs []
     (* insert p1 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p1`] mp_tac)
     \\ rpt (disch_then drule)
     \\ disch_then (qspec_then `ByteArray T [10w]` assume_tac)
     \\ `wf (insert p1 (ByteArray T [10w]) s.refs)` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p1` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [10w]` mp_tac)
     \\ impl_tac >- fs [closed_ptrs_def,closed_ptrs_refs_insert]
     \\ strip_tac
     (* insert p2 *)
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p2`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert] \\ rfs [] \\ rveq
     \\ pop_assum (qspec_then `ByteArray T [121w; 10w]` assume_tac)
     \\ `wf (insert p2 (ByteArray T [121w; 10w])
              (insert p1 (ByteArray T [10w]) s.refs))` by fs [wf_insert]
     \\ drule closed_ptrs_insert
     \\ disch_then (qspec_then `p2` mp_tac) \\ fs []
     \\ disch_then (qspec_then `ByteArray T [121w; 10w]` mp_tac)
     \\ fs [lookup_insert]
     \\ impl_tac
     >- (irule closed_ptrs_refs_insert \\ fs [closed_ptrs_def,lookup_insert])
     \\ strip_tac
     \\ drule_then drule size_of_insert
     \\ disch_then (qspecl_then [`s.limits`,`LN`,`p3`] mp_tac)
     \\ fs [lookup_insert]
     \\ strip_tac \\ fs [] \\ rveq
     \\ fs [lookup_insert]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq
     \\ fs [lookup_delete]
     \\ rfs [] \\ rveq \\ fs [] \\ rveq)
  >- fs [lookup_insert]
  >- rw [Once insert_def]
  \\ ho_match_mp_tac closed_ptrs_insert
  \\ fs [lookup_insert] \\ reverse conj_tac
  >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ fs [closed_ptrs_def])
  \\ ho_match_mp_tac closed_ptrs_insert
  \\ fs [lookup_insert] \\ reverse conj_tac
  >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ ho_match_mp_tac closed_ptrs_refs_insert \\ fs [lookup_insert]
     \\ fs [closed_ptrs_def])
  \\ ho_match_mp_tac closed_ptrs_insert
  \\ fs [lookup_insert] \\ reverse conj_tac
  >- (ho_match_mp_tac closed_ptrs_refs_insert \\ fs [closed_ptrs_def])
  \\ ONCE_REWRITE_TAC [closed_ptrs_cons]
  \\ conj_tac >- fs [closed_ptrs_APPEND,stack_to_vs_def]
  \\ fs [closed_ptrs_def,closed_ptrs_list_def]
  end
QED

Theorem data_safe_yes_code_shallow[local] =
  data_safe_yes_code |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_yes_code_abort:
 ∀s ts.
   (s.locals = fromList [RefPtr 2]) ∧
   (lookup 2 s.refs = SOME (ByteArray T [121w])) ∧
   2 ≤ s.limits.length_limit ∧
   (s.stack_frame_sizes = yes_config.word_conf.stack_frame_size) ∧
   s.limits.arch_64_bit ∧
   (s.tstamps = SOME ts) ∧
   (s.code = fromAList yes_data_prog)
   ⇒ ∃s' e. evaluate ((SND o SND) ^f21, s) =
       (SOME (Rerr (Rabort e)),s')
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList yes_data_prog`
                         yes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `yes_config.word_conf.stack_frame_size`
                         yes_config_def
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
  \\ rw [] \\ fs [fromList_def]
  \\ strip_call
  \\ `1 < 2 ** s.limits.length_limit`
     by (irule LESS_TRANS \\ qexists_tac `s.limits.length_limit` \\ fs [])
  \\ `2 < 2 ** s.limits.length_limit`
     by (Cases_on `s.limits.length_limit` \\ fs [])
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac `insert p1 _ s.refs`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp1) _`
  \\ `pp1 = p1`  by
     (UNABBREV_ALL_TAC \\ fs [least_from_def]
     \\ Cases_on `lookup 0 s.refs` \\ fs []
     >- (numLib.LEAST_ELIM_TAC
        \\ conj_tac >- (asm_exists_tac \\ fs [])
        \\ rw [] \\ Cases_on `n` \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (qexists_tac `ptr` \\ fs [])
     \\ rw [] \\ CCONTR_TAC
     \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [])
     \\ fs [NOT_LESS] \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  (* strip_makespace *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ simp []
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ ntac 2 strip_assign
  \\ strip_assign \\ fs []
  \\ Q.ABBREV_TAC `pred = ∃w. 10 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 10` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 6 (strip_assign \\ fs [])
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
  \\ `lookup p1 s.refs = NONE`  by
     (Q.UNABBREV_TAC `p1` \\ fs [least_from_def]
     \\ EVERY_CASE_TAC \\ fs [] \\ numLib.LEAST_ELIM_TAC
     >- metis_tac []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain s.refs` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x s.refs` \\ fs []
     \\ asm_exists_tac \\ fs [])
  \\ `p1 ≠ 2` by (CCONTR_TAC  \\ fs [])
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  (* open_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ ntac 6 strip_assign
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
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
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ push_env_def , to_shallow_def , to_shallow_thm]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* strip_assign *)
  \\ strip_assign
  \\ make_if
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p2 _ _)) _`
  \\ fs [insert_shadow]
  \\ `lookup p2 s.refs = NONE` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
  \\ `p1 ≠ p2` by
  (Q.UNABBREV_TAC `p2`
  \\ rw [least_from_def]
  >- (Cases_on `0 = p1` \\ fs [])
  >- (numLib.LEAST_ELIM_TAC \\ rw []
     \\ Cases_on `ptr = p1` \\ fs []
     \\ qexists_tac `ptr` \\ fs [])
  \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
  \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
  \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
  \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
  \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p2` by (CCONTR_TAC  \\ fs [])
  \\ IF_CASES_TAC >- simp [data_safe_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def
                 , to_shallow_thm , to_shallow_def ]
  \\ simp [LET_DEF]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ strip_assign
  \\ make_if
  \\ ntac 8 strip_assign
  (* make_tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ fs [insert_shadow]
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
  \\ qmatch_goalsub_abbrev_tac `dataSem$state_refs_fupd (K (insert p3 _ _)) _`
  \\ qmatch_goalsub_abbrev_tac `insert _ (RefPtr pp3) _`
  \\ `pp3 = p3` by
     (rw [Abbr`pp3`,Abbr`p3`,least_from_def]
     >- (Cases_on `0 = p2` \\ fs []
        \\ Cases_on `0 = p1` \\ fs []
        \\ numLib.LEAST_ELIM_TAC
        \\ rw []
        >- (mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
           \\ rw [] \\ pop_assum (qspec_then `domain ((insert p2 ARB (insert p1 ARB s.refs)))` assume_tac)
           \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
           \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ Cases_on `x = p2` \\ fs [lookup_insert])
        \\ CCONTR_TAC \\ `0 < n` by rw []
        \\ first_x_assum drule \\ rw [])
     \\ fs [] \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC
     \\ conj_tac >- (asm_exists_tac \\ fs [])
     \\ rw [] \\ Cases_on `n' < n`
     >- (first_x_assum drule \\ rw [] \\ Cases_on `n'` \\ fs [])
     \\ fs [NOT_LESS]
     \\ CCONTR_TAC
     \\ `n < n'` by rw []
     \\ first_x_assum drule \\ rw[]
     \\ Cases_on `n` \\ fs [])
  \\ rveq \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ `p3 ≠ p2` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `p3 ≠ p1` by
     (rw [Abbr `p3`,least_from_def]
     >- (CCONTR_TAC \\ fs [] \\ rfs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ asm_exists_tac \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV \\ rw []
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `lookup p3 s.refs = NONE` by
     (Q.UNABBREV_TAC `p3`
     \\ rw [least_from_def]
     >- (Cases_on `0 = p2` \\ Cases_on `0 = p1` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p2`
        \\ Cases_on `ptr = p1`
        \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ pop_assum (qspec_then `domain (insert p2 ARB (insert p1 ARB s.refs))` assume_tac)
     \\ fs [FINITE_domain,domain_lookup]
     \\ Cases_on `lookup x (insert p2 ARB (insert p1 ARB s.refs))`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p2` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ `2 ≠ p3` by (CCONTR_TAC  \\ fs [])
  \\ strip_assign
  \\ fs [lookup_insert]
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" [121w; 10w] []`
             \\ fs [])
  \\ strip_assign \\ strip_assign
  \\ simp [return_def,lookup_def,data_safe_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [insert_shadow,size_of_Number_head]
  \\ rveq \\ fs [flush_state_def]
  \\ Q.UNABBREV_TAC `rest_call`
  (* strip tailcall *)
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def ]
  \\ simp [code_lookup,lookup_def,lookup_insert,lookup_inter,frame_lookup]
  \\ IF_CASES_TAC
  >- fs [data_safe_def,GREATER_DEF,libTheory.the_def,size_of_stack_def]
  \\ simp[dec_clock_def]
  \\ eval_goalsub_tac ``dataSem$call_env _ _``
  \\ qmatch_goalsub_abbrev_tac `f0 (evaluate _)`
  \\ qmatch_goalsub_abbrev_tac `f0 e0`
  \\ reverse (sg `∃s' e. e0 = (SOME (Rerr (Rabort e)),s')`)
  \\ fs [Abbr`f0`,Abbr`e0`]
  \\ qmatch_goalsub_abbrev_tac `evaluate (p0,s0)`
  \\ `s0.clock < s.clock` by fs [Abbr `s0`,dec_clock_def]
  \\ first_x_assum (drule_then (qspec_then `ts + 2` mp_tac))
  \\ impl_tac >- (fs [Abbr `s0`,lookup_insert,call_env_def] \\ EVAL_TAC)
  \\ rw [Abbr`p0`,to_shallow_def,to_shallow_thm] \\ fs []
  end
QED

Theorem data_safe_yes_code_abort_shallow[local] =
  data_safe_yes_code_abort |> simp_rule [to_shallow_thm,to_shallow_def]

Theorem data_safe_yes:
 ∀ffi.
  backend_config_ok ^yes_x64_conf
  ⇒ is_safe_for_space ffi
       yes_x64_conf
       yes_prog
       (56,89)
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList yes_data_prog`
                         yes_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `yes_config.word_conf.stack_frame_size`
                         yes_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val open_call     = mk_open_call code_lookup frame_lookup
  val make_call     = mk_make_call open_call
  val strip_call    = mk_strip_call open_call
  val open_tailcall = mk_open_tailcall code_lookup frame_lookup
  val make_tailcall = mk_make_tailcall open_tailcall
 in
 REWRITE_TAC [yes_prog_def,yes_x64_conf_def]
 \\ strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ conj_tac >- EVAL_TAC
 \\ assume_tac yes_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac yes_to_data_updated_thm
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
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ntac 2 strip_assign
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 121 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 121` \\ rw [])
  \\ fs [] \\ ntac 2 (pop_assum kall_tac)
  \\ ho_match_mp_tac data_safe_bind_some
  \\ open_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ `∃s' e'. f s = (SOME (Rerr (Rabort e')),s')`
     by (UNABBREV_ALL_TAC
        \\ ho_match_mp_tac data_safe_yes_code_abort_shallow
        \\ fs [] \\ EVAL_TAC)
  \\ `data_safe (f s)` suffices_by (rw [] \\ rfs [])
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac data_safe_yes_code_shallow
  \\ rw [lookup_def,lookup_fromList,code_lookup]
  \\ EVAL_TAC
  \\ qexists_tac `12` \\ fs []
  end
QED

Theorem yes_s_def = mk_abbrev"yes_s"
                      ((rand o rand o rhs o concl) primSemEnvTheory.prim_sem_env_eq)

Definition yes_env_def:
  yes_env ffi = FST (THE (prim_sem_env sio_ffi_state))
End

Theorem prim_sem_env_yes:
  THE (prim_sem_env sio_ffi_state) = (yes_env ffi,yes_s)
Proof
EVAL_TAC \\ rw [yes_s_def]
QED

Theorem backend_config_ok_yes:
  backend_config_ok yes_x64_conf
Proof
 assume_tac x64_backend_config_ok
 \\ fs [backend_config_ok_def,yes_x64_conf_def,x64_backend_config_def]
QED

Theorem yes_semantics_prog_not_Fail:
  let (s,env) = THE (prim_sem_env sio_ffi_state)
  in ¬semantics_prog s env yes_prog Fail
Proof
  assume_tac yes_semantics_prog_Diverge
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

val yes_safe_thm =
    let
      val ffi = ``sio_ffi_state``
      val is_safe = data_safe_yes
                    |> REWRITE_RULE [GSYM yes_prog_def
                                    ,GSYM yes_x64_conf_def]
                    |> ISPEC ffi
      val not_fail = yes_semantics_prog_not_Fail
                     |> SIMP_RULE std_ss [LET_DEF,prim_sem_env_yes
                                         ,ELIM_UNCURRY]
      val is_corr = MATCH_MP compile_correct_is_safe_for_space yes_thm
                    |> REWRITE_RULE [GSYM yes_prog_def
                                    ,GSYM yes_x64_conf_def]
                    |> Q.INST [`stack_limit` |-> `56`
                              ,`heap_limit` |-> `89`]
                    |> INST_TYPE [``:'ffi`` |-> ``:unit``]
                    |> Q.INST [`ffi` |-> `sio_ffi_state`]
                    |> SIMP_RULE std_ss [prim_sem_env_yes,LET_DEF,not_fail,ELIM_UNCURRY]
      val machine_eq = MATCH_MP (machine_sem_eq_semantics_prog |> INST_TYPE [``:'ffi`` |-> ``:unit``])
                                (yes_semantics_prog_Diverge
                                   |> SIMP_RULE std_ss [LET_DEF,prim_sem_env_yes,ELIM_UNCURRY])
      val safe_thm_aux = MATCH_MP (IMP_TRANS is_safe is_corr) backend_config_ok_yes
    in MATCH_MP (MATCH_MP IMP_IMP_TRANS_THM machine_eq)
                (safe_thm_aux |> SIMP_RULE std_ss [prim_sem_env_yes,LET_DEF,ELIM_UNCURRY,backend_config_ok_yes])
    end

Theorem yes_has_space_for_dessert:
 (read_limits yes_x64_conf mc ms = (56,89)) ⇒
      mc_conf_ok mc ∧ mc_init_ok yes_x64_conf mc ∧
      installed yes_code cbspace yes_data data_sp
        yes_config.lab_conf.ffi_names sio_ffi_state
        (heap_regs yes_x64_conf.stack_conf.reg_names) mc ms ⇒
      machine_sem mc sio_ffi_state ms
        (Diverge (LREPEAT [put_str_event «y\n» ]))
Proof
  rw [] \\ drule yes_safe_thm
  \\ rpt (disch_then drule)
  \\ simp []
QED

val _ = check_thm yes_has_space_for_dessert;

val _ = export_theory();
