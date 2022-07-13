(*
  A data-cost example of a reverse (proofs)
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory
open costLib costPropsTheory
open dataSemTheory data_monadTheory dataLangTheory;
open miniBasisProgTheory;
open x64_configProofTheory;
open reverseProgTheory;

val _ = new_theory "reverseProof"

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val reverse_x64_conf = (rand o rator o lhs o concl) reverse_thm

val _ = install_naming_overloads "reverseProg";
val _ = write_to_file reverse_data_prog_def;

val reverse_body =
  “lookup_reverse (fromAList reverse_data_prog)”
  |> (REWRITE_CONV [reverse_data_prog_def] THENC EVAL)
  |> concl |> rand |> rand |> rand

val bvi_aux_body =
  “lookup_bvi_aux (fromAList reverse_data_prog)”
  |> (REWRITE_CONV [reverse_data_prog_def] THENC EVAL)
  |> concl |> rand |> rand |> rand

Definition repchar_list_def:
  (* cons *)
  (repchar_list (Block ts _ [Number i; rest]) (l:num) (tsb:num) ⇔
    (0 ≤ i ∧ i ≤ 255 ∧ (* i reps a character *)
    ts < tsb ∧
    l > 0 ∧ repchar_list rest (l-1) tsb)) ∧
  (* nil *)
  (repchar_list (Block _ tag []) (l:num) tsb ⇔ (tag = 0)) ∧
  (* everything else *)
  (repchar_list _ _ _ ⇔ F)
End

Theorem bvi_aux_constant_stack:
  ∀s ts sstack lsize res s' block1 block2.
   wf s.refs ∧
   (s.stack_frame_sizes = reverse_config.word_conf.stack_frame_size) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (s.locals_size = SOME lsize) ∧
   s.limits.arch_64_bit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (s.locals = fromList [block1; block2]) ∧
   (s.code = fromAList reverse_data_prog) ∧
   (evaluate (^bvi_aux_body, s) = (res,s'))
   ⇒ ∃k. s'.stack_max = OPTION_MAP ($+ k) s.stack_max
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList reverse_data_prog`
                         reverse_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `reverse_config.word_conf.stack_frame_size`
                         reverse_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val yk_strip_assign  = qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ ASM_REWRITE_TAC [ bind_def           , assign_def
                     , op_space_reset_def , closLangTheory.op_case_def
                     , cut_state_opt_def  , option_case_def
                     , do_app_def         , data_spaceTheory.op_space_req_def
                     , do_space_def       , closLangTheory.op_distinct
                     , MEM                , IS_NONE_DEF
                     , add_space_def      , check_lim_def
                     , do_stack_def       , flush_state_def
                     , cut_state_def
                     , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ TRY(eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp [])
  \\ TRY(eval_goalsub_tac ``dataSem$get_vars    _ _`` \\ simp [])
  \\ simp [ do_app_aux_def    , set_var_def       , lookup_def
          , domain_IS_SOME    , code_lookup       , size_of_heap_def
          , consume_space_def , with_fresh_ts_def , stack_consumed_def
          , frame_lookup      , allowed_op_def    , size_of_stack_def
          , flush_state_def   , vs_depth_def      , eq_code_stack_max_def
          , lookup_insert     , semanticPrimitivesTheory.copy_array_def
          , size_of_stack_frame_def
          , backend_commonTheory.small_enough_int_def ]
  \\ (fn (asm, goal) => let
        val pat   = ``sptree$lookup _ _``
        val terms = find_terms (can (match_term pat)) goal
        val simps = map (PATH_CONV "lr" EVAL) terms
      in ONCE_REWRITE_TAC simps (asm,goal) end)
  \\ simp [frame_lookup]
  \\ Q.UNABBREV_TAC `rest_ass`
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
  \\ pop_assum mp_tac
  \\ strip_assign
  \\ Cases_on ‘block1’
  \\ TRY(rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
         Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ simp[]
  \\ simp[Once bind_def,data_monadTheory.if_var_def,lookup_insert]
  \\ TOP_CASE_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >>
      pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
  \\ IF_CASES_TAC >-
       (‘BIT1 (BIT1 ZERO) = 3’ by(PURE_REWRITE_TAC[BIT1,ADD,ALT_ZERO,NUMERAL_DEF] >>
                                  simp[]) >>
        pop_assum SUBST_ALL_TAC >>
        strip_assign >>
        qmatch_goalsub_abbrev_tac ‘if a1 then _ else _’ >>
        ‘a1’ by(qunabbrev_tac ‘a1’ >> EVAL_TAC) >>
        simp[] >>
        qunabbrev_tac ‘a1’ >>
        simp[get_vars_def,get_var_def,lookup_inter,lookup_def,lookup_insert] >>
        simp[v_to_list_def,backend_commonTheory.nil_tag_def] >>
        simp[flush_state_def,check_lim_def] >>
        rw[] >> fs[AllCaseEqs()] >> rveq >> fs[] >> rw[] >>
        fs[size_of_stack_def] >> simp[reverse_config_def,lookup_def] >>
        Cases_on ‘s.stack_max’ >> rw[MAX_DEF,PULL_EXISTS] >>
        fs[lookup_def] >>
        pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC
        )
  \\ ‘BIT1 (BIT1 ZERO) = 3’ by(PURE_REWRITE_TAC[BIT1,ADD,ALT_ZERO,NUMERAL_DEF] >>
                               simp[])
  \\ pop_assum SUBST_ALL_TAC
  \\ reverse TOP_CASE_TAC >-
    (rw[] >> rw[] >>
     Cases_on ‘s.stack_max’ >> rw[MAX_DEF,PULL_EXISTS] >>
     fs[lookup_def] >>
     pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
  \\ strip_makespace
  \\ strip_assign
  \\ ‘NUMERAL (BIT1 3) = 7’ by(PURE_REWRITE_TAC[BIT1,ADD,ALT_ZERO,NUMERAL_DEF] >>
                               simp[])
  \\ pop_assum SUBST_ALL_TAC
  \\ ‘NUMERAL (BIT2(BIT1(BIT2(BIT1 3)))) = 68’ by(PURE_REWRITE_TAC[BIT1,ADD,ALT_ZERO,NUMERAL_DEF] >>
                                                  simp[])
  \\ pop_assum SUBST_ALL_TAC
  \\ strip_assign
  \\ reverse IF_CASES_TAC >-
    (rw[] >> rw[] >>
     Cases_on ‘s.stack_max’ >> rw[MAX_DEF,PULL_EXISTS] >>
     fs[lookup_def] >>
     pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
  \\ simp[]
  \\ eval_goalsub_tac “lookup 0 (insert _ _ _)”
  \\ simp[]
  \\ reverse IF_CASES_TAC >-
    (rw[] >> rw[] >>
     Cases_on ‘s.stack_max’ >> rw[MAX_DEF,PULL_EXISTS] >>
     fs[lookup_def] >>
     pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC >>
     qexists_tac ‘0’ \\ simp[])
  \\ simp[]
  \\ strip_assign
  \\ strip_assign
  \\ ‘NUMERAL 3 = 3’ by(metis_tac[NUMERAL_DEF])
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[]
  \\ simp[numeralTheory.numeral_eq]
  \\ strip_assign
  \\ simp[v_to_list_def,backend_commonTheory.cons_tag_def,backend_commonTheory.nil_tag_def]
  \\ Cases_on ‘v_to_list block2’ >-
    (simp[] >> rw[] >> simp[] >> fs[size_of_stack_def] >>
     Cases_on ‘s.stack_max’ >> rw[MAX_DEF,PULL_EXISTS] >>
     fs[lookup_def] >>
     pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
  \\ simp[check_lim_def]
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ simp [lookup_insert,lookup_def]
  \\ eval_goalsub_tac “lookup (NUMERAL _) (fromAList reverse_data_prog)”
  \\ ‘BIT1 (BIT1 (BIT1 (BIT2 3))) = 71’ by metis_tac[NUMERAL_DEF]
  \\ simp [code_lookup]
  \\ IF_CASES_TAC >-
    (simp[] >> rw[] >> simp[] >>fs[size_of_stack_def] >>
     Cases_on ‘s.stack_max’ >> rw[MAX_DEF,PULL_EXISTS] >>
     fs[lookup_def] >>
     pop_assum mp_tac >> rpt(pop_assum kall_tac) >> intLib.COOPER_TAC)
  \\ fs [ to_shallow_thm
        , to_shallow_def
        , initial_state_def
        , call_env_def
        , dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘_ (_ s'') = (res,s')’
  \\ first_x_assum(qspec_then ‘s''’ mp_tac)
  \\ simp[Abbr ‘s''’]
  \\ simp[fromList_def]
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ disch_then(qspec_then ‘(list_to_v (ts + 1) block2 [HD l])’ mp_tac)
  \\ disch_then(qspec_then ‘(EL 1 l)’ mp_tac)
  \\ simp[]
  \\ ‘NUMERAL 71 = 71’ by metis_tac[NUMERAL_DEF]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[frame_lookup]
  \\ ‘NUMERAL 6 = 6’ by(metis_tac[NUMERAL_DEF])
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac ‘a1 = (_,_)’
  \\ disch_then(qspecl_then [‘SND a1’,‘FST a1’] mp_tac)
  \\ Cases_on ‘a1’ >> rw[] >> simp[]
  \\ fs[size_of_stack_def]
  \\ rpt(pop_assum kall_tac)
  \\ Cases_on ‘s.stack_max’ \\ simp[]
  \\ rw[MAX_DEF] \\ intLib.COOPER_TAC
  end
QED

Theorem reverse_code_constant_stack:
  ∀s ts sstack lsize res s' block.
   wf s.refs ∧
   (s.stack_frame_sizes = reverse_config.word_conf.stack_frame_size) ∧
   (size_of_stack s.stack = SOME sstack) ∧
   (s.locals_size = SOME lsize) ∧
   s.limits.arch_64_bit ∧
   2 ≤ s.limits.length_limit ∧
   (s.tstamps = SOME ts) ∧
   0 < ts ∧
   (s.locals = fromList [block]) ∧
   (repchar_list block l ts) ∧
   (s.code = fromAList reverse_data_prog) ∧
   (evaluate (^reverse_body, s) = (res,s'))
   ⇒ ∃k. s'.stack_max = OPTION_MAP ($+ k) s.stack_max
Proof
 let
  val code_lookup   = mk_code_lookup
                        `fromAList reverse_data_prog`
                         reverse_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `reverse_config.word_conf.stack_frame_size`
                         reverse_config_def
  val strip_assign  = mk_strip_assign code_lookup frame_lookup
  val yk_strip_assign  = qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ ASM_REWRITE_TAC [ bind_def           , assign_def
                     , op_space_reset_def , closLangTheory.op_case_def
                     , cut_state_opt_def  , option_case_def
                     , do_app_def         , data_spaceTheory.op_space_req_def
                     , do_space_def       , closLangTheory.op_distinct
                     , MEM                , IS_NONE_DEF
                     , add_space_def      , check_lim_def
                     , do_stack_def       , flush_state_def
                     , cut_state_def
                     , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ TRY(eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp [])
  \\ TRY(eval_goalsub_tac ``dataSem$get_vars    _ _`` \\ simp [])
  \\ simp [ do_app_aux_def    , set_var_def       , lookup_def
          , domain_IS_SOME    , code_lookup       , size_of_heap_def
          , consume_space_def , with_fresh_ts_def , stack_consumed_def
          , frame_lookup      , allowed_op_def    , size_of_stack_def
          , flush_state_def   , vs_depth_def      , eq_code_stack_max_def
          , lookup_insert     , semanticPrimitivesTheory.copy_array_def
          , size_of_stack_frame_def
          , backend_commonTheory.small_enough_int_def ]
  \\ (fn (asm, goal) => let
        val pat   = ``sptree$lookup _ _``
        val terms = find_terms (can (match_term pat)) goal
        val simps = map (PATH_CONV "lr" EVAL) terms
      in ONCE_REWRITE_TAC simps (asm,goal) end)
  \\ simp [frame_lookup]
  \\ Q.UNABBREV_TAC `rest_ass`
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
  \\ pop_assum mp_tac
  \\ yk_strip_assign
  \\ rename1 `state_safe_for_space_fupd (K safe) _`
  \\ yk_strip_assign
  \\ TOP_CASE_TAC >> fs[repchar_list_def]
  \\ reverse TOP_CASE_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ simp[Once bind_def,data_monadTheory.if_var_def,lookup_insert]
  \\ TOP_CASE_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ fs[CaseEq "dataSem$v",CaseEq "prod", CaseEq "option", CaseEq "semanticPrimitives$result"] >> rveq >> fs[] >> rveq >> fs[]
  \\ IF_CASES_TAC >-
     (yk_strip_assign >>
      qmatch_goalsub_abbrev_tac ‘if a1 then _ else _’ >>
      ‘a1’ by(qunabbrev_tac ‘a1’ >> EVAL_TAC) >>
      simp[] >>
      qunabbrev_tac ‘a1’ >>
      simp[get_vars_def,get_var_def,lookup_inter,lookup_def,lookup_insert] >>
      simp[v_to_list_def,backend_commonTheory.nil_tag_def] >>
      simp[flush_state_def,check_lim_def] >>
      rw[] >> simp[] >>
      Cases_on ‘s.stack_max’ >> rw[PULL_EXISTS] >>
      simp[reverse_config_def,lookup_def] >>
      fs[size_of_stack_def] >>
      rw[MAX_DEF] >>
      intLib.COOPER_TAC)
  \\ reverse TOP_CASE_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ rename1 `state_safe_for_space_fupd (K safe') _`
  \\ strip_makespace
  \\ strip_assign
  \\ strip_assign
  \\ reverse IF_CASES_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ simp[]
  \\ simp[lookup_insert,lookup_def]
  \\ reverse IF_CASES_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ simp[]
  \\ strip_assign
  \\ strip_assign
  \\ strip_assign
  \\ simp[v_to_list_def,backend_commonTheory.cons_tag_def,backend_commonTheory.nil_tag_def]
  \\ simp[]
  \\ ASM_REWRITE_TAC [ tailcall_def , find_code_def
                     , get_vars_def , get_var_def
                     , lookup_def   , timeout_def
                     , flush_state_def , lookup_insert,check_lim_def,
                       code_lookup,lookup_def,frame_lookup]
  \\ simp[lookup_insert,check_lim_def,code_lookup,lookup_def,frame_lookup]
  \\ IF_CASES_TAC >-
     (rw[] >> fs[AllCaseEqs()] >> rveq >> rw[] >> fs[size_of_stack_def] >>
      Cases_on ‘s.stack_max’ >> rw[MAX_DEF] >> intLib.COOPER_TAC)
  \\ simp[call_env_def,dec_clock_def]
  \\ simp [code_lookup,lookup_def,frame_lookup]
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac ‘_ (evaluate(_,a1)) = (_,_)’
  \\ qspec_then ‘a1’ mp_tac bvi_aux_constant_stack
  \\ simp[GSYM PULL_FORALL,GSYM PULL_EXISTS]
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV List.rev))
  \\ simp[GSYM PULL_FORALL,GSYM PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate a2’
  \\ disch_then(qspec_then ‘SND(evaluate a2)’ mp_tac)
  \\ reverse impl_tac >-
    (Cases_on ‘evaluate a2’ >> fs[Abbr ‘a1’,Abbr‘a2’] >>
     rw[] >> rw[] >>
     fs[size_of_stack_def] >> Cases_on ‘s.stack_max’ >> simp[] >>
     rw[] >> rw[MAX_DEF] >>
     intLib.COOPER_TAC)
  \\ Cases_on ‘evaluate a2’ >> simp[Abbr ‘a1’,Abbr ‘a2’]
  \\ metis_tac[]
  end
QED

val _ = export_theory();
