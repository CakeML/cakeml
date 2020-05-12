(*
  Prove that lcgLoop never exits prematurely.
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory;
open costLib costPropsTheory;
open dataSemTheory data_monadTheory dataLangTheory;
open lcgLoopProgTheory;

val _ = new_theory "lcgLoopProof"

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val lcgLoop = lcgLoop_ast_def |> concl |> rand

val _ = install_naming_overloads "lcgLoopProg";
val _ = write_to_file lcgLoop_data_prog_def;

val body = ``lookup_lcgLoop (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand


val coeff_bounds_def = Define`
  coeff_bounds a c m =
  small_num T (&a) ∧
  small_num T (&c) ∧
  small_num T (&m) ∧
  small_num T (&(a*m + c))`

Theorem size_of_Number_head_append:
  ∀ls.
  EVERY (λl. case l of Number n => small_num lims.arch_64_bit n | _ => F) ls ⇒
  (size_of lims (ls++vs) refs seen = size_of lims vs refs seen)
Proof
  Induct>>rw[]>>
  Cases_on`h`>>fs[]>>
  DEP_REWRITE_TAC [size_of_Number_head]>>
  simp[]
QED

Theorem small_num_bound_imp_1:
  small_num b (&n) ∧ x < n ⇒
  small_num b (&x)
Proof
  rw[small_num_def]
QED

Theorem small_num_bound_imp_2:
  small_num b (&(c+a*n)) ∧ x < n ⇒
  small_num b (&(a * x) + &c) ∧
  small_num b (&(a*x))
Proof
  rw[small_num_def]>>
  `(&(a * x) + &c):int = &(a*x+c)` by
    simp[integerTheory.INT_ADD]>>
  `c+a*x <= c+a*n` by simp[]>>
  simp[]
QED

Theorem max_right_absorb[simp]:
  MAX (MAX a b) b = MAX a b
Proof
  rw[MAX_DEF]
QED

Theorem max_right_absorb_2:
  b ≤ c ⇒
  (MAX (MAX a b) c = MAX a c)
Proof
  rw[MAX_DEF]
QED

Theorem data_safe_lcgLoop_code[local]:
  ∀s sstack smax y.
  s.safe_for_space ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (s.stack_max = SOME smax) ∧
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (sstack + N1 < s.limits.stack_limit) ∧
  (sstack + lsize + N2 < s.limits.stack_limit) ∧
  (smax < s.limits.stack_limit) ∧
  s.limits.arch_64_bit ∧
  (size_of_heap s + 3 (* N3 *) ≤ s.limits.heap_limit) ∧
  (s.locals = fromList [Number (&x); Number (&m); Number (&c); Number (&a)]) ∧
  (* N1, N2, N3 are TODO constants to fill *)
  (* unsure *) (s.tstamps = SOME ts) ∧
  (1 < s.limits.length_limit) ∧
  (coeff_bounds a c m ∧ x < m ) ∧
  (lookup_lcgLoop s.code = SOME (1,^body))
  ⇒ data_safe (evaluate (^body, s))
Proof
let
  val code_lookup   = mk_code_lookup
                        `fromAList lcgLoop_data_prog`
                        lcgLoop_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `lcgLoop_config.word_conf.stack_frame_size`
                        lcgLoop_config_def
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

  (* strip_assign has an internal call to eval_goalsub_tac that doesn't work well *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ REWRITE_TAC [ bind_def           , assign_def
                 , op_space_reset_def , closLangTheory.op_case_def
                 , cut_state_opt_def  , option_case_def
                 , do_app_def         , data_spaceTheory.op_space_req_def
                 , do_space_def       , closLangTheory.op_distinct
                 , MEM                , IS_NONE_DEF
                 , add_space_def      , check_lim_def
                 , do_stack_def       , flush_state_def
                 , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ qmatch_goalsub_abbrev_tac`cut_state cs s` >>
  `cut_state cs s = SOME s` by (
    simp[Abbr`cs`,cut_state_def,cut_env_def]>>
    simp[state_component_equality]>>
    EVAL_TAC)>>
  simp[Abbr`cs`]
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
  \\ Q.UNABBREV_TAC `rest_ass` >>

  fs[coeff_bounds_def] >>
  `small_num T (&x)` by metis_tac[small_num_bound_imp_1]>>
  drule small_num_bound_imp_2>>
  disch_then drule>>simp[]>>
  strip_tac>>

  `space_consumed s Mult [Number (&a); Number (&x)] = 0` by (
    fs[small_num_def]>>
    EVAL_TAC>>
    simp[])>>
  simp[libTheory.the_def]>>
  simp[size_of_heap_def]

  \\ qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ REWRITE_TAC [ bind_def           , assign_def
                 , op_space_reset_def , closLangTheory.op_case_def
                 , cut_state_opt_def  , option_case_def
                 , do_app_def         , data_spaceTheory.op_space_req_def
                 , do_space_def       , closLangTheory.op_distinct
                 , MEM                , IS_NONE_DEF
                 , add_space_def      , check_lim_def
                 , do_stack_def       , flush_state_def
                 , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ qmatch_goalsub_abbrev_tac`cut_state cs s2` >>
  `cut_state cs s2 = SOME (s2 with locals := inter s2.locals cs)` by
    (simp[Abbr`cs`,cut_state_def,cut_env_def,Abbr`s2`]>>
    simp[state_component_equality])
  \\ simp[Abbr`cs`,Abbr`s2`]
  \\ eval_goalsub_tac``inter _ _``
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
  \\ Q.UNABBREV_TAC `rest_ass` >>

  simp[space_consumed_def,stack_to_vs_def]>>

  PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
  DEP_ONCE_REWRITE_TAC [size_of_Number_head_append]>>
  CONJ_TAC >- (
    eval_goalsub_tac``sptree$toList _``>>
    simp[] )>>
  simp[libTheory.the_def]>>

  qpat_abbrev_tac`sss = size_of _ (_ ++ _ ++ _) _ _`>>
  `sss = size_of s.limits (FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global) s.refs LN` by
    (simp[Abbr`sss`]>>
    PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
    match_mp_tac size_of_Number_head_append>>
    eval_goalsub_tac``sptree$toList _``>>
    simp[])>>
  simp[]>>
  ntac 2 (pop_assum kall_tac)>>

  strip_assign>>
  simp[Once bind_def,data_monadTheory.if_var_def]>>
  eval_goalsub_tac``sptree$lookup _ _``>>
  `~(0 = m)` by intLib.ARITH_TAC>>
  simp[]>>
  eval_goalsub_tac``dataSem$isBool _ _``>>
  simp[]>>
  eval_goalsub_tac``dataSem$isBool _ _``>>
  simp[] >>

  qpat_abbrev_tac`temp = bind _ _`>>
  qpat_abbrev_tac`xxx = bind _ _`>>
  simp[Abbr`temp`]>>
  qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ REWRITE_TAC [ bind_def           , assign_def
                 , op_space_reset_def , closLangTheory.op_case_def
                 , cut_state_opt_def  , option_case_def
                 , do_app_def         , data_spaceTheory.op_space_req_def
                 , do_space_def       , closLangTheory.op_distinct
                 , MEM                , IS_NONE_DEF
                 , add_space_def      , check_lim_def
                 , do_stack_def       , flush_state_def
                 , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ qmatch_goalsub_abbrev_tac`cut_state cs s2` >>
  `cut_state cs s2 = SOME (s2 with locals := inter s2.locals cs)` by
    (simp[Abbr`cs`,cut_state_def,cut_env_def,Abbr`s2`]>>
    simp[state_component_equality])
  \\ simp[Abbr`cs`,Abbr`s2`]
  \\ eval_goalsub_tac``inter _ _``
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
  \\ Q.UNABBREV_TAC `rest_ass` >>

  `small_num T ((&(a * x) + &c) % &m)` by (
    simp[integerTheory.INT_ADD,integerTheory.INT_MOD]>>
    match_mp_tac (GEN_ALL small_num_bound_imp_1)>>
    qexists_tac`m`>>simp[])>>
  simp[space_consumed_def,stack_to_vs_def]>>

  qpat_abbrev_tac`sss = size_of _ (_ ++ _ ++ _) _ _`>>
  `sss = size_of s.limits (FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global) s.refs LN` by
    (simp[Abbr`sss`]>>
    PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
    match_mp_tac size_of_Number_head_append>>
    eval_goalsub_tac``sptree$toList _``>>
    simp[])>>
  simp[]>>
  ntac 2 (pop_assum kall_tac)>>
  simp[libTheory.the_def,move_def,set_var_def]>>

  simp[Abbr`xxx`]>>

  (* strip_makespace *)
  qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ simp[size_of_heap_def,size_of_def,stack_to_vs_def] >>
  qpat_abbrev_tac`sss = size_of _ (_ ++ _ ++ _) _ _`>>
  `sss = size_of s.limits (FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global) s.refs LN` by
    (simp[Abbr`sss`]>>
    PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
    match_mp_tac size_of_Number_head_append>>
    eval_goalsub_tac``sptree$toList _``>>
    simp[])>>
  simp[]>>
  ntac 2 (pop_assum kall_tac)>>

  DEP_REWRITE_TAC[max_right_absorb_2]>>simp[]>>
  Q.UNABBREV_TAC `rest_mkspc`>>

  strip_assign>>
  strip_assign>>
  simp[]>>
  strip_assign>>
  simp[check_lim_def]>>

  simp[GSYM size_of_stack_def]>>
  qmatch_goalsub_abbrev_tac `sz ≤ s.limits.heap_limit`>>
  `sz = size_of_heap s` by (
    simp[Abbr`sz`]>>simp[size_of_heap_def,stack_to_vs_def]>>
    qpat_abbrev_tac`sss = size_of _ (_ ++ _ ++ _) _ _`>>
    `sss = size_of s.limits (FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global) s.refs LN` by
      (simp[Abbr`sss`]>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac size_of_Number_head_append>>
      eval_goalsub_tac``sptree$toList _``>>
      simp[])>>
    simp[])>>
  simp[libTheory.the_def]>>
  cheat
QED

val _ = export_theory();
