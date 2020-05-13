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

val hex_body = ``lookup_hex (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

val hex_body_def = Define`
  hex_body = ^hex_body`

val strip_asg_n =
  REWRITE_TAC [ bind_def           , assign_def
                 , op_space_reset_def , closLangTheory.op_case_def
                 , cut_state_opt_def  , option_case_def
                 , do_app_def         , data_spaceTheory.op_space_req_def
                 , do_space_def       , closLangTheory.op_distinct
                 , MEM                , IS_NONE_DEF
                 , add_space_def      , check_lim_def
                 , do_stack_def       , flush_state_def
                 , bvi_to_dataTheory.op_requires_names_eqn ]
  \\ BETA_TAC
  \\ simp[get_vars_def, get_var_def, lookup_insert]
  \\ simp [ do_app_aux_def    , set_var_def       , lookup_def
          , domain_IS_SOME    , size_of_heap_def
          , consume_space_def , with_fresh_ts_def , stack_consumed_def
          , allowed_op_def    , size_of_stack_def
          , flush_state_def   , vs_depth_def      , eq_code_stack_max_def
          , lookup_insert     , semanticPrimitivesTheory.copy_array_def
          , size_of_stack_frame_def
          , backend_commonTheory.small_enough_int_def ]
  \\ (fn (asm, goal) => let
        val pat   = ``sptree$lookup _ _``
        val terms = find_terms (can (match_term pat)) goal
        val simps = map (PATH_CONV "lr" EVAL) terms
      in ONCE_REWRITE_TAC simps (asm,goal) end)
  \\ simp []

val strip_asg =
  qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
  \\ strip_asg_n
  \\ Q.UNABBREV_TAC `rest_ass`

Theorem isBool_Boolv[simp]:
  isBool b (Boolv b') ⇔ (b = b')
Proof
  simp[bvi_to_dataProofTheory.isBool_eq]>>
  EVAL_TAC>>
  rw[]>>
  EVAL_TAC
QED

Theorem hex_evaluate:
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (sstack + lsize < s.limits.stack_limit) ∧
  (lookup 0 s.locals = SOME (Number (&n))) ∧
  n < 10 ⇒
  (evaluate (hex_body,s) = (SOME (Rval (Number (&(n+48)))),
    s with <|locals := LN; locals_size := SOME 0;
         stack_max := OPTION_MAP2 MAX s.stack_max (SOME (lsize + sstack))|>))
Proof
  rw[hex_body_def]>>
  simp[ to_shallow_thm, to_shallow_def, initial_state_def ]>>
  ntac 9 (
  strip_asg>>
  simp[Once bind_def,data_monadTheory.if_var_def,lookup_insert]>>
  IF_CASES_TAC
  >- (
    pop_assum (assume_tac o SYM)>>
    strip_asg_n>>
    simp[state_component_equality,libTheory.the_def]))>>
  simp[Once bind_def,data_monadTheory.if_var_def,lookup_insert]>>
  strip_asg_n>>
  simp[state_component_equality,libTheory.the_def]>>
  simp[GSYM size_of_stack_def]>>
  simp[state_component_equality,libTheory.the_def]
QED

val n2l_acc_body = ``lookup_n2l_acc (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

val n2l_acc_body_def = Define`
  n2l_acc_body = ^n2l_acc_body`

Theorem n2l_acc_evaluate:
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (s.stack_max = SOME sm) ∧
  (sstack + lsize < s.limits.stack_limit) ∧
  (s.locals = fromList [acc; Number (&n)]) ∧
  (lookup 16 s.stack_frame_sizes = SOME sz16) ∧
  (lookup 17 s.stack_frame_sizes = SOME sz17) ∧
  (lookup LongDiv_location s.stack_frame_sizes = SOME ld) ∧
  (lookup LongDiv1_location s.stack_frame_sizes = SOME ld1) ∧
  (lsize + (sstack + MAX sz17 sz16) < s.limits.stack_limit) ∧
  (lsize + (sstack + MAX ld ld1) < s.limits.stack_limit) ∧
  s.safe_for_space ∧
  s.limits.arch_64_bit ∧
  small_num T (&n) ∧
  (lookup_hex s.code = SOME(1,hex_body)) ∧
  (lookup_hex s.stack_frame_sizes = SOME szhex) ∧
  s.clock > 0 ∧
  (s.tstamps = SOME ts)
  ⇒
  (evaluate (n2l_acc_body,s) = (SOME res, s'))
Proof
  rw[n2l_acc_body_def]>>
  simp[ to_shallow_thm, to_shallow_def, initial_state_def ]>>
  strip_asg >>
  simp[libTheory.the_def]>>
  strip_asg >>
  qmatch_goalsub_abbrev_tac`cut_state ll ss`>>
  `cut_state ll ss = SOME (ss with locals := fromList [acc; Number (&n); Number 10])` by
    (unabbrev_all_tac>>EVAL_TAC)>>
  simp[Abbr`ss`,Abbr`ll`]>>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  simp[space_consumed_def,stack_to_vs_def] >>
  simp[GSYM size_of_stack_def]>>
  eval_goalsub_tac``size_of _ _ _``>>
  simp[Once bind_def,data_monadTheory.if_var_def,lookup_insert]>>
  IF_CASES_TAC
  >- (
    cheat
    (* simp[call_def]>>
    eval_goalsub_tac``get_vars [1] (_:dataSem$v sptree$num_map)``>>simp[]>>
    simp[find_code_def]>>
    qmatch_goalsub_abbrev_tac`cut_env ll loc`>>
    `dataSem$cut_env ll loc = SOME (fromList[acc])` by
      (unabbrev_all_tac>>EVAL_TAC)>>
    simp[]>>
    IF_CASES_TAC
    >- cheat
    DEP_REWRITE_TAC [GEN_ALL hex_evaluate]>>
    CONJ_TAC>- *)
    )
  >>
  strip_asg>>
  strip_asg>>
  qmatch_goalsub_abbrev_tac`cut_state ll ss`>>
  `cut_state ll ss = SOME (ss with locals := fromAList [(0,acc); (1,Number (&n)); (8,Number 10)])` by
    (unabbrev_all_tac>>EVAL_TAC)>>
  simp[Abbr`ss`,Abbr`ll`]>>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  `small_num T 10 ∧ small_num T (&(n MOD 10))` by
    (EVAL_TAC>>simp[]>>
    intLib.ARITH_TAC)>>
  simp[stack_consumed_def,space_consumed_def,libTheory.the_def,stack_to_vs_def]>>
  simp[GSYM size_of_stack_def,libTheory.the_def]>>
  eval_goalsub_tac``sptree$toList _``>> simp[] >>
  simp[Once bind_def,call_def]>>
  eval_goalsub_tac``get_vars [9] (_:dataSem$v sptree$num_map)``>>simp[]>>
  simp[find_code_def]>>
  qmatch_goalsub_abbrev_tac`cut_env ll loc`>>
  `dataSem$cut_env ll loc = SOME (fromList[acc ; Number(&n)])` by
    (unabbrev_all_tac>>EVAL_TAC)>>
  simp[Abbr`ll`,Abbr`loc`]>>
  simp[call_env_def,push_env_def,dec_clock_def]>>
  simp[size_of_stack_def,size_of_stack_frame_def]>>
  simp[GSYM size_of_stack_def]>>

  qmatch_goalsub_abbrev_tac`(hex_body,ss)`>>
  `size_of_stack ss.stack = SOME (lsize+sstack)` by
    (simp[Abbr`ss`,size_of_stack_def,size_of_stack_frame_def]>>
    simp[GSYM size_of_stack_def])>>
  `(ss.locals_size = SOME szhex)` by fs[Abbr`ss`]>>
  `((lsize+sstack) + szhex < ss.limits.stack_limit)` by cheat>>
  drule hex_evaluate>>
  disch_then drule>>
  simp[Abbr`ss`]>>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  disch_then kall_tac>>
  simp[pop_env_def]>>
  strip_makespace >>
  simp[]>>
  `n MOD 10 + 48 < 2305843009213693952` by cheat>>
  simp[]>>
  strip_asg>>
  simp[check_lim_def]>>
  strip_asg>>
  strip_asg>>
  qmatch_goalsub_abbrev_tac`cut_state ll ss`>>
  `cut_state ll ss = SOME (ss with locals := fromAList [(1,Number (&n)); (11, (Block ts 0 [Number (&(n MOD 10 + 48)); acc])); (14, Number 10)])`
    (unabbrev_all_tac>>EVAL_TAC)>>
  simp[]>>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
  simp[tailcall_def]>>
  cheat
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
  val still_safe    =
    (qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
    \\ ‘safe’ by
      (Q.UNABBREV_TAC ‘safe’
       \\ fs[coeff_bounds_def,libTheory.the_def,size_of_Number_head,
             small_num_def,data_safe_def,size_of_heap_def,stack_to_vs_def,
             size_of_def,size_of_stack_def]
       \\ rpt (pairarg_tac \\ fs []) \\ rveq
       \\ pop_assum mp_tac
       \\ eval_goalsub_tac ``size_of _ _`` \\ simp []
       \\ fs [size_of_Number_head,small_num_def])
    \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac))
  fun max_is t =
     (qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _`
     \\ ‘max0 = SOME (^(Term t))’ by
       (Q.UNABBREV_TAC ‘max0’ \\ fs [small_num_def,size_of_stack_def])
     \\ ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac))
in
  measureInduct_on `^s.clock`
  \\ fs [to_shallow_thm
         , to_shallow_def
         , coeff_bounds_def
         , initial_state_def ]
  \\ rw [] \\ fs [fromList_def]
  (* Preliminaries *)
  \\ `small_num T ((&(a * x) + &c) % &m)` by
    (simp[integerTheory.INT_ADD,integerTheory.INT_MOD]
     \\ match_mp_tac (GEN_ALL small_num_bound_imp_1)
     \\ qexists_tac`m`>>simp[])
  \\ `small_num T (&x)` by metis_tac[small_num_bound_imp_1,coeff_bounds_def]
  \\ drule small_num_bound_imp_2
  \\ disch_then drule \\ simp[]
  \\ strip_tac \\ simp []
  (* 9 :≡ (Mult,[3; 0],...) *)
  \\ strip_assign \\ still_safe
  (* stack_max *)
  \\ max_is ‘MAX smax (lsize + sstack)’
  (* Do we care about peak heap? *)
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap0) _`
  \\ pop_assum kall_tac
  (* 10 :≡ (Add,[9; 2],...) *)
  \\ strip_assign \\ still_safe
  (* peak_heap *)
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap1) _`
  \\ pop_assum kall_tac
  (* 11 :≡ (EqualInt 0,[1],NONE) *)
  \\ strip_assign
  (* if_var 11 ... *)
  \\ qmatch_goalsub_abbrev_tac `bind _ if_rest_ass`
  \\ simp [bind_def]
  \\ make_if
  (* 13 :≡ (Mod,[10; 1],...) *)
  \\ strip_assign \\ still_safe
  (* stack_max *)
  \\ max_is ‘MAX smax (lsize + sstack)’
  (* peak_heap *)
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap2) _`
  \\ pop_assum kall_tac
  (* move 14 13 *)
  \\ simp [move_def,lookup_def,set_var_def]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* Exit if *)
  \\ Q.UNABBREV_TAC ‘if_rest_ass’
  (* make_space 3 ... *)
  \\ strip_makespace \\ still_safe
  (* Do we care about peak heap? *)
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap3) _`
  \\ pop_assum kall_tac
  (* 17 :≡ (Cons 0,[],NONE) *)
  \\ strip_assign \\ still_safe
  (* 18 :≡ (Const 10,[],NONE) *)
  \\ strip_assign
  (* 19 :≡ (Cons 0,[18; 17],NONE); *)
  \\ strip_assign \\ still_safe
  (* stack_max *)
  \\ max_is ‘MAX smax (lsize + sstack)’
  \\ cheat
end
QED

val _ = export_theory();
