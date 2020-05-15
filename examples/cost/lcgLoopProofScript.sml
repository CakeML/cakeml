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

Theorem max_right_absorb_3:
  c ≤ b ⇒
  (MAX (MAX a b) c = MAX a b)
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

(* blocks is a Block representation of a char? list of length ≤ l and with timestamps strictly bounded by tsb *)
val repchar_list_def = Define`
  (* cons *)
  (repchar_list (Block ts _ [Number i; rest]) (l:num) (tsb:num) ⇔
    (0 ≤ i ∧ i ≤ 255 ∧ (* i reps a character *)
    ts < tsb ∧
    l > 0 ∧ repchar_list rest (l-1) tsb)) ∧
  (* nil *)
  (repchar_list (Block _ _ []) (l:num) tsb ⇔ T) ∧
  (* everything else *)
  (repchar_list _ _ _ ⇔ F)`

val repchar_list_ind = theorem "repchar_list_ind";

Theorem size_of_repchar_list:
  ∀blocks l tsb.
  repchar_list blocks l tsb ⇒
  ∀sl refs seen n a b.
  (size_of sl [blocks] refs seen = (n,a,b)) ⇒
  n ≤ 3*l
Proof
  ho_match_mp_tac repchar_list_ind>>
  rw[repchar_list_def]>>
  fs[size_of_def]>>
  rpt (pairarg_tac>>fs[])>>
  every_case_tac>>fs[]>>
  first_x_assum drule
  >-
    rw[]>>
  qpat_x_assum`~small_num _ _` mp_tac>>
  simp[small_num_def]>>rw[]>>
  intLib.ARITH_TAC
QED

(* TODO move to sptree *)
Theorem wf_fromList:
  ∀ls.
  sptree$wf (fromList ls)
Proof
  simp[fromList_def]>>
  qmatch_goalsub_abbrev_tac`(s,t)`>>
  `wf t` by fs[Abbr`t`]>>
  strip_tac>>
  pop_assum mp_tac>>
  qid_spec_tac`s`>>
  qid_spec_tac`t`>>
  qid_spec_tac`ls`>>
  Induct>>rw[]>>
  first_x_assum match_mp_tac>>
  simp[wf_insert]
QED

Theorem fromList_11[simp]:
  (sptree$fromList xs = fromList ys) <=>
  (xs = ys)
Proof
  DEP_REWRITE_TAC [spt_eq_thm]>>
  simp[wf_fromList]>>
  rw[EQ_IMP_THM]>>
  fs[lookup_fromList]>>
  match_mp_tac LIST_EQ>>
  CONJ_ASM1_TAC
  >- (
    CCONTR_TAC>>fs[]>>
    `LENGTH xs < LENGTH ys ∨ LENGTH ys < LENGTH xs` by fs[]
    >-
      (first_x_assum(qspec_then`LENGTH xs` assume_tac)>>fs[])>>
    (first_x_assum(qspec_then`LENGTH ys` assume_tac)>>fs[]))>>
  rw[]>>first_x_assum(qspec_then`x` mp_tac)>>fs[]
QED

Theorem repchar_list_more:
  ∀block x tsb y.
  repchar_list block x tsb ∧ x ≤ y ⇒
  repchar_list block y tsb
Proof
  ho_match_mp_tac repchar_list_ind>>
  rw[repchar_list_def]
QED

Theorem repchar_list_more_tsb:
  ∀block x tsb tsb'.
  repchar_list block x tsb ∧ tsb ≤ tsb' ⇒
  repchar_list block x tsb'
Proof
  ho_match_mp_tac repchar_list_ind>>
  rw[repchar_list_def]
QED

Theorem repchar_list_more_seen:
  ∀block l ts refs seen a1 b1 c1.
  repchar_list block l ts ∧
  (size_of lims [block] refs seen = (a1,b1,c1)) ⇒
  (size_of lims [block] refs (insert ts () seen) = (a1,b1,insert ts () c1))
Proof
  ho_match_mp_tac repchar_list_ind>>rw[repchar_list_def]
  >- (
    fs[size_of_def,lookup_insert]>>
    IF_CASES_TAC>>fs[]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[]>>
    first_x_assum drule>>
    `insert ts' () (insert ts () seen) = insert ts () (insert ts' () seen)` by
      simp[insert_swap]>>
    simp[])>>
  fs[size_of_def]
QED

Theorem n2l_acc_evaluate:
  ∀k n s block sstack lsize sm acc ls l ts.
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (s.stack_max = SOME sm) ∧
  (s.locals = fromList [block ; Number (&n)]) ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (lookup_n2l_acc s.stack_frame_sizes = SOME lsize) ∧
  (sm < s.limits.stack_limit) ∧
  (lsize + sstack  < s.limits.stack_limit) ∧
  s.safe_for_space ∧
  s.limits.arch_64_bit ∧
  small_num T (&n) ∧
  n < 10**k ∧ k > 0 ∧
  repchar_list block l ts ∧
  (size_of_heap s + 3 * k ≤ s.limits.heap_limit) ∧
  (lookup_hex s.code = SOME(1,hex_body)) ∧
  (lookup_n2l_acc s.code = SOME(2, n2l_acc_body)) ∧
  (* 2*k < s.clock ∧ -- n2l_acc is guaranteed to work if sufficient clock is provided *)
  (s.tstamps = SOME ts) ∧
  1 < s.limits.length_limit
  ⇒
  ∃res lcls0 lsz0 clk0 ts0 pkheap0 stk.
  (evaluate (n2l_acc_body,s) =
   (SOME res, s with <| locals := lcls0;
                              locals_size := lsz0;
                              stack_max := SOME (MAX sm (lsize + sstack));
                              clock := clk0;
                              space := 0;
                              tstamps := SOME ts0;
                              peak_heap_length := pkheap0;
                              stack := stk
                              |>)) ∧
    clk0 ≤ s.clock ∧
   (
    (res = (Rerr(Rabort Rtimeout_error))) ∨
    (∃vv. (res = Rval vv) ∧ repchar_list vv (k + l) ts0 ∧ (stk = s.stack))
   )
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
    qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _` >>
    subgoal ‘safe’
    THENL
    [(Q.UNABBREV_TAC ‘safe’
       \\ fs[coeff_bounds_def,libTheory.the_def,size_of_Number_head,
             small_num_def,data_safe_def,size_of_heap_def,stack_to_vs_def,
             size_of_def,size_of_stack_def]
       \\ rpt (pairarg_tac \\ fs []) \\ rveq
       \\ pop_assum mp_tac
       \\ eval_goalsub_tac ``size_of _ _`` \\ simp []
       \\ fs [size_of_Number_head,small_num_def]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
  fun max_is t =
    qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _` >>
    subgoal ‘max0 = SOME (^(Term t))’
    THENL
    [(Q.UNABBREV_TAC ‘max0’ \\ fs [small_num_def,size_of_stack_def]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
in
  completeInduct_on`k`>>
  rw[n2l_acc_body_def]>>
  simp[ to_shallow_thm, to_shallow_def, initial_state_def ]>>
  (*  2 :≡ (Const 10,[],NONE); *)
  strip_assign >>
  (*  3 :≡ (Less,[1; 2],SOME ⦕ 0; 1; 2 ⦖); *)
  strip_assign >> simp[] >>
  max_is `MAX sm (lsize + sstack)` >>
  still_safe
  >- (
    strip_tac>>
    drule size_of_repchar_list>>
    disch_then drule>>
    pop_assum mp_tac>>
    eval_goalsub_tac``size_of _ _ ``>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    DEP_REWRITE_TAC [size_of_Number_head]>>
    simp[small_num_def])>>
  rename1`state_peak_heap_length_fupd (K pkheap) _`>>
  (* if_var 3 *)
  make_if >>
  Cases_on` n < 10` >> simp[]
  >- (
    (* call_hex (4,⦕ 0 ⦖) [1] NONE *)
    simp[Once bind_def]>>
    simp [ call_def      , find_code_def  , push_env_def
     , get_vars_def  , call_env_def   , dec_clock_def
     , cut_env_def   , domain_def     , data_safe_def
     , EMPTY_SUBSET  , get_var_def    , size_of_stack_def
     , lookup_def    , domain_IS_SOME , frame_lookup
     , code_lookup   , lookup_def     , domain_IS_SOME
     , lookup_insert , flush_state_def
     , size_of_stack_frame_def] >>
    IF_CASES_TAC >- (
      simp[state_component_equality,PULL_EXISTS,GSYM size_of_stack_def]>>
      simp[MAX_DEF,libTheory.the_def])>>
    qmatch_goalsub_abbrev_tac`(hex_body,ss)`>>
    `size_of_stack ss.stack = SOME (lsize+sstack)` by
      (simp[Abbr`ss`,size_of_stack_def,size_of_stack_frame_def]>>
      simp[GSYM size_of_stack_def])>>
    `(ss.locals_size = SOME 0)` by fs[Abbr`ss`]>>
    drule hex_evaluate>>
    disch_then drule>>
    disch_then (qspec_then`n` mp_tac)>> simp[]>>
    impl_tac >- (
      simp[Abbr`ss`]>>
      EVAL_TAC)>>
    simp[]>> disch_then kall_tac>>
    simp[pop_env_def,Abbr`ss`,set_var_def]>>
    fs[size_of_stack_frame_def,size_of_stack_def]>>rw[]>>
    max_is `MAX sm (lsize + sstack)` >>
    still_safe
    >- (
      eval_goalsub_tac``size_of _ _ ``>>
      simp[Once data_to_word_gcProofTheory.size_of_cons]>>
      pairarg_tac>>fs[]>>
      pairarg_tac>>fs[]>>rw[]
      >- (
        DEP_REWRITE_TAC[ max_right_absorb_3]>>simp[]>>
        intLib.ARITH_TAC)>>
      DEP_ONCE_REWRITE_TAC[ max_right_absorb_2]>>simp[]>>
      intLib.ARITH_TAC) >>
    (* makespace 3 ⦕ 0; 4 ⦖ *)
    strip_makespace >>
    simp[GSYM size_of_stack_def]>>
    (* 5 :≡ (Cons 0,[4; 0],NONE) *)
    strip_assign>>
    (* return 5 *)
    simp[return_def]>>
    eval_goalsub_tac``sptree$lookup _ _``>> simp[] >>
    simp[flush_state_def]>>
    reverse (rw [state_component_equality])>- (
      simp[repchar_list_def]>>
      drule repchar_list_more_tsb>>
      disch_then(qspec_then`ts+1` mp_tac)>>simp[]>>
      strip_tac>>
      drule repchar_list_more>>
      disch_then match_mp_tac>>
      simp[])>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    rveq>>fs[]>>
    drule size_of_repchar_list>>
    disch_then drule>>
    qpat_x_assum`_ + size_of_heap _ ≤ _` mp_tac>>
    eval_goalsub_tac``size_of_heap _``>>
    simp[]>>
    eval_goalsub_tac``toListA _ _``>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    DEP_REWRITE_TAC [size_of_Number_head]>>
    simp[small_num_def])>>
  (*  8 :≡ (Const 10,[],NONE); *)
  strip_assign>>
  (* preliminaries *)
  `small_num T (&(n MOD 10))` by
    (fs[small_num_def]>> intLib.ARITH_TAC)>>
  `small_num T (&(n DIV 10))` by
    (fs[small_num_def]>> intLib.ARITH_TAC)>>
  `small_num T (&n − &(10 * (n DIV 10)))` by
    (fs[small_num_def]>> intLib.ARITH_TAC)>>
  `small_num T &(n MOD 10 + 48)` by
    (fs[small_num_def]>> intLib.ARITH_TAC)>>
  (* 9 :≡ (Mod,[1; 8],SOME ⦕ 0; 1; 8 ⦖); *)
  strip_assign>>simp[]>>
  fs[small_num_def]>>
  max_is `MAX sm (lsize + sstack)` >>
  still_safe
  >- (
    eval_goalsub_tac``size_of _ _ ``>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>rw[]>>
    qpat_x_assum`size_of _ (Number _ :: _) _ _ = _` mp_tac>>
    DEP_REWRITE_TAC [size_of_Number_head]>>
    simp[small_num_def]>>
    strip_tac>>fs[])>>
  (* call_hex (10,⦕ 0; 1 ⦖) [9] NONE; *)
  simp[Once bind_def]>>
  simp [ call_def      , find_code_def  , push_env_def
   , get_vars_def  , call_env_def   , dec_clock_def
   , cut_env_def   , domain_def     , data_safe_def
   , EMPTY_SUBSET  , get_var_def    , size_of_stack_def
   , lookup_def    , domain_IS_SOME , frame_lookup
   , code_lookup   , lookup_def     , domain_IS_SOME
   , lookup_insert , flush_state_def
   , size_of_stack_frame_def] >>
   qmatch_goalsub_abbrev_tac`(hex_body,ss)`>>
  `size_of_stack ss.stack = SOME (lsize+sstack)` by
    (simp[Abbr`ss`,size_of_stack_def,size_of_stack_frame_def]>>
    simp[GSYM size_of_stack_def])>>
  `(ss.locals_size = SOME 0)` by fs[Abbr`ss`]>>
  drule hex_evaluate>>
  disch_then drule>>
  disch_then (qspec_then`n MOD 10` mp_tac)>> simp[]>>
  impl_tac >- (
    simp[Abbr`ss`]>>
    EVAL_TAC)>>
  simp[]>> disch_then kall_tac>>
  simp[pop_env_def,Abbr`ss`,set_var_def]>>
  fs[size_of_stack_def,size_of_stack_frame_def]>>
  max_is `MAX sm (lsize + sstack)` >>
  still_safe
  >- (
    eval_goalsub_tac``size_of _ _ ``>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>rw[]
    >- (
      DEP_REWRITE_TAC[ max_right_absorb_3]>>simp[]>>
      rw[Once MAX_DEF]>>
      intLib.ARITH_TAC)>>
    DEP_ONCE_REWRITE_TAC[ max_right_absorb_2]>>simp[]>>
    rw[Once MAX_DEF]>>
    rw[Once MAX_DEF]>>
    intLib.ARITH_TAC)>>
  (* makespace 3 ⦕ 0; 1; 10 ⦖; *)
  strip_makespace >>
  simp[GSYM size_of_stack_def]>>
  (* 11 :≡ (Cons 0,[10; 0],NONE); *)
  strip_assign >>
  (* 14 :≡ (Const 10,[],NONE); *)
  strip_assign >>
  (* 15 :≡ (Div,[1; 14],SOME ⦕ 1; 11; 14 ⦖); *)
  strip_assign >>
  simp[]>>
  max_is `MAX sm (lsize + sstack)` >>
  still_safe >- (
    eval_goalsub_tac``size_of _ _ ``>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    strip_tac>>rveq>>
    qpat_x_assum`size_of _ (Number _ :: _) _ _ = (n1,refs1,seen1)` mp_tac>>
    DEP_REWRITE_TAC [size_of_Number_head]>>
    simp[small_num_def]>>
    strip_tac>>rveq>>
    fs[]>>rveq>>
    qpat_x_assum`size_of _ (Block _ _ _ :: _) _ _ = (_,_,_)` mp_tac>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    simp[size_of_def]>>simp[small_num_def]>>
    IF_CASES_TAC >- simp[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    strip_tac>>rveq>>
    pop_assum mp_tac>>
    drule repchar_list_more_seen>>
    disch_then drule>>
    simp[])>>
  rename1`state_peak_heap_length_fupd (K pkheap1) _`>>
  (* tailcall_n2l_acc [11; 15] *)
  ASM_REWRITE_TAC [ tailcall_def , find_code_def
                  , get_vars_def , get_var_def
                  , lookup_def   , timeout_def
                  , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup] >>
  `k ≥ 2` by
    (Cases_on`k`>>fs[ADD1]>>
    Cases_on`n'`>>fs[])>>
  simp[GSYM n2l_acc_body_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def ]
  \\ simp [] >>
  still_safe
  >- (
    strip_tac>>
    DEP_ONCE_REWRITE_TAC[max_right_absorb_3]>>simp[]>>
    rw[Once MAX_DEF]>>
    rw[Once MAX_DEF]>>
    rfs [frame_lookup])>>
  qmatch_goalsub_abbrev_tac`(n2l_acc_body,ss)`>>
  first_x_assum(qspec_then`k-1` mp_tac)>>simp[]>>
  disch_then(qspecl_then[`n DIV 10`, `ss`] mp_tac)>>
  simp[PULL_EXISTS,Abbr`ss`]>>
  fs[GSYM size_of_stack_def]>>
  disch_then(qspec_then`l+1` mp_tac)>>simp[]>>
  impl_tac >- (
    simp[GSYM n2l_acc_body_def]>>
    rfs[frame_lookup]>>
    CONJ_TAC>- (
      DEP_REWRITE_TAC[DIV_LT_X]>>simp[]>>
      `10 * 10 **(k-1) = 10**k` by
        (Cases_on`k`>>simp[EXP])>>
      simp[])>>
    CONJ_TAC>- (
      simp[repchar_list_def]>>
      CONJ_TAC >- intLib.ARITH_TAC>>
      drule repchar_list_more_tsb>>
      disch_then match_mp_tac>>
      simp[])>>
    fs[size_of_heap_def,stack_to_vs_def]>>
    eval_goalsub_tac ``sptree$toList _ ``>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    DEP_REWRITE_TAC [size_of_Number_head]>>
    simp[size_of_def,small_num_def]>>
    rpt(pairarg_tac>>fs[])>>
    rw[]>>fs[]>>
    pop_assum mp_tac>>
    simp[]>>
    eval_goalsub_tac ``size_of _ _ _ _``>>
    DEP_REWRITE_TAC [size_of_Number_head]>>
    simp[size_of_def,small_num_def]>>
    pairarg_tac>>fs[]>>
    rw[]>>fs[]>>
    qpat_x_assum` _ = (n2, _, _)` mp_tac>>rw[]>>
    drule repchar_list_more_seen>>
    disch_then drule>>
    simp[])>>
  strip_tac>>simp[]>>
  rw [state_component_equality]>>
  rfs[frame_lookup]
end
QED

val lcgLoop_body = ``lookup_lcgLoop (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

val lcgLoop_body_def = Define`
  lcgLoop_body = ^lcgLoop_body`

Theorem data_safe_lcgLoop_code[local]:
  ∀s sstack smax y.
  s.safe_for_space ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (s.code = fromAList lcgLoop_data_prog) ∧
  (s.stack_max = SOME smax) ∧
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (* (sstack + N1 (* 5 *) < s.limits.stack_limit) ∧ *)
  (sstack + lsize + 5 < s.limits.stack_limit) ∧
  (smax < s.limits.stack_limit) ∧
  s.limits.arch_64_bit ∧
  (size_of_heap s + 60 (* N3 *) ≤ s.limits.heap_limit) ∧
  (s.locals = fromList [Number (&x); Number (&m); Number (&c); Number (&a)]) ∧
  (* N1, N2, N3 are TODO constants to fill *)
  (s.tstamps = SOME ts) ∧
  (1 < s.limits.length_limit) ∧
  (coeff_bounds a c m ∧ x < m ) ∧
  (lookup_lcgLoop s.code = SOME (4,lcgLoop_body))
  ⇒ data_safe (evaluate (lcgLoop_body, s))
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
  measureInduct_on `^s.clock`>>
  simp[lcgLoop_body_def]
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
  \\ qmatch_goalsub_abbrev_tac ‘bind _ n2l_rest’
  \\ simp [bind_def,call_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ eval_goalsub_tac “dataSem$cut_env _ _” \\ fs []
  \\ IF_CASES_TAC >- fs [data_safe_def,frame_lookup,size_of_stack_def,
                         call_env_def,push_env_def,dec_clock_def,
                         size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
  \\ simp[call_env_def,push_env_def,dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac ‘state_safe_for_space_fupd (K safe) _’
  \\ qmatch_goalsub_abbrev_tac ‘state_stack_max_fupd (K max0) _’
  \\ ‘(max0 = SOME (MAX smax (lsize + sstack + 5))) ∧ safe’ by
    (UNABBREV_ALL_TAC
     \\ fs [data_safe_def,frame_lookup,size_of_stack_def,
            call_env_def,push_env_def,dec_clock_def,
            size_of_stack_frame_def,MAX_DEF,libTheory.the_def])
  \\ ASM_REWRITE_TAC [] \\ ntac 4 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,s0)’
  \\ qspecl_then [‘19’,‘(a * x + c) MOD m’,‘s0’] mp_tac n2l_acc_evaluate
  \\ UNABBREV_ALL_TAC \\ simp []
  \\ fs [data_safe_def,frame_lookup,size_of_stack_def,
            call_env_def,push_env_def,dec_clock_def,
            size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
  \\ disch_then (qspec_then ‘1’ mp_tac)
  \\ impl_tac >- (
      simp[code_lookup,frame_lookup,
          data_to_wordTheory.Compare_location_eq,
          data_to_wordTheory.Compare1_location_eq,
          data_to_wordTheory.LongDiv_location_eq,
          data_to_wordTheory.LongDiv1_location_eq] >>
      simp[GSYM hex_body_def, GSYM n2l_acc_body_def, repchar_list_def]>>
      CONJ_TAC >-
        simp[integerTheory.INT_ADD,integerTheory.INT_MOD]>>
      CONJ_ASM1_TAC>- (
       match_mp_tac (GEN_ALL small_num_bound_imp_1)
       \\ qexists_tac`m`>>simp[])>>
      CONJ_TAC >-
        fs[small_num_def]>>
      CONJ_TAC >- (
        simp[size_of_heap_def]>>
        eval_goalsub_tac``size_of _ _ _``>>
        simp[Once data_to_word_gcProofTheory.size_of_cons]>>
        DEP_REWRITE_TAC [size_of_Number_head]>>
        simp[size_of_def]>>
        simp[small_num_def]>>
        fs[size_of_heap_def,stack_to_vs_def]>>
        rpt(pairarg_tac>>fs[])>>
        pop_assum mp_tac >>
        eval_goalsub_tac``sptree$toList _``>>
        PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
        DEP_ONCE_REWRITE_TAC [size_of_Number_head_append]>>
        simp[]>>rw[]>>
        pop_assum mp_tac>>rw[])>>
      (* clock? *)
      cheat )>>
  simp[integerTheory.INT_ADD,integerTheory.INT_MOD,GSYM n2l_acc_body_def]>>
  strip_tac>>simp[]>>
  simp[pop_env_def,set_var_def]
  \\ cheat
end
QED

Theorem data_safe_lcgLoop_code_shallow[local] =
  data_safe_lcgLoop_code |> simp_rule [lcgLoop_body_def,to_shallow_thm,to_shallow_def];

Theorem evaluate_mono:
  (dataSem$evaluate (prog,s) = (res,s')) ⇒
  subspt s.code s'.code ∧
  s'.clock ≤ s.clock
Proof
  cheat
QED

Theorem call_env_consts[simp]:
  ((dataSem$call_env a b s).clock = s.clock) ∧
  ((dataSem$call_env a b s).code = s.code)
Proof
  rw[call_env_def]
QED

Theorem data_safe_lcgLoop_code_abort:
  ∀s x m c a.
  (s.locals = fromList [x;m;c;a]) ∧
  (lookup_lcgLoop s.code = SOME (4,lcgLoop_body))
  ⇒ ∃s' e. evaluate (lcgLoop_body, s) = (SOME (Rerr e),s')
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
  val drop_state     =
      (
      TRY(qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe0)  _` >> pop_assum kall_tac) >>
      rename1 `state_safe_for_space_fupd (K safe)  _` >>
      TRY(qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap0)  _` >> pop_assum kall_tac) >>
      rename1 `state_peak_heap_length_fupd (K pkheap)  _` >>
      TRY (qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0)  _`>> pop_assum kall_tac)>>
      rename1 `state_stack_max_fupd (K max)  _`
      )
in
  measureInduct_on `^s.clock` >>
  rw[]>>
  simp[lcgLoop_body_def]
  \\ fs [to_shallow_thm
         , to_shallow_def
         , coeff_bounds_def
         , initial_state_def ]
  \\ rw [] \\ fs [fromList_def]>>
  strip_assign >>
  every_case_tac>>simp[]>>
  drop_state>>
  strip_assign >>
  drop_state>>
  every_case_tac>>simp[]>>
  rename1 `state_safe_for_space_fupd (K safe)  _` >>
  rename1 `state_peak_heap_length_fupd (K pkheap)  _` >>
  rename1 `state_stack_max_fupd (K max)  _`>>
  strip_assign >>
  every_case_tac>>simp[]>>
  drop_state>>
  (* if_var 11 ... *)
  qmatch_goalsub_abbrev_tac `bind _ if_rest_ass`
  \\ simp [bind_def]
  \\ make_if
  \\ IF_CASES_TAC
  >- (
    strip_assign \\ drop_state>>
    simp[raise_def]>>
    every_case_tac>>simp[])>>
  IF_CASES_TAC >> simp[]>>
  strip_assign>>
  IF_CASES_TAC>> simp[]>>
  drop_state>>
  (* move 14 13 *)
  simp [move_def,lookup_def,set_var_def]
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``>>
  (* Exit if *)
  Q.UNABBREV_TAC ‘if_rest_ass’ >>
  (* make_space 3 ... *)
  strip_makespace
  \\ simp[]
  \\ drop_state >>
  (* 17 :≡ (Cons 0,[],NONE) *)
  (* 18 :≡ (Const 10,[],NONE) *)
  (* 19 :≡ (Cons 0,[18; 17],NONE); *)
  strip_assign>> drop_state>>
  strip_assign>> drop_state>>
  strip_assign>> drop_state>>
  every_case_tac>> simp[check_lim_def] >>
  (
    simp[bind_def,call_def]>>
    every_case_tac>>simp[]>>
    simp[tailcall_def,set_var_def]>>
    rename1` _ _ _ tt.code tt.stack_frame_sizes`>>
    `(subspt s.code tt.code) ∧ (tt.clock ≤ s.clock)` by
      (imp_res_tac evaluate_mono>>
      fs[dec_clock_def]>>
      qpat_x_assum`pop_env _ = _` mp_tac>>
      qpat_x_assum`pop_env _ = _` mp_tac>>
      simp[pop_env_def]>>every_case_tac>>simp[state_component_equality]>>
      fs[set_var_def]>>
      metis_tac[subspt_trans])>>
    every_case_tac>>simp[]>>
    pop_assum mp_tac>>fs[find_code_def]>>
    fs[subspt_lookup]>>
    first_x_assum drule>>
    rw[]>>
    simp[call_env_def,dec_clock_def]>>
    qmatch_goalsub_abbrev_tac`(lcgLoop_body,ttt)`>>
    first_x_assum(qspec_then`ttt` mp_tac)>>
    impl_tac >-
      fs[Abbr`ttt`]>>
    simp[to_shallow_thm]>>
    simp[Abbr`ttt`]>>
    rename1`fromList qq`>>
    `∃aa bb cc dd. qq = [aa;bb;cc;dd]` by (
      fs[get_vars_def]>>
      qpat_x_assum`_ = SOME qq` mp_tac>>
      rpt(pop_assum kall_tac)>>
      every_case_tac>>simp[]>>
      rw[])>>
    simp[fromList_def]>>
    disch_then(qspecl_then[`aa`,`bb`,`cc`,`dd`] assume_tac)>>fs[])
end
QED

Theorem data_safe_lcgLoop_code_abort_shallow[local] =
  data_safe_lcgLoop_code_abort |> simp_rule [lcgLoop_body_def,to_shallow_thm,to_shallow_def];

val lcgLoop_x64_conf = (rand o rator o lhs o concl) lcgLoop_thm

Theorem data_safe_lcgLoop:
  ∀ffi.
  backend_config_ok ^lcgLoop_x64_conf
  ⇒ is_safe_for_space ffi ^lcgLoop_x64_conf ^lcgLoop (1000,1000)
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
 strip_tac \\ strip_tac
 \\ irule IMP_is_safe_for_space_alt \\ fs []
 \\ conj_tac >- EVAL_TAC
 \\ assume_tac lcgLoop_thm
 \\ asm_exists_tac \\ fs []
 \\ assume_tac lcgLoop_to_data_updated_thm
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
 \\ ntac 10
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
 (* This avoid last unabbrev *)
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ ntac 6 strip_assign
 \\ ntac 11
    (open_tailcall
     \\ ntac 4 strip_assign
     \\ make_if
     \\ ntac 2 strip_assign)
  \\ open_tailcall
  \\ ntac 4 strip_assign
  \\ make_if
  \\ Q.UNABBREV_TAC `rest_call`
  \\ strip_assign
  \\ make_tailcall
  \\ ntac 10
     (strip_makespace
      \\ ntac 6 strip_assign
      \\ make_tailcall)
  (* Place the arguments *)
  \\ ntac 4 strip_assign
  \\ ho_match_mp_tac data_safe_bind_some
  \\ open_call
  \\ qmatch_goalsub_abbrev_tac `f (state_locals_fupd _ _)`
  \\ qmatch_goalsub_abbrev_tac `f s`
  \\ `∃s' e'. f s = (SOME (Rerr e'),s')`
     by (UNABBREV_ALL_TAC
     \\ ho_match_mp_tac data_safe_lcgLoop_code_abort_shallow
     \\ rw [code_lookup] >>
     EVAL_TAC>>
     metis_tac[])
  \\ `data_safe (f s)` suffices_by
     (rw [] \\ rfs [] \\ EVERY_CASE_TAC \\ fs [])
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac (GEN_ALL data_safe_lcgLoop_code_shallow)
  \\ rw [lookup_def,lookup_fromList,code_lookup]
  \\ EVAL_TAC
  \\ rw []
QED

val _ = export_theory();
