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
  IF_CASES_TAC >- (
    simp[state_component_equality,PULL_EXISTS,GSYM size_of_stack_def]>>
    simp[MAX_DEF,libTheory.the_def])>>
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

val max_depth_AnyArith = ``max_depth lcgLoop_config.word_conf.stack_frame_size AnyArith_call_tree`` |> (SIMP_CONV std_ss [lcgLoop_config_def] THENC EVAL);

Theorem pull_some:
  (if P then SOME x else SOME y) = SOME (if P then x else y)
Proof
  rw[]
QED

Theorem bignum_size_mono:
  ∀x y.
    x ≤ y ⇒
    bignum_size s.limits.arch_64_bit (&x) ≤ bignum_size s.limits.arch_64_bit (&y)
Proof
  fs[bignum_size_def]
  \\ qspec_tac (‘s.limits.arch_64_bit’,‘k’)
  \\ ho_match_mp_tac bignum_digits_ind
  \\ rw [] \\ once_rewrite_tac [bignum_digits_def]
  \\ fs [] \\ rw [] \\ fs []
  \\ first_x_assum match_mp_tac
  \\ match_mp_tac DIV_LE_MONOTONE \\ fs []
QED

Theorem n2l_acc_evaluate_bignum:
  ∀k n s block sstack lsize sm acc ls l ts.
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (s.stack_max = SOME sm) ∧
  (s.locals = fromList [block ; Number (&n)]) ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (lookup_n2l_acc s.stack_frame_sizes = SOME lsize) ∧
  s.safe_for_space ∧
  n < 10**k ∧ k > 0 ∧
  repchar_list block l ts ∧
  (lookup_hex s.code = SOME(1,hex_body)) ∧
  (lookup_n2l_acc s.code = SOME(2, n2l_acc_body)) ∧
  (s.tstamps = SOME ts) ∧
  (* size assumptions *)
  (lsize + sstack + 9 < s.limits.stack_limit) ∧
  1 < s.limits.length_limit ∧
  bignum_size s.limits.arch_64_bit (&n) + 3 < 2 ** s.limits.length_limit ∧
  size_of_heap s + 2 * bignum_size s.limits.arch_64_bit (&n) + 3 * k + 4 ≤ s.limits.heap_limit ∧
  sm < s.limits.stack_limit
  ⇒
  ∃res lcls0 lsz0 sm0 clk0 ts0 pkheap0 stk.
  (evaluate (n2l_acc_body,s) =
   (SOME res, s with <| locals := lcls0;
                              locals_size := lsz0;
                              stack_max := SOME sm0;
                              clock := clk0;
                              space := 0;
                              tstamps := SOME ts0;
                              peak_heap_length := pkheap0;
                              stack := stk
                              |>)) ∧
    clk0 ≤ s.clock ∧
   (
    (res = (Rerr(Rabort Rtimeout_error))) ∨
    (∃vv. (res = Rval vv) ∧ repchar_list vv (k + l) ts0 ∧ (stk = s.stack) ∧
       sm0 ≤ (MAX sm (lsize + sstack + 9))
    )
   )
Proof
let
  val code_lookup   = mk_code_lookup
                        `fromAList lcgLoop_data_prog`
                        lcgLoop_data_code_def
  val frame_lookup   = mk_frame_lookup
                        `lcgLoop_config.word_conf.stack_frame_size`
                        lcgLoop_config_def
    (* usual strip_assign but do not expand locals *)
  val strip_assign  = qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
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
  val still_safe    =
    qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _` >>
    subgoal ‘safe’
    THENL
    [(Q.UNABBREV_TAC ‘safe’
       \\ fs[coeff_bounds_def,libTheory.the_def,size_of_Number_head,
             data_safe_def,size_of_heap_def,stack_to_vs_def,
             size_of_def,size_of_stack_def]
       \\ rpt (pairarg_tac \\ fs []) \\ rveq
       \\ pop_assum mp_tac
       \\ TRY(eval_goalsub_tac ``size_of _ _`` \\ simp [])
       \\ fs [size_of_Number_head]),
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
  simp[ to_shallow_thm, to_shallow_def, initial_state_def ]
  \\ qabbrev_tac `szh = (size_of s.limits (FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global) s.refs LN)`
  \\ `?nn xx yy. szh = (nn,xx,yy)` by
    (PairCases_on`szh`>>fs[])

  \\ qabbrev_tac `szacc = size_of s.limits [block] xx yy `
  \\ `∃bn xn yn. szacc = (bn,xn,yn)` by
    (PairCases_on`szacc`>>fs[])>>
  fs[]>>
  (* these must be true *)
  ‘bignum_size s.limits.arch_64_bit 10 < 3’ by
    (simp [bignum_size_def,Once bignum_digits_def] \\ rw []
     \\ simp [bignum_size_def,Once bignum_digits_def] \\ rw []) >>
  `bignum_size s.limits.arch_64_bit (&n) +
   bignum_size s.limits.arch_64_bit 10 ≤ 2 ** s.limits.length_limit` by fs [] >>
  `bn + nn + 2 * bignum_size s.limits.arch_64_bit (&n) + 2 * bignum_size s.limits.arch_64_bit 10 +
    (if small_num s.limits.arch_64_bit (&n) then 0 else bignum_size s.limits.arch_64_bit (&n)) +
    3 * k ≤ s.limits.heap_limit` by
      (fs[size_of_heap_def,stack_to_vs_def] >>
      qpat_x_assum `_ ≤ s.limits.heap_limit` mp_tac>>
      simp[]>>
      eval_goalsub_tac``sptree$toList _``>>
      simp[Once size_of_def]>>
      rpt(pairarg_tac>>fs[])>>
      qpat_x_assum`_ = (n1, _, _)` mp_tac>>
      simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
      strip_tac>>fs[]>>rveq>>fs[markerTheory.Abbrev_def]>>
      `bignum_size s.limits.arch_64_bit 10 = 2` by
        (simp[bignum_size_def,Once bignum_digits_def]>>
        rw[]>>
        EVAL_TAC)>>
      simp[]>>
      rw[])>>
  `bn + nn + 2 * bignum_size s.limits.arch_64_bit (&n) + 2 * bignum_size s.limits.arch_64_bit 10 +
    (if small_num s.limits.arch_64_bit (&n) then 0 else bignum_size s.limits.arch_64_bit (&n)) + 3
    ≤ s.limits.heap_limit` by
      (rw[]>>fs[])>>
  qpat_x_assum`3*k + _  ≤ _` kall_tac>>
  `bn + nn + bignum_size s.limits.arch_64_bit (&n) + 3 ≤ s.limits.heap_limit` by
    (pop_assum mp_tac>>rw[]>>fs[])>>
  `bn + nn +
   (2 * bignum_size s.limits.arch_64_bit (&n) + 2 * bignum_size s.limits.arch_64_bit 10) +
   (if small_num s.limits.arch_64_bit (&n) then 0 else bignum_size s.limits.arch_64_bit (&n))
     ≤ s.limits.heap_limit` by
    (rw[]>>fs [])>>
  `1 < s.limits.length_limit` by fs [] >>
  (*  2 :≡ (Const 10,[],NONE); *)
  strip_assign >>
  (*  3 :≡ (Less,[1; 2],SOME ⦕ 0; 1; 2 ⦖); *)
  strip_assign >> simp[] >>
  still_safe
  >- (
    simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
    simp[space_consumed_def]>>
    rpt (pairarg_tac>>fs[])>>
    strip_tac>>rveq>>fs[]>>
    rw[]>>simp[]>>
    fs[small_num_def]
    )>>
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
    >- ( simp[MAX_DEF])>>
    (* makespace 3 ⦕ 0; 4 ⦖ *)
    strip_makespace >>
    simp[GSYM size_of_stack_def]>>
    (* 5 :≡ (Cons 0,[4; 0],NONE) *)
    strip_assign>>
    (* return 5 *)
    simp[return_def]>>
    simp[flush_state_def,check_lim_def]>>
    still_safe >- (
      simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
      strip_tac>>rveq>>fs[]>>
      simp[arch_size_def]>>
      rw[])>>
    rw[state_component_equality] >>
    simp[repchar_list_def]>>
    drule repchar_list_more_tsb>>
    disch_then(qspec_then`ts+1` mp_tac)>>simp[]>>
    strip_tac>>
    drule repchar_list_more>>
    disch_then match_mp_tac>>
    simp[])>>
  (*  8 :≡ (Const 10,[],NONE); *)
  strip_assign>>
  simp[libTheory.the_def]>>

  (* preliminaries *)
  `small_num s.limits.arch_64_bit 10` by
    (fs[small_num_def])>>
  `small_num s.limits.arch_64_bit (&(n MOD 10 + 48))` by
    (fs[small_num_def]>>
    rw[]>>intLib.ARITH_TAC)>>

  (* 9 :≡ (Mod,[1; 8],SOME ⦕ 0; 1; 8 ⦖); *)
  (* strip_assign but don't expand locals>> *)
  strip_assign>>
  simp[max_depth_AnyArith,space_consumed_def,stack_to_vs_def]>>
  still_safe
  >- (
    simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
    strip_tac>>rveq>>fs[]>>
    rw[]>>simp[]>>
    fs[small_num_def]>>
    rw[]>>simp[libTheory.the_def]) >>
  rename1`state_peak_heap_length_fupd (K pkheap1) _`>>
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
  IF_CASES_TAC >- (
    simp[state_component_equality,PULL_EXISTS,GSYM size_of_stack_def]>>
    rw[]>>simp[libTheory.the_def]>>
    fs[MAX_DEF])>>
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
  still_safe
  >- (
    rw[]>>simp[libTheory.the_def]>>
    simp[MAX_DEF])>>
  (* makespace 3 ⦕ 0; 1; 10 ⦖; *)
  (* strip_makespace >> *)
  qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ Q.UNABBREV_TAC `rest_mkspc` >>
  simp[]>>
  (* 11 :≡ (Cons 0,[10; 0],NONE); *)
  strip_assign >>
  (* 14 :≡ (Const 10,[],NONE); *)
  strip_assign >>
  (* 15 :≡ (Div,[1; 14],SOME ⦕ 1; 11; 14 ⦖); *)
  strip_assign >>
  simp[max_depth_AnyArith]>>
  still_safe >- (
    simp[size_of_def]>>
    simp[Once data_to_word_gcProofTheory.size_of_cons]>>
    simp[size_of_def]>>
    rpt (pairarg_tac>>fs[])>>
    strip_tac>>rveq>>fs[]>>
    simp[space_consumed_def]>>
    reverse CONJ_TAC >-
      (rw[]>>simp[libTheory.the_def])>>
    rpt (pairarg_tac>>fs[])>>
    rveq>>fs[]>>
    CONJ_TAC >- (
      CONJ_TAC >-
        (simp[arch_size_def]>>rw[])>>
      qpat_x_assum`_ = (n',_,_)` mp_tac>>
      eval_goalsub_tac``sptree$toList _``>>
      simp[size_of_def]>>
      rpt (pairarg_tac>>fs[])>>
      qpat_x_assum`size_of _ (Number _ :: _) _ _ = _` mp_tac>>
      simp[Once data_to_word_gcProofTheory.size_of_cons]>>
      rpt (pairarg_tac>>fs[])>>
      strip_tac>>strip_tac>>rveq>>fs[]>>
      fs[size_of_def]>>rveq>>fs[]>>
      fs[markerTheory.Abbrev_def]>>rveq>>
      rw[]>>simp[])>>
    qpat_x_assum` _ = (n2,_,_)` mp_tac>>
    IF_CASES_TAC>-
      (strip_tac>>fs[]>>rveq>>simp[]>>
      rw[]>>simp[]>>
      fs[])>>
    strip_tac>>fs[]>>rveq>>simp[]>>
    fs[markerTheory.Abbrev_def]>>
    qpat_x_assum`_ = size_of _ _ _ _` (assume_tac o SYM)>>
    drule repchar_list_more_seen>>
    disch_then drule>>
    simp[]>> strip_tac>>
    rveq>>simp[]>>
    rw[]>>simp[]>>
    fs[])>>
  rename1`state_peak_heap_length_fupd (K pkheap2) _`>>
  eval_goalsub_tac``insert 15 _ _``>>
  (* tailcall_n2l_acc [11; 15] *)
  ASM_REWRITE_TAC [ tailcall_def , find_code_def
                  , get_vars_def , get_var_def
                  , lookup_def   , timeout_def
                  , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup] >>
  IF_CASES_TAC >- (
    simp[state_component_equality,PULL_EXISTS,GSYM size_of_stack_def]>>
    rw[]>>simp[])>>
  `k ≥ 2` by
    (Cases_on`k`>>fs[ADD1]>>
    Cases_on`n'`>>fs[])>>
  simp[GSYM n2l_acc_body_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def ]
  \\ simp [] >>
  still_safe
  >- (
    strip_tac>>
    rw[]>> simp[]>>
    simp[MAX_DEF,libTheory.the_def])>>
  qmatch_goalsub_abbrev_tac`(n2l_acc_body,ss)`>>
  first_x_assum(qspec_then`k-1` mp_tac)>>simp[]>>
  disch_then(qspecl_then[`n DIV 10`, `ss`] mp_tac)>>
  simp[PULL_EXISTS,Abbr`ss`]>>
  fs[GSYM size_of_stack_def]>>
  disch_then(qspec_then`l+1` mp_tac)>>
  simp[pull_some]>>
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
      CONJ_TAC >- (
        qpat_x_assum`PP` kall_tac>>
        intLib.ARITH_TAC)>>
      drule repchar_list_more_tsb>>
      disch_then match_mp_tac>>
      simp[])>>
    `bignum_size s.limits.arch_64_bit (&(n DIV 10)) ≤
     bignum_size s.limits.arch_64_bit (&n)` by
      (match_mp_tac bignum_size_mono>>
      intLib.ARITH_TAC)>>
    CONJ_TAC >- (simp[])>>
    CONJ_TAC>- (
      simp[size_of_heap_def,stack_to_vs_def]>>
      eval_goalsub_tac``sptree$toList _``>>
      simp[size_of_def]>>
      rpt (pairarg_tac>>fs[])>>rveq>>fs[]>>
      qpat_x_assum`_ = (n1, _, _)` mp_tac>>
      simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
      strip_tac>>fs[]>>rveq>>fs[markerTheory.Abbrev_def]>>
      qpat_x_assum`_=(n2,_,_)` mp_tac>>
      drule repchar_list_more_seen>>
      qpat_x_assum`(bn,_,_) = _` (assume_tac o SYM)>>
      disch_then drule>>
      simp[]>> strip_tac>>
      rveq>>fs[]>>
      `bignum_size s.limits.arch_64_bit 10 = 2` by
        (simp[bignum_size_def,Once bignum_digits_def]>>
        rw[]>>
        EVAL_TAC)>>
      fs[]>>
      IF_CASES_TAC>>strip_tac>>fs[]>>rveq>>fs[]
      >- (
        qpat_x_assum`bn + (3 *k + _) ≤ _` mp_tac>>
        rw[]>>simp[]>>
        qpat_x_assum`small_num _ _` mp_tac>>
        qpat_x_assum`¬small_num _ _` mp_tac>>
        simp[small_num_def]>>
        rw[]>>
        intLib.ARITH_TAC)>>
      qpat_x_assum`bn + (3 *k + _) ≤ _` mp_tac>>
      rw[]>>simp[]>>
      qpat_x_assum`small_num _ _` mp_tac>>
      qpat_x_assum`¬small_num _ _` mp_tac>>
      simp[small_num_def]>>
      rw[]>>
      intLib.ARITH_TAC)>>
    rw[]>>simp[])>>
  strip_tac>>simp[]>>
  rw [state_component_equality]>>
  rfs[frame_lookup]>>
  pop_assum mp_tac>>rw[]>>simp[]
end
QED

Definition approx_of_heap_def[simp]:
  approx_of_heap s = approx_of s.limits (stack_to_vs s) s.refs
End

val put_char_body = ``lookup_put_char (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

val put_char_body_def = Define`
    put_char_body = ^put_char_body`

Definition no_ptrs_list_def:
  (no_ptrs_list [] = T) ∧
  (no_ptrs_list [RefPtr p] = F) ∧
  (no_ptrs_list [Block ts tag l] = no_ptrs_list l) ∧
  (no_ptrs_list [x] = T) ∧
  (no_ptrs_list (v::vs) = no_ptrs_list [v] ∧ no_ptrs_list vs)
Termination
  WF_REL_TAC `(inv_image (measure v1_size) I)`
End

Theorem no_ptrs_list_approx_of:
  ∀vs l refs.
  no_ptrs_list vs
  ⇒ (approx_of l vs refs = approx_of l vs (insert p x refs))
Proof
  ho_match_mp_tac no_ptrs_list_ind>>
  rw[no_ptrs_list_def]
  >-
    simp[dataPropsTheory.approx_of_def]
  >- (
    Cases_on`vs`
    >- (
      simp[Once dataPropsTheory.approx_of_def]>>
      simp[Once dataPropsTheory.approx_of_def] )>>
    fs[]>>
    PURE_REWRITE_TAC[Once dataPropsTheory.approx_of_def,SimpLHS]>>
    PURE_REWRITE_TAC[Once dataPropsTheory.approx_of_def,SimpRHS]>>
    metis_tac[])
  >- simp[dataPropsTheory.approx_of_def]
  >- simp[dataPropsTheory.approx_of_def]
  >- simp[dataPropsTheory.approx_of_def] >>
  PURE_REWRITE_TAC[Once dataPropsTheory.approx_of_def,SimpLHS]>>
  PURE_REWRITE_TAC[Once dataPropsTheory.approx_of_def,SimpRHS]>>
  metis_tac[]
QED

Definition no_ptrs_refs_def:
  no_ptrs_refs refs =
    ∀x l. (sptree$lookup x refs = SOME (ValueArray l)) ⇒ no_ptrs_list l
End

Theorem delete_insert:
  p ≠ r ∧ wf refs ⇒
  (delete r (insert p x refs) = insert p x (delete r refs))
Proof
  rw[]>>
  DEP_REWRITE_TAC[spt_eq_thm]>>
  fs[wf_delete,wf_insert]>>
  simp[lookup_delete,lookup_insert]>>
  rw[]>>simp[]
QED

Theorem closed_ptrs_list_cons:
  ∀x.
  closed_ptrs_list (x::xs) refs ⇔
  closed_ptrs_list [x] refs ∧
  closed_ptrs_list xs refs
Proof
  Cases>>rw[closed_ptrs_list_def]
QED

Theorem closed_ptrs_list_append:
  ∀xs ys.
  closed_ptrs_list (xs++ys) refs ⇔
  closed_ptrs_list xs refs ∧
  closed_ptrs_list ys refs
Proof
  Induct>>rw[closed_ptrs_list_def]>>
  simp[Once closed_ptrs_list_cons]>>
  simp[Once closed_ptrs_list_cons,SimpRHS]>>
  metis_tac[]
QED

Theorem closed_ptrs_approx_of:
  ∀l vs refs.
  closed_ptrs_list vs refs ∧ no_ptrs_refs refs ∧ (lookup p refs = NONE) ∧
  wf refs
  ⇒ (approx_of l vs refs = approx_of l vs (insert p x refs))
Proof
  ho_match_mp_tac dataPropsTheory.approx_of_ind>>
  rw[dataPropsTheory.approx_of_def]>>
  fs[closed_ptrs_def]
  >- (
    qpat_x_assum`_ _ refs` mp_tac>>
    simp[Once closed_ptrs_list_cons])
  >- (
    fs[closed_ptrs_list_def]>>
    TOP_CASE_TAC>>fs[]>>
    simp[lookup_insert]>>
    IF_CASES_TAC>>fs[]>>
    TOP_CASE_TAC>>simp[]>>
    simp[delete_insert]>>
    match_mp_tac no_ptrs_list_approx_of>>
    fs[no_ptrs_refs_def]>>
    metis_tac[])>>
  fs[closed_ptrs_list_def]
QED

Theorem no_ptrs_list_imp_closed_ptrs_list:
  ∀l refs.
  no_ptrs_list l ⇒ closed_ptrs_list l refs
Proof
  ho_match_mp_tac no_ptrs_list_ind>>
  rw[closed_ptrs_list_def,no_ptrs_list_def]>>
  fs[]>>
  simp[closed_ptrs_list_cons]
QED

Theorem no_ptrs_refs_imp_closed_ptrs_refs:
  no_ptrs_refs refs ⇒ closed_ptrs_refs refs
Proof
  rw[no_ptrs_refs_def,closed_ptrs_refs_def]>>
  first_x_assum drule>>
  metis_tac[no_ptrs_list_imp_closed_ptrs_list]
QED

Theorem no_ptrs_imp_closed_ptrs:
  closed_ptrs_list ls refs ∧
  no_ptrs_refs refs ⇒
  closed_ptrs ls refs
Proof
  rw[closed_ptrs_def]>>
  metis_tac[no_ptrs_refs_imp_closed_ptrs_refs]
QED

Theorem put_char_evaluate:
  ∀s sstack lsize sm ts i.
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (s.stack_max = SOME sm) ∧
  (wf s.refs) ∧
  (closed_ptrs_list (stack_to_vs s) s.refs) ∧
  no_ptrs_refs s.refs ∧
  0 ≤ i ∧ i ≤ 255 ∧
  (s.locals = fromList [Number i]) ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (sm < s.limits.stack_limit) ∧
  (size_of_heap s + 5 ≤ s.limits.heap_limit) ∧
  (lsize + sstack + 6 < s.limits.stack_limit) ∧
  s.safe_for_space ∧
  s.limits.arch_64_bit ∧
  (s.code = fromAList lcgLoop_data_prog) ∧
  (s.tstamps = SOME ts) ∧
  1 < s.limits.length_limit
  ⇒
  ∃res clk0 lcls0 lsz0 refs0 ts0 pkheap0 stk spc0 ffi0.
  (evaluate (put_char_body,s) =
   (SOME res, s with <|locals := lcls0;
                       stack_max := SOME (MAX sm (lsize + sstack + spc0));
                       locals_size := lsz0;
                       stack := stk;
                       space := 0;
                       ffi := ffi0;
                       tstamps := SOME ts0;
                       peak_heap_length := pkheap0;
                       clock := clk0;
                       refs := refs0 |>)) ∧
    subspt s.refs refs0 ∧
    clk0 ≤ s.clock ∧
   (
    (∃e. res = (Rerr(Rabort e)))
    ∨
    ((∃vv. (res = Rval vv)) ∧
     (stk = s.stack) ∧ (spc0 = 6) ∧ (ts < ts0) ∧
     closed_ptrs_list (stack_to_vs s) refs0 ∧ wf refs0 ∧ no_ptrs_refs refs0 ∧
     (size_of_heap (s with refs := refs0) = size_of_heap s) ∧
     (approx_of_heap (s with refs := refs0) = approx_of_heap s)))
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
  rw [put_char_body_def]
  \\ simp [to_shallow_thm, to_shallow_def]
  (* Preliminaries *)
  \\ qpat_x_assum ‘s.locals = _’ (ASSUME_TAC o EVAL_RULE)
  \\ ‘small_num s.limits.arch_64_bit i’ by
     (fs [small_num_def] \\ intLib.ARITH_TAC)
  \\ `1 < 2 ** s.limits.length_limit`
     by (irule LESS_TRANS \\ qexists_tac `s.limits.length_limit` \\ fs [])
  (* makespace 3 *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ ASM_REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ still_safe
  \\ rename1`state_peak_heap_length_fupd (K pkheap1) _`
  (* 1 :≡ (Cons 0,[],NONE); *)
  (* 2 :≡ (Cons 0,[],NONE); *)
  (* 3 :≡ (Cons 0,[0; 2],NONE); *)
  (* 5 :≡ (Const 0,[],NONE); *)
  (* 6 :≡ (Const 0,[],NONE); *)
  (* 7 :≡ (Const 0,[],NONE); *)
  \\ ntac 6 strip_assign
  \\ still_safe
  \\ max_is ‘MAX sm (lsize + sstack)’
  (* call_ListLength (8,⦕ 3; 5; 6 ⦖) [3; 7] NONE; *)
  \\ qmatch_goalsub_abbrev_tac ‘bind _ print_char_rest’
  \\ simp [bind_def,call_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ eval_goalsub_tac “dataSem$cut_env _ _” \\ fs []
  \\ IF_CASES_TAC
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘5’ \\ rw [])
  \\ simp [to_shallow_thm, to_shallow_def]
  \\ simp [call_env_def,push_env_def,dec_clock_def]
  \\ simp [frame_lookup]
  \\ still_safe
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  \\ max_is ‘MAX sm (lsize + sstack + 5)’
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  (* Inside ListLength *)
  (* 2 :≡ (TagLenEq 0 0,[0],NONE); *)
  \\ strip_assign
  (* if_var 2 (F) *)
  \\ make_if
  (* 4 :≡ (Const 1,[],NONE); *)
  (* 5 :≡ (El,[0; 4],NONE); *)
  (* 6 :≡ (Const 1,[],NONE); *)
  (* 7 :≡ (Add,[6; 1],SOME ⦕ 1; 5; 6 ⦖); *)
  \\ ntac 4 strip_assign
  \\ still_safe
  >- (fs [size_of_Number_head]
      \\ qmatch_asmsub_abbrev_tac ‘size_of _ (_::ll)’
      \\ Cases_on ‘ll’ \\ fs [size_of_def,lookup_def]
      \\ rfs [] \\ rw []
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ pop_assum mp_tac \\ IF_CASES_TAC
      \\ fs [])
  \\ max_is ‘MAX sm (lsize + sstack + 5)’
  \\ rename1`state_peak_heap_length_fupd (K pkheap2) _`
  (* tailcall_ListLength [5; 7] *)
  \\ simp [bind_def,tailcall_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ IF_CASES_TAC
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def,
          flush_state_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘5’ \\ rw [])
  \\ simp [to_shallow_thm, to_shallow_def]
  \\ simp [call_env_def,push_env_def,dec_clock_def]
  \\ simp [frame_lookup]
  \\ still_safe
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  \\ max_is ‘MAX sm (lsize + sstack + 5)’
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  (* Inside ListLength (X2)*)
  (* 2 :≡ (TagLenEq 0 0,[0],NONE); *)
  \\ strip_assign
  (* if_var 2 (T) *)
  \\ make_if
  (* Exit ListLength  *)
  \\ still_safe
  \\ max_is ‘MAX sm (lsize + sstack + 5)’
  \\ Q.UNABBREV_TAC ‘print_char_rest’
  (* 9 :≡ (RefByte T,[8; 6],SOME ⦕ 3; 5; 6; 8 ⦖); *)
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ still_safe
  >- (rfs [size_of_Number_head,small_num_def]
      \\ qmatch_asmsub_abbrev_tac ‘size_of _ (_::ll)’
      \\ Cases_on ‘ll’ \\ fs [size_of_def,lookup_def]
      \\ rfs [small_num_def] \\ rw []
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ pop_assum mp_tac \\ IF_CASES_TAC
      \\ fs [])
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
  (* call_FromListByte (10,LN) [3; 5; 9] NONE; *)
  \\ qmatch_goalsub_abbrev_tac ‘bind _ print_char_rest’
  \\ simp [bind_def,call_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ eval_goalsub_tac “dataSem$cut_env _ _” \\ fs []
  \\ rename1`state_peak_heap_length_fupd (K pkheap22) _`
  \\ IF_CASES_TAC
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
      \\ ONCE_REWRITE_TAC [state_component_equality]
      \\ EVAL_TAC \\ rw []
      \\ qexists_tac ‘6’ \\ rw []
      \\ rw[subspt_lookup,lookup_insert,Abbr ‘p1’]
      \\ rw[] >> fs[])
  \\ simp [to_shallow_thm, to_shallow_def]
  \\ simp [call_env_def,push_env_def,dec_clock_def]
  \\ simp [frame_lookup]
  \\ still_safe
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  (* Inside FromListByte *)
  (* 3 :≡ (TagLenEq 0 0,[0],NONE); *)
  \\ strip_assign
  (* if_var 3 (F) *)
  \\ make_if
  \\ still_safe
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  (* 5 :≡ (Const 0,[],NONE); *)
  (* 6 :≡ (El,[0; 5],NONE); *)
  \\ ntac 2 strip_assign
  \\ still_safe
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  (* 7 :≡ (UpdateByte,[2; 1; 6],NONE); *)
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. i = &w2n (w:word8)`
  \\ `pred` by
    (UNABBREV_ALL_TAC
     \\ qexists_tac ‘n2w (integer$Num i)’
     \\ fs [w2n_n2w] \\ Cases_on ‘i’ \\ fs [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ still_safe
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  (* 8 :≡ (Const 1,[],NONE); *)
  (* 9 :≡ (El,[0; 8],NONE); *)
  (* 10 :≡ (Const 1,[],NONE); *)
  (* 11 :≡ (Add,[10; 1],SOME ⦕ 1; 2; 9; 10 ⦖); *)
  \\ ntac 4 strip_assign
  \\ still_safe
  >- (rfs [size_of_Number_head,small_num_def,insert_shadow]
      \\ qmatch_goalsub_abbrev_tac ‘size_of _ (a ++ b)’
      \\ `closed_ptrs (a ++ b) s.refs` by
        metis_tac[no_ptrs_imp_closed_ptrs,closed_ptrs_APPEND]
      \\ disch_then (mp_then Any drule_all size_of_insert)
      \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
      \\ disch_then (qspec_then ‘x’ assume_tac)
      \\ rveq \\ rfs [] \\ fs []
      \\ Q.UNABBREV_TAC ‘x’
      \\ fs [] \\ rveq \\ fs [small_num_def])
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  \\ rename1`state_peak_heap_length_fupd (K pkheap3) _`
  (* tailcall_FromListByte [9; 11; 2] *)
  \\ simp [bind_def,tailcall_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ IF_CASES_TAC
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def,
          flush_state_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘6’ \\ rw []
      \\ rw[subspt_lookup,lookup_insert,Abbr ‘p1’]
      \\ rw[] >> fs[]
     )
  \\ simp [to_shallow_thm, to_shallow_def]
  \\ simp [call_env_def,push_env_def,dec_clock_def]
  \\ simp [frame_lookup]
  \\ still_safe
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF])
  (* Inside FromListByte (X2) *)
  (* 3 :≡ (TagLenEq 0 0,[0],NONE); *)
  \\ strip_assign
  (* if_var 3 (T) *)
  \\ make_if
  (* Exit FromListByte *)
  \\ still_safe
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  \\ Q.UNABBREV_TAC ‘print_char_rest’
  (* 12 :≡ (Const 0,[],NONE); *)
  (* 17 :≡ (Const 0,[],NONE); *)
  \\ ntac 2 strip_assign
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  >- (rw [MAX_DEF])
  (* 18 :≡ (RefByte F,[17; 12],SOME ⦕ 10; 12; 17 ⦖); *)
  \\ simp [insert_shadow]
  \\ strip_assign
  \\ Q.ABBREV_TAC `pred = ∃w. 0 = w2n (w:word8)`
  \\ `pred` by (UNABBREV_ALL_TAC \\ qexists_tac `n2w 0` \\ rw [])
  \\ fs [] \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  \\ qmatch_goalsub_abbrev_tac `insert p2 _ (insert p1 _ s.refs)`
  \\ simp []
  \\ `p1 ≠ p2` by
     (rw [Abbr `p2`,least_from_def]
     >- (CCONTR_TAC \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     >- (numLib.LEAST_ELIM_TAC \\ rw []
        \\ Cases_on `ptr = p1` \\ fs []
        \\ qexists_tac `ptr` \\ fs [])
     \\ numLib.LEAST_ELIM_TAC \\ rw [] \\ fs []
     \\ mp_then Any assume_tac IN_INFINITE_NOT_FINITE INFINITE_NUM_UNIV
     \\ rw [] \\ pop_assum (qspec_then `domain (insert p1 ARB s.refs)` assume_tac)
     \\ fs [FINITE_domain,domain_lookup] \\ Cases_on `lookup x (insert p1 ARB s.refs)`
     \\ fs [] \\ qexists_tac `x` \\ Cases_on `x = p1` \\ fs [lookup_insert])
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac ‘insert p1 (ByteArray T x0)’
  \\ `lookup p2 (insert p1 (ByteArray T x0) s.refs) = NONE` by
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
  \\ `wf (insert p1 (ByteArray T x0) s.refs)` by fs [wf_insert]
  \\ still_safe
  >- (rfs [size_of_Number_head,small_num_def,insert_shadow]
      \\ qmatch_goalsub_abbrev_tac ‘size_of _ (a ++ b)’
      \\ `closed_ptrs (a ++ b) s.refs` by
        metis_tac[no_ptrs_imp_closed_ptrs, closed_ptrs_APPEND]
      \\ disch_then (mp_then Any drule_all size_of_insert)
      \\ qmatch_asmsub_abbrev_tac `insert p1 x s.refs`
      \\ disch_then (qspec_then ‘x’ assume_tac)
      \\ rveq \\ rfs [] \\ fs []
      \\ Q.UNABBREV_TAC ‘x’
      \\ fs [] \\ rveq \\ fs [small_num_def]
      \\ rw [Abbr‘x0’])
  \\ max_is `MAX sm (lsize + sstack + 6)`
  >- rw [MAX_DEF]
  (* 19 :≡ (FFI "put_char",[10; 18],SOME ⦕ 10; 18 ⦖); *)
  \\ strip_assign
  \\ reverse (Cases_on `call_FFI s.ffi "put_char" x0 []` \\ fs [])
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘6’ \\ rw []
      \\ rw[subspt_lookup,lookup_insert]
      \\ rw[]
      \\ fs[lookup_insert] \\ rfs[])
  (* 20 :≡ (Cons 0,[],NONE); *)
  \\ strip_assign
  \\ simp [return_def,lookup_def,flush_state_def]
  \\ rw [state_component_equality,MAX_DEF,wf_insert]
  >- (fs [size_of_heap_def,stack_to_vs_def]
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ pop_assum (ASSUME_TAC o EVAL_RULE)
      \\ rfs [size_of_Number_head,small_num_def]
      \\ qmatch_asmsub_abbrev_tac ‘size_of _ ll’
      \\ Cases_on ‘ll’
      >- (fs [size_of_def] \\ rveq \\ fs [arch_size_def]
          \\ fs [lookup_delete,lookup_insert] \\ rfs [Abbr‘x0’]
          \\ rveq \\ fs [])
      \\ fs [size_of_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ qpat_x_assum ‘size_of _ _ s.refs _ = _’ (mp_then Any mp_tac size_of_insert)
      \\ disch_then (qspecl_then [‘p1’,‘ByteArray T x0’] mp_tac)
      \\ impl_tac >- (
        UNABBREV_ALL_TAC \\
        fs [closed_ptrs_APPEND] \\
        metis_tac[no_ptrs_imp_closed_ptrs,closed_ptrs_APPEND])
      \\ disch_then (mp_then Any mp_tac size_of_insert)
      \\ disch_then (qspecl_then [‘p2’,‘ByteArray F []’] mp_tac)
      \\ impl_tac
      >- (fs [] \\ irule closed_ptrs_insert \\ fs []
          \\ conj_tac
          >- (
            irule closed_ptrs_refs_insert \\
            fs[] \\
            metis_tac[no_ptrs_refs_imp_closed_ptrs_refs])
          \\ UNABBREV_ALL_TAC \\ fs [closed_ptrs_APPEND]
          \\  metis_tac[no_ptrs_imp_closed_ptrs,closed_ptrs_APPEND])
      \\ rw [] \\ fs [] \\ rveq \\ fs []
      \\ rw [arch_size_def] \\ fs [lookup_insert,lookup_delete] \\ rfs []
      \\ rveq \\ fs []
      \\ rfs [Abbr‘x0’] \\ rveq \\ fs [])
  >- (rw[subspt_lookup,lookup_insert]
      \\ rw[]
      \\ fs[lookup_insert] \\ rfs[])
  >- (simp [insert_shadow]
      \\ metis_tac [closed_ptrs_insert,
                    closed_ptrs_refs_insert,
                    closed_ptrs_def, no_ptrs_imp_closed_ptrs])
  >-  (fs[no_ptrs_refs_def]>>
      rw[lookup_insert]>>
      metis_tac[])
  >- (fs [insert_shadow] \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ fs [stack_to_vs_def]
      \\ qmatch_asmsub_abbrev_tac ‘size_of _ ll’
      \\ first_x_assum (mp_then Any mp_tac size_of_insert)
      \\ disch_then (qspecl_then [‘p1’,‘ByteArray T x0’] mp_tac)
      \\ impl_tac >- (
        UNABBREV_ALL_TAC \\ fs [closed_ptrs_APPEND]
        \\ metis_tac[no_ptrs_imp_closed_ptrs,closed_ptrs_APPEND])
      \\ disch_then (mp_then Any mp_tac size_of_insert)
      \\ disch_then (qspecl_then [‘p2’,‘ByteArray F l’] mp_tac)
      \\ impl_tac
      >- (fs [wf_insert,Abbr‘ll’]
          \\ metis_tac [closed_ptrs_insert,
                        closed_ptrs_refs_insert,
                        closed_ptrs_def, no_ptrs_imp_closed_ptrs])
      \\ rw [] \\ rfs [] \\ rveq \\ fs [])
  \\ fs [dataPropsTheory.approx_of_def,stack_to_vs_def]
  \\ eval_goalsub_tac “sptree$toList _”
  \\ qmatch_asmsub_abbrev_tac ‘closed_ptrs_list (a ++ b ++ c)’
  \\ ‘closed_ptrs_list (b ++ c) s.refs’ by
    metis_tac[closed_ptrs_APPEND,no_ptrs_imp_closed_ptrs,closed_ptrs_def]
  \\ map_every Q.UNABBREV_TAC [‘a’,‘b’,‘c’]
  \\ rw [dataPropsTheory.approx_of_def,stack_to_vs_def]
  \\ qmatch_goalsub_abbrev_tac ‘approx_of _ (_::ll)’
  \\ Cases_on ‘ll’ \\ fs [dataPropsTheory.approx_of_def,closed_ptrs_APPEND]
  \\ fs [insert_shadow]
  \\ drule_then (qspecl_then [‘ByteArray T x0’,‘p1’,‘s.limits’] mp_tac) closed_ptrs_approx_of \\ simp[]
  \\ fs [] \\ rw []
  \\ qpat_x_assum ‘lookup p2 (insert p1 (ByteArray T x0) s.refs) = _’
                  (mp_then Any mp_tac closed_ptrs_approx_of)
  \\ disch_then (qspecl_then [‘ByteArray F l’,‘s.limits’,‘h::t’] mp_tac)
  \\ impl_tac
  >- (
    simp[]>> CONJ_TAC>- (
      metis_tac [closed_ptrs_insert,
                 closed_ptrs_refs_insert,
                 closed_ptrs_def, no_ptrs_imp_closed_ptrs,closed_ptrs_APPEND])>>
    fs[no_ptrs_refs_def]>>rw[lookup_insert]>>
    metis_tac[])
  \\ rw []
end
QED

val put_chars_body = ``lookup_put_chars (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

val put_chars_body_def = Define`
    put_chars_body = ^put_chars_body`

Theorem closed_ptrs_repchar_list:
  ∀block l ts refs.
   repchar_list block l ts
   ⇒ closed_ptrs_list [block] refs
Proof
  ho_match_mp_tac repchar_list_ind \\ rw [closed_ptrs_list_def]
  \\ fs [repchar_list_def]
QED

Theorem put_chars_evaluate:
  ∀s block sstack lsize sm l ts.
  (size_of_stack s.stack = SOME sstack) ∧
  (wf s.refs) ∧
  (closed_ptrs_list (stack_to_vs s) s.refs) ∧
  no_ptrs_refs s.refs ∧
  (s.locals_size = SOME lsize) ∧
  (s.stack_max = SOME sm) ∧
  (s.locals = fromList [block]) ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (* (lookup_put_chars s.stack_frame_sizes = SOME lsize) ∧ *)
  (sm < s.limits.stack_limit) ∧
  (approx_of_heap s + 5 ≤ s.limits.heap_limit) ∧
  (lsize + sstack + 12 < s.limits.stack_limit) ∧
  (sstack + 15 < s.limits.stack_limit) ∧
  s.safe_for_space ∧
  s.limits.arch_64_bit ∧
  repchar_list block l ts ∧
  (s.code = fromAList lcgLoop_data_prog) ∧
  (s.tstamps = SOME ts) ∧
  1 < s.limits.length_limit
  ⇒
  ∃res clk0 lcls0 lsz0 refs0 ts0 pkheap0 stk spc0 ffi0 sps0.
  (evaluate (put_chars_body,s) =
   (SOME res, s with <|locals := lcls0;
                       stack_max := SOME (MAX sm (lsize + sstack + spc0));
                       locals_size := lsz0;
                       stack := stk;
                       space := sps0;
                       ffi := ffi0;
                       tstamps := SOME ts0;
                       peak_heap_length := pkheap0;
                       clock := clk0;
                       refs := refs0 |>)) ∧
    subspt s.refs refs0 ∧
    clk0 ≤ s.clock ∧
   (
    (∃e. res = (Rerr(Rabort e)))
    ∨
    ((∃vv. (res = Rval vv)) ∧
     (stk = s.stack) ∧ (spc0 ≤ 6) ∧
     closed_ptrs_list (stack_to_vs s) refs0 ∧ wf refs0 ∧
     no_ptrs_refs refs0 ∧
     (size_of_heap (s with refs := refs0) = size_of_heap s)))
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
  completeInduct_on`l`
  \\ rw [put_chars_body_def]
  \\ simp [to_shallow_thm, to_shallow_def]
  (* Preliminaries *)
  \\ Cases_on ‘block’ \\ fs [repchar_list_def]
  \\ rename1 ‘Block ts0 n btl’
  \\ qpat_x_assum ‘s.locals = _’ (ASSUME_TAC o EVAL_RULE)
  (* 2 :≡ (TagLenEq 0 0,[0],NONE); *)
  \\ strip_assign
  (* if_var 2 *)
  \\ make_if
  \\ Cases_on ‘btl’ \\ fs [repchar_list_def]
  >- (strip_assign \\ simp [return_def]
      \\ eval_goalsub_tac “sptree$lookup 3 _”
      \\ simp [flush_state_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘0’ \\ fs []
      \\ fs [stack_to_vs_def])
  \\ rename1 ‘Block _ _ (chr0::str0)’
  \\ Cases_on ‘chr0’ \\ fs [repchar_list_def]
  \\ Cases_on ‘str0’ \\ fs [repchar_list_def]
  \\ Cases_on ‘t’    \\ fs [repchar_list_def]
  \\ rename1 ‘Block _ _ [_;str0]’
  (* 4 :≡ (Const 0,[],NONE); *)
  (* 5 :≡ (El,[0; 4],NONE); *)
  (* 6 :≡ (Const 1,[],NONE); *)
  (* 7 :≡ (El,[0; 6],NONE); *)
  \\ ntac 4 strip_assign
  \\ qmatch_goalsub_abbrev_tac ‘bind _ put_chars_rest’
  (* call_put_char *)
  \\ simp [bind_def,call_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ eval_goalsub_tac “dataSem$cut_env _ _” \\ fs []
  \\ IF_CASES_TAC
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘6’ \\ rw [])
  \\ simp[call_env_def,push_env_def,dec_clock_def]
  \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _`
  \\ ‘safe’ by
    (Q.UNABBREV_TAC ‘safe’
     \\ fs[coeff_bounds_def,libTheory.the_def,size_of_Number_head,
           small_num_def,data_safe_def,size_of_heap_def,stack_to_vs_def,
           size_of_def,size_of_stack_def,frame_lookup,size_of_stack_frame_def]
     \\ rw [MAX_DEF])
  \\ max_is ‘MAX sm (lsize + sstack + 6)’
  >- (simp [size_of_stack_frame_def,libTheory.the_def]
      \\ rw [MAX_DEF,frame_lookup,libTheory.the_def])
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,s0)’
  \\ qspecl_then [‘s0’] mp_tac put_char_evaluate
  \\ fs [frame_lookup]
  \\ Q.UNABBREV_TAC ‘s0’ \\ simp []
  \\ fs [size_of_stack_def,size_of_stack_frame_def]
  \\ impl_tac
  >- (rw []
      >- (
          fs [stack_to_vs_def,closed_ptrs_list_append,extract_stack_def]
          \\ eval_goalsub_tac “sptree$toList _”
          \\ eval_goalsub_tac “sptree$toList _”
          \\ fs [closed_ptrs_list_def]
          \\ irule closed_ptrs_repchar_list
          \\ asm_exists_tac \\ simp [])
      \\ fs [size_of_heap_def,stack_to_vs_def,extract_stack_def]
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ drule dataPropsTheory.size_of_approx_of
      \\ rw []
      \\ irule LESS_EQ_TRANS
      \\ qmatch_asmsub_abbrev_tac ‘approx_of _ ll _ + 5’
      \\ qexists_tac ‘approx_of s.limits ll  s.refs + 5’
      \\ fs []
      \\ irule LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
      \\ Q.UNABBREV_TAC ‘ll’
      \\ eval_goalsub_tac “sptree$toList _”
      \\ eval_goalsub_tac “sptree$toList _”
      \\ eval_goalsub_tac “sptree$toList _”
      \\ fs [dataPropsTheory.approx_of_def]
      \\ ‘small_num s.limits.arch_64_bit i’
        by (rw [small_num_def] \\ intLib.ARITH_TAC)
      \\ fs [] \\ rfs []
      \\ qmatch_goalsub_abbrev_tac ‘approx_of _ (_::ll)’
      \\ Cases_on ‘ll’
      \\ fs [dataPropsTheory.approx_of_def])
  \\ rw [put_char_body_def] \\ simp []
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘spc0 + 6’ \\ rw [])
  \\ simp[call_env_def,push_env_def,dec_clock_def,pop_env_def,set_var_def]
  \\ Q.UNABBREV_TAC ‘put_chars_rest’
  (* tailcall_put_chars [7] *)
  \\ simp [bind_def,tailcall_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ IF_CASES_TAC
  >- (fs [data_safe_def,frame_lookup,size_of_stack_def,
          call_env_def,push_env_def,dec_clock_def,
          size_of_stack_frame_def,MAX_DEF,libTheory.the_def,
          flush_state_def]
      \\ rw [state_component_equality]
      \\ qexists_tac ‘12’ \\ rw [])
  \\ simp [call_env_def,push_env_def,dec_clock_def]
  \\ simp [frame_lookup]
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max1) _`
  \\ ‘max1 = SOME (MAX sm (sstack + lsize + 12))’
    by (Q.UNABBREV_TAC ‘max1’
        \\ fs [small_num_def,size_of_stack_def]
        \\ rw [MAX_DEF])
  \\ ASM_REWRITE_TAC []
  \\ ntac 2 (pop_assum kall_tac)
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,s0)’
  \\ first_x_assum (qspec_then ‘l - 1’ mp_tac)
  \\ fs []
  \\ disch_then (qspecl_then [‘s0’] mp_tac)
  \\ fs [frame_lookup]
  \\ disch_then (qspecl_then [‘str0’,‘sstack’,‘3’,‘THE s0.stack_max’, ‘ts0'’] mp_tac)
  \\ impl_tac
  >- (Q.UNABBREV_TAC ‘s0’ \\ simp []
      \\ fs [size_of_stack_def,size_of_stack_frame_def]
      \\ rw []
      >- (
          fs [stack_to_vs_def,closed_ptrs_list_append]
          \\ eval_goalsub_tac “sptree$toList _”
          \\ irule closed_ptrs_repchar_list
          \\ metis_tac [])
      >- (fs [size_of_heap_def,stack_to_vs_def]
          \\ rpt (pairarg_tac \\ fs []) \\ rveq
          \\ qpat_x_assum ‘approx_of _ _ _ = approx_of _ _ _’ (ASSUME_TAC o EVAL_RULE)
          \\ ‘small_num s.limits.arch_64_bit i’
            by (rw [small_num_def] \\ intLib.ARITH_TAC)
          \\ fs []
          \\ eval_goalsub_tac “sptree$toList _”
          \\ fs [dataPropsTheory.approx_of_def]
          \\ irule LESS_EQ_TRANS
          \\ qmatch_asmsub_abbrev_tac ‘approx_of _ ll _ + 5’
          \\ qexists_tac ‘approx_of s.limits ll  s.refs + 5’
          \\ fs []
          \\ Q.UNABBREV_TAC ‘ll’
          \\ eval_goalsub_tac “sptree$toList _”
          \\ fs [dataPropsTheory.approx_of_def]
          \\ qmatch_goalsub_abbrev_tac ‘approx_of _ (_::ll)’
          \\ Cases_on ‘ll’
          \\ fs [dataPropsTheory.approx_of_def])
      >- (rw [libTheory.the_def,MAX_DEF])
      \\ irule repchar_list_more_tsb
      \\ qexists_tac ‘ts’ \\ fs [])
  \\ rw [put_chars_body_def] \\ simp []
  >- (
    fs[state_component_equality,Abbr`s0`]>>
    cheat) >>
  fs[state_component_equality,Abbr`s0`]>>
  cheat
end
QED

val lcgLoop_body = ``lookup_lcgLoop (fromAList lcgLoop_data_prog)``
           |> (REWRITE_CONV [lcgLoop_data_code_def] THENC EVAL)
           |> concl |> rhs |> rand |> rand

val lcgLoop_body_def = Define`
  lcgLoop_body = ^lcgLoop_body`

Theorem data_safe_lcgLoop_code[local]:
  ∀s sstack smax lsize y x ts.
  s.safe_for_space ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (s.code = fromAList lcgLoop_data_prog) ∧
  (s.stack_max = SOME smax) ∧
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (lookup_lcgLoop s.stack_frame_sizes = SOME lsize) ∧
  (wf s.refs) ∧
  (closed_ptrs_list (stack_to_vs s) s.refs) ∧
  (no_ptrs_refs s.refs) ∧
  (* (sstack + N1 (* 5 *) < s.limits.stack_limit) ∧ *)
  (sstack + lsize + 15 < s.limits.stack_limit) ∧
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
  val still_safer =
    qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _` >>
    subgoal ‘safe’
    THENL
    [(Q.UNABBREV_TAC ‘safe’
       \\ fs[coeff_bounds_def,libTheory.the_def,size_of_Number_head,
             data_safe_def,size_of_heap_def,stack_to_vs_def,
             size_of_def,size_of_stack_def]
       \\ rpt (pairarg_tac \\ fs []) \\ rveq
       \\ pop_assum mp_tac
       \\ TRY(eval_goalsub_tac ``size_of _ _`` \\ simp [])
       \\ fs [size_of_Number_head]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
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
  \\ impl_tac
  >- (simp[code_lookup,frame_lookup,
          data_to_wordTheory.Compare_location_eq,
          data_to_wordTheory.Compare1_location_eq,
          data_to_wordTheory.LongDiv_location_eq,
          data_to_wordTheory.LongDiv1_location_eq]
      \\ simp[GSYM hex_body_def, GSYM n2l_acc_body_def, repchar_list_def]
      \\ CONJ_TAC
      >- simp[integerTheory.INT_ADD,integerTheory.INT_MOD]
      \\ CONJ_ASM1_TAC
      >- (match_mp_tac (GEN_ALL small_num_bound_imp_1)
          \\ qexists_tac`m`>>simp[])
      \\ CONJ_TAC
      >- fs[small_num_def]
      \\ simp[size_of_heap_def]
      \\ eval_goalsub_tac``size_of _ _ _``
      \\ simp[Once data_to_word_gcProofTheory.size_of_cons]
      \\ DEP_REWRITE_TAC [size_of_Number_head]
      \\ simp[size_of_def]
      \\ simp[small_num_def]
      \\ fs[size_of_heap_def,stack_to_vs_def]
      \\ rpt(pairarg_tac \\ fs[])
      \\ pop_assum mp_tac
      \\ eval_goalsub_tac``sptree$toList _``
      \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
      \\ DEP_ONCE_REWRITE_TAC [size_of_Number_head_append]
      \\ simp[] \\ rw[]
      \\ pop_assum mp_tac \\ rw[])
  \\ simp[integerTheory.INT_ADD,integerTheory.INT_MOD,GSYM n2l_acc_body_def]
  \\ strip_tac \\ simp[]
  >- simp[data_safe_def]
  \\ simp[pop_env_def,set_var_def]
  \\ eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  (* call_put_chars (21,⦕ 1; 2; 3; 14 ⦖) [20] NONE; *)
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
    rw[]>>simp[libTheory.the_def]>>
    fs[MAX_DEF]>>
    simp[data_safe_def] )>>
  simp[GSYM put_chars_body_def]>>
  still_safer
  >- (rw[MAX_DEF]>>simp[])>>
  qmatch_goalsub_abbrev_tac`(_,ss)`>>
  `size_of_stack ss.stack = SOME (lsize+sstack)` by
    (simp[Abbr`ss`,size_of_stack_def,size_of_stack_frame_def]>>
    simp[GSYM size_of_stack_def])>>
  `(ss.locals_size = SOME 3)` by fs[Abbr`ss`]>>
  drule put_chars_evaluate>>
  simp[Abbr`ss`]>>
  qmatch_goalsub_abbrev_tac`evaluate(put_chars_body,ss)`>>
  disch_then(qspec_then`20` mp_tac)>>
  impl_tac >- (
    simp[Abbr`ss`,stack_to_vs_def,extract_stack_def]>>
    eval_goalsub_tac``sptree$toList _``>>
    eval_goalsub_tac``sptree$toList _``>>
    CONJ_TAC>-
      (fs[stack_to_vs_def,extract_stack_def,closed_ptrs_list_append,
          closed_ptrs_list_def] >>
       drule_then MATCH_ACCEPT_TAC closed_ptrs_repchar_list) >>
    (* ?????? *)
    cheat)>>
  strip_tac>>
  simp[]
  >- simp[data_safe_def]>>
  simp[pop_env_def,set_var_def] >>
  eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  (* tailcall_lcgLoop [14; 1; 2; 3] *)
  ASM_REWRITE_TAC [ tailcall_def , find_code_def
                  , get_vars_def , get_var_def
                  , lookup_def   , timeout_def
                  , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup] >>
  IF_CASES_TAC >- (
    simp[state_component_equality,PULL_EXISTS,GSYM size_of_stack_def]>>
    simp[MAX_DEF,libTheory.the_def]>>
    rw[]>>simp[data_safe_def] )>>
  simp[GSYM lcgLoop_body_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def ]
  \\ simp [] >>
  still_safer
  >- (
    strip_tac>>
    rw[MAX_DEF]) >>
  qmatch_goalsub_abbrev_tac`(_,sss)`>>
  first_x_assum(qspec_then`sss` mp_tac)>>
  `sss.clock < s.clock` by
    fs[Abbr`sss`]>>
  simp[Abbr`sss`,PULL_EXISTS,size_of_stack_def]>>
  disch_then(qspec_then `(c + a * x) MOD m` mp_tac)>>
  impl_tac >- (
    fs[frame_lookup,code_lookup,GSYM lcgLoop_body_def]>>
    `lsize = 6` by
      (qpat_x_assum`lookup_lcgLoop s.stack_frame_sizes = SOME lsize` mp_tac>>
      simp[frame_lookup])>>
    simp[]>>
    CONJ_TAC>- (
      fs[stack_to_vs_def,Abbr`ss`]>>
      fs[stack_to_vs_def,extract_stack_def,closed_ptrs_list_append,
          closed_ptrs_list_def] >>
      EVAL_TAC) >>
    CONJ_TAC >- (
      qpat_x_assum ‘size_of_heap _ + _ ≤ _’ assume_tac >>
      match_mp_tac LESS_EQ_TRANS >>
      simp[Once CONJ_SYM] >>
      goal_assum dxrule >>
      simp[size_of_heap_def,stack_to_vs_def] >>
      qmatch_goalsub_abbrev_tac ‘size_of _ (a1 ++ _ ++ _)’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
      CONV_TAC(LAND_CONV EVAL) >>
      disch_then SUBST_ALL_TAC >>
      fs[] >>
      dep_rewrite.DEP_REWRITE_TAC[size_of_Number_head] >>
      simp[] >>
      conj_tac >-
        (qpat_x_assum ‘small_num T ((&(a * x) + &c) % &m)’ mp_tac >>
         qpat_x_assum ‘x < m’ mp_tac >>
         rpt(pop_assum kall_tac) >>
         simp[integerTheory.INT_ADD]) >>
      qmatch_goalsub_abbrev_tac ‘size_of _ (a1 ++ _ ++ _)’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
      CONV_TAC(LAND_CONV EVAL) >>
      disch_then SUBST_ALL_TAC >>
      fs[] >>
      dep_rewrite.DEP_REWRITE_TAC[size_of_Number_head] >>
      simp[] >>
      cheat (* requires adding subspt s.refs refs0 to put_chars concl *)) >> (* easy *)
    EVAL_TAC)>>
  simp[to_shallow_thm]>>
  eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  strip_tac>>
  eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  pairarg_tac>>fs[]>>
  rw[]>>fs[data_safe_def]
end
QED

Theorem data_safe_lcgLoop_code_bignum[local]:
  ∀s sstack smax y.
  s.safe_for_space ∧
  (s.stack_frame_sizes = lcgLoop_config.word_conf.stack_frame_size) ∧
  (s.code = fromAList lcgLoop_data_prog) ∧
  (s.stack_max = SOME smax) ∧
  (size_of_stack s.stack = SOME sstack) ∧
  (s.locals_size = SOME lsize) ∧
  (s.locals = fromList [Number (&x); Number (&m); Number (&c); Number (&a)]) ∧
  (s.tstamps = SOME ts) ∧
  (* big num conditions *)
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
  (* usual strip_assign but do not expand locals *)
  val strip_assign  = qmatch_goalsub_abbrev_tac `bind _ rest_ass _`
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
  val still_safe    =
    qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K safe)  _` >>
    subgoal ‘safe’
    THENL
    [(Q.UNABBREV_TAC ‘safe’
       \\ fs[coeff_bounds_def,libTheory.the_def,size_of_Number_head,
             data_safe_def,size_of_heap_def,stack_to_vs_def,
             size_of_def,size_of_stack_def]
       \\ rpt (pairarg_tac \\ fs []) \\ rveq
       \\ pop_assum mp_tac
       \\ TRY(eval_goalsub_tac ``size_of _ _`` \\ simp [])
       \\ fs [size_of_Number_head]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
  fun max_is t =
    qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K max0) _` >>
    subgoal ‘max0 = SOME (^(Term t))’
    THENL
    [(Q.UNABBREV_TAC ‘max0’ \\ fs [size_of_stack_def]),
    ASM_REWRITE_TAC [] \\ ntac 2 (pop_assum kall_tac)]
in
  measureInduct_on `^s.clock`>>
  simp[lcgLoop_body_def]
  \\ fs [to_shallow_thm
         , to_shallow_def
         , coeff_bounds_def
         , initial_state_def ]
  \\ rw [] \\ fs [fromList_def]
  \\ qabbrev_tac `szh = (size_of s.limits (FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global) s.refs LN)`
  \\ `?n xx yy. szh = (n,xx,yy)` by
    (PairCases_on`szh`>>fs[])

  (* These must all be implied *)
  \\ `x < m ∧
  bignum_size s.limits.arch_64_bit (&a) + bignum_size s.limits.arch_64_bit (&x) ≤ 2 ** s.limits.length_limit ∧
  bignum_size s.limits.arch_64_bit (&c) + bignum_size s.limits.arch_64_bit (&(a * x)) ≤ 2 ** s.limits.length_limit ∧
  bignum_size s.limits.arch_64_bit (&m) + bignum_size s.limits.arch_64_bit (&(a * x) + &c) ≤ 2 ** s.limits.length_limit ∧
  (* size_of_heap s but expanded *)
  bignum_size s.limits.arch_64_bit (&a) +
  bignum_size s.limits.arch_64_bit (&c) +
  bignum_size s.limits.arch_64_bit (&m) +
  bignum_size s.limits.arch_64_bit (&x) +
  n +
  (* extra consumption *)
  2 * bignum_size s.limits.arch_64_bit (&a) + 2 * bignum_size s.limits.arch_64_bit (&x) ≤ s.limits.heap_limit ∧

  n +
  2 * bignum_size s.limits.arch_64_bit (&c) +
  2 * bignum_size s.limits.arch_64_bit (&(a * x)) +
  bignum_size s.limits.arch_64_bit (&a) +
  bignum_size s.limits.arch_64_bit (&c) +
  bignum_size s.limits.arch_64_bit (&m) +
  bignum_size s.limits.arch_64_bit (&(a*x)) ≤ s.limits.heap_limit ∧

  n +
  2 * bignum_size s.limits.arch_64_bit (&m) +
  2 * bignum_size s.limits.arch_64_bit (&(a * x) + &c) +
  bignum_size s.limits.arch_64_bit (&a) +
  bignum_size s.limits.arch_64_bit (&c) +
  bignum_size s.limits.arch_64_bit (&m) +
  bignum_size s.limits.arch_64_bit (&(a * x) + &c) ≤ s.limits.heap_limit ∧

  n +
  bignum_size s.limits.arch_64_bit (&a) +
  bignum_size s.limits.arch_64_bit (&c) +
  bignum_size s.limits.arch_64_bit (&m) +
  bignum_size s.limits.arch_64_bit ((&(a * x) + &c) % &m) + 3 ≤ s.limits.heap_limit ∧

  smax < s.limits.stack_limit ∧
  (lsize + sstack + 14 < s.limits.stack_limit) ∧
   1 < s.limits.length_limit ` by cheat

  \\ fs[]
  (* 9 :≡ (Mult,[3; 0],...) *)
  \\ strip_assign
  \\ still_safe
  >- (
    simp[size_of_def]>>
    simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
    rpt (pairarg_tac>>fs[])>>
    strip_tac>>rveq>>fs[]>>
    simp[space_consumed_def]>>
    CONJ_TAC >-
      (rw[]>>simp[])>>
    simp[max_depth_AnyArith]>>
    rw[]>>simp[libTheory.the_def])>>
  fs[max_depth_AnyArith]>>
  rename1 `state_peak_heap_length_fupd (K pkheap) _`
  (* 10 :≡ (Add,[9; 2],...) *)
  \\ strip_assign
  \\ still_safe
  >- (
    simp[size_of_def] >>
    simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
    strip_tac>>rveq>>fs[]>>
    simp[space_consumed_def]>>
    CONJ_TAC >-
      (rw[]>>simp[])>>
    simp[max_depth_AnyArith]>>
    rw[]>>simp[libTheory.the_def]) >>
  fs[max_depth_AnyArith]
  (* peak_heap *)
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap1) _`
  \\ pop_assum kall_tac
  (* 11 :≡ (EqualInt 0,[1],NONE) *)
  \\ strip_assign
  (* if_var 11 ... *)
  \\ qmatch_goalsub_abbrev_tac `bind _ if_rest_ass`
  \\ simp [bind_def]
  (* \\ make_if  but dont expand locals *)
  \\ simp [if_var_def,data_safe_def,lookup_def,flush_state_def]
  \\ REWRITE_TAC [ isBool_def
                 , backend_commonTheory.bool_to_tag_def
                 , backend_commonTheory.true_tag_def
                 , backend_commonTheory.false_tag_def]
  \\ simp [pop_env_def]
  \\ simp[libTheory.the_def]
  (* 13 :≡ (Mod,[10; 1],...) *)
  \\ strip_assign
  \\ still_safe
  >- (
    simp[size_of_def] >>
    simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
    strip_tac>>rveq>>fs[]>>
    simp[space_consumed_def]>>
    CONJ_TAC >-
      (rw[]>>simp[])>>
    simp[max_depth_AnyArith]>>
    rw[]>>simp[libTheory.the_def])
  (* peak_heap *)
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap2) _`
  \\ pop_assum kall_tac
  (* move 14 13 *)
  \\ simp [move_def,lookup_def,set_var_def]
  \\ simp[max_depth_AnyArith]
  (* abbreviate stack_max *)
  \\ qmatch_goalsub_abbrev_tac `state_stack_max_fupd (K sm) _`
  \\ `∃smm. (sm = SOME smm) ∧ smm < s.limits.stack_limit` by
    (simp[Abbr`sm`]>>rw[MAX_DEF])
  (* throw sm away -- DANGEROUS *)
  \\ qpat_x_assum`Abbrev( _ )` kall_tac
  \\ eval_goalsub_tac ``dataSem$state_locals_fupd _ _``
  (* Exit if *)
  \\ Q.UNABBREV_TAC ‘if_rest_ass’
  (* make_space 3 ... *)
  (* \\ strip_makespace but don't expnad locals *)
  \\ qmatch_goalsub_abbrev_tac `bind _ rest_mkspc _`
  \\ REWRITE_TAC [ bind_def, makespace_def, add_space_def]
  \\ eval_goalsub_tac ``dataSem$cut_env _ _`` \\ simp []
    \\ Q.UNABBREV_TAC `rest_mkspc`
  \\ still_safe
  >- (
    simp[size_of_def] >>
    simp[Once data_to_word_gcProofTheory.size_of_cons,size_of_def]>>
    strip_tac>>rveq>>fs[]>>
    rw[]>>simp[])
  \\ qmatch_goalsub_abbrev_tac `state_peak_heap_length_fupd (K pkheap3) _`
  \\ pop_assum kall_tac
  (* 17 :≡ (Cons 0,[],NONE) *)
  \\ strip_assign
  (* 18 :≡ (Const 10,[],NONE) *)
  \\ strip_assign
  \\ eval_goalsub_tac “dataSem$state_locals_fupd _ _”
  (* 19 :≡ (Cons 0,[18; 17],NONE); *)
  \\ strip_assign
  \\ simp[check_lim_def]
  \\ still_safe
  >- (
    strip_tac>>
    simp[arch_size_def]>>rw[])
  (* call_n2l_acc (20,⦕ 1; 2; 3; 14 ⦖) [19; 14] NONE; *)
  \\ qmatch_goalsub_abbrev_tac ‘bind _ n2l_rest’
  \\ simp [bind_def,call_def]
  \\ eval_goalsub_tac “dataSem$get_vars _ _” \\ fs []
  \\ simp [find_code_def,code_lookup]
  \\ simp[GSYM n2l_acc_body_def]
  \\ eval_goalsub_tac “dataSem$cut_env _ _” \\ fs []
  \\ IF_CASES_TAC >- (
    fs [data_safe_def,frame_lookup,size_of_stack_def,
        call_env_def,push_env_def,dec_clock_def,
        size_of_stack_frame_def,MAX_DEF,libTheory.the_def])
  \\ simp[call_env_def,push_env_def,dec_clock_def]
  \\ still_safe
  >- (
    simp[size_of_stack_frame_def,frame_lookup]>>
    rw[MAX_DEF,libTheory.the_def])
  \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,s0)’
  \\ qspecl_then [‘LOG 10 m + 1’,‘(a * x + c) MOD m’,‘s0’] mp_tac n2l_acc_evaluate_bignum
  \\ UNABBREV_ALL_TAC \\ simp []
  \\ fs [data_safe_def,frame_lookup,size_of_stack_def,
            call_env_def,push_env_def,dec_clock_def,
            size_of_stack_frame_def]
  \\ disch_then (qspec_then ‘1’ mp_tac)
  \\ impl_tac
  >- (simp[code_lookup,frame_lookup,
          data_to_wordTheory.Compare_location_eq,
          data_to_wordTheory.Compare1_location_eq,
          data_to_wordTheory.LongDiv_location_eq,
          data_to_wordTheory.LongDiv1_location_eq]
      \\ simp[GSYM hex_body_def, GSYM n2l_acc_body_def, repchar_list_def]
      \\ CONJ_TAC
      >- simp[integerTheory.INT_ADD,integerTheory.INT_MOD]
      \\ CONJ_TAC >- cheat
      \\ CONJ_TAC >- cheat
      \\ cheat
      (*
      \\ CONJ_ASM1_TAC
      >- (match_mp_tac (GEN_ALL small_num_bound_imp_1)
          \\ qexists_tac`m`>>simp[])
      \\ CONJ_TAC
      >- fs[small_num_def]
      \\ simp[size_of_heap_def]
      \\ eval_goalsub_tac``size_of _ _ _``
      \\ simp[Once data_to_word_gcProofTheory.size_of_cons]
      \\ DEP_REWRITE_TAC [size_of_Number_head]
      \\ simp[size_of_def]
      \\ simp[small_num_def]
      \\ fs[size_of_heap_def,stack_to_vs_def]
      \\ rpt(pairarg_tac \\ fs[])
      \\ pop_assum mp_tac
      \\ eval_goalsub_tac``sptree$toList _``
      \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
      \\ DEP_ONCE_REWRITE_TAC [size_of_Number_head_append]
      \\ simp[] \\ rw[]
      \\ pop_assum mp_tac \\ rw[]*)) >>
  (* not updated
  \\ simp[integerTheory.INT_ADD,integerTheory.INT_MOD,GSYM n2l_acc_body_def]
  \\ strip_tac \\ simp[]
  >- simp[data_safe_def]
  \\ simp[pop_env_def,set_var_def]
  \\ eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  (* call_put_chars (21,⦕ 1; 2; 3; 14 ⦖) [20] NONE; *)
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
    rw[]>>simp[libTheory.the_def]>>
    fs[MAX_DEF]>>
    simp[data_safe_def] )>>
  simp[GSYM put_chars_body_def]>>
  still_safer
  >- (rw[MAX_DEF]>>simp[])>>
  qmatch_goalsub_abbrev_tac`(_,ss)`>>
  `size_of_stack ss.stack = SOME (lsize+sstack)` by
    (simp[Abbr`ss`,size_of_stack_def,size_of_stack_frame_def]>>
    simp[GSYM size_of_stack_def])>>
  `(ss.locals_size = SOME 3)` by fs[Abbr`ss`]>>
  drule put_chars_evaluate>>
  simp[Abbr`ss`]>>
  qmatch_goalsub_abbrev_tac`evaluate(put_chars_body,ss)`>>
  disch_then(qspec_then`20` mp_tac)>>
  impl_tac >- (
    simp[Abbr`ss`,stack_to_vs_def,extract_stack_def]>>
    eval_goalsub_tac``sptree$toList _``>>
    eval_goalsub_tac``sptree$toList _``>>
    CONJ_TAC>-
      (fs[stack_to_vs_def,extract_stack_def,closed_ptrs_list_append,
          closed_ptrs_list_def] >>
       drule_then MATCH_ACCEPT_TAC closed_ptrs_repchar_list) >>
    (* ?????? *)
    cheat)>>
  strip_tac>>
  simp[]
  >- simp[data_safe_def]>>
  simp[pop_env_def,set_var_def] >>
  eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  (* tailcall_lcgLoop [14; 1; 2; 3] *)
  ASM_REWRITE_TAC [ tailcall_def , find_code_def
                  , get_vars_def , get_var_def
                  , lookup_def   , timeout_def
                  , flush_state_def]
  \\ simp [code_lookup,lookup_def,frame_lookup] >>
  IF_CASES_TAC >- (
    simp[state_component_equality,PULL_EXISTS,GSYM size_of_stack_def]>>
    simp[MAX_DEF,libTheory.the_def]>>
    rw[]>>simp[data_safe_def] )>>
  simp[GSYM lcgLoop_body_def]
  \\ REWRITE_TAC [ call_env_def   , dec_clock_def ]
  \\ simp [] >>
  still_safer
  >- (
    strip_tac>>
    rw[MAX_DEF]) >>
  qmatch_goalsub_abbrev_tac`(_,sss)`>>
  first_x_assum(qspec_then`sss` mp_tac)>>
  `sss.clock < s.clock` by
    fs[Abbr`sss`]>>
  simp[Abbr`sss`,PULL_EXISTS,size_of_stack_def]>>
  disch_then(qspec_then `(c + a * x) MOD m` mp_tac)>>
  impl_tac >- (
    fs[frame_lookup,code_lookup,GSYM lcgLoop_body_def]>>
    `lsize = 6` by
      (qpat_x_assum`lookup_lcgLoop s.stack_frame_sizes = SOME lsize` mp_tac>>
      simp[frame_lookup])>>
    simp[]>>
    CONJ_TAC>- (
      fs[stack_to_vs_def,Abbr`ss`]>>
      fs[stack_to_vs_def,extract_stack_def,closed_ptrs_list_append,
          closed_ptrs_list_def] >>
      EVAL_TAC) >>
    CONJ_TAC >- (
      qpat_x_assum ‘size_of_heap _ + _ ≤ _’ assume_tac >>
      match_mp_tac LESS_EQ_TRANS >>
      simp[Once CONJ_SYM] >>
      goal_assum dxrule >>
      simp[size_of_heap_def,stack_to_vs_def] >>
      qmatch_goalsub_abbrev_tac ‘size_of _ (a1 ++ _ ++ _)’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
      CONV_TAC(LAND_CONV EVAL) >>
      disch_then SUBST_ALL_TAC >>
      fs[] >>
      dep_rewrite.DEP_REWRITE_TAC[size_of_Number_head] >>
      simp[] >>
      conj_tac >-
        (qpat_x_assum ‘small_num T ((&(a * x) + &c) % &m)’ mp_tac >>
         qpat_x_assum ‘x < m’ mp_tac >>
         rpt(pop_assum kall_tac) >>
         simp[integerTheory.INT_ADD]) >>
      qmatch_goalsub_abbrev_tac ‘size_of _ (a1 ++ _ ++ _)’ >>
      pop_assum (mp_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
      CONV_TAC(LAND_CONV EVAL) >>
      disch_then SUBST_ALL_TAC >>
      fs[] >>
      dep_rewrite.DEP_REWRITE_TAC[size_of_Number_head] >>
      simp[] >>
      cheat (* requires adding subspt s.refs refs0 to put_chars concl *)) >> (* easy *)
    EVAL_TAC)>>
  simp[to_shallow_thm]>>
  eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  strip_tac>>
  eval_goalsub_tac “dataSem$state_locals_fupd _ _”>>
  pairarg_tac>>fs[]>>
  rw[]>>fs[data_safe_def]
  *)
  cheat
end
QED

Theorem data_safe_lcgLoop_code_shallow[local] =
  data_safe_lcgLoop_code |> simp_rule [lcgLoop_body_def,to_shallow_thm,to_shallow_def];

Theorem do_app_mono:
  (dataSem$do_app op xs s = Rval (r,s')) ⇒
  subspt s.code s'.code ∧
  s'.clock ≤ s.clock
Proof
  rw [] \\ imp_res_tac dataPropsTheory.do_app_const \\ fs []
  \\ Cases_on ‘op’ \\ fs [dataSemTheory.do_app_def]
  \\ fs [AllCaseEqs()] \\ rw []
  \\ fs [do_space_def,AllCaseEqs()] \\ rw [] \\ fs [op_space_reset_def]
  \\ fs [do_space_def,AllCaseEqs()] \\ rw [] \\ fs [data_spaceTheory.op_space_req_def]
  \\ fs [do_app_aux_def,with_fresh_ts_def,check_lim_def,consume_space_def]
  \\ fs [AllCaseEqs()] \\ rw []
  \\ fs [do_install_def,AllCaseEqs()]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [AllCaseEqs()] \\ rw []
  \\ fs [] \\ fs [subspt_lookup,lookup_union]
QED

Theorem evaluate_mono:
  ∀prog s res s'.
    (dataSem$evaluate (prog,s) = (res,s')) ⇒
    subspt s.code s'.code ∧
    s'.clock ≤ s.clock
Proof
  recInduct dataSemTheory.evaluate_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [evaluate_def]
  \\ TRY (simp [AllCaseEqs(),cut_state_opt_def,cut_state_def,
           cut_state_opt_def,cut_state_def,jump_exc_def,call_env_def,pop_env_def,
           set_var_def,flush_state_def,dec_clock_def,add_space_def]
    \\ fs [] \\ rw []
    \\ rpt (pairarg_tac \\ fs [AllCaseEqs()])
    \\ rw [] \\ fs []
    \\ imp_res_tac do_app_mono \\ fs [] \\ NO_TAC)
  THEN1
   (fs [] \\ rpt (pairarg_tac \\ fs [AllCaseEqs()])
    \\ rw [] \\ fs [] \\ res_tac
    \\ imp_res_tac subspt_trans \\ fs [])
  THEN1
   (fs [] \\ rpt (pairarg_tac \\ fs [AllCaseEqs()])
    \\ rw [] \\ fs [] \\ res_tac
    \\ imp_res_tac subspt_trans \\ fs [])
  \\ simp [AllCaseEqs()] \\ rw [] \\ fs []
  \\ first_x_assum drule \\ rpt (disch_then drule) \\ fs []
  \\ TRY (fs [flush_state_def,call_env_def,dec_clock_def,set_var_def]
          \\ rw [] \\ imp_res_tac subspt_trans \\ fs []
          \\ fs [pop_env_def,AllCaseEqs()] \\ rw [] \\ fs [] \\ NO_TAC)
  \\ fs [flush_state_def,call_env_def,dec_clock_def,set_var_def,push_env_def]
  \\ rw [] \\ imp_res_tac subspt_trans \\ fs []
  \\ fs [pop_env_def,AllCaseEqs()] \\ rw [] \\ fs []
  \\ first_x_assum drule \\ rpt (disch_then drule) \\ fs []
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
 \\ ntac 11
    (strip_call
    \\ ntac 9 strip_assign
    \\ make_if
    \\ UNABBREV_ALL_TAC)
 (* This avoid last unabbrev *)
 \\ strip_call
 \\ ntac 9 strip_assign
 \\ make_if
 \\ ntac 6 strip_assign
 \\ ntac 12
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
  \\ ntac 11
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
  \\ simp[frame_lookup]
  \\ EVAL_TAC
  \\ rw []
  `(x = 0) ∨ (x = 1)` by
    (qmatch_asmsub_abbrev_tac`lookup x ss`>>
    `domain ss = {0; 1}` by
      (simp[Abbr`ss`]>>EVAL_TAC)>>
    `x ∈ domain ss` by
      simp[domain_lookup]>>
    rfs[])>>
  qpat_x_assum`_= SOME _` mp_tac>>
  simp[]>> EVAL_TAC>>
  disch_then sym_sub_tac>>EVAL_TAC
end
QED

val _ = export_theory();
