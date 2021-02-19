st(*
  Correctness proof for --
*)

open preamble
     timeSemTheory panSemTheory
     timePropsTheory panPropsTheory
     pan_commonPropsTheory time_to_panTheory
     labPropsTheory ffiTimeTheory


val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem", "ffiTime",
         "pan_commonProps", "timeProps",
         "time_to_pan"];


Definition equiv_val_def:
  equiv_val fm xs v <=>
    v = MAP (ValWord o n2w o THE o (FLOOKUP fm)) xs
End


Definition valid_clks_def:
  valid_clks clks tclks wt <=>
    EVERY (λck. MEM ck clks) tclks ∧
    EVERY (λck. MEM ck clks) (MAP SND wt)
End


Definition resetClksVals_def:
  resetClksVals fm xs ys  =
    MAP
    (ValWord o n2w o THE o
     (FLOOKUP (resetClocks fm ys))) xs
End


Definition retVal_def:
  retVal s clks tclks wt dest =
    Struct [
        Struct (resetClksVals s.clocks clks tclks);
        ValWord (case wt of [] => 1w | _ => 0w);
        ValWord (case wt of [] => 0w
                         | _ => n2w (THE (calculate_wtime s tclks wt)));
        ValLabel (toString dest)]
End


Definition maxClksSize_def:
  maxClksSize clks ⇔
    SUM (MAP (size_of_shape o shape_of) clks) ≤ 29
End


Definition clock_bound_def:
  clock_bound fm clks (m:num) ⇔
    EVERY
      (λck. ∃n. FLOOKUP fm ck = SOME n ∧
                n < m) clks
End

Definition time_range_def:
  time_range wt (m:num) ⇔
    EVERY (λ(t,c). t < m) wt
End


Definition restore_from_def:
  (restore_from t lc [] = lc) ∧
  (restore_from t lc (v::vs) =
   restore_from t (res_var lc (v, FLOOKUP t.locals v)) vs)
End

Definition emptyVals_def:
  emptyVals n = REPLICATE n (ValWord 0w)
End

Definition constVals_def:
  constVals n v = REPLICATE n v
End


Definition minOption_def:
  (minOption (x:'a word) NONE = x) ∧
  (minOption x (SOME (y:num)) =
    if x <₊ n2w y then x else n2w y)
End


Definition well_behaved_ffi_def:
  well_behaved_ffi ffi_name s n (m:num) <=>
  explode ffi_name ≠ "" ∧ n < m ∧
  ∃bytes nbytes.
    read_bytearray ffiBufferAddr n
                   (mem_load_byte s.memory s.memaddrs s.be) =
    SOME bytes ∧
    s.ffi.oracle (explode ffi_name) s.ffi.ffi_state [] bytes =
    Oracle_return s.ffi.ffi_state nbytes ∧
    LENGTH nbytes = LENGTH bytes
End


Definition ffi_return_state_def:
  ffi_return_state s ffi_name bytes nbytes =
  s with
    <|memory := write_bytearray 4000w nbytes s.memory s.memaddrs s.be;
      ffi :=
      s.ffi with
       <|io_events :=
         s.ffi.io_events ++
          [IO_event (explode ffi_name) [] (ZIP (bytes,nbytes))]|> |>
End


Definition nffi_state_def:
  nffi_state s (n:num) bytes nbytes =
    s.ffi with
     <|io_events :=
       s.ffi.io_events ++
        [IO_event (toString n) [] (ZIP (bytes,nbytes))]|>
End

Definition code_installed_def:
  code_installed code prog <=>
  ∀loc tms.
    MEM (loc,tms) prog ⇒
    let clks = clksOf prog;
        n = LENGTH clks
    in
      FLOOKUP code (toString loc) =
      SOME ([(«clks», genShape n);
             («event», One)],
            compTerms clks «clks» «event» tms)
End


Definition ffi_vars_def:
  ffi_vars fm  ⇔
  FLOOKUP fm «ptr1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «len1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «ptr2» = SOME (ValWord ffiBufferAddr) ∧
  FLOOKUP fm «len2» = SOME (ValWord ffiBufferSize)
End


Definition time_vars_def:
  time_vars fm ⇔
  (∃st. FLOOKUP fm «sysTime»  = SOME (ValWord st)) ∧
  (∃wt. FLOOKUP fm «wakeUpAt» = SOME (ValWord wt)) ∧
  (∃io. FLOOKUP fm «event»    = SOME (ValWord io)) ∧
  (∃i.  FLOOKUP fm «isInput»  = SOME (ValWord i)) ∧
  (∃w.  FLOOKUP fm «waitSet»  = SOME (ValWord w))
End


(* for easier reasoning *)
Definition clkvals_rel_def:
  clkvals_rel fm xs ys (n:num) ⇔
    MAP (λ(x,y). y + THE (FLOOKUP fm x)) (ZIP (xs,ys)) =
    MAP (λx. n) ys ∧
    EVERY (\x. THE (FLOOKUP fm x) <= n) xs
End


Definition clocks_rel_def:
  clocks_rel sclocks tlocals clks stime ⇔
  ∃ns.
    FLOOKUP tlocals «clks» =
    SOME (Struct (MAP (ValWord o n2w) ns)) ∧
    LENGTH clks = LENGTH ns ∧
    clkvals_rel sclocks clks ns stime
End


Definition active_low_def:
  (active_low NONE = 1w) ∧
  (active_low (SOME _) = 0w)
End


Definition add_time_def:
  (add_time t NONE     = SOME (ValWord 0w)) ∧
  (add_time t (SOME n) = SOME (ValWord (t + n2w n)))
End


Definition equivs_def:
  equivs fm loc wt ⇔
  FLOOKUP fm «loc» = SOME (ValLabel (toString loc)) ∧
  FLOOKUP fm «waitSet» = SOME (ValWord (active_low wt))
End

Definition time_seq_def:
  time_seq (f:num -> num # num) m ⇔
  (∀n. ∃d. FST (f (SUC n)) = FST (f n) + d) ∧
  (∀n. FST (f n) < m)
End


Definition mem_config_def:
  mem_config (mem:'a word -> 'a word_lab) (adrs:('a word) set) be ⇔
    (∃w. mem ffiBufferAddr = Word w) ∧
    (∃w. mem (ffiBufferAddr + bytes_in_word) = Word w) ∧
    ffiBufferAddr ∈ adrs ∧
    ffiBufferAddr + bytes_in_word ∈ adrs
End


Definition state_rel_def:
  state_rel clks s (t:('a,time_input) panSem$state) ⇔
    equivs t.locals s.location s.waitTime ∧
    ffi_vars t.locals ∧  time_vars t.locals ∧
    mem_config t.memory t.memaddrs t.be ∧
    LENGTH clks ≤ 29 ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    let
      ffi = t.ffi.ffi_state;
      io_events = t.ffi.io_events;
      (tm,io_flg) = ffi 0
    in
      t.ffi = build_ffi (:'a) t.be ffi io_events ∧
      time_seq ffi (dimword (:'a)) ∧
      FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
      clocks_rel s.clocks t.locals clks tm
End

Definition nexts_ffi_def:
  nexts_ffi m (f:num -> (num # num)) =
  λn. f (n+m)
End

Definition delay_rep_def:
  delay_rep m (d:num) (seq:time_input) cycles ⇔
    FST (seq cycles) = d + FST (seq 0) ∧
    FST (seq cycles) < m ∧
    ∀i. i <= cycles ⇒ SND (seq i) = 0
End

(*
Definition delay_rep_def:
  delay_rep m (d:num) (seq:time_input) cycles ⇔
    FST (seq cycles) = d + FST (seq 0) ∧
    FST (seq cycles) < m ∧
    ∀i. i < cycles ⇒ ¬SND (seq i)
End
*)

Definition wakeup_rel_def:
  (wakeup_rel fm m NONE (seq:time_input) cycles = T) ∧
  (wakeup_rel fm m (SOME wt) seq cycles =
   let
     st =  FST (seq 0)
   in
     FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
     FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w (wt + st))) ∧
     wt + st < m ∧
     FST (seq cycles) < wt + st)
End


Theorem eval_empty_const_eq_empty_vals:
  ∀s n.
    OPT_MMAP (λe. eval s e) (emptyConsts n) =
    SOME (emptyVals n)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  fs [emptyConsts_def, emptyVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n' (REPLICATE n ((Const 0w):'a panLang$exp)) = Const 0w’ by (
    match_mp_tac EL_REPLICATE >>
    fs []) >>
  ‘EL n' (REPLICATE n (ValWord 0w)) = ValWord 0w’ by (
    match_mp_tac EL_REPLICATE >>
    fs []) >>
  fs [eval_def]
QED

Theorem opt_mmap_resetTermClocks_eq_resetClksVals:
  ∀t clkvals s clks tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    OPT_MMAP (λa. eval t a)
             (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- fs [resetTermClocks_def, resetClksVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- fs [resetTermClocks_def, resetClksVals_def] >>
  rw [] >>
  fs [resetTermClocks_def] >>
  TOP_CASE_TAC
  >- (
    ‘EL n (resetClksVals s.clocks clks tclks) = ValWord 0w’ by (
    fs [resetClksVals_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’] >>
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ mp_tac) >>
    fs []) >>
   fs [eval_def]) >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘EL n clks’ mp_tac) >>
  impl_tac
  >- (match_mp_tac EL_MEM >> fs []) >>
  strip_tac >>
  fs [FDOM_FLOOKUP] >>
  ‘EL n (resetClksVals s.clocks clks tclks) = ValWord (n2w v)’ by (
    fs [resetClksVals_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’] >>
    drule reset_clks_not_mem_flookup_same >>
    fs []) >>
  fs [] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
  ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’]
QED


Theorem maxClksSize_reset_clks_eq:
  ∀s clks (clkvals:α v list) tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals  ⇒
    maxClksSize ((resetClksVals s.clocks clks tclks):α v list)
Proof
  rw [] >>
  fs [resetClksVals_def] >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [maxClksSize_def] >>
  fs [MAP_MAP_o] >>
  fs [SUM_MAP_FOLDL] >>
  qmatch_asmsub_abbrev_tac ‘FOLDL ff _ _’ >>
  qmatch_goalsub_abbrev_tac ‘FOLDL gg _ _’ >>
  ‘FOLDL ff 0 clks = FOLDL gg 0 clks ’ by (
    match_mp_tac FOLDL_CONG >>
    fs [Abbr ‘ff’, Abbr ‘gg’] >> rw [shape_of_def]) >>
  fs []
QED


Theorem calculate_wait_times_eq:
  ∀t vname clkvals s clks wt.
    FLOOKUP t.locals vname = SOME (Struct clkvals) ∧
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    EVERY (λck. MEM ck clks) (MAP SND wt) ∧
    EVERY (λ(t,c). ∃v. FLOOKUP s.clocks c = SOME v ∧ v ≤ t) wt ⇒
    OPT_MMAP (λe. eval t e)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var vname)) (indicesOf clks (MAP SND wt)))) =
    SOME (MAP (ValWord ∘ n2w ∘ THE ∘ evalDiff s) wt)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  rw [waitTimes_def, indicesOf_def, LIST_REL_EL_EQN] >>
  ‘SND (EL n wt) ∈ FDOM s.clocks’ by (
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘SND (EL n wt)’ mp_tac) >>
    impl_tac
    >- (
      drule EL_MEM >>
      fs [MEM_MAP] >>
      metis_tac []) >>
    strip_tac >>
    last_x_assum drule >>
    fs []) >>
  qmatch_goalsub_abbrev_tac ‘MAP2 ff xs ys’ >>
  ‘EL n (MAP2 ff xs ys) =
   ff (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    fs [Abbr ‘xs’, Abbr ‘ys’]) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘xs’] >>
  ‘EL n (MAP FST wt) = FST (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘ys’] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP gg _)’ >>
  ‘EL n (MAP gg wt) = gg (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘MAP hh _’ >>
  ‘EL n (MAP hh wt) = hh (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘gg’, Abbr ‘ff’, Abbr ‘hh’] >>
  cases_on ‘EL n wt’ >> fs [] >>
  fs [evalDiff_def, evalExpr_def, EVERY_EL] >>
  fs [FDOM_FLOOKUP] >>
  fs [minusT_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [eval_def] >>
  ‘findi r clks < LENGTH clkvals’ by (
    fs [equiv_val_def] >>
    match_mp_tac MEM_findi >>
    res_tac >> fs [] >>
    rfs [] >>
    ‘EL n (MAP SND wt) = SND (EL n wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    rfs [] >> rveq >> fs []) >>
  fs [] >>
  rfs [equiv_val_def] >>
  qmatch_goalsub_abbrev_tac ‘EL m (MAP ff _)’ >>
  ‘EL m (MAP ff clks) = ff (EL m clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’, Abbr ‘m’] >>
  pop_assum kall_tac >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  ‘EL (findi r clks) clks = r’ by (
    match_mp_tac EL_findi >>
    res_tac >> fs [] >>
    rfs [] >>
    ‘EL n (MAP SND wt) = SND (EL n wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    rfs [] >> rveq >> fs []) >>
  fs [wordLangTheory.word_op_def] >>
  first_x_assum drule >>
  fs [] >>
  strip_tac >>
  ‘n2w (q − v):'a word = n2w q − n2w v’ suffices_by fs [] >>
  match_mp_tac n2w_sub >> rveq >> fs [] >> rveq >> rfs [] >>
  first_x_assum drule >>
  fs []
QED


Theorem eval_term_clkvals_equiv_reset_clkvals:
  ∀s io io' cnds tclks dest wt s' clks.
    evalTerm s io
             (Tm io' cnds tclks dest wt) s' ⇒
    equiv_val s'.clocks clks (resetClksVals s.clocks clks tclks)
Proof
  rw [] >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [equiv_val_def] >>
  fs [resetClksVals_def]
QED


Theorem evaluate_minop_eq:
  ∀es s vname n ns res t.
    FLOOKUP s.locals vname = SOME (ValWord (n2w n)) ∧
    (∀n. n < LENGTH es ⇒ ~MEM vname (var_exp (EL n es))) ∧
    MAP (eval s) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ∧
    n < dimword (:α) ∧
    EVERY (λn. n < dimword (:α)) ns ∧
    evaluate (minOp vname es,s) = (res,t) ⇒
    res = NONE ∧
    t = s with locals:= s.locals |+
                         (vname,
                          ValWord (minOption (n2w n) (list_min_option ns)))
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >> fs []
  >- (
    fs [minOp_def, evaluate_def] >> rveq >>
    fs [minOption_def, list_min_option_def] >>
    cases_on ‘s’ >>
    fs [state_fn_updates] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_ELIM >>
    fs [FLOOKUP_DEF]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minOp_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def] >>
  rfs [] >>
  fs [asmTheory.word_cmp_def] >>
  cases_on ‘(n2w h'):'a word <₊ n2w n’ >>
  fs []
  >- (
    fs [evaluate_def] >>
    rfs [] >>
    fs [is_valid_value_def] >>
    rfs [] >>
    fs [panSemTheory.shape_of_def] >>
    rveq >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, stNew)’ >>
    last_x_assum
    (qspecl_then
     [‘stNew’, ‘vname’, ‘h'’, ‘t'’, ‘res’, ‘t’] mp_tac) >>
    fs [Abbr ‘stNew’] >>
    fs [FLOOKUP_UPDATE] >>
    impl_tac
    >- (
      reverse conj_tac
      >- (
        fs [MAP_EQ_EVERY2] >>
        fs [LIST_REL_EL_EQN] >>
        rw [] >>
        match_mp_tac update_locals_not_vars_eval_eq >>
        last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
        fs []) >>
      rw [] >> fs [] >>
      last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
      fs []) >>
    strip_tac >>
    fs [list_min_option_def] >>
    cases_on ‘list_min_option t'’ >> fs []
    >- (
    fs [minOption_def] >>
    ‘~(n2w n <₊ n2w h')’ by (
      fs [WORD_NOT_LOWER] >>
      gs [WORD_LOWER_OR_EQ]) >>
    fs []) >>
    drule list_min_option_some_mem >>
    strip_tac >>
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘x’ mp_tac) >>
    fs [] >>
    strip_tac >>
    cases_on ‘h' < x’ >> fs []
    >- (
    fs [minOption_def] >>
     ‘~(n2w n <₊ n2w h')’ by (
      fs [WORD_NOT_LOWER] >>
      gs [WORD_LOWER_OR_EQ]) >>
     fs [] >>
    qsuff_tac ‘(n2w h'):'a word <₊ n2w x’ >- fs [] >>
    fs [word_lo_n2w]) >>
    fs [minOption_def] >>
    ‘~((n2w h'):'a word <₊ n2w x)’ by (
      fs [WORD_NOT_LOWER, NOT_LESS, word_ls_n2w]) >>
    fs [] >>
    ‘~((n2w n):'a word <₊ n2w x)’ by (
      fs [WORD_NOT_LOWER] >>
      fs [NOT_LESS] >>
      ‘h' < n’ by gs [word_lo_n2w] >>
      ‘x < n’ by gs [] >>
      gs [word_ls_n2w]) >>
    fs []) >>
  fs [evaluate_def] >>
  rfs [] >> rveq >>
  last_x_assum
  (qspecl_then
   [‘s’, ‘vname’, ‘n’, ‘t'’, ‘res’, ‘t’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
    rw [] >>
    last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [list_min_option_def] >>
  cases_on ‘list_min_option t'’ >> fs []
  >- (
    fs [minOption_def] >>
    fs [WORD_NOT_LOWER] >>
    gs [WORD_LOWER_OR_EQ]) >>
  fs [minOption_def] >>
  every_case_tac >> fs [WORD_NOT_LOWER]
  >- (
    qsuff_tac ‘h' = n’ >- fs [] >>
    qsuff_tac ‘h' ≤ n ∧ n ≤ h'’ >- fs [] >>
    gs [word_ls_n2w]) >> (
  drule list_min_option_some_mem >>
  strip_tac >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >>
  gs [word_ls_n2w])
QED


Theorem evaluate_min_exp_eq:
  ∀es s vname v ns res t.
    FLOOKUP s.locals vname = SOME (ValWord v) ∧
    (∀n. n < LENGTH es ⇒ ~MEM vname (var_exp (EL n es))) ∧
    MAP (eval s) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ∧
    EVERY (λn. n < dimword (:α)) ns ∧
    evaluate (minExp vname es,s) = (res,t) ⇒
    res = NONE ∧
    (es = [] ⇒ t = s) ∧
    (es ≠ [] ⇒
     t = s with locals :=
         s.locals |+
          (vname, ValWord ((n2w:num -> α word) (THE (list_min_option ns)))))
Proof
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘es’ >> fs []
  >- (
    fs [minExp_def] >>
    fs [evaluate_def]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minExp_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  rfs [] >>
  fs [is_valid_value_def] >>
  rfs [] >>
  fs [panSemTheory.shape_of_def] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,stInit)’ >>
  ‘FLOOKUP stInit.locals vname = SOME (ValWord (n2w h'))’ by (
    fs [Abbr ‘stInit’] >>
    fs [FLOOKUP_UPDATE]) >>
  last_x_assum mp_tac >>
  drule evaluate_minop_eq >>
  disch_then (qspecl_then [‘t'’, ‘t''’, ‘res’, ‘t’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
    conj_tac
    >- (
      rw [] >>
      last_x_assum (qspec_then ‘SUC n’ mp_tac) >>
      fs []) >>
    fs [Abbr ‘stInit’] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    match_mp_tac update_locals_not_vars_eval_eq >>
    last_x_assum (qspec_then ‘SUC n’ mp_tac) >>
    fs []) >>
  rpt strip_tac >> fs [] >>
  fs [list_min_option_def] >>
  cases_on ‘list_min_option t''’ >> fs [] >>
  fs [Abbr ‘stInit’, minOption_def] >>
  drule list_min_option_some_mem >>
  strip_tac >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  fs [] >>
  strip_tac >>
  every_case_tac
  >- (
    fs [NOT_LESS] >>
    qsuff_tac ‘h' < x’ >- fs [] >>
    gs [word_lo_n2w]) >>
  fs [WORD_NOT_LOWER] >>
  gs [word_ls_n2w]
QED


Theorem every_conj_spec:
  ∀fm xs w.
    EVERY
    (λck. ∃n. FLOOKUP fm ck = SOME n ∧
              n < dimword (:α)) xs ⇒
    EVERY (λck. ck IN FDOM fm) xs
Proof
  rw [] >>
  fs [EVERY_MEM] >>
  rw [] >>
  last_x_assum drule >>
  strip_tac >> fs [FDOM_FLOOKUP]
QED


Theorem shape_of_resetClksVals_eq:
  ∀fm (clks:mlstring list) (tclks:mlstring list) (clkvals:'a v list).
    EVERY (λv. ∃w. v = ValWord w) clkvals /\
    LENGTH clks = LENGTH clkvals ⇒
    MAP ((λa. size_of_shape a) ∘ (λa. shape_of a))
        ((resetClksVals fm clks tclks):'a v list) =
    MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  fs [resetClksVals_def] >>
  rw [] >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
  ‘EL n (MAP f clks) = f (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘f’] >>
  pop_assum kall_tac >>
  fs [EVERY_MEM] >>
  drule EL_MEM >>
  strip_tac >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  fs [panSemTheory.shape_of_def]
QED

Theorem comp_input_term_correct:
  ∀s n cnds tclks dest wt s' t (clkvals:'a v list) clks.
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ⇒
      evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with locals :=
       restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clock_bound_def, time_range_def] >>
  drule every_conj_spec >>
  strip_tac >>
  drule eval_term_clkvals_equiv_reset_clkvals >>
  disch_then (qspec_then ‘clks’ assume_tac) >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [compTerm_def] >>
  cases_on ‘wt’
  >- ( (* wait set is disabled *)
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
   ‘OPT_MMAP (λa. eval stInit a)
      (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
     qexists_tac ‘clkvals’ >> rfs [] >>
     fs [Abbr ‘stInit’] >>
     rfs [FLOOKUP_UPDATE]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [emptyConsts_def] >>
   fs [OPT_MMAP_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [eval_def] >>
   fs [indicesOf_def, waitTimes_def, minExp_def] >>
   pop_assum mp_tac >>
   rewrite_tac [OPT_MMAP_def] >>
   strip_tac >>
   fs [is_valid_value_def] >>
   fs [FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule maxClksSize_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [maxClksSize_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [restore_from_def]) >>
  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘emptyConsts (LENGTH wt)’ >>
  ‘(case wt of [] => Const 1w | v2::v3 => Const 0w) =
   (Const 0w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [panLangTheory.decs_def] >>
  fs [evaluate_def] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  rfs [] >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
  ‘OPT_MMAP (λa. eval stInit a)
   (resetTermClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
    qexists_tac ‘clkvals’ >> rfs [] >>
    fs [Abbr ‘stInit’] >>
    rfs [FLOOKUP_UPDATE]) >>
  fs [] >>
  pop_assum kall_tac >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [eval_empty_const_eq_empty_vals] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [panLangTheory.nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  qmatch_asmsub_abbrev_tac ‘eval stReset _’ >>
  fs [eval_def] >>
  (* waitimes eq eval diffs *)
  ‘OPT_MMAP (λa. eval stReset a)
   (waitTimes (MAP FST wt)
    (MAP (λn. Field n (Var «newClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ THE ∘ evalDiff
              (s with clocks := resetClocks s.clocks tclks)) wt)’ by (
    match_mp_tac calculate_wait_times_eq >>
    qexists_tac ‘resetClksVals s.clocks clks tclks’ >>
    rfs [Abbr ‘stReset’] >>
    rewrite_tac [FLOOKUP_UPDATE] >>
    fs [] >>
    fs [equiv_val_def] >>
    last_x_assum assume_tac >>
    drule fdom_reset_clks_eq_clks >>
    strip_tac >>
    rfs [valid_clks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs [] >>
    cases_on ‘e’ >> fs [] >>
    strip_tac >>
    fs [] >>
    match_mp_tac flookup_reset_clks_leq >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘is_valid_value tt _ wtval’ >>
  ‘is_valid_value tt «waitTimes» wtval’ by (
    fs [Abbr ‘tt’, Abbr ‘wtval’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    fs [emptyVals_def, emptyConsts_def] >>
    fs [MAP_MAP_o, GSYM MAP_K_REPLICATE, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (minExp _ es, stWait)’ >>
  ‘FLOOKUP stWait.locals «wakeUpAt» = SOME (ValWord 0w)’ by
    fs [Abbr ‘stWait’, FLOOKUP_UPDATE] >>
  drule evaluate_min_exp_eq >>
  disch_then (
    qspecl_then [
        ‘es’,
        ‘MAP (THE o evalDiff (s with clocks := resetClocks s.clocks tclks)) wt’,
        ‘res''’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (
   rfs [] >>
   conj_tac
   >- (
    rw [] >>
    fs [Abbr ‘es’] >>
    fs [panLangTheory.var_exp_def]) >>
   conj_tac
   >- (
    fs [Abbr ‘stWait’, Abbr ‘es’] >>
    fs [Abbr ‘wtval’] >>
    fs [MAP_MAP_o] >>
    fs [MAPi_enumerate_MAP] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [LENGTH_enumerate] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    ‘EL n (enumerate 0 wt) = (n+0,EL n wt)’ by (
      match_mp_tac EL_enumerate >>
      fs []) >>
    fs [] >>
    pop_assum kall_tac >>
    fs [eval_def] >>
    fs [FLOOKUP_UPDATE] >>
    rveq >> rfs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL i (MAP ff wt) = ff (EL i wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’]) >>
   fs [EVERY_MAP, EVERY_MEM] >>
   gen_tac >>
   strip_tac >>
   cases_on ‘x’ >>
   fs [evalDiff_def, evalExpr_def] >>
   cases_on ‘MEM r tclks’
   >- (
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ assume_tac) >>
    fs [] >>
    fs [minusT_def] >>
    first_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
    fs []) >>
   rfs [valid_clks_def] >>
   rfs [EVERY_MEM] >>
   ‘MEM r clks’ by (
     ‘MEM r (MAP SND wt)’ by (
       fs [MEM_MAP] >>
       qexists_tac ‘(q,r)’ >> fs []) >>
     res_tac >> gs []) >>
   res_tac >> rfs [] >>
   drule reset_clks_not_mem_flookup_same >>
   disch_then (qspec_then ‘tclks’ mp_tac) >>
   rfs [] >>
   strip_tac >>
   fs [minusT_def] >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs [] >>
   strip_tac >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   gs []) >>
  strip_tac >> fs [] >>
  ‘es ≠ []’ by fs [Abbr ‘wt’, Abbr ‘es’] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  fs [OPT_MMAP_def, eval_def, FLOOKUP_UPDATE] >>
  rfs [FDOM_FLOOKUP] >>
  rfs [] >>
  fs [panLangTheory.size_of_shape_def, panSemTheory.shape_of_def] >>
  fs [MAP_MAP_o] >>
  qmatch_asmsub_abbrev_tac ‘SUM ss’ >>
  ‘ss =
   MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals’ by (
    fs [Abbr ‘ss’] >>
    match_mp_tac shape_of_resetClksVals_eq >>
    rfs [equiv_val_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [MEM_MAP]) >>
  rfs [maxClksSize_def] >>
  qmatch_asmsub_abbrev_tac ‘ss = tt’ >>
  ‘SUM ss + 3 ≤ 32’ by fs [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [empty_locals_def] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  fs [restore_from_def] >>
  fs [retVal_def] >>
  fs [calculate_wtime_def]
QED


Theorem ffi_eval_state_thm:
  !ffi_name s (res:'a result option) t nbytes bytes.
    evaluate
    (ExtCall ffi_name «ptr1» «len1» «ptr2» «len2»,s) = (res,t)∧
    well_behaved_ffi ffi_name s
                     (w2n (ffiBufferSize:'a word)) (dimword (:α))  /\
    FLOOKUP s.locals «ptr1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «len1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «ptr2» = SOME (ValWord ffiBufferAddr) ∧
    FLOOKUP s.locals «len2» = SOME (ValWord ffiBufferSize) ==>
    res = NONE ∧
    ∃bytes nbytes.
      t = ffi_return_state s ffi_name bytes nbytes
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [well_behaved_ffi_def] >>
  gs [evaluate_def] >>
  gs [read_bytearray_def] >>
  gs [read_bytearray_def, ffiBufferAddr_def] >>
  dxrule LESS_MOD >>
  strip_tac >> rfs [] >>
  pop_assum kall_tac >>
  rfs [ffiTheory.call_FFI_def] >>
  rveq >> fs [] >>
  gs [ffi_return_state_def] >>
  rveq >> gs[] >>
  qexists_tac ‘bytes’ >>
  qexists_tac ‘nbytes’ >>
  gs [state_component_equality,
      ffiTheory.ffi_state_component_equality]
QED


Theorem comp_output_term_correct:
  ∀s out cnds tclks dest wt s' t (clkvals:'a v list) clks.
    evalTerm s NONE
             (Tm (Output out) cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ∧
    well_behaved_ffi (strlit (toString out)) t
                     (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
    ∃bytes nbytes.
      evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with
         <|locals :=
           restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                  «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
           memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
           ffi := nffi_state t out bytes nbytes|>)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clock_bound_def, time_range_def] >>
  drule every_conj_spec >>
  strip_tac >>
  drule eval_term_clkvals_equiv_reset_clkvals >>
  disch_then (qspec_then ‘clks’ assume_tac) >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [compTerm_def] >>
  cases_on ‘wt’
  >- ( (* wait set is disabled *)
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def, eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
   ‘OPT_MMAP (λa. eval stInit a)
      (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
     qexists_tac ‘clkvals’ >> rfs [] >>
     fs [Abbr ‘stInit’] >>
     rfs [FLOOKUP_UPDATE]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [emptyConsts_def] >>
   fs [OPT_MMAP_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >>
   fs [eval_def] >>
   fs [indicesOf_def, waitTimes_def, minExp_def] >>
   pop_assum mp_tac >>
   rewrite_tac [OPT_MMAP_def] >>
   strip_tac >>
   fs [is_valid_value_def] >>
   fs [FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   drule ffi_eval_state_thm >>
   disch_then (qspecl_then
               [‘nbytes’, ‘bytes’] mp_tac) >>
   impl_tac
   >- (
    fs [FLOOKUP_UPDATE] >>
    fs [well_behaved_ffi_def]) >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   pop_assum kall_tac >>
   fs [ffi_return_state_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule maxClksSize_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [maxClksSize_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [nffi_state_def, restore_from_def] >>
   metis_tac []) >>
  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘emptyConsts (LENGTH wt)’ >>
  ‘(case wt of [] => Const 1w | v2::v3 => Const 0w) =
   (Const 0w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [panLangTheory.decs_def] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  rfs [] >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
  ‘OPT_MMAP (λa. eval stInit a)
   (resetTermClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
    qexists_tac ‘clkvals’ >> rfs [] >>
    fs [Abbr ‘stInit’] >>
    rfs [FLOOKUP_UPDATE]) >>
  fs [] >>
  pop_assum kall_tac >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  fs [eval_empty_const_eq_empty_vals] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [panLangTheory.nested_seq_def] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘eval stReset _’ >>
  fs [eval_def] >>
  (* waitimes eq eval diffs *)
  ‘OPT_MMAP (λa. eval stReset a)
   (waitTimes (MAP FST wt)
    (MAP (λn. Field n (Var «newClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ THE ∘ evalDiff
              (s with clocks := resetClocks s.clocks tclks)) wt)’ by (
    match_mp_tac calculate_wait_times_eq >>
    qexists_tac ‘resetClksVals s.clocks clks tclks’ >>
    rfs [Abbr ‘stReset’] >>
    rewrite_tac [FLOOKUP_UPDATE] >>
    fs [] >>
    fs [equiv_val_def] >>
    last_x_assum assume_tac >>
    drule fdom_reset_clks_eq_clks >>
    strip_tac >>
    rfs [valid_clks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs [] >>
    cases_on ‘e’ >> fs [] >>
    strip_tac >>
    fs [] >>
    match_mp_tac flookup_reset_clks_leq >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘is_valid_value tt _ wtval’ >>
  ‘is_valid_value tt «waitTimes» wtval’ by (
    fs [Abbr ‘tt’, Abbr ‘wtval’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    fs [emptyVals_def, emptyConsts_def] >>
    fs [MAP_MAP_o, GSYM MAP_K_REPLICATE, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (minExp _ es, stWait)’ >>
  ‘FLOOKUP stWait.locals «wakeUpAt» = SOME (ValWord 0w)’ by
    fs [Abbr ‘stWait’, FLOOKUP_UPDATE] >>
  drule evaluate_min_exp_eq >>
  disch_then (
    qspecl_then [
        ‘es’,
        ‘MAP (THE ∘ evalDiff (s with clocks := resetClocks s.clocks tclks)) wt’,
        ‘res''’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (
   rfs [] >>
   conj_tac
   >- (
    rw [] >>
    fs [Abbr ‘es’] >>
    fs [panLangTheory.var_exp_def]) >>
   conj_tac
   >- (
    fs [Abbr ‘stWait’, Abbr ‘es’] >>
    fs [Abbr ‘wtval’] >>
    fs [MAP_MAP_o] >>
    fs [MAPi_enumerate_MAP] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [LENGTH_enumerate] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    ‘EL n (enumerate 0 wt) = (n+0,EL n wt)’ by (
      match_mp_tac EL_enumerate >>
      fs []) >>
    fs [] >>
    pop_assum kall_tac >>
    fs [eval_def] >>
    fs [FLOOKUP_UPDATE] >>
    rveq >> rfs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL i (MAP ff wt) = ff (EL i wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’]) >>
   fs [EVERY_MAP, EVERY_MEM] >>
   gen_tac >>
   strip_tac >>
   cases_on ‘x’ >>
   fs [evalDiff_def, evalExpr_def] >>
   cases_on ‘MEM r tclks’
   >- (
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ assume_tac) >>
    fs [] >>
    fs [minusT_def] >>
    first_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
    fs []) >>
   rfs [valid_clks_def] >>
   rfs [EVERY_MEM] >>
   ‘MEM r clks’ by (
     ‘MEM r (MAP SND wt)’ by (
       fs [MEM_MAP] >>
       qexists_tac ‘(q,r)’ >> fs []) >>
     res_tac >> gs []) >>
   res_tac >> rfs [] >>
   drule reset_clks_not_mem_flookup_same >>
   disch_then (qspec_then ‘tclks’ mp_tac) >>
   rfs [] >>
   strip_tac >>
   fs [minusT_def] >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs [] >>
   strip_tac  >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs []) >>
  strip_tac >> fs [] >>
  ‘es ≠ []’ by fs [Abbr ‘wt’, Abbr ‘es’] >>
  fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  drule ffi_eval_state_thm >>
  disch_then (qspecl_then
              [‘nbytes’, ‘bytes’] mp_tac) >>
  impl_tac
  >- (
  fs [FLOOKUP_UPDATE] >>
  fs [well_behaved_ffi_def]) >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  pop_assum kall_tac >>
  fs [ffi_return_state_def] >>
  fs [evaluate_def] >>
  fs [eval_def] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
  fs [OPT_MMAP_def] >>
  fs [eval_def] >>
  fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
  rfs [] >>
  fs [panLangTheory.size_of_shape_def, panSemTheory.shape_of_def] >>
  fs [MAP_MAP_o] >>
  qmatch_asmsub_abbrev_tac ‘SUM ss’ >>
  ‘ss =
   MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals’ by (
    fs [Abbr ‘ss’] >>
    match_mp_tac shape_of_resetClksVals_eq >>
    rfs [equiv_val_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [MEM_MAP]) >>
  rfs [maxClksSize_def] >>
  qmatch_asmsub_abbrev_tac ‘ss = tt’ >>
  ‘SUM ss + 3 ≤ 32’ by fs [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [empty_locals_def] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  fs [restore_from_def] >>
  fs [retVal_def] >>
  fs [calculate_wtime_def] >>
  fs [nffi_state_def] >>
  metis_tac []
QED


Theorem comp_term_correct:
  ∀s io ioAct cnds tclks dest wt s' t (clkvals:'a v list) clks.
    evalTerm s io
             (Tm ioAct cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ⇒
    case (io,ioAct) of
     | (SOME _,Input n) =>
         evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
         (SOME (Return (retVal s clks tclks wt dest)),
          (* we can throw away the locals *)
          t with locals :=
          restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
     | (NONE, Output out) =>
         (well_behaved_ffi (strlit (toString out)) t
                           (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
          ∃bytes nbytes.
            evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
            (SOME (Return (retVal s clks tclks wt dest)),
             t with
               <|locals :=
                 restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                        «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
                 memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
                 ffi := nffi_state t out bytes nbytes|>))
     | (_,_) => F
Proof
  rw [] >>
  cases_on ‘ioAct’ >>
  cases_on ‘io’ >>
  fs [] >>
  TRY (fs[evalTerm_cases] >> NO_TAC)
  >- (
    drule eval_term_inpput_ios_same >>
    strip_tac >> rveq >>
    imp_res_tac comp_input_term_correct) >>
  imp_res_tac comp_output_term_correct
QED


Theorem comp_exp_correct:
  ∀s e n clks t:('a,'b)panSem$state clkvals.
    evalExpr s e = SOME n ∧
    EVERY (λck. MEM ck clks) (exprClks [] e) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compExp clks «clks» e) = SOME (ValWord (n2w n))
Proof
  ho_match_mp_tac evalExpr_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
    fs [evalExpr_def] >>
    fs [compExp_def] >>
    fs [eval_def])
  >- (
    fs [evalExpr_def, timeLangTheory.exprClks_def] >>
    fs [compExp_def] >>
    fs [equiv_val_def] >> rveq >> gs [] >>
    fs [eval_def] >>
    ‘findi m clks < LENGTH clks’ by (
      match_mp_tac MEM_findi >>
      gs []) >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘EL nn (MAP ff _)’ >>
    ‘EL nn (MAP ff clks) = ff (EL nn clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’, Abbr ‘nn’] >>
    pop_assum kall_tac >>
    ‘EL (findi m clks) clks = m’ by (
      match_mp_tac EL_findi >>
      gs []) >>
    fs []) >>
  qpat_x_assum ‘evalExpr _ _ = _’ mp_tac >>
  rewrite_tac [Once evalExpr_def] >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  strip_tac >>
  qpat_x_assum ‘EVERY _ (exprClks [] _)’ mp_tac >>
  once_rewrite_tac [timeLangTheory.exprClks_def] >>
  fs [] >>
  strip_tac >>
  ‘EVERY (λck. MEM ck clks) (exprClks [] e0) ∧
   EVERY (λck. MEM ck clks) (exprClks [] e')’ by (
    drule exprClks_accumulates >>
    fs [] >>
    strip_tac >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
  fs [] >>
  last_x_assum drule >>
  last_x_assum drule >>
  fs [] >>
  disch_then (qspecl_then [‘t’, ‘clkvals’] assume_tac) >>
  disch_then (qspecl_then [‘t’, ‘clkvals’] assume_tac) >>
  gs [] >>
  rewrite_tac [compExp_def] >>
  fs [eval_def] >>
  gs [OPT_MMAP_def] >>
  fs [wordLangTheory.word_op_def] >>
  match_mp_tac EQ_SYM >>
  rewrite_tac [Once evalExpr_def] >>
  fs [minusT_def] >>
  rveq >> gs [] >>
  drule n2w_sub >>
  fs []
QED


Theorem comp_condition_true_correct:
  ∀s cnd (t:('a,'b) panSem$state) clks clkvals.
    evalCond s cnd ∧
    EVERY (λe. case (evalExpr s e) of
               | SOME n => n < dimword (:α)
               | _ => F) (destCond cnd) ∧
    EVERY (λck. MEM ck clks) (condClks cnd) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compCondition clks «clks» cnd) = SOME (ValWord 1w)
Proof
  rw [] >>
  cases_on ‘cnd’ >>
  fs [evalCond_def, timeLangTheory.condClks_def,
      timeLangTheory.destCond_def, timeLangTheory.clksOfExprs_def] >>
  every_case_tac >> fs [] >>
  qpat_x_assum ‘_ < dimword (:α)’ mp_tac >>
  qpat_x_assum ‘_ < dimword (:α)’ assume_tac >>
  strip_tac >>
  dxrule LESS_MOD >>
  dxrule LESS_MOD >>
  strip_tac >> strip_tac
  >- (
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
     fs [] >>
     drule exprClks_accumulates >>
     fs []) >>
   strip_tac >>
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
   strip_tac >>
   fs [compCondition_def] >>
   fs [eval_def, OPT_MMAP_def] >>
   gs [] >>
   fs [asmTheory.word_cmp_def] >>
   gs [word_lo_n2w] >>
   gs [LESS_OR_EQ, wordLangTheory.word_op_def]) >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
  fs [] >>
  drule exprClks_accumulates >>
  fs []) >>
  strip_tac >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
  fs [EVERY_MEM] >>
  rw [] >>
  fs [] >>
  drule exprClks_sublist_accum >>
  fs []) >>
  strip_tac >>
  fs [compCondition_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [] >>
  fs [asmTheory.word_cmp_def] >>
  gs [word_lo_n2w]
QED


Theorem map_comp_conditions_true_correct:
  ∀cnds s (t:('a,'b) panSem$state) clks clkvals.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < dimword (:α)
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    MAP (eval t o compCondition clks «clks») cnds =
    MAP (SOME o (λx. ValWord 1w)) cnds
Proof
  Induct
  >- rw [] >>
  rpt gen_tac >>
  strip_tac >>
  fs [] >>
  drule comp_condition_true_correct >>
  fs [] >>
  disch_then drule_all >>
  strip_tac >>
  last_x_assum match_mp_tac >>
  gs [] >>
  qexists_tac ‘s’ >>
  gs []
QED

Theorem and_ones_eq_one:
  ∀n. word_op And (1w::REPLICATE n 1w) = SOME 1w
Proof
  Induct >>
  rw [] >>
  fs [wordLangTheory.word_op_def]
QED



Theorem comp_conditions_true_correct:
  ∀cnds s (t:('a,'b) panSem$state) clks clkvals.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < dimword (:α)
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compConditions clks «clks» cnds) = SOME (ValWord 1w)
Proof
  rw [] >>
  drule map_comp_conditions_true_correct >>
  gs [] >>
  disch_then drule_all >>
  strip_tac >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
  Induct >> rw []
  >- (
    fs [compConditions_def] >>
    fs [eval_def]) >>
  fs [compConditions_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [GSYM MAP_MAP_o] >>
  fs [GSYM opt_mmap_eq_some] >>
  ‘MAP (λx. ValWord 1w) cnds =
   REPLICATE (LENGTH cnds) (ValWord 1w)’ by (
    once_rewrite_tac [GSYM map_replicate] >>
    once_rewrite_tac [GSYM map_replicate] >>
    once_rewrite_tac [GSYM map_replicate] >>
    rewrite_tac  [MAP_MAP_o] >>
    rewrite_tac [MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >> fs [] >>
    ‘EL n (REPLICATE (LENGTH cnds) (1:num)) = 1’ by (
      match_mp_tac EL_REPLICATE >>
      fs []) >>
    fs []) >>
  fs [] >>
  rewrite_tac [ETA_AX] >>
  gs [] >>
  metis_tac [and_ones_eq_one]
QED


Theorem pickTerm_output_cons_correct:
  ∀s out cnds tclks dest wt s' t (clkvals:'a v list) clks tms.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    evalTerm s NONE (Tm (Output out) cnds tclks dest wt) s' ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < dimword (:α)
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    valid_clks clks tclks wt ∧
    FLOOKUP t.locals «event» = SOME (ValWord 0w) ∧
    toString dest IN FDOM t.code ∧
     well_behaved_ffi (strlit (toString out)) t
                      (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
    ∃bytes nbytes.
      evaluate (compTerms clks «clks» «event» (Tm (Output out) cnds tclks dest wt::tms), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with
         <|locals :=
           restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                  «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
           memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
           ffi := nffi_state t out bytes nbytes|>)
Proof
  rw [] >>
  drule_all comp_conditions_true_correct >>
  strip_tac >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  once_rewrite_tac [evaluate_def] >>
  gs [timeLangTheory.termConditions_def,
      eval_def,OPT_MMAP_def, ETA_AX, timeLangTheory.termAction_def] >>
  gs [event_match_def,compAction_def, eval_def, asmTheory.word_cmp_def,
      wordLangTheory.word_op_def] >>
  drule_all comp_output_term_correct >>
  fs []
QED


Theorem pickTerm_input_cons_correct:
  ∀s n cnds tclks dest wt s' t (clkvals:'a v list) clks tms.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    evalTerm s (SOME n) (Tm (Input n) cnds tclks dest wt) s' ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < dimword (:α)
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    valid_clks clks tclks wt ∧
    FLOOKUP t.locals «event» = SOME (ValWord (n2w (n + 1))) ∧
    n + 1 < dimword (:α) ∧
    toString dest IN FDOM t.code ⇒
    evaluate (compTerms clks «clks» «event» (Tm (Input n) cnds tclks dest wt::tms), t) =
    (SOME (Return (retVal s clks tclks wt dest)),
     t with locals :=
     restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
Proof
  rw [] >>
  drule_all comp_conditions_true_correct >>
  strip_tac >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  once_rewrite_tac [evaluate_def] >>
  gs [timeLangTheory.termConditions_def,
      eval_def,OPT_MMAP_def, ETA_AX, timeLangTheory.termAction_def] >>
  gs [event_match_def,compAction_def, eval_def, asmTheory.word_cmp_def,
      wordLangTheory.word_op_def] >>
  drule_all comp_input_term_correct >>
  fs []
QED


Theorem comp_condition_false_correct:
  ∀s cnd (t:('a,'b) panSem$state) clks clkvals.
    ~(evalCond s cnd) ∧
    EVERY (λe. case (evalExpr s e) of
               | SOME n => n < dimword (:α)
               | _ => F) (destCond cnd) ∧
    EVERY (λck. MEM ck clks) (condClks cnd) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compCondition clks «clks» cnd) = SOME (ValWord 0w)
Proof
  rw [] >>
  cases_on ‘cnd’ >>
  fs [evalCond_def, timeLangTheory.condClks_def,
      timeLangTheory.destCond_def, timeLangTheory.clksOfExprs_def] >>
  every_case_tac >> fs []
  >- (
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
     fs [] >>
     drule exprClks_accumulates >>
     fs []) >>
   strip_tac >>
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
   strip_tac >>
   fs [compCondition_def] >>
   fs [eval_def, OPT_MMAP_def] >>
   gs [] >>
   fs [asmTheory.word_cmp_def] >>
   gs [word_lo_n2w] >>
   fs [wordLangTheory.word_op_def]) >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    fs [] >>
    drule exprClks_accumulates >>
    fs []) >>
  strip_tac >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
  strip_tac >>
  fs [compCondition_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [] >>
  fs [asmTheory.word_cmp_def] >>
  gs [word_lo_n2w]
QED


Theorem comp_conditions_false_correct:
  ∀cnds s (t:('a,'b) panSem$state) clks clkvals.
    ~EVERY (λcnd. evalCond s cnd) cnds ∧
    EVERY (λcnd. EVERY (λe. ∃t. evalExpr s e = SOME t) (destCond cnd)) cnds ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < dimword (:α)
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compConditions clks «clks» cnds) = SOME (ValWord 0w)
Proof
  Induct
  >- (
    rw [] >>
    fs []) >>
  rpt gen_tac >>
  strip_tac >>
  fs []
  >- (
  imp_res_tac comp_condition_false_correct >>
  cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
  >- (
    imp_res_tac comp_conditions_true_correct >>
    fs [compConditions_def] >>
    gs [eval_def, OPT_MMAP_def, ETA_AX] >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
    Induct >> rw []
    >- (
      fs [compConditions_def] >>
      fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
    gs [compConditions_def, eval_def, OPT_MMAP_def] >>
    every_case_tac >> gs [] >>
    rveq >> gs [] >>
    every_case_tac >> gs [wordLangTheory.word_op_def] >>
    rveq >> gs [] >>
    metis_tac [EVERY_NOT_EXISTS]) >>
  fs []  >>
  last_x_assum drule_all >>
  strip_tac >>
  drule comp_condition_false_correct >>
  disch_then drule_all >>
  strip_tac >>
  fs [compConditions_def] >>
  fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def] >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
  Induct >> rw []
  >- (
    fs [compConditions_def] >>
    fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
  gs [compConditions_def, eval_def, OPT_MMAP_def] >>
  every_case_tac >> gs [] >>
  rveq >> gs [] >>
  every_case_tac >> gs [wordLangTheory.word_op_def] >>
  rveq >> gs [] >>
  metis_tac [EVERY_NOT_EXISTS]) >>
  last_x_assum drule_all >>
  strip_tac >>
  cases_on ‘evalCond s h’
  >- (
    drule comp_condition_true_correct >>
    disch_then drule_all >>
    strip_tac >>
    fs [compConditions_def] >>
    fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
    Induct >> rw []
    >- (
    fs [compConditions_def] >>
    fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
    gs [compConditions_def, eval_def, OPT_MMAP_def] >>
    every_case_tac >> gs [] >>
    rveq >> gs [] >>
    every_case_tac >> gs [wordLangTheory.word_op_def] >>
    rveq >> gs [] >>
    metis_tac [EVERY_NOT_EXISTS]) >>
  drule comp_condition_false_correct >>
  disch_then drule_all >>
  strip_tac >>
  fs [compConditions_def] >>
  fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
  Induct >> rw []
  >- (
  fs [compConditions_def] >>
  fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
  gs [compConditions_def, eval_def, OPT_MMAP_def] >>
  every_case_tac >> gs [] >>
  rveq >> gs [] >>
  every_case_tac >> gs [wordLangTheory.word_op_def] >>
  rveq >> gs [] >>
  metis_tac [EVERY_NOT_EXISTS]
QED

Definition conds_eval_lt_dimword_def:
  conds_eval_lt_dimword (:'a) s tms =
    EVERY (λtm.
            EVERY (λcnd.
                    EVERY (λe. case (evalExpr s e) of
                               | SOME n => n < dimword (:α)
                               | _ => F) (destCond cnd))
                  (termConditions tm)
          ) tms
End


Definition conds_clks_mem_clks_def:
  conds_clks_mem_clks clks tms =
    EVERY (λtm.
            EVERY (λcnd.
                    EVERY (λck. MEM ck clks) (condClks cnd))
                  (termConditions tm)
          ) tms
End

Definition terms_time_range_def:
  terms_time_range (:'a) tms =
    EVERY (λtm.
            time_range (termWaitTimes tm) (dimword (:'a))
          ) tms
End

Definition terms_valid_clocks_def:
  terms_valid_clocks clks tms  =
    EVERY (λtm.
            valid_clks clks (termClks tm) (termWaitTimes tm)
          ) tms
End

(*
  we could phrase this at the term's diff level instead of
  calculate_wtime, or may be thats fine
*)
Definition terms_wtimes_ffi_bound_def:
  terms_wtimes_ffi_bound (:'a) s tms n =
    EVERY (λtm.
            case calculate_wtime (resetOutput s) (termClks tm) (termWaitTimes tm) of
            | NONE => T
            | SOME wt => n + wt <  dimword (:'a)
          ) tms
End

Definition locs_in_code_def:
  locs_in_code fm tms =
    EVERY (λtm.
            toString (termDest tm) IN FDOM fm
          ) tms
End

Definition input_terms_actions_def:
  input_terms_actions (:'a) tms =
    EVERY (λn. n+1 < dimword (:'a))
          (terms_in_signals tms)
End


Definition out_signals_ffi_def:
  out_signals_ffi (t :('a, 'b) panSem$state) tms =
    EVERY (λout.
            well_behaved_ffi (strlit (toString out)) t
                             (w2n (ffiBufferSize:'a word)) (dimword (:α)))
          (terms_out_signals tms)
End


Theorem pick_term_thm:
  ∀s e tms s'.
    pickTerm s e tms s' ⇒
    (∀(t :('a, 'b) panSem$state) clks clkvals.
       conds_eval_lt_dimword (:'a) s tms ∧
       conds_clks_mem_clks clks tms ∧
       terms_time_range (:'a) tms ∧
       terms_valid_clocks clks tms ∧
       locs_in_code t.code tms ∧
       FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
       equiv_val s.clocks clks clkvals ∧
       maxClksSize clkvals ∧
       clock_bound s.clocks clks (dimword (:'a)) ∧
       input_terms_actions (:'a) tms ∧
       out_signals_ffi t tms ⇒
       (e = NONE ∧
        FLOOKUP t.locals «event» = SOME (ValWord 0w) ⇒
        ∃out cnds tclks dest wt.
          MEM (Tm (Output out) cnds tclks dest wt) tms ∧
          EVERY (λcnd. evalCond s cnd) cnds ∧
          evalTerm s NONE
                   (Tm (Output out) cnds tclks dest wt) s' ∧
          (* (∃tt. s.waitTime = SOME tt) ∧ *)
          ∃bytes nbytes.
            evaluate (compTerms clks «clks» «event» tms, t) =
            (SOME (Return (retVal s clks tclks wt dest)),
             t with
               <|locals :=
                 restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                        «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
                 memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
                 ffi := nffi_state t out bytes nbytes|>)) ∧
       (∀n. e = SOME n ∧ n+1 < dimword (:'a) ∧
            FLOOKUP t.locals «event» = SOME (ValWord (n2w (n+1))) ⇒
            ∃cnds tclks dest wt.
              MEM (Tm (Input n) cnds tclks dest wt) tms ∧
              EVERY (λcnd. evalCond s cnd) cnds ∧
              evalTerm s (SOME n)
                       (Tm (Input n) cnds tclks dest wt) s' ∧
              evaluate (compTerms clks «clks» «event» tms, t) =
              (SOME (Return (retVal s clks tclks wt dest)),
               t with locals :=
               restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])))
Proof
  ho_match_mp_tac pickTerm_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    MAP_EVERY qexists_tac
              [‘cnds’, ‘clks’, ‘dest’, ‘diffs'’] >>
    fs [] >>
    match_mp_tac pickTerm_input_cons_correct >>
    qexists_tac ‘s'’ >>
    qexists_tac ‘clkvals’ >>
    gs [] >>
    conj_tac
    >- gs [conds_eval_lt_dimword_def, timeLangTheory.termConditions_def] >>
    conj_tac
    >- gs [conds_clks_mem_clks_def, timeLangTheory.termConditions_def] >>
    conj_tac
    >- gs [terms_time_range_def, timeLangTheory.termWaitTimes_def] >>
    conj_tac
    >- gs [terms_valid_clocks_def, timeLangTheory.termClks_def,
           timeLangTheory.termWaitTimes_def] >>
    gs [locs_in_code_def, timeLangTheory.termDest_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    MAP_EVERY qexists_tac
              [‘out_signal’, ‘cnds’, ‘clks’, ‘dest’, ‘diffs'’] >>
    fs [] >>
    match_mp_tac pickTerm_output_cons_correct >>
    qexists_tac ‘s'’ >>
    qexists_tac ‘clkvals’ >>
    gs [] >>
    conj_tac
    >- gs [conds_eval_lt_dimword_def, timeLangTheory.termConditions_def] >>
    conj_tac
    >- gs [conds_clks_mem_clks_def, timeLangTheory.termConditions_def] >>
    conj_tac
    >- gs [terms_time_range_def, timeLangTheory.termWaitTimes_def] >>
    conj_tac
    >- gs [terms_valid_clocks_def, timeLangTheory.termClks_def,
           timeLangTheory.termWaitTimes_def] >>
    conj_tac
    >- gs [locs_in_code_def, timeLangTheory.termDest_def] >>
    gs [out_signals_ffi_def, timeLangTheory.terms_out_signals_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    cases_on ‘e’ >> fs []
    >- (
      rw [] >>
      fs [] >>
      last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
      gs [] >>
      impl_tac
      >- (
      gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
          terms_time_range_def, terms_valid_clocks_def,
          locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
      cases_on ‘ioAction’ >>
      gs [timeLangTheory.terms_out_signals_def,
          timeLangTheory.terms_in_signals_def]) >>
      strip_tac >>
      MAP_EVERY qexists_tac
                [‘out’, ‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
      fs [] >>
      MAP_EVERY qexists_tac
                [‘bytes’, ‘nbytes’] >>
      (* we can have a separate theorem *)
      fs [compTerms_def] >>
      fs [pick_term_def] >>
      once_rewrite_tac [evaluate_def] >>
      fs [timeLangTheory.termConditions_def] >>
      ‘eval t (compConditions clks' «clks» cnds) = SOME (ValWord 0w)’ by (
        match_mp_tac comp_conditions_false_correct >>
        gs [] >>
        qexists_tac ‘s’ >>
        gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
            timeLangTheory.termConditions_def]) >>
      gs [eval_def, OPT_MMAP_def] >>
      fs [timeLangTheory.termAction_def] >>
      cases_on ‘ioAction’ >>
      fs [event_match_def] >>
      gs [eval_def,compAction_def,
          asmTheory.word_cmp_def,
          wordLangTheory.word_op_def]) >>
    rw [] >>
    fs [] >>
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
    gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
        terms_time_range_def, terms_valid_clocks_def,
        locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
    cases_on ‘ioAction’ >>
    gs [timeLangTheory.terms_out_signals_def,
        timeLangTheory.terms_in_signals_def]) >>
    strip_tac >>
    MAP_EVERY qexists_tac
              [‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
    fs [] >>
    fs [compTerms_def] >>
    fs [pick_term_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [timeLangTheory.termConditions_def] >>
    ‘eval t (compConditions clks' «clks» cnds) = SOME (ValWord 0w)’ by (
      match_mp_tac comp_conditions_false_correct >>
      gs [] >>
      qexists_tac ‘s’ >>
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          timeLangTheory.termConditions_def]) >>
    gs [eval_def, OPT_MMAP_def] >>
    fs [timeLangTheory.termAction_def] >>
    cases_on ‘ioAction’ >>
    fs [event_match_def] >>
    gs [eval_def,compAction_def,
        asmTheory.word_cmp_def,
        wordLangTheory.word_op_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    rw [] >>
    gs []
    >- (
      last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
      gs [] >>
      impl_tac
      >- (
        gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
            terms_time_range_def, terms_valid_clocks_def,
            locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
        gs [timeLangTheory.terms_out_signals_def, timeLangTheory.terms_in_signals_def]) >>
      strip_tac >>
      MAP_EVERY qexists_tac
                [‘out’,‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
      fs [] >>
      fs [compTerms_def] >>
      fs [pick_term_def] >>
      fs [timeLangTheory.termConditions_def,
          timeLangTheory.termAction_def] >>
      fs [event_match_def, compAction_def] >>
      once_rewrite_tac [evaluate_def] >>
      fs [eval_def, OPT_MMAP_def] >>
      cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
      >- (
        drule comp_conditions_true_correct >>
        disch_then (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
        impl_tac
        >- (
          gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
              timeLangTheory.termConditions_def]) >>
        strip_tac >> fs [] >>
        gs [asmTheory.word_cmp_def] >>
        ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
          match_mp_tac LESS_MOD >>
          gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
        fs [] >>
        fs [wordLangTheory.word_op_def] >>
        metis_tac []) >>
      drule comp_conditions_false_correct >>
      disch_then (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
      impl_tac
      >- (
        gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
            timeLangTheory.termConditions_def] >>
        gs [EVERY_MEM] >>
        rw [] >>
        res_tac  >> gs [] >>
        every_case_tac >> gs []) >>
      strip_tac >> fs [] >>
      gs [asmTheory.word_cmp_def] >>
      ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
        match_mp_tac LESS_MOD >>
        gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
        fs [] >>
      fs [wordLangTheory.word_op_def] >>
      metis_tac []) >>
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
    gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
        terms_time_range_def, terms_valid_clocks_def,
        locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
    gs [timeLangTheory.terms_out_signals_def, timeLangTheory.terms_in_signals_def]) >>
    strip_tac >>
    MAP_EVERY qexists_tac
              [‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
    fs [] >>
    fs [compTerms_def] >>
    fs [pick_term_def] >>
    fs [timeLangTheory.termConditions_def,
        timeLangTheory.termAction_def] >>
    fs [event_match_def, compAction_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [eval_def, OPT_MMAP_def] >>
    cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
    >- (
    drule comp_conditions_true_correct >>
    disch_then (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          timeLangTheory.termConditions_def]) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
    drule comp_conditions_false_correct >>
    disch_then (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
      >- (
    gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    rw [] >>
    res_tac  >> gs [] >>
    every_case_tac >> gs []) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
  strip_tac >>
  rw [] >>
  gs [] >>
  last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
  gs [] >>
  impl_tac
  >- (
  gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
      terms_time_range_def, terms_valid_clocks_def,
      locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
  gs [timeLangTheory.terms_out_signals_def, timeLangTheory.terms_in_signals_def]) >>
  strip_tac >>
  MAP_EVERY qexists_tac
            [‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
  fs [] >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  fs [timeLangTheory.termConditions_def,
      timeLangTheory.termAction_def] >>
  fs [event_match_def, compAction_def] >>
  once_rewrite_tac [evaluate_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
  >- (
  drule comp_conditions_true_correct >>
  disch_then (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
        timeLangTheory.termConditions_def]) >>
  strip_tac >> fs [] >>
  gs [asmTheory.word_cmp_def] >>
  fs [wordLangTheory.word_op_def]) >>
  drule comp_conditions_false_correct >>
  disch_then (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
  gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
      timeLangTheory.termConditions_def] >>
  gs [EVERY_MEM] >>
  rw [] >>
  res_tac  >> gs [] >>
  every_case_tac >> gs []) >>
  strip_tac >> fs [] >>
  gs [asmTheory.word_cmp_def] >>
  fs [wordLangTheory.word_op_def]
QED


Theorem pick_term_dest_eq:
  ∀s e tms s'.
    pickTerm s e tms s' ⇒
    (e = NONE ⇒
     ∀out cnds tclks dest wt.
       MEM (Tm (Output out) cnds tclks dest wt) tms ∧
       EVERY (λcnd. evalCond s cnd) cnds ∧
       evalTerm s NONE (Tm (Output out) cnds tclks dest wt) s' ⇒
       dest = s'.location ∧
       (case wt of [] => s'.waitTime = NONE | _ => ∃nt. s'.waitTime = SOME nt)) ∧
    (∀n.
       e = SOME n ⇒
       ∀cnds tclks dest wt.
         MEM (Tm (Input n) cnds tclks dest wt) tms ∧
         EVERY (λcnd. evalCond s cnd) cnds ∧
         evalTerm s (SOME n) (Tm (Input n) cnds tclks dest wt) s' ⇒
         dest = s'.location ∧
         (case wt of [] => s'.waitTime = NONE | _ => ∃nt. s'.waitTime = SOME nt))
Proof
  ho_match_mp_tac pickTerm_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    fs [evalTerm_cases] >>
    every_case_tac >>
    fs [calculate_wtime_def, list_min_option_def] >>
    every_case_tac >> gs [] >>
    metis_tac []) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    fs [evalTerm_cases] >>
    every_case_tac >>
    gs [calculate_wtime_def, list_min_option_def] >>
    every_case_tac >> gs [] >>
    metis_tac []) >>
  strip_tac >>
  rpt gen_tac
  >- (
   strip_tac >>
   cases_on ‘e’ >> fs [] >>
   rw [] >> fs [] >>
   metis_tac [EVERY_NOT_EXISTS]) >>
  strip_tac >>
  cases_on ‘e’ >> fs [] >>
  rw [] >> fs [] >>
  metis_tac [EVERY_NOT_EXISTS]
QED

(*
Theorem pick_term_dest_eq:
  ∀s e tms s'.
    pickTerm s e tms s' ⇒
    (e = NONE ⇒
     ∀out cnds tclks dest wt.
       MEM (Tm (Output out) cnds tclks dest wt) tms ∧
       EVERY (λcnd. evalCond s cnd) cnds ∧
       evalTerm s NONE (Tm (Output out) cnds tclks dest wt) s' ⇒
       dest = s'.location) ∧
    (∀n.
       e = SOME n ⇒
       ∀cnds tclks dest wt.
         MEM (Tm (Input n) cnds tclks dest wt) tms ∧
         EVERY (λcnd. evalCond s cnd) cnds ∧
         evalTerm s (SOME n) (Tm (Input n) cnds tclks dest wt) s' ⇒
         dest = s'.location)
Proof
  ho_match_mp_tac pickTerm_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    fs [evalTerm_cases]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    fs [evalTerm_cases]) >>
  strip_tac >>
  rpt gen_tac
  >- (
   strip_tac >>
   cases_on ‘e’ >> fs [] >>
   rw [] >> fs [] >>
   metis_tac [EVERY_NOT_EXISTS]) >>
  strip_tac >>
  cases_on ‘e’ >> fs [] >>
  rw [] >> fs [] >>
  metis_tac [EVERY_NOT_EXISTS]
QED
*)
(* step theorems *)

Theorem state_rel_imp_time_seq_ffi:
  ∀cks s t.
    state_rel cks s (t:('a,time_input) panSem$state) ⇒
    time_seq t.ffi.ffi_state (dimword (:'a))
Proof
  rw [state_rel_def] >>
  pairarg_tac >> gs []
QED


Theorem state_rel_imp_ffi_vars:
  ∀cks s t.
    state_rel cks s (t:('a,time_input) panSem$state) ⇒
    ffi_vars t.locals
Proof
  rw [state_rel_def]
QED


Theorem state_rel_imp_equivs:
  ∀cks s t.
    state_rel cks s (t:('a,time_input) panSem$state) ⇒
    equivs t.locals s.location s.waitTime
Proof
  rw [state_rel_def]
QED

Theorem time_seq_mono:
  ∀m n f a.
    n ≤ m ∧
    time_seq f a ⇒
    FST (f n) ≤ FST (f m)
Proof
  Induct >>
  rw [] >>
  fs [time_seq_def] >>
  fs [LE] >>
  last_x_assum (qspecl_then [‘n’, ‘f’, ‘a’] mp_tac) >>
  impl_tac
  >- gs [] >>
  strip_tac >>
  ‘FST (f m) ≤ FST (f (SUC m))’ suffices_by gs [] >>
  last_x_assum (qspec_then ‘m’ mp_tac) >>
  gs []
QED



Theorem step_delay_eval_wait_not_zero:
  !t.
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 1w) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)) ∧
    (?tm. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord tm)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs []
QED


Theorem step_wait_delay_eval_wait_not_zero:
  !(t:('a,'b) panSem$state).
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
          ?wt. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord (n2w wt)) ∧
               tm < wt ∧
               wt < dimword (:α) ∧
               tm < dimword (:α)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [wait_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [active_low_def,
      wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs [] >>
  fs [asmTheory.word_cmp_def] >>
  fs [addressTheory.WORD_CMP_NORMALISE] >>
  fs [word_ls_n2w] >>
  ‘wt MOD dimword (:α) = wt’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  ‘tm MOD dimword (:α) = tm’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  fs []
QED


Theorem state_rel_imp_mem_config:
  ∀clks io s t.
    state_rel clks s t ==>
    mem_config t.memory t.memaddrs t.be
Proof
  rw [state_rel_def]
QED


Theorem state_rel_imp_systime_defined:
  ∀clks io s t.
    state_rel clks s t ==>
    ∃tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)
Proof
  rw [state_rel_def, time_vars_def] >>
  pairarg_tac >> fs []
QED

Theorem state_rel_imp_time_vars:
  ∀clks s t.
    state_rel clks s t ==>
    time_vars t.locals
Proof
  rw [state_rel_def]
QED

Definition mem_call_ffi_def:
  mem_call_ffi (:α) mem adrs be (ffi: (num -> num # num)) =
    write_bytearray
    ffiBufferAddr
    (get_bytes (:α) be ((n2w (FST (ffi 1))):'a word) ++
     get_bytes (:α) be ((n2w (SND (ffi 1))):'a word))
    mem adrs be
End


Definition ffi_call_ffi_def:
  ffi_call_ffi (:α) be ffi bytes =
    ffi with
        <|ffi_state := next_ffi ffi.ffi_state;
          io_events := ffi.io_events ++
          [IO_event "get_ffi" []
           (ZIP
            (bytes,
             get_bytes (:α) be ((n2w (FST (ffi.ffi_state (1:num)))):'a word) ++
             get_bytes (:α) be ((n2w (SND (ffi.ffi_state 1))):'a word)))]|>

End

Theorem length_get_bytes:
  ∀w be.
    LENGTH (get_bytes (:α) be w) = dimindex (:α) DIV 8
Proof
  rw [] >>
  fs [get_bytes_def]
QED


Theorem evaluate_ext_call:
  ∀(t :('a, time_input) panSem$state) res t' bytes.
    evaluate (ExtCall «get_ffi» «ptr1» «len1» «ptr2» «len2» ,t) = (res,t') ∧
    read_bytearray ffiBufferAddr (w2n (ffiBufferSize:α word))
                   (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes ∧
    t.ffi = build_ffi (:'a) t.be t.ffi.ffi_state t.ffi.io_events ∧
    ffi_vars t.locals ∧ labProps$good_dimindex (:'a) ⇒
    res = NONE ∧
    t' = t with
           <| memory := mem_call_ffi (:α) t.memory t.memaddrs t.be t.ffi.ffi_state
            ; ffi := ffi_call_ffi (:α) t.be t.ffi bytes|>
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [labPropsTheory.good_dimindex_def] >>
  (fs [evaluate_def, ffi_vars_def, read_bytearray_def] >>
   gs [build_ffi_def, ffiTheory.call_FFI_def] >>
   gs [ffiTheory.ffi_state_component_equality] >>
   fs [time_input_def] >>
   drule read_bytearray_LENGTH >>
   strip_tac >>
   fs [length_get_bytes] >>
   fs [ffiBufferSize_def] >>
   fs [bytes_in_word_def, dimword_def] >>
   rveq >>
   gs [mem_call_ffi_def, ffi_call_ffi_def])
QED

Theorem evaluate_assign_load:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr tm w.
    evaluate (Assign dst (Load One (Var trgt)),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    FLOOKUP t.locals dst = SOME (ValWord tm) ∧
    t.memory adr = Word w ∧
    adr ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def] >>
  gs [mem_load_def] >>
  gs [is_valid_value_def, shape_of_def]
QED


Theorem evaluate_assign_load_next_address:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr w.
    evaluate (Assign dst
              (Load One (Op Add [Var trgt ; Const bytes_in_word])),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    (∃tm. FLOOKUP t.locals dst = SOME (ValWord tm)) ∧
    t.memory (adr + bytes_in_word) = Word w ∧
    adr + bytes_in_word ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, OPT_MMAP_def] >>
  gs [mem_load_def, wordLangTheory.word_op_def] >>
  gs [is_valid_value_def, shape_of_def]
QED


Theorem evaluate_assign_compare_next_address:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr n.
    evaluate (Assign dst
              (Cmp Equal
               (Load One (Op Add [Var trgt ; Const bytes_in_word]))
               (Const n)),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    (∃tm. FLOOKUP t.locals dst = SOME (ValWord tm)) ∧
    t.memory (adr + bytes_in_word) = Word n ∧
    adr + bytes_in_word ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord 1w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, OPT_MMAP_def] >>
  gs [mem_load_def, wordLangTheory.word_op_def] >>
  gs [is_valid_value_def, shape_of_def] >>
  fs [asmTheory.word_cmp_def]
QED


Theorem time_seq_add_holds:
  ∀f m p.
    time_seq f m ⇒
    time_seq (λn. f (p + n)) m
Proof
  rw [time_seq_def] >>
  fs [] >>
  last_x_assum (qspec_then ‘p + n’ assume_tac) >>
  fs [ADD_SUC]
QED

(* good be more generic, but its a trivial theorem *)
Theorem read_bytearray_some_bytes_for_ffi:
  ∀m adrs be.
    labProps$good_dimindex (:'a) ∧
    ffiBufferAddr ∈ adrs ∧
    bytes_in_word + ffiBufferAddr ∈ adrs ∧
    (∃w. m ffiBufferAddr = Word w) ∧
    (∃w. m (bytes_in_word + ffiBufferAddr) = Word w) ⇒
    ∃bytes.
      read_bytearray (ffiBufferAddr:'a word) (w2n (ffiBufferSize:'a word))
                     (mem_load_byte m adrs be) = SOME bytes
Proof
  rw [] >>
  gs [labPropsTheory.good_dimindex_def]
  >- (
    gs [ffiBufferSize_def, bytes_in_word_def] >>
    ‘8 MOD dimword (:α) = 8’ by gs [dimword_def] >>
    gs [] >>
    pop_assum kall_tac >>
    qmatch_goalsub_abbrev_tac ‘read_bytearray _ n _’ >>
    pop_assum (mp_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac [‘m’, ‘adrs’, ‘be’, ‘w’, ‘w'’, ‘n’] >>
    Induct
    >- (rw [] >> fs []) >>
    rpt gen_tac >>
    rpt strip_tac >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n'’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n'’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n'’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    cases_on ‘n’ >- fs [] >>
    rewrite_tac [read_bytearray_def] >>
    fs [] >>
    cases_on ‘n'’ >> fs [] >>
    fs [ffiBufferAddr_def] >>
    fs [mem_load_byte_def] >>
    ‘byte_align (4000w:'a word) = 4000w ∧
     byte_align (4001w:'a word) = 4000w ∧
     byte_align (4002w:'a word) = 4000w ∧
     byte_align (4003w:'a word) = 4000w ∧
     byte_align (4004w:'a word) = 4004w ∧
     byte_align (4005w:'a word) = 4004w ∧
     byte_align (4006w:'a word) = 4004w ∧
     byte_align (4007w:'a word) = 4004w’ by (
      fs [byte_align_def] >>
      fs [align_def] >>
      EVAL_TAC >>
      gs [dimword_def] >>
      EVAL_TAC) >>
    fs [read_bytearray_def]) >>
  gs [ffiBufferSize_def, bytes_in_word_def] >>
  ‘16 MOD dimword (:α) = 16’ by gs [dimword_def] >>
  gs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘read_bytearray _ n _’ >>
  pop_assum (mp_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘m’, ‘adrs’, ‘be’, ‘w’, ‘w'’, ‘n’] >>
  Induct
  >- (rw [] >> fs []) >>
  rpt gen_tac >>
  rpt strip_tac >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n'’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  cases_on ‘n’ >- fs [] >>
  rewrite_tac [read_bytearray_def] >>
  fs [] >>
  cases_on ‘n'’ >> fs [] >>
  fs [ffiBufferAddr_def] >>
  fs [mem_load_byte_def] >>
  ‘byte_align (4000w:'a word) = 4000w ∧
   byte_align (4001w:'a word) = 4000w ∧
   byte_align (4002w:'a word) = 4000w ∧
   byte_align (4003w:'a word) = 4000w ∧
   byte_align (4004w:'a word) = 4000w ∧
   byte_align (4005w:'a word) = 4000w ∧
   byte_align (4006w:'a word) = 4000w ∧
   byte_align (4007w:'a word) = 4000w’ by (
    fs [byte_align_def] >>
    fs [align_def] >>
    EVAL_TAC >>
    gs [dimword_def] >>
    EVAL_TAC) >>
  ‘byte_align (4008w:'a word) = 4008w ∧
   byte_align (4009w:'a word) = 4008w ∧
   byte_align (4010w:'a word) = 4008w ∧
   byte_align (4011w:'a word) = 4008w ∧
   byte_align (4012w:'a word) = 4008w ∧
   byte_align (4013w:'a word) = 4008w ∧
   byte_align (4014w:'a word) = 4008w ∧
   byte_align (4015w:'a word) = 4008w’ by (
    fs [byte_align_def] >>
    fs [align_def] >>
    EVAL_TAC >>
    gs [dimword_def] >>
    EVAL_TAC) >>
  fs [read_bytearray_def]
QED


Definition mem_read_ffi_results_def:
  mem_read_ffi_results  (:'a) ffi (cycles:num) ⇔
  ∀i (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state).
    i < cycles ∧
    t.ffi.ffi_state = nexts_ffi i ffi ∧
    evaluate
    (ExtCall «get_ffi» «ptr1» «len1» «ptr2» «len2» , t) =
    (NONE,t') ⇒
    t'.memory ffiBufferAddr =
    Word (n2w (FST (nexts_ffi i ffi 1))) ∧
    t'.memory (bytes_in_word + ffiBufferAddr) =
    Word (n2w (SND (nexts_ffi i ffi 1)))
End


Theorem step_delay_loop:
  !cycles prog d s s' (t:('a,time_input) panSem$state) ck_extra.
    step prog (LDelay d) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    delay_rep (dimword (:α)) d t.ffi.ffi_state cycles ∧
    wakeup_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state cycles ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event» =  SOME (ValWord 0w) ∧
    labProps$good_dimindex (:'a) ==>
    ?ck t'.
      evaluate (wait_input_time_limit, t with clock := t.clock + ck) =
      evaluate (wait_input_time_limit, t' with clock := t'.clock + ck_extra) ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) s' t' ∧
      t'.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      FLOOKUP t'.locals «event» =  SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «taskRet» = FLOOKUP t.locals «taskRet» ∧
      FLOOKUP t'.locals «sysTime»  =
        SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles))))
Proof
  Induct_on ‘cycles’ >>
  fs []
  >- (
    rw [] >>
    fs [delay_rep_def] >>
    ‘d = 0’ by fs [] >>
    fs [] >>
    pop_assum kall_tac >>
    fs [step_cases] >>
    fs [delay_clocks_def, mkState_def] >>
    rveq >> gs [] >>
    fs [fmap_to_alist_eq_fm] >>
    qexists_tac ‘ck_extra’ >> fs [] >>
    qexists_tac ‘t’ >> fs [] >>
    gs [state_rel_def, nexts_ffi_def, GSYM ETA_AX] >>
    pairarg_tac >> gs []) >>
  rw [] >>
  ‘∃sd. sd ≤ d ∧
        delay_rep (dimword (:α)) sd t.ffi.ffi_state cycles’ by (
    fs [delay_rep_def] >>
    imp_res_tac state_rel_imp_time_seq_ffi >>
    ‘FST (t.ffi.ffi_state 0) ≤ FST (t.ffi.ffi_state cycles)’ by (
      match_mp_tac time_seq_mono >>
      qexists_tac ‘(dimword (:α))’ >>
      fs []) >>
    fs [time_seq_def] >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    strip_tac >> strip_tac >>
    gs [] >>
    qexists_tac ‘d - d'’ >>
    gs [] >>
    qexists_tac ‘st’ >> fs []) >>
  qpat_x_assum ‘step _ _ _ _’ mp_tac >>
  rewrite_tac [step_cases] >>
  strip_tac >>
  fs [] >> rveq
  >- (
    ‘step prog (LDelay sd) s
     (mkState (delay_clocks s.clocks sd) s.location NONE NONE)’ by (
      gs [mkState_def] >>
      fs [step_cases, mkState_def]) >>
    last_x_assum drule >>
    (* ck_extra *)
    disch_then (qspecl_then [‘t’, ‘ck_extra + 1’] mp_tac) >>
    impl_tac
    >- (
      gs [mkState_def, wakeup_rel_def, mem_read_ffi_results_def] >>
      rpt gen_tac >>
      strip_tac >>
      last_x_assum (qspecl_then [‘i’,‘t'’, ‘t''’] mp_tac) >>
      gs []) >>
    strip_tac >> fs [] >>
    ‘(mkState (delay_clocks s.clocks d) s.location NONE NONE).ioAction =
     NONE’ by fs [mkState_def] >>
    fs [] >>
    pop_assum kall_tac >>
    ‘(mkState (delay_clocks s.clocks sd) s.location NONE NONE).ioAction =
     NONE’ by fs [mkState_def] >>
    fs [] >>
    pop_assum kall_tac >>
    qexists_tac ‘ck’ >>
    fs [] >>
    fs [wait_input_time_limit_def] >>
    rewrite_tac [Once evaluate_def] >>
    drule step_delay_eval_wait_not_zero >>
    impl_tac
    >- (
      gs [state_rel_def, mkState_def, equivs_def, time_vars_def, active_low_def] >>
      pairarg_tac >> gs []) >>
    strip_tac >>
    gs [eval_upd_clock_eq] >>
    (* evaluating the function *)
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    fs [dec_clock_def] >>
    ‘state_rel (clksOf prog)
     (mkState (delay_clocks s.clocks sd) s.location NONE NONE)
     (t' with clock := ck_extra + t'.clock)’ by gs [state_rel_def] >>
    qpat_x_assum ‘state_rel _ _ t'’ kall_tac >>
    rewrite_tac [Once check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule state_rel_imp_mem_config >>
    rewrite_tac [Once mem_config_def] >>
    strip_tac >>
    fs [] >>
    ‘∃bytes.
       read_bytearray ffiBufferAddr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte t'.memory t'.memaddrs t'.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      gs []) >>
    drule evaluate_ext_call >>
    disch_then (qspec_then ‘bytes’ mp_tac) >>
    impl_tac
    >- (
      gs [state_rel_def] >>
      pairarg_tac >> gs []) >>
    strip_tac >> gs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    drule state_rel_imp_ffi_vars >>
    strip_tac >>
    pop_assum mp_tac >>
    rewrite_tac [Once ffi_vars_def] >>
    strip_tac >>
    drule state_rel_imp_systime_defined >>
    strip_tac >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory ffiBufferAddr = Word (n2w (FST(t'.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      gs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘cycles’,
        ‘t' with clock := ck_extra + t'.clock’,
        ‘ft’] mp_tac)>>
      impl_tac
      >- gs [Abbr ‘ft’] >>
      strip_tac >>
      gs [Abbr ‘ft’]) >>
    drule evaluate_assign_load >>
    gs [] >>
    disch_then (qspecl_then
                [‘ffiBufferAddr’, ‘tm’,
                 ‘n2w (FST (t'.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      gs [Abbr ‘nt’] >>
      fs [state_rel_def]) >>
    strip_tac >> fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* reading input to the variable event *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
    ‘nnt.memory (ffiBufferAddr +  bytes_in_word) =
     Word (n2w (SND(t'.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nnt’, Abbr ‘nt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      gs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘cycles’,
        ‘t' with clock := ck_extra + t'.clock’,
        ‘ft’] mp_tac)>>
      impl_tac
      >- gs [Abbr ‘ft’] >>
      strip_tac >>
      gs [Abbr ‘ft’]) >>
    gs [] >>
    drule evaluate_assign_load_next_address >>
    gs [] >>
    disch_then (qspecl_then
                [‘ffiBufferAddr’,
                 ‘n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      gs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      gs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >>
    gs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* isInput *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
    ‘nnnt.memory (ffiBufferAddr +  bytes_in_word) =
     Word (n2w (SND(t'.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
    gs [] >>
    ‘nnnt.memory (ffiBufferAddr +  bytes_in_word) = Word 0w’ by (
      gs [delay_rep_def] >>
      fs [nexts_ffi_def]) >>
    fs [] >>
    drule evaluate_assign_compare_next_address >>
    gs [] >>
    disch_then (qspecl_then [‘ffiBufferAddr’] mp_tac) >>
    impl_tac
    >- (
      gs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      gs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >>
    gs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    strip_tac >> fs [] >>
    rveq >> gs [] >>
    unabbrev_all_tac >>
    gs [] >>
    qmatch_goalsub_abbrev_tac ‘evaluate (_, nt)’ >>
    qexists_tac ‘nt with clock := t'.clock’ >>
    fs [] >>
    gs [Abbr ‘nt’] >>
    reverse conj_tac
    >- (
      fs [ffi_call_ffi_def] >>
      fs [nexts_ffi_def, next_ffi_def, FLOOKUP_UPDATE] >>
      fs [ADD1]) >>
    (* proving state rel *)
    gs [state_rel_def, mkState_def] >>
    conj_tac
    (* equivs *)
    >- gs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
    conj_tac
    >- gs [ffi_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- gs [time_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- gs [mem_config_def, mem_call_ffi_def] >>
    conj_tac
    >- (
      (* clock_bound *)
      qpat_x_assum ‘clock_bound s.clocks _ _’ assume_tac >>
      gs [clock_bound_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      strip_tac >>
      fs [] >>
      fs [delay_clocks_def] >>
      qexists_tac ‘d+n’ >>
      gs [] >>
      conj_tac
      >- (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(ck',n)’ >>
        fs []) >>
      gs [delay_rep_def] >>
      qpat_x_assum ‘_ (t.ffi.ffi_state 0)’ assume_tac >>
      pairarg_tac >> fs [] >>
      fs [clocks_rel_def, clkvals_rel_def] >>
      gs [EVERY_MEM] >>
      first_x_assum (qspec_then ‘ck'’ assume_tac) >>
      gs []) >>
    pairarg_tac >> gs [] >>
    conj_tac
    >- (
      fs [ffi_call_ffi_def, build_ffi_def] >>
      fs [ffiTheory.ffi_state_component_equality] >>
      last_x_assum assume_tac >>
      pairarg_tac >>
      fs [] >>
      pairarg_tac >>
      fs []) >>
    conj_tac
    >- (
      (* time_seq holds *)
      gs [ffi_call_ffi_def,
          nexts_ffi_def, next_ffi_def] >>
      qpat_x_assum ‘_ (t.ffi.ffi_state 0)’ mp_tac >>
      pairarg_tac >> gs [] >>
      strip_tac >>
      drule time_seq_add_holds >>
      disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
      fs [])  >>
    (* clocks_rel *)
    qpat_x_assum ‘_ (nexts_ffi _ _ _)’ assume_tac >>
    gs [clocks_rel_def, FLOOKUP_UPDATE,
        nexts_ffi_def, ffi_call_ffi_def, next_ffi_def, time_seq_def] >>
    pairarg_tac >> gs [] >> rveq >> gs [] >>
    qexists_tac ‘ns’ >>
    fs [] >>
    fs [clkvals_rel_def] >>
    conj_tac
    >- (
      fs [MAP_EQ_EVERY2] >>
      fs [LIST_REL_EL_EQN] >>
      rw [] >>
      pairarg_tac >> fs [] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      (* shortcut *)
      ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
        drule EL_ZIP >>
        disch_then (qspec_then ‘n’ mp_tac) >>
        gs [] >>
        strip_tac >>
        gs [clock_bound_def] >>
        imp_res_tac every_conj_spec >>
        fs [EVERY_MEM] >>
        fs [MEM_EL] >>
        first_x_assum (qspec_then ‘x’ mp_tac) >>
        fs [] >>
        impl_tac >- metis_tac [] >>
        gs [FDOM_FLOOKUP]) >>
      fs [delay_clocks_def] >>
      ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
       x = SOME (d + xn)’ by (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(x,xn)’ >>
        fs []) >>
      fs [] >>
      ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
       x = SOME (sd + xn)’ by (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(x,xn)’ >>
        fs []) >>
      fs [] >>
      fs [ffi_call_ffi_def, next_ffi_def] >>
      qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
      qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
      qpat_x_assum ‘sd ≤ d’ assume_tac >>
      gs [delay_rep_def] >>
      gs [ADD1]) >>
    (* repetition *)
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum (qspec_then ‘x’ assume_tac) >>
    gs [] >>
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      gs [clock_bound_def] >>
      gs [EVERY_MEM] >>
      rw [] >> gs [] >>
      last_x_assum (qspec_then ‘x’ assume_tac) >>
      gs []) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    gs [delay_rep_def] >>
    gs [ADD1]) >>
  ‘step prog (LDelay sd) s
   (mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w - sd)))’ by (
    gs [mkState_def] >>
    fs [step_cases, mkState_def]) >>
  last_x_assum drule >>
  (* ck_extra *)
  disch_then (qspecl_then [‘t’, ‘ck_extra + 1’] mp_tac) >>
  impl_tac
  >- (
    gs [mkState_def, wakeup_rel_def] >>
    gs [delay_rep_def] >>
    gs [mem_read_ffi_results_def] >>
    rpt gen_tac >>
    strip_tac >>
    last_x_assum (qspecl_then [‘i’,‘t'’, ‘t''’] mp_tac) >>
    gs []) >>
  strip_tac >> fs [] >>
  ‘(mkState (delay_clocks s.clocks d) s.location NONE (SOME (w - d))).ioAction =
   NONE’ by fs [mkState_def] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘(mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w - sd))).ioAction =
   NONE’ by fs [mkState_def] >>
  fs [] >>
  pop_assum kall_tac >>
  qexists_tac ‘ck’ >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  drule step_wait_delay_eval_wait_not_zero >>
  impl_tac
  >- (
    conj_tac
    >- gs [state_rel_def, mkState_def, equivs_def, active_low_def] >>
    gs [] >>
    gs [wakeup_rel_def, delay_rep_def] >>
    qexists_tac ‘sd + FST (t.ffi.ffi_state 0)’ >>
    gs [] >>
    qexists_tac ‘w + FST (t.ffi.ffi_state 0)’ >>
    gs []) >>
  strip_tac >>
  gs [eval_upd_clock_eq] >>
  (* evaluating the function *)
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  fs [dec_clock_def] >>
  ‘state_rel (clksOf prog)
   (mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w − sd)))
   (t' with clock := ck_extra + t'.clock)’ by gs [state_rel_def] >>
  qpat_x_assum ‘state_rel _ _ t'’ kall_tac >>
  rewrite_tac [Once check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule state_rel_imp_mem_config >>
  rewrite_tac [Once mem_config_def] >>
  strip_tac >>
  ‘∃bytes.
     read_bytearray ffiBufferAddr (w2n (ffiBufferSize:'a word))
                    (mem_load_byte t'.memory t'.memaddrs t'.be) = SOME bytes’ by (
    match_mp_tac read_bytearray_some_bytes_for_ffi >>
    gs []) >>
  drule evaluate_ext_call >>
  disch_then (qspec_then ‘bytes’ mp_tac) >>
  impl_tac
  >- (
    gs [state_rel_def] >>
    pairarg_tac >> gs []) >>
  strip_tac >> gs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  drule state_rel_imp_ffi_vars >>
  strip_tac >>
  pop_assum mp_tac >>
  rewrite_tac [Once ffi_vars_def] >>
  strip_tac >>
  drule state_rel_imp_systime_defined >>
  strip_tac >>
  (* reading systime *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
  ‘nt.memory ffiBufferAddr = Word (n2w (FST(t'.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    gs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum
    (qspecl_then
     [‘cycles’,
      ‘t' with clock := ck_extra + t'.clock’,
      ‘ft’] mp_tac)>>
    impl_tac
    >- gs [Abbr ‘ft’] >>
    strip_tac >>
    gs [Abbr ‘ft’]) >>
  drule evaluate_assign_load >>
  gs [] >>
  disch_then (qspecl_then
              [‘ffiBufferAddr’, ‘tm’,
               ‘n2w (FST (t'.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    gs [Abbr ‘nt’] >>
    fs [state_rel_def]) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  (* reading input to the variable event *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
  ‘nnt.memory (ffiBufferAddr +  bytes_in_word) =
   Word (n2w (SND(t'.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nnt’, Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    gs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum
    (qspecl_then
     [‘cycles’,
      ‘t' with clock := ck_extra + t'.clock’,
      ‘ft’] mp_tac)>>
    impl_tac
    >- gs [Abbr ‘ft’] >>
    strip_tac >>
    gs [Abbr ‘ft’]) >>
  gs [] >>
  drule evaluate_assign_load_next_address >>
  gs [] >>
  disch_then (qspecl_then
              [‘ffiBufferAddr’,
               ‘n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
  gs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
  gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
  gs [delay_rep_def, nexts_ffi_def]) >>
  strip_tac >>
  gs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  (* isInput *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
  ‘nnnt.memory (ffiBufferAddr +  bytes_in_word) =
   Word (n2w (SND(t'.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
  gs [] >>
  ‘nnnt.memory (ffiBufferAddr +  bytes_in_word) = Word 0w’ by (
    gs [delay_rep_def] >>
    fs [nexts_ffi_def]) >>
  fs [] >>
  drule evaluate_assign_compare_next_address >>
  gs [] >>
  disch_then (qspecl_then [‘ffiBufferAddr’] mp_tac) >>
  impl_tac
  >- (
    gs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
    gs [delay_rep_def, nexts_ffi_def]) >>
  strip_tac >>
  gs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  strip_tac >> fs [] >>
  rveq >> gs [] >>
  unabbrev_all_tac >>
  gs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_, nt)’ >>
  qexists_tac ‘nt with clock := t'.clock’ >>
  fs [] >>
  gs [Abbr ‘nt’] >>
  reverse conj_tac
  >- (
    fs [ffi_call_ffi_def] >>
    fs [nexts_ffi_def, next_ffi_def] >>
    fs [FLOOKUP_UPDATE] >>
    gs [ADD1]) >>
  (* proving state rel *)
  gs [state_rel_def, mkState_def] >>
  conj_tac
  (* equivs *)
  >- gs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
  conj_tac
  >- gs [ffi_vars_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- gs [time_vars_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- gs [mem_config_def, mem_call_ffi_def] >>
  conj_tac
  >- (
    (* clock_bound *)
    qpat_x_assum ‘clock_bound s.clocks _ _’ assume_tac >>
    gs [clock_bound_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum drule >>
    strip_tac >>
    fs [] >>
    fs [delay_clocks_def] >>
    qexists_tac ‘d+n’ >>
    gs [] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(ck',n)’ >>
      fs []) >>
    gs [delay_rep_def] >>
    last_x_assum assume_tac >>
    pairarg_tac >> fs [] >>
    fs [clocks_rel_def, clkvals_rel_def] >>
    gs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘ck'’ assume_tac) >>
    gs []) >>
  pairarg_tac >> gs [] >>
  conj_tac
  >- (
    fs [ffi_call_ffi_def, build_ffi_def] >>
    fs [ffiTheory.ffi_state_component_equality] >>
    last_x_assum assume_tac >>
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs []) >>
  conj_tac
  >- (
    (* time_seq holds *)
    gs [ffi_call_ffi_def,
        nexts_ffi_def, next_ffi_def] >>
    last_x_assum mp_tac >>
    pairarg_tac >> gs [] >>
    strip_tac >>
    drule time_seq_add_holds >>
    disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
    fs [])  >>
  gs [clocks_rel_def, FLOOKUP_UPDATE, nexts_ffi_def,
      ffi_call_ffi_def, next_ffi_def, time_seq_def] >>
  pairarg_tac >> gs [] >> rveq >> gs [] >>
  qexists_tac ‘ns’ >>
  fs [] >>
  fs [clkvals_rel_def] >>
  conj_tac
  >- (
    fs [MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    last_x_assum drule >>
    fs [] >>
    strip_tac >>
    (* shortcut *)
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      drule EL_ZIP >>
      disch_then (qspec_then ‘n’ mp_tac) >>
      gs [] >>
      strip_tac >>
      gs [clock_bound_def] >>
      imp_res_tac every_conj_spec >>
      fs [EVERY_MEM] >>
      fs [MEM_EL] >>
      first_x_assum (qspec_then ‘x’ mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >>
      gs [FDOM_FLOOKUP]) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    gs [delay_rep_def] >>
    gs [ADD1]) >>
  (* repetition *)
  fs [EVERY_MEM] >>
  rw [] >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  gs [] >>
  ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
    gs [clock_bound_def] >>
    gs [EVERY_MEM] >>
    rw [] >> gs [] >>
    last_x_assum (qspec_then ‘x’ assume_tac) >>
    gs []) >>
  fs [delay_clocks_def] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
   x = SOME (d + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
   x = SOME (sd + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  fs [ffi_call_ffi_def, next_ffi_def] >>
  qpat_x_assum ‘delay_rep _ d _ _’ assume_tac >>
  qpat_x_assum ‘delay_rep _ sd _ _’ assume_tac >>
  qpat_x_assum ‘sd ≤ d’ assume_tac >>
  gs [delay_rep_def] >>
  gs [ADD1]
QED


Theorem evaluate_seq_fst:
  evaluate (p, t) = evaluate (p, t') ⇒
  evaluate (Seq p q, t) = evaluate (Seq p q, t')
Proof
  rw [] >>
  fs [evaluate_def]
QED


Theorem step_delay:
  !cycles prog d s s' (t:('a,time_input) panSem$state) ck_extra.
    step prog (LDelay d) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    delay_rep (dimword (:α)) d t.ffi.ffi_state cycles ∧
    wakeup_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state cycles ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event» =  SOME (ValWord 0w) ∧
    labProps$good_dimindex (:'a) ==>
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      evaluate (task_controller (nClks prog), t' with clock := t'.clock + ck_extra) ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) s' t' ∧
      t'.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      FLOOKUP t'.locals «event» =  SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «taskRet» = FLOOKUP t.locals «taskRet» ∧
      FLOOKUP t'.locals «sysTime»  =
        SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles))))
Proof
  rw [] >>
  fs [task_controller_def] >>
  fs [panLangTheory.nested_seq_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  imp_res_tac step_delay_loop >>
  first_x_assum (qspec_then ‘ck_extra’ assume_tac) >>
  fs [] >>
  drule evaluate_seq_fst >>
  disch_then (qspec_then ‘q’ assume_tac) >>
  qexists_tac ‘ck’ >> fs [] >>
  qexists_tac ‘t'’ >> fs []
QED


(*
Definition output_rep_def:
  output_rep m wt (seq:time_input) ⇔
    FST (seq 0) = wt ∧
    FST (seq 0) < m ∧
    ¬SND (seq 0)
End
*)

Theorem step_input_eval_wait_zero:
  !t.
    FLOOKUP t.locals «isInput» = SOME (ValWord 0w) ∧
    (?tm. FLOOKUP t.locals «waitSet» = SOME (ValWord tm)) ∧
    (?st. FLOOKUP t.locals «sysTime» = SOME (ValWord st)) ∧
    (?wt. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord wt)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w = 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def]
QED


Theorem step_delay_eval_wait_zero:
  !t st.
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
    FLOOKUP t.locals «sysTime» = SOME (ValWord st) ∧
    FLOOKUP t.locals «wakeUpAt» = SOME (ValWord st) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w = 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def] >>
  fs [asmTheory.word_cmp_def]
QED

Theorem eval_normalisedClks:
  ∀t st ns.
    FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w st)) ∧
    FLOOKUP t.locals «clks» = SOME (Struct (MAP (ValWord o n2w) ns)) ∧
    EVERY (λn. n ≤ st) ns ⇒
      OPT_MMAP (eval t) (normalisedClks «sysTime» «clks» (LENGTH ns)) =
      SOME (MAP (λ(x,y). ValWord (n2w (x-y))) (ZIP (REPLICATE (LENGTH ns) st,ns)))
     (* MAP is better for reasoning than MAP2*)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [normalisedClks_def] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- fs [mkClks_def, fieldsOf_def] >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- fs [mkClks_def, fieldsOf_def] >>
  rw [] >>
  qmatch_goalsub_abbrev_tac ‘MAP2 ff xs ys’ >>
  ‘EL n (MAP2 ff xs ys) = ff (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    fs []) >>
  unabbrev_all_tac >>
  gs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff (ZIP (xs,ys))’ >>
  ‘EL n (MAP ff (ZIP (xs,ys))) = ff (EL n (ZIP (xs,ys)))’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs [mkClks_def]) >>
  unabbrev_all_tac >>
  gs [] >>
  fs [mkClks_def, fieldsOf_def] >>
  ‘EL n (ZIP (REPLICATE (LENGTH ns) st,ns)) =
   (EL n (REPLICATE (LENGTH ns) st),EL n ns)’ by (
    match_mp_tac EL_ZIP >>
    fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
  ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs [mkClks_def]) >>
  fs [] >>
  unabbrev_all_tac >>
  ‘EL n (GENLIST I (LENGTH ns)) = I n’ by (
    match_mp_tac EL_GENLIST >>
    gs []) >>
  fs [] >>
  ‘EL n (REPLICATE (LENGTH ns) (Var «sysTime»)) = Var «sysTime»’ by (
    match_mp_tac EL_REPLICATE >>
    gs []) >>
  fs [] >>
  ‘EL n (REPLICATE (LENGTH ns) st) = st’ by (
    match_mp_tac EL_REPLICATE >>
    gs []) >>
  fs [] >>
  gs [eval_def,  OPT_MMAP_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
  ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs []) >>
  unabbrev_all_tac >>
  gs [] >>
  fs [wordLangTheory.word_op_def] >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘EL n ns’ mp_tac) >>
  gs [MEM_EL] >>
  impl_tac >- metis_tac [] >>
  strip_tac >>
  drule n2w_sub >>
  strip_tac >> fs []
QED


Theorem genshape_eq_shape_of:
  ∀ys x zs.
    LENGTH ys = LENGTH zs ⇒
    genShape (LENGTH ys) =
      shape_of (Struct
                (MAP (λ(x,y). ValWord (n2w (x − y)))
                 (ZIP (REPLICATE (LENGTH ys) x,zs))))
Proof
  rw [] >>
  fs [genShape_def] >>
  fs [shape_of_def] >>
  ‘REPLICATE (LENGTH ys) One = MAP (λx. One) (GENLIST I (LENGTH ys))’ by (
    fs [MAP_GENLIST] >>
    fs [REPLICATE_GENLIST] >>
    fs [seqTheory.K_PARTIAL]) >>
  gs [] >>
  fs [MAP_EQ_EVERY2] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff (ZIP (xs,_))’ >>
  ‘EL n (MAP ff (ZIP (xs,zs))) = ff (EL n (ZIP (xs,zs)))’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs [mkClks_def]) >>
  unabbrev_all_tac >>
  fs [] >>
  ‘EL n (ZIP (REPLICATE (LENGTH zs) x,zs)) =
   (EL n (REPLICATE (LENGTH zs) x), EL n zs)’ by (
    match_mp_tac EL_ZIP >>
    fs []) >>
  gs [shape_of_def]
QED


Definition well_formed_terms_def:
  well_formed_terms prog s (t:('a,time_input) panSem$state) <=>
  ∀tms.
    ALOOKUP prog s.location = SOME tms ⇒
    conds_eval_lt_dimword (:α) (resetOutput s) tms ∧
    conds_clks_mem_clks (clksOf prog) tms ∧ terms_time_range (:α) tms ∧
    terms_valid_clocks (clksOf prog) tms ∧ locs_in_code t.code tms ∧
    out_signals_ffi t tms ∧
    input_terms_actions (:α) tms ∧
    terms_wtimes_ffi_bound (:'a) s tms (FST (t.ffi.ffi_state 0))
End

(* should stay as an invariant *)
Definition task_ret_defined_def:
  task_ret_defined (fm: mlstring |-> 'a v) n ⇔
  ∃(vs:'a v list) v1 v2 v3.
    FLOOKUP fm «taskRet» = SOME (
      Struct [
          Struct vs;
          ValWord v1;
          ValWord v2;
          ValLabel v3
        ]) ∧
    EVERY (λv. ∃w. v = ValWord w) vs ∧
    LENGTH vs = n
End

Theorem foldl_word_size_of:
  ∀xs ys n.
    LENGTH xs = LENGTH ys ⇒
    FOLDL
    (λa e. a +
           size_of_shape (shape_of ((λ(x,y). ValWord (n2w (x − y))) e)))
    n (ZIP (xs,ys)) = n + LENGTH xs
Proof
  Induct >>
  rw [] >>
  cases_on ‘ys’ >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def]
QED

Theorem state_rel_intro:
  ∀clks s t.
    state_rel clks s (t:('a,time_input) panSem$state) ⇒
     equivs t.locals s.location s.waitTime ∧
    ffi_vars t.locals ∧  time_vars t.locals ∧
    mem_config t.memory t.memaddrs t.be ∧
    LENGTH clks ≤ 29 ∧
    clock_bound s.clocks clks (dimword (:'a)) ∧
    let
      ffi = t.ffi.ffi_state;
      io_events = t.ffi.io_events;
      (tm,io_flg) = ffi 0
    in
      t.ffi = build_ffi (:'a) t.be ffi io_events ∧
      time_seq ffi (dimword (:'a)) ∧
      FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
      clocks_rel s.clocks t.locals clks tm
Proof
  rw [state_rel_def]
QED

Theorem foo:
  ∀tclks fm clks.
    EVERY (λck. MEM ck clks) tclks ∧
    EVERY (λck. ∃n. FLOOKUP fm ck = SOME n) clks ⇒
    resetClksVals fm clks tclks =
    MAP (ValWord ∘ n2w)
        (MAP (λck. if MEM ck tclks then 0 else (THE (FLOOKUP fm ck))) clks)
Proof
  rw [] >>
  fs [resetClksVals_def] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  fs [resetClocks_def] >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP ff _)’ >>
  ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’] >>
  cases_on ‘MEM (EL n clks) tclks’ >>
  fs []
  >- (
  ‘FLOOKUP (fm |++ ZIP (tclks,MAP (λx. 0) tclks)) (EL n clks) = SOME 0’ by (
    fs [MEM_EL] >>
    match_mp_tac update_eq_zip_map_flookup >>
    gs []) >>
  fs []) >>
  ‘FLOOKUP (fm |++ ZIP (tclks,MAP (λx. 0) tclks)) (EL n clks) =
   FLOOKUP fm (EL n clks) ’ by (
    match_mp_tac flookup_fupdate_zip_not_mem >>
    fs []) >>
  fs []
QED


Definition input_rel_def:
  input_rel fm m n seq =
   let
     st = FST (seq (0:num));
     input  = SND (seq 0)
   in
     FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
     FLOOKUP fm «event» = SOME (ValWord (n2w input)) ∧
     n = input - 1 ∧ input <> 0 ∧
     st < m ∧ input < m
End

Theorem step_input:
  !prog i s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Input i)) s s' ∧
    state_rel (clksOf prog) s t ∧
    well_formed_terms prog s t ∧
    code_installed t.code prog ∧
    input_rel t.locals (dimword (:α)) i t.ffi.ffi_state ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 0w) ∧
    task_ret_defined t.locals (nClks prog) ∧
    labProps$good_dimindex (:'a)  ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) s' t' ∧
      t'.ffi.ffi_state = t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
      FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      task_ret_defined t'.locals (nClks prog) ∧
      (∃wt.
         FLOOKUP t'.locals «wakeUpAt» =
         SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
         FST (t.ffi.ffi_state 0) + wt < dimword (:α))
Proof
  rw [] >>
  fs [] >>
  fs [step_cases] >>
  fs [task_controller_def] >>
  fs [panLangTheory.nested_seq_def] >>
  gs [input_rel_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  qexists_tac ‘1’ >>
  fs [] >>
  drule step_input_eval_wait_zero >>
  impl_tac
  >- gs [state_rel_def, time_vars_def] >>
  gs [] >>
  strip_tac >>
  gs [eval_upd_clock_eq] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  (* calling the function *)
  (* location will come from equivs: state_rel *)
  imp_res_tac state_rel_imp_equivs >>
  fs [equivs_def] >>
  qmatch_asmsub_abbrev_tac
  ‘FLOOKUP _ «loc» = SOME (ValLabel loc)’ >>
  ‘FLOOKUP t.code loc =
   SOME
   ([(«clks» ,genShape (LENGTH (clksOf prog))); («event» ,One)],
    compTerms (clksOf prog) «clks» «event» tms)’ by (
    fs [code_installed_def] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    last_x_assum drule >>
    strip_tac >>
    fs [Abbr ‘loc’]) >>
  (* evaluation *)
  fs [Once evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  fs [Once evaluate_def, eval_upd_clock_eq] >>
  gs [Once eval_def, eval_upd_clock_eq, FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (eval nnt) [_ ; _]’ >>
  ‘FLOOKUP nnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  drule eval_normalisedClks >>
  gs [Abbr ‘nnt’,  FLOOKUP_UPDATE] >>
  qpat_x_assum ‘state_rel (clksOf prog) s t’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> gs [] >>
  pairarg_tac >> gs [] >>
  gs [clocks_rel_def] >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  impl_tac
  >- (
    conj_tac
    >- gs [EVERY_MEM, time_seq_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    gs [clkvals_rel_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [MEM_EL] >>
    first_x_assum (qspec_then ‘n'’ mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘(EL n' (ZIP (clksOf prog,ns))) =
     (EL n' (clksOf prog),EL n' ns)’ by (
      match_mp_tac EL_ZIP >>
      gs []) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  fs [Once eval_def] >>
  qmatch_asmsub_abbrev_tac ‘(eval nnt)’ >>
  ‘(λa. eval nnt a) =
   eval nnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by gs [] >>
  gs [] >>
  (* event eval *)
  gs [Abbr ‘nnt’, eval_def, FLOOKUP_UPDATE] >>
  gs [lookup_code_def] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by gs [] >>
  drule (INST_TYPE
         [``:'a``|->``:'mlstring``,
          ``:'b``|->``:'a``] genshape_eq_shape_of) >>
  disch_then (qspec_then ‘tm’ assume_tac) >>
  rfs [] >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  fs [shape_of_def] >>
  fs [dec_clock_def] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘(«clks» ,Struct nclks)’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_, nnt)’ >>
  drule  (INST_TYPE [``:'a``|->``:'a``,
                     ``:'b``|->``:time_input``] pick_term_thm) >>
  fs [] >>
  disch_then (qspecl_then [‘nnt’, ‘clksOf prog’,
                           ‘nclks’] mp_tac) >>
  impl_tac
  >- (
    gs [Abbr ‘nnt’] >>
    res_tac >> gs [] >> rveq >>
    gs [well_formed_terms_def] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      fs []) >>
    conj_tac
    >- (
    fs [resetOutput_def, Abbr ‘nclks’] >>
    gs [clkvals_rel_def, equiv_val_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n’ mp_tac) >>
    fs [] >>
    strip_tac >>
    qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,_))’ >>
    ‘EL n (ZIP (xs,ns)) = (EL n xs, EL n ns)’ by (
      match_mp_tac EL_ZIP >>
      unabbrev_all_tac >>
      fs []) >>
    fs [Abbr ‘xs’] >>
    ‘EL n (REPLICATE (LENGTH ns) tm) = tm’ by (
      match_mp_tac EL_REPLICATE >>
      fs []) >>
    fs [] >>
    ‘EL n (ZIP (clksOf prog,ns)) = (EL n (clksOf prog), EL n ns)’ by (
      match_mp_tac EL_ZIP >>
      unabbrev_all_tac >>
      fs []) >>
    fs []) >>
    conj_tac
    >- (
      gs [Abbr ‘nclks’, clock_bound_def, maxClksSize_def] >>
      fs [MAP_MAP_o] >>
      fs [SUM_MAP_FOLDL] >>
      ‘LENGTH (REPLICATE (LENGTH ns) tm) = LENGTH ns’ by fs [] >>
      drule foldl_word_size_of >>
      disch_then (qspec_then ‘0’ mp_tac) >>
      fs []) >>
    gs [resetOutput_def] >>
    gs [out_signals_ffi_def, well_behaved_ffi_def]) >>
  impl_tac
  >- (
    fs [Abbr ‘nnt’] >>
    match_mp_tac mem_to_flookup >>
    fs []) >>
  strip_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac
  ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «taskRet» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    gs [task_ret_defined_def] >>
    fs [shape_of_def] >>
    gs [EVERY_MEM] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    fs [MEM_EL] >>
    last_x_assum (qspec_then ‘EL n vs’ mp_tac) >>
    fs [] >>
    impl_tac
    >- metis_tac [] >>
    strip_tac >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def]) >>
  fs [] >>
  gs [panSemTheory.set_var_def] >>
  rveq >> gs [] >>
  (* from here *)
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, Abbr ‘rtv’] >>
  fs [retVal_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [] >>
  qmatch_goalsub_abbrev_tac
    ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «clks» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    gs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def] >>
    ‘EL n (MAP ((λw. ValWord w) ∘ n2w) ns) =
     ((λw. ValWord w) ∘ n2w) (EL n ns)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [shape_of_def]) >>
  fs [] >>
  strip_tac >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘eval fnt’ >>
  ‘FLOOKUP fnt.locals «sysTime» = SOME (ValWord (n2w tm))’ by (
    unabbrev_all_tac >>
    fs [FLOOKUP_UPDATE]) >>
  ‘(λa. eval fnt a) =
   eval fnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘FLOOKUP fnt.locals «clks» =
   SOME (Struct (MAP ((λw. ValWord w) ∘ n2w)
                 (MAP (λck.
                        if MEM ck tclks then 0 else THE (FLOOKUP s.clocks ck)) (clksOf prog))))’ by (
    fs [Abbr ‘fnt’, FLOOKUP_UPDATE] >>
    fs [Abbr ‘rtv’] >>
    gs [resetOutput_def] >>
    match_mp_tac foo >>
    conj_tac
    >- (
      gs [well_formed_terms_def, EVERY_MEM, terms_valid_clocks_def] >>
      rw [] >>
      last_x_assum drule >>
      gs [valid_clks_def, timeLangTheory.termClks_def, EVERY_MEM]) >>
    gs [state_rel_def, clock_bound_def, EVERY_MEM] >>
    rw [] >> res_tac >> gs []) >>
  ‘EVERY (λn. n ≤ tm)
   (MAP (λck.
          if MEM ck tclks then 0 else THE (FLOOKUP s.clocks  ck)) (clksOf prog))’ by (
    gs [EVERY_MAP, EVERY_MEM] >>
    rw [] >>
    gs [state_rel_def, clock_bound_def, EVERY_MEM] >>
    rw [] >> res_tac >> gs [] >>
    gs [clkvals_rel_def, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_MEM] >>
    first_x_assum (qspec_then ‘ck’ assume_tac) >>
    gs []) >>
  drule_all eval_normalisedClks >>
  strip_tac >>
  gs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value rrt _ rrtv’ >>
  ‘is_valid_value rrt «clks» rrtv’ by (
    fs [Abbr ‘rrt’,Abbr ‘rrtv’,  Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    gs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def, Abbr ‘xs’] >>
    qmatch_goalsub_abbrev_tac ‘ZIP (xs,ys)’ >>
    ‘EL n (ZIP (xs,ys)) =
     (EL n xs,EL n ys)’ by (
      match_mp_tac EL_ZIP >>
      fs [Abbr ‘xs’, Abbr ‘ys’]) >>
    fs [Abbr ‘xs’, Abbr ‘ys’] >>
    fs [shape_of_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, Abbr ‘xs’, shape_of_def]) >>
  fs [] >>
  strip_tac >> gs [] >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, eval_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value wvt _ hm’ >>
  ‘is_valid_value wvt «waitSet» hm’ by (
    fs [Abbr ‘wvt’,Abbr ‘hm’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def]) >>
  fs [Abbr ‘wvt’,Abbr ‘hm’] >>
  strip_tac >>
  gs [] >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE, OPT_MMAP_def,
      wordLangTheory.word_op_def] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  strip_tac >>
  gs [] >> rveq >> gs [] >>
  drule state_rel_imp_time_vars >>
  gs [time_vars_def, shape_of_def] >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  fs [evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  (* evaluation  completed *)
  conj_tac
  >- (unabbrev_all_tac >> gs [] >> rveq >> gs []) >>
  conj_tac
  >- (
    rw [state_rel_def]
    >- (
      gs [equivs_def, FLOOKUP_UPDATE] >>
      drule pick_term_dest_eq >>
      simp [] >>
      disch_then drule >>
      gs [] >>
      strip_tac >>
      TOP_CASE_TAC >> gs [active_low_def])
    >- gs [ffi_vars_def, FLOOKUP_UPDATE]
    >- gs [time_vars_def, FLOOKUP_UPDATE]
    >- (
      unabbrev_all_tac >>
      gs [mem_config_def] >>
      fs[mem_call_ffi_def])
    >- (
      gs [clock_bound_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      gs [state_rel_def, clock_bound_def] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      imp_res_tac eval_term_clocks_reset >>
      gs [resetOutput_def] >>
      res_tac >> gs [] >>
      gs [evalTerm_cases] >>
      rveq >> gs [resetClocks_def]) >>
    pairarg_tac >> gs [] >> rveq >> gs [] >>
    rw []
    >- (
      gs [nffi_state_def, build_ffi_def] >>
      fs [Abbr ‘nnt’, ffi_call_ffi_def] >>
      gs [ffiTheory.ffi_state_component_equality])
    >- (
      gs [time_seq_def, nffi_state_def, ffi_call_ffi_def,
          Abbr ‘nnt’, next_ffi_def] >>
      rw [] >>
      first_x_assum (qspec_then ‘n+1’ assume_tac) >>
      metis_tac [ADD])
    >- gs [Abbr ‘nnt’, FLOOKUP_UPDATE, nffi_state_def] >>
    gs [clocks_rel_def, FLOOKUP_UPDATE, nffi_state_def] >>
    fs [Abbr ‘rrtv’] >>
    fs [nffi_state_def, Abbr ‘nnt’, ffi_call_ffi_def, next_ffi_def] >>
    qexists_tac ‘MAP (λck. tm - THE (FLOOKUP s'.clocks ck)) (clksOf prog)’ >>
    gs [] >>
    conj_tac
    >- (
      gs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> gs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) tm) = tm’ by (
        match_mp_tac EL_REPLICATE >>
        fs []) >>
      fs [] >>
      fs [Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      TOP_CASE_TAC >> gs []
      >- (
        ‘FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME 0’ by (
        gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        metis_tac [update_eq_zip_map_flookup]) >>
        gs []) >>
      ‘?x. FLOOKUP s.clocks (EL n (clksOf prog)) = SOME x ∧
           FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME x’ by (
        gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        gs [clock_bound_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        gs [] >>
        qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
        fs [] >>
        match_mp_tac flookup_fupdate_zip_not_mem >>
        gs [MEM_EL]) >>
      gs []) >>
    gs [clkvals_rel_def] >>
    conj_tac
    >- (
      gs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> gs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’, Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      ‘THE (FLOOKUP s'.clocks (EL n (clksOf prog))) <= tm’ by (
        gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        cases_on ‘MEM (EL n (clksOf prog)) tclks’
        >- (
          fs [MEM_EL] >>
          ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
           (EL n'' tclks) = SOME 0’ by
            metis_tac [update_eq_zip_map_flookup]>>
          fs []) >>
        gs [clock_bound_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        gs [] >>
        ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
         (EL n (clksOf prog)) = SOME n''’ by (
          qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
          fs [] >>
          match_mp_tac flookup_fupdate_zip_not_mem >>
          gs [MEM_EL]) >>
        fs [] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac >- metis_tac [MEM_EL] >>
        gs []) >>
      gs []) >>
    fs [EVERY_MEM] >>
    rw [] >>
    gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
    cases_on ‘MEM (EL n (clksOf prog)) tclks’
    >- (
    fs [MEM_EL] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n'' tclks) = SOME 0’ by
      metis_tac [update_eq_zip_map_flookup]>>
    fs []) >>
    gs [clock_bound_def, EVERY_MEM] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac
    >- metis_tac [MEM_EL] >>
    strip_tac >>
    gs [] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n (clksOf prog)) = SOME n''’ by (
      qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
      fs [] >>
      match_mp_tac flookup_fupdate_zip_not_mem >>
      gs [MEM_EL]) >>
    fs [] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac >- metis_tac [MEM_EL] >>
    gs []) >>
  fs [nffi_state_def, Abbr ‘nnt’] >>
  gs [task_ret_defined_def, FLOOKUP_UPDATE, Abbr ‘rtv’, resetOutput_def,
      resetClksVals_def] >>
  fs [EVERY_MAP] >>
  gs [well_formed_terms_def, terms_wtimes_ffi_bound_def] >>
  gs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘Tm (Input (io_flg − 1)) cnds tclks dest wt’ mp_tac) >>
  gs [timeLangTheory.termClks_def, timeLangTheory.termWaitTimes_def, resetOutput_def] >>
  strip_tac >>
  cases_on ‘wt’
  >- (
    qexists_tac ‘0’ >>
    gs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘n2w (THE (nwt))’ >>
  ‘?t. nwt = SOME t’ by (
    gs [Abbr ‘nwt’] >>
    gs [calculate_wtime_def, list_min_option_def] >>
    TOP_CASE_TAC >>
    gs []) >>
  gs [] >>
  qexists_tac ‘t''’ >>
  gs [word_add_n2w]
QED


Definition output_rel_def:
  (output_rel fm m NONE (seq:time_input) = T) ∧
  (output_rel fm m (SOME wt) seq =
   let
     st = FST (seq 0)
   in
    ∃wt nt.
      FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
      FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w (wt + nt))) ∧
      st = wt + nt ∧
      st < m ∧
      SND (seq 0) = 0)
End

(*
   write thoughts about the output step,
   we can impose that all terms always have a wait time,
   and then we can have the wait
   ‘∃tt. s.waitTime = SOME tt’ as invariants
*)

Theorem step_output:
  !prog os s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Output os)) s s' ∧
    state_rel (clksOf prog) s t ∧
    well_formed_terms prog s t ∧
    code_installed t.code prog ∧
    output_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state ∧
    FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
    task_ret_defined t.locals (nClks prog) ∧
    (∃tt. s.waitTime = SOME tt) ∧
    labProps$good_dimindex (:'a)  ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) s' t' ∧
      t'.ffi.ffi_state = t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
      FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      task_ret_defined t'.locals (nClks prog) ∧
      (∃wt.
         FLOOKUP t'.locals «wakeUpAt» =
         SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
         FST (t.ffi.ffi_state 0) + wt < dimword (:α))
Proof
  rw [] >>
  fs [] >>
  fs [step_cases, task_controller_def,
      panLangTheory.nested_seq_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  qexists_tac ‘1’ >>
  fs [] >>
  gs [output_rel_def] >>
  drule step_delay_eval_wait_zero >>
  disch_then (qspec_then ‘n2w (nt + wt)’ mp_tac) >>
  gs [] >>
  strip_tac >>
  gs [eval_upd_clock_eq] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  (* calling the function *)
  (* location will come from equivs: state_rel *)
  imp_res_tac state_rel_imp_equivs >>
  fs [equivs_def] >>
  qmatch_asmsub_abbrev_tac
  ‘FLOOKUP _ «loc» = SOME (ValLabel loc)’ >>
  ‘FLOOKUP t.code loc =
   SOME
   ([(«clks» ,genShape (LENGTH (clksOf prog))); («event» ,One)],
    compTerms (clksOf prog) «clks» «event» tms)’ by (
    fs [code_installed_def] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    last_x_assum drule >>
    strip_tac >>
    fs [Abbr ‘loc’]) >>
  (* evaluation *)
  fs [Once evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  fs [Once evaluate_def, eval_upd_clock_eq] >>
  gs [Once eval_def, eval_upd_clock_eq, FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (eval nnt) [_ ; _]’ >>
  ‘FLOOKUP nnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  drule eval_normalisedClks >>
  gs [Abbr ‘nnt’,  FLOOKUP_UPDATE] >>
  qpat_x_assum ‘state_rel (clksOf prog) s t’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> gs [] >>
  pairarg_tac >> gs [] >>
  gs [clocks_rel_def] >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  impl_tac
  >- (
    conj_tac
    >- gs [EVERY_MEM, time_seq_def, output_rel_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    gs [clkvals_rel_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [MEM_EL] >>
    first_x_assum (qspec_then ‘n'’ mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘(EL n' (ZIP (clksOf prog,ns))) =
     (EL n' (clksOf prog),EL n' ns)’ by (
      match_mp_tac EL_ZIP >>
      gs []) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  fs [Once eval_def] >>
  qmatch_asmsub_abbrev_tac ‘(eval nnt)’ >>
  ‘(λa. eval nnt a) =
   eval nnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by gs [] >>
  gs [] >>
  (* event eval *)
  gs [Abbr ‘nnt’, eval_def, FLOOKUP_UPDATE] >>
  gs [lookup_code_def] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by gs [] >>
  drule (INST_TYPE
         [``:'a``|->``:'mlstring``,
          ``:'b``|->``:'a``] genshape_eq_shape_of) >>
  disch_then (qspec_then ‘nt + wt’ assume_tac) >>
  rfs [] >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  fs [shape_of_def] >>
  fs [dec_clock_def] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘(«clks» ,Struct nclks)’ >>

  qmatch_asmsub_abbrev_tac ‘evaluate (_, nnt)’ >>
  drule  (INST_TYPE [``:'a``|->``:'a``,
                     ``:'b``|->``:time_input``] pick_term_thm) >>
  fs [] >>
  disch_then (qspecl_then [‘nnt’, ‘clksOf prog’,
                           ‘nclks’] mp_tac) >>
  impl_tac
  >- (
    gs [Abbr ‘nnt’] >>
    res_tac >> gs [] >> rveq >>
    gs [well_formed_terms_def] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      fs []) >>
    conj_tac
    >- (
    fs [resetOutput_def, Abbr ‘nclks’] >>
    gs [clkvals_rel_def, equiv_val_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n’ mp_tac) >>
    fs [] >>
    strip_tac >>
    qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,_))’ >>
    ‘EL n (ZIP (xs,ns)) = (EL n xs, EL n ns)’ by (
      match_mp_tac EL_ZIP >>
      unabbrev_all_tac >>
      fs []) >>
    fs [Abbr ‘xs’] >>
    ‘EL n (REPLICATE (LENGTH ns) (nt + wt)) = nt + wt’ by (
      match_mp_tac EL_REPLICATE >>
      fs []) >>
    fs [] >>
    ‘EL n (ZIP (clksOf prog,ns)) = (EL n (clksOf prog), EL n ns)’ by (
      match_mp_tac EL_ZIP >>
      unabbrev_all_tac >>
      fs []) >>
    fs []) >>
    conj_tac
    >- (
      gs [Abbr ‘nclks’, clock_bound_def, maxClksSize_def] >>
      fs [MAP_MAP_o] >>
      fs [SUM_MAP_FOLDL] >>
      ‘LENGTH (REPLICATE (LENGTH ns) (nt + wt)) = LENGTH ns’ by fs [] >>
      drule foldl_word_size_of >>
      disch_then (qspec_then ‘0’ mp_tac) >>
      fs []) >>
    gs [resetOutput_def] >>
    gs [out_signals_ffi_def, well_behaved_ffi_def]) >>
  impl_tac
  >- (
    fs [Abbr ‘nnt’] >>
    match_mp_tac mem_to_flookup >>
    fs []) >>
  strip_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac
  ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «taskRet» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    gs [task_ret_defined_def] >>
    fs [shape_of_def] >>
    gs [EVERY_MEM] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    fs [MEM_EL] >>
    last_x_assum (qspec_then ‘EL n vs’ mp_tac) >>
    fs [] >>
    impl_tac
    >- metis_tac [] >>
    strip_tac >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def]) >>
  fs [] >>
  gs [panSemTheory.set_var_def] >>
  rveq >> gs [] >>
  (* from here *)
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, Abbr ‘rtv’] >>
  fs [retVal_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [] >>
  qmatch_goalsub_abbrev_tac
    ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «clks» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    gs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def] >>
    ‘EL n (MAP ((λw. ValWord w) ∘ n2w) ns) =
     ((λw. ValWord w) ∘ n2w) (EL n ns)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [shape_of_def]) >>
  fs [] >>
  strip_tac >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘eval fnt’ >>
  ‘FLOOKUP fnt.locals «sysTime» = SOME (ValWord (n2w (nt + wt)))’ by (
    unabbrev_all_tac >>
    fs [FLOOKUP_UPDATE]) >>
  ‘(λa. eval fnt a) =
   eval fnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘FLOOKUP fnt.locals «clks» =
   SOME (Struct (MAP ((λw. ValWord w) ∘ n2w)
                 (MAP (λck.
                        if MEM ck tclks then 0 else THE (FLOOKUP s.clocks  ck)) (clksOf prog))))’ by (
    fs [Abbr ‘fnt’, FLOOKUP_UPDATE] >>
    fs [Abbr ‘rtv’] >>
    gs [resetOutput_def] >>
    match_mp_tac foo >>
    conj_tac
    >- (
      gs [well_formed_terms_def, EVERY_MEM, terms_valid_clocks_def] >>
      rw [] >>
      last_x_assum drule >>
      gs [valid_clks_def, timeLangTheory.termClks_def, EVERY_MEM]) >>
    gs [state_rel_def, clock_bound_def, EVERY_MEM] >>
    rw [] >> res_tac >> gs []) >>
  ‘EVERY (λn. n ≤ nt + wt)
   (MAP (λck.
          if MEM ck tclks then 0 else THE (FLOOKUP s.clocks  ck)) (clksOf prog))’ by (
    gs [EVERY_MAP, EVERY_MEM] >>
    rw [] >>
    gs [state_rel_def, clock_bound_def, EVERY_MEM] >>
    rw [] >> res_tac >> gs [] >>
    gs [clkvals_rel_def, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_MEM] >>
    first_x_assum (qspec_then ‘ck’ assume_tac) >>
    gs []) >>
  drule_all eval_normalisedClks >>
  strip_tac >>
  gs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value rrt _ rrtv’ >>
  ‘is_valid_value rrt «clks» rrtv’ by (
    fs [Abbr ‘rrt’,Abbr ‘rrtv’,  Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    gs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def, Abbr ‘xs’] >>
    qmatch_goalsub_abbrev_tac ‘ZIP (xs,ys)’ >>
    ‘EL n (ZIP (xs,ys)) =
     (EL n xs,EL n ys)’ by (
      match_mp_tac EL_ZIP >>
      fs [Abbr ‘xs’, Abbr ‘ys’]) >>
    fs [Abbr ‘xs’, Abbr ‘ys’] >>
    fs [shape_of_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, Abbr ‘xs’, shape_of_def]) >>
  fs [] >>
  strip_tac >> gs [] >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, eval_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value wvt _ hm’ >>
  ‘is_valid_value wvt «waitSet» hm’ by (
    fs [Abbr ‘wvt’,Abbr ‘hm’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def]) >>
  fs [Abbr ‘wvt’,Abbr ‘hm’] >>
  strip_tac >>
  gs [] >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE, OPT_MMAP_def,
      wordLangTheory.word_op_def] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  strip_tac >>
  gs [] >> rveq >> gs [] >>
  fs [Abbr ‘q’] >>
  fs [evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  (* evaluation  completed *)
  conj_tac
  >- (unabbrev_all_tac >> gs [] >> rveq >> gs []) >>
  conj_tac
  >- (
    rw [state_rel_def]
    >- (
      gs [equivs_def, FLOOKUP_UPDATE] >>
      drule pick_term_dest_eq >>
      gs [] >>
      disch_then drule >>
      gs [] >>
      strip_tac >>
      TOP_CASE_TAC >> gs [active_low_def])
    >- gs [ffi_vars_def, FLOOKUP_UPDATE]
    >- gs [time_vars_def, FLOOKUP_UPDATE]
    >- (
      unabbrev_all_tac >>
      gs [mem_config_def] >>
      fs[mem_call_ffi_def] >>
      cheat)
    >- (
      gs [clock_bound_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      gs [state_rel_def, clock_bound_def] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      imp_res_tac eval_term_clocks_reset >>
      gs [resetOutput_def] >>
      res_tac >> gs [] >>
      gs [evalTerm_cases] >>
      rveq >> gs [resetClocks_def]) >>
    pairarg_tac >> gs [] >> rveq >> gs [] >>
    rw []
    >- (
      gs [nffi_state_def, build_ffi_def] >>
      fs [Abbr ‘nnt’, ffi_call_ffi_def] >>
      gs [ffiTheory.ffi_state_component_equality])
    >- (
      gs [time_seq_def, nffi_state_def, ffi_call_ffi_def,
          Abbr ‘nnt’, next_ffi_def] >>
      rw [] >>
      first_x_assum (qspec_then ‘n+1’ assume_tac) >>
      metis_tac [ADD])
    >- gs [Abbr ‘nnt’, FLOOKUP_UPDATE, nffi_state_def] >>
    gs [clocks_rel_def, FLOOKUP_UPDATE, nffi_state_def] >>
    fs [Abbr ‘rrtv’] >>
    fs [nffi_state_def, Abbr ‘nnt’, ffi_call_ffi_def, next_ffi_def] >>
    qexists_tac ‘MAP (λck. (nt + wt) - THE (FLOOKUP s'.clocks ck)) (clksOf prog)’ >>
    gs [] >>
    conj_tac
    >- (
      gs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> gs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) (nt + wt)) = nt + wt’ by (
        match_mp_tac EL_REPLICATE >>
        fs []) >>
      fs [] >>
      fs [Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      TOP_CASE_TAC >> gs []
      >- (
        ‘FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME 0’ by (
        gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        metis_tac [update_eq_zip_map_flookup]) >>
        gs []) >>
      ‘?x. FLOOKUP s.clocks (EL n (clksOf prog)) = SOME x ∧
           FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME x’ by (
        gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        gs [clock_bound_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        gs [] >>
        qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
        fs [] >>
        match_mp_tac flookup_fupdate_zip_not_mem >>
        gs [MEM_EL]) >>
      gs []) >>
    gs [clkvals_rel_def] >>
    conj_tac
    >- (
      gs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> gs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’, Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      ‘THE (FLOOKUP s'.clocks (EL n (clksOf prog))) <= nt + wt’ by (
        gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        cases_on ‘MEM (EL n (clksOf prog)) tclks’
        >- (
          fs [MEM_EL] >>
          ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
           (EL n'' tclks) = SOME 0’ by
            metis_tac [update_eq_zip_map_flookup]>>
          fs []) >>
        gs [clock_bound_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        gs [] >>
        ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
         (EL n (clksOf prog)) = SOME n''’ by (
          qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
          fs [] >>
          match_mp_tac flookup_fupdate_zip_not_mem >>
          gs [MEM_EL]) >>
        fs [] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac >- metis_tac [MEM_EL] >>
        gs []) >>
      gs []) >>
    fs [EVERY_MEM] >>
    rw [] >>
    gs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
    cases_on ‘MEM (EL n (clksOf prog)) tclks’
    >- (
    fs [MEM_EL] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n'' tclks) = SOME 0’ by
      metis_tac [update_eq_zip_map_flookup]>>
    fs []) >>
    gs [clock_bound_def, EVERY_MEM] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac
    >- metis_tac [MEM_EL] >>
    strip_tac >>
    gs [] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n (clksOf prog)) = SOME n''’ by (
      qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
      fs [] >>
      match_mp_tac flookup_fupdate_zip_not_mem >>
      gs [MEM_EL]) >>
    fs [] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac >- metis_tac [MEM_EL] >>
    gs []) >>
  fs [nffi_state_def, Abbr ‘nnt’] >>
  gs [task_ret_defined_def, FLOOKUP_UPDATE, Abbr ‘rtv’, resetOutput_def,
      resetClksVals_def] >>
  fs [EVERY_MAP] >>
  gs [well_formed_terms_def, terms_wtimes_ffi_bound_def] >>
  gs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘Tm (Output out) cnds tclks dest wt'’ mp_tac) >>
  gs [timeLangTheory.termClks_def, timeLangTheory.termWaitTimes_def, resetOutput_def] >>
  strip_tac >>
  cases_on ‘wt'’
  >- (
    qexists_tac ‘0’ >>
    gs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘n2w (THE (nwt))’ >>
  ‘?t. nwt = SOME t’ by (
    gs [Abbr ‘nwt’] >>
    gs [calculate_wtime_def, list_min_option_def] >>
    TOP_CASE_TAC >>
    gs []) >>
  gs [] >>
  qexists_tac ‘t''’ >>
  gs [word_add_n2w]
QED

(*
Theorem step_thm:
  !prog label s s' (t:('a,time_input) panSem$state) ck_extra.
    step prog label s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ⇒
    case label of
    | LDelay d =>
        ∀cycles.
          delay_rep (dimword (:α)) d t.ffi.ffi_state cycles ∧
          wakeup_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state cycles ∧
          mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
          FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ⇒
          ?ck t'.
            evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
            evaluate (task_controller (nClks prog), t' with clock := t'.clock + ck_extra) ∧
            code_installed t'.code prog ∧
            state_rel (clksOf prog) s' t' ∧
            t'.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
            t'.ffi.oracle = t.ffi.oracle ∧
            FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
            FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
            FLOOKUP t'.locals «sysTime»  =
            SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles))))
    | LAction (Input i) =>
        well_formed_terms prog s t ∧
        input_rel t.locals (dimword (:α)) i t.ffi.ffi_state ∧
        FLOOKUP t.locals «isInput» = SOME (ValWord 0w) ∧
        task_ret_defined t.locals (nClks prog) ⇒
        ?ck t'.
          evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
          (NONE, t') ∧
          code_installed t'.code prog ∧
          state_rel (clksOf prog) s' t' ∧
          t'.ffi.ffi_state = t.ffi.ffi_state ∧
          t'.ffi.oracle = t.ffi.oracle ∧
          FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
          FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
          FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
          task_ret_defined t'.locals (nClks prog) ∧
          (∃wt.
             FLOOKUP t'.locals «wakeUpAt» =
             SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
             FST (t.ffi.ffi_state 0) + wt < dimword (:α))
    | LAction (Output os) =>
        well_formed_terms prog s t ∧
        output_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state ∧
        FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
        FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
        FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
        task_ret_defined t.locals (nClks prog) ∧
        (∃tt. s.waitTime = SOME tt) ⇒
        ?ck t'.
          evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
          (NONE, t') ∧
          code_installed t'.code prog ∧
          state_rel (clksOf prog) s' t' ∧
          t'.ffi.ffi_state = t.ffi.ffi_state ∧
          t'.ffi.oracle = t.ffi.oracle ∧
          FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
          FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
          FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
          task_ret_defined t'.locals (nClks prog) ∧
          (∃wt.
             FLOOKUP t'.locals «wakeUpAt» =
             SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
             FST (t.ffi.ffi_state 0) + wt < dimword (:α))
Proof
  rw [] >>
  cases_on ‘label’ >>
  fs []
  >- (
    rw [] >>
    drule_all step_delay >>
    disch_then (qspec_then ‘ck_extra’ mp_tac) >>
    fs []) >>
  cases_on ‘i’
  >- (
    fs [] >>
    rw [] >>
    drule_all step_input >>
    disch_then (qspec_then ‘ck_extra’ mp_tac) >>
    fs []) >>
  fs [] >>
  rw [] >>
  drule step_output >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  fs []
QED
*)

(*
  !prog label s s' w (t:('a,time_input) panSem$state).
    step prog label s s' ∧
    state_rel (clksOf prog) s t ∧
    ffi_rel label s t ∧
    well_formness label prog s t ∧
    local_state label t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      evaluate (task_controller (nClks prog), t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      task_ret_defined t'.locals (nClks prog) ∧
      next_wakeup label t t' ∧
      event_state t'
*)


Definition action_rel_def:
  (action_rel (Input i) s (t:('a,time_input) panSem$state) =
   input_rel t.locals (dimword (:α)) i t.ffi.ffi_state) ∧
  (action_rel (Output os) s t =
   output_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state)
End


Definition ffi_rel_def:
  (ffi_rel (LDelay d) s (t:('a,time_input) panSem$state) =
   ∃cycles.
     delay_rep (dimword (:α)) d t.ffi.ffi_state cycles ∧
     wakeup_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state cycles ∧
     mem_read_ffi_results (:α) t.ffi.ffi_state cycles) ∧
  (ffi_rel (LAction act) s t = action_rel act s t)
End

(*
Definition well_formness_def:
  (well_formness (LDelay _) prog s (t:('a,time_input) panSem$state) = T) ∧
  (well_formness (LAction _) prog s t =
   (well_formed_terms prog s t ∧ task_ret_defined t.locals (nClks prog)))
End
*)

Definition local_action_def:
  (local_action (Input i) t =
     (FLOOKUP t.locals «isInput» = SOME (ValWord 0w))) ∧
  (local_action (Output os) t =
    (FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
     FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
     FLOOKUP t.locals «waitSet» = SOME (ValWord 0w)))
End

Definition local_state_def:
  (local_state (LDelay _) t =
   (FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event» = SOME (ValWord 0w))) ∧
  (local_state (LAction act) t = local_action act t)
End

Definition next_wakeup_def:
  (next_wakeup (LDelay _) (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) =
   (FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt»)) ∧
  (next_wakeup (LAction _) t t' =
   (t'.ffi.ffi_state = t.ffi.ffi_state ∧
    (∃wt.
       FLOOKUP t'.locals «wakeUpAt» =
       SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
       FST (t.ffi.ffi_state 0) + wt < dimword (:α))))
End

Definition event_state_def:
  event_state t ⇔
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event»   =  SOME (ValWord 0w)
End


Theorem step_delay_weaker:
  !prog d s s' (t:('a,time_input) panSem$state).
    step prog (LDelay d) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rel (LDelay d) s t ∧
    local_state (LDelay d) t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ∧
    (* extra assumptions *)
    task_ret_defined t.locals (nClks prog) ∧
    well_formed_terms prog s t ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      evaluate (task_controller (nClks prog), t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      next_wakeup (LDelay d) t t' ∧
      event_state t' ∧
      task_ret_defined t'.locals (nClks prog) ∧
      well_formed_terms prog s' t'
Proof
  rw [] >>
  fs [ffi_rel_def] >>
  drule step_delay >>
  disch_then (qspecl_then [‘cycles’, ‘t’, ‘0’] mp_tac) >>
  impl_tac
  >- gs [local_state_def] >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘t'’ >>
  gs [] >>
  ‘t' with clock := t'.clock = t'’ by
    fs [state_component_equality] >>
  gs [next_wakeup_def, event_state_def, local_state_def] >>
  gs [task_ret_defined_def] >>
  fs [step_cases]
  >- (
    gs [well_formed_terms_def, mkState_def] >>
    gen_tac >>
    strip_tac >>
    first_x_assum drule >>
    strip_tac >>
    gs [resetOutput_def] >>
    conj_tac
    >- (
      gs [conds_eval_lt_dimword_def] >>
      gs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule_all >>
      gs []  >>
      TOP_CASE_TAC >> gs [] >>
      strip_tac >>
      cheat) >>
    (* this is complicated *)
    conj_tac
    >- cheat >>
    cheat) >>
  cheat
QED

Theorem step_input_weaker:
  !prog i s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Input i)) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rel (LAction (Input i)) s t ∧
    local_state (LAction (Input i)) t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ∧
    (* extra assumptions *)
    task_ret_defined t.locals (nClks prog) ∧
    well_formed_terms prog s t ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      next_wakeup (LAction (Input i)) t t' ∧
      event_state t' ∧
      task_ret_defined t'.locals (nClks prog) ∧
      well_formed_terms prog s' t'
Proof
  rw [] >>
  fs [ffi_rel_def] >>
  drule step_input >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- gs [action_rel_def, local_state_def, local_action_def] >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘t'’ >>
  gs [] >>
  conj_tac
  >- (
    gs [next_wakeup_def] >>
    qexists_tac ‘wt’ >> gs []) >>
  conj_tac
  >- gs [event_state_def] >>
  gs [well_formed_terms_def]  >>
  gen_tac >>
  strip_tac >>
  (* need more assumptions *)
  cheat
QED


Theorem step_output_weaker:
  !prog os s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Output os)) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rel (LAction (Output os)) s t ∧
    local_state (LAction (Output os)) t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ∧
    (* should be rephrased *)
    (∃tt. s.waitTime = SOME tt) ∧
    (* extra assumptions *)
    task_ret_defined t.locals (nClks prog) ∧
    well_formed_terms prog s t ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      next_wakeup (LAction (Output os)) t t' ∧
      event_state t' ∧
      task_ret_defined t'.locals (nClks prog) ∧
      well_formed_terms prog s' t'
Proof
  rw [] >>
  fs [ffi_rel_def] >>
  drule step_output >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- gs [action_rel_def, local_state_def, local_action_def] >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘t'’ >>
  gs [] >>
  conj_tac
  >- (
    gs [next_wakeup_def] >>
    qexists_tac ‘wt’ >> gs []) >>
  conj_tac
  >- gs [event_state_def] >>
  gs [well_formed_terms_def]  >>
  gen_tac >>
  strip_tac >>
  (* need more assumptions *)
  cheat
QED


(*
Definition next_wakeup_def:
  (next_wakeup (LDelay _) (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) =
   (FLOOKUP t'.locals «waitSet» = SOME (ValWord 0w) ∧
    FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt»)) ∧
  (next_wakeup (LAction _) t t' =
   (t'.ffi.ffi_state = t.ffi.ffi_state ∧
    FLOOKUP t'.locals «waitSet» = SOME (ValWord 0w) ∧
    (∃wt.
       FLOOKUP t'.locals «wakeUpAt» =
       SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
       FST (t.ffi.ffi_state 0) + wt < dimword (:α))))
End


Definition eventual_wakeup_def:
  eventual_wakeup prog <=>
  let tms = FLAT (MAP SND prog) in
    EVERY (λtm.
            ∃h t. termWaitTimes tm = h::t)
          tms
End

*)

val _ = export_theory();
