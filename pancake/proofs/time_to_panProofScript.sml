(*
  Correctness proof for --
*)

open preamble
     timeSemTheory panSemTheory
     timePropsTheory panPropsTheory
     pan_commonPropsTheory time_to_panTheory

val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem",
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


Definition clk_range_def:
  clk_range fm clks (m:num) ⇔
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


(*
Definition emptyVals_def:
  emptyVals xs = MAP (λ_. ValWord 0w) xs
End
*)

Definition minOption_def:
  (minOption (x:'a word) NONE = x) ∧
  (minOption x (SOME (y:num)) =
    if x <₊ n2w y then x else n2w y)
End


Definition well_behaved_ffi_def:
  well_behaved_ffi ffi_name s nffi nbytes bytes (m:num) <=>
  explode ffi_name ≠ "" /\ 16 < m /\
  read_bytearray ffiBufferAddr 16
                 (mem_load_byte s.memory s.memaddrs s.be) =
  SOME bytes /\
  s.ffi.oracle (explode ffi_name) s.ffi.ffi_state [] bytes =
  Oracle_return nffi nbytes /\
  LENGTH nbytes = LENGTH bytes
End


Definition ffi_return_state_def:
  ffi_return_state s ffi_name bytes nbytes nffi =
  s with
    <|memory := write_bytearray 4000w nbytes s.memory s.memaddrs s.be;
      ffi :=
      s.ffi with
       <|ffi_state := nffi;
         io_events :=
         s.ffi.io_events ++
          [IO_event (explode ffi_name) [] (ZIP (bytes,nbytes))]|> |>
End


Definition nffi_state_def:
  nffi_state s nffi (n:num) bytes nbytes =
    s.ffi with
     <|ffi_state := nffi;
       io_events :=
       s.ffi.io_events ++
        [IO_event (toString n) [] (ZIP (bytes,nbytes))]|>
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
    clk_range s.clocks clks (dimword (:'a)) ∧
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
  fs [clk_range_def, time_range_def] >>
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
  !ffi_name s (res:'a result option) t nffi nbytes bytes.
    evaluate
    (ExtCall ffi_name «ptr1» «len1» «ptr2» «len2»,s) = (res,t)∧
    well_behaved_ffi ffi_name s nffi nbytes bytes (dimword (:α))  /\
    FLOOKUP s.locals «ptr1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «len1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «ptr2» = SOME (ValWord ffiBufferAddr) ∧
    FLOOKUP s.locals «len2» = SOME (ValWord ffiBufferSize) ==>
    res = NONE ∧ t = ffi_return_state s ffi_name bytes nbytes nffi
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [well_behaved_ffi_def] >>
  gs [evaluate_def] >>
  gs [read_bytearray_def, ffiBufferSize_def, ffiBufferAddr_def] >>
  dxrule LESS_MOD >>
  strip_tac >> rfs [] >>
  pop_assum kall_tac >>
  rfs [ffiTheory.call_FFI_def] >>
  rveq >> fs [] >>
  gs [ffi_return_state_def]
QED


Theorem comp_output_term_correct:
  ∀s out cnds tclks dest wt s' t (clkvals:'a v list) clks
   ffi_name nffi nbytes bytes.
    evalTerm s NONE
             (Tm (Output out) cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clk_range s.clocks clks (dimword (:'a)) ∧
    time_range wt (dimword (:'a)) ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    toString dest IN FDOM t.code ∧
    well_behaved_ffi (strlit (toString out)) t nffi nbytes bytes (dimword (:α)) ⇒
      evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with
       <|locals :=
         restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
         memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
         ffi := nffi_state t nffi out bytes nbytes|>)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clk_range_def, time_range_def] >>
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
               [‘nffi’, ‘nbytes’, ‘bytes’] mp_tac) >>
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
   fs [nffi_state_def, restore_from_def]) >>
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
              [‘nffi’, ‘nbytes’, ‘bytes’] mp_tac) >>
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
  fs [nffi_state_def]
QED


Theorem comp_term_correct:
  ∀s io ioAct cnds tclks dest wt s' t (clkvals:'a v list) clks.
    evalTerm s io
             (Tm ioAct cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clk_range s.clocks clks (dimword (:'a)) ∧
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
         (∀nffi nbytes bytes.
            well_behaved_ffi (strlit (toString out)) t nffi nbytes bytes (dimword (:α)) ⇒
            evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
            (SOME (Return (retVal s clks tclks wt dest)),
             t with
               <|locals :=
                 restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                        «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
                 memory := write_bytearray 4000w nbytes t.memory t.memaddrs t.be;
                 ffi := nffi_state t nffi out bytes nbytes|>))
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



Definition code_installed_def:
  code_installed code prog <=>
  ∀loc tms.
    MEM (loc,tms) prog ⇒
    let clks = clksOf prog;
        n = LENGTH clks
    in
      FLOOKUP code (toString loc) =
      SOME ([(«clks», genShape n)],
            compTerms clks «clks» tms)
End


Definition active_low_def:
  (active_low NONE = 1w) ∧
  (active_low (SOME _) = 0w)
End


Definition add_time_def:
  (add_time t NONE     = SOME (ValWord 0w)) ∧
  (add_time t (SOME n) = SOME (ValWord (t + n2w n)))
End


Definition equiv_labels_def:
  equiv_labels fm v sloc ⇔
    FLOOKUP fm v = SOME (ValLabel (toString sloc))
End


Definition equiv_flags_def:
  equiv_flags fm v n ⇔
    FLOOKUP fm v = SOME (ValWord (active_low n))
End

Definition clkvals_rel_def:
  clkvals_rel fm xs ys z <=>
    MAP2 (λx y. x + y) (MAP (n2w o THE o (FLOOKUP fm)) xs) ys =
    REPLICATE (LENGTH ys) z
End


Definition clocks_rel_def:
  clocks_rel clks tlocals sclocks stime ⇔
  ∃(clkwords:'a word list).
    FLOOKUP tlocals «clks» =
     SOME (Struct (MAP ValWord clkwords)) ∧
    clkvals_rel sclocks clks clkwords stime
End

Definition ffi_works_def:
  ffi_works io (t:('a,'b) panSem$state) =
  !n lc m ffi.
    let t = FUNPOW
            (λt. t with
                   <| memory := m
                    ; locals := lc
                    ; ffi := ffi
                   |>)
            n t
    in
      ?bytes nffi nbytes bytes' nffi' nbytes' tm d.
        16 < dimword (:α) /\
        read_bytearray ffiBufferAddr 16
                       (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes ∧
        t.ffi.oracle "check_input" t.ffi.ffi_state [] bytes = Oracle_return nffi nbytes ∧
        LENGTH nbytes = LENGTH bytes ∧
        mem_load One ffiBufferAddr t.memaddrs
                 (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be) =
        SOME (ValWord (active_low io)) ∧
        (?io. FLOOKUP t.locals «isInput» = SOME (ValWord io)) ∧


        read_bytearray ffiBufferAddr 16
                       (mem_load_byte
                        (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be)
                        t.memaddrs t.be) = SOME bytes' ∧
        t.ffi.oracle "get_time" nffi [] bytes' = Oracle_return nffi' nbytes' ∧
        LENGTH nbytes' = LENGTH bytes' ∧
        FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
        tm < dimword (:α) ∧
        mem_load One ffiBufferAddr t.memaddrs
                 (write_bytearray ffiBufferAddr nbytes'
                  (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs
                   t.be) t.memaddrs t.be) =
        SOME (ValWord (n2w (tm + d))) ∧
        tm + d < dimword (:α)
End


(*
Definition ffi_works_def:
  ffi_works io (t:('a,'b) panSem$state) =
    ?bytes nffi nbytes bytes' nffi' nbytes' tm d.
      16 < dimword (:α) /\
      read_bytearray ffiBufferAddr 16
                     (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes ∧
      t.ffi.oracle "check_input" t.ffi.ffi_state [] bytes = Oracle_return nffi nbytes ∧
      LENGTH nbytes = LENGTH bytes ∧
      mem_load One ffiBufferAddr t.memaddrs
               (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be) =
      SOME (ValWord (active_low io)) ∧
      (?io. FLOOKUP t.locals «isInput» = SOME (ValWord io)) ∧


      read_bytearray ffiBufferAddr 16
                     (mem_load_byte
                      (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be)
                      t.memaddrs t.be) = SOME bytes' ∧
      t.ffi.oracle "get_time" nffi [] bytes' = Oracle_return nffi' nbytes' ∧
      LENGTH nbytes' = LENGTH bytes' ∧
      FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
      tm < dimword (:α) ∧
      mem_load One ffiBufferAddr t.memaddrs
               (write_bytearray ffiBufferAddr nbytes'
                (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs
                 t.be) t.memaddrs t.be) =
      SOME (ValWord (n2w (tm + d))) ∧
      tm + d < dimword (:α)
End
*)

(*
   SOME (ValWord (n2w tm')) ∧
   (*  be very clear of what you want to say here *)
   tm <= tm' ∧ tm < dimword (:α) ∧ tm' < dimword (:α)
*)

(*
Definition check_input_works_def:
  check_input_works s t =
  ∀n.
    ?ffi nffi nbytes bytes m.
      well_behaved_ffi «check_input» (FUNPOW (λt. t with ffi := ffi ) n t) nffi nbytes bytes (m:num) ∧
      mem_load One ffiBufferAddr t.memaddrs
               (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be) =
      SOME (ValWord (active_low s.ioAction))
End


Definition get_time_works_def:
  get_time_works (t:('a,'b) panSem$state) =
  ∀n.
    ?ffi nffi nbytes bytes m.
      well_behaved_ffi «get_time» (FUNPOW (λt. t with ffi := ffi ) n t) nffi nbytes bytes (m:num) ∧
      ?tm tm'.
        FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
        mem_load One ffiBufferAddr t.memaddrs
                 (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be) =
        SOME (ValWord (n2w tm')) /\
        tm <= tm' /\ tm' < dimword (:α)
End
*)

Definition ffi_vars_def:
  ffi_vars fm  ⇔
  FLOOKUP fm «ptr1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «len1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «ptr2» = SOME (ValWord ffiBufferAddr) ∧
  FLOOKUP fm «len2» = SOME (ValWord ffiBufferSize)
End


Definition state_rel_def:
  state_rel clks s s' (t:('a, 'b) panSem$state) ⇔
    equiv_labels t.locals «loc» s.location ∧
    equiv_flags  t.locals «isInput» s'.ioAction ∧
    equiv_flags  t.locals «waitSet» s.waitTime ∧
    (?tm.
      tm < dimword (:'a) /\
      let stime = (n2w tm):'a word in
        FLOOKUP t.locals «sysTime» = SOME (ValWord stime) ∧
        FLOOKUP t.locals «wakeUpAt» = add_time stime s.waitTime ∧
        clocks_rel clks t.locals s.clocks stime) ∧
    LENGTH clks ≤ 29 ∧ clk_range s.clocks clks (dimword (:'a)) ∧
    ffi_works s'.ioAction t ∧ ffi_vars t.locals
    (*
    check_input_works s' t ∧
    get_time_works t *)
End


Definition systime_of_def:
  systime_of t =
   case FLOOKUP t.locals «sysTime» of
   | SOME (ValWord t) => w2n t
   | _ => 0
End


Definition upd_delay_def:
  upd_delay t d m nffi =
  t with
    <| locals := t.locals |++
                  [(«isInput» ,ValWord 1w);
                   («sysTime» ,ValWord (n2w (systime_of t + d)))]
     ; memory := m
     ; ffi := nffi
     |>
End

(*
Definition word_of_def:
  word_of (SOME (ValWord w)) = w /\
  word_of _ = 0w
End

Definition upd_delay_def:
  upd_delay t d m nffi =
  t with
    <| locals := t.locals |++
                  [(«isInput» ,ValWord 1w);
                   («sysTime» ,ValWord (word_of (FLOOKUP t.locals «sysTime») + n2w d))]
     ; memory := m
     ; ffi := nffi
     |>
End
*)


Theorem check_input_time_neq_while:
  check_input_time <> While wait check_input_time
Proof
  rw [check_input_time_def, panLangTheory.nested_seq_def]
QED


Theorem add_time_lemma:
  !a b.
    ∃c. add_time a b = SOME (ValWord c)
Proof
  rw [] >>
  cases_on ‘b’ >>
  fs [add_time_def]
QED


Theorem evaluate_check_input_time:
  !io t.
    ffi_works io (t:('a,'b) panSem$state) ∧
    ffi_vars t.locals ==>
    ?ffi mem d.
      evaluate (check_input_time, t) =
      (NONE,
       t with <| ffi := ffi;
                 memory := mem;
                 locals := t.locals |+
                            («isInput» ,ValWord (active_low io)) |+
                            («sysTime» ,ValWord (n2w (systime_of t + d)))
              |>) ∧
      systime_of t + d < dimword (:α)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [ffi_vars_def] >>
  fs [ffi_works_def] >>
  last_x_assum (qspecl_then [‘0’, ‘t.locals’, ‘t.memory’, ‘t.ffi’] assume_tac) >>
  fs [] >>
  ‘16 MOD dimword (:α) = 16’ by (match_mp_tac LESS_MOD >> fs []) >>
  fs [check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [evaluate_def] >>
  fs [] >>
  pairarg_tac >> rveq >> gs [] >>
  fs [read_bytearray_def] >>
  fs [ffiBufferSize_def] >>
  gs [] >>
  qpat_x_assum ‘_ = (res,s1)’ mp_tac >>
  (* calling check_input *)
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  fs [] >>
  strip_tac >>
  rveq >> gs [] >>
  pairarg_tac >> rveq >> gs [] >>
  gs [eval_def, is_valid_value_def, shape_of_def] >>
  rveq >> gs [] >>
  gs [FLOOKUP_UPDATE] >>
  (* calling get_time *)
  gs [read_bytearray_def] >>
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  gs [] >>
  gs [FLOOKUP_UPDATE] >>
  gs [shape_of_def] >>
  rveq >> gs [] >>
  qmatch_goalsub_abbrev_tac ‘t with <|
                               locals := _;
                               memory := m;
                               ffi := f |>’ >>
  qexists_tac ‘f’ >>
  qexists_tac ‘m’ >>
  qexists_tac ‘d’ >>
  fs [Abbr ‘m’, Abbr ‘f’] >>
  gs [systime_of_def]
QED


Theorem step_delay_eval_wait_not_zero:
  !prog d s t.
    step prog (LDelay d) s (mkState (delay_clocks (s.clocks) d) s.location NONE NONE) ∧
    equiv_flags t.locals «isInput» (NONE:ioAction option) ∧
    equiv_flags t.locals «waitSet» s.waitTime ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)) ∧
    (?tm. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord tm)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [step_cases, mkState_def] >>
  fs [equiv_flags_def, active_low_def] >>
  fs [wait_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [active_low_def,
      wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs []
QED

Theorem ffi_upd_be_memaddrs:
  !n t lc m ffi.
    (FUNPOW
     (λt. t with <|locals := lc; memory := m; ffi := ffi|>) n t).be = t.be /\
    (FUNPOW
     (λt. t with <|locals := lc; memory := m; ffi := ffi|>) n t).memaddrs = t.memaddrs
Proof
  Induct >>
  rw [] >>
  fs [FUNPOW]
QED

Theorem ffi_upd_mem_ffi_lc:
  !n t lc m ffi.
    (FUNPOW
     (λt. t with <|locals := lc; memory := m; ffi := ffi|>) n t).memory =
    (case n of 0 => t.memory | _ => m) /\
    (FUNPOW
     (λt. t with <|locals := lc; memory := m; ffi := ffi|>) n t).ffi =
    (case n of 0 => t.ffi | _ => ffi) /\
    (FUNPOW
     (λt. t with <|locals := lc; memory := m; ffi := ffi|>) n t).locals =
    (case n of 0 => t.locals | _ => lc)
Proof
  Induct >>
  rw [] >>
  fs [FUNPOW] >>
  every_case_tac >>
  fs []
QED


Theorem ffi_work_dec_clock:
  !io t.
    ffi_works io t ==>
    ffi_works io (dec_clock t)
Proof
  rw [dec_clock_def, ffi_works_def] >>
  gs [ffi_upd_be_memaddrs] >>
  pop_assum (qspecl_then
             [‘n’, ‘lc’, ‘m’, ‘ffi’] assume_tac) >>
  fs [ffi_upd_mem_ffi_lc] >>
  qexists_tac ‘tm’ >>
  qexists_tac ‘d’ >>
  gs []
QED


Theorem systime_clock_upd:
  !t ck.
    systime_of (t with clock := ck) =
    systime_of t
Proof
  rw [] >>
  fs [systime_of_def]
QED


Theorem foo:
  !xs ys fm a b.
    EVERY (λx. ∃n. FLOOKUP fm x = SOME n) xs /\
    LENGTH xs = LENGTH ys /\
    MAP2 (λx y. x + y)
         (MAP ((n2w :num -> α word) ∘ THE ∘ FLOOKUP fm) xs)
         (ys :α word list) =
    REPLICATE (LENGTH ys) ((n2w :num -> α word) a) /\
    b + a < dimword (:α) ==>
    MAP2 (λx y. x + y)
         (MAP
          ((n2w :num -> α word) ∘ THE ∘
           FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,b + y)) (fmap_to_alist fm)))
          xs)
         ys =
    REPLICATE (LENGTH ys) ((n2w :num -> α word) (b + a))
Proof
  Induct >> rw [] >>
  cases_on ‘ys’ >>
  fs [] >>
  once_rewrite_tac [GSYM word_add_n2w] >>
  qpat_x_assum ‘_ + _ = _’ (assume_tac o GSYM) >>
  gs [] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,b + y)) (fmap_to_alist fm))
   h = SOME (b + n)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,b + y)) (fmap_to_alist fm)) =
     MAP FST (fmap_to_alist fm)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(h,n)’ >>
    fs []) >>
  fs [] >>
  once_rewrite_tac [GSYM word_add_n2w] >>
  fs []
QED


Theorem step_dely:
  !p t prog d s s'.
    p = wait_input_time_limit ∧
    step prog (LDelay d) s s' ∧
    s.waitTime = NONE ∧
    s' = mkState (delay_clocks (s.clocks) d) s.location NONE NONE ∧
    state_rel (clksOf prog) s s' t ∧
    code_installed t.code prog ==>
    ?m nffi.
      evaluate (p, t) =
      evaluate (p, upd_delay t d m nffi) ∧
      state_rel (clksOf prog) s s' (upd_delay t d m nffi) ∧
      code_installed (upd_delay t d m nffi).code prog
Proof
  recInduct panSemTheory.evaluate_ind >>
  rw [] >>
  TRY (
    fs [wait_input_time_limit_def, panLangTheory.nested_seq_def] >>
    NO_TAC) >>
  fs [wait_input_time_limit_def] >>
  rveq >> gs [] >>
  fs [check_input_time_neq_while] >>
  qpat_x_assum ‘T’ kall_tac >>
  qmatch_goalsub_rename_tac ‘evaluate (_, t) =  _’ >>
  qmatch_asmsub_rename_tac ‘step _ _ s _’ >>
  drule step_delay_eval_wait_not_zero >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- gs [state_rel_def, mkState_def, add_time_lemma] >>
  strip_tac >>
  fs [] >>
  rewrite_tac [Once evaluate_def] >>
  gs [] >>
  reverse TOP_CASE_TAC >> gs []
  (* t.clock ≠ 0 *)
  >- (
    ‘ffi_works (NONE:ioAction option) t’ by
     gs [state_rel_def, mkState_def] >>
    drule ffi_work_dec_clock >>
    strip_tac >>
    drule evaluate_check_input_time >>
    impl_tac >- gs [state_rel_def, ffi_vars_def, dec_clock_def] >>
    strip_tac >>
    fs [] >>
    qpat_x_assum ‘T’ kall_tac >>
    fs [active_low_def] >>
    (* renaming intermediate delay *)
    qmatch_asmsub_rename_tac ‘id + _ < dimword (:α)’ >>
    last_x_assum
    (qspecl_then
     [‘prog’, ‘d - id’,
      ‘mkState
       (delay_clocks (s.clocks) id)
       s.location
       NONE
       NONE’] mp_tac) >>
    impl_tac
    >- (
      gs [dec_clock_def] >>
      conj_tac
      >- (
        rewrite_tac [step_cases] >>
        fs [mkState_def]) >>
      gs [mkState_def, state_rel_def] >>
      gs [equiv_labels_def, equiv_flags_def, FLOOKUP_UPDATE] >>
      gs [FLOOKUP_UPDATE, active_low_def] >>
      conj_tac
      >- (
        qexists_tac ‘id + systime_of t’ >> gs [systime_clock_upd] >>
        fs [] >>
        fs [add_time_def, clocks_rel_def] >>
        qexists_tac ‘clkwords’ >>
        gs [FLOOKUP_UPDATE, delay_clocks_def,
            clkvals_rel_def, systime_of_def] >>
        match_mp_tac foo >>
        fs [] >>
        fs [clk_range_def] >>
        drule every_conj_spec >>
        strip_tac >> fs [FDOM_FLOOKUP] >>
        cheat (* add assumption *)) >>
      conj_tac
      >- (
        gs [clk_range_def, delay_clocks_def] >>
        cheat) >>
      gs [ffi_vars_def, FLOOKUP_UPDATE] >>
      qpat_x_assum ‘ffi_works NONE t’ kall_tac >>
      qpat_x_assum ‘ffi_works NONE _’ assume_tac >>
      gs [ffi_works_def] >>
      rw [] >> gs [] >>
      fs [ffi_upd_mem_ffi_lc, ffi_upd_be_memaddrs] >>
      cases_on ‘n’ >> gs []
      >- (
        first_x_assum (qspecl_then [‘1’, ‘lc’, ‘mem'’, ‘ffi’] assume_tac) >>
        gs [] >>
        gs [FLOOKUP_UPDATE] >>
        gs [systime_of_def] >>



        qexists_tac ‘id + tm’ >>
        gs [] >>
        qexists_tac ‘d' - id’ >>
        gs [] >>
        fs [ADD_ASSOC] >>




      ) >>
      first_x_assum (qspecl_then [‘1’, ‘lc’, ‘m’, ‘ffi'’] assume_tac) >>
      gs [] >>
      qexists_tac ‘tm'’ >>
      gs [] >>
      qexists_tac ‘d'’ >>
      gs []) >>
    strip_tac >>
    fs [] >>
    rewrite_tac [upd_delay_def] >>
    fs [dec_clock_def] >>
    rewrite_tac [FUPDATE_LIST_THM] >>
    rewrite_tac [systime_of_def] >>
    gs [FLOOKUP_UPDATE] >>
    qexists_tac ‘m’ >>
    qexists_tac ‘nffi’ >>
    conj_tac
    >- (
    gs [state_rel_def] >>
    ‘(id + tm') MOD dimword (:α) + (d − id) =
     tm' + d’ by cheat >>
    fs [] >>
    cheat) >>
    cheat) >>
  cheat
QED


Theorem foo:
  !prog d s s' t.
    step prog (LDelay d) s s' ∧
    state_rel (clksOf prog) s s' t  ==>
    ?w.
      eval t wait = SOME (ValWord w) /\
      w ≠ 0w
Proof
  rw [] >>
  fs [state_rel_def] >>
  fs [step_cases, mkState_def]
  >- (
    fs [equiv_flags_def, active_low_def] >>
    fs [wait_def] >>
    fs [eval_def, OPT_MMAP_def] >>
    gs [add_time_def, active_low_def,
        wordLangTheory.word_op_def] >>
    TOP_CASE_TAC >>
    fs []) >>
  rveq >> gs [] >>
  fs [equiv_flags_def, active_low_def] >>
  fs [wait_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [add_time_def] >>
  cheat (* later *)
QED







Theorem foo:
  ffi_works s t ∧
  ffi_vars t.locals /\
  (?io. FLOOKUP t.locals «isInput» = SOME (ValWord io)) ==>
  evaluate (check_input_time,t) = (NONE,ARB t)
Proof
  rw [] >>
  fs [ffi_vars_def] >>
  fs [check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [evaluate_def] >>
  fs [] >>
  pairarg_tac >> rveq >> gs [] >>
  fs [read_bytearray_def] >>
  gs [ffi_works_def] >>
  fs [ffiBufferSize_def] >>
  ‘16 MOD dimword (:α) = 16’ by cheat >> gs [] >>
  qpat_x_assum ‘_ = (res,s1)’ mp_tac >>

  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  fs [] >>
  strip_tac >>
  rveq >> gs [] >>
  pairarg_tac >> rveq >> gs [] >>
  gs [eval_def, is_valid_value_def, shape_of_def] >>
  rveq >> gs [] >>
  gs [FLOOKUP_UPDATE] >>
  gs [read_bytearray_def] >>
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  gs [] >>
  gs [FLOOKUP_UPDATE] >>
  gs [shape_of_def] >>
  rveq >> gs [] >>

 (*
   t.ffi.oracle "get_time" t.ffi.ffi_state [] bytes =
   Oracle_return nffi' nbytes'


   t.ffi.oracle "get_time" nffi [] x
 *)




Theorem foo:
  check_input_works s t ∧ get_time_works t /\
  ffi_vars t.locals /\
  (?io. FLOOKUP t.locals «isInput» = SOME (ValWord io)) ==>
  evaluate (check_input_time,t) = (NONE,ARB t)
Proof
  rw [] >>
  fs [ffi_vars_def] >>
  fs [check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [evaluate_def] >>
  fs [] >>
  pairarg_tac >> rveq >> gs [] >>
  fs [read_bytearray_def] >>
  gs [check_input_works_def] >>
  last_x_assum (qspec_then ‘0’ assume_tac) >>
  fs [] >>
  fs [well_behaved_ffi_def] >>
  fs [ffiBufferSize_def] >>
  ‘16 MOD dimword (:α) = 16’ by cheat >> fs [] >>
  qpat_x_assum ‘_ = (res,s1)’ mp_tac >>



  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  fs [] >>
  strip_tac >>
  rveq >> gs [] >>
  pairarg_tac >> rveq >> gs [] >>
  gs [eval_def, is_valid_value_def, shape_of_def] >>
  rveq >> gs [] >>
  gs [FLOOKUP_UPDATE] >>

  gs [read_bytearray_def] >>

  gs [get_time_works_def] >>
  last_x_assum (qspec_then ‘0’ assume_tac) >>
  fs [] >>
  fs [well_behaved_ffi_def] >>
  (*
  read_bytearray ffiBufferAddr 16
                 (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes' *)
  (*
  read_bytearray ffiBufferAddr 16
  (mem_load_byte
  (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs
  t.be) t.memaddrs t.be) *)
  TOP_CASE_TAC
  >- cheat >>
  gs [] >>


  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  fs [] >>


 (*
   t.ffi.oracle "get_time" t.ffi.ffi_state [] bytes =
   Oracle_return nffi' nbytes'


   t.ffi.oracle "get_time" nffi [] x
 *)




  pairarg_tac >> rveq >> gs [] >>






  gs [read_bytearray_def] >>



  gs [get_time_works_def] >>
  last_x_assum (qspec_then ‘0’ assume_tac) >>
  fs [] >>
  fs [well_behaved_ffi_def] >>
  fs [ffiBufferSize_def] >>
  ‘16 MOD dimword (:α) = 16’ by cheat >> fs [] >>
  fs [ffiTheory.call_FFI_def] >>
  rveq >> fs [] >>
  gs [eval_def, is_valid_value_def, shape_of_def] >>
  rveq >> gs [] >>
  gs [FLOOKUP_UPDATE, read_bytearray_def] >>


  gs []

fs[well_behaved_ffi_def]

QED


Theorem step_dely:
  !p t prog d s s'.
    p = wait_input_time_limit /\
    step prog (LDelay d) s s' ∧
    s' = mkState (delay_clocks (s.clocks) d) s.location NONE NONE /\
    state_rel (clksOf prog) s s' t /\
    code_installed t.code prog ==>
    ?m nffi.
      evaluate (p, t) =
      evaluate (p, upd_delay t d m nffi) /\
      state_rel (clksOf prog) s s' (upd_delay t d m nffi) /\
      code_installed (upd_delay t d m nffi).code prog
Proof
  recInduct panSemTheory.evaluate_ind >>
  rw [] >>
  TRY (
    fs [wait_input_time_limit_def, panLangTheory.nested_seq_def] >>
    NO_TAC) >>
  fs [wait_input_time_limit_def] >>
  rveq >> gs [] >>
  qmatch_goalsub_rename_tac ‘evaluate (_, t) =  _’ >>
  qmatch_asmsub_rename_tac ‘step _ _ s _’ >>
  drule step_delay_eval_wait_not_zero >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- (
    gs [state_rel_def, mkState_def] >>
    cheat) >>
  strip_tac >>
  fs [] >>
  rewrite_tac [Once evaluate_def] >>
  gs [] >>
  TOP_CASE_TAC >> gs []
  >- (
   qexists_tac ‘t.memory’ >>
   qexists_tac ‘t.ffi’ >>
   fs [Once evaluate_def] >>
   drule step_delay_eval_wait_not_zero >>
   disch_then (qspec_then ‘upd_delay t d t.memory t.ffi’ mp_tac) >>
   impl_tac
   >- (
    gs [state_rel_def, mkState_def] >>
    cheat) >>
   strip_tac >>
   gs [] >>
   fs [upd_delay_def] >>
   fs [empty_locals_def] >>
   conj_tac >- cheat >>
   cheat) >>
  pairarg_tac >> gs [] >>


  )

  >-


  drule step_delay_eval_wait_not_zero >>


  rewrite_tac [Once eval_def] >>
  fs [OPT_MMAP_def] >>
  fs [eval_def]





  TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  reverse TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  reverse TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  ‘c ≠ 0w’ by cheat >>
  gs [] >>
  ‘t.clock <> 0’ by cheat >> gs [] >>
  pairarg_tac >> gs [] >>
  ‘res = NONE’ by cheat >>
  gs [] >>


  gs [foo] >>
  first_x_assum drule >>
  impl_tac >- cheat >>
  strip_tac >>
  gs [] >>


  once_rewrite_tac [evaluate_def] >>



QED

Theorem foo:
  !e p.
    check_input_time <> While e p
Proof
  rw [check_input_time_def, panLangTheory.nested_seq_def]
QED


Theorem step_dely:
  !p t prog d s s'.
    p = wait_input_time_limit /\
    step prog (LDelay d) s s' ∧
    s' = mkState (delay_clocks (s.clocks) d) s.location NONE NONE /\
    state_rel (clksOf prog) s s' t /\
    code_installed t.code prog ==>
    ?m nffi.
      evaluate (p, t) =
      evaluate (p, upd_delay t d m nffi) /\
      state_rel (clksOf prog) s s' (upd_delay t d m nffi) /\
      code_installed (upd_delay t d m nffi).code prog
Proof
  recInduct panSemTheory.evaluate_ind >>
  rw [] >>
  TRY (
    fs [wait_input_time_limit_def, panLangTheory.nested_seq_def] >>
    NO_TAC) >>
  fs [wait_input_time_limit_def] >>
  rveq >> gs [] >>





  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  reverse TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  reverse TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  ‘c ≠ 0w’ by cheat >>
  gs [] >>
  ‘s.clock <> 0’ by cheat >> gs [] >>
  pairarg_tac >> gs [] >>
  ‘res = NONE’ by cheat >>
  gs [foo] >>
  first_x_assum drule >>
  impl_tac >- cheat >>
  strip_tac >>
  gs [] >>


  once_rewrite_tac [evaluate_def] >>










  rewrite_tac [Once evaluate_def] >>
  TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  reverse TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  reverse TOP_CASE_TAC
  >- cheat >>
  gs [] >>
  ‘c ≠ 0w’ by cheat >>
  gs [] >>
  ‘s.clock <> 0’ by cheat >> gs [] >>
  pairarg_tac >> gs [] >>
  ‘res = NONE’ by cheat >>
  gs [foo] >>
  first_x_assum drule >>
  impl_tac >- cheat >>
  strip_tac >>
  gs [] >>
  once_rewrite_tac [evaluate_def] >>






QED





(* say that max number of clocks in prog are less then or equal to 29 *)
(* and also ∧
      clk_range sclocks clks (dimword (:'a)) *)


Theorem step_dely:
  !p t prog d s s'.
    p = task_controller (nClks prog) /\
    step prog (LDelay d) s s' ∧
    s' = mkState (delay_clocks (s.clocks) d) s.location NONE NONE /\
    state_rel (clksOf prog) s s' t /\
    code_installed t.code prog ==>
    ?m nffi.
      evaluate (p, t) =
      evaluate (p, upd_delay t d m nffi) /\
      state_rel (clksOf prog) s s' (upd_delay t d m nffi) /\
      code_installed (upd_delay t d m nffi).code prog
Proof
  recInduct panSemTheory.evaluate_ind >>
  rw [] >>



  TRY (
    fs [task_controller_def, panLangTheory.nested_seq_def] >>
    NO_TAC)




QED





Definition active_low_def:
  (active_low NONE = 1w) ∧
  (active_low (SOME _) = 0w)
End

Definition add_time_def:
  (add_time t NONE = 0w) ∧
  (add_time t (SOME n) = n2w t + n2w n)
End


Definition ffi_vars_def:
  ffi_vars fm  ⇔
  FLOOKUP fm «ptr1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «len1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «ptr2» = SOME (ValWord ffiBufferAddr) ∧
  FLOOKUP fm «len2» = SOME (ValWord ffiBufferSize)
End


Definition vars_rel_def:
  vars_rel s t ⇔
  ffi_vars t.locals ∧
  FLOOKUP t.locals «loc» = SOME (ValLabel (toString s.location)) ∧
  FLOOKUP t.locals «isInput» = SOME (ValWord (active_low s.ioAction)) ∧
  FLOOKUP t.locals «waitSet» = SOME (ValWord (active_low s.waitTime)) ∧
  (∃n. FLOOKUP t.locals «sysTime» = SOME (ValWord n)) ∧
  (∃n. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord n))
End


Definition foo_def:
  foo p d s s' t t'  ⇔
  step p (LDelay d) s s' ∧
  vars_rel s t ∧ vars_rel s' t' ∧
  (∀t. t.getTime < d ⇒ isInput has not happened)
End



Definition read_sys_time_def:
  read_sys_time (s:('a,'b) panSem$state) nbytes t ⇔
  mem_load One ffiBufferAddr s.memaddrs
           (write_bytearray ffiBufferAddr nbytes s.memory s.memaddrs s.be) =
  SOME (ValWord (n2w t))
End


Definition mono_system_time_def:
  mono_system_time (s:('a,'b) panSem$state) (r:('a,'b) panSem$state) =
  ∀f res t g res' stime.
    evaluate (f,s) = (res, t) ∧ evaluate (g,t) = (res', r) ∧
    FLOOKUP s.locals «sysTime» = SOME (ValWord (n2w stime)) ∧
    stime < dimword (:α) ⇒
    ∃nffi nbytes bytes nstime.
      well_behaved_ffi «get_time» t nffi nbytes bytes (dimword (:α)) ∧
      read_sys_time t nbytes nstime ∧
      stime ≤ nstime ∧ nstime < dimword (:α)
End


Definition check_input_ffi_correct_def:
  is_input_ffi_correct (s:('a,'b) panSem$state) (r:('a,'b) panSem$state) =
  ∀f res t g res' n.
    evaluate (f,s) = (res, t) ∧ evaluate (g,t) = (res', r) ∧
    FLOOKUP s.locals «isInput» = SOME (ValWord n) ⇒
    ∃nffi nbytes bytes m.
      well_behaved_ffi «check_input» t nffi nbytes bytes (dimword (:α)) ∧
      read_sys_time t nbytes m ∧
      (m = 0 ∨ m = 1) ∧
      m < dimword (:α)
End


Definition label_not_missed_def:
  label_not_missed (s:('a,'b) panSem$state) (r:('a,'b) panSem$state) (LDelay d) =
   ∃t f res g res' stime nffi nbytes bytes nstime.
     evaluate (f,s) = (res, t) ∧ evaluate (g,t) = (res', r) ∧
     FLOOKUP s.locals «sysTime» = SOME (ValWord (n2w stime)) ∧
     stime < dimword (:α) ∧
     well_behaved_ffi «get_time» t nffi nbytes bytes (dimword (:α)) ∧
     read_sys_time t nbytes nstime ∧
     stime ≤ nstime ∧ nstime < dimword (:α) ∧
     nstime - stime = d
End


Theorem ffi_vars_intro:
  ∀fm.
    ffi_vars fm  ⇒
    FLOOKUP fm «ptr1» = SOME (ValWord 0w) ∧
    FLOOKUP fm «len1» = SOME (ValWord 0w) ∧
    FLOOKUP fm «ptr2» = SOME (ValWord ffiBufferAddr) ∧
    FLOOKUP fm «len2» = SOME (ValWord ffiBufferSize)
Proof
  rw [] >>
  fs [ffi_vars_def]
QED

Definition ioaction_rel_def:
  ioaction_rel s s' t t' =
    step p l s s' ∧
    s'.ioAction = NONE ∧

End


Theorem step_delay_comp_correct:
  ∀prog d s s' (t:('a, 'b)panSem$state) stime res t'.
    step prog (LDelay d) s s' ∧
    s' = mkState (delay_clocks (s.clocks) d) s.location NONE NONE ∧
    ARB s s' t t' ∧ (* input never occurs *)
    ffi_vars t.locals ∧
    FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w stime)) ∧ stime < dimword (:α) ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord (active_low s.ioAction)) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord (active_low s.waitTime)) ∧
    FLOOKUP t.locals «wakeUpAt» = SOME (system_wait_time (n2w stime) s.waitTime) ∧
    is_input_ffi_correct t t' ∧
    evaluate (wait_input_time_limit, t) = (res, t') ⇒
    res = ARB ∧ t' = ARB t
Proof
  rpt gen_tac >>
  strip_tac >>
  drule ffi_vars_intro >>
  strip_tac >>
  fs [step_cases] >> rveq >> gs []
  >- (
    qpat_x_assum ‘_ = (res,t')’ assume_tac >>
    fs [wait_input_time_limit_def] >>
    fs [Once evaluate_def] >>
    fs [active_low_def] >> cheat) >>
  cheat
QED



Definition clocks_rel_def:
  clocks_rel sclocks tlocals prog n ⇔
  ∃(clkwords:'a word list).
    let clks = clksOf prog;
        clkvals = MAP (λn. ValWord n) clkwords in
      FLOOKUP tlocals «clks» = SOME (Struct clkvals) ∧
      equiv_val sclocks clks (MAP (λw. ValWord (n - w)) clkwords) ∧
      maxClksSize clkvals ∧
      clk_range sclocks clks (dimword (:'a))
End


(*
Definition clocks_rel_def:
  clocks_rel sclocks tlocals prog (sysTime:num) ⇔
  ∃nclks.
    let clks = clksOf prog;
        clkvals = MAP (λn. ValWord (n2w n)) nclks in
      FLOOKUP tlocals «clks» = SOME (Struct clkvals) ∧
      equiv_val sclocks clks (MAP (λn. ValWord (n2w sysTime - n2w n)) nclks) ∧
      maxClksSize clkvals ∧
      clk_range sclocks clks (dimword (:'a))
End
*)


Definition state_rel_def:
  state_rel prog s t ⇔
  FLOOKUP t.locals «loc» = SOME (ValLabel (toString s.location)) ∧
  FLOOKUP t.locals «isInput» = SOME (ValLabel (active_low s.ioAction)) ∧
  FLOOKUP t.locals «waitSet» = SOME (ValWord (active_low s.waitTime)) ∧
  ∃stime.
    FLOOKUP t.locals «sysTime» = SOME (ValWord stime) ∧
    clocks_rel s.clocks t.locals prog stime ∧
    FLOOKUP t.locals «wakeUpAt» = SOME (wtStimeVal stime s.waitTime)
End

Definition ffi_vars_def:
  ffi_vars tlocals  ⇔
  FLOOKUP tlocals «ptr1» = SOME (ValWord 0w) ∧
  FLOOKUP tlocals «len1» = SOME (ValWord 0w) ∧
  FLOOKUP tlocals «ptr2» = SOME (ValWord ffiBufferAddr) ∧
  FLOOKUP tlocals «len2» = SOME (ValWord ffiBufferSize)
End

Theorem state_rel_intro:
  ∀prog s t. state_rel prog s t ⇒
  FLOOKUP t.locals «loc» = SOME (ValLabel (toString s.location)) ∧
  s.ioAction = ARB (* should be about is_input *) ∧
  FLOOKUP t.locals «waitSet» = SOME (wtVal s.waitTime) ∧
  ∃stime.
    FLOOKUP t.locals «sysTime» = SOME (ValWord stime) ∧
    clocks_rel s.clocks t.locals prog stime ∧
    FLOOKUP t.locals «wakeUpAt» = SOME (wtStimeVal stime s.waitTime)
Proof
  rw [] >>
  fs [state_rel_def]
QED


Theorem ffi_vars_intro:
  ∀tlocals.
    ffi_vars tlocals ⇒
    FLOOKUP tlocals «ptr1» = SOME (ValWord 0w) ∧
    FLOOKUP tlocals «len1» = SOME (ValWord 0w) ∧
    FLOOKUP tlocals «ptr2» = SOME (ValWord ffiBufferAddr) ∧
    FLOOKUP tlocals «len2» = SOME (ValWord ffiBufferSize)
Proof
  rw [] >>
  fs [ffi_vars_def]
QED


Definition mono_sysTime_def:
  mono_sysTime (s:('a, 'b)panSem$state) (r:('a, 'b)panSem$state) =
  ∀f res t g res' stime.
    evaluate (f,s) = (res, t) ∧
    evaluate (g,t) = (res', r) ∧
    FLOOKUP s.locals «sysTime» = SOME (ValWord stime) ⇒
    ∃nffi nbytes bytes nstime.
      well_behaved_ffi «get_time» t nffi nbytes bytes (dimword (:α)) ∧
      mem_load One ffiBufferAddr t.memaddrs
               (write_bytearray ffiBufferAddr nbytes t.memory t.memaddrs t.be) =
      SOME (ValWord (n2w nstime)) ∧
      stime ≤ ((n2w nstime):'a word) ∧ nstime < dimword (:α)
      (* 4 ≤ LENGTH nbytes *)
      (*
      (∃n. ARB nbytes = Word (n2w n) ∧
           stime ≤ n ∧ n < dimword (:α)) *)
End


Theorem foo:
  ∀prog d s (t:('a, 'b)panSem$state) res t' nbytes bytes nffi.
    step prog (LDelay d) s
         (mkState
          (delay_clocks (s.clocks) d)
          s.location
          NONE
          NONE) ∧
    state_rel prog s t ∧
    ffi_vars t.locals ∧
    code_installed prog t.code ∧
    mono_sysTime t t' ⇒
    evaluate (task_controller (nClks prog), t) =
    evaluate (task_controller (nClks prog), ARB t)
(* I will need a while theorem *)
Proof
  rpt gen_tac >>
  strip_tac >>
  drule state_rel_intro >>
  drule ffi_vars_intro >>
  strip_tac >>
  strip_tac >>
  fs [step_cases] >> rveq >> gs []
  >- (
    fs [task_controller_def] >>
    fs [panLangTheory.nested_seq_def] >>
    fs [Once evaluate_def] >>
    pairarg_tac >> gs [] >>
    ‘evaluate (Skip, t) = (NONE,t)’ by rewrite_tac [evaluate_def]  >>
    qpat_x_assum ‘mono_sysTime _ _’ assume_tac >>
    fs [mono_sysTime_def] >>
    first_x_assum drule >>
    first_x_assum kall_tac >>
    disch_then (qspecl_then [‘task_controller (nClks prog)’, ‘res’,
                             ‘stime’] mp_tac) >>
    gs [] >>
    impl_tac >- cheat >>
    strip_tac >>
    drule ffi_eval_state_thm >>

    disch_then (qspecl_then [‘nffi’, ‘nbytes’, ‘bytes’] mp_tac) >>
    gs [] >>
    strip_tac >>
    fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    fs [] >>
    qpat_x_assum ‘_= (res,t')’ mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    strip_tac >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>

    fs [ffi_return_state_def] >>
    fs [eval_def] >>
    gs [ffiBufferAddr_def] >>
    gs [is_valid_value_def, shape_of_def] >>
    strip_tac >> rveq >> gs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, nst)=  (res,t')’ >>
    qpat_x_assum ‘_= (res,t')’ mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    strip_tac >>
    fs [] >>
    pairarg_tac >> fs [] >>
    (* state rel is not preserved, rather systime and is_input has some relation with time Sem *)



    fs [Once evaluate_def] >>
    pairarg_tac >> gs [] >>
    pop_assum mp_tac >>
    rewrite_tac [evaluate_def] >>
    rewrite_tac [ffi_return_state_def] >>
    fs [eval_def, ffiBufferAddr_def, mem_load_def] >>
    ‘4000w ∈ t.memaddrs’ by cheat >>
    fs [] >>
    gs [is_valid_value_def] >>
    ‘∃nstime.
       write_bytearray 4000w nSysTime t.memory t.memaddrs t.be 4000w =
       Word nstime’ by cheat >>
    fs [] >>
    fs [shape_of_def] >>
    strip_tac >> fs [] >>



    ‘∃sysTime xs. nSysTime = sysTime::xs’ by cheat >>
    fs [] >>
    fs [write_bytearray_def] >>
    fs [mem_store_byte_def]



Theorem foo:
  ∀prog d s (t:('a, 'b)panSem$state) res t' nbytes bytes nffi.
    step prog (LDelay d) s
         (mkState
          (delay_clocks (s.clocks) d)
          s.location
          NONE
          NONE) ∧
    state_rel prog s t ∧
    ffi_vars t.locals ∧
    code_installed prog t.code ∧
    mono_sysTime t t' ∧
    (*
    well_behaved_ffi «get_time» t nffi nbytes bytes (dimword (:α)) ∧
    *)
    evaluate (task_controller (nClks prog), t) = (res, t') ⇒
    state_rel prog
              (mkState
               (delay_clocks (s.clocks) d)
               s.location
               NONE
               NONE) t' ∧ res = ARB
Proof
  rpt gen_tac >>
  strip_tac >>
  drule state_rel_intro >>
  drule ffi_vars_intro >>
  strip_tac >>
  strip_tac >>
  fs [step_cases] >> rveq >> gs []
  >- (
    fs [task_controller_def] >>
    fs [panLangTheory.nested_seq_def] >>
    fs [Once evaluate_def] >>
    pairarg_tac >> gs [] >>
    ‘evaluate (Skip, t) = (NONE,t)’ by rewrite_tac [evaluate_def]  >>
    qpat_x_assum ‘mono_sysTime _ _’ assume_tac >>
    fs [mono_sysTime_def] >>
    first_x_assum drule >>
    first_x_assum kall_tac >>
    disch_then (qspecl_then [‘task_controller (nClks prog)’, ‘res’,
                             ‘stime’] mp_tac) >>
    gs [] >>
    impl_tac >- cheat >>
    strip_tac >>
    drule ffi_eval_state_thm >>

    disch_then (qspecl_then [‘nffi’, ‘nbytes’, ‘bytes’] mp_tac) >>
    gs [] >>
    strip_tac >>
    fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    fs [] >>
    qpat_x_assum ‘_= (res,t')’ mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    strip_tac >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>

    fs [ffi_return_state_def] >>
    fs [eval_def] >>
    gs [ffiBufferAddr_def] >>
    gs [is_valid_value_def, shape_of_def] >>
    strip_tac >> rveq >> gs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, nst)=  (res,t')’ >>
    qpat_x_assum ‘_= (res,t')’ mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    strip_tac >>
    fs [] >>
    pairarg_tac >> fs [] >>
    (* state rel is not preserved, rather systime and is_input has some relation with time Sem *)

    cheat

QED

(*
  panLang: sysTime   0 1 2 3 4 5 6 7 8 9
                                 |

  panLang: clockA        |

  timeLang: clockA in semantics is 4

  panLang.clockA + timeLang.clockA = panLang.sysTime
*)


Theorem evaluate_check_input_time:
  !io t tm.
    ffi_works io (t:('a,'b) panSem$state) ∧
    ffi_vars t.locals ∧
    (?io. FLOOKUP t.locals «isInput» = SOME (ValWord io)) ==>
    ?ffi mem tm.
      evaluate (check_input_time,t) =
      (NONE,
       t with <| ffi := ffi;
                 memory := mem;
                 locals := t.locals |+
                            («isInput» ,ValWord (active_low io)) |+
                            («sysTime» ,ValWord (n2w tm))
              |>) ∧
      tm < dimword (:α) ∧
      (!stime.
        FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w stime)) ==>
        stime ≤ tm)

Proof
  rpt gen_tac >>
  strip_tac >>
  fs [ffi_vars_def] >>
  fs [check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [evaluate_def] >>
  fs [] >>
  pairarg_tac >> rveq >> gs [] >>
  fs [read_bytearray_def] >>
  gs [ffi_works_def] >>
  fs [ffiBufferSize_def] >>
  ‘16 MOD dimword (:α) = 16’ by (match_mp_tac LESS_MOD >> fs [])>>
  gs [] >>
  qpat_x_assum ‘_ = (res,s1)’ mp_tac >>
  (* calling check_input *)
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  fs [] >>
  strip_tac >>
  rveq >> gs [] >>
  pairarg_tac >> rveq >> gs [] >>
  gs [eval_def, is_valid_value_def, shape_of_def] >>
  rveq >> gs [] >>
  gs [FLOOKUP_UPDATE] >>
  (* calling get_time *)
  gs [read_bytearray_def] >>
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  gs [] >>
  gs [FLOOKUP_UPDATE] >>
  gs [shape_of_def] >>
  rveq >> gs [] >>
  qmatch_goalsub_abbrev_tac ‘t with <|
                               locals := _;
                               memory := m;
                               ffi := f |>’ >>
  qexists_tac ‘f’ >>
  qexists_tac ‘m’ >>
  qexists_tac ‘tm'’ >>
  fs [Abbr ‘m’, Abbr ‘f’] >>
  rw [] >>
  ‘stime MOD dimword (:α) = stime’ by (
    match_mp_tac LESS_MOD >> gs [] >> cheat) >>
  fs []
QED

Theorem evaluate_check_input_time:
  !io t tm.
    ffi_works io (t:('a,'b) panSem$state) ∧
    ffi_vars t.locals ∧
    FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
    tm < dimword (:α) ∧
    (?io. FLOOKUP t.locals «isInput» = SOME (ValWord io)) ==>
    ?ffi mem d.
      evaluate (check_input_time, t) =
      (NONE,
       t with <| ffi := ffi;
                 memory := mem;
                 locals := t.locals |+
                            («isInput» ,ValWord (active_low io)) |+
                            («sysTime» ,ValWord (n2w (tm + d)))
              |>) ∧
      tm + d < dimword (:α)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [ffi_vars_def] >>

  fs [ffi_works_def] >>
  ‘tm' MOD dimword (:α) = tm'’ by (
    match_mp_tac LESS_MOD >> gs []) >>
  fs [] >> rveq >> gs [] >>
  ‘16 MOD dimword (:α) = 16’ by (match_mp_tac LESS_MOD >> fs []) >>

  fs [check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [evaluate_def] >>
  fs [] >>
  pairarg_tac >> rveq >> gs [] >>
  fs [read_bytearray_def] >>
  fs [ffiBufferSize_def] >>
  gs [] >>
  qpat_x_assum ‘_ = (res,s1)’ mp_tac >>
  (* calling check_input *)
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  fs [] >>
  strip_tac >>
  rveq >> gs [] >>
  pairarg_tac >> rveq >> gs [] >>
  gs [eval_def, is_valid_value_def, shape_of_def] >>
  rveq >> gs [] >>
  gs [FLOOKUP_UPDATE] >>
  (* calling get_time *)
  gs [read_bytearray_def] >>
  rewrite_tac [Once ffiTheory.call_FFI_def] >>
  gs [] >>
  gs [FLOOKUP_UPDATE] >>
  gs [shape_of_def] >>
  rveq >> gs [] >>
  qmatch_goalsub_abbrev_tac ‘t with <|
                               locals := _;
                               memory := m;
                               ffi := f |>’ >>
  qexists_tac ‘f’ >>
  qexists_tac ‘m’ >>
  qexists_tac ‘d’ >>
  fs [Abbr ‘m’, Abbr ‘f’]
QED



val _ = export_theory();
