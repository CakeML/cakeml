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
        ValWord (case wt of [] => 0w | _ => 1w);
        ValWord (case wt of [] => 0w
                         | _ => n2w (THE (calculate_wtime s tclks wt)));
        ValLabel (toString dest)]
End


Definition clk_range_def:
  clk_range clks ⇔
    SUM (MAP (size_of_shape o shape_of) clks) ≤ 29
End


Definition restore_from_def:
  (restore_from t lc [] = lc) ∧
  (restore_from t lc (v::vs) =
   restore_from t (res_var lc (v, FLOOKUP t.locals v)) vs)
End

Definition emptyVals_def:
  emptyVals xs = MAP (λ_. ValWord 0w) xs
End


(* the genlist version *)

(*
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
  fs [emptyConsts_def, emptyVals_def] >>
  rw [] >>
  fs [eval_def]
QED
*)

Theorem eval_empty_const_eq_empty_vals:
  ∀s n.
    OPT_MMAP (λe. eval s e) (emptyConsts n) =
    SOME (emptyVals (emptyConsts n))
  (* could be any array of suitable length*)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  fs [emptyConsts_def, emptyVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
  ‘EL n' (MAP f n) = f (EL n' n)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘f’] >>
  qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
  ‘EL n' (MAP f n) = f (EL n' n)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘f’] >>
  fs [eval_def]
QED


Theorem opt_mmap_resetClocks_eq_resetClksVals:
  ∀t clkvals s clks tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    OPT_MMAP (λa. eval t a)
             (resetClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- fs [resetClocks_def, resetClksVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- fs [resetClocks_def, resetClksVals_def] >>
  rw [] >>
  fs [resetClocks_def] >>
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


Theorem clk_range_reset_clks_eq:
  ∀s clks (clkvals:α v list) tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    clk_range clkvals  ⇒
    clk_range ((resetClksVals s.clocks clks tclks):α v list)
Proof
  rw [] >>
  fs [resetClksVals_def] >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [clk_range_def] >>
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
    SOME (MAP (ValWord ∘ n2w ∘ evalDiff s) wt)
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


Theorem comp_term_correct:
  ∀s n cnds tclks dest wt s' t clkvals clks t'.
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    clk_range clkvals ∧
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    t.clock ≠ 0 ∧ (toString dest) IN FDOM t.code ⇒
      ∃t'. evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
           (SOME (Return (retVal s clks tclks wt dest)), t') ∧
           t' = t with locals :=
                restore_from t FEMPTY [«waitTimes»; «resetClks» ; «wakeUpAt»; «waitSet»]
Proof
  rpt gen_tac >>
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
      (resetClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetClocks_eq_resetClksVals >>
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
   fs [indicesOf_def, waitTimes_def] >>
   fs [destruct_def, minOf_def] >>
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
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, dec_clock_def, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule clk_range_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [clk_range_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [restore_from_def]) >>

  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘LENGTH wt’ >>
  ‘(case wt of [] => Const 0w | v2::v3 => Const 1w) =
   (Const 1w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
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
   (resetClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetClocks_eq_resetClksVals >>
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
    (MAP (λn. Field n (Var «resetClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ evalDiff
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
    fs [MAP_MAP_o, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_, stWait)’ >>
  (* now about minOp evaluation *)




Definition clk_rel_def:
  clk_rel clks vname s t <=>
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    FLOOKUP t.locals vname =
    SOME (Struct (MAP (ValWord o n2w o THE o (FLOOKUP s.clocks)) clks))
End


Definition valid_term_def:
  valid_term clks (Tm io cnds tclks dest wt) =
  let wclks = MAP SND wt
  in
    ALL_DISTINCT tclks ∧ ALL_DISTINCT wclks ∧
    LENGTH tclks ≤ LENGTH clks ∧ LENGTH wclks ≤ LENGTH clks ∧
    EVERY (λck. MEM ck clks) tclks ∧ EVERY (λck. MEM ck clks) wclks

End

(* should be reflected in timeSem *)
Definition valid_wtimes_def:
  valid_wtimes (clks:mlstring |-> num) wt =
  EVERY (λ(t,c).
          c IN FDOM clks ⇒
          THE (FLOOKUP clks c) ≤ t) wt
End


Definition valid_clk_var_def:
  valid_clk_var clks fm vname clkvals ⇔
    FLOOKUP fm vname = SOME (Struct clkvals) ∧
    LENGTH clkvals = LENGTH clks ∧
    EVERY (λv. ∃w. v = ValWord w) clkvals
End

(* should be identical to resetClks *)
Definition reset_vals_def:
  reset_vals xs ys =
  MAPi (λn x.
         if (MEM n ys)
         then (ValWord 0w)
         else x)
       xs
End


Definition retVal_def:
  retVal s tclks clks wt dest =
    Struct [
        Struct (resetClksVals s tclks clks);
        ValWord (case wt of [] => 0w | _ => 1w);
        ValWord (case wt of [] => 0w
                         | _ => n2w (THE (calculate_wtime s tclks wt)));
        ValLabel (toString dest)]
End


Definition defined_task_ret_def:
   defined_task_ret fm vname n =
   ∃vs ws wt loc.
     FLOOKUP fm vname =
     SOME (Struct (Struct vs :: MAP ValWord [ws; wt; loc])) ∧
     EVERY (λv. ∃w. v = ValWord w) vs ∧
     LENGTH vs = n
End



(*
  («task_ret»,
  Struct (Struct (empty_consts n) :: MAP Var
  [«wait_set»; «wake_up_at»; «location»]));
*)



(*  indicesOf theorems *)

Theorem flip_enum_not_mem_alookup:
  ∀xs x n.
    ~MEM x xs ⇒
    ALOOKUP (flipEnum n xs) x = NONE
Proof
  Induct >>
  rw [] >>
  fs [flipEnum_def]
QED


Theorem flip_enum_mem_alookup:
  ∀xs x n.
    MEM x xs ⇒
    ∃m.
      ALOOKUP (flipEnum n xs) x = SOME m ∧
      n <= m ∧ m < n + LENGTH xs
Proof
  Induct >>
  rw [] >>
  fs [flipEnum_def] >>
  fs [flipEnum_def] >>
  TOP_CASE_TAC >> fs [] >>
  last_x_assum drule >>
  disch_then (qspec_then ‘n+1’ mp_tac) >>
  strip_tac >> fs []
QED


Theorem indice_of_mem_lt_len:
  ∀x xs.
    MEM x xs ⇒
    indiceOf xs x < LENGTH xs
Proof
  rw [] >>
  fs [indiceOf_def] >>
  drule flip_enum_mem_alookup >>
  disch_then (qspec_then ‘0:num’ mp_tac) >>
  strip_tac >> rfs [] >>
  fs [toNum_def]
QED

Theorem flip_enum_alookup_range:
  ∀xs x n m.
    ALOOKUP (flipEnum n xs) x = SOME m ⇒
    n <= m ∧ m < n + LENGTH xs
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  fs [flipEnum_def] >>
  FULL_CASE_TAC >> fs [] >>
  last_x_assum drule >>
  fs []
QED

Theorem alookup_flip_num_el:
  ∀xs x n m.
    ALOOKUP (flipEnum n xs) x = SOME m ⇒
    EL (m - n) xs = x
Proof
  Induct >> rw []
  >- fs [flipEnum_def] >>
  fs [flipEnum_def] >>
  FULL_CASE_TAC >> fs [] >>
  drule flip_enum_alookup_range >>
  strip_tac >> fs [] >>
  cases_on ‘m − n’ >>
  fs [] >>
  last_x_assum (qspecl_then [‘x’, ‘n+1’, ‘m’] mp_tac) >>
  fs [] >>
  fs [ADD1, SUB_PLUS]
QED


Theorem mem_el_indice_of_eq:
  ∀x xs.
    MEM x xs ⇒
    EL (indiceOf xs x) xs = x
Proof
  rw [] >>
  fs [indiceOf_def] >>
  drule flip_enum_mem_alookup >>
  disch_then (qspec_then ‘0:num’ mp_tac) >>
  strip_tac >> rfs [] >>
  fs [toNum_def] >>
  drule alookup_flip_num_el >>
  fs []
QED

(* not exactly quite true, why I need it *)

(*
Theorem abc:
  ∀ys xs.
    EVERY (λck. MEM ck xs) ys ⇒
    LENGTH (indicesOf xs ys) ≤ LENGTH xs
Proof
  rw [] >>
  fs [indicesOf_def] >>

  qmatch_goalsub_abbrev_tac ‘LENGTH is ≤ _’ >>
  pop_assum(mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘ys’, ‘xs’, ‘is’] >>
  Induct >> rw [] >>
  fs [] >>
  fs [indicesOf_def] >>
  cases_on ‘ys’ >> fs [] >>
  rveq >> rfs [] >> fs [] >>
  cheat
QED



pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def])

  Induct >> rw [] >>
  fs [indicesOf_def] >>
  fs [ADD1] >>


QED
*)



Theorem length_reset_vals_eq:
  ∀ns vs.
    LENGTH (reset_vals vs ns) = LENGTH vs
Proof
  rw [] >>
  fs [reset_vals_def]
QED


Theorem reset_vals_not_indice_same:
  ∀ns vs n.
    ~MEM n ns ∧
    n < LENGTH vs ⇒
    EL n (reset_vals vs ns) = EL n vs
Proof
  rw [] >>
  fs [reset_vals_def]
QED


Theorem reset_vals_el_indice_zero:
  ∀ns vs n.
    MEM n ns ∧
    n < LENGTH vs ⇒
    EL n (reset_vals vs ns) = ValWord 0w
Proof
  rw [] >>
  fs [reset_vals_def]
QED


Theorem opt_mmap_reset_clocks_eq_reset_vals:
  ∀t vs ns clks.
    FLOOKUP t.locals «clks» = SOME (Struct vs) ∧
    LENGTH clks = LENGTH vs ∧
    LENGTH ns ≤ LENGTH clks ⇒
    OPT_MMAP (λa. eval t a)
             (resetClocks «clks» (LENGTH clks) ns) =
    SOME (reset_vals vs ns)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- (
    fs [resetClocks_def] >>
    fs [length_reset_vals_eq]) >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- (
    fs [resetClocks_def] >>
    fs [length_reset_vals_eq]) >>
  rw [] >>
  fs [resetClocks_def] >>
  TOP_CASE_TAC
  >- (
    fs [eval_def] >>
    match_mp_tac reset_vals_el_indice_zero >>
    fs []) >>
  fs [eval_def] >>
  fs [reset_vals_not_indice_same]
QED

(*
  EVERY (λ(t,c). c IN FDOM s.clocks) wt
*)

Theorem calculate_wait_times_eq:
  ∀clks s t wt .
    clk_rel clks «resetClks» s t ∧
    EVERY (λ(t,c). MEM c clks) wt ∧
    valid_wtimes s.clocks wt ⇒
    MAP (eval t)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var «resetClks»)) (indicesOf clks (MAP SND wt)))) =
    MAP (SOME ∘ ValWord ∘ n2w ∘ evalDiff s) wt
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2] >>
  rw [waitTimes_def, indicesOf_def, LIST_REL_EL_EQN] >>
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
  fs [Abbr ‘gg’, Abbr ‘ff’] >>
  cases_on ‘EL n wt’ >> fs [] >>
  fs [evalDiff_def, evalExpr_def, EVERY_EL] >>
  last_x_assum drule >>
  fs [] >> strip_tac >>
  fs [clk_rel_def] >>
  fs [EVERY_MEM] >>
  last_x_assum drule >>
  strip_tac >>
  fs [FDOM_FLOOKUP] >>
  fs [minusT_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [eval_def] >>
  drule indice_of_mem_lt_len >>
  strip_tac >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘EL m (MAP ff _)’ >>
  ‘EL m (MAP ff clks) = ff (EL m clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’, Abbr ‘m’] >>
  pop_assum kall_tac >>
  ‘EL (indiceOf clks r) clks = r’ by (
    match_mp_tac mem_el_indice_of_eq >>
    fs []) >>
  fs [wordLangTheory.word_op_def] >>
  ‘n2w (q − v):'a word = n2w q − n2w v’ suffices_by fs [] >>
  match_mp_tac n2w_sub >>
  fs [valid_wtimes_def] >>
  fs [EVERY_MEM] >>
  qpat_x_assum ‘n < LENGTH wt’ assume_tac >>
  drule EL_MEM >> rfs [] >>
  strip_tac >>
  last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
  fs [] >> strip_tac >> rfs [flookup_thm]
QED


Theorem min_of_eq:
  ∀es t ns t' res v.
    FLOOKUP t.locals «wakeUpAt» = SOME v ∧  shape_of v = One ∧
    evaluate (minOf «wakeUpAt» es, t) = (res, t') ∧
    MAP (eval t) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ⇒
    res = NONE ∧
    (es = [] ⇒
     FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt») ∧
    (es ≠ [] ⇒
     FLOOKUP t'.locals «wakeUpAt» =
     SOME (ValWord ((n2w:num -> α word) (THE (list_min_option ns)))))
Proof
  cheat
QED


(* ignore the If for the time being *)
Theorem comp_term_correct:
  ∀clks s t n cnds tclks dest wt s' clkvals t' loc.
    clk_rel clks «clks» s t ∧
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    valid_term clks (Tm (Input n) cnds tclks dest wt) ∧
    valid_wtimes s.clocks wt ∧
    valid_clk_var clks t.locals «clks» clkvals ∧
    defined_task_ret t.locals «task_ret» (LENGTH clks) ∧
    FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
    t.clock ≠ 0 ∧ (toString dest) IN FDOM t.code ∧
    FLOOKUP t.code loc =
    SOME ([(«clks», genShape (LENGTH clks))],
          compTerm clks (Tm (Input n) cnds tclks dest wt)) ⇒
      evaluate
      (Call (Ret «task_ret» NONE) (Var «location») [Var «clks»], t) = (NONE, t') ∧
      FLOOKUP t'.locals «task_ret» = SOME (retVal s tclks clks wt dest) ∧
      clk_rel clks «» s' t'
      (* task resturn field *)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def] >>
  once_rewrite_tac [eval_def] >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  once_rewrite_tac [eval_def] >>
  fs [valid_clk_var_def] >>
  fs [lookup_code_def] >>
  pop_assum kall_tac >>
  ‘genShape (LENGTH clks) = shape_of (Struct clkvals)’ by (
    fs [genShape_def ,shape_of_def] >>
    fs [GENLIST_eq_MAP] >>
    rw [] >>
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘EL n' clkvals’ mp_tac) >>
    impl_tac
    >- (
      ‘n' < LENGTH clkvals’ by fs [] >>
      drule EL_MEM >> fs []) >>
    strip_tac >>
    fs [shape_of_def]) >>
  fs [compTerm_def] >>
  cases_on ‘wt’ >> fs []
  >- (
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stNew a) _’ >>
   ‘OPT_MMAP (λa. eval stNew a)
      (resetClocks «clks» (LENGTH clks) (indicesOf clks tclks)) =
    SOME (reset_vals clkvals (indicesOf clks tclks))’ by (
     match_mp_tac opt_mmap_reset_clocks_eq_reset_vals >>
     fs [Abbr ‘stNew’] >>
     fs [FLOOKUP_UPDATE] >>
     fs [GSYM FUPDATE_EQ_FUPDATE_LIST] >>
     fs [FLOOKUP_UPDATE] >>
     fs [indicesOf_def] >>
     fs [valid_term_def]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [waitTimes_def, minOf_def] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [eval_def] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stNewer a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stNewer’, FLOOKUP_UPDATE, dec_clock_def, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def] >>
   fs [panLangTheory.size_of_shape_def] >>
   ‘SUM
    (MAP (λa. size_of_shape a)
     (MAP (λa. shape_of a)
      (reset_vals clkvals (indicesOf clks tclks)))) ≤ 29’ by cheat >>
   fs [] >> pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >>
   fs [is_valid_value_def] >>






   ‘OPT_MMAP (λa. eval stNewer a)
    (resetClocks «clks» (LENGTH clks) (indicesOf clks tclks)) =
    SOME (reset_vals clkvals (indicesOf clks tclks))’

     fs []



     )






      )



    )






  TOP_CASE_TAC
  >- fs [eval_def] >>
  pop_assum mp_tac >>





  fs [evalTerm_cases] >>
  rveq >> fs [] >>







QED












Theorem comp_term_correct:
  ∀clks s t n cnds tclks dest wt s' clkvals t' loc.
    clk_rel clks «clks» s t ∧
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    ALL_DISTINCT tclks ∧ ALL_DISTINCT clks ∧
    EVERY (λck. MEM ck clks) tclks ∧
    ALL_DISTINCT (MAP SND wt) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    LENGTH clkvals = LENGTH clks ∧
    EVERY (λv. ∃w. v = ValWord w) clkvals ∧
    FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
    FLOOKUP t.code loc =
    SOME ([(«clks», genShape n)],
          compTerm clks (Tm (Input n) cnds tclks dest wt)) ⇒
      evaluate
        (Call (Ret «task_ret» NONE) (Var «location») [Var «clks»], t) =
      (SOME (Return (Struct [
                        Struct (resetClksVals s tclks clks);
                        ValWord (case wt of [] => 0w | _ => 1w);
                        ValWord (case wt of [] => 0w
                                         | _ => n2w (THE (calculate_wtime s tclks wt)));
                        ValLabel (toString dest)])), t') ∧
      clk_rel clks «» s' t'
      (* task resturn field *)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evalTerm_cases] >>
QED

(*
  SOME (Struct (MAP (ValWord o n2w o THE o (FLOOKUP s.clocks)) clks))
*)



(* write about the code installed *)

Theorem comp_term_correct:
  ∀s n cnds tclks dest wt s' t clks stime clkvals t.
    clk_rel clks «clks» s t ∧
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    ALL_DISTINCT tclks ∧ ALL_DISTINCT clks ∧
    EVERY (λck. MEM ck clks) tclks ∧
    ALL_DISTINCT (MAP SND wt) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    LENGTH clkvals = LENGTH clks ∧
    EVERY (λv. ∃w. v = ValWord w) clkvals ⇒
      evaluate (comp_term clks (Tm (Input n) cnds tclks dest wt), t) =
      (SOME (Return ARB), ARB t) ∧ clk_rel clks «clks» s' t'
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evalTerm_cases] >>



QED




(* leave it for the time being, and add back the defs later *)
(* specify it in terms of invariants *)

Theorem min_of_eq:
  ∀es n t ns t' res v.
    (* «wakeUpAt» IN FDOM t.locals ∧ *)
    FLOOKUP t.locals «wakeUpAt» = SOME v ∧  shape_of v = One ∧
    evaluate (minOf «wakeUpAt» n es, t) = (res, t') ∧
    MAP (eval t) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ⇒
    res = NONE ∧
    (es = [] ⇒
     FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt») ∧
    (es ≠ [] ∧ n = 0 ⇒
     FLOOKUP t'.locals «wakeUpAt» =
     SOME (ValWord ((n2w:num -> α word) (THE (list_min_option ns)))))
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >>
  fs []
  >- (
   fs [minOf_def] >>
   fs [evaluate_def]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minOf_def] >>
  conj_tac >- cheat >>
  rw [] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  rfs [] >>
  fs [is_valid_value_def] >>
  rfs [] >>
  rfs [shape_of_def] >>
  rveq >> rfs [] >> fs [] >>
  fs [list_min_option_def] >>
  last_x_assum
  (qspecl_then
   [‘1’, ‘t with locals := t.locals |+ («wakeUpAt» ,ValWord (n2w h'))’] mp_tac) >>
  rfs [] >>
  fs [FLOOKUP_UPDATE] >>
  fs [shape_of_def] >>
  disch_then (qspec_then ‘t''’ mp_tac) >>
  rfs [] >>
  impl_tac >- cheat >>
  fs [] >> rfs [] >>
  strip_tac >>
  cases_on ‘es’ >>
  fs []
  >- cheat >>



  rfs []





  rfs [flookup_thm] >>





  rw [] >>
  fs [] >>

QED













Theorem foo:
  evaluate
  (min_of «wake_up_at»
   (wait_times «sys_time» (MAP FST wt)
    (destruct
     (mk_struct (LENGTH clks) («sys_time» ,«clks» )
      (indices_of clks tclks)) (indices_of clks (MAP SND wt)))),
   t with
     locals :=
   t.locals |+ («wait_set» ,value) |+ («wake_up_at» ,value')) =
  (res,s1)
Proof
  rw [] >>
  fs [calculate_wtime_def] >>





QED






Theorem abc:
  evaluate (update_wakeup_time («wake_up_at» ,«sys_time» )
            (wait_times «sys_time» (MAP FST wt)
             (destruct
              (mk_struct (LENGTH clks)
               («sys_time» ,«clks» )
               (indices_of clks tclks))
              (indices_of clks (MAP SND wt)))),
            t with
              locals :=
            t.locals |+ («wait_set» ,value) |+
             («wake_up_at» ,value')) = ARB
Proof
  rw [] >>
  fs [update_wakeup_time_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>



QED



Theorem comp_term_correct:
  ∀s n cnds tclks dest wt s' t clks stime clkvals t.
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    ALL_DISTINCT tclks ∧ ALL_DISTINCT clks ∧
    EVERY (λck. MEM ck clks) tclks ∧
    ALL_DISTINCT (MAP SND wt) ∧
    FLOOKUP t.locals «sys_time» = SOME (ValWord stime) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    LENGTH clkvals = LENGTH clks ∧
    EVERY (λv. ∃w. v = ValWord w) clkvals ⇒
      evaluate (comp_term clks (Tm (Input n) cnds tclks dest wt), t) =
      (SOME (Return ARB), ARB t) ∧ ARB s'
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evalTerm_cases] >>



  fs [resetClocks_def] >>






  fs [comp_term_def, panLangTheory.decs_def,
      panLangTheory.nested_seq_def] >>
  fs [evaluate_def] >>

  fs [calculate_wtime_def] >>




  cases_on ‘tclks’ >> fs []
  >- (
   fs [calculate_wtime_def] >> (* timeSem *)
   fs [resetClocks_def] >>
   fs [FUPDATE_LIST_THM] >>
   ‘s with clocks := s.clocks = s’ by cheat >>
   fs [] >>
   pop_assum kall_tac >>
   (* prove corresondance between list_min_option and min_of *)


    (* panLang *)
   fs [indices_of_def] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>



   fs [update_wakeup_time_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [destruct_def] >>
   fs [wait_times_def] >>
   fs [mk_struct_def] >>
   fs [MAP_MAP_o] >>


    fs [min_of_def] >>



    fs [OPT_MMAP_def] >>


  )






QED



(* EVERY (λck. ck IN FDOM s.clocks) tclks ∧ *)




Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  ALL_DISTINCT tclks ∧
  ALL_DISTINCT clks ∧
  EVERY (λck. MEM ck clks) tclks ∧
  ALL_DISTINCT (MAP SND wt) ∧
  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
  LENGTH clkvals = LENGTH clks ∧
  EVERY (λv. ∃w. v = ValWord w) clkvals ∧







  evaluate (comp_term clks (Tm io cnds tclks dest wt), t) =
  (SOME (Return ARB), t')
Proof


QED





  (* is it derivable from the def of evalTerm *)
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
  tms = (Tm io cnds tclks dest wt) :: tmss ∧
  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_term («clks»,clks) tms) ∧

Proof

QED







(* :timeSem$state -> num option -> term -> timeSem$state -> bool *)
Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧

  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_step («clks»,clks) tms) ∧
  (* assume that comp_conditions (vname, clks) cds holds for the current state
     so that I get to reason about comp_term then *) ∧





  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  (* clkvals and tclks follow some order *)
  FLOOKUP t.locals «task_ret» = SOME (Struct [Struct clkvals; wset; wtime; lc]) ∧
  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_step («clks»,clks) tms) ∧
  (* assume that comp_conditions (vname, clks) cds holds for the current state
     so that I get to reason about comp_term then *) ∧
  evaluate (Call (Ret «task_ret» NONE) (Var «location»)
            [Var «sys_time»; Field 0 (Var «task_ret»)]) =
  (Return ARB,t')
Proof
QED

(*
   FLOOKUP st_code (toString loc) =
      SOME ([(«sys_time», One); («clks», gen_shape n)],
            comp_terms comp_step («clks»,clks) tms)
*)

(*
  assume that comp_conditions (vname, clks) cds holds for the current state
  so that I get to reason about comp_term then
*)

(*
  comp_conditions («clks»,clks) cds
  what will happen when none of the conditions are not true
*)


(* :timeSem$state -> num option -> term -> timeSem$state -> bool *)
Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  (* is it derivable from the def of evalTerm *)
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
  tms = (Tm io cnds tclks dest wt) :: tmss ∧
  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_term («clks»,clks) tms) ∧










  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  (* clkvals and tclks follow some order *)
  FLOOKUP t.locals «task_ret» = SOME (Struct [Struct clkvals; wset; wtime;lc]) ∧
  FLOOKUP t.code loc = SOME ARB

Proof
QED


  t.code = code is installed for the term ∧






  Call (Ret «task_ret» NONE) (Var «location»)
       [Var «sys_time»; Field 0 (Var «task_ret»)
        (* elapsed time clock variables *)]




Proof


QED





(* ioAction and io are related *)

Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks loc wt) t ∧
  comp_term clks (Tm io cnds tclks loc wt) = Return (Struct [])
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [step_def]

QED





Definition code_installed_def:
  code_installed prog st_code <=>
  ∀loc tms.
    MEM (loc,tms) prog ⇒
    let clks = clks_of prog;
        n = LENGTH clks
    in
      FLOOKUP st_code (toString loc) =
      SOME ([(«sys_time», One); («clks», gen_shape n)],
            comp_terms comp_step («clks»,clks) tms)
End

(*
  ta_prog = (prog, init_wtime) ∧
  res = NONE would ensure that the FFI returned with the correct results
*)

(*
  about ioAction:
  should be none in the beginning

  state relations:
  we can set up intitial wait time for s
*)

Theorem time_to_pan_compiler_correct:
  step prog label s s' ∧
  (* prog ≠ [] ∧ *)
  s.waitTime = wtime ∧
  s.location = FST (ohd prog) ∧
  (FDOM s.clocks) = set (clks_of prog) ∧
  s.ioAction = NONE ∧
  code_installed prog t.code ∧
  evaluate (start_controller (prog,wtime), t) = (res, t') ∧
  res = NONE ⇒
    something
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [step_def]

QED



Theorem time_to_pan_compiler_correct:
  step prog label s s' ∧
  s.waitTime = wtime ∧
  s.location = FST (ohd prog) ∧
  (FDOM s.clocks) = set (clks_of prog) ∧
  s.ioAction = NONE ∧
  code_installed prog t.code ⇒
  ∃ck. evaluate (main_while_loop, t with clock := t.clock + ck) =
       evaluate (main_while_loop, t') ∧
       state_rel s' t'
Proof
QED

(*
  ioaction of timeSem state represents the triggered action or action generated to
  reach to a particular state
*)


(*
  timeSem permits:
  1. a delay transition with no ioaction
  2. action transition, (input or output), time does not pass in these transitions

  what is the behavior of the corresponding pancake program:
  1. delay transitions:
     1. stay within the loop, waiting for the input trigger
     2. stay within the loop, waiting for the wakeup time or input trigger

  2. action tanstion:
     1. input trigger: break the loop, call the function
     2. output transtion: happens only within the call
        (I think), signal the output

  pickTerm and evalTerm are also relevant
  time semantics only talk about delay, input, but also pick term and evaluate term
  I think while loop related conditions should come from pickterm and evalterm
*)


(*
  what is the difference between step_ind and step_strongind
  the induction rule is phrased differently (step_ind)
   step _ _ _ _ => step' _ _ _
*)


Theorem foo:
  ∀prog label st st'.
    step prog label st st' ⇒
    (∀t wtime s res s'.
       prog ≠ [] ⇒
       evaluate (start_controller (prog,wtime), s) = (res, s'))
Proof

QED




Theorem abc:
  ∀prog label st st'.
    step prog label st st' ⇒
     step prog label st st'
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [step_def]

QED




Theorem abc:
  ∀prog label st st'.
    step prog label st st' ⇒
    (∀t wtime s res s'.
       prog ≠ [] ⇒
       evaluate (start_controller (prog,wtime), s) = (res, s'))
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [] >>

  fs [start_controller_def] >>
  fs [task_controller_def] >>
  fs [] >>







QED



Theorem abc:
  ∀prog label st st'.
    step prog label st st' ⇒
    (∀t.
       label = (LDelay t) ⇒
       evaluate (start_controller (prog,init_wake_time),s) = (res,t))
Proof
  ho_match_mp_tac step_ind >>
  rw [] >> fs [] >>



QED


(*
  step (FST prog) label st st' ∧
  evaluate (start_controller prog,s) = (res,t)
*)







(* might not be needed *)
Definition clk_rel_def:
  clk_rel str st =
     ARB str.clocks st.locals
End

(*
  we need some assumptions on FFI

*)




(*
  1. step (FST prog) label st st'
  2. evaluate (start_controller prog,s) = (res,t)
  3. what is the relation with st and s

Datatype:
  store =
  <| clocks   : clock |-> time
   ; location : loc
   ; consumed : in_signal option
   ; output   : out_signal option
   ; waitTime : time option
  |>
End

*)



(*
  store
  state

  "timeSem", "step_def"
  "timeSem", "step_ind"
  "timeSem", "step_rules"
  "timeSem", "step_strongind"

*)





val _ = export_theory();
