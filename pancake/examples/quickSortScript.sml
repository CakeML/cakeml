(*
  Proof of correctness of a simplified in-place quicksort program.
*)

open preamble HolKernel Parse boolLib bossLib stringLib numLib intLib
     panLangTheory panPtreeConversionTheory panSemTheory
     panHoareTheory panHoareLib;

val _ = new_theory "quickSort";

(* copied from panConcreteExampleScript *)

val (ast, _) = parse_pancake_file "../examples/quick_sort.pnk"

Definition the_code_def:
  the_code = FEMPTY |++ (MAP (I ## SND) (^ast))
End

Theorem lookup_do_sort = EVAL ``FLOOKUP (the_code) «do_sort»``

val do_sort_loop =
  lookup_do_sort |> concl |> find_term (can (match_term ``(panLang$While _ _)``))

Definition w_count_def:
  w_count i x = (if ~ (i < x) then []
    else GENLIST (\j. i + n2w j) (w2n (x - i)))
End

Theorem w_count_MEM:
  MEM y (w_count i x) <=> i <= y /\ y < x
Proof
  rw [w_count_def] \\ TRY EQ_TAC
  >- (
    metis_tac [ WORD_LESS_EQ_LESS_TRANS]
  )
  \\ cheat
QED

Theorem word_plus_one_le:
  x < y ==> x + 1w <= y
Proof
  qspec_then `w2n (x + 1w)` mp_tac (GEN_ALL wordsTheory.word_msb_n2w_numeric)
  \\ qspec_then `w2n x` mp_tac (GEN_ALL wordsTheory.word_msb_n2w_numeric)
  \\ simp [w2n_lt]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ qspec_then `y` mp_tac w2n_lt
  \\ rw [] \\ fs [WORD_LE, WORD_LT, wordsTheory.w2n_minus1]
  \\ fs []
QED

Theorem word_le_minus_one:
  x < y ==> x <= y + (-1w)
Proof
  CCONTR_TAC \\ fs []
  \\ full_simp_tac bool_ss [GSYM WORD_NOT_LESS]
  \\ drule word_plus_one_le
  \\ simp []
  \\ full_simp_tac bool_ss [GSYM WORD_NOT_LESS]
QED

Theorem w_count_cons:
  i < x ==> w_count i x = i :: w_count (i + 1w) x
Proof
  simp [w_count_def]
  \\ disch_tac
  \\ DEP_ONCE_REWRITE_TAC [GSYM wordsTheory.SUC_WORD_PRED]
  \\ simp [listTheory.GENLIST_CONS, wordsTheory.WORD_LEFT_ADD_DISTRIB]
  \\ simp [combinTheory.o_DEF, wordsTheory.n2w_SUC]
  \\ rw []
  >- (
    strip_tac
    \\ full_simp_tac bool_ss [wordsTheory.WORD_SUB_INTRO]
    \\ fs [wordsTheory.WORD_EQ_SUB_ZERO]
  )
  >- (
    fs [WORD_NOT_LESS]
    \\ drule_then mp_tac WORD_LESS_EQUAL_ANTISYM
    \\ simp [word_plus_one_le] 
  )
QED

Theorem w_count_snoc:
  i < x ==> w_count i x = w_count i (x - 1w) ++ [x - 1w]
Proof
  simp [w_count_def]
  \\ disch_tac
  \\ DEP_ONCE_REWRITE_TAC [GSYM wordsTheory.SUC_WORD_PRED]
  \\ simp [GENLIST]
  \\ rw []
  >- (
    strip_tac
    \\ full_simp_tac bool_ss [wordsTheory.WORD_SUB_INTRO]
    \\ fs [wordsTheory.WORD_EQ_SUB_ZERO]
  )
  >- (
    fs [WORD_NOT_LESS]
    \\ drule_then mp_tac WORD_LESS_EQUAL_ANTISYM
    \\ simp [word_le_minus_one]
    \\ rw []
    \\ REWRITE_TAC [WORD_SUB_INTRO, WORD_MULT_CLAUSES, WORD_SUB_SUB]
    \\ simp []
  )
QED

Theorem w_count_drop1:
  i - 1w < x ==> w_count i x = DROP 1 (w_count (i - 1w) x)
Proof
  rw []
  \\ drule w_count_cons
  \\ simp []
QED

Definition while_then_def:
  while_then C B X = Seq (While C B) X
End

Definition clock_after_def:
  clock_after s1 s2 = (s2.clock < s1.clock)
End

Theorem FLOOKUP_res_var:
  FLOOKUP (res_var fmap (nm1, r)) nm2 = if nm1 = nm2 then r
    else FLOOKUP fmap nm2
Proof
  Cases_on `r` \\ simp [res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM]
QED

Theorem res_var_FUPDATE_LIST:
  res_var (fmap |++ xs) (nm, FLOOKUP fmap nm)
    = fmap |++ (FILTER (((<>) nm) o FST) xs)
Proof
  Cases_on `FLOOKUP fmap nm` \\ simp [res_var_def]
  >- (
    simp [finite_mapTheory.DOMSUB_FUPDATE_LIST]
    \\ simp [DOMSUB_NOT_IN_DOM, FDOM_FLOOKUP]
  )
  >- (
    simp [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_FUPDATE_LIST]
    \\ simp [combinTheory.o_DEF, ALOOKUP_FILTER |> SIMP_RULE std_ss [ELIM_UNCURRY],
        GSYM FILTER_REVERSE]
    \\ rw [] \\ rpt (TOP_CASE_TAC \\ fs [])
    \\ simp []
  )
QED

Theorem FUPDATE_LIST_UNCHANGED:
  EVERY (\(x, y). FLOOKUP f x = SOME y) xs ==>
  f |++ xs = f
Proof
  simp [fmap_eq_flookup, FLOOKUP_UPDATE, FLOOKUP_FUPDATE_LIST]
  \\ rw []
  \\ TOP_CASE_TAC \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM]
  \\ res_tac
  \\ fs []
QED

Theorem evaluate_while_then_imp:
  evaluate (while_then C B X, st1) = (res, st2) ==>
  (? res1 step_st. evaluate (If C (Seq Tick B) Break, st1) = (res1, step_st) /\
    (case res1 of
        | NONE => (evaluate (while_then C B X, step_st) = (res, st2) /\
            clock_after st1 step_st)
        | SOME Continue => (evaluate (while_then C B X, step_st) = (res, st2) /\
            clock_after st1 step_st)
        | SOME Break => evaluate (X, step_st) = (res, st2)
        | _ => (res1, step_st) = (res, st2)
    ))
Proof
  simp [evaluate_def]
  \\ simp [while_then_def]
  \\ simp [Once evaluate_def]
  \\ simp [Once evaluate_def]
  \\ simp [GSYM while_then_def]
  \\ pairarg_tac \\ fs []
  \\ fs [CaseEq "option", CaseEq "v", CaseEq "word_lab"]
  \\ fs [CaseEq "bool"]
  \\ simp [evaluate_def]
  \\ pairarg_tac \\ fs []
  \\ rename [`evaluate (_, dec_clock _) = (_, step_st)`]
  \\ reverse (qsuff_tac `clock_after st1 step_st`)
  >- (
    imp_res_tac evaluate_clock
    \\ fs [clock_after_def, dec_clock_def]
  )
  \\ fs [CaseEq "option", CaseEq "result"] \\ rw []
  \\ simp [while_then_def, EVAL ``evaluate (panLang$Seq _ _, _)``]
QED

Theorem evaluate_while_then_to_skip:
  evaluate (while_then C B X, st1) = (res, st2) ==>
  ? res1 step_st.
  evaluate (while_then C B Skip, st1) = (res1, step_st) /\
  (case res1 of
    | NONE => evaluate (X, step_st) = (res, st2)
    | _ => (res1, step_st) = (res, st2)
  )
Proof
  simp [while_then_def, EVAL ``evaluate (panLang$Seq _ _, _)``]
  \\ pairarg_tac \\ fs []
  \\ simp [evaluate_def]
  \\ rw []
  \\ BasicProvers.every_case_tac
  \\ fs []
QED

Theorem clock_after_induct:
  (! s. (! step_st. clock_after s step_st ==> P step_st) ==> P s) ==>
  ! s. P s
Proof
  rw []
  \\ measureInduct_on `s.clock`
  \\ fs [clock_after_def]
QED

Theorem UPDATE_LIST_UNCHANGED:
  EVERY (\(x, y). f x = y) xs ==>
  f =++ xs = f
Proof
  Induct_on `xs` \\ simp [UPDATE_LIST_THM]
  \\ simp [FORALL_PROD, combinTheory.UPDATE_APPLY_IMP_ID]
QED

Triviality w2n_rotate:
  w2n (x + INT_MINw) = (if word_msb x then w2n x - INT_MIN (:'a) else w2n x + INT_MIN (:'a))
Proof
  cheat
QED

Triviality word_msb_numeric:
  word_msb (x : 'a word) = (INT_MIN (:'a) <= w2n x)
Proof
  ONCE_REWRITE_TAC [GSYM n2w_w2n]
  \\ REWRITE_TAC [word_msb_n2w_numeric]
  \\ simp []
QED

Theorem word_lt_rotate:
  x < y <=> w2n (x + INT_MINw) < w2n (y + INT_MINw)
Proof
  simp [WORD_LT, word_add_def, w2n_rotate]
  \\ qspec_then `x` mp_tac w2n_lt
  \\ qspec_then `y` mp_tac w2n_lt
  \\ rw []
  \\ fs [word_msb_numeric, GSYM dimword_IS_TWICE_INT_MIN]
QED

Theorem word_less_plus_one:
  x <= y /\ y < z ==>
  x < y + 1w
Proof
  rw []
  \\ drule_then irule WORD_LESS_EQ_LESS_TRANS
  \\ fs [word_lt_rotate]
  \\ DEP_ONCE_REWRITE_TAC [GSYM wordsTheory.SUC_WORD_PRED |> Q.SPEC `_ + 1w`]
  \\ simp []
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ REWRITE_TAC [WORD_SUM_ZERO]
  \\ CCONTR_TAC \\ fs []
  \\ full_simp_tac bool_ss [WORD_SUB_INTRO, WORD_MULT_CLAUSES, WORD_SUB_PLUS]
  \\ fs []
  \\ full_simp_tac bool_ss [w2n_minus1, arithmeticTheory.LESS_EQ]
  \\ fs []
  \\ dxrule LESS_EQ_LESS_TRANS
  \\ simp []
  \\ irule_at Any w2n_lt
  \\ simp []
QED

Theorem word_minus_one_less:
  x <= y /\ z < x ==>
  x + (-1w) < y
Proof
  rw []
  \\ drule_at_then Any irule WORD_LESS_LESS_EQ_TRANS
  \\ fs [word_lt_rotate]
  \\ DEP_ONCE_REWRITE_TAC [GSYM wordsTheory.SUC_WORD_PRED |> Q.SPEC `_ + INT_MINw`]
  \\ simp []
  \\ simp [WORD_SUM_ZERO]
  \\ CCONTR_TAC \\ fs []
QED

Triviality w_count_add_one_snoc_cons:
  x < y ==> y < z ==>
  w_count x (y + 1w) = x :: w_count (x + 1w) y ++ [y]
Proof
  rw []
  \\ DEP_ONCE_REWRITE_TAC [w_count_snoc]
  \\ simp [w_count_cons]
  \\ irule word_less_plus_one
  \\ simp [WORD_LESS_IMP_LESS_OR_EQ]
  \\ metis_tac []
QED

val do_sort_while_then =
  list_mk_icomb (``\a b. while_then a b Skip``, snd (strip_comb do_sort_loop))
    |> DEPTH_CONV BETA_CONV |> concl |> rhs

Triviality PERM_MAP_update_flip:
  x_v = f y ==> y_v = f x ==> ALL_DISTINCT zs ==>
  MEM x zs ==> MEM y zs ==>
  PERM (MAP (f ⦇ x ↦ x_v; y ↦ y_v ⦈) zs) (MAP f zs)
Proof
  REWRITE_TAC [Once MEM_SPLIT] \\ rw []
  \\ fs [MEM_APPEND, UPDATE_APPLY_IMP_ID]
  \\ fs [MEM_SPLIT]
  \\ fs [ALL_DISTINCT_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
  \\ simp [UPDATE_APPLY, Q.SPECL [`xs`, `xs`, `f (| _ |-> _; _ |-> _ |)`, `f`] MAP_CONG]
  \\ DEP_REWRITE_TAC [Q.SPECL [`xs`, `xs`, `f (| _ |-> _; _ |-> _ |)`, `f`] MAP_CONG]
  \\ simp [sortingTheory.PERM_APPEND_IFF]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC, PERM_APPEND_IFF]
  \\ irule_at Any APPEND_PERM_SYM
  \\ simp_tac bool_ss [APPEND_ASSOC, PERM_SWAP_L_AT_FRONT, PERM_REFL]
  \\ rw [combinTheory.UPDATE_def] \\ fs []
QED

Triviality NOT_NONE_EQ_EX = IS_SOME_EQ_NOT_NONE |> GSYM |> REWRITE_RULE [IS_SOME_EXISTS]

Triviality case_opt_f = TypeBase.case_pred_imp_of ``: 'a option``
  |> Q.GEN `v` |> Q.ISPEC `F` |> Q.SPEC `\x. x` |> SIMP_RULE bool_ss []




Theorem do_sort_hoare_correct:


  !Q.
  (!s ls. Q (SOME TimeOut) s ls) ==>
  hoare_logic G 
    (\s ls.
        the_code ⊑ s.code /\
        EVERY ((<>) NONE) (MAP (local_word s.locals) [«base_addr»; «x»; «y»]) /\
        let v = tlw s in
        ?len.
        0w <= v «x» /\ v «y» <= len /\
        let addrs = MAP (\i. v «base_addr» + (i * 8w)) (w_count 0w len) in
        set addrs SUBSET s.memaddrs /\
        EVERY (((<>) NONE) o word_of o s.memory) addrs /\
        (!shuffle. PERM shuffle (MAP s.memory addrs) ==>
            !locs clock. Q (SOME (Return (ValWord 0w)))
                (s with <| locals := locs; clock := clock; memory := s.memory =++ ZIP (addrs, shuffle) |>) ls)
    )
    (TailCall (Label «do_sort») [Var «base_addr»; Var «x»; Var «y»])
    Q

Proof

  ho_match_mp_tac hoare_logic_image_triple_induction
  \\ rw []
  \\ irule hoare_logic_rev_init
  \\ rpt rev_hoare_tac
  \\ qspec_then `the_code` irule hoare_logic_TailCall_rev_code
  \\ simp [lookup_do_sort]
  \\ rpt rev_hoare_tac
  \\ qspec_then `the_code` irule hoare_logic_TailCall_norm_args_rev_code
  \\ simp [lookup_do_sort]
  \\ irule hoare_logic_use_context_triple_rev
  \\ rpt acc_abbrev_gamma_tac
  \\ simp []
  \\ irule_at Any boolTheory.OR_INTRO_THM1
  \\ simp []
  \\ rpt rev_hoare_tac
  \\ qspec_then `the_code` irule hoare_logic_TailCall_norm_args_rev_code
  \\ simp [lookup_do_sort]
  \\ irule hoare_logic_use_context_triple_rev
  \\ rpt acc_abbrev_gamma_tac
  \\ simp []
  \\ irule_at Any boolTheory.OR_INTRO_THM1
  \\ simp []
  \\ rpt rev_hoare_tac

  \\ qspec_then `\s ls.
    the_code ⊑ s.code /\
    EVERY ((<>) NONE) (MAP (local_word s.locals) [«x»;«y»;«xt»;«yt»;«piv»;«len»;«base_addr»]) /\
    let v = tlw s in
    ?len.
    v «x» < len /\ v «y» <= len /\ 0w <= v «x» /\ 0w <= v «y» /\
    v «xt» < len /\ v «yt» < len /\ 0w <= v «xt» /\ 0w <= v «yt» /\
    v «xt» <= v «yt» /\
    let addrs = MAP (\i. v «base_addr» + (i * 8w)) (w_count 0w (v «len»)) in
    set addrs SUBSET s.memaddrs /\
    EVERY (((<>) NONE) o word_of o s.memory) addrs /\
    (!shuffle. PERM shuffle (MAP s.memory addrs) ==>
        !locs clock. Q (SOME (Return (ValWord 0w)))
            (s with <| locals := locs; clock := clock; memory := s.memory =++ ZIP (addrs, shuffle) |>) ls)`
    (REWRITE_TAC o single) (GSYM annot_While_def)
  \\ rpt rev_hoare_tac
  \\ simp hoare_simp_rules

  \\ conj_tac
  >- (
    csimp ([logic_imp_def] @ hoare_simp_ex_rules)
    \\ rw []
    \\ ntac 3 (imp_res_tac neq_NONE_IMP \\ fs [])
    \\ gs [val_of_eq_SOME, word_of_eq_SOME]
    \\ simp [pan_op_def, wordLangTheory.word_op_def, flatten_def, mem_stores_def, mem_store_def]
    \\ gvs []
    \\ rw []
    \\ Cases_on 
    \\ reverse (Cases_on `word_cmp Less (tlw s «x») (tlw s «y»)`) \\ gs []

 
  \\ WITHOUT_ABBREVS (simp [])

  \\ simp [empty_locals_def]
  \\ qspec_then `the_code` irule hoare_logic_TailCall_norm_args_rev_code
  \\ simp [lookup_do_sort]



Triviality do_sort_loop_correct:

  ! st1 res st2. panSem$evaluate (^do_sort_while_then, st1) = (res, st2) ==>
  EVERY ((<>) NONE) (MAP (local_word st1.locals) [«x»;«y»;«piv»;«len»;«base_addr»]) /\
  (
  let v nm = THE (local_word st1.locals nm) in
  v «x» < v «len» /\ v «y» < v «len» /\ 0w < v «x» /\ 0w < v «y» /\
  let addrs = MAP (\i. v «base_addr» + (i * 8w)) (w_count 0w (v «len»)) in
  set addrs SUBSET st1.memaddrs /\
  EVERY (((<>) NONE) o word_of o st1.memory) addrs
  )
  ==>
  (res = SOME TimeOut) \/ (res = NONE /\
  (?n shuffle x_v y_v.
    let v nm = THE (local_word st1.locals nm) in
    let addrs = MAP (\i. v «base_addr» + (i * 8w)) (w_count 0w (v «len»)) in
    let m2 = st1.memory =++ ZIP (addrs, shuffle) in
    st2 = (st1 with <| memory := m2; clock := st1.clock - n;
        locals := st1.locals |++ [(«x», x_v); («y», y_v)] |>) /\
    PERM shuffle (MAP st1.memory addrs)
  ))

Proof

  ho_match_mp_tac clock_after_induct
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ dxrule evaluate_while_then_imp
  \\ rpt (disch_tac ORELSE gen_tac)
  \\ fs []
  \\ imp_res_tac (hd (RES_CANON IS_SOME_EXISTS) |> REWRITE_RULE [optionTheory.IS_SOME_EQ_NOT_NONE])
  \\ fs []
  \\ imp_res_tac (hd (RES_CANON IS_SOME_EXISTS) |> REWRITE_RULE [optionTheory.IS_SOME_EQ_NOT_NONE])
  \\ fs [val_of_eq_SOME, val_of_def]
  \\ imp_res_tac (hd (RES_CANON IS_SOME_EXISTS) |> REWRITE_RULE [optionTheory.IS_SOME_EQ_NOT_NONE])
  \\ fs [word_of_eq_SOME, word_of_def]
  \\ gvs []
  \\ gs [Once evaluate_def, eval_def]
  \\ fs [evaluate_def, eval_def]
  \\ rename [`word_cmp Less x_v y_v`]
  \\ reverse (Cases_on `word_cmp Less x_v y_v`) \\ fs []

  >- (
    gvs [evaluate_def]
    \\ irule_at Any PERM_REFL
    \\ DEP_REWRITE_TAC [UPDATE_LIST_UNCHANGED]
    \\ simp [ZIP_MAP, EVERY_MAP]
    \\ simp [panSemTheory.state_component_equality]
    \\ irule_at Any (GSYM FUPDATE_LIST_UNCHANGED)
    \\ simp []
    \\ qexists_tac `0`
    \\ simp []
  )

  >- (
    gs [evaluate_def, eval_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [CaseEq "bool" |> Q.GEN `x` |> Q.ISPEC `cl = 0n`] \\ gvs []
    \\ gs [dec_clock_def, pan_op_def, wordLangTheory.word_op_def, flatten_def,
        mem_stores_def, mem_store_def,
        finite_mapTheory.FLOOKUP_UPDATE, mem_load_def]
    (* get x and y in memaddrs *)
    \\ fs [asmTheory.word_cmp_def]
    \\ rename [`w_count 0w len_v`]
    \\ qspecl_then [`x_v`, `0w`, `len_v`] mp_tac
        (w_count_MEM |> GSYM |> RES_CANON |> hd |> SIMP_RULE bool_ss [PULL_FORALL])
    \\ qspecl_then [`y_v`, `0w`, `len_v`] mp_tac
        (w_count_MEM |> GSYM |> RES_CANON |> hd |> SIMP_RULE bool_ss [PULL_FORALL])
    \\ rw [WORD_LESS_IMP_LESS_OR_EQ]
    \\ drule SUBSET_IMP
    \\ drule (hd (RES_CANON EVERY_MEM))
    \\ simp [MEM_MAP, PULL_EXISTS]
    \\ disch_then imp_res_tac
    \\ disch_then imp_res_tac
    \\ gs [IS_SOME_EXISTS |> REWRITE_RULE [optionTheory.IS_SOME_EQ_NOT_NONE],
        word_of_eq_SOME, val_of_eq_SOME]
    \\ qmatch_asmsub_abbrev_tac `evaluate (if (if C then _ else _) <> _ then _ else _, _)`

    \\ Cases_on `C` \\ fs [markerTheory.Abbrev_def]
    >- (
      gs [evaluate_def, eval_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def,
          is_valid_value_def, shape_of_def]
      \\ gvs []
      \\ first_x_assum (drule_then drule)
      \\ impl_tac
      >- (
        simp [FLOOKUP_res_var, FLOOKUP_UPDATE, val_of_def, word_of_def]
        \\ drule_then assume_tac word_plus_one_le
        \\ drule_then (irule_at Any) WORD_LESS_EQ_LESS_TRANS
        \\ simp []
        \\ rpt (drule_at_then (Pat `_ < _`) (irule_at Any) word_less_plus_one)
        \\ simp [WORD_LESS_IMP_LESS_OR_EQ]
      )
      \\ rw []
      \\ gs [FLOOKUP_res_var, FLOOKUP_UPDATE, val_of_def, word_of_def]
      \\ simp [panSemTheory.state_component_equality]
      \\ irule_at Any EQ_REFL
      \\ simp [FUPDATE_EQ_FUPDATE_LIST, GSYM FUPDATE_LIST_APPEND]
      \\ simp [res_var_FUPDATE_LIST]
      \\ simp [GSYM FUPDATE_EQ_FUPDATE_LIST, FUPDATE_FUPDATE_LIST_MEM]
      \\ irule_at Any EQ_REFL
      \\ irule_at Any EQ_REFL
    )
    \\ gs [evaluate_def, eval_def, FLOOKUP_UPDATE]
    \\ qmatch_asmsub_abbrev_tac `evaluate (if (if C then _ else _) <> _ then _ else _, _)`
    \\ Cases_on `C` \\ fs [markerTheory.Abbrev_def]
    >- (
      gs [evaluate_def, eval_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def,
          is_valid_value_def, shape_of_def]
      \\ gvs []
      \\ first_x_assum (drule_then drule)
      \\ impl_tac
      >- (
        simp [FLOOKUP_res_var, FLOOKUP_UPDATE, val_of_def, word_of_def]
        \\ irule_at (Pat `0w < _`) WORD_LESS_LESS_EQ_TRANS
        \\ drule_then (irule_at Any) word_le_minus_one
        \\ simp []
        \\ irule word_minus_one_less
        \\ simp [WORD_LESS_IMP_LESS_OR_EQ]
        \\ first_assum (irule_at Any)
      )
      \\ rw []
      \\ gs [FLOOKUP_res_var, FLOOKUP_UPDATE, val_of_def, word_of_def]
      \\ simp [panSemTheory.state_component_equality]
      \\ rpt (irule_at Any EQ_REFL)
      \\ simp [FUPDATE_EQ_FUPDATE_LIST, GSYM FUPDATE_LIST_APPEND]
      \\ simp [res_var_FUPDATE_LIST]
      \\ simp [GSYM FUPDATE_EQ_FUPDATE_LIST, FUPDATE_FUPDATE_LIST_MEM]
      \\ irule_at Any EQ_REFL
    )
    (* swap case *)
    \\ gs [evaluate_def, eval_def, FLOOKUP_UPDATE,
            pan_op_def, wordLangTheory.word_op_def, flatten_def, mem_stores_def, mem_store_def,
            is_valid_value_def, shape_of_def]
    \\ gvs []
    \\ first_x_assum (drule_then drule)
    \\ impl_tac
    >- (
      DEP_REWRITE_TAC [last (RES_CANON EVERY_MEM)]
      \\ conj_tac
      >- (
        rw [APPLY_UPDATE_THM, word_of_def]
        \\ imp_res_tac EVERY_MEM
        \\ fs []
      )
      \\ metis_tac [word_plus_one_le, word_minus_one_less, WORD_LESS_LESS_EQ_TRANS,
              WORD_LESS_EQ_LESS_TRANS, WORD_LESS_IMP_LESS_OR_EQ,
              word_less_plus_one, word_le_minus_one]
    )
    \\ rw []
    \\ gs [FLOOKUP_res_var, FLOOKUP_UPDATE, val_of_def, word_of_def]
    \\ simp [panSemTheory.state_component_equality]
    \\ rpt (irule_at Any EQ_REFL)
    \\ simp [FUPDATE_EQ_FUPDATE_LIST, GSYM FUPDATE_LIST_APPEND]
    \\ simp [res_var_FUPDATE_LIST]
    \\ simp [GSYM FUPDATE_EQ_FUPDATE_LIST, FUPDATE_FUPDATE_LIST_MEM]
    \\ simp [FUPDATE_LIST_CANCEL]
    \\ irule_at Any EQ_REFL
    \\ qexists_tac `shuffle`
    \\ conj_tac
    >- (
      simp [FUN_EQ_THM, APPLY_UPDATE_LIST_ALOOKUP]
      \\ rw []
      \\ TOP_CASE_TAC \\ fs []
      \\ rw [APPLY_UPDATE_THM]
      \\ imp_res_tac PERM_LENGTH
      \\ fs [REVERSE_ZIP, ALOOKUP_ZIP_FAIL]
      \\ fs [MEM_MAP]
    )
    >- (
      drule_then irule PERM_TRANS
      \\ irule PERM_MAP_update_flip
      \\ simp [MEM_MAP]
      \\ REWRITE_TAC [Q.SPEC `_ * _` WORD_ADD_COMM]
      \\ simp []
      \\ rpt (irule_at Any EQ_REFL)
      \\ simp []

... more on array indices 

      \\ simp []
      \\ fs [] \\ ALOOKUP_ZIP_FAIL

print_match [] ``UPDATE _ _ _ =++ _``;
print_match [] ``UPDATE_LIST``;

      

      simp [EVERY_MEM, APPLY_UPDATE_THM]
      drule_then (irule_at Any) word_plus_one_le
    \\ simp [FLOOKUP_res_var, FLOOKUP_UPDATE, val_of_def, word_of_def]
    \\ rename [`evaluate (If _, dec_clock _) = (_, step_st)`]
    >- 


      \\ irule_at Any (last (RES_CANON PERM_CONS_IFF))
      \\ irule_at Any (last (RES_CANON PERM_APPEND_IFF))
      \\ qspecl_then [`y_v + 1w`, `x_v + 1w`] mp_tac (GEN_ALL w_count_drop1)
      \\ impl_tac
      >- (
        simp []
        \\ metis_tac [word_less_plus_one, WORD_LESS_IMP_LESS_OR_EQ]
      )
      \\ strip_tac \\ fs []
print_find "perm_app"

      \\ DEP_REWRITE_TAC [w_count_snoc |> Q.GEN `x` |> Q.SPEC `_ + _`]
      \\ simp []
      \\ fs [FLOOKUP_res_var, FLOOKUP_UPDATE]


print_match [] ``(_ |+ _) |++ _``;



    \\ CCONTR_TAC
    \\ pop_assum kall_tac

    \\ gs []


    \\ qspecl_then [`y_v + 1w`, `x_v + 1w`




    \\ fs [pan_op_def, wordLangTheory.word_op_def, flatten_def, mem_stores_def, mem_store_def]
    \\ fs [mem_load_def]

mem_load_def


    \\ fs [asmTheory.word_cmp_def]
    \\ drule_then assume_tac w_count_cons
    \\ gvs [is_valid_value_def, shape_of_def, word_of_def]
    \\ first_x_assum (drule_then drule)
    \\ simp [finite_mapTheory.FLOOKUP_UPDATE, word_of_def]
    \\ simp [empty_locals_def, miscTheory.UPDATE_LIST_THM]
    \\ rw [] \\ fs []
    \\ irule_at Any EQ_REFL
  )
QED

Theorem init_array_correct:
  st1.code = the_code ==>
  panSem$evaluate (Call NONE (Label «init_array») [Const base; Const len], st1) = (res, st2) /\
  (set (MAP (\i. base + (8w * i)) (w_count 0w len)) SUBSET st1.memaddrs) ==>
  res <> NONE /\
  (res <> SOME TimeOut ==> (case res of SOME (Return (ValWord i)) => i = 0w | _ => F) /\
  ?n. st2 = ((empty_locals st1) with <|
    memory := st1.memory =++ (MAP (\i. (base + (i * 8w), Word i)) (w_count 0w len));
    clock := st1.clock - n |>))
Proof
  simp [evaluate_def, eval_def, lookup_code_def,
        REWRITE_RULE [GSYM while_then_def] lookup_init_array]
  \\ simp [shape_of_def]
  \\ rpt disch_tac
  \\ fs [CaseEq "bool"]
  \\ fs [evaluate_def, eval_def]
  \\ pairarg_tac \\ fs []
  \\ dxrule (REWRITE_RULE [GSYM while_then_def] init_array_loop_correct)
  \\ simp [FLOOKUP_FUPDATE_LIST, FLOOKUP_UPDATE, word_of_def, dec_clock_def]
  \\ gvs [CaseEq "option", CaseEq "result"]
  \\ simp [empty_locals_def]
  \\ rw []
  \\ simp [panSemTheory.state_component_equality]
  \\ irule_at Any EQ_REFL
QED

val _ = export_theory ();
