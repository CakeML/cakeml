(*
  Proof of correctness of a simplified in-place quicksort program.
*)

open preamble HolKernel Parse boolLib bossLib stringLib numLib intLib
     panLangTheory panPtreeConversionTheory panSemTheory
     panHoareTheory panHoareLib;

val _ = new_theory "quickSort";

val (ast, _) = parse_pancake_file "../examples/quick_sort.pnk"

val ast_funs = listSyntax.dest_list ast |> fst
  |> map (hd o pairSyntax.strip_pair)

Definition the_code_def:
  the_code = FEMPTY |++ (MAP (I ## SND) (^ast))
End

val lookups = LIST_CONJ (map (fn nm => EVAL ``FLOOKUP the_code ^nm``) ast_funs)

Definition w_count_def:
  w_count i x = (if ~ (i <+ x) then []
    else GENLIST (\j. i + n2w j) (w2n (x - i)))
End

Triviality word_plus_one_lower:
  x <+ y ==> x + 1w <=+ y
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ rw []
QED

Triviality word_minus_one_lower:
  x <+ y ==> x <=+ y - 1w
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ rw []
  \\ cheat
QED

Theorem w_count_cons:
  i <+ x ==> w_count i x = i :: w_count (i + 1w) x
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
    fs [WORD_NOT_LOWER]
    \\ drule_then mp_tac WORD_LOWER_EQUAL_ANTISYM
    \\ simp [word_plus_one_lower]
  )
QED

Theorem w_count_snoc:
  i <+ x ==> w_count i x = w_count i (x - 1w) ++ [x - 1w]
Proof
  simp [w_count_def]
  \\ disch_tac
  \\ DEP_ONCE_REWRITE_TAC [GSYM wordsTheory.SUC_WORD_PRED]
  \\ simp [listTheory.GENLIST]
  \\ rw []
  >- (
    strip_tac
    \\ full_simp_tac bool_ss [wordsTheory.WORD_SUB_INTRO]
    \\ fs [wordsTheory.WORD_EQ_SUB_ZERO]
  )
  >- (
    drule word_minus_one_lower
    \\ fs [WORD_NOT_LOWER]
    \\ rw []
    \\ imp_res_tac WORD_LOWER_EQUAL_ANTISYM
    \\ fs [] \\ gvs []
    \\ full_simp_tac bool_ss [wordsTheory.WORD_SUB_INTRO, wordsTheory.WORD_MULT_CLAUSES,
            wordsTheory.WORD_SUB_SUB]
    \\ simp []
  )
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

Theorem UPDATE_LIST_UNCHANGED:
  EVERY (\(x, y). f x = y) xs ==>
  f =++ xs = f
Proof
  Induct_on `xs` \\ simp [UPDATE_LIST_THM]
  \\ simp [FORALL_PROD, combinTheory.UPDATE_APPLY_IMP_ID]
QED

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


Theorem partition_hoare_correct:

  !Q.
  (!s ls. Q (SOME TimeOut) s ls) ==>
  hoare_logic G 
    (\s ls.
        the_code ⊑ s.code /\
        EVERY ((<>) NONE) (MAP (local_word s.locals) [«base_addr»; «piv»; «x»; «y»]) /\
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
    (TailCall (Label «partition») [Var «base_addr»; Var «piv»; Var «x»; Var «y»])
    Q




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
