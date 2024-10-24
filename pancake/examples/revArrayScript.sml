(*
  Proof of correctness of a simplified in-place quicksort program.
*)

open preamble HolKernel Parse boolLib bossLib stringLib numLib intLib
     panLangTheory panPtreeConversionTheory panSemTheory
     panHoareTheory panHoareLib;

val _ = new_theory "revArray";

val (ast, _) = parse_pancake_file "../examples/rev_array.pnk"

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

Theorem w_count_nil:
  x <=+ i
  ==>
  w_count i x = []
Proof
  simp [w_count_def, WORD_NOT_LOWER]
QED

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

Triviality word_minus_one_lower_self:
  x <> 0w ==>
  x + -1w <+ x
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x - 1w` mp_tac w2n_plus1
  \\ rw []
QED

Triviality word_plus_one_lower_self:
  x <> -1w ==>
  x <+ x + 1w
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ rw []
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

Theorem Q_EQ_helper:
  !Q s ls s' ls'. Q s ls /\ s = s' /\ ls = ls' ==> Q s' ls'
Proof
  metis_tac []
QED

Theorem FOLD_UPDATE_LIST:
  ((UPDATE x y m) =++ zs) = (m =++ ((x, y) :: zs))
Proof
  simp [UPDATE_LIST_THM]
QED

Theorem APPLY_UPDATE_LIST_IF_MEM:
  (m =++ xs) y = (if MEM y (MAP FST xs)
    then THE (ALOOKUP (REVERSE xs) y)
    else m y)
Proof
  simp [miscTheory.APPLY_UPDATE_LIST_ALOOKUP]
  \\ CASE_TAC
  \\ fs [alistTheory.ALOOKUP_NONE, MAP_REVERSE]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP]
  \\ rw []
  \\ fs []
QED


Theorem UPDATE_LIST_PERM_EQ:
  ALL_DISTINCT (MAP FST xs) ==>
  PERM xs ys ==>
  m =++ xs = m=++ ys
Proof
  cheat
QED

Theorem rev_array_hoare_correct:

  !Q.
  (!s ls. Q (SOME TimeOut) s ls) ==>
  hoare_logic G 
    (\s ls.
        the_code ⊑ s.code /\
        EVERY ((<>) NONE) (MAP (local_word s.locals) [«base_addr»; «len»]) /\
        let addrs = MAP (\i. tlw s «base_addr» + (i * 8w)) (w_count 0w (tlw s «len»)) in
        set addrs SUBSET s.memaddrs /\
        ALL_DISTINCT addrs /\
        EVERY (((<>) NONE) o word_of o s.memory) addrs /\
        (!locs clock. Q (SOME (Return (ValWord 0w)))
                (s with <| locals := locs; clock := clock;
                    memory := s.memory =++ ZIP (addrs, REVERSE (MAP s.memory addrs)) |>) ls)
    )
    (TailCall (Label «reverse») [Var «base_addr»; Var «len»])
    Q

Proof

  rw []
  \\ irule hoare_logic_rev_init
  \\ rpt rev_hoare_tac
  \\ qspec_then `the_code` irule hoare_logic_TailCall_rev_code
  \\ simp [lookups]
  \\ rpt rev_hoare_tac

  \\ qspec_then `\s ls.
    the_code ⊑ s.code /\
    EVERY ((<>) NONE) (MAP (local_word s.locals) [«base_addr»; «len»; «xt»; «yt»]) /\
    tlw s «yt» <+ tlw s «len» /\
    let addrs1 = MAP (\i. tlw s «base_addr» + (i * 8w)) (w_count 0w (tlw s «xt»));
        addrs2 = MAP (\i. tlw s «base_addr» + (i * 8w)) (w_count (tlw s «xt») (tlw s «yt» + 1w));
        addrs3 = MAP (\i. tlw s «base_addr» + (i * 8w)) (w_count (tlw s «yt» + 1w) (tlw s «len»))
    in
    set addrs2 SUBSET s.memaddrs /\
    EVERY (((<>) NONE) o word_of o s.memory) addrs2 /\
    ALL_DISTINCT (addrs1 ++ addrs2 ++ addrs3) /\
    (!locs clock. Q (SOME (Return (ValWord 0w)))
            (s with <| locals := locs; clock := clock;
                memory := s.memory =++ ZIP (addrs2, REVERSE (MAP s.memory addrs2)) |>) (DROP 2 ls))
    `
    (REWRITE_TAC o single) (GSYM annot_While_def)
  \\ rpt rev_hoare_tac
  \\ simp hoare_simp_rules

  \\ conj_tac
  >- (

    csimp ([logic_imp_def] @ hoare_simp_ex_rules)
    \\ rw []
    \\ ntac 3 (imp_res_tac neq_NONE_IMP \\ fs [])
    \\ gs [val_of_eq_SOME, word_of_eq_SOME]
    \\ name_flookup_tac
    \\ qspec_then `yt_v_1` mp_tac (GEN_ALL word_plus_one_lower_self)
    \\ impl_tac \\ rpt strip_tac \\ fs []
    \\ rw []
    >- (
      qspec_then `Q _` irule Q_EQ_helper
      \\ first_x_assum (irule_at Any)
      \\ simp [state_component_equality]
      \\ fs [CaseEq "bool", asmTheory.word_cmp_def, wordsTheory.WORD_NOT_LOWER]
      \\ fs [wordsTheory.WORD_LOWER_OR_EQ]
      \\ simp [w_count_nil, word_plus_one_lower, UPDATE_LIST_THM]
      \\ fs [w_count_cons, w_count_nil, UPDATE_LIST_THM]
    )
    \\ fs [CaseEq "bool", asmTheory.word_cmp_def, mem_load_def]
    \\ simp [pan_op_def, wordLangTheory.word_op_def, flatten_def, mem_stores_def, mem_store_def]

    \\ DISJ2_TAC
    \\ drule_then (drule_then assume_tac) wordsTheory.WORD_LOWER_TRANS
    \\ dxrule_then assume_tac w_count_snoc
    \\ gs []
    \\ drule_then assume_tac w_count_cons
    \\ gs []
    \\ imp_res_tac neq_NONE_IMP \\ fs []
    \\ gs [word_of_eq_SOME]
    \\ rw []
    >- (
      irule wordsTheory.WORD_LOWER_TRANS
      \\ irule_at Any word_minus_one_lower_self
      \\ simp []
      \\ CCONTR_TAC \\ fs []
    )
    >- (
      drule_at_then Any irule EVERY_MONOTONIC
      \\ rw [combinTheory.APPLY_UPDATE_THM]
    )
    >- (
      DEP_REWRITE_TAC [Q.GEN `x` w_count_snoc |> Q.SPEC `_ + 1w`]
      \\ simp [w_count_cons]
      \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
      \\ irule wordsTheory.WORD_LOWER_EQ_LOWER_TRANS
      \\ irule_at Any word_plus_one_lower_self
      \\ simp []
      \\ CCONTR_TAC \\ fs []
    )
    \\ qspec_then `Q _` irule Q_EQ_helper
    \\ first_x_assum (irule_at Any)
    \\ simp [state_component_equality]
    \\ simp [REVERSE_APPEND, GSYM ZIP_APPEND, UPDATE_LIST_THM]
    \\ simp [FUN_EQ_THM]
    \\ simp [APPLY_UPDATE_LIST_IF_MEM, MAP_ZIP, REVERSE_APPEND]
    \\ strip_tac
    \\ rw [] \\ gs [ALL_DISTINCT_APPEND]
    >- (
      AP_TERM_TAC
      \\ AP_THM_TAC
      \\ AP_TERM_TAC
      \\ AP_TERM_TAC
      \\ AP_TERM_TAC
      \\ simp []
      \\ irule MAP_CONG
      \\ rw [APPLY_UPDATE_THM]
      \\ gs []
    )
    \\ rw [APPLY_UPDATE_THM]
  )
  \\ rpt rev_hoare_tac
  \\ csimp ([logic_imp_def] @ hoare_simp_ex_rules)
  \\ rw []
  \\ ntac 3 (imp_res_tac neq_NONE_IMP \\ fs [])
  \\ gs [val_of_eq_SOME, word_of_eq_SOME]
  \\ name_flookup_tac
  \\ simp ([asmTheory.word_cmp_def] @ hoare_simp_rules)
  \\ DISJ2_TAC
  \\ rw []
  >- (
    fs [CaseEq "bool"]
    \\ qspec_then `Q _` irule Q_EQ_helper
    \\ first_x_assum (irule_at Any)
    \\ simp [state_component_equality]
    \\ drule wordsTheory.WORD_LOWER_CASES_IMP
    \\ simp []
    \\ Cases_on `len_v_1 = 1w`
    >- (
      simp [w_count_cons, WORD_LO, w_count_nil]
      \\ simp [w_count_nil, UPDATE_LIST_THM]
    )
    \\ simp []
    \\ rw []
    \\ drule word_minus_one_lower
    \\ simp [w_count_nil, UPDATE_LIST_THM]
  )
  \\ fs []
  \\ simp [pan_op_def, wordLangTheory.word_op_def, flatten_def, mem_stores_def, mem_store_def]
  \\ simp [w_count_nil]
  \\ irule word_minus_one_lower_self
  \\ CCONTR_TAC \\ fs []
QED

val _ = export_theory ();
