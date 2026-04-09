(* Example of proving the correctness of reversing an array. *)
        
Theory revArray
Ancestors
  itreeTau panLang panSem
  pan_itreeSem pan_itreeProps
  panItreeAbsSem
  panPtreeConversion
  alignment wordLang ffi misc
Libs
  preamble stringSyntax numSyntax
  stringLib sumSyntax
  HolKernel boolLib bossLib
  listSyntax mlstringLib optionSyntax
  simpLib panItreeDecompilerLib



val _ = set_trace "notify type variable guesses" 0;


(* Extension of itreeTauTheory *)
val _ = monadsyntax.enable_monadsyntax();
val _ = declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
                      ignorebind = NONE,
                      choice = NONE,
                      fail = NONE,
                      guard = NONE});
val _ = enable_monad "itree";

(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;


                                                   
fun read_file fname = let
    val s = TextIO.openIn fname
    fun get ss = case TextIO.inputLine s of
        SOME str => get (str :: ss)
      | NONE => rev ss
  in concat (get []) end


(** Copied from panPtreeConversion *)
fun parse_pancake_code word_ty str =
  let
    val parse_topdecs_to_ast_s = inst [alpha |-> word_ty] “parse_topdecs_to_ast”
    val thm = EVAL (mk_comb (parse_topdecs_to_ast_s, stringLib.fromMLstring str))
    val r = rhs (concl thm)
  in
    if sumSyntax.is_inl r
    then (fst (sumSyntax.dest_inl r), thm)
    else failwith ("parse_pancake_code: failed to EVAL")
  end


fun parse_pancake_file word_ty fname =
  parse_pancake_code word_ty (read_file fname)

                     

val (rev_array_topdecs, _) = parse_pancake_file “:64” "revArray.pnk"

val rev_array_fundecs = topdecs_to_fundecs rev_array_topdecs

val rev_array_result = decompile_2_reduce "revArray" [] rev_array_fundecs

val reverse_while = List.nth (fst rev_array_result, 0) |> (fn (x,y,z) => hd y) |> reduce_to_view []
    
Theorem LET_same_CONJ:
  (LET f v ∧ LET g v) = LET (λx. f x ∧ g x) v
Proof
  rw[]
QED

Theorem LET_capture:
  LET (λx. f v) v = LET (λx. f x) v
Proof
  rw[]
QED
        
Theorem itree_bind_resp_wbisim_compose_intro:
  t ≈ t' ⇒ (∀r. k r ≈ k' r) ⇒ t'' = t' >>= k' ⇒ t >>= k ≈ t''
Proof
  rw[]
  \\ irule itree_bind_resp_wbisim
  \\ gvs[]
QED



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

Theorem word_plus_one_lower:
  x <+ y ==> x + 1w <=+ y
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ rw []
QED

Theorem word_minus_one_lower:
  x <+ y ==> x <=+ y - 1w
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `y - 1w` mp_tac (GSYM w2n_plus1)
  \\ rw []
QED

Theorem word_minus_one_lower_self:
  x <> 0w ==>
  x + -1w <+ x
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x - 1w` mp_tac w2n_plus1
  \\ rw []
QED

Theorem word_plus_one_lower_self:
  x <> -1w ==>
  x <+ x + 1w
Proof
  simp [WORD_LO, GSYM WORD_NOT_LOWER]
  \\ qspec_then `x` mp_tac w2n_plus1
  \\ rw []
QED

Theorem w_count_empty:
  w_count x y = [] ⇒ ¬(x <+ y)
Proof
  rpt strip_tac
  \\ gvs[w_count_def, GENLIST_EQ_NIL]
  \\ last_x_assum $ assume_tac o PURE_REWRITE_RULE[WORD_SUB_INTRO, WORD_MULT_CLAUSES, WORD_EQ_SUB_ZERO]
  \\ gvs[]
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

Theorem PERM_MAP_update_flip:
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

Theorem NOT_NONE_EQ_EX = IS_SOME_EQ_NOT_NONE |> GSYM |> REWRITE_RULE [IS_SOME_EXISTS]

Theorem case_opt_f = TypeBase.case_pred_imp_of ``: 'a option``
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


Theorem FOLD_UPDATE_LIST_ONCE:
  m⦇x ↦ y⦈ = m =++ [(x,y)]
Proof
  qsuff_tac ‘m⦇x ↦ y⦈ =++ [] = m =++ ((x,y)::[])’
  >- rw[UPDATE_LIST_THM]
  \\ rw[FOLD_UPDATE_LIST]
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

Theorem UPDATE_LIST_APPEND:
  fm =++ (kvl1 ++ kvl2) = fm =++ kvl1 =++ kvl2
Proof
  qid_spec_tac ‘fm’
  \\ Induct_on ‘kvl1’
  \\ rw[UPDATE_LIST_THM]
QED
        
Theorem UPDATE_UPDATE_LIST_COMMUTES:
  ¬MEM k (MAP FST kvl) ⇒ fm⦇k ↦ v⦈ =++ kvl = (fm =++ kvl)⦇k ↦ v⦈
Proof
let open rich_listTheory in
Q.ID_SPEC_TAC `kvl` THEN
HO_MATCH_MP_TAC SNOC_INDUCT THEN
SRW_TAC [][UPDATE_LIST_THM] THEN
FULL_SIMP_TAC (srw_ss()) [UPDATE_LIST_THM,MAP_SNOC,SNOC_APPEND,UPDATE_LIST_APPEND] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [UPDATE_COMMUTES]
end
QED


Theorem UPDATE_LIST_ALL_DISTINCT_PERM:
  ∀ls ls' fm.
    ALL_DISTINCT (MAP FST ls) ∧ PERM ls ls' ⇒ fm =++ ls = fm =++ ls'
Proof
  Induct >> rw[] >>
  fs[sortingTheory.PERM_CONS_EQ_APPEND] >>
  rw[UPDATE_LIST_THM] >>
  PairCases_on`h` >> fs[] >>
  imp_res_tac UPDATE_UPDATE_LIST_COMMUTES >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `(fm =++ (M ++ N))⦇h0 ↦ h1⦈` >>
  conj_tac
  >- metis_tac[sortingTheory.ALL_DISTINCT_PERM,sortingTheory.PERM_MAP] >>
  rw[UPDATE_LIST_APPEND] >>
  `h0 NOTIN set (MAP FST N)`
  by metis_tac[sortingTheory.PERM_MEM_EQ,MEM_MAP,MEM_APPEND] >>
  imp_res_tac UPDATE_UPDATE_LIST_COMMUTES >>
  rw[UPDATE_LIST_THM]
QED


Theorem MEM_w_count_le:
  ∀i x y.
    MEM i (w_count x y) ⇔ x <=+ i ∧ i <+ y
Proof
  Induct_on ‘w_count x y’ \\ rw[]
  >- (gvs[w_count_def]
      \\ FULL_CASE_TAC \\ gvs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
      >- (Cases_on ‘i <₊ x’ \\ gvs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
          \\ drule_all_then assume_tac WORD_LOWER_EQ_TRANS
          \\ gvs[]
         )
      \\ gvs[GENLIST_EQ_NIL, WORD_SUM_ZERO]
     )
  \\ reverse $ Cases_on ‘x <₊ y’ \\ gvs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
  >- (drule_then assume_tac w_count_nil
      \\ gvs[]
     )
  \\ drule_then assume_tac w_count_cons
  \\ gvs[]
  \\ last_x_assum $ qspecl_then [‘h + 1w’, ‘y’] assume_tac \\ gvs[]
  \\ Cases_on ‘i = h’ \\ gvs[]
  \\ iff_tac \\ rw[]
  >- (irule WORD_LOWER_EQ_TRANS
      \\ first_assum $ irule_at (Pos last)
      \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
      \\ irule word_plus_one_lower_self
      \\ CCONTR_TAC \\ gvs[]
     )
  \\ qpat_x_assum ‘_ <=+ _’ $ assume_tac o SRULE[WORD_LOWER_OR_EQ]
  \\ gvs[]
  \\ irule word_plus_one_lower
  \\ pop_assum $ irule_at Any
QED


Theorem w_count_append:
  ∀i x y.
    x <=+ i ∧ i <=+ y ⇒ w_count x y = w_count x i ++ w_count i y
Proof
  Induct_on ‘w_count x i’ \\ rw[]
  >- (gvs[w_count_def]
      \\ FULL_CASE_TAC \\ gvs[GENLIST_EQ_NIL, WORD_NOT_LOWER]
      >- (‘y <=+ i’ suffices_by rw[]
          \\ irule WORD_LOWER_EQ_TRANS
          \\ pop_assum $ irule_at Any
          \\ rw[]
         )
      \\ FULL_CASE_TAC \\ gvs[GENLIST_EQ_NIL, WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
      >- (FULL_CASE_TAC \\ gvs[GENLIST_EQ_NIL, WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
          >- (imp_res_tac WORD_LOWER_EQUAL_ANTISYM
              \\ rw[]
             )
          \\ imp_res_tac WORD_LOWER_EQUAL_ANTISYM
          \\ rw[]
         )
      \\ FULL_CASE_TAC \\ gvs[GENLIST_EQ_NIL, WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
      >- (imp_res_tac WORD_LOWER_EQUAL_ANTISYM
          \\ rw[]
         )
      \\ gvs[WORD_SUM_ZERO]
     )
  \\ reverse $ Cases_on ‘x <₊ i’ \\ gvs[WORD_NOT_LOWER, WORD_NOT_LOWER_EQUAL]
  >- (drule_then assume_tac w_count_nil
      \\ gvs[]
     )
  \\ drule_then assume_tac w_count_cons
  \\ gvs[]
  \\ last_x_assum $ qspecl_then [‘h + 1w’, ‘i’] assume_tac \\ gvs[]
  \\ pop_assum $ qspec_then ‘y’ assume_tac \\ gvs[]
  \\ drule_then assume_tac word_plus_one_lower
  \\ gvs[]
  \\ subgoal ‘h <+ y’
  >- (irule WORD_LOWER_LOWER_EQ_TRANS
      \\ first_assum $ irule_at Any
      \\ rw[]
     )
  \\ drule_then assume_tac w_count_cons
  \\ gvs[]
QED

Theorem list_biind:
  ∀P. P [] ∧ (∀x. P [x]) ∧ (∀t. P t ⇒ ∀h x. P (h::(t ++ [x]))) ⇒ ∀l. P l
Proof
  rpt strip_tac
  \\ measureInduct_on ‘LENGTH l’
  \\ Cases_on ‘l’ \\ rw[]
  \\ Cases_on ‘t’ using SNOC_CASES \\ rw[SNOC_APPEND]
QED

        
        
Theorem reverse_while_correctness:
  ∀xt yt s.
    MAP (\i. base_addr + (i * 8w)) (w_count xt (yt + 1w)) = addrs ∧
    yt ≠ -1w ∧
    set addrs ⊆ s.memaddrs ∧
    ALL_DISTINCT addrs ∧
    FLOOKUP s.locals «base_addr» = SOME (ValWord base_addr) ∧
    FLOOKUP s.locals «xt» = SOME (ValWord xt) ∧
    FLOOKUP s.locals «yt» = SOME (ValWord yt) ∧
    xt <=+ yt + 1w ⇒
    ∃new_xt new_yt.
      let
        addrs1 = MAP (\i. base_addr + (i * 8w)) (w_count xt new_xt);
        addrs2 = MAP (\i. base_addr + (i * 8w)) (w_count new_xt (new_yt + 1w));
        addrs3 = MAP (\i. base_addr + (i * 8w)) (w_count (new_yt + 1w) (yt + 1w));
        s' = s with <| locals := s.locals |++ [(«xt», ValWord new_xt);(«yt», ValWord new_yt)];
                       memory := s.memory =++ ZIP (addrs1 ++ addrs3, REVERSE (MAP s.memory addrs3) ++ REVERSE (MAP s.memory addrs1))|>
      in
        reverse_while_2 s ≈ Ret (INR (NONE,s')) ∧
        xt <=+ new_xt ∧ new_xt <=+ yt + 1w ∧ xt <=+ new_yt + 1w ∧
        new_yt <=+ yt ∧ new_xt <=+ new_yt + 1w ∧ new_yt <=+ new_xt ∧
        LENGTH addrs1 = LENGTH addrs3
Proof
  Induct_on ‘addrs’ using list_biind
  \\ rpt strip_tac
  >- (gvs[]
      \\ irule_at (Pos hd) itree_wbisim_trans
      \\ irule_at (Pos hd) $ cj 1 reverse_while
      \\ gvs[word_of_val_def, UPDATE_LIST_THM, MAP_EQ_NIL, Once itree_wbisim_cases]
      \\ drule_then assume_tac w_count_empty
      \\ gvs[WORD_NOT_LOWER]
      \\ subgoal ‘yt <=+ xt’
      >- (irule_at Any WORD_LOWER_EQ_TRANS
          \\ pop_assum $ irule_at (Pos last)
          \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
          \\ irule word_plus_one_lower_self
          \\ gvs[]
         )
      \\ gvs[bstate_component_equality]
      \\ irule_at (Pos hd) FUPDATE_LIST_UNCHANGED
      \\ gvs[w_count_def, UPDATE_LIST_THM]
      \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
      \\ irule WORD_LOWER_EQ_LOWER_TRANS
      \\ irule_at Any word_plus_one_lower_self
      \\ gvs[]
     )
  >- (gvs[MAP_EQ_SING, w_count_def]
      \\ Cases_on ‘¬(xt <₊ yt + 1w)’ \\ gvs[]
      \\ subgoal ‘LENGTH (GENLIST (λj. xt + n2w j) (w2n (-1w * xt + yt + 1w))) = 1’
      >- (last_assum (fn x => PURE_REWRITE_TAC[x])
          \\ rw[]
         )
      \\ gvs[]
      \\ ‘(n2w:num -> word64) (w2n (-1w * i + yt + 1w)) = n2w 1’ by rw[]
      \\ pop_assum $ assume_tac o PURE_REWRITE_RULE[n2w_w2n, WORD_SUB_INTRO]
      \\ gvs[]
      \\ pop_assum $ assume_tac o PURE_REWRITE_RULE[n2w_w2n, WORD_SUB_INTRO, WORD_MULT_CLAUSES, WORD_EQ_SUB_ZERO]
      \\ gvs[]
      \\ irule_at (Pos hd) itree_wbisim_trans
      \\ irule_at (Pos hd) $ cj 1 reverse_while
      \\ gvs[word_of_val_def, w_count_def, UPDATE_LIST_THM, mem_stores_def,
             mem_store_def, flatten_def, Once itree_wbisim_cases, bstate_component_equality]
      \\ irule_at Any FUPDATE_LIST_UNCHANGED
      \\ gvs[UPDATE_LIST_THM]
      \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
      \\ gvs[]
     )
  \\ gvs[]
  \\ irule_at (Pos hd) itree_wbisim_trans
  \\ irule_at (Pos hd) $ cj 2 reverse_while
  \\ gvs[word_of_val_def, UPDATE_LIST_THM, mem_stores_def, mem_store_def, flatten_def]
  \\ subgoal ‘xt <+ yt’
  >- (last_x_assum $ kall_tac
      \\ gvs[w_count_def]
      \\ Cases_on ‘¬(xt <₊ yt + 1w)’ \\ gvs[]
      \\ drule_then assume_tac word_minus_one_lower
      \\ gvs[WORD_LOWER_OR_EQ]
     )
  \\ gvs[]
  \\ subgoal ‘xt <+ yt + 1w’
  >- (last_x_assum $ kall_tac
      \\ gvs[w_count_def]
      \\ Cases_on ‘¬(xt <₊ yt + 1w)’ \\ gvs[]
     )
  \\ drule_then assume_tac w_count_cons
  \\ gvs[]
  \\ subgoal ‘xt + 1w <+ yt + 1w’
  >- (last_x_assum $ kall_tac
      \\ gvs[w_count_def]
      \\ Cases_on ‘¬(xt + 1w <₊ yt + 1w)’ \\ gvs[]
     )
  \\ drule_then assume_tac w_count_snoc
  \\ gvs[]
  \\ last_x_assum $ qspecl_then [‘xt + 1w’, ‘yt + -1w’, ‘s with
             <|locals :=
                 res_var_list
                   s.locals⟨
                     «yt» ↦ ValWord (yt + -1w); «xt» ↦ ValWord (xt + 1w);
                     «yv» ↦ Val (s.memory (base_addr + 8w * yt));
                     «xv» ↦ Val (s.memory (base_addr + 8w * xt))
                   ⟩
                   [(«yv»,FLOOKUP s.locals «yv»);
                    («xv»,FLOOKUP s.locals «xv»)];
               memory :=
                 s.memory⦇
                   base_addr + 8w * yt ↦ s.memory (base_addr + 8w * xt);
                   base_addr + 8w * xt ↦ s.memory (base_addr + 8w * yt)
                 ⦈|>’] assume_tac
  \\ gvs[word_of_val_def, UPDATE_LIST_THM, mem_stores_def, mem_store_def, flatten_def, ALL_DISTINCT_APPEND,
         res_var_list_def, panPropsTheory.FLOOKUP_pan_res_var_thm, FLOOKUP_SIMP]
  \\ qmatch_asmsub_abbrev_tac ‘prog_asm ⇒ _’
  \\ subgoal ‘prog_asm’
  >- (unabbrev_all_tac
      \\ conj_tac
      >- (‘0w <+ yt’ suffices_by rw[WORD_LOWER_NOT_EQ]
          \\ irule WORD_LOWER_EQ_LOWER_TRANS
          \\ metis_tac[WORD_0_LS]
         )
      \\ pop_assum $ kall_tac
      \\ irule word_plus_one_lower
      \\ gvs[]
     )
  \\ gvs[]
  \\ irule_at Any itree_wbisim_trans
  \\ first_x_assum $ irule_at (Pos hd)
  \\ gvs[Once itree_wbisim_cases, bstate_component_equality, FUPDATE_EQ_FUPDATE_LIST, GSYM FUPDATE_LIST_APPEND,
         res_var_list_def, res_var_FUPDATE_LIST]
  \\ ‘s.locals |++
          [(«xt»,ValWord (xt + 1w)); («yt»,ValWord (yt + -1w));
           («xt»,ValWord (new_xt));
           («yt»,ValWord (new_yt))] =
          s.locals |++
           [(«xt»,ValWord (xt + 1w)); («yt»,ValWord (yt + -1w))] |++
           [(«xt»,ValWord (new_xt));
            («yt»,ValWord(new_yt))]’ by rw[GSYM FUPDATE_LIST_APPEND]
  \\ pop_assum (fn x => PURE_REWRITE_TAC[x])
  \\ irule_at Any EQ_SYM
  \\ irule_at Any FUPDATE_LIST_CANCEL
  \\ gvs[]
  \\ reverse $ conj_asm2_tac
  >- (conj_tac
      >- (irule WORD_LOWER_EQ_TRANS
          \\ last_assum $ irule_at (Pos last)
          \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
          \\ irule word_plus_one_lower_self
          \\ CCONTR_TAC \\ gvs[]
         )
      \\ conj_tac
      >- (irule WORD_LOWER_EQ_TRANS
          \\ last_assum $ irule_at (Pos hd)
          \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
          \\ irule word_plus_one_lower_self
          \\ CCONTR_TAC \\ gvs[]
         )
      \\ conj_tac
      >- (irule WORD_LOWER_EQ_TRANS
          \\ last_assum $ irule_at (Pos last)
          \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
          \\ irule word_plus_one_lower_self
          \\ CCONTR_TAC \\ gvs[]
         )
      \\ conj_tac
      >- (irule WORD_LOWER_EQ_TRANS
          \\ last_assum $ irule_at (Pos hd)
          \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
          \\ irule word_minus_one_lower_self
          \\ gvs[]
         )
      \\ DEP_ONCE_REWRITE_TAC[w_count_cons]
      \\ irule_at (Pos hd) WORD_LOWER_LOWER_EQ_TRANS
      \\ irule_at (Pos hd) word_plus_one_lower_self
      \\ gvs[]
      \\ conj_tac
      >- (CCONTR_TAC \\ gvs[]
         )
      \\ irule EQ_SYM
      \\ DEP_ONCE_REWRITE_TAC[w_count_snoc]
      \\ irule_at (Pos hd) WORD_LOWER_EQ_LOWER_TRANS
      \\ qexists ‘yt’
      \\ irule_at Any word_plus_one_lower_self
      \\ gvs[]
      \\ qpat_x_assum ‘_ ≤₊ _ + -1w’ $ assume_tac o SRULE[WORD_LOWER_OR_EQ]
      \\ gvs[]
      \\ drule_then assume_tac word_plus_one_lower
      \\ irule WORD_LOWER_EQ_TRANS
      \\ pop_assum $ irule_at Any
      \\ irule WORD_LOWER_IMP_LOWER_OR_EQ
      \\ irule word_minus_one_lower_self
      \\ gvs[]
     )
  \\ gvs[]
  \\ subgoal ‘xt <+ new_xt’
  >- (irule WORD_LOWER_LOWER_EQ_TRANS
      \\ last_assum $ irule_at (Pos last)
      \\ irule word_plus_one_lower_self
      \\ CCONTR_TAC \\ gvs[]
     )
  \\ dxrule_then assume_tac w_count_cons
  \\ subgoal ‘new_yt + 1w <+ yt + 1w’
  >- (irule WORD_LOWER_EQ_LOWER_TRANS
      \\ irule_at Any word_plus_one_lower_self
      \\ gvs[]
      \\ irule word_plus_one_lower
      \\ qpat_x_assum ‘new_yt ≤₊ yt + -1w’ $ assume_tac o SRULE[WORD_LOWER_OR_EQ]
      \\ gvs[]
      >- (irule WORD_LOWER_TRANS
          \\ pop_assum $ irule_at Any
          \\ irule word_minus_one_lower_self
          \\ gvs[]
         )
      \\ irule word_minus_one_lower_self
      \\ gvs[]
     )
  \\ dxrule_then assume_tac w_count_snoc
  \\ gvs[REVERSE_APPEND]
  \\ gvs[GSYM SNOC_APPEND]
  \\ DEP_REWRITE_TAC[ZIP_SNOC]
  \\ gvs[LENGTH_REVERSE]
  \\ gvs[SNOC_APPEND]
  \\ gvs[FOLD_UPDATE_LIST, FOLD_UPDATE_LIST_ONCE]
  \\ gvs[SNOC_APPEND]
  \\ subgoal ‘REVERSE
                (MAP
                   (s.memory =++
                    [(base_addr + 8w * xt,s.memory (base_addr + 8w * yt));
                     (base_addr + 8w * yt,s.memory (base_addr + 8w * xt))])
                   (MAP (λi. base_addr + 8w * i) (w_count (new_yt + 1w) yt))) =
              REVERSE
              (MAP s.memory
                   (MAP (λi. base_addr + 8w * i) (w_count (new_yt + 1w) yt)))’
  >- (rw[MAP_COMPOSE, o_DEF, MAP_EQ_f, APPLY_UPDATE_LIST_IF_MEM]
      \\ subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) (new_yt + 1w) ++ w_count (new_yt + 1w) yt’
      >- (irule w_count_append
          \\ rw[]
          \\ irule word_plus_one_lower
          \\ irule WORD_LOWER_EQ_LOWER_TRANS
          \\ last_assum $ irule_at (Pos last)
          \\ irule word_minus_one_lower_self
          \\ rw[]
         )
      \\ gvs[]
      \\ FULL_CASE_TAC \\ gvs[]
      \\ FULL_CASE_TAC \\ gvs[]
     )
  \\ rw[FOLD_UPDATE_LIST, FOLD_UPDATE_LIST_ONCE]
  \\ subgoal ‘REVERSE
                (MAP
                   (s.memory =++
                    [(base_addr + 8w * xt,s.memory (base_addr + 8w * yt));
                     (base_addr + 8w * yt,s.memory (base_addr + 8w * xt))])
                   (MAP (λi. base_addr + 8w * i) (w_count (xt + 1w) new_xt))) =
              REVERSE
              (MAP s.memory
                   (MAP (λi. base_addr + 8w * i) (w_count (xt + 1w) new_xt)))’
  >- (rw[MAP_COMPOSE, o_DEF, MAP_EQ_f, APPLY_UPDATE_LIST_IF_MEM]
      \\ subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) new_xt ++ w_count new_xt yt’
      >- (irule w_count_append
          \\ rw[]
         )
      \\ FULL_CASE_TAC \\ gvs[]
      \\ FULL_CASE_TAC \\ gvs[]
     )
  \\ rw[FOLD_UPDATE_LIST, FOLD_UPDATE_LIST_ONCE]
  \\ PURE_REWRITE_TAC[GSYM MAP_APPEND, GSYM REVERSE_APPEND]
  \\ DEP_REWRITE_TAC[REWRITE_RULE [SNOC_APPEND] ZIP_SNOC]
  \\ irule UPDATE_LIST_ALL_DISTINCT_PERM
  \\ gvs[]
  \\ rw[]
  >- (DEP_REWRITE_TAC[cj 1 MAP_ZIP]
      \\ gvs[LENGTH_MAP, LENGTH_REVERSE]
      \\ conj_tac
      >- (subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) new_xt ++ w_count new_xt yt’
          >- (irule w_count_append
              \\ rw[]
             )
          \\ gvs[]
         )
      \\ subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) (new_yt + 1w) ++ w_count (new_yt + 1w) yt’
      >- (irule w_count_append
          \\ rw[]
          \\ irule word_plus_one_lower
          \\ irule WORD_LOWER_EQ_LOWER_TRANS
          \\ last_assum $ irule_at (Pos last)
          \\ irule word_minus_one_lower_self
          \\ rw[]
         )
      \\ gvs[]
     )
  >- (rw[ALL_DISTINCT_APPEND]
      >- (DEP_REWRITE_TAC[cj 1 MAP_ZIP]
          \\ gvs[LENGTH_MAP, LENGTH_REVERSE, ALL_DISTINCT_APPEND]
          \\ conj_tac
          >- (subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) new_xt ++ w_count new_xt yt’
              >- (irule w_count_append
                  \\ rw[]
                 )
              \\ gvs[ALL_DISTINCT_APPEND]
             )
          \\ conj_tac
          >- (subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) (new_yt + 1w) ++ w_count (new_yt + 1w) yt’
              >- (irule w_count_append
                  \\ rw[]
                  \\ irule word_plus_one_lower
                  \\ irule WORD_LOWER_EQ_LOWER_TRANS
                  \\ last_assum $ irule_at (Pos last)
                  \\ irule word_minus_one_lower_self
                  \\ rw[]
                 )
              \\ gvs[ALL_DISTINCT_APPEND]
             )
          \\ subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) new_xt ++ w_count new_xt yt’
          >- (irule w_count_append
              \\ rw[]
             )
          \\ subgoal ‘w_count new_xt yt = w_count new_xt (new_yt + 1w) ++ w_count (new_yt + 1w) yt’
          >- (irule w_count_append
              \\ rw[]
              \\ irule word_plus_one_lower
              \\ irule WORD_LOWER_EQ_LOWER_TRANS
              \\ last_assum $ irule_at (Pos last)
              \\ irule word_minus_one_lower_self
              \\ rw[]
             )
          \\ gvs[ALL_DISTINCT_APPEND]
         )
      \\ DEP_REWRITE_TAC[cj 1 MAP_ZIP]
      \\ gvs[LENGTH_MAP, LENGTH_REVERSE, ALL_DISTINCT_APPEND]
      \\ conj_tac
      >- (subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) new_xt ++ w_count new_xt yt’
          >- (irule w_count_append
              \\ rw[]
             )
          \\ gvs[ALL_DISTINCT_APPEND]
         )
      \\ subgoal ‘w_count (xt + 1w) yt = w_count (xt + 1w) (new_yt + 1w) ++ w_count (new_yt + 1w) yt’
      >- (irule w_count_append
          \\ rw[]
          \\ irule word_plus_one_lower
          \\ irule WORD_LOWER_EQ_LOWER_TRANS
          \\ last_assum $ irule_at (Pos last)
          \\ irule word_minus_one_lower_self
          \\ rw[]
         )
      \\ gvs[ALL_DISTINCT_APPEND]
     )
  \\ irule PERM_TRANS
  \\ irule_at Any PERM_APPEND
  \\ gvs[]
QED


val reverse_shallow = List.nth (fst rev_array_result, 0) |> (fn (x,y,z) => x)

        
Theorem reverse_correctness:
  ∀s.
    MAP (\i. base_addr + (i * 8w)) (w_count 0w len) = addrs ∧
    set addrs ⊆ s.memaddrs ∧
    ALL_DISTINCT addrs ⇒
    reverse_body [ValWord base_addr; ValWord len] s ≈
                 let
                   s' = if len <=+ 1w then s with locals := FEMPTY
                       else s with <| locals := FEMPTY;
                                      memory := s.memory =++ ZIP (addrs, REVERSE (MAP s.memory addrs))|>
                 in
                   Ret (INR (SOME (Return (ValWord 0w)),s'))
Proof
  rpt strip_tac
  \\ irule itree_wbisim_trans
  \\ irule_at (Pos hd) reverse_shallow
  \\ gvs[WORD_NOT_LOWER]
  \\ FULL_CASE_TAC \\ gvs[itree_wbisim_refl]
  \\ assume_tac $ GEN_ALL reverse_while_correctness
  \\ pop_assum $ qspecl_then [‘base_addr’, ‘MAP (λi. base_addr + 8w * i) (w_count 0w len)’,
                              ‘0w’, ‘len + -1w’, ‘s with locals := FEMPTY⟨«yt» ↦ ValWord (len + -1w); «xt» ↦ ValWord 0w;
                                                  «len» ↦ ValWord len; «base_addr» ↦ ValWord base_addr⟩’] assume_tac
  \\ gvs[word_of_val_def, UPDATE_LIST_THM, res_var_list_def, panPropsTheory.FLOOKUP_pan_res_var_thm, FLOOKUP_SIMP, WORD_NOT_LOWER_EQUAL]
  \\ ‘len ≠ 0w’ by (CCONTR_TAC \\ gvs[])
  \\ gvs[]
  \\ irule itree_wbisim_trans
  \\ irule_at (Pos hd) itree_bind_resp_wbisim_compose_intro
  \\ first_x_assum $ irule_at (Pos hd)
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’]
  \\ rw[Once itree_wbisim_cases, bstate_component_equality]
  \\ Cases_on ‘new_xt = new_yt + 1w’
  >- (gvs[]
      \\ subgoal ‘w_count 0w len = w_count 0w (new_yt + 1w) ++ w_count (new_yt + 1w) len’
      >- (irule w_count_append
          \\ rw[]
         )
      \\ gvs[ALL_DISTINCT_APPEND, REVERSE_APPEND]
     )
  \\ subgoal ‘new_xt = new_yt’
  >- (irule WORD_LOWER_EQUAL_ANTISYM
      \\ first_assum $ irule_at Any
      \\ qpat_x_assum ‘_ <=+ _ + 1w’ $ assume_tac o SRULE[WORD_LOWER_OR_EQ]
      \\ gvs[]
      \\ drule_then assume_tac word_minus_one_lower
      \\ gvs[]
     )
  \\ gvs[]
  \\ subgoal ‘w_count 0w len = w_count 0w new_xt ++ w_count new_xt len’
  >- (irule w_count_append
      \\ rw[]
     )
  \\ gvs[]
  \\ subgoal ‘w_count new_xt len = w_count new_xt (new_xt + 1w) ++ w_count (new_xt + 1w) len’
  >- (irule w_count_append
      \\ rw[]
      \\ irule word_plus_one_lower
      \\ qpat_x_assum ‘_ <=+ _ + -1w’ $ assume_tac o SRULE[WORD_LOWER_OR_EQ]
      \\ gvs[]
      >- (irule WORD_LOWER_TRANS
          \\ pop_assum $ irule_at (Pos hd)
          \\ irule word_minus_one_lower_self
          \\ rw[]
         )
      \\ irule word_minus_one_lower_self
      \\ rw[]
     )
  \\ gvs[]
  \\ subgoal ‘w_count new_xt (new_xt + 1w) = [new_xt]’
  >- (DEP_ONCE_REWRITE_TAC[w_count_cons]
      \\ conj_tac
      >- (qpat_x_assum ‘_ <=+ _ + 1w’ $ assume_tac o SRULE[WORD_LOWER_OR_EQ]
          \\ gvs[]
         )
      \\ rw[LIST_SING_EQ]
      \\ irule w_count_nil
      \\ rw[]
     )
  \\ gvs[ALL_DISTINCT_APPEND, REVERSE_APPEND]
  \\ ‘s.memory (base_addr + 8w * new_xt)::
             REVERSE
               (MAP s.memory
                    (MAP (λi. base_addr + 8w * i) (w_count 0w new_xt))) =
      [s.memory (base_addr + 8w * new_xt)] ++
             REVERSE
               (MAP s.memory
                  (MAP (λi. base_addr + 8w * i) (w_count 0w new_xt)))’ by rw[]
  \\ pop_assum (fn x => PURE_REWRITE_TAC[x, APPEND_ASSOC])
  \\ DEP_REWRITE_TAC[GSYM ZIP_APPEND]
  \\ gvs[LENGTH_REVERSE, LENGTH_APPEND]
  \\ rw[UPDATE_LIST_APPEND, GSYM FOLD_UPDATE_LIST_ONCE]
  \\ DEP_REWRITE_TAC[GSYM UPDATE_UPDATE_LIST_COMMUTES]
  \\ conj_tac
  >- rw[MAP_ZIP]
  \\ ‘s.memory⦇base_addr + 8w * new_xt ↦ s.memory (base_addr + 8w * new_xt)⦈ = s.memory’ by rw[]
  \\ pop_assum (fn x => PURE_REWRITE_TAC[x])
  \\ gvs[]
QED


      
val reverse_twice_shallow = List.nth (fst rev_array_result, 1) |> (fn (x,y,z) => x)



Theorem MEM_ZIP_IMP:
  MEM x (ZIP (ys, zs)) ==>
  MEM (FST x) ys /\ MEM (SND x) zs
Proof
  rw []
  \\ imp_res_tac MEM_ZIP2
  \\ fs [EL_MEM]
QED
        
    
Theorem update_list_reverse_reverse:
  ALL_DISTINCT l ⇒ m =++ ZIP (l, REVERSE (MAP (m =++ ZIP (l, REVERSE (MAP m l))) l)) = m
Proof
  qid_spec_tac ‘m’
  \\ Induct_on ‘l’ using list_biind
  \\ rw[UPDATE_LIST_THM]
  \\ gvs[ZIP, REVERSE_APPEND]
  \\ DEP_REWRITE_TAC[GSYM ZIP_APPEND]
  \\ gvs[LENGTH_MAP, LENGTH_REVERSE]
  \\ gvs[UPDATE_LIST_THM]
  \\ DEP_REWRITE_TAC[UPDATE_UPDATE_LIST_COMMUTES]
  \\ gvs[MAP_ZIP, ALL_DISTINCT_APPEND]
  \\ subgoal ‘(m =++ (ZIP (l,REVERSE (MAP m l)) ++ [(x,m h)]))⦇h ↦ m x⦈ x = m h’
  >- (rw[APPLY_UPDATE_LIST_IF_MEM, APPLY_UPDATE_THM]
      \\ DEP_REWRITE_TAC[alookup_distinct_reverse]
      \\ gvs[MAP_ZIP, ALL_DISTINCT_APPEND]
      \\ rw[ALOOKUP_APPEND]
      \\ FULL_CASE_TAC \\ gvs[]
      \\ drule_then assume_tac ALOOKUP_MEM
      \\ drule_then assume_tac MEM_ZIP_IMP
      \\ gvs[]
     )
  \\ rw[UPDATE_LIST_APPEND, GSYM FOLD_UPDATE_LIST_ONCE]
  \\ subgoal ‘MAP (m =++ ZIP (l,REVERSE (MAP m l)))⦇h ↦ m x; x ↦ m h⦈ l = MAP (m =++ ZIP (l,REVERSE (MAP m l))) l’
  >- (rw[MAP_EQ_f, APPLY_UPDATE_THM]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  \\ gvs[]
  \\ rw[FUN_EQ_THM, APPLY_UPDATE_THM]
QED


Theorem UPDATE_LIST_CANCEL:
  ∀ls1 fm ls2.
    (∀k. MEM k (MAP FST ls1) ⇒ MEM k (MAP FST ls2)) ⇒
    fm =++ ls1 =++ ls2 = fm =++ ls2
Proof
  Induct_on ‘ls1’
  \\ rw[UPDATE_LIST_THM, FUN_EQ_THM, APPLY_UPDATE_LIST_ALOOKUP]
  \\ FULL_CASE_TAC \\ gvs[]
  \\ FULL_CASE_TAC \\ gvs[ALOOKUP_NONE]
  \\ imp_res_tac ALOOKUP_MEM
  \\ gvs[]
  >- (subgoal ‘MEM (FST (x,x')) (MAP FST ls1)’
      >- (irule MEM_MAP_f
          \\ gvs[]
         )
      \\ gvs[MAP_REVERSE, MEM_REVERSE]
     )
  \\ first_x_assum $ qspec_then ‘x’ assume_tac \\ gvs[MAP_REVERSE, MEM_REVERSE]
QED

Theorem reverse_twice_correctness:
  ∀s.
    s.code = rev_array_codes ∧
    MAP (\i. base_addr + (i * 8w)) (w_count 0w len) = addrs ∧
    set addrs ⊆ s.memaddrs ∧
    ALL_DISTINCT addrs ⇒
    reverse_twice_body [ValWord base_addr; ValWord len] s ≈ Ret (INR (SOME (Return (ValWord 0w)),s with locals := FEMPTY))
Proof
  rpt strip_tac
  \\ irule itree_wbisim_trans
  \\ irule_at (Pos hd) reverse_twice_shallow
  \\ assume_tac $ GEN_ALL reverse_correctness
  \\ pop_assum $ qspecl_then [‘len’, ‘base_addr’, ‘addrs’,
                              ‘s with locals :=
                               FEMPTY⟨«len» ↦ ValWord len; «base_addr» ↦ ValWord base_addr⟩’] assume_tac
  \\ gvs[]
  \\ conj_tac
  >- (irule ret_satisfy_impl_bind_impl
      \\ dxrule_then assume_tac ret_satisfy_wbisim_biim
      \\ gvs[ret_satisfy_Ret]
      \\ irule_at (Pos last) EQ_REFL
      \\ rw[itree_call_handler_def]
      >- (FULL_CASE_TAC \\ gvs[ret_satisfy_Ret, FLOOKUP_SIMP]
         )
      \\ FULL_CASE_TAC \\ gvs[ret_satisfy_Ret, FLOOKUP_SIMP]
     )
  \\ irule itree_wbisim_trans
  \\ rw[itree_bind_assoc]
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’]
  \\ rw[Once itree_call_handler_def, word_of_val_def, FLOOKUP_SIMP, set_var_defs, shape_of_def, itree_bind_assoc]
  >- (assume_tac $ GEN_ALL reverse_correctness
      \\ pop_assum $ qspecl_then [‘len’, ‘base_addr’, ‘MAP (λi. base_addr + 8w * i) (w_count 0w len)’,
                                  ‘s with locals :=
                                   FEMPTY⟨«len» ↦ ValWord len; «base_addr» ↦ ValWord base_addr⟩’] assume_tac
      \\ gvs[]
      \\ irule itree_wbisim_trans
      \\ rw[itree_bind_assoc]
      \\ irule_at Any itree_bind_resp_wbisim_compose_intro
      \\ last_x_assum $ irule_at Any
      \\ irule_at Any EQ_REFL
      \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
      \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’]
      \\ rw[Once itree_call_handler_def, word_of_val_def, FLOOKUP_SIMP, set_var_defs,
            shape_of_def, itree_bind_assoc, itree_wbisim_refl]
     )
  \\ assume_tac $ GEN_ALL reverse_correctness
  \\ pop_assum $ qspecl_then [‘len’, ‘base_addr’, ‘MAP (λi. base_addr + 8w * i) (w_count 0w len)’,
                              ‘s with
                               <|locals :=
                                 FEMPTY⟨«len» ↦ ValWord len; «base_addr» ↦ ValWord base_addr⟩;
                                 memory :=
                                 s.memory =++
                                  ZIP
                                  (MAP (λi. base_addr + 8w * i) (w_count 0w len),
                                   REVERSE
                                   (MAP s.memory
                                        (MAP (λi. base_addr + 8w * i) (w_count 0w len))))|>’] assume_tac
  \\ gvs[]
  \\ irule itree_wbisim_trans
  \\ rw[itree_bind_assoc]
  \\ irule_at Any itree_bind_resp_wbisim_compose_intro
  \\ last_x_assum $ irule_at Any
  \\ irule_at Any EQ_REFL
  \\ qmatch_goalsub_abbrev_tac ‘k _ ≈ _ _’
  \\ qexists ‘k’ \\ gvs[itree_wbisim_refl, Abbr ‘k’]
  \\ rw[Once itree_call_handler_def, word_of_val_def, FLOOKUP_SIMP, set_var_defs,
        shape_of_def, itree_bind_assoc]
  \\ rw[Once itree_wbisim_cases, bstate_component_equality]
  \\ DEP_ONCE_REWRITE_TAC[UPDATE_LIST_CANCEL]
  \\ gvs[MAP_ZIP]
  \\ irule $ GSYM update_list_reverse_reverse
  \\ gvs[]
QED

             
