(*
  Correctness proof for word_simp
*)
open alistTheory preamble wordLangTheory wordSemTheory wordPropsTheory word_simpTheory;

val _ = new_theory "word_simpProof";

val s = ``s:('a,'c,'ffi) wordSem$state``

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_simp"];

(** common **)

val labels_rel_def = Define `
  labels_rel old_labs new_labs <=>
    (ALL_DISTINCT old_labs ==> ALL_DISTINCT new_labs) /\
    set new_labs SUBSET set old_labs`;

Theorem labels_rel_refl[simp]:
   !xs. labels_rel xs xs
Proof
  fs [labels_rel_def]
QED

Theorem labels_rel_APPEND:
   labels_rel xs xs1 /\ labels_rel ys ys1 ==>
   labels_rel (xs++ys) (xs1++ys1)
Proof
  fs [labels_rel_def,ALL_DISTINCT_APPEND,SUBSET_DEF] \\ metis_tac []
QED

Theorem PERM_IMP_labels_rel:
   PERM xs ys ==> labels_rel ys xs
Proof
  fs [labels_rel_def] \\ rw [] \\ fs [SUBSET_DEF]
  \\ metis_tac [ALL_DISTINCT_PERM,MEM_PERM]
QED

val labels_rel_TRANS = Q.prove(
  `labels_rel xs ys /\ labels_rel ys zs ==> labels_rel xs zs`,
  fs [labels_rel_def] \\ rw [] \\ fs [SUBSET_DEF]);

(** verification of Seq_assoc **)

Theorem evaluate_SmartSeq:
   evaluate (SmartSeq p1 p2,s) = evaluate (Seq p1 p2,^s)
Proof
  rw [SmartSeq_def,evaluate_def]
QED

Theorem evaluate_Seq_Skip:
   !p1 s. evaluate (Seq p1 Skip,s) = evaluate (p1,^s)
Proof
  Induct \\ fs [evaluate_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs [])
QED

Theorem evaluate_Skip_Seq:
   evaluate (Seq Skip p,s) = evaluate (p,^s)
Proof
  fs [evaluate_def]
QED

Theorem evaluate_Seq_assoc_lemma:
   !p1 p2 s. evaluate (Seq_assoc p1 p2,s) = evaluate (Seq p1 p2,^s)
Proof
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [evaluate_SmartSeq,Seq_assoc_def,evaluate_Seq_Skip,evaluate_def]
  \\ (rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs []))
  \\ Cases_on `get_vars args s1` \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ret_prog` \\ fs []
  \\ Cases_on `handler` \\ fs []
  \\ fs [add_ret_loc_def]
  \\ PairCases_on `x'` \\ fs[add_ret_loc_def]
  \\ PairCases_on `x''` \\ fs[add_ret_loc_def,push_env_def]
QED

Theorem evaluate_Seq_assoc:
   !p s. evaluate (Seq_assoc Skip p,s) = evaluate (p,^s)
Proof
  fs [evaluate_Seq_assoc_lemma,evaluate_def]
QED

Theorem extract_labels_SmartSeq:
   extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)
Proof
  rw [SmartSeq_def,extract_labels_def]
QED

Theorem extract_labels_Seq_assoc_lemma:
   !p1 p2. extract_labels (Seq_assoc p1 p2) =
            extract_labels p1 ++ extract_labels p2
Proof
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_def,extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `ret_prog` \\ Cases_on `handler` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ PairCases_on `x'` \\ fs []
QED

Theorem extract_labels_Seq_assoc:
   extract_labels (Seq_assoc Skip p) = extract_labels p
Proof
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]
QED

(** verification of simp_if **)

Theorem dest_If_Eq_Imm_thm:
   dest_If_Eq_Imm x2 = SOME (n,w,p1,p2) <=>
    x2 = If Equal n (Imm w) p1 p2
Proof
  Cases_on `x2` \\ fs [dest_If_Eq_Imm_def,dest_If_def]
  \\ every_case_tac \\ fs []
QED

Theorem dest_If_thm:
   dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5
Proof
  Cases_on `x2` \\ fs [dest_If_def]
QED

Theorem dest_Seq_IMP:
   dest_Seq p1 = (x1,x2) ==> evaluate (p1,s) = evaluate (Seq x1 x2,^s)
Proof
  Cases_on `p1` \\ fs [SmartSeq_def,dest_Seq_def]
  \\ rw [] \\ fs [evaluate_Skip_Seq]
QED

Theorem dest_Seq_Assign_Const_IMP:
   dest_Seq_Assign_Const v p = SOME (q,w) ==>
    evaluate (p,s) = evaluate (Seq q (Assign v (Const w)),^s)
Proof
  fs [dest_Seq_Assign_Const_def] \\ pairarg_tac \\ fs []
  \\ Cases_on `p2` \\ fs [] \\ Cases_on `e` \\ fs []
  \\ rw [] \\ imp_res_tac dest_Seq_IMP \\ fs []
QED

Theorem evaluate_apply_if_opt:
   apply_if_opt p1 p2 = SOME x ==>
    evaluate (Seq p1 p2,s) = evaluate (x,^s)
Proof
  fs [apply_if_opt_def]
  \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs []
  \\ fs [dest_If_Eq_Imm_thm] \\ strip_tac \\ rveq
  \\ fs [evaluate_SmartSeq]
  \\ imp_res_tac dest_Seq_IMP \\ fs []
  \\ fs [dest_If_thm]
  \\ fs [evaluate_def]
  \\ Cases_on `evaluate (x0,s)` \\ fs []
  \\ rename1 `evaluate (x0,s) = (res1,s1)` \\ fs []
  \\ Cases_on `res1` \\ fs []
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ fs [])
  \\ fs [get_var_imm_def]
  \\ imp_res_tac dest_Seq_Assign_Const_IMP \\ fs []
  \\ rename1 `dest_Seq_Assign_Const v1 t1 = SOME (t1a,w1)`
  \\ qpat_x_assum `dest_Seq_Assign_Const v1 t1 = SOME (t1a,w1)` mp_tac
  \\ rename1 `dest_Seq_Assign_Const v2 t2 = SOME (t2a,w2)`
  \\ qpat_x_assum `dest_Seq_Assign_Const v2 t2 = SOME (t2a,w2)` mp_tac
  \\ rw [] \\ rpt (qpat_x_assum `!x._` kall_tac)
  \\ fs [evaluate_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs [] \\ fs []
  \\ Cases_on `res' = NONE` \\ fs [word_exp_def] \\ rveq
  \\ fs [get_var_def,set_var_def,asmTheory.word_cmp_def]
QED

Theorem evaluate_simp_if:
   !p s. evaluate (simp_if p,s) = evaluate (p,^s)
Proof
  HO_MATCH_MP_TAC simp_if_ind \\ fs [simp_if_def,evaluate_def] \\ rw []
  THEN1
   (CASE_TAC \\ fs [evaluate_def]
    \\ imp_res_tac evaluate_apply_if_opt \\ fs []
    \\ pop_assum (fn th => once_rewrite_tac [GSYM th])
    \\ fs [evaluate_def])
  \\ Cases_on `get_vars args s` \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ret_prog` \\ fs []
  \\ Cases_on `handler` \\ fs [] \\ fs [add_ret_loc_def]
  \\ PairCases_on `x'` \\ fs[add_ret_loc_def,push_env_def]
  \\ TRY (PairCases_on `x''`) \\ fs[add_ret_loc_def,push_env_def]
QED

(*
Theorem simp_if_works:
   IS_SOME (apply_if_opt
     (If Less 5 (Imm 5w) (Assign 3 (Const 5w)) (Assign 3 (Const (4w:word32))))
     (If Equal 3 (Imm (4w:word32)) (Raise 1) (Raise 2)))
Proof
  EVAL_TAC
QED *)

Theorem extract_labels_apply_if_opt:
   apply_if_opt p1 p2 = SOME p ==>
    PERM (extract_labels p) (extract_labels p1 ++ extract_labels p2)
Proof
  fs [apply_if_opt_def]
  \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [dest_If_thm,dest_If_Eq_Imm_thm] \\ rveq
  \\ fs [extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `p1` \\ fs [dest_Seq_def] \\ rveq \\ fs [extract_labels_def]
  \\ metis_tac[PERM_APPEND,APPEND_ASSOC,PERM_APPEND_IFF]
QED

Theorem extract_labels_simp_if:
   !p. PERM (extract_labels (simp_if p)) (extract_labels p)
Proof
  HO_MATCH_MP_TAC simp_if_ind \\ fs [simp_if_def] \\ rw []
  \\ fs [extract_labels_def]
  \\ every_case_tac \\ fs [extract_labels_def]
  \\ imp_res_tac extract_labels_apply_if_opt
  \\ metis_tac[PERM_APPEND,PERM_TRANS,PERM_APPEND_IFF]
QED

(** verification of const_fp **)

(* gc *)

val is_gc_word_const_def = Define `
  is_gc_word_const (Loc _ _) = T /\
  is_gc_word_const (Word w) = is_gc_const w`;

val gc_fun_const_ok_def = Define `
  gc_fun_const_ok (f:'a gc_fun_type) =
    !x y. f x = SOME y ==> EVERY2 (\a b. is_gc_word_const a ==> b = a) (FST x) (FST y)`;

val sf_gc_consts_def = Define `
  sf_gc_consts (StackFrame sv h) (StackFrame sw h') =
  (EVERY2 (\(ak, av) (bk, bv). (ak = bk) /\ (is_gc_word_const av ==> bv = av)) sv sw /\ h = h')`;

Theorem sf_gc_consts_refl:
   !x. sf_gc_consts x x
Proof
  Cases_on `x` \\ rw [sf_gc_consts_def] \\ irule EVERY2_refl \\ Cases_on `x` \\ rw []
QED

Theorem sf_gc_consts_trans:
   !a b c. sf_gc_consts a b /\ sf_gc_consts b c ==>
           sf_gc_consts a c
Proof
  Cases_on `a` \\ Cases_on `b` \\ Cases_on `c` \\ rw [sf_gc_consts_def] \\
  irule EVERY2_trans
    \\ conj_tac >- (Cases_on `x` \\ Cases_on `y` \\ Cases_on `z` \\ fs [])
    >- (asm_exists_tac \\ rw [])
QED

(* Assign *)

Theorem strip_const_thm:
   !xs x s. strip_const xs = SOME x ==> MAP (\a. word_exp s a) xs = MAP (SOME o Word) x
Proof
  Induct \\ TRY (Cases_on `h`) \\ fs [strip_const_def, word_exp_def] \\ CASE_TAC \\ fs []
QED

Theorem the_words_thm:
   !x. the_words (MAP (SOME o Word) x) = SOME x
Proof
  Induct \\ rw [the_words_def]
QED

Theorem const_fp_exp_word_exp:
   !e cs s. (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) ==>
            word_exp s (const_fp_exp e cs) = word_exp s e
Proof
  ho_match_mp_tac const_fp_exp_ind \\ rw [const_fp_exp_def]
  >-
  (CASE_TAC \\ rw [word_exp_def] \\ fs [get_var_def])
  >-
  (CASE_TAC \\ rw [word_exp_def] \\
  `(MAP (\a. word_exp s a) (MAP (\a. const_fp_exp a cs) args)) =
   (MAP (\a. word_exp s a) args)` by (fs [] \\ fs [MAP_MAP_o, MAP_EQ_f]) \\ fs [] \\
  `MAP (\a. word_exp s a) args = MAP (SOME o Word) x` by metis_tac [strip_const_thm] \\
  fs [the_words_thm] \\ CASE_TAC \\ fs [word_exp_def] \\
  rw [MAP_MAP_o, o_DEF, word_exp_def, SIMP_RULE std_ss [o_DEF] the_words_thm])
  >-
  (CASE_TAC \\ CASE_TAC \\ rw [word_exp_def] \\ every_case_tac \\
  res_tac \\ qpat_x_assum `_ = word_exp s e` (assume_tac o GSYM) \\ fs [word_exp_def])
QED

Theorem const_fp_exp_word_exp_const:
   !e cs s c. (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) /\
              const_fp_exp e cs = Const c ==>
              word_exp s e = SOME (Word c)
Proof
  ho_match_mp_tac const_fp_exp_ind \\ rw [const_fp_exp_def]

  >- (* Var *)
  (every_case_tac \\ rw [word_exp_def] \\ fs [get_var_def])

  >- (* Op *)
  (every_case_tac \\ rw [word_exp_def] \\
  `(MAP (\a. word_exp s a) args) =
   (MAP (\a. word_exp s a) (MAP (\a. const_fp_exp a cs) args))`
  by (fs [MAP_MAP_o, MAP_EQ_f, const_fp_exp_word_exp]) \\
  asm_rewrite_tac [] \\ imp_res_tac strip_const_thm \\
  last_x_assum (qspec_then `s` assume_tac) \\ asm_rewrite_tac [] \\
  rw [the_words_thm])

  >- (* Shift *)
  (every_case_tac \\ rw [word_exp_def] \\ res_tac \\
  qpat_x_assum `!c. _` (qspec_then `c'` assume_tac) \\ fs [])

  >- (* Others *)
  (rw [word_exp_def])
QED

(* Move *)

Theorem set_vars_move_NONE:
   !moves x s s' v.
   set_vars (MAP FST moves) x s = s' /\
   ALOOKUP moves v = NONE ==>
   get_var v s' = get_var v s
Proof
  Induct \\ Induct_on `x` \\ fs [set_vars_def, get_var_def, alist_insert_def] \\ rw [] \\
  Cases_on `h'` \\ rw [] \\
  Cases_on `q = v`\\ fs [] \\
  rw [lookup_insert] \\ first_assum match_mp_tac \\ fs []
QED

Theorem set_vars_move_SOME:
   !moves x v w s s'.
   set_vars (MAP FST moves) x s = s' /\
   get_vars (MAP SND moves) s = SOME x /\
   ALOOKUP moves v = SOME w ==>
   get_var v s' = get_var w s
Proof
  Induct \\ rw [] \\ Cases_on `h` \\
  fs [get_var_def, get_vars_def, set_vars_def] \\
  every_case_tac \\ fs [] \\ rw [alist_insert_def, lookup_insert]
QED

Theorem get_var_move_thm:
   !s s' moves x v.
   get_vars (MAP SND moves) s = SOME x /\
   set_vars (MAP FST moves) x s = s' ==>
   get_var v s' = case ALOOKUP moves v of
     | SOME w => get_var w s
     | NONE => get_var v s
Proof
  rw [] \\ CASE_TAC \\ metis_tac [set_vars_move_SOME, set_vars_move_NONE]
QED

Theorem lookup_const_fp_move_cs_NONE:
   !moves v cs cs'.
   ALOOKUP moves v = NONE /\
   lookup v cs = lookup v cs' ==>
   lookup v (const_fp_move_cs moves cs cs') = lookup v cs'
Proof
  Induct \\ rw [const_fp_move_cs_def] \\ fs [] \\
  qsuff_tac `ALOOKUP moves v = NONE`
    >-
    (Cases_on `h` \\ rw [] \\ `q <> v` by (fs [ALOOKUP_def]) \\ every_case_tac \\ rw []
      >-
      (qsuff_tac `lookup v cs = lookup v (delete q cs')` \\ rw [lookup_delete])
      >-
      (qsuff_tac `lookup v cs = lookup v (insert q x cs')` \\ rw [lookup_insert]))

    >-
    (Cases_on `h` \\ fs [] \\ Cases_on `q = v` \\ fs [])
QED

Theorem lookup_const_fp_move_cs_SOME_part:
   !moves q cs cs' x.
   ¬MEM q (MAP FST moves) /\
   lookup q cs' = x ==>
   lookup q (const_fp_move_cs moves cs cs') = x
Proof
  Induct \\ rw [const_fp_move_cs_def] \\ CASE_TAC \\ rw [lookup_delete, lookup_insert]
QED

(* TODO: In need of cleanup *)
Theorem lookup_const_fp_move_cs_SOME:
   !moves v w cs cs'.
   ALOOKUP moves v = SOME w /\
   ALL_DISTINCT (MAP FST moves) /\
   lookup v cs = lookup v cs' ==>
   lookup v (const_fp_move_cs moves cs cs') = lookup w cs
Proof
  Induct
    >-
    (rw [ALOOKUP_def])

    >-
    (rw [const_fp_move_cs_def] \\ Cases_on `h` \\ Cases_on `v = q`
      >-
      (fs [ALOOKUP_def] \\ every_case_tac \\ rw [] \\
      match_mp_tac lookup_const_fp_move_cs_SOME_part \\
      rw [lookup_delete, lookup_insert])

      >-
      (every_case_tac \\ rw []
        >-
        (`lookup v cs = lookup v (delete q cs')` by (rw [lookup_delete]) \\
        fs [ALOOKUP_def])

        >-
        (`lookup v cs = lookup v (insert q x cs')` by (rw [lookup_insert]) \\
        fs [])))
QED

Theorem lookup_const_fp_move_cs:
   !v moves cs.
   ALL_DISTINCT (MAP FST moves) ==>
   lookup v (const_fp_move_cs moves cs cs) = case ALOOKUP moves v of
     | SOME w => lookup w cs
     | NONE => lookup v cs
Proof
  rw [] \\ CASE_TAC \\ metis_tac [lookup_const_fp_move_cs_SOME,
                                  lookup_const_fp_move_cs_NONE]
QED

(* If *)

Theorem get_var_imm_cs_imp_get_var_imm:
   !x y s cs. (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) /\
              get_var_imm_cs x cs = SOME y ==>
              get_var_imm x s = SOME (Word y)
Proof
  rw [] \\ Cases_on `x` \\ fs [get_var_imm_cs_def, get_var_imm_def]
QED

(* Helpful lemmas about locals *)

Theorem get_var_set_var_thm:
   !k1 k2 v s. get_var k1 (set_var k2 v s) =
               if k1 = k2 then SOME v else get_var k1 s
Proof
  rw [get_var_def, set_var_def, lookup_insert]
QED

Theorem get_var_set_store_thm:
   !v w x s. get_var v (set_store w x s) = get_var v s
Proof
  rw [get_var_def, set_store_def]
QED

Theorem get_var_mem_store_thm:
   !v addr x s. mem_store addr x s = SOME s' ==>
                get_var v s' = get_var v s
Proof
  rw [mem_store_def] \\ rw [get_var_def]
QED

Theorem cs_delete_if_set:
   !x v1 v2 s cs w.
   (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) /\
  lookup v2 (delete v1 cs) = SOME w ==>
  get_var v2 (set_var v1 x s) = SOME (Word w)
Proof
  rw [get_var_set_var_thm] \\ fs [lookup_delete]
QED

Theorem cs_delete_if_set_x2:
   !x1 x2 v1 v2 v3 s cs w.
   (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) /\
  lookup v3 (delete v2 (delete v1 cs)) = SOME w ==>
  get_var v3 (set_var v2 x2 (set_var v1 x1 s)) = SOME (Word w)
Proof
  rw [] \\ irule cs_delete_if_set \\ metis_tac [cs_delete_if_set]
QED

(* Lookup thms *)

Theorem lookup_inter_eq_some:
   !m1 m2 k x. lookup k (inter_eq m1 m2) = SOME x ==>
               lookup k m1 = SOME x /\ lookup k m2 = SOME x
Proof
  rw [lookup_inter_eq] \\ every_case_tac \\ fs []
QED

Theorem lookup_filter_v_SOME:
   !t k v f. lookup k (filter_v f t) = SOME v ==> f v
Proof
  rewrite_tac [lookup_filter_v] \\ rpt gen_tac \\ TOP_CASE_TAC \\ rw [] \\ rw []
QED

Theorem lookup_filter_v_SOME_imp:
   !t k v f. lookup k (filter_v f t) = SOME v ==>
             lookup k t = SOME v
Proof
  rewrite_tac [lookup_filter_v] \\ rpt gen_tac \\ TOP_CASE_TAC \\ rw []
QED

(* LIST_REL/EVERY2 thms *)

Theorem LIST_REL_prefix:
   !R l1 l2 l1' l2'. LIST_REL R (l1 ++ l2) (l1' ++ l2') /\
                     LENGTH l1 = LENGTH l1' ==>
                     LIST_REL R l1 l1'
Proof
  Induct_on `l1` \\ Cases_on `l1'` \\ fs [] \\ rw [] \\ first_assum irule \\ rw [] \\ metis_tac []
QED

Theorem LIST_REL_append_left:
   !l0 l1 l2 R.
   LIST_REL R (l0 ++ l1) l2 ==>
   LIST_REL R l0 (TAKE (LENGTH l0) l2) /\
   LIST_REL R l1 (DROP (LENGTH l0) l2)
Proof
  rpt gen_tac \\ DISCH_TAC \\ imp_res_tac LIST_REL_LENGTH \\ irule LIST_REL_APPEND_IMP \\ fs []
QED

(* Stack thms *)

Theorem push_env_set_store_stack:
   !x1 x2 x3 x4 s. (push_env x1 x2 (set_store x3 x4 s)).stack = (push_env x1 x2 s).stack
Proof
  Cases_on `x2` \\ TRY (PairCases_on `x`) \\ rw [push_env_def, set_store_def] \\ pairarg_tac \\ fs []
QED

Theorem push_env_stack_gc:
   !s ls h. (push_env ls h s).gc_fun = s.gc_fun
Proof
  Cases_on `h` \\ TRY (PairCases_on `x`) \\
  rw [push_env_def, env_to_list_def]
QED

Theorem pop_env_stack_gc:
   !s. pop_env s = SOME s' ==> s'.gc_fun = s.gc_fun
Proof
  rw [pop_env_def] \\ every_case_tac \\ fs [] \\ rw []
QED

Theorem ALOOKUP_LIST_REL_sf_gc_consts:
   !l1 l2 k v.
   LIST_REL (\(ak, av) (bk, bv). ak = bk /\ (is_gc_word_const av ==> bv = av)) l1 l2 /\
   is_gc_word_const v /\
   ALOOKUP l1 k = SOME v ==>
   ALOOKUP l2 k = SOME v
Proof
  Induct_on `l2`
    >- (rpt gen_tac \\ rpt strip_tac \\ fs [] \\ rveq \\ fs [ALOOKUP_def]) \\
  rw [] \\ Cases_on `h` \\ Cases_on `x` \\ fs [ALOOKUP_def] \\ rveq \\ TOP_CASE_TAC \\ fs [] \\
  first_assum irule \\ rw [] \\ asm_exists_tac \\ rw []
QED

Theorem ALL_DISTINCT_PERM_FST:
   !l. ALL_DISTINCT (MAP FST l) /\ PERM l (f l) ==> ALL_DISTINCT (MAP FST (f l))
Proof
  rw [] \\
  `PERM (MAP FST l) (MAP FST (f l))` by (rw [PERM_MAP]) \\
  drule ALL_DISTINCT_PERM \\
  rw []
QED

Theorem ALOOKUP_LIST_REL_value_rel:
   !f l' l k v. LIST_REL (\(ak, av) (bk, bv). (ak = bk) /\ (f av ==> bv = av)) l' l /\
                ALOOKUP l' k = SOME v /\
                f v ==>
                ALOOKUP l k = SOME v
Proof
  Induct_on `l` \\ Cases_on `l'` \\ rw [] \\
  Cases_on `h'` \\ Cases_on `h` \\ fs [] \\ rw [] \\ fs [] \\ res_tac
QED

Theorem ALOOKUP_ALL_DISTINCT_FST_PERM:
   !l1 l2. ALL_DISTINCT (MAP FST l1) /\ PERM l1 l2 ==> ALOOKUP l1 = ALOOKUP l2
Proof
  rw [] \\ irule ALOOKUP_ALL_DISTINCT_PERM_same \\ rw [PERM_LIST_TO_SET, PERM_MAP]
QED

Theorem ALOOKUP_ALL_DISTINCT_FST_PERM_SOME:
   !l1 f k v. ALL_DISTINCT (MAP FST l1) /\
              PERM l1 (f l1) /\
              ALOOKUP l1 k = SOME v ==>
              ALOOKUP (f l1) k = SOME v
Proof
  metis_tac [ALOOKUP_ALL_DISTINCT_FST_PERM]
QED

Theorem push_env_gc_fun:
   !s x h. (push_env x h s).gc_fun = s.gc_fun
Proof
  Cases_on `h` \\ fs [] \\ TRY (PairCases_on `x`) \\ rw [push_env_def, env_to_list_def]
QED

Theorem pop_env_gc_fun:
   !s s'. pop_env s = SOME s' ==> s'.gc_fun = s.gc_fun
Proof
  rw [pop_env_def] \\ every_case_tac \\ fs [] \\ rw []
QED

Theorem pop_env_gc_fun_const_ok:
   !s s'. pop_env s = SOME s' /\ gc_fun_const_ok s.gc_fun ==>
          gc_fun_const_ok s'.gc_fun
Proof
  metis_tac [pop_env_gc_fun]
QED

(*Theorem call_env_push_env_dec_clock:
   !s s'. s' = (call_env x0 (push_env x1 x2 (dec_clock s))) ==> s'.gc_fun = s.gc_fun
Proof
  rw [dec_clock_def, call_env_def] \\ metis_tac [push_env_gc_fun]
QED*)

Theorem evaluate_gc_fun_const_ok:
   !p s res s'. evaluate (p, s) = (res, s') /\ gc_fun_const_ok s.gc_fun ==>
                gc_fun_const_ok s'.gc_fun
Proof
  metis_tac[evaluate_consts]
QED

val get_above_handler_def = Define `
  get_above_handler s = case EL (LENGTH s.stack - (s.handler + 1)) s.stack of
                          | StackFrame _ (SOME (h,_,_)) => h`;

Theorem enc_stack_dec_stack_is_gc_word_const:
   !s s' s'l.
   LIST_REL (\a b. is_gc_word_const a ==> b = a) (enc_stack s) s'l /\
   dec_stack s'l s = SOME s' ==>
   LIST_REL sf_gc_consts s s'
Proof
  Induct >- (rw [enc_stack_def] \\ fs [dec_stack_def]) \\
  Cases_on `h` \\ rw [enc_stack_def] \\ fs [dec_stack_def] \\ every_case_tac \\ fs [] \\ rw []
  >-
  (rw [sf_gc_consts_def] \\
  `(\(ak:num, av) (bk, bv). ak = bk /\ (is_gc_word_const av ==> bv = av)) =
   (\a b. (FST a) = (FST b) /\ (is_gc_word_const (SND a) ==> (SND b) = (SND a)))`
  by (rpt (irule EQ_EXT \\ rw [] \\ Cases_on `x'`) \\ rw []) \\
  simp [LIST_REL_CONJ] \\ conj_tac
    >-
    (`(\a:(num#'a word_loc) b:(num#'a word_loc). FST a = FST b) = (\a b. a = (FST b)) o FST`
    by (rpt (irule EQ_EXT \\ rw [] \\ Cases_on `x'`) \\ rw []) \\
    rw [GSYM LIST_REL_MAP1] \\ rw [Once (GSYM LIST_REL_MAP2)] \\ rw [MAP_ZIP] \\ rw [EVERY2_refl])
    >-
    (`(\a:(num#'a word_loc) b:(num#'a word_loc). is_gc_word_const (SND a) ==> SND b = SND a) =
     (\a b. is_gc_word_const a ==> SND b = a) o SND`
    by (rpt (irule EQ_EXT \\ rw [] \\ Cases_on `x'`) \\ rw []) \\
    rw [GSYM LIST_REL_MAP1] \\

    `(\a:('a word_loc) b:(num#'a word_loc). is_gc_word_const a ==> SND b = a) =
     (\a b. (\x y. is_gc_word_const x ==> y = x) a (SND b))`
    by (rpt (irule EQ_EXT \\ Cases_on `x`) \\ rw []) \\
    asm_rewrite_tac [] \\ rewrite_tac [GSYM LIST_REL_MAP2] \\

    rw [MAP_ZIP] \\ imp_res_tac LIST_REL_append_left \\ fs []))
  >-
  (last_assum irule \\ asm_exists_tac \\ rw [] \\
  imp_res_tac LIST_REL_append_left \\ fs [])
QED

Theorem gc_fun_sf_gc_consts:
   !s s'l s' gc_fun memory memory' mdomain store store'.
   gc_fun_const_ok gc_fun /\
   gc_fun (enc_stack s, memory, mdomain, store) = SOME (s'l, memory', store') /\
   dec_stack s'l s = SOME s' ==>
   LIST_REL sf_gc_consts s s'
Proof
  rw [] \\ imp_res_tac gc_fun_const_ok_def \\ fs [] \\
  metis_tac [enc_stack_dec_stack_is_gc_word_const]
QED

Theorem gc_sf_gc_consts:
   !s s'. gc_fun_const_ok s.gc_fun /\ gc s = SOME s' ==> LIST_REL sf_gc_consts s.stack s'.stack
Proof
  rw [gc_def] \\ every_case_tac \\ fs [] \\ imp_res_tac gc_fun_sf_gc_consts \\ rw []
QED

Theorem gc_handler:
   !s s'. gc s = SOME s' ==> s'.handler = s.handler
Proof
  rw [gc_def] \\ every_case_tac \\ rw [] \\ rw []
QED

Theorem sf_gc_consts_get_above_handler:
   !s s'. LIST_REL sf_gc_consts s.stack s'.stack /\
          s'.handler = s.handler /\
          s.handler < LENGTH s.stack ==>
          get_above_handler s' = get_above_handler s
Proof
  rw [get_above_handler_def] \\ imp_res_tac EVERY2_LENGTH \\
  `sf_gc_consts (EL (LENGTH s'.stack − (s.handler + 1)) s.stack)
                (EL (LENGTH s'.stack − (s.handler + 1)) s'.stack)`
  by (fs [LIST_REL_EL_EQN]) \\ every_case_tac \\ fs [sf_gc_consts_def]
QED

Theorem LIST_REL_call_Result:
   !s s' s'' s''' env handler.
   LIST_REL sf_gc_consts (push_env env handler s).stack s''.stack /\
   pop_env s'' = SOME s''' /\
   s''.handler = (push_env env handler s).handler ==>
   LIST_REL sf_gc_consts s.stack s'''.stack /\ s'''.handler = s.handler
Proof
  rpt gen_tac \\ strip_tac \\
  Cases_on `handler` \\ TRY (PairCases_on `x`) \\ fs [push_env_def, pop_env_def] \\ pairarg_tac \\ fs [] \\
  every_case_tac \\ fs [] \\ rw [] \\ rfs [] \\ qpat_x_assum `_ = x` (assume_tac o GSYM) \\ fs [sf_gc_consts_def]
QED

Theorem get_above_handler_call_env_push_env_dec_clock:
   !s s' s'' args env x0 x1 x2 x3.
   s' = call_env args (push_env env (SOME (x0,x1,x2,x3)) (dec_clock s)) /\
   s''.handler = get_above_handler s' ==>
   s''.handler = s.handler
Proof
  rw [call_env_def, push_env_def, dec_clock_def] \\ pairarg_tac \\ fs [get_above_handler_def] \\
  `SUC (LENGTH s.stack) − (LENGTH s.stack + 1) = 0` by (rw[]) \\ asm_rewrite_tac [] \\ rw []
QED

Theorem call_env_push_env_dec_clock_handler_length:
   !s s' args env x0 x1 x2 x3. s' = call_env args (push_env env (SOME (x0,x1,x2,x3)) (dec_clock s)) ==>
   s'.handler < LENGTH s'.stack
Proof
  rw [call_env_def, push_env_def, dec_clock_def] \\ pairarg_tac \\ fs []
QED

Theorem EVERY2_trans_LASTN_sf_gc_consts:
   !l l' l'' n R. n <= LENGTH l /\ LIST_REL sf_gc_consts l l' /\ LIST_REL sf_gc_consts (LASTN n l') l'' ==>
             LIST_REL sf_gc_consts (LASTN n l) l''
Proof
  rw [] \\ irule EVERY2_trans \\ conj_tac >- metis_tac [sf_gc_consts_trans] \\
  qexists_tac `LASTN n l'` \\ rw [list_rel_lastn]
QED

Theorem LIST_REL_push_env:
   !R s s' env h. LIST_REL R (push_env env h s).stack s'.stack ==> LIST_REL R s.stack (TL s'.stack)
Proof
  Cases_on `h` \\ TRY (PairCases_on `x`) \\ rw [push_env_def] \\ pairarg_tac \\ fs []
QED

Theorem LASTN_LENGTH_CONS:
   !l h. LASTN (LENGTH l) (h::l) = l
Proof
  rw [] \\ `h::l = [h] ++ l` by (rw[]) \\ asm_rewrite_tac [] \\ irule LASTN_LENGTH_APPEND
QED

Theorem LASTN_TL_res:
   !l n h t. n < LENGTH l /\ LASTN (n + 1) l = (h::t) ==> t = LASTN n l
Proof
  rw [] \\ `n + 1 <= LENGTH l` by (DECIDE_TAC) \\ fs [LASTN_DROP, DROP_EL_CONS]
QED

Theorem HD_LASTN:
   !l n. 0 < n /\ n <= LENGTH l ==> HD (LASTN n l) = EL (LENGTH l - n) l
Proof
  rw [] \\ imp_res_tac LASTN_DROP \\ ASSUME_TAC (Q.SPEC `0` EL_DROP) \\ fs []
QED

Theorem push_env_pop_env_locals_thm:
   !^s s' s'':('a,'c,'ffi) wordSem$state s''' env names (handler:(num # 'a prog # num # num) option).
  cut_env names s.locals = SOME env /\
  push_env env handler s = s' /\
  LIST_REL sf_gc_consts s'.stack s''.stack /\
  pop_env s'' = SOME s''' ==>
  (!v w. get_var v s = SOME w /\ is_gc_word_const w /\ lookup v names <> NONE ==> get_var v s''' = SOME w)
Proof
  Cases_on `handler` \\ TRY (PairCases_on `x`) \\ rw [push_env_def, env_to_list_def] \\
  fs [LIST_REL_def] \\ Cases_on `y` \\ fs [sf_gc_consts_def, pop_env_def] \\ rfs [] \\ rveq \\ fs [] \\
  rw [get_var_def, lookup_fromAList] \\

  irule ALOOKUP_LIST_REL_sf_gc_consts \\ rw [Once CONJ_COMM] \\ asm_exists_tac \\ rw [] \\

  `ALL_DISTINCT (MAP FST (toAList env))` by (rw [ALL_DISTINCT_MAP_FST_toAList]) \\

  (irule ALOOKUP_ALL_DISTINCT_FST_PERM_SOME \\ rpt conj_tac
      >- (irule ALL_DISTINCT_PERM_FST \\ fs [QSORT_PERM])
      >- (irule ALOOKUP_ALL_DISTINCT_FST_PERM_SOME \\ fs [ALOOKUP_toAList, QSORT_PERM, ALOOKUP_toAList]
          \\ fs [cut_env_def, get_var_def] \\ rw [lookup_inter_EQ])
      >- (irule PERM_list_rearrange \\ metis_tac [ALL_DISTINCT_MAP, QSORT_PERM, ALL_DISTINCT_PERM]))
QED

Theorem evaluate_sf_gc_consts:
   !p s s' res.
   evaluate (p, s) = (res, s') /\ gc_fun_const_ok s.gc_fun ==>
   (case res of
     | NONE =>
       LIST_REL sf_gc_consts s.stack s'.stack /\
       s'.handler = s.handler
     | SOME (Result _ _) =>
       LIST_REL sf_gc_consts s.stack s'.stack /\
       s'.handler = s.handler
     | SOME (Exception _ _) =>
       s.handler < LENGTH s.stack ==>
       LIST_REL sf_gc_consts (LASTN s.handler s.stack) s'.stack /\
       s'.handler = get_above_handler s
     | _ => T)
Proof
  recInduct evaluate_ind \\ reverse (rpt conj_tac)

  >- (** Call **)
  (rpt gen_tac \\ rpt DISCH_TAC \\ rpt gen_tac \\ DISCH_TAC \\ fs [evaluate_def] \\
  qpat_x_assum `_ = (res,s')` mp_tac \\
  ntac 3 (TOP_CASE_TAC >- (rw [] \\ rw [])) \\
  PairCases_on `x'` \\ fs [] \\
  TOP_CASE_TAC
    >- (every_case_tac \\ rw [] \\ fs [call_env_def, dec_clock_def, get_above_handler_def]) \\

  PairCases_on `x'` \\ fs [] \\
  ntac 3 (TOP_CASE_TAC >- (rw [] \\ rw [])) \\
  TOP_CASE_TAC \\
  TOP_CASE_TAC >- (rw [] \\ rw []) \\
  TOP_CASE_TAC
    >- (* Result from fun call *)
    (ntac 2 (TOP_CASE_TAC >- (rw [] \\ rw [])) \\
    reverse TOP_CASE_TAC >- (rw [] \\ rw []) \\
    fs [call_env_def, dec_clock_def, set_var_def] \\

    rfs [push_env_gc_fun] \\
    imp_res_tac evaluate_gc_fun_const_ok \\
    rfs [push_env_gc_fun] \\
    imp_res_tac pop_env_gc_fun_const_ok \\

    imp_res_tac LIST_REL_call_Result \\
    DISCH_TAC \\ TOP_CASE_TAC
      >- (* NONE from ret_handler *)
      (res_tac \\ fs [] \\ irule EVERY2_trans \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans \\
      asm_exists_tac \\ rw []) \\

    TOP_CASE_TAC
      >- (* Result from ret_handler *)
      (res_tac \\ fs[] \\ irule EVERY2_trans \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans \\
      asm_exists_tac \\ rw [])

      >- (* Exception from ret_handler *)
      (DISCH_TAC \\ res_tac \\
      `x''.handler < LENGTH x''.stack` by (metis_tac [LIST_REL_LENGTH]) \\ fs [] \\ conj_tac
        >-
        (irule EVERY2_trans_LASTN_sf_gc_consts \\ conj_tac >- rw [] \\ rfs [] \\ asm_exists_tac \\ rw [])
        >-
        rw [sf_gc_consts_get_above_handler]))

    >- (* Exception from fun call *)
    (TOP_CASE_TAC
      >- (* NONE, no handler *)
      (rw [] \\ fs [call_env_def, push_env_def, dec_clock_def] \\ pairarg_tac \\ fs [] \\
      DISCH_TAC \\ res_tac \\ `s.handler < SUC (LENGTH s.stack)` by DECIDE_TAC \\ fs [] \\ conj_tac
        >-
        fs [LASTN_CONS]
        >-
        (rw [get_above_handler_def, ADD1] \\
        `(LENGTH s.stack − s.handler) = SUC (LENGTH s.stack − (s.handler + 1))` by (fs[]) \\ fs []))

      >- (* SOME, has handler *)
      (PairCases_on `x''` \\ fs [] \\
      TOP_CASE_TAC >- (rw [] \\ rw []) \\
      reverse (TOP_CASE_TAC) >- (rw [] \\ rw []) \\

      imp_res_tac evaluate_gc_fun_const_ok \\
      fs [call_env_def, push_env_def, dec_clock_def, set_var_def] \\ pairarg_tac \\ fs [] \\ res_tac \\ fs [] \\

      fs [LASTN_LENGTH_CONS] \\

      DISCH_TAC \\ TOP_CASE_TAC \\ TRY (TOP_CASE_TAC)
        \\ TRY ( (* NONE or Result from handler *)
        res_tac \\ fs [] \\ rw []
          >- (irule EVERY2_trans
            \\ conj_tac >- ACCEPT_TAC sf_gc_consts_trans
            >- (asm_exists_tac \\ rw []))
          >- (rw [get_above_handler_def] \\ rw [ADD1]))

        >- (* Exception from handler *)
        (DISCH_TAC \\ res_tac \\ fs [get_above_handler_def, ADD1] \\
        `r.handler < LENGTH r.stack` by (metis_tac [LIST_REL_LENGTH]) \\
        fs [] \\ conj_tac
          >- (irule EVERY2_trans_LASTN_sf_gc_consts \\ conj_tac >- rw [] \\ asm_exists_tac \\ rw [])
          >- metis_tac [sf_gc_consts_get_above_handler, get_above_handler_def])))

    \\ (* Other cases *)
    (rw [] \\ rw []))

  \\ (** Easy cases **)
  TRY (rw [evaluate_def] \\ every_case_tac \\
  fs [call_env_def, dec_clock_def, mem_store_def, set_var_def, set_vars_def, set_store_def] \\
  TRY (pairarg_tac \\ fs []) \\
  imp_res_tac inst_const_full \\
  rw [] \\
  irule EVERY2_refl \\ rw [sf_gc_consts_refl])
  >- (* Install *)
    (rw[evaluate_def] \\ fs[case_eq_thms]>>rw[]>>
    pairarg_tac>>fs[case_eq_thms]>>rw[]>>
    irule EVERY2_refl>>
    metis_tac[sf_gc_consts_refl])
  >- (** Raise **)
  (rw [evaluate_def, jump_exc_def] \\ every_case_tac \\ fs [] \\
  imp_res_tac LASTN_TL_res \\ rw [get_above_handler_def]
    >- (irule EVERY2_refl \\ rw [sf_gc_consts_refl])
    >- fs [GSYM HD_LASTN])

  >- (** Seq **)
  (rw [evaluate_def] \\ pairarg_tac \\ fs [] \\ every_case_tac \\ fs [] \\
  imp_res_tac evaluate_gc_fun_const_ok \\ res_tac \\
  TRY (rw [] \\ irule EVERY2_trans \\ rpt conj_tac
  >- ACCEPT_TAC sf_gc_consts_trans >- (asm_exists_tac \\ rw [])) \\
  DISCH_TAC \\ imp_res_tac LIST_REL_LENGTH \\ fs [] \\ conj_tac
    >- (irule EVERY2_trans_LASTN_sf_gc_consts \\ rw [] \\ asm_exists_tac \\ rw [])
    >- rw [sf_gc_consts_get_above_handler])

  >- (** MustTerminate **)
  (rw [evaluate_def] \\ pairarg_tac \\ fs [] \\ every_case_tac \\ rw [] \\ rw [get_above_handler_def])

  >- (** Alloc **)
  (rw [evaluate_def, alloc_def] \\ every_case_tac \\ fs [] \\
  imp_res_tac gc_sf_gc_consts \\ fs [push_env_def, set_store_def, pop_env_def] \\
  pairarg_tac \\ fs [] \\ res_tac \\ Cases_on `y` \\ fs [sf_gc_consts_def] \\
  rveq \\ fs [] \\ imp_res_tac gc_handler \\ rw [])
QED

Theorem get_var_set_fp_var[simp]:
   get_var x (set_fp_var y v s) = get_var x s
Proof
  fs[get_var_def,set_fp_var_def]
QED

Theorem evaluate_const_fp_loop:
   !p cs p' cs' s res s'.
   evaluate (p, s) = (res, s') /\
   const_fp_loop p cs = (p', cs') /\
   gc_fun_const_ok s.gc_fun /\
   (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) ==>
   evaluate (p', s) = (res, s') /\
   (res = NONE ==> (!v w. lookup v cs' = SOME w ==> get_var v s' = SOME (Word w)))
Proof
  ho_match_mp_tac const_fp_loop_ind \\ (rpt conj_tac)
  >- (** Move **)
  (fs [const_fp_loop_def, evaluate_def] \\ rw [const_fp_move_cs_def] \\
  every_case_tac \\ fs [] \\
  imp_res_tac get_var_move_thm \\ asm_rewrite_tac [] \\
  imp_res_tac (INST_TYPE [``:'a``|->``:'a word``] lookup_const_fp_move_cs) \\
  CASE_TAC \\ fs [])
  >- (** Inst **)
  (rw [] >- fs [const_fp_loop_def] \\
  Cases_on `i` \\ fs [const_fp_loop_def, const_fp_inst_cs_def, evaluate_def]
    >- (* Skip *)
    (fs [inst_def] \\ rw [])
    >- (* Const *)
    (fs [inst_def, assign_def, word_exp_def] \\ metis_tac [cs_delete_if_set])
    >- (* Arith *)
    (Cases_on `a` \\ fs [const_fp_inst_cs_def, inst_def, assign_def] \\
    every_case_tac \\ fs [] \\ rveq \\
    fs [get_var_def,set_var_def,lookup_insert,lookup_delete] \\
    metis_tac [cs_delete_if_set, cs_delete_if_set_x2])
    >- (* Mem *)
    (Cases_on `m` \\ fs [inst_def, const_fp_inst_cs_def]
      >- (* Load *)
      (every_case_tac \\ fs [] \\ metis_tac [cs_delete_if_set])
      >- (* Load8 *)
      (every_case_tac \\ fs [mem_store_def] \\ rw [] \\
      metis_tac [cs_delete_if_set, cs_delete_if_set])
      \\ (* Otherwise *)
      every_case_tac \\ fs [mem_store_def, get_var_def] \\ rw [])
    >- (*Float*)
      (Cases_on`f`>>fs[inst_def,const_fp_inst_cs_def]>>rw[]>>
      every_case_tac>>fs[]>>rw[]>>
      metis_tac [cs_delete_if_set,cs_delete_if_set_x2])
  )

  >- (** Assign **)
  (rpt gen_tac \\ strip_tac \\
  fs [const_fp_loop_def] \\ FULL_CASE_TAC \\ fs [] \\
  rveq \\ fs [evaluate_def] \\ (rw [] >- (metis_tac [const_fp_exp_word_exp]))
    >- (* Const *)
    (imp_res_tac const_fp_exp_word_exp_const \\
    fs [lookup_insert] \\ every_case_tac \\ fs [] \\ rw [get_var_set_var_thm])
    \\ (* Other cases *)
    fs [lookup_delete] \\ every_case_tac \\ fs [] \\ rw [get_var_set_var_thm])

  >- (** Get **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  every_case_tac \\ fs [] \\ metis_tac [cs_delete_if_set])

  >- (** MustTerminate **)
  (rpt (rpt gen_tac \\ DISCH_TAC) \\ fs [const_fp_loop_def] \\ pairarg_tac \\
  fs [] \\ qpat_x_assum `_ = p'` (assume_tac o GSYM) \\ fs [evaluate_def] \\
  TOP_CASE_TAC >- (rw []) \\ rpt (pairarg_tac \\ fs []) \\
  `gc_fun_const_ok (s with <|clock := MustTerminate_limit (:'a); termdep := s.termdep − 1|>).gc_fun`
  by (rw []) \\
  `!v w. lookup v cs = SOME w ==>
         get_var v (s with <|clock := MustTerminate_limit (:'a); termdep := s.termdep − 1|>) = SOME (Word w)`
  by (fs [get_var_def]) \\
  res_tac \\ every_case_tac \\ fs [get_var_def] \\ rw [])

  >- (** Seq **)
  (rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac \\
  fs [evaluate_def, const_fp_loop_def] \\
  rpt (pairarg_tac \\ fs []) \\
  imp_res_tac evaluate_consts \\
  (* Does the first program evaluation fail? *)
  Cases_on `res'` \\ fs [] \\ res_tac \\ fs [] \\ rw [evaluate_def])

  >- (** If **)
  (rpt gen_tac \\ strip_tac \\ rewrite_tac [evaluate_def, const_fp_loop_def] \\ rpt gen_tac \\
  reverse (Cases_on `lookup lhs cs`) \\ reverse (Cases_on `get_var_imm_cs rhs cs`) \\
  DISCH_TAC \\ fs []
    >- (* Both SOME *)
    (imp_res_tac get_var_imm_cs_imp_get_var_imm \\ res_tac \\ fs [] \\
    Cases_on `word_cmp cmp x x'` \\ fs [] \\ res_tac \\ rw [])

    \\ (* Otherwise *)
    (rpt (pairarg_tac \\ fs []) \\ every_case_tac \\ rw [evaluate_def] \\
    res_tac \\ fs [lookup_inter_eq] \\ every_case_tac \\ rw []))

  >- (** Call **)
  (rpt (rpt gen_tac \\ DISCH_TAC) \\ fs [const_fp_loop_def, evaluate_def] \\
  qpat_x_assum `_ = (res, s')` mp_tac \\
  ntac 3 (TOP_CASE_TAC >- (every_case_tac \\ TRY (pairarg_tac) \\ fs [] \\
                           rw [evaluate_def] \\ rw [] \\ fs [add_ret_loc_def])) \\
  TOP_CASE_TAC \\
  TOP_CASE_TAC >- (every_case_tac \\ fs [] \\
                   rw [evaluate_def] \\ rw [] \\ fs [add_ret_loc_def]) \\
  PairCases_on `x'` \\ fs [] \\
  ntac 3 (TOP_CASE_TAC >- (every_case_tac \\ TRY (pairarg_tac) \\ fs [] \\
                           rw [evaluate_def] \\ rw [] \\ fs [add_ret_loc_def])) \\
  TOP_CASE_TAC \\
  TOP_CASE_TAC >- (every_case_tac \\ TRY (pairarg_tac) \\ fs [] \\
                   rw [evaluate_def] \\ rw [] \\ fs [add_ret_loc_def]) \\
  reverse (Cases_on `handler`) \\ fs []
    >- (every_case_tac \\ rw [evaluate_def] \\ fs [lookup_def]) \\
  pairarg_tac \\ fs [] \\ TOP_CASE_TAC \\ fs [] \\
  TRY (rw [evaluate_def] \\ fs [add_ret_loc_def] \\ NO_TAC) \\
  rveq \\ fs [add_ret_loc_def] \\
  TOP_CASE_TAC >- rw [evaluate_def, add_ret_loc_def, find_code_def] \\
  rewrite_tac [evaluate_def, add_ret_loc_def, find_code_def] \\
  imp_res_tac evaluate_sf_gc_consts \\ fs [call_env_def, dec_clock_def] \\
  TOP_CASE_TAC >- rw [] \\
  reverse TOP_CASE_TAC >- rw [] \\
  DISCH_TAC \\ first_assum irule \\ rpt conj_tac
    >- (rw [get_var_set_var_thm, lookup_delete] \\
       imp_res_tac lookup_filter_v_SOME \\
       imp_res_tac lookup_filter_v_SOME_imp \\
       fs [lookup_inter_EQ] \\ rfs [] \\
       drule push_env_pop_env_locals_thm \\ fs [] \\
       rpt (disch_then drule) \\
       last_x_assum drule>>
       strip_tac>>
       disch_then drule>>
       fs[is_gc_word_const_def])
    >- (imp_res_tac evaluate_consts \\ imp_res_tac pop_env_gc_fun \\
       fs [set_var_def, push_env_gc_fun])
    >- rw[])

  >- (** FFI **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  every_case_tac \\ fs [] \\
  fs [cut_env_def, get_var_def, lookup_inter] \\
  every_case_tac \\ fs [] \\ res_tac \\ rw [lookup_inter])

  >- (** LocValue **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  metis_tac [cs_delete_if_set])

  >- (** Alloc **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def, alloc_def] \\ every_case_tac \\ fs [] \\
  `gc_fun_const_ok (push_env x (NONE:(num # 'a prog # num # num) option) (set_store AllocSize (Word c) s)).gc_fun`
  by (fs [set_store_def, push_env_gc_fun]) \\
  imp_res_tac gc_sf_gc_consts \\
  fs [push_env_set_store_stack] \\
  imp_res_tac lookup_filter_v_SOME \\
  imp_res_tac lookup_filter_v_SOME_imp \\ fs [lookup_inter_EQ] \\
  metis_tac [push_env_pop_env_locals_thm, is_gc_word_const_def])

  >- (* Install *) (
    rw[const_fp_loop_def]\\ fs[evaluate_def,case_eq_thms] \\
    pairarg_tac \\ fs[case_eq_thms] \\
    rw[] \\ fs[cut_env_def,get_var_def] \\
    fs[lookup_insert,lookup_delete] \\
    imp_res_tac lookup_filter_v_SOME_imp \\
    rw[]>>
    fs[lookup_inter,case_eq_thms])

  >- (** Skip **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\ fs [])

  >- (** Set **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  res_tac \\ every_case_tac \\ rw [] \\ rw [get_var_set_store_thm])

  >- (** Store **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  every_case_tac \\ rw [] \\ metis_tac [get_var_mem_store_thm])

  \\ (** Remaining: Raise, Return and Tick, buffer writes**)
    rw[const_fp_loop_def,evaluate_def] \\ fs[case_eq_thms,evaluate_def] \\
    rw[dec_clock_def]
QED

Theorem evaluate_const_fp:
   !p s. gc_fun_const_ok s.gc_fun ==> evaluate (const_fp p, s) = evaluate (p, s)
Proof
  rw [const_fp_def] \\ imp_res_tac evaluate_const_fp_loop \\
  last_assum (qspec_then `LN` assume_tac) \\ fs [lookup_def] \\
  Cases_on `const_fp_loop p LN` \\ simp [] \\ res_tac \\
  Cases_on `evaluate (p, s)` \\ res_tac
QED

Theorem extract_labels_const_fp:
   labels_rel (extract_labels p) (extract_labels (const_fp p))
Proof
  fs [const_fp_def] \\ Cases_on `const_fp_loop p LN`
  \\ rename1 `const_fp_loop p cs = (p1,cs1)` \\ fs []
  \\ pop_assum mp_tac
  \\ qspec_tac (`cs1`,`cs1`) \\ qspec_tac (`p1`,`p1`)
  \\ qspec_tac (`cs`,`cs`) \\ qspec_tac (`p`,`p`)
  \\ ho_match_mp_tac const_fp_loop_ind
  \\ ntac 6 (conj_tac THEN1
   (fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def]
    \\ every_case_tac
    \\ fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def]
    \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [extract_labels_def]
    \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [extract_labels_def]
    \\ match_mp_tac labels_rel_APPEND \\ fs []))
  \\ reverse (rpt conj_tac)
  \\ TRY (fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def] \\ NO_TAC)
  THEN1 (* Call *)
   (rw [] \\ fs [const_fp_loop_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [extract_labels_def]
    \\ once_rewrite_tac [CONS_APPEND]
    \\ match_mp_tac labels_rel_APPEND \\ fs [])
  \\ (* If *) rw [] \\ fs [const_fp_loop_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [extract_labels_def]
  \\ TRY (match_mp_tac labels_rel_APPEND \\ fs [])
  \\ fs [labels_rel_def,ALL_DISTINCT_APPEND,SUBSET_DEF]
QED

Theorem every_inst_inst_ok_less_const_fp:
   ∀prog.
    every_inst (inst_ok_less ac) prog ⇒
    every_inst (inst_ok_less ac) (const_fp prog)
Proof
  strip_tac
  \\ fs [const_fp_def] \\ Cases_on `const_fp_loop prog LN`
  \\ rename1 `const_fp_loop p cs = (p1,cs1)` \\ fs []
  \\ pop_assum mp_tac
  \\ qspec_tac (`cs1`,`cs1`) \\ qspec_tac (`p1`,`p1`)
  \\ qspec_tac (`cs`,`cs`) \\ qspec_tac (`p`,`p`)
  \\ ho_match_mp_tac const_fp_loop_ind \\ rw []
  \\ fs [const_fp_loop_def] \\ rw [] \\ fs [every_inst_def]
  \\ every_case_tac \\ rw [] \\ fs [every_inst_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [every_inst_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [every_inst_def]
QED

(* putting it all together *)

Theorem compile_exp_thm:
   wordSem$evaluate (prog,^s) = (res,s2) /\ res <> SOME Error /\
   gc_fun_const_ok s.gc_fun ==>
   evaluate (word_simp$compile_exp prog,s) = (res,s2)
Proof
    fs [word_simpTheory.compile_exp_def,evaluate_simp_if,evaluate_Seq_assoc,
        evaluate_const_fp]
QED

Theorem extract_labels_compile_exp[simp]:
   !p. labels_rel (extract_labels p)
                  (extract_labels (word_simp$compile_exp p))
Proof
  fs [word_simpTheory.compile_exp_def]>>
  metis_tac[extract_labels_simp_if,extract_labels_Seq_assoc,PERM_TRANS,
            extract_labels_const_fp,PERM_IMP_labels_rel,labels_rel_TRANS]
QED

val dest_Seq_no_inst = Q.prove(`
  ∀prog.
  every_inst (inst_ok_less ac) prog ⇒
  every_inst (inst_ok_less ac) (FST (dest_Seq prog)) ∧
  every_inst (inst_ok_less ac) (SND (dest_Seq prog))`,
  ho_match_mp_tac dest_Seq_ind>>rw[dest_Seq_def]>>fs[every_inst_def])

val simp_if_no_inst = Q.prove(`
  ∀prog.
  every_inst (inst_ok_less ac) prog ⇒
  every_inst (inst_ok_less ac) (simp_if prog)`,
  ho_match_mp_tac simp_if_ind>>rw[simp_if_def]>>
  EVERY_CASE_TAC>>
  fs[every_inst_def,apply_if_opt_def]>>
  pop_assum mp_tac>>EVERY_CASE_TAC>>
  pairarg_tac>>fs[]>>
  FULL_CASE_TAC>>
  PairCases_on`x'`>>
  fs[dest_If_thm]>>
  EVERY_CASE_TAC>>fs[SmartSeq_def]>>
  EVERY_CASE_TAC>>rw[]>>rveq>>fs[every_inst_def,dest_If_Eq_Imm_thm]>>
  imp_res_tac dest_Seq_no_inst>> rfs[every_inst_def])

val Seq_assoc_no_inst = Q.prove(`
  ∀p1 p2.
  every_inst (inst_ok_less ac) p1 ∧ every_inst (inst_ok_less ac) p2 ⇒
  every_inst (inst_ok_less ac) (Seq_assoc p1 p2)`,
  ho_match_mp_tac Seq_assoc_ind>>fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  fs[every_inst_def]>>
  every_case_tac>>fs[])

Theorem compile_exp_no_inst:
    ∀prog.
  every_inst (inst_ok_less ac) prog ⇒
  every_inst (inst_ok_less ac) (compile_exp prog)
Proof
  fs[compile_exp_def]>>
  metis_tac[simp_if_no_inst,Seq_assoc_no_inst,every_inst_def,
            every_inst_inst_ok_less_const_fp]
QED

val _ = export_theory();
