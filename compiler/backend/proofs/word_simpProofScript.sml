(*
  Correctness proof for word_simp
*)
open alistTheory preamble wordLangTheory wordSemTheory wordPropsTheory word_simpTheory;

val _ = new_theory "word_simpProof";

val s = ``s:('a,'c,'ffi) wordSem$state``

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_simp"];

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

(** verification of const_fp **)

(* gc *)

Definition is_gc_word_const_def:
  is_gc_word_const (Loc _ _) = T /\
  is_gc_word_const (Word w) = is_gc_const w
End

Definition gc_fun_const_ok_def:
  gc_fun_const_ok (f:'a gc_fun_type) =
    !x y. f x = SOME y ==> EVERY2 (\a b. is_gc_word_const a ==> b = a) (FST x) (FST y)
End


Definition sf_gc_consts_def:
  sf_gc_consts (StackFrame _ l0 sv h) (StackFrame _ l0' sw h') =
  (EVERY2 (\(ak, av) (bk, bv). (ak = bk) /\ (is_gc_word_const av ==> bv = av)) sv sw /\   l0 = l0' /\ h = h')
End

(*
Definition sf_gc_consts_def:
  sf_gc_consts (StackFrame lsz sv h) (StackFrame lsz' sw h') =
  (EVERY2 (\(ak, av) (bk, bv). (ak = bk) /\ (is_gc_word_const av ==> bv = av)) sv sw /\
   lsz = lsz' /\ h = h')
End
*)

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
(*TODO move*)
Theorem get_var_set_var_thm:
   !k1 k2 v s. get_var k1 (set_var k2 v s) =
               if k1 = k2 then SOME v else get_var k1 s
Proof
  rw [get_var_def, set_var_def, lookup_insert]
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

(*TODO delete*)
Triviality pop_env_stack_gc:
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
  rw [] \\
  Cases_on `h` \\ Cases_on `x` \\ fs [ALOOKUP_def] \\ rveq \\ TOP_CASE_TAC \\ fs [] \\
  first_assum irule \\ rw [] \\ asm_exists_tac \\ rw []
QED

Theorem ALOOKUP_LIST_REL_sf_gc_consts_NONE:
   !l1 l2 k v.
   LIST_REL (\(ak, av) (bk, bv). ak = bk /\ (is_gc_word_const av ==> bv = av)) l1 l2 /\
   ALOOKUP l1 k = NONE ==>
   ALOOKUP l2 k = NONE
Proof
  Induct_on `l2`
    >- (rpt gen_tac \\ rpt strip_tac \\ fs [] \\ rveq \\ fs [ALOOKUP_def]) \\
  rw [] \\ Cases_on `h` \\ Cases_on `x` \\
  gvs [ALOOKUP_def] \\
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

Definition get_above_handler_def:
  get_above_handler s = case EL (LENGTH s.stack - (s.handler + 1)) s.stack of
                          | StackFrame _ _ _ (SOME (h,_,_)) => h
End

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
   !s s' s'' args lsz env x0 x1 x2 x3.
   s' = call_env args lsz (push_env env (SOME (x0,x1,x2,x3)) (dec_clock s)) /\
   s''.handler = get_above_handler s' ==>
   s''.handler = s.handler
Proof
  rw [call_env_def, flush_state_def, push_env_def, dec_clock_def] \\ pairarg_tac \\ fs [get_above_handler_def] \\
  `SUC (LENGTH s.stack) − (LENGTH s.stack + 1) = 0` by (rw[]) \\ asm_rewrite_tac [] \\ rw []
QED

Theorem call_env_push_env_dec_clock_handler_length:
   !s s' args lsz env x0 x1 x2 x3. s' = call_env args lsz (push_env env (SOME (x0,x1,x2,x3)) (dec_clock s)) ==>
   s'.handler < LENGTH s'.stack
Proof
  rw [call_env_def, flush_state_def, push_env_def, dec_clock_def] \\ pairarg_tac \\ fs []
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

(*TODO move*)
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
  ∀^s s' s'':('a,'c,'ffi) wordSem$state s''' env names (handler:(num # 'a prog # num # num) option).
  cut_envs names s.locals = SOME env /\
  push_env env handler s = s' /\
  LIST_REL sf_gc_consts s'.stack s''.stack /\
  pop_env s'' = SOME s''' ==>
  (!v w. get_var v s = SOME w /\ is_gc_word_const w /\ lookup v (all_names names) <> NONE ==> get_var v s''' = SOME w)
Proof
  Cases_on `handler` \\ TRY (PairCases_on `x`) \\ rw [push_env_def, env_to_list_def] \\
  fs [LIST_REL_def] \\ Cases_on `y` \\ fs [sf_gc_consts_def, pop_env_def] \\ rfs [] \\ rveq \\ fs [] \\
  rw [get_var_def, lookup_fromAList] \\
  PairCases_on ‘names’ \\
  gvs [cut_envs_def,AllCaseEqs(),lookup_union,lookup_fromAList,cut_names_def,get_var_def,ALOOKUP_toAList,
       lookup_inter] \\
  Cases_on ‘lookup v names1’ \\ fs []
  \\ TRY
     (disj1_tac
      \\ Cases_on ‘lookup v names0’ \\ fs []
      \\ irule ALOOKUP_LIST_REL_sf_gc_consts_NONE
      \\ first_x_assum $ irule_at Any
      \\ fs [ALOOKUP_NONE,MEM_MAP,mem_list_rearrange,sortingTheory.QSORT_MEM]
      \\ fs [MEM_toAList,FORALL_PROD,lookup_inter] \\ NO_TAC)
  \\ disj2_tac \\ drule ALOOKUP_LIST_REL_sf_gc_consts
  \\ disch_then irule \\ fs []
  \\ (irule ALOOKUP_ALL_DISTINCT_FST_PERM_SOME \\ rpt conj_tac
      >- (irule ALL_DISTINCT_PERM_FST \\ fs [QSORT_PERM,ALL_DISTINCT_MAP_FST_toAList])
      >- (irule ALOOKUP_ALL_DISTINCT_FST_PERM_SOME \\ fs [ALOOKUP_toAList, QSORT_PERM, ALOOKUP_toAList]
          \\ fs [cut_env_def, get_var_def] \\ rw [lookup_inter_EQ,ALL_DISTINCT_MAP_FST_toAList])
      >- (irule PERM_list_rearrange \\
       metis_tac [ALL_DISTINCT_MAP, QSORT_PERM, ALL_DISTINCT_PERM,ALL_DISTINCT_MAP_FST_toAList]))
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
    >- (every_case_tac \\ rw [] \\ fs [call_env_def, flush_state_def, dec_clock_def, get_above_handler_def]) \\

  PairCases_on `x'` \\ fs [] \\
  ntac 3 (TOP_CASE_TAC >- (rw [] \\ rw [])) \\
  TOP_CASE_TAC \\
  TOP_CASE_TAC >- (rw [] \\ rw []) \\
  TOP_CASE_TAC
    >- (* Result from fun call *)
    (ntac 2 (TOP_CASE_TAC >- (rw [] \\ rw [])) \\
    reverse TOP_CASE_TAC >- (rw [] \\ rw []) \\
    fs [call_env_def, flush_state_def, dec_clock_def, set_var_def] \\

    rfs [] \\
    imp_res_tac evaluate_gc_fun_const_ok \\
    rfs [] \\
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
      (rw [] \\ fs [call_env_def, flush_state_def, push_env_def, dec_clock_def] \\ pairarg_tac \\ fs [] \\
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
      fs [call_env_def, flush_state_def, push_env_def, dec_clock_def, set_var_def] \\ pairarg_tac \\ fs [] \\ res_tac \\ fs [] \\

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
  >~ [`ShareInst`]
  >- (gvs[evaluate_def,oneline share_inst_def,
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
      oneline sh_mem_set_var_def] >>
    rw[] >>
    gvs[AllCaseEqs(),set_var_def,flush_state_def] >>
    irule EVERY2_refl >>
    metis_tac[sf_gc_consts_refl] )
  \\ (** Easy cases **)
  TRY (rw [evaluate_def] \\ every_case_tac \\
  fs [call_env_def, flush_state_def, dec_clock_def, mem_store_def] \\
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
  imp_res_tac gc_sf_gc_consts \\ fs [push_env_def, pop_env_def] \\
  pairarg_tac \\ fs [] \\ res_tac \\ Cases_on `y` \\ fs [sf_gc_consts_def] \\
  rveq \\ fs [] \\ imp_res_tac gc_handler \\ rw [])
QED

Theorem evaluate_drop_consts_1:
  ∀vs rest s.
  (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) ==>
  evaluate (drop_consts cs vs,s) = (NONE, s)
Proof
  Induct>>rw[evaluate_def,drop_consts_def]>>
  every_case_tac>>gvs[evaluate_SmartSeq,evaluate_def]>>
  simp[word_exp_def,set_var_def,state_component_equality]>>
  metis_tac[insert_unchanged,get_var_def]
QED

Theorem evaluate_drop_consts[simp]:
  (!v w. lookup v cs = SOME w ==> get_var v s = SOME (Word w)) ==>
  evaluate (SmartSeq (drop_consts cs vs) p,s) = evaluate (p, s)
Proof
  rw[evaluate_SmartSeq,evaluate_def,evaluate_drop_consts_1]
QED

Theorem lookup_FOLDR_delete[local]:
  ∀l m v w.
    lookup v (FOLDR delete m l) = SOME w ⇒
    lookup v m = SOME w ∧ ~MEM v l
Proof
  Induct \\ fs [lookup_delete,AllCaseEqs(),SF SFY_ss]
QED

Theorem get_var_set_vars_ignore:
  ∀xs l m. ~MEM v xs ⇒ get_var v (set_vars xs l m) = get_var v m
Proof
  Induct \\ fs [set_vars_def,get_var_def,alist_insert_def]
  \\ Cases_on ‘l’ \\ fs [set_vars_def,get_var_def,alist_insert_def]
  \\ fs [lookup_insert]
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
      >- (* Load32 *)
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
  >- (** OpCurrHeap **)
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
  (
  rpt (rpt gen_tac \\ DISCH_TAC) \\ fs [const_fp_loop_def, evaluate_def] \\
  qpat_x_assum `_ = (res, s')` mp_tac \\
  ntac 3 (
    TOP_CASE_TAC >- (
      every_case_tac \\ TRY (pairarg_tac) \\
      rw[] \\ gvs[evaluate_def] \\
      fs [add_ret_loc_def])) \\
  PairCases_on `x'` \\ fs[]  \\
  TOP_CASE_TAC >- (
    every_case_tac \\ fs [] \\
    rw [] \\ gvs[evaluate_def] \\
    fs [add_ret_loc_def]) \\
  PairCases_on `x'` \\ fs [] \\
  ntac 3 (
    TOP_CASE_TAC >- (
      every_case_tac \\ TRY (pairarg_tac) \\
      rw[] \\ gvs[evaluate_def] \\
      fs [add_ret_loc_def])) \\
  TOP_CASE_TAC \\
  TOP_CASE_TAC >- (
      every_case_tac \\ TRY (pairarg_tac) \\
      rw[] \\ gvs[evaluate_def] \\
      fs [add_ret_loc_def]) \\
  reverse (Cases_on `handler`) \\ fs []
  >- (
      every_case_tac \\ TRY (pairarg_tac) \\
      rw[] \\ gvs[evaluate_def] \\
      fs [add_ret_loc_def]) \\
  pairarg_tac \\ fs [] \\ TOP_CASE_TAC \\ fs [] \\
  TRY (rw [] \\ gvs[evaluate_def,add_ret_loc_def] \\ NO_TAC) \\
  (* one subgoal left *)
  gvs [add_ret_loc_def] \\
  TOP_CASE_TAC >-
    rw [evaluate_def,add_ret_loc_def, find_code_def] \\
  rewrite_tac [evaluate_def,evaluate_drop_consts, add_ret_loc_def, find_code_def] \\
  imp_res_tac evaluate_sf_gc_consts \\ fs [call_env_def, flush_state_def, dec_clock_def] \\
  TOP_CASE_TAC >-
    rw [] \\
  reverse TOP_CASE_TAC >- rw [] \\
  DISCH_TAC \\ first_assum irule \\
  rpt conj_tac
    >- (rw [get_var_set_var_thm, lookup_delete] \\
       drule lookup_FOLDR_delete \\ rw [] \\
       drule_then assume_tac lookup_filter_v_SOME \\
       imp_res_tac lookup_filter_v_SOME_imp \\
       fs [lookup_inter_EQ] \\ rfs [] \\
       drule push_env_pop_env_locals_thm \\ fs [] \\
       rpt (disch_then drule) \\
       last_x_assum drule>>
       strip_tac>>
       disch_then drule>>
       fs[is_gc_word_const_def,get_var_set_vars_ignore])
    >- (imp_res_tac evaluate_consts \\ imp_res_tac pop_env_gc_fun \\
       fs [set_vars_def])
    >- rw[])

  >- (** FFI **)

   (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
    gvs [AllCaseEqs(), cut_env_def, get_var_def, lookup_inter, cut_envs_def] \\
    PairCases_on ‘names’ \\ gvs [lookup_inter,lookup_union,AllCaseEqs(),cut_names_def] \\
    res_tac \\ fs [] \\ Cases_on ‘lookup v names1’ \\ fs [])
  >- (** LocValue **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  metis_tac [cs_delete_if_set])

  >- (** Alloc **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def, alloc_def] \\ every_case_tac \\ fs [] \\
  `gc_fun_const_ok (push_env x (NONE:(num # 'a prog # num # num) option) (set_store AllocSize (Word c) s)).gc_fun`
  by (fs [set_store_def]) \\
  imp_res_tac gc_sf_gc_consts \\
  fs [push_env_set_store_stack] \\
  imp_res_tac lookup_filter_v_SOME \\
  imp_res_tac lookup_filter_v_SOME_imp \\ fs [lookup_inter_EQ] \\
  metis_tac [push_env_pop_env_locals_thm, is_gc_word_const_def])

  >- ( (** StoreConsts **)
    fs [const_fp_loop_def] \\ rw [evaluate_def] \\ every_case_tac \\ fs [] \\
    fs [get_var_def,lookup_delete] \\ res_tac \\
    gvs [set_var_def,lookup_insert,lookup_delete,unset_var_def])
  >- (* Install *)
   (rw[const_fp_loop_def]\\ fs[evaluate_def,case_eq_thms] \\
    pairarg_tac \\ gvs[case_eq_thms] \\
    rw[] \\ fs[cut_env_def,get_var_def] \\
    fs[lookup_insert,lookup_delete] \\
    imp_res_tac lookup_filter_v_SOME_imp \\
    rw[]>>
    gvs[lookup_inter,case_eq_thms] \\
    PairCases_on ‘names’ \\
    gvs [cut_envs_def,cut_names_def,AllCaseEqs(),lookup_union,lookup_inter] \\
    Cases_on ‘lookup v names1’ \\ fs [] \\
    Cases_on ‘lookup v s.locals’ \\ fs [])

  >- (** Store **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  every_case_tac \\ rw [] \\
  drule_then assume_tac const_fp_exp_word_exp \\
  gvs[] \\
  metis_tac [get_var_mem_store_thm])

  (** ShareInst **)
  >>~- ([`ShareInst`],
    fs[const_fp_loop_def] \\
    gvs[evaluate_def,oneline share_inst_def,
      sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_load32_def,
      oneline sh_mem_set_var_def] \\
    rw[] \\
    gvs[AllCaseEqs(),set_var_def,flush_state_def,
      get_var_def,lookup_insert,lookup_delete] \\
    metis_tac[SIMP_RULE(srw_ss())[get_var_def]const_fp_exp_word_exp] )

  >- (** Skip **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\ fs [])

  >- (** Set **)
  (fs [const_fp_loop_def] \\ rw [evaluate_def] \\
  res_tac \\ every_case_tac \\ rw [] \\ rw [])

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

(* the duplicate-if pass *)

Triviality evaluate_try_if_hoist2:
  ! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  gc_fun_const_ok s.gc_fun ==>
  evaluate (p3, s) = evaluate (Seq (Seq p1 interm) p2, s)
Proof
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rw []
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs []
  >- (
    ONCE_REWRITE_TAC [GSYM evaluate_Seq_assoc]
    \\ simp [Seq_assoc_def]
  )
  >- (
    fs [dest_If_thm]
    \\ simp [evaluate_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ imp_res_tac evaluate_gc_fun_const_ok
    \\ fs [evaluate_const_fp]
    \\ fs [evaluate_def]
    \\ rpt ((pairarg_tac ORELSE TOP_CASE_TAC) \\ fs [])
    \\ gs []
  )
  >- (
    fs [dest_If_thm]
    \\ simp [evaluate_const_fp]
    \\ simp [evaluate_def]
    \\ rpt ((pairarg_tac ORELSE TOP_CASE_TAC) \\ fs [])
    \\ gs []
  )
QED

Triviality evaluate_try_if_hoist1:
  try_if_hoist1 p1 p2 = SOME p3 ==>
  gc_fun_const_ok s.gc_fun ==>
  evaluate (p3, s) = evaluate (Seq p1 p2, s)
Proof
  simp [try_if_hoist1_def]
  \\ every_case_tac \\ fs []
  \\ rw []
  \\ drule evaluate_try_if_hoist2
  \\ rw []
  \\ ONCE_REWRITE_TAC [GSYM evaluate_Seq_assoc]
  \\ simp [Seq_assoc_def]
QED

Theorem evaluate_simp_duplicate_if:
  !p s. gc_fun_const_ok s.gc_fun ==>
  evaluate (simp_duplicate_if p, s) = evaluate (p, s)
Proof
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ ((Cases_on `p` \\ fs []) >~ [`Seq`] >~ [`Call`])
  >- (
    irule (Q.prove (`((?x y. a = (x, y)) ==> a = b) ==> a = b`,
        Cases_on `a` \\ simp []))
    \\ rpt (TOP_CASE_TAC \\ fs [])
    \\ strip_tac
    \\ fs [evaluate_def]
    \\ fs [CaseEq "option", CaseEq "bool", CaseEq "prod",
        CaseEq "wordSem$result",
        add_ret_loc_def]
    \\ gvs []
    \\ fs [set_var_def, call_env_def]
    \\ imp_res_tac pop_env_stack_gc
    \\ imp_res_tac evaluate_gc_fun_const_ok
    \\ gs [dec_clock_def, push_env_def]
  )
  >- (
    TOP_CASE_TAC
    >- (
      simp [evaluate_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ imp_res_tac evaluate_gc_fun_const_ok
      \\ simp []
    )
    >- (
      simp [evaluate_Seq_assoc]
      \\ imp_res_tac evaluate_try_if_hoist1
      \\ simp [evaluate_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ imp_res_tac evaluate_gc_fun_const_ok
      \\ simp []
    )
  )
  \\ simp [evaluate_def]
QED

(* putting it all together *)

Theorem compile_exp_thm:
   wordSem$evaluate (prog,^s) = (res,s2) /\ res <> SOME Error /\
   gc_fun_const_ok s.gc_fun ==>
   evaluate (word_simp$compile_exp prog,s) = (res,s2)
Proof
    fs [word_simpTheory.compile_exp_def,evaluate_Seq_assoc,
        evaluate_const_fp, evaluate_simp_duplicate_if]
QED

val _ = export_theory();
