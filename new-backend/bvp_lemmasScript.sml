open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp_lemmas";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory bvpTheory;
open sptreeTheory lcsymtacs;

val bvp_state_explode = store_thm("bvp_state_explode",
  ``!t1 t2.
      t1 = t2 <=>
      (t1.code = t2.code) /\
      (t1.clock = t2.clock) /\
      (t1.globals = t2.globals) /\
      (t1.locals = t2.locals) /\
      (t1.output = t2.output) /\
      (t1.refs = t2.refs) /\
      (t1.handler = t2.handler) /\
      (t1.stack = t2.stack) /\
      (t1.space = t2.space)``,
  Cases \\ Cases \\ fs (TypeBase.updates_of ``:bvp_state`` @
                        TypeBase.accessors_of ``:bvp_state``)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ fs []);

val lookup_inter_EQ = store_thm("lookup_inter_EQ",
  ``((lookup x (inter t1 t2) = SOME y) <=>
       (lookup x t1 = SOME y) /\ lookup x t2 <> NONE) /\
    ((lookup x (inter t1 t2) = NONE) <=>
       (lookup x t1 = NONE) \/ (lookup x t2 = NONE))``,
  fs [lookup_inter] \\ REPEAT BasicProvers.CASE_TAC);

val LAST_N_LENGTH = store_thm("LAST_N_LENGTH",
  ``!xs. LAST_N (LENGTH xs) xs = xs``,
  fs [LAST_N_def] \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [TAKE_LENGTH_ID] \\ fs []);

val LAST_N_TL = store_thm("LAST_N_TL",
  ``n < LENGTH xs ==>
    (LAST_N (n+1) (x::xs) = LAST_N (n+1) xs)``,
  fs [LAST_N_def] \\ REPEAT STRIP_TAC
  \\ `n+1 <= LENGTH (REVERSE xs)` by (fs [] \\ DECIDE_TAC)
  \\ imp_res_tac TAKE_APPEND1 \\ fs []);

val pEval_locals_LN_lemma = prove(
  ``!c s.
      FST (pEval (c,s)) <> NONE /\
      FST (pEval (c,s)) <> SOME Error ==>
      ((SND (pEval (c,s))).locals = LN) \/
      ?t. FST (pEval (c,s)) = SOME (Exception t)``,
  recInduct pEval_ind \\ REPEAT STRIP_TAC \\ fs [pEval_def]
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [call_env_def,fromList_def])
  \\ SRW_TAC [] [] \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val pEval_locals_LN = store_thm("pEval_locals_LN",
  ``!c s res t.
      (pEval (c,s) = (res,t)) /\ res <> NONE /\ res <> SOME Error ==>
      (t.locals = LN) \/ ?t. res = SOME (Exception t)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL pEval_locals_LN_lemma) \\ fs []);

val LAST_N_LEMMA = prove(
  ``(LAST_N (LENGTH xs + 1 + 1) (x::y::xs) = x::y::xs) /\
    (LAST_N (LENGTH xs + 1) (x::xs) = x::xs)``,
  MP_TAC (Q.SPEC `x::y::xs` LAST_N_LENGTH)
  \\ MP_TAC (Q.SPEC `x::xs` LAST_N_LENGTH) \\ fs [ADD1]);

val PUSH_EXISTS_CONJ = METIS_PROVE [] ``(?x. P x /\ Q) <=> (?x. P x) /\ Q``

val IMP_IMP = save_thm("IMP_IMP",
  METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``);

local
  val get_vars_with_stack = prove(
    ``!args s. (s.locals = t.locals) ==>
               (get_vars args s = get_vars args t)``,
    Induct \\ fs [get_vars_def,get_var_def])
  val get_vars_with_stack_rwt = prove(
    ``(get_vars args (s with stack := xs) = get_vars args s)``,
    MATCH_MP_TAC get_vars_with_stack \\ fs [])
  val tac =
    fs [pEval_def]
    \\ REPEAT (BasicProvers.FULL_CASE_TAC
          \\ fs [call_env_def,fromList_def,set_var_def,cut_state_opt_def,
                 pEvalOp_def,pEvalOpSpace_def,consume_space_def,add_space_def,
                 bvl_to_bvp_def,cut_state_def,cut_env_def,dec_clock_def,
                 jump_exc_def,get_var_def,push_exc_def,push_env_def,set_var_def,
                 get_vars_with_stack_rwt])
    \\ SRW_TAC [] []
in
  val pEval_stack_swap = store_thm("pEval_stack_swap",
    ``!c s.
        case pEval (c,s) of
        | (SOME Error,s1) => T
        | (SOME TimeOut,s1) => (s1.stack = []) /\
                      (!xs. (LENGTH s.stack = LENGTH xs) ==>
                              pEval (c,s with stack := xs) =
                                (SOME TimeOut,s1))
        | (SOME (Exception t),s1) =>
              (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                    (s2.stack = s1.stack) /\ (s2.handler = s1.handler) /\
                    (!xs s7. (jump_exc (s with stack := xs) = SOME s7) /\
                             (LENGTH s.stack = LENGTH xs) ==>
                             (pEval (c,s with stack := xs) =
                                (SOME (Exception t),
                                 s1 with <| stack := s7.stack ;
                                            handler := s7.handler ;
                                            locals := s7.locals |>))))
        | (res,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler) /\
                      (!xs. (LENGTH s.stack = LENGTH xs) ==>
                              pEval (c,s with stack := xs) =
                                (res, s1 with stack := xs))``,
    recInduct pEval_ind \\ REPEAT STRIP_TAC
    THEN1 tac THEN1 tac
    THEN1 (* Assign *)
     (tac \\ fs [bvp_to_bvl_def]
      \\ Q.MATCH_ASSUM_RENAME_TAC
           `get_vars args (s with locals := mk_wf (inter s.locals x2)) = SOME vs` []
      \\ `get_vars args (s with <|locals := mk_wf (inter s.locals x2); stack := xs|>) =
          get_vars args (s with locals := mk_wf (inter s.locals x2))` by
            (MATCH_MP_TAC get_vars_with_stack \\ fs [] \\ NO_TAC) \\ fs [])
    THEN1 tac THEN1 tac THEN1 (tac \\ tac) THEN1 tac
    THEN1 (* Seq *)
     (fs [pEval_def]
      \\ Cases_on `pEval (c1,s)` \\ fs [LET_DEF]
      \\ Cases_on `pEval (c2,r)` \\ fs [LET_DEF]
      \\ Cases_on `q = NONE` \\ fs [] \\ Cases_on `q'` \\ fs []
      \\ TRY (Cases_on `x`) \\ fs [jump_exc_def]
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []
      \\ POP_ASSUM MP_TAC
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs []
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] [])
    THEN1 (* Handle *)
     (Cases_on `cut_env ns1 s.locals` \\ fs [pEval_def]
      \\ Cases_on `cut_env ns2 s.locals` \\ fs []
      \\ Cases_on `pEval (c1,push_exc x x' s)` \\ fs []
      \\ Cases_on `q` \\ fs [] THEN1
       (Cases_on `get_var v r` \\ fs [] \\ Cases_on `pop_exc r` \\ fs []
        \\ REWRITE_TAC [CONJ_ASSOC] \\ STRIP_TAC THEN1
         (SRW_TAC [] [] \\ fs [set_var_def,push_exc_def,pop_exc_def]
          \\ REV_FULL_SIMP_TAC (srw_ss()) [] \\ fs [] \\ SRW_TAC [] [])
        \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM (MP_TAC o
             Q.SPEC `(push_exc x x' (s with stack := xs)).stack`)
        \\ `push_exc x x' s with
              stack := (push_exc x x' (s with stack := xs)).stack
             = push_exc x x' (s with stack := xs)` by
                (fs [push_exc_def,bvp_state_explode] \\ NO_TAC)
        \\ fs [get_var_def,pop_exc_def,push_exc_def,set_var_def]
        \\ REPEAT STRIP_TAC \\ fs [bvp_state_explode]
        \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs [] \\ SRW_TAC [] [])
      \\ Cases_on `x''` \\ fs []
      \\ Cases_on `pEval (c2,set_var n b r)` \\ fs []
      \\ Cases_on `q` \\ fs []
      \\ TRY (`(set_var n b r).stack = s.stack /\
          (set_var n b r).handler = s.handler` by
         (SRW_TAC [] []
          \\ fs [set_var_def,push_exc_def,pop_exc_def,jump_exc_def]
          \\ fs [LAST_N_LEMMA] \\ SRW_TAC [] []
          \\ REV_FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)) \\ fs []
      \\ TRY (Cases_on `x''`) \\ fs []
      \\ REPEAT STRIP_TAC \\ TRY
       (Q.PAT_ASSUM `!xx. bbb` (MP_TAC o
             Q.SPEC `(push_exc x x' (s with stack := xs)).stack`)
        \\ `push_exc x x' s with
                stack := (push_exc x x' (s with stack := xs)).stack
               = push_exc x x' (s with stack := xs)` by
                 (fs [push_exc_def,bvp_state_explode] \\ NO_TAC)
        \\ fs [jump_exc_def,push_exc_def,LAST_N_LEMMA]
        \\ REPEAT STRIP_TAC \\ fs [] \\ fs [bvp_state_explode]
        \\ Q.PAT_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
        \\ fs [LAST_N_LEMMA] \\ SRW_TAC [] [] \\ fs []
        \\ `(set_var n b r).stack = r.stack` by fs [set_var_def] \\ fs []
        \\ `set_var n b (r with <| locals := r.locals; stack := xs;
                                     handler := r.handler|>) =
            (set_var n b r) with stack := xs` by
               fs [set_var_def,bvp_state_explode] \\ fs [] \\ NO_TAC)
      \\ REWRITE_TAC [CONJ_ASSOC] \\ fs [PUSH_EXISTS_CONJ]
      \\ STRIP_TAC THEN1
       (fs [jump_exc_def,set_var_def]
        \\ REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ SRW_TAC [] [] \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `!xx. bbb` (MP_TAC o
             Q.SPEC `(push_exc x x' (s with stack := xs)).stack`)
      \\ `push_exc x x' s with
                stack := (push_exc x x' (s with stack := xs)).stack
               = push_exc x x' (s with stack := xs)` by
                 (fs [push_exc_def,bvp_state_explode] \\ NO_TAC) \\ fs []
      \\ SIMP_TAC std_ss [Once push_exc_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ fs [LAST_N_LEMMA]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      THEN1 (fs [push_exc_def] \\ DECIDE_TAC)
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `r.handler = s.handler /\ r.stack = s.stack` by fs [set_var_def]
      \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`xs`,`s2'
           with <| locals := s7.locals ;
                   stack := s7.stack ;
                   handler := s7.handler |>`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs [jump_exc_def]
        \\ REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ SRW_TAC [] [] \\ fs [bvp_state_explode,set_var_def]
        \\ Q.PAT_ASSUM `xxx = SOME s2'` MP_TAC
        \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] []
        \\ SRW_TAC [] [])
      \\ `r.locals = x'` by ALL_TAC THEN1
       (`LENGTH xs = LENGTH s.stack` by fs []
        \\ fs [jump_exc_def,push_exc_def,LAST_N_LEMMA]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `set_var n b
           (r with <|locals := x'; stack := xs; handler := s.handler|>) =
          set_var n b r with stack := xs` by
             (fs [bvp_state_explode,set_var_def] \\ NO_TAC) \\ fs [])
    THEN1 (* If *)
     (fs [pEval_def]
      \\ Cases_on `pEval (g,s)` \\ fs [LET_DEF]
      \\ Cases_on `pEval (c1,r)` \\ fs [LET_DEF]
      \\ Cases_on `pEval (c2,r)` \\ fs [LET_DEF]
      \\ REVERSE (Cases_on `q`) \\ fs []
      THEN1 (Cases_on `x` \\ fs [] \\ REPEAT STRIP_TAC
             \\ RES_TAC \\ fs [])
      \\ Cases_on `get_var n r` \\ fs []
      \\ Cases_on `x = bool_to_val T` \\ fs [get_var_def] THEN1
       (Cases_on `q'` \\ fs []
        \\ Cases_on `x'` \\ fs [jump_exc_def]
        \\ REPEAT BasicProvers.CASE_TAC \\ fs [jump_exc_def]
        \\ SRW_TAC [] [bvp_state_explode] \\ fs [set_var_def]
        \\ POP_ASSUM MP_TAC
        \\ REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs []
        \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] [])
      \\ Cases_on `x = bool_to_val F` \\ fs [get_var_def] THEN1
       (Cases_on `q''` \\ fs []
        \\ Cases_on `x'` \\ fs [jump_exc_def]
        \\ REPEAT BasicProvers.CASE_TAC \\ fs [jump_exc_def]
        \\ SRW_TAC [] [bvp_state_explode] \\ fs [set_var_def]
        \\ POP_ASSUM MP_TAC
        \\ REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs []
        \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] []))
    THEN1 (* Call *)
     (fs [pEval_def]
      \\ Cases_on `s.clock = 0` \\ fs []
      \\ Cases_on `get_vars args s` \\ fs []
      \\ Cases_on `find_code dest x s.code` \\ fs []
      \\ TRY (fs [call_env_def] \\ NO_TAC)
      \\ Cases_on `x'` \\ fs []
      \\ Cases_on `ret` \\ fs [get_vars_with_stack_rwt] THEN1
       (REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ fs [call_env_def,dec_clock_def,jump_exc_def]
        \\ REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ SRW_TAC [] [] \\ fs []
        \\ Q.PAT_ASSUM `xxx = SOME s7` MP_TAC
        \\ REPEAT BasicProvers.CASE_TAC \\ fs []
        \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs [])
      \\ fs [get_vars_with_stack_rwt]
      \\ Cases_on `x'` \\ fs []
      \\ Cases_on `cut_env r' s.locals` \\ fs []
      \\ Cases_on `pEval (r,call_env q (push_env x' (dec_clock s)))` \\ fs []
      \\ Cases_on `q''` \\ fs []
      \\ Cases_on `x''` \\ fs []
      \\ fs [pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
      \\ fs [jump_exc_def]
      \\ Cases_on `s.handler = LENGTH s.stack` \\ fs [LAST_N_LEMMA]
      THEN1 (REPEAT (BasicProvers.FULL_CASE_TAC \\ fs []))
      \\ `s.handler < LENGTH s.stack` by DECIDE_TAC \\ fs []
      \\ IMP_RES_TAC LAST_N_TL \\ fs []
      \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
      \\ SRW_TAC [] [] \\ fs []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPECL [`Env x'::xs`,
           `s7 with clock := s7.clock - 1`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC LAST_N_TL \\ fs []
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ fs [bvp_state_explode]))
end

val pEval_stack = store_thm("pEval_stack",
  ``!c s.
      case pEval (c,s) of
      | (SOME Error,s1) => T
      | (SOME TimeOut,s1) => (s1.stack = [])
      | (SOME (Exception t),s1) =>
            (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                  (s2.stack = s1.stack) /\ (s2.handler = s1.handler))
      | (_,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler)``,
  REPEAT STRIP_TAC \\ ASSUME_TAC (SPEC_ALL pEval_stack_swap)
  \\ REPEAT BasicProvers.CASE_TAC \\ fs []);

val list_insert_def = Define `
  (list_insert [] t = t) /\
  (list_insert (n::ns) t = list_insert ns (insert n () t))`;

val domain_list_insert = store_thm("domain_list_insert",
  ``!xs x t.
      x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain t``,
  Induct \\ fs [list_insert_def] \\ METIS_TAC []);

val lookup_inter_alt = store_thm("lookup_inter_alt",
  ``lookup x (inter t1 t2) =
      if x IN domain t2 then lookup x t1 else NONE``,
  fs [lookup_inter,domain_lookup]
  \\ Cases_on `lookup x t2` \\ fs [] \\ Cases_on `lookup x t1` \\ fs []);

val pEvalOp_IMP = store_thm("pEvalOp_IMP",
  ``(pEvalOp op args s1 = SOME (v,s2)) ==>
    (s1.handler = s2.handler) /\ (s1.stack = s2.stack) /\ (s1.locals = s2.locals)``,
  fs [pEvalOp_def,pEvalOpSpace_def,bvp_to_bvl_def,bvl_to_bvp_def,consume_space_def]
  \\ REPEAT (BasicProvers.CASE_TAC \\ fs [])
  \\ SRW_TAC [] [] \\ SRW_TAC [] []);

val get_vars_IMP_domain = store_thm("get_vars_IMP_domain",
  ``!args x s vs. MEM x args /\ (get_vars args s = SOME vs) ==>
                  x IN domain s.locals``,
  Induct \\ fs [get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ fs [domain_lookup]);

val EVERY_get_vars = store_thm("EVERY_get_vars",
  ``!args s1 s2.
      EVERY (\a. lookup a s1.locals = lookup a s2.locals) args ==>
      (get_vars args s1 = get_vars args s2)``,
  Induct \\ fs [get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val _ = export_theory();
