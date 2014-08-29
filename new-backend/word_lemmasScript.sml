open HolKernel Parse boolLib bossLib miscLib word_langTheory
open listTheory sptreeTheory pred_setTheory pairTheory optionTheory
(*TODO: remove the last_n lemmas*)
open bvp_lemmasTheory

val _ = new_theory "word_lemmas";

(*Stacks look the same except for the keys (e.g. recolored and in order)*)
val s_frame_val_eq_def = Define`
  (s_frame_val_eq (StackFrame ls NONE) (StackFrame ls' NONE)
     <=> MAP SND ls = MAP SND ls') /\
  (s_frame_val_eq (StackFrame ls (SOME y)) (StackFrame ls' (SOME y'))
     <=> MAP SND ls = MAP SND ls' /\ y=y') /\
  (s_frame_val_eq _ _ = F)`

val s_val_eq_def = Define`
  (s_val_eq [] [] = T) /\
  (s_val_eq (x::xs) (y::ys) = (s_val_eq xs ys /\
                                    s_frame_val_eq x y)) /\
  (s_val_eq _ _ = F)`

(*Stacks look the same except for the values (e.g. result of gc)*)
val s_frame_key_eq_def = Define`
  (s_frame_key_eq (StackFrame ls NONE) (StackFrame ls' NONE)
     <=> MAP FST ls = MAP FST ls') /\
  (s_frame_key_eq (StackFrame ls (SOME y)) (StackFrame ls' (SOME y'))
     <=> MAP FST ls = MAP FST ls' /\ y=y') /\
  (s_frame_key_eq _ _ = F)`

val s_key_eq_def = Define`
  (s_key_eq [] [] = T) /\
  (s_key_eq (x::xs) (y::ys) = (s_key_eq xs ys /\
                                    s_frame_key_eq x y)) /\
  (s_key_eq _ _ = F)`

(*
EVAL ``s_val_eq [] []``
EVAL ``s_key_eq [] []``
*)

(*Reflexive*)
val s_key_eq_refl = prove(
  ``!ls .s_key_eq ls ls = T``,
   Induct >> rw[s_key_eq_def]>>
   Cases_on`h`>> Cases_on`o'`>>rw[s_frame_key_eq_def])

val s_val_eq_refl = prove(
  ``!ls.s_val_eq ls ls = T``,
  Induct >> rw[s_val_eq_def]>>
  Cases_on`h`>> Cases_on`o'`>>rw[s_frame_val_eq_def])

(*transitive*)
val s_frame_key_eq_trans = prove(
  ``!a b c. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
            s_frame_key_eq a c``,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  fs[s_frame_key_eq_def])

val s_key_eq_trans = prove(
  ``!a b c. s_key_eq a b /\ s_key_eq b c ==>
            s_key_eq a c``,
  Induct>>
  Cases_on`b`>>Cases_on`c`>>fs[s_key_eq_def]>>
  rw[]>>metis_tac[s_frame_key_eq_trans])

val s_frame_val_eq_trans = prove(
  ``!a b c. s_frame_val_eq a b /\ s_frame_val_eq b c ==>
            s_frame_val_eq a c``,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  fs[s_frame_val_eq_def])

val s_val_eq_trans = prove(
  ``!a b c. s_val_eq a b /\ s_val_eq b c ==>
            s_val_eq a c``,
  Induct>>
  Cases_on`b`>>Cases_on`c`>>fs[s_val_eq_def]>>
  rw[]>>metis_tac[s_frame_val_eq_trans])


(*Symmetric*)
val s_frame_key_eq_sym = prove(
  ``!a b. s_frame_key_eq a b <=> s_frame_key_eq b a``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>fs[s_frame_key_eq_def,EQ_SYM_EQ])

val s_key_eq_sym = prove(
  ``!a b. s_key_eq a b <=> s_key_eq b a``,
  Induct>> Cases_on`b`>>fs[s_key_eq_def]>>
  strip_tac>>metis_tac[s_frame_key_eq_sym])

val s_frame_val_eq_sym = prove(
   ``!a b. s_frame_val_eq a b <=> s_frame_val_eq b a``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>fs[s_frame_val_eq_def,EQ_SYM_EQ])

val s_val_eq_sym = prove(
  ``!a b. s_val_eq a b <=> s_val_eq b a``,
  Induct>> Cases_on`b`>>fs[s_val_eq_def]>>
  strip_tac>>metis_tac[s_frame_val_eq_sym])

val s_frame_val_and_key_eq = prove(
  ``!s t. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>
  fs[s_frame_val_eq_def,s_frame_key_eq_def,LIST_EQ_MAP_PAIR])

val dec_stack_stack_key_eq = prove(
  ``!wl st st'. dec_stack wl st = SOME st' ==> s_key_eq st st'``,
  ho_match_mp_tac dec_stack_ind>>rw[dec_stack_def]>>
  fs[s_key_eq_def]>>
  first_x_assum mp_tac>>BasicProvers.FULL_CASE_TAC>>
  fs[s_key_eq_def]>>rfs[]>>
  rw[]>> fs[s_key_eq_def]>>
  Cases_on`handler`>>fs[MAP_ZIP,s_frame_key_eq_def])

(*wGC preserves the stack_key relation*)
val wGC_s_key_eq = prove(
  ``!s x. wGC s = SOME x ==> s_key_eq s.stack x.stack``,
  rw[wGC_def] >>fs[LET_THM]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  fs[word_state_component_equality]>>rfs[])

val s_val_eq_enc_stack = prove(
  ``!st st'. s_val_eq st st' ==> enc_stack st = enc_stack st'``,
  Induct>>Cases_on`st'`>>fs[s_val_eq_def]>>
  Cases_on`h`>>Cases_on`h'`>>Cases_on`o''`>>Cases_on`o'`>>
  fs[s_frame_val_eq_def,enc_stack_def])

val s_val_eq_dec_stack = prove(
  ``!q st st' x. s_val_eq st st' /\ dec_stack q st = SOME x ==>
    ?y. dec_stack q st' = SOME y /\ s_val_eq x y``,
   ho_match_mp_tac dec_stack_ind >> rw[] >>
   Cases_on`st'`>>fs[s_val_eq_def,s_val_eq_refl]>>
   Cases_on`h`>>fs[dec_stack_def]>>
   pop_assum mp_tac>>CASE_TAC >>
   first_x_assum(qspecl_then [`t`,`x'`] assume_tac)>> rfs[]>>
   strip_tac>>pop_assum (SUBST1_TAC o SYM)>>
   fs[s_frame_val_eq_def,s_val_eq_def]>>
   Cases_on`handler`>>Cases_on`o'`>>
   fs[s_frame_val_eq_def,MAP_ZIP,ZIP_MAP]>>
   `LENGTH l = LENGTH l'` by metis_tac[LENGTH_MAP]>>fs[MAP_ZIP])

(*wGC succeeds on all stacks related by stack_val and there are relations
  in the result*)
val wGC_s_val_eq = prove(
  ``!s x st y. s_val_eq s.stack st /\ 
             wGC s = SOME y ==> 
      ?z. wGC (s with stack := st) = SOME (y with stack := z) /\
          s_val_eq y.stack z /\ s_key_eq z st``,
  rw[wGC_def]>>fs[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>fs[]>>
  qpat_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> fs[]>>
  strip_tac>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`y'`>>fs[word_state_component_equality]>>rfs[])

(*pushing and popping maintain the stack_key relation*)
val push_env_pop_env_s_key_eq = prove(
  ``!s t x b. s_key_eq (push_env x b s).stack t.stack ==>
              ?y. (pop_env t = SOME y /\
                   s_key_eq s.stack y.stack)``,
  rw[push_env_def]>>fs[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
  fs[s_key_eq_def,pop_env_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[])

val get_vars_stack_swap = prove(
  ``!l s t. s.locals = t.locals ==>
    get_vars l s = get_vars l t``,
  Induct>>fs[get_vars_def,get_var_def]>>
  rw[]>> BasicProvers.EVERY_CASE_TAC>>
  metis_tac[NOT_NONE_SOME,SOME_11])

val s_val_eq_length = prove(
  ``!s t. s_val_eq s t ==> LENGTH s = LENGTH t``,
  Induct>>Cases>>fs[s_val_eq_def,LENGTH]>>
  Cases>>fs[s_val_eq_def])

val s_key_eq_length = prove(
  ``!s t. s_key_eq s t ==> LENGTH s = LENGTH t``,
  Induct>>Cases>>fs[s_key_eq_def,LENGTH]>>
  Cases>>fs[s_key_eq_def])

val s_val_eq_APPEND = prove(
  ``!s t x y. (s_val_eq s t /\ s_val_eq x y)==> s_val_eq (s++x) (t++y)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[]>>fs[s_val_eq_def])

val s_val_eq_REVERSE = prove(
  ``!s t. s_val_eq s t ==> s_val_eq (REVERSE s) (REVERSE t)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[]>>fs[s_val_eq_def,s_val_eq_APPEND])

val s_val_eq_TAKE = prove(
  ``!s t n. s_val_eq s t ==> s_val_eq (TAKE n s) (TAKE n t)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[]>>fs[s_val_eq_def]>>IF_CASES_TAC>>
  fs[s_val_eq_def])

val s_val_eq_LAST_N = prove(
  ``!s t n. s_val_eq s t 
    ==> s_val_eq (LAST_N n s) (LAST_N n t)``,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  rw[bvpTheory.LAST_N_def]>>fs[s_val_eq_def]>>
  `s_val_eq [x] [y]` by fs[s_val_eq_def]>>
  `s_val_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    fs[s_val_eq_APPEND,s_val_eq_REVERSE]>>
  IMP_RES_TAC s_val_eq_TAKE>> 
  metis_tac[s_val_eq_REVERSE])

val s_key_eq_APPEND = prove(
  ``!s t x y. (s_key_eq s t /\ s_key_eq x y)==> s_key_eq (s++x) (t++y)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>fs[s_key_eq_def])

val s_key_eq_REVERSE = prove(
  ``!s t. s_key_eq s t ==> s_key_eq (REVERSE s) (REVERSE t)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>fs[s_key_eq_def,s_key_eq_APPEND])

val s_key_eq_TAKE = prove(
  ``!s t n. s_key_eq s t ==> s_key_eq (TAKE n s) (TAKE n t)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>fs[s_key_eq_def]>>IF_CASES_TAC>>
  fs[s_key_eq_def])

val s_key_eq_LAST_N = prove(
  ``!s t n. s_key_eq s t 
    ==> s_key_eq (LAST_N n s) (LAST_N n t)``,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[bvpTheory.LAST_N_def]>>fs[s_key_eq_def]>>
  `s_key_eq [x] [y]` by fs[s_key_eq_def]>>
  `s_key_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    fs[s_key_eq_APPEND,s_key_eq_REVERSE]>>
  IMP_RES_TAC s_key_eq_TAKE>> 
  metis_tac[s_key_eq_REVERSE])
 
val s_key_eq_tail = prove(
 ``!a b c d. s_key_eq (a::b) (c::d) ==> s_key_eq b d``,
  fs[s_key_eq_def])

val s_val_eq_tail = prove(
 ``!a b c d. s_val_eq (a::b) (c::d) ==> s_val_eq b d``,
  fs[s_val_eq_def])

val s_key_eq_LAST_N_exists = prove(
  ``!s t n e y xs. s_key_eq s t /\
    LAST_N n s = StackFrame e (SOME y)::xs
    ==> ?e' ls. LAST_N n t = StackFrame e' (SOME y)::ls
        /\ MAP FST e' = MAP FST e
        /\ s_key_eq xs ls``,
   rpt strip_tac>>
   IMP_RES_TAC s_key_eq_LAST_N>>
   first_x_assum (qspec_then `n` assume_tac)>> rfs[]>>
   Cases_on`LAST_N n t`>>
   fs[s_key_eq_def]>>
   Cases_on`h`>>Cases_on`o'`>>fs[s_frame_key_eq_def])

val s_val_eq_LAST_N_exists = prove(
  ``!s t n e y xs. s_val_eq s t /\
   LAST_N n s = StackFrame e (SOME y)::xs
    ==> ?e' ls. LAST_N n t = StackFrame e' (SOME y)::ls
       /\ MAP SND e' = MAP SND e
       /\ s_val_eq xs ls``,
  rpt strip_tac>>
  IMP_RES_TAC s_val_eq_LAST_N>>
  first_x_assum (qspec_then `n` assume_tac)>> rfs[]>>
  Cases_on`LAST_N n t`>>
  fs[s_val_eq_def]>>
  Cases_on`h`>>Cases_on`o'`>>fs[s_frame_val_eq_def])


val LAST_N_LENGTH_cond = prove(
  ``!n xs. n = LENGTH xs ==> LAST_N n xs =xs``,
  metis_tac[LAST_N_LENGTH] )

val handler_eq = prove(
  ``x with handler := x.handler = x``, fs[word_state_component_equality])

(*Stack is irrelevant to word_exp*)
val word_exp_stack_swap = prove(
  ``!s e st. word_exp s e = word_exp (s with stack:=st) e``,
  ho_match_mp_tac word_exp_ind>>
  rw[word_exp_def]>-
  (first_x_assum(qspec_then `st` SUBST1_TAC)>>
  BasicProvers.EVERY_CASE_TAC>>fs[mem_load_def])>-
  (`ws = ws'` by
  (bossLib.UNABBREV_ALL_TAC>> 
  fs[MEM_MAP,EVERY_MEM,MAP_EQ_f])>>fs[])>>
  BasicProvers.EVERY_CASE_TAC>>fs[])


(*Stack swap theorem for wEval*)
val wEval_stack_swap = store_thm("wEval_stack_swap",
  ``!c s.
      case wEval (c,s) of
      | (SOME Error,s1) => T
      | (SOME TimeOut,s1) => T (*probably needs a cond here*)
      | (SOME NotEnoughSpace,s1) => T (*probably needs a cond here*)
      | (SOME (Exception t),s1) =>
            (s.handler<LENGTH s.stack) /\ (*precondition for jump_exc*)
            (?e n ls lss. 
                (LAST_N (s.handler+1) s.stack = StackFrame e (SOME n)::ls) /\
                (MAP FST e = MAP FST lss /\ 
                   s1.locals = fromAList lss) /\
                (s_key_eq s1.stack ls) /\ (s1.handler = n) /\
                (!xs e' ls'. 
                           (LAST_N (s.handler+1) xs = 
                             StackFrame e' (SOME n):: ls') /\
                           (s_val_eq s.stack xs) ==> (*this implies n=n'*)
                           ?st locs.
                           (wEval (c,s with stack := xs) =
                              (SOME (Exception t),
                               s1 with <| stack := st;
                                          handler := n;
                                          locals := locs |>) /\
                            (?lss'. MAP FST e' = MAP FST lss' /\
                               locs = fromAList lss' /\
                               MAP SND lss = MAP SND lss')/\
                            (*set (MAP FST e') = domain locs /\*)
                            (*sort s1.locals by MAP FST e and 
                              sort locs by MAP FST e'
                              their MAP SND should be the same
                              needs e and e' to be distinct*)
                            (*MAP SND (sort e s1.locals) = 
                            MAP SND (sort e' locs)*)
                            s_val_eq s1.stack st /\ s_key_eq ls' st)))
      | (res,s1) => (s_key_eq s.stack s1.stack) /\ (s1.handler = s.handler) /\
                    (!xs. s_val_eq s.stack xs ==>
                          ?st. wEval (c,s with stack := xs) =
                                (res, s1 with stack := st)  /\ 
                                s_val_eq s1.stack st /\
                                s_key_eq xs st)``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>-
  (*Skip*)
  (fs[wEval_def,s_key_eq_refl]>>rw[]>>HINT_EXISTS_TAC>>fs[s_key_eq_refl])>-
  (*Alloc*) 
  (fs[wEval_def,wAlloc_def]>>BasicProvers.EVERY_CASE_TAC>>
  IMP_RES_TAC wGC_s_key_eq>>
  IMP_RES_TAC push_env_pop_env_s_key_eq>>
  `s_key_eq s.stack y.stack` by fs[set_store_def]>>
  fs[SOME_11]>>rw[]>-
    (qpat_assum`wGC a = SOME b` mp_tac>>
    qpat_assum`pop_env a = b` mp_tac>>
    fs[pop_env_def,wGC_def,push_env_def,set_store_def
      ,LET_THM,env_to_list_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs[s_key_eq_def,s_frame_key_eq_def]>>
    rw[]>>fs[])>>
  BasicProvers.FULL_CASE_TAC>>fs[get_var_def]>>
  BasicProvers.FULL_CASE_TAC>>
  Q.MATCH_ASSUM_ABBREV_TAC `wGC a = y`>>
  Q.MATCH_ASSUM_ABBREV_TAC `wGC b = SOME x'`>>
  `s_val_eq b.stack a.stack /\ b with stack:=a.stack = a` by 
    (fs[push_env_def,LET_THM,env_to_list_def,set_store_def]>>
    bossLib.UNABBREV_ALL_TAC>>
    fs[s_val_eq_def,s_frame_val_eq_def,s_val_eq_sym])>>
  Q.UNABBREV_TAC `y`>>
  IMP_RES_TAC wGC_s_val_eq>>rfs[]>>
  Q.UNABBREV_TAC`b`>>Q.UNABBREV_TAC`a`>>
  fs[push_env_def,set_store_def,LET_THM,env_to_list_def]>>
  Cases_on`x'.stack`>>
  Cases_on`z'`>>fs[s_key_eq_def,word_state_component_equality]>>
  `h=h'` by (
    fs[s_val_eq_def,s_key_eq_def]>> 
    `s_frame_key_eq h' h` by metis_tac[s_frame_key_eq_trans]>>
    metis_tac[s_frame_val_and_key_eq,s_frame_key_eq_sym])>>
  fs[pop_env_def] >>Cases_on`h'`>>Cases_on`o'`>>fs[s_frame_key_eq_def]>>
  fs[word_state_component_equality]>>
  fs[has_space_def]>>
  Q.EXISTS_TAC`t'`>>
  fs[word_state_component_equality]>>
  metis_tac[s_val_eq_def,s_key_eq_sym])>-
  (*Move*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[set_vars_def,s_key_eq_refl]>>
  rpt strip_tac>>HINT_EXISTS_TAC>>
  `s.locals = (s with stack := xs).locals` by
    fs[word_state_component_equality]>>
  IMP_RES_TAC get_vars_stack_swap>>fs[s_key_eq_refl])>-
  (*Assign*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  rpt strip_tac>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Set*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[set_store_def,s_key_eq_refl]>>
  rpt strip_tac>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Store*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[mem_store_def,word_state_component_equality,s_key_eq_refl]>>
  rpt strip_tac>>HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,get_var_def,
     word_state_component_equality])>-
  (*Tick*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>fs[dec_clock_def,s_key_eq_refl]>>
  rpt strip_tac>>Q.EXISTS_TAC`xs`>>fs[s_key_eq_refl])>-
  (*Seq*)
  (fs[wEval_def]>>
  Cases_on`wEval(c,s)`>>
  fs[LET_THM]>>
  IF_CASES_TAC>-
    (*q = NONE*)
    (BasicProvers.EVERY_CASE_TAC>>
    fs[s_key_eq_trans]>> TRY
      (qho_match_abbrev_tac`A ∧ ∀xs. P xs` >> unabbrev_all_tac >> simp[] >>
      CONJ_TAC>-metis_tac[s_key_eq_trans]>>
      rpt strip_tac>>
      first_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>
      first_x_assum(qspec_then `st` assume_tac)>>rfs[]>> 
      HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>>
      ASSUME_TAC (INST_TYPE [``:'b``|->``:'a``]s_key_eq_LAST_N_exists)>>
      (*get the result stack from first eval*)
      IMP_RES_TAC s_key_eq_length>>fs[]>>
      first_x_assum(qspecl_then [`r.stack`,`s.stack`,`s.handler+1`,`e`,
        `r'.handler`,`ls`] assume_tac)>>
      `s_key_eq r.stack s.stack` by rw[s_key_eq_sym]>>
      fs[]>>rfs[]>>Q.EXISTS_TAC`lss`>>
      simp[]>>CONJ_TAC>-metis_tac[s_key_eq_trans]>>
      rpt strip_tac>>
      first_x_assum(qspec_then `xs` assume_tac)>>
      rfs[]>>
      IMP_RES_TAC s_key_eq_LAST_N_exists>>
      last_x_assum(qspecl_then [`st`,`e'''''''`,`ls'''''''`] assume_tac)>>
      rfs[]>>
      HINT_EXISTS_TAC>>
      Q.EXISTS_TAC`fromAList lss'`>>
      fs[]>>
      CONJ_TAC>- (Q.EXISTS_TAC`lss'`>>fs[])>>
      metis_tac[s_key_eq_trans])>>
    Cases_on`q`>>fs[]>>
    Cases_on`x`>>fs[]>>
    rpt strip_tac>-
      (first_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>HINT_EXISTS_TAC>>
      fs[])>>
    Q.EXISTS_TAC`lss`>>fs[]>>
    rpt strip_tac>>
    first_x_assum (qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>>fs[]>>
    Q.EXISTS_TAC`lss'`>>fs[])>-
  (*Return*)
  (fs[wEval_def]>> BasicProvers.EVERY_CASE_TAC>>
  fs[call_env_def,s_key_eq_refl]>>
  rpt strip_tac>>fs[get_var_def]>>HINT_EXISTS_TAC>>
  fs[word_state_component_equality,s_key_eq_refl])>-
  (*Raise*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>fs[get_var_def,jump_exc_def]>>
  qpat_assum `(a = SOME x)` mp_tac>>
  BasicProvers.EVERY_CASE_TAC>>fs[word_state_component_equality]>>
  strip_tac>> Q.EXISTS_TAC `l`>>
  fs[EQ_SYM_EQ,s_key_eq_refl]>>
  rpt strip_tac>>
  IMP_RES_TAC s_val_eq_length>>fs[EQ_SYM_EQ,word_state_component_equality]>>
  fs[s_key_eq_refl]>>
  `s.handler + 1<= LENGTH s.stack` by metis_tac[arithmeticTheory.LESS_OR,arithmeticTheory.ADD1]>>
  rpt (qpat_assum `a = LAST_N b c` (ASSUME_TAC o SYM))>>
  IMP_RES_TAC s_val_eq_LAST_N>>
  first_x_assum(qspec_then `s.handler+1` assume_tac)>>rfs[]>>
  IMP_RES_TAC s_val_eq_tail>>
  fs[s_val_eq_def,s_frame_val_eq_def]>>
  Q.EXISTS_TAC`e'`>>fs[])>-
  (*If*)
  (fs[wEval_def]>>BasicProvers.FULL_CASE_TAC>>
  Cases_on`q`>> fs[]>-
    (*NONE*)
    (ntac 3 BasicProvers.FULL_CASE_TAC>>fs[]>>
      rpt (BasicProvers.EVERY_CASE_TAC>>
      fs[s_key_eq_trans]>> TRY
      (qho_match_abbrev_tac`A ∧ ∀xs. P xs` >> unabbrev_all_tac >> simp[] >>
      CONJ_TAC>-metis_tac[s_key_eq_trans]>>
      rpt strip_tac>>
      last_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>
      fs[get_var_def]>>
      first_x_assum(qspec_then `st` assume_tac)>>rfs[]>> 
      HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>>
      ASSUME_TAC (INST_TYPE [``:'b``|->``:'a``]s_key_eq_LAST_N_exists)>>
      IMP_RES_TAC s_key_eq_length>>fs[]>>
      first_x_assum(qspecl_then [`r.stack`,`s.stack`,`s.handler+1`,`e`,
        `r'.handler`,`ls`] assume_tac)>>
      `LENGTH s.stack = LENGTH r.stack` by fs[s_key_eq_length]>>
      CONJ_TAC>- metis_tac[EQ_SYM_EQ]>>
      `s_key_eq r.stack s.stack` by metis_tac[s_key_eq_sym]>>
      IMP_RES_TAC s_key_eq_LAST_N_exists>>fs[]>>
      qpat_assum `a.handler = b.handler` (ASSUME_TAC o SYM)>>
      fs[]>>
      Q.EXISTS_TAC`lss`>>fs[]>>
      CONJ_TAC>-metis_tac[s_key_eq_trans]>>
      rpt strip_tac>>
      last_x_assum(qspec_then `xs` assume_tac)>> rfs[]>>
      fs[get_var_def]>>
      IMP_RES_TAC s_val_eq_LAST_N_exists>>
      last_x_assum(qspecl_then [`st`,`e''''''''`,`ls''''''''`] assume_tac)>>
      rfs[]>>
      HINT_EXISTS_TAC>>
      Q.EXISTS_TAC`fromAList lss'`>>
      fs[]>>
      rpt BasicProvers.VAR_EQ_TAC>>
      `s_key_eq (StackFrame e'''' (SOME r'.handler)::ls'''') 
                (StackFrame e''''' (SOME r'.handler)::ls''''')` by 
         metis_tac[s_key_eq_LAST_N,s_key_eq_tail]>>
      fs[s_key_eq_def]>>
      CONJ_TAC>- (Q.EXISTS_TAC`lss'`>>fs[s_frame_key_eq_def])>>
      metis_tac[s_key_eq_trans]))>>
    (*SOME*)
    BasicProvers.EVERY_CASE_TAC>>fs[]>>rpt strip_tac>-
    (first_x_assum(qspec_then `xs` assume_tac) >> rfs[]>>
    HINT_EXISTS_TAC>>fs[])>>
    Q.EXISTS_TAC `lss`>>fs[]>>rpt strip_tac>>
    IMP_RES_TAC s_val_eq_LAST_N_exists>>
    first_x_assum(qspecl_then [`xs`,`e'''`,`ls'''`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>> fs[]>>Q.EXISTS_TAC`lss'`>>fs[])>-
  (*Call*) 
  (fs[wEval_def]>>
  Cases_on`s.clock=0`>>fs[]>>
  Cases_on`get_vars args s`>> fs[]>>
  Cases_on`find_code dest x s.code`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  Cases_on`ret`>>fs[]>-
    (*Tail Call*)
    (Cases_on`handler`>>fs[]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[dec_clock_def,call_env_def]>-
    (ntac 2 strip_tac>>
    `s.locals = (s with stack := xs).locals` by fs[word_state_component_equality]>>
    IMP_RES_TAC get_vars_stack_swap >>
    first_x_assum(qspec_then `args` (SUBST1_TAC o SYM))>>simp[]>>
    first_x_assum(qspec_then `xs` (assume_tac))>>rfs[]>>
    Q.EXISTS_TAC`st`>>
    fs[word_state_component_equality,s_key_eq_refl])>>
    Q.EXISTS_TAC`lss`>>fs[]>>rpt strip_tac>>
    `s.locals = (s with stack := xs).locals` by fs[word_state_component_equality]>>
    IMP_RES_TAC get_vars_stack_swap >>
    first_x_assum(qspec_then `args` (SUBST1_TAC o SYM))>>simp[]>>
    first_x_assum(qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>>fs[word_state_component_equality]>>
    Q.EXISTS_TAC`lss'`>>fs[])>>
    (*Returning call*)
    Cases_on`x'`>> fs[]>>
    Cases_on`cut_env r' s.locals`>>fs[]>>
    Cases_on`wEval (r,call_env q (push_env x' (IS_SOME handler) (dec_clock s)))`>>
    Cases_on`q''`>>fs[]>>Cases_on`x''`>>fs[]>-
      (*Result*)
      (BasicProvers.FULL_CASE_TAC>>
      BasicProvers.FULL_CASE_TAC>>
      fs[set_var_def,call_env_def]>>
      IMP_RES_TAC push_env_pop_env_s_key_eq>>fs[dec_clock_def,SOME_11]>>
      `s_key_eq s.stack x''.stack` by fs[EQ_SYM_EQ]>>fs[]>>
      CONJ_TAC>-
        (Cases_on`handler`>>fs[push_env_def,LET_THM,env_to_list_def,pop_env_def]>>
        Cases_on`r''.stack`>>fs[s_key_eq_def]>>Cases_on`h`>>Cases_on`o'`>>
        fs[s_frame_key_eq_def]>>
        `y.handler = s.handler` by fs[word_state_component_equality]>>rfs[])>>
       ntac 2 strip_tac>>
       `s.locals = (s with stack := xs).locals` by fs[word_state_component_equality]>>
       IMP_RES_TAC get_vars_stack_swap >>
       first_x_assum(qspec_then `args` (SUBST1_TAC o SYM))>>simp[]>>
       `!a. s_val_eq (a::s.stack) (a::xs)` by 
         (strip_tac>> fs[s_val_eq_def]>>Cases_on`a'`>>
          Cases_on`o'`>>fs[s_frame_val_eq_def])>>
       fs[push_env_def,LET_THM,env_to_list_def]>>
       qpat_abbrev_tac `frame = StackFrame ls n`>>
       first_x_assum (qspec_then `frame` assume_tac)>>
       first_x_assum(qspec_then `frame::xs` assume_tac)>>
       rfs[]>>
       `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]>>
       Cases_on`st`>>fs[s_key_eq_def]>>
       Cases_on`r''.stack`>>fs[pop_env_def,s_key_eq_def]>>
       `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                   s_frame_val_and_key_eq,s_val_eq_def]>>
       Cases_on`h'`>>Cases_on`o'`>>fs[]>>
       fs[word_state_component_equality]>>
       IMP_RES_TAC s_val_eq_tail>>metis_tac[EQ_SYM_EQ])>>
       (*Exception*)
       Cases_on`handler`>>fs[]>-
         (*no handler*)
         (fs[call_env_def,push_env_def,env_to_list_def,dec_clock_def,LET_THM]>>
         CONJ_ASM1_TAC>-
         (IMP_RES_TAC prim_recTheory.LESS_LEMMA1>>
         qpat_assum `LAST_N a as=b` mp_tac>>simp[]>>
         qpat_abbrev_tac `frame = StackFrame a b`>>
         `LENGTH s.stack+1 = LENGTH (frame::s.stack) ` by fs[arithmeticTheory.ADD1]>>
         pop_assum SUBST1_TAC>> fs[LAST_N_LENGTH]>>
         Q.UNABBREV_TAC`frame`>>fs[option_nchotomy])>>
         fs[GEN_ALL LAST_N_TL]>>
         Q.EXISTS_TAC`lss`>>fs[]>>rpt strip_tac>>
         `s.locals = (s with stack:=xs).locals` by fs[word_state_component_equality]>>
         IMP_RES_TAC get_vars_stack_swap>>
         first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
         qpat_abbrev_tac `frame = StackFrame a b`>>
         `s.handler < LENGTH xs` by (IMP_RES_TAC s_val_eq_length>>fs[])>>
         first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
         IMP_RES_TAC (GEN_ALL LAST_N_TL)>>
         last_x_assum(qspec_then `frame` assume_tac)>>
         fs[]>> rfs[]>>
         `s_val_eq (frame::s.stack) (frame::xs)` by
           metis_tac[s_val_eq_def,s_frame_val_eq_def] >>
         fs[]>> HINT_EXISTS_TAC>>
         Q.EXISTS_TAC`fromAList lss'`>>fs[word_state_component_equality]>>
         Q.EXISTS_TAC`lss'`>>fs[])>>
         (*handler*)
         fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
         Cases_on`x''`>>BasicProvers.EVERY_CASE_TAC>>rfs[set_var_def]>>fs[]>>
         `r''.handler = s.handler` by (`LENGTH s.stack +1 = 
          LENGTH (StackFrame (list_rearrange (s.permute 0) 
             (QSORT (λx y.FST x ≤ FST y) (toAList x'))) 
             (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           metis_tac[s_key_eq_trans,s_key_eq_sym])>>
         TRY
           (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
           (ONCE_REWRITE_TAC[CONJ_ASSOC]>>CONJ_TAC>-
           (`LENGTH s.stack +1 = 
             LENGTH (StackFrame (list_rearrange (s.permute 0) 
             (QSORT (λx y.FST x ≤ FST y) (toAList x'))) 
             (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           metis_tac[s_key_eq_trans,s_key_eq_sym])>>
           rpt strip_tac>>
           `s.locals = (s with stack:=xs).locals` by fs[word_state_component_equality]>>
           IMP_RES_TAC get_vars_stack_swap>>
           first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
           qpat_abbrev_tac`frame = StackFrame c d`>>
           `s_val_eq (frame::s.stack) (frame::xs)` by 
             metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
           IMP_RES_TAC s_val_eq_LAST_N_exists>>
           `LENGTH s.stack = LENGTH xs` by fs[s_val_eq_length] >>
           first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
           `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
            LENGTH s.stack +1 = LENGTH (frame::xs)` by 
               fs[arithmeticTheory.ADD1,s_val_eq_length]>>
            fs[LAST_N_LENGTH_cond]>>
            `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
            `lss = lss'` by fs[LIST_EQ_MAP_PAIR]>>
            pop_assum (SUBST1_TAC o SYM)>>
            fs[]>>
            first_x_assum(qspec_then `st` assume_tac)>>
            rfs[]>> HINT_EXISTS_TAC>>
            metis_tac[s_key_eq_trans,handler_eq]))>>
            CONJ_TAC >- (
            `LENGTH s.stack +1 = 
             LENGTH (StackFrame (list_rearrange (s.permute 0) 
             (QSORT (λx y.FST x ≤ FST y) (toAList x'))) 
             (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
             pop_assum SUBST_ALL_TAC>>
             fs[LAST_N_LENGTH]>>
             `LENGTH ls = LENGTH r''.stack` by fs[s_key_eq_length]>>
             fs[])>>
             IMP_RES_TAC s_key_eq_LAST_N_exists>>
             Q.EXISTS_TAC`e'''`>>
             Q.EXISTS_TAC`ls'''`>>            
             fs[]>>
             Q.EXISTS_TAC`lss'`>> 
            (*check*)
             CONJ_TAC>-
             (`LENGTH s.stack +1 = 
               LENGTH (StackFrame (list_rearrange (s.permute 0) 
               (QSORT (λx y.FST x ≤ FST y) (toAList x'))) 
               (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
             pop_assum SUBST_ALL_TAC>>
             fs[LAST_N_LENGTH]>>
             `LENGTH ls = LENGTH r''.stack` by fs[s_key_eq_length]>>
             fs[EQ_SYM_EQ])>>
             fs[]>>
             CONJ_TAC>- metis_tac[s_key_eq_trans]>>
             rpt strip_tac>>
             `s.locals = (s with stack:=xs).locals` by fs[word_state_component_equality]>>
             IMP_RES_TAC get_vars_stack_swap>>
             first_x_assum(qspec_then `args` assume_tac)>>fs[]>>
             qpat_abbrev_tac`frame = StackFrame c d`>>
             `s_val_eq (frame::s.stack) (frame::xs)` by 
               metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
             IMP_RES_TAC s_val_eq_LAST_N_exists>>
             `LENGTH s.stack = LENGTH xs` by fs[s_val_eq_length] >>
             first_x_assum(qspecl_then [`frame::xs`,`e'''''`,`ls'''''`] assume_tac)>>
             rfs[]>>
             `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
              LENGTH s.stack +1 = LENGTH (frame::xs)` by 
               fs[arithmeticTheory.ADD1,s_val_eq_length]>>
             fs[LAST_N_LENGTH_cond]>>
             `MAP FST lss = MAP FST lss''` by metis_tac[EQ_SYM_EQ]>>
             `lss'' = lss` by fs[LIST_EQ_MAP_PAIR]>>
             fs[]>>
             IMP_RES_TAC s_key_eq_LAST_N_exists>> 
             first_x_assum (qspecl_then [`st`,`e''''''''`,`ls''''''''`] assume_tac)>>
             rfs[]>>
             qpat_assum `asd.handler =bcd.handler` (assume_tac o SYM)>>
             fs[handler_eq]>>
             HINT_EXISTS_TAC>>Q.EXISTS_TAC`fromAList lss'''`>>
             fs[]>>
             CONJ_TAC >-
               (Q.EXISTS_TAC`lss'''`>>fs[])>>
             metis_tac[s_key_eq_trans]))
(*DONE*)

val _ = export_theory();
