open HolKernel Parse boolLib bossLib miscLib word_langTheory
open listTheory sptreeTheory pred_setTheory pairTheory optionTheory
open sortingTheory relationTheory

(*
open wordsLib
*)
(*TODO: remove the last_n lemmas*)
open bvp_lemmasTheory miscTheory

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
val s_key_eq_refl = store_thm( "s_key_eq_refl",
  ``!ls .s_key_eq ls ls = T``,
   Induct >> rw[s_key_eq_def]>>
   Cases_on`h`>> Cases_on`o'`>>rw[s_frame_key_eq_def])

val s_val_eq_refl = store_thm( "s_val_eq_refl",
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

val s_key_eq_trans = store_thm("s_key_eq_trans",
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

val s_key_eq_sym = store_thm("s_key_eq_sym",
  ``!a b. s_key_eq a b <=> s_key_eq b a``,
  Induct>> Cases_on`b`>>fs[s_key_eq_def]>>
  strip_tac>>metis_tac[s_frame_key_eq_sym])

val s_frame_val_eq_sym = prove(
   ``!a b. s_frame_val_eq a b <=> s_frame_val_eq b a``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>fs[s_frame_val_eq_def,EQ_SYM_EQ])

val s_val_eq_sym = store_thm("s_val_eq_sym",
  ``!a b. s_val_eq a b <=> s_val_eq b a``,
  Induct>> Cases_on`b`>>fs[s_val_eq_def]>>
  strip_tac>>metis_tac[s_frame_val_eq_sym])

val s_frame_val_and_key_eq = prove(
  ``!s t. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t``,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>
  fs[s_frame_val_eq_def,s_frame_key_eq_def,LIST_EQ_MAP_PAIR])

val s_val_and_key_eq = store_thm("s_val_and_key_eq",
  ``!s t. s_val_eq s t /\ s_key_eq s t ==> s =t``,
  Induct>-
    (Cases>>fs[s_val_eq_def])>>
  rw[]>>
  Cases_on`t`>>fs[s_val_eq_def,s_key_eq_def,s_frame_val_and_key_eq])

val dec_stack_stack_key_eq = prove(
  ``!wl st st'. dec_stack wl st = SOME st' ==> s_key_eq st st'``,
  ho_match_mp_tac dec_stack_ind>>rw[dec_stack_def]>>
  fs[s_key_eq_def]>>
  first_x_assum mp_tac>>BasicProvers.FULL_CASE_TAC>>
  fs[s_key_eq_def]>>rfs[]>>
  rw[]>> fs[s_key_eq_def]>>
  Cases_on`handler`>>fs[MAP_ZIP,s_frame_key_eq_def])

(*wGC preserves the stack_key relation*)
val wGC_s_key_eq = store_thm("wGC_s_key_eq",
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
val wGC_s_val_eq = store_thm("wGC_s_val_eq",
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

(*Slightly more general theorem allows the unused locals to be differnt*)
val wGC_s_val_eq_word_state = store_thm("wGC_s_val_eq_word_state",
  ``!s tlocs tstack y.
          s_val_eq s.stack tstack /\
          wGC s = SOME y ==>
    ?zlocs zstack.
          wGC (s with <|stack:=tstack;locals:=tlocs|>) =
          SOME (y with <|stack:=zstack;locals:=zlocs|>) /\
          s_val_eq y.stack zstack /\ s_key_eq zstack tstack``,
  rw[wGC_def]>>fs[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>fs[]>>
  qpat_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> fs[]>>
  strip_tac>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`tlocs`>>
  Q.EXISTS_TAC`y'`>>
  fs[word_state_component_equality]>>rfs[])

(*Most generalized wGC_s_val_eq*)
val wGC_s_val_eq_gen = store_thm ("wGC_s_val_eq_gen",
``
  !s t s'.
  s.gc_fun = t.gc_fun ∧
  s.memory = t.memory ∧
  s.mdomain = t.mdomain ∧ 
  s.store = t.store ∧
  s_val_eq s.stack t.stack ∧
  wGC s = SOME s' ⇒ 
  ?t'.
  wGC t = SOME t' ∧
  s_val_eq s'.stack t'.stack ∧
  s_key_eq t.stack t'.stack ∧
  t'.memory = s'.memory ∧
  t'.store = s'.store`` ,
  rw[]>>
  fs[wGC_def,LET_THM]>>
  IMP_RES_TAC s_val_eq_enc_stack>>
  BasicProvers.EVERY_CASE_TAC>>rfs[]>>
  IMP_RES_TAC s_val_eq_dec_stack>>fs[]>>
  qpat_assum`A=s'` (SUBST_ALL_TAC o SYM)>>
  IMP_RES_TAC dec_stack_stack_key_eq>>fs[]>>
  metis_tac[s_val_eq_sym])
 
(*pushing and popping maintain the stack_key relation*)
val push_env_pop_env_s_key_eq = store_thm("push_env_pop_env_s_key_eq",
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

val get_vars_stack_swap_simp = prove(
  ``!args. get_vars args (s with stack := xs) = get_vars args s``,
  `(s with stack:=xs).locals = s.locals` by fs[]>>
  metis_tac[get_vars_stack_swap])

val s_val_eq_length = store_thm("s_val_eq_length",
  ``!s t. s_val_eq s t ==> LENGTH s = LENGTH t``,
  Induct>>Cases>>fs[s_val_eq_def,LENGTH]>>
  Cases>>fs[s_val_eq_def])

val s_key_eq_length = store_thm("s_key_eq_length",
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

val s_key_eq_tail = store_thm("s_key_eq_tail",
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

val s_val_eq_LAST_N_exists = store_thm("s_val_eq_LAST_N_exists",
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


val LAST_N_LENGTH_cond = store_thm("LAST_N_LENGTH_cond",
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
      | (SOME TimeOut,s1) => s1.stack = [] /\ s1.locals = LN /\
                             (!xs. s_val_eq s.stack xs ==>
                                   wEval(c,s with stack := xs) =
                                        (SOME TimeOut, s1))
      | (SOME NotEnoughSpace,s1) => s1.stack = [] /\ s1.locals = LN /\
                                    (!xs. s_val_eq s.stack xs ==>
                                          wEval(c,s with stack := xs) =
                                               (SOME NotEnoughSpace, s1))
                             (*for both errors,
                               the stack and locs should also be [] so the swapped stack
                               result should be exactly the same*)
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
                            s_val_eq s1.stack st /\ s_key_eq ls' st)))
      (*NONE, SOME Result cases*)
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
  (fs[wEval_def,wAlloc_def]>>REVERSE BasicProvers.EVERY_CASE_TAC>>
  (BasicProvers.EVERY_CASE_TAC>>
  IMP_RES_TAC wGC_s_key_eq>>
  IMP_RES_TAC push_env_pop_env_s_key_eq>>
  `s_key_eq s.stack y.stack` by fs[set_store_def]>>
  fs[SOME_11]>>TRY(CONJ_TAC>>rw[]>-
    (qpat_assum`wGC a = SOME b` mp_tac>>
    qpat_assum`pop_env a = b` mp_tac>>
    fs[pop_env_def,wGC_def,push_env_def,set_store_def
      ,LET_THM,env_to_list_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs[s_key_eq_def,s_frame_key_eq_def]>>
    rw[]>>fs[]))>> TRY(fs[call_env_def,fromList2_def]>>rw[])>>
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
  fs[has_space_def])>-fs[word_state_component_equality]>>
  Q.EXISTS_TAC`t'`>>
  fs[word_state_component_equality]>>
  metis_tac[s_val_eq_def,s_key_eq_sym])>-
  (*Move*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[set_vars_def,s_key_eq_refl]>>
  rpt strip_tac>>HINT_EXISTS_TAC>>
  assume_tac get_vars_stack_swap_simp>>
  fs[s_key_eq_refl])>-
  (*Inst*)
  (fs[wEval_def,wInst_def,word_assign_def]>>
  BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  srw_tac [] []>>fs[set_var_def,s_key_eq_refl]>>
  BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,mem_store_def]>>
  srw_tac [] []>>fs[set_var_def,s_key_eq_refl,get_var_def]>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Assign*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  rpt strip_tac>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Get*)
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  fs[set_store_def,s_key_eq_refl]>>
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
  (fs[wEval_def]>>BasicProvers.EVERY_CASE_TAC>- fs[call_env_def,fromList2_def] >>
   fs[dec_clock_def,s_key_eq_refl]>>
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
      HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>-
      (ASSUME_TAC (INST_TYPE [``:'b``|->``:'a``]s_key_eq_LAST_N_exists)>>
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
      rpt strip_tac>>
      first_x_assum(qspec_then `xs` assume_tac)>>rfs[])>>
    Cases_on`q`>>fs[]>>
    Cases_on`x`>>fs[]>>
    rpt strip_tac>-
      (first_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>HINT_EXISTS_TAC>>
      fs[])>-
    (Q.EXISTS_TAC`lss`>>fs[]>>
    rpt strip_tac>>
    first_x_assum (qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>>fs[]>>
    Q.EXISTS_TAC`lss'`>>fs[])>>
    first_x_assum (qspec_then `xs` assume_tac)>> rfs[]>>HINT_EXISTS_TAC>>fs[])>-
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
      HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>-
      (ASSUME_TAC (INST_TYPE [``:'b``|->``:'a``]s_key_eq_LAST_N_exists)>>
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
      metis_tac[s_key_eq_trans])>>
      rpt strip_tac>>
      last_x_assum(qspec_then `xs` assume_tac)>>rfs[get_var_def]))>>
    (*SOME*)
    BasicProvers.EVERY_CASE_TAC>>fs[]>>rpt strip_tac>>
    TRY (first_x_assum(qspec_then `xs` assume_tac) >> rfs[]>>
    HINT_EXISTS_TAC>>fs[])>>
    Q.EXISTS_TAC `lss`>>fs[]>>rpt strip_tac>>
    IMP_RES_TAC s_val_eq_LAST_N_exists>>
    first_x_assum(qspecl_then [`xs`,`e'''`,`ls'''`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>> fs[]>>Q.EXISTS_TAC`lss'`>>fs[])>-
  (*Call*)
  (fs[wEval_def]>>
  Cases_on`get_vars args s`>> fs[]>>
  Cases_on`find_code dest x s.code`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  Cases_on`ret`>>fs[]>-
    (*Tail Call*)
    (Cases_on`handler`>>fs[]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[dec_clock_def,call_env_def,fromList2_def]>>
    TRY (ntac 2 strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
    first_x_assum(qspec_then `xs` (assume_tac))>>rfs[]>>
    Q.EXISTS_TAC`st`>>
    fs[word_state_component_equality,s_key_eq_refl])>>
    Q.EXISTS_TAC`lss`>>fs[]>>rpt strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
    first_x_assum(qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>>fs[word_state_component_equality]>>
    Q.EXISTS_TAC`lss'`>>fs[])>>
    (*Returning call*)
    PairCases_on`x'`>> fs[]>>
    Cases_on`cut_env x'1 s.locals`>>fs[]>>
    Cases_on`s.clock=0`>-
      (fs[call_env_def,fromList2_def]>>rw[]>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[])>>
    Cases_on`wEval (r,call_env q (push_env x' (IS_SOME handler) (dec_clock s)))`>>
    Cases_on`q'`>>fs[]>>Cases_on`x''`>>fs[]>-
      (*Result*)
      (BasicProvers.FULL_CASE_TAC>>
      BasicProvers.FULL_CASE_TAC>>
      fs[set_var_def,call_env_def]>>
      IMP_RES_TAC push_env_pop_env_s_key_eq>>fs[dec_clock_def,SOME_11]>>
      `s_key_eq s.stack x''.stack` by fs[EQ_SYM_EQ]>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      Cases_on`q'`>>fs[]>> (*Note value restriction on return handler*)
      CONJ_TAC>- metis_tac[s_key_eq_trans]>>CONJ_ASM1_TAC>-
      (Cases_on`handler`>>fs[push_env_def,LET_THM,env_to_list_def,pop_env_def]>>
      Cases_on`r'.stack`>>fs[s_key_eq_def]>>Cases_on`h`>>Cases_on`o'`>>
      fs[s_frame_key_eq_def]>>
      fs[word_state_component_equality]>>rfs[])>>
      ntac 2 strip_tac>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> fs[s_val_eq_def]>>Cases_on`a'`>>
        Cases_on`o'`>>fs[s_frame_val_eq_def])>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      qpat_abbrev_tac `frame = StackFrame ls n`>>
      first_x_assum (qspec_then `frame` assume_tac)>>
      last_x_assum(qspec_then `frame::xs` assume_tac)>>
      rfs[]>>
      `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]>>
      Cases_on`st`>>fs[s_key_eq_def]>>
      Cases_on`r'.stack`>>fs[pop_env_def,s_key_eq_def]>>
      `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                            s_frame_val_and_key_eq,s_val_eq_def]>>
      Cases_on`h'`>>Cases_on`o'`>>fs[]>>
      fs[word_state_component_equality]>>
      IMP_RES_TAC s_val_eq_tail>>
      first_x_assum(qspec_then `t` assume_tac)>> rfs[]>>
      Q.EXISTS_TAC`st`>> fs[word_state_component_equality]>>
      TRY (`x'' with <|locals := insert x'0 a x''.locals; stack := t|> =
           r' with <|locals := insert x'0 a x''.locals; stack := t|>` by
           (fs[word_state_component_equality]>>NO_TAC)>>
           pop_assum SUBST_ALL_TAC)>>
      TRY (`x'' with <|locals := insert x'0 a x''.locals; stack := t|> =
            r' with <|locals := insert x'0 a x''.locals; stack := t; handler:=s.handler|>` by
            fs[word_state_component_equality]>>
            pop_assum SUBST_ALL_TAC)>> rw[]>>
       metis_tac[word_state_component_equality,EQ_SYM_EQ,s_key_eq_trans])>-
       (*Exception*)
       (Cases_on`handler`>>fs[]>-
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
         assume_tac get_vars_stack_swap_simp>>
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
         `r'.handler = s.handler` by (`LENGTH s.stack +1 =
          LENGTH (StackFrame (list_rearrange (s.permute 0)
             (QSORT key_val_compare (nub (toAList x'))))
             (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           metis_tac[s_key_eq_trans,s_key_eq_sym])>>
         TRY
           (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
           (ONCE_REWRITE_TAC[CONJ_ASSOC]>>CONJ_TAC>-
           (`LENGTH s.stack +1 =
             LENGTH (StackFrame (list_rearrange (s.permute 0)
             (QSORT key_val_compare (nub (toAList x'))))
             (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           metis_tac[s_key_eq_trans,s_key_eq_sym])>>
           rpt strip_tac>>
           assume_tac get_vars_stack_swap_simp>>
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
            metis_tac[s_key_eq_trans,handler_eq]))>-
            (CONJ_TAC >- (
            `LENGTH s.stack +1 =
             LENGTH (StackFrame (list_rearrange (s.permute 0)
             (QSORT key_val_compare (nub (toAList x'))))
             (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
             pop_assum SUBST_ALL_TAC>>
             fs[LAST_N_LENGTH]>>
             `LENGTH ls = LENGTH r'.stack` by fs[s_key_eq_length]>>
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
               (QSORT key_val_compare (nub (toAList x'))))
               (SOME s.handler)::s.stack)` by fs[arithmeticTheory.ADD1]>>
             pop_assum SUBST_ALL_TAC>>
             fs[LAST_N_LENGTH]>>
             `LENGTH ls = LENGTH r'.stack` by fs[s_key_eq_length]>>
             fs[EQ_SYM_EQ])>>
             fs[]>>
             CONJ_TAC>- metis_tac[s_key_eq_trans]>>
             rpt strip_tac>>
             assume_tac get_vars_stack_swap_simp>>
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
             metis_tac[s_key_eq_trans])>>
             (*TimeOut*)
             rpt strip_tac>>
             assume_tac get_vars_stack_swap_simp>>
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
              rfs[]>>
              `r' with handler := s.handler = r'` by fs[word_state_component_equality]>>
              fs[]>>HINT_EXISTS_TAC>>fs[])>>
      (*Cleanup...*)
      (ntac 2 strip_tac>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` SUBST1_TAC)>>simp[]>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
         (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
          Cases_on`o'`>>fs[s_frame_val_eq_def])>>
       fs[push_env_def,LET_THM,env_to_list_def,dec_clock_def]>>
       qpat_abbrev_tac `frame = StackFrame ls n`>>
       first_x_assum (qspec_then `frame` assume_tac)>>
       first_x_assum(qspec_then `frame::xs` assume_tac)>>
       rfs[call_env_def]>>
       `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[])))

(*DONE*)

val GENLIST_MAP = prove(
  ``!k. (!i. i < LENGTH l ==> m i < LENGTH l) /\ k <= LENGTH l ==>
        GENLIST (\i. EL (m i) (MAP f l)) k =
        MAP f (GENLIST (\i. EL (m i) l) k)``,
  Induct \\ fs [GENLIST] \\ REPEAT STRIP_TAC
  \\ `k < LENGTH l /\ k <= LENGTH l` by DECIDE_TAC
  \\ fs [EL_MAP]);

val list_rearrange_MAP = store_thm ("list_rearrange_MAP",
  ``!l f m. list_rearrange m (MAP f l) = MAP f (list_rearrange m l)``,
  SRW_TAC [] [list_rearrange_def] \\ MATCH_MP_TAC GENLIST_MAP \\
  fs[BIJ_DEF,INJ_DEF]);

val monotonic_color_def = Define`
  !f. monotonic_color f <=>
        !x:num y. x < y ==> (f x):num < f y`

val rel_monotonic_def = Define`
  !R f. rel_monotonic R f <=>
    !x y. R x y ==> R (f x) (f y)`

(*Theorems about sorting under a rel_monotonic relation*)
val rel_monotonic_SORTED = prove(
 ``!R ls f. rel_monotonic R f /\ SORTED R ls==>
   SORTED R (MAP f ls)``,
  ho_match_mp_tac SORTED_IND>> rw[]>>
  fs[SORTED_DEF,rel_monotonic_def])


val MAP_monotonic_QSORT_EQ = prove(
  ``!R f ls. total R /\ transitive R /\ antisymmetric R /\
             rel_monotonic R f
    ==> MAP f (QSORT R ls) = QSORT R (MAP f ls)`` ,
    rpt strip_tac>>
    match_mp_tac (MP_CANON SORTED_PERM_EQ) >>
    HINT_EXISTS_TAC >> simp[] >>
    conj_tac >- (
      metis_tac[QSORT_SORTED,rel_monotonic_SORTED])>>
    conj_tac >- metis_tac[QSORT_SORTED] >>
    match_mp_tac PERM_TRANS >>
    qexists_tac`MAP f ls` >>
    conj_tac >- (
      match_mp_tac PERM_MAP >>
      metis_tac[QSORT_PERM,PERM_SYM] ) >>
    metis_tac[QSORT_PERM] )

val facts = prove(
  ``total key_val_compare /\
    transitive key_val_compare /\
    antisymmetric key_val_compare``,
  fs[total_def,transitive_def,antisymmetric_def,key_val_compare_def]>>
  rw[]>>fsrw_tac[ARITH_ss][]>-
    (Cases_on`a'=a`>>
    BasicProvers.EVERY_CASE_TAC>>
    fsrw_tac[ARITH_ss][]>>
    wordsLib.WORD_DECIDE_TAC)>-
    (Cases_on`y`>>fs[LET_THM]>>
    BasicProvers.EVERY_CASE_TAC>>
    fsrw_tac[ARITH_ss][]>>
    wordsLib.WORD_DECIDE_TAC)>>
  (Cases_on`x`>>Cases_on`y`>>
  Cases_on`q=q'`>>fsrw_tac[ARITH_ss][LET_THM]>>
  BasicProvers.EVERY_CASE_TAC>-
    wordsLib.WORD_DECIDE_TAC>-
    fs[]>- fs[]>>
    Cases_on`n=n'`>>
    fsrw_tac[ARITH_ss][]))

(*Pull out the definition of exactly matched locals
  We use an injective f so the 2nd condition is insufficient*)
val exact_colored_locals_def = Define`
exact_colored_locals f x y <=>
  (domain y = IMAGE f (domain x) /\
   !z. lookup z x = lookup (f z) y)`

val MEM_nub = prove(
 ``!ls x. MEM x (nub ls) <=> MEM x ls``,
  Induct>> rw[nub_def]>>
  metis_tac[])

val toAList_exact_colored_locals_permute = prove(
  ``!f x y. INJ f UNIV UNIV /\
            exact_colored_locals f x y
       ==>  PERM (MAP (\a,b.(f a,b)) (nub (toAList x))) (nub (toAList y))``,
  rw[]>> fs[exact_colored_locals_def]>>
  match_mp_tac PERM_ALL_DISTINCT>>
  rw[]>-
    (`INJ (\a,b:'a. (f a,b)) UNIV UNIV` by
      (fs[INJ_DEF]>>rpt strip_tac>> Cases_on`x'`>>Cases_on`y'`>>fs[])>>
    ASSUME_TAC (INST_TYPE [``:'a``|-> ``:num # 'a``] all_distinct_nub)>>
    first_assum (qspec_then `toAList x` assume_tac)>>
    match_mp_tac ALL_DISTINCT_MAP_INJ>>
    rw[]>- (Cases_on`x'`>>Cases_on`y'`>>fs[INJ_DEF]))>-
    fs[all_distinct_nub]>>
  Cases_on`x'`>>
  rw[EQ_IMP_THM]>-
    (fs[MEM_MAP]>>Cases_on`y'`>>fs[]>>
    IMP_RES_TAC MEM_nub>>
    metis_tac[MEM_toAList,MEM_nub])>>
  IMP_RES_TAC MEM_nub>>
  IMP_RES_TAC MEM_toAList>>
    `?z. lookup z x = SOME r /\ f z = q` by
      (IMP_RES_TAC domain_lookup>>
      fs[EXTENSION] >> last_x_assum(qspec_then `q` assume_tac)>>fs[]>>
      fs[domain_lookup]>>
      HINT_EXISTS_TAC>>fs[])>>
      match_mp_tac (GEN_ALL (snd(EQ_IMP_RULE (SPEC_ALL MEM_MAP))))>>
    Q.EXISTS_TAC `z,r`>>
    fs[]>>metis_tac[PAIR,MEM_toAList,MEM_nub])

val color_fst_monotonic = prove(``
  monotonic_color f ==> rel_monotonic key_val_compare (\x,y.f x,y)``,
  strip_tac>>fs[monotonic_color_def,rel_monotonic_def]>>
  Cases>>Cases>>fs[LET_THM,key_val_compare_def]>>
  metis_tac[])

(*Under a monotonic coloring f rename of keys in the locals*)
val env_to_list_monotonic_eq = store_thm("env_to_list_monotonic_eq",
  ``!f x y p.
    monotonic_color f /\
    INJ f UNIV UNIV /\
    exact_colored_locals f x y
    ==>
    let (x',p') = env_to_list x p in
    let (y',p'') = env_to_list y p in
      MAP (\x,y.f x,y) x' = y' /\
      p' = p'' ``,
  rpt strip_tac>>fs[env_to_list_def,LET_THM]>>
  ASSUME_TAC (SPEC_ALL toAList_exact_colored_locals_permute)>>
  simp[GSYM list_rearrange_MAP]>>
  AP_TERM_TAC>>
  assume_tac color_fst_monotonic>>
  qmatch_abbrev_tac`MAP h (QSORT R ls) = X`>>
  Q.ISPECL_THEN[`R`,`h`,`ls`]mp_tac MAP_monotonic_QSORT_EQ >>
  discharge_hyps_keep >- (
    assume_tac (INST_TYPE [``:'b``|->``:'a``,``:'c``|->``:'a``] facts)>>
    fs[LET_THM,Abbr`R`,Abbr`h`]) >>
  disch_then SUBST1_TAC >>
  fs[Abbr`X`] >> simp[QSORT_eq_if_PERM] >>
  unabbrev_all_tac >>
  fs[toAList_exact_colored_locals_permute])

(*Theorems about sorting that ended up not used*)

(*Equality under a relation R*)
val EQ_R_def = Define`
  EQ_R R x y <=> R x y /\ R y x`


(*set_trace "simplifier" 0*)
(*all distinct with respect to R which is meant to be
total, transitive and reflexive i.e. a total order*)
val ALL_DISTINCT_R_def = Define`
  (ALL_DISTINCT_R R [] <=> T) /\
  (ALL_DISTINCT_R R (x::xs) <=>
    ~EXISTS (EQ_R R x) xs /\ ALL_DISTINCT_R R xs)`

val SORTED_HEAD_SWAP = prove(
``!R x h xs. transitive R /\ SORTED R (h::xs) /\ R x h ==>
             SORTED R (x::xs)``,
  Induct_on `xs`>> fs[]>>
  rpt strip_tac>>
  metis_tac[SORTED_DEF,transitive_def])

(*Head element is < everything in the list*)
val SORTED_ALL_DISTINCT_R_head = prove
(``!R x xs. transitive R /\
           SORTED R (x::xs) /\
           ALL_DISTINCT_R R (x::xs)
  ==> EVERY (\y. R x y /\~R y x) xs``,
Induct_on `xs`>>
fs[]>>rpt strip_tac>>
fs[SORTED_DEF,ALL_DISTINCT_R_def,EQ_R_def]>>
IMP_RES_TAC SORTED_HEAD_SWAP>>
last_assum(qspecl_then [`R`,`x`] assume_tac)>>
metis_tac[])

val SORTED_HEAD_LT = prove
(``!R x xs. transitive R /\
            SORTED R (x::xs)
        ==> EVERY (\y. R x y) xs``,
  Induct_on`xs`>>
  fs[SORTED_DEF]>>rpt strip_tac>>
  last_x_assum(qspecl_then [`R`,`h`] assume_tac)>> rfs[]>>
  fs [EVERY_MEM] >> rpt strip_tac>>
  metis_tac[transitive_def])

val UNIQUE_SORTED_PERM_ALL_DISTINCT_R = prove
(``!R l1 l2.
  transitive R /\
  SORTED R l1 /\
  SORTED R l2 /\
  ALL_DISTINCT_R R l1 /\
  PERM l1 l2 (*Implies ALL_DISTINCT_R l2*)
  ==>
  l1 = l2``,
ho_match_mp_tac SORTED_IND>>
rw[SORTED_DEF]>>
Cases_on`l2`>> fs[]>>
`SORTED R t` by (Cases_on`t`>>fs[SORTED_DEF])>>
CONJ_ASM1_TAC>-
  (`MEM x (h::t) /\ MEM h (x::y::rst)` by
    (IMP_RES_TAC PERM_MEM_EQ>> metis_tac[MEM])>>
  `SORTED R (x::y::rst)` by fs[SORTED_DEF]>>
  IMP_RES_TAC SORTED_HEAD_LT>>
  Cases_on`x=h`>> simp[]>>
  `MEM x t /\ MEM h (y::rst)` by fs[]>>
  `EQ_R R x h` by fs[EQ_R_def,EVERY_MEM]>>
  metis_tac[EXISTS_MEM,ALL_DISTINCT_R_def])>>
(`PERM(y::rst) t` by fs[PERM_CONS_IFF]>>
metis_tac[ALL_DISTINCT_R_def]))

val _ = export_theory();
