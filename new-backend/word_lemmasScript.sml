open HolKernel Parse boolLib bossLib miscLib word_langTheory
open listTheory sptreeTheory pred_setTheory pairTheory optionTheory
val _ = new_theory "word_lemmas";

(*TODO: may need to define the [] (x::xs) cases?*)
(*Stacks look the same except for the keys (recolored and in order)*)
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

(*Stacks look the same except for the values (result of gc)*)
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

 

val s_frame_key_eq_trans = prove(
  ``!a b c. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
            s_frame_key_eq a c``,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  fs[s_frame_key_eq_def])

(*transitive*)
val s_key_eq_trans = prove(
  ``!a b c. s_key_eq a b /\ s_key_eq b c ==>
            s_key_eq a c``,
  Induct>>
  Cases_on`b`>>Cases_on`c`>>fs[s_key_eq_def]>>
  rw[]>>metis_tac[s_frame_key_eq_trans])

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

(*wGC succeeds on all stacks related by stack_val*)

val wGC_s_val_eq = prove(
  ``!s x st y. s_val_eq s.stack st /\ 
             wGC s = SOME y ==> 
      ?z. wGC (s with stack := st) = SOME (y with stack := z) /\
          s_val_eq y.stack z /\ s_key_eq z st``,
  rw[wGC_def]>>fs[LET_THM]>>
  IMP_RES_TAC s_val_eq_enc_stack>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  qpat_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>>
  simp[]
  fs[dec_stack_def]
  BasicProvers.EVERY_CASE_TAC>>

(*pushing and popping maintain the stack_key relation*)
val push_env_pop_env_s_key_eq = prove(
  ``!s t x b. s_key_eq (push_env x b s).stack t.stack ==>
              ?y. (pop_env t = SOME y /\
                   s_key_eq s.stack y.stack)``,
  rw[push_env_def]>>fs[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
  fs[s_key_eq_def,pop_env_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[])

(*Stack swap theorem for wEval*)
val wEval_stack_swap = store_thm("wEval_stack_swap",
  ``!c s.
      case wEval (c,s) of
      | (SOME Error,s1) => T
      | (SOME TimeOut,s1) => T (*probably needs a cond here*)
      | (SOME NotEnoughSpace,s1) => T (*probably needs a cond here*)
      | (SOME (Exception t),s1) =>
            (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                  (s2.stack = s1.stack) /\ (s2.handler = s1.handler) /\
                  (!xs s7. (jump_exc (s with stack := xs) = SOME s7) /\
                           (s_val_eq s.stack xs) ==>
                           ?st locs.
                           (wEval (c,s with stack := xs) =
                              (SOME (Exception t),
                               s1 with <| stack := st;
                                          handler := s7.handler ;
                                          locals := locs |>) /\
                            loc_key_rel s7.locals locs /\
                            loc_val_rel s1.locals locs /\
                            s_val_eq s1.stack st /\ s_key_eq s7.stack st)))
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
  fs[wEval_def,wAlloc_def]>>BasicProvers.EVERY_CASE_TAC>>
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
  EXISTS_TAC ``xs``
     
BasicProvers.EVERY_CASE_TAC>>fs[] 


