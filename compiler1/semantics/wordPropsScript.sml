open HolKernel Parse boolLib bossLib miscLib

open wordLangTheory wordSemTheory
open listTheory sptreeTheory pred_setTheory pairTheory optionTheory
open sortingTheory relationTheory
open miscTheory

(*
Defines a stack swap lemma and some basic coventions for wordlang
*)
(*TODO: remove the last_n lemmas*)

val _ = new_theory "wordProps";

(*Stacks look the same except for the keys (e.g. recoloured and in order)*)
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

(*gc preserves the stack_key relation*)
val gc_s_key_eq = store_thm("gc_s_key_eq",
  ``!s x. gc s = SOME x ==> s_key_eq s.stack x.stack``,
  rw[gc_def] >>fs[LET_THM]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  fs[state_component_equality]>>rfs[])

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

(*gc succeeds on all stacks related by stack_val and there are relations
  in the result*)
val gc_s_val_eq = store_thm("gc_s_val_eq",
  ``!s x st y. s_val_eq s.stack st /\
             gc s = SOME y ==>
      ?z. gc (s with stack := st) = SOME (y with stack := z) /\
          s_val_eq y.stack z /\ s_key_eq z st``,
  rw[gc_def]>>fs[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>fs[]>>
  qpat_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> fs[]>>
  strip_tac>>fs[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`y'`>>fs[state_component_equality]>>rfs[])

(*Slightly more general theorem allows the unused locals to be differnt*)
val gc_s_val_eq_word_state = store_thm("gc_s_val_eq_word_state",
  ``!s tlocs tstack y.
          s_val_eq s.stack tstack /\
          gc s = SOME y ==>
    ?zlocs zstack.
          gc (s with <|stack:=tstack;locals:=tlocs|>) =
          SOME (y with <|stack:=zstack;locals:=zlocs|>) /\
          s_val_eq y.stack zstack /\ s_key_eq zstack tstack``,
  rw[gc_def]>>fs[LET_THM]>>
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
  fs[state_component_equality]>>rfs[])

(*Most generalised gc_s_val_eq*)
val gc_s_val_eq_gen = store_thm ("gc_s_val_eq_gen",
``
  !s t s'.
  s.gc_fun = t.gc_fun ∧
  s.memory = t.memory ∧
  s.mdomain = t.mdomain ∧
  s.store = t.store ∧
  s_val_eq s.stack t.stack ∧
  gc s = SOME s' ⇒
  ?t'.
  gc t = SOME t' ∧
  s_val_eq s'.stack t'.stack ∧
  s_key_eq t.stack t'.stack ∧
  t'.memory = s'.memory ∧
  t'.store = s'.store`` ,
  rw[]>>
  fs[gc_def,LET_THM]>>
  IMP_RES_TAC s_val_eq_enc_stack>>
  BasicProvers.EVERY_CASE_TAC>>rfs[]>>
  IMP_RES_TAC s_val_eq_dec_stack>>fs[]>>
  qpat_assum`A=s'` (SUBST_ALL_TAC o SYM)>>
  IMP_RES_TAC dec_stack_stack_key_eq>>fs[]>>
  metis_tac[s_val_eq_sym])

(*pushing and popping maintain the stack_key relation*)
val push_env_pop_env_s_key_eq = store_thm("push_env_pop_env_s_key_eq",
  ``!s t x opt. s_key_eq (push_env x opt s).stack t.stack ==>
              ?y. (pop_env t = SOME y /\
                   s_key_eq s.stack y.stack)``,
  rw[]>>Cases_on`opt`>>TRY(PairCases_on`x'`)>>
  fs[push_env_def]>>fs[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
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
  rw[LAST_N_def]>>fs[s_val_eq_def]>>
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
  rw[LAST_N_def]>>fs[s_key_eq_def]>>
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
  ``x with handler := x.handler = x``, fs[state_component_equality])

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

(*Stack swap theorem for evaluate*)
val evaluate_stack_swap = store_thm("evaluate_stack_swap",
  ``!c s.
      case evaluate (c,s) of
      | (SOME Error,s1) => T
      | (SOME TimeOut,s1) => s1.stack = [] /\ s1.locals = LN /\
                             (!xs. s_val_eq s.stack xs ==>
                                   evaluate(c,s with stack := xs) =
                                        (SOME TimeOut, s1))
      | (SOME NotEnoughSpace,s1) => s1.stack = [] /\ s1.locals = LN /\
                                    (!xs. s_val_eq s.stack xs ==>
                                          evaluate(c,s with stack := xs) =
                                               (SOME NotEnoughSpace, s1))
                             (*for both errors,
                               the stack and locs should also be [] so the swapped stack
                               result should be exactly the same*)
      | (SOME (Exception x y),s1) =>
            (s.handler<LENGTH s.stack) /\ (*precondition for jump_exc*)
            (?e n ls lss.
                (LAST_N (s.handler+1) s.stack = StackFrame e (SOME n)::ls) /\
                (MAP FST e = MAP FST lss /\
                   s1.locals = fromAList lss) /\
                (s_key_eq s1.stack ls) /\ (s1.handler = case n of(a,b,c)=>a) /\
                (!xs e' ls'.
                           (LAST_N (s.handler+1) xs =
                             StackFrame e' (SOME n):: ls') /\
                           (s_val_eq s.stack xs) ==> (*this implies n=n'*)
                           ?st locs.
                           (evaluate (c,s with stack := xs) =
                              (SOME (Exception x y),
                               s1 with <| stack := st;
                                          handler := case n of (a,b,c) => a;
                                          locals := locs |>) /\
                            (?lss'. MAP FST e' = MAP FST lss' /\
                               locs = fromAList lss' /\
                               MAP SND lss = MAP SND lss')/\
                            s_val_eq s1.stack st /\ s_key_eq ls' st)))
      (*NONE, SOME Result cases*)
      | (res,s1) => (s_key_eq s.stack s1.stack) /\ (s1.handler = s.handler) /\
                    (!xs. s_val_eq s.stack xs ==>
                          ?st. evaluate (c,s with stack := xs) =
                                (res, s1 with stack := st)  /\
                                s_val_eq s1.stack st /\
                                s_key_eq xs st)``,
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>-
  (*Skip*)
  (fs[evaluate_def,s_key_eq_refl]>>rw[]>>HINT_EXISTS_TAC>>fs[s_key_eq_refl])>-
  (*Alloc*)
  (fs[evaluate_def,alloc_def]>>REVERSE BasicProvers.EVERY_CASE_TAC>>
  (BasicProvers.EVERY_CASE_TAC>>
  IMP_RES_TAC gc_s_key_eq>>
  IMP_RES_TAC push_env_pop_env_s_key_eq>>
  `s_key_eq s.stack y.stack` by fs[set_store_def]>>
  fs[SOME_11]>>TRY(CONJ_TAC>>rw[]>-
    (qpat_assum`gc a = SOME b` mp_tac>>
    qpat_assum`pop_env a = b` mp_tac>>
    fs[pop_env_def,gc_def,push_env_def,set_store_def
      ,LET_THM,env_to_list_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs[s_key_eq_def,s_frame_key_eq_def]>>
    rw[]>>fs[]))>> TRY(fs[call_env_def,fromList2_def]>>rw[])>>
  BasicProvers.FULL_CASE_TAC>>fs[get_var_def]>>
  BasicProvers.FULL_CASE_TAC>>
  Q.MATCH_ASSUM_ABBREV_TAC `gc a = y`>>
  Q.MATCH_ASSUM_ABBREV_TAC `gc b = SOME x'`>>
  `s_val_eq b.stack a.stack /\ b with stack:=a.stack = a` by
    (fs[push_env_def,LET_THM,env_to_list_def,set_store_def]>>
    bossLib.UNABBREV_ALL_TAC>>
    fs[s_val_eq_def,s_frame_val_eq_def,s_val_eq_sym])>>
  Q.UNABBREV_TAC `y`>>
  IMP_RES_TAC gc_s_val_eq>>rfs[]>>
  Q.UNABBREV_TAC`b`>>Q.UNABBREV_TAC`a`>>
  fs[push_env_def,set_store_def,LET_THM,env_to_list_def]>>
  Cases_on`x'.stack`>>
  Cases_on`z'`>>fs[s_key_eq_def,state_component_equality]>>
  `h=h'` by (
    fs[s_val_eq_def,s_key_eq_def]>>
    `s_frame_key_eq h' h` by metis_tac[s_frame_key_eq_trans]>>
    metis_tac[s_frame_val_and_key_eq,s_frame_key_eq_sym])>>
  fs[pop_env_def] >>Cases_on`h'`>>Cases_on`o'`>>fs[s_frame_key_eq_def]>>
  fs[state_component_equality]>>
  fs[has_space_def])>-fs[state_component_equality]>>
  Q.EXISTS_TAC`t'`>>
  fs[state_component_equality]>>
  metis_tac[s_val_eq_def,s_key_eq_sym])>-
  (*Move*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[set_vars_def,s_key_eq_refl]>>
  rpt strip_tac>>HINT_EXISTS_TAC>>
  assume_tac get_vars_stack_swap_simp>>
  fs[s_key_eq_refl])>-
  (*Inst*)
  (fs[evaluate_def,inst_def,assign_def]>>
  BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  srw_tac [] []>>fs[set_var_def,s_key_eq_refl]>>
  BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,mem_store_def]>>
  srw_tac [] []>>fs[set_var_def,s_key_eq_refl,get_var_def]>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Assign*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  rpt strip_tac>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Get*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>>fs[set_var_def,s_key_eq_refl]>>
  fs[set_store_def,s_key_eq_refl]>>
  rpt strip_tac>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Set*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[set_store_def,s_key_eq_refl]>>
  rpt strip_tac>>
  HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>-
  (*Store*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>>
  fs[mem_store_def,state_component_equality,s_key_eq_refl]>>
  rpt strip_tac>>HINT_EXISTS_TAC>>
  fs[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,get_var_def,
     state_component_equality])>-
  (*Tick*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>- fs[call_env_def,fromList2_def] >>
   fs[dec_clock_def,s_key_eq_refl]>>
   rpt strip_tac>>Q.EXISTS_TAC`xs`>>fs[s_key_eq_refl])>-
  (*Seq*)
  (fs[evaluate_def]>>
  Cases_on`evaluate(c',s)`>>
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
      first_x_assum(qspecl_then [`r.stack`,`s.stack`,`s.handler+1`,`e`,`n`,`ls`] assume_tac)>>
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
  (fs[evaluate_def]>> BasicProvers.EVERY_CASE_TAC>>
  fs[call_env_def,s_key_eq_refl]>>
  rpt strip_tac>>fs[get_var_def]>>HINT_EXISTS_TAC>>
  fs[state_component_equality,s_key_eq_refl])>-
  (*Raise*)
  (fs[evaluate_def]>>BasicProvers.EVERY_CASE_TAC>>fs[get_var_def,jump_exc_def]>>
  qpat_assum `(a = SOME x)` mp_tac>>
  BasicProvers.EVERY_CASE_TAC>>fs[state_component_equality]>>
  strip_tac>> Q.EXISTS_TAC `l`>>
  fs[EQ_SYM_EQ,s_key_eq_refl]>>
  rpt strip_tac>>
  IMP_RES_TAC s_val_eq_length>>fs[EQ_SYM_EQ,state_component_equality]>>
  fs[s_key_eq_refl]>>
  `s.handler + 1<= LENGTH s.stack` by metis_tac[arithmeticTheory.LESS_OR,arithmeticTheory.ADD1]>>
  rpt (qpat_assum `a = LAST_N b c` (ASSUME_TAC o SYM))>>
  IMP_RES_TAC s_val_eq_LAST_N>>
  first_x_assum(qspec_then `s.handler+1` assume_tac)>>rfs[]>>
  IMP_RES_TAC s_val_eq_tail>>
  fs[s_val_eq_def,s_frame_val_eq_def]>>
  Q.EXISTS_TAC`e'`>>fs[])>-
  (*If*)
  (fs[evaluate_def]>>
  ntac 4 BasicProvers.FULL_CASE_TAC>>fs[]>>
  Cases_on`word_cmp cmp c''' c`>> fs[]>>
  BasicProvers.EVERY_CASE_TAC>>
  fs[s_key_eq_trans]>>rw[]>>
  TRY(last_x_assum(qspec_then `xs` assume_tac)>>rfs[]>>
  fs[get_var_def]>>Cases_on`ri`>>fs[get_var_imm_def,get_var_def]>>
  HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>>
  qexists_tac`lss`>>fs[]>>rw[]>>
  IMP_RES_TAC s_val_eq_LAST_N_exists>>
  last_x_assum(qspecl_then [`xs`,`e'''`,`ls'''`] assume_tac)>>
  Cases_on`ri`>>rfs[get_var_def,get_var_imm_def]>>
  HINT_EXISTS_TAC>>fs[]>>
  qexists_tac`fromAList lss'`>>fs[]>>
  qexists_tac`lss'`>>fs[])>-
 (*Call*)
  (fs[evaluate_def]>>
  Cases_on`get_vars args s`>> fs[]>>
  Cases_on`find_code dest x s.code`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  Cases_on`ret`>>fs[]
  >-
    (*Tail Call*)
    (Cases_on`handler`>>fs[]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[dec_clock_def,call_env_def,fromList2_def]>>
    TRY (ntac 2 strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
    first_x_assum(qspec_then `xs` (assume_tac))>>rfs[]>>
    Q.EXISTS_TAC`st`>>
    fs[state_component_equality,s_key_eq_refl])>>
    Q.EXISTS_TAC`lss`>>fs[]>>rpt strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
    first_x_assum(qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
    HINT_EXISTS_TAC>>
    Q.EXISTS_TAC`fromAList lss'`>>fs[state_component_equality]>>
    Q.EXISTS_TAC`lss'`>>fs[])
  >>
    (*Returning call*)
    PairCases_on`x'`>> fs[]>>
    Cases_on`cut_env x'1 s.locals`>>fs[]>>
    Cases_on`s.clock=0`>-
      (fs[call_env_def,fromList2_def]>>rw[]>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[])>>
    fs[]>>
    Cases_on`evaluate (r,call_env (Loc x'3 x'4::q) (push_env x' handler (dec_clock s)))`>>
    Cases_on`q'`>>fs[]>>Cases_on`x''`>>fs[]>-
      (*Result*)
      (BasicProvers.EVERY_CASE_TAC>>
      fs[set_var_def,call_env_def]>>
      IMP_RES_TAC push_env_pop_env_s_key_eq>>fs[dec_clock_def,SOME_11]>>
      `s_key_eq s.stack x''.stack` by fs[EQ_SYM_EQ]>>fs[]>>
      (CONJ_TAC>- metis_tac[s_key_eq_trans]>>CONJ_ASM1_TAC>-
      (fs[push_env_def,LET_THM,env_to_list_def,pop_env_def]>>
      Cases_on`r'.stack`>>fs[s_key_eq_def]>>Cases_on`h`>>Cases_on`o'`>>
      TRY(PairCases_on`x'''`)>>
      fs[s_frame_key_eq_def]>>
      fs[state_component_equality]>>rfs[])>>
      ntac 2 strip_tac>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` (SUBST1_TAC))>>simp[]>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
        Cases_on`o'`>>fs[s_frame_val_eq_def])>>
      fs[push_env_def,LET_THM,env_to_list_def]>>
      qpat_abbrev_tac `frame = StackFrame ls n`>>
      first_x_assum (qspec_then `frame` assume_tac)>>
      first_x_assum(qspec_then `frame::xs` assume_tac)>>
      rfs[]>>
      `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[]>>
      Cases_on`st`>>fs[s_key_eq_def]>>
      Cases_on`r'.stack`>>fs[pop_env_def,s_key_eq_def]>>
      `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                            s_frame_val_and_key_eq,s_val_eq_def]>>
      Cases_on`h'`>>Cases_on`o'`>>fs[]>>
      fs[state_component_equality]>>
      IMP_RES_TAC s_val_eq_tail>>
      first_x_assum(qspec_then `t` assume_tac)>> rfs[]>>
      TRY(Cases_on`x'''`>>
          `x''.stack = t'` by fs[EQ_SYM_EQ]>>fs[]>>rfs[])>>
      Q.EXISTS_TAC`st`>> fs[state_component_equality]
      >-
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r' with <|locals := insert x'0 w0 x''.locals; stack := t|>` by
          fs[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        rw[]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])
      >>
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r' with <|locals := insert x'0 w0 x''.locals; stack := t; handler:=s.handler|>` by
          fs[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        rw[]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])))>-
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
       Q.EXISTS_TAC`fromAList lss'`>>fs[state_component_equality]>>
       Q.EXISTS_TAC`lss'`>>fs[])>>
       (*handler*)
       PairCases_on`x''`>>
       fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
       BasicProvers.EVERY_CASE_TAC>>rfs[set_var_def]>>fs[]>>
       `r'.handler = s.handler` by
       (`LENGTH s.stack +1 =
        LENGTH (StackFrame (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
         pop_assum SUBST_ALL_TAC>>
         fs[LAST_N_LENGTH]>>
         metis_tac[s_key_eq_trans,s_key_eq_sym])>>
       TRY
         (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
         (ONCE_REWRITE_TAC[CONJ_ASSOC]>>CONJ_TAC>-
         (`LENGTH s.stack +1 =
           LENGTH (StackFrame (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
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
         first_x_assum(qspec_then`frame::xs` assume_tac)>>rfs[]>>
         first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rfs[]>>
         `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
          LENGTH s.stack +1 = LENGTH (frame::xs)` by
           fs[arithmeticTheory.ADD1,s_val_eq_length]>>
          fs[LAST_N_LENGTH_cond]>>
          `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
          `lss = lss'` by fs[LIST_EQ_MAP_PAIR]>>
          fs[]>>
          last_x_assum(qspec_then `st` assume_tac)>>
          rfs[]>>HINT_EXISTS_TAC>>
          metis_tac[s_key_eq_trans,handler_eq]))>-
          (CONJ_TAC >- (
          `LENGTH s.stack +1 =
           LENGTH (StackFrame (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           fs[LAST_N_LENGTH]>>
           `LENGTH ls = LENGTH r'.stack` by fs[s_key_eq_length]>>
           fs[])>>
           IMP_RES_TAC s_key_eq_LAST_N_exists>>
           Q.EXISTS_TAC`e'''`>>
           Q.EXISTS_TAC`n`>>
           Q.EXISTS_TAC`ls'''`>>
           fs[]>>
           Q.EXISTS_TAC`lss'`>>
          (*check*)
           CONJ_TAC>-
           (`LENGTH s.stack +1 =
             LENGTH (StackFrame (list_rearrange (s.permute 0)
             (QSORT key_val_compare (toAList x')))
             (SOME (s.handler,x''2,x''3))::s.stack)` by fs[arithmeticTheory.ADD1]>>
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
           pop_assum kall_tac>>
           first_x_assum(qspec_then `frame::xs` assume_tac)>>
           rfs[]>>
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
           fs[handler_eq]>>
           HINT_EXISTS_TAC>>Q.EXISTS_TAC`fromAList lss'''`>>
           fs[handler_eq]>>
           CONJ_TAC >-
             metis_tac[handler_eq]>>
           CONJ_TAC>-
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
           first_x_assum(qspec_then`frame::xs` assume_tac)>>rfs[]>>
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
            metis_tac[handler_eq])>>
    (*Cleanup...*)
    TRY(ntac 2 strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` SUBST1_TAC)>>simp[]>>
    `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> fs[s_val_eq_def]>>Cases_on`a`>>
        Cases_on`o'`>>fs[s_frame_val_eq_def])>>
     Cases_on`handler`>>TRY(PairCases_on`x''`)>>
     fs[push_env_def,LET_THM,env_to_list_def,dec_clock_def]>>
     qpat_abbrev_tac `frame = StackFrame ls n`>>
     first_x_assum (qspec_then `frame` assume_tac)>>
     first_x_assum(qspec_then `frame::xs` assume_tac)>>
     rfs[call_env_def]>>
     `LENGTH xs = LENGTH s.stack` by fs[s_val_eq_length]>> fs[])>>
    cheat))

(*Stack swap lemma DONE*)

(*Defines some conventions for the allocator*)
val every_var_exp_def = tDefine "every_var_exp" `
  (every_var_exp P (Var num) = P num) ∧
  (every_var_exp P (Load exp) = every_var_exp P exp) ∧
  (every_var_exp P (Op wop ls) = EVERY (every_var_exp P) ls) ∧
  (every_var_exp P (Shift sh exp nexp) = every_var_exp P exp) ∧
  (every_var_exp P expr = T)`
(WF_REL_TAC `measure (exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC);

val every_var_imm_def = Define`
  (every_var_imm P (Reg r) = P r) ∧
  (every_var_imm P _ = T)`

val every_var_inst_def = Define`
  (every_var_inst P (Const reg w) = P reg) ∧
  (every_var_inst P (Arith (Binop bop r1 r2 ri)) =
    (P r1 ∧ P r2 ∧ every_var_imm P ri)) ∧
  (every_var_inst P (Arith (Shift shift r1 r2 n)) = (P r1 ∧ P r2)) ∧
  (every_var_inst P (Mem Load r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (Mem Store r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P inst = T)` (*catchall*)

val every_var_def = Define `
  (every_var P Skip = T) ∧
  (every_var P (Move pri ls) = (EVERY P (MAP FST ls) ∧ EVERY P (MAP SND ls))) ∧
  (every_var P (Inst i) = every_var_inst P i) ∧
  (every_var P (Assign num exp) = (P num ∧ every_var_exp P exp)) ∧
  (every_var P (Get num store) = P num) ∧
  (every_var P (Store exp num) = (P num ∧ every_var_exp P exp)) ∧
  (every_var P (Call ret dest args h) =
    ((EVERY P args) ∧
    (case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
      (P v ∧
      (∀x. x ∈ domain cutset ⇒ P x) ∧
      every_var P ret_handler ∧
      (*TODO: check if this is the best way to handle faulty Calls?*)
      (case h of
        NONE => T
      | SOME (v,prog,l1,l2) =>
        (P v ∧
        every_var P prog)))))) ∧
  (every_var P (Seq s1 s2) = (every_var P s1 ∧ every_var P s2)) ∧
  (every_var P (If cmp r1 ri e2 e3) =
    (P r1 ∧ every_var_imm P ri ∧ every_var P e2 ∧ every_var P e3)) ∧
  (every_var P (Alloc num numset) =
    (P num ∧ (∀x. x ∈ domain numset ⇒ P x))) ∧
  (every_var P (Raise num) = P num) ∧
  (every_var P (Return num1 num2) = (P num1 ∧ P num2)) ∧
  (every_var P Tick = T) ∧
  (every_var P (Set n exp) = every_var_exp P exp) ∧
  (every_var P p = T)`

(*Recursor for stack variables*)
val every_stack_var_def = Define `
  (every_stack_var P (Call ret dest args h) =
    (case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
      (∀x. x ∈ domain cutset ⇒ P x) ∧
      every_stack_var P ret_handler ∧
    (case h of  (*Does not check the case where Calls are ill-formed*)
      NONE => T
    | SOME (v,prog,l1,l2) =>
      every_stack_var P prog))) ∧
  (every_stack_var P (Alloc num numset) =
    (∀x. x ∈ domain numset ⇒ P x)) ∧
  (every_stack_var P (Seq s1 s2) =
    (every_stack_var P s1 ∧ every_stack_var P s2)) ∧
  (every_stack_var P (If cmp r1 ri e2 e3) =
    (every_stack_var P e2 ∧ every_stack_var P e3)) ∧
  (every_stack_var P p = T)`

val call_arg_convention_def = Define`
  (call_arg_convention (Return x y) = (y=2)) ∧
  (call_arg_convention (Raise y) = (y=2)) ∧
  (call_arg_convention (Call ret dest args h) =
    (case ret of
      NONE => args = GENLIST (\x.2*x) (LENGTH args)
    | SOME (v,cutset,ret_handler,l1,l2) =>
      args = GENLIST (\x.2*(x+1)) (LENGTH args) ∧
      (v = 2) ∧ call_arg_convention ret_handler ∧
    (case h of  (*Does not check the case where Calls are ill-formed*)
      NONE => T
    | SOME (v,prog,l1,l2) =>
      (v = 2) ∧ call_arg_convention prog))) ∧
  (call_arg_convention (Seq s1 s2) =
    (call_arg_convention s1 ∧ call_arg_convention s2)) ∧
  (call_arg_convention (If cmp r1 ri e2 e3) =
    (call_arg_convention e2 ∧
     call_arg_convention e3)) ∧
  (call_arg_convention p = T)`

(*TODO: fix these (should probably be defined elsewhere) *)
val is_stack_var_def = Define`is_stack_var = ARB`;
val is_phy_var_def = Define`is_phy_var = ARB`;

val pre_alloc_conventions_def = Define`
  pre_alloc_conventions p =
    (every_stack_var is_stack_var p ∧
    call_arg_convention p)`

val post_alloc_conventions_def = Define`
  post_alloc_conventions k prog =
    (every_var is_phy_var prog ∧
    every_stack_var (λx. x ≥ 2*k) prog ∧
    call_arg_convention prog)`

(*Monotonicity*)
val every_var_inst_mono = store_thm("every_var_inst_mono",``
  ∀P inst Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_inst P inst
  ⇒
  every_var_inst Q inst``,
  ho_match_mp_tac (fetch "-" "every_var_inst_ind")>>rw[every_var_inst_def]>>
  Cases_on`ri`>>fs[every_var_imm_def])

val every_var_exp_mono = store_thm("every_var_exp_mono",``
  ∀P exp Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_exp P exp
  ⇒
  every_var_exp Q exp``,
  ho_match_mp_tac (fetch "-" "every_var_exp_ind")>>rw[every_var_exp_def]>>
  fs[EVERY_MEM])

val every_var_mono = store_thm("every_var_mono",``
  ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_var P prog
  ⇒
  every_var Q prog``,
  ho_match_mp_tac (fetch "-" "every_var_ind")>>rw[every_var_def]>>
  TRY(Cases_on`ret`>>fs[]>>PairCases_on`x`>>Cases_on`h`>>fs[]>>Cases_on`x`>>fs[])>>
  TRY(Cases_on`r`>>fs[])>>
  TRY(Cases_on`ri`>>fs[every_var_imm_def])>>
  metis_tac[EVERY_MONOTONIC,every_var_inst_mono,every_var_exp_mono])

(*Conjunct*)
val every_var_inst_conj = store_thm("every_var_inst_conj",``
  ∀P inst Q.
  every_var_inst P inst ∧ every_var_inst Q inst ⇔
  every_var_inst (λx. P x ∧ Q x) inst``,
  ho_match_mp_tac (fetch "-" "every_var_inst_ind")>>rw[every_var_inst_def]>>
  TRY(Cases_on`ri`>>fs[every_var_imm_def])>>
  metis_tac[])

val every_var_exp_conj = store_thm("every_var_exp_conj",``
  ∀P exp Q.
  every_var_exp P exp ∧ every_var_exp Q exp ⇔
  every_var_exp (λx. P x ∧ Q x) exp``,
  ho_match_mp_tac (fetch "-" "every_var_exp_ind")>>rw[every_var_exp_def]>>
  fs[EVERY_MEM]>>
  metis_tac[])

val every_var_conj = store_thm("every_var_conj",``
  ∀P prog Q.
  every_var P prog  ∧ every_var Q prog ⇔
  every_var (λx. P x ∧ Q x) prog``,
  ho_match_mp_tac (fetch "-" "every_var_ind")>>rw[every_var_def]>>
  TRY(Cases_on`ret`>>fs[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>fs[])>>
  TRY(Cases_on`x`>>fs[])>>
  TRY(Cases_on`r`>>fs[])>>
  TRY(Cases_on`ri`>>fs[every_var_imm_def])>>
  TRY(metis_tac[EVERY_CONJ,every_var_inst_conj,every_var_exp_conj]))

(*Similar lemmas about every_stack_var*)
val every_var_imp_every_stack_var = store_thm("every_var_imp_every_stack_var",``
  ∀P prog.
  every_var P prog ⇒ every_stack_var P prog``,
  ho_match_mp_tac (fetch"-" "every_stack_var_ind")>>
  rw[every_stack_var_def,every_var_def]>>
  Cases_on`ret`>>
  Cases_on`h`>>fs[]>>
  PairCases_on`x`>>fs[]>>
  Cases_on`x'`>>Cases_on`r`>>fs[])

val every_stack_var_mono = store_thm("every_stack_var_mono",``
  ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_stack_var P prog
  ⇒
  every_stack_var Q prog``,
  ho_match_mp_tac (fetch "-" "every_stack_var_ind")>>rw[every_stack_var_def]>>
  TRY(Cases_on`ret`>>fs[]>>PairCases_on`x`>>Cases_on`h`>>fs[]>>Cases_on`x`>>Cases_on`r`>>fs[]))

val every_stack_var_conj = store_thm("every_stack_var_conj",``
  ∀P prog Q.
  every_stack_var P prog  ∧ every_stack_var Q prog ⇔
  every_stack_var (λx. P x ∧ Q x) prog``,
  ho_match_mp_tac (fetch "-" "every_stack_var_ind")>>rw[every_stack_var_def]>>
  TRY(Cases_on`ret`>>fs[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>fs[])>>
  TRY(Cases_on`x`>>Cases_on`r`>>fs[])>>
  TRY(metis_tac[EVERY_CONJ]))

val _ = export_theory();
