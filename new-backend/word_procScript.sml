open HolKernel Parse boolLib bossLib miscLib word_langTheory
open listTheory sptreeTheory pred_setTheory pairTheory
val _ = new_theory "word_proc";

(*Coloring expressions*)
val apply_color_exp_def = tDefine "apply_color_exp" `
  (apply_color_exp f (Var num) = Var (f num)) /\
  (apply_color_exp f (Load exp) = Load (apply_color_exp f exp)) /\
  (apply_color_exp f (Op wop ls) = Op wop (MAP (apply_color_exp f) ls)) /\
  (apply_color_exp f (Shift sh exp nexp) = Shift sh (apply_color_exp f exp) nexp) /\
  (apply_color_exp f expr = expr)`
(WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC);

(*Apply f to the keys of a num_map, numsets are special cases with values ()*)
val apply_nummap_key_def = Define `
  apply_nummap_key f nummap = fromAList (
                                 ZIP (MAP (f o FST) (toAList nummap),
                                      MAP SND (toAList nummap)))`

val apply_numset_key_def = Define `
  apply_numset_key f (numset:num_set) = apply_nummap_key f numset`


(*Color a prog*)
val apply_color_def = Define `
  (apply_color f Skip = Skip) /\
  (apply_color f (Move ls) = 
    Move (ZIP (MAP (f o FST) ls, MAP (f o SND) ls))) /\
  (apply_color f (Assign num exp) = Assign (f num) (apply_color_exp f exp)) /\
  (apply_color f (Store exp num) = Store (apply_color_exp f exp) (f num)) /\
  (apply_color f (Call ret dest args h) = 
    let ret = case ret of NONE => NONE 
                        | SOME (v,cutset) => 
                             SOME (f v,apply_nummap_key f cutset) in
    let args = MAP f args in
    let h = case h of NONE => NONE
                     | SOME (v,prog) => SOME (f v, apply_color f prog) in
      Call ret dest args h) /\
  (apply_color f (Seq s1 s2) = Seq (apply_color f s1) (apply_color f s2)) /\
  (apply_color f (If e1 num e2 e3) = 
    If (apply_color f e1) (f num) (apply_color f e2) (apply_color f e3)) /\
  (apply_color f (Alloc num numset) = 
    Alloc (f num) (apply_nummap_key f numset)) /\
  (apply_color f (Raise num) = Raise (f num)) /\
  (apply_color f (Return num) = Return (f num)) /\ 
  (apply_color f Tick = Tick) /\
  (apply_color f (Set n exp) = Set n (apply_color_exp f exp)) /\
  (apply_color f p = p )
`
val _ = export_rewrites ["apply_nummap_key_def","apply_color_exp_def","apply_color_def"];

(*
EVAL ``apply_color (\x.x+1) (Seq (Call (SOME (5,LN)) (SOME 4) [3;2;1] NONE) Skip)``
*)
(*Note that we cannot use get_var v s = get_var f v t because t is allowed to contain extra variables ==> get_var (f v) t may succeed*)

(*Helpful:
   traces();
   Goalstack.print_goal_fvs := 1;
    show_types:=true;
    show_types:=false; Or use HJ
 *)

(*Prove that mapping injective f over an exp + initial state gives the same result*)

(*Prove 2 side conditions on the semantics that help in the Call case
               1
wEval(prog,st) ==> (res,rst)
  ||                  || 2
  \/                  \/
wEval(prog,st') ==> (res',rst')

1) Show that st,rst have the same keys on stack and in the case of 

   where does SOME Exception go?? the locals??

2) Show that rst,rst' have the same values on the stack
*)
(*Abbrev the and away to make the proofs easier to handle..*)
val abbrev_and_def = Define`
  abbrev_and a b <=> a /\ b`

val wf_stack_def = Define`
  (wf_stack st 0 = T) /\
  (wf_stack st n = 
    case LAST_N (n+1) st of 
      StackFrame ls (SOME y)::xs => wf_stack xs y
    | _ => F)`,
WF_REL_TAC `measure LENGTH`
    
(*If wEval goes to 
  NONE/SOME result then the resulting stack must be stack_key_eq_rel 
  to the starting stack i.e. successful programs do not disturb the stack
  
  SOME Exception --> resulting stack is popped exactly according to st.handler*)


(*LAST_N lemma*)
val LAST_N_lemma = prove(
  ``!x y ls xs. LAST_N x ls = xs /\ xs <> [] ==>LAST_N x (y::ls) = xs``,
  strip_tac>>strip_tac>>Induct>>
  strip_tac>>
  `xs = []` >>
  fs[bvpTheory.LAST_N_def]

 rw[]














(*wEval of a prog should retain the keys of the stack
Unless there is SOME Exception in which case it should exactly retain the remainder of the stack after handle (AND the locals must be popped)
*)
val wEval_s_key_eq = prove(
  ``!prog st res rst. 
      wEval (prog,st) = (res,rst) /\ (st.handler < LENGTH st.stack) ==>
         case res of NONE => s_key_eq st.stack rst.stack /\ 
                             rst.handler = st.handler
                             (*implies rst.handler < LENGTH rst.stack*)
         |  SOME (Result x) => s_key_eq st.stack rst.stack /\
                               rst.handler = st.handler
         |  SOME (Exception x)=> 
              (case LAST_N (st.handler+1) st.stack of
              StackFrame ls (SOME y) :: xs =>
                s_key_eq xs rst.stack /\
                MAP FST ls = MAP FST (toAList rst.locals) /\
                rst.handler = y
              | _ => F) /\
              rst.handler < LENGTH rst.stack 
              (*In exceptional cases the stack is exactly popped and 
                the locals are exactly corresponding*)
         | _ => T (*not entirely sure about the other cases*)``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>-
  (*Skip*)
  (fs[wEval_def,s_key_eq_refl]>>rw[])>-

  (*Alloc*)

  (*Raise*)
  fs[wEval_def]>>
  qpat_assum `x = y` mp_tac>>
  BasicProvers.EVERY_CASE_TAC>>fs[jump_exc_def]>>
  rw[]>-
    fs[s_key_eq_refl]>-
    cheat>- (*This might be a problem...*)
    fs[]>-
     

  (*Call 10hR*)
  pop_assum mp_tac>>pop_assum mp_tac>>
  fs[wEval_def]>>IF_CASES_TAC>-(rw[abbrev_and_def]>>fs[])>>
  Cases_on`get_vars args st`>> fs[]>-
    (rw[]>>fs[optionTheory.option_nchotomy])>>
  Cases_on`find_code dest x st.code`>>fs[]>-
    (rw[]>>fs[optionTheory.option_nchotomy])>>
  Cases_on`x'`>>fs[]>>Cases_on`ret`>>fs[]>-
    (*NONE - Tail call*)
    (IF_CASES_TAC>-
      (BasicProvers.EVERY_CASE_TAC>>rfs[]>>rw[]>>
      `(call_env q (dec_clock st)).stack = st.stack` by
         fs[dec_clock_def,call_env_def]>>
      `(call_env q (dec_clock st)).handler = st.handler` by
         fs[dec_clock_def,call_env_def]>>
      fs[]>> rfs[]>>Cases_on`x'`>>fs[])>>
    rw[]>>fs[] )>>
    (*SOME - Returning Call*)
    Cases_on`x'`>>simp[]>>Cases_on`cut_env r' st.locals`>-(rw[]>>fs[])>>
    fs[]>>
    CASE_TAC>>fs[]>-
      (*NO HANDLER*)
      (
      Cases_on`wEval (r,call_env q (push_env x' F (dec_clock st)))`>>
      Cases_on`q''`>>rw[]>>fs[]>>
      Cases_on`x''`>>fs[]>>rw[]>>
      `(call_env q (push_env x' F (dec_clock st))).handler <
      LENGTH (call_env q (push_env x' F (dec_clock st))).stack` by
      (fs[dec_clock_def,push_env_def,call_env_def,LET_THM,env_to_list_def]>>
      simp[])>-
        (*Result*)
        (Cases_on`pop_env r''`>>fs[]>>rw[]>>
        Cases_on`domain x''.locals = domain x'`>>fs[]>>rw[]>-
        (`s_key_eq (push_env x' F (dec_clock st)).stack r''.stack` by
          fs[call_env_def]>>
        IMP_RES_TAC push_env_pop_env_s_key_eq >> fs[dec_clock_def]>>
        rw[set_var_def])>>
        rw[set_var_def]>>
        fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
        `x''.handler = r''.handler` by cheat>>fs[])>>
         (*Argument:
           r''.stack's head is s_key_eq to a push_env .. F... 
           therefore it is SOME NONE therefore the handler is unchanged 
           therefore x''.handler = r''.handler*)
        (*exception*) 
        (fs[]>> cheat)>>fs[])>>
        (*Argument:
          since st.handler < LENGTH st.stack
          we have that LAST_N st.handler (_::st.stack) = 
                       LAST_N st.handler st.stack
          also the handler is unchanged in the push_env ..F...
          therefore, can just use assum 6 immediately*)
      (*SOME HANDLER*)
      Cases_on`wEval(r,call_env q (push_env x' T (dec_clock st)))`>>
      Cases_on`q''`>>fs[]>>rw[]>>fs[]>>
      Cases_on`x'''`>>fs[]>>rw[]>>
      `(call_env q (push_env x' T (dec_clock st))).handler <
      LENGTH (call_env q (push_env x' T (dec_clock st))).stack` by
      (fs[dec_clock_def,push_env_def,call_env_def,LET_THM,env_to_list_def]>>
      simp[])>-
        (*Result*)
        (Cases_on`pop_env r''`>>fs[]>>rw[]>>
        Cases_on`domain x''.locals = domain x'`>>fs[]>>rw[]>-
        (`s_key_eq (push_env x' T (dec_clock st)).stack r''.stack` by
          fs[call_env_def]>>
        IMP_RES_TAC push_env_pop_env_s_key_eq >> fs[dec_clock_def]>>
        rw[set_var_def])>>
        rw[set_var_def]>>
        fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
        cheat)>> 
        (*Argument: 
          since r'' is skey_eq to SOME st.handler :: xs then 
          the pop_env should be exactly equal to st.handler*)       
        (*Exception
        First prove this condition using assum 4 and 9
        Argument: push_env ... T ... 
        pushes a handler exactly*)
        `s_key_eq st.stack r''.stack /\
         (*MAP FST (toAList x') = MAP FST (toAList r''.locals) /\*)
         r''.handler = st.handler` by cheat>>
         Cases_on`x''`>>Cases_on`domain r''.locals = domain x'`>>fs[]>>rw[]>>
         Cases_on`res`>>fs[]>-
           (fs[set_var_def]>>rfs[]>>metis_tac[s_key_eq_trans])>>
         Cases_on`x''`>>fs[set_var_def]>>rfs[]>- metis_tac[s_key_eq_trans]>>
         cheat>> (*use assum 7 and s_key_eq is an equivalence*)





      BasicProvers.EVERY_CASE_TAC     

       CASE_TAC>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rfs[]>>
      fs[]
       fs[]>>BasicProvers.FULL_CASE_TAC>>
      BasicProvers.FULL_CASE_TAC>>
      

CASE_TAC>>rw[]>>fs[]>>Cases_on`q''`


BasicProvers.EVERY_CASE_TAC>>fs[s_key_eq_def]
 (fs[wEval_def,stack_key_eq_rel_refl]>>BasicProvers.EVERY_CASE_TAC>>fs[])>-
 fs[wEval_def,wAlloc_def] >> first_x_assum mp_tac>> BasicProvers.EVERY_CASE_TAC>>
 IMP_RES_TAC wGC_stack_key_eq_rel

(*Relation over states parameterized by f*)

(*For NONE results, the strong state rel should hold*)
val strong_state_rel_def = Define`
  strong_state_rel f s t <=> 
  t.store = s.store /\
  t.stack = s.stack /\
  t.memory = s.memory /\
  t.mdomain = s.mdomain /\
  t.permute = s.permute /\
  t.gc_fun = s.gc_fun /\
  t.handler = s.handler /\
  t.clock = s.clock /\
  t.code = s.code /\
  t.output = s.output /\
  !n v. (lookup n s.locals = SOME v) ==> (lookup (f n) t.locals = SOME v)`

(*For SOME results, the weak state rel should hold*)
val weak_state_rel_def = Define`
  weak_state_rel f s t <=> (t=s \/ strong_state_rel f s t)`

val strong_imp_weak_state_rel = prove
  (``!f s t. strong_state_rel f s t ==> weak_state_rel f s t``,
     rw[strong_state_rel_def,weak_state_rel_def])

val strong_state_rel_get_var_lemma = prove(
  ``!f s t v x. strong_state_rel f s t /\ get_var v s = SOME x
    ==> get_var (f v) t = SOME x``,
    fs[strong_state_rel_def,get_var_def]>>
    metis_tac[])

val strong_state_rel_get_vars_lemma = prove(
  ``!f s t ls x. strong_state_rel f s t /\ get_vars ls s = SOME x
    ==> get_vars (MAP f ls) t = SOME x``,
  strip_tac>>strip_tac>>strip_tac>>Induct >>
  fs[get_vars_def,strong_state_rel_def,get_var_def]>>
  rw[]>> Cases_on`lookup h s.locals`>>fs[]>>
  `lookup (f h) t.locals = SOME x'` by metis_tac[]>> fs[]>>
  Cases_on`get_vars ls s`>>fs[])

val strong_state_rel_set_var_lemma = prove(
  ``!f s t v x. INJ f UNIV UNIV /\ strong_state_rel f s t ==> 
                strong_state_rel f (set_var v x s) (set_var (f v) x t)``,
   rw[strong_state_rel_def,set_var_def]>>fs[strong_state_rel_def]>>
   Cases_on`n=v`>>fs[lookup_insert]>>
   `f n <> f v` by (fs[INJ_DEF]>>metis_tac[])>>
   simp[])

val strong_state_rel_set_vars_lemma = prove(
   ``!f s t vs xs. INJ f UNIV UNIV /\ strong_state_rel f s t 
                   /\ LENGTH vs = LENGTH xs ==>
                 strong_state_rel f (set_vars vs xs s) 
                                    (set_vars (MAP f vs) xs t)``,
   Induct_on`vs`>>
   fs[set_vars_def,list_insert_def
      ,word_state_component_equality,strong_state_rel_def]>>
   rw[list_insert_def]>>
   Cases_on `xs`>>fs[list_insert_def]>>
   Cases_on`n=h`>>fs[lookup_insert]>>
   `f n <> f h` by (fs[INJ_DEF]>>metis_tac[])>>
   last_x_assum(qspecl_then [`f`,`s`,`t`,`t'`] assume_tac)>>
   simp[])

val get_vars_length_lemma = prove(
  ``!ls s y. get_vars ls s = SOME y ==>
           LENGTH y = LENGTH ls``,
  Induct>>fs[get_vars_def]>>
  Cases_on`get_var h s`>>fs[]>>
  Cases_on`get_vars ls s`>>fs[]>>
  metis_tac[LENGTH])

val get_var_top_of_stack_lemma = prove(
  ``!v s s'. s.locals = s'.locals ==> get_var v s = get_var v s'``,
  rw[get_var_def])

val get_vars_top_of_stack_lemma = prove(
  ``!l s s'. s.locals = s'.locals ==> get_vars l s = get_vars l s'``,
  Induct>>rw[get_vars_def]>>
  `get_var h s = get_var h s'` by fs[get_var_top_of_stack_lemma]>>
  Cases_on`get_var h s'`>>fs[]>> 
  Cases_on`get_vars l s`>>metis_tac[])

val MEM_fromAList = store_thm ("MEM_fromAList",
  ``∀t k. MEM k (MAP FST t) <=> 
          k IN domain (fromAList t) ``,
  Induct_on`t`>> rw[fromAList_def]>>
  Cases_on`h`>> Cases_on`q=k`>>rw[fromAList_def])

val lookup_apply_nummap_key = prove(
  ``!f t z. INJ f UNIV UNIV ==>
     lookup (f z) (apply_nummap_key f t) = lookup z t``,cheat)
 
(*cutting the environment on strongly related locals returns locals where equality is true*)
val cut_env_lemma = prove(
  ``!names sloc tloc x f. INJ f UNIV UNIV /\ cut_env names sloc = SOME x /\
    (!n v. (lookup n sloc = SOME v) ==> (lookup (f n) tloc = SOME v))
    ==> (?y. cut_env (apply_nummap_key f names) tloc = SOME y /\
        !z. lookup z x = lookup (f z) y)``,
    rw[cut_env_def]>-
    (*domain*)
    (simp[SUBSET_DEF]>>
    strip_tac>>
    disch_then(mp_tac o MATCH_MP(snd(EQ_IMP_RULE(SPEC_ALL MEM_fromAList))))>>
    simp[MAP_ZIP,MEM_MAP]>>rw[]>>
    fs[MEM_ZIP,EL_MAP]>>
    qmatch_abbrev_tac`f x IN s` >>
    `∃v. lookup x names = SOME v`
       by metis_tac[MEM_toAList,MEM_EL,
                    pairTheory.pair_CASES,pairTheory.FST] >>
    `?v. lookup x sloc = SOME v` by metis_tac[domain_lookup,SUBSET_DEF]>>
    metis_tac[domain_lookup])>>
    (*lookup*)
    simp[lookup_inter]>> Cases_on`lookup z sloc`>-
      (*NONE*)
      (simp[]>>Cases_on`lookup (f z) tloc`>>simp[]>>
      `lookup z names = NONE` by 
        metis_tac[SUBSET_DEF,lookup_NONE_domain]>>
      BasicProvers.EVERY_CASE_TAC>>fs[]>>
      IMP_RES_TAC domain_lookup>> IMP_RES_TAC MEM_fromAList>>
      fs[MEM_MAP,MAP_ZIP,MEM_ZIP]>>
      rw[]>>fs[EL_MAP]>>
      `z = FST (EL n (toAList names))` by fs[INJ_DEF]>>
      `∃v. lookup z names = SOME v`
       by metis_tac[MEM_toAList,MEM_EL,
                    pairTheory.pair_CASES,pairTheory.FST] >>fs[])>>
       (*SOME*)
       simp[]>>
       (*Match assumption and pop*)
       first_assum(fn th => first_x_assum(assume_tac o C MATCH_MP th)) >> 
       fs[]>>
       IMP_RES_TAC (INST_TYPE [``:'a``|->``:unit``] 
         lookup_apply_nummap_key)>>fs[])


(*wEval of same prog with different top of stack gives the same result*)
val pop_assum_wEval =
   fs[wEval_def]>> first_x_assum mp_tac>>last_x_assum mp_tac
   
(*Looking at 2 stacks:
  If the only difference in states is the stack and the stacks only differ in the (top of stack's (values)


  The top element must be "equivalent" ALists on the values
Preconditions:
  Top of stack should differ only on keys and handler either both exist 
  or both not exist
  Don't care about NONE case..
*)
val enc_stack_push_env = prove(
  ``!x b s s'. s.permute = s'.permute ==>(
      enc_stack (push_env x b s).stack = enc_stack(push_env x b s').stack <=>
      enc_stack s.stack = enc_stack s'.stack)``,
  fs[push_env_def,LET_THM,env_to_list_def] >> rw[enc_stack_def])

val enc_stack_set_store = prove(
  ``!s s' a w. s.permute = s'.permute ==> (
     enc_stack(set_store a w s).stack = enc_stack(set_store a w s').stack <=>
     enc_stack s.stack = enc_stack s'.stack)``,
  fs[set_store_def])

(*Split into NONE and SOME cases*)
val wEval_stack_no_handler_lemma = prove(
  ``!prog state res rst hd handler tl hd'.
      wEval(prog,state) = (res,rst) /\
      res <> NONE /\ res <> SOME Error /\
      state.stack = (StackFrame hd NONE)::tl /\
      rst.stack = (StackFrame hd' NONE)::tl' /\
      MAP SND hd' = MAP SND hd
  ==>
   ?rst'.
    wEval(prog,state with stack:= (StackFrame hd' NONE)::tl) = (res,rst') /\
    case res of 
      SOME (Result x) =>
        ?rhd rtl rhd'.
          rst.stack = (StackFrame rhd NONE)::rtl /\
          domain (fromAList rhd) = domain (fromAList hd) /\
          rst'.stack = (StackFrame rhd' NONE)::rtl /\
          MAP SND rhd' = MAP SND rhd
    | SOME (Exception x) => rst =rst'``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>-
  (*Skip*)
  fs[wEval_def]>-
  (*Alloc*)
  fs[wEval_def]>>
  Cases_on`get_var n state`>>fs[]>>
  `get_var n (state with stack := StackFrame hd' NONE::tl) = SOME x` by
    fs[get_var_def]>>
  BasicProvers.FULL_CASE_TAC>>fs[]>>
  BasicProvers.FULL_CASE_TAC>>fs[wAlloc_def]>>
  BasicProvers.FULL_CASE_TAC>>fs[]>>
  fs[wGC_def,LET_THM]
  first_x_assum mp_tac>>
  qpat_abbrev_tac `ls = push_env a F rest`>>
  qpat_abbrev_tac `ls' = push_env a F rest`>>
  `enc_stack ls.stack = enc_stack ls'.stack` by  
    (Q.UNABBREV_TAC`ls`>>
    Q.UNABBREV_TAC`ls'`>>
    assume_tac enc_stack_push_env>>
    qpat_abbrev_tac `st = set_store a w s`>>
    qpat_abbrev_tac `st = set_store a w s`>>
    first_x_assum(qspecl_then [`x`,`F`,`st`,`st'`] assume_tac)>>
    Q.UNABBREV_TAC`st`>>Q.UNABBREV_TAC`st'`>>fs[set_store_def]>>
    fs[enc_stack_def])>>
    pop_assum(SUBST1_TAC o SYM) >>
    `ls'.gc_fun = ls.gc_fun /\ ls'.memory=ls.memory /\ 
     ls'.mdomain = ls.mdomain /\ ls'.store = ls.store` by
    (Q.UNABBREV_TAC`ls`>>Q.UNABBREV_TAC`ls'`>>
    fs[push_env_def,set_store_def,env_to_list_def]>>simp[])>>
    fs[]>>
    BasicProvers.FULL_CASE_TAC>>fs[]>>
    BasicProvers.FULL_CASE_TAC>>fs[]>>
    Cases_on`q`>-(
      Q.UNABBREV_TAC `ls`>>
      fs[push_env_def,LET_THM,NOT_NIL_CONS,env_to_list_def,set_store_def,dec_stack_def]
    `
    fs[push_env_def,set_store_def]
    Cases_on`ls.stack`>-(
      fs[push_env_def,LET_THM,set_store_def]>>
      fs[env_to_list_def,LET_THM]>>
      Q.UNABBREV_TAC`ls`>>
      fs[NOT_NIL_CONS])>>
    Cases_on`ls'.stack`>-(
       fs[push_env_def,LET_THM,set_store_def]>>
       fs[env_to_list_def,LET_THM]>>
       Q.UNABBREV_TAC`ls'`>>
       fs[NOT_NIL_CONS])>>
    Cases_on`h`>>fs[enc_stack_def]>>
    Cases_on`h'`>>fs[enc_stack_def]
    fs[
      `ls.stack <> []` by 
        Q.UNABBREV_TAC`ls`>>fs[env_to

BasicProvers.FULL_CASE_TAC>>
Q.UNABBREV_TAC`ls`>>Q.UNABBREV_TAC`ls'`>>fs[set_store_def,push_env_def,LET_THM]
  fs[push_env_def,set_store_def,wGC_def,LET_THM]>>
  
first_x_assum mp_tac>>
  qpat_abbrev_tac `X = wGC s`>>
  qpat_abbrev_tac `X' = wGC s`>>
  Cases_on `X`>> fs[] 

BasicProvers.FULL_CASE_TAC>>fs[]
 


(*not too sure about the assum for toAList x and toAList y yet*)
(*If res is a result, then the result states differ only in head keys*)
val wEval_top_of_stack_lemma = prove(
  ``!prog st rst res x y rst' locs b.
      wEval(prog,call_env locs (push_env x b st)) = (res,rst) /\
      MAP SND (toAList x) = MAP SND (toAList y) 
      /\res<>NONE /\ res <> SOME Error
   ==>
      ?rst'.
      wEval(prog,call_env locs (push_env y b st)) = (res,rst') /\ 
      case res of 
      SOME (Result _) =>
        (let prst = THE (pop_env rst) in
        let prst' = THE (pop_env rst') in
          domain prst.locals = domain x /\
          domain prst'.locals = domain y /\
          !z. lookup z prst.locals = lookup z prst'.locals
         (*word_states_match_except_locals rst rst'
           may need  that the popped envs are SOME?*))
    | SOME (Exception _) => 
        (case b of 
          T => domain rst.locals = domain x /\
               domain rst'.locals = domain y /\
               !z. lookup z rst.locals = lookup z rst'.locals
               (*word_states_match_except_locals rst rst'*)
        | F => rst = rst' (*Popped past, locals already set so eq*))``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> fs[call_env_def,LET_THM,env_to_list_def]>>
  rw[]>>Q.ABBREV_TAC`hand = if b then SOME st.handler else NONE`>>
  fs[push_env_def]>>
  >- 
  fs[wEval_def]>-
  fs[wEval_def,get_var_def]>>
  BasicProvers.TOP_CASE_TAC>>fs[]>>
  BasicProvers.TOP_CASE_TAC>>fs[wAlloc_def]>> 
  BasicProvers.TOP_CASE_TAC>>fs[wGC_def,LET_THM]>>
  BasicProvers.TOP_CASE_TAC>>fs[] >- cheat (*prove somewhere that the gc_funs will be the same result*)>>
  BasicProvers.TOP_CASE_TAC>>fs[]
 
  (*Call*)
  fs[wEval_def,LET_THM]>>
  BasicProvers.TOP_CASE_TAC>>fs[] 

st with stack:= (StackFrame (toAList x) h)::tl ) 
        = (res,rst) /\
      (∀z. lookup z x = lookup (f z) y )/\
      T /\ (*need properties on fmonotonicity*)
      (h = NONE <=> h' = NONE) /\
      res <> SOME Error /\ res <> NONE
      ==>
      (abbrev_and 
      (wEval(prog,st with stack:= (StackFrame (toAList y) h')::tl) 
         = (res,rst'))
      (case res of 
          SOME(Exception x') =>
            (*If raised an exception, check if there's a handler*) 
            (case hd of StackFrame x NONE => rst' = rst (*handler goes past*)
            |           StackFrame x (SOME h) =>
                          strong_state_rel f rst rst') 
                       (*Need some condition here*)
        | SOME (Result x') => T
           (* ?nst. rst' = rst with stack:= nst /\
            HD nst = StackFrame
              case HD rst.stack of
                StackFrame z _ => domain fromAList z = domain x
             rst' = rst with stack:= (StackFrame (
             HD rst'.stack = head /\

              rst.stack = rst'.stack /\
             domain(
             domain(THE (pop_env y)) = domain x
          /\ domain(THE (pop_env_clock= SOME s1
               domain y.locals = domain x*)
        | _ => rst'=rst))
        (*I think there should be an extra condition in this case*)``,
   ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[]>-
    (*Skip*)
    fs[wEval_def,abbrev_and_def]>-
    (*Alloc*)
    pop_assum_wEval>>
    BasicProvers.FULL_CASE_TAC>>fs[]>>
    `get_var n (st with stack := StackFrame (toAList y) h''::tl) = SOME x` by 
      fs[get_var_def]>> fs[]
    BasicProvers.FULL_CASE_TAC>>fs[wAlloc_def]>>
    BasicProvers.FULL_CASE_TAC>>fs[]
    fs[wGC_def,enc_stack_def,push_env_def,set_store_def,env_to_list_def]

>>metis_tac[]
     BasicProvers.FULL_CASE_TAC>>fs[]>>
     BasicProvers.FULL_CASE_TAC>>fs[wAlloc_def]>>
     BasicProvers.FULL_CASE_TAC>>fs[] 
     Cases_on`get_var n st`>>fs[]>>
     Cases_on`x`>>fs[wAlloc_def]>>
     Cases_on`cut_env names st.locals`>>fs[]>> 
     Q.ABBREV_TAC `ns = push_env x F (set_store AllocSize (Word c) st)`>>
     Q.ABBREV_TAC `ns2 = push_env x F (set_store AllocSize (Word c)
                 (st with stack := hd::TL st.stack))`>>
     `ns.gc_fun = ident_gc /\ ns2.gc_fun = ident_gc` by 
       CONJ_TAC>> Q.UNABBREV_TAC`ns` >>Q.UNABBREV_TAC `ns2`>>
       simp[push_env_def,set_store_def]
     `wGC (push_env x F (set_store AllocSize (Word c) st))`
     fs[push_env_def,set_store_def,ident_gc_wGC,word_state_component_equality]
     wGC_def,push_env_def]
    (rpt strip_tac >> fs[wEval_def])>>
   strip_tac>-(
     rpt strip_tac >>fs[wEval_def,LET_THM] >>
     fs[wAlloc_def,get_var_def]>>
     Cases_on`lookup n st.locals`>>fs[]
     Cases_on`x`>>fs[]>> 
     Cases_on`cut_env names st.locals`>>fs[]>>
     
     BasicProvers.EVERY_CASE_TAC>>fs[]

 rw[]>>
     
    rpt strip_tac >>
    >> BasicProvers.EVERY_CASE_TAC>>fs[]
  >>rpt strip_tac>>fs[wEval_def,LET_THM]>-
    (BasicProvers.EVERY_CASE_TAC>>fs[])>-
    (BasicProvers.EVERY_CASE_TAC>>fs[])>-
    (BasicProvers.EVERY_CASE_TAC>>fs[])>-
    (BasicProvers.EVERY_CASE_TAC>>fs[])>-
      Cases_on`st.clock=0`>>fs[call_env_def,LET_THM]>>rw[EQ_SYM_EQ]>>
      `get_vars l (st with stack := hd :: TL st.stack) =
       get_vars l st` by fs[get_vars_top_of_stack_lemma] >> fs[]
      Cases_on`get_vars l st`>>fs[get_vars_def]>>
      Cases_on`find_code o0 x st.code`>>fs[]>> Cases_on`x'`>>fs[]>>
      Cases_on`o1`>>fs[]>-
        (*NONE*)


    BasicProvers.EVERY_CASE_TAC>>fs[call_env_def,LET_THM]>-
    
  rw[wEval_def]>>fs[]
      


)      

           case res of SOME (Exception x') ==> 

val get_var_tactic = 
  Cases_on`get_var n st`>>fs[]>>
  `get_var (f n) cst = SOME x` by 
  metis_tac[strong_state_rel_get_var_lemma];

(*Prove that mapping (doesnt need to be injective) f over an exp + initial state vars gives the same result and a new state which contains mapped vars*)
val inj_apply_color_exp_invariant = store_thm("inj_apply_color_exp_invariant",
  ``!st exp cst f res. word_exp st exp = SOME res 
                        /\ strong_state_rel f st cst
    ==> word_exp cst (apply_color_exp f exp) = SOME res``,
  ho_match_mp_tac word_exp_ind>>rw[]>>
  fs[word_exp_def,apply_color_exp_def,strong_state_rel_def]>-
    (Cases_on`lookup st' st.locals`>>fs[]>>
      Cases_on`x`>>`lookup (f st') cst.locals = lookup st' st.locals` by 
      fs[strong_state_rel_def] >> fs[]) >-
    (Cases_on`word_exp st exp`>>fs[]>>
    `mem_load x st = mem_load x cst` by 
      fs[mem_load_def]>>fs[])>-
    (fs[LET_THM]>> 
    `MAP (\a.word_exp st a) wexps = 
     MAP (\a.word_exp cst a) (MAP (\a. apply_color_exp f a) wexps)` 
     by  (
       simp[MAP_MAP_o] >>
       simp[MAP_EQ_f] >>
       gen_tac >>
       strip_tac >>
       first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
       fs[EVERY_MEM,MEM_MAP,PULL_EXISTS
         ,miscTheory.IS_SOME_EXISTS] >>
       pop_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
       strip_tac >>
       disch_then(qspec_then`cst`mp_tac) >> simp[] ) >>
     pop_assum(SUBST1_TAC o SYM) >>
     simp[EQ_SYM_EQ] )
     >>
    Cases_on`word_exp st exp`>>fs[])
 
(*Prove that mapping injective f over a prog + initial state variables gives the same result and a new state which contains mapped vars*)
val inj_apply_color_invariant = store_thm ("inj_apply_color_invariant",
  ``!prog st rst f cst res. 
                  wEval(prog,st) = (res,rst) 
                  /\ INJ f UNIV UNIV
                  /\ res <> SOME Error
                  (*/\ wf st.locals*)
                  /\ strong_state_rel f st cst ==>
     let (res',rcst) = wEval(apply_color f prog,cst) in
     (res' = res) /\
      (case res of
        NONE => strong_state_rel f rst rcst
      | SOME _ => weak_state_rel f rst rcst)``
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[] 
  (*Induct>> rpt strip_tac>>simp[]>-*)
Cases_on`o'`>>Cases_on`x`
   (*Skip*)
    (rw[abbrev_and_def,apply_color_def,wEval_def,EQ_SYM_EQ]>>fs[wEval_def]>>
    rw[EQ_SYM_EQ]) >-
   (*Alloc*)
    (pop_assum_wEval>>BasicProvers.FULL_CASE_TAC>>
    IMP_RES_TAC strong_state_rel_get_var_lemma>> fs[]>>
    Cases_on`x`>>fs[wAlloc_def]>>
    Cases_on`cut_env names st.locals`>> fs[strong_state_rel_def]>>
    IMP_RES_TAC cut_env_lemma>>fs[]>> 
    qpat_abbrev_tac`X = set_store a w t`>>
    qpat_abbrev_tac`X' = set_store a w t`>>
    Cases_on`wGC (push_env x F X)`>>fs[]>>
    BasicProvers.FULL_CASE_TAC>> fs[]>>
    (*need a lemma about wGC here*)
    `wGC(push_env y F X') = SOME z' /\
     pop_env z' = SOME z'' /\
     strong_state_rel f x'' z''` by cheat >>
    fs[has_space_def,strong_state_rel_def,wGC_def,abbrev_and_def]>> rw[]>>
    BasicProvers.EVERY_CASE_TAC>>fs[weak_state_rel_def]>>
    DISJ2_TAC>>fs[strong_state_rel_def])
   (*Move*)
    (pop_assum_wEval>>
    BasicProvers.FULL_CASE_TAC>>fs[MAP_ZIP]>>
    BasicProvers.FULL_CASE_TAC>>fs[MAP_ZIP]>>
    `ALL_DISTINCT (MAP (f o FST) moves)` by (
      `MAP (f o FST) moves = MAP f (MAP FST moves)` by fs[MAP_MAP_o]>>
      fs[INJ_DEF]>>
      metis_tac[miscTheory.ALL_DISTINCT_MAP_INJ])>>
    `MAP (f o SND) moves = MAP f (MAP SND moves)` by fs[MAP_MAP_o]>>
    ASSUME_TAC strong_state_rel_get_vars_lemma>>
    first_x_assum(qspecl_then [`f`,`st`,`cst`,`MAP SND moves`,`x`] 
      assume_tac)>>
    simp[]>>    
      `MAP (f o FST) l = MAP f (MAP FST l)` by fs[MAP_MAP_o]>>
      `LENGTH (MAP FST l) = LENGTH x` by (
         ASSUME_TAC get_vars_length_lemma>>
         first_x_assum(qspecl_then [`MAP SND l`,`st`,`x`] assume_tac)>>
         fs[])>>
      ASSUME_TAC strong_state_rel_set_vars_lemma>>
      metis_tac[]) >-
   (*Assign*)
     (fs[wEval_def]>> Cases_on`word_exp st w`>>fs[]>>
     `word_exp cst (apply_color_exp f w) =  word_exp st w` by 
       metis_tac[inj_apply_color_exp_invariant]>>
     simp[] >>Cases_on`res`>>fs[]>> 
     metis_tac[strong_state_rel_set_var_lemma])>-
   (*Set*)
     (fs[wEval_def]>>
     Cases_on`word_exp st w`>>fs[set_store_def]>>
     `word_exp cst (apply_color_exp f w) = word_exp st w` by 
       metis_tac[inj_apply_color_exp_invariant]>>
     Cases_on`res`>>fs[strong_state_rel_def,word_state_component_equality])>-
   (*Store*)
     (fs[wEval_def]>>
     Cases_on`word_exp st w`>>fs[]>>
     IMP_RES_TAC inj_apply_color_exp_invariant>>
     Cases_on`get_var n st`>>fs[]>>
     IMP_RES_TAC strong_state_rel_get_var_lemma>>
     fs[mem_store_def]>>Cases_on`x IN st.mdomain`>>fs[]>>
     Cases_on`res`>>
     fs[strong_state_rel_def,word_state_component_equality]>>
     Cases_on`x IN rst.mdomain`>>fs[]>>metis_tac[])>-
   (*Call*)cheat>- 
     fs[wEval_def,LET_THM]>>
     Cases_on`st.clock=0`>-(
       fs[strong_state_rel_def,wEval_def]>>
       rfs[]>>
       rw[abbrev_and_def,call_env_def,weak_state_rel_def,fromList2_def]>>
       DISJ1_TAC>>
       fs[word_state_component_equality])>>
     `cst.clock <> 0` by fs[strong_state_rel_def]>>fs[]>>
     Cases_on`get_vars l st`>>  fs[]>>
     (*get_vars of the new set is equal*)
     IMP_RES_TAC strong_state_rel_get_vars_lemma>> rfs[]>>fs[]>>
     Cases_on`find_code o0 x st.code` >> rfs[strong_state_rel_def]>>fs[]>>
     Cases_on`x'` >> fs[]>>
     Cases_on`o1`>>fs[]>-
       (*NONE i.e. TAIL CALL*)
       (
       Cases_on`o'`>>fs[]>>
       `call_env q (dec_clock cst) = call_env q (dec_clock st)` by
          fs[dec_clock_def,call_env_def,word_state_component_equality]>>
        rfs[abbrev_and_def,weak_state_rel_def]>>fs[]>>
        BasicProvers.EVERY_CASE_TAC>>fs[])
       (*SOME i.e. RETURNING CALL*)
       Cases_on`x'`>>fs[]>>
       Cases_on`cut_env r' st.locals`>>fs[strong_state_rel_def]>>
       IMP_RES_TAC cut_env_lemma>>fs[]>>rw[]>>
       (*Need lemma here about wEval:
          wEval on 2 stacks differing only in the head's keys:
          wEval (prog, call_env locs (push_env y b (
          If SOME (Exception e) ->
            If head was a SOME handler and the handler position was correct
              then locals is exactly the popped handler in both cases 
          If SOME(Result x) then resulting states 
            should be the same except differ in head keys
        *)
       Cases_on `handler`>-
         (*No handler*)
         (fs[abbrev_and_def]>>BasicProvers.FULL_CASE_TAC>>cheat)>>
         (*SOME handler*) 
         fs[]
wEval 
         (r,call_env q (push_env x' (IS_SOME handler) (dec_clock st)))`>>
       Cases_on
       
        (*cut_env r' st.locals = SOME x' 
          ==> dom r' SUBSET dom st.locals
          consider x IN dom (apply_nummap_key r') ==> ?y. y in dom r'
          ==> y in dom st.locals ==> f y  in dom cst.locals therefore
          subset is true on cst therefore it gives SOME env
          TODO: needs more condition on the cut, I think strong state rel
         *)
         `cut_env (apply_nummap_key f r') cst.locals = SOME a` by cheat>>
         fs[call_env_def,push_env_def]>>
         Cases_on`o'`>-
           (*NONE i.e. NO HANDLER*)
           fs[LET_THM,env_to_list_def,dec_clock_def]


    simp[]
        rw[]>>fs[wEval_def]>-
          fs[]

        
              SPOSE_NOT_THEN ASSUME_TAC>> fs[strong_state_rel_def,fetch "-" "word_state_updates_eq_literal"]
         rw[strong_state_rel_def] >> simp[]
    (*Seq*)
    >-
      (Cases_on`wEval (prog,st)`>>
      last_x_assum (qspecl_then [`st`,`r`,`f`,`cst`,`q`] assume_tac)>>
      Cases_on`q`>-
      (*prog-->NONE*)
      (fs[apply_color_def,wEval_def]>> rfs[]>>
      fs[LET_THM]>>
      first_assum(split_applied_pair_tac o concl)>>
      fs[]>>
      first_x_assum (qspecl_then [`r`,`rst`,`f`,`rcst`,`res`] assume_tac)>>
      rfs[])>>
      (*prog-->SOME*)
      fs[apply_color_def,wEval_def]>>
      (*Instantiate the induction hyp*)
      last_x_assum(qspecl_then [`st`,`r`,`f`,`cst`,`SOME x`] assume_tac)>>
      fs[]>>
      `res = SOME x` by (rw[]>> fs[LET_THM])>>
      `x<>Error` by fs[]>>
       rfs[]>> fs[LET_THM] >>
       first_assum(split_applied_pair_tac o concl) >> fs[] >> rw[])>-
    (*If*)
    (fs[wEval_def]>>
     Cases_on`wEval(prog,st)`>>
     last_x_assum (qspecl_then [`st`,`r`,`f`,`cst`,`q`] assume_tac)>>
     Cases_on`q`>-
       (*NONE*)
       (rfs[LET_THM]>>fs[]>>
       Cases_on`wEval(apply_color f prog,cst)` >>fs[]>>
       IMP_RES_TAC strong_state_rel_get_var_lemma>>
       Cases_on`get_var n r`>>fs[]>>
       first_assum(fn th => first_x_assum(assume_tac o C MATCH_MP th))>>
       fs[]>>
       Cases_on`x`>>fs[]>>
       Cases_on`c=0w`>> fs[]>>metis_tac[])>>
       (*SOME*)
       rfs[LET_THM]>>`x<>Error`by (SPOSE_NOT_THEN assume_tac>>fs[])>>
       Cases_on`wEval(apply_color f prog,cst)`>>fs[]>>
       Cases_on`res`>>fs[])>-
   (*Raise*)
      (fs[wEval_def]>>get_var_tactic>>
       Cases_on`jump_exc st`>>fs[strong_state_rel_def,jump_exc_def]>>
      BasicProvers.EVERY_CASE_TAC>>fs[weak_state_rel_def]>>DISJ1_TAC>>
      fs[word_state_component_equality])>-
    (*Return*)
      (fs[wEval_def]>>get_var_tactic>>
       fs[call_env_def,fromList2_def,word_state_component_equality]>>
       BasicProvers.EVERY_CASE_TAC>>
       fs[strong_state_rel_def,weak_state_rel_def
       ,word_state_component_equality])>-
    (*Tick*)
    (fs[wEval_def,strong_state_rel_def]>>Cases_on`st.clock=0`>>
     fs[call_env_def,fromList2_def]>>
     BasicProvers.EVERY_CASE_TAC>>fs[word_state_component_equality]>-
       fs[weak_state_rel_def,word_state_component_equality]>>
     fs[dec_clock_def])


>>DISJ1_TAC>>
       fs[word_state_component_equality]


    (*Raise*)
    >-
    fs[wEval_def]>>Cases_on`get_var n st`>>fs[]>>
    `get_var (f n) cst = SOME x` by cheat (*same thm about get_var*)>>
    BasicProvers.EVERY_CASE_TAC>>fs[strong_state_rel_def,jump_exc_def]>-
      (`cst.handler < LENGTH cst.stack` by rw[] >> fs[]>>
      Cases_on`LAST_N (st.handler +1) st.stack`>> fs[]>>
      `LAST_N (cst.handler +1) cst.stack = LAST_N (st.handler+1) st.stack`
      by rw[]>>fs[]>>simp[]>>Cases_on`h`>>fs[]>>Cases_on`o'`>>fs[])>>
    simp[weak_state_rel_def]>>DISJ1_TAC>>
    Cases_on`LAST_N (st.handler +1) st.stack`>> fs[]>>
    `LAST_N (cst.handler +1) cst.stack = LAST_N (st.handler+1) st.stack`
    by rw[]>>fs[]>>Cases_on`h`>>fs[]>>Cases_on`o'`>>fs[]>>rw[word_state_component_equality]

    BasicProvers.EVERY_CASE_TAC>>fs[]>>
     
    fs[jump_exc_def]



    (*Seq*)
    >-
    fs[wEval_def]>>
    fs[LET_THM] >>
    first_assum(miscLib.split_applied_pair_tac o lhs o concl) 
    (*Return*)
    >-
    (*Raise*)
    >-   
    (*If*)
    >-
    (*Call rotate 10 after skip*)
    fs[MAP_ZIP,wEval_def,get_vars_def,set_vars_def,list_insert_def]>>
    Cases_on`s.clock=0`>>fs[]>-
      (rw[call_env_def,fromList2_def,toAList_def]>>EVAL_TAC>>HINT_EXISTS_TAC)>>
    BasicProvers.EVERY_CASE_TAC >>fs[]
    Cases_on`get_vars args s`>> fs[] >>
    `get_vars args' (s with locals := 
    apply_nummap_key f s.locals) = SOME x` by
    (ASSUME_TAC get_vars_inj>>
    fs[map_compose]>>
    first_x_assum(qspecl_then [`f`,`args`,`s`] assume_tac) >>
    metis_tac[])>>
    fs[apply_nummap_key_def]>>simp[]>>
    Cases_on`find_code dest x s.code`>> fs[] >>
    Cases_on`x'`>>simp[]>>
    Cases_on`ret`>-( 
      (*NONE RETURN*)
      fs[]>>Q.UNABBREV_TAC`ret'`>>simp[]>>
      Cases_on`handler`>-(
         (*NONE HANDLER*)
         fs[]>> 
         fs[call_env_def,dec_clock_def]>>
          
          

    (s with locals :=
        fromAList (ZIP (MAP (f o FST) (toAList s.locals),
        MAP SND (toAList s.locals))))`>>
    simp[]>>fs[]


    ASSUME_TAC 
      (INST_TYPE [``:'a``|->``:'a word_loc``] fromAList_list_insert)>>
    first_x_assum(qspecl_then [`MAP(f o FST) moves`,`x`] assume_tac)>>
    fs[rich_ZIP_APPEND,MAP_APPEND]>>
    fs[LENGTH_MAP,ZIP_MAP_EQ]>>
    
    rw[]
 strip_tac>> 
     (*Cases split on whethere y was in MAP FST moves*)
     ASSUME_TAC lookup_list_insert
     Cases_on`?z.f z =y/\ MEM z (MAP FST moves)`

     Cases_on `?z.f z = y /\ MEM z (toAList s.locals)`
          

    `MAP (f o FST) moves ++ MAP (f o FST) (toAList s.locals)

    ASSUME_TAC (INST_TYPE [``:'a``|->``:'a word_loc``] toAList_list_insert)>>
    first_x_assum(qspecl_then [`MAP FST moves`,`x`,`s.locals`] assume_tac)>>
    fs[] >> 
    

    fs[get_vars_inj]>>fs[]
    `get_vars (MAP (f o SND) moves) 
       (s with locals := apply_nummap_key f s.locals) =
     get_vars (MAP SND moves) s` by
      fs[map_compose] >>
      

    `!x f. INJ f UNIV UNIV /\ get_vars (MAP SND moves) s = SOME x ==>
     get_vars (MAP (f o SND) moves) (s with locals := apply_nummap_key f s.locals) = SOME x` by
    Induct_on `moves`>>
      fs[get_vars_def]>>
    rpt strip_tac >>
    Cases_on`get_var (SND h) s`>> fs[]>>
    rw[get_var_def]>> 

(*2nd subgoal of moves*)
  >> `ALL_DISTINCT (MAP FST moves)` by 
   (SPOSE_NOT_THEN ASSUME_TAC>> fs[])>>
   `MAP (f o FST) moves = MAP f (MAP FST moves)` by fs[map_compose]>>
   fs[INJ_DEF] 
   >> metis_tac[miscTheory.ALL_DISTINCT_MAP_INJ]
   
fs[]
     rw[]
      metis_tac[]

     Induct_on`moves` >- fs[] >>
       metis_tac[] 
   metis_tac[miscTheory.ALL_DISTINCT_MAP_INJ]
   IF_CASES_TAC
   simp[]>>
metis_tac[INJ_DEF]
    rw[fromAList_def]]
    rw[get_vars_def]>>
       Induct_on `moves`>-
         fs[get_vars_def] >>
       rw[get_vars_def,get_var_def]>>

  Induct_on `moves`>-
   (>>
   strip_tac>>
   rw[word_state_updates_eq_literal])>>

  rw[wEval_def,apply_color_def] >
   fs[MAP_ZIP,get_vars_def,apply_nummap_key_def]








val even_list_def = Define `
  (even_list (0:num) = []) /\
  (even_list n = 2*(n-1) :: even_list (n-1))`

(*move_conv takes prog, the initial args and a function. 
  adds a move and 
  replaces the varnames in the body*)
val move_conv_def = Define `
  move_conv prog f args= 
    let mov = Move (ZIP (MAP f args, args)) in
    let body = apply_color f prog in
      Seq mov body`

(*
EVAL ``move_conv (Seq (Call (SOME (5,LN)) (SOME 4) [3;2;1] NONE) Skip) 
       (\x.x+1) [1;2;3]`` 
*)


(*Correctness of move_conv
  For states which is a function entry point i.e. locals are 
  equal to some list some list [0,2,...,2*(n-1)]
  then p1_conv produces the same result, 
  TODO: with a different state
*)
val all_distinct_even_list_def = store_thm ("all_distinct_even_list",
  ``!n. ALL_DISTINCT (even_list n) /\ (!x. MEM x (even_list n)==> x < 2*n)``,
  Induct_on`n`>-
    rw [even_list_def]>>simp[] >>
  CONJ_TAC>>
  rw[even_list_def]>>
first_x_assum(qspec_then`2*n`mp_tac)>>
  simp[]>>
FULL_SIMP_TAC arith_ss []>>

(*The move added by move conv does not result in an Error if started 
  with locals of a state
  The resulting state is equivalent except it has new locals as given by the
  injection
  The injection does not overwrite any of the existing locals
*)
val move_conv_lemma = store_thm ("move_conv_lemma",
  ``!s f. (INJ f UNIV UNIV) /\ (!x y. f x = y ==> ~(y IN (domain s.locals)))
    ==> 
      let args = SET_TO_LIST (domain s.locals) in
        ?l. wEval(Move(ZIP (MAP f args,args)),s) = (NONE,s with locals := l)
                (*Original locals unchanged and there is a copy*) 
             /\ (!x. x IN domain s.locals ==>
                    lookup x s.locals = lookup x l
                 /\ lookup x s.locals = lookup (f x) l)
                (*Only those locals exist*)
             /\ (!x. x IN domain l ==>
                     x IN domain s.locals \/ 
                     ?y. x = f y /\ y IN domain s.locals)``
  rpt strip_tac>> rw[]>>
  EXISTS_TAC ``(let ls = toAList s.locals in fromAList (MAP f ls ++ ls))``>>
  rw[]>>
  (*`MEM x (SET_TO_LIST (domain s.locals)) ==> 
    IS_SOME (get_var x s)` by
    (strip_tac>>
    rw[get_var_def]>> fs[MEM_SET_TO_LIST,domain_lookup]) >>*)
  `!l. (!x.MEM x l ==> x IN (domain s.locals)) ==> 
        get_vars l s = 
          SOME(MAP (\x. case (lookup x s.locals) of SOME y => y)l)` by
    (Induct>-
      rw[get_vars_def] >>
    rpt strip_tac>>
    fs[]>>
    rw[get_vars_def,get_var_def,domain_lookup] >>
    first_x_assum(qspec_then`h`mp_tac) >>
    simp[]>> fs[domain_lookup]>>
    strip_tac>> fs[] )
  >>
  Q.UNABBREV_TAC `args`>>
  rw[wEval_def]>-
    (fs[MAP_ZIP,ALL_DISTINCT_SET_TO_LIST,
       ALL_DISTINCT_MAP_INJ,INJ_DEF,MEM_SET_TO_LIST]>> 
    first_x_assum(qspec_then`SET_TO_LIST (domain s.locals)`mp_tac) >>
    simp[] >> Q.ABBREV_TAC `args = SET_TO_LIST (domain s.locals)`>>
    rw[set_vars_def,list_insert_def] >> simp[]
    
    Cases_on `get_vars args s` >>
    fs[] ) >>
  fs[MAP_ZIP,ALL_DISTINCT_MAP_INJ,ALL_DISTINCT_SET_TO_LIST]>>
  pop_assum mp_tac>> simp[] >>
  match_mp_tac ALL_DISTINCT_MAP_INJ>> simp[]>>
  fs[INJ_DEF] );

  

(*Result of adding a move using injective f is invariant
Resulting state might have extra locals (depending on f) 
but any of the original locals must be present
*)
val inj_move_conv_invariant = store_thm ("move_invariant",
  ``!prog s s1 f res. wEval(prog,s) = (res,s1) 
            /\ res <> SOME Error
            /\ (INJ f UNIV UNIV)
     ==> ?s2. 
         wEval (move_conv prog f (SET_TO_LIST (domain s.locals)),s) = (res,s2)
         /\ (!x y. lookup x s1.locals = y ==> lookup (f x) s2.locals = y)
         (*Other state conditions TODO *)
         /\ (?l. s2 = s1 with locals := l) ``,

  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >>
  rw[] >>
  
  (*Move rotate 6*)
  rw[move_conv_def,wEval_def]>>
  rw[wEval_def]>>
  Cases_on `res`>-
    Q.UNABBREV_TAC `mov` >>
    IMP_RES_TAC move_conv_lemma>>
    first_x_assum(qspec_then`s`mp_tac)>>
    simp[] >> rw[] >>
    

    
   
  Cases_on `s.locals`>-
    fs[move_conv_def,wEval_def]>>
    
  rw[]>-
    
  strip_tac
 

 
val p1_conv_correct = store_thm ("p1_conv_correct",
  ``!prog n s s1 s2 res. wEval (prog,s) = (res, s1) /\ res <> SOME Error /\
            (!x. x IN (domain s.locals) <=>  MEM x (even_list n)) 
     ==> FST (wEval ((p1_conv prog n),s)) = res``,
strip_tac >>
ho_mp

Induct_on `prog` >>

(*Move*)
rw[p1_conv_def]>>
Cases_on`l`>-
  fs[get_vars_def,wEval_def,set_vars_def]>>
  Q.UNABBREV_TAC `body`>> Q.UNABBREV_TAC `f`>> Q.UNABBREV_TAC `mov`>>
  rw [apply_args_list_def,apply_color_def] >>
  Q.ABBREV_TAC `mov2 = ((ZIP (MAP (λx. 2 * x + 1) ls,ls)))` >>
  fs [wEval_def]
  
fs[apply_color_def]

fs[wEval_def,get_vars_def]>>


print_apropos ``Abbrev x``

(*
GOAL:
!prog s1 s2 res. wEval (prog,s) = (res,s2) /\ res <> SOME Error /\ ...
                 ==> ?s3. wEval (add_mov prog,s) = (res,s3) /\
                          state_rel s2 s3


(*Convert prog
(*Change function body to use odd vars*)

val rename_var_def = Define `
  (rename_var Skip = Skip) /\
  (rename_var (Move ls) =  

