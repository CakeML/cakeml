open HolKernel Parse boolLib bossLib miscLib
open word_langTheory 
open word_lemmasTheory
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

(*Abbrev the and away to make the proofs easier to handle..*)
val abbrev_and_def = Define`
  abbrev_and a b <=> a /\ b`

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

val MEM_fromAList = store_thm ("MEM_fromAList",
  ``∀t k. MEM k (MAP FST t) <=> 
          k IN domain (fromAList t) ``,
  Induct_on`t`>>
    rw[fromAList_def]>>
  Cases_on`h`>> 
  Cases_on`q=k`>>
    rw[fromAList_def])
 
(*cutting the environment on strongly related locals returns an
 exact_colored_locals *)

val cut_env_lemma = prove(
  ``!names sloc tloc x f. INJ f UNIV UNIV /\ cut_env names sloc = SOME x /\
    (!n v. (lookup n sloc = SOME v) ==> (lookup (f n) tloc = SOME v))
    ==> (?y. cut_env (apply_nummap_key f names) tloc = SOME y /\
              exact_colored_locals f x y)``,
    rpt strip_tac>>
    fs[cut_env_def,exact_colored_locals_def]>>
    CONV_TAC(lift_conjunct_conv(can dest_forall))>>
    CONJ_TAC>-
    (*lookup*)
    (rw[]>>simp[lookup_inter]>> Cases_on`lookup z sloc`>-
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
         lookup_apply_nummap_key)>>fs[])>>
    REVERSE CONJ_ASM2_TAC>-
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
    fs[domain_inter] >>
    qpat_abbrev_tac `X:num_set = fromAList Y`>>
    `domain tloc INTER domain X = domain X /\
     domain x = domain names` by
      metis_tac[domain_inter,GEN_ALL INTER_SUBSET_EQN,INTER_COMM]>>
     fs[]>> unabbrev_all_tac>>
     simp[EXTENSION]>>
     rw[EQ_IMP_THM]>-
       (IMP_RES_TAC MEM_fromAList>>
       fs[MAP_MAP_o,MEM_MAP,MAP_ZIP,MEM_ZIP]>>
       Cases_on`y`>>
       fs[EL_MAP]>>
       IMP_RES_TAC rich_listTheory.EL_MEM>>
       Q.ABBREV_TAC `elem = (EL n (toAList names))`>>
       Q.EXISTS_TAC `FST elem`>>
       Cases_on`elem`>>fs[MEM_toAList,domain_lookup])>>
       IMP_RES_TAC domain_lookup>>
       IMP_RES_TAC MEM_toAList>>
       qmatch_abbrev_tac `f x IN domain (fromAList (ZIP (A,B)))`>>
       `MEM (f x) (MAP FST (ZIP(A,B)))` by 
         (simp[MAP_ZIP,LENGTH_MAP,Abbr`A`,Abbr`B`]>>
         metis_tac[ZIP_MAP,EVAL``(f o FST) (x,v)``,Abbr`A`,MEM_MAP])>>
       fs[MEM_fromAList])

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

val locals_eq_toAList = prove(
  ``!x y f.
     (!z:num. lookup z x = lookup (f z) y)
      ==> !k v. MEM(k,v) (toAList x) <=> MEM (f k,v) (toAList y)``,
  metis_tac[MEM_toAList])

val map_keys = prove(
  ``!ls f. MAP SND (MAP (\x,y. f x,y) ls) = MAP SND ls``,
  simp[MAP_MAP_o,MAP_EQ_f]>> rpt strip_tac>>Cases_on`e`>>
  EVAL_TAC)

(*Can just prove with a single MAP but this form is easier..*)
val ALOOKUP_key_remap = prove(
  ``!ls ls' f. INJ f UNIV UNIV /\
               MAP SND ls = MAP SND ls' /\
               MAP (f o FST) ls = MAP FST ls'
      ==> !k. ALOOKUP ls k = ALOOKUP ls' (f k)``,
  Induct>>rw[]>>
  Cases_on`ls'`>> fs[]>>
  Cases_on`h`>>Cases_on`h'`>>fs[alistTheory.ALOOKUP_def]>>
  IF_CASES_TAC>-
    fs[]>>
  IF_CASES_TAC>-
    (fs[INJ_DEF]>>metis_tac[])>>
  metis_tac[])
  

val inj_apply_color_invariant = store_thm ("inj_apply_color_invariant",
  ``!prog st rst f cst res. 
                  wEval(prog,st) = (res,rst) 
                  /\ INJ f UNIV UNIV
                  /\ monotonic_color f
                  /\ res <> SOME Error
                  (*/\ wf st.locals*)
                  /\ strong_state_rel f st cst ==>
     let (res',rcst) = wEval(apply_color f prog,cst) in
      abbrev_and (res' = res) 
      (case res of
        NONE => strong_state_rel f rst rcst
      | SOME (Result x) => weak_state_rel f rst rcst
      | SOME (Exception e) => weak_state_rel f rst rcst
      | _ => T)`` (*TODO: Ignore the state results for the others?*)
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >>
  rw[] >-
   (*Skip*)
    (rw[abbrev_and_def,apply_color_def,wEval_def,EQ_SYM_EQ]>>fs[wEval_def]>>
    rw[EQ_SYM_EQ]) >-
   (*Alloc*)
    (pop_assum mp_tac>>fs[wEval_def]>>
    last_x_assum mp_tac>>
    BasicProvers.FULL_CASE_TAC>>fs[]>>
    IMP_RES_TAC strong_state_rel_get_var_lemma>> fs[]>>
    Cases_on`x`>>fs[wAlloc_def]>>
    Cases_on`cut_env names st.locals`>> fs[strong_state_rel_def]>>
    IMP_RES_TAC cut_env_lemma>>fs[]>> 
    qpat_abbrev_tac`X = set_store a w t`>>
    qpat_abbrev_tac`Y = set_store a w t`>>
    (*Prove that (push env x F X) and (push_env y F Y) are s_val_eq*)
    `s_val_eq X.stack Y.stack` by 
       (bossLib.UNABBREV_ALL_TAC>>fs[s_val_eq_refl,set_store_def])>>
    `s_val_eq (push_env x F X).stack (push_env y F Y).stack` by
       (fs[push_env_def,LET_THM,env_to_list_def,s_val_eq_def,s_frame_val_eq_def]>>
      `X.permute = Y.permute` by fs[set_store_def,Abbr`X`,Abbr`Y`]>>
       IMP_RES_TAC env_to_list_monotonic_eq>>
       last_x_assum (qspec_then `Y.permute` mp_tac)>>
       simp[LET_THM,env_to_list_def]>>
       metis_tac[map_keys])>>
    Cases_on`wGC (push_env x F X)`>>fs[]>>
    Q.ABBREV_TAC `Y' = push_env y F Y`>>
    IMP_RES_TAC wGC_s_val_eq_word_state>>
    first_x_assum(qspec_then `Y'.locals` assume_tac)>>
    fs[]>>
    `(push_env x F X with <|locals := Y'.locals; stack := Y'.stack|>) = Y'` by 
      (unabbrev_all_tac>>
      fs[set_store_def,word_state_component_equality,push_env_def,env_to_list_def,LET_THM])>>
    pop_assum SUBST_ALL_TAC>> fs[]>>
    Cases_on`pop_env x'`>>fs[]>>
    `s_key_eq Y'.stack zstack` by 
      metis_tac[s_key_eq_sym]>>
    Q.UNABBREV_TAC `Y'`>> 
    qabbrev_tac `Z = x' with <|locals := zlocs; stack:= zstack|>`>>
    `s_key_eq (push_env y F Y).stack Z.stack` by fs[word_state_component_equality,Abbr`Z`]>>
    IMP_RES_TAC push_env_pop_env_s_key_eq>>
    fs[]>>
    unabbrev_all_tac>>
    `strong_state_rel f x'' y''''` by 
      (fs[strong_state_rel_def,pop_env_def]>>
      BasicProvers.EVERY_CASE_TAC>>
      fs[s_key_eq_def,word_state_component_equality,s_val_eq_def,s_frame_val_eq_def]>>
      CONJ_TAC>-
        (`s_key_eq y''''.stack x''.stack` by
          (IMP_RES_TAC wGC_s_key_eq>>
          fs[push_env_def,LET_THM,set_store_def,env_to_list_def]>>
          metis_tac[s_key_eq_tail,s_key_eq_sym,s_key_eq_refl,EQ_SYM_EQ,s_key_eq_trans])>>
        metis_tac[s_val_eq_sym,s_val_and_key_eq])>>
        ntac 2 (qpat_assum `fromAList L = X.locals` (SUBST1_TAC o SYM))>>
        simp[lookup_fromAList]>>
        IMP_RES_TAC wGC_s_key_eq>>
        qpat_assum `x'.stack = bla` SUBST_ALL_TAC>>
        fs[push_env_def,LET_THM,set_store_def,env_to_list_def
          ,s_key_eq_def,s_frame_key_eq_def]>>        
        IMP_RES_TAC env_to_list_monotonic_eq>>
        rpt BasicProvers.VAR_EQ_TAC>>
        `MAP (f o FST) l' = MAP FST l` by(
           fs[env_to_list_def,LET_THM]>>
           last_x_assum (qspec_then `st.permute` assume_tac)>>
           qpat_assum `MAP FST ls = MAP FST l` (SUBST1_TAC o SYM)>>
           simp[(GEN_ALL o SYM o SPEC_ALL) MAP_MAP_o]>>
           qpat_assum `MAP FST ls = MAP FST l'` (SUBST1_TAC o SYM)>>
           (*got to be a simpler way to do this..*)
           `MAP FST  (MAP (λ(x,y). (f x,y))
            (list_rearrange (st.permute 0)
            (QSORT key_val_compare (nub (toAList x))))) = MAP FST (
            list_rearrange (st.permute 0)
            (QSORT key_val_compare (nub (toAList y))))` by fs[]>>
            `!ls.MAP f (MAP FST ls) = MAP FST (MAP (\x,y:'a word_loc. (f x,y)) ls)` by
               (simp[MAP_MAP_o,MAP_EQ_f]>>strip_tac>>Cases>>EVAL_TAC)>>
            metis_tac[])>>
         metis_tac[ALOOKUP_key_remap])>>
    BasicProvers.FULL_CASE_TAC>>fs[strong_state_rel_def]>>
    BasicProvers.FULL_CASE_TAC>>fs[has_space_def]>>
    IF_CASES_TAC>>rw[abbrev_and_def]>>fs[weak_state_rel_def]>>
    DISJ2_TAC>>fs[strong_state_rel_def]) >-
   (*Move*)
    (fs[wEval_def]>> pop_assum mp_tac>> last_x_assum mp_tac>>
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
    simp[]>> rw[]>>fs[abbrev_and_def]>>
      `MAP (f o FST) l = MAP f (MAP FST l)` by fs[MAP_MAP_o]>>
      `LENGTH (MAP FST moves) = LENGTH x` by (
         ASSUME_TAC get_vars_length_lemma>>
         first_x_assum(qspecl_then [`MAP SND moves`,`st`,`x`] assume_tac)>>
         fs[])>>
      ASSUME_TAC strong_state_rel_set_vars_lemma>>
      metis_tac[MAP_MAP_o]) >-
   (*Assign*)
     (fs[wEval_def]>> pop_assum mp_tac>>last_x_assum mp_tac>>
     BasicProvers.EVERY_CASE_TAC>> fs[abbrev_and_def]>>
     `word_exp cst (apply_color_exp f exp) =  word_exp st exp` by 
       metis_tac[inj_apply_color_exp_invariant]>>rfs[]>>rw[]>>
     metis_tac[strong_state_rel_set_var_lemma])>-
   (*Set*)
     (
     fs[wEval_def]>>first_assum mp_tac>>last_x_assum mp_tac>>
     BasicProvers.EVERY_CASE_TAC>>fs[set_store_def,abbrev_and_def]>>
     `word_exp cst (apply_color_exp f exp) = word_exp st exp` by 
       metis_tac[inj_apply_color_exp_invariant]>-rfs[optionTheory.SOME_11]>>
     fs[strong_state_rel_def,word_state_component_equality,optionTheory.SOME_11]>>
     fs[EQ_SYM_EQ]
     )>-
   (*Store*)
     (fs[wEval_def]>>pop_assum mp_tac>> last_x_assum mp_tac>>
     Cases_on`word_exp st exp`>>
     IMP_RES_TAC inj_apply_color_exp_invariant>> fs[]>>
     Cases_on`get_var prog st`>>fs[]>>
     IMP_RES_TAC strong_state_rel_get_var_lemma>>
     fs[mem_store_def]>>Cases_on`x IN st.mdomain`>>fs[]>>
     fs[strong_state_rel_def,word_state_component_equality,abbrev_and_def]>>
     rw[]>>fs[])>-
   (*Call*) 
     fs[wEval_def,LET_THM]>>
     Cases_on`st.clock=0`>-(
       fs[strong_state_rel_def,wEval_def]>>
       rfs[]>>
       rw[abbrev_and_def,call_env_def,weak_state_rel_def,fromList2_def]>>
       DISJ1_TAC>>
       fs[word_state_component_equality])>>
     `cst.clock <> 0` by fs[strong_state_rel_def]>>fs[]>>
     Cases_on`get_vars args st`>>  fs[]>>
     (*get_vars of the new set is equal*)
     IMP_RES_TAC strong_state_rel_get_vars_lemma>> rfs[]>>fs[]>>
     Cases_on`find_code dest x st.code` >> rfs[strong_state_rel_def]>>fs[]>>
     Cases_on`x'` >> fs[]>>
     Cases_on`ret`>>fs[]>-
       (*NONE i.e. TAIL CALL*)
       (unabbrev_all_tac>>
       Cases_on`handler`>>fs[]>>
       `call_env q (dec_clock cst) = call_env q (dec_clock st)` by
          fs[dec_clock_def,call_env_def,word_state_component_equality]>>
        rfs[abbrev_and_def,weak_state_rel_def]>>fs[]>>
        BasicProvers.EVERY_CASE_TAC>>fs[])>>
       (*SOME i.e. RETURNING CALL*)
       Cases_on`x'`>>fs[]>>unabbrev_all_tac>>
       Cases_on`cut_env r' st.locals`>>fs[strong_state_rel_def]>>
       IMP_RES_TAC cut_env_lemma>>fs[]>>rw[]>>
       Q.ABBREV_TAC `envx = call_env q (push_env x' (IS_SOME handler) (dec_clock st))`>>
       Q.ABBREV_TAC `envy = call_env q (push_env y  (IS_SOME 
                     (case handler of
                        NONE => NONE
                      | SOME (v,prog) => SOME (f v,apply_color f prog))) (dec_clock cst))`>>
       `s_val_eq envx.stack envy.stack /\ envy = envx with stack:=envy.stack` by
         (unabbrev_all_tac>>
         BasicProvers.FULL_CASE_TAC>>
         (TRY (Cases_on `x''`))>>fs[]>>
         IMP_RES_TAC env_to_list_monotonic_eq>>
         fs[dec_clock_def,push_env_def,call_env_def,LET_THM,strong_state_rel_def
           ,env_to_list_def,s_val_eq_def,s_val_eq_refl,s_frame_val_eq_def]>>
         (CONJ_TAC>- metis_tac[map_keys]>>
         fs[strong_state_rel_def,word_state_component_equality]))>>
       assume_tac wEval_stack_swap>>
       pop_assum (qspecl_then [`r`,`envx`] mp_tac)>>
       ntac 3 BasicProvers.FULL_CASE_TAC>>fs[]>>
       (*Apply the stack swap lemma*)
       (rw[]>>pop_assum (qspec_then `envy.stack` assume_tac)>>rfs[]>>
       qpat_assum `envy = X` (SUBST_ALL_TAC o SYM) >>fs[abbrev_and_def])>-
         (*Result*)
         (rw[]>>pop_assum(qspec_then `envy.stack` assume_tac)>>
         rfs[]>>
         qpat_assum `envy = X` (SUBST_ALL_TAC o SYM) >>fs[]>>
         Cases_on`pop_env r''`>>fs[]>>
         Q.UNABBREV_TAC `envy`>>
         fs[call_env_def]>>
         qpat_assum `s_key_eq (push_env A B C).stack st'` mp_tac>>
         `st' = (r'' with stack:=st').stack` by fs[] >> 
         pop_assum SUBST1_TAC>>
         strip_tac>>
         IMP_RES_TAC push_env_pop_env_s_key_eq>>
         fs[]>>
         Cases_on`domain x''.locals = domain x'`>> fs[]>>
         `strong_state_rel f x'' y'` by
           (fs[strong_state_rel_def,pop_env_def]>>
           BasicProvers.EVERY_CASE_TAC>>
           fs[s_key_eq_def,word_state_component_equality,s_val_eq_def,s_frame_val_eq_def]>>
           (
           TRY (qpat_assum `y'.stack = rcst.stack` (SUBST1_TAC o SYM) >>
                qpat_assum `y'.locals = rcst.locals` (SUBST1_TAC o SYM) )>>
           CONJ_TAC>-
             (`s_key_eq y'.stack x''.stack` by
               (unabbrev_all_tac>>fs[]>>
               fs[push_env_def,LET_THM,set_store_def,env_to_list_def,dec_clock_def]>>
               metis_tac[s_key_eq_tail,s_key_eq_sym,s_key_eq_refl
                        ,EQ_SYM_EQ,s_key_eq_trans])>>
               metis_tac[s_val_eq_sym,s_val_and_key_eq])>>
           ntac 2 (qpat_assum `fromAList L = X.locals` (SUBST1_TAC o SYM))>>
           simp[lookup_fromAList]>>
           unabbrev_all_tac>>fs[]>>
           fs[push_env_def,LET_THM,set_store_def,env_to_list_def
             ,s_key_eq_def,s_frame_key_eq_def,dec_clock_def]>>        
           IMP_RES_TAC env_to_list_monotonic_eq>>
           rpt BasicProvers.VAR_EQ_TAC>>
           `MAP (f o FST) l' = MAP FST l` by(
             fs[env_to_list_def,LET_THM]>>
             last_x_assum (qspec_then `st.permute` assume_tac)>>
             qpat_assum `MAP FST ls = MAP FST l` (SUBST1_TAC o SYM)>>
             simp[(GEN_ALL o SYM o SPEC_ALL) MAP_MAP_o]>>
             qpat_assum `MAP FST ls = MAP FST l'` (SUBST1_TAC o SYM)>>
             (*got to be a simpler way to do this..*)
             `MAP FST  (MAP (λ(x,y). (f x,y))
              (list_rearrange (st.permute 0)
              (QSORT key_val_compare (nub (toAList x'))))) = MAP FST (
              list_rearrange (st.permute 0)
              (QSORT key_val_compare (nub (toAList y))))` by fs[]>>
              `!ls.MAP f (MAP FST ls) = MAP FST (MAP (\x,y:'a word_loc. (f x,y)) ls)` by
                (simp[MAP_MAP_o,MAP_EQ_f]>>strip_tac>>Cases>>EVAL_TAC)>>
              metis_tac[])>>
            metis_tac[ALOOKUP_key_remap]))>>
            (*Get down to the MAP FST level again...*)
            unabbrev_all_tac>>
            fs[pop_env_def,s_key_eq_def,push_env_def,env_to_list_def,LET_THM]>>
            Cases_on`st'`>>fs[]>>Cases_on`h`>>Cases_on`o'`>>
            Cases_on`r''.stack`>>fs[]>>Cases_on`h`>>Cases_on`o'`>>
            fs[s_key_eq_def,s_frame_key_eq_def]>> Cases_on`handler`>>
            fs[s_val_eq_def,s_frame_key_eq_def,s_frame_val_eq_def]>>
            fs[dec_clock_def]>>
            IMP_RES_TAC env_to_list_monotonic_eq>>
            `MAP (f o FST) l' = MAP FST l` by(
             fs[env_to_list_def,LET_THM]>>
             last_x_assum (qspec_then `st.permute` assume_tac)>>
             qpat_assum `MAP FST ls = MAP FST l` (SUBST1_TAC o SYM)>>
             simp[(GEN_ALL o SYM o SPEC_ALL) MAP_MAP_o]>>
             qpat_assum `MAP FST ls = MAP FST l'` (SUBST1_TAC o SYM)>>
             (*got to be a simpler way to do this..*)
             `MAP FST  (MAP (λ(x,y). (f x,y))
              (list_rearrange (st.permute 0)
              (QSORT key_val_compare (nub (toAList x'))))) = MAP FST (
              list_rearrange (st.permute 0)
              (QSORT key_val_compare (nub (toAList y))))` by fs[]>>
              `!ls.MAP f (MAP FST ls) = MAP FST (MAP (\x,y:'a word_loc. (f x,y)) ls)` by
                (simp[MAP_MAP_o,MAP_EQ_f]>>strip_tac>>Cases>>EVAL_TAC)>>
              fs[]>>metis_tac[])>>
             fs[exact_colored_locals_def]>>
            `domain y'.locals = domain y` by
               (`y'.locals = fromAList l /\ x''.locals = fromAList l'` by 
                 fs[word_state_component_equality]>>
                 assume_tac (INST_TYPE [``:'a``|->``:'a word_loc``] domain_fromAList)>>
                 first_assum(qspec_then `l` assume_tac)>>
                 first_x_assum(qspec_then `l'` assume_tac)>>
                 `set(MAP FST l') = domain x'` by fs[]>>
                 `IMAGE f (set (MAP FST l')) = domain y` by fs[]>>
                 `set (MAP (f o FST) l') = domain y` by 
                   metis_tac[LIST_TO_SET_MAP,MAP_MAP_o]>> 
                 qpat_assum `MAP g l' = MAP FST l` SUBST_ALL_TAC>>
                 `domain y'.locals = set(MAP FST l)` by fs[]>>
                 metis_tac[])>> fs[abbrev_and_def]>>metis_tac[strong_state_rel_def]
                 

            fs[s_frame_key_eq_def]>>
            
            `y'.locals = fromAList l` by fs[word_state_component_equality]>> 
            pop_assum SUBST1_TAC>>
            simp[domain_fromAList]>>
            qpat_assum `A = MAP FST l` (SUBST1_TAC o SYM)
            fs[list_rearrange_MAP]

            `y'.locals = fromAList l` by fs[word_state_component_equality]
            simp[EXTENSION]>>
            
        


         qunabbrev_tac `Z`>>fs[])
         (*Exception*) 
         IMP_RES_TAC s_val_eq_LAST_N_exists>>
         last_x_assum (qspecl_then [`e''`,`ls''`] assume_tac)>>
         rfs[]>>Cases_on`handler`>>fs[]>-
           (*No handler*)
           qpat_assum`X = res` (SUBST_ALL_TAC o SYM)>>fs[weak_state_rel_def]>-
           DISJ1_TAC>>fs[strong_state_rel_def,word_state_component_equality]>>
           (*We know there is no handler, so envx.handler+1 is not the top of stack
             therefore the LAST_N after that are equal and the rest follows*)
       
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

val even_list_def = Define `
  (even_list (0:num) = []) /\
  (even_list n = 2*(n-1) :: even_list (n-1))`

val LT_even_list = prove(
  ``!n x. MEM x (even_list n) ==> x < 2*n``,
  ho_match_mp_tac (fetch "-" "even_list_ind")>>
  rw[]>> fs[even_list_def] >> 
  first_x_assum(qspec_then `x` assume_tac)>> rfs[]>>
  DECIDE_TAC)

val ALL_DISTINCT_even_list = prove(
 ``!n. ALL_DISTINCT (even_list n)``,
  Induct>> fs[even_list_def]>>
  SPOSE_NOT_THEN assume_tac>>
  IMP_RES_TAC LT_even_list>> fs[])

(*Adding a move: takes an f and n = expected local number and generates a move*)
val move_locals_def = Define`
  move_locals f n = 
    let names = even_list n in
      Move ((MAP \n. f n,n) names)`
(*
EVAL ``move_locals (\x.2*x+1) 10``
*)

val get_vars_domain_eq_lemma = prove(
  ``!ls s x.
        (set ls) SUBSET (domain s.locals) ==>
        get_vars ls s = SOME (MAP (THE o (\x.lookup x s.locals)) ls)``,
  Induct>>rw[get_vars_def,get_var_def]>>
  fs[domain_lookup])

val lookup_list_insert = prove(
  ``!x y t (z:num). LENGTH x = LENGTH y ==> 
    (lookup z (list_insert x y t) = 
    case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)``,
    ho_match_mp_tac list_insert_ind>>
    rw[]>-
      (Cases_on`y`>>
      rw[list_insert_def]>>fs[LENGTH]) >>
    Cases_on`z=x`>>
      rw[lookup_def,list_insert_def]>>
    fs[lookup_insert]) 

val ZIP_MAP_MAP_EQ = prove(
  ``!ls f g. ZIP (MAP f ls, MAP g ls) = MAP (\x. f x,g x) ls``,
  Induct>>fs[])

(*Need injectivity to ensure ALL_DISTINCT of the move target,
  problem with needing to know that the keys are ALL_DISTINCT..*)
val move_locals_strong_state_rel = prove(
  ``!f s n. INJ f UNIV UNIV /\ 
          domain s.locals = set (even_list n) ==>
  let (res,s') = wEval (move_locals f n,s) in
    res = NONE /\ strong_state_rel f s s'``,
  rpt strip_tac>>fs[wEval_def,LET_THM,move_locals_def,MAP_ZIP]>>
  assume_tac ALL_DISTINCT_even_list>>
  pop_assum (qspec_then `n` assume_tac)>>
  fs[MAP_MAP_o]>>
  `INJ (FST o (\n.(f n,n))) UNIV UNIV` by fs[INJ_DEF]>>
  fs[GEN_ALL FINITE_domain,ALL_DISTINCT_MAP_INJ,INJ_DEF
    ,ALL_DISTINCT_SET_TO_LIST]>>
  `set (even_list n) SUBSET (domain s.locals)` by
     fs[pred_setTheory.SUBSET_REFL]>>
  IMP_RES_TAC get_vars_domain_eq_lemma >>
  `!ls. MAP (SND o (\n. (f n,n))) ls = ls` by
    simp[miscTheory.MAP_EQ_ID]>>
  fs[]>>
  fs[set_vars_def,strong_state_rel_def]>>
  rw[]>>
  assume_tac lookup_list_insert>>
  qmatch_abbrev_tac `lookup (f n') (list_insert A B s.locals) = SOME v`>>
  `LENGTH A = LENGTH B` by (unabbrev_all_tac>>fs[LENGTH_MAP])>>
  imp_res_tac lookup_list_insert>>
  last_x_assum (qspecl_then [`f n'`,`s.locals`] assume_tac)>>
  simp[ZIP_MAP]>>
  `ALL_DISTINCT (MAP FST (ZIP(A,B))) /\ MEM (f n',v) (ZIP (A,B))` by
  (unabbrev_all_tac>> CONJ_TAC >-
    fs[MAP_ZIP,INJ_DEF,ALL_DISTINCT_MAP_INJ] >>
  `MEM n' (even_list n)` by 
    (IMP_RES_TAC domain_lookup>>metis_tac[])>>
  simp[ZIP_MAP_MAP_EQ,MEM_MAP]>>HINT_EXISTS_TAC>>fs[])>>
  Q.ISPECL_THEN [`v`,`f n'`,`ZIP(A,B)`]assume_tac (GEN_ALL alistTheory.ALOOKUP_ALL_DISTINCT_MEM)>>
  fs[])
  
val odd_coloring_def = Define`
  odd_coloring n:num = 2*n +1`

val odd_coloring_facts = prove(
  ``INJ odd_coloring UNIV UNIV /\
    monotonic_color odd_coloring``,
  fs[INJ_DEF,odd_coloring_def,monotonic_color_def]>>
  DECIDE_TAC)

(*The full theorem for the first conversion*)
val seq_move_locals_def = Define`
  seq_move_locals f n prog = Seq (move_locals f n) prog`

val seq_move_correct = store_thm("seq_move_correct",
  ``!prog s n.
       wEval(prog,s) = (res,s') /\
       domain s.locals = set(even_list n) /\
       res <> SOME Error ==> 
       wEval(seq_move_locals odd_coloring n prog,s) = (res,s'') /\
       strong_state_rel (odd_coloring) s' s''``



  `MEM n ls` by fs[domain_lookup]>>
  MEM n move_locals_strong_state_rel

  Induct_on`SET_TO_LIST (domain s.locals)`>>

  fs[get_var_def,et_vars_def,strong_state_rel_def,set_vars_def,list_insert_def]

val FV_exp_def = tDefine "FV_exp" `
  (FV_exp (Const c) = {}) /\
  (FV_exp (Var v) = {v}) /\
  (FV_exp (Get name) = {}) /\
  (FV_exp (Load addr) = FV_exp addr) /\
  (FV_exp (Op op wexps) = BIGUNION (IMAGE (FV_exp) (set wexps)))/\
  (FV_exp (Shift sh wexp nexp)) = FV_exp wexp`
 (WF_REL_TAC `measure (word_exp_size ARB )`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

(*Local var bindings introduced by the instruction*)
val BV_def = Define`
  (BV Skip = {}) /\
  (BV (Move ls) = set (MAP FST ls)) /\
  (BV (Assign v exp) = {v}) /\
  (BV (Set v exps) = {}) /\
  (BV (Store exp v) = {}) /\
  (BV Tick = {}) /\
  (BV (Seq c1 c2) = (BV c1) UNION (BV c2)) /\
  (BV (Return n) = {}) /\ 

 
val FV_def = Define`
  (FV Skip = {}) /\
  (FV (Move ls) = set (MAP SND ls)) /\
  (FV (Assign v exp s) = 
  TypeBase.constructors_of ``:'a word_prog``


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
       doALL_DISTINCT_MAP_INJ,INJ_DEF,MEM_SET_TO_LIST]>> 
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

