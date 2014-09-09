open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open bvp_lemmasTheory
open word_langTheory 
open word_lemmasTheory
open alistTheory

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
                        | SOME (v,cutset,ret_handler) => 
                          SOME (f v,apply_nummap_key f cutset,apply_color f ret_handler) in
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

val ZIP_MAP_MAP_EQ = prove(
  ``!ls f g. ZIP (MAP f ls, MAP g ls) = MAP (\x. f x,g x) ls``,
  Induct>>fs[])

val ALOOKUP_INJ_keys = prove(
  ``!ls f. INJ f UNIV UNIV ==>
           !k. ALOOKUP ls k = ALOOKUP (MAP (\x,y.f x,y) ls) (f k)``,
  Induct>>rw[]>>
  Cases_on`h`>>fs[]>>IF_CASES_TAC>>fs[]>>
  `f q <> f k` by (SPOSE_NOT_THEN assume_tac >> fs[INJ_DEF] >>metis_tac[])>> fs[])

(*Generalize a theorem in sptree*)
val ALOOKUP_INJ_toAList = store_thm("ALOOKUP_INJ_toAList",
  ``!f t x.INJ f UNIV UNIV ==>
      ALOOKUP ((MAP \x,y. f x,y) (toAList t)) (f x) = lookup x t``,
  rpt strip_tac>>Cases_on `lookup x t` >-
    (simp[ALOOKUP_FAILS,MEM_toAList,MEM_MAP] >>
    rpt strip_tac>>Cases_on`y`>>fs[]>>
    Cases_on`f x = f q`>>fs[MEM_toAList]>>
    `x = q` by fs[INJ_DEF]>>fs[])>>
  Cases_on`ALOOKUP (toAList t) x`>-
    fs[ALOOKUP_FAILS,MEM_toAList] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_toAList]>>
  Q.ISPECL_THEN [`toAList t`,`f`] assume_tac ALOOKUP_INJ_keys >> rfs[]>>
  metis_tac[])

val lookup_apply_nummap_key = prove(
  ``!f t z. INJ f UNIV UNIV ==>
     lookup (f z) (apply_nummap_key f t) = lookup z t``,
  rw[]>>
  simp[lookup_fromAList,ZIP_MAP_MAP_EQ]>>
  `(\x. (f (FST x),SND x)) = (\x,y. f x,y)` by
    (rw[FUN_EQ_THM]>>Cases_on`x`>>fs[])>>
  simp[ALOOKUP_INJ_toAList])

val ALOOKUP_toAList = store_thm("ALOOKUP_toAList",
  ``!t x. ALOOKUP (toAList t) x = lookup x t``,
  strip_tac>>strip_tac>>Cases_on `lookup x t` >-
    simp[ALOOKUP_FAILS,MEM_toAList] >>
  Cases_on`ALOOKUP (toAList t) x`>-
    fs[ALOOKUP_FAILS,MEM_toAList] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_toAList])

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
      | _ => weak_state_rel f rst rcst)``,
  (*Actually: when we have Some Timeout or Some NotEnoughSpace - locals := LN and stack:=[]
    This is implied by this theorem + the stack swap theorem*)
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
    DISJ1_TAC>>fs[call_env_def,fromList2_def,word_state_component_equality])>-
   (*Move*)
    (fs[wEval_def]>> pop_assum mp_tac>> last_x_assum mp_tac>>
    BasicProvers.FULL_CASE_TAC>>fs[MAP_ZIP]>>
    BasicProvers.FULL_CASE_TAC>>fs[MAP_ZIP]>>
    `ALL_DISTINCT (MAP (f o FST) moves)` by (
      `MAP (f o FST) moves = MAP f (MAP FST moves)` by fs[MAP_MAP_o]>>
      fs[INJ_DEF]>>
      metis_tac[ALL_DISTINCT_MAP_INJ])>>
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
     (fs[wEval_def]>>first_assum mp_tac>>last_x_assum mp_tac>>
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
    (*Tick*)
    (fs[wEval_def]>>pop_assum mp_tac>> last_x_assum mp_tac>>
     BasicProvers.EVERY_CASE_TAC>>
     fs[abbrev_and_def,call_env_def,fromList2_def,strong_state_rel_def,
        word_state_component_equality,weak_state_rel_def,dec_clock_def]>>rw[]>>
     metis_tac[])>-
    (*Seq*)
     (Cases_on`wEval (prog,st)`>>
      first_x_assum (qspecl_then [`r`,`f`,`cst`,`q`] assume_tac)>>
      Cases_on`q`>-
      (*prog-->NONE*)
      (fs[apply_color_def,wEval_def]>> rfs[]>>
      fs[LET_THM,abbrev_and_def]>>
      first_assum(split_applied_pair_tac o concl)>>
      fs[]>>
      first_x_assum (qspecl_then [`f`,`rcst'`] assume_tac)>>
      rfs[])>>
      (*prog-->SOME*)
      fs[apply_color_def,wEval_def,LET_THM]>>rfs[]>>
      `res = SOME x` by (rw[]>> fs[LET_THM])>>
      `x<>Error` by fs[]>>
      rfs[]>> fs[LET_THM,abbrev_and_def] >>
      first_assum(split_applied_pair_tac o concl) >> fs[] >> rw[]>>simp[])>-
    (*Return*)
    (fs[wEval_def]>>pop_assum mp_tac>> last_x_assum mp_tac>>
     Cases_on`get_var n st`>>fs[]>>
     IMP_RES_TAC strong_state_rel_get_var_lemma>>rw[]>>
     fs[call_env_def,fromList2_def,strong_state_rel_def,abbrev_and_def,
          weak_state_rel_def,word_state_component_equality])>-
    (*Raise*)
    (fs[wEval_def]>>pop_assum mp_tac>>last_x_assum mp_tac>>
     Cases_on`get_var n st`>>fs[]>>
     IMP_RES_TAC strong_state_rel_get_var_lemma>>rw[]>>
     Cases_on`jump_exc st`>>fs[strong_state_rel_def,jump_exc_def]>>
     rfs[]>>fs[]>>
     BasicProvers.EVERY_CASE_TAC>>fs[weak_state_rel_def,abbrev_and_def]>>DISJ1_TAC>>
     fs[word_state_component_equality])>-
    (*If*)
    (fs[wEval_def]>>
     Cases_on`wEval(prog,st)`>>
     last_x_assum (qspecl_then [`r`,`f`,`cst`,`q`] assume_tac)>>
     Cases_on`q`>-
       (*NONE*)
       (rfs[LET_THM]>>fs[abbrev_and_def]>>
       first_assum(split_applied_pair_tac o concl)>>fs[]>>
       Cases_on`get_var n r`>>fs[]>>       
       IMP_RES_TAC strong_state_rel_get_var_lemma>>fs[]>>
       Cases_on`x`>>fs[]>>
       Cases_on`c=0w`>> fs[]>>
       first_x_assum(qspecl_then [`f`,`rcst'`] assume_tac)>>rfs[])>>
       (*SOME*)
       rfs[LET_THM]>>`x<>Error`by (SPOSE_NOT_THEN assume_tac>>fs[])>>
       Cases_on`wEval(apply_color f prog,cst)`>>fs[]>>
       Cases_on`res`>>fs[abbrev_and_def]>>metis_tac[])>-
   (*Call*) 
     (fs[wEval_def,LET_THM]>>
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
       PairCases_on`x'`>>fs[]>>unabbrev_all_tac>>
       Cases_on`cut_env x'1 st.locals`>>fs[strong_state_rel_def]>>
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
       (*Apply the stack swap lemma, solves the Timeout and NotEnoughSpace cases*)
       (rw[]>>pop_assum (qspec_then `envy.stack` assume_tac)>>rfs[]>>
       qpat_assum `envy = X` (SUBST_ALL_TAC o SYM) >>fs[abbrev_and_def,weak_state_rel_def])>-
         (*Result*)
         (Cases_on`pop_env r'`>>fs[]>>
         Q.UNABBREV_TAC `envy`>>
         fs[call_env_def]>>
         qpat_assum `s_key_eq (push_env A B C).stack st'` mp_tac>>
         `st' = (r' with stack:=st').stack` by fs[] >> 
         pop_assum SUBST1_TAC>>
         strip_tac>>
         IMP_RES_TAC push_env_pop_env_s_key_eq>>
         fs[]>>
         Cases_on`domain x''.locals = domain x'`>> fs[]>>
         `(IS_SOME (case handler of NONE => NONE 
           | SOME (v,prog) => SOME (f v,apply_color f prog))) = IS_SOME handler` by
           (BasicProvers.EVERY_CASE_TAC>>fs[])>>
         fs[]>>
         unabbrev_all_tac>>
         fs[pop_env_def,s_key_eq_def,push_env_def,env_to_list_def,LET_THM]>>
         Cases_on`st'`>>fs[]>>Cases_on`h`>>Cases_on`o'`>>
         Cases_on`r'.stack`>>fs[]>>Cases_on`h`>>Cases_on`o'`>>
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
         `domain y'.locals = domain y` by
           (fs[exact_colored_locals_def]>>
            `y'.locals = fromAList l /\ x''.locals = fromAList l'` by 
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
             metis_tac[])>>
         fs[]>>
         `strong_state_rel f x'' y'` by
           (fs[strong_state_rel_def,pop_env_def]>>
           BasicProvers.EVERY_CASE_TAC>>
           fs[s_key_eq_def,word_state_component_equality,s_val_eq_def,s_frame_val_eq_def]>>
           (
           CONJ_TAC>-
             (`s_key_eq y'.stack x''.stack` by
               (unabbrev_all_tac>>fs[]>>
               fs[push_env_def,LET_THM,set_store_def,env_to_list_def,dec_clock_def]>>
               metis_tac[s_key_eq_tail,s_key_eq_sym,s_key_eq_refl
                        ,EQ_SYM_EQ,s_key_eq_trans])>>
               metis_tac[s_val_eq_sym,s_val_and_key_eq])>>
           ntac 2 (qpat_assum `fromAList L = X.locals` (SUBST1_TAC o SYM))>>
           simp[lookup_fromAList]>>
           metis_tac[ALOOKUP_key_remap]))>>
         Cases_on`wEval (x'2,set_var x'0 a x'')` >>
         Cases_on`q'`>>fs[]>>
         IMP_RES_TAC strong_state_rel_set_var_lemma>>
         first_x_assum (qspecl_then [`f`,`set_var (f x'0) a y'`] assume_tac)>>
         rfs[strong_state_rel_def]>>
         first_assum (split_applied_pair_tac o concl)>> fs[]>>
         BasicProvers.EVERY_CASE_TAC>>fs[])>>
         (*Exception*)
         IMP_RES_TAC s_val_eq_LAST_N_exists>>
         last_x_assum (qspecl_then [`e''`,`ls''`] assume_tac)>>
         rfs[]>>Cases_on`handler`>>fs[]>-
           (*No handler*)
           (qpat_assum`X = res` (SUBST_ALL_TAC o SYM)>>fs[weak_state_rel_def]>>
           DISJ1_TAC>>fs[strong_state_rel_def,word_state_component_equality]>>
           unabbrev_all_tac>>
           fs[call_env_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
          `e = e'' /\ ls = ls''` by (
             assume_tac (GEN_ALL bvp_lemmasTheory.LAST_N_TL)>>
             `st.handler <= LENGTH st.stack` by DECIDE_TAC>>
             Cases_on`st.handler = LENGTH st.stack`>>
             rpt (qpat_assum `LAST_N A B = C` mp_tac)>-
               simp[LAST_N_LENGTH_cond]>>
             `st.handler<LENGTH st.stack` by DECIDE_TAC>>
              simp[GEN_ALL LAST_N_TL])>>
           ntac 2 (pop_assum SUBST_ALL_TAC)>>
           `lss = lss'` by fs[LIST_EQ_MAP_PAIR]>>
           qpat_assum `A = rcst.stack` SUBST_ALL_TAC>>
           qpat_assum `A = rst.stack` SUBST_ALL_TAC>>
           metis_tac[s_val_and_key_eq,s_key_eq_trans])>>
           (*SOME handler*)
           unabbrev_all_tac>>
           Cases_on`x''`>>fs[]>>
           Cases_on`domain (fromAList lss) = domain x'` >>fs[]>>
           fs[call_env_def,dec_clock_def,s_key_eq_def,push_env_def,env_to_list_def,LET_THM]>>
           rpt (qpat_assum `LAST_N A B = C` mp_tac)>>
           simp[LAST_N_LENGTH_cond]>>strip_tac>>strip_tac>>
           IMP_RES_TAC env_to_list_monotonic_eq>> 
           `MAP (f o FST) lss = MAP FST lss'` by(
             fs[env_to_list_def,LET_THM]>>
             last_x_assum (qspec_then `st.permute` assume_tac)>>
             qpat_assum `MAP FST e'' = MAP FST lss'` (SUBST1_TAC o SYM)>>
             simp[(GEN_ALL o SYM o SPEC_ALL) MAP_MAP_o]>>
             qpat_assum `MAP FST e = MAP FST lss` (SUBST1_TAC o SYM)>>
             (*got to be a simpler way to do this..*)
             `MAP FST  (MAP (λ(x,y). (f x,y))
               (list_rearrange (st.permute 0)
               (QSORT key_val_compare (nub (toAList x'))))) = MAP FST (
               list_rearrange (st.permute 0)
               (QSORT key_val_compare (nub (toAList y))))` by fs[]>>
             `!ls.MAP f (MAP FST ls) = MAP FST (MAP (\x,y:'a word_loc. (f x,y)) ls)` by
               (simp[MAP_MAP_o,MAP_EQ_f]>>strip_tac>>Cases>>EVAL_TAC)>>
               fs[]>>metis_tac[])>>
           `domain (fromAList lss') = domain y` by
           (fs[exact_colored_locals_def]>>
             assume_tac (INST_TYPE [``:'a``|->``:'a word_loc``] domain_fromAList)>>
             first_assum(qspec_then `lss'` assume_tac)>>
             first_x_assum(qspec_then `lss` assume_tac)>>
             `set(MAP FST lss) = domain x'` by fs[]>>
             `IMAGE f (set (MAP FST lss)) = domain y` by fs[]>>
             `set (MAP (f o FST) lss) = domain y` by 
               metis_tac[LIST_TO_SET_MAP,MAP_MAP_o]>> 
             metis_tac[])>> 
           fs[set_var_def]>>
           Q.ABBREV_TAC `Y = r' with <|locals := insert (f q') w (fromAList lss'); 
                         stack := st';handler := r'.handler|>`>>
           Q.ABBREV_TAC `X = r' with locals := insert q' w (fromAList lss)`>>
           `strong_state_rel f X Y` by 
             (unabbrev_all_tac>>
             fs[strong_state_rel_def]>>CONJ_TAC>-
               metis_tac[s_key_eq_trans,s_val_and_key_eq]>>
             rpt strip_tac>>
             Cases_on`n = q'`>- fs[]>>
             `f n <> f q'` by (fs[INJ_DEF]>>metis_tac[])>>
             fs[lookup_insert,lookup_fromAList]>>
             ASSUME_TAC (INST_TYPE [``:'a``|->``:num``,``:'b``|->``:'a word_loc``
                        ,``:'c``|->``:num``] ALOOKUP_key_remap)>>
             pop_assum(qspecl_then [`lss`,`lss'`,`f`] assume_tac)>>rfs[]>>
             metis_tac[INJ_DEF])>>
          `insert q' w (fromAList lss) = X.locals` by (unabbrev_all_tac>>
            fs[insert_def,word_state_component_equality])>>pop_assum SUBST_ALL_TAC>>
          first_x_assum(qspecl_then [`rst`,`f`,`Y`,`res`] assume_tac)>>
          fs[strong_state_rel_def,Abbr`X`]>>rfs[]))

val even_list_def = Define `
  (even_list = GENLIST (\x.2*x))`

(*EVAL ``even_list 5``*)

val ALL_DISTINCT_even_list = prove(
 ``!n. ALL_DISTINCT (even_list n)``,
  rw[even_list_def]>>
  simp [ALL_DISTINCT_GENLIST])

(*Adding a move: takes an f and n = num of locals and generates a move
e.g. (1,0) (5,2) (9,4)... *)
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

(*TODO: There are multiple defs of list_insert..*)
val lookup_list_insert = prove(
  ``!x y t (z:num). LENGTH x = LENGTH y ==> 
    (lookup z (list_insert x y t) = 
    case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)``,
    ho_match_mp_tac list_insert_ind>>
    rw[]>-
      (Cases_on`y`>>
      fs[LENGTH,list_insert_def]) >>
    Cases_on`z=x`>>
      rw[lookup_def,list_insert_def]>>
    fs[lookup_insert]) 

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
  seq_move_locals f n prog = Seq (move_locals f n) (apply_color f prog)`

val seq_move_correct = store_thm("seq_move_correct",
  ``!prog s n res rst.
       wEval(prog,s) = (res,rst) /\
       domain s.locals = set(even_list n) /\
       res <> SOME Error ==>
       let (res',rcst) = wEval(seq_move_locals odd_coloring n prog,s) in
         res' = res /\ 
         (case res of
            NONE => strong_state_rel odd_coloring rst rcst
             | _ => weak_state_rel odd_coloring rst rcst) ``,
  rpt strip_tac>>
  fs[wEval_def,seq_move_locals_def]>>
  assume_tac odd_coloring_facts>>
  IMP_RES_TAC move_locals_strong_state_rel>>
  pop_assum(qspec_then `odd_coloring` assume_tac)>> rfs[LET_THM]>>
  first_assum (split_applied_pair_tac o concl)>>fs[]>>
  metis_tac[inj_apply_color_invariant,abbrev_and_def])

(*
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
*)


(*Start defining the second conversion...
lim is meant to be an (odd) limit variable i.e. no larger var is mentioned in the program
conv_args are the converted names for arguments to be restored ..
*)

val num_set_to_list_def = Define`
  num_set_to_list (numset:num_set) = MAP FST (toAList numset)`

val list_to_num_set = Define`
  list_to_num_set ls = fromAList (MAP (\x.(x,())) ls)`

val call_conv_trans_def = Define`
  (*Returning calls*)
  (call_conv_trans lim (Call (SOME (ret,names,ret_handler)) dest args h) = 
    (*Forcing args into registers*)
    let lim = if lim > 2 * LENGTH args then lim else 2*LENGTH args +1 in
    let conv_args = even_list (LENGTH args) in
    let names = num_set_to_list names in 
    (*numset -> Alist, might want to add nub here to give all_distinct?
      This transform needs to be monotonic and injective*)
    let conv_names = GENLIST (\i. 2*i + lim) (LENGTH names) in
    (*Move that restores the cutset*)
    let restore = Move (ZIP (names,conv_names)) in
    (*Both handlers are recursively renamed 
      and exceptional return vals are mapped to 0
      NOTE: 2 Moves required because of possible shadowing of the cut-set values*)
    let conv_h = case h of NONE => NONE
                        |  SOME(n,h) => SOME(0, Seq restore 
                                               (Seq (Move [n,0])
                                                    (call_conv_trans lim h))) in
    let conv_ret = Seq restore 
                  (Seq (Move [ret,0]) 
                       (call_conv_trans lim ret_handler)) in
    Seq (Move (ZIP (conv_names++conv_args,names++args)))
        (Call (SOME (0,list_to_num_set conv_names,conv_ret)) dest conv_args conv_h))/\
  (*Tail calls -- Only need to add a move on the args to force args into registers
    (handler should be NONE)*)
  (call_conv_trans lim (Call NONE dest args h) =
    let conv_args = even_list (LENGTH args) in
    Seq (Move (ZIP (conv_args,args))) (Call NONE dest conv_args h)) /\
  (call_conv_trans lim (Seq p p') = Seq (call_conv_trans lim p) (call_conv_trans lim p')) /\
  (call_conv_trans lim (If g n c1 c2) = If (call_conv_trans lim g) n (call_conv_trans lim c1)
                                         (call_conv_trans lim c2)) /\
  (call_conv_trans lim x = x) `

val _ = export_rewrites ["num_set_to_list_def","list_to_num_set_def"
                        ,"call_conv_trans_def","even_list_def"]

(*We might only need to check if the cut-set is all odd?*)    
val odd_calls_def = Define`
  (odd_calls (Call ret dest args handler) <=>
    EVERY ODD args) 
    (*case ret of NONE => T 
    | SOME (_,names,_) => EVERY ODD (num_set_to_list names)*)/\
  (odd_calls (Seq p p') <=> odd_calls p /\ odd_calls p') /\
  (odd_calls (If g n c1 c2) <=> odd_calls g /\ odd_calls c1 /\ odd_calls c2) `

val strong_state_rel_I_refl = prove(
  ``!s. strong_state_rel I s s``,
  strip_tac>>fs[strong_state_rel_def]) 


(*generalized form for get_vars*)
val get_vars_list_insert_eq_gen= prove(
``!ls x locs a b. (LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
                  LENGTH a = LENGTH b /\ !e. MEM e ls ==> ~MEM e a)
  ==> get_vars ls (st with locals := list_insert (a++ls) (b++x) locs) = SOME x``,
  ho_match_mp_tac list_insert_ind>>
  rw[]>-
    (Cases_on`x`>>fs[get_vars_def])>>
  fs[get_vars_def,get_var_def,lookup_list_insert]>>
  `LENGTH (ls::ls') = LENGTH (x::x')` by fs[]>>
  IMP_RES_TAC rich_listTheory.ZIP_APPEND>>
  (*Best way I could find...*)
  ntac 9 (pop_assum (SUBST1_TAC o SYM))>>
  fs[ALOOKUP_APPEND]>>
  first_assum(qspec_then `ls` assume_tac)>>fs[]>>
  `ALOOKUP (ZIP (a,b)) ls = NONE` by metis_tac[ALOOKUP_NONE,MEM_MAP,MAP_ZIP]>>
  fs[]>>
  first_x_assum(qspecl_then [`a++[ls]`,`b++[x]`] assume_tac)>>
  `LENGTH (a++[ls]) = LENGTH (b++[x])` by fs[]>> rfs[]>>
  `a++[ls]++ls' = a++ls::ls' /\ b++[x]++x' = b++x::x'` by fs[]>>
  ntac 2 (pop_assum SUBST_ALL_TAC)>> fs[])

val list_insert_append = prove(
``!x y locs a b. LENGTH a = LENGTH b /\ LENGTH x = LENGTH y ==>
  list_insert(a++x) (b++y) locs = list_insert a b (list_insert x y locs)``
  rw[]>>
  list_
  ho_match_mp_tac list_insert_ind>>
  rw[]>-
    (Cases_on`y`>>fs[list_insert_def])>>


val get_vars_list_insert_eq_gen2 = prove(
``!ls x locs a b. (LENGTH ls = LENGTH x /\ ALL_DISTINCT a /\
                  LENGTH a = LENGTH b /\ !e. MEM e ls ==> ~MEM e a)
  ==> get_vars a (st with locals := list_insert (a++ls) (b++x) locs) = SOME b``,
  ho_match_mp_tac list_insert_ind>>
  rw[]>-
    (Cases_on`x`>>fs[]>>
    assume_tac get_vars_list_insert_eq_gen>>
    pop_assum(qspecl_then [`a`,`b`,`locs`,`[]`,`[]`] assume_tac)>>
    fs[])>>
  `ALL_DISTINCT (a++[ls])` by fs[ALL_DISTINCT_APPEND]>>
  first_x_assum(qspecl_then [`a++[ls]`,`b++[x]`] assume_tac)>>
  rfs[]
  
  !ls x locs a b. (LENGTH ls = 

val ALL_DISTINCT_even_list_rw =REWRITE_RULE [even_list_def] ALL_DISTINCT_even_list 

val ALL_DISTINCT_offset_list_rw = prove(
``!n. ALL_DISTINCT (GENLIST (\i.2*i +lim) n)``,
  fs[ALL_DISTINCT_GENLIST]>>DECIDE_TAC)

val get_vars_append = prove(
  ``get_vars (a++b) st = case get_vars a st of NONE => NONE | SOME x => 
             case get_vars b st of NONE => NONE | SOME y => SOME (x++y)``,
  Induct_on`a`>>
  fs[get_vars_def]>- BasicProvers.EVERY_CASE_TAC>>
  rw[]>>
  Cases_on`get_var h st`>>fs[]>>
  Cases_on`get_vars a st`>>fs[]>>
  Cases_on`get_vars b st`>>fs[])

(*Rough statement*)
val call_conv_trans_correct = store_thm("call_conv_trans_correct",
``!prog st res rst lim. wEval(prog,st) = (res,rst) /\
                        (*odd_calls prog /\ -- Only odd vars are mentioned in Calls*)
                  (*TODO: limit_var lim prog /\ -- Only *)
                  res <> SOME Error /\
                  res <> SOME TimeOut 
  (*TODO: Timeouts break this because timeout is checked BEFORE args are checked*)
  ==> ?rst'. wEval(call_conv_trans lim prog,st) = (res,rst') /\
            strong_state_rel I rst rst'``,
  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >>
  rw[]>>fs[wEval_def,strong_state_rel_I_refl]>>

  (*Call*)
  Cases_on`ret`>>
  fs[wEval_def,LET_THM,MAP_ZIP,ALL_DISTINCT_even_list_rw]>-
  (*Tail call*)
    (BasicProvers.EVERY_CASE_TAC>>fs[set_vars_def,get_vars_def]>>
    IMP_RES_TAC get_vars_length_lemma>>
    pop_assum (assume_tac o SYM)>>
    assume_tac get_vars_list_insert_eq_gen>>
    pop_assum(qspecl_then [`even_list (LENGTH args)`,`x`,`st.locals`,`[]`,`[]`] assume_tac)>>
    fs[]>>rfs[ALL_DISTINCT_even_list_rw]>>
    fs[call_env_def,dec_clock_def]>>
    Q.EXISTS_TAC`rst`>>fs[strong_state_rel_I_refl]>>
    qpat_assum `bla = res` (SUBST1_TAC o SYM)>>
    fs[])
  (*Normal call*)
    qpat_assum `bla = (res,rst)` mp_tac>>
    IF_CASES_TAC>>fs[]>>
    PairCases_on`x`>>
    Cases_on`get_vars args st`>>fs[]>>
    Cases_on`find_code dest x st.code`>>fs[]>>
    Cases_on`x'`>>fs[]>>
    Cases_on`cut_env x1 st.locals`>-
    fs[cut_env_def]>>
    fs[LET_THM,wEval_def,MAP_ZIP,ALL_DISTINCT_APPEND
      ,ALL_DISTINCT_even_list_rw,ALL_DISTINCT_offset_list_rw]>>
    (*This is true because the args list is bounded by 2* LENGTH args
      lim is deliberately forced to be greater so it is not a MEM*)
    Q.ABBREV_TAC `lim' = if lim > 2 * LENGTH args then lim else 2 * LENGTH args + 1`>>
    Q.ABBREV_TAC `ls = GENLIST (λx. 2 * x) (LENGTH args)`>>
    Q.ABBREV_TAC `a = GENLIST (λi. 2 * i + lim') (LENGTH (toAList x1))`>>

    `∀e. MEM e a ==> ~ MEM e ls` by cheat>>
    fs[get_vars_append]>>
    (*This is true b.c. dom x1 SUBST dom st, but do we need to make this all distinct?
      Needs some condition on y...*)
    `get_vars (MAP FST (toAList x1)) st = SOME y` by cheat>>
    fs[set_vars_def]>>
    IMP_RES_TAC get_vars_length_lemma>>
    `get_vars ls (st with locals := list_insert (a ++ ls) (y ++ x) st.locals) = SOME x` by
    (Q.ISPECL_THEN [`ls`,`x`,`st.locals`,`a`,`y`] assume_tac get_vars_list_insert_eq_gen>>
    `LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\ LENGTH a = LENGTH y` by
      (unabbrev_all_tac>> 
      fs[ALL_DISTINCT_offset_list_rw,ALL_DISTINCT_even_list_rw])
    metis_tac[LENGTH_GENLIST,LENGTH_MAP])>>
    fs[cut_env_def]>>
    (*Certainly true..*)
    `domain (fromAList (MAP (λx. (x,())) a)) ⊆
     domain (list_insert (a ++ ls) (y ++ x) st.locals)` by cheat>>fs[]>>
    fs[push_env_def,LET_THM,word_state_component_equality,dec_clock_def]>>
    `IS_SOME (case handler of NONE => NONE 
                     | SOME (n,h') => SOME (0,Seq (Move (ZIP (MAP FST (toAList x1),a)))
		                             (Seq (Move [(n,0)]) (call_conv_trans lim' h'))))
    = IS_SOME handler` by 
      (BasicProvers.EVERY_CASE_TAC>>fs[])>>
     fs[env_to_list_monotonic_eq]
     pop_assum SUBST1_TAC
     simp[]
    (*We need to end up with this condition:
      Probably best to do the entire cut_env in a separate lemma*)
 
    `MAP SND x' = MAP SND (inter (list_insert (a ++ ls) (y ++ x) st.locals)
     (fromAList (MAP (λx. (x,())) a)))` by cheat>>


      = SOME x` by cheat>>
    fs[cut_env_def] >>

    (*I might have been able to use cut_env_lemma here... the problem is no easy way to 
      state an INJ f --> one certainly exists...*)>>
    pop_assum (qspecl_then [`x1`,`st.locals`,`

	    fs[cut_env_def]>>
    
    `

    BasicProvers.FULL_CASE_TAC>>fs[]>>

    _CASE_TAC
       qabbrev_tac `X = st with locals := 
                       list_insert (GENLIST (λx. 2 * x) (LENGTH args)) x st.locals`>>
    fs[get_vars_def]>>
    `get_vars args X = SOME x` by
      fs[get_vars_def,Abbr`X`,odd_calls_def]>>
      Induct_on`args`>>fs[get_vars_def,get_var_def]>>
      rw[]>>
     
         
      `
      simp [lookup_list_insert,LENGTH_GENLIST]>>
     
  Cases_on`st.clock`>>fs[]

  BasicProvers.FULL_CASE_TAC>>fs[]
every_case_tac

EVERY_CASE_TAC
  fs[GEN_ALL MAP_ZIP,LENGTH_GENLIST]

,strong_state_rel_def]
 
         let (res',rcst) = wEval(seq_move_locals odd_coloring n prog,s) in
         res' = res /\ 
         (case res of
            NONE => strong_state_rel I rst rcst (*might have extra locals*)
             | _ => weak_state_rel odd_coloring rst rcst)


(*
EVAL ``call_conv_trans 999 (Call (SOME (3, list_insert [1;3;5;7;9] [();();();();()] LN,Skip)) (SOME 400) [7;9] NONE)``
*)

(*Compute a limit variable satisfying
1) not mentioned in the program (strictly > than anything USED (not just looked up) 
   in the program)
2) odd *)

(*
EVAL ``FOLDL (\x y. MAX x y) 1 [1;2;3;4;5]``
*)
val limit_var_exp_def = tDefine "limit_var_exp" `
  (limit_var_exp (Const _) = 1) /\
  (limit_var_exp (Var n) = 2* n +1) /\
  (limit_var_exp (Get _) = 1) /\
  (limit_var_exp (Load exp) = limit_var_exp exp) /\
  (limit_var_exp (Op op exps) = FOLDL (\x y. MAX x (limit_var_exp y)) 1 exps) /\
  (limit_var_exp (Shift sh exp nexp) = limit_var_exp exp)`
  (WF_REL_TAC `measure (word_exp_size ARB )`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

val is_limit_exp_def = tDefine "is_limit_exp" `
  (is_limit_exp n (Const _) = T) /\
  (is_limit_exp n (Var y) = (y < n)) /\
  (is_limit_exp n (Get _) = T) /\
  (is_limit_exp n (Load exp) = is_limit_exp n exp) /\
  (is_limit_exp n (Op op exps) = EVERY (is_limit_exp n) exps) /\
  (is_limit_exp n (Shift sh exp nexp) = is_limit_exp n exp)`
  (WF_REL_TAC `measure (word_exp_size ARB o SND )`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

(*TODO
val FOLDL_MAX_f = prove(
  ``!exps f. 
      let n = FOLDL (\x y. MAX x (f y)) 1 exps in
        EVERY (\y. f y <= n) exps``,
   Induct>>rw[]>>simp[]>-
     unabbrev_all_tac>>
     pop_assum (qspec_then `f` assume_tac)>> fs[LET_THM]
     fs[arithmeticTheory.MAX_DEF]


      let n = FOLDL (\x y. MAX x (limit_var_exp y)) 1 exps in
          EVERY (is_limit_exp n) exps``,
  Induct>>fs[LET_THM]>>
  rw[]

val is_limit_exp_limit_var_exp = prove(
``!exp n. (limit_var_exp exp <= n) ==> is_limit_exp n exp``,
  ho_match_mp_tac (fetch "-" "limit_var_exp_ind")>>
  rw[is_limit_exp_def,limit_var_exp_def]>- DECIDE_TAC>>
  `EVERY (\x. (limit_var_exp x) ≤ n) exps` by
    Induct_on`exps`>>fs[]>>rw[]
  rw[]>>

  rpt strip_tac>>
*)
val _ = export_theory();

