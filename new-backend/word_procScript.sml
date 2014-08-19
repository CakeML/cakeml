open HolKernel Parse boolLib bossLib; 

val _ = new_theory "word_proc";

set_trace "Goalstack.print_goal_at_top" 0;

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

(*Prove side results about fromAList: 
  The keys in the Alist will always be in the resulting domain*)
val MEM_fromAList = store_thm ("MEM_fromAList",
  ``∀t k. MEM k (MAP FST t) <=> 
          k IN domain (fromAList t) ``,
  Induct_on`t`>>
    rw[fromAList_def]>>
  Cases_on`h`>> 
  Cases_on`q=k`>>
    rw[fromAList_def])

val lookup_fromAList = store_thm ("lookup_fromAList",
  ``!x v ls. lookup x (fromAList ls) = SOME v ==> MEM (x,v) ls``,
  strip_tac>>strip_tac>>Induct>>
  fs[fromAList_def,lookup_def]>>
  Cases_on`h`>>
    Cases_on`q=x`>>
      rw[lookup_def,fromAList_def]>> fs[lookup_insert] >>
      metis_tac[]
  )

val MEM_MAP_FST = store_thm ("MEM_MAP_FST",
``!f v x ls. MEM (f v,x) ls ==> MEM (f v) (MAP FST ls)``,
     Induct_on `ls` >>
      fs[]>> 
      Cases>>
      rpt strip_tac>>
      fs[]>>
      metis_tac[])

(*Map compose*)
val map_compose = prove (
  ``!f g ls. MAP (f o g) ls = MAP f (MAP g ls)``,
   strip_tac>>strip_tac>>Induct>>
   fs[]);

val ZIP_CORRECT = store_thm ("ZIP_CORRECT",
``!l v x' f. MEM (v,x') l 
  ==> MEM (f v,x') (ZIP (MAP (f o FST) l,MAP SND l))``,
     (Induct_on `l`>>
     fs[] >>
     Cases >>
     rpt strip_tac>>
     fs[]) )

val ZIP_CORRECT_INJ = store_thm ("ZIP_CORRECT_INJ",
``!l v x' f. INJ f UNIV UNIV
  ==> 
  ((MEM (v,x') l) <=> (MEM (f v,x') (ZIP (MAP (f o FST) l,MAP SND l))))``,
  Induct_on `l`>>
  fs[] >>
  Cases >>
  rpt strip_tac>>
  fs[]>>
  Cases_on `v=q`>-
    (fs[]>>metis_tac[])>>
  fs[] >> 
  `f v <> f q` by
  fs[INJ_DEF]>>
  metis_tac[INJ_DEF])

(*fromAList list_insert*)

val fromAList_list_insert = prove(
  ``!x y ls ls'. ls = fromAList ls' /\ LENGTH x = LENGTH y ==> 
      list_insert x y ls = fromAList (ZIP (x,y) ++ ls')``,
  ho_match_mp_tac (fetch "-" "list_insert_ind")>> 
  rw[]>-
    (Cases_on`y`>> fs[list_insert_def])>>
  fs[list_insert_def,fromAList_def])

(*ZIP equivalence - Simplification for Move*)
val ZIP_MAP_EQ = prove(
  ``!f ls. ZIP ( MAP (f o FST) ls , MAP SND ls)  = MAP (\x,y.f x,y) ls``,
  strip_tac>>Induct>> fs[]>>
  Cases>>simp[])

(*Delete repeated keys in AList*)
(*val unique_key_def =  tDefine "unique_key"`
  (unique_key [] = [] ) /\
  (unique_key ((x,y)::xs) = (x,y) :: unique_key (FILTER (\a,b. a<>x) xs))`
  (WF_REL_TAC `measure LENGTH` >>
  rpt strip_tac>>
  `LENGTH (FILTER (\a,b. a<>x) xs) <= LENGTH xs` by
  fs[rich_listTheory.LENGTH_FILTER_LEQ]>> simp[])
*)

(*This defn seems much easier to work with:*)
val unique_key_def = Define`
  (unique_key ls = toAList (fromAList ls))`
 
val MEM_MAP_FST_gen = prove(
  ``!ls x. (?y. MEM (x,y) ls) <=> MEM x (MAP FST ls)``,
 Induct >- fs[]>>
 Cases>>strip_tac>>
 rw[]>>Cases_on`x=q`>>
 fs[]>> 
 EXISTS_TAC ``r:'b`` >>fs[] >>
 fs[])

(*toAList fromAList cancellation thms*)
val fromAList_toAList_lemma = prove(
  ``!t x. lookup x (fromAList (toAList t)) = lookup x t``,
  rpt strip_tac>>Cases_on`lookup x t`>-(
    `!y. ~MEM (x,y) (toAList t)` by fs[MEM_toAList]>>
    ASSUME_TAC lookup_fromAList >>
    SPOSE_NOT_THEN ASSUME_TAC>> simp[] >> 
    metis_tac[lookup_def,lookup_fromAList,MEM_toAList,NOT_SOME_NONE,fromAList_def,toAList_def,option_nchotomy]) >>
  Cases_on `lookup x (fromAList (toAList t))`>-
    (fs[lookup_NONE_domain]>> ASSUME_TAC MEM_fromAList >>
    `~ MEM x (MAP FST (toAList t))` by metis_tac[]>>
    ASSUME_TAC MEM_toAList >> 
    `!y. ~MEM (x,y) (toAList t)` by metis_tac[MEM_MAP_FST_gen]>>
    metis_tac[])>>
    `MEM (x,x'') (toAList t)` by metis_tac[lookup_fromAList]>>
    metis_tac[MEM_toAList])

val fromAList_wf = prove(
  ``!ls. wf (fromAList ls)``,
  Induct >> 
    rw[fromAList_def,wf_def]>>
  Cases_on`h`>>
  rw[fromAList_def]>>
    simp[wf_insert])

val fromAList_toAList = prove (
  ``!t. wf t ==> fromAList (toAList t) = t``,
  metis_tac[fromAList_wf,fromAList_toAList_lemma,spt_eq_thm])

val fromAList_unique_key = prove(
  ``!ls. fromAList ls = fromAList (unique_key ls)``,
  metis_tac[unique_key_def,fromAList_toAList,fromAList_wf])

val toAList_unique_key = prove(
  ``!t.wf t ==> toAList t = unique_key (toAList t)``,
  metis_tac[unique_key_def,fromAList_toAList,fromAList_wf] )

val fromAList_split = prove(
  ``!x y. fromAList(x++y)=list_insert (MAP FST x) (MAP SND x) (fromAList y)``,
  Induct>> fs[list_insert_def]>>
    Cases>> rw[fromAList_def])

val toAList_list_insert = prove(
  ``!x y t. LENGTH x = LENGTH y /\ wf t ==>
      toAList(list_insert x y t) = unique_key (ZIP (x,y) ++ (toAList t))``,
  rw[unique_key_def,fromAList_split]>>
  fs[MAP_ZIP,fromAList_toAList])

val lookup_list_insert = prove(
  ``!x y t (z:num). LENGTH x = LENGTH y ==> 
    (lookup z (list_insert x y t) = 
    case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)``,
    ho_match_mp_tac (fetch "-" "list_insert_ind")>>
    rw[]>-
      (Cases_on`y`>>
      rw[list_insert_def]>>fs[LENGTH]) >>
    Cases_on`z=x`>>
      rw[lookup_def,list_insert_def]>>
    fs[lookup_insert]) 

val ALOOKUP_toAList_eq = prove(
  ``!t x. ALOOKUP (toAList t) x = lookup x t``,
  strip_tac>>strip_tac>>Cases_on `lookup x t` >-
    (*NONE*)
    (SPOSE_NOT_THEN ASSUME_TAC>>
    `?y. ALOOKUP(toAList t) x = SOME y` by metis_tac[option_nchotomy]>>
    metis_tac[alistTheory.ALOOKUP_MEM,MEM_toAList])>>
    (*SOME*)
    SPOSE_NOT_THEN ASSUME_TAC>>
    Cases_on`ALOOKUP (toAList t) x`>-(
      `MEM (x,x') (toAList t)` by fs[MEM_toAList]>>
      `MEM x (MAP FST (toAList t))` by
        (simp[MEM_MAP,EXISTS_PROD]>>metis_tac[])>>
       metis_tac[alistTheory.ALOOKUP_NONE]
       ) >>
      `MEM(x,x'') (toAList t)` by fs[alistTheory.ALOOKUP_MEM]>>
      metis_tac[alistTheory.ALOOKUP_NONE,MEM_toAList])
  
val ALOOKUP_toAList_list_insert = prove(
  ``!z x y t. LENGTH x = LENGTH y ==>
   ALOOKUP (toAList (list_insert x y t)) z = 
   case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t``,
  strip_tac>>ho_match_mp_tac (fetch "-" "list_insert_ind")>>
  rw[]>-
    (Cases_on`y`>>rw[list_insert_def]>>fs[LENGTH,ALOOKUP_toAList_eq])>>
  fs[ALOOKUP_toAList_eq,list_insert_def,lookup_insert])
    
val toAList_unique_key = prove(
  ``!t. ALL_DISTINCT (MAP FST (toAList t))``>>
  SPOSE_NOT_THEN ASSUME_TAC >>
  fs[]>>
  `?k1 k2. MEM k1 (MAP FST (toAList t)) /\ MEM k2 (MAP FST (toAList t)`>>
  by rw[]

val ALOOKUP_toAList_list_insert_inj = prove(
  ``!f z x y t. INJ f UNIV UNIV /\ LENGTH x = LENGTH y ==>
    ALOOKUP (MAP (\x,y. (f x,y)) (toAList (list_insert x y t))) z = 
    case ALOOKUP (ZIP ((MAP f x),y)) z of 
      NONE => ALOOKUP (MAP (\x,y. (f x,y)) (toAList t)) z
    | SOME a => SOME a``,
   strip_tac>>strip_tac>>ho_match_mp_tac (fetch "-" "list_insert_ind")>>
  rw[]>-(
    Cases_on`y`>> 
     fs[list_insert_def,LENGTH]) >-(

    fs[list_insert_def]>>
    `lookup x (insert x x'' (list_insert x' y t)) = SOME x''` 
    by fs[lookup_insert]>>
    Q.ABBREV_TAC `tree = (insert x x'' (list_insert x' y t))`
    `MEM (x,x'') (toAList tree) /\ 
      !y. MEM (x,y) (toAList tree) ==> y=x''` by
      fs[MEM_toAList] >>
    `MEM (f x,x'') (MAP (λ(x,y). (f x,y)) (toAList tree)) /\
      !y.MEM (f x,y) (MAP (λ(x,y). (f x,y)) (toAList tree)) ==> y=x''` by
      (CONJ_TAC >-
        (fs[MEM_MAP]>> HINT_EXISTS_TAC >> simp[])>-
      (SPOSE_NOT_THEN ASSUME_TAC>> 
      fs[MEM_MAP]>> Cases_on`y''`>> fs[]>>
      `x=q` by fs[INJ_DEF] >>
      metis_tac[MEM_toAList]) >>
     SPOSE_NOT_THEN ASSUME_TAC>>
     Cases_on`ALOOKUP (MAP (λ(x,y). (f x,y)) (toAList tree)) (f x)`>-
     (*NONE CASE*)
     (fs[alistTheory.ALOOKUP_NONE]>>
     `MEM (f x,x'') (MAP (λ(x,y). (f x,y)) (toAList tree))` by 
       (fs[MEM_MAP]>>HINT_EXISTS_TAC>> fs[])>>
     metis_tac[MEM_MAP,MEM_MAP_FST])>>
     (*SOME CASE*)
     `MEM (f x,x''') (MAP (λ(x,y). (f x,y)) (toAList tree))` 
     by fs[alistTheory.ALOOKUP_MEM]>>
     `MEM (f x,x'') (MAP (λ(x,y). (f x,y)) (toAList tree))` by 
        (fs[MEM_MAP]>> Q.EXISTS_TAC `x,x''` >> rw[])>> 
     `MEM (x,x''') (toAList tree)` by fs[]>> metis_tac[MEM_toAList]>>
    (*OUTER MOST INDUCTIVE CASE*)
    fs[]>>
    `ALOOKUP (MAP (λ(x,y). (f x,y)) 
       (toAList (list_insert (x::x') (x''::y) t))) z =
     ALOOKUP (MAP (λ(x,y). (f x,y)) (toAList (list_insert x' y t))) z`
     by SPOSE_NOT_THEN ASSUME_TAC >>
     Cases_on `ALOOKUP (MAP (λ(x,y). (f x,y)) 
        (toAList (list_insert x' y t))) z`>-
       (*NONE CASE*)
        `?a. f a = z /\ MEM a (MAP FST (toAList (list
`
   fs[]

   
   metis_tac[INJ_DEF]

       metis_tac[]
  fs[MEM_MAP,INJ_DEF]>>CONJ_TAC>>
  


val lookup_fromAList_eq = prove(
  ``!ls x.lookup x (fromAList ls) = ALOOKUP ls x``,
  ho_match_mp_tac (fetch "-" "fromAList_ind")>>
  rw[fromAList_def,lookup_def]>>
  fs[lookup_insert]>> simp[EQ_SYM_EQ])

(*Can make this stronger*)
val domain_list_insert = prove(
  ``!x y t. LENGTH x = LENGTH y ==> 
    domain t SUBSET domain (list_insert x y t)``,
  ho_match_mp_tac (fetch "-" "list_insert_ind")>>
  rw[]>-
    (Cases_on`y`>>rw[list_insert_def]>>fs[LENGTH])>>
  rw[list_insert_def]>>
  metis_tac[pred_setTheory.SUBSET_INSERT_RIGHT,pred_setTheory.SUBSET_TRANS])

(*Prove that get_var gives the same result under an injective f*)
val get_var_inj = prove(
  ``!f v s x. INJ f UNIV UNIV /\ get_var v s = x 
    ==> get_var (f v) (s with locals := apply_nummap_key f s.locals) = x``,
  rpt strip_tac>>
  Cases_on `x`>>
  fs[get_var_def]>-
  (SPOSE_NOT_THEN ASSUME_TAC>>
  fs[lookup_NONE_domain] >>
  IMP_RES_TAC MEM_fromAList>>
  fs[MAP_ZIP]>>
  fs[MEM_MAP]>>
  Cases_on `y`>>
    fs[MEM_toAList]>>
    Cases_on `q=v`>- 
      fs[domain_lookup] 
    >> fs[INJ_DEF] >>metis_tac[]) >> 
  (*FIND A NEATER WAY*)
  Q.ABBREV_TAC `ls = (ZIP
        (MAP (f o FST) (toAList s.locals),
         MAP SND (toAList s.locals)))` >>
  Cases_on `lookup (f v) (fromAList ls)` >> rw[] 
   >-(
    fs[lookup_NONE_domain]>>
    ASSUME_TAC (INST_TYPE [``:'a``|->``:'a word_loc``]MEM_fromAList)>>
    first_x_assum(qspecl_then [`ls`,`f v`] assume_tac)>>
    IMP_RES_TAC MEM_toAList>>
  ASSUME_TAC (INST_TYPE [``:'c``|-> ``:num``,``:'b``|->``:'a word_loc``,``:'a``|-> ``:num``] ZIP_CORRECT) >>
 first_x_assum(qspecl_then [`toAList s.locals`,`v`,`x'`,`f`] mp_tac)>>
  strip_tac>>
  Q.UNABBREV_TAC `ls`>>
  Q.ABBREV_TAC `ls = (ZIP
        (MAP (f o FST) (toAList s.locals),
         MAP SND (toAList s.locals)))` >>
  ASSUME_TAC (INST_TYPE [``:'a`` |-> ``:num``,``:'b``|->``:num``,
                         ``:'c``|->``:'a word_loc``] MEM_MAP_FST)>>
  first_x_assum(qspecl_then [`f`,`v`,`x'`,`ls`] assume_tac)>>
  metis_tac[])>>
  ASSUME_TAC (INST_TYPE [``:'a`` |->``:'a word_loc``] lookup_fromAList) >>
  first_x_assum (qspecl_then [`f v`,`x`,`ls`] assume_tac) >>
  `MEM (v,x') (toAList s.locals)` by metis_tac[MEM_toAList] >>
  `MEM (f v,x') ls` by metis_tac[ZIP_CORRECT]>>
  `!y. MEM (v,y) (toAList s.locals) ==> y=x'` by
    (rw[] >> fs[MEM_toAList]) >>
  `MEM (f v,x) ls` by metis_tac[] >> 
   ASSUME_TAC (INST_TYPE [``:'c``|-> ``:num``,``:'b``|->``:'a word_loc``,``:'a``|-> ``:num``] ZIP_CORRECT_INJ)>>
   first_x_assum (qspecl_then [`toAList s.locals`,`v`] assume_tac) >>
   first_assum(qspecl_then [`x'`,`f`] assume_tac)>>
   first_assum(qspecl_then [`x`,`f`] assume_tac)>>
   metis_tac[]) 

(*Same thing as get_var_inj except for get_vars*)
val get_vars_inj = prove(
  ``!f ls s. INJ f UNIV UNIV ==> get_vars ls s = get_vars (MAP f ls) (s with locals := apply_nummap_key f s.locals)``, 
  strip_tac >> Induct >> rpt strip_tac>> fs[get_vars_def]>>
  ASSUME_TAC get_var_inj >>
  first_x_assum(qspecl_then [`f`,`h`,`s`] assume_tac)>>
  Cases_on `get_var h s` >> 
  fs[]);

(*ALOOKUP under an injective map over the keys*)
val ALOOKUP_MAP_inj = prove(
  ``!f. ALOOKUP (MAP (\x,y. (f x,y)) ls) 
  
(*Helpful:
   traces();
   Goalstack.print_goal_fvs := 1;
    show_types:=true;
    show_types:=false; Or use HJ
 *)

(*Prove that mapping injective f over an exp + initial state gives the same result*)

(*Relation over states parameterized by f*)
val state_rel_def = Define`
  (state_rel f s t <=> (t=s \/ t = s with locals := apply_nummap_key f s.locals))`

(*Prove that mapping injective f over a prog + initial state variables gives the same result and a new state which contains mapped vars*)
val inj_apply_color_invariant = store_thm ("inj_apply_color_invariant",
  ``!prog s s1 f res. wEval(prog,s) = (res,s1) 
                  /\ INJ f UNIV UNIV
                  /\ res <> SOME Error
                  /\ wf s.locals
    ==> ?s2. wEval(apply_color f prog, 
              s with locals := apply_nummap_key f s.locals) = 
        (res,s2) /\ state_rel f s1 s2``,

  ho_match_mp_tac (wEval_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> rw[] >-
  (*Skip*)
  fs[wEval_def] >-

  (*Alloc*)
   >-
  (*Move*)
  fs[MAP_ZIP,wEval_def,get_vars_def,set_vars_def,list_insert_def]>>
  rw[]>> simp[] >-
    Cases_on`ALL_DISTINCT (MAP FST moves)` >>
    fs[]>>
    Cases_on `get_vars (MAP SND moves) s` >>
    fs[]>>
    `get_vars (MAP (f o SND) moves) (s with locals := 
    apply_nummap_key f s.locals) = SOME x` by
    (ASSUME_TAC get_vars_inj>>
    fs[map_compose]>>
    first_x_assum(qspecl_then [`f`,`MAP SND moves`,`s`] assume_tac) >>
    metis_tac[]) >> fs[apply_nummap_key_def]>>
   (*Just need to prove something about list_insert now*)
    (*This follows from get_vars = SOME*)
    `LENGTH moves = LENGTH x` by cheat >>
    fs[ZIP_MAP_EQ]>>rw[]>>
    `!z. lookup z (list_insert (MAP (f o FST) moves) x
    (fromAList (MAP (λ(x,y). (f x,y)) (toAList s.locals)))) =
         lookup z (fromAList (MAP (λ(x,y). (f x,y)) 
    (toAList (list_insert (MAP FST moves) x s.locals))))` by
    rw[lookup_list_insert,lookup_fromAList_eq]>>
    CASE_TAC>-
      (*ALOOKUP NONE*)
      `LENGTH (MAP (f o FST) moves) = LENGTH x` by fs[LENGTH_MAP]>>
      `LENGTH (MAP FST moves) = LENGTH x` by fs[LENGTH_MAP]>>
      fs[alistTheory.ALOOKUP_NONE,MAP_ZIP,LENGTH_MAP]>>
      Cases_on `lookup z (fromAList (MAP (λ(x,y). (f x,y))
       (toAList (list_insert (MAP FST moves) x s.locals))))`>-
        (*NONE*)
        fs[lookup_NONE_domain]>>
        SPOSE_NOT_THEN ASSUME_TAC>>
        `MEM z (MAP FST (MAP (λ(x,y). (f x,y)) (toAList s.locals)))` by
           metis_tac[MEM_fromAList]>>
        fs[MEM_MAP]>>
        `~MEM z (MAP FST (MAP (λ(x,y). (f x,y))
         (toAList (list_insert (MAP FST moves) x s.locals))))` 
        by metis_tac[MEM_fromAList]>>
        fs[alistTheory.ALOOKUP_NONE]>>
        `(FST y') ∈ domain (s.locals)` by 
           (rw[]>>Cases_on`y'`>>
           fs[MEM_toAList,domain_lookup])>>
        `(FST y') ∈ (domain (list_insert (MAP FST moves) x s.locals))` by
           (rw[] >>metis_tac[SUBSET_DEF,domain_list_insert])>>
        `z = f (FST y')` by (Cases_on`y'`>>rw[]>>EVAL_TAC) >>
        `?v. MEM (FST y',v) 
           (toAList (list_insert (MAP FST moves) x s.locals))` by
        metis_tac[MEM_toAList,domain_lookup]>>
        metis_tac[MEM_MAP]
          
    (*Assign*)
    >-
    (*Set*)
    >- 
    (*Store*)
    >-
    (*Tick*)
    >-
    (*Seq*)
    >-
    (*Return*)
    >-
    (*Raise*)
    >-   
    (*If*)
    >-
    (*Call rotate 10 after skip*)
    fs[MAP_ZIP,wEval_def,get_vars_def,set_vars_def,list_insert_def]>>
    Cases_on`s.clock=0`>>fs[]>-
      (rw[call_env_def,fromList2_def,toAList_def]>>EVAL_TAC)>>
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
    fs[rich_listTheory.ZIP_APPEND,MAP_APPEND]>>
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
    (fs[listTheory.MAP_ZIP,listTheory.ALL_DISTINCT_SET_TO_LIST,
       listTheory.ALL_DISTINCT_MAP_INJ,INJ_DEF,listTheory.MEM_SET_TO_LIST]>> 
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

