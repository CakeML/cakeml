open HolKernel Parse boolLib bossLib; 

val _ = new_theory "word_proc";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs bvpTheory;
open word_langTheory

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

(*Apply f to the keys of a num_map*)
val apply_key_numset_def = Define `
  (apply_numset f nummap = fromAList (MAP (\x,y.f x,y) (toAList nummap)))`

(*TODO: Coloring a prog*)
val apply_color_def = Define `
  (apply_color f Skip = Skip) /\
  (apply_color f (Move ls) = 
    Move (ZIP (MAP (f o FST) ls, MAP (f o SND) ls))) /\
  (apply_color f (Assign num exp) = Assign (f num) (apply_color_exp f exp)) /\
  (apply_color f (Store exp num) = Store (apply_color_exp f exp) (f num)) /\
  (apply_color f (Call ret dest args h) = 
    let ret = case ret of NONE => NONE 
                        | SOME (v,cutset) => 
                             SOME (f v,apply_numset f cutset) in
    let dest = case dest of NONE => NONE
                          | SOME n => SOME (f n) in
    let args = MAP f args in
    let h = case h of NONE => NONE
                     | SOME (v,prog) => SOME (f v, apply_color f prog) in
      Call ret dest args h) /\
  (apply_color f (Seq s1 s2) = Seq (apply_color f s1) (apply_color f s2)) /\
  (apply_color f (If e1 num e2 e3) = 
    If (apply_color f e1) (f num) (apply_color f e2) (apply_color f e3)) /\
  (*Need a map over numsets*)
  (apply_color f (Alloc num numset) = Alloc (f num) (apply_numset f numset)) /\
  (apply_color f (Raise num) = Raise (f num)) /\
  (apply_color f (Return num) = Return (f num)) /\ 
  (apply_color f Tick = Tick)/\
  (apply_color f p = p )
`
(*
EVAL ``apply_color (\x.x+1) (Seq (Call (SOME (5,LN)) (SOME 4) [3;2;1] NONE) Skip)``
*)

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
    Cases_on `get_vars l s` >> fs[])>>
  Q.UNABBREV_TAC `args`>>
  rw[wEval_def]>-
    (fs[listTheory.MAP_ZIP,listTheory.ALL_DISTINCT_SET_TO_LIST,
       listTheory.ALL_DISTINCT_MAP_INJ,INJ_DEF,listTheory.MEM_SET_TO_LIST]>> 
    first_x_assum(qspec_then`SET_TO_LIST (domain s.locals)`mp_tac) >>
    simp[] >> Q.ABBREV_TAC `args = SET_TO_LIST (domain s.locals)`>>
    rw[] >>
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

