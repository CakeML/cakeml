open HolKernel Parse boolLib bossLib miscLib
open listTheory sptreeTheory pred_setTheory pairTheory
open bvp_lemmasTheory
open word_langTheory word_lemmasTheory
open alistTheory BasicProvers
open sptreeTheory

val _ = new_theory "word_proc";

(*TODO: Rework this file into preliminary definitions (and simple helpers) 
  for word_lang transformations
  
  The transformation passes should be moved out (deleted after SSA is done)
  *)

(*Variable conventions of wordLang*)

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

val is_stack_var_def = Define`
  is_stack_var (n:num) = (n MOD 4 = 3)`
val is_phy_var_def = Define`
  is_phy_var (n:num) = (n MOD 2 = 0)`
val is_alloc_var_def = Define`
  is_alloc_var (n:num) = (n MOD 4 = 1)`

val convention_partitions = store_thm("convention_partitions",``
  ∀n. (is_stack_var n ⇔ (¬is_phy_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_phy_var n ⇔ (¬is_stack_var n) ∧ ¬(is_alloc_var n)) ∧
      (is_alloc_var n ⇔ (¬is_phy_var n) ∧ ¬(is_stack_var n))``,
  rw[is_stack_var_def,is_phy_var_def,is_alloc_var_def,EQ_IMP_THM]
  \\ `n MOD 2 = (n MOD 4) MOD 2` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``2*2:num``)]
    \\ fs [arithmeticTheory.MOD_MULT_MOD])
  \\ fs []
  \\ `n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs []);

(*Preference edges*)
(*Create a list of preferences from input program
  Some of these will be invalid preferences (e.g. 0<-2)
  The priority is added to the front of each Move pair
  TODO: Check if we should support things like Assign Var Var -- Should be just compiled to Move when eliminating expressions
*)

val get_prefs_def = Define`
  (get_prefs (Move pri ls) acc = (MAP (λx,y. (pri,x,y)) ls) ++ acc) ∧ 
  (get_prefs (Seq s1 s2) acc =
    get_prefs s1 (get_prefs s2 acc)) ∧
  (get_prefs (If cmp num rimm e2 e3) acc =
    get_prefs e2 (get_prefs e3 acc)) ∧
  (get_prefs (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) acc =
    case h of 
      NONE => get_prefs ret_handler acc
    | SOME (v,prog,l1,l2) => get_prefs prog (get_prefs ret_handler acc)) ∧ 
  (get_prefs prog acc = acc)`


(*Coloring expressions*)
val apply_colour_exp_def = tDefine "apply_colour_exp" `
  (apply_colour_exp f (Var num) = Var (f num)) /\
  (apply_colour_exp f (Load exp) = Load (apply_colour_exp f exp)) /\
  (apply_colour_exp f (Op wop ls) = Op wop (MAP (apply_colour_exp f) ls)) /\
  (apply_colour_exp f (Shift sh exp nexp) = Shift sh (apply_colour_exp f exp) nexp) /\
  (apply_colour_exp f expr = expr)`
(WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC);

val apply_colour_imm_def = Define`
  (apply_colour_imm f (Reg n) = Reg (f n)) ∧ 
  (apply_colour_imm f x = x)`

(*Colouring instructions*)
val apply_colour_inst_def = Define`
  (apply_colour_inst f Skip = Skip) ∧ 
  (apply_colour_inst f (Const reg w) = Const (f reg) w) ∧
  (apply_colour_inst f (Arith (Binop bop r1 r2 ri)) = 
    Arith (Binop bop (f r1) (f r2) (apply_colour_imm f ri))) ∧ 
  (apply_colour_inst f (Arith (Shift shift r1 r2 n)) =
    Arith (Shift shift (f r1) (f r2) n)) ∧ 
  (apply_colour_inst f (Mem Load r (Addr a w)) =
    Mem Load (f r) (Addr (f a) w)) ∧ 
  (apply_colour_inst f (Mem Store r (Addr a w)) =
    Mem Store (f r) (Addr (f a) w)) ∧
  (apply_colour_inst f x = x)` (*Catchall -- for future instructions to be added*) 

(*Apply f to the keys of a num_map, numsets are special cases with values ()*)
val apply_nummap_key_def = Define `
  apply_nummap_key f nummap = fromAList (
                                 ZIP (MAP (f o FST) (toAList nummap),
                                      MAP SND (toAList nummap)))`

val apply_numset_key_def = Define `
  apply_numset_key f (numset:num_set) = apply_nummap_key f numset`

(*Colour a prog*)
val apply_colour_def = Define `
  (apply_colour f Skip = Skip) ∧
  (apply_colour f (Move pri ls) =
    Move pri (ZIP (MAP (f o FST) ls, MAP (f o SND) ls))) ∧ 
  (apply_colour f (Inst i) = Inst (apply_colour_inst f i)) ∧
  (apply_colour f (Assign num exp) = Assign (f num) (apply_colour_exp f exp)) ∧
  (apply_colour f (Get num store) = Get (f num) store) ∧  
  (apply_colour f (Store exp num) = Store (apply_colour_exp f exp) (f num)) ∧ 
  (apply_colour f (Call ret dest args h) =
    let ret = case ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (f v,apply_nummap_key f cutset,apply_colour f ret_handler,l1,l2) in
    let args = MAP f args in
    let h = case h of NONE => NONE
                     | SOME (v,prog,l1,l2) => SOME (f v, apply_colour f prog,l1,l2) in
      Call ret dest args h) ∧ 
  (apply_colour f (Seq s1 s2) = Seq (apply_colour f s1) (apply_colour f s2)) ∧  
  (apply_colour f (If cmp r1 ri e2 e3) =
    If cmp (f r1) (apply_colour_imm f ri) (apply_colour f e2) (apply_colour f e3)) ∧ 
  (apply_colour f (Alloc num numset) =
    Alloc (f num) (apply_nummap_key f numset)) ∧
  (apply_colour f (Raise num) = Raise (f num)) ∧ 
  (apply_colour f (Return num1 num2) = Return (f num1) (f num2)) ∧
  (apply_colour f Tick = Tick) ∧
  (apply_colour f (Set n exp) = Set n (apply_colour_exp f exp)) ∧
  (apply_colour f p = p )
`
val _ = export_rewrites ["apply_nummap_key_def","apply_colour_exp_def"
                        ,"apply_colour_inst_def","apply_colour_def"
                        ,"apply_colour_imm_def"];

(*We will frequently need to express a property over every variable in the 
  program
  NOTE: This is defined over the current non-faulting instructions
  specificially, the var check for insts of the form
    Mem Load8 etc. is not properly defined
  *)
val every_var_exp_def = tDefine "every_var_exp" `
  (every_var_exp P (Var num) = P num) ∧
  (every_var_exp P (Load exp) = every_var_exp P exp) ∧ 
  (every_var_exp P (Op wop ls) = EVERY (every_var_exp P) ls) ∧ 
  (every_var_exp P (Shift sh exp nexp) = every_var_exp P exp) ∧  
  (every_var_exp P expr = T)`
(WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
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

(*Probably needs the restriction that
  return location and call locations are 0*)
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

(*Flow of calling conventions:

Input -- Any wordLang program
⇒ 
SSA -- Every stack location satisfies is_stack_var and Calls have args 0 ..
These will be called pre_alloc_conventions
⇒ 
RegAlloc k -- Every location satisfies is_phy_var, stack locations satisfy is_stack_var and ≥ 2*k and Calls have args 0 ...
These will be called post_alloc_conventions

*)

val pre_alloc_conventions_def = Define`
  pre_alloc_conventions p =
    (every_stack_var is_stack_var p ∧ 
    call_arg_convention p)`

val post_alloc_conventions_def = Define`
  post_alloc_conventions k prog =
    (every_var is_phy_var prog ∧ 
    every_stack_var (λx. x ≥ 2*k) prog ∧ 
    call_arg_convention prog)`     

(*Useful lemmas about every_var*)

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

(*Composing with a function using apply_colour*)
val every_var_inst_apply_colour_inst = store_thm("every_var_inst_apply_colour_inst",``
  ∀P inst Q f.
  every_var_inst P inst ∧
  (∀x. P x ⇒ Q (f x)) ⇒ 
  every_var_inst Q (apply_colour_inst f inst)``,
  ho_match_mp_tac (fetch "-" "every_var_inst_ind")>>rw[every_var_inst_def]>>
  TRY(Cases_on`ri`>>fs[apply_colour_imm_def])>>
  EVERY_CASE_TAC>>fs[every_var_imm_def])

val every_var_exp_apply_colour_exp = store_thm("every_var_exp_apply_colour_exp",``
  ∀P exp Q f.
  every_var_exp P exp ∧ 
  (∀x. P x ⇒ Q (f x)) ⇒ 
  every_var_exp Q (apply_colour_exp f exp)``,
  ho_match_mp_tac (fetch "-" "every_var_exp_ind")>>rw[every_var_exp_def]>>
  fs[EVERY_MAP,EVERY_MEM])

val every_var_apply_colour = store_thm("every_var_apply_colour",``
  ∀P prog Q f.
  every_var P prog ∧
  (∀x. P x ⇒ Q (f x)) ⇒
  every_var Q (apply_colour f prog)``,
  ho_match_mp_tac (fetch "-" "every_var_ind")>>rw[every_var_def]>>
  fs[MAP_ZIP,(GEN_ALL o SYM o SPEC_ALL) MAP_MAP_o]>>
  fs[EVERY_MAP,EVERY_MEM]
  >-
    metis_tac[every_var_inst_apply_colour_inst]
  >-
    metis_tac[every_var_exp_apply_colour_exp]
  >-
    metis_tac[every_var_exp_apply_colour_exp]
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>fs[every_var_def,EVERY_MAP,EVERY_MEM]>>
    rw[]>>fs[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`x'`>>fs[MEM_toAList,domain_lookup])
  >-
    (Cases_on`ri`>>fs[every_var_imm_def])
  >-
    (fs[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`x'`>>fs[MEM_toAList,domain_lookup])
  >>
    metis_tac[every_var_exp_apply_colour_exp])

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

val every_stack_var_apply_colour = store_thm("every_stack_var_apply_colour",``
  ∀P prog Q f.
  every_stack_var P prog ∧
  (∀x. P x ⇒ Q (f x)) ⇒
  every_stack_var Q (apply_colour f prog)``,
  ho_match_mp_tac (fetch "-" "every_stack_var_ind")>>rw[every_stack_var_def]
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>fs[every_stack_var_def,EVERY_MAP,EVERY_MEM]>>
    rw[]>>fs[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`x'`>>fs[MEM_toAList,domain_lookup])
  >>
    (fs[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`x'`>>fs[MEM_toAList,domain_lookup]))

val in_clash_sets_def = Define`
  in_clash_sets (ls: ('a num_map) list) x = ∃y. MEM y ls ∧ x ∈ domain y`

(*Find a value that is larger than everything else
  For SSA, we will make it 4*n+1
  For stack locations we will make it 4*n+3
*)
(*val limit_var_exp_def = tDefine "limit_var_exp" `
  (limit_var_exp (Const _) = 1) ∧ 
  (limit_var_exp (Var n) = 2* n +1) ∧ 
  (limit_var_exp (Lookup _) = 1) /\
  (limit_var_exp (Load exp) = limit_var_exp exp) /\
  (limit_var_exp (Op op exps) = FOLDL (\x y. MAX x (limit_var_exp y)) 1 exps) /\
  (limit_var_exp (Shift sh exp nexp) = limit_var_exp exp)`
  (WF_REL_TAC `measure (word_exp_size ARB )`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)
*)
val _ = export_theory();
