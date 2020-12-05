(*
  Correctness proof for --
*)

open preamble
     timeSemTheory panSemTheory panPropsTheory
     pan_commonPropsTheory time_to_panTheory

val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem", "pan_commonProps", "time_to_pan"];


Definition clk_rel_def:
  clk_rel clks vname s t <=>
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    FLOOKUP t.locals vname =
    SOME (Struct (MAP (ValWord o n2w o THE o (FLOOKUP s.clocks)) clks))
End


Definition reset_vals_def:
  reset_vals xs ys =
  MAPi (λn x.
         if (MEM n ys)
         then (ValWord 0w)
         else x)
       xs
End


Theorem length_reset_vals_eq:
  ∀ns vs.
    LENGTH (reset_vals vs ns) = LENGTH vs
Proof
  rw [] >>
  fs [reset_vals_def]
QED


Theorem reset_vals_not_indice_same:
  ∀ns vs n.
    ~MEM n ns ∧
    n < LENGTH vs ⇒
    EL n (reset_vals vs ns) = EL n vs
Proof
  rw [] >>
  fs [reset_vals_def]
QED


Theorem reset_vals_el_indice_zero:
  ∀ns vs n.
    MEM n ns ∧
    n < LENGTH vs ⇒
    EL n (reset_vals vs ns) = ValWord 0w
Proof
  rw [] >>
  fs [reset_vals_def]
QED


Theorem opt_mmap_reset_clocks_eq_reset_vals:
  ∀t vs ns clks.
    FLOOKUP t.locals «clks» = SOME (Struct vs) ∧
    LENGTH clks = LENGTH vs ∧
    LENGTH ns ≤ LENGTH clks ⇒
    OPT_MMAP (λa. eval t a)
             (resetClocks «clks» (LENGTH clks) ns) =
    SOME (reset_vals vs ns)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- (
    fs [resetClocks_def] >>
    fs [length_reset_vals_eq]) >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- (
    fs [resetClocks_def] >>
    fs [length_reset_vals_eq]) >>
  rw [] >>
  fs [resetClocks_def] >>
  TOP_CASE_TAC
  >- (
    fs [eval_def] >>
    match_mp_tac reset_vals_el_indice_zero >>
    fs []) >>
  fs [eval_def] >>
  fs [reset_vals_not_indice_same]
QED


Theorem flip_enum_not_mem_alookup:
  ∀xs x n.
    ~MEM x xs ⇒
    ALOOKUP (flipEnum n xs) x = NONE
Proof
  Induct >>
  rw [] >>
  fs [flipEnum_def]
QED


Theorem flip_enum_mem_alookup:
  ∀xs x n.
    MEM x xs ⇒
    ∃m.
      ALOOKUP (flipEnum n xs) x = SOME m ∧
      n <= m ∧ m < n + LENGTH xs
Proof
  Induct >>
  rw [] >>
  fs [flipEnum_def] >>
  fs [flipEnum_def] >>
  TOP_CASE_TAC >> fs [] >>
  last_x_assum drule >>
  disch_then (qspec_then ‘n+1’ mp_tac) >>
  strip_tac >> fs []
QED



Theorem foo:
  ∀ck clks.
    MEM ck clks ⇒
    indiceOf clks ck < LENGTH clks
Proof
  rw [] >>
  fs [indiceOf_def] >>





        , INDEX_OF_def] >>




  fs [indiceOf_def, toNum_def] >>


QED






Theorem foo:
  ∀clks ck.
    MEM ck clks ⇒
    THE (INDEX_OF ck clks) < LENGTH clks
Proof




  Induct >>
  rw [] >>
  fs [indiceOf_def]
  >- fs [INDEX_OF_def, INDEX_FIND_def] >>
  fs [INDEX_OF_def, INDEX_FIND_def] >>
  TOP_CASE_TAC >> fs [] >>
  last_x_assum drule >>
  strip_tac >>
  cheat
QED




Theorem foo:
  ∀ck clks.
    MEM ck clks ⇒
    indiceOf clks ck < LENGTH clks
Proof
  rw [] >>
  fs [indiceOf_def, INDEX_OF_def] >>




  fs [indiceOf_def, toNum_def] >>


QED



(*
  EVERY (λ(t,c). c IN FDOM s.clocks) wt
*)

Theorem calculate_wait_times_eq:
  ∀clks s t wt .
    clk_rel clks «resetClks» s t ∧
    EVERY (λ(t,c). MEM c clks) wt ⇒
    MAP (eval t)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var «resetClks»)) (indicesOf clks (MAP SND wt)))) =
    MAP (SOME ∘ ValWord ∘ n2w ∘ evalDiff s) wt
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2] >>
  rw [waitTimes_def, indicesOf_def, LIST_REL_EL_EQN] >>
  qmatch_goalsub_abbrev_tac ‘MAP2 ff xs ys’ >>
  ‘EL n (MAP2 ff xs ys) =
   ff (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    fs [Abbr ‘xs’, Abbr ‘ys’]) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘xs’] >>
  ‘EL n (MAP FST wt) = FST (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘ys’] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP gg _)’ >>
  ‘EL n (MAP gg wt) = gg (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘gg’, Abbr ‘ff’] >>
  cases_on ‘EL n wt’ >> fs [] >>




  (* first start with timeSem *)
  fs [evalDiff_def, evalExpr_def, EVERY_EL] >>
  last_x_assum drule >>
  fs [] >> strip_tac >>
  fs [clk_rel_def] >>
  fs [EVERY_MEM] >>
  last_x_assum drule >>
  strip_tac >>
  fs [FDOM_FLOOKUP] >>
  fs [minusT_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [eval_def] >>

  fs [clk_rel_def] >>




  (* r needs to be related with clks *)
  ‘indiceOf clks r < LENGTH clks’ by cheat >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘EL m (MAP ff _)’ >>
  ‘EL m (MAP ff clks) = ff (EL m clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’, Abbr ‘m’] >>
  pop_assum kall_tac >>
  ‘FLOOKUP s.clocks (EL (indiceOf clks r) clks) = SOME v’ by cheat >>
  fs [] >>
  fs [wordLangTheory.word_op_def] >>
  cheat (* add assumptions *)
QED


(*
  next theorem should be about min_of
  that min_of are equal
*)




Theorem calculate_wait_times_eq:
  ∀clks s t wt vs vs'.
    clk_rel clks «resetClks» s t ∧
    MAP (eval t)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var «resetClks»)) (indicesOf clks (MAP SND wt)))) = MAP SOME vs  ∧
    MAP (ValWord ∘ n2w ∘ evalDiff s) wt = vs' ⇒
    vs = vs'
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2] >>



QED




Theorem calculate_wait_times_eq:
  ∀clks s t wt n.
    clk_rel clks «resetClks» s t ⇒
    MAP (eval t)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var «resetClks»)) (indicesOf clks (MAP SND wt)))) = SOME vs ∧
    MAP (ValWord ∘ n2w ∘ evalDiff s) wt = vs' ⇒
        vs = vs'
Proof
  rw [] >>


QED


Theorem calculate_wait_times_eq:
  clk_rel clks s t ∧
  FLOOKUP t.locals «resetClks» =
  SOME (Struct (resetClocks «clks» (LENGTH clks) (indicesOf clks tclks))) ⇒
    MAP (eval t)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var «resetClks»)) (indicesOf clks (MAP SND wt)))) =
    MAP (SOME ∘ (λw. ValWord w) ∘ n2w)
        (MAP (evalDiff (s with clocks := resetClocks s.clocks tclks)) wt)
Proof


QED






Theorem foo:

Proof

QED




(*
  waitTimes (MAP FST wt)
  (MAP (λn. Field n (Var «resetClks»)) waitClks)
*)



Definition foo_def:
  foo clks s <=>
    MAP (panLang$Const o n2w o THE o (FLOOKUP s.clocks)) clks
End


Definition about_clocks_def:
  about_clocks clks s t <=>
    EVERY (λck. ck IN FDOM s) clks ∧
    ∃vs. FLOOKUP t.locals «clk» = SOME (Struct vs) ∧
         MAP (panLang$Const o n2w o THE o (FLOOKUP s.clocks)) clks = ARB
End






















Theorem calculate_wait_times_eq:
  MAP (eval t)
  (wait_times «sys_time» (MAP FST wt)
   (MAP
    (λx.
      Field x
            (reset_clocks clks («sys_time» ,«clks» )
             (indices_of clks tclks))) (indices_of clks (MAP SND wt)))) =
  MAP (SOME ∘ (λw. ValWord w) ∘ n2w)
      (MAP (evalDiff (s with clocks := resetClocks s.clocks tclks)) wt)
Proof
  rw [wait_times_def] >>
  fs [MAP_EQ_EVERY2] >>
  rw [] >>
  fs []
  >- fs [indices_of_def] >>
  fs [LIST_REL_EL_EQN] >>
  rw []
  >- fs [indices_of_def] >>
  ‘EL n (MAP (evalDiff (s with clocks := resetClocks s.clocks tclks)) wt) =
   (evalDiff (s with clocks := resetClocks s.clocks tclks)) (EL n wt)’ by cheat >>
  fs [] >>
  pop_assum kall_tac >>
  cases_on ‘EL n wt’ >> fs [] >>
  fs [evalDiff_def] >>
  fs [evalExpr_def] >>
  cases_on ‘FLOOKUP (resetClocks s.clocks tclks) r’ >> fs []
  >- cheat (* add an assumption to make it false *) >>
  ‘EL n
   (MAP2
    (λt e. Op Sub [Op Add [Const (n2w t); Var «sys_time» ]; e])
    (MAP FST wt)
    (MAP
     (λx.
       Field x
             (reset_clocks clks («sys_time» ,«clks» )
              (indices_of clks tclks)))
     (indices_of clks (MAP SND wt)))) =
   (λt e. Op Sub [Op Add [Const (n2w t); Var «sys_time» ]; e])
   (EL n (MAP FST wt)) (EL n (MAP
                   (λx.
                        Field x
                          (reset_clocks clks («sys_time» ,«clks» )
                             (indices_of clks tclks)))
                   (indices_of clks (MAP SND wt))))’ by (
    match_mp_tac EL_MAP2 >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [eval_def] >>
  ‘EL n
                (MAP
                   (λx.
                        Field x
                          (reset_clocks clks («sys_time» ,«clks» )
                             (indices_of clks tclks)))
                   (indices_of clks (MAP SND wt))) =
                   (λx. Field x (reset_clocks clks («sys_time» ,«clks» )
                 (indices_of clks tclks))) (EL n (indices_of clks (MAP SND wt)))’
    by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  cases_on ‘OPT_MMAP (λa. eval t a)
            [Op Add [Const (n2w (EL n (MAP FST wt))); Var «sys_time» ];
             Field (EL n (indices_of clks (MAP SND wt)))
                   (reset_clocks clks («sys_time» ,«clks» )
                    (indices_of clks tclks))]’
  >- cheat >> (* should prove that its wont happen, that systime and clocks are always defined *)
  fs [] >>
  ‘∃tt cc. x' = [ValWord tt; ValWord cc]’ by cheat >>
  fs [] >>
  fs [wordLangTheory.word_op_def] >>
  fs [minusT_def] >>
  ‘n2w (q − x) = n2w q - n2w x’ by cheat >>
  fs [] >>







  cases_on ‘x'’ >>
  fs []


  fs [OPT_MMAP_def, eval_def] >>




    ) >>


EL n
                (MAP
                   (λx.
                        Field x
                          (reset_clocks clks («sys_time» ,«clks» )
                             (indices_of clks tclks)))
                   (indices_of clks (MAP SND wt)))


    ) >>
  fs [] >>









QED

(*
  to start by optimising wait_times
  there should be a better way, to not add sys time

*)

Theorem calculate_wait_times_eq:
  MAP (evalDiff (s with clocks := resetClocks s.clocks tclks)) wt = ts ∧
  wait_times «sys_time» (MAP FST wt)
             (MAP (λx. Field x (reset_clocks clks
                                («sys_time» ,«clks» )
                                (indices_of clks tclks)))
              (indices_of clks (MAP SND wt))) = es ⇒
  MAP (eval t) es = MAP (SOME o ValWord o n2w) ts
Proof
  rw [] >>


QED


(*
  wait_times «sys_time» (MAP FST wt)
*)

(*
calculate_wtime s tclks wt
*)


Theorem foo:
  wait_times «sys_time» (MAP FST wt)
    (MAP (λx.
           Field x
                 (reset_clocks clks
                  («sys_time» ,«clks» )
                  (indices_of clks tclks)))
     (indices_of clks (MAP SND wt)))
Proof
  rw [] >>

QED






Theorem foo:
  evaluate
  (min_of «wake_up_at»
   (wait_times «sys_time» (MAP FST wt)
    (destruct
     (mk_struct (LENGTH clks) («sys_time» ,«clks» )
      (indices_of clks tclks)) (indices_of clks (MAP SND wt)))),
   t with
     locals :=
   t.locals |+ («wait_set» ,value) |+ («wake_up_at» ,value')) =
  (res,s1)
Proof
  rw [] >>
  fs [calculate_wtime_def] >>





QED






Theorem abc:
  evaluate (update_wakeup_time («wake_up_at» ,«sys_time» )
            (wait_times «sys_time» (MAP FST wt)
             (destruct
              (mk_struct (LENGTH clks)
               («sys_time» ,«clks» )
               (indices_of clks tclks))
              (indices_of clks (MAP SND wt)))),
            t with
              locals :=
            t.locals |+ («wait_set» ,value) |+
             («wake_up_at» ,value')) = ARB
Proof
  rw [] >>
  fs [update_wakeup_time_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>



QED



Theorem comp_term_correct:
  ∀s n cnds tclks dest wt s' t clks stime clkvals t.
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    ALL_DISTINCT tclks ∧ ALL_DISTINCT clks ∧
    EVERY (λck. MEM ck clks) tclks ∧
    ALL_DISTINCT (MAP SND wt) ∧
    FLOOKUP t.locals «sys_time» = SOME (ValWord stime) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    LENGTH clkvals = LENGTH clks ∧
    EVERY (λv. ∃w. v = ValWord w) clkvals ⇒
      evaluate (comp_term clks (Tm (Input n) cnds tclks dest wt), t) =
      (SOME (Return ARB), ARB t) ∧ ARB s'
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evalTerm_cases] >>



  fs [resetClocks_def] >>






  fs [comp_term_def, panLangTheory.decs_def,
      panLangTheory.nested_seq_def] >>
  fs [evaluate_def] >>

  fs [calculate_wtime_def] >>




  cases_on ‘tclks’ >> fs []
  >- (
   fs [calculate_wtime_def] >> (* timeSem *)
   fs [resetClocks_def] >>
   fs [FUPDATE_LIST_THM] >>
   ‘s with clocks := s.clocks = s’ by cheat >>
   fs [] >>
   pop_assum kall_tac >>
   (* prove corresondance between list_min_option and min_of *)


    (* panLang *)
   fs [indices_of_def] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>



   fs [update_wakeup_time_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [destruct_def] >>
   fs [wait_times_def] >>
   fs [mk_struct_def] >>
   fs [MAP_MAP_o] >>


    fs [min_of_def] >>



    fs [OPT_MMAP_def] >>


  )






QED



(* EVERY (λck. ck IN FDOM s.clocks) tclks ∧ *)




Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  ALL_DISTINCT tclks ∧
  ALL_DISTINCT clks ∧
  EVERY (λck. MEM ck clks) tclks ∧
  ALL_DISTINCT (MAP SND wt) ∧
  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
  LENGTH clkvals = LENGTH clks ∧
  EVERY (λv. ∃w. v = ValWord w) clkvals ∧







  evaluate (comp_term clks (Tm io cnds tclks dest wt), t) =
  (SOME (Return ARB), t')
Proof


QED





  (* is it derivable from the def of evalTerm *)
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
  tms = (Tm io cnds tclks dest wt) :: tmss ∧
  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_term («clks»,clks) tms) ∧

Proof

QED







(* :timeSem$state -> num option -> term -> timeSem$state -> bool *)
Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧

  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_step («clks»,clks) tms) ∧
  (* assume that comp_conditions (vname, clks) cds holds for the current state
     so that I get to reason about comp_term then *) ∧





  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  (* clkvals and tclks follow some order *)
  FLOOKUP t.locals «task_ret» = SOME (Struct [Struct clkvals; wset; wtime; lc]) ∧
  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_step («clks»,clks) tms) ∧
  (* assume that comp_conditions (vname, clks) cds holds for the current state
     so that I get to reason about comp_term then *) ∧
  evaluate (Call (Ret «task_ret» NONE) (Var «location»)
            [Var «sys_time»; Field 0 (Var «task_ret»)]) =
  (Return ARB,t')
Proof
QED

(*
   FLOOKUP st_code (toString loc) =
      SOME ([(«sys_time», One); («clks», gen_shape n)],
            comp_terms comp_step («clks»,clks) tms)
*)

(*
  assume that comp_conditions (vname, clks) cds holds for the current state
  so that I get to reason about comp_term then
*)

(*
  comp_conditions («clks»,clks) cds
  what will happen when none of the conditions are not true
*)


(* :timeSem$state -> num option -> term -> timeSem$state -> bool *)
Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  (* is it derivable from the def of evalTerm *)
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
  tms = (Tm io cnds tclks dest wt) :: tmss ∧
  FLOOKUP t.code loc =
    SOME ([(«sys_time», One); («clks», gen_shape n)],
          comp_terms comp_term («clks»,clks) tms) ∧










  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  (* clkvals and tclks follow some order *)
  FLOOKUP t.locals «task_ret» = SOME (Struct [Struct clkvals; wset; wtime;lc]) ∧
  FLOOKUP t.code loc = SOME ARB

Proof
QED


  t.code = code is installed for the term ∧






  Call (Ret «task_ret» NONE) (Var «location»)
       [Var «sys_time»; Field 0 (Var «task_ret»)
        (* elapsed time clock variables *)]




Proof


QED





(* ioAction and io are related *)

Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks loc wt) t ∧
  comp_term clks (Tm io cnds tclks loc wt) = Return (Struct [])
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [step_def]

QED





Definition code_installed_def:
  code_installed prog st_code <=>
  ∀loc tms.
    MEM (loc,tms) prog ⇒
    let clks = clks_of prog;
        n = LENGTH clks
    in
      FLOOKUP st_code (toString loc) =
      SOME ([(«sys_time», One); («clks», gen_shape n)],
            comp_terms comp_step («clks»,clks) tms)
End

(*
  ta_prog = (prog, init_wtime) ∧
  res = NONE would ensure that the FFI returned with the correct results
*)

(*
  about ioAction:
  should be none in the beginning

  state relations:
  we can set up intitial wait time for s
*)

Theorem time_to_pan_compiler_correct:
  step prog label s s' ∧
  (* prog ≠ [] ∧ *)
  s.waitTime = wtime ∧
  s.location = FST (ohd prog) ∧
  (FDOM s.clocks) = set (clks_of prog) ∧
  s.ioAction = NONE ∧
  code_installed prog t.code ∧
  evaluate (start_controller (prog,wtime), t) = (res, t') ∧
  res = NONE ⇒
    something
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [step_def]

QED



Theorem time_to_pan_compiler_correct:
  step prog label s s' ∧
  s.waitTime = wtime ∧
  s.location = FST (ohd prog) ∧
  (FDOM s.clocks) = set (clks_of prog) ∧
  s.ioAction = NONE ∧
  code_installed prog t.code ⇒
  ∃ck. evaluate (main_while_loop, t with clock := t.clock + ck) =
       evaluate (main_while_loop, t') ∧
       state_rel s' t'
Proof
QED

(*
  ioaction of timeSem state represents the triggered action or action generated to
  reach to a particular state
*)


(*
  timeSem permits:
  1. a delay transition with no ioaction
  2. action transition, (input or output), time does not pass in these transitions

  what is the behavior of the corresponding pancake program:
  1. delay transitions:
     1. stay within the loop, waiting for the input trigger
     2. stay within the loop, waiting for the wakeup time or input trigger

  2. action tanstion:
     1. input trigger: break the loop, call the function
     2. output transtion: happens only within the call
        (I think), signal the output

  pickTerm and evalTerm are also relevant
  time semantics only talk about delay, input, but also pick term and evaluate term
  I think while loop related conditions should come from pickterm and evalterm
*)


(*
  what is the difference between step_ind and step_strongind
  the induction rule is phrased differently (step_ind)
   step _ _ _ _ => step' _ _ _
*)


Theorem foo:
  ∀prog label st st'.
    step prog label st st' ⇒
    (∀t wtime s res s'.
       prog ≠ [] ⇒
       evaluate (start_controller (prog,wtime), s) = (res, s'))
Proof

QED




Theorem abc:
  ∀prog label st st'.
    step prog label st st' ⇒
     step prog label st st'
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [step_def]

QED




Theorem abc:
  ∀prog label st st'.
    step prog label st st' ⇒
    (∀t wtime s res s'.
       prog ≠ [] ⇒
       evaluate (start_controller (prog,wtime), s) = (res, s'))
Proof
  ho_match_mp_tac step_ind >>
  rw [] >>
  fs [] >>

  fs [start_controller_def] >>
  fs [task_controller_def] >>
  fs [] >>







QED



Theorem abc:
  ∀prog label st st'.
    step prog label st st' ⇒
    (∀t.
       label = (LDelay t) ⇒
       evaluate (start_controller (prog,init_wake_time),s) = (res,t))
Proof
  ho_match_mp_tac step_ind >>
  rw [] >> fs [] >>



QED


(*
  step (FST prog) label st st' ∧
  evaluate (start_controller prog,s) = (res,t)
*)







(* might not be needed *)
Definition clk_rel_def:
  clk_rel str st =
     ARB str.clocks st.locals
End

(*
  we need some assumptions on FFI

*)




(*
  1. step (FST prog) label st st'
  2. evaluate (start_controller prog,s) = (res,t)
  3. what is the relation with st and s

Datatype:
  store =
  <| clocks   : clock |-> time
   ; location : loc
   ; consumed : in_signal option
   ; output   : out_signal option
   ; waitTime : time option
  |>
End

*)



(*
  store
  state

  "timeSem", "step_def"
  "timeSem", "step_ind"
  "timeSem", "step_rules"
  "timeSem", "step_strongind"

*)





val _ = export_theory();
