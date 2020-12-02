(*
  Correctness proof for --
*)

open preamble
     timeSemTheory panSemTheory
     time_to_panTheory

val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem", "time_to_pan"];

(* :timeSem$state -> num option -> term -> timeSem$state -> bool *)
Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
  FLOOKUP t.locals «sys_time» = SOME (ValWord systime) ∧
  (* clkvals and tclks follow some order *)
  FLOOKUP t.locals «task_ret» = SOME (Struct [Struct clkvals; wset; wtime;lc]) ∧
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


(* :timeSem$state -> num option -> term -> timeSem$state -> bool *)
Theorem comp_term_correct:
  evalTerm s ioAction (Tm io cnds tclks dest wt) s' ∧
  EVERY (λck. ck IN FDOM s.clocks) tclks ∧
  (* is it derivable from the def of evalTerm *)
  FLOOKUP t.locals «location» = SOME (ValLabel loc) ∧
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
