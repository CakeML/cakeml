(*
  Correctness proof for --
*)

open preamble
     timeSemTheory panSemTheory
     time_to_panTheory

val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem", "time_to_pan"];


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
*)




(*
 what are input and output

*)



(*
(!p st d.
    st.waitTime = NONE /\
    (0:num) <= d ==>
    step p (LDelay d) st
         (mkStore
          (delay_clocks (st.clocks) d)
          st.location
          NONE
          NONE
          NONE))
*)



Theorem abc:
  ∀prog label st st' ta_prog.
    step prog label st st' ∧
     prog = FST ta_prog ⇒ step' a0
Proof
  ho_match_mp_tac step_ind >>
  rw [] >> fs []


QED



(*

  try setting up an induction theorem:





*)






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
