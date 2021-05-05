(*
  Correctness proof for --
*)

open preamble
     timeFunSemTheory
     time_to_panProofTheory


val _ = new_theory "time_to_panSemProof";

val _ = set_grammar_ancestry
        ["timeFunSem",
         "time_to_panProof"];





Datatype:
  observed_io = ObsTime    num
              | ObsInput   num
              | ObsOutput  num
End




Theorem timed_automata_correct:
  ∀k prog or st sts labels (t:('a,time_input) panSem$state).
    eval_steps k prog
               (dimword (:α) - 1) (FST (t.ffi.ffi_state 0))
               or st = SOME (labels, sts) ∧
    prog ≠ [] ∧ LENGTH (clksOf prog) ≤ 29 ∧
    LENGTH sts = LENGTH labels ∧
    st.location =  FST (ohd prog) ∧
    init_clocks st.clocks (clksOf prog) ∧
    (* merge these two into one *)
    code_installed t.code prog ∧
    FLOOKUP t.code «start» =
      SOME ([], start_controller (prog,st.waitTime)) ∧
    well_formed_code prog t.code ∧
    mem_config t.memory t.memaddrs t.be ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    t.ffi =
    build_ffi (:'a) t.be (MAP explode (out_signals prog))
              t.ffi.ffi_state t.ffi.io_events ∧
    init_ffi t.ffi.ffi_state ∧
    input_time_rel t.ffi.ffi_state ∧
    time_seq t.ffi.ffi_state (dimword (:α)) ∧
    ffi_rels_after_init prog labels st t ∧
    good_dimindex (:'a) ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog)) ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (t.ffi.io_events ++ io::ios) ∧
      LENGTH labels = LENGTH ns ∧
      SUM ns ≤ LENGTH ios ∧
      decode_ios (:α) t.be labels ns
                 (io::TAKE (SUM ns) ios)
Proof
  rw [] >>
  dxrule eval_steps_imp_steps >>
  strip_tac >>
  metis_tac [timed_automata_correct]
QED





Definition recover_time_input_def:
  recover_time_input (:'a) be l =
  let ns =
      MAP w2n
          ((words_of_bytes: bool -> word8 list -> α word list) be (MAP SND l))
  in
    (EL 0 ns, EL 1 ns)
End


Definition decode_io_event_def:
  decode_io_event (:'a) be (IO_event s conf l) =
    if s ≠ "get_time_input" then (ObsOutput (toNum s))
    else (
      let
        (time,input) = recover_time_input (:'a) be l
      in
        if input = 0 then (ObsTime time)
        else (ObsInput input))
End

Definition decode_io_events_def:
  decode_io_events (:'a) be ios =
   MAP (decode_io_event (:'a) be) ios
End

Definition rem_delay_dup_def:
  (rem_delay_dup [] = ARB) ∧
  (rem_delay_dup (io::ios) =
     case io of
     |





  )
End


(*
 (("ASCIInumbers", "toString_toNum_cancel"),
     (⊢ ∀n. toNum (toString n) = n, Thm))
*)




(*
  thoughts:
  write a func that decodes io_events

*)




(*
   eval_steps (LENGTH labels) prog (dimword (:α) - 1) n or st =
   SOME (labels, sts)
*)




(* forward style *)
Theorem eval_steps_thm:
  ∀prog n or st labels sts (t:('a,time_input) panSem$state).
    eval_steps (LENGTH labels) prog (dimword (:α) - 1) n or st ([],[]) =
    SOME (labels, sts) ∧
    assumptions prog labels n st t ⇒
    evaluations prog labels sts t
Proof
  rw [] >>
  fs [] >>
  imp_res_tac eval_steps_imp_steps >>
  match_mp_tac steps_thm >>
  metis_tac []
QED


Theorem foo:
  ∀prog n or st labels sts (t:('a,time_input) panSem$state).
    eval_steps (LENGTH labels) prog (dimword (:α) - 1) n or st ([],[]) =
    SOME (labels, sts) ∧
    assumptions prog labels n st t ⇒
    ∃io_events.
      semantics t start = Terminate Success io_events
Proof

QED









(*** to be flipped ***)
(*
eval_step prog m n or orn st = SOME (label, st') ⇒
 assumptions prog labels n st t ⇒
  ∃io_events.
    semantics_pancake t = Terminate Success io_events
    (* io_events and (labels + oracle) are related *)
*)




Theorem steps_thm:
  evaluate (time_to_pan$always (nClks prog), t) =
  evaluate (time_to_pan$always (nClks prog), nt) ∧
  assumptions prog [label] n st t ⇒
  ∃sts.
    steps prog [label] (dimword (:α) - 1) n st [sts] ∧
    state_rel (clksOf prog) (out_signals prog) st nt
    (* and more *)
Proof
  rw [] >>
  fs [] >>






QED








(*
Definition semantics_def:
  semantics ^s start =
   let prog = Call Tail (Label start) [] in
    if ∃k. case FST (evaluate (prog,s with clock := k)) of
            | SOME TimeOut => F
            | SOME (FinalFFI _) => F
            | SOME (Return _) => F
            | _ => T
    then Fail
    else
     case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (r,t) ∧
        (case r of
         | (SOME (FinalFFI e)) => outcome = FFI_outcome e
         | (SOME (Return _))   => outcome = Success
         | _ => F) ∧
        res = Terminate outcome t.ffi.io_events
      of
    | SOME res => res
    | NONE =>
      Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList
              (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
End
*)






(*

(* start with only one state *)
Theorem steps_thm:
  ∀label prog n st sts (t:('a,time_input) panSem$state).
    evaluations prog [label] [sts] t ∧
    assumptions prog [label] n st t ⇒
      steps prog [label] (dimword (:α) - 1) n st [sts]
Proof

QED
*)

(*
We have:

  s_eval x s = (s_res,s1) /\ state_rel s t ==>
  ?t1 t_res. t_eval (compile x) t = (t_res,t1) /\ state_rel s1 t1

We want:

  t_eval (compile x) t = (t_res,t1) /\ state_rel s t ==>
  ?s1 s_res. s_eval x s = (s_res,s1) /\ state_rel s1 t1

Proof:
  t_eval (compile x) t = (t_res,t1)
  state_rel s t
  s_eval x s = (s_res,s1)
  ?t1' t_res'. t_eval (compile x) t = (t_res',t1') /\ state_rel s1' t1'
  ?t1' t_res'. (t_res,t1) = (t_res',t1') /\ state_rel s1' t1'
  state_rel s1 t1


Plan:
  - define new alt version of steps that separates input from output
  - require that steps_eval is total
  step_eval s or = SOME (s',labels)
  step_eval s or = SOME (s',label) ==>
  step label s s'
*)



val _ = export_theory();
