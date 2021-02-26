(*
  Correctness proof for --
*)

open preamble
     time_to_panProofTheory


val _ = new_theory "ntime_to_panProof";

val _ = set_grammar_ancestry
        ["time_to_panProof"];

Definition local_action_def:
  (local_action (Input i) t =
     (FLOOKUP t.locals «isInput» = SOME (ValWord 0w))) ∧
  (local_action (Output os) t =
    (FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
     FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
     FLOOKUP t.locals «waitSet» = SOME (ValWord 0w)))
End

Definition local_state_def:
  (local_state (LDelay _) t =
   (FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event» = SOME (ValWord 0w))) ∧
  (local_state (LAction act) t = local_action act t)
End

(*
Definition event_state_def:
  event_state t ⇔
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event»   =  SOME (ValWord 0w)
End


(* taken from the conclusion of individual step thorems *)
Definition next_ffi_state_def:
  (next_ffi_state (LDelay d) ffi (t:('a,time_input) panSem$state) ⇔
   ∀cycles.
     delay_rep d ffi cycles ⇒
     t.ffi.ffi_state = nexts_ffi cycles ffi) ∧
  (next_ffi_state (LAction _) ffi t ⇔ t.ffi.ffi_state = ffi)
End
*)

Definition action_rel_def:
  (action_rel (Input i) s (t:('a,time_input) panSem$state) =
   input_rel t.locals i t.ffi.ffi_state) ∧
  (action_rel (Output os) s t =
   output_rel t.locals s.waitTime t.ffi.ffi_state)
End

(* add the resulting ffi' here *)
Definition ffi_rel_def:
  (ffi_rel (LDelay d) s (t:('a,time_input) panSem$state) ffi =
   ∃cycles.
     delay_rep d t.ffi.ffi_state cycles ∧
     wakeup_rel t.locals s.waitTime t.ffi.ffi_state cycles ∧
     mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
     ffi = nexts_ffi cycles t.ffi.ffi_state) ∧
  (ffi_rel (LAction act) s t ffi =
     (action_rel act s t ∧
      ffi = t.ffi.ffi_state))
End

Definition ffi_rels_def:
  (ffi_rels prog [] s (t:('a,time_input) panSem$state) ⇔ T) ∧
  (ffi_rels prog (label::labels) s t ⇔
   ∃ffi.
     ffi_rel label s t ffi ∧
     ∀s' (t':('a,time_input) panSem$state) m n.
       step prog label m n s s' ∧
       t'.ffi.ffi_state = ffi ⇒
       ffi_rels prog labels s' t')
End


Definition always_def:
  always clksLength =
  While (Const 1w)
        (task_controller clksLength)
End


Theorem foo:
  ∀prog s s' labels (t:('a,time_input) panSem$state).
    stepTrace prog
              (dimword (:α) - 1)
              (FST (t.ffi.ffi_state 0)) s s' labels ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rels prog labels s t ∧
    labProps$good_dimindex (:'a) ∧
    local_state HD labels t ∧
    (* we shoud be able to prove that this stays as an invariant
       after each invocation of the task *)
    (* should we assume that labels are non-empty *) ⇒
    ?ck t'.
      evaluate (always (nClks prog), t with clock := t.clock + ck) =
      evaluate (always (nClks prog), t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog
Proof
QED





(*
Definition next_wakeup_def:
  (next_wakeup (LDelay _) (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) =
   (FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt»)) ∧
  (next_wakeup (LAction _) t t' =
   (t'.ffi.ffi_state = t.ffi.ffi_state ∧
    (∃wt.
       FLOOKUP t'.locals «wakeUpAt» =
       SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
       FST (t.ffi.ffi_state 0) + wt < dimword (:α))))
End
*)


(*
Theorem step_thm:
  !prog label s s' (t:('a,time_input) panSem$state) ck_extra.
    step prog label s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ⇒
    case label of
    | LDelay d =>
        ∀cycles.
          delay_rep (dimword (:α)) d t.ffi.ffi_state cycles ∧
          wakeup_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state cycles ∧
          mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
          FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ⇒
          ?ck t'.
            evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
            evaluate (task_controller (nClks prog), t' with clock := t'.clock + ck_extra) ∧
            code_installed t'.code prog ∧
            state_rel (clksOf prog) s' t' ∧
            t'.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
            t'.ffi.oracle = t.ffi.oracle ∧
            FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
            FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
            FLOOKUP t'.locals «sysTime»  =
            SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles))))
    | LAction (Input i) =>
        well_formed_terms prog s t ∧
        input_rel t.locals (dimword (:α)) i t.ffi.ffi_state ∧
        FLOOKUP t.locals «isInput» = SOME (ValWord 0w) ∧
        task_ret_defined t.locals (nClks prog) ⇒
        ?ck t'.
          evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
          (NONE, t') ∧
          code_installed t'.code prog ∧
          state_rel (clksOf prog) s' t' ∧
          t'.ffi.ffi_state = t.ffi.ffi_state ∧
          t'.ffi.oracle = t.ffi.oracle ∧
          FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
          FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
          FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
          task_ret_defined t'.locals (nClks prog) ∧
          (∃wt.
             FLOOKUP t'.locals «wakeUpAt» =
             SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
             FST (t.ffi.ffi_state 0) + wt < dimword (:α))
    | LAction (Output os) =>
        well_formed_terms prog s t ∧
        output_rel t.locals (dimword (:α)) s.waitTime t.ffi.ffi_state ∧
        FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
        FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
        FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
        task_ret_defined t.locals (nClks prog) ∧
        (∃tt. s.waitTime = SOME tt) ⇒
        ?ck t'.
          evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
          (NONE, t') ∧
          code_installed t'.code prog ∧
          state_rel (clksOf prog) s' t' ∧
          t'.ffi.ffi_state = t.ffi.ffi_state ∧
          t'.ffi.oracle = t.ffi.oracle ∧
          FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
          FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
          FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
          task_ret_defined t'.locals (nClks prog) ∧
          (∃wt.
             FLOOKUP t'.locals «wakeUpAt» =
             SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
             FST (t.ffi.ffi_state 0) + wt < dimword (:α))
Proof
  rw [] >>
  cases_on ‘label’ >>
  fs []
  >- (
    rw [] >>
    drule_all step_delay >>
    disch_then (qspec_then ‘ck_extra’ mp_tac) >>
    fs []) >>
  cases_on ‘i’
  >- (
    fs [] >>
    rw [] >>
    drule_all step_input >>
    disch_then (qspec_then ‘ck_extra’ mp_tac) >>
    fs []) >>
  fs [] >>
  rw [] >>
  drule step_output >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  fs []
QED
*)




(*
Definition well_formness_def:
  (well_formness (LDelay _) prog s (t:('a,time_input) panSem$state) = T) ∧
  (well_formness (LAction _) prog s t =
   (well_formed_terms prog s t ∧ task_ret_defined t.locals (nClks prog)))
End
*)



Theorem step_delay_weaker:
  !prog d s s' (t:('a,time_input) panSem$state).
    step prog (LDelay d) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rel (LDelay d) s t ∧
    local_state (LDelay d) t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ∧
    (* extra assumptions *)
    task_ret_defined t.locals (nClks prog) ∧
    well_formed_terms prog s t ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      evaluate (task_controller (nClks prog), t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      next_wakeup (LDelay d) t t' ∧
      event_state t' ∧
      task_ret_defined t'.locals (nClks prog) ∧
      well_formed_terms prog s' t'
Proof
  rw [] >>
  fs [ffi_rel_def] >>
  drule step_delay >>
  disch_then (qspecl_then [‘cycles’, ‘t’, ‘0’] mp_tac) >>
  impl_tac
  >- gs [local_state_def] >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘t'’ >>
  gs [] >>
  ‘t' with clock := t'.clock = t'’ by
    fs [state_component_equality] >>
  gs [next_wakeup_def, event_state_def, local_state_def] >>
  gs [task_ret_defined_def] >>
  fs [step_cases]
  >- (
    gs [well_formed_terms_def, mkState_def] >>
    gen_tac >>
    strip_tac >>
    first_x_assum drule >>
    strip_tac >>
    gs [resetOutput_def] >>
    conj_tac
    >- (
      gs [conds_eval_lt_dimword_def] >>
      gs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule_all >>
      gs []  >>
      TOP_CASE_TAC >> gs [] >>
      strip_tac >>
      cheat) >>
    (* this is complicated *)
    conj_tac
    >- cheat >>
    cheat) >>
  cheat
QED

Theorem step_input_weaker:
  !prog i s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Input i)) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rel (LAction (Input i)) s t ∧
    local_state (LAction (Input i)) t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ∧
    (* extra assumptions *)
    task_ret_defined t.locals (nClks prog) ∧
    well_formed_terms prog s t ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      next_wakeup (LAction (Input i)) t t' ∧
      event_state t' ∧
      task_ret_defined t'.locals (nClks prog) ∧
      well_formed_terms prog s' t'
Proof
  rw [] >>
  fs [ffi_rel_def] >>
  drule step_input >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- gs [action_rel_def, local_state_def, local_action_def] >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘t'’ >>
  gs [] >>
  conj_tac
  >- (
    gs [next_wakeup_def] >>
    qexists_tac ‘wt’ >> gs []) >>
  conj_tac
  >- gs [event_state_def] >>
  gs [well_formed_terms_def]  >>
  gen_tac >>
  strip_tac >>
  (* need more assumptions *)
  cheat
QED


Theorem step_output_weaker:
  !prog os s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Output os)) s s' ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rel (LAction (Output os)) s t ∧
    local_state (LAction (Output os)) t ∧
    code_installed t.code prog ∧
    labProps$good_dimindex (:'a) ∧
    (* should be rephrased *)
    (∃tt. s.waitTime = SOME tt) ∧
    (* extra assumptions *)
    task_ret_defined t.locals (nClks prog) ∧
    well_formed_terms prog s t ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog ∧
      next_wakeup (LAction (Output os)) t t' ∧
      event_state t' ∧
      task_ret_defined t'.locals (nClks prog) ∧
      well_formed_terms prog s' t'
Proof
  rw [] >>
  fs [ffi_rel_def] >>
  drule step_output >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- gs [action_rel_def, local_state_def, local_action_def] >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘t'’ >>
  gs [] >>
  conj_tac
  >- (
    gs [next_wakeup_def] >>
    qexists_tac ‘wt’ >> gs []) >>
  conj_tac
  >- gs [event_state_def] >>
  gs [well_formed_terms_def]  >>
  gen_tac >>
  strip_tac >>
  (* need more assumptions *)
  cheat
QED


(*
Definition next_wakeup_def:
  (next_wakeup (LDelay _) (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) =
   (FLOOKUP t'.locals «waitSet» = SOME (ValWord 0w) ∧
    FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt»)) ∧
  (next_wakeup (LAction _) t t' =
   (t'.ffi.ffi_state = t.ffi.ffi_state ∧
    FLOOKUP t'.locals «waitSet» = SOME (ValWord 0w) ∧
    (∃wt.
       FLOOKUP t'.locals «wakeUpAt» =
       SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) + wt))) ∧
       FST (t.ffi.ffi_state 0) + wt < dimword (:α))))
End


Definition eventual_wakeup_def:
  eventual_wakeup prog <=>
  let tms = FLAT (MAP SND prog) in
    EVERY (λtm.
            ∃h t. termWaitTimes tm = h::t)
          tms
End
*)



(* start from here *)
(*
 While (Const 1w)
             (task_controller clksLength)
*)
(* should we talk about number of states, more like a trace
   sts: list of reachable timeSem state
   ts: list of states,

   what exactly do we need∃ *)
Theorem foo:
  ∀prog s s' labels (t:('a,time_input) panSem$state).
    stepTrace prog s s' labels ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    ffi_rels labels prog s t ∧
    labProps$good_dimindex (:'a) ∧
    (* everything is declared *)
    (* add more updates later *) ⇒
    ?ck t'.
      evaluate (always (nClks prog), t with clock := t.clock + ck) =
      evaluate (always (nClks prog), t') ∧
      state_rel (clksOf prog) s' t' ∧
      code_installed t'.code prog
Proof
QED




















































val _ = export_theory();
