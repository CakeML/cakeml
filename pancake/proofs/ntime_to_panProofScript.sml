(*
  Correctness proof for --
*)

open preamble
     time_to_panProofTheory


val _ = new_theory "ntime_to_panProof";

val _ = set_grammar_ancestry
        ["time_to_panProof"];


Definition well_formed_code_def:
  well_formed_code prog code <=>
  ∀loc tms.
    ALOOKUP prog loc = SOME tms ⇒
    well_formed_terms prog loc code
End


Definition out_ffi_def:
  out_ffi prog (t:('a,time_input) panSem$state) <=>
  ∀tms loc.
    ALOOKUP prog loc = SOME tms ⇒
    out_signals_ffi t tms
End


Definition action_rel_def:
  (action_rel (Input i) s (t:('a,time_input) panSem$state) ffi ⇔
    input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    ffi = next_ffi t.ffi.ffi_state) ∧
  (action_rel (Output os) s t ffi ⇔
    output_rel t.locals s.waitTime t.ffi.ffi_state ∧
    ffi = t.ffi.ffi_state)
End


Definition ffi_rel_def:
  (ffi_rel (LDelay d) s (t:('a,time_input) panSem$state) ffi =
   ∃cycles.
     delay_rep d t.ffi.ffi_state cycles ∧
     wakeup_rel t.locals s.waitTime t.ffi.ffi_state cycles ∧
     mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
     ffi = nexts_ffi cycles t.ffi.ffi_state) ∧
  (ffi_rel (LAction act) s t ffi =
     action_rel act s t ffi)
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


Definition event_inv_def:
  event_inv fm ⇔
    FLOOKUP fm «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP fm «event» = SOME (ValWord 0w)
End

(*
Definition wakup_time_bound_def:
  wakup_time_bound (:'a) fm ⇔
    ∃wt.
      FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w wt)) ∧
      wt < dimword (:α)
End
*)
Definition assumptions_def:
  assumptions prog labels s (t:('a,time_input) panSem$state) ⇔
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    well_formed_code prog t.code ∧
    (* this is a bit complicated, state t *)
    out_ffi prog t ∧
    ffi_rels prog labels s t ∧
    labProps$good_dimindex (:'a) ∧
    event_inv t.locals ∧
    (* wakup_time_bound (:α) t.locals ∧ *)
    wait_time_locals (:α) t.locals s.waitTime t.ffi.ffi_state ∧
    task_ret_defined t.locals (nClks prog)
End

(* initialise it by an empty list *)
Definition gen_max_times_def:
  (gen_max_times [] n ns = ns) ∧
  (gen_max_times (lbl::lbls) n ns =
   n ::
   let m =
       case lbl of
       | LDelay d => d + n
       | LAction _ => n
   in
   gen_max_times lbls m ns)
End

Definition steps_def:
  (steps prog [] m [] s [] ⇔ T) ∧
  (steps prog (lbl::lbls) m (n::ns) s (st::sts) ⇔
    step prog lbl m n s st ∧ steps prog lbls m ns st sts) ∧
  (steps prog _ m _ s _ ⇔ T)
End

(* ignoring clocks for the time-being *)

(* taken from the conclusion of individual step thorems *)
Definition next_ffi_state_def:
  (next_ffi_state (LDelay d) ffi ffi' ⇔
   ∃cycles.
     delay_rep d ffi cycles ⇒
     ffi' = nexts_ffi cycles ffi) ∧
  (next_ffi_state (LAction _) ffi ffi' ⇔ ffi = ffi)
End


Definition nlocals_def:
  (nlocals (LDelay d) fm ffi wt m ⇔
    ∃cycles.
      delay_rep d ffi cycles ⇒
        FLOOKUP fm «wakeUpAt» = FLOOKUP fm «wakeUpAt» ∧
        FLOOKUP fm «taskRet»  = FLOOKUP fm «taskRet» ∧
        FLOOKUP fm «sysTime»  = SOME (ValWord (n2w (FST (ffi cycles))))) ∧
  (nlocals (LAction _) fm ffi wt m ⇔
    FLOOKUP fm «sysTime» = FLOOKUP fm «sysTime» ∧
    FLOOKUP fm «wakeUpAt» =
    SOME (ValWord (n2w (FST (ffi 0) +
       case wt of
       | NONE => 0
       | SOME wt => wt))) ∧
    (case wt of
     | SOME wt => FST (ffi 0) + wt < m
     | _ => T))
End


Definition always_def:
  always clksLength =
  While (Const 1w)
        (task_controller clksLength)
End


Definition evaluations_def:
  (evaluations prog [] s (t:('a,time_input) panSem$state) ⇔ T) ∧
  (evaluations prog (lbl::lbls) s t ⇔
   ∃ck nt.
     evaluate (always (nClks prog), t with clock := t.clock + ck) =
     evaluate (always (nClks prog), nt) ∧
     ∃m n st.
       step prog lbl m n s st ⇒
       state_rel (clksOf prog) st nt ∧
       event_inv nt.locals ∧
       nt.code = t.code ∧
       next_ffi_state lbl t.ffi.ffi_state nt.ffi.ffi_state  ∧
       nt.ffi.oracle = t.ffi.oracle ∧
       nlocals lbl nt.locals (t.ffi.ffi_state) st.waitTime (dimword (:α)) ∧
       wait_time_locals (:α) nt.locals st.waitTime nt.ffi.ffi_state ∧
       task_ret_defined nt.locals (nClks prog) ∧
       evaluations prog lbls st nt)
End


Theorem ffi_rels_clock_upd:
  ∀lbls prog s t ck.
    ffi_rels prog lbls s t ⇒
    ffi_rels prog lbls s (t with clock := ck)
Proof
  Induct >>
  rw [] >>
  gs [ffi_rels_def, ffi_rel_def] >>
  cases_on ‘h’ >>
  gs [ffi_rels_def, ffi_rel_def]
  >- metis_tac [] >>
  cases_on ‘i’ >>
  gs [action_rel_def] >>
  metis_tac []
QED


Theorem steps_thm:
  ∀labels prog st sts (t:('a,time_input) panSem$state).
    steps prog labels (dimword (:α) - 1)
          (gen_max_times labels (FST (t.ffi.ffi_state 0)) [])
          st sts ∧
    LENGTH sts = LENGTH labels ∧
    assumptions prog labels st t ⇒
      evaluations prog labels st t
Proof
  Induct
  >- (
    rpt gen_tac >>
    strip_tac >>
    fs [evaluations_def]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘sts’ >>
  fs [] >>
  fs [gen_max_times_def] >>
  cases_on ‘h’ >> gs []
  >- ((* delay step *)
    gs [steps_def] >>
    gs [assumptions_def, event_inv_def, ffi_rels_def, ffi_rel_def] >>
    rveq >> gs [] >>
    drule step_delay >>
    gs [] >>
    disch_then (qspecl_then [‘cycles’, ‘t’, ‘0’] mp_tac) >>
    impl_tac
    >- gs [] >>
    strip_tac >>
    gs [evaluations_def, event_inv_def] >>
    qexists_tac ‘ck+1’ >>
    gs [always_def] >>
    once_rewrite_tac [panSemTheory.evaluate_def] >>
    gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
    qexists_tac ‘t'' with clock := t''.clock + 1’ >>
    gs [] >>
    MAP_EVERY qexists_tac [‘dimword (:α) − 1’,‘FST (t.ffi.ffi_state 0)’,‘h'’] >>
    gs [] >>
    conj_asm1_tac
    >- gs [state_rel_def] >>
    conj_asm1_tac
    >- (
      gs [next_ffi_state_def] >>
      qexists_tac ‘cycles’ >>
      gs []) >>
    conj_asm1_tac
    >- (
      gs [nlocals_def] >>
      qexists_tac ‘cycles’ >>
      gs []) >>
    conj_asm1_tac
    >- (
      gs [wait_time_locals_def] >>
      qexists_tac ‘wt’ >>
      qexists_tac ‘st'’ >>
      gs [] >>
      cases_on ‘st.waitTime’
      >- gs [compactDSLSemTheory.step_cases, compactDSLSemTheory.mkState_def] >>
      fs [wakeup_rel_def] >>
      fs [nexts_ffi_def] >>
      ‘(st' + wt) MOD dimword (:α) = st' + wt’ by (
        match_mp_tac LESS_MOD >>
        gs []) >>
      ‘(x + FST (t.ffi.ffi_state 0)) MOD dimword (:α) =
       x + FST (t.ffi.ffi_state 0)’ by (
        match_mp_tac LESS_MOD >>
        gs [compactDSLSemTheory.step_cases]) >>
      TOP_CASE_TAC >> gs []) >>
    conj_asm1_tac
    >- gs [task_ret_defined_def] >>
    last_x_assum match_mp_tac >>
    gs [] >>
    qexists_tac ‘t'’ >>
    gs [] >>
    conj_tac
    >- (
      gs [nexts_ffi_def] >>
      gs [delay_rep_def]) >>
    conj_tac
    (* out_ffi cheat *)
    >- cheat >>
    first_x_assum drule_all >>
    strip_tac >>
    drule ffi_rels_clock_upd >>
    disch_then (qspec_then ‘t''.clock + 1’ assume_tac) >>
    gs []) >>
  cases_on ‘i’ >>
  gs []
  >- (
    (* input step *)
    gs [steps_def] >>
    gs [assumptions_def, event_inv_def, ffi_rels_def, ffi_rel_def] >>
    rveq >> gs [] >>
    drule step_input >>
    gs [] >>
    disch_then (qspec_then ‘t’ mp_tac) >>
    impl_tac
    >- (
      gs [compactDSLSemTheory.step_cases] >>
      gs [well_formed_code_def] >>
      fs [action_rel_def] >>
      (* out_ffi cheat *)
      cheat) >>
    strip_tac >>
    ‘FST (next_ffi t.ffi.ffi_state 0) = FST (t.ffi.ffi_state 0)’ by (
      gs [state_rel_def] >>
      pairarg_tac >> gs [] >>
      gs [input_time_rel_def] >>
      pairarg_tac >> gs [] >>
      gs [input_time_eq_def, has_input_def] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        gs [action_rel_def, input_rel_def, ffiTimeTheory.next_ffi_def]) >>
      gs [ffiTimeTheory.next_ffi_def]) >>
    gs [evaluations_def, event_inv_def] >>
    qexists_tac ‘ck+1’ >>
    gs [always_def] >>
    rewrite_tac [Once panSemTheory.evaluate_def] >>
    gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
    qexists_tac ‘t''’ >>
    fs [] >>
    MAP_EVERY qexists_tac [‘dimword (:α) − 1’,‘FST (t.ffi.ffi_state 0)’,‘h'’] >>
    gs [] >>
    conj_asm1_tac
    >- gs [next_ffi_state_def] >>
    gs [nlocals_def] >>
    conj_asm1_tac
    >- (
      cases_on ‘h'.waitTime’ >>
      gs [wait_time_locals_def]
      >- (
       qexists_tac ‘0’ >>
       qexists_tac ‘FST (t.ffi.ffi_state 0)’ >>
       gs [compactDSLSemTheory.step_cases]) >>
      qexists_tac ‘x’ >>
      qexists_tac ‘FST (t.ffi.ffi_state 0)’ >>
      gs []) >>
    last_x_assum match_mp_tac >>
    gs [] >>
    qexists_tac ‘t'’ >>
    gs [ffiTimeTheory.next_ffi_def] >>
    conj_tac
    (* out_ffi cheat *)
    >- cheat >>
    first_x_assum drule >>
    disch_then (qspec_then ‘t''’ mp_tac) >>
    impl_tac
    >- gs [action_rel_def, ffiTimeTheory.next_ffi_def] >>
    gs []) >>
  (* output step *)
  gs [steps_def] >>
  gs [assumptions_def, event_inv_def, ffi_rels_def, ffi_rel_def] >>
  rveq >> gs [] >>
  drule step_output >>
  gs [] >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- (
    gs [compactDSLSemTheory.step_cases] >>
    gs [well_formed_code_def] >>
    gs [action_rel_def] >>
    (* out_ffi cheat *)
    cheat) >>
  strip_tac >>
  gs [evaluations_def, event_inv_def] >>
  qexists_tac ‘ck+1’ >>
  gs [always_def] >>
  rewrite_tac [Once panSemTheory.evaluate_def] >>
  gs [panSemTheory.eval_def] >>
  gs [panSemTheory.dec_clock_def] >>
  qexists_tac ‘t''’ >>
  fs [] >>
  MAP_EVERY qexists_tac [‘dimword (:α) − 1’,‘FST (t.ffi.ffi_state 0)’,‘h'’] >>
  gs [] >>
  conj_asm1_tac
  >- gs [next_ffi_state_def] >>
  gs [nlocals_def] >>
  conj_asm1_tac
  >- (
  cases_on ‘h'.waitTime’ >>
  gs [wait_time_locals_def]
  >- (
    qexists_tac ‘0’ >>
    qexists_tac ‘FST (t.ffi.ffi_state 0)’ >>
    gs [compactDSLSemTheory.step_cases]) >>
  qexists_tac ‘x’ >>
  qexists_tac ‘FST (t.ffi.ffi_state 0)’ >>
  gs []) >>
  last_x_assum match_mp_tac >>
  gs [] >>
  qexists_tac ‘t'’ >>
  gs [ffiTimeTheory.next_ffi_def] >>
  conj_tac
  (* out_ffi cheat *)
  >- cheat >>
  first_x_assum drule >>
  disch_then (qspec_then ‘t''’ mp_tac) >>
  impl_tac
  >- gs [action_rel_def, ffiTimeTheory.next_ffi_def] >>
  gs []
QED
val _ = export_theory();
