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

(*
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

Definition locals_def:
  (locals [] t = T) ∧
  (locals (lbl::lbls) t = local_state lbl t)
End
*)

Definition event_inv_def:
  event_inv fm ⇔
    FLOOKUP fm «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP fm «event» = SOME (ValWord 0w)
End

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
       next_ffi_state lbl t.ffi.ffi_state nt.ffi.ffi_state ∧
       nt.ffi.oracle = t.ffi.oracle ∧
       nlocals lbl nt.locals (t.ffi.ffi_state) st.waitTime (dimword (:α)) ∧
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
    (* delay input *)
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
      cheat) >>
    strip_tac >>
    gs [evaluations_def, event_inv_def] >>
    qexists_tac ‘ck+1’ >>
    gs [always_def] >>
    rewrite_tac [Once panSemTheory.evaluate_def] >>
    gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
    qexists_tac ‘t''’ >>
    fs []
    MAP_EVERY qexists_tac [‘dimword (:α) − 1’,‘FST (t.ffi.ffi_state 0)’,‘h'’] >>
    gs [] >>
    conj_asm1_tac
    >- gs [state_rel_def] >>
    conj_asm1_tac
    >- cheat >>
    conj_asm1_tac
    >- gs [next_ffi_state_def] >>
    gs [nlocals_def] >>
    last_x_assum match_mp_tac >>
    gs [] >>
    qexists_tac ‘t'’ >>
    gs [next_ffi_def] >>
    ‘FST (next_ffi t.ffi.ffi_state 0) = FST (t.ffi.ffi_state 0)’ by
      cheat >>
    gs [] >>
    conj_tac
    (* out_ffi cheat *)
    >- cheat >>
    first_x_assum drule >>
    gs [action_rel_def]) >>
  cheat
QED


(*
Definition evaluations_def:
  (evaluations prog [] t ⇔ T) ∧
  (evaluations prog (lbl::lbls) t ⇔
   ∃ck nt.
     evaluate (always (nClks prog), t with clock := t.clock + ck) =
     evaluate (always (nClks prog), nt) ∧
     evaluations prog lbls nt)
End


Definition evaluation_invs_def:
  (evaluation_inv prog [] s (t:('a,time_input) panSem$state) ⇔ T) ∧
  (evaluation_inv prog (lbl::lbls) s t ⇔
   ∃m n st nt.
     step prog lbl m n s st ∧
     evaluate (always (nClks prog), t) =
     evaluate (always (nClks prog), nt) ⇒
     state_rel (clksOf prog) st nt ∧
     nt.code = t.code ∧
     next_ffi_state lbl t.ffi.ffi_state nt.ffi.ffi_state ∧
     nt.ffi.oracle = t.ffi.oracle ∧
     nlocals lbl nt.locals (t.ffi.ffi_state) st.waitTime (dimword (:α)) ∧
     task_ret_defined nt.locals (nClks prog) ∧
     evaluation_inv prog lbls st nt)
End
*)


(*
Definition evaluate_rel_def:
  (evaluate_rel prog lbl t nt ⇔
   case lbl of
   | LDelay d =>
       evaluate (task_controller (nClks prog), t) =
       evaluate (task_controller (nClks prog), nt)
   | LAction _ =>
       evaluate (task_controller (nClks prog), t) =
       (NONE, nt))
End


Definition evaluations_def:
  (evaluations prog [] t ⇔ T) ∧
  (evaluations prog (lbl::lbls) t ⇔
   ∃nt.
     evaluate_rel prog lbl t nt ∧
     evaluations prog lbls nt) ∧
  (evaluations prog _ t ⇔ T)
End
*)

(*
(*
Definition event_state_def:
  event_state t ⇔
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event»   =  SOME (ValWord 0w)
End

Definition evaluations_def:
  (evaluations prog t [] [] ⇔ T) ∧
  (evaluations prog t (lbl::lbls) (nt::nts) ⇔
     evaluate_rel prog lbl t nt ∧
     evaluations prog nt lbls nts) ∧
  (evaluations prog t _ _ ⇔ T)
End

Definition state_rels_def:
  (state_rels prog [] s t ⇔ T) ∧
  (state_rels prog (lbl::lbls) s t ⇔
   ∀m n st nt.
     step prog lbl m n s st ∧
     evaluate_rel prog lbl t nt ⇒
     state_rel (clksOf prog) st nt ∧
     state_rels prog lbls st nt)
End

Definition always_code_installed_def:
  (always_code_installed prog [] t ⇔ T) ∧
  (always_code_installed prog (lbl::lbls) t ⇔
   ∀nt.
     evaluate_rel prog lbl t nt ⇒
     code_installed nt.code prog ∧
     always_code_installed prog lbls nt)
End
*)


Theorem foo:
  ∀prog s s' labels (t:('a,time_input) panSem$state).
    stepTrace prog
              (dimword (:α) - 1)
              (FST (t.ffi.ffi_state 0)) s s' labels ∧
    state_rel (clksOf prog) s t ∧
    code_installed t.code prog ∧
    well_formed_code prog t.code ∧
    out_ffi prog t ∧
    ffi_rels prog labels s t ∧
    labProps$good_dimindex (:'a) ∧
    local_state (HD labels) t ∧
    (* we shoud be able to prove that this stays as an invariant
       after each invocation of the task *)
    (* should we assume that labels are non-empty *)
    task_ret_defined t.locals (nClks prog) ⇒
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

*)

val _ = export_theory();
