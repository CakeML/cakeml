(*
  General definitions and theorems that are useful within the proofs
  about the Dafny semantics.
*)

Theory dafnyProps
Ancestors
  dafny_semanticPrimitives
Libs
  preamble

(* simps *)
Theorem with_same_locals[simp]:
  s with locals := s.locals = s
Proof
  gvs [state_component_equality]
QED

Theorem with_same_clock[simp]:
  s with clock := s.clock = s
Proof
  gvs [state_component_equality]
QED

Theorem declare_local_clock[simp]:
  (declare_local s n).clock = s.clock
Proof
  gvs [declare_local_def]
QED

Theorem restore_caller_clock[simp]:
  (restore_caller cur prev).clock = cur.clock
Proof
  gvs [restore_caller_def]
QED

(* misc *)

(* Used often when trying to prove statements about Forall *)
Theorem snd_tuple:
  SND x = z ⇔ ∃y. x = (y, z)
Proof
  Cases_on ‘x’ \\ gvs []
QED

(* size *)
Theorem list_exp_size_snd:
  list_size (λx. exp_size (SND x)) vars =
  list_size (λx. exp_size x) (MAP SND vars)
Proof
  Induct_on ‘vars’ \\ gvs []
QED

(* Pushing and popping locals *)

Theorem push_locals_cons:
  push_locals s ((n,v)::(ZIP (ns,vs))) =
  (push_locals (push_local s n v) (ZIP (ns,vs)))
Proof
  gvs [push_locals_def, push_local_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem push_locals_len:
  ∀binds s s'.
    LENGTH (push_locals s binds).locals = LENGTH s.locals + LENGTH binds
Proof
  Induct \\ gvs [push_locals_def]
QED

Theorem drop_push_locals:
  ∀n ys s. LENGTH ys = n ⇒ DROP n (push_locals s ys).locals = s.locals
Proof
  Induct \\ rpt strip_tac
  \\ gvs [push_locals_def, DROP_APPEND]
QED

Theorem pop_local_some:
  s.locals ≠ [] ⇒ ∃s'. pop_locals 1 s = SOME s'
Proof
  rpt strip_tac \\ Cases_on ‘s.locals’ \\ gvs [safe_drop_def, pop_locals_def]
QED

(* clock *)

Theorem set_up_call_clock_eq:
  set_up_call st in_ns in_vs outs = SOME st₁ ⇒ st₁.clock = st.clock
Proof
  gvs [set_up_call_def, safe_zip_def, state_component_equality, AllCaseEqs()]
QED

Theorem set_up_call_some_with_clock:
  set_up_call st in_ns in_vs outs = SOME st₁ ⇒
  set_up_call (st with clock := ck) in_ns in_vs outs =
  SOME (st₁ with clock := ck)
Proof
  gvs [set_up_call_def, safe_zip_def, AllCaseEqs()]
QED

Theorem set_up_call_none_with_clock:
  set_up_call st in_ns in_vs outs = NONE ⇒
  set_up_call (st with clock := ck) in_ns in_vs outs = NONE
Proof
  gvs [set_up_call_def, AllCaseEqs()]
QED

Theorem declare_local_with_clock:
  declare_local (s with clock := ck) n = (declare_local s n) with clock := ck
Proof
  gvs [declare_local_def]
QED

Theorem pop_locals_some_clock:
  pop_locals n s = SOME s' ⇒
  pop_locals n (s with clock := ck) = SOME (s' with clock := ck)
Proof
  gvs [pop_locals_def, state_component_equality, AllCaseEqs()]
QED

Theorem pop_locals_clock_eq:
  pop_locals n s = SOME s' ⇒ s'.clock = s.clock
Proof
  gvs [pop_locals_def, state_component_equality, AllCaseEqs()]
QED

Theorem update_local_some_with_clock:
  update_local s var val = SOME s' ⇒
  update_local (s with clock := ck) var val = SOME (s' with clock := ck)
Proof
  rpt strip_tac \\ gvs [update_local_def, AllCaseEqs()]
QED

Theorem update_local_some_clock_eq:
  update_local s var val = SOME s' ⇒ s'.clock = s.clock
Proof
  rpt strip_tac \\ gvs [update_local_def, AllCaseEqs()]
QED

Theorem update_local_none_with_clock:
  update_local s var val = NONE ⇒
  update_local (s with clock := ck) var val = NONE
Proof
  rpt strip_tac \\ gvs [update_local_def, AllCaseEqs()]
QED

Theorem alloc_array_none_with_clock:
  alloc_array s len init = NONE ⇒
  alloc_array (s with clock := ck) len init = NONE
Proof
  rpt strip_tac \\ gvs [alloc_array_def, AllCaseEqs()]
QED

Theorem alloc_array_some_with_clock:
  alloc_array s len init = SOME (s', arr) ⇒
  alloc_array (s with clock := ck) len init = SOME (s' with clock := ck, arr)
Proof
  rpt strip_tac \\ gvs [alloc_array_def, AllCaseEqs()]
QED

Theorem alloc_array_some_clock_eq:
  alloc_array s len init = SOME (s', arr) ⇒ s'.clock = s.clock
Proof
  rpt strip_tac \\ gvs [alloc_array_def, AllCaseEqs()]
QED

Theorem update_array_none_with_clock:
  update_array s arr idx val = NONE ⇒
  update_array (s with clock := ck) arr idx val = NONE
Proof
  rpt strip_tac \\ gvs [update_array_def, AllCaseEqs()]
QED

Theorem update_array_some_with_clock:
  update_array s arr idx val = SOME s' ⇒
  update_array (s with clock := ck) arr idx val = SOME (s' with clock := ck)
Proof
  rpt strip_tac \\ gvs [update_array_def, AllCaseEqs()]
QED

Theorem update_array_some_clock_eq:
  update_array s arr idx val = SOME s' ⇒ s'.clock = s.clock
Proof
  rpt strip_tac \\ gvs [update_array_def, AllCaseEqs()]
QED

Theorem restore_caller_cur_with_clock:
  restore_caller (cur with clock := ck) prev =
  (restore_caller cur prev) with clock := ck
Proof
  gvs [restore_caller_def]
QED

Theorem restore_caller_prev_with_clock:
  restore_caller cur (prev with clock := ck) = restore_caller cur prev
Proof
  gvs [restore_caller_def]
QED
