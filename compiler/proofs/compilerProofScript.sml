open preamble
     semanticsTheory
     compilerTheory
     targetSemTheory

val _ = new_theory"compilerProof";

val initial_condition_def = Define`
  initial_condition (st:'ffi top_state) (cc:α compiler$config) = (ARB:bool)`;

val code_loaded_def = Define`
  code_loaded (cc:ξ compiler$config) (cc':ξ compiler$config) (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) = (ARB:bool)`;

val compile_correct = Q.store_thm("compile_correct",
  `∀st cc input.
    initial_condition st cc ⇒
    case compile cc input of
    | Failure _ => semantics st input = NONE
    | Success (bytes,cc') =>
      ∃behaviours.
        (semantics st input = SOME behaviours) ∧
        ∀mc ms.
          code_loaded cc cc' bytes mc ms ⇒
            machine_sem mc st.sem_st.ffi ms ⊆ behaviours`,
  cheat)

val _ = export_theory();
