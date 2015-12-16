open preamble
     semanticsTheory
     compilerTheory
     targetSemTheory

val _ = new_theory"compilerProof";

val initial_condition_def = Define`
  initial_condition (st:'ffi top_state) (cc:α compiler$config) (prelude:top list) = (ARB:bool)`;

val compile_correct = Q.store_thm("compile_correct",
  `∀st cc prelude input.
    initial_condition st cc prelude ⇒
    case compiler$compile cc prelude input of
    | Failure ParseError => semantics st prelude input = CannotParse
    | Failure TypeError => semantics st prelude input = IllTyped
    | Failure CompileError => T (* see theorem about to_lab to avoid CompileError *)
    | Success (bytes,cc') =>
      ∃behaviours.
        (semantics st prelude input = Execute behaviours) ∧
        ∀mc ms.
          code_loaded bytes mc ms ⇒
            machine_sem mc st.sem_st.ffi ms ⊆
              extend_with_resource_limit behaviours
              (* see theorem about to_bvp to avoid extend_with_resource_limit *)`,
  cheat)

val _ = export_theory();
