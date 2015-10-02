open preamble
     semanticsTheory
     compilerTheory
     targetSemTheory

val _ = new_theory"compilerProof";

val initial_condition_def = Define`
  initial_condition (st:'ffi top_state) (cc:α compiler$config) = (ARB:bool)`;

val code_loaded_def = Define`
  code_loaded (cc:ξ compiler$config) (cc':ξ compiler$config) (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) = (ARB:bool)`;

val extend_with_resource_limit_def = Define`
  extend_with_resource_limit behaviours =
  behaviours ∪
  { Terminate Resource_limit_hit (TAKE n io_list)
    | n,io_list | ∃t. Terminate t io_list ∈ behaviours } ∪
  { Terminate Resource_limit_hit io_list
    | io_list | ∃io_trace n.
                  Diverge io_trace ∈ behaviours ∧
                  LTAKE n io_trace = SOME io_list }`;

val compile_correct = Q.store_thm("compile_correct",
  `∀st cc input.
    initial_condition st cc ⇒
    case compile cc input of
    | Failure ParseError => semantics st input = CannotParse
    | Failure TypeError => semantics st input = IllTyped
    | Failure CompileError => T (* see theorem about compile_to_lab *)
    | Success (bytes,cc') =>
      ∃behaviours.
        (semantics st input = Execute behaviours) ∧
        ∀mc ms.
          code_loaded cc cc' bytes mc ms ⇒
            machine_sem mc st.sem_st.ffi ms ⊆
              extend_with_resource_limit behaviours
              (* see theorem about compile_to_bvp to avoid extend_with_resource_limit *)`,
  cheat)

val _ = export_theory();
