open preamble
     to_target64ProgTheory compilerTheory
     ml_translatorLib ml_translatorTheory

val _ = new_theory"compiler64";

val _ = translation_extends "to_target64Prog";

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val max_heap_limit_64_def = Define`
  max_heap_limit_64 c =
    ^(spec64 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[data_to_wordTheory.shift_def]
      |> concl |> rhs)`;

val res = translate max_heap_limit_64_def

val max_heap_limit_64_thm = Q.store_thm("max_heap_limit_64_thm",
  `max_heap_limit (:64) = max_heap_limit_64`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val def = spec64 compilerTheory.compile_def

val res = translate def

val res = translate basisProgTheory.basis_def

val res = translate compilerTheory.encode_error_def

val def = spec64 compilerTheory.compile_to_bytes_def

val res = translate def

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
