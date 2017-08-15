open preamble
     to_target32ProgTheory compilerTheory
     ml_translatorLib ml_translatorTheory

val _ = new_theory"compiler32Prog";

val _ = translation_extends "to_target32Prog";

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec32 = INST_TYPE[alpha|->``:32``]

val max_heap_limit_32_def = Define`
  max_heap_limit_32 c =
    ^(spec32 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[wordLangTheory.shift_def]
      |> concl |> rhs)`;

val res = translate max_heap_limit_32_def

val max_heap_limit_32_thm = Q.store_thm("max_heap_limit_32_thm",
  `max_heap_limit (:32) = max_heap_limit_32`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val def = spec32
  (backendTheory.attach_bitmaps_def
   |> Q.GENL[`bitmaps`,`bytes`,`c`]
   |> Q.ISPECL[`bitmaps:'a word list`,`bytes:word8 list`,`c:'a lab_to_target$config`])

val res = translate def

val def = spec32 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_32_thm]

val res = translate def

val def = spec32 compilerTheory.compile_def

val _ = translate compilerTheory.locs_to_string_def;
val res = translate def

val res = translate basisProgTheory.basis_def

(*

val res = translate compilerTheory.encode_error_def

val def = spec32 compilerTheory.compile_to_bytes_def

val res = translate def

*)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
