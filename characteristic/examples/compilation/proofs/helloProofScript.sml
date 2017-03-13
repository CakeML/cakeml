open preamble
     semanticsPropsTheory backendProofTheory configProofTheory
     helloProgTheory helloCompileTheory

val _ = new_theory"helloProof";

val _ = Globals.max_print_depth := 20;

(* TODO: move, export for reuse *)
val conf_ok_with_word_to_word_conf = Q.store_thm("conf_ok_with_word_to_word_conf",
  `conf_ok (cc with word_to_word_conf := wc) mc ⇔ conf_ok cc mc`, rw[conf_ok_def]);

val installed_with_word_to_word_conf = Q.store_thm("installed_with_word_to_word_conf",
  `installed (bytes,cc with word_to_word_conf := wc,rest) ⇔ installed(bytes,cc,rest)`,
  PairCases_on`rest` \\ rw[installed_def]);

val semantics_prog_Terminate_not_Fail = Q.store_thm("semantics_prog_Terminate_not_Fail",
  `semantics_prog s e p (Terminate x y) ⇒
    ¬semantics_prog s e p Fail ∧
    semantics_prog s e p = {Terminate x y}`,
  rpt strip_tac
  \\ simp[FUN_EQ_THM]
  \\ imp_res_tac semantics_prog_deterministic \\ fs[]
  \\ metis_tac[semantics_prog_deterministic]);

val compile_correct_matchable =
  compile_correct
  |> CONV_RULE(
       RAND_CONV(REWR_CONV ml_progTheory.init_state_env_thm)
       THENC REWR_CONV LET_THM
       THENC PAIRED_BETA_CONV THENC
       LAND_CONV(move_conj_left(equal"compile" o #1 o dest_const o #1 o strip_comb o lhs)))
  |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
(* -- *)

(* TODO: generate compilation theorems like this *)
val oracle_tm =
  hello |> concl |> lhs |> find_term listSyntax.is_list
val hello_oracle_def = Define`hello_oracle = ^oracle_tm`;

val bytes_tm =
  hello |> concl |> rhs |> find_term listSyntax.is_list
val hello_bytes_def = Define`hello_bytes = ^bytes_tm`;

val ffis_tm =
  hello |> concl |> rhs
  |> find_term (can (assert (equal stringSyntax.string_ty) o listSyntax.dest_list_type o type_of))
val hello_ffis_def = Define`hello_ffis = ^ffis_tm`;

val hello_compiled =
  hello |> ONCE_REWRITE_RULE[GSYM hello_prog_def,GSYM hello_oracle_def,GSYM hello_bytes_def,GSYM hello_ffis_def]
(* -- *)

val io_events_def = new_specification("io_events_def",["io_events"],
  hello_semantics |> Q.GENL(List.rev[`inp`,`cls`,`files`]) |> SIMP_RULE bool_ss [SKOLEM_THM]);

val hello_sem1 = io_events_def |> SPEC_ALL |> CONJUNCT1
val hello_sem2 = MATCH_MP semantics_prog_Terminate_not_Fail hello_sem1

val compile_correct_applied =
  MATCH_MP compile_correct_matchable hello_compiled
  |> SIMP_RULE(srw_ss())[LET_THM]
  |> CONV_RULE(PATH_CONV"lrlr"(EVAL)) |> SIMP_RULE bool_ss []
  |> CONV_RULE(PATH_CONV"lrlr"(EVAL)) |> SIMP_RULE bool_ss []
  |> CONV_RULE(PATH_CONV"lrlr"(EVAL))
  |> SIMP_RULE bool_ss [conf_ok_with_word_to_word_conf,installed_with_word_to_word_conf]
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP (CONJUNCT1 hello_sem2)
  |> REWRITE_RULE[CONJUNCT2 hello_sem2]

val hello_compiled_thm =
  CONJ compile_correct_applied (CONJUNCT2 (SPEC_ALL io_events_def))
  |> curry save_thm "hello_compiled_thm";

val _ = export_theory();
