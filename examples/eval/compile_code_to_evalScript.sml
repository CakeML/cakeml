(*
  Defines and compiles (using incremental compiler) the
  code that gets eval'd by the eval example.
*)

open preamble eval_exampleCompileTheory compilationLib
     backendProofTheory

val _ = new_theory "compile_code_to_eval";

(* The eval'd code just sets the string ref to another value
   (and binds a new variable "it" to unit). *)

Definition decs_to_eval_def:
  decs_to_eval =
  [Dlet unknown_loc (Pvar "it")
     (App Opassign [Var (Short "the_string_ref");
                    Lit (StrLit "eval'd code did this\n")])]
End

(* The state to start the incremental compiler with comes
   from the compilation of eval_example. The compiler to
   run is defined in backendProofScript.sml currently.
   TODO: move the compiler out of proofs *)

Definition compilation_def:
  compilation =
  compile_inc_progs_for_eval
    eval_exampleCompile$config.lab_conf.asm_conf
    ((0, 0)
    , config_to_inc_config eval_exampleCompile$config
    , decs_to_eval)
End

(* Now we build a little library for in-logic evaluation of
   the incremental compiler, modeled on compilationLib.
   TODO: Probably should become an actual library? But
   maybe this in-logic compilation won't happen again. *)

val cs = compilation_compset();
val () = computeLib.extend_compset [
  computeLib.Defs
  [compilation_def
  ,decs_to_eval_def
  ,backendTheory.inc_config_to_config_def
  ,backendTheory.config_to_inc_config_def
  ,lab_to_targetTheory.inc_config_to_config_def
  ,lab_to_targetTheory.config_to_inc_config_def
  ],
  computeLib.Tys
  [``:'a backend$inc_config``
  ,``:'a backend$backend_progs``
  ,``:lab_to_target$inc_config``
  ]
  ] cs;
val eval = computeLib.CBV_CONV cs;

Theorem extract_name_thm:
  (extract_name [] = (0, [])) /\
  (extract_name ((Op t (Const (&n)) [])::xs) =
   (n, if xs = [] then [Op t (Const (&n)) []] else xs))
Proof
  rw[clos_to_bvlTheory.extract_name_def]
QED

val () = computeLib.extend_compset [
  computeLib.Defs
  [clos_to_bvlTheory.clos_to_bvl_compile_inc_def
  ,clos_numberTheory.ignore_table_def
  ,clos_to_bvlTheory.compile_inc_def
  ,extract_name_thm
  ,clos_mtiTheory.compile_inc_def
  ,clos_mtiTheory.cond_mti_compile_inc_def
  ,clos_annotateTheory.compile_inc_def
  ,clos_callTheory.compile_inc_def
  ,clos_callTheory.cond_call_compile_inc_def
  ,clos_fvsTheory.compile_inc_def
  ,clos_knownTheory.compile_inc_def
  ,clos_knownTheory.known_compile_inc_def
  ,clos_knownTheory.option_val_approx_spt_def
  ,clos_knownTheory.known_static_conf_def
  ,clos_letopTheory.compile_inc_def
  ,clos_numberTheory.compile_inc_def
  ,clos_ticksTheory.compile_inc_def
  ,bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def
  ,bvl_to_bviTheory.compile_inc_def
  ]
] cs;

Triviality compilation_to_compile_inc_progs =
  compilation_def
  |> CONV_RULE(RAND_CONV(
     (PATH_CONV"rr"eval
      THENC REWR_CONV compile_inc_progs_for_eval_def
      THENC REWR_CONV LET_THM THENC PAIRED_BETA_CONV
      THENC REWR_CONV LET_THM THENC RAND_CONV eval
      THENC BETA_CONV THENC REWR_CONV LET_THM)))

val [config, env_id_p] =
  compilation_to_compile_inc_progs
  |> rconc |> rand |> strip_comb |> #2 |> List.tl
val (env_id, p) = pairSyntax.dest_pair env_id_p

Definition to_flat_inc_def:
  to_flat_inc c env_id p =
    let ps = empty_progs with <| env_id := env_id; source_prog := p |> in
    let (c',p) = source_to_flat$inc_compile env_id c.source_conf p in
    let ps = ps with <| flat_prog := p |> in
    let c = c with source_conf := c' in
    (c, ps)
End

val () = computeLib.extend_compset
  [computeLib.Defs [to_flat_inc_def, config_def]] cs

Triviality to_flat_inc_thm0 = eval ``to_flat_inc
  ^config ^env_id ^p``

val (c, ps) = to_flat_inc_thm0 |> rconc |> dest_pair
Definition flat_conf_inc_def[nocompute]:
  flat_conf_inc = ^c
End
Definition flat_prog_def[nocompute]:
  flat_prog = ^ps
End
val to_flat_inc_thm =
  to_flat_inc_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM flat_conf_inc_def),
              REWR_CONV(SYM flat_prog_def))));
val () = computeLib.extend_compset [computeLib.Defs [flat_prog_def]] cs;

Definition to_clos_inc_def:
  to_clos_inc c env_id p =
    let (c, ps) = to_flat_inc c env_id p in
    let p = flat_to_clos$inc_compile_decs ps.flat_prog in
    let ps = ps with <| clos_prog := p |> in
    (c, ps)
End

Triviality to_clos_inc_thm0 =
  ``to_clos_inc ^config ^env_id ^p``
  |> (REWR_CONV to_clos_inc_def THENC
      RAND_CONV (REWR_CONV to_flat_inc_thm) THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC eval)

val ps = to_clos_inc_thm0 |> rconc |> dest_pair |> #2
Definition clos_prog_def[nocompute]:
  clos_prog = ^ps
End
val to_clos_inc_thm =
  to_clos_inc_thm0 |> CONV_RULE(RAND_CONV(
    RAND_CONV(REWR_CONV(SYM clos_prog_def))))
val () = computeLib.extend_compset [computeLib.Defs [clos_prog_def]] cs;

Definition to_bvl_inc_def:
  to_bvl_inc c env_id p =
    let (c, ps) = to_clos_inc c env_id p in
    let (c',p) = clos_to_bvl_compile_inc c.clos_conf ps.clos_prog in
    let c = c with clos_conf := c' in
    let ps = ps with <| bvl_prog := p |> in
    (c, ps)
End

val flat_conf_inc_clos_conf =
  ``flat_conf_inc.clos_conf``
  |> (RAND_CONV(REWR_CONV flat_conf_inc_def) THENC eval)

val flat_conf_inc_bvl_conf =
  ``flat_conf_inc.bvl_conf``
  |> (RAND_CONV(REWR_CONV flat_conf_inc_def) THENC eval)

Triviality flat_conf_inc_lab_conf_asm_conf:
  flat_conf_inc.lab_conf.asm_conf = x64_config
Proof
  rewrite_tac[flat_conf_inc_def]
  \\ CONV_TAC eval
QED

Triviality to_bvl_inc_thm0 =
  ``to_bvl_inc ^config ^env_id ^p``
  |> (REWR_CONV to_bvl_inc_def THENC
      RAND_CONV (REWR_CONV to_clos_inc_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      PATH_CONV"rlr"(REWR_CONV flat_conf_inc_clos_conf))
  |> CONV_RULE(RAND_CONV eval)

val (c,ps) = to_bvl_inc_thm0 |> rconc |> dest_pair
Definition bvl_conf_inc_def[nocompute]:
  bvl_conf_inc = ^c
End
Definition bvl_prog_def[nocompute]:
  bvl_prog = ^ps
End
val to_bvl_inc_thm =
  to_bvl_inc_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM bvl_conf_inc_def),
              REWR_CONV(SYM bvl_prog_def))));
val () = computeLib.extend_compset [computeLib.Defs
                                     [bvl_prog_def]] cs;

Definition to_bvi_inc_def:
  to_bvi_inc c env_id p =
    let (c, ps) = to_bvl_inc c env_id p in
    let (c', p) = bvl_to_bvi_compile_inc_all c.bvl_conf ps.bvl_prog in
    let c = c with <| bvl_conf := c' |> in
    let ps = ps with <| bvi_prog := p |> in
    (c, ps)
End

val bvl_conf_inc_bvl_conf =
  ``bvl_conf_inc.bvl_conf``
  |> (RAND_CONV(REWR_CONV bvl_conf_inc_def) THENC eval
      THENC REWR_CONV flat_conf_inc_bvl_conf)

Triviality to_bvi_inc_thm0 =
  ``to_bvi_inc ^config ^env_id ^p``
  |> (REWR_CONV to_bvi_inc_def THENC
      RAND_CONV (REWR_CONV to_bvl_inc_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC
      PATH_CONV"rlr"(REWR_CONV bvl_conf_inc_bvl_conf))
  |> CONV_RULE (RAND_CONV eval)

val (c,ps) = to_bvi_inc_thm0 |> rconc |> dest_pair
Definition bvi_conf_inc_def[nocompute]:
  bvi_conf_inc = ^c
End
Definition bvi_prog_def[nocompute]:
  bvi_prog = ^ps
End
val to_bvi_inc_thm =
  to_bvi_inc_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM bvi_conf_inc_def),
              REWR_CONV(SYM bvi_prog_def))));
val () = computeLib.extend_compset
  [computeLib.Defs [bvi_prog_def]] cs;

Triviality bvi_conf_inc_lab_conf_asm_conf:
  bvi_conf_inc.lab_conf.asm_conf = x64_config
Proof
  rewrite_tac[bvi_conf_inc_def,bvl_conf_inc_def]
  \\ CONV_TAC eval
  \\ MATCH_ACCEPT_TAC flat_conf_inc_lab_conf_asm_conf
QED

Definition to_data_inc_def:
  to_data_inc c env_id p =
    let (c, ps) = to_bvi_inc c env_id p in
    let p = bvi_to_data$compile_prog ps.bvi_prog in
    let ps = ps with <| data_prog := p |> in
    (c, ps)
End

val to_data_inc_thm0 =
  ``to_data_inc ^config ^env_id ^p``
  |> (REWR_CONV to_data_inc_def THENC
      RAND_CONV (REWR_CONV to_bvi_inc_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      REWR_CONV_BETA LET_THM THENC
      REWR_CONV LET_THM)
  |> CONV_RULE(RAND_CONV eval)

val (_,ps) = to_data_inc_thm0 |> rconc |> dest_pair
Definition data_prog_def[nocompute]:
  data_prog = ^ps
End
val to_data_inc_thm =
  to_data_inc_thm0 |> CONV_RULE(RAND_CONV(
  (RAND_CONV(REWR_CONV(SYM data_prog_def)))));
val () = computeLib.extend_compset
  [computeLib.Defs [data_prog_def]] cs;

Definition to_word_inc_def:
  to_word_inc c env_id p =
  let (c, ps) = to_data_inc c env_id p in
  let asm_c = c.lab_conf.asm_conf in
  let dc = ensure_fp_conf_ok asm_c c.data_conf in
  let p = MAP (compile_part dc) ps.data_prog in
  let reg_count1 = asm_c.reg_count - (5 + LENGTH asm_c.avoid_regs) in
  let p = MAP (\p. full_compile_single asm_c.two_reg_arith reg_count1
      c.word_to_word_conf.reg_alg asm_c (p, NONE)) p in
  let ps = ps with <| word_prog := p |> in
  (c, ps)
End

val () = computeLib.extend_compset
  [computeLib.Extenders [x64_targetLib.add_x64_encode_compset],
   computeLib.Defs [
     x64_backend_config_def,
     x64_names_def
  ]] cs;

val bvi_conf_inc_data_conf =
``bvi_conf_inc.data_conf``
|> (REWRITE_CONV[bvi_conf_inc_def,bvl_conf_inc_def,flat_conf_inc_def] THENC eval)

val bvi_conf_inc_word_to_word_conf =
``bvi_conf_inc.word_to_word_conf``
|> (REWRITE_CONV[bvi_conf_inc_def,bvl_conf_inc_def,flat_conf_inc_def] THENC eval)

(* TODO: compilationLib avoids this somehow. maybe we should too
val () = computeLib.extend_compset [
  computeLib.Defs [
    ml_monadBaseTheory.st_ex_return_def,
    ml_monadBaseTheory.st_ex_bind_def,
    ml_monadBaseTheory.run_def,
    reg_allocProofTheory.adj_ls_sub_eqn,
    reg_allocProofTheory.update_adj_ls_eqn,
    reg_allocProofTheory.update_node_tag_eqn,
    reg_allocProofTheory.node_tag_sub_eqn,
    reg_allocProofTheory.update_degrees_eqn,
    reg_allocProofTheory.update_coalesced_eqn,
    reg_allocProofTheory.update_move_related_eqn,
    reg_allocProofTheory.degrees_sub_eqn,
    reg_allocProofTheory.coalesced_sub,
    reg_allocProofTheory.move_related_sub,
    reg_allocTheory.full_consistency_ok_def,
    reg_allocTheory.get_dim_def,
    reg_allocTheory.is_Fixed_k_def,
    reg_allocTheory.considered_var_def,
    reg_allocTheory.set_avail_moves_wl_def,
    reg_allocTheory.set_unavail_moves_wl_def,
    reg_allocTheory.set_spill_wl_def,
    reg_allocTheory.set_simp_wl_def,
    reg_allocTheory.set_freeze_wl_def,
    reg_allocTheory.rpt_do_step_compute,
    reg_allocTheory.get_avail_moves_wl_def,
    reg_allocTheory.get_unavail_moves_wl_def,
    reg_allocTheory.get_spill_wl_def,
    reg_allocTheory.get_simp_wl_def,
    reg_allocTheory.get_freeze_wl_def,
    reg_allocTheory.get_stack_def
  ],
  computeLib.Tys [
    ``:('a,'b) ml_monadBase$exc``,
    ``:reg_alloc$algorithm``
  ]
] cs;
*)

val to_word_inc_thm0 =
  ``to_word_inc ^config ^env_id ^p``
  |> (REWR_CONV to_word_inc_def THENC
      RAND_CONV (REWR_CONV to_data_inc_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      REWR_CONV_BETA LET_THM THENC
      REWR_CONV_BETA LET_THM THENC
      REWR_CONV_BETA LET_THM THENC
      REWR_CONV_BETA LET_THM THENC
      REWR_CONV LET_THM THENC
      REWRITE_CONV [
        bvi_conf_inc_lab_conf_asm_conf,
        bvi_conf_inc_data_conf,
        bvi_conf_inc_word_to_word_conf] THENC
      PATH_CONV "rr" eval THENC
      PATH_CONV "rlr" eval THENC
      REWRITE_CONV [MAP] THENC
      RAND_CONV(DEPTH_CONV BETA_CONV))

val compile_single_thms =
  to_word_inc_thm0
  |> rconc |> rand
  |> listSyntax.dest_list |> #1
  |> List.map EVAL (* TODO *)

val to_word_inc_thm1 =
  to_word_inc_thm0
  |> REWRITE_RULE compile_single_thms
  |> CONV_RULE(RAND_CONV(
       BETA_CONV THENC
       REWR_CONV_BETA LET_THM))

val (_,ps) = to_word_inc_thm1 |> rconc |> dest_pair
Definition word_prog_def[nocompute]:
  word_prog = ^ps
End
val () = computeLib.extend_compset
  [computeLib.Defs [word_prog_def]] cs;
val to_word_inc_thm =
  to_word_inc_thm1 |>
  REWRITE_RULE[GSYM word_prog_def]

Definition to_stack_inc_def:
  to_stack_inc c env_id p =
  let (c, ps) = to_word_inc c env_id p in
  let asm_c = c.lab_conf.asm_conf in
  let reg_count1 = asm_c.reg_count - (5 + LENGTH asm_c.avoid_regs) in
  let bm0 = c.word_conf.bitmaps in
  let (p, fs, bm) = compile_word_to_stack reg_count1 ps.word_prog bm0 in
  let cur_bm = DROP (LENGTH bm0) bm in
  let c = c with word_conf := <|bitmaps := bm|> in
  let ps = ps with <| stack_prog := p ; cur_bm := cur_bm |> in (c, ps)
End

val bvi_conf_inc_word_conf_bitmaps =
  ``bvi_conf_inc.word_conf.bitmaps``
  |> (REWRITE_CONV[bvi_conf_inc_def,bvl_conf_inc_def,flat_conf_inc_def]
      THENC eval)

val to_stack_inc_thm =
  ``to_stack_inc ^config ^env_id ^p``
  |> (REWR_CONV to_stack_inc_def THENC
      REWRITE_CONV[to_word_inc_thm] THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV_BETA LET_THM THENC
      REWRITE_CONV[bvi_conf_inc_lab_conf_asm_conf,bvi_conf_inc_word_conf_bitmaps,word_prog_def] THENC
      EVAL)

Definition to_lab_inc_def:
  to_lab_inc c env_id p =
    let (c, ps) = to_stack_inc c env_id p in
    let asm_c = c.lab_conf.asm_conf in
    let reg_count2 = asm_c.reg_count - (3 + LENGTH asm_c.avoid_regs) in
    let p = stack_to_lab$compile_no_stubs
        c.stack_conf.reg_names c.stack_conf.jump asm_c.addr_offset
        reg_count2 ps.stack_prog in
    let ps = ps with <| lab_prog := p |> in
    (c, ps)
End

val bvi_conf_inc_stack_conf =
  ``bvi_conf_inc.stack_conf``
  |> (REWRITE_CONV[bvi_conf_inc_def,bvl_conf_inc_def,flat_conf_inc_def]
      THENC eval)

val to_lab_inc_thm =
  ``to_lab_inc ^config ^env_id ^p``
  |> (REWR_CONV to_lab_inc_def THENC
      REWRITE_CONV[to_stack_inc_thm] THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC RAND_CONV EVAL THENC
      REWRITE_CONV[bvi_conf_inc_lab_conf_asm_conf] THENC
      BETA_CONV THENC REWR_CONV LET_THM THENC
      RAND_CONV eval THENC BETA_CONV THENC
      REWR_CONV LET_THM THENC PATH_CONV "rr" eval THENC
      PATH_CONV "rlllr"
        (eval THENC REWRITE_CONV[bvi_conf_inc_stack_conf] THENC eval) THENC
      PATH_CONV "rllllr"
        (eval THENC REWRITE_CONV[bvi_conf_inc_stack_conf] THENC eval))
  |> CONV_RULE(RAND_CONV EVAL)

Definition to_target_inc_def:
  to_target_inc c env_id p =
  let (c, ps) = to_lab_inc c env_id p in
  let target = lab_to_target$compile c.lab_conf ps.lab_prog in
  let ps = ps with <| target_prog := OPTION_MAP
      (\(bytes, _). (bytes, c.word_conf.bitmaps)) target |> in
  let c = c with lab_conf updated_by (case target of NONE => I
      | SOME (_, c') => K c') in
  (c, ps)
End

val bvi_conf_inc_lab_conf =
  ``bvi_conf_inc.lab_conf``
  |> (REWRITE_CONV[bvi_conf_inc_def,bvl_conf_inc_def,flat_conf_inc_def]
      THENC eval)

val to_target_inc_thm =
  ``to_target_inc ^config ^env_id ^p``
  |> (REWRITE_CONV[to_target_inc_def,
                   to_lab_inc_thm] THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC REWR_CONV LET_THM THENC
      PATH_CONV "rr" eval THENC
      PATH_CONV "rlr" eval THENC
      REWRITE_CONV[bvi_conf_inc_lab_conf] THENC
      eval)

Theorem to_target_inc_eq_compile_inc_progs:
  to_target_inc c env_id p = compile_inc_progs T c (env_id, p)
Proof
  rw[compile_inc_progs_def]
  \\ rw[to_target_inc_def,to_lab_inc_def,to_stack_inc_def,
        to_word_inc_def,to_data_inc_def,to_bvi_inc_def,
        to_bvl_inc_def,to_clos_inc_def,to_flat_inc_def]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[keep_progs_def] \\ rw[]
  \\ rw[GSYM source_evalProofTheory.pairarg_to_pair_map]
  \\ pairarg_tac \\ fs[keep_progs_def]
QED

val (bytes_tm, words_tm) =
  ``^(to_target_inc_thm |> rconc |> dest_pair |> #2).target_prog``
  |> eval |> rconc |> optionSyntax.dest_some
  |> dest_pair

(* Finally, write the generated code out to files *)

fun write_words list_tm fname =
  let
    val out = TextIO.openOut fname
    val word_to_string =
      Int.toString o wordsSyntax.uint_of_word
    fun write_word w =
      (TextIO.output (out, word_to_string w);
       TextIO.output1 (out, #"\n"))
    val () =
      list_tm
      |> listSyntax.dest_list |> #1
      |> List.app write_word
  in
    TextIO.closeOut out
  end

val () = write_words words_tm "eval_words.txt"
val () = write_words bytes_tm "eval_bytes.txt"

val _ = export_theory();
