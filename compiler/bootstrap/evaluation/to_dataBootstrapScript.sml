open preamble
     compilerProgTheory
     ml_translatorLib ml_progLib
     backendTheory
     compilerComputeLib

val _ = new_theory"to_dataBootstrap";

(*
  Eventually, this file will prove
   |- to_data c prog_t1 = ...
   |- to_data c prog_t2 = ...
   |- ...
   where
     c =
       a default initial config (shared by all targets)
     prog_tn =
       a prog declaring the entire compiler for target n

  With incremental compilation, we might get away with only one prog, which is
  the prog for all the non-target-specific parts of the compiler, but Magnus
  suggests incremental compilation like that might be impossible, since some
  phases need to know they have the whole program.

  For now, while the rest of the compiler is still being translated, we settle
  for prog = declarations up to that of to_data itself
  which is not target specific
*)

val _ = translation_extends"compilerProg";

val _ = Globals.max_print_depth := 20;

val rconc = rhs o concl;

(* TODO: there is probably a better way to get this *)
val pgst = let val r = ref init_state val () = ml_prog_update (fn s => (r := s; s)) in !r end;

val ML_code_prog =
  get_thm pgst |> CONV_RULE (PATH_CONV"lllr" EVAL)

val prog = ML_code_prog |> concl |> strip_comb |> #2 |> el 3
(* -- *)

val cs = wordsLib.words_compset();
val () = basicComputeLib.add_basic_compset cs;
val () = compilerComputeLib.add_compiler_compset cs;
val eval = computeLib.CBV_CONV cs;

val init_prog_def = zDefine`
  init_prog = ^prog`;

(* These are evaluated out to avoid the type variable in prim_config *)
val default_source_conf = eval ``prim_config.source_conf`` |> rconc;
val default_mod_conf    = eval ``prim_config.mod_conf`` |> rconc;

val init_conf_def = zDefine`
  init_conf = <|
    source_conf := ^default_source_conf;
    mod_conf    := ^default_mod_conf;
    clos_conf   := clos_to_bvl$default_config;
    bvl_conf    := bvl_to_bvi$default_config
  |>`;

val () = computeLib.extend_compset [computeLib.Defs [init_conf_def, init_prog_def]] cs;

val _ = Lib.say "eval to_mod: ";
val to_mod_thm0 = time eval ``to_mod init_conf init_prog``;
val (c,p) = to_mod_thm0 |> rconc |> dest_pair
val mod_conf_def = zDefine`mod_conf = ^c`;
val mod_prog_def = zDefine`mod_prog = ^p`;
val to_mod_thm = save_thm("to_mod_thm",
  to_mod_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM mod_conf_def),
              REWR_CONV(SYM mod_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [mod_prog_def]] cs;

val mod_conf_mod_conf =
  ``mod_conf.mod_conf``
  |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

val mod_conf_source_conf =
  ``mod_conf.source_conf``
  |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

val mod_conf_clos_conf =
  ``mod_conf.clos_conf``
  |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

val mod_conf_bvl_conf =
  ``mod_conf.bvl_conf``
  |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

val _ = Lib.say "eval to_con: ";
val to_con_thm0 =
  ``to_con init_conf init_prog``
  |> (REWR_CONV to_con_def THENC
      RAND_CONV (REWR_CONV to_mod_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      PATH_CONV"rlr"(REWR_CONV mod_conf_mod_conf))
  |> time (CONV_RULE(RAND_CONV eval))
val (c,p) = to_con_thm0 |> rconc |> dest_pair
val con_conf_def = zDefine`con_conf = ^c`;
val con_prog_def = zDefine`con_prog = ^p`;
val to_con_thm = save_thm("to_con_thm",
  to_con_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM con_conf_def),
              REWR_CONV(SYM con_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [con_prog_def]] cs;

val con_conf_source_conf_next_global =
  ``con_conf.source_conf.next_global`` |>
    (RAND_CONV(RAND_CONV(REWR_CONV con_conf_def)) THENC eval
     THENC RAND_CONV(REWR_CONV mod_conf_source_conf) THENC eval)

val con_conf_mod_conf_exh_ctors_env =
  ``con_conf.mod_conf.exh_ctors_env``
  |> (RAND_CONV(RAND_CONV(REWR_CONV con_conf_def)) THENC eval)

val con_conf_clos_conf =
  ``con_conf.clos_conf``
  |> (RAND_CONV(REWR_CONV con_conf_def) THENC eval
      THENC REWR_CONV mod_conf_clos_conf)

val con_conf_bvl_conf =
  ``con_conf.bvl_conf``
  |> (RAND_CONV(REWR_CONV con_conf_def) THENC eval
      THENC REWR_CONV mod_conf_bvl_conf)

val _ = Lib.say "eval to_dec: ";
val to_dec_thm0 =
  ``to_dec init_conf init_prog``
  |> (REWR_CONV to_dec_def THENC
      RAND_CONV (REWR_CONV to_con_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      PATH_CONV"rlr"(REWR_CONV con_conf_source_conf_next_global))
  |> time (CONV_RULE(RAND_CONV eval))
val (c,p) = to_dec_thm0 |> rconc |> dest_pair
val dec_conf_def = zDefine`dec_conf = ^c`;
val dec_prog_def = zDefine`dec_prog = ^p`;
val to_dec_thm = save_thm("to_dec_thm",
  to_dec_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM dec_conf_def),
              REWR_CONV(SYM dec_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [dec_prog_def]] cs;

val dec_conf_mod_conf_exh_ctors_env =
  ``dec_conf.mod_conf.exh_ctors_env``
  |> (RAND_CONV(RAND_CONV(REWR_CONV dec_conf_def) THENC eval) THENC
      REWR_CONV con_conf_mod_conf_exh_ctors_env)

val dec_conf_clos_conf =
  ``dec_conf.clos_conf``
  |> (RAND_CONV(REWR_CONV dec_conf_def) THENC eval
      THENC REWR_CONV con_conf_clos_conf)

val dec_conf_bvl_conf =
  ``dec_conf.bvl_conf``
  |> (RAND_CONV(REWR_CONV dec_conf_def) THENC eval
      THENC REWR_CONV con_conf_bvl_conf)

val _ = Lib.say "eval to_exh: ";
val to_exh_thm0 =
  ``to_exh init_conf init_prog``
  |> (REWR_CONV to_exh_def THENC
      RAND_CONV (REWR_CONV to_dec_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      PATH_CONV"rlr"(REWR_CONV dec_conf_mod_conf_exh_ctors_env))
  |> time (CONV_RULE(RAND_CONV eval))
val (_,p) = to_exh_thm0 |> rconc |> dest_pair
val exh_prog_def = zDefine`exh_prog = ^p`;
val to_exh_thm = save_thm("to_exh_thm",
  to_exh_thm0 |> CONV_RULE(RAND_CONV(
    RAND_CONV(REWR_CONV(SYM exh_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [exh_prog_def]] cs;

val _ = Lib.say "eval to_pat: ";
val to_pat_thm0 =
  ``to_pat init_conf init_prog``
  |> (REWR_CONV to_pat_def THENC
      RAND_CONV (REWR_CONV to_exh_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV)
  |> time (CONV_RULE(RAND_CONV(RAND_CONV eval)))
  |> CONV_RULE(RAND_CONV(REWR_CONV LET_THM THENC BETA_CONV))
val (_,p) = to_pat_thm0 |> rconc |> dest_pair
val pat_prog_def = zDefine`pat_prog = ^p`;
val to_pat_thm = save_thm("to_pat_thm",
  to_pat_thm0 |> CONV_RULE(RAND_CONV(
    RAND_CONV(REWR_CONV(SYM pat_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [pat_prog_def]] cs;

val _ = Lib.say "eval to_clos: ";
val to_clos_thm0 =
  ``to_clos init_conf init_prog``
  |> (REWR_CONV to_clos_def THENC
      RAND_CONV (REWR_CONV to_pat_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV)
  |> time (CONV_RULE(RAND_CONV(RAND_CONV eval)))
  |> CONV_RULE(RAND_CONV(REWR_CONV LET_THM THENC BETA_CONV))
val (_,p) = to_clos_thm0 |> rconc |> dest_pair
val clos_prog_def = zDefine`clos_prog = ^p`;
val to_clos_thm = save_thm("to_clos_thm",
  to_clos_thm0 |> CONV_RULE(RAND_CONV(
    RAND_CONV(REWR_CONV(SYM clos_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [clos_prog_def]] cs;

val _ = Lib.say "eval to_bvl: ";
val to_bvl_thm0 =
  ``to_bvl init_conf init_prog``
  |> (REWR_CONV to_bvl_def THENC
      RAND_CONV (REWR_CONV to_clos_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      PATH_CONV"rlr"(REWR_CONV dec_conf_clos_conf))
  |> time (CONV_RULE(RAND_CONV eval))
val (c,p) = to_bvl_thm0 |> rconc |> dest_pair
val bvl_conf_def = zDefine`bvl_conf = ^c`;
val bvl_prog_def = zDefine`bvl_prog = ^p`;
val to_bvl_thm = save_thm("to_bvl_thm",
  to_bvl_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM bvl_conf_def),
              REWR_CONV(SYM bvl_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [bvl_prog_def]] cs;

val bvl_conf_clos_conf_next_loc =
  ``bvl_conf.clos_conf.next_loc``
  |> (RAND_CONV(RAND_CONV(REWR_CONV bvl_conf_def)) THENC eval)

val bvl_conf_clos_conf_start =
  ``bvl_conf.clos_conf.start``
  |> (RAND_CONV(RAND_CONV(REWR_CONV bvl_conf_def)) THENC eval)

val bvl_conf_bvl_conf =
  ``bvl_conf.bvl_conf``
  |> (RAND_CONV(REWR_CONV bvl_conf_def) THENC eval
      THENC REWR_CONV dec_conf_bvl_conf)

val _ = Lib.say "eval to_bvi: ";
val to_bvi_thm0 =
  ``to_bvi init_conf init_prog``
  |> (REWR_CONV to_bvi_def THENC
      RAND_CONV (REWR_CONV to_bvl_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      PATH_CONV"rllr"(REWR_CONV bvl_conf_clos_conf_next_loc) THENC
      PATH_CONV"rlllr"(REWR_CONV bvl_conf_clos_conf_start) THENC
      PATH_CONV"rlr"(REWR_CONV bvl_conf_bvl_conf))
  |> time (CONV_RULE(RAND_CONV eval))
val (c,p) = to_bvi_thm0 |> rconc |> dest_pair
val bvi_conf_def = zDefine`bvi_conf = ^c`;
val bvi_prog_def = zDefine`bvi_prog = ^p`;
val to_bvi_thm = save_thm("to_bvi_thm",
  to_bvi_thm0 |> CONV_RULE(RAND_CONV(
    FORK_CONV(REWR_CONV(SYM bvi_conf_def),
              REWR_CONV(SYM bvi_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [bvi_prog_def]] cs;

val _ = Lib.say "eval to_data: ";
val to_data_thm0 =
  ``to_data init_conf init_prog``
  |> (REWR_CONV to_data_def THENC
      RAND_CONV (REWR_CONV to_bvi_thm) THENC
      REWR_CONV LET_THM THENC
      PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC BETA_CONV)
  |> time (CONV_RULE(RAND_CONV(RAND_CONV eval)))
val (_,p) = to_data_thm0 |> rconc |> dest_pair
val data_prog_def = zDefine`data_prog = ^p`;
val to_data_thm = save_thm("to_data_thm",
  to_data_thm0 |> CONV_RULE(RAND_CONV(
    RAND_CONV(REWR_CONV(SYM data_prog_def)))));
val () = computeLib.extend_compset [computeLib.Defs [data_prog_def]] cs;

val _ = reset_translation();

val _ = export_theory();
