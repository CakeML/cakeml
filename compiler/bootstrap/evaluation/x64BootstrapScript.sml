open preamble
     backendTheory
     to_dataBootstrapTheory
     x64_configTheory
     x64_targetTheory
     asmLib

val _ = new_theory "x64Bootstrap";

val _ = Globals.max_print_depth := 10;

val rconc = rhs o concl;

val to_data_thm0 =
  MATCH_MP backendTheory.to_data_change_config to_data_thm
  |> Q.GEN`c2` |> Q.ISPEC`x64_compiler_config`

val same_config = prove(to_data_thm0 |> concl |> rator |> rand,
  REWRITE_TAC[init_conf_def,x64_compiler_config_def]
  \\ EVAL_TAC
  \\ rw[FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_UPDATE,FLOOKUP_FUNION]
  \\ EVAL_TAC
  \\ rpt (IF_CASES_TAC \\ rveq \\ EVAL_TAC))

val to_data_thm1 =
  MATCH_MP to_data_thm0 same_config

val cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset [
    computeLib.Extenders [
      basicComputeLib.add_basic_compset,
      compilerComputeLib.add_compiler_compset,
      asmLib.add_asm_compset ],
    computeLib.Defs [
      x64_compiler_config_def,
      x64_config_def,
      data_prog_def]
  ] cs
val eval = computeLib.CBV_CONV cs;

val to_livesets_thm0 =
  ``to_livesets x64_compiler_config init_prog``
  |> (REWR_CONV to_livesets_def THENC
      RAND_CONV (REWR_CONV to_data_thm1) THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC BETA_CONV THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC
      PATH_CONV "rlrraraalralrarllr" eval THENC
      PATH_CONV"rlrraraalralralralralrar"
        (RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
         REWR_CONV(CONJUNCT1 bool_case_thm)))

(*
val tm1 =
  to_livesets_thm0 |> rconc
  |> rand |> rator |> rand
  |> rand |> dest_abs |> #2
  |> rand |> dest_abs |> #2
  |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  (*
  |> rand |> rator |> rator |> rand
  *)
  |> rator |> rand |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  |> rand
  |> rator |> rator |> rand
*)

(* about 5 minutes *)

Lib.say "eval data_to_word: ";
val tm0 = to_livesets_thm0 |> rconc |> rand |> rand
val thm0 = time eval tm0;

(*
val word_prog0_def = Define`
  word_prog0 = ^(thm0 |> rconc)`;

val thm1 = thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM word_prog0_def)))
*)

(* could do it all at once?

Lib.say "eval to_livesets1: "

val to_livesets_thm1 =
  to_livesets_thm0
  |> CONV_RULE (RAND_CONV (
       RAND_CONV(RAND_CONV(REWR_CONV thm0) THENC
                 time eval)))
*)

val tm1 = to_livesets_thm0 |> rconc |> rand

val (args,body) = tm1 |> rator |> rand |> dest_pabs
val word_to_word_fn_def = Define`word_to_word_fn ^args = ^body`;
val word_to_word_fn_eq =
  word_to_word_fn_def
  |> SPEC_ALL
  |> PairRules.PABS args
  |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)
val word_to_word_fn = word_to_word_fn_eq|>concl|>lhs

val word_prog = thm0 |> rconc |> listSyntax.dest_list |> #1

val num_progs = length word_prog

open Thread

fun chunks_of n ls =
  let
    val (ch,rst) = split_after n ls
  in
    if null rst then [ch]
    else ch::(chunks_of n rst)
  end handle HOL_ERR _ => [ls]

val chunk_size = 400

val chs = chunks_of chunk_size word_prog

fun do_word_to_word n [] acc = acc
  | do_word_to_word n (p::ps) acc =
    let
      val tm = mk_comb(word_to_word_fn,p)
      val () = Lib.say("eval word_to_word ("^Int.toString(n)^" remain): ")
      val th = tm
        |> (RATOR_CONV(REWR_CONV word_to_word_fn_eq) THENC
            time eval)
    in do_word_to_word (n-1) ps (th::acc) end

val mutex = Mutex.mutex();

val cvar = ConditionVar.conditionVar();

val num_chunks = length chs

val threads_left = ref num_chunks

fun do_chunk ch n r () =
  let
    val () = r := do_word_to_word n ch []
    val () = Mutex.lock mutex
    val () = threads_left := !threads_left-1
    val () = Mutex.unlock mutex
    val () = ConditionVar.signal cvar
  in () end

fun foldthis (ch,(n,refs)) =
  let
    val r = ref []
    val _ = Thread.fork (do_chunk ch n r, [])
  in (n-chunk_size,r::refs) end

val true = Mutex.trylock mutex

val (_,refs) = List.foldl foldthis (num_progs,[]) chs

fun wait () =
  if !threads_left = 0 then Mutex.unlock mutex
  else (ConditionVar.wait(cvar,mutex); wait())

val () = wait ()

val ths = List.concat (List.map (op!) refs)

val next_thm = ref ths
fun el_conv _ =
  case !next_thm of th :: rest =>
    let val () = next_thm := rest in th end

val thm1 =
  tm1
  |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM word_to_word_fn_eq))) THENC
      RAND_CONV(REWR_CONV thm0) THENC
      listLib.MAP_CONV el_conv)

val word_prog0_def = zDefine`
  word_prog0 = ^(thm1 |> rconc)`;

val thm1' = thm1 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM word_prog0_def)))

val to_livesets_thm1 =
  to_livesets_thm0
  |> CONV_RULE (RAND_CONV (
       RAND_CONV(REWR_CONV thm1') THENC
       BETA_CONV THENC
       REWR_CONV LET_THM))

(* evaluate this MAP similarly to above *)

val _ = export_theory();
