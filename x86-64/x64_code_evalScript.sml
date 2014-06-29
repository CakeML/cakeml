open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_code_eval";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;
open prog_x64_extraTheory prog_x64Theory temporalTheory;

open x64_heapTheory lcsymtacs;

val x64_code_rev_def = Define `
  (x64_code_rev i [] res = res) /\
  (x64_code_rev i (b::bs) res =
     let c = x64 i b in x64_code_rev (i + LENGTH c) bs (REVERSE c ++ res))`;

val x64_code_rev_eval =
  ([],``!b. x64_code_rev i (b::bs) res =
          let c = x64 i b in
            x64_code_rev (i + LENGTH c) bs (REVERSE c ++ res)``)
  |> (Cases \\ TRY (Cases_on `b'`) \\ TRY (Cases_on `l`)) |> fst
  |> map (SIMP_RULE std_ss [LET_DEF] o REWRITE_CONV [x64_code_rev_def] o snd)
  |> (fn thms => LIST_CONJ (CONJUNCT1 x64_code_rev_def::thms))
  |> SIMP_RULE std_ss [x64_def,LET_DEF,APPEND,LENGTH,small_offset_def,REVERSE_DEF,
       small_offset6_def,small_offset12_def,small_offset16_def,IMM32_def,LENGTH_IF]
  |> REWRITE_RULE [APPEND_IF,APPEND,IF_AND]
  |> SIMP_RULE std_ss []
  |> REWRITE_RULE [GSYM IF_AND]

val _ = save_thm("x64_code_rev_eval",x64_code_rev_eval);

val x64_code_rev_thm = prove(
  ``!bs i res. x64_code_rev i bs res = REVERSE (x64_code i bs) ++ res``,
  Induct THEN1 (SRW_TAC [] [x64_code_def,x64_code_rev_def])
  \\ SRW_TAC [] [x64_code_ALT,x64_code_rev_def] \\ SRW_TAC [] []);

val x64_code_rev_thm = store_thm("x64_code_rev_thm",
  ``!bs i. x64_code i bs = REVERSE (x64_code_rev i bs [])``,
  SRW_TAC [] [x64_code_rev_thm]);

val x64_code_INTRO = prove(
  ``(x64_code_rev n xs [] = ys) = (x64_code n xs = REVERSE ys)``,
  SRW_TAC [] [x64_code_rev_thm]);

val _ = computeLib.add_persistent_funs
          ["x64_code_rev_eval",
           "x64_code_rev_thm"];

(*

  EVAL ``x64_code 0 [Stack Pop]``

val proper_code_labels_rev_bootstrap_lcode =
  MP (DISCH_ALL compileCallReplStepDecTheory.code_labels_rev_bootstrap_lcode)
     code_labels_ok_bootstrap_lcode |> RW [GSYM real_inst_length_thm];

fun take n [] = []
  | take 0 xs = []
  | take n (x::xs) = x::take (n-1) xs;

fun drop n [] = []
  | drop 0 xs = xs
  | drop n (x::xs) = drop (n-1) xs;

fun x64_code_rev ys = let
  val chunk_size = 5000
  val chunk_size_gc = 1 * chunk_size
  fun eval_chunks i total n [] = []
    | eval_chunks i total n xs = let
    val _ = print ((int_to_string i) ^ " of " ^ (int_to_string total) ^ "\n")
    val ys = take chunk_size xs
    val end_tm = mk_var("rest",``:bc_inst list``)
    val list_term = foldr (fn (x,y) => listSyntax.mk_cons(x,y)) end_tm ys
    val _ = if i mod chunk_size_gc = 0 then PolyML.fullGC() else ()
    val lemma = time EVAL ``x64_code_rev ^n ^list_term res``
    val n = lemma |> concl |> rand |> rator |> rator |> rand
    in lemma :: eval_chunks (i+chunk_size) total n (drop chunk_size xs) end
  val res = eval_chunks 0 (length ys) ``0:num`` ys
  val thms = res
  val lemma = REFL ``x64_code_rev 0 rest []``
  val rest_var = ``rest : bc_inst list``
  val res_var = ``res : word8 list``
  fun stick_together lemma [] = lemma
    | stick_together lemma thms = let
    val (th::thms) = thms
    val res_tm = lemma |> concl |> dest_eq |> snd |> rand
    val input_tm = th |> concl |> dest_eq |> fst |> rator |> rand
    val th1 = lemma |> INST [rest_var|->input_tm]
    val th2 = th |> INST [res_var|->res_tm]
    val lemma = TRANS th1 th2
    in stick_together lemma thms end
  val _ = print "Plugging parts together\n"
  val result = time (stick_together lemma) res
  val result = INST [rest_var |-> ``[] : bc_inst list``,
                     res_var |-> ``[] : word8 list``] result
  val rw = x64_code_rev_def |> CONJUNCT1 |> SPEC_ALL
  val result = CONV_RULE (RAND_CONV (REWR_CONV rw)) result
  in result end;

val x64_code_evaluated = let
  val (xs,ty) = proper_code_labels_rev_bootstrap_lcode
                |> concl |> rand |> listSyntax.dest_list
  val result = time x64_code_rev xs
  val rw = proper_code_labels_rev_bootstrap_lcode
  val result = CONV_RULE
    ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
       (TRY_CONV (REWR_CONV (GSYM rw))) THENC
     REWR_CONV x64_code_INTRO THENC
     RAND_CONV listLib.REVERSE_CONV) result
  in result end;

val x64_code_LENGTH_evaluated = let
  val tm = x64_code_evaluated |> concl |> rator |> rand
  in (RAND_CONV (REWR_CONV x64_code_evaluated)
      THENC listLib.LENGTH_CONV) ``LENGTH ^tm``
     |> RW [GSYM x64_bootstrap_code_def] end;

val _ = save_thm("x64_code_evaluated",x64_code_evaluated);
val _ = save_thm("x64_code_LENGTH_evaluated",x64_code_LENGTH_evaluated);

*)

val _ = export_theory();
