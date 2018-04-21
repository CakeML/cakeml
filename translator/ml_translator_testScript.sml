open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_translator_test";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;

(* This file contains a collection of functions that have in the past
   turned out to be tricky to translate. *)

val ZIP2_def = Define `
  (ZIP2 ([],[]) z = []) /\
  (ZIP2 (x::xs,y::ys) z = (x,y) :: ZIP2 (xs, ys) (5:int))`

val res = translate ZIP2_def;

val res = translate APPEND;
val res = translate REVERSE_DEF;
val res = translate mllistTheory.tabulate_aux_def;

val res = translate MEMBER_def;

val AEVERY_AUX_def = Define `
  (AEVERY_AUX aux P [] = T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) =
     if MEMBER x aux then AEVERY_AUX aux P xs else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)`;

val res = translate AEVERY_AUX_def;

val res = translate mlstringTheory.strcat_def;
val res = translate mlstringTheory.concatWith_aux_def

val ADEL_def = Define `
  (ADEL [] z = []) /\
  (ADEL ((x:'a,y:'b)::xs) z = if x = z then ADEL xs z else (x,y)::ADEL xs z)`

val res = translate ADEL_def;

val ZIP4_def = Define `
  ZIP4 xs = ZIP2 xs 6`

val res = translate ZIP4_def;

val char_to_byte_def = Define`
  char_to_byte c = (n2w (ORD c) : word8)`;

val res = translate char_to_byte_def;

val res = translate MAP;

val res = translate mlstringTheory.explode_aux_def;

val res = translate mlstringTheory.explode_def;

val string_to_bytes_def = Define`
  string_to_bytes s = MAP char_to_byte (explode s)`;

val res = translate string_to_bytes_def;

val res = translate miscTheory.any_word64_ror_def

val def = Define `bar = []:'a list`
val res = translate def

val def = Define `foo = if bar = []:'a list then [] else []:'a list`
val res = translate def

val def = Define `foo = 4:num`
val res = translate def

val _ = Datatype`
  foo = <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; do_known : bool
            ; do_call : bool |>`
val res = register_type``:foo``

val foo_def = tDefine"foo"`
  foo (k:num) n =
  if n = 0 then []
  else if n ≤ 256n then [k]
  else foo (k+1) (n-256)`
  (WF_REL_TAC `measure SND`\\fs[])

val res = translate foo_def

val _ = Datatype `bar1 = ta | ti`
val _ = Datatype `bar2 = Ta | TI`
val _ = register_type ``:bar1``
val _ = register_type ``:bar2``

val and_pre_def = Define`
  and_pre x ⇔ x <> 0i ∧ 2 / x > 0`;
val or_pre_def = Define`
  or_pre x = if (x = 0) \/ 2 / x > 0 then and_pre x \/ 0 < x else x < 0`
val res =  translate and_pre_def;
val res =  translate or_pre_def;

val _ = Hol_datatype `exn_type = Fail of string | Subscript`
val _ = register_exn_type ``:exn_type``

val _ = (print_asts := true);

(* test no_ind *)

val word64_msb_thm = Q.prove(
  `!w. word_msb (w:word64) =
         ((w && 0x8000000000000000w) = 0x8000000000000000w)`,
  blastLib.BBLAST_TAC);

val res = translate word64_msb_thm;

val res = translate (miscTheory.arith_shift_right_def
                     |> INST_TYPE [alpha|->``:64``]
                     |> PURE_REWRITE_RULE [wordsTheory.dimindex_64]
                     |> CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV));

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ first_x_assum match_mp_tac \\ wordsLib.WORD_EVAL_TAC \\ rw[])
  |> update_precondition;

val shift_test_def = Define `shift_test (x:word64) y = arith_shift_right x y`

val res = translate shift_test_def;

val _ = export_theory();
