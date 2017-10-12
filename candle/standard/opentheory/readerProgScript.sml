open preamble
     readerTheory
     ml_monad_translatorLib
     ml_hol_kernelProgTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

(* --- Standard translation --- *)

val _ = translate init_state_def
(*val _ = translate K_DEF*)
(*val _ = translate EVEN*)
val _ = translate mk_BN_def
val _ = translate mk_BS_def
val _ = translate insert_def
val _ = translate delete_def
val _ = translate lookup_def
val _ = translate push_def
val _ = translate insert_dict_def
val _ = translate delete_dict_def
val _ = translate first_def
(*val _ = translate REVERSE_DEF*)
val _ = translate stringTheory.isDigit_def

(* --- match_type, tymatch : Replace REV_ASSOCD, use MEM_INTRO. --- *)

val rev_assocd_thm = Q.prove (
  `!a l d. REV_ASSOCD a l d = rev_assocd a l d`,
  recInduct (fetch "holKernel" "rev_assocd_ind") \\ rw []
  \\ Cases_on `l` \\ fs []
  \\ once_rewrite_tac [holKernelTheory.rev_assocd_def]
  \\ fs [holSyntaxLibTheory.REV_ASSOCD_def]
  \\ PairCases_on `h` \\ fs [])

val _ = translate rev_assocd_thm;

val _ = (use_mem_intro := true)
val _ = translate holSyntaxExtraTheory.tymatch_def
val _ = (use_mem_intro := false)
val _ = translate OPTION_MAP_DEF
val _ = translate holSyntaxExtraTheory.match_type_def

(* --- Side conditions --- *)

(*val _ = translate FRONT_DEF*)

(*val front_side = Q.store_thm ("front_side",*)
  (*`!xs. front_side xs <=> xs <> []`,*)
  (*Induct*)
  (*\\ once_rewrite_tac [fetch "-" "front_side_def"] \\ fs [])*)
  (*|> update_precondition;*)

val _ = translate numposrepTheory.l2n_def

val l2n_side = Q.store_thm("l2n_side",
  `!a0 a1. l2n_side a0 a1 <=> T`,
  cheat
  (*fetch "-" "l2n_side_def"*)
  ) |> update_precondition;

val _ = translate ASCIInumbersTheory.s2n_def

val _ = translate ASCIInumbersTheory.UNHEX_def

val unhex_side = Q.store_thm("unhex_side",
  `!x1. unhex_side x1 <=> T`,
  cheat
  (*fetch "-" "unhex_side_def"*)
  ) |> update_precondition;

val _ = translate ASCIInumbersTheory.num_from_dec_string_def
val _ = translate ASCIInumbersTheory.fromDecString_def

(* --- Monadic translation --- *)

val _ = m_translate find_axiom_def
val _ = m_translate getNum_def
val _ = m_translate getName_def
val _ = m_translate getList_def
val _ = m_translate getTypeOp_def
val _ = m_translate getType_def
val _ = m_translate getConst_def
val _ = m_translate getVar_def
val _ = m_translate getTerm_def
val _ = m_translate getThm_def
val _ = m_translate pop_def
val _ = m_translate peek_def
val _ = m_translate getPair_def
val _ = m_translate getNvs_def
val _ = m_translate getCns_def
val _ = m_translate getTys_def
val _ = m_translate getTms_def

val r = m_translate readLine_def (* Has side conditions *)

val readline_side = Q.store_thm("readline_side",
  `!v0 v1. readline_side v0 v1 <=> T`,
  cheat
  (*fetch "-" "readline_side_def"*)
  ) |> update_precondition;

val r = m_translate readLines_def
val r = m_translate run_reader_def

(* --- Get reader program. --- *)

(*
val reader_prog_tm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl
  |> rator |> rator |> rand
  |> EVAL |> concl |> rhs
*)

(* --- Imperative code --- *)

open ioProgTheory cfTacticsLib basisFunctionsLib rofsFFITheory
      mlfileioProgTheory

(*
val _ = translation_extends "ioProg"
val _ = append_decs reader_prog_tm
*)

(*
val r =
  reader_prog_thm
  |> concl |> rator |> rator |> rand
  |> EVAL |> concl |> rhs
  |> append_prog
*)

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>"`
val _ = translate msg_usage_def

val _ = process_topdecs `
  fun msg_bad_name s = String.concat ["Bad filename: ", s, "\n"]

  fun msg_success len =
    String.concat [ "Success. Theorem stack contains ", Int.toString len
                  , " theorems." ]

  fun msg_failure loc =
    String.concat [ "FAIL.\n Exception thrown from ", loc, "." ]
  ` |> append_prog;

val _ = process_topdecs`
  fun read_lines ls =
    let
      val st_rec = run_reader ls
      val thms  = st_rec.thms
    in
      print (msg_success (length thms));
      print "OK."
    end
    handle Fail msg => printerr (msg_failure msg)
  ` |> append_prog;

val _ = process_topdecs `
  fun read_file fname =
    case FileIO.inputLinesFrom fname of
      SOME ls => read_lines ls
    | NONE    => print_err (msg_bad_name fname)
  ` |> append_prog;

val _ = process_topdecs `
  fun reader_main u =
    case Commandline.arguments () of
      [fname] => read_file fname
    | _       => print_err msg_usage
  ` |> append_prog;

val reader_prog_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]

val _ = save_thm ("reader_prog_thm", reader_prog_thm);

val _ = export_theory ();

