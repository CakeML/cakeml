open preamble
     readerTheory
     ml_monad_translatorLib
     ml_hol_kernelProgTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

(* --- Standard translation --- *)

val _ = translate init_state_def
val _ = translate mk_BN_def
val _ = translate mk_BS_def
val _ = translate insert_def
val _ = translate delete_def
val _ = translate lookup_def
val _ = translate push_def
val _ = translate insert_dict_def
val _ = translate delete_dict_def
val _ = translate first_def
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

val _ = m_translate readLine_def (* Has side conditions *)

val readline_side = Q.store_thm("readline_side",
  `!v0 v1. readline_side v0 v1 <=> T`,
  cheat
  (*fetch "-" "readline_side_def"*)
  ) |> update_precondition;

val _ = m_translate readLines_def
val _ = m_translate run_reader_def

(* --- CakeML wrapper --- *)

open ioProgTheory ioProgLib cfTacticsLib basisFunctionsLib rofsFFITheory
     mlfileioProgTheory

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [strlit"Bad filename: "; s; strlit".\n"]
  `;

val msg_failure_def = Define `
  msg_failure loc = concat
    [strlit"Reader threw exception: "; loc; strlit".\n"]
  `;

val _ = translate msg_usage_def
val _ = translate msg_bad_name_def
val _ = translate msg_failure_def

(* For some reason inputLine keeps the newline characters *)

val clean_line_def = Define `
  clean_line s =
    case explode s of
      []    => strlit""
    | c::cs => implode (FRONT (c::cs))
    `;

val clean_lines_def = Define `
  clean_lines ss = FILTER ($<> (strlit"")) (MAP clean_line ss)
  `;

val _ = translate clean_line_def
val _ = translate clean_lines_def

val _ = process_topdecs `
  fun read_lines ls =
    let
      val st_rec = run_reader (clean_lines ls)
      (*val thms = st_rec.thms*)
    in
      (*print (msg_success (length thms));*)
      print "OK.\n"
    end
    handle Fail msg => print_err (msg_failure msg)
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

val st   = get_ml_prog_state ();
val name = "reader_main"

(* TODO: Replace with call_thm *)
val reader_prog_tm =
  let
    val th =
      call_main_thm_basis
      |> C MATCH_MP (st |> get_thm |> GEN_ALL |> ISPEC basis_ffi_tm)
      |> SPEC(stringSyntax.fromMLstring name)
      |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
      |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
      (*|> C HO_MATCH_MP spec*)
    val prog_with_snoc = th |> concl |> find_term listSyntax.is_snoc
    val prog_rewrite = EVAL prog_with_snoc
  in
    rhs (concl prog_rewrite)
  end

val reader_prog_def = Define `reader_prog = ^reader_prog_tm`

val _ = export_theory ();

