open preamble
     readerTheory
     ml_monad_translatorLib
     ml_hol_kernelProgTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

(* --- Translate readerTheory ---------------------------------------------- *)

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
val _ = m_translate readLine_def

val readline_side = Q.store_thm("readline_side",
  `!st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

(* --- CakeML wrapper ------------------------------------------------------ *)

open basisProgTheory basis_ffiTheory basis_ffiLib basisFunctionsLib
     cfTacticsLib cfLib fsFFITheory
open cfMonadTheory cfMonadLib
open ml_translatorTheory fsFFIPropsTheory

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

val _ = process_topdecs `
  fun read_line st0 ins =
    case TextIO.inputLine ins of
      NONE    => st0 (* EOF *)
    | SOME ln =>
        let val len = String.size ln in
          if len <= 1 then st0 (* Invalid line; "" or "\n" *)
          else if String.sub ln 0 = #"#" then st0 (* Comment *)
          else
            let
              val pfx = String.extract ln 0 (SOME (len-1))
            in
              readline pfx st0
            end
        end`
  |> append_prog;

val Valid_line_def = Define `
  Valid_line str <=>
    STRLEN str > 1 /\
    ~IS_PREFIX str "#"`;

val str_prefix_def = Define `
  str_prefix str = extract str 0 (SOME (strlen str - 1))`;

val readline_spec = save_thm (
  "readline_spec",
  mk_app_of_ArrowP ``p: 'ffi ffi_proj`` (theorem "readline_v_thm"));

(* Additional definitions *)
open holKernelTheory ml_monadBaseTheory mlstringTheory

val read_line_spec = Q.store_thm("read_line_spec",
  `WORD (n2w fd : word8) fdv /\ fd <= 255 /\
   IS_SOME (get_file_content fs fd) /\
   STATE_TYPE st stv
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "read_line" (get_ml_prog_state()))
     [stv; fdv]
     (STDIO fs * HOL_STORE refs)
     (POST
       (\stov.
        case lineFD fs fd of
          NONE =>
            STDIO (lineForwardFD fs fd) *
            HOL_STORE refs *
            &(stov = stv)
        | SOME ln =>
            if Valid_line ln then
              SEP_EXISTS sto refs'.
                STDIO (lineForwardFD fs fd) * HOL_STORE refs' *
                &(readLine (str_prefix (strlit ln)) st refs = (Success sto, refs')) *
                &STATE_TYPE sto stov
            else
              STDIO (lineForwardFD fs fd) *
              HOL_STORE refs *
              &(stov = stv))
       (\ev.
         SEP_EXISTS e ln refs'.
           STDIO (lineForwardFD fs fd) * HOL_STORE refs' *
           &(readLine (str_prefix (strlit ln)) st refs = (Failure e, refs')) *
           &HOL_EXN_TYPE e ev *
           &(lineFD fs fd = SOME ln /\
             STRLEN ln > 1 /\
             ~IS_PREFIX ln "#")))`,
  xcf "read_line" (get_ml_prog_state())
  \\ xlet_auto >- xsimpl (* TextIO.inputLine *)
  \\ Cases_on `lineFD fs fd` \\ fs [OPTION_TYPE_def] \\ xmatch
  >- (xvar \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif \\ fs [Valid_line_def]
  >- (xvar \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (`?t. x = #"#"::t` by (Cases_on `x` \\ fs [implode_def]) \\ fs []
    \\ xvar \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ `OPTION_TYPE NUM (SOME (STRLEN x - 1)) v'` by
   (fs [OPTION_TYPE_def, NUM_def, INT_def]
    \\ Cases_on `x` \\ fs []
    \\ intLib.COOPER_TAC)
  \\ rveq
  \\ xlet_auto >- xsimpl
  \\ xapp \\ xsimpl
  \\ instantiate \\ xsimpl
  \\ fs [str_prefix_def]
  \\ xsimpl
  \\ `?h t. x = h::t /\ h <> #"#"` by (Cases_on `x` \\ fs [implode_def]) \\ fs []
  \\ qexists_tac `STDIO (lineForwardFD fs fd)` \\ xsimpl
  \\ qexists_tac `refs` \\ xsimpl
  \\ conj_tac
  \\ rw [implode_def] \\ xsimpl);

(* Read all lines until input is exhausted *)
val _ = process_topdecs `
  fun read_lines inp =



  `
  |> append_prog;

(*
val _ = process_topdecs `
  fun read_lines ls =
    let
      val st = run_reader (strip_comments (clean_lines ls))
    in
      TextIO.print_string "OK.\n"
    end
    handle Fail Lsg => TextIO.prerr_string (msg_failure msg)
  ` |> append_prog;
*)
val _ = process_topdecs `
  fun read_file fname =
    case TextIO.inputLinesFrom fname of
      SOME ls => read_lines ls
    | NONE    => TextIO.prerr_string (msg_bad_name fname)
  ` |> append_prog;

val _ = process_topdecs `
  fun reader_main u =
    case CommandLine.arguments () of
      [fname] => read_file fname
    | _       => TextIO.prerr_string msg_usage
  ` |> append_prog;

val st   = get_ml_prog_state ();
val name = "reader_main"

open ml_progLib

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

