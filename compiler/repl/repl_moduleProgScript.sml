(*
  Module for the configurable part of the REPL. Note that this file
  does not contain the code for the main loop of the REPL (which is at
  the end of bootstrap translation).

  This REPL module defines some references:
   - REPL.prompt : string ref
      -- the string that the default input function prints before reading
         user input (by default this is "> ")
   - REPL.isEOF : bool ref
      -- true means that all user input has been read (e.g. if we have
         reached the end of stdin)
   - REPL.nextString : string ref
      -- contains the next user input (if isEOF is false)
   - REPL.readNextString : (unit -> unit) ref
      -- the function that the REPL uses to read user input; it is this
         function that assigns new values to REPL.isEOF and REPL.nextString.

  At runtine, users are allowed (encouraged?) to change these references.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib basisFunctionsLib
     candle_kernelProgTheory

val _ = new_theory"repl_moduleProg";

val _ = translation_extends "candle_kernelProg";

val _ = ml_prog_update (open_module "REPL");

(* declares: val exn = ref Bind; *)
val bind_e = ``App Opref [Con (SOME (Short "Bind")) []]``
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = ``^st with refs := ^st.refs ++ [Refv (Conv (SOME (ExnStamp 0)) [])]``
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, bind_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ gvs [] \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "exn" v_tm
  val v_thm = v_thm |> CONV_RULE (PATH_CONV "lr" (EVAL THENC
     REWRITE_CONV (DB.find "refs_def" |> map (fst o snd)) THENC
     REWRITE_CONV [APPEND,APPEND_NIL]))
  in v_thm |> REWRITE_RULE [GSYM v_def] end
val _ = ml_prog_update (add_Dlet eval_thm "exn" []);

Theorem isEOF_def      = declare_new_ref "isEOF"      “F”
Theorem nextString_def = declare_new_ref "nextString" “strlit ""”

val _ = ml_prog_update open_local_block;

Definition char_cons_def:
  char_cons (x:char) l = x::(l:char list)
End

val char_cons_v_thm = translate char_cons_def;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  fun charsFrom fname =
    case TextIO.foldChars char_cons [] (Some fname) of
      Some res => List.rev res
    | None     => (print ("ERROR: Unable to read file: " ^ fname ^ "\n");
                   Runtime.exit(5)); `

val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs) `
  fun default_readNextString () =
    (TextIO.print (!prompt);
     case TextIO.inputLine TextIO.stdIn of
       None =>      (isEOF := True;  nextString := "")
     | Some line => (isEOF := False; nextString := line)); `

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  val readNextString = Ref default_readNextString; `

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* --- *)

val repl_prog = get_ml_prog_state () |> remove_snocs |> ml_progLib.get_prog;

val repl_prog_def = Define `repl_prog = ^repl_prog`;

Theorem Decls_repl_prog =
  ml_progLib.get_Decls_thm (get_ml_prog_state ())
  |> REWRITE_RULE [GSYM repl_prog_def];

(* verification of REPL.charsFrom *)

Theorem charsFrom_spec:
  file_content fs fname = SOME content ∧ hasFreeFD fs ∧
  FILENAME fname fnamev ⇒
  app (p:'ffi ffi_proj) TextIO_charsFrom_v [fnamev]
    (STDIO fs)
    (POSTv retv. STDIO fs * cond (HOL_STRING_TYPE content retv))
Proof
  xcf_with_def "REPL.charsFrom" (fetch "-" "REPL_charsFrom_v_def")
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet ‘POSTv retv. STDIO fs *
                 & (OPTION_TYPE (LIST_TYPE CHAR)
                      (OPTION_MAP (foldl char_cons []) (file_content fs fname))
                      retv)’
  THEN1
   (assume_tac char_cons_v_thm
    \\ drule foldChars_SOME \\ fs []
    \\ disch_then (drule_at (Pos last))
    \\ fs [std_preludeTheory.OPTION_TYPE_def,PULL_EXISTS]
    \\ disch_then (drule_at (Pos last))
    \\ disch_then (qspecl_then [‘v’,‘[]’,‘p’] mp_tac)
    \\ fs [LIST_TYPE_def]
    \\ strip_tac
    \\ xapp \\ xsimpl
    \\ qexists_tac ‘[]’
    \\ qexists_tac ‘fname’
    \\ fs [std_preludeTheory.OPTION_TYPE_def,LIST_TYPE_def])
  \\ gvs [decProgTheory.OPTION_TYPE_def,LIST_TYPE_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto \\ xsimpl
  \\ xcon \\ xsimpl
  \\ fs [foldl_char_cons]
QED

val _ = export_theory();
