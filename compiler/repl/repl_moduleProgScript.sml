(*
  This file defines two modules:
  - Repl, for the configurable part of the REPL,
  - Interrupt, for the INT signal polling mechanism, which raises the
    Interrupt exception.

  Note that this file does not contain the code for the main loop of the REPL
  (which is at the end of bootstrap translation).

  This Repl module defines some references:
   - Repl.isEOF : bool ref
      -- true means that all user input has been read (e.g. if we have
         reached the end of stdin)
   - Repl.nextString : string ref
      -- contains the next user input (if isEOF is false)
   - Repl.readNextString : (unit -> unit) ref
      -- the function that the Repl uses to read user input; it is this
         function that assigns new values to Repl.isEOF and Repl.nextString
   - Repl.exn : exn
      -- the most recent exception to propagate to the top

  At runtine, users are allowed (encouraged?) to change these references.

  The Interrupt module contains:
  - Interrupt.check : unit -> unit
    -- This function checks whether an INT signal has been trapped by the
       runtime, and raises the Interrupt exception (defined outside of this
       module) if that has happened. Users are responsible of calling
       Interrupt.poll at the start of functions that might loop forever, or
       the interrupt will not be detected.
  - Interrupt.poll : unit -> unit
    -- Same as above, but here the checks are performed with a
       frequency controlled by another reference:
  - Interrupt.freq : int ref
    -- Default value is 1000, meaning that the FFI call occurs after 1000 steps.
       All values below 1 are treated as 1.

*)
Theory repl_moduleProg
Ancestors
  ml_translator candle_kernelProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib cfLib

val _ = translation_extends "candle_kernelProg";

val _ = (append_prog o process_topdecs) `
  fun pp_type ty =
    ((case ty of Tyvar _ => () | _ => ());
     PrettyPrinter.token "<type>");
  fun pp_hol_type ty =
    ((case ty of Tyvar _ => () | _ => ());
     PrettyPrinter.token "<hol_type>");
  fun pp_term tm =
    ((case tm of Var _ _ => () | _ => ());
     PrettyPrinter.token "<term>");
  fun pp_thm th =
    (case th of Sequent _ _ =>
     PrettyPrinter.token "<thm>");
  fun pp_update up =
    ((case up of Newaxiom _ => () | _ => ());
     PrettyPrinter.token "<update>"); `

val _ = (append_prog o process_topdecs) ‘exception Interrupt;’;

val _ = ml_prog_update (open_module "Interrupt");

val _ = ml_prog_update open_local_block;

val sigint_e = “App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)]”;
val eval_thm = let
  val env = get_ml_prog_state () |> ml_progLib.get_env
  val st = get_ml_prog_state () |> ml_progLib.get_state
  val new_st = “^st with refs := ^st.refs ++ [W8array [0w]]”
  val goal = list_mk_icomb (prim_mk_const {Thy="ml_prog", Name="eval_rel"},
    [st, env, sigint_e, new_st, mk_var ("x", semanticPrimitivesSyntax.v_ty)])
  val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
  val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "sigint_loc" v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end
val _ = ml_prog_update (add_Dlet eval_thm "sigint");

Theorem count_eval_thm = declare_new_ref "count" “1000:int”;

val _ = ml_prog_update open_local_in_block;

Theorem freq_eval_thm = declare_new_ref "freq" “1000:int”;

val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs) ‘
  fun inc () =
    let val res = !count in
      count := res - 1;
      if res < 2 then
        (count := max 1 (!freq) ; True)
      else False
    end;
  ’;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) ‘
  fun check () =
    let val _ = #(poll_sigint) "" sigint in
      if Word8Array.sub sigint 0 = Word8.fromInt 1 then
        raise Interrupt
      else ()
    end;
  fun poll () = if inc () then check () else ();
  ’;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

val tidy_up =
  SIMP_RULE (srw_ss()) (LENGTH :: (DB.find "refs_def" |> map (#1 o #2)));

val _ = ml_prog_update (open_module "Repl");

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
    \\ asm_simp_tac bool_ss [] \\ fs [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL
    |> CONV_RULE (PATH_CONV "lr" EVAL)
  val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
  val v_def = define_abbrev false "exn" v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end
val _ = ml_prog_update (add_Dlet eval_thm "exn");

Theorem exn_def[allow_rebind]          = fetch "-" "exn_def"                        |> tidy_up;
Theorem isEOF_def[allow_rebind]        = declare_new_ref "isEOF"        “F”         |> tidy_up;
Theorem nextString_def[allow_rebind]   = declare_new_ref "nextString"   “strlit ""” |> tidy_up;
Theorem errorMessage_def[allow_rebind] = declare_new_ref "errorMessage" “strlit ""” |> tidy_up;

val _ = ml_prog_update open_local_block;

Definition char_cons_def:
  char_cons (x:char) l = x::(l:char list)
End

val _ = (next_ml_names := ["char_cons"]);
val char_cons_v_thm = translate char_cons_def;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  fun charsFrom fname =
    case TextIO.foldChars char_cons [] (Some fname) of
      Some res => List.rev res
    | None     => (print ("ERROR: Unable to read file: " ^ fname ^ "\n");
                   raise Bind); `

val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs) `
  fun init_readNextString () =
    let
      val _ = TextIO.print "Welcome to the CakeML read-eval-print loop.\n"
      val fname = (if !nextString = "candle" then "candle_boot.ml" else "repl_boot.cml")
      val str = charsFrom fname
    in
      (isEOF := False; nextString := String.implode str)
    end; `

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  val readNextString = Ref init_readNextString; `

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* --- *)

val repl_prog = get_ml_prog_state () |> remove_snocs |> ml_progLib.get_prog;

Definition repl_prog_def:
  repl_prog = ^repl_prog
End

Theorem Decls_repl_prog =
  ml_progLib.get_Decls_thm (get_ml_prog_state ())
  |> REWRITE_RULE [GSYM repl_prog_def];

(* verification of Repl.charsFrom *)

Triviality foldl_char_cons:
  ∀xs ys. foldl char_cons ys xs = REVERSE xs ++ ys
Proof
  Induct \\ fs [mllistTheory.foldl_def,char_cons_def]
QED

Theorem charsFrom_spec:
  file_content fs fname = SOME content ∧ hasFreeFD fs ∧
  FILENAME fname fnamev ⇒
  app (p:'ffi ffi_proj) Repl_charsFrom_v [fnamev]
    (STDIO fs)
    (POSTv retv. STDIO fs * cond (LIST_TYPE CHAR content retv))
Proof
  strip_tac
  \\ xcf_with_def (fetch "-" "Repl_charsFrom_v_def")
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet ‘POSTv retv. STDIO fs *
                 & (OPTION_TYPE (LIST_TYPE CHAR)
                      (OPTION_MAP (foldl char_cons []) (file_content fs fname))
                      retv)’
  THEN1
   (assume_tac char_cons_v_thm
    \\ drule TextIOProofTheory.foldChars_SOME \\ fs []
    \\ disch_then (drule_at (Pos last))
    \\ fs [std_preludeTheory.OPTION_TYPE_def,PULL_EXISTS]
    \\ disch_then (drule_at (Pos last))
    \\ rename [‘w = Conv _ []’]
    \\ disch_then (qspecl_then [‘w’,‘[]’,‘p’] mp_tac)
    \\ fs [LIST_TYPE_def]
    \\ strip_tac
    \\ xapp \\ xsimpl \\ rw []
    \\ fs [std_preludeTheory.OPTION_TYPE_def,LIST_TYPE_def])
  \\ gvs [std_preludeTheory.OPTION_TYPE_def,LIST_TYPE_def]
  \\ xmatch
  \\ xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [“:'a”|->“:char”])
  \\ xsimpl
  \\ first_x_assum $ irule_at Any
  \\ fs [foldl_char_cons]
QED

