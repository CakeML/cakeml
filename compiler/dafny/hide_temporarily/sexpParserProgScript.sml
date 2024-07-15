(*
 * Translate the alternative s-expression parser.
 *
 * Adapted from compiler/bootstrap/translation/sexp_parserProgScript.sml
 *)

open preamble
open basis

val _ = use_long_names:=true;
    
val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "sexpParserProg";
val _ = translation_extends "basisProg";

val r = translate simpleSexpPEGTheory.pnt_def;
val r = translate pegTheory.ignoreR_def;
val r = translate pegTheory.ignoreL_def;
val r = translate simpleSexpTheory.arb_sexp_def;
val r = translate simpleSexpPEGTheory.sumID_def;
val r = translate simpleSexpPEGTheory.choicel_def;

val r = translate simpleSexpPEGTheory.tokeq_def;
val r = translate simpleSexpPEGTheory.pegf_def;
val r = translate simpleSexpPEGTheory.grabWS_def;
val r = translate simpleSexpPEGTheory.replace_nil_def;
val r = translate simpleSexpTheory.destSXNUM_def;
val r = translate simpleSexpTheory.destSXCONS_def;
val r = translate simpleSexpTheory.destSXSYM_def;
val r = translate stringTheory.isPrint_def;
val r = translate stringTheory.isGraph_def;
val r = translate stringTheory.isDigit_def; (* Added *)
val r = translate (simpleSexpTheory.valid_first_symchar_def
                  |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY]);
val r = translate (simpleSexpTheory.valid_symchar_def
                  |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY]);
val r = translate pairTheory.PAIR_MAP_THM;
val r = translate listTheory.FOLDL; (* Added *)
val r = translate finite_mapTheory.FUPDATE_LIST; (* Added *)
val r = translate simpleSexpPEGTheory.sexpPEG_def;
val () = next_ml_names := ["destResult"];
val r = translate pegexecTheory.destResult_def;

(* Added section *)
val r = translate pegTheory.optmax_def;
val r = translate locationTheory.locnrow_def;
val r = translate locationTheory.locncol_def;
val r = translate locationTheory.locnle_def;
val r = translate locationTheory.locsle_def;
val r = translate pegTheory.MAXerr_def;
val r = translate pegTheory.sloc_def;
val r = translate boolTheory.IN_DEF;
val r = translate sumTheory.ISL; (* Added *)

(* Copied from examples/grepProgScript.sml *)
Theorem INTRO_FLOOKUP:
   (if n ∈ FDOM G.rules then
      pegexec$EV (G.rules ' n) i r eo errs (appf1 tf3 k) fk
    else Looped) =
   (case FLOOKUP G.rules n of
      NONE => Looped
    | SOME x => pegexec$EV x i r eo errs (appf1 tf3 k) fk)
Proof
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]
QED

val r = translate pegexecTheory.poplist_aux_def; (* Added *)
val r = translate pegexecTheory.poplistval_def; (* Added *)
(* coreloop translation copied from examples/grepProgScript *)
val coreloop_def' = pegexecTheory.coreloop_def
                      |> REWRITE_RULE [INTRO_FLOOKUP]
                      |> SPEC_ALL
                      |> ONCE_REWRITE_RULE [FUN_EQ_THM];
val r = translate coreloop_def';

val r = translate pegexecTheory.peg_exec_def;

(* Moved monad_unitbind_assert and OPTION_BIND_THM close to where they are first used *)

(* Replaced parserProgTheory.monad_unitbind_assert; with actual definition to avoid
 * including it *)
Theorem monad_unitbind_assert:
  !b x. OPTION_IGNORE_BIND (OPTION_GUARD b) x = if b then x else NONE
Proof
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []
QED

Theorem OPTION_BIND_THM:
   !x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i
Proof
  Cases THEN SRW_TAC [] []
QED

val r =
  simpleSexpParseTheory.parse_sexp_def
  |> SIMP_RULE std_ss[monad_unitbind_assert,OPTION_BIND_THM,
                  pegexecTheory.pegparse_def,
                  simpleSexpPEGTheory.wfG_sexpPEG,UNCURRY,GSYM NULL_EQ]
  |> translate;

(* ^^^ works ^^^ *)
val termination_lemma = MATCH_MP pegexecTheory.coreloop_total simpleSexpPEGTheory.wfG_sexpPEG
                          |> SIMP_RULE(srw_ss())[coreloop_def'];

val parse_sexp_side = Q.prove(
  `∀x. simplesexpparse_parse_sexp_side x = T`,
     rw[fetch "-" "simplesexpparse_parse_sexp_side_def"]
  \\ rw[fetch "-" "pegexec_peg_exec_side_def"]
  \\ rw[fetch "-" "pegexec_coreloop_side_def"]
  \\ qspec_then`MAP add_loc x`strip_assume_tac (GEN_ALL termination_lemma)
  \\ qmatch_abbrev_tac`IS_SOME (OWHILE f g h)`
  \\ qmatch_assum_abbrev_tac`OWHILE f g' h = SOME _`
  \\ qsuff_tac `g' = g` THEN1 (rw [] \\ fs [])
  \\ unabbrev_all_tac
  \\ simp[FUN_EQ_THM]
  \\ Cases \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]) |> update_precondition;

(* Changes from sexp_parserProgScript.sml:
 * - use fetch "-" "..."
 * - update names (goal, definition) *)
val parse_sexp_side = Q.prove(
  `∀x. simplesexpparse_parse_sexp_side x = T`,
  simp[fetch "-" "simplesexpparse_parse_sexp_side_def",
       fetch "-" "pegexec_peg_exec_side_def",
       fetch "-" "pegexec_coreloop_side_def"]
  \\ qx_gen_tac`i`
  \\ (MATCH_MP pegexecTheory.peg_exec_total simpleSexpPEGTheory.wfG_sexpPEG
        |> strip_assume_tac)
  \\ fs[fetch "-" "pegexec_destresult_side_def"]
  \\ (MATCH_MP pegexecTheory.coreloop_total simpleSexpPEGTheory.wfG_sexpPEG
        |> strip_assume_tac)
  \\ fs[coreloop_def']
  \\ qmatch_abbrev_tac`IS_SOME (OWHILE a b c)`
  \\ qmatch_assum_abbrev_tac`OWHILE a b' c = _`
  \\ qsuff_tac `b = b'` THEN1 fs []
  \\ simp[Abbr`b`,Abbr`b'`,FUN_EQ_THM]
  \\ rpt gen_tac
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ Cases_on ‘k’ \\ TRY (fs [] \\ NO_TAC)
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[])
                        |> update_precondition;


val r = fromSexpTheory.sexplist_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM]
        |> translate;

val r = translate simpleSexpTheory.strip_sxcons_def
val r = translate simpleSexpTheory.dstrip_sexp_def


val _ = export_theory ();
