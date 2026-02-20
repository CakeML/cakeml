(*
  Translates the Dafny to CakeML compiler.
*)
Theory dafny_compilerProg
Ancestors
  dafny_remove_assertProg dafny_compiler
  fromSexp
Libs
  preamble ml_translatorLib basisFunctionsLib

val _ = translation_extends "dafny_remove_assertProg";

val _ = ml_translatorLib.use_sub_check true;
val _ = add_preferred_thy "-";

(* fromSexp encoder translations *)

val r = translate fromSexpTheory.listsexp_def;

val r = translate (fromSexpTheory.locnsexp_def |> SIMP_RULE list_ss []);
val r = translate fromSexpTheory.locssexp_def;

val r = translate stringTheory.isPrint_def;

val r = translate ASCIInumbersTheory.HEX_def;

Definition hex_alt_def:
  hex_alt x = if x < 16 then HEX x else #"0"
End

val r = translate hex_alt_def;

Theorem hex_alt_side_thm[local]:
  ∀n. hex_alt_side n ⇔ T
Proof
  PURE_REWRITE_TAC [fetch "-" "hex_alt_side_def",fetch "-" "hex_side_def"]
  >> intLib.COOPER_TAC
QED

val _ = hex_alt_side_thm |> update_precondition;

Definition num_to_hex_string_alt:
  num_to_hex_string_alt = n2s 16 hex_alt
End

Theorem num_to_hex_string_alt_intro:
  ∀n. num_to_hex_string n = num_to_hex_string_alt n
Proof
  simp[num_to_hex_string_def,num_to_hex_string_alt,n2s_def] >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rw[] >>
  PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def] >>
  rw[hex_alt_def]
QED

val r = translate numposrepTheory.n2l_def;

Theorem n2l_side_thm[local]:
  ∀n m. n2l_side n m ⇔ n ≠ 0
Proof
  strip_tac >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[fetch "-" "n2l_side_def"] >>
  rw[]
QED

val _ = n2l_side_thm |> update_precondition;


val r = translate ASCIInumbersTheory.n2s_def;

Theorem n2s_side_thm[local]:
  ∀n f m. n2s_side n f m ⇔ n ≠ 0
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[fetch "-" "n2s_side_def"] >>
  rw[n2l_side_thm]
QED

val _ = n2s_side_thm |> update_precondition;


val r = translate num_to_hex_string_alt;

val r = translate num_to_hex_string_alt_intro;


val r = translate fromSexpTheory.encode_control_def;

val r = translate fromSexpTheory.SEXSTR_def;

val r = translate fromSexpTheory.litsexp_def;

Theorem litsexp_side_thm[local]:
  ∀v. litsexp_side v ⇔ T
Proof
  PURE_ONCE_REWRITE_TAC[fetch "-" "litsexp_side_def"] >> rw[]
  >> intLib.COOPER_TAC
QED

val _ = litsexp_side_thm |> update_precondition;

val r = translate fromSexpTheory.optsexp_def;
val r = translate fromSexpTheory.idsexp_def;
val r = translate fromSexpTheory.typesexp_def;
val r = translate fromSexpTheory.patsexp_def;
val r = translate fromSexpTheory.encode_thunk_mode_def;
val r = translate fromSexpTheory.prim_typesexp_def;
val r = translate fromSexpTheory.testsexp_def;
val r = translate fromSexpTheory.arithsexp_def;
val r = translate fromSexpTheory.opsexp_def;
val r = translate fromSexpTheory.logsexp_def;
val r = translate fromSexpTheory.expsexp_def;
val r = translate fromSexpTheory.type_defsexp_def;
val r = translate fromSexpTheory.decsexp_def;

(* Translating dafny_compilerTheory *)

val r = translate dafny_compilerTheory.compile_def;
val r = translate dafny_compilerTheory.dfy_to_cml_def;
val r = translate dafny_compilerTheory.unpack_def;
val r = translate dafny_compilerTheory.cmlm_to_str_def;

val r = translate dafny_compilerTheory.main_function_def;

(* Sanity checks + Finalizing *)

val _ = type_of "main_function" = ":mlsexp$sexp -> mlstring"
        orelse failwith "The main_function has the wrong type.";

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of \
                  \dafny_compilerTheory.main_function_def");

Quote main = cakeml:
  print (main_function (Sexp.parse (TextIO.openStdIn ())));
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => "^tm ++ ^main")
  |> EVAL |> concl |> rand;

Definition dafny_compiler_prog_def:
  dafny_compiler_prog = ^prog
End
