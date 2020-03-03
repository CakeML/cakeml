(*
  Module about CakeML assertions
*)
open preamble ml_translatorLib ml_progLib RuntimeProgTheory basisFunctionsLib;

val _ = new_theory "AssertProg";

val _ = translation_extends "RuntimeProg";

val _ = ml_prog_update (open_module "Assert");

val _ = process_topdecs `
  fun assert cond msg =
  if (cond)
  then ()
  else (Runtime.debugMsg (String.^ ("Assertion Failure:") (msg));
        Runtime.abort());`
  |> append_prog;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
