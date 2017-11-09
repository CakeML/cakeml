open preamble
     ml_translatorLib ml_progLib ml_translatorTheory
     ArrayProgTheory basisFunctionsLib

val _ = new_theory "CommandlineProg";

val _ = translation_extends "ArrayProg";

val _ = option_monadsyntax.temp_add_option_monadsyntax();

val _ = ml_prog_update (open_module "Commandline")
val e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "cl_state" e) "cl_state" [])

val e = process_topdecs`
  fun cline u =
    let
      val cs = Word8Array.array 256 (Word8.fromInt 0)
      val u = #(getArgs) "" cs
      fun f x = (Char.ord x = 0)
    in String.tokens f (Word8Array.substring cs 0 256) end`;
val _ = append_prog e;

val _ = (append_prog o process_topdecs) `fun name u = List.hd (cline ())`

val _ = (append_prog o process_topdecs) `fun arguments u = List.tl (cline ())`

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
