open preamble;
open intLib wordsLib unifyLib;
open astTheory initialEnvTheory lexer_implTheory;
open compilerTheory;
open compilerTerminationTheory;

val _ = new_theory "progToMc";

val get_all_asts_def = tDefine "get_all_asts" `
get_all_asts input =
  case lex_until_toplevel_semicolon input of
       NONE => Success []
     | SOME (tokens, rest_of_input) =>
        case parse_top tokens of
             NONE => Failure "<parse error>\n"
           | SOME top => 
               case get_all_asts rest_of_input of
                    Failure x => Failure x
                  | Success prog => Success (top::prog)`
(wf_rel_tac `measure LENGTH` >>
 rw [lex_until_toplevel_semicolon_LESS]);

val compile_def = Define `
compile p =
  case get_all_asts p of
       Failure x => Failure x
     | Success asts =>
         let (x,asts') = elab_prog init_type_bindings asts in
         case FST (infer_prog init_infer_decls [] init_tenvC init_type_env asts' infer$init_infer_state) of
              Failure x => Failure x
            | Success x =>
                let bc = compile_prog asts' in
                  Success bc`;

val _ = computeLib.add_funs [
  pat_bindings_def, 
  decLangTheory.prog_to_i3_def,
  CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook) compilerTerminationTheory.compile_def];

val _ = unifyLib.add_unify_compset (computeLib.the_compset)

val x = ``"val x = 1;"``

val x = ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val th = EVAL ``compile ^x``;

val _ = export_theory ();
