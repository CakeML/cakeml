open preamble;
open intLib wordsLib unifyLib;
open astTheory initialEnvTheory lexer_implTheory;
open intLang1Theory intLang2Theory intLang3Theory intLang4Theory;

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
                let (x,y,z,asts_i1) = prog_to_i1 0 FEMPTY (FEMPTY |++ alloc_defs 0 (MAP FST init_env)) asts' in
                let (x,asts_i2) = prog_to_i2 init_tagenv_state asts_i1 in
                let (x,asts_i3) = prog_to_i3 0 asts_i2 in
                let asts_i4 = MAP (exp_to_i4 []) asts_i3 in
                  Success asts_i4`;

val _ = computeLib.add_funs [pat_bindings_def, intLang3Theory.prog_to_i3_def];
val _ = unifyLib.add_unify_compset (computeLib.the_compset)

val x = ``"val x = 1;"``

val x = ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

EVAL ``compile ^x``;

val _ = export_theory ();
