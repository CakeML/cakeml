open preamble;
open intLib wordsLib unifyLib;
open astTheory initialEnvTheory lexer_implTheory;
open terminationTheory;
open compilerTheory initialProgramTheory;
open compilerTerminationTheory bytecodeEncodeTheory;

val _ = new_theory "progToBytecode";

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

val elab_all_asts_def = Define `
elab_all_asts asts =
  case asts of 
     | Failure x => Failure x
     | Success asts =>
         Success (SND (elab_prog init_type_bindings asts))`;

val infer_all_asts_def = Define `
infer_all_asts asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         case FST (infer_prog init_infer_decls [] init_tenvC init_type_env asts infer$init_infer_state) of
            | Failure x => Failure x
            | Success x => Success asts`; 

val compile_all_asts_def = Define `
compile_all_asts asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         Success (compile_prog (Tdec initial_program::asts))`;

val compile_all_asts_no_init_def = Define `
compile_all_asts_no_init asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         Success (compile_prog asts)`;

val remove_labels_all_asts_def = Define `
remove_labels_all_asts len asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         Success (code_labels len asts)`;

val all_asts_to_string_def = Define `
all_asts_to_string asts =
  case asts of
     | Failure x => Failure x
     | Success bcs => Success (FLAT (MAP (\inst. bc_inst_to_string inst ++ "\n") bcs))`;

val all_asts_to_encoded_def = Define `
all_asts_to_encoded asts =
  case asts of
     | Failure x => Failure x
     | Success bcs => Success (encode_bc_insts bcs : word64 list option)`;

val prog_to_bytecode_def = Define `
prog_to_bytecode len p =
  remove_labels_all_asts len (compile_all_asts (infer_all_asts (elab_all_asts (get_all_asts p))))`;

val prog_to_bytecode_string_def = Define `
prog_to_bytecode_string len p =
  all_asts_to_string (prog_to_bytecode len p)`;

val prog_to_bytecode_encoded_def = Define `
prog_to_bytecode_encoded len p =
  case prog_to_bytecode len p of
     | Failure x => Failure x
     | Success bcs => Success (encode_bc_insts bcs : word64 list option)`;

val _ = export_theory ();
