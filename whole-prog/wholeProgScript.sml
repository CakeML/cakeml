open preamble;
open lexer_implTheory replTheory;

val _ = new_theory "wholeProg";

val tac = (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lex_until_toplevel_semicolon_LESS);

val wp_main_loop_def = tDefine "wp_main_loop" `
  wp_main_loop s input =
    case lex_until_toplevel_semicolon input of
      (* case: no semicolon found, i.e. trailing characters then end of input *)
      NONE => Success []
    | (* case: tokens for next top have been read, now eval-print-and-loop *)
      SOME (tokens, rest_of_input) =>
        case parse_elaborate_infertype_compile tokens s of
          (* case: cannot turn into code, print error message, continue *)
          Failure error_msg => Failure error_msg
        | (* case: new code generated, install, run, print and continue *)
          Success (code,s,s_exc) =>
            case wp_main_loop s rest_of_input of
                 Failure error_msg => Failure error_msg
               | Success code' => Success (code ++ code')` tac;

val bc_loc_to_string_def = Define `
(bc_loc_to_string (Lab n) = "lab " ++ toString n) ∧
(bc_loc_to_string (Addr n) = "addr " ++ toString n)`;

val bc_inst_to_string_def = Define `
(bc_inst_to_string (Stack Pop) = "pop") ∧
(bc_inst_to_string (Stack (Pops n)) = "pops " ++ toString n) ∧
(bc_inst_to_string (Stack (Shift n1 n2)) = "shift " ++ toString n1 ++ " " ++ toString n2) ∧
(bc_inst_to_string (Stack (PushInt i)) = "pushInt " ++ int_to_string i) ∧
(bc_inst_to_string (Stack (Cons n1 n2)) = "cons " ++ toString n1 ++ " " ++ toString n2) ∧
(bc_inst_to_string (Stack (Load n)) = "load " ++ toString n) ∧
(bc_inst_to_string (Stack (Store n)) = "store " ++ toString n) ∧
(bc_inst_to_string (Stack (LoadRev n)) = "loadRev " ++ toString n) ∧
(bc_inst_to_string (Stack (El n)) = "el " ++ toString n) ∧
(bc_inst_to_string (Stack (TagEq n)) = "tagEq " ++ toString n) ∧
(bc_inst_to_string (Stack IsBlock) = "isBlock") ∧
(bc_inst_to_string (Stack Equal) = "=") ∧
(bc_inst_to_string (Stack Add) = "+") ∧
(bc_inst_to_string (Stack Sub) = "-") ∧
(bc_inst_to_string (Stack Mult) = "*") ∧
(bc_inst_to_string (Stack Div) = "/") ∧
(bc_inst_to_string (Stack Mod) = "%") ∧
(bc_inst_to_string (Stack Less) = "<") ∧
(bc_inst_to_string (Label n) = "label " ++ toString n) ∧
(bc_inst_to_string (Jump l) = "jump " ++ bc_loc_to_string l) ∧
(bc_inst_to_string (JumpIf l) = "jumpIf " ++ bc_loc_to_string l) ∧
(bc_inst_to_string (Call l) = "call " ++ bc_loc_to_string l) ∧
(bc_inst_to_string JumpPtr = "jumpPtr") ∧
(bc_inst_to_string CallPtr = "callPtr") ∧
(bc_inst_to_string (PushPtr l)= "pushPtr " ++ bc_loc_to_string l) ∧
(bc_inst_to_string Return = "return") ∧
(bc_inst_to_string PushExc = "pushExc") ∧
(bc_inst_to_string PopExc = "popExc") ∧
(bc_inst_to_string Ref = "ref") ∧
(bc_inst_to_string Deref = "deref") ∧
(bc_inst_to_string Update = "update") ∧
(bc_inst_to_string Stop = "stop") ∧
(bc_inst_to_string Tick = "tick") ∧
(bc_inst_to_string Print = "print") ∧
(bc_inst_to_string (PrintC c) = "printC '" ++ [c] ++ "'")`;

val whole_prog_compile_def = Define`
  whole_prog_compile input = 
    case wp_main_loop initial_repl_fun_state input of
         Failure error_msg => "<error>: " ++ error_msg ++ "\n"
       | Success code => FLAT (MAP (\inst. bc_inst_to_string inst ++ "\n") code)`;

val _ = export_theory ();
