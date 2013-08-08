open wordsLib intLib;
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

(* TODO: Move the bytecode->string and encoder/decoder to the bytecode directory *)

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

val encode_num_def = Define `
encode_num n =
  if n < UINT_MAX (:'a) then
    SOME ((n2w n) : 'a word)
  else
    NONE`;

val encode_loc_def = Define `
(encode_loc tag (Lab n) = 
  OPTION_MAP (\w. [tag; w]) (encode_num n)) ∧
(encode_loc tag (Addr n) =
  OPTION_MAP (\w. [tag+1w; w]) (encode_num n))`;

val encode_char_def = Define `
encode_char c = encode_num (ORD c)`;

val encode_bc_inst_def = Define `
(encode_bc_inst (Stack Pop) = SOME [0w]) ∧
(encode_bc_inst (Stack (Pops n)) = 
  OPTION_MAP (\w. [1w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (Shift n1 n2)) = 
  OPTION_BIND (encode_num n1) (\w1. OPTION_BIND (encode_num n2) (\w2. SOME [2w; w1; w2]))) ∧
(encode_bc_inst (Stack (PushInt i)) = 
  if i < 0 then
    OPTION_MAP (\w. [3w; w]) (encode_num (Num (-i)))
  else
    OPTION_MAP (\w. [4w; w]) (encode_num (Num (i)))) ∧
(encode_bc_inst (Stack (Cons n1 n2)) =
  OPTION_BIND (encode_num n1) (\w1. OPTION_BIND (encode_num n2) (\w2. SOME [5w; w1; w2]))) ∧
(encode_bc_inst (Stack (Load n)) = 
  OPTION_MAP (\w. [6w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (Store n)) =
  OPTION_MAP (\w. [7w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (LoadRev n)) =
  OPTION_MAP (\w. [8w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (El n)) =
  OPTION_MAP (\w. [9w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (TagEq n)) =
  OPTION_MAP (\w. [10w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack IsBlock) = SOME [11w]) ∧
(encode_bc_inst (Stack Equal) = SOME [12w]) ∧
(encode_bc_inst (Stack Add) = SOME [13w]) ∧
(encode_bc_inst (Stack Sub) = SOME [14w]) ∧
(encode_bc_inst (Stack Mult) = SOME [15w]) ∧
(encode_bc_inst (Stack Div) = SOME [16w]) ∧
(encode_bc_inst (Stack Mod) = SOME [17w]) ∧
(encode_bc_inst (Stack Less) = SOME [18w]) ∧
(encode_bc_inst (Label n) =
  OPTION_MAP (\w. [19w; w]) (encode_num n)) ∧
(encode_bc_inst (Jump l) = encode_loc 20w l) ∧
(encode_bc_inst (JumpIf l) = encode_loc 22w l) ∧
(encode_bc_inst (Call l) = encode_loc 24w l) ∧
(encode_bc_inst JumpPtr = SOME [26w]) ∧
(encode_bc_inst CallPtr = SOME [27w]) ∧
(encode_bc_inst (PushPtr l) = encode_loc 28w l) ∧
(encode_bc_inst Return = SOME [30w]) ∧
(encode_bc_inst PushExc = SOME [31w]) ∧
(encode_bc_inst PopExc = SOME [32w]) ∧
(encode_bc_inst Ref = SOME [33w]) ∧
(encode_bc_inst Deref = SOME [34w]) ∧
(encode_bc_inst Update = SOME [35w]) ∧
(encode_bc_inst Stop = SOME [36w]) ∧
(encode_bc_inst Tick = SOME [37w]) ∧
(encode_bc_inst Print = SOME [38w]) ∧
(encode_bc_inst (PrintC c) = 
  OPTION_MAP (\w. [39w; w]) (encode_char c))`;

val decode_num_def = Define `
decode_num wl =
  case wl of
       [] => NONE
     | (w::rest) => SOME (w2n w, rest)`;

val decode_char_def = Define `
decode_char wl =
  case wl of
     | [] => NONE
     | (w::rest) =>
         if w2n w < 256 then
           SOME (CHR (w2n w), rest)
         else
           NONE`;

val option_map_fst_def = Define `
option_map_fst f x = 
  OPTION_MAP (\(x,y). (f x, y)) x`;

val decode_bc_inst_def = Define `
decode_bc_inst wl =
  case wl of
       [] => NONE
     | (tag::rest) =>
         if tag = 0w then
           SOME (Stack Pop, rest)
         else if tag = 1w then
           option_map_fst (\n. Stack (Pops n)) (decode_num rest)
         else if tag = 2w then
           OPTION_BIND (decode_num rest) (\(n1, rest). OPTION_BIND (decode_num rest) (\(n2, rest). SOME (Stack (Shift n1 n2), rest)))
         else if tag = 3w then
           option_map_fst (\n. Stack (PushInt (-&n))) (decode_num rest)
         else if tag = 4w then
           option_map_fst (\n. Stack (PushInt (&n))) (decode_num rest)
         else if tag = 5w then
           OPTION_BIND (decode_num rest) (\(n1, rest). OPTION_BIND (decode_num rest) (\(n2, rest). SOME (Stack (Cons n1 n2), rest)))
         else if tag = 6w then
           option_map_fst (\n. Stack (Load n)) (decode_num rest)
         else if tag = 7w then
           option_map_fst (\n. Stack (Store n)) (decode_num rest)
         else if tag = 8w then
           option_map_fst (\n. Stack (LoadRev n)) (decode_num rest)
         else if tag = 9w then
           option_map_fst (\n. Stack (El n)) (decode_num rest)
         else if tag = 10w then
           option_map_fst (\n. Stack (TagEq n)) (decode_num rest)
         else if tag = 11w then
           SOME (Stack IsBlock, rest)
         else if tag = 12w then
           SOME (Stack Equal, rest)
         else if tag = 13w then
           SOME (Stack Add, rest)
         else if tag = 14w then
           SOME (Stack Sub, rest)
         else if tag = 15w then
           SOME (Stack Mult, rest)
         else if tag = 16w then
           SOME (Stack Div, rest)
         else if tag = 17w then
           SOME (Stack Mod, rest)
         else if tag = 18w then
           SOME (Stack Less, rest)
         else if tag = 19w then
           option_map_fst Label (decode_num rest)
         else if tag = 20w then
           option_map_fst (\n. Jump (Lab n)) (decode_num rest)
         else if tag = 21w then
           option_map_fst (\n. Jump (Addr n)) (decode_num rest)
         else if tag = 22w then
           option_map_fst (\n. JumpIf (Lab n)) (decode_num rest)
         else if tag = 23w then
           option_map_fst (\n. JumpIf (Addr n)) (decode_num rest)
         else if tag = 24w then
           option_map_fst (\n. Call (Lab n)) (decode_num rest)
         else if tag = 25w then
           option_map_fst (\n. Call (Addr n)) (decode_num rest)
         else if tag = 26w then
           SOME (JumpPtr, rest)
         else if tag = 27w then
           SOME (CallPtr, rest)
         else if tag = 28w then
           option_map_fst (\n. PushPtr (Lab n)) (decode_num rest)
         else if tag = 29w then
           option_map_fst (\n. PushPtr (Addr n)) (decode_num rest)
         else if tag = 30w then
           SOME (Return, rest)
         else if tag = 31w then
           SOME (PushExc, rest)
         else if tag = 32w then
           SOME (PopExc, rest)
         else if tag = 33w then
           SOME (Ref, rest)
         else if tag = 34w then
           SOME (Deref, rest)
         else if tag = 35w then
           SOME (Update, rest)
         else if tag = 36w then
           SOME (Stop, rest)
         else if tag = 37w then
           SOME (Tick, rest)
         else if tag = 38w then
           SOME (Print, rest)
         else if tag = 39w then
           option_map_fst (\c. PrintC c) (decode_char rest)
         else
           NONE`;

val decode_encode_num = Q.prove (
`!n w l. 
  (encode_num n = SOME w)
  ⇒
  (decode_num (w::l) = SOME (n,l))`,
 rw [encode_num_def, decode_num_def, UINT_MAX_def] >>
 rw [w2n_n2w] >>
 decide_tac);

val decode_encode_bc_inst = Q.store_thm ("decode_encode_bc_inst",
`39 < dimword (:'a) 
 ⇒
 !inst (l1:'a word list) l2.
  (encode_bc_inst inst = SOME l1)
  ⇒
  (decode_bc_inst (l1 ++ l2) = SOME (inst, l2))`,
 strip_tac >>
 ho_match_mp_tac (fetch "-" "encode_bc_inst_ind") >>
 `0 < dimword (:'a) ∧
  1 < dimword (:'a) ∧
  2 < dimword (:'a) ∧
  3 < dimword (:'a) ∧
  4 < dimword (:'a) ∧
  5 < dimword (:'a) ∧
  6 < dimword (:'a) ∧
  7 < dimword (:'a) ∧
  8 < dimword (:'a) ∧
  9 < dimword (:'a) ∧
  10 < dimword (:'a) ∧
  11 < dimword (:'a) ∧
  12 < dimword (:'a) ∧
  13 < dimword (:'a) ∧
  14 < dimword (:'a) ∧
  15 < dimword (:'a) ∧
  16 < dimword (:'a) ∧
  17 < dimword (:'a) ∧
  18 < dimword (:'a) ∧
  19 < dimword (:'a) ∧
  20 < dimword (:'a) ∧
  21 < dimword (:'a) ∧
  22 < dimword (:'a) ∧
  23 < dimword (:'a) ∧
  24 < dimword (:'a) ∧
  25 < dimword (:'a) ∧
  26 < dimword (:'a) ∧
  27 < dimword (:'a) ∧
  28 < dimword (:'a) ∧
  29 < dimword (:'a) ∧
  30 < dimword (:'a) ∧
  31 < dimword (:'a) ∧
  32 < dimword (:'a) ∧
  33 < dimword (:'a) ∧
  34 < dimword (:'a) ∧
  35 < dimword (:'a) ∧
  36 < dimword (:'a) ∧
  37 < dimword (:'a) ∧
  38 < dimword (:'a) ∧
  39 < dimword (:'a)`
          by decide_tac >>
 rw [encode_bc_inst_def, decode_bc_inst_def] >>
 fs [option_map_fst_def] >>
 TRY (Cases_on `l`) >>
 fs [encode_loc_def, encode_char_def, decode_char_def] >>
 imp_res_tac decode_encode_num >>
 fs []
 >- ARITH_TAC
 >- ARITH_TAC
 >- (pop_assum (assume_tac o Q.SPEC `[]`) >>
     fs [decode_num_def] >>
     rw [ORD_BOUND, CHR_ORD]));
   
val whole_prog_compile_def = Define`
  whole_prog_compile input = 
    case wp_main_loop initial_repl_fun_state input of
         Failure error_msg => "<error>: " ++ error_msg ++ "\n"
       | Success code => FLAT (MAP (\inst. bc_inst_to_string inst ++ "\n") code)`;

val _ = export_theory ();
