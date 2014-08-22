open preamble;
open intLib wordsLib bytecodeLabelsTheory;

val _ = new_theory "bytecodeEncode";

val bc_loc_to_string_def = Define `
(bc_loc_to_string (Lab n) = "lab " ++ toString n) ∧
(bc_loc_to_string (Addr n) = "addr " ++ toString n)`;

val int_to_string2_def = Define `
int_to_string2 z =
  if z < 0 then STRCAT "-" (toString (Num (-z))) else toString (Num z)`;

val bc_inst_to_string_def = Define `
(bc_inst_to_string (Stack Pop) = "pop") ∧
(bc_inst_to_string (Stack (Pops n)) = "pops " ++ toString n) ∧
(bc_inst_to_string (Stack (PushInt i)) = "pushInt " ++ int_to_string2 i) ∧
(bc_inst_to_string (Stack (Cons n1 n2)) = "cons " ++ toString n1 ++ " " ++ toString n2) ∧
(bc_inst_to_string (Stack (Cons2 n1)) = "cons2 " ++ toString n1) ∧
(bc_inst_to_string (Stack (Load n)) = "load " ++ toString n) ∧
(bc_inst_to_string (Stack (Store n)) = "store " ++ toString n) ∧
(bc_inst_to_string (Stack El) = "el") ∧
(bc_inst_to_string (Stack (TagEq n)) = "tagEq " ++ toString n) ∧
(bc_inst_to_string (Stack IsBlock) = "isBlock") ∧
(bc_inst_to_string (Stack LengthBlock) = "lengthBlock") ∧
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
(bc_inst_to_string CallPtr = "callPtr") ∧
(bc_inst_to_string (PushPtr l)= "pushPtr " ++ bc_loc_to_string l) ∧
(bc_inst_to_string Return = "return") ∧
(bc_inst_to_string PushExc = "pushExc") ∧
(bc_inst_to_string PopExc = "popExc") ∧
(bc_inst_to_string Ref = "ref") ∧
(bc_inst_to_string RefByte = "refByte") ∧
(bc_inst_to_string Deref = "deref") ∧
(bc_inst_to_string DerefByte = "derefByte") ∧
(bc_inst_to_string Update = "update") ∧
(bc_inst_to_string UpdateByte = "updateByte") ∧
(bc_inst_to_string Length = "length") ∧
(bc_inst_to_string LengthByte = "lengthByte") ∧
(bc_inst_to_string (Galloc n) = "galloc" ++ toString n) ∧
(bc_inst_to_string (Gupdate n) = "gupdate" ++ toString n) ∧
(bc_inst_to_string (Gread n) = "gread" ++ toString n) ∧
(bc_inst_to_string (Stop b) = "stop" ++ (if b then toString 1 else toString 0)) ∧
(bc_inst_to_string Tick = "tick") ∧
(bc_inst_to_string Print = "print") ∧
(bc_inst_to_string PrintWord8 = "printWord8") ∧
(bc_inst_to_string (PrintC c) = "printC '" ++ (if c = #"\n" then "\\n" else [c]) ++ "'")`;

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
(encode_bc_inst (Stack (PushInt i)) =
  if i < 0 then
    OPTION_MAP (\w. [3w; w]) (encode_num (Num (-i)))
  else
    OPTION_MAP (\w. [4w; w]) (encode_num (Num (i)))) ∧
(encode_bc_inst (Stack (Cons n1 n2)) =
  OPTION_BIND (encode_num n1) (\w1. OPTION_BIND (encode_num n2) (\w2. SOME [5w; w1; w2]))) ∧
(encode_bc_inst (Stack (Cons2 n1)) =
  OPTION_BIND (encode_num n1) (\w1. SOME [48w; w1])) ∧
(encode_bc_inst (Stack (Load n)) =
  OPTION_MAP (\w. [6w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (Store n)) =
  OPTION_MAP (\w. [7w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack (TagEq n)) =
  OPTION_MAP (\w. [10w; w]) (encode_num n)) ∧
(encode_bc_inst (Stack El) = SOME [47w]) ∧
(encode_bc_inst (Stack LengthBlock) = SOME [46w]) ∧
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
(encode_bc_inst CallPtr = SOME [27w]) ∧
(encode_bc_inst (PushPtr l) = encode_loc 28w l) ∧
(encode_bc_inst Return = SOME [30w]) ∧
(encode_bc_inst PushExc = SOME [31w]) ∧
(encode_bc_inst PopExc = SOME [32w]) ∧
(encode_bc_inst Ref = SOME [33w]) ∧
(encode_bc_inst RefByte = SOME [42w]) ∧
(encode_bc_inst Deref = SOME [34w]) ∧
(encode_bc_inst DerefByte = SOME [43w]) ∧
(encode_bc_inst Update = SOME [35w]) ∧
(encode_bc_inst UpdateByte = SOME [44w]) ∧
(encode_bc_inst Length = SOME [40w]) ∧
(encode_bc_inst LengthByte = SOME [41w]) ∧
(encode_bc_inst (Galloc n) = 
  OPTION_MAP (\w. [36w; w]) (encode_num n)) ∧
(encode_bc_inst (Gupdate n) =
  OPTION_MAP (\w. [37w; w]) (encode_num n)) ∧
(encode_bc_inst (Gread n) =
  OPTION_MAP (\w. [38w; w]) (encode_num n)) ∧
(encode_bc_inst (Stop b) = OPTION_MAP (\w. [39w; w]) (encode_num (if b then 1 else 0))) ∧
(encode_bc_inst Tick = SOME [8w]) ∧
(encode_bc_inst Print = SOME [26w]) ∧
(encode_bc_inst PrintWord8 = SOME [45w]) ∧
(encode_bc_inst (PrintC c) = 
  OPTION_MAP (\w. [2w; w]) (encode_char c))`;

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
         else if tag = 3w then
           option_map_fst (\n. Stack (PushInt (-&n))) (decode_num rest)
         else if tag = 4w then
           option_map_fst (\n. Stack (PushInt (&n))) (decode_num rest)
         else if tag = 48w then
           option_map_fst (\n. Stack (Cons2 (&n))) (decode_num rest)
         else if tag = 5w then
           OPTION_BIND (decode_num rest) (\(n1, rest). OPTION_BIND (decode_num rest) (\(n2, rest). SOME (Stack (Cons n1 n2), rest)))
         else if tag = 6w then
           option_map_fst (\n. Stack (Load n)) (decode_num rest)
         else if tag = 7w then
           option_map_fst (\n. Stack (Store n)) (decode_num rest)
         else if tag = 10w then
           option_map_fst (\n. Stack (TagEq n)) (decode_num rest)
         else if tag = 47w then
           SOME (Stack El, rest)
         else if tag = 46w then
           SOME (Stack LengthBlock, rest)
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
         else if tag = 42w then
           SOME (RefByte, rest)
         else if tag = 34w then
           SOME (Deref, rest)
         else if tag = 43w then
           SOME (DerefByte, rest)
         else if tag = 35w then
           SOME (Update, rest)
         else if tag = 44w then
           SOME (UpdateByte, rest)
         else if tag = 40w then
           SOME (Length, rest)
         else if tag = 41w then
           SOME (LengthByte, rest)
         else if tag = 36w then
           option_map_fst (\n. Galloc n) (decode_num rest)
         else if tag = 37w then
           option_map_fst (\n. Gupdate n) (decode_num rest)
         else if tag = 38w then
           option_map_fst (\n. Gread n) (decode_num rest)
         else if tag = 39w then
           option_map_fst (\n. Stop (0 < n)) (decode_num rest)
         else if tag = 8w then
           SOME (Tick, rest)
         else if tag = 26w then
           SOME (Print, rest)
         else if tag = 45w then
           SOME (PrintWord8, rest)
         else if tag = 2w then
           option_map_fst (\c. PrintC c) (decode_char rest)
         else
           NONE`;

val encode_bc_insts_def = Define `
(encode_bc_insts [] = SOME []) ∧
(encode_bc_insts (i::rest) =
  case encode_bc_inst i of
       NONE => NONE
     | SOME wl =>
         case encode_bc_insts rest of
              NONE => NONE
            | SOME wl' => SOME (wl++wl'))`;

val lem = Q.prove (
`!l. LENGTH l < SUC (LENGTH l) ∧ LENGTH l < SUC (SUC (LENGTH l)) ∧ LENGTH l < SUC (SUC (SUC (LENGTH l)))`,
decide_tac);

fun tzDefine s q = Lib.with_flag (computeLib.auto_import_definitions,false) (tDefine s q)
val decode_bc_insts_prim_def = tzDefine "decode_bc_insts" `
(decode_bc_insts [] = SOME []) ∧
(decode_bc_insts (wl:'a word list) =
  case decode_bc_inst wl of
       NONE => NONE
     | SOME (i,rest) =>
         if 48 < dimword (:'a) then
           case decode_bc_insts rest of
                NONE => NONE
              | SOME is => SOME (i::is)
         else
           NONE)`
(wf_rel_tac `measure LENGTH` >>
 rw [] >>
 fs [decode_bc_inst_def] >>
 rpt (full_case_tac
      >- (full_simp_tac (srw_ss()++ARITH_ss) [decode_num_def, option_map_fst_def, decode_char_def] >>
          every_case_tac >>
          TRY (PairCases_on `x`) >>
          rw [] >>
          fs [] >>
          every_case_tac >>
          rw [] >>
          fs [] >>
          rw [lem]) >>
      pop_assum  (fn _ => all_tac)) >>
 rw []);

val decode_bc_insts_def = Q.store_thm ("decode_bc_insts_def",
`(decode_bc_insts [] = SOME []) ∧
 (48 < dimword (:'a) ⇒
   (decode_bc_insts ((w:'a word)::wl) =
     case decode_bc_inst (w::wl) of
         NONE => NONE
       | SOME (i,rest) =>
           case decode_bc_insts rest of
                NONE => NONE
              | SOME is => SOME (i::is)))`,
 rw [decode_bc_insts_prim_def] >>
 every_case_tac >>
 fs [decode_bc_inst_def]);

val decode_encode_num = Q.prove (
`!n w l.
  (encode_num n = SOME w)
  ⇒
  (decode_num (w::l) = SOME (n,l))`,
 rw [encode_num_def, decode_num_def, UINT_MAX_def] >>
 rw [w2n_n2w] >>
 decide_tac);

val decode_encode_bc_inst = Q.store_thm ("decode_encode_bc_inst",
`48 < dimword (:'a)
 ⇒
 !inst (l1:'a word list) l2.
  (encode_bc_inst inst = SOME l1)
  ⇒
  (decode_bc_inst (l1 ++ l2) = SOME (inst, l2))`,
 strip_tac >>
 ho_match_mp_tac (fetch "-" "encode_bc_inst_ind") >>
 rw [encode_bc_inst_def, decode_bc_inst_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [option_map_fst_def] >>
 TRY (Cases_on `l`) >>
 full_simp_tac (srw_ss()++ARITH_ss)  [encode_loc_def, encode_char_def, decode_char_def] >>
 imp_res_tac decode_encode_num >>
 full_simp_tac (srw_ss()++ARITH_ss) []
 >- ARITH_TAC
 >- ARITH_TAC
 >- (pop_assum (assume_tac o Q.SPEC `[]`) >>
     full_simp_tac (srw_ss()++ARITH_ss)  [decode_num_def] >>
     rw [ORD_BOUND, CHR_ORD]));

val decode_encode_bc_insts = Q.store_thm ("decode_encode_bc_insts",
`48 < dimword (:'a)
 ⇒
 !(l1:'a word list) insts.
  (encode_bc_insts insts = SOME l1)
  ⇒
  (decode_bc_insts l1 = SOME insts)`,
 strip_tac >>
 ho_match_mp_tac (fetch "-" "decode_bc_insts_ind") >>
 rw [decode_bc_insts_def, encode_bc_insts_def] >>
 cases_on `insts` >>
 fs [decode_bc_insts_def, encode_bc_insts_def] >>
 every_case_tac >>
 rw [] >>
 imp_res_tac decode_encode_bc_inst
 >- (cases_on `h` >>
     fs [encode_bc_inst_def] >>
     TRY (cases_on `l`) >>
     TRY (cases_on `b`) >>
     fs [encode_bc_inst_def, encode_loc_def] >>
     every_case_tac >>
     fs []) >>
 metis_tac [optionTheory.SOME_11, optionTheory.NOT_SOME_NONE, PAIR_EQ]);

(* TODO: Incorporate the ideas in this email from Anthony Fox:
*
Not sure if this does what you’re after but it does demonstrate w2l and l2w (both defined in wordsTheory). The following defines two constants:

wordsToBytes: α word list -> word8 list

and

bytesToWords: word8 list -> α word list

Where α is expected to represent some multiple of 8.

(* ——————————————————————————————————————————*)

val wordToBytes_def = Define`
  wordToBytes (w:'a word) =
  MAP (n2w:num->word8) (PAD_RIGHT 0 (dimindex(:'a) DIV 8) (w2l 256 w))`

val wordsToBytes_def = Define `wordsToBytes = FLAT o MAP wordToBytes`

val SPLITN_def = tDefine "SPLITN"
 `(SPLITN a 0 l = []) /\
  (SPLITN a n [] = REVERSE a) /\
  (SPLITN a n l = SPLITN (TAKE n l :: a) n (DROP n l))`
  (WF_REL_TAC `measure (\(a,n,l). LENGTH l)` \\ simp [])

val bytesToWords_def = Define`
  bytesToWords (l: word8 list) =
  MAP (l2w 256) (SPLITN [] (dimindex(:'a) DIV 8) (MAP w2n l)) : 'a word list`;

(* ——————————————————————————————————————————*)

EVAL ``wordsToBytes ([0xFFEEDDCCAA998877w; 0x1122334455667788w]: word64 list)``;
val it =
  |- wordsToBytes [0xFFEEDDCCAA998877w; 0x1122334455667788w] =
  [119w; 136w; 153w; 170w; 204w; 221w; 238w; 255w; 136w; 119w; 102w;
   85w; 68w; 51w; 34w; 17w]:
  thm

EVAL ``bytesToWords (wordsToBytes ([0xFFEEDDCCAA998877w; 0x1122334455667788w]: word64 list)) : word64 list``;
val it =
  |- bytesToWords
    (wordsToBytes [0xFFEEDDCCAA998877w; 0x1122334455667788w]) =
  [0xFFEEDDCCAA998877w; 0x1122334455667788w]:
  thm



Of course, you can change the byte ordering by inserting “REVERSE” in where appropriate.
*) 


val _ = export_theory ();
