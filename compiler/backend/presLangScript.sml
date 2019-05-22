(*
  Functions for converting various intermediate languages
  into displayLang representations.
*)
open preamble astTheory mlintTheory
open flatLangTheory patLangTheory closLangTheory
     displayLangTheory source_to_flatTheory
     wordLangTheory;

val _ = new_theory"presLang";

(* basics *)

val empty_item_def = Define`
  empty_item name = Item NONE name []`;

val string_to_display_def = Define`
  string_to_display s = empty_item (concat [strlit "\""; s; strlit "\""])`;

val string_to_display2_def = Define`
  string_to_display2 s = string_to_display (implode s)`;

val num_to_display_def = Define`
  num_to_display (n : num) = string_to_display (toString n)`;

val item_with_num_def = Define`
  item_with_num name n = Item NONE name [num_to_display n]`;

val item_with_nums_def = Define`
  item_with_nums name ns = Item NONE name (MAP num_to_display ns)`;

val bool_to_display_def = Define`
  bool_to_display b = empty_item (if b then strlit "True" else strlit "False")`;

val num_to_hex_digit_def = Define `
  num_to_hex_digit n =
    if n < 10 then [CHR (48 + n)] else
    if n < 16 then [CHR (55 + n)] else []`;

val num_to_hex_def = Define `
  num_to_hex n =
    (if n < 16 then [] else num_to_hex (n DIV 16)) ++
    num_to_hex_digit (n MOD 16)`;

(* num_to_hex "implements" words$word_to_hex_string in a
   simple way that the translator can handle. these lemmas
   check that is true. *)
Theorem num_to_hex_digit_eq:
   !i. i < 16 ==> num_to_hex_digit i = [HEX i]
Proof
  CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL))
  \\ simp []
QED

Theorem num_to_hex_eq:
   num_to_hex (w2n w) = words$word_to_hex_string w
Proof
  simp [wordsTheory.word_to_hex_string_def, wordsTheory.w2s_def]
  \\ Q.SPEC_TAC (`w2n w`, `n`)
  \\ measureInduct_on `I n`
  \\ simp [Once numposrepTheory.n2l_def, ASCIInumbersTheory.n2s_def]
  \\ simp [Once num_to_hex_def, num_to_hex_digit_eq]
  \\ (PURE_CASE_TAC \\ simp[ASCIInumbersTheory.n2s_def])
QED

val display_word_to_hex_string_def = Define `
  display_word_to_hex_string w =
    empty_item (implode ("0x" ++ num_to_hex (w2n w)))`;

val lit_to_display_def = Define`
  (lit_to_display (IntLit i) =
    Item NONE (strlit "IntLit") [empty_item (toString i)])
  /\
  (lit_to_display (Char c) =
    Item NONE (strlit "Char") [empty_item (implode ("#\"" ++ [c] ++ "\""))])
  /\
  (lit_to_display (StrLit s) =
    Item NONE (strlit "StrLit") [string_to_display2 s])
  /\
  (lit_to_display (Word8 w) =
    Item NONE (strlit "Word8") [display_word_to_hex_string w])
  /\
  (lit_to_display (Word64 w) =
    Item NONE (strlit "Word64") [display_word_to_hex_string w])`;

val list_to_display_def = Define`
  (list_to_display f xs = displayLang$List (MAP f xs))`

val option_to_display_def = Define`
  (option_to_display f opt = case opt of
          | NONE => empty_item (strlit "NONE")
          | SOME opt' => Item NONE (strlit "SOME") [f opt'])`

(* semantic ops and values *)

val fp_cmp_to_display_def = Define `
  fp_cmp_to_display cmp = case cmp of
    | FP_Less => empty_item (strlit "FP_Less")
    | FP_LessEqual => empty_item (strlit "FP_LessEqual")
    | FP_Greater => empty_item (strlit "FP_Greater")
    | FP_GreaterEqual => empty_item (strlit "FP_GreaterEqual")
    | FP_Equal => empty_item (strlit "FP_Equal")`

val fp_uop_to_display_def = Define `
  fp_uop_to_display op = case op of
    | FP_Abs => empty_item (strlit "FP_Abs")
    | FP_Neg => empty_item (strlit "FP_Neg")
    | FP_Sqrt => empty_item (strlit "FP_Sqrt")`

val fp_bop_to_display_def = Define `
  fp_bop_to_display op = case op of
    | fpSem$FP_Add => empty_item (strlit "FP_Add")
    | FP_Sub => empty_item (strlit "FP_Sub")
    | FP_Mul => empty_item (strlit "FP_Mul")
    | FP_Div => empty_item (strlit "FP_Div")`

val fp_top_to_display_def = Define `
  fp_top_to_display op =
    case op of
      |FP_Fma => empty_item (strlit "FP_Fma")`

val word_size_to_display_def = Define`
  (word_size_to_display W8 = empty_item (strlit "W8"))
  /\
  (word_size_to_display W64 = empty_item (strlit "W64"))`;

val opn_to_display_def = Define`
  (opn_to_display Plus = empty_item (strlit "Plus"))
  /\
  (opn_to_display Minus = empty_item (strlit "Minus"))
  /\
  (opn_to_display Times = empty_item (strlit "Times"))
  /\
  (opn_to_display Divide = empty_item (strlit "Divide"))
  /\
  (opn_to_display Modulo = empty_item (strlit "Modulo"))`;

val opb_to_display_def = Define`
  (opb_to_display Lt = empty_item (strlit "Lt"))
  /\
  (opb_to_display Gt = empty_item (strlit "Gt"))
  /\
  (opb_to_display Leq = empty_item (strlit "Leq"))
  /\
  (opb_to_display Geq = empty_item (strlit "Geq"))`;

val opw_to_display_def = Define`
  (opw_to_display Andw = empty_item (strlit "Andw"))
  /\
  (opw_to_display Orw = empty_item (strlit "Orw"))
  /\
  (opw_to_display Xor = empty_item (strlit "Xor"))
  /\
  (opw_to_display Add = empty_item (strlit "Add"))
  /\
  (opw_to_display Sub = empty_item (strlit "Sub"))`;

val shift_to_display_def = Define`
  (shift_to_display Lsl = empty_item (strlit "Lsl"))
  /\
  (shift_to_display Lsr = empty_item (strlit "Lsr"))
  /\
  (shift_to_display Asr = empty_item (strlit "Asr"))
  /\
  (shift_to_display Ror = empty_item (strlit "Ror"))`;


 (* flatLang *)

val MEM_pat_size = prove(
  ``!pats a. MEM a (pats:flatLang$pat list) ==> pat_size a < pat1_size pats``,
  Induct \\ rw [] \\ rw [flatLangTheory.pat_size_def] \\ res_tac \\ fs []);

val opt_con_to_display_def = Define `
  opt_con_to_display ocon = case ocon of
    | NONE => empty_item (strlit "ConIdNone")
    | SOME (c, NONE) => item_with_num (strlit "ConIdUntyped") c
    | SOME (c, SOME t) => item_with_nums (strlit "ConIdTyped") [c; t]`

val flat_pat_to_display_def = tDefine "flat_pat_to_display" `
  flat_pat_to_display p =
    case p of
       | flatLang$Pvar varN => Item NONE (strlit "Pvar")
            [string_to_display2 varN]
       | Pany => empty_item (strlit "Pany")
       | Plit lit => Item NONE (strlit "Plit") [lit_to_display lit]
       | flatLang$Pcon id pats => Item NONE (strlit "Pcon")
            (MAP flat_pat_to_display pats)
       | Pref pat => Item NONE (strlit "Pref") [flat_pat_to_display pat] `
  (WF_REL_TAC `measure pat_size` \\ rw []
   \\ imp_res_tac MEM_pat_size \\ fs [])

val flat_op_to_display_def = Define `
  flat_op_to_display op = case op of
    | Opn op => opn_to_display op
    | Opb op => opb_to_display op
    | Opw ws op =>
        Item NONE (strlit "Opw") [ word_size_to_display ws; opw_to_display op ]
    | Shift ws sh num => Item NONE (strlit "Shift") [
      word_size_to_display ws;
      shift_to_display sh;
      num_to_display num
    ]
    | Equality => empty_item (strlit "Equality")
    | FP_cmp cmp => fp_cmp_to_display cmp
    | FP_uop op => fp_uop_to_display op
    | FP_bop op => fp_bop_to_display op
    | FP_top op => fp_top_to_display op
    | Opapp => empty_item (strlit "Opapp")
    | Opassign => empty_item (strlit "Opassign")
    | Opref => empty_item (strlit "Opref")
    | Opderef => empty_item (strlit "Opderef")
    | Aw8alloc => empty_item (strlit "Aw8alloc")
    | Aw8sub => empty_item (strlit "Aw8sub")
    | Aw8length => empty_item (strlit "Aw8length")
    | Aw8update => empty_item (strlit "Aw8update")
    | WordFromInt ws =>
        Item NONE (strlit "WordFromInt") [word_size_to_display ws]
    | WordToInt ws =>
        Item NONE (strlit "WordToInt") [word_size_to_display ws]
    | CopyStrStr => empty_item (strlit "CopyStrStr")
    | CopyStrAw8 => empty_item (strlit "CopyStrAw8")
    | CopyAw8Str => empty_item (strlit "CopyAw8Str")
    | CopyAw8Aw8 => empty_item (strlit "CopyAw8Aw8")
    | Ord => empty_item (strlit "Ord")
    | Chr => empty_item (strlit "Chr")
    | Chopb op => Item NONE (strlit "Chopb") [opb_to_display op]
    | Implode => empty_item (strlit "Implode")
    | Strsub => empty_item (strlit "Strsub")
    | Strlen => empty_item (strlit "Strlen")
    | Strcat => empty_item (strlit "Strcat")
    | VfromList => empty_item (strlit "VfromList")
    | Vsub => empty_item (strlit "Vsub")
    | Vlength => empty_item (strlit "Vlength")
    | Aalloc => empty_item (strlit "Aalloc")
    | Asub => empty_item (strlit "Asub")
    | Alength => empty_item (strlit "Alength")
    | Aupdate => empty_item (strlit "Aupdate")
    | ListAppend => empty_item (strlit "ListAppend")
    | ConfigGC => empty_item (strlit "ConfigGC")
    | FFI s => Item NONE (strlit "FFI") [string_to_display2 s]
    | GlobalVarAlloc n => item_with_num (strlit "GlobalVarAlloc") n
    | GlobalVarInit n => item_with_num (strlit "GlobalVarInit") n
    | GlobalVarLookup n => item_with_num (strlit "GlobalVarLookup") n
    `

val MEM_funs_size = prove(
  ``!fs v1 v2 e. MEM (v1,v2,e) fs ==> flatLang$exp_size e < exp1_size fs``,
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []);

val MEM_exps_size = prove(
  ``!exps e. MEM e exps ==> flatLang$exp_size e < exp6_size exps``,
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []);

val MEM_pats_size = prove(
  ``!pats p e. MEM (p, e) pats ==> flatLang$exp_size e < exp3_size pats``,
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []);

val flat_to_display_def = tDefine"flat_to_display" `
  (flat_to_display (flatLang$Raise tra exp) =
    Item (SOME tra) (strlit "Raise") [flat_to_display exp])
  /\
  (flat_to_display (Handle tra exp pes) =
    Item (SOME tra) (strlit "Handle") (flat_to_display exp
        :: MAP (\(pat,exp). displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp]) pes))
  /\
  (flat_to_display (Lit tra lit) = Item (SOME tra) (strlit "Lit") [])
  /\
  (flat_to_display (flatLang$Con tra id_opt exps) =
    Item (SOME tra) (strlit "Con") (opt_con_to_display id_opt
        :: MAP flat_to_display exps))
  /\
  (flat_to_display (Var_local tra varN) =
    Item (SOME tra) (strlit "Var_local") [string_to_display2 varN])
  /\
  (flat_to_display (Fun tra varN exp) =
    Item (SOME tra) (strlit "Fun") [string_to_display2 varN; flat_to_display exp])
  /\
  (flat_to_display (App tra op exps) =
    Item (SOME tra) (strlit "App") (flat_op_to_display op :: MAP flat_to_display exps))
  /\
  (flat_to_display (If tra exp1 exp2 exp3) =
    Item (SOME tra) (strlit "If") [flat_to_display exp1; flat_to_display exp2;
        flat_to_display exp3])
  /\
  (flat_to_display (Mat tra exp pes) =
    Item (SOME tra) (strlit "Mat") (flat_to_display exp
        :: MAP (\(pat,exp). displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp]) pes))
  /\
  (flat_to_display (Let tra varN_opt exp1 exp2) =
    Item (SOME tra) (strlit "Let") [option_to_display string_to_display2 varN_opt;
        flat_to_display exp1; flat_to_display exp2])
  /\
  (flat_to_display (Letrec tra funs exp) =
    Item (SOME tra) (strlit "Letrec")
        [List (MAP (\(v1,v2,e). Tuple [string_to_display2 v1; string_to_display2 v2;
              flat_to_display e]) funs); flat_to_display exp]
  )`
  (WF_REL_TAC `inv_image $< (flatLang$exp_size)`
   \\ rw [flatLangTheory.exp_size_def]
   \\ imp_res_tac MEM_funs_size \\ fs []
   \\ imp_res_tac MEM_exps_size \\ fs []
   \\ imp_res_tac MEM_pats_size \\ fs []
);

val flat_to_display_dec_def = Define`
  flat_to_display_dec d =
    case d of
       | Dlet exp => Item NONE (strlit "Dlet") [flat_to_display exp]
       | Dtype mods con_arities => item_with_num (strlit "Dtype") mods
       | Dexn n1 n2 => item_with_nums (strlit "Dexn") [n1; n2]`

val flat_to_display_decs_def = Define`
  flat_to_display_decs = list_to_display flat_to_display_dec`;

(* pat to displayLang *)

val num_to_varn_def = tDefine "num_to_varn" `
  num_to_varn n = if n < 26 then [CHR (97 + n)]
                  else (num_to_varn ((n DIV 26)-1)) ++ ([CHR (97 + (n MOD 26))])`
  (WF_REL_TAC `measure I` \\ rw [] \\ fs [DIV_LT_X]);

val display_num_as_varn_def = Define `
  display_num_as_varn n = string_to_display2 (num_to_varn n)`;

val pat_op_to_display_def = Define `
  pat_op_to_display op = case op of
    | patLang$Op op2 => flat_op_to_display op2
    | Run => empty_item (strlit "Run")
    | Tag_eq n1 n2 => item_with_nums (strlit "Tag_eq") [n1; n2]
    | El num => item_with_num (strlit "El") num
  `

val MEM_pat_exps_size = prove(
  ``!exps e. MEM a exps ==> patLang$exp_size a < exp1_size exps``,
  Induct \\ fs [patLangTheory.exp_size_def] \\ rw []
  \\ fs [patLangTheory.exp_size_def] \\ res_tac \\ fs []);

(* The constructors in pat differ a bit because of de bruijn indices. This is
* solved with the argument h, referring to head of our indexing. Combined with
* num_to_varn this means we create varNs to match the presLang-constructors
* where either nums or no name at all were provided. *)

val pat_to_display_def = tDefine "pat_to_display" `
  (pat_to_display h (patLang$Raise t e) =
    Item (SOME t) (strlit "Raise") [pat_to_display h e])
  /\
  (pat_to_display h (Handle t e1 e2) =
    Item (SOME t) (strlit "Handle")
        [pat_to_display h e1; pat_to_display (h+1) e2])
  /\
  (pat_to_display h (Lit t lit) =
    Item (SOME t) (strlit "Lit") [lit_to_display lit])
  /\
  (pat_to_display h (Con t num es) =
    Item (SOME t) (strlit "Con") (num_to_display num :: MAP (pat_to_display h) es))
  /\
  (pat_to_display h (Var_local t var_index) =
    Item (SOME t) (strlit "Var_local") [display_num_as_varn (h-var_index-1)])
  /\
  (pat_to_display h (Fun t e) =
    Item (SOME t) (strlit "Fun") [display_num_as_varn h; pat_to_display (h+1) e])
  /\
  (pat_to_display h (App t op es) =
    Item (SOME t) (strlit "App") (pat_op_to_display op :: MAP (pat_to_display h) es))
  /\
  (pat_to_display h (If t e1 e2 e3) =
    Item (SOME t) (strlit "If") [pat_to_display h e1; pat_to_display h e2;
        pat_to_display h e3])
  /\
  (pat_to_display h (Let t e1 e2) =
    Item (SOME t) (strlit "Let") [display_num_as_varn h;
        pat_to_display h e1; pat_to_display (h+1) e2])
  /\
  (pat_to_display h (Seq t e1 e2) =
    Item (SOME t) (strlit "Seq") [pat_to_display h e1; pat_to_display h e2])
  /\
  (pat_to_display h (Letrec t es e) =
    (let len = LENGTH es in Item (SOME t) (strlit "Letrec")
        [List (pat_to_display_rec_tups h (len-1) len es);
            pat_to_display (h+len) e]))
  /\
  (* Gives letrec functions names and variable names. *)
  (pat_to_display_rec_tups _ _ _ [] = [])
  /\
  (pat_to_display_rec_tups h i len (e::es) =
    Tuple [display_num_as_varn (h+i); display_num_as_varn (h+len);
        pat_to_display (h+len+1) e]
        :: pat_to_display_rec_tups h (i-1) len es)`
 (WF_REL_TAC `measure (\x. case x of INL (_,e) => exp_size e
                                   | INR (_,_,_,es) => exp1_size es)`
  \\ rw [patLangTheory.exp_size_def]
  \\ imp_res_tac MEM_pat_exps_size \\ fs []);

(* clos to displayLang *)

val num_to_varn_list_def = Define `
  num_to_varn_list h n =
    if n = 0 then [] else
      num_to_varn (h + n) :: num_to_varn_list h (n-1)`

val clos_op_to_display_def = Define `
  clos_op_to_display op = case op of
    | Global num => item_with_num (strlit "Global") num
    | SetGlobal num => item_with_num (strlit "SetGlobal") num
    | AllocGlobal => empty_item (strlit "AllocGlobal")
    | GlobalsPtr => empty_item (strlit "GlobalsPtr")
    | SetGlobalsPtr => empty_item (strlit "SetGlobalsPtr")
    | Cons num => item_with_num (strlit "Cons") num
    | ConsExtend num => item_with_num (strlit "ConsExtend") num
    | El => empty_item (strlit "El")
    | LengthBlock => empty_item (strlit "LengthBlock")
    | Length => empty_item (strlit "Length")
    | LengthByte => empty_item (strlit "LengthByte")
    | RefByte b => Item NONE (strlit "RefByte") [bool_to_display b]
    | RefArray => empty_item (strlit "RefArray")
    | DerefByte => empty_item (strlit "DerefByte")
    | UpdateByte => empty_item (strlit "UpdateByte")
    | ConcatByteVec => empty_item (strlit "ConcatByteVec")
    | CopyByte b => Item NONE (strlit "CopyByte") [bool_to_display b]
    | ListAppend => empty_item (strlit "ListAppend")
    | FromList num => item_with_num (strlit "FromList") num
    | closLang$String s => Item NONE (strlit "String") [string_to_display2 s]
    | FromListByte => empty_item (strlit "FromListByte")
    | LengthByteVec => empty_item (strlit "LengthByteVec")
    | DerefByteVec => empty_item (strlit "DerefByteVec")
    | TagLenEq n1 n2 => item_with_nums (strlit "TagLenEq") [n1; n2]
    | TagEq num => item_with_num (strlit "TagEq") num
    | Ref => empty_item (strlit "Ref")
    | Deref => empty_item (strlit "Deref")
    | Update => empty_item (strlit "Update")
    | Label num => item_with_num (strlit "Label") num
    | FFI s => Item NONE (strlit "FFI") [string_to_display2 s]
    | Equal => empty_item (strlit "Equal")
    | EqualInt i => empty_item (strlit "EqualIntWithMissingData")
    | Const i => empty_item (strlit "ConstWithMissingData")
    | Add => empty_item (strlit "Add")
    | Sub => empty_item (strlit "Sub")
    | Mult => empty_item (strlit "Mult")
    | Div => empty_item (strlit "Div")
    | Mod => empty_item (strlit "Mod")
    | Less => empty_item (strlit "Less")
    | LessEq => empty_item (strlit "LessEq")
    | Greater => empty_item (strlit "Greater")
    | GreaterEq => empty_item (strlit "GreaterEq")
    | WordOp ws op =>
        Item NONE (strlit "WordOp") [ word_size_to_display ws; opw_to_display op ]
    | WordShift ws sh num => Item NONE (strlit "WordShift") [
      word_size_to_display ws;
      shift_to_display sh;
      num_to_display num
    ]
    | WordFromInt => empty_item (strlit "WordFromInt")
    | WordToInt => empty_item (strlit "WordToInt")
    | WordFromWord b => Item NONE (strlit "WordFromWord") [bool_to_display b]
    | FP_cmp cmp => fp_cmp_to_display cmp
    | FP_uop op => fp_uop_to_display op
    | FP_bop op => fp_bop_to_display op
    | FP_top op => fp_top_to_display op
    | BoundsCheckBlock => empty_item (strlit "BoundsCheckBlock")
    | BoundsCheckArray => empty_item (strlit "BoundsCheckArray")
    | BoundsCheckByte b => Item NONE (strlit "BoundsCheckByte") [bool_to_display b]
    | LessConstSmall num => item_with_num (strlit "LessConstSmall") num
    | closLang$ConfigGC => empty_item (strlit "ConfigGC")
    | Install => empty_item (strlit "Install")
`

val MEM_clos_exps_size = prove(
  ``!exps e. MEM e exps ==> closLang$exp_size e < exp3_size exps``,
  Induct \\ fs [closLangTheory.exp_size_def] \\ rw []
  \\ fs [closLangTheory.exp_size_def] \\ res_tac \\ fs []);

(* The clos_to_display function uses the same approach to de bruijn
   indices as the pat_to_display function *)
val clos_to_display_def = tDefine "clos_to_display" `
  (clos_to_display h (Var t n) =
    Item (SOME t) (strlit "Var") [display_num_as_varn (h-n-1)]) /\
  (clos_to_display h (If t x1 x2 x3) =
    Item (SOME t) (strlit "If") [clos_to_display h x1; clos_to_display h x2;
        clos_to_display h x3]) /\
  (clos_to_display h (closLang$Let t xs x) =
    Item (SOME t) (strlit "Let'")
        [List (clos_to_display_lets h (LENGTH xs - 1) xs);
            clos_to_display (h + LENGTH xs) x]) /\
  (clos_to_display h (Raise t x) =
    Item (SOME t) (strlit "Raise") [clos_to_display h x]) /\
  (clos_to_display h (Tick t x) =
    Item (SOME t) (strlit "Tick") [clos_to_display h x]) /\
  (clos_to_display h (Handle t x y) =
    Item (SOME t) (strlit "Handle")
        [clos_to_display h x; display_num_as_varn h;
            clos_to_display (h+1) y]) /\
  (clos_to_display h (Call t ticks dest xs) =
    Item (SOME t) (strlit "Call") [num_to_display ticks; num_to_display dest;
       List (MAP (clos_to_display h) xs)]) /\
  (clos_to_display h (App t opt_n x xs) =
    Item (SOME t) (strlit "App'")
        [option_to_display num_to_display opt_n;
         clos_to_display h x; List (MAP (clos_to_display h) xs)]) /\
  (clos_to_display h (Fn t n1 n2 vn x) =
    Item (SOME t) (strlit "Fn")
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         list_to_display string_to_display2 (num_to_varn_list h vn);
         clos_to_display h x]) /\
  (clos_to_display h (closLang$Letrec t n1 n2 es e) =
    Item (SOME t) (strlit "Letrec'")
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         List (clos_to_display_letrecs h (LENGTH es-1) (LENGTH es) es);
         clos_to_display h e]) /\
  (clos_to_display h (Op t op xs) =
    Item (SOME t) (strlit "Op") [clos_op_to_display op;
        List (MAP (clos_to_display h) xs)]) /\
  (clos_to_display_lets h i [] = []) /\
  (clos_to_display_lets h i (x::xs) =
    Tuple [display_num_as_varn (h+i); clos_to_display h x] :: clos_to_display_lets h (i-1) xs) /\
  (clos_to_display_letrecs h i len [] = []) /\
  (clos_to_display_letrecs h i len ((vn,e)::es) =
    Tuple [display_num_as_varn (h+i);
        list_to_display string_to_display2 (num_to_varn_list (h+len-1) vn);
        clos_to_display (h+len+vn) e]
    :: clos_to_display_letrecs h (i-1) len es)`
 (WF_REL_TAC `measure (\x. case x of
    | INL (_,e) => exp_size e
    | INR (INL (_,_,es)) => exp3_size es
    | INR (INR (_,_,_,es)) => exp1_size es)`
  \\ rw [closLangTheory.exp_size_def]
  \\ imp_res_tac MEM_clos_exps_size \\ fs []
 );

(* stackLang *)

val store_name_to_display_def = Define `
  store_name_to_display st = case st of
    | NextFree => empty_item (strlit "NextFree")
    | EndOfHeap => empty_item (strlit "EndOfHeap")
    | TriggerGC => empty_item (strlit "TriggerGC")
    | HeapLength => empty_item (strlit "HeapLength")
    | ProgStart => empty_item (strlit "ProgStart")
    | BitmapBase => empty_item (strlit "BitmapBase")
    | CurrHeap => empty_item (strlit "CurrHeap")
    | OtherHeap => empty_item (strlit "OtherHeap")
    | AllocSize => empty_item (strlit "AllocSize")
    | Globals => empty_item (strlit "Globals")
    | Handler => empty_item (strlit "Handler")
    | GenStart => empty_item (strlit "GenStart")
    | CodeBuffer => empty_item (strlit "CodeBuffer")
    | CodeBufferEnd => empty_item (strlit "CodeBufferEnd")
    | BitmapBuffer => empty_item (strlit "BitmapBuffer")
    | BitmapBufferEnd => empty_item (strlit "BitmapBufferEnd")
    | Temp n => item_with_num (strlit "Temp") (w2n n)`;

(* asm *)
(* also, yuck. programming with python now *)

val asm_binop_to_display_def = Define `
  asm_binop_to_display op = case op of
    | asm$Add => empty_item (strlit "Add")
    | Sub => empty_item (strlit "Sub")
    | And => empty_item (strlit "And")
    | Or => empty_item (strlit "Or")
    | Xor => empty_item (strlit "Xor")`;

val asm_reg_imm_to_display_def = Define `
  asm_reg_imm_to_display reg_imm = case reg_imm of
    | asm$Reg reg => item_with_num (strlit "Reg") reg
    | Imm imm => item_with_num (strlit "Imm") (w2n imm)`;

val asm_arith_to_display_def = Define `
  asm_arith_to_display op = case op of
    | asm$Binop bop n1 n2 reg_imm => Item NONE (strlit "Binop")
        [asm_binop_to_display bop; num_to_display n1; num_to_display n2;
            asm_reg_imm_to_display reg_imm]
    | asm$Shift sh n1 n2 n3 => Item NONE (strlit "Shift")
        (shift_to_display sh :: MAP num_to_display [n1; n2; n3])
    | Div n1 n2 n3 => item_with_nums (strlit "Div") [n1; n2; n3]
    | LongMul n1 n2 n3 n4 => item_with_nums (strlit "LongMul") [n1; n2; n3; n4]
    | LongDiv n1 n2 n3 n4 n5 => item_with_nums (strlit "LongDiv") [n1; n2; n3; n4; n5]
    | AddCarry n1 n2 n3 n4 => item_with_nums (strlit "AddCarry") [n1; n2; n3; n4]
    | AddOverflow n1 n2 n3 n4 => item_with_nums (strlit "AddOverflow") [n1; n2; n3; n4]
    | SubOverflow n1 n2 n3 n4 => item_with_nums (strlit "SubOverflow") [n1; n2; n3; n4]`;

val asm_addr_to_display_def = Define `
  asm_addr_to_display addr = case addr of
    | Addr reg w => item_with_nums (strlit "Addr") [reg; w2n w]`;

val asm_memop_to_display_def = Define `
  asm_memop_to_display op = case op of
    | Load => empty_item (strlit "Load")
    | Load8 => empty_item (strlit "Load8")
    | Store => empty_item (strlit "Store")
    | Store8 => empty_item (strlit "Store8")`;

val asm_fp_to_display_def = Define `
  asm_fp_to_display op = case op of
    | FPLess n1 n2 n3 => item_with_nums (strlit "FPLess") [n1; n2; n3]
    | FPLessEqual n1 n2 n3 => item_with_nums (strlit "FPLessEqual") [n1; n2; n3]
    | FPEqual n1 n2 n3 => item_with_nums (strlit "FPEqual") [n1; n2; n3]
    | FPAbs n1 n2 => item_with_nums (strlit "FPAbs") [n1; n2]
    | FPNeg n1 n2 => item_with_nums (strlit "FPNeg") [n1; n2]
    | FPSqrt n1 n2 => item_with_nums (strlit "FPSqrt") [n1; n2]
    | FPAdd n1 n2 n3 => item_with_nums (strlit "FPAdd") [n1; n2; n3]
    | FPSub n1 n2 n3 => item_with_nums (strlit "FPSub") [n1; n2; n3]
    | FPMul n1 n2 n3 => item_with_nums (strlit "FPMul") [n1; n2; n3]
    | FPDiv n1 n2 n3 => item_with_nums (strlit "FPDiv") [n1; n2; n3]
    | FPFma n1 n2 n3 => item_with_nums (strlit "FPFma") [n1; n2; n3]
    | FPMov n1 n2 => item_with_nums (strlit "FPMov") [n1; n2]
    | FPMovToReg n1 n2 n3 => item_with_nums (strlit "FPMovToReg") [n1; n2; n3]
    | FPMovFromReg n1 n2 n3 => item_with_nums (strlit "FPMovFromReg") [n1; n2; n3]
    | FPToInt n1 n2 => item_with_nums (strlit "FPToInt") [n1; n2]
    | FPFromInt n1 n2 => item_with_nums (strlit "FPFromInt") [n1; n2]`;

val asm_inst_to_display_def = Define `
  asm_inst_to_display inst = case inst of
    | asm$Skip => empty_item (strlit "Skip")
    | Const reg w => item_with_nums (strlit "Const") [reg; w2n w]
    | Arith a => Item NONE (strlit "Arith") [asm_arith_to_display a]
    | Mem mop r addr => Item NONE (strlit "Mem") [asm_memop_to_display mop;
        num_to_display r; asm_addr_to_display addr]
    | FP fp => Item NONE (strlit "FP") [asm_fp_to_display fp]`;

(* wordLang *)

val MEM_word_exps_size_ARB =
    wordLangTheory.MEM_IMP_exp_size |> Q.GEN `l` |> Q.SPEC `ARB`;

val word_exp_to_display_def = tDefine "word_exp_to_display" `
  (word_exp_to_display (wordLang$Const v)
    = item_with_num (strlit "Const") (w2n v)) /\
  (word_exp_to_display (Var n)
    = item_with_num (strlit "Var") n) /\
  (word_exp_to_display (Lookup st)
    = Item NONE (strlit "Lookup") [store_name_to_display st]) /\
  (word_exp_to_display (Load exp2)
    = Item NONE (strlit "Load") [word_exp_to_display exp2]) /\
  (word_exp_to_display (Op bop exs)
    = Item NONE (strlit "Op") (asm_binop_to_display bop
        :: MAP word_exp_to_display exs)) /\
  (word_exp_to_display (Shift sh exp num)
    = Item NONE (strlit "Shift") [
      shift_to_display sh;
      word_exp_to_display exp;
      num_to_display num
    ])`
 (WF_REL_TAC `measure (wordLang$exp_size ARB)`
  \\ rw []
  \\ imp_res_tac MEM_word_exps_size_ARB
  \\ rw []
 );

val num_set_to_display_def = Define
  `num_set_to_display ns = List (MAP num_to_display
    (MAP FST (sptree$toAList ns)))`;

val word_prog_to_display_def = tDefine "word_prog_to_display" `
  (word_prog_to_display Skip = empty_item (strlit "Skip")) /\
  (word_prog_to_display (Move n mvs) = Item NONE (strlit "Move")
    [num_to_display n; displayLang$List (MAP (\(n1, n2). Tuple
        [num_to_display n1; num_to_display n2]) mvs)]) /\
  (word_prog_to_display (Inst i) = empty_item (strlit "Inst")) /\
  (word_prog_to_display (Assign n exp) = Item NONE (strlit "Assign")
    [num_to_display n; word_exp_to_display exp]) /\
  (word_prog_to_display (Get n sn) = Item NONE (strlit "Get")
    [num_to_display n; store_name_to_display sn]) /\
  (word_prog_to_display (Set sn exp) = Item NONE (strlit "Set")
    [store_name_to_display sn; word_exp_to_display exp]) /\
  (word_prog_to_display (Store exp n) = Item NONE (strlit "Store")
    [word_exp_to_display exp; num_to_display n]) /\
  (word_prog_to_display (MustTerminate prog) = Item NONE (strlit "MustTerminate")
    [word_prog_to_display prog]) /\
  (word_prog_to_display (Call a b c d) = Item NONE (strlit "Call")
    [word_prog_to_display_ret a; option_to_display num_to_display b;
        list_to_display num_to_display c;
        word_prog_to_display_handler d]) /\
  (word_prog_to_display (Seq prog1 prog2) = Item NONE (strlit "Seq")
    [word_prog_to_display prog1; word_prog_to_display prog2]) /\
  (word_prog_to_display (If cmp n reg p1 p2) = Item NONE (strlit "If")
    [word_prog_to_display p1; word_prog_to_display p2]) /\
  (word_prog_to_display (Alloc n ns) = Item NONE (strlit "Alloc")
    [num_to_display n; num_set_to_display ns]) /\
  (word_prog_to_display (Raise n) = item_with_num (strlit "Raise") n) /\
  (word_prog_to_display (Return n1 n2) = item_with_nums (strlit "Return") [n1; n2]) /\
  (word_prog_to_display Tick = empty_item (strlit "Tick")) /\
  (word_prog_to_display (LocValue n1 n2) =
    item_with_nums (strlit "LocValue") [n1; n2]) /\
  (word_prog_to_display (Install n1 n2 n3 n4 ns) =
    Item NONE (strlit "Install") (MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ns])) /\
  (word_prog_to_display (CodeBufferWrite n1 n2) =
    item_with_nums (strlit "CodeBufferWrite") [n1; n2]) /\
  (word_prog_to_display (DataBufferWrite n1 n2) =
    item_with_nums (strlit "DataBufferWrite") [n1; n2]) /\
  (word_prog_to_display (FFI nm n1 n2 n3 n4 ns) =
    Item NONE (strlit "FFI") (string_to_display2 nm :: MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ns])) /\
  (word_prog_to_display_ret NONE = empty_item (strlit "NONE")) /\
  (word_prog_to_display_ret (SOME (n1, ns, prog, n2, n3)) =
    Item NONE (strlit "SOME") [Tuple [num_to_display n1; num_set_to_display ns;
        word_prog_to_display prog; num_to_display n2; num_to_display n3]]) /\
  (word_prog_to_display_handler NONE = empty_item (strlit "NONE")) /\
  (word_prog_to_display_handler (SOME (n1, prog, n2, n3)) =
    Item NONE (strlit "SOME") [Tuple [num_to_display n1;
        word_prog_to_display prog; num_to_display n2; num_to_display n3]])
`
  (WF_REL_TAC `measure (\x. case x of
        | INL p => wordLang$prog_size ARB p
        | INR (INL v) => wordLang$prog1_size ARB v
        | INR (INR v) => wordLang$prog3_size ARB v)`
    \\ rw []
  )
;

val word_progs_to_display_def = Define`
  word_progs_to_display ps = list_to_display
    (\(n1, n2, prog). displayLang$Tuple [num_to_display n1;
        num_to_display n2; word_prog_to_display prog]) ps`;

(* Function to construct general functions from a language to JSON. Call with
* the name of the language and what function to use to convert it to
* displayLang to obtain a wrapper function which exports JSON. *)
val lang_to_json_def = Define`
  lang_to_json langN func =
    \ p . Object [
      ("lang", String langN);
      ("prog", display_to_json (func p))]`;

(* tap configuration. which bits of compilation should we save?
   top-level code for assembling the tapped data. *)

val () = Datatype `
  tap_config = Tap_Config
    (* save filename prefix *) mlstring
    (* bits which should be saved. the boolean indicates
       the presence of a '*' suffix, and matches all suffixes *)
    ((mlstring # bool) list)`;

val mk_tap_star = Define `
  mk_tap_star str = if isSuffix (strlit "*") str
    then (substring str 0 (strlen str - 1), T)
    else (str, F)`;

val mk_tap_config = Define `
  mk_tap_config fname taps = Tap_Config (case fname of
    | NONE => (strlit "default.tap") | SOME s => s) (MAP mk_tap_star taps)`;

val default_tap_config = Define `
  default_tap_config = mk_tap_config NONE []`;

val should_tap_def = Define `
  should_tap (conf : tap_config) nm = case conf of
    | Tap_Config _ taps => EXISTS (\(s, star). if star then
        isPrefix s nm else s = nm) taps`;

val tap_name_def = Define `
  tap_name (conf : tap_config) nm = case conf of
    | Tap_Config fname _ => concat [fname; strlit "."; nm]`;

val () = Datatype `
  tap_data = Tap_Data mlstring (unit -> jsonLang$obj)`;

val add_tap_def = Define `
  add_tap conf nm (to_display : 'a -> displayLang$sExp) (v : 'a) tds
    = if should_tap conf nm
    then Tap_Data (tap_name conf nm)
            (\_. lang_to_json (explode nm) to_display v) :: tds
    else tds`;

val tap_data_strings_def = Define `
  tap_data_strings td = case td of
    | Tap_Data nm json_f => (nm,
        implode (misc$append (json_to_string (json_f ()))))`;

val tap_flat_def = Define `
  tap_flat conf v = add_tap conf (strlit "flat") flat_to_display_decs v`;

val tap_word_def = Define `
  tap_word conf v = add_tap conf (strlit "word") word_progs_to_display v`;

val tap_pat_def = Define`
  tap_pat conf v = add_tap conf (strlit "pat")
    (list_to_display (pat_to_display 0)) v`;

val tap_clos_def = Define`
  tap_clos conf v = add_tap conf (strlit "clos")
    (list_to_display (clos_to_display 0)) v`;

val _ = export_theory();
