open preamble astTheory mlnumTheory mlintTheory
open flatLangTheory patLangTheory closLangTheory
     displayLangTheory source_to_flatTheory
     wordLangTheory;

val _ = new_theory"presLang";

(* Functions for converting various intermediate languages
   into displayLang representations. *)

(* basics *)

val empty_item_def = Define`
  empty_item name = Item NONE name []`;

val string_to_display_def = Define`
  string_to_display s = empty_item ("\"" ++ s ++ "\"")`;

val num_to_display_def = Define`
  num_to_display (n : num) = string_to_display (explode (toString n))`;

val item_with_num_def = Define`
  item_with_num name n = Item NONE name [num_to_display n]`;

val item_with_nums_def = Define`
  item_with_nums name ns = Item NONE name (MAP num_to_display ns)`;

val bool_to_display_def = Define`
  bool_to_display b = empty_item (if b then "True" else "False")`;

val num_to_hex_digit_def = Define `
  num_to_hex_digit n =
    if n < 10 then [CHR (48 + n)] else
    if n < 16 then [CHR (55 + n)] else []`;

val num_to_hex_def = Define `
  num_to_hex n =
    (if n < 16 then [] else num_to_hex (n DIV 16)) ++
    num_to_hex_digit (n MOD 16)`;

val display_word_to_hex_string_def = Define `
  display_word_to_hex_string w =
    empty_item ("0x" ++ words$word_to_hex_string w)`;

val lit_to_display_def = Define`
  (lit_to_display (IntLit i) =
    Item NONE "IntLit" [empty_item (explode (toString i))])
  /\
  (lit_to_display (Char c) =
    Item NONE "Char" [empty_item ("#\"" ++ [c] ++ "\"")])
  /\
  (lit_to_display (StrLit s) =
    Item NONE "StrLit" [string_to_display s])
  /\
  (lit_to_display (Word8 w) =
    Item NONE "Word8" [display_word_to_hex_string w])
  /\
  (lit_to_display (Word64 w) =
    Item NONE "Word64" [display_word_to_hex_string w])`;

val list_to_display_def = Define`
  (list_to_display f xs = displayLang$List (MAP f xs))`

val option_to_display_def = Define`
  (option_to_display f opt = case opt of
                      | NONE => empty_item "NONE"
                      | SOME opt' => Item NONE "SOME" [f opt'])`

val option_string_to_display_def = Define`
  (option_string_to_display opt = case opt of
                      | NONE => empty_item "NONE"
                      | SOME opt' => Item NONE "SOME" [string_to_display opt'])`

(* semantic ops and values *)

val fp_cmp_to_display_def = Define `
  fp_cmp_to_display cmp = case cmp of
    | FP_Less => empty_item "FP_Less"
    | FP_LessEqual => empty_item "FP_LessEqual"
    | FP_Greater => empty_item "FP_Greater"
    | FP_GreaterEqual => empty_item "FP_GreaterEqual"
    | FP_Equal => empty_item "FP_Equal"`

val fp_uop_to_display_def = Define `
  fp_uop_to_display op = case op of
    | FP_Abs => empty_item "FP_Abs"
    | FP_Neg => empty_item "FP_Neg"
    | FP_Sqrt => empty_item "FP_Sqrt"`

val fp_bop_to_display_def = Define `
  fp_bop_to_display op = case op of
    | fpSem$FP_Add => empty_item "FP_Add"
    | FP_Sub => empty_item "FP_Sub"
    | FP_Mul => empty_item "FP_Mul"
    | FP_Div => empty_item "FP_Div"`

val word_size_to_display_def = Define`
  (word_size_to_display W8 = empty_item "W8")
  /\
  (word_size_to_display W64 = empty_item "W64")`;

val opn_to_display_def = Define`
  (opn_to_display Plus = empty_item "Plus")
  /\
  (opn_to_display Minus = empty_item "Minus")
  /\
  (opn_to_display Times = empty_item "Times")
  /\
  (opn_to_display Divide = empty_item "Divide")
  /\
  (opn_to_display Modulo = empty_item "Modulo")`;

val opb_to_display_def = Define`
  (opb_to_display Lt = empty_item "Lt")
  /\
  (opb_to_display Gt = empty_item "Gt")
  /\
  (opb_to_display Leq = empty_item "Leq")
  /\
  (opb_to_display Geq = empty_item "Geq")`;

val opw_to_display_def = Define`
  (opw_to_display Andw = empty_item "Andw")
  /\
  (opw_to_display Orw = empty_item "Orw")
  /\
  (opw_to_display Xor = empty_item "Xor")
  /\
  (opw_to_display Add = empty_item "Add")
  /\
  (opw_to_display Sub = empty_item "Sub")`;

val shift_to_display_def = Define`
  (shift_to_display Lsl = empty_item "Lsl")
  /\
  (shift_to_display Lsr = empty_item "Lsr")
  /\
  (shift_to_display Asr = empty_item "Asr")
  /\
  (shift_to_display Ror = empty_item "Ror")`;


 (* flatLang *)

val MEM_pat_size = prove(
  ``!pats a. MEM a (pats:flatLang$pat list) ==> pat_size a < pat1_size pats``,
  Induct \\ rw [] \\ rw [flatLangTheory.pat_size_def] \\ res_tac \\ fs []);

val opt_con_to_display_def = Define `
  opt_con_to_display ocon = case ocon of
    | NONE => empty_item "ConIdNone"
    | SOME (c, NONE) => item_with_num "ConIdUntyped" c
    | SOME (c, SOME t) => item_with_nums "ConIdTyped" [c; t]`

val flat_pat_to_display_def = tDefine "flat_pat_to_display" `
  flat_pat_to_display p =
    case p of
       | flatLang$Pvar varN => Item NONE "Pvar" [string_to_display varN]
       | Pany => empty_item "Pany"
       | Plit lit => Item NONE "Plit" [lit_to_display lit]
       | flatLang$Pcon id pats => Item NONE "Pcon"
            (MAP flat_pat_to_display pats)
       | Pref pat => Item NONE "Pref" [flat_pat_to_display pat] `
  (WF_REL_TAC `measure pat_size` \\ rw []
   \\ imp_res_tac MEM_pat_size \\ fs [])

val flat_op_to_display_def = Define `
  flat_op_to_display op = case op of
    | Opn op => opn_to_display op
    | Opb op => opb_to_display op
    | Opw ws op =>
        Item NONE "Opw" [ word_size_to_display ws; opw_to_display op ]
    | Shift ws sh num => Item NONE "Shift" [
      word_size_to_display ws;
      shift_to_display sh;
      num_to_display num
    ]
    | Equality => empty_item "Equality"
    | FP_cmp cmp => fp_cmp_to_display cmp
    | FP_uop op => fp_uop_to_display op
    | FP_bop op => fp_bop_to_display op
    | Opapp => empty_item "Opapp"
    | Opassign => empty_item "Opassign"
    | Opref => empty_item "Opref"
    | Opderef => empty_item "Opderef"
    | Aw8alloc => empty_item "Aw8alloc"
    | Aw8sub => empty_item "Aw8sub"
    | Aw8length => empty_item "Aw8length"
    | Aw8update => empty_item "Aw8update"
    | WordFromInt ws =>
        Item NONE "WordFromInt" [word_size_to_display ws]
    | WordToInt ws =>
        Item NONE "WordToInt" [word_size_to_display ws]
    | CopyStrStr => empty_item "CopyStrStr"
    | CopyStrAw8 => empty_item "CopyStrAw8"
    | CopyAw8Str => empty_item "CopyAw8Str"
    | CopyAw8Aw8 => empty_item "CopyAw8Aw8"
    | Ord => empty_item "Ord"
    | Chr => empty_item "Chr"
    | Chopb op => Item NONE "Chopb" [opb_to_display op]
    | Implode => empty_item "Implode"
    | Strsub => empty_item "Strsub"
    | Strlen => empty_item "Strlen"
    | Strcat => empty_item "Strcat"
    | VfromList => empty_item "VfromList"
    | Vsub => empty_item "Vsub"
    | Vlength => empty_item "Vlength"
    | Aalloc => empty_item "Aalloc"
    | Asub => empty_item "Asub"
    | Alength => empty_item "Alength"
    | Aupdate => empty_item "Aupdate"
    | ListAppend => empty_item "ListAppend"
    | ConfigGC => empty_item "ConfigGC"
    | FFI s => Item NONE "FFI" [string_to_display s]
    | GlobalVarAlloc n => item_with_num "GlobalVarAlloc" n
    | GlobalVarInit n => item_with_num "GlobalVarInit" n
    | GlobalVarLookup n => item_with_num "GlobalVarLookup" n
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
    Item (SOME tra) "Raise" [flat_to_display exp])
  /\
  (flat_to_display (Handle tra exp pes) =
    Item (SOME tra) "Handle" (flat_to_display exp
        :: MAP (\(pat,exp). displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp]) pes))
  /\
  (flat_to_display (Lit tra lit) = Item (SOME tra) "Lit" [])
  /\
  (flat_to_display (flatLang$Con tra id_opt exps) =
    Item (SOME tra) "Con" (opt_con_to_display id_opt
        :: MAP flat_to_display exps))
  /\
  (flat_to_display (Var_local tra varN) =
    Item (SOME tra) "Var_local" [string_to_display varN])
  /\
  (flat_to_display (Fun tra varN exp) =
    Item (SOME tra) "Fun" [string_to_display varN; flat_to_display exp])
  /\
  (flat_to_display (App tra op exps) =
    Item (SOME tra) "App" (flat_op_to_display op :: MAP flat_to_display exps))
  /\
  (flat_to_display (If tra exp1 exp2 exp3) =
    Item (SOME tra) "If" [flat_to_display exp1; flat_to_display exp2;
        flat_to_display exp3])
  /\
  (flat_to_display (Mat tra exp pes) =
    Item (SOME tra) "Mat" (flat_to_display exp
        :: MAP (\(pat,exp). displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp]) pes))
  /\
  (flat_to_display (Let tra varN_opt exp1 exp2) =
    Item (SOME tra) "Let" [option_string_to_display varN_opt;
        flat_to_display exp1; flat_to_display exp2])
  /\
  (flat_to_display (Letrec tra funs exp) =
    Item (SOME tra) "Letrec"
        [List (MAP (\(v1,v2,e). Tuple [string_to_display v1; string_to_display v2;
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
       | Dlet exp => Item NONE "Dlet" [flat_to_display exp]
       | Dtype mods con_arities => item_with_num "Dtype" mods
       | Dexn n1 n2 => item_with_nums "Dexn" [n1; n2]`

val flat_to_display_decs_def = Define`
  flat_to_display_decs = list_to_display flat_to_display_dec`;

(* pat to displayLang *)

val num_to_varn_def = tDefine "num_to_varn" `
  num_to_varn n = if n < 26 then [CHR (97 + n)]
                  else (num_to_varn ((n DIV 26)-1)) ++ ([CHR (97 + (n MOD 26))])`
  (WF_REL_TAC `measure I` \\ rw [] \\ fs [DIV_LT_X]);

val display_num_as_varn_def = Define `
  display_num_as_varn n = string_to_display (num_to_varn n)`;

val pat_op_to_display_def = Define `
  pat_op_to_display op = case op of
    | patLang$Op op2 => flat_op_to_display op2
    | Run => empty_item "Run"
    | Tag_eq n1 n2 => item_with_nums "Tag_eq" [n1; n2]
    | El num => item_with_num "El" num
  `

val MEM_exps_size = prove(
  ``!exps e. MEM a exps ==> patLang$exp_size a < exp1_size exps``,
  Induct \\ fs [patLangTheory.exp_size_def] \\ rw []
  \\ fs [patLangTheory.exp_size_def] \\ res_tac \\ fs []);

(* The constructors in pat differ a bit because of de bruijn indices. This is
* solved with the argument h, referring to head of our indexing. Combined with
* num_to_varn this means we create varNs to match the presLang-constructors
* where either nums or no name at all were provided. *)

val pat_to_display_def = tDefine "pat_to_display" `
  (pat_to_display h (patLang$Raise t e) =
    Item (SOME t) "Raise" [pat_to_display h e])
  /\
  (pat_to_display h (Handle t e1 e2) =
    Item (SOME t) "Handle" [pat_to_display h e1; pat_to_display (h+1) e2])
  /\
  (pat_to_display h (Lit t lit) =
    Item (SOME t) "Lit" [lit_to_display lit])
  /\
  (pat_to_display h (Con t num es) =
    Item (SOME t) "Con" (num_to_display num :: MAP (pat_to_display h) es))
  /\
  (pat_to_display h (Var_local t var_index) =
    Item (SOME t) "Var_local" [display_num_as_varn (h-var_index-1)])
  /\
  (pat_to_display h (Fun t e) =
    Item (SOME t) "Fun" [display_num_as_varn h; pat_to_display (h+1) e])
  /\
  (pat_to_display h (App t op es) =
    Item (SOME t) "App" (pat_op_to_display op :: MAP (pat_to_display h) es))
  /\
  (pat_to_display h (If t e1 e2 e3) =
    Item (SOME t) "If" [pat_to_display h e1; pat_to_display h e2;
        pat_to_display h e3])
  /\
  (pat_to_display h (Let t e1 e2) =
    Item (SOME t) "Let" [display_num_as_varn h;
        pat_to_display h e1; pat_to_display (h+1) e2])
  /\
  (pat_to_display h (Seq t e1 e2) =
    Item (SOME t) "Seq" [pat_to_display h e1; pat_to_display h e2])
  /\
  (pat_to_display h (Letrec t es e) =
    (let len = LENGTH es in Item (SOME t) "Letrec"
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
  \\ imp_res_tac MEM_exps_size \\ fs []);

(* clos to displayLang *)

val num_to_varn_list_def = Define `
  num_to_varn_list h n =
    if n = 0 then [] else
      num_to_varn (h + n) :: num_to_varn_list h (n-1)`

val clos_op_to_display_def = Define `
  clos_op_to_display op = case op of
    | Global num => item_with_num "Global" num
    | SetGlobal num => item_with_num "SetGlobal" num
    | AllocGlobal => empty_item "AllocGlobal"
    | GlobalsPtr => empty_item "GlobalsPtr"
    | SetGlobalsPtr => empty_item "SetGlobalsPtr"
    | Cons num => item_with_num "Cons" num
    | ConsExtend num => item_with_num "ConsExtend" num
    | El => empty_item "El"
    | LengthBlock => empty_item "LengthBlock"
    | Length => empty_item "Length"
    | LengthByte => empty_item "LengthByte"
    | RefByte b => Item NONE "RefByte" [bool_to_display b]
    | RefArray => empty_item "RefArray"
    | DerefByte => empty_item "DerefByte"
    | UpdateByte => empty_item "UpdateByte"
    | ConcatByteVec => empty_item "ConcatByteVec"
    | CopyByte b => Item NONE "CopyByte" [bool_to_display b]
    | ListAppend => empty_item "ListAppend"
    | FromList num => item_with_num "FromList" num
    | closLang$String s => Item NONE "String" [string_to_display s]
    | FromListByte => empty_item "FromListByte"
    | LengthByteVec => empty_item "LengthByteVec"
    | DerefByteVec => empty_item "DerefByteVec"
    | TagLenEq n1 n2 => item_with_nums "TagLenEq" [n1; n2]
    | TagEq num => item_with_num "TagEq" num
    | Ref => empty_item "Ref"
    | Deref => empty_item "Deref"
    | Update => empty_item "Update"
    | Label num => item_with_num "Label" num
    | FFI s => Item NONE "FFI" [string_to_display s]
    | Equal => empty_item "Equal"
    | EqualInt i => empty_item "EqualIntWithMissingData"
    | Const i => empty_item "ConstWithMissingData"
    | Add => empty_item "Add"
    | Sub => empty_item "Sub"
    | Mult => empty_item "Mult"
    | Div => empty_item "Div"
    | Mod => empty_item "Mod"
    | Less => empty_item "Less"
    | LessEq => empty_item "LessEq"
    | Greater => empty_item "Greater"
    | GreaterEq => empty_item "GreaterEq"
    | WordOp ws op =>
        Item NONE "WordOp" [ word_size_to_display ws; opw_to_display op ]
    | WordShift ws sh num => Item NONE "WordShift" [
      word_size_to_display ws;
      shift_to_display sh;
      num_to_display num
    ]
    | WordFromInt => empty_item "WordFromInt"
    | WordToInt => empty_item "WordToInt"
    | WordFromWord b => Item NONE "WordFromWord" [bool_to_display b]
    | FP_cmp cmp => fp_cmp_to_display cmp
    | FP_uop op => fp_uop_to_display op
    | FP_bop op => fp_bop_to_display op
    | BoundsCheckBlock => empty_item "BoundsCheckBlock"
    | BoundsCheckArray => empty_item "BoundsCheckArray"
    | BoundsCheckByte b => Item NONE "BoundsCheckByte" [bool_to_display b]
    | LessConstSmall num => item_with_num "LessConstSmall" num
    | closLang$ConfigGC => empty_item "ConfigGC"
    | Install => empty_item "Install"
`

val MEM_clos_exps_size = prove(
  ``!exps e. MEM e exps ==> closLang$exp_size e < exp3_size exps``,
  Induct \\ fs [closLangTheory.exp_size_def] \\ rw []
  \\ fs [closLangTheory.exp_size_def] \\ res_tac \\ fs []);

(* The clos_to_display function uses the same approach to de bruijn
   indices as the pat_to_display function *)
val clos_to_display_def = tDefine "clos_to_display" `
  (clos_to_display h (Var t n) =
    Item (SOME t) "Var" [display_num_as_varn (h-n-1)]) /\
  (clos_to_display h (If t x1 x2 x3) =
    Item (SOME t) "If" [clos_to_display h x1; clos_to_display h x2;
        clos_to_display h x3]) /\
  (clos_to_display h (closLang$Let t xs x) =
    Item (SOME t) "Let'" [List (clos_to_display_lets h (LENGTH xs - 1) xs);
        clos_to_display (h + LENGTH xs) x]) /\
  (clos_to_display h (Raise t x) =
    Item (SOME t) "Raise" [clos_to_display h x]) /\
  (clos_to_display h (Tick t x) =
    Item (SOME t) "Tick" [clos_to_display h x]) /\
  (clos_to_display h (Handle t x y) =
    Item (SOME t) "Handle" [clos_to_display h x; display_num_as_varn h;
        clos_to_display (h+1) y]) /\
  (clos_to_display h (Call t ticks dest xs) =
    Item (SOME t) "Call" [num_to_display ticks; num_to_display dest;
       List (MAP (clos_to_display h) xs)]) /\
  (clos_to_display h (App t opt_n x xs) =
    Item (SOME t) "App'"
        [option_to_display num_to_display opt_n;
         clos_to_display h x; List (MAP (clos_to_display h) xs)]) /\
  (clos_to_display h (Fn t n1 n2 vn x) =
    Item (SOME t) "Fn"
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         list_to_display string_to_display (num_to_varn_list h vn);
         clos_to_display h x]) /\
  (clos_to_display h (closLang$Letrec t n1 n2 es e) =
    Item (SOME t) "Letrec'" 
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         List (clos_to_display_letrecs h (LENGTH es-1) (LENGTH es) es);
         clos_to_display h e]) /\
  (clos_to_display h (Op t op xs) =
    Item (SOME t) "Op" [clos_op_to_display op;
        List (MAP (clos_to_display h) xs)]) /\
  (clos_to_display_lets h i [] = []) /\
  (clos_to_display_lets h i (x::xs) =
    Tuple [display_num_as_varn (h+i); clos_to_display h x] :: clos_to_display_lets h (i-1) xs) /\
  (clos_to_display_letrecs h i len [] = []) /\
  (clos_to_display_letrecs h i len ((vn,e)::es) =
    Tuple [display_num_as_varn (h+i); 
        list_to_display string_to_display (num_to_varn_list (h+len-1) vn);
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
    | NextFree => empty_item "NextFree"
    | EndOfHeap => empty_item "EndOfHeap"
    | TriggerGC => empty_item "TriggerGC"
    | HeapLength => empty_item "HeapLength"
    | ProgStart => empty_item "ProgStart"
    | BitmapBase => empty_item "BitmapBase"
    | CurrHeap => empty_item "CurrHeap"
    | OtherHeap => empty_item "OtherHeap"
    | AllocSize => empty_item "AllocSize"
    | Globals => empty_item "Globals"
    | Handler => empty_item "Handler"
    | GenStart => empty_item "GenStart"
    | CodeBuffer => empty_item "CodeBuffer"
    | CodeBufferEnd => empty_item "CodeBufferEnd"
    | BitmapBuffer => empty_item "BitmapBuffer"
    | BitmapBufferEnd => empty_item "BitmapBufferEnd"
    | Temp n => item_with_num "Temp" (w2n n)`;

(* asm *)
(* also, yuck. programming with python now *)

val asm_binop_to_display_def = Define `
  asm_binop_to_display op = case op of
    | asm$Add => empty_item "Add"
    | Sub => empty_item "Sub"
    | And => empty_item "And"
    | Or => empty_item "Or"
    | Xor => empty_item "Xor"`;

val asm_reg_imm_to_display_def = Define `
  asm_reg_imm_to_display reg_imm = case reg_imm of
    | asm$Reg reg => item_with_num "Reg" reg
    | Imm imm => item_with_num "Imm" (w2n imm)`;

val asm_arith_to_display_def = Define `
  asm_arith_to_display op = case op of
    | asm$Binop bop n1 n2 reg_imm => Item NONE "Binop"
        [asm_binop_to_display bop; num_to_display n1; num_to_display n2;
            asm_reg_imm_to_display reg_imm]
    | asm$Shift sh n1 n2 n3 => Item NONE "Shift"
        (shift_to_display sh :: MAP num_to_display [n1; n2; n3])
    | Div n1 n2 n3 => item_with_nums "Div" [n1; n2; n3]
    | LongMul n1 n2 n3 n4 => item_with_nums "LongMul" [n1; n2; n3; n4]
    | LongDiv n1 n2 n3 n4 n5 => item_with_nums "LongDiv" [n1; n2; n3; n4; n5]
    | AddCarry n1 n2 n3 n4 => item_with_nums "AddCarry" [n1; n2; n3; n4]
    | AddOverflow n1 n2 n3 n4 => item_with_nums "AddOverflow" [n1; n2; n3; n4]
    | SubOverflow n1 n2 n3 n4 => item_with_nums "SubOverflow" [n1; n2; n3; n4]`;

val asm_addr_to_display_def = Define `
  asm_addr_to_display addr = case addr of
    | Addr reg w => item_with_nums "Addr" [reg; w2n w]`;

val asm_memop_to_display_def = Define `
  asm_memop_to_display op = case op of
    | Load => empty_item "Load"
    | Load8 => empty_item "Load8"
    | Store => empty_item "Store"
    | Store8 => empty_item "Store8"`;

val asm_fp_to_display_def = Define `
  asm_fp_to_display op = case op of
    | FPLess n1 n2 n3 => item_with_nums "FPLess" [n1; n2; n3]
    | FPLessEqual n1 n2 n3 => item_with_nums "FPLessEqual" [n1; n2; n3]
    | FPEqual n1 n2 n3 => item_with_nums "FPEqual" [n1; n2; n3]
    | FPAbs n1 n2 => item_with_nums "FPAbs" [n1; n2]
    | FPNeg n1 n2 => item_with_nums "FPNeg" [n1; n2]
    | FPSqrt n1 n2 => item_with_nums "FPSqrt" [n1; n2]
    | FPAdd n1 n2 n3 => item_with_nums "FPAdd" [n1; n2; n3]
    | FPSub n1 n2 n3 => item_with_nums "FPSub" [n1; n2; n3]
    | FPMul n1 n2 n3 => item_with_nums "FPMul" [n1; n2; n3]
    | FPDiv n1 n2 n3 => item_with_nums "FPDiv" [n1; n2; n3]
    | FPMov n1 n2 => item_with_nums "FPMov" [n1; n2]
    | FPMovToReg n1 n2 n3 => item_with_nums "FPMovToReg" [n1; n2; n3]
    | FPMovFromReg n1 n2 n3 => item_with_nums "FPMovFromReg" [n1; n2; n3]
    | FPToInt n1 n2 => item_with_nums "FPToInt" [n1; n2]
    | FPFromInt n1 n2 => item_with_nums "FPFromInt" [n1; n2]`;

val asm_inst_to_display_def = Define `
  asm_inst_to_display inst = case inst of
    | asm$Skip => empty_item "Skip"
    | Const reg w => item_with_nums "Const" [reg; w2n w]
    | Arith a => Item NONE "Arith" [asm_arith_to_display a]
    | Mem mop r addr => Item NONE "Mem" [asm_memop_to_display mop;
        num_to_display r; asm_addr_to_display addr]
    | FP fp => Item NONE "FP" [asm_fp_to_display fp]`;

(* wordLang *)

val MEM_word_exps_size_ARB =
    wordLangTheory.MEM_IMP_exp_size |> Q.GEN `l` |> Q.SPEC `ARB`;

val word_exp_to_display_def = tDefine "word_exp_to_display" `
  (word_exp_to_display (wordLang$Const v)
    = item_with_num "Const" (w2n v)) /\
  (word_exp_to_display (Var n)
    = item_with_num "Var" n) /\
  (word_exp_to_display (Lookup st)
    = Item NONE "Lookup" [store_name_to_display st]) /\
  (word_exp_to_display (Load exp2)
    = Item NONE "Load" [word_exp_to_display exp2]) /\
  (word_exp_to_display (Op bop exs)
    = Item NONE "Op" (asm_binop_to_display bop
        :: MAP word_exp_to_display exs)) /\
  (word_exp_to_display (Shift sh exp num)
    = Item NONE "Shift" [
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
  (word_prog_to_display Skip = empty_item "Skip") /\
  (word_prog_to_display (Move n mvs) = Item NONE "Move"
    [num_to_display n; displayLang$List (MAP (\(n1, n2). Tuple
        [num_to_display n1; num_to_display n2]) mvs)]) /\
  (word_prog_to_display (Inst i) = empty_item "Inst") /\
  (word_prog_to_display (Assign n exp) = Item NONE "Assign"
    [num_to_display n; word_exp_to_display exp]) /\
  (word_prog_to_display (Get n sn) = Item NONE "Get"
    [num_to_display n; store_name_to_display sn]) /\
  (word_prog_to_display (Set sn exp) = Item NONE "Set"
    [store_name_to_display sn; word_exp_to_display exp]) /\
  (word_prog_to_display (Store exp n) = Item NONE "Store"
    [word_exp_to_display exp; num_to_display n]) /\
  (word_prog_to_display (MustTerminate prog) = Item NONE "MustTerminate"
    [word_prog_to_display prog]) /\
  (word_prog_to_display (Call a b c d) = Item NONE "Call"
    [word_prog_to_display_ret a; option_to_display num_to_display b;
        list_to_display num_to_display c;
        word_prog_to_display_handler d]) /\
  (word_prog_to_display (Seq prog1 prog2) = Item NONE "Seq"
    [word_prog_to_display prog1; word_prog_to_display prog2]) /\
  (word_prog_to_display (If cmp n reg p1 p2) = Item NONE "If"
    [word_prog_to_display p1; word_prog_to_display p2]) /\
  (word_prog_to_display (Alloc n ns) = Item NONE "Alloc"
    [num_to_display n; num_set_to_display ns]) /\
  (word_prog_to_display (Raise n) = item_with_num "Raise" n) /\
  (word_prog_to_display (Return n1 n2) = item_with_nums "Return" [n1; n2]) /\
  (word_prog_to_display Tick = empty_item "Tick") /\
  (word_prog_to_display (LocValue n1 n2) =
    item_with_nums "LocValue" [n1; n2]) /\
  (word_prog_to_display (Install n1 n2 n3 n4 ns) =
    Item NONE "Install" (MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ns])) /\
  (word_prog_to_display (CodeBufferWrite n1 n2) =
    item_with_nums "CodeBufferWrite" [n1; n2]) /\
  (word_prog_to_display (DataBufferWrite n1 n2) =
    item_with_nums "DataBufferWrite" [n1; n2]) /\
  (word_prog_to_display (FFI nm n1 n2 n3 n4 ns) =
    Item NONE "FFI" (string_to_display nm :: MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ns])) /\
  (word_prog_to_display_ret NONE = empty_item "NONE") /\
  (word_prog_to_display_ret (SOME (n1, ns, prog, n2, n3)) =
    Item NONE "SOME" [Tuple [num_to_display n1; num_set_to_display ns;
        word_prog_to_display prog; num_to_display n2; num_to_display n3]]) /\
  (word_prog_to_display_handler NONE = empty_item "NONE") /\
  (word_prog_to_display_handler (SOME (n1, prog, n2, n3)) =
    Item NONE "SOME" [Tuple [num_to_display n1;
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
    (* save filename prefix *) string
    (* bits which should be saved *) (string list)`;

val () = Datatype `
  tap_data = Tap_Data ((string # (unit -> jsonLang$obj)) list)`;

val empty_tap_data_def = Define `
  empty_tap_data = Tap_Data []`;

val should_tap_def = Define `
  should_tap (conf : tap_config) nm = case conf of
    | Tap_Config _ taps => EXISTS (\s. s = nm) taps`;

val tap_name_def = Define `
  tap_name (conf : tap_config) nm = case conf of
    | Tap_Config fname _ => fname ++ "." ++ nm`;

val add_tap_def = Define `
  add_tap conf nm (to_display : 'a -> displayLang$sExp) (v : 'a) td
    = if should_tap conf nm
    then (case td of Tap_Data tds
        => Tap_Data ((tap_name conf nm,
            (\_. lang_to_json nm to_display v)) :: tds))
    else td`;

val tap_flat_def = Define `
  tap_flat conf v = add_tap conf "flat" flat_to_display_decs v`;

val tap_word_def = Define `
  tap_word conf v = add_tap conf "word" word_progs_to_display v`;

val tap_pat_def = Define`
  tap_pat conf v = add_tap conf "pat"
    (list_to_display (pat_to_display 0)) v`;

val tap_clos_def = Define`
  tap_clos conf v = add_tap conf "clos"
    (list_to_display (clos_to_display 0)) v`;

val _ = export_theory();
