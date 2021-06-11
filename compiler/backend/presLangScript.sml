(*
  Functions for converting various intermediate languages
  into displayLang representations.
*)
open preamble astTheory mlintTheory mloptionTheory
open flatLangTheory closLangTheory
     displayLangTheory source_to_flatTheory
     dataLangTheory wordLangTheory labLangTheory
     stackLangTheory;

val _ = new_theory"presLang";

(* basics *)

val empty_item_def = Define`
  empty_item name = Item NONE name []`;

val num_to_display_def = Define`
  num_to_display (n : num) = String (toString n)`;

val int_to_display_def = Define`
  int_to_display (i : int) = String (toString i)`;

val string_imp_def = Define`
  string_imp s = String (implode s)`;

val item_with_num_def = Define`
  item_with_num name n = Item NONE name [num_to_display n]`;

val item_with_nums_def = Define`
  item_with_nums name ns = Item NONE name (MAP num_to_display ns)`;

val bool_to_display_def = Define`
  bool_to_display b = empty_item (if b then strlit "True" else strlit "False")`;

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
    Item NONE (strlit "StrLit") [string_imp s])
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
       | flatLang$Pvar varN => Item NONE (strlit "Pvar") [string_imp varN]
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
    | Aw8alloc => empty_item (strlit "Aw8alloc")
    | Aw8sub => empty_item (strlit "Aw8sub")
    | Aw8sub_unsafe => empty_item (strlit "Aw8sub_unsafe")
    | Aw8length => empty_item (strlit "Aw8length")
    | Aw8update => empty_item (strlit "Aw8update")
    | Aw8update_unsafe => empty_item (strlit "Aw8update_unsafe")
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
    | Explode => empty_item (strlit "Explode")
    | Strsub => empty_item (strlit "Strsub")
    | Strlen => empty_item (strlit "Strlen")
    | Strcat => empty_item (strlit "Strcat")
    | VfromList => empty_item (strlit "VfromList")
    | Vsub => empty_item (strlit "Vsub")
    | Vlength => empty_item (strlit "Vlength")
    | Aalloc => empty_item (strlit "Aalloc")
    | Asub => empty_item (strlit "Asub")
    | Asub_unsafe => empty_item (strlit "Asub_unsafe")
    | Alength => empty_item (strlit "Alength")
    | Aupdate => empty_item (strlit "Aupdate")
    | Aupdate_unsafe => empty_item (strlit "Aupdate_unsafe")
    | ListAppend => empty_item (strlit "ListAppend")
    | ConfigGC => empty_item (strlit "ConfigGC")
    | FFI s => Item NONE (strlit "FFI") [string_imp s]
    | Eval => empty_item (strlit "Eval")
    | GlobalVarAlloc n => item_with_num (strlit "GlobalVarAlloc") n
    | GlobalVarInit n => item_with_num (strlit "GlobalVarInit") n
    | GlobalVarLookup n => item_with_num (strlit "GlobalVarLookup") n
    | TagLenEq n1 n2 => item_with_nums (strlit "TagLenEq") [n1; n2]
    | LenEq n1 => item_with_nums (strlit "LenEq") [n1]
    | El n => item_with_num (strlit "El") n
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
    Item (SOME tra) (strlit "Var_local") [string_imp varN])
  /\
  (flat_to_display (Fun _ varN exp) =
    Item (SOME None) (strlit "Fun") [string_imp varN; flat_to_display exp])
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
    Item (SOME tra) (strlit "Let") [option_to_display string_imp varN_opt;
        flat_to_display exp1; flat_to_display exp2])
  /\
  (flat_to_display (Letrec _ funs exp) =
    Item (SOME None) (strlit "Letrec")
        [List (MAP (\(v1,v2,e). Tuple [string_imp v1; string_imp v2;
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
  display_num_as_varn n = string_imp (num_to_varn n)`;

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
    | closLang$String s => Item NONE (strlit "String") [string_imp s]
    | FromListByte => empty_item (strlit "FromListByte")
    | ToListByte => empty_item (strlit "ToListByte")
    | LengthByteVec => empty_item (strlit "LengthByteVec")
    | DerefByteVec => empty_item (strlit "DerefByteVec")
    | TagLenEq n1 n2 => item_with_nums (strlit "TagLenEq") [n1; n2]
    | ElemAt num => item_with_num (strlit "ElemAt") num
    | LenEq num => item_with_num (strlit "LenEq") num
    | TagEq num => item_with_num (strlit "TagEq") num
    | Ref => empty_item (strlit "Ref")
    | Update => empty_item (strlit "Update")
    | Label num => item_with_num (strlit "Label") num
    | FFI s => Item NONE (strlit "FFI") [string_imp s]
    | Equal => empty_item (strlit "Equal")
    | EqualInt i => Item NONE (strlit "EqualInt") [int_to_display i]
    | Const i => Item NONE (strlit "Const") [int_to_display i]
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
  (clos_to_display h (Fn _ n1 n2 vn x) =
    Item (SOME None) (strlit "Fn")
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         list_to_display string_imp (num_to_varn_list h vn);
         clos_to_display h x]) /\
  (clos_to_display h (closLang$Letrec _ n1 n2 es e) =
    Item (SOME None) (strlit "Letrec'")
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
        list_to_display string_imp (num_to_varn_list (h+len-1) vn);
        clos_to_display (h+len+vn) e]
    :: clos_to_display_letrecs h (i-1) len es)`
 (WF_REL_TAC `measure (\x. case x of
    | INL (_,e) => exp_size e
    | INR (INL (_,_,es)) => exp3_size es
    | INR (INR (_,_,_,es)) => exp1_size es)`
  \\ rw [closLangTheory.exp_size_def]
  \\ imp_res_tac MEM_clos_exps_size \\ fs []
 );

(* dataLang *)

val num_set_to_display_def = Define
  `num_set_to_display ns = List (MAP num_to_display
    (MAP FST (sptree$toAList ns)))`;

val data_prog_to_display_def  = Define `
  data_prog_to_display prog = case prog of
    | dataLang$Skip => empty_item (strlit "Skip")
    | dataLang$Move x y => Item NONE (strlit "Move")
        [num_to_display x; num_to_display y]
    | Call rets target args NONE => Item NONE (strlit "Call")
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) rets;
            option_to_display num_to_display target;
            list_to_display num_to_display args;
            empty_item (strlit "NONE")]
     | Call rets target args (SOME (v, handler)) => Item NONE (strlit "Call")
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) rets;
            option_to_display num_to_display target;
            list_to_display num_to_display args;
            Item NONE (strlit "SOME") [Tuple [num_to_display v;
                data_prog_to_display handler]]]
    | Assign n op ns n_set => Item NONE (strlit "Assign")
        [num_to_display n; clos_op_to_display op;
            list_to_display num_to_display ns;
            option_to_display num_set_to_display n_set]
    | Seq x y => Item NONE (strlit "Seq")
        [data_prog_to_display x; data_prog_to_display y]
    | If n x y => Item NONE (strlit "If")
        [num_to_display n; data_prog_to_display x; data_prog_to_display y]
    | MakeSpace n ns => Item NONE (strlit "MakeSpace")
        [num_to_display n; num_set_to_display ns]
    | Raise n => Item NONE (strlit "Raise") [num_to_display n]
    | Return n => Item NONE (strlit "Return") [num_to_display n]
    | Tick => empty_item (strlit "Tick")`;

val data_progs_to_display_def = Define`
  data_progs_to_display (ps, names) = list_to_display
    (\(n1, n2, prog). displayLang$Tuple [num_to_display n1;
        String (getOpt (sptree$lookup n1 names) (strlit "_unmatched"));
        num_to_display n2; data_prog_to_display prog]) ps`;

(* asm *)

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

val asm_cmp_to_display_def = Define`
  asm_cmp_to_display op = case op of
    | Equal => empty_item «Equal»
    | Lower => empty_item «Lower»
    | Less => empty_item «Less»
    | Test => empty_item «Test»
    | NotEqual => empty_item «NotEqual»
    | NotLower => empty_item «NotLower»
    | NotLess => empty_item «NotLess»
    | NotTest => empty_item «NotTest»`

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

val asm_asm_to_display_def = Define `
  asm_asm_to_display inst = case inst of
    | Inst i => asm_inst_to_display i
    | Jump w => item_with_num «Jump» (w2n w)
    | JumpCmp c r to w => Item NONE «JumpCmp»
      [asm_cmp_to_display c; num_to_display r; asm_reg_imm_to_display to;
       num_to_display (w2n w)]
    | Call w => item_with_num «Call» (w2n w)
    | JumpReg r => item_with_num «JumpReg>» r
    | Loc r w => item_with_nums «Loc» [r; w2n w]`

(* stackLang *)

val store_name_to_display_def = Define `
  store_name_to_display st = case st of
    | NextFree => empty_item «NextFree»
    | EndOfHeap => empty_item «EndOfHeap»
    | TriggerGC => empty_item «TriggerGC»
    | HeapLength => empty_item «HeapLength»
    | ProgStart => empty_item «ProgStart»
    | BitmapBase => empty_item «BitmapBase»
    | CurrHeap => empty_item «CurrHeap»
    | OtherHeap => empty_item «OtherHeap»
    | AllocSize => empty_item «AllocSize»
    | Globals => empty_item «Globals»
    | GlobReal => empty_item «GlobReal»
    | Handler => empty_item «Handler»
    | GenStart => empty_item «GenStart»
    | CodeBuffer => empty_item «CodeBuffer»
    | CodeBufferEnd => empty_item «CodeBufferEnd»
    | BitmapBuffer => empty_item «BitmapBuffer»
    | BitmapBufferEnd => empty_item «BitmapBufferEnd»
    | Temp n => item_with_num «Temp» (w2n n)`;

val stack_prog_to_display_def = Define`
  stack_prog_to_display prog = case prog of
    | stackLang$Skip => empty_item «Skip»
    | Inst i => asm_inst_to_display i
    | Get n sn => Item NONE «Get» [num_to_display n;
        store_name_to_display sn]
    | Set sn n => Item NONE «Set» [store_name_to_display sn;
        num_to_display n]
    | OpCurrHeap b n1 n2 => Item NONE «OpCurrHeap»
        [asm_binop_to_display b; num_to_display n1; num_to_display n2]
    | Call rh tgt eh => Item NONE «Call»
        [(case rh of
            | NONE => empty_item «Tail»
            | SOME (p,lr,l1,l2) => Item NONE «Return»
              [num_to_display lr; num_to_display l1; num_to_display l2;
               stack_prog_to_display p]);
         (case tgt of
            | INL l => item_with_num «Direct» l
            | INR r => item_with_num «Reg» r);
         (case eh of
            | NONE => empty_item «NoHandle»
            | SOME (p,l1,l2) => Item NONE «Handle»
              [num_to_display l1; num_to_display l2; stack_prog_to_display p])]
    | Seq x y => Item NONE «Seq»
        [stack_prog_to_display x; stack_prog_to_display y]
    | If c n to x y => Item NONE «If»
        [asm_cmp_to_display c; num_to_display n;
         asm_reg_imm_to_display to; stack_prog_to_display x;
         stack_prog_to_display y]
    | While c n to x => Item NONE «While»
        [asm_cmp_to_display c; num_to_display n;
         asm_reg_imm_to_display to; stack_prog_to_display x]
    | JumpLower n1 n2 n3 => item_with_nums «JumpLower» [n1; n2; n3]
    | Alloc n => item_with_num «Alloc» n
    | Raise n => item_with_num «Raise» n
    | Return n1 n2 => item_with_nums «Return» [n1; n2]
    | FFI nm cp cl ap al ra => Item NONE «FFI»
        (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra])
    | Tick => empty_item «Tick»
    | LocValue n1 n2 n3 => item_with_nums «LocValue» [n1; n2; n3]
    | Install n1 n2 n3 n4 n5 => item_with_nums «Install»
        [n1; n2; n3; n4; n5]
    | CodeBufferWrite n1 n2 => item_with_nums «CodeBufferWrite»
        [n1; n2]
    | DataBufferWrite n1 n2 => item_with_nums «DataBufferWrite»
        [n1; n2]
    | RawCall n => item_with_num «RawCall» n
    | StackAlloc n => item_with_num «StackAlloc» n
    | StackFree n => item_with_num «StackFree» n
    | StackStore n m => item_with_nums «StackStore» [n; m]
    | StackStoreAny n m => item_with_nums «StackStoreAny» [n; m]
    | StackLoad n m => item_with_nums «StackLoad» [n; m]
    | StackLoadAny n m => item_with_nums «StackLoadAny» [n; m]
    | StackGetSize n => item_with_num «RawCall» n
    | StackSetSize n => item_with_num «RawCall» n
    | BitmapLoad n m => item_with_nums «BitmapLoad» [n; m]
    | Halt n => item_with_num «Halt» n`;

val stack_progs_to_display_def = Define`
  stack_progs_to_display (ps,names) = list_to_display
    (\(n1, prog). displayLang$Tuple [num_to_display n1;
        String (getOpt (sptree$lookup n1 names) «NOT FOUND»);
        stack_prog_to_display prog]) ps`;

(* labLang *)

val lab_asm_to_display_def = Define`
  lab_asm_to_display la = case la of
    | labLang$Jump (Lab s n) => item_with_nums «Jump» [s; n]
    | JumpCmp c r ri (Lab s n) => Item NONE «JumpCmp»
      [asm_cmp_to_display c; num_to_display r;
       asm_reg_imm_to_display ri; num_to_display s; num_to_display n]
    | Call (Lab s n) => item_with_nums «Call» [s; n]
    | LocValue r (Lab s n) => item_with_nums «LocValue» [r; s; n]
    | CallFFI name => Item NONE «CallFFI» [string_imp name]
    | Install => empty_item «Install»
    | Halt => empty_item «Halt»`

val lab_line_to_display_def = Define`
  lab_line_to_display line = case line of
    | Label se nu le => item_with_nums «Label» [se; nu; le]
    | Asm aoc enc len => (case aoc of
      | Asmi i => Item NONE «Asm» [asm_asm_to_display i]
      | Cbw r1 r2 => item_with_nums «Cbw» [r1; r2])
    | LabAsm la pos enc len => lab_asm_to_display la`

val lab_secs_to_display_def = Define`
  lab_secs_to_display (ss,names) = list_to_display (\sec.
    case sec of Section n lines => displayLang$Tuple [num_to_display n;
        String (getOpt (sptree$lookup n names) «NOT FOUND»);
        list_to_display lab_line_to_display lines]) ss`

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
  (word_prog_to_display (OpCurrHeap b n1 n2) = Item NONE «OpCurrHeap»
    [asm_binop_to_display b; num_to_display n1; num_to_display n2]) /\
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
    Item NONE (strlit "FFI") (string_imp nm :: MAP num_to_display [n1; n2; n3; n4]
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
  word_progs_to_display (ps,names) = list_to_display
    (\(n1, n2, prog). displayLang$Tuple [num_to_display n1;
        String (getOpt (sptree$lookup n1 names) (strlit "NOT FOUND"));
        num_to_display n2; word_prog_to_display prog]) ps`;

(* Function to construct general functions from a language to JSON. Call with
* the name of the language and what function to use to convert it to
* displayLang to obtain a wrapper function which exports JSON. *)
val lang_to_json_def = Define`
  lang_to_json langN func =
    \ p . Object [
      (strlit "lang", String langN);
      (strlit "prog", display_to_json (func p))]`;

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
            (\_. lang_to_json nm to_display v) :: tds
    else tds`;

val tap_data_mlstrings_def = Define `
  tap_data_mlstrings td = case td of
    | Tap_Data nm json_f => (nm, json_to_mlstring (json_f ()))`;

val tap_flat_def = Define `
  tap_flat conf v = add_tap conf (strlit "flat") flat_to_display_decs v`;

val tap_clos_def = Define`
  tap_clos conf v = add_tap conf (strlit "clos")
    (list_to_display (clos_to_display 0)) v`;

val tap_data_lang_def = Define `
  tap_data_lang conf v = add_tap conf (strlit "data") data_progs_to_display v`;

val tap_word_def = Define `
  tap_word conf v = add_tap conf (strlit "word") word_progs_to_display v`;

val tap_stack_def = Define `
  tap_stack conf v = add_tap conf (strlit "stack") stack_progs_to_display v`;

val tap_lab_def = Define `
  tap_lab conf v = add_tap conf (strlit "lab") lab_secs_to_display v`;

val _ = export_theory();
