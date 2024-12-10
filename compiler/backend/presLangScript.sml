(*
  Functions for converting various intermediate languages
  into displayLang representations.
*)
open preamble astTheory mlintTheory mloptionTheory
open flatLangTheory closLangTheory
     displayLangTheory source_to_flatTheory
     dataLangTheory wordLangTheory labLangTheory
     stackLangTheory bvlTheory clos_to_bvlTheory;

val _ = new_theory"presLang";

(* basics *)

Definition empty_item_def:
  empty_item name = String name
End

Definition num_to_display_def:
  num_to_display (n : num) = String (toString n)
End

Definition int_to_display_def:
  int_to_display (i : int) = String (toString i)
End

Definition string_imp_def:
  string_imp s = String (implode s)
End

Definition item_with_num_def:
  item_with_num name n = Item NONE name [num_to_display n]
End

Definition item_with_nums_def:
  item_with_nums name ns = Item NONE name (MAP num_to_display ns)
End

Definition bool_to_display_def:
  bool_to_display b = empty_item (if b then strlit "True" else strlit "False")
End

Definition num_to_hex_def:
  num_to_hex n =
    (if n < 16 then [] else num_to_hex (n DIV 16)) ++
    num_to_hex_digit (n MOD 16)
End

Definition separate_lines_def:
  separate_lines name xs = List (String name :: xs)
End

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

Definition num_to_hex_mlstring_def:
  num_to_hex_mlstring n = implode ("0x" ++ num_to_hex n)
End

Definition word_to_display_def:
  word_to_display w = empty_item (num_to_hex_mlstring (w2n w))
End

Definition item_with_word_def:
  item_with_word name w = Item NONE name [word_to_display w]
End

Definition lit_to_display_def:
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
    Item NONE (strlit "Word8") [word_to_display w])
  /\
  (lit_to_display (Word64 w) =
    Item NONE (strlit "Word64") [word_to_display w])
End

Definition list_to_display_def:
  (list_to_display f xs = displayLang$Tuple (MAP f xs))
End

Definition option_to_display_def:
  (option_to_display f opt = case opt of
          | NONE => empty_item (strlit "none")
          | SOME opt' => Item NONE (strlit "some") [f opt'])
End

(* source *)

Definition fp_cmp_to_display_def:
  fp_cmp_to_display cmp = case cmp of
    | FP_Less => empty_item (strlit "FP_Less")
    | FP_LessEqual => empty_item (strlit "FP_LessEqual")
    | FP_Greater => empty_item (strlit "FP_Greater")
    | FP_GreaterEqual => empty_item (strlit "FP_GreaterEqual")
    | FP_Equal => empty_item (strlit "FP_Equal")
End

Definition fp_uop_to_display_def:
  fp_uop_to_display op = case op of
    | FP_Abs => empty_item (strlit "FP_Abs")
    | FP_Neg => empty_item (strlit "FP_Neg")
    | FP_Sqrt => empty_item (strlit "FP_Sqrt")
End

Definition fp_bop_to_display_def:
  fp_bop_to_display op = case op of
    | fpValTree$FP_Add => empty_item (strlit "FP_Add")
    | FP_Sub => empty_item (strlit "FP_Sub")
    | FP_Mul => empty_item (strlit "FP_Mul")
    | FP_Div => empty_item (strlit "FP_Div")
End

Definition fp_top_to_display_def:
  fp_top_to_display op =
    case op of
      |FP_Fma => empty_item (strlit "FP_Fma")
End

Definition word_size_to_display_def:
  (word_size_to_display W8 = empty_item (strlit "W8"))
  /\
  (word_size_to_display W64 = empty_item (strlit "W64"))
End

Definition opn_to_display_def:
  (opn_to_display Plus = empty_item (strlit "Plus"))
  /\
  (opn_to_display Minus = empty_item (strlit "Minus"))
  /\
  (opn_to_display Times = empty_item (strlit "Times"))
  /\
  (opn_to_display Divide = empty_item (strlit "Divide"))
  /\
  (opn_to_display Modulo = empty_item (strlit "Modulo"))
End

Definition opb_to_display_def:
  (opb_to_display Lt = empty_item (strlit "Lt"))
  /\
  (opb_to_display Gt = empty_item (strlit "Gt"))
  /\
  (opb_to_display Leq = empty_item (strlit "Leq"))
  /\
  (opb_to_display Geq = empty_item (strlit "Geq"))
End

Definition opw_to_display_def:
  (opw_to_display Andw = empty_item (strlit "Andw"))
  /\
  (opw_to_display Orw = empty_item (strlit "Orw"))
  /\
  (opw_to_display Xor = empty_item (strlit "Xor"))
  /\
  (opw_to_display Add = empty_item (strlit "Add"))
  /\
  (opw_to_display Sub = empty_item (strlit "Sub"))
End

Definition shift_to_display_def:
  (shift_to_display Lsl = empty_item (strlit "Lsl"))
  /\
  (shift_to_display Lsr = empty_item (strlit "Lsr"))
  /\
  (shift_to_display Asr = empty_item (strlit "Asr"))
  /\
  (shift_to_display Ror = empty_item (strlit "Ror"))
End

Definition op_to_display_def:
  op_to_display (p:ast$op) =
  case p of
  | Opn op => opn_to_display op
  | Opb op => opb_to_display op
  | Opw ws op =>
      Item NONE (strlit "Opw") [ word_size_to_display ws; opw_to_display op ]
  | Shift ws sh num => Item NONE (strlit "Shift")
                            [word_size_to_display ws;
                             shift_to_display sh;
                             num_to_display num]
  | Equality => empty_item (strlit "Equality")
  | FP_cmp cmp => fp_cmp_to_display cmp
  | FP_uop op => fp_uop_to_display op
  | FP_bop op => fp_bop_to_display op
  | FP_top op => fp_top_to_display op
  | FpFromWord => empty_item (strlit "FpFromWord")
  | FpToWord => empty_item (strlit "FpToWord")
  | Real_cmp cmp => empty_item (strlit "Real_cmp")
  | Real_uop op => empty_item (strlit "Real_uop")
  | Real_bop op => empty_item (strlit "Real_bop")
  | RealFromFP => empty_item (strlit "RealFromFP")
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
  | Explode => empty_item (strlit "Explode")
  | Strsub => empty_item (strlit "Strsub")
  | Strlen => empty_item (strlit "Strlen")
  | Strcat => empty_item (strlit "Strcat")
  | VfromList => empty_item (strlit "VfromList")
  | Vsub => empty_item (strlit "Vsub")
  | Vlength => empty_item (strlit "Vlength")
  | Aalloc => empty_item (strlit "Aalloc")
  | AallocEmpty => empty_item (strlit "AallocEmpty")
  | AallocFixed => empty_item (strlit "AallocFixed")
  | Asub => empty_item (strlit "Asub")
  | Alength => empty_item (strlit "Alength")
  | Aupdate => empty_item (strlit "Aupdate")
  | Asub_unsafe => empty_item (strlit "Asub_unsafe")
  | Aupdate_unsafe => empty_item (strlit "Aupdate_unsafe")
  | Aw8sub_unsafe => empty_item (strlit "Aw8sub_unsafe")
  | Aw8update_unsafe => empty_item (strlit "Aw8update_unsafe")
  | ListAppend => empty_item (strlit "ListAppend")
  | ConfigGC => empty_item (strlit "ConfigGC")
  | FFI v35 => empty_item (strlit "FFI v35")
  | Eval => empty_item (strlit "Eval")
  | Env_id => empty_item (strlit "Eval")
  | ThunkOp t =>
       (case t of
        | AllocThunk b => Item NONE (strlit "AllocThunk") [bool_to_display b]
        | UpdateThunk b => Item NONE (strlit "UpdateThunk") [bool_to_display b]
        | ForceThunk => empty_item (strlit "ForceThunk"))
End

Definition lop_to_display_def:
  lop_to_display (c:ast$lop) =
  case c of
  | And => empty_item «And»
  | Or  => empty_item «Or»
End

Definition id_to_display_def:
  id_to_display (Short n) =
    Item NONE «Short» [String (implode n)] ∧
  id_to_display (Long n i) =
    Item NONE «Long» [String (implode n); id_to_display i]
End

Definition ast_t_to_display_def:
  ast_t_to_display c =
  case c of
  | Atvar n => Item NONE «Atvar» [String (implode n)]
  | Atfun t1 t2 => Item NONE «Atfun» [ast_t_to_display t1; ast_t_to_display t2]
  | Attup ts => Item NONE «Attup» [Tuple (MAP ast_t_to_display ts)]
  | Atapp ts id => Item NONE «Attup» [Tuple (MAP ast_t_to_display ts);
                                      id_to_display id]
Termination
  WF_REL_TAC ‘measure ast_t_size’
End

Definition pat_to_display_def:
  pat_to_display (c:ast$pat) =
  case c of
  | Pany => Item NONE «Pany» []
  | Pvar v => Item NONE «Pvar» [String (implode v)]
  | Plit l => Item NONE «Plit» [lit_to_display l]
  | Pcon opt_id pats =>
      Item NONE «Pcon» [option_to_display id_to_display opt_id;
                        Tuple (MAP pat_to_display pats)]
  | Pas t v => Item NONE «Pas» [pat_to_display t; String (implode v)]
  | Pref t => Item NONE «Pref» [pat_to_display t]
  | Ptannot x y => Item NONE «Ptannot» [pat_to_display x; ast_t_to_display y]
Termination
  WF_REL_TAC ‘measure pat_size’
End

Definition exp_to_display_def:
  exp_to_display (c:ast$exp) =
  case c of
  | Lit l => Item NONE «Lit» [lit_to_display l]
  | Raise e => Item NONE «Raise» [exp_to_display e]
  | Con opt_id es => Item NONE «Con» [option_to_display id_to_display opt_id;
                                      Tuple (MAP exp_to_display es)]
  | Var id => Item NONE «Var» [id_to_display id]
  | Fun n e => Item NONE «Fun» [String (implode n); exp_to_display e]
  | App op es => Item NONE «App» (op_to_display op ::
                                  MAP exp_to_display es)
  | Log lop e1 e2 => Item NONE «Log» [lop_to_display lop;
                                      exp_to_display e1;
                                      exp_to_display e2]
  | If e1 e2 e3 => Item NONE «If» [exp_to_display e1;
                                   exp_to_display e2;
                                   exp_to_display e3]
  | Let n_opt e1 e2 => Item NONE «Let»
      [option_to_display (λn. String (implode n)) n_opt;
       exp_to_display e1;
       exp_to_display e2]
  | Mat e pats => Item NONE «Mat»
      [exp_to_display e;
       Tuple (MAP (λ(p,e). Tuple [pat_to_display p; exp_to_display e]) pats)]
  | Handle e pats => Item NONE «Handle»
      [exp_to_display e;
       Tuple (MAP (λ(p,e). Tuple [pat_to_display p; exp_to_display e]) pats)]
  | Letrec fns e => Item NONE «Letrec»
      [Tuple (MAP (λ(m,n,e). Tuple [String (implode m);
                                    String (implode n);
                                    exp_to_display e]) fns);
       exp_to_display e]
  | Tannot e _ => Item NONE «Tannot» [exp_to_display e]
  | Lannot e _ => Item NONE «Lannot» [exp_to_display e]
  | FpOptimise _ e => Item NONE «FpOptimise» [exp_to_display e]
Termination
  WF_REL_TAC ‘measure exp_size’
End

Definition source_to_display_dec_def:
  source_to_display_dec (d:ast$dec) =
  case d of
  | Dlet _ pat e => Item NONE «Dlet» [pat_to_display pat; exp_to_display e]
  | Dletrec _ fns => Item NONE «Dletrec»
                          (MAP (λ(m,n,e). Tuple [String (implode m);
                                                 String (implode n);
                                                 exp_to_display e]) fns)
  | Dtype _ ts => Item NONE «Dtype» (MAP (λ(ns,n,z).
                    Tuple [Tuple (MAP (λn. String (implode n)) ns);
                           String (implode n);
                           Tuple (MAP (λ(n,tys). Tuple [String (implode n);
                              Tuple (MAP ast_t_to_display tys)]) z)]) ts)
  | Dtabbrev _ ns n ty =>
      Item NONE «Dtabbrev» [Tuple (MAP (λn. String (implode n)) ns);
                            String (implode n);
                            ast_t_to_display ty]
  | Dexn _ n tys => Item NONE «Dexn» [String (implode n);
                                      Tuple (MAP ast_t_to_display tys)]
  | Dmod n ds => Item NONE «Dmod» [String (implode n);
                                   Tuple (MAP source_to_display_dec ds)]
  | Dlocal xs ys => Item NONE «Dlocal» [Tuple (MAP source_to_display_dec xs);
                                        Tuple (MAP source_to_display_dec ys)]
  | Denv n => Item NONE «Denv» [String (implode n)]
Termination
  WF_REL_TAC ‘measure dec_size’
End

(* flatLang *)

Triviality MEM_pat_size:
  !pats a. MEM a (pats:flatLang$pat list) ==> pat_size a < pat1_size pats
Proof
  Induct \\ rw [] \\ rw [flatLangTheory.pat_size_def] \\ res_tac \\ fs []
QED

Definition opt_con_to_display_def:
  opt_con_to_display ocon = case ocon of
    | NONE => empty_item (strlit "ConIdNone")
    | SOME (c, NONE) => item_with_num (strlit "ConIdUntyped") c
    | SOME (c, SOME t) => item_with_nums (strlit "ConIdTyped") [c; t]
End

Definition flat_pat_to_display_def:
  flat_pat_to_display p =
    case p of
       | flatLang$Pvar varN => Item NONE (strlit "Pvar") [string_imp varN]
       | Pany => empty_item (strlit "Pany")
       | Plit lit => Item NONE (strlit "Plit") [lit_to_display lit]
       | flatLang$Pcon id pats => Item NONE (strlit "Pcon")
            (MAP flat_pat_to_display pats)
       | Pas pat varN => Item NONE (strlit "Pas") [flat_pat_to_display pat;
                                                   string_imp varN]
       | Pref pat => Item NONE (strlit "Pref") [flat_pat_to_display pat]
Termination
  WF_REL_TAC `measure pat_size` \\ rw []
  \\ imp_res_tac MEM_pat_size \\ fs []
End

Definition flat_op_to_display_def:
  flat_op_to_display op = case op of
    | Opn op => opn_to_display op
    | Opb op => opb_to_display op
    | Opw ws op =>
        Item NONE (strlit "Opw") [ word_size_to_display ws; opw_to_display op ]
    | Shift ws sh num => Item NONE (strlit "Shift") [
      word_size_to_display ws;
      shift_to_display sh;
      num_to_display num]
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
    | AallocFixed => empty_item (strlit "AallocFixed")
    | Asub => empty_item (strlit "Asub")
    | Asub_unsafe => empty_item (strlit "Asub_unsafe")
    | Alength => empty_item (strlit "Alength")
    | Aupdate => empty_item (strlit "Aupdate")
    | Aupdate_unsafe => empty_item (strlit "Aupdate_unsafe")
    | ListAppend => empty_item (strlit "ListAppend")
    | ConfigGC => empty_item (strlit "ConfigGC")
    | FFI s => Item NONE (strlit "FFI") [string_imp s]
    | Eval => empty_item (strlit "Eval")
    | ThunkOp t =>
       (case t of
        | AllocThunk b => Item NONE (strlit "AllocThunk") [bool_to_display b]
        | UpdateThunk b => Item NONE (strlit "UpdateThunk") [bool_to_display b]
        | ForceThunk => empty_item (strlit "ForceThunk"))
    | GlobalVarAlloc n => item_with_num (strlit "GlobalVarAlloc") n
    | GlobalVarInit n => item_with_num (strlit "GlobalVarInit") n
    | GlobalVarLookup n => item_with_num (strlit "GlobalVarLookup") n
    | TagLenEq n1 n2 => item_with_nums (strlit "TagLenEq") [n1; n2]
    | LenEq n1 => item_with_nums (strlit "LenEq") [n1]
    | El n => item_with_num (strlit "El") n
    | Id => empty_item (strlit "Id")
End

Triviality MEM_funs_size:
  !fs v1 v2 e. MEM (v1,v2,e) fs ==> flatLang$exp_size e < exp1_size fs
Proof
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Triviality MEM_exps_size:
  !exps e. MEM e exps ==> flatLang$exp_size e < exp6_size exps
Proof
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Triviality MEM_pats_size:
  !pats p e. MEM (p, e) pats ==> flatLang$exp_size e < exp3_size pats
Proof
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition add_name_hint_def:
  add_name_hint prefix name_hint =
    concat [prefix; strlit "<"; name_hint; strlit ">"]
End

Definition flat_to_display_def:
  (flat_to_display (flatLang$Raise tra exp) =
    Item (SOME tra) (strlit "raise") [flat_to_display exp])
  /\
  (flat_to_display (Handle tra exp pes) =
    Item (SOME tra) (strlit "handle") (flat_to_display exp
        :: MAP (\(pat,exp). displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp]) pes))
  /\
  (flat_to_display (Lit tra lit) = Item (SOME tra) (strlit "lit") [])
  /\
  (flat_to_display (flatLang$Con tra id_opt exps) =
    Item (SOME tra) (strlit "con") (opt_con_to_display id_opt
        :: MAP flat_to_display exps))
  /\
  (flat_to_display (Var_local tra varN) =
    Item (SOME tra) (strlit "var_local") [string_imp varN])
  /\
  (flat_to_display (Fun name_hint varN exp) =
    Item (SOME None) (add_name_hint (strlit "fun") (implode name_hint))
      [string_imp varN; flat_to_display exp])
  /\
  (flat_to_display (App tra op exps) =
    Item (SOME tra) (strlit "app") (flat_op_to_display op :: MAP flat_to_display exps))
  /\
  (flat_to_display (If tra exp1 exp2 exp3) =
    Item (SOME tra) (strlit "if") [flat_to_display exp1; flat_to_display exp2;
        flat_to_display exp3])
  /\
  (flat_to_display (Mat tra exp pes) =
    Item (SOME tra) (strlit "mat") (flat_to_display exp
        :: MAP (\(pat,exp). displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp]) pes))
  /\
  (flat_to_display (Let tra varN_opt exp1 exp2) =
    Item (SOME tra) (strlit "let") [option_to_display string_imp varN_opt;
        flat_to_display exp1; flat_to_display exp2])
  /\
  (flat_to_display (Letrec name_hint funs exp) =
    Item (SOME None) (add_name_hint (strlit "letrec") (implode name_hint))
        [Tuple (MAP (\(v1,v2,e). Tuple [string_imp v1; string_imp v2;
              flat_to_display e]) funs); flat_to_display exp]
  )
Termination
  WF_REL_TAC `inv_image $< (flatLang$exp_size)`
  \\ rw [flatLangTheory.exp_size_def]
  \\ imp_res_tac MEM_funs_size \\ fs []
  \\ imp_res_tac MEM_exps_size \\ fs []
  \\ imp_res_tac MEM_pats_size \\ fs []
End

Definition flat_to_display_dec_def:
  flat_to_display_dec (d:flatLang$dec) =
    case d of
       | Dlet exp => Item NONE (strlit "dlet") [flat_to_display exp]
       | Dtype mods con_arities => item_with_num (strlit "dtype") mods
       | Dexn n1 n2 => item_with_nums (strlit "dexn") [n1; n2]
End

(* clos to displayLang *)

Definition num_to_varn_def:
  num_to_varn n = if n < 26 then [CHR (97 + n)]
                  else (num_to_varn ((n DIV 26)-1)) ++ ([CHR (97 + (n MOD 26))])
Termination
  WF_REL_TAC `measure I` \\ rw [] \\ fs [DIV_LT_X]
End

Definition display_num_as_varn_def:
  display_num_as_varn n = string_imp (num_to_varn n)
End

Definition num_to_varn_list_def:
  num_to_varn_list h n =
    if n = 0 then [] else
      num_to_varn (h + n) :: num_to_varn_list h (n-1)
End

Definition attach_name_def:
  attach_name ns NONE = strlit "none" ∧
  attach_name ns (SOME d) =
    case lookup d ns of
    | NONE => toString d
    | SOME name => concat [name; strlit "@"; toString d]
End

Definition const_part_to_display_def:
  const_part_to_display (Int i : const_part) =
    Item NONE (strlit "Int") [int_to_display i] ∧
  const_part_to_display (Con t vs) =
    Item NONE (strlit "Con") [num_to_display t; Tuple (MAP num_to_display vs)] ∧
  const_part_to_display (Str s) =
    Item NONE (strlit "Str") [String (concat [strlit "\""; s; strlit "\""])] ∧
  const_part_to_display (W64 w) =
    Item NONE (strlit "W64") [word_to_display w]
End

Definition const_to_display_def:
  const_to_display (ConstInt i : const) =
    Item NONE (strlit "ConstInt") [int_to_display i] ∧
  const_to_display (ConstCons t vs) =
    Item NONE (strlit "ConstCons") [num_to_display t; Tuple (MAP const_to_display vs)] ∧
  const_to_display (ConstStr s) =
    Item NONE (strlit "ConstStr") [String (concat [strlit "\""; s; strlit "\""])] ∧
  const_to_display (ConstWord64 w) =
    Item NONE (strlit "ConstWord64") [word_to_display w]
Termination
  WF_REL_TAC ‘measure const_size’
End

Definition clos_op_to_display_def:
  clos_op_to_display ns op = case op of
    | Global num => item_with_num (strlit "Global") num
    | SetGlobal num => item_with_num (strlit "SetGlobal") num
    | AllocGlobal => String (strlit "AllocGlobal")
    | GlobalsPtr => String (strlit "GlobalsPtr")
    | SetGlobalsPtr => String (strlit "SetGlobalsPtr")
    | Cons num => item_with_num (strlit "Cons") num
    | Constant c => Item NONE (strlit "Constant") [const_to_display c]
    | ConsExtend num => item_with_num (strlit "ConsExtend") num
    | Build bs => Item NONE (strlit "Build") (MAP const_part_to_display bs)
    | El => String (strlit "El")
    | LengthBlock => String (strlit "LengthBlock")
    | Length => String (strlit "Length")
    | LengthByte => String (strlit "LengthByte")
    | RefByte b => Item NONE (strlit "RefByte") [bool_to_display b]
    | RefArray => String (strlit "RefArray")
    | DerefByte => String (strlit "DerefByte")
    | UpdateByte => String (strlit "UpdateByte")
    | ConcatByteVec => String (strlit "ConcatByteVec")
    | CopyByte b => Item NONE (strlit "CopyByte") [bool_to_display b]
    | ListAppend => String (strlit "ListAppend")
    | FromList num => item_with_num (strlit "FromList") num
    | FromListByte => String (strlit "FromListByte")
    | ToListByte => String (strlit "ToListByte")
    | LengthByteVec => String (strlit "LengthByteVec")
    | DerefByteVec => String (strlit "DerefByteVec")
    | TagLenEq n1 n2 => item_with_nums (strlit "TagLenEq") [n1; n2]
    | ElemAt num => item_with_num (strlit "ElemAt") num
    | LenEq num => item_with_num (strlit "LenEq") num
    | TagEq num => item_with_num (strlit "TagEq") num
    | Ref => String (strlit "Ref")
    | Update => String (strlit "Update")
    | Label num => Item NONE (strlit "Label") [String (attach_name ns (SOME num))]
    | FFI s => Item NONE (strlit "FFI") [string_imp s]
    | Equal => String (strlit "Equal")
    | EqualConst c => Item NONE (strlit "EqualConst") [const_part_to_display c]
    | Const i => Item NONE (strlit "Const") [int_to_display i]
    | Add => String (strlit "Add")
    | Sub => String (strlit "Sub")
    | Mult => String (strlit "Mult")
    | Div => String (strlit "Div")
    | Mod => String (strlit "Mod")
    | Less => String (strlit "Less")
    | LessEq => String (strlit "LessEq")
    | Greater => String (strlit "Greater")
    | GreaterEq => String (strlit "GreaterEq")
    | WordOp ws op =>
        Item NONE (strlit "WordOp") [ word_size_to_display ws; opw_to_display op ]
    | WordShift ws sh num => Item NONE (strlit "WordShift") [
      word_size_to_display ws;
      shift_to_display sh;
      num_to_display num
    ]
    | WordFromInt => String (strlit "WordFromInt")
    | WordToInt => String (strlit "WordToInt")
    | WordFromWord b => Item NONE (strlit "WordFromWord") [bool_to_display b]
    | FP_cmp cmp => fp_cmp_to_display cmp
    | FP_uop op => fp_uop_to_display op
    | FP_bop op => fp_bop_to_display op
    | FP_top op => fp_top_to_display op
    | BoundsCheckBlock => String (strlit "BoundsCheckBlock")
    | BoundsCheckArray => String (strlit "BoundsCheckArray")
    | BoundsCheckByte b => Item NONE (strlit "BoundsCheckByte") [bool_to_display b]
    | LessConstSmall num => item_with_num (strlit "LessConstSmall") num
    | closLang$ConfigGC => String (strlit "ConfigGC")
    | Install => String (strlit "Install")
End

Triviality MEM_clos_exps_size:
  !exps e. MEM e exps ==> closLang$exp_size e < exp3_size exps
Proof
  Induct \\ fs [closLangTheory.exp_size_def] \\ rw []
  \\ fs [closLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition commas_def:
  commas [] = strlit "" ∧
  commas [x] = x ∧
  commas (x::xs) = x ^ strlit "," ^ commas xs
End

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
Definition clos_to_display_def:
  (clos_to_display ns h (Var t n) =
    Item (SOME t) (strlit "var") [display_num_as_varn (h-n-1)]) /\
  (clos_to_display ns h (If t x1 x2 x3) =
    Item (SOME t) (strlit "if") [clos_to_display ns h x1; clos_to_display ns h x2;
        clos_to_display ns h x3]) /\
  (clos_to_display ns h (closLang$Let t xs x) =
    separate_lines (strlit "let")
        [Tuple (clos_to_display_lets ns h (LENGTH xs - 1) xs);
            clos_to_display ns (h + LENGTH xs) x]) /\
  (clos_to_display ns h (Raise t x) =
    Item (SOME t) (strlit "raise") [clos_to_display ns h x]) /\
  (clos_to_display ns h (Tick t x) =
    Item (SOME t) (strlit "tick") [clos_to_display ns h x]) /\
  (clos_to_display ns h (Handle t x y) =
    Item (SOME t) (strlit "handle")
        [clos_to_display ns h x; display_num_as_varn h;
            clos_to_display ns (h+1) y]) /\
  (clos_to_display ns h (Call t ticks dest xs) =
    Item (SOME t) (strlit "call")
      ([num_to_display ticks; String (attach_name ns (SOME dest))] ++
       MAP (clos_to_display ns h) xs)) /\
  (clos_to_display ns h (App t opt_n x xs) =
    Item (SOME t) (strlit "app")
        ([option_to_display num_to_display opt_n;
          clos_to_display ns h x] ++ MAP (clos_to_display ns h) xs)) /\
  (clos_to_display ns h (Fn name_hint n1 n2 vn x) =
    Item (SOME None) (add_name_hint (strlit "fn") name_hint)
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         list_to_display string_imp (num_to_varn_list h vn);
         clos_to_display ns h x]) /\
  (clos_to_display ns h (closLang$Letrec name_hint n1 n2 es e) =
    Item (SOME None) (add_name_hint (strlit "letrec") (commas name_hint))
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         Tuple (clos_to_display_letrecs ns h (LENGTH es-1) (LENGTH es) es);
         clos_to_display ns h e]) /\
  (clos_to_display ns h (Op t op xs) =
    Item (SOME t) (strlit "op") (clos_op_to_display LN op ::
        MAP (clos_to_display ns h) xs)) /\
  (clos_to_display_lets ns h i [] = []) /\
  (clos_to_display_lets ns h i (x::xs) =
    Tuple [display_num_as_varn (h+i); String (strlit "<-"); clos_to_display ns h x]
      :: clos_to_display_lets ns h (i-1) xs) /\
  (clos_to_display_letrecs ns h i len [] = []) /\
  (clos_to_display_letrecs ns h i len ((vn,e)::es) =
    Tuple [display_num_as_varn (h+i);
        list_to_display string_imp (num_to_varn_list (h+len-1) vn);
        clos_to_display ns (h+len+vn) e]
    :: clos_to_display_letrecs ns h (i-1) len es)
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL (_,_,e) => exp_size e
    | INR (INL (_,_,_,es)) => exp3_size es
    | INR (INR (_,_,_,_,es)) => exp1_size es)`
  \\ rw [closLangTheory.exp_size_def]
  \\ imp_res_tac MEM_clos_exps_size \\ fs []
End

Definition clos_fun_to_display_def:
  clos_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (REVERSE $ GENLIST display_num_as_varn argc);
           clos_to_display names argc body]
End

Definition clos_dec_to_display_def:
  clos_dec_to_display names dec =
    Tuple [String «dec»;
           clos_to_display names 0 dec]
End

(* bvl to displayLang *)

Triviality MEM_bvl_exps_size:
  !exps e. MEM e exps ==> bvl$exp_size e < exp1_size exps
Proof
  Induct \\ fs [bvlTheory.exp_size_def] \\ rw []
  \\ fs [bvlTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition bvl_to_display_def:
  (bvl_to_display ns h (Var n) =
    Item NONE (strlit "var") [display_num_as_varn (h-n-1)]) /\
  (bvl_to_display ns h (If x1 x2 x3) =
    Item NONE (strlit "if") [bvl_to_display ns h x1; bvl_to_display ns h x2;
        bvl_to_display ns h x3]) /\
  (bvl_to_display ns h (bvl$Let xs x) =
    separate_lines (strlit "let")
        (bvl_to_display_lets ns h (LENGTH xs - 1) xs ++
            [bvl_to_display ns (h + LENGTH xs) x])) /\
  (bvl_to_display ns h (Raise x) =
    Item NONE (strlit "raise") [bvl_to_display ns h x]) /\
  (bvl_to_display ns h (Tick x) =
    Item NONE (strlit "tick") [bvl_to_display ns h x]) /\
  (bvl_to_display ns h (Handle x y) =
    Item NONE (strlit "handle")
        [bvl_to_display ns h x; display_num_as_varn h;
            bvl_to_display ns (h+1) y]) /\
  (bvl_to_display ns h (Call ticks dest xs) =
    Item NONE (strlit "call")
         (String (attach_name ns dest) ::
          MAP (bvl_to_display ns h) xs)) /\
  (bvl_to_display ns h (Op op xs) =
    Item NONE (strlit "op") (clos_op_to_display ns op ::
                             MAP (bvl_to_display ns h) xs)) /\
  (bvl_to_display_lets ns h i [] = []) /\
  (bvl_to_display_lets ns h i (x::xs) =
    Tuple [display_num_as_varn (h+i); String (strlit "<-"); bvl_to_display ns h x]
    :: bvl_to_display_lets ns h (i-1) xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL (ns,h,x) => exp_size x
                                    | INR (ns,h,i,xs) => exp1_size xs’
End

Definition bvl_fun_to_display_def:
  bvl_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (REVERSE $ GENLIST display_num_as_varn argc);
           bvl_to_display names argc body]
End

(* bvi to displayLang *)

Triviality MEM_bvi_exps_size:
  !exps e. MEM e exps ==> bvi$exp_size e < exp2_size exps
Proof
  Induct \\ fs [bviTheory.exp_size_def] \\ rw []
  \\ fs [bviTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition bvi_to_display_def:
  (bvi_to_display ns h (Var n) =
    Item NONE (strlit "var") [display_num_as_varn (h-n-1)]) /\
  (bvi_to_display ns h (If x1 x2 x3) =
    Item NONE (strlit "if") [bvi_to_display ns h x1; bvi_to_display ns h x2;
        bvi_to_display ns h x3]) /\
  (bvi_to_display ns h (bvi$Let xs x) =
    separate_lines (strlit "let")
        (bvi_to_display_lets ns h (LENGTH xs - 1) xs ++
            [bvi_to_display ns (h + LENGTH xs) x])) /\
  (bvi_to_display ns h (Raise x) =
    Item NONE (strlit "raise") [bvi_to_display ns h x]) /\
  (bvi_to_display ns h (Tick x) =
    Item NONE (strlit "tick") [bvi_to_display ns h x]) /\
  (bvi_to_display ns h (Call ticks dest xs handler) =
    Item NONE (strlit "call")
         (String (attach_name ns dest) ::
          MAP (bvi_to_display ns h) xs ++
          (case handler of
           | NONE => []
           | SOME e => [Item NONE (strlit "handler") [display_num_as_varn h;
                                                      empty_item (strlit "->");
                                                      bvi_to_display ns (h+1) e]]))) /\
  (bvi_to_display ns h (Op op xs) =
    Item NONE (strlit "op") (clos_op_to_display ns op ::
                             MAP (bvi_to_display ns h) xs)) /\
  (bvi_to_display_lets ns h i [] = []) /\
  (bvi_to_display_lets ns h i (x::xs) =
    Tuple [display_num_as_varn (h+i); String (strlit "<-"); bvi_to_display ns h x]
    :: bvi_to_display_lets ns h (i-1) xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL (ns,h,x) => exp_size x
                                    | INR (ns,h,i,xs) => exp2_size xs’
End

Definition bvi_fun_to_display_def:
  bvi_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (REVERSE $ GENLIST display_num_as_varn argc);
           bvi_to_display names argc body]
End

(* dataLang *)

Definition num_set_to_display_def:
  num_set_to_display ns =
    String $ concat [strlit "{";
                     commas (MAP toString (MAP FST (sptree$toSortedAList ns)));
                     strlit "}"]
End

Definition data_seqs_def:
  data_seqs z =
    case z of
    | dataLang$Seq x y => Append (data_seqs x) (data_seqs y)
    | _ => List [z]
End

Triviality MEM_append_data_seqs:
  ∀x. MEM a (append (data_seqs x)) ⇒ prog_size a ≤ prog_size x
Proof
  Induct \\ simp [Once data_seqs_def,dataLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Definition data_prog_to_display_def:
  data_prog_to_display ns prog = case prog of
    | dataLang$Skip => empty_item (strlit "skip")
    | dataLang$Move x y => Tuple
        [num_to_display x; String (strlit ":="); num_to_display y]
    | Call rets target args NONE => Item NONE (strlit "call")
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) rets;
            String (attach_name ns target);
            list_to_display num_to_display args;
            empty_item (strlit "none")]
     | Call rets target args (SOME (v, handler)) => Item NONE (strlit "call")
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) rets;
            String (attach_name ns target);
            list_to_display num_to_display args;
            Item NONE (strlit "some") [Tuple [num_to_display v;
                data_prog_to_display ns handler]]]
    | Assign n op args n_set => Tuple
        [num_to_display n;
         String (strlit ":=");
         clos_op_to_display ns op;
            list_to_display num_to_display args;
            option_to_display num_set_to_display n_set]
    | Seq x y =>
        (let xs = append (Append (data_seqs x) (data_seqs y)) in
           separate_lines (strlit "seq") (MAP (data_prog_to_display ns) xs))
    | If n x y => Item NONE (strlit "if")
        [num_to_display n; data_prog_to_display ns x; data_prog_to_display ns y]
    | MakeSpace n ns => Item NONE (strlit "make_space")
        [num_to_display n; num_set_to_display ns]
    | Raise n => Item NONE (strlit "raise") [num_to_display n]
    | Return n => Item NONE (strlit "return") [num_to_display n]
    | Tick => empty_item (strlit "tick")
Termination
  WF_REL_TAC ‘measure $ prog_size o SND’
  \\ fs [append_thm] \\ rw []
  \\ imp_res_tac MEM_append_data_seqs \\ fs []
End

Definition data_fun_to_display_def:
  data_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (GENLIST num_to_display argc);
           data_prog_to_display names body]
End

(* asm *)

Definition asm_binop_to_display_def:
  asm_binop_to_display op = case op of
    | asm$Add => empty_item (strlit "Add")
    | Sub => empty_item (strlit "Sub")
    | And => empty_item (strlit "And")
    | Or => empty_item (strlit "Or")
    | Xor => empty_item (strlit "Xor")
End

Definition asm_reg_imm_to_display_def:
  asm_reg_imm_to_display reg_imm = case reg_imm of
    | asm$Reg reg => item_with_num (strlit "Reg") reg
    | Imm imm => item_with_word (strlit "Imm") imm
End

Definition asm_arith_to_display_def:
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
    | SubOverflow n1 n2 n3 n4 => item_with_nums (strlit "SubOverflow") [n1; n2; n3; n4]
End

Definition asm_addr_to_display_def:
  asm_addr_to_display addr = case addr of
    | Addr reg w => Item NONE (strlit "Addr")
                         [num_to_display reg; word_to_display w]
End

Definition asm_memop_to_display_def:
  asm_memop_to_display op = case op of
    | Load => empty_item (strlit "Load")
    | Load8 => empty_item (strlit "Load8")
    | Load32 => empty_item (strlit "Load32")
    | Store => empty_item (strlit "Store")
    | Store8 => empty_item (strlit "Store8")
    | Store32 => empty_item (strlit "Store32")
End

Definition asm_cmp_to_display_def:
  asm_cmp_to_display op = case op of
    | Equal => empty_item «Equal»
    | Lower => empty_item «Lower»
    | Less => empty_item «Less»
    | Test => empty_item «Test»
    | NotEqual => empty_item «NotEqual»
    | NotLower => empty_item «NotLower»
    | NotLess => empty_item «NotLess»
    | NotTest => empty_item «NotTest»
End

Definition asm_fp_to_display_def:
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
    | FPFromInt n1 n2 => item_with_nums (strlit "FPFromInt") [n1; n2]
End

Definition asm_inst_to_display_def:
  asm_inst_to_display inst = case inst of
    | asm$Skip => empty_item (strlit "Skip")
    | Const reg w => Item NONE (strlit "Const") [num_to_display reg;
                                                 word_to_display w]
    | Arith a => Item NONE (strlit "Arith") [asm_arith_to_display a]
    | Mem mop r addr => Item NONE (strlit "Mem") [asm_memop_to_display mop;
        num_to_display r; asm_addr_to_display addr]
    | FP fp => Item NONE (strlit "FP") [asm_fp_to_display fp]
End

Definition asm_asm_to_display_def:
  asm_asm_to_display inst = case inst of
    | Inst i => asm_inst_to_display i
    | Jump w => item_with_word «Jump» w
    | JumpCmp c r to w => Item NONE «JumpCmp»
      [asm_cmp_to_display c; num_to_display r; asm_reg_imm_to_display to;
       word_to_display w]
    | Call w => item_with_word «Call» w
    | JumpReg r => item_with_num «JumpReg>» r
    | Loc r w => Item NONE «Loc» [num_to_display r; word_to_display w]
End

(* stackLang *)

Definition store_name_to_display_def:
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
    | Temp w => item_with_word «Temp» w
End

Definition stack_seqs_def:
  stack_seqs z =
    case z of
    | stackLang$Seq x y => Append (stack_seqs x) (stack_seqs y)
    | _ => List [z]
End

Triviality MEM_append_stack_seqs:
  ∀x. MEM a (append (stack_seqs x)) ⇒ prog_size ARB a ≤ prog_size ARB x
Proof
  Induct \\ simp [Once stack_seqs_def,stackLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Definition stack_prog_to_display_def:
  stack_prog_to_display ns stackLang$Skip = empty_item «skip» ∧
  stack_prog_to_display ns (Inst i) = asm_inst_to_display i ∧
  stack_prog_to_display ns (Get n sn) = Tuple
    [num_to_display n; String (strlit "<-"); store_name_to_display sn] ∧
  stack_prog_to_display ns (Set sn n) = Tuple
    [store_name_to_display sn; String (strlit "<-"); num_to_display n] ∧
  stack_prog_to_display ns (OpCurrHeap b n1 n2) = Tuple
    [num_to_display n1; String (strlit ":="); String (strlit "CurrHeap");
     asm_binop_to_display b; num_to_display n2] ∧
  stack_prog_to_display ns (Call rh tgt eh) =
    Item NONE «call»
         [(case rh of
           | NONE => empty_item «tail»
           | SOME (p,lr,l1,l2) =>
               Item NONE «returning»
                    [num_to_display lr;
                     String (attach_name ns (SOME l1));
                     num_to_display l2;
                     stack_prog_to_display ns p]);
         (case tgt of
          | INL l => Item NONE «direct» [String (attach_name ns (SOME l))]
          | INR r => item_with_num «reg» r);
         (case eh of
          | NONE => empty_item «no_handler»
          | SOME (p,l1,l2) =>
              Item NONE «handler»
                   [String (attach_name ns (SOME l1));
                    num_to_display l2;
                    stack_prog_to_display ns p])] ∧
   stack_prog_to_display ns (Seq x y) =
        (let xs = append (Append (stack_seqs x) (stack_seqs y)) in
           separate_lines (strlit "seq") (MAP (stack_prog_to_display ns) xs)) ∧
   stack_prog_to_display ns (If c n to x y) = Item NONE «if»
        [Tuple [asm_cmp_to_display c; num_to_display n; asm_reg_imm_to_display to];
         stack_prog_to_display ns x;
         stack_prog_to_display ns y] ∧
   stack_prog_to_display ns (While c n to x) = Item NONE «while»
        [Tuple [asm_cmp_to_display c; num_to_display n; asm_reg_imm_to_display to];
         stack_prog_to_display ns x] ∧
   stack_prog_to_display ns (JumpLower n1 n2 n3) =
     item_with_nums «jump_lower» [n1; n2; n3] ∧
   stack_prog_to_display ns (Alloc n) = item_with_num «alloc» n ∧
   stack_prog_to_display ns (StoreConsts n1 n2 _) = item_with_nums «store_consts» [n1; n2] ∧
   stack_prog_to_display ns (Raise n) = item_with_num «raise» n ∧
   stack_prog_to_display ns (Return n1 n2) = item_with_nums «return» [n1; n2] ∧
   stack_prog_to_display ns (FFI nm cp cl ap al ra) = Item NONE «ffi»
        (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra]) ∧
   stack_prog_to_display ns (Tick) = empty_item «tick» ∧
   stack_prog_to_display ns (LocValue n1 n2 n3) =
     Item NONE «loc_value» [num_to_display n1;
                            String (attach_name ns (SOME n2));
                            num_to_display n3] ∧
   stack_prog_to_display ns (Install n1 n2 n3 n4 n5) =
     item_with_nums «install» [n1; n2; n3; n4; n5] ∧
   stack_prog_to_display ns (ShMemOp mop r a) =
     Item NONE (strlit "sh_mem") [asm_memop_to_display mop;
                                  num_to_display r; asm_addr_to_display a] ∧
   stack_prog_to_display ns (CodeBufferWrite n1 n2) =
     item_with_nums «code_buffer_write» [n1; n2] ∧
   stack_prog_to_display ns (DataBufferWrite n1 n2) =
     item_with_nums «data_buffer_write» [n1; n2] ∧
   stack_prog_to_display ns (RawCall n) =
     Item NONE «raw_call» [String (attach_name ns (SOME n))] ∧
   stack_prog_to_display ns (StackAlloc n) = item_with_num «stack_alloc» n ∧
   stack_prog_to_display ns (StackFree n) = item_with_num «stack_free» n ∧
   stack_prog_to_display ns (StackStore n m) =
     Tuple [String («stack[» ^ num_to_hex_mlstring n ^ «] := » ^ toString m)] ∧
   stack_prog_to_display ns (StackStoreAny n m) =
     Tuple [String («stack[var » ^ toString n ^ «] := » ^ toString m)] ∧
   stack_prog_to_display ns (StackLoad n m) =
     Tuple [String (concat [toString n;
                            strlit " := stack[";
                            num_to_hex_mlstring m; strlit"]"])] ∧
   stack_prog_to_display ns (StackLoadAny n m) =
     Tuple [String (concat [toString n;
                            strlit " := stack[var ";
                            toString m; strlit"]"])] ∧
   stack_prog_to_display ns (StackGetSize n) = item_with_num «stack_get_size» n ∧
   stack_prog_to_display ns (StackSetSize n) = item_with_num «stack_set_size» n ∧
   stack_prog_to_display ns (BitmapLoad n m) =
     Tuple [String (concat [toString n;
                            strlit " := bitmap[";
                            num_to_hex_mlstring m;
                            strlit"]"])] ∧
   stack_prog_to_display ns (Halt n) = item_with_num «halt» n
Termination
  WF_REL_TAC ‘measure $ prog_size ARB o SND’
  \\ gvs [append_thm] \\ rw []
  \\ imp_res_tac MEM_append_stack_seqs \\ fs []
End

Definition stack_fun_to_display_def:
  stack_fun_to_display names (n,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           stack_prog_to_display names body]
End

(* labLang *)

Definition lab_asm_to_display_def:
  lab_asm_to_display ns la = case la of
    | labLang$Jump (Lab s n) =>
        Item NONE «jump»
          [String (attach_name ns (SOME s)); num_to_display n]
    | JumpCmp c r ri (Lab s n) =>
        Item NONE «jump_cmp»
          [Tuple [asm_cmp_to_display c; num_to_display r;
                  asm_reg_imm_to_display ri];
           String (attach_name ns (SOME s)); num_to_display n]
    | Call (Lab s n) =>
        Item NONE «call»
          [String (attach_name ns (SOME s)); num_to_display n]
    | LocValue r (Lab s n) =>
        Item NONE «loc_value»
          [num_to_display r; String (attach_name ns (SOME s)); num_to_display n]
    | CallFFI name => Item NONE «call_FFI» [string_imp name]
    | Install => empty_item «install»
    | Halt => empty_item «halt»
End

Definition lab_line_to_display_def:
  lab_line_to_display ns line = case line of
    | Label s n le =>
        Item NONE «label» [String (attach_name ns (SOME s)); num_to_display n]
    | Asm aoc enc len => (case aoc of
      | Asmi i => Item NONE «asm» [asm_asm_to_display i]
      | Cbw r1 r2 => item_with_nums «cbw» [r1; r2]
      | ShareMem mop r a => Item NONE «share_mem» [asm_memop_to_display mop;
                                                   num_to_display r;
                                                   asm_addr_to_display a])
    | LabAsm la pos enc len => lab_asm_to_display ns la
End

Definition lab_fun_to_display_def:
  lab_fun_to_display names (Section n lines) =
    List (String (attach_name names (SOME n))
           :: MAP (lab_line_to_display names) lines)
End

(* wordLang *)

Definition word_seqs_def:
  word_seqs z =
    case z of
    | wordLang$Seq x y => Append (word_seqs x) (word_seqs y)
    | _ => List [z]
End

Triviality MEM_append_word_seqs:
  ∀x. MEM a (append (word_seqs x)) ⇒ prog_size ARB a ≤ prog_size ARB x
Proof
  Induct \\ simp [Once word_seqs_def,wordLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Triviality MEM_word_exps_size_ARB =
  wordLangTheory.MEM_IMP_exp_size |> Q.GEN `l` |> Q.SPEC `ARB`;

Definition word_exp_to_display_def:
  (word_exp_to_display (wordLang$Const v)
    = item_with_word (strlit "Const") v) /\
  (word_exp_to_display (Var n)
    = item_with_num (strlit "Var") n) /\
  (word_exp_to_display (Lookup st)
    = Item NONE (strlit "Lookup") [store_name_to_display st]) /\
  (word_exp_to_display (Load exp2)
    = Item NONE (strlit "MemLoad") [word_exp_to_display exp2]) /\
  (word_exp_to_display (Op bop exs)
    = Item NONE (strlit "Op") (asm_binop_to_display bop
        :: MAP word_exp_to_display exs)) /\
  (word_exp_to_display (Shift sh exp num)
    = Item NONE (strlit "Shift") [
      shift_to_display sh;
      word_exp_to_display exp;
      num_to_display num
    ])
Termination
  WF_REL_TAC `measure (wordLang$exp_size ARB)`
  \\ rw []
  \\ imp_res_tac MEM_word_exps_size_ARB
  \\ rw []
End

Definition ws_to_display_def:
  ws_to_display [] = [] ∧
  ws_to_display ((b,x)::xs) =
    Tuple [bool_to_display b; word_to_display x] :: ws_to_display xs
End

Definition word_prog_to_display_def:
  (word_prog_to_display ns Skip = empty_item (strlit "skip")) /\
  (word_prog_to_display ns (Move n mvs) = Item NONE (strlit "move")
    [num_to_display n; displayLang$Tuple (MAP (\(n1, n2). Tuple
        [num_to_display n1;
         String (strlit ":=");
         num_to_display n2]) mvs)]) /\
  (word_prog_to_display ns (Inst i) =
    Item NONE (strlit "inst") [asm_inst_to_display i]) /\
  (word_prog_to_display ns (Assign n exp) =
     Tuple [num_to_display n;
            String (strlit ":=");
            word_exp_to_display exp]) /\
  (word_prog_to_display ns (Get n sn) = Tuple
    [num_to_display n; String (strlit "<-"); store_name_to_display sn]) /\
  (word_prog_to_display ns (Set sn exp) = Tuple
    [store_name_to_display sn; String (strlit "<-"); word_exp_to_display exp]) /\
  (word_prog_to_display ns (Store exp n) = Tuple
    [String (strlit "mem"); word_exp_to_display exp;
     String (strlit ":="); num_to_display n]) /\
  (word_prog_to_display ns (ShareInst mop n exp) = Tuple
    [String (strlit "share_mem"); asm_memop_to_display mop;
     num_to_display n; word_exp_to_display exp]) /\
  (word_prog_to_display ns (MustTerminate prog) = Item NONE (strlit "must_terminate")
    [word_prog_to_display ns prog]) /\
  (word_prog_to_display ns (Call a b c d) = Item NONE (strlit "call")
    [word_prog_to_display_ret ns a;
     option_to_display (λn. String (attach_name ns (SOME n))) b;
     list_to_display num_to_display c;
     word_prog_to_display_handler ns d]) /\
  (word_prog_to_display ns (OpCurrHeap b n1 n2) = Tuple
    [num_to_display n1; String (strlit ":="); String (strlit "CurrHeap");
     asm_binop_to_display b; num_to_display n2]) /\
  (word_prog_to_display ns (Seq prog1 prog2) =
    (let xs = append (Append (word_seqs prog1) (word_seqs prog2)) in
       separate_lines (strlit "seq") (MAP (word_prog_to_display ns) xs))) /\
  (word_prog_to_display ns (If cmp n reg p1 p2) =
    Item NONE (strlit "if")
      [Tuple [asm_cmp_to_display cmp;
              num_to_display n;
              asm_reg_imm_to_display reg];
       word_prog_to_display ns p1; word_prog_to_display ns p2]) /\
  (word_prog_to_display ns (Alloc n ms) = Item NONE (strlit "alloc")
    [num_to_display n; num_set_to_display ms]) /\
  (word_prog_to_display ns (StoreConsts a b c d ws) = Item NONE (strlit "store_consts")
    [num_to_display a;
     num_to_display b;
     num_to_display c;
     num_to_display d;
     Tuple (ws_to_display ws)]) /\
  (word_prog_to_display ns (Raise n) = item_with_num (strlit "raise") n) /\
  (word_prog_to_display ns (Return n1 n2) = item_with_nums (strlit "return") [n1; n2]) /\
  (word_prog_to_display ns Tick = empty_item (strlit "tick")) /\
  (word_prog_to_display ns (LocValue n1 n2) =
    Item NONE (strlit "loc_value") [String (attach_name ns (SOME n1)); num_to_display n2]) /\
  (word_prog_to_display ns (Install n1 n2 n3 n4 ms) =
    Item NONE (strlit "install") (MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ms])) /\
  (word_prog_to_display ns (CodeBufferWrite n1 n2) =
    item_with_nums (strlit "code_buffer_write") [n1; n2]) /\
  (word_prog_to_display ns (DataBufferWrite n1 n2) =
    item_with_nums (strlit "data_buffer_write") [n1; n2]) /\
  (word_prog_to_display ns (FFI nm n1 n2 n3 n4 ms) =
    Item NONE (strlit "ffi") (string_imp nm :: MAP num_to_display [n1; n2; n3; n4]
        ++ [num_set_to_display ms])) /\
  (word_prog_to_display_ret ns NONE = empty_item (strlit "tail")) /\
  (word_prog_to_display_ret ns (SOME (n1, ms, prog, n2, n3)) =
    Item NONE (strlit "returning") [Tuple [num_to_display n1; num_set_to_display ms;
        word_prog_to_display ns prog;
        String (attach_name ns (SOME n2));
        num_to_display n3]]) /\
  (word_prog_to_display_handler ns NONE = empty_item (strlit "no_handler")) /\
  (word_prog_to_display_handler ns (SOME (n1, prog, n2, n3)) =
    Item NONE (strlit "handler") [Tuple [num_to_display n1;
        word_prog_to_display ns prog;
        String (attach_name ns (SOME n2));
        num_to_display n3]])
Termination
  WF_REL_TAC `measure (\x. case x of
        | INL (_,p) => wordLang$prog_size ARB p
        | INR (INL (_,v)) => wordLang$prog1_size ARB v
        | INR (INR (_,v)) => wordLang$prog3_size ARB v)`
  \\ rw [] \\ imp_res_tac MEM_append_word_seqs \\ rw []
End

Definition word_fun_to_display_def:
  word_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (GENLIST (λn. num_to_display (2 * n)) argc);
           word_prog_to_display names body]
End

(* tap configuration *)

Datatype:
  tap_config = <| explore_flag : bool |>
End

Definition default_tap_config_def:
  default_tap_config = <| explore_flag := F |>
End

(* ------------------------- *)

Definition map_to_append_def:
  map_to_append f [] = Nil ∧
  map_to_append f (x::xs) = Append (List (f x)) (map_to_append f xs)
End

Definition source_to_strs_def:
  source_to_strs decs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   source_to_display_dec) decs
End

Definition flat_to_strs_def:
  flat_to_strs (decs:flatLang$dec list) =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   flat_to_display_dec) decs
End

Definition clos_to_strs_def:
  clos_to_strs (decs,funs) =
    let names = clos_to_bvl$get_src_names (decs ++ MAP (SND o SND) funs) LN in
      Append (map_to_append (v2strs (strlit "\n\n") o
                             display_to_str_tree o
                             clos_dec_to_display names) decs)
             (map_to_append (v2strs (strlit "\n\n") o
                             display_to_str_tree o
                             clos_fun_to_display names) funs)
End

Definition bvl_to_strs_def:
  bvl_to_strs names xs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   bvl_fun_to_display names) xs
End

val bvl_test =
  “concat $ append $ bvl_to_strs
     (insert 50 (strlit "foo") (insert 60 (strlit "bar") LN))
     [(50,2,Let [Var 0; Var 1]
              $ Op Add [Var 0; Var 1; Var 2; Var 3]);
      (60,2,Let [Var 0; Var 1]
              $ Call 0 (SOME 50) [Var 2; Var 0])]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))

Definition bvi_to_strs_def:
  bvi_to_strs names xs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   bvi_fun_to_display names) xs
End

val bvi_test =
  “concat $ append $ bvi_to_strs
     (insert 50 (strlit "foo") (insert 60 (strlit "bar") LN))
     [(50,2,Let [Var 0]
              $ Op Add [Var 0; Var 1; Var 2; Var 3]);
      (60,2,Let [Var 0; Var 1]
              $ Call 0 (SOME 50) [Var 2; Var 0] (SOME (Var 0)))]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))

Definition data_to_strs_def:
  data_to_strs names xs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   data_fun_to_display names) xs
End

val data_test =
  “concat $ append $ data_to_strs
     (insert 50 (strlit "foo") (insert 60 (strlit "bar") LN))
     [(50,2,Seq (Move 5 1) $
            Seq (Assign 3 Add [0;1] NONE) $
            Seq (Assign 6 Sub [5;3] NONE) $ Return 6);
      (60,2,Skip)]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))

Definition word_to_strs_def:
  word_to_strs names xs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   word_fun_to_display names) xs
End

Definition stack_to_strs_def:
  stack_to_strs names xs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   stack_fun_to_display names) xs
End

Definition lab_to_strs_def:
  lab_to_strs names xs =
    map_to_append (v2strs (strlit "\n\n") o
                   display_to_str_tree o
                   lab_fun_to_display names) xs
End

val lab_test =
  “concat $ append $ lab_to_strs
     (insert 50 (strlit "foo") (insert 60 (strlit "bar") LN))
     [Section 50 [Label 50 1 0;
                  Asm (Asmi (Inst (Const 5 (70w:word32)))) [] 0;
                  Label 50 2 0];
      Section 60 [Label 50 5 0]]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))

(*

val names_tm = “(insert 50 (strlit "foo") (insert 60 (strlit "bar") LN))”

val data_prog_tm =
    “[(50,2,Seq (Move 5 1) $
            Seq (Assign 3 Add [0;1] NONE) $
            Seq (Assign 6 Sub [5;3] NONE) $ Return 6);
      (60n,2n,Skip)]”

val _ = data_to_strs data_prog_tm names_tm |> print_strs

*)

val _ = export_theory();
