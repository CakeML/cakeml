(*
  Functions for converting various intermediate languages
  into displayLang representations.
*)
Theory presLang
Ancestors
  ast mlint mloption flatLang closLang displayLang source_to_flat
  dataLang wordLang labLang stackLang bvl bvi clos_to_bvl
Libs
  preamble

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
  string_imp s = String s
End

Definition item_with_num_def:
  item_with_num name n = Item NONE name [num_to_display n]
End

Definition item_with_nums_def:
  item_with_nums name ns = Item NONE name (MAP num_to_display ns)
End

Definition bool_to_display_def:
  bool_to_display b = empty_item (if b then «True» else «False»)
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
    Item NONE «IntLit» [empty_item (toString i)])
  /\
  (lit_to_display (Char c) =
    Item NONE «Char» [empty_item (implode ("#\"" ++ [c] ++ "\""))])
  /\
  (lit_to_display (StrLit s) =
    Item NONE «StrLit» [string_imp s])
  /\
  (lit_to_display (Word8 w) =
    Item NONE «Word8» [word_to_display w])
  /\
  (lit_to_display (Word64 w) =
    Item NONE «Word64» [word_to_display w])
  /\
  (lit_to_display (Float64 w) =
    Item NONE «Float64» [word_to_display w])
End

Overload list_to_display = ``λf xs. displayLang$Tuple (MAP f xs)``

Overload option_to_display =
  ``λf opt. case opt of
          | NONE => empty_item «none»
          | SOME opt' => Item NONE «some» [f opt']``
(* source *)

Definition fp_cmp_to_display_def:
  fp_cmp_to_display cmp = case cmp of
    | FP_Less => empty_item «FP_Less»
    | FP_LessEqual => empty_item «FP_LessEqual»
    | FP_Greater => empty_item «FP_Greater»
    | FP_GreaterEqual => empty_item «FP_GreaterEqual»
    | FP_Equal => empty_item «FP_Equal»
End

Definition fp_uop_to_display_def:
  fp_uop_to_display op = case op of
    | FP_Abs => empty_item «FP_Abs»
    | FP_Neg => empty_item «FP_Neg»
    | FP_Sqrt => empty_item «FP_Sqrt»
End

Definition fp_bop_to_display_def:
  fp_bop_to_display op = case op of
    | FP_Add => empty_item «FP_Add»
    | FP_Sub => empty_item «FP_Sub»
    | FP_Mul => empty_item «FP_Mul»
    | FP_Div => empty_item «FP_Div»
End

Definition fp_top_to_display_def:
  fp_top_to_display op =
    case op of
      |FP_Fma => empty_item «FP_Fma»
End

Definition word_size_to_display_def:
  (word_size_to_display W8 = empty_item «W8»)
  /\
  (word_size_to_display W64 = empty_item «W64»)
End

Definition opb_to_display_def:
  (opb_to_display Lt = empty_item «Lt»)
  /\
  (opb_to_display Gt = empty_item «Gt»)
  /\
  (opb_to_display Leq = empty_item «Leq»)
  /\
  (opb_to_display Geq = empty_item «Geq»)
End

Definition opw_to_display_def:
  (opw_to_display Andw = empty_item «Andw»)
  /\
  (opw_to_display Orw = empty_item «Orw»)
  /\
  (opw_to_display Xor = empty_item «Xor»)
  /\
  (opw_to_display Add = empty_item «Add»)
  /\
  (opw_to_display Sub = empty_item «Sub»)
End

Definition shift_to_display_def:
  (shift_to_display Lsl = empty_item «Lsl»)
  /\
  (shift_to_display Lsr = empty_item «Lsr»)
  /\
  (shift_to_display Asr = empty_item «Asr»)
  /\
  (shift_to_display Ror = empty_item «Ror»)
End

Definition thunk_mode_to_display_def:
  (thunk_mode_to_display Evaluated = empty_item «Evaluated»)
  /\
  (thunk_mode_to_display NotEvaluated = empty_item «NotEvaluated»)
End

Definition thunk_op_to_display_def:
  (thunk_op_to_display (AllocThunk m) =
    Item NONE «AllocThunk» [thunk_mode_to_display m]) ∧
  (thunk_op_to_display (UpdateThunk m) =
    Item NONE «UpdateThunk» [thunk_mode_to_display m]) ∧
  (thunk_op_to_display ForceThunk = empty_item «ForceThunk»)
End

Definition test_to_display_def:
  test_to_display Equal = empty_item «Equal» ∧
  test_to_display (Compare cmp) = Item NONE «Compare» [opb_to_display cmp] ∧
  test_to_display (AltCompare cmp) = Item NONE «AltCompare» [opb_to_display cmp]
End

Definition arith_to_display_def:
  arith_to_display Add = empty_item «Add» ∧
  arith_to_display Sub = empty_item «Sub» ∧
  arith_to_display Mul = empty_item «Mul» ∧
  arith_to_display Div = empty_item «Div» ∧
  arith_to_display Mod = empty_item «Mod» ∧
  arith_to_display And = empty_item «And» ∧
  arith_to_display Xor = empty_item «Xor» ∧
  arith_to_display Or  = empty_item «Or» ∧
  arith_to_display Neg = empty_item «Neg» ∧
  arith_to_display Not = empty_item «Not» ∧
  arith_to_display Abs = empty_item «Abs» ∧
  arith_to_display Sqrt = empty_item «Sqrt» ∧
  arith_to_display FMA = empty_item «FMA»
End

Definition prim_type_to_display_def:
  prim_type_to_display BoolT = empty_item «BoolT» ∧
  prim_type_to_display IntT = empty_item «IntT» ∧
  prim_type_to_display CharT = empty_item «CharT» ∧
  prim_type_to_display StrT = empty_item «StrT» ∧
  prim_type_to_display Float64T = empty_item «Float64T» ∧
  prim_type_to_display (WordT W8) = empty_item «WordT_W8» ∧
  prim_type_to_display (WordT W64) = empty_item «WordT_W64»
End

Definition lop_to_display_def:
  lop_to_display Andalso = empty_item «Andalso» ∧
  lop_to_display Orelse = empty_item «Orelse»
End

Definition op_to_display_def:
  op_to_display (p:ast$op) =
  case p of
  | Shift ws sh num => Item NONE «Shift»
                            [word_size_to_display ws;
                             shift_to_display sh;
                             num_to_display num]
  | Arith a ty => Item NONE «Arith»
                         [arith_to_display a;
                          prim_type_to_display ty]
  | FromTo ty1 ty2 => Item NONE «FromTo»
                         [prim_type_to_display ty1;
                          prim_type_to_display ty2]
  | Test test ty => Item NONE «Test»
                         [test_to_display test;
                          prim_type_to_display ty]
  | Equality => empty_item «Equality»
  | PtrEq => empty_item «PtrEq»
  | Opapp => empty_item «Opapp»
  | Opassign => empty_item «Opassign»
  | Opref => empty_item «Opref»
  | Opderef => empty_item «Opderef»
  | Aw8alloc => empty_item «Aw8alloc»
  | Aw8sub => empty_item «Aw8sub»
  | Aw8length => empty_item «Aw8length»
  | Aw8update => empty_item «Aw8update»
  | CopyStrStr => empty_item «CopyStrStr»
  | CopyStrAw8 => empty_item «CopyStrAw8»
  | CopyAw8Str => empty_item «CopyAw8Str»
  | CopyAw8Aw8 => empty_item «CopyAw8Aw8»
  | Implode => empty_item «Implode»
  | Explode => empty_item «Explode»
  | Strsub => empty_item «Strsub»
  | Strlen => empty_item «Strlen»
  | Strcat => empty_item «Strcat»
  | VfromList => empty_item «VfromList»
  | Vsub => empty_item «Vsub»
  | Vsub_unsafe => empty_item «Vsub_unsafe»
  | Vlength => empty_item «Vlength»
  | Aalloc => empty_item «Aalloc»
  | AallocEmpty => empty_item «AallocEmpty»
  | AallocFixed => empty_item «AallocFixed»
  | Asub => empty_item «Asub»
  | Alength => empty_item «Alength»
  | Aupdate => empty_item «Aupdate»
  | Asub_unsafe => empty_item «Asub_unsafe»
  | Aupdate_unsafe => empty_item «Aupdate_unsafe»
  | Aw8sub_unsafe => empty_item «Aw8sub_unsafe»
  | Aw8update_unsafe => empty_item «Aw8update_unsafe»
  | XorAw8Str_unsafe => empty_item «XorAw8Str_unsafe»
  | ListAppend => empty_item «ListAppend»
  | ConfigGC => empty_item «ConfigGC»
  | FFI v35 => empty_item «FFI v35»
  | Eval => empty_item «Eval»
  | Env_id => empty_item «Env_id»
  | ThunkOp t => thunk_op_to_display t
End

Definition id_to_display_def:
  id_to_display (Short n) =
    Item NONE «Short» [String n] ∧
  id_to_display (Long n i) =
    Item NONE «Long» [String n; id_to_display i]
End

Definition ast_t_to_display_def:
  (ast_t_to_display c =
  case c of
  | Atvar n => Item NONE «Atvar» [String n]
  | Atfun t1 t2 => Item NONE «Atfun» [ast_t_to_display t1; ast_t_to_display t2]
  | Attup ts => Item NONE «Attup» [Tuple (ast_t_to_display_list ts)]
  | Atapp ts id => Item NONE «Attup» [Tuple (ast_t_to_display_list ts);
                                      id_to_display id]) ∧
  (ast_t_to_display_list [] = []) ∧
  (ast_t_to_display_list (x::xs) =
    ast_t_to_display x :: ast_t_to_display_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL v => ast_t_size v | INR v => list_size ast_t_size v’
End

Definition pat_to_display_def:
  (pat_to_display (c:ast$pat) =
  case c of
  | Pany => Item NONE «Pany» []
  | Pvar v => Item NONE «Pvar» [String v]
  | Plit l => Item NONE «Plit» [lit_to_display l]
  | Pcon opt_id pats =>
      Item NONE «Pcon» [option_to_display id_to_display opt_id;
                        Tuple (pat_to_display_list pats)]
  | Pas t v => Item NONE «Pas» [pat_to_display t; String v]
  | Pref t => Item NONE «Pref» [pat_to_display t]
  | Ptannot x y => Item NONE «Ptannot» [pat_to_display x; ast_t_to_display y])
  ∧
  (pat_to_display_list [] = []) ∧
  (pat_to_display_list (x::xs) =
    pat_to_display x :: pat_to_display_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL v => pat_size v | INR v => list_size pat_size v’
End

Definition exp_to_display_def:
  (exp_to_display (c:ast$exp) =
  case c of
  | Lit l => Item NONE «Lit» [lit_to_display l]
  | Raise e => Item NONE «Raise» [exp_to_display e]
  | Con opt_id es => Item NONE «Con» [option_to_display id_to_display opt_id;
                                      Tuple (exp_to_display_list es)]
  | Var id => Item NONE «Var» [id_to_display id]
  | Fun n e => Item NONE «Fun» [String n; exp_to_display e]
  | App op es => Item NONE «App» (op_to_display op ::
                                  exp_to_display_list es)
  | Log lop e1 e2 => Item NONE «Log» [lop_to_display lop;
                                      exp_to_display e1;
                                      exp_to_display e2]
  | If e1 e2 e3 => Item NONE «If» [exp_to_display e1;
                                   exp_to_display e2;
                                   exp_to_display e3]
  | Let n_opt e1 e2 => Item NONE «Let»
      [option_to_display String n_opt;
       exp_to_display e1;
       exp_to_display e2]
  | Mat e pats =>
      Item NONE «Mat»
      [exp_to_display e;
       Tuple (pat_exp_to_display_list pats)]
  | Handle e pats =>
      Item NONE «Handle»
      [exp_to_display e;
       Tuple (pat_exp_to_display_list pats)]
  | Letrec fns e =>
      Item NONE «Letrec»
      [Tuple (fun_to_display_list fns);
       exp_to_display e]
  | Tannot e _ => Item NONE «Tannot» [exp_to_display e]
  | Lannot e _ => Item NONE «Lannot» [exp_to_display e]) ∧
  (exp_to_display_list [] = []) ∧
  (exp_to_display_list (x::xs) =
    exp_to_display x :: exp_to_display_list xs) ∧
  (pat_exp_to_display_list [] = []) ∧
  (pat_exp_to_display_list ((p,e)::xs) =
    Tuple [pat_to_display p; exp_to_display e]::
    pat_exp_to_display_list xs) ∧
  (fun_to_display_list [] = []) ∧
  (fun_to_display_list ((m,n,e)::xs) =
    Tuple [String m;
           String n;
           exp_to_display e] ::
    fun_to_display_list xs)
End

Definition source_to_display_dec_def:
  (source_to_display_dec (d:ast$dec) =
  case d of
  | Dlet _ pat e => Item NONE «Dlet» [pat_to_display pat; exp_to_display e]
  | Dletrec _ fns => Item NONE «Dletrec»
                          (MAP (λ(m,n,e). Tuple [String m;
                                                 String n;
                                                 exp_to_display e]) fns)
  | Dtype _ ts => Item NONE «Dtype» (MAP (λ(ns,n,z).
                    Tuple [Tuple (MAP String ns);
                           String n;
                           Tuple (MAP (λ(n,tys). Tuple [String n;
                              Tuple (MAP ast_t_to_display tys)]) z)]) ts)
  | Dtabbrev _ ns n ty =>
      Item NONE «Dtabbrev» [Tuple (MAP String ns);
                            String n;
                            ast_t_to_display ty]
  | Dexn _ n tys => Item NONE «Dexn» [String n;
                                      Tuple (MAP ast_t_to_display tys)]
  | Dmod n ds => Item NONE «Dmod» [String n;
                                   Tuple (source_to_display_dec_list ds)]
  | Dlocal xs ys => Item NONE «Dlocal» [Tuple (source_to_display_dec_list xs);
                                        Tuple (source_to_display_dec_list ys)]
  | Denv n => Item NONE «Denv» [String n])  ∧
  (source_to_display_dec_list [] = []) ∧
  (source_to_display_dec_list (x::xs) =
    source_to_display_dec x :: source_to_display_dec_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL v => dec_size v | INR v => list_size dec_size v’
End

(* flatLang *)

Theorem MEM_pat_size[local]:
  !pats a. MEM a (pats:flatLang$pat list) ==> pat_size a < pat1_size pats
Proof
  Induct \\ rw [] \\ rw [flatLangTheory.pat_size_def] \\ res_tac \\ fs []
QED

Definition opt_con_to_display_def:
  opt_con_to_display ocon = case ocon of
    | NONE => empty_item «ConIdNone»
    | SOME (c, NONE) => item_with_num «ConIdUntyped» c
    | SOME (c, SOME t) => item_with_nums «ConIdTyped» [c; t]
End

Definition flat_pat_to_display_def:
  (flat_pat_to_display p =
    case p of
       | flatLang$Pvar varN => Item NONE «Pvar» [string_imp varN]
       | Pany => empty_item «Pany»
       | Plit lit => Item NONE «Plit» [lit_to_display lit]
       | flatLang$Pcon id pats => Item NONE «Pcon»
            (flat_pat_to_display_list pats)
       | Pas pat varN => Item NONE «Pas» [flat_pat_to_display pat;
                                                   string_imp varN]
       | Pref pat => Item NONE «Pref» [flat_pat_to_display pat])  ∧
  (flat_pat_to_display_list [] = []) ∧
  (flat_pat_to_display_list (x::xs) =
    flat_pat_to_display x :: flat_pat_to_display_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL v => pat_size v | INR v => list_size pat_size v’
End

Definition flat_op_to_display_def:
  flat_op_to_display op = case op of
    | Src ast_op => op_to_display ast_op
    | GlobalVarAlloc n => item_with_num «GlobalVarAlloc» n
    | GlobalVarInit n => item_with_num «GlobalVarInit» n
    | GlobalVarLookup n => item_with_num «GlobalVarLookup» n
    | TagLenEq n1 n2 => item_with_nums «TagLenEq» [n1; n2]
    | LenEq n1 => item_with_nums «LenEq» [n1]
    | El n => item_with_num «El» n
    | Id => empty_item «Id»
End

Theorem MEM_funs_size[local]:
  !fs v1 v2 e. MEM (v1,v2,e) fs ==> flatLang$exp_size e < exp1_size fs
Proof
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Theorem MEM_exps_size[local]:
  !exps e. MEM e exps ==> flatLang$exp_size e < exp6_size exps
Proof
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Theorem MEM_pats_size[local]:
  !pats p e. MEM (p, e) pats ==> flatLang$exp_size e < exp3_size pats
Proof
  Induct \\ fs [flatLangTheory.exp_size_def] \\ rw []
  \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition add_name_hint_def:
  add_name_hint prefix name_hint =
    concat [prefix; «<»; name_hint; «>»]
End

Definition flat_to_display_def:
  (flat_to_display (flatLang$Raise tra exp) =
    Item (SOME tra) «raise» [flat_to_display exp])
  /\
  (flat_to_display (Handle tra exp pes) =
    Item (SOME tra) «handle» (flat_to_display exp
        :: pat_flat_to_display_list pes))
  /\
  (flat_to_display (Lit tra lit) = Item (SOME tra) «lit» [])
  /\
  (flat_to_display (flatLang$Con tra id_opt exps) =
    Item (SOME tra) «con» (opt_con_to_display id_opt
        :: flat_to_display_list exps))
  /\
  (flat_to_display (Var_local tra varN) =
    Item (SOME tra) «var_local» [string_imp varN])
  /\
  (flat_to_display (Fun name_hint varN exp) =
    Item (SOME None) (add_name_hint «fun» name_hint)
      [string_imp varN; flat_to_display exp])
  /\
  (flat_to_display (App tra op exps) =
    Item (SOME tra) «app» (flat_op_to_display op :: flat_to_display_list exps))
  /\
  (flat_to_display (If tra exp1 exp2 exp3) =
    Item (SOME tra) «if» [flat_to_display exp1; flat_to_display exp2;
        flat_to_display exp3])
  /\
  (flat_to_display (Mat tra exp pes) =
    Item (SOME tra) «mat» (flat_to_display exp
        :: pat_flat_to_display_list pes))
  /\
  (flat_to_display (Let tra varN_opt exp1 exp2) =
    Item (SOME tra) «let» [option_to_display string_imp varN_opt;
        flat_to_display exp1; flat_to_display exp2])
  /\
  (flat_to_display (Letrec name_hint funs exp) =
    Item (SOME None) (add_name_hint «letrec» name_hint)
        [Tuple (fun_flat_to_display_list funs); flat_to_display exp]
  )  ∧
  (flat_to_display_list [] = []) ∧
  (flat_to_display_list (x::xs) =
    flat_to_display x :: flat_to_display_list xs)  ∧
  (pat_flat_to_display_list [] = []) ∧
  (pat_flat_to_display_list ((pat,exp)::xs) =
    displayLang$Tuple [flat_pat_to_display pat; flat_to_display exp] :: pat_flat_to_display_list xs) ∧
  (fun_flat_to_display_list [] = []) ∧
  (fun_flat_to_display_list ((v1,v2,e)::xs) =
     Tuple [string_imp v1; string_imp v2; flat_to_display e] ::
        fun_flat_to_display_list xs)
End

(* clos to displayLang *)

Definition num_to_varn_aux_def:
  num_to_varn_aux n =
    if n < 26 then [CHR (97 + n)]
    else (num_to_varn_aux ((n DIV 26)-1)) ++ ([CHR (97 + (n MOD 26))])
Termination
  WF_REL_TAC `measure I` \\ rw [] \\ fs [DIV_LT_X]
End

Definition num_to_varn_def:
  num_to_varn n = implode (num_to_varn_aux n)
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
  attach_name ns NONE = «none» ∧
  attach_name ns (SOME d) =
    case lookup d ns of
    | NONE => toString d
    | SOME name => concat [name; «@»; toString d]
End

Definition const_part_to_display_def:
  const_part_to_display (Int i : const_part) =
    Item NONE «Int» [int_to_display i] ∧
  const_part_to_display (Con t vs) =
    Item NONE «Con» [num_to_display t; Tuple (MAP num_to_display vs)] ∧
  const_part_to_display (Str s) =
    Item NONE «Str» [String (concat [strlit "\""; s; strlit "\""])] ∧
  const_part_to_display (W64 w) =
    Item NONE «W64» [word_to_display w]
End

Definition const_to_display_def:
  const_to_display (ConstInt i : const) =
    Item NONE «ConstInt» [int_to_display i] ∧
  const_to_display (ConstCons t vs) =
    Item NONE «ConstCons» [num_to_display t; Tuple (const_to_display_list vs)] ∧
  const_to_display (ConstStr s) =
    Item NONE «ConstStr» [String (concat [strlit "\""; s; strlit "\""])] ∧
  const_to_display (ConstWord64 w) =
    Item NONE «ConstWord64» [word_to_display w] ∧
  (const_to_display_list [] = []) ∧
  (const_to_display_list (x::xs) =
    const_to_display x :: const_to_display_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL v => const_size v | INR v => list_size const_size v’
End

Definition clos_op_to_display_def:
  clos_op_to_display ns op = case op of
    | GlobOp (Global num) => item_with_num «Global» num
    | GlobOp (SetGlobal num) => item_with_num «SetGlobal» num
    | GlobOp AllocGlobal => String «AllocGlobal»
    | GlobOp GlobalsPtr => String «GlobalsPtr»
    | GlobOp SetGlobalsPtr => String «SetGlobalsPtr»
    | BlockOp (Cons num) => item_with_num «Cons» num
    | BlockOp (ElemAt num) => item_with_num «ElemAt» num
    | BlockOp (TagLenEq n1 n2) => item_with_nums «TagLenEq» [n1; n2]
    | BlockOp (BoolTest test) => Item NONE «BoolTest» [test_to_display test]
    | BlockOp BoolNot => String «BoolNot»
    | BlockOp (LenEq num) => item_with_num «LenEq» num
    | BlockOp (TagEq num) => item_with_num «TagEq» num
    | BlockOp LengthBlock => String «LengthBlock»
    | BlockOp BoundsCheckBlock => String «BoundsCheckBlock»
    | BlockOp (ConsExtend num) => item_with_num «ConsExtend» num
    | BlockOp (FromList num) => item_with_num «FromList» num
    | BlockOp ListAppend => String «ListAppend»
    | BlockOp (Constant c) => Item NONE «Constant» [const_to_display c]
    | BlockOp Equal => String «Equal»
    | BlockOp (EqualConst c) => Item NONE «EqualConst» [const_part_to_display c]
    | BlockOp (Build bs) => Item NONE «Build» (MAP const_part_to_display bs)
    | MemOp Ref => String «Ref»
    | MemOp Update => String «Update»
    | MemOp El => String «El»
    | MemOp Length => String «Length»
    | MemOp LengthByte => String «LengthByte»
    | MemOp (RefByte b) => Item NONE «RefByte» [bool_to_display b]
    | MemOp RefArray => String «RefArray»
    | MemOp DerefByte => String «DerefByte»
    | MemOp UpdateByte => String «UpdateByte»
    | MemOp ConcatByteVec => String «ConcatByteVec»
    | MemOp (CopyByte b) => Item NONE «CopyByte» [bool_to_display b]
    | MemOp FromListByte => String «FromListByte»
    | MemOp ToListByte => String «ToListByte»
    | MemOp LengthByteVec => String «LengthByteVec»
    | MemOp DerefByteVec => String «DerefByteVec»
    | MemOp BoundsCheckArray => String «BoundsCheckArray»
    | MemOp (BoundsCheckByte b) => Item NONE «BoundsCheckByte» [bool_to_display b]
    | MemOp closLang$ConfigGC => String «ConfigGC»
    | MemOp (StringCmp b opb) => Item NONE «StringCmp» [bool_to_display b;
                                                                 opb_to_display opb]
    | MemOp XorByte => String «XorByte»
    | Label num => Item NONE «Label» [String (attach_name ns (SOME num))]
    | FFI s => Item NONE «FFI» [string_imp s]
    | IntOp (Const i) => Item NONE «Const» [int_to_display i]
    | IntOp Add => String «Add»
    | IntOp Sub => String «Sub»
    | IntOp Mult => String «Mult»
    | IntOp Div => String «Div»
    | IntOp Mod => String «Mod»
    | IntOp Less => String «Less»
    | IntOp LessEq => String «LessEq»
    | IntOp Greater => String «Greater»
    | IntOp GreaterEq => String «GreaterEq»
    | IntOp (LessConstSmall num) => item_with_num «LessConstSmall» num
    | WordOp (WordOpw ws op) => Item NONE «WordOp»
                                     [word_size_to_display ws;
                                      opw_to_display op]
    | WordOp (WordShift ws sh num) => Item NONE «WordShift»
                                           [word_size_to_display ws;
                                            shift_to_display sh;
                                            num_to_display num]
    | WordOp (WordTest ws test) => Item NONE «WordTest»
                                        [word_size_to_display ws;
                                         test_to_display test]
    | WordOp WordFromInt => String «WordFromInt»
    | WordOp WordToInt => String «WordToInt»
    | WordOp (WordFromWord b) => Item NONE «WordFromWord» [bool_to_display b]
    | WordOp (FP_cmp cmp) => fp_cmp_to_display cmp
    | WordOp (FP_uop op) => fp_uop_to_display op
    | WordOp (FP_bop op) => fp_bop_to_display op
    | WordOp (FP_top op) => fp_top_to_display op
    | Install => String «Install»
    | ThunkOp t => thunk_op_to_display t
End

Theorem MEM_clos_exps_size[local]:
  !exps e. MEM e exps ==> closLang$exp_size e < exp3_size exps
Proof
  Induct \\ fs [closLangTheory.exp_size_def] \\ rw []
  \\ fs [closLangTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition commas_def:
  commas [] = «» ∧
  commas [x] = x ∧
  commas (x::xs) = x ^ «,» ^ commas xs
End

(* The clos_to_display ns function uses the same approach to de bruijn
   indices as the pat_to_display function *)
Definition clos_to_display_def:
  (clos_to_display ns h (Var t n) =
    Item (SOME t) «var» [display_num_as_varn (h-n-1)]) /\
  (clos_to_display ns h (If t x1 x2 x3) =
    Item (SOME t) «if» [clos_to_display ns h x1; clos_to_display ns h x2;
        clos_to_display ns h x3]) /\
  (clos_to_display ns h (closLang$Let t xs x) =
    separate_lines «let»
        [Tuple (clos_to_display_lets ns h (LENGTH xs - 1) xs);
            clos_to_display ns (h + LENGTH xs) x]) /\
  (clos_to_display ns h (Raise t x) =
    Item (SOME t) «raise» [clos_to_display ns h x]) /\
  (clos_to_display ns h (Tick t x) =
    Item (SOME t) «tick» [clos_to_display ns h x]) /\
  (clos_to_display ns h (Handle t x y) =
    Item (SOME t) «handle»
        [clos_to_display ns h x; display_num_as_varn h;
            clos_to_display ns (h+1) y]) /\
  (clos_to_display ns h (Call t ticks dest xs) =
    Item (SOME t) «call»
      ([num_to_display ticks; String (attach_name ns (SOME dest))] ++
       (clos_to_display_list ns h xs))) /\
  (clos_to_display ns h (App t opt_n x xs) =
    Item (SOME t) «app»
        ([option_to_display num_to_display opt_n;
          clos_to_display ns h x] ++ (clos_to_display_list ns h xs))) /\
  (clos_to_display ns h (Fn name_hint n1 n2 vn x) =
    Item (SOME None) (add_name_hint «fn» name_hint)
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         list_to_display string_imp (num_to_varn_list h vn);
         clos_to_display ns h x]) /\
  (clos_to_display ns h (closLang$Letrec name_hint n1 n2 es e) =
    Item (SOME None) (add_name_hint «letrec» (commas name_hint))
        [option_to_display num_to_display n1;
         option_to_display (list_to_display num_to_display) n2;
         Tuple (clos_to_display_letrecs ns h (LENGTH es-1) (LENGTH es) es);
         clos_to_display ns h e]) /\
  (clos_to_display ns h (Op t op xs) =
    Item (SOME t) «op» (clos_op_to_display LN op ::
        (clos_to_display_list ns h xs))) /\
  (clos_to_display_list ns h [] = []) ∧
  (clos_to_display_list ns h (x::xs) =
    clos_to_display ns h x :: clos_to_display_list ns h xs) ∧
  (clos_to_display_lets ns h i [] = []) /\
  (clos_to_display_lets ns h i (x::xs) =
    Tuple [display_num_as_varn (h+i); String «<-»; clos_to_display ns h x]
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
    | INR (INL (_,_,e)) => list_size exp_size e
    | INR (INR (INL (_,_,_,es))) => list_size exp_size es
    | INR (INR (INR (_,_,_,_,es))) => list_size (pair_size I exp_size) es)`>>
  rw[list_size_pair_size_MAP_FST_SND]
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

Theorem MEM_bvl_exps_size[local]:
  !exps e. MEM e exps ==> bvl$exp_size e < exp1_size exps
Proof
  Induct \\ fs [bvlTheory.exp_size_def] \\ rw []
  \\ fs [bvlTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition bvl_to_display_def:
  (bvl_to_display ns h (Var n) =
    Item NONE «var» [display_num_as_varn (h-n-1)]) /\
  (bvl_to_display ns h (If x1 x2 x3) =
    Item NONE «if» [bvl_to_display ns h x1; bvl_to_display ns h x2;
        bvl_to_display ns h x3]) /\
  (bvl_to_display ns h (bvl$Let xs x) =
    separate_lines «let»
        (bvl_to_display_lets ns h (LENGTH xs - 1) xs ++
            [bvl_to_display ns (h + LENGTH xs) x])) /\
  (bvl_to_display ns h (Raise x) =
    Item NONE «raise» [bvl_to_display ns h x]) /\
  (bvl_to_display ns h (Tick x) =
    Item NONE «tick» [bvl_to_display ns h x]) /\
  (bvl_to_display ns h (Handle x y) =
    Item NONE «handle»
        [bvl_to_display ns h x; display_num_as_varn h;
            bvl_to_display ns (h+1) y]) /\
  (bvl_to_display ns h (Call ticks dest xs) =
    Item NONE «call»
         (String (attach_name ns dest) ::
          (bvl_to_display_list ns h xs))) /\
  (bvl_to_display ns h (Force loc n) =
    Item NONE «force»
         [display_num_as_varn (h-n-1); String (attach_name ns (SOME loc))]) /\
  (bvl_to_display ns h (Op op xs) =
    Item NONE «op» (clos_op_to_display ns op ::
                             (bvl_to_display_list ns h xs)))  ∧
  (bvl_to_display_list ns h [] = []) ∧
  (bvl_to_display_list ns h (x::xs) =
    bvl_to_display ns h x :: bvl_to_display_list ns h xs) ∧
  (bvl_to_display_lets ns h i [] = []) /\
  (bvl_to_display_lets ns h i (x::xs) =
    Tuple [display_num_as_varn (h+i); String «<-»; bvl_to_display ns h x]
    :: bvl_to_display_lets ns h (i-1) xs)
Termination
  WF_REL_TAC ‘measure $ λx.
  case x of
    INL (ns,h,x) => exp_size x
  | INR (INL (ns,h,xs)) => list_size exp_size xs
  | INR (INR (ns,h,i,xs)) => list_size exp_size xs’
End

Definition bvl_fun_to_display_def:
  bvl_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (REVERSE $ GENLIST display_num_as_varn argc);
           bvl_to_display names argc body]
End

(* bvi to displayLang *)

Theorem MEM_bvi_exps_size[local]:
  !exps e. MEM e exps ==> bvi$exp_size e < exp2_size exps
Proof
  Induct \\ fs [bviTheory.exp_size_def] \\ rw []
  \\ fs [bviTheory.exp_size_def] \\ res_tac \\ fs []
QED

Definition bvi_to_display_def:
  (bvi_to_display ns h (Var n) =
    Item NONE «var» [display_num_as_varn (h-n-1)]) /\
  (bvi_to_display ns h (If x1 x2 x3) =
    Item NONE «if» [bvi_to_display ns h x1; bvi_to_display ns h x2;
        bvi_to_display ns h x3]) /\
  (bvi_to_display ns h (bvi$Let xs x) =
    separate_lines «let»
        (bvi_to_display_lets ns h (LENGTH xs - 1) xs ++
            [bvi_to_display ns (h + LENGTH xs) x])) /\
  (bvi_to_display ns h (Raise x) =
    Item NONE «raise» [bvi_to_display ns h x]) /\
  (bvi_to_display ns h (Tick x) =
    Item NONE «tick» [bvi_to_display ns h x]) /\
  (bvi_to_display ns h (Call ticks dest xs handler) =
    Item NONE «call»
         (String (attach_name ns dest) ::
          (bvi_to_display_list ns h xs) ++
          (case handler of
           | NONE => []
           | SOME e => [Item NONE «handler» [display_num_as_varn h;
                                                      empty_item «->»;
                                                      bvi_to_display ns (h+1) e]]))) /\
  (bvi_to_display ns h (Force loc n) =
    Item NONE «force»
         [display_num_as_varn (h-n-1); String (attach_name ns (SOME loc))]) ∧
  (bvi_to_display ns h (Op op xs) =
    Item NONE «op» (clos_op_to_display ns op ::
                             (bvi_to_display_list ns h xs)))  ∧
  (bvi_to_display_list ns h [] = []) ∧
  (bvi_to_display_list ns h (x::xs) =
    bvi_to_display ns h x :: bvi_to_display_list ns h xs) /\
  (bvi_to_display_lets ns h i [] = []) /\
  (bvi_to_display_lets ns h i (x::xs) =
    Tuple [display_num_as_varn (h+i); String «<-»; bvi_to_display ns h x]
    :: bvi_to_display_lets ns h (i-1) xs)
Termination
  WF_REL_TAC ‘measure $ λx.
  case x of
    INL (ns,h,x) => exp_size x
  | INR (INL (ns,h,xs)) => list_size exp_size xs
  | INR (INR (ns,h,i,xs)) => list_size exp_size xs’
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
    String $ concat [«{»;
                     commas (MAP toString (MAP FST (sptree$toSortedAList ns)));
                     «}»]
End

Definition data_seqs_def:
  data_seqs z =
    case z of
    | dataLang$Seq x y => Append (data_seqs x) (data_seqs y)
    | _ => List [z]
End

Theorem MEM_append_data_seqs[local]:
  ∀x. MEM a (append (data_seqs x)) ⇒ prog_size a ≤ prog_size x
Proof
  Induct \\ simp [Once data_seqs_def,dataLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Theorem list_size_append_data_seqs[local]:
  ∀x.
  list_size prog_size (append (data_seqs x)) =
  prog_size x + 1
Proof
  Induct \\ simp [Once data_seqs_def,dataLangTheory.prog_size_def,list_size_def,list_size_append]
QED

Definition data_prog_to_display_def:
  (data_prog_to_display 0 ns prog = empty_item «...» ) ∧
  (data_prog_to_display (SUC k) ns prog =
      case prog of
    | dataLang$Skip => empty_item «skip»
    | dataLang$Move x y => Tuple
        [num_to_display x; String «:=»; num_to_display y]
    | Call rets target args NONE => Item NONE «call»
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) rets;
            String (attach_name ns target);
            list_to_display num_to_display args;
            empty_item «none»]
     | Call rets target args (SOME (v, handler)) => Item NONE «call»
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) rets;
            String (attach_name ns target);
            list_to_display num_to_display args;
            Item NONE «some» [Tuple [num_to_display v;
                data_prog_to_display k ns handler]]]
    | Force ret loc src => Item NONE «force»
        [option_to_display (\(x, y). Tuple
                [num_to_display x; num_set_to_display y]) ret;
         num_to_display loc;
         num_to_display src]
    | Assign n op args n_set => Tuple
        [num_to_display n;
         String «:=»;
         clos_op_to_display ns op;
            list_to_display num_to_display args;
            option_to_display num_set_to_display n_set]
    | Seq x y =>
        (let xs = append (Append (data_seqs x) (data_seqs y)) in
           separate_lines «seq» (data_prog_to_display_list k ns xs))
    | If n x y => Item NONE «if»
        [num_to_display n; data_prog_to_display k ns x; data_prog_to_display k ns y]
    | MakeSpace n ns => Item NONE «make_space»
        [num_to_display n; num_set_to_display ns]
    | Raise n => Item NONE «raise» [num_to_display n]
    | Return n => Item NONE «return» [num_to_display n]
    | Tick => empty_item «tick»
  )  ∧
  (data_prog_to_display_list k ns [] = []) ∧
  (data_prog_to_display_list k ns (x::xs) =
    case k of
      0 => []
    | SUC k =>
    data_prog_to_display k ns x :: data_prog_to_display_list k ns xs)
Termination
  WF_REL_TAC ‘measure $ λx.
  case x of
    INL (k,_,_) => k
  | INR (k,_,_) => k’
End

Definition data_fun_to_display_def:
  data_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (GENLIST num_to_display argc);
           data_prog_to_display 1000000000 names body]
End

(* asm *)

Definition asm_binop_to_display_def:
  asm_binop_to_display op = case op of
    | asm$Add => empty_item «Add»
    | Sub => empty_item «Sub»
    | And => empty_item «And»
    | Or => empty_item «Or»
    | Xor => empty_item «Xor»
End

Definition asm_reg_imm_to_display_def:
  asm_reg_imm_to_display reg_imm = case reg_imm of
    | asm$Reg reg => item_with_num «Reg» reg
    | Imm imm => item_with_word «Imm» imm
End

Definition asm_arith_to_display_def:
  asm_arith_to_display op = case op of
    | asm$Binop bop n1 n2 reg_imm => Item NONE «Binop»
        [asm_binop_to_display bop; num_to_display n1; num_to_display n2;
            asm_reg_imm_to_display reg_imm]
    | asm$Shift sh n1 n2 n3 => Item NONE «Shift»
        [shift_to_display sh;
         num_to_display n1;
         num_to_display n2;
         asm_reg_imm_to_display n3]
    | Div n1 n2 n3 => item_with_nums «Div» [n1; n2; n3]
    | LongMul n1 n2 n3 n4 => item_with_nums «LongMul» [n1; n2; n3; n4]
    | LongDiv n1 n2 n3 n4 n5 => item_with_nums «LongDiv» [n1; n2; n3; n4; n5]
    | AddCarry n1 n2 n3 n4 => item_with_nums «AddCarry» [n1; n2; n3; n4]
    | AddOverflow n1 n2 n3 n4 => item_with_nums «AddOverflow» [n1; n2; n3; n4]
    | SubOverflow n1 n2 n3 n4 => item_with_nums «SubOverflow» [n1; n2; n3; n4]
End

Definition asm_addr_to_display_def:
  asm_addr_to_display addr = case addr of
    | Addr reg w => Item NONE «Addr»
                         [num_to_display reg; word_to_display w]
End

Definition asm_memop_to_display_def:
  asm_memop_to_display op = case op of
    | Load => empty_item «Load»
    | Load8 => empty_item «Load8»
    | Load16 => empty_item «Load16»
    | Load32 => empty_item «Load32»
    | Store => empty_item «Store»
    | Store8 => empty_item «Store8»
    | Store16 => empty_item «Store16»
    | Store32 => empty_item «Store32»
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
    | FPLess n1 n2 n3 => item_with_nums «FPLess» [n1; n2; n3]
    | FPLessEqual n1 n2 n3 => item_with_nums «FPLessEqual» [n1; n2; n3]
    | FPEqual n1 n2 n3 => item_with_nums «FPEqual» [n1; n2; n3]
    | FPAbs n1 n2 => item_with_nums «FPAbs» [n1; n2]
    | FPNeg n1 n2 => item_with_nums «FPNeg» [n1; n2]
    | FPSqrt n1 n2 => item_with_nums «FPSqrt» [n1; n2]
    | FPAdd n1 n2 n3 => item_with_nums «FPAdd» [n1; n2; n3]
    | FPSub n1 n2 n3 => item_with_nums «FPSub» [n1; n2; n3]
    | FPMul n1 n2 n3 => item_with_nums «FPMul» [n1; n2; n3]
    | FPDiv n1 n2 n3 => item_with_nums «FPDiv» [n1; n2; n3]
    | FPFma n1 n2 n3 => item_with_nums «FPFma» [n1; n2; n3]
    | FPMov n1 n2 => item_with_nums «FPMov» [n1; n2]
    | FPMovToReg n1 n2 n3 => item_with_nums «FPMovToReg» [n1; n2; n3]
    | FPMovFromReg n1 n2 n3 => item_with_nums «FPMovFromReg» [n1; n2; n3]
    | FPToInt n1 n2 => item_with_nums «FPToInt» [n1; n2]
    | FPFromInt n1 n2 => item_with_nums «FPFromInt» [n1; n2]
End

Definition asm_inst_to_display_def:
  asm_inst_to_display inst = case inst of
    | asm$Skip => empty_item «Skip»
    | Const reg w => Item NONE «Const» [num_to_display reg;
                                                 word_to_display w]
    | Arith a => Item NONE «Arith» [asm_arith_to_display a]
    | Mem mop r addr => Item NONE «Mem» [asm_memop_to_display mop;
        num_to_display r; asm_addr_to_display addr]
    | FP fp => Item NONE «FP» [asm_fp_to_display fp]
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

Theorem MEM_append_stack_seqs[local]:
  ∀x. MEM a (append (stack_seqs x)) ⇒ prog_size ARB a ≤ prog_size ARB x
Proof
  Induct \\ simp [Once stack_seqs_def,stackLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Theorem list_size_append_stack_seqs[local]:
  ∀x.
  list_size (prog_size ARB) (append (stack_seqs x)) =
  prog_size ARB x + 1
Proof
  Induct \\ simp [Once stack_seqs_def,stackLangTheory.prog_size_def,list_size_def,list_size_append]
QED

Definition stack_prog_to_display_def:
  stack_prog_to_display 0 ns prog = empty_item «...» ∧
  stack_prog_to_display (SUC k) ns stackLang$Skip = empty_item «skip» ∧
  stack_prog_to_display (SUC k) ns (Inst i) = asm_inst_to_display i ∧
  stack_prog_to_display (SUC k) ns (Get n sn) = Tuple
    [num_to_display n; String «<-»; store_name_to_display sn] ∧
  stack_prog_to_display (SUC k) ns (Set sn n) = Tuple
    [store_name_to_display sn; String «<-»; num_to_display n] ∧
  stack_prog_to_display (SUC k) ns (OpCurrHeap b n1 n2) = Tuple
    [num_to_display n1; String «:=»; String «CurrHeap»;
     asm_binop_to_display b; num_to_display n2] ∧
  stack_prog_to_display (SUC k) ns (Call rh tgt eh) =
    Item NONE «call»
         [(case rh of
           | NONE => empty_item «tail»
           | SOME (p,lr,l1,l2) =>
               Item NONE «returning»
                    [num_to_display lr;
                     String (attach_name ns (SOME l1));
                     num_to_display l2;
                     stack_prog_to_display k ns p]);
         (case tgt of
          | INL l => Item NONE «direct» [String (attach_name ns (SOME l))]
          | INR r => item_with_num «reg» r);
         (case eh of
          | NONE => empty_item «no_handler»
          | SOME (p,l1,l2) =>
              Item NONE «handler»
                   [String (attach_name ns (SOME l1));
                    num_to_display l2;
                    stack_prog_to_display k ns p])] ∧
   stack_prog_to_display (SUC k) ns (Seq x y) =
        (let xs = append (Append (stack_seqs x) (stack_seqs y)) in
           separate_lines «seq» (stack_prog_to_display_list k ns xs)) ∧
   stack_prog_to_display (SUC k) ns (If c n to x y) = Item NONE «if»
        [Tuple [asm_cmp_to_display c; num_to_display n; asm_reg_imm_to_display to];
         stack_prog_to_display k ns x;
         stack_prog_to_display k ns y] ∧
   stack_prog_to_display (SUC k) ns (Loop x) = Item NONE «loop»
        [stack_prog_to_display k ns x] ∧
   stack_prog_to_display (SUC k) ns (JumpLower n1 n2 n3) =
     item_with_nums «jump_lower» [n1; n2; n3] ∧
   stack_prog_to_display (SUC k) ns (Alloc n) = item_with_num «alloc» n ∧
   stack_prog_to_display (SUC k) ns (StoreConsts n1 n2 _) = item_with_nums «store_consts» [n1; n2] ∧
   stack_prog_to_display (SUC k) ns (Raise n) = item_with_num «raise» n ∧
   stack_prog_to_display (SUC k) ns (Return n) = item_with_num «return» n ∧
   stack_prog_to_display (SUC k) ns (Break n) = item_with_num «break» n ∧
   stack_prog_to_display (SUC k) ns (Continue n) = item_with_num «continue» n ∧
   stack_prog_to_display (SUC k) ns (FFI nm cp cl ap al ra) = Item NONE «ffi»
        (string_imp nm :: MAP num_to_display [cp; cl; ap; al; ra]) ∧
   stack_prog_to_display (SUC k) ns (Tick) = empty_item «tick» ∧
   stack_prog_to_display (SUC k) ns (LocValue n1 n2 n3) =
     Item NONE «loc_value» [num_to_display n1;
                            String (attach_name ns (SOME n2));
                            num_to_display n3] ∧
   stack_prog_to_display (SUC k) ns (Install n1 n2 n3 n4 n5) =
     item_with_nums «install» [n1; n2; n3; n4; n5] ∧
   stack_prog_to_display (SUC k) ns (ShMemOp mop r a) =
     Item NONE «sh_mem» [asm_memop_to_display mop;
                                  num_to_display r; asm_addr_to_display a] ∧
   stack_prog_to_display (SUC k) ns (CodeBufferWrite n1 n2) =
     item_with_nums «code_buffer_write» [n1; n2] ∧
   stack_prog_to_display (SUC k) ns (DataBufferWrite n1 n2) =
     item_with_nums «data_buffer_write» [n1; n2] ∧
   stack_prog_to_display (SUC k) ns (RawCall n) =
     Item NONE «raw_call» [String (attach_name ns (SOME n))] ∧
   stack_prog_to_display (SUC k) ns (StackAlloc n) = item_with_num «stack_alloc» n ∧
   stack_prog_to_display (SUC k) ns (StackFree n) = item_with_num «stack_free» n ∧
   stack_prog_to_display (SUC k) ns (StackStore n m) =
     Tuple [String («stack[» ^ num_to_hex_mlstring n ^ «] := » ^ toString m)] ∧
   stack_prog_to_display (SUC k) ns (StackStoreAny n m) =
     Tuple [String («stack[var » ^ toString n ^ «] := » ^ toString m)] ∧
   stack_prog_to_display (SUC k) ns (StackLoad n m) =
     Tuple [String (concat [toString n;
                            « := stack[»;
                            num_to_hex_mlstring m; «]»])] ∧
   stack_prog_to_display (SUC k) ns (StackLoadAny n m) =
     Tuple [String (concat [toString n;
                            « := stack[var »;
                            toString m; «]»])] ∧
   stack_prog_to_display (SUC k) ns (StackGetSize n) = item_with_num «stack_get_size» n ∧
   stack_prog_to_display (SUC k) ns (StackSetSize n) = item_with_num «stack_set_size» n ∧
   stack_prog_to_display (SUC k) ns (BitmapLoad n m) =
     Tuple [String (concat [toString n;
                            « := bitmap[»;
                            num_to_hex_mlstring m;
                            «]»])] ∧
   stack_prog_to_display (SUC k) ns (Halt n) = item_with_num «halt» n  ∧
  (stack_prog_to_display_list k ns [] = []) ∧
  (stack_prog_to_display_list k ns (x::xs) =
    case k of 0 => []
    | SUC k =>
    stack_prog_to_display k ns x :: stack_prog_to_display_list k ns xs)
Termination
  WF_REL_TAC ‘measure $ λx.
  case x of
    INL (k,_,_) => k
  | INR (k,_,_) => k’
End

Definition stack_fun_to_display_def:
  stack_fun_to_display names (n,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           stack_prog_to_display 1000000000 names body]
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

Theorem MEM_append_word_seqs[local]:
  ∀x. MEM a (append (word_seqs x)) ⇒ prog_size ARB a ≤ prog_size ARB x
Proof
  Induct \\ simp [Once word_seqs_def,wordLangTheory.prog_size_def]
  \\ rw [] \\ res_tac \\ gvs []
QED

Theorem MEM_word_exps_size_ARB[local] =
  wordLangTheory.MEM_IMP_exp_size |> Q.GEN `l` |> Q.SPEC `ARB`;

Definition word_exp_to_display_def:
  (word_exp_to_display (wordLang$Const v)
    = item_with_word «Const» v) /\
  (word_exp_to_display (Var n)
    = item_with_num «Var» n) /\
  (word_exp_to_display (Lookup st)
    = Item NONE «Lookup» [store_name_to_display st]) /\
  (word_exp_to_display (Load exp2)
    = Item NONE «MemLoad» [word_exp_to_display exp2]) /\
  (word_exp_to_display (Op bop exs)
    = Item NONE «Op» (asm_binop_to_display bop
        :: word_exp_to_display_list exs)) /\
  (word_exp_to_display (Shift sh exp exp1)
    = Item NONE «Shift» [
      shift_to_display sh;
      word_exp_to_display exp;
      word_exp_to_display exp1
    ]) ∧
  (word_exp_to_display_list [] = []) ∧
  (word_exp_to_display_list (x::xs) =
    word_exp_to_display x :: word_exp_to_display_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL v => wordLang$exp_size ARB v | INR v => list_size wordLang$exp_size ARB v’
End

Definition ws_to_display_def:
  ws_to_display [] = [] ∧
  ws_to_display ((b,x)::xs) =
    Tuple [bool_to_display b; word_to_display x] :: ws_to_display xs
End

Definition num_sets_to_display_def:
  num_sets_to_display (l,r) =
    Tuple [num_set_to_display l;
           num_set_to_display r]
End

Definition word_prog_to_display_def:
  (word_prog_to_display 0 ns x = empty_item «...») /\
  (word_prog_to_display (SUC k) ns Skip = empty_item «skip») /\
  (word_prog_to_display (SUC k) ns (Move n mvs) = Item NONE «move»
    [num_to_display n; displayLang$Tuple (MAP (\(n1, n2). Tuple
        [num_to_display n1;
         String «:=»;
         num_to_display n2]) mvs)]) /\
  (word_prog_to_display (SUC k) ns (Inst i) =
    Item NONE «inst» [asm_inst_to_display i]) /\
  (word_prog_to_display (SUC k) ns (Assign n exp) =
     Tuple [num_to_display n;
            String «:=»;
            word_exp_to_display exp]) /\
  (word_prog_to_display (SUC k) ns (Get n sn) = Tuple
    [num_to_display n; String «<-»; store_name_to_display sn]) /\
  (word_prog_to_display (SUC k) ns (Set sn exp) = Tuple
    [store_name_to_display sn; String «<-»; word_exp_to_display exp]) /\
  (word_prog_to_display (SUC k) ns (Store exp n) = Tuple
    [String «mem»; word_exp_to_display exp;
     String «:=»; num_to_display n]) /\
  (word_prog_to_display (SUC k) ns (ShareInst mop n exp) = Tuple
    [String «share_mem»; asm_memop_to_display mop;
     num_to_display n; word_exp_to_display exp]) /\
  (word_prog_to_display (SUC k) ns (MustTerminate prog) = Item NONE «must_terminate»
    [word_prog_to_display k ns prog]) /\
  (word_prog_to_display (SUC k) ns (Call a b c d) = Item NONE «call»
    [word_prog_to_display_ret k ns a;
     option_to_display (λn. String (attach_name ns (SOME n))) b;
     list_to_display num_to_display c;
     word_prog_to_display_handler k ns d]) /\
  (word_prog_to_display (SUC k) ns (OpCurrHeap b n1 n2) = Tuple
    [num_to_display n1; String «:=»; String «CurrHeap»;
     asm_binop_to_display b; num_to_display n2]) /\
  (word_prog_to_display (SUC k) ns (Seq prog1 prog2) =
    (let xs = append (Append (word_seqs prog1) (word_seqs prog2)) in
       separate_lines «seq» (word_prog_to_display_list k ns xs))) /\
  (word_prog_to_display (SUC k) ns (If cmp n reg p1 p2) =
    Item NONE «if»
      [Tuple [asm_cmp_to_display cmp;
              num_to_display n;
              asm_reg_imm_to_display reg];
       word_prog_to_display k ns p1; word_prog_to_display k ns p2]) /\
  (word_prog_to_display (SUC k) ns (Loop ns1 p ns2) =
    Item NONE «Loop»
      [num_set_to_display ns1;
       word_prog_to_display k ns p;
       num_set_to_display ns2]) /\
  (word_prog_to_display (SUC k) ns (Alloc n ms) = Item NONE «alloc»
    [num_to_display n; num_sets_to_display ms]) /\
  (word_prog_to_display (SUC k) ns (StoreConsts a b c d ws) = Item NONE «store_consts»
    [num_to_display a;
     num_to_display b;
     num_to_display c;
     num_to_display d;
     Tuple (ws_to_display ws)]) /\
  (word_prog_to_display (SUC k) ns (Raise n) = item_with_num «raise» n) /\
  (word_prog_to_display (SUC k) ns (Break n) = item_with_num «break» n) ∧
  (word_prog_to_display (SUC k) ns (Continue n) = item_with_num «continue» n) ∧
  (word_prog_to_display (SUC k) ns (Return n vs) =
     Item NONE «return»
       [num_to_display n;
        Tuple (MAP num_to_display vs)]) ∧
  (word_prog_to_display (SUC k) ns Tick = empty_item «tick») /\
  (word_prog_to_display (SUC k) ns (LocValue n1 n2) =
    Item NONE «loc_value» [String (attach_name ns (SOME n1)); num_to_display n2]) /\
  (word_prog_to_display (SUC k) ns (Install n1 n2 n3 n4 ms) =
    Item NONE «install» (MAP num_to_display [n1; n2; n3; n4]
        ++ [num_sets_to_display ms])) /\
  (word_prog_to_display (SUC k) ns (CodeBufferWrite n1 n2) =
    item_with_nums «code_buffer_write» [n1; n2]) /\
  (word_prog_to_display (SUC k) ns (DataBufferWrite n1 n2) =
    item_with_nums «data_buffer_write» [n1; n2]) /\
  (word_prog_to_display (SUC k) ns (FFI nm n1 n2 n3 n4 ms) =
    Item NONE «ffi» (string_imp nm :: MAP num_to_display [n1; n2; n3; n4]
        ++ [num_sets_to_display ms]))  ∧
  (word_prog_to_display_list k ns [] = []) ∧
  (word_prog_to_display_list k ns (x::xs) =
    case k of 0 => []
    | SUC k =>
    word_prog_to_display k ns x :: word_prog_to_display_list k ns xs) /\
  (word_prog_to_display_ret k ns NONE = empty_item «tail») /\
  (word_prog_to_display_ret k ns (SOME (vs, ms, prog, n2, n3)) =
    case k of 0 => empty_item «...»
    | SUC k =>
    Item NONE «returning» [Tuple [Tuple (MAP num_to_display vs); num_sets_to_display ms;
        word_prog_to_display k ns prog;
        String (attach_name ns (SOME n2));
        num_to_display n3]]) /\
  (word_prog_to_display_handler k ns NONE = empty_item «no_handler») /\
  (word_prog_to_display_handler k ns (SOME (n1, prog, n2, n3)) =
    case k of 0 => empty_item «...»
    | SUC k =>
    Item NONE «handler» [Tuple [num_to_display n1;
        word_prog_to_display k ns prog;
        String (attach_name ns (SOME n2));
        num_to_display n3]])
Termination
  WF_REL_TAC `measure (\x. case x of
        | INL (k,_) => k
        | INR (INL (k,_)) => k
        | INR (INR (INL (k,_))) => k
        | INR (INR (INR (k,_))) => k)`
End

Definition word_fun_to_display_def:
  word_fun_to_display names (n,argc,body) =
    Tuple [String «func»;
           String (attach_name names (SOME n));
           Tuple (GENLIST (λn. num_to_display (2 * n)) argc);
           word_prog_to_display 1000000000 names body]
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
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   source_to_display_dec) decs
End

Definition flat_to_strs_def:
  flat_to_strs (decs:flatLang$exp list) =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   flat_to_display) decs
End

Definition clos_to_strs_def:
  clos_to_strs (decs,funs) =
    let names = clos_to_bvl$get_src_names (decs ++ MAP (SND o SND) funs) LN in
      Append (map_to_append (str_tree_to_strs «\n\n» o
                             display_to_str_tree o
                             clos_dec_to_display names) decs)
             (map_to_append (str_tree_to_strs «\n\n» o
                             display_to_str_tree o
                             clos_fun_to_display names) funs)
End

Definition bvl_to_strs_def:
  bvl_to_strs names xs =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   bvl_fun_to_display names) xs
End

val bvl_test =
  “concat $ append $ bvl_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [(50,2,Let [Var 0; Var 1]
              $ Op (IntOp Add) [Var 0; Var 1; Var 2; Var 3]);
      (60,2,Let [Var 0; Var 1]
              $ Call 0 (SOME 50) [Var 2; Var 0])]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))

Definition bvi_to_strs_def:
  bvi_to_strs names xs =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   bvi_fun_to_display names) xs
End

val bvi_test =
  “concat $ append $ bvi_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [(50,2,Let [Var 0]
              $ Op (IntOp Add) [Var 0; Var 1; Var 2; Var 3]);
      (60,2,Let [Var 0; Var 1]
              $ Call 0 (SOME 50) [Var 2; Var 0] (SOME (Var 0)))]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"))

Definition data_to_strs_def:
  data_to_strs names xs =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   data_fun_to_display names) xs
End

val data_test =
  “concat $ append $ data_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [(50,2,Seq (Move 5 1) $
            Seq (Assign 3 (IntOp Add) [0;1] NONE) $
            Seq (Assign 6 (IntOp Sub) [5;3] NONE) $ Return 6);
      (60,2,Skip)]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"));

Definition word_to_strs_def:
  word_to_strs names xs =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   word_fun_to_display names) xs
End

Definition stack_to_strs_def:
  stack_to_strs names xs =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   stack_fun_to_display names) xs
End

Definition lab_to_strs_def:
  lab_to_strs names xs =
    map_to_append (str_tree_to_strs «\n\n» o
                   display_to_str_tree o
                   lab_fun_to_display names) xs
End

val lab_test =
  “concat $ append $ lab_to_strs
     (insert 50 «foo» (insert 60 «bar» LN))
     [Section 50 [Label 50 1 0;
                  Asm (Asmi (Inst (Const 5 (70w:word32)))) [] 0;
                  Label 50 2 0];
      Section 60 [Label 50 5 0]]”
  |> EVAL |> concl |> rand |> rand |> stringSyntax.fromHOLstring
  |> (fn t => (print "\n\n"; print t; print "\n"));

(*

val names_tm = “(insert 50 «foo» (insert 60 «bar» LN))”

val data_prog_tm =
    “[(50,2,Seq (Move 5 1) $
            Seq (Assign 3 Add [0;1] NONE) $
            Seq (Assign 6 Sub [5;3] NONE) $ Return 6);
      (60n,2n,Skip)]”

val _ = data_to_strs data_prog_tm names_tm |> print_strs

*)
