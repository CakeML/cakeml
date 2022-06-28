(*
  Compilation from flatLang to closLang. This compiler phase converts
  explicit variable names of flatLang to de Bruijn indexing of
  closLang. It also makes all division-by-zero and out-of-bounds
  exceptions raised explicitly.
*)
open preamble flatLangTheory closLangTheory

val _ = new_theory"flat_to_clos"

val _ = set_grammar_ancestry ["flatLang","closLang","backend_common"];

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition dest_pat_def:
  dest_pat [(Pvar v, h)] = SOME (v:string,h) /\
  dest_pat _ = NONE
End

Theorem dest_pat_pmatch:
  dest_pat x =
    case x of [(Pvar v, h)] => SOME (v:string,h) | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [dest_pat_def]
QED

Theorem dest_pat_thm:
  dest_pat pes = SOME (p_1,p_2) <=> pes = [(Pvar p_1, p_2)]
Proof
  Cases_on `pes` \\ fs [dest_pat_def]
  \\ Cases_on `t` \\ fs [dest_pat_def]
  \\ Cases_on `h` \\ fs [dest_pat_def]
  \\ Cases_on `q` \\ fs [dest_pat_def]
QED

Definition compile_lit_def:
  compile_lit t l =
    closLang$Op t
     (dtcase l of
      | IntLit i => Const i
      | Char c => Const (& (ORD c))
      | StrLit s => Constant (ConstStr (mlstring$implode s))
      | Word8 b => Const (& (w2n b))
      | Word64 w => Constant (ConstWord64 w)) []
End

Definition arg1_def:
  arg1 xs f =
    dtcase xs of [x] => f x | _ => closLang$Let None xs (Var None 0)
End

Theorem arg1_pmatch:
  arg1 xs f =
    case xs of [x] => f x | _ => closLang$Let None xs (Var None 0)
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [arg1_def]
QED

Definition arg2_def:
  arg2 xs f =
    dtcase xs of [x; y] => f x y | _ => closLang$Let None xs (Var None 0)
End

Theorem arg2_pmatch:
  arg2 xs f =
    case xs of [x; y] => f x y | _ => closLang$Let None xs (Var None 0)
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [arg2_def]
QED

Definition AllocGlobals_def:
  AllocGlobals t n =
    if n = 0 then Op t (Cons 0) [] else
    if n = 1 then Op t AllocGlobal [] else
      Let t [Op t AllocGlobal []] (AllocGlobals t (n-1:num))
End

fun var_fun m n = ``closLang$Var t ^(numSyntax.term_of_int(m-n))``;

fun check1 tm var =
``(If t (Op t Less [Op t (Const 0) []; ^(var 2)]) (Raise t (Op t (Cons subscript_tag) []))
  (If t (Op t Less [Op t (Const 0) []; ^(var 1)]) (Raise t (Op t (Cons subscript_tag) []))
  (If t (Op t (BoundsCheckByte T) [Op t Add [^(var 2); ^(var 1)]; ^(var 0)]) ^tm
  (Raise t (Op t (Cons subscript_tag) [])))))``;

val checkT = check1
  ``(closLang$Op t (CopyByte T) [Var t 0; Var t 1; Var t 2])`` (var_fun 2);

val checkF = check1
``(If t (Op t Less [Op t (Const 0) []; Var t 0]) (Raise t (Op t (Cons subscript_tag) []))
  (If t (Op t (BoundsCheckByte T) [Op t Add [Var t 2; Var t 0]; Var t 1])
     (Op t (CopyByte F) [Var t 0; Var t 1; Var t 2; Var t 3; Var t 4])
     (Raise t (Op t (Cons subscript_tag) []))))`` (var_fun 4);

Definition CopyByteStr_def:
  CopyByteStr t = ^checkT
End

Definition CopyByteAw8_def:
  CopyByteAw8 t = ^checkF
End

Definition compile_op_def:
  compile_op t op xs =
    dtcase op of
    | Opapp => arg2 xs (\x f. closLang$App t NONE f [x])
    | TagLenEq tag n => closLang$Op t (TagLenEq tag n) xs
    | LenEq n => closLang$Op t (LenEq n) xs
    | El n => arg1 xs (\x. Op t El [Op None (Const (& n)) []; x])
    | Ord => arg1 xs (\x. x)
    | Chr => Let t xs (If t (Op t Less [Op None (Const 0) []; Var t 0])
                        (Raise t (Op t (Cons chr_tag) []))
                        (If t (Op t Less [Var t 0; Op None (Const 255) []])
                          (Raise t (Op t (Cons chr_tag) []))
                          (Var t 0)))
    | Chopb chop => Op t (dtcase chop of
                          | Lt => Less
                          | Gt => Greater
                          | Leq => LessEq
                          | Geq => GreaterEq) xs
    | Opassign => arg2 xs (\x y. Op t Update [x; Op None (Const 0) []; y])
    | Opref => Op t Ref xs
    | ConfigGC => Op t ConfigGC xs
    | Opb l => Op t (dtcase l of
                     | Lt => Less
                     | Gt => Greater
                     | Leq => LessEq
                     | Geq => GreaterEq) xs
    | Opn Plus => Op t Add xs
    | Opn Minus => Op t Sub xs
    | Opn Times => Op t Mult xs
    | Opn Divide => Let t xs (If t (Op t Equal [Var t 0; Op t (Const 0) []])
                                    (Raise t (Op t (Cons div_tag) []))
                                    (Op t Div [Var t 0; Var t 1]))
    | Opn Modulus => Let t xs (If t (Op t Equal [Var t 0; Op t (Const 0) []])
                                    (Raise t (Op t (Cons div_tag) []))
                                    (Op t Mod [Var t 0; Var t 1]))
    | GlobalVarAlloc n => Let t xs (AllocGlobals t n)
    | GlobalVarInit n => Op t (SetGlobal n) xs
    | GlobalVarLookup n => Op t (Global n) xs
    | Equality => Op t Equal xs
    | FFI n => Op t (FFI n) xs
    | ListAppend => Op t ListAppend xs
    | Vlength => Op t LengthBlock xs
    | Alength => Op t Length xs
    | Implode => Op t FromListByte xs
    | Explode => Op t ToListByte xs
    | Strlen => Op t LengthByteVec xs
    | Strcat => Op t ConcatByteVec xs
    | CopyStrStr => Let t xs (CopyByteStr t)
    | CopyStrAw8 => Let t xs (CopyByteAw8 t)
    | CopyAw8Str => Let t xs (CopyByteStr t)
    | CopyAw8Aw8 => Let t xs (CopyByteAw8 t)
    | VfromList => Op t (FromList 0) xs
    | WordFromInt W64 => Op t WordFromInt xs
    | WordToInt W64 => Op t WordToInt xs
    | WordFromInt W8 => arg1 xs (\x. Op t Mod [Op t (Const 256) []; x])
    | WordToInt W8 => arg1 xs (\x. x)
    | Aw8length => Op t LengthByte xs
    | AallocFixed => Op t Ref xs
    | Aalloc => Let t xs (If t (Op t Less [Op t (Const 0) []; Var t 1])
                               (Raise t (Op t (Cons subscript_tag) []))
                               (Op t RefArray [Var t 0; Var t 1]))
    | Aw8alloc => Let t xs (If t (Op t Less [Op t (Const 0) []; Var t 1])
                                 (Raise t (Op t (Cons subscript_tag) []))
                                 (Op t (RefByte F) [Var t 0; Var t 1]))
    | Vsub => Let t xs (If t (Op t BoundsCheckBlock [Var t 0; Var t 1])
                             (Op t El [Var t 0; Var t 1])
                             (Raise t (Op t (Cons subscript_tag) [])))
    | Asub => Let t xs (If t (Op t BoundsCheckArray [Var t 0; Var t 1])
                             (Op t El [Var t 0; Var t 1])
                             (Raise t (Op t (Cons subscript_tag) [])))
    | Asub_unsafe => Op t El xs
    | Aupdate => Let t xs (If t (Op t BoundsCheckArray [Var t 1; Var t 2])
                                (Op t Update [Var t 0; Var t 1; Var t 2])
                                (Raise t (Op t (Cons subscript_tag) [])))
    | Aupdate_unsafe => Op t Update xs
    | Aw8sub => Let t xs (If t (Op t (BoundsCheckByte F) [Var t 0; Var t 1])
                               (Op t DerefByte [Var t 0; Var t 1])
                               (Raise t (Op t (Cons subscript_tag) [])))
    | Aw8sub_unsafe => Op t DerefByte xs
    | Aw8update => Let t xs (If t (Op t (BoundsCheckByte F) [Var t 1; Var t 2])
                                  (Op t UpdateByte [Var t 0; Var t 1; Var t 2])
                                  (Raise t (Op t (Cons subscript_tag) [])))
    | Aw8update_unsafe => Op t UpdateByte xs
    | Strsub => Let t xs (If t (Op t (BoundsCheckByte F) [Var t 0; Var t 1])
                               (Op t DerefByteVec [Var t 0; Var t 1])
                               (Raise t (Op t (Cons subscript_tag) [])))
    | FP_cmp c => Op t (FP_cmp c) xs
    | FP_uop c => Op t (FP_uop c) xs
    | FP_bop c => Op t (FP_bop c) xs
    | FP_top c => Op t (FP_top c) xs
    | Shift x1 x2 x3 => Op t (WordShift x1 x2 x3) xs
    | Opw x1 x2 => Op t (WordOp x1 x2) xs
    | Eval => Op t Install xs (* if need to flip:  Let t xs (Op t Install [Var t 1; Var t 0]) *)
    | _ => Let None xs (Var None 0)
End

Definition join_strings_def:
  join_strings (x:mlstring$mlstring) y =
    if mlstring$strlen x = 0 then y
    else mlstring$concat [x; mlstring$strlit "_"; y]
End

Definition dest_nop_def:
  dest_nop op e =
    dtcase op of
    | WordFromInt W8 => (dtcase e of [App _ Ord [x]] => SOME x | _ => NONE)
    | Chr => (dtcase e of [App _ (WordToInt W8) [x]] => SOME x | _ => NONE)
    | _ => NONE
End

Theorem dest_nop_thm:
  dest_nop op es = SOME x ⇔
    (∃t. op = WordFromInt W8 ∧ es = [App t Ord [x]]) ∨
    (∃t. op = Chr ∧ es = [App t (WordToInt W8) [x]])
Proof
  Cases_on ‘op’ \\ fs [dest_nop_def] \\ every_case_tac \\ fs []
QED

Definition dest_Constant_def:
  dest_Constant (Op t (Constant c) []) = SOME c ∧
  dest_Constant (Op t (Const i) []) = SOME (ConstInt i) ∧
  dest_Constant (Op t (Cons n) []) = SOME (ConstCons n []) ∧
  dest_Constant _ = NONE
End

Theorem dest_Constant_pmatch:
  dest_Constant xs =
    case xs of
    | Op t (Constant x) [] => SOME x
    | Op t (Const i) [] => SOME (ConstInt i)
    | Op t (Cons n) [] => SOME (ConstCons n [])
    | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [dest_Constant_def]
QED

Definition dest_Constants_def:
  dest_Constants [] = SOME [] ∧
  dest_Constants (c::cs) =
    dtcase dest_Constant c of
    | NONE => NONE
    | SOME x => dtcase dest_Constants cs of
                | NONE => NONE
                | SOME xs => SOME (x::xs)
End

Definition SmartCons_def:
  SmartCons t tag xs =
    if NULL xs then Op t (Cons tag) [] else
    dtcase dest_Constants xs of
    | NONE => Op t (Cons tag) xs
    | SOME cs => Op t (Constant (ConstCons tag (REVERSE cs))) []
End

Definition compile_def:
  (compile m [] = []) /\
  (compile m (x::y::xs) = compile m [x] ++ compile m (y::xs)) /\
  (compile m [flatLang$Raise t e] = [closLang$Raise t (HD (compile m [e]))]) /\
  (compile m [Lit t l] = [compile_lit t l]) /\
  (compile m [Var_local t v] = [Var t (findi (SOME v) m)]) /\
  (compile m [Con t n es] =
     let tag = (dtcase n of SOME (t,_) => t | _ => 0) in
       [SmartCons t tag (compile m (REVERSE es))]) /\
  (compile m [App t op es] =
     dtcase dest_nop op es of
     | SOME e => compile m [e]
     | NONE => [compile_op t op (compile m (REVERSE es))]) /\
  (compile m [Fun t v e] =
     [Fn (mlstring$implode t) NONE NONE 1 (HD (compile (SOME v::m) [e]))]) /\
  (compile m [If t x1 x2 x3] =
     [If t (HD (compile m [x1]))
           (HD (compile m [x2]))
           (HD (compile m [x3]))]) /\
  (compile m [Let t vo e1 e2] =
     [Let t (compile m [e1]) (HD (compile (vo::m) [e2]))]) /\
  (compile m [Mat t e pes] = [Op t (Const 0) []]) /\
  (compile m [Handle t e pes] =
     dtcase dest_pat pes of
     | SOME (v,h) => [Handle t (HD (compile m [e])) (HD (compile (SOME v::m) [h]))]
     | _ => compile m [e]) /\
  (compile m [Letrec t funs e] =
     let new_m = MAP (\n. SOME (FST n)) funs ++ m in
       [Letrec (MAP (\n. join_strings (mlstring$implode t) (mlstring$implode (FST n))) funs) NONE NONE
          (MAP ( \ (f,v,x). (1, HD (compile (SOME v :: new_m) [x]))) funs)
          (HD (compile new_m [e]))])
Termination
  WF_REL_TAC `measure (flatLang$exp6_size o SND)` \\ rw []
  \\ `!funs f v x. MEM (f,v,x) funs ==> exp_size x < flatLang$exp1_size funs` by
    (Induct \\ fs [] \\ rw [] \\ fs [flatLangTheory.exp_size_def] \\ res_tac \\ fs [])
  \\ res_tac \\ fs [dest_pat_thm] \\ fs [flatLangTheory.exp_size_def]
  \\ gvs [dest_nop_thm] \\ fs [flatLangTheory.exp_size_def]
End

Definition compile_decs_def:
  compile_decs [] = [] /\
  compile_decs ((Dlet e)::xs) = compile [] [e] ++ compile_decs xs /\
  compile_decs (_::xs) = compile_decs xs
End

Definition inc_compile_decs_def:
  inc_compile_decs decs = (compile_decs decs ++
    compile_decs [Dlet (Con None NONE [])], [])
End

Theorem LENGTH_compile:
  !m xs. LENGTH (compile m xs) = LENGTH xs
Proof
  ho_match_mp_tac compile_ind \\ fs [compile_def]
  \\ rw [] \\ every_case_tac \\ fs []
QED

Theorem compile_NOT_NIL[simp]:
  compile m (x::xs) <> []
Proof
  rewrite_tac [GSYM LENGTH_NIL,LENGTH_compile] \\ fs []
QED

Theorem HD_compile[simp]:
  [HD (compile m [x])] = compile m [x]
Proof
  qspecl_then [`m`,`[x]`] mp_tac (SIMP_RULE std_ss [] LENGTH_compile)
  \\ Cases_on `compile m [x]` \\ fs []
QED

val _ = export_theory()
