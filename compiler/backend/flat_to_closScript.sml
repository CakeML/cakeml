(*
  Compilation from flatLang to closLang. This compiler phase converts
  explicit variable names of flatLang to de Bruijn indexing of
  closLang. It also makes all division-by-zero and out-of-bounds
  exceptions raised explicitly.
*)
Theory flat_to_clos
Ancestors
  flatLang closLang clos_interp backend_common[qualified]
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

Definition dest_pat_def:
  dest_pat [(Pvar v, h)] = SOME (v:mlstring,h) /\
  dest_pat _ = NONE
End

Theorem dest_pat_pmatch:
  dest_pat x =
    pmatch x of [(Pvar v, h)] => SOME (v:mlstring,h) | _ => NONE
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
     (case l of
      | IntLit i => IntOp (Const i)
      | Char c => IntOp (Const (& (ORD c)))
      | StrLit s => BlockOp (Constant (ConstStr s))
      | Word8 b => IntOp (Const (& (w2n b)))
      | Word64 w => BlockOp (Constant (ConstWord64 w))
      | Float64 w => BlockOp (Constant (ConstWord64 w))) []
End

Definition arg1_def:
  arg1 xs f =
    case xs of [x] => f x | _ => closLang$Let None xs (Var None 0)
End

Theorem arg1_pmatch:
  arg1 xs f =
    pmatch xs of [x] => f x | _ => closLang$Let None xs (Var None 0)
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [arg1_def]
QED

Definition arg2_def:
  arg2 xs f =
    case xs of [x; y] => f x y | _ => closLang$Let None xs (Var None 0)
End

Theorem arg2_pmatch:
  arg2 xs f =
    pmatch xs of [x; y] => f x y | _ => closLang$Let None xs (Var None 0)
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [arg2_def]
QED

fun var_fun m n = ``closLang$Var t ^(numSyntax.term_of_int(m-n))``;

fun check1 tm var =
``(If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; ^(var 2)]) (Raise t (Op t (BlockOp (Cons subscript_tag)) []))
  (If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; ^(var 1)]) (Raise t (Op t (BlockOp (Cons subscript_tag)) []))
  (If t (Op t (MemOp (BoundsCheckByte T)) [Op t (IntOp Add) [^(var 2); ^(var 1)]; ^(var 0)]) ^tm
  (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))))``;

val checkT = check1
  ``(closLang$Op t (MemOp (CopyByte T)) [Var t 0; Var t 1; Var t 2])`` (var_fun 2);

val checkF = check1
``(If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; Var t 0]) (Raise t (Op t (BlockOp (Cons subscript_tag)) []))
  (If t (Op t (MemOp (BoundsCheckByte T)) [Op t (IntOp Add) [Var t 2; Var t 0]; Var t 1])
     (Op t (MemOp (CopyByte F)) [Var t 0; Var t 1; Var t 2; Var t 3; Var t 4])
     (Raise t (Op t (BlockOp (Cons subscript_tag)) []))))`` (var_fun 4);

Definition CopyByteStr_def:
  CopyByteStr t = ^checkT
End

Definition CopyByteAw8_def:
  CopyByteAw8 t = ^checkF
End

Definition compile_arith_def:
  compile_arith t (a: ast$arith) ty xs =
    case ty of
    | IntT => (case a of
               | Add => Op t (IntOp Add) xs
               | Sub => Op t (IntOp Sub) xs
               | Mul => Op t (IntOp Mult) xs
               | Div => Let t xs (If t (Op t (BlockOp Equal) [Var t 0; Op t (IntOp (Const 0)) []])
                                   (Raise t (Op t (BlockOp (Cons div_tag)) []))
                                   (Op t (IntOp closLang$Div) [Var t 0; Var t 1]))
               | Mod => Let t xs (If t (Op t (BlockOp Equal) [Var t 0; Op t (IntOp (Const 0)) []])
                                   (Raise t (Op t (BlockOp (Cons div_tag)) []))
                                   (Op t (IntOp closLang$Mod) [Var t 0; Var t 1]))
               | _ => Let None xs (Var None 0))
    | Float64T => (case a of
                   | Abs => Op t (WordOp (FP_uop FP_Abs)) xs
                   | Neg => Op t (WordOp (FP_uop FP_Neg)) xs
                   | Sqrt => Op t (WordOp (FP_uop FP_Sqrt)) xs
                   | Add => Op t (WordOp (FP_bop FP_Add)) xs
                   | Sub => Op t (WordOp (FP_bop FP_Sub)) xs
                   | Mul => Op t (WordOp (FP_bop FP_Mul)) xs
                   | Div => Op t (WordOp (FP_bop FP_Div)) xs
                   | FMA => Op t (WordOp (FP_top FP_Fma)) xs
                   | _   => Let None xs (Var None 0))
    | WordT ws => (case a of
                   | Add => Op t (WordOp (WordOpw ws Add)) xs
                   | Sub => Op t (WordOp (WordOpw ws Sub)) xs
                   | And => Op t (WordOp (WordOpw ws Andw)) xs
                   | Or  => Op t (WordOp (WordOpw ws Orw)) xs
                   | Xor => Op t (WordOp (WordOpw ws Xor)) xs
                   | _   => Let None xs (Var None 0))
    | BoolT => Op t (BlockOp BoolNot) xs
    | _ => Let None xs (Var None 0)
End

Definition compile_op_def:
  compile_op t op xs =
    case op of
    | Opapp => arg2 xs (\x f. closLang$App t NONE f [x])
    | TagLenEq tag n => closLang$Op t (BlockOp (TagLenEq tag n)) xs
    | LenEq n => closLang$Op t (BlockOp (LenEq n)) xs
    | El n => arg1 xs (\x. Op t (MemOp El) [Op None (IntOp (Const (& n))) []; x])
    | Opassign => arg2 xs (\x y. Op t (MemOp Update) [x; Op None (IntOp (Const 0)) []; y])
    | Opref => Op t (MemOp Ref) xs
    | ConfigGC => Op t (MemOp ConfigGC) xs
    | GlobalVarAlloc n => Let t xs (Op t (GlobOp AllocGlobal) [Op t (IntOp (Const (&n))) []])
    | GlobalVarInit n => Op t (GlobOp (SetGlobal (n+1))) xs
    | GlobalVarLookup n => Op t (GlobOp (Global (n+1))) xs
    | Equality => Op t (BlockOp Equal) xs
    | FFI n => Op t (FFI n) xs
    | ListAppend => Op t (BlockOp ListAppend) xs
    | Vlength => Op t (BlockOp LengthBlock) xs
    | Alength => Op t (MemOp Length) xs
    | Implode => Op t (MemOp FromListByte) xs
    | Explode => Op t (MemOp ToListByte) xs
    | Strlen => Op t (MemOp LengthByteVec) xs
    | Strcat => Op t (MemOp ConcatByteVec) xs
    | CopyStrStr => Let t xs (CopyByteStr t)
    | CopyStrAw8 => Let t xs (CopyByteAw8 t)
    | CopyAw8Str => Let t xs (CopyByteStr t)
    | CopyAw8Aw8 => Let t xs (CopyByteAw8 t)
    | Aw8xor_unsafe => Op t (MemOp XorByte) xs
    | VfromList => Op t (BlockOp (FromList 0)) xs
    | Test test test_ty =>
         (case test_ty of
          | BoolT     => Op t (BlockOp (BoolTest test)) xs
          | CharT     => Op t (WordOp (WordTest W8 test)) xs
          | WordT W8  => Op t (WordOp (WordTest W8 test)) xs
          | IntT      => (case test of
                          | Compare Lt  => Op t (IntOp Less) xs
                          | Compare Leq => Op t (IntOp LessEq) xs
                          | Compare Gt  => Op t (IntOp Greater) xs
                          | Compare Geq => Op t (IntOp GreaterEq) xs
                          | _           => Op t (BlockOp Equal) xs)
          | Float64T  => (case test of
                          | Compare Lt  => Op t (WordOp (FP_cmp FP_Less)) xs
                          | Compare Leq => Op t (WordOp (FP_cmp FP_LessEqual)) xs
                          | Compare Gt  => Op t (WordOp (FP_cmp FP_Greater)) xs
                          | Compare Geq => Op t (WordOp (FP_cmp FP_GreaterEqual)) xs
                          | _           => Op t (WordOp (FP_cmp FP_Equal)) xs)
          | _         => Op t (BlockOp Equal) xs)
    | Aw8length => Op t (MemOp LengthByte) xs
    | AallocFixed => Op t (MemOp Ref) xs
    | Aalloc => Let t xs (If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; Var t 1])
                               (Raise t (Op t (BlockOp (Cons subscript_tag)) []))
                               (Op t (MemOp RefArray) [Var t 0; Var t 1]))
    | Aw8alloc => Let t xs (If t (Op t (IntOp Less) [Op t (IntOp (Const 0)) []; Var t 1])
                                 (Raise t (Op t (BlockOp (Cons subscript_tag)) []))
                                 (Op t (MemOp (RefByte F)) [Var t 0; Var t 1]))
    | Vsub => Let t xs (If t (Op t (BlockOp BoundsCheckBlock) [Var t 0; Var t 1])
                             (Op t (MemOp El) [Var t 0; Var t 1])
                             (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))
    | Vsub_unsafe => Op t (MemOp El) xs
    | Asub => Let t xs (If t (Op t (MemOp BoundsCheckArray) [Var t 0; Var t 1])
                             (Op t (MemOp El) [Var t 0; Var t 1])
                             (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))
    | Asub_unsafe => Op t (MemOp El) xs
    | Aupdate => Let t xs (If t (Op t (MemOp BoundsCheckArray) [Var t 1; Var t 2])
                                (Op t (MemOp Update) [Var t 0; Var t 1; Var t 2])
                                (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))
    | Aupdate_unsafe => Op t (MemOp Update) xs
    | Aw8sub => Let t xs (If t (Op t (MemOp (BoundsCheckByte F)) [Var t 0; Var t 1])
                               (Op t (MemOp DerefByte) [Var t 0; Var t 1])
                               (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))
    | Aw8sub_unsafe => Op t (MemOp DerefByte) xs
    | Aw8update => Let t xs (If t (Op t (MemOp (BoundsCheckByte F)) [Var t 1; Var t 2])
                                  (Op t (MemOp UpdateByte) [Var t 0; Var t 1; Var t 2])
                                  (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))
    | Aw8update_unsafe => Op t (MemOp UpdateByte) xs
    | Strsub => Let t xs (If t (Op t (MemOp (BoundsCheckByte F)) [Var t 0; Var t 1])
                               (Op t (MemOp DerefByteVec) [Var t 0; Var t 1])
                               (Raise t (Op t (BlockOp (Cons subscript_tag)) [])))
    | Shift x1 x2 x3 => Op t (WordOp (WordShift x1 x2 x3)) xs
    | Eval => Op t Install xs (* if need to flip:  Let t xs (Op t Install [Var t 1; Var t 0]) *)
    | ThunkOp op => Op t (ThunkOp op) xs
    | Arith a ty => compile_arith t a ty xs
    | FromTo (WordT W8) IntT => arg1 xs (\x. x)
    | FromTo (WordT W64) IntT => Op t (WordOp WordToInt) xs
    | FromTo IntT (WordT W8) => arg1 xs (\x. Op t (IntOp Mod) [Op t (IntOp (Const 256)) []; x])
    | FromTo IntT (WordT W64) => Op t (WordOp WordFromInt) xs
    | FromTo CharT IntT => arg1 xs (\x. x)
    | FromTo IntT CharT => Let t xs (If t (Op t (IntOp Less) [Op None (IntOp (Const 0)) []; Var t 0])
                        (Raise t (Op t (BlockOp (Cons chr_tag)) []))
                        (If t (Op t (IntOp Less) [Var t 0; Op None (IntOp (Const 255)) []])
                          (Raise t (Op t (BlockOp (Cons chr_tag)) []))
                          (Var t 0)))
    | FromTo Float64T (WordT W64) => Let None xs (Var None 0)
    | FromTo (WordT W64) Float64T => Let None xs (Var None 0)
    | _ => Let None xs (Var None 0)
End

Definition join_strings_def:
  join_strings (x:mlstring$mlstring) y =
    if mlstring$strlen x = 0 then y
    else mlstring$concat [x; mlstring$strlit "_"; y]
End

Definition dest_nop_def:
  dest_nop op e =
    if op = FromTo IntT (WordT W8) then
      (case e of
       | [App _ op1 [x]] => (if op1 = FromTo CharT IntT then SOME x else NONE)
       | _ => NONE)
    else if op = FromTo IntT CharT then
      (case e of
       | [App _ op1 [x]] => (if op1 = FromTo (WordT W8) IntT then SOME x else NONE)
       | _ => NONE)
    else NONE
End

Theorem dest_nop_thm:
  dest_nop op es = SOME x ⇔
    (∃t. op = FromTo IntT (WordT W8) ∧ es = [App t (FromTo CharT IntT) [x]]) ∨
    (∃t. op = FromTo IntT CharT ∧ es = [App t (FromTo (WordT W8) IntT) [x]])
Proof
  Cases_on ‘op’ \\ gvs [dest_nop_def]
  \\ fs [dest_nop_def] \\ every_case_tac \\ fs []
QED

Definition dest_Constant_def:
  dest_Constant (Op t (BlockOp (Constant c)) []) = SOME c ∧
  dest_Constant (Op t (IntOp (Const i)) []) = SOME (ConstInt i) ∧
  dest_Constant (Op t (BlockOp (Cons n)) []) = SOME (ConstCons n []) ∧
  dest_Constant _ = NONE
End

Theorem dest_Constant_pmatch:
  dest_Constant xs =
    pmatch xs of
    | Op t (BlockOp (Constant x)) [] => SOME x
    | Op t (IntOp (Const i)) [] => SOME (ConstInt i)
    | Op t (BlockOp (Cons n)) [] => SOME (ConstCons n [])
    | _ => NONE
Proof
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ every_case_tac \\ fs [dest_Constant_def]
QED

Definition dest_Constants_def:
  dest_Constants [] = SOME [] ∧
  dest_Constants (c::cs) =
    case dest_Constant c of
    | NONE => NONE
    | SOME x => case dest_Constants cs of
                | NONE => NONE
                | SOME xs => SOME (x::xs)
End

Definition SmartCons_def:
  SmartCons t tag xs =
    if NULL xs then Op t (BlockOp (Cons tag)) [] else
    case dest_Constants xs of
    | NONE => Op t (BlockOp (Cons tag)) xs
    | SOME cs => Op t (BlockOp (Constant (ConstCons tag (REVERSE cs)))) []
End

Definition compile_def:
  (compile m [] = []) /\
  (compile m (x::y::xs) = compile m [x] ++ compile m (y::xs)) /\
  (compile m [flatLang$Raise t e] = [closLang$Raise t (HD (compile m [e]))]) /\
  (compile m [Lit t l] = [compile_lit t l]) /\
  (compile m [Var_local t v] = [Var t (findi (SOME v) m)]) /\
  (compile m [Con t n es] =
     let tag = (case n of SOME (t,_) => t | _ => 0) in
       [SmartCons t tag (compile m (REVERSE es))]) /\
  (compile m [App t op es] =
     case dest_nop op es of
     | SOME e => compile m [e]
     | NONE => [compile_op t op (compile m (REVERSE es))]) /\
  (compile m [Fun t v e] =
     [Fn t NONE NONE 1 (HD (compile (SOME v::m) [e]))]) /\
  (compile m [If t x1 x2 x3] =
     [If t (HD (compile m [x1]))
           (HD (compile m [x2]))
           (HD (compile m [x3]))]) /\
  (compile m [Let t vo e1 e2] =
     [Let t (compile m [e1]) (HD (compile (vo::m) [e2]))]) /\
  (compile m [Mat t e pes] = [Op t (IntOp (Const 0)) []]) /\
  (compile m [Handle t e pes] =
     case dest_pat pes of
     | SOME (v,h) => [Handle t (HD (compile m [e])) (HD (compile (SOME v::m) [h]))]
     | _ => compile m [e]) /\
  (compile m [Letrec t funs e] =
     let new_m = MAP (\n. SOME (FST n)) funs ++ m in
       [Letrec (MAP (\n. join_strings t (FST n)) funs) NONE NONE
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

Definition compile_prog_def:
  compile_prog xs =
    attach_interpreter (compile_decs xs)
End

Definition inc_compile_decs_def:
  inc_compile_decs decs =
    let xs = compile_decs decs ++ compile_decs [Dlet (Con None NONE [])] in
      (insert_interp xs,[])
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
