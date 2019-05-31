(*
  The translation from patLang to closLang is very simple.
  Its main purpose is simplifying the semantics of some operations,
  for example to explicitly raise an exception for Div so the semantics
  in closLang can make more assumptions about the arguments.
*)
open preamble patLangTheory closLangTheory backend_commonTheory

val _ = new_theory"pat_to_clos"
val _ = set_grammar_ancestry ["patLang", "closLang", "backend_common"]

val vector_tag_def = Define`vector_tag = 0:num`

fun var_fun m n = ``closLang$Var (tra § ^(numSyntax.term_of_int(36+n))) ^(numSyntax.term_of_int(m-n))``;

fun check1 tm var =
``(If (tra§1) (Op (tra§2) Less [Op (tra§3) (Const 0) []; ^(var 2)]) (Raise (tra§4) (Op (tra§5) (Cons subscript_tag) []))
  (If (tra§6) (Op (tra§7) Less [Op (tra§8) (Const 0) []; ^(var 1)]) (Raise (tra§9) (Op (tra§10) (Cons subscript_tag) []))
  (If (tra§11) (Op (tra§12) (BoundsCheckByte T) [Op (tra§13) Add [^(var 2); ^(var 1)]; ^(var 0)]) ^tm
  (Raise (tra§14) (Op (tra§15) (Cons subscript_tag) [])))))``;

val checkT = check1
  ``(closLang$Op (tra§16) (CopyByte T) [Var (tra§17) 0; Var (tra§18) 1; Var (tra§19) 2])`` (var_fun 2);

val checkF = check1
``(If (tra§16) (Op (tra§17) Less [Op (tra§18) (Const 0) []; Var (tra§19) 0]) (Raise (tra§20) (Op (tra§21) (Cons subscript_tag) []))
  (If (tra§22) (Op (tra§23) (BoundsCheckByte T) [Op (tra§24) Add [Var (tra§25) 2; Var (tra§26) 0]; Var (tra§27) 1])
     (Op (tra§28) (CopyByte F) [Var (tra§29) 0; Var (tra§30) 1; Var (tra§31) 2; Var (tra§32) 3; Var (tra§33) 4])
     (Raise (tra§34) (Op (tra§35) (Cons subscript_tag) []))))`` (var_fun 4);

val CopyByteStr_def = Define`CopyByteStr tra = ^checkT`;
val CopyByteAw8_def = Define`CopyByteAw8 tra = ^checkF`;

val dest_WordToInt_def = Define `
  (dest_WordToInt w [App _ op [x]] =
    (if op = Op (WordToInt w) then SOME x else NONE)) /\
  (dest_WordToInt w _ = NONE)`

val exp_size_def = patLangTheory.exp_size_def

val MEM_exp1_size = prove(
  ``!es. MEM a es ==> exp_size a < exp1_size es``,
  Induct_on`es` >> simp[exp_size_def] >>
  rw[] >> res_tac >> fs[] >> simp[exp_size_def] >>
  Cases_on`es`>>fs[LENGTH_NIL,exp_size_def] >> simp[] >>
  Cases_on`t`>>fs[exp_size_def] >> rw[] >> simp[]>>
  Cases_on`t'`>>fs[exp_size_def] >> rw[] >> simp[]);

val dest_WordToInt_exp_size = prove(
  ``!w es e. (dest_WordToInt w es = SOME e) ==>
             exp_size e < exp1_size es``,
  ho_match_mp_tac (theorem "dest_WordToInt_ind")
  \\ fs [dest_WordToInt_def] \\ fs [exp_size_def]);

val compile_def = tDefine"compile" `
  (compile (Raise tra e) =
    Raise tra (compile e)) ∧
  (compile (Handle tra e1 e2) =
    Handle tra (compile e1) (compile e2)) ∧
  (compile (Lit tra (IntLit i)) =
    Op tra (Const i) []) ∧
  (compile (Lit tra (Word8 w)) =
    Op tra (Const (& (w2n w))) []) ∧
  (compile (Lit tra (Word64 w)) =
    Op (tra§0) WordFromInt [Op (tra§1) (Const (&(w2n w))) []]) ∧
  (compile (Lit tra (Char c)) =
    Op tra (Const (& ORD c)) []) ∧
  (compile (Lit tra (StrLit s)) =
    Op tra (String s) []) ∧
  (compile (Con tra cn es) =
    Op tra (Cons cn) (REVERSE (MAP compile es))) ∧
  (compile (Var_local tra n) =
    Var tra n) ∧
  (compile (Fun tra e) =
    Fn tra NONE NONE 1 (compile e)) ∧
  (compile (App tra (Op Opapp) es) =
    if LENGTH es ≠ 2 then Op tra Sub (REVERSE (MAP compile es)) else
    App tra NONE (compile (EL 0 es)) [compile (EL 1 es)]) ∧
  (compile (App tra (Op (Opn Plus)) es) =
    Op tra Add (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Opn Minus)) es) =
    Op tra Sub (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Opn Times)) es) =
    Op tra Mult (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Opn Divide)) es) =
    Let (tra§1) (REVERSE (MAP compile es))
      (If (tra§2)
        (Op (tra§3) Equal [Var (tra§4) 0;
                           Op (tra§5) (Const 0) []])
        (Raise (tra§6) (Op (tra§7) (Cons div_tag) []))
        (Op (tra§8) Div [Var (tra§9) 0; Var (tra§10) 1]))) ∧
  (compile (App tra (Op (Opn Modulo)) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) Equal [Var (tra§3) 0; Op (tra§4) (Const 0) []])
          (Raise (tra§5) (Op (tra§6) (Cons div_tag) []))
          (Op (tra§7) Mod [Var (tra§8) 0; Var (tra§9) 1]))) ∧
  (compile (App tra (Op (Opw wz opw)) es) =
      Op tra (WordOp wz opw) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Shift wz sh n)) es) =
      Op tra (WordShift wz sh n) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Opb Lt)) es) =
    Op tra Less (REVERSE (MAP compile es))) ∧
 (compile (App tra (Op (Opb Gt)) es) =
    Op tra Greater (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Opb Leq)) es) =
    Op tra LessEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Opb Geq)) es) =
    Op tra GreaterEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Chopb Lt)) es) =
    Op tra Less (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Chopb Gt)) es) =
    Op tra Greater (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Chopb Leq)) es) =
    Op tra LessEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Chopb Geq)) es) =
    Op tra GreaterEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Equality) es) =
    Op tra Equal (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Opassign) es) =
    if LENGTH es ≠ 2 then Op tra Sub (REVERSE (MAP compile es)) else
      Op (tra§0) Update [compile (EL 1 es);
                         Op (tra§1) (Const 0) [];
                         compile (EL 0 es)]) ∧
  (compile (App tra (Op Opderef) es) =
    Op (tra§0) Deref ((Op (tra§1) (Const 0) [])::(REVERSE (MAP compile es)))) ∧
  (compile (App tra (Op Opref) es) =
    Op tra Ref (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (WordFromInt W8)) es) =
      case dest_WordToInt W64 es of
      | SOME e => Op tra (WordFromWord T) [compile e]
      | NONE =>  Op (tra§0) Mod
          ((Op (tra§1) (Const 256) [])::(REVERSE (MAP compile es)))) ∧
  (compile (App tra (Op (WordFromInt W64)) es) =
      case dest_WordToInt W8 es of
      | SOME e => Op tra (WordFromWord F) [compile e]
      | NONE => (Op tra WordFromInt (REVERSE (MAP compile es)))) ∧
  (compile (App tra (Op (WordToInt W8)) es) =
    if LENGTH es ≠ 1 then Op tra Sub (REVERSE (MAP compile es)) else
                     compile (HD es)) ∧
  (compile (App tra (Op (WordToInt W64)) es) =
    Op tra WordToInt (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Ord) es) =
    if LENGTH es ≠ 1 then Op tra Sub (REVERSE (MAP compile es))
    else compile (HD es)) ∧
  (compile (App tra (Op Chr) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) Less [Op (tra§3) (Const 0) []; Var (tra§4) 0])
        (Raise (tra§5) (Op (tra§6) (Cons chr_tag) []))
        (If (tra§7) (Op (tra§8) Less [Var (tra§9) 0; Op (tra§10) (Const 255) []])
          (Raise (tra§11) (Op (tra§12) (Cons chr_tag) []))
          (Var (tra§13) 0)))) ∧
  (compile (App tra (Op Aw8alloc) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) Less [Op (tra§3) (Const 0) []; Var (tra§4) 1])
          (Raise (tra§5) (Op (tra§6) (Cons subscript_tag) []))
          (Op (tra§7) (RefByte F) [Var (tra§8) 0; Var (tra§9) 1]))) ∧
  (compile (App tra (Op Aw8sub) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) (BoundsCheckByte F) [Var (tra§3) 0; Var (tra§4) 1])
         (Op (tra§5) DerefByte [Var (tra§6) 0; Var (tra§7) 1])
         (Raise (tra§8) (Op (tra§9) (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op Aw8length) es) =
    Op tra LengthByte (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Aw8update) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) (BoundsCheckByte F) [Var (tra§3) 1; Var (tra§4) 2])
         (Let (tra§5) [Op (tra§6) UpdateByte [Var (tra§7) 0;
                        Var (tra§8) 1; Var (tra§9) 2]]
           (Op (tra§10) (Cons tuple_tag) []))
         (Raise (tra§11) (Op (tra§12) (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op Strsub) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) (BoundsCheckByte F) [Var (tra§3) 0; Var (tra§4) 1])
         (Op (tra§5) DerefByteVec [Var (tra§6) 0; Var (tra§7) 1])
         (Raise (tra§8) (Op (tra§9) (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op Implode) es) =
    Op tra (FromListByte) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Strlen) es) =
    Op tra LengthByteVec (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Strcat) es) =
    Op tra ConcatByteVec (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op CopyStrStr) es) =
    Let (tra§0) (REVERSE (MAP compile es)) (CopyByteStr tra)) ∧
  (compile (App tra (Op CopyStrAw8) es) =
    Let (tra§0) (REVERSE (MAP compile es)) (CopyByteAw8 tra)) ∧
  (compile (App tra (Op CopyAw8Str) es) =
    Let (tra§0) (REVERSE (MAP compile es)) (CopyByteStr tra)) ∧
  (compile (App tra (Op CopyAw8Aw8) es) =
    Let (tra§0) (REVERSE (MAP compile es)) (CopyByteAw8 tra)) ∧
  (compile (App tra (Op VfromList) es) =
    Op tra (FromList vector_tag) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Vsub) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) BoundsCheckBlock [Var (tra§3) 0; Var (tra§4) 1])
         (Op (tra§5) El [Var (tra§6) 0; Var (tra§7) 1])
         (Raise (tra§8) (Op (tra§9) (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op Vlength) es) =
    Op tra LengthBlock (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Aalloc) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) Less [Op (tra§3) (Const 0) []; Var (tra§4) 1])
          (Raise (tra§5) (Op (tra§6) (Cons subscript_tag) []))
          (Op (tra§7) RefArray [Var (tra§8) 0; Var (tra§9) 1]))) ∧
  (compile (App tra (Op Asub) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) BoundsCheckArray [Var (tra§3) 0; Var (tra§4) 1])
         (Op (tra§5) Deref [Var (tra§6) 0; Var (tra§7) 1])
         (Raise (tra§8) (Op (tra§9) (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op Alength) es) =
    Op tra Length (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op Aupdate) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (If (tra§1) (Op (tra§2) BoundsCheckArray [Var (tra§3) 1; Var (tra§4) 2])
         (Let (tra§5) [Op (tra§6) Update [Var (tra§7) 0;
                        Var (tra§8) 1; Var (tra§9) 2]]
            (Op (tra§10) (Cons tuple_tag) []))
         (Raise (tra§11) (Op (tra§12) (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op ConfigGC) es) =
    Op tra ConfigGC (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (FFI n)) es) =
    Op tra (FFI n) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (GlobalVarAlloc n)) es) =
    Let (tra§0) (REVERSE (MAP compile es))
      (Let (tra§1) (REPLICATE n (Op (tra§2) AllocGlobal []))
         (Op (tra§3) (Cons tuple_tag) []))) ∧
  (compile (App tra (Op (GlobalVarInit n)) es) =
    Let (tra§0) [Op (tra§1) (SetGlobal n) (REVERSE (MAP compile es))]
      (Op (tra§2) (Cons tuple_tag) [])) ∧
  (compile (App tra (Op (GlobalVarLookup n)) es) =
    Op tra (Global n) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op ListAppend) es) =
    Op tra ListAppend (REVERSE (MAP compile es))) ∧
  (compile (App tra (Tag_eq n l) es) =
    Op tra (TagLenEq n l) (REVERSE (MAP compile es))) ∧
  (compile (App tra (El n) es) =
    if LENGTH es ≠ 1 then Op tra Sub (REVERSE (MAP compile es)) else
      Op (tra§0) El [Op (tra§1) (Const &n) []; compile (HD es)]) ∧
  (compile (App tra Run es) =
    Op tra Install (REVERSE (MAP compile es))) ∧
  (compile (If tra e1 e2 e3) =
    If tra (compile e1) (compile e2) (compile e3)) ∧
  (compile (Let tra e1 e2) =
    Let tra [compile e1] (compile e2)) ∧
  (compile (Seq tra e1 e2) =
    Let (tra§0) [compile e1;compile e2] (Var (tra§1) 1)) ∧
  (compile (Letrec tra es e) =
    Letrec tra NONE NONE (MAP (λe. (1,compile e)) es) (compile e)) ∧
  (compile (App tra (Op (FP_cmp cmp)) es) =
    (Op tra (FP_cmp cmp) (REVERSE (MAP compile es)))) /\
  (compile (App tra (Op (FP_uop u)) es) =
    (Op tra (FP_uop u) (REVERSE (MAP compile es)))) /\
  (compile (App tra (Op (FP_bop b)) es) =
    (Op tra (FP_bop b) (REVERSE (MAP compile es)))) /\
  (compile (App tra (Op (FP_top t)) es) =
    (Op tra (FP_top t) (REVERSE (MAP compile es))))`
  let
    val exp_size_def = patLangTheory.exp_size_def
  in
    WF_REL_TAC `measure exp_size` >>
    simp[exp_size_def] >>
    rpt conj_tac >> rpt gen_tac >>
    rw[] >> imp_res_tac MEM_exp1_size >> fs [] >>
    fs [LENGTH_EQ_NUM_compute,exp_size_def] >>
    imp_res_tac dest_WordToInt_exp_size >> fs []
  end
val _ = export_rewrites["compile_def"]

val _ = export_theory()
