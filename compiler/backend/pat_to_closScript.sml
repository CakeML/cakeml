open preamble patLangTheory closLangTheory backend_commonTheory

val _ = new_theory"pat_to_clos"
val _ = set_grammar_ancestry ["patLang", "closLang", "backend_common"]

val vector_tag_def = Define`vector_tag = 0:num`

(* The translation from patLang to closLang is very simple.
   Its main purpose is simplifying the semantics of some operations,
   for example to explicitly raise an exception for Div so the semantics
   in closLang can make more assumptions about the arguments.
*)

val compile_def = tDefine"compile"`
  (compile (Raise tra e) =
    Raise (compile e)) ∧
  (compile (Handle tra e1 e2) =
    Handle (compile e1) (compile e2)) ∧
  (compile (Lit tra (IntLit i)) =
    Op (Const i) []) ∧
  (compile (Lit tra (Word8 w)) =
    Op (Const (& (w2n w))) []) ∧
  (compile (Lit tra (Word64 w)) =
    Op WordFromInt [Op (Const (&(w2n w))) []]) ∧
  (compile (Lit tra (Char c)) =
    Op (Const (& ORD c)) []) ∧
  (compile (Lit tra (StrLit s)) =
    Op (String s) []) ∧
  (compile (Con tra cn es) =
    Op (Cons cn) (REVERSE (MAP compile es))) ∧
  (compile (Var_local tra n) =
    Var n) ∧
  (compile (Var_global tra n) =
    Op (Global n) []) ∧
  (compile (Fun tra e) =
    Fn NONE NONE 1 (compile e)) ∧
  (compile (App tra (Op (Op Opapp)) es) =
    if LENGTH es ≠ 2 then Op Sub (REVERSE (MAP compile es)) else
    App NONE (compile (EL 0 es)) [compile (EL 1 es)]) ∧
  (compile (App tra (Op (Op (Opn Plus))) es) =
    Op Add (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opn Minus))) es) =
    Op Sub (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opn Times))) es) =
    Op Mult (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opn Divide))) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Equal [Var 0; Op (Const 0) []])
          (Raise (Op (Cons div_tag) []))
          (Op Div [Var 0; Var 1]))) ∧
  (compile (App tra (Op (Op (Opn Modulo))) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Equal [Var 0; Op (Const 0) []])
          (Raise (Op (Cons div_tag) []))
          (Op Mod [Var 0; Var 1]))) ∧
  (compile (App tra (Op (Op (Opw wz opw))) es) =
      Op (WordOp wz opw) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Shift wz sh n))) es) =
      Op (WordShift wz sh n) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opb Lt))) es) =
    Op Less (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opb Gt))) es) =
    Op Greater (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opb Leq))) es) =
    Op LessEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Opb Geq))) es) =
    Op GreaterEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Chopb Lt))) es) =
    Op Less (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Chopb Gt))) es) =
    Op Greater (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Chopb Leq))) es) =
    Op LessEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (Chopb Geq))) es) =
    Op GreaterEq (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Equality)) es) =
    Op Equal (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Opassign)) es) =
    if LENGTH es ≠ 2 then Op Sub (REVERSE (MAP compile es)) else
      Op Update [compile (EL 1 es); Op (Const 0) []; compile (EL 0 es)]) ∧
  (compile (App tra (Op (Op Opderef)) es) =
    Op Deref ((Op (Const 0) [])::(REVERSE (MAP compile es)))) ∧
  (compile (App tra (Op (Op Opref)) es) =
    Op Ref (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (WordFromInt W8))) es) =
      Op Mod ((Op (Const 256) [])::(REVERSE (MAP compile es)))) ∧
  (compile (App tra (Op (Op (WordFromInt W64))) es) =
      Op WordFromInt (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op (WordToInt W8))) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else compile (HD es)) ∧
  (compile (App tra (Op (Op (WordToInt W64))) es) =
    Op WordToInt (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Ord)) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else compile (HD es)) ∧
  (compile (App tra (Op (Op Chr)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 0])
        (Raise (Op (Cons chr_tag) []))
        (If (Op Less [Var 0; Op (Const 255) []])
          (Raise (Op(Cons chr_tag) []))
          (Var 0)))) ∧
  (compile (App tra (Op (Op Aw8alloc)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 1])
          (Raise (Op (Cons subscript_tag) []))
          (Op (RefByte F) [Var 0; Var 1]))) ∧
  (compile (App tra (Op (Op Aw8sub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op BoundsCheckByte [Var 0; Var 1])
         (Op DerefByte [Var 0; Var 1])
         (Raise (Op (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op (Op Aw8length)) es) =
    Op LengthByte (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Aw8update)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op BoundsCheckByte [Var 1; Var 2])
         (Let [Op UpdateByte [Var 0; Var 1; Var 2]]
           (Op (Cons tuple_tag) []))
         (Raise (Op (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op (Op Strsub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op BoundsCheckByte [Var 0; Var 1])
         (Op DerefByteVec [Var 0; Var 1])
         (Raise (Op (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op (Op Implode)) es) =
    Op (FromListByte) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Strlen)) es) =
    Op LengthByteVec (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op VfromList)) es) =
    Op (FromList vector_tag) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Vsub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op BoundsCheckBlock [Var 0; Var 1])
         (Op El [Var 0; Var 1])
         (Raise (Op (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op (Op Vlength)) es) =
    Op LengthBlock (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Aalloc)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 1])
          (Raise (Op (Cons subscript_tag) []))
          (Op RefArray [Var 0; Var 1]))) ∧
  (compile (App tra (Op (Op Asub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op BoundsCheckArray [Var 0; Var 1])
         (Op Deref [Var 0; Var 1])
         (Raise (Op (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op (Op Alength)) es) =
    Op Length (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Op Aupdate)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op BoundsCheckArray [Var 1; Var 2])
         (Let [Op Update [Var 0; Var 1; Var 2]]
            (Op (Cons tuple_tag) []))
         (Raise (Op (Cons subscript_tag) [])))) ∧
  (compile (App tra (Op (Op (FFI n))) es) =
    Op (FFI n) (REVERSE (MAP compile es))) ∧
  (compile (App tra (Op (Init_global_var n)) es) =
    Let [Op (SetGlobal n) (REVERSE (MAP compile es))]
      (Op (Cons tuple_tag) [])) ∧
  (compile (App tra (Tag_eq n l) es) =
    Op (TagLenEq n l) (REVERSE (MAP compile es))) ∧
  (compile (App tra (El n) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else
      Op El [Op (Const &n) []; compile (HD es)]) ∧
  (compile (If tra e1 e2 e3) =
    If (compile e1) (compile e2) (compile e3)) ∧
  (compile (Let tra e1 e2) =
    Let [compile e1] (compile e2)) ∧
  (compile (Seq tra e1 e2) =
    Let [compile e1;compile e2] (Var 1)) ∧
  (compile (Letrec tra es e) =
    Letrec NONE NONE (MAP (λe. (1,compile e)) es) (compile e)) ∧
  (compile (Extend_global tra n) =
    Let (REPLICATE n (Op AllocGlobal []))
      (Op (Cons tuple_tag) []))`
  let
    val exp_size_def = patLangTheory.exp_size_def
  in
    WF_REL_TAC `measure exp_size` >>
    simp[exp_size_def] >>
    rpt conj_tac >> rpt gen_tac >>
    Induct_on`es` >> simp[exp_size_def] >>
    rw[] >> res_tac >> fs[] >> simp[exp_size_def] >>
    Cases_on`es`>>fs[LENGTH_NIL,exp_size_def] >> simp[] >>
    Cases_on`t`>>fs[exp_size_def] >> rw[] >> simp[]>>
    Cases_on`t'`>>fs[exp_size_def] >> rw[] >> simp[]
  end
val _ = export_rewrites["compile_def"]

val _ = export_theory()
