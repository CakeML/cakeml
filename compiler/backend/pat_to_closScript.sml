open preamble patLangTheory closLangTheory dec_to_exhTheory

val _ = new_theory"pat_to_clos"

val string_tag_def = Define`string_tag = 0:num`
val vector_tag_def = Define`vector_tag = 1:num`

(* The translation from patLang to closLang is very simple.
   Its main purpose is simplifying the semantics of some operations,
   for example to explicitly raise an exception for Div so the semantics
   in closLang can make more assumptions about the arguments.
*)

val compile_def = tDefine"compile"`
  (compile (Raise e) =
    Raise (compile e)) ∧
  (compile (Handle e1 e2) =
    Handle (compile e1) (compile e2)) ∧
  (compile (Lit (IntLit i)) =
    Op (Const i) []) ∧
  (compile (Lit (Word8 w)) =
    Op (Const (&w2n w)) []) ∧
  (compile (Lit (Char c)) =
    Op (Const (& ORD c)) []) ∧
  (compile (Lit (StrLit s)) =
    Op (Cons string_tag) (REVERSE (MAP (λc. Op (Const (& ORD c)) []) s))) ∧
  (compile (Con cn es) =
    Op (Cons cn) (REVERSE (MAP compile es))) ∧
  (compile (Var_local n) =
    Var n) ∧
  (compile (Var_global n) =
    Op (Global n) []) ∧
  (compile (Fun e) =
    Fn NONE NONE 1 (compile e)) ∧
  (compile (App (Op (Op Opapp)) es) =
    if LENGTH es ≠ 2 then Op Sub (REVERSE (MAP compile es)) else
    App NONE (compile (EL 0 es)) [compile (EL 1 es)]) ∧
  (compile (App (Op (Op (Opn Plus))) es) =
    Op Add (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Opn Minus))) es) =
    Op Sub (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Opn Times))) es) =
    Op Mult (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Opn Divide))) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Equal [Var 0; Op (Const 0) []])
          (Raise (Op (Cons div_tag) []))
          (Op Div [Var 0; Var 1]))) ∧
  (compile (App (Op (Op (Opn Modulo))) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Equal [Var 0; Op (Const 0) []])
          (Raise (Op (Cons div_tag) []))
          (Op Mod [Var 0; Var 1]))) ∧
  (compile (App (Op (Op (Opb Lt))) es) =
    Op Less (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Opb Gt))) es) =
    Op Greater (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Opb Leq))) es) =
    Op LessEq (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Opb Geq))) es) =
    Op GreaterEq (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Chopb Lt))) es) =
    Op Less (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Chopb Gt))) es) =
    Op Greater (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Chopb Leq))) es) =
    Op LessEq (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op (Chopb Geq))) es) =
    Op GreaterEq (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Equality)) es) =
    Op Equal (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Opassign)) es) =
    if LENGTH es ≠ 2 then Op Sub (REVERSE (MAP compile es)) else
      Op Update [compile (EL 1 es); Op (Const 0) []; compile (EL 0 es)]) ∧
  (compile (App (Op (Op Opderef)) es) =
    Op Deref ((Op (Const 0) [])::(REVERSE (MAP compile es)))) ∧
  (compile (App (Op (Op Opref)) es) =
    Op Ref (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op W8fromInt)) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else compile (HD es)) ∧
  (compile (App (Op (Op W8toInt)) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else compile (HD es)) ∧
  (compile (App (Op (Op Ord)) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else compile (HD es)) ∧
  (compile (App (Op (Op Chr)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 0])
        (Raise (Op (Cons chr_tag) []))
        (If (Op Less [Var 0; Op (Const 255) []])
          (Raise (Op (Cons chr_tag) []))
          (Var 0)))) ∧
  (compile (App (Op (Op Aw8alloc)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 1])
          (Raise (Op (Cons subscript_tag) []))
          (Op RefByte [Var 0; Var 1]))) ∧
  (compile (App (Op (Op Aw8sub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 0])
          (Raise (Op (Cons subscript_tag) []))
          (If (Op Less [Op LengthByte [Var 1]; Var 0])
              (Op DerefByte [Var 0; Var 1])
              (Raise (Op (Cons subscript_tag) []))))) ∧
  (compile (App (Op (Op Aw8length)) es) =
    Op LengthByte (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Aw8update)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 1])
          (Raise (Op (Cons subscript_tag) []))
          (If (Op Less [Op LengthByte [Var 2]; Var 1])
              (Let [Op UpdateByte [Var 0; Var 1; Var 2]]
                 (Op (Cons tuple_tag) []))
              (Raise (Op (Cons subscript_tag) []))))) ∧
  (compile (App (Op (Op Explode)) es) =
    Op ToList (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Implode)) es) =
    Op (FromList string_tag) (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Strlen)) es) =
    Op LengthBlock (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op VfromList)) es) =
    Op (FromList vector_tag) (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Vsub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 0])
          (Raise (Op (Cons subscript_tag) []))
          (If (Op Less [Op LengthBlock [Var 1]; Var 0])
              (Op El [Var 0; Var 1])
              (Raise (Op (Cons subscript_tag) []))))) ∧
  (compile (App (Op (Op Vlength)) es) =
    Op LengthBlock (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Aalloc)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 1])
          (Raise (Op (Cons subscript_tag) []))
          (Op RefArray [Var 0; Var 1]))) ∧
  (compile (App (Op (Op Asub)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 0])
          (Raise (Op (Cons subscript_tag) []))
          (If (Op Less [Op Length [Var 1]; Var 0])
              (Op Deref [Var 0; Var 1])
              (Raise (Op (Cons subscript_tag) []))))) ∧
  (compile (App (Op (Op Alength)) es) =
    Op Length (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Op Aupdate)) es) =
    Let (REVERSE (MAP compile es))
      (If (Op Less [Op (Const 0) []; Var 1])
          (Raise (Op (Cons subscript_tag) []))
          (If (Op Less [Op Length [Var 2]; Var 1])
              (Let [Op Update [Var 0; Var 1; Var 2]]
                 (Op (Cons tuple_tag) []))
              (Raise (Op (Cons subscript_tag) []))))) ∧
  (compile (App (Op (Op (FFI n))) es) =
    Op (FFI n) (REVERSE (MAP compile es))) ∧
  (compile (App (Op (Init_global_var n)) es) =
    Let [Op (SetGlobal n) (REVERSE (MAP compile es))]
      (Op (Cons tuple_tag) [])) ∧
  (compile (App (Tag_eq n l) es) =
    Op (TagLenEq n l) (REVERSE (MAP compile es))) ∧
  (compile (App (El n) es) =
    if LENGTH es ≠ 1 then Op Sub (REVERSE (MAP compile es)) else
      Op El [Op (Const &n) []; compile (HD es)]) ∧
  (compile (If e1 e2 e3) =
    If (compile e1) (compile e2) (compile e3)) ∧
  (compile (Let e1 e2) =
    Let [compile e1] (compile e2)) ∧
  (compile (Seq e1 e2) =
    Let [compile e1;compile e2] (Var 1)) ∧
  (compile (Letrec es e) =
    Letrec NONE NONE (MAP (λe. (1,compile e)) es) (compile e)) ∧
  (compile (Extend_global n) =
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
