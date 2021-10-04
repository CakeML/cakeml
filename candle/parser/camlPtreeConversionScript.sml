(*
  A theory for converting OCaml parse trees to abstract syntax.
 *)

open preamble caml_lexTheory camlPEGTheory astTheory;

val _ = new_theory "camlPtreeConversion";

(* -------------------------------------------------------------------------
 * Sum monad syntax
 * ------------------------------------------------------------------------- *)

Definition bind_def[simp]:
  bind (INL e) f = INL e ∧
  bind (INR x) f = f x
End

Definition ignore_bind_def[simp]:
  ignore_bind m1 m2 = bind m1 (λu. m2)
End

Definition choice_def[simp]:
  choice (INL e) b = b ∧
  choice (INR x) b = INR x
End

Definition return_def[simp]:
  return = INR
End

Definition fail_def[simp]:
  fail = INL
End

val sum_monadinfo : monadinfo = {
  bind = “bind”,
  ignorebind = SOME “ignore_bind”,
  unit = “return”,
  fail = SOME “fail”,
  choice = SOME “choice”,
  guard = NONE
  };

val _ = declare_monad ("sum", sum_monadinfo);
val _ = enable_monadsyntax ();
val _ = enable_monad "sum";

Definition mapM_def:
  mapM f [] = return [] : 'a + 'b list ∧
  mapM f (x::xs) =
    do
      y <- f x;
      ys <- mapM f xs;
      return (y::ys)
    od
End

Theorem mapM_cong[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      mapM f xs: 'a + 'b list = mapM g ys
Proof
  Induct \\ rw [mapM_def]
  \\ Cases_on ‘g h’ \\ fs [mapM_def]
  \\ ‘mapM f xs = mapM g xs’ suffices_by simp_tac std_ss []
  \\ first_x_assum irule \\ fs []
QED

Definition option_def[simp]:
  option NONE = INL "option" ∧
  option (SOME x) = INR x
End

Definition fmap_def[simp]:
  fmap f (INR x) = INR (f x) ∧
  fmap f (INL err) = INL err
End

(* -------------------------------------------------------------------------
 * Parse tree conversion
 * ------------------------------------------------------------------------- *)

Definition destLf_def:
  destLf (Lf x) = return x ∧
  destLf _ = fail "destLf: Not a leaf"
End

Definition ptree_Ident_def:
  ptree_Ident (Lf t) = fail "Expected Ident non-terminal" ∧
  ptree_Ident (Nd n args) =
    if FST n = INL nIdent then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail "Impossible: nIdent"
    else
      fail "Expected Ident non-terminal"
End

Definition ptree_Name_def:
  ptree_Name symb =
    do
      lf <- destLf symb;
      tk <- option $ destTOK lf;
      option $ destIdent tk
    od
End

(* TODO
 *   Printing the tokens involved would be helpful.
 *)

Definition expect_tok_def:
  expect_tok symb token =
    do
      lf <- destLf symb;
      tk <- option $ destTOK lf;
      if tk = token then return tk else fail "Unexpected token"
    od
End

Definition ptree_TVar_def:
  ptree_TVar (Lf t) = fail "Expected type variable non-terminal" ∧
  ptree_TVar (Nd n args) =
    if FST n = INL nTVar then
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            nm <- ptree_Ident id;
            return (Atvar nm)
          od
      | _ => fail "Impossible: nTVar"
    else
      fail "Expected type variable non-terminal"
End

(* TODO
 *   There are no wildcard patterns in the type syntax of CakeML. Perhaps we
 *   can simulate it later by using some state for fresh variables.
 *)

Definition ptree_TAny_def:
  ptree_TAny (Lf t) = fail "Expected wildcard type non-terminal" ∧
  ptree_TAny (Nd n args) =
    if FST n = INL nTAny then
      fail "Wildcard type variables are not supported"
    else
      fail "Expected wildcard type variable non-terminal"
End

Definition ptree_Type_def:
  (ptree_Type (Lf _) = fail "Expected a type non-terminal") ∧
  (ptree_Type (Nd n args) =
    if FST n = INL nType then
      case args of
        [ty] => ptree_Type ty
      | _ => fail "Impossible: nType"
    else if FST n = INL nTBase then
      case args of
        [lpar; args; rpar; ctor] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ts <- ptree_TypeList args;
            nm <- ptree_Name ctor;
            return (Atapp ts (Short nm))
          od
      | [lpar; arg; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Type arg
          od
      | [arg] =>
          ptree_TVar arg ++ ptree_TAny arg
      | _ => fail "Impossible: nTBase"
    else if FST n = INL nTConstr then
      case args of
        [arg] => ptree_Type arg
      | arg::rest =>
          do
            ty <- ptree_Type arg;
            ids <- mapM ptree_Name rest;
            return (FOLDL (λt id. Atapp [t] (Short id)) ty ids)
          od
      | _ => fail "Impossible: nTConstr"
    else if FST n = INL nTProd then
      case args of
        [arg] => ptree_Type arg
      | [arg;star;prod] =>
          do
            expect_tok star StarT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type prod;
            return (Attup [ty1; ty2])
          od
      | _ => fail "Impossible: nTProd"
    else if FST n = INL nTFun then
      case args of
        [arg] => ptree_Type arg
      | [arg;rarrow;fun] =>
          do
            expect_tok rarrow RarrowT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type fun;
            return (Atfun ty1 ty2)
          od
      | _ => fail "Impossible: nTFun"
    else if FST n = INL nTAs then
      fail "Aliases in types are not supported"
    else
      fail "Expected type non-terminal") ∧
  (ptree_TypeList (Lf t) = fail "Expected a type list non-terminal") ∧
  (ptree_TypeList (Nd n args) =
    if FST n = INL nTypeList then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            return (t::ts)
          od
      | _ => fail "Impossible: nTypeList"
    else if FST n = INL nTypeLists then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            return (t::ts)
          od
      | [typ] => fmap (λt. [t]) $ ptree_Type typ
      | _ => fail "Impossible: nTypeLists"
    else
      fail "Expected a type list non-terminal")
End

Definition ptree_Literal:
  ptree_Literal (Lf t) = fail "Expected a literal non-terminal" ∧
  ptree_Literal (Nd n args) =
    if FST n = INL nLiteral then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            case tk of
              IntT n => return (IntLit n)
            | CharT c => return (Char c)
            | StringT s => return (StrLit s)
            | _ => fail "Impossible: nLiteral"
          od
      | _ => fail "Impossible: nLiteral"
    else
      fail "Expected a literal non-terminal"
End

(* TODO
 *   There's several made-up function names here that should be replaced
 *   by code which converts from integers to 64-bit words and back.
 w   For example, CakeML.lsl a b should be:
 *
 *     App WordToInt [
 *       App (Opw Lsl) [App WordFromInt [a];
 *                      App WordFromInt [b]]]
 *)

Definition ptree_Op_def:
  ptree_Op (Lf t) = fail "Expected binary operation non-terminal" ∧
  ptree_Op (Nd n args) =
    case args of
      [arg] =>
        do
          lf <- destLf arg;
          tk <- option $ destTOK lf;
          if FST n = INL nShiftOp then
            case tk of
              LslT => return $ INL $ Long "CakeML" $ Short "lsl"
            | LsrT => return $ INL $ Long "CakeML" $ Short "lsr"
            | AsrT => return $ INL $ Long "CakeML" $ Short "asr"
            | SymbolT "**" => return $ INL $ Long "Double" $ Short "pow"
            | SymbolT s => return $ INL $ Short s
            | _ => fail "Impossible: nShiftOp"
          else if FST n = INL nMultOp then
            case tk of
              StarT => return $ INR $ Opn Times
            | LandT => return $ INL $ Long "CakeML" $ Short "land"
            | LorT => return $ INL $ Long "CakeML" $ Short "lor"
            | LxorT => return $ INL $ Long "CakeML" $ Short "lxor"
            | SymbolT "/" => return $ INR $ Opn Divide
            | SymbolT "*." => return $ INR $ FP_bop FP_Mul
            | SymbolT "/." => return $ INR $ FP_bop FP_Div
            | SymbolT s => return $ INL $ Short s
            | _ => fail "Impossible: nMultOp"
          else if FST n = INL nAddOp then
            case tk of
              PlusT => return $ INR $ Opn Plus
            | MinusT => return $ INR $ Opn Minus
            | MinusFT => return $ INR $ FP_bop FP_Sub
            | SymbolT "+." => return $ INR $ FP_bop FP_Add
            | SymbolT s => return $ INL $ Short s
            | _ => fail "Impossible: nAddOp"
          else if FST n = INL nRelOp then
            case tk of
              LessT => return $ INR $ Opb Lt
            | GreaterT => return $ INR $ Opb Gt
            | EqualT => return $ INR Equality
            | SymbolT "<=" => return $ INR $ Opb Leq
            | SymbolT ">=" => return $ INR $ Opb Geq
            | SymbolT "<." => return $ INR $ FP_cmp FP_Less
            | SymbolT ">." => return $ INR $ FP_cmp FP_Greater
            | SymbolT "<=." => return $ INR $ FP_cmp FP_LessEqual
            | SymbolT ">=." => return $ INR $ FP_cmp FP_GreaterEqual
            | SymbolT s => return $ INL $ Short s
            | _ => fail "Impossible: nRelOp"
          else if FST n = INL nAndOp then
            case tk of
              AndalsoT => return $ INL $ Long "CakeML" $ Short "and"
            | AmpT => return $ INL $ Long "CakeML" $ Short "and"
            | SymbolT s => return $ INL $ Short s
            | _ => fail "Impossible: nAndOp"
          else if FST n = INL nOrOp then
            case tk of
              OrelseT => return $ INL $ Long "CakeML" $ Short "or"
            | OrT => return $ INL $ Long "CakeML" $ Short "or"
            | SymbolT s => return $ INL $ Short s
            | _ => fail "Impossible: nOrOp"
          else
            fail "Expected binary operation non-terminal"
        od
    | _ => fail "Expected binary operation non-terminal"
End

(* Turns a list literal pattern “[x; y; z]” into the
 * constructor pattern “x::y::z::[]”.
 *)

Definition build_list_pat_def:
  build_list_pat =
    FOLDR (λt p. Pcon (SOME (Short "::")) [t; p])
          (Pcon (SOME (Short "[]")) [])
End

(* Builds the cartesian product of two lists (of equal length).
 *)

Definition cart_prod_def:
  cart_prod ps qs =
    FLAT (MAP (λp. ZIP (REPLICATE (LENGTH qs) p, qs)) ps)
End

(* Builds the n-ary cartesian product of n lists (of any lengths).
 *)

Definition list_cart_prod_def:
  list_cart_prod [] = [[]] ∧
  list_cart_prod (xs::xss) =
    FLAT (MAP (λx. MAP (λy. x::y) (list_cart_prod xss)) xs)
End

Overload psize[local] = “parsetree_size (K 0) (K 0) (K 0)”;

Overload p1size[local] = “parsetree1_size (K 0) (K 0) (K 0)”;

Theorem parsetree_size_lemma[local]:
  p1size = list_size psize
Proof
  rw [FUN_EQ_THM]
  \\ Induct_on ‘x’ \\ rw [list_size_def, grammarTheory.parsetree_size_def]
QED

(* The parse trees contain or-patterns. “ptree_Pattern” creates one result
 * for each alternative in a or-pattern, as if all or-patterns were pulled up
 * to the top of the tree.
 *)

Definition ptree_Pattern_def:
  (ptree_Pattern (Lf t) = fail "Expected a pattern non-terminal") ∧
  (ptree_Pattern (Nd n args) =
    if FST n = INL nPAny then
      case args of
        [arg] =>
          do
            expect_tok arg AnyT;
            return [Pany]
          od
      | _ => fail "Impossible: nPAny"
    else if FST n = INL nPBase then
      case args of
        [arg] =>
          fmap (λn. [Pvar n]) (ptree_Ident arg) ++
          ptree_Pattern arg
      | [l; r] =>
          do
            expect_tok l LparT;
            expect_tok r RparT;
            return [Pcon NONE []]
          od
      | [l; p; r] =>
          do
            expect_tok l LparT;
            expect_tok r RparT;
            ptree_Pattern p
          od ++
          do
            expect_tok p DotsT;
            c1 <- ptree_Literal l;
            c2 <- ptree_Literal r;
            return [Pcon (SOME (Short "..")) [Plit c1; Plit c2]]
          od
      | [lpar; pat; colon; typ; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            ps <- ptree_Pattern pat;
            ty <- ptree_Type typ;
            return (MAP (λp. Ptannot p ty) ps)
          od
      | _ => fail "Impossible: nPBase"
    else if FST n = INL nPList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            pats <- ptree_PatternList rest;
            return (MAP build_list_pat (list_cart_prod pats))
          od
      | _ => fail "Impossible: nPList"
    else if FST n = INL nPLazy then
      case args of
        [pat] => ptree_Pattern pat
      | [lazy; pat] =>
          do
            expect_tok lazy LazyT;
            ps <- ptree_Pattern pat;
            return (MAP (λp. Pcon (SOME (Short "lazy")) [p]) ps)
          od
      | _ => fail "Impossible: nPLazy"
    else if FST n = INL nPConstr then
      case args of
        [pat] => ptree_Pattern pat
      | [id; pat] =>
          do
            nm <- ptree_Name id;
            ps <- ptree_Pattern pat;
            return (MAP (λp. Pcon (SOME (Short nm)) [p]) ps)
          od
      | _ => fail "Impossible: nPConstr"
    else if FST n = INL nPApp then
      case args of
        [pat] => ptree_Pattern pat
      | _ => fail "Impossible: nPApp"
    else if FST n = INL nPCons then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; colons; p2] =>
          do
            expect_tok colons ColonT;
            ps <- ptree_Pattern p1;
            qs <- ptree_Pattern p2;
            return (MAP (λ(p,q). Pcon (SOME (Short "::")) [p; q])
                        (cart_prod ps qs))
          od
      | _ => fail "Impossible: nPCons"
    else if FST n = INL nPProd then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; comma; p2] =>
          do
            expect_tok comma CommaT;
            ps <- ptree_Pattern p1;
            qs <- ptree_Pattern p2;
            return (MAP (λ(p,q). Pcon (SOME (Short ",")) [p; q])
                        (cart_prod ps qs))
          od
      | _ => fail "Impossible: nPProd"
    else if FST n = INL nPOr then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; bar; p2] =>
          do
            expect_tok bar BarT;
            ps <- ptree_Pattern p1;
            qs <- ptree_Pattern p2;
            return (ps ++ qs)
          od
      | _ => fail "Impossible: nPOr"
    else if FST n = INL nPAs then
      fail "Pattern aliases are not supported"
    else if FST n = INL nPattern then
      case args of
        [pat] => ptree_Pattern pat
      | _ => fail "Impossible: nPattern"
    else
      fail "Expected a pattern non-terminal") ∧
  (ptree_PatternList [] = fail "Pattern lists cannot be empty") ∧
  (ptree_PatternList [t] =
     do
       expect_tok t RbrackT;
       return []
     od) ∧
  (ptree_PatternList (p::ps) =
     do
       q <- ptree_Pattern p;
       qs <- ptree_PatternList ps;
       return (q::qs)
     od)
Termination
  WF_REL_TAC ‘measure (sum_size psize (list_size psize))’
  \\ simp [parsetree_size_lemma]
End

Definition ptree_Patterns_def:
  (ptree_Patterns (Lf t) = fail "Expected pattern list non-terminal") ∧
  (ptree_Patterns (Nd n args) =
    if FST n = INL nPatterns then
      case args of
        [pat] => fmap (λp. [p]) $ ptree_Pattern pat
      | [pat; rest] =>
          do
            p <- ptree_Pattern pat;
            ps <- ptree_Patterns rest;
            return (p::ps)
          od
      | _ => fail "Impossible: nPatterns"
    else
      fail "Expected pattern list non-terminal")
End

(* Builds a binary operation based on the output from “ptree_Op”.
 *)

Definition build_binop_def:
  build_binop (INR opn) x y = App opn [x; y] ∧
  build_binop (INL symb) x y = App Opapp [App Opapp [Var symb; x]; y]
End

(* Turns a list literal expression “[x; y; z]” into the
 * constructor application “x::y::z::[]”.
 *)

Definition build_list_exp_def:
  build_list_exp =
    FOLDR (λt e. Con (SOME (Short "::")) [t; e])
          (Con (SOME (Short "[]")) [])
End

Definition build_funapp_def:
  build_funapp f xs = FOLDL (λa b. App Opapp [a; b]) f xs
End

(* Turns a curried lambda with patterns, e.g. “fun a [3;4] c -> e”
 * into a sequence of lambdas, possibly with pattern matches:
 * “fun a -> fun fresh -> match fresh with [3;4] -> fun c -> e”.
 *)

Definition build_fun_lam_def:
  build_fun_lam body pats =
      FOLDR (λp b. case p of
                     Pvar x => Fun x b
                   | _ => Fun "" (Mat (Var (Short "")) [p, b]))
            body pats
End

(* Builds a letrec out of a list of let rec-bindings.
 *)

Definition build_letrec_def:
  build_letrec binds body =
    Letrec (MAP (λ(f,ps,x). (f,"",Mat (Var (Short ""))
                                      [HD ps, build_fun_lam x (TL ps)]))
                binds)
           body
End

(* Builds a sequence of lets out of a list of let bindings.
 *)

Definition build_lets_def:
  build_lets binds body =
    FOLDR (λbind rest.
             case bind of
               INL (p,x) =>
                 Mat x [p, rest]
             | INR (f,ps,x) =>
                 Let (SOME f) (build_fun_lam x ps) rest)
          binds body
End

(* TODO
 * With these functions it's not possible to mix value definitions
 * and recursive function definitions.
 *)

(* Builds a pattern match for a match expression. The third part of each tuple
 * is SOME when there's a guard-expression present. Each guard expression
 * duplicates the rest of the match expression.
 *
 *)

Definition build_pmatch_def:
  build_pmatch bv cn [] = [] ∧
  build_pmatch bv cn ((pat,body,NONE)::rest) =
    (pat,body)::build_pmatch bv cn rest ∧
  build_pmatch bv cn ((pat,body,SOME guard)::rest) =
    let rs = build_pmatch bv cn rest in
      (pat,If guard body (cn (Var (Short bv)) rs))::rs
End

Definition build_match_def:
  build_match bv pmatch x =
    Let (SOME bv) x (Mat (Var (Short bv)) (build_pmatch bv Mat pmatch))
End

Definition build_handle_def:
  build_handle bv pmatch x =
    Let (SOME bv) x (Handle (Var (Short bv)) (build_pmatch bv Handle pmatch))
End

Definition build_function_def:
  build_function bv pmatch =
    Fun bv (Mat (Var (Short bv)) (build_pmatch bv Mat pmatch))
End

(* Turn a boolean literal into a constructor expression.
 *)

Definition bool_to_exp_def:
  bool_to_exp b = Con (SOME (Short (if b then "True" else "False"))) []
End

(* Flatten the row-alternatives in a pattern-match.
 *)

Definition flatten_pmatch_def:
  flatten_pmatch pss = FLAT (MAP (λ(ps,x,w). MAP (λp. (p,x,w)) ps) pss)
End

Theorem list_size_lemma[local]:
  MEM x xs ⇒ m x < list_size m xs
Proof
  Induct_on ‘xs’ \\ rw [list_size_def]
  \\ res_tac \\ fs []
QED

Definition ptree_Expr:
  (ptree_Expr (Lf t) = fail "Expected an expression non-terminal") ∧
  (ptree_Expr (Nd n args) =
    if FST n = INL nEList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            exps <- ptree_ExprList rest;
            return (build_list_exp exps)
          od
      | _ => fail "Impossible: nEList"
    else if FST n = INL nEBase then
      case args of
        [lpar;expr;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Expr expr
          od ++
          do
            expect_tok lpar BeginT;
            expect_tok rpar BeginT;
            ptree_Expr expr
          od
      | [lpar;expr;colon;typ;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            ty <- ptree_Type typ;
            x <- ptree_Expr expr;
            return (Tannot x ty)
          od
      | [arg] =>
          fmap Lit (ptree_Literal arg) ++
          fmap (Var o Short) (ptree_Ident arg) ++
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if tk = TrueT ∨ tk = FalseT then
              return (bool_to_exp (tk = TrueT))
            else
              fail ""
          od ++
          ptree_Expr arg
      | _ => fail "Impossible: nEBase"
    else if FST n = INL nEAssert then
      case args of
        [assr; expr] =>
          do
            expect_tok assr AssertT;
            x <- ptree_Expr expr;
            return (App Opapp [Var (Short "assert"); x])
          od
      | _ => fail "Impossible: nEAssert"
    else if FST n = INL nELazy then
      case args of
        [lazy; expr] =>
          do
            expect_tok lazy LazyT;
            x <- ptree_Expr expr;
            return (App Opapp [Var (Short "lazy"); x])
          od
      | _ => fail "Impossible: nELazy"
    else if FST n = INL nEConstr then
      case args of
        [consid; expr] =>
          do
            id <- ptree_Name consid;
            x <- ptree_Expr expr;
            return (Con (SOME (Short id)) [x])
          od
      | _ => fail "Impossible: nEConstr"
    else if FST n = INL nEFunapp then
      case args of
        funexp::funargs =>
          do
            f <- ptree_Expr funexp;
            xs <- mapM ptree_Expr funargs;
            return (build_funapp f xs)
          od
      | _ => fail "Impossible: nEFunapp"
    else if FST n = INL nEApp then
      case args of
        [arg] => ptree_Expr arg
      | _ => fail "Impossible: nEApp"
    else if FST n = INL nEPrefix then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- option $ destTOK lf;
            sym <- option $ destSymbol tk;
            x <- ptree_Expr expr;
            return (App Opapp [Var (Short sym); x])
          od
      | [arg] => ptree_Expr arg
      | _ => fail "Impossible: nEPrefix"
    else if FST n = INL nENeg then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- option $ destTOK lf;
            x <- ptree_Expr expr;
            case tk of
              MinusT => return (App (Opn Minus) [Lit (IntLit 0i); x])
            | MinusFT => return (App (FP_bop FP_Sub) [Lit (Word64 0w); x])
            | SymbolT s => return (App Opapp [Var (Short s); x])
            | _ => fail "Impossible: nEPrefix"
          od
      | [arg] => ptree_Expr arg
      | _ => fail "Impossible: nENeg"
    else if FST n = INL nEShift then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail "Impossible: nEShift"
    else if FST n = INL nEMult then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail "Impossible: nEMult"
    else if FST n = INL nEAdd then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail "Impossible: nEAdd"
    else if FST n = INL nECons then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; colons; rhs] =>
          do
            expect_tok colons ColonsT;
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            return (Con (SOME (Short "::")) [x; y])
          od
      | _ => fail "Impossible: nECons"
    else if FST n = INL nECat then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            return (build_funapp (Var (Long "String" (Short [CHR 94]))) [x; y])
          od
      | _ => fail "Impossible: nECat"
    else if FST n = INL nERel then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail "Impossible: nERel"
    else if FST n = INL nEAnd then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail "Impossible: nEAnd"
    else if FST n = INL nEOr then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail "Impossible: nEOr"
    else if FST n = INL nEProd then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; comma; rhs] =>
          do
            expect_tok comma CommaT;
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            return (Con (SOME (Short ",")) [x; y])
          od
      | _ => fail "Impossible: nEProd"
    else if FST n = INL nEIf then
      case args of
        [ift; x; thent; y; elset; z] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            expect_tok elset ElseT;
            x1 <- ptree_Expr x;
            y1 <- ptree_Expr y;
            z1 <- ptree_Expr z;
            return (If x1 y1 z1)
          od
      | [ift; x; thent; y] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            x1 <- ptree_Expr x;
            y1 <- ptree_Expr y;
            return (If x1 y1 (Con NONE []))
          od
      | _ => fail "Impossible: nEIf"
    else if FST n = INL nESeq then
      case args of
        [x; semi; y] =>
          do
            expect_tok semi SemiT;
            x1 <- ptree_Expr x;
            y1 <- ptree_Expr y;
            return (Let NONE x1 y1)
          od
      | [x] => ptree_Expr x
      | _ => fail "Impossible: nESeq"
    else if FST n = INL nELet then
      case args of
        [lett; rec; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok rec RecT;
            expect_tok int InT;
            binds <- ptree_LetRecBindings binds;
            body <- ptree_Expr expr;
            return (build_letrec binds body)
          od
      | [lett; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok int InT;
            binds <- ptree_LetBindings binds;
            body <- ptree_Expr expr;
            return (build_lets body binds)
          od
      | _ => fail "Impossible: nELet"
    else if FST n = INL nEMatch then
      case args of
        [match; expr; witht; pmatch] =>
          do
            expect_tok match MatchT;
            expect_tok witht WithT;
            x <- ptree_Expr expr;
            ps <- ptree_PatternMatch pmatch;
            return (build_match "" (flatten_pmatch ps) x)
          od
      | _ => fail "Impossible: nEMatch"
    else if FST n = INL nEFun then
      case args of
        [funt; params; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr expr;
            return (Fun "" (Mat (Var (Short ""))
                           (MAP (λps. (HD ps, build_fun_lam x (TL ps))) ps)))
          od
      | [funt; params; colon; typ; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr expr;
            ty <- ptree_Type typ;
            return (Tannot (Fun "" (Mat (Var (Short ""))
                                   (MAP (λps. (HD ps, build_fun_lam x (TL ps)))
                                        ps))) ty)
          od
      | _ => fail "Impossible: nEFun"
    else if FST n = INL nEFunction then
      case args of
        [funct; pmatch] =>
          do
            expect_tok funct FunctionT;
            ps <- ptree_PatternMatch pmatch;
            return (build_function "" (flatten_pmatch ps))
          od
      | _ => fail "Impossible: nEFunction"
    else if FST n = INL nETry then
      case args of
        [tryt; expr; witht; pmatch] =>
          do
            expect_tok tryt TryT;
            expect_tok witht WithT;
            x <- ptree_Expr expr;
            ps <- ptree_PatternMatch pmatch;
            return (build_handle "" (flatten_pmatch ps) x)
          od
      | _ => fail "Impossible: nETry"
    else if FST n = INL nEWhile then
      case args of
        [while; expr; dot; body; donet] =>
          do
            expect_tok while WhileT;
            expect_tok dot DoT;
            expect_tok donet DoneT;
            x <- ptree_Expr expr;
            b <- ptree_Expr body;
            return (build_funapp (Var (Short "while")) [x; b])
          od
      | _ => fail "Impossible: nEWhile"
    else if FST n = INL nEFor then
      case args of
        [for; ident; eq; ubd; updown; lbd; dot; body; donet] =>
          do
            expect_tok for ForT;
            expect_tok eq EqualT;
            expect_tok dot DoT;
            lf <- destLf updown;
            tk <- option $ destTOK lf;
            (if tk = ToT ∨ tk = DowntoT then return () else
              fail "Expected 'to' or 'downto'");
            id <- ptree_Ident ident;
            u <- ptree_Expr ubd;
            l <- ptree_Expr lbd;
            b <- ptree_Expr body;
            return (build_funapp (Var (Short "for"))
                                 [bool_to_exp (tk = ToT);
                                  Var (Short id); u; l; b])
          od
      | _ => fail "Impossible: nEFor"
    else if FST n = INL nExpr then
      case args of
        [arg] => ptree_Expr arg
      | _ => fail "Impossible: nExpr"
    else
      fail "Expected an expression non-terminal") ∧
  (ptree_PatternMatch (Lf t) = fail "Expected a pattern-match non-terminal") ∧
  (ptree_PatternMatch (Nd n args) =
    if FST n = INL nPatternMatch then
      case args of
        [bar; pms] =>
          do
            expect_tok bar BarT;
            ptree_PatternMatch pms
          od
      | [pms] => ptree_PatternMatch pms
      | _ => fail "Impossible: nPatternMatch"
    else if FST n = INL nPatternMatches then
      case args of
        pat :: whent :: whenx :: rarrow :: body :: rest =>
          do
            expect_tok rarrow RarrowT;
            expect_tok whent WhenT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr body;
            w <- ptree_Expr whenx;
            case rest of
              [] => return [p, x, SOME w]
            | [bar; pms] =>
                do
                  expect_tok bar BarT;
                  ps <- ptree_PatternMatch pms;
                  return ((p, x, SOME w)::ps)
                od
            | _ => fail "Impossible: nPatternMatches"
          od
      | pat :: rarrow :: body :: rest =>
          do
            expect_tok rarrow RarrowT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr body;
            case rest of
              [] => return [p, x, NONE]
            | [bar; pms] =>
                do
                  expect_tok bar BarT;
                  ps <- ptree_PatternMatch pms;
                  return ((p, x, NONE)::ps)
                od
            | _ => fail "Impossible: nPatternMatches"
          od
      | _ => fail "Impossible: nPatternMatches"
    else
      fail "Expected a pattern-match non-terminal") ∧
  (ptree_LetRecBinding (Lf t) =
    fail "Expected a let rec binding non-terminal") ∧
  (ptree_LetRecBinding (Nd n args) =
    if FST n = INL nLetRecBinding then
      case args of
        [id; pats; colon; type; eq; expr] =>
          do
            expect_tok colon ColonT;
            expect_tok eq EqualT;
            nm <- ptree_Ident id;
            ps <- ptree_Patterns pats;
            if LENGTH ps = 1 then INR () else
              fail "Or-patterns are not allowed in let rec bindings";
            ty <- ptree_Type type;
            bd <- ptree_Expr expr;
            return (nm, HD ps, Tannot bd ty)
          od
      | [id; pats; eq; expr] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_Ident id;
            ps <- ptree_Patterns pats;
            if LENGTH ps = 1 then INR () else
              fail "Or-patterns are not allowed in let rec bindings";
            bd <- ptree_Expr expr;
            return (nm, HD ps, bd)
          od
      | _ => fail "Impossible: nLetRecBinding"
    else
      fail "Expected a let rec binding non-terminal") ∧
  (ptree_LetRecBindings (Lf t) =
      fail "Expected a list of let rec bindings non-terminal") ∧
  (ptree_LetRecBindings (Nd n args) =
    if FST n = INL nLetRecBindings then
      case args of
        [rec] =>
          fmap (λr. [r]) $ ptree_LetRecBinding rec
      | [rec; andt; recs] =>
          do
            expect_tok andt AndT;
            r <- ptree_LetRecBinding rec;
            rs <- ptree_LetRecBindings recs;
            return (r::rs)
          od
      | _ => fail "Impossible: nLetRecBindings"
    else
      fail "Expected a list of let rec bindings non-terminal") ∧
  (ptree_LetBinding (Lf t) = fail "Expected a let binding non-terminal") ∧
  (ptree_LetBinding (Nd n args) =
    if FST n = INL nLetBinding then
      case args of
        [pat; eq; bod] =>
          do
            expect_tok eq EqualT;
            ps <- ptree_Pattern pat;
            if LENGTH ps = 1 then INR () else
              fail "Or-patterns are not allowed in let bindings";
            x <- ptree_Expr bod;
            return (INL (HD ps, x))
          od
      | [id; pats; eq; bod] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_Ident id;
            ps <- ptree_Patterns pats;
            if LENGTH ps = 1 then INR () else
              fail "Or-patterns are not allowed in let bindings";
            x <- ptree_Expr bod;
            return (INR (nm, HD ps, x))
          od
      | [id; pats; colon; typ; eq; bod] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_Ident id;
            ps <- ptree_Patterns pats;
            if EVERY (λp. LENGTH p = 1) ps then INR () else
              fail "Or-patterns are not allowed in let bindings";
            x <- ptree_Expr bod;
            return (INR (nm, MAP HD ps, x))
          od
      | _ => fail "Impossible: nLetBinding"
    else
      fail "Expected a let binding non-terminal") ∧
  (ptree_LetBindings (Lf t) =
     fail "Expected a list of let bindings non-terminal") ∧
  (ptree_LetBindings (Nd n args) =
    if FST n = INL nLetBindings then
      case args of
        [letb] =>
          fmap (λl. [l]) $ ptree_LetBinding letb
      | [letb; andt; lets] =>
          do
            expect_tok andt AndT;
            r <- ptree_LetBinding letb;
            rs <- ptree_LetBindings lets;
            return (r::rs)
          od
      | _ => fail "Impossible: nLetBindings"
    else
      fail "Expected a list of let bindings non-terminal") ∧
  (ptree_ExprList [] = fail "Expression lists cannot be empty") ∧
  (ptree_ExprList [t] =
    do
      expect_tok t RbrackT;
      return []
    od) ∧
  (ptree_ExprList (t::ts) =
    do
      expect_tok t SemiT;
      ptree_ExprList ts
    od ++
    do
      e <- ptree_Expr t;
      es <- ptree_ExprList ts;
      return (e::es)
    od)
Termination
  WF_REL_TAC ‘measure (sum_size psize (sum_size psize (sum_size psize
                      (sum_size psize (sum_size psize
                      (sum_size psize p1size))))))’
  \\ rw [parsetree_size_lemma]
  \\ drule_then (qspec_then ‘psize’ mp_tac) list_size_lemma
  \\ gs []
End

Definition ptree_StarTypes_def:
  ptree_StarTypes [] = return [] ∧
  ptree_StarTypes (x::xs) =
    do
      expect_tok x StarT;
      ptree_StarTypes xs
    od ++
    do
      t <- ptree_Type x;
      ts <- ptree_StarTypes xs;
      return (t::ts)
    od
End

Definition ptree_ConstrArgs_def:
  (ptree_ConstrArgs (Lf t) =
    fail "Expected a constructor arguments non-terminal") ∧
  (ptree_ConstrArgs (Nd n args) =
    if FST n = INL nConstrArgs then
      case args of
        ty::rest =>
          do
            t <- ptree_Type ty;
            ts <- ptree_StarTypes rest;
            return (t::ts)
          od
      | _ => fail "Impossible: nConstrArgs"
    else
      fail "Expected a constructor arguments non-terminal")
End

Definition ptree_ConstrDecl_def:
  (ptree_ConstrDecl (Lf t) =
    fail "Expected a constructor declaration non-terminal") ∧
  (ptree_ConstrDecl (Nd n args) =
    if FST n = INL nConstrDecl then
      case args of
        [name] =>
          fmap (λnm. (nm,[])) $ ptree_Ident name
      | [name; oft; args] =>
          do
            expect_tok oft OfT;
            nm <- ptree_Ident name;
            ts <- ptree_ConstrArgs args;
            return (nm, ts)
          od
      | _ => fail "Impossible: nConstrDecl"
    else
      fail "Expected a constructor declaration non-terminal")
End

Definition ptree_ExcDefinition_def:
  (ptree_ExcDefinition (Lf t) =
    fail "Expected an exception definition non-terminal") ∧
  (ptree_ExcDefinition (Nd n args) =
    if FST n = INL nExcDefinition then
      case args of
        [exnt; cdecl] =>
          do
            expect_tok exnt ExceptionT;
            (nm, args) <- ptree_ConstrDecl cdecl;
            return (Dexn (SND n) nm args)
          od
      | [exnt; lhsid; eq; rhsid] =>
          do
            expect_tok exnt ExceptionT;
            expect_tok eq EqualT;
            lhs <- ptree_Ident lhsid;
            rhs <- ptree_Ident rhsid;
            return (Dexn (SND n) lhs [Atapp [] (Short rhs)])
          od
      | _ => fail "Impossible: nExcDefinition"
    else
      fail "Expected an exception definition non-terminal")
End

(* ptree_TypeRepr picks out constructor declarations and returns
 * a list of (constructor_name # argument_types) pairs, one for
 * each constructor.
 *)

Definition ptree_TypeRepr_def:
  (ptree_TypeRepr (Lf t) = fail "Expected a type-repr non-terminal") ∧
  (ptree_TypeRepr (Nd n args) =
    if FST n = INL nTypeRepr then
      case args of
        [bart; cdecl; reprs] =>
          do
            expect_tok bart BarT;
            tr <- ptree_ConstrDecl cdecl;
            trs <- ptree_TypeRepr reprs;
            return (tr::trs)
          od
      | [a; b] =>
          do
            expect_tok a BarT;
            tr <- ptree_ConstrDecl b;
            return [tr]
          od ++
          do
            tr <- ptree_ConstrDecl a;
            trs <- ptree_TypeRepr b;
            return (tr::trs)
          od
      | [cdecl] =>
          do
            tr <- ptree_ConstrDecl cdecl;
            return [tr]
          od
      | _ => fail "Impossible: nTypeRepr"
    else if FST n = INL nTypeRepr then
      case args of
        [bart; cdecl] =>
          do
            expect_tok bart BarT;
            ts <- ptree_ConstrDecl cdecl;
            return [ts]
          od
      | [bart; cdecl; tyreps] =>
          do
            expect_tok bart BarT;
            ts <- ptree_ConstrDecl cdecl;
            trs <- ptree_TypeRepr tyreps;
            return (ts::trs)
          od
      | _ => fail "Impossible: nTypeReprs"
    else
      fail "Expected a type-repr non-terminal")
End

Definition ptree_TypeInfo_def:
  (ptree_TypeInfo (Lf t) =
    fail "Expected a type-info non-terminal") ∧
  (ptree_TypeInfo (Nd n args) =
    if FST n = INL nTypeInfo then
      case args of
        [tr] =>
          fmap INR $ ptree_TypeRepr tr
      | [eq; ty] =>
          do
            expect_tok eq EqualT;
            fmap INL $ ptree_Type ty
          od
      | _ => fail "Impossible: nTypeInfo"
    else
      fail "Expected a type-info non-terminal")
End

(* There ar
  type-definition ::= type [nonrec] typedef  { and typedef }
  typedef ::= [type-params]  typeconstr-name  type-information
  type-information ::= [type-equation] [type-representation] { type-constraint }  *

  type-params ::= type-param
                ∣ ( type-param { , type-param } )
  type-param ::= ' ident
 *)

Definition ptree_TypeName_def:
  ptree_TypeName (Lf t) = fail "Expected type variable non-terminal" ∧
  ptree_TypeName (Nd n args) =
    if FST n = INL nTVar then
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            ptree_Ident id
          od
      | _ => fail "Impossible: nTVar"
    else
      fail "Expected type variable non-terminal"
End

Definition ptree_TypeParamList_def:
  (ptree_TypeParamList [] = fail "Empty type parameters are not supported") ∧
  (ptree_TypeParamList [t] =
    do
      expect_tok t RparT;
      return []
    od) ∧
  (ptree_TypeParamList (p::ps) =
    do
      expect_tok p CommaT;
      ptree_TypeParamList ps
    od ++
    do
      t <- ptree_TypeName p;
      ts <- ptree_TypeParamList ps;
      return (t::ts)
    od)
End

Definition ptree_TypeParams_def:
  (ptree_TypeParams (Lf t) =
    fail "Expected a type-parameters non-terminal") ∧
  (ptree_TypeParams (Nd n args) =
    if FST n = INL nTypeParams then
      case args of
        [tv] =>
          fmap (λt. [t]) $ ptree_TypeName tv
      | lpar :: tv :: rest =>
          do
            expect_tok lpar LparT;
            tn <- ptree_TypeName tv;
            ts <- ptree_TypeParamList rest;
            return (tn::ts)
          od
      | _ => fail "Impossible: nTypeParams"
    else
      fail "Expected a type-parameters non-terminal")
End

Definition ptree_TypeDef_def:
  (ptree_TypeDef (Lf t) =
    fail "Expected a typedef non-terminal") ∧
  (ptree_TypeDef (Nd n args) =
    if FST n = INL nTypeDef then
      case args of
        [tps; id; info] =>
          do
            tys <- ptree_TypeParams tps;
            nm <- ptree_Ident id;
            trs <- ptree_TypeInfo info;
            return (SND n, tys, nm, trs)
          od
      | [id; info] =>
          do
            nm <- ptree_Ident id;
            trs <- ptree_TypeInfo info;
            return (SND n, [], nm, trs)
          od
      | _ => fail "Impossible: nTypeDef"
    else
      fail "Expected a typedef non-terminal")
End

Definition ptree_TypeDefs_def:
  (ptree_TypeDefs (Lf t) =
    fail "Expected a typedef:s non-terminal") ∧
  (ptree_TypeDefs (Nd n args) =
    if FST n = INL nTypeDefs then
      case args of
        [td] =>
          fmap (λt. [t]) $ ptree_TypeDef td
      | [td; andt; tds] =>
          do
            expect_tok andt AndT;
            t <- ptree_TypeDef td;
            ts <- ptree_TypeDefs tds;
            return (t::ts)
          od
      | _ => fail "Impossible: nTypeDefs"
    else
      fail "Expected a typedef:s non-terminal")
End

(* Ocaml datatype definitions and type abbreviations can be made mutually
 * recursive with each other and this is not supported in CakeML. Example:
 *   type foo = A of bar | B of baz | ...
 *   and baz = foo list
 *)

Definition ptree_TypeDefinition_def:
  (ptree_TypeDefinition (Lf t) =
    fail "Expected a type definition non-terminal") ∧
  (ptree_TypeDefinition (Nd n args) =
    if FST n = INL nTypeDefinition then
      case args of
        [typet; nrec; tds] =>
          do
            expect_tok typet TypeT;
            expect_tok nrec NonrecT;
            tdefs <- ptree_TypeDefs tds;
            if EVERY (λ(locs,tys,nm,trs). ISL trs) tdefs then
              return $ MAP (λ(locs,tys,nm,trs). Dtabbrev locs tys nm (OUTL trs))
                           tdefs
            else if EVERY (λ(locs,tys,nm,trs). ISR trs) tdefs then
              return $ [Dtype (SND n) (MAP (λ(_,tys,nm,trs). (tys,nm,OUTR trs))
                                           tdefs)]
            else
              fail $ "Type abbreviations and datatype definitions cannot be" ++
                     " mutually recursive in CakeML"
          od
      | [typet; tds] =>
          do
            expect_tok typet TypeT;
            tdefs <- ptree_TypeDefs tds;
            (abbrevs,datas) <<- PARTITION (λ(_,tys,nm,trs). ISL trs) tdefs;
            abbrevs <<-
              MAP (λ(locs,tys,nm,trs). Dtabbrev locs tys nm (OUTL trs))
                  abbrevs;
            datas <<-
              Dtype (SND n) (MAP (λ(_,tys,nm,trs). (tys,nm,OUTR trs)) datas);
            return (datas::abbrevs)
          od
      | _ => fail "Impossible: nTypeDefinition"
    else
      fail "Expected a type definition non-terminal")
End

(* Build a top-level letrec out of a list of let rec-bindings.
 *)

Definition build_dletrec_def:
  build_dletrec locs binds =
    Dletrec locs (MAP (λ(f,ps,x). (f,"",Mat (Var (Short ""))
                                      [HD ps, build_fun_lam x (TL ps)]))
                      binds)
End

(* Builds a top-level let out of a list of let bindings.
 *)

Definition build_dlet_def:
  build_dlet locs binds =
    MAP (λbind.
           case bind of
             INL (p, x) => Dlet locs p x
           | INR (f, ps, x) => Dlet locs (Pvar f) (build_fun_lam x ps))
        binds
End

(* TODO
 * The location information gets a bit lost. ptree_LetBindings should also
 * return the location of the first token of each let binding (i.e. a pattern
 * or a variable name).
 *)

Definition ptree_ModPath_def:
  (ptree_ModPath (Lf t) =
    fail "Expected a module path non-terminal") ∧
  (ptree_ModPath (Nd n args) =
    if FST n = INL nModPath then
      case args of
        [arg] => ptree_Ident arg
      | _ => fail "Impossible: nModPath"
    else
      fail "Expected a module path non-terminal")
End

Definition ptree_Definition_def:
  (ptree_Definition (Lf t) =
    fail "Expected a top-level definition non-terminal") ∧
  (ptree_Definition (Nd n args) =
    if FST n = INL nTopLet then
      case args of
        [lett; lbs] =>
          do
            expect_tok lett LetT;
            binds <- ptree_LetBindings lbs;
            return (build_dlet (SND n) binds)
          od
      | _ => fail "Impossible: nTopLet"
    else if FST n = INL nTopLetRec then
      case args of
        [lett; rect; lbs] =>
          do
            expect_tok lett LetT;
            expect_tok rect RecT;
            binds <- ptree_LetRecBindings lbs;
            return [build_dletrec (SND n) binds]
          od
      | _ => fail "Impossible: nTopLetRec"
    else if FST n = INL nTypeDefinition then
      ptree_TypeDefinition (Nd n args)
    else if FST n = INL nExcDefinition then
      fmap (λd. [d]) $ ptree_ExcDefinition (Nd n args)
    else if FST n = INL nOpen then
      fail "open-declarations are not supported (yet)"
    else if FST n = INL nModuleDef then
      case args of
        [modt; modid; eq; mexpr] =>
          do
            expect_tok modt ModuleT;
            expect_tok eq EqualT;
            nm <- ptree_Ident modid;
            mx <- ptree_ModExpr mexpr;
            case mx of
              INL name =>
                fail "Structure assignment is not supported (yet?)"
            | INR decs =>
                return [Dmod nm decs]
          od
      | _ => fail "Impossible: nModuleDef"
    else
      fail "Expected a top-level definition non-terminal") ∧
  (ptree_ModExpr (Lf t) =
    fail "Expected a module expression non-terminal") ∧
  (ptree_ModExpr (Nd n args) =
    if FST n = INL nModExpr then
      case args of
        [path] => fmap INL $ ptree_ModPath path
      | [struct; its; endt] =>
          do
            expect_tok struct StructT;
            expect_tok endt EndT;
            fmap INR $ ptree_ModuleItems its
          od
    else
      fail "Expected a module expression non-terminal") ∧
  (ptree_ModuleItems (Lf t) =
    fail "Expected a module item list non-terminal") ∧
  (ptree_ModuleItems (Nd n args) =
    if FST n = INL nModuleItems then
      ptree_Items args
    else
      fail "Expected a module item list non-terminal") ∧
  (ptree_Items [] = fail "Empty module item lists are not supported") ∧
  (ptree_Items [t] =
    fmap (λx. []) (expect_tok t SemisT) ++
    ptree_ModuleItem t) ∧
  (ptree_Items (t::ts) =
    do
      i <- ptree_ModuleItem t;
      is <- ptree_Items ts;
      return (i ++ is)
    od) ∧
  (ptree_ModuleItem (Lf t) =
    fail "Expected a module item non-terminal") ∧
  (ptree_ModuleItem (Nd n args) =
    if FST n = INL nModuleItem then
      case args of
        [semis; exdef] =>
          do
            expect_tok semis SemiT;
            x <- ptree_Expr exdef;
            return [Dlet (SND n) (Pvar "") x]
          od ++
          ptree_Definition exdef
      | [exdef] =>
          do
            x <- ptree_Expr exdef;
            return [Dlet (SND n) (Pvar "") x]
          od ++
          ptree_Definition exdef
      | _ => fail "Impossible: nModuleItem"
    else
      fail "Expected a module item non-terminal")
Termination
  WF_REL_TAC ‘measure (sum_size psize (sum_size psize (sum_size psize
                      (sum_size p1size psize))))’
End

Definition ptree_Start_def:
  (ptree_Start (Lf t) =
    fail "Expected the start non-terminal") ∧
  (ptree_Start (Nd n args) =
    if FST n = INL nStart then
      case args of
        [] => return []
      | [modits] => ptree_ModuleItems modits
      | _ => fail "Impossible: nStart"
    else
      fail "Expected the start non-terminal")
End

val _ = export_theory ();

