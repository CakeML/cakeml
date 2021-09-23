(*
  A theory for converting OCaml parse trees to abstract syntax.
 *)

open preamble caml_lexTheory camlPEGTheory astTheory;

val _ = new_theory "camlPTreeConversion";

val _ = enable_monadsyntax ();
val _ = enable_monad "option";

Definition ifM_def:
  ifM bM tM eM =
    do
      b <- bM;
      if b then tM else eM
    od
End

Definition mapM_def:
  mapM f [] = SOME [] ∧
  mapM f (x::xs) =
    do
      y <- f x;
      ys <- mapM f xs;
      SOME (y::ys)
    od
End

Theorem mapM_cong[defncong]:
  ∀xs ys f g.
    xs = ys ∧
    (∀x. MEM x xs ⇒ f x = g x) ⇒
      mapM f xs = mapM g ys
Proof
  Induct \\ rw [mapM_def]
  \\ Cases_on ‘g h’ \\ fs [mapM_def]
  \\ ‘mapM f xs = mapM g xs’ suffices_by simp_tac std_ss []
  \\ first_x_assum irule \\ fs []
QED

Definition destLf_def:
  destLf (Lf x) = SOME x ∧
  destLf _ = NONE
End

Definition ptree_Ident_def:
  ptree_Ident (Lf t) = NONE ∧
  ptree_Ident (Nd n args) =
    do
      assert (FST n = INL nIdent);
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- destTOK lf;
            destIdent tk
          od
      | _ => NONE
    od
End

Definition ptree_Name_def:
  ptree_Name symb =
    do
      lf <- destLf symb;
      tk <- destTOK lf;
      destIdent tk
    od
End

Definition expect_tok_def:
  expect_tok symb token =
    do
      lf <- destLf symb;
      tk <- destTOK lf;
      assert (tk = token);
      SOME tk
    od
End

Definition ptree_TVar_def:
  ptree_TVar (Lf t) = NONE ∧
  ptree_TVar (Nd n args) =
    do
      assert (FST n = INL nTVar);
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            nm <- ptree_Ident id;
            SOME (TVar nm)
          od
      | _ => NONE
    od
End

Definition ptree_TAny_def:
  ptree_TAny (Lf t) = NONE ∧
  ptree_TAny (Nd n args) =
    do
      assert (FST n = INL nTAny);
      SOME TAny
    od
End

Definition ptree_Type_def:
  (ptree_Type (Lf _) = NONE) ∧
  (ptree_Type (Nd n args) =
    if FST n = INL nType then
      case args of
        [ty] => ptree_Type ty
      | _ => NONE
    else if FST n = INL nTBase then
      case args of
        [lpar; args; rpar; ctor] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ts <- ptree_TypeList args;
            nm <- ptree_Name ctor;
            SOME (TCons nm ts)
          od
      | [lpar; arg; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Type arg
          od
      | [arg] =>
          ptree_TVar arg ++ ptree_TAny arg
      | _ => NONE
    else if FST n = INL nTConstr then
      case args of
        [arg] => ptree_Type arg
      | arg::rest =>
          do
            ty <- ptree_Type arg;
            ids <- mapM ptree_Name rest;
            SOME (FOLDL (λt id. TCons id [t]) ty ids)
          od
      | _ => NONE
    else if FST n = INL nTProd then
      case args of
        [arg] => ptree_Type arg
      | [arg;star;prod] =>
          do
            expect_tok star StarT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type prod;
            SOME (TProd ty1 ty2)
          od
      | _ => NONE
    else if FST n = INL nTFun then
      case args of
        [arg] => ptree_Type arg
      | [arg;rarrow;fun] =>
          do
            expect_tok rarrow RarrowT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type fun;
            SOME (TFun ty1 ty2)
          od
      | _ => NONE
    else if FST n = INL nTAs then
      case args of
        [arg] => ptree_Type arg
      | [arg;as;tick;id] =>
          do
            expect_tok as AsT;
            expect_tok tick TickT;
            ty <- ptree_Type arg;
            nm <- ptree_Name id;
            SOME (TAs ty nm)
          od
      | _ => NONE
    else
      NONE) ∧
  (ptree_TypeList (Lf t) : type list option = NONE) ∧
  (ptree_TypeList (Nd n args) =
    if FST n = INL nTypeList then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            SOME (t::ts)
          od
      | _ => NONE
    else if FST n = INL nTypeLists then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            SOME (t::ts)
          od
      | [typ] =>
          do
            t <- ptree_Type typ;
            SOME [t]
          od
      | _ => NONE
    else
      NONE)
End

Definition ptree_Literal:
  ptree_Literal (Lf t) = NONE ∧
  ptree_Literal (Nd n args) =
    do
      assert (FST n = INL nLiteral);
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- destTOK lf;
            case tk of
              TrueT => SOME (Lbool T)
            | FalseT => SOME (Lbool F)
            | IntT n => SOME (Lint n)
            | CharT c => SOME (Lchar c)
            | StringT s => SOME (Lstring s)
            | _ => NONE
          od
      | _ => NONE
    od
End

Definition ptree_Op_def:
  ptree_Op (Lf t) = NONE ∧
  ptree_Op (Nd n args) =
    case args of
      [arg] =>
        do
          lf <- destLf arg;
          tk <- destTOK lf;
          if FST n = INL nShiftOp then
            case tk of
              LslT => SOME (INR Lsl)
            | LsrT => SOME (INR Lsr)
            | AsrT => SOME (INR Asr)
            | SymbolT "**" => SOME (INR FExp)
            | SymbolT s => SOME (INL s)
            | _ => NONE
          else if FST n = INL nMultOp then
            case tk of
              StarT => SOME (INR Mult)
            | LandT => SOME (INR Land)
            | LorT => SOME (INR Lor)
            | LxorT => SOME (INR Lxor)
            | SymbolT "/" => SOME (INR Div)
            | SymbolT "*." => SOME (INR FMult)
            | SymbolT "/." => SOME (INR FDiv)
            | SymbolT s => SOME (INL s)
            | _ => NONE
          else if FST n = INL nAddOp then
            case tk of
              PlusT => SOME (INR Add)
            | MinusT => SOME (INR Sub)
            | MinusFT => SOME (INR FSub)
            | SymbolT "+." => SOME (INR FAdd)
            | SymbolT s => SOME (INL s)
            | _ => NONE
          else if FST n = INL nRelOp then
            case tk of
              LessT => SOME (INR Le)
            | GreaterT => SOME (INR Ge)
            | EqualT => SOME (INR Eq)
            | SymbolT "<=" => SOME (INR Leq)
            | SymbolT ">=" => SOME (INR Geq)
            | SymbolT "<." => SOME (INR FLe)
            | SymbolT ">." => SOME (INR FGe)
            | SymbolT "<=." => SOME (INR FLeq)
            | SymbolT ">=." => SOME (INR FGeq)
            | SymbolT s => SOME (INL s)
            | _ => NONE
          else if FST n = INL nAndOp then
            case tk of
              AndalsoT => SOME (INR And)
            | AmpT => SOME (INR And)
            | SymbolT s => SOME (INL s)
            | _ => NONE
          else if FST n = INL nOrOp then
            case tk of
              OrelseT => SOME (INR Or)
            | OrT => SOME (INR Or)
            | SymbolT s => SOME (INL s)
            | _ => NONE
          else
            NONE
        od
    | _ => NONE
End

Definition ptree_Pattern_def:
  (ptree_Pattern (Lf t) = NONE) ∧
  (ptree_Pattern (Nd n args) =
    if FST n = INL nPAny then
      case args of
        [arg] =>
          do
            expect_tok arg AnyT;
            SOME PAny
          od
      | _ => NONE
    else if FST n = INL nPBase then
      case args of
        [arg] =>
          OPTION_MAP PVar (ptree_Ident arg) ++
          ptree_Pattern arg
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
            SOME (PCons ".." [PLit c1; PLit c2])
          od
      | [lpar; pat; colon; typ; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            p <- ptree_Pattern pat;
            ty <- ptree_Type typ;
            SOME (PTyped p ty)
          od
      | _ => NONE
    else if FST n = INL nPList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            pats <- ptree_PatternList rest;
            SOME (FOLDR (λt p. PCons "::" [t; p]) (PCons "[]" []) pats)
          od
      | _ => NONE
    else if FST n = INL nPLazy then
      case args of
        [pat] => ptree_Pattern pat
      | [lazy; pat] =>
          do
            expect_tok lazy LazyT;
            p <- ptree_Pattern pat;
            SOME (PCons "lazy" [p])
          od
      | _ => NONE
    else if FST n = INL nPConstr then
      case args of
        [pat] => ptree_Pattern pat
      | [id; pat] =>
          do
            nm <- ptree_Name id;
            p <- ptree_Pattern pat;
            SOME (PCons nm [p])
          od
      | _ => NONE
    else if FST n = INL nPApp then
      case args of
        [pat] => ptree_Pattern pat
      | _ => NONE
    else if FST n = INL nPCons then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; colons; p2] =>
          do
            expect_tok colons ColonT;
            q1 <- ptree_Pattern p1;
            q2 <- ptree_Pattern p2;
            SOME (PCons "::" [q1; q2])
          od
      | _ => NONE
    else if FST n = INL nPProd then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; comma; p2] =>
          do
            expect_tok comma CommaT;
            q1 <- ptree_Pattern p1;
            q2 <- ptree_Pattern p2;
            SOME (PCons "," [q1; q2])
          od
      | _ => NONE
    else if FST n = INL nPOr then
      case args of
        [pat] => ptree_Pattern pat
      | [p1; bar; p2] =>
          do
            expect_tok bar BarT;
            q1 <- ptree_Pattern p1;
            q2 <- ptree_Pattern p2;
            SOME (POr q1 q2)
          od
      | _ => NONE
    else if FST n = INL nPAs then
      case args of
        [pat] => ptree_Pattern pat
      | [pat; as; id] =>
          do
            expect_tok as AsT;
            p <- ptree_Pattern pat;
            nm <- ptree_Name id;
            SOME (PAs p nm)
          od
      | _ => NONE
    else if FST n = INL nPattern then
      case args of
        [pat] => ptree_Pattern pat
      | _ => NONE
    else
      NONE) ∧
  (ptree_PatternList [] = NONE) ∧
  (ptree_PatternList [t] =
     do
       expect_tok t RbrackT;
       SOME []
     od) ∧
  (ptree_PatternList (p::ps) =
     do
       q <- ptree_Pattern p;
       qs <- ptree_PatternList ps;
       SOME (q::qs)
     od)
Termination
  WF_REL_TAC ‘inv_image $<
                (λx. if ISL x
                     then parsetree_size (K 0) (K 0) (K 0) (OUTL x)
                     else parsetree1_size (K 0) (K 0) (K 0) (OUTR x))’
  \\ rw [] \\ gs [grammarTheory.parsetree_size_def]
End

Definition ptree_Patterns_def:
  (ptree_Patterns (Lf t) = NONE) ∧
  (ptree_Patterns (Nd n args) =
    if FST n = INL nPatterns then
      case args of
        [pat] => OPTION_MAP (λx. [x]) (ptree_Pattern pat)
      | [pat; rest] =>
          do
            p <- ptree_Pattern pat;
            ps <- ptree_Patterns rest;
            SOME (p::ps)
          od
      | _ => NONE
    else
      NONE)
End

Definition build_binop_def:
  build_binop (INR opn) x y = Op opn [x; y] ∧
  build_binop (INL symb) x y = App (App (Id symb) x) y
End

Theorem parsetree_size_lemma[local]:
  ∀xs x. MEM x xs ⇒ parsetree_size (K 0) (K 0) (K 0) x <
                    parsetree1_size (K 0) (K 0) (K 0) xs
Proof
  Induct \\ rw [] \\ gs [grammarTheory.parsetree_size_def]
  \\ res_tac \\ fs []
QED

(* TODO Figure out what to do with the stuff that comes out of
        ptree_Letbinding.

        The ones with patterns on the left are particularily annoying/
        problematic, and they're used throughout the HOL light sources.
        Examples:

        let fun1, fun2 = ... ;;
        let [a; b; c] = CONJUNCTS foo;;

 *)

Definition ptree_Expr:
  (ptree_Expr (Lf t) = NONE) ∧
  (ptree_Expr (Nd n args) =
    if FST n = INL nEList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            exps <- ptree_ExprList rest;
            SOME (FOLDR (λt e. Cons "::" [t; e]) (Cons "[]" []) exps)
          od
      | _ => NONE
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
            SOME (Typed x ty)
          od
      | [arg] =>
          OPTION_MAP Lit (ptree_Literal arg) ++
          OPTION_MAP Id (ptree_Ident arg) ++
          ptree_Expr arg
      | _ => NONE
    else if FST n = INL nEAssert then
      case args of
        [assr; expr] =>
          do
            expect_tok assr AssertT;
            x <- ptree_Expr expr;
            SOME (App (Id "assert") x)
          od
      | _ => NONE
    else if FST n = INL nELazy then
      case args of
        [lazy; expr] =>
          do
            expect_tok lazy LazyT;
            x <- ptree_Expr expr;
            SOME (App (Id "lazy") x)
          od
      | _ => NONE
    else if FST n = INL nEConstr then
      case args of
        [consid; expr] =>
          do
            id <- ptree_Name consid;
            x <- ptree_Expr expr;
            SOME (Cons id [x])
          od
      | _ => NONE
    else if FST n = INL nEFunapp then
      case args of
        funexp::funargs =>
          do
            x <- ptree_Expr funexp;
            xs <- mapM ptree_Expr funargs;
            SOME (FOLDL App x xs)
          od
      | _ => NONE
    else if FST n = INL nEApp then
      case args of
        [arg] => ptree_Expr arg
      | _ => NONE
    else if FST n = INL nEPrefix then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- destTOK lf;
            sym <- destSymbol tk;
            x <- ptree_Expr expr;
            SOME (App (Id sym) x)
          od
      | [arg] => ptree_Expr arg
      | _ => NONE
    else if FST n = INL nENeg then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- destTOK lf;
            x <- ptree_Expr expr;
            case tk of
              MinusT => SOME (Op Neg [x])
            | MinusFT => SOME (Op FNeg [x])
            | SymbolT s => SOME (App (Id s) x)
            | _ => NONE
          od
      | [arg] => ptree_Expr arg
      | _ => NONE
    else if FST n = INL nEShift then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            SOME (build_binop op x y)
          od
      | _ => NONE
    else if FST n = INL nEMult then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            SOME (build_binop op x y)
          od
      | _ => NONE
    else if FST n = INL nEAdd then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            SOME (build_binop op x y)
          od
      | _ => NONE
    else if FST n = INL nECons then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; colons; rhs] =>
          do
            expect_tok colons ColonsT;
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            SOME (Cons "::" [x; y])
          od
      | _ => NONE
    else if FST n = INL nECat then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            SOME (FOLDL App (Id "String.cat") [x; y])
          od
      | _ => NONE
    else if FST n = INL nERel then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            SOME (build_binop op x y)
          od
      | _ => NONE
    else if FST n = INL nEAnd then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            SOME (build_binop op x y)
          od
      | _ => NONE
    else if FST n = INL nEOr then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            op <- ptree_Op opn;
            SOME (build_binop op x y)
          od
      | _ => NONE
    else if FST n = INL nEProd then
      case args of
        [exp] => ptree_Expr exp
      | [lhs; comma; rhs] =>
          do
            expect_tok comma CommaT;
            x <- ptree_Expr lhs;
            y <- ptree_Expr rhs;
            SOME (Cons "," [x; y])
          od
      | _ => NONE
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
            SOME (If x1 y1 z1)
          od
      | [ift; x; thent; y] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            x1 <- ptree_Expr x;
            y1 <- ptree_Expr y;
            SOME (If x1 y1 (Cons "()" []))
          od
      | _ => NONE
    else if FST n = INL nESeq then
      case args of
        [x; semi; y] =>
          do
            expect_tok semi SemiT;
            x1 <- ptree_Expr x;
            y1 <- ptree_Expr y;
            SOME (Seq x1 y1)
          od
      | [x] => ptree_Expr x
      | _ => NONE
    else if FST n = INL nELet then
      case args of
        [lett; rec; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok rec RecT;
            expect_tok int InT;
            bs <- ptree_LetBinding binds;
            x <- ptree_Expr expr;
            ARB (*
            SOME (Let T bs x) *)
          od
      | [lett; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok int InT;
            bs <- ptree_LetBinding binds;
            x <- ptree_Expr expr;
            ARB (*
            SOME (Let F bs x) *)
          od
      | _ => NONE
    else if FST n = INL nEMatch then
      case args of
        [match; expr; witht; pmatch] =>
          do
            expect_tok match MatchT;
            expect_tok witht WithT;
            x <- ptree_Expr expr;
            ps <- ptree_PatternMatch pmatch;
            SOME (Match x ps)
          od
      | _ => NONE
    else if FST n = INL nEFun then
      case args of
        [funt; params; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr expr;
            ARB (* Fun does not accept a pattern; use match *)
          od
      | [funt; params; colon; typ; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr expr;
            ty <- ptree_Type typ;
            assert (¬NULL ps);
            ARB (* Fun does not accept a pattern; use match *)
          od
      | _ => NONE
    else if FST n = INL nEFunction then
      case args of
        [funct; pmatch] =>
          do
            expect_tok funct FunctionT;
            pms <- ptree_PatternMatch pmatch;
            SOME (Fun "" (Match (Id "") pms))
          od
      | _ => NONE
    else if FST n = INL nETry then
      case args of
        [tryt; expr; witht; pmatch] =>
          do
            expect_tok tryt TryT;
            expect_tok witht WithT;
            x <- ptree_Expr expr;
            pms <- ptree_PatternMatch pmatch;
            SOME (Try x pms)
          od
      | _ => NONE
    else if FST n = INL nEWhile then
      case args of
        [while; expr; dot; body; donet] =>
          do
            expect_tok while WhileT;
            expect_tok dot DoT;
            expect_tok donet DoneT;
            x <- ptree_Expr expr;
            b <- ptree_Expr body;
            SOME (FOLDL App (Id "while") [x; b])
          od
      | _ => NONE
    else if FST n = INL nEFor then
      case args of
        [for; ident; eq; ubd; updown; lbd; dot; body; donet] =>
          do
            expect_tok for ForT;
            expect_tok eq EqualT;
            expect_tok dot DoT;
            lf <- destLf updown;
            tk <- destTOK lf;
            assert (tk = ToT ∨ tk = DowntoT);
            id <- ptree_Ident ident;
            u <- ptree_Expr ubd;
            l <- ptree_Expr lbd;
            b <- ptree_Expr body;
            SOME (FOLDL App (Id "for")
                        [Lit (Lbool (tk = ToT)); Id id; u; l; b])
          od
      | _ => NONE
    else if FST n = INL nExpr then
      case args of
        [arg] => ptree_Expr arg
      | _ => NONE
    else
      NONE) ∧
  (ptree_PatternMatch (Lf t) = NONE) ∧
  (ptree_PatternMatch (Nd n args) =
    if FST n = INL nPatternMatch then
      case args of
        [bar; pms] =>
          do
            expect_tok bar BarT;
            ptree_PatternMatch pms
          od
      | [pms] => ptree_PatternMatch pms
      | _ => NONE
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
              [] => SOME [p, x, SOME w]
            | [bar; pms] =>
                do
                  expect_tok bar BarT;
                  ps <- ptree_PatternMatch pms;
                  SOME ((p, x, SOME w)::ps)
                od
            | _ => NONE
          od
      | pat :: rarrow :: body :: rest =>
          do
            expect_tok rarrow RarrowT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr body;
            case rest of
              [] => SOME [p, x, NONE]
            | [bar; pms] =>
                do
                  expect_tok bar BarT;
                  ps <- ptree_PatternMatch pms;
                  SOME ((p, x, NONE)::ps)
                od
            | _ => NONE
          od
      | _ => NONE
    else
      NONE) ∧
  (ptree_LetBinding (Lf t) = NONE) ∧
  (ptree_LetBinding (Nd n args) =
    if FST n = INL nLetBinding then
      case args of
        [pat; eq; bod] =>
          do
            expect_tok eq EqualT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr bod;
            SOME [(NONE, [p], x)]
          od
      | [id; pats; eq; bod] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_Ident id;
            ps <- ptree_Patterns pats;
            x <- ptree_Expr bod;
            SOME [(SOME n, ps, x)]
          od
      | [id; pats; colon; typ; eq; bod] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_Ident id;
            ps <- ptree_Patterns pats;
            x <- ptree_Expr bod;
            SOME [(SOME n, ps, x)]
          od
      | _ => NONE
    else if FST n = INL nLetBindings then
      case args of
        [lb] => ptree_LetBinding lb
      | [lb; andt; lbs] =>
          do
            l1 <- ptree_LetBinding lb;
            l2 <- ptree_LetBinding lbs;
            SOME (l1 ++ l2)
          od
      | _ => NONE
    else
      NONE) ∧
  (ptree_ExprList [] = NONE) ∧
  (ptree_ExprList [t] =
    do
      expect_tok t RbrackT;
      SOME []
    od) ∧
  (ptree_ExprList (t::ts) =
    do
      expect_tok t SemiT;
      ptree_ExprList ts
    od ++
    do
      e <- ptree_Expr t;
      es <- ptree_ExprList ts;
      SOME (e::es)
    od)
Termination
  WF_REL_TAC ‘inv_image $<
              (λx. case x of
                     INL x => parsetree_size (K 0) (K 0) (K 0) x
                   | INR (INL x) => parsetree_size (K 0) (K 0) (K 0) x
                   | INR (INR (INL x)) => parsetree_size (K 0) (K 0) (K 0) x
                   | INR (INR (INR x)) => parsetree1_size (K 0) (K 0) (K 0) x)’
  \\ rw [] \\ gs [grammarTheory.parsetree_size_def]
  \\ imp_res_tac parsetree_size_lemma \\ gs []
End

val _ = export_theory ();

