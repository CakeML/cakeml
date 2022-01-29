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
  option NONE = INL (unknown_loc, «option») ∧
  option (SOME x) = INR x
End

Definition fmap_def[simp]:
  fmap f (INR x) = INR (f x) ∧
  fmap f (INL err) = INL err
End

(* -------------------------------------------------------------------------
 * Parse tree conversion
 * ------------------------------------------------------------------------- *)

Overload psize[local] = “parsetree_size (K 0) (K 0) (K 0)”;

Overload p1size[local] = “parsetree1_size (K 0) (K 0) (K 0)”;

Theorem parsetree_size_lemma[local]:
  p1size = list_size psize
Proof
  rw [FUN_EQ_THM]
  \\ Induct_on ‘x’ \\ rw [list_size_def, grammarTheory.parsetree_size_def]
QED

Definition destLf_def:
  destLf (Lf x) = return x ∧
  destLf (Nd (nterm, locs) _) = fail (locs, «destLf»)
End

Definition expect_tok_def:
  expect_tok symb (token: token) =
    do
      lf <- destLf symb;
      tk <- option $ destTOK lf;
      if tk = token then
        return tk
      else
        fail (SND lf, «Unexpected token»)
    od
End

Definition path_to_ns_def:
  path_to_ns locs [] = fail (locs, «Empty path») ∧
  path_to_ns locs [i] = return (Short i) ∧
  path_to_ns locs (m::ms) =
    do
      id <- path_to_ns locs ms;
      return $ Long m id
    od
End

Definition ptree_Ident_def:
  ptree_Ident (Lf (_, locs)) = fail (locs, «Expected ident non-terminal») ∧
  ptree_Ident (Nd (nterm, locs) args) =
    if nterm = INL nIdent then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nIdent»)
    else
      fail (locs, «Expected ident non-terminal»)
End

(* Returns a (function) name corresponding to the operator.
 *)

Definition ptree_Op_def:
  ptree_Op (Lf (_, locs)) =
    fail (locs, «Expected operator non-terminal») ∧
  ptree_Op (Nd (nterm, locs) args) =
    case args of
      [arg] =>
        do
          lf <- destLf arg;
          tk <- option $ destTOK lf;
          if nterm = INL nShiftOp then
            if tk = LslT then
              return "lsl"
            else if tk = LsrT then
              return "lsr"
            else if tk = AsrT then
              return "asr"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nShiftOp»)
          else if nterm = INL nMultOp then
            if tk = StarT then
              return "*"
            else if tk = ModT then
              return "mod"
            else if tk = LandT then
              return "land"
            else if tk = LorT then
              return "lor"
            else if tk = LxorT then
              return "lxor"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nMultOp»)
          else if nterm = INL nAddOp then
            if tk = PlusT then
              return "+"
            else if tk = MinusT then
              return "-"
            else if tk = MinusFT then
              return "-."
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
             fail (locs, «Impossible: nAddOp»)
          else if nterm = INL nRelOp then
            if tk = LessT then
              return "<"
            else if tk = GreaterT then
              return ">"
            else if tk = EqualT then
              return "="
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nRelOp»)
          else if nterm = INL nAndOp then
            if tk = AndalsoT then
              return "&&"
            else if tk = AmpT then
              return "&"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nAndOp»)
          else if nterm = INL nOrOp then
            if tk = OrelseT then
              return "||"
            else if tk = OrT then
              return "|"
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nOrOp»)
          else if nterm = INL nHolInfixOp then
            if tk = FuncompT then
              return "o"
            else if tk = F_FT then
              return "F_F"
            else if tk = THEN_T then
              return "THEN"
            else if tk = THENC_T then
              return "THENC"
            else if tk = THENL_T then
              return "THENL"
            else if tk = THEN_TCL_T then
              return "THEN_TCL"
            else if tk = ORELSE_T then
              return "ORELSE"
            else if tk = ORELSEC_T then
              return "ORELSEC"
            else if tk = ORELSE_TCL_T then
              return "ORELSE_TCL"
            else
              fail (locs, «Impossible: nHolInfixOp»)
          else if nterm = INL nCatOp then
            if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nCatOp»)
          else if nterm = INL nPrefixOp then
            if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nPrefixOp»)
          else if nterm = INL nAssignOp then
            if tk = LarrowT then
              return "<-"
            else if tk = UpdateT then
              return ":="
            else
              fail (locs, «Impossible: nAssignOp»)
          else
            fail (locs, «Expected operator non-terminal»)
        od
    | _ => fail (locs, «Expected operator non-terminal»)
End

Definition ptree_OperatorName_def:
  ptree_OperatorName (Lf (_, locs)) =
    fail (locs, «Expected operator-name non-terminal») ∧
  ptree_OperatorName (Nd (nterm, locs) args) =
    if nterm = INL nOperatorName then
      case args of
        [arg] => ptree_Op arg
      | _ => fail (locs, «Impossible: nOperatorName»)
    else
      fail (locs, «Expected operator-name non-terminal»)
End

Definition ptree_ValueName_def:
  ptree_ValueName (Lf (_, locs)) =
    fail (locs, «Expected value-name non-terminal») ∧
  ptree_ValueName (Nd (nterm, locs) args) =
    if nterm = INL nValueName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | [lpar; opn; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_OperatorName opn
          od
      | _ => fail (locs, «Impossible: nValueName»)
    else
      fail (locs, «Expected value-name non-terminal»)
End

Definition ptree_ConstrName_def:
  ptree_ConstrName (Lf (_, locs)) =
    fail (locs, «Expected constr-name non-terminal») ∧
  ptree_ConstrName (Nd (nterm, locs) args) =
    if nterm = INL nConstrName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nConstrName»)
    else
      fail (locs, «Expected constr-name non-terminal»)
End

Definition ptree_TypeConstrName_def:
  ptree_TypeConstrName (Lf (_, locs)) =
    fail (locs, «Expected typeconstr-name non-terminal») ∧
  ptree_TypeConstrName (Nd (nterm, locs) args) =
    if nterm = INL nTypeConstrName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nTypeConstrName»)
    else
      fail (locs, «Expected typeconstr-name non-terminal»)
End

Definition ptree_ModuleName_def:
  ptree_ModuleName (Lf (_, locs)) =
    fail (locs, «Expected modulename non-terminal») ∧
  ptree_ModuleName (Nd (nterm, locs) args) =
    if nterm = INL nModuleName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nModuleName»)
    else
      fail (locs, «Expected modulename non-terminal»)
End

Definition ptree_ModTypeName_def:
  ptree_ModTypeName (Lf (_, locs)) =
    fail (locs, «Expected modtypename non-terminal») ∧
  ptree_ModTypeName (Nd (nterm, locs) args) =
    if nterm = INL nModTypeName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nModTypeName»)
    else
      fail (locs, «Expected modtypename non-terminal»)
End

Definition ptree_ModulePath_def:
  ptree_ModulePath (Lf (_, locs)) =
    fail (locs, «Expected module-path non-terminal») ∧
  ptree_ModulePath (Nd (nterm, locs) args) =
    if nterm = INL nModulePath then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ModuleName arg
      | [arg; dot; path] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModulePath path;
            vn <- ptree_ModuleName arg;
            return (vn::vp)
          od
      | _ => fail (locs, «Impossible: nModulePath»)
    else
      fail (locs, «Expected module-path non-terminal»)
End

Definition ptree_ValuePath_def:
  ptree_ValuePath (Lf (_, locs)) =
    fail (locs, «Expected value-path non-terminal») ∧
  ptree_ValuePath (Nd (nterm, locs) args) =
    if nterm = INL nValuePath then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ValueName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModulePath path;
            vn <- ptree_ValueName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nValuePath»)
    else
      fail (locs, «Expected value-path non-terminal»)
End

Definition ptree_Constr_def:
  ptree_Constr (Lf (_, locs)) = fail (locs, «Expected constr non-terminal») ∧
  ptree_Constr (Nd (nterm, locs) args) =
    if nterm = INL nConstr then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ConstrName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModulePath path;
            vn <- ptree_ConstrName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nConstr»)
    else
      fail (locs, «Expected constr non-terminal»)
End

Definition ptree_TypeConstr_def:
  ptree_TypeConstr (Lf (_, locs)) =
    fail (locs, «Expected typeconstr non-terminal») ∧
  ptree_TypeConstr (Nd (nterm, locs) args) =
    if nterm = INL nTypeConstr then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_TypeConstrName arg
      | [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModulePath path;
            vn <- ptree_TypeConstrName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nTypeConstr»)
    else
      fail (locs, «Expected typeconstr non-terminal»)
End

Definition ptree_ModTypePath_def:
  ptree_ModTypePath (Lf (_, locs)) =
    fail (locs, «Expected modtypepath non-terminal») ∧
  ptree_ModTypePath (Nd (nterm, locs) args) =
    if nterm = INL nModTypePath then
      case args of
        [path; dot; arg] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModulePath path;
            vn <- ptree_ModTypeName arg;
            return (vp ++ [vn])
          od
      | _ => fail (locs, «Impossible: nModTypePath»)
    else
      fail (locs, «Expected typeconstr non-terminal»)
End

Definition ptree_TVar_def:
  ptree_TVar (Lf (_, locs)) =
    fail (locs, «Expected type variable non-terminal») ∧
  ptree_TVar (Nd (nterm, locs) args) =
    if nterm = INL nTVar then
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            nm <- ptree_Ident id;
            return (Atvar nm)
          od
      | _ => fail (locs, «Impossible: nTVar»)
    else
      fail (locs, «Expected type variable non-terminal»)
End

Definition ptree_Type_def:
  (ptree_Type (Lf (_, locs)) =
    fail (locs, «Expected a type non-terminal»)) ∧
  (ptree_Type (Nd (nterm, locs) args) =
    if nterm = INL nType then
      case args of
        [ty] => ptree_Type ty
      | _ => fail (locs, «Impossible: nType»)
    else if nterm = INL nTBase then
      case args of
        [lpar; args; rpar; ctor] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ts <- ptree_TypeList args;
            nm <- ptree_TypeConstr ctor;
            ns <- path_to_ns locs nm;
            return (Atapp ts ns)
          od
      | [lpar; arg; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Type arg
          od
      | [arg] =>
          ptree_TVar arg
      | _ => fail (locs, «Impossible: nTBase»)
    else if nterm = INL nTConstr then
      case args of
        arg::rest =>
          do
            ty <- ptree_Type arg;
            ids <- mapM ptree_TypeConstr rest;
            cns <- mapM (path_to_ns locs) ids;
            return (FOLDL (λt id. Atapp [t] id) ty cns)
          od ++
          do
            id <- ptree_TypeConstr arg;
            cn <- path_to_ns locs id;
            ids <- mapM ptree_TypeConstr rest;
            cns <- mapM (path_to_ns locs) ids;
            return (FOLDL (λt id. Atapp [t] id) (Atapp [] cn) cns)
          od
      | _ => fail (locs, «Impossible: nTConstr»)
    else if nterm = INL nTProd then
      case args of
        arg::rest =>
          do
            ty <- ptree_Type arg;
            ts <- ptree_StarTypes rest;
            return (Attup (ty::ts))
          od
      | _ => fail (locs, «Impossible: nTProd»)
    else if nterm = INL nTFun then
      case args of
        [arg] => ptree_Type arg
      | [arg;rarrow;fun] =>
          do
            expect_tok rarrow RarrowT;
            ty1 <- ptree_Type arg;
            ty2 <- ptree_Type fun;
            return (Atfun ty1 ty2)
          od
      | _ => fail (locs, «Impossible: nTFun»)
    else
      fail (locs, «Expected type non-terminal»)) ∧
  (ptree_TypeList (Lf (_, locs)) =
    fail (locs, «Expected a type list non-terminal»)) ∧
  (ptree_TypeList (Nd (nterm, locs) args) =
    if nterm = INL nTypeList then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            return (t::ts)
          od
      | _ => fail (locs, «Impossible: nTypeList»)
    else if nterm = INL nTypeLists then
      case args of
        [typ;comma;tlist] =>
          do
            t <- ptree_Type typ;
            expect_tok comma CommaT;
            ts <- ptree_TypeList tlist;
            return (t::ts)
          od
      | [typ] => fmap (λt. [t]) $ ptree_Type typ
      | _ => fail (locs, «Impossible: nTypeLists»)
    else
      fail (locs, «Expected a type list non-terminal»)) ∧
  (ptree_StarTypes [] = return []) ∧
  (ptree_StarTypes (x::xs) =
    do
      expect_tok x StarT;
      ptree_StarTypes xs
    od ++
    do
      t <- ptree_Type x;
      ts <- ptree_StarTypes xs;
      return (t::ts)
    od)
Termination
  WF_REL_TAC ‘measure $ sum_size psize $
                        sum_size psize (list_size psize)’
  \\ simp [parsetree_size_lemma]
End

Definition ptree_Literal_def:
  ptree_Literal (Lf (_, locs)) =
    fail (locs, «Expected a literal non-terminal») ∧
  ptree_Literal (Nd (nterm, locs) args) =
    if nterm = INL nLiteral then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if isInt tk then
              return $ IntLit $ THE $ destInt tk
            else if isChar tk then
              return $ Char $ THE $ destChar tk
            else if isString tk then
              return $ StrLit $ THE $ destString tk
            else
              fail (locs, «Impossible: nLiteral»)
          od
      | _ => fail (locs, «Impossible: nLiteral»)
    else
      fail (locs, «Expected a literal non-terminal»)
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

Definition nterm_of_def:
  nterm_of (Lf (_, locs)) = fail (locs, «nterm_of: Not a parsetree node») ∧
  nterm_of (Nd (nterm, _) args) = return nterm
End

(* The parse trees contain or-patterns. “ptree_Pattern” creates one result
 * for each alternative in a or-pattern, as if all or-patterns were pulled up
 * to the top of the tree.
 *)

Definition ptree_Pattern_def:
  (ptree_Pattern et (Lf (_, locs)) =
    fail (locs, «Expected a pattern non-terminal»)) ∧
  (ptree_Pattern et (Nd (nterm, locs) args) =
    if INL et ≠ nterm then
      fail (locs, «ptree_Pattern»)
    else if nterm = INL nPAny then
      case args of
        [arg] =>
          do
            expect_tok arg AnyT;
            return [Pany]
          od
      | _ => fail (locs, «Impossible: nPAny»)
    else if nterm = INL nPBase then
      case args of
        [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nValueName then
              fmap (λn. [Pvar n]) (ptree_ValueName arg)
            else if n = INL nPAny then
              ptree_Pattern nPAny arg
            else if n = INL nPList then
              ptree_Pattern nPList arg
            else if n = INL nLiteral then
              fmap (λlit. [Plit lit]) (ptree_Literal arg)
            else
              fail (locs, «Impossible: nPBase»)
         od
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
            ptree_Pattern nPattern p
          od
      | [lpar; pat; colon; typ; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            ps <- ptree_Pattern nPattern pat;
            ty <- ptree_Type typ;
            return (MAP (λp. Ptannot p ty) ps)
          od
      | _ => fail (locs, «Impossible: nPBase»)
    else if nterm = INL nPList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            pats <- ptree_PatternList rest;
            return (MAP build_list_pat (list_cart_prod pats))
          od
      | _ => fail (locs, «Impossible: nPList»)
    else if nterm = INL nPLazy then
      case args of
        [pat] => ptree_Pattern nPBase pat
      | [lazy; pat] =>
          do
            expect_tok lazy LazyT;
            ps <- ptree_Pattern nPBase pat;
            return (MAP (λp. Pcon (SOME (Short "lazy")) [p]) ps)
          od
      | _ => fail (locs, «Impossible: nPLazy»)
    else if nterm = INL nPConstr then
      case args of
        [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nConstr then
              do
                cns <- ptree_Constr arg;
                id <- path_to_ns locs cns;
                return [Pcon (SOME id) []]
              od
            else
              ptree_Pattern nPLazy arg
          od
      | [id; pat] =>
          do
            cns <- ptree_Constr id;
            id <- path_to_ns locs cns;
            ps <- ptree_Pattern nPLazy pat;
            return (MAP (λp. Pcon (SOME id) [p]) ps)
          od
      | _ => fail (locs, «Impossible: nPConstr»)
    else if nterm = INL nPApp then
      case args of
        [pat] =>
          do
            n <- nterm_of pat;
            if n = INL nPConstr then
              ptree_Pattern nPConstr pat
            else if n = INL nPLazy then
              ptree_Pattern nPLazy pat
            else
              fail (locs, «Impossible: nPApp»)
          od
      | _ => fail (locs, «Impossible: nPApp»)
    else if nterm = INL nPCons then
      case args of
        [pat] => ptree_Pattern nPApp pat
      | [p1; colons; p2] =>
          do
            expect_tok colons ColonsT;
            ps <- ptree_Pattern nPApp p1;
            qs <- ptree_Pattern nPCons p2;
            return (MAP (λ(p,q). Pcon (SOME (Short "::")) [p; q])
                        (cart_prod ps qs))
          od
      | _ => fail (locs, «Impossible: nPCons»)
    else if nterm = INL nPProd then
      case args of
        [pat] => ptree_Pattern nPCons pat
      | pat::pats =>
          do
            p <- ptree_Pattern nPCons pat;
            ps <- ptree_PatternCommas pats;
            return (MAP (λps. Pcon NONE ps) (list_cart_prod (p::ps)))
          od
      | _ => fail (locs, «Impossible: nPProd»)
    else if nterm = INL nPOr then
      case args of
        [pat] => ptree_Pattern nPProd pat
      | [p1; bar; p2] =>
          do
            expect_tok bar BarT;
            ps <- ptree_Pattern nPOr p1;
            qs <- ptree_Pattern nPProd p2;
            return (ps ++ qs)
          od
      | _ => fail (locs, «Impossible: nPOr»)
    else if nterm = INL nPAs then
      case args of
        [pat] => ptree_Pattern nPOr pat
      | [pat; ast; id] =>
          do
            expect_tok ast AsT;
            p <- ptree_Pattern nPOr pat;
            nm <- ptree_Ident id;
            return (MAP (λp. Pas p nm) p)
          od
      | _ => fail (locs, «Impossible: nPAs»)
    else if nterm = INL nPattern then
      case args of
        [pat] => ptree_Pattern nPAs pat
      | _ => fail (locs, «Impossible: nPattern»)
    else
      fail (locs, «Expected a pattern non-terminal»)) ∧
  (ptree_PatternList [] =
    fail (unknown_loc, «Pattern lists cannot be empty»)) ∧
  (ptree_PatternList [t] =
     do
       expect_tok t RbrackT;
       return []
     od) ∧
  (ptree_PatternList (p::ps) =
     do
       expect_tok p SemiT;
       ptree_PatternList ps
     od ++
     do
       q <- ptree_Pattern nPattern p;
       qs <- ptree_PatternList ps;
       return (q::qs)
     od) ∧
  (ptree_PatternCommas [] = return []) ∧
  (ptree_PatternCommas (p::ps) =
    do
      expect_tok p CommaT;
      ptree_PatternCommas ps
    od ++
    do
      q <- ptree_Pattern nPCons p;
      qs <- ptree_PatternCommas ps;
      return (q::qs)
    od)
Termination
  WF_REL_TAC ‘measure $ sum_size (pair_size camlNT_size psize)
                      $ sum_size (list_size psize)
                                 (SUC o list_size psize)’
  \\ simp [parsetree_size_lemma]
End

Definition ptree_Patterns_def:
  ptree_Patterns (Lf (_, locs)) =
    fail (locs, «Expected pattern list non-terminal») ∧
  ptree_Patterns (Nd (nterm, locs) args) =
    if nterm = INL nPatterns then
      case args of
        [pat] => fmap (λp. [p]) $ ptree_Pattern nPattern pat
      | [pat; rest] =>
          do
            p <- ptree_Pattern nPattern pat;
            ps <- ptree_Patterns rest;
            return (p::ps)
          od
      | _ => fail (locs, «Impossible: nPatterns»)
    else
      fail (locs, «Expected pattern list non-terminal»)
End

(* Builds a binary operation based on the output from “ptree_Op”.
 *)

Definition build_binop_def:
  build_binop symb x y = App Opapp [App Opapp [Var (Short symb); x]; y]
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
 *
 * TODO Can we replace this with build_letrec_binding?
 *)

Definition build_fun_lam_def:
  build_fun_lam body pats =
      FOLDR (λp b. case p of
                     Pvar x => Fun x b
                   | _ => Fun "" (Mat (Var (Short "")) [p, b]))
            body pats
End

(* This builds the body of a let rec expression out of a list of patterns
 * (a list instead of one, because of or-patterns) and an expression body.
 *
 * TODO
 * This is sort-of like build_fun_lam but accepts _lists_ of patterns at
 * each level. I think we should replace build_fun_lam with this thing.
 *)

Definition build_letrec_binding_def:
  build_letrec_binding bv pats body =
    FOLDR (λps b. Fun bv (Mat (Var (Short bv)) (MAP (λp. (p, b)) ps)))
      body pats
End

(* Builds a sequence of lets out of a list of let bindings.
 *)

Definition build_lets_def:
  build_lets binds body =
    FOLDR (λbind rest.
             case bind of
               INL (p,x) =>
                 Mat x [p, rest]
             | INR (f,_,x) =>
                 Let (SOME f) x rest)
          binds body
End

(* TODO
 * With these functions it's not possible to mix value definitions
 * and recursive function definitions.
 *
 * NOTE
 * I think this means that the parser won't accept
 *
 *   let rec f x = something
 *   and y = 5;;
 *
 * which is a bit annoying but it hardly matters.
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

Definition ptree_Bool_def:
  ptree_Bool (Lf (_, locs)) =
    fail (locs, «Expected a boolean literal non-terminal») ∧
  ptree_Bool (Nd (nterm, locs) args) =
    if nterm = INL nLiteral then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if tk = TrueT ∨ tk = FalseT then
              return (bool_to_exp (tk = TrueT))
            else
              fail (locs, «not a boolean literal»)
          od
      | _ => fail (locs, «Impossible: nLiteral (bool)»)
    else
      fail (locs, «Expected a boolean literal non-terminal»)
End

Definition ptree_Expr_def:
  (ptree_Expr et (Lf (_, locs)) =
    fail (locs, «Expected an expression non-terminal»)) ∧
  (ptree_Expr et (Nd (nterm, locs) args) =
    if INL et ≠ nterm then
      fail (locs, «ptree_Expr»)
    else if nterm = INL nExpr then
      case args of
        [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nESeq then
              ptree_Expr nESeq arg
            else if n = INL nELet then
              ptree_Expr nELet arg
            else if n = INL nELetRec then
              ptree_Expr nELetRec arg
            else if n = INL nEMatch then
              ptree_Expr nEMatch arg
            else if n = INL nEFun then
              ptree_Expr nEFun arg
            else if n = INL nEFunction then
              ptree_Expr nEFunction arg
            else if n = INL nETry then
              ptree_Expr nETry arg
            else if n = INL nEWhile then
              ptree_Expr nEWhile arg
            else if n = INL nEFor then
              ptree_Expr nEFor arg
            else
              fail (locs, «Expected an expression non-terminal»)
          od
      | _ => fail (locs, «Impossible: nExpr»)
    else if nterm = INL nEList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            exps <- ptree_ExprList rest;
            return (build_list_exp exps)
          od
      | _ => fail (locs, «Impossible: nEList»)
    else if nterm = INL nEBase then
      case args of
        [lpar;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            return (Con NONE [])
          od ++
          do
            expect_tok lpar BeginT;
            expect_tok rpar EndT;
            return (Con NONE [])
          od
      | [lpar;expr;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ptree_Expr nExpr expr
          od ++
          do
            expect_tok lpar BeginT;
            expect_tok rpar EndT;
            ptree_Expr nExpr expr
          od
      | [lpar;expr;colon;typ;rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            ty <- ptree_Type typ;
            x <- ptree_Expr nExpr expr;
            return (Tannot x ty)
          od
      | [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nLiteral then
              ptree_Bool arg ++
              fmap Lit (ptree_Literal arg)
            else if n = INL nValuePath then
              do
                cns <- ptree_ValuePath arg;
                ns <- path_to_ns locs cns;
                return (Var ns)
              od
            else if n = INL nConstr then
              do
                cns <- ptree_Constr arg;
                ns <- path_to_ns locs cns;
                return (Con (SOME ns) [])
              od
            else if n = INL nEList then
              ptree_Expr nEList arg
            else
              fail (locs, «Impossible: nEBase»)
          od
      | _ => fail (locs, «Impossible: nEBase»)
    else if nterm = INL nEAssert then
      case args of
        [assr; expr] =>
          do
            expect_tok assr AssertT;
            x <- ptree_Expr nEBase expr;
            return (App Opapp [Var (Short "assert"); x])
          od
      | _ => fail (locs, «Impossible: nEAssert»)
    else if nterm = INL nELazy then
      case args of
        [lazy; expr] =>
          do
            expect_tok lazy LazyT;
            x <- ptree_Expr nEBase expr;
            return (App Opapp [Var (Short "lazy"); x])
          od
      | _ => fail (locs, «Impossible: nELazy»)
    else if nterm = INL nEConstr then
      case args of
        [consid; expr] =>
          do
            cns <- ptree_Constr consid;
            id <- path_to_ns locs cns;
            x <- ptree_Expr nEBase expr;
            return (Con (SOME id) [x])
          od
      | _ => fail (locs, «Impossible: nEConstr»)
    else if nterm = INL nEFunapp then
      case args of
        [exp] => ptree_Expr nEBase exp
      | [fexp; aexp] =>
          do
            f <- ptree_Expr nEFunapp fexp;
            x <- ptree_Expr nEBase aexp;
            return (build_funapp f [x])
          od
      | _ => fail (locs, «Impossible: nEFunapp»)
    else if nterm = INL nEApp then
      case args of
        [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nELazy then
              ptree_Expr nELazy arg
            else if n = INL nEAssert then
              ptree_Expr nEAssert arg
            else if n = INL nEConstr then
              ptree_Expr nEConstr arg
            else if n = INL nEFunapp then
              ptree_Expr nEFunapp arg
            else if n = INL nEBase then
              ptree_Expr nEBase arg
            else
              fail (locs, «Impolssible: nEApp»)
          od
      | _ => fail (locs, «Impossible: nEApp»)
    else if nterm = INL nEPrefix then
      case args of
        [opn; expr] =>
          do
            op <- ptree_Op opn;
            x <- ptree_Expr nEApp expr;
            return (App Opapp [Var (Short op); x])
          od
      | [arg] => ptree_Expr nEApp arg
      | _ => fail (locs, «Impossible: nEPrefix»)
    else if nterm = INL nENeg then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- option $ destTOK lf;
            x <- ptree_Expr nEPrefix expr;
            if tk = MinusT then
              return (App Opapp [Var (Long "Int" (Short "~")); x])
            else if tk = MinusFT then
              return (App Opapp [Var (Long "Double" (Short "~")); x])
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return (App Opapp [Var (Short s); x])
            else
              fail (locs, «Impossible: nEPrefix»)
          od
      | [arg] => ptree_Expr nEPrefix arg
      | _ => fail (locs, «Impossible: nEPrefix»)
    else if nterm = INL nEShift then
      case args of
        [exp] => ptree_Expr nENeg exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nENeg lhs;
            y <- ptree_Expr nEShift rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEShift»)
    else if nterm = INL nEMult then
      case args of
        [exp] => ptree_Expr nEShift exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEMult lhs;
            y <- ptree_Expr nEShift rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nMult»)
    else if nterm = INL nEAdd then
      case args of
        [exp] => ptree_Expr nEMult exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEAdd lhs;
            y <- ptree_Expr nEMult rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEAdd»)
    else if nterm = INL nECons then
      case args of
        [exp] => ptree_Expr nEAdd exp
      | [lhs; colons; rhs] =>
          do
            expect_tok colons ColonsT;
            x <- ptree_Expr nEAdd lhs;
            y <- ptree_Expr nECons rhs;
            return (Con (SOME (Short "::")) [x; y])
          od
      | _ => fail (locs, «Impossible: nECons»)
    else if nterm = INL nECat then
      case args of
        [exp] => ptree_Expr nECons exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nECons lhs;
            y <- ptree_Expr nECat rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nECat»)
    else if nterm = INL nERel then
      case args of
        [exp] => ptree_Expr nECat exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nERel lhs;
            y <- ptree_Expr nECat rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nERel»)
    else if nterm = INL nEAnd then
      case args of
        [exp] => ptree_Expr nERel exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nERel lhs;
            y <- ptree_Expr nEAnd rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEAnd»)
    else if nterm = INL nEOr then
      case args of
        [exp] => ptree_Expr nEAnd exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEAnd lhs;
            y <- ptree_Expr nEOr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEOr»)
    else if nterm = INL nEHolInfix then
      case args of
        [exp] => ptree_Expr nEOr exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEHolInfix lhs;
            y <- ptree_Expr nEOr rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEHolInfix»)
    else if nterm = INL nEProd then
      case args of
        [exp] => ptree_Expr nEHolInfix exp
      | exp::exps =>
          do
            x <- ptree_Expr nEHolInfix exp;
            xs <- ptree_ExprCommas exps;
            return (Con NONE (x::xs))
          od
      | _ => fail (locs, «Impossible: nEProd»)
    else if nterm = INL nEAssign then
      case args of
        [exp] => ptree_Expr nEProd exp
      | [lhs; opn; rhs] =>
          do
            x <- ptree_Expr nEProd lhs;
            y <- ptree_Expr nEAssign rhs;
            op <- ptree_Op opn;
            return (build_binop op x y)
          od
      | _ => fail (locs, «Impossible: nEAssign»)
    else if nterm = INL nEIf then
      case args of
        [ift; x; thent; y; elset; z] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            expect_tok elset ElseT;
            x1 <- ptree_Expr nExpr x;
            y1 <- ptree_Expr nExpr y;
            z1 <- ptree_Expr nExpr z;
            return (If x1 y1 z1)
          od
      | [ift; x; thent; y] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            x1 <- ptree_Expr nExpr x;
            y1 <- ptree_Expr nExpr y;
            return (If x1 y1 (Con NONE []))
          od
      | [exp] => ptree_Expr nEAssign exp
      | _ => fail (locs, «Impossible: nEIf»)
    else if nterm = INL nESeq then
      case args of
        [x; semi; y] =>
          do
            expect_tok semi SemiT;
            x1 <- ptree_Expr nEIf x;
            y1 <- ptree_Expr nESeq y;
            return (Let NONE x1 y1)
          od
      | [x] => ptree_Expr nEIf x
      | _ => fail (locs,«Impossible: nESeq»)
    else if nterm = INL nELetRec then
      case args of
        [lett; rec; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok rec RecT;
            expect_tok int InT;
            binds <- ptree_LetRecBindings binds;
            body <- ptree_Expr nExpr expr;
            return (Letrec binds body)
          od
      | _ => fail (locs, «Impossible: nELetRec»)
    else if nterm = INL nELet then
      case args of
        [lett; binds; int; expr] =>
          do
            expect_tok lett LetT;
            expect_tok int InT;
            binds <- ptree_LetBindings binds;
            body <- ptree_Expr nExpr expr;
            return (build_lets body binds)
          od
      | _ => fail (locs, «Impossible: nELet»)
    else if nterm = INL nEMatch then
      case args of
        [match; expr; witht; pmatch] =>
          do
            expect_tok match MatchT;
            expect_tok witht WithT;
            x <- ptree_Expr nExpr expr;
            ps <- ptree_PatternMatch pmatch;
            return (build_match "" (flatten_pmatch ps) x)
          od
      | _ => fail (locs, «Impossible: nEMatch»)
    else if nterm = INL nEFun then
      case args of
        [funt; params; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr nExpr expr;
            return (Fun "" (Mat (Var (Short ""))
                           (MAP (λps. case ps of
                                        [] => (Pany, Var (Short ""))
                                      | p::ps =>
                                              (p, build_fun_lam x ps))
                                ps)))
          od
      | [funt; params; colon; typ; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr nExpr expr;
            ty <- ptree_Type typ;
            return (Tannot (Fun "" (Mat (Var (Short ""))
                                   (MAP (λps. case ps of
                                                      (* this never happens:*)
                                                [] => (Pany, Var (Short ""))
                                              | p::ps =>
                                                  (p, build_fun_lam x ps))
                                        ps))) ty)
          od
      | _ => fail (locs, «Impossible: nEFun»)
    else if nterm = INL nEFunction then
      case args of
        [funct; pmatch] =>
          do
            expect_tok funct FunctionT;
            ps <- ptree_PatternMatch pmatch;
            return (build_function "" (flatten_pmatch ps))
          od
      | _ => fail (locs, «Impossible: nEFunction»)
    else if nterm = INL nETry then
      case args of
        [tryt; expr; witht; pmatch] =>
          do
            expect_tok tryt TryT;
            expect_tok witht WithT;
            x <- ptree_Expr nExpr expr;
            ps <- ptree_PatternMatch pmatch;
            return (build_handle "" (flatten_pmatch ps) x)
          od
      | _ => fail (locs, «Impossible: nETry»)
    else if nterm = INL nEWhile then
      case args of
        [while; expr; dot; body; donet] =>
          do
            expect_tok while WhileT;
            expect_tok dot DoT;
            expect_tok donet DoneT;
            x <- ptree_Expr nExpr expr;
            b <- ptree_Expr nExpr body;
            return (build_funapp (Var (Short "while")) [x; b])
          od
      | _ => fail (locs, «Impossible: nEWhile»)
    else if nterm = INL nEFor then
      case args of
        [for; ident; eq; ubd; updown; lbd; dot; body; donet] =>
          do
            expect_tok for ForT;
            expect_tok eq EqualT;
            expect_tok dot DoT;
            lf <- destLf updown;
            tk <- option $ destTOK lf;
            (if tk = ToT ∨ tk = DowntoT then return () else
              fail (locs, «Expected 'to' or 'downto'»));
            id <- ptree_ValueName ident;
            u <- ptree_Expr nExpr ubd;
            l <- ptree_Expr nExpr lbd;
            b <- ptree_Expr nExpr body;
            return (build_funapp (Var (Short "for"))
                                 [bool_to_exp (tk = ToT);
                                  Var (Short id); u; l; b])
          od
      | _ => fail (locs, «Impossible: nEFor»)
    else
      fail (locs, «ptree_Expr»)) ∧
  (ptree_LetRecBinding (Lf (_, locs)) =
    fail (locs, «Expected a let rec binding non-terminal»)) ∧
  (ptree_LetRecBinding (Nd (nterm, locs) args) =
    if nterm = INL nLetRecBinding then
      case args of
        [id; pats; colon; type; eq; expr] =>
          do
            expect_tok colon ColonT;
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            ty <- ptree_Type type;
            bd <- ptree_Expr nExpr expr;
            return (nm, "", build_letrec_binding "" ps (Tannot bd ty))
          od
      | [id; pats; eq; expr] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            bd <- ptree_Expr nExpr expr;
            return (nm, "", build_letrec_binding "" ps bd)
          od
      | _ => fail (locs, «Impossible: nLetRecBinding»)
    else
      fail (locs, «Expected a let rec binding non-terminal»)) ∧
  (ptree_LetRecBindings (Lf (_, locs)) =
      fail (locs, «Expected a list of let rec bindings non-terminal»)) ∧
  (ptree_LetRecBindings (Nd (nterm, locs) args) =
    if nterm = INL nLetRecBindings then
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
      | _ => fail (locs, «Impossible: nLetRecBindings»)
    else
      fail (locs, «Expected a list of let rec bindings non-terminal»)) ∧
  (ptree_LetBinding (Lf (_, locs)) =
    fail (locs, «Expected a let binding non-terminal»)) ∧
  (ptree_LetBinding (Nd (nterm, locs) args) =
    if nterm = INL nLetBinding then
      case args of
        [pat; eq; bod] =>
          do
            expect_tok eq EqualT;
            ps <- ptree_Pattern nPattern pat;
            bd <- ptree_Expr nExpr bod;
            case ps of
              [p] => return (INL (p, bd))
            | _ =>
              fail (locs, concat [
                            «Or-patterns are not allowed in let bindings»;
                            « like this one: 'let' <pattern> '=' <expr';;»])
          od
      | [id; pats; eq; bod] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            bd <- ptree_Expr nExpr bod;
            return $ INR (nm, "", build_letrec_binding "" ps bd)
          od
      | [id; pats; colon; type; eq; bod] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            ty <- ptree_Type type;
            bd <- ptree_Expr nExpr bod;
            return $ INR (nm, "", build_letrec_binding "" ps (Tannot bd ty))
          od
      | _ => fail (locs, «Impossible: nLetBinding»)
    else
      fail (locs, «Expected a let binding non-terminal»)) ∧
  (ptree_LetBindings (Lf (_, locs)) =
     fail (locs, «Expected a list of let bindings non-terminal»)) ∧
  (ptree_LetBindings (Nd (nterm, locs) args) =
    if nterm = INL nLetBindings then
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
      | _ => fail (locs, «Impossible: nLetBindings»)
    else
      fail (locs, «Expected a list of let bindings non-terminal»)) ∧
  (ptree_PatternMatches (Lf (_, locs)) =
    fail (locs, «Expected a pattern-matches non-terminal»)) ∧
  (ptree_PatternMatches (Nd (nterm, locs) args) =
    if nterm = INL nPatternMatches then
      case args of
        (* urk: these cases overlap *)
        [a; b; c; d; e] =>
          let pat = a; whent = b; whenx = c; rarrow = d; body = e in
            do
              expect_tok rarrow RarrowT;
              expect_tok whent WhenT;
              p <- ptree_Pattern nPattern pat;
              x <- ptree_Expr nExpr body;
              w <- ptree_Expr nExpr whenx;
              return [p, x, SOME w]
            od ++
          let pat = a; rarrow = b; body = c; bar = d; pms = e in
            do
              expect_tok rarrow RarrowT;
              expect_tok bar BarT;
              p <- ptree_Pattern nPattern pat;
              x <- ptree_Expr nExpr body;
              ps <- ptree_PatternMatches pms;
              return ((p, x, NONE)::ps)
            od
      | [pat; whent; whenx; rarrow; body; bar; pms] =>
          do
            expect_tok rarrow RarrowT;
            expect_tok whent WhenT;
            p <- ptree_Pattern nPattern pat;
            x <- ptree_Expr nExpr body;
            w <- ptree_Expr nExpr whenx;
            expect_tok bar BarT;
            ps <- ptree_PatternMatches pms;
            return ((p, x, SOME w)::ps)
          od
      | [pat; rarrow; body] =>
          do
            expect_tok rarrow RarrowT;
            p <- ptree_Pattern nPattern pat;
            x <- ptree_Expr nExpr body;
            return [p, x, NONE]
          od
      | _ => fail (locs, «Impossible: nPatternMatches»)
    else
      fail (locs, «Expected a pattern-matches non-terminal»)) ∧
  (ptree_PatternMatch (Lf (_, locs)) =
    fail (locs, «Expected a pattern-match non-terminal»)) ∧
  (ptree_PatternMatch (Nd (nterm, locs) args) =
    if nterm = INL nPatternMatch then
      case args of
        [bar; pms] =>
          do
            expect_tok bar BarT;
            ptree_PatternMatches pms
          od
      | [pms] => ptree_PatternMatches pms
      | _ => fail (locs, «Impossible: nPatternMatch»)
    else
      fail (locs, «Expected a pattern-match non-terminal»)) ∧
  (ptree_ExprList [] =
    fail (unknown_loc, «Expression lists cannot be empty»)) ∧
  (ptree_ExprList [t] =
     do
       expect_tok t RbrackT;
       return []
     od) ∧
  (ptree_ExprList (x::xs) =
     do
       expect_tok x SemiT;
       ptree_ExprList xs
     od ++
     do
       y <- ptree_Expr nEIf x;
       ys <- ptree_ExprList xs;
       return (y::ys)
     od) ∧
  (ptree_ExprCommas [] = return []) ∧
  (ptree_ExprCommas (x::xs) =
    do
      expect_tok x CommaT;
      ptree_ExprCommas xs
    od ++
    do
      y <- ptree_Expr nEHolInfix x;
      ys <- ptree_ExprCommas xs;
      return (y::ys)
    od)
Termination
  WF_REL_TAC ‘measure $ sum_size (pair_size camlNT_size psize)
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size (SUC o list_size psize) (SUC o list_size psize)’
  \\ simp [parsetree_size_lemma]
End

(* Tidy up the list bits of the induction theorem.
 *)

Theorem ptree_Expr_ind = ptree_Expr_ind |> SIMP_RULE (srw_ss() ++ CONJ_ss) [];

Definition ptree_ConstrArgs_def:
  ptree_ConstrArgs (Lf (_, locs)) =
    fail (locs, «Expected a constructor arguments non-terminal») ∧
  ptree_ConstrArgs (Nd (nterm, locs) args) =
    if nterm = INL nConstrArgs then
      case args of
        ty::rest =>
          do
            t <- ptree_Type ty;
            ts <- ptree_StarTypes rest;
            return (t::ts)
          od
      | _ => fail (locs, «Impossible: nConstrArgs»)
    else
      fail (locs, «Expected a constructor arguments non-terminal»)
End

Definition ptree_ConstrDecl_def:
  ptree_ConstrDecl (Lf (_, locs)) =
    fail (locs, «Expected a constructor declaration non-terminal») ∧
  ptree_ConstrDecl (Nd (nterm, locs) args) =
    if nterm = INL nConstrDecl then
      case args of
        [name] =>
          fmap (λnm. (nm,[])) $ ptree_ConstrName name
      | [name; oft; args] =>
          do
            expect_tok oft OfT;
            nm <- ptree_ConstrName name;
            ts <- ptree_ConstrArgs args;
            return (nm, ts)
          od
      | _ => fail (locs, «Impossible: nConstrDecl»)
    else
      fail (locs, «Expected a constructor declaration non-terminal»)
End

Definition ptree_ExcType_def:
  ptree_ExcType (Lf (_, locs)) =
    fail (locs, «Expected an exception type declaration non-terminal») ∧
  ptree_ExcType (Nd (nterm, locs) args) =
    if nterm = INL nExcType then
      case args of
        [exnt; cdecl] =>
          do
            expect_tok exnt ExceptionT;
            (nm, args) <- ptree_ConstrDecl cdecl;
            return () (* No types in the CakeML ast *)
          od
      | _ =>
          fail (locs, «Impossible: nExcType»)
    else
      fail (locs, «Expected an exception type declaration non-terminal»)
End

Definition ptree_ExcDefinition_def:
  ptree_ExcDefinition (Lf (_, locs)) =
    fail (locs, «Expected an exception definition non-terminal») ∧
  ptree_ExcDefinition (Nd (nterm, locs) args) =
    if nterm = INL nExcDefinition then
      case args of
        [exnt; cdecl] =>
          do
            expect_tok exnt ExceptionT;
            (nm, args) <- ptree_ConstrDecl cdecl;
            return (Dexn locs nm args)
          od
      | [exnt; lhsid; eq; rhsid] =>
          do
            expect_tok exnt ExceptionT;
            expect_tok eq EqualT;
            lhs <- ptree_ConstrName lhsid;
            cns <- ptree_Constr rhsid;
            rhs <- path_to_ns locs cns;
            return (Dexn locs lhs [Atapp [] rhs])
          od
      | _ => fail (locs, «Impossible: nExcDefinition»)
    else
      fail (locs, «Expected an exception definition non-terminal»)
End

(* ptree_TypeRepr picks out constructor declarations and returns
 * a list of (constructor_name # argument_types) pairs, one for
 * each constructor.
 *)

Definition ptree_TypeRepr_def:
  ptree_TypeRepr (Lf (_, locs)) =
    fail (locs, «Expected a type-repr non-terminal») ∧
  ptree_TypeRepr (Nd (nterm, locs) args) =
    if nterm = INL nTypeRepr then
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
      | _ => fail (locs, «Impossible: nTypeRepr»)
    else if nterm = INL nTypeReprs then
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
      | _ => fail (locs, «Impossible: nTypeReprs»)
    else
      fail (locs, «Expected a type-repr non-terminal»)
End

Definition ptree_TypeInfo_def:
  ptree_TypeInfo (Lf (_, locs)) =
    fail (locs, «Expected a type-info non-terminal») ∧
  ptree_TypeInfo (Nd (nterm, locs) args) =
    if nterm = INL nTypeInfo then
      case args of
        [eq; arg] =>
          do
            expect_tok eq EqualT;
            n <- nterm_of arg;
            if n = INL nType then
              fmap INL (ptree_Type arg)
            else if n = INL nTypeRepr then
              fmap INR (ptree_TypeRepr arg)
            else
              fail (locs, «Impossible: nTypeInfo»)
          od
      | _ => fail (locs, «Impossible: nTypeInfo»)
    else
      fail (locs, «Expected a type-info non-terminal»)
End

Definition ptree_TypeName_def:
  ptree_TypeName (Lf (_, locs)) =
    fail (locs, «Expected type variable non-terminal») ∧
  ptree_TypeName (Nd (nterm, locs) args) =
    if nterm = INL nTVar then
      case args of
        [tick; id] =>
          do
            expect_tok tick TickT;
            ptree_Ident id
          od
      | _ => fail (locs, «Impossible: nTVar»)
    else
      fail (locs, «Expected type variable non-terminal»)
End

Definition ptree_TypeParamList_def:
  ptree_TypeParamList [] =
    fail (unknown_loc, «Empty type parameters are not supported») ∧
  ptree_TypeParamList [t] =
    do
      expect_tok t RparT;
      return []
    od ∧
  ptree_TypeParamList (p::ps) =
    do
      expect_tok p CommaT;
      ptree_TypeParamList ps
    od ++
    do
      t <- ptree_TypeName p;
      ts <- ptree_TypeParamList ps;
      return (t::ts)
    od
End

Definition ptree_TypeParams_def:
  ptree_TypeParams (Lf (_, locs)) =
    fail (locs, «Expected a type-parameters non-terminal») ∧
  ptree_TypeParams (Nd (nterm, locs) args) =
    if nterm = INL nTypeParams then
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
      | _ => fail (locs, «Impossible: nTypeParams»)
    else
      fail (locs, «Expected a type-parameters non-terminal»)
End

Definition ptree_TypeDef_def:
  ptree_TypeDef (Lf (_, locs)) =
    fail (locs, «Expected a typedef non-terminal») ∧
  ptree_TypeDef (Nd (nterm, locs) args) =
    if nterm = INL nTypeDef then
      case args of
        [tps; id; info] =>
          do
            tys <- ptree_TypeParams tps;
            nm <- ptree_TypeConstrName id;
            trs <- ptree_TypeInfo info;
            return (locs, tys, nm, trs)
          od
      | [id; info] =>
          do
            nm <- ptree_TypeConstrName id;
            trs <- ptree_TypeInfo info;
            return (locs, [], nm, trs)
          od
      | _ => fail (locs, «Impossible: nTypeDef»)
    else
      fail (locs, «Expected a typedef non-terminal»)
End

Definition ptree_TypeDefs_def:
  ptree_TypeDefs (Lf (_, locs)) =
    fail (locs, «Expected a typedef:s non-terminal») ∧
  ptree_TypeDefs (Nd (nterm, locs) args) =
    if nterm = INL nTypeDefs then
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
      | _ => fail (locs, «Impossible: nTypeDefs»)
    else
      fail (locs, «Expected a typedef:s non-terminal»)
End

(* Ocaml datatype definitions and type abbreviations can be made mutually
 * recursive with each other and this is not supported in CakeML. Example:
 *   type foo = A of bar | B of baz | ...
 *   and baz = foo list
 *)

Definition ptree_TypeDefinition_def:
  ptree_TypeDefinition (Lf (_, locs)) =
    fail (locs, «Expected a type definition non-terminal») ∧
  ptree_TypeDefinition (Nd (nterm, locs) args) =
    if nterm = INL nTypeDefinition then
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
              return $ [Dtype locs (MAP (λ(_,tys,nm,trs). (tys,nm,OUTR trs))
                                        tdefs)]
            else
              fail (locs, concat [
                    «Type abbreviations and datatype definitions cannot be»;
                    « mutually recursive in CakeML»])
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
              Dtype locs (MAP (λ(_,tys,nm,trs). (tys,nm,OUTR trs)) datas);
            return (datas::abbrevs)
          od
      | _ => fail (locs, «Impossible: nTypeDefinition»)
    else
      fail (locs, «Expected a type definition non-terminal»)
End

(* Builds a top-level let out of a list of let bindings.
 *)

Definition build_dlet_def:
  build_dlet locs binds =
    MAP (λbind.
           case bind of
             INL (p, x) => Dlet locs p x
           | INR (f,_,x) => Dlet locs (Pvar f) x)
        binds
End

Definition ptree_Semis_def:
  ptree_Semis (Lf (_, locs)) =
    fail (locs, «Expected a semicolons-list non-terminal») ∧
  ptree_Semis (Nd (nterm, locs) args) =
    if nterm = INL nSemis then
      case args of
        [s] => expect_tok s SemisT
      | [s; r] =>
          do
            expect_tok s SemisT;
            ptree_Semis r
          od
      | _ => fail (locs, «Impossible: nSemis»)
    else
      fail (locs, «Expected a semicolons-list non-terminal»)
End

(* Turns "expr;;" into "let it = expr;;". (The results of evaluating the
 * expression must end up somewhere and its strange to put in a variable with
 * no name.
 *)

Definition ptree_ExprDec_def:
  ptree_ExprDec locs pt =
    fmap (λx. [Dlet locs (Pvar "it") x])
         (ptree_Expr nExpr pt)
End

Definition ptree_ValType_def:
  ptree_ValType (Lf (_, locs)) =
    fail (locs, «Expected a val-type declaration non-terminal») ∧
  ptree_ValType (Nd (nterm, locs) args) =
    if nterm = INL nValType then
      case args of
        [valt; valn; colont; typ] =>
          do
            expect_tok valt ValT;
            expect_tok colont ColonT;
            nm <- ptree_ValueName valn;
            ty <- ptree_Type typ;
            return ()
          od
      | _ => fail (locs, «Impossible: nValType»)
    else
      fail (locs, «Expected a val-type declaration non-terminal»)
End

Definition ptree_OpenMod_def:
  ptree_OpenMod (Lf (_, locs)) =
    fail (locs, «Expected a module-open non-terminal») ∧
  ptree_OpenMod (Nd (nterm, locs) args) =
    if nterm = INL nOpenMod then
      case args of
        [opent; modpath] =>
          do
            expect_tok opent OpenT;
            ps <- ptree_ModulePath modpath;
            return ()
          od
      | _ => fail (locs, «Impossible: nOpenMod»)
    else
      fail (locs, «Expected a module-open non-terminal»)
End

Definition ptree_IncludeMod_def:
  ptree_IncludeMod (Lf (_, locs)) =
    fail (locs, «Expected a module-open non-terminal») ∧
  ptree_IncludeMod (Nd (nterm, locs) args) =
    if nterm = INL nIncludeMod then
      case args of
        [opent; modpath] =>
          do
            expect_tok opent IncludeT;
            ps <- ptree_ModulePath modpath;
            return ()
          od
      | _ => fail (locs, «Impossible: nIncludeMod»)
    else
      fail (locs, «Expected a module-open non-terminal»)
End

(* This is currently a no-op since there are no module types. It will report
   an error if someone uses something like a functor or anything like that,
   though.
 *)
Definition ptree_ModuleType_def:
  (ptree_ModuleType (Lf (_, locs)) =
    fail (locs, «Expected a module-type declaration non-terminal»)) ∧
  (ptree_ModuleType (Nd (nterm, locs) args) =
    if nterm = INL nModuleType then
      case args of
        [arg] =>
          do
            nt <- nterm_of arg;
            if nt = INL nModTypePath then
              do
                ptree_ModTypePath arg;
                return ()
              od
            else if nt = INL nSigSpec then
              do
                ptree_SigSpec arg;
                return ()
              od
            else
              fail (locs, «Impossible: nModuleType»)
          od
      | [lpar; modtype; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            ty <- ptree_ModuleType modtype;
            return ()
          od
      | _ => fail (locs, «Impossible: nModuleType»)
    else
      fail (locs, «Expected a module-type declaration non-terminal»)) ∧
  (ptree_SigSpec (Lf (_, locs)) =
    fail (locs, «Expected a signature spec non-terminal»)) ∧
  (ptree_SigSpec (Nd (nterm, locs) args) =
    if nterm = INL nSigSpec then
      case args of
        [sigt; sigits; endt] =>
          do
            expect_tok sigt SigT;
            expect_tok endt EndT;
            ptree_SigItems sigits;
            return ()
          od
      | [sigt; endt] =>
          do
            expect_tok sigt SigT;
            expect_tok endt EndT;
            return ()
          od
      | _ => fail (locs, «Impossible: nSigSpec»)
    else
      fail (locs, «Expected a signature spec non-terminal»)) ∧
  (ptree_SigItems (Lf (_, locs)) =
    fail (locs, «Expected a signature item list non-terminal»)) ∧
  (ptree_SigItems (Nd (nterm, locs) args) =
    if nterm = INL nSigItems then
      case args of
        [sigit; semis; sigits] =>
          do
            ptree_Semis semis;
            x <- ptree_SigItem sigit;
            xs <- ptree_SigItems sigits;
            return (x::xs)
          od
      | [sigit; rest] =>
          do
            ptree_Semis rest;
            x <- ptree_SigItem sigit;
            return [x]
          od ++
          do
            x <- ptree_SigItem sigit;
            xs <- ptree_SigItems rest;
            return (x::xs)
          od
      | [sigit] =>
          do
            ptree_Semis sigit;
            return []
          od ++
          do
            x <- ptree_SigItem sigit;
            return [x]
          od
      | _ => fail (locs, «Impossible: nSigItems»)
    else
      fail (locs, «Expected a signature item list non-terminal»)) ∧
  (ptree_SigItem (Lf (_, locs)) =
    fail (locs, «Expected a signature item non-terminal»)) ∧
  (ptree_SigItem (Nd (nterm, locs) args) =
    if nterm = INL nSigItem then
      case args of
        [arg] =>
          do
            nt <- nterm_of arg;
            if nt = INL nTypeDefinition then
              do
                ptree_TypeDefinition arg;
                return ()
              od
            else if nt = INL nExcType then
              do
                ptree_ExcType arg;
                return ()
              od
            else if nt = INL nValType then
              do
                ptree_ValType arg;
                return ()
              od
            else if nt = INL nModTypeAsc then
              do
                ptree_ModTypeAsc arg;
                return ()
              od
            else if nt = INL nModTypeAssign then
              do
                ptree_ModTypeAssign arg;
                return ()
              od
            else if nt = INL nOpenMod then
              do
                ptree_OpenMod arg;
                return ()
              od
            else if nt = INL nIncludeMod then
              do
                ptree_IncludeMod arg;
                return ()
              od
            else
              fail (locs, «Impossible: nSigItem»)
          od
      | _ => fail (locs, «Impossible: nSigItem»)
    else
      fail (locs, «Expected a signature item non-terminal»)) ∧
  (ptree_ModTypeAssign (Lf (_, locs)) =
    fail (locs, «Expected a signature assignment non-terminal»)) ∧
  (ptree_ModTypeAssign (Nd (nterm, locs) args) =
    if nterm = INL nModTypeAssign then
      case args of
        [modt; typet; name] =>
          do
            expect_tok modt ModuleT;
            expect_tok typet TypeT;
            nm <- ptree_ModTypeName name;
            return ()
          od
      | [modt; typet; name; eqt; typ] =>
          do
            expect_tok modt ModuleT;
            expect_tok typet TypeT;
            expect_tok eqt EqualT;
            nm <- ptree_ModTypeName name;
            ty <- ptree_ModuleType typ;
            return ()
          od
      | _ => fail (locs, «Impossible: nModTypeAssign»)
    else
      fail (locs, «Expected a signature assignment non-terminal»)) ∧
  (ptree_ModTypeAsc (Lf (_, locs)) =
    fail (locs, «Expected a signature ascription non-terminal»)) ∧
  (ptree_ModTypeAsc (Nd (nterm, locs) args) =
    if nterm = INL nModTypeAsc then
      case args of
        [modt; typet; modname; apps; colont; typ] =>
          fail (locs, concat [«Functor syntax is not supported»;
                              « (you attempted to apply a functor type)»])
      | [modt; typet; modname; colont; typ] =>
          do
            expect_tok modt ModuleT;
            expect_tok typet TypeT;
            expect_tok colont ColonT;
            nm <- ptree_ModuleName modname;
            ty <- ptree_ModuleType typ;
            return ()
          od
      | _ => fail (locs, «Impossible: nModTypeAsc»)
    else
      fail (locs, «Expected a module ascription non-terminal»))
  (* This is for converting functor syntax if someone ever gets around to
     implementing that: *)
  (* ∧
  (ptree_ModAscApps (Lf (_, locs)) =
    fail (locs, «Expected a moduletype-ascription list non-terminal»)) ∧
  (ptree_ModAscApps (Nd (nterm, locs) args) =
    if nterm = INL nModAscApps then
      case args of
        [arg] => fmap (λx. [x]) $ ptree_ModAscApp arg
      | [arg; rest] =>
          do
            x <- ptree_ModAscApp arg;
            xs <- ptree_ModAscApps rest;
            return (x::xs)
          od
      | _ => fail (locs, «Impossible: nModAscApps»)
    else
      fail (locs, «Expected a moduletype-ascription list non-terminal»)) ∧
  (ptree_ModAscApp (Lf (_, locs)) =
    fail (locs, «Expected a moduletype-ascription non-terminal»)) ∧
  (ptree_ModAscApp (Nd (nterm, locs) args) =
    if nterm = INL nModAscApp then
      case args of
        [lpar; modname; colont; typ; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok colont ColonT;
            expect_tok rpar RparT;
            nm <- ptree_ModuleName modname;
            ty <- ptree_ModuleType ty;
            return ()
          od
      | _ => fail (locs, «Impossible: nModAscApp»)
    else
      fail (locs, «Expected a moduletype-ascription non-terminal»)) *)
End

Definition ptree_Definition_def:
  (ptree_Definition (Lf (_, locs)) =
    fail (locs, «Expected a top-level definition non-terminal»)) ∧
  (ptree_Definition (Nd (nterm, locs) args) =
    if nterm = INL nDefinition then
      case args of
        [arg] => ptree_Definition arg
      | _ => fail (locs, «Impossible: nDefinition»)
    else if nterm = INL nTopLet then
      case args of
        [lett; lbs] =>
          do
            expect_tok lett LetT;
            binds <- ptree_LetBindings lbs;
            return (build_dlet locs binds)
          od
      | _ => fail (locs, «Impossible: nTopLet»)
    else if nterm = INL nTopLetRec then
      case args of
        [lett; rect; lbs] =>
          do
            expect_tok lett LetT;
            expect_tok rect RecT;
            binds <- ptree_LetRecBindings lbs;
            return [Dletrec locs binds]
          od
      | _ => fail (locs, «Impossible: nTopLetRec»)
    else if nterm = INL nTypeDefinition then
      ptree_TypeDefinition (Nd (nterm, locs) args)
    else if nterm = INL nExcDefinition then
      fmap (λd. [d]) $ ptree_ExcDefinition (Nd (nterm, locs) args)
    else if nterm = INL nOpen then
      fail (locs, «open-declarations are not supported (yet)»)
    else if nterm = INL nModuleTypeDef then
      case args of
        [modt; typet; name; eqt; typ] =>
          do
            expect_tok modt ModuleT;
            expect_tok typet TypeT;
            expect_tok eqt EqualT;
            nm <- ptree_ModTypeName name;
            ty <- ptree_ModuleType typ;
            return []
          od
      | _ => fail (locs, «Impossible: nModuleTypeDef»)
    else if nterm = INL nModuleDef then
      case args of
        [modt; modid; eq; mexpr] =>
          do
            expect_tok modt ModuleT;
            expect_tok eq EqualT;
            nm <- ptree_ModuleName modid;
            mx <- ptree_ModExpr mexpr;
            case mx of
              INL name =>
                fail (locs, «Structure assignment is not supported (yet?)»)
            | INR decs =>
                return [Dmod nm decs]
          od
      | _ => fail (locs, «Impossible: nModuleDef»)
    else
      fail (locs, «Expected a top-level definition non-terminal»)) ∧
  (ptree_ModExpr (Lf (_, locs)) =
    fail (locs, «Expected a module expression non-terminal»)) ∧
  (ptree_ModExpr (Nd (nterm, locs) args) =
    if nterm = INL nModExpr then
      case args of
        [path] => fmap INL $ ptree_ModulePath path
      | [struct; its; endt] =>
          do
            expect_tok struct StructT;
            expect_tok endt EndT;
            is <- ptree_ModuleItems its;
            return (INR is)
          od
      | _ => fail (locs, «Impossible: nModExpr»)
    else
      fail (locs, «Expected a module expression non-terminal»)) ∧
  (ptree_ModuleItems (Lf (_, locs)) =
    fail (locs, «Expected a module item list non-terminal»)) ∧
  (ptree_ModuleItems (Nd (nterm, locs) args) =
    if nterm = INL nModuleItems then
      case args of
        [eord] => ptree_ExprOrDefn eord
      | [eord; mit] =>
          do
            d <- ptree_ExprOrDefn eord;
            do
              ds <- ptree_ModuleItem mit;
              return (d ++ ds)
            od ++
            do
              ptree_Semis mit;
              return d
            od
          od
      | [eord; mit; semis] =>
          do
            d <- ptree_ExprOrDefn eord;
            ds <- ptree_ModuleItem mit;
            ptree_Semis semis;
            return (d ++ ds)
          od
      | _ => fail (locs, «Impossible: nModuleItems»)
    else
      fail (locs, «Expected a module item list non-terminal»)) ∧
  (ptree_ModuleItem (Lf (_, locs)) =
    fail (locs, «Expected a module item non-terminal»)) ∧
  (ptree_ModuleItem (Nd (nterm, locs) args) =
    if nterm = INL nModuleItem then
      case args of
        [eord] => ptree_ExprOrDefn eord
      | [eord; mit] =>
          do
            d <- ptree_ExprOrDefn eord;
            ds <- ptree_ModuleItem mit;
            return (d ++ ds)
          od
      | _ => fail (locs, «Impossible: nModuleItem»)
    else
      fail (locs, «Expected a module item non-terminal»)) ∧
  (ptree_ExprOrDefn (Lf (_, locs)) =
    fail (locs, «Expected a top-level expression/definition non-terminal»)) ∧
  (ptree_ExprOrDefn (Nd (nterm, locs) args) =
    if nterm = INL nExprItems then
      case args of
        [expr] => ptree_ExprDec locs expr
      | [semis; expr] =>
          do
            ptree_Semis semis;
            ptree_ExprDec locs expr
          od
      | _ => fail (locs, «Impossible: nExprItems»)
    else if nterm = INL nExprItem then
      case args of
      | [semis; expr] =>
          do
            ptree_Semis semis;
            ptree_ExprDec locs expr
          od
      | _ => fail (locs, «Impossible: nExprItem»)
    else if nterm = INL nDefItem then
      case args of
        [defn] => ptree_Definition defn
      | [semis; defn] =>
          do
            ptree_Semis semis;
            ptree_Definition defn
          od
      | _ => fail (locs, «Impossible: nExprItem»)
    else
      fail (locs, «Expected a top-level expression/definition non-terminal»))
End

Definition ptree_Start_def:
  ptree_Start (Lf (_, locs)) =
    fail (locs, «Expected the start non-terminal») ∧
  ptree_Start (Nd (nterm, locs) args) =
    if nterm = INL nStart then
      case args of
        [] => return []
      | [modits] => ptree_ModuleItems modits
      | _ => fail (locs, «Impossible: nStart»)
    else
      fail (locs, «Expected the start non-terminal»)
End

val _ = export_theory ();

