(*
  A theory for converting OCaml parse trees to abstract syntax.
 *)
Theory camlPtreeConversion
Libs
  preamble
Ancestors
  misc[qualified] mllist pegexec[qualified] caml_lex camlPEG ast
  precparser sum[qualified] cmlParse[qualified]
  lexer_impl[qualified]

val _ =
  temp_bring_to_front_overload "destResult" {Name="destResult", Thy="pegexec"};

val _ = patternMatchesSyntax.temp_enable_pmatch();

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

(* Builds the n-ary cartesian product of n lists (of any lengths).
 *)

Definition list_cart_prod_def:
  list_cart_prod [] = [[]] ∧
  list_cart_prod (xs::xss) =
    FLAT (MAP (λx. MAP (λy. x::y) (list_cart_prod xss)) xs)
End

(* -------------------------------------------------------------------------
 * Compatibility layer
 * ------------------------------------------------------------------------- *)

(* Resolving precedences and lifting or-patterns to the top at the same time
 * is just too annoying. Until the CakeML syntax supports the latter, we can
 * use this pre-pattern type.
 *
 * Pp_prod and Pp_as correspond to Pp_con NONE and Pp_alias, and are used to
 * trick the precparser into producing n-ary tuples and suffixes (i.e. the
 * as-patterns).
 *)

Datatype:
  ppat = Pp_any
       | Pp_var varN
       | Pp_lit lit
       | Pp_con ((modN, conN) id option) (ppat list)
       | Pp_record ((modN, conN) id) (varN list)
       | Pp_prod (ppat list)
       | Pp_or ppat ppat
       | Pp_tannot ppat ast_t
       | Pp_alias ppat (varN list)
       | Pp_as ppat varN
End

Definition ppat_size'_def:
  ppat_size' Pp_any = 0 ∧
  ppat_size' (Pp_var a) = 1 ∧
  ppat_size' (Pp_lit a) = 1 ∧
  ppat_size' (Pp_con x xs) = (1 + list_size ppat_size' xs) ∧
  ppat_size' (Pp_record x xs) = (1 + list_size mlstring_size xs) ∧
  ppat_size' (Pp_prod xs) = (1 + list_size ppat_size' xs) ∧
  ppat_size' (Pp_or x y) = (1 + ppat_size' x + ppat_size' y) ∧
  ppat_size' (Pp_tannot x y) = (1 + ppat_size' x) ∧
  ppat_size' (Pp_alias x y) = (1 + ppat_size' x) ∧
  ppat_size' (Pp_as x y) = (1 + ppat_size' x)
Termination
  WF_REL_TAC ‘measure ppat_size’
End

(* Convert ppat patterns to CakeML patterns by distributing or-patterns at the
 * top-level (returning a list of patterns).
 *
 * Record patterns don't fit this very well, as there is no syntax for them. To
 * make things simple, we only allow them at the top-level, and this function
 * will bail out if it finds one.
 *)

Definition ppat_to_pat_def:
  ppat_to_pat Pp_any =
    return [Pany] ∧
  ppat_to_pat (Pp_var v) =
    return [Pvar v] ∧
  ppat_to_pat (Pp_lit l) =
    return [Plit l] ∧
  ppat_to_pat (Pp_tannot pp t) =
    fmap (MAP (λp. Ptannot p t)) (ppat_to_pat pp) ∧
  ppat_to_pat (Pp_con id pps) =
    do
      qs <- ppat_to_pats pps;
      return (MAP (λps. Pcon id ps) (list_cart_prod qs))
    od ∧
  ppat_to_pat (Pp_record id fs) =
    fail (unknown_loc, «») ∧
  ppat_to_pat (Pp_prod pps) =
    do
      qs <- (ppat_to_pats pps);
      return (MAP (λps. Pcon NONE ps) (list_cart_prod qs))
    od ∧
  ppat_to_pat (Pp_alias pp ns) =
    fmap (MAP (λp. FOLDL Pas p ns)) (ppat_to_pat pp) ∧
  ppat_to_pat (Pp_as pp n) =
    fmap (MAP (λp. Pas p n)) (ppat_to_pat pp) ∧
  ppat_to_pat (Pp_or p1 p2) =
    do
      ps1 <- ppat_to_pat p1;
      ps2 <- ppat_to_pat p2;
      return (ps1 ++ ps2)
    od ∧
  ppat_to_pats [] = return [] ∧
  ppat_to_pats (p::ps) =
    do
      p1 <- ppat_to_pat p;
      ps1 <- ppat_to_pats ps;
      return (p1::ps1)
    od
Termination
  WF_REL_TAC ‘measure sum_size ppat_size (list_size ppat_size)’
End

(* Fix some constructor applications that needs to be in CakeML's curried
 * style. These are things from basis and Candle; all new constructors will
 * get tupled arguments.
 *)

Definition compatCurryP_def:
  compatCurryP id pat =
    case id of
      Long mn vn =>
        if mn = «PrettyPrinter» ∧ vn = Short «PP_Data» then
          case pat of
            Pp_con NONE ps => Pp_con (SOME id) ps
          | _ => Pp_con (SOME id) [pat]
        else
          Pp_con (SOME id) [pat]
    | Short nm =>
        if nm = «Abs» ∨ nm = «Var» ∨ nm = «Const» ∨ nm = «Comb» ∨
           nm = «Tyapp» ∨ nm = «Sequent» ∨ nm = «Append» then
          case pat of
          | Pp_any => Pp_con (SOME id) [Pp_any; Pp_any]
          | Pp_con NONE ps => Pp_con (SOME id) ps
          | _ => Pp_con (SOME id) [pat]
        else
          Pp_con (SOME id) [pat]
End

Definition compatCurryE_def:
  compatCurryE id exp =
    case id of
      Long mn vn =>
        if mn = «PrettyPrinter» ∧ vn = Short «PP_Data» then
          case exp of
            Con NONE xs => Con (SOME id) xs
          | _ => Con (SOME id) [exp]
        else
          Con (SOME id) [exp]
    | Short nm =>
        if nm = «Abs» ∨ nm = «Var» ∨ nm = «Const» ∨ nm = «Comb» ∨
           nm = «Tyapp» ∨ nm = «Sequent» ∨ nm = «Append» then
          case exp of
            Con NONE xs => Con (SOME id) xs
          | _ => Con (SOME id) [exp]
        else if nm = «Ref» then
          App Opref [exp]
        else
          Con (SOME id) [exp]
End

(* Rename some constructors from basis that Candle needs (but otherwise cannot
 * parse).
 *)

Definition compatCons_def:
  compatCons cn =
    if cn = «Bad_file_name» then «BadFileName»
    else if cn = «Pp_data» then «PP_Data»
    else cn
End

(* Rename some module names from basis that Candle needs (but otherwise cannot
 * parse).
 *)

Definition compatModName_def:
  compatModName mn =
    if mn = «Text_io» then «TextIO»
    else if mn = «Pretty_printer» then «PrettyPrinter»
    else if mn = «Command_line» then «CommandLine»
    else if mn = «Word8_array» then «Word8Array»
    else mn
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
              return «lsl»
            else if tk = LsrT then
              return «lsr»
            else if tk = AsrT then
              return «asr»
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nShiftOp»)
          else if nterm = INL nMultOp then
            if tk = StarT then
              return «*»
            else if tk = ModT then
              return «mod»
            else if tk = LandT then
              return «land»
            else if tk = LorT then
              return «lor»
            else if tk = LxorT then
              return «lxor»
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nMultOp»)
          else if nterm = INL nAddOp then
            if tk = PlusT then
              return «+»
            else if tk = MinusT then
              return «-»
            else if tk = MinusFT then
              return «-.»
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
             fail (locs, «Impossible: nAddOp»)
          else if nterm = INL nRelOp then
            if tk = LessT then
              return «<»
            else if tk = GreaterT then
              return «>»
            else if tk = EqualT then
              return «=»
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nRelOp»)
          else if nterm = INL nAndOp then
            if tk = AndalsoT then
              return «&&»
            else if tk = AmpT then
              return «&»
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nAndOp»)
          else if nterm = INL nOrOp then
            if tk = OrelseT then
              return «||»
            else if tk = OrT then
              return «|»
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return s
            else
              fail (locs, «Impossible: nOrOp»)
          else if nterm = INL nHolInfixOp then
            if tk = FuncompT then
              return «o»
            else if tk = F_FT then
              return «F_F»
            else if tk = THEN_T then
              return «THEN»
            else if tk = THENC_T then
              return «THENC»
            else if tk = THENL_T then
              return «THENL»
            else if tk = THEN_TCL_T then
              return «THEN_TCL»
            else if tk = ORELSE_T then
              return «ORELSE»
            else if tk = ORELSEC_T then
              return «ORELSEC»
            else if tk = ORELSE_TCL_T then
              return «ORELSE_TCL»
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
              return «<-»
            else if tk = UpdateT then
              return «:=»
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
            fmap compatCons $ option $ destIdent tk
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

Definition ptree_FieldName_def:
  ptree_FieldName (Lf (_, locs)) =
    fail (locs, «Expected fieldname non-terminal») ∧
  ptree_FieldName (Nd (nterm, locs) args) =
    if nterm = INL nFieldName then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            option $ destIdent tk
          od
      | _ => fail (locs, «Impossible: nFieldName»)
    else
      fail (locs, «Expected fieldname non-terminal»)
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
            fmap compatModName $ option $ destIdent tk
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
      | [name; dot; rest] =>
          do
            expect_tok dot DotT;
            vp <- ptree_ModuleName name;
            vn <- ptree_Constr rest;
            return (vp::vn)
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
        [arg] => fmap (λvn. [vn]) $ ptree_ModTypeName arg
      | [name; dot; rest] =>
          do
            expect_tok dot DotT;
            vm <- ptree_ModuleName name;
            vp <- ptree_ModTypePath rest;
            return (vm :: vp)
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
        [arg] => ptree_Type arg
      | arg::rest =>
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

Definition bool2id_def:
  bool2id b = Short (if b then «True» else «False»)
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
              return (bool2id (tk = TrueT))
            else
              fail (locs, «not a boolean literal»)
          od
      | _ => fail (locs, «Impossible: nLiteral (bool)»)
    else
      fail (locs, «Expected a boolean literal non-terminal»)
End

Definition ptree_Double_def:
  ptree_Double (Lf (_, locs)) =
    fail (locs, «Expected a float literal non-terminal») ∧
  ptree_Double (Nd (nterm, locs) args) =
    if nterm = INL nLiteral then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if isFloat tk then
              return $ Lit $ StrLit $ THE $ destFloat tk
            else
              fail (locs, «not a float literal»)
          od
      | _ => fail (locs, «Impossible: nLiteral (float)»)
    else
      fail (locs, «Expected a float literal non-terminal»)
End

Definition nterm_of_def:
  nterm_of (Lf (_, locs)) = fail (locs, «nterm_of: Not a parsetree node») ∧
  nterm_of (Nd (nterm, _) args) = return nterm
End

(* This code was adapted from the following parser code in the pure repository:
 * github.com/CakeML/pure/blob/master/compiler/parsing/cst_to_astScript.sml
 *)

val _ = enable_monad "option";

Datatype:
  prec = Left | Right | NonAssoc
End

Datatype:
  pp_op = po_cons | po_prod | po_or | po_alias
End

Definition tokprec_def:
  tokprec op: (num # prec) option = SOME $
    case op of
      po_cons => (3, Right)
    | po_prod => (2, Left)
    | po_or => (1, Left)
    | po_alias => (0, NonAssoc)
End

Definition tok_action_def:
  tok_action (INL stktok, INL inptok) =
    do
      (stkprec, stka) <- tokprec stktok;
      (inpprec, inpa) <- tokprec inptok;
      if stka = NonAssoc then SOME Reduce (* only po_alias *)
      else if inpprec < stkprec then SOME Reduce
      else if stkprec < inpprec then SOME Shift
      else if stka ≠ inpa ∨ stka = NonAssoc then NONE
      else if stka = Left then SOME Reduce
      else SOME Shift
    od ∧
  tok_action _ = NONE
End

val _ = disable_monad "option";

(* Alias-patterns collapse into a pattern, an operator, and an identifier list.
 *)

Definition dest_alias_def:
  dest_alias pp =
    case pp of
      Pp_alias pp ns => SOME (pp, ns)
    | _ => NONE
End

Definition tok2ppo:
  tok2ppo pt =
    do
      lf <- destLf pt;
      tk <- option $ destTOK lf;
      if tk = ColonsT then
        return po_cons
      else if tk = CommaT then
        return po_prod
      else if tk = BarT then
        return po_or
      else
        fail (unknown_loc, «ppatOp: impossible»)
    od
End

(* tok: pp_op + (ppat + varN list)
 * trm: ppat + varN list
 *)

Definition ppat_close_def:
  ppat_close (Pp_prod pps) = Pp_con NONE pps ∧
  ppat_close (Pp_alias pp vs) = FOLDL Pp_as pp vs ∧
  ppat_close pps = pps
End

Definition ppat_reduce_def:
  ppat_reduce a op b =
    case op of
      INL po_or =>
        (case (a, b) of
           (INL x, INL y) => SOME (INL (Pp_or (ppat_close x) y))
         | _ => NONE)
    | INL po_prod =>
        (case (a, b) of
           (INL (Pp_prod ps), INL y) => SOME (INL (Pp_prod (ps ++ [y])))
         | (INL x, INL y) => SOME (INL (Pp_prod [x; y]))
         | _ => NONE)
    | INL po_cons =>
        (case (a, b) of
           (INL x, INL y) =>
             SOME (INL (Pp_con (SOME (Short «::»)) [ppat_close x; y]))
         | _ => NONE)
    | INL po_alias =>
        (case (a, b) of
           (INL x, INR y) => SOME (INL (Pp_alias (ppat_close x) y))
         | _ => NONE)
    | _ => NONE
End

Definition resolve_precs_def:
  resolve_precs xs =
    case precparser$precparse <|
           rules := (λx. tok_action x);
           reduce := (λx op y. ppat_reduce x op y);
           (* All x's should be INR's *)
           lift := (λx. case x of INR y => y | _ => INR []);
           isOp := (λx. ISL x);
           mkApp := (λx y. NONE);
         |> ([], xs) of
      SOME (INL ppat) => return $ ppat_close ppat
    | _ => fail (unknown_loc, «resolve_precs»)
End

Definition ptree_AsIds_def:
  ptree_AsIds [] = return [] ∧
  ptree_AsIds [_] = fail (unknown_loc, «Impossible: ptree_AsIds») ∧
  ptree_AsIds (x::y::xs) =
    do
      expect_tok x AsT;
      n <- ptree_Ident y;
      ns <- ptree_AsIds xs;
      return (n::ns)
    od
End

(* Turns a list literal pattern “[x; y; z]” into the
 * constructor pattern “x::y::z::[]”.
 *)

Definition build_list_ppat_def:
  build_list_ppat =
    FOLDR (λt p. Pp_con (SOME (Short «::»)) [t; p])
          (Pp_con (SOME (Short «[]»)) [])
End

Definition ptree_FieldsList_def:
  (ptree_FieldsList [rbrace] =
    do
      expect_tok rbrace RbraceT;
      return []
    od) ∧
  (ptree_FieldsList [semi; rbrace] =
    do
      expect_tok semi SemiT;
      expect_tok rbrace RbraceT;
      return []
    od) ∧
  (ptree_FieldsList (semi::fname::fs) =
    do
      expect_tok semi SemiT;
      fn <- ptree_FieldName fname;
      fns <- ptree_FieldsList fs;
      return (fn::fns)
    od) ∧
  (ptree_FieldsList [] = fail (unknown_loc, «Impossible: ptree_FieldsList»))
End

Definition ptree_PRecFields_def:
  (ptree_PRecFields (Lf (_, locs)) =
    fail (locs, «Expected a pattern record fields non-terminal»)) ∧
  (ptree_PRecFields (Nd (nterm, locs) args) =
    if nterm = INL nPRecFields then
      case args of
        lbrace::fname::rest =>
          do
            expect_tok lbrace LbraceT;
            fn <- ptree_FieldName fname;
            fns <- ptree_FieldsList rest;
            return (fn::fns)
          od
      | _ => fail (locs, «Impossible: nPRecFields»)
    else
      fail (locs, «Expected a pattern record fields non-terminal»))
End

Definition ptree_PPattern_def:
  (ptree_PPattern (Lf (_, locs)) =
    fail (locs, «Expected a pattern non-terminal»)) ∧
  (ptree_PPattern (Nd (nterm, locs) args) =
    if nterm = INL nPAny then
      case args of
        [arg] =>
          do
            expect_tok arg AnyT;
            return Pp_any
          od
      | _ => fail (locs, «Impossible: nPAny»)
    else if nterm = INL nPList then
      case args of
        lbrack::rest =>
          do
            expect_tok lbrack LbrackT;
            ps <- ptree_PPatternList rest;
            return $ build_list_ppat ps
          od
      | _ => fail (locs, «Impossible: nPList»)
    else if nterm = INL nPPar then
      case args of
        [l; r] =>
          do
            expect_tok l LparT;
            expect_tok r RparT;
            return $ Pp_con NONE []
          od
      | [l; p; r] =>
          do
            expect_tok l LparT;
            expect_tok r RparT;
            ptree_PPattern p
          od
      | [lpar; pat; colon; typ; rpar] =>
          do
            expect_tok lpar LparT;
            expect_tok rpar RparT;
            expect_tok colon ColonT;
            p <- ptree_PPattern pat;
            ty <- ptree_Type typ;
            return $ Pp_tannot p ty
          od
      | _ => fail (locs, «Impossible: nPPar»)
    else if nterm = INL nPatLiteral then
      case args of
        [arg] =>
          fmap Pp_lit (ptree_Literal arg) ++
          fmap (λb. Pp_con (SOME b) []) (ptree_Bool arg)
      | [minus; arg] =>
          do
            expect_tok minus MinusT;
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            if isInt tk then
              return $ Pp_lit $ IntLit $ -(THE $ destInt tk)
            else
              fail (locs, «Impossible: nPatLiteral»)
          od
      | _ => fail (locs, «Impossible: nPatLiteral»)
    else if nterm = INL nPBase then
      case args of
        [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nValueName then
              fmap Pp_var (ptree_ValueName arg)
            else if n = INL nConstr then
              do
                cns <- ptree_Constr arg;
                id <- path_to_ns locs cns;
                return $ Pp_con (SOME id) []
              od
            else if n = INL nPatLiteral ∨ n = INL nPAny ∨ n = INL nPList ∨
                    n = INL nPPar then
              ptree_PPattern arg
            else
              fail (locs, «Impossible: nPBase»)
         od
      | _ => fail (locs, «Impossible: nPBase»)
    else if nterm = INL nPCons then
      case args of
        [cn] =>
          do
            cns <- ptree_Constr cn;
            id <- path_to_ns locs cns;
            return $ Pp_con (SOME id) []
          od ++ ptree_PPattern cn
      | [cn; arg] =>
          do
            cns <- ptree_Constr cn;
            id <- path_to_ns locs cns;
            fs <- ptree_PRecFields arg;
            return $ Pp_record id fs
          od ++
          do
            cns <- ptree_Constr cn;
            id <- path_to_ns locs cns;
            p <- ptree_PPattern arg;
            return $ compatCurryP id p
          od
      | _ => fail (locs, «Impossible: nPCons»)
    else if nterm = INL nPAs then
      case args of
        pat :: asids =>
          do
            p <- ptree_PPattern pat;
            nms <- ptree_AsIds asids;
            case nms of
              [] => return p
            | _ => return $ Pp_alias p nms
          od
      | _ => fail (locs, «Impossible: nPAs»)
    else if nterm = INL nPOps then
      case args of
        [] => fail (locs, «Impossible: nPOps» )
      | pat::rest =>
          do
            p <- ptree_PPattern pat;
            start <<- case dest_alias p of
                        NONE => [INR (INL p)]
                      | SOME (pp,ns) =>
                          [INR (INR ns); INL po_alias; INR (INL pp)];
            precs <- grabPairs start rest;
            resolve_precs precs
          od
    else if nterm = INL nPattern then
      case args of
        [pat] => ptree_PPattern pat
      | _ => fail (locs, «Impossible: nPattern»)
    else
      fail (locs, «Expected a pattern non-terminal»)) ∧
  (ptree_PPatternList [] =
    fail (unknown_loc, «Pattern lists cannot be empty»)) ∧
  (ptree_PPatternList [t] =
     do
       expect_tok t RbrackT;
       return []
     od) ∧
  (ptree_PPatternList (p::ps) =
     do
       expect_tok p SemiT;
       ptree_PPatternList ps
     od ++
     do
       q <- ptree_PPattern p;
       qs <- ptree_PPatternList ps;
       return (q::qs)
     od) ∧
  (grabPairs A [] = return (REVERSE A)) ∧
  (grabPairs A [_] = fail (unknown_loc, «grabPairs»))  ∧
  (grabPairs A (pt1 :: pt2 :: rest) =
    do
      opv <- tok2ppo pt1;
      v <- ptree_PPattern pt2;
      case dest_alias v of
        SOME (pp, ns) =>
          grabPairs (INR (INR ns):: INL po_alias:: INR (INL pp):: INL opv:: A)
                    rest
      | _ => grabPairs (INR (INL v):: INL opv:: A) rest
    od)
Termination
  WF_REL_TAC ‘measure $ sum_size psize
                      $ sum_size (list_size psize)
                      $ pair_size ((K 0)) $ list_size psize’
  \\ simp [parsetree_size_lemma]
End

Theorem ptree_PPattern_ind[allow_rebind] =
  SIMP_RULE (srw_ss() ++ CONJ_ss) [] ptree_PPattern_ind;

(* The pattern parser functions return INL for record patterns, and INR for
 * real patterns. Record patterns do not have a counterpart in the :pat type,
 * so we perform some bookkeeping here.
 *
 * To simplify matters, we don't accept record patterns anywhere but at the
 * top-level. The function ppat_to_pat fails if it encounters a record pattern.
 * We convert record patterns directly in this function instead.
 *)

Definition ptree_Pattern_def:
  ptree_Pattern p =
    do
      pp <- ptree_PPattern p;
      case pp of
        Pp_record id fs => return $ [INL (id, fs)] (* record *)
      | _ =>
        do
          ps <- ppat_to_pat pp;
          return $ MAP INR ps
        od ++
        fail (unknown_loc, «Record patterns may only appear at the top level»)
    od
End

Definition ptree_Patterns_def:
  ptree_Patterns (Lf (_, locs)) =
    fail (locs, «Expected pattern list non-terminal») ∧
  ptree_Patterns (Nd (nterm, locs) args) =
    if nterm = INL nPatterns then
      case args of
        [pat] => fmap (λp. [p]) $ ptree_Pattern pat
      | [pat; rest] =>
          do
            p <- ptree_Pattern pat;
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
  build_binop symb x y =
    if symb = «&&» then
      Log Andalso x y
    else if symb = «||» then
      Log Orelse x y
    else
      App Opapp [App Opapp [Var (Short symb); x]; y]
End

(* Turns a list literal expression “[x; y; z]” into the
 * constructor application “x::y::z::[]”.
 *)

Definition build_list_exp_def:
  build_list_exp =
    FOLDR (λt e. Con (SOME (Short «::»)) [t; e])
          (Con (SOME (Short «[]»)) [])
End

Definition build_funapp_def:
  build_funapp f xs =
    FOLDL (λa b.
      case a of
        Var (Short id) =>
          if id = «raise» then
            Raise b
          else
            App Opapp [a; b]
      | _ => App Opapp [a; b]) f xs
End

(* Functions for records.
 * TODO Make it so that the names include the constructor function, so that we
 *      can have the same record field name defined for different record types.
 *)

Definition mk_record_update_name_def:
  mk_record_update_name field cons =
    concat [«{record_update(» ^ cons ^ «.» ^ field ^ «)}»]
End

Definition id_map_def:
  id_map f (Long mn id) = Long mn (id_map f id) /\
  id_map f (Short nm) = Short (f nm)
End

Definition build_record_upd_def:
  build_record_upd cons b (f,x) =
    App Opapp [App Opapp [Var (id_map (mk_record_update_name f) cons); b]; x]
End

Definition mk_record_proj_name_def:
  mk_record_proj_name field cons =
    concat [«{record_projection(» ^ cons ^ «.» ^ field ^ «)}»]
End

Definition build_record_proj_def:
  build_record_proj cons f x =
    App Opapp [Var (id_map (mk_record_proj_name f) cons); x]
End

Definition mk_record_constr_name_def:
  mk_record_constr_name constr fields =
    concat ([«{record_constructor(»; constr; «)»] ++
            MAP (λfn. «(» ^ fn ^ «)») fields ++ [«}»])
End

Definition build_record_cons_id_def:
  build_record_cons_id fns [] =
    fail (unknown_loc, «build_record_cons_id: empty path») ∧
  build_record_cons_id fns [cn] =
    return $ Short $ mk_record_constr_name cn fns ∧
  build_record_cons_id fns (c::cs) =
    do
      id <- build_record_cons_id fns cs;
      return $ Long c id
    od
End

Definition build_record_cons_def:
  build_record_cons path upds =
    let (names,exprs) = UNZIP (sort (λ(f,_) (g,_). mlstring_lt f g) upds) in
      do
        id <- build_record_cons_id names path;
        return $ build_funapp (Var id) exprs
      od
End

(* Pattern match on a record: first pattern match on the constructor (with
 * a wildcard for the pattern that would otherwise contain the argument tuple)
 * and then generate a let-binding for each field name matched on. Example:
 *
 *   type a = Foo of { a: int; b: bool; c: string };;
 *   match x with
 *   | Foo { a, b } -> f a b
 *
 * becomes
 *
 *   type a = Foo of int * bool * string;;
 *   match x with
 *   | Foo _ -> let a = <build_record_proj(Foo,a)>(x) in
 *              let b = <build_record_proj(Foo,a)>(x) in
 *                f a b
 *)

Definition mk_record_match_aux_def:
  mk_record_match_aux recv constr body [] = body /\
  mk_record_match_aux recv constr body (f::fs) =
    Let (SOME f) (build_record_proj constr f (Var (Short recv)))
                 (mk_record_match_aux recv constr body fs)
End

Definition mk_record_match_def:
  mk_record_match constr fs recv body =
    Mat (Var (Short recv))
        [Pcon (SOME constr) [Pany], mk_record_match_aux recv constr body fs]
End

(* Turns a curried lambda with patterns, e.g. “fun a [3;4] c -> e”
 * into a sequence of lambdas, possibly with pattern matches:
 * “fun a -> fun fresh -> match fresh with [3;4] -> fun c -> e”.
 *)

Definition build_fun_lam_def:
  build_fun_lam body pats =
      FOLDR (λp b. case p of
                     INL (c, fs) => Fun «» (mk_record_match c fs «» b)
                   | INR (Pvar x) => Fun x b
                   | INR p => Fun «» (Mat (Var (Short «»)) [p, b]))
            body pats
End

(*
 * build_letrec is given a list of entries consisting of:
 * - a function name
 * - a list of patterns
 * - a body expression.
 *
 * A letrec in the CakeML AST is made from a function name, a variable name, and
 * a body expression. If there is no pattern in the list given to build_letrec,
 * then we use the empty variable name ("") and apply the body expression to
 * this variable (like eta expansion). This enables us to write things like:
 *   let rec f = function ... -> ...
 * or
 *   let rec f x y = ...
 *   and g = ...
 *
 * As a consequence, the parser will turn this:
 *   let rec f x = ...
 *   and y = 5
 * into this:
 *   let rec f x = ...
 *   and y x = 5 x
 * which is different from what OCaml generates (it correctly binds the value 5
 * to y with a let).
 *
 * Patterns are turned into variables using pattern match expressions:
 * - If the first pattern is not a variable, invent a variable name and
 *   match on it using the first pattern.
 * - If the first pattern is a variable, create a lambda.
 *)

Definition build_letrec_def:
  build_letrec =
    MAP (λ(f,ps,x).
           case ps of
             [] =>
               (f, «», App Opapp [x; Var (Short «»)])
           | INL (c, fs) ::ps =>
               (f, «», mk_record_match c fs «» (build_fun_lam x ps))
           | INR (Pvar v)::ps =>
               (f, v, build_fun_lam x ps)
           | INR p::ps =>
               (f, «», Mat (Var (Short «»)) [(p, build_fun_lam x ps)]))
End

(* Builds a sequence of lets out of a list of let bindings.
 *
 * N.B. The sum type determines whether we're building a regular let (INL), or
 * a let rec (INR).
 *)

Definition build_lets_def:
  build_lets binds body =
    FOLDR (λbind rest.
             case bind of
               INL (INL (c, fs), x) =>
                 Let (SOME « r») x (mk_record_match c fs « r» rest)
             | INL (INR (Pvar v), x) =>
                 Let (SOME v) x rest
             | INL (INR Pany, x) =>
                 Let NONE x rest
             | INL (INR p, x) =>
                 Mat x [p, rest]
             | INR (f, ps, bd) =>
                 Let (SOME f) (build_fun_lam bd ps) rest)
          binds body
End

(* N.B. The match-building functions do not accept mixing value definitions
 * (i.e., with no function arguments) with recursive definitions (let rec y =
 * ...). For example, the parser won't accept this:
 *
 *   let rec f x = y
 *   and z = 5;;
 *)

(* Build pattern match rows from lists of patterns that contain record matches.
 *)

Definition build_match_row_def:
  build_match_row mvar (INL (c, fs), x) =
     (Pcon (SOME c) [Pany], mk_record_match c fs mvar x) ∧
  build_match_row y (INR p, x) =
     (p, x)
End

(* I don't remember what was smart about this? *)

Definition SmartMat_def:
  SmartMat mvar [INR Pany, y] = y ∧
  SmartMat mvar rows =
    Mat (Var (Short mvar)) (MAP (build_match_row mvar) rows)
End

(* Builds a pattern match expression that allocates a closure each time a guard
 * expression is encountered. N.B. this expects a call with pattern rows in
 * reverse order.
 *)

Definition build_pmatch_def:
  build_pmatch mvar acc [] =
    SmartMat mvar acc ∧
  build_pmatch mvar acc ((pat,exp,NONE)::ps) =
    build_pmatch mvar ((pat,exp)::acc) ps ∧
  build_pmatch mvar acc ((pat,exp,SOME guard)::ps) =
    let mexp = SmartMat mvar acc in
    let clos = Let (SOME « p») (Fun « u» mexp) in
    let call = App Opapp [Var (Short « p»); Con NONE []] in
    let mat = SmartMat mvar [(pat,If guard exp call); (INR Pany,call)] in
      build_pmatch mvar [INR Pany,clos mat] ps
End

Definition build_match_def:
  build_match x rows =
    let mvar = « m» in
    Let (SOME mvar) x
      (if EXISTS (λ(p,x,g). case g of SOME _ => T | _ => F) rows then
         build_pmatch mvar [] (REVERSE rows)
       else
         (Mat (Var (Short mvar))
              (MAP (λ(p,x,g). build_match_row mvar (p,x)) rows)))
End

Definition build_handle_def:
  build_handle x rows =
    (* Save the handled exception in a variable by first matching with Handle
     * on a single variable, and then applying Mat to the variable. Reraise the
     * exception in case of no match.
     *
     * This trickery is used to support pattern guards and fake records.
     *)
    let mvar = « e» in
    let rows' = (INR Pany, Raise (Var (Short mvar)), NONE)::REVERSE rows in
    Handle x [Pvar mvar, build_pmatch mvar [] rows']
End

Definition build_function_def:
  build_function rows =
    Fun «»  (build_pmatch «» [] (REVERSE rows))
End

(* Flatten the row-alternatives in a pattern-match.
 *)

Definition flatten_pmatch_def:
  flatten_pmatch pss = FLAT (MAP (λ(ps,x,w). MAP (λp. (p,x,w)) ps) pss)
End

Definition ptree_Expr_def:
  (ptree_Expr et (Lf (_, locs)) =
    fail (locs, «Expected an expression non-terminal»)) ∧
  (ptree_Expr et (Nd (nterm, locs) args) =
    if INL et ≠ nterm then
      fail (locs, «ptree_Expr»)
    else if nterm = INL nExpr then
      case args of
        [arg] => ptree_Expr nESeq arg
      | _ => fail (locs, «Impossible: nExpr»)
    else if nterm = INL nEUnclosed then
      case args of
        [arg] =>
          do
            n <- nterm_of arg;
            if n = INL nELet then
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
            else if n = INL nEApp then
              ptree_Expr nEApp arg
            else
              fail (locs, «Expected an expression non-terminal»)
          od
      | _ => fail (locs, «Impossible: nEUnclosed»)
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
            if n = INL nERecUpdate then
              ptree_Expr nERecUpdate arg
            else if n = INL nLiteral then
              fmap (λid. Con (SOME id) []) (ptree_Bool arg) ++
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
    else if nterm = INL nERecUpdate then
      case args of
        [arg; lb; x; witht; upds; semi; rb] =>
          do
            expect_tok lb LbraceT;
            expect_tok witht WithT;
            expect_tok semi SemiT;
            expect_tok rb RbraceT;
            e <- ptree_Expr nExpr x;
            us <- ptree_Updates upds;
            cns <- ptree_Constr arg;
            ns <- path_to_ns locs cns;
            return $ FOLDL (build_record_upd ns) e us
          od
      | [arg; lb; x; witht; upds; rb] =>
          do
            expect_tok lb LbraceT;
            expect_tok witht WithT;
            expect_tok rb RbraceT;
            e <- ptree_Expr nExpr x;
            us <- ptree_Updates upds;
            cns <- ptree_Constr arg;
            ns <- path_to_ns locs cns;
            return $ FOLDL (build_record_upd ns) e us
          od
      | _ => fail (locs, «Impossible: nERecUpdate»)
    else if nterm = INL nEIndex then
      case args of
        [arg] => ptree_Expr nEPrefix arg
      | [arg; idx] =>
          do
            pfx <- ptree_Expr nEPrefix arg;
            idx_expr <- ptree_Index idx;
            case idx_expr of
              INL str_idx =>
                return $ build_funapp (Var (Long «String» (Short «sub»)))
                                      [pfx; str_idx]
            | INR arr_idx =>
                return $ build_funapp (Var (Long «Array» (Short «sub»)))
                                      [pfx; arr_idx]
          od
      | _ => fail (locs, «Impossible: nEIndex»)
    else if nterm = INL nERecProj then
      case args of
        [arg] => ptree_Expr nEIndex arg
      | [arg; dot1; cons; dot2; fn] =>
          do
            expect_tok dot1 DotT;
            expect_tok dot2 DotT;
            x <- ptree_Expr nEIndex arg;
            f <- ptree_FieldName fn;
            cns <- ptree_Constr cons;
            ns <- path_to_ns locs cns;
            return $ build_record_proj ns f x
          od
      | _ => fail (locs, «Impossible: nERecProj»)
    else if nterm = INL nERecCons then
      case args of
        [cons; lb; upds; semi; rb] =>
          do
            expect_tok lb LbraceT;
            expect_tok semi SemiT;
            expect_tok rb RbraceT;
            path <- ptree_Constr cons;
            us <- ptree_Updates upds;
            build_record_cons path us
          od
      | [cons; lb; upds; rb] =>
          do
            expect_tok lb LbraceT;
            expect_tok rb RbraceT;
            path <- ptree_Constr cons;
            us <- ptree_Updates upds;
            build_record_cons path us
          od
      | _ => fail (locs, «Impossible: nERecCons»)
    else if nterm = INL nEAssert then
      case args of
        [assr; expr] =>
          do
            expect_tok assr AssertT;
            x <- ptree_Expr nERecProj expr;
            return (App Opapp [Var (Short «assert»); x])
          od
      | _ => fail (locs, «Impossible: nEAssert»)
    else if nterm = INL nELazy then
      case args of
        [lazy; expr] =>
          do
            expect_tok lazy LazyT;
            x <- ptree_Expr nERecProj expr;
            return (App Opapp [Var (Short «lazy»); x])
          od
      | _ => fail (locs, «Impossible: nELazy»)
    else if nterm = INL nEConstr then
      case args of
        [consid; expr] =>
          do
            cns <- ptree_Constr consid;
            id <- path_to_ns locs cns;
            x <- ptree_Expr nERecProj expr;
            return $ compatCurryE id x
          od
      | _ => fail (locs, «Impossible: nEConstr»)
    else if nterm = INL nEFunapp then
      case args of
        [exp] => ptree_Expr nERecProj exp
      | [fexp; aexp] =>
          do
            f <- ptree_Expr nEFunapp fexp;
            x <- ptree_Expr nERecProj aexp;
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
            else if n = INL nERecCons then
              ptree_Expr nERecCons arg
            else if n = INL nERecProj then
              ptree_Expr nERecProj arg
            else
              fail (locs, «Impolssible: nEApp»)
          od
      | _ => fail (locs, «Impossible: nEApp»)
    else if nterm = INL nEPrefix then
      case args of
        [opn; expr] =>
          do
            op <- ptree_Op opn;
            x <- ptree_Expr nEBase expr;
            return (App Opapp [Var (Short op); x])
          od
      | [arg] => ptree_Expr nEBase arg
      | _ => fail (locs, «Impossible: nEPrefix»)
    else if nterm = INL nENeg then
      case args of
        [pref; expr] =>
          do
            lf <- destLf pref;
            tk <- option $ destTOK lf;
            x <- ptree_Expr nEUnclosed expr;
            if tk = MinusT then
              return (App Opapp [Var (Long «Int» (Short «~»)); x])
            else if tk = MinusFT then
              return (App Opapp [Var (Long «Double» (Short «~»)); x])
            else if isSymbol tk then
              let s = THE (destSymbol tk) in
                return (App Opapp [Var (Short s); x])
            else
              fail (locs, «Impossible: nEPrefix»)
          od
      | [arg] => ptree_Expr nEUnclosed arg
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
            return (Con (SOME (Short «::»)) [x; y])
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
            y1 <- ptree_Expr nEIf y;
            z1 <- ptree_Expr nEIf z;
            return (If x1 y1 z1)
          od
      | [ift; x; thent; y] =>
          do
            expect_tok ift IfT;
            expect_tok thent ThenT;
            x1 <- ptree_Expr nExpr x;
            y1 <- ptree_Expr nEIf y;
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
            y1 <- ptree_Expr nExpr y;
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
            return (Letrec (build_letrec binds) body)
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
        [match; expr; witht; pm] =>
          do
            expect_tok match MatchT;
            expect_tok witht WithT;
            x <- ptree_Expr nExpr expr;
            ps <- ptree_PatternMatch pm;
            return (build_match x (flatten_pmatch ps))
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
            (if EVERY (λp. case p of [_] => T | _ => F) ps then return () else
              fail (locs, «Or-patterns are not allowed in fun expressions»));
            return (build_fun_lam x (FLAT ps))
          od
      | [funt; params; colon; typ; rarrow; expr] =>
          do
            expect_tok funt FunT;
            expect_tok rarrow RarrowT;
            ps <- ptree_Patterns params;
            x <- ptree_Expr nExpr expr;
            ty <- ptree_Type typ;
            (if EVERY (λp. case p of [_] => T | _ => F) ps then return () else
              fail (locs, «Or-patterns are not allowed in fun expressions»));
            return (Tannot (build_fun_lam x (FLAT ps)) ty)
          od
      | _ => fail (locs, «Impossible: nEFun»)
    else if nterm = INL nEFunction then
      case args of
        [funct; pm] =>
          do
            expect_tok funct FunctionT;
            ps <- ptree_PatternMatch pm;
            return (build_function (flatten_pmatch ps))
          od
      | _ => fail (locs, «Impossible: nEFunction»)
    else if nterm = INL nETry then
      case args of
        [tryt; expr; witht; pm] =>
          do
            expect_tok tryt TryT;
            expect_tok witht WithT;
            x <- ptree_Expr nExpr expr;
            ps <- ptree_PatternMatch pm;
            return (build_handle x (flatten_pmatch ps))
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
            return (build_funapp (Var (Short «while»)) [x; b])
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
            return (build_funapp (Var (Short «for»))
                                 [Con (SOME (bool2id (tk = ToT))) [];
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
            (if EVERY (λp. case p of [_] => T | _ => F) ps then return () else
              fail (locs, «Or-patterns are not allowed in let (rec) bindings»));
            return (nm, FLAT ps, Tannot bd ty)
          od
      | [id; pats; eq; expr] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            bd <- ptree_Expr nExpr expr;
            (if EVERY (λp. case p of [_] => T | _ => F) ps then return () else
              fail (locs, «Or-patterns are not allowed in let (rec) bindings»));
            return (nm, FLAT ps, bd)
          od
      | [id; colon; type; eq; expr] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_ValueName id;
            ty <- ptree_Type type;
            bd <- ptree_Expr nExpr expr;
            return (nm, [], Tannot bd ty)
          od
      | [id; eq; expr] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            bd <- ptree_Expr nExpr expr;
            return (nm, [], bd)
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
            ps <- ptree_Pattern pat;
            bd <- ptree_Expr nExpr bod;
            case ps of
              [p] => return (INL (p, bd))
            | _ =>
              fail (locs, «Or-patterns are not allowed in let (rec) bindings»)
          od
      | [id; pats; eq; bod] =>
          do
            expect_tok eq EqualT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            bd <- ptree_Expr nExpr bod;
            (if EVERY (λp. case p of [_] => T | _ => F) ps then return () else
              fail (locs, «Or-patterns are not allowed in let (rec) bindings»));
            return $ INR (nm, FLAT ps, bd)
          od
      | [id; colon; type; eq; bod] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_ValueName id;
            ty <- ptree_Type type;
            bd <- ptree_Expr nExpr bod;
            return $ INL (INR (Pvar nm), Tannot bd ty)
          od
      | [id; pats; colon; type; eq; bod] =>
          do
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            nm <- ptree_ValueName id;
            ps <- ptree_Patterns pats;
            ty <- ptree_Type type;
            bd <- ptree_Expr nExpr bod;
            (if EVERY (λp. case p of [_] => T | _ => F) ps then return () else
              fail (locs, «Or-patterns are not allowed in let (rec) bindings»));
            return $ INR (nm, FLAT ps, Tannot bd ty)
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
              p <- ptree_Pattern pat;
              x <- ptree_Expr nExpr body;
              w <- ptree_Expr nExpr whenx;
              return [p, x, SOME w]
            od ++
          let pat = a; rarrow = b; body = c; bar = d; pms = e in
            do
              expect_tok rarrow RarrowT;
              expect_tok bar BarT;
              p <- ptree_Pattern pat;
              x <- ptree_Expr nExpr body;
              ps <- ptree_PatternMatches pms;
              return ((p, x, NONE)::ps)
            od
      | [pat; whent; whenx; rarrow; body; bar; pms] =>
          do
            expect_tok rarrow RarrowT;
            expect_tok whent WhenT;
            p <- ptree_Pattern pat;
            x <- ptree_Expr nExpr body;
            w <- ptree_Expr nExpr whenx;
            expect_tok bar BarT;
            ps <- ptree_PatternMatches pms;
            return ((p, x, SOME w)::ps)
          od
      | [pat; rarrow; body] =>
          do
            expect_tok rarrow RarrowT;
            p <- ptree_Pattern pat;
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
    od) ∧
  (ptree_Update (Lf (_, locs)) =
    fail (locs, «Expected an update non-terminal»)) ∧
  (ptree_Update (Nd (nterm,locs) args) =
     if nterm = INL nUpdate then
       case args of
         [fd; eq; expr] =>
           do
             expect_tok eq EqualT;
             f <- ptree_FieldName fd;
             x <- ptree_Expr nEIf expr;
             return (f, x)
           od
       | _ => fail (locs, «Impossible: nUpdate»)
     else
       fail (locs, «Expected an update non-terminal»)) ∧
  (ptree_Updates (Lf (_, locs)) =
    fail (locs, «Expected an updates non-terminal»)) ∧
  (ptree_Updates (Nd (nterm,locs) args) =
     if nterm = INL nUpdates then
       case args of
         [upd] => fmap (λu. [u]) $ ptree_Update upd
       | [upd; semi; upds] =>
           do
             expect_tok semi SemiT;
             u <- ptree_Update upd;
             us <- ptree_Updates upds;
             return (u::us)
           od
       | _ => fail (locs, «Impossible: nUpdates»)
     else
       fail (locs, «Expected an updates non-terminal»)) ∧
  (ptree_Index (Lf (_, locs)) =
    fail (locs, «Expected an index non-terminal»)) ∧
  (ptree_Index (Nd (nterm,locs) args) =
     if nterm = INL nArrIdx then
       case args of
         [dott; lpar; expr; rpar] =>
           do
             expect_tok dott DotT;
             expect_tok lpar LparT;
             expect_tok rpar RparT;
             fmap INR $ ptree_Expr nExpr expr
           od
       | _ => fail (locs, «Impossible: nArrIdx»)
     else if nterm = INL nStrIdx then
       case args of
         [dott; lbrack; expr; rbrack] =>
           do
             expect_tok dott DotT;
             expect_tok lbrack LbrackT;
             expect_tok rbrack RbrackT;
             fmap INL $ ptree_Expr nExpr expr
           od
       | _ => fail (locs, «Impossible: nStrIdx»)
     else
    fail (locs, «Expected an index non-terminal»))
Termination
  WF_REL_TAC ‘measure $ sum_size (pair_size camlNT_size psize)
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size psize
                      $ sum_size (SUC o list_size psize)
                      $ sum_size (SUC o list_size psize)
                      $ sum_size psize
                      $ sum_size psize psize’
  \\ simp [parsetree_size_lemma]
End

(* Tidy up the list bits of the induction theorem.
 *)

Theorem ptree_Expr_ind[allow_rebind] =
  ptree_Expr_ind |> SIMP_RULE (srw_ss() ++ CONJ_ss) [];

Definition ptree_FieldDec_def:
  ptree_FieldDec (Lf (_, locs)) =
    fail (locs, «Expected a field declaration non-terminal») ∧
  ptree_FieldDec (Nd (nterm, locs) args) =
    if nterm = INL nFieldDec then
      case args of
        [fn; colon; ty] =>
          do
            expect_tok colon ColonT;
            f <- ptree_FieldName fn;
            t <- ptree_Type ty;
            return (f, t)
          od
      | _ => fail (locs, «Impossible: nFieldDec»)
    else
      fail (locs, «Expected a field declaration non-terminal»)
End

Definition ptree_FieldDecs_def:
  ptree_FieldDecs (Lf (_, locs)) =
    fail (locs, «Expected a field decls non-terminal») ∧
  ptree_FieldDecs (Nd (nterm, locs) args) =
    if nterm = INL nFieldDecs then
      case args of
        [fdec] => fmap (λfd. [fd]) $ ptree_FieldDec fdec
      | [fdec; semi; fdecs] =>
          do
            expect_tok semi SemiT;
            f <- ptree_FieldDec fdec;
            fs <- ptree_FieldDecs fdecs;
            return (f::fs)
          od
      | _ => fail (locs, «Impossible: nFieldDecs»)
    else
      fail (locs, «Expected a field declaration non-terminal»)
End

(*
 * Record definitions return a list of (field_name,type) pairs.
 *)

Definition ptree_Record_def:
  ptree_Record (Lf (_, locs)) =
    fail (locs, «Expected a record constructor») ∧
  ptree_Record (Nd (nterm, locs) args) =
    if nterm = INL nRecord then
      case args of
        [lb; fds; semi; rb] =>
          do
            expect_tok lb LbraceT;
            expect_tok semi SemiT;
            expect_tok rb RbraceT;
            ptree_FieldDecs fds
          od
      | [lb; fds; rb] =>
          do
            expect_tok lb LbraceT;
            expect_tok rb RbraceT;
            ptree_FieldDecs fds
          od
      | _ => fail (locs, «Impossible: nRecord»)
    else
      fail (locs, «Expected a record constructor»)
End

(*
 * Vanilla constructor definitions return a list of types.
 *)

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

(*
 * A constructor declaration returns one of:
 * - a name and a list of types (a regular constructor)
 * - a name and a list of (name*type) pairs (record constructor)
 * The latter causes a bunch of definitions to be generated.
 *)

Definition ptree_ConstrDecl_def:
  ptree_ConstrDecl (Lf (_, locs)) =
    fail (locs, «Expected a constructor declaration non-terminal») ∧
  ptree_ConstrDecl (Nd (nterm, locs) args) =
    if nterm = INL nConstrDecl then
      case args of
        [name] =>
          fmap (λnm. INL (nm,[])) $ ptree_ConstrName name
      | [name; oft; args] =>
          do
            expect_tok oft OfT;
            nm <- ptree_ConstrName name;
            nt <- nterm_of args;
            if nt = INL nRecord then
              do
                ts <- ptree_Record args;
                return $ INR (nm, ts)
              od
            else if nt = INL nConstrArgs then
              do
                ts <- ptree_ConstrArgs args;
                return $ INL (nm, ts)
              od
            else
              fail (locs, «Impossible: nConstrDecl»)
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
            res <- ptree_ConstrDecl cdecl;
            case res of
            | INR _ => fail (locs, «Record type exceptions are forbidden»)
            | INL (nm, args) => return () (* No types in the CakeML ast *)
          od
      | _ =>
          fail (locs, «Impossible: nExcType»)
    else
      fail (locs, «Expected an exception type declaration non-terminal»)
End

(* Ensure types get 0 or 1 arguments by wrapping >1 arguments in a tuple. *)

Definition ctor_tup_def:
  ctor_tup tys =
    case tys of
      _::_::_ => [Attup tys]
    | _ => tys
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
            res <- ptree_ConstrDecl cdecl;
            case res of
            | INR _ => fail (locs, «Record type exceptions are forbidden»)
            | INL (nm, args) => return $ Dexn locs nm (ctor_tup args)
          od
      | [exnt; lhsid; eq; rhsid] =>
          fail (locs, «Exception abbreviation is not supported»)
      | _ => fail (locs, «Impossible: nExcDefinition»)
    else
      fail (locs, «Expected an exception definition non-terminal»)
End

(* ptree_TypeRepr takes apart the rows in a datatype declaration
 * and returns a list where each element is one of:
 * - a name and a list of types (a regular constructor)
 * - a name and a list of (name*type) pairs (record constructor)
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
        [eqt; arg] =>
          do
            expect_tok eqt EqualT;
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
          od ++
          do
            tys <- ptree_TypeParams id;
            nm <- ptree_TypeConstrName info;
            return (locs, tys, nm, INR [])
          od
      | [id] =>
          do
            nm <- ptree_TypeConstrName id;
            return (locs, [], nm, INR [])
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

(* Builds the constructor, projection, and update functions for a record
 * datatype constructor.
 *
 * TODO It would be possible to build a pretty-printing function for the
 *      datatype, too.
 *)

Definition build_rec_funs_def:
  build_rec_funs (locs, cname, fds) =
    let vars = MAP (Var o Short) fds in
    let rhs = Con (SOME (Short cname))
                  (case vars of
                   | _::_::_ => [Con NONE vars]
                   | _ => vars) in
    let constr = Dlet locs (Pvar (mk_record_constr_name cname fds))
                      (FOLDR (λf x. Fun f x) rhs fds) in
    let pvars = MAP Pvar fds in
    let pat = Pcon (SOME (Short cname))
                   (case pvars of
                    | _::_::_ => [Pcon NONE pvars]
                    | _ => pvars) in
    let projs = MAP (λf.
                  Dlet locs (Pvar (mk_record_proj_name f cname))
                    (Fun «» (Mat (Var (Short «»))
                        [(pat, Var (Short f))]))) fds in
    let upds = MAP (λf.
                  Dlet locs (Pvar (mk_record_update_name f cname))
                    (Fun «» (Mat (Var (Short «»))
                        [(pat, Fun f rhs)]))) fds in
      constr :: projs ++ upds
End

(* This function attempts to make sense of different type declarations. It has
 * grown quite convoluted. ptree_TypeDefs returns a list of tuples:
 *
 *   (locs * (tvarN list) * name * (ast_t + ast_t list + (name * ast_t) list))
 *
 * The sum type chooses between the three kinds of type declarations:
 * - type abbreviations:                  (ast_t)
 *   "type foo = bar"
 * - datatype declarations:               (ast_t list)
 *   "type foo = C of args | D | ..."
 * - record datatype declarations:        ((name # ast_t) list)
 *   "type foo = C { arg1 : type1; ...}"
 *
 * The latter two can be mixed within one declaration. Type declarations can
 * also be mutually recursive, but the type abbreviation cannot be put into
 * mutual recursion with the datatype declarations.
 *
 * A record constructor is turned into a datatype constructor and a set of
 * function definitions for projection, update and construction of values of the
 * record datatype.
 *)

Definition partition_types_def:
  partition_types tdefs =
    let (abbrevs,datas) = PARTITION (λ(_,_,_,trs). ISL trs) tdefs in
    let abbrevs = MAP (λ(l,tvs,cn,trs). (l,tvs,cn,OUTL trs)) abbrevs in
    let datas = MAP (λ(l,tvs,cn,trs). (l,tvs,cn,OUTR trs)) datas in
      (abbrevs,datas)
End

Definition sort_records_def:
  sort_records (locs,tvs,tn,tds) =
    (locs,tvs,tn,
     MAP (λtdef.
       case tdef of
       | INL (cn,tys) => INL (cn,tys)
       | INR (cn,fds) => INR (cn,sort (λ(l,_) (r,_). mlstring_lt l r) fds)) tds)
End

Definition MAP_OUTR_def:
  MAP_OUTR f [] = [] ∧
  MAP_OUTR f ((INR x)::xs) = f x :: MAP_OUTR f xs ∧
  MAP_OUTR f ((INL x)::xs) = MAP_OUTR f xs
End

Definition extract_record_defns_def:
  extract_record_defns (locs,tvs,tn,tds) =
    MAP_OUTR (λ(cn,fds). (locs,cn,MAP FST fds)) tds
End

(* Flattens records into regular datatype constructors. Multi-argument
 * constructors are turned into single argument constructors with tuple
 * arguments.
 *)

Definition strip_record_fields_def:
  strip_record_fields (locs,tvs,cn,trs) =
    (locs,tvs,cn,MAP (λtr. case tr of
                           | INL (n,tys) => (n, ctor_tup tys)
                           | INR (n,fds) => (n, ctor_tup (MAP SND fds))) trs)
End

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
            fail (locs, «nonrec type definitions are not supported»)
          od
      | [typet; tds] =>
          do
            expect_tok typet TypeT;
            tdefs <- fmap REVERSE $ ptree_TypeDefs tds;
            (abbrevs,datas) <<- partition_types tdefs;
            if abbrevs ≠ [] ∧ datas ≠ [] then
              fail (locs, concat[
                    «datatypes and type abbreviations cannot be made »;
                    «mutually recursive»]) else return ();
            abbrevs <<-
              MAP (λ(locs,tys,nm,trs). Dtabbrev locs tys nm trs) abbrevs;
            case datas of
            | [] => return abbrevs
            | _ =>
              do
                defs <<- MAP sort_records datas;
                recs <<- FLAT $ MAP extract_record_defns defs;
                if ¬EVERY (ALL_DISTINCT o SND o SND) recs then
                  fail (locs, «record field names must be distinct»)
                else return ();
                recfuns <<- FLAT $ MAP build_rec_funs recs;
                defs <<- MAP strip_record_fields defs;
                (* Datatype constructors for everything: *)
                datas <<- Dtype locs (MAP SND defs);
                (* Record-related function definitions: *)
                return (datas::abbrevs ++ recfuns)
            od
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
             INL (INL (c, fs), x) =>
               let v = « c» in
               Dlocal
                 [Dlet locs (Pvar v) x]
                 (MAP (λf. Dlet locs (Pvar f)
                                (build_record_proj c f (Var (Short v)))) fs)
           | INL (INR p, x) =>
               Dlet locs p x
           | INR (f,ps,bd) =>
               Dlet locs (Pvar f) (build_fun_lam bd ps))
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
    fmap (λx. [Dlet locs (Pvar «it») x])
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

Definition peg_def:
  peg (Failure locn err) = fail (locn, implode err) ∧
  peg (Success (_: (tokens$token # locs) list) x _) = return x
End

Overload cmlpegexec[local] =
  ``λn t. peg_exec cmlPEG$cmlPEG (cmlPEG$pnt n) t [] NONE [] done failed``;

Definition ptree_Definition_def:
  (ptree_Definition (Lf (_, locs)) =
    fail (locs, «Expected a top-level definition non-terminal»)) ∧
  (ptree_Definition (Nd (nterm, locs) args) =
    if nterm = INL nDefinition then
      case args of
        [arg] => ptree_Definition arg
      | _ => fail (locs, «Impossible: nDefinition»)
    else if nterm = INL nCakeMLPragma then
      case args of
        [arg] =>
          do
            lf <- destLf arg;
            tk <- option $ destTOK lf;
            str <- option $ destPragma tk;
            toks <<- lexer_fun$lexer_fun (explode str);
            if EXISTS (λt. FST t = LexErrorT) toks then
              fail (locs, «The CakeML lexer failed»)
            else
              do
                pts <- peg (destResult (cmlpegexec gram$nTopLevelDecs toks));
                pt <- option $ oHD pts;
                option $ cmlPtreeConversion$ptree_TopLevelDecs pt
              od ++ fail (locs, «The CakeML parser failed»)
          od
      | _ => fail (locs, «Impossible: nCakeMLPragma»)
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
            return [Dletrec locs (build_letrec binds)]
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
      | [modt; modid; colon; modty; eq; mexpr] =>
          do
            expect_tok modt ModuleT;
            expect_tok eq EqualT;
            expect_tok colon ColonT;
            ptree_ModuleType modty;
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
      | [struct; endt] =>
          do
            expect_tok struct StructT;
            expect_tok endt EndT;
            return (INR [])
          od
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

Theorem SmartMat_PMATCH:
  ∀mvar rows.
    SmartMat mvar rows =
      pmatch rows of
        [INR Pany, y] => y
      | _ => Mat (Var (Short mvar)) (MAP (build_match_row mvar) rows)
Proof
  CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘rows’ \\ simp [SmartMat_def]
  \\ rename [‘(h::t)’]
  \\ PairCases_on ‘h’ \\ rpt CASE_TAC \\ simp [SmartMat_def]
QED

Theorem ptree_Pattern_PMATCH:
  ∀p.
    ptree_Pattern p =
      do
        pp <- ptree_PPattern p;
        pmatch pp of
          Pp_record id fs => return $ [INL (id, fs)] (* record *)
        | _ =>
          do
            ps <- ppat_to_pat pp;
            return $ MAP INR ps
          od ++
          fail (unknown_loc, «Record patterns may only appear at the top level»)
      od
Proof
  CONV_TAC (DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ gen_tac \\ simp [ptree_Pattern_def]
QED
