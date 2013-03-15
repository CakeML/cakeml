open HolKernel Parse boolLib bossLib

open mmlGrammarTheory

open monadsyntax lcsymtacs

val _ = new_theory "mmlPtreeConversion"






(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

(* Use of parsing-heap means that this theory is secretly a descendent of
   pegexecTheory, where 'nt' is a constructor name.

   This is a disgusting failing of our theory mechanism.  *)
val _ = hide "nt"

val ptree_Tyop_def = Define`
  ptree_Tyop ptree =
    case ptree of
      Lf _ => NONE
    | Nd (mkNT nTyOp) [Lf (TK (AlphaT s))] => SOME s
    | Nd (mkNT nTyOp) [Lf (TK (SymbolT s))] => SOME s
    | _ => NONE
`;

val ptree_linfix_def = Define`
  ptree_linfix topnt opn elnt (pt : mlptree) =
    case pt of
        Lf _ => NONE
      | Nd nt args =>
        if nt = mkNT topnt then
          case args of
              [pt] => do e <- elnt pt; SOME [e] od
            | [top; op_pt; pt] => do
                assert(op_pt = Lf (TK opn));
                front <- ptree_linfix topnt opn elnt top;
                last <- elnt pt;
                SOME(front ++ [last])
              od
            | _ => NONE
        else NONE
`

val ptree_Type_def = Define`
  (ptree_Type ptree : ast_t option =
    case ptree of
      Nd nt args =>
      (case nt of
         mkNT nType => (case args of
                         [dt] => ptree_Type dt
                       | [dt;Lf(TK ArrowT);rt] => do
                           dty <- ptree_Type dt;
                           rty <- ptree_Type rt;
                           SOME(Ast_Tfn dty rty)
                         od
                       | _ => NONE)
       | mkNT nDType => (case args of
                           [Lf (TK (TyvarT s))] => SOME (Ast_Tvar s)
                         | [opn] => do
                             opname <- ptree_Tyop opn;
                             SOME(Ast_Tapp [] opname)
                           od
                         | [dt; opn] => do
                             dty <- ptree_Type dt;
                             opname <- ptree_Tyop opn;
                             SOME(Ast_Tapp [dty] opname)
                           od
                         | [Lf (TK LparT); t; Lf (TK RparT)] => ptree_Type t
                         | [Lf (TK LparT); tl; Lf (TK RparT); opn] => do
                             tylist <- ptree_Typelist tl;
                             opname <- ptree_Tyop opn;
                             SOME(Ast_Tapp tylist opname)
                           od
                         | _ => NONE)
       | _ => NONE)
    | _ => NONE) ∧
  (ptree_Typelist ptree : ast_t list option =
     case ptree of
       Lf _ => NONE
     | Nd nt args =>
       (case nt of
          mkNT nTypeList => (case args of
                               [dt] => do
                                  ty <- ptree_Type dt;
                                  SOME[ty]
                               od
                             | [dt; Lf (TK CommaT); tl'] => do
                                 ty <- ptree_Type dt;
                                 tylist <- ptree_Typelist tl';
                                 SOME(ty::tylist)
                               od
                             | _ => NONE)
         | _ => NONE))
`;

val ptree_TypeName_def = Define`
  ptree_TypeName ptree : (tvarN list # typeN) option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if nt = mkNT nTypeName then
        case args of
          [opt] => do opn <- ptree_Tyop opt ; SOME([], opn) od
        | [sym; opt] => do tyvn <- destTyvarPT sym ;
                           opn <- ptree_Tyop opt ;
                           SOME ([tyvn], opn)
                        od
        | [lp; tyvl; rp; opt] =>
          if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then do
              tyvnms <- ptree_linfix nTyVarList CommaT destTyvarPT tyvl;
              opn <- ptree_Tyop opt;
              SOME(tyvnms, opn)
            od
          else NONE
        | _ => NONE
      else NONE
`;

val ptree_StarTypes_def = Define`
  ptree_StarTypes p pt : ast_t list option =
    case pt of
        Lf _ => NONE
      | Nd nt args =>
        if p ∧ (nt = mkNT nStarTypesP) then
          case args of
              [pt0] => ptree_StarTypes F pt0
            | [lp; pt0; rp] => do assert (lp = Lf (TK LparT)) ;
                                  assert (rp = Lf (TK RparT)) ;
                                  ptree_StarTypes F pt0
                               od
            | _ => NONE
        else if ¬p ∧ (nt = mkNT nStarTypes) then
          case args of
              [pt0] => do ty <- ptree_Type pt0; SOME([ty]) od
            | [pt1; star; pt2] => do
                 assert(star = Lf (TK StarT));
                 pfx <- ptree_StarTypes F pt1;
                 ty <- ptree_Type pt2;
                 SOME(list$APPEND pfx [ty: ast_t])
              od
        else NONE
`;

val ptree_ConstructorName_def = Define`
  ptree_ConstructorName ast =
    case ast of
        Lf _ => NONE
      | Nd nt args =>
        if nt = mkNT nConstructorName then
          case args of
              [Lf (TOK t)] => destAlphaT t
            | _ => NONE
        else NONE
`

val ptree_Dconstructor_def = Define`
  ptree_Dconstructor ast =
    case ast of
        Lf x => NONE
      | Nd nt args =>
        if nt = mkNT nDconstructor then
          case args of
              [] => NONE
            | t::ts =>
              do
                 cname <- ptree_ConstructorName t;
                 types <- case ts of
                               [] => SOME []
                             | [oft; startys] =>
                               if oft = Lf (TK OfT) then
                                 ptree_StarTypes T startys
                               else NONE
                             | _ => NONE;
                 SOME(cname, types)
              od
            | _ :: t => NONE
        else NONE
`;

val ptree_DtypeDecl_def = Define`
  ptree_DtypeDecl (pt : mlptree) =
    case pt of
        Lf _ => NONE
      | Nd nt args =>
        if nt = mkNT nDtypeDecl then
          case args of
              [tynm_pt; eqt; dtc_pt] => do
                assert(eqt = Lf (TK EqualsT));
                tynm <- ptree_TypeName tynm_pt;
                dtc <- ptree_linfix nDtypeCons BarT ptree_Dconstructor dtc_pt;
                SOME(FST tynm,SND tynm,dtc)
              od
            | _ => NONE
        else NONE
`;

val ptree_TypeDec_def = Define`
  ptree_TypeDec ptree : ast_type_def option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if nt = mkNT nTypeDec then
        case args of
            [datatype_pt; pt] => do
              assert(datatype_pt = Lf (TK DatatypeT));
              ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt
            od
          | _ => NONE
      else NONE`;

val ptree_Op_def = Define`
  ptree_Op (Lf _) = NONE ∧
  ptree_Op (Nd nt subs) =
    if nt = mkNT nMultOps then
      if subs = [Lf (TK StarT)] then SOME "*"
      else if subs = [Lf (TK (SymbolT "/"))] then SOME "/"
      else if subs = [Lf (TK (AlphaT "mod"))] then SOME "mod"
      else if subs = [Lf (TK (AlphaT "div"))] then SOME "div"
      else NONE
    else if nt = mkNT nAddOps then
      if subs = [Lf (TK (SymbolT "+"))] then SOME "+"
      else if subs = [Lf (TK (SymbolT "-"))] then SOME "-"
      else NONE
    else NONE
`;

val OPTION_CHOICE_def = Define`
  OPTION_CHOICE (SOME y) x = SOME y ∧
  OPTION_CHOICE NONE x = x
`
val _ = overload_on ("++", ``OPTION_CHOICE``)

val ptree_V_def = Define`
  ptree_V (Lf _) = NONE ∧
  ptree_V (Nd nt subs) =
    if nt = mkNT nV then
      case subs of
          [Lf (TOK t)] =>
          do s <- (destAlphaT t ++ destSymbolT t);
             SOME (Ast_Var s)
          od
        | _ => NONE
    else NONE
`;

val updAst_Conname_def = Define`
  updAst_Conname cname (Ast_Con _ args) = SOME (Ast_Con cname args) ∧
  updAst_Conname _ _ = NONE
`

val backAppCon_def = Define`
  backAppCon (Ast_Con x args) b = SOME (Ast_Con x (args ++ [b])) ∧
  backAppCon _ _ = NONE
`

val ptree_Expr_def = Define`
  ptree_Expr ent (Lf _) = NONE ∧
  ptree_Expr ent (Nd nt subs) =
    if mkNT ent = nt then
      if nt = mkNT nEbase then
        case subs of
            [lpart; pt; rpart] =>
            if lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT) then
              ptree_Expr nE pt
            else NONE
          | [single] =>
              do
                lf <- destLf single;
                t <- destTOK lf;
                i <- destIntT t ;
                SOME (Ast_Lit (IntLit i))
              od ++
              ptree_V single ++
              do cname <- ptree_ConstructorName single;
                 SOME (Ast_Con cname [])
              od
          | _ => NONE
      else if nt = mkNT nEapp then
        case subs of
            [t1; t2] => do
                          a1 <- ptree_Expr nEapp t1;
                          a2 <- ptree_Expr nEbase t2;
                          SOME(Ast_App a1 a2)
                        od ++
                        do
                          cname <- ptree_ConstructorName t1;
                          cargs <- ptree_Expr nEtuple t2;
                          updAst_Conname cname cargs
                        od
          | [t] => ptree_Expr nEbase t
          | _ => NONE
      else if nt = mkNT nEtuple then
        case subs of
            [lpart; el2; rpart] =>
            if lpart = Lf (TOK LparT) ∧ rpart = Lf (TOK RparT) then
              ptree_Expr nElist2 el2
            else NONE
          | _ => NONE
      else if nt = mkNT nElist2 then
        case subs of
            [el1; ct; e] =>
            if ct = Lf (TOK CommaT) then
              do
                front <- ptree_Expr nElist1 el1;
                back <- ptree_Expr nE e;
                backAppCon front back
              od
            else NONE
          | _ => NONE
      else if nt = mkNT nElist1 then
        case subs of
            [sing] => do e <- ptree_Expr nE sing; SOME(Ast_Con "" [e]) od
          | [el1;ct;e] =>
            if ct = Lf (TOK CommaT) then
              do
                front <- ptree_Expr nElist1 el1 ;
                back <- ptree_Expr nE e;
                backAppCon front back
              od
            else NONE
      else if nt = mkNT nEmult then
        case subs of
          [t1; opt; t2] => do (* s will be *, /, div, or mod *)
            a1 <- ptree_Expr nEmult t1;
            a_op <- ptree_Op opt;
            a2 <- ptree_Expr nEapp t2;
            SOME(Ast_App (Ast_App (Ast_Var a_op) a1) a2)
          od
        | [t] => ptree_Expr nEapp t
        | _ => NONE
      else NONE
    else NONE
`;

val _ = export_theory()
