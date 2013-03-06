open HolKernel Parse boolLib bossLib

open mmlGrammarTheory

open monadsyntax lcsymtacs

val _ = new_theory "mmlPtreeConversion"

val assert_def = Define`assert b = if b then SOME() else NONE`

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def"]

val mmap_def = Define`
  (mmap f [] = SOME []) /\
  (mmap f (h::t) = do
     v <- f h;
     vs <- mmap f t;
     SOME(v::vs)
   od)`

val mmap_CONG = store_thm(
  "mmap_CONG",
  ``∀l1 l2 f f'.
      l1 = l2 ∧ (∀x. MEM x l2 ⇒ f x = f' x) ⇒ mmap f l1 = mmap f l2``,
  Induct >> rw[]);
val _ = DefnBase.export_cong "mmap_CONG"





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

val destTyvar_def = Define`
  (destTyvar (Lf (TK (TyvarT s))) = SOME s) ∧
  (destTyvar _ = NONE)
`;
val destLf_def = Define`
  (destLf (Lf x) = SOME x) ∧ (destLf _ = NONE)
`;
val destTOK_def = Define`(destTOK (TOK t) = SOME t) ∧ (destTOK _ = NONE)`;
val destAlphaT_def = zDefine`destAlphaT t = some s. t = AlphaT s`

val ptree_TypeName_def = Define`
  ptree_TypeName ptree : (tvarN list # typeN) option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if nt = mkNT nTypeName then
        case args of
          [opt] => do opn <- ptree_Tyop opt ; SOME([], opn) od
        | [sym; opt] => do tyvn <- destTyvar sym ;
                           opn <- ptree_Tyop opt ;
                           SOME ([tyvn], opn)
                        od
        | [lp; tyvl; rp; opt] =>
          if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then do
              tyvnms <- ptree_linfix nTyVarList CommaT destTyvar tyvl;
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

val ptree_Dconstructor_def = Define`
  ptree_Dconstructor ast =
    case ast of
        Lf x => NONE
      | Nd nt args =>
        if nt = mkNT nDconstructor then
          case args of
              [] => NONE
            | Nd nt subargs::t =>
              if nt = mkNT nConstructorName then
                do
                  sym <- destLf (HD subargs);
                  tk <- destTOK sym;
                  cname <- destAlphaT tk;
                  types <- case t of
                               [] => SOME []
                             | [oft; startys] =>
                               if oft = Lf (TK OfT) then
                                 ptree_StarTypes T startys
                               else NONE
                             | _ => NONE;
                  SOME(cname, types)
                od
              else NONE
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

(*val ptree_TypeDec_def = Define`
  ptree_TypeDec ptree : ast_type_def option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      (case nt of
         mkNT nTypeDec => (case args of
                             [Lf (TK DatatypeT); pt0] => ptree_DtypeDecls pt0
                           | _ => NONE)
       | _ => NONE)
`*)

val ptree_Op_def = Define`
  ptree_Op (Lf _) = NONE ∧
  ptree_Op (Nd nt subs) =
    if nt = mkNT nMultOps then
      if subs = [Lf (TK (SymbolT "*"))] then SOME "*"
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

val ptree_Expr_def = Define`
  ptree_Expr (Lf _) = NONE ∧
  ptree_Expr (Nd nt subs) =
    case nt of
      mkNT nEbase =>
        (case subs of
           [Lf (TK LparT); Nd t s; Lf (TK RparT)] => ptree_Expr (Nd t s)
         | [Lf (TK (IntT i))] => SOME (Ast_Lit (IntLit i))
         | _ => NONE)
   | mkNT nEapp =>
       (case subs of
          [t1; t2] => do
            a1 <- ptree_Expr t1;
            a2 <- ptree_Expr t2;
            SOME(Ast_App a1 a2)
          od
        | [t] => ptree_Expr t
        | _ => NONE)
   | mkNT nEmult =>
       (case subs of
          [t1; opt; t2] => do (* s will be *, /, div, or mod *)
            a1 <- ptree_Expr t1;
            a_op <- ptree_Op opt;
            a2 <- ptree_Expr t2;
            SOME(Ast_App (Ast_App (Ast_Var a_op) a1) a2)
          od
        | [t] => ptree_Expr t
        | _ => NONE)
   | _ => NONE
`;

val ast = ``Nd (mkNT nEmult) [
              Nd (mkNT nEmult) [
                Nd (mkNT nEmult) [
                  Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 3))]]
                ];
                Nd (mkNT nMultOps) [Lf (TK (SymbolT "*"))];
                Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 4))]]
              ];
              Nd (mkNT nMultOps) [Lf (TK (SymbolT "*"))];
              Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 5))]]
            ]``

val parse_result = EVAL ``ptree_Expr ^ast``;

(* would use EVAL for this too, but it fails to turn (∃i. F) into F, and can't
   be primed with that as a rewrite rule.

   And if you do

     val _ = computeLib.add_conv (existential, 1, REWR_CONV EXISTS_SIMP) computeLib.the_compset
     val _ = computeLib.set_skip computeLib.the_compset ``COND`` (SOME 1)

   you get a situation wherein EVAL isn't idempotent.  Yikes.
*)


val _ = export_theory()
