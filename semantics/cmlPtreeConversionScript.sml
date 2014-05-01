open HolKernel Parse boolLib bossLib

open gramTheory tokenUtilsTheory

open monadsyntax lcsymtacs

local open elabTheory in end (* for "ast" type *)

val _ = new_theory "cmlPtreeConversion"

(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

(* Use of parsing-heap means that this theory is secretly a descendent of
   pegexecTheory, where 'nt' is a constructor name.

   This is a disgusting failing of our theory mechanism.  *)
val _ = hide "nt"


(* ----------------------------------------------------------------------
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------- *)

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)

val oHD_def = Define`oHD l = case l of [] => NONE | h::_ => SOME h`
val safeTL_def = Define`safeTL [] = [] ∧ safeTL (h::t) = t`

val ptree_UQTyop_def = Define`
  ptree_UQTyop (Lf _) = NONE ∧
  ptree_UQTyop (Nd nt args) =
    if nt <> mkNT nUQTyOp then NONE
    else
      case args of
          [pt] =>
          do
            lf <- destLf pt;
            tk <- destTOK lf;
            destSymbolT tk ++ destAlphaT tk
          od
        | _ => NONE
`;

val ptree_TyvarN_def = Define`
  ptree_TyvarN (Lf _) = NONE ∧
  ptree_TyvarN (Nd nt args) =
    if nt <> mkNT nTyvarN then NONE
    else
      case args of
          [tyv] => destTyvarPT tyv
        | _ => NONE
`;

val _ = temp_overload_on ("'", ``λf a. OPTION_BIND a f``);

val ptree_Tyop_def = Define`
  ptree_Tyop (Lf _) = NONE ∧
  ptree_Tyop (Nd nt args) =
    if nt <> mkNT nTyOp then NONE
    else
      case args of
          [pt] =>
          do
            (str,s) <- destLongidT ' (destTOK ' (destLf pt));
            SOME(Long str s)
          od ++
          do
            nm <- ptree_UQTyop pt;
            SOME(Short nm)
          od
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

val tuplify_def = Define`
  tuplify [] = NONE ∧
  tuplify [ty] = SOME ty ∧
  tuplify tys = SOME(Ast_Tapp tys NONE)
`

val ptree_Type_def = Define`
  (ptree_Type nt (Lf _) : ast_t option = NONE) ∧
  (ptree_Type nm (Nd nt args) =
     if nt <> mkNT nm then NONE
     else if nm = nType then
       case args of
          [dt] =>
          do
            tys <- ptree_PType dt;
            tuplify tys
          od
        | [dt;arrowt;rt] =>
              do
                assert(arrowt = Lf (TOK ArrowT));
                dtys <- ptree_PType dt;
                dty <- tuplify dtys;
                rty <- ptree_Type nType rt;
                SOME(Ast_Tfn dty rty)
              od
            | _ => NONE
     else if nm = nDType then
       case args of
           [pt] => ptree_Type nTbase pt
         | [dt; opn] => do
                          dty <- ptree_Type nDType dt;
                          opname <- ptree_Tyop opn;
                          SOME(Ast_Tapp [dty] (SOME opname))
                        od
         | _ => NONE
     else if nm = nTbase then
       case args of
           [pt] =>
                OPTION_MAP Ast_Tvar (destTyvarPT pt) ++
                OPTION_MAP (Ast_Tapp [] o SOME) (ptree_Tyop pt)
         | [lpart; t; rpart] =>
              do
                assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
                ptree_Type nType t
              od
         | [lpart; tl; rpart; opn] =>
           do
              assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
              tylist <- ptree_Typelist2 tl;
              opname <- ptree_Tyop opn;
              SOME(Ast_Tapp tylist (SOME opname))
           od
         | _ => NONE
     else NONE) ∧
  (ptree_Typelist2 ptree : ast_t list option =
     case ptree of
       Lf _ => NONE
     | Nd nt args =>
       if nt <> mkNT nTypeList2 then NONE
       else
         case args of
           | [dt; commat; tl'] =>
             do
               assert(commat = Lf (TK CommaT));
               ty <- ptree_Type nType dt;
               tylist <- ptree_TypeList1 tl';
               SOME(ty::tylist)
             od
           | _ => NONE) ∧
  (ptree_TypeList1 ptree : ast_t list option =
    case ptree of
        Lf _ => NONE
      | Nd nt args =>
        if nt <> mkNT nTypeList1 then NONE
        else
          case args of
              [dt] =>
              do
                ty <- ptree_Type nType dt;
                SOME([ty])
              od
            | [dt; commat; tl] =>
              do
                assert(commat = Lf (TK CommaT));
                ty <- ptree_Type nType dt;
                tl <- ptree_TypeList1 tl;
                SOME(ty::tl)
              od
            | _ => NONE) ∧
  (ptree_PType ptree : ast_t list option =
     case ptree of
         Lf _ => NONE
       | Nd nt args =>
         if nt <> mkNT nPType then NONE
         else
           case args of
               [dty_pt] =>
               do
                 dty <- ptree_Type nDType dty_pt;
                 SOME [dty]
               od
             | [dty_pt; st; pty_pt] =>
               do
                 assert (st = Lf (TK StarT));
                 dty <- ptree_Type nDType dty_pt;
                 ptys <- ptree_PType pty_pt;
                 SOME(dty::ptys)
               od
             | _ => NONE)
`;

val ptree_TypeName_def = Define`
  ptree_TypeName ptree : (tvarN list # typeN) option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if nt = mkNT nTypeName then
        case args of
          [opt] => do opn <- ptree_UQTyop opt ; SOME([], opn) od
        | [sym; opt] => do tyvn <- destTyvarPT sym ;
                           opn <- ptree_UQTyop opt ;
                           SOME ([tyvn], opn)
                        od
        | [lp; tyvl; rp; opt] =>
          if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then do
              tyvnms <- ptree_linfix nTyVarList CommaT ptree_TyvarN tyvl;
              opn <- ptree_UQTyop opt;
              SOME(tyvnms, opn)
            od
          else NONE
        | _ => NONE
      else NONE
`;

val ptree_UQConstructorName_def = Define`
  ptree_UQConstructorName (Lf _) = NONE ∧
  ptree_UQConstructorName (Nd nm args) =
    if nm <> mkNT nUQConstructorName then NONE
    else
      case args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
`

val ptree_ConstructorName_def = Define`
  ptree_ConstructorName ast =
    case ast of
        Lf _ => NONE
      | Nd nt args =>
        if nt <> mkNT nConstructorName then NONE
        else
          case args of
              [pt] =>
              do
                s <- ptree_UQConstructorName pt;
                SOME (Short s)
              od ++
              do
                (str,s) <- destLongidT ' (destTOK ' (destLf pt));
                SOME (Long str s)
              od
            | _ => NONE
`

val detuplify_def = Define`
  detuplify (Ast_Tapp args NONE) = args ∧
  detuplify ty = [ty]
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
                 cname <- ptree_UQConstructorName t;
                 types <- case ts of
                               [] => SOME []
                             | [oft; ty_pt] =>
                               if oft = Lf (TK OfT) then
                                 OPTION_MAP detuplify (ptree_Type nType ty_pt)
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
      if subs = [Lf (TK StarT)] then SOME (Short "*")
      else if subs = [Lf (TK (SymbolT "/"))] then SOME (Short "/")
      else if subs = [Lf (TK (AlphaT "mod"))] then SOME (Short "mod")
      else if subs = [Lf (TK (AlphaT "div"))] then SOME (Short "div")
      else NONE
    else if nt = mkNT nAddOps then
      if subs = [Lf (TK (SymbolT "+"))] then SOME (Short "+")
      else if subs = [Lf (TK (SymbolT "-"))] then SOME (Short "-")
      else NONE
    else if nt = mkNT nListOps then
      if subs = [Lf (TK (SymbolT "::"))] then SOME (Short "::")
      else if subs = [Lf (TK (SymbolT "@"))] then SOME (Short "@")
      else NONE
    else if nt = mkNT nRelOps then
      case subs of
          [pt] =>
          do
            s <- destSymbolT ' (destTOK ' (destLf pt));
            SOME (Short s)
          od ++
          do
            assert(pt = Lf (TK EqualsT));
            SOME(Short "=")
          od
        | _ => NONE
    else if nt = mkNT nCompOps then
      if subs = [Lf (TK (SymbolT ":="))] then SOME (Short ":=")
      else if subs = [Lf (TK (AlphaT "o"))] then SOME (Short "o")
      else NONE
    else NONE
`;

val ptree_V_def = Define`
  ptree_V (Lf _) = NONE ∧
  ptree_V (Nd nt subs) =
    if nt = mkNT nV then
      case subs of
          [Lf (TOK t)] => destAlphaT t ++ destSymbolT t
        | _ => NONE
    else NONE
`;

val ptree_Vlist1_def = Define`
  ptree_Vlist1 (Lf _) = NONE ∧
  ptree_Vlist1 (Nd nm subs) =
    if nm <> mkNT nVlist1 then NONE
    else
      case subs of
          [v_pt] => do v <- ptree_V v_pt; SOME [v] od
        | [v_pt; vs_pt] =>
          do
            v <- ptree_V v_pt;
            vs <- ptree_Vlist1 vs_pt;
            SOME(v::vs)
          od
        | _ => NONE
`

val ptree_FQV_def = Define`
  ptree_FQV (Lf _) = NONE ∧
  ptree_FQV (Nd nt args) =
    if nt <> mkNT nFQV then NONE
    else
      case args of
          [pt] => OPTION_MAP Short (ptree_V pt) ++
                  do
                    (str,s) <- destLongidT ' (destTOK ' (destLf pt));
                    SOME(Long str s)
                  od
        | _ => NONE
`

(* in other words constructors never take tuples as arguments, only ever
   lists of arguments *)
val mkPatApp_def = Define`
  mkPatApp cn p =
    if cn = Short "ref" then Pref p
    else
      case p of
          Pcon NONE pl => Pcon (SOME cn) pl
        | _ => Pcon (SOME cn) [p]
`;

val ptree_Pattern_def = Define`
  (ptree_Pattern nt (Lf _) = NONE) ∧
  (ptree_Pattern nt (Nd nm args) =
    if mkNT nt <> nm then NONE
    else if nm = mkNT nPbase then
      case args of
          [vic] =>
          ptree_Pattern nPtuple vic ++
          do
             cname <- ptree_ConstructorName vic;
             if cname = Short "true" then
               SOME(Plit (Bool T))
             else if cname = Short "false" then
               SOME(Plit (Bool F))
             else
               SOME(Pcon (SOME cname) [])
          od ++
          do
             vname <- ptree_V vic;
             SOME(Pvar vname)
          od ++
          do
            lf <- destLf vic;
            t <- destTOK lf;
            i <- destIntT t ;
            SOME (Plit (IntLit i))
          od ++
          do
            lf <- destLf vic;
            t <- destTOK lf;
            s <- destStringT t ;
            SOME (Plit (StrLit s))
          od ++
          if vic = Lf (TOK UnderbarT) then SOME (Pvar "_")
          else NONE
        | [lb; rb] =>
          if lb = Lf (TK LbrackT) ∧ rb = Lf (TK RbrackT) then
            SOME(Pcon (SOME (Short "nil")) [])
          else NONE
        | [lb; plistpt; rb] =>
          do
            assert (lb = Lf (TK LbrackT) ∧ rb = Lf (TK RbrackT));
            plist <- ptree_Plist plistpt;
            SOME (FOLDR (λp a. Pcon (SOME (Short "::")) [p; a])
                        (Pcon (SOME (Short "nil")) [])
                        plist)
          od
        | _ => NONE
    else if nm = mkNT nPapp then
      case args of
          [pb] => ptree_Pattern nPbase pb
        | [cnm; ppt] =>
          do
            cn <- ptree_ConstructorName cnm;
            p <- ptree_Pattern nPbase ppt;
            SOME(mkPatApp cn p)
          od
        | _ => NONE
    else if nm = mkNT nPattern then
      case args of
          [papt] => ptree_Pattern nPapp papt
        | [papt; cons_t; pattpt] =>
          do
            assert (cons_t = Lf (TK (SymbolT "::")));
            pa <- ptree_Pattern nPapp papt;
            patt <- ptree_Pattern nPattern pattpt;
            SOME(Pcon (SOME (Short "::")) [pa; patt])
          od
        | _ => NONE
    else if nm = mkNT nPtuple then
      case args of
          [lp; rp] => if lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT) then
                        SOME (Plit Unit)
                      else NONE
        | [lp; pl_pt; rp] =>
          do
            assert (lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT));
            pl <- ptree_Plist pl_pt;
            case pl of
                [] => NONE
              | [p] => SOME p
              | _ => SOME (Pcon NONE pl)
          od
        | _ => NONE
    else NONE) ∧

  (ptree_Plist (Lf _) = NONE) ∧
  (ptree_Plist (Nd nm args) =
     if nm <> mkNT nPatternList then NONE
     else
       case args of
           [p_pt] =>
           do
             p <- ptree_Pattern nPattern p_pt;
             SOME [p]
           od
         | [p; ct; pl] =>
           do
             assert (ct = Lf (TOK CommaT));
             hdpat <- ptree_Pattern nPattern p;
             tlpats <- ptree_Plist pl;
             SOME(hdpat::tlpats)
           od
         | _ => NONE)
`;

val Eseq_encode_def = Define`
  (Eseq_encode [] = NONE) ∧
  (Eseq_encode [e] = SOME e) ∧
  (Eseq_encode (e::es) =
   do
     body <- Eseq_encode es;
     SOME(Let NONE e body)
   od)
`

val mkAst_App_def = Define`
  mkAst_App a1 a2 =
   case a1 of
       Con (SOME (Short "ref")) [] => App Opapp [Var (Short "ref"); a2]
     | Con s [] =>
       (case a2 of
            Con NONE tuple => Con s tuple
          | _ => Con s [a2])
     | _ => App Opapp [a1; a2]
`
val ptree_Expr_def = Define`
  ptree_Expr ent (Lf _) = NONE ∧
  ptree_Expr ent (Nd nt subs) =
    (if mkNT ent = nt then
      if nt = mkNT nEbase then
        case subs of
            [lpart; pt; rpart] =>
            do
              assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
              eseq <- ptree_Eseq pt;
              Eseq_encode eseq
            od ++
            do
              assert(lpart = Lf (TK LbrackT) ∧ rpart = Lf (TK RbrackT));
              elist <- ptree_Exprlist nElist1 pt;
              SOME(FOLDR (λe acc. Con (SOME (Short "::")) [e; acc])
                         (Con (SOME (Short "nil")) [])
                         elist)
            od
          | [single] =>
              do
                lf <- destLf single;
                t <- destTOK lf;
                i <- destIntT t ;
                SOME (Lit (IntLit i))
              od ++
              do
                lf <- destLf single;
                t <- destTOK lf;
                s <- destStringT t;
                SOME (Lit (StrLit s))
              od ++
              do
                s <- ptree_FQV single;
                SOME (Var s)
              od ++
              do cname <- ptree_ConstructorName single;
                 if cname = Short "true" then
                   SOME (Lit (Bool T))
                 else if cname = Short "false" then
                   SOME (Lit (Bool F))
                 else
                   SOME (Con (SOME cname) [])
              od ++
              ptree_Expr nEtuple single
          | [lp;rp] => if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then
                         SOME (Lit Unit)
                       else if lp = Lf (TK LbrackT) ∧ rp = Lf (TK RbrackT) then
                         SOME (Con (SOME (Short "nil")) [])
                       else NONE
          | [lett;letdecs_pt;intok;ept;endt] =>
            do
              assert(lett = Lf (TOK LetT) ∧ intok = Lf (TOK InT) ∧
                     endt = Lf (TOK EndT));
              letdecs <- ptree_LetDecs letdecs_pt;
              eseq <- ptree_Eseq ept;
              e <- Eseq_encode eseq;
              SOME(FOLDR (λdf acc. case df of
                                       INL (v,e0) => Let (SOME v) e0 acc
                                     | INR fds => Letrec fds acc)
                         e
                         letdecs)
            od
          | _ => NONE
      else if nt = mkNT nEapp then
        case subs of
            [t1; t2] => do
                          a1 <- ptree_Expr nEapp t1;
                          a2 <- ptree_Expr nEbase t2;
                          SOME(mkAst_App a1 a2)
                        od
          | [t] => ptree_Expr nEbase t
          | _ => NONE
      else if nt = mkNT nEtuple then
        case subs of
            [lpart; el2; rpart] =>
            do
              assert (lpart = Lf (TOK LparT) ∧ rpart = Lf (TOK RparT));
              es <- ptree_Exprlist nElist2 el2;
              SOME(Con NONE es)
            od
          | _ => NONE
      else if nt = mkNT nEmult then
        case subs of
          [t1; opt; t2] => do (* s will be *, /, div, or mod *)
            a1 <- ptree_Expr nEmult t1;
            a_op <- ptree_Op opt;
            a2 <- ptree_Expr nEapp t2;
            SOME(App Opapp [App Opapp [Var a_op; a1]; a2])
          od
        | [t] => ptree_Expr nEapp t
        | _ => NONE
      else if nt = mkNT nEadd then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nEmult t2;
              SOME (App Opapp [App Opapp [Var a_op; a1]; a2])
            od
          | [t] => ptree_Expr nEmult t
          | _ => NONE
      else if nt = mkNT nElistop then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nElistop t2;
              SOME (if a_op = Short "::" then
                      Con (SOME (Short "::")) [a1;a2]
                    else App Opapp [App Opapp [Var a_op; a1]; a2])
            od
          | [t] => ptree_Expr nEadd t
          | _ => NONE
      else if nt = mkNT nErel then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nErel t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nElistop t2;
              SOME (App Opapp [App Opapp [Var a_op; a1]; a2])
            od
          | [t] => ptree_Expr nElistop t
          | _ => NONE
      else if nt = mkNT nEcomp then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEcomp t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nErel t2;
              SOME(App Opapp [App Opapp [Var a_op; a1]; a2])
            od
          | [t] => ptree_Expr nErel t
          | _ => NONE
      else if nt = mkNT nEbefore then
        case subs of
          [t1;opt;t2] => do
            assert(opt = Lf(TOK(AlphaT "before")));
            a1 <- ptree_Expr nEbefore t1;
            a2 <- ptree_Expr nEcomp t2;
            SOME(App Opapp [App Opapp [Var (Short "before"); a1]; a2])
          od
        | [t] => ptree_Expr nEcomp t
        | _ => NONE
      else if nt = mkNT nEtyped then
        case subs of
          [t1;colon;t2] => do
            assert(colon = Lf (TOK ColonT));
            t1 <- ptree_Expr nEbefore t1;
            t2 <- ptree_Type nType t2;
            SOME t1 (* FIXME *)
          od
        | [t] => ptree_Expr nEbefore t
        | _ => NONE
      else if nt = mkNT nElogicAND then
        case subs of
            [t1;andt;t2] => do
              assert(andt = Lf (TOK AndalsoT));
              a1 <- ptree_Expr nElogicAND t1;
              a2 <- ptree_Expr nEtyped t2;
              SOME(Log And a1 a2)
            od
          | [t] => ptree_Expr nEtyped t
          | _ => NONE
      else if nt = mkNT nElogicOR then
        case subs of
            [t1;ort;t2] => do
              assert(ort = Lf (TOK OrelseT));
              a1 <- ptree_Expr nElogicOR t1;
              a2 <- ptree_Expr nElogicAND t2;
              SOME (Log Or a1 a2)
            od
          | [t] => ptree_Expr nElogicAND t
          | _ => NONE
      else if nt = mkNT nEhandle then
        case subs of
            [pt] => ptree_Expr nElogicOR pt
          | [e1pt; handlet; ent] =>
            do
              assert(handlet = Lf (TOK HandleT));
              e <- ptree_Expr nElogicOR e1pt;
              pes <- ptree_PEs ent;
              SOME(Handle e pes)
            od
          | _ => NONE
      else if nt = mkNT nE then
        case subs of
          | [t] => ptree_Expr nEhandle t
          | [raiset; ept] =>
            do
              assert(raiset = Lf (TOK RaiseT));
              e <- ptree_Expr nE ept;
              SOME(Raise e)
            od
          | [fnt; vnt; arrowt; ent] =>
            do
              assert (fnt = Lf (TOK FnT) ∧ arrowt = Lf (TOK DarrowT));
              v <- ptree_V vnt;
              e <- ptree_Expr nE ent;
              SOME(Fun v e)
            od ++ do
              assert (fnt = Lf (TOK CaseT) ∧ arrowt = Lf (TOK OfT));
              e <- ptree_Expr nE vnt;
              pes <- ptree_PEs ent;
              SOME(Mat e pes)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(ift = Lf (TOK IfT) ∧ thent = Lf (TOK ThenT) ∧
                     elset = Lf (TOK ElseT));
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE ee;
              SOME(If a1 a2 a3)
            od
          | _ => NONE
      else if nt = mkNT nE' then
        case subs of
          | [t] => ptree_Expr nElogicOR t
          | [raiset; ept] =>
            do
              assert(raiset = Lf (TOK RaiseT));
              e <- ptree_Expr nE' ept;
              SOME(Raise e)
            od
          | [fnt; vnt; arrowt; ent] =>
            do
              assert (fnt = Lf (TOK FnT) ∧ arrowt = Lf (TOK DarrowT));
              v <- ptree_V vnt;
              e <- ptree_Expr nE' ent;
              SOME(Fun v e)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(ift = Lf (TOK IfT) ∧ thent = Lf (TOK ThenT) ∧
                     elset = Lf (TOK ElseT));
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE' ee;
              SOME(If a1 a2 a3)
            od
          | _ => NONE
      else NONE
    else NONE) ∧
  (ptree_Exprlist nm ast =
     case ast of
         Lf _ => NONE
       | Nd nt subs =>
         if nt = mkNT nElist1 then
           case subs of
               [sing] => do e <- ptree_Expr nE sing; SOME [e] od
             | [e;ct;el1] =>
               do
                 assert(ct = Lf (TOK CommaT));
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 SOME(front::back)
               od
             | _ => NONE
         else if nt = mkNT nElist2 then
           case subs of
               [e;ct;el1] =>
               do
                 assert(ct = Lf (TOK CommaT));
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 SOME(front::back)
               od
             | _ => NONE
         else NONE) ∧
  ptree_AndFDecls ast =
    (case ast of
        Lf _ => NONE
      | Nd nt subs =>
        if nt = mkNT nAndFDecls then
          case subs of
              [single] => do fdec <- ptree_FDecl single; SOME ([fdec]) od
            | [fdecspt;andt;fdecpt] =>
              do
                assert(andt = Lf (TOK AndT));
                fdecs <- ptree_AndFDecls fdecspt;
                fdec <- ptree_FDecl fdecpt;
                SOME(fdecs ++ [fdec])
              od
            | _ => NONE
        else NONE) ∧
  (ptree_FDecl ast =
    case ast of
        Lf _ => NONE
      | Nd nt subs =>
        if nt = mkNT nFDecl then
          case subs of
              [fname_pt; vnames_pt; eqt; body_pt] =>
              do
                assert(eqt = Lf (TOK EqualsT));
                fname <- ptree_V fname_pt;
                vs <- ptree_Vlist1 vnames_pt;
                v1 <- oHD vs;
                body0 <- ptree_Expr nE body_pt;
                SOME(fname,v1,FOLDR Fun body0 (safeTL vs))
              od
            | _ => NONE
        else NONE) ∧
  (ptree_LetDecs ptree =
    case ptree of
        Lf _ => NONE
      | Nd nt args =>
        if nt <> mkNT nLetDecs then NONE
        else
          case args of
              [] => SOME []
            | [ld_pt; lds_pt] =>
              if ld_pt = Lf (TOK SemicolonT) then ptree_LetDecs lds_pt
              else
                do
                  ld <- ptree_LetDec ld_pt;
                  lds <- ptree_LetDecs lds_pt;
                  SOME (ld::lds)
                od
            | _ => NONE) ∧
  (ptree_LetDec ptree =
    case ptree of
        Lf _ => NONE
      | Nd nt args =>
        if nt <> mkNT nLetDec then NONE
        else
          case args of
              [funtok; andfdecls_pt] =>
              do
                assert (funtok = Lf (TOK FunT));
                fds <- ptree_AndFDecls andfdecls_pt;
                SOME (INR fds)
              od
            | [valtok; v_pt; eqtok; e_pt] =>
              do
                assert(valtok = Lf (TOK ValT) ∧ eqtok = Lf (TOK EqualsT));
                v <- ptree_V v_pt;
                e <- ptree_Expr nE e_pt;
                SOME (INL(v,e))
              od
            | _ => NONE) ∧
  (ptree_PEs (Lf _) = NONE) ∧
  (ptree_PEs (Nd nt args) =
    if nt <> mkNT nPEs then NONE
    else
      case args of
          [single] =>
          do
            pe <- ptree_PE single;
            SOME [pe]
          od
        | [pe'_pt; bartok; pes_pt] =>
          do
            assert(bartok = Lf (TOK BarT));
            pes <- ptree_PEs pes_pt;
            pe <- ptree_PE' pe'_pt;
            SOME(pe::pes)
          od
        | _ => NONE) ∧
  (ptree_PE (Lf _) = NONE) ∧
  (ptree_PE (Nd nt args) =
     if nt <> mkNT nPE then NONE
     else
       case args of
           [p_pt; arrow; e_pt] =>
           do
             assert(arrow = Lf (TOK DarrowT));
             p <- ptree_Pattern nPattern p_pt;
             e <- ptree_Expr nE e_pt;
             SOME(p,e)
           od
         | _ => NONE) ∧
  (ptree_PE' (Lf _) = NONE) ∧
  (ptree_PE' (Nd nt args) =
     if nt <> mkNT nPE' then NONE
     else
       case args of
           [p_pt; arrow; e'_pt] =>
           do
             assert(arrow = Lf (TOK DarrowT));
             p <- ptree_Pattern nPattern p_pt;
             e <- ptree_Expr nE' e'_pt;
             SOME(p,e)
           od
         | _ => NONE) ∧
  (ptree_Eseq (Lf _) = NONE) ∧
  (ptree_Eseq (Nd nt args) =
    if nt <> mkNT nEseq then NONE
    else
      case args of
          [single] =>
          do
            e <- ptree_Expr nE single;
            SOME[e]
          od
        | [e_pt; semi; seq_pt] =>
          do
            assert(semi = Lf (TOK SemicolonT));
            e <- ptree_Expr nE e_pt;
            seq <- ptree_Eseq seq_pt;
            SOME(e::seq)
          od
        | _ => NONE)
`;


val ptree_Decl_def = Define`
  ptree_Decl pt : ast_dec option =
    case pt of
       Lf _ => NONE
     | Nd nt args =>
       if nt <> mkNT nDecl then NONE
       else
         case args of
             [dt] =>
             do
               tydec <- ptree_TypeDec dt;
               SOME (Ast_Dtype tydec)
             od
           | [funtok; fdecls] =>
             do
               assert(funtok = Lf (TOK FunT));
               fdecs <- ptree_AndFDecls fdecls;
               SOME (Ast_Dletrec fdecs)
             od ++
             do
               assert (funtok = Lf (TOK ExceptionT));
               (enm, etys) <- ptree_Dconstructor fdecls;
               SOME (Ast_Dexn enm etys)
             od
           | [valtok; patpt; eqtok; ept] =>
             do
               assert (valtok = Lf (TOK ValT) ∧ eqtok = Lf (TOK EqualsT));
               pat <- ptree_Pattern nPattern patpt;
               e <- ptree_Expr nE ept;
               SOME (Ast_Dlet pat e)
             od
           | _ => NONE
`

val ptree_Decls_def = Define`
  ptree_Decls (Lf _) = NONE ∧
  ptree_Decls (Nd nt args) =
    if nt <> mkNT nDecls then NONE
    else
      case args of
          [] => SOME []
        | [d_pt; ds_pt] =>
          if d_pt = Lf (TOK SemicolonT) then ptree_Decls ds_pt
          else
            do
              d <- ptree_Decl d_pt;
              ds <- ptree_Decls ds_pt;
              SOME(d::ds)
            od
        | _ => NONE
`

val ptree_SpecLine_def = Define`
  ptree_SpecLine (Lf _) = NONE ∧
  ptree_SpecLine (Nd nt args) =
    if nt <> mkNT nSpecLine then NONE
    else
      case args of
          [td_pt] =>
          do
            td <- ptree_TypeDec td_pt;
            SOME(Ast_Stype td)
          od
        | [typetok; tynm_pt] =>
          do
            assert(typetok = Lf (TOK TypeT));
            tynm <- ptree_TypeName tynm_pt;
            SOME(Ast_Stype_opq (FST tynm) (SND tynm))
          od
        | [valtok; vname_pt; coltok; type_pt] =>
          do
            assert(valtok = Lf (TOK ValT) ∧ coltok = Lf (TOK ColonT));
            vname <- ptree_V vname_pt;
            ty <- ptree_Type nType type_pt;
            SOME(Ast_Sval vname ty)
          od
        | _ => NONE
`

val ptree_SpeclineList_def = Define`
  ptree_SpeclineList (Lf _) = NONE ∧
  ptree_SpeclineList (Nd nt args) =
    if nt <> mkNT nSpecLineList then NONE
    else
      case args of
          [] => SOME []
        | [sl_pt; sll_pt] =>
          if sl_pt = Lf (TOK SemicolonT) then ptree_SpeclineList sll_pt
          else
            do
              sl <- ptree_SpecLine sl_pt;
              sll <- ptree_SpeclineList sll_pt;
              SOME(sl::sll)
            od
        | _ => NONE
`

val ptree_SignatureValue_def = Define`
  ptree_SignatureValue (Lf _) = NONE ∧
  ptree_SignatureValue (Nd nt args) =
    if nt <> mkNT nSignatureValue then NONE
    else
      case args of
          [sigtok; sll_pt; endtok] =>
          do
            assert(sigtok = Lf (TOK SigT) ∧ endtok = Lf (TOK EndT));
            ptree_SpeclineList sll_pt
          od
        | _ => NONE
`;

val ptree_StructName_def = Define`
  ptree_StructName (Lf _) = NONE ∧
  ptree_StructName (Nd nm args) =
    if nm <> mkNT nStructName then NONE
    else
      case args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
`

val ptree_Structure_def = Define`
  ptree_Structure (Lf _) = NONE ∧
  ptree_Structure (Nd nt args) =
    if nt <> mkNT nStructure then NONE
    else
      case args of
          [structuretok; sname_pt; asc_opt; eqtok; structtok; ds_pt; endtok] =>
          do
            assert(structtok = Lf (TOK StructT) ∧
                   structuretok = Lf (TOK StructureT) ∧
                   eqtok = Lf (TOK EqualsT) ∧ endtok = Lf (TOK EndT));
            sname <- ptree_StructName sname_pt;
            asc <- case asc_opt of
                       Lf _ => NONE
                     | Nd nt args =>
                         if nt <> mkNT nOptionalSignatureAscription then NONE
                         else
                           case args of
                               [] => SOME NONE
                             | [sealtok; sig_pt] =>
                               do
                                 assert(sealtok = Lf (TOK SealT));
                                 sigv <- ptree_SignatureValue sig_pt;
                                 SOME (SOME sigv)
                               od
                             | _ => NONE;
            ds <- ptree_Decls ds_pt;
            SOME(Ast_Tmod sname asc ds)
          od
        | _ => NONE
`

val ptree_TopLevelDec_def = Define`
  ptree_TopLevelDec (Lf _) = NONE ∧
  ptree_TopLevelDec (Nd nt args) =
    if nt <> mkNT nTopLevelDec then NONE
    else
      case args of
          [pt] =>
            ptree_Structure pt ++
            OPTION_MAP Ast_Tdec (ptree_Decl pt)
        | _ => NONE
`

val ptree_TopLevelDecs_def = Define`
  ptree_TopLevelDecs (Lf _) = NONE ∧
  ptree_TopLevelDecs (Nd nt args) =
    if nt <> mkNT nTopLevelDecs then NONE
    else
      case args of
          [] => SOME []
        | [td_pt; tds_pt] =>
          do
            td <- ptree_TopLevelDec td_pt;
            tds <- ptree_TopLevelDecs tds_pt;
            SOME(td::tds)
          od
        | _ => NONE
`;

val ptree_REPLPhrase_def = Define`
  ptree_REPLPhrase (Lf _) = NONE ∧
  ptree_REPLPhrase (Nd nt args) =
    if nt <> mkNT nREPLPhrase then NONE
    else
      case args of
          [pt; semitok] =>
            ptree_TopLevelDecs pt ++
            do
              e <- ptree_Expr nE pt;
              SOME[Ast_Tdec (Ast_Dlet (Pvar "it") e)]
            od
         | _ => NONE
`;

val ptree_REPLTop_def = Define`
  ptree_REPLTop (Lf _) = NONE ∧
  ptree_REPLTop (Nd nt args) =
    if nt <> mkNT nREPLTop then NONE
    else
      case args of
          [pt; semitok] =>
            ptree_TopLevelDec pt ++
            do
              e <- ptree_Expr nE pt;
              SOME(Ast_Tdec (Ast_Dlet (Pvar "it") e))
            od
         | _ => NONE
`;


val _ = export_theory()
