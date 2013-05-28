open HolKernel Parse boolLib bossLib

open gramTheory

open monadsyntax lcsymtacs

local open ElabTheory in end (* for "ast" type *)

val _ = new_theory "mmlPtreeConversion"

(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

(* Use of parsing-heap means that this theory is secretly a descendent of
   pegexecTheory, where 'nt' is a constructor name.

   This is a disgusting failing of our theory mechanism.  *)
val _ = hide "nt"


val OPTION_CHOICE_def = Define`
  OPTION_CHOICE (SOME y) x = SOME y ∧
  OPTION_CHOICE NONE x = x
`

val _ = overload_on ("++", ``OPTION_CHOICE``)

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

val ptree_Type_def = Define`
  (ptree_Type ptree : ast_t option =
    case ptree of
        Nd nt args =>
        if nt = mkNT nType then
          case args of
              [dt] => ptree_Type dt
            | [dt;arrowt;rt] =>
              do
                assert(arrowt = Lf (TOK ArrowT));
                dty <- ptree_Type dt;
                rty <- ptree_Type rt;
                SOME(Ast_Tfn dty rty)
              od
            | _ => NONE
        else if nt = mkNT nDType then
          case args of
              [pt] =>
                OPTION_MAP Ast_Tvar (destTyvarPT pt) ++
                OPTION_MAP (Ast_Tapp []) (ptree_Tyop pt)
            | [dt; opn] => do
                             dty <- ptree_Type dt;
                             opname <- ptree_Tyop opn;
                             SOME(Ast_Tapp [dty] opname)
                           od
            | [lpart; t; rpart] =>
              do
                assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
                ptree_Type t
              od
           | [lpart; tl; rpart; opn] =>
             do
                assert(lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT));
                tylist <- ptree_Typelist tl;
                opname <- ptree_Tyop opn;
                SOME(Ast_Tapp tylist opname)
             od
           | _ => NONE
        else NONE
      | _ => NONE) ∧
  (ptree_Typelist ptree : ast_t list option =
     case ptree of
       Lf _ => NONE
     | Nd nt args =>
       if nt <> mkNT nTypeList then NONE
       else
         case args of
             [dt] => do ty <- ptree_Type dt; SOME[ty] od
           | [dt; commat; tl'] =>
             do
               assert(commat = Lf (TK CommaT));
               ty <- ptree_Type dt;
               tylist <- ptree_Typelist tl';
               SOME(ty::tylist)
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
              tyvnms <- ptree_linfix nTyVarList CommaT destTyvarPT tyvl;
              opn <- ptree_UQTyop opt;
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
      if subs = [Lf (TK StarT)] then SOME (Short "*")
      else if subs = [Lf (TK (SymbolT "/"))] then SOME (Short "/")
      else if subs = [Lf (TK (AlphaT "mod"))] then SOME (Short "mod")
      else if subs = [Lf (TK (AlphaT "div"))] then SOME (Short "div")
      else NONE
    else if nt = mkNT nAddOps then
      if subs = [Lf (TK (SymbolT "+"))] then SOME (Short "+")
      else if subs = [Lf (TK (SymbolT "-"))] then SOME (Short "-")
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

val ptree_Pattern_def = Define`
  (ptree_Pattern nt (Lf _) = NONE) ∧
  (ptree_Pattern nt (Nd nm args) =
    if mkNT nt <> nm then NONE
    else if nm = mkNT nPbase then
      case args of
          [vic] =>
          do
             cname <- ptree_ConstructorName vic;
             if cname = Short "true" then
               SOME(Ast_Plit (Bool T))
             else if cname = Short "false" then
               SOME(Ast_Plit (Bool F))
             else
               SOME(Ast_Pcon cname [])
          od ++
          do
             vname <- ptree_V vic;
             SOME(Ast_Pvar vname)
          od ++
          do
            lf <- destLf vic;
            t <- destTOK lf;
            i <- destIntT t ;
            SOME (Ast_Plit (IntLit i))
          od ++
          if vic = Lf (TOK UnderbarT) then SOME (Ast_Pvar "_")
          else NONE
        | [lp; rp] => if lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT) then
                        SOME (Ast_Plit Unit)
                      else NONE
        | [lp; p; rp] =>
          do
            assert(lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT));
            ptree_Pattern nPattern p
          od
        | _ => NONE
    else if nm = mkNT nPattern then
      case args of
          [pb] => ptree_Pattern nPbase pb
        | [cnm; p] =>
          do
            cn <- ptree_ConstructorName cnm;
            (do
              pb <- ptree_Pattern nPbase p ;
              if cn = Short "ref" then
                SOME(Ast_Pref pb)
              else
                SOME (Ast_Pcon cn [pb])
             od ++ do
              args <- ptree_Ptuple nPtuple p;
              SOME (Ast_Pcon cn args)
            od)
          od
        | _ => NONE
    else NONE) ∧
  (ptree_Ptuple _ (Lf _) = NONE) ∧
  (ptree_Ptuple nt (Nd nm args) =
     if nm <> mkNT nt then NONE
     else if nt = nPtuple then
       case args of
           [lp; pl2; rp] =>
           do
             assert (lp = Lf (TOK LparT) ∧ rp = Lf (TOK RparT));
             ptree_Ptuple nPatternList2 pl2
           od
         | _ => NONE
     else if nt = nPatternList2 then
       case args of
           [p; ct; pl1] =>
           do
             assert (ct = Lf (TOK CommaT));
             hdpat <- ptree_Pattern nPattern p;
             tlpats <- ptree_Ptuple nPatternList1 pl1;
             SOME(hdpat::tlpats)
           od
         | _ => NONE
     else if nt = nPatternList1 then
       case args of
           [p] => do pat <- ptree_Pattern nPattern p; SOME [pat] od
         | [pl1; ct; p] =>
           do
             assert (ct = Lf (TOK CommaT));
             pats <- ptree_Ptuple nPatternList1 pl1;
             pat <- ptree_Pattern nPattern p;
             SOME(APPEND pats [pat])
           od
         | _ => NONE
     else NONE)
`;

val updAst_Conname_def = Define`
  updAst_Conname cname (Ast_Con _ args) = SOME (Ast_Con cname args) ∧
  updAst_Conname _ _ = NONE
`

val backAppCon_def = Define`
  backAppCon (Ast_Con x args) b = SOME (Ast_Con x (args ++ [b])) ∧
  backAppCon _ _ = NONE
`;

val frontAppCon_def = Define`
  frontAppCon e (Ast_Con x args) = SOME (Ast_Con x (e::args)) ∧
  frontAppCon _ _ = NONE
`;

val Eseq_encode_def = Define`
  (Eseq_encode [] = NONE) ∧
  (Eseq_encode [e] = SOME e) ∧
  (Eseq_encode (e::es) =
   do
     body <- Eseq_encode es;
     SOME(Ast_Let "_" e body)
   od)
`

val mkAst_App_def = Define`
  mkAst_App a1 a2 =
   case a1 of
       Ast_Con (Short "ref") [] => Ast_App (Ast_Var (Short "ref")) a2
     | Ast_Con s [] => Ast_Con s [a2]
     | _ => Ast_App a1 a2
`

val ptree_Exn_def = Define`
  ptree_Exn (Lf _) = NONE ∧
  ptree_Exn (Nd nt subs) =
    if nt <> mkNT nExn then NONE
    else
      case subs of
          [bd] => if bd = Lf (TOK (AlphaT "Bind")) then SOME Bind_error
                  else if bd = Lf (TOK (AlphaT "Div")) then SOME Div_error
                  else NONE
        | [ie; ipt] =>
          do
            assert(ie = Lf (TOK (AlphaT "IntError")));
            OPTION_MAP Int_error (destIntT ' (destTOK ' (destLf ipt)))
          od
        | _ => NONE
`;

val ptree_Expr_def = Define`
  ptree_Expr ent (Lf _) = NONE ∧
  ptree_Expr ent (Nd nt subs) =
    (if mkNT ent = nt then
      if nt = mkNT nEbase then
        case subs of
            [lpart; pt; rpart] =>
            if lpart = Lf (TK LparT) ∧ rpart = Lf (TK RparT) then
              do
                eseq <- ptree_Eseq pt;
                Eseq_encode eseq
              od
            else NONE
          | [single] =>
              do
                lf <- destLf single;
                t <- destTOK lf;
                i <- destIntT t ;
                SOME (Ast_Lit (IntLit i))
              od ++
              do
                s <- ptree_FQV single;
                SOME (Ast_Var s)
              od ++
              do cname <- ptree_ConstructorName single;
                 if cname = Short "true" then
                   SOME (Ast_Lit (Bool T))
                 else if cname = Short "false" then
                   SOME (Ast_Lit (Bool F))
                 else
                   SOME (Ast_Con cname [])
              od
          | [lp;rp] => if lp = Lf (TK LparT) ∧ rp = Lf (TK RparT) then
                         SOME (Ast_Lit Unit)
                       else NONE
          | [lett;letdecs_pt;intok;ept;endt] =>
            do
              assert(lett = Lf (TOK LetT) ∧ intok = Lf (TOK InT) ∧
                     endt = Lf (TOK EndT));
              letdecs <- ptree_LetDecs letdecs_pt;
              eseq <- ptree_Eseq ept;
              e <- Eseq_encode eseq;
              SOME(FOLDR (λdf acc. case df of
                                       INL (v,e0) => Ast_Let v e0 acc
                                     | INR fds => Ast_Letrec fds acc)
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
            [e; ct; el] =>
              do
                assert(ct = Lf (TOK CommaT));
                front <- ptree_Expr nE e;
                back <- ptree_Expr nElist1 el;
                frontAppCon front back
              od
          | _ => NONE
      else if nt = mkNT nElist1 then
        case subs of
            [sing] => do e <- ptree_Expr nE sing; SOME(Ast_Con (Short "") [e]) od
          | [el1;ct;e] =>
            if ct = Lf (TOK CommaT) then
              do
                front <- ptree_Expr nElist1 el1 ;
                back <- ptree_Expr nE e;
                backAppCon front back
              od
            else NONE
          | _ => NONE
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
      else if nt = mkNT nEadd then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nEmult t2;
              SOME (Ast_App (Ast_App (Ast_Var a_op) a1) a2)
            od
          | [t] => ptree_Expr nEmult t
          | _ => NONE
      else if nt = mkNT nErel then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nEadd t2;
              SOME (Ast_App (Ast_App (Ast_Var a_op) a1) a2)
            od
          | [t] => ptree_Expr nEadd t
          | _ => NONE
      else if nt = mkNT nEcomp then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEcomp t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nErel t2;
              SOME(Ast_App(Ast_App (Ast_Var a_op) a1) a2)
            od
          | [t] => ptree_Expr nErel t
          | _ => NONE
      else if nt = mkNT nEbefore then
        case subs of
          [t1;opt;t2] => do
            assert(opt = Lf(TOK(AlphaT "before")));
            a1 <- ptree_Expr nEbefore t1;
            a2 <- ptree_Expr nEcomp t2;
            SOME(Ast_App (Ast_App (Ast_Var (Short "before")) a1) a2)
          od
        | [t] => ptree_Expr nEcomp t
        | _ => NONE
      else if nt = mkNT nEtyped then
        case subs of
          [t1;colon;t2] => do
            assert(colon = Lf (TOK ColonT));
            t1 <- ptree_Expr nEbefore t1;
            t2 <- ptree_Type t2;
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
              SOME(Ast_Log And a1 a2)
            od
          | [t] => ptree_Expr nEtyped t
          | _ => NONE
      else if nt = mkNT nElogicOR then
        case subs of
            [t1;ort;t2] => do
              assert(ort = Lf (TOK OrelseT));
              a1 <- ptree_Expr nElogicOR t1;
              a2 <- ptree_Expr nElogicAND t2;
              SOME (Ast_Log Or a1 a2)
            od
          | [t] => ptree_Expr nElogicAND t
          | _ => NONE
      else if nt = mkNT nEhandle then
        case subs of
            [pt] => ptree_Expr nElogicOR pt
          | [e1pt; handlet; interrort; vpt; arrowt; e2pt] =>
            do
              assert(handlet = Lf (TOK HandleT) ∧ arrowt = Lf (TOK DarrowT) ∧
                     interrort = Lf (TOK (AlphaT "IntError")));
              e1 <- ptree_Expr nElogicOR e1pt;
              v <- ptree_V vpt;
              e2 <- ptree_Expr nE e2pt;
              SOME(Ast_Handle e1 v e2)
            od
          | _ => NONE
      else if nt = mkNT nE then
        case subs of
          | [t] => ptree_Expr nEhandle t
          | [raiset; ept] =>
            do
              assert(raiset = Lf (TOK RaiseT));
              e <- ptree_Exn ept;
              SOME(Ast_Raise e)
            od
          | [fnt; vnt; arrowt; ent] =>
            do
              assert (fnt = Lf (TOK FnT) ∧ arrowt = Lf (TOK DarrowT));
              v <- ptree_V vnt;
              e <- ptree_Expr nE ent;
              SOME(Ast_Fun v e)
            od ++ do
              assert (fnt = Lf (TOK CaseT) ∧ arrowt = Lf (TOK OfT));
              e <- ptree_Expr nE vnt;
              pes <- ptree_PEs ent;
              SOME(Ast_Mat e pes)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(ift = Lf (TOK IfT) ∧ thent = Lf (TOK ThenT) ∧
                     elset = Lf (TOK ElseT));
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE ee;
              SOME(Ast_If a1 a2 a3)
            od
          | _ => NONE
      else NONE
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
                SOME(fname,v1,FOLDR Ast_Fun body0 (safeTL vs))
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
        | [pes_pt; bartok; pe_pt] =>
          do
            assert(bartok = Lf (TOK BarT));
            pes <- ptree_PEs pes_pt;
            pe <- ptree_PE pe_pt;
            SOME(pes ++ [pe])
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
        | [seq_pt; semi; e_pt] =>
          do
            assert(semi = Lf (TOK SemicolonT));
            seq <- ptree_Eseq seq_pt;
            e <- ptree_Expr nE e_pt;
            SOME(seq ++ [e])
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
            ty <- ptree_Type type_pt;
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
            sname <- ptree_V sname_pt;
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
              SOME[Ast_Tdec (Ast_Dlet (Ast_Pvar "it") e)]
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
              SOME(Ast_Tdec (Ast_Dlet (Ast_Pvar "it") e))
            od
         | _ => NONE
`;


val _ = export_theory()
