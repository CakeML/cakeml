(*
  Specification of how to convert parse trees to abstract syntax.
*)
Theory cmlPtreeConversion
Ancestors
  gram tokenUtils ast namespace[qualified]
Libs
  preamble


val _ = patternMatchesSyntax.temp_enable_pmatch();

(* handling constructor arities gets very complicated when "open" is
   implemented *)
Datatype:
  PCstate0 = <| fixities : mlstring |-> num option ;
                ctr_arities : (mlstring, mlstring) id |-> num |>
End
(* recording a fixity of NONE is what you have to do to represent an
   explicit nonfix declaration *)

Type M = ``:PCstate0 list -> ('a # PCstate0 list) option``

Definition empty_PCstate0_def:
  empty_PCstate0 = <| fixities := FEMPTY ; ctr_arities := FEMPTY |>
End

Definition mpushPC_scope_def:
  mpushPC_scope : unit M = λpcs. SOME ((), empty_PCstate0 :: pcs)
End

Definition fixity_lookup_def:
  fixity_lookup nm pcs =
    case pcs of
        [] => NONE
      | pc0 :: rest =>
          case FLOOKUP pc0.fixities nm of
              NONE => fixity_lookup nm rest
            | SOME NONE => NONE
            | SOME r => r
End

(* mfixity_lookup : mlstring -> num M
    'fails' if the mlstring has no fixity, even though it is perfectly
    reasonable for a mlstring to be nonfix.
*)
Definition mfixity_lookup_def:
  mfixity_lookup nm : num M =
    λpcs. OPTION_MAP (λr. (r, pcs)) (fixity_lookup nm pcs)
End

Definition mFUPD_HD_def:
  mFUPD_HD f pcs =
    case pcs of
        [] => NONE
      | h :: t => SOME((), f h :: t)
End

(* msetfix : mlstring -> num option -> unit M *)
Definition msetfix_def:
  msetfix nm fix : unit M =
    mFUPD_HD (λs0. s0 with fixities updated_by (λfm. fm |+ (nm, fix)))
End

(* mpop_anonscope : unit M *)
Definition mpop_anonscope_def:
  mpopscope : unit M = λpcs.
    case pcs of
      [] => NONE
    | _ :: t => SOME((), t)
End

Definition mpop_namedscope_def:
  mpop_namedscope (s : mlstring) : unit M = λpcs.
    case pcs of
      [] => NONE
    | [_] => NONE
    | curr :: next :: rest => SOME((), next :: rest)
End
(* needs to be adjusted so that constructors (only) declared in the current
   scope get recorded in the next level up with the given name as a prefix.

   Does nothing different at this stage, when I expect just to be handling
   fixities (which are handled in a non-exportable way).
 *)


(* ----------------------------------------------------------------------
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------- *)

val _ = option_monadsyntax.temp_add_option_monadsyntax();

Overload lift[local] = ``option$OPTION_MAP``

Definition ifM_def:
  ifM bM tM eM =
    do
       b <- bM;
       if b then tM else eM
    od
End

Definition mk_binop_def:
  mk_binop a_op a1 a2 =
    if a_op = Short «::» then Con (SOME (Short «::»)) [a1; a2]
    else App Opapp [App Opapp [Var a_op; a1]; a2]
End

Overload "'"[local] = ``λf a. OPTION_BIND a f``;

Definition tokcheck_def:
  tokcheck pt tok <=> (destTOK ' (destLf pt) = SOME tok)
End

Definition ptree_UQTyop_def:
  ptree_UQTyop (Lf _) = NONE ∧
  ptree_UQTyop (Nd nt args) =
    if FST nt <> mkNT nUQTyOp then NONE
    else
      case args of
          [pt] =>
          do
            lf <- destLf pt;
            tk <- destTOK lf;
            destSymbolT tk ++ destAlphaT tk
          od
        | _ => NONE
End

Definition ptree_TyvarN_def:
  ptree_TyvarN (Lf _) = NONE ∧
  ptree_TyvarN (Nd nt args) =
    if FST nt <> mkNT nTyvarN then NONE
    else
      case args of
          [tyv] => destTyvarPT tyv
        | _ => NONE
End

Definition Long_Short_def:
  Long_Short End (s: mlstring) = Short s ∧
  Long_Short (Mod x xs) s = Long x (Long_Short xs s)
End

Definition ptree_Tyop_def:
  ptree_Tyop (Lf _) = NONE ∧
  ptree_Tyop (Nd nt args) =
    if FST nt <> mkNT nTyOp then NONE
    else
      case args of
          [pt] =>
          do
            (xs,s) <- destLongidT ' (destTOK ' (destLf pt));
            SOME(Long_Short xs s)
          od ++
          do
            nm <- ptree_UQTyop pt;
            SOME(Short nm)
          od
        | _ => NONE
End

Definition tokcheckl_def:
  tokcheckl pts toks <=>
    case (pts,toks) of
      ([],[]) => T
    | (pt::prest, tok::tokrest) => tokcheck pt tok ∧ tokcheckl prest tokrest
    | _ => F
End

Definition ptree_linfix_def:
  ptree_linfix topnt opn elnt (pt : mlptree) =
    case pt of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt = mkNT topnt then
          case args of
              [pt] => do e <- elnt pt; SOME [e] od
            | [x; op_pt; pt] => do
                assert(tokcheck op_pt opn);
                front <- ptree_linfix topnt opn elnt x;
                last <- elnt pt;
                SOME(front ++ [last])
              od
            | _ => NONE
        else NONE
End

Definition tuplify_def:
  tuplify [] = NONE ∧
  tuplify [ty] = SOME ty ∧
  tuplify tys = SOME(Attup tys)
End

Definition ptree_Type_def:
  (ptree_Type nt (Lf _) : ast_t option = NONE) ∧
  (ptree_Type nm (Nd nt args) =
     if FST nt <> mkNT nm then NONE
     else if nm = nType then
       case args of
          [dt] =>
          do
            tys <- ptree_PType dt;
            tuplify tys
          od
        | [dt;arrowt;rt] =>
              do
                assert(tokcheck arrowt ArrowT);
                dtys <- ptree_PType dt;
                dty <- tuplify dtys;
                rty <- ptree_Type nType rt;
                SOME(Atfun dty rty)
              od
            | _ => NONE
     else if nm = nDType then
       case args of
           [pt] => ptree_Type nTbase pt
         | [dt; opn] => do
                          dty <- ptree_Type nDType dt;
                          opname <- ptree_Tyop opn;
                          SOME(Atapp [dty] opname)
                        od
         | _ => NONE
     else if nm = nTbase then
       case args of
           [pt] =>
                OPTION_MAP Atvar (destTyvarPT pt) ++
                OPTION_MAP (Atapp []) (ptree_Tyop pt)
         | [lpart; t; rpart] =>
              do
                assert(tokcheck lpart LparT ∧ tokcheck rpart RparT);
                ptree_Type nType t
              od
         | [lpart; tl; rpart; opn] =>
           do
              assert(tokcheck lpart LparT ∧ tokcheck rpart RparT);
              tylist <- ptree_Typelist2 tl;
              opname <- ptree_Tyop opn;
              SOME(Atapp tylist opname)
           od
         | _ => NONE
     else NONE) ∧
  (ptree_Typelist2 ptree : ast_t list option =
     case ptree of
       Lf _ => NONE
     | Nd nt args =>
       if FST nt <> mkNT nTypeList2 then NONE
       else
         case args of
           | [dt; commat; tl'] =>
             do
               assert(tokcheck commat CommaT);
               ty <- ptree_Type nType dt;
               tylist <- ptree_TypeList1 tl';
               SOME(ty::tylist)
             od
           | _ => NONE) ∧
  (ptree_TypeList1 ptree : ast_t list option =
    case ptree of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt <> mkNT nTypeList1 then NONE
        else
          case args of
              [dt] =>
              do
                ty <- ptree_Type nType dt;
                SOME([ty])
              od
            | [dt; commat; tl] =>
              do
                assert(tokcheck commat CommaT);
                ty <- ptree_Type nType dt;
                tl <- ptree_TypeList1 tl;
                SOME(ty::tl)
              od
            | _ => NONE) ∧
  (ptree_PType ptree : ast_t list option =
     case ptree of
         Lf _ => NONE
       | Nd nt args =>
         if FST nt <> mkNT nPType then NONE
         else
           case args of
               [dty_pt] =>
               do
                 dty <- ptree_Type nDType dty_pt;
                 SOME [dty]
               od
             | [dty_pt; st; pty_pt] =>
               do
                 assert (tokcheck st StarT);
                 dty <- ptree_Type nDType dty_pt;
                 ptys <- ptree_PType pty_pt;
                 SOME(dty::ptys)
               od
             | _ => NONE)
End

Definition ptree_TypeName_def:
  ptree_TypeName ptree : (tvarN list # typeN) option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if FST nt = mkNT nTypeName then
        case args of
          [opt] => do opn <- ptree_UQTyop opt ; SOME([], opn) od
        | [sym; opt] => do tyvn <- destTyvarPT sym ;
                           opn <- ptree_UQTyop opt ;
                           return ([tyvn], opn)
                        od
        | [lp; tyvl; rp; opt] =>
          do
            assert (tokcheck lp LparT ∧ tokcheck rp RparT);
            tyvnms <- ptree_linfix nTyVarList CommaT ptree_TyvarN tyvl;
            opn <- ptree_UQTyop opt;
            return(tyvnms, opn)
          od
        | _ => NONE
      else NONE
End

Definition ptree_UQConstructorName_def:
  ptree_UQConstructorName (Lf _) = NONE ∧
  ptree_UQConstructorName (Nd nm args) =
    if FST nm <> mkNT nUQConstructorName then NONE
    else
      case args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
End

Definition ptree_ConstructorName_def:
  ptree_ConstructorName ast =
    case ast of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt <> mkNT nConstructorName then NONE
        else
          case args of
              [pt] =>
              do
                s <- ptree_UQConstructorName pt;
                SOME (Short s)
              od ++
              do
                (xs,s) <- destLongidT ' (destTOK ' (destLf pt));
                SOME (Long_Short xs s)
              od
            | _ => NONE
End

Definition detuplify_def:
  detuplify (Attup args) = args ∧
  detuplify ty = [ty]
End

Theorem detuplify_pmatch:
  ∀ty.
    detuplify ty =
    pmatch ty of
      Attup args => args
    | ty => [ty]
Proof
  ho_match_mp_tac (theorem "detuplify_ind")
  >> fs[detuplify_def]
QED

Definition ptree_PTbase_def:
  ptree_PTbase ast =
    case ast of
        Lf _ => fail
      | Nd nt args =>
        if FST nt = mkNT nPTbase then
          case args of
              [pt] =>
                OPTION_MAP Atvar (destTyvarPT pt) ++
                OPTION_MAP (Atapp []) (ptree_Tyop pt)
            | [lpart; t; rpart] =>
              do
                assert(tokcheck lpart LparT ∧ tokcheck rpart RparT);
                ptree_Type nType t
              od
            | _ => fail
        else fail
End

Definition ptree_TbaseList_def:
  ptree_TbaseList ast =
    case ast of
        Lf _ => fail
      | Nd nt args =>
        if FST nt = mkNT nTbaseList then
          case args of
              [] => return []
            | [ptb_pt;rest_pt] => do
                b <- ptree_PTbase ptb_pt ;
                rest <- ptree_TbaseList rest_pt ;
                return (b::rest)
              od
            | _ => fail
        else fail
End

Definition ptree_Dconstructor_def:
  ptree_Dconstructor ast =
    case ast of
        Lf x => NONE
      | Nd nt args =>
        if FST nt = mkNT nDconstructor then
          case args of
              [] => NONE
            | t::ts =>
              do
                 cname <- ptree_UQConstructorName t;
                 types <- case ts of
                               [blist] =>
                               do
                                 args <- ptree_TbaseList blist ;
                                 return args
                               od
                             | _ => NONE;
                 SOME(cname, types)
              od
        else NONE
End

Definition ptree_DtypeDecl_def:
  ptree_DtypeDecl (pt : mlptree) =
    case pt of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt = mkNT nDtypeDecl then
          case args of
              [tynm_pt; eqt; dtc_pt] => do
                assert(tokcheck eqt EqualsT);
                tynm <- ptree_TypeName tynm_pt;
                dtc <- ptree_linfix nDtypeCons BarT ptree_Dconstructor dtc_pt;
                SOME(FST tynm,SND tynm,dtc)
              od
            | _ => NONE
        else NONE
End

Definition ptree_TypeDec_def:
  ptree_TypeDec ptree : type_def option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if FST nt = mkNT nTypeDec then
        case args of
            [datatype_pt; pt] => do
              assert(tokcheck datatype_pt DatatypeT);
              ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt
            od
          | _ => NONE
      else NONE
End

Definition ptree_TypeAbbrevDec_def:
  ptree_TypeAbbrevDec ptree : dec option =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      if FST nt = mkNT nTypeAbbrevDec then
        case args of
          [typetok; tynm ; eqtok ; typ_pt] => do
            assert(tokcheck typetok TypeT ∧ tokcheck eqtok EqualsT) ;
            (vars, nm) <- ptree_TypeName tynm;
            typ <- ptree_Type nType typ_pt;
            SOME(Dtabbrev (SND nt) vars nm typ)
          od
        | _ => NONE
      else NONE
End

Definition singleSymP_def:
  singleSymP P [pt] = do s <- destSymbolT ' (destTOK ' (destLf pt)) ;
                        assert (P s);
                        return (Short s)
                     od ∧
  singleSymP _ _ = NONE
End

Definition ptree_Op_def:
  ptree_Op (Lf _) = NONE ∧
  ptree_Op (Nd nt subs) =
    if FST nt = mkNT nMultOps then
      if tokcheckl subs [StarT] then SOME (Short «*»)
      else if tokcheckl subs [AlphaT «mod»] then SOME (Short «mod»)
      else if tokcheckl subs [AlphaT «div»] then SOME (Short «div»)
      else singleSymP (validMultSym ∘ explode) subs
    else if FST nt = mkNT nAddOps then singleSymP (validAddSym ∘ explode) subs
    else if FST nt = mkNT nListOps then singleSymP (validListSym ∘ explode) subs
    else if FST nt = mkNT nRelOps then
      singleSymP (validRelSym ∘ explode) subs ++
      do assert(tokcheckl subs [EqualsT]); return(Short «=») od
    else if FST nt = mkNT nCompOps then
      if tokcheckl subs [SymbolT «:=»] then SOME (Short «:=»)
      else if tokcheckl subs [AlphaT «o»] then SOME (Short «o»)
      else NONE
    else NONE
End

Definition ptree_V_def:
  ptree_V (Lf _) = NONE ∧
  ptree_V (Nd nt subs) =
       do
         assert (FST nt = mkNT nV) ;
         case subs of
            [pt] => do t <- destTOK ' (destLf pt) ;
                       destAlphaT t ++ destSymbolT t
                    od
          | _ => NONE
       od
End

Definition ptree_FQV_def:
  ptree_FQV (Lf _) = NONE ∧
  ptree_FQV (Nd nt args) =
    if FST nt <> mkNT nFQV then NONE
    else
      case args of
          [pt] => OPTION_MAP Short (ptree_V pt) ++
                  do
                    (xs,s) <- destLongidT ' (destTOK ' (destLf pt));
                    SOME(Long_Short xs s)
                  od
        | _ => NONE
End

Definition isSymbolicConstructor_def:
  isSymbolicConstructor s =
    return (s = "::")
End

Definition isConstructor_def:
  isConstructor s =
    do
      ifM (isSymbolicConstructor s)
        (return T)
        (return (case oHD s of NONE => F | SOME c => isAlpha c ∧ isUpper c))
    od
End

(* third clause below will lead to a failure when the environment is
   consulted to reveal that the long-id given does not correspond to a
   constructor.  We do this rather than fail to make the "totality" theorem
   work *)
Definition EtoPat_def:
  (EtoPat (Con x args) = if NULL args then SOME (Pcon x []) else NONE) ∧
  (EtoPat (Var (Short n)) = SOME (Pvar n)) ∧
  (EtoPat (Var (Long str n)) = SOME (Pcon (SOME (Long str n)) [])) ∧
  (EtoPat _ = NONE)
End

Definition ptree_OpID_def:
  ptree_OpID (Lf _) = NONE ∧
  ptree_OpID (Nd nt subs) =
    if FST nt ≠ mkNT nOpID then NONE
    else
      case subs of
          [Lf (TK tk, _)] =>
          do
              s <- destAlphaT tk ;
              ifM (isConstructor (explode s))
                  (return (Con (SOME (Short s)) []))
                  (return (Var (Short s)))
          od ++
          do
              s <- destSymbolT tk ;
              ifM (isSymbolicConstructor (explode s))
                  (return (Con (SOME (Short s)) []))
                  (return (Var (Short s)))
          od ++
          do
              (path,s) <- destLongidT tk ;
              ifM (isConstructor (explode s))
                  (return (Con (SOME (Long_Short path s)) []))
                  (return (Var (Long_Short path s)))
          od ++
          (if tk = StarT then
             ifM (isSymbolicConstructor "*")
                 (return (Con (SOME (Short «*»)) []))
                 (return (Var (Short «*»)))
           else if tk = EqualsT then return (Var (Short «=»))
           else NONE)
        | _ => NONE
End

Definition Papply_def:
  Papply pat arg =
    case pat of
      Pcon cn args => Pcon cn (args ++ [arg])
    | _ => pat
End

val maybe_handleRef_def = PmatchHeuristics.with_classic_heuristic Define ‘
  maybe_handleRef (Pcon (SOME (Short «Ref»)) [pat]) = Pref pat ∧
  maybe_handleRef p = p’

Definition ptree_Pattern_def[nocompute]:
  (ptree_Pattern nt (Lf _) = NONE) ∧
  (ptree_Pattern nt (Nd nm args) =
    if mkNT nt <> FST nm then NONE
    else if FST nm = mkNT nPbase then
      case args of
          [vic] =>
          ptree_Pattern nPtuple vic ++
          do
             cname <- ptree_ConstructorName vic;
             SOME(Pcon (SOME cname) [])
          od ++
          do vname <- ptree_V vic; SOME(Pvar vname) od ++
          do
            lf <- destLf vic;
            t <- destTOK lf;
            (do i <- destIntT t ; return (Plit (IntLit i)) od ++
             do s <- destStringT t ; return (Plit (StrLit s)) od ++
             do c <- destCharT t ; return (Plit (Char c)) od)
          od ++
          do assert(tokcheck vic UnderbarT) ; return Pany od
        | [lb; rb] =>
          if tokcheckl args [LbrackT; RbrackT] then
            SOME(Pcon (SOME (Short «[]»)) [])
          else if tokcheckl [lb] [OpT] then
            do e <- ptree_OpID rb ; EtoPat e od
          else NONE
        | [lb; plistpt; rb] =>
          do
            assert (tokcheckl [lb;rb] [LbrackT; RbrackT]);
            plist <- ptree_Plist plistpt;
            SOME (FOLDR (λp a. Pcon (SOME (Short «::»)) [p; a])
                        (Pcon (SOME (Short «[]»)) [])
                        plist)
          od
        | _ => NONE
    else if FST nm = mkNT nPConApp then
      case args of
        [cn] =>
        do
          cname <- ptree_ConstructorName cn ;
          return (Pcon (SOME cname) [])
        od
      | [capp_pt; base_pt] =>
        do
          capp <- ptree_Pattern nPConApp capp_pt ;
          base <- ptree_Pattern nPbase base_pt ;
          return (Papply capp base)
        od
      | _ => fail
    else if FST nm = mkNT nPapp then
      case args of
          [pb] => ptree_Pattern nPbase pb
        | [capp_pt; ppt] =>
          do
            capp <- ptree_Pattern nPConApp capp_pt;
            b <- ptree_Pattern nPbase ppt;
            return (maybe_handleRef (Papply capp b))
          od
        | _ => NONE
    else if FST nm = mkNT nPcons then
      case args of
          [papt] => ptree_Pattern nPapp papt
        | [papt; cons_t; pcons_pt] =>
          do
            assert (tokcheck cons_t (SymbolT «::»));
            pa <- ptree_Pattern nPapp papt;
            patt <- ptree_Pattern nPcons pcons_pt;
            SOME(Pcon (SOME (Short «::»)) [pa; patt])
          od
        | _ => NONE
    else if FST nm = mkNT nPas then
      case args of
          [papt] => ptree_Pattern nPcons papt
        | [vt; as_t; papt] =>
          do
            assert (tokcheck as_t AsT);
            pa <- ptree_Pattern nPcons papt;
            vtt <- ptree_V vt;
            SOME(Pas pa vtt)
          od
        | _ => fail
    else if FST nm = mkNT nPattern then
      case args of
          [pas] => ptree_Pattern nPas pas
        | [pas_pt; colon_t; type_pt] =>
          do
            assert (tokcheck colon_t ColonT);
            pc <- ptree_Pattern nPas pas_pt;
            ty <- ptree_Type nType type_pt;
            return (Ptannot pc ty)
          od
        | _ => fail
    else if FST nm = mkNT nPtuple then
      case args of
          [lp; rp] => do assert (tokcheckl [lp;rp] [LparT; RparT]);
                         return (Pcon NONE [])
                      od
        | [lp; pl_pt; rp] =>
          do
            assert (tokcheckl [lp;rp] [LparT; RparT]);
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
     if FST nm <> mkNT nPatternList then NONE
     else
       case args of
           [p_pt] =>
           do
             p <- ptree_Pattern nPattern p_pt;
             SOME [p]
           od
         | [p; ct; pl] =>
           do
             assert (tokcheck ct CommaT);
             hdpat <- ptree_Pattern nPattern p;
             tlpats <- ptree_Plist pl;
             SOME(hdpat::tlpats)
           od
         | _ => NONE)
End

Type ptree[local] = “:(token,MMLnonT,locs) parsetree”
fun partial_eval baseth c nodepat nt =
  let val tlf = list_mk_icomb(c, [nt, “Lf l : ptree”])
      val tnd = list_mk_icomb(c, [nt, nodepat])
      val c = ONCE_REWRITE_CONV [baseth] THENC SCONV []
  in
    CONJ (c tlf) (c tnd)
  end

Theorem ptree_Pattern_pevaled[compute] =
   LIST_CONJ $
      map (partial_eval ptree_Pattern_def “ptree_Pattern” “Nd nm args : ptree”)
      [“nPattern”, “nPapp”, “nPcons”, “nPas”, “nPbase”, “nPConApp”, “nPtuple”]

Theorem ptree_Plist_thm[compute] =
        LIST_CONJ $ List.take (List.rev $ CONJUNCTS ptree_Pattern_def, 2)

Definition ptree_PbaseList1_def:
  (ptree_PbaseList1 (Lf _) = NONE) ∧
  (ptree_PbaseList1 (Nd nm args) =
     if FST nm <> mkNT nPbaseList1 then NONE
     else
       case args of
           [p_pt] => lift SINGL (ptree_Pattern nPbase p_pt)
         | [p_pt; pl_pt] =>
               lift2 CONS
                     (ptree_Pattern nPbase p_pt)
                     (ptree_PbaseList1 pl_pt)
         | _ => NONE)
End

Definition Eseq_encode_def:
  (Eseq_encode [] = NONE) ∧
  (Eseq_encode [e] = SOME e) ∧
  (Eseq_encode (e::es) =
   do
     body <- Eseq_encode es;
     SOME(Let NONE e body)
   od)
End

Definition dest_Conk_def:
  (dest_Conk (Con x y) k v = k x y) /\
  (dest_Conk _ k v = v)
End

Definition destFFIop_def[simp]:
  (destFFIop (FFI s) = SOME s) ∧
  (destFFIop _ = NONE)
End

Definition strip_loc_expr_def:
 (strip_loc_expr (Lannot e l) =
    case (strip_loc_expr e) of
      (e0, _) => (e0, SOME l)) ∧
 (strip_loc_expr e = (e, NONE))
End

Definition merge_locsopt_def:
  merge_locsopt (SOME l1) (SOME l2) = SOME (merge_locs l1 l2) ∧
  merge_locsopt _ _ = NONE
End

Definition optLannot_def:
  optLannot NONE e = e ∧
  optLannot (SOME l) e = Lannot e l
End

Definition mkAst_App_def:
  mkAst_App a1 a2 =
    let (a10, loc1) = strip_loc_expr a1
    in
      dest_Conk a10
        (λnm_opt args.
          if nm_opt = SOME (Short «Ref») ∧ NULL args then App Opref [a2]
          else
            let (a2', loc2) = strip_loc_expr a2
            in
              optLannot (merge_locsopt loc1 loc2) (Con nm_opt (args ++ [a2'])))
        (case a10 of
           App opn args =>
             (case (destFFIop opn) of
                NONE => App Opapp [a1;a2]
              | SOME s => App opn (args ++ [a2]))
         | _ => App Opapp [a1;a2])
End

Definition dePat_def:
  (dePat (Pvar v) b = (v, b)) ∧
  (dePat p b = («», Mat (Var (Short «»)) [(p, b)]))
End

Definition mkFun_def:
  mkFun p b = UNCURRY Fun (dePat p b)
End

Definition ptree_Eliteral_def:
  ptree_Eliteral (Lf _) = NONE ∧
  ptree_Eliteral (Nd nt subs) =
    do
      assert (LENGTH subs = 1 ∧ FST nt = mkNT nEliteral);
      lf <- destLf (HD subs);
      t <- destTOK lf;
      (do i <- destIntT t ; return (Lit (IntLit i)) od ++
       do c <- destCharT t ; return (Lit (Char c)) od ++
       do s <- destStringT t ; return (Lit (StrLit s)) od ++
       do n <- destWordT t ; return (Lit (Word64 (n2w n))) od ++
       do s <- destFFIT t ; return (App (FFI s) []) od)
    od
End

Definition bind_loc_def:
  bind_loc (Lannot e l) l' = Lannot e l /\
  bind_loc e l = Lannot e l
End

Definition letFromPat_def:
  letFromPat p rhs body =
    case p of
      Pany => Let NONE rhs body
    | Pvar v => Let (SOME v) rhs body
    | _ => Mat rhs [(p,body)]
End

Definition ptree_Expr_def[nocompute]:
  ptree_Expr ent (Lf _) = NONE ∧
  ptree_Expr ent (Nd (nt,loc) subs) =
  do
  e <- (if mkNT ent = nt then
      if nt = mkNT nEbase then
        case subs of
            [lpart; pt; rpart] =>
              if tokcheck lpart LparT then
                do
                  assert (tokcheck rpart RparT);
                  eseq <- ptree_Eseq pt;
                  Eseq_encode eseq
                od
              else
                do
                  assert(tokcheckl [lpart;rpart][LbrackT; RbrackT]);
                  elist <- ptree_Exprlist nElist1 pt;
                  SOME(FOLDR (λe acc. Con (SOME (Short «::»)) [e; acc])
                             (Con (SOME (Short «[]»)) [])
                         elist)
                od
          | [single] =>
              ptree_Eliteral single ++
              do
                s <- ptree_FQV single;
                SOME (Var s)
              od ++
              do cname <- ptree_ConstructorName single;
                 SOME (Con (SOME cname) [])
              od ++
              ptree_Expr nEtuple single
          | [lp;rp] => if tokcheckl [lp;rp][LparT;RparT] then
                         SOME (Con NONE [])
                       else if tokcheckl [lp;rp] [LbrackT; RbrackT] then
                         SOME (Con (SOME (Short «[]»)) [])
                       else if tokcheck lp OpT then
                         ptree_OpID rp
                       else
                         NONE
          | [lett;letdecs_pt;intok;ept;endt] =>
            do
              assert(tokcheckl [lett; intok; endt] [LetT; InT; EndT]);
              letdecs <- ptree_LetDecs letdecs_pt;
              eseq <- ptree_Eseq ept;
              e <- Eseq_encode eseq;
              SOME(FOLDR (λdf acc. case df of
                                       INL (p,e0) => letFromPat p e0 acc
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
              assert (tokcheckl [lpart; rpart] [LparT; RparT]);
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
            return(mk_binop a_op a1 a2)
          od
        | [t] => ptree_Expr nEapp t
        | _ => NONE
      else if nt = mkNT nEadd then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nEmult t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nEmult t
          | _ => NONE
      else if nt = mkNT nElistop then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nElistop t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nEadd t
          | _ => NONE
      else if nt = mkNT nErel then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nErel t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nElistop t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nElistop t
          | _ => NONE
      else if nt = mkNT nEcomp then
        case subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEcomp t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nErel t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nErel t
          | _ => NONE
      else if nt = mkNT nEbefore then
        case subs of
          [t1;opt;t2] => do
            assert(tokcheck opt (AlphaT «before»));
            a1 <- ptree_Expr nEbefore t1;
            a2 <- ptree_Expr nEcomp t2;
            return (mk_binop (Short «before») a1 a2)
          od
        | [t] => ptree_Expr nEcomp t
        | _ => NONE
      else if nt = mkNT nEtyped then
        case subs of
          [e_pt; colon; ty_pt] => do
            assert(tokcheck colon ColonT);
            e <- ptree_Expr nEbefore e_pt;
            ty <- ptree_Type nType ty_pt;
            return (Tannot e ty)
          od
        | [t] => ptree_Expr nEbefore t
        | _ => NONE
      else if nt = mkNT nElogicAND then
        case subs of
            [t1;andt;t2] => do
              assert(tokcheck andt AndalsoT);
              a1 <- ptree_Expr nElogicAND t1;
              a2 <- ptree_Expr nEtyped t2;
              SOME(Log Andalso a1 a2)
            od
          | [t] => ptree_Expr nEtyped t
          | _ => NONE
      else if nt = mkNT nElogicOR then
        case subs of
            [t1;ort;t2] => do
              assert(tokcheck ort OrelseT);
              a1 <- ptree_Expr nElogicOR t1;
              a2 <- ptree_Expr nElogicAND t2;
              SOME (Log Orelse a1 a2)
            od
          | [t] => ptree_Expr nElogicAND t
          | _ => NONE
      else if nt = mkNT nEhandle then
        case subs of
            [pt] => ptree_Expr nElogicOR pt
          | [e1pt; handlet; ent] =>
            do
              assert(tokcheck handlet HandleT);
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
              assert(tokcheck raiset RaiseT);
              e <- ptree_Expr nE ept;
              SOME(Raise e)
            od
          | [fnt; pnt; arrowt; ent] =>
            do
              assert (tokcheckl [fnt; arrowt] [FnT; DarrowT]);
              p <- ptree_Pattern nPattern pnt;
              e <- ptree_Expr nE ent;
              SOME(mkFun p e)
            od ++ do
              assert (tokcheckl [fnt; arrowt] [CaseT; OfT]);
              e <- ptree_Expr nE pnt;
              pes <- ptree_PEs ent;
              SOME(Mat e pes)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(tokcheckl [ift;thent;elset] [IfT; ThenT; ElseT]);
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE ee;
              SOME(If a1 a2 a3)
            od
          | _ => NONE
      else NONE
    else NONE);
    SOME(bind_loc e loc)
  od  ∧
  (ptree_Exprlist nm ast =
     case ast of
         Lf _ => NONE
       | Nd (nt,_) subs =>
         if nt = mkNT nElist1 then
           case subs of
               [sing] => do e <- ptree_Expr nE sing; SOME [e] od
             | [e;ct;el1] =>
               do
                 assert(tokcheck ct CommaT);
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 SOME(front::back)
               od
             | _ => NONE
         else if nt = mkNT nElist2 then
           case subs of
               [e;ct;el1] =>
               do
                 assert(tokcheck ct CommaT);
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 SOME(front::back)
               od
             | _ => NONE
         else NONE) ∧
  ptree_AndFDecls ast =
    (case ast of
        Lf _ => NONE
      | Nd (nt,_) subs =>
        if nt = mkNT nAndFDecls then
          case subs of
              [single] => do fdec <- ptree_FDecl single; SOME ([fdec]) od
            | [fdecspt;andt;fdecpt] =>
              do
                assert(tokcheck andt AndT);
                fdecs <- ptree_AndFDecls fdecspt;
                fdec <- ptree_FDecl fdecpt;
                SOME(fdecs ++ [fdec])
              od
            | _ => NONE
        else NONE) ∧
  (ptree_FDecl ast =
    case ast of
        Lf _ => NONE
      | Nd (nt,_) subs =>
        if nt = mkNT nFDecl then
          case subs of
              [fname_pt; pats_pt; eqt; body_pt] =>
              do
                assert(tokcheck eqt EqualsT);
                fname <- ptree_V fname_pt;
                ps <- ptree_PbaseList1 pats_pt;
                p1 <- oHD ps;
                body0 <- ptree_Expr nE body_pt;
                SOME(fname,dePat p1 (FOLDR mkFun body0 (TL ps)))
              od
            | _ => NONE
        else NONE) ∧
  (ptree_LetDecs ptree =
    case ptree of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt <> mkNT nLetDecs then NONE
        else
          case args of
              [] => SOME []
            | [ld_pt; lds_pt] =>
              if tokcheck ld_pt SemicolonT then ptree_LetDecs lds_pt
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
      | Nd (nt,_) args =>
        if nt <> mkNT nLetDec then NONE
        else
          case args of
              [funtok; andfdecls_pt] =>
              do
                assert (tokcheck funtok FunT);
                fds <- ptree_AndFDecls andfdecls_pt;
                SOME (INR fds)
              od
            | [valtok; p_pt; eqtok; e_pt] =>
              do
                assert(tokcheckl [valtok;eqtok] [ValT; EqualsT]);
                p <- ptree_Pattern nPattern p_pt;
                e <- ptree_Expr nE e_pt;
                SOME (INL(p,e))
              od
            | _ => NONE) ∧
  (ptree_PEs (Lf _) = NONE : (pat # exp) list option) ∧
  (ptree_PEs (Nd (nt,_) args) =
    if nt <> mkNT nPEs then NONE
    else
      case args of
          [pattern_pt; arrow_pt; pe_pt] =>
          do
            assert(tokcheck arrow_pt DarrowT);
            pat <- ptree_Pattern nPattern pattern_pt;
            (e, pes) <- ptree_PE pe_pt ;
            SOME((pat,e)::pes)
          od
        | _ => NONE) ∧
  (ptree_PE (Lf _) = NONE) ∧
  (ptree_PE (Nd (nt,_) args) =
     if nt <> mkNT nPE then NONE
     else
       case args of
           [eorraise_pt; pesfx_pt] =>
           do
             assert (tokcheck eorraise_pt RaiseT);
             (e, pes) <- ptree_PE pesfx_pt;
             SOME (Raise e, pes)
           od ++
           do
             e <- ptree_Expr nElogicOR eorraise_pt;
             (handlep, pes) <- ptree_PEsfx pesfx_pt;
             SOME (if handlep then (Handle e pes, [])
                   else (e, pes))
           od
         | [fncase_tok; epat_pt; arrowof_tok; last_pt] =>
           do
             assert (tokcheckl [fncase_tok; arrowof_tok] [FnT; DarrowT]);
             pat <- ptree_Pattern nPattern epat_pt;
             e <- ptree_Expr nE last_pt;
             SOME (mkFun pat e, [])
           od ++
           do
             assert (tokcheckl [fncase_tok; arrowof_tok] [CaseT; OfT]);
             e <- ptree_Expr nE epat_pt;
             pes <- ptree_PEs last_pt;
             SOME (Mat e pes, [])
           od
         | [iftok; ge_pt; thentok; then_pt; elsetok; else_pt] =>
           do
             assert (tokcheckl [iftok; thentok; elsetok] [IfT; ThenT; ElseT]);
             ge <- ptree_Expr nE ge_pt;
             te <- ptree_Expr nE then_pt;
             (ee,rest) <- ptree_PE else_pt;
             SOME (If ge te ee, rest)
           od
         | _ => NONE) ∧
  (ptree_PEsfx (Lf _) : (bool # (pat # exp) list) option = NONE) ∧
  (ptree_PEsfx (Nd (nt,_) args) =
     if nt <> mkNT nPEsfx then NONE
     else
       case args of
           [] => SOME (F, [])
         | [handlebar_tok; pes_pt] =>
           do
             assert (tokcheck handlebar_tok HandleT);
             pes <- ptree_PEs pes_pt;
             SOME (T, pes)
           od ++
           do
             assert (tokcheck handlebar_tok BarT);
             pes <- ptree_PEs pes_pt;
             SOME (F, pes)
           od
         | _ => NONE) ∧
  (ptree_Eseq (Lf _) = NONE) ∧
  (ptree_Eseq (Nd (nt,_) args) =
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
            assert(tokcheck semi SemicolonT);
            e <- ptree_Expr nE e_pt;
            seq <- ptree_Eseq seq_pt;
            SOME(e::seq)
          od
        | _ => NONE)
End

Theorem dumb1[local]:
  COND (p = q) t e = COND (q = p) t e
Proof
  rw[]
QED
Theorem dumb2[local]:
  COND gd t NONE = OPTION_IGNORE_BIND (assert gd) t
Proof
  Cases_on ‘gd’ >> simp[]
QED
Theorem ptree_Expr_def'[local] =
  ptree_Expr_def |> ONCE_REWRITE_RULE [dumb1]
                 |> SRULE []
                 |> REWRITE_RULE[dumb2]

Theorem ptree_Expr_pevaled[compute] =
        LIST_CONJ $
           map (partial_eval ptree_Expr_def'
                             “ptree_Expr” “Nd (nt,l) args:ptree”)
           [“nEbase”, “nEtuple”,
            “nElist2”, “nElist1”, “nEapp”, “nEmult”, “nEadd”, “nElistop”,
            “nErel”, “nEcomp”, “nEbefore”, “nEtyped”, “nElogicAND”, “nElogicOR”,
            “nEhandle”, “nE”]

Theorem ptree_Expr_others[compute] =
        LIST_CONJ (List.drop (CONJUNCTS ptree_Expr_def, 2))

Definition ptree_StructName_def:
  ptree_StructName (Lf _) = NONE ∧
  ptree_StructName (Nd nm args) =
    if FST nm <> mkNT nStructName then NONE
    else
      case args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
End

Definition ptree_OptTypEqn_def:
  ptree_OptTypEqn (Lf _) = NONE : ast_t option option ∧
  ptree_OptTypEqn (Nd nt args) =
    if FST nt <> mkNT nOptTypEqn then NONE
    else
      case args of
          [] => SOME NONE
        | [eqtok; typ_pt] =>
          do
            assert (tokcheck eqtok EqualsT);
            typ <- ptree_Type nType typ_pt;
            SOME (SOME typ)
          od
        | _ => NONE
End

Definition ptree_SpecLine_def:
  ptree_SpecLine (Lf _) = NONE ∧
  ptree_SpecLine (Nd nt args) =
    if FST nt <> mkNT nSpecLine then NONE
    else
      case args of
          [td_pt] =>
          do
            td <- ptree_TypeDec td_pt;
            SOME () (* (Stype td) *)
          od
        | [exntok; dcon_pt] =>
          do
            assert (tokcheck exntok ExceptionT);
            (nm,tys) <- ptree_Dconstructor dcon_pt;
            SOME() (* (Sexn nm tys) *)
          od
        | [typetok; tynm_pt; opteqn_pt] =>
          do
            assert(tokcheck typetok TypeT);
            (vs,nm) <- ptree_TypeName tynm_pt;
            opteqn <- ptree_OptTypEqn opteqn_pt;
            SOME() (* (case opteqn of
                     NONE => Stype_opq vs nm
                   | SOME ty => Stabbrev vs nm ty) *)
          od
        | [valtok; vname_pt; coltok; type_pt] =>
          do
            assert(tokcheckl [valtok;coltok] [ValT; ColonT]);
            vname <- ptree_V vname_pt;
            ty <- ptree_Type nType type_pt;
            SOME() (* (SDefinition vname ty)*)
          od
        | _ => NONE
End

Definition ptree_SpeclineList_def:
  ptree_SpeclineList (Lf _) = NONE ∧
  ptree_SpeclineList (Nd nt args) =
    if FST nt <> mkNT nSpecLineList then NONE
    else
      case args of
          [] => SOME () (* [] *)
        | [sl_pt; sll_pt] =>
          if tokcheck sl_pt SemicolonT then ptree_SpeclineList sll_pt
          else
            do
              sl <- ptree_SpecLine sl_pt;
              sll <- ptree_SpeclineList sll_pt;
              SOME () (* (sl::sll) *)
            od
        | _ => NONE
End

Definition ptree_SignatureValue_def:
  ptree_SignatureValue (Lf _) = NONE ∧
  ptree_SignatureValue (Nd nt args) =
    if FST nt <> mkNT nSignatureValue then NONE
    else
      case args of
          [sigtok; sll_pt; endtok] =>
          do
            assert(tokcheckl [sigtok; endtok] [SigT; EndT]);
            ptree_SpeclineList sll_pt
          od
        | _ => NONE
End

Definition ptree_Decl_def:
  (ptree_Decl pt : dec option =
    case pt of
       Lf _ => NONE
     | Nd (nt,locs) args =>
       if nt <> mkNT nDecl then NONE
       else
         case args of
             [dt] =>
             do
               tydec <- ptree_TypeDec dt;
               SOME (Dtype (locs) tydec)
             od ++ ptree_TypeAbbrevDec dt ++ ptree_Structure dt
           | [funtok; fdecls] =>
             do
               assert(tokcheck funtok FunT);
               fdecs <- ptree_AndFDecls fdecls;
               SOME (Dletrec (locs) fdecs)
             od ++
             do
               assert (tokcheck funtok ExceptionT);
               (enm, etys) <- ptree_Dconstructor fdecls;
               SOME (Dexn (locs) enm etys)
             od
           | [valtok; patpt; eqtok; ept] =>
             do
               assert (tokcheckl [valtok; eqtok] [ValT; EqualsT]);
               pat <- ptree_Pattern nPattern patpt;
               e <- ptree_Expr nE ept;
               SOME (Dlet (locs) pat e)
             od
           | [localtok; decls1_pt; intok; decls2_pt; endtok] =>
             do
               assert (tokcheckl [localtok; intok; endtok] [LocalT; InT; EndT]);
               decls1 <- ptree_Decls decls1_pt;
               decls2 <- ptree_Decls decls2_pt;
               return (Dlocal decls1 decls2)
             od
           | _ => NONE) /\
  ptree_Decls (Lf _) = NONE ∧
  (ptree_Decls (Nd (nt,_) args) =
    if nt <> mkNT nDecls then NONE
    else
      case args of
          [] => SOME []
        | [d_pt; ds_pt] =>
          if tokcheck d_pt SemicolonT then ptree_Decls ds_pt
          else
            do
              d <- ptree_Decl d_pt;
              ds <- ptree_Decls ds_pt;
              SOME(d::ds)
            od
        | _ => NONE) ∧
  ptree_Structure (Lf _) = NONE ∧
  ptree_Structure (Nd nt args) =
    if FST nt <> mkNT nStructure then NONE
    else
      case args of
          [structuretok; sname_pt; asc_opt; eqtok; structtok; ds_pt; endtok] =>
          do
            assert(tokcheckl [structtok; structuretok; eqtok;   endtok]
                             [StructT;   StructureT;   EqualsT; EndT]);
            sname <- ptree_StructName sname_pt;
            asc <- case asc_opt of
                       Lf _ => NONE
                     | Nd nt args =>
                         if FST nt <> mkNT nOptionalSignatureAscription then
                           NONE
                         else
                           case args of
                               [] => SOME NONE
                             | [sealtok; sig_pt] =>
                               do
                                 assert(tokcheck sealtok SealT);
                                 sigv <- ptree_SignatureValue sig_pt;
                                 SOME (SOME sigv)
                               od
                             | _ => NONE;
            ds <- ptree_Decls ds_pt;
            SOME(Dmod sname (*asc*) ds)
          od
        | _ => NONE
End

Definition ptree_TopLevelDecs_def:
  ptree_TopLevelDecs (Lf _) = fail ∧
  (ptree_TopLevelDecs (Nd nt args) =
     if FST nt <> mkNT nTopLevelDecs then fail
     else
       case args of
           [] => return []
         | [td_pt; tds_pt] =>
           if tokcheck td_pt SemicolonT then ptree_TopLevelDecs tds_pt
           else
             do
               td <- ptree_Decl td_pt;
               tds <- ptree_NonETopLevelDecs tds_pt;
               return(td::tds)
             od
         | [e_pt; semitok; tds_pt] =>
           do
             assert (tokcheck semitok SemicolonT);
             e <- ptree_Expr nE e_pt;
             tds <- ptree_TopLevelDecs tds_pt;
             return (Dlet (SND nt) (Pvar «it») e :: tds)
           od
         | _ => NONE) ∧
  (ptree_NonETopLevelDecs (Lf _) = fail) ∧
  (ptree_NonETopLevelDecs (Nd nt args) =
     if FST nt <> mkNT nNonETopLevelDecs then fail
     else
       case args of
         [] => return []
       | [pt1 ; pt2] =>
         if tokcheck pt1 SemicolonT then ptree_TopLevelDecs pt2
         else
           do
             td <- ptree_Decl pt1 ;
             tds <- ptree_NonETopLevelDecs pt2 ;
             return (td :: tds)
           od
       | _ => fail)
End
