(*
  Specification of how to convert parse trees to abstract syntax.
*)

open preamble gramTheory tokenUtilsTheory astTheory

val _ = new_theory "cmlPtreeConversion"

val _ = set_grammar_ancestry ["gram", "tokenUtils", "ast", "namespace"]
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* handling constructor arities gets very complicated when "open" is
   implemented *)
val _ = Datatype`PCstate0 = <| fixities : string |-> num option ;
                               ctr_arities : (string, string) id |-> num |>`
(* recording a fixity of NONE is what you have to do to represent an
   explicit nonfix declaration *)

val _ = temp_type_abbrev
            ("M", ``:PCstate0 list -> ('a # PCstate0 list) option``)

val empty_PCstate0 = Define`
  empty_PCstate0 = <| fixities := FEMPTY ; ctr_arities := FEMPTY |>
`;

val mpushPC_scope_def = Define`
  mpushPC_scope : unit M = λpcs. SOME ((), empty_PCstate0 :: pcs)
`;

val fixity_lookup_def = Define`
  fixity_lookup nm pcs =
    dtcase pcs of
        [] => NONE
      | pc0 :: rest =>
          dtcase FLOOKUP pc0.fixities nm of
              NONE => fixity_lookup nm rest
            | SOME NONE => NONE
            | SOME r => r
`;


(* mfixity_lookup : string -> num M
    'fails' if the string has no fixity, even though it is perfectly
    reasonable for a string to be nonfix.
*)
val mfixity_lookup_def = Define`
  mfixity_lookup nm : num M =
    λpcs. OPTION_MAP (λr. (r, pcs)) (fixity_lookup nm pcs)
`

val mFUPD_HD_def = Define`
  mFUPD_HD f pcs =
    dtcase pcs of
        [] => NONE
      | h :: t => SOME((), f h :: t)
`

(* msetfix : string -> num option -> unit M *)
val msetfix_def = Define`
  msetfix nm fix : unit M =
    mFUPD_HD (λs0. s0 with fixities updated_by (λfm. fm |+ (nm, fix)))
`

(* mpop_anonscope : unit M *)
val mpop_anonscope_def = Define`
  mpopscope : unit M = λpcs.
    dtcase pcs of
      [] => NONE
    | _ :: t => SOME((), t)
`

val mpop_namedscope_def = Define`
  mpop_namedscope (s : string) : unit M = λpcs.
    dtcase pcs of
      [] => NONE
    | [_] => NONE
    | curr :: next :: rest => SOME((), next :: rest)
`;
(* needs to be adjusted so that constructors (only) declared in the current
   scope get recorded in the next level up with the given name as a prefix.

   Does nothing different at this stage, when I expect just to be handling
   fixities (which are handled in a non-exportable way).
 *)


(* ----------------------------------------------------------------------
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------- *)

val _ = option_monadsyntax.temp_add_option_monadsyntax();
val _ = temp_overload_on ("lift", ``option$OPTION_MAP``)

val ifM_def = Define`
  ifM bM tM eM =
    do
       b <- bM;
       if b then tM else eM
    od
`

val mk_binop_def = Define`
  mk_binop a_op a1 a2 =
    if a_op = Short "::" then Con (SOME (Short "::")) [a1; a2]
    else App Opapp [App Opapp [Var a_op; a1]; a2]
`

val _ = temp_overload_on ("'", ``λf a. OPTION_BIND a f``);
val tokcheck_def = Define`
  tokcheck pt tok <=> (destTOK ' (destLf pt) = SOME tok)
`;

val ptree_UQTyop_def = Define`
  ptree_UQTyop (Lf _) = NONE ∧
  ptree_UQTyop (Nd nt args) =
    if FST nt <> mkNT nUQTyOp then NONE
    else
      dtcase args of
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
    if FST nt <> mkNT nTyvarN then NONE
    else
      dtcase args of
          [tyv] => destTyvarPT tyv
        | _ => NONE
`;


val ptree_Tyop_def = Define`
  ptree_Tyop (Lf _) = NONE ∧
  ptree_Tyop (Nd nt args) =
    if FST nt <> mkNT nTyOp then NONE
    else
      dtcase args of
          [pt] =>
          do
            (str,s) <- destLongidT ' (destTOK ' (destLf pt));
            SOME(Long str (Short s))
          od ++
          do
            nm <- ptree_UQTyop pt;
            SOME(Short nm)
          od
        | _ => NONE
`;

val tokcheckl_def = Define`
  tokcheckl pts toks <=>
    dtcase (pts,toks) of
      ([],[]) => T
    | (pt::prest, tok::tokrest) => tokcheck pt tok ∧ tokcheckl prest tokrest
    | _ => F
`

val ptree_linfix_def = Define`
  ptree_linfix topnt opn elnt (pt : mlptree) =
    dtcase pt of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt = mkNT topnt then
          dtcase args of
              [pt] => do e <- elnt pt; SOME [e] od
            | [top; op_pt; pt] => do
                assert(tokcheck op_pt opn);
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
  tuplify tys = SOME(Attup tys)
`

val ptree_Type_def = Define`
  (ptree_Type nt (Lf _) : ast_t option = NONE) ∧
  (ptree_Type nm (Nd nt args) =
     if FST nt <> mkNT nm then NONE
     else if nm = nType then
       dtcase args of
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
       dtcase args of
           [pt] => ptree_Type nTbase pt
         | [dt; opn] => do
                          dty <- ptree_Type nDType dt;
                          opname <- ptree_Tyop opn;
                          SOME(Atapp [dty] opname)
                        od
         | _ => NONE
     else if nm = nTbase then
       dtcase args of
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
     dtcase ptree of
       Lf _ => NONE
     | Nd nt args =>
       if FST nt <> mkNT nTypeList2 then NONE
       else
         dtcase args of
           | [dt; commat; tl'] =>
             do
               assert(tokcheck commat CommaT);
               ty <- ptree_Type nType dt;
               tylist <- ptree_TypeList1 tl';
               SOME(ty::tylist)
             od
           | _ => NONE) ∧
  (ptree_TypeList1 ptree : ast_t list option =
    dtcase ptree of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt <> mkNT nTypeList1 then NONE
        else
          dtcase args of
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
     dtcase ptree of
         Lf _ => NONE
       | Nd nt args =>
         if FST nt <> mkNT nPType then NONE
         else
           dtcase args of
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
`;

val ptree_TypeName_def = Define`
  ptree_TypeName ptree : (tvarN list # typeN) option =
    dtcase ptree of
      Lf _ => NONE
    | Nd nt args =>
      if FST nt = mkNT nTypeName then
        dtcase args of
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
`;

val ptree_UQConstructorName_def = Define`
  ptree_UQConstructorName (Lf _) = NONE ∧
  ptree_UQConstructorName (Nd nm args) =
    if FST nm <> mkNT nUQConstructorName then NONE
    else
      dtcase args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
`

val ptree_ConstructorName_def = Define`
  ptree_ConstructorName ast =
    dtcase ast of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt <> mkNT nConstructorName then NONE
        else
          dtcase args of
              [pt] =>
              do
                s <- ptree_UQConstructorName pt;
                SOME (Short s)
              od ++
              do
                (str,s) <- destLongidT ' (destTOK ' (destLf pt));
                SOME (Long str (Short s))
              od
            | _ => NONE
`

val detuplify_def = Define`
  detuplify (Attup args) = args ∧
  detuplify ty = [ty]
`

Theorem detuplify_pmatch `!ty.
  detuplify ty =
  case ty of
    Attup args => args
  | ty => [ty]`
  (ho_match_mp_tac (theorem "detuplify_ind")
  >> fs[detuplify_def]);

val ptree_PTbase_def = Define‘
  ptree_PTbase ast =
    dtcase ast of
        Lf _ => fail
      | Nd nt args =>
        if FST nt = mkNT nPTbase then
          dtcase args of
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
’;

val ptree_TbaseList_def = Define‘
  ptree_TbaseList ast =
    dtcase ast of
        Lf _ => fail
      | Nd nt args =>
        if FST nt = mkNT nTbaseList then
          dtcase args of
              [] => return []
            | [ptb_pt;rest_pt] => do
                b <- ptree_PTbase ptb_pt ;
                rest <- ptree_TbaseList rest_pt ;
                return (b::rest)
              od
            | _ => fail
        else fail
’;

val ptree_Dconstructor_def = Define`
  ptree_Dconstructor ast =
    dtcase ast of
        Lf x => NONE
      | Nd nt args =>
        if FST nt = mkNT nDconstructor then
          dtcase args of
              [] => NONE
            | t::ts =>
              do
                 cname <- ptree_UQConstructorName t;
                 types <- dtcase ts of
                               [blist] =>
                               do
                                 args <- ptree_TbaseList blist ;
                                 return args
                               od
                             | _ => NONE;
                 SOME(cname, types)
              od
        else NONE
`;

val ptree_DtypeDecl_def = Define`
  ptree_DtypeDecl (pt : mlptree) =
    dtcase pt of
        Lf _ => NONE
      | Nd nt args =>
        if FST nt = mkNT nDtypeDecl then
          dtcase args of
              [tynm_pt; eqt; dtc_pt] => do
                assert(tokcheck eqt EqualsT);
                tynm <- ptree_TypeName tynm_pt;
                dtc <- ptree_linfix nDtypeCons BarT ptree_Dconstructor dtc_pt;
                SOME(FST tynm,SND tynm,dtc)
              od
            | _ => NONE
        else NONE
`;

val ptree_TypeDec_def = Define`
  ptree_TypeDec ptree : type_def option =
    dtcase ptree of
      Lf _ => NONE
    | Nd nt args =>
      if FST nt = mkNT nTypeDec then
        dtcase args of
            [datatype_pt; pt] => do
              assert(tokcheck datatype_pt DatatypeT);
              ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt
            od
          | _ => NONE
      else NONE`;

val ptree_TypeAbbrevDec_def = Define`
  ptree_TypeAbbrevDec ptree : dec option =
    dtcase ptree of
      Lf _ => NONE
    | Nd nt args =>
      if FST nt = mkNT nTypeAbbrevDec then
        dtcase args of
          [typetok; tynm ; eqtok ; typ_pt] => do
            assert(tokcheck typetok TypeT ∧ tokcheck eqtok EqualsT) ;
            (vars, nm) <- ptree_TypeName tynm;
            typ <- ptree_Type nType typ_pt;
            SOME(Dtabbrev (SND nt) vars nm typ)
          od
        | _ => NONE
      else NONE
`

val ptree_Op_def = Define`
  ptree_Op (Lf _) = NONE ∧
  ptree_Op (Nd nt subs) =
    if FST nt = mkNT nMultOps then
      if tokcheckl subs [StarT] then SOME (Short "*")
      else if tokcheckl subs [SymbolT "/"] then SOME (Short "/")
      else if tokcheckl subs [AlphaT "mod"] then SOME (Short "mod")
      else if tokcheckl subs [AlphaT "div"] then SOME (Short "div")
      else NONE
    else if FST nt = mkNT nAddOps then
      if tokcheckl subs [SymbolT "+"] then SOME (Short "+")
      else if tokcheckl subs [SymbolT "-"] then SOME (Short "-")
      else if tokcheckl subs [SymbolT "\094"] then SOME (Short "\094")
      else NONE
    else if FST nt = mkNT nListOps then
      if tokcheckl subs [SymbolT "::"] then SOME (Short "::")
      else if tokcheckl subs [SymbolT "@"] then SOME (Short "@")
      else NONE
    else if FST nt = mkNT nRelOps then
      dtcase subs of
          [pt] =>
          do
            s <- destSymbolT ' (destTOK ' (destLf pt));
            SOME (Short s)
          od ++
          do
            assert(tokcheck pt EqualsT);
            SOME(Short "=")
          od
        | _ => NONE
    else if FST nt = mkNT nCompOps then
      if tokcheckl subs [SymbolT ":="] then SOME (Short ":=")
      else if tokcheckl subs [AlphaT "o"] then SOME (Short "o")
      else NONE
    else NONE
`;

val ptree_V_def = Define`
  ptree_V (Lf _) = NONE ∧
  ptree_V (Nd nt subs) =
       do
         assert (FST nt = mkNT nV) ;
         dtcase subs of
            [pt] => do t <- destTOK ' (destLf pt) ;
                       destAlphaT t ++ destSymbolT t
                    od
          | _ => NONE
       od
`;

val ptree_FQV_def = Define`
  ptree_FQV (Lf _) = NONE ∧
  ptree_FQV (Nd nt args) =
    if FST nt <> mkNT nFQV then NONE
    else
      dtcase args of
          [pt] => OPTION_MAP Short (ptree_V pt) ++
                  do
                    (str,s) <- destLongidT ' (destTOK ' (destLf pt));
                    SOME(Long str (Short s))
                  od
        | _ => NONE
`

val isSymbolicConstructor_def = Define`
  isSymbolicConstructor (structopt : modN option) s =
    return (s = "::")
`;

val isConstructor_def = Define`
  isConstructor structopt s =
    do
      ifM (isSymbolicConstructor structopt s)
        (return T)
        (return (dtcase oHD s of NONE => F | SOME c => isAlpha c ∧ isUpper c))
    od
`;

(* third clause below will lead to a failure when the environment is
   consulted to reveal that the long-id given does not correspond to a
   constructor.  We do this rather than fail to make the "totality" theorem
   work *)
val EtoPat_def = Define`
  (EtoPat (Con x args) = if NULL args then SOME (Pcon x []) else NONE) ∧
  (EtoPat (Var (Short n)) = SOME (Pvar n)) ∧
  (EtoPat (Var (Long str n)) = SOME (Pcon (SOME (Long str n)) [])) ∧
  (EtoPat _ = NONE)
`;

val ptree_OpID_def = Define`
  ptree_OpID (Lf _) = NONE ∧
  ptree_OpID (Nd nt subs) =
    if FST nt ≠ mkNT nOpID then NONE
    else
      dtcase subs of
          [Lf (TK tk, _)] =>
          do
              s <- destAlphaT tk ;
              ifM (isConstructor NONE s)
                  (return (Con (SOME (Short s)) []))
                  (return (Var (Short s)))
          od ++
          do
              s <- destSymbolT tk ;
              ifM (isSymbolicConstructor NONE s)
                  (return (Con (SOME (Short s)) []))
                  (return (Var (Short s)))
          od ++
          do
              (str,s) <- destLongidT tk ;
              ifM (isConstructor (SOME str) s)
                  (return (Con (SOME (Long str (Short s))) []))
                  (return (Var (Long str (Short s))))
          od ++
          (if tk = StarT then
             ifM (isSymbolicConstructor NONE "*")
                 (return (Con (SOME (Short "*")) []))
                 (return (Var (Short "*")))
           else if tk = EqualsT then return (Var (Short "="))
           else NONE)
        | _ => NONE
`;

val Papply_def = Define`
  Papply pat arg =
    dtcase pat of
      Pcon cn args => Pcon cn (args ++ [arg])
    | _ => pat
`;

val maybe_handleRef_def = Define‘
  maybe_handleRef (Pcon (SOME (Short "Ref")) [pat]) = Pref pat ∧
  maybe_handleRef p = p
’;

val ptree_Pattern_def = Define`
  (ptree_Pattern nt (Lf _) = NONE) ∧
  (ptree_Pattern nt (Nd nm args) =
    if mkNT nt <> FST nm then NONE
    else if FST nm = mkNT nPbase then
      dtcase args of
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
            SOME(Pcon (SOME (Short "[]")) [])
          else if tokcheckl [lb] [OpT] then
            do e <- ptree_OpID rb ; EtoPat e od
          else NONE
        | [lb; plistpt; rb] =>
          do
            assert (tokcheckl [lb;rb] [LbrackT; RbrackT]);
            plist <- ptree_Plist plistpt;
            SOME (FOLDR (λp a. Pcon (SOME (Short "::")) [p; a])
                        (Pcon (SOME (Short "[]")) [])
                        plist)
          od
        | _ => NONE
    else if FST nm = mkNT nPConApp then
      dtcase args of
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
      dtcase args of
          [pb] => ptree_Pattern nPbase pb
        | [capp_pt; ppt] =>
          do
            capp <- ptree_Pattern nPConApp capp_pt;
            b <- ptree_Pattern nPbase ppt;
            return (maybe_handleRef (Papply capp b))
          od
        | _ => NONE
    else if FST nm = mkNT nPcons then
      dtcase args of
          [papt] => ptree_Pattern nPapp papt
        | [papt; cons_t; pcons_pt] =>
          do
            assert (tokcheck cons_t (SymbolT "::"));
            pa <- ptree_Pattern nPapp papt;
            patt <- ptree_Pattern nPcons pcons_pt;
            SOME(Pcon (SOME (Short "::")) [pa; patt])
          od
        | _ => NONE
    else if FST nm = mkNT nPattern then
      dtcase args of
          [pcons] => ptree_Pattern nPcons pcons
        | [pcons_pt; colon_t; type_pt] =>
          do
            assert (tokcheck colon_t ColonT);
            pc <- ptree_Pattern nPcons pcons_pt;
            ty <- ptree_Type nType type_pt;
            return (Ptannot pc ty)
          od
        | _ => fail
    else if FST nm = mkNT nPtuple then
      dtcase args of
          [lp; rp] => do assert (tokcheckl [lp;rp] [LparT; RparT]);
                         return (Pcon NONE [])
                      od
        | [lp; pl_pt; rp] =>
          do
            assert (tokcheckl [lp;rp] [LparT; RparT]);
            pl <- ptree_Plist pl_pt;
            dtcase pl of
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
       dtcase args of
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
`;

val ptree_PbaseList1_def = Define`
  (ptree_PbaseList1 (Lf _) = NONE) ∧
  (ptree_PbaseList1 (Nd nm args) =
     if FST nm <> mkNT nPbaseList1 then NONE
     else
       dtcase args of
           [p_pt] => lift SINGL (ptree_Pattern nPbase p_pt)
         | [p_pt; pl_pt] =>
               lift2 CONS
                     (ptree_Pattern nPbase p_pt)
                     (ptree_PbaseList1 pl_pt)
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

val dest_Conk_def = Define`
  (dest_Conk (Con x y) k v = k x y) /\
  (dest_Conk _ k v = v)
`;

val destFFIop_def = Define`
  (destFFIop (FFI s) = SOME s) ∧
  (destFFIop _ = NONE)
`;
val _ = export_rewrites ["destFFIop_def"]

val strip_loc_expr_def = Define`
 (strip_loc_expr (Lannot e l) =
    dtcase (strip_loc_expr e) of
      (e0, _) => (e0, SOME l)) ∧
 (strip_loc_expr e = (e, NONE))
`

val merge_locsopt_def = Define`
  merge_locsopt (SOME l1) (SOME l2) = SOME (merge_locs l1 l2) ∧
  merge_locsopt _ _ = NONE
`;

val optLannot_def = Define`
  optLannot NONE e = e ∧
  optLannot (SOME l) e = Lannot e l
`;

val mkAst_App_def = Define`
  mkAst_App a1 a2 =
    let (a10, loc1) = strip_loc_expr a1
    in
      dest_Conk a10
        (λnm_opt args.
          if nm_opt = SOME (Short "Ref") ∧ NULL args then App Opref [a2]
          else
            let (a2', loc2) = strip_loc_expr a2
            in
              optLannot (merge_locsopt loc1 loc2) (Con nm_opt (args ++ [a2'])))
        (dtcase a10 of
           App opn args =>
             (dtcase (destFFIop opn) of
                NONE => App Opapp [a1;a2]
              | SOME s => App opn (args ++ [a2]))
         | _ => App Opapp [a1;a2])
`;


val dePat_def = Define`
  (dePat (Pvar v) b = (v, b)) ∧
  (dePat p b = ("", Mat (Var (Short "")) [(p, b)]))
`

val mkFun_def = Define`
  mkFun p b = UNCURRY Fun (dePat p b)
`

val ptree_Eliteral_def = Define`
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
`

val bind_loc_def = Define`
  bind_loc (Lannot e l) l' = Lannot e l /\
  bind_loc e l = Lannot e l
`

val letFromPat_def = Define‘
  letFromPat p rhs body =
    dtcase p of
      Pany => Let NONE rhs body
    | Pvar v => Let (SOME v) rhs body
    | _ => Mat rhs [(p,body)]
’;

local
  val ptree_Expr_quotation = `
  ptree_Expr ent (Lf _) = NONE ∧
  ptree_Expr ent (Nd (nt,loc) subs) =
  do
  e <- (if mkNT ent = nt then
      if nt = mkNT nEbase then
        dtcase subs of
            [lpart; pt; rpart] =>
            do
              assert(tokcheckl [lpart; rpart] [LparT; RparT]);
              eseq <- ptree_Eseq pt;
              Eseq_encode eseq
            od ++
            do
              assert(tokcheckl [lpart;rpart][LbrackT; RbrackT]);
              elist <- ptree_Exprlist nElist1 pt;
              SOME(FOLDR (λe acc. Con (SOME (Short "::")) [e; acc])
                         (Con (SOME (Short "[]")) [])
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
                         SOME (Con (SOME (Short "[]")) [])
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
              SOME(FOLDR (λdf acc. dtcase df of
                                       INL (p,e0) => letFromPat p e0 acc
                                     | INR fds => Letrec fds acc)
                         e
                         letdecs)
            od
          | _ => NONE
      else if nt = mkNT nEapp then
        dtcase subs of
            [t1; t2] => do
                          a1 <- ptree_Expr nEapp t1;
                          a2 <- ptree_Expr nEbase t2;
                          SOME(mkAst_App a1 a2)
                        od
          | [t] => ptree_Expr nEbase t
          | _ => NONE
      else if nt = mkNT nEtuple then
        dtcase subs of
            [lpart; el2; rpart] =>
            do
              assert (tokcheckl [lpart; rpart] [LparT; RparT]);
              es <- ptree_Exprlist nElist2 el2;
              SOME(Con NONE es)
            od
          | _ => NONE
      else if nt = mkNT nEmult then
        dtcase subs of
          [t1; opt; t2] => do (* s will be *, /, div, or mod *)
            a1 <- ptree_Expr nEmult t1;
            a_op <- ptree_Op opt;
            a2 <- ptree_Expr nEapp t2;
            return(mk_binop a_op a1 a2)
          od
        | [t] => ptree_Expr nEapp t
        | _ => NONE
      else if nt = mkNT nEadd then
        dtcase subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nEmult t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nEmult t
          | _ => NONE
      else if nt = mkNT nElistop then
        dtcase subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEadd t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nElistop t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nEadd t
          | _ => NONE
      else if nt = mkNT nErel then
        dtcase subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nErel t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nElistop t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nElistop t
          | _ => NONE
      else if nt = mkNT nEcomp then
        dtcase subs of
            [t1;opt;t2] => do
              a1 <- ptree_Expr nEcomp t1;
              a_op <- ptree_Op opt;
              a2 <- ptree_Expr nErel t2;
              return (mk_binop a_op a1 a2)
            od
          | [t] => ptree_Expr nErel t
          | _ => NONE
      else if nt = mkNT nEbefore then
        dtcase subs of
          [t1;opt;t2] => do
            assert(tokcheck opt (AlphaT "before"));
            a1 <- ptree_Expr nEbefore t1;
            a2 <- ptree_Expr nEcomp t2;
            return (mk_binop (Short "before") a1 a2)
          od
        | [t] => ptree_Expr nEcomp t
        | _ => NONE
      else if nt = mkNT nEtyped then
        dtcase subs of
          [e_pt; colon; ty_pt] => do
            assert(tokcheck colon ColonT);
            e <- ptree_Expr nEbefore e_pt;
            ty <- ptree_Type nType ty_pt;
            return (Tannot e ty)
          od
        | [t] => ptree_Expr nEbefore t
        | _ => NONE
      else if nt = mkNT nElogicAND then
        dtcase subs of
            [t1;andt;t2] => do
              assert(tokcheck andt AndalsoT);
              a1 <- ptree_Expr nElogicAND t1;
              a2 <- ptree_Expr nEtyped t2;
              SOME(Log And a1 a2)
            od
          | [t] => ptree_Expr nEtyped t
          | _ => NONE
      else if nt = mkNT nElogicOR then
        dtcase subs of
            [t1;ort;t2] => do
              assert(tokcheck ort OrelseT);
              a1 <- ptree_Expr nElogicOR t1;
              a2 <- ptree_Expr nElogicAND t2;
              SOME (Log Or a1 a2)
            od
          | [t] => ptree_Expr nElogicAND t
          | _ => NONE
      else if nt = mkNT nEhandle then
        dtcase subs of
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
        dtcase subs of
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
      else if nt = mkNT nE' then
        dtcase subs of
          | [t] => ptree_Expr nElogicOR t
          | [raiset; ept] =>
            do
              assert(tokcheck raiset RaiseT);
              e <- ptree_Expr nE' ept;
              SOME(Raise e)
            od
          | [fnt; vnt; arrowt; ent] =>
            do
              assert (tokcheckl [fnt; arrowt] [FnT; DarrowT]);
              v <- ptree_V vnt;
              e <- ptree_Expr nE' ent;
              SOME(Fun v e)
            od
          | [ift;g;thent;te;elset;ee] => do
              assert(tokcheckl [ift; thent; elset] [IfT; ThenT; ElseT]);
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE' ee;
              SOME(If a1 a2 a3)
            od
          | _ => NONE
      else NONE
    else NONE);
    SOME(bind_loc e loc)
  od  ∧
  (ptree_Exprlist nm ast =
     dtcase ast of
         Lf _ => NONE
       | Nd (nt,_) subs =>
         if nt = mkNT nElist1 then
           dtcase subs of
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
           dtcase subs of
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
    (dtcase ast of
        Lf _ => NONE
      | Nd (nt,_) subs =>
        if nt = mkNT nAndFDecls then
          dtcase subs of
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
    dtcase ast of
        Lf _ => NONE
      | Nd (nt,_) subs =>
        if nt = mkNT nFDecl then
          dtcase subs of
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
    dtcase ptree of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt <> mkNT nLetDecs then NONE
        else
          dtcase args of
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
    dtcase ptree of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt <> mkNT nLetDec then NONE
        else
          dtcase args of
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
  (ptree_PEs (Lf _) = NONE) ∧
  (ptree_PEs (Nd (nt,_) args) =
    if nt <> mkNT nPEs then NONE
    else
      dtcase args of
          [single] =>
          do
            pe <- ptree_PE single;
            SOME [pe]
          od
        | [pe'_pt; bartok; pes_pt] =>
          do
            assert(tokcheck bartok BarT);
            pes <- ptree_PEs pes_pt;
            pe <- ptree_PE' pe'_pt;
            SOME(pe::pes)
          od
        | _ => NONE) ∧
  (ptree_PE (Lf _) = NONE) ∧
  (ptree_PE (Nd (nt,_) args) =
     if nt <> mkNT nPE then NONE
     else
       dtcase args of
           [p_pt; arrow; e_pt] =>
           do
             assert(tokcheck arrow DarrowT);
             p <- ptree_Pattern nPattern p_pt;
             e <- ptree_Expr nE e_pt;
             SOME(p,e)
           od
         | _ => NONE) ∧
  (ptree_PE' (Lf _) = NONE) ∧
  (ptree_PE' (Nd (nt,_) args) =
     if nt <> mkNT nPE' then NONE
     else
       dtcase args of
           [p_pt; arrow; e'_pt] =>
           do
             assert(tokcheck arrow DarrowT);
             p <- ptree_Pattern nPattern p_pt;
             e <- ptree_Expr nE' e'_pt;
             SOME(p,e)
           od
         | _ => NONE) ∧
  (ptree_Eseq (Lf _) = NONE) ∧
  (ptree_Eseq (Nd (nt,_) args) =
    if nt <> mkNT nEseq then NONE
    else
      dtcase args of
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
`;
in

val ptree_Expr_def = Define ptree_Expr_quotation
(*
val ptree_Expr_pmatch = Q.store_thm("ptree_decl_pmatch",
  (ptree_Expr_quotation |>
   map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
       | aq => aq)),
  rpt strip_tac
  >> TRY(CONV_TAC patternMatchesLib.PMATCH_LIFT_BOOL_CONV)
  >> rpt strip_tac
  >> fs[Once ptree_Expr_def] >> every_case_tac >> fs[]
  >> TRY(CONV_TAC patternMatchesLib.PMATCH_LIFT_BOOL_CONV)
  >> rpt strip_tac);
*)
end

val ptree_Decl_def = Define`
  (ptree_Decl pt : dec option =
    dtcase pt of
       Lf _ => NONE
     | Nd (nt,locs) args =>
       if nt <> mkNT nDecl then NONE
       else
         dtcase args of
             [dt] =>
             do
               tydec <- ptree_TypeDec dt;
               SOME (Dtype (locs) tydec)
             od ++ ptree_TypeAbbrevDec dt
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
  ptree_Decls (Nd (nt,_) args) =
    if nt <> mkNT nDecls then NONE
    else
      dtcase args of
          [] => SOME []
        | [d_pt; ds_pt] =>
          if tokcheck d_pt SemicolonT then ptree_Decls ds_pt
          else
            do
              d <- ptree_Decl d_pt;
              ds <- ptree_Decls ds_pt;
              SOME(d::ds)
            od
        | _ => NONE
`

val ptree_OptTypEqn_def = Define`
  ptree_OptTypEqn (Lf _) = NONE : ast_t option option ∧
  ptree_OptTypEqn (Nd nt args) =
    if FST nt <> mkNT nOptTypEqn then NONE
    else
      dtcase args of
          [] => SOME NONE
        | [eqtok; typ_pt] =>
          do
            assert (tokcheck eqtok EqualsT);
            typ <- ptree_Type nType typ_pt;
            SOME (SOME typ)
          od
        | _ => NONE
`

val ptree_SpecLine_def = Define`
  ptree_SpecLine (Lf _) = NONE ∧
  ptree_SpecLine (Nd nt args) =
    if FST nt <> mkNT nSpecLine then NONE
    else
      dtcase args of
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
            SOME() (* (dtcase opteqn of
                     NONE => Stype_opq vs nm
                   | SOME ty => Stabbrev vs nm ty) *)
          od
        | [valtok; vname_pt; coltok; type_pt] =>
          do
            assert(tokcheckl [valtok;coltok] [ValT; ColonT]);
            vname <- ptree_V vname_pt;
            ty <- ptree_Type nType type_pt;
            SOME() (* (Sval vname ty)*)
          od
        | _ => NONE
`

val ptree_SpeclineList_def = Define`
  ptree_SpeclineList (Lf _) = NONE ∧
  ptree_SpeclineList (Nd nt args) =
    if FST nt <> mkNT nSpecLineList then NONE
    else
      dtcase args of
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
`

val ptree_SignatureValue_def = Define`
  ptree_SignatureValue (Lf _) = NONE ∧
  ptree_SignatureValue (Nd nt args) =
    if FST nt <> mkNT nSignatureValue then NONE
    else
      dtcase args of
          [sigtok; sll_pt; endtok] =>
          do
            assert(tokcheckl [sigtok; endtok] [SigT; EndT]);
            ptree_SpeclineList sll_pt
          od
        | _ => NONE
`;

val ptree_StructName_def = Define`
  ptree_StructName (Lf _) = NONE ∧
  ptree_StructName (Nd nm args) =
    if FST nm <> mkNT nStructName then NONE
    else
      dtcase args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
`

val ptree_Structure_def = Define`
  ptree_Structure (Lf _) = NONE ∧
  ptree_Structure (Nd nt args) =
    if FST nt <> mkNT nStructure then NONE
    else
      dtcase args of
          [structuretok; sname_pt; asc_opt; eqtok; structtok; ds_pt; endtok] =>
          do
            assert(tokcheckl [structtok; structuretok; eqtok;   endtok]
                             [StructT;   StructureT;   EqualsT; EndT]);
            sname <- ptree_StructName sname_pt;
            asc <- dtcase asc_opt of
                       Lf _ => NONE
                     | Nd nt args =>
                         if FST nt <> mkNT nOptionalSignatureAscription then
                           NONE
                         else
                           dtcase args of
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
`

val ptree_TopLevelDec_def = Define`
  ptree_TopLevelDec (Lf _) = NONE ∧
  ptree_TopLevelDec (Nd nt args) =
    if FST nt <> mkNT nTopLevelDec then NONE
    else
      dtcase args of
          [pt] =>
            ptree_Structure pt ++ (ptree_Decl pt)
        | _ => NONE
`

val ptree_TopLevelDecs_def = Define`
  ptree_TopLevelDecs (Lf _) = fail ∧
  (ptree_TopLevelDecs (Nd nt args) =
     if FST nt <> mkNT nTopLevelDecs then fail
     else
       dtcase args of
           [] => return []
         | [td_pt; tds_pt] =>
           if tokcheck td_pt SemicolonT then ptree_TopLevelDecs tds_pt
           else
             do
               td <- ptree_TopLevelDec td_pt;
               tds <- ptree_NonETopLevelDecs tds_pt;
               return(td::tds)
             od
         | [e_pt; semitok; tds_pt] =>
           do
             assert (tokcheck semitok SemicolonT);
             e <- ptree_Expr nE e_pt;
             tds <- ptree_TopLevelDecs tds_pt;
             return (Dlet (SND nt) (Pvar "it") e :: tds)
           od
         | _ => NONE) ∧
  (ptree_NonETopLevelDecs (Lf _) = fail) ∧
  (ptree_NonETopLevelDecs (Nd nt args) =
     if FST nt <> mkNT nNonETopLevelDecs then fail
     else
       dtcase args of
         [] => return []
       | [pt1 ; pt2] =>
         if tokcheck pt1 SemicolonT then ptree_TopLevelDecs pt2
         else
           do
             td <- ptree_TopLevelDec pt1 ;
             tds <- ptree_NonETopLevelDecs pt2 ;
             return (td :: tds)
           od
       | _ => fail)
`;

val _ = export_theory()
