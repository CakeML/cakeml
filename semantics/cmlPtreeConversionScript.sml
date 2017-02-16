open HolKernel Parse boolLib bossLib

open gramTheory tokenUtilsTheory astTheory

open lcsymtacs

val _ = new_theory "cmlPtreeConversion"

(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

val _ = set_grammar_ancestry ["gram", "tokenUtils", "ast", "namespace"]
val _ = monadsyntax.temp_add_monadsyntax()
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

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("fail", ``NONE``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_MAP_DEF",
                                        "option.OPTION_MAP2_DEF",
                                        "option.OPTION_CHOICE_def"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)
val _ = overload_on ("lift", ``option$OPTION_MAP``)

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

val ptree_UQTyop_def = Define`
  ptree_UQTyop (Lf _) = NONE ∧
  ptree_UQTyop (Nd (nt,_) args) =
    if nt <> mkNT nUQTyOp then NONE
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
  ptree_TyvarN (Nd (nt,_) args) =
    if nt <> mkNT nTyvarN then NONE
    else
      dtcase args of
          [tyv] => destTyvarPT tyv
        | _ => NONE
`;

val _ = temp_overload_on ("'", ``λf a. OPTION_BIND a f``);

val ptree_Tyop_def = Define`
  ptree_Tyop ((Lf _) : mlptree) = NONE ∧
  ptree_Tyop (Nd (nt,_) args) =
    if nt <> mkNT nTyOp then NONE
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



val ptree_linfix_def = Define`
  ptree_linfix topnt opn elnt (pt : mlptree) =
    dtcase pt of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt = mkNT topnt then
          dtcase args of
              [pt] => do e <- elnt pt; SOME [e] od
            | [top; Lf (TK opn,_); pt] => do
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
  tuplify tys = SOME(Tapp tys TC_tup)
`

val ptree_Type_def = Define`
  (ptree_Type nt (Lf _) : t option = NONE) ∧
  (ptree_Type nm (Nd (nt,_) args) =
     if nt <> mkNT nm then NONE
     else if nm = nType then
       dtcase args of
          [dt] =>
          do
            tys <- ptree_PType dt;
            tuplify tys
          od
        | [dt;Lf (TOK ArrowT,_);rt] =>
              do
                dtys <- ptree_PType dt;
                dty <- tuplify dtys;
                rty <- ptree_Type nType rt;
                SOME(Tfn dty rty)
              od
            | _ => NONE
     else if nm = nDType then
       dtcase args of
           [pt] => ptree_Type nTbase pt
         | [dt; opn] => do
                          dty <- ptree_Type nDType dt;
                          opname <- ptree_Tyop opn;
                          SOME(Tapp [dty] (TC_name opname))
                        od
         | _ => NONE
     else if nm = nTbase then
       dtcase args of
           [pt] =>
                OPTION_MAP Tvar (destTyvarPT pt) ++
                OPTION_MAP (Tapp [] o TC_name) (ptree_Tyop pt)
         | [Lf (TK LparT,_) ; t; Lf (TK RparT,_)] =>
              do
                ptree_Type nType t
              od
         | [Lf (TK LparT,_) ; tl; Lf (TK RparT,_); opn] =>
           do
              tylist <- ptree_Typelist2 tl;
              opname <- ptree_Tyop opn;
              SOME(Tapp tylist (TC_name opname))
           od
         | _ => NONE
     else NONE) ∧
  (ptree_Typelist2 ptree : t list option =
     dtcase ptree of
       Lf _ => NONE
     | Nd (nt,_) args =>
       if nt <> mkNT nTypeList2 then NONE
       else
         dtcase args of
           | [dt; Lf (TK CommaT,_); tl'] =>
             do
               ty <- ptree_Type nType dt;
               tylist <- ptree_TypeList1 tl';
               SOME(ty::tylist)
             od
           | _ => NONE) ∧
  (ptree_TypeList1 ptree : t list option =
    dtcase ptree of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt <> mkNT nTypeList1 then NONE
        else
          dtcase args of
              [dt] =>
              do
                ty <- ptree_Type nType dt;
                SOME([ty])
              od
            | [dt; Lf (TK CommaT,_); tl] =>
              do
                ty <- ptree_Type nType dt;
                tl <- ptree_TypeList1 tl;
                SOME(ty::tl)
              od
            | _ => NONE) ∧
  (ptree_PType ptree : t list option =
     dtcase ptree of
         Lf _ => NONE
       | Nd (nt,_) args =>
         if nt <> mkNT nPType then NONE
         else
           dtcase args of
               [dty_pt] =>
               do
                 dty <- ptree_Type nDType dty_pt;
                 SOME [dty]
               od
             | [dty_pt; Lf (TK StarT,_); pty_pt] =>
               do
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
    | Nd (nt,_) args =>
      if nt = mkNT nTypeName then
        dtcase args of
          [opt] => do opn <- ptree_UQTyop opt ; SOME([], opn) od
        | [sym; opt] => do tyvn <- destTyvarPT sym ;
                           opn <- ptree_UQTyop opt ;
                           SOME ([tyvn], opn)
                        od
        | [Lf (TK LparT,_) ; tyvl; Lf (TK RparT,_) ; opt] =>
            do
              tyvnms <- ptree_linfix nTyVarList CommaT ptree_TyvarN tyvl;
              opn <- ptree_UQTyop opt;
              SOME(tyvnms, opn)
            od
        | _ => NONE
      else NONE
`;

val ptree_UQConstructorName_def = Define`
  ptree_UQConstructorName (Lf _) = NONE ∧
  ptree_UQConstructorName (Nd (nm,_) args) =
    if nm <> mkNT nUQConstructorName then NONE
    else
      dtcase args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
`

val ptree_ConstructorName_def = Define`
  ptree_ConstructorName ast =
    dtcase ast of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt <> mkNT nConstructorName then NONE
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
  detuplify (Tapp args TC_tup) = args ∧
  detuplify ty = [ty]
`

val detuplify_pmatch = Q.store_thm("detuplify_pmatch",`!ty.
  detuplify ty =
  case ty of
    Tapp args t => if t = TC_tup then args else [Tapp args t]
  | ty => [ty]`,
  ho_match_mp_tac (theorem "detuplify_ind")
  >> fs[detuplify_def]);

val ptree_Dconstructor_def = Define`
  ptree_Dconstructor ast =
    dtcase ast of
        Lf x => NONE
      | Nd (nt,_) args =>
        if nt = mkNT nDconstructor then
          dtcase args of
              [] => NONE
            | t::ts =>
              do
                 cname <- ptree_UQConstructorName t;
                 types <- dtcase ts of
                               [] => SOME []
                             | [Lf (TK OfT,_) ; ty_pt] =>
                                 OPTION_MAP detuplify (ptree_Type nType ty_pt)
                             | _ => NONE;
                 SOME(cname, types)
              od
            | _ :: t => NONE
        else NONE
`;

val ptree_DtypeDecl_def = Define`
  ptree_DtypeDecl (pt : mlptree) =
    dtcase pt of
        Lf _ => NONE
      | Nd (nt,_) args =>
        if nt = mkNT nDtypeDecl then
          dtcase args of
              [tynm_pt; Lf (TK EqualsT,_); dtc_pt] => do
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
    | Nd (nt,_) args =>
      if nt = mkNT nTypeDec then
        dtcase args of
            [Lf (TK DatatypeT,_); pt] => do
              ptree_linfix nDtypeDecls AndT ptree_DtypeDecl pt
            od
          | _ => NONE
      else NONE`;

val ptree_TypeAbbrevDec_def = Define`
  ptree_TypeAbbrevDec ptree : dec option =
    dtcase ptree of
      Lf _ => NONE
    | Nd (nt,_) args =>
      if nt = mkNT nTypeAbbrevDec then
        dtcase args of
          [Lf (TK TypeT,_); tynm ; Lf (TK EqualsT,_) ; typ_pt] => do
            (vars, nm) <- ptree_TypeName tynm;
            typ <- ptree_Type nType typ_pt;
            SOME(Dtabbrev vars nm typ)
          od
        | _ => NONE
      else NONE
`

val ptree_Op_def = Define`
  ptree_Op (Lf _) = NONE ∧
  ptree_Op (Nd (nt,_) subs) =
    if nt = mkNT nMultOps then
      dtcase subs of 
           [Lf (TK StarT,_)] => SOME (Short "*")
         | [Lf (TK (SymbolT "/"),_)]  => SOME (Short "/")
         | [Lf (TK (AlphaT "mod"),_)] => SOME (Short "mod")
         | [Lf (TK (AlphaT "div"),_)] => SOME (Short "div")
         | _ => NONE
    else if nt = mkNT nAddOps then
      dtcase subs of 
           [Lf (TK (SymbolT "+"),_)] => SOME (Short "+")
         | [Lf (TK (SymbolT "-"),_)] => SOME (Short "-")
         | _ => NONE
    else if nt = mkNT nListOps then
      dtcase subs of 
           [Lf (TK (SymbolT "::"),_)] => SOME (Short "::")
         | [Lf (TK (SymbolT "@"),_)] => SOME (Short "@")
         | _ => NONE
    else if nt = mkNT nRelOps then
      dtcase subs of
         [Lf (TK EqualsT,_)] => SOME(Short "=")
       | [pt] =>
          do
            s <- destSymbolT ' (destTOK ' (destLf pt));
            SOME (Short s)
          od
        | _ => NONE
    else if nt = mkNT nCompOps then
      dtcase subs of 
           [Lf (TK (SymbolT ":="),_)] => SOME (Short ":=")
         | [Lf (TK (AlphaT "o"),_)] => SOME (Short "o")
         |_ => NONE
    else NONE
`;

val ptree_V_def = Define`
  ptree_V (Lf _) = NONE ∧
  ptree_V (Nd (nt,_) subs) =
    if nt = mkNT nV then
      dtcase subs of
          [Lf (TOK t,_)] => destAlphaT t ++ destSymbolT t
        | _ => NONE
    else NONE
`;

val ptree_FQV_def = Define`
  ptree_FQV (Lf _) = NONE ∧
  ptree_FQV (Nd (nt,_) args) =
    if nt <> mkNT nFQV then NONE
    else
      dtcase args of
          [pt] => OPTION_MAP Short (ptree_V pt) ++
                  do
                    (str,s) <- destLongidT ' (destTOK ' (destLf pt));
                    SOME(Long str (Short s))
                  od
        | _ => NONE
`

(* in other words constructors never take tuples as arguments, only ever
   lists of arguments *)
val mkPatApp_def = Define`
  mkPatApp cn p =
    if cn = Short "ref" then Pref p
    else
      dtcase p of
          Pcon NONE pl => Pcon (SOME cn) pl
        | _ => Pcon (SOME cn) [p]
`;

val ptree_Pattern_def = Define`
  (ptree_Pattern nt (Lf _) = NONE) ∧
  (ptree_Pattern nt (Nd (nm,_) args) =
    if mkNT nt <> nm then NONE
    else if nm = mkNT nPbase then
      dtcase args of
          [Lf (TOK UnderbarT,_)] => return (Pvar "_") 
        | [vic] =>
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
          od
        | [Lf (TK LbrackT,_); Lf (TK RbrackT,_)] =>
            SOME(Pcon (SOME (Short "nil")) [])
        | [Lf (TK LbrackT,_) ; plistpt; Lf (TK RbrackT,_)] =>
          do
            plist <- ptree_Plist plistpt;
            SOME (FOLDR (λp a. Pcon (SOME (Short "::")) [p; a])
                        (Pcon (SOME (Short "nil")) [])
                        plist)
          od
        | _ => NONE
    else if nm = mkNT nPapp then
      dtcase args of
          [pb] => ptree_Pattern nPbase pb
        | [cnm; ppt] =>
          do
            cn <- ptree_ConstructorName cnm;
            p <- ptree_Pattern nPbase ppt;
            SOME(mkPatApp cn p)
          od
        | _ => NONE
    else if nm = mkNT nPcons then
      dtcase args of
          [papt] => ptree_Pattern nPapp papt
        | [papt; Lf (TK (SymbolT "::"),_); pcons_pt] =>
          do
            pa <- ptree_Pattern nPapp papt;
            patt <- ptree_Pattern nPcons pcons_pt;
            SOME(Pcon (SOME (Short "::")) [pa; patt])
          od
        | _ => NONE
    else if nm = mkNT nPattern then
      dtcase args of
          [pcons] => ptree_Pattern nPcons pcons
        | [pcons_pt; Lf (TOK ColonT,_); type_pt] =>
          do
            pc <- ptree_Pattern nPcons pcons_pt;
            ty <- ptree_Type nType type_pt;
            return (Ptannot pc ty)
          od
        | _ => fail
    else if nm = mkNT nPtuple then
      dtcase args of
          [Lf (TOK LparT,_) ; Lf (TOK RparT,_) ] =>
                        SOME (Pcon NONE [])
        | [Lf (TOK LparT,_) ; pl_pt; Lf (TOK RparT,_)] =>
          do
            pl <- ptree_Plist pl_pt;
            dtcase pl of
                [] => NONE
              | [p] => SOME p
              | _ => SOME (Pcon NONE pl)
          od
        | _ => NONE
    else NONE) ∧

  (ptree_Plist (Lf _) = NONE) ∧
  (ptree_Plist (Nd (nm,_) args) =
     if nm <> mkNT nPatternList then NONE
     else
       dtcase args of
           [p_pt] =>
           do
             p <- ptree_Pattern nPattern p_pt;
             SOME [p]
           od
         | [p; Lf (TOK CommaT,_); pl] =>
           do
             hdpat <- ptree_Pattern nPattern p;
             tlpats <- ptree_Plist pl;
             SOME(hdpat::tlpats)
           od
         | _ => NONE)
`;

val ptree_PbaseList1_def = Define`
  (ptree_PbaseList1 (Lf _) = NONE) ∧
  (ptree_PbaseList1 (Nd (nm,_) args) =
     if nm <> mkNT nPbaseList1 then NONE
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

val mkAst_App_def = Define`
  mkAst_App a1 a2 =
    dest_Conk a1
      (λnm_opt args.
               if ~NULL args then App Opapp [a1;a2]
               else if nm_opt = SOME (Short "ref") then
                 App Opapp [Var (Short "ref"); a2]
               else
                 dest_Conk a2
                           (λnm_opt2 args2.
                                     if nm_opt2 = NONE ∧ ~ NULL args2 then
                                       Con nm_opt args2
                                     else
                                       Con nm_opt [a2])
                           (Con nm_opt [a2]))
      (App Opapp [a1;a2])
`;

(* this re-expression of the above blows up disgustingly when the case
   expressions are expanded but is perhaps easier to understand. *)
val mkAst_App_thm = Q.store_thm(
  "mkAst_App_thm",
  `mkAst_App a1 a2 =
     dtcase a1 of
         Con (SOME (Short "ref")) [] => App Opapp [Var (Short "ref"); a2]
       | Con s [] =>
         (dtcase a2 of
              Con NONE [] => Con s [a2]
                (* applying a constructor to unit has to be viewed as
                   applying it to one argument (unit), rather than as
                   applying it to none *)
            | Con NONE tuple => Con s tuple
            | _ => Con s [a2])
       | _ => App Opapp [a1; a2]`,
  Cases_on `a1` >> simp[mkAst_App_def, dest_Conk_def] >>
  rename1 `Con nm_opt args` >> Cases_on `args` >> simp[] >>
  Cases_on `nm_opt` >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >>
      rename1 `Con NONE [Con opt2 args2]` >> Cases_on `opt2` >> simp[] >>
      Cases_on `args2` >> simp[]) >>
  rename1`ident = Short "ref"` >> reverse (Cases_on `ident`) >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rename1`[Con opt2 args2]` >>
      map_every Cases_on [`opt2`, `args2`] >> simp[]) >>
  rename1 `str = "ref"` >> Cases_on `str` >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rename1`[Con opt2 args2]` >>
      map_every Cases_on [`opt2`, `args2`] >> simp[]) >>
  rename1`SOME(Short (STRING c str'))` >> Cases_on `str'` >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rename1`[Con opt2 args2]` >>
      map_every Cases_on [`opt2`, `args2`] >> simp[]) >>
  rename1`SOME(Short (STRING c1 (STRING c2 str')))` >> Cases_on `str'` >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rename1`[Con opt2 args2]` >>
      map_every Cases_on [`opt2`, `args2`] >> simp[]) >>
  rename1`SOME(Short (STRING c1 (STRING c2 (STRING c3 str'))))` >>
  reverse (Cases_on `str'`) >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rw[] >>
      rename1`Con _ args2` >> Cases_on `args2` >> fs[] >>
      rename1`option_CASE opt2` >> Cases_on `opt2` >> fs[] >>
      rename1`list_CASE args2` >> Cases_on `args2` >> fs[]) >>
  reverse (Cases_on`c1 = #"r"`) >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rw[] >>
      rename1`Con _ args2` >> Cases_on `args2` >> fs[] >>
      rename1`option_CASE opt2` >> Cases_on `opt2` >> fs[] >>
      rename1`list_CASE args2` >> Cases_on `args2` >> fs[]) >>
  reverse (Cases_on`c2 = #"e"`) >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rw[] >>
      rename1`Con _ args2` >> Cases_on `args2` >> fs[] >>
      rename1`option_CASE opt2` >> Cases_on `opt2` >> fs[] >>
      rename1`list_CASE args2` >> Cases_on `args2` >> fs[]) >>
  reverse (Cases_on`c3 = #"f"`) >> simp[]
  >- (Cases_on `a2` >> simp[dest_Conk_def] >> rw[] >>
      rename1`Con _ args2` >> Cases_on `args2` >> fs[] >>
      rename1`option_CASE opt2` >> Cases_on `opt2` >> fs[] >>
      rename1`list_CASE args2` >> Cases_on `args2` >> fs[]))
                               
val isSymbolicConstructor_def = Define`
  isSymbolicConstructor (structopt : modN option) s =
    return (s = "::")
`;

val isConstructor_def = Define`
  isConstructor structopt s =
    do
      ifM (isSymbolicConstructor structopt s)
        (return T)
        (return (dtcase misc$oHD s of
                     NONE => F
                   | SOME c => isAlpha c ∧ isUpper c))
    od
`;

val ptree_OpID_def = Define`
  ptree_OpID (Lf _) = NONE ∧
  ptree_OpID (Nd (nt,_) subs) =
    if nt ≠ mkNT nOpID then NONE
    else
      dtcase subs of
          [Lf (TK tk,_)] =>
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
           else
             NONE)
        | _ => NONE
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
  ptree_Eliteral (Nd (nt,_) subs) =
    do
      assert (LENGTH subs = 1 ∧ nt = mkNT nEliteral);
      lf <- destLf (HD subs);
      t <- destTOK lf;
      (do i <- destIntT t ; return (Lit (IntLit i)) od ++
       do c <- destCharT t ; return (Lit (Char c)) od ++
       do s <- destStringT t ; return (Lit (StrLit s)) od ++
       do n <- destWordT t ; return (Lit (Word64 (n2w n))) od)
    od
`

val bind_loc_def = Define`
  bind_loc (Lannot e l) l' = Lannot e l /\
  bind_loc e l = Lannot e l
`

local
  val ptree_Expr_quotation = `
  ptree_Expr ent (Lf _) = NONE ∧
  ptree_Expr ent (Nd (nt,loc) subs) = 
  do
  e <- (if mkNT ent = nt then
      if nt = mkNT nEbase then
        dtcase subs of
            [Lf (TK LparT,_) ; pt; Lf (TK RparT,_)] =>
            do
              eseq <- ptree_Eseq pt;
              Eseq_encode eseq
            od
          | [Lf (TK LbrackT,_) ; pt; Lf (TK RbrackT,_)] =>
            do
              elist <- ptree_Exprlist nElist1 pt;
              SOME(FOLDR (λe acc. Con (SOME (Short "::")) [e; acc])
                         (Con (SOME (Short "nil")) [])
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
          | [Lf (TK LparT,_) ;Lf (TK RparT,_) ] =>  SOME (Con NONE [])
          | [Lf (TK LbrackT,_) ;Lf (TK RbrackT,_) ] => SOME (Con (SOME (Short "nil")) [])
          | [Lf (TK OpT,_) ; rp ] => ptree_OpID rp
          | [Lf (TOK LetT,_) ;letdecs_pt;Lf (TOK InT,_) ;ept; Lf (TOK EndT,_)] =>
            do
              letdecs <- ptree_LetDecs letdecs_pt;
              eseq <- ptree_Eseq ept;
              e <- Eseq_encode eseq;
              SOME(FOLDR (λdf acc. dtcase df of
                                       INL (v,e0) => Let (SOME v) e0 acc
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
            [Lf (TOK LparT,_) ; el2; Lf (TOK RparT,_)] =>
            do
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
          [t1;Lf(TOK(AlphaT "before"),_);t2] => do
            a1 <- ptree_Expr nEbefore t1;
            a2 <- ptree_Expr nEcomp t2;
            return (mk_binop (Short "before") a1 a2)
          od
        | [t] => ptree_Expr nEcomp t
        | _ => NONE
      else if nt = mkNT nEtyped then
        dtcase subs of
          [e_pt; Lf (TOK ColonT,_); ty_pt] => do
            e <- ptree_Expr nEbefore e_pt;
            ty <- ptree_Type nType ty_pt;
            return (Tannot e ty)
          od
        | [t] => ptree_Expr nEbefore t
        | _ => NONE
      else if nt = mkNT nElogicAND then
        dtcase subs of
            [t1;Lf (TOK AndalsoT,_);t2] => do
              a1 <- ptree_Expr nElogicAND t1;
              a2 <- ptree_Expr nEtyped t2;
              SOME(Log And a1 a2)
            od
          | [t] => ptree_Expr nEtyped t
          | _ => NONE
      else if nt = mkNT nElogicOR then
        dtcase subs of
            [t1;Lf (TOK OrelseT,_);t2] => do
              a1 <- ptree_Expr nElogicOR t1;
              a2 <- ptree_Expr nElogicAND t2;
              SOME (Log Or a1 a2)
            od
          | [t] => ptree_Expr nElogicAND t
          | _ => NONE
      else if nt = mkNT nEhandle then
        dtcase subs of
            [pt] => ptree_Expr nElogicOR pt
          | [e1pt; Lf (TOK HandleT,_); ent] =>
            do
              e <- ptree_Expr nElogicOR e1pt;
              pes <- ptree_PEs ent;
              SOME(Handle e pes)
            od
          | _ => NONE
      else if nt = mkNT nE then
        dtcase subs of
          | [t] => ptree_Expr nEhandle t
          | [Lf (TOK RaiseT,_); ept] =>
            do
              e <- ptree_Expr nE ept;
              SOME(Raise e)
            od
          | [Lf (TOK FnT,_) ; pnt; Lf (TOK DarrowT,_); ent] =>
            do
              p <- ptree_Pattern nPattern pnt;
              e <- ptree_Expr nE ent;
              SOME(mkFun p e)
            od
          |[Lf (TOK CaseT,_); pnt; Lf (TOK OfT,_); ent ] =>
            do
              e <- ptree_Expr nE pnt;
              pes <- ptree_PEs ent;
              SOME(Mat e pes)
            od
          | [Lf (TOK IfT,_) ;g;Lf (TOK ThenT,_) ;te;Lf (TOK ElseT,_);ee] => do
              a1 <- ptree_Expr nE g;
              a2 <- ptree_Expr nE te;
              a3 <- ptree_Expr nE ee;
              SOME(If a1 a2 a3)
            od
          | _ => NONE
      else if nt = mkNT nE' then
        dtcase subs of
          | [t] => ptree_Expr nElogicOR t
          | [Lf (TOK RaiseT,_); ept] =>
            do
              e <- ptree_Expr nE' ept;
              SOME(Raise e)
            od
          | [Lf (TOK FnT,_) ; vnt; Lf (TOK DarrowT,_); ent] =>
            do
              v <- ptree_V vnt;
              e <- ptree_Expr nE' ent;
              SOME(Fun v e)
            od
          | [Lf (TOK IfT,_) ;g;Lf (TOK ThenT,_);te;Lf (TOK ElseT,_);ee] => do
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
             | [e;Lf (TOK CommaT,_);el1] =>
               do
                 front <- ptree_Expr nE e;
                 back <- ptree_Exprlist nElist1 el1 ;
                 SOME(front::back)
               od
             | _ => NONE
         else if nt = mkNT nElist2 then
           dtcase subs of
               [e;Lf (TOK CommaT,_);el1] =>
               do
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
            | [fdecspt;Lf (TOK AndT,_);fdecpt] =>
              do
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
              [fname_pt; pats_pt;Lf (TOK EqualsT,_); body_pt] =>
              do
                fname <- ptree_V fname_pt;
                ps <- ptree_PbaseList1 pats_pt;
                p1 <- misc$oHD ps;
                body0 <- ptree_Expr nE body_pt;
                SOME(fname,dePat p1 (FOLDR mkFun body0 (misc$safeTL ps)))
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
            | [Lf (TOK SemicolonT,_) ; lds_pt] => ptree_LetDecs lds_pt
            | [ld_pt; lds_pt] =>
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
              [Lf (TOK FunT,_); andfdecls_pt] =>
              do
                fds <- ptree_AndFDecls andfdecls_pt;
                SOME (INR fds)
              od
            | [Lf (TOK ValT,_) ; v_pt; Lf (TOK EqualsT,_); e_pt] =>
              do
                v <- ptree_V v_pt;
                e <- ptree_Expr nE e_pt;
                SOME (INL(v,e))
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
        | [pe'_pt; Lf (TOK BarT,_); pes_pt] =>
          do
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
           [p_pt; Lf (TOK DarrowT,_); e_pt] =>
           do
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
           [p_pt; Lf (TOK DarrowT,_); e'_pt] =>
           do
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
        | [e_pt; Lf (TOK SemicolonT,_) ; seq_pt] =>
          do
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
  ptree_Decl pt : dec option =
    dtcase pt of
       Lf _ => NONE
     | Nd (nt,_) args =>
       if nt <> mkNT nDecl then NONE
       else
         dtcase args of
             [dt] =>
             do
               tydec <- ptree_TypeDec dt;
               SOME (Dtype tydec)
             od ++ ptree_TypeAbbrevDec dt
           | [Lf (TOK FunT,_); fdecls] =>
             do
               fdecs <- ptree_AndFDecls fdecls;
               SOME (Dletrec fdecs)
             od
           | [Lf (TOK ExceptionT,_); fdecls] =>
             do
               (enm, etys) <- ptree_Dconstructor fdecls;
               SOME (Dexn enm etys)
             od
           | [Lf (TOK ValT,_); patpt; Lf (TOK EqualsT,_); ept] =>
             do
               pat <- ptree_Pattern nPattern patpt;
               e <- ptree_Expr nE ept;
               SOME (Dlet pat e)
             od
           | _ => NONE
`

val ptree_Decls_def = Define`
  ptree_Decls (Lf _) = NONE ∧
  ptree_Decls (Nd (nt,_) args) =
    if nt <> mkNT nDecls then NONE
    else
      dtcase args of
          [] => SOME []
        | [Lf (TOK SemicolonT,_); ds_pt] => ptree_Decls ds_pt
        | [d_pt; ds_pt] =>
            do
              d <- ptree_Decl d_pt;
              ds <- ptree_Decls ds_pt;
              SOME(d::ds)
            od
        | _ => NONE
`

val ptree_OptTypEqn_def = Define`
  ptree_OptTypEqn (Lf _) = NONE : t option option ∧
  ptree_OptTypEqn (Nd (nt,_) args) =
    if nt <> mkNT nOptTypEqn then NONE
    else
      dtcase args of
          [] => SOME NONE
        | [Lf (TOK EqualsT,_); typ_pt] =>
          do
            typ <- ptree_Type nType typ_pt;
            SOME (SOME typ)
          od
        | _ => NONE
`

val ptree_SpecLine_def = Define`
  ptree_SpecLine (Lf _) = NONE ∧
  ptree_SpecLine (Nd (nt,_) args) =
    if nt <> mkNT nSpecLine then NONE
    else
      dtcase args of
          [td_pt] =>
          do
            td <- ptree_TypeDec td_pt;
            SOME(Stype td)
          od
        | [Lf (TOK ExceptionT,_); dcon_pt] =>
          do
            (nm,tys) <- ptree_Dconstructor dcon_pt;
            SOME(Sexn nm tys)
          od
        | [Lf (TOK TypeT,_); tynm_pt; opteqn_pt] =>
          do
            (vs,nm) <- ptree_TypeName tynm_pt;
            opteqn <- ptree_OptTypEqn opteqn_pt;
            SOME(dtcase opteqn of
                     NONE => Stype_opq vs nm
                   | SOME ty => Stabbrev vs nm ty)
          od
        | [Lf (TOK ValT,_); vname_pt; Lf (TOK ColonT,_); type_pt] =>
          do
            vname <- ptree_V vname_pt;
            ty <- ptree_Type nType type_pt;
            SOME(Sval vname ty)
          od
        | _ => NONE
`

val ptree_SpeclineList_def = Define`
  ptree_SpeclineList (Lf _) = NONE ∧
  ptree_SpeclineList (Nd (nt,_) args) =
    if nt <> mkNT nSpecLineList then NONE
    else
      dtcase args of
          [] => SOME []
        | [Lf (TOK SemicolonT,_) ; sll_pt] => ptree_SpeclineList sll_pt
        | [sl_pt; sll_pt] =>
            do
              sl <- ptree_SpecLine sl_pt;
              sll <- ptree_SpeclineList sll_pt;
              SOME(sl::sll)
            od
        | _ => NONE
`

val ptree_SignatureValue_def = Define`
  ptree_SignatureValue (Lf _) = NONE ∧
  ptree_SignatureValue (Nd (nt,_) args) =
    if nt <> mkNT nSignatureValue then NONE
    else
      dtcase args of
          [Lf (TOK SigT,_) ; sll_pt; Lf (TOK EndT,_)] => 
            ptree_SpeclineList sll_pt
        | _ => NONE
`;

val ptree_StructName_def = Define`
  ptree_StructName (Lf _) = NONE ∧
  ptree_StructName (Nd (nm,_) args) =
    if nm <> mkNT nStructName then NONE
    else
      dtcase args of
          [pt] => destAlphaT ' (destTOK ' (destLf pt))
        | _ => NONE
`

val ptree_Structure_def = Define`
  ptree_Structure (Lf _) = NONE ∧
  ptree_Structure (Nd (nt,_) args) =
    if nt <> mkNT nStructure then NONE
    else
      dtcase args of
          [Lf (TOK StructureT,_);sname_pt;asc_opt;Lf (TOK EqualsT,_);
           Lf (TOK StructT,_);ds_pt;Lf (TOK EndT,_)] =>
          do
            sname <- ptree_StructName sname_pt;
            asc <- dtcase asc_opt of
                       Lf _ => NONE
                     | Nd (nt,_) args =>
                         if nt <> mkNT nOptionalSignatureAscription then NONE
                         else
                           dtcase args of
                               [] => SOME NONE
                             | [Lf (TOK SealT,_); sig_pt] =>
                               do
                                 sigv <- ptree_SignatureValue sig_pt;
                                 SOME (SOME sigv)
                               od
                             | _ => NONE;
            ds <- ptree_Decls ds_pt;
            SOME(Tmod sname asc ds)
          od
        | _ => NONE
`

val ptree_TopLevelDec_def = Define`
  ptree_TopLevelDec (Lf _) = NONE ∧
  ptree_TopLevelDec (Nd (nt,_) args) =
    if nt <> mkNT nTopLevelDec then NONE
    else
      dtcase args of
          [pt] =>
            ptree_Structure pt ++
            OPTION_MAP Tdec (ptree_Decl pt)
        | _ => NONE
`

val ptree_TopLevelDecs_def = Define`
  ptree_TopLevelDecs (Lf _) = fail ∧
  (ptree_TopLevelDecs (Nd (nt,_) args) =
     if nt <> mkNT nTopLevelDecs then fail
     else
       dtcase args of
           [] => return []
         | [Lf (TOK SemicolonT,_); tds_pt] => ptree_TopLevelDecs tds_pt
         | [td_pt; tds_pt] =>
             do
               td <- ptree_TopLevelDec td_pt;
               tds <- ptree_NonETopLevelDecs tds_pt;
               return(td::tds)
             od
         | [e_pt; Lf (TOK SemicolonT,_); tds_pt] =>
           do
             e <- ptree_Expr nE e_pt;
             tds <- ptree_TopLevelDecs tds_pt;
             return (Tdec (Dlet (Pvar "it") e) :: tds)
           od
         | _ => NONE) ∧
  (ptree_NonETopLevelDecs (Lf _) = fail) ∧
  (ptree_NonETopLevelDecs (Nd (nt,_) args) =
     if nt <> mkNT nNonETopLevelDecs then fail
     else
       dtcase args of
         [] => return []
       | [Lf (TOK SemicolonT,_) ; pt2] => ptree_TopLevelDecs pt2
       | [pt1 ; pt2] =>
           do
             td <- ptree_TopLevelDec pt1 ;
             tds <- ptree_NonETopLevelDecs pt2 ;
             return (td :: tds)
           od
       | _ => fail)
`;

val _ = export_theory()
