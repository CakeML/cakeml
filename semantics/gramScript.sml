(*
  Definition of CakeML's Context-Free Grammar.
  The grammar specifies how token lists should be converted to syntax trees.
*)

open HolKernel Parse boolLib bossLib

open tokensTheory grammarTheory locationTheory

open lcsymtacs grammarLib

val _ = new_theory "gram"
val _ = set_grammar_ancestry ["tokens", "grammar", "location"]

val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                ("[", ``LbrackT``),
                ("]", ``RbrackT``),
                (";", ``SemicolonT``), (":=", ``SymbolT ":="``),
                (":>", ``SealT``),
                ("::", ``SymbolT "::"``), ("@", ``SymbolT "@"``),
                ("->", ``ArrowT``), ("=>", ``DarrowT``),
                ("*", ``StarT``),
                ("|", ``BarT``), ("=", ``EqualsT``), (":", ``ColonT``),
                ("_", ``UnderbarT``),
                ("and", ``AndT``),
                ("andalso", ``AndalsoT``),
                ("before", ``AlphaT "before"``),
                ("Bind", ``AlphaT "Bind"``),
                ("case", ``CaseT``),
                ("datatype", ``DatatypeT``),
                ("Div", ``AlphaT "Div"``),
                ("else", ``ElseT``),
                ("end", ``EndT``),
                ("exception", ``ExceptionT``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("handle", ``HandleT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("IntError", ``AlphaT "IntError"``),
                ("let", ``LetT``),
                ("local", ``LocalT``),
                ("o", ``AlphaT "o"``),
                ("of", ``OfT``),
                ("op", ``OpT``),
                ("orelse", ``OrelseT``),
                ("raise", ``RaiseT``),
                ("sig", ``SigT``),
                ("struct", ``StructT``),
                ("structure", ``StructureT``),
                ("then", ``ThenT``),
                ("type", ``TypeT``),
                ("val", ``ValT``)]
fun tokmap s =
    case Binarymap.peek(tokmap0, s) of
        NONE => raise Fail ("No token binding for "^s)
      | SOME t => t

val ginfo = { tokmap = tokmap,
              tokty = ``:token``, nt_tyname = "MMLnonT",
              start = "TopLevelDecs",
              gname = "cmlG", mkntname = (fn s => "n" ^ s) }

val cmlG_def = mk_grammar_def ginfo
`(* types *)
 UQTyOp ::= <AlphaT> | <SymbolT> ;
 TyvarN ::= <TyvarT>;
 TyOp ::= UQTyOp | <LongidT>;
 TypeList1 ::= Type | Type "," TypeList1;
 TypeList2 ::= Type "," TypeList1;
 Tbase ::= <TyvarT> | TyOp | "(" TypeList2 ")" TyOp | "(" Type ")";
 DType ::= DType TyOp | Tbase;
 PType ::= DType "*" PType | DType;
 Type ::= PType | PType "->" Type;
 TbaseList ::=  | PTbase TbaseList ;
 PTbase ::= <TyvarT> | TyOp | "(" Type ")" ;

 (* type declarations *)
 TypeName ::= UQTyOp | "(" TyVarList ")" UQTyOp | <TyvarT> UQTyOp ;
 TyVarList ::= TyvarN | TyVarList "," TyvarN;
 Dconstructor ::= UQConstructorName TbaseList;
 DtypeCons ::= Dconstructor | DtypeCons "|" Dconstructor;
 DtypeDecl ::= TypeName "=" DtypeCons ;
 DtypeDecls ::= DtypeDecl | DtypeDecls "and" DtypeDecl;
 TypeDec ::= "datatype" DtypeDecls;
 TypeAbbrevDec ::= "type" TypeName "=" Type;

 (* expressions - base cases and function applications *)
 UQConstructorName ::= ^(``{AlphaT s | s ≠ "" ∧ isUpper (HD s)}``);
 ConstructorName ::=
     UQConstructorName
  | ^(``{LongidT str s | str,s | s ≠ "" ∧ isAlpha (HD s) ∧ isUpper (HD s)}``);
 V ::= ^(``{AlphaT s | s ∉ {"before"; "div"; "mod"; "o"} ∧
                       s ≠ "" ∧ ¬isUpper (HD s)}``)
    |  ^(``{SymbolT s |
            s ∉ {"+"; "*"; "-"; "/"; "<"; ">"; "<="; ">="; "<>"; ":=";
                 "::"; "@"; "\094"}}``);
 FQV ::= V
      |  ^(``{LongidT str s | str,s |
              s ≠ "" ∧ (isAlpha (HD s) ⇒ ¬isUpper (HD s))}``) ;
 OpID ::= ^(``{LongidT str s | str,s | s ≠ ""}``)
       |  ^(``{AlphaT s | s ≠ ""}``)
       |  ^(``{SymbolT s | s ≠ ""}``)
       |  "*" | "=" ;

 Eliteral ::= <IntT> |  <CharT> | <StringT> | <WordT> | <FFIT> ;

 Ebase ::= "(" Eseq ")" | Etuple | "(" ")" | FQV | ConstructorName | Eliteral
        | "let" LetDecs "in" Eseq "end" | "[" "]"
        | "[" Elist1 "]" | "op" OpID ;
 Eseq ::= E ";" Eseq | E;
 Etuple ::= "(" Elist2 ")";
 Elist2 ::= E "," Elist1;
 Elist1 ::= E | E "," Elist1;
 Eapp ::= Eapp Ebase | Ebase;

 (* expressions - binary operators *)
 MultOps ::= ^(``{AlphaT "div"; AlphaT "mod"; StarT; SymbolT "/"}``);
 AddOps ::= ^(``{SymbolT "+"; SymbolT "-"; SymbolT "\094" }``);
 RelOps ::= ^(``{SymbolT s | s ∈ {"<"; ">"; "<="; ">="; "<>"}}``) | "=";
 CompOps ::= "o" | ":=";
 ListOps ::= "@" | "::";
 Emult ::= Emult MultOps Eapp | Eapp;
 Eadd ::= Eadd AddOps Emult | Emult;
 Elistop ::= Eadd ListOps Elistop | Eadd;
 Erel ::= Erel RelOps Elistop | Elistop;
 Ecomp ::= Ecomp CompOps Erel | Erel;
 Ebefore ::= Ebefore "before" Ecomp | Ecomp;
 Etyped ::= Ebefore | Ebefore ":" Type;
 ElogicAND ::= ElogicAND "andalso" Etyped | Etyped;
 ElogicOR ::= ElogicOR "orelse" ElogicAND | ElogicAND;
 Ehandle ::= ElogicOR | ElogicOR "handle" PEs ;
 E ::= "if" E "then" E "else" E | "case" E "of" PEs | "fn" Pattern "=>" E
    | "raise" E |  Ehandle;
 E' ::= "if" E "then" E "else" E' | "raise" E' | ElogicOR ;

 (* function and value declarations *)
 FDecl ::= V PbaseList1 "=" E ;
 AndFDecls ::= FDecl | AndFDecls "and" FDecl;
 LetDec ::= "val" Pattern "=" E | "fun" AndFDecls ;
 LetDecs ::= LetDec LetDecs | ";" LetDecs | ;

 (* patterns *)
 Pbase ::= V | ConstructorName | <IntT> | <StringT> | <CharT> | Ptuple | "_"
        |  "[" "]" | "[" PatternList "]" | "op" OpID;
 PConApp ::= ConstructorName | PConApp Pbase ;
 Papp ::= PConApp Pbase | Pbase ;
 Pcons ::= Papp "::" Pcons | Papp ;
 Pattern ::= Pcons | Pcons ":" Type ;
 Ptuple ::= "(" ")" | "(" PatternList ")";
 PatternList ::= Pattern | Pattern "," PatternList ;
 PbaseList1 ::= Pbase | Pbase PbaseList1 ;
 PE ::= Pattern "=>" E;
 PE' ::= Pattern "=>" E';
 PEs ::= PE | PE' "|" PEs;

 (* modules *)
 StructName ::= ^(``{AlphaT s | s ≠ ""}``) ;
 SpecLine ::= "val" V ":" Type
           |  "type" TypeName OptTypEqn
           |  "exception" Dconstructor
           |  TypeDec ;
 OptTypEqn ::= "=" Type | ;
 SpecLineList ::= SpecLine SpecLineList | ";" SpecLineList | ;
 SignatureValue ::= "sig" SpecLineList "end" ;
 OptionalSignatureAscription ::= ":>" SignatureValue | ;
 Decl ::= "val" Pattern "=" E  | "fun" AndFDecls |  TypeDec
       |  "exception" Dconstructor
       | TypeAbbrevDec | "local" Decls "in" Decls "end";
 Decls ::= Decl Decls | ";" Decls | ;
 Structure ::= "structure" StructName OptionalSignatureAscription "=" "struct" Decls "end";
 TopLevelDec ::= Structure | Decl ;
 TopLevelDecs ::= E ";" TopLevelDecs | TopLevelDec NonETopLevelDecs
               |  ";" TopLevelDecs | ;
 NonETopLevelDecs ::= TopLevelDec NonETopLevelDecs | ";" TopLevelDecs | ;
`;

Type NT = ``:MMLnonT inf``

Overload mkNT = ``INL : MMLnonT -> NT``
Overload NN = ``\nt. NT (mkNT nt)``
Overload TK = ``TOK : token -> (token,MMLnonT)symbol``

Type mlptree = ``:(token, MMLnonT, locs) parsetree``

val nt_distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  save_thm("nt_distinct_ths",  LIST_CONJ (recurse ntlist))
end

val Ndl_def = Define`
  (Ndl n l = Nd (n, unknown_loc) l)`

val Lfl_def = Define`
  (Lfl t = Lf (t, unknown_loc))`

val _ = computeLib.add_persistent_funs ["nt_distinct_ths"]

val ast =
  ``let mkI = λn. Ndl (mkNT nEbase) [Ndl (mkNT nEliteral) [Lfl (TK (IntT n))]]
    in
      Ndl (mkNT nEmult) [
              Ndl (mkNT nEmult) [
                Ndl (mkNT nEmult) [Ndl (mkNT nEapp) [mkI 3]];
                Ndl (mkNT nMultOps) [Lfl (TK StarT)];
                Ndl (mkNT nEapp) [mkI 4]
              ];
              Ndl (mkNT nMultOps) [Lfl (TK (SymbolT "/"))];
              Ndl (mkNT nEapp) [mkI 5]
            ]``

val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, cmlG_def,DISJ_IMP_THM, FORALL_AND_THM,
               finite_mapTheory.FAPPLY_FUPDATE_THM, LET_THM,Ndl_def,Lfl_def])
 ``valid_ptree cmlG ^ast``

val _ = if aconv (rhs (concl check_results)) T then print "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"

val _ = export_theory()
