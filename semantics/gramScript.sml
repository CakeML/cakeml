(*
  Definition of CakeML's Context-Free Grammar.
  The grammar specifies how token lists should be converted to syntax trees.
*)
Theory gram
Ancestors
  tokens grammar location
Libs
  grammarLib


val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                ("[", ``LbrackT``),
                ("]", ``RbrackT``),
                (";", ``SemicolonT``), (":=", ``SymbolT «:=»``),
                (":>", ``SealT``),
                ("->", ``ArrowT``), ("=>", ``DarrowT``),
                ("*", ``StarT``),
                ("::", “SymbolT «::»”),
                ("|", ``BarT``), ("=", ``EqualsT``), (":", ``ColonT``),
                ("_", ``UnderbarT``),
                ("and", ``AndT``),
                ("andalso", ``AndalsoT``),
                ("as", ``AsT``),
                ("before", ``AlphaT «before»``),
                ("Bind", ``AlphaT «Bind»``),
                ("case", ``CaseT``),
                ("datatype", ``DatatypeT``),
                ("Div", ``AlphaT «Div»``),
                ("else", ``ElseT``),
                ("end", ``EndT``),
                ("exception", ``ExceptionT``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("handle", ``HandleT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("IntError", ``AlphaT «IntError»``),
                ("let", ``LetT``),
                ("local", ``LocalT``),
                ("o", ``AlphaT «o»``),
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

Definition validMultSym_def:
  validMultSym s ⇔ "/" ≼ s ∨ "*" ≼ s ∨ "%" ≼ s ∨ "&" ≼ s
End

Definition validAddSym_def:
  validAddSym s ⇔ s ≠ "" ∧ HD s ∈ {#"+"; #"-"; #"\094" (* caret *)} ∨
                  2 ≤ LENGTH s ∧ HD s = #"|"
End

Definition validRelSym_def:
  validRelSym s ⇔ "<" ≼ s ∨ ">" ≼ s ∨ (2 ≤ LENGTH s ∧ ("=" ≼ s ∨ "~" ≼ s))
End

Definition validListSym_def:
  validListSym s ⇔ "@" ≼ s ∨ (":" ≼ s ∧ 2 ≤ LENGTH s ∧ s ≠ ":=")
End

Definition validPrefixSym_def:
  validPrefixSym s ⇔ s = "~" ∨ "!" ≼ s ∨ "?" ≼ s
End

Theorem disjneq:
  x ≠ y ∨ P ⇔ x = y ⇒ P
Proof
  decide_tac
QED

Theorem validSym_incompatibility:
  ¬(validAddSym s ∧ validRelSym s) ∧
  ¬(validAddSym s ∧ validListSym s) ∧
  ¬(validAddSym s ∧ validPrefixSym s) ∧
  ¬(validAddSym s ∧ validMultSym s) ∧
  ¬(validRelSym s ∧ validListSym s) ∧
  ¬(validRelSym s ∧ validPrefixSym s) ∧
  ¬(validRelSym s ∧ validMultSym s) ∧
  ¬(validListSym s ∧ validPrefixSym s) ∧
  ¬(validListSym s ∧ validMultSym s) ∧
  ¬(validPrefixSym s ∧ validMultSym s)
Proof
rw[validRelSym_def, validAddSym_def, validMultSym_def, validPrefixSym_def,
   validListSym_def, disjneq] >>
Cases_on ‘s’ >> simp[] >>
map_every (fn q => Cases_on (`h = ` @ q) >> simp[disjneq] >> rw[])
  [‘#"+"’, ‘#"-"’, ‘#"\094"’, ‘#"<"’, ‘#">"’, ‘#"|"’, ‘#"~"’, ‘#"="’, ‘#"@"’,
   ‘#":"’, ‘#"*"’, ‘#"!"’]>> simp[] >>
Cases_on ‘t’ >> simp[disjneq]
QED

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
 UQConstructorName ::= ^(``{AlphaT s | s ≠ «» ∧ isUpper (strsub s 0)}``);
 ConstructorName ::=
     UQConstructorName
  | ^(``{LongidT str s | str,s | s ≠ «» ∧ isAlpha (strsub s 0) ∧ isUpper (strsub s 0)}``);
 V ::= ^(``{AlphaT s | s ∉ {«before»; «div»; «mod»; «o»} ∧
                       s ≠ «» ∧ ¬isUpper (strsub s 0)}``)
    |  ^(“{SymbolT s | validPrefixSym (explode s)}”);
 FQV ::= V
      |  ^(``{LongidT str s | str,s |
              s ≠ «» ∧ (isAlpha (strsub s 0) ⇒ ¬isUpper (strsub s 0))}``) ;
 OpID ::= ^(``{LongidT str s | str,s | s ≠ «»}``)
       |  ^(``{AlphaT s | s ≠ «»}``)
       |  ^(``{SymbolT s | s ≠ «»}``)
       |  "*" | "=" ;

 Eliteral ::= <IntT> | <CharT> | <StringT> | <WordT> | <FFIT> ;

 Ebase ::= "(" Eseq ")" | Etuple | "(" ")" | FQV | ConstructorName | Eliteral
        | "let" LetDecs "in" Eseq "end" | "[" "]"
        | "[" Elist1 "]" | "op" OpID ;
 Eseq ::= E ";" Eseq | E;
 Etuple ::= "(" Elist2 ")";
 Elist2 ::= E "," Elist1;
 Elist1 ::= E | E "," Elist1;
 Eapp ::= Eapp Ebase | Ebase;

 (* expressions - binary operators *)
 MultOps ::= ^(``{AlphaT «div»; AlphaT «mod»; StarT} ∪
                 {SymbolT s | validMultSym (explode s)}``);
 AddOps ::= ^(``{SymbolT s | validAddSym (explode s)}``);
 RelOps ::= ^(``{SymbolT s | validRelSym (explode s)}``) | "=";
 CompOps ::= "o" | ":=";
 ListOps ::= ^(``{SymbolT s | validListSym (explode s)}``);
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
 Pas ::= V "as" Pcons | Pcons ;
 Pattern ::= Pas | Pas ":" Type ;
 Ptuple ::= "(" ")" | "(" PatternList ")";
 PatternList ::= Pattern | Pattern "," PatternList ;
 PbaseList1 ::= Pbase | Pbase PbaseList1 ;
 PE ::= "case" E "of" PEs
     |  "if" E "then" E "else" PE
     |  "fn" Pattern "=>" E
     |  "raise" PE
     |  ElogicOR PEsfx ;
 PEsfx ::= | "handle" PEs | "|" PEs;
 PEs ::= Pattern "=>" PE;

 (* modules *)
 StructName ::= ^(``{AlphaT s | s ≠ «»}``) ;
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
       | TypeAbbrevDec | "local" Decls "in" Decls "end" | Structure;
 Decls ::= Decl Decls | ";" Decls | ;
 Structure ::= "structure" StructName OptionalSignatureAscription "=" "struct"
               Decls "end";
 TopLevelDecs ::= E ";" TopLevelDecs | Decl NonETopLevelDecs
               |  ";" TopLevelDecs | ;
 NonETopLevelDecs ::= Decl NonETopLevelDecs | ";" TopLevelDecs | ; (*
 REPLCommand ::= <REPLIDT> Ebase ;
 TopLevel ::= REPLCommand | TopLevelDecs ; *)
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

Definition Ndl_def:
  (Ndl n l = Nd (n, unknown_loc) l)
End

Definition Lfl_def:
  (Lfl t = Lf (t, unknown_loc))
End

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
              Ndl (mkNT nMultOps) [Lfl (TK (SymbolT «/»))];
              Ndl (mkNT nEapp) [mkI 5]
            ]``

val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, cmlG_def,DISJ_IMP_THM, FORALL_AND_THM,
               finite_mapTheory.FAPPLY_FUPDATE_THM, LET_THM,Ndl_def,Lfl_def,
               validMultSym_def])
 ``valid_ptree cmlG ^ast``

val _ = if aconv (rhs (concl check_results)) T then print "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"
