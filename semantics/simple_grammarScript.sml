open preamble

open tokensTheory grammarTheory

open grammarLib

val _ = new_theory "simple_grammar"
val _ = set_grammar_ancestry ["tokens", "grammar"]

(* ----------------------------------------------------------------------
    Define an ambiguous but simple version of the CakeML grammar.

    This is supposed to accept/define the same set of strings but doesn't
    have to bother with complicated precedence levels and the like.
   ---------------------------------------------------------------------- *)

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
                ("false", ``AlphaT "false"``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("handle", ``HandleT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("IntError", ``AlphaT "IntError"``),
                ("let", ``LetT``),
                ("nil", ``AlphaT "nil"``),
                ("o", ``AlphaT "o"``),
                ("of", ``OfT``),
                ("op", ``OpT``),
                ("orelse", ``OrelseT``),
                ("raise", ``RaiseT``),
                ("ref", ``AlphaT "ref"``),
                ("sig", ``SigT``),
                ("struct", ``StructT``),
                ("structure", ``StructureT``),
                ("then", ``ThenT``),
                ("true", ``AlphaT "true"``),
                ("type", ``TypeT``),
                ("val", ``ValT``)]
fun tokmap s =
    case Binarymap.peek(tokmap0, s) of
        NONE => raise Fail ("No token binding for "^s)
      | SOME t => t

val ginfo = { tokmap = tokmap,
              tokty = ``:token``, nt_tyname = "SCMLnonT",
              start = "TopLevelDecs",
              gname = "scmlG", mkntname = (fn s => "sn" ^ s) }

val cmlG_def = mk_grammar_def ginfo
`(* types *)
 UQTyOp ::= <AlphaT> | <SymbolT>;
 TyvarN ::= <TyvarT>;
 TyOp ::= UQTyOp | <LongidT>;
 TypeList1 ::= Type | Type "," TypeList1;
 TypeList2 ::= Type "," TypeList1;
 Type ::= <TyvarT> | TyOp | "(" TypeList2 ")" TyOp | "(" Type ")"
       |  Type TyOp | Type "*" Type | Type "->" Type ;

 (* type declarations *)
 TypeName ::= UQTyOp | "(" TyVarList ")" UQTyOp | <TyvarT> UQTyOp ;
 TyVarList ::= TyvarN | TyVarList "," TyvarN;
 Dconstructor ::= UQConstructorName "of" Type | UQConstructorName;
 DtypeCons ::= Dconstructor | DtypeCons "|" Dconstructor;
 DtypeDecl ::= TypeName "=" DtypeCons ;
 DtypeDecls ::= DtypeDecl | DtypeDecls "and" DtypeDecl;
 TypeDec ::= "datatype" DtypeDecls;
 TypeAbbrevDec ::= "type" TypeName "=" Type;

 (* expressions - base cases and function applications *)
 UQConstructorName ::= ^(``{AlphaT s | s ≠ "" ∧ isUpper (HD s)}``)
                    | "true" | "false" | "ref" | "nil";
 ConstructorName ::=
     UQConstructorName
  | ^(``{LongidT str s | str,s | s ≠ "" ∧ isAlpha (HD s) ∧ isUpper (HD s) ∨
                                 s ∈ {"true"; "false"; "ref"; "nil"}}``);
 V ::= ^(``{AlphaT s | s ∉ {"before"; "div"; "mod"; "o"; "true"; "false"; "ref";
                            "nil" } ∧
                       s ≠ "" ∧ ¬isUpper (HD s)}``)
    |  ^(``{SymbolT s |
            s ∉ {"+"; "*"; "-"; "/"; "<"; ">"; "<="; ">="; "<>"; ":=";
                 "::"; "@"}}``);
 FQV ::= V
      |  ^(``{LongidT str s | str,s |
              s ≠ "" ∧ (isAlpha (HD s) ⇒ ¬isUpper (HD s)) ∧
              s ∉ {"true"; "false"; "ref"; "nil"}}``) ;
 OpID ::= ^(``{LongidT str s | str,s | s ≠ ""}``)
       |  ^(``{AlphaT s | s ≠ ""}``)
       |  ^(``{SymbolT s | s ≠ ""}``)
       |  "*" | "=" ;

 Expr ::= <IntT> |  <CharT> | <StringT> | <WordT> |
       | "(" Eseq ")" | "(" Elist0 ")" | FQV | ConstructorName |
       | "let" LetDecs "in" Eseq "end" | "[" "]"
       | "[" Elist1 "]" | "op" OpID | Expr Expr
       | Expr BinOp Expr | Expr ":" Type
       | Expr "handle" PEs
       | "if" Expr "then" Expr "else" Expr | "case" Expr "of" PEs
       | "fn" Pattern "=>" Expr | "raise" Expr ;

 Eseq ::= E ";" Eseq | E;
 Elist0 ::=  | Elist1 ;
 Elist1 ::= E | E "," Elist1;

 (* expressions - binary operators *)
 BinOp ::= MultOps | AddOps | RelOps | CompOps | ListOps | "before" |
           "andalso" | "orelse" ;
 AddOps ::= ^(``{SymbolT "+"; SymbolT "-"}``) ;
 RelOps ::= ^(``{SymbolT s | s ∈ {"<"; ">"; "<="; ">="; "<>"}}``) | "=";
 CompOps ::= "o" | ":=";
 ListOps ::= "@" | "::";

 (* function and value declarations *)
 FDecl ::= V PbaseList1 "=" Expr ;
 AndFDecls ::= FDecl | AndFDecls "and" FDecl;
 Decl ::= "val" Pattern "=" Expr  | "fun" AndFDecls |  TypeDec
       |  "exception" Dconstructor
       | TypeAbbrevDec ;
 Decls ::= Decl Decls | ";" Decls | ;
 LetDec ::= "val" V "=" Expr | "fun" AndFDecls ;
 LetDecs ::= LetDec LetDecs | ";" LetDecs | ;

 (* patterns *)
 Pbase ::= V | ConstructorName | <IntT> | <StringT> | <CharT> | "_"
        |  "[" PatternList0 "]" | "(" PatternList0 ")";
 Pattern ::= Pattern "::" Pattern | Pattern ":" Type | Pbase
          |  ConstructorName Pbase;
 PatternList1 ::= Pattern | Pattern "," PatternList1 ;
 PatternList0 ::= | PatternList1 ;
 PbaseList1 ::= Pbase | Pbase PbaseList1 ;
 PE ::= Pattern "=>" E;
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
 Structure ::= "structure" StructName OptionalSignatureAscription "=" "struct" Decls "end";
 TopLevelDec ::= Structure | Decl;
 TopLevelDecs ::= Expr ";" TopLevelDecs | TopLevelDec NonETopLevelDecs
               | ";" TopLevelDecs | ;
 NonETopLevelDecs ::= TopLevelDec NonETopLevelDecs | ";" TopLevelDecs | ;
`;



val _ = export_theory()
