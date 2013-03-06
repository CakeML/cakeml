open HolKernel Parse boolLib bossLib

open TokensTheory AstTheory grammarTheory

val _ = new_theory "mmlGrammar"


(* ----------------------------------------------------------------------
    Define the Mini ML CFG
   ---------------------------------------------------------------------- *)

open grammarLib
val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                ("->", ``ArrowT``), ("*", ``StarT``),
                ("|", ``BarT``), ("=", ``EqualsT``),
                ("and", ``AndT``),
                ("datatype", ``DatatypeT``),
                ("end", ``EndT``),
                ("fun", ``FunT``),
                ("in", ``InT``),
                ("let", ``LetT``),
                ("of", ``OfT``),
                ("val", ``ValT``)]
fun tokmap s =
    case Binarymap.peek(tokmap0, s) of
        NONE => raise Fail ("No token binding for "^s)
      | SOME t => t

val ginfo = { tokmap = tokmap,
              tokty = ``:token``, nt_tyname = "MMLnonT",
              start = "Type",
              gname = "mmlG", mkntname = (fn s => "n" ^ s) }

val mmlG_def = mk_grammar_def ginfo
`(* types *)
 TyOp ::= <AlphaT> | <SymbolT>;
 TypeList ::= Type | Type "," TypeList;
 DType ::= <TyvarT> | TyOp | DType TyOp | "(" TypeList ")" TyOp | "(" Type ")";
 Type ::= DType | DType "->" Type;

 (* type declarations *)
 StarTypes ::= StarTypes "*" DType | DType;
 StarTypesP ::= "(" StarTypes ")" | StarTypes;
 TypeName ::= TyOp | "(" TyVarList ")" TyOp | <TyvarT> TyOp ;
 TyVarList ::= <TyvarT> | TyVarList "," <TyvarT>;
 Dconstructor ::= ConstructorName "of" StarTypesP | ConstructorName;
 DtypeCons ::= Dconstructor | DtypeCons "|" Dconstructor;
 DtypeDecl ::= TypeName "=" DtypeCons ;
 DtypeDecls ::= DtypeDecl | DtypeDecls "and" DtypeDecl;
 TypeDec ::= "datatype" DtypeDecls;

 (* expressions - base cases and function applications *)
 ConstructorName ::= ^(``{AlphaT s | s ≠ "" ∧ isUpper (HD s)}``);
 V ::= ^(``{AlphaT s | s ∉ {"before"; "div"; "mod"; "o" } ∧ s ≠ "" ∧
                       ¬isUpper (HD s)}``)
    |  ^(``{SymbolT s | s ∉ {"+"; "*"; "-"; "/"; "<"; ">"; "<="; ">="}}``);
 Ebase ::= "(" E ")" | V | ConstructorName | <IntT>
        |  "let" "val" V "=" E "in" E "end"
        |  "let" "fun" AndFDecls "in" E "end";
 Etuple ::= "(" Elist2 ")";
 Elist2 ::= Elist1 "," E;
 Elist1 ::= E | Elist1 "," E;
 Eapp ::= Eapp Ebase | Ebase
        | ConstructorName Etuple;

 (* expressions - binary operators *)
 MultOps ::= ^(``{AlphaT "div";AlphaT "mod";SymbolT "*";SymbolT "/"}``);
 AddOps ::= ^(``{SymbolT "+"; SymbolT "-"}``);
 RelOps ::= ^(``{SymbolT s | s ∈ {"<"; ">"; "<="; ">="; "<>"}}``) | EqualsT;
 CompOps ::= ^(``{AlphaT "o"}``);
 BeforeOps ::= ^(``{AlphaT "before"}``);
 Emult ::= Emult MultOps Eapp | Eapp;
 Eadd ::= Eadd AddOps Emult | Emult;
 Erel ::= Eadd RelOps Eadd | Eadd;
 Ecomp ::= Ecomp CompOps Erel | Erel;
 Ebefore ::= Ebefore BeforeOps Ecomp | Ecomp;
`;

val _ = type_abbrev("NT", ``:MMLnonT inf``)
val _ = overload_on("mkNT", ``INL : MMLnonT -> NT``)

val _ = overload_on ("NN", ``\nt. NT (mkNT nt)``)
val _ = overload_on ("TK", ``TOK : token -> (token,MMLnonT)symbol``)
val _ = type_abbrev("mlptree", ``:(token, MMLnonT) parsetree``)


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

val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, mmlG_def,DISJ_IMP_THM, FORALL_AND_THM])
 ``valid_ptree mmlG ^ast``

val _ = if aconv (rhs (concl check_results)) T then print "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"

val _ = export_theory()
