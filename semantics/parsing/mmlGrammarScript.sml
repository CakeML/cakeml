open HolKernel Parse boolLib bossLib

open TokensTheory mmlTokenUtilsTheory AstTheory grammarTheory

open lcsymtacs grammarLib monadsyntax

val _ = new_theory "mmlGrammar"

(* ----------------------------------------------------------------------
    We'll be using the option monad quite a bit in what follows
   ---------------------------------------------------------------------- *)

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def"]

val assert_def = Define`assert b = if b then SOME() else NONE`

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
    Define the Mini ML CFG
   ---------------------------------------------------------------------- *)

val tokmap0 =
    List.foldl (fn ((s,t), acc) => Binarymap.insert(acc,s,t))
               (Binarymap.mkDict String.compare)
               [("(", ``LparT``), (")", ``RparT``), (",", ``CommaT``),
                (";", ``SemicolonT``),
                ("->", ``ArrowT``), ("=>", ``DarrowT``),
                ("*", ``StarT``),
                ("|", ``BarT``), ("=", ``EqualsT``), (":", ``ColonT``),
                ("and", ``AndT``),
                ("andalso", ``AndalsoT``),
                ("before", ``AlphaT "before"``),
                ("case", ``CaseT``),
                ("datatype", ``DatatypeT``),
                ("else", ``ElseT``),
                ("end", ``EndT``),
                ("false", ``AlphaT "false"``),
                ("fn", ``FnT``),
                ("fun", ``FunT``),
                ("if", ``IfT``),
                ("in", ``InT``),
                ("let", ``LetT``),
                ("o", ``AlphaT "o"``),
                ("of", ``OfT``),
                ("orelse", ``OrelseT``),
                ("raise", ``RaiseT``),
                ("ref", ``AlphaT "ref"``),
                ("then", ``ThenT``),
                ("true", ``AlphaT "true"``),
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

 (* optional semicolon NT *)
 OptSemi ::= ";" | ;

 (* expressions - base cases and function applications *)
 ConstructorName ::= ^(``{AlphaT s | s ≠ "" ∧ isUpper (HD s)}``)
                  | "true" | "false" | "ref";
 V ::= ^(``{AlphaT s | s ∉ {"before"; "div"; "mod"; "o"; "true"; "false"; "ref" } ∧
                       s ≠ "" ∧ ¬isUpper (HD s)}``)
    |  ^(``{SymbolT s |
            s ∉ {"+"; "*"; "-"; "/"; "<"; ">"; "<="; ">="; "<>"}}``);
 Ebase ::= "(" Eseq ")" | V | ConstructorName | <IntT>
        |  "let" LetDecs "in" Eseq "end";
 Eseq ::= Eseq ";" E | E;
 Etuple ::= "(" Elist2 ")";
 Elist2 ::= E "," Elist1;
 Elist1 ::= E | Elist1 "," E;
 Eapp ::= Eapp Ebase | Ebase
        | ConstructorName Etuple;

 (* expressions - binary operators *)
 MultOps ::= ^(``{AlphaT "div"; AlphaT "mod"; StarT; SymbolT "/"}``);
 AddOps ::= ^(``{SymbolT "+"; SymbolT "-"}``);
 RelOps ::= ^(``{SymbolT s | s ∈ {"<"; ">"; "<="; ">="; "<>"}}``) | "=";
 Emult ::= Emult MultOps Eapp | Eapp;
 Eadd ::= Eadd AddOps Emult | Emult;
 Erel ::= Eadd RelOps Eadd | Eadd;
 Ecomp ::= Ecomp "o" Erel | Erel;
 Ebefore ::= Ebefore "before" Ecomp | Ecomp;
 Etyped ::= Ebefore | Ebefore ":" Type;
 ElogicAND ::= ElogicAND "andalso" Etyped | Etyped;
 ElogicOR ::= ElogicOR "orelse" ElogicAND | ElogicAND;
 E ::= "if" E "then" E "else" E | "case" E "of" PEs | "fn" V "=>" E | "raise" E
    |  ElogicOR;

 (* function and value declarations *)
 FDecl ::= V V "=" E ;
 AndFDecls ::= FDecl | AndFDecls "and" FDecl;
 Decl ::= "val" Pattern "=" E  | "fun" AndFDecls |  TypeDec | ";" ;
 Decls ::= Decl Decls | ;
 LetDec ::= "val" V "=" E | "fun" AndFDecls | ";" ;
 LetDecs ::= LetDec LetDecs | ;

 (* patterns *)
 Pbase ::= V | ConstructorName | <IntT> | "(" Pattern ")";
 Pattern ::= ConstructorName Ptuple |  ConstructorName Pbase | Pbase;
 Ptuple ::= "(" PatternList2 ")";
 PatternList2 ::= Pattern "," PatternList1;
 PatternList1 ::= Pattern | PatternList1 "," Pattern;
 PE ::= Pattern "=>" E;
 PEs ::= PE | PEs "|" PE;
`;

val _ = type_abbrev("NT", ``:MMLnonT inf``)
val _ = overload_on("mkNT", ``INL : MMLnonT -> NT``)

val _ = overload_on ("NN", ``\nt. NT (mkNT nt)``)
val _ = overload_on ("TK", ``TOK : token -> (token,MMLnonT)symbol``)
val _ = type_abbrev("mlptree", ``:(token, MMLnonT) parsetree``)

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

val _ = computeLib.add_persistent_funs ["nt_distinct_ths"]

val ast = ``Nd (mkNT nEmult) [
              Nd (mkNT nEmult) [
                Nd (mkNT nEmult) [
                  Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 3))]]
                ];
                Nd (mkNT nMultOps) [Lf (TK StarT)];
                Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 4))]]
              ];
              Nd (mkNT nMultOps) [Lf (TK (SymbolT "/"))];
              Nd (mkNT nEapp) [Nd (mkNT nEbase) [Lf (TK (IntT 5))]]
            ]``

val check_results =
    time (SIMP_CONV (srw_ss())
              [valid_ptree_def, mmlG_def,DISJ_IMP_THM, FORALL_AND_THM])
 ``valid_ptree mmlG ^ast``

val _ = if aconv (rhs (concl check_results)) T then print "valid_ptree: OK\n"
        else raise Fail "valid_ptree: failed"

val _ = export_theory()
