open HolKernel Parse boolLib bossLib

open TokensTheory AstTheory grammarTheory

val _ = new_theory "mmlGrammar"

val _ = Hol_datatype`
  MMLnonT = nV |
    nEbase | nEapp | nEmult | nEadd | nEcons | nErel | nEcomp | nEbefore |
    nElogic | nE | nError | nLogicalOp | nLiteral | nFDecl
    | nAndFDecls | nPEs | nPE
    | nPattern | nType | nDType | nTypeList | nTypeDec | nDtypeDecls
    | nDtypeDecl | nTypeName | nTyVarList | nDconstructor | nDtypeCons
    | nStarTypes | nDecl
    | nMultOps | nAddOps | nConsOps | nRelOps | nCompOps | nBeforeOps
`;

val _ = type_abbrev("NT", ``:MMLnonT inf``)
val _ = overload_on("mkNT", ``INL : MMLnonT -> NT``)

val _ = overload_on ("NN", ``\nt. NT (mkNT nt)``)
val _ = overload_on ("TK", ``TOK : token -> (token,MMLnonT)symbol``)

val V_rules_def = Define`
  V_rules =
   {(mkNT nV, [TK (AlphaT s)]) | T } ∪
   {(mkNT nV, [TK (SymbolT s)]) | T } ∪
   {(mkNT nV, [TK OpT; TK (SymbolT s)]) | T }`

val mkRules_def = Define`
  mkRules n rset = IMAGE (\r. (mkNT n, r)) rset
`

val Ebase_rules_def = Define`
  Ebase_rules =
    mkRules nEbase
      ({[TK LparT; NN nE; TK RparT];
        [NN nV];
        [TK LetT; TK ValT; NN nV; TK EqualsT; NN nE; TK InT;
         NN nE; TK EndT];
        [TK LetT; TK FunT; NN nAndFDecls; TK InT; NN nE; TK EndT]} ∪
      { [TK (IntT i)] | T })
`

val binop_rule_def = Define`
  binop_rule tight loose opn = mkRules loose {
    [NN loose; NN opn; NN tight];
    [NN tight]
  }`

val Eapp_rules_def = Define`
  Eapp_rules = mkRules nEapp {
    [NN nEapp; NN nEbase];
    [NN nEbase]
  }`

(* various left associative binary operators *)
val Emult_rules_def = Define`
  Emult_rules = binop_rule nEapp nEmult nMultOps
`;
val Eadd_rules_def = Define`
  Eadd_rules = binop_rule nEmult nEadd nAddOps
`;
val Erel_rules_def = Define`
  Erel_rules = binop_rule nEcons nErel nConsOps
`;
val Ecomp_rules_def = Define`
  Ecomp_rules = binop_rule nErel nEcomp nCompOps
`;
val Ebefore_rules_def = Define`
  Ebefore_rules = binop_rule nEcomp nEbefore nBeforeOps
`;

(* right associative list ops fit into the middle of the above *)
val Econs_rules_def = Define`
  Econs_rules = mkRules nEcons {
    [NN nEadd; NN nConsOps; NN nEcons]; [NN nEadd]
  }
`;


(* ----------------------------------------------------------------------
    Parse trees to abstract syntax
   ---------------------------------------------------------------------- *)

val _ = type_abbrev("mlptree", ``:(token, MMLnonT) parsetree``)

open monadsyntax
val _ = overload_on ("monad_bind", ``OPTION_BIND``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def"]

val ptree_Expr_def = Define`
  ptree_Expr (Lf _) = NONE ∧
  ptree_Expr (Nd nt subs) =
    case nt of
      mkNT nEbase =>
        (case subs of
           [Lf (TK LparT); Nd t s; Lf (TK RparT)] => ptree_Expr (Nd t s)
         | [Lf (TK (IntT i))] => SOME (Ast_Lit (IntLit i))
         | _ => NONE)
   | mkNT nEapp =>
       (case subs of
          [t1; t2] => do
            a1 <- ptree_Expr t1;
            a2 <- ptree_Expr t2;
            SOME(Ast_App a1 a2)
          od
        | [t] => ptree_Expr t
        | _ => NONE)
   | _ => NONE
`;

val _ = export_theory()
