open HolKernel Parse boolLib bossLib

open mmlPEGTheory mmlGrammarTheory mmlPtreeConversionTheory grammarTheory

val _ = new_theory "mmlTests"


val result_t = ``Result``
fun parsetest nt sem s t = let
  val ttoks = rhs (concl (EVAL ``MAP TK ^t``))
  val _ = print ("Evaluating "^s^"\n")
  val evalth = time EVAL
                    ``peg_exec mmlPEG (nt (mkNT ^nt) I) ^t [] done failed``
  val r = rhs (concl evalth)
  fun diag(s,t) = let
    fun pp pps (s,t) =
        (PP.begin_block pps PP.CONSISTENT 0;
         PP.add_string pps s;
         PP.add_break pps (1,2);
         pp_term pps t;
         PP.end_block pps)
  in
    print (PP.pp_to_string 79 pp (s,t) ^ "\n")
  end
  fun die (s,t) = (diag (s,t); raise Fail "Failed")

in
  if same_const (rator r) result_t then
    if optionSyntax.is_some (rand r) then let
      val pair = rand (rand r)
      val remaining_input = pair |> rator |> rand
      val res = pair |> rand |> rator |> rand
    in
      if listSyntax.is_nil remaining_input then let
        val _ = diag ("EVAL to: ", res)
        val fringe_th = EVAL ``ptree_fringe ^res``
        val fringe_t = rhs (concl fringe_th)
        val _ = diag ("fringe = ", fringe_t)
      in
        if aconv fringe_t ttoks then let
          val ptree_res =
              case Lib.total mk_comb(sem,res) of
                  NONE => optionSyntax.mk_none bool
                | SOME t => rhs (concl (time EVAL t))
          val _ = diag ("Semantics ("^term_to_string sem^") to ", ptree_res)
          val valid_t = ``valid_ptree mmlG ^res``
          val vth = SIMP_CONV (srw_ss())
                              [grammarTheory.valid_ptree_def, mmlG_def,
                               DISJ_IMP_THM, FORALL_AND_THM,
                               stringTheory.isUpper_def]
                              valid_t
          val vres = rhs (concl vth)
        in
          if aconv boolSyntax.T vres then print "Valid\n"
          else die ("Invalid parse-tree: ", vres)
        end
        else die ("Fringe not preserved!", ttoks)
      end
      else die ("REMANING INPUT:", pair)
    end
    else die ("FAILED:", r)
  else die ("NO RESULT:", r)
end
val tytest = parsetest ``nType`` ``ptree_Type``

val _ = tytest "'a" ``[TyvarT "'a"]``
val _ = tytest "'a -> bool" ``[TyvarT "'a"; ArrowT; AlphaT "bool"]``
val _ = tytest "'a -> bool -> foo"
                     ``[TyvarT "'a"; ArrowT; AlphaT "bool"; ArrowT;
                        AlphaT "foo"]``
val _ = tytest "('a)" ``[LparT; TyvarT "'a"; RparT]``
val _ = tytest "('a)list" ``[LparT; TyvarT "'a"; RparT; AlphaT "list"]``
val _ = tytest "('a->bool)list"
               ``[LparT; TyvarT "'a"; ArrowT; AlphaT "bool"; RparT;
                  AlphaT "list"]``
val _ = tytest "'a->bool list"
               ``[TyvarT "'a"; ArrowT; AlphaT "bool"; AlphaT "list"]``
val _ = tytest "('a->bool)->bool"
                     ``[LparT; TyvarT "'a"; ArrowT; AlphaT "bool"; RparT;
                        ArrowT; AlphaT "bool"]``
val _ = tytest "('a,foo)bar"
                     ``[LparT; TyvarT "'a";CommaT;AlphaT"foo";
                        RparT;AlphaT"bar"]``
val _ = tytest "('a) list list" ``[LparT; TyvarT "'a"; RparT; AlphaT"list";
                                   AlphaT"list"]``
val _ = tytest "('a,'b) foo list"
               ``[LparT; TyvarT "'a"; CommaT; TyvarT"'b"; RparT; AlphaT"foo";
                  AlphaT"list"]``
val _ = tytest "'a list" ``[TyvarT "'a"; AlphaT "list"]``
val _ = tytest "'a list list" ``[TyvarT "'a"; AlphaT "list"; AlphaT "list"]``
val _ = tytest "bool list list" ``[AlphaT "bool"; AlphaT "list"; AlphaT "list"]``
val _ = tytest "('a,bool list)++"
               ``[LparT; TyvarT "'a"; CommaT; AlphaT "bool"; AlphaT "list";
                  RparT; SymbolT"++"]``
val _ = parsetest ``nStarTypes`` ``ptree_StarTypes F`` "'a" ``[TyvarT "'a"]``;
val _ = parsetest ``nStarTypesP`` ``ptree_StarTypes T`` "'a * bool"
                  ``[TyvarT "'a"; StarT; AlphaT "bool"]``
val _ = parsetest ``nStarTypesP`` ``ptree_StarTypes T`` "('a * bool)"
                  ``[LparT; TyvarT "'a"; StarT; AlphaT "bool"; RparT]``
val _ = parsetest ``nStarTypesP`` ``ptree_StarTypes T``
                  "('a * bool * (bool -> bool))"
                  ``[LparT; TyvarT "'a"; StarT; AlphaT "bool"; StarT;
                     LparT; AlphaT "bool"; ArrowT; AlphaT "bool"; RparT;
                     RparT]``
val _ = parsetest ``nTypeName`` ``ptree_TypeName`` "bool" ``[AlphaT "bool"]``
val _ = parsetest ``nTypeName`` ``ptree_TypeName``
                  "'a list"
                  ``[TyvarT "'a"; AlphaT "list"]``
val _ = parsetest ``nTypeName`` ``ptree_TypeName``
                  "('a,'b) foo"
                  ``[LparT; TyvarT "'a"; CommaT; TyvarT "'b"; RparT;
                     AlphaT "foo"]``
val _ = parsetest ``nConstructorName`` T "Cname" ``[AlphaT "Cname"]``
val _ = parsetest ``nDconstructor`` ``ptree_Dconstructor`` "Cname"
                  ``[AlphaT "Cname"]``
val _ = parsetest ``nDconstructor`` ``ptree_Dconstructor``
                  "Cname of bool * 'a"
                  ``[AlphaT "Cname"; OfT; AlphaT "bool"; StarT; TyvarT "'a"]``
val _ = parsetest ``nDtypeDecl`` ``ptree_DtypeDecl``
                  "'a foo = C of 'a | D of bool | E"
                  ``[TyvarT "'a"; AlphaT "foo"; EqualsT;
                     AlphaT "C"; OfT; TyvarT "'a"; BarT;
                     AlphaT "D"; OfT; AlphaT "bool"; BarT; AlphaT "E"]``
val _ = parsetest ``nTypeDec`` ``ptree_TypeDec``
                  "datatype 'a foo = C of 'a | D of bool | E and bar = F | G"
                  ``[DatatypeT; TyvarT "'a"; AlphaT "foo"; EqualsT;
                     AlphaT "C"; OfT; TyvarT "'a"; BarT;
                     AlphaT "D"; OfT; AlphaT "bool"; BarT; AlphaT "E"; AndT;
                     AlphaT "bar"; EqualsT; AlphaT "F"; BarT; AlphaT "G"]``

(* expressions *)
val _ = parsetest ``nEbase`` ``ptree_Expr nEbase`` "x" ``[AlphaT "x"]``
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f x y"
                  ``[AlphaT "f"; AlphaT"x"; AlphaT"y"]``
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f true y"
                  ``[AlphaT "f"; AlphaT"true"; AlphaT"y"]``
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f true Constructor"
                  ``[AlphaT "f"; AlphaT"true"; AlphaT"Constructor"]``
val _ = parsetest ``nElist1`` ``ptree_Expr nElist1`` "x"
                  ``[AlphaT "x"]``
val _ = parsetest ``nElist1`` ``ptree_Expr nElist1`` "x,2"
                  ``[AlphaT "x"; CommaT; IntT 2]``
val _ = parsetest ``nElist2`` ``ptree_Expr nElist2`` "x,2"
                  ``[AlphaT "x"; CommaT; IntT 2]``
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "C (x)"
                  ``[AlphaT "C"; LparT; AlphaT "x"; RparT]``
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "C(x, y)"
                  ``[AlphaT "C"; LparT; AlphaT "x"; CommaT; AlphaT "y"; RparT]``
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult``
                  "f x * 3"
                  ``[AlphaT "f"; AlphaT "x"; StarT; IntT 3]``
val _ = parsetest ``nErel`` ``ptree_Expr nErel`` "x <> true"
                  ``[AlphaT "x"; SymbolT "<>"; AlphaT "true"]``
val _ = parsetest ``nEcomp`` ``ptree_Expr nEcomp`` "x <> true"
                  ``[AlphaT "x"; SymbolT "<>"; AlphaT "true"]``
val _ = parsetest ``nEcomp`` ``ptree_Expr nEcomp`` "f o g z"
                  ``[AlphaT "f"; AlphaT "o"; AlphaT "g"; AlphaT"z"]``
val _ = parsetest ``nEtyped`` T "map f Nil : 'a list"
                  ``[AlphaT "map"; AlphaT "f"; AlphaT"Nil"; ColonT;
                     TyvarT "'a"; AlphaT "list"]``
val _ = parsetest ``nElogicOR`` T "3 < x andalso x < 10 orelse p andalso q"
                  ``[IntT 3; SymbolT "<"; AlphaT "x"; AndalsoT;
                     AlphaT "x"; SymbolT "<"; IntT 10; OrelseT;
                     AlphaT"p"; AndalsoT; AlphaT "q"]``

val _ = parsetest ``nE`` ``ptree_Expr nE`` "if x < 10 then f x else C(x,3,g x)"
                  ``[IfT; AlphaT "x"; SymbolT "<"; IntT 10;
                     ThenT; AlphaT "f"; AlphaT "x";
                     ElseT; AlphaT "C";
                     LparT; AlphaT "x";CommaT;IntT 3;CommaT;
                     AlphaT "g"; AlphaT "x"; RparT]``

val _ = parsetest ``nE`` ``ptree_Expr nE`` "let val x = 3 in x + 4 end"
                  ``[LetT; ValT; AlphaT "x"; EqualsT; IntT 3; InT; AlphaT "x";
                     SymbolT "+"; IntT 4; EndT]``



val _ = export_theory()
