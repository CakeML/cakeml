open HolKernel Parse boolLib bossLib

open mmlPEGTheory gramTheory mmlPtreeConversionTheory
     mmlvalidTheory grammarTheory lexer_funTheory

local open ASCIInumbersLib in end

val _ = new_theory "mmlTests"

val _ = overload_on ("NN", ``λn. Nd (mkNT n)``)
val _ = overload_on ("Tf", ``λt. Lf (TK t)``)
val _ = overload_on ("Tfa", ``λs. Lf (TK (AlphaT s))``)
val _ = overload_on ("Tfs", ``λs. Lf (TK (SymbolT s))``)
val _ = overload_on (
  "EREL",
  ``λl. NN nE [NN nEhandle
                  [NN nElogicOR
                      [NN nElogicAND
                          [NN nEtyped [NN nEbefore [NN nEcomp l]]]]]]``)
val _ = overload_on (
  "EB",
  ``λl. EREL [NN nErel [NN nEadd [NN nEmult [NN nEapp [NN nEbase l]]]]]``)

val result_t = ``Result``
fun parsetest0 nt sem s opt = let
  val s_t = stringSyntax.lift_string bool s
  val _ = print ("Lexing "^s^"\n")
  val t = time (rhs o concl o EVAL) ``lexer_fun ^s_t``
  val ttoks = rhs (concl (EVAL ``MAP TK ^t``))
  val _ = print ("Parsing\n")
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
                | SOME t =>
                  let
                    val rt = rhs (concl (time EVAL t))
                  in
                    if optionSyntax.is_some rt then
                      rand rt
                    else die ("Sem. failure", rt)
                  end
          val _ = diag ("Semantics ("^term_to_string sem^") to ", ptree_res)
          val _ = if not (optionSyntax.is_none ptree_res) then
                    case opt of
                        NONE => ()
                      | SOME t => if aconv t ptree_res then
                                    print "Semantic output as expected\n"
                                  else
                                    die ("Semantics not required ", t)
                  else ()
          val valid_t = ``valid_ptree mmlG ^res``
          val vth = time EVAL valid_t
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

fun parsetest t1 t2 s = parsetest0 t1 t2 s NONE
fun tytest0 s r = parsetest0 ``nType`` ``ptree_Type`` s (SOME r)
val tytest = parsetest ``nType`` ``ptree_Type``

val elab_decls = ``OPTION_MAP (elab_decs NONE [] []) o ptree_Decls``

val _ = tytest "'a"
val _ = tytest "'a -> bool"
val _ = tytest "'a -> bool -> foo"
val _ = tytest "('a)"
val _ = tytest0 "('a)list" ``Ast_Tapp [Ast_Tvar "'a"] (Short "list")``
val _ = tytest "('a->bool)list"
val _ = tytest "'a->bool list"
val _ = tytest "('a->bool)->bool"
val _ = tytest0 "('a,foo)bar"
                ``Ast_Tapp [Ast_Tvar "'a"; Ast_Tapp [] (Short "foo")]
                           (Short "bar")``
val _ = tytest "('a) list list"
val _ = tytest "('a,'b) foo list"
val _ = tytest "'a list"
val _ = tytest "'a list list"
val _ = tytest "bool list list"
val _ = tytest "('a,bool list)++"
val _ = parsetest0 ``nREPLPhrase`` ``ptree_REPLPhrase``
          "case g of C p1 => e1 | p2 => e2;"
          (SOME ``[Ast_Tdec
                     (Ast_Dlet
                        (Ast_Pvar "it")
                        (Ast_Mat (Ast_Var (Short "g"))
                                 [(Ast_Pcon (Short "C") [Ast_Pvar "p1"],
                                   Ast_Var (Short "e1"));
                                  (Ast_Pvar "p2", Ast_Var (Short "e2"))]))]``)

val _ = parsetest0 ``nREPLPhrase`` ``ptree_REPLPhrase``
                   "structure s :> sig type 'a t type ('b,'c) u val z : 'a t end = struct end;"
                   (SOME ``[Ast_Tmod "s"
                                     (SOME [Ast_Stype_opq ["'a"] "t";
                                            Ast_Stype_opq ["'b"; "'c"] "u";
                                            Ast_Sval "z"
                                                     (Ast_Tapp [Ast_Tvar "'a"]
                                                               (Short "t"))])
                                     []]``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "4 handle x => 3 + 4"
                   (SOME ``Ast_Handle (Ast_Lit (IntLit 4))
                                      "x"
                                      (Ast_App (Ast_App (Ast_Var (Short "+"))
                                                        (Ast_Lit (IntLit 3)))
                                               (Ast_Lit (IntLit 4)))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE``
                   "if raise 4 then 2 else 3 handle f => 23"
                   (SOME ``Ast_If (Ast_Raise (Int_error 4))
                                  (Ast_Lit (IntLit 2))
                                  (Ast_Handle
                                     (Ast_Lit (IntLit 3))
                                     "f"
                                     (Ast_Lit (IntLit 23)))``);
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "f x handle n => case n of 0 => raise Div\n\
                  \                        | 1 => raise Bind\n\
                  \                        | _ => n - 2"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "C(3)"
                   (SOME ``Ast_Con (Short "C") [Ast_Lit (IntLit 3)]``)

val _ = parsetest ``nREPLPhrase`` ``ptree_REPLPhrase``
                  "val x = z : S.ty -> bool;"
val _ = parsetest ``nREPLPhrase`` ``ptree_REPLPhrase``
                  "val S.C x = z;"
val _ = parsetest ``nREPLPhrase`` ``ptree_REPLPhrase`` "val x = str.y;"
val _ = parsetest ``nREPLPhrase`` ``ptree_REPLPhrase`` "val x = 10 val y = 3;"
val _ = parsetest ``nREPLPhrase`` ``ptree_REPLPhrase`` "x + 10;"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec``
                  "structure s = struct val x = 3 end"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec``
                  "structure s :> sig val x : int end = struct val x = 3 end"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec``
                  "structure s :> sig val x : int; end = struct val x = 3 end"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec`` "val x = 10"
val _ = parsetest ``nDecls`` elab_decls "fun f x y = x + y"
val _ = parsetest ``nDecls`` elab_decls
                  "datatype 'a list = Nil | Cons of 'a * 'a list \
                  \fun map f l = case l of Nil => Nil \
                  \                      | Cons(h,t) => Cons(f h, map f t)"
val _ = parsetest ``nDecls`` elab_decls "val x = f()"
val _ = parsetest ``nDecls`` elab_decls "val () = f x"
val _ = parsetest ``nDecls`` elab_decls "val x = ref false;"
val _ = parsetest ``nDecls`` elab_decls "val ref y = f z"
val _ = parsetest ``nDecls`` elab_decls "val x = (y := 3);"
val _ = parsetest ``nDecls`` elab_decls "val _ = (y := 3);"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "(f x; 3)"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "let val x = 2 in f x; g (x + 1); 3 end"
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "case x of Nil => 0 | Cons(h,t) => 1 + len t"
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "case x of Nil => 0\n\
                  \        | Cons(h,t) => case h of 0 => 0\n\
                  \                               | x => x*2 + len t"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "let in 3 end"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "let ; in 3 end"
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "let val x = 3 val y = 4 in x + y end"
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "let val x = 3; val y = 4; in x + y end"
val _ = parsetest ``nDecl`` ``ptree_Decl`` "val x = 3"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "val x = 3;"
val _ = parsetest ``nDecl`` ``ptree_Decl`` "val C x = 3"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "val x = 3; val C y = f z"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "val C(x,y) = foo"
val _ = parsetest ``nDecl`` ``ptree_Decl`` "fun f x = x"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "datatype foo = C | D"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "datatype foo = C | D val x = y"
val _ = parsetest ``nPbase`` ``ptree_Pattern nPbase`` "3"
val _ = parsetest ``nPbase`` ``ptree_Pattern nPbase`` "x"
val _ = parsetest ``nPbase`` ``ptree_Pattern nPbase`` "C"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "(3)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C D"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,D)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,D(1),true)"

val _ = parsetest ``nStarTypes`` ``ptree_StarTypes F`` "'a"
val _ = parsetest ``nStarTypesP`` ``ptree_StarTypes T`` "'a * bool"
val _ = parsetest ``nStarTypesP`` ``ptree_StarTypes T`` "('a * bool)"
val _ = parsetest ``nStarTypesP`` ``ptree_StarTypes T``
                  "('a * bool * (bool -> bool))"
val _ = parsetest ``nTypeName`` ``ptree_TypeName`` "bool"
val _ = parsetest ``nTypeName`` ``ptree_TypeName``
                  "'a list"
val _ = parsetest ``nTypeName`` ``ptree_TypeName``
                  "('a,'b) foo"
val _ = parsetest ``nConstructorName`` T "Cname"
val _ = parsetest ``nDconstructor`` ``ptree_Dconstructor`` "Cname"
val _ = parsetest ``nDconstructor`` ``ptree_Dconstructor``
                  "Cname of bool * 'a"
val _ = parsetest ``nDtypeDecl`` ``ptree_DtypeDecl``
                  "'a foo = C of 'a | D of bool | E"
val _ = parsetest ``nTypeDec`` ``ptree_TypeDec``
                  "datatype 'a foo = C of 'a | D of bool | E and bar = F | G"

(* expressions *)
val _ = parsetest ``nEbase`` ``ptree_Expr nEbase`` "x"
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f x y"
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f true y"
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f true Constructor"
val _ = parsetest ``nElist1`` ``ptree_Expr nElist1`` "x"
val _ = parsetest ``nElist1`` ``ptree_Expr nElist1`` "x,2"
val _ = parsetest ``nElist2`` ``ptree_Expr nElist2`` "x,2"
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "C (x)"
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "C(x, y)"
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "f x * 3"
val _ = parsetest ``nErel`` ``ptree_Expr nErel`` "x <> true"
val _ = parsetest ``nEcomp`` ``ptree_Expr nEcomp`` "x <> true"
val _ = parsetest ``nEcomp`` ``ptree_Expr nEcomp`` "f o g z"
val _ = parsetest ``nEtyped`` ``ptree_Expr nEtyped`` "map f Nil : 'a list"
val _ = parsetest ``nElogicOR`` ``ptree_Expr nElogicOR``
                  "3 < x andalso x < 10 orelse p andalso q"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "if x < 10 then f x else C(x,3,g x)"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "1 + 2 + 3"
                   (SOME ``Ast_App
                             (Ast_App (Ast_Var (Short "+"))
                                      (Ast_App
                                         (Ast_App (Ast_Var (Short "+"))
                                                  (Ast_Lit (IntLit 1)))
                                         (Ast_Lit (IntLit 2))))
                             (Ast_Lit (IntLit 3))``)
val _ = parsetest ``nE`` ``ptree_Expr nE`` "x = 3"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "if x = 10 then 3 else 4"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "let val x = 3 in x + 4 end"
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "let fun sqr x = x * x in sqr 3 + y end"
val _ = parsetest  ``nE`` ``ptree_Expr nE``
                   "let fun f x = 1 and g x = 3 in 10 end"
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "let fun f1 x = x * f2 (x - 1)\n\
                  \    and f2 y = if y = 2 then 1 else f1 (y + 2)\n\
                  \in f1 (3 + y)\n\
                  \end"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "fn v => v + 2"

val _ = export_theory()
