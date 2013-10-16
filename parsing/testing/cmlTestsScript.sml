open HolKernel Parse boolLib bossLib

open cmlPEGTheory gramTheory cmlPtreeConversionTheory
     grammarTheory lexer_funTheory

local open ASCIInumbersLib in end

val _ = new_theory "cmlTests"

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
  ``λl. EREL [NN nErel [NN nElistop [NN nEadd [NN nEmult [NN nEapp [NN nEbase l]]]]]]``)

val result_t = ``Result``
fun parsetest0 nt sem s opt = let
  val s_t = stringSyntax.lift_string bool s
  val _ = print ("**********\nLexing "^s^"\n")
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
        in
          if not (optionSyntax.is_none ptree_res) then
            case opt of
                NONE => ()
              | SOME t => if aconv t ptree_res then
                            print "Semantic output as expected\n"
                          else
                            die ("Semantics fails; is not the required ", t)
          else ()
        end
        else die ("Fringe not preserved!", ttoks)
      end
      else die ("REMANING INPUT:", pair)
    end
    else die ("FAILED:", r)
  else die ("NO RESULT:", r)
end

fun parsetest t1 t2 s = parsetest0 t1 t2 s NONE
fun tytest0 s r = parsetest0 ``nType`` ``ptree_Type nType`` s (SOME r)
val tytest = parsetest ``nType`` ``ptree_Type nType``

val elab_decls = ``OPTION_MAP (elab_decs NONE [] []) o ptree_Decls``

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val h::List.nil = [3]"
          (SOME ``Ast_Dlet
                    (Ast_Pcon (SOME (Short "::"))
                              [Ast_Pvar "h";
                               Ast_Pcon (SOME (Long "List" "nil")) []])
                    (Ast_Con (SOME (Short "::"))
                             [Ast_Lit (IntLit 3);
                              Ast_Con (SOME (Short "nil")) []])``)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val nil = f x"
          (SOME ``Ast_Dlet (Ast_Pcon (SOME (Short "nil")) [])
                           (Ast_App (Ast_Var (Short "f"))
                                    (Ast_Var (Short "x")))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE``
                   "case x of [] => 3 | [] :: _ => 1 | (h::t) :: rest => 2"
          (SOME ``Ast_Mat (Ast_Var (Short "x"))
                    [(Ast_Pcon (SOME (Short "nil")) [],Ast_Lit (IntLit 3));
                     (Ast_Pcon (SOME (Short "::"))
                               [Ast_Pcon (SOME (Short "nil")) []; Ast_Pvar "_"],
                      Ast_Lit (IntLit 1));
                     (Ast_Pcon (SOME (Short "::"))
                               [Ast_Pcon (SOME (Short "::"))
                                         [Ast_Pvar "h"; Ast_Pvar "t"];
                                Ast_Pvar "rest"],
                      Ast_Lit (IntLit 2))]``)


val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "case x of [] => 3 | [e, _] => e"
           (SOME ``Ast_Mat (Ast_Var (Short "x"))
                     [(Ast_Pcon (SOME (Short "nil")) [],Ast_Lit (IntLit 3));
                      (Ast_Pcon (SOME (Short "::"))
                                [Ast_Pvar "e";
                                 Ast_Pcon (SOME (Short "::"))
                                          [Ast_Pvar "_";
                                           Ast_Pcon (SOME (Short "nil")) []]],
                       Ast_Var (Short "e"))]``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "[3,4]"
                   (SOME ``Ast_Con (SOME (Short "::"))
                             [Ast_Lit (IntLit 3);
                              Ast_Con (SOME (Short "::"))
                                      [Ast_Lit (IntLit 4);
                                       Ast_Con (SOME (Short "nil")) []]]``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "[]"
                   (SOME ``Ast_Con (SOME (Short "nil")) []``);
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "3::t = l"
                   (SOME ``Ast_App
                            (Ast_App (Ast_Var (Short "="))
                                     (Ast_Con (SOME (Short "::"))
                                              [Ast_Lit (IntLit 3);
                                               Ast_Var (Short "t")]))
                            (Ast_Var (Short "l"))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "3 < x = true"
                   (SOME ``Ast_App
                            (Ast_App (Ast_Var (Short "="))
                                     (Ast_App (Ast_App (Ast_Var (Short "<"))
                                                       (Ast_Lit (IntLit 3)))
                                              (Ast_Var (Short "x"))))
                            (Ast_Lit (Bool T))``)

val _ = tytest0 "'a * bool"
                ``Ast_Tapp [Ast_Tvar "'a";
                            Ast_Tapp [] (SOME (Short "bool"))] NONE``
val _ = tytest0 "'a * bool * 'c"
                ``Ast_Tapp [Ast_Tvar "'a";
                            Ast_Tapp [] (SOME (Short "bool"));
                            Ast_Tvar "'c"] NONE``
val _ = tytest "'a * bool -> 'a"
val _ = tytest "'a * (bool * 'c)"
val _ = tytest "(bool * int)"
val _ = tytest "(bool list * int) * bool"
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "exception Foo"
                   (SOME ``Ast_Dexn "Foo" []``)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "exception Bar of int"
                   (SOME ``Ast_Dexn "Bar" [Ast_Tapp [] (SOME (Short "int"))]``)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "exception Bar of int * int"
                   (SOME ``Ast_Dexn "Bar"
                             [Ast_Tapp [] (SOME (Short "int"));
                              Ast_Tapp [] (SOME (Short "int"))]``);
val _ = parsetest ``nPType`` ``ptree_PType`` "'a"
val _ = parsetest ``nPType`` ``ptree_PType`` "'a * bool"
val _ = parsetest ``nPatternList`` ``ptree_Plist`` "x,y"
val _ = parsetest ``nPtuple`` ``ptree_Pattern nPtuple`` "(x,y)"

val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,y)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "(x,3)"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "(x,y,4)"
                   (SOME ``Ast_Con NONE [Ast_Var (Short "x");
                                         Ast_Var (Short "y");
                                         Ast_Lit (IntLit 4)]``);
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "C(x,3)"
                   (SOME ``Ast_Con (SOME (Short "C"))
                                   [Ast_Var (Short "x"); Ast_Lit (IntLit 3)]``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "f(x,3)"
                   (SOME ``Ast_App (Ast_Var (Short "f"))
                                   (Ast_Con NONE
                                            [Ast_Var (Short "x");
                                             Ast_Lit (IntLit 3)])``)

val _ = tytest "'a"
val _ = tytest "'a -> bool"
val _ = tytest "'a -> bool -> foo"
val _ = tytest "('a)"
val _ = tytest0 "('a)list" ``Ast_Tapp [Ast_Tvar "'a"] (SOME(Short "list"))``
val _ = tytest "('a->bool)list"
val _ = tytest "'a->bool list"
val _ = tytest "('a->bool)->bool"
val _ = tytest0 "('a,foo)bar"
                ``Ast_Tapp [Ast_Tvar "'a"; Ast_Tapp [] (SOME(Short "foo"))]
                           (SOME (Short "bar"))``
val _ = tytest "('a) list list"
val _ = tytest "('a,'b) foo list"
val _ = tytest "'a list"
val _ = tytest "'a list list"
val _ = tytest "bool list list"
val _ = tytest "('a,bool list)++"
val _ = parsetest0 ``nREPLTop`` ``ptree_REPLTop``
          "case g of C p1 => e1 | p2 => e2;"
          (SOME ``Ast_Tdec
                     (Ast_Dlet
                        (Ast_Pvar "it")
                        (Ast_Mat (Ast_Var (Short "g"))
                                 [(Ast_Pcon (SOME (Short "C")) [Ast_Pvar "p1"],
                                   Ast_Var (Short "e1"));
                                  (Ast_Pvar "p2", Ast_Var (Short "e2"))]))``)

val _ = parsetest0 ``nREPLTop`` ``ptree_REPLTop``
                   "structure s :> sig type 'a t type ('b,'c) u val z : 'a t end = struct end;"
      (SOME ``Ast_Tmod "s"
          (SOME [Ast_Stype_opq ["'a"] "t";
                 Ast_Stype_opq ["'b"; "'c"] "u";
                 Ast_Sval "z" (Ast_Tapp [Ast_Tvar "'a"] (SOME (Short "t")))])
          []``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "4 handle IntError x => 3 + 4"
                   (SOME ``Ast_Handle (Ast_Lit (IntLit 4))
                                      [(Ast_Pcon (SOME (Short "IntError"))
                                                [Ast_Pvar "x"],
                                        Ast_App (Ast_App (Ast_Var (Short "+"))
                                                         (Ast_Lit (IntLit 3)))
                                                (Ast_Lit (IntLit 4)))]``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE``
                   "if raise IntError 4 then 2 else 3 handle IntError f => 23"
                   (SOME ``Ast_If (Ast_Raise
                                     (Ast_Con (SOME (Short "IntError"))
                                              [Ast_Lit (IntLit 4)]))
                                  (Ast_Lit (IntLit 2))
                                  (Ast_Handle
                                     (Ast_Lit (IntLit 3))
                                     [(Ast_Pcon (SOME(Short "IntError"))
                                                [Ast_Pvar"f"],
                                       Ast_Lit (IntLit 23))])``);
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "f x handle IntError n => case n of 0 => raise Div\n\
                  \                        | 1 => raise Bind\n\
                  \                        | _ => n - 2"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "C(3)"
                   (SOME ``Ast_Con (SOME (Short "C")) [Ast_Lit (IntLit 3)]``)

val _ = parsetest ``nREPLTop`` ``ptree_REPLTop``
                  "val x = z : S.ty -> bool;"
val _ = parsetest ``nREPLTop`` ``ptree_REPLTop``
                  "val S.C x = z;"
val _ = parsetest ``nREPLTop`` ``ptree_REPLTop`` "val x = str.y;"
val _ = parsetest ``nREPLTop`` ``ptree_REPLTop`` "x + 10;"
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
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "3"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "(3)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C D"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,D)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,D(1),true)"

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
val _ = parsetest ``nElist1`` ``ptree_Exprlist nElist1`` "x"
val _ = parsetest ``nElist1`` ``ptree_Exprlist nElist1`` "x,2"
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
