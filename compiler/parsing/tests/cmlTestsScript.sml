(*
  Some tests for the compiler's parser.
*)
open HolKernel Parse boolLib bossLib

open cmlPEGTheory gramTheory cmlPtreeConversionTheory
     grammarTheory lexer_funTheory lexer_implTheory

local open ASCIInumbersLib stringSyntax in end

val _ = new_theory "cmlTests"

Overload NN = ``λn. Nd (mkNT n,unknown_loc)``
Overload Tf = ``λt. Lf (TK t,unknown_loc)``
Overload Tfa = ``λs. Lf (TK (AlphaT s),unknown_loc)``
Overload Tfs = ``λs. Lf (TK (SymbolT s),unknown_loc)``
Overload EREL =
  ``λl. NN nE [NN nEhandle
                  [NN nElogicOR
                      [NN nElogicAND
                          [NN nEtyped [NN nEbefore [NN nEcomp l]]]]]]``
Overload EB = ``λl. EREL [NN nErel [NN nElistop [NN nEadd [NN nEmult [NN nEapp [NN nEbase l]]]]]]``

Overload OLDAPP = ``λt1 t2. App Opapp [t1; t2]``
(* Overload "" = ``λt1 t2. App Opapp [t1; t2]`` *)
Overload vbinop = ``λopn a1 a2. App Opapp [App Opapp [Var opn; a1]; a2]``
Overload V = ``λvnm. Var (Short vnm)``
Overload Pc = ``λcnm. Pcon (SOME (Short cnm))``

val _ = temp_add_user_printer
          ("locsprinter", ``Locs x y``,
           (fn gs => fn be => fn sysp => fn {add_string,...} =>
            fn gravs => fn depth => fn t => add_string "L"))

fun strip_Lannot t =
  if is_comb t then
        let val (tl, tr) = dest_comb t in
          if is_comb tl then
                let val (t1, t2) = dest_comb tl in
                  if t1 ~~ ``Lannot`` then strip_Lannot t2
                  else mk_comb(mk_comb(strip_Lannot t1, strip_Lannot t2), strip_Lannot tr)
                end
          else mk_comb(tl, strip_Lannot tr)
    end
  else t

val locs_ty = ``:locs``
fun aconv_mod_locs t1 t2 =
  case total (match_term t1) t2
  of SOME (s,[]) =>
       List.all (equal locs_ty o #2 o dest_var o #redex) s
  |  _ => false

val result_t = ``Result``
val success_t = “Success”
fun parsetest0 nt sem s opt = let
  val s_t = stringSyntax.lift_string bool s
  val _ = print ("**********\nLexing "^s^"\n")
  val t = time (rhs o concl o EVAL) ``lexer_fun ^s_t``
  val ttoks = rhs (concl (EVAL ``MAP (TK o FST)  ^t``))
  val _ = print ("Lexes to : " ^ term_to_string ttoks ^ "\n")
  val _ = print ("Parsing\n")
  val evalth = time EVAL
                   “peg_exec cmlPEG (nt (mkNT ^nt) I) ^t [] NONE [] done failed”
  val r = rhs (concl evalth)
  fun diag(s,t) = let
    fun pp (s,t) =
      PP.block PP.CONSISTENT 0 [
        PP.add_string s,
        PP.add_break (1,2),
        pp_term t
      ]
  in
    PP.prettyPrint (print, 79) (pp (s,t))
  end
  fun die (s,t) = (diag (s,t); raise Fail ("Failed "^s))

in
  if same_const (rator r) result_t then
    if same_const (rand r |> strip_comb |> #1) success_t then let
        val (_, args) = strip_comb (rand r)
        val remaining_input = hd args
        val resl = hd (tl args) (* should be singleton list *)
        val res = lhand resl (* extract h of CONS h NIL *)
    in
      if listSyntax.is_nil remaining_input then let
        val _ = diag ("EVAL to: ", res)
        val fringe_th = EVAL ``ptree_fringe ^res``
        val fringe_t = rhs (concl fringe_th)
        val _ = diag ("fringe = ", fringe_t)
      in
        if aconv fringe_t ttoks then let
          val ptree_res =
              case Lib.total mk_icomb(sem,res) of
                  NONE => optionSyntax.mk_none bool
                | SOME t =>
                  let
                    val rt = rhs (concl (time EVAL t))
                  in
                    if optionSyntax.is_some rt then
                      rand rt
                    else die ("Sem. failure", rt)
                  end
          val ptree_clean = strip_Lannot ptree_res
          val _ = diag ("Semantics ("^term_to_string sem^") to ", ptree_clean)
        in
          if not (optionSyntax.is_none ptree_res) then
            case opt of
                NONE => ()
              | SOME t => if aconv_mod_locs t (ptree_clean) then
                            print "Semantic output as expected\n"
                          else
                            die ("Semantics fails; is not the required ", t)
          else ()
        end
        else die ("Fringe not preserved!", ttoks)
      end
      else die ("REMAINING INPUT:", remaining_input)
    end
    else die ("FAILED:", r)
  else die ("NO RESULT:", r)
end

fun parsetest t1 t2 s = parsetest0 t1 t2 s NONE
fun tytest0 s r = parsetest0 ``nType`` ``ptree_Type nType`` s (SOME r)
val tytest = parsetest ``nType`` ``ptree_Type nType``

(* There is no longer something called 'elab_decs' in the codebase:
val elab_decls = ``OPTION_MAP (elab_decs NONE [] []) o ptree_Decls``
 *)

val _ = parsetest0 ``nE`` ``ptree_Expr nE``
         "let val _ = print \"foo\"\
            \ val z = 10\
            \ val (x,y) = g z\
            \ fun h x = x + 1\
         \ in x + y end"
 (SOME ``Let NONE (App Opapp [V "print"; Lit (StrLit "foo")])
           (Let (SOME "z") (Lit (IntLit 10))
              (Mat (App Opapp [V "g"; V "z"])
                   [(Pcon NONE [Pvar "x"; Pvar "y"],
                     Letrec [("h", "x",
                              vbinop (Short "+") (V "x") (Lit (IntLit 1)))]
                            (vbinop (Short "+") (V "x") (V "y")))]))``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE``
         "let val (x,y) = g z\
            \ val [h] = f a\
         \ in x + y * h end"
 (SOME ``Mat (App Opapp [V "g"; V "z"])
             [(Pcon NONE [Pvar "x"; Pvar "y"],
               Mat (App Opapp [V "f"; V "a"])
                   [(Pcon (SOME (Short "::"))
                          [Pvar "h"; Pcon (SOME (Short "[]")) []],
                     vbinop (Short "+") (V "x")
                            (vbinop (Short "*") (V "y") (V "h")))])]``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val w = 0wx3"
          (SOME ``Dlet locs (Pvar "w") (Lit (Word64 3w))``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "#(read) byte_array"
          (SOME ``App (FFI "read") [Var (Short "byte_array")]``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val w = 0wxf"
          (SOME ``Dlet locs (Pvar "w") (Lit (Word64 15w))``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val w = 0w3"
          (SOME ``Dlet locs (Pvar "w") (Lit (Word64 3w))``)

val _ = parsetest0 ``nPattern`` ``ptree_Pattern nPattern`` "(x:int) :: _"
          (SOME ``Pcon (SOME (Short "::")) [
                     Ptannot (Pvar "x") (Atapp [] (Short "int"));
                     Pany]``)

val _ = parsetest0 ``nPattern`` ``ptree_Pattern nPattern``
          "(_, x::y :int list, z)"
          (SOME ``Pcon NONE [
                     Pany;
                     Ptannot (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "y"])
                             (Atapp [Atapp [] (Short "int")]
                                    (Short "list"));
                     Pvar "z"]``)

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
          "a as (b as c)"
          (SOME “Pas (Pas (Pvar "c") "b") "a"”)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "x : int"
          (SOME ``Tannot (Var (Short "x")) (Atapp [] (Short "int"))``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "(x : int) + 3"
          (SOME ``vbinop (Short "+")
                         (Tannot (Var (Short "x"))
                                 (Atapp [] (Short "int")))
                         (Lit (IntLit 3))``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "op="
          (SOME ``Var (Short "=")``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl``
          "val x = 10"
          (SOME ``Dlet locs (Pvar "x") (Lit (IntLit 10))``)

val _ = parsetest0 ``nTopLevelDecs`` ``ptree_TopLevelDecs``
          "val x = 10"
          (SOME ``[Dlet locs (Pvar "x") (Lit (IntLit 10))]``)

val _ = parsetest0 ``nTopLevelDecs`` ``ptree_TopLevelDecs``
          "val x = 10 val y = 20; print (x + y); val z = 30"
          (SOME ``[Dlet locs1 (Pvar "x") (Lit (IntLit 10));
                   Dlet locs2 (Pvar "y") (Lit (IntLit 20));
                   Dlet locs3 (Pvar "it")
                           (App Opapp
                                [Var (Short "print");
                                 vbinop (Short "+")
                                        (Var (Short "x"))
                                        (Var (Short "y"))]);
                   Dlet locs4 (Pvar "z") (Lit (IntLit 30))]``)

val _ = parsetest0 ``nTopLevelDecs`` ``ptree_TopLevelDecs``
          "; ; val x = 10"
          (SOME ``[Dlet locs (Pvar "x") (Lit (IntLit 10))]``)

val _ = parsetest0 ``nTopLevelDecs`` ``ptree_TopLevelDecs``
          "; ; val x = 10;"
          (SOME ``[Dlet locs (Pvar "x") (Lit (IntLit 10))]``)

val _ = parsetest0 ``nTopLevelDecs`` ``ptree_TopLevelDecs`` "; ; "
                   (SOME ``[] : dec list``)
val _ = parsetest0 ``nTopLevelDecs`` ``ptree_TopLevelDecs`` ""
                   (SOME ``[] : dec list``)


val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "fn x => x"
                   (SOME ``Fun "x" (Var (Short "x"))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "fn (x,y) => x + y"
                   (SOME ``Fun "" (Mat (Var (Short ""))
                                       [(Pcon NONE [Pvar "x"; Pvar "y"],
                                         vbinop (Short "+")
                                                (Var (Short "x"))
                                                (Var (Short "y")))])``)
val _ = parsetest0 “nDecl” “ptree_Decl”
                   "local val x = 3; val z = 10; in val y = x; end"
                   (SOME “Dlocal [Dlet _ (Pvar "x") (Lit(IntLit 3));
                                  Dlet _ (Pvar "z") (Lit(IntLit 10));
                                 ]
                         [Dlet _ (Pvar "y") (Var (Short "x"))]”);

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "fun f 0 NONE = 3"
                   (SOME ``Dletrec locs
                            [("f","",
                              Mat (Var (Short ""))
                                  [(Plit (IntLit 0),
                                    Fun ""
                                        (Mat (Var (Short ""))
                                             [(Pcon (SOME (Short "NONE")) [],
                                               Lit (IntLit 3))]))])]``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "fun f (x,y) (SOME z) = x * y + z"
                   (SOME
                      ``Dletrec locs
                         [("f","",
                           Mat (Var (Short ""))
                               [(Pcon NONE [Pvar "x"; Pvar "y"],
                                 Fun ""
                                     (Mat (Var (Short ""))
                                          [(Pcon (SOME (Short "SOME"))
                                                 [Pvar "z"],
                                            vbinop (Short "+")
                                                   (vbinop (Short "*")
                                                           (Var (Short "x"))
                                                           (Var (Short "y")))
                                                   (Var (Short "z")))]))])]``)


val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "op*" (SOME ``Var (Short "*")``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "f op* 10"
                   (SOME ``OLDAPP (OLDAPP (Var (Short "f")) (Var (Short "*")))
                                  (Lit (IntLit 10))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "f op+ 10"
                   (SOME ``OLDAPP (OLDAPP (Var (Short "f")) (Var (Short "+")))
                                  (Lit (IntLit 10))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "op*(2,3)"
                   (SOME ``OLDAPP (Var (Short "*"))
                              (Con NONE [Lit (IntLit 2); Lit (IntLit 3)])``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "op tHEN(t1,t2)"
                   (SOME ``OLDAPP (Var (Short "tHEN"))
                              (Con NONE [Var (Short "t1"); Var (Short "t2")])``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "2 * 3"
                   (SOME ``vbinop (Short "*")
                              (Lit (IntLit 2))
                              (Lit (IntLit 3))``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "()"
                   (SOME ``Con NONE []``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "SOME ()"
                   (SOME ``Con (SOME (Short "SOME")) [Con NONE []]``)

val _ = parsetest0 ``nSpecLine`` ``ptree_SpecLine`` "type 'a foo = 'a list"
                   (SOME ``() (* Stabbrev ["'a"] "foo"
                             (Atapp [Atvar "'a"] (Short "list")) *)``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "type 'a foo = 'a list"
                   (SOME ``Dtabbrev locs ["'a"] "foo"
                             (Atapp [Atvar "'a"] (Short "list"))``)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val h::List.Nil = [3]"
          (SOME ``Dlet locs
                    (Pcon (SOME (Short "::"))
                              [Pvar "h";
                               Pcon (SOME (Long "List" (Short "Nil"))) []])
                    (Con (SOME (Short "::"))
                             [Lit (IntLit 3);
                              Con (SOME (Short "[]")) []])``)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val [] = f x"
          (SOME ``Dlet locs (Pcon (SOME (Short "[]")) [])
                           (OLDAPP (Var (Short "f"))
                                    (Var (Short "x")))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE``
                   "case x of [] => 3 | [] :: _ => 1 | (h::t) :: rest => 2"
          (SOME ``Mat (Var (Short "x"))
                    [(Pcon (SOME (Short "[]")) [],Lit (IntLit 3));
                     (Pcon (SOME (Short "::"))
                               [Pcon (SOME (Short "[]")) []; Pany],
                      Lit (IntLit 1));
                     (Pcon (SOME (Short "::"))
                               [Pcon (SOME (Short "::"))
                                         [Pvar "h"; Pvar "t"];
                                Pvar "rest"],
                      Lit (IntLit 2))]``)


val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "case x of [] => 3 | [e, _] => e"
           (SOME ``Mat (Var (Short "x"))
                     [(Pcon (SOME (Short "[]")) [],Lit (IntLit 3));
                      (Pcon (SOME (Short "::"))
                                [Pvar "e";
                                 Pcon (SOME (Short "::"))
                                          [Pany;
                                           Pcon (SOME (Short "[]")) []]],
                       Var (Short "e"))]``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "[3,4]"
                   (SOME ``Con (SOME (Short "::"))
                             [Lit (IntLit 3);
                              Con (SOME (Short "::"))
                                      [Lit (IntLit 4);
                                       Con (SOME (Short "[]")) []]]``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "[]"
                   (SOME ``Con (SOME (Short "[]")) []``);
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "3::t = l"
                   (SOME ``OLDAPP
                            (OLDAPP (Var (Short "="))
                                     (Con (SOME (Short "::"))
                                              [Lit (IntLit 3);
                                               Var (Short "t")]))
                            (Var (Short "l"))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "3 < x = True"
                   (SOME ``vbinop (Short "=")
                                  (vbinop (Short "<")
                                          (Lit (IntLit 3))
                                          (Var (Short "x")))
                                  (Con (SOME (Short "True")) [])``)

val _ = tytest0 "'a * bool"
                ``Attup [Atvar "'a"; Atapp [] (Short "bool")]``

val _ = tytest0 "'a * bool * 'c"
                ``Attup [Atvar "'a";
                         Atapp [] (Short "bool");
                         Atvar "'c"]``

val _ = tytest "'a * bool -> 'a"
val _ = tytest "'a * (bool * 'c)"
val _ = tytest "(bool * int)"
val _ = tytest "(bool list * int) * bool"
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "exception Foo"
                   (SOME ``Dexn locs "Foo" []``)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "exception Bar int"
                   (SOME ``Dexn locs "Bar" [Atapp [] (Short "int")]``)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "exception Bar int int"
                   (SOME ``Dexn locs "Bar"
                             [Atapp [] (Short "int");
                              Atapp [] (Short "int")]``);
val _ = parsetest ``nPType`` ``ptree_PType`` "'a"
val _ = parsetest ``nPType`` ``ptree_PType`` "'a * bool"
val _ = parsetest ``nPatternList`` ``ptree_Plist`` "x,y"
val _ = parsetest ``nPtuple`` ``ptree_Pattern nPtuple`` "(x,y)"

val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,y)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "(x,3)"
val _ = parsetest “nPas” “ptree_Pattern nPas” "t as C(x,y)"
val _ = parsetest “nPattern” “ptree_Pattern nPattern”
                  "x3 as [C _ (x as [y,z]), D]"

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "(x,y,4)"
                   (SOME ``Con NONE [Var (Short "x");
                                         Var (Short "y");
                                         Lit (IntLit 4)]``);
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "C(x,3)"
                   (SOME ``Con (SOME (Short "C"))
                               [Con NONE [Var (Short "x"); Lit (IntLit 3)]]``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "f(x,3)"
                   (SOME ``OLDAPP (Var (Short "f"))
                                   (Con NONE
                                            [Var (Short "x");
                                             Lit (IntLit 3)])``)

val _ = tytest "'a"
val _ = tytest "'a -> bool"
val _ = tytest "'a -> bool -> foo"
val _ = tytest "('a)"
val _ = tytest0 "('a)list" ``Atapp [Atvar "'a"] (Short "list")``
val _ = tytest "('a->bool)list"
val _ = tytest "'a->bool list"
val _ = tytest "('a->bool)->bool"
val _ = tytest0 "('a,foo)bar"
                ``Atapp [Atvar "'a"; Atapp [] (Short "foo")] (Short "bar")``
val _ = tytest "('a) list list"
val _ = tytest "('a,'b) foo list"
val _ = tytest "'a list"
val _ = tytest "'a list list"
val _ = tytest "bool list list"
val _ = tytest "('a,bool list)++"
(*val _ = parsetest0 ``nREPLTop`` ``ptree_REPLTop``
          "case g of C p1 => e1 | p2 => e2;"
          (SOME ``Tdec
                     (Dlet
                        (Pvar "it")
                        (Mat (Var (Short "g"))
                                 [(Pcon (SOME (Short "C")) [Pvar "p1"],
                                   Var (Short "e1"));
                                  (Pvar "p2", Var (Short "e2"))]))``)

val _ = parsetest0 ``nREPLTop`` ``ptree_REPLTop``
                   "structure s :> sig type 'a t type ('b,'c) u val z : 'a t end = struct end;"
      (SOME ``Tmod "s"
          (SOME [Stype_opq ["'a"] "t";
                 Stype_opq ["'b"; "'c"] "u";
                 Sval "z" (Atapp [Atvar "'a"] (SOME (Short "t")))])
          []``)
*)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "4 handle IntError x => 3 + 4"
                   (SOME ``Handle (Lit (IntLit 4))
                                      [(Pcon (SOME (Short "IntError"))
                                                [Pvar "x"],
                                        vbinop (Short "+")
                                               (Lit (IntLit 3))
                                               (Lit (IntLit 4)))]``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE``
                   "if raise IntError 4 then 2 else 3 handle IntError f => 23"
                   (SOME ``If (Raise
                                     (Con (SOME (Short "IntError"))
                                              [Lit (IntLit 4)]))
                                  (Lit (IntLit 2))
                                  (Handle
                                     (Lit (IntLit 3))
                                     [(Pcon (SOME(Short "IntError"))
                                                [Pvar"f"],
                                       Lit (IntLit 23))])``);
val _ = parsetest ``nE`` ``ptree_Expr nE``
                  "f x handle IntError n => case n of 0 => raise Div\n\
                  \                        | 1 => raise Bind\n\
                  \                        | _ => n - 2"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "C(3)"
                   (SOME ``Con (SOME (Short "C")) [Lit (IntLit 3)]``)

val _ = parsetest ``nTopLevelDecs`` ``ptree_TopLevelDecs``
                  "val x = z : S.ty -> bool;"
val _ = parsetest ``nTopLevelDecs`` ``ptree_TopLevelDecs``
                  "val S.C x = z;"
val _ = parsetest ``nTopLevelDecs`` ``ptree_TopLevelDecs`` "val x = str.y;"
val _ = parsetest ``nTopLevelDecs`` ``ptree_TopLevelDecs`` "x + 10;"
val _ = parsetest ``nDecl`` ``ptree_Decl``
                  "structure s = struct val x = 3 end"
val _ = parsetest ``nDecl`` ``ptree_Decl``
                  "structure s :> sig val x : int end = struct val x = 3 end"
val _ = parsetest ``nDecl`` ``ptree_Decl``
                  "structure s :> sig val x : int; end = struct val x = 3 end"
val _ = parsetest ``nDecl`` ``ptree_Decl`` "val x = 10"
val _ = parsetest0 ``nDecl`` ``ptree_Decl``
                  "local structure s = struct val x = 10 end in\n\
                  \structure t = struct val y = s.x + 1 end end"
                  (SOME “Dlocal [Dmod "s"
                                 [Dlet _ (Pvar "x") (Lit (IntLit 10))]]
                         [Dmod "t" [Dlet _ (Pvar "y") $
                                   vbinop (Short "+")
                                     (Var (Long "s" (Short "x")))
                                     (Lit (IntLit 1))]]”)
val _ = parsetest0 ``nDecl`` ``ptree_Decl``
            "structure s = struct structure t = struct type ty = int end end"
                  (SOME “Dmod "s" [
                           Dmod "t" [
                               Dtabbrev _ [] "ty" (Atapp [] (Short "int"))
                           ]
                         ]”)

(* elab_decls doesn't exist:

val _ = parsetest ``nDecls`` elab_decls "fun f x y = x + y"
val _ = parsetest ``nDecls`` elab_decls
                  "datatype 'a list = Nil | Cons 'a ('a list) \
                  \fun map f l = case l of Nil => Nil \
                  \                      | Cons h t => Cons(f h, map f t)"
*)

val _ = parsetest0 “nDecl” “ptree_Decl”
          "datatype 'a Tree = Lf1 | Nd ('a Tree) 'a ('a Tree) | Lf2 int"
          (SOME “Dtype _ [(["'a"], "Tree",
                           [("Lf1", []);
                            ("Nd", [Atapp [Atvar "'a"] (Short "Tree");
                                    Atvar "'a";
                                    Atapp [Atvar "'a"] (Short "Tree")]);
                            ("Lf2", [Atapp [] (Short "int")])])]”)
val _ = parsetest0 “nDecl” “ptree_Decl”
          "datatype 'a Tree = Lf1 | Nd ('a Tree) 'a ('a Tree) | Lf2 int"
          (SOME “Dtype _ [(["'a"], "Tree",
                           [("Lf1", []);
                            ("Nd", [Atapp [Atvar "'a"] (Short "Tree");
                                    Atvar "'a";
                                    Atapp [Atvar "'a"] (Short "Tree")]);
                            ("Lf2", [Atapp [] (Short "int")])])]”)
(*
val _ = parsetest ``nDecls`` elab_decls "val x = f()"
val _ = parsetest ``nDecls`` elab_decls "val () = f x"
*)
val _ = parsetest0 ``nDecls`` “ptree_Decls” "val x = Ref False;"
                   (SOME “[Dlet someloc (Pvar "x")
                                (App Opref [Con (SOME (Short "False")) []])]”)
val _ = parsetest0 ``nDecls`` “ptree_Decls” "val Ref y = f z"
                   (SOME “[Dlet someloc (Pref (Pvar "y"))
                                (App Opapp [V "f"; V "z"])]”)
val _ = parsetest0 “nDecl” “ptree_Decl” "val x = (y : int ref)"
                   (SOME “Dlet someloc (Pvar "x")
                           (Tannot (V "y")
                             (Atapp [Atapp [] (Short "int")]
                                    (Short "ref")))”)
val _ = parsetest0 “nE” “ptree_Expr nE” "op Ref"
                   (SOME “Con (SOME (Short "Ref")) []”);
val _ = parsetest0 “nE” “ptree_Expr nE” "Ref"
                   (SOME “Con (SOME (Short "Ref")) []”);
(*
val _ = parsetest ``nDecls`` elab_decls "val x = (y := 3);"
val _ = parsetest ``nDecls`` elab_decls "val _ = (y := 3);"
*)
val _ = parsetest ``nE`` ``ptree_Expr nE`` "(f x; 3)"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "!x"
                   (SOME “App Opapp [V "!"; V "x"]”)
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
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val C x = 3"
                   (SOME “Dlet someloc (Pcon (SOME (Short "C")) [Pvar "x"])
                               (Lit (IntLit 3))”)
val _ = parsetest ``nDecls`` ``ptree_Decls`` "val x = 3; val C y = f z"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "val C(x,y) = foo"
val _ = parsetest ``nDecl`` ``ptree_Decl`` "fun f x = x"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "datatype foo = C | D"
val _ = parsetest ``nDecls`` ``ptree_Decls`` "datatype foo = C | D val x = y"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "3"
val _ = parsetest0 ``nPattern`` ``ptree_Pattern nPattern`` "C"
          (SOME “Pc "C" []”)
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "x"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "(3)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C x"
val _ = parsetest0 ``nPattern`` ``ptree_Pattern nPattern`` "C D"
          (SOME “Pc "C" [Pc "D" []]”)
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,D)"
val _ = parsetest ``nPattern`` ``ptree_Pattern nPattern`` "C(x,D(1),True)"

val _ = parsetest ``nTypeName`` ``ptree_TypeName`` "bool"
val _ = parsetest ``nTypeName`` ``ptree_TypeName``
                  "'a list"
val _ = parsetest ``nTypeName`` ``ptree_TypeName``
                  "('a,'b) foo"
val _ = parsetest ``nConstructorName`` T "Cname"
val _ = parsetest ``nDconstructor`` ``ptree_Dconstructor`` "Cname"
val _ = parsetest ``nDconstructor`` ``ptree_Dconstructor``
                  "Cname bool 'a"
val _ = parsetest ``nDtypeDecl`` ``ptree_DtypeDecl``
                  "'a foo = C 'a | D bool | E"
val _ = parsetest ``nTypeDec`` ``ptree_TypeDec``
                  "datatype 'a foo = C 'a | D bool | E and bar = F | G"

(* expressions *)
val _ = parsetest ``nEbase`` ``ptree_Expr nEbase`` "x"
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f x y"
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f True y"
val _ = parsetest ``nEapp`` ``ptree_Expr nEapp`` "f True Constructor"
val _ = parsetest ``nElist1`` ``ptree_Exprlist nElist1`` "x"
val _ = parsetest ``nElist1`` ``ptree_Exprlist nElist1`` "x,2"
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "C (x)"
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "C(x, y)"
val _ = parsetest ``nEmult`` ``ptree_Expr nEmult`` "f x * 3"
val _ = parsetest ``nErel`` ``ptree_Expr nErel`` "x <> True"
val _ = parsetest ``nEcomp`` ``ptree_Expr nEcomp`` "x <> True"
val _ = parsetest ``nEcomp`` ``ptree_Expr nEcomp`` "f o g z"
val _ = parsetest ``nEtyped`` ``ptree_Expr nEtyped`` "map f Nil : 'a list"
val _ = parsetest ``nElogicOR`` ``ptree_Expr nElogicOR``
                  "3 < x andalso x < 10 orelse p andalso q"
val _ = parsetest ``nE`` ``ptree_Expr nE`` "if x < 10 then f x else C(x,3,g x)"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "1 + 2 + 3"
                   (SOME ``vbinop (Short "+")
                                  (vbinop (Short "+")
                                          (Lit (IntLit 1))
                                          (Lit (IntLit 2)))
                                  (Lit (IntLit 3))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "1 ++ 2 */ 3"
                   (SOME ``vbinop (Short "++")
                                  (Lit (IntLit 1))
                                  (vbinop (Short "*/")
                                          (Lit (IntLit 2))
                                          (Lit (IntLit 3)))``)
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "s1 ^ s2"
                   (SOME ``vbinop (Short "\094") (V "s1") (V "s2")``)
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
val _ = parsetest ``nE`` ``ptree_Expr nE`` "#\"a\" + 1"
val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "case c of #\"a\" => 1 | _ => 2"
                   (SOME ``Mat (Var (Short "c"))
                               [(Plit (Char #"a"), Lit (IntLit 1));
                                (Pany, Lit (IntLit 2))]``)

(* val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "let val op+ = 3 in f op+ end"
                   NONE *)
val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val op+ = (fn x => fn y => x * y)"
                   (SOME “Dlet locs (Pvar "+")
                     (Fun "x" (Fun "y" (vbinop (Short "*") (V "x") (V "y"))))”)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val C(x,y) = f a"
    (SOME “Dlet locs
                (Pcon (SOME (Short "C")) [Pcon NONE [Pvar "x"; Pvar "y"]])
                (App Opapp [V "f"; V "a"])”)

val _ = parsetest0 ``nDecl`` ``ptree_Decl`` "val C x y = f a"
    (SOME “Dlet locs
                (Pcon (SOME (Short "C")) [Pvar "x"; Pvar "y"])
                (App Opapp [V "f"; V "a"])”)

val _ = export_theory()
