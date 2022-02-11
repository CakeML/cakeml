(*
  Some tests for the OCaml parser.

  The setup is copied from ../tests/cmlTestsScript.sml.
*)

open preamble camlPEGTheory camlPtreeConversionTheory caml_lexTheory;
local open ASCIInumbersLib stringSyntax in end

val _ = new_theory "camlTests"

val _ = set_grammar_ancestry [
  "misc", "pegexec", "caml_lex", "camlPEG", "camlPtreeConversion", "ast"
  ]

val _ = bring_to_front_overload "nType" {Name="nType", Thy="camlPEG"};
val _ = bring_to_front_overload "nPattern" {Name="nPattern", Thy="camlPEG"};

Type NT = “:camlNT inf”;
Overload mkNT = “INL : camlNT -> NT”;
Overload TK = “TOK : token -> (token,camlNT) grammar$symbol”;
Overload NN = “Nd (mkNT n, unknown_loc)”;
Overload Tf = “λt. Lf (TOK t, unknown_loc)”;

Overload vbinop = “λopn a1 a2. App Opapp [App Opapp [Var opn; a1]; a2]”;
Overload V = “λvnm. Var (Short vnm)”;
Overload Pv = “λvnm. Pvar vnm”;
Overload Pc = “λcnm. Pcon (SOME (Short cnm))”;
Overload C = “λcnm. Con (SOME (Short cnm))”

(*
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
 *)

val _ = temp_add_user_printer
  ("locsprinter", “Locs x y”,
   (fn gs => fn be => fn sysp => fn {add_string,...} =>
    fn gravs => fn depth => fn t => add_string "L"));

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
  else t;

val locs_ty = “:locs”;
fun aconv_mod_locs t1 t2 =
  case total (match_term t1) t2
  of SOME (s,[]) =>
       List.all (equal locs_ty o #2 o dest_var o #redex) s
  |  _ => false;

val result_t = “Result”;
val success_t = “Success”;
fun parsetest0 nt sem s opt = let
  val s_t = stringSyntax.lift_string bool s
  val _ = print ("**********\nLexing "^s^"\n")
  val t = time (rhs o concl o EVAL) “lexer_fun ^s_t”
  val ttoks = rhs (concl (EVAL “MAP (TK o FST)  ^t”))
  val _ = print ("Lexes to : " ^ term_to_string ttoks ^ "\n")
  val _ = print ("Parsing\n")
  val evalth =
    time EVAL “peg_exec camlPEG (nt (mkNT ^nt) I) ^t [] NONE [] done failed”
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
        val fringe_th = EVAL “ptree_fringe ^res”
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
                    if sumSyntax.is_inr rt then
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
end;

fun parsetest t1 t2 s = parsetest0 t1 t2 s NONE;

(* -------------------------------------------------------------------------
 * CakeML escape hatch
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "raise (Fail \"5\")"
  (SOME “Raise (C "Fail" [Lit (StrLit "5")])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "raise (f x)"
  (SOME “Raise (App Opapp [V "f"; V "x"])”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "let x = 2 ;; (*CML val x = 5; print \"z\"; fun ref x = Ref x; *)"
  (SOME “[Dlet L1 (Pv "x") (Lit (IntLit 2));
          Dlet L2 (Pv "x") (Lit (IntLit 5));
          Dlet L3 (Pv "it") (App Opapp [V "print"; Lit (StrLit "z")]);
          Dletrec L4 [("ref","x", App Opref [V "x"])]]”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "(*CML val x = x; (*CML comments and pragmas are skipped *) val y = y;*)"
  (SOME “[Dlet L1 (Pv "x") (V "x");
          Dlet L2 (Pv "y") (V "y")]”)
  ;

(* This fails, as expected:
val _ = parsetest0 “nStart” “ptree_Start”
  "let x = (*CML val x = x; *) 6;;"
  NONE
  ;
 *)

(* -------------------------------------------------------------------------
 * Types
 * ------------------------------------------------------------------------- *)

fun tytest0 s r = parsetest0 “nType” “ptree_Type” s (SOME r);
val tytest = parsetest “nType” “ptree_Type”;

val _ = tytest0 "'a"
  “Atvar "a"”
  ;

val _ = tytest0 "'a * 'b"
  “Attup [Atvar "a"; Atvar "b"]”
  ;

val _ = tytest0 "'a * 'b * 'c"
  “Attup [Atvar "a"; Atvar "b"; Atvar "c"]”
  ;

val _ = tytest0 "'a * 'b -> 'c"
  “Atfun (Attup [Atvar "a"; Atvar "b"]) (Atvar "c")”
  ;

val _ = tytest0 "('a, 'b) blorb"
  “Atapp [Atvar "a"; Atvar "b"] (Short "blorb")”
  ;

val _ = tytest0 "Foo.blorb"
  “Atapp [] (Long "Foo" (Short "blorb"))”
  ;

val _ = tytest0 "'a * bool"
  “Attup [Atvar "a"; Atapp [] (Short "bool")]”
  ;

val _ = tytest0 "'a * bool * 'c"
  “Attup [Atvar "a"; Atapp [] (Short "bool"); Atvar "c"]”
  ;

val _ = tytest0 "'a * bool -> 'a"
  “Atfun (Attup [Atvar "a"; Atapp [] (Short "bool")]) (Atvar "a")”
  ;

val _ = tytest0 "'a * (bool * 'c)"
  “Attup [Atvar "a"; Attup [Atapp [] (Short "bool"); Atvar "c"]]”
  ;

val _ = tytest0 "('a * bool) * 'c"
  “Attup [Attup [Atvar "a"; Atapp [] (Short "bool")]; Atvar "c"]”
  ;

val _ = tytest0 "('a * 'b)"
  “Attup [Atvar "a"; Atvar "b"]”
  ;

val _ = tytest0 "('a,'b) d"
 “Atapp [Atvar "a"; Atvar "b"] (Short "d")”
 ;

(* -------------------------------------------------------------------------
 * Patterns
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "Cc a as i, Dd b as j"
  (SOME “[Pcon NONE [Pas (Pc "Cc" [Pv "a"]) "i";
                     Pas (Pc "Dd" [Pv "b"]) "j"]]”)
  ;


val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "a, b | c, d"
  (SOME “[Pcon NONE [Pv "a"; Pv "b"];
          Pcon NONE [Pv "c"; Pv "d"]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "Comb (a,b) as c, d"
  (SOME “[Pcon NONE [Pas (Pc "Comb" [Pv "a"; Pv "b"]) "c"; Pv "d"]]”)

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "false::[]"
  (SOME “[Pc "::" [Pc "False" []; Pc "[]" []]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "x as y"
  (SOME “[Pas (Pvar "x") "y"]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "x | y"
  (SOME “[Pvar "x"; Pvar "y"]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "Some x | y"
  (SOME “[Pc "Some" [Pvar "x"]; Pvar "y"]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "y,z,x"
  (SOME “[Pcon NONE [Pvar "y"; Pvar "z"; Pvar "x"]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "(x: int)"
  (SOME “[Ptannot (Pvar "x") (Atapp [] (Short "int"))]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "Aa (Bb (Cc x))"
  (SOME “[Pc "Aa" [Pc "Bb" [Pc "Cc" [Pvar "x"]]]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "a :: 1"
  (SOME “[Pc "::" [Pvar "a"; Plit (IntLit 1)]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern nPattern”
  "[a,b ; c]"
  (SOME “[Pc "::" [Pcon NONE [Pvar "a"; Pvar "b"];
                   Pc "::" [Pvar "c"; Pc "[]" []]]]”)
  ;

(* -------------------------------------------------------------------------
 * Expressions
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "true || let y = z in y"
  (SOME “Log Or (C "True" []) (Let (SOME "y") (V "z") (V "y"))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let y = z in y || true"
  (SOME “Let (SOME "y") (V "z") (Log Or (V "y") (C "True" []))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "0 + match x with y -> z"
  (SOME (“vbinop (Short "+") (Lit (IntLit 0)) (Mat (V "x") [(Pv "y", V "z")])”))
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "- fun x -> x"
  (SOME “App Opapp [Var (Long "Int" (Short "~")); Fun "x" (V "x")]”)
  ;

val _ = parsetest0 “nENeg” “ptree_Expr nENeg”
  " - let y = z in y"
  (SOME “App Opapp [Var (Long "Int" (Short "~"));
                    Let (SOME "y") (V "z") (V "y")]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "a, [], fun x -> ()"
  (SOME “Con NONE [V "a"; C "[]" []; Fun "x" (Con NONE [])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "a, match x with y -> z, w"
  (SOME “Con NONE [V "a"; Mat (V "x") [(Pv "y", Con NONE [V "z"; V "w"])]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match x with y -> z, w"
  (SOME “Mat (V "x") [(Pv "y", Con NONE [V "z"; V "w"])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match !myref () with a -> b"
  (SOME “Mat (App Opapp [App Opapp [V "!"; V "myref"]; Con NONE []])
             ([(Pv "a", V "b")])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "f !myref"
  (SOME “App Opapp [V "f"; App Opapp [V "!"; V "myref"]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "x && y"
  (SOME “Log And (V "x") (V "y")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "x || y"
  (SOME “Log Or (V "x") (V "y")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if x || y then x && y"
  (SOME “If (Log Or (V "x") (V "y"))
            (Log And (V "x") (V "y"))
            (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(n-1)"
  (SOME “vbinop (Short "-") (V "n") (Lit (IntLit 1))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(n -1)"
  (SOME “vbinop (Short "-") (V "n") (Lit (IntLit 1))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "-1"
  (SOME “App Opapp [Var (Long "Int" (Short "~")); Lit (IntLit 1)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(+) ; 2"
  (SOME “Let NONE (V "+") (Lit (IntLit 2))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "function x -> y ; function a -> b"
  (SOME “Fun "" (Mat (V "")
                     [(Pv "x", Let NONE (V "y")
                              (Fun "" (Mat (V "")
                                      [(Pv "a", V "b")])))])”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " let print_stdout printer data =\
  \   let st = empty () in\
  \   printer st data;\
  \   let tok = to_token st in\
  \   let apps = Pretty_core.print (!margin) tok in\
  \   App_list.iter (output_string stdout) apps"
  (SOME “[Dlet L (Pv "print_stdout") (Fun "printer" (Fun "data"
            (Let (SOME "st") (App Opapp [V "empty"; Con NONE []])
              (Let NONE (App Opapp [App Opapp [V "printer"; V "st"]; V "data"])
                (Let (SOME "tok") (App Opapp [V "to_token"; V "st"])
                  (Let (SOME "apps")
                    (App Opapp [App Opapp [Var (Long "Pretty_core"
                                                 (Short "print"));
                                           App Opapp [V "!"; V "margin"]];
                                V "tok"])
                    (App Opapp [App Opapp [Var (Long "App_list" (Short "iter"));
                                           App Opapp [V "output_string";
                                                      V "stdout"]];
                                V "apps"])))))))]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if x;y then  z"
  (SOME “If (Let NONE (V "x") (V "y")) (V "z") (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if y then z; w"
  (SOME “Let NONE (If (V "y") (V "z") (Con NONE [])) (V "w")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x -> y ; z"
  (SOME “Fun "x" (Let NONE (V "y") (V "z"))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(fun x -> y) ; z"
  (SOME “Let NONE (Fun "x" (V "y")) (V "z")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "[let x = a in x; let y = b in y]"
  (SOME “
    C "::" [Let (SOME "x") (V "a")
                (Let NONE (V "x")
                          (Let (SOME "y") (V "b") (V "y")));
            C "[]" []]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match x with \
  \ | a -> f; c \
  \ | b -> q; w"
  (SOME “
    Mat (V "x")
        [(Pv "a", Let NONE (V "f") (V "c"));
         (Pv "b", Let NONE (V "q") (V "w"))]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if b then let x = z in a; b"
  (SOME “
    If (V "b")
       (Let (SOME "x") (V "z")
            (Let NONE (V "a") (V "b")))
       (Con NONE [])”)
  ;


val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "foo; if b then print (); bar"
  (SOME “
    Let NONE (V "foo")
        (Let NONE (If (V "b") (App Opapp [V "print"; Con NONE []])
                      (Con NONE []))
                  (V "bar"))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "foo; let x = z in y ; bar"
  (SOME “
    Let NONE (V "foo")
        (Let (SOME "x") (V "z")
             (Let NONE (V "y") (V "bar")))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let (:=) x = z in w"
  (SOME “Let (SOME ":=") (Fun "x" (V "z")) (V "w")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(:=)"
  (SOME “(V ":=")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let _ = Ref x in z"
  (SOME “Let NONE (App Opref [V "x"]) (V "z")”)
  ;

val _ = parsetest0 “nValuePath” “ptree_ValuePath”
  "Aa.B_b.c"
  (SOME “["Aa"; "B_b"; "c"]”)
  ;

val _ = parsetest0 “nValuePath” “ptree_ValuePath”
  "B_b.cDEF"
  (SOME “["B_b"; "cDEF"]”)
  ;

val _ = parsetest0 “nValuePath” “ptree_ValuePath”
  "cDEF"
  (SOME “["cDEF"]”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Cd"
  (SOME “["Cd"]”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Ab.Cd"
  (SOME “["Ab"; "Cd"]”)
  ;

val _ = parsetest0 “nModulePath” “ptree_ModulePath”
  "Mm.Nn"
  (SOME “["Mm"; "Nn"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let [x; y] = z in w"
  (SOME “Mat (V "z")
           [(Pc "::" [Pvar "x";
               Pc "::" [Pvar "y";
                 Pc "[]" []]], V "w")]”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let a x = y and b x = z in w"
  (SOME “Let (SOME "a") (Fun "x" (Var (Short "y")))
             (Let (SOME "b") (Fun "x" (Var (Short "z")))
                  (Var (Short "w")))”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let f x y = x in z"
  (SOME “Let (SOME "f") (Fun "x" (Fun "y" (V "x"))) (V "z")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let f (x,y) = x in z"
  (SOME “Let (SOME "f")
             (Fun "" (Mat (V "") [(Pcon NONE [Pvar "x"; Pvar "y"], V "x")]))
             (V "z")”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let f x = x in y"
  (SOME “Let (SOME "f") (Fun "x" (V "x")) (V "y")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let rec f x = x in y"
  (SOME “Letrec [("f", "x", V "x")] (V "y")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let rec f x y = x in z"
  (SOME “Letrec [("f", "x", Fun "y" (V "x"))] (V "z")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let _ = print \"foo\" in\
  \  let z = 10 in\
  \  let (x,y) = g z in\
  \  let rec h x = x + 1 in\
  \  x + y"
  (SOME “Let NONE (App Opapp [V "print"; Lit (StrLit "foo")])
           (Let (SOME "z") (Lit (IntLit 10))
             (Mat (App Opapp [V "g"; V "z"])
                [(Pcon NONE [Pvar "x"; Pvar "y"],
                  Letrec [("h", "x",
                           vbinop (Short "+") (V "x") (Lit (IntLit 1)))]
                         (vbinop (Short "+") (V "x") (V "y")))]))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let (x,y) = g z in\
  \  let [h] = f a in\
  \  x + y * h"
 (SOME “Mat (App Opapp [V "g"; V "z"])
            [(Pcon NONE [Pvar "x"; Pvar "y"],
              Mat (App Opapp [V "f"; V "a"])
                  [(Pc "::" [Pvar "h"; Pc "[]" []],
                    vbinop (Short "+") (V "x")
                           (vbinop (Short "*") (V "y") (V "h")))])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x -> x"
  (SOME “Fun "x" (V "x")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun (x, y) -> x + y"
  (SOME “Fun "" (Mat (V "")
                     [(Pcon NONE [Pvar "x"; Pvar "y"],
                       vbinop (Short "+") (V "x") (V "y"))])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x y z -> y"
  (SOME “Fun "x" (Fun "y" (Fun "z" (V "y")))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun z (x, y) w -> x + y"
  (SOME “Fun "z" (Fun "" (Mat (V "")
                     [(Pcon NONE [Pvar "x"; Pvar "y"],
                       Fun "w" (vbinop (Short "+") (V "x") (V "y")))]))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(x : int)"
  (SOME “Tannot (V "x") (Atapp [] (Short "int"))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(x : int) + 3"
  (SOME “vbinop (Short "+") (Tannot (V "x") (Atapp [] (Short "int")))
                            (Lit (IntLit 3))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(=)"
  (SOME “V "="”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(THEN)"
  (SOME “V "THEN"”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(mod)"
  (SOME “V "mod"”)
  ;

(* TODO: lexer should support parenthesized star *)

(*
val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "f (+) 10"
  (SOME “App Opapp [App Opapp [V "f"; V "*"]; Lit (IntLit 10)]”)
  ;
 *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "f (+) 10"
  (SOME “App Opapp [App Opapp [V "f"; V "+"]; Lit (IntLit 10)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(+) 10 11"
  (SOME “App Opapp [App Opapp [V "+"; Lit (IntLit 10)]; Lit (IntLit 11)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(THEN) t1 t2"
  (SOME “App Opapp [App Opapp [V "THEN"; V "t1"]; V "t2"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "t1 THEN t2"
  (SOME “vbinop (Short "THEN") (V "t1") (V "t2")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "t1 * t2"
  (SOME “vbinop (Short "*") (V "t1") (V "t2")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "()"
  (SOME “Con NONE []”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "begin end"
  (SOME “Con NONE []”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Some begin end"
  (SOME “C "Some" [Con NONE []]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with\
  \ | [] -> 3\
  \ | [e;_] -> e"
  (SOME “Mat (Var (Short "x"))
             [(Pc "[]" [], Lit (IntLit 3));
              (Pc "::" [Pvar "e"; Pc "::" [Pany; Pc "[]" []]],
                       V "e")]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with\
  \ | Some 3 | Some 4 -> e\
  \ | _ -> d"
  (SOME “Mat (V "x")
             [(Pc "Some" [Plit (IntLit 3)], V "e");
              (Pc "Some" [Plit (IntLit 4)], V "e");
              (Pany, V "d")]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with \
  \ | [] -> 3\
  \ | [] :: _ -> 1\
  \ | (h::t) :: rest -> 2"
  (SOME “Mat (V "x")
             [(Pc "[]" [], Lit (IntLit 3));
              (Pc "::" [Pc "[]" []; Pany], Lit (IntLit 1));
              (Pc "::" [Pc "::" [Pvar "h"; Pvar "t"]; Pvar "rest"],
               Lit (IntLit 2))]”)
  ;

(* pattern match with guard;
 * expression matched on is bound to a variable to be re-used in else-branch of
 * condition on P, in order to execute its side effects only once. All remaining
 * pattern match rows (after the guarded row) are duplicated in the else-branch
 * of the condition on P.
 *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with \
  \ | h::t when P -> z \
  \ | _ -> w"
  (SOME “Let (SOME "") (V "x")
             (Mat (V "")
                  [(Pc "::" [Pvar "h"; Pvar "t"],
                    If (V "P") (V "z")
                       (Mat (V "") [(Pany, V "w")]));
                   (Pany, V "w")])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " try f x with E1 _ -> g x\
  \            | E2 -> h"
  (SOME “Handle (App Opapp [V "f"; V "x"])
                [(Pc "E1" [Pany], App Opapp [V "g"; V "x"]);
                 (Pc "E2" [], V "h")]”)
  ;


val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " function C1 _ -> A\
  \        | C2 -> B"
  (SOME “Fun "" (Mat (V "")
                     [(Pc "C1" [Pany], V "A");
                      (Pc "C2" [], V "B")])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "[3;4]"
  (SOME “C "::" [Lit (IntLit 3); C "::" [Lit (IntLit 4); C "[]" []]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "[ ]"
  (SOME “C "[]" []”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "3::t = l"
  (SOME “vbinop (Short "=")
                (C "::" [Lit (IntLit 3); V "t"])
                (V "l")”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "3 < x = true"
  (SOME “vbinop (Short "=")
                (vbinop (Short "<") (Lit (IntLit 3)) (V "x"))
                (C "True" [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(x,y,4)"
  (SOME “Con NONE [V "x"; V "y"; Lit (IntLit 4)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Cons (x,3)"
  (SOME “C "Cons" [Con NONE [V "x"; Lit (IntLit 3)]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "FUNCTION (x,3)"
  (SOME “App Opapp [V "FUNCTION"; Con NONE [V "x"; Lit (IntLit 3)]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "- 3"
  (SOME “App Opapp [Var (Long "Int" (Short "~")); Lit (IntLit 3)]”)
  ;

(* TODO: floating point literals not handled; not sure how to handle.
 *       call Double.fromString on them? *)

(*
val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "-. 3.0"
  (SOME “App Opapp [Var (Long "Double" (Short "~")); Lit (IntLit 3)]”)
  ;
 *)

(* if without the else *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if a then b"
  (SOME “If (V "a") (V "b") (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if a;c then b"
  (SOME “If (Let NONE (V "a") (V "c")) (V "b") (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Con (a,b,c)"
  (SOME “C "Con" [Con NONE [V "a"; V "b"; V "c"]]”)
  ;

(* -------------------------------------------------------------------------
 * Declarations
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " let v = A\
  \ and c = B"
  (SOME “[Dlet L (Pvar "v") (V "A");
          Dlet L (Pvar "c") (V "B")]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " let rec f x = A\
  \ and g y = B"
  (SOME “[Dletrec L [("f", "x", V "A");
                     ("g", "y", V "B")]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type t = s"
  (SOME “[Dtabbrev L [] "t" (Atapp [] (Short "s"))]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a, 'b) t = Cn of 'a * 'b"
  (SOME “[Dtype L [(["a"; "b"], "t", [("Cn", [Attup [Atvar "a"; Atvar "b"]])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a, 'b) t = Cn of ('a)"
  (SOME “[Dtype L [(["a"; "b"], "t", [("Cn", [Atvar "a"])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " type t = C1\
  \        | C2\
  \ and s = D1 of t"
  (SOME “[Dtype L [([], "t", [("C1", []); ("C2", [])]);
                   ([], "s", [("D1", [Atapp [] (Short "t")])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "exception This of 'a * 'b"
  (SOME “[Dexn L "This" [Attup [Atvar "a"; Atvar "b"]]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "exception This of 'a"
  (SOME “[Dexn L "This" [Atvar "a"]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type 'a tree = Lf1 | Nd of 'a tree * 'a * 'a tree | Lf2 of int"
  (SOME “[Dtype L [(["a"], "tree",
                   [("Lf1", []);
                    ("Nd", [Attup [Atapp [Atvar "a"] (Short "tree");
                                   Atvar "a";
                                   Atapp [Atvar "a"] (Short "tree")]]);
                    ("Lf2", [Atapp [] (Short "int")])])]]”);

(* -------------------------------------------------------------------------
 * Some larger examples with modules
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " module Queue = struct\
  \   type 'a queue = 'a list * 'a list\
  \   ;;\
  \   let enqueue (xs, ys) y = (xs, y::ys)\
  \   ;;\
  \   let rec dequeue (xs, ys) =\
  \     match xs with\
  \     | x::xs -> Some (x, (xs, ys))\
  \     | [] ->\
  \         (match ys with\
  \         | [] -> None\
  \         | _ -> dequeue (List.rev ys, []))\
  \   ;;\
  \   let empty = ([], [])\
  \   ;;\
  \   let flush (xs, ys) = xs @ List.rev ys\
  \   ;;\
  \ end (* struct *)"
  NONE
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " module Buffer = struct\
  \   type 'a buffer = 'a Queue.queue ref\
  \   ;;\
  \   let enqueue q x = q := Queue.enqueue (!q) x\
  \   ;;\
  \   let dequeue q =\
  \     match Queue.dequeue (!q) with\
  \     | None -> None\
  \     | Some (x, q') ->\
  \         q := q';\
  \         Some x\
  \   ;;\
  \   let empty () = ref Queue.empty\
  \   ;;\
  \   let flush q =\
  \     let els = Queue.flush (!q) in\
  \     q := Queue.empty;\
  \     els\
  \   ;;\
  \ end (* struct *)"
  NONE
  ;

(* -------------------------------------------------------------------------
 * Modules (structs, signatures)
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a,'b) t"
  (SOME “[Dtype L [(["a"; "b"], "t", [])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type tyname"
  (SOME “[Dtype L [([], "tyname", [])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a,'b) t = B1 | A1"
  (SOME “[Dtype L [(["a"; "b"], "t", [("B1", []); ("A1", [])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type t = B1 | A1"
  (SOME “[Dtype L [([], "t", [("B1", []); ("A1", [])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type t = z"
  (SOME “[Dtabbrev L [] "t" (Atapp [] (Short "z"))]”)
  ;

val _ = parsetest0 “nSigSpec” “ptree_SigSpec”
  "sig val x : t end"
  (SOME “()”)
  ;

val _ = parsetest0 “nModuleType” “ptree_ModuleType”
  "sig val x : t end"
  (SOME “()”)
  ;

val _ = parsetest0 “nModuleType” “ptree_ModuleType”
  "SIGNATURENAME"
  (SOME “()”)
  ;

val _ = parsetest0 “nModuleType” “ptree_ModuleType”
  "Module.SIGnaturename"
  (SOME “()”)
  ;

val _ = parsetest0 “nModuleType” “ptree_ModuleType”
  "Module.Signature_name"
  (SOME “()”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " module type SIGNAME = sig \
  \   val x : t \
  \   val y : d \
  \ end"
  (SOME “[]:dec list”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " module type Sig_Name3 = sig \
  \   type t = foo \
  \   val x : t \
  \   val y : d \
  \ end"
  (SOME “[]:dec list”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " module type Sig_Name3 = sig \
  \   type 'a t \
  \ end"
  (SOME “[]:dec list”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "module Mod : Ssig = struct end"
  (SOME “[Dmod "Mod" ([]:dec list)]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "module type sign = sig end"
  (SOME “[]:dec list”)
  ;

(* -------------------------------------------------------------------------
 * Candle compatibility layer.
 *
 * We replace all on the left in this list, with what's on the right:
 *
 * Modules:
 *   Text_io        -> TextIO
 *   Word8_array    -> Word8Array
 *   Command_line   -> CommandLine
 *   Pretty_printer -> PrettyPrinter
 *
 * Constructors:
 *   Bad_file_name  -> BadFileName
 *   Pp_data        -> PP_Data
 *
 * This is done for constructor names and module names.
 *
 * We also curry all constructor application patterns and constructor
 * applications that come from this list:
 *
 *   Abs, Comb, Var, Const (two arguments)
 *   Sequent               (two arguments)
 *   PP_Data               (two arguments)
 *
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nConstrName” “ptree_ConstrName”
  "Bad_file_name"
  (SOME “"BadFileName"”)
  ;

val _ = parsetest0 “nConstrName” “ptree_ConstrName”
  "Pp_data"
  (SOME “"PP_Data"”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Text_io.Bad_file_name"
  (SOME “["TextIO"; "BadFileName"]”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Pretty_printer.Pp_data"
  (SOME “["PrettyPrinter"; "PP_Data"]”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Text_io"
  (SOME “"TextIO"”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Word8_array"
  (SOME “"Word8Array"”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Command_line"
  (SOME “"CommandLine"”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Pretty_printer"
  (SOME “"PrettyPrinter"”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Pretty_printer.token"
  (SOME “Var (Long "PrettyPrinter" (Short "token"))”)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Pretty_printer.Text_io.stuff"
  (SOME “Var (Long "PrettyPrinter" (Long "TextIO" (Short "stuff")))”)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Comb (x, y)"
  (SOME “C "Comb" [V "x"; V "y"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Abs (x, y)"
  (SOME “C "Abs" [V "x"; V "y"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Var (x, y)"
  (SOME “C "Var" [V "x"; V "y"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Sequent (x, y)"
  (SOME “C "Sequent" [V "x"; V "y"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Const (x, y)"
  (SOME “C "Const" [V "x"; V "y"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Pretty_printer.Pp_data (x, y)"
  (SOME “Con (SOME (Long "PrettyPrinter" (Short "PP_Data"))) [V "x"; V "y"]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Comb (Var (v, s), Const (w, t))"
  (SOME “C "Comb" [C "Var" [V "v"; V "s"]; C "Const" [V "w"; V "t"]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Comb (Var (v, s), Const (w, t))"
  (SOME “Pc "Comb" [Pc "Var" [Pv "v"; Pv "s"]; Pc "Const" [Pv "w"; Pv "t"]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Append (Append (v, s), Append (w, t))"
  (SOME “Pc "Append" [Pc "Append" [Pv "v"; Pv "s"];
                      Pc "Append" [Pv "w"; Pv "t"]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Append (Append (v, s), Append (w, t))"
  (SOME “C "Append" [C "Append" [V "v"; V "s"];
                     C "Append" [V "w"; V "t"]]”)
  ;

(* TODO
 *   It's not necessary, but it would be nice if we can turn
 *   e.g. Comb _ into Comb _ _.
 *)

(*


val _ = parsetest0 ``nTopLevelDec`` ``ptree_TopLevelDec`` "val w = 0wx3"
          (SOME ``Dlet locs (Pvar "w") (Lit (Word64 3w))``)

val _ = parsetest0 ``nE`` ``ptree_Expr nE`` "#(read) byte_array"
          (SOME ``App (FFI "read") [Var (Short "byte_array")]``)

val _ = parsetest0 ``nTopLevelDec`` ``ptree_TopLevelDec`` "val w = 0wxf"
          (SOME ``Dlet locs (Pvar "w") (Lit (Word64 15w))``)

val _ = parsetest0 ``nTopLevelDec`` ``ptree_TopLevelDec`` "val w = 0w3"
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

val _ = parsetest0 ``nTopLevelDec`` ``ptree_TopLevelDec``
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
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec``
                  "structure s = struct val x = 3 end"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec``
                  "structure s :> sig val x : int end = struct val x = 3 end"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec``
                  "structure s :> sig val x : int; end = struct val x = 3 end"
val _ = parsetest ``nTopLevelDec`` ``ptree_TopLevelDec`` "val x = 10"

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
 *)

val _ = export_theory ();

