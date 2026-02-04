(*
  Some tests for the OCaml parser.

  The setup is copied from ../tests/cmlTestsScript.sml.
*)
Theory camlTests
Ancestors
  misc[qualified] pegexec[qualified] caml_lex camlPEG
  camlPtreeConversion ast[qualified]
Libs
  preamble ASCIInumbersLib[qualified] stringSyntax[qualified]


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

exception ExpectedFailure;
fun expectFailure prefix test =
  (test (); raise ExpectedFailure)
  handle Fail m =>
    if String.isPrefix ("Failed " ^ prefix) m then
      print ("OK, failed as expected, message: " ^ m ^ "\n")
    else
      (print "Unexpected failure!\n"; raise Fail m);

(* -------------------------------------------------------------------------
 * Various identifiers
 * ------------------------------------------------------------------------- *)

(* No lowercase letters in tail means it's a variable name *)

val _ = parsetest0 “nValueName” “ptree_ValueName”
  "A_"
  (SOME “«A_»”)
  ;

(* Starts with uppercase, one lowercase letter in tail and no uppercase
 * means its a constructor. *)

val _ = parsetest0 “nConstrName” “ptree_ConstrName”
  "A_a"
  (SOME “«A_a»”)
  ;


(* Variable; an uppercase letter in the tail. *)

val _ = parsetest0 “nValueName” “ptree_ValueName”
  "A_aA"
  (SOME “«A_aA»”)
  ;


(* Starts with lowercase; variable. *)

val _ = parsetest0 “nValueName” “ptree_ValueName”
  "aAa"
  (SOME “«aAa»”)
  ;

(* Starts with uppercase; one lowercase in tail; no uppercase in tail:
 * module name (same as constructor). *)

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "A_b"
  (SOME “«A_b»”)
  ;

(* Module name. *)

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Bbb"
  (SOME “«Bbb»”)
  ;

(* No lowercase letters in tail: variable. *)

val _ = parsetest0 “nValueName” “ptree_ValueName”
  "B"
  (SOME “«B»”)
  ;

(* -------------------------------------------------------------------------
 * CakeML escape hatch
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "raise (Fail \"5\")"
  (SOME “Raise (C «Fail» [Lit (StrLit «5»)])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "raise (f x)"
  (SOME “Raise (App Opapp [V «f»; V «x»])”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "let x = 2 ;; (*CML val x = 5; print \"z\"; fun ref x = Ref x; *)"
  (SOME “[Dlet L1 (Pv «x») (Lit (IntLit 2));
          Dlet L2 (Pv «x») (Lit (IntLit 5));
          Dlet L3 (Pv «it») (App Opapp [V «print»; Lit (StrLit «z»)]);
          Dletrec L4 [(«ref»,«x», App Opref [V «x»])]]”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "(*CML val x = x; (*CML comments and pragmas are skipped *) val y = y;*)"
  (SOME “[Dlet L1 (Pv «x») (V «x»);
          Dlet L2 (Pv «y») (V «y»)]”)
  ;

val _ = expectFailure "REMAINING INPUT"
      (fn () => parsetest0 “nStart” “ptree_Start”
                           "let x = (*CML val x = x; *) 6;;"
                           NONE);

(* -------------------------------------------------------------------------
 * Types
 * ------------------------------------------------------------------------- *)

fun tytest0 s r = parsetest0 “nType” “ptree_Type” s (SOME r);
val tytest = parsetest “nType” “ptree_Type”;

val _ = tytest0 "'a"
  “Atvar «a»”
  ;

val _ = tytest0 "'a * 'b"
  “Attup [Atvar «a»; Atvar «b»]”
  ;

val _ = tytest0 "'a * 'b * 'c"
  “Attup [Atvar «a»; Atvar «b»; Atvar «c»]”
  ;

val _ = tytest0 "'a * 'b -> 'c"
  “Atfun (Attup [Atvar «a»; Atvar «b»]) (Atvar «c»)”
  ;

val _ = tytest0 "('a, 'b) blorb"
  “Atapp [Atvar «a»; Atvar «b»] (Short «blorb»)”
  ;

val _ = tytest0 "Foo.blorb"
  “Atapp [] (Long «Foo» (Short «blorb»))”
  ;

val _ = tytest0 "'a * bool"
  “Attup [Atvar «a»; Atapp [] (Short «bool»)]”
  ;

val _ = tytest0 "'a * bool * 'c"
  “Attup [Atvar «a»; Atapp [] (Short «bool»); Atvar «c»]”
  ;

val _ = tytest0 "'a * bool -> 'a"
  “Atfun (Attup [Atvar «a»; Atapp [] (Short «bool»)]) (Atvar «a»)”
  ;

val _ = tytest0 "'a * (bool * 'c)"
  “Attup [Atvar «a»; Attup [Atapp [] (Short «bool»); Atvar «c»]]”
  ;

val _ = tytest0 "('a * bool) * 'c"
  “Attup [Attup [Atvar «a»; Atapp [] (Short «bool»)]; Atvar «c»]”
  ;

val _ = tytest0 "('a * 'b)"
  “Attup [Atvar «a»; Atvar «b»]”
  ;

val _ = tytest0 "('a,'b) d"
 “Atapp [Atvar «a»; Atvar «b»] (Short «d»)”
 ;

(* -------------------------------------------------------------------------
 * Patterns
 * ------------------------------------------------------------------------- *)

Definition mkpat_def:
  mkpat p = INR p : (modN, varN) id # mlstring list + pat
End

val eval = rconc o EVAL;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Cc a as i, Dd b as j" (* = ((Cc a as i), Dd b) as j *)
  (SOME $ eval “[mkpat $ Pas (Pcon NONE [Pas (Pc «Cc» [Pv «a»]) «i»;
                                         Pc «Dd» [Pv «b»]]) «j»]” )
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "(x) as i :: j" (* = (x as i) :: j *)
  (SOME $ eval “[mkpat $ Pc «::» [Pas (Pv «x») «i»; Pv «j»]]”)
  ;

(* , is below :: in prec. but we can raise it by wrapping it with 'as i' *)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x,y as i :: j"
  (SOME $ eval “[mkpat $ Pc «::» [Pas (Pcon NONE [Pv «x»; Pv «y»]) «i»;
                                  Pv «j»]]”)
  ;

(* can nest 'as' arbitrarily deep (though its a pretty useless feature) *)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x as i as j as k"
  (SOME $ eval “[mkpat $ Pas (Pas (Pas (Pv «x») «i») «j») «k»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x as i as j as k :: j"
  (SOME $ eval “[mkpat $ Pc «::» [Pas (Pas (Pas (Pv «x») «i») «j») «k»;
                                  Pv «j»]]”)
  ;

(* as needs to bind anything to its left *)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x as i :: y as j"
  (SOME $ eval “[mkpat $ Pas (Pc «::» [Pas (Pv «x») «i»; Pv «y»]) «j»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x as i :: y as j :: z as k"
  (SOME $ eval “[mkpat $ Pas (Pc «::» [
                 Pas (Pc «::» [Pas (Pv «x») «i»; Pv «y»]) «j»; Pv «z»])
              «k»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x,y as i :: y as j :: z as k"
  (SOME $ eval “[mkpat $ Pas (Pc «::» [
                 Pas (Pc «::» [Pas (Pcon NONE [Pv «x»; Pv «y»]) «i»;
                               Pv «y»]) «j»;
                 Pv «z»]) «k»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "a, b | c, d"
  (SOME $ eval “[mkpat $ Pcon NONE [Pv «a»; Pv «b»];
                 mkpat $ Pcon NONE [Pv «c»; Pv «d»]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Comb (a,b) as c, d"
  (SOME $ eval “[mkpat $ Pcon NONE [Pas (Pc «Comb» [Pv «a»; Pv «b»]) «c»;
                 Pv «d»]]”)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "false::[]"
  (SOME $ eval “[mkpat $ Pc «::» [Pc «False» []; Pc «[]» []]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x as y"
  (SOME $ eval “[mkpat $ Pas (Pvar «x») «y»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "x | y"
  (SOME $ eval “[mkpat $ Pvar «x»; mkpat $ Pvar «y»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Some x | y"
  (SOME $ eval “[mkpat $ Pc «Some» [Pvar «x»]; mkpat $ Pvar «y»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "y,z,x"
  (SOME $ eval “[mkpat $ Pcon NONE [Pvar «y»; Pvar «z»; Pvar «x»]]”)
  ;

(* Make sure or-patterns distribute OK *)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Some (x | Inl (y | z))"
  (SOME $ eval “[mkpat $ Pc «Some» [Pv «x»];
                 mkpat $ Pc «Some» [Pc «Inl» [Pv «y»]];
                 mkpat $ Pc «Some» [Pc «Inl» [Pv «z»]]]”)
  ;

(* Make sure the precedence parser can handle commas correctly
   (they are non-associative)
 *)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "(y,z),x"
  (SOME $ eval “[mkpat $ Pcon NONE [Pcon NONE [Pvar «y»; Pvar «z»]; Pvar «x»]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "y,(z,x)"
  (SOME $ eval “[mkpat $ Pcon NONE [Pv «y»; Pcon NONE [Pvar «z»; Pvar «x»]]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "(x: int)"
  (SOME $ eval “[mkpat $ Ptannot (Pvar «x») (Atapp [] (Short «int»))]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Aa (Bb (Cc x))"
  (SOME $ eval “[mkpat $ Pc «Aa» [Pc «Bb» [Pc «Cc» [Pvar «x»]]]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "a :: 1"
  (SOME $ eval “[mkpat $ Pc «::» [Pvar «a»; Plit (IntLit 1)]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "[a,b ; c]"
  (SOME $ eval “[mkpat $ Pc «::» [Pcon NONE [Pvar «a»; Pvar «b»];
                   Pc «::» [Pvar «c»; Pc «[]» []]]]”)
  ;

(* Nesting with all three pattern operators at once. The alias distributes over
 * both sides due to the or-pattern which is apparently what happens in OCaml
 * as well (madness).
 *)

val _ = parsetest0 “nPattern” “ptree_PPattern”
  "a,b :: c, d | zs as i"
  (SOME “ Pp_as (Pp_or (Pp_con NONE [
             Pp_var «a»; Pp_con (SOME (Short «::»)) [Pp_var «b»; Pp_var «c»];
             Pp_var «d»]) (Pp_var «zs»)) «i»”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "a,b :: c, d | zs as i"
  (SOME $ eval “[mkpat $ Pas (Pcon NONE [Pv «a»; Pc «::» [Pv «b»; Pv «c»];
                                   Pv «d»]) «i»;
                 mkpat $ Pas (Pv «zs») «i»]”)
  ;

val _ = parsetest0 “nPattern” “ptree_PPattern”
  "(y as z)"
  NONE


val _ = parsetest0 “nPattern” “ptree_PPattern”
  "Cn(x,(y as z))"
  (SOME “Pp_con (SOME (Short «Cn»))
                [Pp_con NONE [Pp_var «x»; Pp_as (Pp_var «y») «z»]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Cn(x,(y as z))"
  (SOME $ eval “[mkpat $ Pc «Cn» [Pcon NONE [Pv «x»; Pas (Pv «y») «z»]]]”)
  ;

(* -------------------------------------------------------------------------
 * Record syntax
 * ------------------------------------------------------------------------- *)

(* record projection and update *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "x.Cons.foo"
  (SOME $ eval “App Opapp [V (mk_record_proj_name «foo» «Cons»);
                           V «x»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Foo {x with foo = bar}"
  (SOME $ eval “App Opapp [App Opapp [
                        V (mk_record_update_name «foo» «Foo»); V «x»];
                        V «bar»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Foo {x with foo = bar;}"
  (SOME $ eval “App Opapp [App Opapp [
                        V (mk_record_update_name «foo» «Foo»); V «x»];
                        V «bar»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Foo {x with foo = bar; baz = quux;}"
  (SOME $ eval “App Opapp [App Opapp [V (mk_record_update_name «baz» «Foo»);
           App Opapp [App Opapp [V (mk_record_update_name «foo» «Foo»);
             V «x»]; V «bar»]]; V «quux»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Bar.Foo {x with foo = bar; baz = quux;}"
  (SOME $ eval “App Opapp [App Opapp [
                  Var (Long «Bar» (Short (mk_record_update_name «baz» «Foo»)));
                  App Opapp [App Opapp [
                    Var (Long «Bar» (Short (mk_record_update_name «foo» «Foo»)));
                    V «x»]; V «bar»]]; V «quux»]”)
  ;

(* construction *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Foo { foo = 5; bar = true }"
  (SOME $ eval
    “App Opapp [App Opapp [V (mk_record_constr_name «Foo» [«bar»;«foo»]);
                           (C «True» [])];
                    Lit (IntLit 5)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Foo { f2 = 2; f1 = 1; f3 = 3;}"
  NONE
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Bar.Foo { f2 = 2; f1 = 1; f3 = 3;}"
  NONE
  ;

(* declaration *)

val _ = parsetest0 “nStart” “ptree_Start”
  "type rec1 = Foo of {f3: t3; f1: t1; f2: t2};;"
  NONE
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "type rec1 = Foo of {foo: int; bar: bool};;"
  (SOME $ eval “
      [Dtype L [([],«rec1»,[(«Foo»,[Attup [Atapp [] (Short «bool»); Atapp [] (Short «int»)]])])];
       Dlet L1 (Pv (mk_record_constr_name «Foo» [«bar»;«foo»]))
          (Fun «bar» (Fun «foo» (C «Foo» [Con NONE [V «bar»; V «foo»]])));
        Dlet L2 (Pv (mk_record_proj_name «bar» «Foo»))
          (Fun «» (Mat (V «») [(Pc «Foo» [Pcon NONE [Pv «bar»; Pv «foo»]],V «bar»)]));
        Dlet L3 (Pv (mk_record_proj_name «foo» «Foo»))
          (Fun «» (Mat (V «») [(Pc «Foo» [Pcon NONE [Pv «bar»; Pv «foo»]],V «foo»)]));
        Dlet L4 (Pv (mk_record_update_name «bar» «Foo»))
          (Fun «»
             (Mat (V «»)
                [(Pc «Foo» [Pcon NONE [Pv «bar»; Pv «foo»]],
                  Fun «bar» (C «Foo» [Con NONE [V «bar»; V «foo»]]))]));
        Dlet L5 (Pv (mk_record_update_name «foo» «Foo»))
          (Fun «»
             (Mat (V «»)
                [(Pc «Foo» [Pcon NONE [Pv «bar»; Pv «foo»]],
                  Fun «foo» (C «Foo» [Con NONE [V «bar»; V «foo»]]))]))]”)
  ;

(* 2024-06-06: pattern matching *)

Definition mkrec_def:
  mkrec x = INL x : (modN, varN) id # mlstring list + pat
End

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Foo {b; a}"
  (SOME $ eval “[mkrec (Short «Foo», [«b»; «a»])]”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "let f d (Foo {c; a}) b = z;;"
  NONE;

val _ = parsetest0 “nStart” “ptree_Start”
  "match y with\
  \  Foo {z} -> f z;;"
  NONE
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "match y with\
  \  Bar.Foo {z} -> f z;;"
  NONE
  ;

(* -------------------------------------------------------------------------
 * Expressions
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "true || let y = z in y"
  (SOME “Log Orelse (C «True» []) (Let (SOME «y») (V «z») (V «y»))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let y = z in y || true"
  (SOME “Let (SOME «y») (V «z») (Log Orelse (V «y») (C «True» []))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "0 + match x with y -> z"
  (SOME (“vbinop (Short «+») (Lit (IntLit 0))
                 (Let (SOME « m») (V «x»)
                   (Mat (V « m») [(Pv «y», V «z»)]))”))
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "- fun x -> x"
  (SOME “App Opapp [Var (Long «Int» (Short «~»)); Fun «x» (V «x»)]”)
  ;

val _ = parsetest0 “nENeg” “ptree_Expr nENeg”
  " - let y = z in y"
  (SOME “App Opapp [Var (Long «Int» (Short «~»));
                    Let (SOME «y») (V «z») (V «y»)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "a, [], fun x -> ()"
  (SOME “Con NONE [V «a»; C «[]» []; Fun «x» (Con NONE [])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "a, match x with y -> z, w"
  (SOME “Con NONE [V «a»;
                   Let (SOME « m») (V «x»)
                       (Mat (V « m») [(Pv «y», Con NONE [V «z»; V «w»])])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match x with y -> z, w"
  (SOME “Let (SOME « m») (V «x»)
             (Mat (V « m») [(Pv «y», Con NONE [V «z»; V «w»])])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match !myref () with a -> b"
  (SOME “Let (SOME « m»)
             (App Opapp [App Opapp [V «!»; V «myref»]; Con NONE []])
             (Mat (V « m») ([(Pv «a», V «b»)]))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "f !myref"
  (SOME “App Opapp [V «f»; App Opapp [V «!»; V «myref»]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "x && y"
  (SOME “Log Andalso (V «x») (V «y»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "x || y"
  (SOME “Log Orelse (V «x») (V «y»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if x || y then x && y"
  (SOME “If (Log Orelse (V «x») (V «y»))
            (Log Andalso (V «x») (V «y»))
            (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(n-1)"
  (SOME “vbinop (Short «-») (V «n») (Lit (IntLit 1))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(n -1)"
  (SOME “vbinop (Short «-») (V «n») (Lit (IntLit 1))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "-1"
  (SOME “App Opapp [Var (Long «Int» (Short «~»)); Lit (IntLit 1)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(+) ; 2"
  (SOME “Let NONE (V «+») (Lit (IntLit 2))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "function x -> y ; function a -> b"
  (SOME “Fun «» (Mat (V «»)
                     [(Pv «x», Let NONE (V «y»)
                              (Fun «» (Mat (V «»)
                                      [(Pv «a», V «b»)])))])”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " let print_stdout printer data =\
  \   let st = empty () in\
  \   printer st data;\
  \   let tok = to_token st in\
  \   let apps = Pretty_core.print (!margin) tok in\
  \   App_list.iter (output_string stdout) apps"
  (SOME “[Dlet L (Pv «print_stdout») (Fun «printer» (Fun «data»
            (Let (SOME «st») (App Opapp [V «empty»; Con NONE []])
              (Let NONE (App Opapp [App Opapp [V «printer»; V «st»]; V «data»])
                (Let (SOME «tok») (App Opapp [V «to_token»; V «st»])
                  (Let (SOME «apps»)
                    (App Opapp [App Opapp [Var (Long «Pretty_core»
                                                 (Short «print»));
                                           App Opapp [V «!»; V «margin»]];
                                V «tok»])
                    (App Opapp [App Opapp [Var (Long «App_list» (Short «iter»));
                                           App Opapp [V «output_string»;
                                                      V «stdout»]];
                                V «apps»])))))))]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if x;y then  z"
  (SOME “If (Let NONE (V «x») (V «y»)) (V «z») (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if y then z; w"
  (SOME “Let NONE (If (V «y») (V «z») (Con NONE [])) (V «w»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x -> y ; z"
  (SOME “Fun «x» (Let NONE (V «y») (V «z»))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(fun x -> y) ; z"
  (SOME “Let NONE (Fun «x» (V «y»)) (V «z»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "[let x = a in x; let y = b in y]"
  (SOME “
    C «::» [Let (SOME «x») (V «a»)
                (Let NONE (V «x»)
                          (Let (SOME «y») (V «b») (V «y»)));
            C «[]» []]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match x with \
  \ | a -> f; c \
  \ | b -> q; w"
  (SOME “
    Let (SOME « m») (V «x»)
      (Mat (V « m»)
          [(Pv «a», Let NONE (V «f») (V «c»));
           (Pv «b», Let NONE (V «q») (V «w»))])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if b then let x = z in a; b"
  (SOME “
    If (V «b»)
       (Let (SOME «x») (V «z»)
            (Let NONE (V «a») (V «b»)))
       (Con NONE [])”)
  ;


val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "foo; if b then print (); bar"
  (SOME “
    Let NONE (V «foo»)
        (Let NONE (If (V «b») (App Opapp [V «print»; Con NONE []])
                      (Con NONE []))
                  (V «bar»))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "foo; let x = z in y ; bar"
  (SOME “
    Let NONE (V «foo»)
        (Let (SOME «x») (V «z»)
             (Let NONE (V «y») (V «bar»)))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let (:=) x = z in w"
  (SOME “Let (SOME «:=») (Fun «x» (V «z»)) (V «w»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(:=)"
  (SOME “(V «:=»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let _ = Ref x in z"
  (SOME “Let NONE (App Opref [V «x»]) (V «z»)”)
  ;

val _ = parsetest0 “nValuePath” “ptree_ValuePath”
  "Aa.B_b.c"
  (SOME “[«Aa»; «B_b»; «c»]”)
  ;

val _ = parsetest0 “nValuePath” “ptree_ValuePath”
  "B_b.cDEF"
  (SOME “[«B_b»; «cDEF»]”)
  ;

val _ = parsetest0 “nValuePath” “ptree_ValuePath”
  "cDEF"
  (SOME “[«cDEF»]”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Cd"
  (SOME “[«Cd»]”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Ab.Cd"
  (SOME “[«Ab»; «Cd»]”)
  ;

val _ = parsetest0 “nModulePath” “ptree_ModulePath”
  "Mm.Nn"
  (SOME “[«Mm»; «Nn»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let [x; y] = z in w"
  (SOME “Mat (V «z»)
           [(Pc «::» [Pvar «x»;
               Pc «::» [Pvar «y»;
                 Pc «[]» []]], V «w»)]”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let a x = y and b x = z in w"
  (SOME “Let (SOME «a») (Fun «x» (Var (Short «y»)))
             (Let (SOME «b») (Fun «x» (Var (Short «z»)))
                  (Var (Short «w»)))”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let f x y = x in z"
  (SOME “Let (SOME «f») (Fun «x» (Fun «y» (V «x»))) (V «z»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let f (x,y) = x in z"
  (SOME “Let (SOME «f»)
             (Fun «» (Mat (V «») [(Pcon NONE [Pvar «x»; Pvar «y»], V «x»)]))
             (V «z»)”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let f x = x in y"
  (SOME “Let (SOME «f») (Fun «x» (V «x»)) (V «y»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let rec f x = x in y"
  (SOME “Letrec [(«f», «x», V «x»)] (V «y»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let rec f x y = x in z"
  (SOME “Letrec [(«f», «x», Fun «y» (V «x»))] (V «z»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let _ = print \"foo\" in\
  \  let z = 10 in\
  \  let (x,y) = g z in\
  \  let rec h x = x + 1 in\
  \  x + y"
  (SOME “Let NONE (App Opapp [V «print»; Lit (StrLit «foo»)])
           (Let (SOME «z») (Lit (IntLit 10))
             (Mat (App Opapp [V «g»; V «z»])
                [(Pcon NONE [Pvar «x»; Pvar «y»],
                  Letrec [(«h», «x»,
                           vbinop (Short «+») (V «x») (Lit (IntLit 1)))]
                         (vbinop (Short «+») (V «x») (V «y»)))]))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "let (x,y) = g z in\
  \  let [h] = f a in\
  \  x + y * h"
 (SOME “Mat (App Opapp [V «g»; V «z»])
            [(Pcon NONE [Pvar «x»; Pvar «y»],
              Mat (App Opapp [V «f»; V «a»])
                  [(Pc «::» [Pvar «h»; Pc «[]» []],
                    vbinop (Short «+») (V «x»)
                           (vbinop (Short «*») (V «y») (V «h»)))])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x -> x"
  (SOME “Fun «x» (V «x»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun (x, y) -> x + y"
  (SOME “Fun «» (Mat (V «»)
                     [(Pcon NONE [Pvar «x»; Pvar «y»],
                       vbinop (Short «+») (V «x») (V «y»))])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x y z -> y"
  (SOME “Fun «x» (Fun «y» (Fun «z» (V «y»)))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun z (x, y) w -> x + y"
  (SOME “Fun «z» (Fun «» (Mat (V «»)
                     [(Pcon NONE [Pvar «x»; Pvar «y»],
                       Fun «w» (vbinop (Short «+») (V «x») (V «y»)))]))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(x : int)"
  (SOME “Tannot (V «x») (Atapp [] (Short «int»))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(x : int) + 3"
  (SOME “vbinop (Short «+») (Tannot (V «x») (Atapp [] (Short «int»)))
                            (Lit (IntLit 3))”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(=)"
  (SOME “V «=»”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(THEN)"
  (SOME “V «THEN»”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(mod)"
  (SOME “V «mod»”)
  ;

(* TODO: lexer should support parenthesized star *)

(*
val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "f (+) 10"
  (SOME “App Opapp [App Opapp [V «f»; V «*»]; Lit (IntLit 10)]”)
  ;
 *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "f (+) 10"
  (SOME “App Opapp [App Opapp [V «f»; V «+»]; Lit (IntLit 10)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(+) 10 11"
  (SOME “App Opapp [App Opapp [V «+»; Lit (IntLit 10)]; Lit (IntLit 11)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(THEN) t1 t2"
  (SOME “App Opapp [App Opapp [V «THEN»; V «t1»]; V «t2»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "t1 THEN t2"
  (SOME “vbinop (Short «THEN») (V «t1») (V «t2»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "t1 * t2"
  (SOME “vbinop (Short «*») (V «t1») (V «t2»)”)
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
  (SOME “C «Some» [Con NONE []]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with\
  \ | [] -> 3\
  \ | [e;_] -> e"
  (SOME “Let (SOME « m») (V «x»)
             (Mat (V « m»)
                  [(Pc «[]» [], Lit (IntLit 3));
                   (Pc «::» [Pvar «e»; Pc «::» [Pany; Pc «[]» []]],
                            V «e»)])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with\
  \ | Some 3 | Some 4 -> e\
  \ | _ -> d"
  (SOME “Let (SOME « m») (V «x»)
             (Mat (V « m»)
                  [(Pc «Some» [Plit (IntLit 3)], V «e»);
                   (Pc «Some» [Plit (IntLit 4)], V «e»);
                   (Pany, V «d»)])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " match x with \
  \ | [] -> 3\
  \ | [] :: _ -> 1\
  \ | (h::t) :: rest -> 2"
  (SOME “Let (SOME « m») (V «x»)
             (Mat (V « m»)
                  [(Pc «[]» [], Lit (IntLit 3));
                   (Pc «::» [Pc «[]» []; Pany], Lit (IntLit 1));
                   (Pc «::» [Pc «::» [Pvar «h»; Pvar «t»]; Pvar «rest»],
                    Lit (IntLit 2))])”)
  ;

(* pattern match with guard;
 * expression matched on is bound to a variable to be re-used in else-branch of
 * condition on P, in order to execute its side effects only once. All remaining
 * pattern match rows (after the guarded row) are duplicated in the else-branch
 * of the condition on P.
 *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match x with \n\
  \| h::t when P -> z \n\
  \| [] -> z \n\
  \| _ -> w"
  (SOME “
    Let (SOME « m») (V «x»)
      (Let (SOME « p») (Fun « u» (Mat (V « m») [(Pc «[]» [],V «z»);
                                                (Pany,V «w»)]))
       (Mat (V « m»)
          [(Pc «::» [Pv «h»; Pv «t»],
            If (V «P») (V «z») (App Opapp [V « p»; Con NONE []]));
           (Pany,App Opapp [V « p»; Con NONE []])]))”);


val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "match x with \n\
  \| r1 when x1 -> y1\n\
  \| r2 -> y2\n\
  \| r3 when x3 -> y3\n\
  \| r4 -> y4\n"
  (SOME “
    Let (SOME « m») (V «x»)
      (Let (SOME « p»)
        (Fun « u» (Mat (V « m») [
                    (Pv «r2», V «y2»);
                    (Pany, Let (SOME « p»)
                             (Fun « u» (Mat (V « m») [(Pv «r4»,V «y4»)]))
                             (Mat (V « m») [
                               (Pv «r3», If (V «x3») (V «y3»)
                                         (App Opapp [V « p»; Con NONE []]));
                               (Pany,App Opapp [V « p»; Con NONE []])]))]))
        (Mat (V « m») [
          (Pv «r1»,If (V «x1») (V «y1») (App Opapp [V « p»; Con NONE []]));
          (Pany,App Opapp [V « p»; Con NONE []])]))”);

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " try f x with Ea _ -> g x\
  \            | Eb -> h"
  (SOME “Handle (App Opapp [V «f»; V «x»])
           [(Pv « e», Mat (V « e»)
               [(Pc «Ea» [Pany],App Opapp [V «g»; V «x»]);
                (Pc «Eb» [],V «h»);
                (Pany, Raise (V « e»))])]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "try f ()\n\
  \with Bar when P -> X"
  (SOME “
    Handle (App Opapp [V «f»; Con NONE []])
     [(Pv « e»,
       Let (SOME « p») (Fun « u» (Raise (V « e»)))
           (Mat (V « e»)
                [(Pc «Bar» [],
                  If (V «P») (V «X»)
                     (App Opapp [V « p»; Con NONE []]));
                 (Pany, App Opapp [V « p»; Con NONE []])]))]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  " function Ca _ -> A\
  \        | Cb -> B"
  (SOME “Fun «» (Mat (V «»)
                     [(Pc «Ca» [Pany], V «A»);
                      (Pc «Cb» [], V «B»)])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "[3;4]"
  (SOME “C «::» [Lit (IntLit 3); C «::» [Lit (IntLit 4); C «[]» []]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "[ ]"
  (SOME “C «[]» []”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "3::t = l"
  (SOME “vbinop (Short «=»)
                (C «::» [Lit (IntLit 3); V «t»])
                (V «l»)”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "3 < x = true"
  (SOME “vbinop (Short «=»)
                (vbinop (Short «<») (Lit (IntLit 3)) (V «x»))
                (C «True» [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "(x,y,4)"
  (SOME “Con NONE [V «x»; V «y»; Lit (IntLit 4)]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Cons (x,3)"
  (SOME “C «Cons» [Con NONE [V «x»; Lit (IntLit 3)]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "FUNCTION (x,3)"
  (SOME “App Opapp [V «FUNCTION»; Con NONE [V «x»; Lit (IntLit 3)]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "- 3"
  (SOME “App Opapp [Var (Long «Int» (Short «~»)); Lit (IntLit 3)]”)
  ;

(* if without the else *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if a then b"
  (SOME “If (V «a») (V «b») (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "if a;c then b"
  (SOME “If (Let NONE (V «a») (V «c»)) (V «b») (Con NONE [])”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Con (a,b,c)"
  (SOME “C «Con» [Con NONE [V «a»; V «b»; V «c»]]”)
  ;

(* -------------------------------------------------------------------------
 * Declarations
 * ------------------------------------------------------------------------- *)

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " let v = A\
  \ and c = B"
  (SOME “[Dlet L (Pvar «v») (V «A»);
          Dlet L (Pvar «c») (V «B»)]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " let rec f x = A\
  \ and g y = B"
  (SOME “[Dletrec L [(«f», «x», V «A»);
                     («g», «y», V «B»)]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type t = s"
  (SOME “[Dtabbrev L [] «t» (Atapp [] (Short «s»))]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a, 'b) t = Cn of 'a * 'b"
  (SOME “[Dtype L [([«a»; «b»], «t», [(«Cn», [Attup [Atvar «a»; Atvar «b»]])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a, 'b) t = Cn of ('a)"
  (SOME “[Dtype L [([«a»; «b»], «t», [(«Cn», [Atvar «a»])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  " type t = Ca\
  \        | Cb\
  \ and s = Dd of t"
  (SOME “[Dtype L [([], «t», [(«Ca», []); («Cb», [])]);
                   ([], «s», [(«Dd», [Atapp [] (Short «t»)])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "exception This of 'a * 'b"
  (SOME “[Dexn L «This» [Attup [Atvar «a»; Atvar «b»]]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "exception This of 'a"
  (SOME “[Dexn L «This» [Atvar «a»]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type 'a tree = Lf1 | Nd of 'a tree * 'a * 'a tree | Lf2 of int"
  (SOME “[Dtype L [([«a»], «tree»,
                   [(«Lf1», []);
                    («Nd», [Attup [Atapp [Atvar «a»] (Short «tree»);
                                   Atvar «a»;
                                   Atapp [Atvar «a»] (Short «tree»)]]);
                    («Lf2», [Atapp [] (Short «int»)])])]]”);

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
  (SOME “[Dtype L [([«a»; «b»], «t», [])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type tyname"
  (SOME “[Dtype L [([], «tyname», [])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type ('a,'b) t = B1a | A1b"
  (SOME “[Dtype L [([«a»; «b»], «t», [(«B1a», []); («A1b», [])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type t = Ba1 | Ab1"
  (SOME “[Dtype L [([], «t», [(«Ba1», []); («Ab1», [])])]]”)
  ;

val _ = parsetest0 “nDefinition” “ptree_Definition”
  "type t = z"
  (SOME “[Dtabbrev L [] «t» (Atapp [] (Short «z»))]”)
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
  (SOME “[Dmod «Mod» ([]:dec list)]”)
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
  (SOME “«BadFileName»”)
  ;

val _ = parsetest0 “nConstrName” “ptree_ConstrName”
  "Pp_data"
  (SOME “«PP_Data»”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Text_io.Bad_file_name"
  (SOME “[«TextIO»; «BadFileName»]”)
  ;

val _ = parsetest0 “nConstr” “ptree_Constr”
  "Pretty_printer.Pp_data"
  (SOME “[«PrettyPrinter»; «PP_Data»]”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Text_io"
  (SOME “«TextIO»”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Word8_array"
  (SOME “«Word8Array»”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Command_line"
  (SOME “«CommandLine»”)
  ;

val _ = parsetest0 “nModuleName” “ptree_ModuleName”
  "Pretty_printer"
  (SOME “«PrettyPrinter»”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Pretty_printer.token"
  (SOME “Var (Long «PrettyPrinter» (Short «token»))”)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Pretty_printer.Text_io.stuff"
  (SOME “Var (Long «PrettyPrinter» (Long «TextIO» (Short «stuff»)))”)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Comb (x, y)"
  (SOME “C «Comb» [V «x»; V «y»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Abs (x, y)"
  (SOME “C «Abs» [V «x»; V «y»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Var (x, y)"
  (SOME “C «Var» [V «x»; V «y»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Sequent (x, y)"
  (SOME “C «Sequent» [V «x»; V «y»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Const (x, y)"
  (SOME “C «Const» [V «x»; V «y»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Pretty_printer.Pp_data (x, y)"
  (SOME “Con (SOME (Long «PrettyPrinter» (Short «PP_Data»))) [V «x»; V «y»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Comb (Var (v, s), Const (w, t))"
  (SOME “C «Comb» [C «Var» [V «v»; V «s»]; C «Const» [V «w»; V «t»]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Comb (Var (v, s), Const (w, t))"
  (SOME $ eval “[mkpat $ Pc «Comb» [Pc «Var» [Pv «v»; Pv «s»]; Pc «Const» [Pv «w»; Pv «t»]]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Append (Append (v, s), Append (w, t))"
  (SOME $ eval “[mkpat $  Pc «Append» [Pc «Append» [Pv «v»; Pv «s»];
                            Pc «Append» [Pv «w»; Pv «t»]]]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Append (Append (v, s), Append (w, t))"
  (SOME “C «Append» [C «Append» [V «v»; V «s»];
                     C «Append» [V «w»; V «t»]]”)
  ;

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Var _, Comb _"
  (SOME $ eval “[mkpat $ Pcon NONE [Pc «Var» [Pany; Pany];
                                    Pc «Comb» [Pany; Pany]]]”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "let x = 2 ;; (*CML val x = 5; print \"z\"; fun ref x = Ref x; *)"
  (SOME “[Dlet L1 (Pv «x») (Lit (IntLit 2));
          Dlet L2 (Pv «x») (Lit (IntLit 5));
          Dlet L3 (Pv «it») (App Opapp [V «print»; Lit (StrLit «z»)]);
          Dletrec L4 [(«ref»,«x», App Opref [V «x»])]]”)
  ;

(* 2023-08-16: add support for type annotations on lets bound to a value-name
 * without parenthesis:
 *
 *   let name : type = ...
 *
 * where previously:
 *
 *   let (name : type) = ...
 *
 * was required. (There, "(name : type)" is parsed as a pattern).
 *)

val _ = parsetest0 “nStart” “ptree_Start”
  "let x : int = 2 ;;"
  (SOME “[Dlet L (Pv «x») (Tannot (Lit (IntLit 2)) (Atapp [] (Short «int»)))]”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "let _ = let x : int = 2 in x;;"
  (SOME “[Dlet L Pany
          (Let (SOME «x») (Tannot (Lit (IntLit 2)) (Atapp [] (Short «int»)))
               (Var (Short «x»)))]”)
  ;

val _ = parsetest0 “nStart” “ptree_Start”
  "let (x : int) = 2 ;;"
  (SOME “[Dlet L (Ptannot (Pv «x») (Atapp [] (Short «int»))) (Lit (IntLit 2))]”)
  ;

(* 2023-08-17: add support for OCaml's string and array index shorthands:
 *   string-expr .[ int-expr ]
 *   array-expr .( int-expr )
 *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "!s.[c]"
  (SOME “App Opapp [App Opapp [Var (Long «String» (Short «sub»));
                               App Opapp [V «!»; V «s»]];
                    V «c»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "-  a.( i) + 3"
  (SOME “vbinop (Short «+»)
                (App Opapp [Var (Long «Int» (Short «~»));
                            App Opapp [
                                App Opapp [Var (Long «Array» (Short «sub»));
                                           V «a»];
                                V «i»]])
                (Lit (IntLit 3))”)
  ;

(* 2023-08-17: attempt to deal with let recs/ands without explicit arguments:
 *   let rec f = function | ...
 * is a pattern occurring in the HOL Light code, for example.
 *)

val _ = parsetest0 “nStart” “ptree_Start”
  "let rec f : t = e ;;"
  (SOME “[Dletrec L [(«f»,«», App Opapp [Tannot (V «e») (Atapp [] (Short «t»));
                                         V «»])]]”)
  ;

(* This is a bit strange: OCaml (apparently) supports mixing recursive functions
 * with values, and its parser would generate code that binds g to 3 (as if we
 * would've used a let) but unfortunately our hack must create functions always:
 *)

val _ = parsetest0 “nStart” “ptree_Start”
  "let rec f = e\
  \ and g = 3;;"
  (SOME “[Dletrec L [(«f»,«», App Opapp [V «e»; V «»]);
                     («g», «», App Opapp [Lit (IntLit 3); V «»])]]”)
  ;

(* 2023-08-17: attach - signs to number literals in patterns.
 *)

val _ = parsetest0 “nPattern” “ptree_Pattern”
  "-1"
  (SOME $ eval “[mkpat $ Plit (IntLit (-1))]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "-1"
  (SOME “App Opapp [Var (Long «Int» (Short «~»)); Lit (IntLit 1)]”)
  ;

(* 2023-08-25: Parse .( as two tokens and make sure structure projection of
   parenthesized things works and isn't parsed as array indexing.
 *)

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "a . ( i)"
  (SOME “App Opapp [App Opapp [Var (Long «Array» (Short «sub»)); V «a»];
                               V «i»]”)
  ;

val _ = parsetest0 “nExpr” “ptree_Expr nExpr”
  "Double.(-)"
  (SOME “Var (Long «Double» (Short «-»))”)
  ;

(* 2024-07-25: Pattern constructors applied to pattern constructors *)
val _ = parsetest0 “nPattern” “ptree_Pattern”
  "Some (Some None)"
  (SOME $ eval “[mkpat $  Pc «Some» [Pc «Some» [Pc «None» []]]]”)
  ;

(* 2024-07-27: Parse patterns in function lets properly: require parenthesis
 * around anything below nPBase.
 *)

(* Application of the constructor Some to the variable x: *)
val _ = parsetest0 “nStart” “ptree_Start”
  "let f (Some x) = y"
  (SOME $ eval
   “[Dlet L (Pv «f») (Fun «» (Mat (V«») [(Pc «Some» [Pv «x»], V «y»)]))]”)
  ;

(* A function with two arguments: the first pattern-matching on the constructor
 * Some (with no arguments), and the second, a variable: *)
val _ = parsetest0 “nStart” “ptree_Start”
  "let f Some x = y"
  (SOME $ eval
   “[Dlet L (Pv «f») (Fun «» (Mat (V«») [(Pc «Some» [], Fun «x» (V «y»))]))]”)
  ;

(* This should fail: we require parenthesis around ambiguous patterns here: *)
val _ = expectFailure "FAILED" (fn () =>
  parsetest0 “nExpr” “ptree_Expr nExpr”
  "fun x,y -> z"
  NONE);


(* This should fail: we require parenthesis around ambiguous patterns here: *)
val _ = expectFailure "REMAINING INPUT" (fn () =>
  parsetest0 “nStart” “ptree_Start”
  "let f x,y = z"
  NONE);

(* This is OK though: *)
val _ =
  parsetest0 “nStart” “ptree_Start”
  "let x,y = z"
  NONE;
