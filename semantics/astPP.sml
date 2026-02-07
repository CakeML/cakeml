(*
  Pretty printing for CakeML AST
*)
structure astPP=
struct
open HolKernel boolLib bossLib Parse astTheory stringLib
open Portable smpp term_pp_types

(* Bring forward explicitly so that the PP rules don't confuse things*)
fun bring_fwd_ctors ty =
  TypeBase.constructors_of ty
  |> map (fn cn =>
    let val {Thy,Name,...} = dest_thy_const cn in
      Parse.bring_to_front_overload Name {Name=Name,Thy=Thy}
    end)

val _ = bring_fwd_ctors ``:ast$lit``
val _ = bring_fwd_ctors ``:ast$arith``
val _ = bring_fwd_ctors ``:ast$prim_type``
val _ = bring_fwd_ctors ``:('a,'b) namespace$id``
val _ = bring_fwd_ctors ``:ast$op``
val _ = bring_fwd_ctors ``:ast$lop``
(* val _ = bring_fwd_ctors ``:ast$tctor`` *)
(* val _ = bring_fwd_ctors ``:ast$t`` *)
val _ = bring_fwd_ctors ``:ast$pat``
val _ = bring_fwd_ctors ``:ast$exp``
val _ = bring_fwd_ctors ``:ast$dec``
(* val _ = bring_fwd_ctors ``:ast$spec`` *)
(* val _ = bring_fwd_ctors ``:ast$top`` *)

val astPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

(*Control whether lists are printed as Cons(1,Cons...) or in list syntax*)
(*NOT IMPLEMENTED: val prettify_lists = true;*)

fun add_astPP hd = astPrettyPrinters:= (hd:: !astPrettyPrinters)

fun strip t = #2 (dest_comb t);
fun toString s = stringSyntax.fromHOLstring s;

fun wrap_sys sys = fn gravs => fn d => sys {gravs = gravs,depth = d, binderp=false}

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) (pg,lg,rg) d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc (wrap_sys sys) d t pg str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun bracketize str x = str"(">>x>>str")";

fun m_brack str sym b = case sym of (Prec(_,_)) => bracketize str b | _ => b;

fun printTuple sep f str [] = str""
    |   printTuple sep f str [x] = f x
    |   printTuple sep f str (x::xs) = printTuple sep f str [x] >>str sep >> printTuple sep f str xs;

(*Dmod none -- no signatures for now *)
fun dmodnonePrint sys d t pg str brk blk =
  let val (_,[name,decs]) = strip_comb t
      val ls = #1(listSyntax.dest_list decs)
      val printTerms = printTuple "" (sys (pg,pg,pg) d) str
  in
    add_newline>>blk CONSISTENT 0 (str "structure ">>str (toString name)
    >>str" ">>str "=">>add_newline>>
    str "  ">>blk CONSISTENT 2 (str"struct" >> printTerms ls )>>add_newline>>str"  end")
  end;

val _ = add_astPP ("dmodnoneprint", ``Dmod x xs``,genPrint dmodnonePrint);

(*Dmod some
fun dmodsomePrint sys d t pg str brk blk =
  let val (_,[name,opt,decs]) = strip_comb t
      val ls = #1(listSyntax.dest_list decs)
      val printTerms = printTuple "" (sys (pg,pg,pg) d) str
      val opt = #1(listSyntax.dest_list (rand opt))
  in
    add_newline>>blk CONSISTENT 2 (str "structure ">>str (toString name)
    >>str" :>">>brk(1,0)>>(blk CONSISTENT 2 (str"sig">>printTerms opt))>>add_newline>>str "end =">>add_newline>>
    blk CONSISTENT 2 (str"struct" >> printTerms ls )>>add_newline>>str"end")
  end;

val _=add_astPP ("dmodsomeprint", ``Dmod y xs``,genPrint dmodsomePrint);
*)

(*Top level exception decl*)
fun dexnPrint modn sys d t pg str brk blk =
  let
    val (_,[l,x,y]) = strip_comb t
    val args = #1(listSyntax.dest_list y)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (pg,pg,pg) (d-1) x
    |   printTerms (x::xs) = sys (pg,pg,pg) (d-1) x >> str "," >>brk(1,0)>> (printTerms xs);
  in
    add_newline >> str "exception " >> (if(modn="") then str"" else str modn>>str ".") >>str (toString x) >>
    (case args of [] => str ""
    | [x] => str " of ">>printTerms args
    | (_::_) => str " of" >> brk (1,2) >> str "(" >> printTerms args >>str ")")>>str ";"
  end;

val _=add_astPP ("dexnprint", ``Dexn locs x y``,genPrint (dexnPrint""));

(*Top level datatypes list(list tvarN *typeN * list ... ) *)
(*Extra arg at the front for i1 names*)
fun dtypePrint modn sys d t pg str brk blk =
  let
    val ls = strip t
    val dtypelist = #1(listSyntax.dest_list ls);
    fun printCtors [] = str""
    |   printCtors [x] = let
          val (name,ls) = pairSyntax.dest_pair x
          val args = #1(listSyntax.dest_list ls)
          in
            str (toString name) >>
            (case args of [] => str""
            | _ => str " of ">>printTuple " * " (sys (pg,pg,pg) d) str args)
          end
    |   printCtors (x::xs) = printCtors[x] >> add_newline >> str"| ">>(printCtors xs)

    fun printTerms [] = str ""
    |   printTerms [x] = let
          val (params, rest) = pairSyntax.dest_pair x
          val (name, ctors) = pairSyntax.dest_pair rest
          val typaram = #1(listSyntax.dest_list params)
          in
             add_newline>> str "datatype" >> (case typaram of [] => str""
             | (x::y::xs) => str " (">>printTuple " , " (str o toString) str typaram >> str")"
             | _ => str" ">>printTuple " , " (str o toString) str typaram)>>str" "
             >> (if(modn="") then str"" else str modn>>str ".") >> str (toString name)
             >> str" ">>blk CONSISTENT 0 (str "= " >> printCtors (#1(listSyntax.dest_list ctors)))
          end
    |   printTerms (x::xs) = printTerms [x] >> printTerms xs
  in
    printTerms dtypelist >>str ";"
  end;

val _=add_astPP ("dtypeprint", ``Dtype locs x``,genPrint (dtypePrint ""));

fun dtabbrevPrint sys d t pg str brk blk =
  let val (t,[locs,ls,name,typ]) = strip_comb t
      val typaram = #1(listSyntax.dest_list ls)
  in
    add_newline >> str"type" >> (case typaram of [] => str""
             | (x::y::xs) => str " (">>printTuple " , " (str o toString) str typaram >> str")"
             | _ => str" ">>printTuple " , " (str o toString) str typaram)>>str" "
             >> str (toString name)
             >> str" ">>blk CONSISTENT 0 (str "= " >> sys (pg,pg,pg) d typ>>str ";")
  end;

val _ = add_astPP("dtabbrevprint",``Dtabbrev locs x y z``,genPrint (dtabbrevPrint));

(*tvar name*)
fun tvarPrint sys d t pg str brk blk =
  str (toString (strip t));

val _=add_astPP("tvarprint", ``Atvar x``,genPrint tvarPrint);

fun deftypePrint typestr sys d t pg str brk blk=
    str typestr;

(* TODO: Fix these names
val _=add_astPP("inttypeprint",``TC_int``,genPrint (deftypePrint "int"));
val _=add_astPP("chartypeprint",``TC_char``,genPrint (deftypePrint "char"));
val _=add_astPP("stringtypeprint",``TC_string``,genPrint (deftypePrint "string"));
val _=add_astPP("reftypeprint",``TC_ref``,genPrint (deftypePrint "ref"));
val _=add_astPP("fntypeprint",``TC_fn``,genPrint (deftypePrint ""));
val _=add_astPP("tuptypeprint",``TC_tup``,genPrint (deftypePrint ""));
val _=add_astPP("exntypeprint",``TC_exn``,genPrint (deftypePrint "exn"));

(*TC_name*)
fun tcnamelongPrint sys d t pg str brk blk =
  let val (_,t) = dest_comb t
      val (_,[x,sy]) = strip_comb t
      val (_,y) = dest_comb sy
  in
    str (toString x)>>str".">>str (toString y)
  end;

val _=add_astPP("tcnamelongprint", ``TC_name (Long x y)``,genPrint tcnamelongPrint);

fun tcnameshortPrint sys d t pg str brk blk =
  str (toString (strip (strip t)));

val _=add_astPP("tcnameshortprint", ``TC_name (Short x)``,genPrint tcnameshortPrint);

(*Atapp*)
*)
fun tappPrint sys d t pg str brk blk =
  let val (l,r) = dest_comb t
      val args = #1(listSyntax.dest_list (strip l))
      val sep = " , "
                (* if aconv r ``TC_fn``  then " -> " else " , " *)
      val spa = " "
  in
    (case args of [] => str"" | (_::_::_) => str"(">>printTuple sep (sys (pg,pg,pg) d) str args >>str ")" >>str spa
     | _ => printTuple sep (sys (pg,pg,pg) d) str args >>str spa)
     >> sys (pg,pg,pg) d r
  end;

fun ttupPrint sys d t pg str brk blk =
  let val args = #1(listSyntax.dest_list (strip t))
  in
    (case args of
      [] => str"unit"
    | (_::_::_) => str"(">>printTuple " * " (sys (pg,pg,pg) d) str args >>str ")"
    | _ => printTuple " * " (sys (pg,pg,pg) d) str args)
  end;

val _=add_astPP("ttupprint",``Attup xs``,genPrint ttupPrint);
val _=add_astPP("tappprint", ``Atapp x y``,genPrint tappPrint);

(*Tfn*)

fun tfnPrint sys d t pg str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys (pg,pg,pg) d (rand l) >> str " -> " >> sys (pg,pg,pg) d r>>str")"
  end;

val _=add_astPP("tfunprint", ``Tfn x y``,genPrint tfnPrint);

(*return a list of strings*)
fun strip_func funs =
  ((match_term ``Fun x y`` funs);
  let val (_,[name,expr]) = strip_comb funs
      val (names,rest) = strip_func expr in
      (name::names,rest) end)
      handle _ => ([],funs)

fun flat_names str [] = str""
|   flat_names str (x::xs) = str" ">>str (toString x)>>flat_names str xs

(*top level letrec list varN*varN*exp *)
fun dletrecPrint sys d t pg str brk blk =
  let
    val ls = strip t
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] =
        let val (x::y::[z]) = pairSyntax.strip_pair t
            val (names,z) = strip_func z
        in
         blk CONSISTENT ~2 (str (toString x) >> str " ">> str (toString y)>>flat_names str names>> str " =" >> brk(1,0)>> sys (Top,pg,pg) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and " >> (printTerms xs)
  in
    add_newline>>(blk CONSISTENT 0 (str "fun " >> printTerms fundef>>str ";"))
  end;

val _=add_astPP ("dletrecprint", ``Dletrec locs x``, genPrint dletrecPrint);

fun next_is_let body =
      ((match_term ``Let (SOME x) y z`` body; true)
      handle _ => ((match_term ``Letrec x y`` body; true)
                  handle _ => false))

(*Nested mutually recursive letrec*)

fun letrecPrint sys d t pg str brk blk =
  let
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] =
        let val (x::y::[z]) = pairSyntax.strip_pair t
            val (names,z) = strip_func z
        in
          blk CONSISTENT 0 (str (toString x) >> str " ">> str (toString y)>>flat_names str names>> str " =">>brk(1,0) >> sys (Top,pg,pg) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and ">> (printTerms xs)
    val next_is_let = next_is_let expr
    val next_sym = if next_is_let then (Prec(0,"nested_let")) else Top
  in
    case pg of
    (*Skip bracketizing if it is a nested let*)
    (Prec(_,"nested_let")) =>
      (blk CONSISTENT 0 (str "    " >>
      (blk CONSISTENT 0 (str "fun ">>printTerms fundef))
      >>add_newline>>
      (if next_is_let then str"" else str "in">>add_newline>>str"  ")>>
      sys (next_sym,pg,pg) d expr >>
      (if next_is_let then str"" else (add_newline>>str "end"))))
    | _ =>
      m_brack str pg (blk CONSISTENT 0 (str "let " >>
      (blk CONSISTENT 0 (str "fun ">>printTerms fundef))>>add_newline>>
      (if next_is_let then str"" else str "in">>add_newline>>str"  ")>>
      sys (next_sym,pg,pg) d expr >>
      (if next_is_let then str"" else (add_newline>>str "end"))))
  end;

val _=add_astPP ("letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*Lambdas varN*expr *)
fun lambdaPrint sys d t pg str brk blk =
  let
    val (_,[name,expr]) = strip_comb t
  in
    blk CONSISTENT 0 (str "(fn ">> str (toString name) >>str" =>">>brk(1,2)>> blk CONSISTENT 0 (sys (pg,pg,pg) (d-1) expr) >> str")")
  end;

val _=add_astPP ("lambdaprint", ``Fun x y``,genPrint lambdaPrint);

(*Toplevel declaration of a function
  TODO: this is a heuristic that might fail if there's a backreference e.g.
  fun exp ... = ...
  val exp = fn x => ... exp ...
*)
fun dletfunPrint sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,[locs,l,r]) = strip_comb t;
    val (_,[name]) = strip_comb l;
    val (_,[arg,expr]) = strip_comb r;
  in
    add_newline>>blk CONSISTENT 2
    (str "fun " >> str (toString name) >> str " " >> str (toString arg) >> str " = " >> brk (1,0) >>
     sys (Top,pg,pg) (d-1) expr>>str ";")
  end
val _ = add_astPP("dletfunPrint", ``Dlet locs (Pvar x) (Fun y z)``,genPrint dletfunPrint);

(*Toplevel Dlet  pat*expr *)
fun dletvalPrint sys d t pg str brk blk=
  let
    open Portable smpp
    val (_,[locs,l,r]) = strip_comb t;
  in
    add_newline>>blk CONSISTENT 2 (str "val " >>
    sys (pg,pg,pg) (d-1) l >>
    str " =" >> brk (1,0) >> sys (Top,pg,pg) (d-1) r>>str ";")
  end;

val _=add_astPP ("dletvalprint", ``Dlet locs x y``,genPrint dletvalPrint);

(*Inner Let SOME*)
fun letvalPrint sys d t pg str brk blk =
  let
    val (t,body) = dest_comb t
    val (t,eq) = dest_comb t
    val name = toString (strip (strip t))
    val next_is_let = next_is_let body
    val next_sym = if next_is_let then (Prec(0,"nested_let")) else Top
  in
    case pg of
    (*Skip bracketizing if it is a nested let*)
    (Prec(_,"nested_let")) =>
      (blk CONSISTENT 0 (blk CONSISTENT 2(
      str "    val " >>str name >>str" =">>brk(1,0)>>sys (Top,pg,pg) d eq)
      >> add_newline >>
      (if next_is_let then str"" else str"in">>add_newline>>str"  ")>>
      (sys (next_sym,pg,pg) d body) >>
      (if next_is_let then str"" else (add_newline>>str "end"))))
    | _ =>
    m_brack str pg (blk CONSISTENT 0 (blk CONSISTENT 2(
    str "let val " >> str name >>str" =">>brk(1,0)>> sys (Top,pg,pg) d eq)
    >> add_newline >>
    (if next_is_let then str"" else str "in">>add_newline>>str"  ")>>
    (sys (next_sym,pg,pg) d body) >>
    (if next_is_let then str"" else (add_newline>>str "end"))))
  end;

val _=add_astPP ("letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);
(*Inner Let NONE*)
(*This should be sequencing*)
fun letnonePrint sys d t pg str brk blk =
  let val (l,r) = dest_comb t
      val os = blk CONSISTENT 0 ( sys(Prec(0,"letnone"),Top,Top) d (strip l) >>str ";">>
    brk (1,0)>>sys (Prec(0,"letnone"),Top,Top) d r )
  in
     (*Only bracketize if it is not a nested sequence*)
     case pg of Prec(_,"letnone") => os
            |  _ => str"(">>os>>str ")"
  end;

val _=add_astPP ("letnoneprint",``Let NONE x y``,genPrint letnonePrint);

(*Pattern var*)
fun pvarPrint sys d t pg str brk blk =
    str (toString (strip t));

val _=add_astPP ("pvarprint", ``Pvar x``, genPrint pvarPrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
fun pconPrint sys d t pg str brk blk =
  let
    val terms = #1(listSyntax.dest_list (strip t))
  in
    if List.null terms then
      str"()"
    else
    let
      fun printTerms [] = str ""
      |   printTerms [x] = sys (Top,pg,pg) (d-1) x
      |   printTerms (x::xs) = sys (Top,pg,pg) (d-1) x >> str ",">> (printTerms xs);
      val os =blk INCONSISTENT 0 (printTerms terms)
    in
      str"(">>os>>str ")"
    end
  end;

val _=add_astPP ("pconprint", ``Pcon NONE x``,genPrint pconPrint);
val _=add_astPP ("conprint", ``Con NONE x``,genPrint pconPrint);

(*Con SOME*)
fun pconsomePrint sys d t pg str brk blk=
  let
    val (temp,r) = dest_comb t
    val (_,l) = dest_comb temp
    val args = #1(listSyntax.dest_list r)
    (*Stuff in comma sep ctor doesnt need bracketizing*)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,pg,pg) (d-1) x
    |   printTerms (x::xs) = sys (Top,pg,pg) (d-1) x >> str ",">> (printTerms xs);
    val (ty,ls) = strip_comb (rand l);
    val ctor =
      if (term_to_string ty = "Short") then
        toString(hd ls)
      else (case ls of [l,r] => (toString l)^"."^(toString(rand r)))
    (*Properly handle LONG names*)
  in
    case args of [] => str ctor
    | _ => m_brack str pg (str ctor >> str "(">>
           (blk INCONSISTENT 0 (printTerms args)) >>str ")")
  end;

val _=add_astPP ("pconsomeprint", ``Pcon (SOME x) y``,genPrint pconsomePrint);
val _=add_astPP ("consomeprint", ``Con (SOME x) y``,genPrint pconsomePrint);

(*Special case for constructor applied on a tuple
  TODO: Remove once fixed since this makes the code more verbose
*)
fun contupPrint sys d t pg str brk blk=
 let
    val (temp,r) = dest_comb t
    val [r] = #1(listSyntax.dest_list r)
    val (_,l) = dest_comb temp
    val t = ``Let (SOME «x») ^(r) (^(temp) [Var (Short «x»)])``
 in
   letvalPrint sys d t pg str brk blk
 end

val _=add_astPP ("contupprint", ``Con (SOME x) [Con NONE y]``,genPrint contupPrint);

(*Special case for list syntax
check_tail checks whether it is a fully specified list*)
fun check_tail t =
  let val (x,y) = dest_comb t in
    if aconv x ``Con (SOME (Short «nil»))`` then true
    else
      if aconv x ``Con (SOME (Short «::»))`` then
           check_tail (hd (tl (#1(listSyntax.dest_list y))))
    else false
  end;

fun pconconsPrint check_tail sys d t pg str brk blk =
  let
    val (temp,r) = dest_comb t
    val [hd,tl] = #1(listSyntax.dest_list r)
  in
    case pg of
      Prec(_,"full_list") =>
        str "," >> sys(Top,pg,pg) (d-1) hd >> sys(pg,pg,pg) (d-1) tl
    | Prec(_,"non_list") =>
       (*don't think bracketing is necessary here
       m_brack str pg*)
       (sys(Top,pg,pg) (d-1) hd >> str"::" >> sys (pg,pg,pg) (d-1) tl)
    | _ =>
      if check_tail tl then
        str"[">> sys (Top,pg,pg) (d-1) hd >>
        sys (Prec(0,"full_list"),pg,pg) (d-1) tl
      else
        m_brack str pg
        (sys(Top,pg,pg) (d-1) hd >> str"::" >>sys(Prec(0,"non_list"),pg,pg)(d-1) tl)
  end;

val _ = add_astPP("conconsprint",``Con (SOME (Short «::»)) y``,genPrint (pconconsPrint check_tail));
val _ = add_astPP("pconconsprint",``Pcon (SOME (Short «::»)) y``,genPrint (pconconsPrint check_tail));

fun pconnilPrint sys d t pg str brk blk =
  case pg of Prec(0,"full_list") => str"]" | _ => str"[]";

val _=add_astPP ("connilprint",``Con (SOME (Short «nil»)) y``,genPrint pconnilPrint);
val _=add_astPP ("pconnilprint",``Pcon (SOME (Short «nil»)) y``,genPrint pconnilPrint);

(*Literals*)
(*Pattern lit*)
fun plitPrint sys d t pg str brk blk=
    sys (pg,pg,pg) (d-1) (strip (strip t));

val _=add_astPP("plitprint", ``Plit x``, genPrint plitPrint);
val _=add_astPP ("litprint", ``Lit x``, genPrint plitPrint);

(* no special-casing required
fun unitPrint sys d t pg str brk blk =
  str "()";

val _=add_astPP ("unitprint", ``Con NONE []``,genPrint unitPrint);
val _=add_astPP ("punitprint", ``Pcon NONE []``,genPrint unitPrint);
*)

(*Short Var name*)
fun varShortPrint sys d t pg str brk blk=
    str (toString (strip t));

val _=add_astPP ("varshortprint", ``(Short x)``,genPrint varShortPrint);

(*Long Var name*)
fun varLongPrint sys d t pg str brk blk =
  let val (_,[l,sr]) = strip_comb t
      val r = rand sr;
  in
    str (toString l)>> str".">>str(toString r)
  end;

val _=add_astPP ("varlongprint", ``(Long x y)``,genPrint varLongPrint);

fun varPrint sys d t pg str brk blk =
  sys (pg,pg,pg) d (strip t)

val _=add_astPP ("varprint", ``Var x``,genPrint varPrint);

(*Long Var name*)
fun varLongPrint sys d t pg str brk blk =
  let val t = rand t
      val (_,[l,sr]) = strip_comb t
      val r = rand sr;
  in
    str (toString l)>> str".">>str(toString r)
  end;

val _=add_astPP ("varlongprint", ``(Long x y)``,genPrint varLongPrint);


(*Matching*)
fun matPrint sys d t pg str brk blk=
  let
    open Portable smpp
    val (temp,r) = dest_comb t
    val l = #2(dest_comb temp)
    val cases = #1(listSyntax.dest_list r)
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (pg,pg,pg) (d-1) l >> str " => " >> sys (Prec(0,"case"),pg,pg) (d-1) r end;
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>> add_newline>>str"|  ">>(printMatch xs)
  in
    m_brack str pg (blk CONSISTENT 0 (str "case " >> blk CONSISTENT 0 ((sys (Prec(0,"case"),pg,pg) (d-1) l ))>>brk(1,0)>>blk CONSISTENT 0 (str"of ">>printMatch (#1 (listSyntax.dest_list r)))))
  end;

val _=add_astPP ("matprint", ``Mat x y``,genPrint matPrint);

(*Not sure why matching Var A directly fails*)
(*
fun rhs_var var =
      ((match_term ``Var (Short A)`` var ; true)
      handle _ => (match_term ``Var (Long A)`` var; true) handle _ => false)
*)

(*Apply, don't bracketize the LHS of something already in an Apply*)
fun oppappPrint sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,ls) = dest_comb t
    val (hd::[tl]) = #1(listSyntax.dest_list ls) (*Assumes only 1-arg functions*)
    val output = sys (Prec(0,"app2"),pg,pg) d hd >> str" ">>sys (Prec(0,"app"),pg,pg) d tl
  in
    case pg of
      Prec(0,"app2") => output
    | _ => m_brack str pg output
    (*
    case pg of Prec(_,_) => (bracketize str (sys (pg,pg,pg) d f >> str" ">> sys (Top,pg,pg) d x))
         |     _         => (sys (Prec(0,"app"),pg,pg) d f >> str " " >> sys (Prec(0,"app"),pg,pg) d x)*)
  end;

val _=add_astPP ("oppappprint", ``App Opapp ls``, genPrint oppappPrint);

(* special case for deref to avoid the space; almost the same as above *)
fun derefPrint sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,ls) = dest_comb t
    val (_::[tl]) = #1(listSyntax.dest_list ls)
    val output = str"!">>sys (Prec(0,"app"),pg,pg) d tl
  in
    case pg of
      Prec(0,"app2") => output
    | _ => m_brack str pg output
  end;

val _=add_astPP ("derefprint", ``App Opapp [Var(Short «!»); x]``, genPrint derefPrint);


(*Infix apply*)

fun infixappPrint arithop sys d t pg str brk blk=
  let val (_,ls) = dest_comb t
      val (t::[x]) = #1(listSyntax.dest_list ls)
  in
    sys (Prec(0,"app"),pg,pg) d x >>str" ">> str arithop
  end;

fun infixrealPrint arithop sys d t pg str brk blk=
  let val (_,ls) = dest_comb t
      val ([x,y]) = #1(listSyntax.dest_list ls)
  in
    m_brack str pg
    (sys (Prec(0,"app"),pg,pg) d x >>str" ">> str arithop>>str" ">>
    sys (Prec(0,"app"),pg,pg) d y)
  end;

(*Pattern match against lists*)
val _=add_astPP ("assignappprint", ``App Opapp [Var (Short «:=»); x]``,genPrint (infixappPrint ":="));
val _=add_astPP ("eqappprint", ``App Opapp [Var (Short «=»); x]``,genPrint (infixappPrint "="));
val _=add_astPP ("gteqappprint", ``App Opapp [Var (Short «>=»); x]``,genPrint (infixappPrint ">="));
val _=add_astPP ("lteqappprint", ``App Opapp [Var (Short «<=»); x]``,genPrint (infixappPrint "<="));
val _=add_astPP ("gtappprint", ``App Opapp [Var (Short «>»); x]``,genPrint (infixappPrint ">"));
val _=add_astPP ("ltappprint", ``App Opapp [Var (Short «<»); x]``,genPrint (infixappPrint "<"));
val _=add_astPP ("modappprint", ``App Opapp [Var (Short «mod»); x]``,genPrint (infixappPrint "mod"));
val _=add_astPP ("divappprint", ``App Opapp [Var (Short «div»); x]``,genPrint (infixappPrint "div"));
val _=add_astPP ("timesappprint", ``App Opapp [Var (Short «*»); x]``,genPrint (infixappPrint "*"));
val _=add_astPP ("minusappprint", ``App Opapp [Var (Short «-»); x]``,genPrint (infixappPrint "-"));
val _=add_astPP ("addappprint", ``App Opapp [Var (Short «+»); x]``,genPrint (infixappPrint "+"));

(*These are primitive ops that do not appear using the lexer/parser*)

fun prefixargsPrint uop sys d t pg str brk blk =
  let
    val (_,ls) = dest_comb t
    val ls = #1(listSyntax.dest_list ls)
    fun printList [] = str ""
      | printList [x] = str " " >> sys (Prec(0,"app"),pg,pg) d x
      | printList (x::xs) = str " " >> sys (Prec(0,"app"),pg,pg) d x >>str",">> printList xs
  in
    m_brack str pg ( str uop >> str"(" >>printList ls>> str")")
  end;

(*Assignment & References*)
val _=add_astPP ("assignrealprint", ``App Opassign [x;y]``,genPrint (infixrealPrint ":="));
val _=add_astPP ("eqrealprint", ``App Equality [x;y]``,genPrint (infixrealPrint "="));

(*TODO: should the PP rules check for correct arity?
  TODO: bracketing -may be- broken*)
(*For example, these should take lists of 1 element*)
val _=add_astPP ("refrealprint", ``App Opref x``,genPrint (prefixargsPrint "ref"))
val _=add_astPP ("derefrealprint", ``App Opderef x``,genPrint (prefixargsPrint "!"))

val _=add_astPP ("W64toIntprint", ``App (WordToInt W64) x``,genPrint (prefixargsPrint "W64toInt"))
val _=add_astPP ("W8toIntprint", ``App (WordToInt W8) x``,genPrint (prefixargsPrint "W8toInt"))
val _=add_astPP ("W64fromIntprint", ``App (WordFromInt W64) x``,genPrint (prefixargsPrint "W64fromInt"))
val _=add_astPP ("W8fromIntprint", ``App (WordFromInt W8) x``,genPrint (prefixargsPrint "W8fromInt"))

val _=add_astPP ("Opw64Andwprint", ``App (Opw W64 Andw) x``,genPrint (prefixargsPrint "Opw64Andw"))
val _=add_astPP ("Opw8Andwprint", ``App (Opw W8 Andw) x``,genPrint (prefixargsPrint "Opw8Andw"))
val _=add_astPP ("Opw64Orwprint", ``App (Opw W64 Orw) x``,genPrint (prefixargsPrint "Opw64Orw"))
val _=add_astPP ("Opw8Orwprint", ``App (Opw W8 Orw) x``,genPrint (prefixargsPrint "Opw8Orw"))
val _=add_astPP ("Opw64Xorprint", ``App (Opw W64 Xor) x``,genPrint (prefixargsPrint "Opw64Xor"))
val _=add_astPP ("Opw8Xorprint", ``App (Opw W8 Xor) x``,genPrint (prefixargsPrint "Opw8Xor"))
val _=add_astPP ("Opw64Xorprint", ``App (Opw W64 Xor) x``,genPrint (prefixargsPrint "Opw64Xor"))
val _=add_astPP ("Opw8Xorprint", ``App (Opw W8 Xor) x``,genPrint (prefixargsPrint "Opw8Xor"))

(*Opb*)
val _=add_astPP ("gteqrealprint", ``App (Opb Geq) [x;y]``,genPrint (infixrealPrint ">="));
val _=add_astPP ("lteqrealprint", ``App (Opb Leq) [x;y]``,genPrint (infixrealPrint "<="));
val _=add_astPP ("gtrealprint", ``App (Opb Gt) [x;y]``,genPrint (infixrealPrint ">"));
val _=add_astPP ("ltrealprint", ``App (Opb Lt) [x;y]``,genPrint (infixrealPrint "<"));

(*Opn*)
val _=add_astPP ("modrealprint", ``App (Opn Modulo) [x;y]``,genPrint (infixrealPrint "mod"));
val _=add_astPP ("divrealprint", ``App (Opn Divide) [x;y]``,genPrint (infixrealPrint "div"));
val _=add_astPP ("timesrealprint", ``App (Opn Times) [x;y]``,genPrint (infixrealPrint "*"));
val _=add_astPP ("minusrealprint", ``App (Opn Minus) [x;y]``,genPrint (infixrealPrint "-"));
val _=add_astPP ("addrealprint", ``App (Opn Plus) [x;y]``,genPrint (infixrealPrint "+"));

(*Word8Array curried, not checking arity*)
val _=add_astPP ("w8allocrealprint", ``App (Aw8alloc) ls``,genPrint (prefixargsPrint "Word8Array.array"));
val _=add_astPP ("w8subrealprint", ``App (Aw8sub) ls``,genPrint (prefixargsPrint "Word8Array.sub"));
val _=add_astPP ("w8lengthrealprint", ``App (Aw8length) ls``,genPrint (prefixargsPrint "Word8Array.length"));
val _=add_astPP ("w8updaterealprint", ``App (Aw8update) ls``,genPrint (prefixargsPrint "Word8Array.update"));

(* Doubles *)
val _ = add_astPP ("fp_lessequal_print", “App (FP_cmp FP_LessEqual) ls”,
  genPrint (prefixargsPrint "Double.<="));
val _ = add_astPP ("fp_less_print", “App (FP_cmp FP_Less) ls”,
  genPrint (prefixargsPrint "Double.<"));
val _ = add_astPP ("fp_equal_print", “App (FP_cmp FP_Equal) ls”,
  genPrint (prefixargsPrint "Double.="));
val _ = add_astPP ("fp_greater_print", “App (FP_cmp FP_Greater) ls”,
  genPrint (prefixargsPrint "Double.>"));
val _ = add_astPP ("fp_greaterequal_print", “App (FP_cmp FP_GreaterEqual) ls”,
  genPrint (prefixargsPrint "Double.>="));
val _ = map add_astPP [
  ("fp_neg_print", “App (FP_uop FP_Neg) ls”, genPrint (prefixargsPrint "Double.~")),
  ("fp_abs_print", “App (FP_uop FP_Abs) ls”, genPrint (prefixargsPrint "Double.abs")),
  ("fp_sqrt_print", “App (FP_uop FP_Sqrt) ls”, genPrint (prefixargsPrint "Double.sqrt")),
  ("fp_add_print", “App (FP_bop FP_Add) ls”, genPrint (prefixargsPrint "Double.+")),
  ("fp_sub_print", “App (FP_bop FP_Sub) ls”, genPrint (prefixargsPrint "Double.-")),
  ("fp_mul_print", “App (FP_bop FP_Mul) ls”, genPrint (prefixargsPrint "Double.*")),
  ("fp_div_print", “App (FP_bop FP_Div) ls”, genPrint (prefixargsPrint "Double./")),
  ("fp_fma_print", “App (FP_top FP_Fma) ls”, genPrint (prefixargsPrint "Double.FMA"))]

(*Char curried, not checking arity*)

val _=add_astPP ("charordrealprint", ``App Ord ls``,genPrint (prefixargsPrint "Char.ord"));
val _=add_astPP ("charchrrealprint", ``App Chr ls``,genPrint (prefixargsPrint "Char.chr"));
(*I think these are currently prefixes*)

(*String curried, not checking arity*)
val _=add_astPP ("stringimploderealprint", ``App Implode ls``,genPrint (prefixargsPrint "String.implode"));
(*Confusing name??*)
val _=add_astPP ("stringstrlenrealprint", ``App Strlen ls``,genPrint (prefixargsPrint "String.size"));
val _=add_astPP ("stringstrsubrealprint", ``App Strsub ls``,genPrint (prefixargsPrint "String.sub"));
val _=add_astPP ("stringconcatsubrealprint", ``App Strcat ls``,genPrint (prefixargsPrint "String.concat"));


(*Vector curried, not checking arity*)
val _=add_astPP ("vectorvfromlistrealprint", ``App VfromList ls``,genPrint (prefixargsPrint "Vector.fromList"));
val _=add_astPP ("vectorvsubrealprint", ``App Vsub ls``,genPrint (prefixargsPrint "Vector.sub"));
val _=add_astPP ("vectorvlengthrealprint", ``App Vlength ls``,genPrint (prefixargsPrint "Vector.length"));

(*Array curried, not checking arity*)
val _=add_astPP ("arrayAallocrealprint", ``App Aalloc ls``,genPrint (prefixargsPrint "Array.array"));
val _=add_astPP ("arrayAsubrealprint", ``App Asub ls``,genPrint (prefixargsPrint "Array.sub"));
val _=add_astPP ("arrayAlengthrealprint", ``App Alength ls``,genPrint (prefixargsPrint "Array.length"));
val _=add_astPP ("arrayAupdaterealprint", ``App Aupdate ls``,genPrint (prefixargsPrint "Array.update"));

val _=add_astPP ("addappendprint", ``App ListAppend [x;y]``,genPrint (infixrealPrint "@"));

(*End Apps*)

(*raise expr*)
fun raisePrint sys d t pg str brk blk=
    m_brack str pg (str "raise " >> sys (Top,pg,pg) (d-1) (strip t))

val _=add_astPP ("raiseprint", ``Raise x``,genPrint raisePrint);

(*handle expr * list (pat*expr)*)
fun handlePrint sys d t pg str brk blk =
  let
    val (te,pats) = dest_comb t
    val (_, expr) = dest_comb te
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (Top,pg,pg) (d-1) l >> str " => " >> sys (Top,pg,pg) (d-1) r end
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>>add_newline>>str "|      " >> (printMatch xs)
  in
    m_brack str pg (blk CONSISTENT 0 (sys (Prec(0,"handle"),pg,pg) d expr>>brk(1,0)>> (str "handle " >>printMatch (#1 (listSyntax.dest_list pats)))))
  end;

val _=add_astPP ("handleprint", ``Handle x y``,genPrint handlePrint);

(*Logical AND and OR*)
fun logPrint logop sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,[_,x,y]) = strip_comb t
  in
   m_brack str pg (sys (Prec(0,"lop"),pg,pg) (d-1) x >> str logop >> sys (Prec(0,"lop"),pg,pg) (d-1) y)
  end;

val _=add_astPP ("andprint", ``Log Andalso y z``, genPrint (logPrint " andalso "));
val _=add_astPP ("orprint", ``Log Orelse y z``, genPrint (logPrint " orelse "));

(*If-then-else*)
fun ifthenelsePrint sys d t pg str brk blk =
  let
    val (_,[x,y,z]) = strip_comb t
    val os =
      blk CONSISTENT 0 (
      str("if ")  >> (sys (Prec(0,"if"),pg,pg) d x) >>add_newline>>
      str("then ") >> (sys (Prec(0,"if"),pg,pg) d y) >>add_newline>>
      str("else ") >> (sys (Prec(0,"if"),pg,pg) d z) )
    in
      m_brack str pg os
    end

val _=add_astPP("ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);

(* Signatures *)
(*
(*Stype Concrete*)
val _=add_astPP("stypeprint",``Stype t``,genPrint (dtypePrint ""));
(*Sexn*)
val _=add_astPP("sexnprint",``Sexn x y``,genPrint (dexnPrint ""));

(*Sval*)
fun svalPrint sys d t pg str brk blk =
  let
    val (_,[v,ty]) = strip_comb t
  in
    add_newline>>str"val ">>str (toString v)>>str " : ">>sys (pg,pg,pg) d ty>>str ";"
  end;

val _=add_astPP("svalprint",``Sval v t``,genPrint svalPrint);

(*Stype opaque*)
fun stypeopqPrint sys d t pg str brk blk =
  let
    val (_,[ls,ty]) = strip_comb t
    val typaram = #1 (listSyntax.dest_list ls)
  in
    add_newline>>str "type ">>
    (case typaram of [] => str""
                  | (x::y::xs) => str "(">>printTuple " , " (str o toString) str typaram >> str") "
                  | _ => printTuple " , " (str o toString) str typaram >>str" ")
    >>str (toString ty)>>str ";"
  end;

val _ = add_astPP("stypeopqprint",``Stype_opq l t``,genPrint stypeopqPrint);

(*Stabbrev*)
val _ = add_astPP("stabbrevprint",``Stabbrev x y z``,genPrint (dtabbrevPrint));
*)

(*Booleans - no special-casing required
fun boolPrint b sys d t pg str brk blk =
  str b;

val _=add_astPP("truelitprint",``Con (SOME (Short «true»)) []``,genPrint (boolPrint "true"));
val _=add_astPP("falselitprint",``Con (SOME (Short «false»)) []``,genPrint (boolPrint "false"));
*)

(*Pretty printer for ast list form, pattern to terms*)
fun astlistPrint sys d t pg str brk blk =
  let val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = sys(pg,pg,pg) d x
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;

val _=add_astPP("astlistprint",``x:ast$dec list``,genPrint astlistPrint);

fun enable_astPP_verbose () = map temp_add_user_printer (!astPrettyPrinters);
fun enable_astPP () = (enable_astPP_verbose();())
fun disable_astPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!astPrettyPrinters);
fun disable_astPP () = (disable_astPP_verbose();())
(*
enable_astPP_verbose();
disable_astPP_verbose();
``Var(Long "asdf" (Short("asdf")))``
val t = ``Dlet a b c``
``App (Aw8sub) [x;y]``
``App (Aw8length) [x]``
``Dlet a (App Opref [App (Aw8update) [x;y;z]])``
``App Vsub [v1;v2]``
``App Vlength [v1]``
``[App VfromList [as]]``
disable_astPP_verbose();
``Dlet x (App Ord [App Chr [a;b];z])``
*)

end;
