(*Pretty printing for CakeML AST*)
structure astPP=
struct
open HolKernel boolLib bossLib Parse astTheory stringLib
open Portable smpp term_pp_types

val astPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

(*Control whether lists are printed as Cons(1,Cons...) or in list syntax*)
val prettify_lists = true;

fun add_astPP hd = astPrettyPrinters:= (hd:: !astPrettyPrinters)

fun strip t = #2 (dest_comb t);
fun toString s = stringSyntax.fromHOLstring s;

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) (pg,lg,rg) d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc sys d t pg str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun bracketize str x = str"(">>x>>str")";

fun m_brack str sym b = case sym of (Prec(_,_)) => bracketize str b | _ => b;

fun printTuple sep f str [] = str""
    |   printTuple sep f str [x] = f x
    |   printTuple sep f str (x::xs) = printTuple sep f str [x] >>str sep >> printTuple sep f str xs;

(*Tmod none*)
fun tmodnonePrint sys d t pg str brk blk =
  let val (_,[name,opt,decs]) = strip_comb t
      val ls = #1(listSyntax.dest_list decs)
      val printTerms = printTuple "" (sys (pg,pg,pg) d) str
  in
    add_newline>>blk CONSISTENT 0 (str "structure ">>str (toString name) 
    >>str" ">>str "=">>add_newline>>
    str "  ">>blk CONSISTENT 2 (str"struct" >> printTerms ls )>>add_newline>>str"  end")
  end;

val _ = add_astPP ("tmodnoneprint", ``Tmod x NONE xs``,genPrint tmodnonePrint);

(*Tmod some*)
fun tmodsomePrint sys d t pg str brk blk =
  let val (_,[name,opt,decs]) = strip_comb t
      val ls = #1(listSyntax.dest_list decs)
      val printTerms = printTuple "" (sys (pg,pg,pg) d) str
      val opt = #1(listSyntax.dest_list (rand opt))
  in
    add_newline>>blk CONSISTENT 2 (str "structure ">>str (toString name) 
    >>str" :>">>brk(1,0)>>(blk CONSISTENT 2 (str"sig">>printTerms opt))>>add_newline>>str "end =">>add_newline>>
    blk CONSISTENT 2 (str"struct" >> printTerms ls )>>add_newline>>str"end")
  end;
      
val _=add_astPP ("tmodsomeprint", ``Tmod x (SOME y) xs``,genPrint tmodsomePrint);


(*TDec*)
fun tdecPrint sys d t pg str brk blk =
  sys (pg,pg,pg) d (strip t);

val _=add_astPP("tdecprint", ``Tdec x``,genPrint tdecPrint);

(*Top level exception decl*)
fun dexnPrint modn sys d t pg str brk blk =
  let
    val (_,[x,y]) = strip_comb t
    val args = #1(listSyntax.dest_list y)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (pg,pg,pg) (d-1) x
    |   printTerms (x::xs) = sys (pg,pg,pg) (d-1) x >> str "," >>brk(1,0)>> (printTerms xs);
  in 
    add_newline >> str "exception " >> (if(modn="") then str"" else str modn>>str ".") >>str (toString x) >> 
    (case args of [] => str "" 
    | [x] => str " of ">>printTerms args 
    | (_::_) => str " of" >> brk (1,2) >> str "(" >> printTerms args >>str ")")
  end;

val _=add_astPP ("dexnprint", ``Dexn x y``,genPrint (dexnPrint""));

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
    printTerms dtypelist
  end;

val _=add_astPP ("dtypeprint", ``Dtype x``,genPrint (dtypePrint ""));

fun dtabbrevPrint sys d t pg str brk blk =
  let val (t,typ) = dest_comb t
      val (t,name) = dest_comb t
      val (_,ls) = dest_comb t
      val typaram = #1(listSyntax.dest_list ls)
  in
    add_newline >> str"type" >> (case typaram of [] => str"" 
             | (x::y::xs) => str " (">>printTuple " , " (str o toString) str typaram >> str")"
             | _ => str" ">>printTuple " , " (str o toString) str typaram)>>str" "
             >> str (toString name) 
             >> str" ">>blk CONSISTENT 0 (str "= " >> sys (pg,pg,pg) d typ)
  end;

val _ = add_astPP ("dtabbrevprint",``Dtabbrev x y z``,genPrint (dtabbrevPrint ));
(*tvar name*)
fun tvarPrint sys d t pg str brk blk =
  str (toString (strip t));

val _=add_astPP("tvarprint", ``Tvar x``,genPrint tvarPrint);

fun deftypePrint typestr sys d t pg str brk blk=
    str typestr;

(*Fix these names*)
val _=add_astPP("inttypeprint",``TC_int``,genPrint (deftypePrint "int"));
val _=add_astPP("stringtypeprint",``TC_string``,genPrint (deftypePrint "string"));
val _=add_astPP("booltypeprint",``TC_bool``,genPrint (deftypePrint "bool"));
val _=add_astPP("unittypeprint",``TC_unit``,genPrint (deftypePrint "unit"));
val _=add_astPP("reftypeprint",``TC_ref``,genPrint (deftypePrint "ref"));
val _=add_astPP("fntypeprint",``TC_fn``,genPrint (deftypePrint ""));
val _=add_astPP("tuptypeprint",``TC_tup``,genPrint (deftypePrint ""));
val _=add_astPP("exntypeprint",``TC_exn``,genPrint (deftypePrint "exn"));


(*TC_name*)
fun tcnamelongPrint sys d t pg str brk blk =
  let val (_,t) = dest_comb t
      val (_,[x,y]) = strip_comb t
  in
    str (toString x)>>str".">>str (toString y)
  end;

val _=add_astPP("tcnamelongprint", ``TC_name (Long x y)``,genPrint tcnamelongPrint);

fun tcnameshortPrint sys d t pg str brk blk =
  str (toString (strip (strip t)));

val _=add_astPP("tcnameshortprint", ``TC_name (Short x)``,genPrint tcnameshortPrint);

(*Tapp*)
fun tappPrint sys d t pg str brk blk = 
  let val (l,r) = dest_comb t
      val args = #1(listSyntax.dest_list (strip l))
      val sep = if r = ``TC_tup`` then " * " else 
                if r = ``TC_fn``  then " -> " else " , "
      val spa = if r = ``TC_tup`` then "" else " "
  in
    (case args of [] => str"" | (_::_::_) => str"(">>printTuple sep (sys (pg,pg,pg) d) str args >>str ")" >>str spa
     | _ => printTuple sep (sys (pg,pg,pg) d) str args >>str spa)
     >> sys (pg,pg,pg) d r
  end;

val _=add_astPP("tappprint", ``Tapp x y``,genPrint tappPrint);

(*Tfn*)

fun tfnPrint sys d t pg str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys (pg,pg,pg) d (rand l) >> str " -> " >> sys (pg,pg,pg) d r>>str")"
  end;
  
val _=add_astPP("tfunprint", ``Tfn x y``,genPrint tfnPrint);


(*top level letrec list varN*varN*exp *)
fun dletrecPrint sys d t pg str brk blk =
  let
    val ls = strip t
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] = let val (x::y::[z]) = pairSyntax.strip_pair t
        in
         blk CONSISTENT ~2 (str (toString x) >> str " ">> str (toString y)>> str " =" >> brk(1,0)>> sys (pg,pg,pg) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and " >> (printTerms xs)
  in
    add_newline>>(blk CONSISTENT 0 (str "fun " >> printTerms fundef))
  end;

val _=add_astPP ("dletrecprint", ``Dletrec x``, genPrint dletrecPrint);

(*Nested mutually recursive letrec*)

fun letrecPrint sys d t pg str brk blk =
  let
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] = let val (x::y::[z]) = pairSyntax.strip_pair t
        in
          blk CONSISTENT 0 (str (toString x) >> str " ">> str (toString y)
          >> str " =">>brk(1,0) >> sys (Top,pg,pg) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and ">> (printTerms xs)
  in
     m_brack str pg (blk CONSISTENT 0 (str "let " >> (blk CONSISTENT 0 (str "fun ">>printTerms fundef))
     >>add_newline>>str "in">>add_newline>>str"  ">>sys (Top,pg,pg) d expr >>add_newline>> str "end"))
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

(*Toplevel declaration of a function *)
fun dletfunPrint sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,[l,r]) = strip_comb t;
    val (_,[name]) = strip_comb l;
    val (_,[arg,expr]) = strip_comb r;
  in
    add_newline>>blk CONSISTENT 2
    (str "fun " >> str (toString name) >> str " " >> str (toString arg) >> str " = " >> brk (1,0) >>
     sys (pg,pg,pg) (d-1) expr)
  end
val _ = add_astPP("dletfunPrint", ``Dlet (Pvar x) (Fun y z)``,genPrint dletfunPrint);

(*Toplevel Dlet  pat*expr *)
fun dletvalPrint sys d t pg str brk blk=
  let
    open Portable smpp
    val (_,[l,r]) = strip_comb t;
  in
    add_newline>>blk CONSISTENT 2 (str "val " >>
    sys (pg,pg,pg) (d-1) l >>
    str " =" >> brk (1,0) >> sys (pg,pg,pg) (d-1) r)
  end;

val _=add_astPP ("dletvalprint", ``Dlet x y``,genPrint dletvalPrint);

(*Inner Let SOME*)
fun letvalPrint sys d t pg str brk blk =
  let
    val (t,body) = dest_comb t
    val (t,eq) = dest_comb t
    val name = toString (strip (strip t))
  in
    m_brack str pg (blk CONSISTENT 0 (blk CONSISTENT 2(str "let val " >> str name >>str" =">>brk(1,0)>> sys (Top,pg,pg) d eq)
    >> add_newline >> str "in">>add_newline >> str"  ">>(sys (Top,pg,pg) d body) >>add_newline>>str"end"))
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
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,pg,pg) (d-1) x
    |   printTerms (x::xs) = sys (Top,pg,pg) (d-1) x >> str ",">> (printTerms xs);
    val terms = #1(listSyntax.dest_list (strip t))
    val os =blk INCONSISTENT 0 (printTerms terms)
    in
      str"(">>os>>str ")"
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
      else (case ls of [l,r] => (toString l)^"."^(toString r))
    (*Properly handle LONG names*)
  in
    case args of [] => str ctor
    | _ => m_brack str pg (str ctor >> str "(">> 
           (blk INCONSISTENT 0 (printTerms args)) >>str ")")
  end;

val _=add_astPP ("pconsomeprint", ``Pcon (SOME x) y``,genPrint pconsomePrint);
val _=add_astPP ("consomeprint", ``Con (SOME x) y``,genPrint pconsomePrint);

(*Special case for list syntax 
check_tail checks whether it is a fully specified list*)
fun check_tail t =
  let val (x,y) = dest_comb t in
    if x = ``Con (SOME (Short "nil"))`` then true
    else 
      if x = ``Con (SOME (Short "::"))`` then
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
        sys(Top,pg,pg) (d-1) hd >> str"::" >> sys (pg,pg,pg) (d-1) tl
    | _ => 
      if check_tail tl then 
        str"[">> sys (Top,pg,pg) (d-1) hd >> 
        sys (Prec(0,"full_list"),pg,pg) (d-1) tl
      else sys(Top,pg,pg) (d-1) hd >> str"::" >>
           sys(Prec(0,"non_list"),pg,pg)(d-1) tl
  end;

val _ = add_astPP("conconsprint",``Con (SOME (Short"::")) y``,genPrint (pconconsPrint check_tail));
val _ = add_astPP("pconconsprint",``Pcon (SOME (Short"::")) y``,genPrint (pconconsPrint check_tail));

fun pconnilPrint sys d t pg str brk blk = 
  case pg of Prec(0,"full_list") => str"]" | _ => str"[]";

val _=add_astPP ("connilprint",``Con (SOME (Short "nil")) y``,genPrint pconnilPrint);
val _=add_astPP ("pconnilprint",``Pcon (SOME (Short "nil")) y``,genPrint pconnilPrint);

(*Literals*)
(*Pattern lit*)
fun plitPrint sys d t pg str brk blk=
    sys (pg,pg,pg) (d-1) (strip (strip t));

val _=add_astPP("plitprint", ``Plit x``, genPrint plitPrint);
val _=add_astPP ("litprint", ``Lit x``, genPrint plitPrint);

fun unitPrint sys d t pg str brk blk =
  str "()";  

val _=add_astPP ("unitprint", ``Lit Unit``,genPrint unitPrint);
val _=add_astPP ("punitprint", ``Plit Unit``,genPrint unitPrint);

(*Short Var name*)
fun varShortPrint sys d t pg str brk blk=
    str (toString (strip (strip t)));

val _=add_astPP ("varshortprint", ``Var (Short x)``,genPrint varShortPrint);

(*Long Var name*)
fun varLongPrint sys d t pg str brk blk =
  let val t = rand t
      val (_,[l,r]) = strip_comb t
  in
    str (toString l)>> str".">>str(toString r)
  end;

val _=add_astPP ("varlongprint", ``Var (Long x y)``,genPrint varLongPrint);

(*Matching*)
fun matPrint sys d t pg str brk blk=
  let
    open Portable smpp
    val (temp,r) = dest_comb t
    val l = #2(dest_comb temp)
    val cases = #1(listSyntax.dest_list r)
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (pg,pg,pg) (d-1) l >> str " => " >> sys (Top,pg,pg) (d-1) r end;
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>> add_newline>>str"|  ">>(printMatch xs) 
  in
    m_brack str pg (blk CONSISTENT 0 (str "case " >> blk CONSISTENT 0 ((sys (Prec(0,"case"),pg,pg) (d-1) l ))>>brk(1,0)>>blk CONSISTENT 0 (str"of ">>printMatch (#1 (listSyntax.dest_list r))))) 
  end;

val _=add_astPP ("matprint", ``Mat x y``,genPrint matPrint);

(*Apply*)
fun oppappPrint sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,ls) = dest_comb t
    val (hd::[tl]) = #1(listSyntax.dest_list ls) (*Assumes only 1-arg functions*)
  in
    m_brack str pg (sys (Prec(0,"app"),pg,pg) d hd >> str" ">>sys (Prec(0,"app"),pg,pg) d tl)
    (*
    case pg of Prec(_,_) => (bracketize str (sys (pg,pg,pg) d f >> str" ">> sys (Top,pg,pg) d x))
         |     _         => (sys (Prec(0,"app"),pg,pg) d f >> str " " >> sys (Prec(0,"app"),pg,pg) d x)*)
  end;
 
val _=add_astPP ("oppappprint", ``App Opapp ls``, genPrint oppappPrint);

(*Infix apply*)

fun infixappPrint arithop sys d t pg str brk blk=
  let val (_,ls) = dest_comb t
      val (t::[x]) = #1(listSyntax.dest_list ls)
  in
    sys (Prec(0,"app"),pg,pg) d x >>str" ">> str arithop
  end;

(*Pattern match against lists*)
val _=add_astPP ("assignappprint", ``App Opapp [Var (Short":="); x]``,genPrint (infixappPrint ":=")); 
val _=add_astPP ("eqappprint", ``App Opapp [Var (Short"="); x]``,genPrint (infixappPrint "=")); 
val _=add_astPP ("gteqappprint", ``App Opapp [Var (Short">="); x]``,genPrint (infixappPrint ">=")); 
val _=add_astPP ("lteqappprint", ``App Opapp [Var (Short"<="); x]``,genPrint (infixappPrint "<=")); 
val _=add_astPP ("gtappprint", ``App Opapp [Var (Short">"); x]``,genPrint (infixappPrint ">")); 
val _=add_astPP ("ltappprint", ``App Opapp [Var (Short"<"); x]``,genPrint (infixappPrint "<")); 
val _=add_astPP ("modappprint", ``App Opapp [Var (Short"mod"); x]``,genPrint (infixappPrint "mod")); 
val _=add_astPP ("divappprint", ``App Opapp [Var (Short"div"); x]``,genPrint (infixappPrint "div")); 
val _=add_astPP ("timesappprint", ``App Opapp [Var (Short"*"); x]``,genPrint (infixappPrint "*")); 
val _=add_astPP ("minusappprint", ``App Opapp [Var (Short"-"); x]``,genPrint (infixappPrint "-")); 
val _=add_astPP ("addappprint", ``App Opapp [Var (Short"+"); x]``,genPrint (infixappPrint "+")); 

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
   sys (pg,pg,pg) (d-1) x >> str logop >> sys (pg,pg,pg) (d-1) y
  end;

val _=add_astPP ("andprint", ``Log And y z``, genPrint (logPrint " andalso "));
val _=add_astPP ("orprint", ``Log Or y z``, genPrint (logPrint " orelse "));

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
 
(*Signatures*)
(*Stype Concrete*)
val _=add_astPP("stypeprint",``Stype t``,genPrint (dtypePrint ""));
(*Sexn*)
val _=add_astPP("sexnprint",``Sexn x y``,genPrint (dexnPrint ""));

(*Sval*)
fun svalPrint sys d t pg str brk blk =
  let
    val (_,[v,ty]) = strip_comb t
  in
    add_newline>>str"val ">>str (toString v)>>str " : ">>sys (pg,pg,pg) d ty
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
    >>str (toString ty)
  end;

val _=add_astPP("stypeopqprint",``Stype_opq l t``,genPrint stypeopqPrint);

(*Stabbrev*)
val _ = add_astPP("stabbrevprint",``Sabbrev x y z``,genPrint (dtabbrevPrint));

(*Booleans*)
fun boolPrint b sys d t pg str brk blk =
  str b;

val _=add_astPP("truelitprint",``Lit (Bool T)``,genPrint (boolPrint "true"));
val _=add_astPP("falselitprint",``Lit (Bool F)``,genPrint (boolPrint "false"));

val _=add_astPP("trueplitprint",``Plit (Bool T)``,genPrint (boolPrint "true"));
val _=add_astPP("falseplitprint",``Plit (Bool F)``,genPrint (boolPrint "false"));

(*Pretty printer for ast list form, pattern to terms*)
fun astlistPrint sys d t pg str brk blk =
  let val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = sys(pg,pg,pg) d x>>str";"
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;

val _=add_astPP("astlistprint",``x:prog``,genPrint astlistPrint);

(*TODO: Word8*)

fun enable_astPP_verbose () = map temp_add_user_printer (!astPrettyPrinters); 
fun enable_astPP () = (enable_astPP_verbose();())
fun disable_astPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!astPrettyPrinters);
fun disable_astPP () = (disable_astPP_verbose();())

(*
enable_astPP_verbose();
``Var(Long "asdf" "asdf")``
disable_astPP_verbose();
*)

end;
