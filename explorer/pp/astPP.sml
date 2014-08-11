structure astPP=
struct
open compute_bytecodeLib
open HolKernel boolLib bossLib Parse astTheory terminationTheory
open Portable smpp term_pp_types
open x64DisassembleLib
(*x64DisassembleLib.sig is missing include Abbrev*)

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

val _=temp_add_user_printer ("tmodnoneprint", ``Tmod x NONE xs``,genPrint tmodnonePrint);

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
      
val _=temp_add_user_printer ("tmodsomeprint", ``Tmod x (SOME y) xs``,genPrint tmodsomePrint);


(*TDec*)
fun tdecPrint sys d t pg str brk blk =
  sys (pg,pg,pg) d (strip t);

val _=temp_add_user_printer("tdecprint", ``Tdec x``,genPrint tdecPrint);

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

val _=temp_add_user_printer ("dexnprint", ``Dexn x y``,genPrint (dexnPrint""));

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

val _=temp_add_user_printer ("dtypeprint", ``Dtype x``,genPrint (dtypePrint ""));

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

val _ = temp_add_user_printer ("dtabbrevprint",``Dtabbrev x y z``,genPrint (dtabbrevPrint ));
(*tvar name*)
fun tvarPrint sys d t pg str brk blk =
  str (toString (strip t));

val _=temp_add_user_printer("tvarprint", ``Tvar x``,genPrint tvarPrint);

fun deftypePrint typestr sys d t pg str brk blk=
    str typestr;

(*Fix these names*)
val _=temp_add_user_printer("inttypeprint",``TC_int``,genPrint (deftypePrint "int"));
val _=temp_add_user_printer("stringtypeprint",``TC_string``,genPrint (deftypePrint "string"));
val _=temp_add_user_printer("booltypeprint",``TC_bool``,genPrint (deftypePrint "bool"));
val _=temp_add_user_printer("unittypeprint",``TC_unit``,genPrint (deftypePrint "unit"));
val _=temp_add_user_printer("reftypeprint",``TC_ref``,genPrint (deftypePrint "ref"));
val _=temp_add_user_printer("fntypeprint",``TC_fn``,genPrint (deftypePrint "fn"));
val _=temp_add_user_printer("tuptypeprint",``TC_tup``,genPrint (deftypePrint ""));
val _=temp_add_user_printer("exntypeprint",``TC_exn``,genPrint (deftypePrint "exn"));


(*TC_name*)
fun tcnamelongPrint sys d t pg str brk blk =
  let val (_,t) = dest_comb t
      val (_,[x,y]) = strip_comb t
  in
    str (toString x)>>str".">>str (toString y)
  end;

val _=temp_add_user_printer("tcnamelongprint", ``TC_name (Long x y)``,genPrint tcnamelongPrint);

fun tcnameshortPrint sys d t pg str brk blk =
  str (toString (strip (strip t)));

val _=temp_add_user_printer("tcnameshortprint", ``TC_name (Short x)``,genPrint tcnameshortPrint);

(*Tapp*)
fun tappPrint sys d t pg str brk blk = 
  let val (l,r) = dest_comb t
      val args = #1(listSyntax.dest_list (strip l))
      val sep = if r = ``TC_tup`` then " * " else " , "
      val spa = if r = ``TC_tup`` then "" else " "
  in
    (case args of [] => str"" | (_::_::_) => str"(">>printTuple sep (sys (pg,pg,pg) d) str args >>str ")" >>str spa
     | _ => printTuple sep (sys (pg,pg,pg) d) str args >>str spa)
     >> sys (pg,pg,pg) d r
  end;

val _=temp_add_user_printer("tappprint", ``Tapp x y``,genPrint tappPrint);

(*Tfn*)

fun tfnPrint sys d t pg str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys (pg,pg,pg) d (rand l) >> str " -> " >> sys (pg,pg,pg) d r>>str")"
  end;
  
val _=temp_add_user_printer("tfunprint", ``Tfn x y``,genPrint tfnPrint);


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

val _=temp_add_user_printer ("dletrecprint", ``Dletrec x``, genPrint dletrecPrint);

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

val _=temp_add_user_printer ("letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*Lambdas varN*expr *)
fun lambdaPrint sys d t pg str brk blk = 
  let
    val (_,[name,expr]) = strip_comb t
  in
    blk CONSISTENT 0 (str "(fn ">> str (toString name) >>str" =>">>brk(1,2)>> blk CONSISTENT 0 (sys (pg,pg,pg) (d-1) expr) >> str")")
  end;

val _=temp_add_user_printer ("lambdaprint", ``Fun x y``,genPrint lambdaPrint);

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

val _=temp_add_user_printer ("dletvalprint", ``Dlet x y``,genPrint dletvalPrint);

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

val _=temp_add_user_printer ("letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);

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

val _=temp_add_user_printer ("letnoneprint",``Let NONE x y``,genPrint letnonePrint);

(*Pattern var*)
fun pvarPrint sys d t pg str brk blk =
    str (toString (strip t));

val _=temp_add_user_printer ("pvarprint", ``Pvar x``, genPrint pvarPrint);

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
    
val _=temp_add_user_printer ("pconprint", ``Pcon NONE x``,genPrint pconPrint);
val _=temp_add_user_printer ("conprint", ``Con NONE x``,genPrint pconPrint);

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
    (*Special case for cons and handle long names*)
    val ctor = if (term_to_string ty = "Short") then (let val ctort = toString (hd ls) in 
                                                      (if (ctort = "::") then "Cons" else ctort) end)
               else case ls of [l,r] => (toString l)^"."^(toString r)
    (*Properly handle LONG names*)
  in
    case args of [] => str ctor
    | _ => m_brack str pg (str ctor >> str "(">> (blk INCONSISTENT 0 (printTerms args)) >>str ")")
  end;

val _=temp_add_user_printer ("pconsomeprint", ``Pcon (SOME x) y``,genPrint pconsomePrint);
val _=temp_add_user_printer ("consomeprint", ``Con (SOME x) y``,genPrint pconsomePrint);

(*Special case for list syntax*)

fun pconnilPrint sys d t pg str brk blk = str "[]";

val _=temp_add_user_printer ("pconnilprint",``Con (SOME (Short "nil")) y``,genPrint pconnilPrint);
val _=temp_add_user_printer ("pconnilprint",``Pcon (SOME (Short "nil")) y``,genPrint pconnilPrint);

(*Literals*)
(*Pattern lit*)
fun plitPrint sys d t pg str brk blk=
    sys (pg,pg,pg) (d-1) (strip (strip t));

val _=temp_add_user_printer("plitprint", ``Plit x``, genPrint plitPrint);
val _=temp_add_user_printer ("litprint", ``Lit x``, genPrint plitPrint);

fun unitPrint sys d t pg str brk blk =
  str "()";  

val _=temp_add_user_printer ("unitprint", ``Lit Unit``,genPrint unitPrint);
val _=temp_add_user_printer ("punitprint", ``Plit Unit``,genPrint unitPrint);

(*Short Var name*)
fun varShortPrint sys d t pg str brk blk=
    str (toString (strip (strip t)));

val _=temp_add_user_printer ("varshortprint", ``Var (Short x)``,genPrint varShortPrint);

(*Long Var name*)
fun varLongPrint sys d t pg str brk blk =
  let val t = rand t
      val (_,[l,r]) = strip_comb t
  in
    str (toString l)>> str".">>str(toString r)
  end;

val _=temp_add_user_printer ("varlongprint", ``Var (Long x y)``,genPrint varLongPrint);

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

val _=temp_add_user_printer ("matprint", ``Mat x y``,genPrint matPrint);

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
 
val _=temp_add_user_printer ("oppappprint", ``App Opapp ls``, genPrint oppappPrint);

(*Infix apply*)

fun infixappPrint arithop sys d t pg str brk blk=
  let val (_,ls) = dest_comb t
      val (t::[x]) = #1(listSyntax.dest_list ls)
  in
    sys (Prec(0,"app"),pg,pg) d x >>str" ">> str arithop
  end;

(*Pattern match against lists*)
val _=temp_add_user_printer ("assignappprint", ``App Opapp [Var (Short":="); x]``,genPrint (infixappPrint ":=")); 
val _=temp_add_user_printer ("eqappprint", ``App Opapp [Var (Short"="); x]``,genPrint (infixappPrint "=")); 
val _=temp_add_user_printer ("gteqappprint", ``App Opapp [Var (Short">="); x]``,genPrint (infixappPrint ">=")); 
val _=temp_add_user_printer ("lteqappprint", ``App Opapp [Var (Short"<="); x]``,genPrint (infixappPrint "<=")); 
val _=temp_add_user_printer ("gtappprint", ``App Opapp [Var (Short">"); x]``,genPrint (infixappPrint ">")); 
val _=temp_add_user_printer ("ltappprint", ``App Opapp [Var (Short"<"); x]``,genPrint (infixappPrint "<")); 
val _=temp_add_user_printer ("modappprint", ``App Opapp [Var (Short"mod"); x]``,genPrint (infixappPrint "mod")); 
val _=temp_add_user_printer ("divappprint", ``App Opapp [Var (Short"div"); x]``,genPrint (infixappPrint "div")); 
val _=temp_add_user_printer ("timesappprint", ``App Opapp [Var (Short"*"); x]``,genPrint (infixappPrint "*")); 
val _=temp_add_user_printer ("minusappprint", ``App Opapp [Var (Short"-"); x]``,genPrint (infixappPrint "-")); 
val _=temp_add_user_printer ("addappprint", ``App Opapp [Var (Short"+"); x]``,genPrint (infixappPrint "+")); 

(*raise expr*) 
fun raisePrint sys d t pg str brk blk=
    m_brack str pg (str "raise " >> sys (Top,pg,pg) (d-1) (strip t))

val _=temp_add_user_printer ("raiseprint", ``Raise x``,genPrint raisePrint);

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

val _=temp_add_user_printer ("handleprint", ``Handle x y``,genPrint handlePrint);

(*Logical AND and OR*)
fun logPrint logop sys d t pg str brk blk =
  let
    open Portable smpp
    val (_,[_,x,y]) = strip_comb t
  in
   sys (pg,pg,pg) (d-1) x >> str logop >> sys (pg,pg,pg) (d-1) y
  end;

val _=temp_add_user_printer ("andprint", ``Log And y z``, genPrint (logPrint " andalso "));
val _=temp_add_user_printer ("orprint", ``Log Or y z``, genPrint (logPrint " orelse "));

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

val _=temp_add_user_printer("ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);
 
(*Signatures*)
(*Stype Concrete*)
val _=temp_add_user_printer("stypeprint",``Stype t``,genPrint (dtypePrint ""));
(*Sexn*)
val _=temp_add_user_printer("sexnprint",``Sexn x y``,genPrint (dexnPrint ""));

(*Sval*)
fun svalPrint sys d t pg str brk blk =
  let
    val (_,[v,ty]) = strip_comb t
  in
    add_newline>>str"val ">>str (toString v)>>str " : ">>sys (pg,pg,pg) d ty
  end;

val _=temp_add_user_printer("svalprint",``Sval v t``,genPrint svalPrint);

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

val _=temp_add_user_printer("stypeopqprint",``Stype_opq l t``,genPrint stypeopqPrint);

(*Stabbrev*)
val _ = temp_add_user_printer("stabbrevprint",``Sabbrev x y z``,genPrint (dtabbrevPrint));

(*Booleans*)
fun boolPrint b sys d t pg str brk blk =
  str b;

val _=temp_add_user_printer("truelitprint",``Lit (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("falselitprint",``Lit (Bool F)``,genPrint (boolPrint "false"));

val _=temp_add_user_printer("trueplitprint",``Plit (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("falseplitprint",``Plit (Bool F)``,genPrint (boolPrint "false"));

(*Pretty printer for ast list form, pattern to terms*)
fun astlistPrint sys d t pg str brk blk =
  let val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = sys(pg,pg,pg) d x>>str";"
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;

(*Fixed in latest ver of HOL*)
val _=temp_add_user_printer("astlistprint",``x:prog``,genPrint astlistPrint);

(*TODO: Word8*)

(*TODO: the remainder of this should really go into a miscPP file*)
(*Pretty Printer specifics for globals, types & exceptions*)

fun tidPrinter sys d t pg str brk blk =
  str "datatype " >>str (toString (strip (strip t)));

fun texnPrinter sys d t pg str brk blk = 
  str "exception " >>str (toString (strip (strip t)));

fun tlongPrinter pref sys d t pg str brk blk =
  let val t = rand t
      val(_,[l,r]) = strip_comb t
  in
    str pref >>str" ">> str (toString l) >> str".">>str(toString r)
  end;


val _=temp_add_user_printer("typeidprint",``TypeId (Short x)``, genPrint tidPrinter);
val _=temp_add_user_printer("typeexnprint",``TypeExn (Short x)``, genPrint texnPrinter);


val _=temp_add_user_printer("typelongidprint",``TypeId (Long x y)``, genPrint (tlongPrinter "datatype"));
val _=temp_add_user_printer("typelongexnprint",``TypeExn (Long x y)``, genPrint (tlongPrinter "exception"));


(*Pretty Printer specifics for bytecode*)
fun bclistPrint sys d t pg str brk blk =
  let val t = rand t
      val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = str ((fn s=> if(String.isPrefix "Label" s) then s^":" else "  "^s^"") 
		               (term_to_string x)) >> str"\n"
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;


val _=temp_add_user_printer("bclistprint",``(SOME x ,(y:bc_inst list))``,genPrint bclistPrint);


(*Unlabeled*)
fun ubclistPrint sys d t pg str brk blk =
  let val t = rand t
      val ls = #1(listSyntax.dest_list t)
  fun printterms _ [] = str""
  |   printterms n [x] = str (Int.toString n) >>str":  ">> str (term_to_string x)>>str"\n"
  |   printterms n (x::xs) = (printterms n [x])>>printterms (n+1) xs
  in
    printterms 0 ls
  end;

val _=temp_add_user_printer("ubclistprint",``(NONE ,(y:bc_inst list))``,genPrint ubclistPrint);


(*ASM*)
fun asmPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val ls = x64_disassemble t
    val maxlen = 45 (*x86 inst at most 15 bytes long so leave 45 bytes of space, could probably do with less*)
    fun pad 0 = str""
    |   pad n = str" ">>pad (n-1)
    fun printAsm [] = str""
    |   printAsm (x::xs) = case x of (hex,dis) => 
          (sty [FG DarkGrey] (str hex))>> pad (maxlen - String.size hex) >>str dis>>str"\n">>printAsm xs
    (*Hex dump*)
    (*fun print [] = str""
    |   print (x::xs) = case x of (hex,dis) => str hex>>str" ">>print xs*)
  in
    printAsm ls
  end;
val _=temp_add_user_printer("asmlistprint",``x:word8 list``,asmPrint);
end;
