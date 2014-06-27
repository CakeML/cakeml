structure astPP=
struct
open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib 
open Portable smpp

fun strip t = #2 (dest_comb t);
fun toString s = stringSyntax.fromHOLstring s;

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc sys d t Top str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

fun printTuple sep f str [] = str""
    |   printTuple sep f str [x] = f x
    |   printTuple sep f str (x::xs) = printTuple sep f str [x] >>str sep >> printTuple sep f str xs;

(*Tmod none*)
fun tmodnonePrint sys d t Top str brk blk =
  let val (_,[name,opt,decs]) = strip_comb t
      val ls = #1(listSyntax.dest_list decs)
      val printTerms = printTuple "" (sys (Top,Top,Top) d) str
  in
    add_newline>>blk CONSISTENT 0 (str "structure ">>str (toString name) 
    >>str" ">>str "=">>add_newline>>
    str "  ">>blk CONSISTENT 2 (str"struct" >> printTerms ls )>>add_newline>>str"  end")
  end;

val _=temp_add_user_printer ("tmodnoneprint", ``Tmod x NONE xs``,genPrint tmodnonePrint);

(*Tmod some*)
fun tmodsomePrint sys d t Top str brk blk =
  let val (_,[name,opt,decs]) = strip_comb t
      val ls = #1(listSyntax.dest_list decs)
      val printTerms = printTuple "" (sys (Top,Top,Top) d) str
      val opt = #1(listSyntax.dest_list (rand opt))
  in
    add_newline>>blk CONSISTENT 2 (str "structure ">>str (toString name) 
    >>str" :>">>brk(1,0)>>(blk CONSISTENT 2 (str"sig">>printTerms opt))>>add_newline>>str "end =">>add_newline>>
    blk CONSISTENT 2 (str"struct" >> printTerms ls )>>add_newline>>str"end")
  end;
      
val _=temp_add_user_printer ("tmodsomeprint", ``Tmod x (SOME y) xs``,genPrint tmodsomePrint);


(*TDec*)
fun tdecPrint sys d t Top str brk blk =
  sys (Top,Top,Top) (d-1) (strip t);

val _=temp_add_user_printer("tdecprint", ``Tdec x``,genPrint tdecPrint);

(*Top level exceptions*)
fun dexnPrint modn sys d t Top str brk blk =
  let
    val (_,[x,y]) = strip_comb t
    val args = #1(listSyntax.dest_list y)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >>brk(1,0)>> (printTerms xs);
  in 
    add_newline >> str "exception " >> (if(modn="") then str"" else str modn>>str ".") >>str (toString x) >> 
    (case args of [] => str "" 
    | [x] => str " of ">>printTerms args 
    | (_::_) => str " of" >> brk (1,2) >> str "(" >> printTerms args >>str ")")
  end;

val _=temp_add_user_printer ("dexnprint", ``Dexn x y``,genPrint (dexnPrint""));

(*TODO: LHS tuples should be ('a,'b ,'c) and RHS tuples should be ('a*'b*'c) probably requires rewrite*)
(*Top level datatypes list(list tvarN *typeN * list ... ) *)
(*Extra arg at the front for i1 names*)
fun dtypePrint modn sys d t Top str brk blk =
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
            | _ => str " of ">>printTuple " * " (sys (Top,Top,Top) d) str args)
          end
    |   printCtors (x::xs) = printCtors[x] >> add_newline >> str"| ">>(printCtors xs)

    fun printTerms [] = str ""
    |   printTerms [x] = let
          val (params, rest) = pairSyntax.dest_pair x
          val (name, ctors) = pairSyntax.dest_pair rest
          val typaram = #1(listSyntax.dest_list params)
          in
             add_newline>> str "datatype" >> (case typaram of [] => str"" 
             | (x::y::xs) => str " (">>printTuple "," (str o toString) str typaram >> str") "
             | _ => str" ">>printTuple "," (str o toString) str typaram)>>str" "
             >> (if(modn="") then str"" else str modn>>str ".") >> str (toString name) 
             >> str" ">>blk CONSISTENT 0 (str "= " >> printCtors (#1(listSyntax.dest_list ctors)))
          end
    |   printTerms (x::xs) = printTerms [x] >> printTerms xs
  in
    printTerms dtypelist
  end;

val _=temp_add_user_printer ("dtypeprint", ``Dtype x``,genPrint (dtypePrint ""));

(*tvar name*)
fun tvarPrint sys d t Top str brk blk =
  str (toString (strip t));

val _=temp_add_user_printer("tvarprint", ``Tvar x``,genPrint tvarPrint);

fun deftypePrint typestr sys d t Top str brk blk=
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
fun tcnamePrint sys d t Top str brk blk =
  str (toString (strip (strip t)));

val _=temp_add_user_printer("tcnameprint", ``TC_name x``,genPrint tcnamePrint);

(*Tapp*)
fun tappPrint sys d t Top str brk blk = 
  let val (l,r) = dest_comb t
      val args = #1(listSyntax.dest_list (strip l))
  in
    (case args of [] => str"" | (_::_::_) => str"(">>printTuple "," (sys (Top,Top,Top) d) str args >>str ")"
     | _ => printTuple "," (sys (Top,Top,Top) d) str args >> str" ")  >> sys (Top,Top,Top) d r
  end;

val _=temp_add_user_printer("tappprint", ``Tapp x y``,genPrint tappPrint);

(*Tfn*)

fun tfnPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys (Top,Top,Top) d (rand l) >> str "->" >> sys (Top,Top,Top) d r>>str")"
  end;
  
val _=temp_add_user_printer("tfunprint", ``Tfn x y``,genPrint tfnPrint);


(*Top level letrec list varN*varN*exp *)
fun dletrecPrint sys d t Top str brk blk =
  let
    val ls = strip t
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] = let val (x::y::[z]) = pairSyntax.strip_pair t
        in
         blk CONSISTENT ~2 (str (toString x) >> str " ">> str (toString y)>> str " =" >> brk(1,0)>> sys (Top,Top,Top) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and " >> (printTerms xs)
  in
    add_newline>>(blk CONSISTENT 0 (str "fun " >> printTerms fundef))
  end;

val _=temp_add_user_printer ("dletrecprint", ``Dletrec x``, genPrint dletrecPrint);

(*Nested mutually recursive letrec*)

fun letrecPrint sys d t Top str brk blk =
  let
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] = let val (x::y::[z]) = pairSyntax.strip_pair t
        in
          blk CONSISTENT 0 (str (toString x) >> str " ">> str (toString y)
          >> str " =">>brk(1,0) >> sys (Top,Top,Top) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and ">> (printTerms xs)
  in
     blk CONSISTENT 0 (str "let " >> (blk CONSISTENT 0 (str "fun ">>printTerms fundef))
     >>add_newline>>str "in">>add_newline>>str"  ">>sys (Top,Top,Top) d expr >>add_newline>> str "end")
  end;

val _=temp_add_user_printer ("letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*Lambdas varN*expr *)
fun lambdaPrint sys d t Top str brk blk = 
  let
    val (_,[name,expr]) = strip_comb t
  in
    blk CONSISTENT 0 (str "(fn ">> str (toString name) >>str" =>">>brk(1,2)>> blk CONSISTENT 0 (sys (Top,Top,Top) (d-1) expr) >> str")")
  end;

val _=temp_add_user_printer ("lambdaprint", ``Fun x y``,genPrint lambdaPrint);

(*Toplevel Dlet  pat*expr *)
fun dletvalPrint sys d t Top str brk blk=
  let
    open Portable smpp
    val (_,[l,r]) = strip_comb t;
  in
    add_newline>>blk CONSISTENT 2 (str "val " >>
    sys (Top,Top,Top) (d-1) l >>
    str " =" >> brk (1,0) >> sys (Top,Top,Top) (d-1) r)
  end;

val _=temp_add_user_printer ("dletvalprint", ``Dlet x y``,genPrint dletvalPrint);

(*Inner Let SOME*)
fun letvalPrint sys d t Top str brk blk =
  let
    val (t,body) = dest_comb t
    val (t,eq) = dest_comb t
    val name = toString (strip (strip t))
  in
    blk CONSISTENT 0 (blk CONSISTENT 2(str "let val " >> str name >>str" =">>brk(1,0)>> sys (Top,Top,Top) d eq)
    >> add_newline >> str "in">>add_newline >> str"  ">>(sys (Top,Top,Top) d body) >>add_newline>>str"end")
  end;

val _=temp_add_user_printer ("letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);

(*Inner Let NONE*)

fun letnonePrint sys d t Top str brk blk =
  let
    val (t,body) = dest_comb t
    val (t,eq) = dest_comb t
  in
    blk CONSISTENT 0 (
    str "let val _ = " >> (sys (Top,Top,Top) d eq) >> add_newline 
    >> str"in" >> add_newline>>  str"  ">>(sys (Top,Top,Top) d body) >> add_newline
    >> str"end" )
  end;

val _=temp_add_user_printer ("letnoneprint", ``Let NONE x y``, genPrint letnonePrint);

(*Pattern var*)
fun pvarPrint sys d t Top str brk blk =
    str (toString (strip t));

val _=temp_add_user_printer ("pvarprint", ``Pvar x``, genPrint pvarPrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
fun pconPrint sys d t Top str brk blk =
  let
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str ",">> (printTerms xs);
    val terms = #1(listSyntax.dest_list (strip t))
  in
    str "(" >> (blk INCONSISTENT 0 (printTerms terms) )>>str ")"
  end;
    
val _=temp_add_user_printer ("pconprint", ``Pcon NONE x``,genPrint pconPrint);
val _=temp_add_user_printer ("conprint", ``Con NONE x``,genPrint pconPrint);

(*Con SOME*)
fun pconsomePrint sys d t Top str brk blk=
  let
    val (temp,r) = dest_comb t
    val (_,l) = dest_comb temp
    val args = #1(listSyntax.dest_list r)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str ",">> (printTerms xs);
    val (ty,ls) = strip_comb (rand l);
    (*Special case for cons and handle long names*)
    val ctor = if (term_to_string ty = "Short") then (let val ctort = toString (hd ls) in 
                                                      (if (ctort = "::") then "Cons" else ctort) end)
               else case ls of [l,r] => (toString l)^"."^(toString r)
    (*Properly handle LONG names*)
  in
    str ctor >> (case args of [] => str "" | (_::_) => str "(" >> (blk INCONSISTENT 0 (printTerms args)) >>str ")")
  end;

val _=temp_add_user_printer ("pconsomeprint", ``Pcon (SOME x) y``,genPrint pconsomePrint);
val _=temp_add_user_printer ("consomeprint", ``Con (SOME x) y``,genPrint pconsomePrint);

(*Special case for list syntax*)

fun pconnilPrint sys d t Top str brk blk = str "[]";

val _=temp_add_user_printer ("pconnilprint",``Con (SOME (Short "nil")) y``,genPrint pconnilPrint);
val _=temp_add_user_printer ("pconnilprint",``Pcon (SOME (Short "nil")) y``,genPrint pconnilPrint);

(*Literals*)
(*Pattern lit*)
fun plitPrint sys d t Top str brk blk=
    sys (Top,Top,Top) (d-1) (strip (strip t));

val _=temp_add_user_printer("plitprint", ``Plit x``, genPrint plitPrint);
val _=temp_add_user_printer ("litprint", ``Lit x``, genPrint plitPrint);

fun unitPrint sys d t Top str brk blk =
  str "()";  

val _=temp_add_user_printer ("unitprint", ``Lit Unit``,genPrint unitPrint);
val _=temp_add_user_printer ("punitprint", ``Plit Unit``,genPrint unitPrint);

(*Short Var name*)
fun varShortPrint sys d t Top str brk blk=
    str (toString (strip (strip t)));

val _=temp_add_user_printer ("varshortprint", ``Var (Short x)``,genPrint varShortPrint);

(*Long Var name*)
fun varLongPrint sys d t Top str brk blk =
  let val t = rand t
      val (_,[l,r]) = strip_comb t
  in
    str (toString l)>> str".">>str(toString r)
  end;

val _=temp_add_user_printer ("varlongprint", ``Var (Long x y)``,genPrint varLongPrint);

(*Matching*)
fun matPrint sys d t Top str brk blk=
  let
    open Portable smpp
    val (temp,r) = dest_comb t
    val l = #2(dest_comb temp)
    val cases = #1(listSyntax.dest_list r)
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (Top,Top,Top) (d-1) l >> str " => " >> sys (Top,Top,Top) (d-1) r end;
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>> add_newline>>str"|  ">>(printMatch xs) 
  in
    blk CONSISTENT 0 (str "case (" >> blk CONSISTENT 0 ((sys (Top,Top,Top) (d-1) l ))>> str ")">>brk(1,0)>>blk CONSISTENT 0 (str"of ">>printMatch (#1 (listSyntax.dest_list r)))) 
  end;

val _=temp_add_user_printer ("matprint", ``Mat x y``,genPrint matPrint);

(*Apply with list args*)
fun oppappPrint sys d t Top str brk blk =
  let
    open Portable smpp
    val (_,ls) = dest_comb t
    val (hd::tl) = #1(listSyntax.dest_list ls)
    (*TODO: How are args passed, check it out?? ( a , b , c)? or curried?*)
    fun printTerms [] = str""
    |   printTerms [x] = sys (Top,Top,Top) d x
    |   printTerms (x::xs) = printTerms [x] >> str" ">>printTerms xs
  in
    str "(" >> sys (Top,Top,Top) (d-1) hd >> str " ">> printTerms tl >> str ")"
  end;
 
val _=temp_add_user_printer ("oppappprint", ``App Opapp ls``, genPrint oppappPrint);

(*Infix apply*)

fun infixappPrint arithop sys d t Top str brk blk=
  let val (_,ls) = dest_comb t
      val (t::[y]) = #1(listSyntax.dest_list ls)
      val (_,ls) = dest_comb t
      val(_::[x]) = #1(listSyntax.dest_list ls)
  in
    str"(">>sys (Top,Top,Top) d x>>str" ">> str arithop>>str" ">>sys (Top,Top,Top) d y>>str")"
  end;

(*More icky to do binops in word8, need to match the full apply to both args*)
val _=temp_add_user_printer ("assignappprint", ``App Opapp [App Opapp [Var (Short":="); x];y]``,genPrint (infixappPrint ":=")); 
val _=temp_add_user_printer ("eqappprint", ``App Opapp [App Opapp [Var (Short"="); x];y]``,genPrint (infixappPrint "="));
val _=temp_add_user_printer ("gteqappprint", ``App Opapp [App Opapp [Var (Short">="); x];y]``,genPrint (infixappPrint ">=")); 
val _=temp_add_user_printer ("lteqappprint", ``App Opapp [App Opapp [Var (Short"<="); x];y]``,genPrint (infixappPrint "<=")); 
val _=temp_add_user_printer ("gtappprint", ``App Opapp [App Opapp [Var (Short">"); x];y]``,genPrint (infixappPrint ">")); 
val _=temp_add_user_printer ("ltappprint", ``App Opapp [App Opapp [Var (Short"<"); x];y]``,genPrint (infixappPrint "<")); 
val _=temp_add_user_printer ("modappprint", ``App Opapp [App Opapp [Var (Short"mod"); x];y]``,genPrint (infixappPrint "mod")); 
val _=temp_add_user_printer ("divappprint", ``App Opapp [App Opapp [Var (Short"div"); x];y]``,genPrint (infixappPrint "div")); 
val _=temp_add_user_printer ("timesappprint", ``App Opapp [App Opapp [Var (Short"*"); x];y]``,genPrint (infixappPrint "*")); 
val _=temp_add_user_printer ("minusappprint", ``App Opapp [App Opapp [Var (Short"-"); x];y]``,genPrint (infixappPrint "-")); 
val _=temp_add_user_printer ("addappprint", ``App Opapp [App Opapp [Var (Short"+"); x];y]``,genPrint (infixappPrint "+")); 

(*raise expr*) 
fun raisePrint sys d t Top str brk blk=
  let
    open Portable smpp
  in
    str "raise " >> sys (Top,Top,Top) (d-1) (strip t)
  end;

val _=temp_add_user_printer ("raiseprint", ``Raise x``,genPrint raisePrint);

(*handle expr * list (pat*expr)*)
fun handlePrint sys d t Top str brk blk =
  let
    open Portable smpp
    val (te,pats) = dest_comb t
    val (_, expr) = dest_comb te
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (Top,Top,Top) (d-1) l >> str " => " >> sys (Top,Top,Top) (d-1) r end
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>>add_newline>>str "|      " >> (printMatch xs) 
  in
    str "(" >> sys (Top,Top,Top) (d-1) expr >> str ")">>brk(1,0)>>blk CONSISTENT 0 (str "handle " >>printMatch (#1 (listSyntax.dest_list pats)))
  end;

val _=temp_add_user_printer ("handleprint", ``Handle x y``,genPrint handlePrint);

(*Logical AND and OR*)
fun logPrint logop sys d t Top str brk blk =
  let
    open Portable smpp
    val (_,[_,x,y]) = strip_comb t
  in
   sys (Top,Top,Top) (d-1) x >> str logop >> sys (Top,Top,Top) (d-1) y
  end;

val _=temp_add_user_printer ("andprint", ``Log And y z``, genPrint (logPrint " andalso "));
val _=temp_add_user_printer ("orprint", ``Log Or y z``, genPrint (logPrint " orelse "));

(*If-then-else*)
fun ifthenelsePrint sys d t Top str brk blk = 
  let
    val (_,[x,y,z]) = strip_comb t
  in
    blk CONSISTENT 0 (
    str("if (")  >> (sys (Top,Top,Top) d x) >>str(")")>>add_newline>>
    str("then (") >> (sys (Top,Top,Top) d y) >>str(")")>>add_newline>>
    str("else (") >> (sys (Top,Top,Top) d z) >>str(")"))
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _=temp_add_user_printer("ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);
 
(*Signatures*)
(*Stype Concrete*)
val _=temp_add_user_printer("stypeprint",``Stype t``,genPrint (dtypePrint ""));
(*Sexn*)
val _=temp_add_user_printer("sexnprint",``Sexn x y``,genPrint (dexnPrint ""));

(*Sval*)
fun svalPrint sys d t Top str brk blk =
  let
    val (_,[v,ty]) = strip_comb t
  in
    add_newline>>str"val ">>str (toString v)>>str " : ">>sys (Top,Top,Top) d ty
  end;

val _=temp_add_user_printer("svalprint",``Sval v t``,genPrint svalPrint);

(*Stype opaque*)
fun stypeopqPrint sys d t Top str brk blk =
  let
    val (_,[ls,ty]) = strip_comb t
    val typaram = #1 (listSyntax.dest_list ls)
  in
    add_newline>>str "type ">>
    (case typaram of [] => str"" 
                  | (x::y::xs) => str "(">>printTuple "," (str o toString) str typaram >> str") "
                  | _ => printTuple "," (str o toString) str typaram >>str" ")
    >>str (toString ty)
  end;

val _=temp_add_user_printer("stypeopqprint",``Stype_opq l t``,genPrint stypeopqPrint);

(*Booleans*)
fun boolPrint b sys d t Top str brk blk =
  str b;

val _=temp_add_user_printer("truelitprint",``Lit (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("falselitprint",``Lit (Bool F)``,genPrint (boolPrint "false"));

val _=temp_add_user_printer("trueplitprint",``Plit (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("falseplitprint",``Plit (Bool F)``,genPrint (boolPrint "false"));

(*Word8 - may not be needed depending on how smart sys printer is..*)
fun word8Print sys d t Top str brk blk =
  let val w = strip t
  in 
    str "0wx">>sys (Top,Top,Top) d w
  end

(*Pretty printer for ast list form, pattern to terms*)
fun astlistPrint sys d t Top str brk blk =
  let val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = sys(Top,Top,Top) d x>>str";"
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;

(*List pattern matching should be fixed in latest ver of HOL*)
val _=temp_add_user_printer("astlistprint",``x:prog``,genPrint astlistPrint);

(*TODO: the remainder of this should really go into a miscPP file*)
(*Pretty Printer specifics for globals, types & exceptions*)

fun tidPrinter sys d t Top str brk blk =
  str "datatype " >>str (toString (strip (strip t)));

fun texnPrinter sys d t Top str brk blk = 
  str "exception " >>str (toString (strip (strip t)));

fun tlongPrinter pref sys d t Top str brk blk =
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
fun bclistPrint sys d t Top str brk blk =
  let val t = rand t
      val ls = #1(listSyntax.dest_list t)
  fun printterms [] = str""
  |   printterms [x] = str ((fn s=> if(String.isPrefix "Label" s) then s^":" else "  "^s^"") 
		               (term_to_string x)) >> str"\n"
  |   printterms (x::xs) = (printterms [x])>>printterms xs
  in
    printterms ls
  end;
val _=temp_add_user_printer("bclistprint",``(SOME x ,(y:bc_inst store))``,genPrint bclistPrint);

(*Unlabeled*)
fun ubclistPrint sys d t Top str brk blk =
  let val t = rand t
      val ls = #1(listSyntax.dest_list t)
  fun printterms _ [] = str""
  |   printterms n [x] = str (Int.toString n) >>str":  ">> str (term_to_string x)>>str"\n"
  |   printterms n (x::xs) = (printterms n [x])>>printterms (n+1) xs
  in
    printterms 0 ls
  end;
val _=temp_add_user_printer("ubclistprint",``(NONE ,(y:bc_inst store))``,genPrint ubclistPrint);

end;
