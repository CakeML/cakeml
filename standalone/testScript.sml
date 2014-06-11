open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib progToBytecodeTheory
open Portable smpp

(*Evaluates to AST*)
fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |>rand 
      end;

fun strip t = #2 (dest_comb t);

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc sys d t Top str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*TDec*)
fun tdecPrint sys d t Top str brk blk =
  sys (Top,Top,Top) (d-1) (strip t);

temp_add_user_printer("tdecprint", ``Tdec x``,genPrint tdecPrint);

(*Top level exceptions*)
fun dexnPrint sys d t Top str brk blk =
  let
    val (_,[x,y]) = strip_comb t
    val args = #1(listSyntax.dest_list y)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >>brk(1,0)>> (printTerms xs);
  in 
    add_newline >> str "exception " >> str (stringSyntax.fromHOLstring x)>> (case args of [] => str "" | (_::_) => str "(" >> printTerms args >>str ")")
  end;

temp_add_user_printer ("dexnprint", ``Dexn x y``,genPrint dexnPrint);

(*Top level datatypes list(list tvarN *typeN * list ... ) *)

fun printTuple f str [] = str""
    |   printTuple f str [x] = f x
    |   printTuple f str (x::xs) = printTuple f str [x] >> str "* " >> printTuple f str xs

fun dtypePrint sys d t Top str brk blk =
  let
    val ls = strip t
    val dtypelist = #1(listSyntax.dest_list ls);
    fun printCtors [] = str""
    |   printCtors [x] = let
          val (name,ls) = pairSyntax.dest_pair x
          val args = #1(listSyntax.dest_list ls)
          in
            str (stringSyntax.fromHOLstring name) >> (case args of [] => str"" | _ => str "of ">>printTuple (sys (Top,Top,Top) d) str args)
          end
    |   printCtors (x::xs) = printCtors[x] >> brk(1,0)>> str"|">>(printCtors xs)

    fun printTerms [] = str ""
    |   printTerms [x] = let
          val (params, rest) = pairSyntax.dest_pair x
          val (name, ctors) = pairSyntax.dest_pair rest
          in
             add_newline>> str "datatype " >>printTuple (str o stringSyntax.fromHOLstring) str (#1(listSyntax.dest_list params)) >> str (stringSyntax.fromHOLstring name) >> str " =" >> brk(1,0) >> blk CONSISTENT 0 (printCtors (#1(listSyntax.dest_list ctors)))
          end
    |   printTerms (x::xs) = printTerms [x] >> printTerms xs
  in
    printTerms dtypelist
  end;

temp_add_user_printer ("dtypeprint", ``Dtype x``,genPrint dtypePrint);

(*tvar name*)
fun tvarPrint sys d t Top str brk blk =
  str (stringSyntax.fromHOLstring (strip t));

temp_add_user_printer("tvarprint", ``Tvar x``,genPrint tvarPrint);

(*TODO: need to add for default types as well*)

(*TC_name*)
fun tcnamePrint sys d t Top str brk blk =
  str (stringSyntax.fromHOLstring (strip (strip t)));

temp_add_user_printer("tcnameprint", ``TC_name x``,genPrint tcnamePrint);

(*Tapp*)
fun tappPrint sys d t Top str brk blk = 
  let val (l,r) = dest_comb t
      val args = #1(listSyntax.dest_list (strip l))
  in
    (case args of [] => str"" | _ => str"(">>printTuple (sys (Top,Top,Top) d) str args >>str ")" )>> sys (Top,Top,Top) d r
  end;

temp_add_user_printer("tappprint", ``Tapp x y``,genPrint tappPrint);

(*Top level letrec list varN*varN*exp *)
fun dletrecPrint sys d t Top str brk blk =
  let
    val ls = strip t
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] = let val (x::y::[z]) = pairSyntax.strip_pair t
        in
         add_newline>> str "fun" >> str (stringSyntax.fromHOLstring x) >> str " ">> str (stringSyntax.fromHOLstring y)>> str " =" >> brk(1,0)>> sys (Top,Top,Top) (d-1) z
        end
    |   printTerms (t::xs) = printTerms [t] >>str " and">> brk(1,0)
          >> (printTerms xs)
  in
    printTerms fundef
  end;

temp_add_user_printer ("dletrecprint", ``Dletrec x``, genPrint dletrecPrint);

(*Nested mutually recursive letrec*)

fun letrecPrint sys d t Top str brk blk =
  let
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [t] = let val (x::y::[z]) = pairSyntax.strip_pair t
        in
          blk CONSISTENT 0 (str "fun" >> str (stringSyntax.fromHOLstring x) >> str " ">> str (stringSyntax.fromHOLstring y)>> str " =" >> sys (Top,Top,Top) (d-1) z)
        end
    |   printTerms (t::xs) = printTerms [t] >>str " and">> brk(1,0)
          >> (printTerms xs)
  in
     (blk CONSISTENT 0 (
     str "let" >> printTerms fundef >> brk(1,0) 
     >> str "in" >> sys (Top,Top,Top) d expr >> brk(1,0)
     >> str "end"))
  end;

temp_add_user_printer ("letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*Lambdas varN*expr *)
fun lambdaPrint sys d t Top str brk blk = 
  let
    val (_,[name,expr]) = strip_comb t
  in
    str "(fn">> str (stringSyntax.fromHOLstring name) >>str"=>">>brk(1,0)>> blk CONSISTENT 0 (sys (Top,Top,Top) (d-1) expr) >> str")"
  end;

temp_add_user_printer ("lambdaprint", ``Fun x y``,genPrint lambdaPrint);

(*Toplevel Dlet  pat*expr *)
fun dletvalPrint sys d t Top str brk blk=
  let
    open Portable smpp
    val (_,[l,r]) = strip_comb t;
  in
    add_newline>> str "val" >>
    sys (Top,Top,Top) (d-1) l >> 
    str " =" >> brk (1,0) >> sys (Top,Top,Top) (d-1) r
  end;

temp_add_user_printer ("dletvalprint", ``Dlet x y``,genPrint dletvalPrint);

(*Inner Let SOME*)
fun letvalPrint sys d t Top str brk blk =
  let
    val (t,body) = dest_comb t
    val (t,eq) = dest_comb t
    val name = stringSyntax.fromHOLstring (strip (strip t))
  in
    (blk CONSISTENT 0 (
    brk(1,0)>> str "let" >> str name >>str" = ">> (sys (Top,Top,Top) d eq) >> add_newline 
    >> str"in" >> (sys (Top,Top,Top) d body) >> add_newline
    >> str"end" ))
  end;

temp_add_user_printer ("letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);


(*Pattern var*)
fun pvarPrint sys d t Top str brk blk =
    str (stringSyntax.fromHOLstring (strip t));

temp_add_user_printer ("pvarprint", ``Pvar x``, genPrint pvarPrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
fun pconPrint sys d t Top str brk blk =
  let
    open Portable smpp
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str ",">>brk(1,0) >> (printTerms xs);
    val terms = #1(listSyntax.dest_list (strip t))
  in
    str "(" >> printTerms terms >>str ")"
  end;
    
temp_add_user_printer ("pconprint", ``Pcon NONE x``,genPrint pconPrint);
temp_add_user_printer ("conprint", ``Con NONE x``,genPrint pconPrint);

(*Con SOME*)
fun pconsomePrint sys d t Top str brk blk=
  let
    open Portable smpp
    val (temp,r) = dest_comb t
    val (_,l) = dest_comb temp
    val args = #1(listSyntax.dest_list r)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str ",">>brk(1,0) >> (printTerms xs);
  in
    str (stringSyntax.fromHOLstring (strip (strip l))) >> (case args of [] => str "" | (_::_) => str "(" >> printTerms args >>str ")")
  end;

temp_add_user_printer ("pconsomeprint", ``Pcon (SOME x) y``,genPrint pconsomePrint);
temp_add_user_printer ("consomeprint", ``Con (Some x) y``,genPrint pconsomePrint);

(*Literals*)
(*Pattern lit*)
fun plitPrint sys d t Top str brk blk=
    sys (Top,Top,Top) (d-1) (strip (strip t));

temp_add_user_printer("plitprint", ``Plit x``, genPrint plitPrint);

fun unitPrint sys d t Top str brk blk=
  str "()";  

temp_add_user_printer ("litprint", ``Lit x``, genPrint plitPrint);
temp_add_user_printer ("unitprint", ``Lit Unit``,genPrint unitPrint);
temp_add_user_printer ("punitprint", ``Plit Unit``,genPrint unitPrint);

(*Short Var name*)
fun varShortPrint sys d t Top str brk blk=
    str (stringSyntax.fromHOLstring (strip (strip t)));

temp_add_user_printer ("varshortprint", ``Var (Short x)``,genPrint varShortPrint);


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
    |   printMatch (x::xs) = casePrint x>>brk(1,0)>> str"|">>(printMatch xs) 
  in
    str "case" >> (sys (Top,Top,Top) (d-1) l )>> str " of">>blk CONSISTENT 0 (printMatch (#1 (listSyntax.dest_list r))) 
  end;

temp_add_user_printer ("matprint", ``Mat x y``,genPrint matPrint);

(*Apply*)
fun oppappPrint sys d t Top str brk blk =
  let
    open Portable smpp
    val (temp,x) = dest_comb t
    val (_,f) = dest_comb temp
  in
    str "(" >> sys (Top,Top,Top) (d-1) f >> str " " >> sys (Top,Top,Top) (d-1) x >> str ")"
  end;
 
temp_add_user_printer ("oppappprint", ``App Opapp f x``, genPrint oppappPrint);

(*Infix apply, ignored for now*)
(*
fun infixappPrint arithop sys d t Top str brk =
  let
    open Portable smpp
    val (_,x) = dest_comb t
  in
    sys (Top,Top,Top) (d-1) x >> str arithop
  end;


temp_add_user_printer ("plusappprint", ``App Opapp (Var (Short"+")) x``,genPrint (infixappPrint "+")); 
temp_add_user_printer ("minusappprint", ``App Opapp (Var (Short"-")) x``,genPrint (infixappPrint "-")); 
*)

(*raise expr*) 
fun raisePrint sys d t Top str brk blk=
  let
    open Portable smpp
  in
    str "raise " >> sys (Top,Top,Top) (d-1) (strip t)
  end;

temp_add_user_printer ("raiseprint", ``Raise x``,genPrint raisePrint);

(*handle expr * list (pat*expr)*)
fun handlePrint sys d t Top str brk blk =
  let
    open Portable smpp
    val (te,pats) = dest_comb t
    val (_, expr) = dest_comb te
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (Top,Top,Top) (d-1) l >> str " => " >> sys (Top,Top,Top) (d-1) r end
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>> brk(1,0)>>str "|" >> (printMatch xs) 
  in
    str "(" >> sys (Top,Top,Top) (d-1) expr >> str ")">>brk(1,0)>>str "handle" >> blk CONSISTENT 0 (printMatch (#1 (listSyntax.dest_list pats)))
  end;

temp_add_user_printer ("handleprint", ``Handle x y``,genPrint handlePrint);

(*Logical AND and OR*)
fun logPrint logop sys d t Top str brk blk =
  let
    open Portable smpp
    val (_,[_,x,y]) = strip_comb t
  in
   sys (Top,Top,Top) (d-1) x >> str logop >> sys (Top,Top,Top) (d-1) y
  end;

temp_add_user_printer ("andprint", ``Log And y z``, genPrint (logPrint " andalso "));
temp_add_user_printer ("orprint", ``Log Or y z``, genPrint (logPrint " orelse "));

(*If-then-else*)
(*TODO:Figure out why the extra space appears*)
fun ifthenelsePrint sys d t Top str brk blk = 
  let
    open smpp Portable
    val (_,[x,y,z]) = strip_comb t
  in
    blk CONSISTENT 0 (
    str("if (")  >> (sys (Top,Top,Top) d x) >>str(")")>>brk(1,0)>>
    str("then (") >> (sys (Top,Top,Top) d y) >>str(")")>>brk(1,0)>>
    str("else (") >> (sys (Top,Top,Top) d z) >>str(")"))
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

temp_add_user_printer("ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);

val prog = ``"structure Nat = struct val zero = 0 end;"``


fullEval ``"structure Nat = struct val zero = 0 end;"``

``"structure Nat :> sig type nat; type rnat = int; val bla : nat; val bla2: nat->rnat}
= struct { type nat = int; type rnat = int; val bla = 1; fun bla2 n = n+1; }"``

fullEval ``"(case x of Cons(f)=> if iamtoolongstringgggggggg yasdfasdsdf then 3 else 4 | Cons2(z)=> if z then 4 else raise Fail2 | _=> raise Fail) handle Fail => f y | Fail2 => f z ;"``


fullEval ``"if x>= 5 then (if(x>=10) then x else (if(y>0) then 5 else y)) else z;"``
fullEval ``"val x = if y+5>0 andalso z=0 then 1 else 2;"``; 
fullEval ``"val x = 3+4;"``
fullEval ``"val k = (raise Ex(5)) handle Ex(n) => n | Ex2 => 3 | Ex3 => f 4 |Ex10000000 => f 1000000;"``
fullEval ``"val (x,y,z) = (a,1,c);"``;
fullEval ``"val x = (2,(),true);"``

val p = `` "val b = let fun f x = g (x-1) and g x = if x = 0 andalso x = 1 then 1 else f (x-1) val a = 5 in f a end;"``
val asts = eval ``get_all_asts ^(p)``
fullEval ``"val it = case f (g x) of Cons(h,t) => h | Nil => 2;"``

val p =  ``"datatype foo = A | B | C; fun f A = 1 | B = 2 | C = 3"``
fullEval ``"datatype foo = A | B | C; fun f A = 1 | B = 2 | C = 3"``
fullEval ``"structure Nat = struct val zero = 0 end; val x = Nat.zero;"``

fullEval ``"val it = let fun f x = g (x-1) and g x = if x = 0 then 1 else f (x-1) in f end 3;"``
