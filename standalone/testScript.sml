open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib progToBytecodeTheory
open modLangTheory initialProgramTheory

(*Evaluates to AST*)
fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |>rand 
      end;

fun strip t = #2 (dest_comb t);

fun arglist t =
  let val v = t |>strip |> strip;
  in
    pairSyntax.strip_pair (hd(#1(listSyntax.dest_list v)))
  end;

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc sys d t Top str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*Top level letrec*)
fun tletrecPrint sys d t Top str brk =
  let
    open Portable smpp
    val (x::y::[z]) = arglist t
  in
    str "fun " >> sys (Top,Top,Top) d x >> str " ">>
    sys (Top,Top,Top) d y >> str " = " >> brk (1,0) >> sys (Top,Top,Top) (d-1) z
  end;

(*Nested mutually recursive letrec*)

fun letrecPrint sys d t Top str brk =
  let
    open Portable smpp
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms (t::xs) =
        let val (x::y::[z]) = pairSyntax.strip_pair t
        in
          str "fun " >> str (stringSyntax.fromHOLstring x) >> str " ">> str (stringSyntax.fromHOLstring y) 
          >> brk (1,0) >> str " = " >> brk (1,0) >> sys (Top,Top,Top) (d-1) z >> str "\n">> (printTerms xs)
        end
   in
     str "let" >> printTerms fundef >> str "in " >> sys (Top,Top,Top) (d-1) expr
   end;

temp_add_user_printer ("tletrecprint", ``Tdec (Dletrec x)``, genPrint tletrecPrint);
temp_add_user_printer ("letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*Toplevel Dlet  pat*expr*)
fun tletvalPrint sys d t Top str brk =
  let
    open Portable smpp
    val (l,r) = dest_comb (strip t);
  in
    str "val " >>
    sys (Top,Top,Top) (d-1) (strip l) >> 
    str " = " >> brk (1,0) >> sys (Top,Top,Top) (d-1) r
  end;

temp_add_user_printer ("tletvalprint", ``Tdec (Dlet x y)``,genPrint tletvalPrint);

(*Inner Let TODO*)

(*Pattern var*)
fun pvarPrint sys d t Top str brk =
    str (stringSyntax.fromHOLstring (strip t));

temp_add_user_printer ("pvarprint", ``Pvar x``, genPrint pvarPrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
fun pconPrint sys d t Top str brk =
  let
    open Portable smpp
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >> (printTerms xs);
    val terms = #1(listSyntax.dest_list (strip t))
  in
    str "(" >> printTerms terms >>str ")"
  end;
    
temp_add_user_printer ("pconprint", ``Pcon NONE x``,genPrint pconPrint);
temp_add_user_printer ("conprint", ``Con NONE x``,genPrint pconPrint);

(*Con SOME*)
fun pconsomePrint sys d t Top str brk =
  let
    open Portable smpp
    val (temp,r) = dest_comb t
    val (_,l) = dest_comb temp
    val args = #1(listSyntax.dest_list r)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >> (printTerms xs);
  in
    str (stringSyntax.fromHOLstring (strip (strip l))) >> (case args of [] => str "" | (_::_) => str "(" >> printTerms args >>str ")")
  end;

temp_add_user_printer ("pconsomeprint", ``Pcon (SOME x) y``,genPrint pconsomePrint);
temp_add_user_printer ("consomeprint", ``Con (Some x) y``,genPrint pconsomePrint);

(*Literals*)
(*Pattern lit*)
fun plitPrint sys d t Top str brk =
    sys (Top,Top,Top) (d-1) (strip (strip t));

temp_add_user_printer("plitprint", ``Plit x``, genPrint plitPrint);

fun unitPrint sys d t Top str brk =
  str "()";  

temp_add_user_printer ("litprint", ``Lit x``, genPrint plitPrint);
temp_add_user_printer ("unitprint", ``Lit Unit``,genPrint unitPrint);
temp_add_user_printer ("punitprint", ``Plit Unit``,genPrint unitPrint);

(*Short Var name*)
fun varShortPrint sys d t Top str brk =
    str (stringSyntax.fromHOLstring (strip (strip t)));

temp_add_user_printer ("varshortprint", ``Var (Short x)``,genPrint varShortPrint);


(*Matching*)
fun matPrint sys d t Top str brk =
  let
    open Portable smpp
    val (temp,r) = dest_comb t
    val l = #2(dest_comb temp)
    val cases = #1(listSyntax.dest_list r)
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (Top,Top,Top) (d-1) l >> str " => " >> sys (Top,Top,Top) (d-1) r end;
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>> str "|" >> (printMatch xs) 
  in
    str "case " >> (sys (Top,Top,Top) (d-1) l )>> str " of\n" >> printMatch (#1 (listSyntax.dest_list r)) 
  end;

temp_add_user_printer ("matprint", ``Mat x y``,genPrint matPrint);

(*Apply*)
fun oppappPrint sys d t Top str brk =
  let
    open Portable smpp
    val (temp,x) = dest_comb t
    val (_,f) = dest_comb temp
  in
    str "(" >> sys (Top,Top,Top) (d-1) f >> str " " >> sys (Top,Top,Top) (d-1) x >> str ")"
  end;
 
(*Infix apply, ignored for now*)
fun infixappPrint arithop sys d t Top str brk =
  let
    open Portable smpp
    val (_,x) = dest_comb t
  in
    sys (Top,Top,Top) (d-1) x >> str arithop
  end;


temp_add_user_printer ("plusappprint", ``App Opapp (Var (Short"+")) x``,genPrint (infixappPrint "+")); 
temp_add_user_printer ("minusappprint", ``App Opapp (Var (Short"-")) x``,genPrint (infixappPrint "-")); 

temp_add_user_printer ("oppappprint", ``App Opapp f x``, genPrint oppappPrint);


(*raise expr*) 
fun raisePrint sys d t Top str brk =
  let
    open Portable smpp
  in
    str "raise " >> sys (Top,Top,Top) (d-1) (strip t)
  end;

temp_add_user_printer ("raiseprint", ``Raise x``,genPrint raisePrint);

(*handle expr * list (pat*expr)*)
fun handlePrint sys d t Top str brk =
  let
    open Portable smpp
    val (te,pats) = dest_comb t
    val (_, expr) = dest_comb te
    fun casePrint x = let val (l,r) = pairSyntax.dest_pair x in sys (Top,Top,Top) (d-1) l >> str " => " >> sys (Top,Top,Top) (d-1) r end
    fun printMatch [] = str ""
    |   printMatch [x] = casePrint x
    |   printMatch (x::xs) = casePrint x>> str "|" >> (printMatch xs) 
  in
    str "(" >> sys (Top,Top,Top) (d-1) expr >> str ") handle " >> printMatch (#1 (listSyntax.dest_list pats))
  end;

temp_add_user_printer ("handleprint", ``Handle x y``,genPrint handlePrint);

(*If-then-else*)
fun ifthenelsePrint sys d t Top str brk =
  let
    open Portable smpp
    val (_,x::y::[z]) = strip_comb t
  in
  str "if (" >> sys (Top,Top,Top) (d-1) x >> str") then" >> sys (Top,Top,Top) (d-1) y >> str "else" >> sys (Top,Top,Top) (d-1) z >> str "#"
  end;

temp_add_user_printer ("ifthenelseprint", ``If x y z``, genPrint ifthenelsePrint);


(*Logical AND and OR*)
fun logPrint logop sys d t Top str brk =
  let
    open Portable smpp
    val (_,[_,x,y]) = strip_comb t
  in
   sys (Top,Top,Top) (d-1) x >> str logop >> sys (Top,Top,Top) (d-1) y
  end;

temp_add_user_printer ("andprint", ``Log And y z``, genPrint (logPrint " andalso "));
temp_add_user_printer ("orprint", ``Log Or y z``, genPrint (logPrint " orelse "));

(*TEST CODE for blocked if-then-else*)
(*TODO:Figure out why the extra space appears*)
fun ifthenelseprint sys d t Top str brk blk = 
  let
    open smpp Portable
    val (_,[x,y,z]) = strip_comb t
  in
    blk CONSISTENT 0 (
    str("if")  >> (sys (Top,Top,Top) d x) >>brk(1,0)>>
    str("then (") >> (sys (Top,Top,Top) d y) >>str(")")>>brk(1,0)>>
    str("else (") >> (sys (Top,Top,Top) d z) >>str(")"))
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

temp_add_user_printer("ifblockprint", ``If x y z``,genPrint ifthenelseprint);

fun tletvalPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) (pg,lg,rg) d t = let
  open Portable term_pp_types PPBackEnd smpp
  val {add_string,add_newline,add_break,ublock,ustyle,...} = ppfns
  val (l,r) = dest_comb (strip t)
  in
    ublock CONSISTENT 0 (
    add_string "val ">> sys (Top,Top,Top) (d-1) (strip l) >> add_string" =" >> add_break(1,0)>>
    sys (Top,Top,Top) (d-1) r) 
    
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;


temp_add_user_printer ("tletvalprint", ``Tdec (Dlet x y)``,tletvalPrint);



val prog = ``"structure Nat = struct val zero = 0 end;"``


fullEval ``"structure Nat = struct val zero = 0 end;"``

``"structure Nat :> sig type nat; type rnat = int; val bla : nat; val bla2: nat->rnat}
= struct { type nat = int; type rnat = int; val bla = 1; fun bla2 n = n+1; }"``

fullEval ``"if x>= 5 then (if(x>=10) then x else (if(y>0) then 5 else y)) else z;"``
fullEval ``"val x = if y+5>0 andalso z=0 then 1 else 2;"``; 
fullEval ``"val x = 3+4;"``
fullEval ``"val k = (raise Ex(5)) handle Ex(n) => n | Ex2 => 3 | Ex3 => f 4;"``
fullEval ``"val (x,y,z) = (a,1,c);"``;
fullEval ``"val x = (2,(),true);"``

val p = `` "val b = let fun f x = g (x-1) and g x = if x = 0 andalso x = 1 then 1 else f (x-1) val a = 5 in f a end;"``
val asts = eval ``get_all_asts ^(p)``
fullEval ``"val it = case f (g x) of Cons(h,t) => h | Nil => 2;"``

val p =  ``"datatype foo = A | B | C; fun f A = 1 | B = 2 | C = 3"``
fullEval ``"datatype foo = A | B | C; fun f A = 1 | B = 2 | C = 3"``
fullEval ``"structure Nat = struct val zero = 0 end; val x = Nat.zero;"``

fullEval ``"val it = let fun f x = g (x-1) and g x = if x = 0 then 1 else f (x-1) in f end 3;"``
