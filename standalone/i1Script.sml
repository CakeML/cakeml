open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib progToBytecodeTheory
open modLangTheory initialProgramTheory

(*RHS of theorem to term*)
val rhsThm = rhs o concl;

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)

      (*i1 translation*)
      val n = rhsThm (eval ``init_compiler_state.next_global``)
      val (m1,m2) = pairSyntax.dest_pair( rhsThm( eval ``init_compiler_state.globals_env``))
      val l1 = eval ``prog_to_i1 ^(n) ^(m1) ^(m2) ^(ast)``;
      val [v1,v2,m2,p1] = pairSyntax.strip_pair(rhsThm l1)    

      (*i2 translation*)
      val l2 = eval ``prog_to_i2 init_compiler_state.contags_env ^(p1) ``
      val (v,rest) = pairSyntax.dest_pair (rhsThm l2)
      val (exh,p2) = pairSyntax.dest_pair rest

      (*i3 translation*)
      val arg1 = rhsThm( eval ``(none_tag,SOME(TypeId (Short "option")))``)
      val arg2 = rhsThm( eval ``(some_tag,SOME(TypeId (Short "option")))``)
      val l3 = eval ``prog_to_i3 ^(arg1) ^(arg2) ^(n) ^(p2)``
      val (v,p3) = pairSyntax.dest_pair(rhsThm l3)

      (*exp to exh trans*)
      val exp_to_exh = eval ``exp_to_exh (^(exh) ⊌ init_compiler_state.exh) ^(p3)``
      val p4 = rhsThm exp_to_exh

      (*exp_to_pat trans*)
      val exp_to_pat = eval ``exp_to_pat [] ^(p4)``
      val p5 = rhsThm exp_to_pat
      
      (*exp_to_cexp*)
      val exp_to_Cexp = eval ``exp_to_Cexp ^(p5)``
      val p6 = rhsThm exp_to_Cexp

      (*compileCexp*)
      val compile_Cexp = eval ``compile_Cexp [] 0 <|out:=[];next_label:=init_compiler_state.rnext_label|> ^(p6)``
      val p7 = rhsThm compile_Cexp
  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7}
  end;

val prog = ``"val x = 5; x+2+3;"``

(*Not included yet*)
val compile_print_err = eval ``compile_print_err ^(r)``
val r = rhs(concl compile_print_err)

val addIt = eval ``case FLOOKUP ^(m2) "it" of
                             NONE => ^(r)
                           | SOME n =>
                               (let r = emit ^(r) [Gread n; Print]
                                in
                                  emit r (MAP PrintC (EXPLODE "\n")))``
val r = rhs(concl addIt)
val emit = eval ``emit ^(r) [Stop T]``
val rev = eval ``REVERSE (^(rhs(concl emit))).out``

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc sys d t Top str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*i1_Unnamed Prompts NONE => declist*)
fun i1_promptNonePrint sys d t Top str brk blk=
  let
    open smpp
    val (_,ls) = dest_comb t
  in
    blk CONSISTENT 0 (
    str "prompt {">>brk(1,0)>>sys (Top,Top,Top) (d-1) ls >> brk(1,0) >>str "}")
  end;

temp_add_user_printer("i1_promptnoneprint",``Prompt_i1 NONE x``,genPrint i1_promptNonePrint);

(*Named Prompt SOME => declist TODO*)

(*Top level exceptions*)
fun texnPrint sys d t Top str brk blk =
  let
    val (_,[x,y]) = strip_comb (strip t)
    val args = #1(listSyntax.dest_list y)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >> (printTerms xs);
  in 
    add_newline >> str "exception " >> str (stringSyntax.fromHOLstring x)>> (case args of [] => str "" | (_::_) => str "(" >> printTerms args >>str ")")
  end;

temp_add_user_printer ("texnprint", ``Tdec (Dexn x y)``,genPrint texnPrint);

(*Top level datatypes list(list tvarN *typeN * list ... ) *)

fun printTuple f str [] = str""
    |   printTuple f str [x] = f x
    |   printTuple f str (x::xs) = printTuple f str [x] >> str "* " >> printTuple f str xs

fun ttypePrint sys d t Top str brk blk =
  let
    val ls = strip (strip t)
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

temp_add_user_printer ("ttypeprint", ``Tdec (Dtype x)``,genPrint ttypePrint);

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

(*i1_Top level letrec list varN*varN*exp -- Only strip once *)
fun i1_tletrecPrint sys d t Top str brk blk =
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

temp_add_user_printer ("i1_tletrecprint", ``Dletrec_i1 x``, genPrint i1_tletrecPrint);

(*i1_Nested mutually recursive letrec*)

fun i1_letrecPrint sys d t Top str brk blk =
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

temp_add_user_printer ("i1_letrecprint", ``Letrec_i1 x y``,genPrint letrecPrint);

(*i1_Lambdas varN*expr *)
fun i1_lambdaPrint sys d t Top str brk blk = 
  let
    val (_,[name,expr]) = strip_comb t
  in
    str "(fn">> str (stringSyntax.fromHOLstring name) >>str"=>">>brk(1,0)>> blk CONSISTENT 0 (sys (Top,Top,Top) (d-1) expr) >> str")"
  end;

temp_add_user_printer ("i1_lambdaprint", ``Fun_i1 x y``,genPrint i1_lambdaPrint);

(*Toplevel Dlet nat*expr *)
fun i1_tletvalPrint sys d t Top str brk blk=
  let
    open Portable smpp
    val (l,r) = dest_comb (strip t);
  in
    add_newline>> str "val" >>
    sys (Top,Top,Top) (d-1) (strip l) >> 
    str " =" >> brk (1,0) >> sys (Top,Top,Top) (d-1) r
  end;

temp_add_user_printer ("i1_tletvalprint", ``Tdec (Dlet x y)``,genPrint i1_tletvalPrint);

(*i1_Inner Let SOME*)
fun i1_letvalPrint sys d t Top str brk blk =
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

temp_add_user_printer ("i1_letvalprint", ``Let_i1 (SOME x) y z``,genPrint i1_letvalPrint);


(*Pattern var*)
fun pvarPrint sys d t Top str brk blk =
    str (stringSyntax.fromHOLstring (strip t));

temp_add_user_printer ("pvarprint", ``Pvar x``, genPrint pvarPrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
fun i1_pconPrint sys d t Top str brk blk =
  let
    open Portable smpp
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) (d-1) x
    |   printTerms (x::xs) = sys (Top,Top,Top) (d-1) x >> str "," >> (printTerms xs);
    val terms = #1(listSyntax.dest_list (strip t))
  in
    str "(" >> printTerms terms >>str ")"
  end;
    
temp_add_user_printer ("i1_conprint", ``Con_i1 NONE x``,genPrint i1_pconPrint);

(*Con SOME*)
fun pconsomePrint sys d t Top str brk blk=
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

(*i1_Literals*)
(*i1_Pattern lit*)
fun i1_plitPrint sys d t Top str brk blk=
    sys (Top,Top,Top) (d-1) (strip (strip t));

fun i1_unitPrint sys d t Top str brk blk=
  str "()";  

temp_add_user_printer ("i1_litprint", ``Lit_i1 x``, genPrint i1_plitPrint);
temp_add_user_printer ("i1_unitprint", ``Lit_i1 Unit``,genPrint i1_unitPrint);

(*i1 local Var name, no more long names*)
fun i1_varlocalPrint sys d t Top str brk blk=
    str (stringSyntax.fromHOLstring (strip t));

temp_add_user_printer ("i1_varlocalprint", ``Var_local_i1 x``,genPrint i1_varlocalPrint);


(*i1_Matching*)
fun i1_matPrint sys d t Top str brk blk=
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

temp_add_user_printer ("i1_matprint", ``Mat_i1 x y``,genPrint i1_matPrint);

(*i1_Apply*)
temp_add_user_printer ("i1_oppappprint", ``App_i1 Opapp f x``, genPrint oppappPrint);

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

(*i1_raise expr*) 
temp_add_user_printer ("i1_raiseprint", ``Raise_i1 x``,genPrint raisePrint);

(*handle expr * list (pat*expr)*)
temp_add_user_printer ("i1_handleprint", ``Handle_i1 x y``,genPrint handlePrint);

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

(*i1_If-then-else*)
temp_add_user_printer("i1_ifthenelseprint", ``If_i1 x y z``,genPrint ifthenelsePrint);


val x = ``"val x = 1;"``

val x = ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val th = EVAL ``prog_to_bytecode_string ^x``;

