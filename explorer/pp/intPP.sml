structure intPP =
struct
open astPP conPP modPP exhPP patPP
(*This is stateful!*)
val collectAnnotations :(term list ref)= ref ([]:term list);

(*cexp_Nested mutually recursive letrec
Collects annotations
*)
fun cexp_letrecPrint sys d t Top str brk blk =
  let
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [x] = 
          let val ([opt,num,x]) = pairSyntax.strip_pair x
          in
            if optionSyntax.is_none(opt) then str ""
            else (*Has annotations*)
                let val lab = hd (pairSyntax.strip_pair(strip opt))
                  in 
                    (collectAnnotations := optionSyntax.dest_some(opt) :: (!collectAnnotations));
                     str "_">>str (term_to_string lab)
                  end 
    	    >>str" = ">>sys (Top,Top,Top) d x
          end 
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and">> (printTerms xs)
  in
     blk CONSISTENT 0 (str "let " >> (blk CONSISTENT 0 (str "fun">>printTerms fundef))
     >>add_newline>>str "in">>add_newline>>str"  ">>sys (Top,Top,Top) d expr >>add_newline>> str "end")
  end;

val _ = temp_add_user_printer ("cexp_letrecprint", ``CLetrec x y``,genPrint cexp_letrecPrint);

(*TODO: find an example where this occurs??*)
(*cexp_CUpd*)
fun cexp_cupdPrint sys d t Top str brk blk =
  let val (_,[l,r]) = strip_comb t
  in
    blk CONSISTENT 0 (sys(Top,Top,Top) d l >>str " =">>brk(1,2) >>sys(Top,Top,Top) d r)
  end;

val _ = temp_add_user_printer("cexp_cupdprint", ``CUpd x y``,genPrint cexp_cupdPrint);

(*cexp_Apply Equality*)
val _ = temp_add_user_printer ("cexp_equalityprint", ``CPrim2 CEq x y``, genPrint pat_equalityPrint);

(*cexp_Call TODO: decide whether to use callT/F or not*)
(*Or maybe call (...) with [...]*)
fun cexp_ccallPrint sys d t Top str brk blk =
  let val (t,ls) = dest_comb t
      val (t,name) = dest_comb t
      val (_,b) = dest_comb t
  in
     blk CONSISTENT 0 ( str"call_">>sys(Top,Top,Top) d b>>str" (">>sys (Top,Top,Top) d name >> str ")"
     >>brk(1,0)>>str"with ">>sys (Top,Top,Top) d ls)
  end;

val _ = temp_add_user_printer ("cexp_ccallprint", ``CCall b f x``, genPrint cexp_ccallPrint);

(*cexp_prim1*)
(*TODO: these actually seem rather superfluous...*)
fun cexp_isblockPrint sys d t Top str brk blk =
  str"is_block";

val _ = temp_add_user_printer("cexp_cisblockprint",``CIsBlock``,genPrint cexp_isblockPrint);

val _ = temp_add_user_printer("cexp_ctageqprint",``CTagEq x``,genPrint (pat_uopPrint "tag_eq"));
val _ = temp_add_user_printer("cexp_cprojprint",``CProj x``,genPrint (pat_uopPrint "elem"));

val _ = temp_add_user_printer("cexp_prim1print",``CPrim1 x y``,genPrint pat_uappPrint);

val _ = temp_add_user_printer("cexp_initgprint",``CPrim1 (CInitG x) y``,i2_initglobalPrint);

(*cexp_ constructors*)
val _ = temp_add_user_printer ("cexp_conprint", ``CCon x y``,i2_pconPrint);

(*cexpextend global*)
val _ = temp_add_user_printer("cexp_extendglobal",``CExtG n``,genPrint i2_extendglobalPrint);

(*cexp_Let*)
fun cexp_letpatPrint sys d t Top str brk blk =
  let val (t1,exp2) = dest_comb t
      val (t,exp1) = dest_comb t1
      val (_,b) = dest_comb t
    in
    if b = ``T``
    then
      blk CONSISTENT 0 (str"bind = ">>sys(Top,Top,Top) d exp1 >>add_newline>>str"in">>add_newline>>str"  ">> sys (Top,Top,Top) d exp2>>add_newline>>str"end")
    else
      blk CONSISTENT 0 (sys (Top,Top,Top) d exp1 >>str";">>brk(1,0)>>
      sys(Top,Top,Top) d exp2) 
  end;

val _ = temp_add_user_printer ("cexp_letprint",``CLet b y z ``,genPrint cexp_letpatPrint);

(*cexp_Literals*)
(*cexp_Pattern lit*)
val _ = temp_add_user_printer ("cexp_litprint", ``CLit x``, genPrint plitPrint);
val _ = temp_add_user_printer ("cexp_unitprint", ``CLit Unit``,genPrint unitPrint);

val _ = temp_add_user_printer("cexp_truelitprint",``CLit (Bool T)``,genPrint (boolPrint "true"));
val _ = temp_add_user_printer("cexp_falselitprint",``CLit (Bool F)``,genPrint (boolPrint "false"));

(*cexp local var name debrujin indices*)
val _ = temp_add_user_printer ("cexp_varlocalprint", ``CVar x``,genPrint pat_varlocalPrint);

(*cexp global Var name*)
val _ = temp_add_user_printer ("cexp_varglobalprint", ``CGvar n``,i1_varglobalPrint);

(*cexp_raise expr*) 
val _ = temp_add_user_printer ("cexp_raiseprint", ``CRaise x``,genPrint raisePrint);

(*cexp_handle*)
val _ = temp_add_user_printer ("cexp_handleprint", ``CHandle x y``,genPrint (pat_handlePrint));

(*cexp_If-then-else*)
val _ = temp_add_user_printer("cexp_ifthenelseprint", ``CIf x y z``,genPrint ifthenelsePrint);

end;
