(*INCOMPLETE*)
(*pat_Pvar*)
temp_add_user_printer ("pat_pvarprint", ``Pvar_pat x``, genPrint pvarPrint);

(*pat_Nested mutually recursive letrec*)
fun pat_letrecPrint sys d t Top str brk blk =
  let
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [x] = sys (Top,Top,Top) d x    
    |   printTerms (t::xs) = printTerms [t] >>add_newline>>str "and _ = ">> (printTerms xs)
  in
     blk CONSISTENT 0 (str "let " >> (blk CONSISTENT 0 (str "fun _ = ">>printTerms fundef))
     >>add_newline>>str "in">>add_newline>>str"  ">>sys (Top,Top,Top) d expr >>add_newline>> str "end")
  end;

temp_add_user_printer ("pat_letrecprint", ``Letrec_pat x y``,genPrint pat_letrecPrint);

(*pat_Lambdas expr*)
fun pat_lambdaPrint sys d t Top str brk blk =
  str"fun _ = ">>sys (Top,Top,Top) d (strip t);

temp_add_user_printer ("pat_lambdaprint", ``Fun_pat x``,genPrint pat_lambdaPrint);

(*cexp_Apply Equality*)
temp_add_user_printer ("cexp_equalityprint", ``CPrim2 CEq x y``, genPrint pat_equalityPrint);

(*cexp_Call*)
fun cexp_ccallPrint sys d t Top str brk blk =
  let val (t,ls) = dest_comb t
      val name = strip t
  in
     blk CONSISTENT 0 (str"call (">>sys (Top,Top,Top) d name >> str ")">>brk(1,0)>>str "with ">>sys (Top,Top,Top) d ls)
  end;

temp_add_user_printer ("cexp_ccallprint", ``CCall b f x``, genPrint cexp_ccallPrint);

(*cexp_prim1*)
fun pat_uopPrint uop sys d t Top str brk blk =
  str uop>>str"_">>sys (Top,Top,Top) d (strip t);

temp_add_user_printer("cexp_initgprint",``CInitG x``,genPrint (pat_uopPrint "init_global"));
temp_add_user_printer("cexp_ctageqprint",``CTagEq x``,genPrint (pat_uopPrint "tag_eq"));
temp_add_user_printer("cexp_cprojprint",``CProj x``,genPrint (pat_uopPrint "elem"));

temp_add_user_printer("cexp_prim1print",``CPrim1 x y``,genPrint pat_uappPrint);


(*cexp_ constructors*)
temp_add_user_printer ("cexp_conprint", ``CCon x y``,genPrint i2_pconPrint);

(*cexpextend global*)
temp_add_user_printer("cexp_extendglobal",``CExtG n``,genPrint i2_extendglobalPrint);

(*cexp_Let*)
fun cexp_letpatPrint sys d t Top str brk blk =
  let val (t1,exp2) = dest_comb t
      val (t,exp1) = dest_comb t1
      val (_,b) = dest_comb t
    in
    if b = ``T``
    then
      blk CONSISTENT 0 (str"let _ = ">>sys(Top,Top,Top) d exp1 >>add_newline>>str"in">>add_newline>>str"  ">> sys (Top,Top,Top) d exp2>>add_newline>>str"end")
    else
      blk CONSISTENT 0 (sys (Top,Top,Top) d exp1 >>str";">>brk(0,0)>>
      sys(Top,Top,Top) d exp2) 
  end;

temp_add_user_printer ("cexp_letprint",``CLet b y z ``,genPrint cexp_letpatPrint);

(*cexp_Literals*)
(*cexp_Pattern lit*)
temp_add_user_printer ("cexp_litprint", ``CLit x``, genPrint plitPrint);
temp_add_user_printer ("cexp_unitprint", ``CLit Unit``,genPrint unitPrint);

(*cexp local var name debrujin indices*)
temp_add_user_printer ("cexp_varlocalprint", ``CVar x``,genPrint pat_varlocalPrint);

(*cexp global Var name*)
temp_add_user_printer ("cexp_varglobalprint", ``CGvar n``,genPrint i1_varglobalPrint);

(*cexp_raise expr*) 
temp_add_user_printer ("cexp_raiseprint", ``CRaise x``,genPrint raisePrint);

(*cexp_handle*)
temp_add_user_printer ("cexp_handleprint", ``CHandle x y``,genPrint (pat_handlePrint));

(*cexp_If-then-else*)
temp_add_user_printer("cexp_ifthenelseprint", ``CIf x y z``,genPrint ifthenelsePrint);


