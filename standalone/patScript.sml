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

(*reuse i2 extend global*)
temp_add_user_printer("pat_extendglobal",``Extend_global_pat n``,genPrint i2_extendglobalPrint);

(*pat_uops with nat args*)
fun pat_uopPrint uop sys d t Top str brk blk =
  str uop>>str"_">>sys (Top,Top,Top) d (strip t);

temp_add_user_printer("pat_optageqprint",``Tag_eq_pat x``,genPrint (pat_uopPrint "tag_eq"));
temp_add_user_printer("pat_opelpatprint",``El_pat x``,genPrint (pat_uopPrint "elem"));

fun pat_uappPrint sys d t Top str brk blk =
  let val (l,r)= dest_comb t;
  in
    sys(Top,Top,Top) d (strip l) >>str " ">> sys (Top,Top,Top) d r
  end;

temp_add_user_printer("pat_uappprint",``Uapp_pat x y``,genPrint pat_uappPrint);

(*Special case for Uapp init global*)
temp_add_user_printer("pat_initglobal",``Uapp_pat (Init_global_var_pat n) x``,genPrint i2_initglobalPrint);

(*Prints all constructor args in a list comma separated*)
temp_add_user_printer ("pat_conprint", ``Con_pat x y``,genPrint i2_pconPrint);

(*pat_Apply Equality*)
fun pat_equalityPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in 
    sys (Top,Top,Top) d (strip l) >> str " = " >> sys (Top,Top,Top) d r

  end;
temp_add_user_printer ("pat_equalityprint", ``App_pat Equality x y``, genPrint pat_equalityPrint);

(*pat_Apply Op*)
temp_add_user_printer ("pat_oppappprint", ``App_pat Opapp f x``, genPrint oppappPrint);

(*pat_sequence*)
fun pat_seqPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys(Top,Top,Top) d (strip l) >>str ";" >> sys (Top,Top,Top) d r >>str ")"
  end;
temp_add_user_printer ("pat_seqprint",``Seq_pat x y``,genPrint pat_seqPrint);

(*pat_Let*)
fun pat_letpatPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    blk CONSISTENT 0 (str"let _ = ">>sys(Top,Top,Top) d (strip l) >>add_newline>>str"in">>add_newline>>str"  ">> sys (Top,Top,Top) d r>>add_newline>>str"end")
  end;

temp_add_user_printer ("pat_letprint",``Let_pat y z ``,genPrint pat_letpatPrint);

(*pat_raise expr*) 
temp_add_user_printer ("pat_raiseprint", ``Raise_pat x``,genPrint raisePrint);

(*pat_Literals*)
(*pat_Pattern lit*)
temp_add_user_printer ("pat_litprint", ``Lit_pat x``, genPrint plitPrint);
temp_add_user_printer ("pat_unitprint", ``Lit_pat Unit``,genPrint unitPrint);

(*pat local var name debrujin indices*)
fun pat_varlocalPrint sys d t Top str brk blk =
    str"l_">>sys (Top,Top,Top) d (strip t);
temp_add_user_printer ("pat_varlocalprint", ``Var_local_pat x``,genPrint pat_varlocalPrint);

(*pat global Var name*)
temp_add_user_printer ("pat_varglobalprint", ``Var_global_pat n``,genPrint i1_varglobalPrint);

(*pat_handle*)
fun pat_handlePrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys(Top,Top,Top) d (strip l)>>str ")">>brk(1,0)
    >>blk CONSISTENT 0 (str "handle _ =>">>brk(1,2) >>sys (Top,Top,Top) d r)
  end;

temp_add_user_printer ("pat_handleprint", ``Handle_pat x y``,genPrint (pat_handlePrint));

(*Needs brackets*)
fun pat_seqPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    blk CONSISTENT 0 (sys (Top,Top,Top) d (strip l) >>str";">>brk(0,0)>>
    sys(Top,Top,Top) d r)
  end;

temp_add_user_printer ("pat_seqprint", ``Seq_pat x y``,genPrint pat_seqPrint);


(*pat_If-then-else*)
temp_add_user_printer("pat_ifthenelseprint", ``If_pat x y z``,genPrint ifthenelsePrint);


