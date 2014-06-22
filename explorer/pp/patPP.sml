structure patPP =
struct
open astPP conPP modPP exhPP
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

val _=temp_add_user_printer ("pat_letrecprint", ``Letrec_pat x y``,genPrint pat_letrecPrint);

(*pat_Lambdas expr*)
fun pat_lambdaPrint sys d t Top str brk blk =
  str"fun _ = ">>sys (Top,Top,Top) d (strip t);

val _=temp_add_user_printer ("pat_lambdaprint", ``Fun_pat x``,genPrint pat_lambdaPrint);

(*reuse i2 extend global*)
val _=temp_add_user_printer("pat_extendglobal",``Extend_global_pat n``,genPrint i2_extendglobalPrint);

(*pat_uops with nat args*)
fun pat_uopPrint uop sys d t Top str brk blk =
  str uop>>str"_">>sys (Top,Top,Top) d (strip t);

val _=temp_add_user_printer("pat_optageqprint",``Tag_eq_pat x``,genPrint (pat_uopPrint "tag_eq"));
val _=temp_add_user_printer("pat_opelpatprint",``El_pat x``,genPrint (pat_uopPrint "elem"));

fun pat_uappPrint sys d t Top str brk blk =
  let val (l,r)= dest_comb t;
  in
    sys(Top,Top,Top) d (strip l) >>str " ">> sys (Top,Top,Top) d r
  end;

val _=temp_add_user_printer("pat_uappprint",``Uapp_pat x y``,genPrint pat_uappPrint);

(*Special case for Uapp init global*)
val _=temp_add_user_printer("pat_initglobal",``Uapp_pat (Init_global_var_pat n) x``,genPrint i2_initglobalPrint);

(*Prints all constructor args in a list comma separated*)
val _=temp_add_user_printer ("pat_conprint", ``Con_pat x y``,genPrint i2_pconPrint);

(*pat_Apply Equality*)
fun pat_equalityPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in 
    sys (Top,Top,Top) d (strip l) >> str " = " >> sys (Top,Top,Top) d r

  end;
val _=temp_add_user_printer ("pat_equalityprint", ``App_pat Equality x y``, genPrint pat_equalityPrint);

(*pat_Apply Op*)
val _=temp_add_user_printer ("pat_oppappprint", ``App_pat Opapp f x``, genPrint oppappPrint);

(*pat_sequence*)
fun pat_seqPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    blk CONSISTENT 0 (str"">> sys(Top,Top,Top) d (strip l) >>str ";">>
    brk (1,0)>>sys (Top,Top,Top) d r >>str "")
  end;
val _=temp_add_user_printer ("pat_seqprint",``Seq_pat x y``,genPrint pat_seqPrint);

(*pat_Let*)
fun pat_letpatPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    blk CONSISTENT 0 (str"let _ = ">>sys(Top,Top,Top) d (strip l) >>add_newline>>str"in">>add_newline>>str"  ">> sys (Top,Top,Top) d r>>add_newline>>str"end")
  end;

val _=temp_add_user_printer ("pat_letprint",``Let_pat y z ``,genPrint pat_letpatPrint);

(*pat_raise expr*) 
val _=temp_add_user_printer ("pat_raiseprint", ``Raise_pat x``,genPrint raisePrint);

(*pat_Literals*)
(*pat_Pattern lit*)
val _=temp_add_user_printer ("pat_litprint", ``Lit_pat x``, genPrint plitPrint);
val _=temp_add_user_printer ("pat_unitprint", ``Lit_pat Unit``,genPrint unitPrint);

(*pat local var name debrujin indices*)
fun pat_varlocalPrint sys d t Top str brk blk =
    str"l_">>sys (Top,Top,Top) d (strip t);
val _=temp_add_user_printer ("pat_varlocalprint", ``Var_local_pat x``,genPrint pat_varlocalPrint);

(*pat global Var name*)
val _=temp_add_user_printer ("pat_varglobalprint", ``Var_global_pat n``,genPrint i1_varglobalPrint);

(*pat_handle*)
fun pat_handlePrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys(Top,Top,Top) d (strip l)>>str ")">>brk(1,0)
    >>blk CONSISTENT 0 (str "handle _ =>">>brk(1,2) >>sys (Top,Top,Top) d r)
  end;

val _=temp_add_user_printer ("pat_handleprint", ``Handle_pat x y``,genPrint (pat_handlePrint));

(*TODO: this probabl needs brackets*)
fun pat_seqPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    blk CONSISTENT 0 (sys (Top,Top,Top) d (strip l) >>str";">>brk(0,0)>>
    sys(Top,Top,Top) d r)
  end;

val _=temp_add_user_printer ("pat_seqprint", ``Seq_pat x y``,genPrint pat_seqPrint);


(*pat_If-then-else*)
val _=temp_add_user_printer("pat_ifthenelseprint", ``If_pat x y z``,genPrint ifthenelsePrint);

val _=temp_add_user_printer("pat_truelitprint",``Lit_pat (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("pat_falselitprint",``Lit_pat (Bool F)``,genPrint (boolPrint "false"));

(*pat binops*)
val _=temp_add_user_printer ("pat_assignappprint", ``App_pat Opapp (Var_global_pat 3) x``,genPrint (infixappPrint ":=")); 
val _=temp_add_user_printer ("pat_eqappprint", ``App_pat Opapp (Var_global_pat 4) x``,genPrint (infixappPrint "=")); 
val _=temp_add_user_printer ("pat_gteqappprint", ``App_pat Opapp (Var_global_pat 5) x``,genPrint (infixappPrint ">=")); 
val _=temp_add_user_printer ("pat_lteqappprint", ``App_pat Opapp  (Var_global_pat 6) x``,genPrint (infixappPrint "<=")); 
val _=temp_add_user_printer ("pat_gtappprint", ``App_pat Opapp (Var_global_pat 7) x``,genPrint (infixappPrint ">")); 
val _=temp_add_user_printer ("pat_ltappprint", ``App_pat Opapp (Var_global_pat 8) x``,genPrint (infixappPrint "<")); 
val _=temp_add_user_printer ("pat_modappprint", ``App_pat Opapp (Var_global_pat 9) x``,genPrint (infixappPrint "mod")); 
val _=temp_add_user_printer ("pat_divappprint", ``App_pat Opapp (Var_global_pat 10) x``,genPrint (infixappPrint "div")); 
val _=temp_add_user_printer ("pat_timesappprint", ``App_pat Opapp (Var_global_pat 11) x``,genPrint (infixappPrint "*")); 
val _=temp_add_user_printer ("pat_minusappprint", ``App_pat Opapp (Var_global_pat 12) x``,genPrint (infixappPrint "-")); 
val _=temp_add_user_printer ("pat_addappprint", ``App_pat Opapp (Var_global_pat 13) x``,genPrint (infixappPrint "+"));
 
(*pat uops*)
val _=temp_add_user_printer ("pat_refappprint", ``App_pat Opapp (Var_global_pat 0) x``,genPrint (prefixappPrint "ref")); 
val _=temp_add_user_printer ("pat_derefappprint", ``App_pat Opapp (Var_global_pat 1) x``,genPrint (prefixappPrint "!"));
val _=temp_add_user_printer ("pat_negappprint", ``App_pat Opapp (Var_global_pat 2) x``,genPrint (prefixappPrint "~"));


end;


