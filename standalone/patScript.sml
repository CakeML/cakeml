(*pat_Init_global_var special case for Uapp_pat*)
temp_add_user_printer("pat_initglobal",``Uapp_pat (Init_global_var_i2 n) x``,genPrint i2_initglobalPrint);

(*reuse i2 extend global*)
temp_add_user_printer("pat_extendglobal",``Extend_global_pat n``,genPrint i2_extendglobalPrint);

(*pat_prompt*)
temp_add_user_printer("pat_promptnoneprint",``Prompt_pat x``,genPrint i1_promptNonePrint);

(*pat_Pvar*)
temp_add_user_printer ("pat_pvarprint", ``Pvar_pat x``, genPrint pvarPrint);

(*pat_Plit*)
temp_add_user_printer("pat_plitprint", ``Plit_pat x``, genPrint plitPrint);


(*pat_Nested mutually recursive letrec*)
temp_add_user_printer ("pat_letrecprint", ``Letrec_pat x y``,genPrint letrecPrint);

(*pat_Lambdas varN*expr *)
temp_add_user_printer ("pat_lambdaprint", ``Fun_pat x y``,genPrint lambdaPrint);

(*pat_Let*)
fun pat_letpatPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"let (">>blk CONSISTENT 0 (sys(Top,Top,Top) d (strip l) >>str ") =">> brk(1,0) >>str"(">> sys (Top,Top,Top) d r) >>str ")">>add_newline>>str"endlet"
  end;

temp_add_user_printer ("pat_letprint",``Let_pat y z ``,genPrint pat_letpatPrint);

(*Prints all constructor args in a list comma separated*)
temp_add_user_printer ("pat_conprint", ``Con_pat x y``,genPrint i2_pconPrint);

(*pat_sequence*)
fun pat_seqPrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"(">>sys(Top,Top,Top) d (strip l) >>str ";" >> sys (Top,Top,Top) d r >>str ")"
  end;
temp_add_user_printer ("pat_seqprint",``Seq_pat x y``,genPrint pat_seqPrint);


(*pat_Literals*)
(*pat_Pattern lit*)
temp_add_user_printer ("pat_litprint", ``Lit_pat x``, genPrint plitPrint);
temp_add_user_printer ("pat_unitprint", ``Lit_pat Unit``,genPrint unitPrint);

(*pat local var name debrujin indices*)
fun pat_varlocalPrint sys d t Top str brk blk =
    str"_l_">>sys (Top,Top,Top) d (strip t);
temp_add_user_printer ("pat_varlocalprint", ``Var_local_pat x``,genPrint pat_varlocalPrint);

(*pat global Var name*)
temp_add_user_printer ("pat_varglobalprint", ``Var_global_pat n``,genPrint i1_varglobalPrint);

(*pat_Apply*)
temp_add_user_printer ("pat_oppappprint", ``App_pat Opapp f x``, genPrint oppappPrint);

(*pat_raise expr*) 
temp_add_user_printer ("pat_raiseprint", ``Raise_pat x``,genPrint raisePrint);

(*pat_handle expr * expr*)
fun pat_handlePrint sys d t Top str brk blk =
  let val (l,r) = dest_comb t
  in
    str"handle ">>sys(Top,Top,Top) d (strip l) >>str "=>" >> sys (Top,Top,Top) d r
  end;

temp_add_user_printer ("pat_handleprint", ``Handle_pat x y``,genPrint pat_handlePrint);

(*pat_If-then-else*)
temp_add_user_printer("pat_ifthenelseprint", ``If_pat x y z``,genPrint ifthenelsePrint);


