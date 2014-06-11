(*i2_prompt*)
temp_add_user_printer("i2_promptnoneprint",``Prompt_i2 x``,genPrint i1_promptNonePrint);

(*i2_Pvar*)
temp_add_user_printer ("i2_pvarprint", ``Pvar_i2 x``, genPrint pvarPrint);

(*i2_Plit*)
temp_add_user_printer("i2_plitprint", ``Plit_i2 x``, genPrint plitPrint);


(*i2_Top level letrec list varN*varN*exp -- Only strip once *)
temp_add_user_printer ("i2_dletrecprint", ``Dletrec_i2 x``, genPrint dletrecPrint);

(*i2_Nested mutually recursive letrec*)
temp_add_user_printer ("i2_letrecprint", ``Letrec_i2 x y``,genPrint letrecPrint);

(*i2_Lambdas varN*expr *)
temp_add_user_printer ("i2_lambdaprint", ``Fun_i2 x y``,genPrint lambdaPrint);

(*TODO Toplevel Dlet nat*expr *)
temp_add_user_printer ("i2_dletvalprint", ``Dlet_i2 x y``,genPrint i1_dletvalPrint);

(*i2_Inner Let SOME*)
temp_add_user_printer ("i2_letvalprint", ``Let_i2 (SOME x) y z``,genPrint letvalPrint);

(*Prints all constructor args in a list comma separated*)

(*i2 Con, reuse AST CON NONE*)
fun i2_pconPrint sys d t Top str brk blk =
  let
    val (_,name) = dest_comb (rator t)
  in
    sys (Top,Top,Top) d name >> pconPrint sys d t Top str brk blk
  end;
temp_add_user_printer ("i2_conprint", ``Con_i2 x y``,genPrint i2_pconPrint);
temp_add_user_printer ("i2_pconprint", ``Pcon_i2 x y``,genPrint i2_pconPrint);
(*i2_Literals*)
(*i2_Pattern lit*)
temp_add_user_printer ("i2_litprint", ``Lit_i2 x``, genPrint plitPrint);
temp_add_user_printer ("i2_unitprint", ``Lit_i2 Unit``,genPrint unitPrint);

(*i2 local Var name, no more long names*)
temp_add_user_printer ("i2_varlocalprint", ``Var_local_i2 x``,genPrint i1_varlocalPrint);

(*i2 global Var name*)
temp_add_user_printer ("i2_varglobalprint", ``Var_global_i2 n``,genPrint i1_varglobalPrint);

(*i2_Matching*)
temp_add_user_printer ("i2_matprint", ``Mat_i2 x y``,genPrint matPrint);

(*i2_Apply*)
temp_add_user_printer ("i2_oppappprint", ``App_i2 Opapp f x``, genPrint oppappPrint);

(*i2_raise expr*) 
temp_add_user_printer ("i2_raiseprint", ``Raise_i2 x``,genPrint raisePrint);

(*i2_handle expr * list (pat*expr)*)
temp_add_user_printer ("i2_handleprint", ``Handle_i2 x y``,genPrint handlePrint);

(*i2_If-then-else*)
temp_add_user_printer("i2_ifthenelseprint", ``If_i2 x y z``,genPrint ifthenelsePrint);
