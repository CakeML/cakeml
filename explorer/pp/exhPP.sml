structure exhPP=
struct
open astPP conPP modPP
(*exh_Init_global_var special case for Uapp_exh*)
val _=temp_add_user_printer("exh_initglobal",``Uapp_exh (Init_global_var_i2 n) x``,i2_initglobalPrint);

(*reuse i2 extend global*)
val _=temp_add_user_printer("exh_extendglobal",``Extend_global_exh n``,genPrint i2_extendglobalPrint);

(*exh_Pvar*)
val _=temp_add_user_printer ("exh_pvarprint", ``Pvar_exh x``, genPrint pvarPrint);

(*exh_Plit*)
val _=temp_add_user_printer("exh_plitprint", ``Plit_exh x``, genPrint plitPrint);


(*exh_Nested mutually recursive letrec*)
val _=temp_add_user_printer ("exh_letrecprint", ``Letrec_exh x y``,genPrint letrecPrint);

(*exh_Lambdas varN*expr *)
val _=temp_add_user_printer ("exh_lambdaprint", ``Fun_exh x y``,genPrint lambdaPrint);

(*exh_Inner Let SOME*)
val _=temp_add_user_printer ("exh_letvalprint", ``Let_exh (SOME x) y z``,genPrint letvalPrint);

(*exh_Inner Let NONE*)
val _=temp_add_user_printer ("exh_letnoneprint",``Let_exh NONE y z ``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)
val _=temp_add_user_printer ("exh_conprint", ``Con_exh x y``,i2_pconPrint);
val _=temp_add_user_printer ("exh_pconprint", ``Pcon_exh x y``,i2_pconPrint);

(*exh_Literals*)
(*exh_Pattern lit*)
val _=temp_add_user_printer ("exh_litprint", ``Lit_exh x``, genPrint plitPrint);
val _=temp_add_user_printer ("exh_unitprint", ``Lit_exh Unit``,genPrint unitPrint);

(*exh local Var name, no more long names*)
val _=temp_add_user_printer ("exh_varlocalprint", ``Var_local_exh x``,genPrint i1_varlocalPrint);

(*exh global Var name*)
val _=temp_add_user_printer ("exh_varglobalprint", ``Var_global_exh n``,i1_varglobalPrint);

(*exh_Matching*)
val _=temp_add_user_printer ("exh_matprint", ``Mat_exh x y``,genPrint matPrint);

(*exh_Apply*)
val _=temp_add_user_printer ("exh_oppappprint", ``App_exh Opapp f x``, genPrint oppappPrint);

(*exh_raise expr*) 
val _=temp_add_user_printer ("exh_raiseprint", ``Raise_exh x``,genPrint raisePrint);

(*exh_handle expr * list (pat*expr)*)
val _=temp_add_user_printer ("exh_handleprint", ``Handle_exh x y``,genPrint handlePrint);

(*exh_If-then-else*)
val _=temp_add_user_printer("exh_ifthenelseprint", ``If_exh x y z``,genPrint ifthenelsePrint);

val _=temp_add_user_printer("exh_truelitprint",``Lit_exh (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("exh_falselitprint",``Lit_exh (Bool F)``,genPrint (boolPrint "false"));

(*exh binops*)
val _=temp_add_user_printer ("exh_assignappprint", ``App_exh Opapp (Var_global_exh 3) x``,genPrint (infixappPrint ":=")); 
val _=temp_add_user_printer ("exh_eqappprint", ``App_exh Opapp (Var_global_exh 4) x``,genPrint (infixappPrint "=")); 
val _=temp_add_user_printer ("exh_gteqappprint", ``App_exh Opapp (Var_global_exh 5) x``,genPrint (infixappPrint ">=")); 
val _=temp_add_user_printer ("exh_lteqappprint", ``App_exh Opapp  (Var_global_exh 6) x``,genPrint (infixappPrint "<=")); 
val _=temp_add_user_printer ("exh_gtappprint", ``App_exh Opapp (Var_global_exh 7) x``,genPrint (infixappPrint ">")); 
val _=temp_add_user_printer ("exh_ltappprint", ``App_exh Opapp (Var_global_exh 8) x``,genPrint (infixappPrint "<")); 
val _=temp_add_user_printer ("exh_modappprint", ``App_exh Opapp (Var_global_exh 9) x``,genPrint (infixappPrint "mod")); 
val _=temp_add_user_printer ("exh_divappprint", ``App_exh Opapp (Var_global_exh 10) x``,genPrint (infixappPrint "div")); 
val _=temp_add_user_printer ("exh_timesappprint", ``App_exh Opapp (Var_global_exh 11) x``,genPrint (infixappPrint "*")); 
val _=temp_add_user_printer ("exh_minusappprint", ``App_exh Opapp (Var_global_exh 12) x``,genPrint (infixappPrint "-")); 
val _=temp_add_user_printer ("exh_addappprint", ``App_exh Opapp (Var_global_exh 13) x``,genPrint (infixappPrint "+"));
 
(*exh uops*)
val _=temp_add_user_printer ("exh_refappprint", ``App_exh Opapp (Var_global_exh 0) x``,genPrint (prefixappPrint "ref")); 
val _=temp_add_user_printer ("exh_derefappprint", ``App_exh Opapp (Var_global_exh 1) x``,genPrint (prefixappPrint "!"));
val _=temp_add_user_printer ("exh_negappprint", ``App_exh Opapp (Var_global_exh 2) x``,genPrint (prefixappPrint "~"));

end;
