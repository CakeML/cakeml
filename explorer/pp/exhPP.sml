(*Pretty printing for exhLang*)
structure exhPP=
struct
open astPP conPP modPP

val exhPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

fun add_exhPP hd = exhPrettyPrinters:= (hd:: !exhPrettyPrinters)

(*exh_Init_global_var special case*)
val _=add_exhPP("exh_initglobal",``App_exh (Init_global_var_i2 n) x``,i2_initglobalPrint);

(*reuse i2 extend global*)
val _=add_exhPP("exh_extendglobal",``Extend_global_exh n``,genPrint i2_extendglobalPrint);

(*exh_Pvar*)
val _=add_exhPP ("exh_pvarprint", ``Pvar_exh x``, genPrint pvarPrint);

(*exh_Plit*)
val _=add_exhPP("exh_plitprint", ``Plit_exh x``, genPrint plitPrint);


(*exh_Nested mutually recursive letrec*)
val _=add_exhPP ("exh_letrecprint", ``Letrec_exh x y``,genPrint letrecPrint);

(*exh_Lambdas varN*expr *)
val _=add_exhPP ("exh_lambdaprint", ``Fun_exh x y``,genPrint lambdaPrint);

(*exh_Inner Let SOME*)
val _=add_exhPP ("exh_letvalprint", ``Let_exh (SOME x) y z``,genPrint letvalPrint);

(*exh_Inner Let NONE*)
val _=add_exhPP ("exh_letnoneprint",``Let_exh NONE y z ``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)
val _=add_exhPP ("exh_conprint", ``Con_exh x y``,i2_pconPrint);
val _=add_exhPP ("exh_pconprint", ``Pcon_exh x y``,i2_pconPrint);

(*exh_Literals*)
(*exh_Pattern lit*)
val _=add_exhPP ("exh_litprint", ``Lit_exh x``, genPrint plitPrint);
val _=add_exhPP ("exh_unitprint", ``Lit_exh Unit``,genPrint unitPrint);

(*exh local Var name, no more long names*)
val _=add_exhPP ("exh_varlocalprint", ``Var_local_exh x``,genPrint i1_varlocalPrint);

(*exh global Var name*)
val _=add_exhPP ("exh_varglobalprint", ``Var_global_exh n``,i1_varglobalPrint);

(*exh_Matching*)
val _=add_exhPP ("exh_matprint", ``Mat_exh x y``,genPrint matPrint);

(*exh_Apply*)
val _=add_exhPP ("exh_oppappprint", ``App_exh (Op_i2 Opapp) ls``, genPrint oppappPrint);

(*exh_raise expr*) 
val _=add_exhPP ("exh_raiseprint", ``Raise_exh x``,genPrint raisePrint);

(*exh_handle expr * list (pat*expr)*)
val _=add_exhPP ("exh_handleprint", ``Handle_exh x y``,genPrint handlePrint);

(*exh_If-then-else*)
val _=add_exhPP("exh_ifthenelseprint", ``If_exh x y z``,genPrint ifthenelsePrint);

val _=add_exhPP("exh_truelitprint",``Lit_exh (Bool T)``,genPrint (boolPrint "true"));
val _=add_exhPP("exh_falselitprint",``Lit_exh (Bool F)``,genPrint (boolPrint "false"));

(*exh binops*)
val _=add_exhPP ("exh_assignappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 10; x]``,genPrint (infixappPrint ":=")); 
val _=add_exhPP ("exh_eqappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 9; x]``,genPrint (infixappPrint "=")); 
val _=add_exhPP ("exh_gteqappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 8; x]``,genPrint (infixappPrint ">=")); 
val _=add_exhPP ("exh_lteqappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 7; x]``,genPrint (infixappPrint "<=")); 
val _=add_exhPP ("exh_gtappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 6; x]``,genPrint (infixappPrint ">")); 
val _=add_exhPP ("exh_ltappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 5; x]``,genPrint (infixappPrint "<")); 
val _=add_exhPP ("exh_modappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 4; x]``,genPrint (infixappPrint "mod")); 
val _=add_exhPP ("exh_divappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 3; x]``,genPrint (infixappPrint "div")); 
val _=add_exhPP ("exh_timesappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 2; x]``,genPrint (infixappPrint "*")); 
val _=add_exhPP ("exh_minusappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 1; x]``,genPrint (infixappPrint "-")); 
val _=add_exhPP ("exh_addappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 0; x]``,genPrint (infixappPrint "+")); 

(*exh uops*)
val _=add_exhPP ("exh_refappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 13; x]``,genPrint (prefixappPrint "ref")); 
val _=add_exhPP ("exh_derefappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 12;x]``,genPrint (prefixappPrint "!"));
val _=add_exhPP ("exh_negappprint", ``App_exh (Op_i2 Opapp) [Var_global_exh 11; x]``,genPrint (prefixappPrint "~"));

fun enable_exhPP_verbose () = map temp_add_user_printer (!exhPrettyPrinters); 
fun enable_exhPP () = (enable_exhPP_verbose();())
fun disable_exhPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!exhPrettyPrinters);
fun disable_exhPP () = (disable_exhPP_verbose();());

end;
