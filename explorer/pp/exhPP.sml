(*Pretty printing for exhLang*)
structure exhPP=
struct
open astPP modPP conPP exhLangTheory

val _ = bring_fwd_ctors "exhLang" ``:exhLang$pat``
val _ = bring_fwd_ctors "exhLang" ``:exhLang$exp``

val exhPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

fun add_exhPP hd = exhPrettyPrinters:= (hd:: !exhPrettyPrinters)

(*exh_Init_global_var special case*)
val _=add_exhPP("exh_initglobal",``App (Init_global_var n) x``,con_initglobalPrint);

(*reuse con extend global*)
val _=add_exhPP("exh_extendglobal",``Extend_global n``,genPrint con_extendglobalPrint);

(*exh_Pvar*)
val _=add_exhPP ("exh_pvarprint", ``Pvar x``, genPrint pvarPrint);

(*exh_Plit*)
val _=add_exhPP("exh_plitprint", ``Plit x``, genPrint plitPrint);


(*exh_Nested mutually recursive letrec*)
val _=add_exhPP ("exh_letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*exh_Lambdas varN*expr *)
val _=add_exhPP ("exh_lambdaprint", ``Fun x y``,genPrint lambdaPrint);

(*exh_Inner Let SOME*)
val _=add_exhPP ("exh_letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);

(*exh_Inner Let NONE*)
val _=add_exhPP ("exh_letnoneprint",``Let NONE y z ``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)
val _=add_exhPP ("exh_conprint", ``Con x y``,con_pconPrint);
val _=add_exhPP ("exh_pconprint", ``Pcon x y``,con_pconPrint);

(*exh_Literals*)
(*exh_Pattern lit*)
val _=add_exhPP ("exh_litprint", ``Lit x``, genPrint plitPrint);

(*exh local Var name, no more long names*)
val _=add_exhPP ("exh_varlocalprint", ``Var_local x``,genPrint mod_varlocalPrint);

(*exh global Var name*)
val _=add_exhPP ("exh_varglobalprint", ``Var_global n``,mod_varglobalPrint);

(*exh_Matching*)
val _=add_exhPP ("exh_matprint", ``Mat x y``,genPrint matPrint);

(*exh_Apply*)
val _=add_exhPP ("exh_oppappprint", ``App (Op Opapp) ls``, genPrint oppappPrint);

(*exh_raise expr*)
val _=add_exhPP ("exh_raiseprint", ``Raise x``,genPrint raisePrint);

(*exh_handle expr * list (pat*expr)*)
val _=add_exhPP ("exh_handleprint", ``Handle x y``,genPrint handlePrint);

(*exh_If-then-else*)
val _=add_exhPP("exh_ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);

(*exh binops*)
val _=add_exhPP ("exh_assignappprint", ``App (Op Opapp) [Var_global 10; x]``,genPrint (infixappPrint ":="));
val _=add_exhPP ("exh_eqappprint", ``App (Op Opapp) [Var_global 9; x]``,genPrint (infixappPrint "="));
val _=add_exhPP ("exh_gteqappprint", ``App (Op Opapp) [Var_global 8; x]``,genPrint (infixappPrint ">="));
val _=add_exhPP ("exh_lteqappprint", ``App (Op Opapp) [Var_global 7; x]``,genPrint (infixappPrint "<="));
val _=add_exhPP ("exh_gtappprint", ``App (Op Opapp) [Var_global 6; x]``,genPrint (infixappPrint ">"));
val _=add_exhPP ("exh_ltappprint", ``App (Op Opapp) [Var_global 5; x]``,genPrint (infixappPrint "<"));
val _=add_exhPP ("exh_modappprint", ``App (Op Opapp) [Var_global 4; x]``,genPrint (infixappPrint "mod"));
val _=add_exhPP ("exh_divappprint", ``App (Op Opapp) [Var_global 3; x]``,genPrint (infixappPrint "div"));
val _=add_exhPP ("exh_timesappprint", ``App (Op Opapp) [Var_global 2; x]``,genPrint (infixappPrint "*"));
val _=add_exhPP ("exh_minusappprint", ``App (Op Opapp) [Var_global 1; x]``,genPrint (infixappPrint "-"));
val _=add_exhPP ("exh_addappprint", ``App (Op Opapp) [Var_global 0; x]``,genPrint (infixappPrint "+"));

(*exh uops*)
val _=add_exhPP ("exh_refappprint", ``App (Op Opapp) [Var_global 13; x]``,genPrint (prefixappPrint "ref"));
val _=add_exhPP ("exh_derefappprint", ``App (Op Opapp) [Var_global 12;x]``,genPrint (prefixappPrint "!"));
val _=add_exhPP ("exh_negappprint", ``App (Op Opapp) [Var_global 11; x]``,genPrint (prefixappPrint "~"));

fun enable_exhPP_verbose () = map temp_add_user_printer (!exhPrettyPrinters);
fun enable_exhPP () = (enable_exhPP_verbose();())
fun disable_exhPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!exhPrettyPrinters);
fun disable_exhPP () = (disable_exhPP_verbose();());

end;
