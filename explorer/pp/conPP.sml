structure conPP =
struct
open astPP modPP
(*i2_Init_global_var special case for Uapp_i2*)
fun i2_initglobalPrint sys d t Top str brk blk =
  let
    val (t,x) = dest_comb t
    val num = rand (rand t)
  in
    str"g_" >> sys (Top,Top,Top) (d-1) num >>str " := " >> blk CONSISTENT 0 (sys (Top,Top,Top) (d-1) x)
  end;

val _=temp_add_user_printer("i2_initglobal",``Uapp_i2 (Init_global_var_i2 n) x``,genPrint i2_initglobalPrint);

(*i2_extend_global creates n top level decls*)
fun i2_extendglobalPrint sys d t Top str brk blk =
  let
    val n = rand t
  in
    str"extend_global ">>sys (Top,Top,Top) d n
  end;

val _=temp_add_user_printer("i2_extendglobal",``Extend_global_i2 n``,genPrint i2_extendglobalPrint);

(*i2_prompt*)
fun i2_promptPrint sys d t Top str brk blk=
  let
    val (_,ls) = dest_comb t
    fun printAll [] = str""
    |   printAll [x] = sys (Top,Top,Top) d x
    |   printAll (x::xs) = sys (Top,Top,Top) (d-1) x >>printAll xs
  in
    add_newline>>blk CONSISTENT 2 (
    str "prompt {">>printAll (#1(listSyntax.dest_list ls)))>>add_newline>>str "}"
  end;
val _=temp_add_user_printer("i2_promptprint",``Prompt_i2 x``,genPrint (i2_promptPrint));

(*i2_Pvar*)
val _=temp_add_user_printer ("i2_pvarprint", ``Pvar_i2 x``, genPrint pvarPrint);

(*i2_Plit*)
val _=temp_add_user_printer("i2_plitprint", ``Plit_i2 x``, genPrint plitPrint);


(*i2_Top level letrec list varN*varN*exp -- Only strip once *)
val _=temp_add_user_printer ("i2_dletrecprint", ``Dletrec_i2 x``, genPrint dletrecPrint);

(*i2_Nested mutually recursive letrec*)
val _=temp_add_user_printer ("i2_letrecprint", ``Letrec_i2 x y``,genPrint letrecPrint);

(*i2_Lambdas varN*expr *)
val _=temp_add_user_printer ("i2_lambdaprint", ``Fun_i2 x y``,genPrint lambdaPrint);

(*i2_Toplevel Dlet nat*expr *)
val _=temp_add_user_printer ("i2_dletvalprint", ``Dlet_i2 x y``,genPrint i1_dletvalPrint);

(*i2_Inner Let SOME*)
val _=temp_add_user_printer ("i2_letvalprint", ``Let_i2 (SOME x) y z``,genPrint letvalPrint);

(*i2_Inner Let NONE*)
(*Instead of printing let val _ = in i2, just print the RHS*)

fun i2_letnonePrint sys d t Top str brk blk =
  let
    val (t,body) = dest_comb t
    val (t,eq) = dest_comb t
  in
    (blk CONSISTENT 0 (
    (sys (Top,Top,Top) d eq) >> add_newline 
    >> str"in " >> (sys (Top,Top,Top) d body) >> add_newline
    >> str"end" ))
  end;

val _=temp_add_user_printer ("i2_letnoneprint", ``Let_i2 NONE y z``,genPrint i2_letnonePrint);

val _=temp_add_user_printer ("i2_letnoneprint",``Let_i2 NONE y z ``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)

(*i2 Con, reuse AST CON NONE*)
fun i2_pconPrint sys d t Top str brk blk =
  let
    val (_,name) = dest_comb (rator t)
    val (x::_) = pairSyntax.strip_pair name
  in
    (*TODO: Fix this*)
    str "c_" >> sys (Top,Top,Top) d x >> (pconPrint sys d t Top str brk blk)
  end;

val _=temp_add_user_printer ("i2_conprint", ``Con_i2 x y``,genPrint i2_pconPrint);
val _=temp_add_user_printer ("i2_pconprint", ``Pcon_i2 x y``,genPrint i2_pconPrint);

(*i2_Literals*)
(*i2_Pattern lit*)
val _=temp_add_user_printer ("i2_litprint", ``Lit_i2 x``, genPrint plitPrint);
val _=temp_add_user_printer ("i2_unitprint", ``Lit_i2 Unit``,genPrint unitPrint);

(*i2 local Var name, no more long names*)
val _=temp_add_user_printer ("i2_varlocalprint", ``Var_local_i2 x``,genPrint i1_varlocalPrint);

(*i2 global Var name*)
val _=temp_add_user_printer ("i2_varglobalprint", ``Var_global_i2 n``,genPrint i1_varglobalPrint);

(*i2_Matching*)
val _=temp_add_user_printer ("i2_matprint", ``Mat_i2 x y``,genPrint matPrint);

(*i2_Apply*)
val _=temp_add_user_printer ("i2_oppappprint", ``App_i2 Opapp f x``, genPrint oppappPrint);

(*i2_raise expr*) 
val _=temp_add_user_printer ("i2_raiseprint", ``Raise_i2 x``,genPrint raisePrint);

(*i2_handle expr * list (pat*expr)*)
val _=temp_add_user_printer ("i2_handleprint", ``Handle_i2 x y``,genPrint handlePrint);

(*i2_If-then-else*)
val _=temp_add_user_printer("i2_ifthenelseprint", ``If_i2 x y z``,genPrint ifthenelsePrint);

val _=temp_add_user_printer("i2_truelitprint",``Lit_i2 (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("i2_falselitprint",``Lit_i2 (Bool F)``,genPrint (boolPrint "false"));

(*i2 binops*)
val _=temp_add_user_printer ("i2_assignappprint", ``App_i2 Opapp (Var_global_i2 3) x``,genPrint (infixappPrint ":=")); 
val _=temp_add_user_printer ("i2_eqappprint", ``App_i2 Opapp (Var_global_i2 4) x``,genPrint (infixappPrint "=")); 
val _=temp_add_user_printer ("i2_gteqappprint", ``App_i2 Opapp (Var_global_i2 5) x``,genPrint (infixappPrint ">=")); 
val _=temp_add_user_printer ("i2_lteqappprint", ``App_i2 Opapp  (Var_global_i2 6) x``,genPrint (infixappPrint "<=")); 
val _=temp_add_user_printer ("i2_gtappprint", ``App_i2 Opapp (Var_global_i2 7) x``,genPrint (infixappPrint ">")); 
val _=temp_add_user_printer ("i2_ltappprint", ``App_i2 Opapp (Var_global_i2 8) x``,genPrint (infixappPrint "<")); 
val _=temp_add_user_printer ("i2_modappprint", ``App_i2 Opapp (Var_global_i2 9) x``,genPrint (infixappPrint "mod")); 
val _=temp_add_user_printer ("i2_divappprint", ``App_i2 Opapp (Var_global_i2 10) x``,genPrint (infixappPrint "div")); 
val _=temp_add_user_printer ("i2_timesappprint", ``App_i2 Opapp (Var_global_i2 11) x``,genPrint (infixappPrint "*")); 
val _=temp_add_user_printer ("i2_minusappprint", ``App_i2 Opapp (Var_global_i2 12) x``,genPrint (infixappPrint "-")); 
val _=temp_add_user_printer ("i2_addappprint", ``App_i2 Opapp (Var_global_i2 13) x``,genPrint (infixappPrint "+"));
 
(*i2 uops*)
val _=temp_add_user_printer ("i2_refappprint", ``App_i2 Opapp (Var_global_i2 0) x``,genPrint (prefixappPrint "ref")); 
val _=temp_add_user_printer ("i2_derefappprint", ``App_i2 Opapp (Var_global_i2 1) x``,genPrint (prefixappPrint "!"));
val _=temp_add_user_printer ("i2_negappprint", ``App_i2 Opapp (Var_global_i2 2) x``,genPrint (prefixappPrint "~"));

(*i2 list form*)
val _=temp_add_user_printer("i2listprint",``x:prompt_i2 store``,genPrint astlistPrint);
end;
