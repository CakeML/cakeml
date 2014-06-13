(*i1_Unnamed Prompts NONE => declist*)
fun i1_promptNonePrint sys d t Top str brk blk=
  let
    val (_,ls) = dest_comb t
    fun printAll [] = str""
    |   printAll (x::xs) = sys (Top,Top,Top) (d-1) x >> add_newline
  in
    add_newline>>blk CONSISTENT 0 (
    str "prompt {">>printAll (#1(listSyntax.dest_list ls))>>str "}")
  end;

temp_add_user_printer("i1_promptnoneprint",``Prompt_i1 NONE x``,genPrint i1_promptNonePrint);

(*Named Prompt SOME => declist TODO*)

(*i1_Top level exceptions*)
(*DExn with moduel names TODO*)
(*Unwrap the term*)
fun i1_dexnPrint sys d t Top str brk blk =
  dexnPrint sys d ``Dexn ^(rand (rator t)) ^(rand t)`` Top str brk blk;

temp_add_user_printer ("i1_dexnprint", ``Dexn_i1 NONE x y``,genPrint i1_dexnPrint);

(*i1_Top level datatypes list(list tvarN *typeN * list ... ) *)

temp_add_user_printer ("i1_dtypeprint", ``Dtype_i1 NONE x``,genPrint dtypePrint);

(*Dtype with module names TODO*)


(*i1_Top level letrec list varN*varN*exp -- Only strip once *)
temp_add_user_printer ("i1_dletrecprint", ``Dletrec_i1 x``, genPrint dletrecPrint);

(*i1_Nested mutually recursive letrec*)

temp_add_user_printer ("i1_letrecprint", ``Letrec_i1 x y``,genPrint letrecPrint);

(*i1_Lambdas varN*expr *)
temp_add_user_printer ("i1_lambdaprint", ``Fun_i1 x y``,genPrint lambdaPrint);

(*TODO Toplevel Dlet nat*expr *)
fun i1_dletvalPrint sys d t Top str brk blk=
  let
    val (_,[l,r]) = strip_comb t;
  in
    add_newline>> sys (Top,Top,Top) (d-1) l >>str " var_binding">>add_newline 
    >>sys (Top,Top,Top) (d-1) r
  end;

temp_add_user_printer ("i1_dletvalprint", ``Dlet_i1 x y``,genPrint i1_dletvalPrint);

(*i1_Inner Let SOME*)
temp_add_user_printer ("i1_letvalprint", ``Let_i1 (SOME x) y z``,genPrint letvalPrint);

(*i1_Inner Let NONE*)
temp_add_user_printer ("i1_letnoneprint", ``Let_i1 NONE y z``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
temp_add_user_printer ("i1_conprint", ``Con_i1 NONE x``,genPrint pconPrint);

(*i1_Con SOME*)
temp_add_user_printer ("i1_consomeprint", ``Con_i1 (Some x) y``,genPrint pconsomePrint);

temp_add_user_printer ("i1_connilprint",``Con_i1 (SOME (Short "nil")) y``,genPrint pconnilPrint);

(*i1_Literals*)
(*i1_Pattern lit*)
temp_add_user_printer ("i1_litprint", ``Lit_i1 x``, genPrint plitPrint);
temp_add_user_printer ("i1_unitprint", ``Lit_i1 Unit``,genPrint unitPrint);

(*i1 local Var name, no more long names*)
fun i1_varlocalPrint sys d t Top str brk blk =
    str (stringSyntax.fromHOLstring (strip t));

temp_add_user_printer ("i1_varlocalprint", ``Var_local_i1 x``,genPrint i1_varlocalPrint);

(*i1 global Var name*)
fun i1_varglobalPrint sys d t Top str brk blk =
    str"g_">>sys (Top,Top,Top) d (strip t);

temp_add_user_printer ("i1_varglobalprint", ``Var_global_i1 n``,genPrint i1_varglobalPrint);

(*i1_Matching*)
temp_add_user_printer ("i1_matprint", ``Mat_i1 x y``,genPrint matPrint);

(*i1_Apply*)
temp_add_user_printer ("i1_oppappprint", ``App_i1 Opapp f x``, genPrint oppappPrint);

(*i1_raise expr*) 
temp_add_user_printer ("i1_raiseprint", ``Raise_i1 x``,genPrint raisePrint);

(*i1_handle expr * list (pat*expr)*)
temp_add_user_printer ("i1_handleprint", ``Handle_i1 x y``,genPrint handlePrint);

(*i1_If-then-else*)
temp_add_user_printer("i1_ifthenelseprint", ``If_i1 x y z``,genPrint ifthenelsePrint);

temp_add_user_printer ("i1_assignappprint", ``App_i1 Opapp (Var_global_i1 3) x``,genPrint (infixappPrint ":=")); 
temp_add_user_printer ("i1_eqappprint", ``App_i1 Opapp (Var_global_i1 4) x``,genPrint (infixappPrint "=")); 
temp_add_user_printer ("i1_gteqappprint", ``App_i1 Opapp (Var_global_i1 5) x``,genPrint (infixappPrint ">=")); 
temp_add_user_printer ("i1_lteqappprint", ``App_i1 Opapp  (Var_global_i1 6) x``,genPrint (infixappPrint "<=")); 
temp_add_user_printer ("i1_gtappprint", ``App_i1 Opapp (Var_global_i1 7) x``,genPrint (infixappPrint ">")); 
temp_add_user_printer ("i1_ltappprint", ``App_i1 Opapp (Var_global_i1 8) x``,genPrint (infixappPrint "<")); 
temp_add_user_printer ("i1_modappprint", ``App_i1 Opapp (Var_global_i1 9) x``,genPrint (infixappPrint "mod")); 
temp_add_user_printer ("i1_divappprint", ``App_i1 Opapp (Var_global_i1 10) x``,genPrint (infixappPrint "div")); 
temp_add_user_printer ("i1_timesappprint", ``App_i1 Opapp (Var_global_i1 11) x``,genPrint (infixappPrint "*")); 
temp_add_user_printer ("i1_minusappprint", ``App_i1 Opapp (Var_global_i1 12) x``,genPrint (infixappPrint "-")); 
temp_add_user_printer ("i1_addappprint", ``App_i1 Opapp (Var_global_i1 13) x``,genPrint (infixappPrint "+"));
 
