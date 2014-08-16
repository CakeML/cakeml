structure modPP =
struct
open astPP
(*Extracts the module prefix if any*)
fun modoptionString t=
  if optionSyntax.is_some t then toString (rand t) else "";

(*i1_ Prompts opt => declist*)
fun i1_promptPrint sys d t pg str brk blk=
  let
    val (t,ls) = dest_comb t
    val (_,opt) = dest_comb t
    val opt = modoptionString opt
    fun printAll [] = str""
    |   printAll [x] = sys (pg,pg,pg) d x
    |   printAll (x::xs) = sys (pg,pg,pg) (d-1) x >>printAll xs
  in
    add_newline>>blk CONSISTENT 2 (
    str (if opt="" then "prompt" else opt) >> str" {">>printAll (#1(listSyntax.dest_list ls)))>>add_newline>>str "}"
  end;

val _=temp_add_user_printer("i1_promptprint",``Prompt_i1 opt x``,genPrint i1_promptPrint);

(*i1_pg level exceptions*)
(*DExn with module names TODO*)
(*Unwrap the term*)
fun i1_dexnPrint sys d t pg str brk blk =
  let val opt = (t|> rator|>rator|>rand)
  in
    (dexnPrint (modoptionString opt) sys d ``Dexn ^(rand (rator t)) ^(rand t)`` pg str brk blk)
  end;

val _=temp_add_user_printer ("i1_dexnprint", ``Dexn_i1 opt x y``,genPrint i1_dexnPrint);

(*i1_pg level datatypes list(list tvarN *typeN * list ... ) *)

fun i1_dtypePrint sys d t pg str brk blk =
  let val opt = (t |> rator)|> rand
  in
     (dtypePrint (modoptionString opt) sys d t pg str brk blk)
  end;

val _=temp_add_user_printer ("i1_dtypeprint", ``Dtype_i1 opt x``,genPrint i1_dtypePrint);

(*val _=temp_add_user_printer ("i1_dtypesomeprint", ``Dtype_i1 SOME *)

(*i1_pg level letrec list varN*varN*exp -- Only strip once *)
val _=temp_add_user_printer ("i1_dletrecprint", ``Dletrec_i1 x``, genPrint dletrecPrint);

(*i1_Nested mutually recursive letrec*)

val _=temp_add_user_printer ("i1_letrecprint", ``Letrec_i1 x y``,genPrint letrecPrint);

(*i1_Lambdas varN*expr *)
val _=temp_add_user_printer ("i1_lambdaprint", ``Fun_i1 x y``,genPrint lambdaPrint);

(*i1_ pglevel Dlet nat*expr *)
fun i1_dletvalPrint sys d t pg str brk blk=
  let
    val (_,[l,r]) = strip_comb t;
  in
    add_newline>> blk CONSISTENT 2 (sys (pg,pg,pg) (d-1) l >>str " var_binding">>add_newline 
    >>sys (pg,pg,pg) (d-1) r)
  end;

val _=temp_add_user_printer ("i1_dletvalprint", ``Dlet_i1 x y``,genPrint i1_dletvalPrint);

(*i1_Inner Let SOME*)
val _=temp_add_user_printer ("i1_letvalprint", ``Let_i1 (SOME x) y z``,genPrint letvalPrint);

(*i1_Inner Let NONE*)
val _=temp_add_user_printer ("i1_letnoneprint", ``Let_i1 NONE y z``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
val _=temp_add_user_printer ("i1_conprint", ``Con_i1 NONE x``,genPrint pconPrint);

(*i1_Con SOME*)
val _=temp_add_user_printer ("i1_consomeprint", ``Con_i1 (Some x) y``,genPrint pconsomePrint);

val _=temp_add_user_printer ("i1_connilprint",``Con_i1 (SOME (Short "nil")) y``,genPrint pconnilPrint);

(*i1_Literals*)
(*i1_Pattern lit*)
val _=temp_add_user_printer ("i1_litprint", ``Lit_i1 x``, genPrint plitPrint);
val _=temp_add_user_printer ("i1_unitprint", ``Lit_i1 Unit``,genPrint unitPrint);

(*i1 local Var name, no more long names*)
fun i1_varlocalPrint sys d t pg str brk blk =
    str (toString (strip t));

val _=temp_add_user_printer ("i1_varlocalprint", ``Var_local_i1 x``,genPrint i1_varlocalPrint);

(*i1 global Var name*)
fun i1_varglobalPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
  in
    sty [FG DarkBlue] (str"g">>sys (Top,Top,Top) d (strip t))
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*
fun i1_varglobalPrint sys d t pg str brk blk =
    str"g_">>sys (pg,pg,pg) d (strip t);*)

val _=temp_add_user_printer ("i1_varglobalprint", ``Var_global_i1 n``,i1_varglobalPrint);

(*i1_Matching*)
val _=temp_add_user_printer ("i1_matprint", ``Mat_i1 x y``,genPrint matPrint);

(*i1_Apply*)
val _=temp_add_user_printer ("i1_oppappprint", ``App_i1 Opapp ls``, genPrint oppappPrint);

(*i1_raise expr*) 
val _=temp_add_user_printer ("i1_raiseprint", ``Raise_i1 x``,genPrint raisePrint);

(*i1_handle expr * list (pat*expr)*)
val _=temp_add_user_printer ("i1_handleprint", ``Handle_i1 x y``,genPrint handlePrint);

(*i1_If-then-else*)
val _=temp_add_user_printer("i1_ifthenelseprint", ``If_i1 x y z``,genPrint ifthenelsePrint);

fun prefixappPrint uop sys d t pg str brk blk =
  let
    val (_,ls) = dest_comb t
    val [_,x] = #1(listSyntax.dest_list ls)
  in
    m_brack str pg ( str uop >>str " " >> sys (pg,pg,pg) d x)
  end;

(*i1 binops*)
val _=temp_add_user_printer ("i1_assignappprint", ``App_i1 Opapp [Var_global_i1 3; x]``,genPrint (infixappPrint ":=")); 
val _=temp_add_user_printer ("i1_eqappprint", ``App_i1 Opapp [Var_global_i1 4; x]``,genPrint (infixappPrint "=")); 
val _=temp_add_user_printer ("i1_gteqappprint", ``App_i1 Opapp [Var_global_i1 5; x]``,genPrint (infixappPrint ">=")); 
val _=temp_add_user_printer ("i1_lteqappprint", ``App_i1 Opapp [Var_global_i1 6; x]``,genPrint (infixappPrint "<=")); 
val _=temp_add_user_printer ("i1_gtappprint", ``App_i1 Opapp [Var_global_i1 7; x]``,genPrint (infixappPrint ">")); 
val _=temp_add_user_printer ("i1_ltappprint", ``App_i1 Opapp [Var_global_i1 8; x]``,genPrint (infixappPrint "<")); 
val _=temp_add_user_printer ("i1_modappprint", ``App_i1 Opapp [Var_global_i1 9; x]``,genPrint (infixappPrint "mod")); 
val _=temp_add_user_printer ("i1_divappprint", ``App_i1 Opapp [Var_global_i1 10; x]``,genPrint (infixappPrint "div")); 
val _=temp_add_user_printer ("i1_timesappprint", ``App_i1 Opapp [Var_global_i1 11; x]``,genPrint (infixappPrint "*")); 
val _=temp_add_user_printer ("i1_minusappprint", ``App_i1 Opapp [Var_global_i1 12; x]``,genPrint (infixappPrint "-")); 
val _=temp_add_user_printer ("i1_addappprint", ``App_i1 Opapp [Var_global_i1 13; x]``,genPrint (infixappPrint "+")); 

(*i1 uops*)
val _=temp_add_user_printer ("i1_derefappprint", ``App_i1 Opapp [Var_global_i1 1;x]``,genPrint (prefixappPrint "!"));
val _=temp_add_user_printer ("i1_negappprint", ``App_i1 Opapp [Var_global_i1 2; x]``,genPrint (prefixappPrint "~"));

(*Not sure if necessary*)
val _=temp_add_user_printer ("i1_word8array_arrayprint", ``App_i1 Opapp [Var_global_i1 14; x]``,genPrint (prefixappPrint "Word8Array.array")); 
val _=temp_add_user_printer ("i1_word8array_subprint", ``App_i1 Opapp [Var_global_i1 15; x]``,genPrint (prefixappPrint "Word8Array.sub")); 
val _=temp_add_user_printer ("i1_word8array_lengthprint", ``App_i1 Opapp [Var_global_i1 16; x]``,genPrint (prefixappPrint "Word8Array.length")); 
val _=temp_add_user_printer ("i1_word8Array_updateprint", ``App_i1 Opapp [Var_global_i1 17; x]``,genPrint (prefixappPrint "Word8Array.update")); 

val _=temp_add_user_printer ("i1_vector_fromlistprint", ``App_i1 Opapp [Var_global_i1 18; x]``,genPrint (prefixappPrint "Vector.fromList")); 
val _=temp_add_user_printer ("i1_vector_lengthprint", ``App_i1 Opapp [Var_global_i1 19; x]``,genPrint (prefixappPrint "Vector.length")); 
val _=temp_add_user_printer ("i1_vector_subprint", ``App_i1 Opapp [Var_global_i1 20; x]``,genPrint (prefixappPrint "Vector.sub")); 

val _=temp_add_user_printer ("i1_array_arrayprint", ``App_i1 Opapp [Var_global_i1 21; x]``,genPrint (prefixappPrint "Array.array")); 
val _=temp_add_user_printer ("i1_array_subprint", ``App_i1 Opapp [Var_global_i1 22; x]``,genPrint (prefixappPrint "Array.sub")); 
val _=temp_add_user_printer ("i1_array_lengthprint", ``App_i1 Opapp [Var_global_i1 23; x]``,genPrint (prefixappPrint "Array.length")); 
val _=temp_add_user_printer ("i1_array_updateprint", ``App_i1 Opapp [Var_global_i1 24; x]``,genPrint (prefixappPrint "Array.update")); 






(*i1 list form *)
val _=temp_add_user_printer("i1listprint",``x:prompt_i1 store``,genPrint astlistPrint);

val _=temp_add_user_printer("i1_truelitprint",``Lit_i1 (Bool T)``,genPrint (boolPrint "true"));
val _=temp_add_user_printer("i1_falselitprint",``Lit_i1 (Bool F)``,genPrint (boolPrint "false"));
end;
