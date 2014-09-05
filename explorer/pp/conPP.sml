(*Pretty printing for conLang & decLang*)
structure conPP =
struct
open astPP modPP

val conPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

fun add_conPP hd = conPrettyPrinters:= (hd:: !conPrettyPrinters)

fun i2_initglobalPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val (t,x) = dest_comb t
    val num = rand (rand t)
    val [x] = #1(listSyntax.dest_list x) (*Assume singleton list for arg to init global as well...*)
  in
    sty [FG DarkBlue] (str"g" >> sys (Top,Top,Top) d num) >>str " := " >> blk CONSISTENT 0 (sys (Top,Top,Top) (d-1) x)
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _=add_conPP("i2_initglobal",``App_i2 (Init_global_var_i2 n) x``,i2_initglobalPrint);

(*i2_extend_global creates n top level decls*)
fun i2_extendglobalPrint sys d t pg str brk blk =
  let
    val n = rand t
  in
    str"extend_global ">>sys (pg,pg,pg) d n
  end;

val _=add_conPP("i2_extendglobal",``Extend_global_i2 n``,genPrint i2_extendglobalPrint);

(*i2_prompt*)
fun i2_promptPrint sys d t pg str brk blk=
  let
    val (_,ls) = dest_comb t
    fun printAll [] = str""
    |   printAll [x] = sys (pg,pg,pg) d x
    |   printAll (x::xs) = sys (pg,pg,pg) (d-1) x >>printAll xs
  in
    add_newline>>blk CONSISTENT 2 (
    str "prompt {">>printAll (#1(listSyntax.dest_list ls)))>>add_newline>>str "}"
  end;
val _=add_conPP("i2_promptprint",``Prompt_i2 x``,genPrint (i2_promptPrint));

(*i2_Pvar*)
val _=add_conPP ("i2_pvarprint", ``Pvar_i2 x``, genPrint pvarPrint);

(*i2_Plit*)
val _=add_conPP("i2_plitprint", ``Plit_i2 x``, genPrint plitPrint);


(*i2_pg level letrec list varN*varN*exp -- Only strip once *)
val _=add_conPP ("i2_dletrecprint", ``Dletrec_i2 x``, genPrint dletrecPrint);

(*i2_Nested mutually recursive letrec*)
val _=add_conPP ("i2_letrecprint", ``Letrec_i2 x y``,genPrint letrecPrint);

(*i2_Lambdas varN*expr *)
val _=add_conPP ("i2_lambdaprint", ``Fun_i2 x y``,genPrint lambdaPrint);

(*i2_pglevel Dlet nat*expr *)
val _=add_conPP ("i2_dletvalprint", ``Dlet_i2 x y``,genPrint i1_dletvalPrint);

(*i2_Inner Let SOME*)
val _=add_conPP ("i2_letvalprint", ``Let_i2 (SOME x) y z``,genPrint letvalPrint);

(*i2_Inner Let NONE*)
val _=add_conPP ("i2_letnoneprint",``Let_i2 NONE y z ``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)


(*i2 Con, reuse AST CON NONE*)
(*
fun i2_pconPrint sys d t pg str brk blk =
  let
    val (_,name) = dest_comb (rator t)
    val (x::_) = pairSyntax.strip_pair name
  in
    (*TODO: Fix this*)
    str "c_" >> sys (pg,pg,pg) d x >> (pconPrint sys d t pg str brk blk)
  end;
*)

fun i2_pconPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val (_,name) = dest_comb (rator t)
    val (x::_) = pairSyntax.strip_pair name
  in
    sty [FG RedBrown] (str "c" >> sys (Top,Top,Top) d x )>> (pconPrint sys d t Top str brk blk)
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _=add_conPP ("i2_conprint", ``Con_i2 x y``,i2_pconPrint);
val _=add_conPP ("i2_pconprint", ``Pcon_i2 x y``,i2_pconPrint);
(*TODO: Add special cases for built in CTORS?*)

(*val _=add_conPP ("i2_conprint", ``Con_i2 x y``,genPrint i2_pconPrint);
val _=add_conPP ("i2_pconprint", ``Pcon_i2 x y``,genPrint i2_pconPrint);*)

(*i2_Literals*)
(*i2_Pattern lit*)
val _=add_conPP ("i2_litprint", ``Lit_i2 x``, genPrint plitPrint);
val _=add_conPP ("i2_unitprint", ``Lit_i2 Unit``,genPrint unitPrint);

(*i2 local Var name, no more long names*)
val _=add_conPP ("i2_varlocalprint", ``Var_local_i2 x``,genPrint i1_varlocalPrint);

(*i2 global Var name*)
val _=add_conPP ("i2_varglobalprint", ``Var_global_i2 n``,i1_varglobalPrint);

(*i2_Matching*)
val _=add_conPP ("i2_matprint", ``Mat_i2 x y``,genPrint matPrint);

(*i2_Apply*)
val _=add_conPP ("i2_oppappprint", ``App_i2 (Op_i2 Opapp) ls``, genPrint oppappPrint);

(*i2_raise expr*) 
val _=add_conPP ("i2_raiseprint", ``Raise_i2 x``,genPrint raisePrint);

(*i2_handle expr * list (pat*expr)*)
val _=add_conPP ("i2_handleprint", ``Handle_i2 x y``,genPrint handlePrint);

(*i2_If-then-else*)
val _=add_conPP("i2_ifthenelseprint", ``If_i2 x y z``,genPrint ifthenelsePrint);

val _=add_conPP("i2_truelitprint",``Lit_i2 (Bool T)``,genPrint (boolPrint "true"));
val _=add_conPP("i2_falselitprint",``Lit_i2 (Bool F)``,genPrint (boolPrint "false"));

(*i2 binops*)
val _=add_conPP ("i2_assignappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 10; x]``,genPrint (infixappPrint ":=")); 
val _=add_conPP ("i2_eqappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 9; x]``,genPrint (infixappPrint "=")); 
val _=add_conPP ("i2_gteqappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 8; x]``,genPrint (infixappPrint ">=")); 
val _=add_conPP ("i2_lteqappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 7; x]``,genPrint (infixappPrint "<=")); 
val _=add_conPP ("i2_gtappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 6; x]``,genPrint (infixappPrint ">")); 
val _=add_conPP ("i2_ltappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 5; x]``,genPrint (infixappPrint "<")); 
val _=add_conPP ("i2_modappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 4; x]``,genPrint (infixappPrint "mod")); 
val _=add_conPP ("i2_divappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 3; x]``,genPrint (infixappPrint "div")); 
val _=add_conPP ("i2_timesappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 2; x]``,genPrint (infixappPrint "*")); 
val _=add_conPP ("i2_minusappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 1; x]``,genPrint (infixappPrint "-")); 
val _=add_conPP ("i2_addappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 0; x]``,genPrint (infixappPrint "+")); 

(*i2 uops*)
val _=add_conPP ("i2_refappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 13; x]``,genPrint (prefixappPrint "ref")); 
val _=add_conPP ("i2_derefappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 12;x]``,genPrint (prefixappPrint "!"));
val _=add_conPP ("i2_negappprint", ``App_i2 (Op_i2 Opapp) [Var_global_i2 11; x]``,genPrint (prefixappPrint "~"));

(*i2 list form*)
val _=add_conPP("i2listprint",``x:prompt_i2 store``,genPrint astlistPrint);

fun enable_conPP_verbose () = map temp_add_user_printer (!conPrettyPrinters); 
fun enable_conPP () = (enable_conPP_verbose();())
fun disable_conPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!conPrettyPrinters);
fun disable_conPP () = (disable_conPP_verbose();())

end;
