(*Pretty printing for modLang*)
structure modPP =
struct
open astPP modLangTheory

val _ = bring_fwd_ctors "modLang" ``:modLang$exp``
val _ = bring_fwd_ctors "modLang" ``:modLang$dec``
val _ = bring_fwd_ctors "modLang" ``:modLang$prompt``

val modPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

fun add_modPP hd = modPrettyPrinters:= (hd:: !modPrettyPrinters)

(*Extracts the module prefix if any*)
fun modoptionString t=
  if optionSyntax.is_some t then toString (rand t) else "";

(*modLang Prompts opt => declist*)
fun mod_promptPrint sys d t pg str brk blk=
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

val _ = add_modPP("mod_promptprint",``Prompt opt x``,genPrint mod_promptPrint);

(*mod_pg level exceptions*)
(*DExn with module names TODO*)
(*Unwrap the term*)
fun mod_dexnPrint sys d t pg str brk blk =
  let val opt = (t|> rator|>rator|>rand)
  in
    (dexnPrint (modoptionString opt) sys d ``Dexn ^(rand (rator t)) ^(rand t)`` pg str brk blk)
  end;

val _=add_modPP ("mod_dexnprint", ``Dexn opt x y``,genPrint mod_dexnPrint);

(*mod_pg level datatypes list(list tvarN *typeN * list ... ) *)

fun mod_dtypePrint sys d t pg str brk blk =
  let val opt = (t |> rator)|> rand
  in
     (dtypePrint (modoptionString opt) sys d t pg str brk blk)
  end;

val _=add_modPP ("mod_dtypeprint", ``Dtype opt x``,genPrint mod_dtypePrint);

(*mod_pg level letrec list varN*varN*exp -- Only strip once *)
val _=add_modPP ("mod_dletrecprint", ``Dletrec x``, genPrint dletrecPrint);

(*mod_Nested mutually recursive letrec*)

val _=add_modPP ("mod_letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*mod_Lambdas varN*expr *)
val _=add_modPP ("mod_lambdaprint", ``Fun x y``,genPrint lambdaPrint);

(*mod_ pglevel Dlet nat*expr *)
fun mod_dletvalPrint sys d t pg str brk blk=
  let
    val (_,[l,r]) = strip_comb t;
  in
    add_newline>> blk CONSISTENT 2 (sys (pg,pg,pg) (d-1) l >>str " var_binding">>add_newline
    >>sys (pg,pg,pg) (d-1) r)
  end;

val _=add_modPP ("mod_dletvalprint", ``Dlet x y``,genPrint mod_dletvalPrint);

(*mod_Inner Let SOME*)
val _=add_modPP ("mod_letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);

(*mod_Inner Let NONE*)
val _=add_modPP ("mod_letnoneprint", ``Let NONE y z``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
val _=add_modPP ("mod_conprint", ``Con NONE x``,genPrint pconPrint);

(*mod_Con SOME*)
val _=add_modPP ("mod_consomeprint", ``Con (Some x) y``,genPrint pconsomePrint);

(*Special case for list syntax
check_tail checks whether it is a fully specified list*)
fun check_tail t =
  let val (x,y) = dest_comb t in
    if x = ``Con (SOME (Short "nil"))`` then true
    else
      if x = ``Con (SOME (Short "::"))`` then
           check_tail (hd (tl (#1(listSyntax.dest_list y))))
    else false
  end;

val _=add_modPP ("mod_conconsprint",``Con (SOME (Short "::")) y``, genPrint (pconconsPrint check_tail));
val _=add_modPP ("mod_connilprint",``Con (SOME (Short "nil")) y``,genPrint pconnilPrint);

(*mod_Literals*)
(*mod_Pattern lit*)
val _=add_modPP ("mod_litprint", ``Lit x``, genPrint plitPrint);

(*mod local Var name, no more long names*)
fun mod_varlocalPrint sys d t pg str brk blk =
    str (toString (strip t));

val _=add_modPP ("mod_varlocalprint", ``Var_local x``,genPrint mod_varlocalPrint);

(*mod global Var name*)
fun mod_varglobalPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val sys = wrap_sys sys
  in
    sty [FG DarkBlue] (str"g">>sys (Top,Top,Top) d (strip t))
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*
fun mod_varglobalPrint sys d t pg str brk blk =
    str"g_">>sys (pg,pg,pg) d (strip t);*)

val _=add_modPP ("mod_varglobalprint", ``Var_global n``,mod_varglobalPrint);

(*mod_Matching*)
val _=add_modPP ("mod_matprint", ``Mat x y``,genPrint matPrint);

(*mod_Apply*)
val _=add_modPP ("mod_oppappprint", ``App Opapp ls``, genPrint oppappPrint);

(*mod_raise expr*)
val _=add_modPP ("mod_raiseprint", ``Raise x``,genPrint raisePrint);

(*mod_handle expr * list (pat*expr)*)
val _=add_modPP ("mod_handleprint", ``Handle x y``,genPrint handlePrint);

(*mod_If-then-else*)
val _=add_modPP("mod_ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);

fun prefixappPrint uop sys d t pg str brk blk =
  let
    val (_,ls) = dest_comb t
    val [_,x] = #1(listSyntax.dest_list ls)
  in
    m_brack str pg ( str uop >>str " " >> sys (pg,pg,pg) d x)
  end;

(*mod binops*)
val _=add_modPP ("mod_assignappprint", ``App Opapp [Var_global 10; x]``,genPrint (infixappPrint ":="));
val _=add_modPP ("mod_eqappprint", ``App Opapp [Var_global 9; x]``,genPrint (infixappPrint "="));
val _=add_modPP ("mod_gteqappprint", ``App Opapp [Var_global 8; x]``,genPrint (infixappPrint ">="));
val _=add_modPP ("mod_lteqappprint", ``App Opapp [Var_global 7; x]``,genPrint (infixappPrint "<="));
val _=add_modPP ("mod_gtappprint", ``App Opapp [Var_global 6; x]``,genPrint (infixappPrint ">"));
val _=add_modPP ("mod_ltappprint", ``App Opapp [Var_global 5; x]``,genPrint (infixappPrint "<"));
val _=add_modPP ("mod_modappprint", ``App Opapp [Var_global 4; x]``,genPrint (infixappPrint "mod"));
val _=add_modPP ("mod_divappprint", ``App Opapp [Var_global 3; x]``,genPrint (infixappPrint "div"));
val _=add_modPP ("mod_timesappprint", ``App Opapp [Var_global 2; x]``,genPrint (infixappPrint "*"));
val _=add_modPP ("mod_minusappprint", ``App Opapp [Var_global 1; x]``,genPrint (infixappPrint "-"));
val _=add_modPP ("mod_addappprint", ``App Opapp [Var_global 0; x]``,genPrint (infixappPrint "+"));

(*mod uops*)
val _=add_modPP ("mod_refappprint", ``App Opapp [Var_global 13; x]``,genPrint (prefixappPrint "ref"));
val _=add_modPP ("mod_derefappprint", ``App Opapp [Var_global 12;x]``,genPrint (prefixappPrint "!"));
val _=add_modPP ("mod_negappprint", ``App Opapp [Var_global 11; x]``,genPrint (prefixappPrint "~"));

(*mod list form *)
(*
TODO: Replace
val _=add_modPP("modlistprint",``x:prompt_mod store``,genPrint astlistPrint);
*)

fun enable_modPP_verbose () = map temp_add_user_printer (!modPrettyPrinters);
fun enable_modPP () = (enable_modPP_verbose();())
fun disable_modPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!modPrettyPrinters);
fun disable_modPP () = (disable_modPP_verbose();())

end;
