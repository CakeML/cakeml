(*Pretty printing for conLang & decLang*)
structure conPP =
struct
open astPP modPP conLangTheory

val _ = bring_fwd_ctors "conLang" ``:conLang$op``
val _ = bring_fwd_ctors "conLang" ``:conLang$pat``
val _ = bring_fwd_ctors "conLang" ``:conLang$exp``
val _ = bring_fwd_ctors "conLang" ``:conLang$dec``
val _ = bring_fwd_ctors "conLang" ``:conLang$prompt``

val conPrettyPrinters = ref []: (string * term * term_grammar.userprinter) list ref

fun add_conPP hd = conPrettyPrinters:= (hd:: !conPrettyPrinters)

fun con_initglobalPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val (t,x) = dest_comb t
    val num = rand (rand t)
    val [x] = #1(listSyntax.dest_list x) (*Assume singleton list for arg to init global as well...*)
    val sys = wrap_sys sys
  in
    sty [FG DarkBlue] (str"g" >> sys (Top,Top,Top) d num) >>str " := " >> blk CONSISTENT 0 (sys (Top,Top,Top) (d-1) x)
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _=add_conPP("con_initglobal",``App (Init_global_var n) x``,con_initglobalPrint);

(*con_extend_global creates n top level decls*)
fun con_extendglobalPrint sys d t pg str brk blk =
  let
    val n = rand t
  in
    str"extend_global ">>sys (pg,pg,pg) d n
  end;

val _=add_conPP("con_extendglobal",``Extend_global n``,genPrint con_extendglobalPrint);

(*con_prompt*)
fun con_promptPrint sys d t pg str brk blk=
  let
    val (_,ls) = dest_comb t
    fun printAll [] = str""
    |   printAll [x] = sys (pg,pg,pg) d x
    |   printAll (x::xs) = sys (pg,pg,pg) (d-1) x >>printAll xs
  in
    add_newline>>blk CONSISTENT 2 (
    str "prompt {">>printAll (#1(listSyntax.dest_list ls)))>>add_newline>>str "}"
  end;
val _=add_conPP("con_promptprint",``Prompt x``,genPrint (con_promptPrint));

(*con_Pvar*)
val _=add_conPP ("con_pvarprint", ``Pvar x``, genPrint pvarPrint);

(*con_Plit*)
val _=add_conPP("con_plitprint", ``Plit x``, genPrint plitPrint);


(*con_pg level letrec list varN*varN*exp -- Only strip once *)
val _=add_conPP ("con_dletrecprint", ``Dletrec x``, genPrint dletrecPrint);

(*con_Nested mutually recursive letrec*)
val _=add_conPP ("con_letrecprint", ``Letrec x y``,genPrint letrecPrint);

(*con_Lambdas varN*expr *)
val _=add_conPP ("con_lambdaprint", ``Fun x y``,genPrint lambdaPrint);

(*con_pglevel Dlet nat*expr *)
val _=add_conPP ("con_dletvalprint", ``Dlet x y``,genPrint mod_dletvalPrint);

(*con_Inner Let SOME*)
val _=add_conPP ("con_letvalprint", ``Let (SOME x) y z``,genPrint letvalPrint);

(*con_Inner Let NONE*)
val _=add_conPP ("con_letnoneprint",``Let NONE y z ``,genPrint letnonePrint);

(*Prints all constructor args in a list comma separated*)


(*con Con, reuse AST CON NONE*)
(*
fun con_pconPrint sys d t pg str brk blk =
  let
    val (_,name) = dest_comb (rator t)
    val (x::_) = pairSyntax.strip_pair name
  in
    (*TODO: Fix this*)
    str "c_" >> sys (pg,pg,pg) d x >> (pconPrint sys d t pg str brk blk)
  end;
*)

fun con_pconPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val (_,name) = dest_comb (rator t)
    val (x::_) = pairSyntax.strip_pair name
    val sys = wrap_sys sys
  in
    sty [FG RedBrown] (str "c" >> sys (Top,Top,Top) d x )>> (pconPrint sys d t Top str brk blk)
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _=add_conPP ("con_conprint", ``Con x y``,con_pconPrint);
val _=add_conPP ("con_pconprint", ``Pcon x y``,con_pconPrint);
(*TODO: Add special cases for built in CTORS?*)

(*val _=add_conPP ("con_conprint", ``Con x y``,genPrint con_pconPrint);
val _=add_conPP ("con_pconprint", ``Pcon x y``,genPrint con_pconPrint);*)

(*con_Literals*)
(*con_Pattern lit*)
val _=add_conPP ("con_litprint", ``Lit x``, genPrint plitPrint);

(*con local Var name, no more long names*)
val _=add_conPP ("con_varlocalprint", ``Var_local x``,genPrint mod_varlocalPrint);

(*con global Var name*)
val _=add_conPP ("con_varglobalprint", ``Var_global n``,mod_varglobalPrint);

(*con_Matching*)
val _=add_conPP ("con_matprint", ``Mat x y``,genPrint matPrint);

(*con_Apply*)
val _=add_conPP ("con_oppappprint", ``App (Op Opapp) ls``, genPrint oppappPrint);

(*con_raise expr*)
val _=add_conPP ("con_raiseprint", ``Raise x``,genPrint raisePrint);

(*con_handle expr * list (pat*expr)*)
val _=add_conPP ("con_handleprint", ``Handle x y``,genPrint handlePrint);

(*con_If-then-else*)
val _=add_conPP("con_ifthenelseprint", ``If x y z``,genPrint ifthenelsePrint);

(*con binops*)
val _=add_conPP ("con_assignappprint", ``App (Op Opapp) [Var_global 10; x]``,genPrint (infixappPrint ":="));
val _=add_conPP ("con_eqappprint", ``App (Op Opapp) [Var_global 9; x]``,genPrint (infixappPrint "="));
val _=add_conPP ("con_gteqappprint", ``App (Op Opapp) [Var_global 8; x]``,genPrint (infixappPrint ">="));
val _=add_conPP ("con_lteqappprint", ``App (Op Opapp) [Var_global 7; x]``,genPrint (infixappPrint "<="));
val _=add_conPP ("con_gtappprint", ``App (Op Opapp) [Var_global 6; x]``,genPrint (infixappPrint ">"));
val _=add_conPP ("con_ltappprint", ``App (Op Opapp) [Var_global 5; x]``,genPrint (infixappPrint "<"));
val _=add_conPP ("con_modappprint", ``App (Op Opapp) [Var_global 4; x]``,genPrint (infixappPrint "mod"));
val _=add_conPP ("con_divappprint", ``App (Op Opapp) [Var_global 3; x]``,genPrint (infixappPrint "div"));
val _=add_conPP ("con_timesappprint", ``App (Op Opapp) [Var_global 2; x]``,genPrint (infixappPrint "*"));
val _=add_conPP ("con_minusappprint", ``App (Op Opapp) [Var_global 1; x]``,genPrint (infixappPrint "-"));
val _=add_conPP ("con_addappprint", ``App (Op Opapp) [Var_global 0; x]``,genPrint (infixappPrint "+"));

(*con uops*)
val _=add_conPP ("con_refappprint", ``App (Op Opapp) [Var_global 13; x]``,genPrint (prefixappPrint "ref"));
val _=add_conPP ("con_derefappprint", ``App (Op Opapp) [Var_global 12;x]``,genPrint (prefixappPrint "!"));
val _=add_conPP ("con_negappprint", ``App (Op Opapp) [Var_global 11; x]``,genPrint (prefixappPrint "~"));

(*con list form*)
(*TODO: Replace*)
(*val _=add_conPP("conlistprint",``x:prompt_con store``,genPrint astlistPrint);*)

fun enable_conPP_verbose () = map temp_add_user_printer (!conPrettyPrinters);
fun enable_conPP () = (enable_conPP_verbose();())
fun disable_conPP_verbose () = map (fn (x,y,z) => temp_remove_user_printer x) (!conPrettyPrinters);
fun disable_conPP () = (disable_conPP_verbose();())

end;
