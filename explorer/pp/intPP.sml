structure intPP =
struct
open astPP conPP modPP exhPP patPP
(*This is stateful!*)
val collectAnnotations :(term list ref)= ref ([]:term list);

(*cexp_Nested mutually recursive letrec
Collects annotations statefully when called*)

fun cexp_letrecPrint Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types PPBackEnd
    val (str,brk,blk,sty) = (#add_string ppfns, #add_break ppfns,#ublock ppfns,#ustyle ppfns);
    val (temp,expr) = dest_comb t
    val (_,ls) = dest_comb temp
    val fundef = #1(listSyntax.dest_list ls)
    fun printTerms [] = str ""
    |   printTerms [x] = 
          let val ([opt,num,x]) = pairSyntax.strip_pair x
          in
            (if optionSyntax.is_none(opt) then str "fun" (*Should never be pretty printed*)
            else (*Has annotations*)
                let val lab = hd (pairSyntax.strip_pair(strip opt))
                  in 
                    (collectAnnotations := optionSyntax.dest_some(opt) :: (!collectAnnotations));
                     sty [FG Purple] (str "f">>str (term_to_string lab))
                  end) 
    	    >>str" = ">>sys (Top,Top,Top) d x
          end 
    |   printTerms (t::xs) = printTerms [t] >>add_newline>> (printTerms xs)
  in
     blk CONSISTENT 0 ((blk CONSISTENT 0 (printTerms fundef))
     >>add_newline>>str "in">>add_newline>>str"  ">>sys (Top,Top,Top) d expr >>add_newline>> str "end")
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = temp_add_user_printer ("cexp_letrecprint", ``CLetrec x y``,cexp_letrecPrint);

(*TODO: find an example where this occurs??*)
(*cexp_CUpd*)
fun cexp_cupdPrint sys d t Top str brk blk =
  let val (_,[l,r]) = strip_comb t
  in
    blk CONSISTENT 0 (sys(Top,Top,Top) d l >>str " =">>brk(1,2) >>sys(Top,Top,Top) d r)
  end;

val _ = temp_add_user_printer("cexp_cupdprint", ``CUpd x y``,genPrint cexp_cupdPrint);

(*cexp_Apply Equality*)
val _ = temp_add_user_printer ("cexp_equalityprint", ``CPrim2 CEq x y``, genPrint pat_equalityPrint);

(*cexp_Call*)
(*Or maybe call (...) with [...]*)
fun cexp_ccallPrint sys d t pg str brk blk =
  let val (t,ls) = dest_comb t
      val (t,name) = dest_comb t
      val (_,b) = dest_comb t
  in
     m_brack str pg (blk CONSISTENT 0 ( str"call">>sys(Top,Top,Top) d b>>str" ">>sys (Prec(0,"cexpcall"),Top,Top) d name
     >>brk(1,0)>>str"with ">>sys (Top,Top,Top) d ls))
  end;

val _ = temp_add_user_printer ("cexp_ccallprint", ``CCall b f x``, genPrint cexp_ccallPrint);

(*cexp_prim1*)
(*NOTE: these actually seem rather superfluous...*)
fun cexp_isblockPrint sys d t pg str brk blk =
  str"is_block";

val _ = temp_add_user_printer("cexp_cisblockprint",``CIsBlock``,genPrint cexp_isblockPrint);

val _ = temp_add_user_printer("cexp_ctageqprint",``CTagEq x``,genPrint (pat_uopPrint "tag_eq"));
val _ = temp_add_user_printer("cexp_cprojprint",``CProj x``,genPrint (pat_uopPrint "elem"));

val _ = temp_add_user_printer("cexp_prim1print",``CPrim1 x y``,genPrint pat_uappPrint);

val _ = temp_add_user_printer("cexp_initgprint",``CPrim1 (CInitG x) y``,i2_initglobalPrint);

(*cexp_ constructors*)
val _ = temp_add_user_printer ("cexp_conprint", ``CCon x y``,i2_pconPrint);

(*cexpextend global*)
val _ = temp_add_user_printer("cexp_extendglobal",``CExtG n``,genPrint i2_extendglobalPrint);

(*cexp_Let*)
fun cexp_letpatPrint sys d t pg str brk blk =
  let val (t1,exp2) = dest_comb t
      val (t2,exp1) = dest_comb t1
      val (_,b) = dest_comb t2
    in
    if b = ``T``
    then
      pat_letpatPrint sys d t pg str brk blk
    else
      letnonePrint sys d t pg str brk blk
    end;

val _ = temp_add_user_printer ("cexp_letprint",``CLet b y z ``,genPrint cexp_letpatPrint);

(*cexp_Literals*)
(*cexp_Pattern lit*)
val _ = temp_add_user_printer ("cexp_litprint", ``CLit x``, genPrint plitPrint);
val _ = temp_add_user_printer ("cexp_unitprint", ``CLit Unit``,genPrint unitPrint);

val _ = temp_add_user_printer("cexp_truelitprint",``CLit (Bool T)``,genPrint (boolPrint "true"));
val _ = temp_add_user_printer("cexp_falselitprint",``CLit (Bool F)``,genPrint (boolPrint "false"));

(*cexp local var name debrujin indices*)
val _ = temp_add_user_printer ("cexp_varlocalprint", ``CVar x``,pat_varlocalPrint);

(*cexp global Var name*)
val _ = temp_add_user_printer ("cexp_varglobalprint", ``CGvar n``,i1_varglobalPrint);

(*cexp_raise expr*) 
val _ = temp_add_user_printer ("cexp_raiseprint", ``CRaise x``,genPrint raisePrint);

(*cexp_handle*)
val _ = temp_add_user_printer ("cexp_handleprint", ``CHandle x y``,genPrint (pat_handlePrint));

(*cexp_If-then-else*)
val _ = temp_add_user_printer("cexp_ifthenelseprint", ``CIf x y z``,genPrint ifthenelsePrint);

(*TODO: add the globals for binops?*)
end;
