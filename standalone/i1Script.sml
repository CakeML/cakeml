open HolKernel boolLib bossLib Parse astTheory terminationTheory
open cakeml_computeLib progToBytecodeTheory
open modLangTheory initialProgramTheory

(*RHS of theorem to term*)
val rhsThm = rhs o concl;

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)

      (*i1 translation*)
      val n = rhsThm (eval ``init_compiler_state.next_global``)
      val (m1,m2) = pairSyntax.dest_pair( rhsThm( eval ``init_compiler_state.globals_env``))
      val l1 = eval ``prog_to_i1 ^(n) ^(m1) ^(m2) ^(ast)``;
      val [v1,v2,m2,p1] = pairSyntax.strip_pair(rhsThm l1)    

      (*i2 translation*)
      val l2 = eval ``prog_to_i2 init_compiler_state.contags_env ^(p1) ``
      val (v,rest) = pairSyntax.dest_pair (rhsThm l2)
      val (exh,p2) = pairSyntax.dest_pair rest

      (*i3 translation*)
      val arg1 = rhsThm( eval ``(none_tag,SOME(TypeId (Short "option")))``)
      val arg2 = rhsThm( eval ``(some_tag,SOME(TypeId (Short "option")))``)
      val l3 = eval ``prog_to_i3 ^(arg1) ^(arg2) ^(n) ^(p2)``
      val (v,p3) = pairSyntax.dest_pair(rhsThm l3)

      (*exp to exh trans*)
      val exp_to_exh = eval ``exp_to_exh (^(exh) ⊌ init_compiler_state.exh) ^(p3)``
      val p4 = rhsThm exp_to_exh

      (*exp_to_pat trans*)
      val exp_to_pat = eval ``exp_to_pat [] ^(p4)``
      val p5 = rhsThm exp_to_pat
      
      (*exp_to_cexp*)
      val exp_to_Cexp = eval ``exp_to_Cexp ^(p5)``
      val p6 = rhsThm exp_to_Cexp

      (*compileCexp*)
      val compile_Cexp = eval ``compile_Cexp [] 0 <|out:=[];next_label:=init_compiler_state.rnext_label|> ^(p6)``
      val p7 = rhsThm compile_Cexp
  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7}
  end;

val prog = ``"val x = 5; x+2+3;"``

(*Not included yet*)
val compile_print_err = eval ``compile_print_err ^(r)``
val r = rhs(concl compile_print_err)

val addIt = eval ``case FLOOKUP ^(m2) "it" of
                             NONE => ^(r)
                           | SOME n =>
                               (let r = emit ^(r) [Gread n; Print]
                                in
                                  emit r (MAP PrintC (EXPLODE "\n")))``
val r = rhs(concl addIt)
val emit = eval ``emit ^(r) [Stop T]``
val rev = eval ``REVERSE (^(rhs(concl emit))).out``

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc sys d t Top str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*i1_Unnamed Prompts NONE => declist*)
fun i1_promptNonePrint sys d t Top str brk blk=
  let
    open smpp
    val (_,ls) = dest_comb t
    fun printAll [] = str""
    |   printAll (x::xs) = sys (Top,Top,Top) (d-1) x >> add_newline
  in
    blk CONSISTENT 0 (
    str "prompt {">>brk(1,0)>> printAll (#1(listSyntax.dest_list ls)) >> brk(1,0) >>str "}")
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
    sys (Top,Top,Top) (d-1) l >>str "var_binding">>add_newline 
    >>sys (Top,Top,Top) (d-1) r
  end;

temp_add_user_printer ("i1_dletvalprint", ``Dlet_i1 x y``,genPrint i1_dletvalPrint);

(*i1_Inner Let SOME*)
temp_add_user_printer ("i1_letvalprint", ``Let_i1 (SOME x) y z``,genPrint letvalPrint);

(*Prints all constructor args in a list comma separated*)
(*Con NONE*)
temp_add_user_printer ("i1_conprint", ``Con_i1 NONE x``,genPrint pconPrint);

(*i1_Con SOME*)
temp_add_user_printer ("i1_consomeprint", ``Con_i1 (Some x) y``,genPrint pconsomePrint);

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
    sys (Top,Top,Top) d (strip t)>>str"_global";

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


val x = ``"val x = 1;"``

val x = ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val th = EVAL ``prog_to_bytecode_string ^x``;

