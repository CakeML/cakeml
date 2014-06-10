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

fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types
    val (str,brk) = (#add_string ppfns, #add_break ppfns);
  in
    printFunc sys d t Top str brk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*Unnamed Prompts NONE => declist*)
fun promptNonePrint sys d t Top str brk =
  let
    open smpp
    val (_,ls) = dest_comb t
  in
    str "prompt {" >>sys (Top,Top,Top) (d-1) ls >> str "}"
  end;

temp_add_user_printer("promptnoneprint",``Prompt_i1 NONE x``,genPrint promptNonePrint);

(*Named Prompt SOME => declist TODO*)

(*Top level declarations*)
fun dletPrint sys d t Top str brk =
  let
    open smpp
    val 

temp_add_user_printer("dletprint", ``Delet_i1 n r``



val x = ``"val x = 1;"``

val x = ``"fun append xs ys = case xs of [] => ys | (x::xs) => x :: append xs ys; fun reverse xs = case xs of [] => [] | x::xs => append (reverse xs) [x];"``

val th = EVAL ``prog_to_bytecode_string ^x``;

