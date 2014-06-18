open cakeml_computeLib
open HolKernel boolLib bossLib Parse
open Portable smpp 

fun println str = (print str; print"#@#");
fun printls sep str = (print str; print sep);
fun termToList ls = #1(listSyntax.dest_list(ls));

val _ = set_trace"pp_avoids_symbol_merges"0;

fun fullEval p =
  let val asts = eval ``get_all_asts ^(p)``
      val elab = eval ``elab_all_asts ^(asts |> concl |> rhs)``
      in
        rhs(concl elab) |>rand 
      end;
(*RHS of theorem to term*)
val rhsThm = rhs o concl;

val compile_primitives_def = Define`
  compile_primitives =
    FST(compile_top NONE init_compiler_state
    (Tdec initial_program))`;

val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_def,compilerTheory.compile_top_def] cs
val eval = computeLib.CBV_CONV cs
val compile_primitives_full = eval ``compile_primitives``

val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_full] cs
val eval = computeLib.CBV_CONV cs
val compile_primitives_pieces =
  LIST_CONJ[
  eval ``compile_primitives.globals_env``
  ,eval ``compile_primitives.next_global``
  ,eval ``compile_primitives.exh``
  ,eval ``compile_primitives.contags_env``
  ,eval ``compile_primitives.rnext_label``];
val cs = cakeml_compset();
val _ = computeLib.add_thms [compile_primitives_pieces] cs
val eval = computeLib.CBV_CONV cs

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)
      
      (*i1 translation*)
      val n = rhsThm (eval ``compile_primitives.next_global``)
      val (m1,m2) = pairSyntax.dest_pair( rhsThm( eval ``compile_primitives.globals_env``))
      val l1 = eval ``prog_to_i1 ^(n) ^(m1) ^(m2) ^(ast)``
      val [v1,v2,m2,p1] = pairSyntax.strip_pair(rhsThm l1)    

      (*Assume start from fempty*)
      val (_,modMap) = finite_mapSyntax.strip_fupdate v2
      val (_,globMap) = finite_mapSyntax.strip_fupdate m2

      (*i2 translation*)
      val l2 = eval ``prog_to_i2 compile_primitives.contags_env ^(p1) ``
      val (v,rest) = pairSyntax.dest_pair (rhsThm l2)
      val (exh,p2) = pairSyntax.dest_pair rest

      val p2' = (v,exh,p2)
      (*print the CTORS (num,name,typeid)*)
      val [_,_,_,ct] =pairSyntax.strip_pair v 

      val (_,ctors) = finite_mapSyntax.strip_fupdate ct;
      (*i3 translation*)
      val arg1 = rhsThm( eval ``(none_tag,SOME(TypeId (Short "option")))``)
      val arg2 = rhsThm( eval ``(some_tag,SOME(TypeId (Short "option")))``)
      val l3 = eval ``prog_to_i3 ^(arg1) ^(arg2) ^(n) ^(p2)``
      val (v,p3) = pairSyntax.dest_pair(rhsThm l3)

      (*exp to exh trans*)
      val exp_to_exh = eval ``exp_to_exh (^(exh) ⊌ compile_primitives.exh) ^(p3)``
      val p4 = rhsThm exp_to_exh

      (*exp_to_pat trans*)
      val exp_to_pat = eval ``exp_to_pat [] ^(p4)``
      val p5 = rhsThm exp_to_pat
      
      (*exp_to_cexp*)
      val exp_to_Cexp = eval ``exp_to_Cexp ^(p5)``
      val p6 = rhsThm exp_to_Cexp

      (*compileCexp*)
      val compile_Cexp = eval ``compile_Cexp [] 0 <|out:=[];next_label:=compile_primitives.rnext_label|> ^(p6)``
      val p7 = rhsThm compile_Cexp


  in
     {ast=ast,i1=p1,i2=p2,i3=p3,i4=p4,i5=p5,i6=p6,i7=p7,ctors = ctors,globMap=globMap,modMap=modMap}
  end;

(*Not included yet
val compile_print_err = eval ``compile_print_err ^(r)``;
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
*)
val tm = "val x = 5;";

fun io_Handler() = 
  let val str = SOME(tm)
  in
  (
    case str 
    of SOME(x) =>  
    let val str = stringSyntax.fromMLstring x
    val out = allIntermediates str
    in
      map (printls ";" o term_to_string) (termToList (#ast out));
      println "";
      map (printls ";" o term_to_string) (termToList (#i1 out));
      println ""; 
      map (printls ";" o term_to_string) (termToList (#i2 out));
      println "";
      println (term_to_string (#i3(out)));
      println (term_to_string (#i4(out)));
      println (term_to_string (#i5(out)));
      println (term_to_string (#i6(out)));
      map (printls "\n" o term_to_string) (#globMap out);
      println "";
      map (printls "\n" o term_to_string) (#modMap out);
      println "";
      map (printls "\n" o term_to_string) (#ctors out);()
    end
  ) handle _ => TextIO.print "Invalid Input\n"
  end;

val _ = PolyML.export("pp",io_Handler);
