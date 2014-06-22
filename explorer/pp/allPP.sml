structure allPP = struct local
open HolKernel boolLib bossLib Parse
open cakeml_computeLib astPP modPP conPP exhPP patPP

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

in

exception compilationError of string;
type allIntermediates = {
  ils:term list,
  globMap:term list,
  ctors:term list,
  modMap:term list}

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let val t1 = eval ``get_all_asts ^(prog)``
      val t2 = eval ``elab_all_asts ^(rhsThm t1)``
      val ast = rand (rhsThm t2)

      val _ =if ast = ``"<parse error>\n"`` then raise compilationError "Parse Error" else ();

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
      val p7_1 = rhsThm compile_Cexp

      (*compile print err*)
      val compile_print_err = eval ``compile_print_err ^(p7_1)``;
      val p7_2 = rhsThm compile_print_err

      (*Add it*)
      val addIt = eval ``case FLOOKUP ^(m2) "it" of
                             NONE => ^(p7_2)
                           | SOME n =>
                               (let r = emit ^(p7_2) [Gread n; Print]
                                in
                                  emit r (MAP PrintC (EXPLODE "\n")))``

      val p7_3 = rhsThm addIt

      val emit = eval ``emit ^(p7_3) [Stop T]``
      val p7_4 = rhsThm emit

      val rev = eval ``REVERSE (^p7_4).out``

      val p7 = rhsThm rev
  in
     {ils=[ast,p1,p2,p3,p4,p5,p6,p7],
      ctors=ctors,globMap=globMap,modMap=modMap}
  end;
end
end
