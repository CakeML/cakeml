structure allPP = struct local
open HolKernel boolLib bossLib Parse
open cakeml_computeLib astPP modPP conPP exhPP patPP intPP
open labels_computeLib
open x64_code_evalTheory x64_heapTheory

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

(*x64 heap stuff should probably go into cakeml computelib?*)
val _ = wordsLib.add_words_compset true cs
val _= computeLib.add_thms [prog_x64_extraTheory.IMM32_def,small_offset_def,small_offset6_def,small_offset12_def,small_offset16_def,x64_def,x64_length_def,x64_code_def] cs

val _ = computeLib.add_thms [compile_primitives_pieces] cs
val eval = computeLib.CBV_CONV cs

in

exception compilationError of string;
type allIntermediates = {
  ils:term list,
  globMap:term list,
  ctors:term list,
  modMap:term list,
  annotations:term list}

(*Return all intermediates during compilation in a record*)
fun allIntermediates prog =
  let 
      val t1 = eval ``get_all_asts ^(prog)``
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
      val cs = rhsThm (eval ``<|out:=[];next_label:=compile_primitives.rnext_label|>``);
      
      val lab_closures = eval ``label_closures (LENGTH []) (^(cs).next_label) ^(p6)``
      val (Ce,nl) = pairSyntax.dest_pair(rhsThm lab_closures)
      
      val _ = (collectAnnotations := ([]:term list))
      (*Cheat and call PP internally so that the stateful annotations are updated*)
      val _ = term_to_string Ce
      val p6 = Ce

      val cs = rhsThm (eval ``compile_code_env (^(cs) with next_label := ^(nl)) ^(Ce)``)

      val compile_Cexp = eval ``compile [] TCNonTail 0 ^(cs) ^(Ce)``
      (*val compile_Cexp = eval ``compile_Cexp [] 0 
                           <|out:=[];next_label:=compile_primitives.rnext_label|> ^(p6)``*)
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

      val code_labels_ok_thm = prove(
        ``code_labels_ok ^p7``,
         cheat)

      val _ = with_flag (quiet,true) add_code_labels_ok_thm code_labels_ok_thm

      val rem_labels = with_flag (quiet,true) eval ``remove_labels_all_asts (Success ^(p7))``

      val p8 = rhsThm rem_labels |> rand

      (*Bytecode to asm*)
      val asm = eval ``x64_code 0 ^(p8)``
      val p9 = rhsThm asm

      val p8 = rhsThm (eval ``(NONE,^(p8))``)

      val p7 = rhsThm (eval ``(SOME x,^(p7))``)
      
  in
     {ils=[ast,p1,p2,p3,p4,p5,p6,p7,p8,p9],
      ctors=ctors,globMap=globMap,modMap=modMap,annotations=(!collectAnnotations)}
  end;
end
end


(*Helper for test calls*)

(*val () = set_trace "pp_avoids_symbol_merges" 0

fun take 0 (x::xs) = x
|   take n (_::xs) = take (n-1) xs;

fun i n (ex:allIntermediates) = take n (#ils ex);
*)
