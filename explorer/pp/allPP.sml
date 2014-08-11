structure allPP = struct local
open astPP modPP conPP exhPP patPP intPP
open preamble
open HolKernel boolLib bossLib Parse
open compute_basicLib compute_parsingLib compute_compilerLib compute_inferenceLib compute_semanticsLib compute_bytecodeLib compute_free_varsLib compute_x64Lib
open lexer_implTheory
open initialProgramTheory initCompEnvTheory

val get_all_asts_def = tDefine "get_all_asts" `
get_all_asts input =
  case lex_until_toplevel_semicolon input of
       NONE => Success []
     | SOME (tokens, rest_of_input) =>
        case parse_top tokens of
             NONE => Failure "<parse error>\n"
           | SOME top =>
               case get_all_asts rest_of_input of
                    Failure x => Failure x
                  | Success prog => Success (top::prog)`
(wf_rel_tac `measure LENGTH` >>
 rw [lex_until_toplevel_semicolon_LESS]);

val remove_labels_all_asts_def = Define `
remove_labels_all_asts len asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         Success (code_labels len asts)`;

(*RHS of theorem to term*)
val rhsThm = rhs o concl;

val compile_primitives_def = Define`
  compile_primitives =
   (FST (THE basis_env)).comp_rs`;

val cs = the_basic_compset
val _ = add_compiler_compset false cs
val _ = add_parsing_compset cs
val _ = add_inference_compset cs
val _ = add_ast_compset cs
val _ = add_lexparse_compset cs
val _ = add_bytecode_compset cs
val _ = add_labels_compset cs
val _ = add_free_vars_compset cs
val _ = add_x64_compset cs
val _ = computeLib.add_thms  [basis_env_eq,compile_primitives_def,get_all_asts_def,remove_labels_all_asts_def] cs

val _ =
      let
        fun code_labels_ok_conv tm =
          EQT_INTRO
            (get_code_labels_ok_thm
          (rand tm))
      in
        computeLib.add_conv(``code_labels_ok``,1,code_labels_ok_conv) cs ;
        compute_basicLib.add_datatype ``:bc_inst`` cs;
        computeLib.add_thms [uses_label_def] cs
      end
val _ = compute_basicLib.add_datatype ``:comp_environment`` cs

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
      val ast = rand (rhsThm t1)

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

      val rem_labels = with_flag (quiet,true) eval ``remove_labels_all_asts (\x.0) (Success ^(p7))``

      (*Remove labels for bytecode*)
      val p8 = rhsThm rem_labels |> rand

      (*Remove labels for asm*)
      val rem_labels = with_flag (quiet,true) eval ``remove_labels_all_asts real_inst_length (Success ^(p7))``

      (*Bytecode to asm*)
      val asm = eval ``x64_code 0 ^(rhsThm rem_labels |> rand)``
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

(*
val () = set_trace "pp_avoids_symbol_merges" 0

fun take 0 (x::xs) = x
|   take n (_::xs) = take (n-1) xs;

fun i n (ex:allIntermediates) = take n (#ils ex);
*)
