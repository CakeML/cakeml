structure allPP = struct local
open astPP modPP conPP exhPP patPP
open preamble compilerComputeLib
open inferenceComputeLib parsingComputeLib

val cmp = wordsLib.words_compset ()

(*TODO: Some of these should possiblymove into their own compute libs*)
val () = computeLib.extend_compset
    [computeLib.Extenders
      [compilerComputeLib.add_compiler_compset,
       inferenceComputeLib.add_inference_compset,
       parsingComputeLib.add_parsing_compset
      ],
     computeLib.Defs
      [lexer_funTheory.lexer_fun_def
      ,cmlParseTheory.parse_prog_def
      ,inferTheory.init_config_def
      ,inferTheory.infertype_prog_def
      ,inferTheory.empty_inf_decls_def
      ,inferTheory.init_env_def
      ,initialProgramTheory.prim_types_program_def
      ,initialProgramTheory.basis_program_def
      ,initialProgramTheory.mk_binop_def
      ,initialProgramTheory.mk_unop_def
      ,initialProgramTheory.mk_ffi_def
      ,backendTheory.prim_config_def
      ,optionTheory.OPTION_MAP2_DEF
      ,miscTheory.anub_def
      ]
    ] cmp

val eval = computeLib.CBV_CONV cmp

val () = disable_astPP();
val () = disable_modPP();
val () = disable_conPP();
val () = disable_exhPP();
val () = disable_patPP();

(*RHS of theorem to term*)
val rhsThm = rhs o concl;

(* Basis configuration *)
val basis_config =rhsThm (eval ``FST(to_pat prim_config basis_program)``)

in

exception compilationError of string;
type allIntermediates = {
  ils:term list}
(*Return all intermediates during compilation in a record*)

fun allIntermediates prog =
  let
      val t1 = rhsThm (eval ``parse_prog (lexer_fun ^(prog))``)

      val ast = if optionSyntax.is_none t1
                then raise compilationError "Parse Error"
                else optionSyntax.dest_some t1;

      val infer = rhsThm (eval ``infertype_prog init_config (prim_types_program ++ basis_program ++ ^(ast))``)

      val _ = if optionSyntax.is_none infer
              then raise compilationError "Type Inference Error"
              else ()

      val c = basis_config

      val cp = rhsThm (eval ``
        let (c,p) = (^(c),^(ast)) in
        let (c',p) = source_to_mod$compile c.source_conf p in
        let c = c with source_conf := c' in
        (c,p)``)
      val (c,mod_prog) = pairSyntax.dest_pair cp

      val cp = rhsThm (eval ``
        let (c,p) = (^(c),^(mod_prog)) in
        let (c',p) = mod_to_con$compile c.mod_conf p in
        let c = c with mod_conf := c' in
        (c,p)``)
      val (c,con_prog) = pairSyntax.dest_pair cp

      val ce = rhsThm (eval ``
        let (c,p) = (^(c),^(con_prog)) in
        let (n,e) = con_to_dec$compile c.source_conf.next_global p in
        let c = c with source_conf updated_by (λc. c with next_global := n) in
        (c,e)``)
      val (c,dec_prog) = pairSyntax.dest_pair ce

      val exh_prog = rhsThm (eval``
        let (c,e) = (^(c),^(dec_prog)) in
        let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
        e``)

      val pat_prog = rhsThm (eval``
        exh_to_pat$compile ^(exh_prog)``)

  in
     {ils=[ast,mod_prog,con_prog,dec_prog,exh_prog,pat_prog]}
  end;
end
end


(*Helper for test calls*)

(*

val collectAnnotations :(term list ref)= ref ([]:term list);

val () = set_trace "pp_avoids_symbol_merges" 0

fun take 0 (x::xs) = x
|   take n (_::xs) = take (n-1) xs;

fun i n (ex:allIntermediates) = take n (#ils ex);
*)
