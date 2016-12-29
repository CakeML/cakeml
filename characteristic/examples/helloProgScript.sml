open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     mlcharioProgTheory basisFunctionsLib

val _ = new_theory "helloProg"

val _ = translation_extends"mlcharioProg";

fun basis_st () = get_ml_prog_state ()

val e =
  ``LetApps "_" (Long "CharIO" "write") [Lit (Word8 (n2w (ORD #"H")))]
      (LetApps "_" (Long "CharIO" "write") [Lit (Word8 (n2w (ORD #"i")))]
         (Var (Short "_")))`` |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"main"`` ``"c"`` e "main_v")

val main_spec = Q.store_thm ("main",
  `!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "main" (basis_st()))
        [cv]
        (STDOUT [])
        (POSTv uv. STDOUT (MAP (n2w o ORD) "Hi"))`,
  xcf "main" (basis_st())
  \\ xlet `POSTv v. STDOUT [n2w(ORD #"H")]` THEN1
   (xapp \\ qexists_tac `emp` \\ qexists_tac `[]` \\ qexists_tac `n2w (ORD #"H")`
    \\ xsimpl)
  \\ xlet `POSTv v. STDOUT (MAP (n2w o ORD) "Hi")` THEN1
   (xapp \\ qexists_tac `emp` \\ qexists_tac `[n2w(ORD #"H")]` \\ qexists_tac `n2w (ORD #"i")`
    \\ xsimpl)
  \\ xvar \\ fs [] \\ xsimpl);

val main_applied = let
  val e = ``Apps [Var (Short "main"); Lit (IntLit 0)] ``
          |> EVAL |> concl |> rand
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val th = goal |> NCONV 6 (SIMP_CONV (srw_ss())
                    [Once bigStepTheory.evaluate_cases,PULL_EXISTS])
  val p = find_term (can (match_term ``lookup_var_id _ _ = SOME _``)) (concl th)
  val th = th |> SIMP_RULE std_ss [EVAL p]
  val exists_lemma = METIS_PROVE []
    ``(?x1 x2 x3 x4 x5 x6. P x1 x2 x3 x4 x5 x6) <=>
      (?x3 x4 x5 x6 x1 x2. P x1 x2 x3 x4 x5 x6)``
  val st = goal |> rator |> rator |> rand
  val th =
    main_spec |> SPEC_ALL |> Q.INST_TYPE [`:'ffi`|->`:'a`]
     |> REWRITE_RULE [cfAppTheory.app_basic_rel,cfAppTheory.app_def]
     |> Q.SPEC `st2heap (p:'a ffi_proj) ^st`
     |> Q.SPEC `{}`
     |> Q.SPEC `^st`
     |> SIMP_RULE std_ss [PULL_EXISTS,
          cfHeapsBaseTheory.res_case_def,
          cfHeapsBaseTheory.POSTv_ignore,
          cfHeapsBaseTheory.SPLIT3_emp3,
          cfHeapsBaseTheory.SPLIT_emp2]
     |> Q.INST [`cv`|->`Litv (IntLit 0)`]
     |> SIMP_RULE std_ss [Once exists_lemma]
     |> SIMP_RULE std_ss [GSYM PULL_EXISTS,GSYM th]
  in th end

val raw_evaluate_prog = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
  val th = th |> SPEC_ALL |> UNDISCH |> Q.SPEC `"_"` |> DISCH_ALL |> GEN_ALL
  val th = ConseqConv.WEAKEN_CONSEQ_CONV_RULE
             (ConseqConv.CONSEQ_REWRITE_CONV ([],[],[th])) main_applied
  val tm = th |> concl |> find_term (listSyntax.is_snoc)
  val entire_program_def = Define `entire_program = ^tm`
  val th = th |> SIMP_RULE std_ss [GSYM entire_program_def,PULL_EXISTS,
                   ml_progTheory.ML_code_def,ml_progTheory.Prog_def]
  in th end

val _ = export_theory ()
