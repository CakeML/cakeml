open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     mlw8arrayProgTheory basisFunctionsLib

val _ = new_theory "helloProg"

val _ = translation_extends"mlw8arrayProg";

fun basis_st () = get_ml_prog_state ()

(* TODO: these modules should be inherited rather than re-verified here *)

(* Word8Array module -- CF verified *)


(* CharIO -- CF verified *)

val _ = ml_prog_update (open_module "CharIO");

fun derive_eval_thm v_name e = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val lemma = goal
    |> (NCONV 50 (SIMP_CONV (srw_ss()) [Once bigStepTheory.evaluate_cases,
            PULL_EXISTS,do_app_def,store_alloc_def,LET_THM]) THENC EVAL)
  val v_thm = prove(mk_imp(lemma |> concl |> rand,goal),fs [lemma])
                 |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL
  val v_tm = v_thm |> concl |> rand |> rand |> rand
  val v_def = define_abbrev true v_name v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end

val e = ``(App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "write_loc" e) "write" [])

val Apps_def = tDefine "Apps" `
  (Apps [x;y] = App Opapp [x;y]) /\
  (Apps [] = ARB) /\
  (Apps xs = App Opapp [Apps (FRONT xs); LAST xs])`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_FRONT]);

val LetApps_def = Define `
  LetApps n f args = Let (SOME n) (Apps (Var f::args))`;

val e =
  ``Let (SOME "c") (Apps [Var (Long "Word8Array" "update"); Var (Short "write");  Lit (IntLit 0); Var (Short "c")])
     (Let (SOME "_") (App (FFI "write") [Var (Short "write")])
        (Var (Short "c")))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"write"`` ``"c"`` e "write_v")

val _ = ml_prog_update (close_module NONE);

val stdout_fun_def = Define `
  stdout_fun = (\_ bytes s. case (bytes,s) of (* write *)
                    | ([w],Str output) => SOME ([w],Str (output ++ [CHR (w2n w)]))
                    | _ => NONE)`

val STDOUT_def = Define `
  STDOUT output = IO (Str output) stdout_fun ["write"]`

val CHAR_IO_def = Define `
  CHAR_IO = SEP_EXISTS w. W8ARRAY write_loc [w]`;

val write_spec = Q.store_thm ("write_spec",
  `!a av n nv v.
     WORD (c:word8) cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.write" (basis_st()))
       [cv]
       (CHAR_IO * STDOUT output)
       (POSTv uv. cond (UNIT_TYPE () uv) * CHAR_IO * STDOUT (output ++ [CHR (w2n c)]))`,
  xcf "CharIO.write" (basis_st())
  \\ fs [CHAR_IO_def] \\ xpull
  \\ xlet `POSTv zv. STDOUT output * W8ARRAY write_loc [c] *
                     & (UNIT_TYPE () zv)`
  THEN1
   (xapp \\ xsimpl \\ fs [CHAR_IO_def,EVAL ``write_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC \\ fs [])
  \\ xlet `POSTv _. STDOUT (output ++ [CHR (w2n c)]) * W8ARRAY write_loc [c]`
  THEN1
   (xffi
    \\ fs [EVAL ``write_loc``, STDOUT_def]
    \\ `MEM "write" ["write"]` by EVAL_TAC \\ instantiate \\ xsimpl
    \\ EVAL_TAC \\ fs [ORD_BOUND, CHR_ORD])
  \\ xret \\ xsimpl);

val e =
  ``LetApps "_" (Long "CharIO" "write") [Lit (Word8 (n2w (ORD #"H")))]
      (LetApps "_" (Long "CharIO" "write") [Lit (Word8 (n2w (ORD #"i")))]
         (Var (Short "_")))`` |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"main"`` ``"c"`` e "main_v")

val main_spec = Q.store_thm ("main",
  `!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "main" (basis_st()))
        [cv]
        (CHAR_IO * STDOUT "")
        (POSTv uv. CHAR_IO * STDOUT "Hi")`,
  xcf "main" (basis_st())
  \\ xlet `POSTv v. CHAR_IO * STDOUT "H"` THEN1
   (xapp \\ qexists_tac `emp` \\ qexists_tac `""` \\ qexists_tac `n2w (ORD #"H")`
    \\ xsimpl)
  \\ xlet `POSTv v. CHAR_IO * STDOUT "Hi"` THEN1
   (xapp \\ qexists_tac `emp` \\ qexists_tac `"H"` \\ qexists_tac `n2w (ORD #"i")`
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
