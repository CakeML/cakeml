structure libmLib =
struct

  (* Dandelion *)
  open realZeroLib floverConnTheory;
  (* CakeML & FloVer *)
  open FloVerToCakeMLTheory FloVerToCakeMLProofsTheory expressionsLib
       basisProgTheory basis_ffiTheory cfHeapsBaseTheory basis cfTacticsLib
       ml_translatorLib cfSupportTheory;

  val _ = translation_extends "basisProg";

  (** Literal SML level copy of Dandelions supported datatypes **)
  datatype mf = Exp | Sin | Cos | Atn | Sqrt | Log

  exception libmGenException of string;

  val approxSteps = “16:num”; (** TODO: make this a parameter ? **)

  fun mfToSollya (f:mf) : string =
  case f of
    Exp => "exp"
  | Sin => "sin"
  | Cos => "cos"
  | Atn => "atan"
  | Sqrt => "sqrt"
  | Log => "log";

  val zero_eq = GSYM $ Q.SPEC ‘1’ REAL_DIV_LZERO

  (** For debugging the implement function
  val certDef = cosDeg3Theory.cos_example_def
  val certValid = cosDeg3Theory.err_sound_thm
  **)

  (** implement produce CakeML code for elementary functions Input: f, a math function to be implemented in CakeML with an error bound
          iv, an interval constraint for the function inputs
    Output: a CF theorem relating the code for the mathematical function to its
            real equivalent
    **)
  local
    fun REV_MATCH_MP th1 th2 = MATCH_MP th2 th1
  in
  fun implement (certDef:thm) :thm = let
    val certValid = validateCert certDef approxSteps
    val thePoly = certValid |> SPEC_ALL |> concl |> dest_imp |> snd
                  |> rator |> rand |> rand |> rand |> rator |> rand
    val floverExpThm = EVAL “poly2FloVer ^thePoly” |> ONCE_REWRITE_RULE [zero_eq]
    val floverPoly_bisimThm =
      SPEC thePoly evalPoly_Flover_eval_bisim |> REWRITE_RULE [floverExpThm]
    val floverExpTm = floverExpThm |> rhs o concl
    val floverFloatExpThm = EVAL “toFloVerFloatExp ^floverExpTm” |> ONCE_REWRITE_RULE [zero_eq]
    val floverFloatExpTm = floverFloatExpThm |> rhs o concl
    val floverRatExpThm = realExp2ratExpConv floverFloatExpTm
    val floverRatExpTm = floverRatExpThm |> rhs o concl |> rand
    val floverToCmlRealThm = EVAL “toCmlRealExp ^floverRatExpTm”
    val floverToCmlFloatThm = EVAL “toCmlFloatProg ^floverFloatExpTm”
    val is64BitEvalThm = EVAL “is64BitEval ^floverFloatExpTm” |> SIMP_RULE std_ss []
    val noDowncastThm = EVAL “noDowncast ^floverFloatExpTm” |> SIMP_RULE std_ss []
    val theEnv = EVAL “FloverMapTree_insert (Var 0) M64 FloverMapTree_empty” |> rhs o concl
    val is64BitEnvThm = EVAL “is64BitEnv ^theEnv” |> SIMP_RULE std_ss [CaseEq"expr"]
    val P = EVAL “getPrecondFromCert ^(certDef |> rhs o concl)”
    val ivbounds  = EVAL “inferIntervalbounds ^floverFloatExpTm ^(P |> rhs o concl) FloverMapTree_empty” |> rhs o concl |> optionSyntax.dest_some
    val typeMap = EVAL “case getValidMap ^theEnv ^floverFloatExpTm FloverMapTree_empty of Succes G => G” |> rhs o concl
    val errbounds = EVAL “inferErrorbound ^floverFloatExpTm ^typeMap ^ivbounds FloverMapTree_empty” |> rhs o concl |> optionSyntax.dest_some
    val cc_valid = EVAL “CertificateChecker ^floverFloatExpTm ^errbounds ^(P |> rhs o concl) ^theEnv”
    val find_thm = EVAL “FloverMapTree_find ^floverFloatExpTm ^errbounds”
    val err = find_thm |> rhs o concl |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
    val err_sound_thm =
      MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] FloVer_CakeML_sound_error) floverRatExpThm
      |> REV_MATCH_MP $ GSYM floverToCmlRealThm
      |> REV_MATCH_MP $ GSYM floverToCmlFloatThm
      |> REV_MATCH_MP is64BitEvalThm
      |> REV_MATCH_MP noDowncastThm
      |> REV_MATCH_MP is64BitEnvThm
      |> REV_MATCH_MP cc_valid
      |> REWRITE_RULE [find_thm]
      |> SIMP_RULE std_ss []
    val theFunction =
      (** FIXME: inject name?? **)
      “[Dletrec unknown_loc [("cos","x0",
            (^(floverToCmlFloatThm |> rhs o concl |> optionSyntax.dest_some)))]]”
      |> REWRITE_CONV [machine_ieeeTheory.float_to_fp64_def]
      |> CONV_RULE $ RHS_CONV EVAL
      |> rhs o concl
    val _ = append_prog theFunction;
    val st = get_ml_prog_state();
      val theFunction_v_def = DB.find_in ("cos_v_def")
                            (DB.thy (Theory.current_theory()))|> hd |> #2 |> #1
    val theFunSpec_thm =
      Q.prove (
        ‘! env (st:'ffi semanticPrimitives$state).
         env = merge_env basisProg_env_2 init_env with v :=
              (build_rec_env
                    [("cos","x0",
                      FpOptimise NoOpt
                        (App (FP_bop FP_Add)
                           [App FpFromWord
                              [Lit
                                 (Word64
                                    ((real_to_float roundTiesToEven
                                        (4289449735 / 4294967296)).Sign @@
                                     (real_to_float roundTiesToEven
                                        (4289449735 / 4294967296)).Exponent @@
                                     (real_to_float roundTiesToEven
                                        (4289449735 / 4294967296)).
                                     Significand))];
                            App (FP_bop FP_Mul)
                              [Var (Short "x0");
                               App (FP_bop FP_Add)
                                 [App FpFromWord
                                    [Lit
                                       (Word64
                                          ((real_to_float roundTiesToEven
                                              (139975391 / 8589934592)).Sign @@
                                           (real_to_float roundTiesToEven
                                              (139975391 / 8589934592)).
                                           Exponent @@
                                           (real_to_float roundTiesToEven
                                              (139975391 / 8589934592)).
                                           Significand))];
                                  App (FP_bop FP_Mul)
                                    [Var (Short "x0");
                                     App (FP_bop FP_Add)
                                       [App FpFromWord
                                          [Lit
                                             (Word64
                                                ((real_to_float
                                                    roundTiesToEven
                                                    (-2408138823 / 4294967296)).
                                                 Sign @@
                                                 (real_to_float
                                                    roundTiesToEven
                                                    (-2408138823 / 4294967296)).
                                                 Exponent @@
                                                 (real_to_float
                                                    roundTiesToEven
                                                    (-2408138823 / 4294967296)).
                                                 Significand))];
                                        App (FP_bop FP_Mul)
                                          [Var (Short "x0");
                                           App (FP_bop FP_Add)
                                             [App FpFromWord
                                                [Lit
                                                   (Word64
                                                      ((real_to_float
                                                          roundTiesToEven
                                                          (2948059219 /
                                                           34359738368)).Sign @@
                                                       (real_to_float
                                                          roundTiesToEven
                                                          (2948059219 /
                                                           34359738368)).
                                                       Exponent @@
                                                       (real_to_float
                                                          roundTiesToEven
                                                          (2948059219 /
                                                           34359738368)).
                                                       Significand))];
                                              App (FP_bop FP_Mul)
                                                [Var (Short "x0");
                                                 App FpFromWord
                                                   [Lit
                                                      (Word64
                                                         ((real_to_float
                                                             roundTiesToEven
                                                             0).Sign @@
                                                          (real_to_float
                                                             roundTiesToEven
                                                             0).Exponent @@
                                                          (real_to_float
                                                             roundTiesToEven
                                                             0).Significand))]]]]]]]]]))]
                    (merge_env basisProg_env_2 init_env)
                    (merge_env basisProg_env_2 init_env).v) /\
         FST (^(P |> rhs o concl) 0) <= fp64_to_real (compress_word (Fp_const fp)) /\
         fp64_to_real (compress_word (Fp_const fp)) <= SND (^(P |> rhs o concl) 0) /\
         fp64_isFinite (compress_word (Fp_const fp)) /\
         DOUBLE (Fp_const fp) v ⇒
        app (p:'ffi ffi_proj) ^(fetch_v "cos" st)
          [v]
          (emp)
          (POSTv rv.
            &(case evaluate st
              (env with v := nsAppend (Bind [("x0",v)] []) env.v)
              [^(floverToCmlFloatThm |> rhs o concl |> optionSyntax.dest_some)] of
                | (_, Rval [FP_WordTree fp]) =>
                  DOUBLE fp rv /\
                  (case evaluate (empty_state with
            fp_state :=
              empty_state.fp_state with
              <|real_sem := T; canOpt := FPScope NoOpt|>)
            (env with v := toRspace (nsAppend (Bind [("x0",v)] []) env.v))
              [^(floverToCmlRealThm |> rhs o concl |> optionSyntax.dest_some)] of
                  | (_, Rval [Real r]) => real$abs (r - fp64_to_real (compress_word fp)) <= ^err
                  | _ => F)
                | _ => F))’,
        rpt strip_tac
        >> qmatch_goalsub_abbrev_tac ‘nsAppend flEnv env.v’
        >> qspec_then ‘flEnv’ mp_tac err_sound_thm
        >> impl_tac
        >- (
          unabbrev_all_tac >> gs[usedVars_P_sound_def, usedVars_def]
          >> qmatch_goalsub_abbrev_tac ‘domain theVars’
          >> ‘theVars = insert 0 () LN’ by (unabbrev_all_tac >> EVAL_TAC)
          >> pop_assum $ rewrite_tac o single
          >> rewrite_tac [EVAL “insert 0 () LN”]
          >> rpt strip_tac
          >> ‘x = 0’ by gs[]
          >> gvs[namespaceTheory.nsLookup_def, DOUBLE_def])
        >> disch_then $ qspec_then ‘env’ strip_assume_tac
        >> gs[app_def, app_basic_def] >> rpt strip_tac
        >> simp[semanticPrimitivesTheory.do_opapp_def, theFunction_v_def]
        >> simp[semanticPrimitivesTheory.find_recfun_def]
        >> Q.REFINE_EXISTS_TAC ‘Val fpN’
        >> simp[evaluate_to_heap_def, evaluate_ck_def]
        >> gs[emp_def]
        >> first_x_assum $ qspec_then
            ‘(st' with fp_state := (st'.fp_state with <| real_sem := F; canOpt := FPScope Opt |>))’
            strip_assume_tac
        >> first_x_assum $ mp_then Any mp_tac
            (INST_TYPE [“:'a”|->“:'ffi”, “:'b”|->“:'ffi”] pureExpsTheory.isPureExpList_swap_state)
        >> gs[pureExpsTheory.isPureExp_def, pureExpsTheory.isPureOp_def]
        >> strip_tac
        >> qexists_tac ‘FP_WordTree fp'’
        >> qexists_tac ‘EMPTY’ >> qexists_tac ‘EMPTY’
        >> qexists_tac ‘st2heap p (st' with clock := 0)’
        >> rpt conj_tac
        >- gs[SPLIT_def, SPLIT3_def]
        >- gs[cond_def, DOUBLE_def]
        >> qexists_tac ‘0’ >> qexists_tac ‘st' with clock := 0’
        >> unabbrev_all_tac
        >> first_x_assum $ qspec_then ‘st' with clock := 0’ mp_tac
        >> qmatch_goalsub_abbrev_tac ‘nsAppend _ newEnv’
        >> ‘nsAppend (Bind [("x0", v)] []) newEnv = nsBind "x0" v newEnv’
          by (Cases_on ‘newEnv’ >> gvs[namespaceTheory.nsAppend_def, namespaceTheory.nsBind_def])
        >> pop_assum $ rewrite_tac o single
        >> disch_then $ rewrite_tac o single o GSYM
        >> qmatch_goalsub_abbrev_tac ‘evaluate _ (merge_env _ _ with v := nsBind _ _ newEnv2) _ = _’
        >> ‘newEnv = newEnv2’ by (unabbrev_all_tac >> gs[FUN_EQ_THM] >> rpt $ AP_THM_TAC
                                  >> AP_TERM_TAC
                                  >> gs[] >> cheat)
        >> gs[]
        >> AP_TERM_TAC >> gs[] >> cheat)
    in
      theFunSpec_thm
    end

end

(** UNUSED

  local
    fun removeDots s =
      String.translate (fn c => if c = #"." then "" else Char.toString c) s
  in
  (**
    Input: f:mf, the function to approximate;
           iv:string * string, the input constraints as lower and upper bound in
                               dot notation i.e. "0.1"
  **)
  fun mkSollyaCall (f:mf) (iv:string * string) = let
    val sollyaInp =
      "oldDisplay=display;\n" ^
      "display = powers!;\n" ^
      "approxPrec = 23;\n" ^ (* TODO: Make parameter? *)
      "deg = 3;\n" ^ (* TODO: Same here? *)
      "f = " ^ (mfToSollya f) ^ "(x);\n"^
      "dom = ["^fst(iv)^"; "^snd(iv)^"];\n" ^
      "p = fpminimax(f, deg, [|approxPrec,approxPrec...|], dom, absolute);\n" ^
      "derivativeZeros = findzeros(diff(p-f),dom);\n" ^
      "maximum=0;\n" ^
      "for t in derivativeZeros do {\n" ^
      "  r = evaluate(abs(p-f), t);\n" ^
      "  if sup(r) > maximum then { maximum=sup(r); argmaximum=t; };\n" ^
      "  if (evaluate(diff(p-f),inf(t)) * evaluate (diff(p-f),sup(t)) <= 0 ) then {\n" ^
      "  print (\"Ok zero:\");\n" ^
      "    print (\"    (\", mantissa (inf(t)), \" * inv (2 pow\", -exponent(inf(t)), \"),\");\n" ^
      "    print (\"     \", mantissa (sup(t)), \" * inv (2 pow\", -exponent(sup(t)), \"));\");\n" ^
      "  };\n" ^
      "};\n"
    val outputFile = "/tmp/"^(mfToSollya f)^ removeDots (fst iv) ^ removeDots (snd iv) ^ ".sollya"
    val fd = TextIO.openOut outputFile
    val _ = (TextIO.output(fd, sollyaInp); TextIO.closeOut fd);
    val _ =

print("<|");
print("  poly := [");
for i from 0 to degree(p) do{
    coeff_p = coeff(p, i);
    print("    ", mantissa (coeff_p), " * inv ( 2 pow ", -exponent(coeff_p), ");");
};
print ("    ];");
print("  eps := ", mantissa(maximum), " * inv (2 pow", -exponent(maximum), ");");
print ("  iv := [ (\"x\",");
print ("    (", mantissa (inf(dom)), " * inv (2 pow", -exponent(inf(dom)), "),");
print ("     ", mantissa (sup(dom)), " * inv (2 pow", -exponent(sup(dom)), ")))];");
print("|>");
    val

  (** TODO: Implement;
    returns a Sollya certificate for the math function to be checked by
    Dandelion as well as guesses for the zeros **)
  fun getApproxForFun (f:mf) iv :(term*term) = (“T”,“T”);
**)
