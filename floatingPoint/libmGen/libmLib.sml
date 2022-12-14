(*
  Implementation of automatic generation of libm functions
*)
structure libmLib =
struct

  (* Dandelion *)
  open realZeroLib floverConnTheory;
  (* CakeML & FloVer *)
  open FloVerToCakeMLTheory FloVerToCakeMLProofsTheory expressionsLib
       basisProgTheory basis_ffiTheory cfHeapsBaseTheory basis cfTacticsLib
       ml_translatorLib cfSupportTheory;
  open libmTheory;
  open binary_ieeeLib;

  val _ = translation_extends "basisProg";

  exception libmGenException of string;

  val approxSteps = “16:num”; (** TODO: make this a parameter ? **)

  val zero_eq = GSYM $ Q.SPEC ‘1’ REAL_DIV_LZERO

  val _ = Globals.max_print_depth := 20;

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
  fun implement (certDef:thm) cmlFname :thm = let
    val certValid = validateCert certDef approxSteps
    val thePoly = certValid |> SPEC_ALL |> concl |> dest_imp |> snd
                  |> rator |> rand |> rand |> rand |> rator |> rand
    val theTransc = EVAL “^(certDef |> rhs o concl).transc”
    val thePoly_nonzero = EVAL “^thePoly <> []” |> SIMP_RULE std_ss []
    val thePoly_getThm = EVAL “^(certDef |> rhs o concl).poly = ^thePoly” |> SIMP_RULE std_ss []
    val floverExpThm = EVAL “poly2FloVer ^thePoly” |> ONCE_REWRITE_RULE [zero_eq]
    val floverExpTm = floverExpThm |> rhs o concl
    val floverFloatExpThm = EVAL “toFloVerFloatExp ^floverExpTm” |> ONCE_REWRITE_RULE [zero_eq]
    val floverFloatExpTm = floverFloatExpThm |> rhs o concl
    val floverExpRatEqThm = EVAL “poly2FloVer ^thePoly = toREval ^floverFloatExpTm”
      |> SIMP_RULE std_ss []
    val floverToCmlFloatThm = EVAL “toCmlFloatProg ^floverFloatExpTm”
                        |> SIMP_RULE std_ss [machine_ieeeTheory.float_to_fp64_def]
                        |> REWRITE_RULE [binary_ieeeTheory.real_to_float_def,
                                         binary_ieeeTheory.float_round_def]
                        |> CONV_RULE $ RHS_CONV EVAL
    val is64BitEvalThm = EVAL “is64BitEval ^floverFloatExpTm” |> SIMP_RULE std_ss []
    val noDowncastThm = EVAL “noDowncast ^floverFloatExpTm” |> SIMP_RULE std_ss []
    val theEnv = EVAL “FloverMapTree_insert (Var 0) M64 FloverMapTree_empty” |> rhs o concl
    val is64BitEnvThm = EVAL “is64BitEnv ^theEnv” |> SIMP_RULE std_ss [CaseEq"expr"]
    val P = EVAL “getPrecondFromCert ^(certDef |> rhs o concl)”
    val P_zero = EVAL “^(P |> rhs o concl) 0”
    val usedVarsThm = EVAL “usedVars ^floverFloatExpTm”
    val ivbounds  =
      EVAL “inferIntervalbounds ^floverFloatExpTm ^(P |> rhs o concl) FloverMapTree_empty”
      |> rhs o concl |> optionSyntax.dest_some
    val typeMap =
      EVAL “case getValidMap ^theEnv ^floverFloatExpTm FloverMapTree_empty of Succes G => G”
      |> rhs o concl
    val errbounds =
      EVAL “inferErrorbound ^floverFloatExpTm ^typeMap ^ivbounds FloverMapTree_empty”
      |> rhs o concl |> optionSyntax.dest_some
    val cc_valid = EVAL “CertificateChecker ^floverFloatExpTm ^errbounds ^(P |> rhs o concl) ^theEnv”
    val find_thm = EVAL “FloverMapTree_find ^floverFloatExpTm ^errbounds”
    val floverToCmlFloatTm = floverToCmlFloatThm |> rhs o concl |> optionSyntax.dest_some
    val theFunction =
      (** FIXME: inject name?? **)
      “[Dlet unknown_loc (Pvar ^(stringSyntax.fromMLstring cmlFname)) (Fun "x0"
            ^floverToCmlFloatTm)]”
    val theEnv_before = get_ml_prog_state()
      |> ml_progLib.clean_state
      |> ml_progLib.remove_snocs
      |> ml_progLib.get_env
    val _ = append_prog theFunction;
    val st = get_ml_prog_state();
    val theFunction_v_def = DB.find_in (cmlFname ^ "_v_def") $ DB.thy (Theory.current_theory())|> hd |> #2 |> #1
    val do_opapp_thm = “do_opapp [^(fetch_v cmlFname st); v]”
                      |> SIMP_CONV std_ss [theFunction_v_def]
                      |> CONV_RULE $ RHS_CONV EVAL
    val theEnv_term = theEnv_before |> SIMP_CONV std_ss [ml_progTheory.merge_env_def, namespaceTheory.nsAppend_def, nsBind_nsAppend] |> rhs o concl
    val mkEnv_def = Define ‘mkEnv v = ^theEnv_term with v := nsAppend (Bind [("x0", v)] []) ^(theEnv_term).v’
    val approxErr_def = Define ‘approxErr = ^(certValid |> SPEC_ALL |> concl |> rand |> rand)’
    val roundoffErr_def = Define ‘roundoffErr = ^(find_thm |> rhs o concl |> optionSyntax.dest_some |> dest_pair |> snd)’
    val fullErr_tm = EVAL“approxErr + roundoffErr”|> rhs o concl
    val fullErr_def = Define ‘fullErr = ^fullErr_tm’
    val theCMLprog_def = Define ‘theCMLprog = ^floverToCmlFloatTm’
    in
      MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] theFunSpec_thm_general) P
      |> REV_MATCH_MP floverExpRatEqThm
      |> REV_MATCH_MP thePoly_nonzero
      |> REV_MATCH_MP thePoly_getThm
      |> REV_MATCH_MP P_zero
      |> REV_MATCH_MP is64BitEvalThm
      |> REV_MATCH_MP noDowncastThm
      |> REV_MATCH_MP is64BitEnvThm
      |> REV_MATCH_MP usedVarsThm
      |> REV_MATCH_MP cc_valid
      |> REWRITE_RULE [theTransc]
      |> REV_MATCH_MP $ SIMP_RULE std_ss [GSYM AND_IMP_INTRO] certValid
      |> REV_MATCH_MP find_thm
      |> REV_MATCH_MP $ GSYM floverToCmlFloatThm
      |> REV_MATCH_MP do_opapp_thm
      |> Q.SPEC ‘^theEnv_before’
      |> SIMP_RULE std_ss [ml_progTheory.merge_env_def, namespaceTheory.nsAppend_def, nsBind_nsAppend]
      |> CONV_RULE $ RATOR_CONV EVAL
      |> SIMP_RULE std_ss []
      |> CONV_RULE $ RATOR_CONV EVAL
      |> SIMP_RULE std_ss [GSYM mkEnv_def, GSYM approxErr_def, GSYM roundoffErr_def, GSYM theCMLprog_def]
    end
  end;

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
