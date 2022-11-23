(**
  Library implementing the automatic computations
  done by Dandelion
**)
structure realZeroLib =
struct
  open RealArith realTheory realLib realSyntax polyTheory;
  open realPolyTheory realPolyProofsTheory checkerTheory moreRealTheory
       sturmComputeTheory transcLangTheory transcIntvSemTheory approxPolyTheory
       transcApproxSemTheory transcReflectTheory euclidDivTheory;
  open bossLib preambleDandelion;

  exception ZeroLibErr of string;

  val useBinary = ref false;
  val createMetiTarskiQuery = ref false;
  val createCoqIntervalQuery = ref false;
  val createSOSFile = ref false;

  val _ = computeLib.add_thms [REAL_INV_1OVER] computeLib.the_compset;
  val _ = computeLib.add_funs [polyTheory.poly_diff_def, polyTheory.poly_diff_aux_def, polyTheory.poly_def]
  (* val _ = bitArithLib.use_karatsuba(); *)

  fun appOrErr (P:term -> bool) (f:term -> 'a) (t:term) (errMsg:string) :'a =
    if P t then f t else raise ZeroLibErr errMsg;

  fun extractDom (t:term) (var:term) : term * term =
    let
      val (lhsCond, rhsCond) = appOrErr is_conj dest_conj t "Precondition not a conjunction"
      val (lhs1, rhs1) = appOrErr realSyntax.is_leq realSyntax.dest_leq lhsCond "Precondition must be a conjunction of <= statements"
      val (lhs2, rhs2) = appOrErr realSyntax.is_leq realSyntax.dest_leq rhsCond "Precondition must be a conjunction of <= statements"
      val (var1, cnst1, isUb) = if is_var lhs1 then (lhs1, rhs1, true)
                         else if is_var rhs1 then (rhs1, lhs1, false)
                         else raise ZeroLibErr "No variable in lhs of precondition"
      val (var2, cnst2) = if is_var lhs2 then (lhs2, rhs2)
                          else if is_var rhs2 then (rhs2, lhs2) else raise ZeroLibErr "No variable in rhs of precondition"
      val cnst1Eval = EVAL cnst1 |> concl |> rhs
      val cnst2Eval = EVAL cnst2 |> concl |> rhs
      val _ = if term_eq var1 var2 andalso term_eq var2 var then ()
              else raise ZeroLibErr "Precondition does not depend only on universally quantified variable"
    in
      if isUb then (cnst2Eval, cnst1Eval) else (cnst1Eval, cnst2Eval)
    end;

  fun arbint2String (i:Arbint.int) =
    let val strList = explode o Arbint.toString $ i
      in
      implode (List.take (strList, (FixedInt.- (List.length strList, 1))))
    end;

  fun cst2String (t:term) =
    if realSyntax.is_div t then (* Term is a fractional constant *)
      let
        val (nom, denom) = realSyntax.dest_div t
        val nomI = appOrErr realSyntax.is_real_literal realSyntax.int_of_term nom "Invalid constant"
        val denomI = appOrErr realSyntax.is_real_literal realSyntax.int_of_term denom "Invalid constant"
      in
        arbint2String nomI ^ "/" ^ arbint2String denomI
      end
    else arbint2String (appOrErr realSyntax.is_real_literal realSyntax.int_of_term t "Invalid constant")

  fun var2String (t:term) =
    if realSyntax.is_pow t then
      let val (var, pow) = realSyntax.dest_pow t
      in
        var2String var ^"^"^Arbnum.toString (appOrErr numSyntax.is_numeral numSyntax.dest_numeral pow "Invalid power")
      end
    else fst (appOrErr is_var dest_var t ("Not a variable "^term_to_string t));

  fun mul2String (t:term) =
   let val (var, cst) = appOrErr realSyntax.is_mult realSyntax.dest_mult t "Not a multiplication"
   in
     var2String var ^ " * " ^ cst2String cst
   end;

  fun poly2String (t:term) =
    if realSyntax.is_plus t then (* Recursion case *)
      let
        val (lhs, rhs) = appOrErr realSyntax.is_plus realSyntax.dest_plus t "Translation error"
        val lhsStr =
          if realSyntax.is_mult lhs then (* The lhs is a multiplication of var with cst *)
            mul2String lhs
          else (* The lhs is a constant *)
            cst2String lhs
      in
        "( " ^ lhsStr ^ " ) + ( " ^ poly2String rhs ^ " )"
      end
    else if realSyntax.is_mult t then mul2String t
    else var2String t;

  infix @^;
  fun x @^ y = x ^ "\n" ^ y;

  fun poly2Sollya (poly:string) (dom:string) : string =
    "oldDisplay=display;" @^
    "display = powers!;  //putting ! after a command supresses its output" @^
    "diam = 1b-200!;" @^
    "p = "^ poly ^";" @^
    "zeros = findzeros(p, "^ dom ^ ");" @^
    "for t in zeros do {" @^
    "  print (\"    (\", mantissa (inf(t)), \" * inv (2 pow\", -exponent(inf(t)), \"),\");" @^
    "  print (\"     \", mantissa (sup(t)), \" * inv (2 pow\", -exponent(sup(t)), \"));\");" @^
    "};";

  (** Compute the number of zeros of polynomial diffP on domain dom **)
  fun STURM_SEQ_CONV (diffP:term) (dom:term) =
    let
      val _ = if not (type_of diffP = “:poly”) orelse not (type_of dom = “:real#real”)
              then raise ZeroLibErr "STURM_SEQ_CONV needs polynomial inputs" else ()
      val diffP2 = Parse.Term ‘diff ^diffP’ |> EVAL
      val _ = print "Starting Sturm Sequence computation\n"
      val sseq_aux = decls "sturm_seq_aux";
      (* val _ = computeLib.monitoring := SOME (same_const (hd sseq_aux)) *)
      val sseqOpt = Parse.Term ‘sturm_seq ^diffP (diff ^diffP)’ |> EVAL
      val sseq = appOrErr optionSyntax.is_some optionSyntax.dest_some (sseqOpt |> concl |> rhs) "Sturm sequence computation failed"
      val th = MATCH_MP sturm_seq_equiv sseqOpt
      val zeroList = Parse.Term ‘numZeros ^diffP (diff ^diffP) ^dom ^sseq’ |> EVAL
      val (res, numZeros) = zeroList |> concl |> rhs |> pairSyntax.dest_pair
      val _ = if Term.compare (res, “Valid”) = EQUAL then () else raise ZeroLibErr "Failed to computed number of zeros"
      val zerosThm = MATCH_MP (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] numZeros_sound) sseqOpt) zeroList |> SIMP_RULE std_ss []
      val iv_valid = zerosThm |> concl |> dest_imp |> fst
      val iv_validThm = Q.prove (‘^iv_valid’, gs[]);
      val zerosThmFull = MATCH_MP zerosThm iv_validThm
      val _ = save_thm ("zerosThmFull", zerosThmFull)
    in
      (print "Finished sturm sequence computations\n"; (zerosThmFull, numZeros))
    end;

  fun getZerosFromSollya polyDiff var lb ub = let
    val polyAsReal = Parse.Term ‘evalPoly ^polyDiff ^var’
                     |> REWRITE_CONV [evalPoly_def]
                     |> SIMP_RULE std_ss [REAL_LDISTRIB, REAL_MUL_LZERO,
                                          REAL_MUL_RZERO, REAL_ADD_LID,
                                          REAL_MUL_ASSOC, REAL_ADD_RID,
                                          pow_simp]
                     |> rhs o concl
    val polyAsString = poly2String polyAsReal
    val sollyaInput = poly2Sollya polyAsString ("[" ^ cst2String lb ^"; " ^ cst2String ub ^"]")
    val fileStr = TextIO.openOut ("/tmp/sollya_input_"^Theory.current_theory()^".sollya")
    val _ = (TextIO.output (fileStr, sollyaInput); TextIO.closeOut fileStr)
    val sollyaPath = OS.FileSys.getDir() ^ "/sollya/sollya-8.0/sollya"
        (* case Process.getEnv "SOLLYADIR" of
        SOME p => p ^ "/sollya"
        | NONE =>
          (let val (instr, outstr) = Unix.streamsOf(Unix.execute("/usr/bin/which", ["sollya"]))
          in TextIO.inputAll(instr) |> explode |> List.rev |> tl |> List.rev |> implode end)
          handle SysErr _ => (print "Could not get path for Sollya\n"; ""); *)
    val (instr, outStr) =
        (Unix.streamsOf(Unix.execute(sollyaPath, ["--warnonstderr",
                  "/tmp/sollya_input_"^Theory.current_theory()^".sollya"])))
        handle SysErr _ => (print ("Could not run Sollya at "^sollyaPath ^ "\n"); raise ZeroLibErr "")
    (*val (instr, outStr) =
      (*Unix.streamsOf(Unix.execute("/home/hbecker/Programs/sollya-7.0/sollya", ["--warnonstderr", "/tmp/sollya_input.sollya"])) *)
      Unix.streamsOf(Unix.execute("sollya", ["--warnonstderr", "/tmp/sollya_input.sollya"])) *)
    in
      "[" ^ TextIO.inputAll(instr) ^ "]:(real#real) list"
    end;

  fun var2HOLlightString (t:term) =
    if realSyntax.is_pow t then
      let val (var, pow) = realSyntax.dest_pow t
      in
        var2String var ^" pow " ^ Arbnum.toString (appOrErr numSyntax.is_numeral numSyntax.dest_numeral pow "Invalid power")
      end
    else fst (appOrErr is_var dest_var t ("Not a variable "^term_to_string t));

  fun mul2HOLlightString (t:term) =
   let val (var, cst) = appOrErr realSyntax.is_mult realSyntax.dest_mult t "Not a multiplication"
   in
     var2HOLlightString var ^ " * (&" ^ cst2String cst ^ ")"
   end;

  fun poly2HOLlightString (t:term) =
    if realSyntax.is_plus t then (* Recursion case *)
      let
        val (lhs, rhs) = appOrErr realSyntax.is_plus realSyntax.dest_plus t "Translation error"
        val lhsStr =
          if realSyntax.is_mult lhs then (* The lhs is a multiplication of var with cst *)
            mul2HOLlightString lhs
          else (* The lhs is a constant *)
            "(&" ^ cst2String lhs ^")"
      in
        "( " ^ lhsStr ^ " ) + ( " ^ poly2HOLlightString rhs ^ " )"
      end
    else if realSyntax.is_mult t then mul2HOLlightString t
    else var2HOLlightString t;

  (** Produces a HOL-light input that calls into REAL_SOS_CONV **)
  fun to_SOS_tm (t:term) = let
    val (var, imp) = appOrErr is_forall dest_forall t "Input term not universally quantified"
    val (pre, conc) = appOrErr is_imp dest_imp imp "Input term not of the form ! x. _ ==> _"
    val (lb, ub) = extractDom pre var
    val (polyAppAbs, eps) = appOrErr realSyntax.is_leq realSyntax.dest_leq conc "Input term not of the form ! x. pre ==> _ <= _"
    val realEps = EVAL eps |> rhs o concl
    val polyApp = rand polyAppAbs
    val (poly, var) = strip_comb polyApp |> snd |> (fn ts => (hd ts, hd (tl ts)))
    val polyAsReal = Parse.Term ‘evalPoly ^poly ^var’
                     |> EVAL
                     |> SIMP_RULE std_ss [REAL_LDISTRIB, REAL_MUL_LZERO,
                                          REAL_MUL_RZERO, REAL_ADD_LID,
                                          REAL_MUL_ASSOC, REAL_ADD_RID,
                                          pow_simp]
                     |> rhs o concl
    val polyAsString = poly2HOLlightString polyAsReal
    val varStr = var2HOLlightString var
    val holStr = "! " ^ varStr ^ ". " ^
                 "(&" ^ cst2String lb ^ "):real <= " ^ varStr ^ " /\\ "  ^
                 varStr ^ " <= (&" ^ cst2String ub ^ "):real ==> " ^
                 "( " ^ polyAsString ^ "):real <= (&" ^ cst2String realEps ^ "):real"
  in
    "#use \"hol.ml\";;\n#use \"Examples/sos.ml\";;\ntime PURE_SOS `" ^ holStr ^ "`;;"
  end;

  fun writeSOSFile (t:term) = let
    val tStr = to_SOS_tm t
    val fileStr = TextIO.openOut ("./" ^ Theory.current_theory() ^ ".ml")
    in
      (TextIO.output (fileStr, tStr); TextIO.closeOut fileStr)
    end;

  (** Takes as input a term of the form ! x. x IN ... ==> poly p x <= eps and
      checks it by using the Sollya tool to infer zeros **)
  fun REAL_ZERO_CONV (t:term) =
    let
      val _ = if (!createSOSFile) then writeSOSFile t else ()
      val (var, imp) = appOrErr is_forall dest_forall t "Input term not universally quantified"
      val (pre, conc) = appOrErr is_imp dest_imp imp "Input term not of the form ! x. _ ==> _"
      val (lb, ub) = extractDom pre var
      val dom = Parse.Term ‘(^lb, ^ub)’
      val (polyAppAbs, eps) = appOrErr realSyntax.is_leq realSyntax.dest_leq conc "Input term not of the form ! x. pre ==> _ <= _"
      val polyApp = rand polyAppAbs
      val (poly, var) = strip_comb polyApp |> snd |> (fn ts => (hd ts, hd (tl ts)))
      val polyDiff = Parse.Term ‘diff ^poly’ |> EVAL
      val (zerosThm, numZeros) = STURM_SEQ_CONV (polyDiff |> concl |> rhs) dom
      val _ = print "Getting zeros from Sollya\n"
      val res = getZerosFromSollya (polyDiff |> rhs o concl) var lb ub
      val _ = print "Got zeros from Sollya\n"
      val zeroList = Parse.Term [QUOTE res]
      val zeros = numSyntax.dest_numeral numZeros |> Arbnum.toInt
    in
      if zeros <= 0 then raise ZeroLibErr "Need to check for at least one zero"
      else
        let
          val _ = print ("Starting zero validation\n");
          val validationThm =
            Parse.Term ‘validateZerosLeqErr ^poly ^dom ^zeroList ^eps ^numZeros’
            |> EVAL
          val _ = save_thm ("validationThm", validationThm)
          val _ = if Term.compare (rhs o concl $ validationThm |> pairSyntax.dest_pair |> fst, “Valid”) = EQUAL then ()
                  else raise ZeroLibErr "Failed to prove validity of zeros found by Sollya"
          val _ = print ("Finished zero validation\n");
          val resThm = (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] validateZerosLeqErr_sound) (GSYM polyDiff))
                        |> Q.SPEC ‘(^lb, ^ub)’ |> SIMP_RULE std_ss []
                        |> (fn th => MATCH_MP th zerosThm)
                        |> (fn th => MATCH_MP th validationThm)
                        |> REWRITE_RULE [AND_IMP_INTRO]
          in
            resThm
          end
    end;

  val var1_thm = EVAL “var 1”;

  fun is_real_const (t:term) =
    is_real_literal t orelse
    (realSyntax.is_div t andalso
      (let val (t1, t2) = realSyntax.dest_div t in (is_real_literal t1 andalso is_real_literal t2) end))

  (** Assumes: vars t = [x] and type_of t = “:real” **)
  fun reflect (t:term) (x:term) : thm * thm =
    if is_real_const t then
      let val pEqThm = EVAL o Parse.Term $ ‘cst ^t’ in
        (Q.SPECL [‘^t’, ‘^x’] polyEvalsTo_Const
        |> REWRITE_RULE [pEqThm]
        |> CONV_RULE $ RATOR_CONV $ RATOR_CONV $ RAND_CONV EVAL,
          pEqThm)
      end
    else if is_var t then
      let val pEqThm = var1_thm in
        (Q.SPECL [‘1’, ‘^t’] (GEN “n:num” polyEvalsTo_Var)
        |> REWRITE_RULE [var1_thm, POW_1]
        |> CONV_RULE $ RATOR_CONV $ RATOR_CONV $ RAND_CONV EVAL,
          pEqThm)
      end
    else if realSyntax.is_plus t then
      let
        val (t1, t2) = realSyntax.dest_plus t
        val (thm1, p1) = reflect t1 x
        val (thm2, p2) = reflect t2 x
        val pEqThm = EVAL o Parse.Term $ ‘^(p1 |> concl |> rhs) +p ^(p2 |> concl |> rhs)’
      in
        (MATCH_MP (MATCH_MP polyEvalsTo_Add thm1) thm2
         |> REWRITE_RULE [pEqThm]
         |> CONV_RULE $ RATOR_CONV $ RATOR_CONV $ RAND_CONV EVAL,
          pEqThm)
      end
    else if realSyntax.is_minus t then
      let
        val (t1, t2) = realSyntax.dest_minus t
        val (thm1, p1) = reflect t1 x
        val (thm2, p2) = reflect t2 x
        val pEqThm = EVAL o Parse.Term $ ‘^(p1 |> concl |> rhs) +p ^(p2 |> concl |> rhs)’
      in
        (MATCH_MP (MATCH_MP polyEvalsTo_Sub thm1) thm2
         |> REWRITE_RULE [pEqThm]
         |> CONV_RULE $ RATOR_CONV $ RATOR_CONV $ RAND_CONV EVAL,
          pEqThm)
      end
    else if realSyntax.is_mult t then
      let
        val (t1, t2) = realSyntax.dest_mult t
        val (thm1, p1) = reflect t1 x
        val (thm2, p2) = reflect t2 x
        val pEqThm = EVAL o Parse.Term $ ‘^(p1 |> concl |> rhs) *p ^(p2 |> concl |> rhs)’
      in
        (MATCH_MP (MATCH_MP polyEvalsTo_Mul thm1) thm2
         |> REWRITE_RULE [pEqThm]
         |> CONV_RULE $ RATOR_CONV $ RATOR_CONV $ RAND_CONV EVAL,
          pEqThm)
      end
    else if realSyntax.is_negated t then
      let
        val t1 = realSyntax.dest_negated t
        val (thm1, p1) = reflect t1 x
        val pEqThm = EVAL o Parse.Term $ ‘--p ^(p1 |> concl |> rhs)’
      in
        (MATCH_MP polyEvalsTo_Neg thm1
         |> REWRITE_RULE [pEqThm]
         |> CONV_RULE $ RATOR_CONV $ RATOR_CONV $ RAND_CONV EVAL,
          pEqThm)
      end
    else raise ZeroLibErr "Unsupported term";

  fun findOrErr (P:'a -> bool) (xs:'a list):'a =
    case List.find P xs of
      NONE => raise ZeroLibErr "No element found"
    | SOME a => a

  fun destCert (record:term):(term * term * term * term) =
    let val (comps:(string * term) list) = snd $ TypeBase.dest_record record
    in
      (snd $ findOrErr (fn (x,y) => x = "transc") comps,
       snd $ findOrErr (fn (x,y) => x = "poly") comps,
       snd $ findOrErr (fn (x,y) => x = "eps") comps,
       snd $ findOrErr (fn (x,y) => x = "iv") comps)
    end

  fun testSollya() =
  let
    val sollyaInput =
      "oldDisplay=display;" @^
      "display = powers!;  //putting ! after a command supresses its output" @^
      (* "diam = 1b-100!;" @^ *)
      "p = x * 1’;" @^
      "zeros = findzeros(p, [0;10]);" @^
      "print (\" DONE \");"
    val fileStr = TextIO.openOut ("/tmp/sollya_input.sollya")
    val _ = (TextIO.output (fileStr, sollyaInput); TextIO.closeOut fileStr)
    val _ = print "Testing sollya\n"
    val sollyaPath = OS.FileSys.getDir() ^ "/sollya/sollya-8.0/sollya"
    (* val sollyaPath =
        case Process.getEnv "SOLLYADIR" of
        SOME p => p ^ "/sollya"
        | NONE =>
          (let val (instr, outstr) = Unix.streamsOf(Unix.execute("/usr/bin/which", ["sollya"]))
          in TextIO.inputAll(instr) |> explode |> List.rev |> tl |> List.rev |> implode end)
          handle SysErr _ => (print "Could not get path for Sollya\n"; ""); *)
    val (instr, outStr) =
        (Unix.streamsOf(Unix.execute(sollyaPath, ["--warnonstderr", "/tmp/sollya_input.sollya"])))
        handle SysErr _ => (print ("Could not run Sollya at "^sollyaPath ^ "\n"); raise ZeroLibErr "")
    val res = TextIO.inputAll(instr);
  in
    print res
  end;

  fun cst2BinString (t:term) =
    if realSyntax.is_div t then (* Term is a fractional constant *)
      let
        val (nom, denom) = realSyntax.dest_div t
        val nomI = appOrErr realSyntax.is_real_literal realSyntax.int_of_term nom "Invalid constant"
        val denomI = appOrErr realSyntax.is_real_literal realSyntax.int_of_term denom "Invalid constant"
      in
        arbint2String nomI ^ "/" ^ arbint2String denomI
      end
    else (arbint2String (appOrErr realSyntax.is_real_literal realSyntax.int_of_term t "Invalid constant")) ^ "/" ^ "1"

  fun poly2BinString (t:term) =
    if not (listSyntax.is_list t) then
      raise ZeroLibErr "Translation error"
    else
      let val (tms, _) = listSyntax.dest_list t in
        "POLY" ^ (List.foldl (fn (t,s) => s ^ " " ^ cst2BinString t) "" tms)
      end;

  fun zeros2BinString (t:term) =
    if not (listSyntax.is_list t) then
      raise ZeroLibErr "Translation error"
    else
      let val (tms, _) = listSyntax.dest_list t in
        "ZEROS" ^ (List.foldl
                    (fn (t,s) =>
                      let val (lb,ub) = pairSyntax.dest_pair t in
                        s ^ " " ^ cst2BinString lb ^ " " ^ cst2BinString ub end) "" tms)
      end;

  val approxCfg = Parse.Term ‘<| steps := 16 |> ’;

  fun writeMetiTarskiQuery transc poly eps iv_lo iv_hi var = let
    val polyAsString = Parse.Term ‘evalPoly ^poly X’
                     |> EVAL
                     |> SIMP_RULE std_ss [REAL_LDISTRIB, REAL_MUL_LZERO,
                                          REAL_MUL_RZERO, REAL_ADD_LID,
                                          REAL_MUL_ASSOC, REAL_ADD_RID,
                                          pow_simp]
                     |> rhs o concl
                     |> poly2String
    val transcAsReal = Parse.Term ‘interp ^transc [^var, X]’
                        |> EVAL
    val transcAsString = term_to_string (optionSyntax.dest_some (transcAsReal |> rhs o concl))
                         |> String.translate (fn x => if x = #"X" then "(X)" else implode [x])
    val eps_eval = ((REWRITE_CONV [REAL_INV_1OVER] eps) handle UNCHANGED => REFL eps) |> rhs o concl
                  |> (fn t => (EVAL t handle UNCHANGED => REFL t))|> rhs o concl
    val polyDiffString1 = "(" ^ transcAsString ^ " - (" ^ polyAsString ^ ")" ^ ")"
    val polyDiffString2 = "((" ^ polyAsString ^ ") - " ^ transcAsString ^ ")"
    val text =
      "fof(" ^ Theory.current_theory() ^ ", conjecture, ! [X] :((" ^
      "X : (= "^ cst2String iv_lo ^ ","^cst2String iv_hi^"=)) => (\n"^
      "(" ^ polyDiffString1 ^ " <= " ^ cst2String eps_eval ^ ") &\n\n" ^
      "(" ^ polyDiffString2 ^ " <= " ^ cst2String eps_eval ^ "))))."
    val fileStr = TextIO.openOut ("./" ^ Theory.current_theory() ^ ".tptp")
    in
      (TextIO.output (fileStr, text); TextIO.closeOut fileStr)
    end;

  fun writeCoqIntervalQuery transc poly eps iv_lo iv_hi var = let
    val polyAsString = Parse.Term ‘evalPoly ^poly x’
                     |> EVAL
                     |> SIMP_RULE std_ss [REAL_LDISTRIB, REAL_MUL_LZERO,
                                          REAL_MUL_RZERO, REAL_ADD_LID,
                                          REAL_MUL_ASSOC, REAL_ADD_RID]
                     |> rhs o concl
                     |> term_to_string
    val transcAsReal = Parse.Term ‘interp ^transc [^var, x]’
                        |> EVAL
    val transcAsString = term_to_string (optionSyntax.dest_some (transcAsReal |> rhs o concl))
                         |> String.translate (fn x => if x = #"x" then "(x)" else implode [x])
    val eps_eval = ((REWRITE_CONV [REAL_INV_1OVER] eps) handle UNCHANGED => REFL eps) |> rhs o concl
                  |> (fn t => (EVAL t handle UNCHANGED => REFL t))|> rhs o concl
    val text =
      "Require Import Interval.Tactic.\n"^
      "Require Import Reals.\n\n"^
      "Goal\n"^
      "forall (x:R),(("^ (cst2String iv_lo) ^ " <= x <= " ^ (cst2String iv_hi) ^
      ") ->\n" ^
      "Rabs (" ^ transcAsString ^ " - (" ^ polyAsString ^ "))\n\t<=\n\t" ^
      (cst2String eps_eval) ^ ")%R.\n"^
      "Proof.\nintros.\ntime interval with (i_bisect x, i_taylor x).\nQed."
    val fileStr = TextIO.openOut ("./" ^ Theory.current_theory() ^ ".v")
    in
      (TextIO.output (fileStr, text); TextIO.closeOut fileStr)
    end;

  fun validateCert (defTh:thm) numApprox =
  let
    fun eval t = Parse.Term t |> EVAL
    fun getSome diag t = if optionSyntax.is_some t then optionSyntax.dest_some t else raise ZeroLibErr diag
    (* extract components from certificate *)
    val (transc, poly, eps, iv) = destCert (defTh |> concl |> rhs)
    val ivTm = eval ‘if (LENGTH ^iv = 1) then SOME (SND (HD ^iv)) else NONE’
      |> rhs o concl |> getSome "Could not extract interval"
    val var = eval ‘if (LENGTH ^iv = 1) then SOME (FST (HD ^iv)) else NONE’
      |> rhs o concl |> getSome "Could not extract variable"
    val iv_FST = EVAL “FST ^ivTm”
    val iv_SND = EVAL “SND ^ivTm”
    val _ = if (!createMetiTarskiQuery) then writeMetiTarskiQuery transc poly eps (iv_FST |> rhs o concl) (iv_SND |> rhs o concl) var else ()
    val _ = if (!createCoqIntervalQuery) then writeCoqIntervalQuery transc poly eps (iv_FST |> rhs o concl) (iv_SND |> rhs o concl) var else ()
    val approxSideThm = eval ‘approxPolySideCond ^numApprox’ |> SIMP_RULE std_ss [EQ_CLAUSES]
    val ivAnnotThm = eval ‘interpIntv ^transc ^iv’
    val ivAnnotTm = ivAnnotThm  |> rhs o concl |> getSome "Could not compute interval bounds"
    val ivSoundThm = MATCH_MP interpIntv_sound ivAnnotThm
    (*val sqrtReplPassThm = eval ‘sqrtReplace ^ivAnnotTm’
    val sqrtReplPassTm = sqrtReplPassThm |> rhs o concl |> getSome "Sqrt replacement pass failed"
    val ivAnnotSqrtReplThm = eval ‘interpIntv ^sqrtReplPassTm ^iv’
    val ivAnnotSqrtReplTm = ivAnnotThm  |> rhs o concl |> getSome "Could not compute interval bounds"
    val ivSoundSqrtReplThm = MATCH_MP interpIntv_sound ivAnnotThm *)
    val approxThm = eval ‘approxTransc (^approxCfg with steps := ^numApprox) ^ivAnnotTm’
    val approxTm = approxThm |> rhs o concl |> getSome "Could not compute high-accuracy approximations"
    val length1Thm = eval ‘LENGTH ^iv = 1’ |> REWRITE_RULE [EQ_CLAUSES]
    val approxSoundThm =
      MATCH_MP
        (MATCH_MP
          (MATCH_MP
            (REWRITE_RULE [GSYM AND_IMP_INTRO] approxTransc_sound_single)
            length1Thm)
          ivSoundThm)
        approxThm
      |> SIMP_RULE std_ss [erase_def, getAnn_def]
    val transpThm = eval ‘reflectToPoly (erase (^approxTm)) ^var’
    val transpTm = transpThm |> rhs o concl |> getSome "Could not reflect into a polynomial"
    val reflectOkThm = MATCH_MP reflectSemEquiv transpThm |> REWRITE_RULE [erase_def]
    val varEqThm = EVAL “FST (HD ^iv)”
    val ivEqThm = EVAL “SND (HD ^iv)”
    val approxSoundPolyThm = REWRITE_RULE [varEqThm, ivEqThm, reflectOkThm, optionGet_SOME, AND_IMP_INTRO] approxSoundThm
    (** Get rid of sqrtReplace pass result in conclusion **)
    (* val ivSoundSingleThm = MATCH_MP validIVAnnot_single ivSoundThm
    (* First build a "concrete environment" *)
    val cenv = ‘[^(varEqThm |> rhs o concl), x:real]’
    val evalOrigThm = ivSoundSingleThm |> Q.SPEC cenv |> CONV_RULE $ RATOR_CONV $ RAND_CONV $ RAND_CONV EVAL |> UNDISCH
    val evalSqrtReplPassThm =
      MATCH_MP
        (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] sqrtReplace_sound) sqrtReplPassThm)
        ivSoundThm  |> SIMP_RULE std_ss[AND_IMP_INTRO] |> ONCE_REWRITE_RULE [CONJ_COMM]
      |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> SPEC_ALL |> GEN “cenv:(string#real)list” |> Q.SPEC cenv
      |> UNDISCH *)
    val transpGetThm = Q.ISPEC ‘^(transpThm |> lhs o concl)’ optionGet_def
                     |> SIMP_RULE std_ss [SimpR “$=”, transpThm]
    val err = Parse.Term ‘getAnn ^approxTm’ |> EVAL |> concl |> rhs
    val errorpThm = Parse.Term ‘^transpTm -p ^poly’ |> EVAL
    val errorp = errorpThm |> rhs o concl
  in
    if !useBinary then
      let val polyString = poly2BinString errorp
        val errString = "ERR " ^ cst2BinString (EVAL “^eps - ^err” |> rhs o concl)
        val lb = EVAL “FST ^ivTm” |> rhs o concl
        val ub = EVAL “SND ^ivTm” |> rhs o concl
        val IVstring = "IV " ^ cst2BinString lb ^ " " ^ cst2BinString ub
        val zerosTm = Parse.Term [QUOTE (getZerosFromSollya (EVAL “diff ^errorp” |> rhs o concl) “x:real” lb ub)] |> EVAL |> rhs o concl
        val zeros = zeros2BinString zerosTm
        val inp = polyString ^ "\n" ^ errString ^ "\n" ^ IVstring ^ "\n" ^ zeros
        (** FIXME: Absolute path **)
        val fileStr = TextIO.openOut ("./" ^ Theory.current_theory() ^ ".txt")
        val _ = (TextIO.output (fileStr, inp); TextIO.closeOut fileStr)
      in
        approxSoundPolyThm
      end
    else let
      val polyErrThm =
        (testSollya();
         REAL_ZERO_CONV (Parse.Term ‘! x. FST (^ivTm) <= x /\ x <= SND (^ivTm) ==> abs (evalPoly ^errorp x) <= ^eps - ^err’))
      val polyErrThm_simped = REWRITE_RULE [GSYM errorpThm, eval_simps,
                                            GSYM poly_compat, Once $ GSYM transpGetThm,
                                            Once $ GSYM iv_FST, transpThm, optionGet_SOME] polyErrThm
      val final_thm = MATCH_MP (MATCH_MP REAL_ABS_TRIANGLE_PRE approxSoundPolyThm) polyErrThm_simped
    in
      (save_thm ("err_sound_thm", final_thm); final_thm)
    end end;

  fun REAL_INEQ_CONV (t:term) = let
    val (var, tm) = appOrErr is_forall dest_forall t "Not a universally quantified statement"
    val (pre, conc) = appOrErr is_imp dest_imp tm "Input term not of the form ! x. _ ==> _"
    val (ltm, rtm) = appOrErr realSyntax.is_leq realSyntax.dest_leq conc "Conclusion not a <= expression"
    in
    if not (type_of var = “:real”) then raise ZeroLibErr "Only real number expressions are supported"
    else let
      val isAbs = realSyntax.is_absval ltm
      val argTm = if isAbs then rand ltm else ltm
      val (evalThm, _) = reflect (Parse.Term ‘^argTm :real’) var
      val evalRwThm = evalThm |> REWRITE_RULE [polyEvalsTo_def, poly_compat]
      val theTerm = if isAbs then t else “∀ ^(var). ^pre ⇒ abs ^argTm ≤ ^rtm”
    in
      (REAL_ZERO_CONV (REWRITE_CONV [GSYM evalRwThm ] theTerm |> rhs o concl)
        |> SPEC var
        |> REWRITE_RULE [evalRwThm]
        |> GEN_ALL, isAbs, ltm)
    end end;

  fun REAL_INEQ_TAC (asl, g) = let
    val (ineqThm, isAbs, ltm) = REAL_INEQ_CONV g in
    if isAbs then (MATCH_ACCEPT_TAC ineqThm ORELSE realLib.REAL_ARITH_TAC) (asl,g)
    else ((assume_tac ineqThm
          >> rpt strip_tac >> irule REAL_LE_TRANS >> qexists_tac ‘abs ^ltm’ >> conj_tac >> gs[ABS_LE])
      ORELSE realLib.REAL_ARITH_TAC) (asl, g)
    end;

end;
  (** Some tests **)
(**
  reflect “x * x - 3 * x - 10:real” “x:real”
  (* reflect “~ ((x + 1/2):real) * x” “x:real” *)
  (* val t = REAL_ZERO_CONV “! x. 90 <= x /\ x <= 100 ==> evalPoly [1; 2/100; 3] x <= 100:real” *)
  **)
