open HolKernel Parse boolLib bossLib

open mmlGrammarTheory pegexecTheory

val _ = new_theory "mmlPEG"

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:MMLnonT``
  fun recurse [] = []
    | recurse (t::ts) = let
      val eqns = map (fn t' => mk_eq(t,t')) ts
      val ths0 = map (SIMP_CONV (srw_ss()) []) eqns
      val ths1 = map (CONV_RULE (LAND_CONV (REWR_CONV EQ_SYM_EQ))) ths0
    in
      ths0 @ ths1 @ recurse ts
    end
in
  recurse ntlist
end


val _ = computeLib.add_thms distinct_ths computeLib.the_compset

val isInt_def = Define`
  isInt (IntT i) = T ∧
  isInt _ = F
`;

val sumID_def = Define`
  sumID (INL x) = x ∧
  sumID (INR y) = y
`;

val mk_linfix_def = Define`
  mk_linfix tgt acc [] = acc ∧
  mk_linfix tgt acc (opt::t::rest) =
    mk_linfix tgt (Nd tgt [acc; opt; t]) rest
`;

val peg_linfix_def = Define`
  peg_linfix tgtnt rptnt opnt =
    seq (nt rptnt I) (rpt (seq (nt opnt I) (nt rptnt I) (++)) FLAT)
        (λa b. [mk_linfix tgtnt (Nd tgtnt [HD a]) b])
`;

val mktokLf_def = Define`mktokLf t = [Lf (TK t)]`

val peg_multops_def = Define`
  peg_multops = choice (tok ((=) (SymbolT "*")) mktokLf)
                       (tok ((=) (SymbolT "/")) mktokLf)
                       (λa. [Nd (mkNT nMultOps) [HD (sumID a)]])
`;

val peg_Ebase_def = Define`
  peg_Ebase = tok isInt (λt. [Nd (mkNT nEbase) [Lf (TK t)]])
`;

val peg_Eapp_def = Define`
  peg_Eapp = seq (nt (mkNT nEbase) I)
                 (rpt (nt (mkNT nEbase) I) FLAT)
                 (λa b. [FOLDL (λa b. Nd (mkNT nEapp) [a; b])
                               (Nd (mkNT nEapp) [HD a])
                               b])
`;

val mmlG_def = Define`
  mmlG = <|
    start := nt (mkNT nEmult) I;
    rules := FEMPTY |++
             [(mkNT nEmult, peg_linfix (mkNT nEmult) (mkNT nEapp)
                                       (mkNT nMultOps));
              (mkNT nEapp, peg_Eapp);
              (mkNT nMultOps, peg_multops);
              (mkNT nEbase, peg_Ebase)] |>
`;


val test1 = EVAL ``peg_exec mmlG (nt (mkNT nEmult) I) [IntT 3; SymbolT "*"; IntT 4; SymbolT "/"; IntT (-2)] [] done failed``


val _ = export_theory()
