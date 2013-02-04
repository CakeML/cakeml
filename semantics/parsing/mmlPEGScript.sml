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

val isAlphaT_def = Define`
  isAlphaT (AlphaT s) = T ∧
  isAlphaT _ = F
`;

val isSymbolT_def = Define`isSymbolT (SymbolT s) = T ∧ isSymbolT _ = F`
val isAlphaSym_def = Define`
  isAlphaSym (AlphaT _) = T ∧
  isAlphaSym (SymbolT _) = T ∧
  isAlphaSym _ = F
`;

val isTyvarT_def = Define`isTyvarT (TyvarT _) = T ∧ isTyvarT _ = F`

val sumID_def = Define`
  sumID (INL x) = x ∧
  sumID (INR y) = y
`;

val mk_linfix_def = Define`
  mk_linfix tgt acc [] = acc ∧
  mk_linfix tgt acc (opt::t::rest) =
    mk_linfix tgt (Nd tgt [acc; opt; t]) rest
`;

val mk_rinfix_def = Define`
  mk_rinfix tgt [t] = Nd tgt [t] ∧
  mk_rinfix tgt (t::opt::rest) = Nd tgt [t; opt; mk_rinfix tgt rest]`;

val peg_linfix_def = Define`
  peg_linfix tgtnt rptnt opnt =
    seq (nt rptnt I) (rpt (seq (nt opnt I) (nt rptnt I) (++)) FLAT)
        (λa b. [mk_linfix tgtnt (Nd tgtnt [HD a]) b])
`;

val mktokLf_def = Define`mktokLf t = [Lf (TK t)]`

(* ----------------------------------------------------------------------
    PEG for types
   ---------------------------------------------------------------------- *)

val peg_Type_def = Define`
  peg_Type = seq (nt (mkNT nDType) I)
                 (choice (seq (tok ((=) ArrowT) mktokLf)
                              (nt (mkNT nType) I)
                              (++))
                         (empty [])
                         sumID)
                 (λa b. case b of
                          [] => [Nd (mkNT nType) a]
                        | _ => [Nd (mkNT nType) [HD a; HD b; HD (TL b)]])
`;

val peg_TyOp_def = Define`
  peg_TyOp = tok isAlphaSym (λt. [Nd (mkNT nTyOp) [Lf (TK t)]])`

val splitAt_def = Define`
  splitAt x [] = ([], []) ∧
  splitAt x (h::t) = if x = h then ([], h::t)
                     else let (pfx,s) = splitAt x t
                          in
                            (h::pfx,s)
`

val calcTyOp_def = Define`
  calcTyOp a b =
    case b of
      [Lf (TK RparT)] => [Nd (mkNT nDType) [Lf (TK LparT); HD a; HD b]]
    | Lf (TK RparT)::ops => FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                                  [Lf (TK LparT); Nd (mkNT nTypeList) a; HD b]
                                  ops
    | _ => let (tylist, paren_ops) = splitAt (Lf (TK RparT)) b
           in
             let tylist_n = mk_rinfix (mkNT nTypeList) (HD a :: tylist)
             in
               FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                     [Lf (TK LparT); tylist_n; Lf (TK RparT)]
                     (TL paren_ops)
`;

val peg_DType_def = Define`
  (* TyvarT | TyOp | "(" Type ( ")" TyOp* | ("," Type)* ")" TyOp TyOp* ) *)
  peg_DType =
    choice
      (seq (tok isTyvarT (λx. [Nd (mkNT nDType) (mktokLf x)]))
           (rpt (nt (mkNT nTyOp) I) FLAT)
           (λa ops. FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                          a ops))
      (choice
        (seq (nt (mkNT nTyOp) (λx. [Nd (mkNT nDType) x]))
             (rpt (nt (mkNT nTyOp) I) FLAT)
             (λa ops. FOLDL (λacc opn. [Nd (mkNT nDType) (acc ++ [opn])])
                            a ops))
        (seq (tok ((=) LparT) mktokLf)
             (seq (nt (mkNT nType) I)
                  (choice
                     (* ")" TyOp* *)
                     (seq (tok ((=) RparT) mktokLf)
                          (rpt (nt (mkNT nTyOp) I) FLAT)
                          (++))
                     (* ("," Type)* ")" TyOp TyOp* *)
                     (seq (rpt (seq (tok ((=) CommaT) mktokLf)
                                    (nt (mkNT nType) I)
                                    (++))
                               FLAT)
                          (seq (tok ((=) RparT) mktokLf)
                               (seq (nt (mkNT nTyOp) I)
                                    (rpt (nt (mkNT nTyOp) I) FLAT)
                                    (++))
                               (++))
                          (++))
                     sumID)
                  calcTyOp)
             (λa b. b))
        sumID)
      sumID
`;


val mmltyPEG_def = Define`
  mmltyPEG = <| start := nt (mkNT nType) I;
                rules := FEMPTY |++ [(mkNT nType, peg_Type);
                                     (mkNT nDType, peg_DType);
                                     (mkNT nTyOp, peg_TyOp)] |>`;


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
