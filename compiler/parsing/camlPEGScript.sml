(*
  Definition of a PEG for (a subset of) OCaml.
 *)

open preamble caml_lexTheory;
open pegexecTheory pegTheory;
open finite_mapSyntax;

val _ = new_theory "camlPEG";

val _ = enable_monadsyntax ();

val _ = enable_monad "option";

(* Some definitions taken from cmlPEG:
 *)

Definition sumID_def:
  sumID (INL x) = x ∧
  sumID (INR y) = y
End

Definition mktokLf_def:
  mktokLf t = [Lf (TOK (FST t), SND t)]
End

Definition mkNd_def:
  mkNd ntnm l = Nd (ntnm, ptree_list_loc l) l
End

Definition bindNT0_def:
  bindNT0 ntnm l = Nd (INL ntnm, ptree_list_loc l) l
End

Definition bindNT_def:
  bindNT ntnm l = [bindNT0 ntnm l]
End

Definition mk_linfix_def:
  mk_linfix tgt acc [] = acc ∧
  mk_linfix tgt acc [t] = acc ∧
  mk_linfix tgt acc (opt::t::rest) =
    mk_linfix tgt (mkNd tgt [acc; opt; t]) rest
End

Definition mk_rinfix_def:
  mk_rinfix tgt [] = mkNd tgt [] ∧
  mk_rinfix tgt [t] = mkNd tgt [t] ∧
  mk_rinfix tgt (t::opt::rest) = mkNd tgt [t; opt; mk_rinfix tgt rest]
End

Definition peg_linfix_def:
  peg_linfix tgtnt rptsym opsym =
    seq rptsym (rpt (seq opsym rptsym (++)) FLAT)
        (λa b. case a of
                   [] => []
                  | h::_ => [mk_linfix tgtnt (mkNd tgtnt [h]) b])
End

Definition choicel_def:
  choicel [] = not (empty []) [] ∧
  choicel (h::t) = choice h (choicel t) sumID
End

Definition pegf_def:
  pegf sym f = seq sym (empty []) (λl1 l2. f l1)
End

Definition seql_def:
  seql l f = pegf (FOLDR (\p acc. seq p acc (++)) (empty []) l) f
End

Definition try_def:
  try sym = choicel [sym; empty []]
End

Definition tokeq_def:
  tokeq t = tok ((=) t) mktokLf
End

Definition tokSymP_def:
  tokSymP P =
    tok (λt. (do s <- destSymbol t; assert (P s) od) = SOME ()) mktokLf
End

Definition tokIdP_def:
  tokIdP P =
    tok (λt. (do s <- destIdent t; assert (P s) od) = SOME ()) mktokLf
End

Definition pnt_def:
  pnt ntsym = nt (INL ntsym) I
End

(* -------------------------------------------------------------------------
 * Non-terminals
 * ------------------------------------------------------------------------- *)

Definition validCoreOpChar_def:
  validCoreOpChar c = MEM c "$&*+-/=>@^|"
End

Definition validOpChar_def:
  validOpChar c ⇔ MEM c "!?%<:." ∨ validCoreOpChar c
End

Definition validPrefixSym_def:
  validPrefixSym s =
    case s of
      [] => F
    | c::cs =>
        (c = #"!" ∨ (c = #"?" ∨ c = #"~" ∧ cs ≠ "")) ∧
        EVERY validOpChar cs
End

Definition validInfixSym_def:
  validInfixSym s =
    case s of
      [] => F
    | c::cs =>
      ((validCoreOpChar c ∨ c = #"%" ∨ c = #"<") ∨
       (c = #"#" ∧ cs ≠ "")) ∧
      EVERY validOpChar cs
End

Definition validMultOp_def:
  validMultOp s =
    case s of
      [] => F
    | c::cs =>
        (MEM c "*%/" ∧ cs ≠ "" ∧ EVERY validOpChar cs) ∨
        MEM s [ "%"; "/"; "mod"; "land"; "lor"; "lxor" ]
End

Definition validRelOp_def:
  validRelOp s =
    case s of
      [] => F
    | c::cs =>
        MEM c "<>|&$" ∧ cs ≠ "" ∧ EVERY validOpChar cs
End

Definition validAddOp_def:
  validAddOp s =
    case s of
      [] => F
    | c::cs => MEM c "+-" ∧ cs ≠ "" ∧ EVERY validOpChar cs
End

Definition validRelOp_def:
  validRelOp s =
    case s of
      [] => F
    | c::cs => MEM c "=<>|&$" ∧ cs ≠ "" ∧ EVERY validOpChar cs
End

Definition validShiftOp_def:
  validShiftOp s =
    case s of
      c::d::cs => c = #"*" ∧ d = #"*" ∧ EVERY validOpChar cs
    | _ => F
End

Definition validCatOp_def:
  validCatOp s =
    case s of
      [] => F
    | c::cs => (c = #"@" ∨ c = CHR 94) ∧ EVERY validOpChar cs
End

Definition validConsId_def:
  validConsId s =
    case s of
      [] => F
    | c::cs => isUpper c ∧
               EVERY (λc. isLower c ∨ c = #"_" ∨ c = #"'" ∨ isDigit c) cs
End

Definition validFunId_def:
  validFunId s =
    case s of
      [] => F
    | c::cs =>
        isLower c ∧ EVERY (λc. isLower c ∨ c = #"_" ∨ c = #"'" ∨ isDigit c) cs
End

Datatype:
  camlNT
    = nLiteral
    | nIdent
    | nEBase
    (* in order of presedence, highest to lowest: *)
    | nEApp
    | nEConstr
    | nEFunapp
    | nETagapp
    | nEPrefix
    | nENeg
    | nEShift
    | nEMult
    | nEAdd
    | nECons
    | nECat
    | nERel
    | nEAnd
    | nEOr
    | nEIf
    | nEWhile
    | nEFor
    | nExpr
    (* various modifiers *)
    | nEAssert
    | nELazy
    (* misc *)
    | nShiftOp
    | nMultOp
    | nAddOp
    | nRelOp
    | nAndOp
    | nOrOp
    | nStart
End

(*
 * TODO
 * - commas
 * - assignments <- :=
 * - semicolon ; (sequencing)
 * - let match fun function try
 *
 * - patterns
 * - type expressions
 * - top-level double-semicolon-separated expressions foo ;; bar;; baz
 *
 * - somehow I forgot to allow identifiers to contain dots
 *   (i.e. module paths); this needs to be fixed also in the
 *   lexer
 *)

Definition camlPEG_def[nocompute]:
  camlPEG = <|
    anyEOF   := "Unexpected end-of-file";
    tokFALSE := "Unexpected token";
    tokEOF   := "Expected token, found end-of-file";
    notFAIL  := "Not combinator failed";
    start := pnt nStart;
    rules := FEMPTY |++ [
      (* --------------------------- Expressions --------------------------- *)
      (INL nLiteral,
       choicel [
         tok isInt    (bindNT nLiteral o mktokLf);
         tok isString (bindNT nLiteral o mktokLf);
         tok isChar   (bindNT nLiteral o mktokLf)
       ]);
      (INL nIdent,
       tok isIdent (bindNT nIdent o mktokLf));
      (INL nEBase,
       choicel [
         pegf (pnt nLiteral) (bindNT nEBase);
         pegf (pnt nIdent) (bindNT nEBase);
         seql [tokeq LparT; pnt nExpr; tokeq RparT] (bindNT nEBase)
       ]);
      (INL nEAssert,
       seql [tokeq AssertT; pnt nEBase] (bindNT nEAssert));
      (INL nELazy,
       seql [tokeq LazyT; pnt nEBase] (bindNT nELazy));
      (INL nEConstr,
       seql [tokIdP validConsId; pnt nEBase] (bindNT nEConstr));
      (INL nEFunapp,
       seql [tokIdP validFunId; pnt nEBase] (bindNT nEFunapp));
      (INL nETagapp,
       seql [tokeq BtickT; tokIdP validFunId; pnt nEBase]
            (bindNT nETagapp));
      (INL nEApp,
       pegf (choicel (MAP pnt [nELazy; nEAssert; nEConstr; nEFunapp;
                               nETagapp; nEBase]))
            (bindNT nEApp));
      (INL nEPrefix, (* FIXME try? *)
       choicel [
         seql [tokSymP validPrefixSym; pnt nEApp] (bindNT nEPrefix);
         pegf (pnt nEApp) (bindNT nEPrefix)
       ]);
      (INL nENeg, (* FIXME try? *)
       choicel [
         seql [choicel [tokeq MinusT; tokeq MinusFT]; pnt nEPrefix]
              (bindNT nENeg);
         pegf (pnt nEPrefix) (bindNT nENeg)]);
      (INL nMultOp,
       pegf (choicel [tokeq StarT; tokSymP validMultOp])
            (bindNT nMultOp));
      (INL nAddOp,
       pegf (choicel [tokeq PlusT; tokeq MinusT; tokSymP validAddOp])
            (bindNT nAddOp));
      (INL nRelOp,
       pegf (choicel [tokeq EqualT;
                      tokeq LessT;
                      tokeq GreaterT;
                      tokeq NeqT;
                      tokSymP validRelOp])
            (bindNT nRelOp));
      (INL nAndOp,
       pegf (choicel [tokeq AmpT; tokeq AndalsoT])
            (bindNT nAndOp));
      (INL nOrOp,
       pegf (choicel [tokeq OrelseT; tokeq OrT])
            (bindNT nOrOp));
      (INL nShiftOp,
       pegf (choicel [tokSymP validShiftOp;
                      tokeq LslT;
                      tokeq LsrT;
                      tokeq AsrT])
            (bindNT nShiftOp));
      (INL nEShift, (* TODO r-assoc *)
       choicel [
         seql [pnt nENeg; pnt nShiftOp; pnt nEShift] (bindNT nEShift);
         pegf (pnt nENeg) (bindNT nEShift)]);
      (INL nEMult,
       peg_linfix (INL nEMult) (pnt nEShift) (pnt nMultOp));
      (INL nEAdd,
       peg_linfix (INL nEAdd) (pnt nEMult) (pnt nAddOp));
      (INL nECons, (* TODO r-assoc, try? *)
       choicel [
         seql [ pnt nEAdd; tokeq ColonsT; pnt nECons ]
              (bindNT nECons);
         pegf (pnt nEAdd) (bindNT nECons)]);
      (INL nECat, (* TODO r-assoc, try? *)
       choicel [
         seql [pnt nECons; tokSymP validCatOp; pnt nECat]
              (bindNT nECat);
         pegf (pnt nECons) (bindNT nECat)]);
      (INL nERel,
       peg_linfix (INL nERel) (pnt nECat) (pnt nRelOp));
      (INL nEAnd, (* TODO r-assoc, try? *)
       choicel [
         seql [pnt nERel; pnt nAndOp; pnt nEAnd]
              (bindNT nEAnd);
         pegf (pnt nERel) (bindNT nEAnd)
       ]);
      (INL nEOr, (* TODO r-assoc, try? *)
       choicel [
         seql [pnt nEAnd; pnt nOrOp; pnt nEOr]
              (bindNT nEOr);
         pegf (pnt nEAnd) (bindNT nEOr)
       ]);
      (* ------------------------ Control exprs. --------------------------- *)
      (INL nEIf,
       choicel [
         seql [tokeq IfT; pnt nExpr;
               tokeq ThenT; pnt nExpr;
               tokeq ElseT; pnt nExpr]
              (bindNT nEIf);
         seql [tokeq IfT; pnt nExpr;
               tokeq ThenT; pnt nExpr]
              (bindNT nEIf)]);
      (INL nEWhile,
       seql [tokeq WhileT; pnt nExpr; tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEWhile));
      (INL nEFor,
       seql [tokeq ForT; pnt nIdent; tokeq EqualT;
             choicel [tokeq ToT; tokeq DowntoT]; pnt nExpr;
             tokeq DoT; pnt nExpr; tokeq DoneT]
            (bindNT nEFor));
      (INL nExpr,
       pegf (pnt nEOr) (bindNT nExpr));
      (* --------------------------- Entrypoint ---------------------------- *)
      (INL nStart,
       seql [pnt nExpr; not (any (K [])) [] ] (bindNT nStart))
      ] |>
End

(* -------------------------------------------------------------------------
 * All of the stuff below is taken from cmlPEGScript. Its for doing EVAL
 * using peg_exec:
 * ------------------------------------------------------------------------- *)

val rules_t = “camlPEG.rules”;
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end

val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ,δ)peg``)
                      [camlPEG_def, combinTheory.K_DEF,
                       finite_mapTheory.FUPDATE_LIST_THM] rules_t

val _ = print "Calculating application of camlPEG rules\n"
val camlpeg_rules_applied = let
  val app0 = finite_mapSyntax.fapply_t
  val theta =
      Type.match_type (type_of app0 |> dom_rng |> #1) (type_of rules_t)
  val app = inst theta app0
  val app_rules = AP_TERM app rules
  val sset = bool_ss ++ ty2frag ``:'a + 'b`` ++ ty2frag ``:token``
  fun mkrule t =
      AP_THM app_rules (sumSyntax.mk_inl (t, “:num”))
      |> SIMP_RULE sset [finite_mapTheory.FAPPLY_FUPDATE_THM]
  val ths = TypeBase.constructors_of ``:camlNT`` |> map mkrule
in
    save_thm("camlpeg_rules_applied", LIST_CONJ ths);
    ths
end

val FDOM_camlPEG = save_thm(
  "FDOM_camlPEG",
  SIMP_CONV (srw_ss()) [camlPEG_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM camlPEG.rules``);

val spec0 =
    peg_nt_thm |> Q.GEN `G`  |> Q.ISPEC `camlPEG`
               |> SIMP_RULE (srw_ss()) [FDOM_camlPEG]
               |> Q.GEN `n`

val distinct_ths = let
  val ntlist = TypeBase.constructors_of ``:camlNT``
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

Theorem camlPEG_exec_thm[compute] =
  TypeBase.constructors_of ``:camlNT``
    |> map (fn t => ISPEC (sumSyntax.mk_inl(t, “:num”)) spec0)
    |> map (SIMP_RULE bool_ss (camlpeg_rules_applied @ distinct_ths @
                               [sumTheory.INL_11]))
    |> LIST_CONJ;

val test =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; StarT; IntT 4; SymbolT "/"; IntT (-2);
              ] 0)
             [] NONE [] done failed”;

val test2 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; StarT; IntT 4;
              ] 0)
             [] NONE [] done failed”;

val test3 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; LessT; IdentT "foo";
              ] 0)
             [] NONE [] done failed”;

val test4 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IntT 3; ColonsT; IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test5 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  ColonsT; IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test6 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test7 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IdentT "x"; ColonsT;
                  IdentT "y"; ColonsT;
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test8 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  LparT;
                  IdentT "x"; ColonsT;
                  IdentT "y";
                  RparT;
                  ColonsT;
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

val test9 =
  time EVAL “peg_exec camlPEG (pnt nStart)
             (map_loc [
                  IdentT "y";
                  SymbolT "@<<";
                  IdentT "xs";
              ] 0)
             [] NONE [] done failed”;

(* -------------------------------------------------------------------------
 * Running the lexer, and then the parser
 * ------------------------------------------------------------------------- *)

Overload camlpegexec =
  “λn t. peg_exec camlPEG (pnt n) t [] NONE [] done failed”;

Definition destResult_def:
  destResult (Result (Success [] x eo)) = INR (x, eo) ∧
  destResult (Result (Success ((_,l)::_) _ _)) =
    INL (l, "Expected to be at EOF") ∧
  destResult (Result (Failure fl fe)) = INL (fl, fe) ∧
  destResult _ =
    INL (unknown_loc, "Something catastrophic happened")
End

Definition run_prog_def:
  run_prog input =
    let toks = lexer_fun input in
    let errs = FILTER ($= LexErrorT o FST) toks in
      if errs ≠ [] then
        INL (SND (HD errs), "Lexer error")
      else
        destResult (camlpegexec nStart toks)
End

val test1 = EVAL “run_prog " :: d ? 4"”
val test2 = EVAL “run_prog "1 + ? 4"”
val test3 = EVAL “run_prog "1 + 33 / (a_b_cdef :: 4)"”
val test4 = EVAL “run_prog "abcdef \\s"”;

val _ = export_theory ();

