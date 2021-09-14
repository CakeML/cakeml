(*
  Definition of a PEG for (a subset of) OCaml.
 *)

open preamble caml_lexTheory;
open pegexecTheory pegTheory;
open finite_mapSyntax;

val _ = new_theory "camlPEG";

val _ = enable_monadsyntax ();

val _ = enable_monad "option";

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

(* have to use these versions of choicel and pegf below because the
   "built-in" versions from HOL/examples/ use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   translator
*)

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
      ((validCoreOpChar c ∨ c = #"%" ∨ c = #"<") ∨
       (c = #"#" ∧ cs ≠ "")) ∧
      EVERY validOpChar cs
End

Definition validMultOp_def:
  validMultOp s =
    case s of
      [] => F
    | c::cs =>
        (MEM c "*%/" ∧ EVERY validOpChar cs) ∨
        MEM s [ "mod"; "land"; "lor"; "lxor" ]
End

Definition validAddOp_def:
  validAddOp s =
    case s of
      [] => F
    | c::cs => MEM c "+-" ∧ EVERY validOpChar cs
End

Datatype:
  camlNT
    = nELiteral
    | nEBase
    | nEMult
    | nEAdd
    | nEPrefix
    | nExpr
    | nEMultOp
End

(*
 * TODO
 * - Fix operator parsing (e.g. a * b / c doesnt work; see comment below)
 * - Add remaining non-terminals to datatype and
 *   implement remaining rules
 *)

Definition camlPEG_def[nocompute]:
  camlPEG = <|
    start := ARB;
    rules := FEMPTY |++ [
      (* nELiteral ::= <integer-literal>
       *             / <char-literal>
       *             / <string-literal>
       *)
      (INL nELiteral,
       choicel [
           tok isInt    (bindNT nELiteral o mktokLf);
           tok isString (bindNT nELiteral o mktokLf);
           tok isChar   (bindNT nELiteral o mktokLf)
         ]);
      (* nEBase ::= nELiteral
       *          / <LPAR> ; nE ; [RPAR]
       *)
      (INL nEBase,
       choicel [
           pegf (pnt nELiteral) (bindNT nEBase);
           seql [ tokeq LparT; pnt nExpr; tokeq RparT ] (bindNT nEBase)
        ]);
      (* nEPrefix ::= <prefix-symbol> ; nEBase
       *            / nEBase
       * FIXME prefix symbols
       *)
      (INL nEPrefix,
       choicel [
          seql [ tokSymP validPrefixSym; pnt nEBase ] (bindNT nEPrefix);
          pegf (pnt nEBase) (bindNT nEPrefix)
        ]);
      (* nMultOp ::= StarT
       *           / <validMultOp>
       *)
      (INL nEMultOp,
       choicel [
         pegf (tokeq StarT) (bindNT nEMultOp);
         pegf (tokSymP validMultOp) (bindNT nEMultOp)
       ]);
      (* nEMult ::= nEPrefix ; nMultOp ; nEPrefix
       *          / nEPrefix
       * FIXME
       *)
      (INL nEMult,
       choicel [
           seql [ pnt nEPrefix; pnt nEMultOp; pnt nEPrefix ] (bindNT nEMult);
           pegf (pnt nEPrefix) (bindNT nEMult)
        ]);
      (* nEAdd ::= nEMult ; <add-ops> ; nEMult
       *         / nEMult
       * FIXME
       *)
      (INL nEAdd,
       choicel [
           seql [ pnt nEMult; tokSymP validAddOp; pnt nEMult ]
                (bindNT nEAdd);
           pegf (pnt nEMult) (bindNT nEAdd)
        ]);
      (* nExpr ::= nEAdd
       *)
      (INL nExpr,
       pegf (pnt nEAdd) (bindNT nExpr))
      ] |>
End

(* All of this stuff is taken from cmlPEGScript. Its for doing EVAL
 * using peg_exec.
 *)

val rules_t = “camlPEG.rules”;
fun ty2frag ty = let
  open simpLib
  val {convs,rewrs} = TypeBase.simpls_of ty
in
  merge_ss (rewrites rewrs :: map conv_ss convs)
end

(* can't use srw_ss() as it will attack the bodies of the rules,
   and in particular, will destroy predicates from tok
   constructors of the form
        do ... od = SOME ()
   which matches optionTheory.OPTION_BIND_EQUALS_OPTION, putting
   an existential into our rewrite thereby *)
val rules = SIMP_CONV (bool_ss ++ ty2frag ``:(α,β,γ)peg``)
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

(*
time EVAL “peg_exec camlPEG (pnt nExpr)
           (map_loc [
                IntT 3; StarT; IntT 4; SymbolT "/"; IntT (-2);
            ] 0)
           []
           done
           failed”;
 *)


val _ = export_theory ();

