open HolKernel Parse boolLib bossLib

open mmlGrammarTheory
open lcsymtacs
open boolSimps
open monadsyntax

val _ = new_theory "mmlvalid"

val mmlvalid_def = zDefine`
  mmlvalid pt = valid_ptree mmlG pt
`

val mmlvalidL_def = Define`
  (mmlvalidL [] ⇔ T) ∧
  (mmlvalidL (h::t) ⇔ mmlvalid h ∧ mmlvalidL t)
`
val _ = export_rewrites ["mmlvalidL_def"]

val mmlvalidL_lemma = prove(
  ``mmlvalidL children ⇔ (∀pt. MEM pt children ⇒ valid_ptree mmlG pt)``,
  Induct_on `children` >> asm_simp_tac (srw_ss() ++ DNF_ss) [mmlvalid_def]);

val mml_okrule_def = Define`
  mml_okrule n l ⇔ (n, l) ∈ mmlG.rules
`

val mmlvalid_Nd =
  ``mmlvalid (Nd n l)``
    |> SIMP_CONV (srw_ss()) [mmlvalid_def, GSYM mml_okrule_def,
                             GSYM mmlvalidL_lemma]

(*
fun mk_arrow_t ty =
    mk_thy_const{Name = GrammarSpecials.case_arrow_special,
                 Ty = ty --> bool --> ty --> bool,
                 Thy = "bool"}

fun exists_to_case_arrow t = let
  val (vs, body) = strip_exists t
  val cs = strip_conj body
  val c = hd cs
  val rest = tl cs
  val pat = rhs c
in
  list_mk_comb(mk_arrow_t (type_of pat),
               [pat, if null rest then T else list_mk_conj rest])
end

fun disjs_to_case t = let
  val ds = strip_disj t
  val ts = map exists_to_case_arrow ds
  val ty  = type_of (hd ts)
  val bar = mk_thy_const{Name = GrammarSpecials.case_split_special,
                         Ty = ty --> ty --> ty, Thy = "bool"}
  val (patty, _) = dom_rng ty
  val real_cases =
      List.foldl (fn (t,acc) => list_mk_comb(bar, [acc,t])) (hd ts) (tl ts)
  val arrF_case = list_mk_comb(mk_arrow_t patty, [mk_var("_", patty), F])
in
  (* add in _ => F case *)
  list_mk_comb(bar, [real_cases, arrF_case])
end
*)

val alpha_rwt = prove(
  ``(∃s. (l = [TK (AlphaT s)]) ∧ P s) ⇔
    do assert(LENGTH l = 1);
       tok <- destTOK (HD l);
       s <- destAlphaT tok;
       assert(P s)
    od = SOME ()``,
  Cases_on `l` >> rw[assert_def, optionTheory.OPTION_BIND_def,
                     optionTheory.OPTION_IGNORE_BIND_def] >>
  Cases_on `h` >> rw[] >>
  Cases_on `a` >> rw[listTheory.LENGTH_NIL]);

val symbol_rwt = prove(
  ``(∃s. (l = [TK (SymbolT s)]) ∧ P s) ⇔
    do assert(LENGTH l = 1);
       tok <- destTOK (HD l);
       s <- destSymbolT tok;
       assert(P s)
    od = SOME ()``,
  Cases_on `l` >> rw[assert_def, optionTheory.OPTION_BIND_def,
                     optionTheory.OPTION_IGNORE_BIND_def] >>
  Cases_on `h` >> rw[] >>
  Cases_on `a` >> rw[listTheory.LENGTH_NIL]);

val solosymbol_rwt = prove(
  ``(?s. l = [TK (SymbolT s)]) ⇔
    do assert (LENGTH l = 1);
       tok <- destTOK (HD l);
       assert (isSymbolT tok)
    od = SOME ()``,
  Cases_on `l` >> rw[assert_def, optionTheory.OPTION_BIND_def,
                     optionTheory.OPTION_IGNORE_BIND_def] >>
  Cases_on `h` >> rw[]  >>
  Cases_on `a` >> rw[listTheory.LENGTH_NIL])

val soloalpha_rwt = prove(
  ``(?s. l = [TK (AlphaT s)]) ⇔
    do assert (LENGTH l = 1);
       tok <- destTOK (HD l);
       assert (isAlphaT tok)
    od = SOME ()``,
  Cases_on `l` >> rw[assert_def, optionTheory.OPTION_BIND_def,
                     optionTheory.OPTION_IGNORE_BIND_def] >>
  Cases_on `h` >> rw[]  >>
  Cases_on `a` >> rw[listTheory.LENGTH_NIL])

val onecon_rwts =
    [mmlG_def, alpha_rwt, symbol_rwt, solosymbol_rwt, soloalpha_rwt]
fun onecon t = let
  val _ = print ("onecon: " ^ term_to_string t ^ "\n")
  val n = mk_var("n", ``:NT``)
  val ass = ASSUME (mk_eq(n, t))
in
  SPEC n mml_okrule_def
       |> SPEC_ALL
       |> CONV_RULE
            (RAND_CONV (SIMP_CONV (srw_ss()) (ass::onecon_rwts)))
end

val nt_cases = TypeBase.nchotomy_of  ``:MMLnonT`` |> Q.SPEC `n`

val condcombine_lemma = prove(
  ``(P ==> (v = e1)) ∧ (¬P ⇒ (v = e2)) ⇔ (v = if P then e1 else e2)``,
  Cases_on `P` >> rw[])
fun condcombine1 th1 th2 = let
  val hy = hd (hyp th1)
  val th1' = DISCH hy th1
  val th2' = DISCH (mk_neg hy) th2
  val cth = CONJ th1' th2'
in
  CONV_RULE (REWR_CONV condcombine_lemma) cth
end

val sum_cases = TypeBase.nchotomy_of ``:α + β``
                                     |> Q.SPEC `n`
                                     |> INST_TYPE [alpha |-> ``:MMLnonT``,
                                                   beta |-> ``:num``]

val mkNT_t = Term.inst [alpha |-> ``:MMLnonT``, beta |-> ``:num``]
                       sumSyntax.inl_tm

fun mk_nested_case ntth eqn = let
  fun eqelim nteq = TRANS eqn (AP_TERM mkNT_t nteq)
  fun recurse ntth =
      case Lib.total dest_disj (concl ntth) of
          NONE => eqelim ntth
        | SOME (d1,d2) =>
          let
            val d1_th = eqelim (ASSUME d1)
            val d2_th = recurse (ASSUME d2)
          in
            DISJ_CASES ntth
                       (DISJ1 d1_th (concl d2_th))
                       (DISJ2 (concl d1_th) d2_th)
          end
in
  recurse ntth
end

val nested_nt_cases =
    mk_nested_case nt_cases (ASSUME (mk_eq(``n:NT``, ``mkNT n``)))

val big_cases = let
  val d1 = CHOOSE (``n:MMLnonT``, ASSUME ``?x. n = mkNT x``) nested_nt_cases
in
  DISJ_CASES sum_cases
             (DISJ1 d1 (``∃i. n:NT = INR i``))
             (DISJ2 (concl d1) (ASSUME ``∃i. n:NT = INR i``))
end

fun combine_to_cond ths = let
  fun recurse negconds ths =
      case ths of
          [] => raise Fail "Can't happen"
        | [last] =>
          let
            val hy = hd (hyp last)
            val falsum = REWRITE_RULE (ASSUME (mk_neg hy)::negconds) big_cases
          in
            PROVE_HYP (CCONTR hy falsum) last
          end
        | h::t =>
          let
            val hy = hd (hyp h)
          in
            condcombine1 h (recurse (ASSUME (mk_neg hy)::negconds) t)
          end
in
  recurse [] ths
end

val okrule_rwts0 =
    TypeBase.constructors_of ``:MMLnonT``
                             |> map (fn t => onecon ``mkNT ^t``)

val inr_th = let
  val exth = ASSUME ``?i. n:NT = INR i``
  val th0 = onecon ``INR i:NT``
in
  CHOOSE(``i:num``, exth) th0
end

val mml_okrule_eval_th = save_thm(
  "mml_okrule_eval_th",
  (okrule_rwts0 @ [inr_th]) |> combine_to_cond)

val _ = export_theory()
