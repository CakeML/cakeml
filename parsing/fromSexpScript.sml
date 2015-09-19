open HolKernel Parse boolLib bossLib;

open simpleSexpTheory astTheory
open monadsyntax lcsymtacs

val _ = new_theory "fromSexp";

val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("fail", ``NONE``)
val _ = temp_overload_on ("lift", ``OPTION_MAP``)

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def",
                                        "option.OPTION_MAP2_DEF"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)


val odestSXSTR_def = Define`
  (odestSXSTR (SX_STR s) = SOME s) ∧
  (odestSXSTR _ = NONE)
`;
val odestSXSYM_def = Define`
  (odestSXSYM (SX_SYM s) = SOME s) ∧
  (odestSXSYM _ = NONE)
`;

val odestSXNUM_def = Define`
  (odestSXNUM (SX_NUM n) = SOME n) ∧
  (odestSXNUM _ = NONE)
`;

val sexpopt_def = Define`
  sexpopt p s =
    do
       nm <- odestSXSYM s ;
       assert(nm = "NONE");
       return NONE
    od ++
    do
      (nm,args) <- dstrip_sexp s;
      assert(nm = "SOME" ∧ LENGTH args = 1);
      lift SOME (p (HD args))
    od
`;

val sexplist_def = Define`
  sexplist p s =
    case s of
      SX_CONS h t =>
        do
          ph <- p h;
          pt <- sexplist p t;
          return (ph::pt)
        od
    | SX_SYM s => if s = "nil" then return [] else fail
    | _ => fail
`;

val sexppair_def = Define`
  sexppair p1 p2 s =
    case s of
      SX_CONS s1 s2 => lift2 (,) (p1 s1) (p2 s2)
    | _ => fail
`;

val sexppair_CONG = store_thm(
  "sexppair_CONG[defncong]",
  ``∀s1 s2 p1 p1' p2 p2'.
       s1 = s2 ∧
       (∀s. (∃s'. s2 = SX_CONS s s') ⇒ p1 s = p1' s) ∧
       (∀s. (∃s'. s2 = SX_CONS s' s) ⇒ p2 s = p2' s)
      ⇒
       sexppair p1 p2 s1 = sexppair p1' p2' s2``,
  simp[] >> Cases >> simp[sexppair_def])


val strip_sxcons_FAIL_sexplist_FAIL = store_thm(
  "strip_sxcons_FAIL_sexplist_FAIL",
  ``∀s. (strip_sxcons s = NONE) ⇒ (sexplist p s = NONE)``,
  Induct >> simp[Once strip_sxcons_def, Once sexplist_def] >>
  metis_tac[TypeBase.nchotomy_of ``:α option``]);

val monad_bind_FAIL = store_thm(
  "monad_bind_FAIL",
  ``monad_bind m1 (λx. fail) = fail``,
  Cases_on `m1` >> simp[]);

val monad_unitbind_CONG = store_thm(
  "monad_unitbind_CONG[defncong]",
  ``∀m11 m21 m12 m22.
      m11 = m12 ∧ (m12 = SOME () ⇒ m21 = m22) ⇒
      monad_unitbind m11 m21 = monad_unitbind m12 m22``,
  simp[] >> rpt gen_tac >> qcase_tac `m12 = SOME ()` >>
  Cases_on `m12` >> simp[]);

val sexplist_CONG = store_thm(
  "sexplist_CONG[defncong]",
  ``∀s1 s2 p1 p2.
      (s1 = s2) ∧ (∀e. sxMEM e s2 ⇒ p1 e = p2 e) ⇒
      (sexplist p1 s1 = sexplist p2 s2)``,
  simp[sxMEM_def] >> Induct >> dsimp[Once strip_sxcons_def]
  >- (ONCE_REWRITE_TAC [sexplist_def] >> simp[] >>
      qcase_tac `strip_sxcons t` >> Cases_on `strip_sxcons t` >>
      simp[]
      >- (simp[strip_sxcons_FAIL_sexplist_FAIL, monad_bind_FAIL]) >>
      map_every qx_gen_tac [`p1`, `p2`] >> strip_tac >>
      Cases_on `p2 s2` >> simp[] >> fs[] >> metis_tac[]) >>
  simp[sexplist_def]);

val _ = temp_overload_on ("guard", ``λb m. monad_unitbind (assert b) m``)


val sexpid_def = Define`
  sexpid p s =
    do
       (nm, args) <- dstrip_sexp s;
       (guard (nm = "Short" ∧ LENGTH args = 1)
              (lift Short (p (EL 0 args))) ++
        guard (nm = "Long" ∧ LENGTH args = 2)
              (lift2 Long (odestSXSTR (EL 0 args)) (p (EL 1 args))))
    od
`;

val sexptctor_def = Define`
  sexptctor s =
    do
       (nm, args) <- dstrip_sexp s ;
       assert(nm = "TC_name" ∧ LENGTH args = 1);
       lift TC_name (sexpid odestSXSTR (EL 0 args))
    od ++
    do
      nm <- odestSXSYM s ;
      (guard (nm = "TC_int") (return TC_int) ++
       guard (nm = "TC_char") (return TC_char) ++
       guard (nm = "TC_string") (return TC_string) ++
       guard (nm = "TC_ref") (return TC_ref) ++
       guard (nm = "TC_word") (return TC_word8) ++
       guard (nm = "TC_word8array") (return TC_word8array) ++
       guard (nm = "TC_fn") (return TC_fn) ++
       guard (nm = "TC_tup") (return TC_tup) ++
       guard (nm = "TC_exn") (return TC_exn) ++
       guard (nm = "TC_vector") (return TC_vector) ++
       guard (nm = "TC_array") (return TC_array))
    od
`;

val sxMEM_sizelt = store_thm(
  "sxMEM_sizelt",
  ``∀s1 s2. sxMEM s1 s2 ⇒ sexp_size s1 < sexp_size s2``,
  dsimp[sxMEM_def] >> Induct_on `s2` >>
  dsimp[Once strip_sxcons_def, sexp_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

val dstrip_sexp_size = store_thm(
  "dstrip_sexp_size",
  ``∀s sym args. dstrip_sexp s = SOME (sym, args) ⇒
                 ∀e. MEM e args ⇒ sexp_size e < sexp_size s``,
  Induct >> simp[dstrip_sexp_def, sexp_size_def] >>
  qcase_tac `sexp_CASE sxp` >> Cases_on `sxp` >> simp[] >> rpt strip_tac >>
  qcase_tac `MEM sxp0 sxpargs` >> qcase_tac `strip_sxcons sxp'` >>
  `sxMEM sxp0 sxp'` by metis_tac[sxMEM_def] >> imp_res_tac sxMEM_sizelt >>
  simp[]);

val sexptype_def = tDefine "sexptype" `
  sexptype s =
    do
       (s, args) <- dstrip_sexp s ;
       (guard (s = "Tvar" ∧ LENGTH args = 1)
              (lift Tvar (odestSXSTR (EL 0 args))) ++
        guard (s = "Tvar_db" ∧ LENGTH args = 1)
              (lift Tvar_db (odestSXNUM (EL 0 args))) ++
        guard (s = "Tapp" ∧ LENGTH args = 2)
              (lift2 Tapp (sexplist sexptype (EL 0 args))
                     (sexptctor (EL 1 args))))
    od
` (WF_REL_TAC `measure sexp_size` >> simp[] >> rpt strip_tac >>
   qcase_tac `sxMEM s0 (HD args)` >>
   `sexp_size s0 < sexp_size (HD args)` by metis_tac[sxMEM_sizelt] >>
   `MEM (HD args) args`
      by metis_tac[DECIDE ``0n < 2``, rich_listTheory.EL_MEM, listTheory.EL] >>
   `sexp_size (HD args) < sexp_size s` by metis_tac[dstrip_sexp_size] >>
   simp[]);

val sexplit_def = Define`
  sexplit s =
    lift (IntLit o (&)) (odestSXNUM s) ++
    lift StrLit (odestSXSTR s) ++
    do
      (nm,args) <- dstrip_sexp s;
      assert(LENGTH args = 1);
      guard (nm = "-") (lift (λn. IntLit (-&n)) (odestSXNUM (HD args))) ++
      guard (nm = "char")
            do
              cs <- odestSXSTR (HD args);
              assert(LENGTH cs = 1);
              return (Char (HD cs))
            od ++
      guard (nm = "word8")
            do
              n <- odestSXNUM (HD args);
              assert(n < 256);
              return (Word8 (n2w n))
            od
    od
`;

(* don't require Pvar constructors; bare strings can be pattern variables.
   Unclear if this sort of special-casing is ever likely to be helpful *)
val sexppat_def = tDefine "sexppat" `
  sexppat s =
    lift Pvar (odestSXSTR s) ++
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Plit" ∧ LENGTH args = 1)
            (lift Plit (sexplit (EL 0 args))) ++
      guard (nm = "Pcon" ∧ LENGTH args = 2)
            (lift2 Pcon (sexpopt (sexpid odestSXSTR) (EL 0 args))
                        (sexplist sexppat (EL 1 args))) ++
      guard (nm = "Pref" ∧ LENGTH args = 1) (lift Pref (sexppat (EL 0 args)))
    od
`
  (WF_REL_TAC `measure sexp_size` >> simp[] >> rpt strip_tac
   >- metis_tac[arithmeticTheory.LESS_TRANS, rich_listTheory.EL_MEM,
                DECIDE ``1n < 2``, sxMEM_sizelt, dstrip_sexp_size]
   >- metis_tac[rich_listTheory.EL_MEM, DECIDE ``0n < 1``, listTheory.EL,
                dstrip_sexp_size])

val sexpexp_def = tDefine "sexpexp" `
  sexpexp s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Raise" ∧ LENGTH args = 1)
            (lift Raise (sexpexp (EL 0 args))) ++
      guard (nm = "Handle" ∧ LENGTH args = 2)
            (lift2 Handle
                   (sexpexp (EL 0 args))
                   (sexplist (sexppair sexppat sexpexp) (EL 1 args))) ++
      guard (nm = "Lit" ∧ LENGTH args = 1)
            (lift Lit (sexplit (EL 0 args))) ++
      guard (nm = "Con" ∧ LENGTH args = 2)
            (lift2 Con
                   (sexpopt (sexpid odestSXSTR) (EL 0 args))
                   (sexplist sexpexp (EL 1 args))) ++
      guard (nm = "Var" ∧ LENGTH args = 1)
            (lift Var (sexpid odestSXSTR (EL 0 args)))
    od
`
  (WF_REL_TAC `measure sexp_size` >> simp[] >> rpt strip_tac
   >- (qcase_tac `sxMEM sx0 (EL 1 args)` >>
       `sexp_size sx0 < sexp_size (EL 1 args)` by simp[sxMEM_sizelt] >>
       rw[] >> fs[sexp_size_def] >>
       `sexp_size (EL 1 args) < sexp_size s`
         by simp[dstrip_sexp_size, rich_listTheory.EL_MEM] >>
       simp[])
   >- metis_tac[rich_listTheory.EL_MEM, listTheory.EL, DECIDE ``1n < 2``,
                dstrip_sexp_size, sxMEM_sizelt, arithmeticTheory.LESS_TRANS]
   >- metis_tac[rich_listTheory.EL_MEM, listTheory.EL, DECIDE ``0n < 2``,
                dstrip_sexp_size]
   >- metis_tac[rich_listTheory.EL_MEM, listTheory.EL, DECIDE ``0n < 1``,
                dstrip_sexp_size])

val sexptype_def_def = Define`
  sexptype_def =
  sexplist
    (sexppair (sexplist odestSXSTR)
      (sexppair odestSXSTR
        (sexplist (sexppair odestSXSTR (sexplist sexptype)))))`;

val sexpdec_def = Define`
  sexpdec s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Dlet" ∧ LENGTH args = 2)
            (lift2 Dlet (sexppat (EL 0 args)) (sexpexp (EL 1 args))) ++
      guard (nm = "Dletrec" ∧ LENGTH args = 1)
            (lift Dletrec (sexplist (sexppair odestSXSTR (sexppair odestSXSTR sexpexp)) (HD args))) ++
      guard (nm = "Dtype" ∧ LENGTH args = 1)
            (lift Dtype (sexptype_def (HD args))) ++
      guard (nm = "Dtabbrev" ∧ LENGTH args = 3)
            (lift Dtabbrev (sexplist odestSXSTR (EL 0 args)) <*>
                           (odestSXSTR (EL 1 args)) <*>
                           (sexptype (EL 2 args))) ++
      guard (nm = "Dexn" ∧ LENGTH args = 2)
            (lift2 Dexn (odestSXSTR (EL 0 args)) (sexplist sexptype (EL 1 args)))
    od`;

val sexpspec_def = Define`
  sexpspec s =
    do
       (nm, args) <- dstrip_sexp s ;
       if nm = "Sval" then
         guard (LENGTH args = 2)
               (lift2 Sval (odestSXSTR (HD args)) (sexptype (EL 1 args)))
       else if nm = "Stype" then
         guard (LENGTH args = 1)
               (lift Stype (sexptype_def (HD args)))
       else if nm = "Stabbrev" then
         guard (LENGTH args = 3)
               (lift Stabbrev
                       (sexplist odestSXSTR (HD args)) <*>
                       (odestSXSTR (EL 1 args)) <*>
                       (sexptype (EL 2 args)))
       else if nm = "Stype_opq" then
         guard (LENGTH args = 2)
               (lift2 Stype_opq
                      (sexplist odestSXSTR (EL 0 args))
                      (odestSXSTR (EL 1 args)))
       else if nm = "Sexn" then
         guard (LENGTH args = 2)
               (lift2 Sexn (odestSXSTR (EL 0 args))
                      (sexplist sexptype (EL 1 args)))
       else fail
    od
`;

val sexptop_def = Define`
  sexptop s =
    do
        (nm, args) <- dstrip_sexp s ;
        if nm = "Tmod" then
          do
             assert (LENGTH args = 3);
             modN <- odestSXSTR (HD args);
             specopt <- sexpopt (sexplist sexpspec) (EL 1 args);
             declist <- sexplist sexpdec (EL 2 args);
             return (Tmod modN specopt declist)
          od
        else if nm = "Tdec" then
          do
             assert (LENGTH args = 1);
             lift Tdec (sexpdec (HD args))
          od
        else fail
    od
`;

val _ = export_theory();
