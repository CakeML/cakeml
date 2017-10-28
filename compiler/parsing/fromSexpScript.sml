open preamble match_goal
open simpleSexpTheory astTheory

val _ = new_theory "fromSexp";
val _ = set_grammar_ancestry ["simpleSexp", "ast", "location","fpSem"]
val _ = option_monadsyntax.temp_add_option_monadsyntax()

(* TODO: move*)

(* cf. similar TODO in cmlPtreeConversionScript.sml *)
val _ = temp_overload_on ("lift", ``OPTION_MAP``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_CHOICE_def",
                                        "option.OPTION_MAP2_DEF"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)
(* -- *)

val OPTION_APPLY_MAP3 = Q.store_thm("OPTION_APPLY_MAP3",
  `OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z = SOME r ⇔
   ∃a b c. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ f a b c = r`,
  Cases_on`x`\\simp[] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`y`\\fs[]);

val OPTION_APPLY_MAP4 = Q.store_thm("OPTION_APPLY_MAP3",
  `OPTION_APPLY (OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z ) t= SOME r ⇔
   ∃a b c d. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ t = SOME d /\ f a b c d= r`,
  Cases_on`x`\\simp[] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`y`\\fs[] \\ Cases_on`z`\\fs[]);

val FOLDR_SX_CONS_INJ = Q.store_thm("FOLDR_SX_CONS_INJ",
  `∀l1 l2. FOLDR SX_CONS nil l1 = FOLDR SX_CONS nil l2 ⇔ l1 = l2`,
  Induct \\ simp[]
  >- ( Induct \\ simp[] )
  \\ gen_tac \\ Induct \\ simp[]);

val strip_sxcons_11 = Q.store_thm("strip_sxcons_11",
  `∀s1 s2 x. strip_sxcons s1 = SOME x ∧ strip_sxcons s2 = SOME x ⇒ s1 = s2`,
  ho_match_mp_tac simpleSexpTheory.strip_sxcons_ind
  \\ ntac 4 strip_tac
  \\ simp[Once simpleSexpTheory.strip_sxcons_def]
  \\ CASE_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]
  \\ pop_assum mp_tac
  \\ simp[Once simpleSexpTheory.strip_sxcons_def]
  \\ CASE_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]);

val dstrip_sexp_size = Q.store_thm(
  "dstrip_sexp_size",
  `∀s sym args. dstrip_sexp s = SOME (sym, args) ⇒
                 ∀e. MEM e args ⇒ sexp_size e < sexp_size s`,
  Induct >> simp[dstrip_sexp_def, sexp_size_def] >>
  rename1 `sexp_CASE sxp` >> Cases_on `sxp` >> simp[] >> rpt strip_tac >>
  rename1 `MEM sxp0 sxpargs` >> rename1 `strip_sxcons sxp'` >>
  `sxMEM sxp0 sxp'` by metis_tac[sxMEM_def] >> imp_res_tac sxMEM_sizelt >>
  simp[]);

val dstrip_sexp_SOME = Q.store_thm("dstrip_sexp_SOME",
  `dstrip_sexp s = SOME x ⇔
   ∃sym sa args. s =
     SX_CONS (SX_SYM sym) sa ∧
     strip_sxcons sa = SOME args ∧
     (x = (sym,args))`,
  Cases_on`s`>>simp[dstrip_sexp_def]>>
  every_case_tac>>simp[])

val strip_sxcons_SOME_NIL = Q.store_thm("strip_sxcons_SOME_NIL[simp]",
  `strip_sxcons s = SOME [] ⇔ s = nil`,
  rw[Once strip_sxcons_def] >>
  every_case_tac >> simp[])

val strip_sxcons_EQ_CONS = Q.store_thm(
  "strip_sxcons_EQ_CONS[simp]",
  `strip_sxcons s = SOME (h::t) ⇔
     ∃s0. s = SX_CONS h s0 ∧ strip_sxcons s0 = SOME t`,
  simp[Once strip_sxcons_def] >> every_case_tac >> simp[] >>
  metis_tac[]);

val type_ind =
  (TypeBase.induction_of``:t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`

val pat_ind =
  (TypeBase.induction_of``:pat``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`

val exp_ind =
  (TypeBase.induction_of``:exp``)
  |> Q.SPECL[`P`,`EVERY (P o SND o SND)`,`P o SND o SND`,`EVERY (P o SND)`,`P o SND`,`P o SND`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`
(* -- *)

val encode_control_def = Define`
  (encode_control "" = "") ∧
  (encode_control (c::cs) =
    if c = #"\\" then c::c::(encode_control cs)
    else if isPrint c then c::(encode_control cs)
    else (#"\\" :: ((if ORD c < 16 then "0" else "")++num_to_hex_string (ORD c)))
         ++(encode_control cs))`;

val decode_control_def = Define`
  (decode_control "" = SOME "") ∧
  (decode_control (c::cs) =
     if c = #"\\" then
     case cs of
     | #"\\"::cs => OPTION_MAP (CONS c) (decode_control cs)
     | d1::d2::cs =>
       OPTION_IGNORE_BIND (OPTION_GUARD
         (isHexDigit d1 ∧ isHexDigit d2
          ∧ (isAlpha d1 ⇒ isUpper d1)
          ∧ (isAlpha d2 ⇒ isUpper d2)
          ∧ ¬isPrint (CHR (num_from_hex_string[d1;d2]))))
       (OPTION_MAP (CONS (CHR (num_from_hex_string[d1;d2]))) (decode_control cs))
     | _ => NONE
     else OPTION_IGNORE_BIND (OPTION_GUARD (isPrint c)) (OPTION_MAP (CONS c) (decode_control cs)))`;

val EVERY_isPrint_encode_control = Q.store_thm("EVERY_isPrint_encode_control",
  `∀ls. EVERY isPrint (encode_control ls)`,
  Induct \\ rw[encode_control_def]
  \\ TRY (qmatch_rename_tac`isPrint _` \\ EVAL_TAC)
  \\ metis_tac[EVERY_isHexDigit_num_to_hex_string,MONO_EVERY,isHexDigit_isPrint,EVERY_CONJ]);

val decode_encode_control = Q.store_thm("decode_encode_control[simp]",
  `∀ls. decode_control (encode_control ls) = SOME ls`,
  Induct \\ rw[encode_control_def,decode_control_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ rw[decode_control_def,encode_control_def]
  \\ fs[] \\ rw[decode_control_def]
  \\ imp_res_tac num_to_hex_string_length_1
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_1] \\ rfs[]
  \\ fs[]
  \\ fs[arithmeticTheory.NOT_LESS]
  \\ qspec_then`h`strip_assume_tac stringTheory.ORD_BOUND
  \\ imp_res_tac num_to_hex_string_length_2
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rfs[]
  \\ rw[] \\ fs[] \\ rw[]
  \\ simp[]
  \\ qspec_then`ORD h`strip_assume_tac EVERY_isHexDigit_num_to_hex_string
  \\ rfs[]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ TRY (pop_assum mp_tac \\ EVAL_TAC \\ NO_TAC)
  \\ TRY (RULE_ASSUM_TAC (fn th => if th |> concl |> free_vars |> null then
                                     CONV_RULE EVAL th
                                   else th) \\ fs[] \\ NO_TAC)
  \\ simp[num_from_hex_string_leading_0]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ simp[stringTheory.CHR_ORD])

val isHexDigit_alt = Q.prove(
  `isHexDigit c ⇔ c ∈ set "0123456789abcdefABCDEF"`,
  rw[stringTheory.isHexDigit_def, EQ_IMP_THM] >> CONV_TAC EVAL >> simp[]);

val UNHEX_lt16 = Q.prove(
  `isHexDigit c ⇒ UNHEX c < 16`,
  dsimp[isHexDigit_alt, ASCIInumbersTheory.UNHEX_def]);

val isAlpha_isUpper_isLower = Q.store_thm(
  "isAlpha_isUpper_isLower",
  `isAlpha c ⇒ (isUpper c ⇎ isLower c)`,
  simp[isAlpha_def, isUpper_def, isLower_def]);

val isLower_isAlpha = Q.store_thm(
  "isLower_isAlpha",
  `isLower c ⇒ isAlpha c`,
  simp[isLower_def, isAlpha_def]);

open ASCIInumbersTheory numposrepTheory
val encode_decode_control = Q.store_thm("encode_decode_control",
  `∀ls r. decode_control ls = SOME r ⇒ ls = encode_control r`,
  ho_match_mp_tac (theorem"decode_control_ind")
  \\ rw[]
  >- ( fs[decode_control_def] \\ rw[encode_control_def] )
  \\ pop_assum mp_tac
  \\ reverse(rw[Once decode_control_def])
  >- (
    fs[]
    \\ rw[encode_control_def] )
  \\ last_x_assum mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    rw[] \\ fs[]
    \\ rw[encode_control_def] )
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ rw[] \\ fs[] \\ rw[] \\ fs[] \\ rw[]
  \\ simp[encode_control_def]
  \\ IF_CASES_TAC
  >- ( fs[stringTheory.isPrint_def] )
  \\ simp[num_from_hex_string_length_2]
  \\ simp[num_from_hex_string_def,num_to_hex_string_def]
  \\ simp[n2s_s2n, UNHEX_lt16, GREATER_DEF] >>
  qmatch_abbrev_tac `s = _` >>
  qabbrev_tac `N = s2n 16 UNHEX s` >>
  Cases_on `N = 0` >> simp[]
  >- (simp[Abbr`s`, Abbr`N`] >> fs[s2n_def, l2n_def] >>
      rename1`c1 = #"0" ∧ c2 = #"0"` >>
      `UNHEX c1 < 16 ∧ UNHEX c2 < 16` by simp[UNHEX_lt16] >>
      `UNHEX c1 = 0 ∧ UNHEX c2 = 0` by intLib.ARITH_TAC >>
      conj_tac >| [
        Q.UNDISCH_THEN `isHexDigit c1` mp_tac,
        Q.UNDISCH_THEN `isHexDigit c2` mp_tac
      ] >>
      simp[isHexDigit_alt] >> strip_tac >> fs[UNHEX_def]) >>
  Cases_on `N < 16` >> simp[]
  >- (`LOG 16 N = 0` by simp[logrootTheory.LOG_EQ_0] >>
      simp[Abbr`s`, LASTN_def, HEX_UNHEX, toUpper_def] >>
      simp[Abbr`N`] >> fs[s2n_def, l2n_def] >>
      rename1`16 * UNHEX c1 MOD 16 + UNHEX c2 MOD 16 < 16` >>
      `UNHEX c1 MOD 16 = 0` by simp[] >>
      `UNHEX c1 < 16` by simp[UNHEX_lt16] >>
      `UNHEX c1 = 0` by intLib.ARITH_TAC >>
      conj_tac
      >- (Q.UNDISCH_THEN `isHexDigit c1` mp_tac >> simp[isHexDigit_alt] >>
          strip_tac >> fs[UNHEX_def]) >>
      metis_tac[isLower_isAlpha, isAlpha_isUpper_isLower]) >>
  `N < 256`
    by metis_tac[num_from_hex_string_length_2, num_from_hex_string_def] >>
  `LOG 16 N = 1` by simp[logrootTheory.LOG_UNIQUE] >>
  simp[Abbr`s`, Abbr`N`, LASTN_def, HEX_UNHEX, toUpper_def] >>
  metis_tac[isLower_isAlpha, isAlpha_isUpper_isLower])

val SEXSTR_def = Define`
  SEXSTR s = SX_STR (encode_control s)`;

val SEXSTR_11 = Q.store_thm("SEXSTR_11[simp]",
  `SEXSTR s1 = SEXSTR s2 ⇔ s1 = s2`,
  rw[SEXSTR_def]
  \\ metis_tac[decode_encode_control,SOME_11]);

val SEXSTR_distinct = Q.store_thm("SEXSTR_distinct[simp]",
  `(SEXSTR s ≠ SX_SYM sym) ∧
   (SEXSTR s ≠ SX_NUM num) ∧
   (SEXSTR s ≠ SX_CONS a d) ∧
   ((SEXSTR s = SX_STR s') ⇔ s' = encode_control s)`,
  rw[SEXSTR_def,EQ_IMP_THM]);

val odestSEXSTR_def = Define`
  (odestSEXSTR (SX_STR s) = decode_control s) ∧
  (odestSEXSTR _ = NONE)`;

val encode_control_remove = Q.store_thm("encode_control_remove",
  `∀s. EVERY isPrint s ∧ #"\\" ∉ set s ⇒ encode_control s = s`,
  Induct \\ simp[encode_control_def]);

val SEXSTR_remove = Q.store_thm("SEXSTR_remove",
  `EVERY isPrint s ∧ #"\\" ∉ set s ⇒ SEXSTR s = SX_STR s`,
  rw[SEXSTR_def,encode_control_remove]);

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

val sexppair_CONG = Q.store_thm(
  "sexppair_CONG[defncong]",
  `∀s1 s2 p1 p1' p2 p2'.
       s1 = s2 ∧
       (∀s. (∃s'. s2 = SX_CONS s s') ⇒ p1 s = p1' s) ∧
       (∀s. (∃s'. s2 = SX_CONS s' s) ⇒ p2 s = p2' s)
      ⇒
       sexppair p1 p2 s1 = sexppair p1' p2' s2`,
  simp[] >> Cases >> simp[sexppair_def])


val strip_sxcons_FAIL_sexplist_FAIL = Q.store_thm(
  "strip_sxcons_FAIL_sexplist_FAIL",
  `∀s. (strip_sxcons s = NONE) ⇒ (sexplist p s = NONE)`,
  Induct >> simp[Once strip_sxcons_def, Once sexplist_def] >>
  metis_tac[TypeBase.nchotomy_of ``:α option``]);

val monad_bind_FAIL = Q.store_thm(
  "monad_bind_FAIL",
  `monad_bind m1 (λx. fail) = fail`,
  Cases_on `m1` >> simp[]);

val monad_unitbind_CONG = Q.store_thm(
  "monad_unitbind_CONG[defncong]",
  `∀m11 m21 m12 m22.
      m11 = m12 ∧ (m12 = SOME () ⇒ m21 = m22) ⇒
      monad_unitbind m11 m21 = monad_unitbind m12 m22`,
  simp[] >> rpt gen_tac >> rename1 `m12 = SOME ()` >>
  Cases_on `m12` >> simp[]);

val sexplist_CONG = Q.store_thm(
  "sexplist_CONG[defncong]",
  `∀s1 s2 p1 p2.
      (s1 = s2) ∧ (∀e. sxMEM e s2 ⇒ p1 e = p2 e) ⇒
      (sexplist p1 s1 = sexplist p2 s2)`,
  simp[sxMEM_def] >> Induct >> dsimp[Once strip_sxcons_def]
  >- (ONCE_REWRITE_TAC [sexplist_def] >> simp[] >>
      rename1 `strip_sxcons t` >> Cases_on `strip_sxcons t` >>
      simp[]
      >- (simp[strip_sxcons_FAIL_sexplist_FAIL, monad_bind_FAIL]) >>
      map_every qx_gen_tac [`p1`, `p2`] >> strip_tac >>
      Cases_on `p2 s2` >> simp[] >> fs[] >> metis_tac[]) >>
  simp[sexplist_def]);

val _ = temp_overload_on ("guard", ``λb m. monad_unitbind (assert b) m``);


val sexpid_def = tDefine "sexpid" `
  sexpid p s =
    do
       (nm, args) <- dstrip_sexp s;
       (guard (nm = "Short" ∧ LENGTH args = 1)
              (lift Short (p (EL 0 args))) ++
        guard (nm = "Long" ∧ LENGTH args = 2)
              (lift2 Long (odestSEXSTR (EL 0 args)) (sexpid p (EL 1 args))))
    od
`
 (simp [] >>
  wf_rel_tac `measure (sexp_size o SND)` >>
  rw [] >>
  irule dstrip_sexp_size >>
  rw [EL_MEM]);

val sexptctor_def = Define`
  sexptctor s =
    do
       (nm, args) <- dstrip_sexp s ;
       assert(nm = "TC_name" ∧ LENGTH args = 1);
       lift TC_name (sexpid odestSEXSTR (EL 0 args))
    od ++
    do
      nm <- odestSXSYM s ;
      (guard (nm = "TC_int") (return TC_int) ++
       guard (nm = "TC_char") (return TC_char) ++
       guard (nm = "TC_string") (return TC_string) ++
       guard (nm = "TC_ref") (return TC_ref) ++
       guard (nm = "TC_word8") (return TC_word8) ++
       guard (nm = "TC_word64") (return TC_word64) ++
       guard (nm = "TC_word8array") (return TC_word8array) ++
       guard (nm = "TC_fn") (return TC_fn) ++
       guard (nm = "TC_tup") (return TC_tup) ++
       guard (nm = "TC_exn") (return TC_exn) ++
       guard (nm = "TC_vector") (return TC_vector) ++
       guard (nm = "TC_array") (return TC_array))
    od
`;

val sexptype_def = tDefine "sexptype" `
  sexptype s =
    do
       (s, args) <- dstrip_sexp s ;
       (guard (s = "Tvar" ∧ LENGTH args = 1)
              (lift Tvar (odestSEXSTR (EL 0 args))) ++
        guard (s = "Tvar_db" ∧ LENGTH args = 1)
              (lift Tvar_db (odestSXNUM (EL 0 args))) ++
        guard (s = "Tapp" ∧ LENGTH args = 2)
              (lift2 Tapp (sexplist sexptype (EL 0 args))
                     (sexptctor (EL 1 args))))
    od
` (WF_REL_TAC `measure sexp_size` >> simp[] >> rpt strip_tac >>
   rename1 `sxMEM s0 (HD args)` >>
   `sexp_size s0 < sexp_size (HD args)` by metis_tac[sxMEM_sizelt] >>
   `MEM (HD args) args`
      by metis_tac[DECIDE ``0n < 2``, rich_listTheory.EL_MEM, listTheory.EL] >>
   `sexp_size (HD args) < sexp_size s` by metis_tac[dstrip_sexp_size] >>
   simp[]);

val sexplit_def = Define`
  sexplit s =
    lift (IntLit o (&)) (odestSXNUM s) ++
    lift StrLit (odestSEXSTR s) ++
    do
      (nm,args) <- dstrip_sexp s;
      assert(LENGTH args = 1);
      guard (nm = "-") (OPTION_BIND (odestSXNUM (HD args)) (λn. if n = 0 then NONE else SOME (IntLit (-&n)))) ++
      guard (nm = "char")
            do
              cs <- odestSEXSTR (HD args);
              assert(LENGTH cs = 1);
              return (Char (HD cs))
            od ++
      guard (nm = "word8")
            do
              n <- odestSXNUM (HD args);
              assert(n < 256);
              return (Word8 (n2w n))
            od ++
      guard (nm = "word64")
            do
              n <- odestSXNUM (HD args);
              assert(n < 2**64);
              return (Word64 (n2w n))
            od
    od
`;

(* don't require Pvar constructors; bare strings can be pattern variables.
   Unclear if this sort of special-casing is ever likely to be helpful *)
val sexppat_def = tDefine "sexppat" `
  sexppat s =
    lift Pvar (odestSEXSTR s) ++
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Pany" ∧ LENGTH args = 0)
            (return Pany) ++
      guard (nm = "Plit" ∧ LENGTH args = 1)
            (lift Plit (sexplit (EL 0 args))) ++
      guard (nm = "Pcon" ∧ LENGTH args = 2)
            (lift2 Pcon (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                        (sexplist sexppat (EL 1 args))) ++
      guard (nm = "Pref" ∧ LENGTH args = 1) (lift Pref (sexppat (EL 0 args))) ++
      guard (nm = "Ptannot" ∧ LENGTH args = 2)
            (lift2 Ptannot (sexppat (EL 0 args)) (sexptype (EL 1 args)))
    od
`
  (WF_REL_TAC `measure sexp_size` >> simp[] >> rpt strip_tac
   >- metis_tac[arithmeticTheory.LESS_TRANS, rich_listTheory.EL_MEM,
                DECIDE ``1n < 2``, sxMEM_sizelt, dstrip_sexp_size]
   >- metis_tac[arithmeticTheory.LESS_TRANS, rich_listTheory.EL_MEM,
                DECIDE ``0n < 2``, sxMEM_sizelt, dstrip_sexp_size,
                EL ]
   >- metis_tac[rich_listTheory.EL_MEM, DECIDE ``0n < 1``, listTheory.EL,
                dstrip_sexp_size])

val sexpop_def = Define`
  (sexpop (SX_SYM s) =
  if s = "OpnPlus" then SOME (Opn Plus) else
  if s = "OpnMinus" then SOME (Opn Minus) else
  if s = "OpnTimes" then SOME (Opn Times) else
  if s = "OpnDivide" then SOME (Opn Divide) else
  if s = "OpnModulo" then SOME (Opn Modulo) else
  if s = "OpbLt" then SOME (Opb Lt) else
  if s = "OpbGt" then SOME (Opb Gt) else
  if s = "OpbLeq" then SOME (Opb Leq) else
  if s = "OpbGeq" then SOME (Opb Geq) else
  if s = "Opw8Andw" then SOME (Opw W8 Andw) else
  if s = "Opw8Orw" then SOME (Opw W8 Orw) else
  if s = "Opw8Xor" then SOME (Opw W8 Xor) else
  if s = "Opw8Add" then SOME (Opw W8 Add) else
  if s = "Opw8Sub" then SOME (Opw W8 Sub) else
  if s = "Opw64Andw" then SOME (Opw W64 Andw) else
  if s = "Opw64Orw" then SOME (Opw W64 Orw) else
  if s = "Opw64Xor" then SOME (Opw W64 Xor) else
  if s = "Opw64Add" then SOME (Opw W64 Add) else
  if s = "Opw64Sub" then SOME (Opw W64 Sub) else
  if s = "Equality" then SOME Equality else
  if s = "FPcmpFPLess" then SOME (FP_cmp FP_Less) else
  if s = "FPcmpFPLessEqual" then SOME (FP_cmp FP_LessEqual) else
  if s = "FPcmpFPGreater" then SOME (FP_cmp FP_Greater) else
  if s = "FPcmpFPGreaterEqual" then SOME (FP_cmp FP_GreaterEqual) else
  if s = "FPcmpFPEqual" then SOME (FP_cmp FP_Equal) else
  if s = "FPuopFPAbs" then SOME (FP_uop FP_Abs) else
  if s = "FPuopFPNeg" then SOME (FP_uop FP_Neg) else
  if s = "FPuopFPSqrt" then SOME (FP_uop FP_Sqrt) else
  if s = "FPbopFPAdd" then SOME (FP_bop FP_Add) else
  if s = "FPbopFPSub" then SOME (FP_bop FP_Sub) else
  if s = "FPbopFPMul" then SOME (FP_bop FP_Mul) else
  if s = "FPbopFPDiv" then SOME (FP_bop FP_Div) else
  if s = "Opapp" then SOME Opapp else
  if s = "Opassign" then SOME Opassign else
  if s = "Opref" then SOME Opref else
  if s = "Opderef" then SOME Opderef else
  if s = "Aw8alloc" then SOME Aw8alloc else
  if s = "Aw8sub" then SOME Aw8sub else
  if s = "Aw8length" then SOME Aw8length else
  if s = "Aw8update" then SOME Aw8update else
  if s = "CopyStrStr" then SOME CopyStrStr else
  if s = "CopyStrAw8" then SOME CopyStrAw8 else
  if s = "CopyAw8Str" then SOME CopyAw8Str else
  if s = "CopyAw8Aw8" then SOME CopyAw8Aw8 else
  if s = "Ord" then SOME Ord else
  if s = "Chr" then SOME Chr else
  if s = "W8fromInt" then SOME (WordFromInt W8) else
  if s = "W8toInt" then SOME (WordToInt W8) else
  if s = "W64fromInt" then SOME (WordFromInt W64) else
  if s = "W64toInt" then SOME (WordToInt W64) else
  if s = "ChopbLt" then SOME (Chopb Lt) else
  if s = "ChopbGt" then SOME (Chopb Gt) else
  if s = "ChopbLeq" then SOME (Chopb Leq) else
  if s = "ChopbGeq" then SOME (Chopb Geq) else
  if s = "Implode" then SOME Implode else
  if s = "Strsub" then SOME Strsub else
  if s = "Strlen" then SOME Strlen else
  if s = "Strcat" then SOME Strcat else
  if s = "VfromList" then SOME VfromList else
  if s = "Vsub" then SOME Vsub else
  if s = "Vlength" then SOME Vlength else
  if s = "Aalloc" then SOME Aalloc else
  if s = "AallocEmpty" then SOME AallocEmpty else
  if s = "Asub" then SOME Asub else
  if s = "Alength" then SOME Alength else
  if s = "Aupdate" then SOME Aupdate else NONE) ∧
  (sexpop (SX_CONS (SX_SYM s) (SX_STR s')) =
     if s = "FFI" then OPTION_MAP FFI (decode_control s') else NONE
   ) ∧
  (sexpop (SX_CONS (SX_SYM s) (SX_NUM n)) =
    if s = "Shift8Lsl" then SOME (Shift W8 Lsl n) else
    if s = "Shift8Lsr" then SOME (Shift W8 Lsr n) else
    if s = "Shift8Asr" then SOME (Shift W8 Asr n) else
    if s = "Shift8Ror" then SOME (Shift W8 Ror n) else
    if s = "Shift64Lsl" then SOME (Shift W64 Lsl n) else
    if s = "Shift64Lsr" then SOME (Shift W64 Lsr n) else
    if s = "Shift64Asr" then SOME (Shift W64 Asr n) else
    if s = "Shift64Ror" then SOME (Shift W64 Ror n) else NONE) ∧
  (sexpop _ = NONE)`;

val sexplop_def = Define`
  (sexplop (SX_SYM s) =
   if s = "And" then SOME And else
   if s = "Or" then SOME Or else NONE) ∧
  (sexplop _ = NONE)`;

val sexplocn_def = Define`
  sexplocn s =
    do
      ls <- strip_sxcons s;
      guard (LENGTH ls = 6)
      (lift2 Locs
            (lift locn (odestSXNUM (EL 0 ls)) <*>
                       (odestSXNUM (EL 1 ls)) <*>
                       (odestSXNUM (EL 2 ls)))
            (lift locn (odestSXNUM (EL 3 ls)) <*>
                       (odestSXNUM (EL 4 ls)) <*>
                       (odestSXNUM (EL 5 ls)))
                       )
    od`;

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
                   (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                   (sexplist sexpexp (EL 1 args))) ++
      guard (nm = "Var" ∧ LENGTH args = 1)
            (lift Var (sexpid odestSEXSTR (EL 0 args))) ++
      guard (nm = "Fun" ∧ LENGTH args = 2)
            (lift2 Fun (odestSEXSTR (EL 0 args)) (sexpexp (EL 1 args))) ++
      guard (nm = "App" ∧ LENGTH args = 2)
            (lift2 App (sexpop (EL 0 args)) (sexplist sexpexp (EL 1 args))) ++
      guard (nm = "Log" ∧ LENGTH args = 3)
            (lift Log (sexplop (EL 0 args)) <*>
                      (sexpexp (EL 1 args)) <*>
                      (sexpexp (EL 2 args))) ++
      guard (nm = "If" ∧ LENGTH args = 3)
            (lift If (sexpexp (EL 0 args)) <*>
                     (sexpexp (EL 1 args)) <*>
                     (sexpexp (EL 2 args))) ++
      guard (nm = "Mat" ∧ LENGTH args = 2)
            (lift2 Mat
              (sexpexp (EL 0 args))
              (sexplist (sexppair sexppat sexpexp) (EL 1 args))) ++
      guard (nm = "Let" ∧ LENGTH args = 3)
            (lift Let (sexpopt odestSEXSTR (EL 0 args)) <*>
                      (sexpexp (EL 1 args)) <*>
                      (sexpexp (EL 2 args))) ++
      guard (nm = "Letrec" ∧ LENGTH args = 2)
            (lift2 Letrec
              (sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) (EL 0 args))
              (sexpexp (EL 1 args))) ++
      guard (nm = "Tannot" ∧ LENGTH args = 2)
            (lift2 Tannot
              (sexpexp (EL 0 args))
              (sexptype (EL 1 args))) ++
      guard (nm = "Lannot" ∧ LENGTH args = 2)
            (lift2 Lannot
              (sexpexp (EL 0 args))
              (sexplocn (EL 1 args)))
    od
`
  (WF_REL_TAC `measure sexp_size` >> simp[] >> rpt strip_tac
   >> TRY
     (rename1 `sxMEM sx0 (EL 1 args)` >>
       `sexp_size sx0 < sexp_size (EL 1 args)` by simp[sxMEM_sizelt] >>
       rw[] >> fs[sexp_size_def] >>
       `sexp_size (EL 1 args) < sexp_size s`
         by simp[dstrip_sexp_size, rich_listTheory.EL_MEM] >>
       simp[])
   >- (
     rw[] >>
     imp_res_tac dstrip_sexp_size >>
     imp_res_tac sxMEM_sizelt >>
     fs[sexp_size_def] >>
     `sexp_size a < sexp_size (HD args)` by decide_tac >>
     metis_tac[listTheory.EL,rich_listTheory.EL_MEM,DECIDE``0n < 2``,arithmeticTheory.LESS_TRANS])
   >> metis_tac[rich_listTheory.EL_MEM, listTheory.EL,
                DECIDE ``1n < 2 ∧ 0n < 2 ∧ 0n < 1 ∧ 2n < 3 ∧ 0n < 3 ∧ 1n < 3``,
                dstrip_sexp_size, sxMEM_sizelt, arithmeticTheory.LESS_TRANS])

val sexptype_def_def = Define`
  sexptype_def =
  sexplist
    (sexppair (sexplist odestSEXSTR)
      (sexppair odestSEXSTR
        (sexplist (sexppair odestSEXSTR (sexplist sexptype)))))`;

val sexpdec_def = Define`
  sexpdec s =
    do
      (nm, args) <- dstrip_sexp s;
      guard (nm = "Dlet" ∧ LENGTH args = 3)
            (lift Dlet (sexplocn (HD args)) <*>
                       (sexppat (EL 1 args)) <*>
                       (sexpexp (EL 2 args))) ++
      guard (nm = "Dletrec" ∧ LENGTH args = 2)
            (lift2 Dletrec (sexplocn (HD args))
                           (sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) (EL 1 args))) ++
      guard (nm = "Dtype" ∧ LENGTH args = 2)
            (lift2 Dtype (sexplocn (HD args)) (sexptype_def (EL 1 args))) ++
      guard (nm = "Dtabbrev" ∧ LENGTH args = 4)
            (lift Dtabbrev (sexplocn (EL 0 args)) <*>
                           (sexplist odestSEXSTR (EL 1 args)) <*>
                           (odestSEXSTR (EL 2 args)) <*>
                           (sexptype (EL 3 args)))
                            ++
      guard (nm = "Dexn" ∧ LENGTH args = 3)
            (lift Dexn (sexplocn (EL 0 args)) <*>
                       (odestSEXSTR (EL 1 args)) <*>
                       (sexplist sexptype (EL 2 args)))
    od`;

val sexpspec_def = Define`
  sexpspec s =
    do
       (nm, args) <- dstrip_sexp s ;
       if nm = "Sval" then
         guard (LENGTH args = 2)
               (lift2 Sval (odestSEXSTR (HD args)) (sexptype (EL 1 args)))
       else if nm = "Stype" then
         guard (LENGTH args = 1)
               (lift Stype (sexptype_def (HD args)))
       else if nm = "Stabbrev" then
         guard (LENGTH args = 3)
               (lift Stabbrev
                       (sexplist odestSEXSTR (HD args)) <*>
                       (odestSEXSTR (EL 1 args)) <*>
                       (sexptype (EL 2 args)))
       else if nm = "Stype_opq" then
         guard (LENGTH args = 2)
               (lift2 Stype_opq
                      (sexplist odestSEXSTR (EL 0 args))
                      (odestSEXSTR (EL 1 args)))
       else if nm = "Sexn" then
         guard (LENGTH args = 2)
               (lift2 Sexn (odestSEXSTR (EL 0 args))
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
             modN <- odestSEXSTR (HD args);
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

(* now the reverse: toSexp *)

val listsexp_def = Define`
  listsexp = FOLDR SX_CONS nil`;

val listsexp_11 = Q.store_thm("listsexp_11[simp]",
  `∀ l1 l2. listsexp l1 = listsexp l2 ⇔ l1 = l2`,
  Induct >> gen_tac >> cases_on `l2` >> fs[listsexp_def]);

val optsexp_def = Define`
  (optsexp NONE = SX_SYM "NONE") ∧
  (optsexp (SOME x) = listsexp [SX_SYM "SOME"; x])`;

val optsexp_11 = Q.store_thm("optsexp_11[simp]",
  `optsexp o1 = optsexp o2 ⇔ o1 = o2`,
  cases_on `o1` >> cases_on `o2` >> fs[optsexp_def, listsexp_def]);

val idsexp_def = Define`
  (idsexp (Short n) = listsexp [SX_SYM"Short"; SEXSTR n]) ∧
  (idsexp (Long ns n) = listsexp [SX_SYM"Long"; SEXSTR ns; idsexp n])`;

val idsexp_11 = Q.store_thm("idsexp_11[simp]",
  `∀ i1 i2. idsexp i1 = idsexp i2 ⇔ i1 = i2`,
  Induct >> gen_tac >> cases_on `i2` >> fs[idsexp_def]);

val tctorsexp_def = Define`
  (tctorsexp (TC_name id) = listsexp [SX_SYM "TC_name"; idsexp id]) ∧
  (tctorsexp TC_int = SX_SYM "TC_int") ∧
  (tctorsexp TC_char = SX_SYM "TC_char") ∧
  (tctorsexp TC_string = SX_SYM "TC_string") ∧
  (tctorsexp TC_ref = SX_SYM "TC_ref") ∧
  (tctorsexp TC_word8 = SX_SYM "TC_word8") ∧
  (tctorsexp TC_word64 = SX_SYM "TC_word64") ∧
  (tctorsexp TC_word8array = SX_SYM "TC_word8array") ∧
  (tctorsexp TC_fn = SX_SYM "TC_fn") ∧
  (tctorsexp TC_tup = SX_SYM "TC_tup") ∧
  (tctorsexp TC_exn = SX_SYM "TC_exn") ∧
  (tctorsexp TC_vector = SX_SYM "TC_vector") ∧
  (tctorsexp TC_array = SX_SYM "TC_array")`;

val tctorsexp_11 = Q.store_thm("tctorsexp_11[simp]",
  `∀ t1 t2. tctorsexp t1 = tctorsexp t2 ⇔ t1 = t2`,
  Induct >> gen_tac >> cases_on `t2` >> fs[tctorsexp_def, listsexp_def]);

val typesexp_def = tDefine"typesexp"`
  (typesexp (Tvar s) = listsexp [SX_SYM "Tvar"; SEXSTR s]) ∧
  (typesexp (Tvar_db n) = listsexp [SX_SYM "Tvar_db"; SX_NUM n]) ∧
  (typesexp (Tapp ts ct) = listsexp [SX_SYM "Tapp"; listsexp (MAP typesexp ts); tctorsexp ct])`
  (WF_REL_TAC`measure t_size` >>
   Induct_on`ts` >> simp[t_size_def] >>
   rw[] >> res_tac >> simp[] >>
   first_x_assum(qspec_then`ct`strip_assume_tac)>>
   decide_tac);

val typesexp_11 = Q.store_thm("typesexp_11[simp]",
  `∀t1 t2. typesexp t1 = typesexp t2 ⇔ t1 = t2`,
  ho_match_mp_tac (theorem"typesexp_ind")
  \\ simp[typesexp_def]
  \\ rpt conj_tac \\ simp[PULL_FORALL]
  \\ CONV_TAC(RESORT_FORALL_CONV List.rev)
  \\ Cases \\ simp[typesexp_def]
  \\ srw_tac[ETA_ss][EQ_IMP_THM]
  \\ metis_tac[MAP_EQ_MAP_IMP]);

val litsexp_def = Define`
  (litsexp (IntLit i) =
   if i < 0 then listsexp [SX_SYM "-"; SX_NUM (Num(-i))]
            else SX_NUM (Num i)) ∧
  (litsexp (Char c) = listsexp [SX_SYM "char"; SEXSTR [c]]) ∧
  (litsexp (StrLit s) = SEXSTR s) ∧
  (litsexp (Word8 w) = listsexp [SX_SYM "word8"; SX_NUM (w2n w)]) ∧
  (litsexp (Word64 w) = listsexp [SX_SYM "word64"; SX_NUM (w2n w)])`;

val litsexp_11 = Q.store_thm("litsexp_11[simp]",
  `∀l1 l2. litsexp l1 = litsexp l2 ⇔ l1 = l2`,
  Cases \\ Cases \\ rw[litsexp_def,EQ_IMP_THM,listsexp_def]
  \\ intLib.COOPER_TAC);

val patsexp_def = tDefine"patsexp"`
  (patsexp Pany = listsexp [SX_SYM "Pany"]) ∧
  (patsexp (Pvar s) = SEXSTR s) ∧
  (patsexp (Plit l) = listsexp [SX_SYM "Plit"; litsexp l]) ∧
  (patsexp (Pcon cn ps) = listsexp [SX_SYM "Pcon"; optsexp (OPTION_MAP idsexp cn); listsexp (MAP patsexp ps)]) ∧
  (patsexp (Pref p) = listsexp [SX_SYM "Pref"; patsexp p]) ∧
  (patsexp (Ptannot p t) = listsexp [SX_SYM "Ptannot" ; patsexp p; typesexp t])`
  (WF_REL_TAC`measure pat_size` >>
   simp [] >>
   Induct_on`ps`>>simp[pat_size_def] >>
   rw[] >> simp[] >> res_tac >>
   first_x_assum(qspec_then`cn`strip_assume_tac)>>
   decide_tac );

val patsexp_11 = Q.store_thm("patsexp_11[simp]",
  `∀p1 p2. patsexp p1 = patsexp p2 ⇔ p1 = p2`,
  ho_match_mp_tac (theorem"patsexp_ind")
  \\ rpt conj_tac \\ simp[PULL_FORALL]
  \\ CONV_TAC(RESORT_FORALL_CONV List.rev)
  \\ Cases \\ rw[patsexp_def,listsexp_def]
  \\ rw[EQ_IMP_THM]
  >- ( metis_tac[OPTION_MAP_INJ,idsexp_11] )
  \\ imp_res_tac FOLDR_SX_CONS_INJ
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac
  \\ simp[] \\ metis_tac[]);

val lopsexp_def = Define`
  (lopsexp And = SX_SYM "And") ∧
  (lopsexp Or = SX_SYM "Or")`;

val lopsexp_11 = Q.store_thm("lopsexp_11[simp]",
  `∀l1 l2. lopsexp l1 = lopsexp l2 ⇔ l1 = l2`,
  Cases \\ Cases \\ simp[lopsexp_def]);

val opsexp_def = Define`
  (opsexp (Opn Plus) = SX_SYM "OpnPlus") ∧
  (opsexp (Opn Minus) = SX_SYM "OpnMinus") ∧
  (opsexp (Opn Times) = SX_SYM "OpnTimes") ∧
  (opsexp (Opn Divide) = SX_SYM "OpnDivide") ∧
  (opsexp (Opn Modulo) = SX_SYM "OpnModulo") ∧
  (opsexp (Opb Lt) = SX_SYM "OpbLt") ∧
  (opsexp (Opb Gt) = SX_SYM "OpbGt") ∧
  (opsexp (Opb Leq) = SX_SYM "OpbLeq") ∧
  (opsexp (Opb Geq) = SX_SYM "OpbGeq") ∧
  (opsexp (Opw W8 Andw) = SX_SYM "Opw8Andw") ∧
  (opsexp (Opw W8 Orw) = SX_SYM "Opw8Orw") ∧
  (opsexp (Opw W8 Xor) = SX_SYM "Opw8Xor") ∧
  (opsexp (Opw W8 Add) = SX_SYM "Opw8Add") ∧
  (opsexp (Opw W8 Sub) = SX_SYM "Opw8Sub") ∧
  (opsexp (Opw W64 Andw) = SX_SYM "Opw64Andw") ∧
  (opsexp (Opw W64 Orw) = SX_SYM "Opw64Orw") ∧
  (opsexp (Opw W64 Xor) = SX_SYM "Opw64Xor") ∧
  (opsexp (Opw W64 Add) = SX_SYM "Opw64Add") ∧
  (opsexp (Opw W64 Sub) = SX_SYM "Opw64Sub") ∧
  (opsexp (Shift W8 Lsl n) = SX_CONS (SX_SYM "Shift8Lsl") (SX_NUM n)) ∧
  (opsexp (Shift W8 Lsr n) = SX_CONS (SX_SYM "Shift8Lsr") (SX_NUM n)) ∧
  (opsexp (Shift W8 Asr n) = SX_CONS (SX_SYM "Shift8Asr") (SX_NUM n)) ∧
  (opsexp (Shift W8 Ror n) = SX_CONS (SX_SYM "Shift8Ror") (SX_NUM n)) ∧
  (opsexp (Shift W64 Lsl n) = SX_CONS (SX_SYM "Shift64Lsl") (SX_NUM n)) ∧
  (opsexp (Shift W64 Lsr n) = SX_CONS (SX_SYM "Shift64Lsr") (SX_NUM n)) ∧
  (opsexp (Shift W64 Asr n) = SX_CONS (SX_SYM "Shift64Asr") (SX_NUM n)) ∧
  (opsexp (Shift W64 Ror n) = SX_CONS (SX_SYM "Shift64Ror") (SX_NUM n)) ∧
  (opsexp Equality = SX_SYM "Equality") ∧
  (opsexp (FP_cmp FP_Less) = SX_SYM "FPcmpFPLess") ∧
  (opsexp (FP_cmp FP_LessEqual) = SX_SYM "FPcmpFPLessEqual") ∧
  (opsexp (FP_cmp FP_Greater) = SX_SYM "FPcmpFPGreater") ∧
  (opsexp (FP_cmp FP_GreaterEqual) = SX_SYM "FPcmpFPGreaterEqual") ∧
  (opsexp (FP_cmp FP_Equal) = SX_SYM "FPcmpFPEqual") ∧
  (opsexp (FP_uop FP_Abs) = SX_SYM "FPuopFPAbs") ∧
  (opsexp (FP_uop FP_Neg) = SX_SYM "FPuopFPNeg") ∧
  (opsexp (FP_uop FP_Sqrt) = SX_SYM "FPuopFPSqrt") ∧
  (opsexp (FP_bop FP_Add) = SX_SYM "FPbopFPAdd") ∧
  (opsexp (FP_bop FP_Sub) = SX_SYM "FPbopFPSub") ∧
  (opsexp (FP_bop FP_Mul) = SX_SYM "FPbopFPMul") ∧
  (opsexp (FP_bop FP_Div) = SX_SYM "FPbopFPDiv") ∧
  (opsexp Opapp = SX_SYM "Opapp") ∧
  (opsexp Opassign = SX_SYM "Opassign") ∧
  (opsexp Opref = SX_SYM "Opref") ∧
  (opsexp Opderef = SX_SYM "Opderef") ∧
  (opsexp Aw8alloc = SX_SYM "Aw8alloc") ∧
  (opsexp Aw8sub = SX_SYM "Aw8sub") ∧
  (opsexp Aw8length = SX_SYM "Aw8length") ∧
  (opsexp Aw8update = SX_SYM "Aw8update") ∧
  (opsexp CopyStrStr = SX_SYM "CopyStrStr") ∧
  (opsexp CopyStrAw8 = SX_SYM "CopyStrAw8") ∧
  (opsexp CopyAw8Str = SX_SYM "CopyAw8Str") ∧
  (opsexp CopyAw8Aw8 = SX_SYM "CopyAw8Aw8") ∧
  (opsexp Ord = SX_SYM "Ord") ∧
  (opsexp Chr = SX_SYM "Chr") ∧
  (opsexp (WordFromInt W8) = SX_SYM "W8fromInt") ∧
  (opsexp (WordToInt W8) = SX_SYM "W8toInt") ∧
  (opsexp (WordFromInt W64) = SX_SYM "W64fromInt") ∧
  (opsexp (WordToInt W64) = SX_SYM "W64toInt") ∧
  (opsexp (Chopb Lt) = SX_SYM "ChopbLt") ∧
  (opsexp (Chopb Gt) = SX_SYM "ChopbGt") ∧
  (opsexp (Chopb Leq)= SX_SYM "ChopbLeq") ∧
  (opsexp (Chopb Geq)= SX_SYM "ChopbGeq") ∧
  (opsexp Implode = SX_SYM "Implode") ∧
  (opsexp Strsub = SX_SYM "Strsub") ∧
  (opsexp Strlen = SX_SYM "Strlen") ∧
  (opsexp Strcat = SX_SYM "Strcat") ∧
  (opsexp VfromList = SX_SYM "VfromList") ∧
  (opsexp Vsub = SX_SYM "Vsub") ∧
  (opsexp Vlength = SX_SYM "Vlength") ∧
  (opsexp Aalloc = SX_SYM "Aalloc") ∧
  (opsexp AallocEmpty = SX_SYM "AallocEmpty") ∧
  (opsexp Asub = SX_SYM "Asub") ∧
  (opsexp Alength = SX_SYM "Alength") ∧
  (opsexp Aupdate = SX_SYM "Aupdate") ∧
  (opsexp (FFI s) = SX_CONS (SX_SYM "FFI") (SEXSTR s))`;

(* TODO: This proof is not very scalable... *)
val opsexp_11 = Q.store_thm("opsexp_11[simp]",
  `∀o1 o2. opsexp o1 = opsexp o2 ⇔ o1 = o2`,
  Cases \\ TRY(Cases_on`o'`)
  \\ Cases \\ TRY(Cases_on`o'`)
  \\ simp[opsexp_def]
  \\ TRY (Cases_on`w`)
  \\ simp[opsexp_def]
  \\ TRY (Cases_on`s`)
  \\ simp[opsexp_def]
  \\ TRY (Cases_on`w'`)
  \\ simp[opsexp_def]
  \\ TRY (Cases_on`s'`)
  \\ simp[opsexp_def]
  \\ TRY (Cases_on`f`)
  \\ simp[opsexp_def]
  \\ TRY (Cases_on`f'`)
  \\ simp[opsexp_def]);

val locnsexp_def = Define`
  locnsexp (Locs (locn n1 n2 n3) (locn n4 n5 n6)) =
    listsexp (MAP SX_NUM [n1;n2;n3;n4;n5;n6])`;

val locnsexp_thm = Q.store_thm("locnsexp_thm[compute]",
  `locnsexp (Locs l1 l2) =
   listsexp [&(l1.row); &(l1.col); &(l1.offset);
             &(l2.row); &(l2.col); &(l2.offset)]`,
  Cases_on`l1` \\ Cases_on`l2` \\ rw[locnsexp_def]);

val locnsexp_11 = Q.store_thm("locnsexp_11[simp]",
  `∀l1 l2. locnsexp l1 = locnsexp l2 ⇔ l1 = l2`,
  Cases \\ Cases \\ rename [`locnsexp (Locs l1 l2) = locnsexp (Locs l3 l4)`] >>
  map_every Cases_on [`l1`, `l2`, `l3`, `l4`] >> rw[locnsexp_def]);

val expsexp_def = tDefine"expsexp"`
  (expsexp (Raise e) = listsexp [SX_SYM "Raise"; expsexp e]) ∧
  (expsexp (Handle e pes) = listsexp [SX_SYM "Handle"; expsexp e; listsexp (MAP (λ(p,e). SX_CONS (patsexp p) (expsexp e)) pes)]) ∧
  (expsexp (Lit l) = listsexp [SX_SYM "Lit"; litsexp l]) ∧
  (expsexp (Con cn es) = listsexp [SX_SYM "Con"; optsexp (OPTION_MAP idsexp cn); listsexp (MAP expsexp es)]) ∧
  (expsexp (Var id) = listsexp [SX_SYM "Var"; idsexp id]) ∧
  (expsexp (Fun x e) = listsexp [SX_SYM "Fun"; SEXSTR x; expsexp e]) ∧
  (expsexp (App op es) = listsexp [SX_SYM "App"; opsexp op; listsexp (MAP expsexp es)]) ∧
  (expsexp (Log lop e1 e2) = listsexp [SX_SYM "Log"; lopsexp lop; expsexp e1; expsexp e2]) ∧
  (expsexp (If e1 e2 e3) = listsexp [SX_SYM "If"; expsexp e1; expsexp e2; expsexp e3]) ∧
  (expsexp (Mat e pes) = listsexp [SX_SYM "Mat"; expsexp e; listsexp (MAP (λ(p,e). SX_CONS (patsexp p) (expsexp e)) pes)]) ∧
  (expsexp (Let so e1 e2) = listsexp [SX_SYM "Let"; optsexp (OPTION_MAP SEXSTR so); expsexp e1; expsexp e2]) ∧
  (expsexp (Letrec funs e) = listsexp
    [SX_SYM "Letrec";
     listsexp (MAP (λ(x,y,z). SX_CONS (SEXSTR x) (SX_CONS (SEXSTR y) (expsexp z))) funs);
     expsexp e]) ∧
  (expsexp (Tannot e t) = listsexp [SX_SYM "Tannot"; expsexp e; typesexp t]) ∧
  (expsexp (Lannot e loc) = listsexp [SX_SYM "Lannot"; expsexp e; locnsexp loc])`
  (WF_REL_TAC`measure exp_size` >>
   rpt conj_tac >> simp[] >>
   (Induct_on`pes` ORELSE Induct_on`es` ORELSE Induct_on`funs`) >>
   simp[exp_size_def] >> rw[] >> simp[exp_size_def] >>
   res_tac >>
   first_x_assum(strip_assume_tac o SPEC_ALL) >>
   decide_tac);

val expsexp_11 = Q.store_thm("expsexp_11[simp]",
  `∀e1 e2. expsexp e1 = expsexp e2 ⇒ e1 = e2`,
  ho_match_mp_tac (theorem"expsexp_ind")
  \\ rpt conj_tac \\ simp[PULL_FORALL]
  \\ CONV_TAC(RESORT_FORALL_CONV List.rev)
  \\ Cases \\ rw[expsexp_def]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ TRY(first_x_assum match_mp_tac \\ rw[FORALL_PROD])
  \\ rpt(pairarg_tac \\ fs[])
  \\ metis_tac[OPTION_MAP_INJ,idsexp_11,simpleSexpTheory.sexp_11,SEXSTR_11]);

val type_defsexp_def = Define`
  type_defsexp = listsexp o
    MAP (λ(xs,x,ls).
      SX_CONS (listsexp (MAP SEXSTR xs))
        (SX_CONS (SEXSTR x)
          (listsexp (MAP (λ(y,ts). SX_CONS (SEXSTR y) (listsexp (MAP typesexp ts))) ls))))`;

val type_defsexp_11 = Q.store_thm("type_defsexp_11[simp]",
  `∀t1 t2. type_defsexp t1 = type_defsexp t2 ⇔ t1 = t2`,
  rw[type_defsexp_def,EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac
  \\ rw[FORALL_PROD]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq
  \\ conj_tac
  >- (
    Q.ISPEC_THEN`SEXSTR`match_mp_tac INJ_MAP_EQ
    \\ simp[INJ_DEF] )
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac
  \\ rw[FORALL_PROD]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq
  \\ Q.ISPEC_THEN`typesexp`match_mp_tac INJ_MAP_EQ
  \\ simp[INJ_DEF]);

val decsexp_def = Define`
  (decsexp (Dlet locs p e) = listsexp [SX_SYM "Dlet"; locnsexp locs; patsexp p; expsexp e]) ∧
  (decsexp (Dletrec locs funs) =
     listsexp [SX_SYM "Dletrec"; locnsexp locs;
               listsexp (MAP (λ(f,x,e). SX_CONS (SEXSTR f) (SX_CONS (SEXSTR x) (expsexp e))) funs)]) ∧
  (decsexp (Dtype locs td) = listsexp [SX_SYM "Dtype"; locnsexp locs; type_defsexp td]) ∧
  (decsexp (Dtabbrev locs ns x t) = listsexp [SX_SYM "Dtabbrev"; locnsexp locs; listsexp (MAP SEXSTR ns); SEXSTR x; typesexp t]) ∧
  (decsexp (Dexn locs x ts) = listsexp [SX_SYM "Dexn"; locnsexp locs; SEXSTR x; listsexp (MAP typesexp ts)])`;

val decsexp_11 = Q.store_thm("decsexp_11[simp]",
  `∀d1 d2. decsexp d1 = decsexp d2 ⇔ d1 = d2`,
  Cases \\ Cases \\ rw[decsexp_def,EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ TRY (first_x_assum match_mp_tac \\ rw[])
  \\ rpt(pairarg_tac \\ fs[]));

val specsexp_def = Define`
  (specsexp (Sval x t) = listsexp [SX_SYM "Sval"; SEXSTR x; typesexp t]) ∧
  (specsexp (Stype t) = listsexp [SX_SYM "Stype"; type_defsexp t]) ∧
  (specsexp (Stabbrev ns x t) = listsexp [SX_SYM "Stabbrev"; listsexp (MAP SEXSTR ns); SEXSTR x; typesexp t]) ∧
  (specsexp (Stype_opq ns x) = listsexp [SX_SYM "Stype_opq"; listsexp (MAP SEXSTR ns); SEXSTR x]) ∧
  (specsexp (Sexn x ts) = listsexp [SX_SYM "Sexn"; SEXSTR x; listsexp (MAP typesexp ts)])`;

val specsexp_11 = Q.store_thm("specsexp_11[simp]",
  `∀s1 s2. specsexp s1 = specsexp s2 ⇔ s1 = s2`,
  Induct >> gen_tac >> cases_on `s2` >> fs[specsexp_def] >> rpt gen_tac >> simp[]
  \\ rw[EQ_IMP_THM]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac
  \\ rw[]);

val topsexp_def = Define`
  (topsexp (Tmod modN specopt declist) =
     listsexp [SX_SYM "Tmod"; SEXSTR modN; optsexp (OPTION_MAP (listsexp o MAP specsexp) specopt);
               listsexp (MAP decsexp declist)]) ∧
  (topsexp (Tdec dec) =
     listsexp [SX_SYM "Tdec"; decsexp dec])`;

val topsexp_11 = Q.store_thm("topsexp_11[simp]",
  `∀ t1 t2. topsexp t1 = topsexp t2 ⇔ t1 = t2`,
  Induct >> gen_tac >> cases_on `t2`
  \\ rw[topsexp_def,EQ_IMP_THM]
  \\ imp_res_tac(MP_CANON OPTION_MAP_INJ)
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac \\ rw[]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac \\ rw[]);

(* round trip *)

val odestSXSTR_SOME = Q.store_thm("odestSXSTR_SOME[simp]",
  `odestSXSTR s = SOME y ⇔ (s = SX_STR y)`,
  Cases_on`s`>>simp[odestSXSTR_def])

val odestSEXSTR_SOME = Q.store_thm("odestSEXSTR_SOME[simp]",
  `odestSEXSTR s = SOME y ⇔ (s = SEXSTR y)`,
  Cases_on`s`\\simp[odestSEXSTR_def,SEXSTR_def]
  \\ metis_tac[decode_encode_control,encode_decode_control]);

val odestSXSTR_SX_STR = Q.store_thm("odestSXSTR_SX_STR[simp]",
  `odestSXSTR (SX_STR s) = SOME s`,
  rw[odestSXSTR_def])

val odestSEXSTR_SEXSTR = Q.store_thm("odestSEXSTR_SEXSTR[simp]",
  `odestSEXSTR (SEXSTR s) = SOME s`,
  rw[odestSEXSTR_def]);

val odestSXNUM_SX_NUM = Q.store_thm("odestSXNUM_SX_NUM[simp]",
  `odestSXNUM (SX_NUM n) = SOME n`,
  EVAL_TAC)

val odestSXSYM_SX_SYM = Q.store_thm("odestSXSYM_SX_SYM[simp]",
  `odestSXSYM (SX_SYM s) = SOME s`,
  EVAL_TAC)

val odestSXNUM_SX_STR = Q.store_thm("odestSXNUM_SX_STR[simp]",
  `odestSXNUM (SX_STR s) = NONE`,
  EVAL_TAC)

val odestSXNUM_SEXSTR = Q.store_thm("odestSXNUM_SEXSTR[simp]",
  `odestSXNUM (SEXSTR s) = NONE`,
  EVAL_TAC)

val odestSXSTR_listsexp = Q.store_thm("odestSXSTR_listsexp[simp]",
  `odestSXSTR (listsexp l) = NONE`,
  Cases_on`l`>>EVAL_TAC)

val odestSEXSTR_listsexp = Q.store_thm("odestSEXSTR_listsexp[simp]",
  `odestSEXSTR (listsexp l) = NONE`,
  Cases_on`l`>>EVAL_TAC)

val odestSXNUM_listsexp = Q.store_thm("odestSXNUM_listsexp[simp]",
  `odestSXNUM (listsexp l) = NONE`,
  Cases_on`l`>>EVAL_TAC)

val dstrip_sexp_SX_STR = Q.store_thm("dstrip_sexp_SX_STR[simp]",
  `dstrip_sexp (SX_STR s) = NONE`,
  EVAL_TAC)

val dstrip_sexp_SEXSTR = Q.store_thm("dstrip_sexp_SEXSTR[simp]",
  `dstrip_sexp (SEXSTR s) = NONE`,
  EVAL_TAC)

val strip_sxcons_listsexp = Q.store_thm("strip_sxcons_listsexp[simp]",
  `strip_sxcons (listsexp ls) = SOME ls`,
  Induct_on`ls`>>rw[listsexp_def] >> simp[GSYM listsexp_def]);

val dstrip_sexp_listsexp = Q.store_thm("dstrip_sexp_listsexp[simp]",
  `(dstrip_sexp (listsexp ls) =
    case ls of (SX_SYM x::xs) => SOME (x,xs) | _ => NONE)`,
  BasicProvers.CASE_TAC >> rw[dstrip_sexp_def,listsexp_def] >>
  BasicProvers.CASE_TAC >> rw[GSYM listsexp_def]);

val sexplist_listsexp_matchable = Q.store_thm("sexplist_listsexp_matchable",
  `∀g gl. (∀x. MEM x l ⇒ f (g x) = SOME x) ∧ (gl = MAP g l) ⇒
   sexplist f (listsexp gl) = SOME l`,
  Induct_on`l` >> simp[listsexp_def,Once sexplist_def] >>
  simp[GSYM listsexp_def] >> metis_tac[]);

val sexplist_listsexp_rwt = Q.store_thm("sexplist_listsexp_rwt[simp]",
  `(∀x. MEM x l ⇒ f (g x) = SOME x) ⇒
   (sexplist f (listsexp (MAP g l)) = SOME l)`,
  metis_tac[sexplist_listsexp_matchable]);

val sexplist_listsexp_imp = Q.store_thm("sexplist_listsexp_imp",
  `sexplist f (listsexp l1) = SOME l2 ⇒
   ∀n. n < LENGTH l1 ⇒ f (EL n l1) = SOME (EL n l2)`,
  qid_spec_tac`l2`>>
  Induct_on`l1`>>simp[listsexp_def]>>simp[GSYM listsexp_def] >>
  simp[Once sexplist_def,PULL_EXISTS] >> rw[] >>
  Cases_on`n`>>simp[]);

val sexpopt_optsexp = Q.store_thm("sexpopt_optsexp[simp]",
  `(∀y. (x = SOME y) ⇒ (f (g y) = x)) ⇒
   (sexpopt f (optsexp (OPTION_MAP g x)) = SOME x)`,
  Cases_on`x`>>EVAL_TAC >> simp[]);

val sexpid_odestSEXSTR_idsexp = Q.store_thm("sexpid_odestSEXSTR_idsexp[simp]",
  `sexpid odestSEXSTR (idsexp i) = SOME i`,
  Induct_on `i` >> simp[idsexp_def] >>
  rw [Once sexpid_def]);

val sexptctor_tctorsexp = Q.store_thm("sexptctor_tctorsexp[simp]",
  `sexptctor (tctorsexp t) = SOME t`,
  Cases_on`t`>>simp[tctorsexp_def,sexptctor_def] >>
  simp[dstrip_sexp_def])

val sexptype_typesexp = Q.store_thm("sexptype_typesexp[simp]",
  `sexptype (typesexp t) = SOME t`,
  qid_spec_tac`t` >>
  ho_match_mp_tac type_ind >>
  conj_tac >- rw[Once sexptype_def,typesexp_def] >>
  conj_tac >- rw[Once sexptype_def,typesexp_def] >>
  Induct_on`l`>>rw[typesexp_def] >- (
    rw[Once sexptype_def,sexplist_listsexp_matchable] ) >> fs[] >>
  rw[Once sexptype_def] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  match_mp_tac sexplist_listsexp_matchable >>
  fs[typesexp_def] >> rw[] >> rw[] >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[]);

val exists_g_tac =
  (fn (g as (asl,w)) =>
    let
      val (x,b) = dest_exists w
      val tm = find_term (fn y => type_of x = type_of y andalso not (is_var y)) b
    in EXISTS_TAC tm end g)

val sexptype_def_type_defsexp = Q.store_thm("sexptype_def_type_defsexp[simp]",
  `sexptype_def (type_defsexp l) = SOME l`,
  Induct_on`l` >> rw[type_defsexp_def] >> rw[sexptype_def_def] >>
  match_mp_tac sexplist_listsexp_matchable >> simp[] >>
  exists_g_tac >>
  simp[] >>
  qx_gen_tac`p`>>PairCases_on`p` >> simp[] >>
  strip_tac >- (
    rw[] >>
    simp[sexppair_def] >>
    match_mp_tac sexplist_listsexp_matchable >>
    exists_g_tac >>
    simp[] >>
    qx_gen_tac`p`>>PairCases_on`p` >> simp[] >>
    simp[sexppair_def] ) >>
  fs[sexptype_def_def,type_defsexp_def] >>
  imp_res_tac sexplist_listsexp_imp >>
  fs[listTheory.MEM_EL] >>
  first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  pop_assum(assume_tac o SYM) >>
  simp[rich_listTheory.EL_MAP]);

val sexplit_litsexp = Q.store_thm("sexplit_litsexp[simp]",
  `sexplit (litsexp l) = SOME l`,
  Cases_on`l`>>simp[sexplit_def,litsexp_def]
  >- (
    rw[] >> intLib.ARITH_TAC ) >>
  ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_8] >>
  ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_64] >>
  ONCE_REWRITE_TAC[wordsTheory.w2n_lt] >>
  rw[]);

val sexppat_patsexp = Q.store_thm("sexppat_patsexp[simp]",
  `sexppat (patsexp p) = SOME p`,
  qid_spec_tac`p` >>
  ho_match_mp_tac pat_ind >>
  conj_tac >- simp[patsexp_def,Once sexppat_def] >>
  conj_tac >- simp[patsexp_def,Once sexppat_def] >>
  conj_tac >- simp[patsexp_def,Once sexppat_def] >>
  conj_tac >- (
    Induct >- simp[patsexp_def,Once sexppat_def,sexplist_listsexp_matchable] >>
    rw[] >> fs[] >>
    simp[patsexp_def,Once sexppat_def] >>
    match_mp_tac sexplist_listsexp_matchable >>
    srw_tac[boolSimps.ETA_ss][] >>
    qexists_tac`patsexp`>>simp[] >>
    fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  rw[] >> simp[patsexp_def,Once sexppat_def]);

val sexpop_opsexp = Q.store_thm("sexpop_opsexp[simp]",
  `sexpop (opsexp op) = SOME op`,
  Cases_on`op`>>rw[sexpop_def,opsexp_def]>>
  TRY(Cases_on`o'`>>rw[sexpop_def,opsexp_def]) >>
  TRY(Cases_on`w`>>rw[sexpop_def,opsexp_def]) >>
  TRY(Cases_on`s`>>rw[sexpop_def,opsexp_def,SEXSTR_def])>>
  TRY(Cases_on`f`>>rw[sexpop_def,opsexp_def,SEXSTR_def]));

val sexplop_lopsexp = Q.store_thm("sexplop_lopsexp[simp]",
  `sexplop (lopsexp l) = SOME l`,
  Cases_on`l`>>EVAL_TAC)

val sexplocn_locnsexp = Q.store_thm("sexplocn_locnsexp[simp]",
  `sexplocn (locnsexp l) = SOME l`,
  Cases_on `l` >> rename [`Locs l1 l2`] >>
  Cases_on`l1` \\ Cases_on`l2` \\ rw[locnsexp_def,sexplocn_def]);

val sexpexp_expsexp = Q.store_thm("sexpexp_expsexp[simp]",
  `sexpexp (expsexp e) = SOME e`,
  qid_spec_tac`e` >>
  ho_match_mp_tac exp_ind >> rw[] >>
  rw[expsexp_def] >> rw[Once sexpexp_def] >>
  match_mp_tac sexplist_listsexp_matchable >>
  exists_g_tac >> simp[] >>
  fs[listTheory.EVERY_MEM] >>
  qx_gen_tac`p`>>PairCases_on`p` >> simp[] >>
  simp[sexppair_def] >>
  rw[] >> res_tac >> fs[]);

val sexpdec_decsexp = Q.store_thm("sexpdec_decsexp[simp]",
  `sexpdec (decsexp d) = SOME d`,
  Cases_on`d`>>simp[decsexp_def,sexpdec_def]>>
  match_mp_tac sexplist_listsexp_matchable >>
  exists_g_tac >> simp[] >>
  qx_gen_tac`p`>>PairCases_on`p`>>rw[]>>
  simp[sexppair_def])

val sexpspec_specsexp = Q.store_thm("sexpspec_specsexp[simp]",
  `sexpspec (specsexp s) = SOME s`,
  Cases_on`s`>>simp[specsexp_def,sexpspec_def]);

val sexptop_topsexp = Q.store_thm("sexptop_topsexp",
  `sexptop (topsexp t) = SOME t`,
  Cases_on`t` >> simp[topsexp_def,sexptop_def]);

val sexpopt_SOME = Q.store_thm("sexpopt_SOME",
  `sexpopt f s = SOME opt ⇒
   ∃x. s = optsexp x ∧
       (case x of NONE => opt = NONE | SOME s => IS_SOME opt ∧ opt = f s)`,
  rw[sexpopt_def]
  \\ Cases_on`odestSXSYM s` \\ fs[dstrip_sexp_SOME] \\ rw[]
  \\ fs[odestSXSYM_def] \\ simp[EXISTS_OPTION, optsexp_def, listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[] \\ fs[] \\ rw[]
  \\ rename[`odestSXSYM s = SOME _`] >> Cases_on `s` >>
  fs[odestSXSYM_def, dstrip_sexp_def]);

val listsexp_MAP_EQ_f = Q.store_thm("listsexp_MAP_EQ_f",
  `(∀x. MEM x ls ⇒ f1 x = f2 x) ⇒
    listsexp (MAP f1 ls) = listsexp (MAP f2 ls)`,
  Induct_on`ls` >> simp[] >> fs[listsexp_def])

val sexplist_SOME = Q.store_thm("sexplist_SOME",
  `sexplist f s = SOME ls ⇒ ∃l. s = listsexp l ∧ MAP f l = MAP SOME ls`,
  map_every qid_spec_tac[`s`,`ls`] >>
  Induct >> rw[] >- (
    fs[Once sexplist_def] >>
    every_case_tac >> fs[listsexp_def] ) >>
  pop_assum mp_tac >>
  simp[Once sexplist_def] >>
  every_case_tac >> fs[] >> rw[] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  rw[] >>
  rw[listsexp_def,SimpRHS] >>
  simp[GSYM listsexp_def] >>
  qmatch_assum_rename_tac`f a = return h` >>
  qexists_tac`a::l` >> simp[listsexp_def] )

val sexppair_SOME = Q.store_thm("sexppair_SOME",
  `sexppair f1 f2 s = SOME p ⇒ ∃x y. f1 x = SOME (FST p) ∧ f2 y = SOME (SND p) ∧ s = SX_CONS x y`,
  rw[sexppair_def]
  \\ every_case_tac \\ fs[]);

val OPTION_CHOICE_EQ_SOME = Q.store_thm(
  "OPTION_CHOICE_EQ_SOME",
  `OPTION_CHOICE m1 m2 = SOME x ⇔
    m1 = SOME x ∨ m1 = NONE ∧ m2 = SOME x`,
  Cases_on `m1` >> simp[]);

val dstrip_sexp_EQ_SOME = Q.store_thm(
  "dstrip_sexp_EQ_SOME",
  `dstrip_sexp s = SOME (nm, args) ⇔
   ∃t. s = SX_CONS (SX_SYM nm) t ∧ strip_sxcons t = SOME args`,
  Cases_on`s` >> simp[dstrip_sexp_def] >> every_case_tac >>
  simp[] >> metis_tac[]);

val litsexp_sexplit = Q.store_thm("litsexp_sexplit",
  `∀s l. sexplit s = SOME l ⇒ litsexp l = s`,
  rw[sexplit_def]
  \\ reverse(Cases_on`odestSXNUM s`) \\ fs[]
  >- (
    rw[litsexp_def]
    \\ Cases_on`s` \\ fs[odestSXNUM_def] )
  \\ reverse(Cases_on`odestSEXSTR s`) \\ fs[]
  >- ( rw[litsexp_def])
  \\ pairarg_tac
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[]
  \\ fs[OPTION_CHOICE_EQ_SOME, dstrip_sexp_EQ_SOME] >>
  rw[litsexp_def, listsexp_def]
  \\ Cases_on`e1` \\ fs[odestSXNUM_def]);

val idsexp_sexpid_odestSEXSTR = Q.store_thm("idsexp_sexpid_odestSEXSTR",
  `∀y x. sexpid odestSEXSTR x = SOME y ⇒ x = idsexp y`,
  Induct
  \\ rw[Once sexpid_def]
  \\ fs[dstrip_sexp_SOME] \\ rw[]
  \\ fs[]
  \\ fs[OPTION_CHOICE_EQ_SOME]
  \\ rw[idsexp_def,listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[]
  \\ fs[]
  \\ fs[Once strip_sxcons_def]
  \\ every_case_tac \\ fs[]);

val strip_sxcons_NIL = Q.store_thm(
  "strip_sxcons_NIL[simp]",
  `strip_sxcons ⦇ ⦈ = SOME []`,
  simp[Once strip_sxcons_def]);

val strip_sxcons_SXCONS = Q.store_thm(
  "strip_sxcons_SXCONS[simp]",
  `strip_sxcons (SX_CONS s1 s2) = lift (CONS s1) (strip_sxcons s2)`,
  simp[Once strip_sxcons_def]);

val tctorsexp_sexptctor = Q.store_thm("tctorsexp_sexptctor",
  `sexptctor s = SOME t ⇒ tctorsexp t = s`,
  rw[sexptctor_def]
  \\ qmatch_assum_abbrev_tac`OPTION_CHOICE o1 o2 = _`
  \\ Cases_on`o1` \\ fs[markerTheory.Abbrev_def]
  >- (
    rfs[]
    \\ fs[OPTION_CHOICE_EQ_SOME] \\ rveq
    \\ rw[tctorsexp_def]
    \\ Cases_on`s` \\ fs[odestSXSYM_def, dstrip_sexp_def])
  \\ fs[dstrip_sexp_SOME]
  \\ rveq \\ fs[odestSXSYM_def]
  \\ rveq
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3]
  \\ rveq \\ fs[]
  \\ simp[tctorsexp_def,listsexp_def]
  \\ imp_res_tac idsexp_sexpid_odestSEXSTR
  \\ rw[]);

val typesexp_sexptype = Q.store_thm("typesexp_sexptype",
  `∀s t. sexptype s = SOME t ⇒ typesexp t = s`,
  ho_match_mp_tac(theorem"sexptype_ind")
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[Once sexptype_def]
  \\ fs[dstrip_sexp_SOME,PULL_EXISTS]
  \\ rw[]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ rename1`guard (nm = "Tvar" ∧ _) _`
  \\ reverse (Cases_on `nm ∈ {"Tvar"; "Tvar_db"; "Tapp"}`) >- fs[]
  \\ pop_assum mp_tac >> simp[]
  \\ strip_tac \\ fs[typesexp_def, listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3, PULL_EXISTS]
  \\ rw[] \\ fs[]
  \\ TRY(rename1`odestSXNUM e` \\ Cases_on`e`\\fs[odestSXNUM_def])
  \\ fs[GSYM listsexp_def]
  \\ imp_res_tac tctorsexp_sexptctor \\ simp[]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rfs[EL_MAP]
  \\ rpt strip_tac \\ res_tac
  \\ first_x_assum(MATCH_MP_TAC o MP_CANON)
  \\ simp[sxMEM_def]
  \\ metis_tac[MEM_EL]);

val patsexp_sexppat = Q.store_thm("patsexp_sexppat",
  `∀s p. sexppat s = SOME p ⇒ patsexp p = s`,
  ho_match_mp_tac (theorem"sexppat_ind")
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[Once sexppat_def]
  \\ fs[OPTION_CHOICE_EQ_SOME, patsexp_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[dstrip_sexp_SOME, OPTION_CHOICE_EQ_SOME] >>
  rw[patsexp_def, listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3]
  \\ rw[] \\ fs[]
  >- metis_tac[litsexp_sexplit]
  >- metis_tac[litsexp_sexplit]
  \\ imp_res_tac typesexp_sexptype
  \\ fs[odestSEXSTR_def] \\ rveq
  \\ imp_res_tac sexpopt_SOME \\ rw[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs[optsexp_def, listsexp_def, sexpopt_def, odestSXSYM_def,
        dstrip_sexp_def]
  \\ rpt (pairarg_tac >> fs[])
  \\ simp[idsexp_sexpid_odestSEXSTR]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ rw[listsexp_def] \\ AP_TERM_TAC
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rfs[EL_MAP] \\ rw[]
  \\ first_x_assum(match_mp_tac o MP_CANON)
  \\ simp[]
  \\ simp[sxMEM_def]
  \\ metis_tac[MEM_EL]);

val opsexp_sexpop = Q.store_thm("opsexp_sexpop",
  `sexpop s = SOME p ⇒ opsexp p = s`,
  Cases_on`s` \\ rw[sexpop_def] \\ rw[opsexp_def]
  \\ match1_tac(mg.aub`s_:sexp`,(fn(a,t)=>if is_var(t"s") then Cases_on`^(t"s")`\\fs[sexpop_def] else NO_TAC))
  \\ match1_tac(mg.aub`s_:sexp`,(fn(a,t)=>if is_var(t"s") then Cases_on`^(t"s")`\\fs[sexpop_def] else NO_TAC))
  \\ pop_assum mp_tac
  \\ rpt IF_CASES_TAC \\ rw[]
  \\ rw[opsexp_def, GSYM encode_decode_control]);

val lopsexp_sexplop = Q.store_thm("lopsexp_sexplop",
  `sexplop s = SOME z ⇒ lopsexp z = s`,
  Cases_on`s` \\ rw[sexplop_def] \\ rw[lopsexp_def]);

val locnsexp_sexplocn = Q.store_thm("locnsexp_sexplocn",
  `sexplocn s = SOME z ⇒ locnsexp z = s`,
  Cases_on`z` \\ rename [`Locs l1 l2`] >>
  Cases_on`l1` \\ Cases_on `l2`
  \\ rw[sexplocn_def,locnsexp_def]
  \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
  \\ fs[Once strip_sxcons_def]
  \\ simp[listsexp_def]
  \\ rename [`⦇h1; h2; h3; h4; h5; h6⦈`]
  \\ map_every (fn q => Cases_on q >> fs[odestSXNUM_def])
       [`h1`, `h2`, `h3`, `h4`, `h5`, `h6`]);

val expsexp_sexpexp = Q.store_thm("expsexp_sexpexp",
  `∀s e. sexpexp s = SOME e ⇒ expsexp e = s`,
  ho_match_mp_tac (theorem"sexpexp_ind") >>
  simp[OPTION_GUARD_EQ_THM, quantHeuristicsTheory.LIST_LENGTH_3, PULL_EXISTS,
       dstrip_sexp_SOME]
  \\ rpt gen_tac \\ strip_tac \\ gen_tac
  \\ simp[Once sexpexp_def, EXISTS_PROD, dstrip_sexp_EQ_SOME, PULL_EXISTS]
  \\ rpt gen_tac
  \\ rename1 `guard (nm = "Raise" ∧ _) _`
  \\ reverse (Cases_on `nm ∈ {"Raise"; "Handle"; "Lit"; "Con"; "Var"; "Fun";
                              "App"; "Log"; "If"; "Mat"; "Let"; "Letrec";
                              "Lannot"; "Tannot" }`)
  \\ pop_assum mp_tac
  \\ simp[]
  \\ rw[]
  \\ simp[expsexp_def]
  \\ rw[]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[]
  \\ fs[] \\ rw[]
  \\ fs[listsexp_def] \\ fs[GSYM listsexp_def] \\ rpt conj_tac
  \\ imp_res_tac typesexp_sexptype
  \\ imp_res_tac locnsexp_sexplocn
  >- (imp_res_tac sexplist_SOME \\ rw[]
      \\ fs[LIST_EQ_REWRITE, EL_MAP]
      \\ rfs[EL_MAP] \\ gen_tac \\ pairarg_tac \\ strip_tac \\ simp[]
      \\ res_tac
      \\ imp_res_tac sexppair_SOME \\ fs[] \\ rfs[] \\ conj_tac
      >- (imp_res_tac patsexp_sexppat \\ rfs[])
      \\ fs[sxMEM_def]
      \\ metis_tac[MEM_EL])
  >- imp_res_tac litsexp_sexplit
  >- (imp_res_tac sexpopt_SOME \\ rw[] \\ every_case_tac \\ fs[]
      \\ fs[sexpopt_def, optsexp_def, listsexp_def, odestSXSYM_def,
            IS_SOME_EXISTS, dstrip_sexp_def] \\ rfs[]
      \\ fs[strip_sxcons_def]
      \\ rw[]
      \\ imp_res_tac idsexp_sexpid_odestSEXSTR)
  >- (imp_res_tac sexplist_SOME >> rw[] >>
      fs[LIST_EQ_REWRITE, EL_MAP] >> rfs[EL_MAP, sxMEM_def] >>
      metis_tac[MEM_EL])
  >- (imp_res_tac idsexp_sexpid_odestSEXSTR >> metis_tac[])
  >- (imp_res_tac opsexp_sexpop)
  >- (imp_res_tac sexplist_SOME >> rw[] >>
      fs[LIST_EQ_REWRITE, EL_MAP] >> rfs[EL_MAP, sxMEM_def] >>
      metis_tac[MEM_EL])
  >- (rfs[] >> fs[Once strip_sxcons_def] >> every_case_tac >> fs[] >>
      rw[] >> fs[OPTION_APPLY_MAP3] >> rw[] >>
      simp[expsexp_def, listsexp_def] >> imp_res_tac lopsexp_sexplop)
  >- (rfs[] >> fs[Once strip_sxcons_def] >> every_case_tac >> fs[] >>
      rw[] >> fs[OPTION_APPLY_MAP3] >> rw[] >>
      simp[expsexp_def, listsexp_def])
  >- (imp_res_tac sexplist_SOME \\ rw[]
      \\ fs[LIST_EQ_REWRITE, EL_MAP]
      \\ rfs[EL_MAP] \\ gen_tac \\ pairarg_tac \\ strip_tac \\ simp[]
      \\ res_tac
      \\ imp_res_tac sexppair_SOME \\ fs[] \\ rfs[] \\ conj_tac
      >- (imp_res_tac patsexp_sexppat \\ rfs[])
      \\ fs[sxMEM_def] \\ metis_tac[MEM_EL])
  >- (rfs[] >> fs[Once strip_sxcons_def] >> every_case_tac >> fs[] >> rw[] >>
      fs[OPTION_APPLY_MAP3] >> rw[] >> simp[expsexp_def, listsexp_def] >>
      imp_res_tac sexpopt_SOME >> every_case_tac >> fs[] >> rw[] >>
      fs[IS_SOME_EXISTS])
  >- (imp_res_tac sexplist_SOME \\ rw[]
      \\ fs[LIST_EQ_REWRITE, EL_MAP]
      \\ rfs[EL_MAP] \\ gen_tac \\ pairarg_tac >> strip_tac >> simp[]
      \\ res_tac
      \\ imp_res_tac sexppair_SOME \\ fs[] \\ rfs[] \\ rw[]
      \\ imp_res_tac sexppair_SOME \\ fs[] \\ rfs[] \\ rw[]
      \\ fs[sxMEM_def] \\ metis_tac[MEM_EL]));

val type_defsexp_sexptype_def = Q.store_thm("type_defsexp_sexptype_def",
  `sexptype_def s = SOME x ⇒ type_defsexp x = s`,
  rw[sexptype_def_def,type_defsexp_def]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rw[] \\ rfs[EL_MAP]
  \\ res_tac
  \\ imp_res_tac sexppair_SOME
  \\ imp_res_tac sexppair_SOME
  \\ fs[] \\ rveq \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rw[] \\ rfs[EL_MAP]
  \\ res_tac
  \\ imp_res_tac sexppair_SOME
  \\ fs[] \\ rveq \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rw[] \\ rfs[EL_MAP]
  \\ metis_tac[typesexp_sexptype]);

val decsexp_sexpdec = Q.store_thm("decsexp_sexpdec",
  `sexpdec s = SOME d ⇒ decsexp d = s`,
  rw[sexpdec_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[dstrip_sexp_SOME]
  \\ rpt var_eq_tac
  \\ rename1 `guard (nm = _ ∧ _) _`
  \\ Cases_on `nm ∈ {"Dlet"; "Dletrec"; "Dtype"; "Dtabbrev"; "Dexn"}`
  \\ fs[]
  \\ fs[decsexp_def, quantHeuristicsTheory.LIST_LENGTH_3,
        quantHeuristicsTheory.LIST_LENGTH_4, listsexp_def]
  \\ rveq \\ fs[OPTION_APPLY_MAP3,OPTION_APPLY_MAP4]
  \\ rveq \\ rw[decsexp_def]
  \\ rveq \\ fs[listsexp_def] \\ fs[GSYM listsexp_def]
  \\ imp_res_tac patsexp_sexppat
  \\ imp_res_tac expsexp_sexpexp
  \\ imp_res_tac sexplist_SOME
  \\ imp_res_tac type_defsexp_sexptype_def
  \\ imp_res_tac typesexp_sexptype
  \\ imp_res_tac locnsexp_sexplocn
  \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rw[] \\ rfs[EL_MAP]
  \\ res_tac
  \\ imp_res_tac sexppair_SOME
  \\ imp_res_tac typesexp_sexptype
  \\ fs[] \\ rveq \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac sexppair_SOME
  \\ fs[] \\ rveq \\ fs[]
  \\ imp_res_tac expsexp_sexpexp);

val specsexp_sexpspec = Q.store_thm("specsexp_sexpspec",
  `sexpspec s = SOME z ⇒ specsexp z = s`,
  rw[sexpspec_def]
  \\ fs[dstrip_sexp_SOME]
  \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[]
  \\ fs[OPTION_APPLY_MAP3,quantHeuristicsTheory.LIST_LENGTH_3]
  \\ rw[] \\ fs[]
  \\ rw[specsexp_def,listsexp_def]
  \\ rw[GSYM listsexp_def]
  \\ imp_res_tac typesexp_sexptype
  \\ imp_res_tac type_defsexp_sexptype_def
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE]
  \\ rw[] \\ rfs[EL_MAP]
  \\ metis_tac[typesexp_sexptype]);

val topsexp_sexptop = Q.store_thm("topsexp_sexptop",
  `sexptop s = SOME t ⇒ topsexp t = s`,
  Cases_on`t` >> simp[topsexp_def,sexptop_def,dstrip_sexp_SOME,PULL_EXISTS] >>
  rw[] >>
  fs[listsexp_def, quantHeuristicsTheory.LIST_LENGTH_3] >> rveq >> fs[] >>
  rw[decsexp_sexpdec] >> simp[GSYM listsexp_def] >| [
    imp_res_tac sexpopt_SOME >> every_case_tac >> rw[] >> fs[IS_SOME_EXISTS],
    ALL_TAC
  ] >>
  imp_res_tac sexplist_SOME >>
  rveq >> simp[] >>
  fs[LIST_EQ_REWRITE, EL_MAP] >> rfs[EL_MAP] >> rpt strip_tac >> res_tac >>
  metis_tac[specsexp_sexpspec, decsexp_sexpdec]);

(* valid sexps *)

val SEXSTR_valid = Q.store_thm("SEXSTR_valid[simp]",
  `valid_sexp (SEXSTR s)`,
  rw[SEXSTR_def,EVERY_isPrint_encode_control]);

val listsexp_valid = Q.store_thm("listsexp_valid",
  `∀ls. EVERY valid_sexp ls ⇒ valid_sexp (listsexp ls)`,
  Induct \\ simp[listsexp_def] \\ simp[GSYM listsexp_def]
  \\ EVAL_TAC);

val idsexp_valid = Q.store_thm("idsexp_valid[simp]",
  `∀i. valid_sexp (idsexp i)`,
  Induct \\ simp[idsexp_def] >>
  rw []
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ EVAL_TAC);

val tctorsexp_valid = Q.store_thm("tctorsexp_valid[simp]",
  `∀t. valid_sexp (tctorsexp t)`,
  Cases \\ simp[tctorsexp_def]
  \\ TRY(match_mp_tac listsexp_valid)
  \\ simp[]
  \\ EVAL_TAC);

val typesexp_valid = Q.store_thm("typesexp_valid[simp]",
  `∀t. valid_sexp (typesexp t)`,
  ho_match_mp_tac(theorem"typesexp_ind")
  \\ rw[typesexp_def]
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ rpt conj_tac
  \\ TRY (match_mp_tac listsexp_valid)
  \\ simp[EVERY_MAP,EVERY_MEM]
  \\ EVAL_TAC);

val litsexp_valid = Q.store_thm("litsexp_valid[simp]",
  `∀l. valid_sexp (litsexp l)`,
  Cases \\ rw[litsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[] \\ EVAL_TAC);

val optsexp_valid = Q.store_thm("optsexp_valid",
  `∀x. (∀y. x = SOME y ⇒ valid_sexp y) ⇒ valid_sexp (optsexp x)`,
  Cases \\ rw[optsexp_def]
  \\ TRY(match_mp_tac listsexp_valid) \\ rw[]
  \\ EVAL_TAC);

val patsexp_valid = Q.store_thm("patsexp_valid[simp]",
  `∀p. valid_sexp (patsexp p)`,
  ho_match_mp_tac(theorem"patsexp_ind")
  \\ rw[patsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY (match_mp_tac optsexp_valid \\ rw[] \\ rw[])
  \\ TRY (match_mp_tac listsexp_valid \\ simp[EVERY_MAP,EVERY_MEM])
  \\ EVAL_TAC);

val type_defsexp_valid = Q.store_thm("type_defsexp_valid[simp]",
  `∀t. valid_sexp (type_defsexp t)`,
  rw[type_defsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
  \\ pairarg_tac \\ rw[]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
  \\ pairarg_tac \\ rw[]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]);

val opsexp_valid = Q.store_thm("opsexp_valid[simp]",
  `∀op. valid_sexp (opsexp op)`,
  Cases \\ simp[opsexp_def]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ TRY(Cases_on`o'`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`w`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`s`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`f`) \\ simp[opsexp_def]
  \\ EVAL_TAC);

val lopsexp_valid = Q.store_thm("lopsexp_valid[simp]",
  `∀l. valid_sexp (lopsexp l)`,
  Cases \\ simp[lopsexp_def]
  \\ EVAL_TAC);

val locnsexp_valid = Q.store_thm("locnsexp_valid[simp]",
  `∀l. valid_sexp (locnsexp l)`,
  Cases \\ rename [`Locs l1 l2`] >> Cases_on `l1` \\ Cases_on `l2` \\ EVAL_TAC);

val expsexp_valid = Q.store_thm("expsexp_valid[simp]",
  `∀e. valid_sexp (expsexp e)`,
  ho_match_mp_tac(theorem"expsexp_ind")
  \\ rw[expsexp_def]
  \\ TRY(match_mp_tac listsexp_valid)
  \\ rw[]
  \\ TRY(EVAL_TAC \\ NO_TAC)
  \\ TRY(match_mp_tac optsexp_valid \\ rw[] \\ rw[])
  \\ TRY(match_mp_tac listsexp_valid \\ simp[EVERY_MAP,EVERY_MEM])
  \\ simp[FORALL_PROD]
  \\ first_x_assum MATCH_ACCEPT_TAC);

val decsexp_valid = Q.store_thm("decsexp_valid[simp]",
  `∀d. valid_sexp (decsexp d)`,
  Cases \\ simp[decsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP,EVERY_MEM]
  \\ simp[FORALL_PROD]);

val specsexp_valid = Q.store_thm("specsexp_valid[simp]",
  `∀s. valid_sexp (specsexp s)`,
  Cases \\ simp[specsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY(EVAL_TAC \\ NO_TAC)
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP]);

val topsexp_valid = Q.store_thm("topsexp_valid[simp]",
  `∀t. valid_sexp (topsexp t)`,
  Cases \\ simp[topsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY(EVAL_TAC \\ NO_TAC)
  \\ TRY(match_mp_tac optsexp_valid \\ rw[])
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP,EVERY_MEM]);

val _ = export_theory();
