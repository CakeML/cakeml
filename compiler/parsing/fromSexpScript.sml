(*
  Definitions of functions for conversion between an S-expression encoding of
  the CakeML abstract syntax and the abstract syntax type itself.

  The S-expressions are parsed as *per* the PEG in HOL’s
  `examples/formal-language/context-free/simpleSexpPEGScript.sml`.
*)

open preamble match_goal
open simpleSexpTheory astTheory

val _ = new_theory "fromSexp";
val _ = set_grammar_ancestry ["simpleSexp", "ast", "location","fpSem"]
val _ = option_monadsyntax.temp_add_option_monadsyntax()

(* TODO: this is duplicated in parserProgTheory *)
val monad_unitbind_assert = Q.prove(
  `!b x. monad_unitbind (assert b) x = if b then x else NONE`,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);

val _ = temp_overload_on ("lift", ``OPTION_MAP``)

(* TODO: move*)

Theorem OPTION_APPLY_MAP3
  `OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z = SOME r ⇔
   ∃a b c. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ f a b c = r`
  (Cases_on`x`\\simp[] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`y`\\fs[]);

Theorem OPTION_APPLY_MAP4
  `OPTION_APPLY (OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z ) t= SOME r ⇔
   ∃a b c d. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ t = SOME d /\ f a b c d= r`
  (Cases_on`x`\\simp[] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`y`\\fs[] \\ Cases_on`z`\\fs[]);

Theorem FOLDR_SX_CONS_INJ
  `∀l1 l2. FOLDR SX_CONS nil l1 = FOLDR SX_CONS nil l2 ⇔ l1 = l2`
  (Induct \\ simp[]
  >- ( Induct \\ simp[] )
  \\ gen_tac \\ Induct \\ simp[]);

Theorem strip_sxcons_11
  `∀s1 s2 x. strip_sxcons s1 = SOME x ∧ strip_sxcons s2 = SOME x ⇒ s1 = s2`
  (ho_match_mp_tac simpleSexpTheory.strip_sxcons_ind
  \\ ntac 4 strip_tac
  \\ simp[Once simpleSexpTheory.strip_sxcons_def]
  \\ CASE_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]
  \\ pop_assum mp_tac
  \\ simp[Once simpleSexpTheory.strip_sxcons_def]
  \\ CASE_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]);

Theorem dstrip_sexp_size
  `∀s sym args. dstrip_sexp s = SOME (sym, args) ⇒
                 ∀e. MEM e args ⇒ sexp_size e < sexp_size s`
  (Induct >> simp[dstrip_sexp_def, sexp_size_def] >>
  rename1 `sexp_CASE sxp` >> Cases_on `sxp` >> simp[] >> rpt strip_tac >>
  rename1 `MEM sxp0 sxpargs` >> rename1 `strip_sxcons sxp'` >>
  `sxMEM sxp0 sxp'` by metis_tac[sxMEM_def] >> imp_res_tac sxMEM_sizelt >>
  simp[]);

Theorem dstrip_sexp_SOME
  `dstrip_sexp s = SOME x ⇔
   ∃sym sa args. s =
     SX_CONS (SX_SYM sym) sa ∧
     strip_sxcons sa = SOME args ∧
     (x = (sym,args))`
  (Cases_on`s`>>simp[dstrip_sexp_def]>>
  every_case_tac>>simp[])

Theorem strip_sxcons_SOME_NIL[simp]
  `strip_sxcons s = SOME [] ⇔ s = nil`
  (rw[Once strip_sxcons_def] >>
  every_case_tac >> simp[])

Theorem strip_sxcons_EQ_CONS[simp]
  `strip_sxcons s = SOME (h::t) ⇔
     ∃s0. s = SX_CONS h s0 ∧ strip_sxcons s0 = SOME t`
  (simp[Once strip_sxcons_def] >> every_case_tac >> simp[] >>
  metis_tac[]);

val type_ind =
  (TypeBase.induction_of``:ast_t``)
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

val dec_ind =
  (TypeBase.induction_of``:dec``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`

(* end TODO *)

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

Theorem EVERY_isPrint_encode_control
  `∀ls. EVERY isPrint (encode_control ls)`
  (Induct \\ rw[encode_control_def]
  \\ TRY (qmatch_rename_tac`isPrint _` \\ EVAL_TAC)
  \\ metis_tac[EVERY_isHexDigit_num_to_hex_string,MONO_EVERY,isHexDigit_isPrint,EVERY_CONJ]);

Theorem decode_encode_control[simp]
  `∀ls. decode_control (encode_control ls) = SOME ls`
  (Induct \\ rw[encode_control_def,decode_control_def]
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

Theorem isAlpha_isUpper_isLower
  `isAlpha c ⇒ (isUpper c ⇎ isLower c)`
  (simp[isAlpha_def, isUpper_def, isLower_def]);

Theorem isLower_isAlpha
  `isLower c ⇒ isAlpha c`
  (simp[isLower_def, isAlpha_def]);

open ASCIInumbersTheory numposrepTheory
Theorem encode_decode_control
  `∀ls r. decode_control ls = SOME r ⇒ ls = encode_control r`
  (ho_match_mp_tac (theorem"decode_control_ind")
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

Theorem SEXSTR_11[simp]
  `SEXSTR s1 = SEXSTR s2 ⇔ s1 = s2`
  (rw[SEXSTR_def]
  \\ metis_tac[decode_encode_control,SOME_11]);

Theorem SEXSTR_distinct[simp]
  `(SEXSTR s ≠ SX_SYM sym) ∧
   (SEXSTR s ≠ SX_NUM num) ∧
   (SEXSTR s ≠ SX_CONS a d) ∧
   ((SEXSTR s = SX_STR s') ⇔ s' = encode_control s)`
  (rw[SEXSTR_def,EQ_IMP_THM]);

val odestSEXSTR_def = Define`
  (odestSEXSTR (SX_STR s) = decode_control s) ∧
  (odestSEXSTR _ = NONE)`;

Theorem encode_control_remove
  `∀s. EVERY isPrint s ∧ #"\\" ∉ set s ⇒ encode_control s = s`
  (Induct \\ simp[encode_control_def]);

Theorem SEXSTR_remove
  `EVERY isPrint s ∧ #"\\" ∉ set s ⇒ SEXSTR s = SX_STR s`
  (rw[SEXSTR_def,encode_control_remove]);

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

Theorem sexppair_CONG[defncong]
  `∀s1 s2 p1 p1' p2 p2'.
       s1 = s2 ∧
       (∀s. (∃s'. s2 = SX_CONS s s') ⇒ p1 s = p1' s) ∧
       (∀s. (∃s'. s2 = SX_CONS s' s) ⇒ p2 s = p2' s)
      ⇒
       sexppair p1 p2 s1 = sexppair p1' p2' s2`
  (simp[] >> Cases >> simp[sexppair_def])


Theorem strip_sxcons_FAIL_sexplist_FAIL
  `∀s. (strip_sxcons s = NONE) ⇒ (sexplist p s = NONE)`
  (Induct >> simp[Once strip_sxcons_def, Once sexplist_def] >>
  metis_tac[TypeBase.nchotomy_of ``:α option``]);

Theorem monad_bind_FAIL
  `monad_bind m1 (λx. fail) = fail`
  (Cases_on `m1` >> simp[]);

Theorem monad_unitbind_CONG[defncong]
  `∀m11 m21 m12 m22.
      m11 = m12 ∧ (m12 = SOME () ⇒ m21 = m22) ⇒
      monad_unitbind m11 m21 = monad_unitbind m12 m22`
  (simp[] >> rpt gen_tac >> rename1 `m12 = SOME ()` >>
  Cases_on `m12` >> simp[]);

Theorem sexplist_CONG[defncong]
  `∀s1 s2 p1 p2.
      (s1 = s2) ∧ (∀e. sxMEM e s2 ⇒ p1 e = p2 e) ⇒
      (sexplist p1 s1 = sexplist p2 s2)`
  (simp[sxMEM_def] >> Induct >> dsimp[Once strip_sxcons_def]
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

val sexptype_def = tDefine "sexptype" `
  sexptype s =
    do
       (s, args) <- dstrip_sexp s ;
       (guard (s = "Atvar" ∧ LENGTH args = 1)
              (lift Atvar (odestSEXSTR (EL 0 args))) ++
        guard (s = "Atfun" ∧ LENGTH args = 2)
              (lift2 Atfun (sexptype (EL 0 args)) (sexptype (EL 1 args))) ++
        guard (s = "Attup" ∧ LENGTH args = 1)
              (lift Attup (sexplist sexptype (EL 0 args))) ++
        guard (s = "Atapp" ∧ LENGTH args = 2)
              (lift2 Atapp (sexplist sexptype (EL 0 args))
                     (sexpid odestSEXSTR (EL 1 args))))
    od `
  (wf_rel_tac `measure sexp_size` >> rw[]
   \\ fs[LENGTH_EQ_NUM_compute] \\ rw[] \\ fs[]
   \\ metis_tac[sxMEM_sizelt,dstrip_sexp_size,MEM,LESS_TRANS]);

(* translator friendly version for bootstrapping *)
val sexptype_alt_def = tDefine"sexptype_alt"`
 (sexptype_alt s =
    case dstrip_sexp s of
    | NONE => NONE
    | SOME (nm,args) =>
      if nm = "Atvar" ∧ LENGTH args = 1 then
        OPTION_MAP Atvar (odestSEXSTR (EL 0 args))
      else if nm = "Atfun" ∧ LENGTH args = 2 then
        OPTION_MAP2 Atfun (sexptype_alt (EL 0 args)) (sexptype_alt (EL 1 args))
      else if nm = "Attup" ∧ LENGTH args = 1 then
        OPTION_MAP Attup (sexptype_list (EL 0 args))
      else if nm = "Atapp" ∧ LENGTH args = 2 then
        OPTION_MAP2 Atapp (sexptype_list (EL 0 args)) (sexpid odestSEXSTR (EL 1 args))
      else NONE) ∧
 (sexptype_list s =
    case s of
    | SX_SYM nm => if nm = "nil" then SOME [] else NONE
    | SX_CONS a d =>
      (case sexptype_alt a of
       | NONE => NONE
       | SOME h =>
       case sexptype_list d of
       | NONE => NONE
       | SOME t => SOME (h::t))
    | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size) (λx. case x of INL y => y | INR y => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexptype_alt_ind = theorem"sexptype_alt_ind";

Theorem sexptype_alt_intro
  `(∀s. sexptype s = sexptype_alt s) ∧ (∀s. sexptype_list s = sexplist sexptype s)`
  (ho_match_mp_tac sexptype_alt_ind \\ rw[]
  >- (
    rw[Once sexptype_alt_def,Once sexptype_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    simp[monad_unitbind_assert] \\
    srw_tac[ETA_ss][] )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT2 sexptype_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] ));

Theorem sexptype_alt_intro1
  `sexptype = sexptype_alt ∧ sexplist sexptype = sexptype_list`
  (rw[FUN_EQ_THM,sexptype_alt_intro]);

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

(* translator friendly version for bootstrapping *)
val sexppat_alt_def = tDefine"sexppat_alt"`
 (sexppat_alt s =
    OPTION_MAP Pvar (odestSEXSTR s) ++
    case dstrip_sexp s of
    | NONE => NONE
    | SOME (nm,args) =>
      if nm = "Pany" ∧ LENGTH args = 0 then
        SOME Pany
      else if nm = "Plit" ∧ LENGTH args = 1 then
        OPTION_MAP Plit (sexplit (EL 0 args))
      else if nm = "Pcon" ∧ LENGTH args = 2 then
        OPTION_MAP2 Pcon (sexpopt (sexpid odestSEXSTR) (EL 0 args))
          (sexppat_list (EL 1 args))
      else if nm = "Pref" ∧ LENGTH args = 1 then
        OPTION_MAP Pref (sexppat_alt (EL 0 args))
      else if nm = "Ptannot" ∧ LENGTH args = 2 then
        OPTION_MAP2 Ptannot (sexppat_alt (EL 0 args)) (sexptype_alt (EL 1 args))
      else NONE) ∧
 (sexppat_list s =
    case s of
    | SX_SYM nm => if nm = "nil" then SOME [] else NONE
    | SX_CONS a d =>
      (case sexppat_alt a of
       | NONE => NONE
       | SOME h =>
       case sexppat_list d of
       | NONE => NONE
       | SOME t => SOME (h::t))
    | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size) (λx. case x of INL y => y | INR y => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexppat_alt_ind = theorem"sexppat_alt_ind";

Theorem sexppat_alt_intro
  `(∀s. sexppat s = sexppat_alt s) ∧ (∀s. sexppat_list s = sexplist sexppat s)`
  (ho_match_mp_tac sexppat_alt_ind \\ rw[]
  >- (
    rw[Once sexppat_alt_def,Once sexppat_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    simp[monad_unitbind_assert] \\
    srw_tac[ETA_ss][sexptype_alt_intro1] )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT2 sexppat_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] ));

Theorem sexppat_alt_intro1
  `sexppat = sexppat_alt ∧ sexplist sexppat = sexppat_list`
  (rw[FUN_EQ_THM,sexppat_alt_intro]);

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
  if s = "FPtopFPFma" then SOME (FP_top FP_Fma) else
  if s = "FPtopFPFms" then SOME (FP_top FP_Fms) else
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
  if s = "ListAppend" then SOME ListAppend else
  if s = "Aalloc" then SOME Aalloc else
  if s = "AallocEmpty" then SOME AallocEmpty else
  if s = "Asub" then SOME Asub else
  if s = "Alength" then SOME Alength else
  if s = "Aupdate" then SOME Aupdate else
  if s = "ConfigGC" then SOME ConfigGC else NONE) ∧
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

(* translator friendly version for bootstrapping *)
val sexpexp_alt_def = tDefine"sexpexp_alt"`
  (sexpexp_alt s =
     case dstrip_sexp s of
     | NONE => NONE
     | SOME (nm,args) =>
          if nm = "Raise" ∧ LENGTH args = 1 then
             lift Raise (sexpexp_alt (EL 0 args)) else
          if nm = "Handle" ∧ LENGTH args = 2 then
             OPTION_MAP2 Handle (sexpexp_alt (EL 0 args))
               (sexppes (EL 1 args)) else
          if nm = "Lit" ∧ LENGTH args = 1 then
             lift Lit (sexplit (EL 0 args))
           else
          if nm = "Con" ∧ LENGTH args = 2 then
             OPTION_MAP2 Con (sexpopt (sexpid odestSEXSTR) (EL 0 args))
               (sexpexp_list (EL 1 args))
           else
          if nm = "Var" ∧ LENGTH args = 1 then
             lift Var (sexpid odestSEXSTR (EL 0 args))
           else
          if nm = "Fun" ∧ LENGTH args = 2 then
             OPTION_MAP2 Fun (odestSEXSTR (EL 0 args))
               (sexpexp_alt (EL 1 args))
           else
          if nm = "App" ∧ LENGTH args = 2 then
             OPTION_MAP2 App (sexpop (EL 0 args))
               (sexpexp_list  (EL 1 args))
           else
          if nm = "Log" ∧ LENGTH args = 3 then
             lift Log (sexplop (EL 0 args)) <*> sexpexp_alt (EL 1 args) <*>
             sexpexp_alt (EL 2 args)
           else
          if nm = "If" ∧ LENGTH args = 3 then
             lift If (sexpexp_alt (EL 0 args)) <*> sexpexp_alt (EL 1 args) <*>
             sexpexp_alt (EL 2 args)
           else
          if nm = "Mat" ∧ LENGTH args = 2 then
             OPTION_MAP2 Mat (sexpexp_alt (EL 0 args))
               (sexppes (EL 1 args))
           else
          if nm = "Let" ∧ LENGTH args = 3 then
             lift Let (sexpopt odestSEXSTR (EL 0 args)) <*>
             sexpexp_alt (EL 1 args) <*> sexpexp_alt (EL 2 args)
           else
          if nm = "Letrec" ∧ LENGTH args = 2 then
             OPTION_MAP2 Letrec
               (sexpfuns (EL 0 args))
               (sexpexp_alt (EL 1 args))
           else
          if nm = "Tannot" ∧ LENGTH args = 2 then
             OPTION_MAP2 Tannot (sexpexp_alt (EL 0 args))
               (sexptype_alt (EL 1 args))
           else
          if nm = "Lannot" ∧ LENGTH args = 2 then
            OPTION_MAP2 Lannot (sexpexp_alt (EL 0 args))
              (sexplocn (EL 1 args))
          else NONE) ∧
   (sexpexp_list s =
      case s of
      | SX_SYM nm => if nm = "nil" then SOME [] else NONE
      | SX_CONS a d =>
        (case sexpexp_alt a of
         | NONE => NONE
         | SOME h =>
         case sexpexp_list d of
         | NONE => NONE
         | SOME t => SOME (h::t))
      | _ => NONE) ∧
  (sexppes s =
   case s of
   | SX_SYM nm => if nm = "nil" then SOME [] else NONE
   | SX_CONS a d =>
     (case sexppatexp a of
      | NONE => NONE
      | SOME h =>
      case sexppes d of
      | NONE => NONE
      | SOME t => SOME (h::t))
   | _ => NONE) ∧
  (sexpfuns s =
   case s of
   | SX_SYM nm => if nm = "nil" then SOME [] else NONE
   | SX_CONS a d =>
     (case sexpfun a of
      | NONE => NONE
      | SOME h =>
      case sexpfuns d of
      | NONE => NONE
      | SOME t => SOME (h::t))
   | _ => NONE) ∧
   (sexppatexp s =
    case s of
    | SX_CONS a d =>
      (case (sexppat_alt a, sexpexp_alt d) of
      | (SOME p, SOME e) => SOME (p,e)
      | _ => NONE)
    | _ => NONE) ∧
   (sexpfun s =
     case s of
     | SX_CONS a d =>
       (case d of
       | SX_CONS b d =>
       (case (odestSEXSTR a, odestSEXSTR b, sexpexp_alt d) of
        | (SOME x, SOME y, SOME z) => SOME (x,y,z)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size)
    (λx. case x of
         | INL y => y
         | INR (INL y) => y
         | INR (INR (INL y)) => y
         | INR (INR (INR (INL y))) => y
         | INR (INR (INR (INR (INL y)))) => y
         | INR (INR (INR (INR (INR y)))) => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexpexp_alt_ind = theorem"sexpexp_alt_ind";

Theorem sexpexp_alt_intro
  `(∀s. sexpexp s = sexpexp_alt s) ∧
  (∀s. sexplist sexpexp s = sexpexp_list s) ∧
  (∀s. sexplist (sexppair sexppat sexpexp) s = sexppes s) ∧
  (∀s. sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) s = sexpfuns s) ∧
  (∀s. sexppair sexppat sexpexp s = sexppatexp s) ∧
  (∀s. sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp) s = sexpfun s)`
  (ho_match_mp_tac sexpexp_alt_ind \\ rw[]
  >- (
    rw[Once sexpexp_alt_def,Once sexpexp_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    simp[monad_unitbind_assert] \\
    rpt (
    IF_CASES_TAC >- (
      pop_assum strip_assume_tac \\ rveq \\
      full_simp_tac std_ss []
      \\ fsrw_tac[ETA_ss][sexptype_alt_intro1] ) \\
    simp[] ) )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT2 sexpexp_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 sexpexp_alt_def)))] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT1 (funpow 3 CONJUNCT2 sexpexp_alt_def))] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once sexplist_def,
       sexppair_def,
       Once (CONJUNCT1 (funpow 4 CONJUNCT2 sexpexp_alt_def))] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[sexppat_alt_intro1] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once sexplist_def,
       sexppair_def,
       Once (funpow 5 CONJUNCT2 sexpexp_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[sexppat_alt_intro1] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[]));

Theorem sexpexp_alt_intro1
  `sexpexp = sexpexp_alt ∧
   sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) = sexpfuns`
  (rw[FUN_EQ_THM,sexpexp_alt_intro]);

val sexptype_def_def = Define`
  sexptype_def =
  sexplist
    (sexppair (sexplist odestSEXSTR)
      (sexppair odestSEXSTR
        (sexplist (sexppair odestSEXSTR (sexplist sexptype)))))`;

val sexpdec_def = tDefine"sexpdec"`
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
                       (sexplist sexptype (EL 2 args))) ++
      guard (nm = "Dmod" ∧ LENGTH args = 2)
            (lift2 Dmod (odestSEXSTR (EL 0 args))
                        (sexplist sexpdec (EL 1 args))) ++
      guard (nm = "Dlocal" ∧ LENGTH args = 2)
            (lift2 Dlocal (sexplist sexpdec (EL 0 args))
                (sexplist sexpdec (EL 1 args)))
    od`
  (wf_rel_tac`measure sexp_size`
   \\ rw[LENGTH_EQ_NUM_compute] \\ fs[]
   \\ metis_tac[sxMEM_sizelt,dstrip_sexp_size,MEM,LESS_TRANS]);

(* translator friendly version for bootstrapping *)
val sexpdec_alt_def = tDefine"sexpdec_alt"`
  (sexpdec_alt s =
    case dstrip_sexp s of
    | NONE => NONE
    | SOME (nm,args) =>
      if nm = "Dlet" ∧ LENGTH args = 3 then
          (lift Dlet (sexplocn (HD args)) <*>
                       (sexppat_alt (EL 1 args)) <*>
                       (sexpexp_alt (EL 2 args))) else
      if nm = "Dletrec" ∧ LENGTH args = 2 then
            (lift2 Dletrec (sexplocn (HD args))
                           (sexpfuns  (EL 1 args))) else
      if nm = "Dtype" ∧ LENGTH args = 2 then
            (lift2 Dtype (sexplocn (HD args)) (sexptype_def (EL 1 args))) else
      if nm = "Dtabbrev" ∧ LENGTH args = 4 then
            (lift Dtabbrev (sexplocn (EL 0 args)) <*>
                           (sexplist odestSEXSTR (EL 1 args)) <*>
                           (odestSEXSTR (EL 2 args)) <*>
                           (sexptype_alt (EL 3 args))) else
      if nm = "Dexn" ∧ LENGTH args = 3 then
            (lift Dexn (sexplocn (EL 0 args)) <*>
                       (odestSEXSTR (EL 1 args)) <*>
                       (sexptype_list (EL 2 args))) else
      if nm = "Dmod" ∧ LENGTH args = 2 then
            (lift2 Dmod (odestSEXSTR (EL 0 args))
                        (sexpdec_list (EL 1 args))) else
      if nm = "Dlocal" ∧ LENGTH args = 2  then
            (lift2 Dlocal (sexpdec_list (EL 0 args))
                        (sexpdec_list (EL 1 args))) else NONE) ∧
   (sexpdec_list s =
      case s of
      | SX_SYM nm => if nm = "nil" then SOME [] else NONE
      | SX_CONS a d =>
        (case sexpdec_alt a of
         | NONE => NONE
         | SOME h =>
         case sexpdec_list d of
         | NONE => NONE
         | SOME t => SOME (h::t))
      | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size)
    (λx. case x of
         | INL y => y
         | INR y => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexpdec_alt_ind = theorem"sexpdec_alt_ind";

Theorem sexpdec_alt_intro
  `(∀s. sexpdec s = sexpdec_alt s) ∧
  (∀s. sexplist sexpdec s = sexpdec_list s)`
  (ho_match_mp_tac sexpdec_alt_ind \\ rw[]
  >- (
    rw[Once sexpdec_def,Once sexpdec_alt_def,sexppat_alt_intro1,sexpexp_alt_intro1,sexptype_alt_intro1]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[] \\ rfs[] \\ fsrw_tac[ETA_ss][] )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT2 sexpdec_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] ));

Theorem sexpdec_alt_intro1
  `sexpdec = sexpdec_alt ∧
   sexplist sexpdec = sexpdec_list`
  (rw[FUN_EQ_THM,sexpdec_alt_intro]);

(* now the reverse: toSexp *)

val listsexp_def = Define`
  listsexp = FOLDR SX_CONS nil`;

Theorem listsexp_11[simp]
  `∀ l1 l2. listsexp l1 = listsexp l2 ⇔ l1 = l2`
  (Induct >> gen_tac >> cases_on `l2` >> fs[listsexp_def]);

val optsexp_def = Define`
  (optsexp NONE = SX_SYM "NONE") ∧
  (optsexp (SOME x) = listsexp [SX_SYM "SOME"; x])`;

Theorem optsexp_11[simp]
  `optsexp o1 = optsexp o2 ⇔ o1 = o2`
  (cases_on `o1` >> cases_on `o2` >> fs[optsexp_def, listsexp_def]);

val idsexp_def = Define`
  (idsexp (Short n) = listsexp [SX_SYM"Short"; SEXSTR n]) ∧
  (idsexp (Long ns n) = listsexp [SX_SYM"Long"; SEXSTR ns; idsexp n])`;

Theorem idsexp_11[simp]
  `∀ i1 i2. idsexp i1 = idsexp i2 ⇔ i1 = i2`
  (Induct >> gen_tac >> cases_on `i2` >> fs[idsexp_def]);

val typesexp_def = tDefine"typesexp"`
  (typesexp (Atvar s) = listsexp [SX_SYM "Atvar"; SEXSTR s]) ∧
  (typesexp (Atfun t1 t2) = listsexp [SX_SYM "Atfun"; typesexp t1; typesexp t2]) ∧
  (typesexp (Attup ts) = listsexp [SX_SYM "Attup"; listsexp (MAP typesexp ts)]) ∧
  (typesexp (Atapp ts tc) = listsexp [SX_SYM "Atapp"; listsexp (MAP typesexp ts); idsexp tc])`
  (WF_REL_TAC`measure ast_t_size` >> rw[] \\
   Induct_on`ts` >> simp[ast_t_size_def] >>
   rw[] >> res_tac >> simp[]);

Theorem typesexp_11[simp]
  `∀t1 t2. typesexp t1 = typesexp t2 ⇔ t1 = t2`
  (ho_match_mp_tac (theorem"typesexp_ind")
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

Theorem litsexp_11[simp]
  `∀l1 l2. litsexp l1 = litsexp l2 ⇔ l1 = l2`
  (Cases \\ Cases \\ rw[litsexp_def,EQ_IMP_THM,listsexp_def]
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

Theorem patsexp_11[simp]
  `∀p1 p2. patsexp p1 = patsexp p2 ⇔ p1 = p2`
  (ho_match_mp_tac (theorem"patsexp_ind")
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

Theorem lopsexp_11[simp]
  `∀l1 l2. lopsexp l1 = lopsexp l2 ⇔ l1 = l2`
  (Cases \\ Cases \\ simp[lopsexp_def]);

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
  (opsexp (FP_top FP_Fma) = SX_SYM "FPtopFPFma") ∧
  (opsexp (FP_top FP_Fms) = SX_SYM "FPtopFPFms") ∧
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
  (opsexp ListAppend = SX_SYM "ListAppend") ∧
  (opsexp Aalloc = SX_SYM "Aalloc") ∧
  (opsexp AallocEmpty = SX_SYM "AallocEmpty") ∧
  (opsexp Asub = SX_SYM "Asub") ∧
  (opsexp Alength = SX_SYM "Alength") ∧
  (opsexp Aupdate = SX_SYM "Aupdate") ∧
  (opsexp ConfigGC = SX_SYM "ConfigGC") ∧
  (opsexp (FFI s) = SX_CONS (SX_SYM "FFI") (SEXSTR s))`;

Theorem sexpop_opsexp[simp]
  `sexpop (opsexp op) = SOME op`
  (Cases_on`op`>>rw[sexpop_def,opsexp_def]>>
  TRY(MAP_FIRST rename1 [
        ‘Opn c1’, ‘Opb c1’, ‘Opw c2 c1’, ‘Chopb c1’, ‘Shift c1 c2 _’,
        ‘FP_cmp c1’, ‘FP_uop c1’, ‘FP_bop c1’, `FP_top c1`, ‘WordFromInt c1’,
        ‘WordToInt c1’
      ] >>
      Cases_on`c1` >> rw[sexpop_def,opsexp_def] >>
      Cases_on`c2` >> rw[sexpop_def,opsexp_def]) >>
  rw[sexpop_def,opsexp_def,SEXSTR_def])

Theorem opsexp_11[simp]
  `∀o1 o2. opsexp o1 = opsexp o2 ⇔ o1 = o2`
  (rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM “sexpop”) >> simp[]);

val locnsexp_def = Define`
  locnsexp (Locs (locn n1 n2 n3) (locn n4 n5 n6)) =
    listsexp (MAP SX_NUM [n1;n2;n3;n4;n5;n6])`;

Theorem locnsexp_thm[compute]
  `locnsexp (Locs l1 l2) =
   listsexp [&(l1.row); &(l1.col); &(l1.offset);
             &(l2.row); &(l2.col); &(l2.offset)]`
  (Cases_on`l1` \\ Cases_on`l2` \\ rw[locnsexp_def]);

Theorem locnsexp_11[simp]
  `∀l1 l2. locnsexp l1 = locnsexp l2 ⇔ l1 = l2`
  (Cases \\ Cases \\ rename [`locnsexp (Locs l1 l2) = locnsexp (Locs l3 l4)`] >>
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

Theorem expsexp_11[simp]
  `∀e1 e2. expsexp e1 = expsexp e2 ⇒ e1 = e2`
  (ho_match_mp_tac (theorem"expsexp_ind")
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

Theorem type_defsexp_11[simp]
  `∀t1 t2. type_defsexp t1 = type_defsexp t2 ⇔ t1 = t2`
  (rw[type_defsexp_def,EQ_IMP_THM]
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

Theorem dec1_size_eq
  `dec1_size xs = list_size dec_size xs`
  (Induct_on `xs` \\ fs [dec_size_def, list_size_def]);

Theorem mem_size_lemma
  `list_size sz xs < N ==> (MEM x xs ⇒ sz x < N)`
  (Induct_on `xs` \\ rw [list_size_def] \\ fs []);

val decsexp_def = tDefine "decsexp"`
  (decsexp (Dlet locs p e) = listsexp [SX_SYM "Dlet"; locnsexp locs; patsexp p; expsexp e]) ∧
  (decsexp (Dletrec locs funs) =
     listsexp [SX_SYM "Dletrec"; locnsexp locs;
               listsexp (MAP (λ(f,x,e). SX_CONS (SEXSTR f) (SX_CONS (SEXSTR x) (expsexp e))) funs)]) ∧
  (decsexp (Dtype locs td) = listsexp [SX_SYM "Dtype"; locnsexp locs; type_defsexp td]) ∧
  (decsexp (Dtabbrev locs ns x t) = listsexp [SX_SYM "Dtabbrev"; locnsexp locs; listsexp (MAP SEXSTR ns); SEXSTR x; typesexp t]) ∧
  (decsexp (Dexn locs x ts) = listsexp [SX_SYM "Dexn"; locnsexp locs; SEXSTR x; listsexp (MAP typesexp ts)]) ∧
  (decsexp (Dmod name decs) = listsexp [SX_SYM "Dmod"; SEXSTR name; listsexp (MAP decsexp decs)]) ∧
  decsexp (Dlocal ldecs decs) = listsexp [SX_SYM "Dlocal";
        listsexp (MAP decsexp ldecs); listsexp (MAP decsexp decs)]`
  ((wf_rel_tac`measure dec_size` \\ strip_tac)
   \\ fs [dec1_size_eq]
   \\ rpt (conj_tac ORELSE gen_tac ORELSE match_mp_tac mem_size_lemma)
   \\ fs []);

Theorem decsexp_11[simp]
  `∀d1 d2. decsexp d1 = decsexp d2 ⇔ d1 = d2`
  (ho_match_mp_tac(theorem"decsexp_ind")
  \\ rw[decsexp_def,EQ_IMP_THM] \\ fs[decsexp_def]
  \\ Cases_on`d2` \\ fs[decsexp_def] \\ rw[]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ TRY (first_x_assum match_mp_tac \\ rw[])
  \\ rpt(pairarg_tac \\ fs[]));

(* round trip *)

Theorem odestSXSTR_SOME[simp]
  `odestSXSTR s = SOME y ⇔ (s = SX_STR y)`
  (Cases_on`s`>>simp[odestSXSTR_def])

Theorem odestSEXSTR_SOME[simp]
  `odestSEXSTR s = SOME y ⇔ (s = SEXSTR y)`
  (Cases_on`s`\\simp[odestSEXSTR_def,SEXSTR_def]
  \\ metis_tac[decode_encode_control,encode_decode_control]);

Theorem odestSXSTR_SX_STR[simp]
  `odestSXSTR (SX_STR s) = SOME s`
  (rw[odestSXSTR_def])

Theorem odestSEXSTR_SEXSTR[simp]
  `odestSEXSTR (SEXSTR s) = SOME s`
  (rw[odestSEXSTR_def]);

Theorem odestSXNUM_SX_NUM[simp]
  `odestSXNUM (SX_NUM n) = SOME n`
  (EVAL_TAC)

Theorem odestSXSYM_SX_SYM[simp]
  `odestSXSYM (SX_SYM s) = SOME s`
  (EVAL_TAC)

Theorem odestSXNUM_SX_STR[simp]
  `odestSXNUM (SX_STR s) = NONE`
  (EVAL_TAC)

Theorem odestSXNUM_SEXSTR[simp]
  `odestSXNUM (SEXSTR s) = NONE`
  (EVAL_TAC)

Theorem odestSXSTR_listsexp[simp]
  `odestSXSTR (listsexp l) = NONE`
  (Cases_on`l`>>EVAL_TAC)

Theorem odestSEXSTR_listsexp[simp]
  `odestSEXSTR (listsexp l) = NONE`
  (Cases_on`l`>>EVAL_TAC)

Theorem odestSXNUM_listsexp[simp]
  `odestSXNUM (listsexp l) = NONE`
  (Cases_on`l`>>EVAL_TAC)

Theorem dstrip_sexp_SX_STR[simp]
  `dstrip_sexp (SX_STR s) = NONE`
  (EVAL_TAC)

Theorem dstrip_sexp_SEXSTR[simp]
  `dstrip_sexp (SEXSTR s) = NONE`
  (EVAL_TAC)

Theorem strip_sxcons_listsexp[simp]
  `strip_sxcons (listsexp ls) = SOME ls`
  (Induct_on`ls`>>rw[listsexp_def] >> simp[GSYM listsexp_def]);

Theorem dstrip_sexp_listsexp[simp]
  `(dstrip_sexp (listsexp ls) =
    case ls of (SX_SYM x::xs) => SOME (x,xs) | _ => NONE)`
  (BasicProvers.CASE_TAC >> rw[dstrip_sexp_def,listsexp_def] >>
  BasicProvers.CASE_TAC >> rw[GSYM listsexp_def]);

Theorem sexplist_listsexp_matchable
  `∀g gl. (∀x. MEM x l ⇒ f (g x) = SOME x) ∧ (gl = MAP g l) ⇒
   sexplist f (listsexp gl) = SOME l`
  (Induct_on`l` >> simp[listsexp_def,Once sexplist_def] >>
  simp[GSYM listsexp_def] >> metis_tac[]);

Theorem sexplist_listsexp_rwt[simp]
  `(∀x. MEM x l ⇒ f (g x) = SOME x) ⇒
   (sexplist f (listsexp (MAP g l)) = SOME l)`
  (metis_tac[sexplist_listsexp_matchable]);

Theorem sexplist_listsexp_imp
  `sexplist f (listsexp l1) = SOME l2 ⇒
   ∀n. n < LENGTH l1 ⇒ f (EL n l1) = SOME (EL n l2)`
  (qid_spec_tac`l2`>>
  Induct_on`l1`>>simp[listsexp_def]>>simp[GSYM listsexp_def] >>
  simp[Once sexplist_def,PULL_EXISTS] >> rw[] >>
  Cases_on`n`>>simp[]);

Theorem sexpopt_optsexp[simp]
  `(∀y. (x = SOME y) ⇒ (f (g y) = x)) ⇒
   (sexpopt f (optsexp (OPTION_MAP g x)) = SOME x)`
  (Cases_on`x`>>EVAL_TAC >> simp[]);

Theorem sexpid_odestSEXSTR_idsexp[simp]
  `sexpid odestSEXSTR (idsexp i) = SOME i`
  (Induct_on `i` >> simp[idsexp_def] >>
  rw [Once sexpid_def]);

Theorem sexptype_typesexp[simp]
  `sexptype (typesexp t) = SOME t`
  (qid_spec_tac`t` >>
  ho_match_mp_tac type_ind >>
  conj_tac >- rw[Once sexptype_def,typesexp_def] >>
  conj_tac >- (rw[] \\ rw[Once sexptype_def,typesexp_def]) >>
  conj_tac \\ (
  Induct_on`l`>>rw[typesexp_def] >- (
    rw[Once sexptype_def,sexplist_listsexp_matchable] ) >> fs[] >>
  rw[Once sexptype_def] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  match_mp_tac sexplist_listsexp_matchable >>
  fs[typesexp_def] >> rw[] >> rw[] >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[]));

val exists_g_tac =
  (fn (g as (asl,w)) =>
    let
      val (x,b) = dest_exists w
      val tm = find_term (fn y => type_of x = type_of y andalso not (is_var y)) b
    in EXISTS_TAC tm end g)

Theorem sexptype_def_type_defsexp[simp]
  `sexptype_def (type_defsexp l) = SOME l`
  (Induct_on`l` >> rw[type_defsexp_def] >> rw[sexptype_def_def] >>
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

Theorem sexplit_litsexp[simp]
  `sexplit (litsexp l) = SOME l`
  (Cases_on`l`>>simp[sexplit_def,litsexp_def]
  >- (
    rw[] >> intLib.ARITH_TAC ) >>
  ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_8] >>
  ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_64] >>
  ONCE_REWRITE_TAC[wordsTheory.w2n_lt] >>
  rw[]);

Theorem sexppat_patsexp[simp]
  `sexppat (patsexp p) = SOME p`
  (qid_spec_tac`p` >>
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

Theorem sexplop_lopsexp[simp]
  `sexplop (lopsexp l) = SOME l`
  (Cases_on`l`>>EVAL_TAC)

Theorem sexplocn_locnsexp[simp]
  `sexplocn (locnsexp l) = SOME l`
  (Cases_on `l` >> rename [`Locs l1 l2`] >>
  Cases_on`l1` \\ Cases_on`l2` \\ rw[locnsexp_def,sexplocn_def]);

Theorem sexpexp_expsexp[simp]
  `sexpexp (expsexp e) = SOME e`
  (qid_spec_tac`e` >>
  ho_match_mp_tac exp_ind >> rw[] >>
  rw[expsexp_def] >> rw[Once sexpexp_def] >>
  match_mp_tac sexplist_listsexp_matchable >>
  exists_g_tac >> simp[] >>
  fs[listTheory.EVERY_MEM] >>
  qx_gen_tac`p`>>PairCases_on`p` >> simp[] >>
  simp[sexppair_def] >>
  rw[] >> res_tac >> fs[]);

Theorem sexpdec_decsexp[simp]
  `∀d. sexpdec (decsexp d) = SOME d`
  (ho_match_mp_tac dec_ind
  \\ rw[decsexp_def]
  \\ rw[Once sexpdec_def]
  \\ match_mp_tac sexplist_listsexp_matchable
  \\ exists_g_tac >> simp[] \\ fs[EVERY_MEM]
  \\ qx_gen_tac`p`>>PairCases_on`p`>>rw[]
  \\ simp[sexppair_def])

Theorem sexpopt_SOME
  `sexpopt f s = SOME opt ⇒
   ∃x. s = optsexp x ∧
       (case x of NONE => opt = NONE | SOME s => IS_SOME opt ∧ opt = f s)`
  (rw[sexpopt_def]
  \\ Cases_on`odestSXSYM s` \\ fs[dstrip_sexp_SOME] \\ rw[]
  \\ fs[odestSXSYM_def] \\ simp[EXISTS_OPTION, optsexp_def, listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[] \\ fs[] \\ rw[]
  \\ rename[`odestSXSYM s = SOME _`] >> Cases_on `s` >>
  fs[odestSXSYM_def, dstrip_sexp_def]);

Theorem listsexp_MAP_EQ_f
  `(∀x. MEM x ls ⇒ f1 x = f2 x) ⇒
    listsexp (MAP f1 ls) = listsexp (MAP f2 ls)`
  (Induct_on`ls` >> simp[] >> fs[listsexp_def])

Theorem sexplist_SOME
  `sexplist f s = SOME ls ⇒ ∃l. s = listsexp l ∧ MAP f l = MAP SOME ls`
  (map_every qid_spec_tac[`s`,`ls`] >>
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

Theorem sexppair_SOME
  `sexppair f1 f2 s = SOME p ⇒ ∃x y. f1 x = SOME (FST p) ∧ f2 y = SOME (SND p) ∧ s = SX_CONS x y`
  (rw[sexppair_def]
  \\ every_case_tac \\ fs[]);

Theorem OPTION_CHOICE_EQ_SOME
  `OPTION_CHOICE m1 m2 = SOME x ⇔
    m1 = SOME x ∨ m1 = NONE ∧ m2 = SOME x`
  (Cases_on `m1` >> simp[]);

Theorem dstrip_sexp_EQ_SOME
  `dstrip_sexp s = SOME (nm, args) ⇔
   ∃t. s = SX_CONS (SX_SYM nm) t ∧ strip_sxcons t = SOME args`
  (Cases_on`s` >> simp[dstrip_sexp_def] >> every_case_tac >>
  simp[] >> metis_tac[]);

Theorem litsexp_sexplit
  `∀s l. sexplit s = SOME l ⇒ litsexp l = s`
  (rw[sexplit_def]
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

Theorem idsexp_sexpid_odestSEXSTR
  `∀y x. sexpid odestSEXSTR x = SOME y ⇒ x = idsexp y`
  (Induct
  \\ rw[Once sexpid_def]
  \\ fs[dstrip_sexp_SOME] \\ rw[]
  \\ fs[]
  \\ fs[OPTION_CHOICE_EQ_SOME]
  \\ rw[idsexp_def,listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[]
  \\ fs[]
  \\ fs[Once strip_sxcons_def]
  \\ every_case_tac \\ fs[]);

Theorem strip_sxcons_NIL[simp]
  `strip_sxcons ⟪ ⟫ = SOME []`
  (simp[Once strip_sxcons_def]);

Theorem strip_sxcons_SXCONS[simp]
  `strip_sxcons (SX_CONS s1 s2) = lift (CONS s1) (strip_sxcons s2)`
  (simp[Once strip_sxcons_def]);

Theorem typesexp_sexptype
  `∀s t. sexptype s = SOME t ⇒ typesexp t = s`
  (ho_match_mp_tac(theorem"sexptype_ind")
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[Once sexptype_def]
  \\ fs[dstrip_sexp_SOME,PULL_EXISTS]
  \\ rw[]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ rename1`guard (nm = "Atvar" ∧ _) _`
  \\ reverse (Cases_on `nm ∈ {"Atvar"; "Atfun"; "Attup"; "Atapp"}`) >- fs[]
  \\ pop_assum mp_tac >> simp[]
  \\ strip_tac \\ fs[typesexp_def, listsexp_def]
  \\ fs[LENGTH_EQ_NUM_compute, PULL_EXISTS]
  \\ rw[] \\ fs[]
  \\ fs[GSYM listsexp_def]
  \\ imp_res_tac idsexp_sexpid_odestSEXSTR \\ simp[]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rfs[EL_MAP]
  \\ rpt strip_tac \\ res_tac
  \\ first_x_assum(MATCH_MP_TAC o MP_CANON)
  \\ simp[sxMEM_def]
  \\ metis_tac[MEM_EL]);

Theorem patsexp_sexppat
  `∀s p. sexppat s = SOME p ⇒ patsexp p = s`
  (ho_match_mp_tac (theorem"sexppat_ind")
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

Theorem opsexp_sexpop
  `sexpop s = SOME p ⇒ opsexp p = s`
  (Cases_on`s` \\ rw[sexpop_def] \\ rw[opsexp_def]
  \\ match1_tac(mg.aub`s_:sexp`,(fn(a,t)=>if is_var(t"s") then Cases_on`^(t"s")`\\fs[sexpop_def] else NO_TAC))
  \\ match1_tac(mg.aub`s_:sexp`,(fn(a,t)=>if is_var(t"s") then Cases_on`^(t"s")`\\fs[sexpop_def] else NO_TAC))
  \\ pop_assum mp_tac
  \\ rpt IF_CASES_TAC \\ rw[]
  \\ rw[opsexp_def, GSYM encode_decode_control]);

Theorem lopsexp_sexplop
  `sexplop s = SOME z ⇒ lopsexp z = s`
  (Cases_on`s` \\ rw[sexplop_def] \\ rw[lopsexp_def]);

Theorem locnsexp_sexplocn
  `sexplocn s = SOME z ⇒ locnsexp z = s`
  (Cases_on`z` \\ rename [`Locs l1 l2`] >>
  Cases_on`l1` \\ Cases_on `l2`
  \\ rw[sexplocn_def,locnsexp_def]
  \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
  \\ fs[Once strip_sxcons_def]
  \\ simp[listsexp_def]
  \\ rename [`⟪h1; h2; h3; h4; h5; h6⟫`]
  \\ map_every (fn q => Cases_on q >> fs[odestSXNUM_def])
       [`h1`, `h2`, `h3`, `h4`, `h5`, `h6`]);

Theorem expsexp_sexpexp
  `∀s e. sexpexp s = SOME e ⇒ expsexp e = s`
  (ho_match_mp_tac (theorem"sexpexp_ind") >>
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

Theorem type_defsexp_sexptype_def
  `sexptype_def s = SOME x ⇒ type_defsexp x = s`
  (rw[sexptype_def_def,type_defsexp_def]
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

Theorem decsexp_sexpdec
  `∀s d. sexpdec s = SOME d ⇒ decsexp d = s`
  (ho_match_mp_tac(theorem"sexpdec_ind")
  \\ ntac 3 strip_tac
  \\ rw[Once sexpdec_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[dstrip_sexp_SOME]
  \\ rpt var_eq_tac
  \\ rename1 `guard (nm = _ ∧ _) _`
  \\ Cases_on `nm ∈ {"Dlet"; "Dletrec"; "Dtype"; "Dtabbrev"; "Dexn"; "Dmod"}`
  \\ fs[]
  \\ fs[decsexp_def, LENGTH_EQ_NUM_compute, listsexp_def]
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
  >- (pairarg_tac \\ fs[]
    \\ imp_res_tac sexppair_SOME
    \\ fs[] \\ rveq \\ fs[]
    \\ imp_res_tac expsexp_sexpexp)
  \\ fs [sxMEM_def,listsexp_def]
  \\ metis_tac[MEM_EL]);

(* valid sexps *)

Theorem SEXSTR_valid[simp]
  `valid_sexp (SEXSTR s)`
  (rw[SEXSTR_def,EVERY_isPrint_encode_control]);

Theorem listsexp_valid
  `∀ls. EVERY valid_sexp ls ⇒ valid_sexp (listsexp ls)`
  (Induct \\ simp[listsexp_def] \\ simp[GSYM listsexp_def]
  \\ EVAL_TAC);

Theorem idsexp_valid[simp]
  `∀i. valid_sexp (idsexp i)`
  (Induct \\ simp[idsexp_def] >>
  rw []
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ EVAL_TAC);

Theorem typesexp_valid[simp]
  `∀t. valid_sexp (typesexp t)`
  (ho_match_mp_tac(theorem"typesexp_ind")
  \\ rw[typesexp_def]
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ rpt conj_tac
  \\ TRY (match_mp_tac listsexp_valid)
  \\ simp[EVERY_MAP,EVERY_MEM]
  \\ EVAL_TAC);

Theorem litsexp_valid[simp]
  `∀l. valid_sexp (litsexp l)`
  (Cases \\ rw[litsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[] \\ EVAL_TAC);

Theorem optsexp_valid
  `∀x. (∀y. x = SOME y ⇒ valid_sexp y) ⇒ valid_sexp (optsexp x)`
  (Cases \\ rw[optsexp_def]
  \\ TRY(match_mp_tac listsexp_valid) \\ rw[]
  \\ EVAL_TAC);

Theorem patsexp_valid[simp]
  `∀p. valid_sexp (patsexp p)`
  (ho_match_mp_tac(theorem"patsexp_ind")
  \\ rw[patsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY (match_mp_tac optsexp_valid \\ rw[] \\ rw[])
  \\ TRY (match_mp_tac listsexp_valid \\ simp[EVERY_MAP,EVERY_MEM])
  \\ EVAL_TAC);

Theorem type_defsexp_valid[simp]
  `∀t. valid_sexp (type_defsexp t)`
  (rw[type_defsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
  \\ pairarg_tac \\ rw[]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
  \\ pairarg_tac \\ rw[]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]);

Theorem opsexp_valid[simp]
  `∀op. valid_sexp (opsexp op)`
  (Cases \\ simp[opsexp_def]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ TRY(Cases_on`o'`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`w`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`s`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`f`) \\ simp[opsexp_def]
  \\ EVAL_TAC);

Theorem lopsexp_valid[simp]
  `∀l. valid_sexp (lopsexp l)`
  (Cases \\ simp[lopsexp_def]
  \\ EVAL_TAC);

Theorem locnsexp_valid[simp]
  `∀l. valid_sexp (locnsexp l)`
  (Cases \\ rename [`Locs l1 l2`] >> Cases_on `l1` \\ Cases_on `l2` \\ EVAL_TAC);

Theorem expsexp_valid[simp]
  `∀e. valid_sexp (expsexp e)`
  (ho_match_mp_tac(theorem"expsexp_ind")
  \\ rw[expsexp_def]
  \\ TRY(match_mp_tac listsexp_valid)
  \\ rw[]
  \\ TRY(EVAL_TAC \\ NO_TAC)
  \\ TRY(match_mp_tac optsexp_valid \\ rw[] \\ rw[])
  \\ TRY(match_mp_tac listsexp_valid \\ simp[EVERY_MAP,EVERY_MEM])
  \\ simp[FORALL_PROD]
  \\ first_x_assum MATCH_ACCEPT_TAC);

Theorem decsexp_valid[simp]
  `∀d. valid_sexp (decsexp d)`
  (ho_match_mp_tac dec_ind \\ rw[decsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP,EVERY_MEM]
  \\ simp[FORALL_PROD]);

val _ = export_theory();
