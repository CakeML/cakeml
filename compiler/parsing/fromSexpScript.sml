(*
  Definitions of functions for conversion between an S-expression encoding of
  the CakeML abstract syntax and the abstract syntax type itself.

  The S-expressions are parsed as *per* the PEG in HOL’s
  `examples/formal-language/context-free/simpleSexpPEGScript.sml`.
*)

open preamble match_goal
open simpleSexpTheory astTheory
open bitstringTheory
open bitstring_extraTheory

val _ = new_theory "fromSexp";
val _ = set_grammar_ancestry ["simpleSexp", "ast", "location","fpSem"]
val _ = option_monadsyntax.temp_add_option_monadsyntax()

(* TODO: this is duplicated in parserProgTheory *)
val monad_unitbind_assert = Q.prove(
  `!b x. monad_unitbind (assert b) x = if b then x else NONE`,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);

Overload lift[local] = ``OPTION_MAP``

(* TODO: move*)

Theorem OPTION_APPLY_MAP3:
   OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z = SOME r ⇔
   ∃a b c. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ f a b c = r
Proof
  Cases_on`x`\\simp[] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`y`\\fs[]
QED

Theorem OPTION_APPLY_MAP4:
   OPTION_APPLY (OPTION_APPLY (OPTION_APPLY (OPTION_MAP f x) y) z ) t= SOME r ⇔
   ∃a b c d. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ t = SOME d /\ f a b c d= r
Proof
  Cases_on`x`\\simp[] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ Cases_on`y`\\fs[] \\ Cases_on`z`\\fs[]
QED

Theorem FOLDR_SX_CONS_INJ:
   ∀l1 l2. FOLDR SX_CONS nil l1 = FOLDR SX_CONS nil l2 ⇔ l1 = l2
Proof
  Induct \\ simp[]
  >- ( Induct \\ simp[] )
  \\ gen_tac \\ Induct \\ simp[]
QED

Theorem strip_sxcons_11:
   ∀s1 s2 x. strip_sxcons s1 = SOME x ∧ strip_sxcons s2 = SOME x ⇒ s1 = s2
Proof
  ho_match_mp_tac simpleSexpTheory.strip_sxcons_ind
  \\ ntac 4 strip_tac
  \\ simp[Once simpleSexpTheory.strip_sxcons_def]
  \\ CASE_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]
  \\ pop_assum mp_tac
  \\ simp[Once simpleSexpTheory.strip_sxcons_def]
  \\ CASE_TAC \\ fs[] \\ strip_tac \\ rveq \\ fs[]
QED

Theorem dstrip_sexp_size:
   ∀s sym args. dstrip_sexp s = SOME (sym, args) ⇒
                 ∀e. MEM e args ⇒ sexp_size e < sexp_size s
Proof
  Induct >> simp[dstrip_sexp_def, sexp_size_def] >>
  rename1 `sexp_CASE sxp` >> Cases_on `sxp` >> simp[] >> rpt strip_tac >>
  rename1 `MEM sxp0 sxpargs` >> rename1 `strip_sxcons sxp'` >>
  `sxMEM sxp0 sxp'` by metis_tac[sxMEM_def] >> imp_res_tac sxMEM_sizelt >>
  simp[]
QED

Theorem dstrip_sexp_SOME:
   dstrip_sexp s = SOME x ⇔
   ∃sym sa args. s =
     SX_CONS (SX_SYM sym) sa ∧
     strip_sxcons sa = SOME args ∧
     (x = (sym,args))
Proof
  Cases_on`s`>>simp[dstrip_sexp_def]>>
  every_case_tac>>simp[]
QED

Theorem strip_sxcons_SOME_NIL[simp]:
   strip_sxcons s = SOME [] ⇔ s = nil
Proof
  rw[Once strip_sxcons_def] >>
  every_case_tac >> simp[]
QED

Theorem strip_sxcons_EQ_CONS[simp]:
   strip_sxcons s = SOME (h::t) ⇔
     ∃s0. s = SX_CONS h s0 ∧ strip_sxcons s0 = SOME t
Proof
  simp[Once strip_sxcons_def] >> every_case_tac >> simp[] >>
  metis_tac[]
QED

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

Theorem EVERY_isPrint_encode_control:
   ∀ls. EVERY isPrint (encode_control ls)
Proof
  Induct \\ rw[encode_control_def]
  \\ TRY (qmatch_rename_tac`isPrint _` \\ EVAL_TAC)
  \\ metis_tac[EVERY_isHexDigit_num_to_hex_string,MONO_EVERY,isHexDigit_isPrint,EVERY_CONJ]
QED

Theorem decode_encode_control[simp]:
   ∀ls. decode_control (encode_control ls) = SOME ls
Proof
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
  \\ simp[stringTheory.CHR_ORD]
QED

val isHexDigit_alt = Q.prove(
  `isHexDigit c ⇔ c ∈ set "0123456789abcdefABCDEF"`,
  rw[stringTheory.isHexDigit_def, EQ_IMP_THM] >> CONV_TAC EVAL >> simp[]);

val UNHEX_lt16 = Q.prove(
  `isHexDigit c ⇒ UNHEX c < 16`,
  dsimp[isHexDigit_alt, ASCIInumbersTheory.UNHEX_def]);

Theorem isAlpha_isUpper_isLower:
   isAlpha c ⇒ (isUpper c ⇎ isLower c)
Proof
  simp[isAlpha_def, isUpper_def, isLower_def]
QED

Theorem isLower_isAlpha:
   isLower c ⇒ isAlpha c
Proof
  simp[isLower_def, isAlpha_def]
QED

open ASCIInumbersTheory numposrepTheory
Theorem encode_decode_control:
   ∀ls r. decode_control ls = SOME r ⇒ ls = encode_control r
Proof
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
  metis_tac[isLower_isAlpha, isAlpha_isUpper_isLower]
QED

val SEXSTR_def = Define`
  SEXSTR s = SX_STR (encode_control s)`;

Theorem SEXSTR_11[simp]:
   SEXSTR s1 = SEXSTR s2 ⇔ s1 = s2
Proof
  rw[SEXSTR_def]
  \\ metis_tac[decode_encode_control,SOME_11]
QED

Theorem SEXSTR_distinct[simp]:
   (SEXSTR s ≠ SX_SYM sym) ∧
   (SEXSTR s ≠ SX_NUM num) ∧
   (SEXSTR s ≠ SX_CONS a d) ∧
   ((SEXSTR s = SX_STR s') ⇔ s' = encode_control s)
Proof
  rw[SEXSTR_def,EQ_IMP_THM]
QED

val odestSEXSTR_def = Define`
  (odestSEXSTR (SX_STR s) = decode_control s) ∧
  (odestSEXSTR _ = NONE)`;

Theorem encode_control_remove:
   ∀s. EVERY isPrint s ∧ #"\\" ∉ set s ⇒ encode_control s = s
Proof
  Induct \\ simp[encode_control_def]
QED

Theorem SEXSTR_remove:
   EVERY isPrint s ∧ #"\\" ∉ set s ⇒ SEXSTR s = SX_STR s
Proof
  rw[SEXSTR_def,encode_control_remove]
QED

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

Theorem sexppair_CONG[defncong]:
   ∀s1 s2 p1 p1' p2 p2'.
       s1 = s2 ∧
       (∀s. (∃s'. s2 = SX_CONS s s') ⇒ p1 s = p1' s) ∧
       (∀s. (∃s'. s2 = SX_CONS s' s) ⇒ p2 s = p2' s)
      ⇒
       sexppair p1 p2 s1 = sexppair p1' p2' s2
Proof
  simp[] >> Cases >> simp[sexppair_def]
QED


Theorem strip_sxcons_FAIL_sexplist_FAIL:
   ∀s. (strip_sxcons s = NONE) ⇒ (sexplist p s = NONE)
Proof
  Induct >> simp[Once strip_sxcons_def, Once sexplist_def] >>
  metis_tac[TypeBase.nchotomy_of ``:α option``]
QED

Theorem monad_bind_FAIL:
   monad_bind m1 (λx. fail) = fail
Proof
  Cases_on `m1` >> simp[]
QED

Theorem monad_unitbind_CONG[defncong]:
   ∀m11 m21 m12 m22.
      m11 = m12 ∧ (m12 = SOME () ⇒ m21 = m22) ⇒
      monad_unitbind m11 m21 = monad_unitbind m12 m22
Proof
  simp[] >> rpt gen_tac >> rename1 `m12 = SOME ()` >>
  Cases_on `m12` >> simp[]
QED

Theorem sexplist_CONG[defncong]:
   ∀s1 s2 p1 p2.
      (s1 = s2) ∧ (∀e. sxMEM e s2 ⇒ p1 e = p2 e) ⇒
      (sexplist p1 s1 = sexplist p2 s2)
Proof
  simp[sxMEM_def] >> Induct >> dsimp[Once strip_sxcons_def]
  >- (ONCE_REWRITE_TAC [sexplist_def] >> simp[] >>
      rename1 `strip_sxcons t` >> Cases_on `strip_sxcons t` >>
      simp[]
      >- (simp[strip_sxcons_FAIL_sexplist_FAIL, monad_bind_FAIL]) >>
      map_every qx_gen_tac [`p1`, `p2`] >> strip_tac >>
      Cases_on `p2 s2` >> simp[] >> fs[] >> metis_tac[]) >>
  simp[sexplist_def]
QED

Overload guard[local] = ``λb m. monad_unitbind (assert b) m``

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
        guard (s = "AtwordApp" ∧ LENGTH args = 1)
              (lift AtwordApp (odestSXNUM (EL 0 args))) ++
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
      else if nm = "AtwordApp" ∧ LENGTH args = 1 then
        OPTION_MAP AtwordApp (odestSXNUM (EL 0 args))
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

Theorem sexptype_alt_intro:
   (∀s. sexptype s = sexptype_alt s) ∧ (∀s. sexptype_list s = sexplist sexptype s)
Proof
  ho_match_mp_tac sexptype_alt_ind \\ rw[]
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
    TOP_CASE_TAC \\ fs[] )
QED

Theorem sexptype_alt_intro1:
   sexptype = sexptype_alt ∧ sexplist sexptype = sexptype_list
Proof
  rw[FUN_EQ_THM,sexptype_alt_intro]
QED

val sexplit_def = Define`
  sexplit s =
    lift (IntLit o (&)) (odestSXNUM s) ++
    lift StrLit (odestSEXSTR s) ++
    do
      (nm,args) <- dstrip_sexp s;
      (do
         assert(LENGTH args = 1);
         guard (nm = "-") (OPTION_BIND (odestSXNUM (HD args)) (λn. if n = 0 then NONE else SOME (IntLit (-&n)))) ++
         guard (nm = "char")
            do
              cs <- odestSEXSTR (HD args);
              assert(LENGTH cs = 1);
              return (Char (HD cs))
            od
        od) ++
      guard (nm = "word")
           do
             assert(LENGTH args = 2);
             wsize <- odestSXNUM (HD args);
             n <- odestSXNUM (EL 1 args);
             assert(n < 2 ** wsize);
             return (Word (fixwidth wsize (n2v n)))
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

Theorem sexppat_alt_intro:
   (∀s. sexppat s = sexppat_alt s) ∧ (∀s. sexppat_list s = sexplist sexppat s)
Proof
  ho_match_mp_tac sexppat_alt_ind \\ rw[]
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
    TOP_CASE_TAC \\ fs[] )
QED

Theorem sexppat_alt_intro1:
   sexppat = sexppat_alt ∧ sexplist sexppat = sexppat_list
Proof
  rw[FUN_EQ_THM,sexppat_alt_intro]
QED

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
  if s = "Opapp" then SOME Opapp else
  if s = "Opassign" then SOME Opassign else
  if s = "Opref" then SOME Opref else
  if s = "Opderef" then SOME Opderef else
  if s = "Aw8alloc" then SOME Aw8alloc else
  if s = "Aw8sub" then SOME Aw8sub else
  if s = "Aw8length" then SOME Aw8length else
  if s = "Aw8update" then SOME Aw8update else
  if s = "Aw8sub_unsafe" then SOME Aw8sub_unsafe else
  if s = "Aw8update_unsafe" then SOME Aw8update_unsafe else
  if s = "CopyStrStr" then SOME CopyStrStr else
  if s = "CopyStrAw8" then SOME CopyStrAw8 else
  if s = "CopyAw8Str" then SOME CopyAw8Str else
  if s = "CopyAw8Aw8" then SOME CopyAw8Aw8 else
  if s = "Ord" then SOME Ord else
  if s = "Chr" then SOME Chr else
  if s = "ChopbLt" then SOME (Chopb Lt) else
  if s = "ChopbGt" then SOME (Chopb Gt) else
  if s = "ChopbLeq" then SOME (Chopb Leq) else
  if s = "ChopbGeq" then SOME (Chopb Geq) else
  if s = "Implode" then SOME Implode else
  if s = "Explode" then SOME Explode else
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
  if s = "Asub_unsafe" then SOME Asub_unsafe else
  if s = "Aupdate_unsafe" then SOME Aupdate_unsafe else
  if s = "ConfigGC" then SOME ConfigGC else NONE) ∧
  (sexpop (SX_CONS (SX_SYM s) (SX_STR s')) =
     if s = "FFI" then OPTION_MAP FFI (decode_control s') else NONE
   ) ∧
  (sexpop (SX_CONS (SX_SYM s) (SX_NUM n)) =
    if s = "OpwAndw" then SOME (Opw n Andw) else
    if s = "OpwOrw" then SOME (Opw n Orw) else
    if s = "OpwXor" then SOME (Opw n Xor) else
    if s = "OpwAdd" then SOME (Opw n Add) else
    if s = "OpwSub" then SOME (Opw n Sub) else
    if s = "OpwbLtw" then SOME (Opwb n Ltw) else
    if s = "OpwbGtw" then SOME (Opwb n Gtw) else
    if s = "OpwbLeqw" then SOME (Opwb n Leqw) else
    if s = "OpwbGeqw" then SOME (Opwb n Geqw) else
    if s = "OpwbTest" then SOME (Opwb n Test) else
    if s = "OpwbLtSignw" then SOME (Opwb n LtSignw) else
    if s = "OpwbGtSignw" then SOME (Opwb n GtSignw) else
    if s = "OpwbLeqSignw" then SOME (Opwb n LeqSignw) else
    if s = "OpwbGeqSignw" then SOME (Opwb n GeqSignw) else
    if s = "WtoInt" then SOME (WordToInt n) else
    if s = "WfromInt" then SOME (WordFromInt n) else NONE) ∧
  (sexpop (SX_CONS (SX_SYM s) (SX_CONS (SX_NUM wsize) (SX_NUM n))) =
    if s = "ShiftLsl" then SOME (Shift wsize Lsl n) else
    if s = "ShiftLsr" then SOME (Shift wsize Lsr n) else
    if s = "ShiftAsr" then SOME (Shift wsize Asr n) else
    if s = "ShiftRor" then SOME (Shift wsize Ror n) else
    if s = "WtoW" then SOME (WordToWord wsize n) else NONE)∧
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

Theorem sexpexp_alt_intro:
   (∀s. sexpexp s = sexpexp_alt s) ∧
  (∀s. sexplist sexpexp s = sexpexp_list s) ∧
  (∀s. sexplist (sexppair sexppat sexpexp) s = sexppes s) ∧
  (∀s. sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) s = sexpfuns s) ∧
  (∀s. sexppair sexppat sexpexp s = sexppatexp s) ∧
  (∀s. sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp) s = sexpfun s)
Proof
  ho_match_mp_tac sexpexp_alt_ind \\ rw[]
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
    TOP_CASE_TAC \\ fs[])
QED

Theorem sexpexp_alt_intro1:
   sexpexp = sexpexp_alt ∧
   sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) = sexpfuns
Proof
  rw[FUN_EQ_THM,sexpexp_alt_intro]
QED

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

Theorem sexpdec_alt_intro:
   (∀s. sexpdec s = sexpdec_alt s) ∧
  (∀s. sexplist sexpdec s = sexpdec_list s)
Proof
  ho_match_mp_tac sexpdec_alt_ind \\ rw[]
  >- (
    rw[Once sexpdec_def,Once sexpdec_alt_def,sexppat_alt_intro1,sexpexp_alt_intro1,sexptype_alt_intro1]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[] \\ rfs[] \\ fsrw_tac[ETA_ss][] )
  >- (
    rw[Once sexplist_def,Once (CONJUNCT2 sexpdec_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
QED

Theorem sexpdec_alt_intro1:
   sexpdec = sexpdec_alt ∧
   sexplist sexpdec = sexpdec_list
Proof
  rw[FUN_EQ_THM,sexpdec_alt_intro]
QED

(* now the reverse: toSexp *)

val listsexp_def = Define`
  listsexp = FOLDR SX_CONS nil`;

Theorem listsexp_11[simp]:
   ∀ l1 l2. listsexp l1 = listsexp l2 ⇔ l1 = l2
Proof
  Induct >> gen_tac >> cases_on `l2` >> fs[listsexp_def]
QED

val optsexp_def = Define`
  (optsexp NONE = SX_SYM "NONE") ∧
  (optsexp (SOME x) = listsexp [SX_SYM "SOME"; x])`;

Theorem optsexp_11[simp]:
   optsexp o1 = optsexp o2 ⇔ o1 = o2
Proof
  cases_on `o1` >> cases_on `o2` >> fs[optsexp_def, listsexp_def]
QED

val idsexp_def = Define`
  (idsexp (Short n) = listsexp [SX_SYM"Short"; SEXSTR n]) ∧
  (idsexp (Long ns n) = listsexp [SX_SYM"Long"; SEXSTR ns; idsexp n])`;

Theorem idsexp_11[simp]:
   ∀ i1 i2. idsexp i1 = idsexp i2 ⇔ i1 = i2
Proof
  Induct >> gen_tac >> cases_on `i2` >> fs[idsexp_def]
QED

val typesexp_def = tDefine"typesexp"`
  (typesexp (Atvar s) = listsexp [SX_SYM "Atvar"; SEXSTR s]) ∧
  (typesexp (Atfun t1 t2) = listsexp [SX_SYM "Atfun"; typesexp t1; typesexp t2]) ∧
  (typesexp (Attup ts) = listsexp [SX_SYM "Attup"; listsexp (MAP typesexp ts)]) ∧
  (typesexp (Atapp ts tc) = listsexp [SX_SYM "Atapp"; listsexp (MAP typesexp ts); idsexp tc]) ∧
  (typesexp (AtwordApp n) = listsexp [SX_SYM "AtwordApp"; SX_NUM n])`
  (WF_REL_TAC`measure ast_t_size` >> rw[] \\
   Induct_on`ts` >> simp[ast_t_size_def] >>
   rw[] >> res_tac >> simp[]);

Theorem typesexp_11[simp]:
   ∀t1 t2. typesexp t1 = typesexp t2 ⇔ t1 = t2
Proof
  ho_match_mp_tac (theorem"typesexp_ind")
  \\ simp[typesexp_def]
  \\ rpt conj_tac \\ simp[PULL_FORALL]
  \\ CONV_TAC(RESORT_FORALL_CONV List.rev)
  \\ Cases \\ simp[typesexp_def]
  \\ srw_tac[ETA_ss][EQ_IMP_THM]
  \\ metis_tac[MAP_EQ_MAP_IMP]
QED

val litsexp_def = Define`
  (litsexp (IntLit i) =
   if i < 0 then listsexp [SX_SYM "-"; SX_NUM (Num(-i))]
            else SX_NUM (Num i)) ∧
  (litsexp (Char c) = listsexp [SX_SYM "char"; SEXSTR [c]]) ∧
  (litsexp (StrLit s) = SEXSTR s) ∧
  (litsexp (Word v) = listsexp [SX_SYM "word";SX_NUM
  (LENGTH v);SX_NUM (v2n v)])`;

Theorem litsexp_11[simp]:
   ∀l1 l2. litsexp l1 = litsexp l2 ⇔ l1 = l2
Proof
  Cases \\ Cases \\ rw[litsexp_def,EQ_IMP_THM,listsexp_def]
  >- intLib.COOPER_TAC
  >- intLib.COOPER_TAC
  >- metis_tac[v2n_same_length_11]
QED

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

Theorem patsexp_11[simp]:
   ∀p1 p2. patsexp p1 = patsexp p2 ⇔ p1 = p2
Proof
  ho_match_mp_tac (theorem"patsexp_ind")
  \\ rpt conj_tac \\ simp[PULL_FORALL]
  \\ CONV_TAC(RESORT_FORALL_CONV List.rev)
  \\ Cases \\ rw[patsexp_def,listsexp_def]
  \\ rw[EQ_IMP_THM]
  >- ( metis_tac[OPTION_MAP_INJ,idsexp_11] )
  \\ imp_res_tac FOLDR_SX_CONS_INJ
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ first_x_assum match_mp_tac
  \\ simp[] \\ metis_tac[]
QED

val lopsexp_def = Define`
  (lopsexp And = SX_SYM "And") ∧
  (lopsexp Or = SX_SYM "Or")`;

Theorem lopsexp_11[simp]:
   ∀l1 l2. lopsexp l1 = lopsexp l2 ⇔ l1 = l2
Proof
  Cases \\ Cases \\ simp[lopsexp_def]
QED

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
  (opsexp (Opw x Andw) = SX_CONS (SX_SYM "OpwAndw") (SX_NUM x)) ∧
  (opsexp (Opw x Orw) = SX_CONS (SX_SYM "OpwOrw") (SX_NUM x)) ∧
  (opsexp (Opw x Xor) = SX_CONS (SX_SYM "OpwXor") (SX_NUM x)) ∧
  (opsexp (Opw x Add) = SX_CONS (SX_SYM "OpwAdd") (SX_NUM x)) ∧
  (opsexp (Opw x Sub) = SX_CONS (SX_SYM "OpwSub") (SX_NUM x)) ∧
  (opsexp (Opwb x Ltw) = SX_CONS (SX_SYM "OpwbLtw") (SX_NUM x)) ∧
  (opsexp (Opwb x Gtw) = SX_CONS (SX_SYM "OpwbGtw") (SX_NUM x)) ∧
  (opsexp (Opwb x Leqw) = SX_CONS (SX_SYM "OpwbLeqw") (SX_NUM x)) ∧
  (opsexp (Opwb x Geqw) = SX_CONS (SX_SYM "OpwbGeqw") (SX_NUM x)) ∧
  (opsexp (Opwb x Test) = SX_CONS (SX_SYM "OpwbTest") (SX_NUM x)) ∧
  (opsexp (Opwb x LtSignw) = SX_CONS (SX_SYM "OpwbLtSignw") (SX_NUM x)) ∧
  (opsexp (Opwb x GtSignw) = SX_CONS (SX_SYM "OpwbGtSignw") (SX_NUM x)) ∧
  (opsexp (Opwb x LeqSignw) = SX_CONS (SX_SYM "OpwbLeqSignw") (SX_NUM x)) ∧
  (opsexp (Opwb x GeqSignw) = SX_CONS (SX_SYM "OpwbGeqSignw") (SX_NUM x)) ∧
  (opsexp (Shift x Lsl n) = SX_CONS (SX_SYM "ShiftLsl") (SX_CONS (SX_NUM x)
  (SX_NUM n))) ∧
  (opsexp (Shift x Lsr n) = SX_CONS (SX_SYM "ShiftLsr") (SX_CONS (SX_NUM x)
  (SX_NUM n))) ∧
  (opsexp (Shift x Asr n) = SX_CONS (SX_SYM "ShiftAsr") (SX_CONS (SX_NUM x)
  (SX_NUM n))) ∧
  (opsexp (Shift x Ror n) = SX_CONS (SX_SYM "ShiftRor") (SX_CONS (SX_NUM x)
  (SX_NUM n))) ∧
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
  (opsexp Opapp = SX_SYM "Opapp") ∧
  (opsexp Opassign = SX_SYM "Opassign") ∧
  (opsexp Opref = SX_SYM "Opref") ∧
  (opsexp Opderef = SX_SYM "Opderef") ∧
  (opsexp Aw8alloc = SX_SYM "Aw8alloc") ∧
  (opsexp Aw8sub = SX_SYM "Aw8sub") ∧
  (opsexp Aw8length = SX_SYM "Aw8length") ∧
  (opsexp Aw8update = SX_SYM "Aw8update") ∧
  (opsexp Aw8sub_unsafe = SX_SYM "Aw8sub_unsafe") ∧
  (opsexp Aw8update_unsafe = SX_SYM "Aw8update_unsafe") ∧
  (opsexp CopyStrStr = SX_SYM "CopyStrStr") ∧
  (opsexp CopyStrAw8 = SX_SYM "CopyStrAw8") ∧
  (opsexp CopyAw8Str = SX_SYM "CopyAw8Str") ∧
  (opsexp CopyAw8Aw8 = SX_SYM "CopyAw8Aw8") ∧
  (opsexp Ord = SX_SYM "Ord") ∧
  (opsexp Chr = SX_SYM "Chr") ∧
  (opsexp (WordFromInt x) = SX_CONS (SX_SYM "WfromInt") (SX_NUM x)) ∧
  (opsexp (WordToInt x) = SX_CONS (SX_SYM "WtoInt") (SX_NUM x))∧
  (opsexp (WordToWord src dest) = SX_CONS (SX_SYM "WtoW") (SX_CONS (SX_NUM src)
  (SX_NUM dest)))∧
  (opsexp (Chopb Lt) = SX_SYM "ChopbLt") ∧
  (opsexp (Chopb Gt) = SX_SYM "ChopbGt") ∧
  (opsexp (Chopb Leq)= SX_SYM "ChopbLeq") ∧
  (opsexp (Chopb Geq)= SX_SYM "ChopbGeq") ∧
  (opsexp Implode = SX_SYM "Implode") ∧
  (opsexp Explode = SX_SYM "Explode") ∧
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
  (opsexp Asub_unsafe = SX_SYM "Asub_unsafe") ∧
  (opsexp Aupdate_unsafe = SX_SYM "Aupdate_unsafe") ∧
  (opsexp ConfigGC = SX_SYM "ConfigGC") ∧
  (opsexp (FFI s) = SX_CONS (SX_SYM "FFI") (SEXSTR s))`;

Theorem sexpop_opsexp[simp]:
sexpop (opsexp op) = SOME op
Proof
  `?debug. debug () = op` by (qexists_tac `K op` \\ simp[])>>
  Cases_on`op`>>rw[sexpop_def,opsexp_def]>>
  TRY(MAP_FIRST rename1 [
        ‘Opn c1’, ‘Opb c1’, ‘Opw _ c1’, ‘Chopb c1’, ‘Shift _ c1 _’,
        ‘FP_cmp c1’, ‘FP_uop c1’, ‘FP_bop c1’, `FP_top c1`, ‘WordFromInt _’,
        ‘WordToInt _’, `Opwb _ c1`,`WordToWord _ _`
      ] >>
      Cases_on`c1` >> rw[sexpop_def,opsexp_def] >>
      Cases_on`c2` >> rw[sexpop_def,opsexp_def]) >>
  rw[sexpop_def,opsexp_def,SEXSTR_def]
QED

Theorem opsexp_11[simp]:
   ∀o1 o2. opsexp o1 = opsexp o2 ⇔ o1 = o2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM “sexpop”) >> simp[]
QED

val locnsexp_def = Define`
  locnsexp (Locs (locn n1 n2 n3) (locn n4 n5 n6)) =
    listsexp (MAP SX_NUM [n1;n2;n3;n4;n5;n6])`;

Theorem locnsexp_thm[compute]:
   locnsexp (Locs l1 l2) =
   listsexp [&(l1.row); &(l1.col); &(l1.offset);
             &(l2.row); &(l2.col); &(l2.offset)]
Proof
  Cases_on`l1` \\ Cases_on`l2` \\ rw[locnsexp_def]
QED

Theorem locnsexp_11[simp]:
   ∀l1 l2. locnsexp l1 = locnsexp l2 ⇔ l1 = l2
Proof
  Cases \\ Cases \\ rename [`locnsexp (Locs l1 l2) = locnsexp (Locs l3 l4)`] >>
  map_every Cases_on [`l1`, `l2`, `l3`, `l4`] >> rw[locnsexp_def]
QED

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

Theorem expsexp_11[simp]:
   ∀e1 e2. expsexp e1 = expsexp e2 ⇒ e1 = e2
Proof
  ho_match_mp_tac (theorem"expsexp_ind")
  \\ rpt conj_tac \\ simp[PULL_FORALL]
  \\ CONV_TAC(RESORT_FORALL_CONV List.rev)
  \\ Cases \\ rw[expsexp_def]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ TRY(first_x_assum match_mp_tac \\ rw[FORALL_PROD])
  \\ rpt(pairarg_tac \\ fs[])
  \\ metis_tac[OPTION_MAP_INJ,idsexp_11,simpleSexpTheory.sexp_11,SEXSTR_11]
QED

val type_defsexp_def = Define`
  type_defsexp = listsexp o
    MAP (λ(xs,x,ls).
      SX_CONS (listsexp (MAP SEXSTR xs))
        (SX_CONS (SEXSTR x)
          (listsexp (MAP (λ(y,ts). SX_CONS (SEXSTR y) (listsexp (MAP typesexp ts))) ls))))`;

Theorem type_defsexp_11[simp]:
   ∀t1 t2. type_defsexp t1 = type_defsexp t2 ⇔ t1 = t2
Proof
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
  \\ simp[INJ_DEF]
QED

Theorem dec1_size_eq:
   dec1_size xs = list_size dec_size xs
Proof
  Induct_on `xs` \\ fs [dec_size_def, list_size_def]
QED

Theorem mem_size_lemma:
   list_size sz xs < N ==> (MEM x xs ⇒ sz x < N)
Proof
  Induct_on `xs` \\ rw [list_size_def] \\ fs []
QED

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

Theorem decsexp_11[simp]:
   ∀d1 d2. decsexp d1 = decsexp d2 ⇔ d1 = d2
Proof
  ho_match_mp_tac(theorem"decsexp_ind")
  \\ rw[decsexp_def,EQ_IMP_THM] \\ fs[decsexp_def]
  \\ Cases_on`d2` \\ fs[decsexp_def] \\ rw[]
  \\ imp_res_tac (REWRITE_RULE[AND_IMP_INTRO] MAP_EQ_MAP_IMP)
  \\ TRY (first_x_assum match_mp_tac \\ rw[])
  \\ rpt(pairarg_tac \\ fs[])
QED

(* round trip *)

Theorem odestSXSTR_SOME[simp]:
   odestSXSTR s = SOME y ⇔ (s = SX_STR y)
Proof
  Cases_on`s`>>simp[odestSXSTR_def]
QED

Theorem odestSEXSTR_SOME[simp]:
   odestSEXSTR s = SOME y ⇔ (s = SEXSTR y)
Proof
  Cases_on`s`\\simp[odestSEXSTR_def,SEXSTR_def]
  \\ metis_tac[decode_encode_control,encode_decode_control]
QED

Theorem odestSXSTR_SX_STR[simp]:
   odestSXSTR (SX_STR s) = SOME s
Proof
  rw[odestSXSTR_def]
QED

Theorem odestSEXSTR_SEXSTR[simp]:
   odestSEXSTR (SEXSTR s) = SOME s
Proof
  rw[odestSEXSTR_def]
QED

Theorem odestSXNUM_SX_NUM[simp]:
   odestSXNUM (SX_NUM n) = SOME n
Proof
  EVAL_TAC
QED

Theorem odestSXSYM_SX_SYM[simp]:
   odestSXSYM (SX_SYM s) = SOME s
Proof
  EVAL_TAC
QED

Theorem odestSXNUM_SX_STR[simp]:
   odestSXNUM (SX_STR s) = NONE
Proof
  EVAL_TAC
QED

Theorem odestSXNUM_SEXSTR[simp]:
   odestSXNUM (SEXSTR s) = NONE
Proof
  EVAL_TAC
QED

Theorem odestSXSTR_listsexp[simp]:
   odestSXSTR (listsexp l) = NONE
Proof
  Cases_on`l`>>EVAL_TAC
QED

Theorem odestSEXSTR_listsexp[simp]:
   odestSEXSTR (listsexp l) = NONE
Proof
  Cases_on`l`>>EVAL_TAC
QED

Theorem odestSXNUM_listsexp[simp]:
   odestSXNUM (listsexp l) = NONE
Proof
  Cases_on`l`>>EVAL_TAC
QED

Theorem dstrip_sexp_SX_STR[simp]:
   dstrip_sexp (SX_STR s) = NONE
Proof
  EVAL_TAC
QED

Theorem dstrip_sexp_SEXSTR[simp]:
   dstrip_sexp (SEXSTR s) = NONE
Proof
  EVAL_TAC
QED

Theorem strip_sxcons_listsexp[simp]:
   strip_sxcons (listsexp ls) = SOME ls
Proof
  Induct_on`ls`>>rw[listsexp_def] >> simp[GSYM listsexp_def]
QED

Theorem dstrip_sexp_listsexp[simp]:
   (dstrip_sexp (listsexp ls) =
    case ls of (SX_SYM x::xs) => SOME (x,xs) | _ => NONE)
Proof
  BasicProvers.CASE_TAC >> rw[dstrip_sexp_def,listsexp_def] >>
  BasicProvers.CASE_TAC >> rw[GSYM listsexp_def]
QED

Theorem sexplist_listsexp_matchable:
   ∀g gl. (∀x. MEM x l ⇒ f (g x) = SOME x) ∧ (gl = MAP g l) ⇒
   sexplist f (listsexp gl) = SOME l
Proof
  Induct_on`l` >> simp[listsexp_def,Once sexplist_def] >>
  simp[GSYM listsexp_def] >> metis_tac[]
QED

Theorem sexplist_listsexp_rwt[simp]:
   (∀x. MEM x l ⇒ f (g x) = SOME x) ⇒
   (sexplist f (listsexp (MAP g l)) = SOME l)
Proof
  metis_tac[sexplist_listsexp_matchable]
QED

Theorem sexplist_listsexp_imp:
   sexplist f (listsexp l1) = SOME l2 ⇒
   ∀n. n < LENGTH l1 ⇒ f (EL n l1) = SOME (EL n l2)
Proof
  qid_spec_tac`l2`>>
  Induct_on`l1`>>simp[listsexp_def]>>simp[GSYM listsexp_def] >>
  simp[Once sexplist_def,PULL_EXISTS] >> rw[] >>
  Cases_on`n`>>simp[]
QED

Theorem sexpopt_optsexp[simp]:
   (∀y. (x = SOME y) ⇒ (f (g y) = x)) ⇒
   (sexpopt f (optsexp (OPTION_MAP g x)) = SOME x)
Proof
  Cases_on`x`>>EVAL_TAC >> simp[]
QED

Theorem sexpid_odestSEXSTR_idsexp[simp]:
   sexpid odestSEXSTR (idsexp i) = SOME i
Proof
  Induct_on `i` >> simp[idsexp_def] >>
  rw [Once sexpid_def]
QED

Theorem sexptype_typesexp[simp]:
   sexptype (typesexp t) = SOME t
Proof
  qid_spec_tac`t` >>
  ho_match_mp_tac type_ind >>
  conj_tac >- rw[Once sexptype_def,typesexp_def] >>
  conj_tac >- (rw[] \\ rw[Once sexptype_def,typesexp_def]) >>
  conj_tac >- (
  Induct_on`l`>>rw[typesexp_def] >- (
    rw[Once sexptype_def,sexplist_listsexp_matchable] ) >> fs[] >>
  rw[Once sexptype_def] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  match_mp_tac sexplist_listsexp_matchable >>
  fs[typesexp_def] >> rw[] >> rw[] >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[])
  \\ conj_tac >-(
  Induct_on`l`>>rw[typesexp_def] >- (
    rw[Once sexptype_def,sexplist_listsexp_matchable] ) >> fs[] >>
  rw[Once sexptype_def] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  match_mp_tac sexplist_listsexp_matchable >>
  fs[typesexp_def] >> rw[] >> rw[] >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[])
  \\ rw[typesexp_def,Once sexptype_def]
QED

val exists_g_tac =
  (fn (g as (asl,w)) =>
    let
      val (x,b) = dest_exists w
      val tm = find_term (fn y => type_of x = type_of y andalso not (is_var y)) b
    in EXISTS_TAC tm end g)

Theorem sexptype_def_type_defsexp[simp]:
   sexptype_def (type_defsexp l) = SOME l
Proof
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
  simp[rich_listTheory.EL_MAP]
QED

Theorem LOG_v2n:
   !v. v <> [] /\ HD v ==>
     (LOG 2 (v2n v) = PRE (LENGTH v))
Proof
   rw[]
   \\ simp[v2n_def,num_from_bin_list_def]
   \\ mp_tac(Q.SPEC`2` LOG_l2n)
   \\ rw[]
   \\ pop_assum (mp_tac o Q.SPEC`bitify [] v`)
   \\ simp[]
   \\ strip_tac \\ pop_assum match_mp_tac
   \\ simp[every_bit_bitify,bitify_reverse_map]
   \\ Q.PAT_ABBREV_TAC`X = MAP _ _`
   \\ `X <> []` by (UNABBREV_ALL_TAC
       \\ Cases_on`v` \\ fs[]
   )
   \\ simp[LAST_REVERSE]
   \\ UNABBREV_ALL_TAC
   \\ Cases_on`v` \\ fs[]
QED

val v2n_cons = Q.prove(`
  (v2n (T::ls) = 2**LENGTH ls + v2n ls) ∧
  (v2n (F::ls) = v2n ls)`,
  rw[]>>
  ONCE_REWRITE_TAC[CONS_APPEND]>>
  simp[v2n_append]>>
  EVAL_TAC>>fs[]);

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)


Theorem testbit_n2v:
   !i x. testbit i (n2v x) = (BIT i x /\ i < LENGTH (n2v x))
Proof
   rw[]
   \\ simp[testbit]
   \\ Cases_on`i<LENGTH (n2v x)` \\ simp[]
   \\ simp[n2v_def]
   \\ simp[boolify_reverse_map]
   \\ Q.MATCH_ABBREV_TAC`EL N (REVERSE X) <=> _`
   \\ `N < LENGTH X` by (UNABBREV_ALL_TAC \\ simp[]
      \\ simp[num_to_bin_list_def]
      \\ simp[Once n2l_def]
      \\ TOP_CASE_TAC \\ simp[]
   )
   \\ simp[EL_REVERSE]
   \\ simp[Abbr`X`]
   \\ Q.MATCH_ABBREV_TAC`EL M (MAP _ X) <=> _`
   \\ `M < LENGTH X` by (UNABBREV_ALL_TAC \\ simp[]
      \\ simp[num_to_bin_list_def,Once n2l_def]
      \\ rw[]
      >-(`!x. PRE (1 - x) = 0` by rw[] \\ simp[]
         \\ simp[Once n2l_def])
      \\ ASSUME_TAC(Q.SPECL[`x`,`2`] n2l_def)
      \\ simp[])
   \\ simp[EL_MAP]
   \\ simp[Abbr`X`]
   \\ fs[num_to_bin_list_def,EL_n2l]
   \\ UNABBREV_ALL_TAC
   \\ fs[n2v_def,num_to_bin_list_def]
   \\ fs[boolify_reverse_map]
   \\ simp[GSYM ADD1]
   \\ simp[bitTheory.BIT_def,bitTheory.BITS_THM]
   \\ `!x. x MOD 2 = 0 <=> x MOD 2 <> 1` by (
      rw[] \\ eq_tac \\ rw[]
      \\ rename1`y MOD 2 = 0`
      \\ mp_tac(Q.SPECL[`y`,`2`]MOD_LESS)
      \\ impl_tac >- simp[]
      \\ strip_tac
      \\ DECIDE_TAC
   )
  \\ simp[]
QED

Theorem v2n_MOD2:
  !x. v2n x MOD 2 = if x=[] then 0 else if LAST x then 1 else 0
Proof
  rw[]
  >- EVAL_TAC
  \\ (simp[v2n_def,bitify_reverse_map]
     \\ simp[numposrepTheory.num_from_bin_list_def]
     \\ Cases_on`REVERSE x` \\ fs[]
     \\ fs[SWAP_REVERSE_SYM]
     \\ simp[REVERSE_APPEND]
     \\ ONCE_REWRITE_TAC[numposrepTheory.l2n_def]
     \\ simp[])
QED


Theorem TWO_EXP_SUC_GT1:
  !n. 1<2 ** (SUC n)
Proof
  Induct_on `n` \\ simp[Once EXP]
QED


Theorem v2n_DIV_2EXP_shiftr:
  !i x. v2n x DIV 2**i = v2n (shiftr x i)
Proof
  rw[] \\ Cases_on`LENGTH x = 0`
  >- (Cases_on`x` \\ fs[]
      \\ `v2n [] = 0` by (simp[v2n_def,numposrepTheory.num_from_bin_list_def]
          \\ simp[bitify_def]
          \\ simp[numposrepTheory.l2n_def]
      )
      \\ fs[]
      \\ simp[shiftr_def]
      \\ Cases_on`1 < 2 ** i`
      >- simp[DIV_EQ_0]
      \\ Cases_on`i` \\ fs[TWO_EXP_SUC_GT1]
  )
  \\ fs[shiftr_def]
  \\ Induct_on`i`
  >- fs[]
  \\ simp[EXP]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[GSYM DIV_DIV_DIV_MULT]
  \\ Q.MATCH_ABBREV_TAC`v2n X DIV 2 = v2n Y`
  \\ `Y = shiftr X 1` by (UNABBREV_ALL_TAC \\ simp[shiftr_def]
     \\ simp[ADD1]
     \\ match_mp_tac (MP_CANON(GSYM TAKE_TAKE))
     \\ simp[])
  \\ fs[]
  \\ clean_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp[shiftr_def]
  \\ match_mp_tac DIV_UNIQUE
  \\ Cases_on`REVERSE X`
  \\ fs[]
  >- simp[v2n_def,bitify_reverse_map]
  \\ fs[SWAP_REVERSE_SYM]
  \\ fs[v2n_append]
  \\ simp[TAKE_APPEND,TAKE_LENGTH_TOO_LONG]
  \\ rename1`v2n [h]`
  \\ qexists_tac`v2n [h]` \\ simp[]
  \\ Cases_on`h` \\ EVAL_TAC
QED

Theorem EL_bitstring_BIT_v2n:
  !i x. i < LENGTH x ==> (EL i x = BIT (LENGTH x -i-1) (v2n x))
Proof
  rw[]
  \\ simp[bitTheory.BITS_THM,bitTheory.BIT_def]
  \\ simp[v2n_DIV_2EXP_shiftr]
  \\ simp[v2n_MOD2]
  \\ simp[shiftr_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ simp[GSYM ELL]
  \\ simp[ELL_EL]
  \\ `PRE (i+1)=i` by simp[]
  \\ ASM_REWRITE_TAC[]
  \\ simp[EL_TAKE]
  \\ TOP_CASE_TAC \\ simp[]
QED

Theorem dropWhile_MAP:
  !f g l. dropWhile f (MAP g l) = MAP g (dropWhile (f o g) l)
Proof
  rw[] \\ Induct_on `l`
  >- EVAL_TAC
  \\ EVAL_TAC
  \\ rw[]
QED

Theorem HD_MAP:
 !z f. z <> [] ==> (HD (MAP f z) = f (HD z))
Proof
  Cases \\ fs[]
QED


val GENLIST_K_REVERSE_SUC = Q.prove(`!x y. GENLIST (K x) (SUC y) = [x] ++ GENLIST (K x) y`,
  rw[LIST_EQ_REWRITE] \\ rename1 `EL i _` \\ Cases_on `i` \\ simp[EL]
)

val EVERY_EQ_GENLIST = Q.prove(`!l x. EVERY ($= x) l = (l = GENLIST (K x) (LENGTH l))`,
     Induct \\ fs[] \\ rpt STRIP_TAC \\ EQ_TAC \\ rw[] \\ fs[GENLIST_K_REVERSE_SUC]
)

val GENLIST_K_EVERY = Q.prove(`!x y. (y = GENLIST (K x) (LENGTH y)) = EVERY ($=x) y`,
 simp[EVERY_EQ_GENLIST]
 )

Theorem fixwidth_n2v_v2n:
   !x. fixwidth (LENGTH x) (n2v (v2n x)) = x
Proof
   rw[]
   \\ GEN_REWRITE_TAC (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM
   fixwidth_id]
   \\ simp[fixwidth_eq]
   \\ simp[testbit_n2v]
   \\ simp[testbit]
   \\ rw[]
   \\ simp[EL_bitstring_BIT_v2n]
   \\ Cases_on`i< LENGTH (n2v (v2n x))` \\ fs[]
   \\ simp[bitTheory.BITS_THM,bitTheory.BIT_def]
   \\ simp[v2n_DIV_2EXP_shiftr]
   \\ simp[v2n_MOD2]
   \\ TOP_CASE_TAC \\ fs[]
   \\ simp[GSYM ELL]
   \\ simp[ELL_EL]
   \\ TOP_CASE_TAC \\ simp[]
   \\ pop_assum mp_tac \\ simp[]
   \\ simp[shiftr_def]
   \\ simp[EL_TAKE]
   \\ fs[n2v_def,v2n_def]
   \\ fs[num_to_bin_list_def,num_from_bin_list_def]
   \\ fs[every_bit_bitify,n2l_l2n]
   \\ FULL_CASE_TAC \\ fs[]
   >-(fs[boolify_reverse_map]
      \\ fs[l2n_eq_0]
      \\ fs[bitify_reverse_map]
      \\ fs[EVERY_REVERSE,EVERY_MAP]
      \\ Q.MATCH_ASMSUB_ABBREV_TAC`EVERY G _`
      \\ `G = $~` by (
         simp[Abbr`G`]
         \\ GEN_REWRITE_TAC(ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX]
         \\ ABS_TAC
         \\ TOP_CASE_TAC \\ fs[]
      )
      \\ fs[]
      \\ ntac 2 (pop_assum kall_tac)
      \\ Induct_on`x` \\ fs[EVERY_DEF]
      \\ rw[]
      \\ fs[]
      \\ Cases_on`i<LENGTH x` \\ fs[]
      >-(Cases_on`x=[]` \\ fs[]
         \\ fs[shiftr_def]
         \\ rw[]
         \\ `PRE (SUC (LENGTH x) - i) = LENGTH x - i` by DECIDE_TAC
         \\ simp[]
         \\ fs[] \\ rw[]
         \\ Cases_on`LENGTH x - i` \\ fs[EL]
      )
      \\ `PRE (SUC (LENGTH x) - i) = 0` by DECIDE_TAC
      \\ fs[]
   )
   \\ fs[boolify_reverse_map]
   \\ fs[l2n_eq_0]
   \\ fs[bitify_reverse_map]
   \\ fs[EXISTS_REVERSE]
   \\ fs[EXISTS_MAP]
   \\ Q.MATCH_ASMSUB_ABBREV_TAC`EXISTS G _`
   \\ `G = I` by (
         simp[Abbr`G`,I_DEF,K_DEF,S_DEF]
         \\ ABS_TAC
         \\ TOP_CASE_TAC \\ fs[])
   \\ fs[]
   \\ ntac 2 (pop_assum kall_tac)
   \\ reverse(fs[LENGTH_TAKE_EQ_MIN])
   >-rfs[]
   \\ Q.MATCH_ASMSUB_ABBREV_TAC`l2n _ L`
   \\ `EVERY ($> 2) L` by (
       simp[Abbr`L`]
       \\ simp[EVERY_REVERSE,EVERY_MAP]
       \\ Q.MATCH_ABBREV_TAC`EVERY X _`
       \\ `X = K T`by (simp[Abbr`X`]
          \\ simp[K_DEF]
          \\ ABS_TAC \\ TOP_CASE_TAC \\ simp[]
       )
       \\ fs[]
       \\ rpt (pop_assum kall_tac)
       \\ Induct_on`x` \\ fs[]
   )
   \\ mp_tac (Q.SPEC`2` LOG_l2n) \\ simp[]
   \\ strip_tac \\ pop_assum (qspec_then`L`mp_tac)
   \\ Cases_on`L=[]`
   >-(simp[Abbr`L`]
      \\ fs[]
   )
   \\ fs[]
   \\ Cases_on`0 < LAST L` \\ fs[]
   >- (rw[] \\ fs[]
       \\ `SUC (PRE (LENGTH L)) = LENGTH L` by (Cases_on`LENGTH L` \\ fs[])
       \\ fs[]
       \\ `LENGTH L = LENGTH x` by (UNABBREV_ALL_TAC \\ fs[])
       \\ fs[]
   )
   \\ mp_tac(Q.SPECL[`2`,`L`] LOG_l2n_dropWhile) \\ simp[]
   \\ Q.MATCH_ABBREV_TAC`(P ==> _) ==> _`
   \\ Cases_on`P`
   >-(fs[] \\ rw[] \\ fs[]
      \\ UNABBREV_ALL_TAC \\ fs[]
      \\ fs[EVERY_REVERSE,EVERY_MAP,EXISTS_REVERSE,EXISTS_MAP]
      \\ fs[dropWhile_MAP]
      \\ Q.MATCH_ASMSUB_ABBREV_TAC`LAST (REVERSE X) = 0`
      \\ `X <> []` by (UNABBREV_ALL_TAC \\ fs[])
      \\ fs[LAST_REVERSE]
      \\ simp[Abbr`X`]
      \\ fs[HD_MAP]
      \\ Cases_on`HD x` \\ fs[]
      \\ rw[]
      \\ Cases_on`x` \\ fs[]
      \\ `PRE (SUC (LENGTH t) - i) = LENGTH t - i` by DECIDE_TAC
      \\ ASM_REWRITE_TAC[]
      \\ fs[]
      \\ Cases_on`h` \\ rw[]
      \\ fs[l2n_2_append]
      \\ Induct_on`t` \\ fs[]
      \\ strip_tac
      \\ strip_tac \\ simp[]
      \\ simp[shiftr_def]
      \\ `!h. (2:num) > (if h then 1 else 0)` by (rw[])
      \\ simp[]
      \\ reverse (Cases_on`shiftr (F::t) i <> []`) \\ fs[]
      >-(fs[shiftr_def]
         \\ `i = SUC (LENGTH t)` by DECIDE_TAC
         \\ fs[]
      )
      \\ Cases_on`h` \\ fs[]
      >-(Cases_on`EXISTS I t`
         >- (fs[]
            \\ rw[] \\ fs[]
            \\ rw[]
            \\ `i = SUC (LENGTH t)` by DECIDE_TAC
            \\ fs[]
         )
         \\ last_x_assum mp_tac
         \\ ASM_REWRITE_TAC[]
         \\ ntac 2 strip_tac
         \\ `i = SUC (LENGTH t)` by DECIDE_TAC \\ simp[]
      )
    \\ reverse(Cases_on`i < SUC (LENGTH t)` \\ fs[])
    >-(`i = SUC (LENGTH t)` by DECIDE_TAC
       \\ fs[]
    )
    \\ rw[]
    \\ last_x_assum mp_tac
    \\ fs[]
    \\ fs[l2n_2_append]
    \\ `SUC (LENGTH t) - i = SUC (LENGTH t - i)`by simp[]
    \\ simp[]
   )
   \\ simp[]
   \\ `~F` by simp[]
   \\ UNABBREV_ALL_TAC
   \\ Q.MATCH_ASMSUB_ABBREV_TAC`l2n 2 L`
   \\ fs[NOT_EXISTS]
   \\ fs[o_DEF]
   \\ simp[Abbr`L`]
   \\ fs[EVERY_REVERSE]
   \\ fs[EVERY_MAP]
   \\ Q.MATCH_ASMSUB_ABBREV_TAC`EVERY G x`
   \\ `G = $~` by (
      GEN_REWRITE_TAC(ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX]
      \\ simp[Abbr`G`] \\ ABS_TAC
      \\ TOP_CASE_TAC \\ simp[])
   \\ fs[]
   \\ ntac 2 (pop_assum kall_tac)
   \\ fs[Once NOT_DEF]
   \\ `(\t. ~t) = ($= F)` by (
      GEN_REWRITE_TAC(ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX]
      \\ simp[]
   )
   \\ fs[]
   \\ fs[EVERY_EQ_GENLIST]
   \\ ONCE_ASM_REWRITE_TAC[]
   \\ simp[]
QED

Theorem sexplit_litsexp[simp]:
   sexplit (litsexp l) = SOME l
Proof
  `?debug. debug () = l`by (qexists_tac`K l` \\ simp[])
  \\ Cases_on`l`>>simp[sexplit_def,litsexp_def]
  >- (
    rw[] >> intLib.ARITH_TAC ) >>
  rw[]
  >- simp[v2n_lt]
  \\ simp[fixwidth_n2v_v2n]
QED

Theorem sexppat_patsexp[simp]:
   sexppat (patsexp p) = SOME p
Proof
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
  rw[] >> simp[patsexp_def,Once sexppat_def]
QED

Theorem sexplop_lopsexp[simp]:
   sexplop (lopsexp l) = SOME l
Proof
  Cases_on`l`>>EVAL_TAC
QED

Theorem sexplocn_locnsexp[simp]:
   sexplocn (locnsexp l) = SOME l
Proof
  Cases_on `l` >> rename [`Locs l1 l2`] >>
  Cases_on`l1` \\ Cases_on`l2` \\ rw[locnsexp_def,sexplocn_def]
QED

Theorem sexpexp_expsexp[simp]:
   sexpexp (expsexp e) = SOME e
Proof
  qid_spec_tac`e` >>
  ho_match_mp_tac exp_ind >> rw[] >>
  rw[expsexp_def] >> rw[Once sexpexp_def] >>
  match_mp_tac sexplist_listsexp_matchable >>
  exists_g_tac >> simp[] >>
  fs[listTheory.EVERY_MEM] >>
  qx_gen_tac`p`>>PairCases_on`p` >> simp[] >>
  simp[sexppair_def] >>
  rw[] >> res_tac >> fs[]
QED

Theorem sexpdec_decsexp[simp]:
   ∀d. sexpdec (decsexp d) = SOME d
Proof
  ho_match_mp_tac dec_ind
  \\ rw[decsexp_def]
  \\ rw[Once sexpdec_def]
  \\ match_mp_tac sexplist_listsexp_matchable
  \\ exists_g_tac >> simp[] \\ fs[EVERY_MEM]
  \\ qx_gen_tac`p`>>PairCases_on`p`>>rw[]
  \\ simp[sexppair_def]
QED

Theorem sexpopt_SOME:
   sexpopt f s = SOME opt ⇒
   ∃x. s = optsexp x ∧
       (case x of NONE => opt = NONE | SOME s => IS_SOME opt ∧ opt = f s)
Proof
  rw[sexpopt_def]
  \\ Cases_on`odestSXSYM s` \\ fs[dstrip_sexp_SOME] \\ rw[]
  \\ fs[odestSXSYM_def] \\ simp[EXISTS_OPTION, optsexp_def, listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[] \\ fs[] \\ rw[]
  >- (qexists_tac `SOME e1` \\ fs [] \\ EVAL_TAC)
  \\ rename[`odestSXSYM s = SOME _`] >> Cases_on `s`
  \\ fs[odestSXSYM_def, dstrip_sexp_def]
  \\ qexists_tac `NONE` \\ fs [] \\ EVAL_TAC
QED

Theorem listsexp_MAP_EQ_f:
   (∀x. MEM x ls ⇒ f1 x = f2 x) ⇒
    listsexp (MAP f1 ls) = listsexp (MAP f2 ls)
Proof
  Induct_on`ls` >> simp[] >> fs[listsexp_def]
QED

Theorem sexplist_SOME:
   sexplist f s = SOME ls ⇒ ∃l. s = listsexp l ∧ MAP f l = MAP SOME ls
Proof
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
  qexists_tac`a::l` >> simp[listsexp_def]
QED

Theorem sexppair_SOME:
   sexppair f1 f2 s = SOME p ⇒ ∃x y. f1 x = SOME (FST p) ∧ f2 y = SOME (SND p) ∧ s = SX_CONS x y
Proof
  rw[sexppair_def]
  \\ every_case_tac \\ fs[]
QED

Theorem OPTION_CHOICE_EQ_SOME:
   OPTION_CHOICE m1 m2 = SOME x ⇔
    m1 = SOME x ∨ m1 = NONE ∧ m2 = SOME x
Proof
  Cases_on `m1` >> simp[]
QED

Theorem dstrip_sexp_EQ_SOME:
   dstrip_sexp s = SOME (nm, args) ⇔
   ∃t. s = SX_CONS (SX_SYM nm) t ∧ strip_sxcons t = SOME args
Proof
  Cases_on`s` >> simp[dstrip_sexp_def] >> every_case_tac >>
  simp[] >> metis_tac[]
QED

Theorem v2n_longer_fixwidth_n2v:
   !x n. n < 2 ** x ==> v2n(fixwidth x (n2v n)) = n
Proof
   rw[]
   \\ Cases_on`x = 0`
   >- (fs[] \\ EVAL_TAC)
   \\ `LENGTH (n2v n) <= x` by (
      simp[LENGTH_n2v]
      \\ TOP_CASE_TAC \\ fs[]
      \\ `LOG 2 n < x` suffices_by simp[]
      \\ mp_tac(Q.SPECL[`2`,`LOG 2 n`,`x`]logrootTheory.LT_EXP_ISO)
      \\ impl_tac >- simp[]
      \\ strip_tac \\ ASM_REWRITE_TAC[]
      \\ match_mp_tac LESS_EQ_LESS_TRANS
      \\ qexists_tac`n` \\ simp[]
      \\ simp[logrootTheory.LOG]
   )
   \\ simp[v2n_fixwidth]
QED

Theorem litsexp_sexplit:
   ∀s l. sexplit s = SOME l ⇒ litsexp l = s
Proof
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
  \\ Cases_on`e1` \\ fs[odestSXNUM_def,v2n_longer_fixwidth_n2v]
  \\ Cases_on`e2` \\ fs[odestSXNUM_def]
QED

Theorem idsexp_sexpid_odestSEXSTR:
   ∀y x. sexpid odestSEXSTR x = SOME y ⇒ x = idsexp y
Proof
  Induct
  \\ rw[Once sexpid_def]
  \\ fs[dstrip_sexp_SOME] \\ rw[]
  \\ fs[]
  \\ fs[OPTION_CHOICE_EQ_SOME]
  \\ rw[idsexp_def,listsexp_def]
  \\ fs[quantHeuristicsTheory.LIST_LENGTH_3] \\ rw[]
  \\ fs[]
  \\ fs[Once strip_sxcons_def]
  \\ every_case_tac \\ fs[]
QED

Theorem strip_sxcons_NIL[simp]:
   strip_sxcons ⟪ ⟫ = SOME []
Proof
  simp[Once strip_sxcons_def]
QED

Theorem strip_sxcons_SXCONS[simp]:
   strip_sxcons (SX_CONS s1 s2) = lift (CONS s1) (strip_sxcons s2)
Proof
  simp[Once strip_sxcons_def]
QED

Theorem typesexp_sexptype:
   ∀s t. sexptype s = SOME t ⇒ typesexp t = s
Proof
  ho_match_mp_tac(theorem"sexptype_ind")
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[Once sexptype_def]
  \\ fs[dstrip_sexp_SOME,PULL_EXISTS]
  \\ rw[]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ rename1`guard (nm = "Atvar" ∧ _) _`
  \\ reverse (Cases_on `nm ∈ {"Atvar"; "Atfun"; "Attup"; "Atapp";"AtwordApp"}`) >- fs[]
  \\ pop_assum mp_tac >> simp[]
  \\ reverse(strip_tac) \\ fs[typesexp_def, listsexp_def]
  \\ fs[LENGTH_EQ_NUM_compute, PULL_EXISTS]
  \\ rw[] \\ fs[]
  \\ fs[GSYM listsexp_def]
  \\ imp_res_tac idsexp_sexpid_odestSEXSTR \\ simp[]
  \\ imp_res_tac sexplist_SOME \\ rw[]
  \\ fs[LIST_EQ_REWRITE,EL_MAP]
  \\ rfs[EL_MAP]
  \\ rpt strip_tac \\ res_tac
  >- (rename1 `odestSXNUM x` \\ Cases_on`x` \\ fs[odestSXNUM_def])
  \\ first_x_assum(MATCH_MP_TAC o MP_CANON)
  \\ simp[sxMEM_def]
  \\ metis_tac[MEM_EL]
QED

Theorem patsexp_sexppat:
   ∀s p. sexppat s = SOME p ⇒ patsexp p = s
Proof
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
  \\ metis_tac[MEM_EL]
QED

Theorem opsexp_sexpop:
   sexpop s = SOME p ⇒ opsexp p = s
Proof
  Cases_on`s` \\ rw[sexpop_def] \\ rw[opsexp_def]
  \\ match1_tac(mg.aub`s_:sexp`,(fn(a,t)=>if is_var(t"s") then Cases_on`^(t"s")`\\fs[sexpop_def] else NO_TAC))
  \\ match1_tac(mg.aub`s_:sexp`,(fn(a,t)=>if is_var(t"s") then Cases_on`^(t"s")`\\fs[sexpop_def] else NO_TAC))
  \\ pop_assum mp_tac
  \\ rpt IF_CASES_TAC \\ rw[]
  \\ rw[opsexp_def, GSYM encode_decode_control]
  \\ rename1`SX_CONS (SX_SYM x) (SX_CONS y z)`
  \\ Cases_on`y` \\ fs[sexpop_def]
  \\ Cases_on`z` \\ fs[sexpop_def]
  \\ rpt FULL_CASE_TAC \\ rw[] \\ simp[opsexp_def]
QED

Theorem lopsexp_sexplop:
   sexplop s = SOME z ⇒ lopsexp z = s
Proof
  Cases_on`s` \\ rw[sexplop_def] \\ rw[lopsexp_def]
QED

Theorem locnsexp_sexplocn:
   sexplocn s = SOME z ⇒ locnsexp z = s
Proof
  Cases_on`z` \\ rename [`Locs l1 l2`] >>
  Cases_on`l1` \\ Cases_on `l2`
  \\ rw[sexplocn_def,locnsexp_def]
  \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
  \\ fs[Once strip_sxcons_def]
  \\ simp[listsexp_def]
  \\ rename [`⟪h1; h2; h3; h4; h5; h6⟫`]
  \\ map_every (fn q => Cases_on q >> fs[odestSXNUM_def])
       [`h1`, `h2`, `h3`, `h4`, `h5`, `h6`]
QED

Theorem expsexp_sexpexp:
   ∀s e. sexpexp s = SOME e ⇒ expsexp e = s
Proof
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
      \\ fs[sxMEM_def] \\ metis_tac[MEM_EL])
QED

Theorem type_defsexp_sexptype_def:
   sexptype_def s = SOME x ⇒ type_defsexp x = s
Proof
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
  \\ metis_tac[typesexp_sexptype]
QED

Theorem decsexp_sexpdec:
   ∀s d. sexpdec s = SOME d ⇒ decsexp d = s
Proof
  ho_match_mp_tac(theorem"sexpdec_ind")
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
  \\ metis_tac[MEM_EL]
QED

(* valid sexps *)

Theorem SEXSTR_valid[simp]:
   valid_sexp (SEXSTR s)
Proof
  rw[SEXSTR_def,EVERY_isPrint_encode_control]
QED

Theorem listsexp_valid:
   ∀ls. EVERY valid_sexp ls ⇒ valid_sexp (listsexp ls)
Proof
  Induct \\ simp[listsexp_def] \\ simp[GSYM listsexp_def]
  \\ EVAL_TAC
QED

Theorem idsexp_valid[simp]:
   ∀i. valid_sexp (idsexp i)
Proof
  Induct \\ simp[idsexp_def] >>
  rw []
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ EVAL_TAC
QED

Theorem typesexp_valid[simp]:
   ∀t. valid_sexp (typesexp t)
Proof
  ho_match_mp_tac(theorem"typesexp_ind")
  \\ rw[typesexp_def]
  \\ match_mp_tac listsexp_valid
  \\ simp[]
  \\ rpt conj_tac
  \\ TRY (match_mp_tac listsexp_valid)
  \\ simp[EVERY_MAP,EVERY_MEM]
  \\ EVAL_TAC
QED

Theorem litsexp_valid[simp]:
   ∀l. valid_sexp (litsexp l)
Proof
  Cases \\ rw[litsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[] \\ EVAL_TAC
QED

Theorem optsexp_valid:
   ∀x. (∀y. x = SOME y ⇒ valid_sexp y) ⇒ valid_sexp (optsexp x)
Proof
  Cases \\ rw[optsexp_def]
  \\ TRY(match_mp_tac listsexp_valid) \\ rw[]
  \\ EVAL_TAC
QED

Theorem patsexp_valid[simp]:
   ∀p. valid_sexp (patsexp p)
Proof
  ho_match_mp_tac(theorem"patsexp_ind")
  \\ rw[patsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY (match_mp_tac optsexp_valid \\ rw[] \\ rw[])
  \\ TRY (match_mp_tac listsexp_valid \\ simp[EVERY_MAP,EVERY_MEM])
  \\ EVAL_TAC
QED

Theorem type_defsexp_valid[simp]:
   ∀t. valid_sexp (type_defsexp t)
Proof
  rw[type_defsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
  \\ pairarg_tac \\ rw[]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
  \\ pairarg_tac \\ rw[]
  \\ match_mp_tac listsexp_valid
  \\ rw[EVERY_MEM,EVERY_MAP]
QED

Theorem opsexp_valid[simp]:
   ∀op. valid_sexp (opsexp op)
Proof
  Cases \\ simp[opsexp_def]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ TRY(Cases_on`o'`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`w`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`s`) \\ simp[opsexp_def]
  \\ TRY(Cases_on`f`) \\ simp[opsexp_def]
  \\ EVAL_TAC
QED

Theorem lopsexp_valid[simp]:
   ∀l. valid_sexp (lopsexp l)
Proof
  Cases \\ simp[lopsexp_def]
  \\ EVAL_TAC
QED

Theorem locnsexp_valid[simp]:
   ∀l. valid_sexp (locnsexp l)
Proof
  Cases \\ rename [`Locs l1 l2`] >> Cases_on `l1` \\ Cases_on `l2` \\ EVAL_TAC
QED

Theorem expsexp_valid[simp]:
   ∀e. valid_sexp (expsexp e)
Proof
  ho_match_mp_tac(theorem"expsexp_ind")
  \\ rw[expsexp_def]
  \\ TRY(match_mp_tac listsexp_valid)
  \\ rw[]
  \\ TRY(EVAL_TAC \\ NO_TAC)
  \\ TRY(match_mp_tac optsexp_valid \\ rw[] \\ rw[])
  \\ TRY(match_mp_tac listsexp_valid \\ simp[EVERY_MAP,EVERY_MEM])
  \\ simp[FORALL_PROD]
  \\ first_x_assum MATCH_ACCEPT_TAC
QED

Theorem decsexp_valid[simp]:
   ∀d. valid_sexp (decsexp d)
Proof
  ho_match_mp_tac dec_ind \\ rw[decsexp_def]
  \\ match_mp_tac listsexp_valid
  \\ rw[]
  \\ TRY (EVAL_TAC \\ NO_TAC)
  \\ match_mp_tac listsexp_valid
  \\ simp[EVERY_MAP,EVERY_MEM]
  \\ simp[FORALL_PROD]
QED

val _ = export_theory();
