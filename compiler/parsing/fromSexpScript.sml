(*
  Definitions of functions for conversion between an S-expression encoding of
  the CakeML abstract syntax and the abstract syntax type itself.

  The S-expressions use the mlsexp type (Atom mlstring | Expr (sexp list))
  from basis/pure/mlsexpScript.sml.
*)
Theory fromSexp
Ancestors
  mlsexp mlint mlstring ast location[qualified] fpSem
  quantHeuristics ASCIInumbers numposrep
Libs
  preamble match_goal

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = option_monadsyntax.temp_add_option_monadsyntax()

(* TODO: this is duplicated in parserProgTheory *)
Theorem monad_unitbind_assert[local]:
  !b x. monad_unitbind (assert b) x = if b then x else NONE
Proof
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []
QED

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

Definition encode_control_def:
  (encode_control "" = "") ∧
  (encode_control (c::cs) =
    if c = #"\\" then c::c::(encode_control cs)
    else if isPrint c then c::(encode_control cs)
    else (#"\\" :: ((if ORD c < 16 then "0" else "")++num_to_hex_string (ORD c)))
         ++(encode_control cs))
End

Definition decode_control_def:
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
     else OPTION_IGNORE_BIND (OPTION_GUARD (isPrint c)) (OPTION_MAP (CONS c) (decode_control cs)))
End

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
  \\ fs[LENGTH_EQ_NUM_compute] \\ rfs[]
  \\ fs[]
  \\ fs[arithmeticTheory.NOT_LESS]
  \\ qspec_then`h`strip_assume_tac stringTheory.ORD_BOUND
  \\ imp_res_tac num_to_hex_string_length_2
  \\ fs[LENGTH_EQ_NUM_compute] \\ rfs[]
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

Theorem isHexDigit_alt[local]:
  isHexDigit c ⇔ c ∈ set "0123456789abcdefABCDEF"
Proof
  rw[stringTheory.isHexDigit_def, EQ_IMP_THM] >> CONV_TAC EVAL >> simp[]
QED

Theorem UNHEX_lt16[local]:
  isHexDigit c ⇒ UNHEX c < 16
Proof
  dsimp[isHexDigit_alt, ASCIInumbersTheory.UNHEX_def]
QED

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
      rename1`16 * (UNHEX c1 MOD 16) + UNHEX c2 MOD 16 < 16` >>
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

Theorem encode_control_remove:
   ∀s. EVERY isPrint s ∧ #"\\" ∉ set s ⇒ encode_control s = s
Proof
  Induct \\ simp[encode_control_def]
QED

(* --- mlsexp-based encoding/decoding helpers --- *)

(* Encode a string with control char escaping *)
Definition SEXSTR_def:
  SEXSTR s = Atom (implode (encode_control s))
End

Theorem SEXSTR_11[simp]:
   SEXSTR s1 = SEXSTR s2 ⇔ s1 = s2
Proof
  rw[SEXSTR_def]
  \\ metis_tac[decode_encode_control,SOME_11,explode_implode]
QED

(* Encode a natural number *)
Definition SXNUM_def:
  SXNUM (n:num) = Atom (toString (&n))
End

Theorem SXNUM_11[simp]:
   SXNUM n1 = SXNUM n2 ⇔ n1 = n2
Proof
  simp[SXNUM_def, mlintTheory.num_to_str_11]
QED

(* Decode a string with control char unescaping *)
Definition odestSEXSTR_def[simp]:
  (odestSEXSTR (Atom s) = OPTION_MAP implode (decode_control (explode s))) ∧
  (odestSEXSTR (Expr _) = NONE)
End

(* Decode a symbol/tag (raw mlstring) *)
Definition odestSXSYM_def[simp]:
  (odestSXSYM (Atom s) = SOME s) ∧
  (odestSXSYM (Expr _) = NONE)
End

(* Decode a natural number *)
Definition odestSXNUM_def[simp]:
  (odestSXNUM (Atom s) =
    (case fromString s of
     | SOME i => if 0 ≤ i ∧ toString i = s then SOME (Num i) else NONE
     | NONE => NONE)) ∧
  (odestSXNUM (Expr _) = NONE)
End

(* Decode an integer *)
Definition odestSXINT_def[simp]:
  (odestSXINT (Atom s) =
    (case fromString s of
     | SOME i => if toString i = s then SOME i else NONE
     | NONE => NONE)) ∧
  (odestSXINT (Expr _) = NONE)
End

Theorem odestSXNUM_SXNUM[simp]:
  odestSXNUM (SXNUM n) = SOME n
Proof
  simp[SXNUM_def,odestSXNUM_def,num_to_str_def,fromString_toString]
QED

Theorem odestSXINT_SXINT[simp]:
  odestSXINT (Atom (toString i)) = SOME i
Proof
  simp[odestSXINT_def, fromString_toString]
QED

Theorem odestSEXSTR_SEXSTR[simp]:
   odestSEXSTR (SEXSTR s) = SOME (implode s)
Proof
  simp[SEXSTR_def,odestSEXSTR_def]
QED

(* Lists: Expr wraps a list directly *)
Definition listsexp_def:
  listsexp xs = Expr xs
End

Theorem listsexp_thm[simp]:
  listsexp [] = Expr [] ∧ listsexp (h::t) = Expr (h :: t)
Proof
  simp[listsexp_def]
QED

Theorem listsexp_11[simp]:
   ∀ l1 l2. listsexp l1 = listsexp l2 ⇔ l1 = l2
Proof
  simp[listsexp_def]
QED

(* Extract tag + args from (Tag arg1 arg2 ...) *)
Definition dstrip_sexp_def[simp]:
  dstrip_sexp (Expr (Atom tag :: args)) = SOME (explode tag, args) ∧
  dstrip_sexp _ = NONE
End

Theorem dstrip_sexp_size:
   ∀s sym args. dstrip_sexp s = SOME (sym, args) ⇒
                 ∀e. MEM e args ⇒ sexp_size e < sexp_size s
Proof
  Cases >> simp[dstrip_sexp_def] >>
  rename1 `Expr l` >>
  Cases_on `l` >> simp[dstrip_sexp_def] >>
  rename1 `h :: t` >> Cases_on `h` >> simp[dstrip_sexp_def] >>
  rw[] >> gvs[sexp_size_def] >>
  `sexp_size e <= list_size sexp_size t` by metis_tac[MEM_list_size] >>
  simp[]
QED

Theorem explode_eq:
  (explode tag = s ⇔ tag = strlit s) ∧
  (s = explode tag ⇔ strlit s = tag)
Proof
  simp[mlstringTheory.implode_def, EQ_IMP_THM] >>
  metis_tac[mlstringTheory.implode_explode, mlstringTheory.explode_implode,
            mlstringTheory.implode_def]
QED

Theorem dstrip_sexp_SOME:
   dstrip_sexp s = SOME x ⇔
   ∃nm args. s = Expr (Atom (strlit nm) :: args) ∧ x = (nm, args)
Proof
  Cases_on `s` >> simp[dstrip_sexp_def] >>
  Cases_on `l` >> simp[dstrip_sexp_def] >>
  Cases_on `h` >> simp[dstrip_sexp_def] >>
  rw[EQ_IMP_THM] >> gvs[explode_eq] >>
  metis_tac[mlstringTheory.implode_explode, mlstringTheory.implode_def]
QED

Theorem dstrip_sexp_listsexp[simp]:
   (dstrip_sexp (listsexp ls) =
    case ls of (Atom x :: xs) => SOME (explode x, xs) | _ => NONE)
Proof
  Cases_on `ls` >> simp[dstrip_sexp_def,listsexp_def] >>
  Cases_on `h` >> simp[dstrip_sexp_def]
QED

Theorem dstrip_sexp_SEXSTR[simp]:
   dstrip_sexp (SEXSTR s) = NONE
Proof
  simp[SEXSTR_def,dstrip_sexp_def]
QED

Theorem dstrip_sexp_SXNUM[simp]:
   dstrip_sexp (SXNUM n) = NONE
Proof
  simp[SXNUM_def,dstrip_sexp_def]
QED

(* Decode list *)
Definition sexplist_def:
  sexplist p (Atom _) = NONE ∧
  sexplist p (Expr []) = SOME [] ∧
  sexplist p (Expr (h::t)) =
    do
      ph <- p h;
      pt <- sexplist p (Expr t);
      return (ph::pt)
    od
Termination
  wf_rel_tac `measure (sexp_size o SND)` >>
  simp[sexp_size_def]
End

Theorem sexplist_thm[simp]:
  sexplist p (Atom a) = NONE ∧
  sexplist p (Expr []) = SOME [] ∧
  sexplist p (Expr (h::t)) =
    do ph <- p h ; pt <- sexplist p (Expr t); return (ph::pt) od
Proof
  rpt strip_tac >> simp[Once sexplist_def]
QED

(* Decode pair from 2-element Expr *)
Definition sexppair_def:
  sexppair p1 p2 s =
    case s of
      Expr [s1; s2] => lift2 (,) (p1 s1) (p2 s2)
    | _ => fail
End

Theorem sexppair_CONG[defncong]:
   ∀s1 s2 p1 p1' p2 p2'.
       s1 = s2 ∧
       (∀s. (∃s'. s2 = Expr [s; s']) ⇒ p1 s = p1' s) ∧
       (∀s. (∃s'. s2 = Expr [s'; s]) ⇒ p2 s = p2' s)
      ⇒
       sexppair p1 p2 s1 = sexppair p1' p2' s2
Proof
  rw[sexppair_def] >> every_case_tac >> gvs[]
QED

Overload guard[local] = ``λb m. monad_unitbind (assert b) m``

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
     s1 = s2 ∧ (∀e xs. s2 = Expr xs ∧ MEM e xs ⇒ p1 e = p2 e) ⇒
     sexplist p1 s1 = sexplist p2 s2
Proof
  simp[] >> Induct_on `s2` >> simp[] >>
  Induct_on `l` >> rw[] >> simp[Once sexplist_def] >>
  `p1 h = p2 h` by gvs[] >>
  `sexplist p1 (Expr l) = sexplist p2 (Expr l)`
    by (first_x_assum irule >> rw[]) >>
  simp[]
QED

Theorem sexpMEM_sizelt:
  ∀s xs e. s = Expr xs ∧ MEM e xs ⇒ sexp_size e < sexp_size s
Proof
  rw[sexp_size_def] >>
  Induct_on `xs` >> simp[sexp_size_def] >> rw[] >> res_tac >> simp[]
QED

Theorem sexpMEM_sizelt':
  ∀xs a. MEM a xs ⇒ sexp_size a < sexp_size (Expr xs)
Proof
  Induct >> rw[sexp_size_def] >> res_tac >> fs[sexp_size_def]
QED

Theorem dstrip_sexp_sexpMEM_size:
  ∀s nm args i xs a. dstrip_sexp s = SOME (nm, args) ∧
    i < LENGTH args ∧ EL i args = Expr xs ∧ MEM a xs ⇒
    sexp_size a < sexp_size s
Proof
  rw[] >>
  `sexp_size a < sexp_size (Expr xs)` by metis_tac[sexpMEM_sizelt'] >>
  `sexp_size (EL i args) < sexp_size s`
    by (irule dstrip_sexp_size >> metis_tac[MEM_EL]) >>
  gvs[]
QED

(* Decode optional *)
Definition sexpopt_def:
  sexpopt p s =
    do
       nm <- odestSXSYM s ;
       assert(nm = «NONE»);
       return NONE
    od ++
    do
      (nm,args) <- dstrip_sexp s;
      assert(nm = "SOME" ∧ LENGTH args = 1);
      lift SOME (p (HD args))
    od
End

(* Decode identifiers *)
Definition sexpid_def:
  sexpid p s =
    do
       (nm, args) <- dstrip_sexp s;
       (guard (nm = "Short" ∧ LENGTH args = 1)
              (lift Short (p (EL 0 args))) ++
        guard (nm = "Long" ∧ LENGTH args = 2)
              (lift2 Long (odestSEXSTR (EL 0 args)) (sexpid p (EL 1 args))))
    od
Termination
  wf_rel_tac `measure (sexp_size o SND)` >>
  rw[] >> imp_res_tac dstrip_sexp_size >>
  gvs[LENGTH_EQ_NUM_compute]
End

(* --- Decoder functions --- *)

Definition sexptype_def:
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
    od
Termination
  wf_rel_tac `measure sexp_size` >>
  rw[] >> imp_res_tac dstrip_sexp_size >>
  imp_res_tac sexpMEM_sizelt' >>
  gvs[LENGTH_EQ_NUM_compute, sexp_size_def, SF DNF_ss]
End

(* translator friendly version for bootstrapping *)
Definition sexptype_alt_def:
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
    | Atom _ => NONE
    | Expr [] => SOME []
    | Expr (a::d) =>
      (case sexptype_alt a of
       | NONE => NONE
       | SOME h =>
       case sexptype_list (Expr d) of
       | NONE => NONE
       | SOME t => SOME (h::t)))
Termination
  wf_rel_tac`inv_image (measure sexp_size)
                (λx. case x of INL y => y | INR y => y)` \\ rw[] \\
  imp_res_tac dstrip_sexp_size \\
  gvs[LENGTH_EQ_NUM_compute, sexp_size_def]
End

Theorem sexptype_alt_intro:
  (∀s. sexptype s = sexptype_alt s) ∧
  ∀s. sexptype_list s = sexplist sexptype s
Proof
  ho_match_mp_tac sexptype_alt_ind >> rw[] >>
  simp[Once sexptype_def, Once sexptype_alt_def, Once sexplist_def] >>
  every_case_tac >> gvs[ETA_THM]
QED

Theorem sexptype_alt_intro1:
   sexptype = sexptype_alt ∧ sexplist sexptype = sexptype_list
Proof
  rw[FUN_EQ_THM,sexptype_alt_intro]
QED

Definition sexplit_def:
  sexplit s =
    lift StrLit (odestSEXSTR s) ++
    do
      (nm,args) <- dstrip_sexp s;
      assert(LENGTH args = 1);
      guard (nm = "IntLit")
            (lift IntLit (odestSXINT (HD args))) ++
      guard (nm = "char")
            do
              cs <- odestSEXSTR (HD args);
              assert(strlen cs = 1);
              return (Char (strsub cs 0))
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
            od ++
      guard (nm = "float64")
            do
              n <- odestSXNUM (HD args);
              assert (n < 2 ** 64);
              return (Float64(n2w n))
            od
    od
End

(* don't require Pvar constructors; bare strings can be pattern variables.
   Unclear if this sort of special-casing is ever likely to be helpful *)
Definition sexppat_def:
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
      guard (nm = "Pas" ∧ LENGTH args = 2)
            (lift2 Pas (sexppat (EL 0 args))
                       (odestSEXSTR (EL 1 args))) ++
      guard (nm = "Pref" ∧ LENGTH args = 1) (lift Pref (sexppat (EL 0 args))) ++
      guard (nm = "Ptannot" ∧ LENGTH args = 2)
            (lift2 Ptannot (sexppat (EL 0 args)) (sexptype (EL 1 args)))
    od
Termination
  WF_REL_TAC `measure sexp_size` >>
  rw[] >>
  imp_res_tac dstrip_sexp_size >>
  imp_res_tac sexpMEM_sizelt' >>
  gvs[LENGTH_EQ_NUM_compute, sexp_size_def, SF DNF_ss]
End

(* translator friendly version for bootstrapping *)
Definition sexppat_alt_def:
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
      else if nm = "Pas" ∧ LENGTH args = 2 then
        OPTION_MAP2 Pas (sexppat_alt (EL 0 args))
                        (odestSEXSTR (EL 1 args))
      else if nm = "Pref" ∧ LENGTH args = 1 then
        OPTION_MAP Pref (sexppat_alt (EL 0 args))
      else if nm = "Ptannot" ∧ LENGTH args = 2 then
        OPTION_MAP2 Ptannot (sexppat_alt (EL 0 args)) (sexptype_alt (EL 1 args))
      else NONE) ∧
 (sexppat_list s =
    case s of
    | Atom _ => NONE
    | Expr [] => SOME []
    | Expr (a::d) =>
      (case sexppat_alt a of
       | NONE => NONE
       | SOME h =>
       case sexppat_list (Expr d) of
       | NONE => NONE
       | SOME t => SOME (h::t)))
Termination
  wf_rel_tac`inv_image (measure sexp_size) (λx. case x of INL y => y | INR y => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   gvs[LENGTH_EQ_NUM_compute, sexp_size_def]
End

val sexppat_alt_ind = theorem"sexppat_alt_ind";

Theorem sexppat_alt_intro:
   (∀s. sexppat s = sexppat_alt s) ∧ (∀s. sexppat_list s = sexplist sexppat s)
Proof
  ho_match_mp_tac sexppat_alt_ind >> rw[] >>
  simp[Once sexppat_def, Once sexppat_alt_def, Once sexplist_def] >>
  every_case_tac >> gvs[ETA_THM, sexptype_alt_intro]
QED

Theorem sexppat_alt_intro1:
   sexppat = sexppat_alt ∧ sexplist sexppat = sexppat_list
Proof
  rw[FUN_EQ_THM,sexppat_alt_intro]
QED

Definition decode_thunk_mode_def:
  decode_thunk_mode s =
    if s = "Evaluated" then SOME Evaluated
    else if s = "NotEvaluated" then SOME NotEvaluated
    else NONE
End

Definition encode_thunk_mode_def:
  encode_thunk_mode Evaluated = "Evaluated" ∧
  encode_thunk_mode NotEvaluated = "NotEvaluated"
End

Definition decode_test_def:
  decode_test (Atom s) =
    (if s = «Equal» then SOME Equal else
     if s = «Less» then SOME (Compare Lt) else
     if s = «LessEq» then SOME (Compare Leq) else
     if s = «Greater» then SOME (Compare Gt) else
     if s = «GreaterEq» then SOME (Compare Geq) else
     if s = «AltLess» then SOME (AltCompare Lt) else
     if s = «AltLessEq» then SOME (AltCompare Leq) else
     if s = «AltGreater» then SOME (AltCompare Gt) else
     if s = «AltGreaterEq» then SOME (AltCompare Geq) else NONE) ∧
  decode_test _ = NONE
End

Definition decode_prim_type_def:
  decode_prim_type (Atom s) =
    (if s = «BoolT» then SOME BoolT else
     if s = «IntT» then SOME IntT else
     if s = «CharT» then SOME CharT else
     if s = «StrT» then SOME StrT else
     if s = «Word8T» then SOME $ WordT W8 else
     if s = «Word64T» then SOME $ WordT W64 else
     if s = «Float64T» then SOME Float64T else NONE) ∧
  decode_prim_type _ = NONE
End

Definition sexparith_def:
  sexparith (Atom s) =
    (if s = «Add» then SOME Add else
     if s = «Sub» then SOME Sub else
     if s = «Mul» then SOME Mul else
     if s = «Div» then SOME Div else
     if s = «Mod» then SOME Mod else
     if s = «Neg» then SOME Neg else
     if s = «Abs» then SOME Abs else
     if s = «And» then SOME And else
     if s = «Xor» then SOME Xor else
     if s = «Or»  then SOME Or  else
     if s = «Not» then SOME Not else
     if s = «Sqrt» then SOME Sqrt else
     if s = «FMA» then SOME FMA else NONE) ∧
  sexparith _ = NONE
End

Definition sexplog_def:
  sexplog (Atom s) =
    (if s = «Andalso» then SOME Andalso else
     if s = «Orelse» then SOME Orelse else NONE) ∧
  sexplog _ = NONE
End

Definition sexpop_def:
  sexpop s =
    case s of
    | Atom a =>
      (if a = «Equality» then SOME Equality else
       if a = «Opapp» then SOME Opapp else
       if a = «Opassign» then SOME Opassign else
       if a = «Opref» then SOME Opref else
       if a = «Opderef» then SOME Opderef else
       if a = «Aw8alloc» then SOME Aw8alloc else
       if a = «Aw8sub» then SOME Aw8sub else
       if a = «Aw8length» then SOME Aw8length else
       if a = «Aw8update» then SOME Aw8update else
       if a = «Aw8subunsafe» then SOME Aw8sub_unsafe else
       if a = «Aw8updateunsafe» then SOME Aw8update_unsafe else
       if a = «CopyStrStr» then SOME CopyStrStr else
       if a = «CopyStrAw8» then SOME CopyStrAw8 else
       if a = «CopyAw8Str» then SOME CopyAw8Str else
       if a = «CopyAw8Aw8» then SOME CopyAw8Aw8 else
       if a = «XorAw8Strunsafe» then SOME XorAw8Str_unsafe else
       if a = «Implode» then SOME Implode else
       if a = «Explode» then SOME Explode else
       if a = «Strsub» then SOME Strsub else
       if a = «Strlen» then SOME Strlen else
       if a = «Strcat» then SOME Strcat else
       if a = «VfromList» then SOME VfromList else
       if a = «Vsub» then SOME Vsub else
       if a = «Vsub_unsafe» then SOME Vsub_unsafe else
       if a = «Vlength» then SOME Vlength else
       if a = «ListAppend» then SOME ListAppend else
       if a = «Aalloc» then SOME Aalloc else
       if a = «AallocEmpty» then SOME AallocEmpty else
       if a = «AallocFixed» then SOME AallocFixed else
       if a = «Asub» then SOME Asub else
       if a = «Alength» then SOME Alength else
       if a = «Aupdate» then SOME Aupdate else
       if a = «Asubunsafe» then SOME Asub_unsafe else
       if a = «Aupdateunsafe» then SOME Aupdate_unsafe else
       if a = «ForceThunk» then SOME (ThunkOp ForceThunk) else
       if a = «ConfigGC» then SOME ConfigGC else
       if a = «Eval» then SOME Eval else
       if a = «Envid» then SOME Env_id else NONE)
    | Expr [Atom tag; arg] =>
      (if tag = «FFI» then lift FFI (odestSEXSTR arg) else
       if tag = «Shift8Lsl» then lift (Shift W8 Lsl) (odestSXNUM arg) else
       if tag = «Shift8Lsr» then lift (Shift W8 Lsr) (odestSXNUM arg) else
       if tag = «Shift8Asr» then lift (Shift W8 Asr) (odestSXNUM arg) else
       if tag = «Shift8Ror» then lift (Shift W8 Ror) (odestSXNUM arg) else
       if tag = «Shift64Lsl» then lift (Shift W64 Lsl) (odestSXNUM arg) else
       if tag = «Shift64Lsr» then lift (Shift W64 Lsr) (odestSXNUM arg) else
       if tag = «Shift64Asr» then lift (Shift W64 Asr) (odestSXNUM arg) else
       if tag = «Shift64Ror» then lift (Shift W64 Ror) (odestSXNUM arg) else
       if tag = «AllocThunk» then
         (case arg of
          | Atom a =>
            (case decode_thunk_mode (explode a) of
             | SOME m => SOME (ThunkOp (AllocThunk m))
             | NONE => NONE)
          | _ => NONE) else
       if tag = «UpdateThunk» then
         (case arg of
          | Atom a =>
            (case decode_thunk_mode (explode a) of
             | SOME m => SOME (ThunkOp (UpdateThunk m))
             | NONE => NONE)
          | _ => NONE) else
       NONE)
    | Expr [Atom tag; arg1; arg2] =>
      (if tag = «Arith» then
        (case (sexparith arg1, decode_prim_type arg2) of
         | (SOME a, SOME prim_type) => SOME (Arith a prim_type)
         | _ => NONE) else
       if tag = «FromTo» then
        (case (decode_prim_type arg1, decode_prim_type arg2) of
         | (SOME ty1, SOME ty2) => SOME (FromTo ty1 ty2)
         | _ => NONE) else
       if tag = «Test» then
        (case (decode_test arg1, decode_prim_type arg2) of
         | (SOME test, SOME prim_type) => SOME (Test test prim_type)
         | _ => NONE) else
       NONE)
    | _ => NONE
End

Definition sexplocpt_def:
  sexplocpt (Atom s) =
    (if s = «unk» then SOME UNKNOWNpt
     else if s = «eof» then SOME EOFpt
     else NONE) ∧
  sexplocpt (Expr ls) =
    if LENGTH ls = 2 then
      lift2 POSN (odestSXNUM (EL 0 ls)) (odestSXNUM (EL 1 ls))
    else NONE
End

Definition sexplocn_def:
  sexplocn s =
    case s of
    | Expr ls =>
      if LENGTH ls = 2 then
        lift2 Locs (sexplocpt (EL 0 ls)) (sexplocpt (EL 1 ls))
      else NONE
    | _ => NONE
End

Definition sexpexp_def:
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
            (lift Log (sexplog (EL 0 args)) <*>
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
Termination
  WF_REL_TAC `measure sexp_size` >>
  rw[] >>
  imp_res_tac dstrip_sexp_size >>
  imp_res_tac sexpMEM_sizelt' >>
  gvs[LENGTH_EQ_NUM_compute, sexp_size_def, SF DNF_ss]
End

(* translator friendly version for bootstrapping *)
Definition sexpexp_alt_def:
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
             lift Log (sexplog (EL 0 args)) <*> sexpexp_alt (EL 1 args) <*>
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
      | Atom _ => NONE
      | Expr [] => SOME []
      | Expr (a::d) =>
        (case sexpexp_alt a of
         | NONE => NONE
         | SOME h =>
         case sexpexp_list (Expr d) of
         | NONE => NONE
         | SOME t => SOME (h::t))) ∧
  (sexppes s =
   case s of
   | Atom _ => NONE
   | Expr [] => SOME []
   | Expr (a::d) =>
     (case sexppatexp a of
      | NONE => NONE
      | SOME h =>
      case sexppes (Expr d) of
      | NONE => NONE
      | SOME t => SOME (h::t))) ∧
  (sexpfuns s =
   case s of
   | Atom _ => NONE
   | Expr [] => SOME []
   | Expr (a::d) =>
     (case sexpfun a of
      | NONE => NONE
      | SOME h =>
      case sexpfuns (Expr d) of
      | NONE => NONE
      | SOME t => SOME (h::t))) ∧
   (sexppatexp s =
    case s of
    | Expr [a; d] =>
      (case (sexppat_alt a, sexpexp_alt d) of
      | (SOME p, SOME e) => SOME (p,e)
      | _ => NONE)
    | _ => NONE) ∧
   (sexpfun s =
     case s of
     | Expr [a; d] =>
       (case d of
       | Expr [b; e] =>
       (case (odestSEXSTR a, odestSEXSTR b, sexpexp_alt e) of
        | (SOME x, SOME y, SOME z) => SOME (x,y,z)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
Termination
  wf_rel_tac`inv_image (measure sexp_size)
    (λx. case x of
         | INL y => y
         | INR (INL y) => y
         | INR (INR (INL y)) => y
         | INR (INR (INR (INL y))) => y
         | INR (INR (INR (INR (INL y)))) => y
         | INR (INR (INR (INR (INR y)))) => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   gvs[LENGTH_EQ_NUM_compute, sexp_size_def]
End

Theorem sexpexp_alt_intro:
  (∀s. sexpexp s = sexpexp_alt s) ∧
  (∀s. sexplist sexpexp s = sexpexp_list s) ∧
  (∀s. sexplist (sexppair sexppat sexpexp) s = sexppes s) ∧
  (∀s. sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) s = sexpfuns s) ∧
  (∀s. sexppair sexppat sexpexp s = sexppatexp s) ∧
  (∀s. sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp) s = sexpfun s)
Proof
  ho_match_mp_tac sexpexp_alt_ind >> rw[] >-
    (simp[Once sexpexp_def, Once sexpexp_alt_def] >>
     Cases_on `dstrip_sexp s` >> simp[] >>
     PairCases_on `x` >> rw[] >>
     gvs[ETA_THM, sexptype_alt_intro, sexppat_alt_intro]) >-
    (Cases_on `s` >> simp[Once sexplist_def, Once (cj 2 sexpexp_alt_def)] >>
     rename1 `Expr l` >> Cases_on `l` >> simp[Once sexplist_def] >>
     gvs[] >> Cases_on `sexpexp_alt h` >> gvs[] >>
     Cases_on `sexpexp_list (Expr t)` >> simp[]) >-
    (Cases_on `s` >> simp[Once sexplist_def, Once (cj 3 sexpexp_alt_def)] >>
     rename1 `Expr l` >> Cases_on `l` >> simp[Once sexplist_def] >>
     gvs[] >> Cases_on `sexppatexp h` >> gvs[] >>
     Cases_on `sexppes (Expr t)` >> simp[]) >-
    (Cases_on `s` >> simp[Once sexplist_def, Once (cj 4 sexpexp_alt_def)] >>
     rename1 `Expr l` >> Cases_on `l` >> simp[Once sexplist_def] >>
     gvs[] >> Cases_on `sexpfun h` >> gvs[] >>
     Cases_on `sexpfuns (Expr t)` >> simp[]) >-
    (simp[sexppair_def, Once (cj 5 sexpexp_alt_def), sexppat_alt_intro] >>
     every_case_tac >> gvs[]) >>
  simp[sexppair_def, Once (cj 6 sexpexp_alt_def)] >>
  every_case_tac >> gvs[]
QED

Theorem sexpexp_alt_intro1:
   sexpexp = sexpexp_alt ∧
   sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) = sexpfuns
Proof
  rw[FUN_EQ_THM,sexpexp_alt_intro]
QED

Definition sexptype_def_def:
  sexptype_def =
  sexplist
    (sexppair (sexplist odestSEXSTR)
      (sexppair odestSEXSTR
        (sexplist (sexppair odestSEXSTR (sexplist sexptype)))))
End

Definition sexpdec_def:
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
      guard (nm = "Denv" ∧ LENGTH args = 1)
            (lift Denv (odestSEXSTR (EL 0 args))) ++
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
    od
Termination
  wf_rel_tac`measure sexp_size`
   \\ rw[] \\ imp_res_tac dstrip_sexp_size
   \\ imp_res_tac sexpMEM_sizelt'
   \\ gvs[LENGTH_EQ_NUM_compute, sexp_size_def, SF DNF_ss]
End

(* translator friendly version for bootstrapping *)
Definition sexpdec_alt_def:
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
      if nm = "Denv" ∧ LENGTH args = 1 then
            (lift Denv (odestSEXSTR (EL 0 args))) else
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
      | Atom _ => NONE
      | Expr [] => SOME []
      | Expr (a::d) =>
        (case sexpdec_alt a of
         | NONE => NONE
         | SOME h =>
         case sexpdec_list (Expr d) of
         | NONE => NONE
         | SOME t => SOME (h::t)))
Termination
  wf_rel_tac`inv_image (measure sexp_size)
    (λx. case x of
         | INL y => y
         | INR y => y)` \\ rw[] \\
   imp_res_tac dstrip_sexp_size \\
   gvs[LENGTH_EQ_NUM_compute, sexp_size_def]
End

val sexpdec_alt_ind = theorem"sexpdec_alt_ind";

Theorem sexpdec_alt_intro:
   (∀s. sexpdec s = sexpdec_alt s) ∧
  (∀s. sexplist sexpdec s = sexpdec_list s)
Proof
  ho_match_mp_tac sexpdec_alt_ind >> rw[] >-
    (simp[Once sexpdec_def, Once sexpdec_alt_def] >>
     Cases_on `dstrip_sexp s` >> simp[] >>
     PairCases_on `x` >> rw[] >>
     gvs[ETA_THM, sexptype_alt_intro, sexppat_alt_intro, sexpexp_alt_intro]) >>
  Cases_on `s` >> simp[Once sexplist_def, Once (cj 2 sexpdec_alt_def)] >>
  rename1 `Expr l` >> Cases_on `l` >> simp[Once sexplist_def] >>
  gvs[] >> Cases_on `sexpdec_alt h` >> gvs[] >>
  Cases_on `sexpdec_list (Expr t)` >> simp[]
QED

Theorem sexpdec_alt_intro1:
   sexpdec = sexpdec_alt ∧
   sexplist sexpdec = sexpdec_list
Proof
  rw[FUN_EQ_THM,sexpdec_alt_intro]
QED

(* --- Encoder functions (toSexp) --- *)

Definition optsexp_def:
  (optsexp NONE = Atom «NONE») ∧
  (optsexp (SOME x) = Expr [Atom «SOME»; x])
End

Theorem optsexp_11[simp]:
   optsexp o1 = optsexp o2 ⇔ o1 = o2
Proof
  cases_on `o1` >> cases_on `o2` >> fs[optsexp_def]
QED

Definition idsexp_def:
  (idsexp (Short n) = Expr [Atom «Short»; SEXSTR (explode n)]) ∧
  (idsexp (Long ns n) = Expr [Atom «Long»; SEXSTR (explode ns); idsexp n])
End

Theorem idsexp_11[simp]:
   ∀ i1 i2. idsexp i1 = idsexp i2 ⇔ i1 = i2
Proof
  Induct >> gen_tac >> cases_on `i2` >> fs[idsexp_def]
QED

Definition typesexp_def:
  (typesexp (Atvar s) = Expr [Atom «Atvar»; SEXSTR (explode s)]) ∧
  (typesexp (Atfun t1 t2) = Expr [Atom «Atfun»; typesexp t1; typesexp t2]) ∧
  (typesexp (Attup ts) = Expr [Atom «Attup»; Expr (MAP typesexp ts)]) ∧
  (typesexp (Atapp ts tc) = Expr [Atom «Atapp»; Expr (MAP typesexp ts); idsexp tc])
Termination
  WF_REL_TAC`measure ast_t_size` >> rw[] \\
   Induct_on`ts` >> simp[ast_t_size_def] >>
   rw[] >> res_tac >> simp[]
End

Definition litsexp_def:
  (litsexp (IntLit i) = Expr [Atom «IntLit»; Atom (toString i)]) ∧
  (litsexp (Char c) = Expr [Atom «char»; SEXSTR [c]]) ∧
  (litsexp (StrLit s) = SEXSTR (explode s)) ∧
  (litsexp (Word8 w) = Expr [Atom «word8»; SXNUM (w2n w)]) ∧
  (litsexp (Word64 w) = Expr [Atom «word64»; SXNUM (w2n w)]) ∧
  (litsexp (Float64 w) = Expr [Atom «float64»; SXNUM (w2n w)])
End

Definition patsexp_def:
  (patsexp Pany = Expr [Atom «Pany»]) ∧
  (patsexp (Pvar s) = SEXSTR (explode s)) ∧
  (patsexp (Plit l) = Expr [Atom «Plit»; litsexp l]) ∧
  (patsexp (Pcon cn ps) = Expr [Atom «Pcon»; optsexp (OPTION_MAP idsexp cn); Expr (MAP patsexp ps)]) ∧
  (patsexp (Pas p i) = Expr [Atom «Pas»; patsexp p; SEXSTR (explode i)]) ∧
  (patsexp (Pref p) = Expr [Atom «Pref»; patsexp p]) ∧
  (patsexp (Ptannot p t) = Expr [Atom «Ptannot» ; patsexp p; typesexp t])
Termination
  WF_REL_TAC`measure pat_size` >>
   simp [] >>
   Induct_on`ps`>>simp[pat_size_def] >>
   rw[] >> simp[] >> res_tac >>
   first_x_assum(qspec_then`cn`strip_assume_tac)>>
   decide_tac
End

Definition testsexp_def:
  testsexp Equal = Atom «Equal» ∧
  testsexp (Compare Lt) = Atom «Less» ∧
  testsexp (Compare Leq) = Atom «LessEq» ∧
  testsexp (Compare Gt) = Atom «Greater» ∧
  testsexp (Compare Geq) = Atom «GreaterEq» ∧
  testsexp (AltCompare Lt) = Atom «AltLess» ∧
  testsexp (AltCompare Leq) = Atom «AltLessEq» ∧
  testsexp (AltCompare Gt) = Atom «AltGreater» ∧
  testsexp (AltCompare Geq) = Atom «AltGreaterEq»
End

Theorem testsexp_11[simp]:
   ∀l1 l2. testsexp l1 = testsexp l2 ⇔ l1 = l2
Proof
  rw []
  \\ simp [oneline testsexp_def]
  \\ every_case_tac \\ fs []
QED

Theorem sexptest_testsexp[simp]:
  ∀x. decode_test (testsexp x) = SOME x
Proof
  Cases
  \\ TRY (rename [`Compare oo`] \\ Cases_on `oo`)
  \\ TRY (rename [`AltCompare oo`] \\ Cases_on `oo`)
  \\ fs [decode_test_def,testsexp_def]
QED

Definition arithsexp_def:
  arithsexp Add = Atom «Add» ∧
  arithsexp Sub = Atom «Sub» ∧
  arithsexp Mul = Atom «Mul» ∧
  arithsexp Div = Atom «Div» ∧
  arithsexp Mod = Atom «Mod» ∧
  arithsexp And = Atom «And» ∧
  arithsexp Xor = Atom «Xor» ∧
  arithsexp Or  = Atom «Or» ∧
  arithsexp Not = Atom «Not» ∧
  arithsexp Neg = Atom «Neg» ∧
  arithsexp Abs = Atom «Abs» ∧
  arithsexp Sqrt = Atom «Sqrt» ∧
  arithsexp FMA = Atom «FMA»
End

Theorem arithsexp_11[simp]:
   ∀l1 l2. arithsexp l1 = arithsexp l2 ⇔ l1 = l2
Proof
  rw []
  \\ simp [oneline arithsexp_def]
  \\ every_case_tac \\ fs []
QED

Theorem arithsexp_sexparith[simp]:
  ∀x. sexparith (arithsexp x) = SOME x
Proof
  Cases \\ fs [sexparith_def,arithsexp_def]
QED

Definition prim_typesexp_def:
  prim_typesexp BoolT = Atom «BoolT» ∧
  prim_typesexp IntT = Atom «IntT» ∧
  prim_typesexp CharT = Atom «CharT» ∧
  prim_typesexp StrT = Atom «StrT» ∧
  prim_typesexp (WordT W8) = Atom «Word8T» ∧
  prim_typesexp (WordT W64) = Atom «Word64T» ∧
  prim_typesexp Float64T = Atom «Float64T»
End

Theorem sexpprim_type_testsexp[simp]:
  ∀x. decode_prim_type (prim_typesexp x) = SOME x
Proof
  Cases \\ fs [decode_prim_type_def,prim_typesexp_def]
  \\ Cases_on `w` \\ fs [decode_prim_type_def,prim_typesexp_def]
QED

Theorem prim_typesexp_11[simp]:
   ∀l1 l2. prim_typesexp l1 = prim_typesexp l2 ⇔ l1 = l2
Proof
  Cases \\ Cases \\ simp[prim_typesexp_def]
  \\ Cases_on `w` \\ simp[prim_typesexp_def]
  \\ Cases_on `w'` \\ simp[prim_typesexp_def]
QED

Definition opsexp_def:
  (opsexp (Shift W8 Lsl n) = Expr [Atom «Shift8Lsl»; SXNUM n]) ∧
  (opsexp (Shift W8 Lsr n) = Expr [Atom «Shift8Lsr»; SXNUM n]) ∧
  (opsexp (Shift W8 Asr n) = Expr [Atom «Shift8Asr»; SXNUM n]) ∧
  (opsexp (Shift W8 Ror n) = Expr [Atom «Shift8Ror»; SXNUM n]) ∧
  (opsexp (Shift W64 Lsl n) = Expr [Atom «Shift64Lsl»; SXNUM n]) ∧
  (opsexp (Shift W64 Lsr n) = Expr [Atom «Shift64Lsr»; SXNUM n]) ∧
  (opsexp (Shift W64 Asr n) = Expr [Atom «Shift64Asr»; SXNUM n]) ∧
  (opsexp (Shift W64 Ror n) = Expr [Atom «Shift64Ror»; SXNUM n]) ∧
  (opsexp Equality = Atom «Equality») ∧
  (opsexp Opapp = Atom «Opapp») ∧
  (opsexp Opassign = Atom «Opassign») ∧
  (opsexp Opref = Atom «Opref») ∧
  (opsexp Opderef = Atom «Opderef») ∧
  (opsexp Aw8alloc = Atom «Aw8alloc») ∧
  (opsexp Aw8sub = Atom «Aw8sub») ∧
  (opsexp Aw8length = Atom «Aw8length») ∧
  (opsexp Aw8update = Atom «Aw8update») ∧
  (opsexp Aw8sub_unsafe = Atom «Aw8subunsafe») ∧
  (opsexp Aw8update_unsafe = Atom «Aw8updateunsafe») ∧
  (opsexp CopyStrStr = Atom «CopyStrStr») ∧
  (opsexp CopyStrAw8 = Atom «CopyStrAw8») ∧
  (opsexp CopyAw8Str = Atom «CopyAw8Str») ∧
  (opsexp CopyAw8Aw8 = Atom «CopyAw8Aw8») ∧
  (opsexp XorAw8Str_unsafe = Atom «XorAw8Strunsafe») ∧
  (opsexp Implode = Atom «Implode») ∧
  (opsexp Explode = Atom «Explode») ∧
  (opsexp Strsub = Atom «Strsub») ∧
  (opsexp Strlen = Atom «Strlen») ∧
  (opsexp Strcat = Atom «Strcat») ∧
  (opsexp VfromList = Atom «VfromList») ∧
  (opsexp Vsub = Atom «Vsub») ∧
  (opsexp Vsub_unsafe = Atom «Vsub_unsafe») ∧
  (opsexp Vlength = Atom «Vlength») ∧
  (opsexp ListAppend = Atom «ListAppend») ∧
  (opsexp Aalloc = Atom «Aalloc») ∧
  (opsexp AallocEmpty = Atom «AallocEmpty») ∧
  (opsexp AallocFixed = Atom «AallocFixed») ∧
  (opsexp Asub = Atom «Asub») ∧
  (opsexp Alength = Atom «Alength») ∧
  (opsexp Aupdate = Atom «Aupdate») ∧
  (opsexp Asub_unsafe = Atom «Asubunsafe») ∧
  (opsexp Aupdate_unsafe = Atom «Aupdateunsafe») ∧
  (opsexp ConfigGC = Atom «ConfigGC») ∧
  (opsexp Eval = Atom «Eval») ∧
  (opsexp Env_id = Atom «Envid») ∧
  (opsexp (FFI s) = Expr [Atom «FFI»; SEXSTR (explode s)]) ∧
  (opsexp (ThunkOp ForceThunk) = Atom «ForceThunk»)  ∧
  (opsexp (ThunkOp (AllocThunk m)) =
    Expr [Atom «AllocThunk»; Atom (implode (encode_thunk_mode m))]) ∧
  (opsexp (ThunkOp (UpdateThunk m)) =
    Expr [Atom «UpdateThunk»; Atom (implode (encode_thunk_mode m))]) ∧
  (opsexp (Arith a prim_type) =
    Expr [Atom «Arith»; arithsexp a; prim_typesexp prim_type]) ∧
  (opsexp (FromTo ty1 ty2) =
    Expr [Atom «FromTo»; prim_typesexp ty1; prim_typesexp ty2]) ∧
  (opsexp (Test test prim_type) =
    Expr [Atom «Test»; testsexp test; prim_typesexp prim_type])
End

Theorem sexpop_opsexp[simp]:
  sexpop (opsexp op) = SOME op
Proof
  Cases_on `∃t. op = ThunkOp t`
  >- (gvs [] >> Cases_on `t`
      >> gvs [sexpop_def,opsexp_def]
      >> rw [] >> gvs [AllCaseEqs()]
      >> Cases_on `t'` >> gvs [encode_thunk_mode_def,decode_thunk_mode_def]) >>
  Cases_on `op` >> fs [] >> rw[sexpop_def,opsexp_def] >>
  rw[sexpop_def,opsexp_def,SEXSTR_def] >>
  rename [‘Shift c1 c2 _’] >>
  Cases_on `c1` >> rw[sexpop_def,opsexp_def] >>
  Cases_on `c2` >> rw[sexpop_def,opsexp_def]
QED

Theorem opsexp_11[simp]:
   ∀o1 o2. opsexp o1 = opsexp o2 ⇔ o1 = o2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM ``sexpop``) >> simp[]
QED

Definition logsexp_def:
  logsexp Andalso = Atom «Andalso» ∧
  logsexp Orelse = Atom «Orelse»
End

Theorem logsexp_11[simp]:
   ∀l1 l2. logsexp l1 = logsexp l2 ⇔ l1 = l2
Proof
  Cases \\ Cases \\ simp[logsexp_def]
QED

Definition locnsexp_def:
  locnsexp (POSN n1 n2) = Expr [SXNUM n1; SXNUM n2] ∧
  locnsexp UNKNOWNpt = Atom «unk» ∧
  locnsexp EOFpt = Atom «eof»
End

Theorem locnsexp_11[simp]:
  locnsexp p1 = locnsexp p2 ⇔ p1 = p2
Proof
  map_every Cases_on [`p1`, `p2`] >> simp[locnsexp_def, SXNUM_def, mlintTheory.num_to_str_11]
QED

Definition locssexp_def:
  locssexp (Locs p1 p2) = Expr [locnsexp p1; locnsexp p2]
End

Theorem locssexp_11[simp]:
   ∀l1 l2. locssexp l1 = locssexp l2 ⇔ l1 = l2
Proof
  Cases \\ Cases \\ simp[locssexp_def]
QED

Definition expsexp_def:
  expsexp (Raise e) = Expr [Atom «Raise»; expsexp e] ∧
  expsexp (Handle e pes) =
    Expr [Atom «Handle»; expsexp e;
     Expr (MAP (λ(p,e). Expr [patsexp p; expsexp e]) pes)] ∧
  expsexp (Lit l) = Expr [Atom «Lit»; litsexp l] ∧
  expsexp (Con cn es) =
    Expr [Atom «Con»; optsexp (OPTION_MAP idsexp cn);
              Expr (MAP expsexp es)] ∧
  expsexp (Var id) = Expr [Atom «Var»; idsexp id] ∧
  expsexp (Fun x e) = Expr [Atom «Fun»; SEXSTR (explode x); expsexp e] ∧
  expsexp (App op es) =
    Expr [Atom «App»; opsexp op; Expr (MAP expsexp es)] ∧
  expsexp (Log lop e1 e2) = Expr [Atom «Log»; logsexp lop; expsexp e1; expsexp e2] ∧
  expsexp (If e1 e2 e3) = Expr [Atom «If»; expsexp e1; expsexp e2; expsexp e3] ∧
  expsexp (Mat e pes) =
    Expr [Atom «Mat»; expsexp e;
     Expr (MAP (λ(p,e). Expr [patsexp p; expsexp e]) pes)] ∧
  expsexp (Let so e1 e2) =
    Expr [Atom «Let»; optsexp (OPTION_MAP (SEXSTR ∘ explode) so); expsexp e1; expsexp e2] ∧
  expsexp (Letrec funs e) =
  Expr [Atom «Letrec»;
   Expr (MAP (λ(x,y,z). Expr [SEXSTR (explode x);
                               Expr [SEXSTR (explode y); expsexp z]]) funs);
   expsexp e] ∧
  expsexp (Tannot e t) = Expr [Atom «Tannot»; expsexp e; typesexp t] ∧
  expsexp (Lannot e loc) = Expr [Atom «Lannot»; expsexp e; locssexp loc]
End

Definition type_defsexp_def:
  type_defsexp = Expr o
    MAP (λ(xs,x,ls).
      Expr [Expr (MAP (SEXSTR ∘ explode) xs);
            Expr [SEXSTR (explode x);
                  Expr (MAP (λ(y,ts). Expr [SEXSTR (explode y); Expr (MAP typesexp ts)]) ls)]])
End

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

Definition decsexp_def:
  decsexp (Dlet locs p e) =
    Expr [Atom «Dlet»; locssexp locs; patsexp p; expsexp e] ∧
  decsexp (Dletrec locs funs) =
     Expr [
         Atom «Dletrec»;
         locssexp locs;
         Expr
           (MAP (λ(f,x,e). Expr [SEXSTR (explode f);
                                  Expr [SEXSTR (explode x); expsexp e]])
            funs)] ∧
  decsexp (Dtype locs td) = Expr [Atom «Dtype»; locssexp locs; type_defsexp td] ∧
  decsexp (Dtabbrev locs ns x t) = Expr [Atom «Dtabbrev»; locssexp locs; Expr (MAP (SEXSTR ∘ explode) ns); SEXSTR (explode x); typesexp t] ∧
  decsexp (Denv name) = Expr [Atom «Denv»; SEXSTR (explode name)] ∧
  decsexp (Dexn locs x ts) =
    Expr [Atom «Dexn»; locssexp locs; SEXSTR (explode x); Expr (MAP typesexp ts)] ∧
  decsexp (Dmod name decs) =
    Expr [Atom «Dmod»; SEXSTR (explode name); Expr (MAP decsexp decs)] ∧
  decsexp (Dlocal ldecs decs) =
    Expr [Atom «Dlocal»; Expr (MAP decsexp ldecs);
              Expr (MAP decsexp decs)]
End

(* --- Roundtrip proofs --- *)

Theorem sexplist_listsexp_matchable:
   ∀g gl. (∀x. MEM x l ⇒ f (g x) = SOME x) ∧ (gl = MAP g l) ⇒
   sexplist f (Expr gl) = SOME l
Proof
  Induct_on`l` >> simp[Once sexplist_def] >>
  simp[] >> metis_tac[]
QED

Theorem sexplist_listsexp_rwt[simp]:
   (∀x. MEM x l ⇒ f (g x) = SOME x) ⇒
   (sexplist f (Expr (MAP g l)) = SOME l)
Proof
  metis_tac[sexplist_listsexp_matchable]
QED

Theorem odestSEXSTR_SOME[simp]:
   (odestSEXSTR s = SOME y ⇔ s = SEXSTR (explode y)) ∧
   (SOME y = odestSEXSTR s ⇔ s = SEXSTR (explode y))
Proof
  Cases_on`s`\\simp[odestSEXSTR_def,SEXSTR_def]
  \\ metis_tac[decode_encode_control,encode_decode_control,
               explode_implode,implode_explode]
QED

Theorem odestSXNUM_SOME[simp]:
  (odestSXNUM s = SOME n ⇔ s = SXNUM n) ∧
  (SOME n = odestSXNUM s ⇔ s = SXNUM n)
Proof
  `!s n. odestSXNUM s = SOME n ==> s = SXNUM n` suffices_by
    (rw[EQ_IMP_THM] >> gvs[SXNUM_def, odestSXNUM_def, fromString_toString, num_to_str_def]) >>
  Cases >> simp[odestSXNUM_def, SXNUM_def] >> every_case_tac >> gvs[] >>
  rw[num_to_str_def] >> AP_TERM_TAC >> simp[Once (GSYM integerTheory.INT_OF_NUM)]
QED

Theorem odestSXSYM_EQ_SOME[simp]:
  (odestSXSYM s = SOME strng ⇔ s = Atom strng) ∧
  (SOME strng = odestSXSYM s ⇔ s = Atom strng)
Proof
  Cases_on`s` >> simp[odestSXSYM_def] >> metis_tac[]
QED

Theorem odestSEXSTR_listsexp[simp]:
   odestSEXSTR (listsexp l) = NONE
Proof
  simp[listsexp_def]
QED

Theorem odestSXNUM_listsexp[simp]:
   odestSXNUM (listsexp l) = NONE
Proof
  simp[listsexp_def]
QED

Theorem sexpopt_optsexp[simp]:
   (∀y. (x = SOME y) ⇒ (f (g y) = x)) ⇒
   (sexpopt f (optsexp (OPTION_MAP g x)) = SOME x)
Proof
  Cases_on`x`>>simp[sexpopt_def,optsexp_def,dstrip_sexp_def]
QED

Theorem sexpid_odestSEXSTR_idsexp[simp]:
   sexpid odestSEXSTR (idsexp i) = SOME i
Proof
  Induct_on `i` >> simp[idsexp_def, dstrip_sexp_def] >>
  rw [Once sexpid_def, dstrip_sexp_def, EXISTS_PROD]
QED

Theorem sexptype_typesexp[simp]:
   sexptype (typesexp t) = SOME t
Proof
  qid_spec_tac `t` >>
  ho_match_mp_tac type_ind >>
  conj_tac >- rw[Once sexptype_def,typesexp_def] >>
  conj_tac >- (rw[] >> rw[Once sexptype_def,typesexp_def]) >>
  conj_tac >> (
  Induct >> rw[typesexp_def] >- (
    rw[Once sexptype_def,sexplist_listsexp_matchable] ) >> fs[] >>
  rw[Once sexptype_def] >>
  fsrw_tac[boolSimps.ETA_ss][] >>
  match_mp_tac sexplist_listsexp_matchable >>
  fs[typesexp_def] >> rw[] >> rw[] >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[])
QED

Theorem sexplit_litsexp[simp]:
   sexplit (litsexp l) = SOME l
Proof
  Cases_on `l` >> simp[sexplit_def,litsexp_def,mlstringTheory.implode_def] >>
  ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_8] >>
  ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_64] >>
  simp[wordsTheory.w2n_lt]
QED

Theorem sexppat_patsexp[simp]:
   sexppat (patsexp p) = SOME p
Proof
  qid_spec_tac `p` >>
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
    qexists_tac `patsexp` >> simp[] >>
    fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  rw[] >> simp[patsexp_def,Once sexppat_def]
QED

Theorem sexplocpt_locnsexp[simp]:
  sexplocpt (locnsexp p) = SOME p
Proof
  Cases_on `p` >> simp[sexplocpt_def, locnsexp_def, odestSXNUM_SXNUM]
QED

Theorem sexplocn_locnsexp[simp]:
   sexplocn (locssexp l) = SOME l
Proof
  Cases_on `l` >> rw[sexplocn_def,locssexp_def]
QED

Theorem sexplog_logsexp[simp]:
   sexplog (logsexp l) = SOME l
Proof
  Cases_on `l` >> rw[sexplog_def,logsexp_def]
QED

val exists_g_tac =
  (fn (g as (asl,w)) =>
    let
      val (x,b) = dest_exists w
      val tm = find_term (fn y => type_of x = type_of y andalso not (is_var y)) b
    in EXISTS_TAC tm end g)

Theorem sexpexp_expsexp[simp]:
   sexpexp (expsexp e) = SOME e
Proof
  qid_spec_tac `e` >>
  ho_match_mp_tac exp_ind >> rw[] >>
  rw[expsexp_def] >> rw[Once sexpexp_def] >>
  match_mp_tac sexplist_listsexp_matchable >>
  exists_g_tac >> simp[] >>
  fs[listTheory.EVERY_MEM] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >>
  simp[sexppair_def] >>
  rw[] >> res_tac >> fs[]
QED

Theorem sexptype_def_type_defsexp[simp]:
   sexptype_def (type_defsexp l) = SOME l
Proof
  rw[type_defsexp_def, sexptype_def_def] >>
  irule sexplist_listsexp_matchable >>
  irule_at Any EQ_REFL >> simp[FORALL_PROD, sexppair_def]
QED

Theorem sexpdec_decsexp[simp]:
   ∀d. sexpdec (decsexp d) = SOME d
Proof
  ho_match_mp_tac dec_ind
  >> rw[decsexp_def]
  >> rw[Once sexpdec_def]
  >> match_mp_tac sexplist_listsexp_matchable
  >> exists_g_tac >> simp[] >> fs[EVERY_MEM]
  >> qx_gen_tac `p` >> PairCases_on `p` >> rw[]
  >> simp[sexppair_def]
QED


(* --- Injectivity proofs (via forward roundtrips) --- *)

Theorem typesexp_11[simp]:
   ∀t1 t2. typesexp t1 = typesexp t2 ⇔ t1 = t2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM ``sexptype``) >> simp[]
QED

Theorem litsexp_11[simp]:
   ∀l1 l2. litsexp l1 = litsexp l2 ⇔ l1 = l2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM ``sexplit``) >> simp[]
QED

Theorem patsexp_11[simp]:
   ∀p1 p2. patsexp p1 = patsexp p2 ⇔ p1 = p2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM ``sexppat``) >> simp[]
QED

Theorem expsexp_11[simp]:
   ∀e1 e2. expsexp e1 = expsexp e2 ⇒ e1 = e2
Proof
  rw[] >> pop_assum (mp_tac o AP_TERM ``sexpexp``) >> simp[]
QED

Theorem type_defsexp_11[simp]:
   ∀t1 t2. type_defsexp t1 = type_defsexp t2 ⇔ t1 = t2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM ``sexptype_def``) >> simp[]
QED

Theorem decsexp_11[simp]:
   ∀d1 d2. decsexp d1 = decsexp d2 ⇔ d1 = d2
Proof
  rw[EQ_IMP_THM] >> pop_assum (mp_tac o AP_TERM ``sexpdec``) >> simp[]
QED

(* --- Reverse roundtrip proofs --- *)

Theorem sexpopt_SOME:
   sexpopt f s = SOME opt ⇔
     opt = NONE ∧ s = Atom «NONE» ∨
     ∃x s0. opt = SOME x ∧ f s0 = SOME x ∧ s = Expr [Atom «SOME»; s0]
Proof
  Cases_on `s` >> simp[sexpopt_def, odestSXSYM_def, dstrip_sexp_def] >- metis_tac[] >>
  simp[dstrip_sexp_SOME, PULL_EXISTS, LENGTH_EQ_NUM_compute] >>
  rw[EQ_IMP_THM] >> gvs[] >>
  `tag = implode (explode tag)` by simp[mlstringTheory.implode_explode] >>
  pop_assum SUBST1_TAC >> ASM_REWRITE_TAC[] >> simp[mlstringTheory.implode_def]
QED

Theorem sexplist_SOME:
   sexplist f s = SOME ls ⇔ ∃l. s = Expr l ∧ MAP f l = MAP SOME ls
Proof
  map_every qid_spec_tac [`s`,`ls`] >>
  Induct >> rw[]
  >- (Cases_on `s` >> simp[Once sexplist_def] >>
      Cases_on `l` >> simp[Once sexplist_def, AllCaseEqs()]) >>
  Cases_on `s` >> simp[Once sexplist_def, AllCaseEqs(), PULL_EXISTS, MAP_EQ_CONS] >>
  Cases_on `l` >> simp[Once sexplist_def, AllCaseEqs(), PULL_EXISTS] >> metis_tac[]
QED

Theorem sexppair_SOME:
   sexppair f1 f2 s = SOME p ⇔
     ∃x y a b. f1 x = SOME a ∧ f2 y = SOME b ∧ s = Expr [x; y] ∧ p = (a,b)
Proof
  simp[sexppair_def, AllCaseEqs(), PULL_EXISTS] >> metis_tac[]
QED

Theorem OPTION_CHOICE_EQ_SOME = OPTION_CHOICE_EQUALS_OPTION

val tag_tac =
  `tag = implode (explode tag)` by simp[mlstringTheory.implode_explode] >>
  pop_assum SUBST1_TAC >> ASM_REWRITE_TAC[] >> simp[mlstringTheory.implode_def]

Theorem litsexp_sexplit:
  (sexplit s = SOME l ⇔ litsexp l = s) ∧
  (SOME l = sexplit s ⇔ litsexp l = s)
Proof
  simp[EQ_SYM_EQ] >>
  simp[sexplit_def, OPTION_CHOICE_EQUALS_OPTION, dstrip_sexp_SOME, PULL_EXISTS,
       OPTION_CHOICE_EQ_NONE, LENGTH_EQ_NUM_compute, SF CONJ_ss,
       odestSXNUM_SOME, odestSEXSTR_SOME, odestSXINT_def, AllCaseEqs()] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac >> gvs[litsexp_def]
  (* backward direction *)
  >- (Cases_on `l` >> simp[litsexp_def] >-
      (qexists_tac `str c` >> simp[] >> EVAL_TAC) >>
      ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_8] >>
      ONCE_REWRITE_TAC[GSYM wordsTheory.dimword_64] >>
      simp[wordsTheory.w2n_lt])
  (* IntLit forward *)
  >- (tag_tac >> Cases_on `h` >> gvs[odestSXINT_def, AllCaseEqs()])
  (* Char forward *)
  >- (tag_tac >>
      `LENGTH (explode cs) = 1` by simp[mlstringTheory.strlen_implode] >>
      Cases_on `explode cs` >> gvs[] >>
      Cases_on `cs` >> gvs[mlstringTheory.strsub_def, mlstringTheory.explode_def])
  (* word8, word64, float64 forward - just tag *)
  >> tag_tac
QED

Theorem idsexp_sexpid_odestSEXSTR:
   ∀y x. sexpid odestSEXSTR x = SOME y ⇔ x = idsexp y
Proof
  Induct >>
  simp[Once sexpid_def, EXISTS_PROD, dstrip_sexp_SOME, PULL_EXISTS, idsexp_def,
       OPTION_CHOICE_EQUALS_OPTION, LENGTH_EQ_NUM_compute, explode_eq]
QED

Theorem idsexp_sexpid_odestSEXSTR'[simp]:
  (sexpid odestSEXSTR x = SOME y ⇔ x = idsexp y) ∧
  (SOME y = sexpid odestSEXSTR x ⇔ x = idsexp y)
Proof
  simp[EQ_IMP_THM] >> metis_tac[idsexp_sexpid_odestSEXSTR]
QED

Theorem typesexp_sexptype:
   ∀s t. (sexptype s = SOME t ⇔ typesexp t = s) ∧
         (SOME t = sexptype s ⇔ typesexp t = s)
Proof
  simp[EQ_SYM_EQ] >>
  ho_match_mp_tac (theorem"sexptype_ind")
  >> simp[dstrip_sexp_SOME, LENGTH_EQ_NUM_compute, PULL_EXISTS]
  >> rw[]
  >> Cases_on `t`
  >> simp[Once sexptype_def, EXISTS_PROD, dstrip_sexp_SOME,
          LENGTH_EQ_NUM_compute, PULL_EXISTS, OPTION_CHOICE_EQUALS_OPTION,
          OPTION_CHOICE_EQ_NONE, typesexp_def]
  >> eq_tac >> strip_tac >> gvs[explode_eq] >>
  gvs[sexplist_SOME, LIST_EQ_REWRITE, EL_MAP, PULL_EXISTS, MEM_EL]
QED

Theorem patsexp_sexppat0:
   ∀s p. sexppat s = SOME p ⇒ patsexp p = s
Proof
  ho_match_mp_tac (theorem"sexppat_ind") >>
  simp[dstrip_sexp_SOME, PULL_EXISTS, LENGTH_EQ_NUM_compute] >>
  gen_tac >> strip_tac >> ONCE_REWRITE_TAC [sexppat_def] >>
  Cases >>
  simp[OPTION_CHOICE_EQUALS_OPTION, OPTION_CHOICE_EQ_NONE, EXISTS_PROD,
       dstrip_sexp_SOME, patsexp_def, PULL_EXISTS, LENGTH_EQ_NUM_compute,
       litsexp_sexplit, sexpopt_SOME, typesexp_sexptype, explode_eq] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  rw[] >> rw[optsexp_def] >>
  gvs[PULL_EXISTS, sexplist_SOME, LIST_EQ_REWRITE, EL_MAP, MEM_EL]
QED

Theorem patsexp_sexppat:
  (sexppat s = SOME p ⇔ patsexp p = s) ∧
  (SOME p = sexppat s ⇔ patsexp p = s)
Proof
  metis_tac[patsexp_sexppat0, sexppat_patsexp]
QED

Theorem decode_test_testsexp:
  decode_test s = SOME test ⇒ testsexp test = s
Proof
  rw [oneline decode_test_def, AllCaseEqs()]
  \\ simp [testsexp_def]
QED

Theorem sexparith_arithsexp:
  sexparith s = SOME arith ⇒ arithsexp arith = s
Proof
  rw [oneline sexparith_def, AllCaseEqs()]
  \\ simp [arithsexp_def]
QED

Theorem decode_prim_type_prim_typesexp:
  decode_prim_type s0 = SOME prim_type ⇒
  prim_typesexp prim_type = s0
Proof
  rw [oneline decode_prim_type_def, AllCaseEqs()]
  \\ simp [prim_typesexp_def]
QED

Theorem opsexp_sexpop:
   sexpop s = SOME p ⇒ opsexp p = s
Proof
  Cases_on `s` >> rw[sexpop_def] >> rw[opsexp_def]
  >> gvs[sexpop_def, AllCaseEqs(), opsexp_def, encode_decode_control]
  >> gvs [encode_thunk_mode_def,decode_thunk_mode_def,AllCaseEqs(),
          decode_test_testsexp,decode_prim_type_prim_typesexp,
          sexparith_arithsexp, explode_eq, mlstringTheory.implode_def]
QED

Theorem locnsexp_sexplocpt0:
  sexplocpt s = SOME z ⇒ locnsexp z = s
Proof
  Cases_on `z` >> Cases_on `s` >>
  simp[locnsexp_def, sexplocpt_def, AllCaseEqs(), PULL_EXISTS,
       LENGTH_EQ_NUM_compute] >> rw[] >> gvs[]
QED

Theorem locnsexp_sexplocpt[simp]:
  (sexplocpt s = SOME z ⇔ locnsexp z = s) ∧
  (SOME z = sexplocpt s ⇔ locnsexp z = s)
Proof
  metis_tac[locnsexp_sexplocpt0, sexplocpt_locnsexp]
QED

Theorem locnsexp_sexplocn0:
  sexplocn s = SOME z ⇒ locssexp z = s
Proof
  Cases_on `z` >> Cases_on `s` >>
  simp[sexplocn_def, locssexp_def, AllCaseEqs(), PULL_EXISTS,
       LENGTH_EQ_NUM_compute] >>
  rw[] >> gvs[]
QED

Theorem locnsexp_sexplocn:
   (sexplocn s = SOME z ⇔ locssexp z = s) ∧
   (SOME z = sexplocn s ⇔ locssexp z = s)
Proof
  metis_tac[locnsexp_sexplocn0, sexplocn_locnsexp]
QED

Theorem logsexp_sexplog:
   (sexplog s = SOME z ⇔ logsexp z = s) ∧
   (SOME z = sexplog s ⇔ logsexp z = s)
Proof
  Cases_on`z` >>
  simp[oneline sexplog_def, logsexp_def, LENGTH_EQ_NUM_compute,
       PULL_EXISTS, AllCaseEqs()]
QED

Theorem expsexp_sexpexp:
  (sexpexp s = SOME e ⇔ expsexp e = s) ∧
  (SOME e = sexpexp s ⇔ expsexp e = s)
Proof
  `∀s e. sexpexp s = SOME e ⇒ expsexp e = s`
    suffices_by metis_tac[sexpexp_expsexp] >>
  ho_match_mp_tac (theorem "sexpexp_ind") >>
  simp[OPTION_GUARD_EQ_THM, LENGTH_EQ_NUM_compute, PULL_EXISTS,
       dstrip_sexp_SOME]
  >> rpt gen_tac >> strip_tac >> gen_tac
  >> simp[Once sexpexp_def, EXISTS_PROD, dstrip_sexp_SOME, PULL_EXISTS]
  >> rpt gen_tac
  >> rename1 `guard (nm = "Raise" ∧ _) _`
  >> reverse (Cases_on `nm ∈ {"Raise"; "Handle"; "Lit"; "Con"; "Var"; "Fun";
                              "App"; "Log"; "If"; "Mat"; "Let"; "Letrec";
                              "Lannot"; "Tannot"}`)
  >> pop_assum mp_tac
  >> simp[]
  >> rw[]
  >> simp[expsexp_def]
  >> gvs[LENGTH_EQ_NUM_compute, litsexp_sexplit, opsexp_sexpop,
         idsexp_sexpid_odestSEXSTR, typesexp_sexptype, locnsexp_sexplocn,
         OPTION_APPLY_MAP3, expsexp_def, sexpopt_SOME,
         optsexp_def, logsexp_sexplog] >>
  gvs[sexplist_SOME, EL_MAP, LIST_EQ_REWRITE, MEM_EL, PULL_EXISTS] >>
  rw[] >> pairarg_tac >> first_x_assum drule >>
  simp[sexppair_SOME, PULL_EXISTS, patsexp_sexppat] >> metis_tac[]
QED

Theorem type_defsexp_sexptype_def:
   (sexptype_def s = SOME x ⇔ type_defsexp x = s) ∧
   (SOME x = sexptype_def s ⇔ type_defsexp x = s)
Proof
  simp[EQ_SYM_EQ] >> simp[EQ_IMP_THM] >>
  rw[sexptype_def_def, type_defsexp_def] >>
  gvs[sexplist_SOME, LIST_EQ_REWRITE, EL_MAP, sexppair_SOME, PULL_EXISTS,
      EL_MAP, SF CONJ_ss, typesexp_sexptype] >>
  rpt strip_tac >> pairarg_tac >> simp[] >>
  first_x_assum $ drule_then strip_assume_tac >> simp[] >> gvs[] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rw[] >>
  pairarg_tac >> simp[] >> first_x_assum $ drule_then strip_assume_tac >>
  gvs[] >> simp[LIST_EQ_REWRITE, EL_MAP]
QED

Theorem decsexp_sexpdec:
  (sexpdec s = SOME d ⇔ decsexp d = s) ∧
  (SOME d = sexpdec s ⇔ decsexp d = s)
Proof
  `!s d. sexpdec s = SOME d ==> decsexp d = s`
    suffices_by metis_tac[sexpdec_decsexp] >>
  ho_match_mp_tac (theorem "sexpdec_ind") >>
  ntac 3 strip_tac >>
  rw[Once sexpdec_def] >>
  pairarg_tac >> gvs[dstrip_sexp_SOME] >>
  rename1 `guard (nm = _ ∧ _) _` >>
  Cases_on `nm ∈ {"Dlet"; "Dletrec"; "Dtype"; "Dtabbrev"; "Denv"; "Dexn"; "Dmod"}` >>
  fs[] >>
  fs[decsexp_def, LENGTH_EQ_NUM_compute] >>
  gvs[OPTION_APPLY_MAP3, OPTION_APPLY_MAP4, decsexp_def, expsexp_sexpexp,
      locnsexp_sexplocn, patsexp_sexppat, type_defsexp_sexptype_def,
      typesexp_sexptype] >>
  gvs[sexplist_SOME, LIST_EQ_REWRITE, EL_MAP, sexppair_SOME, PULL_EXISTS,
      typesexp_sexptype, MEM_EL] >>
  rw[] >> pairarg_tac >>
  first_x_assum $ drule_then strip_assume_tac >> gvs[expsexp_sexpexp]
QED

Theorem listsexp_MAP_EQ_f:
   (∀x. MEM x ls ⇒ f1 x = f2 x) ⇒
    listsexp (MAP f1 ls) = listsexp (MAP f2 ls)
Proof
  simp[MAP_CONG]
QED

Theorem sexplist_listsexp_imp:
   sexplist f (Expr l1) = SOME l2 ⇒
   ∀n. n < LENGTH l1 ⇒ f (EL n l1) = SOME (EL n l2)
Proof
  qid_spec_tac`l2`>> Induct_on`l1`>> simp[PULL_EXISTS, LT_SUC, DISJ_IMP_THM]
QED

Theorem odestSXNUM_EQ_SOME[simp]:
  (odestSXNUM s = SOME n ⇔ s = SXNUM n) ∧
  (SOME n = odestSXNUM s ⇔ s = SXNUM n)
Proof
  simp[odestSXNUM_SOME]
QED
