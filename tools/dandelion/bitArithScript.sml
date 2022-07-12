(**
  Translation from HOL4 numbers to bit strings

  Used in inital attempt to speed up computations, used by evaluation of the
  first phase
**)
open HolKernel Parse BasicProvers listTheory arithmeticTheory;
open realTheory;
open boolLib bossLib;

val _ = new_theory "bitArith";

val _ = numLib.prefer_num();

(** Code from Michael Norrish for translating to boolean vectors **)
val tobl_def = new_specification(
  "tobl_def", ["tobl"],
  numeralTheory.bit_initiality
    |> INST_TYPE [alpha |-> “:bool -> bool list”]
    |> SPECL [“λb:bool. if b then [] else [T]”,
              “λ(n:num) r b. b::(r b : bool list)”,
              “λ(n:num) r b. ~b::r F”]
    |> SIMP_RULE bool_ss [FUN_EQ_THM])

val _ = computeLib.add_persistent_funs ["tobl_def"]

Theorem tobl_NUMERAL[compute]: tobl (NUMERAL x) = tobl x
Proof
  simp[arithmeticTheory.NUMERAL_DEF]
QED

Theorem tobl0[compute]: tobl 0 b = tobl ZERO b
Proof
  simp[arithmeticTheory.ALT_ZERO]
QED

Definition bleval_def:
  bleval [] = 0 ∧
  bleval (T::rest) = 2 * bleval rest + 1 ∧
  bleval (F::rest) = 2 * bleval rest
End

Theorem bleval_APPEND:
  bleval (xs ++ ys) = bleval ys * 2 EXP (LENGTH xs) + bleval xs
Proof
  Induct_on ‘xs’ >> simp[FORALL_BOOL, bleval_def] >>
  simp[arithmeticTheory.EXP]
QED

Theorem EVERYF_bleval0:
  bleval bs = 0 ⇔ EVERY ((=) F) bs
Proof
  Induct_on ‘bs’ >> simp[bleval_def, FORALL_BOOL]
QED

Theorem EVERYF_suffix_bleval:
  EVERY ((=) F) s ⇒ bleval (p ++ s) = bleval p
Proof
  simp[bleval_APPEND, EVERYF_bleval0]
QED

Theorem LASTbl_nonzero:
  LAST (x::xs) ⇒ 0 < bleval (x::xs)
Proof
  qid_spec_tac ‘x’ >> Induct_on ‘xs’ >> simp[bleval_def] >> rpt gen_tac >>
  rename [‘bleval (a::b::xs)’] >> Cases_on ‘a’ >> simp[bleval_def]
QED

Theorem tobl_correct:
  bleval (tobl n T) = n ∧
  bleval (tobl n F) = n + 1
Proof
  Induct_on ‘n’ using numeralTheory.bit_induction >>
  simp[tobl_def, bleval_def] >> rpt strip_tac
  >- simp[arithmeticTheory.ALT_ZERO]
  >- simp[arithmeticTheory.ALT_ZERO] >>
  simp[SimpRHS, Once arithmeticTheory.BIT1] >>
  simp[SimpRHS, Once arithmeticTheory.BIT2]
QED

Definition frombl_def:
  frombl addedp [] = 0 ∧
  frombl T [T] = ZERO ∧
  frombl F [T] = BIT1 ZERO ∧
  frombl T (F::rest) = BIT1 (frombl T rest) ∧
  frombl F (F::rest) = BIT2 (frombl T rest) ∧
  frombl T (T::rest) = BIT2 (frombl T rest) ∧
  frombl F (T::rest) = BIT1 (frombl F rest)
End

Theorem frombl_correct:
  bl ≠ [] ∧ LAST bl ⇒
  frombl F bl = bleval bl ∧
  frombl T bl = bleval bl - 1
Proof
  Induct_on ‘bl’ >> simp[] >> Cases_on ‘bl’ >> gs[] >>
  simp[frombl_def, bleval_def]
  >- (simp[Once arithmeticTheory.BIT1, SimpLHS] >>
      simp[arithmeticTheory.ALT_ZERO]) >>
  rpt strip_tac >> gs[] >> rename [‘frombl _ (x::y::xs)’] >>
  Cases_on ‘x’ >> simp[frombl_def, bleval_def]
  >- simp[Once arithmeticTheory.BIT1, SimpLHS]
  >- (simp[Once arithmeticTheory.BIT2, SimpLHS] >>
      ‘0 < bleval (y::xs) ’ suffices_by simp[] >>
      simp[LASTbl_nonzero])
  >- (simp[Once arithmeticTheory.BIT2, SimpLHS] >>
      ‘0 < bleval (y::xs) ’ suffices_by simp[] >>
      simp[LASTbl_nonzero]) >>
  simp[Once arithmeticTheory.BIT1, SimpLHS] >>
  ‘0 < bleval (y::xs) ’ suffices_by simp[] >>
  simp[LASTbl_nonzero]
QED

Definition fromBL_def:
  fromBL bs =
  if bs = [] then 0
  else
    let bs1 = REV bs []
    in
      case HD bs1 of
        T => NUMERAL (frombl F bs)
      | F =>
          let
            bs2 = dropWhile ((=) F) bs1 ;
            bs3 = REV bs2 [] ;
          in
            if bs3 = [] then 0 else NUMERAL (frombl F bs3)
End

Theorem fromBL_correct:
  fromBL bs = bleval bs
Proof
  rw[fromBL_def, bleval_def] >> gs[GSYM listTheory.REVERSE_REV]
  >- (Cases_on ‘bs’ using listTheory.SNOC_CASES >>
      gvs[listTheory.REVERSE_SNOC] >>
      simp[arithmeticTheory.NUMERAL_DEF] >> irule (cj 1 frombl_correct) >>
      simp[])
  >- gs[listTheory.dropWhile_eq_nil, EVERYF_bleval0] >>
  gs[listTheory.dropWhile_eq_nil, listTheory.EXISTS_MEM,
     arithmeticTheory.NUMERAL_DEF] >>
  pop_assum mp_tac >>
  simp[Once listTheory.MEM_SPLIT_APPEND_last] >> rw[] >>
  simp[listTheory.REVERSE_APPEND] >>
  ‘EVERY ((=) F) (REVERSE sfx)’ by simp[listTheory.EVERY_MEM] >>
  simp[listTheory.dropWhile_APPEND_EVERY, frombl_correct] >>
  gs[EVERYF_suffix_bleval]
QED

(** Now use the code to develop bit list arithmetic and implement karatsuba
    multiplication. The original idea is due to Magnus Myreen **)
Definition add_aux_def:
  add_aux [] bs F = bs ∧
  add_aux [] [] T = [T] ∧
  add_aux [] (F :: bs) T = T :: bs ∧
  add_aux [] (T :: bs) T = F :: (add_aux [] bs T) ∧
  add_aux bs [] F = bs ∧
  add_aux (F :: bs) [] T = T :: bs ∧
  add_aux (T :: bs) [] T = F :: (add_aux [] bs T) ∧
  add_aux (F :: bs1) (F :: bs2) T = T ::(add_aux bs1 bs2 F) ∧
  add_aux (F :: bs1) (F :: bs2) F = F :: (add_aux bs1 bs2 F) /\
  add_aux (T :: bs1) (F :: bs2) F = T ::(add_aux bs1 bs2 F) /\
  add_aux (T :: bs1) (F :: bs2) T = F :: (add_aux bs1 bs2 T) /\
  add_aux (F :: bs1) (T :: bs2) T = F :: (add_aux bs1 bs2 T) /\
  add_aux (F :: bs1) (T :: bs2) F = T ::(add_aux bs1 bs2 F) /\
  add_aux (T :: bs1) (T :: bs2) T = T ::(add_aux bs1 bs2 T) /\
  add_aux (T :: bs1) (T :: bs2) F = F :: (add_aux bs1 bs2 T)
End

Definition add_def:
  add bs1 bs2 = add_aux bs1 bs2 F
End

Theorem add_aux_thm:
  ∀m n b.
    bleval (add_aux m n b) = bleval m + bleval n + if b then 1 else 0
Proof
  ho_match_mp_tac add_aux_ind \\ fs [add_aux_def,bleval_def]
QED

Theorem add_thm:
  bleval (add m n) = bleval m + bleval n
Proof
  fs [add_def,add_aux_thm]
QED

Definition divpow2_def:
  divpow2 ([]:bool list) k = [] ∧
  divpow2 bs 0 = bs ∧
  divpow2 (b::bs) (SUC k) = divpow2 bs k
End

Theorem DIV_POW2:
  ∀ x y. 0 < y ⇒ 2 * x DIV (2 * y) = x DIV y
Proof
  rpt strip_tac >> gs[GSYM DIV_DIV_DIV_MULT]
  >> ‘2 * x = x * 2’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> gs[MULT_DIV]
QED

Theorem divpow2_thm:
  ∀ x k. bleval (divpow2 x k) = bleval x DIV (2 ** k)
Proof
  ho_match_mp_tac divpow2_ind >> gs[divpow2_def, bleval_def, ZERO_DIV]
  >> rpt strip_tac
  >> reverse $ Cases_on ‘b’ >> gs[bleval_def]
  >- (
    ‘2 ** SUC k = 2 * 2 ** k’ by gs[EXP]
    >> ‘2 * bleval x = bleval x * 2’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> gs[MULT_DIV, DIV_POW2])
  >> ‘2 ** SUC k = 2 * 2 ** k’ by gs[EXP]
  >> ‘2 * bleval x = bleval x * 2’ by gs[]
  >> gs[GSYM DIV_DIV_DIV_MULT]
  >> ‘2 * bleval x = bleval x * 2’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> gs[DIV_MULT]
QED

(** TODO: Try a tail recursive version that drops leading 0s **)
Definition modpow2_def:
  modpow2 ([]:bool list) k = [] ∧
  modpow2 bs 0 = [] ∧
  modpow2 (b::bs) (SUC k) = b :: (modpow2 bs k)
End

Theorem bleval_less:
  ∀ bs. bleval bs < 2 ** (LENGTH bs)
Proof
  ho_match_mp_tac bleval_ind >> gs[bleval_def] >> rw[]
  >> irule LESS_LESS_EQ_TRANS >> qexists_tac ‘2 * 2 ** LENGTH bs’
  >> conj_tac >> gs[EXP]
QED

Theorem bleval_less_large:
  LENGTH bs ≤ k ⇒ bleval bs < 2 ** k
Proof
  rpt strip_tac >> irule LESS_LESS_EQ_TRANS
  >> qexists_tac ‘2 ** LENGTH bs’ >> gs[bleval_less]
QED

Theorem modpow2_thm:
  ∀ x k. bleval (modpow2 x k) = bleval x MOD (2 ** k)
Proof
  ho_match_mp_tac modpow2_ind >> gs[modpow2_def, bleval_def, ZERO_MOD]
  >> rpt strip_tac >> reverse $ Cases_on ‘b’ >> gs[bleval_def]
  >- (
    Cases_on ‘LENGTH x < k’ >> gs[NOT_LESS]
    >- (
      ‘bleval x MOD 2 ** k = bleval x’ by gs[LESS_MOD, bleval_less_large]
      >> pop_assum $ rewrite_tac o single
      >> ‘2 * bleval x = bleval (F :: x)’ by gs[bleval_def]
      >> pop_assum $ rewrite_tac o single
      >> ‘bleval (F::x) MOD 2 ** SUC k = bleval (F::x)’
        by gs[LESS_MOD, bleval_less_large]
      >> pop_assum $ rewrite_tac o single)
    >> gs[quantHeuristicsTheory.LENGTH_LE_NUM, bleval_APPEND]
    >> ‘bleval l1 MOD 2 ** k = bleval l1’
        by (gs[LESS_MOD] >> rpt VAR_EQ_TAC >> gs[bleval_less])
    >> first_assum $ once_rewrite_tac o single
    >> gs[LEFT_ADD_DISTRIB]
    >> ‘2 * (bleval l2 * 2 ** k) = bleval l2 * 2 ** SUC k’ by gs[EXP]
    >> pop_assum $ once_rewrite_tac o single
    >> gs[]
    >> ‘2 * bleval l1 = bleval (F :: l1)’ by gs[bleval_def]
    >> pop_assum $ rewrite_tac o single
    >> gs[bleval_less_large])
  >> Cases_on ‘LENGTH x < k’ >> gs[NOT_LESS]
  >- (
    ‘bleval x MOD 2 ** k = bleval x’ by gs[LESS_MOD, bleval_less_large]
    >> pop_assum $ rewrite_tac o single
    >> ‘2 * bleval x + 1 = bleval (T :: x)’ by gs[bleval_def]
    >> pop_assum $ rewrite_tac o single
    >> ‘bleval (T::x) MOD 2 ** SUC k = bleval (T::x)’
        by gs[LESS_MOD, bleval_less_large]
    >> pop_assum $ rewrite_tac o single)
  >> gs[quantHeuristicsTheory.LENGTH_LE_NUM, bleval_APPEND]
  >> ‘bleval l1 MOD 2 ** k = bleval l1’
      by (gs[LESS_MOD] >> rpt VAR_EQ_TAC >> gs[bleval_less])
  >> first_assum $ once_rewrite_tac o single
  >> gs[LEFT_ADD_DISTRIB]
  >> ‘2 * (bleval l2 * 2 ** k) = bleval l2 * 2 ** SUC k’ by gs[EXP]
  >> pop_assum $ once_rewrite_tac o single
  >> gs[]
  >> ‘2 * bleval l1 + 1 = bleval (T :: l1)’ by gs[bleval_def]
  >> pop_assum $ rewrite_tac o single
  >> gs[bleval_less_large]
QED

Definition mul_def:
  mul [] _ = [] ∧
  mul (T::bs) bs2 = add bs2 (mul bs (F::bs2)) ∧
  mul (F::bs) bs2 = mul bs (F::bs2)
End

Theorem mul_thm:
  ∀ x y. bleval (mul x y) = bleval x * bleval y
Proof
  ho_match_mp_tac mul_ind >> gs[mul_def, bleval_def, add_thm]
QED

Definition mulpow2_def:
  mulpow2 [] _ = [] ∧
  mulpow2 bs 0 = bs ∧
  mulpow2 bs (SUC k) = F::(mulpow2 bs k)
End

Theorem mulpow2_thm:
  ∀ bs k. bleval (mulpow2 bs k) =  bleval bs * 2 ** k
Proof
  ho_match_mp_tac mulpow2_ind >> gs[mulpow2_def, bleval_def, EXP]
QED

Definition lte_aux_def:
  lte_aux [] [] = T ∧
  lte_aux (F::bs1) (T::bs2) = T ∧
  lte_aux (T::bs1) (F::bs2) = F ∧
  lte_aux (T::bs1) (T::bs2) = lte_aux bs1 bs2 ∧
  lte_aux (F::bs1) (F::bs2) = lte_aux bs1 bs2 ∧
  lte_aux _ _ = F
End

Theorem lte_aux_thm:
  ∀ bs1 bs2.
    LENGTH bs1 = LENGTH bs2 ⇒
    (lte_aux bs1 bs2 ⇔ bleval (REVERSE bs1) ≤ bleval (REVERSE bs2))
Proof
  ho_match_mp_tac lte_aux_ind >> rpt strip_tac
  >> gs[lte_aux_def, bleval_def, bleval_APPEND]
  >- (
    ‘bleval (REVERSE bs1) ≤ 2 ** LENGTH (REVERSE bs1)’
    by gs[LESS_OR_EQ, bleval_less]
    >> ‘LENGTH (REVERSE bs1) = LENGTH bs2’ by gs[LENGTH_REVERSE]
    >> irule LESS_EQ_TRANS
    >> qexists_tac ‘2 ** LENGTH bs2’ >> gs[])
  >> gs[NOT_LEQ]
  >> ‘bleval (REVERSE bs2) < 2 ** LENGTH (REVERSE bs2)’
    by gs[bleval_less]
  >> ‘LENGTH (REVERSE bs2) = LENGTH bs2’ by gs[LENGTH_REVERSE]
  >> ‘SUC (bleval (REVERSE bs2)) ≤ 2 ** LENGTH (REVERSE bs2)’
    by gs[]
  >> irule LESS_EQ_TRANS
  >> qexists_tac ‘2 ** LENGTH bs2’ >> gs[]
QED

Definition zeroPad_def:
  zeroPad [] [] = ([], []) ∧
  zeroPad (b::bs1) [] =
    (let (bs1pad, bs2pad) = zeroPad bs1 [] in
      (b::bs1pad, F::bs2pad)) ∧
  zeroPad [] (b::bs2) =
    (let (bs1pad, bs2pad) = zeroPad [] bs2 in
       (F::bs1pad, b::bs2pad)) ∧
  zeroPad (b1::bs1) (b2::bs2) =
    (let (bs1pad, bs2pad) = zeroPad bs1 bs2 in
       (b1::bs1pad, b2::bs2pad))
End

Theorem zeroPad_thm:
  ∀ bs1 bs2 bs1pad bs2pad.
    zeroPad bs1 bs2 = (bs1pad, bs2pad) ⇒
    bleval bs1 = bleval bs1pad ∧ bleval bs2 = bleval bs2pad ∧
    LENGTH bs1pad = LENGTH bs2pad
Proof
  ho_match_mp_tac zeroPad_ind >> rpt strip_tac
  >> gs[zeroPad_def, bleval_def, CaseEq"prod"]
  >- (
    Cases_on ‘zeroPad bs1 []’ >> gs[zeroPad_def, bleval_def]
    >> Cases_on ‘b’ >> gs[bleval_def]
    >> rpt VAR_EQ_TAC >> gs[bleval_def])
  >- (
    Cases_on ‘zeroPad bs1 []’ >> gs[zeroPad_def, bleval_def]
    >> rpt VAR_EQ_TAC >> gs[bleval_def])
  >- (
    Cases_on ‘zeroPad bs1 []’ >> gs[zeroPad_def, bleval_def]
    >> rpt VAR_EQ_TAC >> gs[])
  >- (
    Cases_on ‘zeroPad [] bs2’ >> gs[zeroPad_def, bleval_def]
    >> Cases_on ‘b’ >> gs[bleval_def]
    >> rpt VAR_EQ_TAC >> gs[bleval_def])
  >- (
    Cases_on ‘zeroPad [] bs2’ >> gs[zeroPad_def, bleval_def]
    >> Cases_on ‘b’ >> gs[bleval_def]
    >> rpt VAR_EQ_TAC >> gs[bleval_def])
  >- (
    Cases_on ‘zeroPad [] bs2’ >> gs[zeroPad_def, bleval_def]
    >> rpt VAR_EQ_TAC >> gs[])
  >- (
    Cases_on ‘zeroPad bs1 bs2’ >> gs[zeroPad_def, bleval_def]
    >> Cases_on ‘b1’ >> gs[bleval_def]
    >> rpt VAR_EQ_TAC >> gs[bleval_def])
  >- (
    Cases_on ‘zeroPad bs1 bs2’ >> gs[zeroPad_def, bleval_def]
    >> Cases_on ‘b2’ >> gs[bleval_def]
    >> rpt VAR_EQ_TAC >> gs[bleval_def])
  >- (
    Cases_on ‘zeroPad bs1 bs2’ >> gs[zeroPad_def, bleval_def]
    >> rpt VAR_EQ_TAC >> gs[])
QED

Definition lte_def:
  lte bs1 bs2 =
  let (bs1pad, bs2pad) = zeroPad bs1 bs2 in
    lte_aux (REV bs1pad []) (REV bs2pad [])
End

Theorem lte_thm:
  ∀ bs1 bs2. lte bs1 bs2 ⇔ bleval bs1 ≤ bleval bs2
Proof
  rpt strip_tac >> gs[lte_def]
  >> Cases_on ‘zeroPad bs1 bs2’ >> imp_res_tac zeroPad_thm
  >> ‘LENGTH (REVERSE q) = LENGTH (REVERSE r)’ by gs[LENGTH_REVERSE]
  >> first_assum $ mp_then Any mp_tac lte_aux_thm
  >> gs[GSYM REVERSE_REV, REVERSE_REVERSE]
QED

Definition sub_aux_def:
  sub_aux [] _ _ = [] ∧
  sub_aux (F :: bs1) [] T = T :: (sub_aux bs1 [] T) ∧
  sub_aux (T :: bs1) [] T = F :: bs1 ∧
  sub_aux (F :: bs1) [] F = F :: bs1 ∧
  sub_aux (T :: bs1) [] F = T :: bs1 ∧
  sub_aux (F :: bs1) (F :: bs2) T = T :: (sub_aux bs1 bs2 T) ∧
  sub_aux (F :: bs1) (F :: bs2) F = F :: (sub_aux bs1 bs2 F) ∧
  sub_aux (F :: bs1) (T :: bs2) T = F :: (sub_aux bs1 bs2 T) ∧
  sub_aux (F :: bs1) (T :: bs2) F = T :: (sub_aux bs1 bs2 T) ∧
  sub_aux (T :: bs1) (F :: bs2) T = F :: (sub_aux bs1 bs2 F) ∧
  sub_aux (T :: bs1) (F :: bs2) F = T :: (sub_aux bs1 bs2 F) ∧
  sub_aux (T :: bs1) (T :: bs2) T = T :: (sub_aux bs1 bs2 T) ∧
  sub_aux (T :: bs1) (T :: bs2) F = F :: (sub_aux bs1 bs2 F)
End

Definition sub_def:
  sub bs1 bs2 = if lte bs2 bs1 then sub_aux bs1 bs2 F else []
End

Theorem sub_aux_thm:
  ∀ bs1 bs2 b.
    (bleval bs2 + if b then 1 else 0) ≤ bleval bs1 ⇒
    bleval (sub_aux bs1 bs2 b) = bleval bs1 - (bleval bs2 + if b then 1 else 0)
Proof
  ho_match_mp_tac sub_aux_ind >> rpt conj_tac >> rpt strip_tac
  >> gs[sub_aux_def, bleval_def, LEFT_SUB_DISTRIB, LEFT_ADD_DISTRIB, SUB_RIGHT_ADD]
  >- (
    TOP_CASE_TAC >> gs[]
    >> ‘bleval bs1 = 1’ by (Cases_on ‘bleval bs1’ >> gs[])
    >> gs[])
  >- (
    COND_CASES_TAC >> gs[]
    >> ‘bleval bs1 = bleval bs2 + 1’ by gs[]
    >> pop_assum $ once_rewrite_tac o single >> gs[])
  >- (
    COND_CASES_TAC >> gs[]
    >> ‘bleval bs1 = bleval bs2 + 1’ by gs[]
    >> pop_assum $ once_rewrite_tac o single >> gs[])
  >- (
    COND_CASES_TAC >> gs[]
    >> ‘bleval bs2 ≤ bleval bs1’ by gs[]
    >> ‘bleval bs2 = bleval bs1’ by gs[]
    >> pop_assum $ once_rewrite_tac o single >> gs[])
  >> COND_CASES_TAC >> gs[]
  >> ‘bleval bs1 = bleval bs2 + 1’ by gs[]
  >> pop_assum $ once_rewrite_tac o single >> gs[]
QED

Theorem sub_thm:
  ∀ m n. bleval (sub m n) = bleval m - bleval n
Proof
  rw[sub_def, lte_thm, sub_aux_thm, bleval_def, SUB_EQ_0, NOT_LEQ]
QED

Theorem karatsuba_num:
  ∀d x y.
    0 < d ⇒
    x * y =
      let x1 = x DIV d in
      let x0 = x MOD d in
      let y1 = y DIV d in
      let y0 = y MOD d in
      let z0 = x0 * y0 in
      let z2 = x1 * y1 in
      let z1a = x1 + x0 in
      let z1b = y1 + y0 in
      let z1 = z1a * z1b in
      let z1 = z1 - z2 - z0 in
        (z2 * d + z1) * d + z0
Proof
  rpt strip_tac
  \\ irule EQ_TRANS
  \\ qexists_tac ‘(x DIV d * d + x MOD d) * (y DIV d * d + y MOD d)’
  \\ conj_tac THEN1 metis_tac [DIVISION]
  \\ fs [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
QED

Theorem karatsuba_bit:
  ∀ x y.
  bleval (mul x y) = bleval (
    let d = (fromBL
            (divpow2
             (add (divpow2 (tobl (LENGTH x) F) 1)
              (divpow2 (tobl (LENGTH y) F) 1)) 1)) + 1 in
      let x1 = divpow2 x d in
      let x0 = modpow2 x d in
      let y1 = divpow2 y d in
      let y0 = modpow2 y d in
      let z0 = mul x0 y0 in
      let z2 = mul x1 y1 in
      let z1a = add x1 x0 in
      let z1b = add y1 y0 in
      let z1Mul = mul z1a z1b in
      let z1 = sub (sub z1Mul z2) z0 in
        add (mulpow2 (add (mulpow2 z2 d) z1) d) z0)
Proof
  rpt strip_tac >> rewrite_tac [mul_thm]
  >> qmatch_goalsub_abbrev_tac ‘fromBL dVal’
  >> qspecl_then [‘2 ** (fromBL dVal + 1)’, ‘bleval x’, ‘bleval y’] mp_tac karatsuba_num
  >> impl_tac
  >- (unabbrev_all_tac >> gs[fromBL_correct, divpow2_thm, add_thm])
  >> disch_then $ rewrite_tac o single
  >> unabbrev_all_tac
  >> gs[divpow2_thm, modpow2_thm, add_thm, mul_thm, mulpow2_thm, sub_thm, fromBL_correct]
QED

(** Infrastructural Theorems for lib implementation **)
Theorem mk_frac_thm[unlisted]:
  !(x:real). x = x / 1
Proof
  gs[]
QED

Theorem id_thm[unlisted]:
  ! (x:real). x = x
Proof
  gs[]
QED

Theorem mul_frac_thm[unlisted]:
  ! a b c (d:real). (a / b) * (c / d) = (a * c) / (b * d)
Proof
  rpt gen_tac >> rewrite_tac [real_div, GSYM REAL_MUL_ASSOC]
  >> ‘inv b * (c * inv d) = c * (inv b * inv d)’ by (gs[REAL_MUL_ASSOC] >> gs[REAL_MUL_COMM])
  >> pop_assum $ once_rewrite_tac o single
  >> gs[REAL_INV_MUL']
QED

val _ = export_theory();
