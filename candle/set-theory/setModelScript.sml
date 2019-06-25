(*
  An example universe satisfying is_set_theory and (assuming the
  existence of an infinite set) is_model.
*)
open preamble bitTheory setSpecTheory

val _ = new_theory"setModel"

val is_set_theory_pred_def = Define`
  is_set_theory_pred is_v_rep in_rep ⇔
   (∃x. is_v_rep x) ∧
   (∀x y. is_v_rep x ∧ is_v_rep y ⇒ ((x = y) ⇔ (∀a. is_v_rep a ⇒ (in_rep a x ⇔ in_rep a y)))) ∧
   (∀x P. is_v_rep x ⇒ ∃y. is_v_rep y ∧ ∀a. is_v_rep a ⇒ (in_rep a y ⇔ (in_rep a x ∧ P a))) ∧
   (∀x. is_v_rep x ⇒ ∃y. is_v_rep y ∧ (∀a. is_v_rep a ⇒ (in_rep a y ⇔ (∀b. is_v_rep b ⇒ in_rep b a ⇒ in_rep b x)))) ∧
   (∀x. is_v_rep x ⇒ ∃y. is_v_rep y ∧ (∀a. is_v_rep a ⇒ (in_rep a y ⇔ (∃b. is_v_rep b ∧ in_rep a b ∧ in_rep b x)))) ∧
   (∀x y. is_v_rep x ∧ is_v_rep y ⇒ ∃z. is_v_rep z ∧ (∀a. is_v_rep a ⇒ (in_rep a z ⇔ (a = x ∨ a = y)))) ∧
   (∀x. is_v_rep x ⇒ ∃y. is_v_rep y ∧ (∀a. is_v_rep a ∧ in_rep a x ⇒ in_rep y x))`

Theorem l_model_exists:
   ∃(P : α+num -> bool) (mem : α+num -> α+num -> bool). is_set_theory_pred P mem
Proof
  qexists_tac`ISR` >>
  REWRITE_TAC[is_set_theory_pred_def] >>
  qexists_tac`λl1 l2. BIT (OUTR l1) (OUTR l2)` >>
  conj_tac >- (qexists_tac`INR 0` >> simp[]) >>
  conj_tac >- (
    simp[FORALL_SUM] >>
    rw[] >> EQ_TAC >> simp[] >> strip_tac >>
    (C_BIT_11 |> SPEC_ALL |> EQ_IMP_RULE |> fst |> MATCH_MP_TAC) >>
    rw[]) >>
  conj_tac >- (
    rw[FORALL_SUM] >>
    qexists_tac`INR (num_from_bin_list
      (GENLIST (λn. if ODD (EL n (num_to_bin_list (OUTR x))) ∧
                       P (INR n) then 1 else 0)
        (LENGTH (num_to_bin_list (OUTR x)))))` >>
    simp[EVERY_GENLIST] >>
    rw[] >>
    qmatch_abbrev_tac`BIT aa (num_from_bin_list ll) ⇔ BIT aa xx ∧ P a` >>
    `EVERY ($> 2) ll` by (
      simp[Abbr`ll`,EVERY_GENLIST] >> rw[]) >>
    Cases_on`aa < LENGTH ll` >- (
      simp[numposrepTheory.BIT_num_from_bin_list] >>
      simp[Abbr`ll`] >> fs[] >>
      simp[numposrepTheory.EL_num_to_bin_list] >>
      simp[BITV_THM,SBIT_def] >>
      BasicProvers.CASE_TAC >> simp[] >>
      simp[Abbr`aa`] >>
      rw[]) >>
    fs[numposrepTheory.num_to_bin_list_def,numposrepTheory.LENGTH_n2l] >>
    rfs[Abbr`ll`] >>
    simp[BIT_num_from_bin_list_leading] >>
    disj1_tac >>
    Cases_on`xx=0`>>simp[BIT_ZERO]>>fs[]>>
    MATCH_MP_TAC NOT_BIT_GT_LOG2>>
    simp[LOG2_def] ) >>
  conj_tac >- (
    rw[] >>
    qabbrev_tac`xx = OUTR x` >>
    qexists_tac`INR (num_from_bin_list
      (GENLIST (λa. if (∀b. BIT b a ⇒ BIT b xx) then 1 else 0) (2 * (SUC xx))))` >>
    simp[EVERY_GENLIST] >> rw[] >>
    EQ_TAC >- (
      rw[] >>
      qmatch_assum_abbrev_tac`BIT aa (num_from_bin_list ll)` >>
      `EVERY ($> 2) ll` by (
        simp[Abbr`ll`,EVERY_GENLIST] >> rw[] ) >>
      `¬(LENGTH ll ≤ aa)` by metis_tac[BIT_num_from_bin_list_leading] >>
      fs[arithmeticTheory.NOT_LESS_EQUAL] >>
      fs[numposrepTheory.BIT_num_from_bin_list] >>
      qpat_x_assum`EL aa ll = 1`mp_tac >>
      fs[Abbr`ll`] >>
      rw[] ) >>
    strip_tac >>
    qmatch_abbrev_tac`BIT aa (num_from_bin_list ll)` >>
    `EVERY ($> 2) ll` by (
      simp[Abbr`ll`,EVERY_GENLIST] >> rw[] ) >>
    `aa < LENGTH ll` by (
      fs[Abbr`ll`] >>
      Cases_on`aa=0`>>simp[]>>
      spose_not_then strip_assume_tac >>
      fs[arithmeticTheory.NOT_LESS] >>
      first_x_assum(qspec_then`INR (LOG2 aa)`mp_tac) >>
      simp[EVERY_GENLIST,BIT_LOG2] >>
      MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
      qspec_then`aa`mp_tac logrootTheory.LOG_MOD >>
      simp[] >>
      strip_tac >>
      `aa < 2 * (2 ** LOG 2 aa)` by (
        MATCH_MP_TAC arithmeticTheory.LESS_EQ_LESS_TRANS >>
        qexists_tac`2 ** LOG 2 aa + aa MOD 2 ** LOG 2 aa` >>
        REWRITE_TAC[arithmeticTheory.TIMES2] >>
        simp[] ) >>
      `2 * SUC xx < 2 * 2 ** LOG 2 aa` by DECIDE_TAC >>
      `SUC xx < 2 ** LOG 2 aa` by DECIDE_TAC >>
      simp[LOG2_def] ) >>
    simp[numposrepTheory.BIT_num_from_bin_list] >>
    fs[Abbr`ll`] >>
    rw[] >> fs[] >>
    first_x_assum(qspec_then`INR b`mp_tac) >>
    simp[EVERY_GENLIST] ) >>
  conj_tac >- (
    rw[] >>
    qabbrev_tac`xx = OUTR x` >>
    qexists_tac`INR (num_from_bin_list
      (GENLIST (λa. if (∃b. BIT b xx ∧ BIT a b) then 1 else 0)
      (LENGTH (num_to_bin_list xx))))` >>
    simp[EVERY_GENLIST] >> rw[] >>
    qmatch_abbrev_tac`BIT aa (num_from_bin_list ll) ⇔ P` >>
    `EVERY ($> 2) ll` by (
      simp[Abbr`ll`,EVERY_GENLIST] >> rw[] ) >>
    EQ_TAC >- (
      strip_tac >>
      `¬(LENGTH ll ≤ aa)` by metis_tac[BIT_num_from_bin_list_leading] >>
      fs[arithmeticTheory.NOT_LESS_EQUAL] >>
      qpat_x_assum`BIT X Y`mp_tac >>
      simp[numposrepTheory.BIT_num_from_bin_list] >>
      fs[Abbr`ll`,Abbr`P`] >> rw[] >>
      qexists_tac`INR b` >>
      simp[EVERY_GENLIST] ) >>
    qunabbrev_tac`P` >> strip_tac >>
    `aa < LENGTH ll` by (
      fs[Abbr`ll`] >>
      simp[numposrepTheory.num_to_bin_list_def] >>
      simp[numposrepTheory.LENGTH_n2l] >>
      rw[] >> fs[BIT_ZERO] >>
      `¬(LOG2 xx < OUTR b)` by metis_tac[NOT_BIT_GT_LOG2] >>
      fs[arithmeticTheory.NOT_LESS] >>
      `¬(OUTR b < 2 ** aa)` by metis_tac[NOT_BIT_GT_TWOEXP] >>
      fs[arithmeticTheory.NOT_LESS] >>
      fs[LOG2_def] >>
      qsuff_tac`aa < 2 ** aa` >- DECIDE_TAC >>
      match_mp_tac arithmeticTheory.X_LT_EXP_X >>
      simp[] ) >>
    simp[numposrepTheory.BIT_num_from_bin_list] >>
    fs[Abbr`ll`] >>
    rw[] >> metis_tac[] ) >>
  conj_tac >- (
    rw[] >>
    qabbrev_tac`xx = OUTR x` >>
    qabbrev_tac`yy = OUTR y` >>
    qexists_tac`INR (num_from_bin_list
      (GENLIST (λa. if a = xx ∨ a = yy then 1 else 0) (SUC (MAX xx yy))))` >>
    simp[EVERY_GENLIST] >>
    rw[] >>
    qmatch_abbrev_tac`BIT aa (num_from_bin_list ll) ⇔ P` >>
    `EVERY ($> 2) ll` by (
      simp[Abbr`ll`,EVERY_GENLIST] >> rw[] ) >>
    EQ_TAC >- (
      strip_tac >>
      `¬(LENGTH ll ≤ aa)` by metis_tac[BIT_num_from_bin_list_leading] >>
      fs[arithmeticTheory.NOT_LESS_EQUAL] >>
      simp[Abbr`P`] >>
      qpat_x_assum`BIT X Y`mp_tac >>
      simp[numposrepTheory.BIT_num_from_bin_list] >>
      fs[Abbr`ll`] >>
      BasicProvers.CASE_TAC >> simp[] >>
      Cases_on`a`>>Cases_on`y`>>Cases_on`x`>>fs[]) >>
    simp[Abbr`P`] >>
    strip_tac >>
    `aa < LENGTH ll` by (
      fs[Abbr`ll`] >>
      qmatch_abbrev_tac`q < SUC r` >>
      rfs[] >>
      qsuff_tac`q <= r` >- DECIDE_TAC >>
      simp[Abbr`r`] ) >>
    simp[numposrepTheory.BIT_num_from_bin_list] >>
    fs[Abbr`ll`]) >>
  rw[] >>
  Cases_on`OUTR x=0`>>simp[BIT_ZERO] >- (
    qexists_tac`INR 0` >> simp[] ) >>
  qexists_tac`INR (LOG2 (OUTR x))` >>
  simp[BIT_LOG2,EVERY_GENLIST]
QED

val is_V_def = new_specification("is_V_def",["is_V"],REWRITE_RULE[is_set_theory_pred_def]l_model_exists)

val V_tyax = new_type_definition("V",
  is_V_def |> SIMP_RULE std_ss [GSYM PULL_EXISTS] |> CONJUNCT1)
val V_bij = define_new_type_bijections
  {ABS="mk_V",REP="dest_V",name="V_bij",tyax=V_tyax}
val dest_V_11   = prove_rep_fn_one_one V_bij

val V_mem_rep_def =
  new_specification("V_mem_rep_def",["V_mem_rep"],is_V_def)

val V_mem_def = Define`V_mem x y = V_mem_rep (dest_V x) (dest_V y)`

Theorem is_set_theory_V:
   is_set_theory V_mem
Proof
  simp[is_set_theory_def] >>
  conj_tac >- (
    simp[extensional_def] >>
    simp[V_mem_def] >>
    rw[] >>
    qspecl_then[`dest_V x`,`dest_V y`]mp_tac
      (List.nth(CONJUNCTS V_mem_rep_def,1)) >>
    simp[V_bij,dest_V_11] >> rw[] >>
    metis_tac[V_bij] ) >>
  conj_tac >- (
    simp[is_separation_def,GSYM SKOLEM_THM] >>
    rw[] >>
    qspecl_then[`dest_V x`,`P o mk_V`]mp_tac
      (List.nth(CONJUNCTS V_mem_rep_def,2)) >>
    simp[V_bij] >>
    simp[V_mem_def] >>
    metis_tac[V_bij] ) >>
  conj_tac >- (
    simp[is_power_def,GSYM SKOLEM_THM] >>
    rw[] >>
    qspecl_then[`dest_V x`]mp_tac
      (List.nth(CONJUNCTS V_mem_rep_def,3)) >>
    simp[V_bij] >>
    simp[V_mem_def] >>
    metis_tac[V_bij] ) >>
  conj_tac >- (
    simp[is_union_def,GSYM SKOLEM_THM] >>
    rw[] >>
    qspecl_then[`dest_V x`]mp_tac
      (List.nth(CONJUNCTS V_mem_rep_def,4)) >>
    simp[V_bij] >>
    simp[V_mem_def] >>
    metis_tac[V_bij] ) >>
  simp[is_upair_def,GSYM SKOLEM_THM] >>
  rw[] >>
  qspecl_then[`dest_V x`]mp_tac
    (List.nth(CONJUNCTS V_mem_rep_def,5)) >>
  simp[V_bij] >>
  simp[V_mem_def] >>
  metis_tac[V_bij]
QED

val V_choice_exists = Q.prove(
  `∃ch. is_choice V_mem ch`,
  simp[is_choice_def,GSYM SKOLEM_THM] >>
  rw[] >> simp[V_mem_def] >>
  qspecl_then[`dest_V x`]mp_tac
    (List.nth(CONJUNCTS V_mem_rep_def,6)) >>
  simp[V_bij] >>
  metis_tac[V_bij] )

val V_choice_def =
  new_specification("V_choice_def",["V_choice"],V_choice_exists)

val V_indset_def =
  new_specification("V_indset_def",["V_indset"],
    METIS_PROVE[]``∃i:α V. (∃x:α V. is_infinite V_mem x) ⇒ is_infinite V_mem i``)

Theorem is_model_V:
   (∃I:α V. is_infinite V_mem I) ⇒
    is_model (V_mem,V_indset:α V,V_choice)
Proof
  simp[is_model_def,is_set_theory_V,V_choice_def,V_indset_def]
QED

val _ = export_theory()
