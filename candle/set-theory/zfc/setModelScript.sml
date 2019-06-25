(*
  An example universe satisfying setSpecTheory
*)
app load ["preamble", "bitTheory", "setSpecTheory", "dep_rewrite"];
open preamble bitTheory setSpecTheory dep_rewrite
val _ = temp_tight_equality()
val _ = new_theory"setModel"

val is_set_theory_pred_def = Define`
  is_set_theory_pred is_v_rep in_rep ⇔
   (∃x. is_v_rep x) ∧
   (∀x y. is_v_rep x ∧ is_v_rep y ⇒ ((x = y) ⇔ (∀a. is_v_rep a ⇒ (in_rep a x ⇔ in_rep a y)))) ∧
   (∀x P. is_v_rep x ⇒ ∃y. is_v_rep y ∧ ∀a. is_v_rep a ⇒ (in_rep a y ⇔ (in_rep a x ∧ P a))) ∧
   (∀x. is_v_rep x ⇒ ∃y. is_v_rep y ∧ (∀a. is_v_rep a ⇒ (in_rep a y ⇔ (∀b. is_v_rep b ⇒ in_rep b a ⇒ in_rep b x)))) ∧
   (∀x. is_v_rep x ⇒ ∃y. is_v_rep y ∧ (∀a. is_v_rep a ⇒ (in_rep a y ⇔ (∃b. is_v_rep b ∧ in_rep a b ∧ in_rep b x)))) ∧
   (∀x y. is_v_rep x ∧ is_v_rep y ⇒ ∃z. is_v_rep z ∧ (∀a. is_v_rep a ⇒ (in_rep a z ⇔ (a = x ∨ a = y)))) ∧
   (∀x. is_v_rep x ⇒ (∃y. is_v_rep y ∧ in_rep y x) ⇒
                      ∃y. is_v_rep y ∧ in_rep y x ∧ ∀z. is_v_rep z ⇒ ~(in_rep z x ∧ in_rep z y)) ∧
   (∀R. (∀x y z. is_v_rep x ∧ is_v_rep y ∧ is_v_rep z ⇒
                 R x y ∧ R x z ⇒ y = z) ⇒
        ∀d. is_v_rep d ⇒
            ∃r. is_v_rep r ∧
                ∀y. is_v_rep y ⇒
                    (in_rep y r ⇔ ∃x. is_v_rep x ∧ in_rep x d ∧ R x y)) ∧
   (∀x. is_v_rep x ⇒ ∃y. is_v_rep y ∧ (∀a. is_v_rep a ∧ in_rep a x ⇒ in_rep y x))`

val LESS_EXP = TAC_PROOF(([],
  ``!n:num. n < 2 ** n``),
  Induct >> simp[EXP])

val FINITE_NUM = TAC_PROOF(([],
  ``!n:num. FINITE (\x. x < n)``),
  Induct >- simp[GSYM EMPTY_DEF] >>
  MATCH_MP_TAC FINITE_DIFF_down >>
  qexists_tac `\x. x < n` >>
  simp[DIFF_DEF] >>
  rewrite_tac[DECIDE ``(x < SUC n ∧ ¬(x < n)) = (x = n)``] >>
  simp_tac(bool_ss ++ pred_setLib.PRED_SET_ss)[])

val BIT_num_from_bin_list_el = TAC_PROOF(([],
  ``∀bs. EVERY ($> 2) bs ⇒
         ∀x. BIT x (num_from_bin_list bs) ⇔ (if x < LENGTH bs then EL x bs = 1 else F)``),
  REPEAT strip_tac >>
  COND_CASES_TAC >- simp[numposrepTheory.BIT_num_from_bin_list] >>
  simp[BIT_num_from_bin_list_leading])

val FINITE_BIT_num_from_bin_list = TAC_PROOF(([],
  ``!bs. EVERY ($> 2) bs ⇒ FINITE (λx. BIT x (num_from_bin_list bs))``),
  rw[] >>
  simp[BIT_num_from_bin_list_el] >>
  MATCH_MP_TAC SUBSET_FINITE_I >>
  qexists_tac `\x. x < LENGTH bs` >>
  simp[FINITE_NUM,SUBSET_DEF])

val FINITE_BIT_ELEMS = TAC_PROOF(([],
  ``!n:num. FINITE (λx. BIT x n)``),
  gen_tac >>
  CONV_TAC ((RAND_CONV o ABS_CONV o RAND_CONV) (REWR_CONV (GSYM I_THM))) >>
  PURE_REWRITE_TAC[SYM numposrepTheory.num_bin_list] >>
  rewrite_tac[o_THM] >>
  MATCH_MP_TAC FINITE_BIT_num_from_bin_list >>
  simp[numposrepTheory.num_to_bin_list_def,numposrepTheory.n2l_BOUND])

val FINITE_SET_IMAGE = TAC_PROOF(([],
  ``!s. FINITE s ==>
      !R. (!x:'a y:'b z. R x y ∧ R x z ⇒ (y = z)) ⇒
          !n:num. FINITE (λy. ∃x. x IN s ∧ R x y)``),
  pred_setLib.SET_INDUCT_TAC >-
    ( simp[] >> simp[GSYM EMPTY_DEF] ) >>
  rw[] >>
  MATCH_MP_TAC FINITE_DIFF_down >>
  qexists_tac`λy. ∃x. x ∈ s ∧ R x y` >>
  res_tac >>
  simp[DIFF_DEF] >>
  `∀x. ((∃x'. (x' = e ∨ x' ∈ s) ∧ R x' x) ∧ ∀x'. x' ∉ s ∨ ¬R x' x)
              = (R e x ∧ ∀x'. x' ∉ s ∨ ¬R x' x)` by metis_tac[] >>
  simp[] >>
  match_mp_tac SUBSET_FINITE_I >>
  qexists_tac`\x. R e x` >>
  conj_tac >- (
    cases_on `?y. R e y` >|
      [ POP_ASSUM STRIP_ASSUME_TAC >>
        `(λx. R e x) = {y}`
          by ( simp[EXTENSION] >> metis_tac[] ) >>
        simp[],

        `(λx. R e x) = {}`
          by ( simp[EXTENSION] >> metis_tac[] ) >>
        simp[]
      ] ) >>
  simp[SUBSET_DEF])

val REFORM_RULE = CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV
                             THENC REWRITE_CONV[AND_IMP_INTRO])

val FINITE_SET_IMAGE_I =
  REFORM_RULE FINITE_SET_IMAGE

val FINITE_BIT_IMAGE = TAC_PROOF(([],
  ``!n R. (!x y z. R x y ∧ R x z ⇒ (y = z)) ⇒
          FINITE (λy. ∃x. BIT x n ∧ R x y)``),
  rw[] >>
  `!x. BIT x n = (x IN (\u. BIT u n))` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  HO_MATCH_MP_TAC FINITE_SET_IMAGE_I >>
  simp[FINITE_BIT_ELEMS] >>
  FIRST_ASSUM ACCEPT_TAC)

val FINITE_SET_THEORY_IMAGE = TAC_PROOF(([],
  ``(∀(x: α+num) y (z: α+num). ISR x ∧ ISR y ∧ ISR z ⇒ R x y ∧ R x z ⇒ y = z) ⇒
    !n:num. FINITE (λy. ∃x. BIT x n ∧ R (INR x) (INR y))``),
  strip_tac >>
  gen_tac >>
  ho_match_mp_tac FINITE_BIT_IMAGE >>
  rw[] >>
  first_assum (mp_tac o REFORM_RULE o SPECL[``(INR x):'a+num``,``(INR y):'a+num``,``(INR y'):'a+num``]) >>
  simp[])

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
    simp[] ) >>
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
  conj_tac >- (
    rw[] >>
    qabbrev_tac`xx = OUTR x` >>
    qabbrev_tac`yy = OUTR y` >>
    qexists_tac`INR (LEAST zz. BIT zz xx)` >>
    simp[] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- metis_tac[] >>
    rw[] >>
    qabbrev_tac`zz = OUTR z` >>
    Cases_on `zz < n` >- simp[] >>
    disj2_tac >>
    MATCH_MP_TAC NOT_BIT_GT_TWOEXP >>
    MP_TAC (SPEC ``zz:num`` LESS_EXP) >>
    simp[] ) >>
  conj_tac >- (
    rw[] >>
    qabbrev_tac`dd = OUTR d` >>
    qexists_tac`INR (num_from_bin_list
      (GENLIST (λy. if (∃x. BIT x dd ∧ R (INR x) (INR y)) then 1 else 0)
      (SUC (MAX_SET (\y. ∃x. BIT x dd ∧ R (INR x) (INR y))))))` >>
    simp[] >> rw[] >>
    qabbrev_tac`yy = OUTR y` >>
    qmatch_abbrev_tac`BIT yy (num_from_bin_list ll) ⇔ P` >>
    `EVERY ($> 2) ll` by (
      simp[Abbr`ll`,EVERY_GENLIST] >> rw[] ) >>
    EQ_TAC >|
      [ strip_tac >>
        `¬(LENGTH ll ≤ yy)` by metis_tac[BIT_num_from_bin_list_leading] >>
        fs[arithmeticTheory.NOT_LESS_EQUAL] >>
        imp_res_tac numposrepTheory.BIT_num_from_bin_list >>
        pop_assum mp_tac >>
        simp[Abbr`ll`] >>
        fs[EL_GENLIST] >>
        COND_CASES_TAC >> simp[] >>
        pop_assum strip_assume_tac >>
        simp[Abbr`P`] >>
        qexists_tac`INR x` >>
        pop_assum mp_tac >>
        simp[Abbr`yy`],

        simp[Abbr`P`] >>
        strip_tac >>
        `yy < LENGTH ll` by (
          simp[Abbr`ll`] >>
          rewrite_tac[GSYM LESS_EQ_IFF_LESS_SUC] >>
          match_mp_tac (REFORM_RULE in_max_set) >>
          imp_res_tac FINITE_SET_THEORY_IMAGE >>
          simp[] >>
          qexists_tac`OUTR x` >>
          simp[Abbr`yy`] ) >>
        simp[numposrepTheory.BIT_num_from_bin_list] >>
        simp[Abbr`ll`] >>
        fs[LENGTH_GENLIST,EL_GENLIST] >>
        COND_CASES_TAC >- rewrite_tac[] >>
        pop_assum mp_tac >>
        simp[] >>
        qexists_tac`OUTR x` >>
        simp[Abbr`yy`]
      ] ) >>
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
  conj_tac >- (
    simp[is_upair_def,GSYM SKOLEM_THM] >>
    rw[] >>
    qspecl_then[`dest_V x`]mp_tac
      (List.nth(CONJUNCTS V_mem_rep_def,5)) >>
    simp[V_bij] >>
    simp[V_mem_def] >>
    metis_tac[V_bij] ) >>
  conj_tac >- (
    simp[regular_def] >>
    rw[V_mem_def] >>
    qspecl_then[`dest_V x`]mp_tac
      (List.nth(CONJUNCTS V_mem_rep_def,6)) >>
    simp[V_bij] >>
    metis_tac[V_bij] ) >>
  simp[replacement_def,is_functional_def] >>
  rw[V_mem_def] >>
  qspec_then`\x y. R (mk_V x) (mk_V y)` mp_tac
    (List.nth(CONJUNCTS V_mem_rep_def,7)) >>
  simp[] >>
  `∀x y z.
    is_V x ∧ is_V y ∧ is_V z ⇒
    R (mk_V x) (mk_V y) ∧
    R (mk_V x) (mk_V z) ⇒
    y = z` by metis_tac[V_bij] >>
  asm_rewrite_tac[] >>
  disch_then (strip_assume_tac o REWRITE_RULE[V_bij] o Q.SPEC`dest_V d`) >>
  metis_tac[V_bij]
QED

val V_choice_exists = Q.prove(
  `∃ch. is_choice V_mem ch`,
  simp[is_choice_def,GSYM SKOLEM_THM] >>
  rw[] >> simp[V_mem_def] >>
  qspecl_then[`dest_V x`]mp_tac
    (List.nth(CONJUNCTS V_mem_rep_def,8)) >>
  simp[V_bij] >>
  metis_tac[V_bij] )

val V_choice_def =
  new_specification("V_choice_def",["V_choice"],V_choice_exists)

val V_indset_def =
  new_specification("V_indset_def",["V_indset"],
    METIS_PROVE[]``∃i:α V. (∃x:α V. is_inductive V_mem x) ⇒ is_inductive V_mem i``)

Theorem is_model_V:
   (∃I:α V. is_inductive V_mem I) ⇒
    is_model (V_mem,V_indset:α V,V_choice)
Proof
  simp[is_model_def,is_set_theory_V,V_choice_def,V_indset_def]
QED

val _ = print_theory_to_file "-" "setModel";

val _ = export_theory()
