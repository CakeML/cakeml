open HolKernel SatisfySimps boolLib boolSimps bossLib lcsymtacs pred_setTheory cardinalTheory pairTheory
val _ = temp_tight_equality()
val _ = new_theory"setSpec"

(* http://www.lemma-one.com/ProofPower/specs/spc002.pdf *)

val mem = ``mem:'U->'U->bool``

val _ = Parse.add_infix("<:",425,Parse.NONASSOC)
val _ = Parse.overload_on("<:",mem)

val extensional_def = Define`
  extensional ^mem ⇔ ∀x y. x = y ⇔ ∀a. mem a x ⇔ mem a y`

val is_separation_def = Define`
  is_separation ^mem sub ⇔ ∀x P. ∀a. mem a (sub x P) ⇔ mem a x ∧ P a`

val is_power_def = Define`
  is_power ^mem power ⇔ ∀x. ∀a. mem a (power x) ⇔ ∀b. mem b a ⇒ mem b x`

val is_union_def = Define`
  is_union ^mem union ⇔ ∀x. ∀a. mem a (union x) ⇔ ∃b. mem a b ∧ mem b x`

val is_upair_def = Define`
  is_upair ^mem upair ⇔ ∀x y. ∀a. mem a (upair x y) ⇔ a = x ∨ a = y`

val is_set_theory_def = Define`
  is_set_theory ^mem ⇔
    extensional mem ∧
    (∃sub. is_separation mem sub) ∧
    (∃power. is_power mem power) ∧
    (∃union. is_union mem union) ∧
    (∃upair. is_upair mem upair)`

val separation_unique = store_thm("separation_unique",
  ``extensional ^mem ⇒
    ∀sub1 sub2. is_separation mem sub1 ∧ is_separation mem sub2 ⇒ sub1 = sub2``,
  rw[is_separation_def,extensional_def,FUN_EQ_THM])

val power_unique = store_thm("power_unique",
  ``extensional ^mem ⇒
    ∀power1 power2. is_power mem power1 ∧ is_power mem power2 ⇒ power1 = power2``,
  rw[is_power_def,extensional_def,FUN_EQ_THM])

val union_unique = store_thm("union_unique",
  ``extensional ^mem ⇒
    ∀union1 union2. is_union mem union1 ∧ is_union mem union2 ⇒ union1 = union2``,
  rw[is_union_def,extensional_def,FUN_EQ_THM])

val upair_unique = store_thm("upair_unique",
  ``extensional ^mem ⇒
    ∀upair1 upair2. is_upair mem upair1 ∧ is_upair mem upair2 ⇒ upair1 = upair2``,
  rw[is_upair_def,extensional_def,FUN_EQ_THM])

val sub_def = Define`
  sub ^mem = @sub. is_separation mem sub`

val power_def = Define`
  power ^mem = @power. is_power mem power`

val union_def = Define`
  union ^mem = @union. is_union mem union`

val upair_def = Define`
  upair ^mem = @upair. is_upair mem upair`

val is_extensional = store_thm("is_extensional",
  ``is_set_theory ^mem ⇒ extensional mem``,
  rw[is_set_theory_def])

val is_separation_sub = store_thm("is_separation_sub",
  ``is_set_theory ^mem ⇒ is_separation mem (sub mem)``,
  rw[sub_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_power_power = store_thm("is_power_power",
  ``is_set_theory ^mem ⇒ is_power mem (power mem)``,
  rw[power_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_union_union = store_thm("is_union_union",
  ``is_set_theory ^mem ⇒ is_union mem (union mem)``,
  rw[union_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_upair_upair = store_thm("is_upair_upair",
  ``is_set_theory ^mem ⇒ is_upair mem (upair mem)``,
  rw[upair_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val _ = Parse.add_infix("suchthat",9,Parse.LEFT)
val _ = Parse.overload_on("suchthat",``sub ^mem``)
val _ = Parse.overload_on("Pow",``power ^mem``)
val _ = Parse.overload_on("+",``upair ^mem``)

val mem_sub = store_thm("mem_sub",
  ``is_set_theory ^mem ⇒ ∀x s P. x <: (s suchthat P) ⇔ x <: s ∧ P x``,
  strip_tac >> imp_res_tac is_separation_sub >> fs[is_separation_def])

val mem_power = store_thm("mem_power",
  ``is_set_theory ^mem ⇒
    ∀x y. x <: (Pow y) ⇔ (∀b. b <: x ⇒ b <: y)``,
  strip_tac >> imp_res_tac is_power_power >> fs[is_power_def])

val mem_union = store_thm("mem_union",
  ``is_set_theory ^mem ⇒
    ∀x s. x <: (union mem s) ⇔ ∃a. x <: a ∧ a <: s``,
  strip_tac >> imp_res_tac is_union_union >> fs[is_union_def])

val mem_upair = store_thm("mem_upair",
  ``is_set_theory ^mem ⇒ ∀a x y. a <: (x + y) ⇔ a = x ∨ a = y``,
  strip_tac >> imp_res_tac is_upair_upair >> fs[is_upair_def])

val empty_def = Define`
  empty ^mem = sub mem ARB (K F)`

val _ = Parse.overload_on("∅",``empty ^mem``)

val mem_empty = store_thm("mem_empty",
  ``is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅)``,
  strip_tac >> imp_res_tac is_separation_sub >>
  fs[empty_def,is_separation_def])

val unit_def = Define`
  unit ^mem x = x + x`

val _ = Parse.overload_on("Unit",``unit ^mem``)

val mem_unit = store_thm("mem_unit",
  ``is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y``,
  strip_tac >> imp_res_tac is_upair_upair >>
  fs[is_upair_def,unit_def])

val unit_inj = store_thm("unit_inj",
  ``is_set_theory ^mem ⇒
    ∀x y. Unit x = Unit y ⇔ x = y``,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_unit] >>
  metis_tac[])

val one_def = Define`
  one ^mem = Unit ∅`

val _ = Parse.overload_on("One",``one ^mem``)

val mem_one = store_thm("mem_one",
  ``is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅``,
  strip_tac >> simp[mem_unit,one_def])

val two_def = Define`
  two ^mem = ∅ + One`

val _ = Parse.overload_on("Two",``two ^mem``)

val mem_two = store_thm("mem_two",
  ``is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One``,
  strip_tac >> simp[mem_upair,mem_one,two_def])

val pair_def = Define`
  pair ^mem x y = (Unit x) + (x + y)`

val _ = Parse.overload_on(",",``pair ^mem``)

val upair_inj = store_thm("upair_inj",
  ``is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c``,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_upair] >>
  metis_tac[])

val unit_eq_upair = store_thm("unit_eq_upair",
  ``is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z``,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_unit,mem_upair] >>
  metis_tac[])

val pair_inj = store_thm("pair_inj",
  ``is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d``,
  strip_tac >> fs[pair_def] >> rw[] >>
  simp[upair_inj,unit_inj,unit_eq_upair] >>
  metis_tac[])

val binary_union_def = Define`
  binary_union ^mem x y = union mem (upair mem x y)`

val _ = Parse.overload_on("UNION",``binary_union ^mem``)

val mem_binary_union = store_thm("mem_binary_union",
  ``is_set_theory ^mem ⇒
    ∀a x y. a <: (x ∪ y) ⇔ a <: x ∨ a <: y``,
  strip_tac >> fs[binary_union_def,mem_union,mem_upair] >>
  metis_tac[])

val product_def = Define`
  product ^mem x y =
    (Pow (Pow (x ∪ y)) suchthat
     λa. ∃b c. b <: x ∧ c <: y ∧ a = (b,c))`

val _ = Parse.overload_on("CROSS",``product ^mem``)

val mem_product = store_thm("mem_product",
  ``is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y``,
  strip_tac >> fs[product_def] >>
  simp[mem_sub,mem_power,mem_binary_union] >>
  rw[EQ_IMP_THM] >> TRY(metis_tac[]) >>
  rfs[pair_def,mem_upair] >> rw[] >>
  rfs[mem_unit,mem_upair])

val relspace_def = Define`
  relspace ^mem x y = Pow (x × y)`

val _ = Parse.overload_on("Relspace",``relspace ^mem``)

val funspace_def = Define`
  funspace ^mem x y =
    (Relspace x y suchthat
     λf. ∀a. a <: x ⇒ ∃!b. (a,b) <: f)`

val _ = Parse.overload_on("Funspace",``funspace ^mem``)

val apply_def = Define`
  apply ^mem x y = @a. (y,a) <: x`

val _ = Parse.overload_on("'",``apply ^mem``)

val _ = Parse.overload_on("boolset",``Two``)

val true_def = Define`
  true ^mem = ∅`

val false_def = Define`
  false ^mem = One`

val _ = Parse.overload_on("True",``true ^mem``)
val _ = Parse.overload_on("False",``false ^mem``)

val true_neq_false = store_thm("true_neq_false",
  ``is_set_theory ^mem ⇒ True ≠ False``,
  strip_tac >>
  imp_res_tac mem_one >>
  imp_res_tac mem_empty >>
  fs[true_def,false_def,is_set_theory_def,extensional_def,one_def] >>
  metis_tac[])

val mem_boolset = store_thm("mem_boolset",
  ``is_set_theory ^mem ⇒
    ∀x. x <: boolset ⇔ ((x = True) ∨ (x = False))``,
  strip_tac >> fs[mem_two,true_def,false_def])

val boolean_def = Define`
  boolean ^mem b = if b then True else False`

val _ = Parse.overload_on("Boolean",``boolean ^mem``)

val boolean_in_boolset = store_thm("boolean_in_boolset",
  ``is_set_theory ^mem ⇒
    ∀b. Boolean b <: boolset``,
  strip_tac >> imp_res_tac mem_boolset >>
  Cases >> simp[boolean_def])

val boolean_eq_true = store_thm("boolean_eq_true",
  ``is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b``,
  strip_tac >> rw[boolean_def,true_neq_false])

val holds_def = Define`
  holds ^mem s x ⇔ s ' x = True`

val _ = Parse.overload_on("Holds",``holds ^mem``)

val abstract_def = Define`
  abstract ^mem dom rng f = (dom × rng suchthat λx. ∃a. x = (a,f a))`

val _ = Parse.overload_on("Abstract",``abstract ^mem``)

val apply_abstract = store_thm("apply_abstract",
  ``is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x``,
  strip_tac >>
  rw[apply_def,abstract_def] >>
  SELECT_ELIM_TAC >>
  simp[mem_sub,mem_product,pair_inj])

val apply_abstract_matchable = store_thm("apply_abstract_matchable",
  ``∀f x s t u. x <: s ∧ f x <: t ∧ is_set_theory ^mem ∧ f x = u ⇒ Abstract s t f ' x = u``,
  metis_tac[apply_abstract])

val apply_in_rng = store_thm("apply_in_rng",
  ``is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t``,
  strip_tac >>
  simp[funspace_def,mem_sub,relspace_def,
       mem_power,apply_def,mem_product,EXISTS_UNIQUE_THM] >>
  rw[] >> res_tac >> SELECT_ELIM_TAC >> res_tac >> rfs[pair_inj] >> metis_tac[])

val abstract_in_funspace = store_thm("abstract_in_funspace",
  ``is_set_theory ^mem ⇒
    ∀f s t. (∀x. x <: s ⇒ f x <: t) ⇒ Abstract s t f <: Funspace s t``,
  strip_tac >>
  simp[funspace_def,relspace_def,abstract_def,mem_power,mem_product,mem_sub] >>
  simp[EXISTS_UNIQUE_THM,pair_inj])

val abstract_eq = store_thm("abstract_eq",
  ``is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. x <: s ⇒ f x <: t1 ∧ g x <: t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g``,
  rw[] >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  simp[abstract_def,mem_sub,mem_product] >>
  metis_tac[pair_inj])

val in_funspace_abstract = store_thm("in_funspace_abstract",
  ``is_set_theory ^mem ⇒
    ∀z s t. z <: Funspace s t ⇒
    ∃f. z = Abstract s t f ∧ (∀x. x <: s ⇒ f x <: t)``,
  rw[funspace_def,mem_sub,relspace_def,mem_power] >>
  qexists_tac`λx. @y. (x,y) <: z` >>
  conj_tac >- (
    imp_res_tac is_extensional >>
    pop_assum(fn th => SIMP_TAC std_ss [SIMP_RULE std_ss [extensional_def] th]) >>
    simp[abstract_def,EQ_IMP_THM] >> gen_tac >>
    rfs[mem_sub,mem_product] >>
    conj_tac >>
    TRY strip_tac >>
    rfs[pair_inj] >>
    fs[EXISTS_UNIQUE_THM] >>
    metis_tac[] ) >>
  rfs[EXISTS_UNIQUE_THM,mem_product] >>
  metis_tac[pair_inj])

val axiom_of_choice = save_thm("axiom_of_choice",UNDISCH(prove(
  ``is_set_theory ^mem ⇒
    ∀x. (∀a. mem a x ⇒ ∃b. mem b a) ⇒
       ∃f. ∀a. mem a x ⇒ mem (f ' a) a``,
  rw[] >>
  qexists_tac`Abstract x (union mem x) (λa. @b. mem b a)` >>
  rw[] >>
  qmatch_abbrev_tac`z <: a` >>
  qsuff_tac`z = @b. b <: a` >- (
    SELECT_ELIM_TAC >> rw[] ) >>
  unabbrev_all_tac >>
  match_mp_tac apply_abstract_matchable >>
  rw[mem_union] >>
  SELECT_ELIM_TAC >> rw[] >>
  metis_tac[])))

val indset = ``indset:'U``
val ch = ``ch:'U->'U``
val s = ``(^mem,^indset,^ch)``

val _ = Parse.overload_on("M",s)

val is_choice_def = Define`
  is_choice ^mem ch = ∀x. (∃a. a <: x) ⇒ ch x <: x`

val is_infinite_def = Define`
  is_infinite ^mem s = INFINITE {a | a <: s}`

val is_model_def = Define`
  is_model ^s ⇔
    is_set_theory mem ∧
    is_infinite mem indset ∧
    is_choice mem ch`

val is_model_is_set_theory = store_thm("is_model_is_set_theory",
  ``is_model M ⇒ is_set_theory ^mem``,
  rw[is_model_def])

val indset_inhabited = store_thm("indset_inhabited",
  ``is_infinite ^mem indset ⇒ ∃i. i <: indset``,
  rw[is_infinite_def] >> imp_res_tac INFINITE_INHAB >>
  fs[] >> metis_tac[])

val funspace_inhabited = store_thm("funspace_inhabited",
  ``is_set_theory ^mem ⇒ ∀s t. (∃x. x <: s) ∧ (∃x. x <: t) ⇒ ∃f. f <: Funspace s t``,
  rw[] >> qexists_tac`Abstract s t (λx. @x. x <: t)` >>
  match_mp_tac (MP_CANON abstract_in_funspace) >>
  metis_tac[])

val tuple_def = Define`
  (tuple0 ^mem [] = ∅) ∧
  (tuple0 ^mem (a::as) = (a, tuple0 ^mem as))`
val _ = Parse.overload_on("tuple",``tuple0 ^mem``)

val pair_not_empty = store_thm("pair_not_empty",
  ``is_set_theory ^mem ⇒ (x,y) ≠ ∅``,
  rw[] >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_empty] >>
  pop_assum kall_tac >>
  simp[pair_def,mem_upair] >>
  metis_tac[])

val tuple_empty = store_thm("tuple_empty",
  ``is_set_theory ^mem ⇒ ∀ls. tuple ls = ∅ ⇔ ls = []``,
  strip_tac >> Cases >> simp[tuple_def] >>
  simp[pair_not_empty] )

val tuple_inj = store_thm("tuple_inj",
  ``is_set_theory ^mem ⇒
    ∀l1 l2. tuple l1 = tuple l2 ⇔ l1 = l2``,
  strip_tac >>
  Induct >> simp[tuple_def] >- metis_tac[tuple_empty] >>
  gen_tac >> Cases >> simp[tuple_def,pair_not_empty] >>
  simp[pair_inj])

val bigcross_def = Define`
  (bigcross0 ^mem [] = One) ∧
  (bigcross0 ^mem (a::as) = a × (bigcross0 ^mem as))`
val _ = Parse.overload_on("bigcross",``bigcross0 ^mem``)

val mem_bigcross = store_thm("mem_bigcross",
  ``is_set_theory ^mem ⇒
    ∀ls x. (mem x (bigcross ls) ⇔ ∃xs. x = tuple xs ∧ LIST_REL mem xs ls)``,
  strip_tac >> Induct >>
  simp[bigcross_def,tuple_def,mem_one] >>
  simp[mem_product,PULL_EXISTS,tuple_def])

val _ = export_theory()
