open HolKernel SatisfySimps boolLib boolSimps bossLib lcsymtacs pred_setTheory cardinalTheory pairTheory
val _ = numLib.prefer_num()
val _ = new_theory"polySet"

(* http://www.lemma-one.com/ProofPower/specs/spc002.pdf *)

val mem = ``mem:'U->'U->bool``

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

val _ = Parse.overload_on("Sub",``sub ^mem``)
val _ = Parse.overload_on("Pow",``power ^mem``)
val _ = Parse.overload_on("+",``upair ^mem``)

val mem_sub = store_thm("mem_sub",
  ``is_set_theory ^mem ⇒ ∀x s P. mem x (Sub s P) ⇔ mem x s ∧ P x``,
  strip_tac >> imp_res_tac is_separation_sub >> fs[is_separation_def])

val mem_power = store_thm("mem_power",
  ``is_set_theory ^mem ⇒
    ∀x y. mem x (Pow y) ⇔ (∀b. mem b x ⇒ mem b y)``,
  strip_tac >> imp_res_tac is_power_power >> fs[is_power_def])

val mem_union = store_thm("mem_union",
  ``is_set_theory ^mem ⇒
    ∀x s. mem x (union mem s) ⇔ ∃a. mem x a ∧ mem a s``,
  strip_tac >> imp_res_tac is_union_union >> fs[is_union_def])

val mem_upair = store_thm("mem_upair",
  ``is_set_theory ^mem ⇒ ∀a x y. mem a (x + y) ⇔ a = x ∨ a = y``,
  strip_tac >> imp_res_tac is_upair_upair >> fs[is_upair_def])

val empty_def = Define`
  empty ^mem = sub mem ARB (K F)`

val _ = Parse.overload_on("∅",``empty ^mem``)

val mem_empty = store_thm("mem_empty",
  ``is_set_theory ^mem ⇒ ∀x. ¬mem x ∅``,
  strip_tac >> imp_res_tac is_separation_sub >>
  fs[empty_def,is_separation_def])

val unit_def = Define`
  unit ^mem x = x + x`

val _ = Parse.overload_on("Unit",``unit ^mem``)

val mem_unit = store_thm("mem_unit",
  ``is_set_theory ^mem ⇒
    ∀x y. mem x (Unit y) ⇔ x = y``,
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
    ∀x. mem x One ⇔ x = ∅``,
  strip_tac >> simp[mem_unit,one_def])

val two_def = Define`
  two ^mem = ∅ + One`

val _ = Parse.overload_on("Two",``two ^mem``)

val mem_two = store_thm("mem_two",
  ``is_set_theory ^mem ⇒
    ∀x. mem x Two ⇔ x = ∅ ∨ x = One``,
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
    ∀a x y. mem a (x ∪ y) ⇔ mem a x ∨ mem a y``,
  strip_tac >> fs[binary_union_def,mem_union,mem_upair] >>
  metis_tac[])

val product_def = Define`
  product ^mem x y =
    Sub (Pow (Pow (x ∪ y)))
        (λa. ∃b c. mem b x ∧ mem c y ∧ a = (b,c))`

val _ = Parse.overload_on("CROSS",``product ^mem``)

val mem_product = store_thm("mem_product",
  ``is_set_theory ^mem ⇒
    ∀a x y. mem a (x × y) ⇔ ∃b c. a = (b,c) ∧ mem b x ∧ mem c y``,
  strip_tac >> fs[product_def] >>
  simp[mem_sub,mem_power,mem_binary_union] >>
  rw[EQ_IMP_THM] >> TRY(metis_tac[]) >>
  rfs[pair_def,mem_upair] >> rw[] >>
  rfs[mem_unit,mem_upair])

val relspace_def = Define`
  relspace ^mem x y = Pow (x × y)`

val _ = Parse.overload_on("Rel",``relspace ^mem``)

val funspace_def = Define`
  funspace ^mem x y =
    Sub (Rel x y)
        (λf. ∀a. mem a x ⇒ ∃!b. mem (a,b) f)`

val _ = Parse.overload_on("Fun",``funspace ^mem``)

val apply_def = Define`
  apply ^mem x y = @a. mem (y,a) x`

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
    ∀x. mem x boolset ⇔ ((x = True) ∨ (x = False))``,
  strip_tac >> fs[mem_two,true_def,false_def])

val boolean_def = Define`
  boolean ^mem b = if b then True else False`

val _ = Parse.overload_on("Boolean",``boolean ^mem``)

val boolean_in_boolset = store_thm("boolean_in_boolset",
  ``is_set_theory ^mem ⇒
    ∀b. mem (Boolean b) boolset``,
  strip_tac >> imp_res_tac mem_boolset >>
  Cases >> simp[boolean_def])

val boolean_eq_true = store_thm("boolean_eq_true",
  ``is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b``,
  strip_tac >> rw[boolean_def,true_neq_false])

val holds_def = Define`
  holds ^mem s x ⇔ s ' x = True`

val _ = Parse.overload_on("Holds",``holds ^mem``)

val abstract_def = Define`
  abstract ^mem dom rng f = Sub (dom × rng) (λx. ∃a. x = (a,f a))`

val _ = Parse.overload_on("Abstract",``abstract ^mem``)

val apply_abstract = store_thm("apply_abstract",
  ``is_set_theory ^mem ⇒
    ∀f x s t. mem x s ∧ mem (f x) t ⇒ (Abstract s t f) ' x = f x``,
  strip_tac >>
  rw[apply_def,abstract_def] >>
  SELECT_ELIM_TAC >>
  simp[mem_sub,mem_product,pair_inj])

val apply_in_rng = store_thm("apply_in_rng",
  ``is_set_theory ^mem ⇒
    ∀f x s t. mem x s ∧ mem f (Fun s t) ⇒
    mem (f ' x) t``,
  strip_tac >>
  simp[funspace_def,mem_sub,relspace_def,
       mem_power,apply_def,mem_product,EXISTS_UNIQUE_THM] >>
  rw[] >> res_tac >> SELECT_ELIM_TAC >> res_tac >> rfs[pair_inj] >> metis_tac[])

val abstract_in_funspace = store_thm("abstract_in_funspace",
  ``is_set_theory ^mem ⇒
    ∀f s t. (∀x. mem x s ⇒ mem (f x) t) ⇒ mem (Abstract s t f) (Fun s t)``,
  strip_tac >>
  simp[funspace_def,relspace_def,abstract_def,mem_power,mem_product,mem_sub] >>
  simp[EXISTS_UNIQUE_THM,pair_inj])

val abstract_eq = store_thm("abstract_eq",
  ``is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. mem x s ⇒ mem (f x) t1 ∧ mem (g x) t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g``,
  rw[] >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  simp[abstract_def,mem_sub,mem_product] >>
  metis_tac[pair_inj])

val _ = export_theory()
