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
val _ = export_rewrites["is_extensional"]

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

val _ = export_rewrites["is_separation_sub","is_power_power","is_union_union","is_upair_upair"]

val _ = Parse.overload_on("Sub",``sub ^mem``)
val _ = Parse.overload_on("+",``upair ^mem``)
val _ = Parse.overload_on("Pow",``power ^mem``)

val empty_def = Define`
  empty ^mem = sub mem ARB (K F)`

val _ = Parse.overload_on("∅",``empty ^mem``)

val unit_def = Define`
  unit ^mem x = x + x`

val _ = Parse.overload_on("Unit",``unit ^mem``)

val one_def = Define`
  one ^mem = Unit ∅`

val _ = Parse.overload_on("One",``one ^mem``)

val two_def = Define`
  two ^mem = ∅ + One`

val _ = Parse.overload_on("Two",``two ^mem``)

val pair_def = Define`
  pair ^mem x y = (Unit x) + (x + y)`

val _ = Parse.overload_on(",",``pair ^mem``)

val binary_union_def = Define`
  binary_union ^mem x y = union mem (upair mem x y)`

val _ = Parse.overload_on("UNION",``binary_union ^mem``)

val product_def = Define`
  product ^mem x y =
    Sub (Pow (Pow (x ∪ y)))
        (λa. ∃b c. mem b x ∧ mem c y ∧ a = (b,c))`

val _ = Parse.overload_on("CROSS",``product ^mem``)

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

val _ = export_theory()
