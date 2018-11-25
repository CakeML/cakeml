(*
  Zermelo's set theory
*)
app load ["SatisfySimps", "lcsymtacs"];
open HolKernel SatisfySimps boolLib boolSimps bossLib lcsymtacs pred_setTheory cardinalTheory pairTheory
val _ = temp_tight_equality()
val _ = new_theory"setSpec"

(* TODO: this functionality should be implemented by Parse *)
local val ct = current_theory () in
fun remove_tyabbrev s =
  let
    val _ = Parse.temp_set_grammars(type_grammar.remove_abbreviation(Parse.type_grammar())s,Parse.term_grammar())
    val q = String.concat["val ",ct,"_grammars = (type_grammar.remove_abbreviation(#1 ",ct,"_grammars)\"",s,"\",#2 ",ct,"_grammars);"]
    val _ = adjoin_to_theory{sig_ps=NONE, struct_ps=SOME(fn _ => PP.add_string q)}
  in () end
end
val _ = remove_tyabbrev"reln"
val _ = remove_tyabbrev"inf"
(* -- *)

val REFORM_RULE = CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV
                             THENC REWRITE_CONV[AND_IMP_INTRO])

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

val regular_def = Define`
  regular ^mem ⇔ ∀x. (∃y. mem y x) ⇒ ∃y. mem y x ∧ ∀z. ~(mem z x ∧ mem z y)`

val is_functional_def = Define`
  is_functional (R:'a -> 'b -> bool) ⇔ ∀x y z. R x y ∧ R x z ⇒ y = z`

val replacement_def = Define`
  replacement ^mem ⇔
      ∀R. is_functional R ⇒
          ∀d. ∃r. ∀y. mem y r ⇔ ∃x. mem x d ∧ R x y`

val is_set_theory_def = Define`
  is_set_theory ^mem ⇔
    extensional mem ∧
    (∃sub. is_separation mem sub) ∧
    (∃power. is_power mem power) ∧
    (∃union. is_union mem union) ∧
    (∃upair. is_upair mem upair) ∧
    regular mem ∧
    replacement mem`

val separation_unique = Q.store_thm("separation_unique",
  `extensional ^mem ⇒
    ∀sub1 sub2. is_separation mem sub1 ∧ is_separation mem sub2 ⇒ sub1 = sub2`,
  rw[is_separation_def,extensional_def,FUN_EQ_THM])

val power_unique = Q.store_thm("power_unique",
  `extensional ^mem ⇒
    ∀power1 power2. is_power mem power1 ∧ is_power mem power2 ⇒ power1 = power2`,
  rw[is_power_def,extensional_def,FUN_EQ_THM])

val union_unique = Q.store_thm("union_unique",
  `extensional ^mem ⇒
    ∀union1 union2. is_union mem union1 ∧ is_union mem union2 ⇒ union1 = union2`,
  rw[is_union_def,extensional_def,FUN_EQ_THM])

val upair_unique = Q.store_thm("upair_unique",
  `extensional ^mem ⇒
    ∀upair1 upair2. is_upair mem upair1 ∧ is_upair mem upair2 ⇒ upair1 = upair2`,
  rw[is_upair_def,extensional_def,FUN_EQ_THM])

val sub_def = Define`
  sub ^mem = @sub. is_separation mem sub`

val power_def = Define`
  power ^mem = @power. is_power mem power`

val union_def = Define`
  union ^mem = @union. is_union mem union`

val upair_def = Define`
  upair ^mem = @upair. is_upair mem upair`

val is_extensional = Q.store_thm("is_extensional",
  `is_set_theory ^mem ⇒ extensional mem`,
  rw[is_set_theory_def])

val is_separation_sub = Q.store_thm("is_separation_sub",
  `is_set_theory ^mem ⇒ is_separation mem (sub mem)`,
  rw[sub_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_power_power = Q.store_thm("is_power_power",
  `is_set_theory ^mem ⇒ is_power mem (power mem)`,
  rw[power_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_union_union = Q.store_thm("is_union_union",
  `is_set_theory ^mem ⇒ is_union mem (union mem)`,
  rw[union_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_upair_upair = Q.store_thm("is_upair_upair",
  `is_set_theory ^mem ⇒ is_upair mem (upair mem)`,
  rw[upair_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def])

val is_regular = Q.store_thm("is_regular",
  `is_set_theory ^mem ⇒ regular mem`,
  rw[is_set_theory_def])

val _ = Parse.add_infix("suchthat",9,Parse.LEFT)
val _ = Parse.overload_on("suchthat",``sub ^mem``)
val _ = Parse.overload_on("Pow",``power ^mem``)
val _ = Parse.overload_on("+",``upair ^mem``)
val _ = Parse.overload_on("⋃",``union ^mem``)

val mem_sub = Q.store_thm("mem_sub",
  `is_set_theory ^mem ⇒ ∀x s P. x <: (s suchthat P) ⇔ x <: s ∧ P x`,
  strip_tac >> imp_res_tac is_separation_sub >> fs[is_separation_def])

val mem_power = Q.store_thm("mem_power",
  `is_set_theory ^mem ⇒
    ∀x y. x <: (Pow y) ⇔ (∀b. b <: x ⇒ b <: y)`,
  strip_tac >> imp_res_tac is_power_power >> fs[is_power_def])

val mem_union = Q.store_thm("mem_union",
  `is_set_theory ^mem ⇒
    ∀x s. x <: ⋃ s ⇔ ∃a. x <: a ∧ a <: s`,
  strip_tac >> imp_res_tac is_union_union >> fs[is_union_def])

val mem_upair = Q.store_thm("mem_upair",
  `is_set_theory ^mem ⇒ ∀a x y. a <: (x + y) ⇔ a = x ∨ a = y`,
  strip_tac >> imp_res_tac is_upair_upair >> fs[is_upair_def])

val empty_def = Define`
  empty ^mem = sub mem ARB (K F)`

val _ = Parse.overload_on("∅",``empty ^mem``)

val mem_empty = Q.store_thm("mem_empty",
  `is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅)`,
  strip_tac >> imp_res_tac is_separation_sub >>
  fs[empty_def,is_separation_def])

val not_empty = Q.store_thm("not_empty",
  `is_set_theory ^mem ⇒ ∀x. ¬(x = ∅) ⇔ ∃y. y <: x`,
  strip_tac >> imp_res_tac is_extensional >>
  fs[empty_def,extensional_def,mem_sub])

val eq_empty = Q.store_thm("eq_empty",
  `is_set_theory ^mem ⇒ ∀x. (x = ∅) ⇔ ∀y. ~(y <: x)`,
  strip_tac >> imp_res_tac is_extensional >>
  fs[empty_def,extensional_def,mem_sub])

val unit_def = Define`
  unit ^mem x = x + x`

val _ = Parse.overload_on("Unit",``unit ^mem``)

val mem_unit = Q.store_thm("mem_unit",
  `is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y`,
  strip_tac >> imp_res_tac is_upair_upair >>
  fs[is_upair_def,unit_def])

val unit_inj = Q.store_thm("unit_inj",
  `is_set_theory ^mem ⇒
    ∀x y. Unit x = Unit y ⇔ x = y`,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_unit] >>
  metis_tac[])

val one_def = Define`
  one ^mem = Unit ∅`

val _ = Parse.overload_on("One",``one ^mem``)

val mem_one = Q.store_thm("mem_one",
  `is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅`,
  strip_tac >> simp[mem_unit,one_def])

val two_def = Define`
  two ^mem = ∅ + One`

val _ = Parse.overload_on("Two",``two ^mem``)

val mem_two = Q.store_thm("mem_two",
  `is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One`,
  strip_tac >> simp[mem_upair,mem_one,two_def])

val binary_inter_def = Define`
  binary_inter ^mem x y = (x suchthat λz. z <: y)`

val _ = Parse.overload_on("INTER",``binary_inter ^mem``)

val mem_binary_inter = Q.store_thm("mem_binary_inter",
  `is_set_theory ^mem ⇒
    ∀x y z. x <: y ∩ z ⇔ x <: y ∧ x <: z`,
  strip_tac >> simp[binary_inter_def,mem_sub])

val subset_def = Define`
  subset ^mem x y = ∀z. z <: x ⇒ z <: y`

val _ = Parse.overload_on("SUBSET",``subset ^mem``)

val subset_refl = Q.store_thm("subset_refl",
  `is_set_theory ^mem ⇒
    ∀x. x ⊆ x`,
  strip_tac >> simp[subset_def])

val subset_mem = Q.store_thm("subset_mem",
  `is_set_theory ^mem ⇒
    ∀x y z. x <: y ∧ y ⊆ z ⇒ x <: z`,
  strip_tac >> simp[subset_def])

val psubset_def = Define`
  psubset ^mem x y = (x ⊆ y ∧ ~(x = y))`

val _ = Parse.overload_on("PSUBSET",``psubset ^mem``)

val pair_def = Define`
  pair ^mem x y = (Unit x) + (x + y)`

val _ = Parse.overload_on(",",``pair ^mem``)

val mem_pair = Q.store_thm("mem_pair",
  `is_set_theory ^mem ⇒
    ∀a x y. a <: (x,y) ⇔ a = Unit x ∨ a = (x + y)`,
  strip_tac >>
  simp[pair_def,mem_upair])

val upair_inj = Q.store_thm("upair_inj",
  `is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c`,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_upair] >>
  metis_tac[])

val unit_eq_upair = Q.store_thm("unit_eq_upair",
  `is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z`,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_unit,mem_upair] >>
  metis_tac[])

val pair_inj = Q.store_thm("pair_inj",
  `is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d`,
  strip_tac >> fs[pair_def] >> rw[] >>
  simp[upair_inj,unit_inj,unit_eq_upair] >>
  metis_tac[])

val binary_union_def = Define`
  binary_union ^mem x y = ⋃ (upair mem x y)`

val _ = Parse.overload_on("UNION",``binary_union ^mem``)

val mem_binary_union = Q.store_thm("mem_binary_union",
  `is_set_theory ^mem ⇒
    ∀a x y. a <: (x ∪ y) ⇔ a <: x ∨ a <: y`,
  strip_tac >> fs[binary_union_def,mem_union,mem_upair] >>
  metis_tac[])

val product_def = Define`
  product ^mem x y =
    (Pow (Pow (x ∪ y)) suchthat
     λa. ∃b c. b <: x ∧ c <: y ∧ a = (b,c))`

val _ = Parse.overload_on("CROSS",``product ^mem``)

val mem_product = Q.store_thm("mem_product",
  `is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y`,
  strip_tac >> fs[product_def] >>
  simp[mem_sub,mem_power,mem_binary_union] >>
  rw[EQ_IMP_THM] >> TRY(metis_tac[]) >>
  rfs[pair_def,mem_upair] >> rw[] >>
  rfs[mem_unit,mem_upair])

val relspace_def = Define`
  relspace ^mem x y = Pow (x × y)`

val _ = Parse.overload_on("Relspace",``relspace ^mem``)

val mem_relspace = Q.store_thm("mem_relspace",
  `is_set_theory ^mem ⇒
    ∀d r f. f <: Relspace d r ⇔
            f <: Pow (d × r)`,
  rw[relspace_def])

val relspace_pairs = Q.store_thm("relspace_pairs",
  `is_set_theory ^mem ⇒
    ∀d r f a. f <: Relspace d r ∧ a <: f ⇒ ∃x y. x <: d ∧ y <: r ∧ a = (x,y)`,
  strip_tac >>
  simp[relspace_def,mem_sub,mem_power,mem_product] >>
  metis_tac[])

val mem_rel = Q.store_thm("mem_rel",
  `is_set_theory ^mem ⇒
    ∀d r f. f <: Relspace d r ⇒
            ∀x y. (x,y) <: f ⇒ x <: d ∧ y <: r`,
  strip_tac >>
  simp[relspace_def,mem_power,mem_product] >>
  metis_tac[pair_inj])

val funspace_def = Define`
  funspace ^mem x y =
    (Relspace x y suchthat
     λf. ∀a. a <: x ⇒ ∃!b. (a,b) <: f)`

val _ = Parse.overload_on("Funspace",``funspace ^mem``)

val mem_funspace = Q.store_thm("mem_funspace",
  `is_set_theory ^mem ⇒
    ∀d r f. f <: Funspace d r ⇔
            f <: Relspace d r ∧ ∀x. x <: d ⇒ ∃!y. (x,y) <: f`,
  rw[funspace_def,mem_sub])

val funspace_pairs = Q.store_thm("funspace_pairs",
  `is_set_theory ^mem ⇒
    ∀d r f a. f <: Funspace d r ∧ a <: f ⇒ ∃x y. x <: d ∧ y <: r ∧ a = (x,y)`,
  strip_tac >>
  simp[funspace_def,mem_sub] >>
  metis_tac[relspace_pairs])

val apply_def = Define`
  apply ^mem x y = @a. (y,a) <: x`

val _ = Parse.overload_on("'",``apply ^mem``)

val id_def = Define`
  id ^mem d = (d × d suchthat λa. ∃b. a = (b,b))`

val _ = Parse.overload_on("Id",``id ^mem``)

val mem_id = Q.store_thm("mem_id",
  `is_set_theory ^mem ⇒
        ∀d x y. (x,y) <: Id d ⇔ (y <: d ∧ x = y)`,
  strip_tac >>
  simp[id_def,mem_sub,mem_product,pair_inj] >>
  rw[] >>
  EQ_TAC >>
  strip_tac >>
  asm_rewrite_tac[])

val replacement = Q.store_thm("replacement",
  `is_set_theory ^mem ⇒
     ∀R. is_functional R ⇒
          ∀d. ∃r. ∀y. y <: r ⇔ ∃x. x <: d ∧ R x y`,
  DISCH_TAC >> IMP_RES_TAC is_set_theory_def >>
  IMP_RES_THEN MP_TAC replacement_def >>
  rw[])

val image_def = Define`
  image ^mem f d = @r. ∀y. y <: r ⇔ ∃x. x <: d ∧ f x = y`

val _ = Parse.hide "''"
val _ = Parse.add_infix("''",2000,Parse.LEFT)
val _ = Parse.overload_on("''",``image ^mem``)

val mem_image = Q.store_thm("mem_image",
  `is_set_theory ^mem ⇒
    ∀f d y. y <: f '' d ⇔ ∃x. x <: d ∧ f x = y`,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC replacement >>
  `is_functional (λx y. f x = y)` by simp[is_functional_def] >>
  rw[image_def] >> SELECT_ELIM_TAC >> rw[replacement])

val is_one_one_def = Define`
  is_one_one ^mem f d ⇔ ∀x y z. x <: d ∧ (x,z) <: f ∧ (y,z) <: f ⇒ x = y`

val _ = Parse.overload_on("is_11",``is_one_one ^mem``)

val is_onto_def = Define`
  is_onto ^mem f r ⇔ ∀y. y <: r ⇒ ∃x. (x,y) <: f`

val _ = Parse.overload_on("is_Onto",``is_onto ^mem``)

val inverse_def = Define`
  inverse ^mem f ⇔ @f1. ∀a. a <: f1 ⇔ ∃x y. a = (x,y) ∧ (y,x) <: f`

val _ = Parse.overload_on("Inverse",``inverse ^mem``)

val mem_inverse = Q.store_thm("mem_inverse",
  `is_set_theory ^mem ⇒
    ∀f x y. (x,y) <: Inverse f ⇔ (y,x) <: f`,
  strip_tac >> simp[inverse_def] >> rw[] >>
  SELECT_ELIM_TAC >>
  conj_tac >- (
    qexists_tac`(⋃ (⋃ f) × ⋃ (⋃ f)) suchthat λa. ∃x y. a = (x,y) ∧ (y,x) <: f` >>
    simp[mem_sub,mem_product,mem_union,pair_inj] >>
    metis_tac[mem_pair,mem_unit,mem_upair,pair_inj] ) >>
  metis_tac[pair_inj])

val inverse_pairs = Q.store_thm("inverse_pairs",
  `is_set_theory ^mem ⇒
    ∀f a. a <: Inverse f ⇒ ∃y x. a = (y,x)`,
  strip_tac >> simp[inverse_def] >>
  REPEAT gen_tac >>
  SELECT_ELIM_TAC >>
  conj_tac >- (
    qexists_tac`(⋃ (⋃ f) × ⋃ (⋃ f)) suchthat λa. ∃x y. a = (x,y) ∧ (y,x) <: f` >>
    simp[mem_sub,mem_product,mem_union,pair_inj] >>
    metis_tac[mem_pair,mem_unit,mem_upair,pair_inj] ) >>
  metis_tac[])

(* Unless f is 1-1 and onto, Inverse f is not a function. *)

val funspace_inverse = Q.store_thm("funspace_inverse",
  `is_set_theory ^mem ⇒
    ∀f d r. f <: Funspace d r ∧ is_11 f d ∧ is_Onto f r ⇒ Inverse f <: Funspace r d`,
  strip_tac >>
  simp[is_one_one_def,is_onto_def,mem_funspace,mem_relspace,mem_power,mem_product,EXISTS_UNIQUE_THM] >>
  REPEAT gen_tac >> strip_tac >>
  conj_tac >|
    [ rw[] >>
      imp_res_tac inverse_pairs >>
      metis_tac[mem_inverse,pair_inj],
      simp[mem_inverse] >>
      metis_tac[pair_inj]
    ])

val inverse_is_11_onto = Q.store_thm("inverse_is_11_onto",
  `is_set_theory ^mem ⇒
    ∀f d r. f <: Funspace d r ∧ is_11 f d ∧ is_Onto f r ⇒ is_11 (Inverse f) r ∧ is_Onto (Inverse f) d`,
  strip_tac >>
  simp[is_one_one_def,is_onto_def,mem_funspace,mem_relspace,mem_power,mem_product,EXISTS_UNIQUE_THM] >>
  REPEAT gen_tac >> strip_tac >>
  conj_tac >|
    [ simp[mem_inverse] >>
      metis_tac[pair_inj],
      simp[mem_inverse]
    ])

val mem_funspace_pairs = Q.store_thm("mem_funspace_pairs",
  `is_set_theory ^mem ⇒
    ∀f d r. f <: Funspace d r ⇒ ∀a. a <: f ⇒ ∃x y. a = (x,y)`,
  strip_tac >>
  simp[is_one_one_def,is_onto_def,mem_funspace,mem_relspace,mem_power,mem_product,EXISTS_UNIQUE_THM] >>
  metis_tac[])

val pop_tac = pop_assum (fn th => all_tac)

val inverse_inverse_eq_id = Q.store_thm("inverse_inverse_eq_id",
  `is_set_theory ^mem ⇒
    ∀f d r. f <: Funspace d r ∧ is_11 f d ∧ is_Onto f r ⇒ Inverse (Inverse f) = f`,
  rw[] >>
  `is_11 (Inverse f) r ∧ is_Onto (Inverse f) d` by metis_tac[inverse_is_11_onto] >>
  `Inverse f <: Funspace r d` by simp[funspace_inverse] >>
  `Inverse (Inverse f) <: Funspace d r` by simp[funspace_inverse] >>
  imp_res_tac is_extensional >>
  fs[extensional_def] >>
  pop_tac >>
  imp_res_tac mem_funspace_pairs >>
  metis_tac[pair_inj,mem_inverse])

val _ = Parse.overload_on("boolset",``Two``)

val true_def = Define`
  true ^mem = ∅`

val false_def = Define`
  false ^mem = One`

val _ = Parse.overload_on("True",``true ^mem``)
val _ = Parse.overload_on("False",``false ^mem``)

val true_neq_false = Q.store_thm("true_neq_false",
  `is_set_theory ^mem ⇒ True ≠ False`,
  strip_tac >>
  imp_res_tac mem_one >>
  imp_res_tac mem_empty >>
  fs[true_def,false_def,is_set_theory_def,extensional_def,one_def] >>
  metis_tac[])

val mem_boolset = Q.store_thm("mem_boolset",
  `is_set_theory ^mem ⇒
    ∀x. x <: boolset ⇔ ((x = True) ∨ (x = False))`,
  strip_tac >> fs[mem_two,true_def,false_def])

val boolean_def = Define`
  boolean ^mem b = if b then True else False`

val _ = Parse.overload_on("Boolean",``boolean ^mem``)

val boolean_in_boolset = Q.store_thm("boolean_in_boolset",
  `is_set_theory ^mem ⇒
    ∀b. Boolean b <: boolset`,
  strip_tac >> imp_res_tac mem_boolset >>
  Cases >> simp[boolean_def])

val boolean_eq_true = Q.store_thm("boolean_eq_true",
  `is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b`,
  strip_tac >> rw[boolean_def,true_neq_false])

val holds_def = Define`
  holds ^mem s x ⇔ s ' x = True`

val _ = Parse.overload_on("Holds",``holds ^mem``)

val suc_def = Define`
  suc ^mem x = x ∪ Unit x`

val _ = Parse.overload_on("Suc",``suc ^mem``)

val mem_suc = Q.store_thm("mem_suc",
  `is_set_theory ^mem ⇒
    ∀x y. x <: (Suc y) ⇔ x = y ∨ x <: y`,
  strip_tac >> rw[suc_def,mem_binary_union,mem_unit] >> METIS_TAC[])

val suc_not_empty = Q.store_thm("suc_not_empty",
  `is_set_theory ^mem ⇒
    ∀x. ~(∅ = Suc x)`,
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_empty] >>
  simp[suc_def,mem_binary_union,mem_unit] >>
  metis_tac[])

val not_mem_ident = Q.store_thm("not_mem_ident",
  `is_set_theory ^mem ⇒
    ∀x. ~(x <: x)`,
  strip_tac >>
  imp_res_tac is_regular >>
  gen_tac >>
  strip_tac >>
  fs[regular_def] >>
  first_assum (mp_tac o Q.SPEC`Unit x`) >>
  simp[mem_unit])

val not_mem_cycle = Q.store_thm("not_mem_cycle",
  `is_set_theory ^mem ⇒
    ∀x y. ~(x <: y ∧ y <: x)`,
  strip_tac >>
  imp_res_tac is_regular >>
  REPEAT gen_tac >>
  strip_tac >>
  fs[regular_def] >>
  first_assum (mp_tac o Q.SPEC`x + y`) >>
  metis_tac[mem_upair])

val suc_11 = Q.store_thm("suc_11",
  `is_set_theory ^mem ⇒
    ∀x y. (Suc x = Suc y) ⇔ (x = y)`,
  metis_tac[mem_suc,not_mem_cycle])


val abstract_def = Define`
  abstract ^mem dom rng f = (dom × rng suchthat λx. ∃a. x = (a,f a))`

val _ = Parse.overload_on("Abstract",``abstract ^mem``)

val apply_abstract = Q.store_thm("apply_abstract",
  `is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x`,
  strip_tac >>
  rw[apply_def,abstract_def] >>
  SELECT_ELIM_TAC >>
  simp[mem_sub,mem_product,pair_inj])

val apply_abstract_matchable = Q.store_thm("apply_abstract_matchable",
  `∀f x s t u. x <: s ∧ f x <: t ∧ is_set_theory ^mem ∧ f x = u ⇒ Abstract s t f ' x = u`,
  metis_tac[apply_abstract])

val apply_in_rng = Q.store_thm("apply_in_rng",
  `is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t`,
  strip_tac >>
  simp[funspace_def,mem_sub,relspace_def,
       mem_power,apply_def,mem_product,EXISTS_UNIQUE_THM] >>
  rw[] >> res_tac >> SELECT_ELIM_TAC >> res_tac >> rfs[pair_inj] >> metis_tac[])

val abstract_in_funspace = Q.store_thm("abstract_in_funspace",
  `is_set_theory ^mem ⇒
    ∀f s t. (∀x. x <: s ⇒ f x <: t) ⇒ Abstract s t f <: Funspace s t`,
  strip_tac >>
  simp[funspace_def,relspace_def,abstract_def,mem_power,mem_product,mem_sub] >>
  simp[EXISTS_UNIQUE_THM,pair_inj])

val abstract_eq = Q.store_thm("abstract_eq",
  `is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. x <: s ⇒ f x <: t1 ∧ g x <: t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g`,
  rw[] >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  simp[abstract_def,mem_sub,mem_product] >>
  metis_tac[pair_inj])

val in_funspace_abstract = Q.store_thm("in_funspace_abstract",
  `is_set_theory ^mem ⇒
    ∀z s t. z <: Funspace s t ⇒
    ∃f. z = Abstract s t f ∧ (∀x. x <: s ⇒ f x <: t)`,
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

val apply_eq_mem = Q.store_thm("apply_eq_mem",
  `is_set_theory ^mem ⇒
    ∀f d r. f <: Funspace d r ⇒
            ∀x. x <: d ⇒ ∀y. f ' x = y ⇔ (x,y) <: f`,
  strip_tac >> simp[apply_def,mem_funspace,EXISTS_UNIQUE_THM] >> rw[] >>
  SELECT_ELIM_TAC >>
  conj_tac >- simp[] >>
  metis_tac[])

val id_funspace = Q.store_thm("id_funspace",
  `is_set_theory ^mem ⇒
    ∀d. Id d <: Funspace d d`,
  strip_tac >>
  simp[id_def,funspace_def,mem_sub,mem_relspace,mem_power,mem_product,pair_inj,EXISTS_UNIQUE_THM])

val apply_id = Q.store_thm("apply_id",
  `is_set_theory ^mem ⇒
    ∀d x. x <: d ⇒ Id d ' x = x`,
  rw[] >>
  imp_res_tac id_funspace >>
  pop_assum (assume_tac o SPEC_ALL) >>
  imp_res_tac apply_eq_mem >>
  asm_rewrite_tac[] >>
  simp[mem_id])

val apply_extensional = Q.store_thm("apply_extensional",
  `is_set_theory ^mem ⇒
    ∀d r f g. f <: Funspace d r ∧ g <: Funspace d r ⇒ ((f = g) ⇔ ∀x. x <: d ⇒ f ' x = g ' x)`,
  rw[] >>
  EQ_TAC >|
    [ strip_tac >>
      asm_rewrite_tac[],

      strip_tac >>
      imp_res_tac is_extensional >>
      pop_assum mp_tac >>
      simp[extensional_def] >>
      disch_then kall_tac >>
      gen_tac >> EQ_TAC >> strip_tac >>
      `∃x y. x <: d ∧ y <: r ∧ a = (x,y)` by metis_tac[funspace_pairs] >>
      pop_assum (fn th => fs[th]) >>
      res_tac >>
      pop_assum mp_tac >>
      metis_tac[apply_eq_mem]
    ])

val dep_funspace_def = Define`
  dep_funspace ^mem d f =
    (Funspace d (⋃ (f '' d)) suchthat
     λg. ∀x. x <: d ⇒ g ' x <: f x)`

val _ = Parse.overload_on("Dep_funspace",``dep_funspace ^mem``)

val mem_dep_funspace = Q.store_thm("mem_dep_funspace",
  `is_set_theory ^mem ⇒
    ∀f d g. g <: Dep_funspace d f ⇔
            g <: Relspace d (⋃ (f '' d)) ∧
            ∀x. x <: d ⇒ (∃!y. (x,y) <: g) ∧ g ' x <: f x`,
  rw[dep_funspace_def,mem_sub,mem_funspace] >>
  METIS_TAC[])

val dep_prodspace_def = Define`
  dep_prodspace ^mem d f =
    (d × ⋃ (f '' d) suchthat
     λr. ∀x y. (x,y) <: r ⇒ x <: d ∧ y <: f x)`

val _ = Parse.overload_on("Dep_prodspace",``dep_prodspace ^mem``)

val mem_dep_prodspace = Q.store_thm("mem_dep_prodspace",
  `is_set_theory ^mem ⇒
    ∀f d r. r <: Dep_prodspace d f ⇔
            r <: d × ⋃ (f '' d) ∧
            ∀x y. (x,y) <: r ⇒ x <: d ∧ y <: f x`,
  rw[dep_prodspace_def,mem_sub])

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

(* The following version of the infinity axiom is taken from page 12 of
   "Set Theory, The Third Millennium Edition" by Thomas Jech, Springer, 2006,
   using the successor operator as defined (Definition 1.20) on page 19 of
   "Introduction to Set Theory" by J. Donald Monk, McGraw Hill, 1969.
*)

val is_inductive_def = Define`
  is_inductive ^mem s ⇔
      ∅ <: s ∧ ∀x. x <: s ⇒ Suc x <: s`

val is_model_def = Define`
  is_model ^s ⇔
    is_set_theory mem ∧
    is_inductive mem indset ∧
    is_choice mem ch`

val is_model_is_set_theory = Q.store_thm("is_model_is_set_theory",
  `is_model M ⇒ is_set_theory ^mem`,
  rw[is_model_def])

val indset_inhabited = Q.store_thm("indset_inhabited",
  `is_infinite ^mem indset ⇒ ∃i. i <: indset`,
  rw[is_infinite_def] >> imp_res_tac INFINITE_INHAB >>
  fs[] >> metis_tac[])

val inductive_set_inhabited = Q.store_thm("inductive_set_inhabited",
  `is_inductive ^mem indset ⇒ ∃i. i <: indset`,
  metis_tac[is_inductive_def])

val num2indset_def = Define`
  (num2indset ^mem 0 = ∅) ∧
  (num2indset ^mem (SUC n) = Suc (num2indset mem n))`;

val _ = Parse.overload_on("Num2indset",``num2indset ^mem``)

val num2indset_in_indset = Q.store_thm("num2indset_in_indset",
  `is_inductive ^mem indset ⇒ ∀n. Num2indset n <: indset`,
  simp[is_inductive_def] >>
  strip_tac >>
  Induct >>
  simp[num2indset_def])

val empty_num2indset = Q.store_thm("empty_num2indset",
  `is_set_theory ^mem ⇒
    ∀n. ∅ = Num2indset n ∨ ∅ <: Num2indset n`,
  strip_tac >>
  Induct >>
  simp[num2indset_def,mem_suc])

val full_mem_num2indset = Q.store_thm("full_mem_num2indset",
  `is_set_theory ^mem ⇒
    ∀n m. m < n ⇒ Num2indset m <: Num2indset n`,
  strip_tac >>
  Induct >>
  simp[prim_recTheory.NOT_LESS_0,prim_recTheory.LESS_THM,num2indset_def,mem_suc] >>
  metis_tac[])

val mem_num2indset_is_num2indset = Q.store_thm("mem_num2indset_is_num2indset",
  `is_set_theory ^mem ⇒
    ∀n a. a <: Num2indset n ⇒ ∃m. a = Num2indset m ∧ m < n`,
  strip_tac >>
  Induct >>
  simp[prim_recTheory.NOT_LESS_0,prim_recTheory.LESS_THM,num2indset_def,mem_empty,mem_suc] >>
  metis_tac[])

val mem_num2indset_is_num2indset_eq = Q.store_thm("mem_num2indset_is_num2indset_eq",
  `is_set_theory ^mem ⇒
    ∀n a. (a <: Num2indset n) = ∃m. a = Num2indset m ∧ m < n`,
  metis_tac[mem_num2indset_is_num2indset,full_mem_num2indset] )

val MAX_SUC = TAC_PROOF(([],
  ``∀a b. MAX (SUC a) (SUC b) = SUC (MAX a b)``),
  simp[arithmeticTheory.MAX_DEF])

val num2indset_11 = Q.store_thm("num2indset_11",
  `is_set_theory ^mem ⇒
    ∀n m. (Num2indset n = Num2indset m) ⇔ (n = m)`,
  strip_tac >>
  completeInduct_on `MAX n m` >>
  Cases >> Cases >>
  simp[num2indset_def,mem_suc,mem_empty,suc_not_empty,empty_num2indset] >>
  simp[MAX_SUC] >>
  strip_tac >>
  first_assum (mp_tac o Q.SPEC`MAX n' n`) >>
  first_assum (fn th => rewrite_tac[th]) >>
  rewrite_tac[prim_recTheory.LESS_SUC_REFL] >>
  strip_tac >>
  simp[suc_11])

val num2indset_mem_less = Q.store_thm("num2indset_mem_less",
  `is_set_theory ^mem ⇒
    ∀n m. (Num2indset m <: Num2indset n) ⇔ (m < n)`,
  strip_tac >>
  simp[mem_num2indset_is_num2indset_eq] >>
  simp[num2indset_11])

val inductive_set_infinite = Q.store_thm("inductive_set_infinite",
  `is_set_theory ^mem ∧ is_inductive ^mem indset ⇒ is_infinite mem indset`,
  rw[is_infinite_def] >>
  match_mp_tac (REFORM_RULE INFINITE_SUBSET) >>
  qexists_tac`pred_set$IMAGE Num2indset UNIV` >>
  conj_tac >| [
      match_mp_tac (REFORM_RULE IMAGE_11_INFINITE) >>
      simp_tac (bool_ss ++ pred_setLib.PRED_SET_ss) [] >>
      simp[num2indset_11],

      simp_tac (bool_ss ++ pred_setLib.PRED_SET_ss) [SUBSET_DEF] >>
      rw[] >>
      simp[num2indset_in_indset] ])

val funspace_inhabited = Q.store_thm("funspace_inhabited",
  `is_set_theory ^mem ⇒ ∀s t. (∃x. x <: s) ∧ (∃x. x <: t) ⇒ ∃f. f <: Funspace s t`,
  rw[] >> qexists_tac`Abstract s t (λx. @x. x <: t)` >>
  match_mp_tac (MP_CANON abstract_in_funspace) >>
  metis_tac[])

val tuple_def = Define`
  (tuple0 ^mem [] = ∅) ∧
  (tuple0 ^mem (a::as) = (a, tuple0 ^mem as))`
val _ = Parse.overload_on("tuple",``tuple0 ^mem``)

val pair_not_empty = Q.store_thm("pair_not_empty",
  `is_set_theory ^mem ⇒ (x,y) ≠ ∅`,
  rw[] >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_empty] >>
  pop_assum kall_tac >>
  simp[pair_def,mem_upair] >>
  metis_tac[])

val tuple_empty = Q.store_thm("tuple_empty",
  `is_set_theory ^mem ⇒ ∀ls. tuple ls = ∅ ⇔ ls = []`,
  strip_tac >> Cases >> simp[tuple_def] >>
  simp[pair_not_empty] )

val tuple_inj = Q.store_thm("tuple_inj",
  `is_set_theory ^mem ⇒
    ∀l1 l2. tuple l1 = tuple l2 ⇔ l1 = l2`,
  strip_tac >>
  Induct >> simp[tuple_def] >- metis_tac[tuple_empty] >>
  gen_tac >> Cases >> simp[tuple_def,pair_not_empty] >>
  simp[pair_inj])

val bigcross_def = Define`
  (bigcross0 ^mem [] = One) ∧
  (bigcross0 ^mem (a::as) = a × (bigcross0 ^mem as))`
val _ = Parse.overload_on("bigcross",``bigcross0 ^mem``)

val mem_bigcross = Q.store_thm("mem_bigcross",
  `is_set_theory ^mem ⇒
    ∀ls x. (mem x (bigcross ls) ⇔ ∃xs. x = tuple xs ∧ LIST_REL mem xs ls)`,
  strip_tac >> Induct >>
  simp[bigcross_def,tuple_def,mem_one] >>
  simp[mem_product,PULL_EXISTS,tuple_def])

val _ = print_theory_to_file "-" "setSpec";

val _ = export_theory()
