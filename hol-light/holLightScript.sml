open HolKernel Opentheory
val _ = new_theory"holLight"
val BIT0_def = bossLib.Define`
  (BIT0 0 = 0) ∧
  (BIT0 (SUC n) = SUC (SUC (BIT0 n)))`
val member_def = bossLib.Define`
  member x y = MEM x y`
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="holLight",Name="BIT0"},name=(["Number","Natural"],"bit0")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="holLight",Name="member"},name=(["Data","List"],"member")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="EXISTS"},name=(["Data","List"],"any")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="FILTER"},name=(["Data","List"],"filter")}
val _ = OpenTheoryMap.OpenTheory_const_name {const={Thy="list",Name="MAP"},name=(["Data","List"],"map")}
fun const_name n = const_name_in_map n handle NotFound => {Thy="holLight",Name=snd n}
fun tyop_name n = tyop_name_in_map n handle NotFound => {Thy="holLight",Tyop=snd n}
fun fix_name "|-" = "proves"
  | fix_name "===" = "equiv"
  | fix_name s = if String.sub(s,0) = #"_" then ("holLight"^s) else s
val reader =
{ define_tyop  = define_tyop_in_thy
, define_const = define_const_in_thy fix_name
, axiom        = axiom_in_db
, const_name   = const_name
, tyop_name    = tyop_name
}
val thms = Net.listItems (read_article "model-syntax.art" reader)
val _ = map2 (curry save_thm) ["proves_cases","proves_ind","proves_rules"] thms
val _ = export_theory()
