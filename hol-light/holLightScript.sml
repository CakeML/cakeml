open HolKernel Opentheory
val _ = new_theory"holLight"
fun const_name (["Number","Natural"],"bit0") = {Thy="arithmetic",Name="BIT0"}
  | const_name n = const_name_in_map n
val reader =
{ define_tyop  = define_tyop_in_thy
, define_const = define_const_in_thy (fn s => String.extract(s,9,NONE))
, axiom        = axiom_in_db
, const_name   = const_name
, tyop_name    = tyop_name_in_map
}
val thms = read_article "model-syntax.art" reader
val _ = export_theory()
