open preamble
     ml_monadBaseLib
     ml_monad_translatorLib

val _ = new_theory "test1_mon";

val _ = hide "state"

(* --- State type --- *)

val _ = Datatype `state_refs = <| foo_ref : num |>`;
val state_type = ``:state_refs``;

(* --- Translation init --- *)

val refs_access_funs = define_monad_access_funs state_type;
val [( the_foo_ref_name
     , get_the_foo_ref_def
     , set_the_foo_ref_def)] = refs_access_funs;

val init_foo_ref_def = Define `init_foo_ref = (0 : num)`;

val refs_init_list =
    [( the_foo_ref_name
     , init_foo_ref_def
     , get_the_foo_ref_def
     , set_the_foo_ref_def
     )];

val arrays_init_list = []
val store_hprop_name = "STATE_STORE";
val exn_ri_def = ml_translatorTheory.UNIT_TYPE_def;
val exn_functions = []
val type_theories = []
val store_pinv_opt = NONE

val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
					      arrays_init_list
					      store_hprop_name
					      state_type
					      exn_ri_def
					      exn_functions
					      type_theories
                                              store_pinv_opt;

(* --- Monadic syntax + functions + translation --- *)

val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val baz_def = Define `
  baz n =
    do
      m <- get_foo_ref;
      return (m < n)
    od`;

val bar_def = Define `
  bar n =
    do
      m <- get_foo_ref;
      set_foo_ref (m + n)
    od`;

val simple_def = Define `
  simple n = return (n > 10n)`;

val r = m_translate baz_def;

val _ = export_theory ();

