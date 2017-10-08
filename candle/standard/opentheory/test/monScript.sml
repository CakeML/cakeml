open preamble
     ml_monad_translatorLib
     ml_monad_translatorTheory
     ml_monadBaseLib
     ml_progLib

val _ = new_theory "test";

val _ = (use_full_type_names := false);
val _ = hide "state"

(* --- Monad syntax --- *)
val _ = ParseExtras.temp_loose_equality();
val _ = monadsyntax.temp_add_monadsyntax();
val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* --- Set up first translation --- *)

(*val _ = ml_prog_update (open_module "Test");*)

val _ = Datatype `
  state = <| foo : num |>`;

val refs_access_funs = define_monad_access_funs ``:state``;
val [(the_foo_ref_name, get_the_foo_ref_def, set_the_foo_ref_def)] = refs_access_funs;

val init_foo_ref_def = Define `init_foo = (0 : num)`;
val refs_init_list =
    [( the_foo_ref_name
     , init_foo_ref_def
     , get_the_foo_ref_def
     , set_the_foo_ref_def
     )];

val arrays_init_list = []
val store_hprop_name = "STATE_STORE";
val state_type = ``:state``;
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

(* --- Functions --- *)

val foo_fun_def = Define `
  foo_fun u =
    do
      old <- get_foo;
      if old < 10 then
        do
          set_foo (old + 1);
          return ()
        od
      else
        return ()
    od`

val r = m_translate foo_fun_def

(*val _ = ml_prog_update (close_module NONE)*)

val _ = export_theory ();

