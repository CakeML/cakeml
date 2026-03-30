(*
  Post-translation of heap_list_sort
*)
Theory heap_list_sort_translation
Ancestors
  mergesort std_prelude mllist ml_translator heap_list_sort_monadic
Libs
  preamble ml_translatorLib ml_progLib
  ml_monad_translator_interfaceLib

val _ = ml_prog_update (open_module "Sort_Post_Translation");

val () = generate_sigs := true;

(* Little bits of List translation that might be needed. *)

val r = translate NULL;

val _ = ml_prog_update open_local_block;
val res = translate LENGTH_AUX_def;
val _ = ml_prog_update open_local_in_block;

val result = next_ml_names := ["length"]
val res = translate LENGTH_AUX_THM;

val _ = ml_prog_update close_local_block;

val _ = ml_prog_update open_local_block;

(* Config to use monadic translator temporarily. *)
val _ = ml_translatorLib.use_sub_check true;

val tvar = ``: 'el``;

val state_type = ``: ( ^tvar ) heap_list_state``;

val subs = ``Heap_List_Subscript``

val exn_type = type_of subs;

val config = local_state_config |>
              with_state state_type |>
              with_exception exn_type |>
              with_resizeable_arrays [
                ("heap_array", listSyntax.mk_list ([], tvar), subs, subs),
                ("sz_array", ``[] : num list``, subs, subs)
              ];

val _ = start_translation config;

(* Some clunking around to translate the accessors as auto-defined in
   heap_list_sort_monadicTheory using their counterparts auto-defined above. *)
val heap_list_acc_def_names = ["heap_array_sub_def", "update_heap_array_def",
  "alloc_heap_array_def", "sz_array_sub_def", "update_sz_array_def",
  "alloc_sz_array_def"]

val configured_acc_defs = map (fetch "-") heap_list_acc_def_names;
val previous_acc_defs = map (fetch "heap_list_sort_monadic") heap_list_acc_def_names;
val redefs = previous_acc_defs
  |> map (REWRITE_RULE (map GSYM configured_acc_defs))
val do_redef = REWRITE_RULE redefs

Definition comp_exp_def:
  comp_exp m x 0 = x /\
  comp_exp (m : num) x (SUC i) = comp_exp m (x * m) i
End

Theorem comp_exp_eq_ind[local]:
  !i x. comp_exp m x i = x * (m EXP i)
Proof
  Induct \\ simp [comp_exp_def, EXP]
QED

Theorem use_comp_exp:
  (m EXP i) = comp_exp m 1 i
Proof
  simp [comp_exp_eq_ind]
QED

val comp_exp_v_thm = comp_exp_def |> translate;

val sfx_heap_left_v_thm = sfx_heap_left_def
  |> REWRITE_RULE [use_comp_exp] |> translate;

val insert_into_sfx_heap_v_thm = insert_into_sfx_heap_def
  |> do_redef |> m_translate;

val insert_into_sfx_heap_list_v_thm = insert_into_sfx_heap_list_def
  |> REWRITE_RULE [use_comp_exp]
  |> do_redef |> m_translate;

Theorem bind_assoc[local]:
  (st_ex_bind (st_ex_bind f g) h) =
  (st_ex_bind f (\x. st_ex_bind (g x) h))
Proof
  rw [ml_monadBaseTheory.st_ex_bind_def, FUN_EQ_THM]
  \\ rpt (TOP_CASE_TAC \\ fs [])
QED

val add_to_sfx_heaps_v_thm = add_to_sfx_heaps_def
  |> SIMP_RULE bool_ss [add_to_sfx_heaps_step1_def, bind_assoc]
  |> do_redef |> m_translate;

val add_all_to_sfx_heaps_v_thm = add_all_to_sfx_heaps_def
  |> do_redef |> m_translate;

val reinsert_tree_v_thm = reinsert_tree_def
  |> REWRITE_RULE [use_comp_exp]
  |> do_redef |> m_translate;

val sfx_trees_to_list_v_thm = sfx_trees_to_list_def
  |> do_redef |> m_translate;

val above_log2_v_thm = above_log2_def |> translate;

val sort_via_sfx_trees_worker_v_thm = sort_via_sfx_trees_worker_def
  |> do_redef |> m_translate;

val run_init_heap_list_state_def = define_run state_type [] "init_heap_list_state";

Definition sort_via_sfx_trees_run_worker_def:
  sort_via_sfx_trees_run_worker R x xs =
  run_init_heap_list_state (sort_via_sfx_trees_worker R x xs)
    (init_heap_list_state [] [])
End

val run_init_heap_list_state_v_thm = sort_via_sfx_trees_run_worker_def
  |> m_translate_run;

Definition sort_via_sfx_trees_def:
  sort_via_sfx_trees R xs = (case xs of [] => []
    | x :: _ => (case sort_via_sfx_trees_run_worker R x xs of
        M_success ys => ys
      | _ => [])
  )
End

val sort_via_sfx_trees_v_thm = sort_via_sfx_trees_def |> translate;

(* Done monadic translation. *)

val _ = ml_translatorLib.use_sub_check false;

Theorem heap_list_sort_eq_sort_via_sfx_trees:
  heap_list_sort R xs = sort_via_sfx_trees R xs
Proof
  simp [sort_via_sfx_trees_def]
  \\ Cases_on `xs` \\ simp [EVAL ``(heap_list_sort R [])``]
  \\ simp [sort_via_sfx_trees_run_worker_def,
        run_init_heap_list_state_def, ml_monadBaseTheory.run_def]
  \\ simp [heap_list_sort_monadicTheory.sort_via_sfx_trees_worker_eq]
QED

val _ = ml_prog_update open_local_in_block;

val heap_list_sort_v_thm = heap_list_sort_eq_sort_via_sfx_trees |> translate;

val _ = next_ml_names := ["heap_list_sort"];

val _ =  ml_prog_update close_local_blocks;



