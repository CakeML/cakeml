(*
  Post-translation of merge_run_sort
*)
Theory merge_run_sort_translation
Ancestors
  mergesort std_prelude mllist ml_translator merge_run_sort_monadic
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

val tvar = ``: 'el``;

val state_type = ``: ( ^tvar ) merge_run_state``;

val subs = ``MR_Subscript``

val exn_type = type_of subs;

val config = local_state_config |>
              with_state state_type |>
              with_exception exn_type |>
              with_resizeable_arrays [
                ("main_array", listSyntax.mk_list ([], tvar), subs, subs),
                ("copy_array", listSyntax.mk_list ([], tvar), subs, subs),
                ("sz_array", ``[] : num list``, subs, subs)
              ];

val _ = start_translation config;

(* Some clunking around to translate the accessors as auto-defined in
   heap_list_sort_monadicTheory using their counterparts auto-defined above. *)
val heap_list_acc_def_names = ["main_array_sub_def", "update_main_array_def",
  "alloc_main_array_def", "sz_array_sub_def", "update_sz_array_def",
  "alloc_sz_array_def", "copy_array_sub_def", "update_copy_array_def",
  "alloc_copy_array_def"]

val configured_acc_defs = map (fetch "-") heap_list_acc_def_names;
val previous_acc_defs = map (fetch "merge_run_sort_monadic") heap_list_acc_def_names;
val redefs = previous_acc_defs
  |> map (REWRITE_RULE (map GSYM configured_acc_defs))
val do_redef = REWRITE_RULE redefs

(* Translate all monadic defs. *)

val merge_runs_v_thm = merge_runs_def
  |> do_redef |> m_translate;

val copy_to_copy_v_thm = copy_to_copy_def
  |> do_redef |> m_translate;

(* Include a check in the translation of the subtraction in do_merge_array.
   There is an invariant (arri = SUM (DROP ri) st.sz_array) that proves the
   subtraction is safe, but that invariant would have to be maintained
   through all the other functions here. *)
val _ = (ml_translatorLib.use_sub_check true);
val do_merge_array_v_thm = do_merge_array_def
  |> do_redef |> m_translate;
val _ = (ml_translatorLib.use_sub_check false);

val merge_smaller_array_v_thm = merge_smaller_array_def
  |> do_redef |> m_translate;

val merge_similar_array_v_thm = merge_similar_array_def
  |> do_redef |> m_translate;

val merge_every_array_v_thm = merge_every_array_def
  |> do_redef |> m_translate;

val merge_in_run_array_v_thm = merge_in_run_array_def
  |> do_redef |> m_translate;

val find_known_run_array_v_thm = find_known_run_array_def
  |> do_redef |> m_translate;

val reverse_run_v_thm = reverse_run_def
  |> do_redef |> m_translate;

val find_run_array_v_thm = find_run_array_def
  |> do_redef |> m_translate;

val first_pass_array_v_thm = first_pass_array_def
  |> do_redef |> m_translate;

val merge_run_sort_monadic_v_thm = merge_run_sort_monadic_def
  |> do_redef |> m_translate;

val above_log2_v_thm = above_log2_def
  |> translate;

val copy_into_array_v_thm = copy_into_array_def
  |> do_redef |> m_translate;

val copy_from_array_v_thm = copy_from_array_def
  |> do_redef |> m_translate;

val merge_run_sort_worker_v_thm = merge_run_sort_worker_def
  |> do_redef |> m_translate;

(* Set up the "run" mechanism. *)
val run_init_merge_run_state_def =
  define_run state_type [] "init_merge_run_state";

Definition sort_via_merge_run_sort_worker_def:
  sort_via_merge_run_sort_worker R x xs =
  run_init_merge_run_state (merge_run_sort_worker R x xs)
    (init_merge_run_state [] [] [])
End

val run_v_thm = sort_via_merge_run_sort_worker_def
  |> m_translate_run;

Definition sort_via_array_merge_def:
  sort_via_array_merge R xs = (case xs of [] => []
    | x :: _ => (case sort_via_merge_run_sort_worker R x xs of
        M_success ys => ys
      | _ => [])
  )
End

val sort_via_array_merge_v_thm = sort_via_array_merge_def |> translate;

(* Done monadic translation. *)

val _ = ml_translatorLib.use_sub_check false;

Theorem merge_run_sort_worker_eq_FST[local]:
  xs <> [] ==>
  FST (merge_run_sort_worker R x xs st) =
    (M_success (merge_run_sort R xs))
Proof
  mp_tac merge_run_sort_worker_eq
  \\ rw [] \\ fs []
QED

Theorem merge_run_sort_eq_sort_via_array_merge:
  merge_run_sort R xs = sort_via_array_merge R xs
Proof
  simp [sort_via_array_merge_def]
  \\ Cases_on `xs` \\ simp [EVAL ``(merge_run_sort R [])``]
  \\ simp [sort_via_merge_run_sort_worker_def,
        run_init_merge_run_state_def, ml_monadBaseTheory.run_def]
  \\ simp [merge_run_sort_worker_eq_FST]
QED

val _ = ml_prog_update open_local_in_block;

val merge_run_sort_v_thm = merge_run_sort_eq_sort_via_array_merge |> translate;

val _ = ml_prog_update close_local_block;

