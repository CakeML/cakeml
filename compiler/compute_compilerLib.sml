structure compute_compilerLib = struct local
open HolKernel boolLib bossLib computeLib
open libTheory modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory toIntLangTheory toBytecodeTheory compilerTheory
open compilerTerminationTheory

val SUC_TO_NUMERAL_RULE = CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)

(* The middle of the compiler, but not the top-level interfaces.
   There are two options for those, depending on whether you want to
   be able to use the labels database to later prove code_labels_ok
   of the result of evaluation or not. *)
fun add_intermediate_compiler_compset compset = let
  fun add_datatype t = compute_basicLib.add_datatype t compset
  (* compiler lib *)
  val () = add_thms
    [lunion_def
    ,lshift_def
    ,el_check_def
    ,the_def
    ,num_fold_def] compset
  (* tags *)
  val () = add_thms
    [tuple_tag_def
    ,div_tag_def
    ,bind_tag_def
    ,eq_tag_def
    ,cons_tag_def
    ,nil_tag_def
    ,some_tag_def
    ,none_tag_def
    ,subscript_tag_def
    ] compset
  (* modLang compiler *)
  val () = add_thms
    [prog_to_i1_def
    ,top_to_i1_def
    ,decs_to_i1_def
    ,dec_to_i1_def
    ,exp_to_i1_def
    ,alloc_defs_def
    ] compset
  val () = add_datatype ``:prompt_i1``
  val () = add_datatype ``:dec_i1``
  (* conLang compiler *)
  val () = add_thms
    [prog_to_i2_def
    ,prompt_to_i2_def
    ,decs_to_i2_def
    ,exp_to_i2_def
    ,pat_to_i2_def
    ,get_tagenv_def
    ,lookup_tag_env_def
    ,lookup_tag_flat_def
    ,num_defs_def
    ,mod_tagenv_def
    ,insert_tag_env_def
    ,alloc_tag_def
    ,alloc_tags_def
    ,build_exh_env_def
    ] compset
  val () = add_datatype ``:prompt_i2``
  val () = add_datatype ``:dec_i2``
  val () = add_datatype ``:pat_i2``
  val () = add_datatype ``:exp_i2``
  val () = add_datatype ``:op_i2``
  (* decLang compiler *)
  val () = add_thms
    [prog_to_i3_def
    ,prompt_to_i3_def
    ,init_globals_def
    ,init_global_funs_def
    ,decs_to_i3_def
    ] compset
  (* exhLang compiler *)
  val () = add_thms
    [exp_to_exh_def
    ,pat_to_exh_def
    ,add_default_def
    ,exhaustive_match_def
    ,is_unconditional_def
    ,get_tags_def
    ] compset
  (* patLang compiler *)
  val () = add_thms
    [exp_to_pat_def
    ,row_to_pat_def
    ,pat_to_pat_def
    ,sLet_pat_thm
    ,sIf_pat_def
    ,ground_pat_def
    ,pure_pat_def
    ,SUC_TO_NUMERAL_RULE Let_Els_pat_def
    ,pure_op_pat_def
    ,pure_op_def
    ] compset
  val () = add_datatype ``:exp_pat``
  val () = add_datatype ``:op_pat``
  (* intLang compiler *)
  val () = add_thms
    [exp_to_Cexp_def
    ,opn_to_prim2_def
    ,free_labs_def
    ,free_vars_def
    ,no_labs_def
    ,app_to_il_def
    ,binop_to_il_def
    ,unop_to_il_def
    ] compset
  val () = add_datatype ``:Cprim1``
  val () = add_datatype ``:Cprim2``
  (* bytecode compiler *)
  val () =
    let
      val nameof = fst o dest_const o fst o strip_comb o lhs o snd o strip_forall o concl
      val (l1,l2) = List.partition(equal"compile" o nameof)(CONJUNCTS compile_def)
      val (l2,l3) = List.partition(equal"compile_bindings" o nameof) l2
    in
      add_thms
        [label_closures_def
        ,bind_fv_def
        ,shift_def
        ,mkshift_def
        ,compile_code_env_def
        ,cce_aux_def
        ,get_label_def
        ,emit_def
        ,pushret_def
        ,push_lab_def
        ,cons_closure_def
        ,emit_ceenv_def
        ,emit_ceref_def
        ,update_refptr_def
        ,compile_closures_def
        ,compile_envref_def
        ,compile_varref_def
        ,stackshift_def
        ,stackshiftaux_def
        ,prim1_to_bc_def
        ,prim2_to_bc_def
        ,LIST_CONJ l1
        ,SUC_TO_NUMERAL_RULE (LIST_CONJ l2)
        ,LIST_CONJ l3
        ] compset
    end
  val () = add_thms
    [compile_Cexp_def
    ,compile_print_top_def
    ,compile_print_err_def
    ,prog_to_i3_initial_def
    ,prompt_to_i3_initial_def
    ] compset
  val () = add_datatype ``:compiler_result``
  val () = add_datatype ``:call_context``
  val () = add_datatype ``:compiler_state``
in
  ()
end

in

  fun add_compiler_compset track_labels compset = (
    add_intermediate_compiler_compset compset;
    if track_labels then
      () (* TODO *)
    else
    let
      val () = add_thms
        [compile_top_def
        ,compile_prog_def
        ,compile_initial_prog_def
        ,compile_special_def
        ] compset
    in () end)

  fun the_compiler_compset track_labels =
    let
      val c = compute_basicLib.the_basic_compset
      val () = compute_semanticsLib.add_ast_compset c
      val () = add_compiler_compset track_labels c
    in
      c
    end

end
end
