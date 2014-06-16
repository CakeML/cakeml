open HolKernel Parse boolLib bossLib;

val _ = new_theory "compile_primitives";

open astTheory libTheory semanticPrimitivesTheory bigStepTheory;
open terminationTheory determTheory evalPropsTheory bigClockTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory terminationTheory;
open lcsymtacs finite_mapTheory miscTheory;
open modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory compilerTheory intLangTheory toIntLangTheory toBytecodeTheory;
open terminationTheory compilerTerminationTheory

val c = let
val compset = wordsLib.words_compset()
val add_datatype = computeLib.add_datatype_info compset o valOf o TypeBase.fetch
(* good libraries which provide compsets :) *)
val () = intReduce.add_int_compset compset
(* included in words_compset
val () = listLib.list_rws compset
val () = numposrepLib.add_numposrep_compset compset
val () = ASCIInumbersLib.add_ASCIInumbers_compset compset
*)
val () = stringLib.add_string_compset compset
val () = sumSimps.SUM_rws compset
val () = optionLib.OPTION_rws compset
val () = pred_setLib.add_pred_set_compset compset
val () = combinLib.add_combin_compset compset
val () = pairLib.add_pair_compset compset
val () = finite_mapLib.add_finite_map_compset compset
(* misc :( *)
val () = computeLib.add_thms
  [miscTheory.find_index_def
  ,compilerLibTheory.lunion_def
  ,compilerLibTheory.lshift_def
  ,compilerLibTheory.el_check_def
  ,compilerLibTheory.the_def
  ,compilerLibTheory.num_fold_def
  ] compset
(* semantics *)
val () = computeLib.add_thms
  [gramTheory.nt_distinct_ths
  ,libTheory.merge_def
  ,libTheory.bind_def
  ,terminationTheory.is_value_def
  ,pat_bindings_def
  ,typeSystemTheory.merge_tenvC_def
  ,bytecodeTheory.bool_to_tag_def
  ,bytecodeTheory.unit_tag_def
  ,bytecodeTheory.closure_tag_def
  ,bytecodeTheory.string_tag_def
  ,bytecodeTheory.block_tag_def
  ,conLangTheory.tuple_tag_def
  ,conLangTheory.div_tag_def
  ,conLangTheory.bind_tag_def
  ,conLangTheory.eq_tag_def
  ,conLangTheory.cons_tag_def
  ,conLangTheory.nil_tag_def
  ,conLangTheory.some_tag_def
  ,conLangTheory.none_tag_def
  ] compset
val () = add_datatype ``:MMLnonT``
val () = add_datatype ``:top``
val () = add_datatype ``:dec``
val () = add_datatype ``:pat``
val () = add_datatype ``:exp``
val () = add_datatype ``:tid_or_exn``
val () = add_datatype ``:op``
val () = add_datatype ``:lop``
val () = add_datatype ``:lit``
val () = add_datatype ``:opb``
val () = add_datatype ``:opn``
val () = add_datatype ``:'a id``
val () = add_datatype ``:eq_result``
(* modLang compiler *)
val () = computeLib.add_thms
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
val () = computeLib.add_thms
  [prog_to_i2_def
  ,prompt_to_i2_def
  ,decs_to_i2_def
  ,exp_to_i2_def
  ,pat_to_i2_def
  ,init_tagenv_state_def
  ,get_tagenv_def
  ,lookup_tag_env_def
  ,lookup_tag_flat_def
  ,num_defs_def
  ,mod_tagenv_def
  ,insert_tag_env_def
  ,alloc_tag_def
  ] compset
val () = add_datatype ``:prompt_i2``
val () = add_datatype ``:dec_i2``
val () = add_datatype ``:pat_i2``
val () = add_datatype ``:exp_i2``
(* decLang compiler *)
val () = computeLib.add_thms
  [prog_to_i3_def
  ,prompt_to_i3_def
  ,init_globals_def
  ,init_global_funs_def
  ,decs_to_i3_def
  ] compset
(* exhLang compiler *)
val () = computeLib.add_thms
  [exp_to_exh_def
  ,pat_to_exh_def
  ,add_default_def
  ,exhaustive_match_def
  ,is_var_def
  ,get_tags_def
  ] compset
(* patLang compiler *)
val () = computeLib.add_thms
  [exp_to_pat_def
  ,row_to_pat_def
  ,pat_to_pat_def
  ,sLet_pat_def
  ,sIf_pat_def
  ,ground_pat_def
  ,pure_pat_def
  ,(CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)) Let_Els_pat_def
  ] compset
val () = add_datatype ``:exp_pat``
(* intLang compiler *)
val () = computeLib.add_thms
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
    computeLib.add_thms
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
      ,(CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)) (LIST_CONJ l2)
      ,LIST_CONJ l3
      ] compset
  end
val () = computeLib.add_thms
  [compile_Cexp_def,
   repl_funTheory.compile_primitives_def,
   compilerTheory.compile_print_top_def,
   compilerTheory.compile_print_err_def,
   compilerTheory.compile_top_def
  ] compset
val () = add_datatype ``:compiler_result``
val () = add_datatype ``:call_context``
val () = add_datatype ``:compiler_state``
val () = computeLib.add_thms
  [initialProgramTheory.initial_program_def
  ,init_compiler_state_def
  ] compset
in compset end

val res = computeLib.CBV_CONV c ``compile_primitives``
val compile_primitives_eq = save_thm("compile_primitives_eq",res);

val _ = export_theory();

