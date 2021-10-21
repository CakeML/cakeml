(*
  Translate the compiler's state decoder.
*)
open preamble basisFunctionsLib
     num_list_enc_decTheory num_tree_enc_decTheory backend_enc_decTheory
     mipsProgTheory ml_translatorLib ml_translatorTheory cfLib

val _ = new_theory "decode64Prog"

val _ = translation_extends "mipsProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "decode64Prog");

(* translator setup *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

Theorem NOT_NIL_AND_LEMMA:
   (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* --- *)

val res = translate dec_next_def;
val res = translate chars_to_nums_def;

val res = translate const_dec_def;
val res = translate unit_dec_def;
val res = translate num_dec_def;
val res = translate num_list_enc_decTheory.list_dec'_def;
val res = translate list_dec_def;
val res = translate bool_dec_def;
val res = translate int_dec_def;
val _ = next_ml_names := ["word8_dec"];
val res = translate (word_dec_def |> INST_TYPE [alpha|->“:8”]);
val _ = next_ml_names := ["word64_dec"];
val res = translate (word_dec_def |> INST_TYPE [alpha|->“:64”]);
val res = translate char_dec_def;
val res = translate num_list_enc_decTheory.mlstring_dec_def;
val res = translate prod_dec_def;
val res = translate option_dec_def;
val res = translate sum_dec_def;
val res = translate spt_dec'_def;
val res = translate spt_dec''_def;
val res = translate spt_dec_def;
val res = translate namespace_dec'_def;
val res = translate namespace_dec_def;

(* --- *)

val res = translate num_tree_dec'_def;
val res = translate num_tree_dec_def;
val res = translate nth_def;
val res = translate int_dec'_def;
val res = translate bool_dec'_def;
val res = translate chr_dec'_def;
val res = translate list_dec'_def;
val res = translate pair_dec'_def;
val res = translate option_dec'_def;

(* --- *)

val _ = ml_translatorLib.use_string_type false;
val res = translate (tra_dec'_def |> DefnBase.one_line_ify NONE);
val res = translate safe_chr_list_def;
val res = translate list_chr_dec'_def;
val _ = ml_translatorLib.use_string_type true;
val res = translate string_dec_def;
val res = translate next_indices_dec_def;
val res = translate flat_pattern_config_dec_def;
val res = translate namespace_dec'_def;
val res = translate namespace_dec_def;
val res = translate (var_name_dec'_def |> REWRITE_RULE [string_dec'_intro]);
val res = translate var_name_dec_def;
val res = translate environment_dec_def;
val res = translate environment_store_dec_def;
val res = translate source_to_flat_config_dec_def;
val _ = ml_translatorLib.use_string_type false;

val res = translate data_to_word_config_dec_def;
val res = translate word_to_word_config_dec_def;
val res = translate (word_to_stack_config_dec_def |> INST_TYPE [alpha|->“:64”]);
val res = translate stack_to_lab_config_dec_def;

val res = translate (mlstring_dec'_def |> REWRITE_RULE [GSYM mlstringTheory.implode_def]);
val res = translate tap_config_dec'_def;
val res = translate tap_config_dec_def;

val res = translate (closLang_op_dec'_def |> DefnBase.one_line_ify NONE);

Theorem list_dec'_eq_MAP:
  ∀f t. list_dec' f t = MAP f (list_dec' I t)
Proof
  Cases_on ‘t’ \\ fs [list_dec'_def]
QED

val def = bvl_exp_dec'_def |> DefnBase.one_line_ify NONE
          |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]
val res = translate def;

val res = translate bvl_to_bvi_config_dec_def;

Theorem pair_dec'_eq:
  pair_dec' d1 d2 = λt. (d1 (nth 0 (list_dec' I t)), d2 (nth 1 (list_dec' I t)))
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
  \\ Cases \\ fs [pair_dec'_def,list_dec'_def]
QED

val def = closLang_exp_dec'_def |> DefnBase.one_line_ify NONE
          |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]
          |> ONCE_REWRITE_RULE [pair_dec'_eq]
          |> CONV_RULE (DEPTH_CONV BETA_CONV)
val res = translate_no_ind def;

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ rewrite_tac [num_tree_11]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt var_eq_tac
  \\ gen_tac \\ disch_then (assume_tac o SYM)
  \\ Cases_on ‘x6 = 0’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ ‘n ≠ 1 ∧ n ≠ 0’ by decide_tac
  \\ Cases_on ‘x6 = 1’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ ‘n ≠ 2’ by decide_tac
  \\ Cases_on ‘n = 3’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 4’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 5’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 6’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 7’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 8’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 9’ \\ asm_rewrite_tac []
  \\ rpt var_eq_tac \\ gvs [ADD1])
  |> update_precondition;

val def = val_approx_dec'_def |> DefnBase.one_line_ify NONE
          |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]
val res = translate def;

val def = clos_to_bvl_config_dec_def
val res = translate def;

val _ = ml_translatorLib.use_string_type true;
val def = lab_to_target_config_dec_def |> INST_TYPE [alpha|->“:64”]
          |> REWRITE_RULE [GSYM string_dec_thm]
val res = translate def;
val _ = ml_translatorLib.use_string_type false;

val _ = register_type “:64 backend$config”;

val def = config_dec_def |> INST_TYPE [alpha|->“:64”]
val res = translate def;

val res = translate (decode_backend_config_def |> INST_TYPE [alpha|->“:64”]);

Definition char_cons_def:
  char_cons (x:char) l = x::(l:char list)
End

val char_cons_v_thm = translate char_cons_def;

val _ = (append_prog o process_topdecs) `
  fun read_config x fname =
    case TextIO.foldChars char_cons [] (Some fname) of
      None     => None
    | Some res => Some (decode_backend_config x (List.rev res))`

Theorem foldl_char_cons:
  ∀ys xs. foldl char_cons xs ys = REVERSE ys ++ xs
Proof
  Induct \\ fs [mllistTheory.foldl_def,char_cons_def]
QED

Theorem read_config_spec:
  file_content fs fname = SOME content ∧ hasFreeFD fs ∧
  FILENAME fname fnamev ∧ ASM_ASM_CONFIG_TYPE x xv ⇒
  app (p:'ffi ffi_proj) decode64Prog_read_config_v [xv; fnamev]
    (STDIO fs)
    (POSTv retv. STDIO fs * cond (OPTION_TYPE BACKEND_CONFIG_TYPE
                                    (SOME (decode_backend_config x content)) retv))
Proof
  xcf_with_def "decode64Prog.read_config" (fetch "-" "decode64Prog_read_config_v_def")
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ gvs []
  \\ xlet ‘POSTv retv. STDIO fs *
                 & (OPTION_TYPE (LIST_TYPE CHAR)
                      (OPTION_MAP (foldl char_cons []) (file_content fs fname))
                      retv)’
  THEN1
   (assume_tac char_cons_v_thm
    \\ drule TextIOProofTheory.foldChars_SOME \\ fs []
    \\ disch_then (drule_at (Pos last)) \\ fs []
    \\ strip_tac
    \\ xapp \\ xsimpl
    \\ qexists_tac ‘[]’
    \\ qexists_tac ‘fname’
    \\ fs [decProgTheory.OPTION_TYPE_def,LIST_TYPE_def])
  \\ gvs [decProgTheory.OPTION_TYPE_def,LIST_TYPE_def]
  \\ xmatch
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto \\ xsimpl
  \\ xcon \\ xsimpl
  \\ fs [foldl_char_cons]
QED

val _ = (append_prog o process_topdecs) `
  fun read_x64_config fname =
    case read_config x64Prog.x64_config fname of
      Some c => c
    | None   => Runtime.exit 5;
  fun read_arm8_config fname =
    case read_config arm8Prog.arm8_config fname of
      Some c => c
    | None   => Runtime.exit 5;
`;

Theorem read_x64_config_spec:
  file_content fs fname = SOME (encode_backend_config c) ∧
  hasFreeFD fs ∧ FILENAME fname fnamev ∧
  c.lab_conf.asm_conf = x64_config ⇒
  app (p:'ffi ffi_proj) decode64Prog_read_x64_config_v [fnamev]
    (STDIO fs)
    (POSTv retv. STDIO fs * cond (BACKEND_CONFIG_TYPE c retv))
Proof
  xcf_with_def "decode64Prog.read_x64_config"
    (fetch "-" "decode64Prog_read_x64_config_v_def")
  \\ xlet ‘POSTv retv. STDIO fs * cond (OPTION_TYPE BACKEND_CONFIG_TYPE
          (SOME (decode_backend_config x64_config (encode_backend_config c))) retv)’
  THEN1
   (drule read_config_spec \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ xapp \\ fs [x64ProgTheory.x64_config_v_thm])
  \\ gvs [decProgTheory.OPTION_TYPE_def]
  \\ xmatch \\ xvar \\ xsimpl
  \\ metis_tac [encode_backend_config_thm]
QED

Theorem read_arm8_config_spec:
  file_content fs fname = SOME (encode_backend_config c) ∧
  hasFreeFD fs ∧ FILENAME fname fnamev ∧
  c.lab_conf.asm_conf = arm8_config ⇒
  app (p:'ffi ffi_proj) decode64Prog_read_arm8_config_v [fnamev]
    (STDIO fs)
    (POSTv retv. STDIO fs * cond (BACKEND_CONFIG_TYPE c retv))
Proof
  xcf_with_def "decode64Prog.read_arm8_config"
    (fetch "-" "decode64Prog_read_arm8_config_v_def")
  \\ xlet ‘POSTv retv. STDIO fs * cond (OPTION_TYPE BACKEND_CONFIG_TYPE
          (SOME (decode_backend_config arm8_config (encode_backend_config c))) retv)’
  THEN1
   (drule read_config_spec \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ xapp \\ fs [arm8ProgTheory.arm8_config_v_thm])
  \\ gvs [decProgTheory.OPTION_TYPE_def]
  \\ xmatch \\ xvar \\ xsimpl
  \\ metis_tac [encode_backend_config_thm]
QED

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
