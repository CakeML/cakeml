open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open to_word64ProgTheory;

val _ = new_theory "to_target64Prog"

val _ = translation_extends "to_word64Prog";

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

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);
val inst_tyargs = ref ([]:hol_type list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then map (fn x => x |-> ``:64``) (!inst_tyargs)  else []

  val def = def |> RW (!extra_preprocessing)
                |> INST_TYPE insts
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``]

val _ = inst_tyargs := [alpha]

open word_to_stackTheory

val _ = translate (conv64 write_bitmap_def|> (RW (!extra_preprocessing)))

(* TODO: The paired let trips up the translator's single line def mechanism, unable to find a smaller failing example yet *)
val _ = translate (conv64 (wLive_def |> SIMP_RULE std_ss [LET_THM]))

(* TODO: the name is messed up (pair_) *)
val _ = translate PAIR_MAP

val _ = translate parmoveTheory.fstep_def

val parmove_fstep_side = prove(``
  ∀x. parmove_fstep_side x ⇔ T``,
  EVAL_TAC>>rw[]>>Cases_on`v18`>>fs[]) |> update_precondition

val _ = translate (spec64 word_to_stackTheory.wMove_def)

val _ = translate (spec64 call_dest_def)

val word_to_stack_call_dest_side = prove(``
  ∀a b c. word_to_stack_call_dest_side a b c ⇔ T``,
  EVAL_TAC>>Cases_on`b`>>fs[]) |> update_precondition

val _ = translate (spec64 comp_def)

val _ = translate (compile_word_to_stack_def |> INST_TYPE [beta |-> ``:64``])

val _ = translate (compile_def |> INST_TYPE [alpha|->``:64``,beta|->``:64``])

open stack_allocTheory

val inline_simp = SIMP_RULE std_ss [bytes_in_word_def,stackLangTheory.word_shift_def]
val _ = translate (conv64 clear_top_inst_def)
val _ = translate (memcpy_code_def |> inline_simp |> conv64)
val _ = translate (word_gc_move_code_def |> inline_simp |> conv64)

val _ = translate (word_gc_move_bitmap_code_def |> inline_simp |> conv64)
val _ = translate (word_gc_move_bitmaps_code_def |> inline_simp |> conv64)
val _ = translate (word_gc_move_roots_bitmaps_code_def |> inline_simp |> conv64)

val _ = translate (word_gc_move_list_code_def |> inline_simp |> conv64)
val _ = translate (word_gc_move_loop_code_def |> inline_simp |> conv64)

val _ = translate (spec64 stubs_def)

val _ = translate (spec64 compile_def)

open stack_removeTheory

(* Might be better to inline this *)
val _ = translate (conv64 word_offset_def)
val _ = translate (conv64 store_offset_def |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv64)

val _ = translate (comp_def |> inline_simp |> conv64)

val _ = translate (prog_comp_def |> INST_TYPE [beta|->``:64``])

val _ = translate (store_list_code_def |> inline_simp |> conv64)
val _ = translate (init_memory_def |> inline_simp |> conv64)
val _ = translate (init_code_def |> inline_simp |> conv64 |> SIMP_RULE std_ss [word_mul_def])

val _ = translate (spec64 compile_def)

open stack_namesTheory

val _ = translate (spec64 comp_def)
val _ = translate (prog_comp_def |> INST_TYPE [beta |-> ``:64``])
val _ = translate (compile_def |> INST_TYPE [beta |-> ``:64``])

val _ = translate x64_names_def
val _ = translate arm_names_def

open stack_to_labTheory

val _ = matches := [``foo:'a labLang$prog``,``foo:'a labLang$sec``,``foo:'a labLang$line``,``foo:'a labLang$asm_with_lab``,``foo:'a labLang$line list``,``foo:'a inst``,``foo:'a asm_config``] @ (!matches)

val _ = translate (flatten_def |> spec64)

val _ = translate (compile_def |> spec64)

open lab_filterTheory lab_to_targetTheory asmTheory

val _ = translate (spec64 filter_skip_def)

val _ = translate (get_jump_offset_def |>INST_TYPE [alpha|->``:64``,beta |-> ``:64``])

val _ = translate(conv64 arith_ok_def)

(* TODO: there may be a better rewrite for aligned*)
val _ = translate(jump_offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv64)
val _ = translate(cjump_offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv64)
val _ = translate(loc_offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv64)

val _ = translate (spec64 asmTheory.asm_ok_def)

val _ = translate (spec64 compile_def)

val _ = export_theory();
