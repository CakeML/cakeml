(*
  Simple automation for instantiating asm_conf in backend definitions.
*)
structure backend_asmLib :> backend_asmLib =
struct

open HolKernel boolLib bossLib;
open backendTheory backend_asmTheory;

(*
val asm_config_def = x64_targetTheory.x64_config_def
*)

fun define_target_specific_backend asm_config_def = let
  val def = asm_config_def
  val asm_conf = def |> concl |> dest_eq |> fst;
  val tokens = String.tokens (fn c => c = #"_")
  val name = asm_conf |> dest_const |> fst |> tokens |> hd;
  val lemma = TypeBase.accessors_of (type_of asm_conf)
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
    |> map (fn tm => mk_icomb(tm,asm_conf))
    |> map (fn tm => SIMP_CONV (srw_ss()) [def] tm)
    |> LIST_CONJ
  val mem = ref ([]:thm list)
  fun asm_spec th0 = let
    val th1 = th0 |> DefnBase.one_line_ify NONE |> SPEC_ALL
    val (c,args) = th1 |> concl |> dest_eq |> fst |> strip_comb
    val tm = first (fn tm => can (match_term tm) asm_conf) args
    val (i,s) = match_term tm asm_conf
    val th2 = INST i (INST_TYPE s th1)
    val tm1 = th2 |> concl |> dest_eq |> fst
    val (c,args1) = strip_comb tm1
    fun takeWhile p [] = []
      | takeWhile p (x::xs) = if p x then x :: takeWhile p xs else []
    val args2' = takeWhile is_var (rev args1)
    val args2 = filter is_var args1
    val tm2 = list_mk_abs(args2,tm1)
    val prefix = c |> dest_const |> fst
    val full_name = prefix ^ "_" ^ name
    val full_name_def = full_name ^ "_def"
    val v = mk_var(full_name,type_of tm2)
    val d = new_definition(full_name_def,mk_eq(v,tm2))
              |> SIMP_RULE std_ss [FUN_EQ_THM] |> GSYM
              |> REWRITE_RULE [GSYM FUN_EQ_THM] |> SPEC_ALL
    val _ = (mem := (d::(!mem)))
    val th3 = th2 |> REWRITE_RULE (!mem)
                  |> SIMP_RULE (srw_ss()) [lemma,combinTheory.o_DEF]
                  |> REWRITE_RULE (!mem)
                  |> SPEC_ALL
    val _ = List.null (find_terms (aconv asm_conf) (concl th3))
                orelse (print_thm th3;
                        failwith "resulting term contains asm_conf reference")
    val _ = save_thm(full_name_def ^ "[userdef,allow_rebind]",th3)
    in d end
  (* to_livesets *)
  val th = data_to_wordTheory.compile_0_def |> asm_spec
  val th = to_word_0_def |> asm_spec
  val th = word_instTheory.inst_select_exp_def |> asm_spec
  val th = word_instTheory.inst_select_def |> asm_spec
  val th = word_allocTheory.get_forced_def |> asm_spec
  val th = to_livesets_0_def |> asm_spec
  val th = to_livesets_def |> asm_spec
  val th = ISPEC asm_conf to_livesets_thm |> REWRITE_RULE [th]
  val res = save_thm ("to_livesets_" ^ name ^ "_thm", th)
  (* lab_to_target *)
  val th = enc_line_def |> asm_spec
  val th = enc_sec_def |> asm_spec
  val th = enc_sec_list_def |> asm_spec
  val th = enc_lines_again_def |> asm_spec
  val th = enc_secs_again_def |> asm_spec
  val th = asmTheory.reg_ok_def |> asm_spec
  val th = asmTheory.fp_reg_ok_def |> asm_spec
  val th = asmTheory.fp_ok_def |> asm_spec
  val th = asmTheory.reg_imm_ok_def |> asm_spec
  val th = asmTheory.arith_ok_def |> asm_spec
  val th = asmTheory.inst_ok_def |> asm_spec
  val th = asmTheory.cmp_ok_def |> asm_spec
  val th = asmTheory.asm_ok_def |> asm_spec
  val th = lab_to_targetTheory.line_ok_light_def |> asm_spec
  val th = lab_to_targetTheory.sec_ok_light_def |> asm_spec
  val th = remove_labels_loop_def |> asm_spec
  val th = remove_labels_def |> asm_spec
  val th = compile_lab_def |> asm_spec
  val th = lab_to_target_def |> asm_spec
  (* rest *)
  val th = from_lab_def |> asm_spec
  val th = from_stack_def |> asm_spec
  val th = word_to_stackTheory.comp_def |> asm_spec
  val th = word_to_stackTheory.compile_prog_def |> asm_spec
  val th = word_to_stackTheory.compile_word_to_stack_def |> asm_spec
  val th = from_word_def |> REWRITE_RULE [word_to_stackTheory.compile_def] |> asm_spec
  val th = word_alloc_inlogic_def |> asm_spec
  val th = each_inlogic_def |> asm_spec
  val th = word_to_word_inlogic_def |> asm_spec
  val th = from_word_0_def |> asm_spec
  val th = compile_cake_def |> asm_spec
  val th = ISPEC asm_conf compile_cake_thm |> REWRITE_RULE [th]
  val res = save_thm ("compile_cake_" ^ name ^ "_thm", th)
  (* cake_to_stack *)
  val th = from_word_0_to_stack_0_def
             |> REWRITE_RULE [word_to_stackTheory.compile_def] |> asm_spec
  val th = compile_cake_to_stack_def |> asm_spec
  val th = ISPEC asm_conf compile_cake_to_stack_thm |> REWRITE_RULE [th]
  val res = save_thm ("compile_cake_to_stack_" ^ name ^ "_thm", th)
  (* explorer *)
  val th = backend_passesTheory.word_internal_def |> asm_spec
  val th = to_word_all_def |> asm_spec
  val th = to_stack_all_def |> REWRITE_RULE [word_to_stackTheory.compile_def] |> asm_spec
  val th = to_lab_all_def |> asm_spec
  val th = compile_cake_explore_def |> asm_spec
  in th end

end
