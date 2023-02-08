(*
  Translate the pan_to_target part of the 64-bit compiler.
*)

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target64ProgTheory std_preludeTheory;
local open backendTheory in end

val _ = new_theory "from_pancake64Prog"

val _ = translation_extends "to_target64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake64Prog");
val _ = ml_translatorLib.use_string_type true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];
fun preprocess def =
  def |> RW (!extra_preprocessing)
      |> CONV_RULE (DEPTH_CONV BETA_CONV)
      |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
      |> REWRITE_RULE [NOT_NIL_AND_LEMMA];

val matches = ref ([]: term list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``,beta|->``:64``] else []

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

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``, “foo:'a pan_to_crep$context”]

open panLangTheory;

val _ = register_type “:64 panLang$exp”;

val _ = register_type “:64 panLang$prog”;

val _ = translate $ spec64 exp_ids_def;

open crepLangTheory;

val _ = register_type “:64 crepLang$exp”;

val _ = register_type “:64 crepLang$prog”;

val _ = translate $ spec64 var_cexp_def;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_decs_def;

val _ = translate $ spec64 nested_seq_def;

val lem = Q.prove(‘dimindex(:64) = 64’, EVAL_TAC);

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 stores_def;

val _ = translate $ spec64 store_globals_def;

val _ = translate $ spec64 load_globals_def;

val _ = translate $ spec64 assign_ret_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 load_shape_def;

open pan_simpTheory;

val _ = translate $ spec64 SmartSeq_def;

val _ = translate $ spec64 seq_assoc_def;

val _ = translate $ spec64 seq_call_ret_def;

val _ = translate $ conv64 ret_to_tail_def;

val _ = translate $ conv64 compile_def;

val _ = translate $ INST_TYPE[gamma|->“:64”] compile_prog_def;

open loopLangTheory;

val _ = register_type “:64 loopLang$exp”;

val _ = register_type “:64 loopLang$prog”;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_seq_def;

open loop_removeTheory;

val _ = translate $ INST_TYPE[alpha|->“:64”, beta|->“:64 loopLang$prog”, gamma|->“:one$one”] store_cont_def;

val _ = translate $ spec64 comp_no_loop_def;

val _ = translate $ spec64 comp_with_loop_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_prog_def;

open loop_to_wordTheory;

val _ = translate $ spec64 comp_exp_def;

val _ = translate $ spec64 find_reg_imm_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ spec64 compile_prog_def;

val _ = translate $ spec64 compile_def;

open pan_to_crepTheory;

val _ = translate $ spec64 ret_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:num”] ret_var_def;

val _ = translate $ INST_TYPE[alpha|->“:64 crepLang$exp”] cexp_heads_def;

val _ = translate $ spec64 comp_field_def;

val _ = translate $ spec64 exp_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:64”,
                              beta|->“:64”] compile_exp_def

val res = translate_no_ind $ spec64 compile_def;

val ind_lemma = Q.prove(
  `^(hd (hyp res))`,
  PURE_REWRITE_TAC [fetch "-" "pan_to_crep_compile_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ FULL_SIMP_TAC bool_ss[panLangTheory.prog_11, panLangTheory.prog_distinct]
  \\ rveq
  \\ metis_tac [])
|> update_precondition;

val _ = translate $ spec64 mk_ctxt_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ INST_TYPE[alpha|->“:64”,
                              beta|->“:mlstring”,
                              gamma|->“:(mlstring # shape) list”,
                              delta|->“:64”] get_eids_def;

val _ = translate $ spec64 compile_prog_def;

open loop_callTheory;

val _ = translate $ spec64 comp_def;

val loop_call_comp_side = Q.prove(
  ‘∀spt prog. (loop_call_comp_side spt prog) ⇔ T’,
  ho_match_mp_tac comp_ind
  \\ rw[]
  \\ simp[Once (fetch "-" "loop_call_comp_side_def")]
  \\ TRY (metis_tac []))
  |> update_precondition;

open loop_liveTheory;

val _ = translate $ spec64 vars_of_exp_def;

val res = translate $ spec64 shrink_def;

val ind_lemma = Q.prove(
  `^(hd (hyp res))`,
  PURE_REWRITE_TAC [fetch "-" "loop_live_shrink_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ TRY (last_x_assum match_mp_tac
          \\ rpt strip_tac
          \\ fs [FORALL_PROD] \\ NO_TAC)
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD])
  |> update_precondition;

val _ = translate $ spec64 mark_all_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 optimise_def;

open crep_to_loopTheory;

val _ = translate $ spec64 prog_if_def;

val _ = translate $ spec64 compile_exp_def;

val _ = translate $ spec64 compile_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ spec64 compile_prog_def;

open pan_to_wordTheory;

val _ = translate $ spec64 compile_prog_def;

open word_to_wordTheory;

(* TODO: duplicate *)     
val _ = translate $ spec64 compile_single_def;

val _ = translate $ spec64 full_compile_single_def;

val _ = translate $ spec64 compile_def;

open backendTheory;

(* TODO: duplicated from compiler64ProgScript. *)
val _ = translate $ INST_TYPE[alpha|->“:word8 list”,
                              beta|->“:word64 list”,
                              gamma|->“:64”,
                              delta|->“:64”] attach_bitmaps_def;

val _ = translate $ INST_TYPE[alpha|->“:64 word list”,
                              beta|->“:64”] from_lab_def;

val _ = translate $ SIMP_RULE std_ss [dimword_def,lem,backend_commonTheory.word_shift_def]
                  $ SIMP_RULE std_ss [data_to_wordTheory.max_heap_limit_def]
                  $ INST_TYPE[alpha|->“:64”,
                              beta|->“:64 word list”] from_stack_def;

val _ = translate $ spec64 from_word_def;

open pan_to_targetTheory;

val _ = translate $ spec64 compile_prog_def;

open panPtreeConversionTheory;

val res = translate argsNT_def;

val res = translate destLf_def;    

val res = translate destTOK_def;

val res = translate $ PURE_REWRITE_RULE [GSYM mlstringTheory.implode_def] conv_ident_def;

val res = translate isNT_def;

val res = translate conv_int_def;

Theorem conv_const_thm:
  conv_const t =
  case conv_int t of NONE => (NONE:'a panLang$exp option)
         | SOME x => SOME(Const(i2w x))
Proof
  Cases_on ‘conv_int t’ \\ rw[conv_const_def]
QED

val res = translate $ spec64 conv_const_thm;        
        
val res = translate conv_nat_def;

Theorem conv_nat_side[local]:
  ∀x. panptreeconversion_conv_nat_side x
Proof
  rw [fetch "-" "panptreeconversion_conv_nat_side_def"]
  >> gs[integerTheory.INT_GE_CALCULATE]
QED

val _ = update_precondition conv_nat_side;

Theorem option_map_thm[local]:
  OPTION_MAP f x = case x of NONE => NONE | SOME y => SOME(f y) 
Proof
  Cases_on ‘x’ \\ rw[]
QED

val res = translate $ PURE_REWRITE_RULE [option_map_thm] $ spec64 conv_var_def;

val res = translate $ conv_shift_def;

Overload ptree_size[local] = ``parsetree_size (K 0) (K 0) (K 0)``;
Overload ptree1_size[local] = ``parsetree1_size (K 0) (K 0) (K 0)``;

Definition conv_ShapeList_def:
  (
        conv_Shape_alt tree =
        case argsNT tree ShapeNT of
          NONE => NONE
        | SOME [] => NONE
        | SOME [t] => if tokcheck t StarT then SOME One else conv_ShapeComb_alt t
        | SOME (t::v8::v9) => NONE) ∧
  (
     conv_ShapeComb_alt tree =
     case argsNT tree ShapeCombNT of
       NONE => NONE
     | SOME ts =>
         case conv_ShapeList ts of NONE => NONE | SOME y => SOME (Comb y))
  ∧
  conv_ShapeList l =
  (case l of
     [] => SOME []
   | x::xs =>
       (case conv_Shape_alt x of
          NONE => NONE
        | SOME y =>
            (case conv_ShapeList xs of
               SOME ys => SOME(y::ys)
             | NONE => NONE)))
Termination
  WF_REL_TAC ‘measure (λx. sum_CASE x ptree_size (λx. sum_CASE x ptree_size (ptree1_size)))’ >> rw[]
  >> Cases_on ‘tree’
  >> gvs[argsNT_def,grammarTheory.parsetree_size_def]
End

val tree = “tree:(token, pancakeNT, α) parsetree”

Triviality conv_Shapelist_thm:
  (∀tree. conv_Shape_alt tree = conv_Shape ^tree)
  ∧
  (∀tree. conv_ShapeComb_alt tree = conv_ShapeComb ^tree)
  ∧
  (∀xs. conv_ShapeList xs = OPT_MMAP (λtree. conv_Shape ^tree) xs)
Proof
  ho_match_mp_tac (fetch "-" "conv_ShapeList_ind") \\ rpt strip_tac \\
  rw[Once conv_ShapeList_def]
  THEN1 (rw[Once conv_Shape_def] \\
         rpt(PURE_FULL_CASE_TAC \\ gvs[]))
  THEN1 (rw[Once conv_Shape_def] \\
         rpt(PURE_FULL_CASE_TAC \\ gvs[])) \\
  Cases_on ‘xs’
  THEN1 (ntac 2 $ rw[Once conv_ShapeList_def]) \\
  rw[] \\ rw[Once conv_ShapeList_def] \\
  rpt(PURE_FULL_CASE_TAC \\ gvs[]) \\
  last_x_assum (simp o single o GSYM)
QED
        
val res = translate_no_ind $ conv_ShapeList_def;

val ind_lemma = Q.prove(
  `^(hd (hyp res))`,
  PURE_REWRITE_TAC [fetch "-" "from_pancake64prog_conv_shape_alt_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ TRY (last_x_assum match_mp_tac
          \\ rpt strip_tac
          \\ fs [FORALL_PROD] \\ NO_TAC))
  |> update_precondition;

val res = translate $ GSYM $ cj 1 conv_Shapelist_thm;

val res = translate $ conv_binop_def;

Theorem OPTION_MAP2_thm:
  OPTION_MAP2 f x y =
  case x of
    NONE => NONE
  | SOME x =>
      (case y of
         NONE => NONE
       | SOME y => SOME(f x y))
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ rw[]
QED

Triviality FOLDR_eta:
  FOLDR (λt. f t) = FOLDR (λt e. f t e)
Proof
  CONV_TAC(DEPTH_CONV ETA_CONV) \\ rw[]
QED

val res = translate conv_cmp_def;

val res = translate kw_def;

val res = translate $ spec64 isSubOp_def;

val res = translate_no_ind $ spec64 panPtreeConversionTheory.conv_Shift_def;

Triviality panptreeconversion_conv_shift_1_ind:
  panptreeconversion_conv_shift_1_ind
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_conv_shift_1_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = panptreeconversion_conv_shift_1_ind |> update_precondition;

fetch "-" "panptreeconversion_conv_shift_1_ind_def"


Theorem conv_shift_1_side[local]:
  ∀x y. panptreeconversion_conv_shift_1_side x y
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_conv_shift_1_side_def"]
  >> rw[]
  >> gs[integerTheory.INT_GE_CALCULATE]
QED


val ind_lemma = Q.prove(
  `^(hd (hyp res))`,
  PURE_REWRITE_TAC [fetch "-" "panptreeconversion_conv_shift_1_ind_def"]
  >> ONCE_REWRITE_TAC [fetch "-" "panptreeconversion_conv_shift_1_side_def"]>>
     rw[PRECONDITION_DEF]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ TRY (last_x_assum match_mp_tac
          \\ rpt strip_tac
          \\ fs [FORALL_PROD] \\ NO_TAC))
  |> update_precondition;



Theorem conv_shift_1_side[local]:
  ∀x. panptreeconversion_conv_shift_1_side x
Proof
  rw [fetch "-" "panptreeconversion_conv_shift_1_side_def"]
  >> gs[integerTheory.INT_GE_CALCULATE]
QED

val _ = update_precondition conv_nat_side;


val res = translate_no_ind $ spec64 $ SIMP_RULE std_ss [option_map_thm,OPTION_MAP2_thm,FOLDR_eta] $ conv_Exp_def;

val res = translate $ INST_TYPE[beta|->``:64``] conv_NonRecStmt_def;

val res = translate $ spec64 conv_Prog_def;
    
val res = translate $ spec64 parse_to_ast_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = export_theory();

