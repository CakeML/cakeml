(*
  Translate the pan_to_target part of the 32-bit compiler.
*)
Theory from_pancake32Prog
Ancestors
  ml_translator to_target32Prog std_prelude panLang crepLang
  pan_simp loopLang loop_remove loop_to_word pan_to_crep
  loop_call loop_live crep_arith crep_to_loop pan_to_word
  word_to_word backend pan_to_target panPtreeConversion
  pan_globals
Libs
  preamble ml_translatorLib

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target32ProgTheory std_preludeTheory;

val _ = translation_extends "to_target32Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake32Prog");
val _ = ml_translatorLib.use_string_type true;
val _ = ml_translatorLib.use_sub_check true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Triviality NOT_NIL_AND_LEMMA:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

Theorem option_map_thm[local]:
  OPTION_MAP f x = case x of NONE => NONE | SOME y => SOME(f y)
Proof
  Cases_on ‘x’ \\ rw[]
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP,parserProgTheory.OPTION_BIND_THM,option_map_thm];

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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:32``,beta|->``:32``] else []

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

val spec32 = INST_TYPE[alpha|->``:32``]

val conv32 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val conv32_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``, “foo:'a pan_to_crep$context”]

open panLangTheory;

val _ = register_type “:32 panLang$exp”;

val _ = register_type “:32 panLang$prog”;

val _ = register_type “:32 panLang$decl”;

val _ = translate $ spec32 exp_ids_def;

open crepLangTheory;

val _ = register_type “:32 crepLang$exp”;

val _ = register_type “:32 crepLang$prog”;

val _ = translate $ spec32 var_cexp_def;

val _ = translate $ spec32 nested_decs_def;

val _ = translate $ spec32 nested_seq_def;

Triviality lem:
  dimindex(:32) = 32
Proof
  EVAL_TAC
QED

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec32 stores_def;

val _ = translate $ spec32 store_globals_def;

val _ = translate $ spec32 load_globals_def;

val _ = translate $ spec32 assign_ret_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec32 load_shape_def;

open pan_simpTheory;

val _ = translate $ spec32 SmartSeq_def;

val _ = translate $ spec32 seq_assoc_def;

val _ = translate $ spec32 seq_call_ret_def;

val _ = translate $ conv32 ret_to_tail_def;

val _ = translate $ conv32 compile_def;

val _ = translate $ conv32 compile_prog_def;

open pan_globalsTheory;

val _ = register_type “:32 pan_globals$context”;

val _ = translate $ conv32 compile_exp_def;

val _ = translate $ fresh_name_def;

val _ = translate $ conv32 var_exp_def;

val _ = translate $ conv32 free_var_ids_def;

val _ = translate $ conv32 shape_val_def;

val _ = translate $ conv32 compile_def;

val _ = translate size_of_shape_def;

val _ = translate_no_ind $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ conv32 compile_decs_def;

Triviality pan_globals_compile_decs_ind:
  pan_globals_compile_decs_ind
Proof
  once_rewrite_tac [fetch "-" "pan_globals_compile_decs_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,bytes_in_word_def]
QED

val _ = pan_globals_compile_decs_ind |> update_precondition;

val _ = translate $ spec32 is_function_def;

val _ = translate $ spec32 resort_decls_def;

val _ = translate fperm_name_def;

val _ = translate $ spec32 fperm_def;

val _ = translate $ spec32 fperm_decs_def;

val _ = translate $ spec32 functions_def;

val _ = translate $ spec32 new_main_name_def;

val _ = translate $ spec32 dec_shapes_def;

val _ = translate $ spec32 panLangTheory.nested_seq_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec32 compile_top_def;

open loopLangTheory;

val _ = register_type “:32 loopLang$exp”;

val _ = register_type “:32 loopLang$prog”;

val _ = translate $ spec32 acc_vars_def;

val _ = translate $ spec32 nested_seq_def;

open loop_removeTheory;

val _ = translate $ INST_TYPE[alpha|->“:32”, beta|->“:32 loopLang$prog”, gamma|->“:one$one”] store_cont_def;

val _ = translate $ spec32 comp_no_loop_def;

val _ = translate $ spec32 comp_with_loop_def;

val _ = translate $ spec32 comp_def;

val _ = translate $ spec32 comp_prog_def;

open loop_to_wordTheory;

val _ = translate $ spec32 comp_exp_def;

val _ = translate $ spec32 find_reg_imm_def;

val _ = translate $ spec32 comp_def;

val _ = translate $ spec32 comp_func_def;

val _ = translate $ spec32 compile_prog_def;

val _ = translate $ spec32 compile_def;

open pan_to_crepTheory;

val _ = translate $ spec32 ret_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:num”] ret_var_def;

val _ = translate $ INST_TYPE[alpha|->“:32 crepLang$exp”] cexp_heads_def;

val _ = translate $ spec32 comp_field_def;

val _ = translate $ spec32 exp_hdl_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem]
                  $ INST_TYPE[alpha|->“:32”,
                              beta|->“:32”] compile_exp_def;

val res = translate_no_ind $ spec32 compile_def;

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

val _ = translate $ spec32 mk_ctxt_def;

val _ = translate $ spec32 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ INST_TYPE[alpha|->“:32”,
                              beta|->“:mlstring”,
                              gamma|->“:(mlstring # shape) list”,
                              delta|->“:32”] get_eids_def;

val _ = translate $ spec32 compile_prog_def;

open loop_callTheory;

val _ = translate $ spec32 comp_def;

open loop_liveTheory;

val _ = translate $ spec32 vars_of_exp_def;

val res = translate $ spec32 shrink_def;

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

val _ = translate $ spec32 mark_all_def;

val _ = translate $ spec32 comp_def;

val _ = translate $ spec32 optimise_def;

open crep_arithTheory;

val _ = translate $ spec32 dest_const_def;

val _ = translate $ spec32 dest_2exp_def;

val _ = translate $ spec32 mul_const_def;

val _ = translate $ spec32 simp_exp_def;

val _ = translate $ spec32 simp_prog_def;

open crep_to_loopTheory;

val _ = translate $ spec32 prog_if_def;

val _ = translate $ spec32 compile_crepop_def;

val _ = translate $ spec32 compile_exp_def;

val _ = translate $ spec32 compile_def;

val _ = translate $ spec32 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ spec32 compile_prog_def;

open pan_to_wordTheory;

val _ = translate $ spec32 compile_prog_def;

open word_to_wordTheory;

val _ = translate $ spec32 compile_single_def;

val _ = translate $ spec32 full_compile_single_def;

val _ = translate $ spec32 compile_def;

open backendTheory;

val _ = translate $ INST_TYPE[alpha|->“:word8 list”,
                              beta|->“:word32 list”,
                              gamma|->“:32”,
                              delta|->“:32”] attach_bitmaps_def;

val _ = translate $ INST_TYPE[alpha|->“:32 word list”,
                              beta|->“:32”] from_lab_def;

val _ = translate $ SIMP_RULE std_ss [dimword_def,lem,backend_commonTheory.word_shift_def]
                  $ SIMP_RULE std_ss [data_to_wordTheory.max_heap_limit_def]
                  $ INST_TYPE[alpha|->“:32”,
                              beta|->“:32 word list”] from_stack_def;

val _ = translate $ spec32 from_word_def;

open pan_to_targetTheory;

val _ = translate $ spec32 exports_def;

val _ = translate $ spec32 compile_prog_def;

(* ptree conversion *)

open panPtreeConversionTheory;

val res = translate argsNT_def;

val res = translate destLf_def;

val res = translate destTOK_def;

val res = translate $ PURE_REWRITE_RULE [GSYM mlstringTheory.implode_def] conv_ident_def;

val res = translate $ PURE_REWRITE_RULE [GSYM mlstringTheory.implode_def] conv_ffi_ident_def;

val res = translate isNT_def;

val res = translate conv_int_def;

Theorem conv_const_thm:
  conv_const t =
  case conv_int t of NONE => (NONE:'a panLang$exp option)
         | SOME x => SOME(Const(i2w x))
Proof
  Cases_on ‘conv_int t’ \\ rw[conv_const_def]
QED

val res = translate $ spec32 conv_const_thm;

val res = translate conv_nat_def;

Theorem conv_nat_side[local]:
  ∀x. panptreeconversion_conv_nat_side x
Proof
  rw [fetch "-" "panptreeconversion_conv_nat_side_def"]
  >> gs[integerTheory.INT_GE_CALCULATE]
QED

val _ = update_precondition conv_nat_side;

val res = translate $ PURE_REWRITE_RULE [option_map_thm] $ spec32 conv_var_def;

val res = translate $ conv_shift_def;

Overload ptree_size[local] = ``parsetree_size (K 0) (K 0) (K 0)``;

val res = translate $ conv_default_shape_def;

Definition conv_ShapeList_def:
  (conv_Shape_alt tree =
    case conv_default_shape tree of
    | SOME s => SOME s
    | _ =>
      case conv_int tree of
        NONE =>
          (case argsNT tree ShapeCombNT of
              NONE => NONE
            | SOME ts =>
                (case conv_ShapeList ts of
                  NONE => NONE
                | SOME x => SOME (Comb x)))
      | SOME n =>
          if n < 1 then NONE
          else if n = 1 then SOME One
          else SOME (Comb (REPLICATE (num_of_int n) One))) ∧
  (conv_ShapeList [] = SOME []) ∧
  (conv_ShapeList (x::xs) =
   (case conv_Shape_alt x of
      NONE => NONE
    | SOME y =>
        (case conv_ShapeList xs of
           SOME ys => SOME(y::ys)
         | NONE => NONE)))
Termination
  WF_REL_TAC ‘measure (λx. sum_CASE x ptree_size (list_size ptree_size))’ >> rw[]
  >> gvs[oneline  argsNT_def,AllCaseEqs()]
End

val tree = “tree:(panLexer$token, pancakeNT, α) parsetree”

Triviality conv_Shapelist_thm:
  (∀tree. conv_Shape_alt tree = conv_Shape ^tree)
  ∧
  (∀xs. conv_ShapeList xs = OPT_MMAP (λtree. conv_Shape ^tree) xs)
Proof
  ho_match_mp_tac (fetch "-" "conv_ShapeList_ind") \\ rpt strip_tac \\
  rw[Once conv_ShapeList_def]
  THEN1 (rw[Once conv_Shape_def] \\
         rpt(PURE_FULL_CASE_TAC \\gvs[]) >>
         gs[num_of_int_def,integerTheory.INT_ABS,
            integerTheory.INT_NOT_LT]>>
         rename1 ‘conv_int _ = SOME n’>>
         ‘¬(n < 0)’ by intLib.COOPER_TAC>>gs[])>>
  TOP_CASE_TAC >> gs[parserProgTheory.OPTION_BIND_THM]
QED

val res = translate_no_ind $ preprocess $ conv_ShapeList_def;

Theorem conv_shape_alt_ind:
  from_pancake32prog_conv_shape_alt_ind (:'a)
Proof
  rewrite_tac [fetch "-" "from_pancake32prog_conv_shape_alt_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ TRY (last_x_assum match_mp_tac
          \\ rpt strip_tac
          \\ fs [FORALL_PROD] \\ NO_TAC)
QED

val _ = conv_shape_alt_ind |> update_precondition;

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

val res = translate $ spec32 isSubOp_def;

val res = translate $ preprocess $ spec32 conv_Shift_def;

val res = translate $ conv_panop_def;

Definition conv_Exp_alt_def:
  (conv_mmap_exp l =
   (case l of
      [] => SOME []
    | x::xs =>
        (case conv_Exp_alt x of
           NONE => NONE
         | SOME y =>
             (case conv_mmap_exp xs of
                NONE => NONE
              | SOME ys => SOME (y::ys))))) ∧
  (conv_ArgList_alt tree =
   case argsNT tree ArgListNT of
     NONE => NONE
   | SOME [] => NONE
   | SOME (t::ts) => conv_mmap_exp (t::ts)) ∧
  (conv_Exp_alt tree =
   (case tree of
      Nd nodeNT args =>
        if isNT nodeNT EBaseNT then
          case args of
            [] => NONE
          | [t] =>
              OPTION_CHOICE (OPTION_CHOICE (conv_const t) (conv_var t))
                            (conv_Exp_alt t)
          | t::v4::v5 =>
              FOLDL (λe t. OPTION_MAP2 Field (conv_nat t) e)
                    (OPTION_CHOICE (conv_var t) (conv_Exp_alt t)) (v4::v5)
        else if isNT nodeNT StructNT then
          case args of
            [] => NONE
          | [ts] => do es <- conv_ArgList_alt ts; SOME (Struct es) od
          | ts::v6::v7 => NONE
        else if isNT nodeNT NotNT then
          case args of
            [t] => OPTION_MAP (λe. Cmp Equal (Const 0w) e) (conv_Exp_alt t)
          | _ => NONE
        else if isNT nodeNT ELoadByteNT then
          case args of
            [] => NONE
          | [t] => OPTION_MAP LoadByte (conv_Exp_alt t)
          | t::v6::v7 => NONE
        else if isNT nodeNT ELoad32NT then
          case args of
            [] => NONE
          | [t] => OPTION_MAP Load32 (conv_Exp_alt t)
          | t::v6::v7 => NONE
        else if isNT nodeNT ELoadNT then
          case args of
            [] => NONE
          | [t1] => NONE
          | [t1; t2] =>
              (case conv_Shape t1 of
                 NONE => NONE
               | SOME s =>
                   (case conv_Exp_alt t2 of
                      NONE => NONE
                    | SOME e => SOME (Load s e)))
          | t1::t2::v10::v11 => NONE
        else if isNT nodeNT ECmpNT ∨ isNT nodeNT EEqNT then
          case args of
            [] => NONE
          | [e] => conv_Exp_alt e
          | [e; op] => NONE
          | [e; op; e2] =>
              (case conv_Exp_alt e of
                 NONE => NONE
               | SOME e1' =>
                   (case conv_cmp op of
                      NONE => NONE
                    | SOME (op', b) =>
                        (case conv_Exp_alt e2 of
                           NONE => NONE
                         | SOME e2' => if b then SOME (Cmp op' e2' e1')
                                       else SOME (Cmp op' e1' e2'))))
          | e::op::e2::v14::v15 => NONE
        else if isNT nodeNT ExpNT then (* boolean or *)
          case args of
            [e] => conv_Exp_alt e
          | e1::args' => do es  <- conv_mmap_exp $ e1::args';
                            SOME $ Cmp NotEqual (Const 0w) $ Op Or es
                         od
          | _ => NONE
        else if isNT nodeNT EBoolAndNT then
          case args of
            [e] => conv_Exp_alt e
          | e1::args' => do es  <- conv_mmap_exp $ e1::args';
                            SOME $ Op And $ MAP (λe. Cmp NotEqual (Const 0w) e) es
                         od
          | _ => NONE
        else if isNT nodeNT EShiftNT then
          case args of
            [] => NONE
          | e::es => monad_bind (conv_Exp_alt e) (conv_Shift es)
        else if EXISTS (isNT nodeNT) binaryExps then
          case args of
            [] => NONE
          | e::es =>
              (case conv_Exp_alt e of
                 NONE => NONE
               | SOME a => conv_binaryExps_alt es a)
        else if EXISTS (isNT nodeNT) panExps then
          case args of
            [] => NONE
          | (e::es) =>
              (case conv_Exp_alt e of
                 NONE => NONE
               | SOME a => conv_panops_alt es a)
        else NONE
    | Lf v12 =>
        if tokcheck (Lf v12) (kw BaseK) then SOME BaseAddr
        else if tokcheck (Lf v12) (kw TopK) then SOME TopAddr
        else if tokcheck (Lf v12) (kw BiwK) then SOME BytesInWord
        else if tokcheck (Lf v12) (kw TrueK) then SOME $ Const 1w
                   else if tokcheck (Lf v12) (kw FalseK) then SOME $ Const 0w
        else NONE)) ∧
  (conv_binaryExps_alt trees res =
   (case trees of
      [] => SOME res
    | [x] => NONE
    | t1::t2::ts =>
        (case conv_binop t1 of
           NONE => NONE
         | SOME op =>
             (case conv_Exp_alt t2 of
                NONE => NONE
              | SOME e' =>
                  (case res of
                     Op bop es =>
                       if bop ≠ op ∨ isSubOp res then
                         conv_binaryExps_alt ts (Op op [res; e'])
                       else conv_binaryExps_alt ts (Op bop (es ++ [e']))
                   | e =>
                       conv_binaryExps_alt ts (Op op [e; e'])))))) ∧
  (conv_panops_alt trees res =
   (case trees of
      [] => SOME res
    | [x] => NONE
    | t1::t2::ts =>
        (case conv_panop t1 of
           NONE => NONE
         | SOME op =>
             (case conv_Exp_alt t2 of
                NONE => NONE
              | SOME e' =>
                  conv_panops_alt ts (Panop op [res; e'])))))
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INR (INR (INR (INL x))) => (list_size ptree_size) (FST x)
                           | INR (INR (INR (INR x))) => (list_size ptree_size) (FST x)
                           | INR (INR (INL x)) => ptree_size x
                           | INR (INL x) => ptree_size x
                           | INL x => (list_size ptree_size) x)’ >> rw[]
  >> Cases_on ‘tree’
  >> gvs[argsNT_def]
End

val tree = “tree:(panLexer$token, pancakeNT, β) parsetree”
val trees = “trees:(panLexer$token, pancakeNT, β) parsetree list”

Triviality conv_Exp_thm:
  (∀trees. (conv_mmap_exp ^trees:'a panLang$exp list option) = OPT_MMAP (λtree. conv_Exp ^tree) ^trees)
  ∧
  (∀tree. conv_ArgList_alt ^tree = (conv_ArgList ^tree: 'a panLang$exp list option))
  ∧
  (∀tree. conv_Exp_alt ^tree = (conv_Exp ^tree:'a panLang$exp option))
  ∧
  (∀trees res. conv_binaryExps_alt ^trees res = (conv_binaryExps ^trees res: 'a panLang$exp option))  ∧
  (∀trees res. conv_panops_alt ^trees res = (conv_panops (^trees) res: 'a panLang$exp option))
Proof
  ho_match_mp_tac (fetch "-" "conv_Exp_alt_ind") \\ rpt strip_tac
  >- (Cases_on ‘trees’>-(fs[]>>gs[conv_Exp_alt_def])>>
      rewrite_tac[Once conv_Exp_alt_def]>>rpt (CASE_TAC>>fs[]))
  >- (simp[Once conv_Exp_alt_def]>>
      PURE_CASE_TAC>>gs[]>>
      simp[conv_Exp_def]>>
      rename1 ‘_ = SOME x’>>Cases_on ‘x’>>gs[])
  >- (Cases_on ‘tree’>>fs[]
      >- (simp[conv_Exp_alt_def, conv_Exp_def])>>
      rename1 ‘Nd p l’>>
      rewrite_tac[Once conv_Exp_alt_def,Once conv_Exp_def]>>
      IF_CASES_TAC
      >- (fs[]>>ntac 2 (CASE_TAC>>fs[]))>>
      IF_CASES_TAC
      >- (fs[]>>ntac 2 (CASE_TAC>>fs[]))>>
      IF_CASES_TAC
      >- (fs[]>>ntac 2 (CASE_TAC>>fs[]) >> metis_tac[])>>
      IF_CASES_TAC
      >- (fs[]>>ntac 6 (CASE_TAC>>fs[]))>>
      IF_CASES_TAC
      >- (fs[]>>ntac 6 (CASE_TAC>>fs[]))>>
      IF_CASES_TAC
      >- (fs[]>>rpt (CASE_TAC>>fs[]))>>
      IF_CASES_TAC
      >- (fs[]>>rpt (CASE_TAC>>fs[])>>metis_tac[option_CASES])
      >- (fs[]>>rpt (CASE_TAC>>fs[])>>metis_tac[option_CASES]))>>
  (Cases_on ‘trees’>>fs[]
   >- simp[Once conv_Exp_alt_def, Once conv_Exp_def]>>
   rename1 ‘h::t’>>Cases_on ‘t’>>fs[]>>
   simp[Once conv_Exp_alt_def, Once conv_Exp_def]>>
   rpt (CASE_TAC>>fs[parserProgTheory.OPTION_BIND_THM]))
QED

val res = translate_no_ind $ spec32 $ SIMP_RULE std_ss [option_map_thm, OPTION_MAP2_thm, FOLDR_eta] conv_Exp_alt_def;

Theorem conv_Exp_ind[local]:
  from_pancake32prog_conv_mmap_exp_ind (:'a)
Proof
  PURE_REWRITE_TAC [fetch "-" "from_pancake32prog_conv_mmap_exp_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  >- (last_x_assum match_mp_tac>>
      rpt strip_tac>>res_tac)
  >- (last_x_assum match_mp_tac>>
      rpt strip_tac>>res_tac)
  >- (last_x_assum match_mp_tac>>
      ntac 3 strip_tac>>
      rename1 ‘tree = Nd p l’>>
      rpt (first_x_assum (qspecl_then [‘p’, ‘l’] assume_tac))>>
      rw[]>>fs[])
  \\ last_x_assum match_mp_tac \\ metis_tac[CONS_11]
QED

val _ = conv_Exp_ind  |> update_precondition;

val res = translate $ spec32 $ GSYM $ cj 3 conv_Exp_thm

val res = translate $ spec32 $ GSYM $ cj 2 conv_Exp_thm

val res = translate $ spec32 $ SIMP_RULE std_ss [option_map_thm, OPTION_MAP2_thm] conv_NonRecStmt_def;

val res = translate $ spec32 $ add_locs_annot_def;

val res = translate butlast_def;

val res = translate $ spec32 $ conv_Dec_def;

val res = translate $ spec32 $ conv_GlobalDec_def;

val res = translate $ spec32 $ conv_DecCall_def;

val res = preprocess $ spec32 conv_Prog_def |> translate_no_ind;

Theorem conv_Prog_ind:
  panptreeconversion_conv_handle_ind
Proof
  PURE_REWRITE_TAC [fetch "-" "panptreeconversion_conv_handle_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (spec32 $ latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac \\ simp[]
  \\ fs[]
QED

val _ = conv_Prog_ind  |> update_precondition;

val res  = translate $ conv_export_def;

val res = translate_no_ind $ spec32 conv_TopDec_def;

Triviality panptreeconversion_conv_topdec_side:
  ∀t. panptreeconversion_conv_topdec_side t
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_conv_topdec_side_def"]
  \\ rpt gen_tac
  \\ rw[]
  \\ once_rewrite_tac [fetch "-" "panptreeconversion_conv_params_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac conv_params_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = panptreeconversion_conv_topdec_side |> update_precondition;

val res = translate_no_ind $ spec32 conv_TopDecList_def;

Triviality panptreeconversion_conv_topdeclist_ind:
  panptreeconversion_conv_topdeclist_ind
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_conv_topdeclist_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac $ spec32 conv_TopDecList_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = panptreeconversion_conv_topdeclist_ind |> update_precondition;

val res = translate $ spec32 panLexerTheory.dest_lexErrorT_def;

val res = translate $ spec32 collect_globals_def;

val res = translate $ spec32 localise_exp_def;

val res = translate_no_ind $ preprocess $ spec32 localise_prog_def;

Triviality panptreeconversion_localise_prog_ind:
  panptreeconversion_localise_prog_ind
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_localise_prog_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac localise_prog_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = panptreeconversion_localise_prog_ind |> update_precondition;

val res = translate $ spec32 localise_topdec_def;

val res = translate $ spec32 localise_topdecs_def;

val res = translate $ spec32 parse_topdecs_to_ast_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
