open preamble;
open intLib wordsLib unifyLib;
open astTheory initialEnvTheory lexer_implTheory;
open terminationTheory;
open compilerTheory;
open compilerTerminationTheory bytecodeEncodeTheory;

val _ = new_theory "progToBytecode";

(* TODO: Copied from repl_fun. *)
val initial_program_def = Define `
initial_program =
   Dlet (Pcon NONE [Pvar "ref";
                    Pvar "!";
                    Pvar "~";
                    Pvar ":=";
                    Pvar "=";
                    Pvar ">=";
                    Pvar "<=";
                    Pvar ">";
                    Pvar "<";
                    Pvar "mod";
                    Pvar "div";
                    Pvar "*";
                    Pvar "-";
                    Pvar "+"])
        (Con NONE [(Fun "x" (Uapp Opref (Var(Short"x"))));
                   (Fun "x" (Uapp Opderef (Var(Short"x"))));
                   (Fun "x" (App (Opn Minus) (Lit (IntLit 0)) (Var(Short"x"))));
                   (Fun "x" (Fun"y"(App Opassign (Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App Equality(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Geq)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Leq)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Gt)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Lt)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Modulo)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Divide)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Times)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Minus)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Plus)(Var(Short"x"))(Var(Short"y")))))])`;

val get_all_asts_def = tDefine "get_all_asts" `
get_all_asts input =
  case lex_until_toplevel_semicolon input of
       NONE => Success []
     | SOME (tokens, rest_of_input) =>
        case parse_top tokens of
             NONE => Failure "<parse error>\n"
           | SOME top =>
               case get_all_asts rest_of_input of
                    Failure x => Failure x
                  | Success prog => Success (top::prog)`
(wf_rel_tac `measure LENGTH` >>
 rw [lex_until_toplevel_semicolon_LESS]);

val elab_all_asts_def = Define `
elab_all_asts asts =
  case asts of 
     | Failure x => Failure x
     | Success asts =>
         Success (SND (elab_prog init_type_bindings asts))`;

val infer_all_asts_def = Define `
infer_all_asts asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         case FST (infer_prog init_infer_decls [] init_tenvC init_type_env asts infer$init_infer_state) of
            | Failure x => Failure x
            | Success x => Success asts`; 

val compile_all_asts_def = Define `
compile_all_asts asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         Success (compile_prog (Tdec initial_program::asts))`;

val remove_labels_all_asts_def = Define `
remove_labels_all_asts asts =
  case asts of
     | Failure x => Failure x
     | Success asts =>
         Success (code_labels (\x. 0) asts)`;

val all_asts_to_string_def = Define `
all_asts_to_string asts =
  case asts of
     | Failure x => Failure x
     | Success bcs => Success (FLAT (MAP (\inst. bc_inst_to_string inst ++ "\n") bcs))`;

val all_asts_to_encoded_def = Define `
all_asts_to_encoded asts =
  case asts of
     | Failure x => Failure x
     | Success bcs => Success (encode_bc_insts bcs : word64 list option)`;

val prog_to_bytecode_def = Define `
prog_to_bytecode p =
  remove_labels_all_asts (compile_all_asts (infer_all_asts (elab_all_asts (get_all_asts p))))`;

val prog_to_bytecode_string_def = Define `
prog_to_bytecode_string p =
  all_asts_to_string (prog_to_bytecode p)`;

val prog_to_bytecode_encoded_def = Define `
prog_to_bytecode_encoded p =
  case prog_to_bytecode p of
     | Failure x => Failure x
     | Success bcs => Success (encode_bc_insts bcs : word64 list option)`;

open optionLib stringLib listLib
open cmlParseTheory cmlPEGTheory labels_computeLib
open lexer_funTheory elabTheory inferTheory modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory
open intLangTheory toIntLangTheory toBytecodeTheory compilerProofTheory bytecodeLabelsTheory
open terminationTheory compilerTerminationTheory

val () = Parse.bring_to_front_overload"Num"{Name="Num",Thy="integer"}

(* computeLib only adds datatype support for the_compset :(. this code is copied
   and modified slightly to allow building custom compsets with datatype support. *)
local
   val get_f =
      fst o boolSyntax.strip_comb o boolSyntax.lhs o
      snd o boolSyntax.strip_forall o List.hd o boolSyntax.strip_conj o
      Thm.concl
in
   fun add_datatype_info ty =
    let open Drule
        val size_opt =
          case TypeBase.size_of0 ty
           of SOME (_, TypeBasePure.ORIG def) => [def]
            | otherwise => []
        val boolify_opt =
          case TypeBase.encode_of0 ty
           of SOME (_, TypeBasePure.ORIG def) => [def]
            | otherwise => []
        val case_const = Lib.total TypeBase.case_const_of ty
        val simpls = #rewrs (TypeBase.simpls_of ty)
        val (case_thm, simpls) =
           List.partition (fn thm => Lib.total get_f thm = case_const) simpls
        val case_thm = List.map computeLib.lazyfy_thm case_thm
    in
       fn cs =>
       (computeLib.add_thms (size_opt @ boolify_opt @ case_thm @ simpls) cs;
        Option.app (fn t => computeLib.set_skip cs t (SOME 1)) case_const)
    end
end

val compile_Cexp_code_ok_thm = prove(
  ``∀renv rsz cs exp cs'.
    (compile_Cexp renv rsz cs exp = cs') ⇒
    set (free_vars exp) ⊆ count (LENGTH renv) ∧
    no_labs exp ∧ (cs.out = []) ⇒
    code_labels_ok (REVERSE cs'.out)``,
  rw[] >>
  qspecl_then[`renv`,`rsz`,`cs`,`exp`]mp_tac compile_Cexp_thm >>
  simp[] >> strip_tac >> simp[] >>
  PROVE_TAC[REVERSE_APPEND,bytecodeLabelsTheory.code_labels_ok_REVERSE])

val compile_prog_code_ok_thm = prove(
  ``∀ls.
    3 ≤ LENGTH ls ∧
    code_labels_ok (BUTLASTN 3 ls) ∧
    (∀l. ¬uses_label (LASTN 3 ls) l)
    ⇒
    code_labels_ok ls``,
  PROVE_TAC[code_labels_ok_append,code_labels_ok_no_labs,rich_listTheory.APPEND_BUTLASTN_LASTN])

val FORALL_TRUTH = prove(
  ``(∀x. T) ⇔ T``, rw[])

val encode_bc_insts_thm = prove(
  ``∀bcs. encode_bc_insts bcs =
    let ls = MAP encode_bc_inst bcs in
    if EXISTS IS_NONE ls then NONE else
    SOME (FLAT (MAP THE ls))``,
  Induct >> simp[encode_bc_insts_def] >>
  fs[LET_THM] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[])

val compset = wordsLib.words_compset()
(* TODO: add this to intReduce.sml *)
val () = computeLib.add_thms [integerTheory.NUM_OF_INT] compset
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
(* extra option thms :/ *)
val () = computeLib.add_thms
  (map computeLib.lazyfy_thm
     [optionTheory.OPTION_BIND_def
     ,optionTheory.OPTION_GUARD_def
     ,optionTheory.OPTION_IGNORE_BIND_def
     ,optionTheory.OPTION_CHOICE_def])
  compset
val () = computeLib.add_thms
  [optionTheory.OPTION_MAP_DEF
  ] compset
(* combin doesn't provide a compset :( *)
val () = let open combinTheory computeLib
  val K_tm = Term.prim_mk_const{Name="K",Thy="combin"} in
    add_thms
        [K_THM,S_DEF,I_THM,C_DEF,W_DEF,o_THM,K_o_THM,
         APP_DEF,APPLY_UPDATE_THM] compset;
    set_skip compset K_tm (SOME 1)
  end
(* pairLib doesn't provide a compset :( *)
val () = computeLib.add_thms
  (map computeLib.lazyfy_thm
      [CLOSED_PAIR_EQ,FST,SND,pair_case_thm,SWAP_def,
       CURRY_DEF,UNCURRY_DEF,PAIR_MAP_THM])
  compset
(* pred_setLib doesn't provide a compset :( *)
val () = let
  open PFset_conv pred_setLib pred_setSyntax
  fun in_conv eval tm =
    case strip_comb tm
     of (c,[a1,a2]) =>
          if same_const c in_tm
          then if is_set_spec a2 then SET_SPEC_CONV tm else
               IN_CONV eval tm
          else raise ERR "in_conv" "not an IN term"
      | otherwise => raise ERR "in_conv" "not an IN term";
  val T_INTRO =
   let open boolLib Drule
   in Rewrite.PURE_ONCE_REWRITE_RULE
                [SYM (hd(tl (CONJUNCTS (SPEC_ALL EQ_CLAUSES))))]
   end;
  open pred_setTheory
  in
    List.app (Lib.C computeLib.add_conv compset)
         [ (in_tm, 2, in_conv (computeLib.CBV_CONV compset)),
           (insert_tm, 2, INSERT_CONV (computeLib.CBV_CONV compset)),
           (card_tm, 1, CARD_CONV),
           (max_set_tm, 1, MAX_SET_CONV),
           (sum_image_tm, 2, SUM_IMAGE_CONV)
         ];
    computeLib.add_funs
       [INTER_EMPTY,INSERT_INTER,
        CONJ (CONJUNCT1 UNION_EMPTY) INSERT_UNION,
        CONJ EMPTY_DELETE DELETE_INSERT,
        CONJ DIFF_EMPTY DIFF_INSERT,
        CONJ (T_INTRO (SPEC_ALL EMPTY_SUBSET)) INSERT_SUBSET,
        PSUBSET_EQN,
        CONJ IMAGE_EMPTY IMAGE_INSERT,
        CONJ BIGUNION_EMPTY BIGUNION_INSERT,
        LIST_CONJ [BIGINTER_EMPTY,BIGINTER_SING, BIGINTER_INSERT],
        CONJ (T_INTRO (CONJUNCT1 (SPEC_ALL DISJOINT_EMPTY))) DISJOINT_INSERT,
        CROSS_EQNS,CONJUNCT1(SPEC_ALL CROSS_EMPTY),
        FINITE_INSERT, FINITE_EMPTY,
        MIN_SET_THM,
        count_EQN,
        CONJUNCT1 MAX_SET_THM,
        CARD_EMPTY, SUM_SET_DEF,
        CONJUNCT1 (SPEC_ALL SUM_IMAGE_THM),
        SET_EQ_SUBSET, IN_COMPL, POW_EQNS
       ]
  end
val () = computeLib.add_thms
  [LIST_TO_SET_THM
  ,count_EQN
  ,EMPTY_SUBSET
  ] compset
(* finite_mapLib doesn't provide a compset :( *)
val () = computeLib.add_thms
  [o_f_FEMPTY
  ,FLOOKUP_EMPTY
  ,FLOOKUP_UPDATE
  ,FLOOKUP_FUNION
  ,DOMSUB_FLOOKUP_THM
  ,FUNION_FEMPTY_1
  ,FUNION_FEMPTY_2
  ,FUPDATE_LIST_THM
  ,FDOM_FUPDATE
  ,FDOM_FEMPTY
  ] compset
(* examples/parsing doesn't provide a compset :( *)
val () = computeLib.add_thms
  [grammarTheory.isTOK_def
  ,grammarTheory.language_def
  ,grammarTheory.derive_def
  ,grammarTheory.ptree_fringe_def
  ,grammarTheory.complete_ptree_def
  ,grammarTheory.ptree_head_def
  ,grammarTheory.ptree_size_def
  ,pegTheory.subexprs_def
  ,pegTheory.wfG_def
  ,pegTheory.Gexprs_def
  ,pegexecTheory.poplist_aux_def
  ,pegexecTheory.poplistval_def
  ,pegexecTheory.pegparse_def
  ,pegexecTheory.destResult_def
  ,pegexecTheory.applykont_thm
  ,pegexecTheory.peg_exec_thm
  ] compset
val () = add_datatype_info ``:('a,'b)grammar$symbol`` compset
val () = add_datatype_info ``:('a,'b)grammar`` compset
val () = add_datatype_info ``:('a,'b)parsetree`` compset
val () = add_datatype_info ``:('a,'b,'c)pegsym`` compset
val () = add_datatype_info ``:('a,'b,'c)peg`` compset
val () = add_datatype_info ``:('a,'b,'c)kont`` compset
val () = add_datatype_info ``:('a,'b,'c)evalcase`` compset
(* misc :( *)
val () = computeLib.add_thms
  [miscTheory.find_index_def
  ,compilerLibTheory.lunion_def
  ,compilerLibTheory.lshift_def
  ,compilerLibTheory.el_check_def
  ,compilerLibTheory.the_def
  ,compilerLibTheory.num_fold_def
  ,listTheory.MAP2_def
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
val () = add_datatype_info ``:MMLnonT`` compset
val () = add_datatype_info ``:top`` compset
val () = add_datatype_info ``:dec`` compset
val () = add_datatype_info ``:pat`` compset
val () = add_datatype_info ``:exp`` compset
val () = add_datatype_info ``:tid_or_exn`` compset
val () = add_datatype_info ``:uop`` compset
val () = add_datatype_info ``:op`` compset
val () = add_datatype_info ``:lop`` compset
val () = add_datatype_info ``:lit`` compset
val () = add_datatype_info ``:opb`` compset
val () = add_datatype_info ``:opn`` compset
val () = add_datatype_info ``:'a id`` compset
(* lexer *)
val () = computeLib.add_thms
  [lex_until_toplevel_semicolon_def
  ,lex_aux_def
  ,next_token_def
  ,next_sym_def
  ,token_of_sym_def
  ,read_while_def
  ,skip_comment_def
  ,isSymbol_def
  ,isAlphaNumPrime_def
  ,isAlphaNum_def
  ,is_single_char_symbol_def
  ,get_token_def
  ,processIdent_def
  ,tokenUtilsTheory.isInt_def
  ,tokenUtilsTheory.isTyvarT_def
  ,tokenUtilsTheory.destStringT_def
  ,tokenUtilsTheory.destIntT_def
  ,tokenUtilsTheory.destSymbolT_def
  ,tokenUtilsTheory.destAlphaT_def
  ,tokenUtilsTheory.destTOK_def
  ,tokenUtilsTheory.destLf_def
  ,tokenUtilsTheory.destTyvarPT_def
  ,tokenUtilsTheory.destLongidT_def
  ,tokenUtilsTheory.isLongidT_def
  ,tokenUtilsTheory.isWhitespaceT_def
  ,tokenUtilsTheory.isString_def
  ,tokenUtilsTheory.isAlphaSym_def
  ,tokenUtilsTheory.isSymbolT_def
  ,tokenUtilsTheory.isAlphaT_def
  ] compset
val () = add_datatype_info ``:symbol`` compset
val () = add_datatype_info ``:token`` compset
(* parser *)
val () = computeLib.add_thms
  [destResult_def
  ,parse_REPLphrase_def
  ,parse_def
  ,parse_top_def
  ,cmlParseREPLTop_def
  ,cmlParseExpr_def
  ,cmlParseREPLPhrase_def
  ,sumID_def
  ,tokeq_def
  ,cmlPEG_exec_thm
  ,peg_StructName_def
  ,peg_EbaseParen_def
  ,peg_EbaseParenFn_def
  ,peg_longV_def
  ,peg_V_def
  ,peg_TypeDec_def
  ,peg_UQConstructorName_def
  ,pnt_def
  ,try_def
  ,peg_nonfix_def
  ,pegf_def
  ,seql_def
  ,choicel_def
  ,mktokLf_def
  ,bindNT_def
  ,peg_linfix_def
  ,mk_linfix_def
  ,mk_rinfix_def
  ,cmlPtreeConversionTheory.tuplify_def
  ,cmlPtreeConversionTheory.ptree_REPLTop_def
  ,cmlPtreeConversionTheory.ptree_REPLPhrase_def
  ,cmlPtreeConversionTheory.ptree_TopLevelDecs_def
  ,cmlPtreeConversionTheory.ptree_TopLevelDec_def
  ,cmlPtreeConversionTheory.ptree_Structure_def
  ,cmlPtreeConversionTheory.ptree_StructName_def
  ,cmlPtreeConversionTheory.ptree_SignatureValue_def
  ,cmlPtreeConversionTheory.ptree_SpeclineList_def
  ,cmlPtreeConversionTheory.ptree_SpecLine_def
  ,cmlPtreeConversionTheory.ptree_Decls_def
  ,cmlPtreeConversionTheory.ptree_Decl_def
  ,cmlPtreeConversionTheory.ptree_Expr_def
  ,cmlPtreeConversionTheory.mkAst_App_def
  ,cmlPtreeConversionTheory.Eseq_encode_def
  ,cmlPtreeConversionTheory.ptree_Pattern_def
  ,cmlPtreeConversionTheory.mkPatApp_def
  ,cmlPtreeConversionTheory.ptree_FQV_def
  ,cmlPtreeConversionTheory.ptree_Vlist1_def
  ,cmlPtreeConversionTheory.ptree_V_def
  ,cmlPtreeConversionTheory.ptree_Op_def
  ,cmlPtreeConversionTheory.ptree_TypeDec_def
  ,cmlPtreeConversionTheory.ptree_DtypeDecl_def
  ,cmlPtreeConversionTheory.ptree_Dconstructor_def
  ,cmlPtreeConversionTheory.detuplify_def
  ,cmlPtreeConversionTheory.ptree_ConstructorName_def
  ,cmlPtreeConversionTheory.ptree_UQConstructorName_def
  ,cmlPtreeConversionTheory.ptree_TypeName_def
  ,cmlPtreeConversionTheory.ptree_Type_def
  ,cmlPtreeConversionTheory.ptree_linfix_def
  ,cmlPtreeConversionTheory.ptree_Tyop_def
  ,cmlPtreeConversionTheory.ptree_TyvarN_def
  ,cmlPtreeConversionTheory.ptree_UQTyop_def
  ,cmlPtreeConversionTheory.safeTL_def
  ,cmlPtreeConversionTheory.oHD_def
  ] compset
val () = add_datatype_info ``:repl_parse_result`` compset
(* elaborator *)
val () = computeLib.add_thms
  [elab_prog_def
  ,elab_top_def
  ,elab_dec_def
  ,elab_t_def
  ,init_type_bindings_def
  ] compset
(* inferencer *)
val () = unifyLib.reset_wfs_thms()
val () = unifyLib.add_unify_compset compset
val () = computeLib.add_thms
  [infer_prog_def
  ,infer_top_def
  ,infer_d_def
  ,infer_e_def
  ,infer_p_def
  ,st_ex_bind_def
  ,st_ex_return_def
  ,libTheory.lookup_def
  ,libTheory.opt_bind_def
  ,libTheory.emp_def
  ,lookup_tenvC_st_ex_def
  ,typeSystemTheory.merge_tenvC_def
  ,init_tenvC_def
  ,lookup_st_ex_def
  ,init_state_def
  ,get_next_uvar_def
  ,fresh_uvar_def
  ,n_fresh_uvar_def
  ,guard_def
  ,add_constraint_def
  ,add_constraints_def
  ,read_def
  ,generalise_def
  ,apply_subst_list_def
  ,append_decls_def
  ,constrain_op_def
  ,infer_deBruijn_subst_def
  ,Infer_Tfn_def
  ,Infer_Tint_def
  ,Infer_Tbool_def
  ,Infer_Tref_def
  ,Infer_Tunit_def
  ,init_infer_decls_def
  ,init_infer_state_def
  ,init_type_env_def
  ,typeSystemTheory.check_exn_tenv_def
  ,check_freevars_def
  ,mk_id_def
  ,infer_type_subst_def
  ,typeSystemTheory.tid_exn_to_tc_def
  ] compset
val () = add_datatype_info ``:infer_t`` compset
val () = add_datatype_info ``:atom`` compset
val () = add_datatype_info ``:('a,'b)exc`` compset
val () = add_datatype_info ``:'a infer_st`` compset
(* modLang compiler *)
val () = computeLib.add_thms
  [prog_to_i1_def
  ,top_to_i1_def
  ,decs_to_i1_def
  ,dec_to_i1_def
  ,exp_to_i1_def
  ,alloc_defs_def
  ] compset
val () = add_datatype_info ``:prompt_i1`` compset
val () = add_datatype_info ``:dec_i1`` compset
(* conLang compiler *)
val () = computeLib.add_thms
  [prog_to_i2_def
  ,prompt_to_i2_def
  ,decs_to_i2_def
  ,exp_to_i2_def
  ,pat_to_i2_def
  ,uop_to_i2_def
  ,init_tagenv_state_def
  ,get_tagenv_def
  ,lookup_tag_env_def
  ,lookup_tag_flat_def
  ,num_defs_def
  ,mod_tagenv_def
  ,insert_tag_env_def
  ,alloc_tag_def
  ] compset
val () = add_datatype_info ``:prompt_i2`` compset
val () = add_datatype_info ``:dec_i2`` compset
val () = add_datatype_info ``:pat_i2`` compset
val () = add_datatype_info ``:exp_i2`` compset
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
  ] compset
(* patLang compiler *)
val () = computeLib.add_thms
  [exp_to_pat_def
  ,row_to_pat_def
  ,pat_to_pat_def
  ,sLet_pat_def
  ,sIf_pat_def
  ,ground_pat_def
  ,uop_to_pat_def
  ,pure_pat_def
  ,(CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)) Let_Els_pat_def
  ,pure_uop_pat_def
  ] compset
val () = add_datatype_info ``:exp_pat`` compset
val () = add_datatype_info ``:uop_pat`` compset
(* intLang compiler *)
val () = computeLib.add_thms
  [exp_to_Cexp_def
  ,opn_to_prim2_def
  ,free_labs_def
  ,free_vars_def
  ,no_labs_def
  ] compset
val () = add_datatype_info ``:Cprim1`` compset
val () = add_datatype_info ``:Cprim2`` compset
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
val () =
  let
    fun compile_Cexp_conv eval tm =
      let
        val th = (REWR_CONV compile_Cexp_def THENC eval) tm
        val th1 = MATCH_MP compile_Cexp_code_ok_thm th
        val th2 = MP (CONV_RULE(LAND_CONV eval) th1) TRUTH
        val th3 = CONV_RULE (RAND_CONV eval) th2
        val () = labels_computeLib.add_code_labels_ok_thm th3
      in
        th
      end
  in
    computeLib.add_conv(``compile_Cexp``,4,(compile_Cexp_conv (computeLib.CBV_CONV compset))) compset
  end
val () = add_datatype_info ``:compiler_result`` compset
val () = add_datatype_info ``:call_context`` compset
(* labels removal *)
val () = labels_computeLib.reset_code_labels_ok_db()
val () = computeLib.add_conv (``code_labels``,2,code_labels_conv (computeLib.CBV_CONV compset)) compset
(* prog to bytecode *)
val () = computeLib.add_thms
  [prog_to_bytecode_def
  ,prog_to_bytecode_string_def
  ,prog_to_bytecode_encoded_def
  ,bc_inst_to_string_def
  ,bc_loc_to_string_def
  ,int_to_string2_def
  ,encode_bc_insts_thm
  ,encode_bc_inst_def
  ,CONV_RULE(computeLib.CBV_CONV(wordsLib.words_compset()))
    (INST_TYPE[alpha|->``:64``]encode_num_def)
  ,encode_loc_def
  ,encode_char_def
  ,get_all_asts_def
  ,initial_program_def
  ,init_compiler_state_def
  ] compset
val () = add_datatype_info ``:compiler_state`` compset
(* labels removal for the extra printing code added by compile_prog *)
val () =
  let
    fun compile_prog_conv eval tm =
      let
        val th = (REWR_CONV compile_prog_def THENC eval) tm
        fun f ls =
          let
            val th1 = SPEC ls compile_prog_code_ok_thm
            val th2 = MP (CONV_RULE(LAND_CONV eval THENC
                                    (* this could be sped up if necessary *)
                                    PURE_REWRITE_CONV[FORALL_TRUTH,AND_CLAUSES])
                                   th1)
                         TRUTH
          in
            labels_computeLib.add_code_labels_ok_thm th2
          end
        val ls = rhs(concl th)
        val _ = Lib.total f ls
      in
        th
      end
    fun code_labels_ok_conv tm =
      EQT_INTRO
        (labels_computeLib.get_code_labels_ok_thm
          (rand tm))
  in
    computeLib.add_thms
      [rich_listTheory.BUTLASTN_compute
      ,rich_listTheory.LASTN_compute
      ,uses_label_def
      ] compset ;
    add_datatype_info ``:bc_inst`` compset ;
    computeLib.add_conv(``code_labels_ok``,1,code_labels_ok_conv) compset ;
    computeLib.add_conv(``compile_prog``,1,(compile_prog_conv (computeLib.CBV_CONV compset))) compset
  end

val () = computeLib.add_thms
  [elab_all_asts_def
  ,infer_all_asts_def
  ,compile_all_asts_def
  ,all_asts_to_string_def
  ,all_asts_to_encoded_def
  ,remove_labels_all_asts_def
  ] compset

val eval = computeLib.CBV_CONV compset

local
  open TextIO;
  (* Specialised for 64-bit little endian *)
  local
    open IntInf;
    infix ~>>
  in
    fun encode (i:int) =
      Word8Vector.fromList
        (List.map Word8.fromInt [i, (i ~>> 0w8), (i ~>> 0w16), (i ~>> 0w24),
                                 (i ~>> 0w32), (i ~>> 0w40), (i ~>> 0w48), (i ~>> 0w56)])
  end
in
  fun do_compile_string infile outfile =
    let
      val i = openIn infile;
      val s = inputAll i;
      val _ = closeIn i;
      val thm = computeLib.CBV_CONV compset ``case prog_to_bytecode_string ^(fromMLstring s) of Failure x => "<compile error>" ++ x | Success s => s``
      val _ = assert (fn x => hyp x = []) thm;
      val res = fromHOLstring (rhs (concl thm))
      val out = openOut outfile
      val _ = output (out, res)
      val _ = closeOut out
    in
      ()
    end
  fun do_compile_binary infile outfile =
    let
      val i = openIn infile;
      val s = inputAll i;
      val _ = closeIn i;
      val thm = eval ``case prog_to_bytecode_encoded ^(fromMLstring s)
                       of Failure x =>
                         encode_bc_insts (MAP PrintC ("compile error: " ++ x ++ "\n"))
                       | Success s => s``
      val _ = assert (fn x => hyp x = []) thm;
      val res = thm |> concl |> rhs |> dest_some
                    |> listSyntax.dest_list |> fst
                    |> List.map wordsSyntax.uint_of_word
                    |> List.map encode
      val out = BinIO.openOut outfile;
      val _ = List.app (fn ws => BinIO.output (out, ws)) res;
      val _ = BinIO.closeOut out
    in
      ()
    end
end

val initial_bc_state =``
  <| stack := []
   ; code := []
   ; pc := 0
   ; refs := FEMPTY
   ; globals := []
   ; handler := 0
   ; output := ""
   ; cons_names := []
   ; inst_length := K 0
   ; clock := NONE
   |>``

val bc_evaln_def = Define`
  (bc_evaln 0 bs = bs) ∧
  (bc_evaln (SUC n) bs =
   case bc_eval1 bs of
   | NONE => bs
   | SOME bs => bc_evaln n bs)`

val least_from_def = Define`
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P`

val LEAST_thm = prove(
  ``$LEAST P = least_from P 0``,
  rw[least_from_def,ETA_AX])

val least_from_thm = prove(
  ``least_from P n = if P n then n else least_from P (n+1)``,
  rw[least_from_def] >>
  numLib.LEAST_ELIM_TAC >> rw[] >> fs[] >> res_tac >>
  TRY(metis_tac[arithmeticTheory.LESS_OR_EQ]) >- (
    numLib.LEAST_ELIM_TAC >> rw[] >> fs[] >- metis_tac[] >>
    qmatch_rename_tac`a = b`[] >>
    `n ≤ b` by DECIDE_TAC >>
    Cases_on`b < a` >-metis_tac[] >>
    spose_not_then strip_assume_tac >>
    `a < b` by DECIDE_TAC >>
    `¬(n + 1 ≤ a)` by metis_tac[] >>
    `a = n` by DECIDE_TAC >>
    fs[] )
  >- (
    Cases_on`n+1≤x`>-metis_tac[]>>
    `x = n` by DECIDE_TAC >>
    fs[] )
  >- (
    `¬(n ≤ x)` by metis_tac[] >>
    `x = n` by DECIDE_TAC >>
    fs[] ))

val no_labels_def = Define`
  no_labels = EVERY ($~ o is_Label)`
val bc_fetch_aux_0_thm = prove(
  ``∀code pc. bc_fetch_aux code (K 0) pc =
    if no_labels code then el_check pc code
    else FAIL (bc_fetch_aux code (K 0) pc) "code has labels"``,
  REWRITE_TAC[no_labels_def] >>
  Induct >> simp[bytecodeTheory.bc_fetch_aux_def,compilerLibTheory.el_check_def] >>
  rw[] >> fs[combinTheory.FAIL_DEF,compilerLibTheory.el_check_def] >>
  simp[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1])

(* TODO: move? *)
val inst_labels_no_labels = prove(
  ``∀ls f. no_labels (inst_labels f ls)``,
  simp[no_labels_def] >>
  Induct >> simp[inst_labels_def] >>
  Cases >> simp[inst_labels_def] >>
  Cases_on`l`>>simp[inst_labels_def])
val code_labels_no_labels = prove(
  ``∀l ls. no_labels (code_labels l ls)``,
  rw[code_labels_def,inst_labels_no_labels])
val remove_labels_all_asts_no_labels = prove(
  ``(remove_labels_all_asts x = Success ls) ⇒ no_labels ls``,
  Cases_on`x`>>rw[remove_labels_all_asts_def]
  >> rw[code_labels_no_labels])

val () = computeLib.add_thms
  [bytecodeEvalTheory.bc_eval_compute
  ,bytecodeEvalTheory.bc_eval1_def
  ,bytecodeEvalTheory.bc_eval_stack_def
  ,bytecodeTheory.bump_pc_def
  ,bytecodeTheory.bc_fetch_def
  ,bc_fetch_aux_0_thm
  ,bytecodeTheory.bc_equality_result_to_val_def
  ,bytecodeTheory.bool_to_val_def
  ,bytecodeTheory.bool_to_tag_def
  ,bytecodeTheory.bc_find_loc_def
  ,CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook) bc_evaln_def
  ,LEAST_thm
  ,least_from_thm
  ,compilerLibTheory.el_check_def
  ] compset
val () = add_datatype_info ``:bc_state`` compset
val () = add_datatype_info ``:bc_value`` compset

(*
val _ = Globals.max_print_depth := 50

val input = ``"val x = 1; val y = x; val it = x+y;"``
val x1 = eval ``get_all_asts ^(input)``
val x2 = eval ``elab_all_asts ^(x1 |> concl |> rhs)``
val x3 = eval ``infer_all_asts ^(x2 |> concl |> rhs)``
val x4 = eval ``compile_all_asts ^(x3 |> concl |> rhs)``
val x5 = eval ``remove_labels_all_asts ^(x4 |> concl |> rhs)``

val th1 = MATCH_MP remove_labels_all_asts_no_labels x5
val th2 = eval(th1|>concl|>rand|>listSyntax.mk_length)
val () = computeLib.add_thms [EQT_INTRO th1,th2] compset
val res = x5

val x6 = eval ``all_asts_to_encoded ^(x5 |> concl |> rhs)``

val code = rand(rhs(concl x5))
eval ``LENGTH ^code``

val res = eval ``prog_to_bytecode_encoded ^input``
val res = eval ``prog_to_bytecode_string ^input``
val res = eval ``prog_to_bytecode ^input``

val input = ``"fun fact n = if n <= 0 then 1 else n * fact (n-1); fact 5;"``

val input = ``"val it = 1;"``

val th1 = eval ``bc_evaln 100 (^initial_bc_state with code := ^(res |> concl |> rhs |> rand))``
val th2 = eval ``bc_evaln 100 ^(th1 |> concl |> rhs)``
val th3 = eval ``bc_evaln 100 ^(th2 |> concl |> rhs)``
val th4 = eval ``bc_eval1 ^(th3 |> concl |> rhs)``


time (do_compile_binary "tests/test1.ml") "tests/test1.byte"

do_compile_string "tests/test1.ml" "tests/test1.byte"

    val i = openIn "tests/test1.ml";
    val s = inputAll i;
    val _ = closeIn i;
    val asts1 = computeLib.CBV_CONV compset ``get_all_asts ^(fromMLstring s)``;
    val asts1 = computeLib.CBV_CONV compset ``get_all_asts "val x = 1;"``;



    val asts2 = computeLib.CBV_CONV compset ``elab_all_asts ^(asts1 |> concl |> rhs)``;
    val asts3 = computeLib.CBV_CONV compset ``infer_all_asts ^(asts2 |> concl |> rhs)``;
    val asts4 = computeLib.CBV_CONV compset ``compile_all_asts ^(asts3 |> concl |> rhs)``;
    val asts5 = computeLib.CBV_CONV compset ``remove_labels_all_asts ^(asts4 |> concl |> rhs)``;
    val asts6 = computeLib.CBV_CONV compset ``all_asts_to_string ^(asts5 |> concl |> rhs)``;


    val thm = computeLib.CBV_CONV compset ``prog_to_bytecode_string ^(fromMLstring s)``

*)

val _ = export_theory ();
