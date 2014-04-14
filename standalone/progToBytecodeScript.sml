open preamble;
open intLib wordsLib unifyLib;
open astTheory initialEnvTheory lexer_implTheory;
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

val prog_to_bytecode_def = Define `
prog_to_bytecode p =
  case get_all_asts p of
       Failure x => Failure x
     | Success asts =>
         let (x,asts') = elab_prog init_type_bindings asts in
         case FST (infer_prog init_infer_decls [] init_tenvC init_type_env asts' infer$init_infer_state) of
              Failure x => Failure x
            | Success x =>
                let bc = compile_prog (Tdec initial_program::asts') in
                  Success bc`;

val prog_to_bytecode_string_def = Define `
prog_to_bytecode_string p =
  case prog_to_bytecode p of
     | Failure x => Failure x
     | Success bcs => Success (FLAT (MAP (\inst. bc_inst_to_string inst ++ "\n") bcs))`;

val prog_to_bytecode_encoded_def = Define `
prog_to_bytecode_encoded p =
  case prog_to_bytecode p of
     | Failure x => Failure x
     | Success bcs => Success (encode_bc_insts bcs : word64 list option)`;

open optionLib stringLib listLib
open cmlParseTheory cmlPEGTheory
open lexer_funTheory elabTheory inferTheory modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory
open intLangTheory toIntLangTheory toBytecodeTheory compilerTerminationTheory

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

val compset = listLib.list_compset()
(* good libraries which provide compsets :) *)
val () = numposrepLib.add_numposrep_compset compset
val () = ASCIInumbersLib.add_ASCIInumbers_compset compset
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
  fun in_conv tm =
    case strip_comb tm
     of (c,[a1,a2]) =>
          if same_const c in_tm
          then if is_set_spec a2 then SET_SPEC_CONV tm else
               IN_CONV (computeLib.CBV_CONV compset) tm
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
         [ (in_tm, 2, in_conv),
           (insert_tm, 2, fn tm => INSERT_CONV (computeLib.CBV_CONV compset) tm),
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
(* stringLib doesn't provide a compset :( *)
val () = computeLib.add_thms
  [stringTheory.IMPLODE_EXPLODE_I
  ,stringTheory.CHAR_EQ_THM
  ,stringTheory.ORD_CHR_COMPUTE
  ,stringTheory.isDigit_def
  ,stringTheory.isAlpha_def
  ,stringTheory.isLower_def
  ,stringTheory.isUpper_def
  ,stringTheory.isSpace_def
  ] compset
val () = computeLib.add_conv (stringSyntax.ord_tm, 1, stringLib.ORD_CHR_CONV) compset
(* finite_mapLib doesn't provide a compset :( *)
val () = computeLib.add_thms
  [o_f_FEMPTY
  ,FLOOKUP_EMPTY
  ,FLOOKUP_UPDATE
  ,DOMSUB_FLOOKUP_THM
  ,FUNION_FEMPTY_1
  ,FUNION_FEMPTY_2
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
  ,bytecodeTheory.unit_tag_def
  ,bytecodeTheory.closure_tag_def
  ,bytecodeTheory.block_tag_def
  ,conLangTheory.tuple_tag_def
  ,conLangTheory.div_tag_def
  ,conLangTheory.eq_tag_def
  ,conLangTheory.some_tag_def
  ,conLangTheory.none_tag_def
  ] compset
val () = add_datatype_info ``:MMLnonT`` compset
val () = add_datatype_info ``:top`` compset
val () = add_datatype_info ``:dec`` compset
val () = add_datatype_info ``:exp`` compset
val () = add_datatype_info ``:tid_or_exn`` compset
val () = add_datatype_info ``:uop`` compset
val () = add_datatype_info ``:op`` compset
val () = add_datatype_info ``:lit`` compset
val () = add_datatype_info ``:opb`` compset
val () = add_datatype_info ``:opn`` compset
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
  ,init_infer_decls_def
  ,init_infer_state_def
  ,init_type_env_def
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
  ,num_defs_def
  ,mod_tagenv_def
  ] compset
val () = add_datatype_info ``:prompt_i2`` compset
val () = add_datatype_info ``:dec_i2`` compset
val () = add_datatype_info ``:pat_i2`` compset
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
  ] compset
val () = add_datatype_info ``:exp_pat`` compset
val () = add_datatype_info ``:uop_pat`` compset
(* intLang compiler *)
val () = computeLib.add_thms
  [exp_to_Cexp_def
  ,opn_to_prim2_def
  ,free_labs_def
  ,free_vars_def
  ] compset
val () = add_datatype_info ``:Cprim1`` compset
val () = add_datatype_info ``:Cprim2`` compset
(* bytecode compiler *)
val () =
  let
    val (l1,l2) = List.partition(equal"compile" o fst o dest_const o fst o strip_comb o lhs o snd o strip_forall o concl)(CONJUNCTS compile_def)
    val (l2,l3) = List.partition(equal"compile_bindings" o fst o dest_const o fst o strip_comb o lhs o snd o strip_forall o concl) l2
  in computeLib.add_thms
  [compile_Cexp_def
  ,label_closures_def
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
val () = add_datatype_info ``:compiler_result`` compset
val () = add_datatype_info ``:call_context`` compset
(* prog to bytecode *)
val () = computeLib.add_thms
  [prog_to_bytecode_def
  ,prog_to_bytecode_string_def
  ,bc_inst_to_string_def
  ,bc_loc_to_string_def
  ,int_to_string2_def
  ,get_all_asts_def
  ,initial_program_def
  ,init_compiler_state_def
  ,compile_prog_def
  ] compset
val () = add_datatype_info ``:compiler_state`` compset

(*
computeLib.CBV_CONV compset
  ``prog_to_bytecode "val x = 1; val y = x; val it = x+y;"``

computeLib.CBV_CONV compset
  ``toString (Num (1:int))``

computeLib.CBV_CONV compset
  ``prog_to_bytecode "fun fact n = if n <= 0 then 1 else n * fact (n-1); fact 5;"``
*)

val _ = export_theory ();
