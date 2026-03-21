structure panItreeDecompilerLib =
struct

open preamble stringSyntax numSyntax stringLib sumSyntax HolKernel boolLib bossLib
     listSyntax mlstringLib optionSyntax simpLib

open itreeTauTheory panLangTheory panSemTheory pan_itreeSemTheory pan_itreePropsTheory
     panItreeAbsSemTheory alignmentTheory wordLangTheory ffiTheory miscTheory


        
val tree_simp_rules = [mem_stores_def, mem_store_def, pair_case_def, flatten_def, DOMSUB_FEMPTY, DOMSUB_FUPDATE,
                       FUPDATE_EQ, DOMSUB_FUPDATE_THM, v_case_def, OPTION_BIND_def, word_lab_case_def,
                       locals_emmpty_locals, empty_locals_with_locals, upds_multi_locals,
                       state_update_locals_locals, upds_multi_memory, DOMSUB_FEMPTY,
                       state_fupdcanon, state_accfupds, option_case_ID, FUPDATE_LIST,
                       bstate_fupdcanon, FOLDR_MAP,FOLDR, option_case_same, bstate_accfupds, result_case_def, con_dif,
                       neq_1w_0w, asmTheory.word_cmp_def, OPTION_BIND_def, wordLangTheory.word_op_def, pan_op_def, is_valid_value_def,
                       shape_of_def, size_of_shape_def, FLOOKUP_SIMP, FUPDATE_LIST_THM,
                       bool_case_ID, bool_case_rev_ID, nb_op_def, eval_simps, size_of_shape_def, shape_of_def,
                       itree_bind_assoc_tuple, itree_bind_v_case_assoc, itree_bind_option_case_assoc, itree_bind_cond_assoc,
                       UNCURRY_DEF, set_kvar_def, lookup_kvar_defs, tau_let_assoc, LET_ValWord, ret_satisfy_LET, LET_v_LET_in,
                       set_kvar_defs, FLOOKUP_SIMP, o_DEF, set_var_defs,
                       itree_bind_ffi_result_CASE_assoc, itree_bind_let_assoc,
                       itree_bind_cond_assoc, shape_of_def, size_of_shape_def, pair_CASE_sum_CASE_assoc, pair_CASE_if_assoc,
                       mem_load_def, word_of_val_def, struct_of_val_def, LET_AND_split, LET_OR_split,
                       itree_bind_assoc, itree_bind_sum_case_assoc, itree_bind_pair_case_assoc,itree_bind_result_case_def,
                       ret_satisfy_Tau, ret_satisfy_Ret, ret_satisfy_Vis, pair_CASE_same, sum_CASE_eq_pair, COND_eq_pair,
                       bstate_fupdfupds,bstate_fupdcanon,bstate_accfupds,bstate_accessors,empty_locals_def, THE_LET_in,
                       sum_CASE_and, COND_and, OPTION_EQ_AND_IMPL_simp, EXISTS_OR_THM, EXISTS_sum_CASE_THM, EXISTS_COND_THM,
                       option_case_NONE_F, sum_CASE_same, LET_concrete, exists_LET, word_of_val_LET_in, LET_AND,
                       val_mem_valword, val_mem_valword_LET, if_then_else_word_simp, COND_ID,
                       eval_exists_strengthen, ret_satisfy_if, word_lab_exists_word]

         
(*
fun mk_var_from_shape start_num exp_list shape_term =
  if same_const shape_term “One” then
    let val word_term = mk_var (concat ["word_", int_to_string start_num], mk_type ("cart", [“:bool” ,“:32”]))
    in
      (start_num + 1, exp_list@[“ValWord ^word_term”])
    end
  else
    let val shape_list = rand shape_term |> dest_list |> fst
        val (new_num, var_list) = foldl (fn (z, (x, y)) => (mk_var_from_shape x y z)) (start_num, []) shape_list
        val var_list_term = mk_list (var_list, mk_type ("v", [“:32”]))
        val struct_term = inst [alpha |-> “:32”] “Struct”
    in
      (new_num, exp_list@[mk_comb (struct_term, var_list_term)])
    end
*)

fun mk_var_from_shape_once avoid_names [] ty_arg = []
  | mk_var_from_shape_once avoid_names (shape_term::shape_terms) ty_arg =
    if same_const shape_term “One” then
      let val word_term = mk_var ("w", mk_type ("cart", [“:bool” ,ty_arg]))
          val new_word = variant avoid_names word_term
      in
        “ValWord ^new_word”::mk_var_from_shape_once (new_word::avoid_names) shape_terms ty_arg
      end
    else
      let val struct_term = mk_var ("vst", mk_type ("list", [mk_type ("v", [ty_arg])]))
          val new_struct = variant avoid_names struct_term
      in
        “Struct ^new_struct”::mk_var_from_shape_once (new_struct::avoid_names) shape_terms ty_arg
      end
(*
val t_varaaa = mk_var_from_shape 0 [] “Comb [One; Comb [One; Comb [One]; Comb [One; One; One]]]”

val t_var = mk_var_from_shape_once [] [“Comb [One; Comb [One; Comb []; Comb [One; One; One]]]”, “Comb []”, “One”] “:32”
*)
    
fun mk_args_from_aexps avoid_names [] = []
  | mk_args_from_aexps avoid_names (aexp::aexps) =
    let val aexp_type = type_of aexp
        val (_, ty_args) = dest_type aexp_type
        val arg = variant avoid_names (mk_var ("arg", mk_type ("v", ty_args)))
    in
      arg::mk_args_from_aexps (arg::avoid_names) aexps
      end

fun mk_args_from_aexps avoid_names 0 abty = []
  | mk_args_from_aexps avoid_names n abty =
    let val arg = variant avoid_names (mk_var ("arg", mk_type ("v", [abty])))
    in
      arg::mk_args_from_aexps (arg::avoid_names) (n - 1) abty
      end

fun strip_val_struct t =
  let val (c, _) = t |> strip_comb
  in
    if same_const “Val” c then
      t |> rand |> rand
    else
      t |> rand
    end

fun mk_eval_val_term vstv st exp =
  let val (c, _) = vstv |> strip_comb
  in
    if same_const “Val” c then
       “word_of_val (THE (eval ^st ^exp))”
    else
      “struct_of_val (THE (eval ^st ^exp))”
    end
    
fun eval_some_rw th =
  let val eval_term = find_terms (can (match_term “eval _ _”)) (th |> concl)
      val eval_rules = filter (fn x => x |> concl |> rhs |> is_some) (map (QCONV (SIMP_CONV (srw_ss ()) (eval_def::tree_simp_rules))) eval_term)
  in
    if null eval_rules then
      th
    else
      SIMP_RULE (srw_ss ()) eval_rules th
    end

(*
fun mk_call_pre_thm_with_argexps_bu scode fundecs code_thm te =
  let val tree_ty = type_of te
      val tau_ty = mk_type ("fun", [tree_ty, tree_ty])
      val arb_tau = “Tau”
      val ty_match = match_type (type_of arb_tau) tau_ty
      val tau_term = (inst:(hol_type,hol_type) subst -> term -> term) ty_match arb_tau
      val (itc, [progst]) = te |> strip_comb
      val (_, [prog, state]) = progst |> strip_comb
      val (_, [calty, fname, aexps_term]) = prog |> strip_comb
      val (aexps, aexp_type) = aexps_term |> dest_list                         
      val (_, [ty_arg]) = dest_type aexp_type
      val fpb = EVAL “funcname_params_list ^fundecs” |> concl |> rhs
      val fpb_l = fpb |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val (_, (varsh, _)) = List.find (fn (x, (_, _)) => term_eq x fname) fpb_l |> valOf
      val varname_shape_list = varsh |> dest_list |> fst |> map dest_pair
      val args = mk_var_from_shape_once [] (map snd varname_shape_list) ty_arg                    
      val args_term = mk_list (args, mk_type ("v", [ty_arg]))
      val prog_q = mk_var ("q", type_of prog)
      val map_r = mk_var ("r", mk_type ("fmap", [“:mlstring”, mk_type ("v", [ty_arg])]))
      val eval_some_terms = ListPair.map (fn (x, y) => “eval ^state ^x = SOME ^y”) (aexps, args)
      val asm_term = list_mk_conj (eval_some_terms@[“lookup_code ^state.code ^fname ^args_term = SOME (^prog_q, ^map_r)”])
      val exists_terms = prog_q::map_r::(map strip_val_struct args)
      val asm_exists_term = list_mk_exists (exists_terms, asm_term)
      val arg_inner_term =
      “let (vshapes,prog) = THE (FLOOKUP ^state.code ^fname)
        in
          ^tau_term
          (^itc
            (prog,
             ^state with
              locals :=
             FEMPTY |++ ZIP (MAP FST vshapes,^args_term)) >>=
            (λres. itree_call_handler ^calty ^state res))”
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) arg_inner_term v_THE_list
      val concl_term = mk_eq (te, concl_rhs_term)
      val goal_term = mk_imp (asm_exists_term, concl_term)
      val tree_thm = prove (goal_term,
                            rpt disch_tac
                            \\ DEP_REWRITE_TAC[itree_semantics_Call_with_pre]
                            \\ rpt strip_tac
                            \\ rw[FUN_EQ_THM, lookup_code_def]
                            \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def])
      val code_tree_thm = ADD_ASSUM “^state.code = ^scode” tree_thm
                            |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                            |> DISCH_ALL
                            |> eval_some_rw
                            |> SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord]
  in
    code_tree_thm
    end

    
fun mk_deccall_pre_thm_with_argexps scode fundecs code_thm te =
  let val tree_ty = type_of te
      val tau_ty = mk_type ("fun", [tree_ty, tree_ty])
      val arb_tau = “Tau”
      val ty_match = match_type (type_of arb_tau) tau_ty
      val tau_term = (inst:(hol_type,hol_type) subst -> term -> term) ty_match arb_tau
      val (itc, [progst]) = te |> strip_comb
      val (_, [prog, state]) = progst |> strip_comb
      val (_, [rt, sh, fname, aexps_term, prog1]) = prog |> strip_comb
      val (aexps, aexp_type) = aexps_term |> dest_list                         
      val (_, [ty_arg]) = dest_type aexp_type
      val fpb = EVAL “funcname_params_list ^fundecs” |> concl |> rhs
      val fpb_l = fpb |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val (_, (varsh, _)) = List.find (fn (x, (_, _)) => term_eq x fname) fpb_l |> valOf
      val varname_shape_list = varsh |> dest_list |> fst |> map dest_pair
      val args = mk_var_from_shape_once [] (map snd varname_shape_list) ty_arg
      val args_term = mk_list (args, mk_type ("v", [ty_arg]))
      val prog_q = mk_var ("q", type_of prog)
      val eval_some_terms = ListPair.map (fn (x, y) => “eval ^state ^x = SOME ^y”) (aexps, args)
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val eval_some_exists_terms = ListPair.map (fn (x, y) => boolSyntax.mk_exists (strip_val_struct x, y)) (args, eval_some_terms)
      val var_count = length varname_shape_list
      val vname_list = list_mk_var_ty "vname" [] “:mlstring” var_count
      val shape_list = list_mk_var_ty "sh" [] “:shape” var_count
      val var_shape_pair_list = map mk_pair (zip vname_list shape_list)
      val var_shape_pair_list_term = mk_list (var_shape_pair_list, mk_type("prod", [“:mlstring”, “:shape”]))
      val asm_flookup_term = “FLOOKUP ^scode ^fname = SOME (^var_shape_pair_list_term, ^prog_q)”
      val vname_list_term = mk_list (vname_list, “:mlstring”)
      val asm_all_distinct_term = “ALL_DISTINCT ^vname_list_term”
      val shape_eq_terms = ListPair.map (fn (sh, args) => “^sh = shape_of ^args ”) (shape_list, args)
      val vname_arg_list = ListPair.map mk_pair (vname_list, args)
      val vname_arg_list_term = mk_list (vname_arg_list, mk_type("prod", [“:mlstring”, mk_type ("v", [ty_arg])]))
      val asm_inner_term = list_mk_conj ([asm_flookup_term, asm_all_distinct_term]@shape_eq_terms@
                                                    [“ret_satisfy
                                                     (λx.
                                                        ∃r s'.
                                                          x = INR (SOME r,s') ∧
                                                          ∀retv.
                                                            r = Return retv ⇒
                                                            Pre_next (set_var ^rt retv (s' with locals := ^state.locals)))
                                                     (itree_semantics (^prog_q, ^state with locals := FEMPTY |++ ^vname_arg_list_term))”])
      val asm_let_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) asm_inner_term v_THE_list
      val exists_terms = prog_q::vname_list@shape_list
      val asm_exists_term = list_mk_exists (exists_terms, asm_let_term)
      val asm_all_term = list_mk_conj (“^state.code = ^scode”::eval_some_exists_terms@[asm_exists_term])
      val arg_inner_term =
      “let (vshapes,prog) = THE (FLOOKUP ^scode ^fname)
        in
          ^tau_term
          (^itc
            (prog,
             ^state with
              locals :=
             FEMPTY |++ ZIP (MAP FST vshapes,^args_term)) >>=
            (λres. itree_deccall_handler ^rt ^sh ^state res t))”
      val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) arg_inner_term v_THE_list
      val concl_term = mk_eq (te, concl_rhs_term)
      val goal_term = mk_imp (“(∀s. Pre_next s ⇒ ^itc (^prog1,s) = t s)”, mk_imp (asm_all_term, concl_term))
      val tree_thm = prove (goal_term,
                            rpt disch_tac
                            \\ DEP_REWRITE_TAC[cj 2 itree_semantics_DecCall_with_pre_ret_satisfy]
                            \\ rpt strip_tac
                            \\ rw[FUN_EQ_THM, lookup_code_def]
                            \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def]
                            \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                            \\ gvs[]
                            \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                            \\ rw[])
      val code_tree_thm_with_pre = (UNDISCH_CONJUNCTS_ALL tree_thm)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> ASM_SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM]
      val asm_term_non_pre = list_mk_conj ([asm_flookup_term, asm_all_distinct_term]@shape_eq_terms)
      val asm_exists_term_non_pre = list_mk_conj (“^state.code = ^scode”::eval_some_exists_terms@[list_mk_exists (exists_terms, asm_term_non_pre)])
      val goal_term_non_pre = mk_imp (“(∀s. ^itc (^prog1,s) = t s)”, mk_imp (asm_exists_term_non_pre, concl_term))
      val tree_thm_non_pre = prove (goal_term_non_pre,
                                    rpt disch_tac
                                    \\ DEP_REWRITE_TAC[cj 1 itree_semantics_DecCall_with_pre_ret_satisfy]
                                    \\ rpt strip_tac
                                    \\ rw[FUN_EQ_THM, lookup_code_def]
                                    \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def]
                                    \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                                    \\ gvs[]
                                    \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                                    \\ rw[])
      val code_tree_thm_non_pre = (UNDISCH_CONJUNCTS_ALL tree_thm_non_pre)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> ASM_SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM]
  in
    CONJ code_tree_thm_non_pre code_tree_thm_with_pre
    end
*)

fun list_mk_var_ty varname avoid_names varty 0 = []
  | list_mk_var_ty varname avoid_names varty n =
    let val raw_var = mk_var (varname, varty)
        val new_var = variant avoid_names raw_var
    in
      new_var::list_mk_var_ty varname (new_var::avoid_names) varty (n - 1)
      end

val csavcas = list_mk_var_ty "var" [] “:shape” 3

fun UNDISCH_CONJUNCTS_ALL th = UNDISCH_CONJUNCTS_ALL (hurdUtils.UNDISCH_CONJUNCTS th)
                                                     handle _ => th

fun UNDISCH_COMP_CONJUNCTS_ALL th =
  let val undisched_th = UNDISCH_CONJUNCTS_ALL th
  in
    if null (filter I (map is_conj (hyp undisched_th))) then
      undisched_th
    else
      UNDISCH_COMP_CONJUNCTS_ALL (DISCH_ALL undisched_th)
    end

val fsdacsc = ASSUME “(a ∧ c) ∧ d ⇒ b” |> UNDISCH_COMP_CONJUNCTS_ALL |> DISCH_ALL

    
fun mk_call_pre_thm_with_argexps scode fundecs code_thm te =
  let val all_v_list = all_vars te
      val tree_ty = type_of te
      val tau_ty = mk_type ("fun", [tree_ty, tree_ty])
      val arb_tau = “Tau”
      val ty_match = match_type (type_of arb_tau) tau_ty
      val tau_term = (inst:(hol_type,hol_type) subst -> term -> term) ty_match arb_tau
      val (itc, [progst]) = te |> strip_comb
      val (_, [prog, state]) = progst |> strip_comb
      val (_, [calty, fname, aexps_term]) = prog |> strip_comb
      val (aexps, aexp_type) = aexps_term |> dest_list                         
      val (_, [ty_arg]) = dest_type aexp_type
      val fpb = EVAL “funcname_params_list ^fundecs” |> concl |> rhs
      val fpb_l = fpb |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val (_, (varsh, _)) = List.find (fn (x, (_, _)) => term_eq x fname) fpb_l |> valOf
      val varname_shape_list = varsh |> dest_list |> fst |> map dest_pair
      val args = mk_var_from_shape_once all_v_list (map snd varname_shape_list) ty_arg
      val args_vars = map strip_val_struct args
      val args_term = mk_list (args, mk_type ("v", [ty_arg]))
      val prog_q = mk_var ("q", type_of prog)
      val eval_some_terms = ListPair.map (fn (x, y) => “eval ^state ^x = SOME ^y”) (aexps, args)
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val eval_some_exists_terms = ListPair.map (fn (x, y) => boolSyntax.mk_exists (strip_val_struct x, y)) (args, eval_some_terms)
      val var_count = length varname_shape_list
      val vname_list = list_mk_var_ty "vname" (args_vars@all_v_list) “:mlstring” var_count
      val shape_list = list_mk_var_ty "sh" (vname_list@args_vars@all_v_list) “:shape” var_count
      val var_shape_pair_list = map mk_pair (zip vname_list shape_list)
      val var_shape_pair_list_term = mk_list (var_shape_pair_list, mk_type("prod", [“:mlstring”, “:shape”]))
      val asm_flookup_term = “FLOOKUP ^scode ^fname = SOME (^var_shape_pair_list_term, ^prog_q)”
      val vname_list_term = mk_list (vname_list, “:mlstring”)
      val asm_all_distinct_term = “ALL_DISTINCT ^vname_list_term”
      val shape_eq_terms = ListPair.map (fn (sh, args) => “^sh = shape_of ^args ”) (shape_list, args)
      val vname_arg_list = ListPair.map mk_pair (vname_list, args)
      val vname_arg_list_term = mk_list (vname_arg_list, mk_type("prod", [“:mlstring”, mk_type ("v", [ty_arg])]))
      val exists_terms = prog_q::vname_list@shape_list
      val asm_term = list_mk_conj ([asm_flookup_term, asm_all_distinct_term]@shape_eq_terms)
      val asm_exists_term = list_mk_conj (“^state.code = ^scode”::eval_some_exists_terms@[list_mk_exists (exists_terms, asm_term)])
      val arg_inner_term =
      “let (vshapes,prog) = THE (FLOOKUP ^state.code ^fname)
        in
          ^tau_term
          (^itc
            (prog,
             ^state with
              locals :=
             FEMPTY |++ ZIP (MAP FST vshapes,^args_term)) >>=
            (λres. itree_call_handler ^calty ^state res))”
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) arg_inner_term v_THE_list
      val concl_term = mk_eq (te, concl_rhs_term)
      val goal_term = mk_imp (asm_exists_term, concl_term)
      val tree_thm = prove (goal_term,
                            rpt disch_tac
                            \\ DEP_REWRITE_TAC[itree_semantics_Call_with_pre]
                            \\ rpt strip_tac
                            \\ rw[FUN_EQ_THM, lookup_code_def]
                            \\ FULL_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def])
      val code_tree_thm = tree_thm
                            |> UNDISCH_COMP_CONJUNCTS_ALL
                            |> DISCH_ALL
                            |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                            |> DISCH_ALL
                            |> eval_some_rw
                            |> SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM, exists_LET]
  in
    code_tree_thm
    end

        
(*
val (test1_topdecs, _) = parse_pancake_file “:32” "test1.pnk"

val test1_fundecs = topdecs_to_fundecs test1_topdecs

val (t1_code_thm, t1_lookup_thms) = codes_lookup_funcs_assms "test1" test1_fundecs

val t1_code = t1_code_thm |> concl |> lhs

val asdc = EVAL “funcname_params_list ^test1_fundecs”
    
val test1_shallow = decompile_2 "test1" [] test1_fundecs

val fdac = mk_call_pre_thm_with_argexps
           “^t1_code” “^test1_fundecs” t1_lookup_thms “itree_semantics (StandAloneCall NONE «fib» [], nst:32 bstate)”



Theorem Deccall_test:
  (∀s. itree_semantics (prog1,s) = t s) ⇒
  (∃arg1 arg2 q r.
        OPT_MMAP (eval s) [exp1; exp2] = SOME [ValWord arg1; Struct arg2] ∧
        lookup_code s.code fname [ValWord arg1; Struct arg2] = SOME (q,r)) ⇒
  itree_semantics (DecCall rt sh fname [exp1; exp2] prog1,s) =
  (let
     arg1 = word_of_val (THE (eval s exp1));
     arg2 = struct_of_val (THE (eval s exp2));
     (vshapes,prog) = THE (FLOOKUP s.code fname)
   in
     Tau
     (itree_semantics
      (prog,
       s with
         locals :=
       FEMPTY |++ ZIP (MAP FST vshapes,[ValWord arg1; Struct arg2])) >>=
      (λres. itree_deccall_handler rt sh s res t)))
Proof
  rpt disch_tac
  \\ DEP_REWRITE_TAC[cj 1 itree_semantics_DecCall_with_pre_ret_satisfy]
  \\ rpt strip_tac
  \\ rw[FUN_EQ_THM, lookup_code_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def]
QED

Theorem Deccall_test_non_pre:
  (∀s. itree_semantics (prog1,s) = t s) ⇒
  (∃arg1 arg2 shape1 shape2 var1 var2 q r.
     OPT_MMAP (eval s) [exp1; exp2] = SOME [ValWord arg1; Struct arg2] ∧
     FLOOKUP s.code fname = SOME ([(var1, shape1); (var2, shape2)], q) ∧
     ALL_DISTINCT [var1; var2] ∧
     shape1 = shape_of (ValWord arg1) ∧
     shape2 = shape_of (Struct arg2)) ⇒
  itree_semantics (DecCall rt sh fname [exp1; exp2] prog1,s) =
  (let
     arg1 = word_of_val (THE (eval s exp1));
     arg2 = struct_of_val (THE (eval s exp2));
     (vshapes,prog) = THE (FLOOKUP s.code fname)
   in
     Tau
     (itree_semantics
      (prog,
       s with
         locals :=
       FEMPTY |++ ZIP (MAP FST vshapes,[ValWord arg1; Struct arg2])) >>=
      (λres. itree_deccall_handler rt sh s res t)))
Proof
  rpt disch_tac
  \\ DEP_REWRITE_TAC[cj 1 itree_semantics_DecCall_with_pre_ret_satisfy]
  \\ rpt strip_tac
  \\ rw[FUN_EQ_THM, lookup_code_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def]
QED
        
    
Theorem Deccall_test:
  (∀s. Pre_next s ⇒ itree_semantics (prog1,s) = t s) ⇒
  (∃arg1 arg2 shape1 shape2 var1 var2 q r.
     OPT_MMAP (eval s) [exp1; exp2] = SOME [ValWord arg1; Struct arg2] ∧
     FLOOKUP s.code fname = SOME ([(var1, shape1); (var2, shape2)], q) ∧
     ALL_DISTINCT [var1; var2] ∧
     shape1 = shape_of (ValWord arg1) ∧
     shape2 = shape_of (Struct arg2) ∧
        ret_satisfy
        (λx.
           ∃r s'.
             x = INR (SOME r,s') ∧
             ∀retv.
               r = Return retv ⇒
               Pre_next (set_var rt retv (s' with locals := s.locals)))
        (itree_semantics (q,s with locals := FEMPTY |++ [(var1,ValWord arg1); (var2,Struct arg2)]))) ⇒
  itree_semantics (DecCall rt sh fname [exp1; exp2] prog1,s) =
  (let
     arg1 = word_of_val (THE (eval s exp1));
     arg2 = struct_of_val (THE (eval s exp2));
     (vshapes,prog) = THE (FLOOKUP s.code fname)
   in
     Tau
     (itree_semantics
      (prog,
       s with
         locals :=
       FEMPTY |++ ZIP (MAP FST vshapes,[ValWord arg1; Struct arg2])) >>=
      (λres. itree_deccall_handler rt sh s res t)))
Proof
  rpt disch_tac
  \\ DEP_REWRITE_TAC[cj 2 itree_semantics_DecCall_with_pre_ret_satisfy]
  \\ rpt strip_tac
  \\ rw[FUN_EQ_THM, lookup_code_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def]
QED



fun mk_deccall_pre_thm_with_argexps_bu scode fundecs code_thm te =
  let val tree_ty = type_of te
      val tau_ty = mk_type ("fun", [tree_ty, tree_ty])
      val arb_tau = “Tau”
      val ty_match = match_type (type_of arb_tau) tau_ty
      val tau_term = (inst:(hol_type,hol_type) subst -> term -> term) ty_match arb_tau
      val (itc, [progst]) = te |> strip_comb
      val (_, [prog, state]) = progst |> strip_comb
      val (_, [rt, sh, fname, aexps_term, prog1]) = prog |> strip_comb
      val (aexps, aexp_type) = aexps_term |> dest_list                         
      val (_, [ty_arg]) = dest_type aexp_type
      val fpb = EVAL “funcname_params_list ^fundecs” |> concl |> rhs
      val fpb_l = fpb |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val (_, (varsh, _)) = List.find (fn (x, (_, _)) => term_eq x fname) fpb_l |> valOf
      val varname_shape_list = varsh |> dest_list |> fst |> map dest_pair
      val args = mk_var_from_shape_once [] (map snd varname_shape_list) ty_arg                    
      val args_term = mk_list (args, mk_type ("v", [ty_arg]))
      val prog_q = mk_var ("q", type_of prog)
      val map_r = mk_var ("r", mk_type ("fmap", [“:mlstring”, mk_type ("v", [ty_arg])]))
      val eval_some_terms = ListPair.map (fn (x, y) => “eval ^state ^x = SOME ^y”) (aexps, args)
      val asm_term = list_mk_conj (eval_some_terms@[“lookup_code ^state.code ^fname ^args_term = SOME (^prog_q, ^map_r)”,
                                                    “ret_satisfy
                                                     (λx.
                                                        ∃r s'.
                                                          x = INR (SOME r,s') ∧
                                                          ∀retv.
                                                            r = Return retv ⇒
                                                            Pre_next (set_var ^rt retv (s' with locals := ^state.locals)))
                                                     (itree_semantics (^prog_q, ^state with locals := ^map_r))”])
      val exists_terms = prog_q::map_r::(map strip_val_struct args)
      val asm_exists_term = list_mk_exists (exists_terms, asm_term)
      val arg_inner_term =
      “let (vshapes,prog) = THE (FLOOKUP ^state.code ^fname)
        in
          ^tau_term
          (^itc
            (prog,
             ^state with
              locals :=
             FEMPTY |++ ZIP (MAP FST vshapes,^args_term)) >>=
            (λres. itree_deccall_handler ^rt ^sh ^state res t))”
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) arg_inner_term v_THE_list
      val concl_term = mk_eq (te, concl_rhs_term)
      val goal_term = mk_imp (“(∀s. Pre_next s ⇒ ^itc (^prog1,s) = t s)”, mk_imp (asm_exists_term, concl_term))
      val tree_thm = prove (goal_term,
                            rpt disch_tac
                            \\ DEP_REWRITE_TAC[cj 2 itree_semantics_DecCall_with_pre_ret_satisfy]
                            \\ rpt strip_tac
                            \\ rw[FUN_EQ_THM, lookup_code_def]
                            \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def])
      val code_tree_thm_with_pre = ADD_ASSUM “^state.code = ^scode” (UNDISCH_ALL tree_thm)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord]
      val asm_term_non_pre = list_mk_conj (eval_some_terms@[“lookup_code ^state.code ^fname ^args_term = SOME (^prog_q, ^map_r)”])
      val asm_exists_term_non_pre = list_mk_exists (exists_terms, asm_term_non_pre)
      val goal_term_non_pre = mk_imp (“(∀s. ^itc (^prog1,s) = t s)”, mk_imp (asm_exists_term_non_pre, concl_term))
      val tree_thm_non_pre = prove (goal_term_non_pre,
                                    rpt disch_tac
                                    \\ DEP_REWRITE_TAC[cj 1 itree_semantics_DecCall_with_pre_ret_satisfy]
                                    \\ rpt strip_tac
                                    \\ rw[FUN_EQ_THM, lookup_code_def]
                                    \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def])
      val code_tree_thm_non_pre = ADD_ASSUM “^state.code = ^scode” (UNDISCH_ALL tree_thm_non_pre)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord]
  in
    CONJ code_tree_thm_non_pre code_tree_thm_with_pre
    end

                
fun mk_deccall_pre_thm_with_argexps_bu scode fundecs code_thm te =
  let val tree_ty = type_of te
      val tau_ty = mk_type ("fun", [tree_ty, tree_ty])
      val arb_tau = “Tau”
      val ty_match = match_type (type_of arb_tau) tau_ty
      val tau_term = (inst:(hol_type,hol_type) subst -> term -> term) ty_match arb_tau
      val (itc, [progst]) = te |> strip_comb
      val (_, [prog, state]) = progst |> strip_comb
      val (_, [rt, sh, fname, aexps_term, prog1]) = prog |> strip_comb
      val (aexps, aexp_type) = aexps_term |> dest_list                         
      val (_, [ty_arg]) = dest_type aexp_type
      val fpb = EVAL “funcname_params_list ^fundecs” |> concl |> rhs
      val fpb_l = fpb |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val (_, (varsh, _)) = List.find (fn (x, (_, _)) => term_eq x fname) fpb_l |> valOf
      val varname_shape_list = varsh |> dest_list |> fst |> map dest_pair
      val args = mk_var_from_shape_once [] (map snd varname_shape_list) ty_arg
      val args_term = mk_list (args, mk_type ("v", [ty_arg]))
      val prog_q = mk_var ("q", type_of prog)
      val eval_some_terms = ListPair.map (fn (x, y) => “eval ^state ^x = SOME ^y”) (aexps, args)
      val var_count = length varname_shape_list
      val vname_list = list_mk_var_ty "vname" [] “:mlstring” var_count
      val shape_list = list_mk_var_ty "sh" [] “:shape” var_count
      val var_shape_pair_list = map mk_pair (zip vname_list shape_list)
      val var_shape_pair_list_term = mk_list (var_shape_pair_list, mk_type("prod", [“:mlstring”, “:shape”]))
      val asm_flookup_term = “FLOOKUP ^scode ^fname = SOME (^var_shape_pair_list_term, ^prog_q)”
      val vname_list_term = mk_list (vname_list, “:mlstring”)
      val asm_all_distinct_term = “ALL_DISTINCT ^vname_list_term”
      val shape_eq_terms = ListPair.map (fn (sh, args) => “^sh = shape_of ^args ”) (shape_list, args)
      val vname_arg_list = ListPair.map mk_pair (vname_list, args)
      val vname_arg_list_term = mk_list (vname_arg_list, mk_type("prod", [“:mlstring”, mk_type ("v", [ty_arg])]))
      val asm_term = list_mk_conj (“^state.code = ^scode”::eval_some_terms@[asm_flookup_term, asm_all_distinct_term]@shape_eq_terms@
                                                    [“ret_satisfy
                                                     (λx.
                                                        ∃r s'.
                                                          x = INR (SOME r,s') ∧
                                                          ∀retv.
                                                            r = Return retv ⇒
                                                            Pre_next (set_var ^rt retv (s' with locals := ^state.locals)))
                                                     (itree_semantics (^prog_q, ^state with locals := FEMPTY |++ ^vname_arg_list_term))”])
      val exists_terms = prog_q::(map strip_val_struct args)@vname_list@shape_list
      val asm_exists_term = list_mk_exists (exists_terms, asm_term)
      val arg_inner_term =
      “let (vshapes,prog) = THE (FLOOKUP ^scode ^fname)
        in
          ^tau_term
          (^itc
            (prog,
             ^state with
              locals :=
             FEMPTY |++ ZIP (MAP FST vshapes,^args_term)) >>=
            (λres. itree_deccall_handler ^rt ^sh ^state res t))”
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) arg_inner_term v_THE_list
      val concl_term = mk_eq (te, concl_rhs_term)
      val goal_term = mk_imp (“(∀s. Pre_next s ⇒ ^itc (^prog1,s) = t s)”, mk_imp (asm_exists_term, concl_term))
      val tree_thm = prove (goal_term,
                            rpt disch_tac
                            \\ DEP_REWRITE_TAC[cj 2 itree_semantics_DecCall_with_pre_ret_satisfy]
                            \\ rpt strip_tac
                            \\ rw[FUN_EQ_THM, lookup_code_def]
                            \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def]
                            \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                            \\ gvs[]
                            \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                            \\ rw[])
      val code_tree_thm_with_pre = (UNDISCH_ALL tree_thm)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> ASM_SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM]
      val asm_term_non_pre = list_mk_conj (“^state.code = ^scode”::eval_some_terms@[asm_flookup_term, asm_all_distinct_term]@shape_eq_terms)
      val asm_exists_term_non_pre = list_mk_exists (exists_terms, asm_term_non_pre)
      val goal_term_non_pre = mk_imp (“(∀s. ^itc (^prog1,s) = t s)”, mk_imp (asm_exists_term_non_pre, concl_term))
      val tree_thm_non_pre = prove (goal_term_non_pre,
                                    rpt disch_tac
                                    \\ DEP_REWRITE_TAC[cj 1 itree_semantics_DecCall_with_pre_ret_satisfy]
                                    \\ rpt strip_tac
                                    \\ rw[FUN_EQ_THM, lookup_code_def]
                                    \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def]
                                    \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                                    \\ gvs[]
                                    \\ qpat_x_assum ‘_ = FLOOKUP _ _’ $ assume_tac o GSYM
                                    \\ rw[])
      val code_tree_thm_non_pre = (UNDISCH_ALL tree_thm_non_pre)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> ASM_SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM]
  in
    CONJ code_tree_thm_non_pre code_tree_thm_with_pre
    end
*)

        
fun mk_deccall_pre_thm_with_argexps scode fundecs code_thm te =
  let val all_v_list = all_vars te
      val tree_ty = type_of te
      val tau_ty = mk_type ("fun", [tree_ty, tree_ty])
      val arb_tau = “Tau”
      val ty_match = match_type (type_of arb_tau) tau_ty
      val tau_term = (inst:(hol_type,hol_type) subst -> term -> term) ty_match arb_tau
      val (itc, [progst]) = te |> strip_comb
      val (_, [prog, state]) = progst |> strip_comb
      val (_, [rt, sh, fname, aexps_term, prog1]) = prog |> strip_comb
      val (aexps, aexp_type) = aexps_term |> dest_list                         
      val (_, [ty_arg]) = dest_type aexp_type
      val fpb = EVAL “funcname_params_list ^fundecs” |> concl |> rhs
      val fpb_l = fpb |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val (_, (varsh, _)) = List.find (fn (x, (_, _)) => term_eq x fname) fpb_l |> valOf
      val varname_shape_list = varsh |> dest_list |> fst |> map dest_pair
      val args = mk_var_from_shape_once all_v_list (map snd varname_shape_list) ty_arg
      val args_vars = map strip_val_struct args
      val args_term = mk_list (args, mk_type ("v", [ty_arg]))
      val prog_q = mk_var ("q", type_of prog)
      val eval_some_terms = ListPair.map (fn (x, y) => “eval ^state ^x = SOME ^y”) (aexps, args)
      val v_THE_list = ListPair.map (fn (x, y) => (strip_val_struct x, mk_eval_val_term x state y)) (args, aexps)
      val eval_some_exists_terms = ListPair.map (fn (x, y) => boolSyntax.mk_exists (strip_val_struct x, y)) (args, eval_some_terms)
      val var_count = length varname_shape_list
      val vname_list = list_mk_var_ty "vname" (args_vars@all_v_list) “:mlstring” var_count
      val shape_list = list_mk_var_ty "sh" (args_vars@vname_list@all_v_list) “:shape” var_count
      val var_shape_pair_list = map mk_pair (zip vname_list shape_list)
      val var_shape_pair_list_term = mk_list (var_shape_pair_list, mk_type("prod", [“:mlstring”, “:shape”]))
      val asm_flookup_term = “FLOOKUP ^scode ^fname = SOME (^var_shape_pair_list_term, ^prog_q)”
      val vname_list_term = mk_list (vname_list, “:mlstring”)
      val asm_all_distinct_term = “ALL_DISTINCT ^vname_list_term”
      val shape_eq_terms = ListPair.map (fn (sh, args) => “^sh = shape_of ^args ”) (shape_list, args)
      val vname_arg_list = ListPair.map mk_pair (vname_list, args)
      val vname_arg_list_term = mk_list (vname_arg_list, mk_type("prod", [“:mlstring”, mk_type ("v", [ty_arg])]))
      val asm_inner_term = list_mk_conj ([asm_flookup_term, asm_all_distinct_term]@shape_eq_terms@
                                                    [“ret_satisfy
                                                     (λx.
                                                        ∃r s'.
                                                          x = INR (SOME r,s') ∧
                                                          ∀retv.
                                                            r = Return retv ⇒
                                                            Pre_next (set_var ^rt retv (s' with locals := ^state.locals)))
                                                     (itree_semantics (^prog_q, ^state with locals := FEMPTY |++ ^vname_arg_list_term))”])
      val asm_let_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) asm_inner_term v_THE_list
      val exists_terms = prog_q::vname_list@shape_list
      val asm_exists_term = list_mk_exists (exists_terms, asm_let_term)
      val asm_all_term = list_mk_conj (“^state.code = ^scode”::eval_some_exists_terms@[asm_exists_term])
      val arg_inner_term =
      “let (vshapes,prog) = THE (FLOOKUP ^scode ^fname)
        in
          ^tau_term
          (^itc
            (prog,
             ^state with
              locals :=
             FEMPTY |++ ZIP (MAP FST vshapes,^args_term)) >>=
            (λres. itree_deccall_handler ^rt ^sh ^state res t))”
      val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) arg_inner_term v_THE_list
      val concl_term = mk_eq (te, concl_rhs_term)
      val goal_term = mk_imp (“(∀s. Pre_next s ⇒ ^itc (^prog1,s) = t s)”, mk_imp (asm_all_term, concl_term))
      val tree_thm = prove (goal_term,
                            rpt disch_tac
                            \\ DEP_REWRITE_TAC[cj 2 itree_semantics_DecCall_with_pre_ret_satisfy]
                            \\ rpt strip_tac
                            \\ rw[FUN_EQ_THM, lookup_code_def]
                            \\ FULL_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def])
      val code_tree_thm_with_pre = (UNDISCH_COMP_CONJUNCTS_ALL  tree_thm)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> ASM_SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM, exists_LET]
      val asm_term_non_pre = list_mk_conj ([asm_flookup_term, asm_all_distinct_term]@shape_eq_terms)
      val asm_exists_term_non_pre = list_mk_conj (“^state.code = ^scode”::eval_some_exists_terms@[list_mk_exists (exists_terms, asm_term_non_pre)])
      val goal_term_non_pre = mk_imp (“(∀s. ^itc (^prog1,s) = t s)”, mk_imp (asm_exists_term_non_pre, concl_term))
      val tree_thm_non_pre = prove (goal_term_non_pre,
                                    rpt disch_tac
                                    \\ DEP_REWRITE_TAC[cj 1 itree_semantics_DecCall_with_pre_ret_satisfy]
                                    \\ rpt strip_tac
                                    \\ rw[FUN_EQ_THM, lookup_code_def]
                                    \\ FULL_CASE_TAC \\ gvs[word_of_val_def, struct_of_val_def, shape_of_def])
      val code_tree_thm_non_pre = (UNDISCH_COMP_CONJUNCTS_ALL  tree_thm_non_pre)
                                     |> Rules.FILTER_DISCH_ALL (fn x => not (can (match_term “∀_. _ ⇒ itree_semantics _ = _”) x))
                                     |> DISCH_ALL
                                     |> ASM_SIMP_RULE (srw_ss ()) (shape_of_def::pair_LET_pair::code_thm)
                                     |> DISCH_ALL
                                     |> eval_some_rw
                                     |> ASM_SIMP_RULE (srw_ss ()) [word_of_val_def, LET_ValWord, FUPDATE_LIST_THM, exists_LET]
  in
    CONJ code_tree_thm_non_pre code_tree_thm_with_pre
    end

        
fun inst_match_concl_lhs th trm_some =
  let val (_, [trm, res]) = trm_some |> strip_comb
  in
    if can (match_term “SOME (ValWord _)”) res orelse can (match_term “SOME (Struct _)”) res then
      let val thm_concl_lhs = th |> concl |> lhs
      in
        if can (match_term thm_concl_lhs) trm then
          let val (trm_inst, ty_inst) = match_term thm_concl_lhs trm
          in
            (INST:(term, term) subst -> thm -> thm) trm_inst ((INST_TYPE:(hol_type, hol_type) subst -> thm -> thm) ty_inst th)
          end
        else
          raise Domain
       end
    else
      raise Domain
  end
(*
val ascaxx = inst_match_concl_lhs (UNDISCH_ALL (cj 5 eval_eq_SOME_eval_to_let))
                                            “eval nst (Panop Mul [Var Local «i»; Const 8w]) = SOME (ValWord v)”
*)
        

fun inst_match_concl_lhs_in_list [] trm = raise Domain
  | inst_match_concl_lhs_in_list (th::ths) trm = inst_match_concl_lhs th trm
                                                                      handle _ => inst_match_concl_lhs_in_list ths trm

fun inst_match_concl_lhs_list_list ths [] = []
  | inst_match_concl_lhs_list_list ths (trm::trms) = inst_match_concl_lhs_in_list ths trm::inst_match_concl_lhs_list_list ths trms
                                                                                  handle _ => inst_match_concl_lhs_list_list ths trms

  
val teac = inst_match_concl_lhs_list_list (map UNDISCH_ALL (CONJUNCTS eval_eq_SOME_eval_to_let))
                                          [“eval s (Cmp Less (Var Local «i») (Var Local «len»)) = SOME (ValWord v)”] |> map DISCH_ALL


fun inst_match_concl_biim_lhs th trm_some =
  let val (_, [trm, res]) = trm_some |> strip_comb
  in
    if can (match_term “SOME (ValWord _)”) res orelse can (match_term “SOME (Struct _)”) res then
      let val thm_biim_lhs = th |> concl |> lhs |> boolSyntax.dest_exists |> snd |> lhs
      in
        if can (match_term thm_biim_lhs) trm then
          let val (trm_inst, ty_inst) = match_term thm_biim_lhs trm
          in
            (INST:(term, term) subst -> thm -> thm) trm_inst ((INST_TYPE:(hol_type, hol_type) subst -> thm -> thm) ty_inst th)
          end
        else
          raise Domain
       end
    else
      raise Domain
  end

(*
val asdcn = inst_match_concl_biim_lhs (cj 5 eval_eq_SOME_strip_eval)
                                 “eval nst (Panop Mul [Var Local «i»; Const 8w]) = SOME (ValWord v)”
*)

fun inst_match_concl_biim_lhs_in_list [] trm = raise Domain
  | inst_match_concl_biim_lhs_in_list (th::ths) trm = inst_match_concl_biim_lhs th trm
                                                                      handle _ => inst_match_concl_biim_lhs_in_list ths trm

fun inst_match_concl_biim_lhs_list_list ths [] = []
  | inst_match_concl_biim_lhs_list_list ths (trm::trms) =
    inst_match_concl_biim_lhs_in_list ths trm::inst_match_concl_biim_lhs_list_list ths trms
                                      handle _ => inst_match_concl_biim_lhs_list_list ths trms

(*
val asdcn = inst_match_concl_biim_lhs_list_list (CONJUNCTS eval_eq_SOME_strip_eval)
                                 [“eval nst (Panop Mul [Var Local «i»; Const 8w]) = SOME (ValWord v)”]
*)

fun mk_eval_word_op_exps trm_some =
  let val (_, [trm, res]) = trm_some |> strip_comb
  in
    if can (match_term “SOME (ValWord _)”) res then
      let val (eval_call, [state, op_exp]) = strip_comb trm
          val (op_call, [w_op, exps]) = strip_comb op_exp
          val exp_terms = dest_list exps |> fst
          val [ty_arg] = state |> type_of |> dest_type |> snd
          val w_ty = mk_type ("cart", [“:bool”, ty_arg])
          val v_list = list_mk_var_ty "v" [] w_ty (length exp_terms)                                               
          val eval_biimpl_list = map (fn x => “∃wv. eval ^state ^x = SOME (ValWord wv)”) exp_terms
          val eval_impl_hyps = “∃wv. ^trm = SOME (ValWord wv)”
          val v_op = if same_const w_op “Add” then inst [alpha |-> ty_arg] “word_add”
                     else if same_const w_op “And” then inst [alpha |-> ty_arg] “word_and”
                     else if same_const w_op “Xor” then inst [alpha |-> ty_arg] “word_xor”
                     else if same_const w_op “Or” then inst [alpha |-> ty_arg] “word_or”
                     else if same_const w_op “Sub” then inst [alpha |-> ty_arg] “word_sub”
                     else raise Domain
          val v_result = foldl (fn (v, accu_v) => “^v_op ^accu_v ^v”) (hd v_list) (tl v_list)
          val some_v_result = “SOME (ValWord ^v_result)”
          val word_of_exps = map (fn x => “word_of_val (THE (eval ^state ^x))”) exp_terms
          val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) some_v_result (zip v_list word_of_exps)
          val impl_goal = mk_imp (eval_impl_hyps, mk_eq (trm, concl_rhs_term))
          val biim_goal = mk_eq (eval_impl_hyps, list_mk_conj eval_biimpl_list)
          val biim_thm = prove (biim_goal, iff_tac
                                           \\ imp_res_tac eval_eq_SOME_strip_eval
                                           \\ gvs[word_of_val_def, pan_op_def, eval_def, word_op_def, asmTheory.word_cmp_def, word_lab_exists_word]
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def,
                                                                        word_op_def, asmTheory.word_cmp_def, word_lab_exists_word])
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def,
                                                                        word_op_def, asmTheory.word_cmp_def, word_lab_exists_word]))
          val impl_thm = prove (impl_goal, PURE_REWRITE_TAC[biim_thm]
                                           \\ rpt strip_tac
                                           \\ imp_res_tac eval_eq_SOME_eval_to_let
                                           \\ gvs[word_of_val_def, pan_op_def, eval_def, word_op_def, asmTheory.word_cmp_def, word_lab_exists_word]
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def,
                                                                        word_op_def, asmTheory.word_cmp_def, word_lab_exists_word])
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def,
                                                                        word_op_def, asmTheory.word_cmp_def, word_lab_exists_word]))
      in
        SOME (impl_thm, biim_thm)
        end
    else
      NONE
      end


fun mk_eval_let_exps_term trm_some =
  if can (match_term “eval _ (Op _ _) = SOME _”) trm_some then
    let val (_, [trm, res]) = trm_some |> strip_comb
    in
      if can (match_term “SOME (ValWord _)”) res then
        let val (eval_call, [state, op_exp]) = strip_comb trm
            val (op_call, [w_op, exps]) = strip_comb op_exp
            val exp_terms = dest_list exps |> fst
            val [ty_arg] = state |> type_of |> dest_type |> snd
            val w_ty = mk_type ("cart", [“:bool”, ty_arg])
            val v_list = list_mk_var_ty "v" [] w_ty (length exp_terms)                                               
            val eval_biimpl_list = map (fn x => “eval ^state ^x = SOME (ValWord wv)”) exp_terms
            val eval_impl_hyps = “∃wv. ^trm = SOME (ValWord wv)”
            val v_op = if same_const w_op “Add” then inst [alpha |-> ty_arg] “word_add”
                       else if same_const w_op “And” then inst [alpha |-> ty_arg] “word_and”
                       else if same_const w_op “Xor” then inst [alpha |-> ty_arg] “word_xor”
                       else if same_const w_op “Or” then inst [alpha |-> ty_arg] “word_or”
                       else if same_const w_op “Sub” then inst [alpha |-> ty_arg] “word_sub”
                       else raise Domain
            val v_result = foldl (fn (v, accu_v) => “^v_op ^accu_v ^v”) (hd v_list) (tl v_list)
            val some_v_result = “SOME (ValWord ^v_result)”
            val word_of_exps = map (fn x => “word_of_val (THE (eval ^state ^x))”) exp_terms
            val concl_rhs_term = foldr (fn ((x, v), t) => mk_let (mk_abs (x, t), v)) some_v_result (zip v_list word_of_exps)
            val let_eq_term = mk_eq (trm, concl_rhs_term)
        in
          SOME (let_eq_term, eval_biimpl_list)
               end
      else
        NONE
        end
  else
    SOME (concl (UNDISCH_ALL (inst_match_concl_lhs_in_list (map UNDISCH_ALL (CONJUNCTS eval_eq_SOME_eval_to_let)) trm_some)),
          rhs (concl (inst_match_concl_biim_lhs_in_list (map UNDISCH_ALL (CONJUNCTS eval_eq_SOME_strip_eval)) trm_some))
            |> boolSyntax.strip_conj
            |> map (fn x => if boolSyntax.is_exists x then (snd o boolSyntax.dest_exists) x else x))
         handle _ => NONE

fun eq_term_to_subst trm = (lhs trm) |-> (rhs trm)

fun mk_eval_let_exps_term_loop trm_some =
  let val eval_let_exps = mk_eval_let_exps_term trm_some
  in
    if isSome eval_let_exps then
      let val (let_term, inner_eval_some_terms) = valOf eval_let_exps
          val (eq_terms, leaf_terms) = ListPair.unzip (map mk_eval_let_exps_term_loop inner_eval_some_terms)
          val subst_term_list = map eq_term_to_subst $ List.concat eq_terms
      in
        ([subst subst_term_list let_term], List.concat leaf_terms)
        end
    else
      ([], [trm_some])
      end
      

fun mk_exists_rhs_var trm = list_mk_exists (all_vars (rhs trm), trm)
                                 

fun mk_eval_let_exps_thms exists_trm =
  let val trm_some = (snd o boolSyntax.dest_exists) exists_trm
      val (let_list, eval_list) = mk_eval_let_exps_term_loop trm_some
  in
    if null let_list then
      NONE
    else
      let val [let_term] = let_list
          val eval_term = boolSyntax.list_mk_conj (map (fn x => if can (match_term “eval _ _ = _”) x then mk_exists_rhs_var x else x) eval_list)
          val impl_goal = mk_imp (exists_trm, let_term)
          val biim_goal = mk_eq (exists_trm, eval_term)
          val biim_thm = prove (biim_goal, iff_tac
                                           \\ imp_res_tac eval_eq_SOME_strip_eval
                                           \\ rpt strip_tac
                                           \\ gvs[word_of_val_def, pan_op_def, eval_def, word_op_def, mem_load_byte_def,
                                                  word_of_Word_def, asmTheory.word_cmp_def, word_lab_exists_word, mem_load_def]
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def, mem_load_byte_def,
                                                                        word_of_Word_def, word_op_def, asmTheory.word_cmp_def,
                                                                        word_lab_exists_word, mem_load_def])
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def, mem_load_byte_def,
                                                                        word_of_Word_def, word_op_def, asmTheory.word_cmp_def,
                                                                        word_lab_exists_word, mem_load_def]))
          val impl_thm = prove (impl_goal, PURE_REWRITE_TAC[biim_thm]
                                           \\ rpt strip_tac
                                           \\ imp_res_tac eval_eq_SOME_eval_to_let
                                           \\ gvs[word_of_val_def, pan_op_def, eval_def, word_op_def, mem_load_byte_def,
                                                  word_of_Word_def, asmTheory.word_cmp_def, word_lab_exists_word, mem_load_def]
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def, mem_load_byte_def,
                                                                        word_of_Word_def, word_op_def, asmTheory.word_cmp_def,
                                                                        word_lab_exists_word, mem_load_def])
                                           \\ rpt (FULL_CASE_TAC \\ gvs[word_of_val_def, pan_op_def, eval_def, mem_load_byte_def,
                                                                        word_of_Word_def, word_op_def, asmTheory.word_cmp_def,
                                                                        word_lab_exists_word, mem_load_def]))
      in
        SOME (impl_thm, biim_thm)
      end
  end

                                              
(*
Theorem asc:
  (∃wv.
     eval
     (s with
        locals :=
      FEMPTY |+ («queue_handle»,ValWord w) |+ («data_region»,ValWord 0w))
     (Op Add [Var Local «queue_handle»; Panop Mul [Const 2w; BytesInWord]]) =
     SOME (ValWord wv)) ⇒
  eval
  (s with
     locals :=
   FEMPTY |+ («queue_handle»,ValWord w) |+ («data_region»,ValWord 0w))
  (Op Add [Var Local «queue_handle»; Panop Mul [Const 2w; BytesInWord]]) =
  (let
     v =
     word_of_val
     (THE
      (eval
       (s with
          locals :=
        FEMPTY |+ («queue_handle»,ValWord w) |+
               («data_region»,ValWord 0w)) (Var Local «queue_handle»)));
     v' =
     word_of_val
     (THE
      (eval
       (s with
          locals :=
        FEMPTY |+ («queue_handle»,ValWord w) |+
               («data_region»,ValWord 0w))
       (Panop Mul [Const 2w; BytesInWord])))
   in
     SOME (ValWord (v + v')))
Proof
  rpt strip_tac
  \\ gvs[eval_def, word_op_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, eval_def, pan_op_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, eval_def, pan_op_def]
QED
*)

fun match_trm_in_exists pat_tm exists_tm = boolSyntax.is_exists exists_tm andalso
                                                 can (match_term pat_tm) (snd (boolSyntax.dest_exists exists_tm))

fun map_opt f [] = []
  | map_opt f (x::xs) = case f x of
                          SOME v => v::map_opt f xs
                        | NONE => map_opt f xs



                        
fun eval_simp_with_hyp_bu th =
  let val th_only_eval_hyp = th |> SPEC_ALL
                                |> UNDISCH_ALL
                                |> Rules.FILTER_DISCH_ALL (not o (match_trm_in_exists “eval _ _ = SOME _”))
      val eval_hyps = hyp th_only_eval_hyp
      val eval_word_op_hyp = filter (match_trm_in_exists “eval _ (Op _ _) = SOME _”) eval_hyps
      val eval_wop_hyp_trm = eval_word_op_hyp |> map (snd o boolSyntax.dest_exists)
      val eval_not_wop_hyp = filter (not o (match_trm_in_exists “eval _ (Op _ _) = SOME _”)) eval_hyps
      val eval_hyp_exp = eval_not_wop_hyp |> map (snd o boolSyntax.dest_exists)
      val (wop_impls, wop_biim) = ListPair.unzip (map_opt mk_eval_word_op_exps eval_wop_hyp_trm)
      val wop_impls_with_hyp = wop_impls |> map UNDISCH_ALL
      val impl_thms = (inst_match_concl_lhs_list_list (map UNDISCH_ALL (CONJUNCTS eval_eq_SOME_eval_to_let)) eval_hyp_exp)
                      @wop_impls_with_hyp
      val _ = if length impl_thms = 0 then raise Domain else "simplifying"
      val biim_thms = (inst_match_concl_biim_lhs_list_list (map UNDISCH_ALL (CONJUNCTS eval_eq_SOME_strip_eval)) eval_hyp_exp)@wop_biim
      val simpler_evals_th = th_only_eval_hyp
                               |> PURE_REWRITE_RULE impl_thms
                               |> DISCH_ALL
                               |> PURE_REWRITE_RULE biim_thms
                               |> UNDISCH_CONJUNCTS_ALL
  in
    simpler_evals_th
    end

fun eval_simp_with_hyp_bu_rpt th = eval_simp_with_hyp_bu_rpt (eval_simp_with_hyp_bu th
                                                          |> DISCH_ALL
                                                          |> SIMP_RULE (srw_ss ()) [eval_simps]
                                                          |> UNDISCH_CONJUNCTS_ALL)
                                                       handle _ => th


       
fun eval_simp_with_hyp_rpt th =
  let val th_only_eval_hyp = th |> SPEC_ALL
                                |> UNDISCH_ALL
                                |> Rules.FILTER_DISCH_ALL (not o (match_trm_in_exists “eval _ _ = SOME _”))
      val eval_hyps = hyp th_only_eval_hyp
      val simp_options = map mk_eval_let_exps_thms eval_hyps
      val (impl_thms, biim_thms) = foldl (fn (z, (x, y)) => if isSome z then ((fst (valOf z))::x, (snd (valOf z))::y) else (x, y)) ([], []) simp_options
      val simpler_evals_th = th_only_eval_hyp
                               |> PURE_REWRITE_RULE (map UNDISCH_ALL impl_thms)
                               |> DISCH_ALL
                               |> PURE_REWRITE_RULE biim_thms
                               |> UNDISCH_CONJUNCTS_ALL
  in
    simpler_evals_th
    end




fun funcname_bodies_list fundecs = EVAL “funcname_bodies ^fundecs” |> concl |> rhs |> dest_list |> fst |> map dest_pair


fun topdecs_to_fundecs topdecs =
  let val fun_topdecs = EVAL “FILTER is_func ^topdecs” |> concl |> rhs
      val fundecs = EVAL “MAP dest_func ^fun_topdecs” |> concl |> rhs
  in
    fundecs
  end


    
fun codes_lookup_funcs_assms fname fundecs =
  let val funcnames_list = funcname_bodies_list fundecs |> map fst
      val file_code_decs = EVAL “file_code ^fundecs” |> concl |> rhs
      val codes_name_str = concat [fname, "_codes"]
      val codes_name = mk_var(codes_name_str, type_of “file_code ^fundecs”)
      val codes_abbr_def = Define $ single $ ANTIQUOTE $ mk_eq(codes_name, file_code_decs)
      val codes_abbr = codes_abbr_def |> concl |> lhs
  in
    (codes_abbr_def, map (fn x => EVAL “FLOOKUP ^codes_abbr ^x”) funcnames_list)
  end

    
fun mlstring_term_to_string mlt =
  let val mlstring_chrlist = mlt |> term_to_string |> explode
      val mlstring_clean_chrlist = filter (fn x => not (mem x [#"\194", #"\171", #"\187"])) mlstring_chrlist
  in
    implode mlstring_clean_chrlist
  end

fun mk_prog_abbr_def fty fname body =
  let val func_abbr_str = concat [fname, "_", fty]
      val itree_body = “itree_semantics (^body, s)”
      val state = itree_body |> rand |> rand
      val func_abbr_ty = (type_of state) --> (type_of itree_body)
      val func_abbr_var = mk_var(func_abbr_str, func_abbr_ty)
      val func_abbr_with_state = mk_comb (func_abbr_var, state)
      val abbr_thm = zDefine $ single $ ANTIQUOTE $ mk_eq(func_abbr_with_state, itree_body)
  in
    abbr_thm
  end

fun code_func_mk_abbr funcname_bodies =
  map (fn x => mk_prog_abbr_def "body" (mlstring_term_to_string (fst x)) (snd x)) funcname_bodies


fun no_assms_thm th =
  if is_forall (concl th) then
    false
  else
    null $ hyp th
           
(*
fun decompile_pure_once_rule_loop_with_assms rule body_def name_def extra_assms scode code_thms prog_tree =
  let val prog = prog_tree |> rand |> rator |> rand
      val state = prog_tree |> rand |> rand
      val raw_assms = SIMP_CONV (srw_ss ()) [vesp_def, vesp_mem_load_def, pswfp_def] “pswfp ^prog ^state”
                        |> concl |> rhs
      val initialised_assms = (gvs([eval_def, vesp_word_op_def, vesp_pan_op_def, is_valid_value_wfp_def,
                                        mem_stores_wfp_def, word_op_def, flatten_def, shape_of_def, mem_load_def,
                                        pan_op_def, shape_of_eq_one_valword, FLOOKUP_SIMP, nb_op_def, lookup_kvar_valword_wfp_def,
                                        word_sh_def
                                       ]@code_thms))
                              ([(“^state.code = ^scode”), (“EVERY (λx. x) ^raw_assms”)]@extra_assms, “F”) |> fst |> hd |> fst
      val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM body_def)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM name_def)))
  in
    (lhs_name_rule o rhs_name_rule) (SIMP_CONV (srw_ss ()) ([Once rule,
                                                             mem_load_def,
                                                             word_sh_def, eval_def]
                                                            @code_thms
                                                             @(map ASSUME initialised_assms)
                                                              @(map ASSUME extra_assms)
                                                               @tree_simp_rules) prog_tree |> BETA_RULE) |> DISCH_ALL |> GEN_ALL
  end
*)
fun mk_abs_impl th avar =
  let val conj_impl = th |> SPEC_ALL |> UNDISCH_ALL |> hurdUtils.DISCH_CONJUNCTS_ALL
      val att = conj_impl |> concl |> rator |> rand
      val shal = conj_impl |> concl |> rand |> rhs
      val abs_att = mk_abs (avar, att)
      val abs_shal = mk_abs (avar, shal)
      val abs_att_thm = prove (“^att = ^abs_att ^avar”, BETA_TAC \\ REFL_TAC)
      val abs_shal_thm = prove (“^shal = ^abs_shal ^avar”, BETA_TAC \\ REFL_TAC)
  in
    PURE_REWRITE_RULE [Once abs_att_thm, Once abs_shal_thm] conj_impl |> GEN avar
  end

fun UNDISCH_CONJUNCTS_NON_ERR th = hurdUtils.UNDISCH_CONJUNCTS th
                                            handle _ => th
fun mk_abs_all_impl th avar =
  if null (hyp th) then
    mk_abs_impl (ADD_ASSUM “T” th) avar
  else
    mk_abs_impl th avar

fun mk_abs_rhs th avar =
  let val conj_impl = th |> SPEC_ALL
      val shal = conj_impl |> concl |> rhs
      val abs_shal = mk_abs (avar, shal)
      val abs_shal_thm = prove (“^shal = ^abs_shal ^avar”, BETA_TAC \\ REFL_TAC)
  in
    PURE_REWRITE_RULE [Once abs_shal_thm] conj_impl |> GEN avar
  end


  
(* test
fun decompile_body_no_sep_bu fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_abs = mk_abs_impl (mk_thm_pre true_thm) new_st
          val while_pre_thm = MATCH_MP (itree_semantics_While_with_pre_T) true_abs
                                |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
          val gen_st = while_pre_thm |> concl |> lhs |> rand |> rand
          val while_thm_sp = while_pre_thm |> DISCH_ALL
                                   |> GEN gen_st |> SPEC state
                                                 |> UNDISCH_ALL
          val while_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
      in
        ((curr_name_rule o rhs_name_rule)
         (QCONV (SIMP_CONV (srw_ss ())
                           ([while_thm,
                             mem_load_def,
                             word_sh_def]
                            @(map ASSUME extra_assms)
                             @tree_simp_rules)) prog_tree), true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^new_st)”
          val (false_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^new_st)”
          val true_abs = mk_abs_impl (mk_thm_pre true_thm) new_st
          val false_abs = mk_abs_impl (mk_thm_pre false_thm) new_st
          val cond_pre_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_T) true_abs) false_abs
                               |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
          val gen_st = cond_pre_thm |> concl |> lhs |> rand |> rand
          val cond_thm_sp = cond_pre_thm |> DISCH_ALL
                                   |> GEN gen_st |> SPEC state
                                                 |> UNDISCH_ALL
          val cond_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
      in
        ((curr_name_rule o rhs_name_rule)
         (QCONV (SIMP_CONV (srw_ss ())
                           ([cond_thm, true_thm, false_thm,
                             mem_load_def,
                             word_sh_def]
                            @(map ASSUME extra_assms)
                             @tree_simp_rules)) prog_tree), true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      ((curr_name_rule o rhs_name_rule) (QCONV (SIMP_CONV (srw_ss ())
                        ([itree_semantics_Skip]
                         @(map ASSUME extra_assms)
                          @tree_simp_rules)) prog_tree),
      [], [], false, n)
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      ((curr_name_rule o rhs_name_rule) (QCONV (SIMP_CONV (srw_ss ())
                        ([itree_semantics_Annot]
                         @(map ASSUME extra_assms)
                          @tree_simp_rules)) prog_tree),
      [], [], false, n)
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) assign_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      ((curr_name_rule o rhs_name_rule) (QCONV (SIMP_CONV (srw_ss ())
                        ([itree_semantics_Break]
                         @(map ASSUME extra_assms)
                          @tree_simp_rules)) prog_tree),
       [], [], false, n)
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      ((curr_name_rule o rhs_name_rule) (QCONV (SIMP_CONV (srw_ss ())
                        ([itree_semantics_Continue]
                         @(map ASSUME extra_assms)
                          @tree_simp_rules)) prog_tree),
       [], [], false, n)
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_red_with_pre prog_tree
      in
        ((curr_name_rule o rhs_name_rule) extcall_thm, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
      in
        ((curr_name_rule o rhs_name_rule) raise_thm, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) return_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) shmemload_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) shmemstore_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) store_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) store32_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
       in
         ((curr_name_rule o rhs_name_rule) storebyte_thm, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      (QCONV (SIMP_CONV (srw_ss ())
                        ([itree_semantics_Tick]
                         @(map ASSUME extra_assms)
                          @tree_simp_rules)) prog_tree,
       [], [], false, n)
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
      in
        if null (hyp inner1_thm) then
          let val tree_abs1 = mk_abs_rhs inner1_thm new_st
              val dec_thm = MATCH_MP (cj 1 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
          in
            ((curr_name_rule o rhs_name_rule)
             (QCONV (SIMP_CONV (srw_ss ()) ([dec_sp_all, FLOOKUP_SIMP]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree),
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        else  
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val dec_thm = MATCH_MP (cj 2 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
          in
            ((curr_name_rule o rhs_name_rule)
             (QCONV (SIMP_CONV (srw_ss ()) ([dec_sp_all, FLOOKUP_SIMP]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree),
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val cond_def = mk_prog_abbr_def (concat ["cond_", int_to_string n]) fname cond_call
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [cond_def] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
      in
        ((curr_name_rule o rhs_name_rule)
         (QCONV (SIMP_CONV (srw_ss ())
                           ([GSYM cond_def]
                            @(map ASSUME extra_assms)
                             @tree_simp_rules)) prog_tree),
         [cond_thm]@inner_cond_thms, [cond_def]@inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
      in
        ((curr_name_rule o rhs_name_rule)
         (QCONV (SIMP_CONV (srw_ss ())
                           ([GSYM while_def]
                            @(map ASSUME extra_assms)
                             @tree_simp_rules)) prog_tree),
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([Once itree_semantics_Seq, call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> DISCH_ALL
                           |> call_name_rule
                           |> UNDISCH_ALL
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
      in
        if null (hyp deccall_next_raw_thm) then
          let val next_tree_abs = mk_abs_rhs deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 1 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> UNDISCH_ALL
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        else
          let val next_tree_abs = mk_abs_impl deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> UNDISCH_ALL
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
          val (inner2_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
      in
        if null (hyp inner1_thm) then
          if null (hyp inner2_thm) then
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_rhs inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 1 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
            in
              ((curr_name_rule o rhs_name_rule)
               (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree),
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
          else
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_impl inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 2 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
            in
              ((curr_name_rule o rhs_name_rule)
               (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree),
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
        else if null (hyp inner2_thm) then
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_rhs inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 3 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                         |> GEN gen_st |> SPEC state
                                       |> UNDISCH_ALL
          in
            ((curr_name_rule o rhs_name_rule)
             (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree),
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        else
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_impl inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 4 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
          in
            ((curr_name_rule o rhs_name_rule)
             (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree),
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end

*)

(* test2
fun decompile_body_no_sep_bu fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_abs = mk_abs_impl (mk_thm_pre true_thm) new_st
          val while_pre_thm = MATCH_MP (itree_semantics_While_with_pre_T) true_abs
                                |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
          val gen_st = while_pre_thm |> concl |> lhs |> rand |> rand
          val while_thm_sp = while_pre_thm |> DISCH_ALL
                                   |> GEN gen_st |> SPEC state
                                                 |> UNDISCH_ALL
          val while_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val while_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([while_thm,
                                                  mem_load_def,
                                                  word_sh_def]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (while_shallow, true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^new_st)”
          val (false_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^new_st)”
          val true_abs = mk_abs_impl (mk_thm_pre true_thm) new_st
          val false_abs = mk_abs_impl (mk_thm_pre false_thm) new_st
          val cond_pre_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_T) true_abs) false_abs
                               |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
          val gen_st = cond_pre_thm |> concl |> lhs |> rand |> rand
          val cond_thm_sp = cond_pre_thm |> DISCH_ALL
                                   |> GEN gen_st |> SPEC state
                                                 |> UNDISCH_ALL
          val cond_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val cond_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([cond_thm, true_thm, false_thm,
                                                 mem_load_def,
                                                 word_sh_def]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> eval_simp_with_hyp_rpt
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (cond_shallow, true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      let val skip_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([itree_semantics_Skip]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> eval_simp_with_hyp_rpt
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (skip_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      let val annot_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([itree_semantics_Annot]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (annot_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
          val assign_shallow = (curr_name_rule o rhs_name_rule) assign_thm
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (assign_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      let val break_shallow = (curr_name_rule o rhs_name_rule)
                                              (QCONV (SIMP_CONV (srw_ss ())
                                                                ([itree_semantics_Break]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (break_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      let val continue_shallow = (curr_name_rule o rhs_name_rule)
                                 (QCONV (SIMP_CONV (srw_ss ())
                                                   ([itree_semantics_Continue]
                                                    @(map ASSUME extra_assms)
                                                     @tree_simp_rules)) prog_tree)
                                   |> eval_simp_with_hyp_rpt
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (continue_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_red_with_pre prog_tree
          val extcall_shallow = (curr_name_rule o rhs_name_rule) extcall_thm
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (extcall_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
          val raise_shallow = (curr_name_rule o rhs_name_rule) raise_thm
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (raise_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
          val return_shallow = (curr_name_rule o rhs_name_rule) return_thm
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (return_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
          val shmemload_shallow = (curr_name_rule o rhs_name_rule) shmemload_thm
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
       in
         (shmemload_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
          val shmemstore_shallow = (curr_name_rule o rhs_name_rule) shmemstore_thm
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
       in
         (shmemstore_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
          val store_shallow = (curr_name_rule o rhs_name_rule) store_thm
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
         (store_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
           val store32_shallow = (curr_name_rule o rhs_name_rule) store32_thm
                                   |> eval_simp_with_hyp_rpt
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
       in
         (store32_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
          val storebyte_shallow = (curr_name_rule o rhs_name_rule) storebyte_thm
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
       in
         (storebyte_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      let val tick_shallow = QCONV (SIMP_CONV (srw_ss ())
                                              ([itree_semantics_Tick]
                                               @(map ASSUME extra_assms)
                                                @tree_simp_rules)) prog_tree
      in
        (tick_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
      in
        if null (hyp inner1_thm) then
          let val tree_abs1 = mk_abs_rhs inner1_thm new_st
              val dec_thm = MATCH_MP (cj 1 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ()) ([dec_sp_all, FLOOKUP_SIMP]
                                                               @(map ASSUME extra_assms)
                                                                @tree_simp_rules)) prog_tree)
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        else  
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val dec_thm = MATCH_MP (cj 2 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ()) ([dec_sp_all, FLOOKUP_SIMP]
                                                               @(map ASSUME extra_assms)
                                                                @tree_simp_rules)) prog_tree)
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val cond_def = mk_prog_abbr_def (concat ["cond_", int_to_string n]) fname cond_call
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [cond_def] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
          val if_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([GSYM cond_def]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> eval_simp_with_hyp_rpt
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (if_shallow,
         [cond_thm]@inner_cond_thms, [cond_def]@inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
          val while_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([GSYM while_def]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> eval_simp_with_hyp_rpt
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (while_shallow,
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([Once itree_semantics_Seq, call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> DISCH_ALL
                           |> call_name_rule
                           |> UNDISCH_ALL
                           |> eval_simp_with_hyp_rpt
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
      in
        if null (hyp deccall_next_raw_thm) then
          let val next_tree_abs = mk_abs_rhs deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 1 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> UNDISCH_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        else
          let val next_tree_abs = mk_abs_impl deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> UNDISCH_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
          val (inner2_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
      in
        if null (hyp inner1_thm) then
          if null (hyp inner2_thm) then
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_rhs inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 1 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
          else
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_impl inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 2 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
        else if null (hyp inner2_thm) then
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_rhs inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 3 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                         |> GEN gen_st |> SPEC state
                                       |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        else
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_impl inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 4 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end
*)






fun eq_match_simp_rule simp_set extra_thms ori_thm mterm =
  let val (term_subst, ty_subst) = match_term (ori_thm |> UNDISCH_ALL |> concl |> lhs) mterm
      val matched_thm = INST term_subst (INST_TYPE ty_subst ori_thm)
  in
    PURE_ONCE_REWRITE_CONV ((UNDISCH_ALL matched_thm)::extra_thms) mterm
  end
(*
fun eq_match_simp_rule_bu simp_set extra_thms ori_thm mterm =
  let val (term_subst, ty_subst) = match_term (ori_thm |> UNDISCH_ALL |> concl |> lhs) mterm
      val matched_thm = INST term_subst (INST_TYPE ty_subst ori_thm)
  in
    matched_thm
  end
*)


 
fun hide_vis t =
  let val vis_terms = find_terms (can (match_term “Vis _ _”)) t
      val hide_vars = map (genvar o type_of) vis_terms
      val hide_vis_subst = ListPair.map (op |->) (vis_terms, hide_vars)
      val show_vis_subst = ListPair.map (op |->) (hide_vars, vis_terms)
  in
    (subst hide_vis_subst t, show_vis_subst)
    end

fun is_vis t = is_comb t andalso same_const “Vis” ((fst o strip_comb) t)

fun term_mem t [] = false
  | term_mem t (x::xs) = term_eq t x orelse term_mem t xs
    
fun safe_replace_recursive rec_call t =
  let val call_vars = all_vars rec_call
  in
    if is_vis t then
      (t, true)
    else if is_cond t then
      let val (b, tb, eb) = dest_cond t
          val (tb_r, tb_safe) = safe_replace_recursive rec_call tb
          val (eb_r, eb_safe) = safe_replace_recursive rec_call eb
      in
        (mk_cond (b, tb_r, eb_r), tb_safe andalso eb_safe)
      end
    else if is_let t then
      let val (abs_f, v_let) = dest_let t
      in
        if term_mem v_let call_vars then
          (t, false)
        else
          let val (abs_v, f) = dest_abs abs_f
              val (f_r, f_s) = safe_replace_recursive rec_call f
              val abs_f_r = mk_abs (abs_v, f_r)
          in
            (mk_let (abs_f_r, v_let), f_s)
          end
      end
    else if is_funpow t then
      let val (fpc, fpn, inner_t) = dest_funpow t
          val spin_raw = “spin”
          val spin_term = inst (match_type (type_of spin_raw) (type_of rec_call)) spin_raw
      in
        if can (match_term rec_call) inner_t then
          if term_eq inner_t rec_call then
            (spin_term, true)
          else
            (t, false)
        else if can (match_term “^rec_call >>= k”) inner_t then
          if term_eq ((rand o rator) inner_t) rec_call then
            (spin_term, true)
          else
            (t, false)
        else
          let val (inner_t_r, inner_t_s) = safe_replace_recursive rec_call inner_t
          in
            (mk_funpow (fpc, fpn, inner_t_r), inner_t_s)
          end
       end
    else if is_comb t andalso same_const ((fst o strip_comb) t) “itree_bind” then
      let val (itb, [lt, rt]) = strip_comb t
          val (lt_r, lt_s) = safe_replace_recursive rec_call lt
          val (rt_r, rt_s) = safe_replace_recursive rec_call rt
      in
        (list_mk_comb (itb, [lt_r, rt_r]), lt_s andalso rt_s)
        end
    else if is_abs t then
      let val (abs_v, inner_t) = dest_abs t
      in
        if term_mem abs_v call_vars then
          (t, false)
        else
          let val (inner_t_r, inner_t_s) = safe_replace_recursive rec_call inner_t
          in
            (mk_abs (abs_v, inner_t_r), inner_t_s)
            end
        end
    else
      (t, true)
  end

fun replace_non_sub_vis_spin_bu bisim_thm =
  let val bisim_term = bisim_thm |> concl
      val lhs_term = bisim_term |> lhs
      val rhs_term = bisim_term |> rhs
      val (rhs_hide_vis, show_vis_subst) = hide_vis rhs_term
      val spin_raw = “spin”
      val spin_term = inst (match_type (type_of spin_raw) (type_of lhs_term)) spin_raw
      val rhs_recursive_terms = find_terms (fn x => can (match_term “FUNPOW Tau _ (^lhs_term)”) x) rhs_hide_vis
      val (rhs_cyclic_terms, rhs_changed_terms) = partition ((term_eq lhs_term) o rand) rhs_recursive_terms
      val rhs_recursive_bind_terms = find_terms (fn x => can (match_term “FUNPOW Tau _ (^lhs_term >>= _)”) x) rhs_hide_vis
      val (rhs_cyclic_bind_terms, rhs_changed_bind_terms) = partition ((term_eq lhs_term) o (rand o rator)) rhs_recursive_bind_terms
      val rhs_replace_spin = subst (map (fn x => x |-> spin_term) (rhs_cyclic_terms@rhs_cyclic_bind_terms)) rhs_hide_vis
      val rhs_replace_spin_show_vis = subst show_vis_subst rhs_replace_spin
      val replace_thm = prove (mk_eq(bisim_term, mk_eq(lhs_term, rhs_replace_spin_show_vis)),
                               rw[GSYM FUNPOW_SUC, GSYM spin]
                               \\ rw[itree_bisim_FUNPOW_Tau_neq_zero_self_bind_spin,
                                  FUNPOW_Tau_neq_zero_cyclic_spin,
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “0:num”
                                                                  (GEN “n:num” itree_bisim_FUNPOW_Tau_SUC_self_bind_spin))),
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “(SUC 0):num”
                                                                  (GEN “n:num” itree_bisim_FUNPOW_Tau_SUC_self_bind_spin))),
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “0:num” (GEN “n:num” FUNPOW_Tau_SUC_cyclic_spin))),
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “(SUC 0):num” (GEN “n:num” FUNPOW_Tau_SUC_cyclic_spin)))])
  in
    (EQ_MP replace_thm bisim_thm, null (rhs_changed_terms@rhs_changed_bind_terms))
    end

fun replace_non_sub_vis_spin bisim_thm =
  let val bisim_term = bisim_thm |> concl
      val lhs_term = bisim_term |> lhs
      val rhs_term = bisim_term |> rhs
      val (rhs_replace_spin, safe) = safe_replace_recursive lhs_term rhs_term
      val replace_thm = prove (mk_eq(bisim_term, mk_eq(lhs_term, rhs_replace_spin)),
                               rw[GSYM FUNPOW_SUC, GSYM spin]
                               \\ rw[itree_bisim_FUNPOW_Tau_neq_zero_self_bind_spin,
                                  FUNPOW_Tau_neq_zero_cyclic_spin,
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “0:num”
                                                                  (GEN “n:num” itree_bisim_FUNPOW_Tau_SUC_self_bind_spin))),
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “(SUC 0):num”
                                                                  (GEN “n:num” itree_bisim_FUNPOW_Tau_SUC_self_bind_spin))),
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “0:num” (GEN “n:num” FUNPOW_Tau_SUC_cyclic_spin))),
                                  (SIMP_RULE (srw_ss ()) [] (SPEC “(SUC 0):num” (GEN “n:num” FUNPOW_Tau_SUC_cyclic_spin)))])
  in
    (EQ_MP replace_thm bisim_thm, safe)
    end




        
fun to_funpow_conv t =
  ((PURE_ONCE_REWRITE_CONV [GSYM FUNPOW_Tau_2]) THENC (PURE_REWRITE_CONV [GSYM (cj 2 FUNPOW)])) t

fun match_mp_until thm t =
  match_mp_until thm (MATCH_MP thm t)
                 handle _ => t


fun to_min_tau_conv t =
  let val t_funpow = to_funpow_conv t;
      val t_wb = MATCH_MP (GEN_ALL itree_eq_imp_wbisim) t_funpow;
      val t_min_tau = match_mp_until (GEN_ALL funpow_tau_conv_thm) t_wb;
      val t_new = PURE_REWRITE_RULE [FUNPOW_1] t_min_tau;
  in
    t_new
  end

fun to_min_tau_conv t =
  let val refl_t = REFL t;
      val t_wb = MATCH_MP (GEN_ALL itree_eq_imp_wbisim) refl_t;
      val t_min_tau = MATCH_MP (GEN_ALL tau_conv_thm) t_wb;
  in
    t_min_tau
  end

  
fun tau_ret_reduce_conv t =
  let val refl_t = REFL t;
      val t_wb = MATCH_MP (GEN_ALL itree_eq_imp_wbisim) refl_t;
      val t_min_tau = MATCH_MP (GEN_ALL tau_ret_conv_thm) t_wb;
  in
    t_min_tau
  end



fun tau_vis_reduce_conv t =
  let val refl_t = REFL t;
      val t_wb = MATCH_MP (GEN_ALL itree_eq_imp_wbisim) refl_t;
      val t_min_tau = MATCH_MP (GEN_ALL tau_vis_conv_thm) t_wb;
  in
    t_min_tau
  end




fun wbisim_cong_tactic thm_list (assms, concl) =
    let val lhs = concl |> rator |> rand;
        val rhs = concl |> rand;
        val lhs_func = lhs |> strip_comb |> fst;
        val rhs_func = rhs |> strip_comb |> fst;
    in
      if ((same_const “Tau” lhs_func) orelse (same_const “Tau” rhs_func)) then
        (rw([itree_wbisim_tau_eqn, UNCURRY_DEF]@thm_list)):(goal, thm) gentactic
      else if ((same_const “Vis” lhs_func) orelse (same_const “Vis” rhs_func)) then
        (rw([itree_wbisim_vis_vis, FUN_EQ_THM, REFL_CLAUSE, AND_CLAUSES]@thm_list)
         \\ rpt strip_tac \\ BETA_TAC \\ FULL_CASE_TAC):(goal, thm) gentactic
      else if ((same_const “option_CASE” lhs_func) andalso (same_const “option_CASE” rhs_func)) then
        irule option_CASE_wbisim_cong \\ rpt strip_tac \\  BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “v_CASE” lhs_func) andalso (same_const “v_CASE” rhs_func)) then
        irule v_CASE_wbisim_cong \\ rpt strip_tac \\ BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “sum_CASE” lhs_func) andalso (same_const “sum_CASE” rhs_func)) then
        irule sum_CASE_wbisim_cong \\ rpt strip_tac \\ BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “pair_CASE” lhs_func) andalso (same_const “pair_CASE” rhs_func)) then
        FULL_CASE_TAC \\ rpt strip_tac \\ BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “word_lab_CASE” lhs_func) andalso (same_const “word_lab_CASE” rhs_func)) then
        irule word_lab_case_wbisim_cong \\ rpt strip_tac \\ BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “COND” lhs_func) andalso (same_const “COND” rhs_func)) then
        irule COND_wbisim_cong \\ rpt strip_tac \\ BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “itree_bind” lhs_func) andalso (same_const “itree_bind” rhs_func)) then
        irule itree_bind_resp_wbisim \\ rpt strip_tac \\ BETA_TAC \\
        rw (itree_wbisim_refl::thm_list) \\ wbisim_cong_tactic thm_list
      else if ((same_const “UNCURRY” lhs_func) andalso (same_const “UNCURRY” rhs_func)) then
        rw (UNCURRY::FUN_EQ_THM::itree_wbisim_refl::thm_list) \\ BETA_TAC \\ wbisim_cong_tactic thm_list
      else if ((same_const “itree_deccall_handler” lhs_func) andalso (same_const “itree_deccall_handler” rhs_func)) then
        rw(itree_deccall_handler_def::thm_list)
      else if ((same_const “itree_call_handler” lhs_func) andalso (same_const “itree_call_handler” rhs_func)) then
        rw(itree_call_handler_def::thm_list)
      else if ((same_const “result_CASE” lhs_func) andalso (same_const “result_CASE” rhs_func)) then
        rw(FUN_EQ_THM::thm_list) \\ FULL_CASE_TAC \\ rw(FUN_EQ_THM::thm_list)
      else if is_abs lhs then
        rw (UNCURRY::FUN_EQ_THM::itree_wbisim_refl::thm_list) \\
        BETA_TAC \\ FULL_CASE_TAC \\ wbisim_cong_tactic thm_list
      else
        rw([itree_wbisim_refl, FUN_EQ_THM]@thm_list)
    end (assms, concl)


fun depth_abs_subst from to t =
  if is_comb t then
    if term_eq from t then
      to
    else
      let val (caller, callees) = strip_comb t;
      in
        list_mk_comb (caller, map (depth_abs_subst from to) callees)
      end
  else if is_abs t then
    let val (abs_vars, abs_term) = strip_abs t;
    in
      list_mk_abs (abs_vars, depth_abs_subst from to abs_term)
    end
  else
    t

fun once_reduce_tau_bu ext_thm thrm =
  let val rhs = thrm |> concl |> rand;
      val wbsim_call = thrm |> concl |> strip_comb |> fst;
      val tau_tau_term = find_term (can (match_term “Tau (Tau _)”)) rhs;
      val rep_thm = to_min_tau_conv tau_tau_term;
      val [from, to] = rep_thm |> concl |> strip_comb |> snd;
      val new_rhs = depth_abs_subst from to rhs;
      val wb_term = list_mk_comb (wbsim_call, [rhs, new_rhs]);
      val wb_thm = prove (wb_term, rpt (wbisim_cong_tactic (rep_thm::ext_thm@[LET_THM, word_of_val_def, struct_of_val_def, FUN_EQ_THM])));
      val conj_thm = CONJ thrm wb_thm;
  in
    if term_eq rhs new_rhs then
      raise Domain
    else  
      MATCH_MP itree_wbisim_trans conj_thm
  end

fun once_reduce_tau ext_thm thrm =
  let val rhs = thrm |> concl |> rand;
      val wbsim_call = thrm |> concl |> strip_comb |> fst;
      val tau_tau_term = find_term (can (match_term “Tau _”)) rhs;
      val rep_thm = to_min_tau_conv tau_tau_term;
      val [from, to] = rep_thm |> concl |> strip_comb |> snd;
      val new_rhs = depth_abs_subst from to rhs;
      val wb_term = list_mk_comb (wbsim_call, [rhs, new_rhs]);
      val wb_thm = prove (wb_term, rpt (wbisim_cong_tactic (rep_thm::ext_thm@[LET_THM, word_of_val_def, struct_of_val_def, FUN_EQ_THM])));
      val conj_thm = CONJ thrm wb_thm;
  in
    if term_eq rhs new_rhs then
      raise Domain
    else  
      MATCH_MP itree_wbisim_trans conj_thm
  end



fun reduce_tau extt thrm = reduce_tau extt (once_reduce_tau extt thrm)
                                      handle _ => thrm

 
fun once_reduce_tau_ret extt thrm =
  let val rhs = thrm |> concl |> rand;
      val wbsim_call = thrm |> concl |> strip_comb |> fst;
      val tau_ret_term = find_term (can (match_term “Tau (Ret _)”)) rhs;
      val rep_thm = tau_ret_reduce_conv tau_ret_term;
      val [from, to] = rep_thm |> concl |> strip_comb |> snd;
      val new_rhs = depth_abs_subst from to rhs; 
      val wb_term = list_mk_comb (wbsim_call, [rhs, new_rhs]);
      val wb_thm = prove (wb_term, rpt (wbisim_cong_tactic (rep_thm::extt@[LET_THM, word_of_val_def, struct_of_val_def, FUN_EQ_THM])));
      val conj_thm = CONJ thrm wb_thm;
  in
    if term_eq rhs new_rhs then
      raise Domain
    else
      MATCH_MP itree_wbisim_trans conj_thm
  end

fun reduce_tau_ret extt thrm = reduce_tau_ret extt (once_reduce_tau_ret extt thrm)
                                         handle _ => thrm


 
fun once_reduce_tau_vis extt thrm =
  let val rhs = thrm |> concl |> rand;
      val wbsim_call = thrm |> concl |> strip_comb |> fst;
      val tau_vis_term = find_term (can (match_term “Tau (Vis _ _)”)) rhs;
      val rep_thm = tau_vis_reduce_conv tau_vis_term;
      val [from, to] = rep_thm |> concl |> strip_comb |> snd;
      val new_rhs = depth_abs_subst from to rhs; 
      val wb_term = list_mk_comb (wbsim_call, [rhs, new_rhs]);
      val wb_thm = prove (wb_term, rpt (wbisim_cong_tactic (rep_thm::extt@[LET_THM, word_of_val_def, struct_of_val_def, FUN_EQ_THM])));
      val conj_thm = CONJ thrm wb_thm;
  in
    if term_eq rhs new_rhs then
      raise Domain
    else
      MATCH_MP itree_wbisim_trans conj_thm
  end

fun reduce_tau_vis extt thrm = reduce_tau_vis extt (once_reduce_tau_vis extt thrm)
                                              handle _ => thrm


fun reduce_to_view_singleton extt th =
  (GEN_ALL o DISCH_ALL o (reduce_tau_vis extt) o (reduce_tau_ret extt) o (reduce_tau extt))
  (th |> SPEC_ALL |> UNDISCH_ALL |>  MATCH_MP (GEN_ALL itree_eq_imp_wbisim))
  handle _ => th


fun deep_conj_app f th =
  if is_conj (concl th) then
    LIST_CONJ $ map f $ CONJUNCTS th
  else
    f th

fun reduce_to_view extt th = deep_conj_app (reduce_to_view_singleton extt) th



fun let_non_comb_rw_once th =
  let val let_terms = find_terms (can (match_term “LET _ _”)) (th |> concl)
      val let_n2w_terms = filter (fn x => ((not o is_comb) (rand x))) let_terms
      val let_rw_thms = map (QCONV (PURE_REWRITE_CONV [LET_THM])) let_n2w_terms
  in
    if null let_rw_thms then
      raise Domain
    else
      PURE_REWRITE_RULE let_rw_thms th
    end



fun let_non_comb_rw th = let_non_comb_rw (let_non_comb_rw_once th)
                               handle _ => th
    
fun let_n2w_rw_once th =
  let val let_terms = find_terms (can (match_term “LET _ _”)) (th |> concl)
      val let_n2w_terms = filter (fn x =>
                                    (is_comb (rand x))
                                    andalso ((same_const (rator (rand x)) “n2w”))) let_terms
      val let_rw_thms = map (QCONV (PURE_REWRITE_CONV [LET_THM])) let_n2w_terms
  in
    if null let_rw_thms then
      raise Domain
    else
      PURE_REWRITE_RULE let_rw_thms th
    end

fun let_n2w_rw_once_bu th =
  let val let_terms = find_terms (can (match_term “LET _ _”)) (th |> concl)
      val let_n2w_terms = filter (fn x =>
                                    (is_comb (rand x))
                                    andalso ((same_const (rator (rand x)) “n2w”)
                                             orelse ((not (same_const (rator (rand x)) “THE”))
                                                     andalso (not (same_const (rator (rand x)) “word_of_val”))
                                                     andalso (not (same_const (rator (rand x)) “struct_of_val”))))) let_terms
      val let_rw_thms = map (QCONV (PURE_REWRITE_CONV [LET_THM])) let_n2w_terms
  in
    if null let_rw_thms then
      raise Domain
    else
      SIMP_RULE (srw_ss ()) let_rw_thms th
    end


fun let_n2w_rw th = let_n2w_rw (let_n2w_rw_once th)
                               handle _ => th

    
fun safe_spin_wbisim_lifting gen_bisim_thm =
  let val bisim_thm = gen_bisim_thm |> SPEC_ALL
                                    |> UNDISCH_ALL
                                    |> PURE_REWRITE_RULE [GSYM FUNPOW_Tau_1, GSYM FUNPOW_ADD, GSYM ADD_SUC, GSYM SUC_ADD_SYM]
      val (spin_bisim_thm, safe) = replace_non_sub_vis_spin bisim_thm
  in
    if safe then
      spin_bisim_thm |> PURE_REWRITE_RULE [FUNPOW]
                     |> DISCH_ALL
                     |> GEN_ALL
                     |> reduce_to_view []
                     |> SIMP_RULE (srw_ss ()) ([FLOOKUP_SIMP, 
                                                GSYM res_var_list_def, res_var_list_thm]@tree_simp_rules)
    else
      spin_bisim_thm |> PURE_REWRITE_RULE [FUNPOW]
                     |> DISCH_ALL
                     |> GEN_ALL
                     |> SIMP_RULE (srw_ss ()) ([FLOOKUP_SIMP, 
                                                GSYM res_var_list_def, res_var_list_thm]@tree_simp_rules)
    end

        
fun conj_safe_spin_wbisim_lifting gen_bisim_thm =
  if is_conj (concl gen_bisim_thm) then
    LIST_CONJ (map safe_spin_wbisim_lifting (CONJUNCTS gen_bisim_thm))
  else
    safe_spin_wbisim_lifting gen_bisim_thm

        
(* test final
fun decompile_body_no_sep fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_abs = mk_abs_all_impl true_thm new_st
          val while_pre_pure_thm = MATCH_MP (itree_semantics_While_with_pre_conj) true_abs
          val while_pre_false_thm = cj 1 while_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val while_pre_true_thm = cj 2 while_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = while_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = while_pre_true_thm |> concl |> lhs |> rand |> rand
          val while_true_thm_sp = while_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_false_thm_sp = while_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_true_thm_sp prog_tree
          val while_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val while_true_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([while_true_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
                                     |> DISCH_ALL
                                     |> GEN_ALL
          val while_false_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([while_false_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eval_simp_with_hyp_rpt
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> eq_val_struct_eq_some_simp
                                      |> DISCH_ALL
                                      |> GEN_ALL
      in
        (CONJ while_false_shallow while_true_shallow, true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^new_st)”
          val (false_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^new_st)”
          val true_abs = mk_abs_all_impl true_thm new_st
          val false_abs = mk_abs_all_impl false_thm new_st
          val cond_pre_pure_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_conj) true_abs) false_abs
          val cond_pre_true_thm = cj 1 cond_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val cond_pre_false_thm = cj 2 cond_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = cond_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = cond_pre_true_thm |> concl |> lhs |> rand |> rand
          val cond_true_thm_sp = cond_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val cond_false_thm_sp = cond_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val cond_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_true_thm_sp prog_tree
          val cond_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val cond_true_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([cond_true_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
                                     |> DISCH_ALL
                                     |> GEN_ALL
          val cond_false_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([cond_false_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eval_simp_with_hyp_rpt
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> eq_val_struct_eq_some_simp
                                      |> DISCH_ALL
                                      |> GEN_ALL
      in
        (CONJ cond_true_shallow cond_false_shallow, true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      let val skip_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([itree_semantics_Skip]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> eq_val_struct_eq_some_simp
      in
        (skip_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      let val annot_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([itree_semantics_Annot]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (annot_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
          val assign_shallow = (curr_name_rule o rhs_name_rule) assign_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> DISCH_ALL
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
      in
        (assign_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      let val break_shallow = (curr_name_rule o rhs_name_rule)
                                              (QCONV (SIMP_CONV (srw_ss ())
                                                                ([itree_semantics_Break]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (break_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      let val continue_shallow = (curr_name_rule o rhs_name_rule)
                                 (QCONV (SIMP_CONV (srw_ss ())
                                                   ([itree_semantics_Continue]
                                                    @(map ASSUME extra_assms)
                                                     @tree_simp_rules)) prog_tree)
                                   |> DISCH_ALL
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                   |> DISCH_ALL
                                   |> UNDISCH_COMP_CONJUNCTS_ALL
                                   |> eval_simp_with_hyp_rpt
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                   |> eq_val_struct_eq_some_simp
      in
        (continue_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_with_pre prog_tree
          val extcall_shallow = (curr_name_rule o rhs_name_rule) extcall_thm
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
      in
        (extcall_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
          val raise_shallow = (curr_name_rule o rhs_name_rule) raise_thm
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (raise_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
          val return_shallow = (curr_name_rule o rhs_name_rule) return_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> DISCH_ALL
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
      in
        (return_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
          val shmemload_shallow = (curr_name_rule o rhs_name_rule) shmemload_thm
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> DISCH_ALL
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> eq_val_struct_eq_some_simp
       in
         (shmemload_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
          val shmemstore_shallow = (curr_name_rule o rhs_name_rule) shmemstore_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (shmemstore_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
          val store_shallow = (curr_name_rule o rhs_name_rule) store_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
      in
         (store_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
           val store32_shallow = (curr_name_rule o rhs_name_rule) store32_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (store32_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
          val storebyte_shallow = (curr_name_rule o rhs_name_rule) storebyte_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (storebyte_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      let val tick_shallow = QCONV (SIMP_CONV (srw_ss ())
                                              ([itree_semantics_Tick]
                                               @(map ASSUME extra_assms)
                                                @tree_simp_rules)) prog_tree
      in
        (tick_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
                                                         val _ = print $ "\ndec_inner_start\n"
                                                         val _ = print $ term_to_string prog1
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
                                                         val _ = print $ "\ndec_inner_end\n"
      in
        if null (hyp inner1_thm) then
          let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                                                         val _ = print "\ndec_post1_start\n"
              val dec_thm = MATCH_MP (cj 1 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ()) ([dec_sp_all, FLOOKUP_SIMP]
                                                               @(map ASSUME extra_assms)
                                                                @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
                                                         val _ = print "\ndec_post1_end\n"
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        else  
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
                                                         val _ = print "\ndec_post1_start\n"
              val dec_thm = MATCH_MP (cj 2 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ()) ([dec_sp_all, FLOOKUP_SIMP]
                                                               @(map ASSUME extra_assms)
                                                                @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
                                                         val _ = print "\ndec_post1_end\n"
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val cond_def = mk_prog_abbr_def (concat ["cond_", int_to_string n]) fname cond_call
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [cond_def] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
          val if_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([GSYM cond_def]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL
                             |> eval_simp_with_hyp_rpt
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> eq_val_struct_eq_some_simp
      in
        (if_shallow,
         [cond_thm]@inner_cond_thms, [cond_def]@inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
          val while_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([GSYM while_def]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (while_shallow,
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = CONV_RULE (QCONV (RHS_CONV (PURE_REWRITE_CONV (map GSYM (rhs_names@lhs_names)))))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
                                            |> call_name_rule
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> DISCH_ALL
                           |> DISCH_ALL
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eval_simp_with_hyp_rpt
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> eq_val_struct_eq_some_simp
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
      in
        if null (hyp deccall_next_raw_thm) then
          let val next_tree_abs = mk_abs_rhs deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 1 deccall_raw_thm) next_tree_abs
                                      |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        else
          let val next_tree_abs = mk_abs_impl deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
                                                         val _ = print "\nseq_start1\n"
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
                                                         val _ = print "\nseq_start1_in1\n"
                                                         val _ = print $ term_to_string tree1
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
                                                         val _ = print "\nseq_start1_in2\n"
                                                         val _ = print $ term_to_string tree2
          val (inner2_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
                                                         val _ = print "\nseq_startend\n"
      in
        if null (hyp inner1_thm) then
          if null (hyp inner2_thm) then
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_rhs inner2_thm new_st
                                                         val _ = print "\nseq_post1_start\n"
                val seq_thm = MATCH_MP (MATCH_MP (cj 1 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL 
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> eq_val_struct_eq_some_simp
                                                         val _ = print "\nseq_post1_end\n"
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
          else
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_impl inner2_thm new_st
                                                         val _ = print "\nseq_post1_start\n"
                val seq_thm = MATCH_MP (MATCH_MP (cj 2 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL 
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> eq_val_struct_eq_some_simp
                                                         val _ = print "\nseq_post1_end\n"
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
        else if null (hyp inner2_thm) then
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_rhs inner2_thm new_st
                                                         val _ = print "\nseq_post1_start\n"
              val seq_thm = MATCH_MP (MATCH_MP (cj 3 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                         |> GEN gen_st |> SPEC state
                                       |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
                                                         val _ = print "\nseq_post1_end\n"
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        else
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_impl inner2_thm new_st
                                                         val _ = print "\nseq_post1_start\n"
              val seq_thm = MATCH_MP (MATCH_MP (cj 4 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (SIMP_CONV (srw_ss ()) ([seq_thm_sp, FLOOKUP_SIMP]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> UNDISCH_COMP_CONJUNCTS_ALL 
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
                                                         val _ = print "\nseq_post1_end\n"
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end

(* test final *)
fun decompile_body_no_sep fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_abs = mk_abs_all_impl true_thm new_st
          val while_pre_pure_thm = MATCH_MP (itree_semantics_While_with_pre_conj) true_abs
          val while_pre_false_thm = cj 1 while_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val while_pre_true_thm = cj 2 while_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = while_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = while_pre_true_thm |> concl |> lhs |> rand |> rand
          val while_true_thm_sp = while_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_false_thm_sp = while_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_true_thm_sp prog_tree
          val while_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val while_true_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([while_true_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
                                     |> DISCH_ALL
                                     |> GEN_ALL
          val while_false_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([while_false_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eval_simp_with_hyp_rpt
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> eq_val_struct_eq_some_simp
                                      |> DISCH_ALL
                                      |> GEN_ALL
      in
        (CONJ while_false_shallow while_true_shallow, true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^new_st)”
          val (false_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^new_st)”
          val true_abs = mk_abs_all_impl true_thm new_st
          val false_abs = mk_abs_all_impl false_thm new_st
          val cond_pre_pure_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_conj) true_abs) false_abs
          val cond_pre_true_thm = cj 1 cond_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val cond_pre_false_thm = cj 2 cond_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = cond_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = cond_pre_true_thm |> concl |> lhs |> rand |> rand
          val cond_true_thm_sp = cond_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val cond_false_thm_sp = cond_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val cond_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_true_thm_sp prog_tree
          val cond_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val cond_true_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([cond_true_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
                                     |> DISCH_ALL
                                     |> GEN_ALL
          val cond_false_shallow = (curr_name_rule o rhs_name_rule)
                                   (QCONV (SIMP_CONV (srw_ss ())
                                                     ([cond_false_thm,
                                                       mem_load_def,
                                                       word_sh_def]
                                                      @(map ASSUME extra_assms)
                                                       @tree_simp_rules)) prog_tree)
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eval_simp_with_hyp_rpt
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> eq_val_struct_eq_some_simp
                                      |> DISCH_ALL
                                      |> GEN_ALL
      in
        (CONJ cond_true_shallow cond_false_shallow, true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      let val skip_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([itree_semantics_Skip]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> eq_val_struct_eq_some_simp
      in
        (skip_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      let val annot_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([itree_semantics_Annot]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (annot_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
          val assign_shallow = (curr_name_rule o rhs_name_rule) assign_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> DISCH_ALL
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
      in
        (assign_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      let val break_shallow = (curr_name_rule o rhs_name_rule)
                                              (QCONV (SIMP_CONV (srw_ss ())
                                                                ([itree_semantics_Break]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (break_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      let val continue_shallow = (curr_name_rule o rhs_name_rule)
                                 (QCONV (SIMP_CONV (srw_ss ())
                                                   ([itree_semantics_Continue]
                                                    @(map ASSUME extra_assms)
                                                     @tree_simp_rules)) prog_tree)
                                   |> DISCH_ALL
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                   |> DISCH_ALL
                                   |> UNDISCH_COMP_CONJUNCTS_ALL
                                   |> eval_simp_with_hyp_rpt
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                   |> eq_val_struct_eq_some_simp
      in
        (continue_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_with_pre prog_tree
          val extcall_shallow = (curr_name_rule o rhs_name_rule) extcall_thm
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
      in
        (extcall_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
          val raise_shallow = (curr_name_rule o rhs_name_rule) raise_thm
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (raise_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
          val return_shallow = (curr_name_rule o rhs_name_rule) return_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> DISCH_ALL
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
      in
        (return_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
          val shmemload_shallow = (curr_name_rule o rhs_name_rule) shmemload_thm
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> DISCH_ALL
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> eq_val_struct_eq_some_simp
       in
         (shmemload_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
          val shmemstore_shallow = (curr_name_rule o rhs_name_rule) shmemstore_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (shmemstore_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
          val store_shallow = (curr_name_rule o rhs_name_rule) store_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
      in
         (store_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
           val store32_shallow = (curr_name_rule o rhs_name_rule) store32_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (store32_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
          val storebyte_shallow = (curr_name_rule o rhs_name_rule) storebyte_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (storebyte_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      let val tick_shallow = QCONV (SIMP_CONV (srw_ss ())
                                              ([itree_semantics_Tick]
                                               @(map ASSUME extra_assms)
                                                @tree_simp_rules)) prog_tree
      in
        (tick_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
      in
        if null (hyp inner1_thm) then
          let val tree_abs1 = mk_abs_rhs inner1_thm new_st
              val dec_thm = MATCH_MP (cj 1 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (PURE_REWRITE_CONV [dec_sp_all]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        else  
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val dec_thm = MATCH_MP (cj 2 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (PURE_REWRITE_CONV [dec_sp_all]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val cond_def = mk_prog_abbr_def (concat ["cond_", int_to_string n]) fname cond_call
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [cond_def] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
          val if_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([GSYM cond_def]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL
                             |> eval_simp_with_hyp_rpt
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> eq_val_struct_eq_some_simp
      in
        (if_shallow,
         [cond_thm]@inner_cond_thms, [cond_def]@inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
          val while_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([GSYM while_def]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (while_shallow,
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = CONV_RULE (QCONV (RHS_CONV (PURE_REWRITE_CONV (map GSYM (rhs_names@lhs_names)))))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
                                            |> call_name_rule
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> DISCH_ALL
                           |> DISCH_ALL
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eval_simp_with_hyp_rpt
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> eq_val_struct_eq_some_simp
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
      in
        if null (hyp deccall_next_raw_thm) then
          let val next_tree_abs = mk_abs_rhs deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 1 deccall_raw_thm) next_tree_abs
                                      |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        else
          let val next_tree_abs = mk_abs_impl deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
          val (inner2_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
      in
        if null (hyp inner1_thm) then
          if null (hyp inner2_thm) then
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_rhs inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 1 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
          else
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_impl inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 2 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL 
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
        else if null (hyp inner2_thm) then
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_rhs inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 3 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                         |> GEN gen_st |> SPEC state
                                       |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eq_val_struct_eq_some_simp
                                  |> eval_simp_with_hyp_rpt
                                  |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        else
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_impl inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 4 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eq_val_struct_eq_some_simp
                                  |> eval_simp_with_hyp_rpt
                                  |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end
*)


    


fun inst_exists_term_impl_lhs_th th trm =
  let val exists_trm = th |> concl |> rator |> rand
      val (trm_subst, ty_subst) = match_term exists_trm trm
  in
    (INST:(term, term) subst -> thm -> thm) trm_subst ((INST_TYPE:(hol_type, hol_type) subst -> thm -> thm) ty_subst th)
    end

fun inst_exists_term_impl_lhs_list_th [] trm = []
  | inst_exists_term_impl_lhs_list_th (th::ths) trm =
    inst_exists_term_impl_lhs_th th trm::inst_exists_term_impl_lhs_list_th ths trm
                                 handle _ => inst_exists_term_impl_lhs_list_th ths trm

(*  
val ascacs = inst_exists_term_impl_lhs_list_th (CONJUNCTS exists_val_struct_weakening)
                                               “(∃v2. FLOOKUP s.locals «i» = SOME (ValWord v2))”
*)

fun eq_val_struct_eq_some_simp th =
  let val filtered_th = th |> SPEC_ALL
                           |> UNDISCH_ALL
                           |> Rules.FILTER_DISCH_ALL
                                   (fn x => not (boolSyntax.is_exists x andalso
                                                           (fn t => can (match_term (“_ = SOME (ValWord _)”)) t
                                                                        orelse can (match_term (“_ = SOME (Struct _)”)) t)
                                                           (snd (boolSyntax.dest_exists x))))
      val simp_rules = map UNDISCH_ALL (flatten (map (inst_exists_term_impl_lhs_list_th
                                                      (CONJUNCTS exists_val_struct_weakening)) (hyp filtered_th)))
  in
    PURE_REWRITE_RULE simp_rules filtered_th
      |> DISCH_ALL
      |> SIMP_RULE (srw_ss ()) tree_simp_rules
      |> UNDISCH_ALL
    end


(*
                                
(* test final cond *)
fun decompile_body_no_sep fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_abs = mk_abs_all_impl true_thm new_st
          val while_pre_pure_thm = MATCH_MP (itree_semantics_While_with_pre_conj) true_abs
          val while_pre_false_thm = cj 1 while_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val while_pre_true_thm = cj 2 while_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = while_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = while_pre_true_thm |> concl |> lhs |> rand |> rand
          val while_true_thm_sp = while_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_false_thm_sp = while_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_true_thm_sp prog_tree
          val while_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val while_true_shallow = ((curr_name_rule o rhs_name_rule)
                                    while_true_thm
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eval_simp_with_hyp_rpt
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> eq_val_struct_eq_some_simp
                                      |> DISCH_ALL
                                      |> GEN_ALL)
          val while_false_shallow = ((curr_name_rule o rhs_name_rule)
                                     while_false_thm
                                       |> DISCH_ALL
                                       |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                       |> UNDISCH_COMP_CONJUNCTS_ALL
                                       |> eval_simp_with_hyp_rpt
                                       |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                       |> eq_val_struct_eq_some_simp
                                       |> DISCH_ALL
                                       |> GEN_ALL)
      in
        (CONJ while_false_shallow while_true_shallow, true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val st = mk_var ("s", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^state)”
          val (false_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^state)”
          val true_thm_simp =  true_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
                                 |> UNDISCH_ALL
          val false_thm_simp =  false_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
                                 |> UNDISCH_ALL
          val true_abs = mk_abs_all_impl true_thm_simp st
          val false_abs = mk_abs_all_impl false_thm_simp st
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val cond_pure_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_T) true_abs) false_abs
                                       |> UNDISCH_ALL
          val cond_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_pure_thm prog_tree
                           |> UNDISCH_ALL
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eq_val_struct_eq_some_simp
                           |> eval_simp_with_hyp_rpt
                           |> eq_val_struct_eq_some_simp
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> GEN_ALL
      in
        (cond_thm, true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      let val skip_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([itree_semantics_Skip]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> eq_val_struct_eq_some_simp
      in
        (skip_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      let val annot_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([itree_semantics_Annot]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (annot_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
          val assign_shallow = (curr_name_rule o rhs_name_rule) assign_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> DISCH_ALL
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
      in
        (assign_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      let val break_shallow = (curr_name_rule o rhs_name_rule)
                                              (QCONV (SIMP_CONV (srw_ss ())
                                                                ([itree_semantics_Break]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (break_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      let val continue_shallow = (curr_name_rule o rhs_name_rule)
                                 (QCONV (SIMP_CONV (srw_ss ())
                                                   ([itree_semantics_Continue]
                                                    @(map ASSUME extra_assms)
                                                     @tree_simp_rules)) prog_tree)
                                   |> DISCH_ALL
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                   |> DISCH_ALL
                                   |> UNDISCH_COMP_CONJUNCTS_ALL
                                   |> eval_simp_with_hyp_rpt
                                   |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                   |> eq_val_struct_eq_some_simp
      in
        (continue_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_with_pre prog_tree
          val extcall_shallow = (curr_name_rule o rhs_name_rule) extcall_thm
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
      in
        (extcall_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
          val raise_shallow = (curr_name_rule o rhs_name_rule) raise_thm
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (raise_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
          val return_shallow = (curr_name_rule o rhs_name_rule) return_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> DISCH_ALL
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> eq_val_struct_eq_some_simp
      in
        (return_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
          val shmemload_shallow = (curr_name_rule o rhs_name_rule) shmemload_thm
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> DISCH_ALL
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eval_simp_with_hyp_rpt
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> eq_val_struct_eq_some_simp
       in
         (shmemload_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
          val shmemstore_shallow = (curr_name_rule o rhs_name_rule) shmemstore_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (shmemstore_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
          val store_shallow = (curr_name_rule o rhs_name_rule) store_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
      in
         (store_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
           val store32_shallow = (curr_name_rule o rhs_name_rule) store32_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (store32_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
          val storebyte_shallow = (curr_name_rule o rhs_name_rule) storebyte_thm
                                     |> DISCH_ALL
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> DISCH_ALL
                                     |> UNDISCH_COMP_CONJUNCTS_ALL
                                     |> eval_simp_with_hyp_rpt
                                     |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                     |> eq_val_struct_eq_some_simp
       in
         (storebyte_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      let val tick_shallow = QCONV (SIMP_CONV (srw_ss ())
                                              ([itree_semantics_Tick]
                                               @(map ASSUME extra_assms)
                                                @tree_simp_rules)) prog_tree
      in
        (tick_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
      in
        if null (hyp inner1_thm) then
          let val tree_abs1 = mk_abs_rhs inner1_thm new_st
              val dec_thm = MATCH_MP (cj 1 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (PURE_REWRITE_CONV [dec_sp_all]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        else  
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val dec_thm = MATCH_MP (cj 2 itree_semantics_Dec_with_pre_let) tree_abs1
                              |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
              val gen_st = dec_thm |> concl |> lhs |> rand |> rand
              val dec_thm_sp = dec_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
              val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
              val dec_shallow = (curr_name_rule o rhs_name_rule)
                                (QCONV (PURE_REWRITE_CONV [dec_sp_all]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
          in
            (dec_shallow,
             inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
          val spec_cond_thm = SPEC state cond_thm
                               |> UNDISCH_CONJUNCTS_ALL
          val if_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([spec_cond_thm]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL
                             |> eval_simp_with_hyp_rpt
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> eq_val_struct_eq_some_simp
      in
        (if_shallow,
         inner_cond_thms, inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
          val while_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([GSYM while_def]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
      in
        (while_shallow,
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = CONV_RULE (QCONV (RHS_CONV (PURE_REWRITE_CONV (map GSYM (rhs_names@lhs_names)))))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
                                            |> call_name_rule
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> DISCH_ALL
                           |> DISCH_ALL
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eval_simp_with_hyp_rpt
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> eq_val_struct_eq_some_simp
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
      in
        if null (hyp deccall_next_raw_thm) then
          let val next_tree_abs = mk_abs_rhs deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 1 deccall_raw_thm) next_tree_abs
                                      |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        else
          let val next_tree_abs = mk_abs_impl deccall_next_raw_thm new_st
              val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                       |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val deccall_thm = (curr_name_rule o rhs_name_rule)
                                (QCONV (SIMP_CONV (srw_ss ())
                                                  ([deccall_gen_thm, FLOOKUP_SIMP]
                                                   @(map ASSUME extra_assms)
                                                    @tree_simp_rules)) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> DISCH_ALL
                                  |> call_name_rule
                                  |> DISCH_ALL
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eval_simp_with_hyp_rpt
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> eq_val_struct_eq_some_simp
          in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
          val (inner2_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
      in
        if null (hyp inner1_thm) then
          if null (hyp inner2_thm) then
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_rhs inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 1 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
          else
            let val tree_abs1 = mk_abs_rhs inner1_thm new_st
                val tree_abs2 = mk_abs_impl inner2_thm new_st
                val seq_thm = MATCH_MP (MATCH_MP (cj 2 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                                |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL 
                val gen_st = seq_thm |> concl |> lhs |> rand |> rand
                val seq_thm_sp = seq_thm |> DISCH_ALL
                                         |> GEN gen_st |> SPEC state
                                                       |> UNDISCH_ALL
                val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                    |> DISCH_ALL
                                    |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
                                    |> eval_simp_with_hyp_rpt
                                    |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
               inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
              end
        else if null (hyp inner2_thm) then
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_rhs inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 3 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                         |> GEN gen_st |> SPEC state
                                       |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eq_val_struct_eq_some_simp
                                  |> eval_simp_with_hyp_rpt
                                  |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        else
          let val tree_abs1 = mk_abs_impl inner1_thm new_st
              val tree_abs2 = mk_abs_impl inner2_thm new_st
              val seq_thm = MATCH_MP (MATCH_MP (cj 4 itree_semantics_Seq_ret_satisfy_pres) tree_abs1) tree_abs2
                              |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
              val gen_st = seq_thm |> concl |> lhs |> rand |> rand
              val seq_thm_sp = seq_thm |> DISCH_ALL
                                       |> GEN gen_st |> SPEC state
                                                     |> UNDISCH_ALL
              val seq_shallow = (curr_name_rule o rhs_name_rule)
                                  (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                  |> DISCH_ALL
                                  |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                  |> UNDISCH_COMP_CONJUNCTS_ALL
                                  |> eq_val_struct_eq_some_simp
                                  |> eval_simp_with_hyp_rpt
                                  |> eq_val_struct_eq_some_simp
            in
              (seq_shallow,
             inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
            end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end
*)
        
(* test final cond 2 *)
fun decompile_body_no_sep fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_abs = mk_abs_all_impl true_thm new_st
          val while_pre_pure_thm = MATCH_MP (itree_semantics_While_with_pre_conj) true_abs
          val while_pre_false_thm = cj 1 while_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val while_pre_true_thm = cj 2 while_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = while_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = while_pre_true_thm |> concl |> lhs |> rand |> rand
          val while_true_thm_sp = while_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_false_thm_sp = while_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
                                    |> eq_val_struct_eq_some_simp
          val while_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_true_thm_sp prog_tree
          val while_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val while_true_shallow = ((curr_name_rule o rhs_name_rule)
                                    while_true_thm
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eq_val_struct_eq_some_simp
                                      |> eval_simp_with_hyp_rpt
                                      |> DISCH_ALL
                                      |> GEN_ALL)
          val while_false_shallow = ((curr_name_rule o rhs_name_rule)
                                     while_false_thm
                                       |> DISCH_ALL
                                       |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                       |> UNDISCH_COMP_CONJUNCTS_ALL
                                       |> eq_val_struct_eq_some_simp
                                       |> eval_simp_with_hyp_rpt
                                       |> DISCH_ALL
                                       |> GEN_ALL)
      in
        (CONJ while_false_shallow while_true_shallow, true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val st = mk_var ("s", type_of state)
          val (true_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^state)”
          val (false_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^state)”
          val true_thm_simp =  true_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> eq_val_struct_eq_some_simp
                                 |> UNDISCH_ALL
          val false_thm_simp =  false_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> eval_simp_with_hyp_rpt
                                 |> eq_val_struct_eq_some_simp
                                 |> UNDISCH_ALL
          val true_abs = mk_abs_all_impl true_thm_simp st
          val false_abs = mk_abs_all_impl false_thm_simp st
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val cond_pure_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_T) true_abs) false_abs
                                       |> UNDISCH_ALL
          val cond_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_pure_thm prog_tree
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eq_val_struct_eq_some_simp
                           |> eval_simp_with_hyp_rpt
                           |> DISCH_ALL
                           |> GEN_ALL                          
      in
        (cond_thm, true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      let val skip_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([itree_semantics_Skip]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (skip_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      let val annot_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([itree_semantics_Annot]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (annot_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
          val assign_shallow = (curr_name_rule o rhs_name_rule) assign_thm
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL 
                                |> eval_simp_with_hyp_rpt
                                |> eq_val_struct_eq_some_simp
      in
        (assign_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      let val break_shallow = (curr_name_rule o rhs_name_rule)
                                              (QCONV (SIMP_CONV (srw_ss ())
                                                                ([itree_semantics_Break]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (break_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      let val continue_shallow = (curr_name_rule o rhs_name_rule)
                                 (QCONV (SIMP_CONV (srw_ss ())
                                                   ([itree_semantics_Continue]
                                                    @(map ASSUME extra_assms)
                                                     @tree_simp_rules)) prog_tree)
                                   |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (continue_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_with_pre prog_tree
          val extcall_shallow = (curr_name_rule o rhs_name_rule) extcall_thm
                                 |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (extcall_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
          val raise_shallow = (curr_name_rule o rhs_name_rule) raise_thm
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (raise_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
          val return_shallow = (curr_name_rule o rhs_name_rule) return_thm
                                |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (return_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
          val shmemload_shallow = (curr_name_rule o rhs_name_rule) shmemload_thm
                                   |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
       in
         (shmemload_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
          val shmemstore_shallow = (curr_name_rule o rhs_name_rule) shmemstore_thm
                                     |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
       in
         (shmemstore_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
          val store_shallow = (curr_name_rule o rhs_name_rule) store_thm
                                    |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
         (store_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
           val store32_shallow = (curr_name_rule o rhs_name_rule) store32_thm
                                    |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
       in
         (store32_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
          val storebyte_shallow = (curr_name_rule o rhs_name_rule) storebyte_thm
                                    |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
       in
         (storebyte_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      let val tick_shallow = QCONV (SIMP_CONV (srw_ss ())
                                              ([itree_semantics_Tick]
                                               @(map ASSUME extra_assms)
                                                @tree_simp_rules)) prog_tree
      in
        (tick_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
      in
        let val tree_abs1 = (if null (hyp inner1_thm) then mk_abs_rhs else mk_abs_impl) inner1_thm new_st
            val itree_dec_pre_thm = if null (hyp inner1_thm) then cj 1 itree_semantics_Dec_with_pre_let else
                                      cj 2 itree_semantics_Dec_with_pre_let
            val dec_thm = MATCH_MP  itree_dec_pre_thm tree_abs1
                            |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
            val gen_st = dec_thm |> concl |> lhs |> rand |> rand
            val dec_thm_sp = dec_thm |> DISCH_ALL
                                     |> GEN gen_st |> SPEC state
            val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
            val dec_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (PURE_REWRITE_CONV [dec_sp_all]) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
        in
          (dec_shallow,
           inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
          val spec_cond_thm = SPEC state cond_thm
                               |> UNDISCH_CONJUNCTS_ALL
          val if_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([spec_cond_thm]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
      in
        (if_shallow,
         inner_cond_thms, inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
          val while_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([GSYM while_def]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                               |> DISCH_ALL
                               |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                               |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL 
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
      in
        (while_shallow,
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = CONV_RULE (QCONV (RHS_CONV (PURE_REWRITE_CONV (map GSYM (rhs_names@lhs_names)))))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
                                            |> call_name_rule
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> DISCH_ALL
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eval_simp_with_hyp_rpt
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> eq_val_struct_eq_some_simp
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
      in
        let val next_tree_abs = (if null (hyp deccall_next_raw_thm) then mk_abs_rhs
                                 else mk_abs_impl) deccall_next_raw_thm new_st
            val itree_dec_pre_thm = if null (hyp deccall_next_raw_thm) then cj 1 deccall_raw_thm else
                                      cj 2 deccall_raw_thm
            val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                    |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
            val deccall_thm = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([deccall_gen_thm, FLOOKUP_SIMP]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> DISCH_ALL
                                |> call_name_rule
                                |> DISCH_ALL
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eval_simp_with_hyp_rpt
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> eq_val_struct_eq_some_simp
        in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
          val (inner1_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
          val (inner2_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
      in
        let val tree_abs1 = (if null (hyp inner1_thm) then mk_abs_rhs else mk_abs_impl) inner1_thm new_st
            val tree_abs2 = (if null (hyp inner2_thm) then mk_abs_rhs else mk_abs_impl) inner2_thm new_st
            val itree_seq_with_pre_thm = if null (hyp inner1_thm) then                                      
                                           if null (hyp inner2_thm) then
                                             cj 1 itree_semantics_Seq_ret_satisfy_pres
                                           else
                                             cj 2 itree_semantics_Seq_ret_satisfy_pres
                                         else
                                           if null (hyp inner2_thm) then
                                             cj 3 itree_semantics_Seq_ret_satisfy_pres
                                           else
                                             cj 4 itree_semantics_Seq_ret_satisfy_pres
            val seq_thm = MATCH_MP (MATCH_MP (itree_seq_with_pre_thm) tree_abs1) tree_abs2
                            |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
            val gen_st = seq_thm |> concl |> lhs |> rand |> rand
            val seq_thm_sp = seq_thm |> DISCH_ALL
                                     |> GEN gen_st |> SPEC state
                                                   |> UNDISCH_ALL
            val seq_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                |> DISCH_ALL
                                |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                |> UNDISCH_COMP_CONJUNCTS_ALL
                                |> eq_val_struct_eq_some_simp
                                |> eval_simp_with_hyp_rpt
        in
          (seq_shallow,
           inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
          end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end
        
(* test final not_simp *)
fun decompile_body_no_sep fname curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
  let fun decompile_while_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_prog = prog |> rand
          val new_st = mk_var ("nst", type_of state)
          val (true_nsimp_thm, true_inner_thms, true_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_prog, ^new_st)”
          val true_thm = true_nsimp_thm
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
          val true_abs = mk_abs_all_impl true_thm new_st
          val while_pre_pure_thm = MATCH_MP (itree_semantics_While_with_pre_conj) true_abs
          val while_pre_false_thm = cj 1 while_pre_pure_thm |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val while_pre_true_thm = cj 2 while_pre_pure_thm  |> SPEC_ALL |> UNDISCH_CONJUNCTS_ALL
          val gen_false_st = while_pre_false_thm |> concl |> lhs |> rand |> rand
          val gen_true_st = while_pre_true_thm |> concl |> lhs |> rand |> rand
          val while_true_thm_sp = while_pre_true_thm
                                    |> DISCH_ALL
                                    |> GEN gen_true_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
          val while_false_thm_sp = while_pre_false_thm
                                    |> DISCH_ALL
                                    |> GEN gen_false_st
                                    |> SPEC state
                                    |> UNDISCH_COMP_CONJUNCTS_ALL
          val while_true_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_true_thm_sp prog_tree
          val while_false_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) while_false_thm_sp prog_tree
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val while_true_shallow = ((curr_name_rule o rhs_name_rule)
                                    while_true_thm
                                      |> DISCH_ALL
                                      |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                      |> UNDISCH_COMP_CONJUNCTS_ALL
                                      |> eq_val_struct_eq_some_simp
                                      |> eval_simp_with_hyp_rpt
                                      |> DISCH_ALL
                                      |> GEN_ALL)
          val while_false_shallow = ((curr_name_rule o rhs_name_rule)
                                     while_false_thm
                                       |> DISCH_ALL
                                       |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                       |> UNDISCH_COMP_CONJUNCTS_ALL
                                       |> eq_val_struct_eq_some_simp
                                       |> eval_simp_with_hyp_rpt
                                       |> DISCH_ALL
                                       |> GEN_ALL)
      in
        (CONJ while_false_shallow while_true_shallow, true_inner_thms, true_inner_def, new_num)
        end
      fun decompile_cond_no_sep curr_names lhs_names rhs_names extra_assms scode code_thms fundecs n prog_tree =
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [prog, state]) = strip_comb progst
          val inner_true_prog = prog |> rator |> rand
          val inner_false_prog = prog |> rand
          val st = mk_var ("s", type_of state)
          val (true_nsimp_thm, true_inner_thms, true_inner_def, _, true_new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs n “^itc (^inner_true_prog, ^state)”
          val true_thm = true_nsimp_thm
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
          val (false_nsimp_thm, false_inner_thms, false_inner_def, _, new_num) =
          decompile_body_no_sep fname [] lhs_names rhs_names
                                ([“^state.code = ^scode”])
                                scode code_thms fundecs true_new_num “^itc (^inner_false_prog, ^state)”
          val false_thm = false_nsimp_thm
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
          val true_thm_simp =  true_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> UNDISCH_ALL
          val false_thm_simp =  false_thm
                                 |> DISCH_ALL
                                 |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                 |> UNDISCH_COMP_CONJUNCTS_ALL
                                 |> UNDISCH_ALL
          val true_abs = mk_abs_all_impl true_thm_simp st
          val false_abs = mk_abs_all_impl false_thm_simp st
          val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
          val lhs_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM lhs_names)))
          val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM (curr_names@rhs_names))))
          val cond_pure_thm = MATCH_MP (MATCH_MP (itree_semantics_If_with_pre_T) true_abs) false_abs
                                       |> UNDISCH_ALL
          val cond_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) cond_pure_thm prog_tree
                           |> DISCH_ALL
                           |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                           |> UNDISCH_COMP_CONJUNCTS_ALL
                           |> eq_val_struct_eq_some_simp
                           |> eval_simp_with_hyp_rpt
                           |> DISCH_ALL
                           |> GEN_ALL                          
      in
        (cond_thm, true_inner_thms@false_inner_thms, true_inner_def@false_inner_def, new_num)
        end
      val curr_name_rule = CONV_RULE (LHS_CONV (PURE_REWRITE_CONV (map GSYM curr_names)))
      val rhs_name_rule = CONV_RULE (RHS_CONV (PURE_REWRITE_CONV (map GSYM rhs_names)))
  in
    if can (match_term “itree_semantics (Skip, _)”) prog_tree then
      let val skip_shallow = (curr_name_rule o rhs_name_rule)
                             (QCONV (SIMP_CONV (srw_ss ())
                                               ([itree_semantics_Skip]
                                                @(map ASSUME extra_assms)
                                                 @tree_simp_rules)) prog_tree)
                               |> UNDISCH_ALL
      in
        (skip_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Annot _ _, _)”) prog_tree then
      let val annot_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([itree_semantics_Annot]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                               |> UNDISCH_ALL
      in
        (annot_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Assign _ _ _, _)”) prog_tree then
      let val assign_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Assign_with_pre prog_tree
          val assign_shallow = (curr_name_rule o rhs_name_rule) assign_thm
                               |> UNDISCH_ALL
      in
        (assign_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Break, _)”) prog_tree then
      let val break_shallow = (curr_name_rule o rhs_name_rule)
                                              (QCONV (SIMP_CONV (srw_ss ())
                                                                ([itree_semantics_Break]
                                                                 @(map ASSUME extra_assms)
                                                                  @tree_simp_rules)) prog_tree)
                               |> UNDISCH_ALL
      in
        (break_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Continue, _)”) prog_tree then
      let val continue_shallow = (curr_name_rule o rhs_name_rule)
                                 (QCONV (SIMP_CONV (srw_ss ())
                                                   ([itree_semantics_Continue]
                                                    @(map ASSUME extra_assms)
                                                     @tree_simp_rules)) prog_tree)
                               |> UNDISCH_ALL
      in
        (continue_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (ExtCall _ _ _ _ _, _)”) prog_tree then
      let val extcall_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ExtCall_with_pre prog_tree
          val extcall_shallow = (curr_name_rule o rhs_name_rule) extcall_thm
                               |> UNDISCH_ALL
      in
        (extcall_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Raise _ _, _)”) prog_tree then
      let val raise_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Raise_with_pre prog_tree
          val raise_shallow = (curr_name_rule o rhs_name_rule) raise_thm
                               |> UNDISCH_ALL
      in
        (raise_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (Return _, _)”) prog_tree then
      let val return_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Return_with_pre prog_tree
          val return_shallow = (curr_name_rule o rhs_name_rule) return_thm
                               |> UNDISCH_ALL
      in
        (return_shallow, [] , [], false, n)
        end
    else if can (match_term “itree_semantics (ShMemLoad _ _ _ _, _)”) prog_tree then
      let val shmemload_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemLoad_with_pre prog_tree
          val shmemload_shallow = (curr_name_rule o rhs_name_rule) shmemload_thm
                               |> UNDISCH_ALL
       in
         (shmemload_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (ShMemStore _ _ _, _)”) prog_tree then
      let val shmemstore_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_ShMemStore_with_pre prog_tree
          val shmemstore_shallow = (curr_name_rule o rhs_name_rule) shmemstore_thm
                               |> UNDISCH_ALL
       in
         (shmemstore_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store _ _, _)”) prog_tree then
      let val store_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store_with_pre prog_tree
          val store_shallow = (curr_name_rule o rhs_name_rule) store_thm
                               |> UNDISCH_ALL
      in
         (store_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Store32 _ _, _)”) prog_tree then
       let val store32_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_Store32_with_pre prog_tree
           val store32_shallow = (curr_name_rule o rhs_name_rule) store32_thm
                               |> UNDISCH_ALL
       in
         (store32_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (StoreByte _ _, _)”) prog_tree then
      let val storebyte_thm = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) itree_semantics_StoreByte_with_pre prog_tree
          val storebyte_shallow = (curr_name_rule o rhs_name_rule) storebyte_thm
                                    |> UNDISCH_ALL
       in
         (storebyte_shallow, [] , [], false, n)
         end
    else if can (match_term “itree_semantics (Tick, _)”) prog_tree then
      let val tick_shallow = QCONV (SIMP_CONV (srw_ss ())
                                              ([itree_semantics_Tick]
                                               @(map ASSUME extra_assms)
                                                @tree_simp_rules)) prog_tree
      in
        (tick_shallow,
         [], [], false, n)
        end
    else if can (match_term “itree_semantics (Dec _ _ _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val (inner1_nsimp_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n “itree_semantics (^prog1, ^new_st)”
          val inner1_thm = inner1_nsimp_thm
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
      in
        let val tree_abs1 = (if null (hyp inner1_thm) then mk_abs_rhs else mk_abs_impl) inner1_thm new_st
            val itree_dec_pre_thm = if null (hyp inner1_thm) then cj 1 itree_semantics_Dec_with_pre_let else
                                      cj 2 itree_semantics_Dec_with_pre_let
            val dec_thm = MATCH_MP  itree_dec_pre_thm tree_abs1
                            |> SPEC_ALL |> UNDISCH_CONJUNCTS_NON_ERR |> UNDISCH_ALL
            val gen_st = dec_thm |> concl |> lhs |> rand |> rand
            val dec_thm_sp = dec_thm |> DISCH_ALL
                                     |> GEN gen_st |> SPEC state
            val dec_sp_all = eq_match_simp_rule (srw_ss ()) ((map ASSUME extra_assms)) (dec_thm_sp) prog_tree |> UNDISCH_ALL
            val dec_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (PURE_REWRITE_CONV [dec_sp_all]) prog_tree)
                               |> UNDISCH_ALL
        in
          (dec_shallow,
           inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num)
            end
        end
    else if can (match_term “itree_semantics (If _ _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [cond_call, state]) = strip_comb progst
          val (cond_thm, inner_cond_thms, inner_cond_def, new_num) =
          decompile_cond_no_sep
          [] lhs_names rhs_names extra_assms
          scode code_thms fundecs (n + 1) “^itc (^cond_call, s)”
          val spec_cond_thm = SPEC state cond_thm
                               |> UNDISCH_CONJUNCTS_ALL
          val if_shallow = (curr_name_rule o rhs_name_rule)
                           (QCONV (SIMP_CONV (srw_ss ())
                                             ([spec_cond_thm]
                                              @(map ASSUME extra_assms)
                                               @tree_simp_rules)) prog_tree)
                             |> UNDISCH_ALL
      in
        (if_shallow,
         inner_cond_thms, inner_cond_def, true, new_num)
      end
    else if can (match_term “itree_semantics (While _ _, _)”) prog_tree then
      let val (itc, [progst]) = strip_comb prog_tree
          val (_, [while_call, state]) = strip_comb progst
          val while_def = mk_prog_abbr_def (concat ["while_", int_to_string n]) fname while_call
          val (while_thm, inner_while_thms, inner_while_def, new_num) = decompile_while_no_sep
                          [while_def] lhs_names rhs_names extra_assms
                          scode code_thms fundecs (n + 1) “^itc (^while_call, s)”
          val while_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([GSYM while_def]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                               |> UNDISCH_ALL
      in
        (while_shallow,
         [while_thm]@inner_while_thms, [while_def]@inner_while_def, true, new_num)
      end
    else if can (match_term “itree_semantics (Call _ _ _, _)”) prog_tree then
      let val call_name_rule = CONV_RULE (QCONV (RHS_CONV (PURE_REWRITE_CONV (map GSYM (rhs_names@lhs_names)))))
          val call_pure_thm = mk_call_pre_thm_with_argexps scode fundecs code_thms prog_tree
                                |> SPEC_ALL |> UNDISCH_ALL
                                            |> call_name_rule
          val call_thm = (curr_name_rule o rhs_name_rule)
                         (QCONV (SIMP_CONV (srw_ss ())
                                           ([call_pure_thm]
                                            @(map ASSUME extra_assms)
                                             @tree_simp_rules)) prog_tree)
                           |> UNDISCH_ALL
      in
        (call_thm, [], [], true, n) 
        end
    else if can (match_term “itree_semantics (DecCall _ _ _ _ _, _)”) prog_tree then
      let val call_name_rule = PURE_REWRITE_RULE (map GSYM (rhs_names@lhs_names))
          val (itc, [progst]) = strip_comb prog_tree
          val (_, [deccall, state]) = strip_comb progst
          val deccall_next = deccall |> rand
          val new_st = mk_var ("nst", type_of state)
          val deccall_raw_thm = mk_deccall_pre_thm_with_argexps scode fundecs code_thms prog_tree
          val (deccall_next_raw_nsimp_thm, deccall_next_inner_thms, deccall_next_inner_def, _, deccall_next_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names (extra_assms) scode code_thms fundecs (n + 1) “^itc (^deccall_next, ^new_st)”
          val deccall_next_raw_thm = deccall_next_raw_nsimp_thm
                                       |> DISCH_ALL
                                       |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                                       |> DISCH_ALL
                                       |> UNDISCH_COMP_CONJUNCTS_ALL 
                                       |> eval_simp_with_hyp_rpt
                                       |> eq_val_struct_eq_some_simp
      in
        let val next_tree_abs = (if null (hyp deccall_next_raw_thm) then mk_abs_rhs
                                 else mk_abs_impl) deccall_next_raw_thm new_st
            val itree_dec_pre_thm = if null (hyp deccall_next_raw_thm) then cj 1 deccall_raw_thm else
                                      cj 2 deccall_raw_thm
            val deccall_gen_thm = MATCH_MP (cj 2 deccall_raw_thm) next_tree_abs
                                    |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
            val deccall_thm = (curr_name_rule o rhs_name_rule)
                              (QCONV (SIMP_CONV (srw_ss ())
                                                ([deccall_gen_thm, FLOOKUP_SIMP]
                                                 @(map ASSUME extra_assms)
                                                  @tree_simp_rules)) prog_tree)
                                |> DISCH_ALL
                                |> call_name_rule
                                |> UNDISCH_ALL
        in
            (deccall_thm, deccall_next_inner_thms, deccall_next_inner_def, true, deccall_next_new_num)
            end
        end
    else if can (match_term “itree_semantics (Seq _ _, _)”) prog_tree then
      let val prog = prog_tree |> rand |> rator |> rand
          val prog1 = prog |> rator |> rand
          val prog2 = prog |> rand
          val state = prog_tree |> rand |> rand
          val new_st = mk_var ("nst", type_of state)
          val itc = prog_tree |> rator
          val tree1 = “^itc (^prog1, ^new_st)”
          val tree2 = “^itc (^prog2, ^new_st)”
          val (inner1_nsimp_thm, inner1_inner_thms, inner1_inner_def, inner1_nondet, inner1_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          (extra_assms) scode code_thms fundecs n tree1
          val inner1_thm = inner1_nsimp_thm
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
          val (inner2_nsimp_thm, inner2_inner_thms, inner2_inner_def, inner2_nondet, inner2_new_num) =
          decompile_body_no_sep
          fname [] lhs_names rhs_names
          ((hyp inner1_thm)@extra_assms) scode code_thms fundecs (inner1_new_num + 1) tree2
          val inner2_thm = inner2_nsimp_thm
                             |> DISCH_ALL
                             |> (fn x => (SIMP_RULE (srw_ss ()) tree_simp_rules) x)
                             |> DISCH_ALL
                             |> UNDISCH_COMP_CONJUNCTS_ALL 
                             |> eval_simp_with_hyp_rpt
                             |> eq_val_struct_eq_some_simp
      in
        let val tree_abs1 = (if null (hyp inner1_thm) then mk_abs_rhs else mk_abs_impl) inner1_thm new_st
            val tree_abs2 = (if null (hyp inner2_thm) then mk_abs_rhs else mk_abs_impl) inner2_thm new_st
            val itree_seq_with_pre_thm = if null (hyp inner1_thm) then                                      
                                           if null (hyp inner2_thm) then
                                             cj 1 itree_semantics_Seq_ret_satisfy_pres
                                           else
                                             cj 2 itree_semantics_Seq_ret_satisfy_pres
                                         else
                                           if null (hyp inner2_thm) then
                                             cj 3 itree_semantics_Seq_ret_satisfy_pres
                                           else
                                             cj 4 itree_semantics_Seq_ret_satisfy_pres
            val seq_thm = MATCH_MP (MATCH_MP (itree_seq_with_pre_thm) tree_abs1) tree_abs2
                            |> SPEC_ALL |> UNDISCH_COMP_CONJUNCTS_ALL
            val gen_st = seq_thm |> concl |> lhs |> rand |> rand
            val seq_thm_sp = seq_thm |> DISCH_ALL
                                     |> GEN gen_st |> SPEC state
                                                   |> UNDISCH_ALL
            val seq_shallow = (curr_name_rule o rhs_name_rule)
                              (QCONV (PURE_REWRITE_CONV [seq_thm_sp]) prog_tree)
                                |> UNDISCH_ALL
        in
          (seq_shallow,
           inner1_inner_thms@inner2_inner_thms, inner1_inner_def@inner2_inner_def, inner2_nondet, inner2_new_num)
          end
        end
    else
      let val _ = print $ term_to_string prog_tree
      in
        raise Domain
      end
  end


fun mk_body_abbr_var_exp name_term params_list arg_ty body =
  let val func_abbr_str = concat [mlstring_term_to_string name_term, "_body"]
      val varname_shape_list = params_list |> dest_list |> fst |> map dest_pair
      val (varname_list, shape_list) = (map fst varname_shape_list, map snd varname_shape_list)
      val exp_terms = mk_var_from_shape_once [] shape_list  arg_ty
      val exp_ty = mk_type ("v", [arg_ty])
      val exps_list = mk_list (exp_terms, exp_ty)
      val varmap_pairs = zip varname_list exp_terms |> map mk_pair
      val varmap_term = mk_list (varmap_pairs, mk_prod (“:mlstring”, exp_ty))
      val itree_body = “itree_semantics (^body, s with locals := FEMPTY |++ ^varmap_term)”
                         |> PURE_REWRITE_CONV [FOLDL, FUPDATE_LIST] |> concl |> rhs
      val state = itree_body |> rand |> rand |> rand
      val func_abbr_ty = (type_of exps_list) --> (type_of state) --> (type_of itree_body)
      val func_abbr_var = mk_var(func_abbr_str, func_abbr_ty)
      val func_abbr_with_state = list_mk_comb (func_abbr_var, [exps_list, state])
      val abbr_thm = Define $ single $ ANTIQUOTE $ mk_eq(func_abbr_with_state, itree_body)
  in
    abbr_thm
  end


  
fun decompile_2 file_name extra_assms fundec =
  let val (code_thm, lookup_thms) = codes_lookup_funcs_assms file_name fundec
      val ty_arg = fundec |> type_of |> dest_type |> snd |> hd |> dest_type |> snd |> hd
      val scode = code_thm |> concl |> lhs
      val fpb_lterm = EVAL “funcname_params_list ^fundec” |> concl |> rhs
      val fpb_l = fpb_lterm |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val name_body_thms = map (fn (x, (y, z)) => (x, mk_body_abbr_var_exp x y ty_arg z)) fpb_l
      val body_thms = map (fn (x, y) => y) name_body_thms
      val bodies = map (fn (x, y) => (x, y |> concl |> strip_forall |> snd |> rhs)) name_body_thms
  in
   (map (fn (x,y) =>
           let val (body_thm, inner_thms, inner_defs, _, _) =
               decompile_body_no_sep (mlstring_term_to_string x) body_thms body_thms [] extra_assms scode lookup_thms fundec 0 y
           in
             (body_thm |> DISCH_ALL
                       |> UNDISCH_COMP_CONJUNCTS_ALL
                       |> eval_simp_with_hyp_rpt
                       |> eq_val_struct_eq_some_simp
                       |> DISCH_ALL
                       |> GEN_ALL
                       |> SIMP_RULE (srw_ss ()) ([FLOOKUP_SIMP, 
                                                  GSYM res_var_list_def, res_var_list_thm]@tree_simp_rules)
                       |> eval_some_rw
                       |> let_non_comb_rw
                       |> SIMP_RULE (srw_ss ()) [shape_of_def, size_of_shape_def]
              , map (fn x => x |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
                               |> DISCH_ALL
                               |> GEN_ALL
                               |> SIMP_RULE (srw_ss ()) ([FLOOKUP_SIMP, 
                                                          GSYM res_var_list_def, res_var_list_thm]@tree_simp_rules)
                               |> eval_some_rw
                               |> let_non_comb_rw
                               |> SIMP_RULE (srw_ss ()) [shape_of_def, size_of_shape_def]) inner_thms, inner_defs)
           end
        )
        bodies, body_thms)
   end

fun decompile_2_reduce file_name extra_assms fundec =
  let val (code_thm, lookup_thms) = codes_lookup_funcs_assms file_name fundec
      val ty_arg = fundec |> type_of |> dest_type |> snd |> hd |> dest_type |> snd |> hd
      val scode = code_thm |> concl |> lhs
      val fpb_lterm = EVAL “funcname_params_list ^fundec” |> concl |> rhs
      val fpb_l = fpb_lterm |> dest_list |> fst |> map dest_pair |> map (fn (x, y) => (x, dest_pair y))
      val name_body_thms = map (fn (x, (y, z)) => (x, mk_body_abbr_var_exp x y ty_arg z)) fpb_l
      val body_thms = map (fn (x, y) => y) name_body_thms
      val bodies = map (fn (x, y) => (x, y |> concl |> strip_forall |> snd |> rhs)) name_body_thms
  in
   (map (fn (x,y) =>
           let val (body_thm, inner_thms, inner_defs, _, _) =
               decompile_body_no_sep (mlstring_term_to_string x) body_thms body_thms [] extra_assms scode lookup_thms fundec 0 y
           in
             (body_thm |> DISCH_ALL
                       |> UNDISCH_COMP_CONJUNCTS_ALL
                       |> eval_simp_with_hyp_rpt
                       |> eq_val_struct_eq_some_simp
                       |> DISCH_ALL
                       |> GEN_ALL
                       |> SIMP_RULE (srw_ss ()) ([FLOOKUP_SIMP, 
                                                  GSYM res_var_list_def, res_var_list_thm]@tree_simp_rules)
                       |> eval_some_rw
                       |> let_non_comb_rw
                       |> SIMP_RULE (srw_ss ()) [shape_of_def, size_of_shape_def]
                       |> conj_safe_spin_wbisim_lifting
              , map (fn x => x |> DISCH_ALL
                               |> UNDISCH_COMP_CONJUNCTS_ALL
                               |> eval_simp_with_hyp_rpt
                               |> eq_val_struct_eq_some_simp
                               |> DISCH_ALL
                               |> GEN_ALL
                               |> SIMP_RULE (srw_ss ()) ([FLOOKUP_SIMP, 
                                                          GSYM res_var_list_def, res_var_list_thm]@tree_simp_rules)
                               |> eval_some_rw
                               |> let_non_comb_rw
                               |> SIMP_RULE (srw_ss ()) [shape_of_def, size_of_shape_def]
                               |> conj_safe_spin_wbisim_lifting
                    ) inner_thms, inner_defs)
           end
        )
        bodies, body_thms)
   end
   
end;