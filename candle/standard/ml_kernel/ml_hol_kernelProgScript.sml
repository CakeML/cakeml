(*
  Apply the monadic translator to the Candle kernel to generate the
  deeply embedded CakeML code for the kernel. As a side effect, the
  monadic translator proves certificate theorems that state a formal
  connection between the generated code and the input HOL functions.
*)
open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory evaluateTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory terminationTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib
open ml_monadBaseTheory ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib
open holKernelTheory
open basisProgTheory
open holAxiomsSyntaxTheory (* for setting up the context *)
local open holKernelPmatchTheory in end

val _ = new_theory "ml_hol_kernelProg";
val _ = translation_extends "basisProg"

val _ = (use_full_type_names := false);

val _ = hide "abs";

val _ = ml_prog_update (open_module "Kernel");

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(* construct type refinement invariants *)

val _ = register_type ``:type``;

(* check ``:type`` is known to be an EqualityType *)
val EqualityType_TYPE = EqualityType_rule [] ``:type``;

val _ = register_type ``:term``;
val _ = register_exn_type ``:hol_exn``;
val HOL_EXN_TYPE_def = theorem"HOL_EXN_TYPE_def";

(* Initialize the translation *)

val init_type_constants_def = Define `
  init_type_constants = [(strlit"bool",0); (strlit"fun",2:num)]`;

val init_term_constants_def = Define `
  init_term_constants = [(strlit"=",
    Tyapp (strlit"fun")
      [Tyvar (strlit"A");
       Tyapp (strlit"fun")
         [Tyvar (strlit"A");
          Tyapp (strlit"bool") []]])]`;

val init_axioms_def = Define `
  init_axioms = []:thm list`;

val init_context_def = Define `
  init_context = ^(rhs(concl(holSyntaxTheory.init_ctxt_def)))`;

val refs_init_list = [
  ("the_type_constants", init_type_constants_def, get_the_type_constants_def,
  set_the_type_constants_def),
  ("the_term_constants", init_term_constants_def, get_the_term_constants_def,
  set_the_term_constants_def),
  ("the_axioms", init_axioms_def, get_the_axioms_def, set_the_axioms_def),
  ("the_context", init_context_def, get_the_context_def, set_the_context_def)
];

val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;

val raise_functions = [raise_Fail_def, raise_Clash_def];
val handle_functions = [handle_Fail_def, handle_Clash_def];
val exn_functions = zip raise_functions handle_functions;

val store_hprop_name = "HOL_STORE";
val state_type = ``:hol_refs``
val exn_ri_def = HOL_EXN_TYPE_def

val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
                                              rarrays_init_list
                                              farrays_init_list
                                              store_hprop_name
                                              state_type
                                              exn_ri_def
                                              exn_functions
                                              []
                                              NONE
                                              NONE;

(**************************************************************************************************)
(**************************************************************************************************)
(* --- perform translation --- *)

(* TODO: want builtin support for these *)
(*
val res = translate mlstringTheory.explode_aux_def;
val res = translate mlstringTheory.explode_def;
val explode_aux_side_thm = Q.prove(
  `∀s n m. n + m = strlen s ==> explode_aux_side s n m `,
  Induct_on`m` \\ rw[Once (theorem"explode_aux_side_def")]);
val explode_side_thm = Q.prove(
  `explode_side x`,
  rw[definition"explode_side_def",explode_aux_side_thm])
  |> update_precondition
val res = translate mlstringTheory.strcat_def;
*) (* TODO temporary *)

val res = translate stringTheory.string_lt_def
val res = translate stringTheory.string_le_def
val res = translate totoTheory.TO_of_LinearOrder

(* -- *)
val res = translate (subset_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.subtract_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.insert_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate holSyntaxExtraTheory.itlist_def;
val res = translate holSyntaxExtraTheory.union_def;
val res = translate mk_vartype_def;
val res = translate is_type_def;
val res = translate is_vartype_def;
val res = translate rev_assocd_def;
val res = translate holKernelTheory.type_subst_def;
val res = translate alphavars_def;
val res = translate holKernelPmatchTheory.raconv_def;

Theorem raconv_side = Q.prove(`
  !x y z. raconv_side x y z`,
  ho_match_mp_tac holKernelTheory.raconv_ind
  \\ ntac 4 (rw [Once (fetch "-" "raconv_side_def")]))
  |> update_precondition;

val res = translate aconv_def;
val res = translate holKernelPmatchTheory.is_var_def;
val res = translate holKernelPmatchTheory.is_const_def;
val res = translate holKernelPmatchTheory.is_abs_def;
val res = translate holKernelPmatchTheory.is_comb_def;
val res = translate mk_var_def;
val res = translate holSyntaxExtraTheory.frees_def;
val res = translate freesl_def;
val res = translate (freesin_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate holKernelPmatchTheory.vfree_in_def;
val res = translate tyvars_def;
val res = translate type_vars_in_term_def;
val res = translate holSyntaxExtraTheory.variant_def;
val res = translate vsubst_aux_def;
val res = translate holKernelPmatchTheory.is_eq_def;
val res = translate dest_thm_def;
val res = translate hyp_def;
val res = translate concl_def;

val type_compare_def = tDefine "type_compare" `
  (type_compare t1 t2 =
     case (t1,t2) of
     | (Tyvar x1,Tyvar x2) => mlstring$compare x1 x2
     | (Tyvar x1,Tyapp _ _) => Less
     | (Tyapp x1 a1,Tyvar _) => Greater
     | (Tyapp x1 a1,Tyapp x2 a2) =>
         case mlstring$compare x1 x2 of
         | Equal => type_list_compare a1 a2
         | other => other) /\
  (type_list_compare ts1 ts2 =
     case (ts1,ts2) of
     | ([],[]) => Equal
     | ([],t2::ts2) => Less
     | (t1::ts1,[]) => Greater
     | (t1::ts1,t2::ts2) =>
         (case type_compare t1 t2 of
          | Equal => type_list_compare ts1 ts2
          | other => other))`
  (WF_REL_TAC `measure (\x. case x of
                  INR (x,_) => type1_size x
                | INL (x,_) => type_size x)`)

val type_cmp_thm = Q.prove(
  `(type_cmp = type_compare) /\
    (list_cmp type_cmp = type_list_compare)`,
  fs [FUN_EQ_THM]
  \\ HO_MATCH_MP_TAC (fetch "-" "type_compare_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [holSyntaxExtraTheory.type_cmp_thm]
  \\ ONCE_REWRITE_TAC [type_compare_def]
  \\ REPEAT BasicProvers.CASE_TAC
  \\ fs [comparisonTheory.pair_cmp_def,ternaryComparisonsTheory.list_compare_def])
  |> CONJUNCT1;

val _ = add_preferred_thy "-";
val _ = save_thm("type_cmp_ind",
          (fetch "-" "type_compare_ind") |> RW [GSYM type_cmp_thm]);
val res = translate (type_compare_def |> RW [GSYM type_cmp_thm]);

val term_compare_def = Define `
  term_compare t1 t2 =
     case (t1,t2) of
       (Var x1 ty1,Var x2 ty2) =>
         (case mlstring$compare x1 x2 of
            Less => Less
          | Equal => type_cmp ty1 ty2
          | Greater => Greater)
     | (Var x1 ty1,Const v52 v53) => Less
     | (Var x1 ty1,Comb v54 v55) => Less
     | (Var x1 ty1,Abs v56 v57) => Less
     | (Const x1' ty1',Var v66 v67) => Greater
     | (Const x1' ty1',Const x2' ty2') =>
         (case mlstring$compare x1' x2' of
            Less => Less
          | Equal => type_cmp ty1' ty2'
          | Greater => Greater)
     | (Const x1' ty1',Comb v70 v71) => Less
     | (Const x1' ty1',Abs v72 v73) => Less
     | (Comb s1 t1,Var v82 v83) => Greater
     | (Comb s1 t1,Const v84 v85) => Greater
     | (Comb s1 t1,Comb s2 t2) =>
         (case term_compare s1 s2 of
            Less => Less
          | Equal => term_compare t1 t2
          | Greater => Greater)
     | (Comb s1 t1,Abs v88 v89) => Less
     | (Abs s1' t1',Var v98 v99) => Greater
     | (Abs s1' t1',Const v100 v101) => Greater
     | (Abs s1' t1',Comb v102 v103) => Greater
     | (Abs s1' t1',Abs s2' t2') =>
         case term_compare s1' s2' of
           Less => Less
         | Equal => term_compare t1' t2'
         | Greater => Greater`;

val term_cmp_thm = Q.prove(
  `term_cmp = term_compare`,
  fs [FUN_EQ_THM]
  \\ HO_MATCH_MP_TAC (fetch "-" "term_compare_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [holSyntaxExtraTheory.term_cmp_thm]
  \\ ONCE_REWRITE_TAC [term_compare_def]
  \\ REPEAT BasicProvers.CASE_TAC
  \\ fs [comparisonTheory.pair_cmp_def])

val _ = add_preferred_thy "-";
val _ = save_thm("term_cmp_ind",
          (fetch "-" "term_compare_ind") |> RW [GSYM term_cmp_thm]);
val res = translate (term_compare_def |> RW [GSYM term_cmp_thm]);

val res = translate holKernelPmatchTheory.codomain_def;
val res = translate holSyntaxTheory.typeof_def;
val res = translate holSyntaxTheory.ordav_def;
val res = translate holSyntaxTheory.orda_def;
val res = translate holSyntaxTheory.term_remove_def;
val res = translate holSyntaxTheory.term_union_def;

val def = try_def |> m_translate;
val def = holKernelTheory.assoc_def   (* rec *) |> m_translate;
val def = holKernelTheory.map_def    (* rec *) |> m_translate;
val def = holKernelTheory.forall_def (* rec *) |> m_translate;
val def = dest_type_def |> m_translate;
val def = dest_vartype_def |> m_translate;
val def = holKernelPmatchTheory.dest_var_def |> m_translate;
val def = holKernelPmatchTheory.dest_const_def |> m_translate;
val def = holKernelPmatchTheory.dest_comb_def |> m_translate;
val def = holKernelPmatchTheory.dest_abs_def |> m_translate;
val def = holKernelPmatchTheory.rator_def |> m_translate;
val def = holKernelPmatchTheory.rand_def |> m_translate;
val def = holKernelPmatchTheory.dest_eq_def |> m_translate;
val def = holKernelPmatchTheory.mk_abs_def |> m_translate;
val def = get_type_arity_def |> m_translate;
val def = mk_type_def |> m_translate;
val def = mk_fun_ty_def |> m_translate;
val def = holKernelPmatchTheory.type_of_def |> m_translate; (* PMATCH *)
val def = get_const_type_def |> m_translate;
val def = holKernelPmatchTheory.mk_comb_def |> m_translate;
val def = can_def |> m_translate;
val def = mk_const_def |> m_translate;
val def = image_def |> m_translate;

val fdM_def = new_definition("fdM_def",``fdM = first_dup``)
val fdM_intro = SYM fdM_def
val fdM_ind = save_thm("fdM_ind",REWRITE_RULE[MEMBER_INTRO]first_dup_ind)
val fdM_eqs = REWRITE_RULE[MEMBER_INTRO,fdM_intro]first_dup_def
val def = fdM_eqs |> translate
val def = REWRITE_RULE[fdM_intro]add_constants_def |> m_translate
val def = add_def_def |> m_translate
val def = new_constant_def |> m_translate
val def = add_type_def |> m_translate
val def = new_type_def |> m_translate

val _ = next_ml_names := ["eq_mp_rule", "assume"];
val def = holKernelPmatchTheory.EQ_MP_def |> m_translate
val def = ASSUME_def |> m_translate

val def = new_axiom_def |> m_translate
val def = vsubst_def |> m_translate
val def = inst_aux_def (* rec *) |> m_translate
val def = inst_def |> m_translate
val def = mk_eq_def |> m_translate

val _ = next_ml_names :=
  ["refl_conv", "trans_rule", "mk_comb_rule", "abs_rule", "beta_conv"];
val def = REFL_def |> m_translate
val def = holKernelPmatchTheory.TRANS_def |> m_translate

val MK_COMB_lemma = prove(
  ``MK_COMB x = case x of (Sequent asl1 c1,Sequent asl2 c2) =>
                  MK_COMB (Sequent asl1 c1,Sequent asl2 c2)``,
  every_case_tac)
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [holKernelPmatchTheory.MK_COMB_def]));

val def = MK_COMB_lemma |> m_translate
val def = holKernelPmatchTheory.ABS_def |> m_translate
val def = holKernelPmatchTheory.BETA_def |> m_translate
val def = DEDUCT_ANTISYM_RULE_def |> m_translate
val def = new_specification_def |> m_translate
val def = new_basic_definition_def |> m_translate

val _ = next_ml_names := ["inst_type_rule", "inst_rule"];
val def = (INST_TYPE_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = (INST_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = new_basic_type_definition_def |> m_translate

val _ = next_ml_names := ["sym_rule"];
val def = holKernelPmatchTheory.SYM_def |> m_translate
val def = PROVE_HYP_def |> m_translate
val def = list_to_hypset_def |> translate
val def = ALPHA_THM_def |> m_translate

val def = axioms_def |> m_translate
val def = types_def |> m_translate
val def = constants_def |> m_translate
val def = context_def |> m_translate

val _ = ml_prog_update (close_module NONE); (* TODO: needs signature SOME ... *)

(* extract the interesting thm *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

val candle_prog_thm =
  get_Decls_thm (get_ml_prog_state()) (* (get_curr_prog_state ()) *)
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"))
  |> curry save_thm "candle_prog_thm"

val _ = (print_asts := true);

val _ = export_theory();
