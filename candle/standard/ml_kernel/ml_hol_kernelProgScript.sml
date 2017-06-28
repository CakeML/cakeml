open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib
open ml_monadBaseTheory ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib holKernelTheory

val _ = new_theory "ml_hol_kernelProg";
			
val _ = (use_full_type_names := false);

val _ = register_type ``:cpn``
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``
val _ = register_type ``:'a option``

val _ = ml_prog_update (open_module "Kernel");

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(* construct type refinement invariants *)

val _ = register_type ``:type``;

val MEM_type_size = Q.prove(
  `!ts t. MEM t ts ==> type_size t < type1_size ts`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val type_ind = Q.store_thm("type_ind",
  `(!s ts. (!t. MEM t ts ==> P t) ==> P (Tyapp s ts)) /\
    (!v. P (Tyvar v)) ==> !x. P x`,
  REPEAT STRIP_TAC \\ completeInduct_on `type_size x`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!x1 x2. bb` MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ EVAL_TAC \\ IMP_RES_TAC MEM_type_size \\ DECIDE_TAC);

val TYPE_TYPE_def = fetch "-" "TYPE_TYPE_def"

val LIST_TYPE_NO_CLOSURES = Q.prove(
  `!xs v.
      (!x v. MEM x xs /\ p x v ==> no_closures v) /\
      LIST_TYPE p xs v ==> no_closures v`,
  Induct \\ FULL_SIMP_TAC std_ss [LIST_TYPE_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF,MEM]
  \\ METIS_TAC []);

val LIST_TYPE_11 = Q.prove(
  `!P ts v1 us v2.
      (!x1.
       MEM x1 ts ==>
        !v1 x2 v2.
          P x1 v1 /\ P x2 v2 ==>
          types_match v1 v2 /\ ((v1 = v2) <=> (x1 = x2))) /\
    LIST_TYPE P ts v1 /\ LIST_TYPE P us v2 ==>
    types_match v1 v2 /\ ((v1 = v2) = (ts = us))`,
  STRIP_TAC \\ Induct \\ Cases_on `us` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [LIST_TYPE_def,types_match_def,ctor_same_type_def]
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,types_match_def,ctor_same_type_def]
  \\ METIS_TAC []);

val CHAR_IMP_no_closures = Q.prove(
  `CHAR x v ==> no_closures v`,
  SIMP_TAC std_ss [CHAR_def,no_closures_def]);

val STRING_IMP_no_closures = Q.prove(
  `STRING_TYPE x v ==> no_closures v`,
  Cases_on`x` \\ SIMP_TAC std_ss [STRING_TYPE_def,no_closures_def]);

val EqualityType_thm = Q.prove(
  `EqualityType abs <=>
      (!x1 v1. abs x1 v1 ==> no_closures v1) /\
      (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2 /\
                                                (v1 = v2 <=> x1 = x2))`,
  SIMP_TAC std_ss [EqualityType_def] \\ METIS_TAC []);

val STRING_TYPE_lemma = Q.prove(
  `EqualityType (STRING_TYPE)`,
  METIS_TAC (eq_lemmas ()));

val EqualityType_TYPE = Q.prove(
  `EqualityType TYPE_TYPE`,
  SIMP_TAC std_ss [EqualityType_thm] \\ STRIP_TAC THEN1
   (HO_MATCH_MP_TAC type_ind
    \\ FULL_SIMP_TAC std_ss [TYPE_TYPE_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF]
    \\ IMP_RES_TAC (LIST_TYPE_NO_CLOSURES |> GEN_ALL)
    \\ METIS_TAC [CHAR_IMP_no_closures,STRING_IMP_no_closures])
  \\ HO_MATCH_MP_TAC type_ind \\ reverse STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [TYPE_TYPE_def]
    \\ FULL_SIMP_TAC (srw_ss()) [types_match_def,ctor_same_type_def]
    \\ ASSUME_TAC STRING_TYPE_lemma
    \\ FULL_SIMP_TAC std_ss [EqualityType_def] \\ RES_TAC)
  \\ REPEAT GEN_TAC \\ STRIP_TAC \\ REPEAT GEN_TAC \\ STRIP_TAC
  \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [TYPE_TYPE_def]
  \\ FULL_SIMP_TAC (srw_ss()) [types_match_def,ctor_same_type_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 /\ (x1 = y1)) /\ (b2 /\ (x2 = y2)) ==>
       (b1 /\ b2) /\ ((x1 /\ x2 <=> y1 /\ y2))``)
  \\ STRIP_TAC THEN1
   (ASSUME_TAC STRING_TYPE_lemma
    \\ FULL_SIMP_TAC std_ss [EqualityType_def] \\ RES_TAC
    \\ ASM_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC LIST_TYPE_11
  \\ Q.EXISTS_TAC `TYPE_TYPE`
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ RES_TAC)
  |> store_eq_thm;

val _ = register_type ``:term``;
val _ = register_type ``:thm``;
val _ = register_type ``:update``;
val _ = register_exn_type ``:hol_exn``;

val HOL_EXN_TYPE_def = theorem"HOL_EXN_TYPE_def";

(* Prove the specifications for the exception handling *)

(* failwith *)
val EvalM_failwith = Q.store_thm("EvalM_failwith",
  `!H x a.
      (lookup_cons "Fail" env = SOME (1,TypeExn (Long "Kernel" (Short "Fail")))) ==>
      Eval env exp1 (STRING_TYPE x) ==>
      EvalM env (Raise (Con (SOME (Short "Fail")) [exp1]))
        (MONAD a HOL_EXN_TYPE (failwith x)) H`,
  rw[Eval_def,EvalM_def,MONAD_def,failwith_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  rw[Once(CONJUNCT2 evaluate_cases)] >>
  first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac) >>
  IMP_RES_TAC (evaluate_empty_state_IMP
               |> INST_TYPE [``:'ffi``|->``:unit``]) >>
  rw[do_con_check_def,build_conv_def] >>
  fs [lookup_cons_def] >>
  fs[HOL_EXN_TYPE_def,namespaceTheory.id_to_n_def] >>
  asm_exists_tac \\ fs[] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] \\ METIS_TAC[REFS_PRED_append]);

(* clash *)

val EvalM_raise_clash = Q.store_thm("EvalM_raise_clash",
  `!H x a.
      (lookup_cons "Clash" env = SOME (1,TypeExn (Long "Kernel" (Short "Clash")))) ==>
      Eval env exp1 (TERM_TYPE x) ==>
      EvalM env (Raise (Con (SOME (Short "Clash")) [exp1]))
        (MONAD a HOL_EXN_TYPE (raise_clash x)) H`,
  rw[Eval_def,EvalM_def,MONAD_def,raise_clash_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  rw[Once(CONJUNCT2 evaluate_cases)] >>
  rw[do_con_check_def,build_conv_def] >>
  fs [lookup_cons_def] >>
  fs[HOL_EXN_TYPE_def,namespaceTheory.id_to_n_def] >>
  first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac) >>
  IMP_RES_TAC (evaluate_empty_state_IMP
               |> INST_TYPE [``:'ffi``|->``:unit``]) >>
  fs[] >> asm_exists_tac \\ fs[] >>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC] \\ METIS_TAC[REFS_PRED_append]);

(* handle_clash *)

val EvalM_handle_clash = Q.store_thm("EvalM_handle_clash",
  `!H n. (lookup_cons "Clash" env = SOME (1,TypeExn (Long "Kernel" (Short "Clash")))) ==>
        EvalM env exp1 (MONAD a HOL_EXN_TYPE x1) H ==>
        (!t v.
          TERM_TYPE t v ==>
          EvalM (write n v env) exp2 (MONAD a HOL_EXN_TYPE (x2 t)) H) ==>
        EvalM env (Handle exp1 [(Pcon (SOME (Short "Clash")) [Pvar n],exp2)])
          (MONAD a HOL_EXN_TYPE (handle_clash x1 x2)) H`,
  SIMP_TAC std_ss [EvalM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ Q.PAT_X_ASSUM `!s refs. REFS_PRED H refs s ==> bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ Cases_on `res` THEN1
   (srw_tac[DNF_ss][] >> disj1_tac \\
    asm_exists_tac \\ fs[MONAD_def,handle_clash_def] \\
    CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  \\ Q.PAT_X_ASSUM `MONAD xx yy zz t1 t2` MP_TAC
  \\ SIMP_TAC std_ss [Once MONAD_def] \\ STRIP_TAC
  \\ Cases_on `x1 refs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [handle_clash_def]
  \\ Cases_on `e` \\ FULL_SIMP_TAC (srw_ss()) [handle_clash_def]
  \\ srw_tac[boolSimps.DNF_ss][] >> disj2_tac >> disj1_tac
  \\ asm_exists_tac \\ fs[]
  \\ simp[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS,pat_bindings_def]
  \\ Cases_on `b` >> fs[HOL_EXN_TYPE_def] >>
  simp[pmatch_def] >> fs[lookup_cons_def] >>
  fs[same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def] >- (
    simp[Once evaluate_cases,MONAD_def,HOL_EXN_TYPE_def] ) >>
  first_x_assum drule >>
  disch_then drule >>
  simp[GSYM write_def] >>
  disch_then(qspec_then`[]`strip_assume_tac) >>
  fs[with_same_refs] >>
  asm_exists_tac >>
  fs[MONAD_def] >>
  TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[]);

val exn_thms = [EvalM_failwith, EvalM_raise_clash, EvalM_handle_clash];

(* Define and translate the store *)
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

val store_hprop_name = "HOL_STORE";
val exc_ri = ``HOL_EXN_TYPE``;
val translated_store_thms = translate_store refs_init_list store_hprop_name exc_ri;

(* Initialize the monadic translation *)
val _ = init_translation translated_store_thms exn_thms exc_ri []

val ty = ``:'b # 'c``; val _ = mem_derive_case_of ty;
val ty = ``:'a list``; val _ = mem_derive_case_of ty;
val ty = ``:'a option``; val _ = mem_derive_case_of ty;
val ty = ``:type``; val _ = mem_derive_case_of ty;
val ty = ``:term``; val _ = mem_derive_case_of ty;
val ty = ``:thm``; val _ = mem_derive_case_of ty;
val ty = ``:update``; val _ = mem_derive_case_of ty;

(**************************************************************************************************)
(**************************************************************************************************)
(* --- perform translation --- *)

val res = translate FST;
val res = translate SND;
val res = translate listTheory.LENGTH;
val res = translate listTheory.MAP;
val res = translate MEMBER_def;
val res = translate listTheory.EVERY_DEF;
val res = translate listTheory.EXISTS_DEF;
val res = translate listTheory.FILTER;
val res = translate listTheory.APPEND;
(* TODO: want builtin support for these *)
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
val res = translate stringTheory.string_lt_def
val res = translate stringTheory.string_le_def
val res = Q.prove(`mlstring_lt x1 x2 = string_lt (explode x1) (explode x2)`,
                simp [inv_image_def, mlstringTheory.mlstring_lt_inv_image])
          |> translate
val res = translate totoTheory.TO_of_LinearOrder
val res = translate mlstringTheory.compare_aux_def
val res = translate mlstringTheory.compare_def

(* Copy and paste from mlstringProg *)
val compare_aux_side_def = theorem"compare_aux_side_def";
val compare_side_def = definition"compare_side_def";

val compare_aux_side_thm = Q.prove (
  `!s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> compare_aux_side s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once compare_aux_side_def]
);

val compare_side_thm = Q.prove (
  `!s1 s2. compare_side s1 s2`,
  rw [compare_side_def, compare_aux_side_thm] ) |> update_precondition
(* end copy and paste *)

val res = translate comparisonTheory.pair_cmp_def
val res = translate comparisonTheory.list_cmp_def
(* -- *)
val res = translate (subset_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.subtract_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.insert_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate holSyntaxExtraTheory.itlist_def;
val res = translate holSyntaxExtraTheory.union_def;
val res = translate mk_vartype_def;
val res = translate is_type_def;
val res = translate is_vartype_def;
val res = translate holKernelPmatchTheory.rev_assocd_def;
val res = translate holKernelTheory.type_subst_def;
val res = translate alphavars_def;
val res = translate holKernelPmatchTheory.raconv_def;
val res = translate aconv_def;
val res = translate holKernelPmatchTheory.is_var_def;
val res = translate holKernelPmatchTheory.is_const_def;
val res = translate holKernelPmatchTheory.is_abs_def;
val res = translate holKernelPmatchTheory.is_comb_def;
val res = translate mk_var_def;
val res = translate holSyntaxExtraTheory.frees_def;
val res = translate combinTheory.o_DEF;
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
val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;

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
  \\ fs [comparisonTheory.pair_cmp_def,comparisonTheory.list_cmp_def])
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

val def = try_def |> m_translate
val def = assoc_def   (* rec *) |> m_translate
val def = map_def    (* rec *) |> m_translate
val def = forall_def (* rec *) |> m_translate
val def = dest_type_def |> m_translate
val def = dest_vartype_def |> m_translate
val def = holKernelPmatchTheory.dest_var_def |> m_translate
val def = holKernelPmatchTheory.dest_const_def |> m_translate
val def = holKernelPmatchTheory.dest_comb_def |> m_translate
val def = holKernelPmatchTheory.dest_abs_def |> m_translate
val def = holKernelPmatchTheory.rator_def |> m_translate
val def = holKernelPmatchTheory.rand_def |> m_translate
val def = holKernelPmatchTheory.dest_eq_def |> m_translate
val def = holKernelPmatchTheory.mk_abs_def |> m_translate
val def = get_type_arity_def |> m_translate
val def = mk_type_def |> m_translate
val def = mk_fun_ty_def |> m_translate
val def = holKernelPmatchTheory.type_of_def |> m_translate
val def = get_const_type_def |> m_translate
val def = holKernelPmatchTheory.mk_comb_def |> m_translate
val def = can_def |> m_translate
val def = mk_const_def |> m_translate
val def = image_def |> m_translate

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
val def = holKernelPmatchTheory.EQ_MP_def |> m_translate
val def = ASSUME_def |> m_translate
val def = new_axiom_def |> m_translate
val def = vsubst_def |> m_translate
val def = inst_aux_def (* rec *) |> m_translate
val def = inst_def |> m_translate
val def = mk_eq_def |> m_translate
val def = REFL_def |> m_translate
val def = holKernelPmatchTheory.TRANS_def |> m_translate
val def = holKernelPmatchTheory.MK_COMB_def |> m_translate
val def = holKernelPmatchTheory.ABS_def |> m_translate
val def = holKernelPmatchTheory.BETA_def |> m_translate
val def = DEDUCT_ANTISYM_RULE_def |> m_translate
val def = new_specification_def |> m_translate
val def = new_basic_definition_def |> m_translate
val def = (INST_TYPE_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = (INST_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = new_basic_type_definition_def |> m_translate
val def = holKernelPmatchTheory.SYM_def |> m_translate
val def = PROVE_HYP_def |> m_translate
val def = list_to_hypset_def |> translate
val def = ALPHA_THM_def |> m_translate

val _ = ml_prog_update (close_module NONE); (* TODO: needs signature SOME ... *)

(* extract the interesting thm *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

val candle_prog_thm =
  get_thm (get_curr_prog_state ())
  |> REWRITE_RULE [ML_code_def]
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"))
  |> curry save_thm "candle_prog_thm"

val _ = (print_asts := true);

val _ = export_theory();
