(*
  Proof of type soundness: a type-correct program does not crash.
*)
open preamble;
open libTheory astTheory typeSystemTheory semanticPrimitivesTheory fpSemTheory
     evaluateTheory;
open namespacePropsTheory fpSemPropsTheory;
open semanticPrimitivesPropsTheory;
open evaluatePropsTheory;
open weakeningTheory typeSysPropsTheory typeSoundInvariantsTheory;
open semanticsTheory;
local open primSemEnvTheory in end;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "getOpClass_def"]

val _ = new_theory "typeSound";

val type_num_defs = LIST_CONJ [
  Tarray_num_def,
  Tbool_num_def,
  Tchar_num_def,
  Texn_num_def,
  Tfn_num_def,
  Tint_num_def,
  Tlist_num_def,
  Tref_num_def,
  Tstring_num_def,
  Ttup_num_def,
  Tvector_num_def,
  Tword64_num_def,
  Tword8_num_def,
  Tword8array_num_def,
  Tdouble_num_def,
  Treal_num_def];

Theorem list_rel_flat:
   !R l1 l2. LIST_REL (LIST_REL R) l1 l2 ⇒ LIST_REL R (FLAT l1) (FLAT l2)
Proof
 Induct_on `l1`
 >> rw [FLAT]
 >> rw [FLAT]
 >> irule EVERY2_APPEND_suff
 >> rw []
QED

val fst_triple = Q.prove (
`(\ (x,y,z). x) = FST`,
 rw [FUN_EQ_THM]
 >> pairarg_tac
 >> rw []);

Theorem disjoint_image:
  !s1 s2 f. DISJOINT (IMAGE f s1) (IMAGE f s2) ⇒ DISJOINT s1 s2
Proof
 rw [DISJOINT_DEF, EXTENSION]
 >> metis_tac []
QED

val sing_list = Q.prove (
`!l. LENGTH l = 1 ⇔ ?x. l = [x]`,
 Cases
 >> rw []
 >> Cases_on `t`
 >> rw []);

val EVERY_LIST_REL = Q.prove (
`EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y)`,
 induct_on `l` >>
 srw_tac[][REPLICATE]);

Theorem v_unchanged[simp]:
 !tenv x. tenv with v := tenv.v = tenv
Proof
 srw_tac[][type_env_component_equality]
QED

Theorem check_dup_ctors_thm:
   check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)
Proof
  rw [check_dup_ctors_def] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  eq_tac >>
  rw [] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs []
QED

(* Classifying values of basic types *)
Theorem prim_canonical_values_thm:
   (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (IntLit n))) ∧
   (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap ⇒ (∃c. v = Litv (Char c))) ∧
   (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap ⇒ (∃s. v = Litv (StrLit s))) ∧
   (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word8 n))) ∧
   (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word64 n))) /\
   (type_v tvs ctMap tenvS v Tdouble /\ ctMap_ok ctMap ==> (? f w. v = FP_WordTree f)) ∧
   (type_v tvs ctMap tenvS v Treal /\ ctMap_ok ctMap ==> (? r. v = Real r)) ∧
   (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap ⇒
     (∃vs. v = Conv NONE vs ∧ LENGTH ts = LENGTH vs)) ∧
   (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap ⇒
     (∃env n e. v = Closure env n e) ∨
     (∃env funs n. v = Recclosure env funs n)) ∧
   (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
     (∃n v2. v = Loc n ∧ store_lookup n envS = SOME (Refv v2) ∧
       type_v 0 ctMap tenvS v2 t1)) ∧
   (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
     (∃n ws. v = Loc n ∧ store_lookup n envS = SOME (W8array ws) ∧
       FLOOKUP tenvS n = SOME W8array_t)) ∧
   (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
     (∃n vs. v = Loc n ∧ store_lookup n envS = SOME (Varray vs) ∧
       EVERY (\v. type_v 0 ctMap tenvS v t) vs ∧
       FLOOKUP tenvS n = SOME (Varray_t t))) ∧
   (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap ⇒
     (?vs. v = Vectorv vs ∧ EVERY (\v. type_v tvs ctMap tenvS v t) vs))
Proof
  strip_tac >>
  rpt (conj_tac) >>
  simp [Once type_v_cases] >>
  fs [prim_type_nums_def, ctMap_ok_def, type_num_defs] >>
  rw [] >>
  imp_res_tac type_funs_Tfn >>
  fs [type_num_defs] >>
  TRY (Cases_on `stamp` >> res_tac >> fs [] >> NO_TAC) >>
  fs [type_s_def]
  >- metis_tac [LIST_REL_LENGTH] >>
  res_tac >>
  Cases_on `v` >>
  fs [type_sv_def]
QED

val has_lists_v_to_list = Q.prove (
`!ctMap tvs tenvS t3.
  ctMap_ok ctMap ∧
  ctMap_has_lists ctMap ∧
  type_v tvs ctMap tenvS v (Tlist t3)
  ⇒
  ?vs. v_to_list v = SOME vs ∧
  EVERY (\v. type_v tvs ctMap tenvS v t3) vs ∧
  (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
  (t3 = Tstring ⇒ ∃str. vs_to_string vs = SOME str)`,
 measureInduct_on `v_size v` >>
 srw_tac[][] >>
 pop_assum mp_tac >>
 srw_tac[][Once type_v_cases] >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac type_funs_Tfn >>
 fs [] >>
 TRY (fs [type_num_defs] >> NO_TAC) >>
 `?cn. stamp = TypeStamp cn list_type_num`
 by (
   fs [ctMap_ok_def, ctMap_has_lists_def] >>
   metis_tac [same_type_def, stamp_nchotomy]) >>
 rw [] >>
 full_simp_tac(srw_ss())[ctMap_has_lists_def] >>
 `cn = "::" ∨ cn = "[]"` by metis_tac [NOT_SOME_NONE] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 fs [EVERY2_THM] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][v_to_list_def,v_to_char_list_def,vs_to_string_def] >>
 full_simp_tac(srw_ss())[type_subst_def] >>
 rename1 `type_v _ _ _ v _` >>
 LAST_X_ASSUM (mp_tac o Q.SPEC `v`) >>
 simp [v_size_def] >>
 disch_then drule >>
 simp [] >>
 disch_then drule >>
 fs [flookup_fupdate_list] >>
 rw [] >>
 rw [] >>
 imp_res_tac (SIMP_RULE (srw_ss()) [] prim_canonical_values_thm) >>
 rw [v_to_char_list_def, vs_to_string_def]);

Theorem ctor_canonical_values_thm:
   (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
      (∃b. v = Boolv b)) /\
   (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap ⇒
     ?vs.
       v_to_list v = SOME vs ∧
       EVERY (\v. type_v tvs ctMap tenvS v t) vs ∧
       (t = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
       (t = Tstring ⇒ ∃str. vs_to_string vs = SOME str)) ∧
   (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
    ctMap_ok ctMap ∧
    FLOOKUP ctMap stamp = SOME (tvs',ts',ti) ⇒
    (?cn n vs. same_type stamp (TypeStamp cn n) ∧ v = Conv (SOME (TypeStamp cn n)) vs) ∨
    (?n vs. same_type stamp (ExnStamp n) ∧ v = Conv (SOME (ExnStamp n)) vs))
Proof
  rw []
  >- (
    fs [Once type_v_cases] >>
    full_simp_tac std_ss [ctMap_has_bools_def, Boolv_def, type_num_defs, ctMap_ok_def] >>
    imp_res_tac type_funs_Tfn
    >- (
      `stamp = TypeStamp "True" bool_type_num ∨ stamp = TypeStamp "False" bool_type_num`
        by metis_tac [NOT_SOME_NONE, same_type_def, stamp_nchotomy] >>
      var_eq_tac >>
      rpt (qpat_x_assum `LIST_REL _ _ _` mp_tac) >>
      rpt (qpat_x_assum `FLOOKUP _ _ = SOME _` mp_tac) >>
      simp_tac list_ss [] >>
      metis_tac [])
    >- fs [])
  >- metis_tac [has_lists_v_to_list, Tlist_def, Tchar_def, Tstring_def]
  >- (
    fs [Once type_v_cases, ctMap_ok_def, type_num_defs] >>
    rw [] >>
    fs [] >>
    res_tac >>
    fs [] >>
    imp_res_tac type_funs_Tfn >>
    fs [prim_type_nums_def, type_num_defs] >>
    Cases_on `stamp` >>
    fs [same_type_def] >>
    res_tac >>
    fs [] >>
    Cases_on `stamp'` >>
    fs [same_type_def] >>
    res_tac >>
    fs [])
QED

val same_type_refl = Q.prove (
  `!t. same_type t t`,
  Cases_on `t` >>
  rw [same_type_def]);

val eq_same_type = Q.prove (
`(!v1 v2 tvs ctMap cns tenvS t.
  ctMap_ok ctMap ∧
  type_v tvs ctMap tenvS v1 t ∧
  type_v tvs ctMap tenvS v2 t
  ⇒
  do_eq v1 v2 ≠ Eq_type_error) ∧
(!vs1 vs2 tvs ctMap cns tenvS ts.
  ctMap_ok ctMap ∧
  LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
  LIST_REL (type_v tvs ctMap tenvS) vs2 ts
  ⇒
  do_eq_list vs1 vs2 ≠ Eq_type_error)`,
  ho_match_mp_tac do_eq_ind >>
  rw [do_eq_def] >>
  TRY (
    (* Solve most non-constructor cases *)
    ONCE_REWRITE_TAC [type_v_cases] >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    imp_res_tac type_funs_Tfn >>
    fs [prim_type_nums_def, lit_same_type_def,ctor_same_type_def, type_num_defs] >>
    NO_TAC) >>
  TRY (
    (* Solve trivial constructor cases *)
   ONCE_REWRITE_TAC [type_v_cases] >>
   CCONTR_TAC >>
   fs [] >>
   rw [] >>
   fs [ctMap_ok_def] >>
   rw [] >>
   imp_res_tac type_funs_Tfn >>
   TRY (fs [prim_type_nums_def, type_num_defs] >> NO_TAC) >>
   Cases_on `stamp` >>
   res_tac >>
   fs [prim_type_nums_def, type_num_defs] >>
   NO_TAC) >>
  TRY (
  (* floating-point value trees *)
    rename1 `Boolv (compress_bool fp)` >>
    fs[Once type_v_cases] >> NO_TAC)
  >- (
    (* Same constructor and type *)
    rpt (qpat_x_assum `type_v _ _ _ _ _` mp_tac) >>
    ONCE_REWRITE_TAC [type_v_cases] >>
    rw [] >>
    fs [] >>
    metis_tac [])
  >- (
   (* Different constructor and type *)
   ONCE_REWRITE_TAC [type_v_cases] >>
   CCONTR_TAC >>
   fs [] >>
   rw [] >>
   fs [ctor_same_type_def] >>
   fs [ctMap_ok_def] >>
   rw [] >>
   metis_tac [prim_type_nums_def, same_type_refl, stamp_nchotomy, MEM,
          Q.prove (`Ttup_num ≠ Texn_num`, rw [type_num_defs])])
  (* Vectors *)
  >- (
    rpt (qpat_x_assum `type_v _ _ _ _ _` mp_tac) >>
    ONCE_REWRITE_TAC [type_v_cases] >>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[combinTheory.o_DEF, EVERY_LIST_REL] >>
    `(\x y. type_v tvs ctMap tenvS x y) = type_v tvs ctMap tenvS` by metis_tac [] >>
    full_simp_tac(srw_ss())[] >>
    metis_tac [])
  >- (FULL_CASE_TAC \\
     full_simp_tac(srw_ss())[bool_case_eq]
     \\ metis_tac[]));

val type_env_conv_thm = Q.prove (
  `∀ctMap envC tenvC.
     nsAll2 (type_ctor ctMap) envC tenvC ⇒
     ∀cn tvs ts tn ti.
       (nsLookup tenvC cn = SOME (tvs,ts,ti) ⇒
        ?cn' stamp.
          nsLookup envC cn = SOME (LENGTH ts,stamp) ∧
          FLOOKUP ctMap stamp = SOME (tvs, ts, ti)) ∧
       (nsLookup tenvC cn = NONE ⇒ nsLookup envC cn = NONE)`,
 rw []
 >> imp_res_tac nsAll2_nsLookup2
 >> TRY (PairCases_on `v1`)
 >> fs [type_ctor_def] >>
 rw [] >>
 metis_tac [nsAll2_nsLookup_none]);

val type_funs_fst = Q.prove (
`!tenv tenvE funs tenv'.
  type_funs tenv tenvE funs tenv'
  ⇒
  MAP FST funs = MAP FST tenv'`,
 induct_on `funs` >>
 srw_tac[][] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_e_cases]) >>
 srw_tac[][] >>
 srw_tac[][] >>
 metis_tac []);

val type_recfun_env_help = Q.prove (
`∀fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
  ALL_DISTINCT (MAP FST funs') ∧
  tenv_ok tenv ∧
  type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
  tenv_val_exp_ok tenvE ∧
  num_tvs tenvE = 0 ∧
  (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
  type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
  type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
  ⇒
  LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
    (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs)
    (MAP (λ(x,t). (x,tvs,t)) bindings)`,
 induct_on `funs`
 >> srw_tac[][]
 >> pop_assum mp_tac
 >> simp [Once type_e_cases]
 >> rw []
 >> rw []
 >- (
   simp [Once type_v_cases]
   >> qexists_tac `tenv`
   >> qexists_tac `tenvE`
   >> rw []
   >> fs [type_all_env_def]
   >> simp []
   >> qexists_tac `bindings'`
   >> rw []
   >> imp_res_tac type_funs_fst
   >> fs []
   >> first_x_assum (qspec_then `fn` mp_tac)
   >> rw []
   >> drule ALOOKUP_MEM
   >> rw [MEM_MAP]
   >> metis_tac [FST])
 >- (
   first_x_assum irule
   >> simp []
   >> qexists_tac `bindings'`
   >> qexists_tac `tenv`
   >> qexists_tac `tenvE`
   >> simp []
   >> rw []
   >> fs []
   >> metis_tac [SOME_11, NOT_SOME_NONE]));

val type_recfun_env = Q.prove (
`∀funs ctMap tenvS tvs tenv tenvE env bindings.
  tenv_ok tenv ∧
  type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
  tenv_val_exp_ok tenvE ∧
  num_tvs tenvE = 0 ∧
  type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
  ALL_DISTINCT (MAP FST funs)
  ⇒
  LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
    (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs)
    (MAP (λ(x,t). (x,tvs,t)) bindings)`,
metis_tac [type_recfun_env_help]);

val type_v_exn = SIMP_RULE (srw_ss()) [] (Q.prove (
`!tvs cenv senv.
  ctMap_has_exns cenv ⇒
  type_v tvs cenv senv (Conv (SOME chr_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME subscript_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME bind_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME div_stamp) []) Texn`,
 ONCE_REWRITE_TAC [type_v_cases] >>
 srw_tac[][ctMap_has_exns_def] >>
 metis_tac [type_v_rules]));

 (*
val v_to_list_type = Q.prove (
`!v vs.
  ctMap_ok ctMap ∧
  ctMap_has_lists ctMap ∧
  v_to_list v = SOME vs ∧
  type_v 0 ctMap tenvS v (Tapp [t] (TC_name (Short "list")))
  ⇒
  type_v tvs ctMap tenvS (Vectorv vs) (Tapp [t] TC_vector)`,
 ho_match_mp_tac v_to_list_ind >>
 srw_tac[][v_to_list_def]
 >- full_simp_tac(srw_ss())[Once type_v_cases] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 qpat_x_assum `type_v x0 x1 x2 (Conv x3 x4) x5` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases] >>
 res_tac >>
 full_simp_tac(srw_ss())[ctMap_has_lists_def] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[type_subst_def, flookup_fupdate_list]
 >- metis_tac [type_v_weakening, weakCT_refl, weakS_refl] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[tid_exn_to_tc_def] >>
 res_tac >>
 FIRST_X_ASSUM (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][]);

val v_to_char_list_type = Q.prove (
`!v vs.
  ctMap_has_lists ctMap ∧
  v_to_char_list v = SOME vs ∧
  type_v 0 ctMap tenvS v (Tapp [t] (TC_name (Short "list")))
  ⇒
  type_v tvs ctMap tenvS (Litv (StrLit (IMPLODE vs))) (Tstring)`,
 ho_match_mp_tac v_to_char_list_ind >>
 srw_tac[][v_to_char_list_def]
 >- full_simp_tac(srw_ss())[Once type_v_cases] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 qpat_x_assum `type_v x0 x1 x2 (Conv x3 x4) x5` (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 srw_tac[][] >>
 srw_tac[][Once type_v_cases]);

 *)

val type_v_Boolv = Q.prove(
  `ctMap_has_bools ctMap ⇒ type_v tvs ctMap tenvS (Boolv b) Tbool`,
  srw_tac[][Boolv_def] >>
  srw_tac[][Once type_v_cases,LENGTH_NIL] >>
  full_simp_tac(srw_ss())[ctMap_has_bools_def] >>
  srw_tac[][Once type_v_cases]);

val remove_lambda_prod = Q.prove (
`(\ (x,y). P x y) = (\xy. P (FST xy) (SND xy))`,
 rw [FUN_EQ_THM]
 >> pairarg_tac
 >> rw []);

Theorem opapp_type_sound:
 !ctMap tenvS vs ts t.
 ctMap_ok ctMap ∧
 type_op Opapp ts t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs ts
 ⇒
 ?env e tenv tenvE.
   tenv_ok tenv ∧
   tenv_val_exp_ok tenvE ∧
   num_tvs tenvE = 0 ∧
   type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
   type_e tenv tenvE e t ∧
   do_opapp vs = SOME (env,e)
Proof
  rw [type_op_cases] >>
  fs [] >>
  rw [] >>
  MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
    (CONJUNCTS prim_canonical_values_thm) >>
  rw [do_opapp_def]
 >- (
   rename1 `type_v _ _ _ (Closure env n e) _`
   >> qpat_x_assum `type_v _ _ _ (Closure env n e) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> qexists_tac `tenv`
   >> qexists_tac `Bind_name n 0 t2 (bind_tvar 0 tenvE)`
   >> rw []
   >> fs [tenv_ok_def, type_all_env_def, tenv_val_exp_ok_def, bind_tvar_def]
   >> simp [add_tenvE_def]
   >> irule nsAll2_nsBind
   >> simp [])
 >- (
   rename1 `type_v _ _ _ (Recclosure env funs n) _`
   >> qpat_x_assum `type_v _ _ _ (Recclosure env funs n) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> imp_res_tac type_funs_find_recfun
   >> fs []
   >> rw []
   >> imp_res_tac (SIMP_RULE (srw_ss()) [Tfn_def] type_recfun_lookup)
   >> fs []
   >> qmatch_assum_abbrev_tac `type_e _ b _ _`
   >> qexists_tac `tenv`
   >> qexists_tac `b`
   >> fs [type_all_env_def]
   >> unabbrev_all_tac
   >> rw [tenv_val_exp_ok_def, add_tenvE_def]
   >- metis_tac [type_v_freevars]
   >- (
     irule tenv_val_exp_ok_bvl_funs
     >> simp []
     >> metis_tac [])
   >- (
     irule nsAll2_nsBind
     >> simp [build_rec_env_merge, nsAppend_to_nsBindList, add_tenvE_bvl]
     >> irule nsAll2_nsBindList
     >> simp []
     >> irule type_recfun_env
     >> simp [type_all_env_def]
     >> metis_tac [])
   >- (
     simp [remove_lambda_prod]
     >> metis_tac []))
QED

val store_type_extension_def = Define `
store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))`;

Theorem store_type_extension_weakS:
 !tenvS1 tenvS2.
  store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1
Proof
 srw_tac[][store_type_extension_def, weakS_def, FLOOKUP_FUNION] >>
 full_simp_tac(srw_ss())[SUBMAP_DEF, FLOOKUP_DEF, FUNION_DEF] >>
 metis_tac []
QED

Theorem store_type_extension_refl:
   !tenvS. store_type_extension tenvS tenvS
Proof
 rw [store_type_extension_def] >>
 qexists_tac `FEMPTY` >>
 rw []
QED

Theorem store_type_extension_trans:
   !s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3
Proof
 rw [store_type_extension_def]
 >> qexists_tac `FUNION tenvS'' tenvS'`
 >> rw [FUNION_ASSOC, FLOOKUP_FUNION]
 >> CASE_TAC
 >> rw []
 >> fs [FLOOKUP_FUNION]
 >> first_x_assum (qspec_then `l` mp_tac)
 >> rw []
 >> every_case_tac
 >> fs []
QED

Theorem store_assign_type_sound:
  !ctMap tenvS store sv st l.
  type_s ctMap store tenvS ∧
  FLOOKUP tenvS l = SOME st ∧
  type_sv ctMap tenvS sv st
  ⇒
  ?store'.
    store_assign l sv store = SOME store' ∧
    type_s ctMap store' tenvS
Proof
 rw [store_assign_def, type_s_def, store_v_same_type_def]
 >- (
   first_x_assum (qspec_then `l` mp_tac)
   >> rw [store_lookup_def]
   >> fs [FLOOKUP_DEF])
 >- (
   first_x_assum (qspec_then `l` mp_tac)
   >> fs [store_lookup_def]
   >> every_case_tac
   >> fs []
   >> Cases_on `st`
   >> fs [type_sv_def])
 >- (
   first_x_assum (qspec_then `l'` mp_tac)
   >> rw [store_lookup_def])
 >- (
   fs [store_lookup_def, EL_LUPDATE]
   >> rw []
   >> fs [])
QED

Theorem store_alloc_type_sound:
  !ctMap tenvS store sv st.
  ctMap_ok ctMap ∧
  type_s ctMap store tenvS ∧
  type_sv ctMap tenvS sv st
  ⇒
  ?store' tenvS' n.
    store_type_extension tenvS tenvS' ∧
    store_alloc sv store = (store', n) ∧
    type_s ctMap store' tenvS' ∧
    FLOOKUP tenvS' n = SOME st
Proof
 rw [store_alloc_def]
 >> qexists_tac `tenvS |+ (LENGTH store, st)`
 >> rw [store_type_extension_def, FLOOKUP_UPDATE]
 >- (
   qexists_tac `FEMPTY |+ (LENGTH store, st)`
   >> fs [type_s_def]
   >> rw [FLOOKUP_UPDATE, fmap_eq_flookup, FLOOKUP_FUNION]
   >> rw []
   >> fs [store_lookup_def]
   >> CCONTR_TAC
   >> fs []
   >> `l < l` by metis_tac [option_nchotomy]
   >> fs [])
 >- (
   fs [type_s_def, store_lookup_def, FLOOKUP_UPDATE, GSYM SNOC_APPEND]
   >> rw []
   >> rw [EL_LENGTH_SNOC, EL_SNOC]
   >> irule type_sv_weakening
   >> rw [weakS_def]
   >> qexists_tac `ctMap`
   >> rw [weakCT_refl]
   >> qexists_tac `tenvS`
   >> rw []
   >> CCONTR_TAC
   >> fs [FLOOKUP_DEF]
   >> fs []
   >> res_tac
   >> fs [])
QED

   (*
Theorem store_lookup_type_sound:
  !ctMap tenvS store n st.
  type_s ctMap store tenvS ∧
  FLOOKUP tenvS n = SOME st
  ⇒
  ?sv.
    store_lookup n store = SOME sv ∧
    type_sv ctMap tenvS sv st
Proof
 rw [type_s_def]
 >> metis_tac []
QED

 *)

Theorem type_v_list_to_v:
   !x xs t.
   type_v n ctMap tenvS x t /\
   v_to_list x = SOME xs ==>
     type_v n ctMap tenvS (list_to_v xs) t
Proof
   recInduct v_to_list_ind \\ rw [Once type_v_cases]
   \\ fs [v_to_list_def, list_to_v_def] \\ rw []
   \\ fs [list_to_v_def]
   \\ FULL_CASE_TAC \\ fs [] \\ rw []
   \\ fs [list_to_v_def]
   \\ qpat_x_assum `type_v _ _ _ _ _` mp_tac
   \\ rw [Once type_v_cases] \\ simp [Once type_v_cases]
QED

Theorem type_v_list_to_v_APPEND:
   !xs ys t.
     ctMap_has_lists ctMap /\
     type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) /\
     type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
     ==>
     type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num)
Proof
  Induct \\ rw [list_to_v_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ rw [Once type_v_cases]
  \\ rw [Once type_v_cases]
  \\ rename1 `_ = [t1;t2]`
  \\ `LENGTH ts = LENGTH [t1;t2]` by metis_tac [LENGTH_MAP]
  \\ fs [LENGTH_EQ_NUM_compute] \\ rveq
  \\ fs [] \\ rveq
  \\ imp_res_tac ctMap_has_lists_def \\ fs [] \\ rveq
  \\ ntac 2 (pop_assum kall_tac)
  \\ qpat_x_assum `type_v _ _ _ (_ xs) _` mp_tac
  \\ EVAL_TAC \\ strip_tac
  \\ first_x_assum (qspec_then `ys` mp_tac)
  \\ EVAL_TAC \\ metis_tac [Tlist_num_def]
QED

Theorem op_type_sound:
 !ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
 good_ctMap ctMap ∧
 op ≠ Opapp ∧
 (~ (getOpClass op = Icing)) /\ (* FP soundness separate *)
 type_s ctMap store tenvS ∧
 type_op op ts t ∧
 check_freevars 0 [] t ∧
 LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap store' tenvS' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort(Rffi_error _)) => T
   | Rerr (Rabort _) => F
Proof
  rw [type_op_cases, good_ctMap_def] >>
  fs [] >>
  rw [] >>
  rpt (
    MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
      (CONJUNCTS prim_canonical_values_thm) >>
    qpat_x_assum `type_v _ _ _ _ _` mp_tac) >>
  rw [] >>
  rw [do_opapp_def]
 >> TRY ( (* FP cases *)
    fs[getOpClass_def] >> NO_TAC)
 >> TRY ( (* simple cases *)
   rw [do_app_cases, PULL_EXISTS] >>
   simp [Once type_v_cases] >>
   qexists_tac `tenvS` >>
   rw [store_type_extension_refl] >>
   NO_TAC)
 >> TRY ( (* Integer ops *)
   rename1 `Opn _` >>
   rw [do_app_cases, PULL_EXISTS] >>
   rename1 `(op = Divide ∨ op = Module) ∧ divisor = 0`
   >> Cases_on `(op = Divide ∨ op = Module) ∧ divisor = 0`
   >- (
     fs []
     >> metis_tac [type_v_exn, store_type_extension_refl, div_exn_v_def])
   >- (
     fs []
     >> simp [Once type_v_cases]
     >> metis_tac [store_type_extension_refl]))
 >> TRY ( (* Boolean ops *)
   rename1 `Opb _` >>
   rw [do_app_cases, PULL_EXISTS] >>
   metis_tac [type_v_Boolv, store_type_extension_refl, Tbool_def])
 >> TRY ( (* Equality *)
   rename1`Equality` >>
   rw [do_app_cases, PULL_EXISTS] >>
   metis_tac [Tbool_def, type_v_Boolv, store_type_extension_refl, eq_result_nchotomy, eq_same_type])
 >> TRY ( (* real comparisons *)
   rename1`Real_cmp cmp` >>
   rw [do_app_cases, PULL_EXISTS] >>
   simp [Once type_v_cases] >>
   qexists_tac `tenvS` >>
   rw [store_type_extension_refl, Boolv_def] >> fs[ctMap_has_bools_def] >> NO_TAC)
 >> TRY ( (* ref update *)
   rename1 `Opassign` >>
   res_tac >>
   rw [do_app_cases, PULL_EXISTS] >>
   simp [Once type_v_cases]
   >> qpat_x_assum `type_v _ _ _ (Loc _) _` mp_tac
   >> simp [Once type_v_cases]
   >> rw [type_num_defs]
   >> metis_tac [type_sv_def, store_type_extension_refl, store_assign_type_sound])
  >> TRY ( (* ref alloc *)
   rename1 `Opref`
   >> rw [do_app_cases, PULL_EXISTS]
   >> simp [Once type_v_cases]
   >> rename1 `type_v _ _ _ v t`
   >> `type_sv ctMap tenvS (Refv v) (Ref_t t)` by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [type_v_freevars])
 >> TRY ( (* deref *)
   rename1 `Opderef`
   >> res_tac
   >> rw [do_app_cases, PULL_EXISTS]
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* W8array alloc *)
   rename1 `Aw8alloc`
   >> rw [do_app_cases, PULL_EXISTS]
   >> rename1 `type_v _ _ _ (Litv (Word8 w)) _`
   >> rename1 `type_v _ _ _ (Litv (IntLit n)) _`
   >> `type_sv ctMap tenvS (W8array (REPLICATE (Num (ABS n)) w)) W8array_t`
     by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `n < 0`
   >> simp [type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* W8array lookup *)
   rename1 `Aw8sub` >>
   rw [do_app_cases, PULL_EXISTS] >>
   first_x_assum drule >>
   rw []
   >> Cases_on `n < 0`
   >> rw [PULL_EXISTS, type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >- (
     Cases_on `Num (ABS n) ≥ LENGTH ws`
     >> rw []
     >> simp [type_v_exn]
     >> simp [Once type_v_cases]
     >> metis_tac [store_type_extension_refl]))
 >> TRY ( (* W8array length *)
   rename1 `Aw8length` >>
   res_tac >>
   rw [do_app_cases, PULL_EXISTS] >>
   simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* W8array assignment *)
   rename1 `Aw8update` >>
   rw [do_app_cases, PULL_EXISTS] >>
   first_x_assum drule >>
   rw [] >>
   rename1 `type_v _ _ _ (Litv (IntLit z)) _` >>
   rename1 `type_v _ _ _ (Loc l) _`
   >> Cases_on `z < 0`
   >> fs [type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> rename1 `store_lookup _ _ = SOME (W8array ws)`
   >> Cases_on `Num (ABS z) ≥ LENGTH ws`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> simp [Once type_v_cases]
   >> `type_sv ctMap tenvS (W8array (LUPDATE n (Num (ABS z)) ws)) W8array_t`
     by rw [type_sv_def]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* copy string *)
   rename1 `CopyStrStr` >>
   rw [do_app_cases, PULL_EXISTS] >>
   rename1`copy_array a b c`
   \\ Cases_on`copy_array a b c` \\ simp[]
   \\ simp[type_v_exn, sub_exn_v_def]
   >- metis_tac[store_type_extension_refl]
   \\ simp[Once type_v_cases]
   >- metis_tac[store_type_extension_refl] )
 >> TRY ( (* copy string/array *)
   rename1 `CopyStrAw8` >>
   rw [do_app_cases, PULL_EXISTS] >>
   res_tac >>
   rw [] >>
   rename1`copy_array a b c`
   \\ Cases_on`copy_array a b c` \\ simp[]
   \\ simp[type_v_exn, sub_exn_v_def]
   >- metis_tac[store_type_extension_refl]
   \\ simp[Once type_v_cases]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [store_type_extension_refl, type_sv_def])
 >> TRY ( (* copy array/string *)
   rename1 `CopyAw8Str` >>
   res_tac >>
   rw [do_app_cases, PULL_EXISTS] >>
   rename1`copy_array a b c`
   \\ Cases_on`copy_array a b c` \\ simp[]
   \\ simp[type_v_exn, sub_exn_v_def]
   >- metis_tac[store_type_extension_refl]
   \\ simp[Once type_v_cases]
   >- metis_tac[store_type_extension_refl] )
 >> TRY ( (* copy array/array *)
   rename1 `CopyAw8Aw8` >>
   rw [do_app_cases, PULL_EXISTS] >>
   res_tac >>
   rw [] >>
   rename1`copy_array a b c`
   \\ Cases_on`copy_array a b c` \\ simp[]
   \\ simp[type_v_exn, sub_exn_v_def]
   >- metis_tac[store_type_extension_refl]
   \\ simp[Once type_v_cases]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> metis_tac [store_type_extension_refl, type_sv_def])
 >> TRY ( (* Int to Char *)
   rename1`Chr` >>
   rw [do_app_cases, PULL_EXISTS] >>
   Cases_on `n < 0 ∨ n > 255`
   >> rw []
   >> rw []
   >> simp [type_v_exn, chr_exn_v_def]
   >> fs []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* character boolean ops *)
   rename1 `Chopb` >>
   rw [do_app_cases, PULL_EXISTS] >>
   metis_tac [type_v_Boolv, store_type_extension_refl, Tbool_def])
 >> TRY ( (* list to string *)
   rename1 `Implode` >>
   rw [do_app_cases, PULL_EXISTS] >>
   MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
     (CONJUNCTS ctor_canonical_values_thm) >>
   rw [] >>
   simp [Once type_v_cases] >>
   metis_tac [store_type_extension_refl])
 >> TRY ( (* string to list *)
   rename1 `Explode` >>
   rw [do_app_cases, PULL_EXISTS] >>
   MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
     (CONJUNCTS ctor_canonical_values_thm) >>
   rw [] >>
   goal_assum (first_assum o mp_then Any mp_tac) >>
   simp [store_type_extension_refl] >>
   qspec_tac (`s`,`s`) >> Induct >>
   fs [IMPLODE_EXPLODE_I,list_to_v_def,ctMap_has_lists_def] >>
   once_rewrite_tac [type_v_cases] >> simp [] >>
   simp [type_subst_def,FLOOKUP_UPDATE,FUPDATE_LIST,check_freevars_def] >>
   once_rewrite_tac [type_v_cases] >> simp [])
 >> TRY ( (* string lookup *)
   rename1 `Strsub` >>
   rw [do_app_cases, PULL_EXISTS] >>
   Cases_on `n < 0`
   >> rw [type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> Cases_on `Num (ABS n) ≥ LENGTH s`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> simp [Once type_v_cases, EVERY_EL]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* string concat *)
   rename1`Strcat` >>
   rw [do_app_cases, PULL_EXISTS] >>
   simp[Once type_v_cases]
   \\ imp_res_tac has_lists_v_to_list
   \\ rveq \\ fs[]
   \\ metis_tac[store_type_extension_refl] )
 >> TRY ( (* list to vector *)
   rename1`VfromList` >>
   rw [do_app_cases, PULL_EXISTS] >>
    MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
      (CONJUNCTS ctor_canonical_values_thm) >>
   rw [] >>
   rw [] >>
   simp [Once type_v_cases] >>
   fs [check_freevars_def] >>
   metis_tac [store_type_extension_refl])
 >> TRY ( (* vector lookup *)
   rename1 `Vsub` >>
   rw [do_app_cases, PULL_EXISTS]
   >> Cases_on `n < 0`
   >> rw [PULL_EXISTS, type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> Cases_on `Num (ABS n) ≥ LENGTH vs` >>
   rw []
   >- (
     rw [type_v_exn, Once type_v_cases] >>
     metis_tac [store_type_extension_refl]) >>
   fs [EVERY_EL]
   >> `Num (ABS n) < LENGTH vs` by decide_tac
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* Array alloc *)
   rename1 `Aalloc` >>
   rw [do_app_cases, PULL_EXISTS] >>
   rename1 `Tapp [t] Tarray_num` >>
   rename1 `REPLICATE _ v` >>
   `type_sv ctMap tenvS (Varray (REPLICATE (Num (ABS n)) v)) (Varray_t t)`
     by rw [type_sv_def, EVERY_REPLICATE]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `n < 0`
   >> simp [type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl, type_v_freevars])
 >> TRY ( (* Empty array alloc *)
   rename1 `AallocEmpty` >>
   rw [do_app_cases, PULL_EXISTS] >>
   rename1`Tapp [t1] Tarray_num` >>
   `type_sv ctMap tenvS (Varray []) (Varray_t t1)`
     by rw [type_sv_def]
   >> drule store_alloc_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> fs [check_freevars_def]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* Array lookup *)
   rename1 `Asub` >>
   rw [do_app_cases, PULL_EXISTS] >>
   res_tac >>
   rw []
   >> Cases_on `n < 0`
   >> rw [PULL_EXISTS, type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> rename1 `store_lookup l store = SOME sv`
   >> Cases_on `Num (ABS n) ≥ LENGTH vs` >>
   rw []
   >- (
     rw [type_v_exn, Once type_v_cases] >>
     metis_tac [store_type_extension_refl]) >>
   fs [EVERY_EL]
   >> `Num (ABS n) < LENGTH vs` by decide_tac
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* Array length *)
   rename1 `Alength` >>
   rw [do_app_cases, PULL_EXISTS] >>
   res_tac >>
   rw [] >>
   rw [Once type_v_cases] >>
   metis_tac [store_type_extension_refl])
 >> TRY ( (* Array update *)
   rename1 `Aupdate` >>
   rw [do_app_cases, PULL_EXISTS] >>
   res_tac >>
   rw [] >>
   Cases_on `n < 0`
   >> fs [type_v_exn, sub_exn_v_def]
   >- metis_tac [store_type_extension_refl]
   >> rename1 `store_lookup _ _ = SOME (Varray vs)`
   >> Cases_on `Num (ABS n) ≥ LENGTH vs`
   >> rw [type_v_exn]
   >- metis_tac [store_type_extension_refl]
   >> qmatch_assum_rename_tac `type_v _ _ _ _ (Tapp [t] Tarray_num)`
   >> `type_sv ctMap tenvS (Varray (LUPDATE x (Num (ABS n)) vs)) (Varray_t t)`
     by (
       rw [type_sv_def]
       >> irule IMP_EVERY_LUPDATE
       >> simp [])
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw []
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* FFI call *)
   rename1`FFI` >>
   rw [do_app_cases, PULL_EXISTS] >>
   res_tac >>
   rw []
   >> reverse TOP_CASE_TAC
   >- metis_tac[store_type_extension_refl]
   >> simp []
   >> `type_sv ctMap tenvS (W8array l) W8array_t` by rw [type_sv_def]
   >> drule store_assign_type_sound
   >> rpt (disch_then drule)
   >> rw [] \\ rw[]
   >> simp [Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >> TRY ( (* list append *)
   rename1`ListAppend` >>
   rw [do_app_cases, PULL_EXISTS] >>
   MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
     (CONJUNCTS ctor_canonical_values_thm) >>
   pop_assum mp_tac >>
   MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
     (CONJUNCTS ctor_canonical_values_thm) >>
   rw [] >>
   rw [] >>
   qexists_tac `tenvS` >>
   rw [store_type_extension_refl] >>
   metis_tac [type_v_list_to_v_APPEND, type_v_list_to_v])
QED

Theorem type_v_valtree:
  type_v 0 ctMap tenvS (FP_WordTree f) (Tapp [] Tdouble_num)
Proof
  assume_tac (SIMP_RULE std_ss [Tdouble_def] type_v_rules) \\ fs[]
QED

Theorem fpOp_type_sound:
   !ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
   good_ctMap ctMap ∧
   op ≠ Opapp ∧
   getOpClass op = Icing /\
   type_s ctMap store tenvS ∧
   type_op op ts t ∧
   check_freevars 0 [] t ∧
   LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
   ⇒
   ?tenvS' store' ffi' r.
     store_type_extension tenvS tenvS' ∧
     type_s ctMap store' tenvS' ∧
     do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
    (~ isFpBool op ==>
     case r of
     | Rval v => type_v 0 ctMap tenvS' v t
     | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
     | Rerr (Rabort(Rffi_error _)) => T
     | Rerr (Rabort _) => F) /\
    (isFpBool op ==>
       case r of
       Rval (FP_BoolTree fv) => type_v 0 ctMap tenvS' (Boolv (compress_bool fv)) t
       | Rval v => type_v 0 ctMap tenvS' v t
       | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
       | Rerr (Rabort(Rffi_error _)) => T
       | Rerr (Rabort _) => F)
Proof
  rw [type_op_cases, good_ctMap_def] >>
  fs [] >>
  rw [] >>
  rpt (
    MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
      (CONJUNCTS prim_canonical_values_thm) >>
    qpat_x_assum `type_v _ _ _ _ _` mp_tac) >>
  rw [] >>
  rw [do_opapp_def]
  >> TRY ( (* exclude non-fp and fp comparison cases *)
    fs[getOpClass_def, isFpBool_def] >> NO_TAC)
  >> TRY ( (* FP ops *)
    (rename1`FP_uop op` ORELSE rename1`FP_bop op` ORELSE rename1 `FP_top op`) >>
    rw [do_app_cases, PULL_EXISTS] >>
    qexists_tac `tenvS` >> fs[store_type_extension_refl, fp_translate_def] >>
    TRY (rename1 `FP_uop op` >> Cases_on `op`) >>
    fs[isFpBool_def] >>
    irule type_v_valtree)
  >> TRY ( (* FP cmp *)
    (rename1`FP_cmp`) >>
    rw [do_app_cases, PULL_EXISTS] >>
    qexists_tac `tenvS` >> fs[store_type_extension_refl, fp_translate_def] >>
    conj_tac >> fs[isFpBool_def] >>
    fs[fpValTreeTheory.fp_cmp_def, compress_word_def, compress_bool_def] >>
    drule type_v_Boolv >> fs[Tbool_def])
QED

Theorem build_conv_type_sound:
 !envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
 nsAll2 (type_ctor ctMap) envC tenvC ∧
 do_con_check envC (SOME cn) l ∧
 num_tvs tenvE = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 nsLookup tenvC cn = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envC (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' tn)
Proof
 rw []
 >> drule do_con_check_build_conv
 >> disch_then (qspec_then `REVERSE vs` mp_tac)
 >> rw []
 >> qexists_tac `v`
 >> rw []
 >> drule type_env_conv_thm
 >> rw []
 >> fs [build_conv_def]
 >> res_tac
 >> fs []
 >> rw []
 >> simp [Once type_v_cases, GSYM EVERY2_REVERSE1]
 >> simp [GSYM FUNION_alist_to_fmap]
 >> rfs [bind_tvar_def, num_tvs_def]
QED

Theorem same_ctor_and_same_tid:
   !stamp1 stamp2.
    same_ctor stamp1 stamp2 ∧
    same_type stamp1 stamp2
    ⇒
    stamp1 = stamp2
Proof
  rw [] >>
  Cases_on `stamp1` >>
  Cases_on `stamp2` >>
  fs [same_ctor_def, same_type_def]
QED

val pat_sound_tac =
 CCONTR_TAC >>
 full_simp_tac(srw_ss())[Once type_v_cases, Once type_p_cases, lit_same_type_def] >>
 srw_tac[][] >>
 imp_res_tac type_funs_Tfn >>
 imp_res_tac nsAll2_nsLookup2 >>
 fs [prim_type_nums_def, type_num_defs, ctMap_ok_def] >>
 TRY (rename1 `type_ctor _ _ v _` >> PairCases_on `v` >> Cases_on `v1`) >>
 fs [type_ctor_def] >>
 TRY (rename1 `FLOOKUP _ stamp = SOME _` >> Cases_on `stamp`) >>
 fs [] >>
 res_tac >>
 rw [] >>
 fs [] >>
 NO_TAC;

Theorem pat_type_sound:
  (∀(cenv : env_ctor) st p v bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings)))
Proof
 ho_match_mp_tac pmatch_ind
 >> rw [pmatch_def]
 >> TRY (qpat_x_assum `type_p _ _ _ _ _` mp_tac
         >> simp [Once type_p_cases])
 >> rw []
 >> rw [bind_var_list_def]
 >- pat_sound_tac
 >- (
   qpat_x_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> drule type_env_conv_thm
   >> rw []
   >> res_tac
   >> fs []
   >> drule type_ps_length
   >> rw []
   >> fs []
   >- (
     first_x_assum irule
     >> simp []
     >> fs [GSYM FUNION_alist_to_fmap]
     >> imp_res_tac same_ctor_and_same_tid >>
     fs [] >>
     metis_tac [])
   >- (fs [same_ctor_def] >> rveq >> imp_res_tac LIST_REL_LENGTH >> fs [])
   >- (
     fs [ctMap_ok_def] >>
     metis_tac []))
 >- (
   qpat_x_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- (
   simp [Once type_v_cases, Once type_p_cases]
   >> CCONTR_TAC
   >> fs []
   >> rw []
   >> metis_tac [type_ps_length, LIST_REL_LENGTH])
 >- (
   qpat_x_assum `type_v _ _ _ _ _` mp_tac
   >> simp [Once type_v_cases]
   >> rw []
   >> fs [type_s_def]
   >> res_tac
   >> fs []
   >> rw []
   >> Cases_on `v`
   >> fs [type_sv_def, type_num_defs]
   >> first_x_assum irule
   >> simp []
   >> metis_tac [type_v_weakening, weakCT_refl, weakS_refl])
 >- ((* Pas case *)
   first_x_assum drule>>
   rpt(disch_then drule)>>
   simp[PULL_EXISTS,FORALL_PROD]>>
   rpt(disch_then drule)>>
   metis_tac[APPEND_ASSOC,CONS_APPEND])
 >- (
   first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- pat_sound_tac
 >- (
   qpat_x_assum `type_ps _ _ (_::_) _ _` mp_tac
   >> simp [Once type_p_cases]
   >> rw []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> Cases_on `pmatch cenv st p v bindings` \\ fs []
   >- (CASE_TAC \\ fs [] \\ metis_tac [])
   >> rw []
   >> rw []
   >> fs []
   >> REWRITE_TAC [GSYM APPEND_ASSOC]
   >> first_x_assum irule
   >> simp []
   >> metis_tac [])
 >- pat_sound_tac
 >- pat_sound_tac
QED

Theorem lookup_var_sound:
   !n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs, t) ∧
    ctMap_ok ctMap ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    EVERY (check_freevars tvs []) targs ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v)
    ⇒
    ?v. nsLookup env.v n = SOME v ∧ type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t)
Proof
 rw [lookup_var_def, type_all_env_def]
 >> `nsLookup (add_tenvE tenvE tenv.v) n = SOME (LENGTH targs, t)`
   suffices_by (
     rw []
     >> imp_res_tac nsAll2_nsLookup2
     >> fs []
     >> rw []
     >> irule (GEN_ALL type_subst)
     >> simp []
     >> drule type_v_freevars
     >> rw [])
 >> fs [lookup_varE_def]
 >> every_case_tac
 >> fs []
 >- metis_tac [nsLookup_add_tenvE2]
 >- (
   irule nsLookup_add_tenvE1 >> conj_tac
   >- metis_tac []
   >> fs [tenv_val_exp_ok_def]
   >> metis_tac [tveLookup_freevars])
 >- metis_tac [nsLookup_add_tenvE3]
QED

(* TODO: Move *)
Theorem fpOp_no_err:
  ! op s store ffi r.
    getOpClass op = Icing /\
    do_app (s.refs, s.ffi) op vs = SOME ((store, ffi), r) ==>
    (isFpBool op ==> (? fv. r = Rval (FP_BoolTree fv))) /\
    (~ isFpBool op ==> (? fv. r = Rval (FP_WordTree fv)))
Proof
  rpt strip_tac
  \\ qpat_x_assum `do_app _ _ _ = _` mp_tac
  \\ Cases_on `isFpBool op` \\ Cases_on `op` \\ fs[getOpClass_def, isFpBool_def, do_app_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ fs[]
QED

(* TODO: Move *)
Theorem fprw_preserves_type:
  (do_fprw (Rval (FP_BoolTree fv_b)) rwApps rws = SOME v ==>
  ? fv_opt. v = Rval (FP_BoolTree fv_opt)) /\
  (do_fprw (Rval (FP_WordTree fv_w)) rwApps rws = SOME v ==>
  ? fv_opt. v = Rval (FP_WordTree fv_opt))
Proof
  fs[do_fprw_def]
  >> TOP_CASE_TAC >> fs[]
  >> rpt strip_tac >> fs[option_case_eq]
  >> rveq >> fs[]
QED

(* TODO: Move *)
Theorem EVERY_REPLICATE:
  EVERY (\x. type_v tvs ctMap tenv x t') vs =
  EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP (vs, REPLICATE (LENGTH vs) t'))
Proof
  Induct_on `vs` \\ fs[]
QED

Theorem EVERY_LIST_REL:
  EVERY (\ v. type_v n ctMap tenvS v t) vs =
  LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)
Proof
  EQ_TAC \\ Induct_on `vs` \\ fs[] \\ rpt strip_tac \\ res_tac
QED

Theorem do_fpoptimise_preserves_type:
! vs ts n ctMap tenvS annot.
  LIST_REL (type_v n ctMap tenvS) vs ts ==>
  ? vs2.
    do_fpoptimise annot vs = vs2 /\
    LIST_REL (type_v n ctMap tenvS) vs2 ts
Proof
  measureInduct_on `v1_size vs`
  \\ Cases_on `vs` \\ fs[do_fpoptimise_def, Once do_fpoptimise_cons]
  \\ rpt strip_tac \\ rveq
  \\ first_assum (qspec_then `t` mp_tac)
  \\ impl_tac >- fs[v_size_def]
  \\ strip_tac \\ res_tac
  \\ Cases_on `h` \\ fs[do_fpoptimise_def]
  >- (
    qpat_x_assum `type_v _ _ _ _ _` mp_tac
    \\ simp[Once type_v_cases]
    \\ rpt strip_tac \\ fs[] \\ rveq
    \\ first_x_assum (qspec_then `l` mp_tac)
    \\ impl_tac \\ fs[v_size_def]
    \\ strip_tac \\ res_tac
    \\ simp [Once type_v_cases])
  >- (
    qpat_x_assum `type_v _ _ _ _ _` mp_tac
    \\ simp[Once type_v_cases]
    \\ rpt strip_tac \\ fs[] \\ rveq
    \\ first_x_assum (qspec_then `l` mp_tac)
    \\ impl_tac \\ fs[v_size_def]
    \\ strip_tac \\ res_tac
    \\ simp [Once type_v_cases]
    \\ fs[EVERY_LIST_REL] \\ res_tac
    \\ fs[do_fpoptimise_LENGTH])
  \\ qpat_x_assum `type_v _ _ _ _ _` mp_tac
  \\ simp[Once type_v_cases]
  \\ rpt strip_tac \\ fs[Once type_v_cases]
QED

Theorem do_fpoptimise_preserves_type_single =
  do_fpoptimise_preserves_type
    |> SPEC_ALL
    |> Q.GEN `ts` |> Q.GEN `vs`
    |> Q.SPEC `[v]` |> Q.SPEC `[t]`
    |> GEN_ALL |> REWRITE_RULE [LIST_REL_def]

Theorem exp_type_sound:
  (!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v Texn ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F)
Proof
 ho_match_mp_tac evaluate_ind
 >> simp [evaluate_def, type_es_list_rel, GSYM CONJ_ASSOC, good_ctMap_def]
 >> rw []
 >- metis_tac [store_type_extension_refl]
 >- (
   split_pair_case_tac
   >> fs []
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rename1 `evaluate _ _ (e2::es) = (s2,r2)`
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> fs [IMP_CONJ_THM]
   >> rpt (disch_then drule)
   >> rw []
   >> rename1 `store_type_extension _ new_tenvS`
   >> `type_all_env ctMap new_tenvS env (tenv with v := add_tenvE tenvE tenv.v)`
     by metis_tac [store_type_extension_weakS, type_all_env_weakening, weakCT_refl]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS, GSYM CONJ_ASSOC]
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `r2`
   >> fs []
   >> rw []
   >> metis_tac [store_type_extension_trans, store_type_extension_weakS,
                 weakCT_refl, type_all_env_weakening, type_v_weakening])
 >- (
   rename [`Lit`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases, Once type_v_cases]
   >> metis_tac [store_type_extension_refl])
 >- (
   rename [`Raise`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rw []
   >> fs [is_value_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspec_then `0` mp_tac)
   >> simp []
   >> rfs []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> rw []
   >> metis_tac [])
 >- (
   rename [`Handle`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rw []
   >> fs [is_value_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspec_then `0` mp_tac)
   >> simp []
   >> rfs []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >> rw []
   >- metis_tac []
   >> reverse (Cases_on `e`)
   >> fs [type_pes_def]
   >> rw []
   >- metis_tac []
   >> rename1`type_v 0 ctMap tenvS' _ _`
   >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
     by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
   >> rename [`can_pmatch_all env.c s1.refs (MAP FST pes) a`]
   >> `can_pmatch_all env.c s1.refs (MAP FST pes) a` by
    (fs [can_pmatch_all_EVERY,RES_FORALL,FORALL_PROD,EVERY_MEM,MEM_MAP,PULL_EXISTS]
     >> rpt strip_tac >> res_tac
     >> fs [type_all_env_def]
     >> drule (CONJUNCT1 pat_type_sound)
     >> rpt (disch_then drule)
     >> disch_then (qspecl_then [`[]`,`[]`] assume_tac)
     >> fs [] >> fs [])
   >> fs []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `r`
   >> fs []
   >> rw []
   >> imp_res_tac evaluate_length
   >> fs [sing_list]
   >> fs [bind_tvar_def]
   >> metis_tac [store_type_extension_trans, type_v_freevars])
 >- (
   rename [`Con`]
   >> qpat_x_assum `type_e _ _ (Con _ _) _` mp_tac
   >> simp [Once type_e_cases]
   >> fs [is_value_def]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1, r1)`
   >> fs [EVERY_REVERSE, ETA_THM]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> rw [type_es_list_rel, GSYM EVERY2_REVERSE1]
   >> qmatch_assum_abbrev_tac `LIST_REL _ _ types`
   >> first_x_assum (qspec_then `REVERSE types` mp_tac)
   >> simp []
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     UNABBREV_ALL_TAC
     >> fs [type_all_env_def]
     >> drule build_conv_type_sound
     >> rpt (disch_then drule)
     >> simp []
     >> rpt (disch_then drule)
     >> simp []
     >> rpt (disch_then drule)
     >> rw []
     >> fs []
     >> rw []
     >> metis_tac [])
   >- metis_tac []
   >- (
     fs [build_conv_def]
     >> rw []
     >> simp [Once type_v_cases, GSYM EVERY2_REVERSE1]
     >> metis_tac [])
   >- metis_tac [])
 >- (
   CCONTR_TAC
   >> fs []
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> CCONTR_TAC
   >> fs []
   >> rw []
   >> fs [do_con_check_def, type_all_env_def]
   >> imp_res_tac type_env_conv_thm
   >> fs []
   >> imp_res_tac type_es_length
   >> fs [])
 >- (
   rename [`Var`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> drule lookup_var_sound
   >> rpt (disch_then drule)
   >> rw []
   >> fs [is_value_def]
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >- (
   pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> simp [Once type_v_cases]
   >> fs [is_value_def, num_tvs_def, bind_tvar_def, type_all_env_def]
   >> metis_tac [store_type_extension_refl])
 >- (
   rename [`App`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> fs [is_value_def, type_es_list_rel]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`REVERSE ts`, `0`] mp_tac)
   >> rw [LIST_REL_REVERSE_EQ]
   >> reverse (Cases_on `r1`)
   >> fs []
   >> rw []
   >- (
     rename1 `evaluate _ _ _ = (s1, Rerr err_v)`
     >> Cases_on `err_v`
     >> fs []
     >> rw []
     >> metis_tac [])
   >> Cases_on `op = Opapp`
   >> fs []
   >> rename1 `LIST_REL (type_v 0 _ _) vs _`
   >- (
     drule opapp_type_sound
     >> fs [EVERY2_REVERSE1]
     >> disch_then drule
     >> disch_then drule
     >> rw []
     >> fs [getOpClass_def]
     >> Cases_on `s1.clock = 0`
     >> fs []
     >> rw []
     >- metis_tac []
     >> fs [type_all_env_def]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> fs [dec_clock_def, PULL_EXISTS]
     >> rename1 `type_e tenv' tenvE' e t`
     >> rename1 `type_s _ _ tenvS'`
     >> disch_then (qspecl_then [`0`, `t`] mp_tac)
     >> simp [bind_tvar_def]
     >> rw []
     >> metis_tac [store_type_extension_trans])
   >> `getOpClass op ≠ FunApp`
     by (Cases_on `op` >> fs[getOpClass_def])
   >> Cases_on `getOpClass op = Icing` >> fs[]
   >- ( (* FP ops *)
    Cases_on `s1.fp_state.canOpt = FPScope Opt`
    >> fs[bind_tvar_def]
    >> `good_ctMap ctMap` by simp [good_ctMap_def]
    >> drule fpOp_type_sound
    >> rpt (disch_then drule)
    >> disch_then (qspec_then `s1.ffi` mp_tac)
    >> rw []
    >> rename1 `do_app _ _ _ = SOME ((store1, ffi1), r1)`
    >> imp_res_tac fpOp_no_err
    >> fs[shift_fp_opts_def] >> rveq
    >> Cases_on `isFpBool op` >> fs[] >> rveq >> fs[]
    >- (
       Cases_on `do_fprw ((Rval (FP_BoolTree fv)):(v,v) result) (s1.fp_state.opts 0) s1.fp_state.rws`
       >> fs[]
       >- metis_tac [store_type_extension_trans]
       >> imp_res_tac fprw_preserves_type
       >> rveq >> fs[Boolv_def]
       >> Cases_on `compress_bool fv`
       >> Cases_on `compress_bool fv_opt`
       >> fs[Once type_v_cases, PULL_EXISTS, ctMap_has_bools_def] >> rveq
       >> fs[] >> rveq
       >> rename [`LENGTH [] = LENGTH ts2`] >> Cases_on `ts2` \\ fs[]
       >> metis_tac [store_type_extension_trans])
    >- (
       Cases_on `do_fprw ((Rval (FP_WordTree fv)):(v,v) result) (s1.fp_state.opts 0) s1.fp_state.rws`
       >> fs[]
       >- metis_tac [store_type_extension_trans]
       >> imp_res_tac fprw_preserves_type
       >> rveq >> fs[Once type_v_cases]
       >> metis_tac [store_type_extension_trans])
    >- (
       fs[do_fprw_def]
       >> Cases_on `s1.fp_state.opts 0` >> fs[]
       >> metis_tac [store_type_extension_trans])
     >> fs[Once type_v_cases]
     >> metis_tac [store_type_extension_trans])
   >> Cases_on `getOpClass op = Reals`
   >- (
     Cases_on `op` >> fs[getOpClass_def]
     >> Cases_on `ts` >> fs[type_op_def])
   >> Cases_on ‘getOpClass op = EvalOp’
   >- (
     Cases_on ‘op’ >> gs[getOpClass_def]
     >> Cases_on ‘ts’ >> fs[type_op_def])
   >> fs [bind_tvar_def]
   >> `good_ctMap ctMap` by simp [good_ctMap_def]
   >> drule op_type_sound
   >> rpt (disch_then drule)
   >> disch_then (qspec_then `s1.ffi` mp_tac)
   >> `getOpClass op = Simple` by (Cases_on `op` >> fs[getOpClass_def])
   >> rw []
   >> rename1 `do_app _ _ _ = SOME ((store1, ffi1), r1)`
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- metis_tac [store_type_extension_trans]
   >> rename1 `do_app _ _ _ = SOME (_, Rerr err_v)`
   >> Cases_on `err_v`
   >> fs []
   >> rw []
   >> every_case_tac
   >> metis_tac [store_type_extension_trans])
 >- (
   rename [`Log`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`, `Tbool`] mp_tac)
   >> simp []
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
         (CONJUNCTS ctor_canonical_values_thm) >>
     rw [] >>
     Cases_on `b`
     >> fs [do_log_def]
     >> Cases_on `lop`
     >> fs []
     >> rw []
     >- (
       rename1`type_s _ _ tenvS'` >>
       `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
         by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
       >> first_x_assum drule
       >> rpt (disch_then drule)
       >> fs [PULL_EXISTS]
       >> disch_then (qspecl_then [`0`, `Tbool`] mp_tac)
       >> simp []
       >> rw []
       >> metis_tac [store_type_extension_trans])
     >- metis_tac []
     >- metis_tac []
     >- (
       rename1`type_s _ _ tenvS'` >>
       `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
         by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
       >> first_x_assum drule
       >> rpt (disch_then drule)
       >> fs [PULL_EXISTS]
       >> disch_then (qspecl_then [`0`, `Tbool`] mp_tac)
       >> simp []
       >> rw []
       >> metis_tac [store_type_extension_trans]))
   >- metis_tac [])
 >- (
   rename [`If`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`, `Tbool`] mp_tac)
   >> simp []
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     MAP_EVERY (TRY o drule o SIMP_RULE (srw_ss()) [] o GEN_ALL)
         (CONJUNCTS ctor_canonical_values_thm) >>
     rw []
     >> rename1`type_s _ _ tenvS'`
     >> Cases_on `b`
     >> fs [do_if_def, Boolv_def]
     >> rw []
     >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
       by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> fs [PULL_EXISTS]
     >> disch_then (qspecl_then [`0`] mp_tac)
     >> simp []
     >> rw []
     >> metis_tac [store_type_extension_trans])
   >- metis_tac [])
 >- (
   rename [`Mat`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ [e1] = (s1,r1)`
   >> rw []
   >> fs [is_value_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspec_then `0` mp_tac)
   >> simp []
   >> rfs []
   >> disch_then drule
   >> rw []
   >> reverse (Cases_on `r1`)
   >> fs []
   >> rw []
   >> rw []
   >- metis_tac []
   >> fs [type_pes_def]
   >> rw []
   >> rename1`type_s _ _ tenvS'`
   >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
     by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
   >> rename [`can_pmatch_all env.c s1.refs (MAP FST pes) x`]
   >> `can_pmatch_all env.c s1.refs (MAP FST pes) x` by
    (fs [can_pmatch_all_EVERY,RES_FORALL,FORALL_PROD,EVERY_MEM,MEM_MAP,PULL_EXISTS]
     >> rpt strip_tac >> res_tac
     >> fs [type_all_env_def]
     >> drule (CONJUNCT1 pat_type_sound)
     >> rpt (disch_then drule)
     >> disch_then (qspecl_then [`[]`,`[]`] assume_tac)
     >> fs [] >> fs [])
   >> fs []
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> fs [type_v_exn, bind_exn_v_def]
   >> rpt (disch_then drule)
   >> rw []
   >> Cases_on `r`
   >> fs []
   >> rw []
   >> imp_res_tac evaluate_length
   >> fs [sing_list]
   >> fs [bind_tvar_def]
   >> metis_tac [store_type_extension_trans, type_v_freevars])
 >- (
   rename [`Let`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (s1,r1)`
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> first_x_assum drule
   >> rpt (disch_then drule)
   >> simp [PULL_EXISTS]
   >> disch_then (qspecl_then [`0`] mp_tac)
   >> simp []
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     rename1 `type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2` >>
     rename1 `type_s _ _ tenvS'`
     >> qabbrev_tac `env' = nsOptBind n (HD [x]) env.v`
     >> qabbrev_tac `tenv' = opt_bind_name n 0 t1 tenvE`
     >> drule type_v_freevars
     >> rw []
     >> `tenv_val_exp_ok tenv'`
       by (Cases_on `n` >> fs [opt_bind_name_def, tenv_val_exp_ok_def, Abbr `tenv'`] >> NO_TAC)
     >> `type_all_env ctMap tenvS' env (tenv with v := add_tenvE tenvE tenv.v)`
       by metis_tac [type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
     >> first_x_assum drule
     >> rpt (disch_then drule)
     >> simp [PULL_EXISTS]
     >> disch_then (qspecl_then [`0`] mp_tac)
     >> `num_tvs tenv' = 0`
       by (Cases_on `n` >> fs [opt_bind_name_def, Abbr `tenv'`] >> NO_TAC)
     >> simp []
     >> `type_all_env ctMap tenvS' (env with v := env') (tenv with v := add_tenvE tenv' tenv.v)`
       by (
         fs [type_all_env_def, Abbr `env'`, Abbr `tenv'`]
         >> Cases_on `n`
         >> fs [opt_bind_name_def, namespaceTheory.nsOptBind_def, add_tenvE_def]
         >> irule nsAll2_nsBind
         >> simp [])
     >> disch_then drule
     >> rw []
     >> metis_tac [store_type_extension_trans])
   >- metis_tac [])
 >- (
   rename [`Letrec`]
   >> fs []
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> fs [PULL_EXISTS, is_value_def]
   >> first_x_assum irule
   >> fs []
   >> qexists_tac `tenv`
   >> qexists_tac `bind_var_list 0 bindings (bind_tvar tvs tenvE)`
   >> simp []
   >> rfs [build_rec_env_merge, bind_tvar_def, tenv_ok_def]
   >> rw []
   >- (
     irule tenv_val_exp_ok_bvl_funs
     >> simp []
     >> metis_tac [])
   >> fs [type_all_env_def]
   >> simp [build_rec_env_merge, nsAppend_to_nsBindList, add_tenvE_bvl]
   >> irule nsAll2_nsBindList
   >> simp []
   >> irule type_recfun_env
   >> simp [type_all_env_def]
   >> fs [fst_triple]
   >> metis_tac [tenv_ok_def])
 >- (
   CCONTR_TAC
   >> fs []
   >> rw []
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> metis_tac [type_funs_distinct])
 >- (
   rename [`Tannot`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> fs [PULL_EXISTS]
   >> first_x_assum irule
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >- (
   rename [`Lannot`]
   >> pop_assum mp_tac
   >> simp [Once type_e_cases]
   >> rw []
   >> rfs [is_value_def, bind_tvar_def]
   >> fs [PULL_EXISTS]
   >> first_x_assum irule
   >> rw []
   >> metis_tac [store_type_extension_refl])
 >- (
    pop_assum mp_tac
    >> simp [Once type_e_cases]
    >> rw[]
    >> rfs[is_value_def, bind_tvar_def]
    >> qpat_x_assum `_ = (_, _)` mp_tac
    >> ntac 2 (TOP_CASE_TAC >> fs[])
    >> first_x_assum drule
    >> rpt (disch_then drule)
    >> rename1 ‘type_e tenv tenvE e te’
    >> disch_then (qspecl_then [`[te]`, `tvs`] assume_tac)
    >> rpt strip_tac >> rveq >> fs[] >> res_tac >> rveq
    >> imp_res_tac do_fpoptimise_preserves_type_single
    >> first_x_assum (qspec_then `annot` assume_tac) >> fs[]
    >> asm_exists_tac >> fs[])
 >- (
    pop_assum mp_tac
    >> simp [Once type_e_cases]
    >> rw[]
    >> rfs[is_value_def, bind_tvar_def]
    >> qpat_x_assum `_ = (_, _)` mp_tac
    >> ntac 2 (TOP_CASE_TAC >> fs[])
    >> first_x_assum drule
    >> rpt (disch_then drule)
    >> rename1 ‘type_e tenv tenvE e te’
    >> disch_then (qspecl_then [`[te]`, `tvs`] assume_tac)
    >> rpt strip_tac >> rveq >> fs[] >> res_tac >> rveq
    >> imp_res_tac do_fpoptimise_preserves_type_single
    >> first_x_assum (qspec_then `annot` assume_tac) >> fs[]
    >> asm_exists_tac >> fs[])
 >- metis_tac [store_type_extension_refl]
 >- (
   fs [type_pes_def, RES_FORALL]
   >> first_assum (qspec_then `(p,e)` mp_tac)
   >> simp_tac (srw_ss()) []
   >> rw []
   >> imp_res_tac type_v_freevars
   >> fs []
   >> qpat_x_assum `type_v _ _ _ _ (Tapp [] TC_exn)` mp_tac
   >> drule (hd (CONJUNCTS pat_type_sound))
   >> fs [type_all_env_def]
   >> rpt (disch_then drule)
   >> disch_then (qspecl_then [`[]`, `[]`] mp_tac)
   >> rw []
   >> fs []
   >- (
     first_x_assum irule
     >> simp []
     >> metis_tac [])
   >- (
     `tenv_val_exp_ok (bind_var_list tvs bindings tenvE)`
       by metis_tac [type_p_bvl]
     >> rename1`pmatch _ _ _ _ _ = Match bindings'`
     >> `nsAll2 (λi v (tvs,t). type_v tvs ctMap tenvS v t)
           (nsAppend (alist_to_ns bindings') env.v)
           (add_tenvE (bind_var_list tvs bindings tenvE) tenv.v)`
       by (
         simp [nsAppend_to_nsBindList, add_tenvE_bvl]
         >> irule nsAll2_nsBindList
         >> simp []
         >> fs [LIST_REL_EL_EQN]
         >> rw []
         >> rfs []
         >> first_x_assum drule
         >> rpt (pairarg_tac >> simp [])
         >> fs []
         >> rfs [EL_MAP])
     >> first_x_assum drule
     >> simp []
     >> rpt (disch_then drule)
     >> simp []
     >> rpt (disch_then drule)
     >> disch_then (qspecl_then [`[t2]`, `0`] mp_tac)
     >> simp [bind_tvar_def]
     >> rw []
     >> Cases_on `r`
     >> fs []
     >> metis_tac [type_v_weakening, weakCT_refl, weakS_refl]))
 >- (
   CCONTR_TAC
   >> fs [type_pes_def, RES_FORALL]
   >> pop_assum (qspec_then `(p,e)` mp_tac)
   >> simp [])
QED

val let_tac =
  rw []
  >> Cases_on `r1`
  >> fs []
  >> rw []
  >- ( (* a value *)
    `type_all_env ctMap tenvS'' env tenv`
      by metis_tac [good_ctMap_def, type_all_env_weakening, weakCT_refl, store_type_extension_weakS]
    >> fs [good_ctMap_def, type_all_env_def]
    >> drule (CONJUNCT1 pat_type_sound)
    >> rpt (disch_then drule)
    >> disch_then (qspecl_then [`[]`, `[]`] mp_tac)
    >> rw []
    >- ( (* No match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> rw [weakCT_refl, type_v_exn, bind_exn_v_def] >>
      metis_tac [consistent_ctMap_def])
    >- ( (* match *)
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> simp [weakCT_refl]
      >> simp [extend_dec_env_def, extend_dec_tenv_def]
      >> fs []
      >> conj_asm1_tac
      >- (
        irule nsAll2_alist_to_ns
        >> fs [tenv_add_tvs_def, EVERY2_MAP, LAMBDA_PROD])
      >> conj_asm1_tac
      >- metis_tac [consistent_ctMap_def]
      >> irule nsAll2_nsAppend
      >> simp []))
  >- ( (* An exception *)
    Cases_on `e'`
    >> fs []
    >- (
      qexists_tac `ctMap`
      >> qexists_tac `tenvS''`
      >> fs [weakCT_refl, type_all_env_def, good_ctMap_def]
      >> conj_tac
      >- metis_tac [consistent_ctMap_def]
      >> irule nsAll2_mono
      >> qexists_tac `(λi v (tvs,t). type_v tvs ctMap tenvS v t)`
      >> rw []
      >> pairarg_tac
      >> fs []
      >> metis_tac [weakCT_refl, type_v_weakening, store_type_extension_weakS])
    >- metis_tac [DIFF_EQ_EMPTY, weakCT_refl]);

val build_tdefs_build_tenv = Q.prove (
  `!tenvT (tds : type_def) (tids : type_ident list) next (ctMap : ctMap).
    EVERY (λ(_, _, ctors). ALL_DISTINCT (MAP FST ctors)) tds ∧
    LENGTH tds = LENGTH tids ⇒
    nsAll2
      (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
      (build_tdefs next tds : env_ctor)
      (build_ctor_tenv tenvT tds tids)`,
  ho_match_mp_tac build_ctor_tenv_ind >>
  rw [build_tdefs_def, build_ctor_tenv_def, type_def_to_ctMap_def] >>
  fs [] >>
  irule nsAll2_nsAppend >>
  rw []
  >- (
    simp [REVERSE_APPEND] >>
    first_x_assum (qspecl_then [`next + 1`, `ctMap |++ MAP (λ(cn,ts). (TypeStamp cn next,tvs,MAP (type_name_subst tenvT) ts,id)) ctors`] assume_tac) >>
    irule (GEN_ALL nsAll2_mono) >>
    qexists_tac `
      type_ctor
           (ctMap |++
            MAP
              (λ(cn,ts).
                 (TypeStamp cn next,tvs,MAP (type_name_subst tenvT) ts,
                  id)) ctors |++
            REVERSE (type_def_to_ctMap tenvT (next + 1) tds tids))` >>
    rw [] >>
    rename1 `type_ctor _ _ stamp t` >>
    PairCases_on `stamp` >>
    PairCases_on `t` >>
    fs [type_ctor_def, flookup_fupdate_list, FLOOKUP_FUNION] >>
    every_case_tac >>
    fs [REVERSE_APPEND, ALOOKUP_APPEND] >>
    rw [])
  >- (
    irule nsAll2_alist_to_ns >>
    irule EVERY2_REVERSE >>
    simp [build_constrs_def, EVERY2_MAP] >>
    irule EVERY2_refl >>
    rw [] >>
    rpt (pairarg_tac >> fs []) >>
    rw [type_ctor_def, flookup_fupdate_list, ALOOKUP_APPEND] >>
    CASE_TAC
    >- (
      simp [] >>
      qmatch_goalsub_abbrev_tac `ALOOKUP (REVERSE l) _` >>
      `ALL_DISTINCT (MAP FST l)`
      by (
        rw [Abbr `l`, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        qpat_x_assum `ALL_DISTINCT _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        induct_on `ctors` >>
        rw [] >>
        fs [MEM_MAP] >>
        rw [] >>
        rpt (pairarg_tac >> fs []) >>
        metis_tac [FST]) >>
      simp [alookup_distinct_reverse] >>
      unabbrev_all_tac >>
      induct_on `ctors` >>
      rw [] >>
      rw [] >>
      fs [] >>
      rpt (pairarg_tac >> fs []) >>
      rw [] >>
      fs [MEM_MAP] >>
      metis_tac [FST])
    >- (
      drule ALOOKUP_MEM >>
      rw [] >>
      drule mem_type_def_to_ctMap >>
      rw [])));

val type_sound_invariant_union = Q.prove (
  `type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
   ⇒
   type_sound_invariant st env ctMap tenvS tids1 tenv`,
  rw [type_sound_invariant_def, consistent_ctMap_def] >>
  metis_tac []);

val check_ctor_tenv_dups = Q.prove (
  `!tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds`,
  ho_match_mp_tac check_ctor_tenv_ind >>
  rw [check_ctor_tenv_def]);

Theorem type_all_env_extend:
   type_all_env ctMap tenvS env1 tenv1
    /\ type_all_env ctMap tenvS env2 tenv2
    ==> type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2)
Proof
  fs [type_all_env_def, extend_dec_env_def, extend_dec_tenv_def]
  \\ metis_tac [nsAll2_nsAppend]
QED

Theorem type_e_con_check:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   every_exp (one_con_check envc) e) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (every_exp (one_con_check envc)) es) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (λ(f,n,e). every_exp (one_con_check envc) e) funs)
Proof
  ho_match_mp_tac type_e_strongind >>
  rw[]>>fs[]
  >- (
    fs [FORALL_PROD, RES_FORALL,EVERY_MEM]>>
    metis_tac[])
  >- (
    imp_res_tac nsAll2_nsLookup2>>
    fs[do_con_check_def]>>
    TOP_CASE_TAC>>rw[]>>
    fs[type_ctor_def]>>
    drule type_es_length>>simp[])
  >- metis_tac[ETA_AX]
  >- simp[do_con_check_def]
  >- metis_tac[ETA_AX]
  >- metis_tac[ETA_AX]
  >- (
    fs [FORALL_PROD, RES_FORALL,EVERY_MEM]>>
    metis_tac[])
QED

Theorem decs_type_sound_no_check:
  ∀(st:'ffi semanticPrimitives$state) env ds st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds F tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T
     | Rerr (Rabort(Rffi_error _)) => T
Proof
 ho_match_mp_tac evaluate_decs_ind
 >> rw [evaluate_decs_def]
 >> rw []
 >> TRY (qpat_x_assum `type_ds _ _ _ _ _ _ _` mp_tac >> simp [Once type_d_cases])
 >> rw []
 >- ( (* case [] *)
   simp [extend_dec_env_def, extend_dec_tenv_def, type_all_env_def]
   >> metis_tac [store_type_extension_refl, weakCT_refl, DIFF_EQ_EMPTY])
 >- ( (* case d1::d2::ds *)
   qpat_x_assum `type_ds _ _ (_::_::_) _ _` mp_tac >>
   simp [Once type_d_cases] >>
   rw [] >>
   split_pair_case_tac
   >> fs []
   >> rename1 `evaluate_decs _ _ _ = (st1, r1)`
   >> Cases_on `r1`
   >> fs []
   >- (
     split_pair_case_tac
     >> fs []
     >> rw []
     >> rename1 `evaluate_decs _ (extend_dec_env env1 _) _ = (st2, r2)`
     >> first_x_assum drule
     >> drule type_sound_invariant_union
     >> strip_tac
     >> disch_then drule
     >> rw []
     >> first_x_assum drule
     >> disch_then (qspecl_then [`ctMap''`, `tenvS''`] mp_tac)
     >> impl_keep_tac
     >- (
       fs [type_sound_invariant_def, consistent_ctMap_def]
       >> rw []
       >> fs [EXTENSION, SUBSET_DEF, DISJOINT_DEF]
       >> metis_tac [])
     >> rw []
     >> simp [combine_dec_result_def]
     >> rename[`weakCT ctMap1 ctMap`,`weakCT ctMap0 ctMap1`]
     >> qexists_tac `ctMap0`
     >> rename[`store_type_extenison tenvS tenvS0`,`store_type_extension tenvS0 tenvS1`]
     >> qexists_tac `tenvS1`
     >> rw []
     >- metis_tac [weakCT_trans]
     >- (
       fs [SUBSET_DEF, EXTENSION]
       >- metis_tac [])
     >- metis_tac [store_type_extension_trans]
     >> Cases_on `r2`
     >> fs []
     >- (
       fs [type_sound_invariant_def, good_ctMap_def, extend_dec_env_def]
       >> fs [extend_dec_tenv_def, extend_dec_env_def]
       >> `type_all_env ctMap0 tenvS1 env1 tenv1`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS]
       >> fs [type_all_env_def]
       >> metis_tac [nsAll2_nsAppend])
     >- (
       Cases_on `e`
       >> fs []
       >> fs [type_sound_invariant_def]
       >- metis_tac [type_all_env_weakening, weakCT_trans,
                     store_type_extension_weakS, store_type_extension_trans]))
   >- (
     rw []
     >> fs []
     >> first_x_assum drule
     >> drule type_sound_invariant_union
     >> strip_tac
     >> disch_then drule
     >> rw []
     >> qexists_tac `ctMap''`
     >> qexists_tac `tenvS''`
     >> rw[]
     >> fs [type_sound_invariant_def, consistent_ctMap_def,
            DISJOINT_DEF, EXTENSION, SUBSET_DEF]))
 >- ( (* case let *)
   split_pair_case_tac
   >> fs []
   >> rename1 `evaluate _ _ _ = (st1, r1)`
   >> FREEZE_THEN drule (hd (CONJUNCTS exp_type_sound))
   >> fs [type_sound_invariant_def]
   >> disch_then drule
   >> disch_then (qspec_then `Empty` mp_tac)
   >> simp [tenv_val_exp_ok_def, add_tenvE_def]
   >> rpt (disch_then drule)
   >> simp [type_es_list_rel, PULL_EXISTS]
   >> drule type_d_tenv_ok
   >> fs [Once type_d_cases]
   >> DISCH_TAC
   >> TRY ( (* Only for let poly case *)
     disch_then drule
     >> simp [bind_tvar_def])
   >> TRY ( (* Only for let mono case *)
     disch_then (qspec_then `0` mp_tac)
     >> simp [bind_tvar_def]
     >> disch_then drule)
   >- let_tac
   >- let_tac)
 >- ( (* case let, duplicate bindings *)
   fs [Once type_d_cases]
   >> fs [type_sound_invariant_def,type_all_env_def]
   >> metis_tac[type_e_con_check])
 >- ( (* case letrec *)
   drule type_d_tenv_ok
   >> fs [Once type_d_cases]
   >> rw []
   >> qexists_tac `ctMap`
   >> qexists_tac `tenvS`
   >> simp [weakCT_refl, store_type_extension_refl, build_rec_env_merge]
   >> fs [type_sound_invariant_def]
   >> fs [extend_dec_env_def, extend_dec_tenv_def]
   >> reverse conj_asm1_tac
   >- (
     fs [type_all_env_def]
     >> irule nsAll2_nsAppend
     >> simp [])
   >> `type_all_env ctMap tenvS env (tenv with v := add_tenvE Empty tenv.v)`
     by rw [add_tenvE_def]
   >> drule type_recfun_env
   >> rpt (disch_then drule)
   >> simp [tenv_val_exp_ok_def]
   >> disch_then drule
   >> strip_tac
   >> fs [type_all_env_def, fst_triple]
   >> irule nsAll2_alist_to_ns
   >> rfs [EVERY2_MAP, tenv_add_tvs_def])
 >- ( (* case letrec duplicate bindings *)
   fs [Once type_d_cases]
   >- metis_tac [type_funs_distinct]
   >> fs [type_sound_invariant_def,type_all_env_def]
   >> metis_tac[type_e_con_check,NOT_EVERY])
 >- ( (* case type definition *)
   drule type_d_tenv_ok
   >> fs [Once type_d_cases]
   >> rw [extend_dec_env_def]
   >> fs [type_sound_invariant_def]
   >> qmatch_assum_abbrev_tac `check_ctor_tenv new_tabbrev _`
   >> qexists_tac `FUNION (FEMPTY |++ REVERSE (type_def_to_ctMap new_tabbrev st.next_type_stamp tds type_identities)) ctMap`
   >> qexists_tac `tenvS`
   >> simp [store_type_extension_refl] >>
   `!cn1 cn2 tid.
     FLOOKUP ctMap (TypeStamp cn1 tid) ≠ NONE ⇒
     ALOOKUP (type_def_to_ctMap new_tabbrev st.next_type_stamp tds type_identities)
       (TypeStamp cn2 tid) = NONE`
   by (
     fs [consistent_ctMap_def] >>
     rw [ALOOKUP_NONE] >>
     `tid < st.next_type_stamp` by metis_tac [FDOM_FLOOKUP, option_nchotomy] >>
     CCONTR_TAC >>
     fs [MEM_MAP] >>
     rename [`TypeStamp _ _ = FST x`] >>
     PairCases_on `x` >>
     imp_res_tac mem_type_def_to_ctMap >>
     rfs [] >>
     rw [] >>
     decide_tac) >>
   conj_asm1_tac
   >- (
     irule disjoint_env_weakCT >>
     fs [DISJOINT_DEF, EXTENSION, consistent_ctMap_def, FDOM_FUPDATE_LIST,
         MEM_MAP] >>
     rw [] >>
     CCONTR_TAC >>
     fs [FDOM_FUPDATE_LIST] >>
     rw [] >>
     rename1 `FST stamp ∈ FDOM _` >>
     PairCases_on `stamp` >>
     drule mem_type_def_to_ctMap >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >>
     res_tac >>
     decide_tac) >>
   conj_asm1_tac
   >- (
     rw [SUBSET_DEF, FRANGE_FLOOKUP, FLOOKUP_o_f] >>
     every_case_tac >>
     fs [FLOOKUP_FUNION, flookup_fupdate_list] >>
     Cases_on `ALOOKUP
                (type_def_to_ctMap new_tabbrev st.next_type_stamp tds type_identities)
                k` >>
     fs []
     >- (
       first_x_assum (qspec_then `k` mp_tac) >>
       simp []) >>
     drule type_def_to_ctMap_mem >>
     simp []) >>
   conj_asm1_tac
   >- (
     fs [type_all_env_def, GSYM fupdate_list_funion] >>
     irule build_tdefs_build_tenv >>
     simp [] >>
     qpat_x_assum `check_ctor_tenv _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     induct_on `tds` >>
     rw [] >>
     rename1 `check_ctor_tenv _ (td::_)` >>
     PairCases_on `td` >>
     fs [check_ctor_tenv_def, check_dup_ctors_thm])
   >> conj_asm1_tac
   >- (
     fs [good_ctMap_def]
     >> rw []
     >- (
       irule ctMap_ok_merge_imp
       >> simp []
       >> conj_tac >- (
         irule ctMap_ok_type_defs >>
         simp [] >>
         fs [tenv_ok_def, extend_dec_tenv_def, Abbr `new_tabbrev`]) >>
       fs [consistent_ctMap_def, DISJOINT_DEF, EXTENSION, flookup_fupdate_list, FRANGE_FLOOKUP, FLOOKUP_o_f] >>
       CCONTR_TAC >>
       fs [] >>
       every_case_tac >>
       fs [] >>
       rw [] >>
       drule type_def_to_ctMap_mem >>
       rw [] >>
       fs [] >>
       CCONTR_TAC >>
       fs [PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
       rpt (last_x_assum drule) >>
       rename [`FLOOKUP ctMap k = SOME v`] >>
       rpt strip_tac >>
       first_x_assum (qspec_then `k` mp_tac) >>
       simp [])
     >- (
       fs [ctMap_has_bools_def, FLOOKUP_FUNION] >>
       rw [flookup_fupdate_list] >>
       every_case_tac >>
       metis_tac [NOT_SOME_NONE])
     >- (
       fs [ctMap_has_exns_def, FLOOKUP_FUNION] >>
       rw [flookup_fupdate_list] >>
       every_case_tac >>
       imp_res_tac ALOOKUP_MEM >>
       imp_res_tac mem_type_def_to_ctMap >>
       rfs [bind_stamp_def, chr_stamp_def, div_stamp_def, subscript_stamp_def])
     >- (
       fs [ctMap_has_lists_def, FLOOKUP_FUNION] >>
       rw [flookup_fupdate_list] >>
       every_case_tac >>
       metis_tac [NOT_SOME_NONE]))
   >> conj_tac
   >- (
     fs [consistent_ctMap_def] >>
     rw [FDOM_FUPDATE_LIST, MEM_MAP]
     >- (
       rename [`TypeStamp _ _ = FST x`] >>
       PairCases_on `x` >>
       imp_res_tac mem_type_def_to_ctMap >>
       rfs [] >>
       rw [] >>
       rw [])
     >- (
       res_tac >>
       decide_tac)
     >- (
       rename [`ExnStamp _ = FST YYY`] >>
       PairCases_on `YYY` >>
       imp_res_tac mem_type_def_to_ctMap >>
       rfs [] >>
       rw [])
     >- (
       res_tac >>
       decide_tac))
   >> conj_tac
   >- (
     `type_all_env (FEMPTY |++ REVERSE (type_def_to_ctMap new_tabbrev st.next_type_stamp tds type_identities) ⊌ ctMap) tenvS env tenv`
     by metis_tac [type_all_env_weakening, weakS_refl] >>
     fs [type_all_env_def, extend_dec_tenv_def] >>
     rw [] >>
     irule nsAll2_nsAppend
     >> simp [])
   >- metis_tac [type_s_weakening, good_ctMap_def])
 >- ( (* case type def not distinct *)
   fs [Once type_d_cases] >>
   rw [] >>
   drule check_ctor_tenv_dups >>
   rw [])
 >- ( (* case type abbrev *)
   drule type_d_tenv_ok
   >> fs [Once type_d_cases]
   >> rw [extend_dec_env_def, extend_dec_tenv_def]
   >> qexists_tac `ctMap`
   >> qexists_tac `tenvS`
   >> rw [weakCT_refl, store_type_extension_refl]
   >> fs [type_sound_invariant_def, type_all_env_def])
 >- (rename [`Denv`] \\ fs [Once type_d_cases])
 >- ( (* case exception *)
   drule type_d_tenv_ok
   >> fs [Once type_d_cases]
   >> rw []
   >> fs [type_sound_invariant_def]
   >> qexists_tac `FUNION (FEMPTY |+ (ExnStamp st.next_exn_stamp,([],MAP (type_name_subst tenv.t) ts, Texn_num))) ctMap`
   >> qexists_tac `tenvS`
   >> simp [store_type_extension_refl]
   >> rfs []
   >> conj_asm1_tac
   >- (
     irule disjoint_env_weakCT
     >> simp []
     >> CCONTR_TAC
     >> fs [consistent_ctMap_def, RES_FORALL]
     >> res_tac
     >> fs []) >>
   conj_asm1_tac
   >- (
     rw [o_f_FUPDATE, o_f_FUNION] >>
     rw [EXTENSION, IN_FRANGE, FUNION_DEF] >>
     CCONTR_TAC >>
     fs [consistent_ctMap_def, good_ctMap_def, ctMap_has_exns_def, FLOOKUP_DEF] >>
     rw []
     >- (
       pop_assum (qspec_then `bind_stamp` mp_tac) >>
       rw []) >>
     pop_assum (qspec_then `k` mp_tac) >>
     rw [] >>
     res_tac >>
     fs [])
   >> conj_asm1_tac
   >- (
     fs [type_all_env_def]
     >> simp [type_ctor_def, FLOOKUP_FUNION, namespaceTheory.id_to_n_def, FLOOKUP_UPDATE])
   >> conj_asm1_tac
   >- (
     fs [good_ctMap_def, ctMap_ok_def] >>
     rw []
     >- (
       irule fevery_funion >>
       rw [FEVERY_FUPDATE, FEVERY_FEMPTY] >>
       simp [EVERY_MAP] >>
       fs [EVERY_MEM] >>
       rw [MEM_MAP] >>
       metis_tac [check_freevars_type_name_subst, tenv_ok_def])
     >- (
       fs [FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       every_case_tac >>
       fs [] >>
       metis_tac [])
     >- (
       fs [FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       every_case_tac >>
       fs [] >>
       metis_tac [])
     >- (
       fs [FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       every_case_tac >>
       fs [] >>
       metis_tac [])
     >- (
       fs [FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       every_case_tac >>
       fs [same_type_refl] >>
       rw []
       >- (
         Cases_on `stamp1` >>
         fs [] >>
         res_tac >>
         fs [prim_type_nums_def, same_type_def])
       >- (
         Cases_on `stamp2` >>
         fs [] >>
         res_tac >>
         fs [prim_type_nums_def, same_type_def]))
     >- (
       simp [ctMap_has_bools_def, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       metis_tac [ctMap_has_bools_def])
     >- (
       simp [ctMap_has_exns_def, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       rw [] >>
       fs [consistent_ctMap_def, ctMap_has_exns_def] >>
       fs [FLOOKUP_DEF, bind_stamp_def, chr_stamp_def, div_stamp_def, subscript_stamp_def] >>
       res_tac >>
       fs [])
     >- (
       simp [ctMap_has_lists_def, FLOOKUP_FUNION, FLOOKUP_UPDATE] >>
       metis_tac [ctMap_has_lists_def, Tlist_def]))
   >> conj_tac
   >- (
     fs [consistent_ctMap_def] >>
     rw [] >>
     rw []
     >- metis_tac [] >>
     res_tac >>
     decide_tac)
   >> conj_tac
   >- (
     qmatch_assum_abbrev_tac `weakCT ctMap' _`
     >> `type_all_env ctMap' tenvS env tenv`
       by metis_tac [type_all_env_weakening, weakS_refl]
     >> fs [type_all_env_def, extend_dec_tenv_def, extend_dec_env_def]
     >> irule nsAll2_nsBind
     >> simp [])
   >- metis_tac [type_s_weakening, good_ctMap_def])
 >- ( (* Case module *)
   qpat_x_assum `type_d _ _ (Dmod _ _) _ _` mp_tac >>
   rw [Once type_d_cases] >>
   split_pair_case_tac >>
   fs [] >>
   rename [`evaluate_decs _ _ _ = (st1, r1)`] >>
   Cases_on `r1` >>
   fs [] >>
   rw []
   >- (
     first_x_assum drule >>
     disch_then drule >>
     rw [] >>
     rename [`weakCT ctMap1 _`] >>
     qexists_tac `ctMap1` >>
     rw [] >>
     rename [`store_type_extension _ tenvS1`] >>
     qexists_tac `tenvS1` >>
     rw []
     >- (
       fs [type_all_env_def, tenvLift_def] >>
       irule nsAll2_mono >>
       qexists_tac `type_ctor ctMap1` >>
       rw [] >>
       rename [`type_ctor _ _ arg1 arg2`] >>
       PairCases_on `arg1` >>
       PairCases_on `arg2` >>
       fs [type_ctor_def])
     >- (
       fs [type_sound_invariant_def] >>
       rw []
       >- (
         irule extend_dec_tenv_ok >>
         fs [tenvLift_def, tenv_ok_def, tenv_val_ok_def,
             tenv_ctor_ok_def, tenv_abbrev_ok_def,
             extend_dec_tenv_def] >>
         metis_tac [nsAll_nsAppend_left])
       >- (
         `type_all_env ctMap1 tenvS1 env tenv`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS] >>
         fs [type_all_env_def, extend_dec_env_def, extend_dec_tenv_def] >>
         rw [] >>
         irule nsAll2_nsAppend >>
         rw [tenvLift_def] >>
         irule nsAll2_mono >>
         qexists_tac `type_ctor ctMap1` >>
         rw [] >>
         rename [`type_ctor _ _ arg1 arg2`] >>
         PairCases_on `arg1` >>
         PairCases_on `arg2` >>
         fs [type_ctor_def])))
   >- (
     first_x_assum drule >>
     disch_then drule >>
     rw []))
 >- ( (* case local *)
   qpat_x_assum `type_d _ _ (Dlocal _ _) _ _` mp_tac
   >> rw [Once type_d_cases]
   >> Cases_on `evaluate_decs st env ds`
   >> fs []
   >> rename1 `evaluate_decs st _ _ = (st1, r1)`
   >> first_x_assum drule
   >> first_assum (assume_tac o MATCH_MP type_sound_invariant_union)
   >> disch_then drule
   >> Cases_on `r1` >> fs []
   >- (
     rw []
     >> rename1 `evaluate_decs _ (extend_dec_env env1 _) _ = (st2, r2)`
     >> first_x_assum drule
     >> disch_then (mp_tac o Q.SPECL [`ctMap'`, `tenvS'`])
     >> impl_keep_tac
     >- (
       fs [type_sound_invariant_def, consistent_ctMap_def,
         boolTheory.FORALL_AND_THM, DISJOINT_DEF, SUBSET_DEF, EXTENSION]
       >> metis_tac []
     )
     >> rpt (ho_match_mp_tac boolTheory.MONO_EXISTS \\ GEN_TAC)
     >> rw []
     >- metis_tac [weakCT_trans]
     >- (
       fs [SUBSET_DEF, EXTENSION]
       >- metis_tac [])
     >- metis_tac [store_type_extension_trans]
     >- (
       CASE_TAC \\ fs []
       >- (
         fs [type_sound_invariant_def]
         \\ fs (BODY_CONJUNCTS type_d_tenv_ok_helper @ [extend_dec_tenv_ok])
         \\ conj_tac
         >- metis_tac [type_d_tenv_ok_helper, extend_dec_tenv_ok]
         >> match_mp_tac type_all_env_extend
         >> fs []
         >> metis_tac [type_all_env_weakening, weakCT_trans, store_type_extension_weakS]
       )
       >> CASE_TAC >> fs []
       >> fs [type_sound_invariant_def]
       >> metis_tac [type_all_env_weakening, weakCT_trans, store_type_extension_weakS]
     )
   )
   >- (
     rveq
     >> fs []
     >> rpt (ho_match_mp_tac boolTheory.MONO_EXISTS \\ GEN_TAC)
     >> rw []
     >> metis_tac [SUBSET_TRANS, SUBSET_UNION]
   )
 )
QED

Theorem decs_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds extra_checks tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort (Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
Proof
  rw [] >>
  imp_res_tac type_d_check_uniq >>
  imp_res_tac decs_type_sound_no_check >>
  qexists_tac `ctMap'` >>
  qexists_tac `tenvS'` >>
  Cases_on `r` >>
  fs []
QED

     (*
val type_sound_invariant_def = Define `
type_sound_invariant st env tdecs ctMap tenvS tenv ⇔
  ?tdecs_no_sig tenv_no_sig.
    decls_ok tdecs_no_sig ∧
    tenv_ok tenv ∧
    tenv_ok tenv_no_sig ∧
    good_ctMap ctMap ∧
    weak tenv_no_sig tenv ∧
    type_all_env ctMap tenvS env tenv_no_sig ∧
    type_s ctMap st.refs tenvS ∧
    weak_decls tdecs_no_sig tdecs ∧
    weak_decls_only_mods tdecs_no_sig tdecs ∧
    consistent_decls st.defined_types tdecs_no_sig ∧
    consistent_ctMap tdecs_no_sig ctMap ∧
    st.defined_mods ⊆ tdecs_no_sig.defined_mods`;

val tscheme_inst2_lemma = Q.prove (
  `(λid. tscheme_inst2 (Long mn id)) = tscheme_inst2`,
 rw [FUN_EQ_THM]
 >> PairCases_on `x`
 >> PairCases_on `x'`
 >> rw [tscheme_inst2_def]);

Theorem tops_type_sound_no_extra_checks:
  ∀(st:'ffi semanticPrimitives$state) env tops st' env' r tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_tops st env tops = (st',r) ∧
   type_prog F tdecs1 tenv tops tdecs1' tenv' ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_sound_invariant st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort(Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
Proof
 ho_match_mp_tac evaluate_tops_ind
 >> rw [evaluate_tops_def]
 >- (
   rw [extend_dec_env_def, extend_dec_tenv_def, type_all_env_def]
   >> metis_tac [weakCT_refl, store_type_extension_refl])
 >- (
   qpat_x_assum `type_prog F _ _ (_::_::_) _ _` mp_tac
   >> simp [Once type_prog_cases]
   >> rw []
   >> split_pair_case_tac
   >> rename1 `evaluate_tops st env [top1] = (st1, r1)`
   >> fs []
   >> Cases_on `r1`
   >> fs []
   >- (
     split_pair_case_tac
     >> fs []
     >> rw []
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> rename1 `weakCT ctMap1 ctMap`
     >> rename1 `store_type_extension tenvS tenvS1`
     >> first_x_assum drule
     >> disch_then drule
     >> rw []
     >> rename1 `weakCT ctMap2 ctMap1`
     >> rename1 `store_type_extension tenvS1 tenvS2`
     >> rename1 `evaluate_tops _ _ (_::_) = (st2, r2)`
     >> Cases_on `r2`
     >> fs []
     >- (
       qexists_tac `ctMap2`
       >> qexists_tac `tenvS2`
       >> rw []
       >- metis_tac [weakCT_trans]
       >- metis_tac [store_type_extension_trans]
       (* >> `type_all_env ctMap2 tenvS2 a tenv1`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS] *)
       >> simp [combine_dec_result_def]
       >> fs [extend_dec_env_def, type_all_env_def, extend_dec_tenv_def]
       >> metis_tac [nsAll2_nsAppend])
     >- (
       simp [combine_dec_result_def]
       >> CASE_TAC
       >> fs []
       >- (
         qexists_tac `ctMap2`
         >> qexists_tac `tenvS2`
         >> rw []
         >- metis_tac [weakCT_trans]
         >- metis_tac [store_type_extension_trans]
         >> fs [type_sound_invariant_def]
         >> qexists_tac `tdecs_no_sig''`
         >> qexists_tac `tenv_no_sig`
         >> rw []
         >> metis_tac [type_all_env_weakening, weakCT_trans, store_type_extension_trans,
                       store_type_extension_weakS, good_ctMap_def])
       >- metis_tac []))
   >- (
     first_x_assum drule
     >> disch_then drule
     >> rw []
     >> CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> fs [type_sound_invariant_def]
       >> qexists_tac `union_decls decls2 tdecs_no_sig'`
       >> qexists_tac `tenv_no_sig'`
       >> simp []
       >> rw []
       >- metis_tac [decls_ok_union, type_prog_decls_ok]
       >> fs [SUBSET_DEF]
       >> metis_tac [weak_decls_union, union_decls_assoc, weak_decls_only_mods_union, consistent_ctMap_union2, consistent_decls_union2])
     >- metis_tac []))
 >- (
   fs [type_top_cases]
   >> rename1 `evaluate_decs _ _ _ [_] = (st1, r1)`
   >> fs []
   >> drule decs_type_sound
   >> fs [type_sound_invariant_def]
   >> `type_d F [] tdecs_no_sig tenv_no_sig d tdecs1' tenv'`
     by (
       irule type_d_weakening
       >> qexists_tac `tdecs1`
       >> qexists_tac `tenv`
       >> rw []
       >> metis_tac [tenv_ok_def, weak_decls_other_mods_only_mods_NIL])
   >> disch_then drule
   >> `decs_type_sound_invariant [] st env tdecs_no_sig ctMap tenvS tenv_no_sig`
     by fs [decs_type_sound_invariant_def, tenv_ok_def, decls_ok_def]
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     qexists_tac `ctMap''`
     >> qexists_tac `tenvS''`
     >> rw []
     >> rename1 `type_all_env _ _ env' tenv'`
     >> qexists_tac `union_decls tdecs1' tdecs_no_sig`
     >> qexists_tac `extend_dec_tenv tenv' tenv_no_sig`
     >> fs [type_sound_invariant_def, decs_type_sound_invariant_def, SUBSET_DEF]
     >> rw []
     >- (
       irule decls_ok_union
       >> simp []
       >> drule type_d_mod
       >> rw [decls_ok_def])
     >- metis_tac [type_d_tenv_ok]
     >- (
       fs [weak_def]
       >> rw []
       >- fs [extend_dec_tenv_def]
       >> irule weak_tenv_extend_dec_tenv
       >> simp []
       >> drule type_d_tenv_ok_helper
       >> fs [tenv_ok_def, extend_dec_tenv_def])
     >- metis_tac [weak_decls_union]
     >- metis_tac [weak_decls_only_mods_union]
     >- metis_tac [evaluate_decs_state_unchanged])
   >- (
     CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> qexists_tac `union_decls tdecs1' tdecs_no_sig`
       >> qexists_tac `tenv_no_sig`
       >> fs [type_sound_invariant_def, decs_type_sound_invariant_def, SUBSET_DEF]
       >> rw []
       >- (
         irule decls_ok_union
         >> simp []
         >> drule type_d_mod
         >> rw [decls_ok_def])
       >- metis_tac [weak_decls_union]
       >- metis_tac [weak_decls_only_mods_union]
       >- metis_tac [evaluate_decs_state_unchanged])
     >- metis_tac []))
 >- (
   split_pair_case_tac
   >> rename1 `evaluate_decs _ _ _ _ = (st1, r1)`
   >> drule type_top_decls_ok
   >> fs [type_top_cases]
   >> rw []
   >> drule decs_type_sound
   >> fs [type_sound_invariant_def]
   >> `type_ds F [mn] tdecs_no_sig tenv_no_sig ds decls_impl tenv_impl`
     by (
       irule type_ds_weakening
       >> simp []
       >> qexists_tac `tdecs1`
       >> qexists_tac `tenv`
       >> rw []
       >> irule weak_decls_other_mods_only_mods_SOME
       >> simp [])
   >> disch_then drule
   >> `decs_type_sound_invariant [mn] st env tdecs_no_sig ctMap tenvS tenv_no_sig`
     by (fs [decs_type_sound_invariant_def, type_sound_invariant_def,
             weak_decls_def,tenv_ok_def])
   >> disch_then drule
   >> rw []
   >> Cases_on `r1`
   >> fs []
   >> rw []
   >- (
     qexists_tac `ctMap''`
     >> qexists_tac `tenvS''`
     >> fs [type_sound_invariant_def, decs_type_sound_invariant_def]
     >> qexists_tac `union_decls (union_decls <|defined_mods := {[mn]}; defined_types := ∅; defined_exns := ∅ |> decls_impl) tdecs_no_sig`
     >> rename1 `type_all_env _ _ (extend_dec_env env' _) _`
     >> qexists_tac `extend_dec_tenv <| v := nsLift mn tenv_impl.v; c := nsLift mn tenv_impl.c; t := nsLift mn tenv_spec.t |> tenv_no_sig`
     >> simp [union_decls_mods]
     >> conj_asm1_tac
     >- (
       drule type_ds_decls_ok
       >> simp []
       >> metis_tac [decls_ok_union])
     >> conj_asm1_tac
     >- (
       drule check_signature_tenv_ok
       >> simp [tenvLift_def]
       >> disch_then irule
       >> simp []
       >> metis_tac [])
     >> conj_asm1_tac
     >- (
       drule type_ds_tenv_ok_helper
       >> simp []
       >> rw []
       >> irule extend_dec_tenv_ok
       >> simp []
       >> fs [tenv_ok_def, tenv_ctor_ok_def, tenv_val_ok_def, tenv_abbrev_ok_def]
       >> fs [check_signature_cases]
       >> drule type_specs_tenv_ok
       >> simp [tenv_abbrev_ok_def, tenv_ok_def])
     >> rw []
     >- (
       fs [weak_def]
       >> rw []
       >- fs [extend_dec_tenv_def, tenvLift_def]
       >> fs [check_signature_cases]
       >- (
         rw [tenvLift_def]
         >> irule weak_tenv_extend_dec_tenv
         >> simp [tenv_val_ok_def]
         >> drule type_ds_tenv_ok_helper
         >> rw [tenv_ok_def, tenv_val_ok_def])
       >> fs [weak_tenv_def, extend_dec_tenv_def, tenvLift_def]
       >> rw []
       >> irule nsSub_nsAppend_lift
       >> simp [tscheme_inst2_lemma, type_ctor_long] >> conj_tac
       >- metis_tac []
       >> irule nsSub_refl
       >> qexists_tac `\x y. T`
       >> rw []
       >> PairCases_on `x`
       >> rw [weak_tenvT_def])
     >- (
       `type_all_env ctMap'' tenvS'' env tenv_no_sig`
         by metis_tac [type_all_env_weakening, store_type_extension_weakS]
       >> rw [type_all_env_def, extend_dec_env_def, extend_dec_tenv_def]
       >> irule nsAll2_nsAppend
       >> simp []
       >> fs [type_all_env_def, type_ctor_long]
       >> metis_tac [])
     >- (
       fs [check_signature_cases]
       >> metis_tac [weak_decls_union3, weak_decls_union, weak_decls_trans])
       >- (
         fs [check_signature_cases]
         >- metis_tac [weak_decls_only_mods_union]
         >> rw_tac std_ss [GSYM union_decls_assoc]
         >> irule weak_decls_only_mods_union
         >> irule weak_decls_only_mods_union2
         >> simp []
         >> drule type_ds_weak_decls_only_mods
         >> simp [])
     >- metis_tac [consistent_decls_union2, union_decls_assoc]
     >- metis_tac [consistent_ctMap_union2, union_decls_assoc]
     >- (
       fs [SUBSET_DEF]
       >> metis_tac [evaluate_decs_state_unchanged]))
   >- (
     CASE_TAC
     >> fs []
     >- (
       qexists_tac `ctMap''`
       >> qexists_tac `tenvS''`
       >> simp []
       >> fs [type_sound_invariant_def, decs_type_sound_invariant_def]
       >> qexists_tac `union_decls (union_decls <|defined_mods := {[mn]}; defined_types := ∅; defined_exns := ∅ |> decls_impl) tdecs_no_sig`
       >> qexists_tac `tenv_no_sig`
       >> simp [union_decls_mods]
       >> rw []
       >- (
         drule type_ds_decls_ok
         >> simp []
         >> metis_tac [decls_ok_union])
       >- (
         fs [check_signature_cases]
         >> metis_tac [weak_decls_union, weak_decls_trans, weak_decls_union3])
       >- (
         fs [check_signature_cases]
         >- metis_tac [weak_decls_only_mods_union]
         >> rw_tac std_ss [GSYM union_decls_assoc]
         >> irule weak_decls_only_mods_union
         >> irule weak_decls_only_mods_union2
         >> simp []
         >> drule type_ds_weak_decls_only_mods
         >> simp [])
       >- metis_tac [consistent_decls_union2, union_decls_assoc]
       >- metis_tac [consistent_ctMap_union2, union_decls_assoc]
       >- (
         fs [SUBSET_DEF]
         >> metis_tac [evaluate_decs_state_unchanged]))
     >- metis_tac []))
 >- (
   fs [type_top_cases]
   >- (
     fs [type_sound_invariant_def, SUBSET_DEF]
     >> metis_tac [weak_decls_def])
   >- metis_tac [type_ds_no_dup_types, pair_CASES])
QED

Theorem tops_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops st' r checks tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_tops st env tops = (st',r) ∧
   type_prog checks tdecs1 tenv tops tdecs1' tenv' ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_sound_invariant st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort(Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
Proof
 rpt strip_tac
 >> irule tops_type_sound_no_extra_checks
 >> qexists_tac `st`
 >> qexists_tac `tops`
 >> rw []
 >> irule type_prog_check_uniq
 >> metis_tac []
QED

Theorem prog_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops st' r checks tdecs1 ctMap tenvS tenv tdecs1' tenv'.
   evaluate_prog st env tops = (st',r) ∧
   type_prog checks tdecs1 tenv tops tdecs1' tenv' ∧
   type_sound_invariant st env tdecs1 ctMap tenvS tenv ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_sound_invariant st' (extend_dec_env env' env)
         (union_decls tdecs1' tdecs1) ctMap' tenvS' (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env (union_decls tdecs1' tdecs1) ctMap' tenvS' tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort(Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T
Proof
 REWRITE_TAC [evaluate_prog_def]
 >> rpt strip_tac
 >> irule tops_type_sound
 >> fs []
 >> qexists_tac `checks`
 >> qexists_tac `st`
 >> qexists_tac `tops`
 >> rw []
 >> every_case_tac
 >> fs []
 >- (
   drule type_no_dup_mods
   >> fs [type_sound_invariant_def, no_dup_mods_def, DISJOINT_DEF, EXTENSION, SUBSET_DEF]
   >> rw []
   >> metis_tac [weak_decls_def])
 >- (
   drule type_no_dup_top_types
   >> fs [type_sound_invariant_def]
   >> rpt (disch_then drule)
   >> fs [no_dup_top_types_def, DISJOINT_DEF, EXTENSION, SUBSET_DEF]
   >> rw []
   >> metis_tac [weak_decls_def])
QED

   *)

Theorem semantics_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops r checks ctMap tenvS tenv new_tenv tids.
   semantics_prog st env tops r ∧
   type_ds checks tenv tops tids new_tenv ∧
   type_sound_invariant st env ctMap tenvS tids tenv ⇒
   r ≠ Fail
Proof
 rw []
 >> CCONTR_TAC
 >> fs [semantics_prog_def]
 >> Cases_on `evaluate_prog_with_clock st env k tops`
 >> fs []
 >> rw []
 >> fs [evaluate_prog_with_clock_def]
 >> pairarg_tac
 >> fs []
 >> rw []
 >> drule decs_type_sound
 >> disch_then drule
 >> simp []
 >> fs [type_sound_invariant_def]
 >> fs [consistent_ctMap_def]
 >> metis_tac []
QED

val _ = export_theory ();
