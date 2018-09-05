open HolKernel boolLib boolSimps bossLib lcsymtacs holSyntaxTheory holSyntaxExtraTheory setSpecTheory

val _ = new_theory"holSemantics"

val mem = ``mem:'U->'U->bool``

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[DB.fetch"holSyntax""type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val _ = Parse.overload_on("inhabited",``λs. ∃x. x <: s``)

val (builtin_closure_rules,builtin_closure_ind,builtin_closure_cases) = Hol_reln `
  (!T ty. T ty ==> builtin_closure T ty)
  /\ (!T. builtin_closure T Bool)
  /\ (!T ty1 ty2. builtin_closure T ty1 /\ builtin_closure T ty2
        ==> builtin_closure T (Fun ty1 ty2))`

val ground_types_def = Define `
  ground_types =
  {ty | tyvars ty = []}
  `

val ground_consts_def = Define `
  ground_consts =
  {c:(mlstring#type) | SND c ∈ ground_types}
  `

val nonbuiltin_types_def = Define `nonbuiltin_types = {ty | ¬is_builtin_type ty}`

val builtin_consts =
  Define `builtin_consts = {(s,ty) | s = strlit "=" /\ ?ty'. ty = Fun ty' (Fun ty' Bool)}`

val nonbuiltin_constinsts_def =
  Define `nonbuiltin_constinsts = {c | c ∉ builtin_consts}`

val consts_of_term_def = Define
  `(consts_of_term(Abs x y) = consts_of_term x ∪ consts_of_term y) /\
   (consts_of_term(Comb x y) = consts_of_term x ∪ consts_of_term y) /\
   (consts_of_term(Const n ty) = {(n,ty)}) /\
   (consts_of_term _ = {})`

val is_sig_fragment_def = Define
  `is_sig_fragment (tys,consts) =
   (tys ⊆ ground_types ∧ tys ⊆ nonbuiltin_types
    ∧ consts ⊆ ground_consts ∧ consts ⊆ nonbuiltin_constinsts
    ∧ (!s c. (s,c) ∈ consts ==> c ∈ builtin_closure tys)
   )
  `

val terms_of_frag_def = Define
  `terms_of_frag (tys,consts) =
   {t | consts_of_term t ∩ nonbuiltin_constinsts ⊆ consts
        /\ set(allTypes t) ⊆ tys /\ welltyped t}
  `

val ground_terms_def = Define
  `ground_terms = {t | ?ty. t has_type ty /\ ty ∈ ground_types}`

val types_of_frag_def = Define
  `types_of_frag (tys,consts) = builtin_closure tys`

(* Lemma 8 from Andrei&Ondra, should go elsewhere*)

val allTypes_no_tyvars = Q.prove(
  `!ty. (∀x. x ∈ q ⇒ tyvars x = [])
        /\ (∀x. MEM x (allTypes' ty) ⇒ x ∈ q)
        ==> tyvars ty = []`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >> fs[allTypes'_def]
  >> BasicProvers.PURE_FULL_CASE_TAC >- fs[tyvars_def]
  >> qpat_x_assum `!x. _` mp_tac >> simp[] >> strip_tac
  >> BasicProvers.PURE_FULL_CASE_TAC
  >- (Cases_on `l` >- fs[tyvars_def]
      >> rename1 `ty::tys` >> Cases_on `tys` >> fs[]
      >> qmatch_goalsub_abbrev_tac `a1 = a2`
      >> `set a1 = set a2` suffices_by(unabbrev_all_tac >> simp[])
      >> unabbrev_all_tac
      >> simp[tyvars_def])
  >> fs[]);

val allTypes_no_tyvars2 = Q.prove(
  `!tm ty1 ty2. tm has_type ty1 /\
           MEM ty2 (allTypes' ty1)
           ==> MEM ty2 (allTypes tm)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac has_type_strongind
  >> rw[allTypes_def,allTypes'_def] >> fs[]);

val builtin_closure_tyvars = Q.prove(
  `∀q x. x ∈ builtin_closure q /\ (∀x. x ∈ q ⇒ tyvars x = []) ==> tyvars x = []`,
  simp [IN_DEF,GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac builtin_closure_ind
  >> rw[tyvars_def]);

val builtin_closure_allTypes' = Q.prove(
  `!ty q. (∀x. MEM x (allTypes' ty) ⇒ x ∈ q) ==> ty ∈ builtin_closure q`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (fs[allTypes'_def,boolTheory.IN_DEF] >> metis_tac[builtin_closure_rules])
  >- (fs[allTypes'_def,listTheory.EVERY_MEM]
      >> BasicProvers.PURE_FULL_CASE_TAC
      >- fs[builtin_closure_rules,boolTheory.IN_DEF]
      >> qpat_x_assum `!x. _` mp_tac >> simp[]
      >> BasicProvers.PURE_FULL_CASE_TAC >> simp[builtin_closure_rules,boolTheory.IN_DEF]
      >> Cases_on `l` >- fs[tyvars_def]
      >> rename1 `ty::tys` >> Cases_on `tys` >> fs[] >> rpt strip_tac
      >> metis_tac[builtin_closure_rules,boolTheory.IN_DEF]));

val allTypes'_builtin_closure = Q.prove(
  `!q ty x. ty ∈ builtin_closure q /\ q ⊆ nonbuiltin_types /\ MEM x (allTypes' ty) ⇒ x ∈ q`,
  simp[boolTheory.IN_DEF,GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac builtin_closure_ind
  >> rpt strip_tac
  >- (fs[nonbuiltin_types_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> first_x_assum drule >> strip_tac >> Cases_on `ty`
      >> fs[is_builtin_type_def,is_builtin_name_def]
      >> fs[allTypes'_def])
  >- fs[allTypes'_def]
  >- (fs[allTypes'_def,boolTheory.IN_DEF] >> rpt(first_x_assum drule >> strip_tac)));

val consts_of_free_const = Q.prove(
  `!tm x v. x ∈ consts_of_term v /\ VFREE_IN v tm
            ==> v = Const (FST x) (SND x)`,
  Induct >> rpt strip_tac
  >> fs[consts_of_term_def,VFREE_IN_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[consts_of_term_def]);

val VFREEs_IN_consts = Q.prove(
  `!tm s ty. VFREE_IN (Const s ty) tm
            ==> (s,ty) ∈ consts_of_term tm`,
  Induct >> rpt strip_tac
  >> fs[consts_of_term_def,VFREE_IN_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[consts_of_term_def]);

val var_type_in_types = Q.prove(
  `!tm ty v. VFREE_IN v tm /\ MEM ty (allTypes v)
            ==> MEM ty (allTypes tm)`,
  Induct >> rpt strip_tac
  >> fs[VFREE_IN_def,allTypes_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[allTypes_def]
  >> rpt(qpat_x_assum `!x. _` imp_res_tac) >> fs[]);

val VFREE_type = Q.prove(
  `!tm v. VFREE_IN v tm ==> v has_type typeof v`,
  Induct >> rpt strip_tac
  >> fs[VFREE_IN_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[typeof_def,has_type_rules]);

val RTC_lifts_invariants_inv = Q.prove(
  `(∀x y. P x ∧ R y x ⇒ P y) ⇒ ∀x y. P x ∧ R^* y x ⇒ P y`,
  rpt strip_tac
  >> Q.ISPECL_THEN [`inv R`,`P`] assume_tac (GEN_ALL relationTheory.RTC_lifts_invariants)
  >> fs[relationTheory.inv_DEF,relationTheory.inv_MOVES_OUT]
  >> metis_tac[])

val terms_of_frag_combE = Q.store_thm("terms_of_frag_combE",
  `!f a b. is_sig_fragment f /\ Comb a b ∈ terms_of_frag f ==> 
   a ∈ terms_of_frag f /\ b ∈ terms_of_frag f`,
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[]);

val terms_of_frag_combI = Q.store_thm("terms_of_frag_combI",
  `!f a b. is_sig_fragment f /\ a ∈ terms_of_frag f /\ b ∈ terms_of_frag f
           /\ welltyped(Comb a b)==> 
   Comb a b ∈ terms_of_frag f`,
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> imp_res_tac WELLTYPED_LEMMA
  >> metis_tac[has_type_rules]);

(* TODO: unify these two lemmas *)
val consts_of_term_REV_ASSOCD = Q.prove(
  `!x t ilist d. x ∈ consts_of_term (REV_ASSOCD t ilist d)
   ==> x ∈ consts_of_term d \/ EXISTS ($IN x) (MAP (consts_of_term o FST) ilist)`,
  Induct_on `ilist`
  >> rw[holSyntaxLibTheory.REV_ASSOCD_def]
  >> metis_tac[]);

val allTypes_REV_ASSOCD = Q.prove(
  `!x t ilist d. MEM x (allTypes (REV_ASSOCD t ilist d))
   ==> MEM x (allTypes d) \/ EXISTS ($MEM x) (MAP (allTypes o FST) ilist)`,
  Induct_on `ilist`
  >> rw[holSyntaxLibTheory.REV_ASSOCD_def]
  >> metis_tac[]);

val consts_of_term_VSUBST = Q.prove(
  `!x n ty tm1 ilist. x ∈ consts_of_term (VSUBST ilist tm1)
   ==> x ∈ consts_of_term tm1 \/ EXISTS ($IN x) (MAP (consts_of_term o FST) ilist)`,
  Induct_on `tm1`
  >> rw[VSUBST_def]
  >- (imp_res_tac consts_of_term_REV_ASSOCD >> simp[])
  >- (fs[consts_of_term_def] >> first_x_assum drule >> strip_tac >> fs[])
  >- (fs[consts_of_term_def,pairTheory.ELIM_UNCURRY,VSUBST_def]
      >> first_x_assum drule
      >> strip_tac >> fs[consts_of_term_def]
      >> disj2_tac
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[])
  >- (fs[consts_of_term_def]
      >> first_x_assum drule
      >> strip_tac >> fs[consts_of_term_def]
      >> disj2_tac
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[]));

val allTypes_VSUBST = Q.prove(
  `!x tm1 ilist. MEM x (allTypes (VSUBST ilist tm1))
                      /\ welltyped tm1
                      ==> MEM x (allTypes tm1) \/ EXISTS ($MEM x) (MAP (allTypes o FST) ilist)`,
  Induct_on `tm1`
  >> rw[VSUBST_def]
  >- (imp_res_tac allTypes_REV_ASSOCD >> simp[])
  >- (fs[allTypes_def] >> first_x_assum drule >> strip_tac >> fs[])
  >- (fs[allTypes_def]
      >> first_x_assum drule >> strip_tac >> fs[allTypes_def]
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[])
  >- (fs[allTypes_def]
      >> first_x_assum drule >> strip_tac >> fs[allTypes_def]
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[]));

(* 8(1) *)
val types_of_frag_ground = Q.store_thm("types_of_frag_ground",
  `!f. is_sig_fragment f ==> types_of_frag f ⊆ ground_types`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def]
  >> metis_tac[builtin_closure_tyvars]);

(* 8(2) *)
val terms_of_frag_ground = Q.store_thm("terms_of_frag_ground",
  `!f. is_sig_fragment f ==> terms_of_frag f ⊆ ground_terms`,
  Cases
  >> rw[terms_of_frag_def,ground_terms_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        ground_types_def,welltyped_def]
  >> qexists_tac `ty` >> simp[]
  >> qpat_x_assum `_ has_type _` (fn thm => rpt(pop_assum mp_tac) >> mp_tac thm)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`ty`,`x`] (* TODO: generated names *)
  >> ho_match_mp_tac has_type_strongind >> rpt strip_tac
  >- (fs[allTypes_def] >> match_mp_tac allTypes_no_tyvars
      >> fs[])
  >- (fs[allTypes_def] >> match_mp_tac allTypes_no_tyvars
      >> fs[])
  >- (match_mp_tac allTypes_no_tyvars >> fs[] >> rw[]
      >> first_x_assum match_mp_tac
      >> match_mp_tac allTypes_no_tyvars2
      >> metis_tac[has_type_rules])
  >- (match_mp_tac allTypes_no_tyvars >> fs[] >> rw[]
      >> first_x_assum match_mp_tac
      >> match_mp_tac allTypes_no_tyvars2
      >> metis_tac[has_type_rules]));

(* 8(3) *)
val term_frag_in_type_frag = Q.store_thm("term_frag_in_type_frag",
  `!f tm ty . is_sig_fragment f /\ tm ∈ terms_of_frag f ==>
          typeof tm ∈ types_of_frag f`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def]
  >> metis_tac[WELLTYPED_LEMMA,allTypes_no_tyvars2,builtin_closure_allTypes']);

(* 8(4) *)
val term_vars_in_term_frag = Q.store_thm("term_vars_in_term_frag",
  `!f tm v. is_sig_fragment f /\ tm ∈ terms_of_frag f /\ VFREE_IN v tm ==>
          v ∈ terms_of_frag f`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def]
  >- (imp_res_tac consts_of_free_const >> fs[consts_of_term_def]
      >> first_x_assum match_mp_tac >> imp_res_tac VFREEs_IN_consts >> fs[])
  >- (imp_res_tac var_type_in_types >> rpt(qpat_x_assum `!x. _` imp_res_tac))
  >- (imp_res_tac VFREE_type >> metis_tac[]));

(* 8(5) *)
val subterm1_in_term_frag = Q.store_thm("subterm1_in_term_frag",
  `!f tm1 tm2. is_sig_fragment f /\ tm1 ∈ terms_of_frag f /\ subterm1 tm2 tm1 ==>
          tm2 ∈ terms_of_frag f`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def,Once subterm1_cases]
  >> fs[consts_of_term_def,allTypes_def]
  >> (imp_res_tac WELLTYPED_LEMMA >> rpt(BasicProvers.VAR_EQ_TAC)
      >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[] >> metis_tac[has_type_rules]));

val subterm_in_term_frag = Q.store_thm("subterm_in_term_frag",
  `!f tm1 tm2. is_sig_fragment f /\ tm1 ∈ terms_of_frag f /\ tm2 subterm tm1 ==>
          tm2 ∈ terms_of_frag f`,
  `!f. is_sig_fragment f ==> !tm1 tm2. tm1 ∈ terms_of_frag f /\ tm2 subterm tm1 ==>
       tm2 ∈ terms_of_frag f` suffices_by metis_tac[]
  >> ntac 2 strip_tac
  >> ho_match_mp_tac RTC_lifts_invariants_inv
  >> rpt strip_tac >> imp_res_tac subterm1_in_term_frag);

(* 8(6) *)
val term_frag_subst_clos = Q.store_thm("subterm_in_term_frag",
  `!f n ty tm1 tm2. is_sig_fragment f /\ tm1 ∈ terms_of_frag f /\ tm2 ∈ terms_of_frag f
                    /\ ty ∈ types_of_frag f
                    /\ tm2 has_type ty ==>
          VSUBST [(tm2, Var n ty)] tm1 ∈ terms_of_frag f`,
  Cases >> Induct_on `tm1`
  >- (rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
         welltyped_def,terms_of_frag_def,VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def,consts_of_term_def,allTypes_def])
  >- (rw[VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def])
  >- (rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
         welltyped_def,terms_of_frag_def,VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def,consts_of_term_def,allTypes_def]
      >> imp_res_tac consts_of_term_VSUBST
      >> fs[consts_of_term_def]
      >> TRY(qmatch_goalsub_abbrev_tac `_ IN _`
             >> drule allTypes_VSUBST >> simp[GSYM PULL_EXISTS]
             >> impl_tac
             >- (fs[Once has_type_cases] >> fs[welltyped_def] >> metis_tac[])
             >> strip_tac >> fs[])
      >> rename1 `Comb _ _ has_type cty`
      >> qexists_tac `cty`
      >> qpat_x_assum `Comb _ _ has_type _` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[]
      >> MAP_FIRST match_mp_tac (CONJUNCTS has_type_rules)
      >> qexists_tac `dty`
      >> conj_tac >> match_mp_tac VSUBST_HAS_TYPE
      >> fs[])
  >- (rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
         welltyped_def,terms_of_frag_def,VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def,consts_of_term_def,allTypes_def]
      >> qpat_x_assum `Abs _ _ has_type _` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[] >> rpt(BasicProvers.VAR_EQ_TAC) >> fs[dest_var_def,consts_of_term_def]
      >> imp_res_tac consts_of_term_VSUBST >> fs[consts_of_term_def,allTypes_def]
      >> TRY(qmatch_goalsub_abbrev_tac `_ IN _`
             >> drule allTypes_VSUBST >> simp[GSYM PULL_EXISTS]
             >> impl_tac
             >- (fs[welltyped_def] >> metis_tac[])
             >> strip_tac >> fs[allTypes_def])
      >> qexists_tac `Fun dty rty`
      >> MAP_FIRST match_mp_tac (CONJUNCTS has_type_rules)
      >> match_mp_tac VSUBST_HAS_TYPE
      >> rw[] >> MAP_FIRST MATCH_ACCEPT_TAC (CONJUNCTS has_type_rules)));

val is_type_frag_interpretation_def = xDefine "is_type_frag_interpretation"`
  is_type_frag_interpretation0 ^mem (tyfrag: type -> bool) (δ: type -> 'U) ⇔
    (∀ty. ty ∈ tyfrag ⇒ inhabited(δ ty))`

val _ = Parse.overload_on("is_type_frag_interpretation",``is_type_frag_interpretation0 ^mem``)

(* Todo: grotesque patterns *)
val ext_type_frag_builtins_def = xDefine "ext_type_frag_builtins"`
  ext_type_frag_builtins0 ^mem (δ: type -> 'U) ty ⇔
  case ty of Bool => boolset
    |  Fun dom rng => Funspace (ext_type_frag_builtins0 ^mem δ dom)
                               (ext_type_frag_builtins0 ^mem δ rng)
    | _ => δ ty`

val _ = Parse.overload_on("ext_type_frag_builtins",``ext_type_frag_builtins0 ^mem``)

val is_type_frag_interpretation_ext = Q.store_thm("is_type_frag_interpretation_ext",
  `!tyfrag tmfrag δ. is_sig_fragment (tyfrag,tmfrag) /\ is_set_theory ^mem /\ is_type_frag_interpretation tyfrag δ ==>
   is_type_frag_interpretation (builtin_closure tyfrag) (ext_type_frag_builtins δ)`,
  rw[] >> rw[is_type_frag_interpretation_def]
  >> qhdtm_x_assum `is_type_frag_interpretation0` mp_tac
  >> qhdtm_x_assum `is_sig_fragment` mp_tac    
  >> pop_assum mp_tac
  >> simp[boolTheory.IN_DEF]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`ty`,`tyfrag`]
  >> ho_match_mp_tac builtin_closure_ind >> rpt strip_tac
  >- (fs[is_type_frag_interpretation_def,Once ext_type_frag_builtins_def,boolTheory.IN_DEF,
         is_sig_fragment_def]
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >> fs[nonbuiltin_types_def,is_builtin_type_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> rpt(first_x_assum drule) >> fs[is_builtin_type_def,is_builtin_name_def])
  >- (fs[is_type_frag_interpretation_def,Once ext_type_frag_builtins_def,boolTheory.IN_DEF,
         is_sig_fragment_def]
      >> metis_tac[boolean_in_boolset])
  >- (rpt(first_x_assum drule >> disch_then drule >> strip_tac)
      >> drule funspace_inhabited
      >> rename1 `Fun dty rty`
      >> disch_then(qspecl_then [`ext_type_frag_builtins δ dty`,
                                 `ext_type_frag_builtins δ rty`] mp_tac)
      >> impl_tac >- metis_tac[]
      >> disch_then assume_tac >> simp[Once ext_type_frag_builtins_def]));

val is_frag_interpretation_def = xDefine "is_frag_interpretation"`
  is_frag_interpretation0 ^mem (tyfrag,tmfrag)
                               (δ: type -> 'U) (γ: mlstring # type -> 'U) ⇔
  (is_type_frag_interpretation tyfrag δ /\
   ∀(c,ty). (c,ty) ∈ tmfrag ⇒ γ(c,ty) ⋲ ext_type_frag_builtins δ ty)
  `

val _ = Parse.overload_on("is_frag_interpretation",``is_frag_interpretation0 ^mem``)

(* TODO: grotesque patterns *)
val ext_term_frag_builtins_def = xDefine "ext_term_frag_builtins"`
  ext_term_frag_builtins0 ^mem (δ: type -> 'U) (γ: mlstring # type -> 'U) tm =
  if ?ty. tm = (strlit "=",Fun ty (Fun ty Bool)) then
    case tm of (_, Fun ty _) =>
      Abstract (δ ty) (Funspace (δ ty) boolset)
        (λx. Abstract (δ ty) boolset (λy. Boolean (x = y)))
    | _ => γ tm
  else γ tm
  `

val _ = Parse.overload_on("ext_term_frag_builtins",``ext_term_frag_builtins0 ^mem``)

val builtin_terms_def = Define
  `builtin_terms tyfrag = builtin_consts ∩ {const | SND const ∈ tyfrag}`

val ext_type_frag_idem = Q.store_thm("ext_type_frag_idem",
  `!ty δ.
    (ext_type_frag_builtins (ext_type_frag_builtins δ) ty)
     = ext_type_frag_builtins δ ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (rw[Once ext_type_frag_builtins_def])
  >> rw[Once ext_type_frag_builtins_def]
  >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
  >> CONV_TAC(RHS_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
  >> simp[]);
                  
val is_frag_interpretation_ext = Q.store_thm("is_frag_interpretation_ext",
  `!tyfrag tmfrag δ γ. is_sig_fragment (tyfrag,tmfrag) /\ is_set_theory ^mem
           /\ is_frag_interpretation (tyfrag,tmfrag) δ γ==>
   is_frag_interpretation (builtin_closure tyfrag,
                           tmfrag ∪ builtin_terms(builtin_closure tyfrag))
                          (ext_type_frag_builtins δ)
                          (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)`,
  rw[is_frag_interpretation_def]
  >- (match_mp_tac is_type_frag_interpretation_ext >> metis_tac[])
  >> fs[pairTheory.ELIM_UNCURRY,is_sig_fragment_def] >> rw[]
  >> Cases_on `x` (* TODO: generated name *)
  >> rw[ext_term_frag_builtins_def] >> fs[]
  >- (fs[nonbuiltin_constinsts_def,builtin_consts,pred_setTheory.SUBSET_DEF]
      >> rpt(first_x_assum drule) >> simp[])
  >- (first_x_assum drule >> fs[]
      >> CONV_TAC(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >> disch_then(mp_tac o PURE_ONCE_REWRITE_RULE [ext_type_frag_builtins_def])
      >> fs[ext_type_frag_idem])
  >- (simp[ext_type_frag_idem]
      >> CONV_TAC(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
      >> CONV_TAC(RAND_CONV(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def])))
      >> CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))))
      >> drule abstract_in_funspace >> disch_then match_mp_tac
      >> rw[]
      >> drule abstract_in_funspace >> disch_then match_mp_tac
      >> rw[] >> metis_tac[boolean_in_boolset])
  >- (rfs[builtin_terms_def,builtin_consts] >> metis_tac[]));

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type signature, and is only constrained for defined type
   operators applied to the right number of non-empty arguments. *)

val _ = Parse.type_abbrev("tyass",``:mlstring -> 'U list -> 'U``)

val is_type_assignment_def = xDefine "is_type_assignment"`
  is_type_assignment0 ^mem tysig (δ:'U tyass) ⇔
    FEVERY
      (λ(name,arity).
        ∀ls. LENGTH ls = arity ∧ EVERY inhabited ls ⇒
             inhabited ((δ name) ls))
      tysig`
val _ = Parse.overload_on("is_type_assignment",``is_type_assignment0 ^mem``)
                         
(* A type valuation is a map from type variable names to non-empty sets. *)

val _ = Parse.type_abbrev("tyval",``:mlstring -> 'U``)

val is_type_valuation_def = xDefine "is_type_valuation"`
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)`
val _ = Parse.overload_on("is_type_valuation",``is_type_valuation0 ^mem``)

(* Semantics of types. Simply applies the valuation and assignment. *)

val typesem_def = tDefine "typesem"`
  (typesem δ (τ:'U tyval) (Tyvar s) = τ s) ∧
  (typesem δ τ (Tyapp name args) =
    (δ name) (MAP (typesem δ τ) args))`
  (type_rec_tac "SND o SND")

(* A term assignment is a map from a constant name and a list of values for the
   free type variables to a value for the constant. The assignment is with
   respect to a signature and is only constrained for defined constants. *)

val _ = Parse.type_abbrev("tmass",``:mlstring -> 'U list -> 'U``)

val is_term_assignment_def = xDefine "is_term_assignment"`
  is_term_assignment0 ^mem tmsig δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty).
        ∀τ. is_type_valuation τ ⇒
              γ name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty))))) <: typesem δ τ ty)
      tmsig`
val _ = Parse.overload_on("is_term_assignment",``is_term_assignment0 ^mem``)

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

val _ = Parse.type_abbrev("tmval",``:mlstring # type -> 'U``)

val is_term_valuation_def = xDefine "is_term_valuation"`
  is_term_valuation0 ^mem tysig δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tysig ty ⇒ σ (v,ty) <: typesem δ τ ty`
val _ = Parse.overload_on("is_term_valuation",``is_term_valuation0 ^mem``)

(* An interpretation is a pair of assignments.
   A valuation is a pair of valuations. *)

val _ = Parse.type_abbrev("interpretation",``:'U tyass # 'U tmass``)
val _ = Parse.overload_on("tyaof",``FST:'U interpretation->'U tyass``)
val _ = Parse.overload_on("tmaof",``SND:'U interpretation->'U tmass``)
val _ = Parse.type_abbrev("valuation",``:'U tyval # 'U tmval``)
val _ = Parse.overload_on("tyvof",``FST:'U valuation->'U tyval``)
val _ = Parse.overload_on("tmvof",``SND:'U valuation->'U tmval``)

val is_valuation_def = xDefine"is_valuation"`
  is_valuation0 ^mem tysig δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tysig δ (tyvof v) (tmvof v)`
val _ = Parse.overload_on("is_valuation",``is_valuation0 ^mem``)

(* term assignment for instances of constants *)

val instance_def = new_specification("instance_def",["instance"],
  Q.prove(`∃f. ∀tmsig (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmsig name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmsig i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar) (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`,
    simp[GSYM SKOLEM_THM] >> rw[] >>
    Cases_on`FLOOKUP tmsig name`>>simp[] >>
    qmatch_assum_rename_tac`FLOOKUP tmsig name = SOME ty0` >>
    Cases_on`is_instance ty0 ty` >> fs[] >>
    qmatch_assum_rename_tac`ty = TYPE_SUBST tyin ty0` >>
    qho_match_abbrev_tac`∃f. ∀tyin. P tyin ⇒ f = Q tyin` >>
    qexists_tac`Q tyin` >>
    rw[Abbr`P`,Abbr`Q`,FUN_EQ_THM] >> rpt AP_TERM_TAC >>
    rw[listTheory.MAP_EQ_f] >> rw[] >>
    fs[listTheory.MEM_MAP,mlstringTheory.implode_explode] >>
    metis_tac[TYPE_SUBST_tyvars]))

(* Semantics of terms. *)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (tmsig:tmsig) (i:'U interpretation) (v:'U valuation) (Var x ty) = tmvof v (x,ty)) ∧
  (termsem0 ^mem tmsig i v (Const name ty) = instance tmsig i name ty (tyvof v)) ∧
  (termsem0 ^mem tmsig i v (Comb t1 t2) =
   termsem0 ^mem tmsig i v t1 ' (termsem0 ^mem tmsig i v t2)) ∧
  (termsem0 ^mem tmsig i v (Abs (Var x ty) b) =
   Abstract (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
     (λm. termsem0 ^mem tmsig i (tyvof v, ((x,ty)=+m)(tmvof v)) b))`
val _ = Parse.overload_on("termsem",``termsem0 ^mem``)

(* Satisfaction of sequents. *)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem i (sig:sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem (tmsof sig) i v t = True) h
      ⇒ termsem (tmsof sig) i v c = True`
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
val _ = Parse.overload_on("satisfies",``satisfies0 ^mem``)

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

val is_interpretation_def = xDefine "is_interpretation"`
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)`
val _ = Parse.overload_on("is_interpretation",``is_interpretation0 ^mem``)

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem (δ:'U tyass) ⇔
    (∀dom rng. δ (strlit "fun") [dom;rng] = Funspace dom rng) ∧
    (δ (strlit "bool") [] = boolset)`
val _ = Parse.overload_on("is_std_type_assignment",``is_std_type_assignment0 ^mem``)

local
  open Parse
  val hs = HardSpace 1
  fun bs n = BreakSpace(1,n)
in
val _ = Parse.add_rule{term_name = "interprets",
                       fixity = Infix (NONASSOC,450),
                       pp_elements = [TOK "interprets", hs, TM, hs, TOK "on", bs 2, TM, hs, TOK "as", bs 2],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))}
end
val interprets_def = xDefine"interprets"`
  interprets0 ^mem γ name vs f ⇔ ∀τ. is_type_valuation τ ⇒ γ name (MAP τ vs) = f (MAP τ vs)`
val _ = Parse.overload_on("interprets",``interprets0 ^mem``)

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem (i:'U interpretation) ⇔
    is_std_type_assignment (tyaof i) ∧
    tmaof i interprets (strlit "=") on [(strlit "A")] as
    λl. (Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y))))`
val _ = Parse.overload_on("is_std_interpretation",``is_std_interpretation0 ^mem``)

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

val models_def = xDefine"models"`
  models0 ^mem i (thy:thy) ⇔
    is_interpretation (sigof thy) i ∧
    is_std_interpretation i ∧
    ∀p. p ∈ (axsof thy) ⇒ i satisfies (sigof thy,[],p)`
val _ = Parse.add_infix("models",450,Parse.NONASSOC)
val _ = Parse.overload_on("models",``models0 ^mem``)

(* Validity of sequents. *)

val entails_def = xDefine"entails"`
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀i. i models thy
        ⇒ i satisfies (sigof thy,h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
val _ = Parse.overload_on("|=",``entails0 ^mem``)

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val`
val _ = Parse.overload_on("is_structure",``is_structure0 ^mem``)

val _ = export_theory()
