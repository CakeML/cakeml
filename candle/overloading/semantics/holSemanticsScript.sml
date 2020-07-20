(*
  Define semantics for HOL sequents, in particular the notion of entailment
  i.e. valid sequents, which are those that are satisfied by any model of the
  theory context.
*)
open HolKernel boolLib boolSimps bossLib holSyntaxTheory holSyntaxExtraTheory setSpecTheory

val _ = new_theory"holSemantics"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[DB.fetch"holSyntax""type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

Overload inhabited = ``λs. ∃x. x <: s``

Inductive builtin_closure:
  (!T ty. T ty ==> builtin_closure T ty)
  /\ (!T. builtin_closure T Bool)
  /\ (!T ty1 ty2. builtin_closure T ty1 /\ builtin_closure T ty2
        ==> builtin_closure T (Fun ty1 ty2))
End

val [builtin_closure_inj,builtin_closure_bool,builtin_closure_fun] =
    map2 (curry save_thm)
         ["builtin_closure_inj","builtin_closure_bool","builtin_closure_fun"]
         (CONJUNCTS builtin_closure_rules);

val ground_types_def = Define `
  ground_types (sig:sig) =
  {ty | tyvars ty = [] /\ type_ok (tysof sig) ty}
  `

val ground_consts_def = Define `
  ground_consts sig =
  {(n,ty) | ty ∈ ground_types sig /\ term_ok sig (Const n ty)}
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
  `is_sig_fragment sig (tys,consts) =
   (tys ⊆ ground_types sig ∧ tys ⊆ nonbuiltin_types
    ∧ consts ⊆ ground_consts sig ∧ consts ⊆ nonbuiltin_constinsts
    ∧ (!s c. (s,c) ∈ consts ==> c ∈ builtin_closure tys)
   )
  `

val terms_of_frag_def = Define
  `terms_of_frag (tys,consts) =
   {t | consts_of_term t ∩ nonbuiltin_constinsts ⊆ consts
        /\ set(allTypes t) ⊆ tys /\ welltyped t}
  `

val TYPE_SUBSTf_def = tDefine "TYPE_SUBSTf" `
  (TYPE_SUBSTf i (Tyvar v) = i v) ∧
  (TYPE_SUBSTf i (Tyapp v tys) =
    Tyapp v (MAP (λa. TYPE_SUBSTf i a) tys))
  `
  (WF_REL_TAC(`measure (type_size o SND)`) >> simp[] >>
   gen_tac >> Induct >> simp[type_size_def] >> rw[] >>
   simp[] >> res_tac >> simp[]);

val _ = export_rewrites["TYPE_SUBSTf_def"]

val terms_of_frag_uninst_def = Define
  `terms_of_frag_uninst (tys,consts) sigma =
   {t | (IMAGE (I ## TYPE_SUBSTf sigma) (consts_of_term t) ∩ nonbuiltin_constinsts) ⊆ consts
        /\ set(FLAT (MAP allTypes'(MAP (TYPE_SUBSTf sigma) (allTypes t)))) ⊆ tys /\ welltyped t}
  `

val ground_terms_def = Define
  `ground_terms sig = {t | ?ty. t has_type ty /\ ty ∈ ground_types sig}`

val ground_terms_uninst_def = Define
  `ground_terms_uninst sig sigma = {t | ?ty. t has_type ty /\ TYPE_SUBSTf sigma ty ∈ ground_types sig}`

val types_of_frag_def = Define
  `types_of_frag (tys,consts) = builtin_closure tys`

(* Lemma 8 from Kunčar and Popescu's ITP2015 paper *)

Theorem builtin_closure_idem:
  !tyfrag. builtin_closure (builtin_closure tyfrag) = builtin_closure tyfrag
Proof
  rw[FUN_EQ_THM]
  >> W (curry Q.SPEC_TAC) `x`
  >> ho_match_mp_tac type_ind
  >> rpt strip_tac
  >- simp[Once builtin_closure_cases]
  >> simp[Once builtin_closure_cases]
  >> rw[EQ_IMP_THM]
  >> rfs[]
  >> simp[Once builtin_closure_cases]
QED

val allTypes_no_tyvars_and_ok = Q.prove(
  `!ty. (∀x. x ∈ q ⇒ tyvars x = [] /\ type_ok (tysof sig) x)
        /\ (∀x. MEM x (allTypes' ty) ⇒ x ∈ q)
        /\ is_std_sig sig
        ==> tyvars ty = [] /\ type_ok (tysof sig) ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >> fs[allTypes'_defn]
  >- (BasicProvers.PURE_FULL_CASE_TAC >- fs[tyvars_def]
      >> qpat_x_assum `!x. _` mp_tac >> simp[] >> strip_tac
      >> BasicProvers.PURE_FULL_CASE_TAC
      >- (Cases_on `l` >- fs[tyvars_def]
          >> rename1 `ty::tys` >> Cases_on `tys` >> fs[]
          >> qmatch_goalsub_abbrev_tac `a1 = a2`
          >> `set a1 = set a2` suffices_by(unabbrev_all_tac >> simp[])
          >> unabbrev_all_tac
          >> simp[tyvars_def])
      >> fs[])
  \\ BasicProvers.PURE_FULL_CASE_TAC >- fs[type_ok_def,is_std_sig_def]
  \\ qpat_x_assum `!x. _` mp_tac >> simp[] >> strip_tac
  >> BasicProvers.PURE_FULL_CASE_TAC
  >- (fs[quantHeuristicsTheory.LIST_LENGTH_2,is_std_sig_def,type_ok_def]
      \\ fs[])
  \\ fs[type_ok_def]);

val allTypes_no_tyvars2 = Q.prove(
  `!tm ty1 ty2. tm has_type ty1 /\
           MEM ty2 (allTypes' ty1)
           ==> MEM ty2 (allTypes tm)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac has_type_strongind
  >> rw[allTypes_def,allTypes'_defn] >> fs[]);

val builtin_closure_tyvars = Q.prove(
  `∀q x. x ∈ builtin_closure q /\ (∀x. x ∈ q ⇒ tyvars x = []) ==> tyvars x = []`,
  simp [IN_DEF,GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac builtin_closure_ind
  >> rw[tyvars_def]);

val builtin_closure_type_ok = Q.prove(
  `∀q x. x ∈ builtin_closure q /\ (∀x. x ∈ q ⇒ type_ok (tysof sig) x)
   /\ is_std_sig sig
   ==> type_ok (tysof sig) x`,
  simp [IN_DEF,GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac builtin_closure_ind
  >> rw[is_std_sig_def,type_ok_def]);

Theorem builtin_closure_allTypes:
  !ty q. (∀x. MEM x (allTypes' ty) ⇒ x ∈ q) ==> ty ∈ builtin_closure q
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (fs[allTypes'_defn,boolTheory.IN_DEF] >> metis_tac[builtin_closure_rules])
  >- (fs[allTypes'_defn,listTheory.EVERY_MEM]
      >> BasicProvers.PURE_FULL_CASE_TAC
      >- fs[builtin_closure_rules,boolTheory.IN_DEF]
      >> qpat_x_assum `!x. _` mp_tac >> simp[]
      >> BasicProvers.PURE_FULL_CASE_TAC >> simp[builtin_closure_rules,boolTheory.IN_DEF]
      >> Cases_on `l` >- fs[tyvars_def]
      >> rename1 `ty::tys` >> Cases_on `tys` >> fs[] >> rpt strip_tac
      >> metis_tac[builtin_closure_rules,boolTheory.IN_DEF])
QED

Theorem builtin_closure_allTypes'':
  !ty sigma q. (∀x. MEM x (allTypes' ty) ⇒ TYPE_SUBSTf sigma x ∈ q) ==> TYPE_SUBSTf sigma  ty ∈ builtin_closure q
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (fs[allTypes'_defn,boolTheory.IN_DEF] >> metis_tac[builtin_closure_rules])
  >- (fs[allTypes'_defn,listTheory.EVERY_MEM]
      >> BasicProvers.PURE_FULL_CASE_TAC
      >- fs[builtin_closure_rules,boolTheory.IN_DEF]
      >> qpat_x_assum `!x. _` mp_tac >> simp[]
      >> BasicProvers.PURE_FULL_CASE_TAC >> simp[builtin_closure_rules,boolTheory.IN_DEF]
      >> Cases_on `l` >- fs[tyvars_def]
      >> rename1 `ty::tys` >> Cases_on `tys` >> fs[] >> rpt strip_tac
      >> metis_tac[builtin_closure_rules,boolTheory.IN_DEF])
QED

Theorem builtin_closure_allTypes''':
  !ty sigma q. (∀y x. MEM x (allTypes' ty) /\ MEM y (allTypes' (TYPE_SUBSTf sigma x)) ⇒ y ∈ q) ==> TYPE_SUBSTf sigma ty ∈ builtin_closure q
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (match_mp_tac builtin_closure_allTypes
      >> fs[allTypes'_defn])
  >> fs[allTypes'_defn]
  >> BasicProvers.PURE_FULL_CASE_TAC
  >- (fs[boolTheory.IN_DEF,builtin_closure_rules])
  >> qpat_x_assum `!x. _` mp_tac >> simp[]
  >> BasicProvers.PURE_FULL_CASE_TAC >> simp[builtin_closure_rules,boolTheory.IN_DEF]
  >> fs[quantHeuristicsTheory.LIST_LENGTH_2]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[allTypes'_defn] >> strip_tac
  >> rfs[quantHeuristicsTheory.LIST_LENGTH_2]
  >> metis_tac[builtin_closure_rules,boolTheory.IN_DEF]
QED

val allTypes'_builtin_closure = Q.prove(
  `!q ty x. ty ∈ builtin_closure q /\ q ⊆ nonbuiltin_types /\ MEM x (allTypes' ty) ⇒ x ∈ q`,
  simp[boolTheory.IN_DEF,GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac builtin_closure_ind
  >> rpt strip_tac
  >- (fs[nonbuiltin_types_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> first_x_assum drule >> strip_tac >> Cases_on `ty`
      >> fs[is_builtin_type_def,is_builtin_name_def]
      >> fs[allTypes'_defn])
  >- fs[allTypes'_defn]
  >- (fs[allTypes'_defn,boolTheory.IN_DEF] >> rpt(first_x_assum drule >> strip_tac)));

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

Theorem terms_of_frag_combE:
  !f a b sig. is_sig_fragment sig f /\ Comb a b ∈ terms_of_frag f ==>
   a ∈ terms_of_frag f /\ b ∈ terms_of_frag f
Proof
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[]
QED

Theorem terms_of_frag_uninst_combE:
  !f a b sig sigma. is_sig_fragment sig f /\ Comb a b ∈ terms_of_frag_uninst f sigma ==>
   a ∈ terms_of_frag_uninst f sigma /\ b ∈ terms_of_frag_uninst f sigma
Proof
  Cases
  >> rw[terms_of_frag_uninst_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def,allTypes'_defn]
  >> fs[listTheory.MEM_FLAT,listTheory.MEM_MAP,PULL_EXISTS]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[]
QED

Theorem terms_of_frag_AbsE:
  !f a b sig. is_sig_fragment sig f /\ Abs a b ∈ terms_of_frag f ==>
   a ∈ terms_of_frag f /\ b ∈ terms_of_frag f
Proof
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[has_type_rules]
QED

Theorem terms_of_frag_uninst_AbsE:
  !f a b sig sigma. is_sig_fragment sig f /\ Abs a b ∈ terms_of_frag_uninst f sigma ==>
   a ∈ terms_of_frag_uninst f sigma /\ b ∈ terms_of_frag_uninst f sigma
Proof
  Cases
  >> rw[terms_of_frag_uninst_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[has_type_rules]
QED

Theorem terms_of_frag_combI:
  !f a b sig. is_sig_fragment sig f /\ a ∈ terms_of_frag f /\ b ∈ terms_of_frag f
           /\ welltyped(Comb a b)==>
   Comb a b ∈ terms_of_frag f
Proof
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> imp_res_tac WELLTYPED_LEMMA
  >> metis_tac[has_type_rules]
QED

Theorem terms_of_frag_uninst_combI:
  !f a b sig sigma. is_sig_fragment sig f /\ a ∈ terms_of_frag_uninst f sigma /\ b ∈ terms_of_frag_uninst f sigma
           /\ welltyped(Comb a b)==>
   Comb a b ∈ terms_of_frag_uninst f sigma
Proof
  Cases
  >> rw[terms_of_frag_uninst_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> imp_res_tac WELLTYPED_LEMMA
  >> metis_tac[has_type_rules]
QED

Theorem terms_of_frag_absI:
  !f a b sig. is_sig_fragment sig f /\ a ∈ terms_of_frag f /\ b ∈ terms_of_frag f
           /\ welltyped(Abs a b)==>
   Abs a b ∈ terms_of_frag f
Proof
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> imp_res_tac WELLTYPED_LEMMA
  >> metis_tac[has_type_rules]
QED

Theorem terms_of_frag_uninst_absI:
  !f a b sig sigma. is_sig_fragment sig f /\ a ∈ terms_of_frag_uninst f sigma /\ b ∈ terms_of_frag_uninst f sigma
           /\ welltyped(Abs a b)==>
   Abs a b ∈ terms_of_frag_uninst f sigma
Proof
  Cases
  >> rw[terms_of_frag_uninst_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> imp_res_tac WELLTYPED_LEMMA
  >> metis_tac[has_type_rules]
QED

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
Theorem types_of_frag_ground:
  !f sig. is_sig_fragment sig f /\ is_std_sig sig ==> types_of_frag f ⊆ ground_types sig
Proof
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def]
  >- metis_tac[builtin_closure_tyvars]
  >- metis_tac[builtin_closure_type_ok]
QED

(* 8(2) *)
Theorem terms_of_frag_ground:
  !f. is_sig_fragment sig f /\ is_std_sig sig ==> terms_of_frag f ⊆ ground_terms sig
Proof
  Cases
  >> rw[terms_of_frag_def,ground_terms_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        ground_types_def,welltyped_def]
  >> qexists_tac `ty` >> simp[]
  >> qpat_x_assum `_ has_type _` (fn thm => rpt(pop_assum mp_tac) >> mp_tac thm)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`ty`,`x`] (* TODO: generated names *)
  >> ho_match_mp_tac has_type_strongind
  >> rpt conj_tac >> rpt gen_tac >> rpt(disch_then strip_assume_tac)
  >- (fs[allTypes_def] >> match_mp_tac allTypes_no_tyvars_and_ok
      >> fs[])
  >- (fs[allTypes_def] >> match_mp_tac allTypes_no_tyvars_and_ok
      >> fs[])
  >- (match_mp_tac allTypes_no_tyvars_and_ok >> fs[] >> rw[]
      >> first_x_assum match_mp_tac
      >> match_mp_tac allTypes_no_tyvars2
      >> metis_tac[has_type_rules])
  >- (match_mp_tac allTypes_no_tyvars_and_ok >> fs[] >> rw[]
      >> first_x_assum match_mp_tac
      >> match_mp_tac allTypes_no_tyvars2
      >> metis_tac[has_type_rules])
QED

(* 8(3) *)
Theorem term_frag_in_type_frag:
  !f tm ty sig. is_sig_fragment sig f /\ tm ∈ terms_of_frag f ==>
          typeof tm ∈ types_of_frag f
Proof
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def]
  >> metis_tac[WELLTYPED_LEMMA,allTypes_no_tyvars2,builtin_closure_allTypes]
QED

Theorem term_frag_uninst_in_type_frag:
  !f tm ty sig. is_sig_fragment sig f /\ tm ∈ terms_of_frag_uninst f sigma ==>
          TYPE_SUBSTf sigma (typeof tm) ∈ types_of_frag f
Proof
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_uninst_def]
  >> fs[listTheory.MEM_FLAT,listTheory.MEM_MAP,PULL_EXISTS]
  >> match_mp_tac builtin_closure_allTypes'''
  >> rw[] >> first_x_assum match_mp_tac
  >> imp_res_tac WELLTYPED_LEMMA
  >> pop_assum(assume_tac o GSYM)
  >> fs[]
  >> metis_tac[allTypes_no_tyvars2]
QED

(* 8(4) *)
Theorem term_vars_in_term_frag:
  !f tm v sig. is_sig_fragment sig f /\ tm ∈ terms_of_frag f /\ VFREE_IN v tm ==>
          v ∈ terms_of_frag f
Proof
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def]
  >- (imp_res_tac consts_of_free_const >> fs[consts_of_term_def]
      >> first_x_assum match_mp_tac >> imp_res_tac VFREEs_IN_consts >> fs[])
  >- (imp_res_tac var_type_in_types >> rpt(qpat_x_assum `!x. _` imp_res_tac))
  >- (imp_res_tac VFREE_type >> metis_tac[])
QED

(* 8(5) *)
Theorem subterm1_in_term_frag:
  !f tm1 tm2 sig. is_sig_fragment sig f /\ tm1 ∈ terms_of_frag f /\ subterm1 tm2 tm1 ==>
          tm2 ∈ terms_of_frag f
Proof
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def,Once subterm1_cases]
  >> fs[consts_of_term_def,allTypes_def]
  >> (imp_res_tac WELLTYPED_LEMMA >> rpt(BasicProvers.VAR_EQ_TAC)
      >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[] >> metis_tac[has_type_rules])
QED

Theorem subterm1_in_term_frag_uninst:
  !f tm1 tm2 sig sigma.
     is_sig_fragment sig f
     /\ tm1 ∈ terms_of_frag_uninst f sigma
     /\ subterm1 tm2 tm1
     ==> tm2 ∈ terms_of_frag_uninst f sigma
Proof
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_uninst_def,Once subterm1_cases]
  >> fs[consts_of_term_def,allTypes_def]
  >> fs[listTheory.MEM_FLAT,listTheory.MEM_MAP,listTheory.MAP_MAP_o,combinTheory.o_DEF,PULL_EXISTS]
  >> (imp_res_tac WELLTYPED_LEMMA >> rpt(BasicProvers.VAR_EQ_TAC)
      >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[] >> metis_tac[has_type_rules])
QED

Theorem subterm_in_term_frag:
  !f tm1 tm2 sig. is_sig_fragment sig f /\ tm1 ∈ terms_of_frag f /\ tm2 subterm tm1 ==>
          tm2 ∈ terms_of_frag f
Proof
  `!f sig. is_sig_fragment sig f ==> !tm1 tm2. tm1 ∈ terms_of_frag f /\ tm2 subterm tm1 ==>
       tm2 ∈ terms_of_frag f` suffices_by metis_tac[]
  >> ntac 3 strip_tac
  >> ho_match_mp_tac RTC_lifts_invariants_inv
  >> rpt strip_tac >> imp_res_tac subterm1_in_term_frag
QED

Theorem subterm_in_term_frag_uninst:
  !f tm1 tm2 sig sigma.
   is_sig_fragment sig f /\ tm1 ∈ terms_of_frag_uninst f sigma /\ tm2 subterm tm1
   ==> tm2 ∈ terms_of_frag_uninst f sigma
Proof
  `!f sig. is_sig_fragment sig f ==> !sigma tm1 tm2. tm1 ∈ terms_of_frag_uninst f sigma /\ tm2 subterm tm1 ==>
       tm2 ∈ terms_of_frag_uninst f sigma` suffices_by metis_tac[]
  >> ntac 4 strip_tac
  >> ho_match_mp_tac RTC_lifts_invariants_inv
  >> rpt strip_tac >> imp_res_tac subterm1_in_term_frag_uninst
QED

(* 8(6) *)
Theorem term_frag_subst_clos:
  !f n ty tm1 tm2 sig. is_sig_fragment sig f /\ tm1 ∈ terms_of_frag f /\ tm2 ∈ terms_of_frag f
                    /\ ty ∈ types_of_frag f
                    /\ tm2 has_type ty ==>
          VSUBST [(tm2, Var n ty)] tm1 ∈ terms_of_frag f
Proof
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
      >> rw[] >> MAP_FIRST MATCH_ACCEPT_TAC (CONJUNCTS has_type_rules))
QED

val is_type_frag_interpretation_def = xDefine "is_type_frag_interpretation"`
  is_type_frag_interpretation0 ^mem (tyfrag: type -> bool) (δ: type -> 'U) ⇔
    (∀ty. ty ∈ tyfrag ⇒ inhabited(δ ty))`

Overload is_type_frag_interpretation = ``is_type_frag_interpretation0 ^mem``

(* Todo: grotesque patterns *)
val ext_type_frag_builtins_def = xDefine "ext_type_frag_builtins"`
  ext_type_frag_builtins0 ^mem (δ: type -> 'U) ty ⇔
  case ty of Bool => boolset
    |  Fun dom rng => Funspace (ext_type_frag_builtins0 ^mem δ dom)
                               (ext_type_frag_builtins0 ^mem δ rng)
    | _ => δ ty`

Overload "ext_type_frag_builtins" = ``ext_type_frag_builtins0 ^mem``

Theorem is_type_frag_interpretation_ext:
  !tyfrag tmfrag δ sig. is_sig_fragment sig (tyfrag,tmfrag) /\ is_set_theory ^mem /\ is_type_frag_interpretation tyfrag δ ==>
   is_type_frag_interpretation (builtin_closure tyfrag) (ext_type_frag_builtins δ)
Proof
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
      >> disch_then assume_tac >> simp[Once ext_type_frag_builtins_def])
QED

val is_frag_interpretation_def = xDefine "is_frag_interpretation"`
  is_frag_interpretation0 ^mem (tyfrag,tmfrag)
                               (δ: type -> 'U) (γ: mlstring # type -> 'U) ⇔
  (is_type_frag_interpretation tyfrag δ /\
   ∀(c,ty). (c,ty) ∈ tmfrag ⇒ γ(c,ty) ⋲ ext_type_frag_builtins δ ty)
  `

Overload is_frag_interpretation = ``is_frag_interpretation0 ^mem``

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

Overload ext_term_frag_builtins = ``ext_term_frag_builtins0 ^mem``

val builtin_terms_def = Define
  `builtin_terms tyfrag = builtin_consts ∩ {const | SND const ∈ tyfrag}`

Theorem ext_type_frag_idem:
  !ty δ.
    (ext_type_frag_builtins (ext_type_frag_builtins δ) ty)
     = ext_type_frag_builtins δ ty
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (rw[Once ext_type_frag_builtins_def])
  >> rw[Once ext_type_frag_builtins_def]
  >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
  >> CONV_TAC(RHS_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
  >> simp[]
QED

Theorem ext_type_frag_mono_eq:
  !ty δ1 δ2.
    (!ty'. MEM ty' (allTypes' ty) ==> δ1 ty' = δ2 ty')
    ==> ext_type_frag_builtins δ1 ty = ext_type_frag_builtins δ2 ty
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (fs[ext_type_frag_builtins_def,allTypes'_defn])
  >> rw[Once ext_type_frag_builtins_def]
  >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[allTypes'_defn])
  >> CONV_TAC(RHS_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
  >> simp[]
  >> qmatch_goalsub_abbrev_tac `Funspace a1 a2 = Funspace a3 a4`
  >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
  >> unabbrev_all_tac >> conj_tac >> first_x_assum match_mp_tac
  >> metis_tac[]
QED

Theorem ext_type_frag_mono_eq'':
  !ty δ1 δ2 sigma.
    (!ty' ty''. MEM ty' (allTypes' ty) /\ MEM ty'' (allTypes' (TYPE_SUBSTf sigma ty')) ==> δ1 ty'' = δ2 ty'')
    ==> ext_type_frag_builtins δ1 (TYPE_SUBSTf sigma ty) = ext_type_frag_builtins δ2 (TYPE_SUBSTf sigma ty)
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (match_mp_tac ext_type_frag_mono_eq >> fs[allTypes'_defn])
  >> fs[TYPE_SUBSTf_def]
  >> simp[Once ext_type_frag_builtins_def,allTypes'_defn]
  >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[allTypes'_defn])
  >> CONV_TAC(RHS_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
  >> simp[]
  >> rpt(BasicProvers.PURE_FULL_CASE_TAC >> fs[allTypes'_defn])
  >> rpt(BasicProvers.VAR_EQ_TAC) >> fs[]
  >> fs[listTheory.MAP_EQ_CONS]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[]
  >> qmatch_goalsub_abbrev_tac `Funspace a1 a2 = Funspace a3 a4`
  >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
  >> unabbrev_all_tac
  >> conj_tac >> first_x_assum match_mp_tac
  >> metis_tac[]
QED

Theorem is_frag_interpretation_ext:
  !tyfrag tmfrag sig δ γ. is_sig_fragment sig (tyfrag,tmfrag) /\ is_set_theory ^mem
           /\ is_frag_interpretation (tyfrag,tmfrag) δ γ==>
   is_frag_interpretation (builtin_closure tyfrag,
                           tmfrag ∪ builtin_terms(builtin_closure tyfrag))
                          (ext_type_frag_builtins δ)
                          (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)
Proof
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
  >- (rfs[builtin_terms_def,builtin_consts] >> metis_tac[])
QED

Type valuation = ``:mlstring # type -> 'U``

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (δ: type -> 'U) (γ: mlstring # type -> 'U) (v:'U valuation) sigma (Var x ty)
   = v (x,ty)) ∧
  (termsem0 ^mem δ γ v sigma (Const name ty) = γ(name,TYPE_SUBSTf sigma ty)) ∧
  (termsem0 ^mem δ γ v sigma (Comb t1 t2) =
   termsem0 ^mem δ γ v sigma t1 ' (termsem0 ^mem δ γ v sigma t2)) ∧
  (termsem0 ^mem δ γ v sigma (Abs (Var x ty) b) =
   Abstract (δ (TYPE_SUBSTf sigma ty)) (δ (TYPE_SUBSTf sigma (typeof b)))
     (λm. termsem0 ^mem δ γ (((x,ty)=+m)v) sigma b))`

Overload termsem = ``termsem0 ^mem``

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem (δ: type -> 'U) ⇔
    (∀dom rng. δ(Fun dom rng) = Funspace (δ dom) (δ rng)) ∧
    (δ(Bool) = boolset)`
Overload is_std_type_assignment = ``is_std_type_assignment0 ^mem``

Theorem ext_std_type_assignment:
  !ty δ. is_std_type_assignment δ ==> ext_type_frag_builtins δ ty = δ ty
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- fs[ext_type_frag_builtins_def]
  >- (simp[Once ext_type_frag_builtins_def]
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >> fs[is_std_type_assignment_def])
QED

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem tyfrag δ γ ⇔
    is_std_type_assignment δ ∧
    builtin_closure tyfrag = tyfrag ∧
    (!ty1 ty2. Fun ty1 ty2 ∈ tyfrag ==> ty1 ∈ tyfrag /\ ty2 ∈ tyfrag) ∧
    !ty. ty ∈ tyfrag ==> γ(strlit "=", Fun ty (Fun ty Bool)) = Abstract (δ ty) (Funspace (δ ty) boolset)
          (λx. Abstract (δ ty) boolset (λy. Boolean (x = y)))`

Overload is_std_interpretation = ``is_std_interpretation0 ^mem``

Theorem termsem_in_type:
  !tyfrag tmfrag δ γ v sigma tm.
  is_set_theory ^mem /\
  is_std_interpretation tyfrag δ γ /\
  is_frag_interpretation (tyfrag,tmfrag) δ γ /\
  tm ∈ terms_of_frag_uninst (tyfrag,tmfrag) sigma /\
  (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ δ(TYPE_SUBSTf sigma ty))
  ==> termsem δ γ v sigma tm ⋲ δ (TYPE_SUBSTf sigma (typeof tm))
Proof
  Induct_on `tm` >> rpt strip_tac
  >- (fs[VFREE_IN_def,termsem_def])
  >- (fs[termsem_def,is_frag_interpretation_def,terms_of_frag_uninst_def,consts_of_term_def]
      >> rfs[is_std_interpretation_def,ext_std_type_assignment]
      >> fs[nonbuiltin_constinsts_def,builtin_consts,pred_setTheory.SUBSET_DEF]
      >> fs[allTypes_def]
      >> reverse(Cases_on `?ty. Const m (TYPE_SUBSTf sigma t) = Equal ty`)
      >- (fs[pairTheory.ELIM_UNCURRY]
          >> rename1 `γ (name,TYPE_SUBSTf sigma t)`
          >> fs[RIGHT_FORALL_OR_THM]
          >> first_x_assum drule >> simp[])
      >- (fs[PULL_EXISTS] >> rpt(BasicProvers.VAR_EQ_TAC) >> fs[allTypes'_defn,is_std_type_assignment_def] >> fs[listTheory.MEM_FLAT,listTheory.MEM_MAP,PULL_EXISTS]
           >> drule builtin_closure_allTypes''' >> simp[]
           >> strip_tac >> first_x_assum drule
           >> strip_tac >> qpat_x_assum `Fun _ Bool ∈ _` kall_tac
           >> first_x_assum drule >> simp[]
           >> strip_tac
           >> drule abstract_in_funspace
           >> disch_then match_mp_tac >> rw[]
           >> drule abstract_in_funspace
           >> disch_then match_mp_tac >> rw[]
           >> match_mp_tac boolean_in_boolset >> simp[]))
  >- (fs[termsem_def,typeof_def,is_frag_interpretation_def,terms_of_frag_uninst_def,
         is_std_type_assignment_def,is_std_interpretation_def]
      >> drule apply_in_rng >> disch_then(match_mp_tac)
      >> rpt(first_x_assum drule >> rpt(disch_then drule) >> strip_tac)
      >> rfs[allTypes'_defn,allTypes_def,consts_of_term_def,
             PURE_ONCE_REWRITE_RULE [pred_setTheory.INTER_COMM] (pred_setTheory.UNION_OVER_INTER)]
      >> rpt(first_x_assum(qspecl_then [`v`,`sigma`] assume_tac)) >> rfs[]
      >> fs[] >> rfs[]
      >> metis_tac[])
  >- (fs[termsem_def,typeof_def,is_frag_interpretation_def,terms_of_frag_uninst_def,
         is_std_type_assignment_def,is_std_interpretation_def]
      >> drule abstract_in_funspace >> disch_then match_mp_tac
      >> rw[]
      >> first_x_assum match_mp_tac
      >> MAP_EVERY qexists_tac [`tyfrag`,`tmfrag`]
      >> fs[consts_of_term_def,allTypes_def]
      >> rw[]
      >> rw[combinTheory.UPDATE_def] >> fs[] >> metis_tac[])
QED

Theorem termsem_in_type_ext:
  !tyfrag tmfrag δ γ v sigma tm sig.
  is_set_theory ^mem /\ is_sig_fragment sig (tyfrag,tmfrag) /\
  is_frag_interpretation (tyfrag,tmfrag) δ γ /\
  tm ∈ terms_of_frag_uninst (tyfrag,tmfrag) sigma /\
  (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ (ext_type_frag_builtins δ) (TYPE_SUBSTf sigma ty))
  ==> termsem (ext_type_frag_builtins δ) (ext_term_frag_builtins (ext_type_frag_builtins δ) γ) v sigma tm ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma(typeof tm))
Proof
  rpt strip_tac
  >> drule termsem_in_type >> disch_then match_mp_tac
  >> MAP_EVERY qexists_tac [`builtin_closure tyfrag`,`tmfrag ∪ builtin_terms(builtin_closure tyfrag)`]
  >> conj_tac
  >- (simp[is_std_interpretation_def,is_std_type_assignment_def]
      >> simp[Once ext_term_frag_builtins_def, Once ext_type_frag_builtins_def]
      >> simp[Once ext_type_frag_builtins_def]
      >> simp[builtin_closure_idem]
      >> rw[boolTheory.IN_DEF] >> pop_assum(mp_tac o REWRITE_RULE[Once builtin_closure_cases])
      >> strip_tac >> fs[is_sig_fragment_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> rpt(first_x_assum drule) >> simp[nonbuiltin_types_def,is_builtin_type_def]
      >> pop_assum(mp_tac o REWRITE_RULE[Once builtin_closure_cases])
      >> strip_tac >> fs[is_sig_fragment_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> rpt(first_x_assum drule) >> simp[nonbuiltin_types_def,is_builtin_type_def])
  >> conj_tac
  >- (match_mp_tac is_frag_interpretation_ext >> qexists_tac `sig` >> simp[])
  >> conj_tac
  >- (fs[terms_of_frag_uninst_def] >> fs[boolTheory.IN_DEF,pred_setTheory.SUBSET_DEF]
      >> metis_tac[builtin_closure_rules])
  >> rw[]
QED

Theorem termsem_in_type_ext2:
  !frag δ γ v sigma tm sig.
  is_set_theory ^mem /\ is_sig_fragment sig frag /\
  is_frag_interpretation frag δ γ /\
  tm ∈ terms_of_frag_uninst frag sigma /\
  (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ (ext_type_frag_builtins δ) (TYPE_SUBSTf sigma ty))
  ==> termsem (ext_type_frag_builtins δ) (ext_term_frag_builtins (ext_type_frag_builtins δ) γ) v sigma tm ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma(typeof tm))
Proof
  Cases >> metis_tac [termsem_in_type_ext]
QED

(* todo: probably useless. later?
Theorem termsem_in_type_closed:
  !tyfrag tmfrag δ γ v tm.
  is_set_theory ^mem /\
  is_std_interpretation tyfrag δ γ /\
  is_frag_interpretation (tyfrag,tmfrag) δ γ /\
  tm ∈ terms_of_frag (tyfrag,tmfrag) sigma /\
  CLOSED tm
  ==> termsem δ γ v tm ⋲ δ (typeof tm)
Proof
  rpt strip_tac >> drule termsem_in_type
  >> rpt(disch_then drule)
  >> disch_then match_mp_tac
  >> fs[CLOSED_def]
QED
*)

(* todo: useless? *)
val empty_valuation = xDefine "empty_valuation"
  `empty_valuation0 ^mem = (K One):(mlstring # type -> 'U)`;

Overload empty_valuation = ``empty_valuation0 ^mem``

val fleq_def = Define
  `fleq ((tyfrag1,tmfrag1),(δ1: type -> 'U,γ1: mlstring # type -> 'U)) ((tyfrag2,tmfrag2),(δ2,γ2)) =
   (tmfrag1 ⊆ tmfrag2 /\ tyfrag1 ⊆ tyfrag2
    /\ (!c ty. (c,ty) ∈ tmfrag1 ==> γ1(c,ty) = γ2(c,ty))
    /\ (!ty. ty ∈ tyfrag1 ==> δ1 ty = δ2 ty))`

val builtin_closure_mono_lemma = Q.prove(
  `!tys1 ty. builtin_closure tys1 ty ==> !tys2. tys1 ⊆ tys2 ==> builtin_closure tys2 ty`,
  ho_match_mp_tac builtin_closure_ind
  >> rpt strip_tac
  >> metis_tac[builtin_closure_rules,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]);

Theorem builtin_closure_mono:
  !tys1 tys2. tys1 ⊆ tys2 ==> builtin_closure tys1 ⊆ builtin_closure tys2
Proof
  metis_tac[builtin_closure_mono_lemma,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
QED

(* Lemma 9 from Kunčar and Popescu's ITP2015 paper *)

(* 9(1) *)
val fleq_types_le = Q.prove(
  `!frag1 i1 frag2 i2. fleq (frag1,i1) (frag2,i2)
   ==> types_of_frag frag1 ⊆ types_of_frag frag2`,
  rpt Cases
  >> rw[fleq_def,types_of_frag_def]
  >> imp_res_tac builtin_closure_mono);

(* 9(2) *)
Theorem fleq_terms_le:
  !frag1 i1 frag2 i2. fleq (frag1,i1) (frag2,i2)
   ==> terms_of_frag frag1 ⊆ terms_of_frag frag2
Proof
  rpt Cases
  >> rw[fleq_def,terms_of_frag_def,pred_setTheory.SUBSET_DEF]
QED

(* 9(3) *)
Theorem fleq_type_interp_le:
  !ty frag1 δ1 γ1 frag2 δ2 γ2 sig. fleq (frag1,(δ1,γ1)) (frag2,(δ2,γ2)) /\
    is_sig_fragment sig frag1 /\ ty ∈ types_of_frag frag1
   ==> ext_type_frag_builtins δ1 ty = ext_type_frag_builtins δ2 ty
Proof
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[fleq_def,types_of_frag_def]
      >> ONCE_REWRITE_TAC [ext_type_frag_builtins_def]
      >> fs[boolTheory.IN_DEF,Once builtin_closure_cases])
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[types_of_frag_def]
      >> qpat_assum `fleq _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [fleq_def])
      >> fs[boolTheory.IN_DEF,Once builtin_closure_cases]
      >> ONCE_REWRITE_TAC [ext_type_frag_builtins_def]
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >- (fs[is_sig_fragment_def,nonbuiltin_types_def,pred_setTheory.SUBSET_DEF,
             boolTheory.IN_DEF] >> rpt(first_x_assum drule)
          >> simp[is_builtin_type_def,is_builtin_name_def])
      >> qmatch_goalsub_abbrev_tac `Funspace a1 a2 = Funspace a3 a4`
      >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
      >> unabbrev_all_tac
      >> rpt(first_x_assum drule >> rpt(disch_then drule))
      >> simp[types_of_frag_def])
QED

(* 9(4) *)
Theorem fleq_term_interp_le:
  !tm v frag1 δ1 γ1 frag2 δ2 γ2 sig sigma. fleq (frag1,(δ1,γ1)) (frag2,(δ2,γ2)) /\
   is_sig_fragment sig frag1 /\ tm ∈ terms_of_frag_uninst frag1 sigma /\ is_set_theory ^mem /\
   is_frag_interpretation frag1 δ1 γ1 /\
   (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ (ext_type_frag_builtins δ1 (TYPE_SUBSTf sigma ty)))
   ==>
   termsem (ext_type_frag_builtins δ1) (ext_term_frag_builtins (ext_type_frag_builtins δ1) γ1) v sigma tm
   = termsem (ext_type_frag_builtins δ2) (ext_term_frag_builtins (ext_type_frag_builtins δ2) γ2) v sigma tm
Proof
  Induct >> rpt strip_tac
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[termsem_def,VFREE_IN_def])
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[termsem_def,fleq_def]
      >> fs[terms_of_frag_uninst_def,consts_of_term_def,allTypes_def]
      >> fs[nonbuiltin_constinsts_def,builtin_consts]
      >> fs[pred_setTheory.SUBSET_DEF]
      >> rw[ext_term_frag_builtins_def]
      >> fs[]
      >- (
         `ext_type_frag_builtins δ1 ty = ext_type_frag_builtins δ2 ty` suffices_by simp[]
          >> fs[PULL_EXISTS]
          >> fs[is_sig_fragment_def,listTheory.MEM_FLAT,listTheory.MEM_MAP,PULL_EXISTS]
          >> Cases_on `t` >> fs[TYPE_SUBSTf_def,allTypes'_defn]
          >> rfs[] >> fs[nonbuiltin_constinsts_def,nonbuiltin_types_def,is_builtin_type_def,
                         pred_setTheory.SUBSET_DEF]
          >- metis_tac[ext_type_frag_mono_eq]
          >> fs[listTheory.MAP_EQ_CONS,listTheory.MAP_EQ_NIL] >> rpt(BasicProvers.VAR_EQ_TAC)
          >> fs[]
          >> match_mp_tac ext_type_frag_mono_eq''
          >> metis_tac[])
      >> fs[RIGHT_FORALL_OR_THM])
  >- (fs[termsem_def]
      >> qmatch_goalsub_abbrev_tac `a1 ' a2 = a3 ' a4`
      >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
      >> unabbrev_all_tac
      >> rpt(first_x_assum drule >> disch_then drule)
      >> rpt(disch_then(qspec_then `v` assume_tac))
      >> fs[terms_of_frag_uninst_def]
      >> imp_res_tac terms_of_frag_uninst_combE
      >> fs[])
  >- (rename1 `Abs ratortm randtm`
      >> `welltyped(Abs ratortm randtm)` by(Cases_on `frag1` >> fs[terms_of_frag_uninst_def])
      >> fs[termsem_def]
      >> qmatch_goalsub_abbrev_tac `Abstract a1 _ _ = Abstract a2 _ _`
      >> `a1 = a2`
         by(unabbrev_all_tac >> fs[termsem_def]
            >> drule fleq_type_interp_le
            >> disch_then drule >> disch_then match_mp_tac
            >> Cases_on `frag1` >> fs[types_of_frag_def,is_sig_fragment_def,terms_of_frag_uninst_def]
            >> fs[allTypes_def,pred_setTheory.SUBSET_DEF,listTheory.MEM_FLAT,listTheory.MEM_MAP,PULL_EXISTS]
            >> match_mp_tac builtin_closure_allTypes'''
            >> fs[] >> metis_tac[])
      >> simp[] >> drule abstract_eq >> disch_then match_mp_tac
      >> rw[]
      >- (match_mp_tac termsem_in_type_ext
          >> MAP_EVERY qexists_tac [`FST frag1`,`SND frag1`,`sig`]
          >> simp[]
          >> imp_res_tac terms_of_frag_uninst_AbsE
          >> rw[combinTheory.UPDATE_def]
          >> unabbrev_all_tac >> simp[]
          >> first_x_assum match_mp_tac >> fs[])
      >- (imp_res_tac terms_of_frag_uninst_AbsE
          >> first_x_assum drule >> rpt(disch_then drule)
          >> disch_then(qspec_then `((n,ty) =+ x) v` mp_tac)
          >> impl_tac
          >- (rw[combinTheory.UPDATE_def] >> unabbrev_all_tac >> simp[]
              >> first_x_assum match_mp_tac >> fs[])
          >> disch_then (strip_assume_tac o GSYM)
          >> simp[]
          >> `ext_type_frag_builtins δ1 (TYPE_SUBSTf sigma (typeof randtm)) = ext_type_frag_builtins δ2 (TYPE_SUBSTf sigma (typeof randtm))`
               by(drule fleq_type_interp_le >> disch_then match_mp_tac >> qexists_tac `sig` >> simp[]
                  >> match_mp_tac term_frag_uninst_in_type_frag \\ metis_tac[])
          >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [GSYM thm])
          >> match_mp_tac termsem_in_type_ext
          >> MAP_EVERY qexists_tac [`FST frag1`,`SND frag1`,`sig`]
          >> simp[]
          >> imp_res_tac terms_of_frag_AbsE
          >> rw[combinTheory.UPDATE_def]
          >> unabbrev_all_tac >> simp[]
          >> first_x_assum match_mp_tac >> fs[])
      >- (imp_res_tac terms_of_frag_uninst_AbsE
          >> first_x_assum drule >> rpt(disch_then drule)
          >> disch_then(qspec_then `((n,ty) =+ x) v` mp_tac)
          >> impl_tac
          >- (rw[combinTheory.UPDATE_def] >> unabbrev_all_tac >> simp[]
              >> first_x_assum match_mp_tac >> fs[])
          >> disch_then (strip_assume_tac o GSYM)
          >> simp[]))
QED

Theorem fleq_term_interp_le_closed:
  !tm v frag1 δ1 γ1 frag2 δ2 γ2 sig sigma. fleq (frag1,(δ1,γ1)) (frag2,(δ2,γ2)) /\
   is_sig_fragment sig frag1 /\ tm ∈ terms_of_frag_uninst frag1 sigma /\ is_set_theory ^mem /\
   is_frag_interpretation frag1 δ1 γ1 /\
   CLOSED tm
   ==>
   termsem (ext_type_frag_builtins δ1) (ext_term_frag_builtins (ext_type_frag_builtins δ1) γ1) v sigma tm
   = termsem (ext_type_frag_builtins δ2) (ext_term_frag_builtins (ext_type_frag_builtins δ2) γ2) v sigma tm
Proof
  rpt strip_tac >> drule fleq_term_interp_le
  >> rpt(disch_then drule) >> disch_then match_mp_tac
  >> fs[CLOSED_def]
QED

val valuates_frag_def = xDefine "valuates_frag"`
  valuates_frag0 ^mem frag δ v sigma = (!x ty. TYPE_SUBSTf sigma ty ∈ types_of_frag frag ==> v(x,ty) ⋲ (ext_type_frag_builtins δ (TYPE_SUBSTf sigma ty)))`;
Overload valuates_frag = ``valuates_frag0 ^mem``

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem frag δ γ sigma (h,c) ⇔
    ∀v. valuates_frag frag δ v sigma ∧ c ∈ terms_of_frag_uninst frag sigma ∧ EVERY (λt. t ∈ terms_of_frag_uninst frag sigma) h ∧
      EVERY (λt. termsem δ γ v sigma t = True) h
      ⇒ termsem δ γ v sigma c = True`
Overload satisfies = ``satisfies0 ^mem``

(* TODO: move to syntax *)
Theorem LIST_UNION_EQ_NIL:
  LIST_UNION a1 a2 = [] <=> (a1 = [] /\ a2 = [])
Proof
  rw[EQ_IMP_THM]
  \\ `set(LIST_UNION a1 a2) = set []` by(simp_tac list_ss [] \\ pop_assum ACCEPT_TAC)
  \\ fs[]
QED

val total_fragment_def = Define `
  total_fragment sig = (ground_types sig ∩ nonbuiltin_types, ground_consts sig ∩ nonbuiltin_constinsts)`

Theorem ground_types_builtin_closure:
  !c sig. c ∈ ground_types sig ==> c ∈ builtin_closure (ground_types sig ∩ nonbuiltin_types)
Proof
  ho_match_mp_tac type_ind
  \\ rpt strip_tac
  >- (fs[boolTheory.IN_DEF] \\ match_mp_tac builtin_closure_inj
      \\ fs[pred_setTheory.INTER_DEF,boolTheory.IN_DEF,nonbuiltin_types_def,is_builtin_type_def,
            is_builtin_name_def])
  \\ Cases_on `Tyapp m l ∈ nonbuiltin_types`
  >- (fs[boolTheory.IN_DEF] \\ match_mp_tac (builtin_closure_inj) \\
      simp[boolTheory.IN_DEF])
  \\ fs[nonbuiltin_types_def,builtin_types_def,is_builtin_type_def,is_builtin_name_def,
        quantHeuristicsTheory.LIST_LENGTH_2,boolTheory.IN_DEF]
  \\ fs[tyvars_def,ground_types_def,LIST_UNION_EQ_NIL,type_ok_def]
  \\ metis_tac[builtin_closure_rules]
QED

Theorem total_fragment_is_fragment:
  !sig. is_sig_fragment sig (total_fragment sig)
Proof
  rw[total_fragment_def,is_sig_fragment_def,ground_consts_def,nonbuiltin_constinsts_def]
  \\ imp_res_tac ground_types_builtin_closure
QED

Theorem total_fragment_is_top_fragment:
  !sig frag. is_sig_fragment sig frag
   ==> FST frag ⊆ FST(total_fragment sig) /\ SND frag ⊆ SND(total_fragment sig)
Proof
  CONV_TAC(SWAP_FORALL_CONV) \\ Cases \\ rw[total_fragment_def,is_sig_fragment_def]
QED

val satisfies_t_def = xDefine"satisfies_t"`
  satisfies_t0 ^mem sig δ γ (h,c) ⇔
  !sigma.
    (!ty. tyvars(sigma ty) = []) /\
    (!ty. type_ok (tysof sig) (sigma ty)) /\
    EVERY (λtm. tm ∈ ground_terms_uninst sig sigma) h /\ c ∈ ground_terms_uninst sig sigma
    ==> satisfies (total_fragment sig) δ γ sigma (h,c)
  `

Overload satisfies_t = ``satisfies_t0 ^mem``
(*val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)*)

val models_def = xDefine"models"`
  models0 ^mem δ γ (thy:thy) ⇔
    is_frag_interpretation (total_fragment (sigof thy)) δ γ ∧
    ∀p. p ∈ (axsof thy) ⇒
    satisfies_t (sigof thy)
                (ext_type_frag_builtins δ)
                (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)
                ([],p)`
Overload models = ``models0 ^mem``

val entails_def = xDefine"entails"`
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀δ γ. models δ γ thy
      ⇒ satisfies_t (sigof thy)
                    (ext_type_frag_builtins δ)
                    (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)
                    (h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
Overload "|=" = ``entails0 ^mem``

(* TODO: use in many places above *)
val termsem_ext_def = xDefine"termsem_ext"`
  termsem_ext0 ^mem δ γ v t = termsem (ext_type_frag_builtins δ)
                                      (ext_term_frag_builtins (ext_type_frag_builtins δ) γ) v t`
Overload termsem_ext = ``termsem_ext0 ^mem``

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig δ γ v ⇔
    is_frag_interpretation (total_fragment sig) δ γ`
Overload is_structure = ``is_structure0 ^mem``

val _ = export_theory()
