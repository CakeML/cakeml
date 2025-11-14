(*
  Auxiliary functions and lemmas for defining and reasoning about the
  model extension function.
*)
Theory holExtension
Ancestors
  mlstring setSpec holSyntaxLib holSyntax holSyntaxExtra
  holSemantics holSemanticsExtra holSoundness holAxiomsSyntax
  holBool
Libs
  preamble

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

Theorem terminating_descending_nats:
  terminating (\x y. x = SUC y)
Proof
  rw[terminating_def] >>
  assume_tac prim_recTheory.WF_PRED >>
  pop_assum mp_tac >>
  qmatch_goalsub_abbrev_tac `WF f ==> WF g` >>
  `f = g` suffices_by simp[] >>
  unabbrev_all_tac >> rw[FUN_EQ_THM,inv_DEF]
QED

Theorem terminating_IMP_wellfounded_INV:
  terminating R ==> WF(Rᵀ)
Proof
  rw[terminating_def]
QED

Theorem terminating_INV_IMP_wellfounded:
  terminating(Rᵀ) ==> WF(R)
Proof
  strip_tac >> drule terminating_IMP_wellfounded_INV >> rw[inv_inv]
QED

Definition type_matches_def:
  type_matches ty defn =
  case defn of
  | TypeDefn name pred abs rep =>
      (let tyvars = MAP implode (STRING_SORT (MAP explode (tvars pred)))
       in
         case ty of
           Tyvar x => NONE (* shouldn't happen --- we only interpret ground types *)
         | Tyapp name2 tyargs =>
           if name = name2 /\ is_instance (Tyapp name (MAP Tyvar tyvars)) ty then
             SOME(pred,name,tyvars)
           else
             NONE)
  | _ => NONE
End

Definition defn_matches_def:
  defn_matches name ty defn =
  case defn of
  | ConstSpec ov eqs prop =>
      FILTER (λ(name0,trm). name = name0 /\ is_instance (typeof trm) ty) eqs
  | _ => []
End

Definition rep_matches_def:
  rep_matches name ty defn =
  case defn of
  | TypeDefn tyname pred abs rep =>
      (let tvs = MAP implode (STRING_SORT (MAP explode (tvars pred)));
           rep_type = domain (typeof pred);
           abs_type = Tyapp tyname (MAP Tyvar tvs)
       in
         if name = rep /\ is_instance (Fun abs_type rep_type) ty then
           SOME(rep,abs_type,rep_type)
         else
           NONE)
  | _ => NONE
End

Definition abs_matches_def:
  abs_matches name ty defn =
  case defn of
  | TypeDefn tyname pred abs rep =>
       (let tvs = MAP implode (STRING_SORT (MAP explode (tvars pred)));
           rep_type = domain (typeof pred);
           abs_type = Tyapp tyname (MAP Tyvar tvs)
        in
          if name = abs /\ is_instance (Fun rep_type abs_type) ty then
            SOME(abs,abs_type,rep_type)
          else
            NONE)
  | _ => NONE
End

Definition abs_or_rep_matches_def:
  abs_or_rep_matches name ty defn =
  case abs_matches name ty defn of
    NONE =>
    (case rep_matches name ty defn of
       NONE => NONE
     | SOME(rep,abs_type,rep_type) =>
       SOME(F,rep,abs_type,rep_type))
  | SOME(abs,abs_type,rep_type) =>
    SOME(T,abs,abs_type,rep_type)
End

Theorem abs_matches_is_instance:
  mapPartial(abs_or_rep_matches c ty) ctxt = [(T,name0,abs_type,rep_type)] ==>
  name0 = c /\ is_instance (Fun rep_type abs_type) ty
Proof
  rw[abs_matches_def,abs_or_rep_matches_def,mllistTheory.mapPartial_thm,
     FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
  qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
  fs[CaseEq"prod",CaseEq"option",CaseEq "update"] >> rveq >> fs[] >>
  qexists_tac `i` >> rw[]
QED

Theorem rep_matches_is_instance:
  mapPartial(abs_or_rep_matches c ty) ctxt = [(F,name0,abs_type,rep_type)] ==>
  name0 = c /\ is_instance (Fun abs_type rep_type) ty
Proof
  rw[rep_matches_def,abs_or_rep_matches_def,mllistTheory.mapPartial_thm,
     FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
  qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
  fs[CaseEq"prod",CaseEq"option",CaseEq "update"] >> rveq >> fs[] >>
  qexists_tac `i` >> rw[]
QED

Theorem type_matches_is_instance:
  type_matches ty upd = SOME(pred,name,tvs) ==>
  (!x. ty <> Tyvar x) /\ tvs = MAP implode (STRING_SORT (MAP explode (tvars pred))) /\
  is_instance (Tyapp name (MAP Tyvar tvs)) ty
Proof
  rw[type_matches_def,CaseEq"update",CaseEq"type"] >> metis_tac[]
QED

Theorem type_matches_is_instance':
  mapPartial (type_matches ty) ctxt = [(pred,name,tvs)] ==>
  (!x. ty <> Tyvar x) /\ tvs = MAP implode (STRING_SORT (MAP explode (tvars pred))) /\
  is_instance (Tyapp name (MAP Tyvar tvs)) ty
Proof
  rw[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
  rfs[] >>
  fs[type_matches_def,CaseEq"update",CaseEq"type"] >> rveq >> fs[] >> rveq >> fs[] >>
  metis_tac[]
QED

Theorem defn_matches_is_instance:
  defn_matches c ty defn = (name0,trm0)::l ==>
  name0 = c /\ is_instance (typeof trm0) ty
Proof
  rw[defn_matches_def,CaseEq "update",FILTER_EQ_CONS] >> metis_tac[]
QED

Theorem defn_matches_wf:
  defn_matches c ty defn = (name0,trm0)::l /\ defn updates something ==>
  CLOSED trm0 ∧ (∀v. MEM v (tvars trm0) ⇒ MEM v (tyvars (typeof trm0))) /\
  welltyped trm0 /\ term_ok (sigof something) trm0
Proof
  rw[defn_matches_def,CaseEq "update",FILTER_EQ_CONS,Once updates_cases,EVERY_MAP] >>
  fs[EVERY_APPEND] >>
  imp_res_tac proves_term_ok >> fs[equation_def,term_ok_def]
QED

Theorem ZIP_swap:
  !l1 l2.
   LENGTH l1 = LENGTH l2
   ==>
   MAP (λ(x,y). (y,x)) (ZIP(l1,l2)) =  ZIP(l2,l1)
Proof
  Induct >- rw[] >>
  strip_tac >> Cases >> rw[]
QED

Definition subst_clos_term_rel_def:
 subst_clos_term_rel (a1:('U -> 'U -> bool) # 'U # update list # type +
    ('U -> 'U -> bool) # 'U # update list # mlstring # type)
                     (a2:('U -> 'U -> bool) # 'U # update list # type +
    ('U -> 'U -> bool) # 'U # update list # mlstring # type) =
 let
   ctxt1 = sum_CASE a1 (FST o SND o SND) (FST o SND o SND);
   ctxt2 = sum_CASE a2 (FST o SND o SND) (FST o SND o SND);
   mem1 = sum_CASE a1 FST FST;
   mem2 = sum_CASE a2 FST FST;
   ind1 = sum_CASE a1 (FST o SND) (FST o SND);
   ind2 = sum_CASE a2 (FST o SND) (FST o SND);
 in
   if ctxt1 = ctxt2 /\ mem1 = mem2 /\ ind1 = ind2 /\ terminating(subst_clos(dependency ctxt2))
   then
     case (a1,a2) of
     | (INL(_,_,_,typ1),INL(_,_,_,typ2)) => (subst_clos (dependency ctxt2))⁺ (INL typ2) (INL typ1)
     | (INL(_,_,_,typ1),INR(_,_,_,c2,typ2)) => (subst_clos (dependency ctxt2))⁺ (INR(Const c2 typ2)) (INL typ1)
     | (INR(_,_,_,c1,typ1),INL(_,_,_,typ2)) => (subst_clos (dependency ctxt2))⁺ (INL typ2) (INR(Const c1 typ1))
     | (INR(_,_,_,c1,typ1),INR(_,_,_,c2,typ2)) => (subst_clos (dependency ctxt2))⁺ (INR(Const c2 typ2)) (INR(Const c1 typ1))
   else F
End

Theorem LIST_LENGTH_2[local]:
  LENGTH l = 2 ⇔ ∃e1 e2. l = [e1; e2]
Proof
  Cases_on ‘l’ \\ fs [] \\ Cases_on ‘t’ \\ fs []
QED

Theorem allTypes'_subst_clos_dependency:
  !ty ty0 ctxt.
  ctxt extends init_ctxt /\
  MEM ty0 (allTypes' ty) /\
  ty0 <> ty ==>
  (subst_clos (dependency ctxt))⁺ (INL ty) (INL ty0)
Proof
  ho_match_mp_tac allTypes'_defn_ind >>
  rw[] >>
  fs[allTypes'_defn] >>
  every_case_tac >> fs[] >>
  rveq >>
  fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
  Cases_on `ty0 = a`
  >- (rveq >>
      match_mp_tac TC_SUBSET >>
      fs[LIST_LENGTH_2] >>
      rveq >> fs[subst_clos_def] >-
        (qexists_tac `Fun (Tyvar(strlit "a")) (Tyvar(strlit "aa"))` >>
         qexists_tac `Tyvar(strlit "a")` >>
         qexists_tac `[(e1,Tyvar(strlit "a"));(e2,Tyvar(strlit "aa"))]` >>
         simp[REV_ASSOCD_def] >>
         `MEM (NewType (strlit"fun") 2) ctxt`
           by(imp_res_tac extends_appends >> simp[init_ctxt_def]) >>
         drule (List.nth(dependency_rules |> CONJUNCTS,5)) >>
         simp[DISJ_IMP_THM,FORALL_AND_THM] >>
         EVAL_TAC >> simp[]) >-
        (qexists_tac `Fun (Tyvar(strlit "a")) (Tyvar(strlit "aa"))` >>
         qexists_tac `Tyvar(strlit "aa")` >>
         qexists_tac `[(e1,Tyvar(strlit "a"));(e2,Tyvar(strlit "aa"))]` >>
         simp[REV_ASSOCD_def] >>
         `MEM (NewType (strlit"fun") 2) ctxt`
           by(imp_res_tac extends_appends >> simp[init_ctxt_def]) >>
         drule (List.nth(dependency_rules |> CONJUNCTS,5)) >>
         simp[DISJ_IMP_THM,FORALL_AND_THM] >>
         EVAL_TAC >> simp[])) >>
  match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
  qexists_tac `INL a` >>
  conj_tac >-
    (rveq >>
      match_mp_tac TC_SUBSET >>
      fs[LIST_LENGTH_2] >>
      rveq >> fs[subst_clos_def] >-
        (qexists_tac `Fun (Tyvar(strlit "a")) (Tyvar(strlit "aa"))` >>
         qexists_tac `Tyvar(strlit "a")` >>
         qexists_tac `[(e1,Tyvar(strlit "a"));(e2,Tyvar(strlit "aa"))]` >>
         simp[REV_ASSOCD_def] >>
         `MEM (NewType (strlit"fun") 2) ctxt`
           by(imp_res_tac extends_appends >> simp[init_ctxt_def]) >>
         drule (List.nth(dependency_rules |> CONJUNCTS,5)) >>
         simp[DISJ_IMP_THM,FORALL_AND_THM] >>
         EVAL_TAC >> simp[]) >-
        (qexists_tac `Fun (Tyvar(strlit "a")) (Tyvar(strlit "aa"))` >>
         qexists_tac `Tyvar(strlit "aa")` >>
         qexists_tac `[(e1,Tyvar(strlit "a"));(e2,Tyvar(strlit "aa"))]` >>
         simp[REV_ASSOCD_def] >>
         `MEM (NewType (strlit"fun") 2) ctxt`
           by(imp_res_tac extends_appends >> simp[init_ctxt_def]) >>
         drule (List.nth(dependency_rules |> CONJUNCTS,5)) >>
         simp[DISJ_IMP_THM,FORALL_AND_THM] >>
         EVAL_TAC >> simp[])) >>
  metis_tac[]
QED

Theorem consts_of_term_nonbuiltin_allCInsts:
  !trm c ty sig.
  (c,ty) ∈ consts_of_term trm /\
  (c,ty) ∈ nonbuiltin_constinsts /\
  term_ok sig trm
  ==>
  MEM (Const c ty) (allCInsts trm)
Proof
  Induct >> rw[consts_of_term_def,allCInsts_def] >-
    (Cases_on `t` >>
     fs[nonbuiltin_constinsts_def,builtin_consts_def,allCInsts_def,builtin_const_def,init_ctxt_def] >>
     rw[]) >>
  fs[term_ok_def] >>
  res_tac >> simp[] >>
  rveq >> fs[consts_of_term_def]
QED

Theorem MEM_allTypes'_TYPE_SUBST_decompose:
  !ty0 ty. MEM ty (allTypes' (TYPE_SUBST sigma ty0)) ==>
  ?ty1. MEM ty1 (allTypes' ty0) /\
        MEM ty (allTypes'(TYPE_SUBST sigma ty1))
Proof
  ho_match_mp_tac type_ind >>
  rw[allTypes'_defn] >>
  rw[] >> rfs[MEM_FLAT,MEM_MAP,EVERY_MEM,PULL_EXISTS] >>
  fs[allTypes'_defn] >> metis_tac[]
QED

Theorem abs_or_rep_matches_abstype:
  mapPartial(abs_or_rep_matches c ty) ctxt = [(b,name0,abs_type,rep_type)] /\
  ctxt extends init_ctxt
  ==>
  allTypes' abs_type = [abs_type]
Proof
  Cases_on `b` >>
  (rw[abs_matches_def,rep_matches_def,abs_or_rep_matches_def,mllistTheory.mapPartial_thm,
     FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
   qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
   fs[CaseEq"prod",CaseEq"option",CaseEq "update"] >> rveq >> fs[] >>
   rveq >> fs[] >> rw[allTypes'_defn] >>
   (drule extends_trans >>
    disch_then(assume_tac o (fn thm => MATCH_MP thm init_ctxt_extends)) >>
    pop_assum(assume_tac o PURE_REWRITE_RULE[GSYM APPEND_ASSOC]) >>
    dxrule extends_APPEND_NIL >> disch_then(assume_tac o SIMP_RULE (srw_ss())[]) >>
    dxrule_then assume_tac extends_NIL_CONS_updates >>
    drule extends_append_MID >> impl_tac >- rw[init_ctxt_def] >>
    strip_tac >>
    drule is_std_sig_extends >> simp[is_std_sig_init] >> strip_tac >>
    fs[updates_cases,is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,GSYM(IMP_DISJ_THM |> ONCE_REWRITE_RULE[DISJ_SYM])] >>
    res_tac >> fs[]))
QED

Theorem ext_inhabited_frag_inhabited:
  ∀^mem. is_set_theory ^mem ==>
   (∀δ ty.
  (ty ∈ ground_types sig /\
  (∀ty'.
     (ty' ∈ ground_types sig ∧ ty' ∈ nonbuiltin_types) ⇒
     inhabited (δ ty'))) ==>
  inhabited(ext_type_frag_builtins δ ty))
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[PULL_FORALL,AND_IMP_INTRO] >>
  ho_match_mp_tac ext_type_frag_builtins_ind >>
  rw[] >> fs[FORALL_AND_THM] >>
  rw[Once ext_type_frag_builtins_def] >>
  rpt(TOP_CASE_TAC >> fs[] >> rveq)
  >- fs[ground_types_def,tyvars_def] >>
  TRY(first_x_assum match_mp_tac >> rw[nonbuiltin_types_def,is_builtin_type_def] >> NO_TAC)
  >- (drule_then match_mp_tac funspace_inhabited >>
      conj_tac >> first_x_assum match_mp_tac >>
      fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def]) >>
  metis_tac[boolean_in_boolset]
QED

Theorem ext_inhabited_frag_inhabited':
  ∀^mem. is_set_theory ^mem ==>
   (∀δ ty.
  (ty ∈ ground_types sig /\
  (∀ty'.
     (ty' ∈ ground_types sig ∧ ty' ∈ nonbuiltin_types ∧ MEM ty' (allTypes' ty)) ⇒
     inhabited (δ ty'))) ==>
  inhabited(ext_type_frag_builtins δ ty))
Proof
  Ho_Rewrite.PURE_REWRITE_TAC[PULL_FORALL,AND_IMP_INTRO] >>
  ho_match_mp_tac ext_type_frag_builtins_ind >>
  rw[] >> fs[FORALL_AND_THM] >>
  rw[Once ext_type_frag_builtins_def] >>
  rpt(TOP_CASE_TAC >> fs[] >> rveq)
  >- fs[ground_types_def,tyvars_def] >>
  TRY(first_x_assum match_mp_tac >> rw[nonbuiltin_types_def,is_builtin_type_def,allTypes'_defn] >> NO_TAC)
  >- (drule_then match_mp_tac funspace_inhabited >>
      conj_tac >> first_x_assum match_mp_tac >>
      fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def,allTypes'_defn]
     ) >>
  metis_tac[boolean_in_boolset]
QED

Theorem TYPE_SUBSTf_I:
  !ty. TYPE_SUBSTf Tyvar ty = ty
Proof
  ho_match_mp_tac type_ind >> rw[TYPE_SUBSTf_def] >>
  pop_assum mp_tac >> Induct_on `l` >> rw[]
QED

Theorem TYPE_SUBST_eq_TYPE_SUBSTf:
  TYPE_SUBST sigma ty =
  TYPE_SUBSTf (λx. (REV_ASSOCD (Tyvar x) sigma (Tyvar x))) ty
Proof
  qspecl_then [`ty`,`Tyvar`,`sigma`] mp_tac TYPE_SUBSTf_TYPE_SUBST_compose >>
  rw[TYPE_SUBSTf_I]
QED

Theorem TYPE_SUBST_allTypes'_ground_types:
  !ty.
  TYPE_SUBST sigma ty ∈ ground_types sig ==>
  set (MAP (TYPE_SUBST sigma) (allTypes' ty)) ⊆ ground_types sig
Proof
  ho_match_mp_tac allTypes'_defn_ind >> rw[allTypes'_defn] >>
  fs[LIST_LENGTH_2] >> rveq >>
  conj_tac >> first_x_assum(match_mp_tac o MP_CANON) >>
  rw[] >>
  fs[ground_types_def,tyvars_def,type_ok_def,LIST_UNION_EQ_NIL]
QED

Theorem consts_of_term_tyvars_tvars:
  !trm0 c' ty ty'. (c',ty) ∈ consts_of_term trm0 /\
  MEM ty' (tyvars ty)
  ==>
  MEM ty' (tvars trm0)
Proof
  ho_match_mp_tac consts_of_term_ind >>
  rw[tvars_def,consts_of_term_def] >>
  res_tac >> rw[]
QED

(* TODO: move *)
Theorem type_ok_TYPE_SUBST_strong:
  ∀s tyin ty.
      type_ok s ty ∧
      (∀x. MEM x (tyvars ty) ⇒ type_ok s (TYPE_SUBST tyin (Tyvar x)))
    ⇒ type_ok s (TYPE_SUBST tyin ty)
Proof
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[type_ok_def] >> rw[EVERY_MAP,EVERY_MEM] >>
  fs[FORALL_PROD,tyvars_def,MEM_FOLDR_LIST_UNION,PULL_EXISTS] >>
  metis_tac[REV_ASSOCD_MEM,type_ok_def]
QED

Theorem ground_consts_TYPE_SUBST_lemma:
  (c,TYPE_SUBST sigma (typeof trm0)) ∈ ground_consts sig /\
  term_ok sig trm0 /\
  (∀v. MEM v (tvars trm0) ⇒ MEM v (tyvars (typeof trm0))) /\
  (c',ty) ∈ consts_of_term trm0 ==>
  (c',TYPE_SUBST sigma ty) ∈ ground_consts sig
Proof
  rw[ground_consts_def,ground_types_def]
  >- (drule_then assume_tac consts_of_term_tyvars_tvars >>
      `!tv. MEM tv (tyvars (TYPE_SUBST sigma ty)) ==> F`
        suffices_by(Cases_on `tyvars (TYPE_SUBST sigma ty)` >> fs[FORALL_AND_THM]) >>
      rw[tyvars_TYPE_SUBST,GSYM IMP_DISJ_THM] >>
      `!x. MEM x (tyvars (TYPE_SUBST sigma (typeof trm0))) ==> F`
        by(Cases_on `tyvars (TYPE_SUBST sigma (typeof trm0))` >> fs[FORALL_AND_THM]) >>
      last_x_assum kall_tac >>
      fs[tyvars_TYPE_SUBST,GSYM IMP_DISJ_THM])
  >- (match_mp_tac type_ok_TYPE_SUBST_strong >>
      drule_all_then assume_tac consts_of_term_ok >>
      rw[] >>
      drule_then assume_tac consts_of_term_tyvars_tvars >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      ntac 3 res_tac >> fs[])
  >- (drule_all_then assume_tac consts_of_term_ok >>
      drule_all_then assume_tac consts_of_term_term_ok >>
      fs[term_ok_def] >>
      reverse conj_tac >- (
         rw[Once TYPE_SUBST_eq_TYPE_SUBSTf] >>
         rw[TYPE_SUBSTf_TYPE_SUBST_compose] >>
         MATCH_ACCEPT_TAC TYPE_SUBSTf_TYPE_SUBST) >>
      pop_assum(SUBST_ALL_TAC o GSYM) >>
      match_mp_tac type_ok_TYPE_SUBST_strong >>
      drule_all_then assume_tac consts_of_term_ok >>
      rw[] >>
      drule_then assume_tac consts_of_term_tyvars_tvars >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      ntac 3 res_tac >> fs[])
QED

Theorem ground_consts_TYPE_SUBST_lemma':
  TYPE_SUBST sigma (typeof trm0) ∈ ground_types sig /\
  term_ok sig trm0 /\
  (∀v. MEM v (tvars trm0) ⇒ MEM v (tyvars (typeof trm0))) /\
  (c',ty) ∈ consts_of_term trm0 ==>
  (c',TYPE_SUBST sigma ty) ∈ ground_consts sig
Proof
  rw[ground_consts_def,ground_types_def]
  >- (drule_then assume_tac consts_of_term_tyvars_tvars >>
      `!tv. MEM tv (tyvars (TYPE_SUBST sigma ty)) ==> F`
        suffices_by(Cases_on `tyvars (TYPE_SUBST sigma ty)` >> fs[FORALL_AND_THM]) >>
      rw[tyvars_TYPE_SUBST,GSYM IMP_DISJ_THM] >>
      `!x. MEM x (tyvars (TYPE_SUBST sigma (typeof trm0))) ==> F`
        by(Cases_on `tyvars (TYPE_SUBST sigma (typeof trm0))` >> fs[FORALL_AND_THM]) >>
      last_x_assum kall_tac >>
      fs[tyvars_TYPE_SUBST,GSYM IMP_DISJ_THM])
  >- (match_mp_tac type_ok_TYPE_SUBST_strong >>
      drule_all_then assume_tac consts_of_term_ok >>
      rw[] >>
      drule_then assume_tac consts_of_term_tyvars_tvars >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      ntac 3 res_tac >> fs[])
  >- (drule_all_then assume_tac consts_of_term_ok >>
      drule_all_then assume_tac consts_of_term_term_ok >>
      fs[term_ok_def] >>
      reverse conj_tac >- (
         rw[Once TYPE_SUBST_eq_TYPE_SUBSTf] >>
         rw[TYPE_SUBSTf_TYPE_SUBST_compose] >>
         MATCH_ACCEPT_TAC TYPE_SUBSTf_TYPE_SUBST) >>
      pop_assum(SUBST_ALL_TAC o GSYM) >>
      match_mp_tac type_ok_TYPE_SUBST_strong >>
      drule_all_then assume_tac consts_of_term_ok >>
      rw[] >>
      drule_then assume_tac consts_of_term_tyvars_tvars >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      ntac 3 res_tac >> fs[])
QED

Theorem term_ok_subterm:
  !sig trm0 trm. trm0 subterm trm /\ term_ok sig trm ==> term_ok sig trm0
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  strip_tac >> ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >>
  res_tac >>
  fs[subterm1_cases] >> rveq >> fs[term_ok_def]
QED

Theorem subterm_allTypes:
  !sig trm0 trm. trm0 subterm trm /\ term_ok sig trm ==> set(allTypes trm0) ⊆ set(allTypes trm)
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  strip_tac >> ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >>
  res_tac >>
  fs[subterm1_cases] >> rveq >>
  imp_res_tac term_ok_subterm >> fs[tyvars_def,term_ok_def] >>
  fs[allTypes_def]
QED

Theorem allTypes'_consts_of_term_IMP:
  !trm0 c ty0 ty.
  MEM ty (allTypes' ty0) /\
  (c,ty0) ∈ consts_of_term trm0 ==>
  MEM ty (allTypes trm0)
Proof
  ho_match_mp_tac consts_of_term_ind >>
  rw[allTypes_def,consts_of_term_def] >>
  res_tac >> simp[]
QED

Theorem abs_or_rep_matches_ext_type_frag_builtins:
  mapPartial(abs_or_rep_matches c ty) ctxt = [(b,name0,abs_type,rep_type)] /\
  ctxt extends init_ctxt
  ==>
  ext_type_frag_builtins σ (TYPE_SUBST sigma abs_type) = σ (TYPE_SUBST sigma abs_type)
Proof
  Cases_on `b` >>
  (rw[abs_matches_def,rep_matches_def,abs_or_rep_matches_def,mllistTheory.mapPartial_thm,
     FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
   qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
   fs[CaseEq"prod",CaseEq"option",CaseEq "update"] >> rveq >> fs[] >>
   rveq >> fs[] >> rw[allTypes'_defn] >>
   (drule extends_trans >>
    disch_then(assume_tac o (fn thm => MATCH_MP thm init_ctxt_extends)) >>
    pop_assum(assume_tac o PURE_REWRITE_RULE[GSYM APPEND_ASSOC]) >>
    dxrule extends_APPEND_NIL >> disch_then(assume_tac o SIMP_RULE (srw_ss())[]) >>
    dxrule_then assume_tac extends_NIL_CONS_updates >>
    drule extends_append_MID >> impl_tac >- rw[init_ctxt_def] >>
    strip_tac >>
    drule is_std_sig_extends >> simp[is_std_sig_init] >> strip_tac >>
    fs[updates_cases,is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,GSYM(IMP_DISJ_THM |> ONCE_REWRITE_RULE[DISJ_SYM])] >>
    res_tac >> fs[] >>
    simp[Once ext_type_frag_builtins_def] >>
    rpt(PURE_TOP_CASE_TAC >> fs[] >> rveq)))
QED

Theorem mapPartial_APPEND:
  mapPartial f (a++b) = mapPartial f a ++ mapPartial f b
Proof
  rw[mllistTheory.mapPartial_thm,FILTER_APPEND]
QED

Theorem abs_or_rep_matches_type_matches:
  mapPartial(abs_or_rep_matches c ty) ctxt = [(F,name0,abs_type,rep_type)] /\
  ctxt extends init_ctxt
  ==>
  ?ctxt1 upd ctxt2.
    ctxt = ctxt1 ++ [upd] ++ ctxt2 /\
    mapPartial(abs_or_rep_matches c ty) ctxt1 = [] /\
    mapPartial(type_matches(domain ty)) ctxt1 = [] /\
    mapPartial(abs_or_rep_matches c ty) ctxt2 = [] /\
    mapPartial(type_matches(domain ty)) ctxt2 = [] /\
    abs_or_rep_matches c ty upd = SOME(F,name0,abs_type,rep_type) /\
    IS_SOME(type_matches (domain ty) upd)
Proof
  disch_then(assume_tac o REWRITE_RULE[mllistTheory.mapPartial_thm]) >>
  fs[MAP_EQ_CONS,FILTER_EQ_CONS,MAP_EQ_APPEND] >> rveq >> fs[IS_SOME_EXISTS] >> rfs[] >>
  rename1 `ctxt1 ++ [upd] ++ ctxt2` >>
  MAP_EVERY qexists_tac [`ctxt1`,`upd`,`ctxt2`] >>
  simp[] >>
  qpat_x_assum `abs_or_rep_matches _ _ _ = SOME _` (assume_tac o REWRITE_RULE[abs_or_rep_matches_def]) >>
  fs[abs_matches_def,rep_matches_def,CaseEq"prod",CaseEq"option",CaseEq"update"] >> rveq >> fs[] >>
  rveq >> fs[] >>
  pop_assum kall_tac >>
  drule extends_trans >> disch_then(assume_tac o C MATCH_MP init_ctxt_extends) >>
  pop_assum(assume_tac o PURE_REWRITE_RULE[GSYM APPEND_ASSOC]) >>
  drule_then assume_tac extends_APPEND_NIL >>
  fs[] >>
  dxrule_then assume_tac extends_NIL_CONS_updates >>
  fs[updates_cases] >>
  (conj_tac >- simp[mllistTheory.mapPartial_thm] >>
   conj_tac >-
     (rw[mllistTheory.mapPartial_thm,FILTER_EQ_NIL,MEM_MAP,EVERY_MEM,type_matches_def] >>
      TOP_CASE_TAC >> simp[] >>
      qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[] >>
      FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
      drule_then assume_tac extends_APPEND_NIL >>
      fs[] >>
      dxrule_then assume_tac extends_NIL_CONS_updates >>
      fs[updates_cases]
     ) >>
   conj_tac >- simp[mllistTheory.mapPartial_thm] >>
   conj_tac >-
     (rw[mllistTheory.mapPartial_thm,FILTER_EQ_NIL,MEM_MAP,EVERY_MEM,type_matches_def] >>
      TOP_CASE_TAC >> simp[] >>
      qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[]
     ) >>
   simp[type_matches_def] >> metis_tac[])
QED

Theorem abs_or_rep_matches_type_matches':
  abs_or_rep_matches c ty upd = SOME(b,name0,abs_type,rep_type) /\
  type_matches ty' upd = SOME(pred,name1,tvs)
  ==>
  rep_type = domain(typeof pred) /\
  abs_type = Tyapp name1 (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred)))))
Proof
  rw[abs_or_rep_matches_def,abs_matches_def,rep_matches_def,type_matches_def,
     CaseEq "update",CaseEq"type",CaseEq"option",CaseEq"prod"]
QED

(* TODO: move to syntax *)
Theorem term_ok_extends:
   ∀upd ctxt. upd extends ctxt ⇒
      term_ok (sigof ctxt) tm ⇒
      term_ok (sigof upd) tm
Proof
  simp[extends_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >>
  imp_res_tac term_ok_updates >>
  fs[]
QED

Theorem term_ok_extends_APPEND:
  term_ok (sigof sig2) trm /\
  sig1 ++ sig2 extends [] ==>
  term_ok (sigof(sig1 ++ sig2)) trm
Proof
  rpt strip_tac >>
  match_mp_tac (MP_CANON term_ok_extends) >>
  imp_res_tac extends_NIL_APPEND_extends >>
  goal_assum drule >> rw[]
QED

Theorem allTypes'_TYPE_SUBST_no_tyvars:
  !ty x sigma.
  tyvars (TYPE_SUBST sigma ty) = [] /\
  MEM x (allTypes' ty) ==>
  tyvars(TYPE_SUBST sigma x) = []
Proof
  ho_match_mp_tac allTypes'_defn_ind >>
  rw[allTypes'_defn] >>
  fs[LIST_LENGTH_2,MEM_FLAT,MEM_MAP] >>
  rveq >>
  fs[FORALL_AND_THM,DISJ_IMP_THM,tyvars_def,LIST_UNION_EQ_NIL] >>
  rveq >> res_tac
QED

Theorem allTypes'_TYPE_SUBST_no_tyvars':
  !ty trm x sigma.
  tyvars (TYPE_SUBST sigma (typeof trm)) = [] /\
  MEM x (allTypes' ty) /\
  (∀v. MEM v (tyvars ty) ⇒ MEM v (tyvars (typeof trm))) ==>
  tyvars(TYPE_SUBST sigma x) = []
Proof
  ho_match_mp_tac allTypes'_defn_ind >>
  rw[allTypes'_defn] >>
  fs[LIST_LENGTH_2,MEM_FLAT,MEM_MAP] >>
  rveq >>
  fs[FORALL_AND_THM,DISJ_IMP_THM,tyvars_def,LIST_UNION_EQ_NIL] >>
  rveq >> res_tac >>
  fs[MEM_FOLDR_LIST_UNION,PULL_EXISTS] >>
  TRY(match_mp_tac FOLDR_LIST_UNION_empty) >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rw[] >> res_tac >>
  TRY(drule_then(qspecl_then [`sigma`] assume_tac) (tyvars_TYPE_SUBST_mono |> REWRITE_RULE [SUBSET_DEF]) >> rfs[] >>
      Cases_on `tyvars(TYPE_SUBST sigma a)` >> fs[FORALL_AND_THM] >> NO_TAC) >>
  `set(tyvars(TYPE_SUBST sigma (typeof trm))) = {}` by simp[] >>
  last_x_assum kall_tac >>
  pop_assum(assume_tac o REWRITE_RULE[tyvars_TYPE_SUBST]) >>
  fs[FUN_EQ_THM] >>
  pop_assum (qspec_then `n` assume_tac o CONV_RULE SWAP_FORALL_CONV) >>
  rfs[] >>
  Cases_on `tyvars (REV_ASSOCD (Tyvar n) sigma (Tyvar n))` >> fs[FORALL_AND_THM]
QED

Theorem allTypes_TYPE_SUBST_no_tyvars:
  !trm0 trm x sigma.
  tyvars (TYPE_SUBST sigma (typeof trm)) = [] /\
  MEM x (allTypes trm0) /\
  (∀v. MEM v (tvars trm0) ⇒ MEM v (tyvars (typeof trm)))
  ==>
  tyvars(TYPE_SUBST sigma x) = []
Proof
  Induct >> rw[allTypes_def]
  >- (fs[tvars_def] >> imp_res_tac allTypes'_TYPE_SUBST_no_tyvars')
  >- (fs[tvars_def] >> imp_res_tac allTypes'_TYPE_SUBST_no_tyvars') >>
  fs[tvars_def,DISJ_IMP_THM,FORALL_AND_THM] >>
  res_tac
QED

Theorem TYPE_SUBST_allTypes'_ground_types':
  !ty.
  TYPE_SUBST sigma ty ∈ ground_types sig ==>
  set (allTypes'(TYPE_SUBST sigma ty)) ⊆ ground_types sig
Proof
  ho_match_mp_tac allTypes'_defn_ind >> rw[allTypes'_defn] >>
  fs[LIST_LENGTH_2] >> rveq >>
  fs[FORALL_AND_THM,DISJ_IMP_THM] >>
  fs[ground_types_def,tyvars_def,type_ok_def,LIST_UNION_EQ_NIL,SUBSET_DEF] >>
  rw[]
  >- (imp_res_tac allTypes'_TYPE_SUBST_no_tyvars' >>
      pop_assum(qspec_then `Var ARB (REV_ASSOCD (Tyvar n) sigma (Tyvar n))` mp_tac) >>
      rw[] >>
      pop_assum(qspec_then `[]` mp_tac) >> fs[])
  >- imp_res_tac allTypes'_type_ok
QED

Theorem nonbuiltin_constinsts_TYPE_SUBSTf:
  !ty c sigma.
  (c,TYPE_SUBSTf sigma ty) ∈ nonbuiltin_constinsts ==>
  (c,ty) ∈ nonbuiltin_constinsts
Proof
  rw[nonbuiltin_constinsts_def,builtin_consts_def] >>
  simp[] >>
  Cases_on `?ty'. ty = Fun ty' (Fun ty' Bool)` >> fs[] >> fs[]
QED

Theorem allTypes'_builtin_closure_IMP:
  !ty ty'. MEM ty' (allTypes' ty) /\ ty ∈ builtin_closure tyfrag /\ tyfrag ⊆ nonbuiltin_types ==>
  ty' ∈ tyfrag
Proof
 ho_match_mp_tac allTypes'_defn_ind >>
 rw[allTypes'_defn] >>
 fs[MEM_FLAT,MEM_MAP,LIST_LENGTH_2] >>
 rveq >> fs[DISJ_IMP_THM,FORALL_AND_THM] >>
 rveq >> res_tac >>
 fs[IN_DEF]
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
 >- (qhdtm_x_assum `builtin_closure` (strip_assume_tac o REWRITE_RULE[Once builtin_closure_cases]) >>
     fs[SUBSET_DEF,IN_DEF] >> res_tac >>
     fs[nonbuiltin_types_def,is_builtin_type_def])
QED

Theorem is_frag_intepretation_ifE:
  is_frag_interpretation (tyfrag,tmfrag) (λty'. if ty' ∈ tyfrag then σ' ty' else whatevz) γ /\
  is_sig_fragment sig (tyfrag,tmfrag)
  ==>
  is_frag_interpretation (tyfrag,tmfrag) σ' γ
Proof
  rw[is_frag_interpretation_def,is_type_frag_interpretation_def,is_sig_fragment_def,GSYM PFORALL_THM] >>
  res_tac >>
  `ext_type_frag_builtins σ' ty = ext_type_frag_builtins
              (λty'. if ty' ∈ tyfrag then σ' ty' else whatevz) ty`
   by(match_mp_tac ext_type_frag_mono_eq >>
      rw[] >>
      imp_res_tac allTypes'_nonbuiltin >>
      imp_res_tac allTypes'_builtin_closure_IMP) >>
  pop_assum SUBST_ALL_TAC >> pop_assum ACCEPT_TAC
QED

Theorem is_frag_interpretation_mono:
  !frag frag' σ γ.
  is_frag_interpretation frag' σ γ /\
  FST(frag) ⊆ FST(frag') /\ SND(frag) ⊆ SND(frag') ==>
  is_frag_interpretation frag σ γ
Proof
  Cases >> Cases >>
  rw[is_frag_interpretation_def,is_type_frag_interpretation_def,SUBSET_DEF,GSYM PFORALL_THM]
QED

Theorem is_frag_intepretation_ifI:
  is_frag_interpretation (tyfrag,tmfrag) σ' (UNCURRY γ) /\ is_sig_fragment sig (tyfrag,tmfrag)
  ==>
  is_frag_interpretation (tyfrag,tmfrag) (λty'. if ty' ∈ tyfrag then σ' ty' else whatevz) (λ(c,ty'). if (c,ty') ∈ tmfrag then γ c ty' else whatevz' c ty')
Proof
  rw[is_frag_interpretation_def,is_type_frag_interpretation_def,is_sig_fragment_def,GSYM PFORALL_THM] >>
  res_tac >>
  `ext_type_frag_builtins σ' ty = ext_type_frag_builtins
              (λty'. if ty' ∈ tyfrag then σ' ty' else whatevz) ty`
   by(match_mp_tac(GSYM ext_type_frag_mono_eq) >>
      rw[] >>
      imp_res_tac allTypes'_nonbuiltin >>
      imp_res_tac allTypes'_builtin_closure_IMP) >>
  pop_assum SUBST_ALL_TAC >> pop_assum ACCEPT_TAC
QED

Theorem ext_type_frag_builtins_Fun:
  ext_type_frag_builtins σ (Fun ty1 ty2) =
  Funspace (ext_type_frag_builtins σ ty1) (ext_type_frag_builtins σ ty2)
Proof
  rw[Once ext_type_frag_builtins_def]
QED

Theorem ext_type_frag_builtins_Bool:
  ext_type_frag_builtins σ Bool = boolset
Proof
  rw[Once ext_type_frag_builtins_def]
QED

Theorem proves_theory_mono:
 !thyh prop. thyh |- prop ==>
       (!tyenv tmenv axs tyenv' tmenv' hyps.
         (thyh = (((tyenv,tmenv),axs),hyps)) ∧ tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' /\
          theory_ok ((tyenv',tmenv'),axs)
         ==>
        (((tyenv',tmenv'),axs),hyps) |- prop)
Proof
  ho_match_mp_tac proves_ind >> rw[] >>
  TRY(match_mp_tac (List.nth(CONJUNCTS proves_rules,7)) >> fs[] >> NO_TAC) >>
  MAP_FIRST match_mp_tac (CONJUNCTS proves_rules) >>
  fs[EVERY_MEM] >> metis_tac[type_ok_extend,term_ok_extend]
QED

Theorem TYPE_SUBSTf_in_types_of_frag_I:
 !trm x ty sigma frag sig.
  VFREE_IN (Var x ty) trm /\ is_sig_fragment sig frag /\
  trm ∈ terms_of_frag_uninst frag sigma ==>
  TYPE_SUBSTf sigma ty ∈ types_of_frag frag
Proof
  Induct >> rw[]
  >- (Cases_on `frag` >> fs[terms_of_frag_uninst_def] >>
      fs[consts_of_term_def,allTypes_def,SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
      drule builtin_closure_allTypes''' >>
      rw[types_of_frag_def])
  >- (drule_all_then strip_assume_tac terms_of_frag_uninst_combE >>
      res_tac)
  >- (drule_all_then strip_assume_tac terms_of_frag_uninst_combE >>
      res_tac)
  >- (drule_all_then strip_assume_tac terms_of_frag_uninst_AbsE >>
      res_tac)
QED

Theorem TYPE_SUBSTf_eq_TYPE_SUBST:
  !ty sigma.
  TYPE_SUBSTf sigma ty =
  TYPE_SUBST (MAP (λx. (sigma x, Tyvar x)) (tyvars ty)) ty
Proof
  ho_match_mp_tac type_ind >>
  rw[tyvars_def,REV_ASSOCD_def,MAP_EQ_f] >>
  fs[EVERY_MEM] >>
  rw[TYPE_SUBST_tyvars] >>
  rw[REV_ASSOCD_ALOOKUP,MAP_MAP_o,o_DEF] >>
  ntac 2 TOP_CASE_TAC >>
  fs[ALOOKUP_SOME_EQ,MAP_EQ_APPEND] >>
  rveq >> fs[MAP_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
  rveq >> fs[] >>
  qpat_x_assum `MEM _ l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  rveq >>
  fs[ALOOKUP_NONE] >>
  fs[MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
  fs[MEM_FOLDR_LIST_UNION,GSYM IMP_DISJ_THM,DISJ_IMP_THM,FORALL_AND_THM]
QED

Theorem ALOOKUP_Tyvar:
  ALOOKUP (MAP (λx. (Tyvar x,f x)) l) (Tyvar x) =
  ALOOKUP (MAP (λx. (x,f x)) l) x
Proof
  Induct_on `l` >> rw[]
QED

Theorem TYPE_SUBSTf_eq_TYPE_SUBSTf:
  !ty sigma sigma'. (TYPE_SUBSTf sigma ty = TYPE_SUBSTf sigma' ty) <=>
  (!x. MEM x (tyvars ty) ==> sigma x = sigma' x)
Proof
  simp[EQ_IMP_THM,FORALL_AND_THM] >>
  conj_tac >>
  ho_match_mp_tac type_ind >>
  rw[tyvars_def,MAP_EQ_f,EVERY_MEM,MEM_FOLDR_LIST_UNION,PULL_EXISTS] >>
  res_tac
QED

Theorem ALOOKUP_MAPf:
  ALOOKUP (MAP (λx. (x,f x)) l) y =
  if MEM y l then SOME(f y) else NONE
Proof
  Induct_on `l` >> rw[] >> fs[]
QED

Theorem tyvars_TYPE_SUBSTf_eq_NIL:
  tyvars (TYPE_SUBSTf sigma ty) = []
  <=>
  !x. MEM x (tyvars ty) ==> tyvars (sigma x) = []
Proof
  `tyvars (TYPE_SUBSTf sigma ty) = [] <=> set(tyvars (TYPE_SUBSTf sigma ty)) = {}`
    by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  PURE_REWRITE_TAC[TYPE_SUBSTf_eq_TYPE_SUBST,tyvars_TYPE_SUBST] >>
  rw[EQ_IMP_THM,FUN_EQ_THM,GSYM IMP_DISJ_THM] >>
  res_tac >>
  fs[REV_ASSOCD_ALOOKUP,MAP_MAP_o,o_DEF,ALOOKUP_Tyvar,ALOOKUP_MAPf] >>
  last_x_assum kall_tac >>
  rfs[] >>
  Cases_on `tyvars(sigma x)` >> fs[FORALL_AND_THM]
QED

Theorem ext_type_frag_builtins_nonbuiltin:
  ty ∈ nonbuiltin_types ==>
  ext_type_frag_builtins σ ty = σ ty
Proof
  simp[Once ext_type_frag_builtins_def] >>
  every_case_tac >>
  simp[nonbuiltin_types_def,is_builtin_type_def]
QED

Theorem termsem_subst:
  !σ γ v sigma sigma' tm.
  welltyped tm /\
  (!x. MEM x (tvars tm) ==> sigma x = sigma' x) ==>
  termsem σ γ v sigma tm = termsem σ γ v sigma' tm
Proof
  Induct_on `tm` >> rw[termsem_def,tvars_def,DISJ_IMP_THM,FORALL_AND_THM]
  >- fs[GSYM TYPE_SUBSTf_eq_TYPE_SUBSTf]
  >- (res_tac >> fs[])
  >- (fs[tvars_def] >> fs[GSYM TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
      res_tac >>
      fs[termsem_def] >>
      `∀x. MEM x (tyvars(typeof tm')) ⇒ sigma x = sigma' x`
        by(rw[] >>
           fs[welltyped_def] >>
           drule tyvars_typeof_subset_tvars >>
           rw[SUBSET_DEF] >>
           imp_res_tac WELLTYPED_LEMMA >>
           rveq >> res_tac >> res_tac) >>
      fs[GSYM TYPE_SUBSTf_eq_TYPE_SUBSTf])
QED

Theorem orth_ctxt_ALOOKUP_eqs:
  MEM (s,t) eqs /\
  orth_ctxt (ctxt1 ++ ConstSpec b eqs prop::ctxt2) ==>
  ALOOKUP (MAP (λx. (Var (FST x) (typeof (SND x)), f x)) eqs) (Var s (typeof t)) =
  SOME (f (s,t))
Proof
  rw[orth_ctxt_def] >>
  last_x_assum(qspecl_then [`b`,`b`,`eqs`,`eqs`,`prop`,`prop`] mp_tac) >>
  rw[] >>
  first_x_assum (drule_then assume_tac) >>
  Cases_on `ALOOKUP
              (MAP (λx. (Var (FST x) (typeof (SND x)),f x)) eqs)
              (Var s (typeof t))` >-
    (fs[ALOOKUP_NONE,MEM_MAP] >> metis_tac[term_11,FST,SND]) >>
  dxrule_then assume_tac ALOOKUP_MEM >>
  fs[MEM_MAP,PULL_EXISTS] >>
  rveq >>
  rename1 `MEM c1 eqs` >> Cases_on `c1` >>
  first_x_assum drule >> simp[] >>
  disch_then (mp_tac o CONTRAPOS) >>
  reverse impl_tac >- simp[] >>
  simp[orth_ci_def,orth_ty_def]
QED

Theorem orth_ctxt_FILTER_ctxt:
  MEM (s,t) eqs /\
  MEM (ConstSpec b eqs prop) ctxt /\
  orth_ctxt ctxt ==>
  ?l1 l2. FILTER (λy. [] ≠ y) (MAP (defn_matches s (TYPE_SUBSTf sigma (typeof t))) ctxt) =
          ((s,t)::l1)::l2
Proof
  rw[orth_ctxt_def] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  rveq >>
  simp[FILTER_APPEND,defn_matches_def] >>
  qpat_x_assum `MEM _ eqs` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  rveq >> fs[FILTER_APPEND] >>
  Q.SUBGOAL_THEN `is_instance (typeof t) (TYPE_SUBSTf sigma (typeof t))` assume_tac >-
    metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `FILTER a1 a2` >>
  Cases_on `FILTER a1 a2` >>
  fs[Abbr `a1`,Abbr `a2`] >-
    (qmatch_goalsub_abbrev_tac `FILTER a1 a2` >>
     Cases_on `FILTER a1 a2` >> fs[Abbr `a1`, Abbr `a2`] >>
     fs[FILTER_EQ_CONS] >> rveq >> fs[] >>
     pairarg_tac >> fs[] >>
     rveq >> fs[] >>
     fs[RIGHT_AND_OVER_OR,LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
     rpt(PRED_ASSUM is_forall kall_tac) >>
     fs[orth_ci_def,orth_ty_def] >> metis_tac[]) >>
  fs[FILTER_EQ_CONS] >> rveq >> fs[] >>
  fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
  fs[defn_matches_def] >> TOP_CASE_TAC >> fs[] >>
  qmatch_asmsub_abbrev_tac `[] <> FILTER a1 a2` >>
  Cases_on `FILTER a1 a2` >> fs[Abbr`a1`,Abbr`a2`] >>
  fs[FILTER_EQ_CONS] >> rveq >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >> fs[] >>
  fs[RIGHT_AND_OVER_OR,LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM] >>
  rpt(PRED_ASSUM is_forall kall_tac) >>
  fs[orth_ci_def,orth_ty_def] >> metis_tac[]
QED

Definition admissible_axiom_def:
 admissible_axiom ^mem ind upd ctxt1 =
   ((upd::ctxt1 = mk_eta_ctxt ctxt1) \/
    (?ctxt2. upd::ctxt1 = mk_select_ctxt(mk_bool_ctxt ctxt2)) \/
    (?ctxt2. (upd::ctxt1 = mk_infinity_ctxt(mk_select_ctxt(mk_bool_ctxt ctxt2))) /\
     is_infinite ^mem ind))
End

Theorem defn_matches_ConstDef:
  a <> b ==>
  defn_matches a ty (ConstDef b def) = []
Proof
  rw[defn_matches_def]
QED

Theorem defn_matches_NewAxiom:
  defn_matches a ty (NewAxiom p) = []
Proof
  rw[defn_matches_def]
QED

Theorem defn_matches_NewConst:
  defn_matches a ty (NewConst c ty') = []
Proof
  rw[defn_matches_def]
QED

Theorem NewConst_no_abs_rep:
  ctxt extends [] /\
  MEM (NewConst c ty) ctxt ==>
  mapPartial (abs_or_rep_matches c ty') ctxt = []
Proof
  rw[MEM_SPLIT] >>
  imp_res_tac extends_NIL_DISJOINT >>
  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
  imp_res_tac extends_NIL_DISJOINT >>
  fs[mllistTheory.mapPartial_thm,abs_or_rep_matches_def,abs_matches_def,rep_matches_def,FILTER_APPEND] >>
  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,abs_or_rep_matches_def] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  rveq >> fs[] >>
  rename1 `abs_matches _ _ upd` >> Cases_on `upd` >> fs[abs_matches_def,rep_matches_def]
QED

Theorem NewType_no_type_match:
  ctxt extends [] /\
  MEM (NewType name arity) ctxt ==>
  mapPartial (type_matches (Tyapp name tyargs)) ctxt = []
Proof
  rw[MEM_SPLIT] >>
  imp_res_tac extends_NIL_DISJOINT >>
  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
  imp_res_tac extends_NIL_DISJOINT >>
  fs[mllistTheory.mapPartial_thm,type_matches_def,FILTER_APPEND] >>
  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,type_matches_def] >>
  pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
  rveq >> fs[] >>
  TOP_CASE_TAC >> fs[type_matches_def]
QED

Theorem exists_valuation:
  is_set_theory ^mem ∧
  is_frag_interpretation (total_fragment sig) δ γ ∧
  (∀ty. tyvars (sigma ty) = []) ∧
  (∀ty. type_ok (tysof sig) (sigma ty))
  ==>
  ?v. valuates_frag (total_fragment sig) δ (v: mlstring # type -> 'U) sigma
Proof
  rw[total_fragment_def,is_frag_interpretation_def,valuates_frag_def,
     is_type_frag_interpretation_def] >>
  simp[PFORALL_THM,ELIM_UNCURRY] >>
  simp[GSYM SKOLEM_THM] >>
  rw[RIGHT_EXISTS_IMP_THM] >>
  drule_then match_mp_tac inhabited_ext >>
  fs[types_of_frag_def] >>
  goal_assum drule >>
  rw[]
QED

Theorem extends_init_ind:
  ctxt1 extends ctxt2 /\
  P ctxt2 /\
  (!upd ctxt1.
    ctxt1 extends ctxt2 /\ upd updates ctxt1 /\
    P ctxt1 ==> P(upd::ctxt1)) ==>
  P ctxt1
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac extends_appends >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `_ extends _` mp_tac >>
  rename1 `ctxt1 ++ ctxt2` >>
  Induct_on `ctxt1` >- rw[] >>
  rpt strip_tac >> fs[] >>
  qpat_x_assum `_ extends _` (strip_assume_tac o REWRITE_RULE[extends_def,Once RTC_CASES1]) >>
  fs[] >> rveq >> fs[GSYM extends_def]
QED

Definition axioms_admissible_def:
 axioms_admissible mem ind ctxt =
 (!ctxt1 p ctxt2. ctxt = ctxt1 ++ NewAxiom p::ctxt2 ==> admissible_axiom mem ind (NewAxiom p) ctxt2)
End

Theorem axioms_admissibleE:
 axioms_admissible mem ind (ctxt1 ++ NewAxiom p::ctxt2) ==> admissible_axiom mem ind (NewAxiom p) ctxt2
Proof
  metis_tac[axioms_admissible_def]
QED

Theorem min_hol_admissible_axioms:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt
            /\ (!p. ~MEM (NewAxiom p) ctxt)
    ⇒
        axioms_admissible ^mem One ctxt
Proof
  rpt strip_tac >>
  rw[axioms_admissible_def] >> fs[FORALL_AND_THM]
QED

Theorem mk_eta_ctxt_extends_init:
  mk_eta_ctxt init_ctxt extends init_ctxt
Proof
  match_mp_tac eta_extends >> rw[is_std_sig_init]
QED

Theorem eta_interpretation_admissible_axioms:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends mk_eta_ctxt(init_ctxt)
            /\ (!p. MEM (NewAxiom p) ctxt ==> MEM (NewAxiom p) (mk_eta_ctxt(init_ctxt)))
    ⇒
        axioms_admissible ^mem One ctxt
Proof
  rw[axioms_admissible_def] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM,mk_eta_ctxt_def,admissible_axiom_def,init_ctxt_def]
QED

Definition finite_hol_ctxt_def:
 finite_hol_ctxt = mk_select_ctxt(mk_bool_ctxt(mk_eta_ctxt(init_ctxt)))
End

Theorem finite_hol_ctxt_extends_init:
  finite_hol_ctxt extends init_ctxt
Proof
  rw[finite_hol_ctxt_def] >>
  match_mp_tac extends_trans >>
  qexists_tac `mk_bool_ctxt (mk_eta_ctxt init_ctxt)` >>
  conj_tac >-
    (match_mp_tac select_extends >> EVAL_TAC) >>
  match_mp_tac extends_trans >>
  qexists_tac `mk_eta_ctxt init_ctxt` >>
  simp[mk_eta_ctxt_extends_init] >>
  match_mp_tac holBoolSyntaxTheory.bool_extends >>
  EVAL_TAC >>
  rw[term_ok_def,type_ok_def,FLOOKUP_UPDATE] >-
    (Q.REFINE_EXISTS_TAC `[(_,Tyvar _)]` >> rw[REV_ASSOCD_def] >> metis_tac[]) >>
  rpt(rw[Once has_type_cases])
QED

Theorem finite_hol_admissible_axioms:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends finite_hol_ctxt
            /\ (!p. MEM (NewAxiom p) (TAKE (LENGTH ctxt - LENGTH finite_hol_ctxt) ctxt) ==> F)
    ⇒
        axioms_admissible ^mem One ctxt
Proof
  rw[axioms_admissible_def] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM,mk_eta_ctxt_def,admissible_axiom_def,init_ctxt_def,
     mk_select_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,finite_hol_ctxt_def] >>
  fs[TAKE_APPEND] >>
  imp_res_tac extends_appends >> rveq >> fs[] >>
  fs[APPEND_EQ_APPEND_MID] >> fs[] >> rveq >>
  fs[TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
  fs[FORALL_AND_THM] >>
  fs[Once(APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV))] >> rveq >> fs[] >>
  ntac 2 (pop_assum mp_tac) >>
  rpt(pop_assum kall_tac) >>
  rw[APPEND_EQ_CONS] >>
  fs[]
QED

Definition hol_ctxt_def:
 hol_ctxt = mk_infinity_ctxt(finite_hol_ctxt)
End

Theorem hol_ctxt_extends_init:
  hol_ctxt extends init_ctxt
Proof
  rw[hol_ctxt_def] >>
  match_mp_tac extends_trans >>
  qexists_tac `finite_hol_ctxt` >>
  conj_tac >-
    (match_mp_tac infinity_extends >>
     conj_tac >-
       (match_mp_tac(MP_CANON extends_theory_ok) >>
        metis_tac[finite_hol_ctxt_extends_init,init_theory_ok]) >>
     EVAL_TAC) >>
  ACCEPT_TAC finite_hol_ctxt_extends_init
QED

Theorem hol_admissible_axioms:
  is_set_theory ^mem /\ is_infinite ^mem ind ⇒
    ∀ctxt. ctxt extends hol_ctxt
            /\ (!p. MEM (NewAxiom p) (TAKE (LENGTH ctxt - LENGTH hol_ctxt) ctxt) ==> F)
    ⇒
        axioms_admissible ^mem ind ctxt
Proof
  rw[axioms_admissible_def] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM,mk_eta_ctxt_def,admissible_axiom_def,init_ctxt_def,
     mk_infinity_ctxt_def,hol_ctxt_def,
     mk_select_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,finite_hol_ctxt_def] >>
  fs[TAKE_APPEND] >>
  imp_res_tac extends_appends >> rveq >> fs[] >>
  fs[APPEND_EQ_APPEND_MID] >> fs[] >> rveq >>
  fs[TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
  fs[FORALL_AND_THM] >>
  fs[Once(APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV))] >> rveq >> fs[] >>
  ntac 2 (pop_assum mp_tac) >>
  rpt(pop_assum kall_tac) >>
  rw[APPEND_EQ_CONS] >>
  fs[]
QED

