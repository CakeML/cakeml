(*
  Proves soundness of the context extension rules: any model of a context can
  be extended to a model of the context obtained by applying one of the
  non-axiomatic context updates.
*)
open preamble mlstringTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory holAxiomsSyntaxTheory holBoolTheory

val _ = new_theory"holExtension"

val _ = temp_delsimps ["NORMEQ_CONV"]
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

val type_matches_def = Define `
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
  `

val defn_matches_def = Define `
  defn_matches name ty defn =
  case defn of
  | ConstSpec ov eqs prop =>
      FILTER (λ(name0,trm). name = name0 /\ is_instance (typeof trm) ty) eqs
  | _ => []
  `

val rep_matches_def = Define `
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
  `

val abs_matches_def = Define `
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
  `

val abs_or_rep_matches_def = Define `
  abs_or_rep_matches name ty defn =
  case abs_matches name ty defn of
    NONE =>
    (case rep_matches name ty defn of
       NONE => NONE
     | SOME(rep,abs_type,rep_type) =>
       SOME(F,rep,abs_type,rep_type))
  | SOME(abs,abs_type,rep_type) =>
    SOME(T,abs,abs_type,rep_type)
  `

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
      fs[quantHeuristicsTheory.LIST_LENGTH_2] >>
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
      fs[quantHeuristicsTheory.LIST_LENGTH_2] >>
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

(* Hiding this under a definition so it won't obstruct drules later *)
Definition extends_init_def:
  extends_init ctxt = (ctxt extends init_ctxt)
End

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

val select_ax = EVAL ``HD(mk_select_ctxt ARB)`` |> concl |> rhs

val select_ty = EVAL ``HD(TL(mk_select_ctxt ARB))`` |> concl |> rhs |> rand

val infinity_ax = EVAL ``HD(mk_infinity_ctxt ARB)`` |> concl |> rhs

val onto_conext = EVAL ``conexts_of_upd(EL 2 (mk_infinity_ctxt ARB))`` |> concl |> rhs

val one_one_conext = EVAL ``conexts_of_upd(EL 3 (mk_infinity_ctxt ARB))`` |> concl |> rhs

val type_interpretation_of_def =
    tDefine "type_interpretation_of" `
  (type_interpretation_of0
   ^mem ind ctxt ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~(orth_ctxt ctxt /\ extends_init ctxt) then
     One:'U
   else
     case mapPartial (type_matches ty) ctxt of
     | [] =>
       if ty = Tyapp (strlit "ind") [] then
         ind
       else
         One
     | [(pred,ty',tvs)] =>
       (case instance_subst [(ty, (Tyapp ty' (MAP Tyvar tvs)))] [] [] of
         | SOME(sigma,e) =>
            let pty = domain(typeof pred);
                consts = consts_of_term pred ∩ nonbuiltin_constinsts;
                inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
                sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
                γ = (λ(c,ty).
                      if (c,ty) ∈ inst_consts then
                        term_interpretation_of0 ^mem ind ctxt c ty
                      else One);
                δ = (λty.
                       if MEM ty (allTypes' (TYPE_SUBST sigma pty)) then
                         type_interpretation_of0 ^mem ind ctxt ty
                       else One);
                atys = MAP (TYPE_SUBST sigma) (allTypes pred);
                δ' = (λty.
                       if MEM ty(FLAT (MAP allTypes' atys)) then
                         type_interpretation_of0 ^mem ind ctxt ty
                       else One);
                tst = termsem (ext_type_frag_builtins δ')
                              (ext_term_frag_builtins
                                (ext_type_frag_builtins δ')
                                γ)
                              empty_valuation
                              sigma'
                              pred
            in
              if ?tm.
                  tm ⋲
                  (ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)) then
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)
              else
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
         | NONE => One:'U)
     | _ => One:'U
  ) /\
  (term_interpretation_of0
   ^mem ind ctxt (name:mlstring) ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~(orth_ctxt ctxt /\ extends_init ctxt) then
     One:'U
   else
     case FILTER ($<> []) (MAP (defn_matches name ty) ctxt) of
       [] =>
       (case mapPartial (abs_or_rep_matches name ty) ctxt of
        | [(is_abs,name0,abs_type,rep_type)] =>
          (let cty = if is_abs then Fun rep_type abs_type else Fun abs_type rep_type
           in
             case instance_subst [(ty, cty)] [] [] of
             | SOME(sigma,e) =>
               let
                 δ = (λty.
                         if MEM ty (allTypes' (TYPE_SUBST sigma cty)) then
                           type_interpretation_of0 ^mem ind ctxt ty
                         else One);
                 sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
               in
                 if is_abs then
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (λv. if v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type) then
                                   v
                                 else
                                   @v. v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                 else
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            I
             | NONE => One (* cannot happen *))
        | _ =>
          (if term_ok (sigof ctxt) (Const name ty) then
             let δ = (λty'.
                         if MEM ty' (allTypes' ty) then
                           type_interpretation_of0 ^mem ind ctxt ty'
                         else One)
             in
               if name = strlit "@" /\ MEM ^select_ax ctxt /\
                  FLOOKUP (tmsof ctxt) (strlit "==>") = SOME (Fun Bool (Fun Bool Bool)) /\
                  FLOOKUP (tmsof ctxt) (strlit "@") = SOME(^select_ty)
                then
                 Abstract (ext_type_frag_builtins δ (domain ty))
                          (ext_type_frag_builtins δ (codomain ty))
                          (λp.
                            case some x. x <: (ext_type_frag_builtins δ (codomain ty)) ∧
                                         p ' x = True of
                              NONE => (@x. x <: ext_type_frag_builtins δ (codomain ty))
                            | SOME v => v
                          )
               else
                 @v. v <: ext_type_frag_builtins δ ty
           else One
          )
       )
     | l =>
       let (name0,trm0) = HD(HD l)
       in
         case instance_subst [(ty, typeof trm0)] [] [] of
         | SOME(sigma,e) =>
           let
             pty = domain(typeof trm0);
             consts = consts_of_term trm0 ∩ nonbuiltin_constinsts;
             inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
             sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
             γ = (λ(c,ty).
                   if (c,ty) ∈ inst_consts then
                     term_interpretation_of0 ^mem ind ctxt c ty
                   else One);
             atys = MAP (TYPE_SUBST sigma) (allTypes trm0);
             δ = (λty.
                    if MEM ty(FLAT (MAP allTypes' atys)) then
                      type_interpretation_of0 ^mem ind ctxt ty
                    else One)
           in
             termsem (ext_type_frag_builtins δ)
                       (ext_term_frag_builtins
                         (ext_type_frag_builtins δ)
                         γ)
                       empty_valuation
                       sigma'
                       trm0
         | NONE => One (* cannot happen *)
  )`
  (wf_rel_tac `subst_clos_term_rel`
   >-
     (rw[wellorderTheory.WF_IND,subst_clos_term_rel_def,WF_TC_EQN] >>
      reverse(Cases_on `x`) >-
        (rename1 `INR args` >> PairCases_on `args` >>
         rename1 `(mem,ind,ctxt,c,ty)` >>
         reverse(Cases_on `terminating(subst_clos(dependency ctxt))`) >-
           (first_x_assum match_mp_tac >> simp[]) >>
         drule terminating_IMP_wellfounded_INV >>
         strip_tac >> dxrule WF_TC >>
         simp[wellorderTheory.WF_IND] >>
         disch_then(qspec_then `λx. case x of INL ty => P(INL(mem,ind,ctxt,ty))
                                            | INR(Const c ty) => P(INR(mem,ind,ctxt,c,ty))
                                            | _ => T` mp_tac) >>
         simp[] >>
         impl_tac >-
           (Cases >> rw[] >-
              (first_x_assum match_mp_tac >>
               Cases >> simp[] >>
               rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
               first_x_assum drule >> simp[]) >>
            TOP_CASE_TAC >> rw[] >>
            first_x_assum match_mp_tac >> Cases >> simp[] >>
            rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
            first_x_assum drule >> simp[]) >>
         disch_then(qspec_then `INR(Const c ty)` mp_tac) >>
         simp[]) >>
      rename1 `INL args` >> PairCases_on `args` >>
      rename1 `(mem,ind,ctxt,ty)` >>
      reverse(Cases_on `terminating(subst_clos(dependency ctxt))`) >-
        (first_x_assum match_mp_tac >> simp[]) >>
      drule terminating_IMP_wellfounded_INV >>
      strip_tac >> dxrule WF_TC >>
      simp[wellorderTheory.WF_IND] >>
      disch_then(qspec_then `λx. case x of INL ty => P(INL(mem,ind,ctxt,ty))
                                         | INR(Const c ty) => P(INR(mem,ind,ctxt,c,ty))
                                         | _ => T` mp_tac) >>
      simp[] >>
      impl_tac >-
        (Cases >> rw[] >-
           (first_x_assum match_mp_tac >>
            Cases >> simp[] >>
            rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
            first_x_assum drule >> simp[]) >>
         TOP_CASE_TAC >> rw[] >>
         first_x_assum match_mp_tac >> Cases >> simp[] >>
         rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF,GSYM inv_TC] >>
         first_x_assum drule >> simp[]) >>
      disch_then(qspec_then `INL ty` mp_tac) >>
      simp[]) >>
    rpt strip_tac >-
      (fs[subst_clos_term_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `mapPartial _ _ = [(pred,name,tvs)]` >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       rename1 `MEM ty1 (allTypes pred)` >>
       rename1 `MEM ty2 (allTypes' _)` >>
       Cases_on `ty2 = TYPE_SUBST sigma ty1` >-
         (match_mp_tac TC_SUBSET >>
          simp[subst_clos_def] >>
          CONV_TAC(RESORT_EXISTS_CONV rev) >>
          qexists_tac `sigma` >>
          qexists_tac `ty1` >>
          qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
          simp[] >>
          match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
          fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
          rveq >>
          fs[IS_SOME_EXISTS] >>
          fs[type_matches_def,CaseEq"update"] >>
          rveq >> fs[] >>
          reverse FULL_CASE_TAC >- metis_tac[] >>
          pop_assum kall_tac >>
          fs[] >>
          simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
          rveq >> simp[]) >>
       fs[extends_init_def] >>
       imp_res_tac allTypes'_subst_clos_dependency >>
       match_mp_tac(CONJUNCT2 (SPEC_ALL TC_RULES)) >>
       HINT_EXISTS_TAC >> simp[] >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       CONV_TAC(RESORT_EXISTS_CONV rev) >>
       qexists_tac `sigma` >>
       qexists_tac `ty1` >>
       qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
       simp[] >>
       match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[type_matches_def,CaseEq"update"] >>
       rveq >> fs[] >>
       reverse FULL_CASE_TAC >- metis_tac[] >>
       pop_assum kall_tac >>
       fs[] >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       rveq >> simp[]) >-
      (fs[subst_clos_term_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `mapPartial _ _ = [(pred,name,tvs)]` >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       drule MEM_allTypes'_TYPE_SUBST_decompose >> strip_tac >>
       `MEM ty1 (allTypes pred)` by
         (fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
          rveq >>
          fs[IS_SOME_EXISTS] >>
          fs[type_matches_def,CaseEq"update"] >>
          rveq >> fs[] >>
          reverse FULL_CASE_TAC >- metis_tac[] >>
          pop_assum kall_tac >>
          fs[] >>
          rveq >>
          fs[extends_init_def] >>
          FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
          drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          dxrule extends_APPEND_NIL >> rw[] >>
          dxrule extends_NIL_CONS_updates >>
          rw[updates_cases] >>
          drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          rw[] >> dxrule extends_NIL_APPEND_extends >>
          strip_tac >>
          dxrule_then drule extends_proves >> strip_tac >>
          drule proves_term_ok >>
          drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
          PURE_REWRITE_TAC[APPEND_ASSOC] >>
          simp[] >>
          rw[term_ok_clauses] >>
          drule_then match_mp_tac (allTypes_typeof |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
          fs[allTypes'_defn]) >>
       Cases_on `ty'' = TYPE_SUBST sigma ty1` >-
         (match_mp_tac TC_SUBSET >>
          simp[subst_clos_def] >>
          CONV_TAC(RESORT_EXISTS_CONV rev) >>
          qexists_tac `sigma` >>
          qexists_tac `ty1` >>
          qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
          simp[] >>
          match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
          fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
          rveq >>
          fs[IS_SOME_EXISTS] >>
          fs[type_matches_def,CaseEq"update"] >>
          rveq >> fs[] >>
          reverse FULL_CASE_TAC >- metis_tac[] >>
          pop_assum kall_tac >>
          fs[] >>
          simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
          rveq >> simp[]) >>
       fs[extends_init_def] >>
       imp_res_tac allTypes'_subst_clos_dependency >>
       match_mp_tac(CONJUNCT2 (SPEC_ALL TC_RULES)) >>
       HINT_EXISTS_TAC >> simp[] >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       CONV_TAC(RESORT_EXISTS_CONV rev) >>
       qexists_tac `sigma` >>
       qexists_tac `ty1` >>
       qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
       simp[] >>
       match_mp_tac (List.nth(dependency_rules |> CONJUNCTS, 2)) >>
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[type_matches_def,CaseEq"update"] >>
       rveq >> fs[] >>
       reverse FULL_CASE_TAC >- metis_tac[] >>
       pop_assum kall_tac >>
       fs[] >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       rveq >> simp[]) >-
      (fs[subst_clos_term_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `mapPartial _ _ = [(pred,name,tvs)]` >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       `term_ok (sigof ctxt) pred`
         by(fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
            rveq >>
            fs[IS_SOME_EXISTS] >>
            fs[type_matches_def,CaseEq"update"] >>
            rveq >> fs[] >>
            reverse FULL_CASE_TAC >- metis_tac[] >>
            pop_assum kall_tac >>
            fs[] >>
            rveq >>
            fs[extends_init_def] >>
            FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
            drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            dxrule extends_APPEND_NIL >> rw[] >>
            dxrule extends_NIL_CONS_updates >>
            rw[updates_cases] >>
            drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            rw[] >> dxrule extends_NIL_APPEND_extends >>
            strip_tac >>
            dxrule_then drule extends_proves >> strip_tac >>
            drule proves_term_ok >>
            drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            PURE_REWRITE_TAC[APPEND_ASSOC] >>
            simp[] >>
            rw[term_ok_clauses]) >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       qexists_tac `Tyapp name (MAP Tyvar tvs)` >>
       qexists_tac `Const c ty'` >>
       qexists_tac `sigma` >>
       conj_tac >- simp[] >>
       conj_tac >- simp[INST_def,INST_CORE_def] >>
       match_mp_tac(List.nth(CONJUNCTS dependency_rules,3)) >>
       qexists_tac `name` >>
       qexists_tac `pred` >>
       imp_res_tac consts_of_term_nonbuiltin_allCInsts >>
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[type_matches_def,CaseEq"update"] >>
       rveq >> fs[] >>
       reverse FULL_CASE_TAC >- metis_tac[] >>
       pop_assum kall_tac >>
       fs[] >>
       rveq >>
       metis_tac[]) >-
      (fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       fs[subst_clos_term_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       rename1 `MEM ty0 (allTypes _)` >>
       rename1 `MEM ty1 (allTypes' _)` >>
       fs[FILTER_EQ_CONS,MAP_EQ_APPEND] >>
       rveq >> fs[] >>
       fs[defn_matches_def] >> FULL_CASE_TAC >> fs[] >>
       fs[FILTER_EQ_NIL,EXISTS_MEM] >>
       pairarg_tac >> rveq >> fs[] >> rveq >>
       `(name0,trm0) = (name,trm)`
         by(fs[orth_ctxt_def] >>
            first_x_assum(qspecl_then [`b`,`b`,`l`,`l`,`t`,`t`,`name0`,`name`,`trm0`,`trm`] mp_tac) >>
            simp[] >>
            qmatch_goalsub_abbrev_tac `FILTER af al` >>
            Cases_on `FILTER af al` >>
            fs[Abbr `af`,Abbr `al`,FILTER_EQ_NIL,FILTER_EQ_CONS,EVERY_MEM] >-
              (res_tac >> fs[] >> metis_tac[]) >>
            rveq >> fs[] >> fs[orth_ty_def,orth_ci_def] >> metis_tac[]) >>
       fs[] >> rveq >>
       `welltyped trm`
         by(fs[extends_init_def] >>
          FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
          drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          dxrule extends_APPEND_NIL >> rw[] >>
          dxrule extends_NIL_CONS_updates >>
          rw[updates_cases] >>
          drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
          rw[] >> dxrule extends_NIL_APPEND_extends >>
          strip_tac >>
          dxrule_then drule extends_proves >> strip_tac >>
          drule proves_term_ok >>
          drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
          PURE_REWRITE_TAC[APPEND_ASSOC] >>
          simp[] >>
          fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
          rpt strip_tac >>
          first_x_assum dxrule >>
          simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL]) >>
       Cases_on `ty1 = TYPE_SUBST sigma ty0` >-
         (match_mp_tac TC_SUBSET >>
          simp[subst_clos_def] >>
          qexists_tac `ty0` >>
          qexists_tac `Const name (typeof trm)` >>
          qexists_tac `sigma` >>
          simp[INST_def,INST_CORE_def] >>
          qmatch_goalsub_abbrev_tac `Const name aty` >>
          match_mp_tac (List.nth(CONJUNCTS dependency_rules,1)) >>
          simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
          qunabbrev_tac `aty` >> metis_tac[welltyped_def,WELLTYPED_LEMMA]) >>
       match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
       qexists_tac `INL(TYPE_SUBST sigma ty0)` >>
       reverse conj_tac >-
         (match_mp_tac allTypes'_subst_clos_dependency >> fs[extends_init_def]) >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       qexists_tac `ty0` >>
       qexists_tac `Const name (typeof trm)` >>
       qexists_tac `sigma` >>
       simp[INST_def,INST_CORE_def] >>
       qmatch_goalsub_abbrev_tac `Const name aty` >>
       match_mp_tac (List.nth(CONJUNCTS dependency_rules,1)) >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       qunabbrev_tac `aty` >> metis_tac[welltyped_def,WELLTYPED_LEMMA]) >-
      (
       fs[subst_clos_term_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       rename1 `(c,ty0)` >>
       fs[FILTER_EQ_CONS,MAP_EQ_APPEND] >>
       rveq >> fs[] >>
       fs[defn_matches_def] >> FULL_CASE_TAC >> fs[] >>
       fs[FILTER_EQ_NIL,EXISTS_MEM] >>
       pairarg_tac >> rveq >> fs[] >> rveq >>
       `(name0,trm0) = (name,trm)`
         by(fs[orth_ctxt_def] >>
            first_x_assum(qspecl_then [`b`,`b`,`l`,`l`,`t`,`t`,`name0`,`name`,`trm0`,`trm`] mp_tac) >>
            simp[] >>
            qmatch_goalsub_abbrev_tac `FILTER af al` >>
            Cases_on `FILTER af al` >>
            fs[Abbr `af`,Abbr `al`,FILTER_EQ_NIL,FILTER_EQ_CONS,EVERY_MEM] >-
              (res_tac >> fs[] >> metis_tac[]) >>
            rveq >> fs[] >> fs[orth_ty_def,orth_ci_def] >> metis_tac[]) >>
       fs[] >> rveq >>
       match_mp_tac TC_SUBSET >>
       simp[subst_clos_def] >>
       qexists_tac `Const name (typeof trm)` >>
       qexists_tac `Const c (ty0)` >>
       qexists_tac `sigma` >>
       simp[INST_def,INST_CORE_def] >>
       qmatch_goalsub_abbrev_tac `Const name ty1` >>
       qmatch_goalsub_abbrev_tac `Const c ty2` >>
       qmatch_asmsub_abbrev_tac `extends_init ctxt` >>
       `term_ok (sigof ctxt) trm`
         by(fs[Abbr`ctxt`,extends_init_def] >>
            FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
            drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            dxrule extends_APPEND_NIL >> rw[] >>
            dxrule extends_NIL_CONS_updates >>
            rw[updates_cases] >>
            drule_then (mp_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            rw[] >> dxrule extends_NIL_APPEND_extends >>
            strip_tac >>
            dxrule_then drule extends_proves >> strip_tac >>
            drule proves_term_ok >>
            drule_then(mp_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            PURE_REWRITE_TAC[APPEND_ASSOC] >>
            simp[] >>
            rw[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
            first_x_assum drule >> simp[term_ok_clauses]) >>
       qunabbrev_tac `ctxt` >>
       imp_res_tac consts_of_term_nonbuiltin_allCInsts >>
       match_mp_tac(CONJUNCT1 dependency_rules) >>
       MAP_EVERY qunabbrev_tac [`ty1`,`ty2`] >>
       simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
       metis_tac[term_ok_welltyped,WELLTYPED_LEMMA,welltyped_def]) >-
      ((* abs/rep case *)
       simp[subst_clos_term_rel_def] >>
       FULL_CASE_TAC >>
       fs[allTypes'_defn] >>
       drule MEM_allTypes'_TYPE_SUBST_decompose >> strip_tac >>
       imp_res_tac instance_subst_soundness >>
       rename1 `instance_subst _ _ _ = SOME(sigma,r)` >>
       rename1 `[(_,name0,abs_type,rep_type)]` >>
       fs[extends_init_def] >>
       imp_res_tac abs_or_rep_matches_abstype >>
       fs[] >> rveq >>
       qmatch_asmsub_abbrev_tac `MEM ty' (allTypes' aty)` >>
       ((* Same proof for 4 subcases (whether LHS is abs or rep, whether RHS is from abs or rep) *)
        Cases_on `ty' = aty` >>
        qmatch_goalsub_abbrev_tac `INR (Const name absreptype)` >-
          (match_mp_tac TC_SUBSET >>
           simp[subst_clos_def] >>
           qunabbrev_tac `aty` >>
           qmatch_goalsub_abbrev_tac `a1 = _` >>
           assume_tac (Q.REFL `a1:type`) >>
           qunabbrev_tac `a1` >>
           goal_assum dxrule >>
           Q.REFINE_EXISTS_TAC `Const name (Fun _ _)` >>
           simp[INST_def,INST_CORE_def] >>
           assume_tac (Q.REFL `absreptype:type`) >>
           qunabbrev_tac `absreptype` >>
           goal_assum dxrule >>
           qmatch_goalsub_abbrev_tac `INR (Const name absreptype)` >>
           match_mp_tac(List.nth(CONJUNCTS dependency_rules,6)) >>
           fs[Abbr `absreptype`] >>
           fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
           rveq >>
           fs[IS_SOME_EXISTS] >>
           fs[abs_or_rep_matches_def,CaseEq "option",CaseEq "prod",abs_matches_def,
              rep_matches_def,CaseEq "update"] >> rveq >> fs[] >>
           rveq >> fs[] >> rfs[] >>
           FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
           drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           dxrule extends_APPEND_NIL >> rw[] >>
           dxrule extends_NIL_CONS_updates >>
           rw[updates_cases] >>
           fs[] >>
           (reverse FULL_CASE_TAC >- metis_tac[]) >>
           pop_assum kall_tac >>
           fs[] >>
           simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
           rveq >> fs[]) >>
        match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
        qexists_tac `INL aty` >>
        reverse conj_tac >-
          (match_mp_tac allTypes'_subst_clos_dependency >> simp[]) >>
        match_mp_tac TC_SUBSET >>
        simp[subst_clos_def] >>
        qunabbrev_tac `aty` >>
        qmatch_goalsub_abbrev_tac `a1 = _` >>
        assume_tac (Q.REFL `a1:type`) >>
        qunabbrev_tac `a1` >>
        goal_assum dxrule >>
        Q.REFINE_EXISTS_TAC `Const name (Fun _ _)` >>
        simp[INST_def,INST_CORE_def] >>
        assume_tac (Q.REFL `absreptype:type`) >>
        qunabbrev_tac `absreptype` >>
        goal_assum dxrule >>
        qmatch_goalsub_abbrev_tac `INR (Const name absreptype)` >>
        match_mp_tac(List.nth(CONJUNCTS dependency_rules,6)) >>
        fs[Abbr `absreptype`] >>
        fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND] >>
        rveq >>
        fs[IS_SOME_EXISTS] >>
        fs[abs_or_rep_matches_def,CaseEq "option",CaseEq "prod",abs_matches_def,
           rep_matches_def,CaseEq "update"] >> rveq >> fs[] >>
        rveq >> fs[] >> rfs[] >>
        FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
        drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
        dxrule extends_APPEND_NIL >> rw[] >>
        dxrule extends_NIL_CONS_updates >>
        rw[updates_cases] >>
        fs[] >>
        (reverse FULL_CASE_TAC >- metis_tac[]) >>
        pop_assum kall_tac >>
        fs[] >>
        simp[EXISTS_OR_THM,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] >>
        rveq >> fs[])) >-
      ((* abs or rep matches two distinct typedefs (impossible) *)
       fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,FILTER_EQ_NIL,MAP_EQ_APPEND,MAP_EQ_CONS] >>
       rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[FILTER_EQ_CONS,MAP_EQ_APPEND,MAP_EQ_CONS] >> rveq >>
       fs[IS_SOME_EXISTS] >>
       fs[abs_or_rep_matches_def,CaseEq "option",CaseEq "prod",abs_matches_def,
          rep_matches_def,CaseEq "update",CaseEq"bool"] >> rveq >> fs[] >>
       rveq >> fs[] >> rfs[] >>
       (rpt(reverse FULL_CASE_TAC >- metis_tac[])) >>
       rpt(PRED_ASSUM is_exists kall_tac) >>
       fs[] >> rveq >>
       fs[extends_init_def] >>
       qpat_x_assum `_ extends init_ctxt` assume_tac >>
       FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
       drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
       drule extends_APPEND_NIL >>
       rw[] >>
       dxrule extends_NIL_CONS_updates >>
       rw[updates_cases]
      ) >-
      ((* No definition matches (hence constant must have been declared with NewConst) *)
       fs[term_ok_def] >>
       drule ALOOKUP_MEM >>
       rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       rename1 `consts_of_upd upd` >>
       Cases_on `upd` >> fs[] >-
         ((* upd is ConstSpec (impossible) *)
          ntac 2 (pop_assum (mp_tac o REWRITE_RULE[MEM_SPLIT])) >> rw[] >>
          fs[] >> fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
          rpt(pairarg_tac >> rveq >> fs[]) >> rveq >>
          fs[FILTER_APPEND,CaseEq "bool",defn_matches_def] >>
          metis_tac[]) >-
         ((* upd is TypeDefn, const is abs (impossible) *)
          rveq >>
          pop_assum (mp_tac o REWRITE_RULE[MEM_SPLIT]) >> rw[] >>
          fs[] >> fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
          rpt(pairarg_tac >> rveq >> fs[]) >> rveq >>
          fs[mllistTheory.mapPartial_thm,FILTER_APPEND,CaseEq "bool",abs_or_rep_matches_def,
             abs_matches_def,CaseEq"option",CaseEq"prod"] >>
          metis_tac[]) >-
         ((* upd is TypeDefn, const is rep (impossible) *)
          rveq >>
          pop_assum (mp_tac o REWRITE_RULE[MEM_SPLIT]) >> rw[] >>
          fs[] >> fs[MAP_EQ_APPEND] >> rveq >> fs[] >>
          rpt(pairarg_tac >> rveq >> fs[]) >> rveq >>
          fs[mllistTheory.mapPartial_thm,FILTER_APPEND,CaseEq "bool",abs_or_rep_matches_def,
             abs_matches_def,rep_matches_def,CaseEq"option",CaseEq"prod"] >>
          metis_tac[]
         ) >-
         ((* upd is NewConst (possible) *)
          rveq >>
          simp[subst_clos_term_rel_def] >>
          rename1 `MEM ty0 (allTypes' (TYPE_SUBST i ty))` >>
          drule_then strip_assume_tac MEM_allTypes'_TYPE_SUBST_decompose >>
          `(subst_clos (dependency ctxt))⁺ (INR (Const m (TYPE_SUBST i ty)))
                                           (INL (TYPE_SUBST i ty1))`
            by(match_mp_tac TC_SUBSET >>
               simp[subst_clos_def] >>
               qexists_tac `ty1` >>
               qexists_tac `Const m ty` >>
               qexists_tac `i` >>
               simp[INST_def,INST_CORE_def] >>
               match_mp_tac(List.nth(CONJUNCTS dependency_rules,4)) >>
               simp[]) >>
          Cases_on `ty0 = TYPE_SUBST i ty1` >> simp[] >>
          match_mp_tac(CONJUNCT2(SPEC_ALL TC_RULES)) >>
          goal_assum drule >>
          match_mp_tac allTypes'_subst_clos_dependency >>
          fs[extends_init_def]
         )
      )
  )

Overload type_interpretation_of = ``type_interpretation_of0 ^mem``
Overload term_interpretation_of = ``term_interpretation_of0 ^mem``

val type_interpretation_of_ind = fetch "-" "type_interpretation_of_ind";

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
  fs[quantHeuristicsTheory.LIST_LENGTH_2] >> rveq >>
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
  fs[quantHeuristicsTheory.LIST_LENGTH_2,MEM_FLAT,MEM_MAP] >>
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
  fs[quantHeuristicsTheory.LIST_LENGTH_2,MEM_FLAT,MEM_MAP] >>
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
  fs[quantHeuristicsTheory.LIST_LENGTH_2] >> rveq >>
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
 fs[MEM_FLAT,MEM_MAP,quantHeuristicsTheory.LIST_LENGTH_2] >>
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

Theorem interpretation_is_total_frag_interpretation_lemma:
  (∀^mem ind ctxt ty.
      is_set_theory ^mem ⇒
        orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) /\
        ctxt extends [] /\ ctxt extends init_ctxt /\
        ty ∈ ground_types (sigof ctxt) /\ inhabited ind /\
        ty ∈ nonbuiltin_types
    ⇒
        inhabited (type_interpretation_of ind ctxt ty)) /\
  (∀^mem ind ctxt c ty.
     is_set_theory ^mem ⇒
        orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) /\
        ctxt extends [] /\ ctxt extends init_ctxt /\
        (c,ty) ∈ ground_consts (sigof ctxt) /\ inhabited ind /\
        ctxt extends [] /\
        (c,ty) ∈ nonbuiltin_constinsts ⇒
        term_interpretation_of ind ctxt c ty ⋲
        ext_type_frag_builtins (type_interpretation_of ind ctxt) ty
  )
Proof
  ho_match_mp_tac type_interpretation_of_ind >> rw[] >>
  rename1 `elem ⋲ ind`
  >- (simp[Once type_interpretation_of_def] >>
      IF_CASES_TAC >- rw[mem_one] >>
      TOP_CASE_TAC >- metis_tac[mem_one] >>
      reverse TOP_CASE_TAC >- rw[mem_one] >>
      PairCases_on `h` >> rename1 `pred,ty',tvs` >>
      simp[] >>
      drule type_matches_is_instance' >>
      disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
      FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
      rveq >>
      fs[IS_SOME_EXISTS] >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
      drule_then assume_tac instance_subst_soundness >>
      fs[] >>
      rw[mem_sub] >>
      drule_then match_mp_tac inhabited_ext >>
      qexists_tac `set(allTypes' (TYPE_SUBST sigma (domain (typeof pred))))` >>
      conj_tac >- (match_mp_tac builtin_closure_allTypes >- rw[]) >>
      conj_tac >- (rw[SUBSET_DEF] >> imp_res_tac allTypes'_nonbuiltin) >>
      rw[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[] >>
      reverse(rpt conj_tac) >- (imp_res_tac allTypes'_nonbuiltin) >- metis_tac[] >>
      match_mp_tac(TYPE_SUBST_allTypes'_ground_types' |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
      HINT_EXISTS_TAC >> rw[] >>
      fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >> rveq >> rfs[] >>
      fs[type_matches_def,CaseEq "update"] >> rveq >> fs[] >> rveq >>
      FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
      drule extends_APPEND_NIL >> rw[] >>
      dxrule extends_NIL_CONS_updates >>
      rw[updates_cases] >> rveq >> fs[] >>
      imp_res_tac proves_term_ok >>
      fs[] >>
      drule extends_append_MID >>
      impl_tac >- rw[init_ctxt_def] >>
      strip_tac >>
      dxrule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
      fs[term_ok_clauses] >>
      simp[ground_types_def] >>
      reverse conj_tac >-
        (match_mp_tac type_ok_TYPE_SUBST_strong >>
         conj_tac
         >- (match_mp_tac type_ok_extend >>
             imp_res_tac term_ok_type_ok >>
             PURE_ONCE_REWRITE_TAC[CONJ_SYM] >>
             goal_assum drule >>
             rw[] >>
             match_mp_tac(CONJUNCT2 SUBMAP_FUNION_ID) >>
             drule extends_NIL_DISJOINT >>
             fs[])
         >- (rw[] >> fs[ground_types_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MAP_EQ_f] >>
             `MEM x (tvars pred)`
               by(match_mp_tac (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
                  fs[welltyped_def] >> imp_res_tac WELLTYPED_LEMMA >> rveq >>
                  goal_assum drule >> fs[tyvars_def]) >>
             res_tac >>
             rfs[])) >>
      `!x. MEM x (tyvars (TYPE_SUBST sigma (typeof witness))) ==> F`
        suffices_by(Cases_on `tyvars(TYPE_SUBST sigma (typeof witness))` >>
                    fs[DISJ_IMP_THM,FORALL_AND_THM]) >>
      rpt strip_tac >>
      `MEM x (tyvars (TYPE_SUBST sigma (typeof pred)))`
        by(fs[tyvars_def]) >>
      fs[ground_types_def,tyvars_def] >>
      imp_res_tac FOLDR_LIST_UNION_empty' >>
      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
      fs[tyvars_TYPE_SUBST] >>
      fs[welltyped_def] >> imp_res_tac WELLTYPED_LEMMA >> rveq >>
      qpat_x_assum `pred has_type typeof pred` assume_tac >>
      drule_all_then assume_tac (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
      res_tac >>
      fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
      res_tac >> fs[]
     )
  >- (simp[Once type_interpretation_of_def] >>
      IF_CASES_TAC >- fs[extends_init_def] >>
      reverse IF_CASES_TAC >- fs[ground_consts_def] >>
      TOP_CASE_TAC >-
        (TOP_CASE_TAC >-
           (reverse IF_CASES_TAC >-
              ((* Uninterpreted constant *)
               qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
               `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_of ind ctxt) ty`
                 by(match_mp_tac ext_type_frag_mono_eq >>
                    rw[Abbr `σ`]) >>
               fs[] >>
               rpt(first_x_assum(drule_then assume_tac)) >>
               fs[ground_consts_def] >>
               `inhabited(ext_type_frag_builtins (type_interpretation_of ind ctxt) ty)`
                 suffices_by metis_tac[] >>
               drule_then match_mp_tac (MP_CANON ext_inhabited_frag_inhabited') >>
               metis_tac[]) >>
            (* Hilbert choice *)
            fs[] >>
            fs[term_ok_def] >>
            simp[ext_type_frag_builtins_Fun] >>
            drule_then match_mp_tac abstract_in_funspace_matchable >>
            simp[] >>
            reverse CONJ_TAC >-
              (simp[allTypes'_defn] >>
               qmatch_goalsub_abbrev_tac `Funspace (Funspace a1 _) _ = Funspace (Funspace a2 _) _` >>
               `a1 = a2`
                 by(qunabbrev_tac `a1` >> qunabbrev_tac `a2` >>
                    match_mp_tac ext_type_frag_mono_eq >> rw[]) >>
               pop_assum SUBST_ALL_TAC >>
               ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[]
              ) >>
            rpt strip_tac >>
            drule_then drule in_funspace_abstract >>
            strip_tac >> rveq >>
            rw[some_def] >-
              (SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
            SELECT_ELIM_TAC >> simp[] >>
            drule_then match_mp_tac ext_inhabited_frag_inhabited >>
            qexists_tac `sigof ctxt` >>
            conj_asm1_tac >-
              (fs[ground_types_def,ground_consts_def,tyvars_def,tvars_def,LIST_UNION_EQ_NIL] >>
               drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
               qpat_x_assum `type_ok _ _` mp_tac >>
               fs[type_ok_def]) >>
            rw[mem_one,allTypes'_defn] >>
            first_x_assum(match_mp_tac o MP_CANON) >>
            simp[allTypes'_defn] >>
            metis_tac[]) >>
         reverse TOP_CASE_TAC >-
           (reverse IF_CASES_TAC >-
              ((* Uninterpreted constant *)
               qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
               `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_of ind ctxt) ty`
                 by(match_mp_tac ext_type_frag_mono_eq >>
                    rw[Abbr `σ`]) >>
               fs[] >>
               rpt(first_x_assum(drule_then assume_tac)) >>
               fs[ground_consts_def] >>
               `inhabited(ext_type_frag_builtins (type_interpretation_of ind ctxt) ty)`
                 suffices_by metis_tac[] >>
               drule_then match_mp_tac (MP_CANON ext_inhabited_frag_inhabited') >>
               metis_tac[]) >>
            (* Hilbert choice *)
            fs[] >>
            fs[term_ok_def] >>
            simp[ext_type_frag_builtins_Fun] >>
            drule_then match_mp_tac abstract_in_funspace_matchable >>
            simp[] >>
            reverse CONJ_TAC >-
              (simp[allTypes'_defn] >>
               qmatch_goalsub_abbrev_tac `Funspace (Funspace a1 _) _ = Funspace (Funspace a2 _) _` >>
               `a1 = a2`
                 by(qunabbrev_tac `a1` >> qunabbrev_tac `a2` >>
                    match_mp_tac ext_type_frag_mono_eq >> rw[]) >>
               pop_assum SUBST_ALL_TAC >>
               ONCE_REWRITE_TAC[ext_type_frag_builtins_def] >> simp[]
              ) >>
            rpt strip_tac >>
            drule_then drule in_funspace_abstract >>
            strip_tac >> rveq >>
            rw[some_def] >-
              (SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
            SELECT_ELIM_TAC >> simp[] >>
            drule_then match_mp_tac ext_inhabited_frag_inhabited >>
            qexists_tac `sigof ctxt` >>
            conj_asm1_tac >-
              (fs[ground_types_def,ground_consts_def,tyvars_def,tvars_def,LIST_UNION_EQ_NIL] >>
               drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
               qpat_x_assum `type_ok _ _` mp_tac >>
               fs[type_ok_def]) >>
            rw[mem_one,allTypes'_defn] >>
            first_x_assum(match_mp_tac o MP_CANON) >>
            simp[allTypes'_defn] >>
            metis_tac[]) >>
         (* abs and rep *)
         PairCases_on `h` >>
         rename1 `(is_abs,name0,abs_type,rep_type)` >>
         rw[] >>
         MAP_FIRST drule [rep_matches_is_instance,abs_matches_is_instance] >>
         disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
         FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
         rveq >>
         fs[IS_SOME_EXISTS] >>
         rename1 `instance_subst _ _ _ = SOME result` >>
         Cases_on `result` >>
         rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
         drule_then assume_tac instance_subst_soundness >>
         fs[] >>
         simp[ext_type_frag_builtins_Fun] >>
         rveq >>
         qabbrev_tac `tyfrag = set(allTypes' (TYPE_SUBST sigma cty))` >>
         qmatch_goalsub_abbrev_tac `Abstract (ext_type_frag_builtins σ _) _ _ ⋲ Funspace (ext_type_frag_builtins σ' _) _` >>
         `ext_type_frag_builtins σ (TYPE_SUBST sigma abs_type) = ext_type_frag_builtins σ' (TYPE_SUBST sigma abs_type)`
           by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`,Abbr`σ'`,allTypes'_defn] >> fs[]) >>
         `ext_type_frag_builtins σ (TYPE_SUBST sigma rep_type) = ext_type_frag_builtins σ' (TYPE_SUBST sigma rep_type)`
           by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`,Abbr`σ'`,allTypes'_defn] >> fs[]) >>
         ntac 2 (pop_assum(fn thm => SUBST_ALL_TAC thm >> mp_tac thm)) >>
         ntac 2 strip_tac >>
         drule_then match_mp_tac abstract_in_funspace
         >- ((* abs *)
             rw[] >>
             `inhabited(ext_type_frag_builtins σ' (TYPE_SUBST sigma abs_type))`
               suffices_by metis_tac[] >>
             drule_then match_mp_tac inhabited_ext >>
             qexists_tac `set(allTypes'(TYPE_SUBST sigma abs_type))` >>
             conj_tac >- (match_mp_tac builtin_closure_allTypes >> rw[]) >>
             conj_tac >- (rw[SUBSET_DEF] >> imp_res_tac allTypes'_nonbuiltin) >>
             rpt strip_tac >>
             first_x_assum(match_mp_tac o MP_CANON) >>
             simp[allTypes'_defn] >>
             reverse(rpt conj_tac) >- imp_res_tac allTypes'_nonbuiltin >- metis_tac[] >>
             fs[ground_consts_def] >>
             fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def] >>
             reverse conj_tac >- imp_res_tac allTypes'_type_ok >>
             imp_res_tac allTypes'_no_tyvars) >>
         (* rep *)
         rw[] >>
         drule abs_or_rep_matches_ext_type_frag_builtins >>
         disch_then drule >>
         disch_then(qspecl_then [`σ'`,`sigma`,`^mem`] SUBST_ALL_TAC) >>
         qunabbrev_tac `σ'` >>
         qpat_x_assum `_ ⋲ _` (assume_tac o REWRITE_RULE[Once type_interpretation_of_def]) >>
         rfs[] >>
         drule_then (drule_then strip_assume_tac) abs_or_rep_matches_type_matches >>
         rveq >>
         fs[IS_SOME_EXISTS] >>
         fs[mapPartial_APPEND,mllistTheory.mapPartial_def] >>
         rename1 `type_matches _ _ = SOME tymtch` >>
         PairCases_on `tymtch` >>
         fs[] >>
         drule type_matches_is_instance >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
         rveq >>
         fs[IS_SOME_EXISTS] >>
         rename1 `instance_subst _ _ _ = SOME result2` >>
         Cases_on `result2` >>
         rename1 `instance_subst _ _ _ = SOME(sigma',result2)` >>
         drule_then assume_tac instance_subst_soundness >>
         fs[] >>
         qpat_x_assum `x ⋲ if _ then _ else _` mp_tac >>
         IF_CASES_TAC >>
         rw[mem_sub] >>
         drule_all_then (MAP_EVERY SUBST_ALL_TAC o CONJUNCTS) abs_or_rep_matches_type_matches' >>
         qpat_x_assum `x ⋲ ext_type_frag_builtins _ _` mp_tac >>
         simp[Abbr `σ`] >>
         `TYPE_SUBST sigma (domain (typeof tymtch0)) =
          TYPE_SUBST sigma' (domain (typeof tymtch0))
         `
           by(imp_res_tac instance_subst_soundness >>
              fs[] >>
              fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
              rw[TYPE_SUBST_tyvars] >>
              first_x_assum match_mp_tac >>
              match_mp_tac(tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
              FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
              drule extends_APPEND_NIL >>
              rw[] >>
              dxrule extends_NIL_CONS_updates >>
              rw[] >> fs[updates_cases,type_matches_def] >>
              rveq >> fs[] >>
              imp_res_tac proves_term_ok >>
              fs[] >>
              drule extends_append_MID >> impl_tac >- rw[init_ctxt_def] >> strip_tac >>
              drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
              fs[term_ok_clauses] >>
              rveq >>
              fs[welltyped_def] >>
              asm_exists_tac >>
              imp_res_tac WELLTYPED_LEMMA >> rveq >>
              fs[tyvars_def]
             ) >>
         fs[] >>
         qmatch_goalsub_abbrev_tac `_ ⋲ ext_type_frag_builtins σ tt ==> _ ⋲ ext_type_frag_builtins σ' tt` >>
         `ext_type_frag_builtins σ tt = ext_type_frag_builtins σ' tt`
           suffices_by simp[] >>
         unabbrev_all_tac >>
         match_mp_tac ext_type_frag_mono_eq >>
         rw[MEM_MAP,MEM_FLAT,PULL_EXISTS]) >>
      fs[FILTER_EQ_CONS] >>
      rpt(pairarg_tac >> fs[] >> rveq) >>
      rename1 `HD ll` >> Cases_on `ll` >> fs[] >> rveq >>
      fs[MAP_EQ_APPEND,MAP_EQ_CONS] >> rveq >> fs[] >>
      qpat_x_assum `_ = defn_matches _ _ _` (assume_tac o GSYM) >>
      drule defn_matches_is_instance >>
      disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
      FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
      rveq >>
      fs[IS_SOME_EXISTS] >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
      drule_then assume_tac instance_subst_soundness >>
      fs[] >>
      FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
      drule_then (strip_assume_tac o REWRITE_RULE[APPEND]) extends_APPEND_NIL >>
      dxrule_then strip_assume_tac extends_NIL_CONS_updates >>
      drule_then (dxrule_then strip_assume_tac) defn_matches_wf >>
      fs[] >>
      dxrule_then (drule_then strip_assume_tac) term_ok_extends_APPEND >>
      rw[] >>
      simp[TYPE_SUBST_eq_TYPE_SUBSTf] >>
      qmatch_goalsub_abbrev_tac `termsem (ext_type_frag_builtins σ) (ext_term_frag_builtins (ext_type_frag_builtins σ) γ) _ _ _ ⋲ ext_type_frag_builtins σ' _` >>
      qabbrev_tac `tyfrag = set(FLAT(MAP allTypes' (MAP (TYPE_SUBST sigma) (allTypes trm0))))` >>
      qabbrev_tac `tmfrag = {(c',ty') | ∃ty''.
                              ty' =
                              TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                              ty'' ∧ (c',ty'') ∈ consts_of_term trm0 ∧
                              (c',ty') ∈ nonbuiltin_constinsts}` >>
      qmatch_asmsub_abbrev_tac `orth_ctxt ctxt` >>
      `is_sig_fragment (sigof ctxt) (tyfrag,tmfrag)`
        by(MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
           rw[is_sig_fragment_def]
           >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
               rw[ground_types_def] >-
                 (fs[ground_consts_def,ground_types_def] >>
                  drule allTypes_TYPE_SUBST_no_tyvars >>
                  rpt(disch_then drule) >> strip_tac >>
                  `!tv. MEM tv (tyvars x) ==> F`
                    suffices_by(Cases_on `tyvars x` >> fs[FORALL_AND_THM]) >>
                  rpt strip_tac >>
                  drule_all_then assume_tac MEM_tyvars_allTypes' >>
                  rfs[]) >>
               match_mp_tac allTypes'_type_ok >>
               goal_assum drule >>
               drule_all_then assume_tac allTypes_type_ok >>
               match_mp_tac type_ok_TYPE_SUBST_strong >>
               fs[] >> rw[] >>
               `type_ok (tysof ctxt) (TYPE_SUBST sigma (typeof trm0))`
                 by(qunabbrev_tac `ctxt` >> fs[ground_consts_def,term_ok_def] >> metis_tac[]) >>
               drule type_ok_TYPE_SUBST_imp >>
               drule_then (drule_then assume_tac) MEM_tyvars_allTypes >>
               rw[TYPE_SUBST_eq_TYPE_SUBSTf])
           >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >> imp_res_tac allTypes'_nonbuiltin)
           >- (rw[SUBSET_DEF] >>
               simp[GSYM TYPE_SUBST_eq_TYPE_SUBSTf] >>
               match_mp_tac ground_consts_TYPE_SUBST_lemma >>
               rw[Abbr `ctxt`])
           >- (rw[SUBSET_DEF] >> simp[])
           >- (
               match_mp_tac builtin_closure_allTypes''' >>
               rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
               drule_then (drule_then assume_tac) allTypes'_consts_of_term_IMP >>
               goal_assum drule >>
               rw[TYPE_SUBST_eq_TYPE_SUBSTf])
           ) >>
      `trm0 ∈ terms_of_frag_uninst (tyfrag,tmfrag) (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))`
        by(MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
           rw[terms_of_frag_uninst_def,IMAGE_DEF,SUBSET_DEF,INTER_DEF,PAIR_MAP]
           >- (rename1 `SND pp` >>
               qexists_tac `SND pp` >>
               rw[])
           >- rw[TYPE_SUBST_eq_TYPE_SUBSTf |> Q.GEN `ty` |> REWRITE_RULE[GSYM FUN_EQ_THM]]) >>
      `is_frag_interpretation (tyfrag,tmfrag) σ γ`
        by(MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
           rw[is_frag_interpretation_def]
           >- (rw[is_type_frag_interpretation_def,Abbr `σ`,Abbr `σ'`,Abbr `ctxt`] >>
               rfs[] >>
               first_x_assum(match_mp_tac o MP_CANON) >>
               simp[] >>
               reverse(rpt conj_tac) >-
                 (fs[MEM_FLAT,MEM_MAP] >> rveq >> imp_res_tac allTypes'_nonbuiltin) >-
                 (metis_tac[]) >>
               fs[ground_types_def] >>
               reverse conj_tac >-
                 (fs[MEM_FLAT,MEM_MAP] >> rveq >>
                  match_mp_tac allTypes'_type_ok >>
                  goal_assum drule >>
                  fs[ground_consts_def] >>
                  match_mp_tac type_ok_TYPE_SUBST_strong >>
                  conj_tac >-
                    (drule_then drule allTypes_type_ok >> rw[]) >>
                  fs[term_ok_def] >>
                  rpt strip_tac >>
                  drule_all_then strip_assume_tac MEM_tyvars_allTypes >>
                  first_x_assum(drule_then strip_assume_tac) >>
                  drule_then drule type_ok_TYPE_SUBST_imp >>
                  simp[]) >>
               fs[MEM_FLAT,MEM_MAP] >> rveq >>
               match_mp_tac allTypes'_no_tyvars >> goal_assum drule >>
               fs[ground_consts_def,ground_types_def] >>
               match_mp_tac allTypes_TYPE_SUBST_no_tyvars >>
               goal_assum drule >> goal_assum drule >>
               first_x_assum MATCH_ACCEPT_TAC) >>
           rw[GSYM PFORALL_THM,Abbr `γ`] >>
           reverse IF_CASES_TAC >-
             (fs[] >>
              pop_assum(qspec_then `ty''` assume_tac) >>
              rfs[] >>
              imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
           `ext_type_frag_builtins σ (TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) ty'')
            = ext_type_frag_builtins σ' (TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) ty'')`
              by(pop_assum kall_tac >>
                 match_mp_tac ext_type_frag_mono_eq'' >>
                 rw[Abbr `σ`] >>
                 fs[MEM_FLAT,MEM_MAP,PULL_FORALL] >> rveq >>
                 fs[GSYM(IMP_DISJ_THM |> ONCE_REWRITE_RULE[DISJ_SYM]),PULL_FORALL] >>
                 fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                 drule_then(drule_then assume_tac) allTypes'_consts_of_term_IMP >>
                 first_assum drule >> rw[]) >>
           pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
           first_x_assum(match_mp_tac o MP_CANON) >>
           simp[] >>
           conj_tac >- metis_tac[nonbuiltin_constinsts_TYPE_SUBSTf,TYPE_SUBST_eq_TYPE_SUBSTf] >>
           simp[GSYM TYPE_SUBST_eq_TYPE_SUBSTf] >>
           reverse conj_tac >- metis_tac[] >>
           match_mp_tac(ground_consts_TYPE_SUBST_lemma) >>
           rw[] >>
           fs[Abbr `ctxt`]) >>
      `is_frag_interpretation (tyfrag,tmfrag) σ' γ`
        by(fs[Abbr `σ`] >> metis_tac[is_frag_intepretation_ifE]) >>
      `termsem (ext_type_frag_builtins σ)
          (ext_term_frag_builtins (ext_type_frag_builtins σ) γ)
          empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) trm0 =
       termsem (ext_type_frag_builtins σ')
          (ext_term_frag_builtins (ext_type_frag_builtins σ') γ)
          empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x)) trm0
      `
       by(match_mp_tac fleq_term_interp_le_closed >>
          ntac 2 (qexists_tac `(tyfrag,tmfrag)`) >>
          qexists_tac `sigof ctxt` >>
          conj_tac >- rw[fleq_def,Abbr `σ`,Abbr `σ'`] >>
          rw[]) >>
      pop_assum SUBST_ALL_TAC >>
      match_mp_tac termsem_in_type_ext >>
      MAP_EVERY qexists_tac [`tyfrag`,`tmfrag`,`sigof ctxt`] >>
      rw[] >> rfs[CLOSED_def])
QED

Theorem interpretation_is_total_frag_interpretation:
  is_set_theory ^mem ⇒
    ∀ctxt. orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) /\ ctxt extends [] /\ ctxt extends init_ctxt /\ inhabited ind
    ⇒
        is_frag_interpretation (total_fragment (sigof ctxt))
          (type_interpretation_of ind ctxt)
          (UNCURRY (term_interpretation_of ind ctxt))
Proof
  rw[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def,
     GSYM PFORALL_THM] >>
  metis_tac[interpretation_is_total_frag_interpretation_lemma]
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

Triviality ALOOKUP_Tyvar:
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

(* TODO: can we state this with less typing? *)
Theorem type_interpretation_of_alt:
  (!^mem ind ctxt ty. is_set_theory ^mem /\ ctxt extends init_ctxt /\
                  is_frag_interpretation (total_fragment(sigof ctxt))
                   (type_interpretation_of ind ctxt)
                   (UNCURRY (term_interpretation_of ind ctxt)) /\
                  ty ∈ ground_types (sigof ctxt) /\
                  ty ∈ nonbuiltin_types
   ==> type_interpretation_of ind ctxt ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~orth_ctxt ctxt then
     One:'U
   else
     case mapPartial (type_matches ty) ctxt of
     | [] =>
       if ty = Tyapp (strlit "ind") [] then
         ind
       else
         One
     | [(pred,ty',tvs)] =>
       (case instance_subst [(ty, (Tyapp ty' (MAP Tyvar tvs)))] [] [] of
         | SOME(sigma,e) =>
            let pty = domain(typeof pred);
                consts = consts_of_term pred ∩ nonbuiltin_constinsts;
                inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
                sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
                γ = (λ(c,ty). term_interpretation_of0 ^mem ind ctxt c ty);
                δ = type_interpretation_of0 ^mem ind ctxt;
                tst = termsem (ext_type_frag_builtins δ)
                              (ext_term_frag_builtins
                                (ext_type_frag_builtins δ)
                                γ)
                              empty_valuation
                              sigma'
                              pred
            in
              if ?tm.
                  tm ⋲
                  (ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)) then
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
                  suchthat (λtm. tst ' tm = True)
              else
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty)
         | NONE => One:'U)
     | _ => One:'U
  ) /\
  (!^mem ind ctxt name ty.
   is_set_theory ^mem /\ ctxt extends init_ctxt /\
   (name,ty) ∈ ground_consts (sigof ctxt) /\
   (name,ty) ∈ nonbuiltin_constinsts /\
   inhabited ind /\
   is_frag_interpretation (total_fragment(sigof ctxt))
     (type_interpretation_of ind ctxt )
     (UNCURRY (term_interpretation_of ind ctxt)) ==>
   term_interpretation_of ind ctxt (name:mlstring) ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~orth_ctxt ctxt then
     One:'U
   else
     case FILTER ($<> []) (MAP (defn_matches name ty) ctxt) of
       [] =>
       (case mapPartial (abs_or_rep_matches name ty) ctxt of
        | [(is_abs,name0,abs_type,rep_type)] =>
          (let cty = if is_abs then Fun rep_type abs_type else Fun abs_type rep_type
           in
             case instance_subst [(ty, cty)] [] [] of
             | SOME(sigma,e) =>
               let
                 δ = type_interpretation_of0 ^mem ind ctxt;
                 sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
               in
                 if is_abs then
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (λv. if v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type) then
                                   v
                                 else
                                   @v. v <: ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                 else
                   Abstract (ext_type_frag_builtins δ (TYPE_SUBST sigma abs_type))
                            (ext_type_frag_builtins δ (TYPE_SUBST sigma rep_type))
                            I
             | NONE => One (* cannot happen *))
        | _ =>
          let δ = type_interpretation_of0 ^mem ind ctxt in
            if name = strlit "@" /\ MEM ^select_ax ctxt /\
               FLOOKUP (tmsof ctxt) (strlit "==>") = SOME (Fun Bool (Fun Bool Bool)) /\
               FLOOKUP (tmsof ctxt) (strlit "@") = SOME(^select_ty)
             then
              Abstract (ext_type_frag_builtins δ (domain ty))
                       (ext_type_frag_builtins δ (codomain ty))
                       (λp.
                         case some x. x <: (ext_type_frag_builtins δ (codomain ty)) ∧
                                      p ' x = True of
                           NONE => (@x. x <: ext_type_frag_builtins δ (codomain ty))
                         | SOME v => v
                       )
            else
              @v. v <: ext_type_frag_builtins δ ty
       )
     | l =>
       let (name0,trm0) = HD(HD l)
       in
         case instance_subst [(ty, typeof trm0)] [] [] of
         | SOME(sigma,e) =>
           let
             pty = domain(typeof trm0);
             consts = consts_of_term trm0 ∩ nonbuiltin_constinsts;
             inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
             sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
             γ = (λ(c,ty). term_interpretation_of0 ^mem ind ctxt c ty);
             atys = MAP (TYPE_SUBST sigma) (allTypes trm0);
             δ = type_interpretation_of0 ^mem ind ctxt
           in
             termsem (ext_type_frag_builtins δ)
                       (ext_term_frag_builtins
                         (ext_type_frag_builtins δ)
                         γ)
                       empty_valuation
                       sigma'
                       trm0
         | NONE => One (* cannot happen *)
  )
Proof
  rpt strip_tac >>
  CONV_TAC(LHS_CONV(PURE_ONCE_REWRITE_CONV[type_interpretation_of_def])) >>
  (IF_CASES_TAC >- rw[]) >>
  (IF_CASES_TAC >- (fs[extends_init_def,ground_consts_def] >> fs[]))
  >-
    ((* type interpretation *)
     ntac 6 (TOP_CASE_TAC >> fs[] >> rveq) >>
     drule_then assume_tac instance_subst_soundness >>
     simp[mem_sub] >>
     qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
     qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins σ') γ` >>
     rename1 `TYPE_SUBST sigma (domain (typeof pred))` >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma (domain (typeof pred))) =
      ext_type_frag_builtins (type_interpretation_of ind ctxt) (TYPE_SUBST sigma (domain (typeof pred)))
     `
       by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`]) >>
     simp[] >>
     `termsem (ext_type_frag_builtins σ')
                 (ext_term_frag_builtins (ext_type_frag_builtins σ') γ)
                 empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                 pred =
      termsem (ext_type_frag_builtins (type_interpretation_of ind ctxt))
                 (ext_term_frag_builtins (ext_type_frag_builtins (type_interpretation_of ind ctxt))
                                         (UNCURRY(term_interpretation_of ind ctxt)))
                 empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                 pred
     `
      by(match_mp_tac fleq_term_interp_le_closed >>
         qabbrev_tac `tyfrag = set(FLAT (MAP allTypes'(MAP (TYPE_SUBST sigma) (allTypes pred))))` >>
         qabbrev_tac `tmfrag = {(c',ty') | ∃ty''.
                                 ty' = TYPE_SUBST sigma ty'' ∧ (c',ty'') ∈ consts_of_term pred ∧
                                 (c',ty') ∈ nonbuiltin_constinsts}` >>
         ntac 2(qexists_tac `(tyfrag,tmfrag)`) >>
         qexists_tac `sigof ctxt` >>
         conj_tac >- (rw[fleq_def,Abbr `σ'`,Abbr`tmfrag`,Abbr `γ`] >> rw[] >>
                      goal_assum kall_tac >>
                      fs[] >>
                      first_x_assum(qspec_then `ty''` mp_tac) >>
                      simp[] >>
                      fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                      imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
         conj_asm1_tac >-
           (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
            rw[is_sig_fragment_def] >>
            fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
            rveq >> fs[] >> rveq >> fs[] >>
            fs[type_matches_def] >>
            qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
            fs[CaseEq "update"] >> rveq >> fs[] >>
            fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
            drule extends_append_MID >>
            (impl_tac >- rw[init_ctxt_def]) >>
            FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
            drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
            drule extends_APPEND_NIL >> simp[] >> strip_tac >>
            dxrule extends_NIL_CONS_updates >>
            simp[updates_cases] >> rpt strip_tac >> rveq >> fs[] >>
            `q' <> strlit "fun"`
              by(drule_then strip_assume_tac extends_appends >>
                 CCONTR_TAC >> fs[init_ctxt_def]) >>
            `q' <> strlit "bool"`
              by(drule_then strip_assume_tac extends_appends >>
                 CCONTR_TAC >> fs[init_ctxt_def]) >>
            simp[allTypes'_defn] >>
            imp_res_tac proves_term_ok >>
            fs[] >>
            drule extends_NIL_APPEND_extends >> strip_tac >>
            dxrule_then drule term_ok_extends >> strip_tac >>
            dxrule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
            fs[term_ok_clauses]
            >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
                rw[ground_types_def]
                >- (match_mp_tac allTypes'_no_tyvars >>
                    goal_assum drule >>
                    `!ty. MEM ty (tyvars (TYPE_SUBST sigma y')) ==> F`
                      suffices_by(Cases_on `tyvars (TYPE_SUBST sigma y')` >> fs[DISJ_IMP_THM,FORALL_AND_THM] >> fs[]) >>
                    rpt strip_tac >>
                    fs[tyvars_TYPE_SUBST] >>
                    drule_all_then assume_tac MEM_tyvars_allTypes >>
                    first_x_assum drule >> strip_tac >>
                    fs[ground_types_def,tyvars_def] >>
                    drule FOLDR_LIST_UNION_empty' >>
                    strip_tac >>
                    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
                drule_then match_mp_tac allTypes'_type_ok >>
                match_mp_tac type_ok_TYPE_SUBST_strong >>
                fs[term_ok_clauses] >>
                conj_tac >- (drule_then drule allTypes_type_ok >> simp[]) >>
                qpat_x_assum `_ ∈ ground_types _` assume_tac >>
                rpt strip_tac >>
                fs[ground_types_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                drule_then drule MEM_tyvars_allTypes >> strip_tac >>
                first_x_assum drule >>
                first_x_assum drule >>
                rw[])
            >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >> imp_res_tac allTypes'_nonbuiltin)
            >- (rw[SUBSET_DEF] >>
                fs[ground_consts_def] >>
                conj_tac >-
                  (simp[ground_types_def] >>
                   conj_tac >-
                     (`!ty. MEM ty (tyvars (TYPE_SUBST sigma ty'')) ==> F`
                      suffices_by(Cases_on `tyvars (TYPE_SUBST sigma ty'')` >> fs[DISJ_IMP_THM,FORALL_AND_THM] >> fs[]) >>
                      rpt strip_tac >>
                      fs[tyvars_TYPE_SUBST] >>
                      drule_then drule consts_of_term_tyvars_tvars >>
                      fs[ground_types_def,tyvars_def] >>
                      drule FOLDR_LIST_UNION_empty' >>
                      strip_tac >>
                      fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                      spose_not_then strip_assume_tac >>
                      ntac 2(first_x_assum drule) >> rpt strip_tac >>
                      fs[]) >>
                   drule_then drule consts_of_term_term_ok >>
                   strip_tac >>
                   drule (ONCE_REWRITE_RULE[CONJ_SYM] term_ok_type_ok) >>
                   impl_tac >- rfs[] >>
                   simp[] >>
                   strip_tac >>
                   drule_then match_mp_tac type_ok_TYPE_SUBST_strong >>
                   rpt strip_tac >>
                   drule_then drule consts_of_term_tyvars_tvars >>
                   strip_tac >>
                   fs[ground_types_def] >>
                   qpat_x_assum `type_ok _ (Tyapp _ _)` mp_tac >>
                   rw[type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
                drule_then drule consts_of_term_term_ok >>
                strip_tac >>
                fs[term_ok_def] >>
                reverse conj_tac >- (metis_tac[TYPE_SUBST_compose]) >>
                pop_assum(SUBST_ALL_TAC o GSYM) >>
                drule_then match_mp_tac type_ok_TYPE_SUBST_strong >>
                rpt strip_tac >>
                drule_then drule consts_of_term_tyvars_tvars >>
                strip_tac >>
                fs[ground_types_def] >>
                qpat_x_assum `type_ok _ (Tyapp _ _)` mp_tac >>
                rw[type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS])
            >- (rw[SUBSET_DEF] >> rw[])
            >- (simp[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                match_mp_tac builtin_closure_allTypes''' >>
                rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
                drule_then drule allTypes'_consts_of_term_IMP >>
                metis_tac[TYPE_SUBST_eq_TYPE_SUBSTf])) >>
         conj_tac >-
           (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
            rw[terms_of_frag_uninst_def,IMAGE_DEF,SUBSET_DEF,INTER_DEF,PAIR_MAP,TYPE_SUBST_eq_TYPE_SUBSTf]
            >- (rename1 `SND pp` >> qexists_tac `SND pp` >> rw[])
            >- (fs[MEM_FLAT,MEM_MAP,PULL_EXISTS,TYPE_SUBST_eq_TYPE_SUBSTf] >> metis_tac[])
            >- (fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
                rveq >> fs[] >> rveq >> fs[] >>
                fs[type_matches_def] >>
                qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
                fs[CaseEq "update"] >> rveq >> fs[] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
                drule extends_append_MID >>
                (impl_tac >- rw[init_ctxt_def]) >>
                FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                drule extends_APPEND_NIL >> simp[] >> strip_tac >>
                dxrule extends_NIL_CONS_updates >>
                simp[updates_cases] >> rpt strip_tac >> rveq >> fs[] >>
                imp_res_tac proves_term_ok >>
                fs[] >>
                drule extends_NIL_APPEND_extends >> strip_tac >>
                dxrule_then drule term_ok_extends >> strip_tac >>
                dxrule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
                drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
                fs[term_ok_clauses])) >>
           conj_tac >- simp[] >>
           conj_tac >-
             (qunabbrev_tac `σ'` >> qunabbrev_tac `γ` >>
              qmatch_goalsub_abbrev_tac `is_frag_interpretation _ _ γ'` >>
              `?whatevz. γ' = (λ(c,ty'). if (c,ty') ∈ tmfrag then term_interpretation_of ind ctxt c ty' else whatevz c ty')`
                by(qexists_tac `CURRY γ'` >>
                   rw[Abbr `γ'`] >> simp[FUN_EQ_THM] >> rpt strip_tac >>
                   IF_CASES_TAC >- rw[] >>
                   rw[Abbr `tmfrag`] >>
                   fs[] >>
                   rename1 `(_,tya) ∈ consts_of_term _` >>
                   goal_assum kall_tac >>
                   first_x_assum(qspec_then `tya` mp_tac) >>
                   rw[] >>
                   fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
                   imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
              pop_assum SUBST_ALL_TAC >>
              pop_assum kall_tac >>
              match_mp_tac(GEN_ALL is_frag_intepretation_ifI) >>
              HINT_EXISTS_TAC >> simp[] >>
              drule_then match_mp_tac is_frag_interpretation_mono >>
              strip_tac >> imp_res_tac total_fragment_is_top_fragment) >>
           fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
           rveq >> fs[] >> rveq >> fs[] >>
           fs[type_matches_def] >>
           qpat_x_assum `SOME _ = _` (assume_tac o GSYM) >>
           fs[CaseEq "update"] >> rveq >> fs[] >>
           fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
           drule extends_append_MID >>
           (impl_tac >- rw[init_ctxt_def]) >>
           FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
           drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_APPEND_NIL >> simp[] >> strip_tac >>
           dxrule extends_NIL_CONS_updates >>
           simp[updates_cases] >> rpt strip_tac >> rveq >> fs[]) >>
     ntac 2 (pop_assum SUBST_ALL_TAC) >>
     simp[ELIM_UNCURRY]) >>
  TOP_CASE_TAC >-
    ((* Type definition matches (so const is abs/rep) *)
     TOP_CASE_TAC >-
       (reverse IF_CASES_TAC >- fs[ground_consts_def] >>
        simp[] >>
        reverse IF_CASES_TAC >-
         (simp[] >>
          qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
          `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_of ind ctxt) ty`
            by(match_mp_tac ext_type_frag_mono_eq >>
               rw[Abbr `σ`]) >>
          simp[]) >>
        (* Hilbert choice *)
        fs[term_ok_def] >>
        simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
        qmatch_goalsub_abbrev_tac `ext_type_frag_builtins δ` >>
        `ext_type_frag_builtins δ (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» )) =
         ext_type_frag_builtins (type_interpretation_of ind ctxt)
                                (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» ))`
          by(match_mp_tac ext_type_frag_mono_eq >> rw[allTypes'_defn,Abbr`δ`]) >>
        pop_assum SUBST_ALL_TAC >>
        drule_then match_mp_tac abstract_eq >>
        rw[] >>
        rw[some_def] >> SELECT_ELIM_TAC >> simp[] >- metis_tac[] >>
        drule_then match_mp_tac ext_inhabited_frag_inhabited >>
        qexists_tac `sigof ctxt` >>
        conj_asm1_tac >-
          (fs[ground_consts_def,ground_types_def,LIST_UNION_EQ_NIL,
              term_ok_def,tyvars_def,type_ok_def] >>
           metis_tac[]) >>
        rw[] >>
        drule_then match_mp_tac(CONJUNCT1 interpretation_is_total_frag_interpretation_lemma) >>
        simp[] >>
        metis_tac[extends_trans,init_ctxt_extends]) >>
     reverse TOP_CASE_TAC >-
       (reverse IF_CASES_TAC >- fs[ground_consts_def] >>
        simp[] >>
        reverse IF_CASES_TAC >-
         (simp[] >>
          qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
          `ext_type_frag_builtins σ ty = ext_type_frag_builtins (type_interpretation_of ind ctxt) ty`
            by(match_mp_tac ext_type_frag_mono_eq >>
               rw[Abbr `σ`]) >>
          simp[]) >>
        (* Hilbert choice *)
        fs[term_ok_def] >>
        simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
        qmatch_goalsub_abbrev_tac `ext_type_frag_builtins δ` >>
        `ext_type_frag_builtins δ (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» )) =
         ext_type_frag_builtins (type_interpretation_of ind ctxt)
                                (REV_ASSOCD (Tyvar «A» ) i (Tyvar «A» ))`
          by(match_mp_tac ext_type_frag_mono_eq >> rw[allTypes'_defn,Abbr`δ`]) >>
        pop_assum SUBST_ALL_TAC >>
        drule_then match_mp_tac abstract_eq >>
        rw[] >>
        rw[some_def] >> SELECT_ELIM_TAC >> simp[] >- metis_tac[] >>
        drule_then match_mp_tac ext_inhabited_frag_inhabited >>
        qexists_tac `sigof ctxt` >>
        conj_asm1_tac >-
          (fs[ground_consts_def,ground_types_def,LIST_UNION_EQ_NIL,
              term_ok_def,tyvars_def,type_ok_def] >>
           metis_tac[]) >>
        rw[] >>
        drule_then match_mp_tac(CONJUNCT1 interpretation_is_total_frag_interpretation_lemma) >>
        simp[] >>
        metis_tac[extends_trans,init_ctxt_extends]) >>
     simp[] >>
     ntac 5 TOP_CASE_TAC >>
     simp[allTypes'_defn] >>
     rename1 `TYPE_SUBST sigma` >>
     rename1 `(is_abs,_,abs_type,rep_type)` >> rw[] >>
     qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma rep_type) = ext_type_frag_builtins (type_interpretation_of ind ctxt) (TYPE_SUBST sigma rep_type)`
       by(match_mp_tac ext_type_frag_mono_eq >>
          rw[Abbr `σ`]) >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma abs_type) = ext_type_frag_builtins (type_interpretation_of ind ctxt) (TYPE_SUBST sigma abs_type)`
       by(match_mp_tac ext_type_frag_mono_eq >>
          rw[Abbr `σ`]) >>
     ntac 2 (pop_assum SUBST_ALL_TAC) >> simp[]) >>
  (* Definition matches *)
  rename1 `elem ⋲ ind` >>
  fs[FILTER_EQ_CONS] >>
  rpt(pairarg_tac >> fs[] >> rveq) >>
  rename1 `HD ll` >> Cases_on `ll` >> fs[] >> rveq >>
  fs[MAP_EQ_APPEND,MAP_EQ_CONS] >> rveq >> fs[] >>
  qpat_x_assum `_ = defn_matches _ _ _` (assume_tac o GSYM) >>
  drule defn_matches_is_instance >>
  disch_then(MAP_EVERY assume_tac o CONJUNCTS) >>
  FULL_SIMP_TAC bool_ss [instance_subst_completeness] >>
  rveq >>
  fs[IS_SOME_EXISTS] >>
  rename1 `instance_subst _ _ _ = SOME result` >>
  Cases_on `result` >>
  rename1 `instance_subst _ _ _ = SOME(sigma,result)` >>
  drule_then assume_tac instance_subst_soundness >>
  fs[] >>
  FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
  drule_then (strip_assume_tac o REWRITE_RULE[APPEND]) extends_APPEND_NIL >>
  dxrule_then strip_assume_tac extends_NIL_CONS_updates >>
  drule_then (dxrule_then strip_assume_tac) defn_matches_wf >>
  fs[] >>
  dxrule_then (drule_then strip_assume_tac) term_ok_extends_APPEND >>
  rw[] >>
  qmatch_goalsub_abbrev_tac `termsem (ext_type_frag_builtins σ) (ext_term_frag_builtins (ext_type_frag_builtins σ) γ)` >>
  qabbrev_tac `tyfrag = set(FLAT(MAP allTypes' (MAP (TYPE_SUBST sigma) (allTypes trm0))))` >>
  qabbrev_tac `tmfrag = {(c',ty') | ∃ty''.
                              ty' =
                              TYPE_SUBSTf (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                              ty'' ∧ (c',ty'') ∈ consts_of_term trm0 ∧
                              (c',ty') ∈ nonbuiltin_constinsts}` >>
  drule_then (assume_tac o C MATCH_MP is_std_sig_init) is_std_sig_extends >>
  match_mp_tac fleq_term_interp_le_closed >>
  ntac 2 (qexists_tac `(tyfrag,tmfrag)`) >>
  rename1 `ctxt1 ++ [upd] ++ ctxt2` >>
  qexists_tac `sigof(ctxt1 ++ [upd] ++ ctxt2)` >>
  conj_tac >- (rw[fleq_def,Abbr `σ`,Abbr`tmfrag`,Abbr `γ`] >> rw[] >>
               goal_assum kall_tac >>
               fs[] >>
               first_x_assum(qspec_then `ty''` mp_tac) >>
               simp[] >>
               fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
               imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
  conj_asm1_tac >-
    (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
     rw[is_sig_fragment_def]
     >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
         rw[ground_types_def] >-
           (fs[ground_consts_def,ground_types_def] >>
            drule allTypes_TYPE_SUBST_no_tyvars >>
            rpt(disch_then drule) >> strip_tac >>
            `!tv. MEM tv (tyvars x) ==> F`
              suffices_by(Cases_on `tyvars x` >> fs[FORALL_AND_THM]) >>
            rpt strip_tac >>
            drule_all_then assume_tac MEM_tyvars_allTypes' >>
            rfs[]) >>
         match_mp_tac allTypes'_type_ok >>
         goal_assum drule >>
         drule_all_then assume_tac allTypes_type_ok >>
         match_mp_tac type_ok_TYPE_SUBST_strong >>
         fs[] >> rw[] >>
         fs[ground_consts_def] >>
         drule_then dxrule term_ok_type_ok >>
         drule_then dxrule term_ok_type_ok >>
         rw[] >>
         drule type_ok_TYPE_SUBST_imp >>
         simp[] >>
         disch_then match_mp_tac >>
         drule_then (drule_then assume_tac) MEM_tyvars_allTypes >>
         res_tac)
     >- (rw[SUBSET_DEF,MEM_FLAT,MEM_MAP] >> imp_res_tac allTypes'_nonbuiltin)
     >- (rw[SUBSET_DEF] >>
         simp[GSYM TYPE_SUBST_eq_TYPE_SUBSTf] >>
         match_mp_tac(GEN_ALL ground_consts_TYPE_SUBST_lemma) >>
         simp[] >>
         goal_assum drule >>
         simp[] >>
         rfs[])
     >- (rw[SUBSET_DEF] >> simp[])
     >- (
         match_mp_tac builtin_closure_allTypes''' >>
         rw[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
         drule_then (drule_then assume_tac) allTypes'_consts_of_term_IMP >>
         goal_assum drule >>
         rw[TYPE_SUBST_eq_TYPE_SUBSTf])) >>
  conj_tac >-
    (MAP_EVERY qunabbrev_tac [`tyfrag`,`tmfrag`] >>
     rw[terms_of_frag_uninst_def,IMAGE_DEF,SUBSET_DEF,INTER_DEF,PAIR_MAP]
     >- (rename1 `SND pp` >>
         qexists_tac `SND pp` >>
         rw[])
     >- rw[TYPE_SUBST_eq_TYPE_SUBSTf |> Q.GEN `ty` |> REWRITE_RULE[GSYM FUN_EQ_THM]]) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (qunabbrev_tac `σ` >> qunabbrev_tac `γ` >>
     qmatch_goalsub_abbrev_tac `is_frag_interpretation _ _ γ'` >>
     `?whatevz. γ' = (λ(c,ty'). if (c,ty') ∈ tmfrag then term_interpretation_of ind (ctxt1 ++ [upd] ++ ctxt2) c ty' else whatevz c ty')`
       by(qexists_tac `CURRY γ'` >>
          rw[Abbr `γ'`] >> simp[FUN_EQ_THM] >> rpt strip_tac >>
          IF_CASES_TAC >- rw[] >>
          rw[Abbr `tmfrag`] >>
          fs[] >>
          rename1 `(_,tya) ∈ consts_of_term _` >>
          goal_assum kall_tac >>
          first_x_assum(qspec_then `tya` mp_tac) >>
          rw[] >>
          fs[TYPE_SUBST_eq_TYPE_SUBSTf] >>
          imp_res_tac nonbuiltin_constinsts_TYPE_SUBSTf) >>
     pop_assum SUBST_ALL_TAC >>
     pop_assum kall_tac >>
     match_mp_tac(GEN_ALL is_frag_intepretation_ifI) >>
     HINT_EXISTS_TAC >> simp[] >>
     drule_then match_mp_tac is_frag_interpretation_mono >>
     strip_tac >> imp_res_tac total_fragment_is_top_fragment >> fs[]) >>
  fs[mllistTheory.mapPartial_thm,FILTER_EQ_CONS,MAP_EQ_APPEND,IS_SOME_EXISTS] >>
  rveq >> fs[] >> rveq >> fs[] >>
  fs[type_matches_def] >>
  fs[CaseEq "update"] >> rveq >> fs[] >>
  fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
  drule extends_append_MID >>
  (impl_tac >- rw[init_ctxt_def]) >>
  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
  drule extends_APPEND_NIL >> simp[] >> strip_tac >>
  dxrule extends_NIL_CONS_updates >>
  simp[updates_cases] >> rpt strip_tac >> rveq >> fs[]
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

Theorem interpretation_models_axioms_lemma:
  is_set_theory ^mem ⇒
  ∀ctxt1 upd ctxt2 p.
    upd updates ctxt2 /\ theory_ok(thyof(ctxt1 ++ upd::ctxt2)) /\
    is_frag_interpretation (total_fragment (sigof (ctxt1 ++ upd::ctxt2)))
      (type_interpretation_of ind (ctxt1 ++ upd::ctxt2))
      (UNCURRY (term_interpretation_of ind (ctxt1 ++ upd::ctxt2))) /\
    is_sig_fragment (sigof (ctxt1 ++ upd::ctxt2)) (total_fragment (sigof (ctxt1 ++ upd::ctxt2))) /\
    ctxt2 extends init_ctxt /\
    ctxt1 ++ upd::ctxt2 extends init_ctxt /\
    is_std_sig (sigof(ctxt1 ++ upd::ctxt2)) /\
    is_std_sig (sigof(ctxt2)) /\
    inhabited ind /\
    (∀p. MEM (NewAxiom p) (upd::ctxt2) ⇒
          MEM (NewAxiom p) ctxt2 \/
          admissible_axiom mem ind upd ctxt2
    ) /\
    orth_ctxt (ctxt1 ++ upd::ctxt2) /\
    terminating (subst_clos (dependency (ctxt1 ++ upd::ctxt2))) /\
    (∀p. MEM p (axiom_list ctxt2) ==>
          satisfies_t (sigof (ctxt1 ++ upd::ctxt2))
          (ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ upd::ctxt2)))
          (ext_term_frag_builtins
             (ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ upd::ctxt2)))
             (UNCURRY (term_interpretation_of ind (ctxt1 ++ upd::ctxt2)))) ([],p)) /\
    MEM p (axioms_of_upd upd)
    ==>
    satisfies_t (sigof (ctxt1 ++ upd::ctxt2))
          (ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ upd::ctxt2)))
          (ext_term_frag_builtins
             (ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ upd::ctxt2)))
             (UNCURRY (term_interpretation_of ind (ctxt1 ++ upd::ctxt2)))) ([],p)
Proof
  rw[updates_cases,axexts_of_upd_def,DISJ_IMP_THM] >>
  fs[axexts_of_upd_def] >> rveq
  >- ((* pre-existing axiom *)
      first_x_assum match_mp_tac >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[])
  >- ((* new axiom *)
      fs[admissible_axiom_def]
      >- ((* ETA axiom*)
          fs[mk_eta_ctxt_def] >>
          rw[satisfies_t_def,satisfies_def,termsem_def] >>
          dep_rewrite.DEP_REWRITE_TAC[termsem_ext_equation |> REWRITE_RULE[termsem_ext_def]] >>
          simp[] >>
          conj_tac >-
            (goal_assum drule >>
             fs[valuates_frag_builtins] >>
             drule_then drule terms_of_frag_uninst_equationE >>
             impl_tac >- (simp[welltyped_equation]) >>
             rw[] >>
             simp[term_ok_equation] >>
             simp[term_ok_clauses]) >>
          simp[boolean_eq_true] >>
          simp[termsem_def] >>
          simp[UPDATE_def] >>
          qmatch_goalsub_abbrev_tac `type_interpretation_of _ ctxt` >>
          `v («f» ,Fun (Tyvar «A» ) (Tyvar «B» )) ⋲
             ext_type_frag_builtins (type_interpretation_of ind ctxt)
                                    (TYPE_SUBSTf sigma (Fun (Tyvar «A» ) (Tyvar «B» )))`
            by(FULL_SIMP_TAC bool_ss [valuates_frag_builtins] >>
               FULL_SIMP_TAC bool_ss [valuates_frag_def] >>
               first_x_assum match_mp_tac >>
               match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
               qexists_tac `Var ARB (Fun (Tyvar «A» ) (Tyvar «B» ))` >>
               simp[VFREE_IN_def] >>
               goal_assum drule >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               simp[] >>
               simp[term_ok_def] >>
               metis_tac[term_ok_clauses,FST]) >>
          fs[ext_type_frag_builtins_Fun] >>
          drule_then drule in_funspace_abstract >>
          rw[] >> rw[] >>
          drule_then match_mp_tac abstract_eq >>
          simp[] >>
          rw[] >> simp[apply_abstract])
      >- ((* Axiom of choice *)
          fs[mk_select_ctxt_def] >>
          rw[satisfies_t_def,satisfies_def] >>
          `ALOOKUP (const_list ctxt1) (strlit "@") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE]) >>
          `ALOOKUP (const_list ctxt1) (strlit "==>") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,holBoolSyntaxTheory.mk_bool_ctxt_def]) >>
          rename1 `mk_bool_ctxt ctxt3` >>
          qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins δ) γ` >>
          qmatch_asmsub_abbrev_tac `ctxt extends init_ctxt` >>
          `is_bool_interpretation_ext (sigof ctxt) δ γ`
            by(drule_then match_mp_tac extends_is_bool_interpretation >>
               qexists_tac `ctxt3` >>
               qexists_tac `axsof (mk_bool_ctxt ctxt3)` >>
               conj_tac >-
                 (qpat_x_assum `NewConst _ _ :: _ extends _` assume_tac >>
                  drule extends_appends >>
                  strip_tac >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rveq >>
                  drule(extends_append_MID |> Q.INST [`a`|->`[]`] |> REWRITE_RULE [APPEND]) >>
                  impl_tac >- rw[init_ctxt_def] >>
                  strip_tac >>
                  drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
                  fs[]) >>
               `ctxt extends mk_bool_ctxt ctxt3`
                 by(qunabbrev_tac `ctxt` >>
                    `mk_bool_ctxt ctxt3 = [] ++ mk_bool_ctxt ctxt3` by simp[] >>
                    pop_assum(fn thm => PURE_ONCE_REWRITE_TAC[Once thm]) >>
                    PURE_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] >>
                    PURE_REWRITE_TAC[APPEND_ASSOC] >>
                    match_mp_tac extends_NIL_APPEND_extends >>
                    drule_then(assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                    PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >> simp[]) >>
               drule extends_sub >>
               rw[] >>
               simp[models_def] >>
               fs[Abbr `ctxt`]) >>
          fs[is_bool_interpretation_ext_def,is_bool_interpretation_def,
             is_implies_interpretation_def] >>
          simp[termsem_def] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_boolrel_rw] >> simp[] >>
          fs[valuates_frag_builtins] >> fs[valuates_frag_def] >>
          `v («P» ,Fun (Tyvar «A» ) Bool) ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (Fun (Tyvar «A» ) Bool))`
            by(first_x_assum match_mp_tac >>
               match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
               Q.REFINE_EXISTS_TAC `Var _ _` >>
               simp[VFREE_IN_def] >>
               goal_assum drule >>
               qexists_tac `ARB` >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               conj_tac >- (rw[term_ok_def] >> metis_tac[term_ok_clauses,FST]) >>
               simp[]) >>
          `v («x» ,Tyvar «A») ⋲ ext_type_frag_builtins δ (TYPE_SUBSTf sigma (Tyvar «A»))`
            by(first_x_assum match_mp_tac >>
               match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
               Q.REFINE_EXISTS_TAC `Var _ _` >>
               simp[VFREE_IN_def] >>
               goal_assum drule >>
               qexists_tac `ARB` >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               conj_tac >- (rw[term_ok_def] >> metis_tac[term_ok_clauses,FST]) >>
               simp[]) >>
          fs[ext_type_frag_builtins_Bool,ext_type_frag_builtins_Fun] >>
          drule_then drule in_funspace_abstract >>
          strip_tac >> rveq >>
          simp[] >>
          simp[ext_term_frag_builtins_def] >>
          `γ (strlit "@",Fun (Fun (sigma(strlit "A")) Bool) (sigma(strlit "A"))) =
           Abstract (ext_type_frag_builtins δ (Fun (sigma(strlit "A")) Bool))
                          (ext_type_frag_builtins δ (sigma(strlit "A")))
                          (λp.
                            case some x. (^mem x (ext_type_frag_builtins δ (sigma(strlit "A"))) ∧
                                         p ' x = True) of
                              NONE => (@x. ^mem x (ext_type_frag_builtins δ (sigma(strlit "A"))))
                            | SOME x => x)`
            by(rw[Abbr `γ`,Abbr `δ`] >>
               dep_rewrite.DEP_ONCE_REWRITE_TAC[CONJUNCT2 type_interpretation_of_alt] >>
               simp[] >>
               conj_tac >-
                 (simp[Abbr `ctxt`] >>
                  simp[nonbuiltin_constinsts_def,builtin_consts_def,ground_consts_def,ground_types_def,tyvars_def] >>
                  fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
                  reverse conj_tac >- metis_tac[] >>
                  conj_asm1_tac >- (metis_tac[term_ok_clauses,FST]) >>
                  simp[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
                  qexists_tac `[(sigma «A»,Tyvar «A»)]` >>
                  EVAL_TAC) >>
               reverse TOP_CASE_TAC >-
                 (goal_assum kall_tac >>
                  pop_assum mp_tac >> simp[] >>
                  qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
                  `FILTER fff lll = []` suffices_by simp[] >>
                  MAP_EVERY qunabbrev_tac [`fff`,`lll`] >>
                  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP] >>
                  fs[Abbr `ctxt`,defn_matches_NewAxiom,defn_matches_NewConst] >-
                    (simp[defn_matches_def] >>
                     TOP_CASE_TAC >> simp[] >>
                     CONV_TAC SYM_CONV >>
                     rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP] >>
                     pairarg_tac >> rw[] >>
                     imp_res_tac ALOOKUP_NONE >>
                     qpat_x_assum `MEM _ ctxt1` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                     rveq >> fs[] >>
                     qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                     rveq >> fs[] >>
                     FULL_CASE_TAC >> fs[] >>
                     qpat_x_assum `_ extends _` assume_tac >>
                     drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                     FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                     dxrule extends_APPEND_NIL >>
                     simp[extends_NIL_CONS_extends,updates_cases,constspec_ok_def,is_reserved_name_def] >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
                     rw[] >> simp[]) >>
                  simp[defn_matches_def] >>
                  TOP_CASE_TAC >> simp[] >>
                  CONV_TAC SYM_CONV >>
                  rw[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP] >>
                  pairarg_tac >> rw[] >>
                  qpat_x_assum `_ :: _ extends _` assume_tac >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  fs[extends_NIL_CONS_extends,updates_cases] >>
                  qpat_x_assum `MEM _ (mk_bool_ctxt _)` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                  rveq >> fs[] >>
                  Cases_on `b` >-
                    (FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                     dxrule extends_APPEND_NIL >>
                     simp[extends_NIL_CONS_extends,updates_cases,constspec_ok_def,is_reserved_name_def] >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
                     rw[] >> res_tac >>
                     simp[]) >>
                  fs[] >>
                  qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
                  rveq >> fs[]) >>
               reverse TOP_CASE_TAC >-
                 (goal_assum kall_tac >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  drule NewConst_no_abs_rep >>
                  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev)) >>
                  disch_then(qspecl_then[`strlit "@"`,`^select_ty`] mp_tac) >>
                  impl_tac >- rw[Abbr `ctxt`] >>
                  strip_tac >> fs[]) >>
               simp[Abbr `ctxt`,ALOOKUP_APPEND] >>
               simp[Once holBoolSyntaxTheory.mk_bool_ctxt_def,holBoolSyntaxTheory.ImpliesDef_def] >>
               simp[typeof_def,equation_def]) >>
          simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
          simp[GSYM CONJ_ASSOC] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >> simp[]) >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[] >>
             rename1 `elem ⋲ ind` >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> simp[] >>
             rw[some_def] >>
             SELECT_ELIM_TAC >> simp[] >> metis_tac[]) >>
          rw[boolean_eq_true] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          rename1 `elem ⋲ ind` >>
          dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> simp[] >>
          rw[some_def] >>
          SELECT_ELIM_TAC >> simp[] >> metis_tac[apply_abstract])
      >- ((* Axiom of infinity *)
          `NewAxiom p = (^infinity_ax)` by
            (qpat_x_assum `NewAxiom _ :: _ = _` (mp_tac o REWRITE_RULE[mk_infinity_ctxt_def]) >>
             simp[]) >>
          fs[] >> rveq >>
          rw[satisfies_t_def,satisfies_def] >>
          `ALOOKUP (type_list ctxt1) (strlit "ind") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "ONE_ONE") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "ONTO") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "!") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                    mk_select_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "?") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                    mk_select_ctxt_def]) >>
          `ALOOKUP (const_list ctxt1) (strlit "==>") = NONE`
            by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule extends_NIL_DISJOINT >>
               simp[ALOOKUP_NONE,mk_infinity_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                    mk_select_ctxt_def]) >>
          rename1 `mk_bool_ctxt ctxt3` >>
          qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins δ) γ` >>
          qmatch_asmsub_abbrev_tac `ctxt extends init_ctxt` >>
          `is_std_sig(sigof ctxt)`
            by(rpt(qpat_x_assum `is_std_sig _` mp_tac) >>
               fs[Abbr `ctxt`,mk_infinity_ctxt_def,mk_select_ctxt_def]) >>
          `is_bool_interpretation_ext (sigof ctxt) δ γ`
            by(drule_then match_mp_tac extends_is_bool_interpretation >>
               qexists_tac `ctxt3` >>
               qexists_tac `axsof (mk_bool_ctxt ctxt3)` >>
               conj_tac >-
                 (qpat_x_assum `ctxt2 extends _` mp_tac >>
                  fs[mk_infinity_ctxt_def,mk_select_ctxt_def] >>
                  strip_tac >>
                  drule extends_appends >>
                  strip_tac >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rename1 `c ++ init_ctxt` >>
                  Cases_on `c` >- fs[init_ctxt_def] >>
                  fs[] >>
                  rveq >>
                  drule(extends_append_MID |> Q.INST [`a`|->`[x;y;z;å]`] |> REWRITE_RULE [APPEND]) >>
                  impl_tac >- rw[init_ctxt_def] >>
                  strip_tac >>
                  drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
                  fs[]) >>
               `ctxt extends mk_bool_ctxt ctxt3`
                 by(qunabbrev_tac `ctxt` >>
                    rw[mk_infinity_ctxt_def,mk_select_ctxt_def] >>
                    `mk_bool_ctxt ctxt3 = [] ++ mk_bool_ctxt ctxt3` by simp[] >>
                    pop_assum(fn thm => PURE_ONCE_REWRITE_TAC[Once thm]) >>
                    PURE_REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] >>
                    PURE_REWRITE_TAC[APPEND_ASSOC] >>
                    match_mp_tac extends_NIL_APPEND_extends >>
                    drule_then(assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                    PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >> simp[] >>
                    pop_assum MP_TAC >> EVAL_TAC) >>
               drule extends_sub >>
               rw[] >>
               simp[models_def] >>
               fs[Abbr `ctxt`] >>
               fs[mk_infinity_ctxt_def,mk_select_ctxt_def]
              ) >>
          fs[is_bool_interpretation_ext_def,is_bool_interpretation_def,
             is_implies_interpretation_def,is_exists_interpretation_def,
             is_and_interpretation_def,is_not_interpretation_def
            ] >>
          simp[termsem_def] >>
          qpat_assum `!ty. ty ∈ ground_types (sigof ctxt) ==> _ = _`
            (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
          conj_tac >-
            (rw[ground_types_def,tyvars_def] >>
             fs[type_ok_def,is_std_sig_def] >>
             rw[Abbr `ctxt`] >>
             simp[ALOOKUP_APPEND] >>
             EVAL_TAC) >>
          simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool,UPDATE_def] >>
          `ext_type_frag_builtins δ Ind = ind`
            by(simp[ext_type_frag_builtins_def,Abbr `δ`] >>
               dep_rewrite.DEP_ONCE_REWRITE_TAC[CONJUNCT1 type_interpretation_of_alt] >>
               simp[] >>
               conj_asm1_tac >-
                 (simp[ground_types_def,nonbuiltin_types_def,tyvars_def,is_builtin_type_def] >>
                  reverse conj_tac >-
                    (rw[Abbr `ctxt`,type_ok_def,ALOOKUP_APPEND] >> EVAL_TAC) >>
                  fs[Abbr `ctxt`,mk_infinity_ctxt_def]) >>
               drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
               drule NewType_no_type_match >>
               disch_then(qspecl_then [`[]`,`strlit "ind"`,`0`] mp_tac) >>
               impl_tac >- (rw[Abbr `ctxt`] >> EVAL_TAC) >>
               disch_then SUBST_ALL_TAC >>
               simp[]) >>
          simp[] >>
          simp[ext_term_frag_builtins_def] >>
          (* Fish out ONTO's defining equation from the conexts ---
             this way we don't need to unfold the model construction *)
          first_assum(qspec_then `HD(^onto_conext)` mp_tac) >>
          impl_tac >-
            (qpat_x_assum `_ :: _ = _` mp_tac >>
             EVAL_TAC >> strip_tac >> rveq >> EVAL_TAC) >>
          simp[] >>
          simp[satisfies_t_def] >>
          disch_then(qspec_then `(K Ind)` mp_tac) >>
          impl_keep_tac >-
            (simp[tyvars_def] >>
             conj_asm1_tac >-
               (qpat_x_assum `_ :: _ = _` (mp_tac o EVAL_RULE) >>
                strip_tac >> rveq >>
                simp[type_ok_def,FLOOKUP_UPDATE,FLOOKUP_FUNION]) >>
             simp[ground_terms_uninst_def] >>
             qmatch_goalsub_abbrev_tac `a1 has_type _` >>
             qexists_tac `typeof a1` >>
             qunabbrev_tac `a1` >>
             simp[typeof_def] >>
             conj_tac >-
               (rpt(rw[Once has_type_cases,PULL_EXISTS])) >>
             rw[ground_types_def,tyvars_def] >>
             metis_tac[term_ok_clauses,FST]) >>
          simp[satisfies_def] >>
          drule_then drule exists_valuation >>
          disch_then(qspec_then `K Ind` mp_tac) >>
          simp[] >>
          fs[] >>
          strip_tac >> simp[valuates_frag_builtins] >>
          disch_then drule >>
          impl_tac >-
            (match_mp_tac terms_of_frag_uninst_term_ok >>
             rw[term_ok_clauses] >>
             simp[term_ok_def] >>
             fs[mk_infinity_ctxt_def,mk_select_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                FLOOKUP_FUNION,FLOOKUP_UPDATE]
             >- metis_tac[term_ok_clauses,FST]
             >- (simp[holBoolSyntaxTheory.ForallDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])
             >- (simp[holBoolSyntaxTheory.ExistsDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])) >>
          simp[termsem_def,UPDATE_def] >>
          simp[Once ext_term_frag_builtins_def] >>
          simp[ext_type_frag_builtins_def] >>
          fs[is_forall_interpretation_def] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (simp[ext_term_frag_builtins_def] >>
             conj_asm1_tac >-
               (qpat_x_assum `is_frag_interpretation _ _ _` mp_tac >>
                rw[is_frag_interpretation_def,total_fragment_def,GSYM PFORALL_THM] >>
                pop_assum(qspecl_then [`strlit"ONTO"`,`Fun (Fun Ind Ind) Bool`] mp_tac) >>
                simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
                disch_then match_mp_tac >>
                rw[ground_consts_def,nonbuiltin_constinsts_def,ground_types_def,tyvars_def,
                   builtin_consts_def,term_ok_def,FLOOKUP_FUNION] >-
                  metis_tac[term_ok_clauses,FST] >>
                fs[mk_infinity_ctxt_def] >>
                rveq >> fs[] >>
                conj_tac >- metis_tac[term_ok_clauses,FST] >>
                qexists_tac `[(Ind,Tyvar «A»);(Ind,Tyvar «B»)]` >>
                EVAL_TAC) >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[] >> rw[boolean_in_boolset]) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (conj_asm1_tac >-
               (dep_rewrite.DEP_ONCE_REWRITE_TAC[abstract_in_funspace] >>
                simp[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («!»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                conj_asm1_tac >- (simp[Abbr `ctxt`] >> fs[mk_infinity_ctxt_def] >> rveq >> fs[]) >>
                rw[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («?»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                rw[] >>
                simp[ext_term_frag_builtins_def] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                qpat_x_assum `m <: Funspace _ _` assume_tac >>
                drule_then drule in_funspace_abstract >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                rw[]) >>
             simp[boolean_in_boolset]) >>
          simp[boolean_eq_true,Once ext_term_frag_builtins_def] >>
          disch_then kall_tac >>
          (* Fish out ONE_ONE's defining equation from the conexts ---
             this way we don't need to unfold the model construction *)
          first_assum(qspec_then `HD(^one_one_conext)` mp_tac) >>
          impl_tac >-
            (qpat_x_assum `_ :: _ = _` mp_tac >>
             EVAL_TAC >> strip_tac >> rveq >> EVAL_TAC) >>
          simp[] >>
          simp[satisfies_t_def] >>
          disch_then(qspec_then `(K Ind)` mp_tac) >>
          simp[] >>
          impl_keep_tac >-
            (simp[ground_terms_uninst_def] >>
             qmatch_goalsub_abbrev_tac `a1 has_type _` >>
             qexists_tac `typeof a1` >>
             qunabbrev_tac `a1` >>
             simp[typeof_def] >>
             conj_tac >-
               (rpt(rw[Once has_type_cases,PULL_EXISTS])) >>
             rw[ground_types_def,tyvars_def] >>
             metis_tac[term_ok_clauses,FST]) >>
          simp[satisfies_def] >>
          simp[valuates_frag_builtins] >>
          disch_then drule >>
          impl_tac >-
            (match_mp_tac terms_of_frag_uninst_term_ok >>
             rw[term_ok_clauses] >>
             simp[term_ok_def] >>
             fs[mk_infinity_ctxt_def,mk_select_ctxt_def,holBoolSyntaxTheory.mk_bool_ctxt_def,
                FLOOKUP_FUNION,FLOOKUP_UPDATE]
             >- metis_tac[term_ok_clauses,FST]
             >- (simp[holBoolSyntaxTheory.ForallDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])
             >- (simp[holBoolSyntaxTheory.ForallDef_def] >>
                 conj_tac >- metis_tac[term_ok_clauses,FST] >>
                 rw[equation_def] >>
                 Q.REFINE_EXISTS_TAC `[(Tyvar _,Tyvar _)]` >>
                 rw[REV_ASSOCD_def] >>
                 rpt(pop_assum kall_tac) >> metis_tac[])
             >- (simp[holBoolSyntaxTheory.ImpliesDef_def] >>
                 rw[equation_def] >>
                 metis_tac[term_ok_clauses,FST])
            ) >>
          simp[termsem_def,UPDATE_def] >>
          simp[Once ext_term_frag_builtins_def] >>
          simp[ext_type_frag_builtins_def] >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (simp[ext_term_frag_builtins_def] >>
             conj_asm1_tac >-
               (qpat_x_assum `is_frag_interpretation _ _ _` mp_tac >>
                disch_then(strip_assume_tac o Ho_Rewrite.REWRITE_RULE[is_frag_interpretation_def,total_fragment_def,GSYM PFORALL_THM]) >>
                pop_assum(qspecl_then [`strlit"ONE_ONE"`,`Fun (Fun Ind Ind) Bool`] mp_tac) >>
                simp[ext_type_frag_builtins_Fun,ext_type_frag_builtins_Bool] >>
                disch_then match_mp_tac >>
                rw[ground_consts_def,nonbuiltin_constinsts_def,ground_types_def,tyvars_def,
                   builtin_consts_def,term_ok_def,FLOOKUP_FUNION] >-
                  metis_tac[term_ok_clauses,FST] >>
                fs[mk_infinity_ctxt_def] >>
                rveq >> fs[] >>
                conj_tac >- metis_tac[term_ok_clauses,FST] >>
                qexists_tac `[(Ind,Tyvar «A»);(Ind,Tyvar «B»)]` >>
                EVAL_TAC) >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[] >> rw[boolean_in_boolset]) >>
          dep_rewrite.DEP_ONCE_REWRITE_TAC[apply_abstract] >>
          simp[] >>
          conj_asm1_tac >-
            (conj_asm1_tac >-
               (dep_rewrite.DEP_ONCE_REWRITE_TAC[abstract_in_funspace] >>
                simp[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («!»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                conj_asm1_tac >- (simp[Abbr `ctxt`] >> fs[mk_infinity_ctxt_def] >> rveq >> fs[]) >>
                rw[] >>
                qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («?»,_) = _`
                  (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
                simp[ground_types_def] >>
                rw[] >>
                simp[ext_term_frag_builtins_def] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                rw[] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                qpat_x_assum `m <: Funspace _ _` assume_tac >>
                drule_then drule in_funspace_abstract >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> rw[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
                simp[boolean_in_boolset]) >>
             simp[boolean_in_boolset]) >>
          simp[boolean_eq_true,Once ext_term_frag_builtins_def] >>
          disch_then kall_tac >>
          qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («!»,_) = _`
            (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
          simp[ground_types_def] >>
          conj_asm1_tac >- (simp[Abbr `ctxt`] >> fs[mk_infinity_ctxt_def] >> rveq >> fs[]) >>
          rw[] >>
          qpat_assum `∀ty. _ => ext_term_frag_builtins _ _ («?»,_) = _`
            (fn thm => dep_rewrite.DEP_ONCE_REWRITE_TAC[thm]) >>
          simp[ground_types_def] >>
          simp[ext_term_frag_builtins_def] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             conj_tac >-
               (rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                qpat_x_assum `m <: Funspace _ _` assume_tac >>
                drule_then drule in_funspace_abstract >>
                strip_tac >> simp[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                simp[boolean_in_boolset] >>
                rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                simp[boolean_in_boolset]) >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qpat_x_assum `m <: Funspace _ _` assume_tac >>
             drule_then drule in_funspace_abstract >>
             strip_tac >> simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[]) >>
          qpat_x_assum `is_infinite _ _` mp_tac >>
          simp[is_infinite_def] >>
          simp[INFINITE_INJ_NOT_SURJ] >>
          strip_tac >>
          rename1 `INJ f` >>
          qexists_tac`Abstract (ext_type_frag_builtins δ Ind) (ext_type_frag_builtins δ Ind) f` >>
          fs[] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >> simp[] >>
             ntac 2 (pop_assum mp_tac) >> simp[INJ_DEF]) >>
          simp[holds_def] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
             simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          simp[] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          conj_tac >-
            (rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
             simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             conj_tac >-
               (rw[] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
                simp[boolean_in_boolset] >>
                dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
                simp[boolean_in_boolset] >>
                conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
                simp[] >>
                dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
                simp[boolean_in_boolset]) >>
             rw[boolean_eq_true] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             conj_asm1_tac >- (qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
             simp[] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_boolrel_rw] >>
             simp[boolean_in_boolset] >>
             simp[boolean_eq_true] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset,boolean_eq_true] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
             simp[boolean_in_boolset,boolean_eq_true] >>
             rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          simp[] >>
          qpat_x_assum`¬(SURJ f X Y)`mp_tac >>
          simp[SURJ_DEF] >>
          strip_tac >-
            (qpat_x_assum`INJ f X Y`mp_tac >>
             simp[INJ_DEF] >>
             PROVE_TAC[]) >>
          rename1 `w <: ext_type_frag_builtins _ Ind` >>
          qexists_tac `w` >>
          simp[] >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          fs[GSYM IMP_DISJ_THM] >>
          dep_rewrite.DEP_REWRITE_TAC[abstract_in_funspace] >>
          simp[boolean_in_boolset,boolean_eq_true] >>
          conj_asm1_tac >-
            (rw[] >>
             dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
             simp[boolean_in_boolset] >>
             qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF]) >>
          ntac 2 strip_tac >>
          dep_rewrite.DEP_REWRITE_TAC[apply_abstract] >>
          simp[boolean_in_boolset] >>
          simp[boolean_def,true_neq_false] >>
          qhdtm_x_assum `INJ` mp_tac >> simp[INJ_DEF])
      )
  >- ((* conexts of new axiom (vacuous) *)
      first_x_assum match_mp_tac >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[conexts_of_upd_def])
  >- ((* NewConst *)
      fs[conexts_of_upd_def])
  >- ((* NewConst *)
      fs[conexts_of_upd_def])
  >- ((* ConstSpec *)
      fs[conexts_of_upd_def] >>
      rw[satisfies_t_def,satisfies_def] >>
      `!name. MEM name (MAP FST eqs) ==> ~MEM name (MAP FST (const_list ctxt1))`
        by(rw[] >>
           drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           fs[DISJOINT_DEF,INTER_DEF,FUN_EQ_THM,GSYM IMP_DISJ_THM,map_fst] >>
           TRY(rename1 `ConstSpec F` >> metis_tac[]) >>
           fs[constspec_ok_def] >>
           qpat_x_assum `MEM _ (MAP FST _)` (strip_assume_tac o REWRITE_RULE[MEM_MAP]) >>
           rveq >>
           rename1 `MEM pp eqs` >>
           Cases_on `pp` >>
           rename1 `MEM (name,typ) eqs` >>
           res_tac >>
           qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
           rw[IMP_CONJ_THM,FORALL_AND_THM]) >>
      TRY(rename1 `ConstSpec T` >> (* overloads case *)
          drule proves_theory_mono >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                                   `tyenv`,`tmenv`] mp_tac) >>
          simp[] >>
          MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
          impl_tac >-
            (rw[] >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >>
                 drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                 drule extends_NIL_DISJOINT >>
                 simp[] >> NO_TAC) >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
                drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                drule extends_NIL_DISJOINT >>
                simp[] >> NO_TAC) >>
             qhdtm_x_assum `theory_ok` mp_tac >>
             rw[theory_ok_def]) >>
          strip_tac >>
          drule_then assume_tac proves_term_ok >>
          fs[] >>
          drule_then assume_tac term_ok_welltyped >>
          drule termsem_VSUBST >>
          disch_then(qspec_then `^mem` mp_tac) >>
          qmatch_goalsub_abbrev_tac `VSUBST ilist` >>
          disch_then(qspec_then `ilist` mp_tac) >>
          impl_tac >-
            (rw[Abbr `ilist`,MEM_MAP,ELIM_UNCURRY] >> metis_tac[has_type_rules]) >>
          simp[] >>
          disch_then kall_tac >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          `models (type_interpretation_of ind (ctxt1 ++ ConstSpec T eqs prop::ctxt2)) (UNCURRY (term_interpretation_of ind (ctxt1 ++ ConstSpec T eqs prop::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
            by(rw[models_def]) >>
          drule_then drule proves_sound >>
          simp[entails_def] >>
          strip_tac >>
          first_x_assum drule >>
          simp[satisfies_t_def] >>
          ntac 2 (disch_then drule) >>
          impl_keep_tac >-
            (rw[ground_terms_uninst_def,EVERY_MEM,MEM_MAP] >>
             qexists_tac `Bool` >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             res_tac >>
             fs[ELIM_UNCURRY] >>
             simp[ground_types_def,tyvars_def] >>
             imp_res_tac theory_ok_sig >>
             metis_tac[FST,term_ok_clauses]) >>
          simp[satisfies_def] >>
          fs[valuates_frag_builtins] >>
          qmatch_goalsub_abbrev_tac `termsem _ _ vv sigma prop = True` >>
          disch_then(qspec_then `vv` mp_tac) >>
          impl_tac >-
            (conj_asm1_tac >-
               (rw[valuates_frag_def,Abbr `vv`] >>
                simp[MAP_REVERSE,APPLY_UPDATE_LIST_ALOOKUP,ALOOKUP_MAP] >>
                TOP_CASE_TAC >- metis_tac[valuates_frag_def] >>
                fs[ALOOKUP_SOME_EQ] >>
                fs[MAP_EQ_APPEND] >> rveq >>
                pairarg_tac >> fs[] >> rveq >>
                qpat_x_assum `Abbrev (_ ++ _ ++ _ = _)` (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                fs[MAP_EQ_APPEND |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
                pairarg_tac >> fs[] >> rveq >>
                fs[] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] >>
                rename1 `Const name` >>
                drule_then(drule_then drule) termsem_in_type_ext2 >>
                disch_then(qspecl_then [`v`,`sigma`,`Const name (typeof t)`] mp_tac) >>
                impl_tac >-
                  (conj_tac >-
                     (match_mp_tac terms_of_frag_uninst_term_ok >>
                      simp[term_ok_def] >>
                      rw[Abbr `tmenv`,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
                      fs[DISJ_IMP_THM,FORALL_AND_THM] >>
                      fs[GSYM ALOOKUP_NONE] >>
                      fs[constspec_ok_def,ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,ALOOKUP_MAP] >>
                      reverse conj_tac >- metis_tac[] >>
                      rfs[term_ok_clauses]) >>
                   simp[VFREE_IN_def]) >>
                simp[typeof_def] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]) >>
             conj_asm1_tac >- (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             conj_asm1_tac >-
               (rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
                fs[EVERY_MEM,MEM_MAP] >> res_tac >> fs[] >>
                match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
             drule_then (drule_then(drule_then drule)) termsem_ext_equation >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             first_x_assum(drule_then strip_assume_tac) >>
             fs[] >>
             drule_then drule terms_of_frag_uninst_equationE >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[welltyped_equation]) >>
             disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS) >>
             disch_then dxrule >>
             disch_then dxrule >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[term_ok_clauses]) >>
             simp[termsem_ext_def] >>
             disch_then kall_tac >>
             simp[boolean_eq_true] >>
             simp[termsem_def,Abbr `vv`] >>
             simp[APPLY_UPDATE_LIST_ALOOKUP,Abbr `ilist`,MAP_REVERSE] >>
             simp[GSYM MAP_MAP_o] >>
             qmatch_goalsub_abbrev_tac `ALOOKUP (MAP _ ll)` >>
             `EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ll)`
               by(fs[Abbr`ll`,EVERY_MEM,MEM_MAP,PULL_EXISTS] >> Cases >> rw[]) >>
             simp[ALOOKUP_MAP_dest_var] >>
             simp[Abbr `ll`,MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
             drule_then(drule_then (fn thm => simp[thm])) orth_ctxt_ALOOKUP_eqs >>
             simp[termsem_def] >>
             `s <> strlit "="`
               by(fs[constspec_ok_def,is_builtin_name_def,is_reserved_name_def] >> metis_tac[]) >>
             simp[SimpL``$=``,ext_term_frag_builtins_def] >>
             qmatch_goalsub_abbrev_tac `type_interpretation_of ind ctxt` >>
             `is_frag_interpretation (total_fragment (sigof ctxt))
                (type_interpretation_of ind ctxt)
                (UNCURRY (term_interpretation_of ind ctxt))`
               by(fs[Abbr `ctxt`]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ ground_consts (sigof ctxt)`
               by(rw[Abbr`ctxt`] >>
                  simp[ground_consts_def] >>
                  conj_tac >-
                    (rw[ground_types_def,tyvars_TYPE_SUBSTf_eq_NIL] >>
                     match_mp_tac type_ok_TYPE_SUBSTf >>
                     simp[] >>
                     fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >> fs[] >>
                     rfs[term_ok_clauses]) >>
                  fs[constspec_ok_def] >> res_tac >>
                  rw[term_ok_def,Abbr`tmenv`,FLOOKUP_FUNION] >>
                  reverse(Cases_on `ALOOKUP (const_list ctxt1) s`) >-
                    (imp_res_tac ALOOKUP_MEM >>
                     res_tac >> metis_tac[FST]) >>
                  simp[] >>
                  reverse conj_tac >-
                    (metis_tac[TYPE_SUBSTf_TYPE_SUBST_compose,TYPE_SUBSTf_eq_TYPE_SUBST]) >>
                  match_mp_tac type_ok_TYPE_SUBSTf >>
                  simp[] >>
                  fs[] >>
                  rfs[term_ok_clauses]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ nonbuiltin_constinsts`
               by(rw[nonbuiltin_constinsts_def,builtin_consts_def]) >>
             Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
             simp[type_interpretation_of_alt] >>
             drule orth_ctxt_FILTER_ctxt >>
             disch_then(drule o ONCE_REWRITE_RULE[CONJ_SYM]) >>
             disch_then(qspecl_then [`sigma`,`prop`,`T`] mp_tac) >>
             impl_tac >- rw[Abbr`ctxt`] >>
             strip_tac >> simp[] >> pop_assum kall_tac >>
             TOP_CASE_TAC >-
               (goal_assum kall_tac >>
                Q.SUBGOAL_THEN `is_instance (typeof t) (TYPE_SUBSTf sigma (typeof t))` assume_tac >-
                  metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
                metis_tac[instance_subst_completeness,IS_SOME_DEF]) >>
             rename1 `instance_subst _ _ _ = SOME result` >>
             Cases_on `result` >>
             rename1 `instance_subst _ _ _ = SOME(sigma',e)` >>
             drule_then (assume_tac o GSYM) instance_subst_soundness >>
             simp[ELIM_UNCURRY] >>
             qmatch_goalsub_abbrev_tac `termsem a1 a2 a3 a4 t = termsem _ _ a5 _ _` >>
             `termsem a1 a2 a3 a4 t = termsem a1 a2 a5 a4 t`
               by(MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                  match_mp_tac termsem_frees >>
                  res_tac >> fs[CLOSED_def] >>
                  rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             pop_assum SUBST_ALL_TAC >>
             match_mp_tac termsem_subst >>
             conj_tac >-
               (MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                res_tac >> fs[] >> rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
             fs[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
             metis_tac[SND]) >>
          simp[]) >>
      TRY(rename1 `ConstSpec F` >> (* fresh constants case *)
          drule proves_theory_mono >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                                   `tyenv`,`tmenv`] mp_tac) >>
          simp[] >>
          MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
          impl_tac >-
            (rw[] >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >>
                 drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                 drule extends_NIL_DISJOINT >>
                 simp[] >> NO_TAC) >>
             TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
                 drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                 drule extends_NIL_DISJOINT >>
                 simp[] >- metis_tac[DISJOINT_SYM] >>
                 disch_then kall_tac >>
                 fs[constspec_ok_def,map_fst] >>
                 fs[DISJOINT_DEF,FUN_EQ_THM] >> metis_tac[]) >>
             qhdtm_x_assum `theory_ok` mp_tac >>
             rw[theory_ok_def]) >>
          strip_tac >>
          drule_then assume_tac proves_term_ok >>
          fs[] >>
          drule_then assume_tac term_ok_welltyped >>
          drule termsem_VSUBST >>
          disch_then(qspec_then `^mem` mp_tac) >>
          qmatch_goalsub_abbrev_tac `VSUBST ilist` >>
          disch_then(qspec_then `ilist` mp_tac) >>
          impl_tac >-
            (rw[Abbr `ilist`,MEM_MAP,ELIM_UNCURRY] >> metis_tac[has_type_rules]) >>
          simp[] >>
          disch_then kall_tac >>
          qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
          `models (type_interpretation_of ind (ctxt1 ++ ConstSpec F eqs prop::ctxt2)) (UNCURRY (term_interpretation_of ind (ctxt1 ++ ConstSpec F eqs prop::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
            by(rw[models_def]) >>
          drule_then drule proves_sound >>
          simp[entails_def] >>
          strip_tac >>
          first_x_assum drule >>
          simp[satisfies_t_def] >>
          ntac 2 (disch_then drule) >>
          impl_keep_tac >-
            (rw[ground_terms_uninst_def,EVERY_MEM,MEM_MAP] >>
             qexists_tac `Bool` >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             res_tac >>
             fs[ELIM_UNCURRY] >>
             simp[ground_types_def,tyvars_def] >>
             imp_res_tac theory_ok_sig >>
             metis_tac[FST,term_ok_clauses]) >>
          simp[satisfies_def] >>
          fs[valuates_frag_builtins] >>
          qmatch_goalsub_abbrev_tac `termsem _ _ vv sigma prop = True` >>
          disch_then(qspec_then `vv` mp_tac) >>
          impl_tac >-
            (conj_asm1_tac >-
               (rw[valuates_frag_def,Abbr `vv`] >>
                simp[MAP_REVERSE,APPLY_UPDATE_LIST_ALOOKUP,ALOOKUP_MAP] >>
                TOP_CASE_TAC >- metis_tac[valuates_frag_def] >>
                fs[ALOOKUP_SOME_EQ] >>
                fs[MAP_EQ_APPEND] >> rveq >>
                pairarg_tac >> fs[] >> rveq >>
                qpat_x_assum `Abbrev (_ ++ _ ++ _ = _)` (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                fs[MAP_EQ_APPEND |> CONV_RULE(LHS_CONV SYM_CONV)] >> rveq >> fs[] >>
                pairarg_tac >> fs[] >> rveq >>
                fs[] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] >>
                rename1 `Const name` >>
                drule_then(drule_then drule) termsem_in_type_ext2 >>
                disch_then(qspecl_then [`v`,`sigma`,`Const name (typeof t)`] mp_tac) >>
                impl_tac >-
                  (conj_tac >-
                     (match_mp_tac terms_of_frag_uninst_term_ok >>
                      simp[term_ok_def] >>
                      rw[Abbr `tmenv`,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
                      fs[DISJ_IMP_THM,FORALL_AND_THM] >>
                      fs[GSYM ALOOKUP_NONE] >>
                      fs[constspec_ok_def,ALL_DISTINCT_APPEND,DISJ_IMP_THM,FORALL_AND_THM,ALOOKUP_MAP] >>
                      fs[GSYM ALOOKUP_NONE] >>
                      rfs[term_ok_clauses]) >>
                   simp[VFREE_IN_def]) >>
                simp[typeof_def] >>
                SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]) >>
             conj_asm1_tac >- (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             conj_asm1_tac >-
               (rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
                fs[EVERY_MEM,MEM_MAP] >> res_tac >> fs[] >>
                match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
             rw[EVERY_MEM,MEM_MAP] >> pairarg_tac >> rveq >> fs[] >>
             drule_then (drule_then(drule_then drule)) termsem_ext_equation >>
             fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             first_x_assum(drule_then strip_assume_tac) >>
             fs[] >>
             drule_then drule terms_of_frag_uninst_equationE >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[welltyped_equation]) >>
             disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS) >>
             disch_then dxrule >>
             disch_then dxrule >>
             impl_tac >-
               (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >>
                fs[term_ok_clauses]) >>
             simp[termsem_ext_def] >>
             disch_then kall_tac >>
             simp[boolean_eq_true] >>
             simp[termsem_def,Abbr `vv`] >>
             simp[APPLY_UPDATE_LIST_ALOOKUP,Abbr `ilist`,MAP_REVERSE] >>
             simp[GSYM MAP_MAP_o] >>
             qmatch_goalsub_abbrev_tac `ALOOKUP (MAP _ ll)` >>
             `EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ll)`
               by(fs[Abbr`ll`,EVERY_MEM,MEM_MAP,PULL_EXISTS] >> Cases >> rw[]) >>
             simp[ALOOKUP_MAP_dest_var] >>
             simp[Abbr `ll`,MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
             qmatch_goalsub_abbrev_tac `ALOOKUP ll` >>
             `ALL_DISTINCT(MAP FST ll)`
               by(rw[Abbr `ll`,ALL_DISTINCT_MAP] >>
                  fs[constspec_ok_def] >>
                  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
                  rpt(pop_assum kall_tac) >>
                  Induct_on `eqs` >- rw[] >>
                  Cases >> rw[] >>
                  rw[MEM_MAP,GSYM IMP_DISJ_THM] >>
                  Cases_on `x` >> fs[] >>
                  rveq >>
                  fs[MEM_MAP,GSYM IMP_DISJ_THM]) >>
             `MEM (Var s (typeof t),Const s (typeof t)) ll`
               by(rw[Abbr `ll`,MEM_MAP,PULL_EXISTS] >> metis_tac[FST,SND]) >>
             drule_then drule ALOOKUP_ALL_DISTINCT_MEM >>
             simp[] >> disch_then kall_tac >>
             simp[termsem_def] >>
             `s <> strlit "="`
               by(fs[constspec_ok_def] >>
                  qpat_x_assum `ctxt2 extends init_ctxt` assume_tac >>
                  drule_then strip_assume_tac extends_appends >>
                  rveq >> fs[init_ctxt_def] >>
                  fs[MEM_MAP,PULL_EXISTS] >> res_tac >>
                  fs[]) >>
             simp[SimpL``$=``,ext_term_frag_builtins_def] >>
             qmatch_goalsub_abbrev_tac `type_interpretation_of ind ctxt` >>
             `is_frag_interpretation (total_fragment (sigof ctxt))
                (type_interpretation_of ind ctxt)
                (UNCURRY (term_interpretation_of ind ctxt))`
               by(fs[Abbr `ctxt`]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ ground_consts (sigof ctxt)`
               by(rw[Abbr`ctxt`] >>
                  simp[ground_consts_def] >>
                  conj_tac >-
                    (rw[ground_types_def,tyvars_TYPE_SUBSTf_eq_NIL] >>
                     match_mp_tac type_ok_TYPE_SUBSTf >>
                     simp[] >>
                     fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >> fs[] >>
                     rfs[term_ok_clauses]) >>
                  rw[term_ok_def,Abbr`tmenv`,FLOOKUP_FUNION] >>
                  reverse(Cases_on `ALOOKUP (const_list ctxt1) s`) >-
                    (imp_res_tac ALOOKUP_MEM >>
                     res_tac >> metis_tac[FST]) >>
                  simp[] >>
                  simp[ALOOKUP_MAP] >>
                  fs[constspec_ok_def] >>
                  dxrule_then dxrule ALOOKUP_ALL_DISTINCT_MEM >>
                  drule_then drule ALOOKUP_ALL_DISTINCT_MEM >>
                  simp[] >> ntac 2 (disch_then kall_tac) >>
                  conj_tac >-
                    (match_mp_tac type_ok_TYPE_SUBSTf >>
                     simp[] >>
                     fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] >> res_tac >> fs[] >>
                     rfs[term_ok_clauses]) >>
                  metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST]) >>
             `(s,TYPE_SUBSTf sigma (typeof t)) ∈ nonbuiltin_constinsts`
               by(rw[nonbuiltin_constinsts_def,builtin_consts_def]) >>
             Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
             simp[type_interpretation_of_alt] >>
             simp[Abbr `ctxt`,FILTER_APPEND] >>
             qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
             `FILTER fff lll = []`
               by(fs[Abbr `fff`,Abbr `lll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                  strip_tac >>
                  disch_then(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  rename1` defn_matches _ _ aaa` >> Cases_on `aaa` >> fs[defn_matches_def] >>
                  fs[FILTER_EQ_NIL,EVERY_MEM] >>
                  FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  dxrule_then assume_tac extends_APPEND_NIL >>
                  fs[] >>
                  dxrule_then assume_tac extends_NIL_CONS_updates >>
                  Cases >> strip_tac >>
                  fs[updates_cases,constspec_ok_def] >>
                  reverse(Cases_on `b`) >-
                    (fs[MEM_MAP,PULL_EXISTS] >>
                     first_x_assum drule >>
                     qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                     first_x_assum drule >>
                     rpt strip_tac >>
                     spose_not_then strip_assume_tac >>
                     rveq >>
                     first_x_assum(qspec_then `(q,t)` mp_tac) >>
                     simp[]) >>
                  fs[] >>
                  first_x_assum drule >>
                  strip_tac
                  >- (qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                      rveq >>
                      qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                      first_x_assum drule >>
                      rpt strip_tac >>
                      fs[] >> metis_tac[FST]) >>
                  qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                  rveq >> fs[MEM_MAP,PULL_EXISTS] >>
                  qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                  first_x_assum drule >>
                  rpt strip_tac >>
                  fs[] >> metis_tac[FST]) >>
             pop_assum SUBST_ALL_TAC >>
             qunabbrev_tac `lll` >>
             qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
             `FILTER fff lll = []`
               by(fs[Abbr `fff`,Abbr `lll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                  strip_tac >>
                  disch_then(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  rename1` defn_matches _ _ aaa` >> Cases_on `aaa` >> fs[defn_matches_def] >>
                  fs[FILTER_EQ_NIL,EVERY_MEM] >>
                  fs[constspec_ok_def] >>
                  Cases >> disch_then(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  reverse(Cases_on `b`) >-
                    (fs[MEM_MAP,PULL_EXISTS] >>
                     qpat_x_assum `!y. MEM y eqs ==> !y'. _` assume_tac >>
                     first_x_assum drule >>
                     rpt strip_tac >>
                     fs[] >> metis_tac[FST]) >>
                  fs[] >>
                  qpat_x_assum `_ ++ ConstSpec T _ _::_ extends _` assume_tac >>
                  drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
                  dxrule_then assume_tac extends_APPEND_NIL >>
                  fs[] >>
                  dxrule_then assume_tac extends_NIL_CONS_updates >>
                  fs[updates_cases,constspec_ok_def,DISJ_IMP_THM,FORALL_AND_THM] >>
                  qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                  rveq >> fs[] >>
                  metis_tac[MEM_MAP,FST]) >>
             pop_assum SUBST_ALL_TAC >>
             simp[] >>
             MAP_EVERY qunabbrev_tac [`fff`,`lll`] >>
             simp[defn_matches_def] >>
             qmatch_goalsub_abbrev_tac `FILTER fff lll` >>
             `FILTER fff lll = [(s,t)]`
               by(MAP_EVERY qunabbrev_tac [`fff`,`lll`] >>
                  qpat_x_assum `MEM _ eqs` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> rveq >>
                  fs[FILTER_APPEND] >>
                  reverse IF_CASES_TAC >- metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
                  simp[APPEND_EQ_CONS] >>
                  fs[constspec_ok_def,ALL_DISTINCT_APPEND,IMP_CONJ_THM,FORALL_AND_THM,DISJ_IMP_THM] >>
                  fs[FILTER_EQ_NIL,EVERY_MEM] >>
                  conj_tac >> Cases >> fs[MEM_MAP,PULL_EXISTS] >> metis_tac[FST]) >>
             pop_assum SUBST_ALL_TAC >> simp[] >>
             fs[Abbr `fff`,Abbr `lll`] >>
             TOP_CASE_TAC >-
               (goal_assum kall_tac >>
                Q.SUBGOAL_THEN `is_instance (typeof t) (TYPE_SUBSTf sigma (typeof t))` assume_tac >-
                  metis_tac[TYPE_SUBSTf_eq_TYPE_SUBST] >>
                metis_tac[instance_subst_completeness,IS_SOME_DEF]) >>
             rename1 `instance_subst _ _ _ = SOME result` >>
             Cases_on `result` >>
             rename1 `instance_subst _ _ _ = SOME(sigma',e)` >>
             drule_then (assume_tac o GSYM) instance_subst_soundness >>
             simp[ELIM_UNCURRY] >>
             qmatch_goalsub_abbrev_tac `termsem a1 a2 a3 a4 t = termsem _ _ a5 _ _` >>
             `termsem a1 a2 a3 a4 t = termsem a1 a2 a5 a4 t`
               by(MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                  match_mp_tac termsem_frees >>
                  res_tac >> fs[CLOSED_def] >>
                  rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             pop_assum SUBST_ALL_TAC >>
             match_mp_tac termsem_subst >>
             conj_tac >-
               (MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
                res_tac >> fs[] >> rfs[term_ok_equation] >> imp_res_tac term_ok_welltyped) >>
             MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`,`a5`] >>
             fs[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
             metis_tac[SND]) >>
            simp[])
     )
  >- ((* NewType *)
      fs[conexts_of_upd_def])
  >- ((* TypeDefn *)
      rename1 `elem ⋲ ind` >>
      fs[conexts_of_upd_def] >>
      rw[satisfies_t_def,satisfies_def,termsem_def] >>
      `~MEM name (MAP FST (type_list ctxt1))`
        by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `~MEM abs (MAP FST (const_list ctxt1))`
        by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `~MEM rep (MAP FST (const_list ctxt1))`
        by(drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `ALOOKUP (type_list ctxt1) name = NONE`
        by rw[ALOOKUP_NONE] >>
       `ALOOKUP (const_list ctxt1) abs = NONE`
        by rw[ALOOKUP_NONE] >>
      `ALOOKUP (const_list ctxt1) rep = NONE`
        by rw[ALOOKUP_NONE]
      >- ((* First abs/rep axiom *)
       drule proves_theory_mono >>
       qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
       disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                               `tyenv`,`tmenv`] mp_tac) >>
       simp[] >>
       MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
       impl_tac >-
         (rw[] >>
          TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
              drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
              drule extends_NIL_DISJOINT >>
              simp[] >> NO_TAC) >>
          qhdtm_x_assum `theory_ok` mp_tac >>
          rw[theory_ok_def]) >>
      strip_tac >>
      drule_then drule (MP_CANON termsem_ext_equation) >>
      disch_then drule >>
      fs[valuates_frag_builtins] >>
      disch_then drule >>
      drule_then drule terms_of_frag_uninst_equationE >>
      impl_keep_tac >- rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
      disch_then (MAP_EVERY assume_tac o rev o CONJUNCTS) >>
      ntac 2 (disch_then dxrule) >>
      impl_keep_tac >-
        (rw[term_ok_clauses] >> rw[term_ok_def] >>
         qpat_assum `is_std_sig(FUNION _ _,_)` (strip_assume_tac o REWRITE_RULE[is_std_sig_def]) >>
         rw[type_ok_def,EVERY_MEM,MEM_MAP,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
         rw[type_ok_def] >>
         drule proves_term_ok >>
         rw[EVERY_MEM,term_ok_def] >> rw[] >>
         drule_then drule term_ok_type_ok >> rw[]) >>
      simp[termsem_ext_def] >>
      disch_then kall_tac >>
      rw[boolean_eq_true] >>
      rw[termsem_def] >>
      `~MEM (strlit "=") (MAP FST (const_list ctxt1))`
        by(drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def] >>
           rveq >> fs[] >>
           fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           drule_then(assume_tac o C MATCH_MP (REWRITE_RULE[init_ctxt_def] init_ctxt_extends))
                     extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `MEM (strlit "=") (MAP FST (const_list ctxt2))`
        by(imp_res_tac extends_appends >> rw[init_ctxt_def]) >>
      `abs <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      `rep <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      simp[ext_term_frag_builtins_def] >>
      qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
      `models (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
              (UNCURRY (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              ((tyenv,tmenv),axsof ctxt2)`
        by(rw[models_def]) >>
      drule_then drule proves_sound >>
      simp[entails_def] >>
      strip_tac >>
      first_x_assum drule >>
      simp[satisfies_t_def] >>
      ntac 2 (disch_then drule) >>
      impl_keep_tac >-
        (rw[ground_terms_uninst_def] >>
         goal_assum drule >>
         rw[ground_types_def,tyvars_def] >>
         imp_res_tac term_ok_type_ok >>
         qpat_x_assum `is_std_sig (tyenv,tmenv)` mp_tac >>
         rw[is_std_sig_def,type_ok_def]) >>
      simp[satisfies_def] >>
      simp[valuates_frag_builtins] >>
      disch_then drule >>
      impl_tac >-
        (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
      simp[termsem_def] >> strip_tac >>
      `termsem
           (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (ext_term_frag_builtins
              (ext_type_frag_builtins
                 (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              (UNCURRY
                 (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))))
           v sigma witness ⋲
         (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (TYPE_SUBSTf sigma (typeof witness))
      `
        by(match_mp_tac termsem_in_type_ext2 >>
           rpt(goal_assum drule) >>
           conj_tac >-
             (match_mp_tac terms_of_frag_uninst_term_ok >>
              simp[] >>
              drule proves_term_ok >>
              rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
           rpt strip_tac >>
           qpat_x_assum `valuates_frag _ _ _ _` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then match_mp_tac >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           goal_assum drule >>
           goal_assum drule >>
           match_mp_tac terms_of_frag_uninst_term_ok >>
           simp[] >>
           drule proves_term_ok >> rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ abs abstype` >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ rep reptype` >>
      `(abs,abstype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(fs[Abbr `abstype`,ground_consts_def,ground_types_def] >>
           conj_tac >-
             (simp[tyvars_def,LIST_UNION_EQ_NIL,tyvars_TYPE_SUBSTf_eq_NIL] >>
              match_mp_tac FOLDR_LIST_UNION_empty >>
              rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
           conj_asm1_tac >-
             (qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
              `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
              pop_assum SUBST_ALL_TAC >>
              simp[term_ok_clauses] >>
              conj_tac >-
                (match_mp_tac type_ok_TYPE_SUBSTf >> simp[] >>
                 qpat_x_assum `term_ok _ (Comb _ _)` mp_tac >>
                 simp[term_ok_clauses] >>
                 rpt strip_tac >>
                 simp[] >> metis_tac[term_ok_type_ok,FST]) >>
              simp[type_ok_def,EVERY_MAP,MEM_MAP,PULL_EXISTS] >>
              rw[Abbr `tyenv`,FLOOKUP_FUNION,FLOOKUP_UPDATE]) >>
           rw[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           qexists_tac `(MAP (λx. (sigma x,Tyvar x)) (tvars pred))` >>
           simp[TYPE_SUBST_eq_TYPE_SUBSTf,MAP_EQ_f,MEM_MAP,PULL_EXISTS,
                REV_ASSOCD_ALOOKUP,MAP_MAP_o,o_DEF,ALOOKUP_Tyvar,ALOOKUP_MAPf] >>
           simp[TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
           rfs[term_ok_clauses] >>
           rpt strip_tac >>
           IF_CASES_TAC >> simp[] >>
           fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
           drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
           drule_then (mp_tac o REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) tyvars_typeof_subset_tvars >>
           disch_then drule >>
           simp[tyvars_def]) >>
      `(abs,abstype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `(rep,reptype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qpat_x_assum `(abs,abstype) ∈ ground_consts _` mp_tac >>
           fs[Abbr `reptype`,Abbr `abstype`,ground_consts_def,ground_types_def] >>
           qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
           `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
           pop_assum SUBST_ALL_TAC >>
           simp[term_ok_clauses] >>
           simp[tyvars_def,LIST_UNION_EQ_NIL] >>
           rw[term_ok_def,term_ok_clauses,FLOOKUP_FUNION,FLOOKUP_UPDATE,MAP_EQ_f] >>
           fs[type_ok_def] >>
           metis_tac[]) >>
      `(rep,reptype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `is_frag_interpretation (total_fragment (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
          (type_interpretation_of ind
             (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
          (UNCURRY
             (term_interpretation_of ind
                (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))`
        by(qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[Abbr `tyenv`,Abbr `tmenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
      MAP_EVERY qunabbrev_tac [`abstype`,`reptype`] >>
      Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
      simp[type_interpretation_of_alt] >>
      qpat_x_assum `inhabited ind` kall_tac >>
      simp[FILTER_APPEND] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
      Cases_on `[] ≠
              defn_matches rep
                (Fun
                   (Tyapp name
                      (MAP (λa. TYPE_SUBSTf sigma a)
                         (MAP Tyvar
                            (MAP implode
                               (STRING_SORT (MAP explode (tvars pred)))))))
                   (TYPE_SUBSTf sigma (domain (typeof pred))))
                (TypeDefn name pred abs rep)` >-
        (fs[defn_matches_def]) >>
      simp[] >>
      ntac 2 (pop_assum kall_tac) >>
      ntac 2 (
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             fs[] >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`] >>
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac (extends_APPEND_NIL |> Q.SPEC `[e]` |> REWRITE_RULE[APPEND]) >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[])
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`]) >>
      simp[] >>
      simp[mllistTheory.mapPartial_def,mapPartial_APPEND] >>
      rpt
        (qmatch_goalsub_abbrev_tac `mapPartial a1 a2` >>
        `mapPartial a1 a2 = []`
          by(rw[Abbr `a1`,Abbr `a2`,mllistTheory.mapPartial_thm,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,
                PULL_EXISTS] >>
             simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
             ntac 3 (PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
             fs[pair_case_eq] >>
             PURE_FULL_CASE_TAC >> fs[] >> rveq >>
             qpat_x_assum `MEM (TypeDefn _ _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             fs[updates_cases]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`a1`,`a2`]) >>
      simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
      reverse IF_CASES_TAC >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> simp[] >>
         simp[TYPE_SUBSTf_eq_TYPE_SUBST] >>
         rw[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
         qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tvars pred)` >>
         conj_tac >-
           (rw[TYPE_SUBST_tyvars,REV_ASSOCD_ALOOKUP] >>
            ntac 2 TOP_CASE_TAC >>
            fs[ALOOKUP_NONE,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
            imp_res_tac ALOOKUP_MEM >>
            fs[MEM_MAP] >> rveq >> pairarg_tac >> rveq >> fs[] >>
            rveq >> fs[] >> rveq >> fs[] >>
            rfs[term_ok_def] >> rfs[] >> fs[welltyped_def] >>
            imp_res_tac WELLTYPED_LEMMA >> rveq >>
            `MEM x (tyvars(typeof pred))` by simp[tyvars_def] >>
            drule_then drule (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
            simp[]) >>
         strip_tac >>
         simp[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP,MAP_MAP_o,o_DEF,tyvars_def] >>
         simp[ALOOKUP_Tyvar,ALOOKUP_MAPf]) >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `if a1 then SOME _ else NONE` >>
      reverse(first_assum (fn thm =>
                              qunabbrev_tac `a1` >>
                              Cases_on [ANTIQUOTE (rhs(rand(concl thm)))])) >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> pop_assum kall_tac >> simp[] >>
         simp[TYPE_SUBSTf_eq_TYPE_SUBST] >>
         rw[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
         qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tvars pred)` >>
         reverse conj_tac >-
           (rw[TYPE_SUBST_tyvars,REV_ASSOCD_ALOOKUP] >>
            ntac 2 TOP_CASE_TAC >>
            fs[ALOOKUP_NONE,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
            imp_res_tac ALOOKUP_MEM >>
            fs[MEM_MAP] >> rveq >> pairarg_tac >> rveq >> fs[] >>
            rveq >> fs[] >> rveq >> fs[] >>
            rfs[term_ok_def] >> rfs[] >> fs[welltyped_def] >>
            imp_res_tac WELLTYPED_LEMMA >> rveq >>
            `MEM x (tyvars(typeof pred))` by simp[tyvars_def] >>
            drule_then drule (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
            simp[]) >>
         strip_tac >>
         simp[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP,MAP_MAP_o,o_DEF,tyvars_def] >>
         simp[ALOOKUP_Tyvar,ALOOKUP_MAPf]) >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma',stuff)` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      qmatch_goalsub_abbrev_tac `instance_subst [ty0,ty1]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma'',stuff')` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      ntac 2 (PRED_ASSUM is_exists kall_tac) >>
      rpt(qpat_x_assum `Fun _ _ = TYPE_SUBST _ _` (mp_tac o GSYM)) >>
      rw[] >> fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
      qmatch_goalsub_abbrev_tac `ext_type_frag_builtins _ (Tyapp name ntys)` >>
      `Tyapp name ntys ∈ nonbuiltin_types`
        by(simp[Abbr`ntys`] >>
           drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def,
              APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           last_assum(qspec_then `(name,0)` mp_tac) >>
           last_x_assum(qspec_then `(name,2)` mp_tac) >>
           simp[] >>
           rw[nonbuiltin_types_def,is_builtin_type_def]) >>
      qunabbrev_tac `ntys` >>
      simp[ext_type_frag_builtins_nonbuiltin] >>
      qmatch_goalsub_abbrev_tac `v (vname,vty)` >>
      `v (vname,vty) ⋲ (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma vty)`
        by(qhdtm_x_assum `valuates_frag0` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then(qspecl_then [`vname`,`vty`] mp_tac) >>
           simp[Abbr `vty`,ext_type_frag_builtins_nonbuiltin] >>
           disch_then match_mp_tac >>
           drule_then drule terms_of_frag_uninst_equationE >>
           impl_tac >- simp[welltyped_equation] >>
           strip_tac >>
           PURE_REWRITE_TAC[GSYM TYPE_SUBSTf_def] >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           Q.REFINE_EXISTS_TAC `Var _ _` >>
           simp[] >>
           metis_tac[]) >>
      `TYPE_SUBSTf sigma vty ∈ ground_types (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qunabbrev_tac `vty` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      `v (vname,vty) ⋲ ext_type_frag_builtins(type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma (domain(typeof pred)))`
        by(qpat_x_assum `_ ⋲ type_interpretation_of ind _ _` mp_tac >>
           fs[Abbr `vty`] >>
           Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
           simp[type_interpretation_of_alt] >>
           qpat_x_assum `inhabited ind` kall_tac >>
           simp[mllistTheory.mapPartial_thm,FILTER_APPEND] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           simp[type_matches_def] >>
           qmatch_goalsub_abbrev_tac `if predd then SOME _ else NONE` >>
           Q.SUBGOAL_THEN `predd` assume_tac >-
             (qunabbrev_tac `predd` >>
              simp[MAP_EQ_f,MEM_MAP,PULL_EXISTS,REV_ASSOCD_ALOOKUP] >>
              qexists_tac `MAP (λx. (sigma x, Tyvar x)) (tvars pred)` >>
              simp[ALOOKUP_Tyvar,MAP_MAP_o,o_DEF,ALOOKUP_MAPf]) >>
           qunabbrev_tac `predd` >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
           Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
             (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
           disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
           rename1 `instance_subst _ _ _ = SOME result` >>
           Cases_on `result` >>
           rename1 `SOME(sigma''',stuff'')` >>
           simp[] >>
           drule_then assume_tac instance_subst_soundness >>
           MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
           qpat_x_assum `Tyapp _ _ = TYPE_SUBST _ _` (assume_tac o GSYM) >>
           simp[] >>
           `TYPE_SUBST sigma'³' (domain (typeof pred)) =
            TYPE_SUBSTf sigma (domain (typeof pred))
           `
             by(simp[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
                rpt strip_tac >> first_x_assum match_mp_tac >>
                rfs[term_ok_clauses] >>
                fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
                drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
                drule_then (match_mp_tac o REWRITE_RULE[SUBSET_DEF]) tyvars_typeof_subset_tvars >>
                rfs[tyvars_def] >>
                disch_then drule) >>
           rw[mem_sub]) >>
      MAP_EVERY qunabbrev_tac [`vname`,`vty`] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           conj_tac >-
             (qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
              `Abstract a1 a2 a3 ' a4 = a3 a4`
                by(drule_then match_mp_tac apply_abstract >>
                   MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                   simp[] >> fs[]) >>
              MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
              pop_assum SUBST_ALL_TAC >>
              simp[]) >>
           rw[] >>
           SELECT_ELIM_TAC >>
           simp[] >>
           qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[is_frag_interpretation_def,total_fragment_def,is_type_frag_interpretation_def] >>
           strip_tac >>
           first_x_assum match_mp_tac >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           simp[] >> fs[]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      pop_assum SUBST_ALL_TAC >>
      simp[] >>
      fs[]) >>
      (* Second abs/rep axiom *)
       drule proves_theory_mono >>
       qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
       disch_then(qspecl_then [`tysof ctxt2`,`tmsof ctxt2`,`axsof ctxt2`,
                               `tyenv`,`tmenv`] mp_tac) >>
       simp[] >>
       MAP_EVERY qunabbrev_tac [`tyenv`,`tmenv`] >>
       impl_tac >-
         (rw[] >>
          TRY(match_mp_tac (CONJUNCT2 SUBMAP_FUNION_ID) >> rw[FDOM_FUPDATE] >>
              drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
              drule extends_NIL_DISJOINT >>
              simp[] >> NO_TAC) >>
          qhdtm_x_assum `theory_ok` mp_tac >>
          rw[theory_ok_def]) >>
      strip_tac >>
      drule_then drule (MP_CANON termsem_ext_equation) >>
      disch_then drule >>
      fs[valuates_frag_builtins] >>
      disch_then drule >>
      drule_then drule terms_of_frag_uninst_equationE >>
      impl_keep_tac >-
        (rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
         imp_res_tac proves_term_ok >>
         fs[] >> rfs[term_ok_clauses] >>
         qpat_x_assum `Comb _ _ has_type Bool` (strip_assume_tac o ONCE_REWRITE_RULE[has_type_cases]) >>
         fs[] >> rveq >>
         imp_res_tac WELLTYPED_LEMMA >>
         rfs[] >> rveq >> fs[] >> rw[equation_def]) >>
      disch_then (MAP_EVERY assume_tac o rev o CONJUNCTS) >>
      ntac 2 (disch_then dxrule) >>
      impl_keep_tac >-
        (rw[term_ok_clauses] >> rw[term_ok_def] >>
         qpat_assum `is_std_sig(FUNION _ _,_)` (strip_assume_tac o REWRITE_RULE[is_std_sig_def]) >>
         rw[type_ok_def,EVERY_MEM,MEM_MAP,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
         rw[type_ok_def] >>
         drule proves_term_ok >>
         rw[EVERY_MEM,term_ok_def] >> rw[] >>
         drule_then drule term_ok_type_ok >> rw[] >>
         fs[] >> rfs[term_ok_clauses] >>
         qpat_x_assum `Comb _ _ has_type Bool` (strip_assume_tac o ONCE_REWRITE_RULE[has_type_cases]) >>
         fs[] >> rveq >>
         imp_res_tac WELLTYPED_LEMMA >>
         rfs[] >> rveq >> fs[] >> rw[equation_def]
        ) >>
      simp[termsem_ext_def] >>
      disch_then kall_tac >>
      rw[boolean_eq_true] >>
      rw[termsem_def] >>
      drule_then drule terms_of_frag_uninst_equationE >>
      impl_tac >- rw[welltyped_equation] >>
      strip_tac >>
      drule_then dxrule terms_of_frag_uninst_equationE >>
      impl_tac >- rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
      disch_then(MAP_EVERY assume_tac o rev o CONJUNCTS) >>
      drule_then drule termsem_ext_equation >>
      disch_then drule >> disch_then drule >>
      disch_then dxrule >> disch_then dxrule >>
      impl_keep_tac >-
        (rw[term_ok_clauses] >> rw[term_ok_def] >>
         qpat_assum `is_std_sig(FUNION _ _,_)` (strip_assume_tac o REWRITE_RULE[is_std_sig_def]) >>
         rw[type_ok_def,EVERY_MEM,MEM_MAP,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
         rw[type_ok_def] >>
         drule proves_term_ok >>
         rw[EVERY_MEM,term_ok_def] >> rw[] >>
         drule_then drule term_ok_type_ok >> rw[] >>
         fs[] >> rfs[term_ok_clauses] >>
         qpat_x_assum `Comb _ _ has_type Bool` (strip_assume_tac o ONCE_REWRITE_RULE[has_type_cases]) >>
         fs[] >> rveq >>
         imp_res_tac WELLTYPED_LEMMA >>
         rfs[] >> rveq >> fs[] >> rw[equation_def]) >>
      simp[termsem_ext_def] >>
      disch_then kall_tac >>
      rw[boolean_eq_true] >>
      rw[termsem_def] >>
      `~MEM (strlit "=") (MAP FST (const_list ctxt1))`
        by(drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def] >>
           rveq >> fs[] >>
           fs[APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           drule_then(assume_tac o C MATCH_MP (REWRITE_RULE[init_ctxt_def] init_ctxt_extends))
                     extends_trans >>
           drule extends_NIL_DISJOINT >>
           rw[]) >>
      `MEM (strlit "=") (MAP FST (const_list ctxt2))`
        by(imp_res_tac extends_appends >> rw[init_ctxt_def]) >>
      `abs <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      `rep <> strlit "="` by(CCONTR_TAC >> fs[]) >>
      simp[ext_term_frag_builtins_def] >>
       qmatch_asmsub_abbrev_tac `total_fragment (tyenv,tmenv)` >>
      `models (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
              (UNCURRY (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              ((tyenv,tmenv),axsof ctxt2)`
        by(rw[models_def]) >>
      drule_then drule proves_sound >>
      simp[entails_def] >>
      strip_tac >>
      first_x_assum drule >>
      simp[satisfies_t_def] >>
      ntac 2 (disch_then drule) >>
      impl_keep_tac >-
        (rw[ground_terms_uninst_def] >>
         goal_assum drule >>
         rw[ground_types_def,tyvars_def] >>
         imp_res_tac term_ok_type_ok >>
         qpat_x_assum `is_std_sig (tyenv,tmenv)` mp_tac >>
         rw[is_std_sig_def,type_ok_def]) >>
      simp[satisfies_def] >>
      simp[valuates_frag_builtins] >>
      disch_then drule >>
      impl_tac >-
        (match_mp_tac terms_of_frag_uninst_term_ok >> simp[]) >>
      simp[termsem_def] >> strip_tac >>
      `termsem
           (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (ext_term_frag_builtins
              (ext_type_frag_builtins
                 (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              (UNCURRY
                 (term_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))))
           v sigma witness ⋲
         (ext_type_frag_builtins
              (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (TYPE_SUBSTf sigma (typeof witness))
      `
        by(match_mp_tac termsem_in_type_ext2 >>
           rpt(goal_assum drule) >>
           conj_tac >-
             (match_mp_tac terms_of_frag_uninst_term_ok >>
              simp[] >>
              drule proves_term_ok >>
              rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
           rpt strip_tac >>
           qpat_x_assum `valuates_frag _ _ _ _` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then match_mp_tac >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           goal_assum drule >>
           goal_assum drule >>
           match_mp_tac terms_of_frag_uninst_term_ok >>
           simp[] >>
           drule proves_term_ok >> rw[EVERY_MEM,MEM_MAP,term_ok_def]) >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ abs abstype` >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of ind _ rep reptype` >>
      `(abs,abstype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(fs[Abbr `abstype`,ground_consts_def,ground_types_def] >>
           conj_tac >-
             (simp[tyvars_def,LIST_UNION_EQ_NIL,tyvars_TYPE_SUBSTf_eq_NIL] >>
              match_mp_tac FOLDR_LIST_UNION_empty >>
              rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
           conj_asm1_tac >-
             (qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
              `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
              pop_assum SUBST_ALL_TAC >>
              simp[term_ok_clauses] >>
              conj_tac >-
                (match_mp_tac type_ok_TYPE_SUBSTf >> simp[] >>
                 qpat_x_assum `term_ok _ (Comb _ _)` mp_tac >>
                 simp[term_ok_clauses] >>
                 rpt strip_tac >>
                 simp[] >> metis_tac[term_ok_type_ok,FST]) >>
              simp[type_ok_def,EVERY_MAP,MEM_MAP,PULL_EXISTS] >>
              rw[Abbr `tyenv`,FLOOKUP_FUNION,FLOOKUP_UPDATE]) >>
           rw[term_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           qexists_tac `(MAP (λx. (sigma x,Tyvar x)) (tvars pred))` >>
           simp[TYPE_SUBST_eq_TYPE_SUBSTf,MAP_EQ_f,MEM_MAP,PULL_EXISTS,
                REV_ASSOCD_ALOOKUP,MAP_MAP_o,o_DEF,ALOOKUP_Tyvar,ALOOKUP_MAPf] >>
           simp[TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
           rfs[term_ok_clauses] >>
           rpt strip_tac >>
           IF_CASES_TAC >> simp[] >>
           fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
           drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
           drule_then (mp_tac o REWRITE_RULE[SUBSET_DEF,Once MONO_NOT_EQ]) tyvars_typeof_subset_tvars >>
           disch_then drule >>
           simp[tyvars_def]) >>
      `(abs,abstype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `(rep,reptype) ∈ ground_consts (sigof(ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qpat_x_assum `(abs,abstype) ∈ ground_consts _` mp_tac >>
           fs[Abbr `reptype`,Abbr `abstype`,ground_consts_def,ground_types_def] >>
           qmatch_goalsub_abbrev_tac `type_ok tyenv'` >>
           `tyenv' = tysof(tyenv,tmenv)`
                by(fs[Abbr `tyenv`,Abbr `tmenv`,Abbr`tyenv'`] >>
                   fs[GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
           pop_assum SUBST_ALL_TAC >>
           simp[term_ok_clauses] >>
           simp[tyvars_def,LIST_UNION_EQ_NIL] >>
           rw[term_ok_def,term_ok_clauses,FLOOKUP_FUNION,FLOOKUP_UPDATE,MAP_EQ_f] >>
           fs[type_ok_def] >>
           metis_tac[]) >>
      `(rep,reptype) ∈ nonbuiltin_constinsts`
        by simp[nonbuiltin_constinsts_def,builtin_consts_def] >>
      `is_frag_interpretation (total_fragment (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
          (type_interpretation_of ind
             (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
          (UNCURRY
             (term_interpretation_of ind
                (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))`
        by(qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[Abbr `tyenv`,Abbr `tmenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
      MAP_EVERY qunabbrev_tac [`abstype`,`reptype`] >>
      Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
      simp[type_interpretation_of_alt] >>
      qpat_x_assum `inhabited ind` kall_tac >>
      simp[FILTER_APPEND] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
      Cases_on `[] ≠
                 defn_matches abs
                   (Fun (TYPE_SUBSTf sigma (domain (typeof pred)))
                      (Tyapp name
                         (MAP (λa. TYPE_SUBSTf sigma a)
                            (MAP Tyvar
                               (MAP implode
                                  (STRING_SORT (MAP explode (tvars pred))))))))
                   (TypeDefn name pred abs rep)` >-
        fs[defn_matches_def] >>
      simp[] >>
      ntac 2 (pop_assum kall_tac) >>
      ntac 2 (
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             FULL_SIMP_TAC bool_ss [GSYM APPEND_ASSOC] >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             fs[] >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`] >>
        qmatch_goalsub_abbrev_tac `FILTER ff ll` >>
        `FILTER ff ll = []`
          by(simp[Abbr `ff`,Abbr `ll`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                  defn_matches_def] >> rpt strip_tac >>
             TOP_CASE_TAC >> simp[] >>
             simp[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
             Cases >> simp[] >> strip_tac >>
             simp[RIGHT_FORALL_OR_THM] >> disj1_tac >>
             qpat_x_assum `MEM (ConstSpec _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac (extends_APPEND_NIL |> Q.SPEC `[e]` |> REWRITE_RULE[APPEND]) >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             Cases_on `b` >>
             fs[updates_cases,constspec_ok_def]
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[])
             >- (pop_assum(drule_then strip_assume_tac) >>
                 qpat_x_assum `MEM (NewConst _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                 fs[]) >>
             qpat_x_assum `MEM (_,_) l` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             fs[]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`ff`,`ll`]) >>
      simp[] >>
      simp[mllistTheory.mapPartial_def,mapPartial_APPEND] >>
      rpt
        (qmatch_goalsub_abbrev_tac `mapPartial a1 a2` >>
        `mapPartial a1 a2 = []`
          by(rw[Abbr `a1`,Abbr `a2`,mllistTheory.mapPartial_thm,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,
                PULL_EXISTS] >>
             simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
             ntac 3 (PURE_TOP_CASE_TAC >> fs[] >> rveq) >>
             fs[pair_case_eq] >>
             PURE_FULL_CASE_TAC >> fs[] >> rveq >>
             qpat_x_assum `MEM (TypeDefn _ _ _ _) _` (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
             rveq >>
             drule_then (assume_tac o C MATCH_MP init_ctxt_extends) extends_trans >>
             dxrule_then assume_tac extends_APPEND_NIL >>
             dxrule_then assume_tac extends_NIL_CONS_updates >>
             fs[updates_cases]) >>
        pop_assum SUBST_ALL_TAC >>
        MAP_EVERY qunabbrev_tac [`a1`,`a2`]) >>
      simp[abs_or_rep_matches_def,abs_matches_def,rep_matches_def] >>
      reverse IF_CASES_TAC >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> pop_assum kall_tac >> simp[] >>
         simp[TYPE_SUBSTf_eq_TYPE_SUBST] >>
         rw[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
         qexists_tac `MAP (λx. (sigma x,Tyvar x)) (tvars pred)` >>
         reverse conj_tac >-
           (rw[TYPE_SUBST_tyvars,REV_ASSOCD_ALOOKUP] >>
            ntac 2 TOP_CASE_TAC >>
            fs[ALOOKUP_NONE,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL] >>
            imp_res_tac ALOOKUP_MEM >>
            fs[MEM_MAP] >> rveq >> pairarg_tac >> rveq >> fs[] >>
            rveq >> fs[] >> rveq >> fs[] >>
            rfs[term_ok_def] >> rfs[] >> fs[welltyped_def] >>
            imp_res_tac WELLTYPED_LEMMA >> rveq >>
            `MEM x (tyvars(typeof pred))` by simp[tyvars_def] >>
            drule_then drule (tyvars_typeof_subset_tvars |> REWRITE_RULE[SUBSET_DEF] |> MP_CANON) >>
            simp[]) >>
         strip_tac >>
         simp[REV_ASSOCD_ALOOKUP,ALOOKUP_MAP,MAP_MAP_o,o_DEF,tyvars_def] >>
         simp[ALOOKUP_Tyvar,ALOOKUP_MAPf]) >>
      simp[] >>
      reverse IF_CASES_TAC >-
        (goal_assum kall_tac >>
         pop_assum mp_tac >> simp[] >>
         fs[] >>
         metis_tac[]) >>
      CONV_TAC(SIMP_CONV (srw_ss())[]) >>
      qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma',stuff)` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      qmatch_goalsub_abbrev_tac `instance_subst [ty0,ty1]` >>
      Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
        (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
      disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
      rename1 `instance_subst _ _ _ = SOME result` >>
      Cases_on `result` >>
      rename1 `SOME(sigma'',stuff')` >>
      simp[] >>
      drule_then assume_tac instance_subst_soundness >>
      MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
      ntac 2 (PRED_ASSUM is_exists kall_tac) >>
      rpt(qpat_x_assum `Fun _ _ = TYPE_SUBST _ _` (mp_tac o GSYM)) >>
      rw[] >> fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
      qmatch_goalsub_abbrev_tac `ext_type_frag_builtins _ (Tyapp name ntys)` >>
      `Tyapp name ntys ∈ nonbuiltin_types`
        by(simp[Abbr`ntys`] >>
           drule_then strip_assume_tac extends_appends >>
           fs[APPEND_EQ_APPEND,init_ctxt_def,
              APPEND_EQ_CONS |> CONV_RULE(LHS_CONV SYM_CONV)] >>
           rveq >> fs[] >>
           last_assum(qspec_then `(name,0)` mp_tac) >>
           last_x_assum(qspec_then `(name,2)` mp_tac) >>
           simp[] >>
           rw[nonbuiltin_types_def,is_builtin_type_def]) >>
      qunabbrev_tac `ntys` >>
      simp[ext_type_frag_builtins_nonbuiltin] >>
      qmatch_goalsub_abbrev_tac `v (vname,vty)` >>
      `v (vname,vty) ⋲ ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma vty)`
        by(qhdtm_x_assum `valuates_frag0` mp_tac >>
           simp[valuates_frag_def] >>
           disch_then(qspecl_then [`vname`,`vty`] mp_tac) >>
           simp[Abbr `vty`,ext_type_frag_builtins_nonbuiltin] >>
           disch_then match_mp_tac >>
           drule_then drule terms_of_frag_uninst_equationE >>
           impl_tac >- simp[welltyped_equation] >>
           strip_tac >>
           PURE_REWRITE_TAC[GSYM TYPE_SUBSTf_def] >>
           match_mp_tac TYPE_SUBSTf_in_types_of_frag_I >>
           Q.REFINE_EXISTS_TAC `Var _ _` >>
           simp[] >>
           drule_then drule terms_of_frag_uninst_equationE >>
           impl_tac >- rw[welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
           strip_tac >>
           metis_tac[]) >>
      `TYPE_SUBSTf sigma vty ∈ ground_types (sigof (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))`
        by(qunabbrev_tac `vty` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           simp[tyvars_TYPE_SUBSTf_eq_NIL] >>
           match_mp_tac type_ok_TYPE_SUBSTf >>
           simp[] >>
           rfs[term_ok_clauses]) >>
      qmatch_goalsub_abbrev_tac `Abstract (type_interpretation_of ind ctxt vty')` >>
      `vty' ∈ ground_types (sigof ctxt)`
        by(qunabbrev_tac `vty'` >> qunabbrev_tac `ctxt` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      `type_interpretation_of ind ctxt vty'
       =
       (ext_type_frag_builtins (type_interpretation_of ind ctxt)
         (TYPE_SUBSTf sigma vty) suchthat
        (λtm. termsem
          (ext_type_frag_builtins (type_interpretation_of ind ctxt))
          (ext_term_frag_builtins (ext_type_frag_builtins (type_interpretation_of ind ctxt))
                                 (UNCURRY (term_interpretation_of ind ctxt))) v sigma
          pred ' tm = True))`
        by(`is_frag_interpretation (total_fragment(sigof ctxt)) (type_interpretation_of ind ctxt)
                                   (UNCURRY (term_interpretation_of ind ctxt))`
             by(simp[Abbr`ctxt`]) >>
           Q.SUBGOAL_THEN `inhabited ind` assume_tac >- metis_tac[] >>
           simp[type_interpretation_of_alt] >>
           qpat_x_assum `inhabited ind` kall_tac >>
           fs[Abbr `vty`,Abbr `vty'`,Abbr `ctxt`] >>
           simp[mllistTheory.mapPartial_thm,FILTER_APPEND] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `FILTER IS_SOME (MAP f1 c1)` >>
           `FILTER IS_SOME (MAP f1 c1) = []`
             by(fs[Abbr `f1`,Abbr `c1`,FILTER_EQ_NIL,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
                strip_tac >>
                simp[type_matches_def] >>
                TOP_CASE_TAC >> fs[] >>
                strip_tac >>
                pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
                fs[] >> metis_tac[FST,SND]) >>
           MAP_EVERY qunabbrev_tac [`f1`,`c1`] >>
           simp[] >>
           simp[type_matches_def] >>
           qmatch_goalsub_abbrev_tac `if predd then SOME _ else NONE` >>
           Q.SUBGOAL_THEN `predd` assume_tac >-
             (qunabbrev_tac `predd` >>
              simp[MAP_EQ_f,MEM_MAP,PULL_EXISTS,REV_ASSOCD_ALOOKUP] >>
              qexists_tac `MAP (λx. (sigma x, Tyvar x)) (tvars pred)` >>
              simp[ALOOKUP_Tyvar,MAP_MAP_o,o_DEF,ALOOKUP_MAPf]) >>
           qunabbrev_tac `predd` >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `instance_subst [(ty0,ty1)]` >>
           Q.SUBGOAL_THEN `is_instance ty1 ty0` mp_tac >-
             (fs[Abbr `ty0`,Abbr`ty1`] >> metis_tac[]) >>
           disch_then (strip_assume_tac o REWRITE_RULE[instance_subst_completeness,IS_SOME_EXISTS]) >>
           rename1 `instance_subst _ _ _ = SOME result` >>
           Cases_on `result` >>
           rename1 `SOME(sigma''',stuff'')` >>
           simp[] >>
           drule_then assume_tac instance_subst_soundness >>
           MAP_EVERY qunabbrev_tac [`ty0`,`ty1`] >>
           qpat_x_assum `Tyapp _ _ = TYPE_SUBST _ _` (assume_tac o GSYM) >>
           simp[] >>
           `TYPE_SUBST sigma'³' (domain (typeof pred)) =
            TYPE_SUBSTf sigma (domain (typeof pred))
           `
             by(simp[TYPE_SUBST_eq_TYPE_SUBSTf,TYPE_SUBSTf_eq_TYPE_SUBSTf] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS] >>
                rpt strip_tac >> first_x_assum match_mp_tac >>
                rfs[term_ok_clauses] >>
                fs[welltyped_def] >> qpat_x_assum `pred has_type _` assume_tac >>
                drule_then assume_tac WELLTYPED_LEMMA >> rveq >>
                drule_then (match_mp_tac o REWRITE_RULE[SUBSET_DEF]) tyvars_typeof_subset_tvars >>
                rfs[tyvars_def] >>
                disch_then drule) >>
           simp[] >>
           simp[mem_sub] >>
           simp[ELIM_UNCURRY] >>
           qmatch_goalsub_abbrev_tac `termsem a1 a2 a3 a4` >>
           `termsem a1 a2 a3 a4 pred =
            termsem a1 a2 v a4 pred`
             by(match_mp_tac(GEN_ALL termsem_frees) >>
                fs[CLOSED_def] >>
                rfs[term_ok_clauses]) >>
           pop_assum SUBST_ALL_TAC >>
           `termsem a1 a2 v a4 pred =
            termsem a1 a2 v sigma pred`
             by(MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                match_mp_tac termsem_subst >>
                rfs[term_ok_clauses] >>
                fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS]) >>
           pop_assum SUBST_ALL_TAC >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           reverse IF_CASES_TAC
           >- (goal_assum kall_tac >>
               pop_assum mp_tac >> simp[] >>
               fs[ELIM_UNCURRY] >>
               rfs[term_ok_clauses] >> metis_tac[]) >>
           pop_assum kall_tac >>
           rw[]) >>
      MAP_EVERY qunabbrev_tac [`vname`,`vty`] >>
      MAP_EVERY qunabbrev_tac [`ctxt`,`vty'`] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           conj_tac >-
             (qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
              `Abstract a1 a2 a3 ' a4 = a3 a4`
                by(drule_then match_mp_tac apply_abstract >>
                   MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                   simp[] >> rw[] >>
                   SELECT_ELIM_TAC >>
                   simp[] >>
                   simp[mem_sub] >>
                   rfs[term_ok_clauses] >>
                   metis_tac[]) >>
              MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
              simp[] >>
              rw[] >>
              SELECT_ELIM_TAC >>
              simp[] >>
              simp[mem_sub] >>
              rfs[term_ok_clauses] >>
              metis_tac[]) >>
           simp[] >>
           qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
           `Abstract a1 a2 a3 ' a4 = a3 a4`
             by(drule_then match_mp_tac apply_abstract >>
                MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
                simp[] >>
                rw[] >>
                SELECT_ELIM_TAC >> simp[] >>
                simp[mem_sub] >>
                rfs[term_ok_clauses] >>
                metis_tac[]) >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           simp[] >>
           rw[] >>
           SELECT_ELIM_TAC >> simp[] >>
           simp[mem_sub] >>
           rfs[term_ok_clauses] >>
           metis_tac[]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `Abstract a1 a2 a3 ' a4` >>
      `Abstract a1 a2 a3 ' a4 = a3 a4`
        by(drule_then match_mp_tac apply_abstract >>
           MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
           conj_tac >- simp[] >>
           simp[] >>
           rw[] >>
           SELECT_ELIM_TAC >>
           simp[] >>
           simp[mem_sub] >>
           rfs[term_ok_clauses] >>
           metis_tac[]) >>
      MAP_EVERY qunabbrev_tac [`a1`,`a2`,`a3`,`a4`] >>
      simp[] >>
      IF_CASES_TAC >- rfs[mem_sub,boolean_def] >>
      rfs[mem_sub] >>
      SELECT_ELIM_TAC >>
      conj_tac >- (rfs[term_ok_clauses] >> metis_tac[]) >>
      rpt strip_tac >>
      `x <> v («r» ,domain (typeof pred))` by
        (spose_not_then strip_assume_tac >>
         rveq >> fs[]) >>
      simp[boolean_def] >>
      qmatch_goalsub_abbrev_tac `a1 ' a2 = False` >>
      `a1 ' a2 ⋲ boolset`
        by(MAP_EVERY qunabbrev_tac [`a1`,`a2`] >>
           drule_then match_mp_tac apply_in_rng >>
           goal_assum drule >>
           qmatch_goalsub_abbrev_tac `_ ⋲ a1` >>
           `a1 = ext_type_frag_builtins
                   (type_interpretation_of ind
                      (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
                   (TYPE_SUBSTf sigma(typeof pred))`
             by(rfs[Abbr `a1`,term_ok_clauses] >>
                simp[ext_type_frag_builtins_Fun] >>
                qpat_x_assum `Comb pred witness has_type Bool` (strip_assume_tac o REWRITE_RULE[Once has_type_cases]) >>
                pop_assum mp_tac >> simp[] >>
                pop_assum mp_tac >> simp[] >>
                pop_assum mp_tac >> simp[] >>
                strip_tac >> rveq >>
                ntac 2 strip_tac >>
                ntac 2(dxrule WELLTYPED_LEMMA) >>
                ntac 2 strip_tac >>
                rveq >>
                rfs[] >>
                CONV_TAC(RHS_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV[ext_type_frag_builtins_def]))) >>
                simp[]) >>
           simp[] >>
           match_mp_tac termsem_in_type_ext2 >>
           simp[] >>
           goal_assum drule >>
           simp[] >>
           fs[CLOSED_def] >>
           qpat_x_assum `Comb pred _ ∈ terms_of_frag_uninst _ _` assume_tac >>
           drule_then drule terms_of_frag_uninst_combE >>
           rw[]) >>
      metis_tac[mem_boolset,true_neq_false])
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

Theorem interpretation_is_model:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt /\ inhabited ind
            /\ (axioms_admissible mem ind ctxt)
    ⇒
        models (type_interpretation_of ind ctxt) (UNCURRY(term_interpretation_of ind ctxt)) (thyof ctxt)
Proof
  rpt strip_tac >>
  drule_then (assume_tac o MATCH_MP extends_nil_orth o C MATCH_MP init_ctxt_extends) extends_trans >>
  imp_res_tac extends_init_ctxt_terminating >>
  simp[models_def] >>
  conj_asm1_tac >-
    metis_tac[interpretation_is_total_frag_interpretation,extends_trans,init_ctxt_extends] >>
  rw[] >>
  qpat_x_assum `_ extends init_ctxt` assume_tac >>
  `!ctxt2. ctxt2 extends init_ctxt ==>
    !ctxt1 p.
    orth_ctxt (ctxt1 ++ ctxt2) /\
    terminating (subst_clos (dependency (ctxt1 ++ ctxt2))) /\
    (axioms_admissible mem ind (ctxt1 ++ ctxt2)) /\ inhabited ind /\
    is_frag_interpretation (total_fragment (sigof (ctxt1 ++ ctxt2)))
      (type_interpretation_of ind (ctxt1 ++ ctxt2))
      (UNCURRY (term_interpretation_of ind (ctxt1 ++ ctxt2))) /\
    MEM p (axiom_list ctxt2) /\
    ctxt1 ++ ctxt2 extends init_ctxt ==>
    satisfies_t (sigof (ctxt1 ++ ctxt2))
      (ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ ctxt2)))
      (ext_term_frag_builtins
         (ext_type_frag_builtins (type_interpretation_of ind (ctxt1 ++ ctxt2)))
         (UNCURRY (term_interpretation_of ind (ctxt1 ++ ctxt2)))) ([],p)`
    by(qhdtm_x_assum `is_set_theory` (fn thm => rpt(pop_assum kall_tac) >> assume_tac thm) >>
       ntac 2 strip_tac >>
       drule_then ho_match_mp_tac extends_init_ind >>
       rpt strip_tac
       >- ((* init ctxt axioms*)
           fs[init_ctxt_def,conexts_of_upd_def])
       >- (rename1 `ctxt0 ++ upd::ctxt1` >>
           first_x_assum(qspec_then `ctxt0 ++ [upd]` mp_tac) >>
           PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >>
           strip_tac >>
           qpat_x_assum `MEM _ _` (strip_assume_tac o SIMP_RULE bool_ss [FLAT,MAP,MEM_APPEND])
           >- (* Axiom in update *)
              (drule_then match_mp_tac interpretation_models_axioms_lemma >>
               rfs[total_fragment_is_fragment] >>
               drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >>
               rw[DISJ_IMP_THM,FORALL_AND_THM] >>
               imp_res_tac extends_appends >>
               rveq >> simp[] >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >-
                 metis_tac[] >-
                 (imp_res_tac axioms_admissibleE >> simp[]) >>
               metis_tac[APPEND_ASSOC,APPEND]
              )
           >- (* Axiom in update (again) *)
              (drule_then match_mp_tac interpretation_models_axioms_lemma >>
               rfs[total_fragment_is_fragment] >>
               drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >>
               rw[DISJ_IMP_THM,FORALL_AND_THM] >>
               imp_res_tac extends_appends >>
               rveq >> simp[] >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               dxrule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >-
                 metis_tac[] >-
                 (imp_res_tac axioms_admissibleE >> simp[]) >>
               metis_tac[APPEND_ASSOC,APPEND]
              )
           >- (* Axiom not in update *)
              (fs[] >> metis_tac[])
          )
      ) >>
  first_x_assum (drule_then (qspec_then `[]` mp_tac)) >>
  rw[] >> metis_tac[]
QED

Theorem min_hol_interpretation_is_model:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt
            /\ (!p. ~MEM (NewAxiom p) ctxt)
    ⇒
        models (type_interpretation_of One ctxt) (UNCURRY(term_interpretation_of One ctxt)) (thyof ctxt)
Proof
  rpt strip_tac >>
  drule_then match_mp_tac interpretation_is_model >>
  simp[mem_one] >>
  rw[axioms_admissible_def] >> fs[FORALL_AND_THM]
QED

Theorem mk_eta_ctxt_extends_init:
  mk_eta_ctxt init_ctxt extends init_ctxt
Proof
  match_mp_tac eta_extends >> rw[is_std_sig_init]
QED

Theorem eta_interpretation_is_model:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends mk_eta_ctxt(init_ctxt)
            /\ (!p. MEM (NewAxiom p) ctxt ==> MEM (NewAxiom p) (mk_eta_ctxt(init_ctxt)))
    ⇒
        models (type_interpretation_of One ctxt) (UNCURRY(term_interpretation_of One ctxt)) (thyof ctxt)
Proof
  rpt strip_tac >>
  drule_then match_mp_tac interpretation_is_model >>
  simp[mem_one] >>
  reverse conj_tac >-
    (rw[axioms_admissible_def] >>
     fs[DISJ_IMP_THM,FORALL_AND_THM,mk_eta_ctxt_def,admissible_axiom_def,init_ctxt_def]) >>
  metis_tac[extends_trans,mk_eta_ctxt_extends_init]
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

Theorem finite_hol_interpretation_is_model:
  is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends finite_hol_ctxt
            /\ (!p. MEM (NewAxiom p) (TAKE (LENGTH ctxt - LENGTH finite_hol_ctxt) ctxt) ==> F)
    ⇒
        models (type_interpretation_of One ctxt) (UNCURRY(term_interpretation_of One ctxt)) (thyof ctxt)
Proof
  rpt strip_tac >>
  drule_then match_mp_tac interpretation_is_model >>
  simp[mem_one] >>
  reverse conj_tac >-
    (rw[axioms_admissible_def] >>
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
    ) >>
  metis_tac[extends_trans,finite_hol_ctxt_extends_init]
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

Theorem hol_interpretation_is_model:
  is_set_theory ^mem /\ is_infinite ^mem ind ⇒
    ∀ctxt. ctxt extends hol_ctxt
            /\ (!p. MEM (NewAxiom p) (TAKE (LENGTH ctxt - LENGTH hol_ctxt) ctxt) ==> F)
    ⇒
        models (type_interpretation_of ind ctxt) (UNCURRY(term_interpretation_of ind ctxt)) (thyof ctxt)
Proof
  rpt strip_tac >>
  drule_then match_mp_tac interpretation_is_model >>
  simp[mem_one] >>
  reverse conj_tac >-
    (conj_tac >- metis_tac[indset_inhabited] >>
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
    ) >>
  metis_tac[extends_trans,hol_ctxt_extends_init]
QED

val _ = export_theory()
