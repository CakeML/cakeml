(*
  Proves soundness of the context extension rules: any model of a context can
  be extended to a model of the context obtained by applying one of the
  non-axiomatic context updates.
*)
open preamble mlstringTheory setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory

val _ = new_theory"holExtension"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

val terminating_descending_nats = Q.store_thm("terminating_descending_nats",
  `terminating (\x y. x = SUC y)`,
  rw[terminating_def]
  >> qexists_tac `x`
  >> Induct_on `x`
  >- simp[]
  >> MAP_EVERY PURE_ONCE_REWRITE_TAC [[ADD1],[ADD_SYM],[NRC_ADD_EQN]]
  >> fs[GSYM ADD1]);

val terminating_IMP_wellfounded_INV = Q.store_thm("terminating_IMP_wellfounded_INV",
  `terminating R ==> WF(Rᵀ)`,
  rw[terminating_def,prim_recTheory.WF_IFF_WELLFOUNDED,prim_recTheory.wellfounded_def,inv_DEF] >>
  CCONTR_TAC >> fs[] >>
  `!n. NRC R n (f 0) (f n)`
   by(last_x_assum kall_tac >>
      Induct >- simp[] >>
      simp[NRC_SUC_RECURSE_LEFT] >>
      metis_tac[]) >>
  metis_tac[]);

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

val ZIP_swap = Q.store_thm("ZIP_swap",
  `!l1 l2.
   LENGTH l1 = LENGTH l2
   ==>
   MAP (λ(x,y). (y,x)) (ZIP(l1,l2)) =  ZIP(l2,l1)
  `,
  Induct >- rw[] >>
  strip_tac >> Cases >> rw[]);

(*
val type_matches_depends = Q.store_thm("type_matches_depends",
  `type_matches ty defn = SOME (pred,name) /\
   MEM defn ctxt /\
   MEM c (allCInsts pred)
   ==>
   subst_clos (dependency ctxt) (INL ty) (INR(INST sigma c))
  `,
  rw[type_matches_def,subst_clos_def,dependency_cases] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >>
  qmatch_goalsub_abbrev_tac `ZIP (l,a1)` >>
  qexists_tac `Tyapp m a1` >>
  qexists_tac `c` >>
  qexists_tac `ZIP (l,a1)` >>
  unabbrev_all_tac >> simp[] >>
  simp[MAP_MAP_o,o_DEF,REV_ASSOCD_ALOOKUP,ZIP_swap] >>
  conj_tac >-
    (
     qspec_then `pred` assume_tac tvars_ALL_DISTINCT >>
     imp_res_tac ALL_DISTINCT_MAP_explode >>
     simp[LIST_EQ_REWRITE] >>
     rw[EL_MAP] >>
     qmatch_goalsub_abbrev_tac `ALOOKUP a1` >>
     qmatch_goalsub_abbrev_tac `EL a2` >>
     Q.ISPECL_THEN [`a1`,`a2`] mp_tac ALOOKUP_ALL_DISTINCT_EL >>
     unabbrev_all_tac >>
     impl_tac >-
       (
        simp[MAP_ZIP] >>
        match_mp_tac ALL_DISTINCT_MAP_INJ >>
        rw[implode_def]
       ) >>
     simp[EL_ZIP,EL_MAP]
    ) >>
  rename1 `TypeDefn _ pred abs rep` >>
  MAP_EVERY qexists_tac [`pred`,`abs`,`rep`] >>
  simp[]);
*)


(*Hol_defn "interpretation_of" `
  (type_interpretation_of0
   ^mem ctxt ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One
   else if ~orth_ctxt ctxt then
     One
   else
     case mapPartial (type_matches ty) ctxt of
     | [] => One
     | [(pred,ty',sigma)] =>
       let t = INST sigma pred;
           pty = domain(typeof pred);
           ptysem = type_interpretation_of0 ^mem ctxt pty;
           consts = allCInsts
       in
         ptysem suchthat
           (ARB(term_interpretation_of0 ^mem
            (*thy*) ctxt ARB ARB
           ))
     | _ => ARB
  )`
*)

(*
Definition sc_ctxt_of_def:
 (sc_ctxt_of (INL(a,ctxt1,b)) = ctxt1) /\
 (sc_ctxt_of (INR(c,ctxt2,d,e)) = ctxt2)
End
*)

Definition subst_clos_term_rel_def:
 subst_clos_term_rel (a1:('U -> 'U -> bool) # update list # type +
    ('U -> 'U -> bool) # update list # mlstring # type)
                     (a2:('U -> 'U -> bool) # update list # type +
    ('U -> 'U -> bool) # update list # mlstring # type) =
 let
   ctxt1 = sum_CASE a1 (FST o SND) (FST o SND);
   ctxt2 = sum_CASE a2 (FST o SND) (FST o SND);
   mem1 = sum_CASE a1 FST FST;
   mem2 = sum_CASE a2 FST FST;
 in
   if ctxt1 = ctxt2 /\ mem1 = mem2 /\ terminating(subst_clos(dependency ctxt2))
   then
     case (a1,a2) of
     | (INL(_,_,typ1),INL(_,_,typ2)) => subst_clos (dependency ctxt2) (INL typ2) (INL typ1)
     | _ => F
   else F
End

val type_interpretation_of_def =
    tDefine "type_interpretation_of" `
  (type_interpretation_of0
   ^mem ctxt ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~orth_ctxt ctxt then
     One:'U
   else
     case mapPartial (type_matches ty) ctxt of
     | [] => One
     | [(pred,ty',tvs)] =>
       (case instance_subst [(ty, (Tyapp ty' (MAP Tyvar tvs)))] [] [] of
         | SOME(sigma,e) =>
            let (*t = INST sigma pred;*)
                pty = domain(typeof pred);
                (*ptysem = type_interpretation_of0 ^mem ctxt pty;*)
                consts = consts_of_term pred ∩ nonbuiltin_constinsts;
                inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
                sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
                γ = (λ(c,ty).
                      if (c,ty) ∈ inst_consts then
                        term_interpretation_of0 ^mem ctxt c ty
                      else One);
                δ = (λty.
                       if MEM ty (allTypes' (TYPE_SUBST sigma pty)) then
                         type_interpretation_of0 ^mem ctxt ty
                       else One);
                atys = MAP (TYPE_SUBST sigma) (allTypes pred);
                δ' = (λty.
                       if MEM ty(FLAT (MAP allTypes' atys)) then
                         type_interpretation_of0 ^mem ctxt ty
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
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty) (* TODO: dodgy AF *)
         | NONE => One:'U)
     | _ => One:'U
  ) /\
  (term_interpretation_of0
   ^mem ctxt (name:mlstring) ty =
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
                 δ = (λty.
                         if MEM ty (allTypes' (TYPE_SUBST sigma cty)) then
                           type_interpretation_of0 ^mem ctxt ty
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
        | _ => @v. v <: ext_type_frag_builtins(type_interpretation_of0 ^mem ctxt) ty (*TODO: smaller fragment! *)
       )
     | l =>
       let (name0,trm0) = HD(HD l)
       in
         case instance_subst [(ty, typeof trm0)] [] [] of
         | SOME(sigma,e) =>
           let (*t = INST sigma pred;*)
             pty = domain(typeof trm0);
             (*ptysem = type_interpretation_of0 ^mem ctxt pty;*)
             consts = consts_of_term trm0 ∩ nonbuiltin_constinsts;
             inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
             sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
             γ = (λ(c,ty).
                   if (c,ty) ∈ inst_consts then
                     term_interpretation_of0 ^mem ctxt c ty
                   else One);
             atys = MAP (TYPE_SUBST sigma) (allTypes trm0);
             δ = (λty.
                    if MEM ty(FLAT (MAP allTypes' atys)) then
                      type_interpretation_of0 ^mem ctxt ty
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
     (rw[wellorderTheory.WF_IND,subst_clos_term_rel_def] >>
      reverse(Cases_on `x`) >-
        (rename1 `INR args` >> PairCases_on `args` >>
         first_x_assum match_mp_tac >> Cases >> rw[] (*TODO*)) >>
      rename1 `INL args` >> PairCases_on `args` >>
      rename1 `(mem,ctxt,ty)` >>
      reverse(Cases_on `terminating(subst_clos(dependency ctxt))`) >-
        (first_x_assum match_mp_tac >> simp[]) >>
      drule terminating_IMP_wellfounded_INV >>
      simp[wellorderTheory.WF_IND] >>
      disch_then(qspec_then `λx. case x of INL ty => P(INL(mem,ctxt,ty)) | INR trm => T (*TODO*)` mp_tac) >>
      simp[] >>
      impl_tac >-
        (Cases >> rw[] >>
         first_x_assum match_mp_tac >> Cases >> simp[] >>
         rpt TOP_CASE_TAC >> rw[] >> fs[inv_DEF] >>
         res_tac >> fs[]) >>
      disch_then(qspec_then `INL ty` mp_tac) >>
      simp[]) >>
    rpt strip_tac >-
      (fs[subst_clos_term_rel_def,subst_clos_def] >>
       drule instance_subst_soundness >> strip_tac >>
       goal_assum drule >>
       cheat
      ) >>
    cheat) (* Big fat todo: termination! *)

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

Theorem extends_NIL_DISJOINT:
  a ++ b extends [] ==> DISJOINT (FDOM(tmsof a)) (FDOM(tmsof b)) /\ DISJOINT (FDOM(tysof a)) (FDOM(tysof b))
Proof
  Induct_on `a` >- rw[] >>
  rw[] >> fs[extends_def]
  >- (qpat_x_assum `(RTC _) _ _` (strip_assume_tac o REWRITE_RULE[Once RTC_CASES1]) >>
      fs[] >> rveq >> imp_res_tac updates_DISJOINT >> fs[] >> metis_tac[DISJOINT_SYM])
  >- (qpat_x_assum `(RTC _) _ _` (strip_assume_tac o REWRITE_RULE[Once RTC_CASES1]) >>
      fs[] >> rveq >> imp_res_tac updates_DISJOINT >> fs[] >> metis_tac[DISJOINT_SYM])
  >- (qpat_x_assum `(RTC _) _ _` (strip_assume_tac o REWRITE_RULE[Once RTC_CASES1]) >>
      fs[] >> rveq >> imp_res_tac updates_DISJOINT >> fs[] >> metis_tac[DISJOINT_SYM])
  >- (qpat_x_assum `(RTC _) _ _` (strip_assume_tac o REWRITE_RULE[Once RTC_CASES1]) >>
      fs[] >> rveq >> imp_res_tac updates_DISJOINT >> fs[] >> metis_tac[DISJOINT_SYM])
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

(*
Theorem tyvars_subterm:
  !sig trm0 trm. trm0 subterm trm /\ term_ok sig trm ==> set(tyvars (typeof trm0)) ⊆ set(tyvars (typeof trm))
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  strip_tac >> ho_match_mp_tac RTC_STRONG_INDUCT >>
  rw[] >>
  res_tac >>
  fs[subterm1_cases] >> rveq >>
  imp_res_tac term_ok_subterm >> fs[tyvars_def,term_ok_def] >>
  fs[]
QED
*)

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

(*
Theorem TYPE_SUBST_allTypes_ground_types:
  !trm0.
  TYPE_SUBST sigma (typeof orig_term) ∈ ground_types sig /\
  (∀v. MEM v (tvars trm0) ⇒ MEM v (tyvars(typeof orig_term))) /\
  trm0 subterm orig_term /\
  term_ok sig orig_term /\ is_std_sig sig ==>
  set (MAP (TYPE_SUBST sigma) (allTypes trm0)) ⊆ ground_types sig
Proof
  Induct >> rw[allTypes_def] >>
  TRY(fs[tvars_def] >>
      match_mp_tac SUBSET_TRANS >>
      drule_then assume_tac TYPE_SUBST_allTypes'_ground_types >>
      PURE_ONCE_REWRITE_TAC[CONJ_SYM] >> goal_assum drule >>
      drule_all_then assume_tac subterm_allTypes >>
      fs[allTypes_def] >>

      allTypes_typeof

      rw[SUBSET_DEF,MEM_MAP]

      match_mp_tac TYPE_SUBST_allTypes'_ground_types >>
      first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  fs[tvars_def,tyvars_def,DISJ_IMP_THM,FORALL_AND_THM] >>
  >- (first_x_assum match_mp_tac >>
      `trm0 subterm orig_term /\ trm0' subterm orig_term`
        by(conj_tac >> match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
           HINT_EXISTS_TAC >> rw[subterm1_rules]) >>
      imp_res_tac term_ok_subterm >>
      rfs[term_ok_clauses] >>
      fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def] >>
      fs[type_ok_def,is_std_sig_def] >>

      conj_asm1_tac >-
        (`!v. ~MEM v (tyvars(TYPE_SUBST sigma (typeof trm0')))`
          by(strip_tac >> spose_not_then strip_assume_tac >>
             `set(tyvars(typeof trm0')) ⊆ set(tyvars rty)`
               by(fs[welltyped_def] >>
                  imp_res_tac tyvars_typeof_subset_tvars >>
                  fs[SUBSET_DEF] >> rw[] >>
                  imp_res_tac WELLTYPED_LEMMA >> rveq >>
                  rpt res_tac) >>
             drule tyvars_TYPE_SUBST_mono >>
             strip_tac >>
             fs[SUBSET_DEF] >>
             first_x_assum drule >>
             rw[]) >>
          Cases_on `(tyvars (TYPE_SUBST sigma (typeof trm0')))` >> fs[FORALL_AND_THM]) >>
      match_mp_tac type_ok_TYPE_SUBST_strong >>
      conj_tac >- (match_mp_tac term_ok_type_ok >> rw[is_std_sig_def]) >>
      rpt strip_tac >> res_tac >>
      `MEM x (tvars trm0')`
        by(fs[welltyped_def] >> imp_res_tac WELLTYPED_LEMMA >> rveq >>
             imp_res_tac tyvars_typeof_subset_tvars >> fs[SUBSET_DEF]) >>
      first_x_assum(drule_then strip_assume_tac) >>
      drule_then drule type_ok_TYPE_SUBST_imp >> rw[])
  >- (first_x_assum match_mp_tac >>
      fs[term_ok_clauses] >>
      fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def] >>
      fs[type_ok_def,is_std_sig_def] >>


Theorem TYPE_SUBST_allTypes_ground_types:
  !trm0.
  TYPE_SUBST sigma (typeof trm0) ∈ ground_types sig /\
  (∀v. MEM v (tvars trm0) ⇒ MEM v (tyvars (typeof trm0))) /\
  term_ok sig trm0 /\ is_std_sig sig ==>
  set (MAP (TYPE_SUBST sigma) (allTypes trm0)) ⊆ ground_types sig
Proof
  Induct >> rw[allTypes_def] >>
  TRY(match_mp_tac TYPE_SUBST_allTypes'_ground_types >>
      first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  fs[tvars_def,tyvars_def,DISJ_IMP_THM,FORALL_AND_THM]
  >- (first_x_assum match_mp_tac >>
      fs[term_ok_clauses] >>
      fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def] >>
      fs[type_ok_def,is_std_sig_def] >>
      conj_asm1_tac >-
        (`!v. ~MEM v (tyvars(TYPE_SUBST sigma (typeof trm0')))`
          by(strip_tac >> spose_not_then strip_assume_tac >>
             `set(tyvars(typeof trm0')) ⊆ set(tyvars rty)`
               by(fs[welltyped_def] >>
                  imp_res_tac tyvars_typeof_subset_tvars >>
                  fs[SUBSET_DEF] >> rw[] >>
                  imp_res_tac WELLTYPED_LEMMA >> rveq >>
                  rpt res_tac) >>
             drule tyvars_TYPE_SUBST_mono >>
             strip_tac >>
             fs[SUBSET_DEF] >>
             first_x_assum drule >>
             rw[]) >>
          Cases_on `(tyvars (TYPE_SUBST sigma (typeof trm0')))` >> fs[FORALL_AND_THM]) >>
      match_mp_tac type_ok_TYPE_SUBST_strong >>
      conj_tac >- (match_mp_tac term_ok_type_ok >> rw[is_std_sig_def]) >>
      rpt strip_tac >> res_tac >>
      `MEM x (tvars trm0')`
        by(fs[welltyped_def] >> imp_res_tac WELLTYPED_LEMMA >> rveq >>
             imp_res_tac tyvars_typeof_subset_tvars >> fs[SUBSET_DEF]) >>
      first_x_assum(drule_then strip_assume_tac) >>
      drule_then drule type_ok_TYPE_SUBST_imp >> rw[])
  >- (first_x_assum match_mp_tac >>
      fs[term_ok_clauses] >>
      fs[ground_types_def,tyvars_def,LIST_UNION_EQ_NIL,type_ok_def] >>
      fs[type_ok_def,is_std_sig_def] >>


     )



QED

*)

(* TODO: move *)
Theorem extends_APPEND_NIL:
  !a b. a ++ b extends [] ==>
     b extends []
Proof
  Induct >> rw[] >>
  fs[extends_def] >>
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[RTC_cases]) >>
  fs[]
QED

Theorem init_ctxt_extends:
  init_ctxt extends []
Proof
  fs[extends_def,init_ctxt_def] >>
  rpt(CHANGED_TAC(simp[Once RTC_CASES1])) >>
  fs[updates_cases,type_ok_def,FLOOKUP_UPDATE]
QED

Theorem is_std_sig_init:
  is_std_sig(sigof init_ctxt)
Proof
  rw[init_ctxt_def,is_std_sig_def,FLOOKUP_UPDATE]
QED

Theorem extends_appends:
  !a b. a extends b ==> ?c. a = c ++ b
Proof
  simp[extends_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> qexists_tac `upd::c` >> rw[]
QED

Theorem extends_DROP:
  !a b n. a extends b /\ n <= LENGTH a - LENGTH b ==>
  (DROP n a) extends b
Proof
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL,extends_def] >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> fs[] >>
  Cases_on `n` >> fs[] >>
  match_mp_tac(CONJUNCT2(SPEC_ALL RTC_RULES)) >>
  rw[] >>
  first_x_assum(qspec_then `0` mp_tac) >> rw[]
QED

Theorem extends_append_MID:
  a ++ [b] ++ c extends d /\ ~MEM b d ==> c extends d
Proof
  rpt strip_tac >>
  imp_res_tac extends_appends >>
  fs[APPEND_EQ_APPEND_MID] >> rveq >> fs[] >>
  drule_then(qspec_then `SUC(LENGTH a)` mp_tac) extends_DROP >>
  rw[DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] >>
  qmatch_asmsub_abbrev_tac `DROP n` >>
  `n = 0` by(rw[Abbr `n`]) >>
  fs[]
QED

Theorem extends_NIL_CONS_updates:
  !a b. a::b extends [] ==> a updates b
Proof
  rw[extends_def,Once RTC_cases]
QED

Theorem extends_NIL_APPEND_extends:
  !a b. a++b extends [] ==> a++b extends b
Proof
  Induct >> rpt strip_tac
  >- simp[extends_def,RTC_REFL]
  >- (qpat_x_assum `_ extends _` mp_tac >>
      fs[extends_def] >>
      PURE_ONCE_REWRITE_TAC[RTC_cases] >> rw[])
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
  pop_assum kall_tac >> (* w00t *)
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

Theorem MEM_tyvars_allTypes':
  !ty0 x ty.
    MEM x (tyvars ty) /\ MEM ty (allTypes' ty0) ==>
    MEM x (tyvars ty0)
Proof
  ho_match_mp_tac allTypes'_defn_ind >>
  rw[tyvars_def,allTypes'_defn] >>
  fs[tyvars_def] >>
  fs[MEM_FLAT,MEM_MAP,quantHeuristicsTheory.LIST_LENGTH_2] >> rveq >> fs[DISJ_IMP_THM,FORALL_AND_THM] >>
  rveq >> res_tac >> simp[]
QED


Theorem MEM_tyvars_allTypes:
  !x ty trm.
    MEM x (tyvars ty) /\ MEM ty (allTypes trm) ==>
    MEM x (tvars trm)
Proof
  Induct_on `trm` >>
  rw[tvars_def,allTypes_def]
  >- metis_tac[MEM_tyvars_allTypes']
  >- metis_tac[MEM_tyvars_allTypes']
  >> res_tac >> rw[]
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

Theorem interpretation_is_total_frag_interpretation_lemma:
  (∀^mem ctxt ty.
      is_set_theory ^mem ⇒
        orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) /\
        ctxt extends [] /\ ctxt extends init_ctxt /\ (* TODO: 1st is redundant *)
        ty ∈ ground_types (sigof ctxt) /\
        ty ∈ nonbuiltin_types
    ⇒
        inhabited (type_interpretation_of ctxt ty)) /\
  (∀^mem ctxt c ty.
     is_set_theory ^mem ⇒
        orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) /\
        ctxt extends [] /\ ctxt extends init_ctxt /\ (* TODO: 1st is redundant *)
        (c,ty) ∈ ground_consts (sigof ctxt) /\
        ctxt extends [] /\
        (c,ty) ∈ nonbuiltin_constinsts ⇒
        term_interpretation_of ctxt c ty ⋲
        ext_type_frag_builtins (type_interpretation_of ctxt) ty
  )
Proof
  ho_match_mp_tac type_interpretation_of_ind >> rw[]
  >- (rw[Once type_interpretation_of_def] >>
      TOP_CASE_TAC >- rw[mem_one] >>
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
      reverse conj_tac >- (imp_res_tac allTypes'_nonbuiltin) >>
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
  >- (rw[Once type_interpretation_of_def] >>
      TOP_CASE_TAC >-
        (TOP_CASE_TAC >-
           (fs[] >>
            rpt(first_x_assum(drule_then assume_tac)) >>
            fs[ground_consts_def] >>
            drule_all(MP_CANON ext_inhabited_frag_inhabited) >>
            metis_tac[]) >>
         reverse TOP_CASE_TAC >-
           (fs[] >>
            rpt(first_x_assum(drule_then assume_tac)) >>
            fs[ground_consts_def] >>
            drule_all(MP_CANON ext_inhabited_frag_inhabited) >>
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
             reverse conj_tac >- imp_res_tac allTypes'_nonbuiltin >>
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
               reverse conj_tac >-
                 (fs[MEM_FLAT,MEM_MAP] >> rveq >> imp_res_tac allTypes'_nonbuiltin) >>
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
    ∀ctxt. orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) /\ ctxt extends [] /\ ctxt extends init_ctxt
    ⇒
        is_frag_interpretation (total_fragment (sigof ctxt))
          (type_interpretation_of ctxt)
          (UNCURRY (term_interpretation_of ctxt))
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
  (!^mem ctxt ty. is_set_theory ^mem /\ ctxt extends init_ctxt /\
                  is_frag_interpretation (total_fragment(sigof ctxt))
                   (type_interpretation_of ctxt)
                   (UNCURRY (term_interpretation_of ctxt)) /\
                  ty ∈ ground_types (sigof ctxt) /\
                  ty ∈ nonbuiltin_types
   ==> type_interpretation_of ctxt ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     One:'U
   else if ~orth_ctxt ctxt then
     One:'U
   else
     case mapPartial (type_matches ty) ctxt of
     | [] => One
     | [(pred,ty',tvs)] =>
       (case instance_subst [(ty, (Tyapp ty' (MAP Tyvar tvs)))] [] [] of
         | SOME(sigma,e) =>
            let (*t = INST sigma pred;*)
                pty = domain(typeof pred);
                (*ptysem = type_interpretation_of0 ^mem ctxt pty;*)
                consts = consts_of_term pred ∩ nonbuiltin_constinsts;
                inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
                sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
                γ = (λ(c,ty). term_interpretation_of0 ^mem ctxt c ty);
                δ = type_interpretation_of0 ^mem ctxt;
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
                ext_type_frag_builtins δ (TYPE_SUBST sigma pty) (* TODO: dodgy AF *)
         | NONE => One:'U)
     | _ => One:'U
  ) /\
  (!^mem ctxt name ty.
   is_set_theory ^mem /\ ctxt extends init_ctxt /\
   (name,ty) ∈ ground_consts (sigof ctxt) /\
   (name,ty) ∈ nonbuiltin_constinsts /\
   is_frag_interpretation (total_fragment(sigof ctxt))
     (type_interpretation_of ctxt )
     (UNCURRY (term_interpretation_of ctxt)) ==>
   term_interpretation_of ctxt (name:mlstring) ty =
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
                 δ = type_interpretation_of0 ^mem ctxt;
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
        | _ => @v. v <: ext_type_frag_builtins(type_interpretation_of0 ^mem ctxt) ty
       )
     | l =>
       let (name0,trm0) = HD(HD l)
       in
         case instance_subst [(ty, typeof trm0)] [] [] of
         | SOME(sigma,e) =>
           let (*t = INST sigma pred;*)
             pty = domain(typeof trm0);
             (*ptysem = type_interpretation_of0 ^mem ctxt pty;*)
             consts = consts_of_term trm0 ∩ nonbuiltin_constinsts;
             inst_consts = {(c,ty) | ?ty'. ty = TYPE_SUBST sigma ty' /\ (c,ty') ∈ consts};
             sigma' = (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x));
             γ = (λ(c,ty). term_interpretation_of0 ^mem ctxt c ty);
             atys = MAP (TYPE_SUBST sigma) (allTypes trm0);
             δ = type_interpretation_of0 ^mem ctxt
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
  rw[] >> rw[]
  >-
    ((* type interpretation *)
     ntac 6 (TOP_CASE_TAC >> fs[] >> rveq) >>
     drule_then assume_tac instance_subst_soundness >>
     simp[mem_sub] >>
     qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
     qmatch_goalsub_abbrev_tac `ext_term_frag_builtins (ext_type_frag_builtins σ') γ` >>
     rename1 `TYPE_SUBST sigma (domain (typeof pred))` >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma (domain (typeof pred))) =
      ext_type_frag_builtins (type_interpretation_of ctxt) (TYPE_SUBST sigma (domain (typeof pred)))
     `
       by(match_mp_tac ext_type_frag_mono_eq >> rw[Abbr `σ`]) >>
     simp[] >>
     `termsem (ext_type_frag_builtins σ')
                 (ext_term_frag_builtins (ext_type_frag_builtins σ') γ)
                 empty_valuation (λx. REV_ASSOCD (Tyvar x) sigma (Tyvar x))
                 pred =
      termsem (ext_type_frag_builtins (type_interpretation_of ctxt))
                 (ext_term_frag_builtins (ext_type_frag_builtins (type_interpretation_of ctxt))
                                         (UNCURRY(term_interpretation_of ctxt)))
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
              `?whatevz. γ' = (λ(c,ty'). if (c,ty') ∈ tmfrag then term_interpretation_of ctxt c ty' else whatevz c ty')`
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
     TOP_CASE_TAC >- (CONV_TAC(DEPTH_CONV ETA_CONV) >> simp[]) >>
     reverse TOP_CASE_TAC >- (CONV_TAC(DEPTH_CONV ETA_CONV) >> simp[]) >>
     ntac 5 TOP_CASE_TAC >>
     simp[allTypes'_defn] >>
     rename1 `TYPE_SUBST sigma` >>
     rename1 `(is_abs,_,abs_type,rep_type)` >> rw[] >>
     qmatch_goalsub_abbrev_tac `ext_type_frag_builtins σ` >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma rep_type) = ext_type_frag_builtins (type_interpretation_of ctxt) (TYPE_SUBST sigma rep_type)`
       by(match_mp_tac ext_type_frag_mono_eq >>
          rw[Abbr `σ`]) >>
     `ext_type_frag_builtins σ (TYPE_SUBST sigma abs_type) = ext_type_frag_builtins (type_interpretation_of ctxt) (TYPE_SUBST sigma abs_type)`
       by(match_mp_tac ext_type_frag_mono_eq >>
          rw[Abbr `σ`]) >>
     ntac 2 (pop_assum SUBST_ALL_TAC) >> simp[]) >>
  (* Definition matches *)
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
     `?whatevz. γ' = (λ(c,ty'). if (c,ty') ∈ tmfrag then term_interpretation_of (ctxt1 ++ [upd] ++ ctxt2) c ty' else whatevz c ty')`
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

Theorem interpretation_models_axioms_lemma:
  is_set_theory ^mem ⇒
  ∀ctxt1 upd ctxt2 p.
    upd updates ctxt2 /\ theory_ok(thyof(ctxt1 ++ upd::ctxt2)) /\
    is_frag_interpretation (total_fragment (sigof (ctxt1 ++ upd::ctxt2)))
      (type_interpretation_of (ctxt1 ++ upd::ctxt2))
      (UNCURRY (term_interpretation_of (ctxt1 ++ upd::ctxt2))) /\
    is_sig_fragment (sigof (ctxt1 ++ upd::ctxt2)) (total_fragment (sigof (ctxt1 ++ upd::ctxt2))) /\ (* trivial *)
    ctxt2 extends init_ctxt /\
    ctxt1 ++ upd::ctxt2 extends init_ctxt /\
    is_std_sig (sigof(ctxt1 ++ upd::ctxt2)) /\
    is_std_sig (sigof(ctxt2)) /\
    (∀p. MEM (NewAxiom p) (upd::ctxt2) ⇒ MEM (NewAxiom p) ctxt2) /\
    orth_ctxt (ctxt1 ++ upd::ctxt2) /\
    terminating (subst_clos (dependency (ctxt1 ++ upd::ctxt2))) /\
    (∀p. MEM p (axiom_list ctxt2) ==>
          satisfies_t (sigof (ctxt1 ++ upd::ctxt2))
          (ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ upd::ctxt2)))
          (ext_term_frag_builtins
             (ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ upd::ctxt2)))
             (UNCURRY (term_interpretation_of (ctxt1 ++ upd::ctxt2)))) ([],p)) /\
    MEM p (axioms_of_upd upd)
    ==>
    satisfies_t (sigof (ctxt1 ++ upd::ctxt2))
          (ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ upd::ctxt2)))
          (ext_term_frag_builtins
             (ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ upd::ctxt2)))
             (UNCURRY (term_interpretation_of (ctxt1 ++ upd::ctxt2)))) ([],p)
Proof
  rw[updates_cases,axexts_of_upd_def,DISJ_IMP_THM] >>
  fs[axexts_of_upd_def] >> rveq
  >- ((* new axiom *)
      first_x_assum match_mp_tac >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[])
  >- ((* new axiom again (?) *)
      first_x_assum match_mp_tac >>
      pop_assum(strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >>
      fs[])
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
          `models (type_interpretation_of (ctxt1 ++ ConstSpec T eqs prop::ctxt2)) (UNCURRY (term_interpretation_of (ctxt1 ++ ConstSpec T eqs prop::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
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
               by(fs[constspec_ok_def,is_builtin_name_def] >> metis_tac[]) >>
             simp[SimpL``$=``,ext_term_frag_builtins_def] >>
             qmatch_goalsub_abbrev_tac `type_interpretation_of ctxt` >>
             `is_frag_interpretation (total_fragment (sigof ctxt))
                (type_interpretation_of ctxt)
                (UNCURRY (term_interpretation_of ctxt))`
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
          `models (type_interpretation_of (ctxt1 ++ ConstSpec F eqs prop::ctxt2)) (UNCURRY (term_interpretation_of (ctxt1 ++ ConstSpec F eqs prop::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
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
             qmatch_goalsub_abbrev_tac `type_interpretation_of ctxt` >>
             `is_frag_interpretation (total_fragment (sigof ctxt))
                (type_interpretation_of ctxt)
                (UNCURRY (term_interpretation_of ctxt))`
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
      `models (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (UNCURRY (term_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
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
              (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (ext_term_frag_builtins
              (ext_type_frag_builtins
                 (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              (UNCURRY
                 (term_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))))
           v sigma witness ⋲
         (ext_type_frag_builtins
              (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
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
      qmatch_goalsub_abbrev_tac `term_interpretation_of _ abs abstype` >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of _ rep reptype` >>
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
          (type_interpretation_of
             (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
          (UNCURRY
             (term_interpretation_of
                (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))`
        by(qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[Abbr `tyenv`,Abbr `tmenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
      MAP_EVERY qunabbrev_tac [`abstype`,`reptype`] >>
      simp[type_interpretation_of_alt] >>
      simp[FILTER_APPEND] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
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
      `v (vname,vty) ⋲ (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma vty)`
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
      `v (vname,vty) ⋲ ext_type_frag_builtins(type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma (domain(typeof pred)))`
        by(qpat_x_assum `_ ⋲ type_interpretation_of _ _` mp_tac >>
           fs[Abbr `vty`] >>
           simp[type_interpretation_of_alt] >>
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
      `models (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (UNCURRY (term_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))) ((tyenv,tmenv),axsof ctxt2)`
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
              (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
           (ext_term_frag_builtins
              (ext_type_frag_builtins
                 (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
              (UNCURRY
                 (term_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))))
           v sigma witness ⋲
         (ext_type_frag_builtins
              (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))
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
      qmatch_goalsub_abbrev_tac `term_interpretation_of _ abs abstype` >>
      qmatch_goalsub_abbrev_tac `term_interpretation_of _ rep reptype` >>
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
          (type_interpretation_of
             (ctxt1 ++ TypeDefn name pred abs rep::ctxt2))
          (UNCURRY
             (term_interpretation_of
                (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)))`
        by(qhdtm_x_assum `is_frag_interpretation0` mp_tac >>
           simp[Abbr `tyenv`,Abbr `tmenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1]) >>
      MAP_EVERY qunabbrev_tac [`abstype`,`reptype`] >>
      simp[type_interpretation_of_alt] >>
      simp[FILTER_APPEND] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
      IF_CASES_TAC >- fs[defn_matches_def] >>
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
      `v (vname,vty) ⋲ ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ TypeDefn name pred abs rep::ctxt2)) (TYPE_SUBSTf sigma vty)`
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
      qmatch_goalsub_abbrev_tac `Abstract (type_interpretation_of ctxt vty')` >>
      `vty' ∈ ground_types (sigof ctxt)`
        by(qunabbrev_tac `vty'` >> qunabbrev_tac `ctxt` >>
           simp[ground_types_def,tyvars_def,type_ok_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,
                FLOOKUP_FUNION,FLOOKUP_UPDATE] >>
           fs[Abbr`tyenv`,GSYM FUNION_ASSOC,FUNION_FUPDATE_1] >>
           match_mp_tac FOLDR_LIST_UNION_empty >>
           rw[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
      `type_interpretation_of ctxt vty'
       =
       (ext_type_frag_builtins (type_interpretation_of ctxt)
         (TYPE_SUBSTf sigma vty) suchthat
        (λtm. termsem
          (ext_type_frag_builtins (type_interpretation_of ctxt))
          (ext_term_frag_builtins (ext_type_frag_builtins (type_interpretation_of ctxt))
                                 (UNCURRY (term_interpretation_of ctxt))) v sigma
          pred ' tm = True))`
        by(`is_frag_interpretation (total_fragment(sigof ctxt)) (type_interpretation_of ctxt)
                                   (UNCURRY (term_interpretation_of ctxt))`
             by(simp[Abbr`ctxt`]) >>
           simp[type_interpretation_of_alt] >>
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
                   (type_interpretation_of
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

Theorem interpretation_is_model:
  is_set_theory ^mem ⇒
    ∀ctxt. orth_ctxt ctxt /\ terminating(subst_clos (dependency ctxt)) (*/\ ctxt extends []*)
            /\ ctxt extends init_ctxt
            /\ (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) init_ctxt)
    ⇒
        models (type_interpretation_of ctxt) (UNCURRY(term_interpretation_of ctxt)) (thyof ctxt)
Proof
  rpt strip_tac >>
  simp[models_def] >>
  conj_asm1_tac >-
    metis_tac[interpretation_is_total_frag_interpretation,extends_trans,init_ctxt_extends] >>
  rw[] >>
  qpat_x_assum `_ extends init_ctxt` assume_tac >>
  `!ctxt2. ctxt2 extends init_ctxt ==>
    !ctxt1 p.
    orth_ctxt (ctxt1 ++ ctxt2) /\
    terminating (subst_clos (dependency (ctxt1 ++ ctxt2))) /\
    (∀p. MEM (NewAxiom p) ctxt2 ⇒ MEM (NewAxiom p) init_ctxt) /\
    is_frag_interpretation (total_fragment (sigof (ctxt1 ++ ctxt2)))
      (type_interpretation_of (ctxt1 ++ ctxt2))
      (UNCURRY (term_interpretation_of (ctxt1 ++ ctxt2))) /\
    MEM p (axiom_list ctxt2) /\
    ctxt1 ++ ctxt2 extends init_ctxt ==>
    satisfies_t (sigof (ctxt1 ++ ctxt2))
      (ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ ctxt2)))
      (ext_term_frag_builtins
         (ext_type_frag_builtins (type_interpretation_of (ctxt1 ++ ctxt2)))
         (UNCURRY (term_interpretation_of (ctxt1 ++ ctxt2)))) ([],p)`
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
               rveq >> simp[])
           >- (* Axiom in update (again) *)
              (drule_then match_mp_tac interpretation_models_axioms_lemma >>
               rfs[total_fragment_is_fragment] >>
               drule_then (assume_tac o C MATCH_MP init_theory_ok) extends_theory_ok >>
               imp_res_tac theory_ok_sig >>
               fs[] >>
               rw[DISJ_IMP_THM,FORALL_AND_THM] >>
               imp_res_tac extends_appends >>
               rveq >> simp[])
           >- (* Axiom not in update *)
              (fs[]))
      ) >>
  first_x_assum (drule_then (qspec_then `[]` mp_tac)) >>
  rw[]
QED

(*WF_REL_TAC `subst_clos_term_rel`
>- (rw[prim_recTheory.WF_IFF_WELLFOUNDED,prim_recTheory.wellfounded_def] >>
    CCONTR_TAC >> fs[]

    match_mp_tac terminating_INV_IMP_wellfounded >>
    (fn (assms,goal) =>
       let val sctr = goal |> rand |> rand
       in qsuff_tac `terminating (λx y. ^sctr y x)` (assms,goal)
       end
    ) >>
    >- (CONV_TAC(RAND_CONV(RAND_CONV(PURE_ONCE_REWRITE_CONV [GSYM ETA_THM]
                                     THENC
                                     ABS_CONV(PURE_ONCE_REWRITE_CONV [GSYM ETA_THM])))) >>
        simp[inv_DEF]) >>
    rw[subst_clos_term_rel_def] >>
    rw[terminating_def,NRC] >>


      rw[subst_clos_term_rel_def]


subst_clos (dependency ctxt)


val ctxt_of_def = Define `
  ctxt_of = SUM_ALL (FST o SND) (FST o SND)`

(*qexists_tac
  `\x y.
  if ctxt_of x = ctxt_of y then
  `

Define `
  common_ctxt
    (INL (_,ctxt,_)) (INL(_,ctxt',_))

 (

 )*)
*)

  (*Hol_defn "interpretation_of" `
  (type_interpretation_of0
   ^mem ctxt ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     ARB:'U
   else if ~orth_ctxt ctxt then
     ARB:'U
   else
     case mapPartial (type_matches ty) ctxt of
     | [] => One
     | [(pred,ty',sigma)] =>
       let t = INST sigma pred;
           pty = domain(typeof pred);
           ptysem = type_interpretation_of0 ^mem ctxt pty;
           consts = allCInsts
       in
         ptysem suchthat
           (ARB(term_interpretation_of0 ^mem
            (*thy*) ctxt ARB ARB
           ))
     | _ => ARB:'U
  ) /\
  (term_interpretation_of0
   ^mem ctxt (name:mlstring) ty =
   if ~terminating(subst_clos (dependency ctxt)) then
     ARB:'U
   else if ~orth_ctxt ctxt then
     ARB:'U
   else
       type_interpretation_of0 ^mem ctxt ARB)
  `
*)

(*  drule WF_REC

  drule WF_INDUCTION_THM >> strip_tac


  strip_tac*)
(*
val LRC2_def = Define
  `(LRC2 R [e1;e2] = R e1 e2) /\
   (LRC2 R (e1::e2::l)= (R e1 e2 /\ LRC2 R (e2::l)))`

val LRC_LRC2 = Q.store_thm("LRC_LRC2",
  `!x y z ls. LRC R (z::ls) x y =
   (x = z /\ LRC2 R (z::ls ++ [y]))`,
  Induct_on `ls`
  >- (rw[LRC_def,LRC2_def] >> metis_tac[])
  >> rw[LRC_def,LRC2_def,EQ_IMP_THM]
  >- (first_x_assum(qspecl_then [`h`,`y`,`h`] (mp_tac o GSYM))
      >> simp[] >> Cases_on `ls` >> fs[LRC2_def,LRC_def])
  >- (Cases_on `ls` >> fs[LRC2_def])
  >> first_x_assum(qspecl_then [`h`,`y`,`h`] mp_tac)
  >> simp[]
  >> Cases_on `ls` >> fs[LRC2_def,LRC_def]);

val LRC_LRC2' = Q.store_thm("LRC_LRC2'",
  `!x y n ls. (LRC R ls x y /\ LENGTH ls = SUC n) =
   (?ls'. ls = x::ls' /\ LENGTH ls' = n /\ LRC2 R (x::ls' ++ [y]))`,
  Cases_on `ls` >> fs[LRC_LRC2] >> metis_tac[]);

  >- (rw[LRC_def,LRC2_def] >> metis_tac[])
  >> rw[LRC_def,LRC2_def,EQ_IMP_THM]
  >- (first_x_assum(qspecl_then [`h`,`y`,`h`] (mp_tac o GSYM))
      >> simp[] >> Cases_on `ls` >> fs[LRC2_def,LRC_def])
  >- (Cases_on `ls` >> fs[LRC2_def])
  >> first_x_assum(qspecl_then [`h`,`y`,`h`] mp_tac)
  >> simp[]
  >> Cases_on `ls` >> fs[LRC2_def,LRC_def]);
*)

(*
  `f' = \n. GENLIST (\n. if n = 0 then x else f(n-1)) (SUC n)`
    (rw[FUN_EQ_THM] >>
     Induct_on `n` >-
     (fs[] >> first_x_assum(qspec_then `0` assume_tac) >> fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
      rveq >> fs[LRC_def,inv_DEF]) >>
     fs[] >>
     first_assum(qspec_then `SUC n` assume_tac) >>
     first_x_assum(qspec_then `n` assume_tac) >> fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
     rveq >> fs[LRC_def,inv_DEF] >> rfs[] >>
     fs[GENLIST] >> rw[] >> fs[] >>
     fs[quantHeuristicsTheory.LIST_LENGTH_2] >>
     rveq >> fs[LRC_def,inv_DEF]
     fs[LRC_def]


  qexists_tac `\n. if n = 0 then x else f(n-1)` >>
  Induct >-
    (fs[] >> first_x_assum(qspec_then `0` assume_tac) >> fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
     rveq >> fs[LRC_def,inv_DEF]) >>
  fs[] >>
  PURE_FULL_CASE_TAC >-
    (first_x_assum(qspec_then `1` assume_tac) >> fs[quantHeuristicsTheory.LIST_LENGTH_2] >>
     rveq >> fs[LRC_def,inv_DEF] >> rveq >> )

  fs[quantHeuristicsTheory.LIST_LENGTH_1] >>
  pop_assum(fn thm => fs[thm,LRC_def]) >> fs[inv_DEF] >> rveq



  fs[SKOLEM_THM]

  first_x_assum(qspec_then `\n. FUNPOW (\x. @y. R y x)  n x` assume_tac) >>
  fs[] >> qexists_tac `n`
  CCONTR_TAC >> fs[]

  >> pop_assum mp_tac >>
  qid_spec_tac `x` >>
  Induct_on `n`


  if n = 0 then x else `

  spose_not_then strip_assume_tac >>


  last_x_assum mp_tac >> rw[] >>
  fs[SKOLEM_THM] >> fs[NRC_LRC] >>
  qexists_tac `\n. if n = 0 then x else f(n-1)` >>
  strip_tac >>
  Induct_on `n` >- (
    pop_assum(qspec_then `0` mp_tac) >> simp[inv_DEF]) >>
  fs[] >>
  PURE_FULL_CASE_TAC >-
    (rveq >> fs[] >> first_x_assum(qspec_then `1` mp_tac) >>
     PURE_ONCE_REWRITE_TAC[NRC_SUC_RECURSE_LEFT] >>
     fs[INV_def]
  fs[NRC_SUC_RECURSE_LEFT]


  first_x_assum(qspec_then `\n. FUNPOW (\x. @y. R y x) n x` strip_assume_tac) >>
  qexists_tac `n` >> fs[]
  SIMP_TAC pure_ss [GSYM NOT_FORALL_THM,GSYM NOT_EXISTS_THM]
  pop_assum mp_tac >>
  W (curry Q.SPEC_TAC) `x` >>
  Induct_on `n` >-
    (rw[] >> qexists_tac `0` >> rw[])

  SIMP_TAC pure_ss [GSYM NOT_FORALL_THM,GSYM NOT_EXISTS_THM]

  CCONTR_TAC >> fs[] >>


  `!n. NRC R n (f 0) (f n)`
   by(last_x_assum kall_tac >>
      Induct >- simp[] >>
      simp[NRC_SUC_RECURSE_LEFT] >>
      metis_tac[]) >>
  metis_tac[]);

      MAP_EVERY PURE_ONCE_REWRITE_TAC [[ADD1],[ADD_SYM],[NRC_ADD_EQN]] >>
      fs[GSYM ADD1] >> metis_tac[])

      )
                                            ]


  CCONTR_TAC >> fs[]

  FULL_SIMP_TAC pure_ss [GSYM NOT_EXISTS_THM,GSYM NOT_FORALL_THM]

  metis_tac[]

      HINT_EXISTS_TAC >> simp[] >>
      qexists_tac `
      PURE_ONCE_REWRITE_TAC [NRC_ADD_EQN] >>
      simp[PULL_EXISTS]

  first_x_assum(qspec_then `w` strip_assume_tac)
  rename1 `B w` >>
  )
 *)

val _ = export_theory()
