open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory listTheory pairTheory;
open alistTheory finite_mapTheory; 
open holSyntaxLibTheory;
open holSyntaxTheory holSyntaxExtraTheory;

val _ = temp_tight_equality();

val _ = new_theory "holConservative";

val updates_disjoint = Q.prove (
`!upd ctxt.
  upd updates ctxt
  ⇒
  DISJOINT (FDOM (alist_to_fmap (consts_of_upd upd))) (FDOM (tmsof ctxt))`,
 rw [Once updates_cases, DISJOINT_DEF, EXTENSION] >>
 rw [consts_of_upd_def] >>
 rw []
 >- metis_tac []
 >- (rw [PROVE [] ``a ∨ b ⇔ ~a ⇒ b``] >>
     first_x_assum match_mp_tac >>
     fs [MEM_MAP, LAMBDA_PROD, EXISTS_PROD] >>
     metis_tac [])
 >- metis_tac []);

val update_extension = Q.prove (
`!lhs tm.
  lhs |- tm
  ⇒
  !ctxt tms upd.
    lhs = (thyof ctxt,tms) ∧
    upd updates ctxt
    ⇒
    (thyof (upd::ctxt),tms) |- tm`,
 ho_match_mp_tac proves_ind >>
 rw []
 >- (rw [Once proves_cases] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`l`, `r`, `ty`, `x`] >>
     rw [] >>
     match_mp_tac type_ok_extend >>
     qexists_tac `tysof (sigof (thyof ctxt))` >>
     rw [] >>
     match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
     fs [Once updates_cases])
 >- (rw [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (match_mp_tac term_ok_extend >>
         MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             metis_tac [updates_disjoint])
         >- (Cases_on `ctxt` >>
             fs [])))
 >- (rw [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`t`, `ty`, `x`] >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (match_mp_tac type_ok_extend >>
         qexists_tac `tysof ctxt` >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (Cases_on `ctxt` >>
             fs []))
     >- (match_mp_tac term_ok_extend >>
         MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             metis_tac [updates_disjoint])
         >- (Cases_on `ctxt` >>
             fs [])))
 >- (rw [Once proves_cases] >>
     ntac 3 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 4 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 5 disj2_tac >>
     disj1_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`tm`, `h`, `ilist`] >>
     rw [] >>
     res_tac  >>
     fs [] >>
     rw [] >>
     match_mp_tac term_ok_extend >>
     MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
     rw []
     >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
         fs [Once updates_cases])
     >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
         metis_tac [updates_disjoint]))
 >- (rw [Once proves_cases] >>
     ntac 6 disj2_tac >>
     disj1_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`tm`, `h`, `tyin`] >>
     rw [] >>
     fs [EVERY_MAP, EVERY_MEM] >>
     rw [] >>
     match_mp_tac type_ok_extend >>
     qexists_tac `tysof ctxt` >>
     rw [] >>
     match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
     fs [Once updates_cases])
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     rw [] >>
     qexists_tac `t` >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (match_mp_tac term_ok_extend >>
         MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
         rw []
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             fs [Once updates_cases])
         >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
             metis_tac [updates_disjoint])
         >- (Cases_on `ctxt` >>
             fs [])))
 >- (rw [Once proves_cases] >>
     ntac 9 disj2_tac >>
     disj1_tac >>
     rw [] >>
     metis_tac [])
 >- (rw [Once proves_cases] >>
     ntac 9 disj2_tac >>
     rw []
     >- (imp_res_tac updates_theory_ok >>
         fs [])
     >- (Cases_on `ctxt` >>
         fs [])));

         (*
val update_conservative = Q.prove (
`!lhs tm.
  lhs |- tm
  ⇒
  !ctxt tms upd.
    lhs = (thyof (upd::ctxt),tms) ∧
    upd updates ctxt
    ⇒
    (thyof ctxt,tms) |- tm`,
 ho_match_mp_tac proves_ind >>
 rw []
 >- (rw [Once proves_cases] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`l`, `r`, `ty`, `x`] >>
     rw [] >>
     match_mp_tac type_ok_extend >>
     qexists_tac `tysof (sigof (thyof ctxt))` >>
     rw [] >>
     match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
     fs [Once updates_cases])
         



disj2_tac





val remove_const_def = Define `
(remove_const c def (Var v ty) = Var v ty) ∧
(remove_const c def (Const c' ty) =
  if c = Const c' ty then
    def
  else
    Const c' ty) ∧
(remove_const c def (Comb tm1 tm2) =
  Comb (remove_const c def tm1) (remove_const c def tm2)) ∧
(remove_const c def (Abs x ty tm) =
  Abs x ty (remove_const c def tm))`;

val typeof_remove_const = Q.prove (
`!c def tm. typeof def = typeof c ⇒ typeof (remove_const c def tm) = typeof tm`,
 Induct_on `tm` >>
 rw [remove_const_def]);

val remove_const_eq = Q.prove (
`typeof c = typeof def ⇒
 remove_const c def (tm1 === tm2) = 
  if c = Equal (typeof tm1) then
    Comb (Comb def (remove_const c def tm1)) (remove_const c def tm2)
  else
    remove_const c def tm1 === remove_const c def tm2`,
 rw [equation_def, remove_const_def, typeof_remove_const]);

val vfree_in_remove_const = Q.prove (
`~VFREE_IN (Var x ty) def ∧ VFREE_IN (Var x ty) (remove_const c def tm) ⇒ VFREE_IN (Var x ty) tm`,
 Induct_on `tm` >>
 rw [VFREE_IN_def, remove_const_def] >>
 rw [VFREE_IN_def]);

val term_ok_remove_const = Q.prove (
`term_ok sig def ⇒ term_ok sig (remove_const c def tm) = term_ok sig tm`,

 Induct_on `tm` >>
 rw [remove_const_def, term_ok_def]

val theory_ok_types = Q.prove (
`!thy c def. theory_ok thy ∧ c === def ∈ axsof thy ⇒ typeof c = typeof def`,
 rw [theory_ok_def] >>
 res_tac >>
 fs [equation_def, Once has_type_cases] >>
 imp_res_tac WELLTYPED_LEMMA >>
 fs [typeof_def]);

(* I don't know if this is supposed to be or not *)
val theory_ok_vfree_in = Q.prove (
`theory_ok thy ∧ c === def ∈ axsof thy ⇒ !x ty. ~VFREE_IN (Var x ty) def`,
 cheat);


val elim_def = Q.prove (
`!ctxt tm.
  ctxt |- tm
  ⇒
  !c def.
    (!ty. c ≠ Equal ty) ∧
    (c === def) ∈ SND (FST ctxt) ⇒
    ((sigof (FST ctxt), axsof (FST ctxt) DELETE (c === def)),
     MAP (remove_const c def) (SND ctxt))
    |- remove_const c def tm`,

 ho_match_mp_tac proves_strongind >>
 rw [] >>
 imp_res_tac proves_theory_ok >>
 fs [] >>
 imp_res_tac theory_ok_types >>
 rw [remove_const_eq, remove_const_def]
 >- (simp [Once proves_cases] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const c def l`, `remove_const c def r`, `ty`, `x`] >>
     first_x_assum (qspecl_then [`c`, `def`] mp_tac) >>
     simp [remove_const_eq, EVERY_MAP] >>
     rw [] >>
     fs [EVERY_MEM] >>
     rw [] >>
     metis_tac [vfree_in_remove_const, theory_ok_vfree_in])
 >- (simp [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>



     metis_tac [remove_const_eq, remove_const_def]

 simp [Once proves_cases] >>
 rw []
 metis_tac []

 >- (res_tac >>

 imp_res_tac 
 `typeof c = typeof def` by 
 
 remove_const_def, remove_const_eq]

 *)

val _ = export_theory ();

