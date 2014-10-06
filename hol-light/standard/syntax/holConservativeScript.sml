open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory listTheory pairTheory;
open optionTheory alistTheory finite_mapTheory; 
open holSyntaxLibTheory;
open holSyntaxTheory holSyntaxExtraTheory;

val _ = temp_tight_equality();
val every_case_tac = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "holConservative";

val CLOSED_INST = Q.prove (
`!tm tysubst. CLOSED tm ⇒ CLOSED (INST tysubst tm)`,
 cheat);

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

val get_type_subst_def = tDefine "get_type_subst" `
(get_type_subst s (Tyvar tv) t =
  case ALOOKUP s (Tyvar tv) of
     | NONE => SOME ((Tyvar tv,t)::s)
     | SOME t' =>
         if t = t' then
           SOME s
         else
           NONE) ∧
(get_type_subst s (Tyapp tc ts) (Tyapp tc' ts') =
  if tc = tc' then
    get_types_subst s ts ts'
  else
    NONE) ∧
(get_type_subst s _ _ = NONE) ∧
(get_types_subst s [] [] = SOME s) ∧
(get_types_subst s (t1::ts1) (t2::ts2) = 
  case get_type_subst s t1 t2 of
     | NONE => NONE
     | SOME s' => get_types_subst s' ts1 ts2) ∧
(get_types_subst s _ _ = NONE)`
(WF_REL_TAC `measure (\x. case x of INL (a,b,c) => type_size b | INR (a,b,c) => type1_size b)`);

val get_type_subst_SUBST = Q.prove (
`!s' t1 t2 s.
  get_type_subst [] t1 t2 = SOME s'
  ⇒
  TYPE_SUBST s' t1 = t2`,
 cheat);

val const_subst_ok_def = Define `
const_subst_ok s = EVERY (\(c,tm). welltyped tm ∧ CLOSED tm) s`;

val remove_const_def = Define `
(remove_const subst (Var v ty) = Var v ty) ∧
(remove_const subst (Const c ty) =
  case ALOOKUP subst c of
     | NONE => Const c ty
     | SOME tm =>
         case get_type_subst [] (typeof tm) ty of
            | NONE => Const c ty (* Can't happen *)
            | SOME tysubst => INST tysubst tm) ∧
(remove_const subst (Comb tm1 tm2) =
  Comb (remove_const subst tm1) (remove_const subst tm2)) ∧
(remove_const subst (Abs x ty tm) =
  Abs x ty (remove_const subst tm))`;

val upd_to_subst_def = Define `
(upd_to_subst (ConstSpec consts p) =
  consts) ∧
(upd_to_subst _ = [])`;

val updates_to_subst = Q.prove (
`!upd ctxt.
  upd updates ctxt 
  ⇒
  const_subst_ok (upd_to_subst upd) ∧
  ALOOKUP (upd_to_subst upd) "=" = NONE`,
 rw [updates_cases] >>
 rw [upd_to_subst_def, const_subst_ok_def] >>
 imp_res_tac proves_theory_ok >>
 imp_res_tac theory_ok_sig
 >- (imp_res_tac proves_term_ok >>
     fs [EVERY_MAP] >>
     fs [EVERY_MEM] >>
     rw [] >>
     res_tac >>
     PairCases_on `e` >>
     fs [] >>
     rfs [term_ok_equation] >>
     metis_tac [term_ok_welltyped])
 >- (fs [is_std_sig_def] >>
     CCONTR_TAC >>
     fs [ALOOKUP_NONE] >>
     imp_res_tac ALOOKUP_MEM >>
     res_tac >>
     fs [MEM_MAP] >>
     metis_tac [pair_CASES, FST, SND]));

val typeof_remove_const = Q.prove (
`!tm s. const_subst_ok s ⇒ typeof (remove_const s tm) = typeof tm`,
 Induct_on `tm` >>
 rw [remove_const_def] >>
 every_case_tac >>
 rw [] >>
 match_mp_tac WELLTYPED_LEMMA >>
 match_mp_tac INST_HAS_TYPE >>
 qexists_tac `typeof x` >>
 rw [GSYM WELLTYPED]
 >- (fs [const_subst_ok_def] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [EVERY_MEM] >>
     res_tac >>
     fs []) >>
 metis_tac [get_type_subst_SUBST]);

val remove_const_eq = Q.prove (
`const_subst_ok s ∧ ALOOKUP s "=" = NONE ⇒ 
  remove_const s (tm1 === tm2) = remove_const s tm1 === remove_const s tm2`,
 rw [equation_def, remove_const_def, typeof_remove_const]);

val has_type_remove_const = Q.prove (
`!tm ty. tm has_type ty ⇒ !s. const_subst_ok s ⇒ remove_const s tm has_type ty`,
 ho_match_mp_tac has_type_ind >>
 rw [remove_const_def]
 >- rw [Once has_type_cases]
 >- (every_case_tac >>
     fs []
     >- rw [Once has_type_cases]
     >- rw [Once has_type_cases] >>
     match_mp_tac INST_HAS_TYPE >>
     qexists_tac `typeof x` >>
     rw [GSYM WELLTYPED]
     >- (fs [const_subst_ok_def, EVERY_MEM] >>
         imp_res_tac ALOOKUP_MEM >>
         res_tac >>
         fs [])
     >- metis_tac [get_type_subst_SUBST])
 >- metis_tac [has_type_cases]
 >- rw [Once has_type_cases]);

val vfree_in_remove_const = Q.prove (
`const_subst_ok s ∧ VFREE_IN (Var x ty) (remove_const s tm) ⇒ VFREE_IN (Var x ty) tm`,
 Induct_on `tm` >>
 rw [VFREE_IN_def, remove_const_def] >>
 rw [VFREE_IN_def] >>
 every_case_tac >>
 fs [] >>
 CCONTR_TAC >>
 fs [] >>
 `CLOSED x'`
       by (fs [const_subst_ok_def, EVERY_MEM] >>
           imp_res_tac ALOOKUP_MEM >>
           res_tac >>
           fs []) >>
 metis_tac [CLOSED_INST, CLOSED_def]);

 (*
val type_ok_remove_upd = Q.prove (
`!sig ty.
  type_ok sig ty
  ⇒
  !ctxt upd.
    sig = alist_to_fmap (types_of_upd upd) ⊌ tysof ctxt
    ⇒
    type_ok (tysof ctxt) ty`,
 ho_match_mp_tac type_ok_ind >>
 rw [type_ok_def] >>

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
 *)


val update_conservative = Q.prove (
`!lhs tm.
  lhs |- tm
  ⇒
  !ctxt tms upd.
    lhs = (thyof (upd::ctxt),tms) ∧
    upd updates ctxt
    ⇒
    (thyof ctxt,MAP (remove_const (upd_to_subst upd)) tms) |- remove_const (upd_to_subst upd) tm`,
 ho_match_mp_tac proves_ind >>
 rw [] >>
 imp_res_tac updates_to_subst >>
 qabbrev_tac `s = upd_to_subst upd`
 >- (rw [Once proves_cases] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const s l`, `remove_const s r`, `ty`, `x`] >>
     rw []
     >- rw [remove_const_eq, remove_const_def]
     >- (fs [EVERY_MEM] >>
         rw [] >>
         fs [MEM_MAP] >>
         rw [] >>
         res_tac >>
         metis_tac [vfree_in_remove_const])
     >- (match_mp_tac type_ok_extend >>
         qexists_tac `tysof (sigof (thyof ctxt))` >>
         rw [] >>
         cheat)
     >- (unabbrev_all_tac >>
         first_x_assum (qspecl_then [`ctxt`, `upd`] mp_tac) >>
         rw [remove_const_eq, remove_const_def]))
 >- (rw [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>
     rw []
     >- cheat
     >- metis_tac [has_type_remove_const]
     >- cheat)
 >- (rw [Once proves_cases] >>
     disj2_tac >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const s t`, `ty`, `x`] >>
     rw [remove_const_eq, remove_const_def]
     >- cheat
     >- cheat
     >- cheat)
 >- (rw [Once proves_cases] >>
     ntac 3 disj2_tac >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const s tm`, `remove_const s tm'`, 
                            `MAP (remove_const s) h1`, `MAP (remove_const s) h2`] >>
     rw [remove_const_eq, remove_const_def]
     >- cheat
     >- cheat
     >- cheat)
 >- (rw [Once proves_cases] >>
     ntac 4 disj2_tac >>
     disj1_tac >>
     cheat)
 >- (rw [Once proves_cases] >>
     ntac 5 disj2_tac >>
     disj1_tac >>
     cheat) 
 >- (rw [Once proves_cases] >>
     ntac 6 disj2_tac >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`remove_const s tm`, `MAP (remove_const s) h`, `tyin`] >>
     rw []
     >- cheat
     >- cheat
     >- cheat
     >- cheat)
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     cheat)
 >- (rw [Once proves_cases] >>
     ntac 7 disj2_tac >>
     disj1_tac >>
     qexists_tac `remove_const s t` >>
     rw [remove_const_eq]
     >- cheat
     >- cheat)
 >- (rw [Once proves_cases] >>
     ntac 9 disj2_tac >>
     disj1_tac >>
     cheat)
 >- (cheat));

val _ = export_theory ();

