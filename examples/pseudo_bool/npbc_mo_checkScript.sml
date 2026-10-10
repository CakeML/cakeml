(*
  Checker for the restricted (multi-objective) proof format
*)
Theory npbc_mo_check
Ancestors
  pbc npbc npbc_check npbc_check_step pbc_mo npbc_mo
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*** The selected objective ordering ***)

(* The order check: the loaded order refines the reference of the ordering *)
Definition ord_ok_def:
  ord_ok mord objs aord xs = ref_ord_ok mord objs aord xs
End

(* The semantic content of an accepted order: it refines the ordering *)
Definition ord_sound_def:
  ord_sound mord objs aspo ⇔
  ∀w1 w2. po_of_aspo aspo w1 w2 ⇒
    ord_le mord (obj_vecs objs w1) (obj_vecs objs w2)
End

(* Everything the checker needs from an ordering: the order check is sound *)
Definition mo_ord_ok_def:
  mo_ord_ok mord ⇔
    ∀objs aord xs.
      ord_ok mord objs aord xs ∧ good_aspo (FST aord,xs) ⇒
      ord_sound mord objs (FST aord,xs)
End

Theorem mo_ord_ok_sound:
  ord_ok mord objs aord xs ∧ good_aspo (FST aord,xs) ∧ mo_ord_ok mord ⇒
  ord_sound mord objs (FST aord,xs)
Proof
  rw[mo_ord_ok_def]
QED

(* The multi-objective checker: every step is the single-objective
   check_cstep, except that

   - a solution is logged and banned over its own assigned variables rather
     than over the (empty) preserved set, and must have no free variables;
   - Sstep and CheckedDelete need a loaded order, because without one their
     witness carries no order relation and hence no bound on the objective
     vector;
   - a loaded order must refine the selected objective ordering. *)
Definition check_mo_cstep_def:
  check_mo_cstep mord (objs:((int # num) list # int) list) cstep
    (fml:pbf) (pc:proof_conf) (sols:int list list) =
  case cstep of
    Sol w free =>
    (let ws = list_to_num_set (MAP FST w) in
    if free = LN ∧ pc.chk ∧
      EVERY (λv. sptree$lookup v ws ≠ NONE) (mo_obj_vars objs) then
      case check_obj NONE w
        (MAP SND (toAList (mk_core_fml T fml))) NONE of
        NONE => NONE
      | SOME (new,wsol) =>
        SOME (
          insert pc.id
            (model_banning (SOME ws) LN wsol,T) fml,
          pc with <| id := pc.id+1; enum := pc.enum+1 |>,
          obj_vecs objs wsol :: sols)
    else NONE)
  | Sstep sstep =>
    (if pc.ord = NONE then NONE
    else
      case check_cstep cstep fml pc of
        NONE => NONE
      | SOME (fml',pc') => SOME (fml',pc',sols))
  | CheckedDelete n s pfs idopt =>
    (if pc.ord = NONE then NONE
    else
      case check_cstep cstep fml pc of
        NONE => NONE
      | SOME (fml',pc') => SOME (fml',pc',sols))
  | LoadOrder name xs =>
    (case ALOOKUP pc.orders name of
      NONE => NONE
    | SOME aord =>
      if ord_ok mord objs aord xs then
        (case check_cstep cstep fml pc of
          NONE => NONE
        | SOME (fml',pc') => SOME (fml',pc',sols))
      else NONE)
  | _ =>
    (case check_cstep cstep fml pc of
      NONE => NONE
    | SOME (fml',pc') => SOME (fml',pc',sols))
End

(* A logged vector already covers this assignment *)
Definition mo_esc_def:
  mo_esc mord objs sols w ⇔
    ∃v. MEM v sols ∧ ord_le mord v (obj_vecs objs w)
End

(* The checker invariant. The last conjunct is npbc's conf_valid', weakened
   so that an assignment may instead be covered by a logged vector. *)
Definition mo_conf_ok_def:
  mo_conf_ok mord objs fml pc sols ⇔
    id_ok fml pc.id ∧
    OPTION_ALL good_aspo_subst pc.ord ∧
    EVERY (good_aord_t o SND) pc.orders ∧
    pc.obj = NONE ∧ pc.pres = NONE ∧
    (pc.tcb ⇒ core_only_fml T fml ⊨ core_only_fml F fml) ∧
    ∀ord. pc.ord = SOME ord ⇒
      ord_sound mord objs (FST ord) ∧
      sat_obj_po_esc (pres_set_spt pc.pres) (SOME (FST ord)) pc.obj
        (mo_esc mord objs sols)
        (core_only_fml T fml) (core_only_fml F fml)
End

Definition check_mo_csteps_def:
  (check_mo_csteps mord (objs:((int # num) list # int) list) []
     fml pc (sols:int list list) = SOME (fml,pc,sols)) ∧
  (check_mo_csteps mord objs (s::ss) fml pc sols =
    case check_mo_cstep mord objs s fml pc sols of
      NONE => NONE
    | SOME (fml',pc',sols') => check_mo_csteps mord objs ss fml' pc' sols')
End

Definition check_mo_top_def:
  check_mo_top mord objs csteps fml id n =
  case check_mo_csteps mord objs csteps fml (init_conf id T NONE NONE) [] of
    NONE => NONE
  | SOME (fml',pc',sols) =>
    if pc'.chk ∧ check_contradiction_fml F fml' n
    then SOME (ord_min mord sols)
    else NONE
End

(* ord_sound turns the order conjunct of sat_obj_po into ord_le *)
Theorem sat_obj_po_ord_le[local]:
  ∀objs aspo pres obj s t w.
  ord_sound mord objs aspo ∧
  sat_obj_po pres (SOME aspo) obj s t ∧
  satisfies w s ⇒
  ∃w'. satisfies w' t ∧ ord_le mord (obj_vecs objs w') (obj_vecs objs w)
Proof
  rw[sat_obj_po_def]>>
  first_x_assum drule>>
  strip_tac>>
  qexists_tac`w'`>>
  simp[]>>
  gvs[ord_sound_def]
QED

(* Failing to satisfy the ban means agreeing with the logged assignment
   on every banned variable *)
Theorem model_banning_agree[local]:
  ¬satisfies_npbc w (model_banning (SOME (list_to_num_set vs)) LN wsol) ⇒
  ∀v. MEM v vs ⇒ (wsol v ⇔ w v)
Proof
  rw[satisfies_npbc_model_banning,pres_set_spt_def]>>
  gvs[EXTENSION]>>
  first_x_assum (qspec_then`v` mp_tac)>>
  simp[domain_list_to_num_set]>>
  simp[IN_DEF]
QED

(* Two assignments agreeing on a set covering every objective variable
   give the same objective vector *)
Theorem obj_vecs_agree[local]:
  EVERY (λv. MEM v vs) (mo_obj_vars (objs:((int # num) list # int) list)) ∧
  (∀v. MEM v vs ⇒ (w1 v ⇔ w2 v)) ⇒
  obj_vecs objs w1 = obj_vecs objs w2
Proof
  rw[obj_vecs_def,MAP_EQ_f]>>
  irule eval_obj_vars_cong>>
  rw[]>>
  first_x_assum irule>>
  gvs[EVERY_MEM]>>
  first_x_assum irule>>
  metis_tac[MEM_mo_obj_vars]
QED



(* ord_sound makes mo_esc upward closed along the order *)
Theorem mo_esc_upward[local]:
  mo_ord_ok mord ∧
  ord_sound mord objs aspo ⇒
  ∀x y. mo_esc mord objs sols x ∧ po_of_aspo aspo x y ⇒ mo_esc mord objs sols y
Proof
  rw[mo_esc_def,ord_sound_def]>>
  first_x_assum drule>>
  metis_tac[ord_le_trans]
QED

Theorem sat_obj_po_esc_refl[local]:
  good_aspo_subst ord ⇒
  sat_obj_po_esc pres (SOME (FST ord)) obj esc f f
Proof
  rw[]>>
  irule sat_obj_po_imp_esc>>
  irule sat_obj_po_refl>>
  gvs[good_aspo_subst_def]
QED

(* Reading the invariant's last conjunct as (a) below *)
Theorem sat_obj_po_esc_ord_le[local]:
  ord_sound mord objs aspo ∧
  sat_obj_po_esc pres (SOME aspo) obj (mo_esc mord objs sols) s t ∧
  satisfies w s ⇒
  (∃w'. satisfies w' t ∧ ord_le mord (obj_vecs objs w') (obj_vecs objs w)) ∨
  (∃v. MEM v sols ∧ ord_le mord v (obj_vecs objs w))
Proof
  rw[sat_obj_po_esc_def]>>
  first_x_assum drule>>
  rw[]
  >- (
    disj1_tac>>
    qexists_tac`w'`>>
    gvs[ord_sound_def])>>
  disj2_tac>>
  gvs[mo_esc_def]>>
  metis_tac[]
QED

(* Composing an order-only step, the invariant, and another order-only step *)
Theorem sat_obj_po_esc_compose[local]:
  mo_ord_ok mord ∧
  good_aspo (FST ord) ∧
  ord_sound mord objs (FST ord) ∧
  sat_obj_po pres (SOME (FST ord)) obj a b ∧
  sat_obj_po_esc pres (SOME (FST ord)) obj (mo_esc mord objs sols) b c ∧
  sat_obj_po pres (SOME (FST ord)) obj c d ⇒
  sat_obj_po_esc pres (SOME (FST ord)) obj (mo_esc mord objs sols) a d
Proof
  strip_tac>>
  irule sat_obj_po_esc_trans>>
  simp[]>>
  qexists_tac`c`>>
  simp[]>>
  irule sat_obj_po_trans_esc>>
  simp[]>>
  CONJ_TAC >- metis_tac[mo_esc_upward]>>
  qexists_tac`b`>>
  simp[]
QED

(* A step that moves the two core views under the loaded order preserves the
   invariant's last conjunct and gives (a) and (b) *)
Theorem mo_step_ok[local]:
  mo_ord_ok mord ∧
  ord_sound mord objs (FST ord) ∧
  good_aspo (FST ord) ∧
  sat_obj_po_esc pres (SOME (FST ord)) obj (mo_esc mord objs sols)
    (core_only_fml T fml) (core_only_fml F fml) ∧
  sat_obj_po pres (SOME (FST ord)) obj
    (core_only_fml F fml) (core_only_fml F fml') ∧
  sat_obj_po pres (SOME (FST ord)) obj
    (core_only_fml T fml') (core_only_fml T fml) ⇒
  sat_obj_po_esc pres (SOME (FST ord)) obj (mo_esc mord objs sols)
    (core_only_fml T fml') (core_only_fml F fml') ∧
  (∀w. satisfies w (core_only_fml F fml) ⇒
     (∃w'. satisfies w' (core_only_fml F fml') ∧
           ord_le mord (obj_vecs objs w') (obj_vecs objs w)) ∨
     (∃v. MEM v sols ∧ ord_le mord v (obj_vecs objs w))) ∧
  (∀w. satisfies w (core_only_fml T fml') ⇒
     ∃w'. satisfies w' (core_only_fml T fml) ∧
          ord_le mord (obj_vecs objs w') (obj_vecs objs w))
Proof
  strip_tac>>
  drule_all sat_obj_po_esc_compose>>
  strip_tac>>
  rw[]>>
  metis_tac[sat_obj_po_ord_le]
QED

(* Soundness of one step.

   (a) every solution of the old derived set is either still represented in
       the new one, or covered by a logged vector;
   (b) every core solution traces back to one of the old core, without
       increasing the objective vector;
   (c) every logged vector is weakly achieved by a real core solution.

   (b) and (c) are conditioned on chk, which unchecked deletion clears; no
   solution can be logged once it is. *)
Theorem check_mo_cstep_sound:
  mo_ord_ok mord ∧
  mo_conf_ok mord objs fml pc sols ∧
  check_mo_cstep mord objs cstep fml pc sols = SOME (fml',pc',sols') ⇒
  mo_conf_ok mord objs fml' pc' sols' ∧
  pc.id ≤ pc'.id ∧
  (pc'.chk ⇒ pc.chk) ∧
  (∀v. MEM v sols ⇒ MEM v sols') ∧
  (∀w. satisfies w (core_only_fml F fml) ⇒
     (∃w'. satisfies w' (core_only_fml F fml') ∧
           ord_le mord (obj_vecs objs w') (obj_vecs objs w)) ∨
     (∃v. MEM v sols' ∧ ord_le mord v (obj_vecs objs w))) ∧
  (pc'.chk ⇒
    ∀w. satisfies w (core_only_fml T fml') ⇒
      ∃w'. satisfies w' (core_only_fml T fml) ∧
           ord_le mord (obj_vecs objs w') (obj_vecs objs w)) ∧
  (pc'.chk ⇒
    ∀v. MEM v sols' ⇒ MEM v sols ∨
      ∃w. satisfies w (core_only_fml T fml) ∧
          ord_le mord (obj_vecs objs w) v)
Proof
  strip_tac>>
  gvs[mo_conf_ok_def]>>
  Cases_on`cstep`>>
  gvs[check_mo_cstep_def]
  >~ [`Dom`] >- (
    gvs[AllCaseEqs()]>>
    (Cases_on`pc.ord`
    >- gvs[check_cstep_def])>>
    gvs[]>>
    qspecl_then [`p`,`l`,`l0`,`o'`,`fml`,`pc`,`mo_esc mord objs sols`] mp_tac
      check_cstep_dom_str>>
    (impl_tac
    >- (
      rw[]>>
      drule_all mo_esc_upward>>
      simp[]))>>
    simp[]>>
    strip_tac>>
    gvs[conf_eq_def,good_aspo_subst_def]>>
    rw[]
    >- (
      irule sat_obj_po_trans_esc>>
      simp[]>>
      CONJ_TAC >- (
        rw[]>>
        drule_all mo_esc_upward>>
        simp[])>>
      qexists_tac`core_only_fml T fml`>>
      simp[])
    >- (
      `satisfies w (core_only_fml T fml)` by (
        irule satisfies_SUBSET>>
        irule_at Any core_only_fml_T_SUBSET_F>>
        simp[])>>
      drule_all sat_obj_po_esc_ord_le>>
      simp[])>>
    drule_all sat_obj_po_ord_le>>
    simp[])
  >~ [`Sstep`] >- (
    gvs[AllCaseEqs()]>>
    qspecl_then [`s`,`fml`,`pc`] mp_tac check_cstep_sstep_str>>
    impl_tac>>
    simp[]>>
    strip_tac>>
    Cases_on`pc.ord`>>
    gvs[conf_eq_def,good_aspo_subst_def]>>
    drule_all mo_step_ok>>
    strip_tac>>
    gvs[])
  >~ [`CheckedDelete`] >- (
    gvs[AllCaseEqs()]>>
    qspecl_then [`n`,`l`,`l0`,`o'`,`fml`,`pc`] mp_tac
      check_cstep_checkeddelete_str>>
    impl_tac>>
    simp[]>>
    strip_tac>>
    Cases_on`pc.ord`>>
    gvs[conf_eq_def,good_aspo_subst_def]>>
    drule_all mo_step_ok>>
    strip_tac>>
    gvs[])
  >~ [`UncheckedDelete`] >- (
    gvs[AllCaseEqs(),check_cstep_def]>>
    drule id_ok_FOLDL_delete>>
    strip_tac>>
    `core_only_fml F (FOLDL (\a b. delete b a) fml l) ⊆ core_only_fml F fml` by (
      rw[core_only_fml_def,SUBSET_DEF]>>
      fs[lookup_FOLDL_delete]>>
      metis_tac[])>>
    `all_core fml ⇒ all_core (FOLDL (\a b. delete b a) fml l)` by (
      strip_tac>>
      fs[all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD]>>
      rw[lookup_FOLDL_delete]>>
      metis_tac[])>>
    Cases_on`pc.ord`>>
    gvs[all_core_core_only_fml_eq]>>
    rw[sat_obj_po_esc_refl,sat_implies_def]>>
    disj1_tac>>
    qexists_tac`w`>>
    simp[]>>
    drule_all satisfies_SUBSET>>
    simp[])
  >~ [`Transfer`] >- (
    gvs[AllCaseEqs(),check_cstep_def]>>
    drule do_transfer_props>>
    strip_tac>>
    gvs[id_ok_def]>>
    rw[]
    >- (gvs[sat_implies_def]>>metis_tac[satisfies_SUBSET])
    >- metis_tac[sat_obj_po_esc_more]
    >- metis_tac[ord_le_refl]>>
    metis_tac[satisfies_SUBSET,ord_le_refl])
  >~ [`StrengthenToCore`] >- (
    gvs[AllCaseEqs(),check_cstep_def]>>
    Cases_on`pc.ord`>>
    gvs[OPTION_ALL_def]>>
    rw[core_only_fml_map_core,id_ok_map,sat_obj_po_esc_refl]>>
    metis_tac[ord_le_refl,satisfies_SUBSET,core_only_fml_T_SUBSET_F])
  >~ [`LoadOrder`] >- (
    gvs[AllCaseEqs(),check_cstep_def]>>
    drule ALOOKUP_MEM>>
    fs[EVERY_MEM,Once FORALL_PROD]>>
    strip_tac>>
    first_x_assum drule>>
    PairCases_on`aord`>>
    simp[good_aord_t_def]>>
    strip_tac>>
    first_x_assum drule>>
    strip_tac>>
    drule mo_ord_ok_sound>>
    (impl_tac >- simp[])>>
    strip_tac>>
    `∀b. core_only_fml b (map (λ(c,b). (c,T)) fml) = core_only_fml F fml` by
      simp[core_only_fml_map_core]>>
    gvs[id_ok_map,mk_ordsub_def]>>
    rw[]
    >- simp[good_aspo_subst_def,good_ord_s_def]
    >- (
      irule sat_obj_po_imp_esc>>
      irule sat_obj_po_refl>>
      simp[])
    >- (
      disj1_tac>>
      qexists_tac`w`>>
      simp[])>>
    qexists_tac`w`>>
    simp[]>>
    irule satisfies_SUBSET>>
    irule_at Any core_only_fml_T_SUBSET_F>>
    simp[])
  >~ [`UnloadOrder`] >- (
    gvs[AllCaseEqs(),check_cstep_def]>>
    rw[]>>
    metis_tac[ord_le_refl])
  >~ [`StoreOrder`] >- (
    gvs[AllCaseEqs()]>>
    drule_all check_cstep_storeorder_str>>
    strip_tac>>
    gvs[]>>
    rw[]>>
    metis_tac[ord_le_refl])
  >~ [`Obj`] >- (
    gvs[AllCaseEqs(),check_cstep_def]>>
    rw[]>>
    metis_tac[ord_le_refl])
  >~ [`model_banning`] >- (
    gvs[AllCaseEqs(),lookup_list_to_num_set]>>
    `pc.id ∉ domain fml` by gvs[id_ok_def]>>
    drule check_obj_imp>>
    strip_tac>>
    `satisfies wsol (core_only_fml T fml)` by
      gvs[GSYM range_mk_core_fml,range_toAList]>>
    `∀w. ¬satisfies_npbc w
        (model_banning (SOME (list_to_num_set (MAP FST l))) LN wsol) ⇒
       obj_vecs objs w = obj_vecs objs wsol` by (
      rw[]>>
      drule model_banning_agree>>
      strip_tac>>
      irule obj_vecs_agree>>
      qexists_tac`MAP FST l`>>
      metis_tac[])>>
    DEP_REWRITE_TAC[core_only_fml_T_insert_T,core_only_fml_F_insert_b]>>
    simp[]>>
    rw[]
    >- simp[id_ok_insert_1]
    >- metis_tac[sat_implies_INSERT]
    >- (
      first_x_assum drule>>
      strip_tac>>
      gvs[sat_obj_po_esc_def,pres_set_spt_def]>>
      rw[]>>
      first_x_assum drule>>
      rw[]
      >- (
        Cases_on`satisfies_npbc w'
          (model_banning (SOME (list_to_num_set (MAP FST l))) LN wsol)`
        >- (
          disj1_tac>>
          qexists_tac`w'`>>
          simp[])>>
        disj2_tac>>
        simp[mo_esc_def]>>
        qexists_tac`obj_vecs objs wsol`>>
        simp[]>>
        `obj_vecs objs w' = obj_vecs objs wsol` by (
          first_x_assum irule>>
          simp[])>>
        gvs[ord_sound_def]>>
        metis_tac[])>>
      disj2_tac>>
      gvs[mo_esc_def]>>
      metis_tac[])
    >- (
      Cases_on`satisfies_npbc w
        (model_banning (SOME (list_to_num_set (MAP FST l))) LN wsol)`
      >- (
        disj1_tac>>
        qexists_tac`w`>>
        simp[])>>
      disj2_tac>>
      qexists_tac`obj_vecs objs wsol`>>
      `obj_vecs objs w = obj_vecs objs wsol` by (
        first_x_assum irule>>
        simp[])>>
      simp[])
    >- (
      qexists_tac`w`>>
      simp[])
    >- (
      disj2_tac>>
      qexists_tac`wsol`>>
      simp[])>>
    simp[])>>
  gvs[check_cstep_def,check_change_obj_def,check_eq_obj_def,
      check_change_pres_def,check_eq_pres_def]
QED

(* Soundness of a whole run: the paper's Lemmas 2 and 3 *)
Theorem check_mo_csteps_sound:
  ∀csteps mord objs fml pc sols fml' pc' sols'.
  mo_ord_ok mord ∧
  mo_conf_ok mord objs fml pc sols ∧
  check_mo_csteps mord objs csteps fml pc sols = SOME (fml',pc',sols') ⇒
  mo_conf_ok mord objs fml' pc' sols' ∧
  pc.id ≤ pc'.id ∧
  (pc'.chk ⇒ pc.chk) ∧
  (∀v. MEM v sols ⇒ MEM v sols') ∧
  (∀w. satisfies w (core_only_fml F fml) ⇒
     (∃w'. satisfies w' (core_only_fml F fml') ∧
           ord_le mord (obj_vecs objs w') (obj_vecs objs w)) ∨
     (∃v. MEM v sols' ∧ ord_le mord v (obj_vecs objs w))) ∧
  (pc'.chk ⇒
    ∀w. satisfies w (core_only_fml T fml') ⇒
      ∃w'. satisfies w' (core_only_fml T fml) ∧
           ord_le mord (obj_vecs objs w') (obj_vecs objs w)) ∧
  (pc'.chk ⇒
    ∀v. MEM v sols' ⇒ MEM v sols ∨
      ∃w. satisfies w (core_only_fml T fml) ∧
          ord_le mord (obj_vecs objs w) v)
Proof
  Induct
  >- (
    rw[check_mo_csteps_def]>>
    metis_tac[ord_le_refl])>>
  rpt gen_tac>>
  strip_tac>>
  gvs[check_mo_csteps_def,AllCaseEqs()]>>
  drule_all check_mo_cstep_sound>>
  strip_tac>>
  first_x_assum drule_all>>
  strip_tac>>
  rw[]
  >- (
    qpat_x_assum `∀w. satisfies w (core_only_fml F fml) ⇒ _` drule>>
    rw[]
    >- (
      qpat_x_assum `∀w. satisfies w (core_only_fml F fml'') ⇒ _` drule>>
      rw[]>>
      drule_all ord_le_trans>>
      metis_tac[])>>
    metis_tac[])
  >- (
    gvs[]>>
    qpat_x_assum `∀w. satisfies w (core_only_fml T fml') ⇒ _` drule>>
    strip_tac>>
    qpat_x_assum `∀w. satisfies w (core_only_fml T fml'') ⇒ _` drule>>
    strip_tac>>
    drule_all ord_le_trans>>
    metis_tac[])>>
  gvs[]>>
  qpat_x_assum `∀v. MEM v sols' ⇒ _` drule>>
  rw[]
  >- metis_tac[]>>
  qpat_x_assum `∀w. satisfies w (core_only_fml T fml'') ⇒ _` drule>>
  strip_tac>>
  drule_all ord_le_trans>>
  metis_tac[]
QED

(* The printed front is the non-dominated set of the input, up to the
  ordering's equivalence: it meets every minimal equivalence class exactly
  once. A printed vector is equivalent to, but not necessarily equal to, an
  achievable minimal vector *)
Theorem check_mo_top_sound:
  mo_ord_ok mord ∧
  all_core fml ∧
  id_ok fml id ∧
  check_mo_top mord objs csteps fml id n = SOME vs ⇒
  is_front mord vs (nondom_set mord (core_only_fml T fml) objs)
Proof
  rw[check_mo_top_def,AllCaseEqs()]>>
  `mo_conf_ok mord objs fml (init_conf id T NONE NONE) []` by
    simp[mo_conf_ok_def,init_conf_def]>>
  drule_all check_mo_csteps_sound>>
  strip_tac>>
  drule check_contradiction_fml_unsat>>
  strip_tac>>
  `core_only_fml T fml = core_only_fml F fml` by
    metis_tac[all_core_core_only_fml_eq]>>
  gvs[unsatisfiable_def,satisfiable_def]>>
  irule is_front_set_equiv>>
  irule_at Any ord_min_is_front>>
  simp[nondom_set_def]>>
  irule min_set_dom_ord>>
  rw[in_obj_img]>>
  metis_tac[]
QED

(* Every ordering the checker accepts satisfies its requirements *)
Theorem mo_ord_ok_thm:
  mo_ord_ok mord
Proof
  rw[mo_ord_ok_def,ord_ok_def,ord_sound_def]>>
  PairCases_on`aord`>>
  gvs[]>>
  irule ref_ord_ok_sound>>
  metis_tac[]
QED
