(*
  Checker for the restricted (multi-objective) proof format
*)
Theory npbc_mo_check
Ancestors
  pbc npbc npbc_check pbc_mo npbc_mo
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*** The Pareto dominance order ***)

(* The variables occurring in a list of objectives *)
Definition mo_obj_vars_def:
  mo_obj_vars objs = FLAT (MAP (λ(f,c). MAP SND f) objs)
End

(* Order objective terms by variable *)
Definition var_le_def[simp]:
  var_le ((_:int),u:num) ((_:int),v:num) ⇔ u ≤ v
End

(* Rename the variables of an objective through rn, restoring the order by
  variable that obj_constraint's add_lists (npbcScript.sml) requires *)
Definition rename_obj_def:
  rename_obj rn ((f,c):((int # var) list # int)) =
    (sort var_le
      (MAP (λ(a,v). (a, case sptree$lookup v rn of NONE => v | SOME u => u)) f), c)
End

(* The substitution described by su *)
Definition vs_to_us_def:
  vs_to_us su v =
    case sptree$lookup v su of
      NONE => NONE
    | SOME u => SOME (INR (Pos u))
End

(* One constraint per objective, each saying O(us) ≤ O(vs) *)
Definition pareto_constrs_def:
  pareto_constrs objs xvars us vs =
    let su = list_list_insert vs us in
    let rn = list_list_insert xvars vs in
      MAP (λob. obj_constraint (vs_to_us su) (rename_obj rn ob)) objs
End

(* Some constraint in cs implies c *)
Definition check_imp_any_def:
  check_imp_any c cs =
    EXISTS (λd. imp d c) cs
End

(* An order is accepted when it has no auxiliaries, no specification, and
  each Pareto constraint follows from one of its constraints *)
Definition pareto_ord_ok_def:
  pareto_ord_ok objs (((f,g,us,vs,as),asv):aord_s) xs ⇔
    as = [] ∧ g = [] ∧
    EVERY SND xs ∧
    (let xsv = list_to_num_set (MAP FST xs) in
      EVERY (λv. sptree$lookup v xsv ≠ NONE) (mo_obj_vars objs)) ∧
    EVERY (λc. check_imp_any c f)
      (pareto_constrs objs (MAP FST xs) us vs)
End

(* With no auxiliary variables, the specification obligation is vacuous *)
Theorem the_spec_NIL:
  the_spec fml [] ws w ⇔ ws = [] ∧ satisfies w fml
Proof
  Cases_on`ws`>>simp[the_spec_def]>>
  qmatch_goalsub_abbrev_tac`satisfies (assign al w) fml`>>
  `assign al w = w` by
    simp[FUN_EQ_THM,assign_def,Abbr`al`]>>
  simp[]
QED

Theorem po_of_aspo_no_aux:
  po_of_aspo ((f,[],us,vs,[]),xs) w1 w2 ⇔
  ∃ww. satisfies
    (assign (ALOOKUP
      (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww) (set f)
Proof
  rw[po_of_aspo_def,the_spec_NIL]>>
  metis_tac[]
QED

(* Renaming an objective and evaluating agrees with the original *)
Theorem eval_obj_rename_obj:
  (∀v. MEM v (MAP SND (FST ob)) ⇒
     B (case sptree$lookup v rn of NONE => v | SOME u => u) = w v) ⇒
  eval_obj (SOME (rename_obj rn ob)) B = eval_obj (SOME ob) w
Proof
  PairCases_on`ob`>>
  rw[rename_obj_def,eval_obj_def]>>
  `SUM (MAP (eval_term B) (sort var_le
     (MAP (λ(a,v). (a, case sptree$lookup v rn of NONE => v | SOME u => u)) ob0))) =
   SUM (MAP (eval_term B)
     (MAP (λ(a,v). (a, case sptree$lookup v rn of NONE => v | SOME u => u)) ob0))` by (
    irule PERM_SUM>>
    irule PERM_MAP>>
    metis_tac[mllistTheory.sort_PERM,PERM_SYM])>>
  pop_assum SUBST_ALL_TAC>>
  simp[MAP_MAP_o]>>
  AP_TERM_TAC>>
  rw[MAP_EQ_f,FORALL_PROD]>>
  gvs[MEM_MAP,PULL_EXISTS]>>
  first_x_assum drule>>
  simp[]
QED

(* The ambient assignment of the order reads off w1 on us and w2 on vs *)
Theorem assign_ord_EL[local]:
  ∀us vs xs w1 w2 ww j.
  ALL_DISTINCT (us ++ vs) ∧
  LENGTH us = LENGTH xs ∧ LENGTH vs = LENGTH xs ∧
  EVERY SND xs ∧ j < LENGTH xs ⇒
  assign (ALOOKUP
    (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww (EL j us) =
    w1 (EL j (MAP FST xs)) ∧
  assign (ALOOKUP
    (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww (EL j vs) =
    w2 (EL j (MAP FST xs))
Proof
  rpt gen_tac>>strip_tac>>
  gvs[ALL_DISTINCT_APPEND]>>
  `ALOOKUP (ZIP (us,xs)) (EL j us) = SOME (EL j xs)` by
    (irule ALOOKUP_ALL_DISTINCT_EL_IMP>>simp[])>>
  `ALOOKUP (ZIP (us,xs)) (EL j vs) = NONE` by
    (irule IMP_ALOOKUP_NONE>>
    simp[]>>
    metis_tac[MEM_EL])>>
  `ALOOKUP (ZIP (vs,xs)) (EL j vs) = SOME (EL j xs)` by
    (irule ALOOKUP_ALL_DISTINCT_EL_IMP>>simp[])>>
  `SND (EL j xs)` by metis_tac[EVERY_EL]>>
  simp[ALOOKUP_APPEND,assign_def,get_bits_def,EL_MAP]
QED

Theorem ALOOKUP_ZIP_index[local]:
  ∀v xvars ys.
  MEM v xvars ∧ LENGTH xvars = LENGTH ys ⇒
  ∃k. k < LENGTH ys ∧ EL k xvars = v ∧
      ALOOKUP (ZIP (xvars,ys)) v = SOME (EL k ys)
Proof
  rw[]>>
  `ALOOKUP (ZIP (xvars,ys)) v ≠ NONE` by
    simp[ALOOKUP_NONE,MAP_ZIP]>>
  Cases_on`ALOOKUP (ZIP (xvars,ys)) v`>>gvs[]>>
  drule ALOOKUP_MEM>>
  simp[MEM_ZIP]>>
  rw[]>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Theorem MEM_mo_obj_vars:
  MEM ob objs ∧ MEM v (MAP SND (FST ob)) ⇒
  MEM v (mo_obj_vars objs)
Proof
  rw[mo_obj_vars_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
  qexists_tac`ob`>>
  PairCases_on`ob`>>gvs[MEM_MAP]>>
  metis_tac[]
QED


(* An objective's variables are all order variables *)
Theorem mo_obj_vars_SUBSET[local]:
  EVERY (λv. MEM v (MAP FST (xs:(num # bool) list)))
    (mo_obj_vars (objs:((int # num) list # int) list)) ∧
  MEM ob objs ⇒
  ∀u. MEM u (MAP SND (FST ob)) ⇒ MEM u (MAP FST xs)
Proof
  rw[EVERY_MEM]>>
  first_x_assum irule>>
  metis_tac[MEM_mo_obj_vars]
QED

(* Every Pareto constraint follows from the accepted order *)
Theorem pareto_constrs_sat[local]:
  ∀f objs xvars us vs ob A.
  EVERY (λc. check_imp_any c f) (pareto_constrs objs xvars us vs) ⇒
  MEM ob objs ⇒
  satisfies A (set f) ⇒
  satisfies_npbc A (obj_constraint (vs_to_us (list_list_insert vs us))
    (rename_obj (list_list_insert xvars vs) ob))
Proof
  rpt gen_tac>>
  rw[pareto_constrs_def,check_imp_any_def,EVERY_MAP,EVERY_MEM,MEM_MAP,
    PULL_EXISTS]>>
  first_x_assum drule>>
  simp[EXISTS_MEM]>>
  strip_tac>>
  gvs[satisfies_def]>>
  metis_tac[imp_thm]
QED

(* Each objective variable is read off the us side as w1 and the vs side as w2 *)
Theorem ord_lookup_vals[local]:
  ∀vs us xs A w1 w2 v.
  ALL_DISTINCT vs ⇒
  LENGTH us = LENGTH vs ⇒
  LENGTH vs = LENGTH xs ⇒
  (∀j. j < LENGTH xs ⇒
     A (EL j us) = w1 (EL j (MAP FST xs)) ∧
     A (EL j vs) = w2 (EL j (MAP FST xs))) ⇒
  MEM v (MAP FST xs) ⇒
  A (case sptree$lookup v (list_list_insert (MAP FST xs) vs) of
       NONE => v | SOME u => u) = w2 v ∧
  assign (vs_to_us (list_list_insert vs us)) A
    (case sptree$lookup v (list_list_insert (MAP FST xs) vs) of
       NONE => v | SOME u => u) = w1 v
Proof
  rpt gen_tac>>rpt strip_tac>>
  rewrite_tac[lookup_list_list_insert]>>
  `∃k. k < LENGTH vs ∧ EL k (MAP FST xs) = v ∧
     ALOOKUP (ZIP (MAP FST xs,vs)) v = SOME (EL k vs)` by
    metis_tac[ALOOKUP_ZIP_index,LENGTH_MAP]>>
  gvs[]>>
  `ALOOKUP (ZIP (vs,us)) (EL k vs) = SOME (EL k us)` by
    (irule ALOOKUP_ALL_DISTINCT_EL_IMP>>simp[])>>
  first_x_assum drule>>
  simp[vs_to_us_def,assign_def,lookup_list_list_insert]
QED

Theorem pareto_ord_ok_sound:
  pareto_ord_ok objs (((f,g,us,vs,as),asv):aord_s) xs ∧
  good_aspo ((f,g,us,vs,as),xs) ∧
  po_of_aspo ((f,g,us,vs,as),xs) w1 w2 ⇒
  vec_le (obj_vecs objs w1) (obj_vecs objs w2)
Proof
  simp[pareto_ord_ok_def,lookup_list_to_num_set]>>
  strip_tac>>
  gvs[po_of_aspo_no_aux,good_aspo_def,good_aord_def,ALL_DISTINCT_APPEND]>>
  simp[vec_le_obj_vecs,EVERY_MEM]>>
  rw[]>>
  `∀j. j < LENGTH xs ⇒
     assign (ALOOKUP
       (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww (EL j us) =
       w1 (EL j (MAP FST xs)) ∧
     assign (ALOOKUP
       (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww (EL j vs) =
       w2 (EL j (MAP FST xs))` by (
    rpt strip_tac>>
    qspecl_then [`us`,`vs`,`xs`,`w1`,`w2`,`ww`,`j`] mp_tac assign_ord_EL>>
    simp[ALL_DISTINCT_APPEND])>>
  qabbrev_tac`A = assign (ALOOKUP
    (ZIP (us,get_bits w1 xs) ++ ZIP (vs,get_bits w2 xs))) ww`>>
  `LENGTH vs = LENGTH xs` by simp[]>>
  (* the reference constraint for ob is satisfied *)
  qspecl_then [`f`,`objs`,`MAP FST xs`,`us`,`vs`,`ob`,`A`] mp_tac
    pareto_constrs_sat>>
  simp[]>>
  strip_tac>>
  qpat_x_assum`satisfies_npbc _ _` mp_tac>>
  rewrite_tac[satisfies_npbc_obj_constraint]>>
  strip_tac>>
  mp_tac mo_obj_vars_SUBSET>>
  simp[]>>
  strip_tac>>
  `eval_obj (SOME (rename_obj (list_list_insert (MAP FST xs) vs) ob)) A =
     eval_obj (SOME ob) w2 ∧
   eval_obj (SOME (rename_obj (list_list_insert (MAP FST xs) vs) ob))
     (assign (vs_to_us (list_list_insert vs us)) A) = eval_obj (SOME ob) w1` by (
    conj_tac>>
    irule eval_obj_rename_obj>>
    rw[]>>
    first_x_assum drule>>
    strip_tac>>
    drule_all ord_lookup_vals>>
    simp[])>>
  qpat_x_assum`eval_obj _ (assign _ _) ≤ _` mp_tac>>
  asm_rewrite_tac[]
QED

(* An objective depends only on its own variables *)
Theorem eval_obj_vars_cong:
  (∀v. MEM v (MAP SND (FST ob)) ⇒ (w1 v ⇔ w2 v)) ⇒
  eval_obj (SOME ob) w1 = eval_obj (SOME ob) w2
Proof
  Cases_on`ob`>>
  rw[eval_obj_def]>>
  AP_TERM_TAC>>
  irule MAP_CONG>>
  rw[]>>
  rename1`MEM cv _`>>
  PairCases_on`cv`>>
  gvs[eval_lit_def]>>
  `w1 cv1 ⇔ w2 cv1` by (
    first_x_assum irule>>
    simp[MEM_MAP]>>
    qexists_tac`(cv0,cv1)`>>
    simp[])>>
  simp[]
QED

(* The semantic content of an accepted order: it refines Pareto dominance *)
Definition pareto_sound_def:
  pareto_sound objs aspo ⇔
  ∀w1 w2. po_of_aspo aspo w1 w2 ⇒
    vec_le (obj_vecs objs w1) (obj_vecs objs w2)
End

Theorem pareto_ord_ok_pareto_sound:
  pareto_ord_ok objs aord xs ∧
  good_aspo (FST aord,xs) ⇒
  pareto_sound objs (FST aord,xs)
Proof
  PairCases_on`aord`>>
  rename1`((f,g,us,vs,as),asv)`>>
  rw[pareto_sound_def]>>
  irule pareto_ord_ok_sound>>
  metis_tac[]
QED

(*** The selected objective ordering ***)

(* The order check for each ordering *)
Definition ord_ok_def:
  ord_ok Pareto objs aord xs = pareto_ord_ok objs aord xs
End

(* The semantic content of an accepted order: it refines the ordering *)
Definition ord_sound_def:
  ord_sound mord objs aspo ⇔
  ∀w1 w2. po_of_aspo aspo w1 w2 ⇒
    ord_le mord (obj_vecs objs w1) (obj_vecs objs w2)
End

(* Everything the checker needs from an ordering *)
Definition mo_ord_ok_def:
  mo_ord_ok mord ⇔
    good_mo_ord mord ∧
    ∀objs aord xs.
      ord_ok mord objs aord xs ∧ good_aspo (FST aord,xs) ⇒
      ord_sound mord objs (FST aord,xs)
End

Theorem mo_ord_ok_refl:
  mo_ord_ok mord ⇒ ord_le mord x x
Proof
  rw[mo_ord_ok_def,good_mo_ord_def]
QED

Theorem mo_ord_ok_trans:
  mo_ord_ok mord ∧ ord_le mord x y ∧ ord_le mord y z ⇒ ord_le mord x z
Proof
  rw[mo_ord_ok_def,good_mo_ord_def]>>
  metis_tac[]
QED

Theorem mo_ord_ok_sound:
  ord_ok mord objs aord xs ∧ good_aspo (FST aord,xs) ∧ mo_ord_ok mord ⇒
  ord_sound mord objs (FST aord,xs)
Proof
  rw[mo_ord_ok_def]
QED

(* The multi-objective checker: every step is the single-objective
   check_cstep, except that

   - a solution is logged and banned over its own assigned variables rather
     than over the (empty) preserved set;
   - Sstep and CheckedDelete need a loaded order, because without one their
     witness carries no order relation and hence no bound on the objective
     vector;
   - a loaded order must refine the selected objective ordering. *)
Definition check_mo_cstep_def:
  check_mo_cstep mord (objs:((int # num) list # int) list) cstep
    (fml:pbf) (pc:proof_conf) (sols:int list list) =
  case cstep of
    Sol w =>
    (let ws = list_to_num_set (MAP FST w) in
    if pc.chk ∧ EVERY (λv. sptree$lookup v ws ≠ NONE) (mo_obj_vars objs) then
      case check_obj NONE w
        (MAP SND (toAList (mk_core_fml T fml))) NONE of
        NONE => NONE
      | SOME (new,wsol) =>
        SOME (
          insert pc.id
            (model_banning (SOME ws) wsol,T) fml,
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
  ¬satisfies_npbc w (model_banning (SOME (list_to_num_set vs)) wsol) ⇒
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
  metis_tac[mo_ord_ok_trans]
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
  gvs[check_mo_cstep_def,check_cstep_def,
      check_cstep_changeobj_def,check_change_obj_def,
      check_cstep_checkobj_def,check_eq_obj_def,
      check_cstep_assertobj_def,
      check_cstep_changepres_def,check_change_pres_def,
      check_cstep_checkpres_def,check_eq_pres_def]
  >~ [`check_cstep_dom`] >- (
    gvs[AllCaseEqs()]>>
    (Cases_on`pc.ord`
    >- gvs[check_cstep_dom_def])>>
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
  >~ [`check_cstep_sstep`] >- (
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
  >~ [`check_cstep_checkeddelete`] >- (
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
  >~ [`check_cstep_uncheckeddelete`] >- (
    gvs[AllCaseEqs(),check_cstep_uncheckeddelete_def]>>
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
    simp[mo_ord_ok_refl]>>
    drule_all satisfies_SUBSET>>
    simp[])
  >~ [`check_cstep_transfer`] >- (
    gvs[AllCaseEqs(),check_cstep_transfer_def]>>
    drule do_transfer_props>>
    strip_tac>>
    gvs[id_ok_def]>>
    rw[]
    >- (gvs[sat_implies_def]>>metis_tac[satisfies_SUBSET])
    >- metis_tac[sat_obj_po_esc_more]
    >- metis_tac[mo_ord_ok_refl]>>
    metis_tac[satisfies_SUBSET,mo_ord_ok_refl])
  >~ [`check_cstep_strengthentocore`] >- (
    gvs[AllCaseEqs(),check_cstep_strengthentocore_def]>>
    Cases_on`pc.ord`>>
    gvs[OPTION_ALL_def]>>
    rw[core_only_fml_map_core,id_ok_map,sat_obj_po_esc_refl]>>
    metis_tac[mo_ord_ok_refl,satisfies_SUBSET,core_only_fml_T_SUBSET_F])
  >~ [`check_cstep_loadorder`] >- (
    gvs[AllCaseEqs(),check_cstep_loadorder_def]>>
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
      simp[mo_ord_ok_refl])>>
    qexists_tac`w`>>
    simp[mo_ord_ok_refl]>>
    irule satisfies_SUBSET>>
    irule_at Any core_only_fml_T_SUBSET_F>>
    simp[])
  >~ [`check_cstep_unloadorder`] >- (
    gvs[AllCaseEqs(),check_cstep_unloadorder_def]>>
    rw[]>>
    metis_tac[mo_ord_ok_refl])
  >~ [`check_cstep_storeorder`] >- (
    gvs[AllCaseEqs()]>>
    drule_all check_cstep_storeorder_str>>
    strip_tac>>
    gvs[]>>
    rw[]>>
    metis_tac[mo_ord_ok_refl])
  >~ [`check_cstep_obj`] >- (
    gvs[AllCaseEqs(),check_cstep_obj_def]>>
    rw[]>>
    metis_tac[mo_ord_ok_refl])
  >- (
    gvs[AllCaseEqs(),lookup_list_to_num_set]>>
    `pc.id ∉ domain fml` by gvs[id_ok_def]>>
    drule check_obj_imp>>
    strip_tac>>
    `satisfies wsol (core_only_fml T fml)` by
      gvs[GSYM range_mk_core_fml,range_toAList]>>
    `∀w. ¬satisfies_npbc w
        (model_banning (SOME (list_to_num_set (MAP FST l))) wsol) ⇒
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
          (model_banning (SOME (list_to_num_set (MAP FST l))) wsol)`
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
        (model_banning (SOME (list_to_num_set (MAP FST l))) wsol)`
      >- (
        disj1_tac>>
        qexists_tac`w`>>
        simp[mo_ord_ok_refl])>>
      disj2_tac>>
      qexists_tac`obj_vecs objs wsol`>>
      `obj_vecs objs w = obj_vecs objs wsol` by (
        first_x_assum irule>>
        simp[])>>
      simp[mo_ord_ok_refl])
    >- (
      qexists_tac`w`>>
      simp[mo_ord_ok_refl])
    >- (
      disj2_tac>>
      qexists_tac`wsol`>>
      simp[mo_ord_ok_refl])>>
    simp[])
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
    metis_tac[mo_ord_ok_refl])>>
  rpt gen_tac>>
  strip_tac>>
  gvs[check_mo_csteps_def,AllCaseEqs()]>>
  drule_all check_mo_cstep_sound>>
  strip_tac>>
  first_x_assum drule_all>>
  strip_tac>>
  rw[]>>
  metis_tac[mo_ord_ok_trans]
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
  Cases_on`mord`>>
  rw[mo_ord_ok_def,ord_ok_def,ord_sound_def,ord_le_def]>>
  drule_all pareto_ord_ok_pareto_sound>>
  simp[pareto_sound_def]
QED
