(*
  Refine the multi-objective PB proof checker to use arrays
*)
Theory npbc_mo_list
Ancestors
  npbc_check npbc_mo_check npbc_slot npbc_list
Libs
  preamble

Definition list_conf_rel_def:
  list_conf_rel fml fmlls assg st inds vimap vomap (pc:proof_conf) ⇔
    fml_rel fml fmlls ∧
    rup_inv fmlls assg st ∧
    ind_rel fmlls inds ∧
    vimap_rel fmlls vimap ∧
    vomap_rel pc.obj vomap ∧
    (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty)
End

Theorem fml_rel_check_cstep_list_conf_rel:
  list_conf_rel fml fmlls assg st inds vimap vomap pc ∧
  check_cstep_list cstep fmlls assg st inds vimap vomap pc =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc') ⇒
  ∃fml'.
    check_cstep cstep fml pc = SOME (fml', pc') ∧
    list_conf_rel fml' fmlls' assg' st' inds' vimap' vomap' pc' ∧
    pc.id ≤ pc'.id
Proof
  rw[list_conf_rel_def]>>
  drule_all fml_rel_check_cstep_list>>
  rw[]>>
  metis_tac[]
QED

(* Every objective variable must be assigned by a logged solution.
  The assignment's domain is the num_set that model_banning bans over *)
Definition mo_vars_covered_def:
  mo_vars_covered objs (ws:num_set) ⇔
  EVERY (λv. sptree$lookup v ws ≠ NONE) (mo_obj_vars objs)
End

(* The multi-objective solution-logging step bans the logged assignment
  over its own domain, so it cannot share the Sol case of check_cstep_list *)
Definition check_mo_cstep_sol_list_def:
  check_mo_cstep_sol_list objs w (free:num_set)
    (fml: slot list) assg st (inds:num list)
    vimap vomap (pc:proof_conf) sols =
  (let ws = list_to_num_set (MAP FST w) in
  if free = LN ∧ pc.chk ∧ mo_vars_covered objs ws then
    case check_obj_core NONE w fml inds NONE of
      NONE => NONE
    | SOME (new,wsol) =>
      let rinds = reindex fml inds in
      let c = model_banning (SOME ws) LN wsol in
      let (s,mv) = enc_mv c T in
      let (fml',inds',vimap',id',assg',st') =
        store_ind fml s mv pc.id rinds vimap assg st in
      SOME (
        fml', assg', st', inds', vimap', vomap,
        pc with <| id := id'; enum := pc.enum+1 |>,
        obj_vecs objs wsol :: sols)
  else NONE)
End

(* Solution logging is the one step that is not delegated *)
Definition get_sol_def:
  (get_sol (Sol w free) = SOME (w,free)) ∧
  (get_sol _ = NONE)
End

(* The multi-objective side conditions on the delegated steps *)
Definition mo_cstep_ok_def:
  mo_cstep_ok mord objs cstep (pc:proof_conf) ⇔
  case cstep of
    Sstep _ => pc.ord ≠ NONE
  | CheckedDelete _ _ _ _ => pc.ord ≠ NONE
  | LoadOrder name xs =>
    (case ALOOKUP pc.orders name of
      NONE => F
    | SOME aord => ord_ok mord objs aord xs)
  | _ => T
End

Definition check_mo_cstep_list_def:
  check_mo_cstep_list mord objs cstep fml assg st inds vimap vomap pc sols =
  case get_sol cstep of
    SOME (w,free) =>
      check_mo_cstep_sol_list objs w free fml assg st inds vimap vomap pc sols
  | NONE =>
    if mo_cstep_ok mord objs cstep pc then
      (case check_cstep_list cstep fml assg st inds vimap vomap pc of
        NONE => NONE
      | SOME (fml',assg',st',inds',vimap',vomap',pc') =>
        SOME (fml',assg',st',inds',vimap',vomap',pc',sols))
    else NONE
End

Definition check_mo_csteps_list_def:
  (check_mo_csteps_list mord objs [] fml assg st inds vimap vomap pc sols =
    SOME (fml, assg, st, inds, vimap, vomap, pc, sols)) ∧
  (check_mo_csteps_list mord objs (c::cs) fml assg st inds vimap vomap pc sols =
    case check_mo_cstep_list mord objs c fml assg st inds vimap vomap pc sols of
      NONE => NONE
    | SOME(fml', assg', st', inds', vimap', vomap', pc', sols') =>
      check_mo_csteps_list mord objs cs fml' assg' st' inds' vimap' vomap' pc'
        sols')
End

Definition check_mo_top_list_def:
  check_mo_top_list mord objs csteps fml assg st inds vimap vomap id n =
  case check_mo_csteps_list mord objs csteps fml assg st inds vimap vomap
    (init_conf id T NONE NONE) [] of
    NONE => NONE
  | SOME (fml',assg',st',inds',vimap',vomap',pc',sols) =>
    if pc'.chk ∧ check_contradiction_fml_list F fml' n
    then SOME (ord_min mord sols)
    else NONE
End

Theorem fml_rel_check_mo_cstep_sol_list:
  list_conf_rel fml fmlls assg st inds vimap vomap pc ∧
  check_mo_cstep_sol_list objs w free fmlls assg st inds vimap vomap pc sols =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc',sols') ⇒
  ∃fml'.
    check_mo_cstep mord objs (Sol w free) fml pc sols =
      SOME (fml', pc', sols') ∧
    list_conf_rel fml' fmlls' assg' st' inds' vimap' vomap' pc' ∧
    pc.id ≤ pc'.id
Proof
  rw[list_conf_rel_def]>>
  gvs[check_mo_cstep_sol_list_def,mo_vars_covered_def,AllCaseEqs(),
    check_mo_cstep_def,check_obj_core_thm,check_obj_slots_thm]>>
  drule_all core_fmlls_mk_core_fml>>strip_tac>>
  drule check_obj_cong>>rw[]>>fs[]>>
  drule_all ind_rel_reindex>>strip_tac>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[enc_mv_enc,store_ind_enc,opt_update_SOME]>>
  drule_all store_rels>>
  simp[]
QED

Theorem fml_rel_check_mo_cstep_list:
  list_conf_rel fml fmlls assg st inds vimap vomap pc ∧
  check_mo_cstep_list mord objs cstep fmlls assg st inds vimap vomap pc sols =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc',sols') ⇒
  ∃fml'.
    check_mo_cstep mord objs cstep fml pc sols = SOME (fml', pc', sols') ∧
    list_conf_rel fml' fmlls' assg' st' inds' vimap' vomap' pc' ∧
    pc.id ≤ pc'.id
Proof
  (Cases_on`cstep`
  >~ [‘Sol’] >- (
    simp[check_mo_cstep_list_def,get_sol_def]>>
    metis_tac[fml_rel_check_mo_cstep_sol_list])
  >~ [‘LoadOrder nn xs’] >- (
    simp[check_mo_cstep_list_def,get_sol_def,check_mo_cstep_def,
      mo_cstep_ok_def]>>
    Cases_on`ALOOKUP pc.orders nn`>>gvs[]>>
    strip_tac>>
    gvs[AllCaseEqs()]>>
    drule_all fml_rel_check_cstep_list_conf_rel>>
    rw[]>>
    metis_tac[]))>>
  simp[check_mo_cstep_list_def,get_sol_def,check_mo_cstep_def,
    mo_cstep_ok_def]>>
  strip_tac>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_check_cstep_list_conf_rel>>
  rw[]>>
  metis_tac[]
QED

Theorem fml_bound_check_mo_cstep_list:
  fml_bound fmlls (LENGTH assg) ∧
  check_mo_cstep_list mord objs cstep fmlls assg st inds vimap vomap pc sols =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc',sols') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg'
Proof
  strip_tac>>
  gvs[check_mo_cstep_list_def,AllCaseEqs()]
  >~ [`check_cstep_list`] >- (
    drule_all fml_bound_check_cstep_list>>
    simp[])>>
  gvs[check_mo_cstep_sol_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[enc_mv_enc]>>
  drule_at (Pos last) fml_bound_store_ind>>
  simp[slot_bound_enc_max_var]
QED

Theorem fml_rel_check_mo_csteps_list:
  ∀csteps fml fmlls assg st inds vimap vomap pc sols
    fmlls' assg' st' inds' vimap' vomap' pc' sols'.
  list_conf_rel fml fmlls assg st inds vimap vomap pc ∧
  check_mo_csteps_list mord objs csteps fmlls assg st inds vimap vomap pc
    sols =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc',sols') ⇒
  ∃fml'.
    check_mo_csteps mord objs csteps fml pc sols = SOME (fml', pc', sols') ∧
    list_conf_rel fml' fmlls' assg' st' inds' vimap' vomap' pc' ∧
    pc.id ≤ pc'.id
Proof
  Induct>>
  rw[check_mo_csteps_list_def,check_mo_csteps_def]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_check_mo_cstep_list>>
  rw[]>>
  first_x_assum drule_all>>
  rw[]>>
  simp[]
QED

Theorem check_mo_csteps_list_concl:
  fmls = MAP (λc. enc c T) fml ∧
  EVERY (λs. slot_bound s (LENGTH assg)) fmls ∧
  (∃dm. dm_rel dm assg st) ∧
  check_mo_csteps_list mord objs csteps
    (FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE m Empty) (enumerate 1 fmls))
    assg st
    (REVERSE (MAP FST (enumerate 1 fmls)))
    (FST (mk_vimap (REPLICATE k Vnone) 0 (enumerate 1 fmls)))
    (mk_vomap_opt (NONE:((int # num) list # int) option))
    (init_conf (LENGTH fml + 1) T NONE NONE) [] =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc',sols) ∧
  pc'.chk ∧ check_contradiction_fml_list F fmlls' n ⇒
  is_front mord (ord_min mord sols) (nondom_set mord (set fml) objs)
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`check_mo_csteps_list mord objs csteps fmlls assg st
    inds vimap vomap pc [] = _`>>
  `fml_rel (build_fml T 1 fml) fmlls ∧ ind_rel fmlls inds ∧
   vimap_rel fmlls vimap ∧ vomap_rel pc.obj vomap ∧
   (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty) ∧
   rup_inv fmlls assg st ∧
   id_ok (build_fml T 1 fml) pc.id ∧ all_core (build_fml T 1 fml)` by (
    irule init_state_rels>>
    simp[Abbr`fmlls`,Abbr`inds`,Abbr`vimap`,Abbr`vomap`,Abbr`pc`]>>
    metis_tac[])>>
  `list_conf_rel (build_fml T 1 fml) fmlls assg st inds vimap vomap pc` by
    simp[list_conf_rel_def]>>
  drule_all fml_rel_check_mo_csteps_list>>
  strip_tac>>
  `check_contradiction_fml F fml' n` by (
    irule fml_rel_check_contradiction_fml>>
    fs[list_conf_rel_def]>>
    metis_tac[])>>
  `check_mo_top mord objs csteps (build_fml T 1 fml) (LENGTH fml + 1) n =
    SOME (ord_min mord sols)` by (
    simp[check_mo_top_def]>>
    qpat_x_assum`check_mo_csteps _ _ _ _ _ _ = _` mp_tac>>
    simp[Abbr`pc`]>>
    strip_tac>>
    simp[])>>
  `core_only_fml T (build_fml T 1 fml) = set fml` by
    simp[core_only_fml_build_fml]>>
  pop_assum (fn th => rewrite_tac[GSYM th])>>
  irule check_mo_top_sound>>
  qpat_x_assum`check_mo_top _ _ _ _ _ _ = _` (irule_at Any)>>
  simp[mo_ord_ok_thm,all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD,lookup_build_fml,
    id_ok_def,domain_build_fml]
QED

Theorem check_mo_top_list_concl:
  fmls = MAP (λc. enc c T) fml ∧
  EVERY (λs. slot_bound s (LENGTH assg)) fmls ∧
  (∃dm. dm_rel dm assg st) ∧
  check_mo_top_list mord objs csteps
    (FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE m Empty) (enumerate 1 fmls))
    assg st
    (REVERSE (MAP FST (enumerate 1 fmls)))
    (FST (mk_vimap (REPLICATE k Vnone) 0 (enumerate 1 fmls)))
    (mk_vomap_opt (NONE:((int # num) list # int) option))
    (LENGTH fml + 1) n = SOME vs ⇒
  is_front mord vs (nondom_set mord (set fml) objs)
Proof
  rw[check_mo_top_list_def,AllCaseEqs()]>>
  drule_at (Pos (el 4)) check_mo_csteps_list_concl>>
  simp[]>>
  metis_tac[]
QED
