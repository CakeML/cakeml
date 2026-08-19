(*
  Refine the multi-objective PB proof checker to use arrays
*)
Theory npbc_mo_list
Ancestors
  npbc_check npbc_mo_check npbc_list
Libs
  preamble

(* Every objective variable must be assigned by a logged solution.
  The assignment's domain is the num_set that model_banning bans over *)
Definition mo_vars_covered_def:
  mo_vars_covered objs (ws:num_set) ⇔
  EVERY (λv. sptree$lookup v ws ≠ NONE) (mo_obj_vars objs)
End

(* The multi-objective solution-logging step bans the logged assignment
  over its own domain, so it cannot share check_cstep_sol_list *)
Definition check_mo_cstep_sol_list_def:
  check_mo_cstep_sol_list objs w
    (fml: (npbc # bool) option list) (zeros:word8 list) (inds:num list)
    (vimap:vimap_ty) (vomap:mlstring) (pc:proof_conf) sols =
  (let ws = list_to_num_set (MAP FST w) in
  if pc.chk ∧ mo_vars_covered objs ws then
    let corels = core_fmlls fml inds in
    case check_obj NONE w (MAP SND corels) NONE of
      NONE => NONE
    | SOME (new,wsol) =>
      let c = model_banning (SOME ws) wsol in
      SOME (
        update_resize fml NONE (SOME (c,T)) pc.id,
        zeros,
        sorted_insert pc.id inds,
        update_vimap T vimap pc.id (FST c),
        vomap,
        pc with <| id := pc.id+1; enum := pc.enum+1 |>,
        obj_vecs objs wsol :: sols)
  else NONE)
End

(* Solution logging is the one step that is not delegated *)
Definition get_sol_def:
  (get_sol (Sol w) = SOME w) ∧
  (get_sol _ = NONE)
End

(* The multi-objective side conditions on the delegated steps *)
Definition mo_cstep_ok_def:
  mo_cstep_ok objs cstep (pc:proof_conf) ⇔
  case cstep of
    Sstep _ => pc.ord ≠ NONE
  | CheckedDelete _ _ _ _ => pc.ord ≠ NONE
  | LoadOrder name xs =>
    (case ALOOKUP pc.orders name of
      NONE => F
    | SOME aord => pareto_ord_ok objs aord xs)
  | _ => T
End

Definition check_mo_cstep_list_def:
  check_mo_cstep_list objs cstep fml zeros inds vimap vomap pc sols =
  case get_sol cstep of
    SOME w =>
      check_mo_cstep_sol_list objs w fml zeros inds vimap vomap pc sols
  | NONE =>
    if mo_cstep_ok objs cstep pc then
      (case check_cstep_list cstep fml zeros inds vimap vomap pc of
        NONE => NONE
      | SOME (fml',zeros',inds',vimap',vomap',pc') =>
        SOME (fml',zeros',inds',vimap',vomap',pc',sols))
    else NONE
End

Definition check_mo_csteps_list_def:
  (check_mo_csteps_list objs [] fml zeros inds vimap vomap pc sols =
    SOME (fml, zeros, inds, vimap, vomap, pc, sols)) ∧
  (check_mo_csteps_list objs (c::cs) fml zeros inds vimap vomap pc sols =
    case check_mo_cstep_list objs c fml zeros inds vimap vomap pc sols of
      NONE => NONE
    | SOME(fml', zeros', inds', vimap', vomap', pc', sols') =>
      check_mo_csteps_list objs cs fml' zeros' inds' vimap' vomap' pc' sols')
End

Definition check_mo_top_list_def:
  check_mo_top_list objs csteps fml zeros inds vimap vomap id n =
  case check_mo_csteps_list objs csteps fml zeros inds vimap vomap
    (init_conf id T NONE NONE) [] of
    NONE => NONE
  | SOME (fml',zeros',inds',vimap',vomap',pc',sols) =>
    if pc'.chk ∧ check_contradiction_fml_list F fml' n
    then SOME (pareto_min sols)
    else NONE
End

Theorem fml_rel_check_mo_cstep_sol_list:
  list_conf_rel fml fmlls zeros inds vimap vomap pc ∧
  check_mo_cstep_sol_list objs w fmlls zeros inds vimap vomap pc sols =
    SOME (fmlls',zeros',inds',vimap',vomap',pc',sols') ⇒
  ∃fml'.
    check_mo_cstep objs (Sol w) fml pc sols = SOME (fml', pc', sols') ∧
    list_conf_rel fml' fmlls' zeros' inds' vimap' vomap' pc' ∧
    pc.id ≤ pc'.id
Proof
  rw[list_conf_rel_def]>>
  gvs[check_mo_cstep_sol_list_def,mo_vars_covered_def,AllCaseEqs(),
    check_mo_cstep_def]>>
  `set (MAP SND (core_fmlls fmlls inds)) =
    set (MAP SND (toAList (mk_core_fml T fml)))` by (
    rw[EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,MEM_core_fmlls]>>
    simp[lookup_mk_core_fml]>>
    metis_tac[ind_rel_lookup_core_only_list,fml_rel_lookup_core_only])>>
  drule check_obj_cong>>rw[]>>fs[]>>
  rw[]
  >- metis_tac[fml_rel_update_resize]
  >- metis_tac[ind_rel_update_resize_sorted_insert]
  >- metis_tac[vimap_rel_update_resize_update_vimap]>>
  simp[any_el_update_resize]
QED

Theorem fml_rel_check_mo_cstep_list:
  list_conf_rel fml fmlls zeros inds vimap vomap pc ∧
  check_mo_cstep_list objs cstep fmlls zeros inds vimap vomap pc sols =
    SOME (fmlls',zeros',inds',vimap',vomap',pc',sols') ⇒
  ∃fml'.
    check_mo_cstep objs cstep fml pc sols = SOME (fml', pc', sols') ∧
    list_conf_rel fml' fmlls' zeros' inds' vimap' vomap' pc' ∧
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

Theorem fml_rel_check_mo_csteps_list:
  ∀csteps fml fmlls zeros inds vimap vomap pc sols
    fmlls' zeros' inds' vimap' vomap' pc' sols'.
  list_conf_rel fml fmlls zeros inds vimap vomap pc ∧
  check_mo_csteps_list objs csteps fmlls zeros inds vimap vomap pc sols =
    SOME (fmlls',zeros',inds',vimap',vomap',pc',sols') ⇒
  ∃fml'.
    check_mo_csteps objs csteps fml pc sols = SOME (fml', pc', sols') ∧
    list_conf_rel fml' fmlls' zeros' inds' vimap' vomap' pc' ∧
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
  check_mo_csteps_list objs csteps
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE m NONE) (enumerate 1 fml))
    (REPLICATE z 0w)
    (REVERSE (MAP FST (enumerate 1 fml)))
    (mk_vimap (REPLICATE k NONE) (enumerate 1 fml))
    «»
    (init_conf (LENGTH fml + 1) T NONE NONE) [] =
    SOME (fmlls',zeros',inds',vimap',vomap',pc',sols) ∧
  pc'.chk ∧ check_contradiction_fml_list F fmlls' n ⇒
  set (pareto_min sols) = nondom_set (set fml) objs
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`check_mo_csteps_list objs csteps fmlls zeros
    inds vimap vomap pc [] = _`>>
  `list_conf_rel (build_fml T 1 fml) fmlls zeros inds vimap vomap pc` by (
    simp[list_conf_rel_def]>>
    rpt CONJ_TAC
    >- simp[Abbr`fmlls`,fml_rel_FOLDL_update_resize]
    >- (
      unabbrev_all_tac>>
      simp[ind_rel_FOLDL_update_resize])
    >- (
      unabbrev_all_tac>>
      rw[mk_vimap_def]>>
      irule vimap_rel_FOLDL_update_resize>>
      rw[vimap_rel_def]>>
      gvs[EL_REPLICATE,any_el_ALT])
    >- simp[Abbr`pc`,init_conf_def,vomap_rel_def]
    >- (
      rw[Abbr`pc`,Abbr`fmlls`,any_el_ALT,init_conf_def]>>
      DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
      simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])>>
    simp[Abbr`zeros`])>>
  drule_all fml_rel_check_mo_csteps_list>>
  strip_tac>>
  `check_contradiction_fml F fml' n` by (
    irule fml_rel_check_contradiction_fml>>
    fs[list_conf_rel_def]>>
    metis_tac[])>>
  `check_mo_top objs csteps (build_fml T 1 fml) (LENGTH fml + 1) n =
    SOME (pareto_min sols)` by (
    simp[check_mo_top_def]>>
    qpat_x_assum`check_mo_csteps _ _ _ _ _ = _` mp_tac>>
    simp[Abbr`pc`]>>
    strip_tac>>
    simp[])>>
  `core_only_fml T (build_fml T 1 fml) = set fml` by
    simp[core_only_fml_build_fml]>>
  pop_assum (fn th => rewrite_tac[GSYM th])>>
  irule check_mo_top_sound>>
  qpat_x_assum`check_mo_top _ _ _ _ _ = _` (irule_at Any)>>
  simp[all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD,lookup_build_fml,
    id_ok_def,domain_build_fml]
QED

Theorem check_mo_top_list_concl:
  check_mo_top_list objs csteps
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE m NONE) (enumerate 1 fml))
    (REPLICATE z 0w)
    (REVERSE (MAP FST (enumerate 1 fml)))
    (mk_vimap (REPLICATE k NONE) (enumerate 1 fml))
    «»
    (LENGTH fml + 1) n = SOME vs ⇒
  set vs = nondom_set (set fml) objs
Proof
  rw[check_mo_top_list_def,AllCaseEqs()]>>
  drule_all check_mo_csteps_list_concl>>
  simp[]
QED
