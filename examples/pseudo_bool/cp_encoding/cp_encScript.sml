(*
  The end-to-end encoder from CP to PB
*)
Theory cp_enc
Libs
  preamble
Ancestors
  cp pbc cp_to_ilp cp_to_ilp_all ilp_to_pb

Definition cencode_bound_var_def:
  cencode_bound_var bnd X =
  let (lb,ub) = bnd X in
  let bX = encode_ivar bnd (X:mlstring) in
  [
    (SOME(concat[strlit"i[";X;strlit"][lb]"])
      ,(pbc$GreaterEqual,bX,lb));
    (SOME(concat[strlit"i[";X;strlit"][ub]"])
      ,(pbc$LessEqual,bX,ub));
  ]
End

Definition cencode_bound_all_def:
  (cencode_bound_all bnd [] = Nil) ∧
  (cencode_bound_all bnd (x::xs) =
    Append (List (cencode_bound_var bnd x))
      (cencode_bound_all bnd xs))
End

Definition encode_def:
  encode bnd cs =
  let bndm = bnd_lookup bnd in
  let cs = append (FST (cencode_constraints bndm cs init_ec)) in
  let cs' = MAP (I ## encode_iconstraint_one bndm) cs in
  let bndcs = cencode_bound_all bndm (MAP FST bnd) in
  append (Append bndcs (List cs'))
End

Definition encode_nivar_def:
  encode_nivar bnd V =
  mul_lin_term (-1) (encode_ivar bnd V)
End

(* The projection variables for X *)
Definition proj_ivar_def:
  proj_ivar bnd (X:'a) =
  let (comp,h) = bit_width bnd X in
  let bits = GENLIST (λi. (Bit X i)) h in
  if comp then
      (Sign X :: bits)
  else bits
End

(* Returns the optional preserved set and the objective *)
Definition encode_prob_type_def:
  encode_prob_type bnd pty =
  case pty of
    Decision => (NONE, NONE)
  | Minimize v => (NONE, SOME (encode_ivar (bnd_lookup bnd) v, 0i))
  | Maximize v => (NONE, SOME (encode_nivar (bnd_lookup bnd) v, 0i))
  | Enumerate vs =>
    (SOME
      (FLAT (MAP (proj_ivar (bnd_lookup bnd)) vs)),
    NONE)
End

Theorem MAP_SND_MAP_I_FST:
  MAP SND (MAP (I ## f) ls) =
  MAP f (MAP SND ls)
Proof
  rw[MAP_MAP_o]
QED

Theorem MAP_SND_cencode_bound_all[simp]:
  ∀ls.
  MAP SND (append (cencode_bound_all bnd ls)) =
  encode_bound_all bnd ls
Proof
  Induct>>
  rw[cencode_bound_all_def,encode_bound_all_def,
    cencode_bound_var_def,encode_bound_var_def]>>
  pairarg_tac>>simp[]
QED

Theorem encode_sem_1:
  ALL_DISTINCT (MAP FST cs) ∧
  cp_sat (bnd_lookup bnd) (set (MAP SND cs)) wi ⇒
  ∃wb.
  satisfies (reify_epb (wi,wb))
    (set (MAP SND (encode bnd cs)))
Proof
  `∃es ec'. cencode_constraints (bnd_lookup bnd) cs init_ec = (es,ec')` by metis_tac[PAIR]>>
  rw[encode_def,cp_sat_def,MAP_SND_MAP_I_FST]>>
  simp[GSYM encode_iconstraint_all_def,GSYM encode_iconstraint_all_sem_1]>>
  fs[GSYM EVERY_MEM,EVERY_MAP]>>
  drule_all cencode_constraints_thm_1>>
  rw[]>>
  fs[EVERY_MAP]>>
  metis_tac[encode_bound_all_sem_1]
QED

Theorem encode_sem_2:
  satisfies w (set (MAP SND (encode bnd cs))) ⇒
  cp_sat (bnd_lookup bnd) (set (MAP SND cs))
    (unreify_epb (bnd_lookup bnd) w)
Proof
  `∃es ec'. cencode_constraints (bnd_lookup bnd) cs init_ec = (es,ec')` by metis_tac[PAIR]>>
  rw[encode_def]>>
  fs[MAP_SND_MAP_I_FST,cencode_bound_all_def,MAP_MAP_o,o_DEF]>>
  drule_at Any encode_bound_all_sem_2>>
  impl_tac >- (
    simp[bnd_lookup_def]>>
    strip_tac>>TOP_CASE_TAC>>
    drule ALOOKUP_MEM>>
    simp[MEM_MAP]>>
    metis_tac[FST])>>
  rw[]>>
  simp[cp_sat_def,GSYM EVERY_MEM,EVERY_MAP]>>
  irule cencode_constraints_thm_2>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  qexists_tac`λx. w (Var x)`>>
  simp[GSYM encode_iconstraint_all_sem_2]>>
  gvs[encode_iconstraint_all_def,MAP_MAP_o,o_DEF]
QED

(* Going into strings for the final encoder *)
Definition format_string_def:
  format_string epb =
  case epb of
    Sign x =>
      concat [strlit"i[";x;strlit"][sign]"]
  | Bit x n =>
      concat [strlit"i[";x;strlit"][b";toString n;strlit"]"]
  | Var v => format_var v
End

Theorem format_string_INJ:
  INJ format_string UNIV UNIV
Proof
  cheat
QED

Definition full_encode_def:
  full_encode (bnd,cs,pty) =
  let (pres,obj) = encode_prob_type bnd pty in
  (OPTION_MAP (MAP format_string) pres,
    map_obj format_string obj,
    MAP (I ## map_pbc format_string) (encode bnd cs))
End

(* Check validity and convert a PB conclusion into a CP one *)
Definition conv_concl_def:
  (conv_concl pty (OBounds lbi ubi) =
    case pty of
      Maximize v =>
        SOME (OBounds (OPTION_MAP (λv. -v) ubi) (OPTION_MAP (λv. -v) lbi))
    | Minimize v => SOME (OBounds lbi ubi)
    | _ => NONE) ∧
  (conv_concl pty (EEnum n complete) =
    case pty of
      Enumerate vs => SOME (EEnum n complete)
    | _ => NONE) ∧
  (conv_concl pty concl = SOME concl)
End

Theorem full_encode_sem_concl:
  ALL_DISTINCT (MAP FST cs) ∧
  full_encode (bnd,cs,pty) = (pres,obj,pbf) ∧
  sem_concl (set (MAP SND pbf)) obj (pres_set_list pres) concl ∧
  conv_concl pty concl = SOME concl' ⇒
  cp_inst_sem_concl (bnd,cs,pty) concl'
Proof
  strip_tac>>
  gvs[full_encode_def]>>
  qpat_x_assum`sem_concl _ _ _ _` mp_tac>>
  gvs[UNCURRY_EQ]>>
  rename1`_ = (pres,obj)`>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE]>>
  simp[GSYM IMAGE_IMAGE, GSYM (Once LIST_TO_SET_MAP)]>>
  `pres_set_list (OPTION_MAP (MAP format_string) pres) =
    IMAGE format_string(pres_set_list pres)` by
      (simp[pres_set_list_def]>>
      every_case_tac>>fs[LIST_TO_SET_MAP])>>
  pop_assum SUBST1_TAC>>
  DEP_REWRITE_TAC[GSYM concl_INJ_iff]>>
  CONJ_TAC >- (
    simp[FINITE_pres_set_list]>>
    assume_tac format_string_INJ>>
    CONJ_TAC>- (
      drule INJ_SUBSET>>
      disch_then match_mp_tac>>
      simp[])>>
    gvs[INJ_DEF])>>
  Cases_on`concl`>>gvs[conv_concl_def]
  >~[`NoConcl`]
  >- fs[cp_inst_sem_concl_def,cp_sem_concl_def]
  >~[`DSat`]
  >- (
    fs[cp_inst_sem_concl_def,cp_sem_concl_def,sem_concl_def]>>
    simp[cp_satisfiable_def,satisfiable_def]>>
    metis_tac[encode_sem_1,encode_sem_2,PAIR])
  >~[`DUnsat`]
  >- (
    fs[cp_inst_sem_concl_def,cp_sem_concl_def,sem_concl_def]>>
    simp[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
    metis_tac[encode_sem_1,encode_sem_2,PAIR])
  >~[`OBounds lbi ubi`]
  >- (
    gvs[AllCaseEqs(),cp_inst_sem_concl_def,cp_sem_concl_def,
      sem_concl_def,encode_prob_type_def]>>
    strip_tac
    >- (
      simp[cp_is_lb_def,cp_has_ub_def]>>
      CONJ_TAC >- (
        Cases_on`lbi`>>fs[]
        >- (
          fs[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
          metis_tac[encode_sem_1,encode_sem_2,PAIR])>>
        rw[]>>
        drule_all encode_sem_1>>
        strip_tac>>fs[]>>
        first_x_assum drule>>
        simp[eval_obj_def]>>
        DEP_REWRITE_TAC[encode_ivar_sem_1]>>
        fs[cp_sat_def])>>
      Cases_on`ubi`>>fs[]>>
      drule encode_sem_2>>
      disch_then (irule_at Any)>>
      fs[GSYM encode_ivar_sem_2,eval_obj_def])
    >- (
      simp[cp_is_ub_def,cp_has_lb_def]>>
      CONJ_TAC >- (
        Cases_on`ubi`>>fs[]>>
        drule encode_sem_2>>
        disch_then (irule_at Any)>>
        fs[GSYM encode_ivar_sem_2,eval_obj_def,encode_nivar_def]>>
        intLib.ARITH_TAC)>>
      Cases_on`lbi`>>fs[]
      >- (
        fs[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
        metis_tac[encode_sem_1,encode_sem_2,PAIR])>>
      rw[]>>
      drule_all encode_sem_1>>
      rw[]>>fs[]>>
      first_x_assum drule>>
      simp[eval_obj_def,encode_nivar_def]>>
      DEP_REWRITE_TAC[encode_ivar_sem_1]>>
      fs[cp_sat_def]>>
      intLib.ARITH_TAC))
  >~[`EEnum n b`]
  >- (
    gvs[AllCaseEqs(),cp_inst_sem_concl_def,cp_sem_concl_def,
      sem_concl_def,encode_prob_type_def]>>
    qmatch_goalsub_abbrev_tac`CARD proj_pb_sols`>>
    qmatch_goalsub_abbrev_tac`_ ⇒ n ≤ CARD proj_cp_sols ∧ _`>>
    `?f. BIJ f proj_pb_sols proj_cp_sols` by cheat>>
    drule_at Any FINITE_BIJ_CARD>>
    impl_tac >- (
      fs[Abbr`proj_pb_sols`]>>
      irule FINITE_proj_pres>>
      irule FINITE_pres_set_list)>>
    rw[])
QED
