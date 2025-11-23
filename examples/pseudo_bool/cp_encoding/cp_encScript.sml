(*
  The end-to-end encoder from CP to PB
*)
Theory cp_enc
Libs
  preamble
Ancestors
  pbc cp cp_to_ilpImpl ilp_to_pb mlstring
  (* mlmap *)

(* The encoder *)

(*
Definition mk_map_def:
  mk_map bnd =
    fromList mlstring$compare bnd
End

Definition lookup_map_def:
  lookup_map bnd x =
  case lookup bnd x of
    NONE => (0i,0i)
  | SOME v => v
End
*)

(* TODO: temporary *)
Definition cencode_bound_all_def:
  cencode_bound_all bnd Xs =
  MAP (λc. (NONE,c)) (encode_bound_all bnd Xs)
End

Definition encode_def:
  encode (inst:cp_inst) =
  case inst of (bnd,cs,_) =>
  let bndm = bnd_lookup bnd in
  let cs = append (FST (cencode_cp_all bndm cs 1 init_ec)) in
  let cs' = MAP (I ## encode_iconstraint_one bndm) cs in
  let bndcs = cencode_bound_all bndm (MAP FST bnd) in
  (bndcs ++ cs'):
    (mlstring option #
    (mlstring, mlstring reif + num) epb pbc) list
End

Definition encode_nivar_def:
  encode_nivar bnd V =
  mul_lin_term (-1) (encode_ivar bnd V)
End

Definition encode_obj_def:
  encode_obj inst =
  case inst of (bnd,cs,obj) =>
  case obj of
    NoObjective => NONE
  | Minimize v => SOME (encode_ivar (bnd_lookup bnd) v, 0i)
  | Maximize v => SOME (encode_nivar (bnd_lookup bnd) v, 0i)
End

Theorem MAP_SND_MAP_I_FST:
  MAP SND (MAP (I ## f) ls) =
  MAP f (MAP SND ls)
Proof
  rw[MAP_MAP_o]
QED

Theorem encode_sem_1:
  cp_sat (bnd_lookup bnd) (set cs) wi ⇒
  ∃wb.
  satisfies (reify_epb (wi,wb))
    (set (MAP SND (encode (bnd,cs,v))))
Proof
  `∃es ec'. cencode_cp_all (bnd_lookup bnd) cs 1 init_ec = (es,ec')` by metis_tac[PAIR]>>
  rw[encode_def,cp_sat_def,MAP_SND_MAP_I_FST]>>
  simp[GSYM encode_iconstraint_all_def,GSYM encode_iconstraint_all_sem_1]>>
  fs[GSYM EVERY_MEM]>>
  drule_all cencode_cp_all_thm_1>>
  rw[]>>
  fs[EVERY_MAP]>>
  first_x_assum (irule_at Any)>>
  simp[cencode_bound_all_def,MAP_MAP_o,o_DEF]>>
  metis_tac[encode_bound_all_sem_1]
QED

Theorem encode_sem_2:
  satisfies w (set (MAP SND (encode (bnd,cs,v)))) ⇒
  cp_sat (bnd_lookup bnd) (set cs) (unreify_epb (bnd_lookup bnd) w)
Proof
  `∃es ec'. cencode_cp_all (bnd_lookup bnd) cs 1 init_ec = (es,ec')` by metis_tac[PAIR]>>
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
  simp[cp_sat_def,GSYM EVERY_MEM]>>
  irule cencode_cp_all_thm_2>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  qexists_tac`λx. w (Var x)`>>
  simp[GSYM encode_iconstraint_all_sem_2]>>
  gvs[encode_iconstraint_all_def,MAP_MAP_o,o_DEF]
QED

(* Going into strings for the final encoder *)
Definition enc_fresh_def:
  enc_fresh n =
    strlit"f_" ^ toString (n:num)
End

Definition enc_reif_def:
  enc_reif reif =
  case reif of
    Ge X i => concat[strlit"ge_";X;toString i]
  | Eq X i => concat[strlit"eq_";X;toString i]
End

Definition enc_string_def:
  enc_string epb =
  case epb of
    Sign x => strlit"s_" ^ x
  | Bit x n => concat[strlit"b_";toString n;strlit"_";x]
  | Var x =>
    case x of
      INL y => enc_reif y
    | INR z => enc_fresh z
End

Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  cheat
QED

Definition full_encode_def:
  full_encode inst =
  (map_obj enc_string
    (encode_obj inst),
  MAP (I ## map_pbc enc_string) (encode inst))
End

Definition conv_concl_def:
  (conv_concl inst (OBounds lbi ubi) =
  case SND (SND inst) of
    Maximize v => OBounds (OPTION_MAP (λv. -v) ubi) (OPTION_MAP (λv. -v) lbi)
  | _ => (OBounds lbi ubi)) ∧
  (conv_concl inst concl = concl)
End

Theorem full_encode_sem_concl:
  full_encode inst = (obj,pbf) ∧
  sem_concl (set (MAP SND pbf)) obj concl ⇒
  cp_inst_sem_concl inst (conv_concl inst concl)
Proof
  `∃bnd cs v. inst = (bnd,cs,v)` by metis_tac[PAIR]>>
  strip_tac>>
  gvs[full_encode_def]>>
  qpat_x_assum`sem_concl _ _ _` mp_tac>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE]>>
  simp[GSYM IMAGE_IMAGE, GSYM (Once LIST_TO_SET_MAP)]>>
  DEP_REWRITE_TAC[GSYM concl_INJ_iff]>>
  CONJ_TAC >- (
    assume_tac enc_string_INJ>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  Cases_on`concl`>>fs[conv_concl_def]
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
    Cases_on`v`>>
    fs[cp_inst_sem_concl_def,cp_sem_concl_def,sem_concl_def]>>
    strip_tac
    >- (
      simp[cp_is_lb_def,cp_has_ub_def]>>
      CONJ_TAC >- (
        Cases_on`lbi`>>fs[]
        >- (
          fs[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
          metis_tac[encode_sem_1,encode_sem_2,PAIR])>>
        rw[]>>
        drule encode_sem_1>>
        disch_then (qspec_then`Minimize a` assume_tac)>>fs[]>>
        first_x_assum drule>>
        simp[encode_obj_def,eval_obj_def]>>
        DEP_REWRITE_TAC[encode_ivar_sem_1]>>
        fs[cp_sat_def])>>
      Cases_on`ubi`>>fs[]>>
      drule encode_sem_2>>
      disch_then (irule_at Any)>>
      fs[GSYM encode_ivar_sem_2,encode_obj_def,eval_obj_def])
    >- (
      simp[cp_is_ub_def,cp_has_lb_def]>>
      CONJ_TAC >- (
        Cases_on`ubi`>>fs[]>>
        drule encode_sem_2>>
        disch_then (irule_at Any)>>
        fs[GSYM encode_ivar_sem_2,encode_obj_def,eval_obj_def,encode_nivar_def]>>
        intLib.ARITH_TAC)>>
      Cases_on`lbi`>>fs[]
      >- (
        fs[cp_unsatisfiable_def,cp_satisfiable_def,unsatisfiable_def,satisfiable_def]>>
        metis_tac[encode_sem_1,encode_sem_2,PAIR])>>
      rw[]>>
      drule encode_sem_1>>
      disch_then (qspec_then`Maximize a` assume_tac)>>fs[]>>
      first_x_assum drule>>
      simp[encode_obj_def,eval_obj_def,encode_nivar_def]>>
      DEP_REWRITE_TAC[encode_ivar_sem_1]>>
      fs[cp_sat_def]>>
      intLib.ARITH_TAC))
QED

(*
EVAL ``full_encode
  ([strlit "X", (-5,10);
   strlit "Y", (-5,5);
   strlit "Z", (0,100)],
  [
    NotEquals (INL (strlit "X")) (INR 5)
  ],
  Maximize (strlit "Z"))``
*)
