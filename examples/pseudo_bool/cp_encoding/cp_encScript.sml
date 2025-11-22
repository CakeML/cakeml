(*
  The end-to-end encoder from CP to PB
*)
Theory cp_enc
Libs
  preamble
Ancestors
  pbc cp cp_to_ilpImpl ilp_to_pb mlstring
  (* mlmap *)

(* Our concrete CP instances will consist of:

- bnd : (mlstring, int # int) alist
- cs : mlstring constraint list
- obj : mlstring option (objective variable, if it exists)
*)

Type cp_inst = ``:(mlstring, int # int) alist # mlstring constraint list # mlstring option``;

(* For any unspecified variable, default to (0,0) *)
Definition bnd_lookup_def:
  bnd_lookup ls x =
    case ALOOKUP ls x of
      NONE => (0i,0i)
    | SOME v => v
End

Definition cp_inst_sat_def:
  cp_inst_sat (inst:cp_inst) w ⇔
  case inst of (bnd,cs,v) =>
    cp_sat (bnd_lookup bnd) (set cs) w
End

Definition cp_inst_satisfiable_def:
  cp_inst_satisfiable inst ⇔
  ∃w. cp_inst_sat inst w
End

Definition cp_inst_minimal_def:
  cp_inst_minimal (inst:cp_inst) w ⇔
  case inst of (bnd,cs,v) =>
    cp_minimal (bnd_lookup bnd) (set cs) (THE v) w
End

Definition cp_inst_maximal_def:
  cp_inst_maximal (inst:cp_inst) w ⇔
  case inst of (bnd,cs,v) =>
    cp_maximal (bnd_lookup bnd) (set cs) (THE v) w
End

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
  case inst of (bnd,cs,v) =>
  let bndm = bnd_lookup bnd in
  let cs = append (FST (cencode_cp_all bndm cs 1 init_ec)) in
  let cs' = MAP (I ## encode_iconstraint_one bndm) cs in
  let bndcs = cencode_bound_all bndm (MAP FST bnd) in
  (bndcs ++ cs'):
    (mlstring option #
    (mlstring, mlstring reif + num) epb pbc) list
End

Theorem MAP_SND_MAP_I_FST:
  MAP SND (MAP (I ## f) ls) =
  MAP f (MAP SND ls)
Proof
  rw[MAP_MAP_o]
QED

Theorem encode_sem_1:
  cp_inst_sat inst wi ⇒
  ∃wb.
  satisfies (reify_epb (wi,wb))
    (set (MAP SND (encode inst)))
Proof
  `∃bnd cs v. inst = (bnd,cs,v)` by metis_tac[PAIR]>>
  `∃es ec'. cencode_cp_all (bnd_lookup bnd) cs 1 init_ec = (es,ec')` by metis_tac[PAIR]>>
  rw[encode_def,cp_inst_sat_def,cp_sat_def,MAP_SND_MAP_I_FST]>>
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
  satisfies w (set (MAP SND (encode inst))) ⇒
  cp_inst_sat inst (unreify_epb (bnd_lookup (FST inst)) w)
Proof
  `∃bnd cs v. inst = (bnd,cs,v)` by metis_tac[PAIR]>>
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
  simp[cp_sat_def,GSYM EVERY_MEM,cp_inst_sat_def]>>
  irule cencode_cp_all_thm_2>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  qexists_tac`λx. w (Var x)`>>
  simp[GSYM encode_iconstraint_all_sem_2]>>
  gvs[encode_iconstraint_all_def,MAP_MAP_o,o_DEF]
QED

Theorem encode_equisatisfiable:
  (
    cp_inst_satisfiable inst ⇔
    satisfiable (set (MAP SND (encode inst)))
  )
Proof
  rw[cp_inst_satisfiable_def,satisfiable_def]>>
  metis_tac[encode_sem_1,encode_sem_2]
QED

(* Every solution to CP is also optimal for PB *)
Theorem encode_sem_minimal_1:
  cp_inst_minimal inst wi ⇒
  ∃wb.
  optimal (reify_epb (wi,wb))
    (set (MAP SND (encode inst)))
    (encode_ivar (bnd_lookup (FST inst))
      (THE (SND (SND inst))))
Proof
  `∃bnd cs v. inst = (bnd,cs,v)` by metis_tac[PAIR]>>
  rw[cp_inst_minimal_def,optimal_def,cp_minimal_def]>>
  `cp_inst_sat (bnd,cs,v) wi` by
    fs[cp_inst_sat_def]>>
  drule encode_sem_1>>rw[]>>
  first_x_assum $ irule_at Any>>
  rw[]>>
  drule_all encode_sem_2>>
  rw[cp_inst_sat_def]>>
  first_x_assum drule>>
  DEP_REWRITE_TAC[encode_ivar_sem_1]>>
  simp[encode_ivar_sem_2]>>
  gvs[cp_sat_def]
QED

(* Every solution to PB is also optimal for CP *)
Theorem encode_sem_minimal_2:
  optimal w
    (set (MAP SND (encode inst)))
    (encode_ivar (bnd_lookup (FST inst))
      (THE (SND (SND inst)))) ⇒
  cp_inst_minimal inst (unreify_epb (bnd_lookup (FST inst)) w)
Proof
  `∃bnd cs v. inst = (bnd,cs,v)` by metis_tac[PAIR]>>
  rw[cp_inst_minimal_def,optimal_def,cp_minimal_def]
  >- (
    drule encode_sem_2>>
    simp[cp_inst_sat_def])>>
  rename1`cp_sat _ _ w'`>>
  `cp_inst_sat (bnd,cs,v) w'` by
    fs[cp_inst_sat_def]>>
  drule_all encode_sem_1>>
  rw[]>>
  first_x_assum drule>>
  DEP_REWRITE_TAC[encode_ivar_sem_1]>>
  simp[encode_ivar_sem_2]>>
  gvs[cp_sat_def]
QED

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

Definition encode_obj_def:
  encode_obj inst =
  case inst of (bnd,cs,v) =>
  case v of NONE => NONE
  | SOME v => SOME (
    encode_ivar (bnd_lookup bnd) v, 0i)
End

Definition full_encode_def:
  full_encode inst =
  (map_obj enc_string
    (encode_obj inst),
  MAP (I ## map_pbc enc_string) (encode inst))
End

(* Interpreting a PB conclusion as CP instead. *)
Definition cp_sem_concl_def:
  (cp_sem_concl inst NoConcl ⇔ T) ∧
  (cp_sem_concl inst DSat ⇔ cp_inst_satisfiable inst) ∧
  (cp_sem_concl inst DUnsat ⇔ ¬cp_inst_satisfiable inst) ∧
  (cp_sem_concl inst (OBounds lbi ubi) ⇔
    ((case lbi of
      NONE => ¬cp_inst_satisfiable inst
    | SOME lb =>
      (∀w. cp_inst_sat inst w ⇒
        lb ≤ w (THE (SND (SND inst))))) ∧
    (case ubi of
      NONE => T
    | SOME ub =>
      (∃w. cp_inst_sat inst w ∧
        w (THE (SND (SND inst))) ≤ ub))))
End

Theorem full_encode_sem_concl:
  full_encode inst = (obj,pbf) ∧
  sem_concl (set (MAP SND pbf)) obj concl ⇒
  cp_sem_concl inst concl
Proof
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
  Cases_on`concl`>>fs[cp_sem_concl_def]>>
  simp[sem_concl_def,unsatisfiable_def]
  >- metis_tac[encode_equisatisfiable]
  >- metis_tac[encode_equisatisfiable]>>
  rw[]>>gvs[AllCasePreds()]
  >- metis_tac[encode_equisatisfiable]
  >- metis_tac[encode_equisatisfiable] >>
  cheat
QED

(*
EVAL ``full_encode
  ([strlit "X", (-5,10);
   strlit "Y", (-5,5);
   strlit "Z", (0,100)],
  [
    NotEquals (INL (strlit "X")) (INR 5)
  ],
  SOME (strlit "Z"))``
*)
