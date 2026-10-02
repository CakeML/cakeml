(*
  Immutable input metadata and the joint typing certificate used at the
  direct-AST REPL boundary. No AST-specific constructor map is assumed here.
*)
Theory repl_inputInvariant
Ancestors
  typeSound typeSoundInvariants typeSysProps namespaceProps primTypes typeSystem
  semanticPrimitives evaluate_skip
Libs
  preamble

Type datatype_catalogue =
  ``:(type_ident, (conN # num # tvarN list # t list) set) fmap``

Type input_slots = ``:(num, t) fmap``

Definition catalogue_matches_def:
  catalogue_matches (catalogue:datatype_catalogue) ctMap <=>
    !ti signature. FLOOKUP catalogue ti = SOME signature ==>
      datatype_signature ctMap ti = signature
End

Definition catalogue_stamps_def:
  catalogue_stamps (catalogue:datatype_catalogue) =
    {TypeStamp cn n | ?ti signature tvs ts.
      FLOOKUP catalogue ti = SOME signature /\
      (cn,n,tvs,ts) IN signature}
End

Definition input_slots_hold_def:
  input_slots_hold (slots:input_slots) tenvS <=>
    !loc ty. FLOOKUP slots loc = SOME ty ==>
      check_freevars 0 [] ty /\ FLOOKUP tenvS loc = SOME (Ref_t ty)
End

Definition input_metadata_bounds_def:
  input_metadata_bounds catalogue slots (st:'ffi semanticPrimitives$state) <=>
    (!cn n. TypeStamp cn n IN catalogue_stamps catalogue ==>
      n < st.next_type_stamp) /\
    (!loc. loc IN FDOM slots ==> loc < LENGTH st.refs)
End

Definition input_typing_witnesses_def:
  input_typing_witnesses catalogue slots tids tenv
      (st:'ffi semanticPrimitives$state) env ctMap tenvS <=>
    FDOM catalogue SUBSET tids UNION prim_type_ids /\
    type_sound_invariant st env ctMap tenvS {} tenv /\
    FRANGE ((SND o SND) o_f ctMap) SUBSET tids UNION prim_type_ids /\
    catalogue_matches catalogue ctMap /\ input_slots_hold slots tenvS
End

Definition initial_input_certificate_def:
  initial_input_certificate catalogue slots tids tenv
      (st:'ffi semanticPrimitives$state) env <=>
    ?ctMap tenvS.
      input_typing_witnesses catalogue slots tids tenv st env ctMap tenvS
End

(* Trusted writes must typecheck for every matching map/store pair and be
   unchanged by reference/exception renaming that fixes protected type stamps. *)
Definition input_stamp_fix_def:
  input_stamp_fix catalogue ft <=>
    !cn n. TypeStamp cn n IN catalogue_stamps catalogue ==>
      FLOOKUP ft n = SOME n
End

Definition trusted_input_value_def:
  trusted_input_value catalogue ty value <=>
    (!ctMap tenvS. good_ctMap ctMap /\ catalogue_matches catalogue ctMap ==>
      type_v 0 ctMap tenvS value ty) /\
    (!fr ft fe. input_stamp_fix catalogue ft ==>
      v_rel fr ft fe value value)
End

Theorem input_stamp_fix_extension:
  input_stamp_fix catalogue ft /\ ft SUBMAP next_ft ==>
  input_stamp_fix catalogue next_ft
Proof
  rw [input_stamp_fix_def] >> metis_tac [FLOOKUP_SUBMAP]
QED

Theorem input_stamp_fix_identity:
  input_metadata_bounds catalogue slots (st:'ffi semanticPrimitives$state) ==>
  input_stamp_fix catalogue (FUN_FMAP I (count st.next_type_stamp))
Proof
  rw [input_metadata_bounds_def,input_stamp_fix_def,FLOOKUP_FUN_FMAP]
QED

Theorem catalogue_stamps_member:
  TypeStamp cn n IN catalogue_stamps catalogue <=>
  ?ti signature tvs ts.
    FLOOKUP catalogue ti = SOME signature /\
    (cn,n,tvs,ts) IN signature
Proof
  simp [catalogue_stamps_def]
QED

Theorem catalogue_matches_lookup:
  catalogue_matches catalogue ctMap /\
  FLOOKUP catalogue ti = SOME signature ==>
  (FLOOKUP ctMap (TypeStamp cn n) = SOME (tvs,ts,ti) <=>
   (cn,n,tvs,ts) IN signature)
Proof
  rw [catalogue_matches_def, GSYM datatype_signature_member] >> metis_tac []
QED

Theorem catalogue_matches_preserved:
  catalogue_matches catalogue ctMap /\
  preserves_datatype_signatures tids ctMap ctMap' /\
  DISJOINT (FDOM catalogue) tids ==>
  catalogue_matches catalogue ctMap'
Proof
  rw [catalogue_matches_def, preserves_datatype_signatures_def, IN_DISJOINT] >>
  fs [flookup_thm] >> metis_tac []
QED

Theorem input_metadata_bounds_from_typing:
  type_sound_invariant (st:'ffi semanticPrimitives$state) env ctMap tenvS {} tenv /\
  catalogue_matches catalogue ctMap /\ input_slots_hold slots tenvS ==>
  input_metadata_bounds catalogue slots st
Proof
  rw [input_metadata_bounds_def]
  >- (
    fs [catalogue_stamps_member] >>
    drule_all catalogue_matches_lookup >> simp [] >> strip_tac >>
    fs [type_sound_invariant_def, consistent_ctMap_def, flookup_thm] >>
    metis_tac []) >>
  `FLOOKUP slots loc = SOME (slots ' loc)` by simp [FLOOKUP_DEF] >>
  fs [type_sound_invariant_def, input_slots_hold_def] >> res_tac >>
  drule_all type_s_reference >> rw [store_lookup_def]
QED

Theorem initial_input_certificate_intro:
  FDOM catalogue SUBSET tids UNION prim_type_ids /\
  type_sound_invariant (st:'ffi semanticPrimitives$state) env ctMap tenvS {} tenv /\
  FRANGE ((SND o SND) o_f ctMap) SUBSET tids UNION prim_type_ids /\
  catalogue_matches catalogue ctMap /\ input_slots_hold slots tenvS ==>
  initial_input_certificate catalogue slots tids tenv st env
Proof
  strip_tac >> simp [initial_input_certificate_def] >>
  qexistsl_tac [`ctMap`,`tenvS`] >> simp [input_typing_witnesses_def]
QED

Theorem input_typing_witnesses_bounds:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS ==>
  input_metadata_bounds catalogue slots st
Proof
  rw [input_typing_witnesses_def] >>
  drule_all input_metadata_bounds_from_typing >> simp []
QED

(* Equivalent to the expanded certificate, with bounds derived from typing. *)
Theorem initial_input_certificate_contract:
  initial_input_certificate catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env <=>
  FDOM catalogue SUBSET tids UNION prim_type_ids /\
  ?ctMap tenvS.
    type_sound_invariant st env ctMap tenvS {} tenv /\
    FRANGE ((SND o SND) o_f ctMap) SUBSET tids UNION prim_type_ids /\
    catalogue_matches catalogue ctMap /\ input_slots_hold slots tenvS /\
    input_metadata_bounds catalogue slots st
Proof
  rewrite_tac [initial_input_certificate_def] >>
  metis_tac [input_typing_witnesses_def, input_typing_witnesses_bounds]
QED

(* Declaration and reference preservation use the same joint witnesses. *)

Theorem input_slots_hold_extension:
  input_slots_hold slots tenvS /\ store_type_extension tenvS tenvS' ==>
  input_slots_hold slots tenvS'
Proof
  strip_tac >> drule store_type_extension_weakS >>
  fs [input_slots_hold_def] >>
  rw [weakeningTheory.weakS_def] >> res_tac >>
  metis_tac [FLOOKUP_SUBMAP]
QED

Theorem input_typing_witnesses_reserve:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  DISJOINT new_ids tids /\ DISJOINT new_ids prim_type_ids ==>
  type_sound_invariant st env ctMap tenvS new_ids tenv /\
  DISJOINT (FDOM catalogue) new_ids
Proof
  rw [input_typing_witnesses_def]
  >- (
    irule type_sound_invariant_reserve >> simp [] >> ASM_SET_TAC []) >>
  ASM_SET_TAC []
QED

Theorem input_typing_witnesses_advance:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  DISJOINT (FDOM catalogue) new_ids /\
  preserves_datatype_signatures new_ids ctMap ctMap' /\
  FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap)
    SUBSET new_ids /\
  store_type_extension tenvS tenvS' /\
  type_sound_invariant new_st new_env ctMap' tenvS' {} new_tenv ==>
  input_typing_witnesses catalogue slots (tids UNION new_ids) new_tenv
    new_st new_env ctMap' tenvS'
Proof
  strip_tac >> fs [input_typing_witnesses_def] >>
  drule_all catalogue_matches_preserved >> strip_tac >>
  drule_all input_slots_hold_extension >> strip_tac >>
  simp [input_typing_witnesses_def] >> ASM_SET_TAC []
QED

Theorem input_typing_declarations_success:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  DISJOINT new_ids tids /\ DISJOINT new_ids prim_type_ids /\
  type_ds T tenv ds new_ids new_tenv /\
  evaluate_decs st env ds = (new_st,Rval new_env) ==>
  ?new_map new_store.
    weakCT new_map ctMap /\ store_type_extension tenvS new_store /\
    input_typing_witnesses catalogue slots (tids UNION new_ids)
      (extend_dec_tenv new_tenv tenv) new_st (extend_dec_env new_env env)
      new_map new_store /\
    type_all_env new_map new_store new_env new_tenv
Proof
  strip_tac >>
  drule_all input_typing_witnesses_reserve >> strip_tac >>
  drule_all decs_type_sound >> simp [] >>
  disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
  drule_all input_typing_witnesses_advance >> strip_tac >>
  qexistsl_tac [`result_map`,`result_store`] >> simp []
QED

Theorem input_typing_declarations_raise:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  DISJOINT new_ids tids /\ DISJOINT new_ids prim_type_ids /\
  type_ds T tenv ds new_ids new_tenv /\
  evaluate_decs st env ds = (new_st,Rerr (Rraise raised_value)) ==>
  ?new_map new_store.
    weakCT new_map ctMap /\ store_type_extension tenvS new_store /\
    input_typing_witnesses catalogue slots (tids UNION new_ids) tenv
      new_st env new_map new_store /\
    type_v 0 new_map new_store raised_value Texn
Proof
  strip_tac >>
  drule_all input_typing_witnesses_reserve >> strip_tac >>
  drule_all decs_type_sound >> simp [] >>
  disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
  drule_all input_typing_witnesses_advance >> strip_tac >>
  qexistsl_tac [`result_map`,`result_store`] >> simp []
QED

(* Reference assignment is independent of whether the typed location belongs
   to the input-slot catalogue or to the primitive reference list. *)
Theorem input_typing_reference_assign:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  FLOOKUP tenvS loc = SOME (Ref_t ty) /\ type_v 0 ctMap tenvS value ty /\
  store_assign loc (Refv value) st.refs = SOME new_refs ==>
  input_typing_witnesses catalogue slots tids tenv
    (st with refs := new_refs) env ctMap tenvS
Proof
  strip_tac >>
  `type_s ctMap st.refs tenvS` by (
    fs [input_typing_witnesses_def, type_sound_invariant_def]) >>
  `type_sv ctMap tenvS (Refv value) (Ref_t ty)` by simp [type_sv_def] >>
  drule_all store_assign_type_sound >> strip_tac >>
  gvs [input_typing_witnesses_def, type_sound_invariant_def,
    consistent_ctMap_def] >> rpt strip_tac >> res_tac
QED

Theorem input_typing_slot_assign:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  FLOOKUP slots loc = SOME ty /\ type_v 0 ctMap tenvS value ty /\
  store_assign loc (Refv value) st.refs = SOME new_refs ==>
  input_typing_witnesses catalogue slots tids tenv
    (st with refs := new_refs) env ctMap tenvS
Proof
  strip_tac >>
  `input_slots_hold slots tenvS` by fs [input_typing_witnesses_def] >>
  `FLOOKUP tenvS loc = SOME (Ref_t ty)` by (
    fs [input_slots_hold_def] >> res_tac) >>
  drule_all input_typing_reference_assign >> simp []
QED

Theorem input_typing_trusted_assign:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  FLOOKUP slots loc = SOME ty /\ trusted_input_value catalogue ty value /\
  store_assign loc (Refv value) st.refs = SOME new_refs ==>
  input_typing_witnesses catalogue slots tids tenv
    (st with refs := new_refs) env ctMap tenvS
Proof
  strip_tac >>
  `type_v 0 ctMap tenvS value ty` by (
    fs [trusted_input_value_def, input_typing_witnesses_def,
      type_sound_invariant_def] >> res_tac) >>
  drule_all input_typing_slot_assign >> simp []
QED

Theorem input_typing_declarations_no_type_error:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  DISJOINT new_ids tids /\ DISJOINT new_ids prim_type_ids /\
  type_ds T tenv ds new_ids new_tenv /\
  evaluate_decs st env ds = (new_st,result) ==>
  result <> Rerr (Rabort Rtype_error)
Proof
  strip_tac >> drule_all input_typing_witnesses_reserve >> strip_tac >>
  CCONTR_TAC >> gvs [] >> drule_all decs_type_sound >> simp []
QED

(* Finite-map interfaces shared by initialization's catalogue partitions. *)

Theorem input_slots_hold_entries:
  EVERY (\(loc,ty). check_freevars 0 [] ty /\
    FLOOKUP tenvS loc = SOME (Ref_t ty)) entries ==>
  input_slots_hold (FEMPTY |++ entries) tenvS
Proof
  rw [input_slots_hold_def, flookup_fupdate_list] >>
  fs [CaseEq "option"] >>
  drule ALOOKUP_MEM >> simp [MEM_REVERSE] >> strip_tac >>
  fs [EVERY_MEM, FORALL_PROD] >> res_tac
QED

Theorem input_catalogue_entries_match:
  EVERY (\(ti,signature). datatype_signature ctMap ti = signature) entries ==>
  catalogue_matches (FEMPTY |++ entries) ctMap
Proof
  rw [catalogue_matches_def, flookup_fupdate_list] >>
  fs [CaseEq "option"] >>
  drule ALOOKUP_MEM >> simp [MEM_REVERSE] >> strip_tac >>
  fs [EVERY_MEM, FORALL_PROD]
QED

Theorem input_catalogue_restrict_entries:
  !entries initial.
    DRESTRICT (initial |++ entries) keys =
    DRESTRICT initial keys |++ FILTER (\(key,value). key IN keys) entries
Proof
  Induct >> simp [FUPDATE_LIST_THM] >>
  qx_genl_tac [`entry`,`initial`] >>
  namedCases_on `entry` ["entry_key entry_value"] >>
  Cases_on `entry_key IN keys` >> simp [FUPDATE_LIST_THM]
QED

Theorem input_catalogue_new_signatures:
  catalogue_matches catalogue allocated /\
  FDOM catalogue SUBSET set identities /\
  (!ti. MEM ti identities ==>
    datatype_signature result_map ti = datatype_signature allocated ti) ==>
  catalogue_matches catalogue result_map
Proof
  rw [catalogue_matches_def, SUBSET_DEF] >>
  fs [flookup_thm]
QED

Theorem input_catalogues_union:
  catalogue_matches first_catalogue ctMap /\
  catalogue_matches second_catalogue ctMap ==>
  catalogue_matches (FUNION first_catalogue second_catalogue) ctMap
Proof
  rw [catalogue_matches_def, FLOOKUP_FUNION] >>
  fs [CaseEq "option"]
QED

Theorem input_typing_witnesses_clock:
  input_typing_witnesses catalogue slots tids tenv
    (st with clock := ck) env ctMap tenvS <=>
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS
Proof
  simp [input_typing_witnesses_def, type_sound_invariant_clock]
QED

Theorem initial_input_certificate_clock:
  initial_input_certificate catalogue slots tids tenv
    (st with clock := ck) env <=>
  initial_input_certificate catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env
Proof
  simp [initial_input_certificate_def, input_typing_witnesses_clock]
QED

(* Exported interfaces must not rest on assumptions or admissions. *)
val _ = List.app (fn theorem => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  in
    if null (hyp theorem) andalso null axioms andalso
      List.all (fn name => name = "DISK_THM") oracles then ()
    else failwith "Input typing invariants have assumptions or admissions"
  end)
  [input_stamp_fix_extension,
   input_stamp_fix_identity,
   catalogue_stamps_member,
   catalogue_matches_lookup,
   catalogue_matches_preserved,
   input_metadata_bounds_from_typing,
   initial_input_certificate_intro,
   input_typing_witnesses_bounds,
   initial_input_certificate_contract,
   input_slots_hold_extension,
   input_typing_witnesses_reserve,
   input_typing_witnesses_advance,
   input_typing_declarations_success,
   input_typing_declarations_raise,
   input_typing_reference_assign,
   input_typing_slot_assign,
   input_typing_trusted_assign,
   input_typing_declarations_no_type_error,
   input_slots_hold_entries,
   input_catalogue_entries_match,
   input_catalogue_restrict_entries,
   input_catalogue_new_signatures,
   input_catalogues_union,
   input_typing_witnesses_clock,
   initial_input_certificate_clock];
