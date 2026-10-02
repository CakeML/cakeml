(*
  Instantiate the registered AST family at the actual inferred REPL
  identities, then strengthen the same initial witnesses with representations.
  These facts establish representation, not Candle declaration allowedness.
*)
Theory repl_inputRepresentation
Ancestors
  astCanonical typeRepCanonical typeRepPreludeCanonical repl_inputInit
  repl_inputInvariant repl_inputMetadata repl_init_types inferSound
  typeSoundInvariants typeSystem semanticPrimitives ml_translator std_prelude
  repl_types evaluate_skip ml_prog envRel
Libs
  preamble mlstringSyntax[qualified] semanticPrimitivesSyntax[qualified]

(* Actual inferred identities, namespace and closed catalogue. *)
Definition repl_ast_canonical_id_def:
  repl_ast_canonical_id registered_name =
    THE (ALOOKUP repl_ast_type_ids registered_name)
End

Definition repl_ast_canonical_base_def:
  repl_ast_canonical_base = (ienv_to_tenv (FST repl_prog_types)).t
End

val canonical_names = ast_canonical_type_groups_def |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> map (fn group => group |> pairSyntax.strip_pair |> el 2);

val concrete_entries = map (fn registered_name => EVAL
  ``~MEM (repl_ast_canonical_id ^registered_name) prim_type_nums /\
    FLOOKUP repl_input_catalogue (repl_ast_canonical_id ^registered_name) =
      SOME (ast_canonical_signature
        (ast_canonical_tenvT repl_ast_canonical_base repl_ast_canonical_id)
        ^registered_name)``
  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [LIST_TO_SET]))
  |> EQT_ELIM) canonical_names;

Theorem repl_ast_canonical_catalogue_entries = LIST_CONJ concrete_entries;

val concrete_namespace =
  ``ast_canonical_tenvT repl_ast_canonical_base repl_ast_canonical_id``;
val list_lookup = EVAL ``nsLookup ^concrete_namespace (Short «list»)``;
val option_lookup = EVAL ``nsLookup ^concrete_namespace (Short «option»)``;
val list_params = list_lookup |> concl |> rand |> optionSyntax.dest_some
  |> pairSyntax.dest_pair |> fst;
val option_params = option_lookup |> concl |> rand |> optionSyntax.dest_some
  |> pairSyntax.dest_pair |> fst;

Theorem repl_ast_canonical_namespace =
  ``ast_canonical_primitive_types ^concrete_namespace /\
    nsLookup ^concrete_namespace (Short «list») =
      SOME (^list_params,Tlist (Tvar ^(hd (fst (listSyntax.dest_list list_params))))) /\
    nsLookup ^concrete_namespace (Short «option») =
      SOME (^option_params,Tapp
        [Tvar ^(hd (fst (listSyntax.dest_list option_params)))] repl_option_type_id) /\
    ~MEM repl_option_type_id prim_type_nums /\
    ~MEM repl_sum_type_id prim_type_nums`` |> EVAL |> EQT_ELIM;

val option_catalogue_lookup = EVAL
  ``FLOOKUP repl_input_catalogue repl_option_type_id``;
val sum_catalogue_lookup = EVAL
  ``FLOOKUP repl_input_catalogue repl_sum_type_id``;
val option_catalogue_signature = option_catalogue_lookup |> concl |> rand
  |> optionSyntax.dest_some;
val sum_catalogue_signature = sum_catalogue_lookup |> concl |> rand
  |> optionSyntax.dest_some;

Theorem repl_input_container_catalogue_lookups =
  CONJ option_catalogue_lookup sum_catalogue_lookup;

Theorem repl_ast_canonical_catalogue_entry:
  MEM registered_name ast_canonical_type_names ==>
  ~MEM (repl_ast_canonical_id registered_name) prim_type_nums /\
  FLOOKUP repl_input_catalogue (repl_ast_canonical_id registered_name) =
    SOME (ast_canonical_signature
      (ast_canonical_tenvT repl_ast_canonical_base repl_ast_canonical_id)
      registered_name)
Proof
  rw [ast_canonical_type_names_def, ast_canonical_stamped_declarations_def] >>
  simp [repl_ast_canonical_catalogue_entries]
QED

Theorem repl_input_option_signature:
  datatype_signature ctMap repl_option_type_id = ^option_catalogue_signature ==>
  instantiated_datatype_signature [element_ty] ctMap repl_option_type_id =
    option_rep_signature element_ty
Proof
  strip_tac >>
  simp [instantiated_datatype_signature_def, option_rep_signature_def,
    EXTENSION, pairTheory.FORALL_PROD, type_subst_def, FUPDATE_LIST,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp [LEFT_AND_OVER_OR, EXISTS_OR_THM, type_subst_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem repl_input_sum_signature:
  datatype_signature ctMap repl_sum_type_id = ^sum_catalogue_signature ==>
  instantiated_datatype_signature [left_ty;right_ty] ctMap repl_sum_type_id =
    sum_rep_signature left_ty right_ty
Proof
  strip_tac >>
  simp [instantiated_datatype_signature_def, sum_rep_signature_def,
    EXTENSION, pairTheory.FORALL_PROD, type_subst_def, FUPDATE_LIST,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp [LEFT_AND_OVER_OR, EXISTS_OR_THM, type_subst_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac [DISJ_COMM]
QED

Theorem repl_ast_canonical_context:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  catalogue_matches repl_input_catalogue ctMap ==>
  ast_canonical_family_context repl_ast_canonical_base repl_ast_canonical_id
    repl_option_type_id ctMap
Proof
  strip_tac >>
  simp [ast_canonical_family_context_def, repl_ast_canonical_namespace] >>
  conj_tac
  >- (
    qx_gen_tac `registered_name` >> strip_tac >>
    drule repl_ast_canonical_catalogue_entry >> strip_tac >>
    fs [catalogue_matches_def] >> res_tac) >>
  qx_gen_tac `element_ty` >> irule repl_input_option_signature >>
  fs [catalogue_matches_def] >>
  metis_tac [repl_input_container_catalogue_lookups]
QED

Theorem repl_ast_canonical_family_complete =
  IMP_TRANS repl_ast_canonical_context
    (Q.INST [`base` |-> `repl_ast_canonical_base`,
      `identities` |-> `repl_ast_canonical_id`,
      `option_id` |-> `repl_option_type_id`] ast_canonical_family_complete);

Theorem repl_ast_canonical_dec_complete =
  CONJUNCTS (UNDISCH repl_ast_canonical_family_complete)
  |> List.find (fn theorem => let
       val (_,args) = theorem |> concl |> strip_comb
       in length args = 5 andalso same_const (last args) ``DEC_TYPE`` end)
  |> valOf
  |> DISCH (repl_ast_canonical_family_complete |> concl |> dest_imp |> fst)
  |> REWRITE_RULE [repl_ast_canonical_id_def, repl_ast_root_type_ids];

(* Input sum and declaration encoder representation. *)
Theorem repl_input_dec_list_complete:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  catalogue_matches repl_input_catalogue ctMap ==>
  type_rep_complete tvs ctMap tenvS (Tlist (Tapp [] repl_dec_type_id))
    (LIST_TYPE DEC_TYPE)
Proof
  strip_tac >> irule type_rep_complete_list >> simp [] >>
  mp_tac (SPEC_ALL repl_ast_canonical_dec_complete) >> simp []
QED

Theorem repl_input_sum_complete:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  catalogue_matches repl_input_catalogue ctMap ==>
  type_rep_complete tvs ctMap tenvS repl_input_type
    (SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE))
Proof
  strip_tac >>
  `type_rep_complete tvs ctMap tenvS Tstring STRING_TYPE` by (
    mp_tac (SPEC_ALL type_rep_complete_primitives) >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tlist (Tapp [] repl_dec_type_id))
    (LIST_TYPE DEC_TYPE)` by (
      irule repl_input_dec_list_complete >> simp []) >>
  rewrite_tac [repl_input_type_def] >> irule type_rep_complete_sum >>
  simp [repl_ast_canonical_namespace] >>
  irule repl_input_sum_signature >> fs [catalogue_matches_def] >>
  metis_tac [repl_input_container_catalogue_lookups]
QED

Theorem repl_input_value_canonical:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  catalogue_matches repl_input_catalogue ctMap /\
  type_v tvs ctMap tenvS value repl_input_type ==>
  ?result. SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) result value
Proof
  strip_tac >>
  `type_rep_complete tvs ctMap tenvS repl_input_type
    (SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE))` by (
      irule repl_input_sum_complete >> simp []) >>
  drule_all type_rep_complete_elim >> simp []
QED

Theorem repl_input_decs_encoded:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  catalogue_matches repl_input_catalogue ctMap /\
  type_v tvs ctMap tenvS value (Tlist (Tapp [] repl_dec_type_id)) ==>
  ?decs. LIST_v DEC_v decs = value
Proof
  strip_tac >>
  `type_rep_complete tvs ctMap tenvS (Tlist (Tapp [] repl_dec_type_id))
    (LIST_TYPE DEC_TYPE)` by (
      irule repl_input_dec_list_complete >> simp []) >>
  drule_all type_rep_complete_elim >> simp [ast_dec_list_representation]
QED

(* Catalogue, slot and representation facts share one constructor-map/store-typing pair. *)
Theorem repl_initial_input_representations:
  ?ctMap tenvS.
    input_typing_witnesses repl_input_catalogue repl_input_slots
      (set_ids start_type_id (SND repl_prog_types))
      (ienv_to_tenv (FST repl_prog_types))
      (input_repl_state (ffi:'ffi ffi_state)) repl_prog_env ctMap tenvS /\
    input_metadata_bounds repl_input_catalogue repl_input_slots
      (input_repl_state ffi) /\
    type_rep_complete 0 ctMap tenvS repl_input_type
      (SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE)) /\
    type_rep_complete 0 ctMap tenvS (Tlist (Tapp [] repl_dec_type_id))
      (LIST_TYPE DEC_TYPE) /\
    (!value. type_v 0 ctMap tenvS value (Tlist (Tapp [] repl_dec_type_id)) ==>
      ?decs. LIST_v DEC_v decs = value)
Proof
  mp_tac (repl_initial_input_certificate |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`
    |> REWRITE_RULE [initial_input_certificate_def]) >>
  disch_then (qx_choosel_then [`canonical_map`,`canonical_store`]
    strip_assume_tac) >>
  `ctMap_ok canonical_map /\ ctMap_has_lists canonical_map` by (
    fs [input_typing_witnesses_def, type_sound_invariant_def, good_ctMap_def]) >>
  `catalogue_matches repl_input_catalogue canonical_map` by
    fs [input_typing_witnesses_def] >>
  `input_metadata_bounds repl_input_catalogue repl_input_slots
    (input_repl_state ffi)` by (
      drule input_typing_witnesses_bounds >> simp []) >>
  `type_rep_complete 0 canonical_map canonical_store repl_input_type
    (SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE))` by (
      irule repl_input_sum_complete >> simp []) >>
  `type_rep_complete 0 canonical_map canonical_store
    (Tlist (Tapp [] repl_dec_type_id)) (LIST_TYPE DEC_TYPE)` by (
      irule repl_input_dec_list_complete >> simp []) >>
  qexistsl_tac [`canonical_map`,`canonical_store`] >> simp [] >>
  qx_gen_tac `value` >> strip_tac >>
  mp_tac (Q.INST [`ctMap` |-> `canonical_map`,
    `tenvS` |-> `canonical_store`, `tvs` |-> `0`, `value` |-> `value`]
    repl_input_decs_encoded) >> simp []
QED

(* Concrete source injection and original initialization locations. *)
val input_source_stamp = find_term semanticPrimitivesSyntax.is_TypeStamp
  (concl (CONJUNCT2 SUM_TYPE_def));
val (input_source_name,input_source_number) =
  semanticPrimitivesSyntax.dest_TypeStamp input_source_stamp;
val input_source_ctor_lookup = EVAL
  ``nsLookup (ienv_to_tenv (FST repl_prog_types)).c
      (Short ^input_source_name)``;
val [input_source_params,input_source_fields,input_source_type] =
  input_source_ctor_lookup |> concl |> rand |> optionSyntax.dest_some
    |> pairSyntax.strip_pair;
val _ = if aconv input_source_type (rhs (concl repl_sum_type_id_def)) then ()
  else failwith "Source constructor does not have the inferred sum identity";
val input_source_signature = EVAL
  ``FLOOKUP repl_input_catalogue repl_sum_type_id``
  |> concl |> rand |> optionSyntax.dest_some;

Definition repl_source_value_def:
  repl_source_value text = Conv (SOME ^input_source_stamp) [Litv (StrLit text)]
End

fun input_origin_value name =
  BODY_CONJUNCTS repl_input_slot_values
  |> List.find (fn th => aconv (lhs (concl th))
       ``nsLookup repl_prog_env.v ^name``)
  |> valOf |> concl |> rand |> optionSyntax.dest_some;

val input_primitive_origins =
  [(``Long «Repl» (Short «isEOF»)`` , ``repl_types$Bool``),
   (``Long «Repl» (Short «errorMessage»)`` , ``repl_types$Str``),
   (``Long «Repl» (Short «exn»)`` , ``repl_types$Exn``)]
  |> map (fn (name,ty) => let
       val (is_ref,loc) = semanticPrimitivesSyntax.dest_Loc (input_origin_value name)
       val _ = if aconv is_ref T then () else failwith "Expected an original reference"
       in pairSyntax.list_mk_pair [name,ty,loc] end);
val (_,input_source_location) = semanticPrimitivesSyntax.dest_Loc
  (input_origin_value ``Long «Repl» (Short «nextInput»)``);

Definition repl_input_primitive_refs_def:
  repl_input_primitive_refs =
    ^(listSyntax.mk_list (input_primitive_origins,
      ``:(mlstring,mlstring) id # simple_type # num``))
End

Definition repl_input_location_def:
  repl_input_location = ^input_source_location
End


Theorem repl_source_representation:
  SUM_TYPE STRING_TYPE right_rep (INL text) (repl_source_value text)
Proof
  simp [SUM_TYPE_def, STRING_TYPE_def, repl_source_value_def]
QED

Theorem repl_source_signature_member:
  ?signature.
      FLOOKUP repl_input_catalogue repl_sum_type_id = SOME signature /\
      (^input_source_name,^input_source_number,
       ^input_source_params,^input_source_fields) IN signature
Proof
  qexists_tac `^input_source_signature` >> EVAL_TAC
QED

Theorem repl_source_constructor_typing:
  catalogue_matches repl_input_catalogue ctMap ==>
  FLOOKUP ctMap ^input_source_stamp =
    SOME (^input_source_params,^input_source_fields,repl_sum_type_id)
Proof
  metis_tac [catalogue_matches_lookup, repl_source_signature_member]
QED

Theorem repl_source_stamp_protected:
  ^input_source_stamp IN catalogue_stamps repl_input_catalogue
Proof
  metis_tac [catalogue_stamps_member, repl_source_signature_member]
QED

Theorem repl_source_value_type:
  catalogue_matches repl_input_catalogue ctMap ==>
  type_v 0 ctMap tenvS (repl_source_value text) repl_input_type
Proof
  strip_tac >> drule repl_source_constructor_typing >> strip_tac >>
  simp [repl_source_value_def, repl_input_type_def, Once type_v_cases] >>
  simp [Once check_freevars_def, Once type_subst_def] >>
  simp [Once check_freevars_def, Once type_v_cases] >> EVAL_TAC
QED

Theorem repl_source_value_self:
  input_stamp_fix repl_input_catalogue ft ==>
  v_rel fr ft fe (repl_source_value text) (repl_source_value text)
Proof
  strip_tac >>
  `FLOOKUP ft ^input_source_number = SOME ^input_source_number` by (
    metis_tac [input_stamp_fix_def, repl_source_stamp_protected]) >>
  simp [repl_source_value_def, Once v_rel_def, stamp_rel_cases] >>
  simp [Once v_rel_def]
QED

Theorem repl_source_value_trusted:
  trusted_input_value repl_input_catalogue repl_input_type (repl_source_value text)
Proof
  simp [trusted_input_value_def, repl_source_value_type, repl_source_value_self]
QED

Theorem repl_input_primitive_refs_types:
  EVERY (check_ref_types (FST repl_prog_types) repl_prog_env)
    repl_input_primitive_refs
Proof
  simp [repl_input_primitive_refs_def, check_ref_types_def,
    repl_input_slot_values] >> EVAL_TAC
QED

Theorem repl_input_location_type:
  FLOOKUP repl_input_slots repl_input_location = SOME repl_input_type
Proof
  EVAL_TAC
QED

Theorem repl_input_initial_environment:
  extend_dec_env input_repl_decl_env init_env = repl_prog_env
Proof
  simp [repl_prog_env_def, GSYM input_repl_decl_env_def,
    merge_env_def, extend_dec_env_def]
QED

Theorem repl_input_initial_reachable:
  !b (ffi:'ffi ffi_state).
    repl_types_input repl_input_catalogue repl_input_slots b
      (ffi,repl_input_primitive_refs)
      (repl_prog_types,input_repl_state ffi,repl_prog_env)
Proof
  qx_genl_tac [`b`,`ffi`] >>
  mp_tac (input_repl_Prog |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  rewrite_tac [Prog_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`initial_clock`,`final_clock`] assume_tac)) >>
  mp_tac (repl_initial_input_certificate |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`) >> strip_tac >>
  mp_tac (Q.ISPECL
    [`repl_input_catalogue`,`repl_input_slots`,`ffi:'ffi ffi_state`,
     `repl_input_primitive_refs`,`repl_prog`,`repl_prog_types`,
     `input_repl_state (ffi:'ffi ffi_state) with clock := final_clock`,
     `input_repl_decl_env`,`initial_clock:num`,`b:bool`] repl_types_input_init) >>
  simp [repl_prog_types_thm, repl_input_initial_environment,
    repl_input_primitive_refs_types, input_init_ok_def,
    initial_input_certificate_clock] >> strip_tac >>
  drule repl_types_input_set_clock >>
  disch_then (qspec_then `(input_repl_state ffi).clock` mp_tac) >>
  simp []
QED

Theorem repl_input_source_assign:
  repl_types_input repl_input_catalogue repl_input_slots b (ffi,rs)
    (input_types,st,env) /\
  store_assign repl_input_location (Refv (repl_source_value text)) st.refs =
    SOME new_store ==>
  repl_types_input repl_input_catalogue repl_input_slots b (ffi,rs)
    (input_types,st with refs := new_store,env)
Proof
  strip_tac >> irule repl_types_input_trusted_assign >> simp [] >>
  qexistsl_tac [`repl_input_location`,`repl_input_type`,`repl_source_value text`] >>
  simp [repl_input_location_type, repl_source_value_trusted]
QED

(* Exact runtime transport through the protected constructor catalogue. *)
Theorem repl_input_representation_stamps_protected:
  set ast_canonical_representation_stamps SUBSET
    catalogue_stamps repl_input_catalogue
Proof
  irule SUBSET_TRANS >>
  qexists_tac `BIGUNION (set (MAP
    (\(ti,signature). IMAGE (\(cn,n,tvs,ts). TypeStamp cn n) signature)
    repl_input_catalogue_entries))` >> conj_tac
  >- (
    EVAL_TAC >> simp [LIST_TO_SET,BIGUNION_INSERT] >> simp [SUBSET_DEF]) >>
  rw [SUBSET_DEF,IN_BIGUNION,MEM_MAP,EXISTS_PROD,IN_IMAGE] >>
  qmatch_asmsub_rename_tac `MEM (type_id,signature) repl_input_catalogue_entries` >>
  fs [IN_IMAGE,EXISTS_PROD] >>
  qmatch_goalsub_rename_tac `TypeStamp ctor_name stamp_num IN catalogue_stamps _` >>
  qmatch_asmsub_rename_tac `(ctor_name,stamp_num,params,field_types) IN signature` >>
  `ALOOKUP (REVERSE repl_input_catalogue_entries) type_id = SOME signature` by (
    irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
    simp [MAP_REVERSE,repl_input_catalogue_keys_distinct]) >>
  simp [catalogue_stamps_member] >>
  qexistsl_tac [`type_id`,`signature`,`params`,`field_types`] >>
  simp [repl_input_catalogue_def,alistTheory.FLOOKUP_FUPDATE_LIST]
QED

Theorem repl_input_representation_stamp_self:
  input_stamp_fix repl_input_catalogue ft ==>
  !stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp
Proof
  rw [] >>
  `stamp IN catalogue_stamps repl_input_catalogue` by (
    metis_tac [repl_input_representation_stamps_protected,SUBSET_DEF,MEM]) >>
  Cases_on `stamp` >> fs [catalogue_stamps_def] >>
  fs [input_stamp_fix_def,catalogue_stamps_def,stamp_rel_cases] >> metis_tac []
QED

Theorem repl_input_dec_list_self:
  input_stamp_fix repl_input_catalogue ft /\ LIST_TYPE DEC_TYPE decs value ==>
  v_rel fr ft fe value value
Proof
  rw [ast_dec_list_representation] >> irule ast_dec_list_encoder_self >>
  match_mp_tac repl_input_representation_stamp_self >> simp []
QED

Theorem repl_input_value_self:
  input_stamp_fix repl_input_catalogue ft /\
  SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) input value ==>
  v_rel fr ft fe value value
Proof
  strip_tac >>
  `!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp` by (
      match_mp_tac repl_input_representation_stamp_self >> simp []) >>
  Cases_on `input` >> fs [SUM_TYPE_def,STRING_TYPE_def]
  >~ [`Litv (StrLit _)`] >- (
    fs [v_rel_def,OPTREL_def,ast_canonical_representation_stamps_def]) >>
  drule_all repl_input_dec_list_self >> strip_tac >>
  fs [v_rel_def,OPTREL_def,ast_canonical_representation_stamps_def]
QED

Theorem repl_input_value_transport:
  input_stamp_fix repl_input_catalogue ft /\
  SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) input value /\
  v_rel fr ft fe value physical_value ==>
  physical_value = value /\
  SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) input physical_value
Proof
  strip_tac >>
  `no_closures value` by (
    Cases_on `input` >> fs [SUM_TYPE_def,STRING_TYPE_def,Once no_closures_def] >>
    fs [Once no_closures_def] >>
    metis_tac [ast_dec_list_equality |> REWRITE_RULE [EqualityType_def]
      |> CONJUNCT1]) >>
  `v_rel fr ft fe value value` by (
    drule_all repl_input_value_self >> simp []) >>
  `physical_value = value` by (
    metis_tac [v_rel_no_closures_functional]) >> simp []
QED

Theorem repl_input_read:
  repl_types_input repl_input_catalogue repl_input_slots T (ffi,rs)
    (input_types,physical,physical_env) ==>
  ?input value.
    store_lookup repl_input_location physical.refs = SOME (Refv value) /\
    SUM_TYPE STRING_TYPE (LIST_TYPE DEC_TYPE) input value
Proof
  strip_tac >> drule repl_types_input_T_F >>
  disch_then (qx_choosel_then
    [`clean`,`clean_env`,`ref_map`,`type_map`,`exn_map`,`prefix_len`]
    strip_assume_tac) >>
  drule repl_types_input_F_thm >> strip_tac >>
  qpat_x_assum `initial_input_certificate _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [initial_input_certificate_def]) >>
  disch_then (qx_choosel_then [`ctor_map`,`store_types`] strip_assume_tac) >>
  fs [input_typing_witnesses_def,type_sound_invariant_def,good_ctMap_def,
    input_slots_hold_def] >>
  `FLOOKUP store_types repl_input_location = SOME (Ref_t repl_input_type)` by (
    metis_tac [repl_input_location_type]) >>
  drule_all type_s_reference >>
  disch_then (qx_choose_then `clean_value` strip_assume_tac) >>
  drule_all repl_input_value_canonical >>
  disch_then (qx_choose_then `input` assume_tac) >>
  `repl_input_location < prefix_len` by (
    fs [SUBSET_DEF,IN_COUNT] >>
    metis_tac [repl_input_location_type,flookup_thm]) >>
  `FLOOKUP ref_map repl_input_location = SOME repl_input_location` by (
    fs [state_rel_def]) >>
  drule_all state_rel_store_lookup >> simp [OPTREL_def] >>
  disch_then (qx_choose_then `physical_ref` strip_assume_tac) >>
  Cases_on `physical_ref` >> fs [ref_rel_def] >>
  qmatch_asmsub_rename_tac
    `store_lookup repl_input_location physical.refs = SOME (Refv physical_value)` >>
  drule_all repl_input_value_transport >> strip_tac >>
  qexists_tac `input` >> simp []
QED

(* Exported interfaces must not rest on assumptions or admissions. *)
val _ = List.app (fn theorem => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  in
    if null (hyp theorem) andalso null axioms andalso
      List.all (fn name => name = "DISK_THM") oracles then ()
    else failwith "Direct-AST input representations have assumptions or admissions"
  end)
  [repl_ast_canonical_catalogue_entries, repl_ast_canonical_namespace,
   repl_input_container_catalogue_lookups, repl_ast_canonical_catalogue_entry,
   repl_input_option_signature, repl_input_sum_signature,
   repl_ast_canonical_context, repl_ast_canonical_family_complete,
   repl_ast_canonical_dec_complete, repl_input_dec_list_complete,
   repl_input_sum_complete, repl_input_value_canonical, repl_input_decs_encoded,
   repl_initial_input_representations, repl_source_representation,
   repl_source_signature_member, repl_source_constructor_typing,
   repl_source_stamp_protected, repl_source_value_type, repl_source_value_self,
   repl_source_value_trusted, repl_input_primitive_refs_types,
   repl_input_location_type, repl_input_initial_environment,
   repl_input_initial_reachable, repl_input_source_assign,
   repl_input_representation_stamps_protected, repl_input_representation_stamp_self,
   repl_input_dec_list_self, repl_input_value_self, repl_input_value_transport,
   repl_input_read];
