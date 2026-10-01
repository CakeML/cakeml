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
Libs
  preamble mlstringSyntax[qualified]

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
   repl_initial_input_representations];
