(*
  Compose the generated initialization execution with joint input witnesses.
  Concrete allocation establishes closed signatures; the common declaration
  preservation interface carries them through the remaining initialization.
*)
Theory repl_inputInit
Ancestors
  repl_inputMetadata repl_inputInvariant repl_init_types astProg
  typeSound inferSound inferProps envRel primSemEnv ml_prog ml_progProps
Libs
  preamble finite_mapSyntax[qualified] semanticPrimitivesSyntax[qualified]

(* Validate the generated execution interface before extracting its results. *)
fun input_decls_result program theorem = let
  val (_,fact) = strip_forall (concl theorem)
  val (relation,args) = strip_comb fact
  val _ = if same_const relation ``Decls`` andalso length args = 5 andalso
    aconv (el 1 args) ``init_env`` andalso aconv (el 3 args) program then ()
    else failwith "Expected a generated Decls execution from init_env"
  val (initial,state_args) = strip_comb (el 2 args)
  val _ = if same_const initial ``init_state`` andalso length state_args = 1 then ()
    else failwith "Expected a generated Decls execution from init_state"
  val ffi = hd state_args
  val _ = if is_var ffi andalso List.exists (aconv ffi) (free_vars fact) then ()
    else failwith "Expected a free initial FFI parameter"
  in (el 4 args,el 5 args,ffi) end;

Theorem input_Prog_declarations_preserve:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  DISJOINT new_ids tids /\ DISJOINT new_ids prim_type_ids /\
  type_ds T tenv ds new_ids new_tenv /\
  Prog env st ds new_env new_st ==>
  ?new_map new_store.
    weakCT new_map ctMap /\ store_type_extension tenvS new_store /\
    input_typing_witnesses catalogue slots (tids UNION new_ids)
      (extend_dec_tenv new_tenv tenv) new_st (extend_dec_env new_env env)
      new_map new_store /\
    type_all_env new_map new_store new_env new_tenv
Proof
  rw [Prog_def] >>
  qmatch_asmsub_rename_tac
    `evaluate_decs (st with clock := initial_clock) env ds =
      (new_st with clock := final_clock,Rval new_env)` >>
  `input_typing_witnesses catalogue slots tids tenv
    (st with clock := initial_clock) env ctMap tenvS` by
    simp [input_typing_witnesses_clock] >>
  drule_all input_typing_declarations_success >>
  simp [input_typing_witnesses_clock]
QED

(* Closed signatures can be computed a constructor at a time, without
   treating positive constructor lookups as a closure argument. *)
Theorem input_signature_fresh_constructor:
  FLOOKUP ctMap (TypeStamp cn n) = NONE ==>
  datatype_signature (ctMap |+ (TypeStamp cn n,(ctor_params,ctor_fields,ti))) other =
  datatype_signature ctMap other UNION
    (if ti = other then {(cn,n,ctor_params,ctor_fields)} else {})
Proof
  rw [EXTENSION, FORALL_PROD,
    typeSoundInvariantsTheory.datatype_signature_member, FLOOKUP_UPDATE] >>
  qmatch_goalsub_rename_tac `TypeStamp inspected_name inspected_index` >>
  Cases_on `cn = inspected_name` >> Cases_on `n = inspected_index` >>
  gvs [] >> metis_tac [EQ_SYM_EQ]
QED

Theorem input_signature_empty =
  typeSoundInvariantsTheory.datatype_signature_empty |> Q.INST
    [`ctMap` |-> `FEMPTY : typeSoundInvariants$ctMap`]
  |> SIMP_RULE std_ss [FLOOKUP_EMPTY];

(* Cache ground constructor-freshness checks. *)
fun input_allocation_signature_rules map_tm =
  if finite_mapSyntax.is_fempty map_tm then [] else let
    val (previous,entry) = finite_mapSyntax.dest_fupdate map_tm
    val (stamp,value) = pairSyntax.dest_pair entry
    val (name,index) = semanticPrimitivesSyntax.dest_TypeStamp stamp
    val [params,field_types,identity] = pairSyntax.strip_pair value
    val fresh = EVAL ``FLOOKUP ^previous ^stamp = NONE`` |> EQT_ELIM
    val rule = input_signature_fresh_constructor |> Q.INST
      [`ctMap` |-> `^previous`, `cn` |-> `^name`, `n` |-> `^index`,
       `ctor_params` |-> `^params`, `ctor_fields` |-> `^field_types`,
       `ti` |-> `^identity`]
      |> (fn th => MATCH_MP th fresh)
    in rule :: input_allocation_signature_rules previous end;

Theorem input_primitive_signatures:
  good_ctMap ctMap ==>
  datatype_signature ctMap Tbool_num =
    {(«True»,bool_type_num,[],[]); («False»,bool_type_num,[],[])} /\
  datatype_signature ctMap Tlist_num =
    {(«[]»,list_type_num,[«'a»],[]);
     («::»,list_type_num,[«'a»],[Tvar «'a»; Tlist (Tvar «'a»)])}
Proof
  rw [typeSoundInvariantsTheory.good_ctMap_def, EXTENSION, FORALL_PROD,
    typeSoundInvariantsTheory.datatype_signature_member]
  >~ [`FLOOKUP _ (TypeStamp _ _) = SOME (_,_,Tbool_num)`] >- (
    qmatch_goalsub_rename_tac
      `FLOOKUP ctMap (TypeStamp cn n) = SOME (ctor_params,ctor_fields,Tbool_num)` >>
    fs [typeSoundInvariantsTheory.ctMap_has_bools_def] >>
    eq_tac >> rw [] >> fs [] >>
    `n = bool_type_num` by metis_tac [typeSoundInvariantsTheory.constructor_type_stamp_index] >>
    gvs [] >> Cases_on `cn = «True»` >> Cases_on `cn = «False»` >> gvs []) >>
  qmatch_goalsub_rename_tac
    `FLOOKUP ctMap (TypeStamp cn n) = SOME (ctor_params,ctor_fields,Tlist_num)` >>
  fs [typeSoundInvariantsTheory.ctMap_has_lists_def] >>
  eq_tac >> rw [] >> fs [] >>
  `n = list_type_num` by metis_tac [typeSoundInvariantsTheory.constructor_type_stamp_index] >>
  gvs [] >> Cases_on `cn = «[]»` >> Cases_on `cn = «::»` >> gvs []
QED

Definition input_primitive_catalogue_def:
  input_primitive_catalogue = FEMPTY |++
    FILTER (\(ti,signature). MEM ti [Tbool_num; Tlist_num])
      repl_input_catalogue_entries
End

Theorem input_primitive_catalogue_matches:
  good_ctMap ctMap ==> catalogue_matches input_primitive_catalogue ctMap
Proof
  strip_tac >> drule input_primitive_signatures >> strip_tac >>
  rewrite_tac [input_primitive_catalogue_def] >>
  irule input_catalogue_entries_match >> CONV_TAC (RAND_CONV EVAL) >>
  fs [typeSystemTheory.Tbool_num_def, typeSystemTheory.Tlist_num_def,
    typeSystemTheory.Tlist_def, semanticPrimitivesTheory.bool_type_num_def,
    semanticPrimitivesTheory.list_type_num_def] >> SET_TAC []
QED

Theorem input_primitive_catalogue_domain:
  FDOM input_primitive_catalogue = {Tbool_num; Tlist_num}
Proof
  simp [input_primitive_catalogue_def, FDOM_FUPDATE_LIST] >>
  CONV_TAC (LAND_CONV (RAND_CONV EVAL)) >>
  simp [typeSystemTheory.Tbool_num_def, typeSystemTheory.Tlist_num_def, LIST_TO_SET]
QED

Theorem input_primitive_initialization:
  ?ctMap.
    input_typing_witnesses input_primitive_catalogue FEMPTY {} prim_tenv
      (init_state (ffi:'ffi ffi_state)) init_env ctMap FEMPTY
Proof
  qspecl_then [`{}`,`init_state ffi`,`init_env`] mp_tac prim_type_sound_invariants >>
  simp [init_state_env_thm] >>
  disch_then (qx_choose_then `seed_map` strip_assume_tac) >>
  `good_ctMap seed_map` by
    fs [typeSoundInvariantsTheory.type_sound_invariant_def] >>
  drule input_primitive_catalogue_matches >> strip_tac >>
  qexists_tac `seed_map` >>
  fs [input_typing_witnesses_def, input_slots_hold_def,
    input_primitive_catalogue_domain, primTypesTheory.prim_type_ids_def]
QED

Theorem input_initial_type_environment:
  ienv_ok {} infer$init_config /\
  ienv_to_tenv infer$init_config = prim_tenv
Proof
  strip_assume_tac input_primitive_initialization >>
  fs [input_typing_witnesses_def, typeSoundInvariantsTheory.type_sound_invariant_def,
    typeSoundInvariantsTheory.tenv_ok_def] >>
  simp [inferTheory.init_config_def, inferPropsTheory.ienv_ok_def,
    inferTheory.ienv_val_ok_def, envRelTheory.ienv_to_tenv_def] >>
  EVAL_TAC
QED

(* Apply the proved inference bridge to each checked transition. All these
   facts are kernel theorem compositions; no stage invariant is assumed. *)
fun input_declarative_stage name (env_ok_th,start_bound_th) = let
  val inference_th = DB.fetch "repl_inputMetadata" (name ^ "_thm")
  val (initial_tm,program_tm) = inference_th |> concl |> lhs |> dest_comb
    |> (fn (application,program) => (rand application,program))
  val output_tm = inference_th |> concl |> rhs |> rand
  val stage_rule = infertype_prog_inc_sound |> SPEC_ALL |> Q.INST
    [`initial_types` |-> `^initial_tm`, `output_types` |-> `^output_tm`,
     `ds` |-> `^program_tm`]
    |> PURE_REWRITE_RULE [FST,SND]
  val sound_th = MATCH_MP stage_rule
    (LIST_CONJ [env_ok_th,start_bound_th,inference_th])
  val _ = save_thm (name ^ "_sound",sound_th)
  val next_ok = CONJUNCT1 sound_th
  val next_mono = sound_th |> CONJUNCT2 |> CONJUNCT1
  val next_bound = MATCH_MP LESS_EQ_TRANS (CONJ start_bound_th next_mono)
  in (sound_th,(next_ok,next_bound)) end;

val initial_input_types =
  (CONJUNCT1 input_initial_type_environment,
   ``start_type_id <= start_type_id`` |> EVAL |> EQT_ELIM);
val (repl_input_prelude_types_sound,prelude_input_types) =
  input_declarative_stage "repl_input_prelude_types"
  initial_input_types;
val (repl_input_before_ast_types_sound,before_ast_input_types) =
  input_declarative_stage "repl_input_before_ast_types"
  prelude_input_types;
val (repl_input_ast_types_sound,_) = input_declarative_stage "repl_input_ast_types"
  before_ast_input_types;
val (repl_input_ast_module_types_sound,ast_module_input_types) =
  input_declarative_stage "repl_input_ast_module_types"
  before_ast_input_types;
val (repl_input_final_types_sound,_) = input_declarative_stage "repl_input_final_types"
  ast_module_input_types;

Theorem repl_input_final_checkpoint_sound =
  repl_input_final_types_sound
  |> PURE_REWRITE_RULE [repl_input_stage_final_types];

(* The complete source prelude includes ordering, although only option and
   sum are protected input types. No allocation is omitted from the map. *)
Definition input_prelude_allocation_tds_def:
  input_prelude_allocation_tds = FLAT (MAP (\dec. case dec of
    Dtype locs tds => tds | _ => []) repl_input_prelude_prog)
End

val input_prelude_groups = EVAL ``input_prelude_allocation_tds`` |> concl |> rhs
  |> listSyntax.dest_list |> fst;
val input_prelude_identities = map (fn td => let
  val name = td |> pairSyntax.strip_pair |> el 2
  val ty = EVAL ``nsLookup (FST repl_input_prelude_types).inf_t (Short ^name)``
    |> concl |> rhs |> optionSyntax.dest_some |> pairSyntax.dest_pair |> snd
  val _ = match_term ``typeSystem$Tapp args identity`` ty
  in rand ty end) input_prelude_groups;

Definition input_prelude_allocation_ids_def:
  input_prelude_allocation_ids =
    ^(listSyntax.mk_list (input_prelude_identities, ``:num``))
End

Definition input_prelude_allocation_tenvT_def:
  input_prelude_allocation_tenvT :
    (mlstring,mlstring,mlstring list # typeSystem$t) namespace =
  alist_to_ns (MAP2 (\(tvs,tn,ctors) ti. (tn,(tvs,Tapp (MAP Tvar tvs) ti)))
    input_prelude_allocation_tds input_prelude_allocation_ids)
End

Theorem input_prelude_allocation_ctor_check =
  ``check_ctor_tenv (nsAppend input_prelude_allocation_tenvT prim_tenv.t)
      input_prelude_allocation_tds`` |> EVAL |> EQT_ELIM;

Theorem input_prelude_allocation_ids_interval =
  ``input_prelude_allocation_ids = GENLIST (\offset. start_type_id + offset)
      (LENGTH input_prelude_allocation_tds)`` |> EVAL |> EQT_ELIM;

Theorem input_prelude_allocation_value_namespace =
  ``(ienv_to_tenv (FST repl_input_prelude_types)).v = prim_tenv.v``
  |> EVAL |> EQT_ELIM;

Theorem input_prelude_allocation_environment_ok =
  MATCH_MP env_rel_ienv_to_tenv
    (CONJUNCT1 repl_input_prelude_types_sound)
  |> PURE_REWRITE_RULE [envRelTheory.env_rel_def] |> CONJUNCT2 |> CONJUNCT1;

Theorem input_prelude_allocation_constructor_namespace:
  (ienv_to_tenv (FST repl_input_prelude_types)).c =
  nsAppend (build_ctor_tenv (nsAppend input_prelude_allocation_tenvT prim_tenv.t)
      input_prelude_allocation_tds input_prelude_allocation_ids) prim_tenv.c
Proof
  EVAL_TAC
QED

Theorem input_prelude_allocation_evaluation:
  evaluate_decs (st:'ffi semanticPrimitives$state) env repl_input_prelude_prog =
  evaluate_decs st env [Dtype NoLocs input_prelude_allocation_tds]
Proof
  EVAL_TAC >> simp []
QED

Definition input_prelude_allocation_map_def:
  input_prelude_allocation_map stamp = FEMPTY |++ REVERSE
    (type_def_to_ctMap (nsAppend input_prelude_allocation_tenvT prim_tenv.t)
      stamp input_prelude_allocation_tds input_prelude_allocation_ids)
End

Theorem input_prelude_allocation_setup:
  ALL_DISTINCT input_prelude_allocation_ids /\
  DISJOINT (set input_prelude_allocation_ids)
    (set (Tlist_num :: Tbool_num :: prim_type_nums)) /\
  LENGTH input_prelude_allocation_ids = LENGTH input_prelude_allocation_tds
Proof
  EVAL_TAC >> simp []
QED

Theorem input_prelude_allocation_invariant:
  type_sound_invariant (st:'ffi semanticPrimitives$state) env ctMap tenvS {} prim_tenv /\
  DISJOINT (set input_prelude_allocation_ids) (FRANGE ((SND o SND) o_f ctMap)) ==>
  let allocated = input_prelude_allocation_map st.next_type_stamp;
      result_map = FUNION allocated ctMap;
      result_env = extend_dec_env
        <|v := nsEmpty;
          c := build_tdefs st.next_type_stamp input_prelude_allocation_tds|> env;
      result_st = st with next_type_stamp :=
        st.next_type_stamp + LENGTH input_prelude_allocation_tds
  in
    type_sound_invariant result_st result_env result_map tenvS {}
      (ienv_to_tenv (FST repl_input_prelude_types)) /\
    FRANGE ((SND o SND) o_f result_map) DIFF FRANGE ((SND o SND) o_f ctMap)
      SUBSET set input_prelude_allocation_ids /\
    preserves_datatype_signatures (set input_prelude_allocation_ids) ctMap result_map /\
    (!ti. MEM ti input_prelude_allocation_ids ==>
      datatype_signature result_map ti = datatype_signature allocated ti)
Proof
  strip_tac >>
  mp_tac (datatype_allocation_type_sound_retarget |> Q.INST
    [`type_identities` |-> `input_prelude_allocation_ids`,
     `tds` |-> `input_prelude_allocation_tds`,
     `tenvT` |-> `input_prelude_allocation_tenvT`, `tenv` |-> `prim_tenv`,
     `target_tenv` |-> `ienv_to_tenv (FST repl_input_prelude_types)`]) >>
  simp [input_prelude_allocation_setup, input_prelude_allocation_ctor_check,
    input_prelude_allocation_tenvT_def, input_prelude_allocation_environment_ok,
    input_prelude_allocation_constructor_namespace,
    input_prelude_allocation_value_namespace] >>
  strip_tac >>
  fs [input_prelude_allocation_map_def, input_prelude_allocation_tenvT_def]
QED

val input_prelude_stamp = EVAL
  ``(init_state (ffi:'ffi ffi_state)).next_type_stamp``;

Definition input_prelude_initial_stamp_def:
  input_prelude_initial_stamp = ^(input_prelude_stamp |> concl |> rhs)
End

Theorem input_prelude_initial_stamp_from_state = input_prelude_stamp
  |> PURE_REWRITE_RULE [GSYM input_prelude_initial_stamp_def];

val input_prelude_map_eval = EVAL
  ``input_prelude_allocation_map input_prelude_initial_stamp``;
val input_prelude_signature_rules = input_allocation_signature_rules
  (input_prelude_map_eval |> concl |> rhs);

Definition input_prelude_catalogue_def:
  input_prelude_catalogue = FEMPTY |++
    FILTER (\(ti,signature). MEM ti input_prelude_allocation_ids)
      repl_input_catalogue_entries
End

Theorem input_prelude_allocation_signatures:
  EVERY (\(ti,signature).
    datatype_signature (input_prelude_allocation_map input_prelude_initial_stamp) ti =
      signature)
    (FILTER (\(ti,signature). MEM ti input_prelude_allocation_ids)
      repl_input_catalogue_entries)
Proof
  CONV_TAC (RAND_CONV EVAL) >>
  simp ([input_prelude_map_eval, input_signature_empty] @
    input_prelude_signature_rules) >>
  simp [INSERT_UNION_EQ]
QED

Theorem input_prelude_catalogue_matches =
  MATCH_MP input_catalogue_entries_match input_prelude_allocation_signatures
  |> PURE_REWRITE_RULE [GSYM input_prelude_catalogue_def];

Theorem input_prelude_catalogue_restriction:
  input_prelude_catalogue =
  DRESTRICT repl_input_catalogue (set input_prelude_allocation_ids)
Proof
  simp [input_prelude_catalogue_def, repl_input_catalogue_def,
    input_catalogue_restrict_entries]
QED

Theorem input_prelude_catalogue_domain_bound =
  input_prelude_catalogue_restriction
  |> AP_TERM ``FDOM : repl_inputInvariant$datatype_catalogue -> num set``
  |> PURE_REWRITE_RULE [FDOM_DRESTRICT];

Theorem input_prelude_catalogue_extension:
  DISJOINT (set input_prelude_allocation_ids) (FRANGE ((SND o SND) o_f ctMap)) ==>
  catalogue_matches input_prelude_catalogue
    (FUNION (input_prelude_allocation_map input_prelude_initial_stamp) ctMap)
Proof
  strip_tac >> irule input_catalogue_new_signatures >>
  qexistsl_tac [`input_prelude_allocation_map input_prelude_initial_stamp`,
    `input_prelude_allocation_ids`] >>
  simp [input_prelude_catalogue_matches, input_prelude_catalogue_domain_bound,
    SUBSET_DEF] >>
  rw [] >> rewrite_tac [input_prelude_allocation_map_def] >>
  irule typeSysPropsTheory.type_def_to_ctMap_new_signature >> simp []
QED

Theorem input_prelude_primitives_disjoint =
  input_prelude_allocation_setup |> CONJUNCT2 |> CONJUNCT1
  |> PURE_REWRITE_RULE [GSYM primTypesTheory.prim_type_ids_def];

Definition input_seed_catalogue_def:
  input_seed_catalogue = FUNION input_prelude_catalogue input_primitive_catalogue
End

Definition input_prelude_decl_env_def:
  input_prelude_decl_env = <|v := nsEmpty;
    c := build_tdefs input_prelude_initial_stamp input_prelude_allocation_tds|>
End

Definition input_prelude_env_def:
  input_prelude_env = extend_dec_env input_prelude_decl_env init_env
End

Definition input_prelude_state_def:
  input_prelude_state (ffi:'ffi ffi_state) = init_state ffi with
    next_type_stamp := input_prelude_initial_stamp + LENGTH input_prelude_allocation_tds
End

Theorem input_prelude_Prog:
  Prog init_env (init_state (ffi:'ffi ffi_state)) repl_input_prelude_prog
    input_prelude_decl_env (input_prelude_state ffi)
Proof
  simp [Prog_def, input_prelude_state_def] >>
  qexistsl_tac [`0`,`0`] >> EVAL_TAC
QED

Theorem input_prelude_initialization:
  ?ctMap.
    input_typing_witnesses input_seed_catalogue FEMPTY
      (set input_prelude_allocation_ids) (ienv_to_tenv (FST repl_input_prelude_types))
      (input_prelude_state (ffi:'ffi ffi_state)) input_prelude_env ctMap FEMPTY
Proof
  mp_tac input_primitive_initialization >>
  disch_then (qx_choose_then `seed_map` strip_assume_tac) >>
  fs [input_typing_witnesses_def] >>
  strip_assume_tac input_prelude_primitives_disjoint >>
  `DISJOINT (set input_prelude_allocation_ids)
    (FRANGE ((SND o SND) o_f seed_map))` by ASM_SET_TAC [] >>
  `DISJOINT (FDOM input_primitive_catalogue) (set input_prelude_allocation_ids)`
    by ASM_SET_TAC [] >>
  drule_all input_prelude_allocation_invariant >>
  simp [input_prelude_initial_stamp_from_state] >> strip_tac >>
  drule_all catalogue_matches_preserved >> strip_tac >>
  drule input_prelude_catalogue_extension >> strip_tac >>
  qexists_tac `FUNION (input_prelude_allocation_map input_prelude_initial_stamp) seed_map` >>
  simp [input_typing_witnesses_def, input_slots_hold_def,
    input_prelude_state_def, input_prelude_env_def, input_prelude_decl_env_def,
    input_seed_catalogue_def, input_catalogues_union, FDOM_FUNION,
    input_prelude_catalogue_domain_bound] >> ASM_SET_TAC []
QED

val (input_prefix_env_tm,input_prefix_state_tm,input_prefix_ffi) =
  input_decls_result ``ast_prefix_prog`` Decls_ast_prefix;

Definition input_ast_prefix_decl_env_def:
  input_ast_prefix_decl_env = ^input_prefix_env_tm
End

Definition input_ast_prefix_state_def:
  input_ast_prefix_state ^input_prefix_ffi = ^input_prefix_state_tm
End

Definition input_ast_prefix_env_def:
  input_ast_prefix_env = extend_dec_env input_ast_prefix_decl_env init_env
End

Theorem input_ast_prefix_Prog =
  MATCH_MP (MATCH_MP Decls_IMP_Prog Decls_ast_prefix) repl_input_prefix_syntax_ok
  |> PURE_REWRITE_RULE [GSYM input_ast_prefix_decl_env_def,
       GSYM input_ast_prefix_state_def];

Theorem input_basis_candle_allocation_setup:
  DISJOINT
    (set_ids (SND repl_input_prelude_types) (SND repl_input_before_ast_types))
    (set input_prelude_allocation_ids UNION prim_type_ids) /\
  set input_prelude_allocation_ids UNION
    set_ids (SND repl_input_prelude_types) (SND repl_input_before_ast_types) =
    set_ids start_type_id (SND repl_input_before_ast_types)
Proof
  EVAL_TAC >> rw [DISJOINT_DEF, SUBSET_DEF, EXTENSION]
QED

Theorem input_ast_prefix_environment_append:
  input_ast_prefix_decl_env = extend_dec_env basis_delta input_prelude_decl_env ==>
  input_ast_prefix_env = extend_dec_env basis_delta input_prelude_env
Proof
  strip_tac >>
  simp [input_ast_prefix_env_def, input_prelude_env_def,
    semanticPrimitivesPropsTheory.extend_dec_env_assoc]
QED

Theorem input_ast_prefix_initialization:
  ?ctMap tenvS.
    input_typing_witnesses input_seed_catalogue FEMPTY
      (set_ids start_type_id (SND repl_input_before_ast_types))
      (ienv_to_tenv (FST repl_input_before_ast_types))
      (input_ast_prefix_state (ffi:'ffi ffi_state)) input_ast_prefix_env ctMap tenvS
Proof
  mp_tac (MATCH_MP Prog_append_split (input_ast_prefix_Prog |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`
    |> PURE_REWRITE_RULE [repl_input_prefix_partition])) >>
  disch_then (qx_choosel_then [`prelude_delta`,`basis_delta`,`prelude_st`]
    strip_assume_tac) >>
  qpat_x_assum `Prog _ _ repl_input_prelude_prog _ _`
    (mp_then (Pos hd) mp_tac Prog_deterministic) >>
  disch_then (qspecl_then [`input_prelude_state ffi`,`input_prelude_decl_env`]
    mp_tac) >>
  simp [input_prelude_Prog] >> strip_tac >>
  gvs [GSYM input_prelude_env_def] >>
  mp_tac repl_input_before_ast_types_sound >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `basis_tenv` strip_assume_tac))) >>
  mp_tac (input_prelude_initialization |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choose_then `seed_map` strip_assume_tac) >>
  strip_assume_tac input_basis_candle_allocation_setup >>
  `DISJOINT
    (set_ids (SND repl_input_prelude_types) (SND repl_input_before_ast_types))
    (set input_prelude_allocation_ids)` by ASM_SET_TAC [] >>
  `DISJOINT
    (set_ids (SND repl_input_prelude_types) (SND repl_input_before_ast_types))
    prim_type_ids` by ASM_SET_TAC [] >>
  drule_all input_Prog_declarations_preserve >>
  disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
  drule input_ast_prefix_environment_append >> strip_tac >>
  qexistsl_tac [`result_map`,`result_store`] >> fs [] >>
  once_rewrite_tac [GSYM (CONJUNCT2 input_basis_candle_allocation_setup)] >>
  asm_rewrite_tac []
QED

(* A grouped allocation is only a proof-side candidate: emitted declarations
   remain unchanged. Verify its resolved fields and runtime equality before
   using it to construct the final certificate. *)
Definition input_ast_allocation_tds_def:
  input_ast_allocation_tds = FLAT (MAP (\dec. case dec of
    Dtype locs tds => tds | _ => []) ast_type_decs)
End

Definition input_ast_allocation_ids_def:
  input_ast_allocation_ids = MAP SND repl_ast_type_ids
End

Definition input_ast_allocation_tenvT_def:
  input_ast_allocation_tenvT :
    (mlstring,mlstring,mlstring list # typeSystem$t) namespace =
  alist_to_ns (MAP2 (\(tvs,tn,ctors) ti. (tn,(tvs,Tapp (MAP Tvar tvs) ti)))
    input_ast_allocation_tds input_ast_allocation_ids)
End

Theorem input_ast_allocation_ctor_check =
  ``check_ctor_tenv
      (nsAppend input_ast_allocation_tenvT
        (ienv_to_tenv (FST repl_input_before_ast_types)).t)
      input_ast_allocation_tds`` |> EVAL |> EQT_ELIM;

Theorem input_ast_allocation_ids_interval =
  ``input_ast_allocation_ids = GENLIST
      (\offset. SND repl_input_before_ast_types + offset)
      (LENGTH input_ast_allocation_tds)`` |> EVAL |> EQT_ELIM;

(* Sequential Dtype declarations reverse the groups in the abbreviation
   association list. Do not assert structural equality of the full tenv. *)
Theorem input_ast_allocation_constructor_namespace:
  (ienv_to_tenv (FST repl_input_ast_types)).c =
  nsAppend
    (build_ctor_tenv
      (nsAppend input_ast_allocation_tenvT
        (ienv_to_tenv (FST repl_input_before_ast_types)).t)
      input_ast_allocation_tds input_ast_allocation_ids)
    (ienv_to_tenv (FST repl_input_before_ast_types)).c
Proof
  EVAL_TAC
QED

Theorem input_ast_allocation_value_namespace =
  ``(ienv_to_tenv (FST repl_input_ast_types)).v =
    (ienv_to_tenv (FST repl_input_before_ast_types)).v`` |> EVAL |> EQT_ELIM;

Theorem input_ast_allocation_evaluation:
  evaluate_decs (st:'ffi semanticPrimitives$state) env ast_type_decs =
  evaluate_decs st env [Dtype NoLocs input_ast_allocation_tds]
Proof
  EVAL_TAC >> simp []
QED

Theorem input_ast_allocation_environment_ok:
  tenv_ok (ienv_to_tenv (FST repl_input_ast_types))
Proof
  mp_tac (MATCH_MP env_rel_ienv_to_tenv
    (CONJUNCT1 repl_input_ast_types_sound)) >>
  simp [envRelTheory.env_rel_def]
QED

Definition input_ast_allocation_map_def:
  input_ast_allocation_map stamp = FEMPTY |++ REVERSE
    (type_def_to_ctMap
      (nsAppend input_ast_allocation_tenvT
        (ienv_to_tenv (FST repl_input_before_ast_types)).t)
      stamp input_ast_allocation_tds input_ast_allocation_ids)
End

Theorem input_ast_allocation_setup:
  ALL_DISTINCT input_ast_allocation_ids /\
  DISJOINT (set input_ast_allocation_ids)
    (set (Tlist_num :: Tbool_num :: prim_type_nums)) /\
  LENGTH input_ast_allocation_ids = LENGTH input_ast_allocation_tds
Proof
  EVAL_TAC >> simp []
QED

Theorem input_ast_allocation_invariant:
  type_sound_invariant (st:'ffi semanticPrimitives$state) env ctMap tenvS {}
    (ienv_to_tenv (FST repl_input_before_ast_types)) /\
  DISJOINT (set input_ast_allocation_ids) (FRANGE ((SND o SND) o_f ctMap)) ==>
  let allocated = input_ast_allocation_map st.next_type_stamp;
      result_map = FUNION allocated ctMap;
      result_env = extend_dec_env
        <|v := nsEmpty; c := build_tdefs st.next_type_stamp input_ast_allocation_tds|>
        env;
      result_st = st with next_type_stamp :=
        st.next_type_stamp + LENGTH input_ast_allocation_tds
  in
    type_sound_invariant result_st result_env result_map tenvS {}
      (ienv_to_tenv (FST repl_input_ast_types)) /\
    FRANGE ((SND o SND) o_f result_map) DIFF FRANGE ((SND o SND) o_f ctMap)
      SUBSET set input_ast_allocation_ids /\
    preserves_datatype_signatures (set input_ast_allocation_ids) ctMap result_map /\
    (!ti. MEM ti input_ast_allocation_ids ==>
      datatype_signature result_map ti = datatype_signature allocated ti) /\
    weakCT result_map ctMap /\
    type_all_env result_map tenvS
      <|v := nsEmpty; c := build_tdefs st.next_type_stamp input_ast_allocation_tds|>
      <|v := nsEmpty;
        c := build_ctor_tenv
          (nsAppend input_ast_allocation_tenvT
            (ienv_to_tenv (FST repl_input_before_ast_types)).t)
          input_ast_allocation_tds input_ast_allocation_ids;
        t := input_ast_allocation_tenvT|>
Proof
  strip_tac >>
  mp_tac (datatype_allocation_type_sound_retarget |> Q.INST
    [`type_identities` |-> `input_ast_allocation_ids`,
     `tds` |-> `input_ast_allocation_tds`,
     `tenvT` |-> `input_ast_allocation_tenvT`, `tenv` |-> `ienv_to_tenv (FST repl_input_before_ast_types)`,
     `target_tenv` |-> `ienv_to_tenv (FST repl_input_ast_types)`]) >>
  simp [input_ast_allocation_setup, input_ast_allocation_ctor_check,
    input_ast_allocation_tenvT_def, input_ast_allocation_environment_ok,
    input_ast_allocation_constructor_namespace,
    input_ast_allocation_value_namespace] >>
  strip_tac >>
  fs [input_ast_allocation_map_def, input_ast_allocation_tenvT_def]
QED

(* Obtain the incoming runtime stamp from the verified prefix execution. *)
val input_prefix_stamp = EVAL
  ``(^input_prefix_state_tm).next_type_stamp``;

Definition input_ast_initial_stamp_def:
  input_ast_initial_stamp = ^(input_prefix_stamp |> concl |> rhs)
End

val input_ast_map_eval = EVAL
  ``input_ast_allocation_map input_ast_initial_stamp``;

val input_ast_signature_rules = input_allocation_signature_rules
  (input_ast_map_eval |> concl |> rhs);

Theorem input_ast_allocation_signatures:
  EVERY (\(ti,signature).
    datatype_signature (input_ast_allocation_map input_ast_initial_stamp) ti = signature)
    (FILTER (\(ti,signature). MEM ti input_ast_allocation_ids)
      repl_input_catalogue_entries)
Proof
  CONV_TAC (RAND_CONV EVAL) >>
  simp ([input_ast_map_eval, input_signature_empty] @ input_ast_signature_rules) >>
  simp [INSERT_UNION_EQ]
QED

Definition input_ast_catalogue_def:
  input_ast_catalogue = FEMPTY |++
    FILTER (\(ti,signature). MEM ti input_ast_allocation_ids)
      repl_input_catalogue_entries
End

Theorem input_ast_catalogue_matches =
  MATCH_MP input_catalogue_entries_match input_ast_allocation_signatures
  |> PURE_REWRITE_RULE [GSYM input_ast_catalogue_def];

Theorem input_ast_catalogue_restriction:
  input_ast_catalogue =
  DRESTRICT repl_input_catalogue (set input_ast_allocation_ids)
Proof
  simp [input_ast_catalogue_def, repl_input_catalogue_def,
    input_catalogue_restrict_entries]
QED

Theorem input_ast_catalogue_domain:
  FDOM input_ast_catalogue = set input_ast_allocation_ids
Proof
  simp [input_ast_catalogue_restriction, FDOM_DRESTRICT,
    repl_input_catalogue_domain, repl_input_datatype_ids_def,
    input_ast_allocation_ids_def] >> SET_TAC []
QED

Theorem input_ast_catalogue_extension:
  DISJOINT (set input_ast_allocation_ids) (FRANGE ((SND o SND) o_f ctMap)) ==>
  catalogue_matches input_ast_catalogue
    (FUNION (input_ast_allocation_map input_ast_initial_stamp) ctMap)
Proof
  strip_tac >> irule input_catalogue_new_signatures >>
  qexistsl_tac [`input_ast_allocation_map input_ast_initial_stamp`,
    `input_ast_allocation_ids`] >>
  simp [input_ast_catalogue_matches, input_ast_catalogue_domain] >>
  rw [] >> rewrite_tac [input_ast_allocation_map_def] >>
  irule typeSysPropsTheory.type_def_to_ctMap_new_signature >> simp []
QED

Theorem input_ast_program_syntax:
  prog_syntax_ok ast_prog
Proof
  irule ml_progTheory.prog_syntax_ok_isPREFIX >>
  qexists_tac `repl_prog` >>
  rewrite_tac [repl_input_syntax_ok, rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `repl_suffix` >>
  rewrite_tac [repl_moduleProgTheory.repl_prog_partition]
QED

val (input_ast_env_tm,input_ast_state_tm,input_ast_ffi) =
  input_decls_result ``ast_prog`` Decls_ast_prog;

Definition input_ast_decl_env_def:
  input_ast_decl_env = ^input_ast_env_tm
End

Definition input_ast_state_def:
  input_ast_state ^input_ast_ffi = ^input_ast_state_tm
End

Definition input_ast_env_def:
  input_ast_env = extend_dec_env input_ast_decl_env init_env
End

Theorem input_ast_Prog =
  MATCH_MP (MATCH_MP Decls_IMP_Prog Decls_ast_prog) input_ast_program_syntax
  |> PURE_REWRITE_RULE [GSYM input_ast_decl_env_def, GSYM input_ast_state_def];

Theorem input_ast_body_execution:
  ?body_env.
    Prog input_ast_prefix_env (input_ast_prefix_state (ffi:'ffi ffi_state))
      (ast_type_decs ++ ast_pp_decs) body_env (input_ast_state ffi) /\
    input_ast_decl_env = extend_dec_env (write_mod «Ast» body_env empty_env)
      input_ast_prefix_decl_env
Proof
  mp_tac (MATCH_MP Prog_append_split (input_ast_Prog |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`
    |> PURE_REWRITE_RULE [ast_prog_partition])) >>
  disch_then (qx_choosel_then [`prefix_delta`,`module_delta`,`prefix_st`]
    strip_assume_tac) >>
  qpat_x_assum `Prog _ _ ast_prefix_prog _ _`
    (mp_then (Pos hd) mp_tac Prog_deterministic) >>
  disch_then (qspecl_then [`input_ast_prefix_state ffi`,`input_ast_prefix_decl_env`]
    mp_tac) >>
  simp [input_ast_prefix_Prog] >> strip_tac >>
  gvs [GSYM input_ast_prefix_env_def] >>
  drule Prog_module_split >>
  disch_then (qx_choose_then `body_env` strip_assume_tac) >>
  qexists_tac `body_env` >> simp []
QED

Theorem input_ast_datatypes_Prog:
  Prog env (st:'ffi semanticPrimitives$state) ast_type_decs
    <|v := nsEmpty; c := build_tdefs st.next_type_stamp input_ast_allocation_tds|>
    (st with next_type_stamp := st.next_type_stamp + LENGTH input_ast_allocation_tds)
Proof
  simp [Prog_def] >>
  qexistsl_tac [`st.clock`,`st.clock`] >>
  rewrite_tac [input_ast_allocation_evaluation] >>
  simp [Once evaluateTheory.evaluate_decs_def,
    semanticPrimitivesTheory.state_component_equality] >>
  `EVERY check_dup_ctors input_ast_allocation_tds` by EVAL_TAC >>
  simp [Once evaluateTheory.evaluate_decs_def]
QED

Theorem input_ast_prefix_stamp:
  (input_ast_prefix_state (ffi:'ffi ffi_state)).next_type_stamp =
    input_ast_initial_stamp
Proof
  simp [input_ast_prefix_state_def, input_ast_initial_stamp_def] >> EVAL_TAC
QED

Definition input_ast_types_decl_env_def:
  input_ast_types_decl_env =
    <|v := nsEmpty; c := build_tdefs input_ast_initial_stamp input_ast_allocation_tds|>
End

Definition input_ast_types_state_def:
  input_ast_types_state ffi = input_ast_prefix_state ffi with next_type_stamp :=
    (input_ast_prefix_state ffi).next_type_stamp + LENGTH input_ast_allocation_tds
End

Definition input_ast_types_env_def:
  input_ast_types_env = extend_dec_env input_ast_types_decl_env input_ast_prefix_env
End

Theorem input_ast_datatypes_actual_Prog:
  Prog input_ast_prefix_env (input_ast_prefix_state (ffi:'ffi ffi_state))
    ast_type_decs input_ast_types_decl_env (input_ast_types_state ffi)
Proof
  mp_tac (input_ast_datatypes_Prog |> Q.INST
    [`env` |-> `input_ast_prefix_env`,
     `st` |-> `input_ast_prefix_state (ffi:'ffi ffi_state)`]) >>
  simp [input_ast_prefix_stamp, GSYM input_ast_types_decl_env_def,
    input_ast_types_state_def]
QED

Theorem input_ast_pp_execution:
  ?pp_env.
    Prog input_ast_types_env (input_ast_types_state (ffi:'ffi ffi_state))
      ast_pp_decs pp_env (input_ast_state ffi) /\
    input_ast_decl_env = extend_dec_env
      (write_mod «Ast» (extend_dec_env pp_env input_ast_types_decl_env) empty_env)
      input_ast_prefix_decl_env
Proof
  mp_tac (input_ast_body_execution |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choose_then `body_env` strip_assume_tac) >>
  drule Prog_append_split >>
  disch_then (qx_choosel_then [`types_delta`,`pp_env`,`types_st`]
    strip_assume_tac) >>
  qpat_x_assum `Prog _ _ ast_type_decs _ _`
    (mp_then (Pos hd) mp_tac Prog_deterministic) >>
  disch_then (qspecl_then [`input_ast_types_state ffi`,`input_ast_types_decl_env`]
    mp_tac) >>
  simp [input_ast_datatypes_actual_Prog] >> strip_tac >>
  gvs [GSYM input_ast_types_env_def] >>
  qexists_tac `pp_env` >> simp []
QED

Theorem input_ast_joint_allocation_setup:
  DISJOINT (set input_ast_allocation_ids)
    (set_ids start_type_id (SND repl_input_before_ast_types) UNION prim_type_ids) /\
  DISJOINT (FDOM input_seed_catalogue) (set input_ast_allocation_ids) /\
  set_ids start_type_id (SND repl_input_before_ast_types) UNION
    set input_ast_allocation_ids =
    set_ids start_type_id (SND repl_input_ast_types)
Proof
  EVAL_TAC >>
  rw [finite_mapTheory.FDOM_FUNION, DISJOINT_DEF, SUBSET_DEF] >>
  rw [EXTENSION]
QED

Theorem input_joint_catalogue_partition:
  repl_input_catalogue = FUNION input_ast_catalogue input_seed_catalogue
Proof
  EVAL_TAC >>
  simp_tac (std_ss ++ numSimps.ARITH_ss)
    [FUNION_FUPDATE_1, FUNION_FEMPTY_1, FUPDATE_COMMUTES]
QED

Definition input_ast_types_tenv_def:
  input_ast_types_tenv =
    <|v := nsEmpty;
      c := build_ctor_tenv
        (nsAppend input_ast_allocation_tenvT
          (ienv_to_tenv (FST repl_input_before_ast_types)).t)
        input_ast_allocation_tds input_ast_allocation_ids;
      t := input_ast_allocation_tenvT|>
End

Theorem input_ast_datatypes_initialization:
  ?ctMap tenvS.
    input_typing_witnesses repl_input_catalogue FEMPTY
      (set_ids start_type_id (SND repl_input_ast_types))
      (ienv_to_tenv (FST repl_input_ast_types))
      (input_ast_types_state (ffi:'ffi ffi_state)) input_ast_types_env ctMap tenvS /\
    type_all_env ctMap tenvS input_ast_types_decl_env input_ast_types_tenv /\
    type_all_env ctMap tenvS input_ast_prefix_env
      (ienv_to_tenv (FST repl_input_before_ast_types))
Proof
  mp_tac (input_ast_prefix_initialization |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choosel_then [`prefix_map`,`prefix_store`] strip_assume_tac) >>
  fs [input_typing_witnesses_def] >>
  strip_assume_tac input_ast_joint_allocation_setup >>
  `DISJOINT (set input_ast_allocation_ids)
    (FRANGE ((SND o SND) o_f prefix_map))` by ASM_SET_TAC [] >>
  drule_all input_ast_allocation_invariant >>
  simp [LET_THM, input_ast_prefix_stamp] >> strip_tac >>
  drule_all catalogue_matches_preserved >> strip_tac >>
  drule input_ast_catalogue_extension >> strip_tac >>
  qexistsl_tac [`FUNION (input_ast_allocation_map input_ast_initial_stamp) prefix_map`,
    `prefix_store`] >>
  `FDOM repl_input_catalogue SUBSET
    set_ids start_type_id (SND repl_input_ast_types) UNION prim_type_ids` by (
    rewrite_tac [input_joint_catalogue_partition, FDOM_FUNION,
      input_ast_catalogue_domain] >> ASM_SET_TAC []) >>
  `FRANGE ((SND o SND) o_f
    FUNION (input_ast_allocation_map input_ast_initial_stamp) prefix_map) SUBSET
    set_ids start_type_id (SND repl_input_ast_types) UNION prim_type_ids`
    by ASM_SET_TAC [] >>
  simp [input_ast_types_state_def, input_ast_types_env_def,
    input_ast_types_decl_env_def, input_ast_prefix_stamp,
    input_joint_catalogue_partition, input_catalogues_union,
    input_ast_types_tenv_def] >>
  qpat_x_assum `type_sound_invariant (input_ast_prefix_state _) _ _ _ _ _`
    (mp_tac o REWRITE_RULE [typeSoundInvariantsTheory.type_sound_invariant_def]) >>
  strip_tac >>
  drule_all (SPEC_ALL weakeningTheory.type_all_env_weakening
    |> Q.INST [`tenvS'` |-> `tenvS`]
    |> SIMP_RULE std_ss [weakeningTheory.weakS_refl]) >> simp []
QED

val input_ast_pp_start = ``repl_input_ast_types``;
val input_ast_pp_initial = EVAL
  ``infer$init_infer_state <|next_id := SND ^input_ast_pp_start|>``
  |> concl |> rhs;

val input_ast_pp_env_ok = CONJUNCT1 repl_input_ast_types_sound;
val input_ast_pp_bound = EVAL ``start_type_id <= (^input_ast_pp_initial).next_id``
  |> EQT_ELIM;
val input_ast_pp_canonical_typing = MATCH_MP (CONJUNCT2 infer_d_sound_canonical)
  (LIST_CONJ [input_ast_pp_inference_thm, input_ast_pp_env_ok, input_ast_pp_bound])
  |> PURE_REWRITE_RULE [input_ast_pp_allocation_interval,
       GSYM input_ast_pp_tenv_def];

Theorem input_ast_pp_typing:
  type_ds T (ienv_to_tenv (FST repl_input_ast_types))
    ast_pp_decs {} input_ast_pp_tenv
Proof
  simp [input_ast_pp_canonical_typing]
QED

Definition input_ast_body_tenv_def:
  input_ast_body_tenv = extend_dec_tenv input_ast_pp_tenv
    (ienv_to_tenv (FST repl_input_ast_types))
End

Definition input_ast_exports_tenv_def:
  input_ast_exports_tenv = extend_dec_tenv input_ast_pp_tenv input_ast_types_tenv
End

Theorem input_ast_module_static_components:
  (extend_dec_tenv (tenvLift «Ast» input_ast_exports_tenv)
    (ienv_to_tenv (FST repl_input_before_ast_types))).c =
    (ienv_to_tenv (FST repl_input_ast_module_types)).c /\
  (extend_dec_tenv (tenvLift «Ast» input_ast_exports_tenv)
    (ienv_to_tenv (FST repl_input_before_ast_types))).v =
    (ienv_to_tenv (FST repl_input_ast_module_types)).v
Proof
  rewrite_tac [input_ast_exports_tenv_def, input_ast_pp_tenv_def,
    input_ast_pp_ienv_def, input_ast_types_tenv_def] >>
  EVAL_TAC
QED

Theorem input_ast_pp_initialization:
  ?pp_env ctMap tenvS.
    input_ast_decl_env = extend_dec_env
      (write_mod «Ast» (extend_dec_env pp_env input_ast_types_decl_env) empty_env)
      input_ast_prefix_decl_env /\
    input_typing_witnesses repl_input_catalogue FEMPTY
      (set_ids start_type_id (SND repl_input_ast_types)) input_ast_body_tenv
      (input_ast_state (ffi:'ffi ffi_state)) (extend_dec_env pp_env input_ast_types_env)
      ctMap tenvS /\
    type_all_env ctMap tenvS pp_env input_ast_pp_tenv /\
    type_all_env ctMap tenvS input_ast_types_decl_env input_ast_types_tenv /\
    type_all_env ctMap tenvS input_ast_prefix_env
      (ienv_to_tenv (FST repl_input_before_ast_types))
Proof
  mp_tac (input_ast_datatypes_initialization |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choosel_then [`types_map`,`types_store`] strip_assume_tac) >>
  mp_tac (input_ast_pp_execution |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choose_then `pp_env` strip_assume_tac) >>
  assume_tac input_ast_pp_typing >>
  drule_all (input_Prog_declarations_preserve |> Q.INST [`new_ids` |-> `{}`]
    |> SIMP_RULE std_ss [DISJOINT_EMPTY, UNION_EMPTY]) >>
  disch_then (qx_choosel_then [`pp_map`,`pp_store`] strip_assume_tac) >>
  qexistsl_tac [`pp_env`,`pp_map`,`pp_store`] >>
  simp [input_ast_body_tenv_def] >>
  conj_tac >> irule weakeningTheory.type_all_env_weakening >>
  qexistsl_tac [`types_map`,`types_store`] >>
  simp [typeSoundTheory.store_type_extension_weakS]
QED

Theorem input_ast_environment_append:
  input_ast_decl_env = extend_dec_env module_delta input_ast_prefix_decl_env ==>
  input_ast_env = extend_dec_env module_delta input_ast_prefix_env
Proof
  strip_tac >>
  simp [input_ast_env_def, input_ast_prefix_env_def,
    semanticPrimitivesPropsTheory.extend_dec_env_assoc]
QED

Theorem input_ast_module_environment_ok:
  tenv_ok (ienv_to_tenv (FST repl_input_ast_module_types))
Proof
  mp_tac (MATCH_MP env_rel_ienv_to_tenv
    (CONJUNCT1 repl_input_ast_module_types_sound)) >>
  simp [envRelTheory.env_rel_def]
QED

Theorem input_ast_module_counter:
  SND repl_input_ast_types = SND repl_input_ast_module_types
Proof
  EVAL_TAC
QED

Theorem input_ast_module_initialization:
  ?ctMap tenvS.
    input_typing_witnesses repl_input_catalogue FEMPTY
      (set_ids start_type_id (SND repl_input_ast_module_types))
      (ienv_to_tenv (FST repl_input_ast_module_types))
      (input_ast_state (ffi:'ffi ffi_state)) input_ast_env ctMap tenvS
Proof
  mp_tac (input_ast_pp_initialization |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choosel_then [`pp_env`,`body_map`,`body_store`] strip_assume_tac) >>
  `type_all_env body_map body_store
    (extend_dec_env pp_env input_ast_types_decl_env) input_ast_exports_tenv` by (
    rewrite_tac [input_ast_exports_tenv_def] >>
    irule type_all_env_extend >> simp []) >>
  `type_all_env body_map body_store
    (write_mod «Ast» (extend_dec_env pp_env input_ast_types_decl_env) empty_env)
    (tenvLift «Ast» input_ast_exports_tenv)` by (
    simp [write_mod_def, empty_env_def] >>
    irule type_all_env_module >> simp []) >>
  `type_all_env body_map body_store
    (extend_dec_env
      (write_mod «Ast» (extend_dec_env pp_env input_ast_types_decl_env) empty_env)
      input_ast_prefix_env)
    (extend_dec_tenv (tenvLift «Ast» input_ast_exports_tenv)
      (ienv_to_tenv (FST repl_input_before_ast_types)))` by (
    irule type_all_env_extend >> simp []) >>
  drule input_ast_environment_append >> strip_tac >>
  qexistsl_tac [`body_map`,`body_store`] >>
  fs [input_typing_witnesses_def,
    typeSoundInvariantsTheory.type_sound_invariant_def,
    typeSoundInvariantsTheory.type_all_env_def, input_ast_module_counter,
    input_ast_module_environment_ok, input_ast_module_static_components]
QED

val input_repl_execution = REWRITE_RULE
  [SNOC_APPEND, APPEND, GSYM repl_moduleProgTheory.repl_prog_def]
  repl_moduleProgTheory.Decls_repl_prog;
val (input_repl_env_tm,input_repl_state_tm,input_repl_ffi) =
  input_decls_result ``repl_prog`` input_repl_execution;

Definition input_repl_decl_env_def:
  input_repl_decl_env = ^input_repl_env_tm
End

Definition input_repl_state_def:
  input_repl_state ^input_repl_ffi = ^input_repl_state_tm
End

Theorem input_repl_Prog =
  MATCH_MP (MATCH_MP Decls_IMP_Prog input_repl_execution) repl_input_syntax_ok
  |> PURE_REWRITE_RULE [GSYM input_repl_decl_env_def, GSYM input_repl_state_def];

Theorem input_repl_suffix_execution:
  ?suffix_env.
    Prog input_ast_env (input_ast_state (ffi:'ffi ffi_state)) repl_suffix
      suffix_env (input_repl_state ffi) /\
    input_repl_decl_env = extend_dec_env suffix_env input_ast_decl_env
Proof
  mp_tac (MATCH_MP Prog_append_split (input_repl_Prog |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`
    |> PURE_REWRITE_RULE [repl_moduleProgTheory.repl_prog_partition])) >>
  disch_then (qx_choosel_then [`ast_delta`,`suffix_env`,`ast_st`]
    strip_assume_tac) >>
  qpat_x_assum `Prog _ _ ast_prog _ _`
    (mp_then (Pos hd) mp_tac Prog_deterministic) >>
  disch_then (qspecl_then [`input_ast_state ffi`,`input_ast_decl_env`] mp_tac) >>
  simp [input_ast_Prog] >> strip_tac >>
  gvs [GSYM input_ast_env_def] >>
  qexists_tac `suffix_env` >> simp []
QED

Theorem input_repl_environment_append:
  input_repl_decl_env = extend_dec_env suffix_env input_ast_decl_env ==>
  repl_prog_env = extend_dec_env suffix_env input_ast_env
Proof
  strip_tac >>
  simp [repl_init_typesTheory.repl_prog_env_def, GSYM input_repl_decl_env_def,
    input_ast_env_def, merge_env_def, semanticPrimitivesTheory.extend_dec_env_def,
    namespacePropsTheory.nsAppend_assoc]
QED

Theorem input_repl_suffix_allocation_setup:
  DISJOINT
    (set_ids (SND repl_input_ast_module_types) (SND repl_prog_types))
    (set_ids start_type_id (SND repl_input_ast_module_types) UNION prim_type_ids) /\
  set_ids start_type_id (SND repl_input_ast_module_types) UNION
    set_ids (SND repl_input_ast_module_types) (SND repl_prog_types) =
    set_ids start_type_id (SND repl_prog_types)
Proof
  EVAL_TAC >> rw [DISJOINT_DEF, SUBSET_DEF] >> rw [EXTENSION]
QED

Theorem input_repl_initialization:
  ?ctMap tenvS.
    input_typing_witnesses repl_input_catalogue FEMPTY
      (set_ids start_type_id (SND repl_prog_types))
      (ienv_to_tenv (FST repl_prog_types))
      (input_repl_state (ffi:'ffi ffi_state)) repl_prog_env ctMap tenvS
Proof
  mp_tac (input_ast_module_initialization |> GEN_ALL
    |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choosel_then [`ast_map`,`ast_store`] strip_assume_tac) >>
  mp_tac (input_repl_suffix_execution |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choose_then `suffix_env` strip_assume_tac) >>
  mp_tac repl_input_final_checkpoint_sound >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `suffix_tenv` strip_assume_tac))) >>
  strip_assume_tac input_repl_suffix_allocation_setup >>
  `DISJOINT (set_ids (SND repl_input_ast_module_types) (SND repl_prog_types))
    (set_ids start_type_id (SND repl_input_ast_module_types))`
    by ASM_SET_TAC [] >>
  `DISJOINT (set_ids (SND repl_input_ast_module_types) (SND repl_prog_types))
    prim_type_ids` by ASM_SET_TAC [] >>
  drule_all input_Prog_declarations_preserve >>
  disch_then (qx_choosel_then [`repl_map`,`repl_store`] strip_assume_tac) >>
  drule input_repl_environment_append >> strip_tac >>
  qexistsl_tac [`repl_map`,`repl_store`] >> fs [] >>
  once_rewrite_tac [GSYM (CONJUNCT2 input_repl_suffix_allocation_setup)] >>
  asm_rewrite_tac []
QED

(* All five inversions use exactly this one map/store-typing assumption. *)
val input_env_typing = ASSUME
  ``type_all_env ctMap tenvS repl_prog_env
    (ienv_to_tenv (FST repl_prog_types))``;
val input_slot_typings = ListPair.map (fn (value_th,type_th) =>
  MATCH_MP typeSoundInvariantsTheory.type_all_env_reference
    (LIST_CONJ [input_env_typing,value_th,type_th]))
  (CONJUNCTS repl_input_slot_values, CONJUNCTS repl_input_slot_types);

val input_entries_typed =
  ``EVERY (\(loc,ty). check_freevars 0 [] ty /\
    FLOOKUP tenvS loc = SOME (Ref_t ty)) repl_input_slot_entries``
  |> SIMP_CONV std_ss
    ([repl_input_slot_entries_def, EVERY_DEF] @ input_slot_typings)
  |> EQT_ELIM;

Theorem repl_input_slots_from_environment =
  MATCH_MP input_slots_hold_entries input_entries_typed
  |> PURE_REWRITE_RULE [GSYM repl_input_slots_def]
  |> DISCH (concl input_env_typing) |> GEN_ALL;

Theorem repl_initial_input_certificate:
  initial_input_certificate repl_input_catalogue repl_input_slots
    (set_ids start_type_id (SND repl_prog_types))
    (ienv_to_tenv (FST repl_prog_types))
    (input_repl_state (ffi:'ffi ffi_state)) repl_prog_env
Proof
  mp_tac (input_repl_initialization |> GEN_ALL |> Q.ISPEC `ffi:'ffi ffi_state`) >>
  disch_then (qx_choosel_then [`initial_map`,`initial_store`] strip_assume_tac) >>
  `type_all_env initial_map initial_store repl_prog_env
    (ienv_to_tenv (FST repl_prog_types))` by
    fs [input_typing_witnesses_def,
      typeSoundInvariantsTheory.type_sound_invariant_def] >>
  drule repl_input_slots_from_environment >> strip_tac >>
  simp [initial_input_certificate_def] >>
  qexistsl_tac [`initial_map`,`initial_store`] >>
  fs [input_typing_witnesses_def]
QED

(* The public existence certificate must not rest on assumptions or admissions. *)
val _ = let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag repl_initial_input_certificate)
  in
    if null (hyp repl_initial_input_certificate) andalso null axioms andalso
      List.all (fn name => name = "DISK_THM") oracles then ()
    else failwith "The initial input certificate has assumptions or admissions"
  end;
