(*
  Canonical forms for the actual registered AST family. Metadata, root
  proofs, recursive families and encoder correspondence share this owner.
  Identities remain parameters; signatures come from the registered module.
*)
Theory astCanonical
Ancestors
  astProg typeRepCanonical typeRepPreludeCanonical typeSoundInvariants
  typeSystem semanticPrimitives namespace ml_translator std_prelude ast evaluate_skip
Libs
  preamble ml_translatorLib astSyntax[qualified]
  semanticPrimitivesSyntax[qualified] mlstringSyntax[qualified]

(* Registration-derived metadata and coverage. *)
val canonical_type_groups = ast_type_decs_def |> concl |> rand
  |> listSyntax.dest_list |> fst
  |> map (fn dec => dec |> astSyntax.dest_Dtype |> snd
       |> listSyntax.dest_list |> fst)
  |> List.concat;

val canonical_representation_defs = map (fn group => let
  val name = group |> pairSyntax.strip_pair |> el 2
    |> mlstringSyntax.dest_mlstring
  in DB.fetch "astProg" (String.map Char.toUpper name ^ "_TYPE_def") end)
  canonical_type_groups;

(* Check every declared constructor against its representation clause; stamps
   and arities are read from the registered declarations. *)
val canonical_stamped_groups = ListPair.map (fn (group,rep_def) => let
  val [params,name,ctors] = pairSyntax.strip_pair group
  val declarations = ctors |> listSyntax.dest_list |> fst
    |> map pairSyntax.dest_pair
  val representation_ctors = CONJUNCTS rep_def |> map (fn clause => let
    val body = clause |> concl |> strip_forall |> snd |> rhs
      |> strip_exists |> snd
    val conv = find_term semanticPrimitivesSyntax.is_Conv body
    val (stamp,values) = semanticPrimitivesSyntax.dest_Conv conv
    val (cn,index) = stamp |> optionSyntax.dest_some
      |> semanticPrimitivesSyntax.dest_TypeStamp
    val arity = values |> listSyntax.dest_list |> fst |> length
    in (cn,index,arity) end)
  val _ = if length representation_ctors = length declarations andalso
      length (mk_set (map (fn (cn,_,_) => mlstringSyntax.dest_mlstring cn)
        representation_ctors)) =
        length representation_ctors then ()
    else failwith "AST declaration/representation constructor coverage mismatch"
  val stamped_ctors = map (fn (cn,fields) => let
    val (_,index,arity) = List.find (fn (name,_,_) => aconv name cn)
      representation_ctors |> valOf
    val _ = if arity = length (fst (listSyntax.dest_list fields)) then ()
      else failwith "AST declaration/representation constructor arity mismatch"
    in pairSyntax.list_mk_pair [cn,index,fields] end) declarations
  in pairSyntax.mk_pair (name,pairSyntax.mk_pair (params,
    listSyntax.mk_list (stamped_ctors,``:mlstring # num # ast_t list``))) end)
  (canonical_type_groups,canonical_representation_defs);

Definition ast_canonical_stamped_declarations_def:
  ast_canonical_stamped_declarations =
    ^(listSyntax.mk_list (canonical_stamped_groups,
      ``:mlstring # mlstring list # (mlstring # num # ast_t list) list``))
End

Definition ast_canonical_type_groups_def:
  ast_canonical_type_groups =
    ^(listSyntax.mk_list (canonical_type_groups,
      ``:mlstring list # mlstring # (mlstring # ast_t list) list``))
End

Definition ast_canonical_type_names_def:
  ast_canonical_type_names = MAP FST ast_canonical_stamped_declarations
End

Definition ast_canonical_tenvT_def:
  ast_canonical_tenvT base identities =
    nsAppend (alist_to_ns
      (MAP (\(params,name,ctors).
        (name,(params,Tapp (MAP Tvar params) (identities name))))
        ast_canonical_type_groups)) base
End

Definition ast_canonical_signature_def:
  ast_canonical_signature tenvT name =
    case ALOOKUP ast_canonical_stamped_declarations name of
      NONE => {}
    | SOME (params,ctors) =>
        set (MAP (\(cn,index,fields).
          (cn,index,params,MAP (type_name_subst tenvT) fields)) ctors)
End

(* Record the representation dependencies actually occurring in registered
   field predicates, including nested container predicates. *)
val canonical_rep_dependencies = canonical_representation_defs
  |> map (fn theorem => CONJUNCTS theorem |> map (fn clause =>
       clause |> concl |> strip_forall |> snd |> rhs
       |> find_terms (fn tm => let
         val (args,result) = strip_fun (type_of tm)
         in is_const tm andalso result = bool andalso
           not (null args) andalso last args = semanticPrimitivesSyntax.v_ty
           andalso not (same_const tm boolSyntax.equality)
         end)
       |> map (fn tm => let val {Thy,Name,...} = dest_thy_const tm
          in (Thy,Name) end)) |> List.concat)
  |> List.concat |> mk_set;

val canonical_available_rep_defs = canonical_representation_defs @
  [INT_def,CHAR_def,WORD_def,STRING_TYPE_def,BOOL_def,LIST_TYPE_def,
   PAIR_TYPE_def,OPTION_TYPE_def,SUM_TYPE_def];
val canonical_available_reps = map (fn theorem => let
  val head = theorem |> CONJUNCTS |> hd |> concl |> strip_forall |> snd
    |> lhs |> strip_comb |> fst
  val {Thy,Name,...} = dest_thy_const head
  in (Thy,Name) end) canonical_available_rep_defs;
val _ = if List.all (fn dependency => mem dependency canonical_available_reps)
    canonical_rep_dependencies then ()
  else failwith "Unrecognized AST field representation dependency";

Theorem ast_canonical_type_lookups = canonical_type_groups
  |> map (fn group => let
    val [params,name,ctors] = pairSyntax.strip_pair group
    in ``nsLookup (ast_canonical_tenvT base identities) (Short ^name) =
         SOME (^params,Tapp (MAP Tvar ^params) (identities ^name))``
      |> EVAL |> EQT_ELIM end)
  |> LIST_CONJ;

Theorem ast_canonical_signatures = canonical_type_groups
  |> map (fn group => let
    val name = group |> pairSyntax.strip_pair |> el 2
    val lookup = EVAL ``ALOOKUP ast_canonical_stamped_declarations ^name``
    in SIMP_CONV (srw_ss ()) [ast_canonical_signature_def,lookup]
      ``ast_canonical_signature tenvT ^name`` end)
  |> LIST_CONJ;

Theorem ast_canonical_names_distinct:
  ALL_DISTINCT ast_canonical_type_names
Proof
  EVAL_TAC
QED

(* Non-recursive registered roots. *)
Theorem type_rep_complete_lop:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «lop» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) LOP_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures] >>
  metis_tac [LOP_TYPE_def]
QED

Definition ast_canonical_primitive_types_def:
  ast_canonical_primitive_types tenvT <=>
    nsLookup tenvT (Short «int») = SOME ([],Tint) /\
    nsLookup tenvT (Short «char») = SOME ([],Tchar) /\
    nsLookup tenvT (Short «string») = SOME ([],Tstring) /\
    nsLookup tenvT (Short «word8») = SOME ([],Tword8) /\
    nsLookup tenvT (Short «word64») = SOME ([],Tword64)
End

Theorem ast_canonical_primitive_fields:
  ast_canonical_primitive_types tenvT ==>
  type_name_subst tenvT (Atapp [] (Short «int»)) = Tint /\
  type_name_subst tenvT (Atapp [] (Short «char»)) = Tchar /\
  type_name_subst tenvT (Atapp [] (Short «string»)) = Tstring /\
  type_name_subst tenvT (Atapp [] (Short «word8»)) = Tword8 /\
  type_name_subst tenvT (Atapp [] (Short «word64»)) = Tword64
Proof
  rw [ast_canonical_primitive_types_def, type_name_subst_def] >>
  simp [Tint_def, Tchar_def, Tstring_def, Tword8_def, Tword64_def,
    type_subst_def]
QED

Theorem type_rep_complete_shift:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «shift» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) SHIFT_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures] >>
  metis_tac [SHIFT_TYPE_def]
QED

Theorem type_rep_complete_word_size:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «word_size» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) WORD_SIZE_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures] >>
  metis_tac [WORD_SIZE_TYPE_def]
QED

Theorem type_rep_complete_thunk_mode:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «thunk_mode» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) THUNK_MODE_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures] >>
  metis_tac [THUNK_MODE_TYPE_def]
QED

Theorem type_rep_complete_opb:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «opb» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) OPB_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures] >>
  metis_tac [OPB_TYPE_def]
QED

Theorem type_rep_complete_lit:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  ast_canonical_primitive_types tenvT /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «lit» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) LIT_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, LIST_REL_CONS2,
    Tint_def, Tchar_def, Tstring_def, Tword8_def, Tword64_def,
    type_subst_def] >>
  imp_res_tac (REWRITE_RULE [type_rep_complete_def,
    Tint_def, Tchar_def, Tstring_def, Tword8_def, Tword64_def]
    type_rep_complete_primitives) >>
  metis_tac [LIT_TYPE_def]
QED

Theorem type_rep_complete_prim_type:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id =
    ast_canonical_signature (ast_canonical_tenvT base identities) «prim_type» /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «word_size»))
    WORD_SIZE_TYPE ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) PRIM_TYPE_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2] >>
  metis_tac [type_rep_complete_elim, PRIM_TYPE_TYPE_def]
QED

Theorem type_rep_complete_arith:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id =
    ast_canonical_signature (ast_canonical_tenvT base identities) «arith» /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «shift»))
    SHIFT_TYPE ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) ARITH_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2] >>
  metis_tac [type_rep_complete_elim, ARITH_TYPE_def]
QED

Theorem type_rep_complete_thunk_op:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id =
    ast_canonical_signature (ast_canonical_tenvT base identities) «thunk_op» /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «thunk_mode»))
    THUNK_MODE_TYPE ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) THUNK_OP_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2] >>
  metis_tac [type_rep_complete_elim, THUNK_OP_TYPE_def]
QED

Theorem type_rep_complete_test:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  datatype_signature ctMap type_id =
    ast_canonical_signature (ast_canonical_tenvT base identities) «test» /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «opb»))
    OPB_TYPE ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) TEST_TYPE
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2] >>
  metis_tac [type_rep_complete_elim, TEST_TYPE_def]
QED

(* Existential operator witnesses are expanded from the HOL datatype's own
   constructors, so each case reasons only about its matching constructor. *)
fun canonical_exists_statement ast_ty = let
  val predicate = mk_var ("predicate",ast_ty --> bool)
  val value = mk_var ("ast_value",ast_ty)
  val branches = TypeBase.constructors_of ast_ty |> map (fn ctor => let
    val (args,_) = strip_fun (type_of ctor)
    val variables = mapi (fn index => fn ty =>
      mk_var ("payload" ^ Int.toString index,ty)) args
    in list_mk_exists (variables,
      mk_comb (predicate,list_mk_comb (ctor,variables))) end)
  in mk_forall (predicate,mk_eq (mk_exists (value,mk_comb (predicate,value)),
    list_mk_disj branches)) end;

Theorem ast_operator_exists:
  ^(canonical_exists_statement ``:ast$op``)
Proof
  qx_gen_tac `predicate` >> eq_tac
  >- (
    disch_then (qx_choose_then `operator_value` strip_assume_tac) >>
    Cases_on `operator_value` >> metis_tac []) >>
  rpt strip_tac >> metis_tac []
QED

Theorem type_rep_complete_op:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  ast_canonical_primitive_types (ast_canonical_tenvT base identities) /\
  datatype_signature ctMap type_id =
    ast_canonical_signature (ast_canonical_tenvT base identities) «op» /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «arith»)) ARITH_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «prim_type»))
    PRIM_TYPE_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «thunk_op»))
    THUNK_OP_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «test»)) TEST_TYPE ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) OP_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  imp_res_tac type_rep_complete_primitives >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2, Tstring_def] >>
  qpat_x_assum `datatype_signature _ _ = _` kall_tac >>
  simp [ast_operator_exists, OP_TYPE_def] >>
  metis_tac [type_rep_complete_elim]
QED

Theorem type_rep_complete_locs:
  ctMap_ok ctMap /\ ~MEM type_id prim_type_nums /\
  ast_canonical_primitive_types tenvT /\
  datatype_signature ctMap type_id = ast_canonical_signature tenvT «locs» ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] type_id) LOCS_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    Ttup_def, Tint_def, type_subst_def, LIST_REL_CONS2] >>
  imp_res_tac (REWRITE_RULE [Ttup_def] type_v_tuple_shape) >>
  gvs [LIST_REL_CONS2] >>
  imp_res_tac (REWRITE_RULE [type_rep_complete_def, Tint_def]
    type_rep_complete_primitives) >>
  metis_tac [LOCS_TYPE_def, PAIR_TYPE_def]
QED

(* Recursive registered roots and container reasoning. *)
Theorem type_rep_complete_id:
  ctMap_ok ctMap /\ ~MEM (identities «id») prim_type_nums /\
  datatype_signature ctMap (identities «id») =
    ast_canonical_signature (ast_canonical_tenvT base identities) «id» /\
  type_rep_complete tvs ctMap tenvS module_ty module_rep /\
  type_rep_complete tvs ctMap tenvS name_ty name_rep ==>
  type_rep_complete tvs ctMap tenvS
    (Tapp [module_ty;name_ty] (identities «id»)) (ID_TYPE module_rep name_rep)
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >>
  measureInduct_on `v_size value` >> strip_tac >>
  drule_all type_v_datatype_signature >> strip_tac >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2,
    FUPDATE_LIST_THM, FLOOKUP_UPDATE]
  >~ [`ID_TYPE _ _ _ (Conv _ [module_value;tail_value])`]
  >- (
    `?identifier. ID_TYPE module_rep name_rep identifier tail_value` by (
      qpat_x_assum `!child. v_size child < _ ==> _` irule >>
      simp [] >> decide_tac) >>
    metis_tac [type_rep_complete_elim, ID_TYPE_def]) >>
  metis_tac [type_rep_complete_elim, ID_TYPE_def]
QED

Theorem type_rep_complete_ast_t:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  ~MEM (identities «ast_t») prim_type_nums /\
  ast_canonical_primitive_types (ast_canonical_tenvT base identities) /\
  nsLookup (ast_canonical_tenvT base identities) (Short «list») =
    SOME ([list_parameter],Tlist (Tvar list_parameter)) /\
  datatype_signature ctMap (identities «ast_t») =
    ast_canonical_signature (ast_canonical_tenvT base identities) «ast_t» /\
  type_rep_complete tvs ctMap tenvS
    (Tapp [Tstring;Tstring] (identities «id»))
    (ID_TYPE STRING_TYPE STRING_TYPE) ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «ast_t»)) AST_T_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  imp_res_tac type_rep_complete_primitives >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >>
  measureInduct_on `v_size value` >> strip_tac >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [] (identities «ast_t»)) AST_T_TYPE` by (
      rw [type_rep_complete_below_def] >>
      qpat_x_assum `!child. v_size child < _ ==> _` irule >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Tapp [] (identities «ast_t»))) (LIST_TYPE AST_T_TYPE)` by (
      irule type_rep_complete_below_list >> simp []) >>
  drule_all type_v_datatype_signature >>
  disch_then (qx_choosel_then
    [`ctor_name`,`runtime_index`,`ctor_fields`,`ctor_params`,`ctor_types`]
    strip_assume_tac) >>
  `EVERY (\field. v_size field < v_size value) ctor_fields` by (
    rewrite_tac [EVERY_MEM] >> qx_gen_tac `field_value` >> strip_tac >>
    qpat_x_assum `value = Conv _ _` (fn theorem => PURE_REWRITE_TAC [theorem]) >>
    BETA_TAC >> irule v_size_less_constructor >> simp []) >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2,
    FUPDATE_LIST_THM, FLOOKUP_UPDATE, Tlist_def, Tstring_def] >>
  qpat_x_assum `!child. v_size child < _ ==> _` kall_tac >>
  fs [type_rep_complete_below_def, type_rep_complete_def] >> res_tac >>
  fs [] >>
  qpat_x_assum `datatype_signature _ _ = _` kall_tac >>
  POP_ASSUM_LIST (fn assumptions => MAP_EVERY assume_tac
    (filter (not o is_forall o concl) assumptions)) >>
  metis_tac [AST_T_TYPE_def]
QED

Theorem type_rep_complete_pat:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  ~MEM (identities «pat») prim_type_nums /\ ~MEM option_id prim_type_nums /\
  ast_canonical_primitive_types (ast_canonical_tenvT base identities) /\
  nsLookup (ast_canonical_tenvT base identities) (Short «list») =
    SOME ([list_parameter],Tlist (Tvar list_parameter)) /\
  nsLookup (ast_canonical_tenvT base identities) (Short «option») =
    SOME ([option_parameter],Tapp [Tvar option_parameter] option_id) /\
  datatype_signature ctMap (identities «pat») =
    ast_canonical_signature (ast_canonical_tenvT base identities) «pat» /\
  instantiated_datatype_signature
    [Tapp [Tstring;Tstring] (identities «id»)] ctMap option_id =
    option_rep_signature (Tapp [Tstring;Tstring] (identities «id»)) /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «ast_t»)) AST_T_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «lit»)) LIT_TYPE /\
  type_rep_complete tvs ctMap tenvS
    (Tapp [Tstring;Tstring] (identities «id»))
    (ID_TYPE STRING_TYPE STRING_TYPE) ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «pat»)) PAT_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  imp_res_tac type_rep_complete_primitives >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >>
  measureInduct_on `v_size value` >> strip_tac >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [] (identities «pat»)) PAT_TYPE` by (
      rw [type_rep_complete_below_def] >>
      qpat_x_assum `!child. v_size child < _ ==> _` irule >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Tapp [] (identities «pat»))) (LIST_TYPE PAT_TYPE)` by (
      irule type_rep_complete_below_list >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [Tapp [Tstring;Tstring] (identities «id»)] option_id)
    (OPTION_TYPE (ID_TYPE STRING_TYPE STRING_TYPE))` by (
      irule type_rep_complete_below_option >> simp [] >>
      irule type_rep_complete_implies_below >> fs [Tstring_def]) >>
  drule_all type_v_datatype_signature >>
  disch_then (qx_choosel_then
    [`ctor_name`,`runtime_index`,`ctor_fields`,`ctor_params`,`ctor_types`]
    strip_assume_tac) >>
  `EVERY (\field. v_size field < v_size value) ctor_fields` by (
    rewrite_tac [EVERY_MEM] >> qx_gen_tac `field_value` >> strip_tac >>
    qpat_x_assum `value = Conv _ _` (fn theorem => PURE_REWRITE_TAC [theorem]) >>
    BETA_TAC >> irule v_size_less_constructor >> simp []) >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2,
    FUPDATE_LIST_THM, FLOOKUP_UPDATE, Tlist_def, Tstring_def] >>
  qpat_x_assum `!child. v_size child < _ ==> _` kall_tac >>
  fs [type_rep_complete_below_def, type_rep_complete_def] >> res_tac >>
  fs [] >> qpat_x_assum `datatype_signature _ _ = _` kall_tac >>
  POP_ASSUM_LIST (fn assumptions => MAP_EVERY assume_tac
    (filter (not o is_forall o concl) assumptions)) >>
  metis_tac [PAT_TYPE_def]
QED

(* Existential case expansions are derived from HOL's current constructors.
   Large families then simplify to the matching representation clause. *)
Theorem ast_expression_exists:
  ^(canonical_exists_statement ``:ast$exp``)
Proof
  qx_gen_tac `predicate` >> eq_tac
  >- (
    disch_then (qx_choose_then `ast_value` strip_assume_tac) >>
    Cases_on `ast_value` >> metis_tac []) >>
  rpt strip_tac >> metis_tac []
QED

Theorem type_rep_complete_exp:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  ~MEM (identities «exp») prim_type_nums /\ ~MEM option_id prim_type_nums /\
  ast_canonical_primitive_types (ast_canonical_tenvT base identities) /\
  nsLookup (ast_canonical_tenvT base identities) (Short «list») =
    SOME ([list_parameter],Tlist (Tvar list_parameter)) /\
  nsLookup (ast_canonical_tenvT base identities) (Short «option») =
    SOME ([option_parameter],Tapp [Tvar option_parameter] option_id) /\
  datatype_signature ctMap (identities «exp») =
    ast_canonical_signature (ast_canonical_tenvT base identities) «exp» /\
  (!element_ty. instantiated_datatype_signature [element_ty] ctMap option_id =
    option_rep_signature element_ty) /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «ast_t»)) AST_T_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «lit»)) LIT_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «pat»)) PAT_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «op»)) OP_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «lop»)) LOP_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «locs»)) LOCS_TYPE /\
  type_rep_complete tvs ctMap tenvS
    (Tapp [Tstring;Tstring] (identities «id»))
    (ID_TYPE STRING_TYPE STRING_TYPE) ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «exp»)) EXP_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  imp_res_tac type_rep_complete_primitives >>
  imp_res_tac type_rep_complete_implies_below >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >>
  measureInduct_on `v_size value` >> strip_tac >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [] (identities «exp»)) EXP_TYPE` by (
      rw [type_rep_complete_below_def] >>
      qpat_x_assum `!child. v_size child < _ ==> _` irule >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Tapp [] (identities «exp»))) (LIST_TYPE EXP_TYPE)` by (
      irule type_rep_complete_below_list >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist Tstring) (LIST_TYPE STRING_TYPE)` by (
      irule type_rep_complete_below_list >> simp [] >>
      irule type_rep_complete_implies_below >> fs [Tstring_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tapp [] (identities «pat»);Tapp [] (identities «exp»)])
    (PAIR_TYPE PAT_TYPE EXP_TYPE)` by (
      irule type_rep_complete_below_pair >> fs []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Ttup [Tapp [] (identities «pat»);Tapp [] (identities «exp»)]))
    (LIST_TYPE (PAIR_TYPE PAT_TYPE EXP_TYPE))` by (
      irule type_rep_complete_below_list >> fs [Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tstring;Tapp [] (identities «exp»)])
    (PAIR_TYPE STRING_TYPE EXP_TYPE)` by (
      irule type_rep_complete_below_pair >> simp [] >>
      irule type_rep_complete_implies_below >> fs [Tstring_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tstring;Ttup [Tstring;Tapp [] (identities «exp»)]])
    (PAIR_TYPE STRING_TYPE (PAIR_TYPE STRING_TYPE EXP_TYPE))` by (
      irule type_rep_complete_below_pair >> fs [Ttup_def] >>
      irule type_rep_complete_implies_below >> fs [Tstring_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Ttup [Tstring;Ttup [Tstring;Tapp [] (identities «exp»)] ]))
    (LIST_TYPE (PAIR_TYPE STRING_TYPE (PAIR_TYPE STRING_TYPE EXP_TYPE)))` by (
      irule type_rep_complete_below_list >> fs [Tstring_def,Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [Tstring] option_id) (OPTION_TYPE STRING_TYPE)` by (
      irule type_rep_complete_below_option >> simp [] >>
      irule type_rep_complete_implies_below >> fs [Tstring_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [Tapp [Tstring;Tstring] (identities «id»)] option_id)
    (OPTION_TYPE (ID_TYPE STRING_TYPE STRING_TYPE))` by (
      irule type_rep_complete_below_option >> fs [Tstring_def]) >>
  drule_all type_v_datatype_signature >>
  disch_then (qx_choosel_then
    [`ctor_name`,`runtime_index`,`ctor_fields`,`ctor_params`,`ctor_types`]
    strip_assume_tac) >>
  `EVERY (\field. v_size field < v_size value) ctor_fields` by (
    rewrite_tac [EVERY_MEM] >> qx_gen_tac `field_value` >> strip_tac >>
    qpat_x_assum `value = Conv _ _` (fn theorem => PURE_REWRITE_TAC [theorem]) >>
    BETA_TAC >> irule v_size_less_constructor >> simp []) >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2,
    FUPDATE_LIST_THM, FLOOKUP_UPDATE, Tlist_def, Tstring_def, Ttup_def] >>
  qpat_x_assum `!child. v_size child < _ ==> _` kall_tac >>
  fs [type_rep_complete_below_def, type_rep_complete_def] >> res_tac >>
  fs [] >> qpat_x_assum `datatype_signature _ _ = _` kall_tac >>
  POP_ASSUM_LIST (fn assumptions => MAP_EVERY assume_tac
    (filter (not o is_forall o concl) assumptions)) >>
  simp [Once ast_expression_exists,EXP_TYPE_def] >> metis_tac []
QED

Theorem ast_declaration_exists:
  ^(canonical_exists_statement ``:ast$dec``)
Proof
  qx_gen_tac `predicate` >> eq_tac
  >- (
    disch_then (qx_choose_then `ast_value` strip_assume_tac) >>
    Cases_on `ast_value` >> metis_tac []) >>
  rpt strip_tac >> metis_tac []
QED

Theorem type_rep_complete_dec:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  ~MEM (identities «dec») prim_type_nums /\
  ast_canonical_primitive_types (ast_canonical_tenvT base identities) /\
  nsLookup (ast_canonical_tenvT base identities) (Short «list») =
    SOME ([list_parameter],Tlist (Tvar list_parameter)) /\
  datatype_signature ctMap (identities «dec») =
    ast_canonical_signature (ast_canonical_tenvT base identities) «dec» /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «ast_t»)) AST_T_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «pat»)) PAT_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «exp»)) EXP_TYPE /\
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «locs»)) LOCS_TYPE ==>
  type_rep_complete tvs ctMap tenvS (Tapp [] (identities «dec»)) DEC_TYPE
Proof
  strip_tac >> imp_res_tac ast_canonical_primitive_fields >>
  imp_res_tac type_rep_complete_primitives >>
  imp_res_tac type_rep_complete_implies_below >>
  rewrite_tac [type_rep_complete_def] >> qx_gen_tac `value` >>
  measureInduct_on `v_size value` >> strip_tac >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tapp [] (identities «dec»)) DEC_TYPE` by (
      rw [type_rep_complete_below_def] >>
      qpat_x_assum `!child. v_size child < _ ==> _` irule >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    Tstring STRING_TYPE` by (
      irule type_rep_complete_implies_below >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist Tstring) (LIST_TYPE STRING_TYPE)` by (
      irule type_rep_complete_below_list >> fs [Tstring_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Tapp [] (identities «dec»))) (LIST_TYPE DEC_TYPE)` by (
      irule type_rep_complete_below_list >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Tapp [] (identities «ast_t»))) (LIST_TYPE AST_T_TYPE)` by (
      irule type_rep_complete_below_list >> simp []) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tstring;Tapp [] (identities «exp»)])
    (PAIR_TYPE STRING_TYPE EXP_TYPE)` by (
      irule type_rep_complete_below_pair >> fs [Tstring_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tstring;Ttup [Tstring;Tapp [] (identities «exp»)]])
    (PAIR_TYPE STRING_TYPE (PAIR_TYPE STRING_TYPE EXP_TYPE))` by (
      irule type_rep_complete_below_pair >> fs [Tstring_def,Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Ttup [Tstring;Ttup [Tstring;Tapp [] (identities «exp»)] ]))
    (LIST_TYPE (PAIR_TYPE STRING_TYPE (PAIR_TYPE STRING_TYPE EXP_TYPE)))` by (
      irule type_rep_complete_below_list >> fs [Tstring_def,Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tstring;Tlist (Tapp [] (identities «ast_t»))])
    (PAIR_TYPE STRING_TYPE (LIST_TYPE AST_T_TYPE))` by (
      irule type_rep_complete_below_pair >> fs [Tstring_def,Tlist_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Ttup [Tstring;Tlist (Tapp [] (identities «ast_t»))]))
    (LIST_TYPE (PAIR_TYPE STRING_TYPE (LIST_TYPE AST_T_TYPE)))` by (
      irule type_rep_complete_below_list >> fs [Tstring_def,Tlist_def,Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tstring;Tlist (Ttup [Tstring;Tlist (Tapp [] (identities «ast_t»))])])
    (PAIR_TYPE STRING_TYPE
      (LIST_TYPE (PAIR_TYPE STRING_TYPE (LIST_TYPE AST_T_TYPE))))` by (
        irule type_rep_complete_below_pair >> fs [Tstring_def,Tlist_def,Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Ttup [Tlist Tstring;
      Ttup [Tstring;Tlist (Ttup [Tstring;Tlist (Tapp [] (identities «ast_t»))])]])
    (PAIR_TYPE (LIST_TYPE STRING_TYPE)
      (PAIR_TYPE STRING_TYPE
        (LIST_TYPE (PAIR_TYPE STRING_TYPE (LIST_TYPE AST_T_TYPE)))))` by (
          irule type_rep_complete_below_pair >> fs [Tstring_def,Tlist_def,Ttup_def]) >>
  `type_rep_complete_below (v_size value) tvs ctMap tenvS
    (Tlist (Ttup [Tlist Tstring;
      Ttup [Tstring;Tlist (Ttup [Tstring;Tlist (Tapp [] (identities «ast_t»))])]]))
    (LIST_TYPE (PAIR_TYPE (LIST_TYPE STRING_TYPE)
      (PAIR_TYPE STRING_TYPE
        (LIST_TYPE (PAIR_TYPE STRING_TYPE (LIST_TYPE AST_T_TYPE))))))` by (
          irule type_rep_complete_below_list >> fs [Tstring_def,Tlist_def,Ttup_def]) >>
  drule_all type_v_datatype_signature >>
  disch_then (qx_choosel_then
    [`ctor_name`,`runtime_index`,`ctor_fields`,`ctor_params`,`ctor_types`]
    strip_assume_tac) >>
  `EVERY (\field. v_size field < v_size value) ctor_fields` by (
    rewrite_tac [EVERY_MEM] >> qx_gen_tac `field_value` >> strip_tac >>
    qpat_x_assum `value = Conv _ _` (fn theorem => PURE_REWRITE_TAC [theorem]) >>
    BETA_TAC >> irule v_size_less_constructor >> simp []) >>
  gvs [ast_canonical_signatures, type_name_subst_def,
    ast_canonical_type_lookups, type_subst_def, LIST_REL_CONS2,
    FUPDATE_LIST_THM, FLOOKUP_UPDATE, Tlist_def, Tstring_def, Ttup_def] >>
  qpat_x_assum `!child. v_size child < _ ==> _` kall_tac >>
  fs [type_rep_complete_below_def, type_rep_complete_def] >> res_tac >>
  fs [] >> qpat_x_assum `datatype_signature _ _ = _` kall_tac >>
  POP_ASSUM_LIST (fn assumptions => MAP_EVERY assume_tac
    (filter (not o is_forall o concl) assumptions)) >>
  simp [Once ast_declaration_exists,DEC_TYPE_def] >> metis_tac []
QED

(* Complete registered family and proof inventory. *)
val family_groups = ast_canonical_type_groups_def |> concl |> rand
  |> listSyntax.dest_list |> fst;

(* The proof inventory: a registered type without exactly one matching theorem
   here, or a theorem without a registered type, fails the checks below. *)
val family_proofs =
  [type_rep_complete_lop,type_rep_complete_shift,type_rep_complete_word_size,
   type_rep_complete_thunk_mode,type_rep_complete_opb,type_rep_complete_lit,
   type_rep_complete_prim_type,type_rep_complete_arith,type_rep_complete_thunk_op,
   type_rep_complete_test,type_rep_complete_op,type_rep_complete_locs,
   type_rep_complete_id,type_rep_complete_ast_t,type_rep_complete_pat,
   type_rep_complete_exp,type_rep_complete_dec];

val family_roots = map (fn group => let
  val [params,name,ctors] = pairSyntax.strip_pair group
  val source_name = mlstringSyntax.dest_mlstring name
  val rep_def = DB.fetch "astProg"
    (String.map Char.toUpper source_name ^ "_TYPE_def")
  val rep_head = rep_def |> CONJUNCTS |> hd |> concl |> strip_forall |> snd
    |> lhs |> strip_comb |> fst
  val matching_proofs = List.filter (fn theorem => let
    val conclusion = theorem |> concl |> strip_forall |> snd |> strip_imp |> snd
    val (head,args) = strip_comb conclusion
    in length args = 5 andalso same_const head ``type_rep_complete`` andalso
      same_const (fst (strip_comb (last args))) rep_head end) family_proofs
  val _ = if length matching_proofs = 1 then ()
    else failwith ("Missing or duplicate canonical proof for " ^ source_name)
  val string_rep_head = inst (map (fn ty => ty |-> ``:mlstring``)
    (type_vars_in_term rep_head)) rep_head
  val parameter_count = params |> listSyntax.dest_list |> fst |> length
  val representation = list_mk_comb (string_rep_head,
    List.tabulate (parameter_count,fn _ => ``STRING_TYPE``))
  val type_arguments = listSyntax.mk_list
    (List.tabulate (parameter_count,fn _ => ``Tstring``),``:typeSystem$t``)
  val root = ``type_rep_complete tvs ctMap tenvS
    (Tapp ^type_arguments (identities ^name)) ^representation``
  in (name,root,hd matching_proofs) end) family_groups;

val _ = if length family_roots = length family_proofs then ()
  else failwith "Canonical proof inventory contains unregistered roots";

Definition ast_canonical_family_context_def:
  ast_canonical_family_context base identities option_id ctMap <=>
    ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
    (!name. MEM name ast_canonical_type_names ==>
      ~MEM (identities name) prim_type_nums /\
      datatype_signature ctMap (identities name) =
        ast_canonical_signature (ast_canonical_tenvT base identities) name) /\
    ast_canonical_primitive_types (ast_canonical_tenvT base identities) /\
    (?parameter. nsLookup (ast_canonical_tenvT base identities) (Short «list») =
      SOME ([parameter],Tlist (Tvar parameter))) /\
    (?parameter. nsLookup (ast_canonical_tenvT base identities) (Short «option») =
      SOME ([parameter],Tapp [Tvar parameter] option_id)) /\
    ~MEM option_id prim_type_nums /\
    (!element_ty. instantiated_datatype_signature [element_ty] ctMap option_id =
      option_rep_signature element_ty)
End

Theorem ast_canonical_family_entry:
  ast_canonical_family_context base identities option_id ctMap /\
  MEM registered_name ast_canonical_type_names ==>
  ~MEM (identities registered_name) prim_type_nums /\
  datatype_signature ctMap (identities registered_name) =
    ast_canonical_signature (ast_canonical_tenvT base identities) registered_name
Proof
  rw [ast_canonical_family_context_def] >> res_tac
QED

val family_name_members = map (fn (name,_,_) =>
  EVAL ``MEM ^name ast_canonical_type_names`` |> EQT_ELIM) family_roots;

Theorem ast_canonical_family_complete:
  ast_canonical_family_context base identities option_id ctMap ==>
  ^(list_mk_conj (map (fn (_,root,_) => root) family_roots))
Proof
  strip_tac >> MAP_EVERY assume_tac family_name_members >>
  imp_res_tac ast_canonical_family_entry >>
  fs [ast_canonical_family_context_def] >>
  qmatch_asmsub_rename_tac `nsLookup _ (Short «list») = SOME ([list_parameter],_)` >>
  qmatch_asmsub_rename_tac `nsLookup _ (Short «option») = SOME ([option_parameter],_)` >>
  imp_res_tac type_rep_complete_primitives >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «lop»)) LOP_TYPE` by (
    irule type_rep_complete_lop >> simp [] >>
    qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «shift»)) SHIFT_TYPE` by (
    irule type_rep_complete_shift >> simp [] >>
    qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «word_size»))
    WORD_SIZE_TYPE` by (
      irule type_rep_complete_word_size >> simp [] >>
      qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «thunk_mode»))
    THUNK_MODE_TYPE` by (
      irule type_rep_complete_thunk_mode >> simp [] >>
      qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «opb»)) OPB_TYPE` by (
    irule type_rep_complete_opb >> simp [] >>
    qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «lit»)) LIT_TYPE` by (
    irule type_rep_complete_lit >> simp [] >>
    qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «locs»)) LOCS_TYPE` by (
    irule type_rep_complete_locs >> simp [] >>
    qexists_tac `ast_canonical_tenvT base identities` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «prim_type»))
    PRIM_TYPE_TYPE` by (
      irule type_rep_complete_prim_type >> simp [] >>
      qexistsl_tac [`base`,`identities`] >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «arith»)) ARITH_TYPE` by (
    irule type_rep_complete_arith >> simp [] >>
    qexistsl_tac [`base`,`identities`] >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «thunk_op»))
    THUNK_OP_TYPE` by (
      irule type_rep_complete_thunk_op >> simp [] >>
      qexistsl_tac [`base`,`identities`] >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «test»)) TEST_TYPE` by (
    irule type_rep_complete_test >> simp [] >>
    qexistsl_tac [`base`,`identities`] >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «op»)) OP_TYPE` by (
    irule type_rep_complete_op >> simp [] >>
    qexistsl_tac [`base`,`identities`] >> simp []) >>
  `type_rep_complete tvs ctMap tenvS
    (Tapp [Tstring;Tstring] (identities «id»))
    (ID_TYPE STRING_TYPE STRING_TYPE)` by (
      irule type_rep_complete_id >> fs [Tstring_def] >>
      qexists_tac `base` >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «ast_t»)) AST_T_TYPE` by (
    mp_tac (SPEC_ALL type_rep_complete_ast_t) >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «pat»)) PAT_TYPE` by (
    mp_tac (SPEC_ALL type_rep_complete_pat) >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «exp»)) EXP_TYPE` by (
    mp_tac (SPEC_ALL type_rep_complete_exp) >> simp []) >>
  `type_rep_complete tvs ctMap tenvS (Tapp [] (identities «dec»)) DEC_TYPE` by (
    mp_tac (SPEC_ALL type_rep_complete_dec) >> simp []) >>
  fs [Tstring_def]
QED

(* Correspondence with the encoders generated by Ast registration. *)
val _ = translation_extends "astProg";

Theorem ast_dec_type_rep:
  IsTypeRep DEC_v DEC_TYPE
Proof
  irule_at Any (fetch_v_fun ``:ast$dec`` |> snd |> hd) >>
  irule_at Any (fetch_v_fun ``:'a list`` |> snd |> hd) >>
  rpt (irule_at Any (fetch_v_fun ``:ast$exp`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:'a # 'b`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:ast$exp`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:ast$pat`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:ast$lit`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:word8`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:word64`` |> snd |> hd)) >>
  rpt (irule_at Any (fetch_v_fun ``:mlstring`` |> snd |> hd)) >> simp []
QED

Theorem ast_dec_list_type_rep = MATCH_MP IsTypeRep_LIST ast_dec_type_rep;

Theorem ast_dec_list_equality = EqualityType_rule [] ``:ast$dec list``;

Theorem ast_dec_list_representation:
  LIST_TYPE DEC_TYPE decs value <=> LIST_v DEC_v decs = value
Proof
  assume_tac ast_dec_list_type_rep >> assume_tac ast_dec_list_equality >>
  fs [IsTypeRep_def, EqualityType_def] >> metis_tac []
QED

(* The stamps used by the representation definitions, including containers
   and Boolv's constructors. The structural proofs below show these suffice. *)
val canonical_representation_stamps = canonical_available_rep_defs @ [Boolv_def]
  |> map (fn theorem => find_terms semanticPrimitivesSyntax.is_TypeStamp
      (concl theorem))
  |> List.concat |> HOLset.fromList Term.compare |> HOLset.listItems;
val _ = if not (null canonical_representation_stamps) andalso
    List.all (fn stamp => null (free_vars stamp)) canonical_representation_stamps
  then () else failwith "AST representation stamps are not closed";

Definition ast_canonical_representation_stamps_def:
  ast_canonical_representation_stamps =
    ^(listSyntax.mk_list (canonical_representation_stamps, ``:stamp``))
End

Theorem ast_encoder_list_self[local]:
  stamp_rel ft fe (TypeStamp «[]» list_type_num) (TypeStamp «[]» list_type_num) /\
  stamp_rel ft fe (TypeStamp «::» list_type_num) (TypeStamp «::» list_type_num) /\
  (!item. v_rel fr ft fe (element_v item) (element_v item)) ==>
  !items. v_rel fr ft fe (LIST_v element_v items) (LIST_v element_v items)
Proof
  strip_tac >> Induct >> rw [] >>
  simp [Once LIST_v_def] >>
  fs [Once LIST_v_def,v_rel_def,OPTREL_def,list_type_num_def]
QED

Theorem ast_literal_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  !literal. v_rel fr ft fe (LIT_v literal) (LIT_v literal)
Proof
  strip_tac >> qx_gen_tac ‘literal’ >> Cases_on ‘literal’ >>
  fs [ast_canonical_representation_stamps_def,LIT_v_def,INT_v_def,
    CHAR_v_def,STRING_v_def,WORD_v_def,v_rel_def,OPTREL_def]
QED

Theorem ast_identifier_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) /\
  (!name. v_rel fr ft fe (module_v name) (module_v name)) /\
  (!name. v_rel fr ft fe (name_v name) (name_v name)) ==>
  !identifier.
    v_rel fr ft fe (ID_v module_v name_v identifier)
      (ID_v module_v name_v identifier)
Proof
  strip_tac >> Induct >> simp [Once ID_v_def] >>
  fs [Once ID_v_def,ast_canonical_representation_stamps_def,v_rel_def,OPTREL_def]
QED

Theorem ast_type_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  (!ty. v_rel fr ft fe (AST_T_v ty) (AST_T_v ty)) /\
  (!tys. v_rel fr ft fe (AST_T_v_aux_1 tys) (AST_T_v_aux_1 tys))
Proof
  strip_tac >>
  ‘!identifier. v_rel fr ft fe (ID_v STRING_v STRING_v identifier)
    (ID_v STRING_v STRING_v identifier)’ by (
      match_mp_tac ast_identifier_encoder_self >> simp [STRING_v_def,v_rel_def]) >>
  ho_match_mp_tac (TypeBase.induction_of ``:ast$ast_t``) >> rw [] >>
  simp [Once AST_T_v_def] >>
  fs [Once AST_T_v_def,ast_canonical_representation_stamps_def,
    STRING_v_def,v_rel_def,OPTREL_def]
QED

Theorem ast_option_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) /\
  (!item. v_rel fr ft fe (element_v item) (element_v item)) ==>
  !item. v_rel fr ft fe (OPTION_v element_v item) (OPTION_v element_v item)
Proof
  strip_tac >> Cases >>
  fs [OPTION_v_def,ast_canonical_representation_stamps_def,v_rel_def,OPTREL_def]
QED

Theorem ast_pattern_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  (!pattern. v_rel fr ft fe (PAT_v pattern) (PAT_v pattern)) /\
  (!patterns. v_rel fr ft fe (PAT_v_aux_1 patterns) (PAT_v_aux_1 patterns))
Proof
  strip_tac >>
  ‘!literal. v_rel fr ft fe (LIT_v literal) (LIT_v literal)’ by (
    match_mp_tac ast_literal_encoder_self >> simp []) >>
  ‘(!ty. v_rel fr ft fe (AST_T_v ty) (AST_T_v ty)) /\
    (!tys. v_rel fr ft fe (AST_T_v_aux_1 tys) (AST_T_v_aux_1 tys))’ by (
      match_mp_tac ast_type_encoder_self >> simp []) >>
  ‘!identifier. v_rel fr ft fe (ID_v STRING_v STRING_v identifier)
    (ID_v STRING_v STRING_v identifier)’ by (
      match_mp_tac ast_identifier_encoder_self >> simp [STRING_v_def,v_rel_def]) >>
  ‘!constructor.
    v_rel fr ft fe (OPTION_v (ID_v STRING_v STRING_v) constructor)
      (OPTION_v (ID_v STRING_v STRING_v) constructor)’ by (
        match_mp_tac ast_option_encoder_self >> simp []) >>
  ho_match_mp_tac (TypeBase.induction_of ``:ast$pat``) >> rw [] >>
  simp [Once PAT_v_def] >>
  fs [Once PAT_v_def,ast_canonical_representation_stamps_def,STRING_v_def,
    v_rel_def,OPTREL_def]
QED

Theorem ast_encoder_pair_self[local]:
  (!item. v_rel fr ft fe (left_v item) (left_v item)) /\
  (!item. v_rel fr ft fe (right_v item) (right_v item)) ==>
  !pair. v_rel fr ft fe (PAIR_v left_v right_v pair) (PAIR_v left_v right_v pair)
Proof
  strip_tac >> Cases >> simp [PAIR_v_def,v_rel_def]
QED

Theorem ast_leaf_encoders_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  (!arg. v_rel fr ft fe (BOOL_v arg) (BOOL_v arg)) /\
  (!arg. v_rel fr ft fe (LOP_v arg) (LOP_v arg)) /\
  (!arg. v_rel fr ft fe (SHIFT_v arg) (SHIFT_v arg)) /\
  (!arg. v_rel fr ft fe (WORD_SIZE_v arg) (WORD_SIZE_v arg)) /\
  (!arg. v_rel fr ft fe (OPB_v arg) (OPB_v arg)) /\
  (!arg. v_rel fr ft fe (THUNK_MODE_v arg) (THUNK_MODE_v arg)) /\
  (!arg. v_rel fr ft fe (PRIM_v_v arg) (PRIM_v_v arg)) /\
  (!arg. v_rel fr ft fe (LOCS_v arg) (LOCS_v arg))
Proof
  strip_tac >>
  ‘!size. v_rel fr ft fe (WORD_SIZE_v size) (WORD_SIZE_v size)’ by (
    Cases >> fs [WORD_SIZE_v_def,ast_canonical_representation_stamps_def,
      v_rel_def,OPTREL_def]) >>
  ‘!pair. v_rel fr ft fe (PAIR_v INT_v INT_v pair) (PAIR_v INT_v INT_v pair)’ by (
    match_mp_tac ast_encoder_pair_self >> simp [INT_v_def,v_rel_def]) >>
  rpt conj_tac >> simp [] >> Cases >>
  fs [ast_canonical_representation_stamps_def,BOOL_v_def,Boolv_def,
    LOP_v_def,SHIFT_v_def,WORD_SIZE_v_def,OPB_v_def,THUNK_MODE_v_def,
    PRIM_v_v_def,LOCS_v_def,v_rel_def,OPTREL_def]
QED

Theorem ast_operator_encoders_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  (!arg. v_rel fr ft fe (ARITH_v arg) (ARITH_v arg)) /\
  (!arg. v_rel fr ft fe (TEST_v arg) (TEST_v arg)) /\
  (!arg. v_rel fr ft fe (THUNK_OP_v arg) (THUNK_OP_v arg)) /\
  (!arg. v_rel fr ft fe (OP_v arg) (OP_v arg))
Proof
  strip_tac >> mp_tac (SPEC_ALL ast_leaf_encoders_self) >> simp [] >> strip_tac >>
  ‘!arg. v_rel fr ft fe (ARITH_v arg) (ARITH_v arg)’ by (
    Cases >> fs [ARITH_v_def,ast_canonical_representation_stamps_def,
      v_rel_def,OPTREL_def]) >>
  ‘!arg. v_rel fr ft fe (TEST_v arg) (TEST_v arg)’ by (
    Cases >> fs [TEST_v_def,ast_canonical_representation_stamps_def,
      v_rel_def,OPTREL_def]) >>
  ‘!arg. v_rel fr ft fe (THUNK_OP_v arg) (THUNK_OP_v arg)’ by (
    Cases >> fs [THUNK_OP_v_def,ast_canonical_representation_stamps_def,
      v_rel_def,OPTREL_def]) >>
  rpt conj_tac >> simp [] >> Cases >>
  fs [OP_v_def,ast_canonical_representation_stamps_def,STRING_v_def,
    v_rel_def,OPTREL_def]
QED

Theorem ast_expression_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  (!arg. v_rel fr ft fe (EXP_v arg) (EXP_v arg)) /\
  (!arg. v_rel fr ft fe (EXP_v_aux_1 arg) (EXP_v_aux_1 arg)) /\
  (!arg. v_rel fr ft fe (EXP_v_aux_2 arg) (EXP_v_aux_2 arg)) /\
  (!arg. v_rel fr ft fe (EXP_v_aux_3 arg) (EXP_v_aux_3 arg)) /\
  (!arg. v_rel fr ft fe (EXP_v_aux_4 arg) (EXP_v_aux_4 arg)) /\
  (!arg. v_rel fr ft fe (EXP_v_aux_5 arg) (EXP_v_aux_5 arg)) /\
  (!arg. v_rel fr ft fe (EXP_v_aux_6 arg) (EXP_v_aux_6 arg))
Proof
  strip_tac >>
  mp_tac (SPEC_ALL ast_leaf_encoders_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_operator_encoders_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_literal_encoder_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_type_encoder_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_pattern_encoder_self) >> simp [] >> strip_tac >>
  ‘!identifier. v_rel fr ft fe (ID_v STRING_v STRING_v identifier)
    (ID_v STRING_v STRING_v identifier)’ by (
      match_mp_tac ast_identifier_encoder_self >> simp [STRING_v_def,v_rel_def]) >>
  ‘!constructor.
    v_rel fr ft fe (OPTION_v (ID_v STRING_v STRING_v) constructor)
      (OPTION_v (ID_v STRING_v STRING_v) constructor)’ by (
        match_mp_tac ast_option_encoder_self >> simp []) >>
  ‘!name. v_rel fr ft fe (OPTION_v STRING_v name) (OPTION_v STRING_v name)’ by (
    match_mp_tac ast_option_encoder_self >> simp [STRING_v_def,v_rel_def]) >>
  ‘!items. v_rel fr ft fe (LIST_v STRING_v items) (LIST_v STRING_v items)’ by (
    qx_gen_tac ‘items’ >> match_mp_tac ast_encoder_list_self >>
    fs [ast_canonical_representation_stamps_def,list_type_num_def,
      STRING_v_def,v_rel_def]) >>
  ho_match_mp_tac (TypeBase.induction_of ``:ast$exp``) >> rw [] >>
  simp [Once EXP_v_def] >>
  fs [Once EXP_v_def,ast_canonical_representation_stamps_def,STRING_v_def,
    v_rel_def,OPTREL_def]
QED

Theorem ast_declaration_encoder_self[local]:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  (!arg. v_rel fr ft fe (DEC_v arg) (DEC_v arg)) /\
  (!arg. v_rel fr ft fe (DEC_v_aux_1 arg) (DEC_v_aux_1 arg))
Proof
  strip_tac >>
  mp_tac (SPEC_ALL ast_leaf_encoders_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_type_encoder_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_pattern_encoder_self) >> simp [] >> strip_tac >>
  mp_tac (SPEC_ALL ast_expression_encoder_self) >> simp [] >> strip_tac >>
  ‘stamp_rel ft fe (TypeStamp «[]» list_type_num) (TypeStamp «[]» list_type_num) /\
    stamp_rel ft fe (TypeStamp «::» list_type_num) (TypeStamp «::» list_type_num)’ by (
      fs [ast_canonical_representation_stamps_def,list_type_num_def]) >>
  ho_match_mp_tac (TypeBase.induction_of ``:ast$dec``) >> rw [] >>
  simp [Once DEC_v_def] >>
  fs [Once DEC_v_def,ast_canonical_representation_stamps_def,STRING_v_def,
    v_rel_def,OPTREL_def,ast_encoder_pair_self,ast_encoder_list_self] >>
  match_mp_tac ast_encoder_list_self >> simp [] >>
  match_mp_tac ast_encoder_pair_self >>
  simp [STRING_v_def,v_rel_def,ast_encoder_list_self,ast_encoder_pair_self]
QED

Theorem ast_dec_list_encoder_self:
  (!stamp. MEM stamp ast_canonical_representation_stamps ==>
    stamp_rel ft fe stamp stamp) ==>
  !decs. v_rel fr ft fe (LIST_v DEC_v decs) (LIST_v DEC_v decs)
Proof
  strip_tac >> mp_tac (SPEC_ALL ast_declaration_encoder_self) >> simp [] >>
  strip_tac >> match_mp_tac ast_encoder_list_self >>
  fs [ast_canonical_representation_stamps_def,list_type_num_def]
QED
