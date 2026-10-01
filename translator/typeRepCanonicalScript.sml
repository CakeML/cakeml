(*
  Typed-value interfaces for translator representation completeness.
  These facts are independent of any particular registered datatype family.
*)
Theory typeRepCanonical
Ancestors
  typeSound typeSysProps typeSoundInvariants typeSystem semanticPrimitives
  ml_translator
Libs
  preamble

Definition type_rep_complete_def:
  type_rep_complete tvs ctMap tenvS ty rep <=>
    !value. type_v tvs ctMap tenvS value ty ==> ?x. rep x value
End

Theorem type_rep_complete_elim:
  type_rep_complete tvs ctMap tenvS ty rep /\
  type_v tvs ctMap tenvS value ty ==> ?x. rep x value
Proof
  rw [type_rep_complete_def] >> res_tac
QED

Theorem type_rep_complete_bool:
  ctMap_ok ctMap /\ ctMap_has_bools ctMap ==>
  type_rep_complete tvs ctMap tenvS Tbool BOOL
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >> rpt strip_tac >>
  drule_all (CONJUNCT1 ctor_canonical_values_thm) >>
  simp [BOOL_def]
QED

(* The bound exposes the smaller-value hypothesis used through nested
   containers in a recursive registered datatype family. *)
Definition type_rep_complete_below_def:
  type_rep_complete_below bound tvs ctMap tenvS ty rep <=>
    !value. v_size value < bound /\ type_v tvs ctMap tenvS value ty ==>
      ?x. rep x value
End

Theorem type_rep_complete_below_elim:
  type_rep_complete_below bound tvs ctMap tenvS ty rep /\
  v_size value < bound /\ type_v tvs ctMap tenvS value ty ==>
  ?x. rep x value
Proof
  rw [type_rep_complete_below_def] >> res_tac
QED

Theorem type_rep_complete_implies_below:
  type_rep_complete tvs ctMap tenvS ty rep ==>
  type_rep_complete_below bound tvs ctMap tenvS ty rep
Proof
  rw [type_rep_complete_def, type_rep_complete_below_def] >> res_tac
QED

Theorem type_v_datatype_shape:
  ~MEM ti prim_type_nums /\ type_v tvs ctMap tenvS value (Tapp args ti) ==>
  ?stamp fields params field_types.
    value = Conv (SOME stamp) fields /\
    FLOOKUP ctMap stamp = SOME (params,field_types,ti) /\
    EVERY (check_freevars tvs []) args /\ LENGTH params = LENGTH args /\
    LIST_REL (type_v tvs ctMap tenvS) fields
      (MAP (type_subst (FEMPTY |++ REVERSE (ZIP (params,args)))) field_types)
Proof
  rw [Once type_v_cases, prim_type_nums_def,
    Tint_def, Tchar_def, Tstring_def, Tword8_def, Tword64_def, Tdouble_def,
    Ttup_def, Tfn_def, Tref_def, Tword8array_def, Tarray_def, Tvector_def] >>
  drule_all type_funs_Tfn >> simp [Tfn_def]
QED

Theorem type_v_datatype_signature:
  ctMap_ok ctMap /\ ~MEM ti prim_type_nums /\
  type_v tvs ctMap tenvS value (Tapp args ti) ==>
  ?cn stamp fields params field_types.
    value = Conv (SOME (TypeStamp cn stamp)) fields /\
    (cn,stamp,params,field_types) IN datatype_signature ctMap ti /\
    EVERY (check_freevars tvs []) args /\ LENGTH params = LENGTH args /\
    LIST_REL (type_v tvs ctMap tenvS) fields
      (MAP (type_subst (FEMPTY |++ REVERSE (ZIP (params,args)))) field_types)
Proof
  strip_tac >> drule_all type_v_datatype_shape >>
  disch_then (qx_choose_then `runtime_stamp` mp_tac) >>
  disch_then (qx_choosel_then [`ctor_fields`,`ctor_params`,`ctor_types`]
    strip_assume_tac) >>
  namedCases_on `runtime_stamp` ["name index","exception_index"] >>
  simp [datatype_signature_member] >>
  qpat_x_assum `ctMap_ok _`
    (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ctMap_ok_def]) >>
  disch_then (qspecl_then [`exception_index`,`ctor_params`,`ctor_types`,`ti`]
    mp_tac) >>
  fs [prim_type_nums_def]
QED

Theorem type_rep_complete_primitives:
  ctMap_ok ctMap ==>
  type_rep_complete tvs ctMap tenvS Tint INT /\
  type_rep_complete tvs ctMap tenvS Tchar CHAR /\
  type_rep_complete tvs ctMap tenvS Tstring STRING_TYPE /\
  type_rep_complete tvs ctMap tenvS Tword8 (WORD : word8 -> v -> bool) /\
  type_rep_complete tvs ctMap tenvS Tword64 (WORD : word64 -> v -> bool)
Proof
  strip_tac >> rpt conj_tac >> rewrite_tac [type_rep_complete_def] >>
  rpt strip_tac >>
  imp_res_tac (LIST_CONJ (List.take (CONJUNCTS prim_canonical_values_thm,5))) >>
  simp [INT_def, CHAR_def, STRING_TYPE_def, WORD_def, wordsTheory.w2w_id]
QED

Theorem type_v_tuple_shape:
  ctMap_ok ctMap /\ type_v tvs ctMap tenvS value (Ttup field_types) ==>
  ?fields. value = Conv NONE fields /\
    LIST_REL (type_v tvs ctMap tenvS) fields field_types
Proof
  strip_tac >> drule_all (List.nth (CONJUNCTS prim_canonical_values_thm,6)) >>
  disch_then (qx_choose_then `ctor_fields` strip_assume_tac) >>
  gvs [Once type_v_cases, Ttup_def]
QED

Theorem v_size_less_fields_size:
  !fields field. MEM field fields ==> v_size field < v1_size fields
Proof
  Induct >> rw [v_size_def] >> res_tac >> decide_tac
QED

Theorem v_size_less_constructor:
  !field fields stamp.
    MEM field fields ==> v_size field < v_size (Conv stamp fields)
Proof
  rpt strip_tac >> drule v_size_less_fields_size >> simp [v_size_def]
QED

Theorem type_rep_complete_below_pair:
  ctMap_ok ctMap /\
  type_rep_complete_below bound tvs ctMap tenvS left_ty left_rep /\
  type_rep_complete_below bound tvs ctMap tenvS right_ty right_rep ==>
  type_rep_complete_below bound tvs ctMap tenvS
    (Ttup [left_ty;right_ty]) (PAIR_TYPE left_rep right_rep)
Proof
  strip_tac >> rewrite_tac [type_rep_complete_below_def] >>
  qx_gen_tac `value` >> strip_tac >> drule_all type_v_tuple_shape >>
  disch_then (qx_choose_then `ctor_fields` strip_assume_tac) >>
  gvs [LIST_REL_CONS2] >>
  qmatch_goalsub_rename_tac `Conv NONE [left_value;right_value]` >>
  `v_size left_value < bound /\ v_size right_value < bound` by fs [] >>
  fs [type_rep_complete_below_def] >> res_tac >>
  simp [EXISTS_PROD, PAIR_TYPE_def] >> metis_tac []
QED

Theorem v_to_list_fields_smaller:
  !value fields. v_to_list value = SOME fields ==>
    EVERY (\field. v_size field < v_size value) fields
Proof
  recInduct v_to_list_ind >> rpt strip_tac >>
  fs [Once v_to_list_def, AllCaseEqs ()] >>
  res_tac >> gvs [EVERY_MEM] >> rw [] >> res_tac >> fs []
QED

Theorem v_to_list_rep_complete:
  !value fields. v_to_list value = SOME fields /\
    EVERY (\field. ?x. rep x field) fields ==>
    ?xs. LIST_TYPE rep xs value
Proof
  recInduct v_to_list_ind >> rpt strip_tac >>
  fs [Once v_to_list_def, AllCaseEqs ()]
  >- (qexists_tac `[]` >> simp [LIST_TYPE_def, list_type_num_def]) >>
  gvs [] >> res_tac >>
  simp [list_type_num_def] >> metis_tac [LIST_TYPE_def]
QED

Theorem type_rep_complete_below_list:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  type_rep_complete_below bound tvs ctMap tenvS element_ty element_rep ==>
  type_rep_complete_below bound tvs ctMap tenvS
    (Tlist element_ty) (LIST_TYPE element_rep)
Proof
  strip_tac >> rewrite_tac [type_rep_complete_below_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all (CONJUNCT1 (CONJUNCT2 ctor_canonical_values_thm)) >>
  disch_then (qx_choose_then `elements` strip_assume_tac) >>
  drule v_to_list_fields_smaller >> disch_tac >>
  irule v_to_list_rep_complete >> qexists_tac `elements` >> simp [] >>
  fs [EVERY_MEM, type_rep_complete_below_def] >>
  qx_gen_tac `field_value` >> strip_tac >> res_tac >>
  `v_size field_value < bound` by fs [] >> res_tac >> simp []
QED

(* Resolve a registered signature at the static type arguments. Retain only
   entries with the right parameter arity, as required by constructor typing. *)
Definition instantiated_datatype_signature_def:
  instantiated_datatype_signature args ctMap ti =
    {entry | ?cn index params fields.
      entry = (TypeStamp cn index,
        MAP (type_subst (FEMPTY |++ REVERSE (ZIP (params,args)))) fields) /\
      LENGTH params = LENGTH args /\
      (cn,index,params,fields) IN datatype_signature ctMap ti}
End

Theorem instantiated_datatype_signature_member:
  !stamp field_types.
    (stamp,field_types) IN instantiated_datatype_signature args ctMap ti <=>
    ?cn index params fields.
      stamp = TypeStamp cn index /\
      field_types =
        MAP (type_subst (FEMPTY |++ REVERSE (ZIP (params,args)))) fields /\
      LENGTH params = LENGTH args /\
      (cn,index,params,fields) IN datatype_signature ctMap ti
Proof
  simp [instantiated_datatype_signature_def, CONJ_ASSOC]
QED

Theorem instantiated_datatype_signature_eq:
  datatype_signature ctMap ti = datatype_signature ctMap' ti ==>
  instantiated_datatype_signature args ctMap ti =
    instantiated_datatype_signature args ctMap' ti
Proof
  rw [instantiated_datatype_signature_def]
QED

Theorem type_v_instantiated_datatype_signature:
  ctMap_ok ctMap /\ ~MEM ti prim_type_nums /\
  type_v tvs ctMap tenvS value (Tapp args ti) ==>
  ?stamp fields field_types.
    value = Conv (SOME stamp) fields /\
    (stamp,field_types) IN instantiated_datatype_signature args ctMap ti /\
    LIST_REL (type_v tvs ctMap tenvS) fields field_types
Proof
  strip_tac >> drule_all type_v_datatype_signature >> strip_tac >>
  simp [instantiated_datatype_signature_member] >> metis_tac []
QED

(* Unbounded completeness from the bounded container interfaces. *)
Theorem type_rep_complete_from_below:
  (!bound. type_rep_complete_below bound tvs ctMap tenvS ty rep) ==>
  type_rep_complete tvs ctMap tenvS ty rep
Proof
  strip_tac >> rewrite_tac [type_rep_complete_def] >>
  qx_gen_tac `value` >> strip_tac >>
  qpat_x_assum `!bound. _`
    (qspec_then `SUC (v_size value)` mp_tac) >>
  rewrite_tac [type_rep_complete_below_def] >>
  disch_then (qspec_then `value` mp_tac) >> simp []
QED

Theorem type_rep_complete_list:
  ctMap_ok ctMap /\ ctMap_has_lists ctMap /\
  type_rep_complete tvs ctMap tenvS element_ty element_rep ==>
  type_rep_complete tvs ctMap tenvS (Tlist element_ty) (LIST_TYPE element_rep)
Proof
  strip_tac >> irule type_rep_complete_from_below >> qx_gen_tac `bound` >>
  irule type_rep_complete_below_list >> simp [] >>
  irule type_rep_complete_implies_below >> simp []
QED

(* Exported interfaces must not rest on assumptions or admissions. *)
val _ = List.app (fn theorem => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  in
    if null (hyp theorem) andalso null axioms andalso
      List.all (fn name => name = "DISK_THM") oracles then ()
    else failwith "Representation completeness has assumptions or admissions"
  end)
  [type_rep_complete_elim,
   type_rep_complete_bool,
   type_rep_complete_below_elim,
   type_rep_complete_implies_below,
   type_v_datatype_shape,
   type_v_datatype_signature,
   type_rep_complete_primitives,
   type_v_tuple_shape,
   v_size_less_fields_size,
   v_size_less_constructor,
   type_rep_complete_below_pair,
   v_to_list_fields_smaller,
   v_to_list_rep_complete,
   type_rep_complete_below_list,
   instantiated_datatype_signature_member,
   instantiated_datatype_signature_eq,
   type_v_instantiated_datatype_signature,
   type_rep_complete_from_below,
   type_rep_complete_list];
