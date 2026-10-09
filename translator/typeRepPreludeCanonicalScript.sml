(*
  Canonical forms for registered prelude containers. Static identities are
  parameters; runtime constructors come from the representation definitions.
*)
Theory typeRepPreludeCanonical
Ancestors
  typeRepCanonical std_prelude typeSoundInvariants typeSystem semanticPrimitives
Libs
  preamble semanticPrimitivesSyntax[qualified]

val option_some_stamp = find_term semanticPrimitivesSyntax.is_TypeStamp
  (concl (CONJUNCT1 OPTION_TYPE_def));
val option_none_stamp = find_term semanticPrimitivesSyntax.is_TypeStamp
  (concl (CONJUNCT2 OPTION_TYPE_def));
val sum_right_stamp = find_term semanticPrimitivesSyntax.is_TypeStamp
  (concl (CONJUNCT1 SUM_TYPE_def));
val sum_left_stamp = find_term semanticPrimitivesSyntax.is_TypeStamp
  (concl (CONJUNCT2 SUM_TYPE_def));

Definition option_rep_signature_def:
  option_rep_signature element_ty =
    {(^option_some_stamp,[element_ty]); (^option_none_stamp,[])}
End

Definition sum_rep_signature_def:
  sum_rep_signature left_ty right_ty =
    {(^sum_left_stamp,[left_ty]); (^sum_right_stamp,[right_ty])}
End

Theorem option_rep_signature_cases:
  !stamp field_types.
    (stamp,field_types) IN option_rep_signature element_ty <=>
    (stamp = ^option_some_stamp /\ field_types = [element_ty]) \/
    (stamp = ^option_none_stamp /\ field_types = [])
Proof
  simp [option_rep_signature_def]
QED

Theorem sum_rep_signature_cases:
  !stamp field_types.
    (stamp,field_types) IN sum_rep_signature left_ty right_ty <=>
    (stamp = ^sum_left_stamp /\ field_types = [left_ty]) \/
    (stamp = ^sum_right_stamp /\ field_types = [right_ty])
Proof
  simp [sum_rep_signature_def]
QED

Theorem type_rep_complete_below_option:
  ctMap_ok ctMap /\ ~MEM option_ti prim_type_nums /\
  instantiated_datatype_signature [element_ty] ctMap option_ti =
    option_rep_signature element_ty /\
  type_rep_complete_below bound tvs ctMap tenvS element_ty element_rep ==>
  type_rep_complete_below bound tvs ctMap tenvS
    (Tapp [element_ty] option_ti) (OPTION_TYPE element_rep)
Proof
  strip_tac >> rewrite_tac [type_rep_complete_below_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_instantiated_datatype_signature >>
  disch_then (qx_choosel_then [`ctor_stamp`,`ctor_fields`,`ctor_types`]
    strip_assume_tac) >>
  gvs [option_rep_signature_cases, LIST_REL_CONS2]
  >~ [`OPTION_TYPE _ _ (Conv _ [])`]
  >- (qexists_tac `NONE` >> simp [OPTION_TYPE_def]) >>
  qmatch_goalsub_rename_tac `Conv _ [field_value]` >>
  `v_size field_value < bound` by fs [] >>
  fs [type_rep_complete_below_def] >> res_tac >>
  metis_tac [OPTION_TYPE_def]
QED

Theorem type_rep_complete_below_sum:
  ctMap_ok ctMap /\ ~MEM sum_ti prim_type_nums /\
  instantiated_datatype_signature [left_ty;right_ty] ctMap sum_ti =
    sum_rep_signature left_ty right_ty /\
  type_rep_complete_below bound tvs ctMap tenvS left_ty left_rep /\
  type_rep_complete_below bound tvs ctMap tenvS right_ty right_rep ==>
  type_rep_complete_below bound tvs ctMap tenvS
    (Tapp [left_ty;right_ty] sum_ti) (SUM_TYPE left_rep right_rep)
Proof
  strip_tac >> rewrite_tac [type_rep_complete_below_def] >>
  qx_gen_tac `value` >> strip_tac >>
  drule_all type_v_instantiated_datatype_signature >>
  disch_then (qx_choosel_then [`ctor_stamp`,`ctor_fields`,`ctor_types`]
    strip_assume_tac) >>
  gvs [sum_rep_signature_cases, LIST_REL_CONS2] >>
  qmatch_goalsub_rename_tac `Conv _ [field_value]` >>
  `v_size field_value < bound` by fs [] >>
  fs [type_rep_complete_below_def] >> res_tac >>
  metis_tac [SUM_TYPE_def]
QED

Theorem type_rep_complete_sum:
  ctMap_ok ctMap /\ ~MEM sum_ti prim_type_nums /\
  instantiated_datatype_signature [left_ty;right_ty] ctMap sum_ti =
    sum_rep_signature left_ty right_ty /\
  type_rep_complete tvs ctMap tenvS left_ty left_rep /\
  type_rep_complete tvs ctMap tenvS right_ty right_rep ==>
  type_rep_complete tvs ctMap tenvS
    (Tapp [left_ty;right_ty] sum_ti) (SUM_TYPE left_rep right_rep)
Proof
  strip_tac >> irule type_rep_complete_from_below >> qx_gen_tac `bound` >>
  irule type_rep_complete_below_sum >> simp [] >>
  conj_tac >> irule type_rep_complete_implies_below >> simp []
QED
