(*
  Translate of all to-CNF encoding functions
*)
Theory sat_encodersProg
Ancestors
  misc set_sep list lispProg boolExpToCnf quantifierExp
  orderEncodingBool numBoolExp numBoolExtended numBoolRange
  unorderedSets toCnfHelper cnf
  (* for parsing: *) parsing source_values
Libs
  preamble basis

val _ = translation_extends "lispProg";

val _ = show_assums := true;

(* boolExp *)
val res = translate bind_def;
val res = translate get_fresh_name_constFree_def;
val res = translate boolExp_to_constFree_def;
val res = translate constFree_to_cnf_inner_def;
val res = translate negate_literal_def;
val res = translate replace_not_def;
val res = translate replace_or_def;
val res = translate replace_and_def;
val res = translate replace_impl_def;
val res = translate replace_iff_def;
val res = translate rhs_to_cnf_def;
val res = translate append_aux_def;
val res = translate append_def;
val res = translate map_to_cnf_def;
val res = translate constFree_to_cnf_def;
val res = translate boolExp_to_cnf_def;

(* quantifierExp *)
val res = translate bool_to_quant_def;
val res = translate quant_size';
val res = translate pseudoBool_size';
val res = translate replace_name_quant_def;
val res = translate quant_to_boolExp_def;
val res = translate none_of_list_to_quant_def;
val res = translate most_one_to_quant_def;
val res = translate pseudoBool_to_quant_def;

(* orderEncodingBool *)
val res = translate orderBool_size';
val res = translate encode_orderAxiom_def;
val res = translate orderBool_to_pseudoBool_def;

(* numBoolExp *)
val res = translate (REWRITE_RULE [MEMBER_INTRO] add_numVar_to_list_def);
val res = translate (REWRITE_RULE [MEMBER_INTRO] nub_def);
val res = translate create_numVarList_inner_def;
val res = translate create_numVarList_def;
val res = translate get_fresh_boolVar_def;
val res = translate create_numVarMap_inner_def;
val res = translate create_numVarMap_def;

val res = translate vMap_to_orderBool_def;
val res = translate encode_combinations_def;
val res = translate encode_add_def;
val res = translate encode_leq_def;
val res = translate EL;

val el_side_def = fetch "-" "el_side_def";

Theorem el_side:
  ∀ n l.
    n < LENGTH l ⇒
    el_side n l
Proof
  gs[Once el_side_def]
  >> Induct
  >- (
    rw[]>>
    pure_rewrite_tac[GSYM LENGTH_NIL]>>
    intLib.ARITH_TAC)
  >> rw[]
  >> rw[Once el_side_def]
QED

val res = translate encode_eqConst_def; (* side *)

val encode_eqconst_side_def = fetch "-" "encode_eqconst_side_def";

Theorem encode_eqconst_side:
  ∀ n bvs.
    encode_eqconst_side n bvs
Proof
  gs[Once encode_eqconst_side_def]
  >> rw[]
  >- gs[]
  >- (irule el_side
      >> gs[])
  >> irule el_side
  >> gs[]
QED

val _ = update_precondition encode_eqconst_side;

val res = translate encode_leqConst_def; (* side *)

val encode_leqconst_side_def = fetch "-" "encode_leqconst_side_def";

Theorem encode_leqconst_side:
  ∀ n bvs.
    encode_leqconst_side n bvs
Proof
  rw[Once encode_leqconst_side_def]
  >> irule el_side >> gs[]
QED

val _ = update_precondition encode_leqconst_side;

val res = translate numBoolExp_to_orderBool_def;
val res = translate encode_axioms_def;
val res = translate numBool_to_orderBool_def;
val res = translate invert_numVarMap_def;
val res = translate encode_assignment_def;
val res = translate minimal_encode_assignment_def;
val res = translate find_value_def;
val res = translate assignment_to_numVarAssignment_def;
val res = translate minimal_assignment_to_numVarAssignment_def;

(* numBoolExtended *)
val res = translate create_numVarList_numBoolExtended_inner_def;
val res = translate create_numVarList_numBoolExtended_def;
val res = translate numBoolExtended_to_numBoolExp_def;
val res = translate encode_assignment_numBoolExtended_def;
val res = translate assignment_to_numVarAssignment_numBoolExtended_def;

(* numBoolRange *)
val res = translate equation_to_numBoolExtended_def;
val res = translate ranges_to_numBoolExtended_def;
val res = translate numBoolRange_to_numBoolExtended_def;
val res = translate get_highest_max_def;
val res = translate rangeList_to_numVarList_def;
val res = translate encode_assignment_numBoolRange_def;
val res = translate assignment_to_numVarAssignment_numBoolRange_def;

(* unorderedSet *)
val res = translate get_varList_inner_def;
val res = translate get_varList_def;
val res = translate indexedListsTheory.findi_def;
val res = translate encode_constant_def;
val res = translate equation_to_numBoolRange_def;
val res = translate get_setName_def;
val res = translate elementVarAssignment_to_numVarAssignment_inner_def;
val res = translate elementVarAssignment_to_numVarAssignment_def;
val res = translate get_max_def;
val res = translate equation_to_rangeList_inner_def;
val res = translate equation_to_rangeList_def;
val res = translate eval_literal_def;
val res = translate eval_rhs_def;
val res = translate make_assignments_def;
val res = translate constFree_to_assignment_def;
val res = translate boolExp_to_assignment_def;
val res = translate pseudoBool_to_assignment_def;
val res = translate orderBool_to_assignment_def;
val res = translate numBoolExp_to_assignment_def;
val res = translate numBoolExtended_to_assignment_def;
val res = translate numBoolRange_to_assignment_def;
val res = translate encode_assignment_unorderedSet_def;
val res = translate oEL_def;
val res = translate numVarAssignment_to_elementVarAssignment_inner_def;
val res = translate numVarAssignment_to_elementVarAssignment_def;
val res = translate assignment_to_elementVarAssignment_def;

val res = translate constFree_to_cnf_inner_def;
val res = translate constFree_to_cnf_def;
val res = translate boolExp_to_cnf_def;
val res = translate pseudoBool_to_cnf_def;
val res = translate orderBool_to_cnf_def;
val res = translate numBool_to_cnf_def;
val res = translate numBoolExtended_to_cnf_def;
val res = translate numBoolRange_to_cnf_def;
val res = translate equation_to_cnf_def;
val res = translate rangeList_ok_def;
val res = translate (exp_rangeList_ok_def |> PURE_REWRITE_RULE [MEMBER_INTRO]);
val res = translate (numVarAssignment_range_ok_def |> PURE_REWRITE_RULE [MEMBER_INTRO]);
val res = translate get_first_non_boolVar_num_def
val res = translate get_boolVar_list_def
