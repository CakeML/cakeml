(*
  CakeML frontend to the CP encoder: parse a CP s-expression input file
  and run full_encode to produce a PB formula.
*)
Theory cpProg
Ancestors
  basis_ffi pbc pbc_encode pbc_normalise npbc_parseProg cp cp_parse
  int_bitwise ilp ilp_to_pb cp_enc
  cp_to_ilp
  cp_to_ilp_prim
  cp_to_ilp_counting
  cp_to_ilp_linear
  cp_to_ilp_array
  cp_to_ilp_extensional
  cp_to_ilp_logical
  cp_to_ilp_lexicographical
  cp_to_ilp_channeling
  cp_to_ilp_misc
  cp_to_ilp_all
Libs
  preamble basis

val _ = translation_extends"npbc_parseProg";

(* HOL *)

val res = translate result_monadTheory.bind_def;
val res = translate integerTheory.INT_MAX;

val res = translate int_not_def;
val res = translate bits_of_num_def;
val res = translate bits_of_int_def;

Theorem bits_of_int_side:
  bits_of_int_side i ⇔ T
Proof
  EVAL_TAC >>
  intLib.ARITH_TAC
QED

val _ = update_precondition bits_of_int_side;

val res = translate COUNT_LIST_AUX_def;
val res = translate COUNT_LIST_compute;

(* pbc *)

val res = translate b2i_def;
val res = translate negate_def;
val res = translate iSUM_def;

(* pbc_encode*)

(* TODO: DEDUPLICATE, also defined in pbc_normalise *)
val res = translate pbc_encodeTheory.flip_coeffs_def;
val res = translate min_lin_term_def;
val res = translate max_lin_term_def;

(* cp *)
val res = translate bnd_lookup_def;

val _ = register_type``:'a constraint``;

(* cp_parse *)

(* generic helpers *)
val res = translate sexp_bnd_def;
val res = translate sexp_bnds_def;

val res = translate sexp_varc_def;
val res = translate sexp_varcs_def;
val res = translate sexp_varc_list_def;

val res = translate sexp_int_def;
val res = translate sexp_ints_def;
val res = translate sexp_int_list_def;

val res = translate sexp_cmpop_kw_def;
val res = translate sexp_cmpop_sym_def;
val res = translate sexp_reify_cmp_def;

val res = translate strip_reif_suffix_def;

Theorem strip_reif_suffix_side:
  strip_reif_suffix_side ms ⇔ T
Proof
  EVAL_TAC>>rw[]
QED

val _ = update_precondition strip_reif_suffix_side;

val res = translate peel_reif_def;

(* primitive *)
val res = translate sexp_prim_unop_def;
val res = translate sexp_prim_binop_def;
val res = translate sexp_unop_body_def;
val res = translate sexp_binop_body_def;
val res = translate sexp_cmpop_body_def;
val res = translate sexp_prim_dispatch_def;

(* linear *)
val res = translate sexp_iclin_pairs_def;
val res = translate sexp_iclin_term_def;
val res = translate sexp_linear_dispatch_def;

(* extensional (table) *)
val res = translate sexp_table_entry_def;
val res = translate sexp_table_row_entries_def;
val res = translate sexp_table_row_def;
val res = translate sexp_table_rows_aux_def;
val res = translate sexp_table_rows_def;
val res = translate sexp_table_body_def;
val res = translate sexp_extensional_dispatch_def;

(* array *)
val res = translate sexp_array_ind_def;
val res = translate sexp_varc_rows_aux_def;
val res = translate sexp_varc_rows_def;
val res = translate sexp_array_aggr_def;
val res = translate sexp_element_body_def;
val res = translate sexp_element_2d_body_def;
val res = translate sexp_array_aggr_body_def;
val res = translate sexp_array_dispatch_def;

(* counting *)
val res = translate sexp_all_different_body_def;
val res = translate sexp_nvalue_body_def;
val res = translate sexp_count_body_def;
val res = translate sexp_among_body_def;
val res = translate sexp_counting_dispatch_def;

(* TODO: lex, logical, channeling, misc — add once hooked into the
   top-level dispatcher in cp_parseScript.sml. *)

(* top-level *)
val res = translate strip_prefix_def;

Theorem strip_prefix_side:
  strip_prefix_side pre s ⇔ T
Proof
  EVAL_TAC>>rw[]
QED

val _ = update_precondition strip_prefix_side;

val res = translate sexp_constraint_dispatch_def;
val res = translate sexp_constraint_def;
val res = translate sexp_constraints_def;
val res = translate sexp_obj_def;
val res = translate sexp_cp_inst_def;
val res = translate parse_cp_inst_def;

(* ilp *)

(* TODO: remove? *)
Theorem int_2_pow_eq:
  (2:int) ** n = &((2:num) ** n)
Proof
  rw[]
QED

val res = translate bit_width_def;
val res = translate (min_iterm_def |> PURE_REWRITE_RULE[int_2_pow_eq]);
val res = translate min_ilin_term_def;
val res = translate bits_imply_def;
val res = translate (max_iterm_def |> PURE_REWRITE_RULE[int_2_pow_eq]);
val res = translate max_ilin_term_def;
val res = translate imply_bit_aux_def;
val res = translate imply_bit_def;
val res = translate imply_bits_def;
val res = translate bimply_bits_def;

(* ilp_to_pb *)

val res = translate encode_ivar_def;
val res = translate mul_lin_term_def;
val res = translate encode_iconstraint_one_def;

(* cp_to_ilp *)

val res = translate format_varc_def;
val res = translate format_reif_def;
val res = translate format_annot_def;
val res = translate format_num_list_def;
val res = translate format_int_list_def;
val res = translate format_flag_def;
val res = translate format_var_def;

val res = translate encode_ge_aux_def;
val res = translate encode_eq_aux_def;

val res = translate mk_constraint_ge_def;
val res = translate mk_ge_def;
val res = translate mk_le_def;
val res = translate mk_gt_def;
val res = translate mk_lt_def;

val res = translate split_iclin_term_def;
val res = translate cbimply_var_def;
val res = translate cvar_imply_def;

val res = translate mk_name_def;
val res = translate at_least_one_def;
val res = translate cat_least_one_def;

val res = translate intnum_def;

Theorem intnum_side:
  intnum_side i ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
QED

val _ = update_precondition intnum_side;

val res = translate numint_def;
val res = translate numset_to_intlist_def;
val res = translate union_def;
val res = translate domlist_def;

Theorem domlist_side:
  domlist_side x y ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
QED

val _ = update_precondition domlist_side;

val res = translate union_dom_def;

val res = translate lookup_int_def;
val res = translate insert_int_def;
val res = translate hash_varc_def;

(* Rewrite lookup_ht so the translator sees a direct case split. *)
Theorem lookup_ht_eq:
  lookup_ht k n ht ⇔
  case lookup (hash_varc k) ht of
    NONE => F
  | SOME t => (case lookup_int n t of NONE => F | SOME ls => MEMBER k ls)
Proof
  rw[lookup_ht_def,MEMBER_INTRO]>>
  every_case_tac>>rw[]
QED

val res = translate lookup_ht_eq;

val res = translate insert_ht_def;

val res = translate has_ge_def;
val res = translate has_eq_def;

val res = translate fold_cenc_def;

val res = translate add_ge_def;
val res = translate add_eq_def;

val res = translate mk_annotate_def;
val res = translate cencode_ge_def;
val res = translate cencode_eq_def;

val res = translate cencode_full_eq_def;
val res = translate cencode_reif_gen_def;

val res = translate reif_gen_def;
val res = translate gtv_def;
val res = translate ltv_def;
val res = translate nev_def;

val res = translate false_constr_def;
val res = translate cfalse_constr_def;

val res = translate flat_app_def;

val res = translate encode_bitsum_def;
val res = translate cencode_bitsum_def;

val res = translate mk_lin_constraint_ge_aux_def;
val res = translate mk_lin_constraint_ge_def;

val res = translate mk_constraint_one_ge_def;

val res = translate init_ec_def;

(* cp_to_ilp_primScript *)

val res = translate cp_to_ilp_primTheory.mk_nge_def;
val res = translate cp_to_ilp_primTheory.mk_nle_def;

val res = translate cp_to_ilp_primTheory.encode_negative_def;
val res = translate cp_to_ilp_primTheory.encode_abs_body_def;

val res = translate cp_to_ilp_primTheory.encode_plus_def;
val res = translate cp_to_ilp_primTheory.cencode_plus_def;

val res = translate cp_to_ilp_primTheory.encode_minus_def;
val res = translate cp_to_ilp_primTheory.cencode_minus_def;

val res = translate cp_to_ilp_primTheory.cencode_negative_def;
val res = translate cp_to_ilp_primTheory.cencode_abs_def;

val res = translate cp_to_ilp_primTheory.cencode_min_def;
val res = translate cp_to_ilp_primTheory.cencode_max_def;

val res = translate cp_to_ilp_primTheory.cmk_eq_def;
val res = translate cp_to_ilp_primTheory.cencode_equal_1_def;
val res = translate cp_to_ilp_primTheory.cencode_equal_2_def;
val res = translate cp_to_ilp_primTheory.cencode_equal_def;

val res = translate cp_to_ilp_primTheory.cencode_not_equal_1_def;
val res = translate cp_to_ilp_primTheory.cencode_not_equal_2_def;
val res = translate cp_to_ilp_primTheory.cencode_not_equal_3_def;
val res = translate cp_to_ilp_primTheory.cencode_not_equal_def;

val res = translate cp_to_ilp_primTheory.encode_cmp_aux_def;
val res = translate cp_to_ilp_primTheory.cencode_order_cmpops_def;

val res = translate cp_to_ilp_primTheory.cencode_prim_constr_def;

(* cp_to_ilp_counting *)

val res = translate cp_to_ilp_countingTheory.neiv_def;
val res = translate cp_to_ilp_countingTheory.cencode_all_different_def;

val res = translate cp_to_ilp_countingTheory.elm_def;
val res = translate cp_to_ilp_countingTheory.cencode_some_eq_def;

val res = translate cp_to_ilp_countingTheory.cencode_n_value_def;

val res = translate cp_to_ilp_countingTheory.eqi_def;
val res = translate cp_to_ilp_countingTheory.cencode_count_def;

val res = translate cp_to_ilp_countingTheory.cencode_among_aux_def;
val res = translate cp_to_ilp_countingTheory.cencode_full_eq_ilist_def;
val res = translate cp_to_ilp_countingTheory.cencode_among_def;

val res = translate cp_to_ilp_countingTheory.cencode_counting_constr_def;

(* cp_to_ilp_linear *)

val res = translate cp_to_ilp_linearTheory.mk_lin_ge_def;
val res = translate cp_to_ilp_linearTheory.mk_lin_le_def;
val res = translate cp_to_ilp_linearTheory.mk_lin_gt_def;
val res = translate cp_to_ilp_linearTheory.mk_lin_lt_def;

val res = translate cp_to_ilp_linearTheory.cmk_lin_eq_def;

val res = translate cp_to_ilp_linearTheory.cencode_lin_equal_1_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_equal_2_def;

val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_1_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_2_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_3_def;

val res = translate cp_to_ilp_linearTheory.encode_lin_cmp_aux_def;

val res = translate cp_to_ilp_linearTheory.cencode_lin_equal_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_not_equal_def;
val res = translate cp_to_ilp_linearTheory.cencode_lin_order_cmpops_def;

val res = translate cp_to_ilp_linearTheory.cencode_linear_constr_def;

(* cp_to_ilp_array *)

val res = translate cp_to_ilp_arrayTheory.encode_proper_index_def;
val res = translate cp_to_ilp_arrayTheory.cencode_proper_index_def;

val res = translate cp_to_ilp_arrayTheory.encode_element_aux_def;
val res = translate cp_to_ilp_arrayTheory.cencode_element_aux_def;
val res = translate cp_to_ilp_arrayTheory.cencode_element_def;

val res = translate cp_to_ilp_arrayTheory.encode_element2d_aux_def;
val res = translate cp_to_ilp_arrayTheory.cencode_element2d_aux_def;

val res = translate cp_to_ilp_arrayTheory.cencode_element2d_def;

Theorem cencode_element2d_side:
  cencode_element2d_side a b c d e f g ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  Cases_on`b`>>fs[]
QED

val _ = update_precondition cencode_element2d_side;

val res = translate cp_to_ilp_arrayTheory.arri_def;
val res = translate cp_to_ilp_arrayTheory.cencode_array_max_def;
val res = translate cp_to_ilp_arrayTheory.cencode_array_min_def;

val res = translate cp_to_ilp_arrayTheory.cencode_array_constr_def;

(* cp_to_ilp_extensional *)

val res = translate cp_to_ilp_extensionalTheory.filter_match_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_tuple_eq_def;
val res = translate cp_to_ilp_extensionalTheory.ctable_al1_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_full_eqs_def;
val res = translate cp_to_ilp_extensionalTheory.creify_tuple_eq_def;
val res = translate cp_to_ilp_extensionalTheory.creify_tuple_eqs_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_table_def;
val res = translate cp_to_ilp_extensionalTheory.cencode_extensional_constr_def;

(* cp_to_ilp_logical *)

val res = translate cp_to_ilp_logicalTheory.encode_and_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_and_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_and_def;

val res = translate cp_to_ilp_logicalTheory.encode_or_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_or_aux_def;
val res = translate cp_to_ilp_logicalTheory.cencode_or_def;

val res = translate cp_to_ilp_logicalTheory.cencode_logical_constr_def;

(* cp_to_ilp_lexicographical *)

val res = translate cp_to_ilp_lexicographicalTheory.cencode_lexicographical_constr_def;

(* cp_to_ilp_channeling *)

val res = translate cp_to_ilp_channelingTheory.cencode_channeling_constr_def;

(* cp_to_ilp_misc *)

val res = translate cp_to_ilp_miscTheory.cencode_misc_constr_def;

(* cp_to_ilp_all *)

val res = translate cencode_constraint_def;
val res = translate cencode_constraints_def;

(* cp_encScript *)

val res = translate cencode_bound_var_def;
val res = translate cencode_bound_all_def;

val res = translate cp_encTheory.encode_def;
val res = translate encode_nivar_def;
val res = translate encode_obj_def;
val res = translate format_string_def;
val res = translate full_encode_def;
val res = translate conv_concl_def;

(* Actual CakeML setup *)

Definition get_cp_inst_def:
  get_cp_inst fs f =
  if inFS_fname fs f then
    case parse_cp_inst (concat (all_lines_file fs f)) of
      INL _ => NONE
    | INR inst => SOME inst
  else NONE
End

(* Read an input file and parse into a cp_inst. *)
Quote add_cakeml:
  fun parse_cp_file f =
    let
      val fd = TextIO.openIn f
      val l = TextIO.inputAll fd
      val u = TextIO.closeIn fd
    in
      parse_cp_inst l
    end
    handle TextIO.BadFileName => Inl (notfound_string f)
End

Quote add_cakeml:
  fun parse_and_enc f =
  case parse_cp_file f of
    Inl err => Inl err
  | Inr inst => Inr (inst, full_encode inst)
End

Theorem parse_and_enc_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_enc"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE CP_INST_TYPE (PAIR_TYPE
            (OPTION_TYPE (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
            INT))
            (LIST_TYPE
              (PAIR_TYPE
              (OPTION_TYPE STRING_TYPE)
              (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT))))
            )) res v ∧
       case res of
        INL err =>
          get_cp_inst fs f = NONE
      | INR (inst,objf) =>
          get_cp_inst fs f = SOME inst ∧
          full_encode inst = objf)
Proof
  cheat
QED

Definition cp_no_concl_str_def:
  cp_no_concl_str = strlit "s NO CONCLUSION\n"
End

Definition cp_sat_str_def:
  cp_sat_str = strlit "s VERIFIED SATISFIABLE\n"
End

Definition cp_unsat_str_def:
  cp_unsat_str = strlit "s VERIFIED UNSATISFIABLE\n"
End

Definition cp_bound_str_def:
  cp_bound_str lbi ubi =
  concat [
    strlit "s VERIFIED BOUNDS ";
    (case lbi of NONE => strlit "-INF" | SOME l => mlint$toString (l:int));
    strlit " <= OBJ <= ";
    (case ubi of NONE => strlit "+INF" | SOME u => mlint$toString (u:int));
    strlit "\n"]
End

Definition print_cp_concl_str_def:
  (print_cp_concl_str NoConcl = cp_no_concl_str) ∧
  (print_cp_concl_str DSat = cp_sat_str) ∧
  (print_cp_concl_str DUnsat = cp_unsat_str) ∧
  (print_cp_concl_str (OBounds lbi ubi) = cp_bound_str lbi ubi) ∧
  (print_cp_concl_str (EEnum n complete) = cp_no_concl_str)
End

val res = translate cp_sat_str_def;
val res = translate cp_unsat_str_def;
val res = translate cp_bound_str_def;
val res = translate cp_no_concl_str_def;
val res = translate print_cp_concl_str_def;

Definition map_concl_to_string_def:
  (map_concl_to_string inst (INL s) = (INL s)) ∧
  (map_concl_to_string inst (INR (out,bnd,c)) =
    INR (print_cp_concl_str (conv_concl inst c)))
End

val res = translate map_concl_to_string_def;

Definition mk_prob_def:
  mk_prob objf = (NONE,objf):mlstring list option #
    ((int # mlstring pbc$lit) list # int) option #
    (mlstring option # (pbop # (int # mlstring pbc$lit) list # int)) list
End

val res = translate mk_prob_def;

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f out ⇔
  (out ≠ strlit"" ⇒
  ∃inst c.
    get_cp_inst fs f = SOME inst ∧
    out = print_cp_concl_str c ∧
    cp_inst_sem_concl inst c)
End

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (inst,objf) =>
    let
      val prob = mk_prob objf
      val prob = strip_annot_prob prob
      val probt = default_prob in
      (case
        map_concl_to_string inst
          (check_unsat_top_norm False prob probt f2) of
        Inl err => TextIO.output TextIO.stdErr err
      | Inr s => TextIO.print s)
    end
End

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  cheat
QED

(* Emit just the PB encoding on stdout. *)
Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_cp_inst fs f1 of
    NONE => out = strlit ""
  | SOME inst =>
    out = concat (print_annot_prob (mk_prob (full_encode inst)))
End

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (inst,objf) =>
    TextIO.print_list (print_annot_prob (mk_prob objf))
End

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_1"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_1_sem fs f1 out))
Proof
  cheat
QED

Definition usage_string_def:
  usage_string = strlit
    "Usage: cake_pb_cp <CP file> <optional: PB proof file>\n"
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
  else out = strlit ""
End

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(main_sem fs cl out))
Proof
  rw[main_sem_def]>>
  xcf"main"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    assume_tac (theorem "usage_string_v_thm")>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `mk_usage_string usage_string` >>
    simp [] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  (*
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>> *)
  xmatch>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `mk_usage_string usage_string` >>
  simp [] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  metis_tac[STDIO_refl]
QED

Theorem main_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 main_v cl fs NONE
     (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        main_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`add_stdout (add_stderr fs x') x`
  \\ xsimpl
  \\ qexists_tac`x`
  \\ qexists_tac`x'`
  \\ xsimpl
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

local

val name = "main"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH main_whole_prog_spec2)
Definition main_prog_def:
  main_prog = ^prog_tm
End

in

Theorem main_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM main_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end
