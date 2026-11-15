(*
  Add shared pbp parsing, normalization and other common stuff to npbc_arrayProg
*)
Theory npbc_parseProg
Ancestors
  npbc_check pb_parse name_table array_ofProof npbc_arrayProg pbc_normalise
  mlint input_lex input_lexProg
Libs
  preamble basis

val _ = translation_extends"npbc_arrayProg";

val _ = computeLib.upd_compset (fn c => computeLib.set_skip c “COND” (SOME 1));

val r = translate numbers_ok_def;
val r = translate rup_hint_ok_def;
val r = translate tok_nums_def;

Theorem tok_nums_side[local]:
  (∀xs. numbers_ok xs ⇒ tok_nums_side xs) ∧
  (∀xs. rup_hint_ok xs ⇒ tok_nums_side xs)
Proof
  conj_tac>>
  Induct>>
  rw[Once (fetch "-" "tok_nums_side_def")]>>
  gvs[numbers_ok_def,rup_hint_ok_def,AllCaseEqs(),integerTheory.int_ge]
QED

val r = translate strip_numbers_ok;

Theorem strip_numbers_side[local]:
  strip_numbers_side xs ⇔ T
Proof
  rw[fetch "-" "strip_numbers_side_def"]>>
  irule (CONJUNCT1 tok_nums_side)>>simp[]
QED

val _ = strip_numbers_side |> update_precondition;

val r = translate pbcTheory.map_lit_def;

Theorem goodChars_small:
  goodChars n str =
  if smallnum_eq_str n 0 str then T
  else
    let m = smallnum_sub_str n 1 str in
    goodChar (strsub_unsafe str m) ∧ goodChars m str
Proof
  Cases_on`n`>>
  simp[goodChars_def,smallnum_eq_str_def,smallnum_sub_str_def]
QED

(* Character codes are below 256: compared as small integers *)
val r = translate_no_ind (goodChars_small
  |> REWRITE_RULE [goodChar_eq]
  |> REWRITE_RULE [GSYM smallnum_lt_def,GSYM smallnum_le_def,GSYM smallnum_eq_def]);

Theorem goodchars_ind_small[local]:
  goodchars_ind
Proof
  once_rewrite_tac [fetch "-" "goodchars_ind_def"]>>
  rpt strip_tac>>
  rename1`P n s`>>
  completeInduct_on`n`>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rw[]>>
  first_x_assum irule>>
  gvs[smallnum_eq_str_def,smallnum_sub_str_def]
QED

val _ = goodchars_ind_small |> update_precondition;

Theorem goodchars_side:
  ∀n s. n ≤ strlen s ⇒ goodchars_side n s
Proof
  Induct>>
  rw[Once (fetch "-" "goodchars_side_def")]>>
  gvs[semanticPrimitivesTheory.index_in_bounds_def,smallnum_eq_str_def,
      smallnum_sub_str_def]>>
  qspec_then`strsub_unsafe s n` assume_tac ORD_BOUND>>
  decide_tac
QED

val r = translate goodString_def;

Theorem goodstring_side[local]:
  ∀x. goodstring_side x = T
Proof
  rw[fetch "-" "goodstring_side_def"]>>
  irule goodchars_side>>simp[]
QED

val _ = goodstring_side |> update_precondition;

(* The parsers' length tests on a token s, as small-integer arithmetic with s
  as the witness *)
Theorem strlen_small:
  (strlen s ≥ 1 ⇔ smallnum_lt_str 0 (strlen s) s) ∧
  (strlen s > 0 ⇔ smallnum_lt_str 0 (strlen s) s) ∧
  (strlen s < 1 ⇔ ¬smallnum_lt_str 0 (strlen s) s) ∧
  (strlen s ≥ 2 ⇔ smallnum_lt_str 0 (strlen s) s ∧ smallnum_lt_str 1 (strlen s) s) ∧
  (strlen s = 1 ⇔ smallnum_lt_str 0 (strlen s) s ∧ ¬smallnum_lt_str 1 (strlen s) s) ∧
  (strlen s > 1 ⇔ smallnum_lt_str 1 (strlen s) s) ∧
  strlen s - 1 = smallnum_sub_str (strlen s) 1 s
Proof
  rw[smallnum_lt_str_def,smallnum_sub_str_def]
QED

val r = translate (parse_lit_def |> REWRITE_RULE [strlen_small]);

Theorem parse_lit_side[local]:
  parse_lit_side s ⇔ T
Proof
  rw[fetch "-" "parse_lit_side_def",smallnum_lt_str_def,smallnum_sub_str_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
QED

val _ = parse_lit_side |> update_precondition;

val r = translate binopc_def;

val r = translate_no_ind (parse_cutting_aux_def |> REWRITE_RULE [strlen_small]);

Theorem parse_cutting_aux_ind_small[local]:
  parse_cutting_aux_ind
Proof
  once_rewrite_tac [fetch "-" "parse_cutting_aux_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac pb_parseTheory.parse_cutting_aux_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[strlen_small]
QED

val _ = parse_cutting_aux_ind_small |> update_precondition;

Theorem parse_cutting_aux_side[local]:
  ∀y z. parse_cutting_aux_side y z ⇔ T
Proof
  Induct>>rw[Once (fetch "-" "parse_cutting_aux_side_def")]>>
  gvs[smallnum_lt_str_def,semanticPrimitivesTheory.index_in_bounds_def,
      integerTheory.int_ge]>>
  qpat_x_assum `∀z. _` kall_tac>>
  intLib.ARITH_TAC
QED

val _ = parse_cutting_aux_side |> update_precondition;

val r = translate parse_cutting_def;

val r = translate parse_var_def;

val r = translate parse_subst_aux_def;

val r = translate parse_subst_def;

val r = translate pbcTheory.lit_var_def;
val r = translate compact_lhs_def;

Theorem lit_var_case[local]:
  lit_var l = case l of Pos v => v | Neg v => v
Proof
  Cases_on`l`>>simp[]
QED

val r = translate (term_le_def |> REWRITE_RULE [lit_var_case]);
val r = translate mk_coeff_def;
val r = translate normalise_lhs_def;

val r = translate flip_coeffs_def;
val r = translate pbcTheory.negate_op_def;
val r = translate ge_of_def;
val r = translate pbcTheory.negate_def;
val r = translate rel_ges_def;
val r = translate (merge_const_def |> REWRITE_RULE [lit_var_case]);

Theorem merge_const_ind_thm[local]:
  merge_const_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "merge_const_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac merge_const_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[GSYM lit_var_case]
QED

val _ = merge_const_ind_thm |> update_precondition;

val r = translate (merge_terms_def |> REWRITE_RULE [lit_var_case]);

Theorem merge_terms_ind_thm[local]:
  merge_terms_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "merge_terms_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac merge_terms_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[GSYM lit_var_case]
QED

val _ = merge_terms_ind_thm |> update_precondition;
val r = translate to_npbc_fast;
val r = translate to_gnpbc_def;
val r = translate inject_def;

val r = translate parse_constraint_LHS_aux_def;
val r = translate parse_constraint_LHS_def;

val r = translate is_arrow_def;
val r = translate parse_reif_aux_def;
val r = translate parse_op_def;
val r = translate mk_hd_def;

val r = translate pbcTheory.map_pbhd_def;
val PBC_PBHD_TYPE_def = fetch "-" "PBC_PBHD_TYPE_def";
val r = translate pbcTheory.map_pbc_def;
val r = translate pbcTheory.map_obj_def;
val r = translate mk_npbc_def;
val r = translate parse_constraint_front_def;
val r = translate parse_pbc_rest_def;

val r = translate strip_rup_hint_ok;

Theorem strip_rup_hint_side[local]:
  strip_rup_hint_side xs ⇔ T
Proof
  rw[fetch "-" "strip_rup_hint_side_def"]>>
  irule (CONJUNCT2 tok_nums_side)>>simp[]
QED

val _ = strip_rup_hint_side |> update_precondition;
val r = translate parse_rup_hint_def;
val r = translate parse_rup_def;

val r = translate start_subproof_def;
val r = translate parse_red_header_def;
val r = translate parse_pbc_header_def;

val r = translate (strip_term_def |> REWRITE_RULE [strlen_small]);

Theorem strip_term_side[local]:
  strip_term_side s ⇔ T
Proof
  rw[fetch "-" "strip_term_side_def",smallnum_lt_str_def,smallnum_sub_str_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

val _ = strip_term_side |> update_precondition;

val _ = translate is_numeric_def;
val _ = translate is_num_prefix_def;

val r = translate (int_start_def |> REWRITE_RULE [strlen_small]);

Theorem int_start_side[local]:
  int_start_side s ⇔ T
Proof
  rw[fetch "-" "int_start_side_def",smallnum_lt_str_def,smallnum_sub_str_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

val _ = int_start_side |> update_precondition;

val r = translate tokenize_eq;
val r = translate term_last_def;
val r = translate replace_last_def;
val r = translate strip_term_line_last;

val r = translate colon_id_opt_def;
val colon_id_opt_side_def = fetch "-" "colon_id_opt_side_def";
val colon_id_opt_side = Q.prove(
  `∀x. colon_id_opt_side x <=> T`,
  rw[Once colon_id_opt_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;


val r = translate check_end_def;

val r = translate check_mark_qed_id_opt_def;
val r = translate check_mark_qed_id_def;

Definition check_mark_qed_id_pbc_def:
  check_mark_qed_id_pbc s = check_mark_qed_id (INL «pbc») s
End

val r = translate check_mark_qed_id_pbc_def;

(* Just ensuring failing to parse line has the right index *)
Definition sub_one_def:
  sub_one (n:num) = if n = 0 then 0 else n - 1
End
val r = translate sub_one_def;

Theorem EqualityType_SUM_TYPE:
  EqualityType t1 ∧ EqualityType t2 ⇒
  EqualityType (SUM_TYPE t1 t2)
Proof
  EVAL_TAC>>rw[]
  >- (
    Cases_on`x1`>>fs[SUM_TYPE_def]>>
    simp[no_closures_def]>>
    metis_tac[])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[SUM_TYPE_def])>>
  Cases_on`x1`>>Cases_on`x2`>>
  fs[SUM_TYPE_def]>>
  EVAL_TAC>>
  metis_tac[]
QED

Theorem EqualityType_PBC_LIT_TYPE:
  EqualityType a ⇒
  EqualityType (PBC_LIT_TYPE a)
Proof
  EVAL_TAC>>
  rw[]>>
  Cases_on`x1`>>fs[PBC_LIT_TYPE_def]>>
  TRY(Cases_on`x2`>>fs[PBC_LIT_TYPE_def])>>
  EVAL_TAC>>
  metis_tac[]
QED

val r = translate (parse_hash_num_def |> REWRITE_RULE [strlen_small]
  |> ONCE_REWRITE_RULE [GSYM sub_check_def]);

Theorem parse_hash_num_side[local]:
  ∀x. parse_hash_num_side x ⇔ T
Proof
  Induct>>
  rw[Once (fetch "-" "parse_hash_num_side_def"),sub_check_def,
     smallnum_lt_str_def,smallnum_sub_str_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

val _ = parse_hash_num_side |> update_precondition;

val r = translate parse_subgoal_num_def;

val parse_subgoal_num_side_def = fetch "-" "parse_subgoal_num_side_def";
val parse_subgoal_num_side = Q.prove(
  `∀x . parse_subgoal_num_side x <=> T`,
  Induct>>rw[Once parse_subgoal_num_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_proofgoal_def;
val r = translate mk_acc_def;
val r = translate mk_proofgoal_mark_def;

val r = translate parse_scopetext_def;
val r = translate parse_scopehead_def;
val r = translate mk_scope_mark_def;
val r = translate check_qed_def;

(* Parsing one proof line *)
val r = translate split_lit_def;
val r = translate parse_lits_line_aux_def;
val r = translate parse_assg_def;

val r = translate_no_ind (parse_solx_aux_def |> REWRITE_RULE [strlen_small]);

Theorem parse_solx_aux_ind_small[local]:
  parse_solx_aux_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "parse_solx_aux_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac pb_parseTheory.parse_solx_aux_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  gvs[strlen_small]
QED

val _ = parse_solx_aux_ind_small |> update_precondition;

Theorem parse_solx_aux_side[local]:
  ∀ss assg free. parse_solx_aux_side ss assg free ⇔ T
Proof
  ho_match_mp_tac parse_solx_aux_ind>>
  rw[]>>
  simp[Once (fetch "-" "parse_solx_aux_side_def")]>>
  rw[smallnum_lt_str_def,smallnum_sub_str_def]>>
  gvs[semanticPrimitivesTheory.index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

val _ = parse_solx_aux_side |> update_precondition;

val res = translate parse_delc_header_def;

Theorem parse_delc_header_side[local]:
  ∀x. parse_delc_header_side x ⇔ T
Proof
  simp[fetch "-" "parse_delc_header_side_def"]>>
  rw[]>>
  intLib.ARITH_TAC
QED

val _ = parse_delc_header_side |> update_precondition;

val res = translate OPTION_BIND_def;

val res = translate (strip_obju_end_def |> SIMP_RULE std_ss [GSYM mllistTheory.take_def,GSYM mllistTheory.drop_def]);
val res = translate normalise_obj_def;
val res = translate parse_obj_term_def;
val res = translate parse_b_obj_term_def;
val res = translate parse_preserve_def;
val res = translate parse_vars_line_aux_def;
val res = translate parse_vars_line_def;

val r = translate parse_line_def;

val PB_PARSE_PLINE_TYPE_def = fetch "-" "PB_PARSE_PLINE_TYPE_def";

val r = translate is_lstep_def;
val r = translate fin_lstep_def;
val res = translate list_to_num_set_def;
val r = translate fin_cstep_def;

(*
  The name table
*)
val r = translate lz97_aux_def;

Theorem lz97_aux_side[local]:
  ∀s n i h. n = strlen s ∧ i ≤ n ∧ h < 2 ** 30 ⇒ lz97_aux_side s n i h
Proof
  ho_match_mp_tac lz97_aux_ind>>
  rpt strip_tac>>
  simp[Once (fetch "-" "lz97_aux_side_def")]>>
  qspecl_then [`h`,`strsub_unsafe s i`] assume_tac lz97_step_bound>>
  `(if h < 11069489 then h else h MOD 11069489) < 11069489` by rw[]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_lt_def,
     smallnum_mod_def,smallnum_add_def,smallnum_mul_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  rw[]
QED

val r = translate lz97_def;

Theorem lz97_side[local]:
  lz97_side s ⇔ T
Proof
  rw[fetch "-" "lz97_side_def"]>>
  irule lz97_aux_side>>simp[]
QED

val _ = lz97_side |> update_precondition;

val r = translate bfind_def;

(* Every hash stored in b is a small number *)
Definition bucket_small_def:
  (bucket_small Bnil ⇔ T) ∧
  (bucket_small (Bnode h w n rest) ⇔ h < 2 ** 30 ∧ bucket_small rest)
End

Theorem bfind_side[local]:
  ∀h v b. h < 2 ** 30 ∧ bucket_small b ⇒ bfind_side h v b
Proof
  Induct_on`b`>>
  rw[Once (fetch "-" "bfind_side_def"),bucket_small_def,
     semanticPrimitivesTheory.index_in_bounds_def]>>
  intLib.ARITH_TAC
QED

val r = translate bidx_def;

Theorem bidx_side[local]:
  bidx_side h m ⇔ h < 2 ** 30 ∧ 0 < m ∧ m < 2 ** 30
Proof
  rw[fetch "-" "bidx_side_def",semanticPrimitivesTheory.index_in_bounds_def]
QED

val r = translate tb_sizes_def;
val r = translate next_size_aux_def;
val r = translate next_size_def;

val r = translate read_nat_def;

Theorem read_nat_side[local]:
  n = strlen s ∧ i ≤ n ⇒ read_nat_side s i n
Proof
  rw[fetch "-" "read_nat_side_def",smallnum_lt_str_def,smallnum_add_str_def]
  >>~- ([`num_run_side _ _ _ _ _`], irule num_run_side>>simp[])>>
  fs[integerTheory.INT_NOT_LT]
QED

val r = translate x_initial_def;

Theorem x_initial_side[local]:
  x_initial_side s ⇔ T
Proof
  rw[fetch "-" "x_initial_side_def",smallnum_lt_str_def,
     semanticPrimitivesTheory.index_in_bounds_def]
QED

val _ = x_initial_side |> update_precondition;

val NAME_TABLE_BUCKET_TYPE_def = fetch "-" "NAME_TABLE_BUCKET_TYPE_def";

Theorem ARRAY_OF_NAME_TABLE_BUCKET_HPROP_INJ[hprop_inj]:
  HPROP_INJ (ARRAY_OF NAME_TABLE_BUCKET_TYPE av xs)
    (ARRAY_OF NAME_TABLE_BUCKET_TYPE av xs') (xs' = xs)
Proof
  irule ARRAY_OF_EqualityType_HPROP_INJ>>
  simp (eq_lemmas())
QED

(*
  The table is a reference to its bucket array, a reference to the next
  number, the first number and the limit (res_var). nt_var numbers a name
  as res_var does; the hash and the bucket index are small numbers
  (lz97_bound).
*)
Definition NT_TABLE_def:
  NT_TABLE lim (s:mlstring name_to_num_state) tv =
    SEP_EXISTS tabr nxtr basev limv av nv bs base.
      &(tv = Conv NONE [tabr; nxtr; basev; limv] ∧
        NUM base basev ∧ OPTION_TYPE NUM lim limv ∧ NUM s.next_num nv ∧
        tb_rel bs s ∧ base ≤ s.next_num) *
      REF tabr av * ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs * REF nxtr nv
End

Quote add_cakeml:
  fun nt_new lim n0 = (Ref (Array.array 1021 Bnil), Ref n0, n0, lim)
End

Theorem nt_new_spec:
  OPTION_TYPE NUM lim limv ∧ NUM n nv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_new" (get_ml_prog_state()))
    [limv; nv]
    emp
    (POSTv tv. NT_TABLE lim (nt_init n) tv)
Proof
  rw[]>>
  xcf "nt_new" (get_ml_prog_state ())>>
  xlet`POSTv nxtr. REF nxtr nv`
  >- (xref>>xsimpl)>>
  xlet`POSTv bv. &NAME_TABLE_BUCKET_TYPE Bnil bv * REF nxtr nv`
  >- (xcon>>xsimpl>>simp[NAME_TABLE_BUCKET_TYPE_def])>>
  xlet`POSTv av.
    ARRAY_OF NAME_TABLE_BUCKET_TYPE av (REPLICATE 1021 Bnil) * REF nxtr nv`
  >- (
    xapp_spec (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_alloc_spec)>>
    xsimpl>>
    qexists_tac`Bnil`>>xsimpl)>>
  xlet`POSTv tabr. REF tabr av *
    ARRAY_OF NAME_TABLE_BUCKET_TYPE av (REPLICATE 1021 Bnil) * REF nxtr nv`
  >- (xref>>xsimpl)>>
  xcon>>
  simp[NT_TABLE_def]>>
  xsimpl>>
  qexistsl_tac[`REPLICATE 1021 Bnil`,`n`]>>
  simp[nt_init_def,tb_rel_init]>>
  xsimpl
QED

Quote add_cakeml:
  fun nt_move arr2 m2 b =
    case b of
      Bnil => ()
    | Bnode h v n rest =>
      let val j = bidx h m2 in
        Unsafe.update arr2 j (Bnode h v n (Unsafe.sub arr2 j));
        nt_move arr2 m2 rest
      end
End

Theorem nt_move_spec:
  ∀b bv bs2 arr2 m2v.
  NAME_TABLE_BUCKET_TYPE b bv ∧
  bucket_small b ∧ NUM (LENGTH bs2) m2v ∧ 0 < LENGTH bs2 ∧
  LENGTH bs2 < 2 ** 30 ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_move" (get_ml_prog_state()))
    [arr2; m2v; bv]
    (ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2 bs2)
    (POSTv u.
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2 (bucket_move bs2 b) *
      &UNIT_TYPE () u)
Proof
  Induct>>
  rw[]>>
  xcf "nt_move" (get_ml_prog_state ())>>
  gvs[NAME_TABLE_BUCKET_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    simp[bucket_move_def]>>
    xsimpl)>>
  rename1`bucket_small (Bnode h w n rest)`>>
  gvs[bucket_small_def]>>
  xmatch>>
  xlet`POSTv jv.
    ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2 bs2 * &NUM (h MOD LENGTH bs2) jv`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`LENGTH bs2`,`h`]>>
    simp[bidx_side,bidx_def,smallnum_mod_def])>>
  `h MOD LENGTH bs2 < LENGTH bs2` by simp[]>>
  xlet_auto_spec
    (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_unsafe_sub_spec))
  >- xsimpl>>
  xlet`POSTv nbv. ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2 bs2 *
    &NAME_TABLE_BUCKET_TYPE
      (Bnode h w n (EL (h MOD LENGTH bs2) bs2)) nbv`
  >- (
    xcon>>
    xsimpl>>
    simp[NAME_TABLE_BUCKET_TYPE_def])>>
  xlet_auto_spec
    (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_unsafe_update_spec))
  >- xsimpl>>
  xapp>>
  qexistsl_tac[`emp`,
    `LUPDATE (Bnode h w n (EL (h MOD LENGTH bs2) bs2))
       (h MOD LENGTH bs2) bs2`]>>
  simp[bucket_move_def]>>
  xsimpl
QED

Quote add_cakeml:
  fun nt_relink arr arr2 m2 i m =
    if Unsafe.Arith.gtWitness m i arr then
      (nt_move arr2 m2 (Unsafe.sub arr i);
       nt_relink arr arr2 m2 (Unsafe.Arith.addWitness i 1 arr) m)
    else ()
End

Theorem nt_relink_spec:
  ∀k i iv bs bs2 arr arr2 mv m2v.
  k = LENGTH bs - i ∧ i ≤ LENGTH bs ∧ EVERY bucket_small bs ∧
  NUM i iv ∧ NUM (LENGTH bs) mv ∧ NUM (LENGTH bs2) m2v ∧
  0 < LENGTH bs2 ∧ LENGTH bs2 < 2 ** 30 ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_relink" (get_ml_prog_state()))
    [arr; arr2; m2v; iv; mv]
    (ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs *
     ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2 bs2)
    (POSTv u.
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs *
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2
        (FOLDL bucket_move bs2 (DROP i bs)) *
      &UNIT_TYPE () u)
Proof
  Induct>>
  rw[]>>
  xcf "nt_relink" (get_ml_prog_state ())>>
  (xlet_auto_spec
     (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ccnf_arithTheory.num_gt_arr_spec))
   >- xsimpl)>>
  xif
  >- (
    qexists_tac`F`>>
    simp[]>>
    xcon>>
    simp[DROP_LENGTH_TOO_LONG]>>
    xsimpl)>>
  qexists_tac`T`>>
  simp[]>>
  `i < LENGTH bs` by decide_tac>>
  xlet_auto_spec
    (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_unsafe_sub_spec))
  >- xsimpl>>
  xlet`POSTv u. ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs *
    ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2 (bucket_move bs2 (EL i bs))`
  >- (
    xapp>>
    qexistsl_tac[`ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs`,`bs2`,`EL i bs`]>>
    xsimpl>>
    gvs[EVERY_EL])>>
  xlet_auto_spec
    (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ccnf_arithTheory.num_add_arr_spec))
  >- (xsimpl>>gvs[])>>
  rename1`NUM (i + 1) iv1`>>
  last_x_assum (qspecl_then [`i + 1`,`iv1`,`bs`,`bucket_move bs2 (EL i bs)`,
                             `arr`,`arr2`,`mv`,`m2v`] mp_tac)>>
  impl_tac
  >- gvs[LENGTH_bucket_move]>>
  strip_tac>>
  xapp>>
  xsimpl>>
  simp[DROP_EL_CONS]>>
  xsimpl
QED

Quote add_cakeml:
  fun nt_grow tabr arr m =
    let val m2 = next_size m in
      if m < m2 then
        let val arr2 = Array.array m2 Bnil in
          (nt_relink arr arr2 m2 0 m; tabr := arr2)
        end
      else ()
    end
End

(* The larger size, if any, is still small *)
Theorem next_size_bound:
  m ≤ next_size m ∧ (m < next_size m ⇒ next_size m ≤ 33456139)
Proof
  `∀l. m ≤ next_size_aux m l ∧
       (m < next_size_aux m l ⇒ MEM (next_size_aux m l) l)` by (
    Induct>>
    rw[next_size_aux_def])>>
  `∀k. MEM k tb_sizes ⇒ k ≤ 33456139` by (
    simp[tb_sizes_def]>>
    rw[]>>
    simp[])>>
  rw[next_size_def]>>
  metis_tac[]
QED

Theorem nt_grow_spec:
  EVERY bucket_small bs ∧
  NUM (LENGTH bs) mv ∧ 0 < LENGTH bs ∧ LENGTH bs < 2 ** 30 ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_grow" (get_ml_prog_state()))
    [tabr; arr; mv]
    (REF tabr arr * ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs)
    (POSTv u. SEP_EXISTS arr'. REF tabr arr' *
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr'
        (if LENGTH bs < next_size (LENGTH bs)
         then tb_grow bs (next_size (LENGTH bs)) else bs) *
      &UNIT_TYPE () u)
Proof
  rw[]>>
  xcf "nt_grow" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_autop>>
  xif
  >- (
    qexists_tac`T`>>
    simp[]>>
    `next_size (LENGTH (bs:bucket list)) ≤ 33456139` by metis_tac[next_size_bound]>>
    xlet`POSTv bv0. &NAME_TABLE_BUCKET_TYPE Bnil bv0 * REF tabr arr *
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs`
    >- (xcon>>xsimpl>>simp[NAME_TABLE_BUCKET_TYPE_def])>>
    xlet`POSTv arr2.
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2
        (REPLICATE (next_size (LENGTH bs)) Bnil) *
      REF tabr arr * ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs`
    >- (
      xapp_spec (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_alloc_spec)>>
      qrefinel[`_`,`Bnil`,`next_size (LENGTH bs)`]>>
      xsimpl)>>
    xlet`POSTv u. REF tabr arr * ARRAY_OF NAME_TABLE_BUCKET_TYPE arr bs *
      ARRAY_OF NAME_TABLE_BUCKET_TYPE arr2
        (tb_grow bs (next_size (LENGTH bs)))`
    >- (
      xapp>>
      qrefinel[`_`,`0`,`REPLICATE (next_size (LENGTH bs)) Bnil`,`bs`]>>
      simp[tb_grow_def]>>
      xsimpl)>>
    xapp>>
    xsimpl)>>
  qexists_tac`F`>>
  simp[]>>
  xcon>>
  xsimpl
QED

(* A table of m buckets, numbering names from base, is due to grow when more
  than half its buckets' worth of names are stored, n1 being the next number *)
Definition nt_grow_due_def:
  nt_grow_due (m:num) n1 base ⇔ m < 2 * (n1 − base)
End

val res = translate nt_grow_due_def;

Quote add_cakeml:
  fun nt_find_ins tabr nxtr base v =
    let
      val arr = !tabr
      val h = lz97 v
      val m = Array.length arr
      val i = bidx h m
      val b = Unsafe.sub arr i
    in
      case bfind h v b of
        Bnode _ _ n _ => n
      | Bnil =>
        let
          val n = !nxtr
          val n1 = n + 1
        in
          (Unsafe.update arr i (Bnode h v n b);
           nxtr := n1;
           (if nt_grow_due m n1 base then nt_grow tabr arr m else ());
           n)
        end
    end
End

(* The hashes stored in a table are small numbers *)
Theorem bucket_ok_bucket_small:
  ∀b. bucket_ok m i b ⇒ bucket_small b
Proof
  Induct>>
  rw[bucket_ok_def,bucket_small_def]>>
  rename1`lz97 w < _`>>
  mp_tac (Q.INST [`s`|->`w`] lz97_bound)>>
  simp[]
QED

Theorem tb_rel_bucket_small:
  tb_rel bs s ⇒ EVERY bucket_small bs
Proof
  rw[tb_rel_def,EVERY_EL]>>
  metis_tac[bucket_ok_bucket_small]
QED

Theorem nt_find_ins_spec:
  tb_rel bs s ∧ base ≤ s.next_num ∧ NUM s.next_num nv ∧
  NUM base basev ∧ STRING_TYPE v vv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_find_ins" (get_ml_prog_state()))
    [tabr; nxtr; basev; vv]
    (REF tabr av * ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs * REF nxtr nv)
    (POSTv r. SEP_EXISTS n s' av' bs' nv'.
      REF tabr av' * ARRAY_OF NAME_TABLE_BUCKET_TYPE av' bs' * REF nxtr nv' *
      &(name_to_num_var v s = (n,s') ∧ NUM n r ∧
        tb_rel bs' s' ∧ base ≤ s'.next_num ∧ NUM s'.next_num nv'))
Proof
  rw[]>>
  xcf "nt_find_ins" (get_ml_prog_state ())>>
  drule tb_rel_bucket_small>>
  strip_tac>>
  `0 < LENGTH bs ∧ LENGTH bs < 2 ** 30` by (
    gvs[tb_rel_def]>>
    Cases_on`bs`>>
    gvs[])>>
  qabbrev_tac`i = lz97 v MOD LENGTH bs`>>
  `i < LENGTH bs` by simp[Abbr`i`]>>
  xlet`POSTv av1. REF tabr av * ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs *
    REF nxtr nv * &(av1 = av)`
  >- (xapp>>xsimpl)>>
  rveq>>
  xlet_autop>>
  xlet`POSTv mv. REF tabr av * ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs *
    REF nxtr nv * &NUM (LENGTH bs) mv`
  >- (
    xapp_spec (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_length_spec)>>
    qexistsl_tac[`REF tabr av * REF nxtr nv`,`bs`]>>
    xsimpl)>>
  rename1`NUM (lz97 v) hv`>>
  assume_tac (Q.INST [`s`|->`v`] lz97_bound)>>
  xlet`POSTv iv. ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs * REF tabr av *
    REF nxtr nv * &NUM i iv`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`LENGTH bs`,`lz97 v`]>>
    gvs[bidx_side,bidx_def,smallnum_mod_def,Abbr`i`])>>
  xlet_auto_spec
    (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_unsafe_sub_spec))
  >- xsimpl>>
  `bucket_small (EL i bs)` by gvs[EVERY_EL]>>
  xlet`POSTv fv. ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs * REF tabr av *
    REF nxtr nv * &NAME_TABLE_BUCKET_TYPE (bfind (lz97 v) v (EL i bs)) fv`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`v`,`lz97 v`,`EL i bs`]>>
    gvs[]>>
    irule bfind_side>>
    simp[])>>
  `(lookup_index s v = NONE ⇔ bfind (lz97 v) v (EL i bs) = Bnil) ∧
   ∀h' w n rest. bfind (lz97 v) v (EL i bs) = Bnode h' w n rest ⇒
     lookup_index s v = SOME n` by (
    drule_then (qspecl_then [`v`,`lz97 v`] mp_tac) tb_rel_bfind>>
    simp[Abbr`i`])>>
  Cases_on`bfind (lz97 v) v (EL i bs)`>>
  gvs[NAME_TABLE_BUCKET_TYPE_def]>>
  xmatch
  >- (
    xlet`POSTv nv1. ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs * REF tabr av *
      REF nxtr nv * &(nv1 = nv)`
    >- (xapp>>xsimpl)>>
    xlet_autop>>
    rename1`NUM (s.next_num + 1) nv2`>>
    Cases_on`name_to_num_var v s`>>
    rename1`name_to_num_var v s = (n1,s1)`>>
    drule_all tb_rel_insert>>
    strip_tac>>
    gvs[]>>
    `LENGTH (tb_insert bs v s.next_num) = LENGTH bs` by
      simp[tb_insert_def]>>
    `LUPDATE (Bnode (lz97 v) v s.next_num (EL i bs)) i bs =
     tb_insert bs v s.next_num` by
      simp[Abbr`i`,tb_insert_def]>>
    `EVERY bucket_small (tb_insert bs v s.next_num)` by (
      irule tb_rel_bucket_small>>
      qexists_tac`s1`>>
      simp[])>>
    xlet`POSTv bnv. ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs * REF tabr av *
      REF nxtr nv *
      &NAME_TABLE_BUCKET_TYPE (Bnode (lz97 v) v s.next_num (EL i bs)) bnv`
    >- (xcon>>xsimpl>>gvs[NAME_TABLE_BUCKET_TYPE_def])>>
    xlet_auto_spec
      (SOME (Q.ISPEC`NAME_TABLE_BUCKET_TYPE` ARRAY_OF_unsafe_update_spec))
    >- xsimpl>>
    xlet`POSTv u.
      ARRAY_OF NAME_TABLE_BUCKET_TYPE av (tb_insert bs v s.next_num) *
      REF tabr av * REF nxtr nv2`
    >- (xapp>>simp[]>>xsimpl)>>
    xlet_auto
    >- (xsimpl>>simp[fetch "-" "nt_grow_due_side_def"])>>
    xlet`POSTv u. SEP_EXISTS av' bs'. REF tabr av' *
      ARRAY_OF NAME_TABLE_BUCKET_TYPE av' bs' * REF nxtr nv2 *
      &tb_rel bs' (s1:mlstring name_to_num_state)`
    >- (
      xif
      >- (
        xapp>>
        qrefinel[`_`,`tb_insert bs v s.next_num`]>>
        xsimpl>>
        rw[]
        >- (
          qexists_tac
            `tb_grow (tb_insert bs v s.next_num) (next_size (LENGTH bs))`>>
          reverse conj_tac
          >- xsimpl>>
          irule tb_rel_grow>>
          simp[]>>
          `next_size (LENGTH (bs:bucket list)) ≤ 33456139` by
            metis_tac[next_size_bound]>>
          simp[])>>
        qexists_tac`tb_insert bs v s.next_num`>>
        simp[]>>
        xsimpl)>>
      xcon>>
      xsimpl>>
      qexists_tac`tb_insert bs v s.next_num`>>
      simp[]>>
      xsimpl)>>
    xvar>>
    xsimpl>>
    qexists_tac`bs'`>>
    simp[]>>
    xsimpl)>>
  drule lookup_index_SOME_name_to_num_var>>
  strip_tac>>
  xvar>>
  xsimpl>>
  qexists_tac`bs`>>
  simp[]>>
  xsimpl
QED

Quote add_cakeml:
  fun nt_var tv lno v =
    case tv of (tabr, nxtr, base, lim) =>
    case lim of
      None => nt_find_ins tabr nxtr base v
    | Some l =>
      if x_initial v then
        (case read_nat v 1 (String.size v) of
          None => raise Fail (format_failure lno ("invalid variable name: " ^ v))
        | Some n => if n <= l then n else nt_find_ins tabr nxtr base v)
      else nt_find_ins tabr nxtr base v
End

Theorem nt_var_spec:
  NUM lno lnov ∧ STRING_TYPE v vv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_var" (get_ml_prog_state()))
    [tv; lnov; vv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS n s'. NT_TABLE lim s' tv *
        &(res_var lim v s = SOME (n,s') ∧ NUM n r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ res_var lim v s = NONE)))
Proof
  rw[]>>
  xcf "nt_var" (get_ml_prog_state ())>>
  simp[NT_TABLE_def]>>
  xpull>>
  xmatch>>
  namedCases_on`lim`["","l"]>>
  gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xapp>>
    xsimpl>>
    qrefinel[`_`,`v`,`s`,`bs`,`base`]>>
    xsimpl>>
    simp[res_var_NONE]>>
    rw[]>>
    qmatch_goalsub_rename_tac`ARRAY_OF _ _ bs1 ==>> _`>>
    qexistsl_tac[`bs1`,`base`]>>
    simp[]>>
    xsimpl)>>
  xlet_autop>>
  xif
  >- (
    `1 ≤ strlen v ∧ strsub v 0 = #"x"` by gvs[x_initial_thm]>>
    xlet_autop>>
    xlet`POSTv ov. REF tabr av * ARRAY_OF NAME_TABLE_BUCKET_TYPE av bs *
      REF nxtr nv *
      &OPTION_TYPE NUM (fromNatString (substring v 1 (strlen v - 1))) ov`
    >- (
      xapp>>
      xsimpl>>
      qexistsl_tac[`v`,`strlen v`]>>
      simp[read_nat_side,read_nat_fromNatString])>>
    namedCases_on`fromNatString (substring v 1 (strlen v - 1))`["","n"]>>
    gvs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      qexists_tac`s`>>
      simp[res_var_def,Fail_exn_def]>>
      xsimpl>>
      qexistsl_tac[`bs`,`base`]>>
      simp[]>>
      first_assum (irule_at Any)>>
      xsimpl)>>
    xlet_autop>>
    xif
    >- (
      xvar>>
      xsimpl>>
      qexistsl_tac[`n`,`s`]>>
      simp[res_var_def]>>
      xsimpl>>
      qexistsl_tac[`bs`,`base`]>>
      simp[]>>
      xsimpl)>>
    `res_var (SOME l) v s = SOME (name_to_num_var v s)` by simp[res_var_def]>>
    xapp>>
    xsimpl>>
    qrefinel[`_`,`v`,`s`,`bs`,`base`]>>
    xsimpl>>
    rw[]>>
    qmatch_goalsub_rename_tac`ARRAY_OF _ _ bs1 ==>> _`>>
    qexistsl_tac[`bs1`,`base`]>>
    simp[]>>
    xsimpl)>>
  `res_var (SOME l) v s = SOME (name_to_num_var v s)` by (
    rw[res_var_def]>>
    gvs[x_initial_thm])>>
  xapp>>
  xsimpl>>
  qrefinel[`_`,`v`,`s`,`bs`,`base`]>>
  xsimpl>>
  rw[]>>
  qmatch_goalsub_rename_tac`ARRAY_OF _ _ bs1 ==>> _`>>
  qexistsl_tac[`bs1`,`base`]>>
  simp[]>>
  xsimpl
QED

(*
  Numbering a parsed line (name_pline); each list is rebuilt in order,
  its head numbered before its tail
*)
Quote add_cakeml:
  fun nt_lit tv lno l =
    case l of
      Pos v => Pos (nt_var tv lno v)
    | Neg v => Neg (nt_var tv lno v)
End

(* TMC *)
Quote add_cakeml:
  fun nt_lin tv lno xs =
    case xs of
      [] => []
    | ((c,l)::rest) =>
      let val l1 = nt_lit tv lno l in (c,l1) :: nt_lin tv lno rest end
End

(* TMC *)
Quote add_cakeml:
  fun nt_lits tv lno ls =
    case ls of
      [] => []
    | (l::rest) =>
      let val l1 = nt_lit tv lno l in l1 :: nt_lits tv lno rest end
End

(* TMC *)
Quote add_cakeml:
  fun nt_vars tv lno vs =
    case vs of
      [] => []
    | (v::rest) =>
      let val n = nt_var tv lno v in n :: nt_vars tv lno rest end
End

(* TMC *)
Quote add_cakeml:
  fun nt_assg tv lno vs =
    case vs of
      [] => []
    | ((v,b)::rest) =>
      let val n = nt_var tv lno v in (n,b) :: nt_assg tv lno rest end
End

(* TMC *)
Quote add_cakeml:
  fun nt_subst tv lno ss =
    case ss of
      [] => []
    | ((v,r)::rest) =>
      let val n = nt_var tv lno v in
        case r of
          Inl b => (n,Inl b) :: nt_subst tv lno rest
        | Inr l =>
          let val l1 = nt_lit tv lno l in (n,Inr l1) :: nt_subst tv lno rest end
      end
End

Quote add_cakeml:
  fun nt_pbhd tv lno h =
    case h of
      Fwd ls rel => Fwd (nt_lits tv lno ls) rel
    | Bwd l cmp => Bwd (nt_lit tv lno l) cmp
    | Iff l cmp => Iff (nt_lit tv lno l) cmp
End

Quote add_cakeml:
  fun nt_pbc tv lno c =
    case c of (h,(xs,d)) =>
      let val h1 = nt_pbhd tv lno h in (h1,(nt_lin tv lno xs,d)) end
End

Quote add_cakeml:
  fun nt_constr tv lno c =
    case c of
      Id n => Id n
    | Add c1 c2 =>
      let val d1 = nt_constr tv lno c1 in Add d1 (nt_constr tv lno c2) end
    | Mul c1 k => Mul (nt_constr tv lno c1) k
    | Div_1 dt c1 k => Div_1 dt (nt_constr tv lno c1) k
    | Minus c1 k => Minus (nt_constr tv lno c1) k
    | Sat c1 => Sat (nt_constr tv lno c1)
    | Lit l => Lit (nt_lit tv lno l)
    | Weak c1 vs =>
      let val d1 = nt_constr tv lno c1 in Weak d1 (nt_vars tv lno vs) end
    | _ => raise Fail (format_failure lno "unexpected cutting planes term")
End

Quote add_cakeml:
  fun nt_hconcl tv lno hc =
    case hc of
      Hnoconcl => Hnoconcl
    | Hdsat ao =>
      (case ao of
        None => Hdsat None
      | Some a => Hdsat (Some (nt_assg tv lno a)))
    | Hdunsat n => Hdunsat n
    | Hobounds lb ub n ao =>
      (case ao of
        None => Hobounds lb ub n None
      | Some a => Hobounds lb ub n (Some (nt_assg tv lno a)))
    | Heenum n b h => Heenum n b h
End

Quote add_cakeml:
  fun nt_line tv lno pl =
    case pl of
      Pbchd c => Pbchd (nt_pbc tv lno c)
    | Pol c => Pol (nt_constr tv lno c)
    | Rupl c ns => Rupl (nt_pbc tv lno c) ns
    | Checkl n c => Checkl n (nt_pbc tv lno c)
    | Implyl n c => Implyl n (nt_pbc tv lno c)
    | Redhd c ss =>
      let val c1 = nt_pbc tv lno c in Redhd c1 (nt_subst tv lno ss) end
    | Domhd c ss =>
      let val c1 = nt_pbc tv lno c in Domhd c1 (nt_subst tv lno ss) end
    | Delchd n ss => Delchd n (nt_subst tv lno ss)
    | Objuhd b (f,k) => Objuhd b (nt_lin tv lno f,k)
    | Preshd b x c =>
      let val n = nt_var tv lno x in Preshd b n (nt_pbc tv lno c) end
    | Loadord r ws => Loadord r (nt_assg tv lno ws)
    | Soll a b ov => Soll (nt_assg tv lno a) b ov
    | Solxl a fr =>
      let val a1 = nt_assg tv lno a in Solxl a1 (nt_vars tv lno fr) end
    | Eobj (f,k) => Eobj (nt_lin tv lno f,k)
    | Epres vs => Epres (nt_vars tv lno vs)
    | Ordhd n => Ordhd n
    | Ldone st => Ldone st
    | Cdone st => Cdone st
End

Overload "line_TYPE" = ``LIST_TYPE (SUM_TYPE STRING_TYPE INT)``
Overload "pbc_TYPE" = ``λa.
  PAIR_TYPE (PBC_PBHD_TYPE a)
    (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE a))) INT)``
Overload "lin_TYPE" = ``λa. LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE a))``

Theorem nt_lit_spec:
  NUM lno lnov ∧ PBC_LIT_TYPE STRING_TYPE l lv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_lit" (get_ml_prog_state()))
    [tv; lnov; lv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS l1 s'. NT_TABLE lim s' tv *
        &(name_lit lim l s = SOME (l1,s') ∧ PBC_LIT_TYPE NUM l1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_lit lim l s = NONE)))
Proof
  rw[]>>
  xcf "nt_lit" (get_ml_prog_state ())>>
  Cases_on`l`>>
  gvs[PBC_LIT_TYPE_def]>>
  xmatch>>
  rename1`STRING_TYPE v vv`>>
  (
    xlet`POSTve
      (λr. SEP_EXISTS n s'. NT_TABLE lim s' tv *
        &(res_var lim v s = SOME (n,s') ∧ NUM n r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ res_var lim v s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_lit_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_lit_def,PBC_LIT_TYPE_def]>>
    xsimpl)
QED

Theorem nt_lits_spec:
  ∀ls lsv s.
  NUM lno lnov ∧ LIST_TYPE (PBC_LIT_TYPE STRING_TYPE) ls lsv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_lits" (get_ml_prog_state()))
    [tv; lnov; lsv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS ls1 s'. NT_TABLE lim s' tv *
        &(name_lits lim ls s = SOME (ls1,s') ∧
          LIST_TYPE (PBC_LIT_TYPE NUM) ls1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_lits lim ls s = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "nt_lits" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xcon>>
    xsimpl>>
    simp[name_lits_def,LIST_TYPE_def]>>
    xsimpl)>>
  xlet`POSTve
    (λr. SEP_EXISTS l1 s1. NT_TABLE lim s1 tv *
      &(name_lit lim h s = SOME (l1,s1) ∧ PBC_LIT_TYPE NUM l1 r))
    (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ name_lit lim h s = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_lits_def]>>metis_tac[SEP_IMP_REFL])>>
  xlet`POSTve
    (λr. SEP_EXISTS ls1 s2. NT_TABLE lim s2 tv *
      &(name_lits lim ls s1 = SOME (ls1,s2) ∧
        LIST_TYPE (PBC_LIT_TYPE NUM) ls1 r))
    (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
      &(Fail_exn e ∧ name_lits lim ls s1 = NONE))`
  >- (xapp>>xsimpl)
  >- (xsimpl>>simp[name_lits_def]>>metis_tac[SEP_IMP_REFL])>>
  xcon>>
  xsimpl>>
  simp[name_lits_def,LIST_TYPE_def]>>
  xsimpl
QED

Theorem nt_assg_spec:
  ∀a av s.
  NUM lno lnov ∧ LIST_TYPE (PAIR_TYPE STRING_TYPE BOOL) a av ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_assg" (get_ml_prog_state()))
    [tv; lnov; av]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS a1 s'. NT_TABLE lim s' tv *
        &(name_assg lim a s = SOME (a1,s') ∧
          LIST_TYPE (PAIR_TYPE NUM BOOL) a1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_assg lim a s = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "nt_assg" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    simp[name_assg_def,LIST_TYPE_def]>>
    xsimpl)>>
  PairCases_on`h`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λr. SEP_EXISTS n s1. NT_TABLE lim s1 tv *
      &(res_var lim h0 s = SOME (n,s1) ∧ NUM n r))
    (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ res_var lim h0 s = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_assg_def]>>metis_tac[SEP_IMP_REFL])>>
  xlet`POSTve
    (λr. SEP_EXISTS a1 s2. NT_TABLE lim s2 tv *
      &(name_assg lim a s1 = SOME (a1,s2) ∧
        LIST_TYPE (PAIR_TYPE NUM BOOL) a1 r))
    (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
      &(Fail_exn e ∧ name_assg lim a s1 = NONE))`
  >- (xapp>>xsimpl)
  >- (xsimpl>>simp[name_assg_def]>>metis_tac[SEP_IMP_REFL])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[name_assg_def,LIST_TYPE_def,PAIR_TYPE_def]>>
  xsimpl
QED

Theorem nt_pbhd_spec:
  NUM lno lnov ∧ PBC_PBHD_TYPE STRING_TYPE h hv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_pbhd" (get_ml_prog_state()))
    [tv; lnov; hv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS h1 s'. NT_TABLE lim s' tv *
        &(name_pbhd lim h s = SOME (h1,s') ∧ PBC_PBHD_TYPE NUM h1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_pbhd lim h s = NONE)))
Proof
  rw[]>>
  xcf "nt_pbhd" (get_ml_prog_state ())>>
  Cases_on`h`>>
  gvs[PBC_PBHD_TYPE_def]>>
  xmatch
  >- (
    rename1`LIST_TYPE _ ls lsv`>>
    xlet`POSTve
      (λr. SEP_EXISTS ls1 s1. NT_TABLE lim s1 tv *
        &(name_lits lim ls s = SOME (ls1,s1) ∧
          LIST_TYPE (PBC_LIT_TYPE NUM) ls1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_lits lim ls s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pbhd_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pbhd_def,PBC_PBHD_TYPE_def]>>
    xsimpl)>>
  rename1`PBC_LIT_TYPE _ l lv`>>
  (
    xlet`POSTve
      (λr. SEP_EXISTS l1 s1. NT_TABLE lim s1 tv *
        &(name_lit lim l s = SOME (l1,s1) ∧ PBC_LIT_TYPE NUM l1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_lit lim l s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pbhd_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pbhd_def,PBC_PBHD_TYPE_def]>>
    xsimpl)
QED

Theorem nt_lin_spec:
  ∀xs xsv s.
  NUM lno lnov ∧ lin_TYPE STRING_TYPE xs xsv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_lin" (get_ml_prog_state()))
    [tv; lnov; xsv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS xs1 s'. NT_TABLE lim s' tv *
        &(name_lin lim xs s = SOME (xs1,s') ∧ lin_TYPE NUM xs1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_lin lim xs s = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "nt_lin" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    simp[name_lin_def,LIST_TYPE_def]>>
    xsimpl)>>
  PairCases_on`h`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λr. SEP_EXISTS l1 s1. NT_TABLE lim s1 tv *
      &(name_lit lim h1 s = SOME (l1,s1) ∧ PBC_LIT_TYPE NUM l1 r))
    (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ name_lit lim h1 s = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_lin_def]>>metis_tac[SEP_IMP_REFL])>>
  xlet`POSTve
    (λr. SEP_EXISTS xs1 s2. NT_TABLE lim s2 tv *
      &(name_lin lim xs s1 = SOME (xs1,s2) ∧ lin_TYPE NUM xs1 r))
    (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
      &(Fail_exn e ∧ name_lin lim xs s1 = NONE))`
  >- (xapp>>xsimpl)
  >- (xsimpl>>simp[name_lin_def]>>metis_tac[SEP_IMP_REFL])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[name_lin_def,LIST_TYPE_def,PAIR_TYPE_def]>>
  xsimpl
QED

Theorem nt_vars_spec:
  ∀vs vsv s.
  NUM lno lnov ∧ LIST_TYPE STRING_TYPE vs vsv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_vars" (get_ml_prog_state()))
    [tv; lnov; vsv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS ns s'. NT_TABLE lim s' tv *
        &(name_vars lim vs s = SOME (ns,s') ∧ LIST_TYPE NUM ns r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_vars lim vs s = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "nt_vars" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xcon>>
    xsimpl>>
    simp[name_vars_def,LIST_TYPE_def]>>
    xsimpl)>>
  xlet`POSTve
    (λr. SEP_EXISTS n s1. NT_TABLE lim s1 tv *
      &(res_var lim h s = SOME (n,s1) ∧ NUM n r))
    (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ res_var lim h s = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_vars_def]>>metis_tac[SEP_IMP_REFL])>>
  xlet`POSTve
    (λr. SEP_EXISTS ns s2. NT_TABLE lim s2 tv *
      &(name_vars lim vs s1 = SOME (ns,s2) ∧ LIST_TYPE NUM ns r))
    (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
      &(Fail_exn e ∧ name_vars lim vs s1 = NONE))`
  >- (xapp>>xsimpl)
  >- (xsimpl>>simp[name_vars_def]>>metis_tac[SEP_IMP_REFL])>>
  xcon>>
  xsimpl>>
  simp[name_vars_def,LIST_TYPE_def]>>
  xsimpl
QED

Theorem nt_constr_spec:
  ∀lim c s cv.
  NUM lno lnov ∧ NPBC_CHECK_CONSTR_TYPE STRING_TYPE c cv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_constr" (get_ml_prog_state()))
    [tv; lnov; cv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS c1 s'. NT_TABLE lim s' tv *
        &(name_constr lim c s = SOME (c1,s') ∧
          NPBC_CHECK_CONSTR_TYPE NUM c1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_constr lim c s = NONE)))
Proof
  Induct_on`c`>>
  rpt strip_tac>>
  xcf "nt_constr" (get_ml_prog_state ())>>
  gvs[NPBC_CHECK_CONSTR_TYPE_def]>>
  xmatch
  >~ [`Id`]
  >- (
    xcon>>
    xsimpl>>
    simp[name_constr_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xsimpl)
  >~ [`Add`]
  >- (
    rename1`name_constr lim (Add ca cb) s`>>
    xlet`POSTve
      (λr. SEP_EXISTS d1 s1. NT_TABLE lim s1 tv *
        &(name_constr lim ca s = SOME (d1,s1) ∧
          NPBC_CHECK_CONSTR_TYPE NUM d1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_constr lim ca s = NONE))`
    >- (
      qpat_x_assum`∀lim s cv. NPBC_CHECK_CONSTR_TYPE _ ca cv ⇒ _` xapp_spec>>
      xsimpl)
    >- (xsimpl>>simp[name_constr_def]>>metis_tac[SEP_IMP_REFL])>>
    xlet`POSTve
      (λr. SEP_EXISTS d2 s2. NT_TABLE lim s2 tv *
        &(name_constr lim cb s1 = SOME (d2,s2) ∧
          NPBC_CHECK_CONSTR_TYPE NUM d2 r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_constr lim cb s1 = NONE))`
    >- (
      qpat_x_assum`∀lim s cv. NPBC_CHECK_CONSTR_TYPE _ cb cv ⇒ _` xapp_spec>>
      xsimpl)
    >- (xsimpl>>simp[name_constr_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_constr_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xsimpl)
  >~ [`Lit`]
  >- (
    rename1`name_constr lim (Lit l) s`>>
    xlet`POSTve
      (λr. SEP_EXISTS l1 s1. NT_TABLE lim s1 tv *
        &(name_lit lim l s = SOME (l1,s1) ∧ PBC_LIT_TYPE NUM l1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_lit lim l s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_constr_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_constr_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xsimpl)
  >~ [`Weak`]
  >- (
    rename1`name_constr lim (Weak c vs) s`>>
    xlet`POSTve
      (λr. SEP_EXISTS d1 s1. NT_TABLE lim s1 tv *
        &(name_constr lim c s = SOME (d1,s1) ∧
          NPBC_CHECK_CONSTR_TYPE NUM d1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_constr lim c s = NONE))`
    >- (xapp>>xsimpl)
    >- (xsimpl>>simp[name_constr_def]>>metis_tac[SEP_IMP_REFL])>>
    xlet`POSTve
      (λr. SEP_EXISTS ns s2. NT_TABLE lim s2 tv *
        &(name_vars lim vs s1 = SOME (ns,s2) ∧ LIST_TYPE NUM ns r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_vars lim vs s1 = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_constr_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_constr_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xsimpl)
  >~ [`Triv`]
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    qexists_tac`s`>>
    simp[name_constr_def,Fail_exn_def]>>
    xsimpl>>
    metis_tac[])
  >~ [`Lincomb`]
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    qexists_tac`s`>>
    simp[name_constr_def,Fail_exn_def]>>
    xsimpl>>
    metis_tac[])>>
  (* Mul, Div, Minus, Sat: one recursive call *)
  (
    xlet`POSTve
      (λr. SEP_EXISTS d1 s1. NT_TABLE lim s1 tv *
        &(name_constr lim c s = SOME (d1,s1) ∧
          NPBC_CHECK_CONSTR_TYPE NUM d1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_constr lim c s = NONE))`
    >- (xapp>>xsimpl)
    >- (xsimpl>>simp[name_constr_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_constr_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xsimpl)
QED

Theorem nt_subst_spec:
  ∀ss ssv s.
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE STRING_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE STRING_TYPE)))
    ss ssv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_subst" (get_ml_prog_state()))
    [tv; lnov; ssv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS ss1 s'. NT_TABLE lim s' tv *
        &(name_subst lim ss s = SOME (ss1,s') ∧ subst_raw_TYPE ss1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_subst lim ss s = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "nt_subst" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    simp[name_subst_def,LIST_TYPE_def]>>
    xsimpl)>>
  PairCases_on`h`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λr. SEP_EXISTS n s1. NT_TABLE lim s1 tv *
      &(res_var lim h0 s = SOME (n,s1) ∧ NUM n r))
    (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ res_var lim h0 s = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_subst_def]>>metis_tac[SEP_IMP_REFL])>>
  Cases_on`h1`>>
  gvs[SUM_TYPE_def]>>
  xmatch
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS ss1 s2. NT_TABLE lim s2 tv *
        &(name_subst lim ss s1 = SOME (ss1,s2) ∧ subst_raw_TYPE ss1 r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_subst lim ss s1 = NONE))`
    >- (xapp>>xsimpl)
    >- (xsimpl>>simp[name_subst_def]>>metis_tac[SEP_IMP_REFL])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    simp[name_subst_def,LIST_TYPE_def,PAIR_TYPE_def,SUM_TYPE_def]>>
    xsimpl)>>
  rename1`PBC_LIT_TYPE _ l lv`>>
  xlet`POSTve
    (λr. SEP_EXISTS l1 s2. NT_TABLE lim s2 tv *
      &(name_lit lim l s1 = SOME (l1,s2) ∧ PBC_LIT_TYPE NUM l1 r))
    (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
      &(Fail_exn e ∧ name_lit lim l s1 = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_subst_def]>>metis_tac[SEP_IMP_REFL])>>
  xlet`POSTve
    (λr. SEP_EXISTS ss1 s3. NT_TABLE lim s3 tv *
      &(name_subst lim ss s2 = SOME (ss1,s3) ∧ subst_raw_TYPE ss1 r))
    (λe. SEP_EXISTS s3. NT_TABLE lim s3 tv *
      &(Fail_exn e ∧ name_subst lim ss s2 = NONE))`
  >- (xapp>>xsimpl)
  >- (xsimpl>>simp[name_subst_def]>>metis_tac[SEP_IMP_REFL])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[name_subst_def,LIST_TYPE_def,PAIR_TYPE_def,SUM_TYPE_def]>>
  xsimpl
QED

Theorem nt_pbc_spec:
  NUM lno lnov ∧ pbc_TYPE STRING_TYPE c cv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_pbc" (get_ml_prog_state()))
    [tv; lnov; cv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS c1 s'. NT_TABLE lim s' tv *
        &(name_pbc lim c s = SOME (c1,s') ∧ pbc_TYPE NUM c1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_pbc lim c s = NONE)))
Proof
  rw[]>>
  xcf "nt_pbc" (get_ml_prog_state ())>>
  PairCases_on`c`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λr. SEP_EXISTS h1 s1. NT_TABLE lim s1 tv *
      &(name_pbhd lim c0 s = SOME (h1,s1) ∧ PBC_PBHD_TYPE NUM h1 r))
    (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ name_pbhd lim c0 s = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_pbc_def]>>metis_tac[SEP_IMP_REFL])>>
  xlet`POSTve
    (λr. SEP_EXISTS xs1 s2. NT_TABLE lim s2 tv *
      &(name_lin lim c1 s1 = SOME (xs1,s2) ∧ lin_TYPE NUM xs1 r))
    (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
      &(Fail_exn e ∧ name_lin lim c1 s1 = NONE))`
  >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
  >- (xsimpl>>simp[name_pbc_def]>>metis_tac[SEP_IMP_REFL])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[name_pbc_def,PAIR_TYPE_def]>>
  xsimpl
QED

Theorem nt_hconcl_spec:
  NUM lno lnov ∧ NPBC_CHECK_HCONCL_TYPE STRING_TYPE hc hcv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_hconcl" (get_ml_prog_state()))
    [tv; lnov; hcv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS hc1 s'. NT_TABLE lim s' tv *
        &(name_hconcl lim hc s = SOME (hc1,s') ∧
          NPBC_CHECK_HCONCL_TYPE NUM hc1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_hconcl lim hc s = NONE)))
Proof
  rw[]>>
  xcf "nt_hconcl" (get_ml_prog_state ())>>
  Cases_on`hc`>>
  gvs[NPBC_CHECK_HCONCL_TYPE_def]>>
  xmatch
  >~ [`HDSat ao`]
  >- (
    Cases_on`ao`>>
    gvs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xcon>>
      xsimpl>>
      simp[name_hconcl_def,NPBC_CHECK_HCONCL_TYPE_def,OPTION_TYPE_def]>>
      xsimpl)>>
    rename1`LIST_TYPE _ a asv`>>
    xlet`POSTve
      (λr. SEP_EXISTS a1 s1. NT_TABLE lim s1 tv *
        &(name_assg lim a s = SOME (a1,s1) ∧
          LIST_TYPE (PAIR_TYPE NUM BOOL) a1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_assg lim a s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_hconcl_def]>>metis_tac[SEP_IMP_REFL])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    simp[name_hconcl_def,NPBC_CHECK_HCONCL_TYPE_def,OPTION_TYPE_def]>>
    xsimpl)
  >~ [`HOBounds lb ub n ao`]
  >- (
    Cases_on`ao`>>
    gvs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xcon>>
      xsimpl>>
      simp[name_hconcl_def,NPBC_CHECK_HCONCL_TYPE_def,OPTION_TYPE_def]>>
      xsimpl)>>
    rename1`LIST_TYPE _ a asv`>>
    xlet`POSTve
      (λr. SEP_EXISTS a1 s1. NT_TABLE lim s1 tv *
        &(name_assg lim a s = SOME (a1,s1) ∧
          LIST_TYPE (PAIR_TYPE NUM BOOL) a1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_assg lim a s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_hconcl_def]>>metis_tac[SEP_IMP_REFL])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    simp[name_hconcl_def,NPBC_CHECK_HCONCL_TYPE_def,OPTION_TYPE_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[name_hconcl_def,NPBC_CHECK_HCONCL_TYPE_def]>>
  xsimpl
QED

Theorem nt_line_spec:
  NUM lno lnov ∧ PB_PARSE_PLINE_TYPE STRING_TYPE pl plv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_line" (get_ml_prog_state()))
    [tv; lnov; plv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS pl1 s'. NT_TABLE lim s' tv *
        &(name_pline lim pl s = SOME (pl1,s') ∧
          PB_PARSE_PLINE_TYPE NUM pl1 r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧ name_pline lim pl s = NONE)))
Proof
  rw[]>>
  xcf "nt_line" (get_ml_prog_state ())>>
  Cases_on`pl`>>
  gvs[PB_PARSE_PLINE_TYPE_def]
  >~ [`ObjuHd b p`]
  >- (
    PairCases_on`p`>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    xlet`POSTve
      (λr. SEP_EXISTS f1 s1. NT_TABLE lim s1 tv *
        &(name_lin lim p0 s = SOME (f1,s1) ∧ lin_TYPE NUM f1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_lin lim p0 s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def,PAIR_TYPE_def]>>
    xsimpl)
  >~ [`EObj p`]
  >- (
    PairCases_on`p`>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    xlet`POSTve
      (λr. SEP_EXISTS f1 s1. NT_TABLE lim s1 tv *
        &(name_lin lim p0 s = SOME (f1,s1) ∧ lin_TYPE NUM f1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_lin lim p0 s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def,PAIR_TYPE_def]>>
    xsimpl)>>
  xmatch
  >~ [`Pol c`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS c1 s1. NT_TABLE lim s1 tv *
        &(name_constr lim c s = SOME (c1,s1) ∧ NPBC_CHECK_CONSTR_TYPE NUM c1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_constr lim c s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`RedHd c ss`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS c1 s1. NT_TABLE lim s1 tv *
        &(name_pbc lim c s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_pbc lim c s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xlet`POSTve
      (λr. SEP_EXISTS ss1 s2. NT_TABLE lim s2 tv *
        &(name_subst lim ss s1 = SOME (ss1,s2) ∧ subst_raw_TYPE ss1 r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_subst lim ss s1 = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`DomHd c ss`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS c1 s1. NT_TABLE lim s1 tv *
        &(name_pbc lim c s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_pbc lim c s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xlet`POSTve
      (λr. SEP_EXISTS ss1 s2. NT_TABLE lim s2 tv *
        &(name_subst lim ss s1 = SOME (ss1,s2) ∧ subst_raw_TYPE ss1 r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_subst lim ss s1 = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`DelcHd n ss`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS ss1 s1. NT_TABLE lim s1 tv *
        &(name_subst lim ss s = SOME (ss1,s1) ∧ subst_raw_TYPE ss1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_subst lim ss s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`PresHd b x c`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS n s1. NT_TABLE lim s1 tv *
        &(res_var lim x s = SOME (n,s1) ∧ NUM n r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ res_var lim x s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xlet`POSTve
      (λr. SEP_EXISTS c1 s2. NT_TABLE lim s2 tv *
        &(name_pbc lim c s1 = SOME (c1,s2) ∧ pbc_TYPE NUM c1 r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_pbc lim c s1 = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`LoadOrd r ws`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS ws1 s1. NT_TABLE lim s1 tv *
        &(name_assg lim ws s = SOME (ws1,s1) ∧
          LIST_TYPE (PAIR_TYPE NUM BOOL) ws1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_assg lim ws s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`SolL a b ov`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS a1 s1. NT_TABLE lim s1 tv *
        &(name_assg lim a s = SOME (a1,s1) ∧
          LIST_TYPE (PAIR_TYPE NUM BOOL) a1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_assg lim a s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`SolxL a fr`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS a1 s1. NT_TABLE lim s1 tv *
        &(name_assg lim a s = SOME (a1,s1) ∧
          LIST_TYPE (PAIR_TYPE NUM BOOL) a1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_assg lim a s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xlet`POSTve
      (λr. SEP_EXISTS fr1 s2. NT_TABLE lim s2 tv *
        &(name_vars lim fr s1 = SOME (fr1,s2) ∧ LIST_TYPE NUM fr1 r))
      (λe. SEP_EXISTS s2. NT_TABLE lim s2 tv *
        &(Fail_exn e ∧ name_vars lim fr s1 = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  >~ [`EPres vs`]
  >- (
    xlet`POSTve
      (λr. SEP_EXISTS ns s1. NT_TABLE lim s1 tv *
        &(name_vars lim vs s = SOME (ns,s1) ∧ LIST_TYPE NUM ns r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_vars lim vs s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)
  (* PbcHd, RupL, CheckL, ImplyL: one constraint *)
  >>~- ([`pbc_TYPE STRING_TYPE _ _`],
    rename1`pbc_TYPE STRING_TYPE c _`>>
    xlet`POSTve
      (λr. SEP_EXISTS c1 s1. NT_TABLE lim s1 tv *
        &(name_pbc lim c s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 r))
      (λe. SEP_EXISTS s1. NT_TABLE lim s1 tv *
        &(Fail_exn e ∧ name_pbc lim c s = NONE))`
    >- (xapp>>xsimpl>>qexists_tac`lno`>>simp[])
    >- (xsimpl>>simp[name_pline_def]>>metis_tac[SEP_IMP_REFL])>>
    xcon>>
    xsimpl>>
    simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
    xsimpl)>>
  (* OrdHd, LDone, CDone: no names *)
  xcon>>
  xsimpl>>
  simp[name_pline_def,PB_PARSE_PLINE_TYPE_def]>>
  xsimpl
QED

(*
  The proof readers. Each reads lines from fd, numbering their names with
  the table tv, and returns the line number after the last line read;
  a line that is not of the reader's kind is returned unnumbered.
*)
Quote add_cakeml:
  fun parse_lsteps_aux tv fd lno acc =
    case input_toks fd of
      None => raise Fail (format_failure lno "reached EOF while reading PBP steps")
    | Some s =>
    case parse_line s of
      None => (List.rev acc, (s, lno+1))
    | Some pl =>
      if is_lstep pl then
        (case nt_line tv lno pl of
          Pbchd c =>
          (case mk_npbc c of
            None => raise Fail (format_failure lno "constraint has no single normal form")
          | Some c1 =>
            case parse_lsteps_aux tv fd (lno+1) [] of
              (pf,(s',lno')) =>
              case check_mark_qed_id_pbc s' of
                None => raise Fail (format_failure (sub_one lno') "subproof not terminated with contradiction id")
              | Some id => parse_lsteps_aux tv fd lno' (Con c1 pf id::acc))
        | pl1 =>
          (case fin_lstep pl1 of
            None => raise Fail (format_failure lno "constraint has no single normal form")
          | Some step => parse_lsteps_aux tv fd (lno+1) (step::acc)))
      else (List.rev acc, (s, lno+1))
End

Theorem parse_lsteps_aux_spec:
  ∀lim s ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE acc accv ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsteps_aux" (get_ml_prog_state()))
    [tv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s' l lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(PAIR_TYPE (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)
             (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
           parse_lsteps_aux lim s ss acc = SOME (acc',s',l,rest) ∧
           MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_lsteps_aux lim s ss acc = NONE)))
Proof
  ho_match_mp_tac parse_lsteps_aux_ind>>
  rw[]
  >- (
    xcf "parse_lsteps_aux" (get_ml_prog_state ())>>
    xlet ‘(POSTv v.
        SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
          NT_TABLE lim s tv *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac[‘NT_TABLE lim s tv’,‘[]’]>>
      xsimpl>>
      metis_tac[SEP_IMP_REFL,SEP_IMP_REFL_gc])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[parse_lsteps_aux_thm,Fail_exn_def]>>
    qexistsl_tac[`k`,`[]`,`s`]>>
    xsimpl>>
    metis_tac[])>>
  xcfs ["parse_lsteps_aux"] (get_ml_prog_state ())>>
  `∃ln lns. lines = ln::lns` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
            NT_TABLE lim s tv *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks ln)) v)’
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac[‘NT_TABLE lim s tv’,‘ln::lns’,‘fs’,‘fd’]>>
    xsimpl>>
    rw[]>>
    qexists_tac‘x’>>
    xsimpl>>
    simp[toks_def])>>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  simp[Once parse_lsteps_aux_thm]>>
  Cases_on`parse_line (toks ln)`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lns`,`lno + 1`]>>
    simp[PAIR_TYPE_def]>>
    xsimpl)>>
  rename1`parse_line (toks ln) = SOME pl`>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lns`,`lno + 1`]>>
    simp[PAIR_TYPE_def]>>
    xsimpl)>>
  xlet`POSTve
    (λv. SEP_EXISTS pl1 s1.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(name_pline lim pl s = SOME (pl1,s1) ∧ PB_PARSE_PLINE_TYPE NUM pl1 v))
    (λe. SEP_EXISTS s1.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ name_pline lim pl s = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k)`,
                 `s`,`pl`,`lim`,`lno`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim t tv ==>> _`>>
    qexists_tac`t`>>
    xsimpl)
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_lsteps_aux_thm]>>
    qexistsl_tac[`k`,`lns`]>>
    xsimpl>>
    metis_tac[SEP_IMP_REFL])>>
  Cases_on`pl1`>>
  qpat_assum`PB_PARSE_PLINE_TYPE NUM _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [PB_PARSE_PLINE_TYPE_def])>>
  xmatch
  >~ [`PbcHd c`]
  >- (
    rveq>>
    xlet_autop>>
    TOP_CASE_TAC>>
    qpat_x_assum`OPTION_TYPE _ _ _` mp_tac>>
    simp[OPTION_TYPE_def]>>
    strip_tac>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def,Once parse_lsteps_aux_thm]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    rpt xlet_autop>>
    rename1`mk_npbc c = SOME c1`>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 acc2 s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE (LIST_TYPE NPBC_CHECK_LSTEP_TYPE) (PAIR_TYPE line_TYPE NUM)
             (acc2,l2,lno2) v ∧
           parse_lsteps_aux lim s1 (MAP toks lns) [] = SOME (acc2,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k2 lines2 s2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(Fail_exn e ∧ parse_lsteps_aux lim s1 (MAP toks lns) [] = NONE))`
    >- (
      qpat_x_assum`∀s'' c c1. _`
        (drule_then (drule_then (drule_then assume_tac)))>>
      xapp>>
      qexistsl_tac[`emp`,`lns`,`forwardFD fs fd k`,`fd`]>>
      xsimpl>>
      qexists_tac`lno + 1`>>
      simp[LIST_TYPE_def,forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      simp[Once parse_lsteps_aux_thm]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    Cases_on`check_mark_qed_id_pbc l2`>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def,Once parse_lsteps_aux_thm]>>
      fs[check_mark_qed_id_pbc_def]>>
      rw[]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    imp_res_tac parse_lsteps_aux_LENGTH>>
    fs[check_mark_qed_id_pbc_def]>>
    rpt xlet_autop>>
    qpat_x_assum
      `∀fd fdv lines lno' lnov' accv' fs. _ ∧ LIST_TYPE _ (Con _ _ _::_) _ ∧ _ ⇒ _`
      xapp_spec>>
    qexistsl_tac[`emp`,`lines2`,`forwardFD fs fd (k + k2)`,`fd`]>>
    xsimpl>>
    qexists_tac`lno2`>>
    simp[LIST_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,forwardFD_o]>>
    rw[]>>
    simp[Once parse_lsteps_aux_thm]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  (* every other numbered line is finished by fin_lstep *)
  (
    rveq>>
    xlet_autop>>
    TOP_CASE_TAC>>
    qpat_x_assum`OPTION_TYPE _ _ _` mp_tac>>
    simp[OPTION_TYPE_def]>>
    strip_tac>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def,Once parse_lsteps_aux_thm]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    rpt xlet_autop>>
    first_x_assum (drule_then (drule_then (drule_then assume_tac)))>>
    xapp>>
    qexistsl_tac[`emp`,`lns`,`forwardFD fs fd k`,`fd`]>>
    xsimpl>>
    qexists_tac`lno + 1`>>
    simp[LIST_TYPE_def,forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    simp[Once parse_lsteps_aux_thm]>>
    metis_tac[SEP_IMP_REFL_gc])
QED

Quote add_cakeml:
  fun parse_lsteps tv fd lno =
    parse_lsteps_aux tv fd lno []
End

Theorem parse_lsteps_spec:
  NUM lno lnov ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsteps" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s' l lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(PAIR_TYPE (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)
             (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
           parse_lsteps lim s ss = SOME (acc',s',l,rest) ∧
           MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_lsteps lim s ss = NONE)))
Proof
  rw[parse_lsteps_def]>>
  xcf "parse_lsteps" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp_spec parse_lsteps_aux_spec>>
  xsimpl>>
  simp[LIST_TYPE_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun parse_subproof_aux tv fd lno acc =
    case parse_lsteps tv fd lno of
      (pf,(s,lno')) =>
      let val acc' = mk_acc pf acc in
        case parse_proofgoal s of
          None => (List.rev acc', (s, lno'))
        | Some ind =>
          (case parse_lsteps tv fd lno' of
            (pf,(s,lno'')) =>
            case check_mark_qed_id (mk_proofgoal_mark ind) s of
              None => raise Fail (format_failure (sub_one lno'') "subproof not terminated with contradiction id")
            | Some id =>
              parse_subproof_aux tv fd lno'' ((Some (ind,id),pf)::acc'))
      end
End

Theorem parse_subproof_aux_spec:
  ∀lim s ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  pfs_TYPE acc accv ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_subproof_aux" (get_ml_prog_state()))
    [tv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s' l lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
           parse_subproof_aux lim s ss acc = SOME (acc',s',l,rest) ∧
           MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_subproof_aux lim s ss acc = NONE)))
Proof
  ho_match_mp_tac parse_subproof_aux_ind>>
  rw[]>>
  xcf "parse_subproof_aux" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv.
       SEP_EXISTS k lines' acc' s1 l lno' rest.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s1 tv *
       &(PAIR_TYPE (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)
           (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
         parse_lsteps lim s (MAP toks lines) = SOME (acc',s1,l,rest) ∧
         MAP toks lines' = rest))
    (λe.
       SEP_EXISTS k lines' s1.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s1 tv *
       &(Fail_exn e ∧ parse_lsteps lim s (MAP toks lines) = NONE))`
  >- (
    xapp>>
    xsimpl>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_subproof_aux_def]>>
    metis_tac[SEP_IMP_REFL])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  rpt xlet_autop>>
  simp[Once parse_subproof_aux_def]>>
  namedCases_on`parse_proofgoal l`["","ind"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lines'`,`lno'`]>>
    xsimpl)>>
  xlet`POSTve
    (λv.
       SEP_EXISTS k2 lines2 acc2 s2 l2 lno2 rest2.
       STDIO (forwardFD fs fd (k + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
       NT_TABLE lim s2 tv *
       &(PAIR_TYPE (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)
           (PAIR_TYPE line_TYPE NUM) (acc2,l2,lno2) v ∧
         parse_lsteps lim s1 (MAP toks lines') = SOME (acc2,s2,l2,rest2) ∧
         MAP toks lines2 = rest2))
    (λe.
       SEP_EXISTS k2 lines2 s2.
       STDIO (forwardFD fs fd (k + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
       NT_TABLE lim s2 tv *
       &(Fail_exn e ∧ parse_lsteps lim s1 (MAP toks lines') = NONE))`
  >- (
    xapp_spec parse_lsteps_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s1`,`lines'`,`lim`,`forwardFD fs fd k`,`fd`,`lno'`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_subproof_aux_def]>>
    metis_tac[SEP_IMP_REFL])
  >- (
    rveq>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    namedCases_on`check_mark_qed_id (mk_proofgoal_mark ind) l2`["","id"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def,Once parse_subproof_aux_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xapp>>
    qexistsl_tac[`emp`,`lines2`,`forwardFD fs fd (k + k2)`,`fd`]>>
    xsimpl>>
    qexists_tac`lno2`>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,forwardFD_o]>>
    rw[]>>
    simp[Once parse_subproof_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])
QED

Quote add_cakeml:
  fun parse_subproof_imp tv fd lno =
    parse_subproof_aux tv fd lno []
End

Theorem parse_subproof_imp_spec:
  NUM lno lnov ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_subproof_imp" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s' l lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
           parse_subproof lim s ss = SOME (acc',s',l,rest) ∧
           MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_subproof lim s ss = NONE)))
Proof
  rw[parse_subproof_def]>>
  xcf "parse_subproof_imp" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp_spec parse_subproof_aux_spec>>
  xsimpl>>
  simp[LIST_TYPE_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun parse_scope_aux tv fd lno acc =
    case parse_subproof_imp tv fd lno of
      (pf,(s,lno')) =>
      let val acc' = mk_acc pf acc in
        case parse_scopehead s of
          None => (List.rev acc', (s, lno'))
        | Some ind =>
          (case parse_subproof_imp tv fd lno' of
            (pf,(s,lno'')) =>
            if check_end (mk_scope_mark ind) s
            then
              parse_scope_aux tv fd lno'' ((Some ind,pf)::acc')
            else
              raise Fail (format_failure (sub_one lno'') "scope not terminated with end (no id allowed)"))
      end
End

Theorem parse_scope_aux_spec:
  ∀lim s ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  scpfs_TYPE acc accv ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_scope_aux" (get_ml_prog_state()))
    [tv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s' l lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(PAIR_TYPE scpfs_TYPE (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
           parse_scope_aux lim s ss acc = SOME (acc',s',l,rest) ∧
           MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_scope_aux lim s ss acc = NONE)))
Proof
  ho_match_mp_tac parse_scope_aux_ind>>
  rw[]>>
  xcf "parse_scope_aux" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv.
       SEP_EXISTS k lines' acc' s1 l lno' rest.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s1 tv *
       &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
         parse_subproof lim s (MAP toks lines) = SOME (acc',s1,l,rest) ∧
         MAP toks lines' = rest))
    (λe.
       SEP_EXISTS k lines' s1.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s1 tv *
       &(Fail_exn e ∧ parse_subproof lim s (MAP toks lines) = NONE))`
  >- (
    xapp>>
    xsimpl>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_scope_aux_def]>>
    metis_tac[SEP_IMP_REFL])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    irule EqualityType_PAIR_TYPE>>
    simp (eq_lemmas())>>
    irule EqualityType_LIST_TYPE>>
    simp (eq_lemmas()))>>
  rpt xlet_autop>>
  simp[Once parse_scope_aux_def]>>
  namedCases_on`parse_scopehead l`["","ind"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lines'`,`lno'`]>>
    xsimpl)>>
  xlet`POSTve
    (λv.
       SEP_EXISTS k2 lines2 acc2 s2 l2 lno2 rest2.
       STDIO (forwardFD fs fd (k + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
       NT_TABLE lim s2 tv *
       &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (acc2,l2,lno2) v ∧
         parse_subproof lim s1 (MAP toks lines') = SOME (acc2,s2,l2,rest2) ∧
         MAP toks lines2 = rest2))
    (λe.
       SEP_EXISTS k2 lines2 s2.
       STDIO (forwardFD fs fd (k + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
       NT_TABLE lim s2 tv *
       &(Fail_exn e ∧ parse_subproof lim s1 (MAP toks lines') = NONE))`
  >- (
    xapp_spec parse_subproof_imp_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s1`,`lines'`,`lim`,`forwardFD fs fd k`,`fd`,`lno'`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_scope_aux_def]>>
    metis_tac[SEP_IMP_REFL])>>
  rveq>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTv v.
    STDIO (forwardFD fs fd (k + k2)) *
    INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
    NT_TABLE lim s2 tv *
    &line_TYPE (mk_scope_mark ind) v`
  >- (
    xapp_spec
      (INST_TYPE [alpha |-> ``:int``] (fetch "-" "mk_scope_mark_v_thm"))>>
    xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def,Once parse_scope_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  xapp>>
  qexistsl_tac[`emp`,`lines2`,`forwardFD fs fd (k + k2)`,`fd`]>>
  xsimpl>>
  qexists_tac`lno2`>>
  simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,forwardFD_o]>>
  rw[]>>
  simp[Once parse_scope_aux_def]>>
  metis_tac[SEP_IMP_REFL_gc]
QED

Quote add_cakeml:
  fun parse_scope_imp tv fd lno =
    parse_scope_aux tv fd lno []
End

Theorem parse_scope_imp_spec:
  NUM lno lnov ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_scope_imp" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s' l lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(PAIR_TYPE scpfs_TYPE (PAIR_TYPE line_TYPE NUM) (acc',l,lno') v ∧
           parse_scope lim s ss = SOME (acc',s',l,rest) ∧
           MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_scope lim s ss = NONE)))
Proof
  rw[parse_scope_def]>>
  xcf "parse_scope_imp" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp_spec parse_scope_aux_spec>>
  xsimpl>>
  simp[LIST_TYPE_def]>>
  metis_tac[]
QED

Definition check_mark_qed_id_opt_red_def:
  check_mark_qed_id_opt_red s = check_mark_qed_id_opt (INL «red») s
End

val r = translate check_mark_qed_id_opt_red_def;

Definition check_mark_qed_id_opt_dom_def:
  check_mark_qed_id_opt_dom s = check_mark_qed_id_opt (INL «dom») s
End

val r = translate check_mark_qed_id_opt_dom_def;

Definition check_mark_qed_id_opt_delc_def:
  check_mark_qed_id_opt_delc s = check_mark_qed_id_opt (INL «delc») s
End

val r = translate check_mark_qed_id_opt_delc_def;

Definition check_mark_qed_id_opt_obju_def:
  check_mark_qed_id_opt_obju s = check_mark_qed_id_opt (INL «obju») s
End

val r = translate check_mark_qed_id_opt_obju_def;

Definition check_mark_qed_id_opt_preserve_def:
  check_mark_qed_id_opt_preserve b s =
    check_mark_qed_id_opt
      (if b then INL «preserved_add» else INL «preserved_rm») s
End

val r = translate check_mark_qed_id_opt_preserve_def;

(*
  The order block of a def_order step, read one line at a time
  (parse_pre_order)
*)
val r = translate parse_cmp_deg_def;
val r = translate parse_constraint_ns_def;

Quote add_cakeml:
  fun read_toks lno fd =
    case input_toks fd of
      None => raise Fail (format_failure lno "reached EOF while reading an order definition")
    | Some l => l
End

Quote add_cakeml:
  fun parse_vars_line_arr tv lno kw l =
    case parse_vars_line kw l of
      None => raise Fail (format_failure lno ("expected a line of variables starting with " ^ kw))
    | Some vs => nt_vars tv lno vs
End

Quote add_cakeml:
  fun parse_vars_block_arr tv fd lno =
    let
      val v = read_toks lno fd
      val l = read_toks (lno+1) fd
      val r = read_toks (lno+2) fd
      val ae = read_toks (lno+3) fd
    in
      if v = [Inl "vars"] then
        let
          val us = parse_vars_line_arr tv (lno+1) "left" l
          val vs = parse_vars_line_arr tv (lno+2) "right" r
        in
          if check_end [Inl "vars"] ae then ((us,(vs,[])), lno+4)
          else
            let
              val aux = parse_vars_line_arr tv (lno+3) "aux" ae
              val e = read_toks (lno+4) fd
            in
              if check_end [Inl "vars"] e then ((us,(vs,aux)), lno+5)
              else raise Fail (format_failure (lno+4) "expected the end of a vars block")
            end
        end
      else raise Fail (format_failure lno "expected a vars block")
    end
End

Quote add_cakeml:
  fun parse_spec_aux_arr tv fd lno acc =
    let val l = read_toks lno fd in
      case parse_line l of
        Some (Redhd c ss) =>
        let
          val c1 = nt_pbc tv lno c
          val ss1 = nt_subst tv lno ss
        in
          case mk_npbc c1 of
            None => raise Fail (format_failure lno "constraint has no single normal form")
          | Some c2 =>
            case parse_scope_imp tv fd (lno+1) of
              (pf,(h,lno')) =>
              case check_mark_qed_id_opt_red h of
                None => raise Fail (format_failure (sub_one lno') "Incorrectly terminated redundancy step")
              | Some idopt =>
                parse_spec_aux_arr tv fd lno' ((c2,(ss1,(pf,idopt)))::acc)
        end
      | _ =>
        if check_end [Inl "spec"] l then (List.rev acc, lno+1)
        else raise Fail (format_failure lno "expected a red step or the end of a spec block")
    end
End

Quote add_cakeml:
  fun parse_spec_block_arr tv fd lno =
    let val h = read_toks lno fd in
      if h = [Inl "spec"] then
        (case parse_spec_aux_arr tv fd (lno+1) [] of
          (spec, lno') =>
          let val h1 = read_toks lno' fd in
            if h1 = [Inl "def"] then (spec, lno'+1)
            else raise Fail (format_failure lno' "expected a def block")
          end)
      else if h = [Inl "def"] then ([], lno+1)
      else raise Fail (format_failure lno "expected a spec or def block")
    end
End

Quote add_cakeml:
  fun parse_def_aux_arr tv fd lno acc =
    let val l = read_toks lno fd in
      if check_end [Inl "def"] l then (List.rev acc, lno+1)
      else
        case parse_constraint_ns l of
          None => raise Fail (format_failure lno "expected a constraint or the end of a def block")
        | Some c =>
          case mk_npbc (nt_pbc tv lno c) of
            None => raise Fail (format_failure lno "constraint has no single normal form")
          | Some c2 => parse_def_aux_arr tv fd (lno+1) (c2::acc)
    end
End

val res = translate trans_vars_head_def;

Quote add_cakeml:
  fun parse_trans_vars_arr tv fd lno =
    let
      val h = read_toks lno fd
      val v = read_toks (lno+1) fd
      val f = read_toks (lno+2) fd
      val ae = read_toks (lno+3) fd
    in
      if trans_vars_head h v then
        let val ws = parse_vars_line_arr tv (lno+2) "fresh_right" f in
          if check_end [Inl "vars"] ae then ((ws,([],[])), lno+4)
          else
            let
              val bs = parse_vars_line_arr tv (lno+3) "fresh_aux_1" ae
              val a2 = read_toks (lno+4) fd
              val e = read_toks (lno+5) fd
              val cs = parse_vars_line_arr tv (lno+4) "fresh_aux_2" a2
            in
              if check_end [Inl "vars"] e then ((ws,(bs,cs)), lno+6)
              else raise Fail (format_failure (lno+5) "expected the end of a vars block")
            end
        end
      else raise Fail (format_failure lno "expected a transitivity block")
    end
End

Quote add_cakeml:
  fun parse_proof_block_arr tv fd lno mark =
    let val h = read_toks lno fd in
      if h = [Inl "proof"] then
        case parse_subproof_imp tv fd (lno+1) of
          (pf,(s,lno')) =>
          if check_qed [Inl "proof"] s then
            let val e = read_toks lno' fd in
              if check_end mark e then (pf, lno'+1)
              else raise Fail (format_failure lno' "expected the end of a proof block")
            end
          else raise Fail (format_failure (sub_one lno') "expected qed proof")
      else raise Fail (format_failure lno "expected a proof block")
    end
End

Quote add_cakeml:
  fun parse_trans_block_arr tv fd lno =
    case parse_trans_vars_arr tv fd lno of
      ((ws,(bs,cs)),lno1) =>
      case parse_proof_block_arr tv fd lno1 [Inl "transitivity"] of
        (pf,lno2) => ((ws,(bs,(cs,pf))),lno2)
End

Quote add_cakeml:
  fun parse_refl_block_arr tv fd lno =
    let val h = read_toks lno fd in
      if h = [Inl "reflexivity"] then
        parse_proof_block_arr tv fd (lno+1) [Inl "reflexivity"]
      else raise Fail (format_failure lno "expected a reflexivity block")
    end
End

Theorem read_toks_spec:
  NUM lno lnov ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_toks" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv. SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
         &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
      (λe. SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
         &(Fail_exn e ∧ lines = [])))
Proof
  rw[]>>
  xcf "read_toks" (get_ml_prog_state ())>>
  xlet`POSTv v. SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
         &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
           (OPTION_MAP toks (oHD lines)) v`
  >- (xapp_spec input_toks_spec>>xsimpl)>>
  Cases_on`lines`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  xvar>>
  xsimpl>>
  metis_tac[SEP_IMP_REFL_gc]
QED

Theorem parse_vars_line_arr_spec:
  NUM lno lnov ∧ STRING_TYPE kw kwv ∧ line_TYPE l lv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_vars_line_arr" (get_ml_prog_state()))
    [tv; lnov; kwv; lv]
    (NT_TABLE lim s tv)
    (POSTve
      (λr. SEP_EXISTS vs ns s'. NT_TABLE lim s' tv *
        &(parse_vars_line kw l = SOME vs ∧
          name_vars lim vs s = SOME (ns,s') ∧ LIST_TYPE NUM ns r))
      (λe. SEP_EXISTS s'. NT_TABLE lim s' tv *
        &(Fail_exn e ∧
          ∀vs. parse_vars_line kw l = SOME vs ⇒ name_vars lim vs s = NONE)))
Proof
  rw[]>>
  xcf "parse_vars_line_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  namedCases_on`parse_vars_line kw l`["","vs"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    qexists_tac`s`>>
    simp[Fail_exn_def]>>
    conj_tac
    >- metis_tac[]>>
    xsimpl)>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`vs`,`s`,`lim`,`lno`]>>
  xsimpl>>
  rw[]>>
  rename1`NT_TABLE lim s1 tv ==>> _`>>
  qexists_tac`s1`>>
  xsimpl
QED

Theorem line_TYPE_keyword[local] =
  SIMP_CONV (srw_ss()) [LIST_TYPE_def,SUM_TYPE_def,STRING_TYPE_def]
    ``line_TYPE [INL kw] v``
  |> iffRL |> Q.GEN `v` |> SIMP_RULE bool_ss [] |> Q.GEN `kw`;

Overload "vars3_TYPE" = ``
  PAIR_TYPE (LIST_TYPE NUM) (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM))``

Theorem parse_vars_block_arr_spec:
  NUM lno lnov ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_vars_block_arr" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' vars s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_vars_block lim s ss = SOME (vars,s',rest) ∧
           PAIR_TYPE vars3_TYPE NUM (vars,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_vars_block lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_vars_block_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k1.
      STDIO (forwardFD fs fd k1) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k1) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_vars_block lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_vars_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln1 lns1. lines = ln1::lns1` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k2.
      STDIO (forwardFD fs fd (k1 + k2)) *
      INSTREAM_LINES #"\n" fd fdv (TL lns1) (forwardFD fs fd (k1 + k2)) *
      NT_TABLE lim s tv *
      &(lns1 ≠ [] ∧ line_TYPE (toks (HD lns1)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_vars_block lim s (MAP toks (ln1::lns1)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lns1`,`forwardFD fs fd k1`,`fd`,
                 `lno + 1`]>>
    xsimpl>>
    rw[]>>
    simp[parse_vars_block_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln2 lns2. lns1 = ln2::lns2` by (Cases_on`lns1`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k3.
      STDIO (forwardFD fs fd (k1 + k2 + k3)) *
      INSTREAM_LINES #"\n" fd fdv (TL lns2)
        (forwardFD fs fd (k1 + k2 + k3)) *
      NT_TABLE lim s tv *
      &(lns2 ≠ [] ∧ line_TYPE (toks (HD lns2)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_vars_block lim s (MAP toks (ln1::ln2::lns2)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lns2`,`forwardFD fs fd (k1 + k2)`,
                 `fd`,`lno + 2`]>>
    xsimpl>>
    rw[]>>
    simp[parse_vars_block_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln3 lns3. lns2 = ln3::lns3` by (Cases_on`lns2`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k4.
      STDIO (forwardFD fs fd (k1 + k2 + k3 + k4)) *
      INSTREAM_LINES #"\n" fd fdv (TL lns3)
        (forwardFD fs fd (k1 + k2 + k3 + k4)) *
      NT_TABLE lim s tv *
      &(lns3 ≠ [] ∧ line_TYPE (toks (HD lns3)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_vars_block lim s (MAP toks (ln1::ln2::ln3::lns3)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lns3`,
                 `forwardFD fs fd (k1 + k2 + k3)`,`fd`,`lno + 3`]>>
    xsimpl>>
    rw[]>>
    simp[parse_vars_block_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln4 rest. lns3 = ln4::rest` by (Cases_on`lns3`>>fs[])>>
  gvs[]>>
  rpt xlet_autop>>
  gvs[]>>
  assume_tac (Q.SPEC`«vars»` line_TYPE_keyword)>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def,parse_vars_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS us us1 s1.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      INSTREAM_LINES #"\n" fd fdv rest
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      NT_TABLE lim s1 tv *
      &(parse_vars_line «left» (toks ln2) = SOME us ∧
        name_vars lim us s = SOME (us1,s1) ∧ LIST_TYPE NUM us1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_vars_block lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
       INSTREAM_LINES #"\n" fd fdv rest
         (forwardFD fs fd (k1 + (k2 + (k3 + k4))))`,
      `s`,`lim`,`toks ln2`,`lno + 1`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s1 tv * _`>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`s1`]>>
    xsimpl>>
    simp[parse_vars_block_def]>>
    Cases_on`parse_vars_line «left» (toks ln2)`>>
    gvs[])
  >- xsimpl>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS vs vs1 s2.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      INSTREAM_LINES #"\n" fd fdv rest
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      NT_TABLE lim s2 tv *
      &(parse_vars_line «right» (toks ln3) = SOME vs ∧
        name_vars lim vs s1 = SOME (vs1,s2) ∧ LIST_TYPE NUM vs1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_vars_block lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
       INSTREAM_LINES #"\n" fd fdv rest
         (forwardFD fs fd (k1 + (k2 + (k3 + k4))))`,
      `s1`,`lim`,`toks ln3`,`lno + 2`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s2 tv * _`>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`s2`]>>
    xsimpl>>
    simp[parse_vars_block_def]>>
    Cases_on`parse_vars_line «right» (toks ln3)`>>
    gvs[])
  >- xsimpl>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`(us1,vs1,[])`,`s2`,`lno + 4`]>>
    xsimpl>>
    simp[parse_vars_block_def,PAIR_TYPE_def,LIST_TYPE_def])>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS as as1 s3.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      INSTREAM_LINES #"\n" fd fdv rest
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      NT_TABLE lim s3 tv *
      &(parse_vars_line «aux» (toks ln4) = SOME as ∧
        name_vars lim as s2 = SOME (as1,s3) ∧ LIST_TYPE NUM as1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_vars_block lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
       INSTREAM_LINES #"\n" fd fdv rest
         (forwardFD fs fd (k1 + (k2 + (k3 + k4))))`,
      `s2`,`lim`,`toks ln4`,`lno + 3`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s3 tv * _`>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`s3`]>>
    xsimpl>>
    simp[parse_vars_block_def]>>
    Cases_on`parse_vars_line «aux» (toks ln4)`>>
    gvs[])
  >- xsimpl>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k5.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)) + k5)) *
      INSTREAM_LINES #"\n" fd fdv (TL rest)
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)) + k5)) *
      NT_TABLE lim s3 tv *
      &(rest ≠ [] ∧ line_TYPE (toks (HD rest)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_vars_block lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s3 tv`,`rest`,
                 `forwardFD fs fd (k1 + (k2 + (k3 + k4)))`,`fd`,`lno + 4`]>>
    xsimpl>>
    rw[]>>
    gvs[parse_vars_block_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln5 rest1. rest = ln5::rest1` by (Cases_on`rest`>>fs[])>>
  gvs[]>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def,parse_vars_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  qexistsl_tac[`k1 + (k2 + (k3 + (k4 + k5)))`,`rest1`,`(us1,vs1,as1)`,`s3`,
               `lno + 5`]>>
  xsimpl>>
  gvs[parse_vars_block_def,PAIR_TYPE_def]
QED

Overload "gspec_TYPE" = ``
  LIST_TYPE
    (PAIR_TYPE constraint_TYPE
       (PAIR_TYPE subst_raw_TYPE (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM))))``

Theorem parse_spec_aux_arr_spec:
  ∀lim s ss acc accv fd fdv lines lno lnov fs.
  NUM lno lnov ∧ gspec_TYPE acc accv ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_spec_aux_arr" (get_ml_prog_state()))
    [tv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' spec s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_spec_aux lim s ss acc = SOME (spec,s',rest) ∧
           PAIR_TYPE gspec_TYPE NUM (spec,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_spec_aux lim s ss acc = NONE)))
Proof
  completeInduct_on`LENGTH (lines:mlstring list)`>>
  rw[]>>
  xcf "parse_spec_aux_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_spec_aux lim s (MAP toks lines) acc = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_spec_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln lns. lines = ln::lns` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  simp[Once parse_spec_aux_def]>>
  namedCases_on`parse_line (toks ln)`["","pl"]>>
  fs[OPTION_TYPE_def]>>>
  NTH_GOAL (Cases_on`pl`>>fs[PB_PARSE_PLINE_TYPE_def]) 2
  >~ [`RedHd c ss`]
  >- (
    xmatch>>
    xlet`POSTve
      (λv. SEP_EXISTS c1 s1.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
        NT_TABLE lim s1 tv *
        &(name_pbc lim c s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 v))
      (λe. SEP_EXISTS k lines' s'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
        NT_TABLE lim s' tv *
        &(Fail_exn e ∧ parse_spec_aux lim s (MAP toks (ln::lns)) acc = NONE))`
    >- (
      xapp>>
      xsimpl>>
      qexistsl_tac[
        `STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k)`,
        `s`,`lim`,`c`,`lno`]>>
      xsimpl>>
      rw[]>>
      rename1`NT_TABLE lim s1 tv * _`>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      gvs[Once parse_spec_aux_def])
    >- xsimpl>>
    xlet`POSTve
      (λv. SEP_EXISTS ss1 s2.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
        NT_TABLE lim s2 tv *
        &(name_subst lim ss s1 = SOME (ss1,s2) ∧ subst_raw_TYPE ss1 v))
      (λe. SEP_EXISTS k lines' s'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
        NT_TABLE lim s' tv *
        &(Fail_exn e ∧ parse_spec_aux lim s (MAP toks (ln::lns)) acc = NONE))`
    >- (
      xapp>>
      xsimpl>>
      qexistsl_tac[
        `STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k)`,
        `ss`,`s1`,`lim`,`lno`]>>
      xsimpl>>
      rw[]>>
      rename1`NT_TABLE lim s2 tv * _`>>
      qexistsl_tac[`k`,`lns`,`s2`]>>
      xsimpl>>
      gvs[Once parse_spec_aux_def])
    >- xsimpl>>
    xlet_autop>>
    namedCases_on`mk_npbc c1`["","c2"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      fs[Fail_exn_def,Once parse_spec_aux_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s3 l3 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s3 tv *
         &(PAIR_TYPE scpfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l3,lno2) v ∧
           parse_scope lim s2 (MAP toks lns) = SOME (pf,s3,l3,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_spec_aux lim s (MAP toks (ln::lns)) acc = NONE))`
    >- (
      xapp_spec parse_scope_imp_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s2`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      gvs[Once parse_spec_aux_def]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- xsimpl>>
    `LENGTH lines2 < LENGTH lns` by (
      gvs[parse_scope_def]>>
      drule parse_scope_aux_LENGTH>>
      simp[])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id_opt (INL «red») l3`["","idopt"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_opt_red_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      fs[Fail_exn_def,Once parse_spec_aux_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    qpat_x_assum`∀m. _`(qspec_then`LENGTH lines2` mp_tac)>>
    impl_tac
    >- simp[]>>
    disch_then (qspec_then`lines2` mp_tac)>>
    simp[]>>
    strip_tac>>
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`s3`,`lim`,`forwardFD fs fd (k + k2)`,`fd`,
                 `(c2,ss1,pf,idopt)::acc`,`lno2`]>>
    xsimpl>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[Once parse_spec_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  (
    xmatch>>
    assume_tac (Q.SPEC`«spec»` line_TYPE_keyword)>>
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      fs[Fail_exn_def,Once parse_spec_aux_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lns`,`lno + 1`]>>
    xsimpl>>
    simp[PAIR_TYPE_def])
QED

Theorem parse_spec_block_arr_spec:
  NUM lno lnov ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_spec_block_arr" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' spec s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_spec_block lim s ss = SOME (spec,s',rest) ∧
           PAIR_TYPE gspec_TYPE NUM (spec,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_spec_block lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_spec_block_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_spec_block lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_spec_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln lns. lines = ln::lns` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  assume_tac (Q.SPEC`«spec»` line_TYPE_keyword)>>
  assume_tac (Q.SPEC`«def»` line_TYPE_keyword)>>
  rpt xlet_autop>>
  gvs[]>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  xif
  >- (
    rpt xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 spec s1 rest1 lno2.
        STDIO (forwardFD fs fd (k + k2)) *
        INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
        NT_TABLE lim s1 tv *
        &(parse_spec_aux lim s (MAP toks lns) [] = SOME (spec,s1,rest1) ∧
          PAIR_TYPE gspec_TYPE NUM (spec,lno2) v ∧
          MAP toks lines2 = rest1))
      (λe. SEP_EXISTS k lines' s'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
        NT_TABLE lim s' tv *
        &(Fail_exn e ∧ parse_spec_block lim s (MAP toks (ln::lns)) = NONE))`
    >- (
      xapp_spec parse_spec_aux_arr_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`[]`,
                   `lno + 1`]>>
      xsimpl>>
      simp[LIST_TYPE_def,forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      simp[parse_spec_block_def]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- xsimpl>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet`POSTve
      (λv. SEP_EXISTS k3.
        STDIO (forwardFD fs fd (k + k2 + k3)) *
        INSTREAM_LINES #"\n" fd fdv (TL lines2)
          (forwardFD fs fd (k + k2 + k3)) *
        NT_TABLE lim s1 tv *
        &(lines2 ≠ [] ∧ line_TYPE (toks (HD lines2)) v))
      (λe. SEP_EXISTS k lines' s'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
        NT_TABLE lim s' tv *
        &(Fail_exn e ∧ parse_spec_block lim s (MAP toks (ln::lns)) = NONE))`
    >- (
      xapp_spec read_toks_spec>>
      xsimpl>>
      qexistsl_tac[`NT_TABLE lim s1 tv`,`lines2`,`forwardFD fs fd (k + k2)`,
                   `fd`,`lno2`]>>
      xsimpl>>
      rw[]>>
      gvs[parse_spec_block_def,forwardFD_o]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- xsimpl>>
    `∃ln2 lns2. lines2 = ln2::lns2` by (Cases_on`lines2`>>fs[])>>
    gvs[]>>
    rpt xlet_autop>>
    gvs[]>>
    xlet_auto
    >- (xsimpl>>simp (eq_lemmas()))>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def,parse_spec_block_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    gvs[parse_spec_block_def]>>
    qexistsl_tac[`k + (k2 + k3)`,`lns2`,`lno2 + 1`]>>
    xsimpl)>>
  rpt xlet_autop>>
  gvs[]>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_spec_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[parse_spec_block_def]>>
  qexistsl_tac[`k`,`lns`,`lno + 1`]>>
  xsimpl>>
  simp[PAIR_TYPE_def,LIST_TYPE_def]
QED

Theorem parse_def_aux_arr_spec:
  ∀ss lim s acc accv fd fdv lines lno lnov fs.
  NUM lno lnov ∧ LIST_TYPE constraint_TYPE acc accv ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_def_aux_arr" (get_ml_prog_state()))
    [tv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' f s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_def_aux lim s ss acc = SOME (f,s',rest) ∧
           PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM (f,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_def_aux lim s ss acc = NONE)))
Proof
  completeInduct_on`LENGTH (lines:mlstring list)`>>
  rw[]>>
  xcf "parse_def_aux_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_def_aux lim s (MAP toks lines) acc = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_def_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln lns. lines = ln::lns` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  assume_tac (Q.SPEC`«def»` line_TYPE_keyword)>>
  rpt xlet_autop>>
  simp[Once parse_def_aux_def]>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lns`,`lno + 1`]>>
    xsimpl>>
    simp[PAIR_TYPE_def])>>
  xlet_autop>>
  namedCases_on`parse_constraint_ns (toks ln)`["","c"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    fs[Fail_exn_def,Once parse_def_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  xlet`POSTve
    (λv. SEP_EXISTS c1 s1.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(name_pbc lim c s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_def_aux lim s (MAP toks (ln::lns)) acc = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k)`,
      `s`,`lim`,`c`,`lno`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s1 tv * _`>>
    qexistsl_tac[`k`,`lns`,`s1`]>>
    xsimpl>>
    gvs[Once parse_def_aux_def])
  >- xsimpl>>
  xlet_autop>>
  namedCases_on`mk_npbc c1`["","c2"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    fs[Fail_exn_def,Once parse_def_aux_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  qpat_x_assum`∀m. _`(qspec_then`LENGTH lns` mp_tac)>>
  impl_tac
  >- simp[]>>
  disch_then (qspec_then`lns` mp_tac)>>
  simp[]>>
  strip_tac>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`s1`,`lim`,`forwardFD fs fd k`,`fd`,`c2::acc`,
               `lno + 1`]>>
  xsimpl>>
  simp[LIST_TYPE_def,forwardFD_o]>>
  rw[]
  >- metis_tac[SEP_IMP_REFL_gc]>>
  gvs[Once parse_def_aux_def]>>
  metis_tac[SEP_IMP_REFL_gc]
QED

Theorem parse_trans_vars_arr_spec:
  NUM lno lnov ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_trans_vars_arr" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' vars s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_trans_vars lim s ss = SOME (vars,s',rest) ∧
           PAIR_TYPE vars3_TYPE NUM (vars,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_trans_vars lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_trans_vars_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k1.
      STDIO (forwardFD fs fd k1) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k1) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_trans_vars lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_trans_vars_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln1 lns1. lines = ln1::lns1` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k2.
      STDIO (forwardFD fs fd (k1 + k2)) *
      INSTREAM_LINES #"\n" fd fdv (TL lns1) (forwardFD fs fd (k1 + k2)) *
      NT_TABLE lim s tv *
      &(lns1 ≠ [] ∧ line_TYPE (toks (HD lns1)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_trans_vars lim s (MAP toks (ln1::lns1)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lns1`,`forwardFD fs fd k1`,`fd`,
                 `lno + 1`]>>
    xsimpl>>
    rw[]>>
    simp[parse_trans_vars_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln2 lns2. lns1 = ln2::lns2` by (Cases_on`lns1`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k3.
      STDIO (forwardFD fs fd (k1 + k2 + k3)) *
      INSTREAM_LINES #"\n" fd fdv (TL lns2)
        (forwardFD fs fd (k1 + k2 + k3)) *
      NT_TABLE lim s tv *
      &(lns2 ≠ [] ∧ line_TYPE (toks (HD lns2)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s (MAP toks (ln1::ln2::lns2)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lns2`,`forwardFD fs fd (k1 + k2)`,
                 `fd`,`lno + 2`]>>
    xsimpl>>
    rw[]>>
    simp[parse_trans_vars_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln3 lns3. lns2 = ln3::lns3` by (Cases_on`lns2`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k4.
      STDIO (forwardFD fs fd (k1 + k2 + k3 + k4)) *
      INSTREAM_LINES #"\n" fd fdv (TL lns3)
        (forwardFD fs fd (k1 + k2 + k3 + k4)) *
      NT_TABLE lim s tv *
      &(lns3 ≠ [] ∧ line_TYPE (toks (HD lns3)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s (MAP toks (ln1::ln2::ln3::lns3)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lns3`,
                 `forwardFD fs fd (k1 + k2 + k3)`,`fd`,`lno + 3`]>>
    xsimpl>>
    rw[]>>
    simp[parse_trans_vars_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln4 rest. lns3 = ln4::rest` by (Cases_on`lns3`>>fs[])>>
  gvs[]>>
  assume_tac (Q.SPEC`«vars»` line_TYPE_keyword)>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def,parse_trans_vars_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS ws ws1 s1.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      INSTREAM_LINES #"\n" fd fdv rest
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      NT_TABLE lim s1 tv *
      &(parse_vars_line «fresh_right» (toks ln3) = SOME ws ∧
        name_vars lim ws s = SOME (ws1,s1) ∧ LIST_TYPE NUM ws1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
       INSTREAM_LINES #"\n" fd fdv rest
         (forwardFD fs fd (k1 + (k2 + (k3 + k4))))`,
      `s`,`lim`,`toks ln3`,`lno + 2`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s1 tv * _`>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`s1`]>>
    xsimpl>>
    simp[parse_trans_vars_def]>>
    Cases_on`parse_vars_line «fresh_right» (toks ln3)`>>
    gvs[])
  >- xsimpl>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`(ws1,[],[])`,`s1`,
                 `lno + 4`]>>
    xsimpl>>
    gvs[parse_trans_vars_def,PAIR_TYPE_def,LIST_TYPE_def])>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS bs bs1 s2.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      INSTREAM_LINES #"\n" fd fdv rest
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
      NT_TABLE lim s2 tv *
      &(parse_vars_line «fresh_aux_1» (toks ln4) = SOME bs ∧
        name_vars lim bs s1 = SOME (bs1,s2) ∧ LIST_TYPE NUM bs1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)))) *
       INSTREAM_LINES #"\n" fd fdv rest
         (forwardFD fs fd (k1 + (k2 + (k3 + k4))))`,
      `s1`,`lim`,`toks ln4`,`lno + 3`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s2 tv * _`>>
    qexistsl_tac[`k1 + (k2 + (k3 + k4))`,`rest`,`s2`]>>
    xsimpl>>
    simp[parse_trans_vars_def]>>
    Cases_on`parse_vars_line «fresh_aux_1» (toks ln4)`>>
    gvs[])
  >- xsimpl>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k5.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)) + k5)) *
      INSTREAM_LINES #"\n" fd fdv (TL rest)
        (forwardFD fs fd (k1 + (k2 + (k3 + k4)) + k5)) *
      NT_TABLE lim s2 tv *
      &(rest ≠ [] ∧ line_TYPE (toks (HD rest)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s (MAP toks (ln1::ln2::ln3::ln4::rest)) =
          NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s2 tv`,`rest`,
                 `forwardFD fs fd (k1 + (k2 + (k3 + k4)))`,`fd`,`lno + 4`]>>
    xsimpl>>
    rw[]>>
    gvs[parse_trans_vars_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln5 rest1. rest = ln5::rest1` by (Cases_on`rest`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k6.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + k5))) + k6)) *
      INSTREAM_LINES #"\n" fd fdv (TL rest1)
        (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + k5))) + k6)) *
      NT_TABLE lim s2 tv *
      &(rest1 ≠ [] ∧ line_TYPE (toks (HD rest1)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s
          (MAP toks (ln1::ln2::ln3::ln4::ln5::rest1)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s2 tv`,`rest1`,
                 `forwardFD fs fd (k1 + (k2 + (k3 + (k4 + k5))))`,`fd`,
                 `lno + 5`]>>
    xsimpl>>
    rw[]>>
    gvs[parse_trans_vars_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln6 rest2. rest1 = ln6::rest2` by (Cases_on`rest1`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS cs cs1 s3.
      STDIO (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + (k5 + k6)))))) *
      INSTREAM_LINES #"\n" fd fdv rest2
        (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + (k5 + k6)))))) *
      NT_TABLE lim s3 tv *
      &(parse_vars_line «fresh_aux_2» (toks ln5) = SOME cs ∧
        name_vars lim cs s2 = SOME (cs1,s3) ∧ LIST_TYPE NUM cs1 v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_trans_vars lim s
          (MAP toks (ln1::ln2::ln3::ln4::ln5::ln6::rest2)) = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + (k5 + k6)))))) *
       INSTREAM_LINES #"\n" fd fdv rest2
         (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + (k5 + k6))))))`,
      `s2`,`lim`,`toks ln5`,`lno + 4`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s3 tv * _`>>
    qexistsl_tac[`k1 + (k2 + (k3 + (k4 + (k5 + k6))))`,`rest2`,`s3`]>>
    xsimpl>>
    simp[parse_trans_vars_def]>>
    Cases_on`parse_vars_line «fresh_aux_2» (toks ln5)`>>
    gvs[])
  >- xsimpl>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_trans_vars_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  qexistsl_tac[`k1 + (k2 + (k3 + (k4 + (k5 + k6))))`,`rest2`,
               `(ws1,bs1,cs1)`,`s3`,`lno + 6`]>>
  xsimpl>>
  gvs[parse_trans_vars_def,PAIR_TYPE_def]
QED

Theorem parse_proof_block_arr_spec:
  NUM lno lnov ∧ line_TYPE mark markv ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_proof_block_arr" (get_ml_prog_state()))
    [tv; fdv; lnov; markv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' pf s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_proof_block lim s mark ss = SOME (pf,s',rest) ∧
           PAIR_TYPE pfs_TYPE NUM (pf,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_proof_block lim s mark ss = NONE)))
Proof
  rw[]>>
  xcf "parse_proof_block_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_proof_block lim s mark (MAP toks lines) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_proof_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln lns. lines = ln::lns` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  assume_tac (Q.SPEC`«proof»` line_TYPE_keyword)>>
  rpt xlet_autop>>
  gvs[]>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_proof_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k2 lines2 pf s1 l lno2 rest.
       STDIO (forwardFD fs fd (k + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
       NT_TABLE lim s1 tv *
       &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l,lno2) v ∧
         parse_subproof lim s (MAP toks lns) = SOME (pf,s1,l,rest) ∧
         MAP toks lines2 = rest))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧
         parse_proof_block lim s mark (MAP toks (ln::lns)) = NONE))`
  >- (
    xapp_spec parse_subproof_imp_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[parse_proof_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_proof_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  xlet`POSTve
    (λv. SEP_EXISTS k3.
      STDIO (forwardFD fs fd (k + k2 + k3)) *
      INSTREAM_LINES #"\n" fd fdv (TL lines2)
        (forwardFD fs fd (k + k2 + k3)) *
      NT_TABLE lim s1 tv *
      &(lines2 ≠ [] ∧ line_TYPE (toks (HD lines2)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧
        parse_proof_block lim s mark (MAP toks (ln::lns)) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s1 tv`,`lines2`,`forwardFD fs fd (k + k2)`,
                 `fd`,`lno2`]>>
    xsimpl>>
    rw[]>>
    gvs[parse_proof_block_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln2 lns2. lines2 = ln2::lns2` by (Cases_on`lines2`>>fs[])>>
  gvs[]>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_proof_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[parse_proof_block_def]>>
  qexistsl_tac[`k + (k2 + k3)`,`lns2`,`lno2 + 1`]>>
  xsimpl
QED

Theorem parse_trans_block_arr_spec:
  NUM lno lnov ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_trans_block_arr" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' pft s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_trans_block lim s ss = SOME (pft,s',rest) ∧
           PAIR_TYPE
             (PAIR_TYPE (LIST_TYPE NUM)
               (PAIR_TYPE (LIST_TYPE NUM)
                 (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE))) NUM (pft,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_trans_block lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_trans_block_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k lines1 vars s1 rest1 lno1.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k) *
       NT_TABLE lim s1 tv *
       &(parse_trans_vars lim s (MAP toks lines) = SOME (vars,s1,rest1) ∧
         PAIR_TYPE vars3_TYPE NUM (vars,lno1) v ∧
         MAP toks lines1 = rest1))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_trans_block lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_trans_vars_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s`,`lines`,`lim`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    simp[parse_trans_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  PairCases_on`vars`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  assume_tac (Q.SPEC`«transitivity»` line_TYPE_keyword)>>
  rpt xlet_autop>>
  gvs[]>>
  xlet`POSTve
    (λv. SEP_EXISTS k2 lines2 pf s2 rest2 lno2.
       STDIO (forwardFD fs fd (k + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
       NT_TABLE lim s2 tv *
       &(parse_proof_block lim s1 [INL «transitivity»] (MAP toks lines1) =
           SOME (pf,s2,rest2) ∧
         PAIR_TYPE pfs_TYPE NUM (pf,lno2) v ∧
         MAP toks lines2 = rest2))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_trans_block lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_proof_block_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s1`,`[INL «transitivity»]`,`lines1`,`lim`,
                 `forwardFD fs fd k`,`fd`,`lno1`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[parse_trans_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[parse_trans_block_def,PAIR_TYPE_def]>>
  qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
  xsimpl
QED

Theorem parse_refl_block_arr_spec:
  NUM lno lnov ∧ MAP toks lines = ss ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_refl_block_arr" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv. SEP_EXISTS k lines' pf s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(parse_refl_block lim s ss = SOME (pf,s',rest) ∧
           PAIR_TYPE pfs_TYPE NUM (pf,lno') v ∧
           MAP toks lines' = rest))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_refl_block lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_refl_block_arr" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
      NT_TABLE lim s tv *
      &(lines ≠ [] ∧ line_TYPE (toks (HD lines)) v))
    (λe. SEP_EXISTS k lines' s'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      NT_TABLE lim s' tv *
      &(Fail_exn e ∧ parse_refl_block lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s tv`,`lines`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]>>
    simp[parse_refl_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln lns. lines = ln::lns` by (Cases_on`lines`>>fs[])>>
  gvs[]>>
  assume_tac (Q.SPEC`«reflexivity»` line_TYPE_keyword)>>
  rpt xlet_autop>>
  gvs[]>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_refl_block_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  gvs[]>>
  xapp_spec parse_proof_block_arr_spec>>
  xsimpl>>
  qexistsl_tac[`emp`,`s`,`[INL «reflexivity»]`,`lns`,`lim`,
               `forwardFD fs fd k`,`fd`,`lno + 1`]>>
  xsimpl>>
  simp[forwardFD_o,parse_refl_block_def]>>
  rw[]>>
  metis_tac[SEP_IMP_REFL_gc]
QED

Quote add_cakeml:
  fun parse_pre_order tv fd lno =
    case parse_vars_block_arr tv fd lno of (vars,lno1) =>
    case parse_spec_block_arr tv fd lno1 of (gspec,lno2) =>
    case parse_def_aux_arr tv fd lno2 [] of (f,lno3) =>
    case parse_trans_block_arr tv fd lno3 of (pft,lno4) =>
    case parse_refl_block_arr tv fd lno4 of (pfr,lno5) =>
    let val h = read_toks lno5 fd in
      if check_end [Inl "def_order"] h then
        (vars,(gspec,(f,(pfr,(pft,lno5+1)))))
      else raise Fail (format_failure lno5 "expected the end of an order definition")
    end
End

Theorem parse_pre_order_spec:
  NUM lno lnov ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_pre_order" (get_ml_prog_state()))
    [tv;fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' vars gspec f pfr pft s' rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(
            parse_pre_order lim s ss =
              SOME (vars,gspec,f,pfr,pft,s',rest) ∧
            PAIR_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))
            (PAIR_TYPE
              (LIST_TYPE
                   (PAIR_TYPE constraint_TYPE
                      (PAIR_TYPE subst_raw_TYPE
                         (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM)))))
            (PAIR_TYPE (LIST_TYPE constraint_TYPE)
            (PAIR_TYPE pfs_TYPE
            (PAIR_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (LIST_TYPE NUM)
                  (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE)))
            NUM))))
            (vars,gspec,f,pfr,pft,lno') v ∧
            MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_pre_order lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_pre_order" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv. SEP_EXISTS k1 lines1 vars s1 rest1 lno1.
       STDIO (forwardFD fs fd k1) *
       INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k1) *
       NT_TABLE lim s1 tv *
       &(parse_vars_block lim s (MAP toks lines) = SOME (vars,s1,rest1) ∧
         PAIR_TYPE vars3_TYPE NUM (vars,lno1) v ∧
         MAP toks lines1 = rest1))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_pre_order lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_vars_block_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s`,`lines`,`lim`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    simp[parse_pre_order_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λv. SEP_EXISTS k2 lines2 gspec s2 rest2 lno2.
       STDIO (forwardFD fs fd (k1 + k2)) *
       INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k1 + k2)) *
       NT_TABLE lim s2 tv *
       &(parse_spec_block lim s1 (MAP toks lines1) = SOME (gspec,s2,rest2) ∧
         PAIR_TYPE gspec_TYPE NUM (gspec,lno2) v ∧
         MAP toks lines2 = rest2))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_pre_order lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_spec_block_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s1`,`lines1`,`lim`,`forwardFD fs fd k1`,`fd`,
                 `lno1`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[parse_pre_order_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet`POSTve
    (λv. SEP_EXISTS k3 lines3 f s3 rest3 lno3.
       STDIO (forwardFD fs fd (k1 + k2 + k3)) *
       INSTREAM_LINES #"\n" fd fdv lines3 (forwardFD fs fd (k1 + k2 + k3)) *
       NT_TABLE lim s3 tv *
       &(parse_def_aux lim s2 (MAP toks lines2) [] = SOME (f,s3,rest3) ∧
         PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM (f,lno3) v ∧
         MAP toks lines3 = rest3))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_pre_order lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_def_aux_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s2`,`lines2`,`lim`,`forwardFD fs fd (k1 + k2)`,`fd`,
                 `[]`,`lno2`]>>
    xsimpl>>
    simp[forwardFD_o,LIST_TYPE_def]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[parse_pre_order_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λv. SEP_EXISTS k4 lines4 pft s4 rest4 lno4.
       STDIO (forwardFD fs fd (k1 + (k2 + k3) + k4)) *
       INSTREAM_LINES #"\n" fd fdv lines4
         (forwardFD fs fd (k1 + (k2 + k3) + k4)) *
       NT_TABLE lim s4 tv *
       &(parse_trans_block lim s3 (MAP toks lines3) = SOME (pft,s4,rest4) ∧
         PAIR_TYPE
           (PAIR_TYPE (LIST_TYPE NUM)
             (PAIR_TYPE (LIST_TYPE NUM)
               (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE))) NUM (pft,lno4) v ∧
         MAP toks lines4 = rest4))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_pre_order lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_trans_block_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s3`,`lines3`,`lim`,
                 `forwardFD fs fd (k1 + (k2 + k3))`,`fd`,`lno3`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[parse_pre_order_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λv. SEP_EXISTS k5 lines5 pfr s5 rest5 lno5.
       STDIO (forwardFD fs fd (k1 + (k2 + (k3 + k4)) + k5)) *
       INSTREAM_LINES #"\n" fd fdv lines5
         (forwardFD fs fd (k1 + (k2 + (k3 + k4)) + k5)) *
       NT_TABLE lim s5 tv *
       &(parse_refl_block lim s4 (MAP toks lines4) = SOME (pfr,s5,rest5) ∧
         PAIR_TYPE pfs_TYPE NUM (pfr,lno5) v ∧
         MAP toks lines5 = rest5))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_pre_order lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_refl_block_arr_spec>>
    xsimpl>>
    qexistsl_tac[`emp`,`s4`,`lines4`,`lim`,
                 `forwardFD fs fd (k1 + (k2 + (k3 + k4)))`,`fd`,`lno4`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    gvs[parse_pre_order_def]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λv. SEP_EXISTS k6.
       STDIO (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + k5))) + k6)) *
       INSTREAM_LINES #"\n" fd fdv (TL lines5)
         (forwardFD fs fd (k1 + (k2 + (k3 + (k4 + k5))) + k6)) *
       NT_TABLE lim s5 tv *
       &(lines5 ≠ [] ∧ line_TYPE (toks (HD lines5)) v))
    (λe. SEP_EXISTS k lines' s'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim s' tv *
       &(Fail_exn e ∧ parse_pre_order lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec read_toks_spec>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim s5 tv`,`lines5`,
                 `forwardFD fs fd (k1 + (k2 + (k3 + (k4 + k5))))`,`fd`,
                 `lno5`]>>
    xsimpl>>
    rw[]>>
    gvs[parse_pre_order_def,forwardFD_o]>>
    metis_tac[SEP_IMP_REFL_gc])
  >- xsimpl>>
  `∃ln lns. lines5 = ln::lns` by (Cases_on`lines5`>>fs[])>>
  gvs[]>>
  assume_tac (Q.SPEC`«def_order»` line_TYPE_keyword)>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def,parse_pre_order_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[parse_pre_order_def,PAIR_TYPE_def]>>
  qexistsl_tac[`k1 + (k2 + (k3 + (k4 + (k5 + k6))))`,`lns`,`lno5 + 1`]>>
  xsimpl
QED

(* One cstep, or the line that is not one *)
Quote add_cakeml:
  fun parse_cstep tv fd lno =
    case input_toks fd of
      None => raise Fail (format_failure lno "Unexpected EOF when parsing proof steps")
    | Some s =>
    case parse_line s of
      None => (Inl s, lno+1)
    | Some pl =>
    case nt_line tv lno pl of
      Pbchd c =>
      (case mk_npbc c of
        None => raise Fail (format_failure lno "constraint has no single normal form")
      | Some c1 =>
        case parse_lsteps tv fd (lno+1) of
          (pf,(res,lno')) =>
          case check_mark_qed_id_pbc res of
            None => raise Fail (format_failure (sub_one lno') "subproof not terminated with contradiction id")
          | Some n => (Inr (Sstep (Lstep (Con c1 pf n))), lno'))
    | Redhd c ss =>
      (case mk_npbc c of
        None => raise Fail (format_failure lno "constraint has no single normal form")
      | Some c1 =>
        case parse_scope_imp tv fd (lno+1) of
          (pf,(h,lno')) =>
          case check_mark_qed_id_opt_red h of
            None => raise Fail (format_failure (sub_one lno') "Incorrectly terminated redundancy step")
          | Some idopt => (Inr (Sstep (Red c1 ss pf idopt)), lno'))
    | Domhd c ss =>
      (case mk_npbc c of
        None => raise Fail (format_failure lno "constraint has no single normal form")
      | Some c1 =>
        case parse_scope_imp tv fd (lno+1) of
          (pf,(h,lno')) =>
          case check_mark_qed_id_opt_dom h of
            None => raise Fail (format_failure (sub_one lno') "Incorrectly terminated dominance step")
          | Some idopt => (Inr (Dom c1 ss pf idopt), lno'))
    | Delchd n ss =>
      (case parse_scope_imp tv fd (lno+1) of
        (pf,(h,lno')) =>
        case check_mark_qed_id_opt_delc h of
          None => raise Fail (format_failure (sub_one lno') "Incorrectly terminated checked deletion step")
        | Some idopt => (Inr (Checkeddelete n ss pf idopt), lno'))
    | Ordhd name =>
      (case parse_pre_order tv fd (lno+1) of
        (vars,(gspec,(f,(pfr,(pft,lno'))))) =>
        (Inr (Storeorder name vars gspec f pfr pft), lno'))
    | Objuhd b f =>
      (case normalise_obj (Some f) of
        None => raise Fail (format_failure lno "objective has no normal form")
      | Some f1 =>
        case parse_subproof_imp tv fd (lno+1) of
          (pf,(s',lno')) =>
          case check_mark_qed_id_opt_obju s' of
            Some None => (Inr (Changeobj b f1 pf), lno')
          | _ => raise Fail (format_failure (sub_one lno') "Incorrectly terminated objective update step"))
    | Preshd b x c =>
      (case mk_npbc c of
        None => raise Fail (format_failure lno "constraint has no single normal form")
      | Some c1 =>
        case parse_subproof_imp tv fd (lno+1) of
          (pf,(s',lno')) =>
          case check_mark_qed_id_opt_preserve b s' of
            Some None => (Inr (Changepres b x c1 pf), lno')
          | _ => raise Fail (format_failure (sub_one lno') "Incorrectly terminated preserved set change step"))
    | pl1 =>
      if is_lstep pl1 then
        (case fin_lstep pl1 of
          None => raise Fail (format_failure lno "constraint has no single normal form")
        | Some step => (Inr (Sstep (Lstep step)), lno+1))
      else
        (case fin_cstep pl1 of
          None => raise Fail (format_failure lno "objective has no normal form")
        | Some cs => (Inr cs, lno+1))
End

Theorem parse_cstep_spec:
  NUM lno lnov ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_cstep" (get_ml_prog_state()))
    [tv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' res s' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(
            parse_cstep lim s ss = SOME (res,s',rest) ∧
            PAIR_TYPE (SUM_TYPE line_TYPE NPBC_CHECK_CSTEP_TYPE) NUM
              (res,lno') v ∧
            MAP toks lines' = rest))
      (λe.
         SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_cstep lim s ss = NONE)))
Proof
  rw[]>>
  xcf "parse_cstep" (get_ml_prog_state ())>>
  Cases_on`lines`
  >- (
    xlet`POSTv v.
      SEP_EXISTS k.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
        NT_TABLE lim s tv *
        &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v`
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac[`NT_TABLE lim s tv`,`[]`]>>
      xsimpl>>
      metis_tac[SEP_IMP_REFL,SEP_IMP_REFL_gc])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[parse_cstep_def,Fail_exn_def]>>
    qexistsl_tac[`k`,`[]`,`s`]>>
    xsimpl>>
    metis_tac[])>>
  rename1`INSTREAM_LINES _ _ _ (ln::lns) _`>>
  xlet`POSTv v.
    SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s tv *
      &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks ln)) v`
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac[`NT_TABLE lim s tv`,`ln::lns`,`fs`,`fd`]>>
    xsimpl>>
    simp[toks_def]>>
    metis_tac[SEP_IMP_REFL_gc])>>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  simp[parse_cstep_def]>>
  namedCases_on`parse_line (toks ln)`["","pl"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lns`,`lno + 1`]>>
    simp[PAIR_TYPE_def,SUM_TYPE_def]>>
    xsimpl)>>
  xlet`POSTve
    (λv. SEP_EXISTS pl1 s1.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(name_pline lim pl s = SOME (pl1,s1) ∧ PB_PARSE_PLINE_TYPE NUM pl1 v))
    (λe. SEP_EXISTS s1.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(Fail_exn e ∧ name_pline lim pl s = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k)`,
      `s`,`pl`,`lim`,`lno`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim s1 tv ==>> _`>>
    qexists_tac`s1`>>
    xsimpl)
  >- (
    xsimpl>>
    rw[]>>
    qexistsl_tac[`k`,`lns`]>>
    xsimpl>>
    metis_tac[SEP_IMP_REFL])>>
  Cases_on`pl1`>>
  qpat_assum`PB_PARSE_PLINE_TYPE NUM _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [PB_PARSE_PLINE_TYPE_def])>>
  xmatch
  >~ [`PbcHd c`]
  >- (
    gvs[]>>
    xlet_autop>>
    namedCases_on`mk_npbc c`["","c1"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE (LIST_TYPE NPBC_CHECK_LSTEP_TYPE) (PAIR_TYPE line_TYPE NUM)
             (pf,l2,lno2) v ∧
           parse_lsteps lim s1 (MAP toks lns) = SOME (pf,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_lsteps lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_lsteps_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id (INL «pbc») l2`["","n"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_pbc_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
    xsimpl>>
    gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def,
        NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def])
  >~ [`RedHd c ss`]
  >- (
    gvs[]>>
    xlet_autop>>
    namedCases_on`mk_npbc c`["","c1"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE scpfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l2,lno2) v ∧
           parse_scope lim s1 (MAP toks lns) = SOME (pf,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_scope lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_scope_imp_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id_opt (INL «red») l2`["","idopt"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_opt_red_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
    xsimpl>>
    gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def,
        NPBC_CHECK_SSTEP_TYPE_def])
  >~ [`DomHd c ss`]
  >- (
    gvs[]>>
    xlet_autop>>
    namedCases_on`mk_npbc c`["","c1"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE scpfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l2,lno2) v ∧
           parse_scope lim s1 (MAP toks lns) = SOME (pf,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_scope lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_scope_imp_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id_opt (INL «dom») l2`["","idopt"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_opt_dom_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
    xsimpl>>
    gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def])
  >~ [`DelcHd n ss`]
  >- (
    gvs[]>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE scpfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l2,lno2) v ∧
           parse_scope lim s1 (MAP toks lns) = SOME (pf,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_scope lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_scope_imp_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id_opt (INL «delc») l2`["","idopt"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_opt_delc_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def]>>
      metis_tac[SEP_IMP_REFL_gc])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
    xsimpl>>
    gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def])
  >~ [`OrdHd nm`]
  >- (
    gvs[]>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 vars gspec f pfr pft s2 rest2 lno2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(parse_pre_order lim s1 (MAP toks lns) =
             SOME (vars,gspec,f,pfr,pft,s2,rest2) ∧
           PAIR_TYPE vars3_TYPE
             (PAIR_TYPE gspec_TYPE
             (PAIR_TYPE (LIST_TYPE constraint_TYPE)
             (PAIR_TYPE pfs_TYPE
             (PAIR_TYPE
               (PAIR_TYPE (LIST_TYPE NUM)
                 (PAIR_TYPE (LIST_TYPE NUM)
                   (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE)))
             NUM)))) (vars,gspec,f,pfr,pft,lno2) v ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_pre_order lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_pre_order_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
    xsimpl>>
    gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def])
  >~ [`ObjuHd b f`]
  >- (
    gvs[]>>
    xlet`POSTv w.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lns (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &OPTION_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE NUM))) INT)
        (SOME f) w`
    >- (
      xcon>>
      xsimpl>>
      simp[OPTION_TYPE_def])>>
    xlet_autop>>
    namedCases_on`normalise_obj (SOME f)`["","f1"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l2,lno2) v ∧
           parse_subproof lim s1 (MAP toks lns) = SOME (pf,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_subproof lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_subproof_imp_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id_opt (INL «obju») l2`["","io"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_opt_obju_def]>>>
    NTH_GOAL (Cases_on`io`>>fs[OPTION_TYPE_def]) 2>>
    xmatch
    >~ [`check_mark_qed_id_opt _ l2 = SOME NONE`]
    >- (
      rpt xlet_autop>>
      xcon>>
      xsimpl>>
      qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
      xsimpl>>
      gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def])>>
    (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def]>>
      metis_tac[SEP_IMP_REFL_gc]))
  >~ [`PresHd b x c`]
  >- (
    gvs[]>>
    xlet_autop>>
    namedCases_on`mk_npbc c`["","c1"]>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS k2 lines2 pf s2 l2 lno2 rest2.
         STDIO (forwardFD fs fd (k + k2)) *
         INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd (k + k2)) *
         NT_TABLE lim s2 tv *
         &(PAIR_TYPE pfs_TYPE (PAIR_TYPE line_TYPE NUM) (pf,l2,lno2) v ∧
           parse_subproof lim s1 (MAP toks lns) = SOME (pf,s2,l2,rest2) ∧
           MAP toks lines2 = rest2))
      (λe. SEP_EXISTS k lines' s'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         &(Fail_exn e ∧ parse_subproof lim s1 (MAP toks lns) = NONE))`
    >- (
      xapp_spec parse_subproof_imp_spec>>
      xsimpl>>
      qexistsl_tac[`emp`,`s1`,`lns`,`lim`,`forwardFD fs fd k`,`fd`,`lno + 1`]>>
      xsimpl>>
      simp[forwardFD_o]>>
      rw[]
      >- metis_tac[SEP_IMP_REFL_gc]>>
      metis_tac[SEP_IMP_REFL_gc])
    >- (
      xsimpl>>
      rw[]>>
      gvs[]>>
      metis_tac[SEP_IMP_REFL])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    namedCases_on`check_mark_qed_id_opt
      (if b then INL «preserved_add» else INL «preserved_rm») l2`["","io"]>>
    fs[OPTION_TYPE_def,check_mark_qed_id_opt_preserve_def]>>>
    NTH_GOAL (Cases_on`io`>>fs[OPTION_TYPE_def]) 2>>
    xmatch
    >~ [`check_mark_qed_id_opt _ l2 = SOME NONE`]
    >- (
      rpt xlet_autop>>
      xcon>>
      xsimpl>>
      qexistsl_tac[`k + k2`,`lines2`,`lno2`]>>
      xsimpl>>
      gvs[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def])>>
    (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      gvs[Fail_exn_def]>>
      metis_tac[SEP_IMP_REFL_gc]))>>
  (
    gvs[is_lstep_def]>>
    xlet_autop>>
    xif>>
    fs[is_lstep_def]>>
    xlet_autop>>
    TOP_CASE_TAC>>
    qpat_x_assum`OPTION_TYPE _ _ _` mp_tac>>
    simp[OPTION_TYPE_def]>>
    strip_tac>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`k`,`lns`,`s1`]>>
      xsimpl>>
      metis_tac[])>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lns`,`lno + 1`]>>
    xsimpl>>
    simp[PAIR_TYPE_def,SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def,
         NPBC_CHECK_SSTEP_TYPE_def])
QED

(* returns the necessary information to check the
  output and conclusion sections *)
Quote add_cakeml:
  fun check_unsat'' tv fd lno fml assg st inds vimap id cfg ht =
    case parse_cstep tv fd lno of
      (Inl s, lno') =>
      (case cfg of (pc,_) =>
      (lno', (s, (fml, (inds, (pc, (id, ht)))))))
    | (Inr cstep, lno') =>
      (case check_cstep_arr lno cstep fml assg st inds vimap id cfg ht of
        (fml', (assg', (st', (inds', (vimap', (id', (cfg', ht'))))))) =>
        check_unsat'' tv fd lno' fml' assg' st' inds' vimap' id' cfg'
          ht')
End

(* Repeatedly parse a line and run the cstep checker,
  returning the last encountered state *)
Definition parse_and_run_def:
  parse_and_run lim s ss
    fml assg st inds vimap id cfg ht =
  case parse_cstep lim s ss of
    NONE => NONE
  | SOME (INL l, s', rest) =>
    SOME (rest, l, s', fml, inds, FST cfg, id, ht)
  | SOME (INR cstep, s', rest) =>
    (case check_cstep_list cstep fml assg st inds vimap id cfg ht of
      SOME (fml', assg', st', inds', vimap', id', cfg', ht') =>
        parse_and_run lim s' rest fml' assg' st' inds' vimap' id' cfg' ht'
    | res => NONE)
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND o SND)`>>
  rw[]>>
  imp_res_tac parse_cstep_LENGTH>>
  fs[]
End

Theorem check_unsat''_spec:
  ∀s ss fmlls assg st inds m vw ents id cfg hw a d
    lno lnov fmlls assgv stv indsv idv cfgv lines fs fmlv
    vimapa vimapv htv bksv bksls.
  NUM lno lnov ∧
  fml_bound fmlls (LENGTH assg) ∧ stamps_ok assg st ∧
  NUM st stv ∧
  (LIST_TYPE NUM) inds indsv ∧
  VIMAP_TYPE (m,vw,vimapa) vimapv ∧
  NUM id idv ∧
  cfg_TYPE cfg cfgv ∧ SND (SND (SND cfg)) = mk_ord_pre (FST cfg).ord ∧
  ht_TYPE (hw,a,d,bksv) htv ∧
  MAP toks lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [tv; fdv; lnov; fmlv; assgv; stv; indsv; vimapv; idv; cfgv; htv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim s tv *
      ARRAY_OF fslot_TYPE fmlv fmlls * ARRAY_OF NUM assgv assg *
      ARRAY_OF vimapn_TYPE vimapa ents * ARRAY_OF NUM bksv bksls)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' l s' fmlv' fmlls' inds' pc' id'
             hw' a' d' bksv' bksls'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         ARRAY_OF fslot_TYPE fmlv' fmlls' * ARRAY_OF NUM bksv' bksls' *
         &(parse_and_run lim s ss fmlls assg st inds (m,vw,ents) id cfg
             (hw,a,d,bksls) =
             SOME (MAP toks lines',l,s',
               (fmlls',inds',pc',id',(hw',a',d',bksls'))) ∧
           PAIR_TYPE NUM (PAIR_TYPE line_TYPE (PAIR_TYPE ($=)
             (PAIR_TYPE (LIST_TYPE NUM) (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
               (PAIR_TYPE NUM ht_TYPE)))))
             (lno',l,fmlv',inds',pc',id',(hw',a',d',bksv')) v))
      (λe.
         SEP_EXISTS k lines' fmlv' fmlls' s'.
           ARRAY_OF fslot_TYPE fmlv' fmlls' * NT_TABLE lim s' tv *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            parse_and_run lim s ss fmlls assg st inds (m,vw,ents) id cfg
              (hw,a,d,bksls) = NONE)))
Proof
  completeInduct_on`LENGTH (lines:mlstring list)`>>
  rw[]>>
  PairCases_on`cfg`>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_def]>>
  xlet`POSTve
    (λv. SEP_EXISTS k lines1 res s1 lno1.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k) *
       NT_TABLE lim s1 tv *
       ARRAY_OF fslot_TYPE fmlv fmlls * ARRAY_OF NUM assgv assg *
       ARRAY_OF vimapn_TYPE vimapa ents * ARRAY_OF NUM bksv bksls *
       &(parse_cstep lim s (MAP toks lines) = SOME (res,s1,MAP toks lines1) ∧
         PAIR_TYPE (SUM_TYPE line_TYPE NPBC_CHECK_CSTEP_TYPE) NUM (res,lno1) v))
    (λe. SEP_EXISTS k lines' fmlv' fmlls' s'.
       ARRAY_OF fslot_TYPE fmlv' fmlls' * NT_TABLE lim s' tv *
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       &(Fail_exn e ∧ parse_cstep lim s (MAP toks lines) = NONE))`
  >- (
    xapp_spec parse_cstep_spec>>
    xsimpl>>
    qexistsl_tac[
      `ARRAY_OF fslot_TYPE fmlv fmlls * ARRAY_OF NUM assgv assg *
       ARRAY_OF vimapn_TYPE vimapa ents * ARRAY_OF NUM bksv bksls`,
      `s`,`lines`,`lim`,`fs`,`fd`,`lno`]>>
    xsimpl>>
    rw[]
    >- metis_tac[SEP_IMP_REFL_gc]>>
    qmatch_goalsub_rename_tac
      `STDIO (forwardFD fs fd kk) * INSTREAM_LINES _ fd fdv ll _ *
       NT_TABLE lim ss tv * _ ==>> _`>>
    qexistsl_tac[`kk`,`ll`,`fmlv`,`fmlls`,`ss`]>>
    xsimpl)
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_and_run_def]>>
    metis_tac[SEP_IMP_REFL])>>
  Cases_on`res`>>
  qpat_x_assum`PAIR_TYPE (SUM_TYPE _ _) _ _ _`
    (strip_assume_tac o REWRITE_RULE[PAIR_TYPE_def])>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    qpat_x_assum`cfg_TYPE _ _`
      (strip_assume_tac o REWRITE_RULE[PAIR_TYPE_def])>>
    gvs[]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`k`,`lines1`,`lno1`]>>
    xsimpl>>
    qexistsl_tac[`fmlv`,`bksv`]>>
    xsimpl>>
    gvs[PAIR_TYPE_def])>>
  rename1`parse_cstep _ _ _ = SOME (INR cstep,s1,_)`>>
  xmatch>>
  xlet`POSTve
    (λv'.
      SEP_EXISTS fmlv' fmlls' assgv' assg' st' inds' m' vw' vimapa' ents'
          id' cfg' hw' a' d' bksv' bksls'.
      ARRAY_OF fslot_TYPE fmlv' fmlls' * ARRAY_OF NUM assgv' assg' *
      ARRAY_OF vimapn_TYPE vimapa' ents' * ARRAY_OF NUM bksv' bksls' *
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(check_cstep_list cstep fmlls assg st inds (m,vw,ents) id
          (cfg0,cfg1,cfg2,mk_ord_pre cfg0.ord) (hw,a,d,bksls) =
          SOME (fmlls',assg',st',inds',(m',vw',ents'),id',cfg',
            (hw',a',d',bksls')) ∧
        PAIR_TYPE ($=) (PAIR_TYPE ($=) (PAIR_TYPE NUM
          (PAIR_TYPE (LIST_TYPE NUM) (PAIR_TYPE VIMAP_TYPE
          (PAIR_TYPE NUM (PAIR_TYPE cfg_TYPE ht_TYPE))))))
          (fmlv',assgv',st',inds',(m',vw',vimapa'),id',cfg',
            (hw',a',d',bksv')) v'))
    (λe.
      SEP_EXISTS fmlv' fmlls'.
      ARRAY_OF fslot_TYPE fmlv' fmlls' *
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k) *
      NT_TABLE lim s1 tv *
      &(Fail_exn e ∧
        check_cstep_list cstep fmlls assg st inds (m,vw,ents) id
          (cfg0,cfg1,cfg2,mk_ord_pre cfg0.ord) (hw,a,d,bksls) = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k) *
       NT_TABLE lim s1 tv`,
      `vw`,`cfg1`,`vimapa`,`st`,`cfg0`,`m`,`inds`,`id`,`hw`,`fmlls`,`ents`,
      `d`,`cfg2`,`cstep`,`bksv`,`bksls`,`assg`,`a`,`lno`]>>
    xsimpl>>
    rw[]
    >- (first_assum (irule_at Any)>>xsimpl)>>
    qmatch_goalsub_rename_tac`ARRAY_OF fslot_TYPE aa bb * ARRAY_OF NUM _ _`>>
    qexistsl_tac[`aa`,`bb`]>>
    xsimpl)
  >- (
    xsimpl>>
    rw[]>>
    fs[Once parse_and_run_def]>>
    rename1`ARRAY_OF fslot_TYPE aa bb * STDIO _ * _ * _ ==>> _`>>
    qexistsl_tac[`k`,`lines1`,`aa`,`bb`,`s1`]>>
    xsimpl)>>
  PairCases_on`cfg'`>>
  drule_at (Pos last) npbc_listTheory.fml_bound_check_cstep_list>>
  impl_tac
  >- fs[]>>
  strip_tac>>
  qpat_x_assum`PAIR_TYPE _ _ (fmlv',_) _`
    (strip_assume_tac o REWRITE_RULE[PAIR_TYPE_def])>>
  gvs[]>>
  xmatch>>
  `LENGTH lines1 < LENGTH lines` by (
    drule parse_cstep_LENGTH>>
    simp[])>>
  qpat_x_assum`∀m. _`(qspec_then`LENGTH lines1` mp_tac)>>
  impl_tac
  >- simp[]>>
  disch_then (qspec_then`lines1` mp_tac)>>
  simp[]>>
  strip_tac>>
  xapp>>
  xsimpl>>
  qrefinel [`emp`,`vw'`,`_`,`st'`,`s1`,`m'`,`inds'`,`id'`,`hw'`,
    `forwardFD fs fd k`,`fmlls'`,`ents'`,`d'`,`(cfg'0,cfg'1,cfg'2,cfg'3)`,
    `bksv'`,`bksls'`,`assg'`,`a'`,`lno1`]>>
  xsimpl>>
  qmatch_goalsub_rename_tac`ARRAY_OF vimapn_TYPE vv ents' ==>> _`>>
  qexists_tac`vv`>>
  simp[PAIR_TYPE_def]>>
  rw[]
  >- xsimpl>>
  simp[forwardFD_o]
  >- (
    qmatch_goalsub_rename_tac
      `STDIO (forwardFD fs fd (k + kk)) * INSTREAM_LINES _ fd fdv ll _ *
       _ * _ ==>> _`>>
    qexistsl_tac[`k + kk`,`ll`]>>
    simp[]>>
    rpt (first_assum (irule_at Any))>>
    xsimpl)>>
  simp[Once parse_and_run_def]>>
  fs[]>>
  qmatch_goalsub_rename_tac
    `ARRAY_OF fslot_TYPE aa bb * NT_TABLE lim ss tv *
     STDIO (forwardFD fs fd (k + kk)) * INSTREAM_LINES _ fd fdv ll _ ==>> _`>>
  qexistsl_tac[`k + kk`,`ll`,`aa`,`bb`,`ss`]>>
  xsimpl
QED

Quote add_cakeml:
  fun fill_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_arr (Array.updateResize arr Empty i v) (i+1) vs
End

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls i iv.
  NUM i iv ∧
  LIST_TYPE fslot_TYPE ls lsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY_OF fslot_TYPE arrv arrls)
  (POSTv resv.
    ARRAY_OF fslot_TYPE resv
      (FOLDL (λacc (i,v). update_resize acc Empty v i)
        arrls (enumerate i ls)))
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto_spec (SOME (Q.SPECL[`arrls`,`arrv`,`Empty`]
    (Q.ISPEC`fslot_TYPE` ARRAY_OF_updateResize_spec)))
  >- (xsimpl>>simp[fslot_TYPE_def,NPBC_SLOT_SLOT_TYPE_def])>>
  xapp>>
  simp[]
QED

Definition rev_enum_def:
  rev_enum (s:num) (e:num) acc =
  if s < e then
    rev_enum (s+1) e (s::acc)
  else
    acc
Termination
  WF_REL_TAC`measure (λ(s,e,acc). e-s)`
End

Theorem rev_enum_rev_enumerate:
  ∀fml k acc.
  rev_enum k (LENGTH fml + k) acc =
  REVERSE (MAP FST (enumerate k fml)) ++ acc
Proof
  Induct>>rw[Once rev_enum_def]>>
  simp[miscTheory.enumerate_def]>>
  first_x_assum(qspec_then`k+1` mp_tac)>>
  simp[ADD1]
QED

val _ = translate rev_enum_def;

Definition rev_enum_full_def:
  rev_enum_full k fml =
  rev_enum k (LENGTH fml + k) []
End

Theorem rev_enum_full_rev_enumerate:
  rev_enum_full k fml =
  REVERSE (MAP FST (enumerate k fml))
Proof
  rw[rev_enum_full_def,rev_enum_rev_enumerate]
QED

val _ = translate rev_enum_full_def;

val res = translate parse_unsat_def;

val parse_unsat_side = Q.prove(
  `∀x. parse_unsat_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate parse_sat_def;

val res = translate parse_int_inf_def;
val res = translate parse_lb_def;

val parse_lb_side = Q.prove(
  `∀x. parse_lb_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate parse_ub_def;
val res = translate parse_bounds_def;

val res = translate parse_enum_def;

val parse_enum_side_def = fetch "-" "parse_enum_side_def";
val parse_enum_side = Q.prove(
  `∀x. parse_enum_side x <=> T`,
  rw[parse_enum_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate parse_concl_def;

val res = translate parse_output_def;

val endtrm = rconc (EVAL``toks «end pseudo-Boolean proof»``);

Definition last_two_ls_def:
  (last_two_ls [x;y] =
  if strip_term_line y = SOME ^endtrm
  then SOME x
  else NONE) ∧
  (last_two_ls _ = NONE)
End

val res = translate last_two_ls_def;

(* output is the first line in s
  Followed by the two conclusion lines
*)
Definition parse_output_concl_def:
  parse_output_concl s ls =
  case last_two_ls ls of NONE => NONE
  | SOME conc =>
    (case parse_output s of NONE => NONE
    | SOME output =>
      (case parse_concl conc of
        NONE => NONE
      | SOME concl =>
        SOME (output,concl)))
End

val res = translate parse_output_concl_def;

(* The output and conclusion sections, from the remaining lines of a proof *)
Definition parse_output_concl_lines_def:
  parse_output_concl_lines s ls = parse_output_concl s (MAP toks ls)
End

val res = translate parse_output_concl_lines_def;

Definition cons_line_def:
  cons_line ls =
  concatWith « »
  (MAP
    (λn. case n of INL s => s | INR i => int_to_string #"-" i) ls)
End

val res = translate cons_line_def;

Definition mk_parse_err_def:
  mk_parse_err s =
    «unable to parse line at (parse error may be later for output/conclusion section): » ^
    cons_line s
End

val res = translate mk_parse_err_def;

Definition format_err_def:
  (format_err NONE NONE = NONE) ∧
  (format_err (SOME s1) NONE = SOME s1) ∧
  (format_err NONE (SOME s2) = SOME s2) ∧
  (format_err (SOME s1) (SOME s2) = SOME (s1 ^ « ; »^ s2))
End

val res = translate format_err_def;

Quote add_cakeml:
  fun check_output_hconcl_arr
    fml obj
    fml' inds' id' ht' pres' obj' bound' dbound' chk' enum'
    fmlt prest objt
    output hconcl =
  format_err
  (check_output_arr fml' inds' id' ht'
    pres' obj' bound' dbound' chk' fmlt prest objt output)
  (check_hconcl_arr fml obj fml' obj' bound' dbound' enum' hconcl)
End

Theorem check_output_hconcl_arr_spec:
  LIST_TYPE fslot_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  (LIST_TYPE NUM) inds1 inds1v ∧
  NUM id1 id1v ∧
  ht_TYPE (hw,a,d,bksv) ht1v ∧
  obj_TYPE obj1 obj1v ∧
  pres_TYPE pres1 pres1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  NUM enum enumv ∧
  BOOL chk1 chk1v ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  pres_TYPE prest prestv ∧
  obj_TYPE objt objtv ∧
  PBC_OUTPUT_TYPE output outputv ∧
  NPBC_CHECK_HCONCL_TYPE NUM hconcl hconclv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_output_hconcl_arr" (get_ml_prog_state()))
    [fmlv; objv;
      fml1v; inds1v; id1v; ht1v; pres1v; obj1v; bound1v; dbound1v; chk1v;
      enumv; fmltv; prestv; objtv;
      outputv; hconclv]
    (ARRAY_OF fslot_TYPE fml1v fmlls * ARRAY_OF NUM bksv bksls)
    (POSTv v.
        ARRAY_OF fslot_TYPE fml1v fmlls *
        &(
        ∃s.
        (OPTION_TYPE STRING_TYPE)
        (if check_output_list fmlls inds1 id1 (hw,a,d,bksls) pres1 obj1
          bound1 dbound1 chk1 fmlt prest objt output ∧
          check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 enum hconcl
        then NONE else SOME s) v))
Proof
  rw[]>>
  xcf"check_output_hconcl_arr"(get_ml_prog_state ())>>
  xlet`POSTv v1. ARRAY_OF fslot_TYPE fml1v fmlls * ARRAY_OF NUM bksv bksls *
    &(∃s. OPTION_TYPE STRING_TYPE
      (if check_hconcl_list fml obj fmlls obj1 bound1 dbound1 enum hconcl
       then NONE else SOME s) v1)`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY_OF NUM bksv bksls`,`obj1`,`obj`,`hconcl`,`fmlls`,
      `fml`,`enum`,`dbound1`,`bound1`]>>
    xsimpl>>
    metis_tac[])>>
  xlet`POSTv v0. ARRAY_OF fslot_TYPE fml1v fmlls *
    &(∃s. OPTION_TYPE STRING_TYPE
      (if check_output_list fmlls inds1 id1 (hw,a,d,bksls) pres1 obj1 bound1
        dbound1 chk1 fmlt prest objt output then NONE else SOME s) v0)`
  >- (xapp>>xsimpl)>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  rw[]>>fs[format_err_def,OPTION_TYPE_def]>>
  metis_tac[]
QED

(* Parse the conclusion from the rest of the file, number its names and
  check it *)
Quote add_cakeml:
  fun run_concl_file fd tv lno s
    fml obj
    fml' inds' id' ht' pres' obj' bound' dbound' chk' enum'
    fmlt prest objt =
  let
    val ls = TextIO.inputLines #"\n" fd
  in
    case parse_output_concl_lines s ls of
      None => Inl (format_failure (sub_one lno) (mk_parse_err s))
    | Some (output,hc) =>
      let val hconcl = nt_hconcl tv lno hc in
      case
        check_output_hconcl_arr
        fml obj
        fml' inds' id' ht' pres' obj' bound' dbound' chk' enum'
        fmlt prest objt
        output hconcl of
        None => Inr (output,hconcl)
      | Some s => Inl (format_failure lno s)
      end
  end
End

(* TODO: may want a stronger theorem saying output and hconcl
  comes from the proof file and isn't just invented out of
  thin air, but that's somewhat annoying to state... *)
Theorem run_concl_file_spec:
  line_TYPE s sv ∧
  NUM lno lnov ∧
  LIST_TYPE fslot_TYPE fml fmlv ∧
  (LIST_TYPE NUM) inds1 inds1v ∧
  NUM id1 id1v ∧
  ht_TYPE (hw,a,d,bksv) ht1v ∧
  obj_TYPE obj objv ∧
  obj_TYPE obj1 obj1v ∧
  pres_TYPE pres1 pres1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  BOOL chk1 chk1v ∧
  NUM enum enumv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "run_concl_file" (get_ml_prog_state()))
    [fdv; tv; lnov; sv;
      fmlv; objv; fml1v; inds1v; id1v; ht1v; pres1v; obj1v; bound1v;
      dbound1v; chk1v; enumv; fmltv; prestv; objtv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv *
      ARRAY_OF fslot_TYPE fml1v fmlls * ARRAY_OF NUM bksv bksls)
    (POSTve
      (λv.
       SEP_EXISTS res st'.
       STDIO (fastForwardFD fs fd) *
       INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
       NT_TABLE lim st' tv *
       &(
        SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE (NPBC_CHECK_HCONCL_TYPE NUM)) res v ∧
        case res of
          INR (output,hconcl) =>
          ∃hc.
          parse_output_concl s (MAP toks lines) = SOME (output,hc) ∧
          name_hconcl lim hc st = SOME (hconcl,st') ∧
          check_output_list fmlls inds1 id1 (hw,a,d,bksls)
            pres1 obj1 bound1 dbound1 chk1 fmlt prest objt output ∧
          check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 enum hconcl
        | INL l => T))
      (λe.
       SEP_EXISTS st'.
       STDIO (fastForwardFD fs fd) *
       INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
       NT_TABLE lim st' tv * &Fail_exn e))
Proof
  rw[]>>
  xcf "run_concl_file" (get_ml_prog_state ())>>
  xlet`POSTv v.
    STDIO (fastForwardFD fs fd) *
    INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
    NT_TABLE lim st tv * ARRAY_OF fslot_TYPE fml1v fmlls *
    ARRAY_OF NUM bksv bksls *
    &LIST_TYPE STRING_TYPE lines v`
  >- (
    xapp_spec inputLines_spec>>
    qexists_tac`NT_TABLE lim st tv * ARRAY_OF fslot_TYPE fml1v fmlls *
      ARRAY_OF NUM bksv bksls`>>
    xsimpl>>
    qexistsl_tac[`lines`,`fs`,`fd`]>>
    xsimpl)>>
  xlet_autop>>
  fs[parse_output_concl_lines_def]>>
  namedCases_on`parse_output_concl s (MAP toks lines)`["","oc"]
  >- (
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`INL (format_failure (sub_one lno) (mk_parse_err s))`,`st`]>>
    simp[SUM_TYPE_def]>>
    xsimpl)>>
  PairCases_on`oc`>>
  fs[OPTION_TYPE_def]>>
  qpat_x_assum`PAIR_TYPE _ _ (oc0,oc1) _`
    (strip_assume_tac o REWRITE_RULE[PAIR_TYPE_def])>>
  gvs[]>>
  xmatch>>
  xlet`POSTve
    (λv. SEP_EXISTS hconcl st1.
      STDIO (fastForwardFD fs fd) *
      INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
      NT_TABLE lim st1 tv * ARRAY_OF fslot_TYPE fml1v fmlls *
      ARRAY_OF NUM bksv bksls *
      &(name_hconcl lim oc1 st = SOME (hconcl,st1) ∧
        NPBC_CHECK_HCONCL_TYPE NUM hconcl v))
    (λe. SEP_EXISTS st'.
      STDIO (fastForwardFD fs fd) *
      INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
      NT_TABLE lim st' tv * &Fail_exn e)`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[
      `STDIO (fastForwardFD fs fd) *
       INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
       ARRAY_OF fslot_TYPE fml1v fmlls * ARRAY_OF NUM bksv bksls`,
      `st`,`lim`,`oc1`,`lno`]>>
    xsimpl>>
    rw[]>>
    rename1`NT_TABLE lim st1 tv * _ * _ ==>> _`>>
    qexists_tac`st1`>>
    xsimpl)
  >- xsimpl>>
  xlet_auto >- (qrefinel [`_`,`fmlls`,`bksls`]>>xsimpl)>>
  pop_assum mp_tac>>
  IF_CASES_TAC
  >- (
    simp[OPTION_TYPE_def]>>
    strip_tac>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`INR (oc0,hconcl)`,`st1`]>>
    simp[SUM_TYPE_def,PAIR_TYPE_def]>>
    xsimpl)>>
  simp[OPTION_TYPE_def]>>
  strip_tac>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  rename1`STRING_TYPE (format_failure lno ss) _`>>
  qexistsl_tac[`INL (format_failure lno ss)`,`st1`]>>
  simp[SUM_TYPE_def]>>
  xsimpl
QED

(* Return the full conclusion, including the proven bound *)
Definition conv_boutput_hconcl_def:
  (conv_boutput_hconcl bound (INL s) = INL s) ∧
  (conv_boutput_hconcl bound (INR (out,con)) =
    INR (out, bound, hconcl_concl con))
End

val res = translate init_conf_def;

val res = translate hconcl_concl_def;
val res = translate conv_boutput_hconcl_def;

Quote add_cakeml:
  fun mk_vomap_opt_arr obj =
  case obj of None => ""
  | Some fc =>
    mk_vomap_arr (List.length (fst fc)) fc
End

Theorem mk_vomap_opt_arr_spec:
  obj_TYPE obj objv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "mk_vomap_opt_arr" (get_ml_prog_state()))
    [objv]
    (emp)
    (POSTv v. &(vomap_TYPE (mk_vomap_opt obj) v))
Proof
  rw[]>>
  xcf "mk_vomap_opt_arr" (get_ml_prog_state ())>>
  Cases_on`obj`>>fs[OPTION_TYPE_def,npbc_listTheory.mk_vomap_opt_def]>>
  xmatch
  >- (
    xlit>>xsimpl)>>
  rpt xlet_autop>>
  xapp>>xsimpl
QED

Definition get_enum_def:
  get_enum pc = pc.enum
End

val res = translate get_enum_def;

(* mx is the largest variable of the slots fml; the index starts empty,
  with the input ids 1 to LENGTH fml *)
Quote add_cakeml:
  fun check_unsat' b tv fd lno fml mx pres obj fmlt prest objt =
  let
    val id = List.length fml + 1
    val arr = Array.array (2*id) Empty
    val arr = fill_arr arr 1 fml
    val inds = rev_enum_full 1 fml
    val vimap = (id - 1, (0, Array.array (mx + 1) Vnone))
    val assg = Array.array (mx + 1) 0
    val vomap = mk_vomap_opt_arr obj
    val cfg = (init_conf True pres obj, (vomap, (0, None)))
    val ht = (0,(0,(0,Array.arrayEmpty ())))
  in
    (case check_unsat'' tv fd lno arr assg 1 inds vimap id cfg ht of
      (lno', (s, (
        (fml', (inds', (pc', (id', ht'))))))) =>
    conv_boutput_hconcl
    (get_bound pc')
    (run_concl_file fd tv lno' s
    fml obj fml' inds' id' ht'
    (get_pres pc') (get_obj pc') (get_bound pc') (get_dbound pc')
    (get_chk pc') (get_enum pc')
    fmlt prest objt))
    handle Fail s => Inl s
  end
End

Theorem parse_and_run_check_csteps_list:
  ∀lim s ss fml assg st inds vimap id cfg ht rest l s' fml' inds' pc' id'
    ht'.
  parse_and_run lim s ss fml assg st inds vimap id cfg ht =
    SOME (rest, l, s', (fml', inds', pc', id', ht')) ⇒
  ∃csteps assg' st' vimap' vomap' cw' po'.
  check_csteps_list csteps fml assg st inds vimap id cfg ht =
    SOME (fml', assg', st', inds', vimap', id', (pc', vomap', cw', po'), ht')
Proof
  ho_match_mp_tac parse_and_run_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_and_run_def]>>
  every_case_tac>>fs[]
  >- (
    rw[]>>
    qexists_tac`[]`>>
    PairCases_on`cfg`>>
    simp[npbc_listTheory.check_csteps_list_def])>>
  rw[]>>
  first_x_assum drule_all>>
  rw[]>>
  qexists_tac`y::csteps`>>
  simp[npbc_listTheory.check_csteps_list_def]
QED

(* TODO: This gap is very annoying *)
Theorem fast_forwardFD_forwardFD_exists:
  get_fd_content fs fd = SOME (c,off) ⇒
  ∃k. fastForwardFD fs fd = forwardFD fs fd k
Proof
  EVAL_TAC>>
  Cases_on`ALOOKUP fs.infds fd`>>fs[]>>
  pairarg_tac>>rw[]>>
  EVAL_TAC>>
  qexists_tac`STRLEN c-off`>>
  simp[fsFFITheory.IO_fs_component_equality]>>
  match_mp_tac AFUPDKEY_eq>>
  rw[]>>simp[]>>
  intLib.ARITH_TAC
QED

Theorem check_unsat'_spec:
  BOOL b bv ∧
  NUM lno lnov ∧
  LIST_TYPE fslot_TYPE fmls fmlv ∧
  fmls = MAP (λc. enc c T) fml ∧
  NUM mx mxv ∧
  EVERY (λs. slot_bound s (mx+1)) fmls ∧
  obj_TYPE obj objv ∧
  pres_TYPE pres presv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat'" (get_ml_prog_state()))
    [bv; tv; fdv; lnov; fmlv; mxv; presv; objv; fmltv; prestv; objtv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv)
    (POSTv v.
     SEP_EXISTS k lines' res st'.
     STDIO (forwardFD fs fd k) *
     INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
     NT_TABLE lim st' tv *
     &(
      SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
        res v ∧
      case res of
        INR (output,bound,concl) =>
        sem_concl (set fml) obj (pres_set_spt pres) concl ∧
        sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt (pres_set_spt prest) output
      | INL l => T))
Proof
  rw[]>>
  reverse (Cases_on`∃c off. get_fd_content fs fd = SOME (c,off)`)
  >- (
    fs[INSTREAM_LINES_def,INSTREAM_STR_def]>>
    xpull)>>
  fs[]>>
  xcf "check_unsat'" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv arrv.
    ARRAY_OF fslot_TYPE arrv (REPLICATE (2 * (LENGTH fml + 1)) Empty) *
    STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv`
  >- (
    xapp_spec (Q.ISPEC`fslot_TYPE` ARRAY_OF_alloc_spec)>>
    qexistsl_tac[
      `STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv`,
      `Empty`,`2 * (LENGTH fml + 1)`]>>
    xsimpl>>
    simp[fslot_TYPE_def,NPBC_SLOT_SLOT_TYPE_def])>>
  xlet_autop>>
  qabbrev_tac`fmlls =
    FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE (2 * (LENGTH fml + 1)) Empty)
      (enumerate 1 (MAP (λc. enc c T) fml))`>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv vimapa.
    ARRAY_OF vimapn_TYPE vimapa (REPLICATE (mx + 1) Vnone) *
    ARRAY_OF fslot_TYPE resv fmlls *
    STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv`
  >- (
    xapp_spec (Q.ISPEC`vimapn_TYPE` ARRAY_OF_alloc_spec)>>
    qexistsl_tac[`ARRAY_OF fslot_TYPE resv fmlls *
      STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv`,
      `Vnone`,`mx + 1`]>>
    xsimpl>>
    simp[npbc_arrayProgTheory.NPBC_LIST_VENT_TYPE_def])>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv assgv.
    ARRAY_OF NUM assgv (REPLICATE (mx + 1) 0) *
    ARRAY_OF vimapn_TYPE vimapa (REPLICATE (mx + 1) Vnone) *
    ARRAY_OF fslot_TYPE resv fmlls *
    STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_alloc_spec)>>
    qexistsl_tac[
      `ARRAY_OF vimapn_TYPE vimapa (REPLICATE (mx + 1) Vnone) *
       ARRAY_OF fslot_TYPE resv fmlls *
       STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * NT_TABLE lim st tv`,
      `0`,`mx + 1`]>>
    xsimpl>>
    simp[ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def])>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  assume_tac BOOL_True_Conv>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` ARRAY_OF_arrayEmpty_spec))
  >- xsimpl>>
  rpt xlet_autop>>
  `fml_bound fmlls (LENGTH (REPLICATE (mx+1) (0:num)))` by (
    simp[Abbr`fmlls`]>>
    irule npbc_listTheory.bound_FOLDL_update_resize>>
    simp[])>>
  qabbrev_tac`inds = rev_enum_full 1 (MAP (λc. enc c T) fml)`>>
  qabbrev_tac`vomap = mk_vomap_opt obj`>>
  qabbrev_tac`assg = REPLICATE (mx+1) (0:num)`>>
  xhandle`POSTve
    (λv. SEP_EXISTS k lines' res st'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim st' tv *
       &(SUM_TYPE STRING_TYPE
           (PAIR_TYPE PBC_OUTPUT_TYPE
             (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE)) res v ∧
         case res of
           INR (output,bound,concl) =>
           sem_concl (set fml) obj (pres_set_spt pres) concl ∧
           sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt
             (pres_set_spt prest) output
         | INL l => T))
    (λe. SEP_EXISTS k lines' st'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       NT_TABLE lim st' tv * &Fail_exn e)`
  >- (
    xlet`POSTve
      (λv.
       SEP_EXISTS k lines' lno' l s' fmlv' res0 res1 res2 res3
           res4 res5 res6 bksv' res7.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim s' tv *
         ARRAY_OF fslot_TYPE fmlv' res0 * ARRAY_OF NUM bksv' res7 *
         &(parse_and_run lim st (MAP toks lines) fmlls assg 1 inds
             (LENGTH fml,0,REPLICATE (mx+1) Vnone) (LENGTH fml + 1)
             (init_conf T pres obj, vomap, 0, NONE) (0,0,0,[]) =
             SOME (MAP toks lines',l,s',
               (res0,res1,res2,res3,(res4,res5,res6,res7))) ∧
           PAIR_TYPE NUM (PAIR_TYPE line_TYPE (PAIR_TYPE ($=)
             (PAIR_TYPE (LIST_TYPE NUM) (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
               (PAIR_TYPE NUM ht_TYPE)))))
             (lno',l,fmlv',res1,res2,res3,(res4,res5,res6,bksv')) v))
      (λe.
       SEP_EXISTS k lines' st'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim st' tv * &Fail_exn e)`
    >- (
      xapp>>
      xsimpl>>
      qexistsl_tac[`emp`,`0`,`vimapa`,`st`,`LENGTH fml`,`lines`,`lim`,`inds`,
        `LENGTH fml + 1`,`0`,`fs`,`fmlls`,`fd`,`REPLICATE (mx+1) Vnone`,`0`,
        `(init_conf T pres obj, vomap, 0, NONE)`,`av`,`[]`,`assg`,`0`,`lno`]>>
      xsimpl>>
      fs[init_conf_def,npbc_listTheory.mk_ord_pre_def,Abbr`assg`,
        ccnf_dmTheory.stamps_ok_REPLICATE,Abbr`vomap`,PAIR_TYPE_def,
        ml_translatorTheory.NUM_def,ml_translatorTheory.INT_def,
        OPTION_TYPE_def]>>
      rw[]
      >- (
        qmatch_goalsub_rename_tac
          `STDIO (forwardFD fs fd kk) * INSTREAM_LINES _ fd fdv ll _`>>
        qexistsl_tac[`kk`,`ll`]>>
        simp[]>>
        rpt (first_assum (irule_at Any))>>
        xsimpl)>>
      qmatch_goalsub_rename_tac
        `ARRAY_OF fslot_TYPE _ _ * NT_TABLE lim ss tv *
         STDIO (forwardFD fs fd kk) * INSTREAM_LINES _ fd fdv ll _`>>
      qexistsl_tac[`kk`,`ll`,`ss`]>>
      xsimpl)
    >- xsimpl>>
    gvs[]>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xlet`POSTve
      (λv. SEP_EXISTS res k st2.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
         NT_TABLE lim st2 tv *
         &(SUM_TYPE STRING_TYPE
             (PAIR_TYPE PBC_OUTPUT_TYPE (NPBC_CHECK_HCONCL_TYPE NUM)) res v ∧
           case res of
             INR (output,hconcl) =>
             check_output_list res0 res1 res3 (res4,res5,res6,res7)
               res2.pres res2.obj res2.bound res2.dbound res2.chk
               fmlt prest objt output ∧
             check_hconcl_list (MAP (λc. enc c T) fml) obj res0
               res2.obj res2.bound res2.dbound res2.enum hconcl
           | INL err => T))
      (λe. SEP_EXISTS k lines' st'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         NT_TABLE lim st' tv * &Fail_exn e)`
    >- (
      xapp>>
      xsimpl>>
      fs[get_pres_def,get_obj_def,get_bound_def,get_dbound_def,get_chk_def,
         get_enum_def]>>
      qexistsl_tac[`emp`,`s'`,`l`,`prest`,`res2.pres`,`objt`,`res2.obj`,
        `obj`,`lines'`,`lim`,`res1`,`res3`,`res4`,`forwardFD fs fd k`,`fmlt`,
        `res0`,`MAP (λc. enc c T) fml`,`fd`,`res2.enum`,`res2.dbound`,`res6`,
        `res2.chk`,`res2.bound`,`bksv'`,`res7`,`res5`,`lno'`]>>
      xsimpl>>
      `∃k'. fastForwardFD (forwardFD fs fd k) fd =
            forwardFD (forwardFD fs fd k) fd k'` by (
        match_mp_tac (GEN_ALL fast_forwardFD_forwardFD_exists)>>
        simp[fsFFIPropsTheory.get_fd_content_forwardFD])>>
      simp[forwardFD_o]>>
      rw[]
      >- fs[PAIR_TYPE_def]
      >- (
        qmatch_goalsub_rename_tac`_ * NT_TABLE lim ss tv ==>> _`>>
        qmatch_asmsub_rename_tac`SUM_TYPE _ _ rr _`>>
        qexistsl_tac[`rr`,`k + k'`,`ss`]>>
        xsimpl>>
        namedCases_on`rr`["err","oh"]>>
        gvs[]>>
        PairCases_on`oh`>>
        gvs[])>>
      qmatch_goalsub_rename_tac`_ * NT_TABLE lim ss tv ==>> _`>>
      qexistsl_tac[`k + k'`,`[]`,`ss`]>>
      xsimpl)
    >- xsimpl>>
    xlet_autop>>
    xapp_spec (fetch "-" "conv_boutput_hconcl_v_thm" |>
      INST_TYPE[alpha|->``:mlstring``, beta|->``:output``,
        gamma |->``:int option``, delta|->``:num``])>>
    xsimpl>>
    qexistsl_tac[`res`,`get_bound res2`,`OPTION_TYPE INT`,`PBC_OUTPUT_TYPE`,
                 `STRING_TYPE`,`NUM`]>>
    rw[]>>
    qexistsl_tac[`k`,`[]`,`conv_boutput_hconcl (get_bound res2) res`,`st2`]>>
    xsimpl>>
    namedCases_on`res`["err","oh"]>>
    simp[conv_boutput_hconcl_def]>>
    PairCases_on`oh`>>
    fs[conv_boutput_hconcl_def]>>
    drule parse_and_run_check_csteps_list>>
    rw[]>>
    unabbrev_all_tac>>
    fs[rev_enum_full_rev_enumerate]
    >- (
      drule_at (Pos (el 4)) npbc_listTheory.check_csteps_list_concl>>
      disch_then irule>>
      simp[]>>
      metis_tac[ccnf_dmTheory.dm_rel_FEMPTY_REPLICATE])>>
    simp[get_bound_def]>>
    drule_at (Pos (el 4)) npbc_listTheory.check_csteps_list_output>>
    disch_then irule>>
    simp[]>>
    metis_tac[ccnf_dmTheory.dm_rel_FEMPTY_REPLICATE])
  >- xsimpl>>
  fs[Fail_exn_def]>>
  xcases>>
  xcon>>
  xsimpl>>
  qexistsl_tac[`k`,`lines'`,`INL s`,`st'`]>>
  simp[SUM_TYPE_def]>>
  xsimpl
QED

(* TODO: We should check that the number of constraints is correct here *)
Definition check_f_line_def:
  check_f_line s =
  case strip_term_line s of NONE => F
  | SOME s =>
  case s of [] => F
  | x::xs => x = INL «f»
End

val r = translate check_f_line_def;

val headertrm = rconc (EVAL``toks «pseudo-Boolean proof version 3.0»``);

Definition parse_proof_header_line_def:
  parse_proof_header_line s ⇔
  s = ^headertrm
End

val r = translate parse_proof_header_line_def;

Definition check_header_full_def:
  check_header_full s (s':(mlstring + int) list option) =
  case s of NONE => SOME 1
  | SOME s =>
  case s' of NONE => SOME 2
  | SOME s' =>
  if parse_proof_header_line s then
    if check_f_line s' then NONE
    else SOME (2:num)
  else SOME 1
End

val r = translate check_header_full_def;

Quote add_cakeml:
  fun check_header fd =
  let
    val s1 = input_toks fd
    val s2 = input_toks fd
  in
  check_header_full s1 s2
  end
End

Theorem check_header_spec:
  !ss fd fdv lines fs.
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_header" (get_ml_prog_state()))
    [fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
       SEP_EXISTS k lines' res.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       &(OPTION_TYPE NUM res v))
Proof
  rw[]>>
  xcf "check_header" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP toks (oHD lines)) v)’
  >- (
    xapp_spec input_toks_spec
    \\ EVAL_TAC)>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv (TL (TL lines)) (forwardFD fs fd k) *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP toks (oHD (TL lines))) v)’
  >- (
    xapp_spec input_toks_spec
    \\ qexists_tac ‘emp’
    \\ xsimpl
    \\ metis_tac[forwardFD_o,SEP_IMP_REFL,SEP_IMP_REFL_gc]
    )>>
  xapp>>
  xsimpl>>
  metis_tac[forwardFD_o,SEP_IMP_REFL,SEP_IMP_REFL_gc]
QED

Quote add_cakeml:
  fun check_unsat_top b tv fml mx pres obj fmlt prest objt fname =
  let
    val fd = TextIO.openInSetBufferSize fname 65531
  in
    case check_header fd of
      Some n =>
      (TextIO.closeIn fd;
      Inl (format_failure n "Unable to parse header"))
    | None =>
      let val res =
        (check_unsat' b tv fd 3 fml mx pres obj fmlt prest objt)
        val close = TextIO.closeIn fd;
      in
        res
      end
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem check_unsat_top_spec:
  BOOL b bv ∧
  LIST_TYPE fslot_TYPE fmls fmlv ∧
  fmls = MAP (λc. enc c T) fml ∧
  NUM mx mxv ∧
  EVERY (λs. slot_bound s (mx+1)) fmls ∧
  obj_TYPE obj objv ∧
  pres_TYPE pres presv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top"(get_ml_prog_state()))
  [bv; tv; fmlv; mxv; presv; objv; fmltv; prestv; objtv; fv]
  (STDIO fs * NT_TABLE lim st tv)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res st'.
     NT_TABLE lim st' tv *
     &(
      SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
        res v ∧
      case res of
        INR (output,bound,concl) =>
        sem_concl (set fml) obj (pres_set_spt pres) concl ∧
        sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt (pres_set_spt prest) output
      | INL l => T))
Proof
  rw[]>>
  xcf"check_unsat_top"(get_ml_prog_state())>>
  reverse (Cases_on`STD_streams fs`)
  >- (
    fs[TextIOProofTheory.STDIO_def]>>
    xpull)>>
  reverse (Cases_on`consistentFS fs`)
  >- (
    fs[STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>
    xpull>>
    metis_tac[])>>
  reverse (Cases_on`inFS_fname fs f`)>>
  simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs * NT_TABLE lim st tv`
    >- (
      xlet_auto_spec (SOME openInSetBufferSize_STDIO_spec)>>
      xsimpl)>>
    fs[BadFileName_exn_def]>>
    xcases>>
    rw[]>>
    xlet_auto>>
    xsimpl>>
    xcon>>
    xsimpl>>
    qexistsl_tac[`INL (notfound_string f)`,`st`]>>
    simp[SUM_TYPE_def]>>
    xsimpl)>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>
  xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec
    (SOME (openInSetBufferSize_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`))>>
  xsimpl>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fd fdv lines fss`>>
  xlet`POSTv v.
    SEP_EXISTS k lines' res.
    STDIO (forwardFD fss fd k) *
    INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fss fd k) *
    NT_TABLE lim st tv *
    &OPTION_TYPE NUM res v`
  >- (
    xapp>>
    qexists_tac`NT_TABLE lim st tv`>>
    xsimpl>>
    metis_tac[SEP_IMP_REFL,SEP_IMP_REFL_gc,
              STAR_COMM])>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fd fdv _ fsss`>>
  reverse (Cases_on`res`)>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xlet`POSTv v. STDIO fs * NT_TABLE lim st tv`
    >- (
      xapp_spec closeIn_spec_lines>>
      xsimpl>>
      qexistsl_tac[`NT_TABLE lim st tv`,`lines'`,`fsss`,`fd`,`#"\n"`]>>
      conj_tac
      >- (
        unabbrev_all_tac>>
        imp_res_tac fsFFIPropsTheory.nextFD_ltX>>
        fs[]>>
        imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>
        fs[])>>
      xsimpl>>
      `validFileFD fd fsss.infds` by (
        unabbrev_all_tac>>
        simp[validFileFD_forwardFD]>>
        imp_res_tac fsFFIPropsTheory.nextFD_ltX>>
        fs[]>>
        match_mp_tac validFileFD_nextFD>>
        fs[])>>
      xsimpl>>
      rw[]>>
      unabbrev_all_tac>>
      xsimpl>>
      simp[forwardFD_ADELKEY_same]>>
      DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
      xsimpl>>
      imp_res_tac (DECIDE ``n<m:num ==> n <= m``)>>
      imp_res_tac fsFFIPropsTheory.nextFD_leX>>
      fs[])>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    rename1`STRING_TYPE (format_failure n _) _`>>
    qexistsl_tac[`INL (format_failure n «Unable to parse header»)`,`st`]>>
    simp[SUM_TYPE_def]>>
    xsimpl)>>
  xlet`POSTv v.
    SEP_EXISTS k2 lines2 res st2.
    STDIO (forwardFD fsss fd k2) *
    INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fsss fd k2) *
    NT_TABLE lim st2 tv *
    &(SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE)) res v ∧
      case res of
        INR (output,bound,concl) =>
        sem_concl (set fml) obj (pres_set_spt pres) concl ∧
        sem_output (set fml) obj (pres_set_spt pres) bound (set fmlt) objt
          (pres_set_spt prest) output
      | INL err => T)`
  >- (
    xapp>>
    xsimpl>>
    metis_tac[])>>
  xlet`POSTv v. STDIO fs * NT_TABLE lim st2 tv`
  >- (
    xapp_spec closeIn_spec_lines>>
    xsimpl>>
    qexistsl_tac[`NT_TABLE lim st2 tv`,`lines2`,`forwardFD fsss fd k2`,`fd`,
                 `#"\n"`]>>
    conj_tac
    >- (
      unabbrev_all_tac>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>
      fs[]>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>
      fs[])>>
    xsimpl>>
    `validFileFD fd (forwardFD fsss fd k2).infds` by (
      unabbrev_all_tac>>
      simp[validFileFD_forwardFD]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>
      fs[]>>
      match_mp_tac validFileFD_nextFD>>
      fs[])>>
    xsimpl>>
    rw[]>>
    unabbrev_all_tac>>
    xsimpl>>
    simp[forwardFD_ADELKEY_same]>>
    DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
    xsimpl>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``)>>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>
    fs[])>>
  xvar>>
  xsimpl>>
  qexistsl_tac[`res`,`st2`]>>
  simp[]>>
  xsimpl
QED

(*
  A string pbc -> npbc normaliser frontend

  This can be used by anything that produces a string pbc
*)

(* normalise *)
val res = translate normalise_acc_def;
val res = translate normalise_eq;
val res = translate normalise_obj_pbf_def;
val res = translate normalise_prob_def;

(* The normal forms of a numbered constraint, in reverse *)
Definition norm_pbc_def:
  norm_pbc (c:num pbc) = REVERSE (MAP inject (to_gnpbc c))
End

val res = translate norm_pbc_def;

Theorem name_norm_pbc_norm_pbc:
  name_norm_pbc c s acc =
  let (c1,s1) = name_to_num_pbc c s in (norm_pbc c1 ++ acc,s1)
Proof
  simp[name_norm_pbc_def,norm_pbc_def]>>
  pairarg_tac>>simp[]
QED

(* Stored (core) form of a list of constraints *)
Definition enc_list_def:
  enc_list fml = MAP (λc. enc c T) fml
End

val res = translate enc_list_def;

(* The largest of mx and the variables of the constraints *)
Definition max_var_list_def:
  max_var_list (fml:npbc list) mx = FOLDL (λm c. MAX m (max_var (FST c))) mx fml
End

Theorem max_var_list_bound:
  EVERY (λs. slot_bound s (max_var_list fml mx + 1)) (enc_list fml)
Proof
  `∀fml mx. mx ≤ max_var_list fml mx ∧
     EVERY (λc. max_var (FST c) ≤ max_var_list fml mx) fml` by (
    Induct>>
    rw[max_var_list_def]>>
    first_x_assum (qspec_then`MAX mx (max_var (FST h))` strip_assume_tac)>>
    gvs[max_var_list_def])>>
  simp[enc_list_def,EVERY_MAP]>>
  first_x_assum (qspecl_then[`fml`,`mx`] strip_assume_tac)>>
  pop_assum mp_tac>>
  match_mp_tac EVERY_MONOTONIC>>
  rw[]>>
  irule npbc_slotTheory.slot_bound_mono>>
  qexists_tac`max_var (FST x) + 1`>>
  simp[npbc_slotTheory.slot_bound_enc_max_var]
QED

Theorem max_var_list_MAX:
  ∀fml mx. max_var_list fml mx = MAX mx (max_var_list fml 0)
Proof
  Induct>>
  rw[max_var_list_def]>>
  once_rewrite_tac[GSYM max_var_list_def]>>
  pop_assum (fn th => once_rewrite_tac[th])>>
  rw[MAX_DEF]
QED

Theorem max_var_list_APPEND:
  max_var_list (l1 ++ l2) mx = max_var_list l1 (max_var_list l2 mx)
Proof
  rw[max_var_list_def,FOLDL_APPEND]>>
  rewrite_tac[GSYM max_var_list_def]>>
  qspecl_then[`l1`,`max_var_list l2 mx`] SUBST1_TAC max_var_list_MAX>>
  qspecl_then[`l2`,`max_var_list l1 mx`] SUBST1_TAC max_var_list_MAX>>
  qspecl_then[`l1`,`mx`] SUBST1_TAC max_var_list_MAX>>
  qspecl_then[`l2`,`mx`] SUBST1_TAC max_var_list_MAX>>
  rw[MAX_DEF]
QED

Theorem max_var_list_REVERSE:
  ∀fml mx. max_var_list (REVERSE fml) mx = max_var_list fml mx
Proof
  Induct>>
  rw[max_var_list_APPEND]>>
  simp[max_var_list_def]
QED

(* The stored (core) forms of the constraints, with the largest of mx and
  their variables *)
Definition enc_list_mv_def:
  (enc_list_mv [] acc (mx:num) = (REVERSE acc, mx)) ∧
  (enc_list_mv (c::cs) acc mx =
    let (s,m) = enc_mv c T in
    enc_list_mv cs (s::acc) (if mx < m then m else mx))
End

val res = translate enc_list_mv_def;

Theorem enc_list_mv_thm:
  ∀fml acc mx.
  enc_list_mv fml acc mx = (REVERSE acc ++ enc_list fml, max_var_list fml mx)
Proof
  Induct>>
  rw[enc_list_mv_def,enc_list_def,max_var_list_def,npbc_slotTheory.enc_mv_enc]>>
  gvs[enc_list_def,max_var_list_def,MAX_DEF]
QED

(* Numbering and normalising a problem with the table (name_norm_prob) *)
Quote add_cakeml:
  fun nt_norm_pbf tv fml acc =
    case fml of
      [] => List.rev acc
    | (c::cs) => nt_norm_pbf tv cs (norm_pbc (nt_pbc tv 0 c) @ acc)
End

Theorem nt_norm_pbf_spec:
  ∀fml fmlv s acc accv.
  LIST_TYPE (pbc_TYPE STRING_TYPE) fml fmlv ∧
  LIST_TYPE constraint_TYPE acc accv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "nt_norm_pbf" (get_ml_prog_state()))
    [tv; fmlv; accv]
    (NT_TABLE NONE s tv)
    (POSTv v. SEP_EXISTS fml1 s'.
      NT_TABLE NONE s' tv *
      &(name_norm_pbf fml s acc = (fml1,s') ∧
        LIST_TYPE constraint_TYPE fml1 v))
Proof
  Induct>>
  rw[]>>
  xcf "nt_norm_pbf" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xapp_spec (INST_TYPE [alpha |-> ``:npbc``] ListProgTheory.reverse_v_thm)>>
    xsimpl>>
    qexistsl_tac[`acc`,`constraint_TYPE`]>>
    xsimpl>>
    simp[name_norm_pbf_def]>>
    xsimpl)>>
  xlet`POSTve
    (λv. SEP_EXISTS c1 s1. NT_TABLE NONE s1 tv *
      &(name_pbc NONE h s = SOME (c1,s1) ∧ pbc_TYPE NUM c1 v))
    (λe. SEP_EXISTS s1. NT_TABLE NONE s1 tv *
      &(Fail_exn e ∧ name_pbc NONE h s = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`0`>>
    simp[])
  >- (
    xsimpl>>
    simp[name_pbc_NONE])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`s1`,`norm_pbc c1 ++ acc`]>>
  xsimpl>>
  gvs[name_pbc_NONE,name_norm_pbf_def,name_norm_pbc_norm_pbc]>>
  xsimpl
QED

(* Numbering the preserved variables of a problem with the table *)
Quote add_cakeml:
  fun nt_pres tv pres =
    case pres of
      None => None
    | Some vs => Some (list_to_num_set (nt_vars tv 0 vs))
End

Theorem nt_pres_spec:
  OPTION_TYPE (LIST_TYPE STRING_TYPE) pres presv ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "nt_pres" (get_ml_prog_state()))
    [tv; presv]
    (NT_TABLE NONE s tv)
    (POSTv v.
      NT_TABLE NONE (SND (name_to_num_pres pres s)) tv *
      &pres_TYPE (OPTION_MAP list_to_num_set (FST (name_to_num_pres pres s))) v)
Proof
  rw[]>>
  xcf "nt_pres" (get_ml_prog_state ())>>
  namedCases_on`pres`["","vs"]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon>>
    xsimpl>>
    simp[name_to_num_pres_def,OPTION_TYPE_def]>>
    xsimpl)>>
  xlet`POSTve
    (λv. SEP_EXISTS ns s1. NT_TABLE NONE s1 tv *
      &(name_vars NONE vs s = SOME (ns,s1) ∧ LIST_TYPE NUM ns v))
    (λe. SEP_EXISTS s1. NT_TABLE NONE s1 tv *
      &(Fail_exn e ∧ name_vars NONE vs s = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`0`>>
    simp[])
  >- (
    xsimpl>>
    simp[name_vars_NONE])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[name_to_num_pres_def,name_vars_NONE,OPTION_TYPE_def]>>
  xsimpl
QED

(* Numbering the objective of a problem with the table *)
Quote add_cakeml:
  fun nt_obj tv obj =
    case obj of
      None => None
    | Some (f,c) => Some (nt_lin tv 0 f,c)
End

Theorem nt_obj_spec:
  OPTION_TYPE (PAIR_TYPE (lin_TYPE STRING_TYPE) INT) obj objv ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "nt_obj" (get_ml_prog_state()))
    [tv; objv]
    (NT_TABLE NONE s tv)
    (POSTv v.
      NT_TABLE NONE (SND (name_to_num_obj obj s)) tv *
      &OPTION_TYPE (PAIR_TYPE (lin_TYPE NUM) INT)
        (FST (name_to_num_obj obj s)) v)
Proof
  rw[]>>
  xcf "nt_obj" (get_ml_prog_state ())>>
  namedCases_on`obj`["","fc"]>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    simp[name_to_num_obj_def,OPTION_TYPE_def]>>
    xsimpl)>>
  PairCases_on`fc`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λv. SEP_EXISTS xs1 s1. NT_TABLE NONE s1 tv *
      &(name_lin NONE fc0 s = SOME (xs1,s1) ∧ lin_TYPE NUM xs1 v))
    (λe. SEP_EXISTS s1. NT_TABLE NONE s1 tv *
      &(Fail_exn e ∧ name_lin NONE fc0 s = NONE))`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`0`>>
    simp[])
  >- (
    xsimpl>>
    simp[name_lin_NONE])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[name_to_num_obj_def,name_lin_NONE,OPTION_TYPE_def,PAIR_TYPE_def]>>
  xsimpl
QED

Quote add_cakeml:
  fun nt_norm_prob tv prob =
    case prob of (pres,(obj,fml)) =>
    let
      val pres1 = nt_pres tv pres
      val obj1 = nt_obj tv obj
      val fml1 = nt_norm_pbf tv fml []
    in
      (pres1,(normalise_obj obj1,fml1))
    end
End

Overload "prob_TYPE" = ``
  PAIR_TYPE
  (OPTION_TYPE
    (LIST_TYPE STRING_TYPE))
  (PAIR_TYPE
  (OPTION_TYPE
    (PAIR_TYPE
    (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
    INT))
  (LIST_TYPE
    (PAIR_TYPE (PBC_PBHD_TYPE STRING_TYPE)
      (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
        INT))))``

Overload "norm_prob_TYPE" = ``
  PAIR_TYPE pres_TYPE (PAIR_TYPE obj_TYPE (LIST_TYPE constraint_TYPE))``

Theorem nt_norm_prob_spec:
  prob_TYPE prob probv ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"nt_norm_prob" (get_ml_prog_state()))
  [tv; probv]
  (NT_TABLE NONE s tv)
  (POSTv v.
     SEP_EXISTS nprob s'.
     NT_TABLE NONE s' tv *
     &(name_norm_prob prob s = (nprob,s') ∧ norm_prob_TYPE nprob v))
Proof
  rw[]>>
  xcf "nt_norm_prob" (get_ml_prog_state ())>>
  PairCases_on`prob`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  Cases_on`name_to_num_pres prob0 s`>>
  fs[]>>
  rename1`name_to_num_pres prob0 s = (pres1,s1)`>>
  xlet_autop>>
  Cases_on`name_to_num_obj prob1 s1`>>
  fs[]>>
  rename1`name_to_num_obj prob1 s1 = (obj1,s2)`>>
  xlet_autop>>
  xlet`POSTv v. SEP_EXISTS fml1 s3.
    NT_TABLE NONE s3 tv *
    &(name_norm_pbf prob2 s2 [] = (fml1,s3) ∧
      LIST_TYPE constraint_TYPE fml1 v)`
  >- (
    xapp>>
    xsimpl>>
    simp[LIST_TYPE_def])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[name_norm_prob_def,PAIR_TYPE_def]>>
  xsimpl
QED

Quote add_cakeml:
  fun check_unsat_top_norm b prob probt fname =
  let
    val tv = nt_new None 0
    val nprob = nt_norm_prob tv prob
    val nprobt = nt_norm_prob tv probt
  in
    case nprob of (pres,(obj,fml)) =>
    case nprobt of (prest,(objt,fmlt)) =>
    case enc_list_mv fml [] 0 of (fmls,mx) =>
    check_unsat_top b tv fmls mx pres obj fmlt prest objt fname
  end
End

Theorem check_unsat_top_norm_spec:
  BOOL b bv ∧
  prob_TYPE prob probv ∧
  prob_TYPE probt probtv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top_norm"
    (get_ml_prog_state()))
  [bv; probv; probtv; fv]
  (STDIO fs)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE PBC_OUTPUT_TYPE
           (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
         res v ∧
       case res of
         INR (output,bound,concl) =>
         sem_concl (set (SND (SND prob))) (FST (SND prob))
            (pres_set_list (FST prob)) concl ∧
         sem_output (set (SND (SND prob))) (FST (SND prob))
            (pres_set_list (FST prob)) bound
            (set (SND (SND probt))) (FST (SND probt))
            (pres_set_list (FST probt)) output
       | INL l => T))
Proof
  rw[]>>
  xcf"check_unsat_top_norm"(get_ml_prog_state())>>
  rpt xlet_autop>>
  xlet`POSTv tv. STDIO fs * NT_TABLE NONE (nt_init 0) tv`
  >- (
    xapp>>
    xsimpl>>
    qexists_tac`NONE`>>
    simp[OPTION_TYPE_def]>>
    xsimpl)>>
  xlet`POSTv v. STDIO fs *
    SEP_EXISTS nprob s1. NT_TABLE NONE s1 tv *
    &(name_norm_prob prob (nt_init 0) = (nprob,s1) ∧ norm_prob_TYPE nprob v)`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`STDIO fs`,`nt_init 0`,`prob`]>>
    xsimpl>>
    rw[]>>
    simp[]>>
    xsimpl)>>
  xlet`POSTv v. STDIO fs *
    SEP_EXISTS nprobt s2. NT_TABLE NONE s2 tv *
    &(name_norm_prob probt s1 = (nprobt,s2) ∧ norm_prob_TYPE nprobt v)`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`STDIO fs`,`s1`,`probt`]>>
    xsimpl>>
    rw[]>>
    simp[]>>
    xsimpl)>>
  PairCases_on`nprob`>>
  PairCases_on`nprobt`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv v. STDIO fs * NT_TABLE NONE s2 tv *
    &PAIR_TYPE (LIST_TYPE NPBC_SLOT_SLOT_TYPE) NUM (enc_list_mv nprob2 [] 0) v`
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac[`[]`,`nprob2`]>>
    simp[LIST_TYPE_def])>>
  assume_tac (Q.INST [`mx`|->`0`,`fml`|->`nprob2`] max_var_list_bound)>>
  gvs[enc_list_mv_thm,enc_list_def,PAIR_TYPE_def]>>
  xmatch>>
  rename1`LIST_TYPE NPBC_SLOT_SLOT_TYPE _ fmlsv`>>
  `LIST_TYPE fslot_TYPE (MAP (λc. enc c T) nprob2) fmlsv` by
    gvs[npbc_arrayProgTheory.LIST_TYPE_fslot_TYPE,EVERY_MAP]>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`s2`,`nprobt0`,`nprob0`,`nprobt1`,`nprob1`,`NONE`,`fs`,
               `nprobt2`,`nprob2`,`b`,`f`,`max_var_list nprob2 0`]>>
  xsimpl>>
  rw[]>>
  qexists_tac`x`>>
  Cases_on`x`>>
  fs[]>>
  rename1`INR y`>>
  PairCases_on`y`>>
  fs[]>>
  PairCases_on`prob`>>
  PairCases_on`probt`>>
  assume_tac (Q.INST [`n`|->`0`] nt_init_ok)>>
  drule_all name_norm_prob_2_sem>>
  simp[]
QED

Overload "annot_prob_TYPE" = ``
  PAIR_TYPE
  (OPTION_TYPE
    (LIST_TYPE STRING_TYPE))
  (PAIR_TYPE
  (OPTION_TYPE
    (PAIR_TYPE
    (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
    INT))
  (LIST_TYPE
    (PAIR_TYPE (LIST_TYPE STRING_TYPE)
    ((PAIR_TYPE (PBC_PBHD_TYPE STRING_TYPE)
      (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
        INT))))))``

val res = translate lit_string_def;
val res = translate lhs_string_def;
val res = translate op_string_def;
val res = translate rel_string_def;
val res = translate lits_string_def;
val res = translate pbc_string_def;
val res = translate annot_pbc_string_def;
val res = translate obj_string_def;
val res = translate pb_parseTheory.pres_string_def;
val res = translate print_prob_def;
val res = translate print_annot_prob_def;
val res = translate strip_annot_prob_def;

(* An empty formula *)
Definition default_prob_def:
  default_prob = (NONE,NONE,[]):
    mlstring list option #
    ((int # mlstring pbc$lit) list # int) option #
    (mlstring pbhd # (int # mlstring pbc$lit) list # int) list
End

val res = translate default_prob_def;

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
(*"*)
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm = mlstring_from_proc "git" ["-C", Globals.HOLDIR, "rev-parse", "HEAD"]

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

Definition print_option_def:
  print_option h x =
    case x of
      NONE => «»
    | SOME y => h ^ « » ^ y ^ «\n»
End

val current_build_info_str_tm = EVAL ``
    let commit = print_option «CakeML:» ^current_version_tm in
    let hol    = print_option «HOL4:  » ^hol_version_tm in
    let poly   = print_option «PolyML:» ^poly_version_tm in
      concat
        [ «CakePB\n\n»
        ; «Version details:\n»
        ; ^date_tm; «\n»
        ; commit; hol; poly ]``
  |> concl |> rhs

Definition current_build_info_str_def:
  current_build_info_str = ^current_build_info_str_tm
End

val res = translate current_build_info_str_def;

Definition mk_usage_string_def:
  mk_usage_string s = current_build_info_str ^ «\n\n» ^ s
End

val res = translate mk_usage_string_def;
