(*
  Refine npbc_list to npbc_array
*)
open preamble basis UnsafeProgTheory UnsafeProofTheory npbcTheory npbc_listTheory;

val _ = new_theory "npbc_arrayProg"

val _ = translation_extends"UnsafeProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val _ = process_topdecs `
  exception Fail string;
` |> append_prog

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``"Fail"``

Definition Fail_exn_def:
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)
End

val _ = register_type ``:constr``
val _ = register_type ``:lstep ``
val _ = register_type ``:sstep ``

Definition format_failure_def:
  format_failure (lno:num) s =
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit " (error may be in subproofs). Reason: " ^ s ^ strlit"\n"
End

val r = translate format_failure_def;

val r = translate OPTION_MAP2_DEF;

(* Translate steps in check_cutting *)
val r = translate listTheory.REV_DEF;
val r = translate offset_def;
val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate delete_def;
val res = translate insert_def;
val res = translate lookup_def;
val res = translate map_def;

val res = translate spt_center_def;
val res = translate spt_right_def;
val res = translate spt_left_def;
val res = translate spts_to_alist_add_pause_def;
val res = translate spts_to_alist_aux_def;
val res = translate spts_to_alist_def;
val res = translate toSortedAList_def;

val res = translate lrnext_def;
val res = translate foldi_def;
val res = translate toAList_def;

val r = translate add_terms_def;
val r = translate add_listsLR_def;
val r = translate add_listsLR_thm;
val r = translate (add_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

val r = translate multiply_def;

val r = translate IQ_def;
val r = translate div_ceiling_def;
val r = translate arithmeticTheory.CEILING_DIV_def ;
val r = translate divide_def;

val divide_side = Q.prove(
  `∀x y. divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  intLib.ARITH_TAC
  ) |> update_precondition

val r = translate abs_min_def;
val r = translate saturate_def;

val r = translate (weaken_aux_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

Triviality weaken_aux_ind:
  weaken_aux_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "weaken_aux_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = weaken_aux_ind |> update_precondition;

val r = translate weaken_def;

val r = translate mergesortTheory.sort2_def;
val r = translate mergesortTheory.sort3_def;
val r = translate mergesortTheory.merge_def;
val r = translate DROP_def;
val r = translate (mergesortTheory.mergesortN_def |> SIMP_RULE std_ss [DIV2_def]);

Triviality mergesortn_ind:
  mergesortn_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "mergesortn_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, DIV2_def]
QED

val _ = mergesortn_ind |> update_precondition;

Triviality mergesortn_side:
  ∀x y z.
  mergesortn_side x y z
Proof
  completeInduct_on`y`>>
  rw[Once (fetch "-" "mergesortn_side_def")]>>
  simp[arithmeticTheory.DIV2_def]
  >- (
    first_x_assum match_mp_tac>>
    simp[]>>
    match_mp_tac dividesTheory.DIV_POS>>
    simp[])
  >>
    match_mp_tac DIV_LESS_EQ>>
    simp[]
QED
val _ = mergesortn_side |> update_precondition;

val r = translate mergesortTheory.mergesort_def;

val r = translate mergesortTheory.sort2_tail_def;
val r = translate mergesortTheory.sort3_tail_def;
val r = translate mergesortTheory.merge_tail_def;
val r = translate (mergesortTheory.mergesortN_tail_def |> SIMP_RULE std_ss [DIV2_def]);

Triviality mergesortn_tail_ind:
  mergesortn_tail_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "mergesortn_tail_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, DIV2_def]
QED

val _ = mergesortn_tail_ind |> update_precondition;

Triviality mergesortn_tail_side:
  ∀w x y z.
  mergesortn_tail_side w x y z
Proof
  completeInduct_on`y`>>
  rw[Once (fetch "-" "mergesortn_tail_side_def")]>>
  simp[arithmeticTheory.DIV2_def]
  >- (
    first_x_assum match_mp_tac>>
    simp[]>>
    match_mp_tac dividesTheory.DIV_POS>>
    simp[])
  >>
    match_mp_tac DIV_LESS_EQ>>
    simp[]
QED
val _ = mergesortn_tail_side |> update_precondition;

val r = translate mergesortTheory.mergesort_tail_def;

val r = translate npbc_checkTheory.weaken_sorted_def;

val r = translate npbc_checkTheory.fuse_weaken_def;
val r = translate npbc_checkTheory.sing_lit_def;
val r = translate npbc_checkTheory.clean_triv_def;

Definition lookup_err_string_def:
  lookup_err_string b =
    if b then
      strlit"invalid core constraint id: "
    else strlit"invalid constraint id: "
End

val r = translate lookup_err_string_def;

(* Overload notation for long _TYPE relations *)
Overload "constraint_TYPE" = ``PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) NUM``
Overload "bconstraint_TYPE" = ``PAIR_TYPE constraint_TYPE BOOL``

val NPBC_CHECK_CONSTR_TYPE_def = fetch "-" "NPBC_CHECK_CONSTR_TYPE_def";
val PBC_LIT_TYPE_def = fetch "-" "PBC_LIT_TYPE_def"

(* option version *)
val lookup_core_only_arr = process_topdecs`
  fun lookup_core_only_arr b fml n =
  case Array.lookup fml None n of
    None => None
  | Some (c,b') =>
    if b then
      (if b' then Some c
       else None)
    else Some c` |> append_prog;

Theorem lookup_core_only_arr_spec:
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lookup_core_only_arr" (get_ml_prog_state()))
    [bv; fmlv; nv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(
        OPTION_TYPE constraint_TYPE
        (lookup_core_only_list b fmlls n) v))
Proof
  rw[lookup_core_only_list_def]>>
  xcf"lookup_core_only_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE (any_el n fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  qpat_x_assum`Conv _ _ = any_el _ _ _` (assume_tac o SYM)>>
  xmatch>>
  reverse xif
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def]) >>
  reverse xif
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def]) >>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def]
QED

val lookup_core_only_err_arr = process_topdecs`
  fun lookup_core_only_err_arr lno b fml n =
  case Array.lookup fml None n of
    None =>
      raise Fail (format_failure lno (lookup_err_string b ^ Int.toString n))
  | Some (c,b') =>
    if b then
      (if b' then c
       else
        raise Fail (format_failure lno (lookup_err_string b ^ Int.toString n)))
    else c` |> append_prog;

Theorem lookup_core_only_err_arr_spec:
  NUM lno lnov ∧
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lookup_core_only_err_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; nv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case lookup_core_only_list b fmlls n of NONE => F
          | SOME x => constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          lookup_core_only_list b fmlls n = NONE)))
Proof
  rw[lookup_core_only_list_def]>>
  xcf"lookup_core_only_err_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE (any_el n fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  qpat_x_assum`Conv _ _ = any_el _ _ _` (assume_tac o SYM)>>
  xmatch>>
  reverse xif
  >- (
    xvar>>xsimpl)>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  xvar>>xsimpl
QED

(* Throws an error *)
val check_cutting_arr = process_topdecs`
  fun check_cutting_arr lno b fml constr =
  case constr of
    Id n =>
    lookup_core_only_err_arr lno b fml n
  | Add c1 c2 =>
    add (check_cutting_arr lno b fml c1)
      (check_cutting_arr lno b fml c2)
  | Mul c k =>
    multiply (check_cutting_arr lno b fml c) k
  | Div_1 c k =>
    if k <> 0 then
      divide (check_cutting_arr lno b fml c) k
    else raise Fail (format_failure lno ("divide by zero"))
  | Sat c =>
    saturate (check_cutting_arr lno b fml c)
  | Lit l =>
    (case l of
      Pos v => ([(1,v)], 0)
    | Neg v => ([(~1,v)], 0))
  | Weak c vs =>
    weaken_sorted (check_cutting_arr lno b fml c) vs
  | Triv ls => (clean_triv ls)` |> append_prog

Theorem check_cutting_arr_spec:
  ∀constr constrv lno lnov b bv fmlls fmllsv fmlv.
  NPBC_CHECK_CONSTR_TYPE constr constrv ∧
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cutting_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; constrv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case check_cutting_list b fmlls constr of NONE => F
          | SOME x => constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          check_cutting_list b fmlls constr = NONE)))
Proof
  Induct_on`constr` >> rw[]>>
  xcf "check_cutting_arr" (get_ml_prog_state ())
  >- ( (* Id *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    metis_tac[])
  >- ( (* Add *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >- ( (* Mul *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >- ( (* Div *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    reverse IF_CASES_TAC>>xif>>asm_exists_tac>>fs[]
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>metis_tac[])>>
    xlet_autop>- xsimpl>>
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    metis_tac[])
  >- ( (* Sat *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp_spec
    (fetch "-" "saturate_v_thm" |> INST_TYPE [alpha|->``:num``])>>
    xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    metis_tac[])
  >- ( (* Lit *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    Cases_on`l`>>
    fs[PBC_LIT_TYPE_def]>>xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def,PAIR_TYPE_def])
  >- ( (* Weak *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp_spec
    (fetch "-" "weaken_sorted_v_thm" |> INST_TYPE [alpha|->``:num``])>>
    xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    first_x_assum (irule_at Any)>>
    metis_tac[EqualityType_NUM_BOOL])
  >- ( (* Triv *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    metis_tac[]
  )
QED

(*
val res = translate npbcTheory.add_terms_spt_def;
val res = translate npbcTheory.lookup_default_def;
val res = translate npbcTheory.add_lists_spt_def;
val res = translate npbcTheory.add_spt_def;
val res = translate npbc_checkTheory.spt_of_list_def;

val res = translate npbcTheory.multiply_spt_def;
val res = translate npbcTheory.divide_spt_def;

val divide_spt_side = Q.prove(
  `∀x y. divide_spt_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  intLib.ARITH_TAC
  ) |> update_precondition

val res = translate npbcTheory.saturate_spt_def;
val res = translate npbcTheory.weaken_spt_def;
val res = translate npbc_checkTheory.spt_of_lit_def

val check_cutting_spt_arr = process_topdecs`
  fun check_cutting_spt_arr lno fml constr =
  case constr of
    Id n =>
    (case Array.lookup fml None n of
      None =>
        raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some c => spt_of_list c)
  | Add c1 c2 =>
    add_spt
      (check_cutting_spt_arr lno fml c1)
      (check_cutting_arr lno fml c2)
  | Mul c k =>
    multiply_spt (check_cutting_spt_arr lno fml c) k
  | Div_1 c k =>
    if k <> 0 then
      divide_spt (check_cutting_spt_arr lno fml c) k
    else raise Fail (format_failure lno ("divide by zero"))
  | Sat c =>
    saturate_spt (check_cutting_spt_arr lno fml c)
  | Weak c var =>
    weaken_spt (check_cutting_spt_arr lno fml c) var
  | Lit l => spt_of_lit l
    ` |> append_prog

val res = translate npbc_checkTheory.constraint_of_spt_def;

val check_cutting_alt_arr = process_topdecs`
  fun check_cutting_alt_arr lno fml constr =
  constraint_of_spt (check_cutting_spt_arr lno fml constr)` |> append_prog;
*)

(* Translation for pb checking *)

val r = translate (lslack_def |> SIMP_RULE std_ss [MEMBER_INTRO, o_DEF]);
val r = translate (check_contradiction_def |> SIMP_RULE std_ss[LET_DEF]);

val delete_arr = process_topdecs`
  fun delete_arr i fml =
    if Array.length fml <= i then ()
    else
      (Unsafe.update fml i None)` |> append_prog

Theorem delete_arr_spec:
  NUM i iv ∧
  LIST_REL (OPTION_TYPE a) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_arr" (get_ml_prog_state()))
    [iv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE a) (delete_list i fmlls) fmllsv') )
Proof
  rw[]>>
  xcf "delete_arr" (get_ml_prog_state ())>>
  simp[delete_list_def]>>
  xlet_autop>>
  xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xif>-
    (xcon>>xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]
QED

val list_delete_arr = process_topdecs`
  fun list_delete_arr ls fml =
    case ls of
      [] => ()
    | (i::is) =>
      (delete_arr i fml; list_delete_arr is fml)` |> append_prog

Theorem list_delete_arr_spec:
  ∀ls lsv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE a) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_delete_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE a) (list_delete_list ls fmlls) fmllsv') )
Proof
  Induct>>
  rw[]>>simp[list_delete_list_def]>>
  xcf "list_delete_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl) >>
  xmatch>>
  xlet_autop>>
  xapp>>
  metis_tac[]
QED

Definition mk_ids_def:
  mk_ids id_start (id_end:num) =
  if id_start < id_end then id_start::mk_ids (id_start+1) id_end else []
Termination
  WF_REL_TAC `measure (λ(a,b). b-a)`
End

val _ = translate mk_ids_def;

val rollback_arr = process_topdecs`
  fun rollback_arr fml id_start id_end =
  list_delete_arr (mk_ids id_start id_end) fml` |> append_prog

Theorem mk_ids_MAP_COUNT_LIST:
  ∀start end.
  mk_ids start end =
  MAP ($+ start) (COUNT_LIST (end − start))
Proof
  ho_match_mp_tac mk_ids_ind>>rw[]>>
  simp[Once mk_ids_def]>>rw[]>>gs[]>>
  Cases_on`end-start`>>fs[COUNT_LIST_def]>>
  `end-(start+1) = n` by fs[]>>
  simp[MAP_MAP_o,MAP_EQ_f]
QED

Theorem rollback_arr_spec:
  NUM start startv ∧
  NUM end endv ∧
  LIST_REL (OPTION_TYPE a) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rollback_arr" (get_ml_prog_state()))
    [fmlv;startv; endv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE a) (rollback fmlls start end) fmllsv') )
Proof
  rw[]>>
  xcf"rollback_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>
  asm_exists_tac>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  rw[]>>fs[rollback_def]>>
  metis_tac[mk_ids_MAP_COUNT_LIST]
QED

val res = translate (not_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])
val res = translate sorted_insert_def;

(* Possibly raise error here directly *)
val check_contradiction_fml_arr = process_topdecs`
  fun check_contradiction_fml_arr b fml n =
  case lookup_core_only_arr b fml n of
    None => False
  | Some c =>
    check_contradiction c` |> append_prog

Theorem check_contradiction_fml_arr_spec:
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_contradiction_fml_arr" (get_ml_prog_state()))
    [bv; fmlv; nv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
        ARRAY fmlv fmllsv *
        &(
        BOOL (check_contradiction_fml_list b fmlls n) v))
Proof
  rw[check_contradiction_fml_list_def]>>
  xcf"check_contradiction_fml_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  Cases_on`lookup_core_only_list b fmlls n`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon>>
    xsimpl)>>
  xapp>>xsimpl>>
  asm_exists_tac>>rw[]
QED

(* TODO: copied *)
Theorem LIST_REL_update_resize:
  LIST_REL R a b ∧ R a1 b1 ∧ R a2 b2 ⇒
  LIST_REL R (update_resize a a1 a2 n) (update_resize b b1 b2 n)
Proof
  rw[update_resize_def]
  >- (
    match_mp_tac EVERY2_LUPDATE_same>>
    fs[])
  >- fs[LIST_REL_EL_EQN]
  >- fs[LIST_REL_EL_EQN]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[]>>
  match_mp_tac EVERY2_APPEND_suff>>
  fs[LIST_REL_EL_EQN]>>rw[]>>
  fs[EL_REPLICATE]
QED

Definition coeff_lit_string_def:
  coeff_lit_string (c,v:var) =
    if c < 0
    then toString (Num ~c) ^ strlit" ~x"^ toString v
    else toString (Num c) ^ strlit" x"^ toString v
End

Definition npbc_lhs_string_def:
  npbc_lhs_string (xs: ((int # var) list)) =
  concatWith (strlit" ")
    (MAP coeff_lit_string xs)
End

Definition npbc_string_def:
  (npbc_string (xs,i:num) =
    concat [
      npbc_lhs_string xs;
      strlit" >= ";
      toString  i; strlit ";"])
End

Definition err_check_string_def:
  err_check_string c c' =
  concat[
    strlit"constraint id check failed. expect: ";
    npbc_string c;
    strlit" got: ";
    npbc_string c']
End

val res = translate coeff_lit_string_def;

val coeff_lit_string_side = Q.prove(
  `∀n. coeff_lit_string_side n ⇔ T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
) |> update_precondition;

val res = translate npbc_lhs_string_def;
val res = translate npbc_string_def;
val res = translate err_check_string_def;

val every_less = process_topdecs`
  fun every_less mindel fml ls =
  (case ls of [] => True
  | (i::is) =>
    case lookup_core_only_arr True fml i of
      None =>
        mindel <= i andalso
        every_less mindel fml is
    | Some c => False
  )` |> append_prog;

Theorem every_less_spec:
  ∀fmlls ls mindel lsv fmlv fmllsv mindelv.
  NUM mindel mindelv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) ls lsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_less" (get_ml_prog_state()))
    [mindelv; fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(BOOL
         (EVERY (λid. mindel ≤ id ∧
          lookup_core_only_list T fmlls id = NONE) ls) v))
Proof
  Induct_on`ls`>>
  rw[]>>
  xcf"every_less"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >-
    (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(
        OPTION_TYPE constraint_TYPE
        (lookup_core_only_list T fmlls h) v)`
  >-
    (xapp>>xsimpl)>>
  Cases_on`lookup_core_only_list T fmlls h`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xlet_autop>>xlog>>
    rw[]
    >-
      (xapp>>xsimpl)>>
    xsimpl>>
    gvs[])>>
  xcon>>
  xsimpl
QED

val opt_update_arr = process_topdecs`
  fun opt_update_arr fml c id =
    case c of
      None => (fml,id)
    | Some cc =>
    (Array.updateResize fml None id (Some cc), id+1)`
    |> append_prog;

Theorem ARRAY_refl:
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Theorem W8ARRAY_refl:
  (W8ARRAY fml fmllsv ==>> W8ARRAY fml fmllsv) ∧
  (W8ARRAY fml fmllsv ==>> W8ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Theorem ARRAY_W8ARRAY_refl:
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros ==>> ARRAY fml fmllsv * W8ARRAY zerosv zeros ) ∧
  (W8ARRAY zerosv zeros * ARRAY fml fmllsv ==>> ARRAY fml fmllsv * W8ARRAY zerosv zeros) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros ==>> ARRAY fml fmllsv * W8ARRAY zerosv zeros * GC) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros ==>> W8ARRAY zerosv zeros * ARRAY fml fmllsv * GC) ∧
  (W8ARRAY zerosv zeros * ARRAY fml fmllsv ==>> ARRAY fml fmllsv * W8ARRAY zerosv zeros * GC) ∧
  (W8ARRAY zerosv zeros * ARRAY fml fmllsv * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv) ∧
  (W8ARRAY zerosv zeros * ARRAY fml fmllsv * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv * GC)  ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv * GC) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv ==>>
    W8ARRAY zerosv zeros * ARRAY fml fmllsv * ARRAY vimapv vimaplsv) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv ==>>
    W8ARRAY zerosv zeros * ARRAY fml fmllsv * ARRAY vimapv vimaplsv * GC) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv ==>>
    ARRAY vimapv vimaplsv * W8ARRAY zerosv zeros * ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv ==>>
    ARRAY vimapv vimaplsv * W8ARRAY zerosv zeros * ARRAY fml fmllsv * GC) ∧
  (ARRAY fml fmllsv * ARRAY vimapv vimaplsv * W8ARRAY zerosv zeros ==>>
    ARRAY vimapv vimaplsv * W8ARRAY zerosv zeros * ARRAY fml fmllsv)
Proof
  rw[]>>
  xsimpl
QED

Theorem opt_update_arr_spec:
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (OPTION_TYPE bconstraint_TYPE) c cv ∧
  NUM id idv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "opt_update_arr" (get_ml_prog_state()))
    [fmlv; cv; idv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          PAIR_TYPE
            (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            NUM
            (opt_update fmlls c id) v))
Proof
  Cases_on`c`>>rw[]>>
  xcf"opt_update_arr"(get_ml_prog_state ())>>
  fs[OPTION_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_refl])>>
  rpt xlet_autop>>
  xlet_auto>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  qmatch_goalsub_abbrev_tac`ARRAY _ lss`>>
  qexists_tac`lss`>>xsimpl>>
  simp[Abbr`lss`]>>
  match_mp_tac LIST_REL_update_resize>>simp[OPTION_TYPE_def]
QED

Definition eq_zw_def:
  eq_zw v ⇔
  v = (0w:word8)
End

val res = translate eq_zw_def;

Definition abs_def:
  abs i = Num (ABS i)
End

val res = translate abs_def;

Definition add_to_acc_def:
  add_to_acc i v k acc =
  if v = (1w:word8) <=> i < (0:int) then acc
  else acc + (k:num)
End

val res = translate add_to_acc_def;

val rup_pass1_arr = process_topdecs`
  fun rup_pass1_arr assg ls acc ys m =
    case ls of [] => (acc,ys,m)
  | inn::xs =>
    case inn of (i,n) =>
    let
      val k = abs i in
      if n < Word8Array.length assg
      then
        let val v = Unsafe.w8sub assg n in
          if eq_zw v then
            rup_pass1_arr assg xs (acc + k) ((k,inn)::ys) (max m n)
          else
            rup_pass1_arr assg xs (add_to_acc i v k acc) ys m
        end
      else
        rup_pass1_arr assg xs (acc + k) ((k,inn)::ys) (max m n)
    end` |> append_prog;

Theorem rup_pass1_arr_spec:
  ∀ls lsv acc ys m accv ysv mv.
  LIST_TYPE (PAIR_TYPE INT NUM) ls lsv ∧
  NUM acc accv ∧
  LIST_TYPE (PAIR_TYPE NUM (PAIR_TYPE INT NUM)) ys ysv ∧
  NUM m mv ∧
  rup_pass1_list assg ls acc ys m = (acc',ys',m') ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rup_pass1_arr" (get_ml_prog_state()))
    [assgv; lsv; accv; ysv; mv]
    (W8ARRAY assgv assg)
    (POSTv v.
      W8ARRAY assgv assg *
      SEP_EXISTS v1 v2 v3.
      &(
        v = Conv NONE [v1; v2; v3] ∧
        NUM acc' v1 ∧
        LIST_TYPE (PAIR_TYPE NUM (PAIR_TYPE INT NUM)) ys' v2 ∧
        NUM m' v3)
    )
Proof
  Induct>>rw[]>>
  xcf"rup_pass1_arr"(get_ml_prog_state ())>>
  gvs[LIST_TYPE_def,rup_pass1_list_def]>>
  xmatch
  >- (
    xcon>>xsimpl)>>
  PairCases_on`h`>>
  gvs[PAIR_TYPE_def,rup_pass1_list_def]>>
  xmatch>>
  rpt xlet_autop>>
  gvs[abs_def]>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xapp>>gvs[]>>
    first_x_assum (irule_at (Pos (el 1)))>>
    simp[LIST_TYPE_def,PAIR_TYPE_def])>>
  gvs[]>>
  rpt xlet_autop>>
  gvs[eq_zw_def]>>xif
  >- (
    rpt xlet_autop>>
    xapp>>gvs[]>>
    first_x_assum (irule_at (Pos (el 1)))>>
    simp[LIST_TYPE_def,PAIR_TYPE_def])>>
  xlet_autop>>
  xapp>>gvs[]>>
  every_case_tac>>gvs[add_to_acc_def]>>
  first_x_assum (irule_at (Pos (el 1)))>>
  gvs[]
QED

Definition mk_flag_def:
  mk_flag (i: int) =
  (if 0 ≤ i then 1w else (2w:word8))
End

val res = translate mk_flag_def;

val rup_pass2_arr = process_topdecs`
  fun rup_pass2_arr assg max ls l changes =
    case ls of [] => changes
  | (k,(i,n))::ys =>
    if max < l + k then
      (Unsafe.w8update assg n (mk_flag i);
        rup_pass2_arr assg max ys l (n::changes))
    else
      rup_pass2_arr assg max ys l changes` |> append_prog;

Theorem rup_pass2_arr_spec:
  ∀ls lsv changes changesv assg.
  NUM max maxv ∧
  LIST_TYPE (PAIR_TYPE NUM (PAIR_TYPE INT NUM)) ls lsv ∧
  NUM l lv ∧
  LIST_TYPE NUM changes changesv ∧
  rup_pass2_list assg max ls l changes =
    (changes2,assg2,T) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rup_pass2_arr" (get_ml_prog_state()))
    [assgv; maxv; lsv; lv; changesv]
    (W8ARRAY assgv assg)
    (POSTv v.
      W8ARRAY assgv assg2 *
      &LIST_TYPE NUM changes2 v
    )
Proof
  Induct>>rw[]>>
  xcf"rup_pass2_arr"(get_ml_prog_state ())>>
  gvs[LIST_TYPE_def,rup_pass2_list_def]
  >- (
    xmatch>>
    xvar>>xsimpl)>>
  PairCases_on`h`>>
  gvs[PAIR_TYPE_def,rup_pass2_list_def]>>
  xmatch>>
  rpt xlet_autop>>
  reverse xif>>gvs[]
  >- (
    xapp>>gvs[]>>
    goal_assum drule>>
    gvs[])>>
  rpt(pairarg_tac>>gvs[])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  gvs[mk_flag_def]>>
  goal_assum drule>>
  simp[LIST_TYPE_def]
QED

Definition w8z_def:
  w8z = (0w: word8)
End

Definition w8o_def:
  w8o = (1w: word8)
End

val w8z_v_thm = translate w8z_def;
val w8o_v_thm = translate w8o_def;

val resize_to_fit = process_topdecs`
  fun resize_to_fit n assg =
    if n < Word8Array.length assg
      then assg
    else
     let val arr = Word8Array.array
      (3* Word8Array.length assg + n + 1) w8z
        val u = Word8Array.copy assg 0 (Word8Array.length assg) arr 0 in
        arr
      end` |> append_prog;

Theorem resize_to_fit_spec:
  NUM n nv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_to_fit" (get_ml_prog_state()))
    [nv; assgv]
    (W8ARRAY assgv assg)
    (POSTv v. SEP_EXISTS assg2.
      W8ARRAY v assg2 *
      &(
        resize_to_fit n assg = assg2
      )
    )
Proof
  rw[]>>
  xcf"resize_to_fit"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xif>>
  simp[resize_to_fit_def]
  >-
    (xvar>>xsimpl)>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop>>
  xvar>>xsimpl>>
  simp[w8z_def]
QED

val update_assg_arr = process_topdecs`
  fun update_assg_arr assg lsn =
  case lsn of (ls,n) =>
  case rup_pass1_arr assg ls 0 [] 0 of (max,ls1,m) =>
    let val assg1 = resize_to_fit m assg
        val changes2 = rup_pass2_arr assg1 max ls1 n [] in
        (changes2,assg1)
    end` |> append_prog;

Theorem update_assg_arr_spec:
  constraint_TYPE lsn lsnv ∧
  update_assg_list assg lsn = (new_changes,assg2,T) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "update_assg_arr" (get_ml_prog_state()))
    [assgv; lsnv]
    (W8ARRAY assgv assg)
    (POSTv v.
      SEP_EXISTS v1 v2.
      W8ARRAY v2 assg2 *
      &(
        v = Conv NONE [v1; v2] ∧
        LIST_TYPE NUM new_changes v1
      )
    )
Proof
  rw[]>>
  xcf"update_assg_arr"(get_ml_prog_state ())>>
  Cases_on`lsn`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[update_assg_list_def]>>
  rpt(pairarg_tac>>gvs[])>>
  xlet_auto
  >- (
    xsimpl>>
    simp[LIST_TYPE_def])>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  xlet_autop>>
  gvs[]>>
  xlet_auto
  >- (
    xsimpl>>
    EVAL_TAC)>>
  xcon>>xsimpl
QED

val get_rup_constraint_arr = process_topdecs`
  fun get_rup_constraint_arr lno b fml n nc =
  if n = 0 then nc
  else
    lookup_core_only_err_arr lno b fml n` |> append_prog;

Theorem get_rup_constraint_arr_spec:
  NUM lno lnov ∧
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  constraint_TYPE nc ncv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_rup_constraint_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; nv; ncv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case get_rup_constraint_list b fmlls n nc of
            NONE => F
          | SOME x => constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          get_rup_constraint_list b fmlls n nc = NONE)))
Proof
  rw[]>>
  xcf"get_rup_constraint_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    xvar>>rw[get_rup_constraint_list_def]>>
    xsimpl)>>
  xapp>>
  xsimpl>>
  goal_assum drule>>
  goal_assum drule>>
  goal_assum drule>>
  goal_assum drule>>
  rw[get_rup_constraint_list_def]
QED

(* no hints case *)
val check_rup_loop_arr = process_topdecs`
  fun check_rup_loop_arr lno b nc fml assg all_changes ls =
  case ls of
    [] =>
      raise Fail (format_failure lno ("invalid RUP step (missing hints)"))
  | (n::ns) =>
    let val c = get_rup_constraint_arr lno b fml n nc in
      if List.null ns then
        case rup_pass1_arr assg (fst c) 0 [] 0 of (max,ls1,m) =>
          if max < snd c then (assg,all_changes)
          else
            raise Fail (format_failure lno ("contradiction not derived at end of hints"))
      else
      case update_assg_arr assg c of (new_changes,assg) =>
      check_rup_loop_arr lno b nc fml assg (new_changes @ all_changes) ns
    end` |> append_prog;

Theorem check_rup_loop_arr_spec:
  ∀ns nsv ac acv assg assgv.
  NUM lno lnov ∧
  BOOL b bv ∧
  constraint_TYPE nc ncv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  LIST_TYPE NUM ac acv ∧
  LIST_TYPE NUM ns nsv ∧
  check_rup_loop_list b nc fmlls assg ac ns =
    (res,assg1,ac1,T) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_rup_loop_arr" (get_ml_prog_state()))
    [lnov; bv; ncv; fmlv; assgv; acv; nsv]
    (ARRAY fmlv fmllsv * W8ARRAY assgv assg)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
      SEP_EXISTS v1 v2.
      W8ARRAY v1 assg1 *
        &(
          v = Conv NONE [v1; v2] ∧
          res ∧
          LIST_TYPE NUM ac1 v2
        )
      )
      (λe.
        SEP_EXISTS v1.
        ARRAY fmlv fmllsv *
        W8ARRAY v1 assg1 *
        & (Fail_exn e ∧ ¬res)))
Proof
  Induct>>rw[]>>
  xcf"check_rup_loop_arr"(get_ml_prog_state ())>>
  gvs[LIST_TYPE_def,check_rup_loop_list_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    gvs[Fail_exn_def]>>
    metis_tac[W8ARRAY_refl])>>
  xlet_autop
  >- (
    xsimpl>>
    rw[]>>gvs[]>>
    metis_tac[W8ARRAY_refl])>>
  gvs[AllCaseEqs()]
  >- (
    (* NULL ns *)
    rpt(pairarg_tac>>gvs[])>>
    xlet_autop>>
    xif>>gvs[]>>
    first_x_assum (irule_at Any)>>
    simp[]>>
    rpt xlet_autop>>
    xlet_auto
    >-
      (xsimpl>> EVAL_TAC)>>
    xmatch>>
    rpt xlet_autop>>
    xif
    >-
      (xcon>>xsimpl)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[W8ARRAY_refl])>>
  (* ¬NULL ns *)
  rpt(pairarg_tac>>gvs[])>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[AllCaseEqs()])>>
  xif>>gvs[]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  xlet_autop>>
  xmatch>>
  xlet_autop>>
  xapp>>xsimpl>>
  goal_assum drule>>
  xsimpl
QED

val delete_each = process_topdecs`
  fun delete_each ns assg =
  case ns of [] => ()
  | (n::ns) =>
    (Unsafe.w8update assg n w8z;
    delete_each ns assg)` |> append_prog;

Theorem delete_each_spec:
  ∀ns nsv assg.
  LIST_TYPE NUM ns nsv ∧
  delete_each ns assg = (assg',T) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_each" (get_ml_prog_state()))
    [nsv; assgv]
    (W8ARRAY assgv assg)
    (POSTv v.
      W8ARRAY assgv assg' *
      &(UNIT_TYPE () v))
Proof
  Induct>>rw[]>>
  xcf"delete_each"(get_ml_prog_state ())>>
  gvs[delete_each_def,LIST_TYPE_def]>>
  xmatch>>xsimpl
  >-
    (xcon>>xsimpl)>>
  pairarg_tac>>gvs[]>>
  assume_tac w8z_v_thm>>
  xlet_autop>>
  xapp>>xsimpl>>
  simp[w8z_def]
QED

val check_rup_arr = process_topdecs`
  fun check_rup_arr lno b nc fml zeros ls =
    case check_rup_loop_arr lno b nc fml zeros [] ls of
     (assg1,all_changes1) =>
      (delete_each all_changes1 assg1; assg1)` |> append_prog;

Theorem check_rup_arr_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  constraint_TYPE nc ncv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  LIST_TYPE NUM ns nsv ∧
  check_rup_list b nc fmlls zeros ns = (res,zeros',T) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_rup_arr" (get_ml_prog_state()))
    [lnov; bv; ncv; fmlv; zerosv; nsv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        W8ARRAY v zeros' *
        &res)
      (λe.
        SEP_EXISTS v1 zeros'.
        ARRAY fmlv fmllsv *
        W8ARRAY v1 zeros' *
        & (Fail_exn e ∧ ¬res)))
Proof
  rw[]>>
  xcf"check_rup_arr"(get_ml_prog_state ())>>
  gvs[check_rup_list_def]>>
  rpt(pairarg_tac>>gvs[])>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    rw[]>- EVAL_TAC>>
    metis_tac[W8ARRAY_refl])
  >- (
    xsimpl>>
    rw[]>>
    metis_tac[W8ARRAY_refl])>>
  xmatch>>
  xlet_autop>>
  xvar>>xsimpl
QED

val res = translate npbc_checkTheory.map_app_list_def;
val res = translate npbc_checkTheory.mul_triv_def;
val res = translate SmartAppend_def;
val res = translate npbc_checkTheory.to_triv_def;

val check_lstep_arr = process_topdecs`
  fun check_lstep_arr lno step b fml mindel id zeros =
  case step of
    Check n c =>
      let val c' = lookup_core_only_err_arr lno b fml n in
        if c = c' then (fml, (None, (id, zeros)))
        else raise Fail (format_failure lno (err_check_string c c'))
      end
  | Noop => (fml, (None, (id, zeros)))
  | Delete ls =>
      if every_less mindel fml ls then
        (list_delete_arr ls fml; (fml, (None, (id, zeros))))
      else
        raise Fail (format_failure lno ("Deletion not permitted for core constraints and constraint index < " ^ Int.toString mindel))
  | Cutting constr =>
    let val c = check_cutting_arr lno b fml (to_triv constr) in
      (fml, (Some(c,b), (id, zeros)))
    end
  | Rup c ls =>
    (let val zeros = check_rup_arr lno b (not_1 c) fml zeros ls in
         (fml, (Some(c,b), (id, zeros)))
    end)
  | Con c pf n =>
    (case opt_update_arr fml (Some (not_1 c,b)) id of
      (fml_not_c,id') =>
      (case check_lsteps_arr lno pf b fml_not_c id id' zeros of
        (fml', (id', zeros)) =>
          if check_contradiction_fml_arr b fml' n then
            let val u = rollback_arr fml' id id' in
              (fml', (Some (c,b), (id',zeros)))
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n))))
  | _ => raise Fail (format_failure lno ("Proof step not supported"))
  and check_lsteps_arr lno steps b fml mindel id zeros =
  case steps of
    [] => (fml, (id, zeros))
  | s::ss =>
    (case check_lstep_arr lno s b fml mindel id zeros of
      (fml', (c , (id', zeros))) =>
        (case opt_update_arr fml' c id' of (fml'',id'') =>
        check_lsteps_arr lno ss b fml'' mindel id'' zeros))
` |> append_prog

val NPBC_CHECK_LSTEP_TYPE_def = fetch "-" "NPBC_CHECK_LSTEP_TYPE_def";

Theorem check_lstep_arr_spec_aux:
  (∀step b fmlls mindel id zeros stepv lno lnov idv fmlv fmllsv mindelv bv zerosv.
  NPBC_CHECK_LSTEP_TYPE step stepv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lstep_arr" (get_ml_prog_state()))
    [lnov; stepv; bv; fmlv; mindelv; idv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_lstep_list step b fmlls mindel id zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (OPTION_TYPE bconstraint_TYPE)
              (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv') )) res v ∧ EVERY (λw. w = 0w) zeros'
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
        check_lstep_list step b fmlls mindel id zeros = NONE)))) ∧
  (∀steps b fmlls mindel id zeros stepsv lno lnov idv fmlv fmllsv mindelv bv zerosv.
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE steps stepsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; bv; fmlv; mindelv; idv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_lsteps_list steps b fmlls mindel id zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv') ) res v ∧
            EVERY (λw. w = 0w) zeros'
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_lsteps_list steps b fmlls mindel id zeros = NONE))))
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]>>fs[]
  >- (
    xcfs ["check_lstep_arr","check_lsteps_arr"] (get_ml_prog_state ())>>
    simp[Once check_lstep_list_def]>>
    Cases_on`step`
    >- ( (* Delete *)
      fs[NPBC_CHECK_LSTEP_TYPE_def]>>
      xmatch>>
      xlet_autop>>
      reverse IF_CASES_TAC >>
      gs[]>>xif>>
      asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_lstep_list_def]>>
        xraise>>xsimpl>>
        simp[Fail_exn_def]>>
        metis_tac[ARRAY_W8ARRAY_refl])>>
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      simp[check_lstep_list_def])
    >- ((* Cutting *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_autop>>
      xlet_autop >- (
        xsimpl>>
        metis_tac[ARRAY_W8ARRAY_refl])>>
      rpt xlet_autop>>
      every_case_tac>>fs[]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- ((* Rup *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      pairarg_tac>>gvs[]>>
      imp_res_tac check_rup_list_pre>>gvs[]>>
      xlet_auto
      >- (
        xsimpl>>
        simp[LIST_TYPE_def]>>
        metis_tac[W8ARRAY_refl])
      >- (
        xsimpl>>rw[]>>
        metis_tac[ARRAY_W8ARRAY_refl])>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>simp[OPTION_TYPE_def,PAIR_TYPE_def]>>
      xsimpl)
    >- ( (* Con *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet`POSTv v. SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv zeros *
        &(
          PAIR_TYPE
            (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            NUM
            (opt_update fmlls (SOME (not p',b)) id) v)`
      >- (
        xapp>>xsimpl>>
        simp[OPTION_TYPE_def,PAIR_TYPE_def]>>
        rpt(first_x_assum (irule_at Any))>>
        qexists_tac`SOME (not p', b)`>>
        simp[OPTION_TYPE_def,PAIR_TYPE_def]>>rw[]>>
        xsimpl)>>
      fs[PAIR_TYPE_def]>>
      xmatch>>
      xlet_auto
      >- (
        xsimpl>>
        metis_tac[ARRAY_W8ARRAY_refl]
      )
      >- (
        xsimpl>>
        metis_tac[ARRAY_W8ARRAY_refl])>>
      pop_assum mp_tac>> TOP_CASE_TAC>>
      fs[]>>
      PairCases_on`x`>>fs[PAIR_TYPE_def]>>
      rw[]
      >- (
        (* successful contradiciton *)
        xmatch>>
        rpt xlet_autop>>
        xif>>asm_exists_tac>>xsimpl>>
        rpt xlet_autop>>
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        qmatch_goalsub_abbrev_tac`ARRAY _ ls`>>
        qexists_tac`ls`>>xsimpl>>
        simp[Abbr`ls`,OPTION_TYPE_def,PAIR_TYPE_def])>>
      xmatch>>
      rpt xlet_autop>>
      xif>>asm_exists_tac>>xsimpl>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])
    >- ( (* Check *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop
      >- (
        xsimpl>>
        rw[]>>
        gvs[lookup_core_only_list_def,AllCaseEqs()]>>
        metis_tac[ARRAY_W8ARRAY_refl])>>
      pop_assum mp_tac>>
      TOP_CASE_TAC>>strip_tac>>
      xlet_autop>>
      xif>>rpt xlet_autop
      >- (
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      xraise>>
      xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])
    >- ( (*No Op*)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
      asm_exists_tac>>xsimpl))
  >- (
    xcfs ["check_lstep_arr","check_lsteps_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    simp[Once check_lstep_list_def]>>
    xcon>>xsimpl
    >- (
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl)>>
    simp[Once check_lstep_list_def])
  >- (
    xcfs ["check_lstep_arr","check_lsteps_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xlet_auto
    >- (
      xsimpl>>rw[]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      rw[]>>simp[Once check_lstep_list_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
    PairCases_on`x`>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_auto
    >- (
      gvs[]>>
      rename1`W8ARRAY zzzv zzz`>>
      qexists_tac`W8ARRAY zzzv zzz`>>
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    Cases_on`opt_update x0 x1 x2`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    xsimpl>>
    rw[]>>simp[Once check_lstep_list_def]
    >- (
      every_case_tac>>fs[]>>asm_exists_tac>>
      xsimpl)>>
    metis_tac[ARRAY_W8ARRAY_refl])
QED

Theorem check_lstep_arr_spec = CONJUNCT1 check_lstep_arr_spec_aux
Theorem check_lsteps_arr_spec = CONJUNCT2 check_lstep_arr_spec_aux

val reindex_aux_arr = process_topdecs `
  fun reindex_aux_arr fml ls iacc =
  case ls of
    [] => (List.rev iacc)
  | (i::is) =>
  case Array.lookup fml None i of
    None => reindex_aux_arr fml is iacc
  | Some vb =>
      reindex_aux_arr fml is (i::iacc)` |> append_prog;

val reindex_arr = process_topdecs `
  fun reindex_arr fml is =
    reindex_aux_arr fml is []`
  |> append_prog;

Theorem reindex_aux_arr_spec:
  ∀inds indsv fmlls fmlv iacc iaccv.
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) iacc iaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_aux_arr" (get_ml_prog_state()))
    [fmlv; indsv; iaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE NUM
        (reindex_aux fmlls inds iacc) v))
Proof
  Induct>>
  rw[]>>
  xcf"reindex_aux_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [alpha |-> ``:num``])>>
    xsimpl>>
    simp[reindex_aux_def,LIST_TYPE_def,PAIR_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE
    (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[reindex_aux_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  xmatch>>
  xlet_autop>>
  xapp>>
  fs[LIST_TYPE_def]
QED

Theorem reindex_arr_spec:
  ∀inds indsv fmlls fmlv.
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_arr" (get_ml_prog_state()))
    [fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE NUM
        (reindex fmlls inds) v))
Proof
  rw[]>>
  xcf"reindex_arr"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[reindex_def]>>
  metis_tac[LIST_TYPE_def]
QED

Definition mk_vacc_def:
  mk_vacc b b' v vacc =
    if b ⇒ b' then v::vacc else vacc
End

val r = translate mk_vacc_def;

val revalue_aux_arr = process_topdecs `
  fun revalue_aux_arr b fml ls vacc =
  case ls of
    [] => vacc
  | (i::is) =>
  case Array.lookup fml None i of
    None => revalue_aux_arr b fml is vacc
  | Some (v,b') =>
      revalue_aux_arr b fml is
        (mk_vacc b b' v vacc)` |> append_prog;

val revalue_arr = process_topdecs `
  fun revalue_arr b fml is =
    revalue_aux_arr b fml is []`
  |> append_prog;

Theorem revalue_aux_arr_spec:
  ∀inds indsv fmlls fmlv vacc vaccv.
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE constraint_TYPE) vacc vaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "revalue_aux_arr" (get_ml_prog_state()))
    [bv; fmlv; indsv; vaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE constraint_TYPE
        (revalue_aux b fmlls inds vacc) v))
Proof
  Induct>>
  rw[]>>
  xcf"revalue_aux_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xvar>>xsimpl>>
    simp[revalue_aux_def,LIST_TYPE_def,PAIR_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE
    (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[revalue_aux_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xapp>>
  fs[LIST_TYPE_def,mk_vacc_def]
QED

Theorem revalue_arr_spec:
  ∀inds indsv fmlls fmlv.
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "revalue_arr" (get_ml_prog_state()))
    [bv; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE constraint_TYPE
        (revalue b fmlls inds) v))
Proof
  rw[]>>
  xcf"revalue_arr"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[revalue_def]>>
  metis_tac[LIST_TYPE_def]
QED

(*
val reindex_partial_aux_arr = process_topdecs `
  fun reindex_partial_aux_arr b fml mini ls iacc vacc =
  case ls of
    [] => (List.rev iacc, (vacc, []))
  | (i::is) =>
  if i < mini then (List.rev iacc, (vacc, ls))
  else
  case Array.lookup fml None i of
    None => reindex_partial_aux_arr b fml mini is iacc vacc
  | Some (v,b') =>
      reindex_partial_aux_arr b fml mini is (i::iacc)
        (mk_vacc b b' v vacc)` |> append_prog;

val reindex_partial_arr = process_topdecs `
  fun reindex_partial_arr b fml mini is =
  case mini of None => ([], ([], is))
  | Some mini =>
    reindex_partial_aux_arr b fml mini is [] []`
  |> append_prog;

Theorem reindex_partial_aux_arr_spec:
  ∀inds indsv b bv fmlls fmlv iacc iaccv vacc vaccv.
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  NUM mini miniv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) iacc iaccv ∧
  (LIST_TYPE constraint_TYPE) vacc vaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_partial_aux_arr" (get_ml_prog_state()))
    [bv; fmlv; miniv; indsv; iaccv; vaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (LIST_TYPE constraint_TYPE)
          (LIST_TYPE NUM))
        (reindex_partial_aux b fmlls mini inds iacc vacc) v))
Proof
  Induct>>
  xcf"reindex_partial_aux_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[reindex_partial_aux_def,LIST_TYPE_def,PAIR_TYPE_def])>>
  xmatch>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>
    simp[reindex_partial_aux_def,PAIR_TYPE_def,LIST_TYPE_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE
    (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[reindex_partial_aux_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xapp>>
  fs[LIST_TYPE_def,mk_vacc_def]
QED

Theorem reindex_partial_arr_spec:
  ∀inds indsv fmlls fmlv.
  BOOL b bv ∧
  OPTION_TYPE NUM mini miniv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_partial_arr" (get_ml_prog_state()))
    [bv; fmlv; miniv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (LIST_TYPE constraint_TYPE) (LIST_TYPE NUM))
        (reindex_partial b fmlls mini inds) v))
Proof
  xcf"reindex_partial_arr"(get_ml_prog_state ())>>
  Cases_on`mini`>>
  gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[reindex_partial_def,PAIR_TYPE_def,LIST_TYPE_def])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[reindex_partial_def]>>
  metis_tac[LIST_TYPE_def]
QED
*)

val res = translate is_Pos_def;
val res = translate subst_aux_def;
val res = translate partition_def;
val res = translate clean_up_def;
val res = translate subst_lhs_def;
val res = translate (subst_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

val res = translate (obj_constraint_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

Theorem subst_fun_alt:
  subst_fun (s:subst) =
  case s of
    INL (m,v) => \n. if n = m then SOME v else NONE
  | INR s =>
    \n. if n < length s then sub s n else NONE
Proof
  rw[FUN_EQ_THM]>>
  every_case_tac>>
  EVAL_TAC>>
  rw[]
QED

val res = translate subst_fun_alt;
val res = translate subst_subst_fun_def;

val extract_clauses_arr = process_topdecs`
  fun extract_clauses_arr lno s b fml rsubs pfs acc =
  case pfs of [] => List.rev acc
  | cpf::pfs =>
    case cpf of
      (None,pf) =>
        extract_clauses_arr lno s b fml rsubs pfs ((None,pf)::acc)
    | (Some (Inl n,i),pf) =>
      let val c = lookup_core_only_err_arr lno b fml n in
        extract_clauses_arr lno s b fml rsubs pfs ((Some ([not_1(subst_subst_fun s c)],i),pf)::acc)
      end
    | (Some (Inr u,i),pf) =>
      if u < List.length rsubs then
        extract_clauses_arr lno s b fml rsubs pfs ((Some (List.nth rsubs u,i),pf)::acc)
      else raise Fail (format_failure lno ("invalid #proofgoal id: " ^ Int.toString u))
` |> append_prog;

Overload "subst_TYPE" = ``SUM_TYPE (PAIR_TYPE NUM (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))) (VECTOR_TYPE (OPTION_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))))``

Overload "pfs_TYPE" = ``LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE))``
Overload "scpfs_TYPE" = ``LIST_TYPE (PAIR_TYPE (OPTION_TYPE NUM) pfs_TYPE)``

Overload "check_subproof_TYPE" = ``
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE))``

Overload "check_scope_TYPE" = ``
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (LIST_TYPE constraint_TYPE)) check_subproof_TYPE)``

Theorem extract_clauses_arr_spec:
  ∀pfs pfsv s sv b bv fmlls fmlv fmllsv
    rsubs rsubsv acc accv lno lnov.
  NUM lno lnov ∧
  subst_TYPE s sv ∧
  BOOL b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  pfs_TYPE pfs pfsv ∧
  check_subproof_TYPE acc accv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extract_clauses_arr" (get_ml_prog_state()))
    [lnov; sv; bv; fmlv; rsubsv; pfsv; accv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        &(case extract_clauses_list s b fmlls rsubs pfs acc of
            NONE => F
          | SOME res =>
            check_subproof_TYPE res v))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          extract_clauses_list s b fmlls rsubs pfs acc = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf"extract_clauses_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [alpha |-> ``:((npbc list # num) option # lstep list) ``])>>
    xsimpl>>
    asm_exists_tac>>rw[]>>
    simp[extract_clauses_list_def])>>
  xmatch>>
  simp[Once extract_clauses_list_def]>>
  Cases_on`h`>>fs[]>>
  Cases_on`q`>>fs[PAIR_TYPE_def,OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    rpt(asm_exists_tac>>xsimpl)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`(NONE,r)::acc`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def])>>
  Cases_on`x`>> Cases_on`q`>>
  fs[PAIR_TYPE_def,SUM_TYPE_def]>>xmatch
  >- (
    (* INL *)
    xlet_autop
    >- (
      xsimpl>>
      simp[extract_clauses_list_def])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>
    gvs[]>> strip_tac>>
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    qmatch_goalsub_abbrev_tac`extract_clauses_list _ _ _ _ _ acc'`>>
    qexists_tac`acc'`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,Abbr`acc'`])>>
  (* INR *)
  rpt xlet_autop>>
  xif>>simp[]
  >- (
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    qmatch_goalsub_abbrev_tac`extract_clauses_list _ _ _ _ _ acc'`>>
    qexists_tac`acc'`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,Abbr`acc'`]>>
    fs[mllistTheory.nth_def])>>
  rpt xlet_autop>>
  xraise>>
  xsimpl>>
  simp[extract_clauses_list_def,Fail_exn_def]>>
  metis_tac[]
QED

val res = translate EL;
val res = translate npbc_checkTheory.mk_scope_def;

Triviality el_side:
  ∀xs n.
  n < LENGTH xs ⇒
  el_side n xs
Proof
  Induct>>
  rw[Once (fetch "-" "el_side_def")]
QED

val _ = el_side |> update_precondition;

Triviality mk_scope_side:
  mk_scope_side x y
Proof
  EVAL_TAC>>rw[]>>
  metis_tac[el_side]
QED
val _ = mk_scope_side |> update_precondition;

val extract_scopes_arr = process_topdecs`
  fun extract_scopes_arr lno scopes s b fml rsubs pfs =
  case pfs of [] => []
  | (sc,pfs)::rest =>
    case mk_scope scopes sc of
      None =>
        raise Fail (format_failure lno ("invalid scope id"))
    | Some scs =>
    let
    val cpfs = extract_clauses_arr lno s b fml rsubs pfs [] in
      (scs,cpfs)::extract_scopes_arr lno scopes s b fml rsubs rest
    end` |> append_prog;

Theorem extract_scopes_arr_spec:
  ∀pfs pfsv s sv b bv fmlls fmlv fmllsv
    rsubs rsubsv lno lnov.
  NUM lno lnov ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) scopes scopesv ∧
  subst_TYPE s sv ∧
  BOOL b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  scpfs_TYPE pfs pfsv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extract_scopes_arr" (get_ml_prog_state()))
    [lnov; scopesv; sv; bv; fmlv; rsubsv; pfsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        &(case extract_scopes_list scopes s b fmlls rsubs pfs of
            NONE => F
          | SOME res =>
            check_scope_TYPE res v))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          extract_scopes_list scopes s b fmlls rsubs pfs = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf"extract_scopes_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    simp[extract_scopes_list_def,LIST_TYPE_def])>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  simp[extract_scopes_list_def]>>
  Cases_on`mk_scope scopes q`>>
  fs[PAIR_TYPE_def,OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  xmatch>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &check_subproof_TYPE [] v`
  >- (xcon>>xsimpl>>simp[LIST_TYPE_def])>>
  xlet_autop
  >- xsimpl>>
  gvs[AllCasePreds()]>>
  xlet` (POSTve
    (λv.
         ARRAY fmlv fmllsv *
         & ∃res.
           extract_scopes_list scopes s b fmlls rsubs pfs =
           SOME res ∧ check_scope_TYPE res v)
    (λe.
         ARRAY fmlv fmllsv *
         &(Fail_exn e ∧
          extract_scopes_list scopes s b fmlls rsubs pfs = NONE)))`
  >- (xapp>>xsimpl>>metis_tac[])
  >- xsimpl>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  simp[LIST_TYPE_def,PAIR_TYPE_def]
QED

val res = translate subst_opt_aux_acc_def;
val res = translate imp_def;
val res = translate (subst_opt_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])
val res = translate subst_opt_subst_fun_def;

val subst_indexes_arr = process_topdecs`
  fun subst_indexes_arr s b fml is =
  case is of [] => []
  | (i::is) =>
    case lookup_core_only_arr b fml i of
      None => subst_indexes_arr s b fml is
    | Some res =>
      (case subst_opt_subst_fun s res of
        None => subst_indexes_arr s b fml is
      | Some c => (i,c)::subst_indexes_arr s b fml is)`
    |> append_prog;

Theorem subst_indexes_arr_spec:
  ∀is isv s sv b bv fmlls fmllsv fmlv.
  subst_TYPE s sv ∧
  BOOL b bv ∧
  LIST_TYPE NUM is isv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "subst_indexes_arr" (get_ml_prog_state()))
    [sv; bv; fmlv; isv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) (subst_indexes s b fmlls is) v))
Proof
  Induct>>
  rw[]>>
  xcf"subst_indexes_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    simp[subst_indexes_def,LIST_TYPE_def])>>
  xmatch>>
  xlet_autop>>
  simp[subst_indexes_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xapp>>
    metis_tac[])>>
  xlet_autop>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>xapp>>
    metis_tac[])>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[LIST_TYPE_def,PAIR_TYPE_def]
QED

val list_insert_fml_arr = process_topdecs`
  fun list_insert_fml_arr ls b id fml =
    case ls of
      [] => (id,fml)
    | (c::cs) =>
      list_insert_fml_arr cs b
      (id+1)
      (Array.updateResize fml None id (Some (c,b)))` |> append_prog

Theorem list_insert_fml_arr_spec:
  ∀ls lsv b bv fmlv fmlls fmllsv id idv.
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  BOOL b bv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_insert_fml_arr" (get_ml_prog_state()))
    [lsv; bv; idv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      SEP_EXISTS fmlv' fmllsv'.
      ARRAY fmlv' fmllsv' *
      &(PAIR_TYPE NUM
          (λl v.
          LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
          v = fmlv')
          (list_insert_fml_list ls b id fmlls) resv))
Proof
  Induct>>
  rw[]>>simp[list_insert_fml_list_def]>>
  xcf "list_insert_fml_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  rpt xlet_autop>>
  xapp>>simp[]>>
  match_mp_tac LIST_REL_update_resize>>
  simp[OPTION_TYPE_def,PAIR_TYPE_def]
QED

val check_subproofs_arr = process_topdecs`
  fun check_subproofs_arr lno pfs b fml mindel id zeros =
  case pfs of
    [] => (fml,(id,zeros))
  | (cnopt,pf)::pfs =>
    (case cnopt of
      None =>
      (case check_lsteps_arr lno pf b fml mindel id zeros of
        (fml', (id', zeros')) =>
        check_subproofs_arr lno pfs b fml' mindel id' zeros')
    | Some (cs,n) =>
      case list_insert_fml_arr cs b id fml of
        (cid, cfml) =>
        (case check_lsteps_arr lno pf b cfml id cid zeros of
          (fml', (id', zeros')) =>
          if check_contradiction_fml_arr b fml' n then
          let val u = rollback_arr fml' id id' in
            check_subproofs_arr lno pfs b fml' mindel id' zeros'
          end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n))))` |> append_prog

Theorem check_subproofs_arr_spec:
  ∀pfs fmlls mindel id pfsv zeros lno lnov idv fmlv fmllsv mindelv b bv zerosv.
  check_subproof_TYPE pfs pfsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_subproofs_arr" (get_ml_prog_state()))
    [lnov; pfsv; bv; fmlv; mindelv; idv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
        case check_subproofs_list pfs b fmlls mindel id zeros of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v.
            LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
            v = fmlv')
            (PAIR_TYPE NUM
            (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros') )
            res v
        ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_subproofs_list pfs b fmlls mindel id zeros = NONE)))
Proof
  Induct>>
  rw[]>>simp[check_subproofs_list_def]>>
  xcf "check_subproofs_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>
    xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  simp[check_subproofs_list_def]>>
  Cases_on`q`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_auto
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x`>>simp[PAIR_TYPE_def]>>
  strip_tac>>xmatch>>
  xlet_autop>>
  reverse xif>> xsimpl
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

val check_scopes_arr = process_topdecs`
  fun check_scopes_arr lno pfs b fml mindel id zeros =
  case pfs of
    [] => (fml,(id,zeros))
  | (scopt,pf)::pfs =>
    (case scopt of
      None =>
      (case check_subproofs_arr lno pf b fml mindel id zeros of
        (fml', (id', zeros')) =>
        check_scopes_arr lno pfs b fml' mindel id' zeros')
    | Some sc =>
      case list_insert_fml_arr sc b id fml of
        (cid, cfml) =>
        (case check_subproofs_arr lno pf b cfml id cid zeros of
          (fml', (id', zeros')) =>
          let val u = rollback_arr fml' id id' in
            check_scopes_arr lno pfs b fml' mindel id' zeros'
          end))` |> append_prog

Theorem check_scopes_arr_spec:
  ∀pfs fmlls mindel id pfsv zeros lno lnov idv fmlv fmllsv mindelv b bv zerosv.
  check_scope_TYPE pfs pfsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_scopes_arr" (get_ml_prog_state()))
    [lnov; pfsv; bv; fmlv; mindelv; idv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
        case check_scopes_list pfs b fmlls mindel id zeros of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v.
            LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
            v = fmlv')
            (PAIR_TYPE NUM
            (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros') )
            res v
        ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_scopes_list pfs b fmlls mindel id zeros = NONE)))
Proof
  Induct>>
  rw[]>>simp[check_scopes_list_def]>>
  xcf "check_scopes_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>
    xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  simp[check_scopes_list_def]>>
  Cases_on`q`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_auto
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  rename1`_ = SOME yy`>>
  PairCases_on`yy`>>simp[PAIR_TYPE_def]>>
  strip_tac>>xmatch>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

val res = translate npbc_checkTheory.extract_pids_def;

Definition do_rso_def:
  do_rso ord s c obj vomap =
  fast_red_subgoals ord s c obj vomap
End

val res = translate npbc_checkTheory.list_list_insert_def;
val res = translate npbcTheory.mk_lit_def;
val res = translate npbcTheory.mk_bit_lit_def;
val res = translate npbc_checkTheory.dom_subst_def;

val res = translate obj_single_aux_def;
val res = translate obj_single_def;
val res = translate full_obj_single_def;

val res = translate fast_obj_constraint_def;
val res = translate fast_red_subgoals_def;
val res = translate do_rso_def;

val res = translate npbc_checkTheory.list_pair_eq_def;
val res = translate npbc_checkTheory.equal_constraint_def;
val res = translate npbc_checkTheory.mem_constraint_def;

val hash_simps = [h_base_def, h_base_sq_def, h_mod_def, splim_def];

val res = translate (hash_pair_def |> REWRITE_RULE hash_simps);

Triviality hash_pair_side:
  hash_pair_side n
Proof
  rw[Once (fetch "-" "hash_pair_side_def")]>>
  intLib.ARITH_TAC
QED
val _ = hash_pair_side |> update_precondition

val res = translate (hash_list_def |> REWRITE_RULE hash_simps);
val res = translate (hash_constraint_def |> REWRITE_RULE hash_simps);

val mk_hashset_arr = process_topdecs`
  fun mk_hashset_arr ps acc =
  case ps of [] => ()
  | p::ps =>
  let val h = hash_constraint p in
    Unsafe.update acc h (p::(Array.sub acc h));
    mk_hashset_arr ps acc
  end` |> append_prog;

Theorem hash_constraint_splim:
  hash_constraint h < splim
Proof
  Cases_on`h`>>fs[hash_constraint_def]>>
  match_mp_tac MOD_LESS>>
  EVAL_TAC
QED

Theorem mk_hashset_arr_spec:
  ∀ls lsv hs hsv.
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  LENGTH hsv = splim ∧
  LIST_REL (LIST_TYPE constraint_TYPE) hs hsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "mk_hashset_arr" (get_ml_prog_state()))
    [lsv; hspv]
    (ARRAY hspv hsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS hsv'.
      ARRAY hspv hsv' *
      &(LIST_REL (LIST_TYPE constraint_TYPE) (mk_hashset ls hs) hsv') )
Proof
  Induct>>
  rw[]>>simp[mk_hashset_def]>>
  xcf "mk_hashset_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl) >>
  xmatch>>
  fs[]>>
  rpt xlet_autop>>
  xlet_auto>- (
    xsimpl>>
    simp[hash_constraint_splim])>>
  rpt xlet_autop>>
  xlet_auto>- (
    xsimpl>>
    simp[hash_constraint_splim])>>
  xapp>>simp[]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[LIST_TYPE_def]>>
  fs[LIST_REL_EL_EQN]>>
  first_x_assum match_mp_tac>>
  gs[hash_constraint_splim]
QED

(* val u = print (Int.toString (List.length r) ^ " " ^ Int.toString h ^ "\n") in *)

val in_hashset_arr = process_topdecs`
  fun in_hashset_arr p hs =
  let val h = hash_constraint p
    val r = Unsafe.sub hs h in
    mem_constraint p r
  end` |> append_prog;

Theorem in_hashset_arr_spec:
  constraint_TYPE c cv ∧
  LENGTH hsv = splim ∧
  LIST_REL (LIST_TYPE constraint_TYPE) hs hsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "in_hashset_arr" (get_ml_prog_state()))
    [cv; hspv]
    (ARRAY hspv hsv)
    (POSTv resv.
      ARRAY hspv hsv *
      &BOOL (in_hashset c hs) resv)
Proof
  rw[]>>simp[in_hashset_def]>>
  xcf "in_hashset_arr" (get_ml_prog_state ())>>
  fs[]>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[hash_constraint_splim])>>
  xapp>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  qexists_tac`EL (hash_constraint c) hs`>>simp[]>>
  fs[LIST_REL_EL_EQN]>>
  first_x_assum match_mp_tac>>
  gs[hash_constraint_splim]
QED

val r = translate splim_def;

val every_hs = process_topdecs`
  fun every_hs hs ls =
  case ls of [] => None
  | l::ls =>
    if in_hashset_arr l hs then
      every_hs hs ls
    else Some (npbc_string l)` |> append_prog

Theorem every_hs_spec:
  ∀ls lsv.
  LIST_TYPE constraint_TYPE ls lsv ∧
  LENGTH hsv = splim ∧
  LIST_REL (LIST_TYPE constraint_TYPE) hs hsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_hs" (get_ml_prog_state()))
    [hspv; lsv]
    (ARRAY hspv hsv)
    (POSTv resv.
      ARRAY hspv hsv *
      & ∃err.
        OPTION_TYPE STRING_TYPE
          (if EVERY (λc. in_hashset c hs) ls
          then NONE else SOME err) resv)
Proof
  Induct>>rw[]>>
  fs[LIST_TYPE_def]>>
  xcf "every_hs" (get_ml_prog_state ())>>
  xmatch
  >- (xcon>>xsimpl>>EVAL_TAC)>>
  xlet_auto>>
  xif
  >-
    (xapp>>xsimpl)>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def]>>
  metis_tac[]
QED

val hash_check = process_topdecs`
  fun hash_check fmlls proved lf =
  let
    val hs = Array.array splim []
    val u = mk_hashset_arr proved hs
    val u = mk_hashset_arr fmlls hs
  in
    every_hs hs lf
  end` |> append_prog

Theorem LENGTH_mk_hashset[simp]:
  ∀x ls.
  LENGTH (mk_hashset x ls) = LENGTH ls
Proof
  Induct>>rw[mk_hashset_def]
QED

Theorem hash_check_spec:
  LIST_TYPE constraint_TYPE ls lsv ∧
  LIST_TYPE constraint_TYPE x xv ∧
  LIST_TYPE constraint_TYPE y yv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "hash_check" (get_ml_prog_state()))
    [xv; yv; lsv]
    emp
    (POSTv resv.
      & ∃err.
        OPTION_TYPE STRING_TYPE
        (let hs = mk_hashset x
          (mk_hashset y (REPLICATE splim [])) in
          if EVERY (λc. in_hashset c hs) ls
          then NONE else SOME err) resv)
Proof
  rw[]>>
  xcf "hash_check" (get_ml_prog_state ())>>
  xlet_autop>>
  assume_tac (fetch "-" "splim_v_thm")>>
  xlet_auto>>
  qmatch_goalsub_abbrev_tac`ARRAY av hsv`>>
  `LIST_REL (LIST_TYPE constraint_TYPE) (REPLICATE splim []) hsv` by
    simp[Abbr`hsv`,LIST_REL_REPLICATE_same,LIST_TYPE_def]>>
  qmatch_asmsub_abbrev_tac`LIST_REL _ hs _`>>
  xlet`POSTv resv.
    &UNIT_TYPE () resv *
    SEP_EXISTS hsv'.
    ARRAY av hsv' *
    &LIST_REL (LIST_TYPE constraint_TYPE) (mk_hashset y hs) hsv'`
  >-
    (xapp>>unabbrev_all_tac>>fs[])>>
  xlet_auto
  >- (
    xsimpl>>
    fs[LIST_REL_EL_EQN,Abbr`hs`])>>
  xapp>>xsimpl>>
  first_assum (irule_at Any)>>
  qexists_tac`ls`>>simp[LIST_TYPE_def]>>
  unabbrev_all_tac>>fs[LIST_REL_EL_EQN]
QED

Definition red_cond_check_def:
  red_cond_check bortcb fml inds extra
    pfs (rsubs:((int # num) list # num) list list) goals skipped =
  let (l,r) = extract_scoped_pids pfs LN LN in
  let fmlls = revalue bortcb fml inds in
  split_goals_hash fmlls extra l goals ∧
  EVERY (λ(id,cs).
    lookup id r ≠ NONE ∨
    check_hash_triv extra cs ∨
    MEM id skipped
    )
  (enumerate 0 rsubs)
End

Definition lookup_hash_triv_def:
  lookup_hash_triv r extra skipped (id,cs) =
  case sptree$lookup id r of
    NONE => check_hash_triv extra cs ∨ MEM id skipped
  | SOME _ => T
End

Definition every_check_hash_triv_def:
  every_check_hash_triv r extra skipped rsubs =
  EVERY (lookup_hash_triv r extra skipped)
    (enumerate 0 rsubs)
End

Definition red_cond_check_pure_def:
  red_cond_check_pure extra
  pfs
  (rsubs:((int # num) list # num) list list)
  (goals:(num # (int # num) list # num) list)
  skipped =
  let (l,r) = extract_scoped_pids pfs LN LN in
  if
     every_check_hash_triv r extra skipped rsubs
  then
    let (lp,lf) =
      PARTITION (λ(i,c). lookup i l ≠ NONE) goals in
    let lf = FILTER (λc. ¬check_triv extra (not c)) (MAP SND lf) in
    let proved = MAP SND lp in
    SOME (proved,lf)
  else NONE
End

Theorem lookup_hash_triv_fun_eq:
  lookup_hash_triv r extra skipped =
  (λ(id,cs). lookup id r = NONE ⇒ check_hash_triv extra cs ∨ MEM id skipped)
Proof
  rw[FUN_EQ_THM]>>
  pairarg_tac>>fs[lookup_hash_triv_def]>>
  every_case_tac>>gvs[]
QED

Theorem red_cond_check_eq:
  red_cond_check bortcb fml inds extra pfs rsubs goals skipped =
  case red_cond_check_pure extra pfs rsubs goals skipped of
    NONE => F
  | SOME (x,ls) =>
    let fmlls = revalue bortcb fml inds in
    let hs = mk_hashset fmlls (mk_hashset x (REPLICATE splim [])) in
    EVERY (λc. in_hashset c hs) ls
Proof
  rw[red_cond_check_def,red_cond_check_pure_def,every_check_hash_triv_def]>>
  pairarg_tac>>fs[split_goals_hash_def]>>
  rpt (pairarg_tac>>fs[])>>
  rw[lookup_hash_triv_fun_eq]
QED

val res = translate npbc_checkTheory.check_triv_def;
val res = translate npbc_checkTheory.check_hash_triv_def;
val res = translate miscTheory.enumerate_def;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate (lookup_hash_triv_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate every_check_hash_triv_def;
val res = translate npbc_checkTheory.extract_scope_val_def;
val res = translate npbc_checkTheory.extract_scoped_pids_def;
val res = translate red_cond_check_pure_def;

val red_cond_check = process_topdecs`
  fun red_cond_check bortcb fml inds extra pfs rsubs goals skipped =
  case red_cond_check_pure extra pfs rsubs goals skipped of
    None => Some "not all # subgoals present"
  | Some (x,ls) =>
    case ls of [] => None
    | _ =>
    let val fmlls = revalue_arr bortcb fml inds in
      hash_check fmlls x ls
    end` |> append_prog

Theorem red_cond_check_spec:
  BOOL bt btv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv ∧
  constraint_TYPE aa aav ∧
  scpfs_TYPE b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) d dv ∧
  LIST_TYPE NUM e ev
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "red_cond_check" (get_ml_prog_state()))
    [btv; fmlv; indsv; aav; bv; cv; dv; ev]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      ARRAY fmlv fmllsv *
      & ∃err.
      OPTION_TYPE STRING_TYPE
        (if red_cond_check bt fmlls inds aa b c d e then NONE
        else SOME err) resv)
Proof
  rw[]>>
  xcf "red_cond_check" (get_ml_prog_state ())>>
  fs[]>>
  xlet_autop>>
  simp[red_cond_check_eq]>>
  Cases_on`red_cond_check_pure aa b c d e`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rename1` _ = SOME (proved,lf)`>>
  Cases_on`lf`>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  fs[]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  qexists_tac`h::t`>>
  simp[LIST_TYPE_def]
QED

(* Definition print_subgoal_def:
  (print_subgoal (INL n) = (toString (n:num))) ∧
  (print_subgoal (INR n) = (strlit"#" ^ toString (n:num)))
End

Definition print_subproofs_def:
  (print_subproofs ls =
    concatWith (strlit " ") (MAP print_subgoal ls))
End *)

Definition print_expected_subproofs_def:
  (print_expected_subproofs rsubs (si: (num # 'a) list) =
    strlit ("#[1-") ^
    toString (LENGTH rsubs) ^ strlit "] and " ^
    concatWith (strlit" ") (MAP (toString o FST) si))
End

Definition print_subproofs_err_def:
  print_subproofs_err rsubs si =
  strlit"Expected (including autoproved): " ^
  print_expected_subproofs rsubs si
  (* ^
  strlit " Got: " ^
  print_subproofs pfs *)
End

(* val res = translate print_subgoal_def;
val res = translate print_subproofs_def; *)
val res = translate print_expected_subproofs_def;
val res = translate print_subproofs_err_def;

Definition format_failure_2_def:
  format_failure_2 (lno:num) s s2 =
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit " Reason: " ^ s
  ^ strlit " Info: " ^ s2 ^ strlit"\n"
End

val r = translate format_failure_2_def;

Theorem vec_eq_nil_thm:
  v = INR (Vector []) ⇔
  case v of INL _ => F
  | INR v => length v = 0
Proof
  Cases_on`v`>>EVAL_TAC>>
  Cases_on`y`>>fs[mlvectorTheory.length_def]
QED

val r = translate (red_fast_def |> SIMP_RULE std_ss [vec_eq_nil_thm]);

val check_red_arr_fast = process_topdecs`
  fun check_red_arr_fast lno b fml inds id c pf cid vimap zeros =
  let
    val nc = not_1 c
    val fml_not_c = Array.updateResize fml None id (Some (nc,b)) in
     case check_lsteps_arr lno pf b fml_not_c id (id+1) zeros of
       (fml', (id', zeros')) =>
      if check_contradiction_fml_arr b fml' cid then
        let val u = rollback_arr fml' id id' in
          (fml', (inds, (vimap, (id',zeros'))))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid))
    end` |> append_prog;

Overload "vimapn_TYPE" = ``
  SUM_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) NUM``

Theorem check_red_arr_fast_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE pfs pfsv ∧
  NUM cid cidv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr_fast" (get_ml_prog_state()))
    [lnov; bv; fmlv; indsv; idv;
      cv; pfsv; cidv; vimapv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_red_list_fast b fmlls inds id
              c pfs cid vimap zeros of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v.
                    LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                    v = vimapv')
                (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros') ))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_red_list_fast b fmlls inds id
              c pfs cid vimap zeros = NONE)))
Proof
  rw[]>>
  xcf "check_red_arr_fast" (get_ml_prog_state ())>>
  rw[check_red_list_fast_def]>>
  rpt xlet_autop>>
  `LIST_REL (OPTION_TYPE bconstraint_TYPE)
   (update_resize fmlls NONE (SOME (not c,b)) id)
   (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
           (Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [v; bv]]) id)` by (
    match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def,PAIR_TYPE_def])>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>
  PairCases_on`x`>>simp[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def]
QED

val get_indices_arr = process_topdecs`
  fun get_indices_arr fml inds s vimap =
  case s of
    Inr v =>
    if Vector.length v = 0 then []
    else reindex_arr fml inds
  | Inl (n,ls) =>
    case Array.lookup vimap None n of
      None => []
    | Some (Inl (nn,inds)) => reindex_arr fml inds
    | Some (Inr (earliest)) => reindex_arr fml inds` |> append_prog;

Theorem get_indices_arr_spec:
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  subst_TYPE s sv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_indices_arr" (get_ml_prog_state()))
    [fmlv; indsv; sv; vimapv]
    (ARRAY fmlv fmllsv * ARRAY vimapv vimaplsv)
    (POSTv v.
        ARRAY fmlv fmllsv * ARRAY vimapv vimaplsv *
        &(
          LIST_TYPE NUM
            (get_indices fmlls inds s vimap) v))
Proof
  rw[]>>
  xcf "get_indices_arr" (get_ml_prog_state ())>>
  reverse (Cases_on`s`)>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    simp[get_indices_def]>>
    rpt xlet_autop>>
    xif
    >-  (xcon>>xsimpl>> simp[LIST_TYPE_def])>>
    xapp>>xsimpl>>
    metis_tac[])>>
  Cases_on`x`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  simp[get_indices_def]>>
  `OPTION_TYPE vimapn_TYPE (any_el q vimap NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  every_case_tac>>
  gvs[OPTION_TYPE_def,SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch
  >-  (xcon>>xsimpl>>EVAL_TAC)>>
  xapp>>xsimpl>>
  metis_tac[]
QED

val set_indices_arr = process_topdecs`
  fun set_indices_arr inds s vimap rinds =
  case s of
    Inr v =>
    if Vector.length v = 0 then (inds,vimap)
    else (rinds,vimap)
  | Inl (n,ls) =>
    (case Array.lookup vimap None n of
      None => (inds,vimap)
    | Some (Inl _) =>
        (inds, Array.updateResize vimap None n (Some (Inl (List.length rinds,rinds))))
    | Some (Inr _) => (rinds,vimap))` |> append_prog;

Theorem set_indices_arr_spec:
  (LIST_TYPE NUM) inds indsv ∧
  subst_TYPE s sv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  (LIST_TYPE NUM) rinds rindsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "set_indices_arr" (get_ml_prog_state()))
    [indsv; sv; vimapv; rindsv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
        SEP_EXISTS vimapv' vimaplsv'.
        ARRAY vimapv' vimaplsv' *
        &(
          PAIR_TYPE
            (LIST_TYPE NUM)
            (λl v.
              LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
              v = vimapv')
            (set_indices inds s vimap rinds) v))
Proof
  rw[]>>
  xcf "set_indices_arr" (get_ml_prog_state ())>>
  reverse (Cases_on`s`)>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    simp[set_indices_def]>>
    rpt xlet_autop>>
    xif
    >-  (xcon>>xsimpl>> simp[LIST_TYPE_def,PAIR_TYPE_def]>>metis_tac[ARRAY_refl])>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_refl])>>
  Cases_on`x`>>gvs[PAIR_TYPE_def,set_indices_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE vimapn_TYPE (any_el q vimap NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  every_case_tac>>
  gvs[OPTION_TYPE_def,SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch
  >-
    (xcon>>xsimpl)
  >- (
    rpt xlet_autop>>
    xlet_auto>>
    xcon>>xsimpl>>
    irule LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def,SUM_TYPE_def])
  >-
    (xcon>>xsimpl)
QED

Overload "vomap_TYPE" = ``STRING_TYPE``

val r = translate spt_to_vecTheory.prepend_def;
val r = translate (spt_to_vecTheory.to_flat_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])

Triviality to_flat_ind:
  to_flat_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "to_flat_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = to_flat_ind |> update_precondition;

val r = translate spt_to_vecTheory.spt_to_vec_def;
val res = translate fromAList_def;
val res = translate npbc_checkTheory.mk_subst_def;

(*
Definition print_lno_mini_def:
  print_lno_mini (lno:num) mini =
  case mini of NONE => toString lno ^ strlit " INF\n"
  | SOME (i:num) => toString lno ^ strlit"  " ^ toString i ^ strlit "\n"
End

val res = translate print_lno_mini_def; *)

val res = translate npbc_checkTheory.check_pres_def;

(* TODO: add the check for
  check_fresh_aspo_list c s ord vimap vomap *)
val check_red_arr = process_topdecs`
  fun check_red_arr lno pres ord obj b tcb fml inds id
    c s pfs idopt vimap vomap zeros =
  if check_pres pres s then
  let val s = mk_subst s in
  case red_fast s idopt pfs of
  None =>
  (
  let
    val bortcb = b orelse tcb
    val rinds = get_indices_arr fml inds s vimap in
    case set_indices_arr inds s vimap rinds of (inds',vimap') =>
    case do_rso ord s c obj vomap of (rsubs,rscopes) =>
  let
    val nc = not_1 c
    val cpfs = extract_scopes_arr lno rscopes s b fml rsubs pfs
    val fml_not_c = Array.updateResize fml None id (Some (nc,b)) in
     case check_scopes_arr lno cpfs b fml_not_c id (id+1) zeros of
       (fml', (id', zeros')) =>
     (case idopt of
       None =>
       let val u = rollback_arr fml' id id'
           val goals = subst_indexes_arr s bortcb fml' rinds in
           case red_cond_check bortcb fml' inds' nc pfs rsubs goals []
             of None =>
             (fml', (inds', (vimap', (id', zeros'))))
           | Some err =>
           raise Fail (format_failure_2 lno ("Redundancy subproofs did not cover all subgoals. Info: " ^ err ^ ".") (print_subproofs_err rsubs goals))
       end
    | Some cid =>
      if check_contradiction_fml_arr b fml' cid then
        let val u = rollback_arr fml' id id' in
           (fml', (inds', (vimap', (id', zeros'))))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
  end
  end)
  | Some (pf,cid) =>
    check_red_arr_fast lno b fml inds id c pf cid vimap zeros
  end
  else raise Fail (format_failure lno ("domain of substitution must not mention projection set."))
  ` |> append_prog;

(* Overloads all the _TYPEs that we will reuse *)
Overload "aspo_TYPE" = ``
  PAIR_TYPE
    (PAIR_TYPE (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE NUM)
      (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))))
    (LIST_TYPE (PAIR_TYPE BOOL NUM))``

Overload "obj_TYPE" = ``
  OPTION_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)``

Overload "subst_raw_TYPE" = ``LIST_TYPE (PAIR_TYPE NUM (SUM_TYPE BOOL (PBC_LIT_TYPE NUM)))``

Overload "pres_TYPE" = ``OPTION_TYPE (SPTREE_SPT_TYPE UNIT_TYPE)``

Theorem check_red_arr_spec:
  NUM lno lnov ∧
  pres_TYPE pres presv ∧
  OPTION_TYPE aspo_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  BOOL b bv ∧
  BOOL tcb tcbv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  subst_raw_TYPE s sv ∧
  scpfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr" (get_ml_prog_state()))
    [lnov; presv; ordv; objv; bv; tcbv; fmlv; indsv; idv;
      cv; sv; pfsv; idoptv; vimapv; vomapv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros' vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_red_list pres ord obj b tcb fmlls inds id
              c s pfs idopt vimap vomap zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v.
                    LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                    v = vimapv')
                (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_red_list pres ord obj b tcb fmlls inds id
              c s pfs idopt vimap vomap zeros = NONE)))
Proof
  rw[]>>
  xcf "check_red_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (
    xsimpl>>
    simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,check_red_list_def]>>
    metis_tac[ARRAY_W8ARRAY_refl,NOT_EVERY,Fail_exn_def])>>
  xlet_auto
  >- (
    xsimpl>>
    simp (eq_lemmas()))>>
  xlet_autop>>
  `check_fresh_aspo_list c s ord vimap vomap` by cheat>>
  rw[check_red_list_def]>>
  reverse (Cases_on`red_fast (mk_subst s) idopt pfs`)
  >- (
    simp[]>>Cases_on`x`>>fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    xmatch>>
    xapp>>
    metis_tac[])>>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet`POSTv v. ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
    ARRAY vimapv vimaplsv *
    &BOOL (b ∨ tcb) v`
  >- (
    xlog>>xsimpl>>rw[]>>fs[]>>
    xvar>>xsimpl)>>
  pairarg_tac>>gs[]>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  pairarg_tac>>gs[do_rso_def]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  gvs[AllCasePreds()]>>
  rename1`_ (not n) vvv`>>
  `LIST_REL (OPTION_TYPE bconstraint_TYPE)
    (update_resize fmlls NONE (SOME (not n,b)) id)
    (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
            (Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [vvv; bv]]) id)` by (
    match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def,PAIR_TYPE_def])>>
  xlet_auto
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  gvs[AllCasePreds()]>>
  rename1`check_scopes_list _ _ _ _ _ _ = SOME yyy`>>
  PairCases_on`yyy`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  Cases_on`idopt`>>fs[OPTION_TYPE_def,do_red_check_def]>>xmatch
  >- (
    ntac 2 xlet_autop>>
    xlet`POSTv v. W8ARRAY zerosv' zeros' * ARRAY fmlv' fmllsv'' *
           ARRAY vimapv' vimaplsv' * &(LIST_TYPE NUM) [] v`
    >- (
      xcon>>xsimpl>>
      simp[LIST_TYPE_def])>>
    xlet_autop>>
    fs[do_red_check_def]>>
    pop_assum mp_tac>>IF_CASES_TAC>>
    strip_tac>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      fs[red_cond_check_def]>>
      pairarg_tac>>fs[]>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def]>>
      xsimpl)
    >- (
      rpt xlet_autop>>
      fs[red_cond_check_def]>>
      xraise>>
      xsimpl>>
      rw[]>>fs[]>>
      metis_tac[ARRAY_W8ARRAY_refl,NOT_EVERY,Fail_exn_def]) )>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    rw[]>>fs[]>>
    metis_tac[ARRAY_W8ARRAY_refl,NOT_EVERY,Fail_exn_def]) >>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[PAIR_TYPE_def]>>
  xsimpl
QED

val res = translate (opt_cons_def |> REWRITE_RULE [ind_lim_def]);

val update_vimap_arr = process_topdecs`
  fun update_vimap_arr vimap v ls =
  case ls of [] => vimap
  | ((i,n)::ns) =>
    update_vimap_arr
    (Array.updateResize vimap None n
      (Some (opt_cons v (Array.lookup vimap None n))))
    v
    ns` |> append_prog;

Theorem update_vimap_arr_spec:
  ∀ls lsv vimap vimaplsv vimapv.
  LIST_TYPE (PAIR_TYPE INT NUM) ls lsv ∧
  NUM v vv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "update_vimap_arr" (get_ml_prog_state()))
    [vimapv; vv; lsv]
    (ARRAY vimapv vimaplsv)
    (POSTv vimapv'.
        SEP_EXISTS vimaplsv'.
        ARRAY vimapv' vimaplsv' *
        &(
        LIST_REL (OPTION_TYPE vimapn_TYPE) (update_vimap vimap v ls) vimaplsv'))
Proof
  Induct>>
  rw[]>>
  xcf "update_vimap_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]
  >- (
    xmatch>>
    xvar>>xsimpl>>
    simp[update_vimap_def])>>
  Cases_on`h`>>gvs[PAIR_TYPE_def,update_vimap_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE vimapn_TYPE (any_el r vimap NONE) v''` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  xlet`POSTv res.
    ARRAY vimapv vimaplsv *
    &vimapn_TYPE (opt_cons v (any_el r vimap NONE)) res`
  >- (
    xapp>>xsimpl  >>
    metis_tac[])>>
  rpt xlet_autop>>
  xlet_auto>>
  xapp>>xsimpl>>
  match_mp_tac LIST_REL_update_resize>>
  fs[OPTION_TYPE_def,PAIR_TYPE_def]
QED

val check_sstep_arr = process_topdecs`
  fun check_sstep_arr lno step pres ord obj tcb fml inds id
    vimap vomap zeros =
  case step of
    Lstep lstep =>
    (case check_lstep_arr lno lstep False fml 0 id zeros of
      (rfml,(c,(id',zeros))) =>
      (case c of
        None => (rfml,(inds,(vimap,(id',zeros))))
      | Some cc =>
        (Array.updateResize rfml None id' (Some cc),
          (sorted_insert id' inds,
          (update_vimap_arr vimap id' (fst (fst cc)),
          (id'+1,
          zeros)))) ))
  | Red c s pfs idopt =>
    (case check_red_arr lno pres ord obj False tcb
        fml inds id c s pfs idopt vimap vomap zeros of
    (fml',(rinds,(vimap',(id',zeros)))) =>
       (Array.updateResize fml' None id'
          (Some (c,tcb)),
        (sorted_insert id' rinds,
        (update_vimap_arr vimap' id' (fst c),
        (id'+1,
        zeros)))))
  ` |> append_prog

val NPBC_CHECK_SSTEP_TYPE_def = theorem "NPBC_CHECK_SSTEP_TYPE_def";

Theorem check_sstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_SSTEP_TYPE step stepv ∧
  pres_TYPE pres presv ∧
  OPTION_TYPE aspo_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  BOOL tcb tcbv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_sstep_arr" (get_ml_prog_state()))
    [lnov; stepv; presv; ordv; objv; tcbv; fmlv; indsv; idv; vimapv; vomapv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_sstep_list step pres ord obj tcb
            fmlls inds id vimap vomap zeros of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v.
                    LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                    v = vimapv')
                (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ))) res v)
          )
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_sstep_list step pres ord obj tcb
            fmlls inds id vimap vomap zeros = NONE)))
Proof
  rw[]>>
  xcf "check_sstep_arr" (get_ml_prog_state ())>>
  rw[check_sstep_list_def]>>
  Cases_on`step`>>fs[NPBC_CHECK_SSTEP_TYPE_def]
  >- ( (* lstep *)
    xmatch>>
    xlet_autop>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv vimaplsv *
        &(
          case check_lstep_list l F fmlls 0 id zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (OPTION_TYPE bconstraint_TYPE)
              (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv') )) res v ∧ EVERY (λw. w = 0w) zeros'
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv vimaplsv *
        & (Fail_exn e ∧
        check_lstep_list l F fmlls 0 id zeros = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      qexists_tac`F`>>simp[]>>
      CONJ_TAC >- EVAL_TAC>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    Cases_on`x1`>>
    fs[opt_update_inds_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,PULL_EXISTS]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
    qexists_tac`A`>>xsimpl>>
    unabbrev_all_tac>>
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def])
  >- ( (*Red*)
    xmatch>>
    xlet_autop>>
    rename1`check_red_list pres ord obj F tcb fmlls inds id
              c s pfs idopt vimap vomap zeros`>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_red_list pres ord obj F tcb fmlls inds id
              c s pfs idopt vimap vomap zeros of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (λl v.
                    LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                    v = vimapv')
                (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_red_list pres ord obj F tcb fmlls inds id
              c s pfs idopt vimap vomap zeros = NONE))`
    >- (
      xapp >> xsimpl>>
      CONJ_TAC >- EVAL_TAC>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    every_case_tac>>fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    match_mp_tac LIST_REL_update_resize>>
    simp[OPTION_TYPE_def,PAIR_TYPE_def]>>
    EVAL_TAC
  )
QED

val _ = register_type ``:cstep ``

val res = translate npbc_checkTheory.trans_subst_def;
val res = translate npbc_checkTheory.build_fml_def;

val res = translate npbc_checkTheory.lookup_core_only_def;
val res = translate npbc_checkTheory.extract_clauses_def;

val extract_clauses_side = Q.prove(
  `∀a b c d e f. extract_clauses_side a b c d e f`,
  Induct_on`e`>>rw[Once (fetch "-" "extract_clauses_side_def")]>>
  gvs[el_side]) |> update_precondition

val res = translate FOLDL;
val res = translate npbc_checkTheory.check_cutting_def;
val res = translate npbc_checkTheory.check_contradiction_fml_def;
val res = translate npbc_checkTheory.insert_fml_def;

val res = translate npbc_checkTheory.nn_int_def;
val nn_int_side = Q.prove(
  `∀x. nn_int_side x`,
  EVAL_TAC>>
  intLib.ARITH_TAC
  ) |> update_precondition
val res = translate npbc_checkTheory.rup_pass1_def;
val res = translate npbc_checkTheory.rup_pass2_def;
val res = translate npbc_checkTheory.update_assg_def;
val res = translate npbc_checkTheory.model_bounding_def;
val res = translate npbc_checkTheory.get_rup_constraint_def;
val res = translate npbc_checkTheory.check_rup_def;
val res = translate npbc_checkTheory.check_lstep_def;
val res = translate npbc_checkTheory.list_insert_fml_def;
val res = translate npbc_checkTheory.check_subproofs_def;

val res = translate (npbc_checkTheory.check_ws_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate
  (npbc_checkTheory.check_transitivity_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate npbc_checkTheory.refl_subst_def;
val res = translate npbc_checkTheory.check_reflexivity_def;

val res = translate npbc_checkTheory.red_subgoals_def;
val res = translate npbc_checkTheory.extract_scopes_def;
val res = translate npbc_checkTheory.check_scopes_def;

Theorem check_red_simp_eq:
  check_red NONE NONE NONE F F fml id c s pfs idopt =
    ( let nc = not c in
      let (fml_not_c,id1) = insert_fml F fml id (not c) in
      let s = mk_subst s in
      let w = subst_fun s in
      let (rsubs,rscopes) = red_subgoals NONE w c NONE in
      case extract_scopes rscopes pfs w F fml rsubs of
        NONE => NONE
      | SOME cpfs =>
      (case check_scopes cpfs F fml_not_c id1 of
        NONE => NONE
      | SOME (fml',id') =>
        let chk =
          (case idopt of
            NONE =>
              let gfml = mk_core_fml F fml in
              let goals = toAList (map_opt (subst_opt w) gfml) in
              let (l,r) = extract_scoped_pids pfs LN LN in
                (* Every goal from the formula is checked *)
                split_goals gfml nc l goals  ∧
                (* Every # goal is checked *)
                EVERY (λ(id,cs).
                  lookup id r ≠ NONE ∨
                  check_hash_triv nc cs
                  )
                  (enumerate 0 rsubs)
            | SOME cid =>
              check_contradiction_fml F fml' cid) in
        if chk then
          SOME id'
        else NONE) )
Proof
  simp[npbc_checkTheory.check_red_def,npbc_checkTheory.check_pres_def,npbc_checkTheory.check_fresh_aspo_def]>>
  gvs[npbc_checkTheory.red_subgoals_def,npbc_checkTheory.dom_subst_def]>>
  rpt (pairarg_tac>>fs[])
QED

Definition check_spec_aux'_def:
  (check_spec_aux' (as:num list) fmlid (ls:specproof) =
    case ls of [] => T
  | (c,s,pfs,idopt)::gs =>
    if check_support as s then
      let (fml,id) = fmlid in
      let nc = not c in
      let (fml_not_c,id1) = insert_fml F fml id (not c) in
      let s = mk_subst s in
      let w = subst_fun s in
      let rsubs = [[not (subst w c)]] in
      case extract_scopes ([[]]:((int # num) list # num) list list) pfs w F fml rsubs of
        NONE => F
      | SOME cpfs =>
      (case check_scopes cpfs F fml_not_c id1 of
        NONE => F
      | SOME (fml',id') =>
        let chk =
          (case idopt of
            NONE =>
              let gfml = mk_core_fml F fml in
              let goals = toAList (map_opt (subst_opt w) gfml) in
              let (l,r) = extract_scoped_pids pfs LN LN in
                (* Every goal from the formula is checked *)
                split_goals gfml nc l goals  ∧
                (* Every # goal is checked *)
                EVERY (λ(id,cs).
                  lookup id r ≠ NONE ∨
                  check_hash_triv nc cs
                  )
                  (enumerate 0 rsubs)
            | SOME cid =>
              check_contradiction_fml F fml' cid) in
        if chk then
          check_spec_aux' as (insert_fml F fml id' c) gs
        else F)
    else F
  )
End

Theorem split_goals_alt:
  split_goals (fml:npbc num_map)
    (extra:npbc) (proved:num_set)
    (goals:(num # (int # num) list # num) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). sptree$lookup i proved ≠ NONE) goals in
  let proved = MAP SND lp in
  let f = MAP SND (toAList fml) in
  EVERY (λ(i,c). check_triv extra (not c) ∨ mem_constraint c proved ∨ MEMBER c f) lf
Proof
  rw[npbc_checkTheory.split_goals_def]>>
  pairarg_tac>>rw[EVERY_MEM]>>
  simp[GSYM MEMBER_INTRO,MEM_MAP,range_def,MEM_toAList,EXISTS_PROD,PULL_EXISTS]>>
  eq_tac>>rw[]>>first_x_assum drule>>
  pairarg_tac>>rw[]>>
  metis_tac[PAIR]
QED

val res = translate npbc_checkTheory.map_opt_def;
val res = translate npbc_checkTheory.mk_core_fml_def;
val res = translate split_goals_alt;
val res = translate (npbc_checkTheory.check_support_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate check_spec_aux'_def;

Theorem check_spec_aux_eq:
  ∀ls fmlid.
  check_spec_aux as fmlid ls =
  check_spec_aux' as fmlid ls
Proof
  Induct>>rw[Once check_spec_aux'_def]>>
  Cases_on`fmlid`>>
  simp[npbc_checkTheory.check_spec_aux_def]>>
  PairCases_on`h`>>simp[npbc_checkTheory.check_spec_aux_def]>>
  simp[npbc_checkTheory.check_red_def,npbc_checkTheory.check_pres_def,npbc_checkTheory.check_fresh_aspo_def]>>
  gvs[npbc_checkTheory.red_subgoals_def,npbc_checkTheory.dom_subst_def]>>
  rpt (pairarg_tac>>fs[])>>
  eq_tac>>rw[]>>gvs[AllCasePreds(),AllCaseEqs()]
QED

val res = translate (npbc_checkTheory.check_spec_def |> REWRITE_RULE[check_spec_aux_eq]);

Definition check_storeorder_def:
  check_storeorder vars gspec f pfst pfsr =
  if check_spec vars gspec
  then
    let aord = mk_aord vars f gspec in
    if check_good_aord aord
    then
      case check_transitivity aord pfst of
        NONE => NONE
      | SOME id =>
        if check_reflexivity aord pfsr id then SOME aord
        else NONE
    else NONE
  else NONE
End

val res = translate npbc_checkTheory.mk_aord_def;
val res = translate (npbc_checkTheory.check_good_aord_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate check_storeorder_def;

val res = translate npbcTheory.b2n_def;
val res = translate npbcTheory.eval_lit_def;

val eval_lit_side = Q.prove(
  `eval_lit_side x y z`,
  EVAL_TAC>>
  Cases_on`x z`>>simp[b2n_def]
  ) |> update_precondition

Theorem eval_term_compute:
  eval_term w (c,v) =
  if w v
  then
    if c < 0 then 0 else Num c
  else
    if c < 0 then Num (-c) else 0
Proof
  rw[]>>
  intLib.ARITH_TAC
QED

val res = translate eval_term_compute;

val eval_term_side = Q.prove(
  `eval_term_side x yz`,
  EVAL_TAC>>
  rw[]>>
  intLib.ARITH_TAC
  ) |> update_precondition

Theorem eval_obj_compute:
  eval_obj fopt w =
  case fopt of NONE => 0
  | SOME (f,c:int) =>
    FOLDL (λn cv. &(eval_term w cv) + n) c f
Proof
  Cases_on`fopt`>>simp[eval_obj_def]>>
  `?f c. x = (f,c)` by metis_tac[PAIR]>>
  simp[]>>
  qid_spec_tac`c`>>
  pop_assum kall_tac>>
  Induct_on`f`>>rw[]>>
  first_x_assum (fn th => DEP_REWRITE_TAC[GSYM th])>>
  intLib.ARITH_TAC
QED

val res = translate eval_obj_compute;
val res = translate npbc_checkTheory.opt_lt_def;

Theorem satisfies_npbc_compute:
  satisfies_npbc w xsn ⇔
    case xsn of (xs,n) =>
    FOLDL (λn cv. eval_term w cv + n) 0 xs ≥ n
Proof
  `?xs n. xsn = (xs,n)` by metis_tac[PAIR]>>
  simp[satisfies_npbc_def,SUM_MAP_FOLDL]
QED

val res = translate satisfies_npbc_compute;

val r = translate (npbc_checkTheory.to_flat_d_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])

Triviality to_flat_d_ind:
  to_flat_d_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "to_flat_d_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = to_flat_d_ind |> update_precondition;

val res = translate npbc_checkTheory.mk_obj_vec_def;
val res = translate npbc_checkTheory.vec_lookup_d_def;
val res = translate npbc_checkTheory.check_obj_def;

val res = translate npbc_checkTheory.model_improving_def;

Definition do_dso_def:
  do_dso spo s c obj =
  dom_subgoals spo (subst_fun s) c obj
End

val res = translate npbc_checkTheory.neg_dom_subst_def;
val res = translate npbc_checkTheory.dom_subgoals_def;
val res = translate do_dso_def;

val core_fmlls_arr = process_topdecs`
  fun core_fmlls_arr fml is =
  case is of [] => []
  | (i::is) =>
    (case Array.lookup fml None i of
      None => core_fmlls_arr fml is
    | Some (v,b) =>
      if b then (i,v)::core_fmlls_arr fml is
      else core_fmlls_arr fml is)` |> append_prog;

Theorem core_fmlls_arr_spec:
  ∀inds indsv fmlv fmlls fmllsv.
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "core_fmlls_arr" (get_ml_prog_state()))
    [fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
        &(LIST_TYPE (PAIR_TYPE NUM constraint_TYPE)
          (core_fmlls fmlls inds) v))
Proof
  Induct>>
  rw[]>>
  xcf "core_fmlls_arr" (get_ml_prog_state ())>>
  simp[core_fmlls_def]>>
  fs[LIST_TYPE_def]>>xmatch
  >-
    (xcon>>xsimpl)>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>xsimpl)>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  qpat_x_assum`Conv _ _ = any_el _ _ _` (assume_tac o SYM)>>
  xmatch>>
  xif>- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def,PAIR_TYPE_def])>>
  xapp>>
  metis_tac[]
QED

Definition check_dom_list_def:
  check_dom_list spo obj fml inds id c s pfs idopt zeros =
  let rinds = reindex fml inds in
  let corels = core_fmlls fml rinds in
  let nc = not c in
  let fml_not_c = update_resize fml NONE (SOME (nc,F)) id in
  let w = subst_fun s in
  let (dsubs,dscopes,dindex) = dom_subgoals spo w c obj in
  case extract_scopes_list dscopes s F fml dsubs pfs of
    NONE => NONE
  | SOME cpfs =>
    (case check_scopes_list cpfs F fml_not_c id (id+1) zeros of
      NONE => NONE
    | SOME (fml',(id',zeros')) =>
      let rfml = rollback fml' id id' in
      if do_dom_check idopt fml' rfml w
        corels rinds nc pfs dsubs dindex then
        SOME (rfml,rinds,id',zeros')
      else NONE)
End

Definition core_subgoals_def:
  core_subgoals s ls =
  MAP_OPT (subst_opt (subst_fun s)) ls
End

val res = translate MAP_OPT_def;
val res = translate core_subgoals_def;

Definition map_snd_def:
  map_snd ls = MAP SND ls
End

val res = translate map_snd_def;

val res = translate npbc_checkTheory.find_scope_1_def;

(* TODO: we can defer corels until the split *)
val check_dom_arr = process_topdecs`
  fun check_dom_arr lno spo obj fml inds
    id c s pfs idopt zeros =
    case do_dso spo s c obj of (dsubs,(dscopes,dindex)) =>
    let
    val rinds = reindex_arr fml inds
    val corels = core_fmlls_arr fml rinds
    val cpfs = extract_scopes_arr lno dscopes s False fml dsubs pfs
    val nc = not_1 c
    val fml_not_c = Array.updateResize fml None id (Some (nc,False)) in
     case check_scopes_arr lno cpfs False
      fml_not_c id (id+1) zeros of
       (fml',(id',zeros')) =>
       (case idopt of
         None =>
         let val u = rollback_arr fml' id id'
             val goals = core_subgoals s corels in
             if find_scope_1 dindex pfs then
               case red_cond_check False fml' rinds nc pfs dsubs goals [dindex] of
                 None => (fml',(rinds,(id',zeros')))
               | Some err =>
                raise Fail (format_failure_2 lno ("Dominance subproofs did not cover all subgoals. Info: " ^ err ^ ".") (print_subproofs_err dsubs goals))
            else
                raise Fail (format_failure_2 lno ("Dominance subproofs did not cover all subgoals. Info: missing geq scope proof.") (print_subproofs_err dsubs goals))
         end
       | Some cid =>
         if check_contradiction_fml_arr False fml' cid then
           let val u = rollback_arr fml' id id' in
             (fml', (rinds, (id', zeros')))
           end
         else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
    end` |> append_prog;

Theorem check_dom_arr_spec:
  NUM lno lnov ∧
  aspo_TYPE spo spov ∧
  obj_TYPE obj objv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  subst_TYPE s sv ∧
  scpfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_dom_arr" (get_ml_prog_state()))
    [lnov; spov; objv; fmlv; indsv; idv;
      cv; sv; pfsv; idoptv;zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_dom_list spo obj fmlls inds id
              c s pfs idopt zeros of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') )) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_dom_list spo obj fmlls inds id
              c s pfs idopt zeros = NONE)))
Proof
  rw[]>>
  xcf "check_dom_arr" (get_ml_prog_state ())>>
  rw[]>>
  xlet_autop>>
  `∃dsubs dscopes dindex. do_dso spo s c obj = (dsubs,dscopes,dindex)` by
    metis_tac[PAIR]>>
  rw[]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet`(POSTve
    (λv.
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      &(case extract_scopes_list dscopes s F fmlls dsubs pfs of
          NONE => F
        | SOME res => check_scope_TYPE res v))
    (λe.
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      & (Fail_exn e ∧ extract_scopes_list dscopes s F fmlls dsubs pfs = NONE)))`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    rpt(first_x_assum (irule_at Any))>>
    qexists_tac`F`>>
    CONJ_TAC >- EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    fs[do_dso_def,check_dom_list_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  gvs[AllCasePreds(),do_dso_def]>>
  rpt xlet_autop>>
  rename1`_ (not n) vvv`>>
  qmatch_asmsub_abbrev_tac`Conv (SOME (TypeStamp "Some" 2))
          [Conv NONE [vvv;bbb]]`>>
  `LIST_REL (OPTION_TYPE bconstraint_TYPE)
    (update_resize fmlls NONE (SOME (not n,F)) id)
    (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
            (Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [vvv;bbb]]) id)` by (
    match_mp_tac LIST_REL_update_resize>>
    unabbrev_all_tac>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    EVAL_TAC)>>
  fs[Abbr`bbb`]>>
  xlet`(POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_scopes_list res F
            (update_resize fmlls NONE (SOME (not n,F)) id)
            id (id+1) zeros of
            NONE => F
          | SOME res' =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ) res' v))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_scopes_list res F
            (update_resize fmlls NONE (SOME (not n,F)) id)
            id (id+1) zeros = NONE)))`
  >- (
    xapp>>
    xsimpl>>
    CONJ_TAC >- EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[check_dom_list_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  fs[AllCasePreds()]>>
  pop_assum mp_tac>>
  PairCases_on`res'`>>fs[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  Cases_on`idopt`>>
  fs[OPTION_TYPE_def,do_dom_check_def,check_dom_list_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Fail_exn_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    qmatch_asmsub_abbrev_tac`LIST_REL _ fmlls'' fmllsv''`>>
    xlet`POSTv resv.
         ARRAY fmlv' fmllsv'' * W8ARRAY zerosv' zeros' *
         & ∃err.
           OPTION_TYPE STRING_TYPE
           (if
                red_cond_check F fmlls'' (reindex fmlls inds) (not n) pfs
                  dsubs
                  (core_subgoals s (core_fmlls fmlls (reindex fmlls inds)))
                  [dindex]
              then
                NONE
              else SOME err) resv`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>xsimpl>>
      qexists_tac`[dindex]`>>
      qexists_tac`F`>>
      xsimpl>>
      CONJ_TAC >- EVAL_TAC>>
      simp[LIST_TYPE_def])>>
    pop_assum mp_tac>>IF_CASES_TAC>>
    strip_tac>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      pairarg_tac>>fs[red_cond_check_def,core_subgoals_def]>>
      fs[PAIR_TYPE_def,OPTION_TYPE_def]>>
      xsimpl)
    >- (
      rpt xlet_autop>>
      fs[red_cond_check_def]>>pairarg_tac>>fs[core_subgoals_def]>>
      xraise>>xsimpl>>
      fs[red_cond_check_def]>>rw[]>>
      metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def,NOT_EVERY])
  )>>
  rename1`check_contradiction_fml_list F A B`>>
  xlet_autop>>
  xlet`POSTv v.
    ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
    &BOOL (check_contradiction_fml_list F A B) v`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    qexists_tac`F`>>xsimpl)>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    rw[]>>fs[]>>
    metis_tac[ARRAY_W8ARRAY_refl,NOT_EVERY,Fail_exn_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  xsimpl
QED

val res = translate npbc_checkTheory.update_bound_def;

val core_from_inds_arr = process_topdecs`
  fun core_from_inds_arr lno fml is =
  case is of [] => fml
  | (i::is) =>
    (case Array.lookup fml None i of
      None => raise Fail (format_failure lno
        "core transfer given invalid ids")
    | Some (c,b) =>
      core_from_inds_arr lno (Array.updateResize fml None i (Some (c,True))) is)` |> append_prog;

Theorem core_from_inds_arr_spec:
  ∀inds indsv fmlv fmlls fmllsv.
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "core_from_inds_arr" (get_ml_prog_state()))
    [lnov; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case core_from_inds fmlls inds of
            NONE => F
          | SOME res =>
            (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
         core_from_inds fmlls inds = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "core_from_inds_arr" (get_ml_prog_state ())>>
  simp[core_from_inds_def]>>
  fs[LIST_TYPE_def]>>xmatch
  >-
    (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  Cases_on`any_el h fmlls NONE`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_refl])>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  qpat_x_assum`Conv _ _ = any_el _ _ _` (assume_tac o SYM)>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  xapp>>
  CONJ_TAC >- (
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    EVAL_TAC)>>
  metis_tac[]
QED

(* TODO: Can be improved with lookup_core_only *)
val all_core_arr = process_topdecs `
  fun all_core_arr fml ls iacc =
  case ls of
    [] => Some (List.rev iacc)
  | (i::is) =>
  case Array.lookup fml None i of
    None => all_core_arr fml is iacc
  | Some (v,b') =>
      if b' then all_core_arr fml is (i::iacc)
      else None` |> append_prog;

Theorem all_core_arr_spec:
  ∀inds indsv b bv fmlls fmlv iacc iaccv vacc vaccv.
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) iacc iaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_core_arr" (get_ml_prog_state()))
    [fmlv; indsv; iaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(OPTION_TYPE (LIST_TYPE NUM)
        (all_core_list fmlls inds iacc) v))
Proof
  Induct>>
  rw[]>>
  xcf"all_core_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[all_core_list_def,LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE
    (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[all_core_list_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xif>> rpt xlet_autop
  >- (
    xapp>>
    xsimpl>>
    simp[LIST_TYPE_def])>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def]
QED

val res = translate npbc_checkTheory.change_obj_subgoals_def;
val res = translate emp_vec_def;
val res = translate do_change_check_def;
val res = translate npbc_checkTheory.add_obj_def;
val res = translate npbc_checkTheory.mk_diff_obj_def;
val res = translate npbc_checkTheory.mk_tar_obj_def;

val check_change_obj_arr = process_topdecs `
  fun check_change_obj_arr lno b fml id obj fc' pfs zeros =
  case obj of None =>
    raise Fail (format_failure lno ("no objective to change"))
  | Some fc =>
    let
    val csubs = change_obj_subgoals (mk_tar_obj b fc) fc'
    val bb = True
    val e = []
    val cpfs = extract_clauses_arr lno emp_vec bb fml csubs pfs e in
    case check_subproofs_arr lno cpfs bb fml id id zeros of
       (fml', (id', zeros')) =>
      let val u = rollback_arr fml' id id' in
        if do_change_check pfs csubs then
          (fml',(mk_diff_obj b fc fc', (id', zeros')))
       else raise Fail (format_failure lno ("Objective change subproofs did not cover all subgoals. Expected: #[1-2]"))
       end
    end` |> append_prog

Theorem check_change_obj_arr_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  NUM id idv ∧
  obj_TYPE obj objv ∧
  (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT) fc fcv ∧
  pfs_TYPE pfs pfsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_change_obj_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; idv; objv; fcv; pfsv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_change_obj_list b fmlls id obj fc pfs zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)
            (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') )) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_change_obj_list b fmlls id obj fc pfs zeros = NONE)))
Proof
  rw[]>>
  xcf "check_change_obj_arr" (get_ml_prog_state ())>>
  simp[check_change_obj_list_def]>>
  Cases_on`obj`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def])>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
  xlet`(POSTve
    (λv.
      ARRAY aa vv * W8ARRAY zerosv zeros *
      &(case extract_clauses_list emp_vec T fmlls
          (change_obj_subgoals (mk_tar_obj b x) fc) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
  (λe.
    ARRAY aa vv * W8ARRAY zerosv zeros *
    & (Fail_exn e ∧
      extract_clauses_list emp_vec T fmlls
      (change_obj_subgoals (mk_tar_obj b x) fc) pfs [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>xsimpl>>
    qexists_tac`emp_vec`>>
    qexists_tac`T`>>
    qexists_tac`[]`>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- metis_tac[fetch "-" "emp_vec_v_thm"]>>
    xsimpl)
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>gvs[]>>
  strip_tac>>
  rename1`check_subproofs_list xx`>>
  xlet`(POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_subproofs_list xx T fmlls id id zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_subproofs_list xx T fmlls id id zeros = NONE)))`
  >- (
    xapp>>xsimpl>>
    CONJ_TAC>-EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>fs[]>>
  qmatch_goalsub_rename_tac`PAIR_TYPE _ _ xxx _`>>
  PairCases_on`xxx`>>fs[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>> xsimpl>>
  metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def]
QED

val res = translate npbc_checkTheory.v_iff_npbc_def;
val res = translate npbc_checkTheory.change_pres_subgoals_def;
val res = translate npbc_checkTheory.pres_only_def;
val res = translate npbc_checkTheory.update_pres_def;

val check_change_pres_arr = process_topdecs `
  fun check_change_pres_arr lno b fml id pres v c pfs zeros =
  case pres of None =>
    raise Fail (format_failure lno ("no projection set to change"))
  | Some pres =>
    if pres_only c pres v then
    let
    val csubs = change_pres_subgoals v c
    val bb = True
    val e = []
    val cpfs = extract_clauses_arr lno emp_vec bb fml csubs pfs e in
    case check_subproofs_arr lno cpfs bb fml id id zeros of
       (fml', (id', zeros')) =>
      let val u = rollback_arr fml' id id' in
        if do_change_check pfs csubs then
          (fml',(update_pres b v pres, (id', zeros')))
       else raise Fail (format_failure lno ("projection set change subproofs did not cover all subgoals. Expected: #[1-2]"))
       end
    end
    else raise Fail (format_failure lno ("defining constraint must mention only variables in the projection set (less variable itself)"))` |> append_prog

Theorem check_change_pres_arr_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  NUM id idv ∧
  pres_TYPE pres presv ∧
  NUM vx vxv ∧
  constraint_TYPE c cv ∧
  pfs_TYPE pfs pfsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_change_pres_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; idv; presv; vxv; cv; pfsv; zerosv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_change_pres_list b fmlls id pres vx c pfs zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE (SPTREE_SPT_TYPE UNIT_TYPE)
            (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros') )) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_change_pres_list b fmlls id pres vx c pfs zeros = NONE)))
Proof
  rw[]>>
  xcf "check_change_pres_arr" (get_ml_prog_state ())>>
  simp[check_change_pres_list_def]>>
  Cases_on`pres`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def])>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def])>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
  xlet`(POSTve
    (λv.
      ARRAY aa vv * W8ARRAY zerosv zeros *
      &(case extract_clauses_list emp_vec T fmlls
          (change_pres_subgoals vx c) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
  (λe.
    ARRAY aa vv * W8ARRAY zerosv zeros *
    & (Fail_exn e ∧
      extract_clauses_list emp_vec T fmlls
      (change_pres_subgoals vx c) pfs [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>xsimpl>>
    qexists_tac`emp_vec`>>
    qexists_tac`T`>>
    qexists_tac`[]`>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- metis_tac[fetch "-" "emp_vec_v_thm"]>>
    xsimpl)
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>gvs[]>>
  strip_tac>>
  rename1`check_subproofs_list xx`>>
  xlet`(POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        &(
          case check_subproofs_list xx T fmlls id id zeros of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        & (Fail_exn e ∧
          check_subproofs_list xx T fmlls id id zeros = NONE)))`
  >- (
    xapp>>xsimpl>>
    CONJ_TAC>-EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>fs[]>>
  qmatch_goalsub_rename_tac`PAIR_TYPE _ _ xxx _`>>
  PairCases_on`xxx`>>fs[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>> xsimpl>>
  metis_tac[ARRAY_W8ARRAY_refl,Fail_exn_def]
QED

val _ = register_type ``:proof_conf``

Definition get_pres_def:
  get_pres pc = pc.pres
End

val res = translate get_pres_def;

Definition get_ord_def:
  get_ord pc = pc.ord
End

val res = translate get_ord_def;

Definition get_obj_def:
  get_obj pc = pc.obj
End

val res = translate get_obj_def;

Definition get_tcb_def:
  get_tcb pc = pc.tcb
End

val res = translate get_tcb_def;

Definition get_id_def:
  get_id pc = pc.id
End

val res = translate get_id_def;

Definition get_orders_def:
  get_orders pc = pc.orders
End

val res = translate get_orders_def;

Definition get_chk_def:
  get_chk pc = pc.chk
End

val res = translate get_chk_def;

Definition get_bound_def:
  get_bound pc = pc.bound
End

val res = translate get_bound_def;

Definition get_dbound_def:
  get_dbound pc = pc.dbound
End

val res = translate get_dbound_def;

Definition set_id_def:
  set_id pc id' = pc with id := id'
End

val res = translate set_id_def;

Definition set_ord_def:
  set_ord pc ord' = pc with ord := ord'
End

val res = translate set_ord_def;

Definition check_tcb_idopt_pc_def:
  check_tcb_idopt_pc pc idopt =
  check_tcb_idopt pc.tcb idopt
End

val res = translate npbc_checkTheory.check_tcb_idopt_def;
val res = translate check_tcb_idopt_pc_def;

Definition check_tcb_ord_def:
  check_tcb_ord pc ⇔ ¬pc.tcb ∧ pc.ord = NONE
End

val res = translate check_tcb_ord_def;

Definition set_chk_def:
  set_chk pc chk' = pc with chk := chk'
End

val res = translate set_chk_def;

Definition set_tcb_def:
  set_tcb pc tcb' = pc with tcb := tcb'
End

val res = translate set_tcb_def;

Definition set_orders_def:
  set_orders pc orders' = pc with orders := orders'
End

val res = translate set_orders_def;

Definition obj_update_def:
  obj_update pc id' bound' dbound' =
    pc with
          <| id := id';
             bound := bound';
             dbound := dbound' |>
End

val res = translate obj_update_def;

Definition change_obj_update_def:
  change_obj_update pc id' fc' =
  pc with <| id := id'; obj := SOME fc' |>
End

val res = translate change_obj_update_def;

Definition change_pres_update_def:
  change_pres_update pc id' pres' =
  pc with <| id := id'; pres := SOME pres' |>
End

val res = translate change_pres_update_def;

Definition npbc_obj_string_def:
  (npbc_obj_string (xs,i:int) =
    concat [
      npbc_lhs_string xs;
      strlit" ";
      toString  i])
End

Definition err_obj_check_string_def:
  err_obj_check_string fc fc' =
  case fc of NONE => strlit"objective check failed, no objective available"
  | SOME fc =>
    concat[
    strlit"objective check failed, expect: ";
    npbc_obj_string fc';
    strlit" got: ";
    npbc_obj_string fc]
End

val res = translate npbc_obj_string_def;
val res = translate err_obj_check_string_def;
val res = translate npbc_checkTheory.eq_obj_def;
val res = translate npbc_checkTheory.check_eq_obj_def;

val fold_update_resize_bitset = process_topdecs`
  fun fold_update_resize_bitset ls acc =
    case ls of
      [] => acc
    | (cx::xs) =>
      case cx of (c,x) =>
      if x < Word8Array.length acc
      then
        (Word8Array.update acc x w8o;
        fold_update_resize_bitset xs acc)
      else
        let
        val arr = Word8Array.array (2*x+1) w8z
        val u = Word8Array.copy acc 0 (Word8Array.length acc) arr 0 in
          (Word8Array.update arr x w8o;
          fold_update_resize_bitset xs arr)
        end
        ` |> append_prog;

Theorem fold_update_resize_bitset_spec:
  ∀ls lsv accv accls.
  LIST_TYPE (PAIR_TYPE INT NUM) ls lsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fold_update_resize_bitset" (get_ml_prog_state()))
    [lsv; accv]
    (W8ARRAY accv accls)
    (POSTv v.
        W8ARRAY v (FOLDL (λacc (c,i). update_resize acc w8z w8o i) accls ls))
Proof
  Induct>>
  rw[]>>
  xcf "fold_update_resize_bitset" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>xmatch
  >- (
    xvar>>xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  assume_tac w8o_v_thm>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop>>
  xif
  >- (
    xlet_autop>>
    xapp>>xsimpl>>
    simp[update_resize_def])>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  simp[update_resize_def]
QED

val mk_vomap_arr = process_topdecs`
  fun mk_vomap_arr n fc =
  let
  val acc = Word8Array.array n w8z
  val acc = fold_update_resize_bitset (fst fc) acc in
    Word8Array.substring acc 0 (Word8Array.length acc)
  end` |> append_prog;

Theorem map_foldl_rel:
  ∀ls accA accB.
  MAP (CHR o w2n) accA = accB ⇒
  MAP (CHR ∘ w2n)
  (FOLDL (λacc (c,i). update_resize acc w8z w8o i) accA ls) =
  FOLDL (λacc i. update_resize acc #"\^@" #"\^A" i) accB (MAP SND ls)
Proof
  Induct>>rw[]>>
  first_x_assum match_mp_tac>>
  Cases_on`h`>>rw[update_resize_def,LUPDATE_MAP]>>
  EVAL_TAC
QED

Theorem mk_vomap_arr_spec:
  NUM n nv ∧
  (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT) fc fcv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "mk_vomap_arr" (get_ml_prog_state()))
    [nv; fcv]
    (emp)
    (POSTv v. &(vomap_TYPE (mk_vomap n fc) v))
Proof
  rw[]>>
  xcf "mk_vomap_arr" (get_ml_prog_state ())>>
  assume_tac w8z_v_thm>>
  xlet_auto>>
  rpt xlet_autop>>
  xlet_auto>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>> rw[]>>
  Cases_on`fc`>>fs[mk_vomap_def]>>
  qmatch_asmsub_abbrev_tac`strlit A`>>
  qmatch_goalsub_abbrev_tac`strlit B`>>
  qsuff_tac`A = B`>- metis_tac[]>>
  unabbrev_all_tac>>
  simp[]>>
  match_mp_tac map_foldl_rel>>
  simp[map_replicate]>>
  EVAL_TAC
QED

val check_cstep_arr = process_topdecs`
  fun check_cstep_arr lno cstep fml zeros inds vimap vomap pc =
  case cstep of
    Dom c s pfs idopt => (
    case get_ord pc of None =>
      raise Fail (format_failure lno "no order loaded for dominance step")
    | Some spo =>
      if check_pres (get_pres pc) s then
      case check_dom_arr lno spo (get_obj pc)
        fml inds (get_id pc) c (mk_subst s) pfs idopt zeros of
        (fml',(rinds,(id',zeros'))) =>
      (Array.updateResize fml' None id' (Some (c,get_tcb pc)),
       (zeros',
       (sorted_insert id' rinds,
       (update_vimap_arr vimap id' (fst c),
        (vomap, set_id pc (id'+1))))))
      else raise Fail (format_failure lno ("domain of substitution must not mention projection set."))
    )
  | Sstep sstep => (
    case check_sstep_arr lno sstep (get_pres pc) (get_ord pc) (get_obj pc)
      (get_tcb pc) fml inds (get_id pc) vimap vomap zeros of
      (fml',(inds',(vimap',(id',zeros')))) =>
      (fml',(zeros',(inds',(vimap',(vomap, set_id pc id'))))))
  | Checkeddelete n s pfs idopt => (
    if check_tcb_idopt_pc pc idopt
    then
      let val c = lookup_core_only_err_arr lno True fml n in
        (delete_arr n fml;
        case
          check_red_arr lno (get_pres pc) (get_ord pc) (get_obj pc) True
            (get_tcb pc) fml inds (get_id pc)
            c s pfs idopt vimap vomap zeros of
            (fml',(inds',(vimap',(id',zeros')))) =>
            (fml',(zeros',(inds',(vimap',(vomap,set_id pc id'))))))
      end
    else raise Fail
      (format_failure lno
        "invalid proof state for checked deletion"))
  | Uncheckeddelete ls => (
    if check_tcb_ord pc then
      (list_delete_arr ls fml;
        (fml, (zeros, (inds, (vimap, (vomap, set_chk pc False))))))
    else
      case all_core_arr fml inds [] of None =>
        raise Fail (format_failure lno
        "not all constraints in core")
      | Some inds' =>
        (list_delete_arr ls fml;
          (fml, (zeros, (inds', (vimap, (vomap, set_chk pc False)))))))
  | Transfer ls => (
      let val fml' = core_from_inds_arr lno fml ls in
        (fml', (zeros, (inds, (vimap, (vomap, pc)))))
      end)
  | Strengthentocore b => (
    let val inds' = reindex_arr fml inds in
      if b
      then (
        let val fml' = core_from_inds_arr lno fml inds' in
          (fml',(zeros, (inds', (vimap, (vomap, set_tcb pc b)))))
        end)
      else
        (fml, (zeros, (inds', (vimap, (vomap, set_tcb pc b)))))
    end)
  | Loadorder nn xs =>
    let val inds' = reindex_arr fml inds in
    case Alist.lookup (get_orders pc) nn of
      None =>
        raise Fail (format_failure lno ("no such order: " ^ nn))
    | Some ord' =>
      if List.length xs = List.length (fst (snd ord')) then
        let val fml' = core_from_inds_arr lno fml inds' in
        (fml', (zeros, (inds', (vimap, (vomap, set_ord pc (Some (ord',xs)))))))
        end
      else
        raise Fail
          (format_failure lno ("invalid order instantiation"))
    end
  | Unloadorder =>
    (case get_ord pc of None =>
     raise Fail (format_failure lno ("no order loaded"))
    | Some spo =>
      (fml,(zeros,(inds,(vimap,(vomap,set_ord pc None))))))
  | Storeorder name vars gspec f pfsr pfst =>
    (case check_storeorder vars gspec f pfst pfsr of
      Some aord =>
       (fml, (zeros, (inds, (vimap, (vomap, set_orders pc ((name,aord)::get_orders pc))))))
    | _ => raise Fail (format_failure lno ("invalid order definition")))
  | Obj w mi bopt => (
    let val obj = get_obj pc in
      case check_obj obj w
        (map_snd (core_fmlls_arr fml inds)) bopt of
      None =>
       raise Fail (format_failure lno
        ("supplied assignment did not satisfy constraints or did not improve objective"))
      | Some new =>
      case update_bound (get_chk pc)
        (get_bound pc) (get_dbound pc) new of (bound',dbound') =>
      if mi
      then
        let
          val id = get_id pc
          val c = model_improving obj new in
          (Array.updateResize fml None id (Some (c,True)),
           (zeros,
           (sorted_insert id inds,
           (update_vimap_arr vimap id (fst c),
           (vomap,
            obj_update pc (id+1) bound' dbound')))))
        end
      else
        (fml, (zeros, (inds, (vimap, (vomap, obj_update pc (get_id pc) bound' dbound')))))
    end
    )
  | Changeobj b fc' pfs =>
    (case check_change_obj_arr lno b fml
      (get_id pc) (get_obj pc) fc' pfs zeros of
      (fml',(fc',(id',zeros'))) =>
        (fml', (zeros', (inds, (vimap, (mk_vomap_arr (String.size vomap) fc', change_obj_update pc id' fc'))))))
  | Checkobj fc' =>
    if check_eq_obj (get_obj pc) fc'
    then (fml, (zeros, (inds, (vimap, (vomap, pc)))))
    else
      raise Fail (format_failure lno
        (err_obj_check_string (get_obj pc) fc'))
  | Changepres b v c pfs =>
    (case check_change_pres_arr lno b fml
      (get_id pc) (get_pres pc) v c pfs zeros of
      (fml',(pres',(id',zeros'))) =>
        (fml', (zeros', (inds, (vimap, (vomap, change_pres_update pc id' pres'))))))
  `
  |> append_prog;

val NPBC_CHECK_CSTEP_TYPE_def = theorem "NPBC_CHECK_CSTEP_TYPE_def";

Theorem EqualityType_OPTION_TYPE:
  EqualityType a ⇒
  EqualityType (OPTION_TYPE a)
Proof
  EVAL_TAC>>
  rw[]>>
  Cases_on`x1`>>fs[OPTION_TYPE_def]>>
  TRY(Cases_on`x2`>>fs[OPTION_TYPE_def])>>
  EVAL_TAC>>
  metis_tac[]
QED

(* TODO: Extremely slow *)
Theorem check_cstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_CSTEP_TYPE cstep cstepv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cstep_arr" (get_ml_prog_state()))
    [lnov; cstepv; fmlv; zerosv; indsv; vimapv; vomapv; pcv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_cstep_list cstep fmlls zeros inds vimap vomap pc of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (λl v.
                    LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                    v = vimapv')
                  (PAIR_TYPE (vomap_TYPE)
                  NPBC_CHECK_PROOF_CONF_TYPE))))
                res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_cstep_list cstep fmlls zeros inds vimap vomap pc = NONE)))
Proof
  rw[]>>
  xcf "check_cstep_arr" (get_ml_prog_state ())>>
  rw[check_cstep_list_def]>>
  Cases_on`cstep`>>fs[NPBC_CHECK_CSTEP_TYPE_def]
  >- ( (* Dom*)
    xmatch>>
    xlet_autop>>
    Cases_on`pc.ord`>>fs[OPTION_TYPE_def,get_ord_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xlet_auto >- (xsimpl>> simp (eq_lemmas()))>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      gvs[get_pres_def]>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    fs[get_pres_def]>>
    `check_fresh_aspo_list p' l (SOME x) vimap vomap` by cheat>>
    simp[]>>
    rpt xlet_autop>>
    xlet_auto >-
      (xsimpl>> simp (eq_lemmas()))>>
    rpt xlet_autop>>
    fs[get_id_def,get_obj_def]>>
    xlet_auto
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      simp[check_dom_list_def]>>
      rw[]>>
      pairarg_tac>>gvs[AllCaseEqs()]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    gvs[AllCasePreds()]>>
    qmatch_asmsub_rename_tac`PAIR_TYPE _ _ xxx _`>>
    PairCases_on`xxx`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    pairarg_tac>>gvs[check_dom_list_def,AllCaseEqs()]>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
    qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
    qexists_tac`A`>>xsimpl>>
    fs[set_id_def,get_tcb_def]>>
    unabbrev_all_tac>>
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    EVAL_TAC )
  >- ( (* Sstep *)
    xmatch>>
    rpt xlet_autop>>
    fs[get_tcb_def,get_id_def,get_obj_def,get_ord_def,get_pres_def]>>
    xlet_auto
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>fs[set_id_def])
  >- ( (* CheckedDelete*)
    xmatch>>
    xlet_autop>>
    reverse xif
    >- (
      fs[check_tcb_idopt_pc_def]>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`(POSTve
      (λv.
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv *
        &(case lookup_core_only_list T fmlls n of NONE => F
          | SOME x => constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv *
        & (Fail_exn e ∧
          lookup_core_only_list T fmlls n = NONE)))`
    >- (
      xapp>>
      xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      qexists_tac`T`>>xsimpl)
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    fs[check_tcb_idopt_pc_def]>>
    Cases_on`lookup_core_only_list T fmlls n`>>
    gvs[]>>
    rpt xlet_autop>>
    fs[get_id_def,get_tcb_def,get_obj_def,get_ord_def,get_pres_def]>>
    rename1`check_red_list pres ord obj T pc.tcb (delete_list n fmlls) inds
      pc.id c s pfs idopt vimap vomap zeros`>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
        case check_red_list pres ord obj T pc.tcb (delete_list n fmlls) inds
          pc.id c s pfs idopt vimap vomap zeros of NONE => F
        | SOME res =>
          PAIR_TYPE (λl v.
            LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
            v = fmlv') (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE
                (λl v.
                  LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                  v = vimapv')
              (PAIR_TYPE NUM (λl v. l = zeros' ∧ v = zerosv'  ∧ EVERY (λw. w = 0w) zeros') ))) res v
        ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_red_list pres ord obj T pc.tcb (delete_list n fmlls) inds
            pc.id c s pfs idopt vimap vomap zeros = NONE))`
    >- (
      xapp>>xsimpl>>
      CONJ_TAC >- EVAL_TAC>>
      metis_tac[])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    strip_tac>>xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>fs[set_id_def])
  >- ( (* Uncheckeddelete *)
    xmatch>>
    simp[GSYM check_tcb_ord_def]>>
    rpt xlet_autop>>
    xif
    >- (
      rpt xlet_autop>>
      xlet`POSTv v.
        ARRAY fmlv fmllsv' *
        W8ARRAY zerosv zeros *
        ARRAY vimapv vimaplsv *
        &NPBC_CHECK_PROOF_CONF_TYPE (set_chk pc F) v`
      >- (
        xapp>>xsimpl>>
        rw[]>>
        qexists_tac`F`>>
        qexists_tac`pc`>>simp[]>>
        EVAL_TAC)>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def,set_chk_def,AllCaseEqs(),check_tcb_ord_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    xlet`POSTv v. ARRAY fmlv fmllsv *
      W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv *
      &(LIST_TYPE NUM [] v)`
    >- (
      xcon>>xsimpl>>
      EVAL_TAC)>>
    xlet_autop>>
    Cases_on`all_core_list fmlls inds []`>>
    fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      fs[check_tcb_ord_def]>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v.
        ARRAY fmlv fmllsv' *
        W8ARRAY zerosv zeros *
        ARRAY vimapv vimaplsv *
        &NPBC_CHECK_PROOF_CONF_TYPE (set_chk pc F) v`
    >- (
      xapp>>xsimpl>>
      rw[]>>
      qexists_tac`F`>>
      qexists_tac`pc`>>simp[]>>
      EVAL_TAC)>>
    rpt xlet_autop>>
    xcon>>xsimpl >>
    fs[PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    fs[set_chk_def]>>
    xsimpl)
  >- ( (* Transfer *)
    xmatch>>
    xlet_auto
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>every_case_tac>>fs[]>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- ( (* StrengthenToCore *)
    xmatch>>
    rpt xlet_autop>>
    xif
    >- (
      xlet_auto
      >- (
        xsimpl>>
        metis_tac[ARRAY_refl])
      >- (
        xsimpl>>
        metis_tac[ARRAY_W8ARRAY_refl])>>
      pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def,set_tcb_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,set_tcb_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- ( (* LoadOrder*)
    xmatch>>
    rpt xlet_autop>>
    fs[get_orders_def]>>
    Cases_on`ALOOKUP pc.orders m`>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xlet_auto
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv' fmllsv' * W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv *
      &NPBC_CHECK_PROOF_CONF_TYPE (set_ord pc (SOME (x,l))) v`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      qexists_tac`SOME (x,l)`>>
      simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    every_case_tac>>
    gvs[AllCaseEqs(),PAIR_TYPE_def,OPTION_TYPE_def,set_ord_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- ( (* UnloadOrder *)
    xmatch>>
    xlet_autop>>fs[get_ord_def]>>
    Cases_on`pc.ord`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv *
      &NPBC_CHECK_PROOF_CONF_TYPE (set_ord pc NONE) v`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      qexists_tac`NONE`>>simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,OPTION_TYPE_def,set_ord_def]>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- ( (* StoreOrder *)
    xmatch>>
    xlet_autop>>
    rename1`check_storeorder a b c d e`>>
    Cases_on`check_storeorder a b c d e`>>
    gvs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      gvs[check_storeorder_def,Fail_exn_def,AllCaseEqs()]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    gvs[check_storeorder_def,AllCaseEqs()]>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv *
      &NPBC_CHECK_PROOF_CONF_TYPE (set_orders pc ((m,mk_aord a c b)::pc.orders)) v`
    >- (
      xapp>>xsimpl>>simp[set_orders_def]>>
      asm_exists_tac>>
      qexists_tac`(m,mk_aord a c b)::pc.orders`>>xsimpl>>
      fs[LIST_TYPE_def,PAIR_TYPE_def,get_orders_def])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,OPTION_TYPE_def,LIST_TYPE_def,set_orders_def]>>
    asm_exists_tac>>simp[]>>
    xsimpl>>
    metis_tac[ARRAY_W8ARRAY_refl])
  >- ( (* Obj *)
    xmatch>>
    rpt xlet_autop>>
    rename1`check_obj _ ll _ oo`>>
    fs[get_obj_def]>>
    Cases_on`check_obj pc.obj ll (MAP SND (core_fmlls fmlls inds)) oo`>>
    fs[map_snd_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    pairarg_tac>>
    fs[get_chk_def,get_bound_def,get_dbound_def,PAIR_TYPE_def]>>
    xmatch>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def,get_id_def,obj_update_def]>>
      `pc with <|id := pc.id; bound := bound'; dbound := dbound'|>
        = pc with <|bound := bound'; dbound := dbound'|>` by
       fs[npbc_checkTheory.proof_conf_component_equality]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- ( (* model improving *)
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
      qexists_tac`A`>>xsimpl>>
      fs[get_id_def,obj_update_def]>>
      unabbrev_all_tac>>
      match_mp_tac LIST_REL_update_resize>>
      fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
      EVAL_TAC))
  >- ( (* ChangeObj *)
    xmatch>>
    rpt xlet_autop>>
    xlet_auto
    >- (
      xsimpl>>
      fs[get_obj_def,get_id_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      fs[get_obj_def,get_id_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>> every_case_tac>>
    fs[get_id_def,get_obj_def]>>
    rw[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    fs[change_obj_update_def])
  >- ( (* CheckObj *)
    xmatch>>
    rpt xlet_autop>>
    fs[get_obj_def]>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])
  >- ( (* ChangePres *)
    xmatch>>
    rpt xlet_autop>>
    xlet_auto
    >- (
      xsimpl>>
      fs[get_obj_def,get_id_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      fs[get_pres_def,get_id_def]>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    pop_assum mp_tac>> every_case_tac>>
    fs[get_id_def,get_pres_def]>>
    rw[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    fs[change_pres_update_def])
QED

val res = translate npbc_checkTheory.check_triv2_def;

val check_implies_fml_arr = process_topdecs`
  fun check_implies_fml_arr fml n c =
  case Array.lookup fml None n of
    None => False
  | Some (ci,b) => check_triv2 ci c
` |> append_prog

Theorem check_implies_fml_arr_spec:
  NUM n nv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  constraint_TYPE c cv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_implies_fml_arr" (get_ml_prog_state()))
    [fmlv; nv; cv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
        ARRAY fmlv fmllsv *
        &(
        BOOL (check_implies_fml_list fmlls n c) v))
Proof
  rw[npbc_listTheory.check_implies_fml_list_def]>>
  xcf"check_implies_fml_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE bconstraint_TYPE (any_el n fmlls NONE) v'` by (
     rw[any_el_ALT]>>
     fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  every_case_tac>>fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl)>>
  xapp>>xsimpl>>
  metis_tac[]
QED

Definition check_sat_def:
  check_sat fml obj bound' wopt =
  case wopt of
    NONE => bound' ≠ NONE
  | SOME wm =>
    check_obj obj wm fml NONE ≠ NONE
End

Definition check_ub_def:
  check_ub fml obj bound' ubi wopt =
    case wopt of
      NONE => opt_le bound' ubi
    | SOME wm =>
      opt_le (check_obj obj wm fml NONE) ubi
End

val res = translate check_sat_def;
val res = translate npbc_checkTheory.opt_le_def;
val res = translate check_ub_def;

val _ = register_type ``:hconcl``

val res = translate npbc_checkTheory.lower_bound_def;

Definition hdsat_res_def:
  hdsat_res b =
  if b then NONE
  else SOME (strlit "conclusion SATISFIABLE check failed: [assignment check] T")
End

val res = translate hdsat_res_def;

Definition bool_to_string_def:
  bool_to_string b =
  if b then strlit"T" else strlit"F"
End

Definition hdunsat_res_def:
  hdunsat_res b1 b2 =
  if b1 ∧ b2 then NONE
  else SOME (
      strlit "conclusion UNSATISFIABLE check failed:" ^
      strlit " [dbound check] " ^ bool_to_string b1 ^
      strlit " [contradiction check] " ^ bool_to_string b2
  )
End

val res = translate bool_to_string_def;
val res = translate hdunsat_res_def;

Definition hobounds_res_def:
  hobounds_res b1 b2 b3 =
  if b1 ∧ b2 ∧ b3 then NONE
  else SOME (
      strlit "conclusion BOUNDS check failed:" ^
      strlit " [lb <= dbound] " ^ bool_to_string b1 ^
      strlit " [upper bound check] " ^ bool_to_string b2 ^
      strlit " [lower bound check] " ^ bool_to_string b3
  )
End

val res = translate hobounds_res_def;

val check_hconcl_arr = process_topdecs`
  fun check_hconcl_arr fml obj fml' obj' bound' dbound' hconcl =
  case hconcl of
    Hnoconcl => None
  | Hdsat wopt => hdsat_res (check_sat fml obj bound' wopt)
  | Hdunsat n =>
    hdunsat_res
      (dbound' = None)
      (check_contradiction_fml_arr False fml' n)
  | Hobounds lbi ubi n wopt =>
    let
    val b1 = opt_le lbi dbound'
    val b2 = check_ub fml obj bound' ubi wopt in
    case lbi of None =>
      hobounds_res b1 b2
        (check_contradiction_fml_arr False fml' n)
    | Some lb =>
      hobounds_res b1 b2
        (check_implies_fml_arr fml' n (lower_bound obj' lb))
    end
    ` |> append_prog

val NPBC_CHECK_HCONCL_TYPE_def = theorem"NPBC_CHECK_HCONCL_TYPE_def";

Theorem check_hconcl_arr_spec:
  LIST_TYPE constraint_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  obj_TYPE obj1 obj1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  NPBC_CHECK_HCONCL_TYPE hconcl hconclv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_hconcl_arr" (get_ml_prog_state()))
    [fmlv; objv; fml1v; obj1v; bound1v; dbound1v; hconclv]
    (ARRAY fml1v fmllsv)
    (POSTv v.
        ARRAY fml1v fmllsv *
        &(
        ∃s.
        OPTION_TYPE STRING_TYPE
        (if check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 hconcl then NONE else SOME s) v))
Proof
  rw[]>>
  xcf"check_hconcl_arr"(get_ml_prog_state ())>>
  Cases_on`hconcl`>>
  fs[npbc_listTheory.check_hconcl_list_def,NPBC_CHECK_HCONCL_TYPE_def]>>
  xmatch
  >- (* Hnoconcl *)
    (xcon>>xsimpl>>simp[OPTION_TYPE_def])
  >- (
    (* Hdsat *)
    xlet_auto
    >-
      (xsimpl>>simp[EqualityType_NUM_BOOL])>>
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    simp[hdsat_res_def]>>rw[]>>fs[OPTION_TYPE_def,check_sat_def]>>
    metis_tac[])
  >- (
    (* Hdunsat *)
    xlet_autop>>
    xlet`POSTv v. ARRAY fml1v fmllsv *
         &(
         BOOL (check_contradiction_fml_list F fmlls n) v)`
    >-
      (xapp>>xsimpl)>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fml1v fmllsv * &(BOOL(dbound1=NONE) v)`
    >- (
      xapp_spec (mlbasicsProgTheory.eq_v_thm |>
        INST_TYPE [alpha |-> ``:int option``])>>
      rpt(first_x_assum (irule_at Any))>>
      qexists_tac`NONE`>>xsimpl>>
      simp[OPTION_TYPE_def]>>
      metis_tac[EqualityType_OPTION_TYPE,EqualityType_NUM_BOOL])>>
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[hdunsat_res_def]>>rw[]>>
    metis_tac[])>>
  rpt xlet_autop>>
  rename1`opt_le lb dbound1`>>
  Cases_on`lb`>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fml1v fmllsv *
         &(
         BOOL (check_contradiction_fml_list F fmlls n) v)`
    >-
      (xapp>>xsimpl)>>
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[hobounds_res_def,check_ub_def]>>rw[]>>every_case_tac>>
    fs[OPTION_TYPE_def]>>
    metis_tac[]) >>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  rpt(first_x_assum (irule_at Any))>>
  simp[hobounds_res_def,check_ub_def]>>rw[]>>every_case_tac>>
  fs[OPTION_TYPE_def]>>
  metis_tac[]
QED

val fml_include_arr = process_topdecs`
  fun fml_include_arr fml fml' =
  let
    val hs = Array.array splim []
    val u = mk_hashset_arr fml hs in
    every_hs hs fml'
  end` |> append_prog;

Theorem fml_include_arr_spec:
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  (LIST_TYPE constraint_TYPE) rs rsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fml_include_arr" (get_ml_prog_state()))
    [lsv; rsv]
    (emp)
    (POSTv v.
      & ∃err.
        OPTION_TYPE STRING_TYPE
          (if fml_include_list ls rs
          then NONE else SOME err) v)
Proof
  rw[fml_include_list_def]>>
  xcf"fml_include_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  assume_tac (fetch "-" "splim_v_thm")>>
  xlet_auto>>
  qmatch_goalsub_abbrev_tac`ARRAY av hsv`>>
  `LIST_REL (LIST_TYPE constraint_TYPE) (REPLICATE splim []) hsv` by
    simp[Abbr`hsv`,LIST_REL_REPLICATE_same,LIST_TYPE_def]>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  fs[LIST_REL_EL_EQN]
QED

val _ = register_type ``:output``

Definition print_opt_string_def:
  (print_opt_string NONE = strlit"T") ∧
  (print_opt_string (SOME s) = s)
End

val res = translate print_opt_string_def;

Definition derivable_res_def:
  derivable_res (dbound :int option) b2opt =
  let b1 = (dbound = NONE) in
  let b2 = (b2opt = NONE) in
  if b1 ∧ b2 then NONE
  else SOME (
      strlit "output DERIVABLE check failed:" ^
      strlit " [dbound = NONE] " ^ bool_to_string b1 ^
      strlit " [core in output] " ^ print_opt_string b2opt)
End

val res = translate derivable_res_def;

Definition equisatisfiable_res_def:
  equisatisfiable_res
    (bound:int option) (dbound:int option) chk b2opt b3opt =
  let b11 = (bound = NONE) in
  let b12 = (dbound = NONE) in
  let b2 = (b2opt = NONE) in
  let b3 = (b3opt = NONE) in
  if b11 ∧ b12 ∧ chk ∧ b2 ∧ b3
  then NONE
    else SOME (
      strlit "output EQUISATISFIABLE check failed:" ^
      strlit " [bound = NONE] " ^ bool_to_string b11 ^
      strlit " [dbound = NONE] " ^ bool_to_string b12 ^
      strlit " [checked deletion] " ^ bool_to_string chk ^
      strlit " [core in output] " ^ print_opt_string b2opt ^
      strlit " [output in core] " ^ print_opt_string b3opt
  )
End

val res = translate equisatisfiable_res_def;

val res = translate npbc_checkTheory.opt_eq_obj_def;

Definition opt_err_obj_check_string_def:
  (opt_err_obj_check_string (SOME fc) (SOME fc') =
    err_obj_check_string (SOME fc) fc') ∧
  (opt_err_obj_check_string _ _ = strlit "missing objective")
End

val res = translate opt_err_obj_check_string_def;

Definition equioptimal_res_def:
  equioptimal_res
    (bound:int option) (dbound:int option) chk
    obj obj' b2opt b3opt =
  let b11 = opt_le bound dbound in
  let b12 = opt_eq_obj obj obj' in
  let b12s =
    if b12 then strlit"T" else opt_err_obj_check_string obj obj' in
  let b2 = (b2opt = NONE) in
  let b3 = (b3opt = NONE) in
  if b11 ∧ b12 ∧ chk ∧ b2 ∧ b3
  then NONE
    else SOME (
      strlit "output EQUIOPTIMAL check failed:" ^
      strlit " [bound <= dbound]: " ^ bool_to_string b11 ^
      strlit " [obj = output obj]: " ^ b12s ^
      strlit " [checked deletion]: " ^ bool_to_string chk ^
      strlit " [core in output] " ^ print_opt_string b2opt ^
      strlit " [output in core] " ^ print_opt_string b3opt
  )
End

val res = translate equioptimal_res_def;

Definition pres_string_def:
  (pres_string (xs:num_set) =
    concatWith (strlit" ") (MAP (toString o FST) (toAList xs)))
End

(* Add a checking command? *)
Definition err_pres_string_def:
  err_pres_string pres pres' =
  case pres of NONE => strlit"projection set check failed, no projection set available"
  | SOME pres =>
    concat[
    strlit"projection set check failed, expect: ";
    pres_string pres';
    strlit" got: ";
    pres_string pres]
End

Definition opt_err_pres_string_def:
  (opt_err_pres_string (SOME pres) (SOME pres') =
    err_pres_string (SOME pres) pres') ∧
  (opt_err_pres_string _ _ = strlit "missing projection set")
End

val res = translate pres_string_def;
val res = translate err_pres_string_def;
val res = translate opt_err_pres_string_def;

val res = translate npbc_checkTheory.opt_eq_obj_opt_def;
val res = translate npbc_checkTheory.opt_eq_pres_def;

Definition equisolvable_res_def:
  equisolvable_res
    (bound:int option) (dbound:int option) chk
    obj obj' (pres:num_set option) pres' b2opt b3opt =
  let b11 = opt_le bound dbound in
  let b12 = opt_eq_obj_opt obj obj' in
  let b12s =
    if b12 then strlit"T" else opt_err_obj_check_string obj obj' in
  let b2 = (b2opt = NONE) in
  let b3 = (b3opt = NONE) in
  let b4 = opt_eq_pres pres pres' in
  let b4s =
    if b4 then strlit"T" else opt_err_pres_string pres pres' in
  if b11 ∧ b12 ∧ chk ∧ b2 ∧ b3 ∧ b4
  then NONE
    else SOME (
      strlit "output EQUISOLVABLE check failed:" ^
      strlit " [bound <= dbound]: " ^ bool_to_string b11 ^
      strlit " [obj = output obj (if present)]: " ^ b12s ^
      strlit " [pres = output pres]: " ^ b4s ^
      strlit " [checked deletion]: " ^ bool_to_string chk ^
      strlit " [core in output] " ^ print_opt_string b2opt ^
      strlit " [output in core] " ^ print_opt_string b3opt
  )
End

val res = translate equisolvable_res_def;

val check_output_arr = process_topdecs`
  fun check_output_arr fml inds
    pres obj bound dbound chk fml' pres' obj' output =
  case output of
    Nooutput => None
  | Derivable =>
    let val cls = map_snd (core_fmlls_arr fml inds) in
      derivable_res dbound (fml_include_arr cls fml')
    end
  | Equisatisfiable =>
    let val cls = map_snd (core_fmlls_arr fml inds) in
    equisatisfiable_res
      bound dbound chk
      (fml_include_arr cls fml')
      (fml_include_arr fml' cls)
    end
  | Equioptimal =>
    let val cls = map_snd (core_fmlls_arr fml inds) in
    equioptimal_res
      bound dbound chk obj obj'
      (fml_include_arr cls fml')
      (fml_include_arr fml' cls)
    end
  | Equisolvable =>
    let val cls = map_snd (core_fmlls_arr fml inds) in
    equisolvable_res
      bound dbound chk obj obj' pres pres'
      (fml_include_arr cls fml')
      (fml_include_arr fml' cls)
    end
  ` |> append_prog;

val PBC_OUTPUT_TYPE_def = theorem"PBC_OUTPUT_TYPE_def";

Theorem check_output_arr_spec:
  (LIST_TYPE NUM) inds indsv ∧
  obj_TYPE obj objv ∧
  pres_TYPE pres presv ∧
  OPTION_TYPE INT bound boundv ∧
  OPTION_TYPE INT dbound dboundv ∧
  BOOL chk chkv ∧
  PBC_OUTPUT_TYPE output outputv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_output_arr" (get_ml_prog_state()))
    [fmlv; indsv; presv; objv; boundv; dboundv; chkv;
      fmltv; prestv; objtv; outputv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
        ARRAY fmlv fmllsv *
        &(
        ∃s.
        OPTION_TYPE STRING_TYPE
        (if check_output_list fmlls inds pres obj
          bound dbound chk fmlt prest objt output
         then NONE else SOME s) v))
Proof
  rw[]>>
  xcf"check_output_arr"(get_ml_prog_state ())>>
  Cases_on`output`>>
  fs[npbc_listTheory.check_output_list_def,PBC_OUTPUT_TYPE_def]>>
  xmatch
  >-
    (xcon>>xsimpl>>simp[OPTION_TYPE_def])
  >- (
    rpt xlet_autop>>
    xapp>>
    rpt(first_x_assum (irule_at Any))>>rw[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>xsimpl>>rw[]>>
    fs[derivable_res_def]>>every_case_tac>>
    fs[OPTION_TYPE_def,map_snd_def]>>
    metis_tac[])
  >- (
    rpt xlet_autop>>
    xapp>>
    rpt(first_x_assum (irule_at Any))>>rw[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>xsimpl>>rw[]>>
    fs[equisatisfiable_res_def]>>every_case_tac>>
    fs[OPTION_TYPE_def,map_snd_def]>>
    metis_tac[])
  >- (
    rpt xlet_autop>>
    xapp>>
    rpt(first_x_assum (irule_at Any))>>rw[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>xsimpl>>rw[]>>
    fs[equioptimal_res_def]>>every_case_tac>>
    fs[OPTION_TYPE_def,map_snd_def]>>
    metis_tac[])
  >- (
    rpt xlet_autop>>
    xapp>>
    rpt(first_x_assum (irule_at Any))>>rw[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>xsimpl>>rw[]>>
    fs[equisolvable_res_def]>>every_case_tac>>
    fs[OPTION_TYPE_def,map_snd_def]>>
    metis_tac[])
QED

val _ = export_theory();
