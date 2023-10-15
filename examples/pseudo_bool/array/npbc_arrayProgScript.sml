(*
  Refine npbc_list to npbc_array
*)
open preamble basis npbcTheory npbc_listTheory;

val _ = new_theory "npbc_arrayProg"

val _ = translation_extends"basisProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val _ = process_topdecs `
  exception Fail string;
` |> append_prog

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``"Fail"``

val Fail_exn_def = Define `
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)`

val _ = register_type ``:constr``
val _ = register_type ``:lstep ``
val _ = register_type ``:sstep ``

val format_failure_def = Define`
  format_failure (lno:num) s =
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

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
val r = translate combine_rle_def;
val r = translate spt_center_def;
val r = translate apsnd_cons_def;
val r = translate spt_centers_def;
val r = translate spt_right_def;
val r = translate spt_left_def;
val r = translate spts_to_alist_def;
val r = translate toSortedAList_def;

val res = translate lrnext_def;
val res = translate foldi_def;
val res = translate toAList_def;

val r = translate add_terms_def;
val r = translate add_lists'_def;
val r = translate add_lists'_thm;
val r = translate add_def;

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

val r = translate weaken_aux_def;
val r = translate weaken_def;

(* Throws an error *)
val check_cutting_arr = process_topdecs`
  fun check_cutting_arr lno b fml constr =
  case constr of
    Id n =>
    (case Array.lookup fml None n of
      None =>
        raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some (c,b') => (
      if b
      then
         (if b' then c
         else raise
              Fail (format_failure lno ("invalid core constraint id: " ^ Int.toString n)))
     else c))
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
  | Weak c var =>
    weaken (check_cutting_arr lno b fml c) var` |> append_prog

(* Overload notation for long _TYPE relations *)
Overload "constraint_TYPE" = ``PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) NUM``
Overload "bconstraint_TYPE" = ``PAIR_TYPE constraint_TYPE BOOL``

val NPBC_CHECK_CONSTR_TYPE_def = fetch "-" "NPBC_CHECK_CONSTR_TYPE_def";
val PBC_LIT_TYPE_def = fetch "-" "PBC_LIT_TYPE_def"

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
    xlet_autop>>
    xlet_auto>>
    `OPTION_TYPE bconstraint_TYPE (any_el n fmlls NONE) v'` by (
      rw[any_el_ALT]>>
      fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]
    >- (
      xmatch>>
      rpt (xlet_autop)>>
      xraise>> xsimpl>>
      simp[lookup_core_only_list_def]>>
      metis_tac[Fail_exn_def])>>
    Cases_on`x`>>fs[PAIR_TYPE_def]>>
    qpat_x_assum`Conv _ _ = any_el _ _ _` (assume_tac o SYM)>>
    xmatch>>
    reverse xif
    >-
      (xvar>>xsimpl>>simp[lookup_core_only_list_def])>>
    reverse xif
    >- (
      rpt (xlet_autop)>>
      xraise>> xsimpl>>
      simp[lookup_core_only_list_def]>>
      metis_tac[Fail_exn_def])>>
    xvar>>xsimpl>>simp[lookup_core_only_list_def])
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
  >> ( (* Weak *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp_spec
    (fetch "-" "weaken_v_thm" |> INST_TYPE [alpha|->``:num``])>>
    xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    first_x_assum (irule_at Any)>>
    metis_tac[EqualityType_NUM_BOOL])
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

(* TODO: can use Unsafe.update instead of Array.update *)
val delete_arr = process_topdecs`
  fun delete_arr i fml =
    if Array.length fml <= i then ()
    else
      (Array.update fml i None)` |> append_prog

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
  xcf"rollback_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>
  asm_exists_tac>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  rw[]>>fs[rollback_def]>>
  metis_tac[mk_ids_MAP_COUNT_LIST]
QED

val res = translate not_def;
val res = translate sorted_insert_def;

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
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
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

val check_lstep_arr = process_topdecs`
  fun check_lstep_arr lno step b fml mindel id =
  case step of
    Check n c =>
    (case Array.lookup fml None n of
      None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some (c',b) =>
      if c = c' then (fml, (None, id))
      else raise Fail (format_failure lno (err_check_string c c')))
  | Noop => (fml, (None, id))
  | Delete ls =>
      if every_less mindel fml ls then
        (list_delete_arr ls fml; (fml, (None, id)))
      else
        raise Fail (format_failure lno ("Deletion not permitted for core constraints and constraint index < " ^ Int.toString mindel))
  | Cutting constr =>
    let val c = check_cutting_arr lno b fml constr in
      (fml, (Some(c,b),id))
    end
  | Con c pf n =>
    (case opt_update_arr fml (Some (not_1 c,b)) id of
      (fml_not_c,id') =>
      (case check_lsteps_arr lno pf b fml_not_c id id' of
        (fml', id') =>
          if check_contradiction_fml_arr b fml' n then
            let val u = rollback_arr fml' id id' in
              (fml', (Some (c,b), id'))
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n))))
  | _ => raise Fail (format_failure lno ("Proof step not supported"))
  and check_lsteps_arr lno steps b fml mindel id =
  case steps of
    [] => (fml, id)
  | s::ss =>
    (case check_lstep_arr lno s b fml mindel id of
      (fml', (c , id')) =>
        (case opt_update_arr fml' c id' of (fml'',id'') =>
        check_lsteps_arr lno ss b fml'' mindel id''))
` |> append_prog

val NPBC_CHECK_LSTEP_TYPE_def = fetch "-" "NPBC_CHECK_LSTEP_TYPE_def";

Theorem check_lstep_arr_spec_aux:
  (∀step b fmlls mindel id stepv lno lnov idv fmlv fmllsv mindelv bv.
  NPBC_CHECK_LSTEP_TYPE step stepv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lstep_arr" (get_ml_prog_state()))
    [lnov; stepv; bv; fmlv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lstep_list step b fmlls mindel id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (OPTION_TYPE bconstraint_TYPE) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
        check_lstep_list step b fmlls mindel id = NONE)))) ∧
  (∀steps b fmlls mindel id stepsv lno lnov idv fmlv fmllsv mindelv bv.
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE steps stepsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; bv; fmlv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lsteps_list steps b fmlls mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              NUM res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_lsteps_list steps b fmlls mindel id = NONE))))
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
      xlet_auto>>
      reverse IF_CASES_TAC >>
      gs[]>>xif>>
      asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_lstep_list_def]>>
        xraise>>xsimpl>>
        simp[Fail_exn_def]>>
        metis_tac[ARRAY_refl])>>
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      simp[check_lstep_list_def])
    >- ((* Cutting *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_auto >- (
        xsimpl>>
        metis_tac[ARRAY_refl])>>
      rpt xlet_autop>>
      every_case_tac>>fs[]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
      metis_tac[ARRAY_refl])
    >- ( (* Con *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet`POSTv v. SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          PAIR_TYPE
            (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            NUM
            (opt_update fmlls (SOME (not p',b)) id) v)`
      >- (
        xapp>>xsimpl>>
        simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
      fs[PAIR_TYPE_def]>>
      xmatch>>
      xlet_autop
      >- (
        xsimpl>>
        metis_tac[ARRAY_refl])>>
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
      metis_tac[Fail_exn_def,ARRAY_refl])
    >- ( (* Check *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet_auto>>
      `OPTION_TYPE bconstraint_TYPE (any_el n fmlls NONE) v'` by (
         rw[any_el_ALT]>>
         fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
      qpat_x_assum`v' = _` (assume_tac o SYM)>>
      Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]
      >- (
        xmatch>>
        rpt xlet_autop>>
        xraise>> xsimpl>>
        metis_tac[Fail_exn_def,ARRAY_refl]) >>
      Cases_on`x`>>fs[PAIR_TYPE_def]>>xmatch>>
      xlet_autop>>
      xif>>rpt xlet_autop
      >- (
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      xraise>>
      xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])
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
    rpt xlet_autop
    >- (
      xsimpl>>
      rw[]>>simp[Once check_lstep_list_def]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    Cases_on`opt_update x0 x1 x2`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    rw[]>>simp[Once check_lstep_list_def]
    >- (
      every_case_tac>>fs[]>>asm_exists_tac>>
      xsimpl)>>
    metis_tac[ARRAY_refl])
QED

Theorem check_lstep_arr_spec = CONJUNCT1 check_lstep_arr_spec_aux
Theorem check_lsteps_arr_spec = CONJUNCT2 check_lstep_arr_spec_aux

Definition mk_vacc_def:
  mk_vacc b b' v vacc =
    if b ⇒ b' then v::vacc else vacc
End

val r = translate mk_vacc_def;

val reindex_aux_arr = process_topdecs `
  fun reindex_aux_arr b fml ls iacc vacc =
  case ls of
    [] => (List.rev iacc, vacc)
  | (i::is) =>
  case Array.lookup fml None i of
    None => reindex_aux_arr b fml is iacc vacc
  | Some (v,b') =>
      reindex_aux_arr b fml is (i::iacc)
        (mk_vacc b b' v vacc)` |> append_prog;

val reindex_arr = process_topdecs `
  fun reindex_arr b fml is =
    reindex_aux_arr b fml is [] []`
  |> append_prog;

Theorem reindex_aux_arr_spec:
  ∀inds indsv b bv fmlls fmlv iacc iaccv vacc vaccv.
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) iacc iaccv ∧
  (LIST_TYPE constraint_TYPE) vacc vaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_aux_arr" (get_ml_prog_state()))
    [bv; fmlv; indsv; iaccv; vaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex_aux b fmlls inds iacc vacc) v))
Proof
  Induct>>
  xcf"reindex_aux_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[reindex_aux_def,LIST_TYPE_def,PAIR_TYPE_def])>>
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
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xapp>>
  fs[LIST_TYPE_def,mk_vacc_def]
QED

Theorem reindex_arr_spec:
  ∀inds indsv fmlls fmlv.
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_arr" (get_ml_prog_state()))
    [bv; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM)
        (LIST_TYPE constraint_TYPE)
        (reindex b fmlls inds) v))
Proof
  xcf"reindex_arr"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[reindex_def]>>
  metis_tac[LIST_TYPE_def]
QED

val res = translate is_Pos_def;
val res = translate subst_aux_def;
val res = translate partition_def;
val res = translate clean_up_def;
val res = translate subst_lhs_def;
val res = translate subst_def;

val res = translate obj_constraint_def;
val res = translate npbc_checkTheory.subst_fun_def;
val res = translate subst_subst_fun_def;

val extract_clauses_arr = process_topdecs`
  fun extract_clauses_arr lno s b fml rsubs pfs acc =
  case pfs of [] => List.rev acc
  | cpf::pfs =>
    case cpf of
      (None,pf) =>
        extract_clauses_arr lno s b fml rsubs pfs ((None,pf)::acc)
    | (Some (Inl n,i),pf) =>
      (case lookup_core_only_arr b fml n of
        None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
      | Some c => extract_clauses_arr lno s b fml rsubs pfs ((Some ([not_1(subst_subst_fun s c)],i),pf)::acc))
    | (Some (Inr u,i),pf) =>
      if u < List.length rsubs then
        extract_clauses_arr lno s b fml rsubs pfs ((Some (List.nth rsubs u,i),pf)::acc)
      else raise Fail (format_failure lno ("invalid #proofgoal id: " ^ Int.toString u))
` |> append_prog;

Overload "subst_TYPE" = ``(VECTOR_TYPE (OPTION_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))))``

Overload "pfs_TYPE" = ``LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE))``

Theorem extract_clauses_arr_spec:
  ∀pfs pfsv s sv b bv fmlls fmlv fmllsv
    rsubs rsubsv acc accv lno lnov.
  NUM lno lnov ∧
  subst_TYPE s sv ∧
  BOOL b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  pfs_TYPE pfs pfsv ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) acc accv ∧
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
            LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          extract_clauses_list s b fmlls rsubs pfs acc = NONE)))
Proof
  Induct>>
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
    xlet_autop>>
    Cases_on`lookup_core_only_list b fmlls x`>>
    fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[extract_clauses_list_def]>>
      metis_tac[Fail_exn_def])>>
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

val res = translate subst_opt_aux_acc_def;
val res = translate imp_def;
val res = translate subst_opt_def;
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
  fun check_subproofs_arr lno pfs b fml mindel id =
  case pfs of
    [] => (fml,id)
  | (cnopt,pf)::pfs =>
    (case cnopt of
      None =>
      (case check_lsteps_arr lno pf b fml mindel id of
        (fml', id') =>
          check_subproofs_arr lno pfs b fml' mindel id')
    | Some (cs,n) =>
      case list_insert_fml_arr cs b id fml of
        (cid, cfml) =>
        (case check_lsteps_arr lno pf b cfml id cid of
          (fml', id') =>
          if check_contradiction_fml_arr b fml' n then
            let val u = rollback_arr fml' id id' in
              check_subproofs_arr lno pfs b fml' mindel id'
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n))))` |> append_prog

Theorem check_subproofs_arr_spec:
  ∀pfs fmlls mindel id pfsv lno lnov idv fmlv fmllsv mindelv b bv.
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) pfs pfsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_subproofs_arr" (get_ml_prog_state()))
    [lnov; pfsv; bv; fmlv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_subproofs_list pfs b fmlls mindel id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') NUM res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_subproofs_list pfs b fmlls mindel id = NONE)))
Proof
  Induct>>
  rw[]>>simp[check_subproofs_list_def]>>
  xcf "check_subproofs_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
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
    xlet_autop
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[])>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x`>>simp[PAIR_TYPE_def]>>
  strip_tac>>xmatch>>
  xlet_autop>>
  reverse xif>> xsimpl
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_refl])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

val res = translate npbc_checkTheory.extract_pids_def;

Definition do_rso_def:
  do_rso ord s c obj =
  red_subgoals ord (subst_fun s) c obj
End

val res = translate list_list_insert_def;
val res = translate npbcTheory.dom_subst_def;
val res = translate npbc_checkTheory.red_subgoals_def;
val res = translate do_rso_def;

val res = translate npbc_checkTheory.list_pair_eq_def;
val res = translate npbc_checkTheory.equal_constraint_def;
val res = translate npbc_checkTheory.mem_constraint_def;

val res = translate hash_pair_def;
val res = translate (hash_list_def |> REWRITE_RULE [splim_def]);
val res = translate (hash_constraint_def |> REWRITE_RULE [splim_def]);

(* TODO: can use Unsafe.update instead *)
val mk_hashset_arr = process_topdecs`
  fun mk_hashset_arr ps acc =
  case ps of [] => ()
  | p::ps =>
  let val h = hash_constraint p in
    Array.update acc h (p::(Array.sub acc h));
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

val in_hashset_arr = process_topdecs`
  fun in_hashset_arr p hs =
  let val h = hash_constraint p in
    mem_constraint p (Array.sub hs h)
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
  case ls of [] => True
  | l::ls =>
    in_hashset_arr l hs andalso
    every_hs hs ls` |> append_prog

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
      &BOOL (EVERY (λc. in_hashset c hs) ls) resv)
Proof
  Induct>>rw[]>>
  fs[LIST_TYPE_def]>>
  xcf "every_hs" (get_ml_prog_state ())>>
  xmatch
  >- (xcon>>xsimpl)>>
  xlet_auto>>
  xlog>>
  xsimpl>>rw[]
  >- (
    xapp>>xsimpl>>
    pairarg_tac>>fs[])>>
  gvs[]
QED

val hash_check = process_topdecs`
  fun hash_check fmlls proved lf =
  case lf of
    [] => True
  | _ =>
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
      &BOOL (
        let hs = mk_hashset x
          (mk_hashset y (REPLICATE splim [])) in
          EVERY (λc. in_hashset c hs) ls) resv)
Proof
  rw[]>>
  xcf "hash_check" (get_ml_prog_state ())>>
  Cases_on`ls`
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl)>>
  fs[LIST_TYPE_def]>>
  xmatch>>
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
  qexists_tac`h::t`>>simp[LIST_TYPE_def]>>
  unabbrev_all_tac>>fs[LIST_REL_EL_EQN]
QED

Definition red_cond_check_def:
  red_cond_check indfml extra
    (pfs:(( ((num + num) # num) option, (lstep list)) alist))
    (rsubs:((int # num) list # num) list list) goals =
  let (l,r) = extract_pids pfs LN LN in
  split_goals_hash indfml extra l goals ∧
  EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs))
End

Definition red_cond_check_pure_def:
  red_cond_check_pure extra
  (pfs:(( ((num + num) # num) option, (lstep list)) alist))
  (rsubs:((int # num) list # num) list list) (goals:(num # (int # num) list # num) list) =
  let (l,r) = extract_pids pfs LN LN in
  if
    EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs))
  then
    let (lp,lf) =
      PARTITION (λ(i,c). lookup i l ≠ NONE) goals in
    let lf = FILTER (λc. ¬(imp extra c)) (MAP SND lf) in
    let proved = MAP SND lp in
    SOME (proved,lf)
  else NONE
End

Theorem red_cond_check_eq:
  red_cond_check indfml extra pfs rsubs goals =
  case red_cond_check_pure extra pfs rsubs goals of
    NONE => F
  | SOME (x,ls) =>
    let hs = mk_hashset indfml (mk_hashset x (REPLICATE splim [])) in
    EVERY (λc. in_hashset c hs) ls
Proof
  rw[red_cond_check_def,red_cond_check_pure_def]>>
  pairarg_tac>>fs[split_goals_hash_def]>>
  IF_CASES_TAC>>fs[]>>
  rpt (pairarg_tac>>fs[])
QED

val res = translate COUNT_LIST_AUX_def;
val res = translate COUNT_LIST_compute;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;

val res = translate red_cond_check_pure_def;

val red_cond_check = process_topdecs`
  fun red_cond_check indfml extra pfs rsubs goals =
  case red_cond_check_pure extra pfs rsubs goals of
    None => False
  | Some (x,ls) =>
    hash_check indfml x ls` |> append_prog

Theorem red_cond_check_spec:
  LIST_TYPE constraint_TYPE a av ∧
  constraint_TYPE aa aav ∧
  LIST_TYPE
     (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM))
        (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) d dv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "red_cond_check" (get_ml_prog_state()))
    [av; aav; bv; cv; dv]
    emp
    (POSTv resv.
      &BOOL (red_cond_check a aa b c d) resv)
Proof
  rw[]>>
  xcf "red_cond_check" (get_ml_prog_state ())>>
  fs[]>>
  xlet_autop>>
  simp[red_cond_check_eq]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xapp>>
  xsimpl>>
  fs[]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]
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
  strlit"Expected: " ^
  print_expected_subproofs rsubs si
  (* ^
  strlit " Got: " ^
  print_subproofs pfs *)
End

(* val res = translate print_subgoal_def;
val res = translate print_subproofs_def; *)
val res = translate print_expected_subproofs_def;
val res = translate print_subproofs_err_def;

val format_failure_2_def = Define`
  format_failure_2 (lno:num) s s2 =
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit " Reason: " ^ s
  ^ strlit " Info: " ^ s2 ^ strlit"\n"`

val r = translate format_failure_2_def;

Theorem vec_eq_nil_thm:
  v = Vector [] ⇔ length v = 0
Proof
  EVAL_TAC>>Cases_on`v`>>fs[mlvectorTheory.length_def]
QED

val r = translate (red_fast_def |> SIMP_RULE std_ss [vec_eq_nil_thm]);

val check_red_arr_fast = process_topdecs`
  fun check_red_arr_fast lno b fml inds id c pf cid =
  let
    val nc = not_1 c
    val fml_not_c = Array.updateResize fml None id (Some (nc,b)) in
     case check_lsteps_arr lno pf b fml_not_c id (id+1) of
       (fml', id') =>
      if check_contradiction_fml_arr b fml' cid then
        let val u = rollback_arr fml' id id' in
          (fml', (inds, id'))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid))
    end` |> append_prog;

val check_red_arr = process_topdecs`
  fun check_red_arr lno ord obj b tcb fml inds id c s pfs idopt =
  case red_fast s idopt pfs of
  None =>
  (
  let val bortcb = b orelse tcb in
  case reindex_arr bortcb fml inds of (rinds,fmlls) =>
  let
    val nc = not_1 c
    val rsubs = do_rso ord s c obj
    val cpfs = extract_clauses_arr lno s b fml rsubs pfs []
    val fml_not_c = Array.updateResize fml None id (Some (nc,b)) in
     case check_subproofs_arr lno cpfs b fml_not_c id (id+1) of
       (fml', id') =>
     (case idopt of
       None =>
       let val u = rollback_arr fml' id id'
           val goals = subst_indexes_arr s bortcb fml' rinds in
           if red_cond_check fmlls nc pfs rsubs goals
           then
             (fml', (rinds,id'))
           else raise Fail (format_failure_2 lno ("Redundancy subproofs did not cover all subgoals.") (print_subproofs_err rsubs goals))
       end
    | Some cid =>
      if check_contradiction_fml_arr b fml' cid then
        let val u = rollback_arr fml' id id' in
          (fml', (rinds, id'))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
  end
  end)
  | Some (pf,cid) =>
    check_red_arr_fast lno b fml inds id c pf cid` |> append_prog;

(* Overloads all the _TYPEs that we will reuse *)
Overload "spo_TYPE" = ``PAIR_TYPE
      (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM))``

Overload "ord_TYPE" = ``
  OPTION_TYPE (PAIR_TYPE spo_TYPE (LIST_TYPE NUM))``

Overload "obj_TYPE" = ``
  OPTION_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)``

Theorem check_red_arr_fast_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE pfs pfsv ∧
  NUM cid cidv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr_fast" (get_ml_prog_state()))
    [lnov; bv; fmlv; indsv; idv;
      cv; pfsv; cidv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_red_list_fast b fmlls inds id
              c pfs cid of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list_fast b fmlls inds id
              c pfs cid = NONE)))
Proof
  rw[]>>
  xcf "check_red_arr_fast" (get_ml_prog_state ())>>
  rw[check_red_list_fast_def]>>
  rpt xlet_autop>>
  xlet_auto>>
  xlet_autop>>
  `LIST_REL (OPTION_TYPE bconstraint_TYPE)
   (update_resize fmlls NONE (SOME (not c,b)) id)
   (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
           (Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [v; bv]]) id)` by (
    match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def,PAIR_TYPE_def])>>
  xlet_autop
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
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
    metis_tac[ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[ARRAY_refl,Fail_exn_def]
QED

Theorem check_red_arr_spec:
  NUM lno lnov ∧
  ord_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  BOOL b bv ∧
  BOOL tcb tcbv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  subst_TYPE s sv ∧
  pfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr" (get_ml_prog_state()))
    [lnov; ordv; objv; bv; tcbv; fmlv; indsv; idv;
      cv; sv; pfsv; idoptv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_red_list ord obj b tcb fmlls inds id
              c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list ord obj b tcb fmlls inds id
              c s pfs idopt = NONE)))
Proof
  rw[]>>
  xcf "check_red_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  rw[check_red_list_def]>>
  reverse (Cases_on`red_fast s idopt pfs`)
  >- (
    simp[]>>Cases_on`x`>>fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    xmatch>>
    xapp>>
    metis_tac[])>>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (b ∨ tcb) v`
  >- (
    xlog>>xsimpl>>rw[]>>fs[]>>
    xvar>>xsimpl)>>
  pairarg_tac>>gs[]>>
  xlet_autop>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  qmatch_asmsub_abbrev_tac`VECTOR_TYPE _ s _`>>
  qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
  xlet`(POSTve
    (λv.
      ARRAY aa vv *
      &(case extract_clauses_list s b fmlls
          (do_rso ord s c obj) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
  (λe.
    ARRAY aa vv *
    & (Fail_exn e ∧
      extract_clauses_list s b fmlls (do_rso ord s c obj) pfs [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    fs[LIST_TYPE_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    fs[do_rso_def]>>
    metis_tac[ARRAY_refl])>>
  fs[]>>
  pop_assum mp_tac>>TOP_CASE_TAC>>gvs[]>>
  strip_tac>>
  fs[do_rso_def]>>
  rpt xlet_autop>>
  xlet_auto>>
  rpt xlet_autop>>
  rename1`_ (not n) vvv`>>
  `LIST_REL (OPTION_TYPE bconstraint_TYPE)
    (update_resize fmlls NONE (SOME (not n,b)) id)
    (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
            (Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [vvv; bv]]) id)` by (
    match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def,PAIR_TYPE_def])>>
  xlet_autop
  >- (
    xsimpl>>rw[]>>
    fs[do_rso_def]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  rename1`check_subproofs_list _ _ _ _ _ = SOME yyy`>>
  PairCases_on`yyy`>>simp[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  Cases_on`idopt`>>fs[OPTION_TYPE_def,do_red_check_def]>>xmatch
  >- (
    rpt xlet_autop>>
    fs[do_red_check_def]>>
    reverse xif
    >- (
      rpt xlet_autop>>
      fs[red_cond_check_def]>>
      xraise>>
      xsimpl>>
      rw[]>>fs[]>>
      metis_tac[ARRAY_refl,NOT_EVERY,Fail_exn_def]) >>
    fs[red_cond_check_def]>>
    pairarg_tac>>fs[]>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    rw[]>>fs[]>>
    metis_tac[ARRAY_refl,NOT_EVERY,Fail_exn_def]) >>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  xsimpl
QED

val check_sstep_arr = process_topdecs`
  fun check_sstep_arr lno step ord obj tcb fml inds id =
  case step of
    Lstep lstep =>
    (case check_lstep_arr lno lstep False fml 0 id of
      (rfml,(c,id')) =>
      (case c of
        None => (rfml,(inds,id'))
      | Some cc =>
        (Array.updateResize rfml None id' (Some cc),
          (sorted_insert id' inds,
          id'+1)) ))
  | Red c s pfs idopt =>
    (case check_red_arr lno ord obj False tcb
        fml inds id c s pfs idopt of
    (fml',(rinds,id')) =>
       (Array.updateResize fml' None id'
          (Some (c,tcb)),
        (sorted_insert id' rinds,(id'+1))))
  ` |> append_prog

val NPBC_CHECK_SSTEP_TYPE_def = theorem "NPBC_CHECK_SSTEP_TYPE_def";

Theorem check_sstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_SSTEP_TYPE step stepv ∧
  ord_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  BOOL tcb tcbv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_sstep_arr" (get_ml_prog_state()))
    [lnov; stepv; ordv; objv; tcbv; fmlv; indsv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_sstep_list step ord obj tcb
            fmlls inds id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_sstep_list step ord obj tcb
            fmlls inds id = NONE)))
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
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lstep_list l F fmlls 0 id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (OPTION_TYPE bconstraint_TYPE) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
        check_lstep_list l F fmlls 0 id = NONE))`
    >- (
      xapp>>xsimpl>>
      CONJ_TAC >- EVAL_TAC>>
      metis_tac[])
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    Cases_on`x1`>>
    fs[opt_update_inds_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      xlet_autop>>xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xlet_auto>>
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
    rename1`check_red_list ord obj F tcb fmlls inds id
              c s pfs idopt`>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_red_list ord obj F tcb fmlls inds id
              c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list ord obj F tcb fmlls inds id
              c s pfs idopt = NONE))`
    >- (
      xapp >> xsimpl>>
      CONJ_TAC >- EVAL_TAC>>
      metis_tac[])
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    every_case_tac>>fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xlet_auto>>
    xcon>>xsimpl>>
    match_mp_tac LIST_REL_update_resize>>
    simp[OPTION_TYPE_def,PAIR_TYPE_def]>>
    EVAL_TAC)
QED

val _ = register_type ``:cstep ``

val res = translate npbc_checkTheory.trans_subst_def;
val res = translate npbc_checkTheory.build_fml_def;
val res = translate EL;

val el_side_def = theorem "el_side_def";
val el_side = Q.prove(
  `∀n ls. el_side n ls ⇔ n < LENGTH ls`,
  Induct>>
  rw[Once el_side_def]>>
  Cases_on`ls`>>simp[]
) |> update_precondition

val res = translate npbc_checkTheory.lookup_core_only_def;
val res = translate npbc_checkTheory.extract_clauses_def;

val res = translate FOLDL;
val res = translate npbc_checkTheory.check_cutting_def;
val res = translate npbc_checkTheory.check_contradiction_fml_def;
val res = translate npbc_checkTheory.insert_fml_def;
val res = translate npbc_checkTheory.check_lstep_def;
val res = translate npbc_checkTheory.list_insert_fml_def;
val res = translate npbc_checkTheory.check_subproofs_def;
val res = translate
  (npbc_checkTheory.check_transitivity_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate (npbc_checkTheory.check_good_ord_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (npbc_checkTheory.check_ws_def |> REWRITE_RULE [MEMBER_INTRO]);

Definition check_storeorder_def:
  check_storeorder spo ws pfst pfsr ⇔
  if check_good_ord spo ∧ check_ws spo ws
  then
    case check_transitivity spo ws pfst of NONE => F
    | SOME id =>
      check_reflexivity spo pfsr id
  else F
End

val res = translate npbc_checkTheory.refl_subst_def;
val res = translate npbc_checkTheory.check_reflexivity_def;
val res = translate check_storeorder_def;

val res = translate npbcTheory.b2n_def;
val res = translate npbcTheory.eval_lit_def;
val res = translate npbcTheory.eval_term_def;
val res = translate npbcTheory.eval_obj_def;
val res = translate npbc_checkTheory.opt_lt_def;
val res = translate npbcTheory.satisfies_npbc_def;
val res = translate npbc_checkTheory.check_obj_def;

val res = translate npbc_checkTheory.nn_int_def;
val nn_int_side = Q.prove(
  `∀x. nn_int_side x`,
  EVAL_TAC>>
  intLib.ARITH_TAC
  ) |> update_precondition

val res = translate npbc_checkTheory.model_improving_def;

Definition do_dso_def:
  do_dso spo s c obj =
  dom_subgoals spo (subst_fun s) c obj
End

val res = translate npbc_checkTheory.neg_dom_subst_def;
val res = translate npbc_checkTheory.dom_subgoals_def;
val res = translate do_dso_def;

val res = translate npbc_checkTheory.model_bounding_def;

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
  check_dom_list spo obj fml inds id c s pfs idopt =
  let (rinds,fmlls) = reindex F fml inds in
  let corels = core_fmlls fml rinds in
  let nc = not c in
  let fml_not_c = update_resize fml NONE (SOME (nc,F)) id in
  let w = subst_fun s in
  let dsubs = dom_subgoals spo w c obj in
  case extract_clauses_list s F fml dsubs pfs [] of
    NONE => NONE
  | SOME cpfs =>
    (case check_subproofs_list cpfs F fml_not_c id (id+1) of
      NONE => NONE
    | SOME (fml',id') =>
      let rfml = rollback fml' id id' in
      if do_dom_check idopt fml' rfml w
        corels fmlls nc pfs dsubs then
        SOME (rfml,rinds,id')
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

(* TODO: we can defer corels until the split *)
val check_dom_arr = process_topdecs`
  fun check_dom_arr lno spo obj fml inds
    id c s pfs idopt =
  (case reindex_arr False fml inds of
    (rinds,fmlls) =>
    let
    val corels = core_fmlls_arr fml rinds
    val dsubs = do_dso spo s c obj
    val cpfs = extract_clauses_arr lno s False fml dsubs pfs []
    val nc = not_1 c
    val fml_not_c = Array.updateResize fml None id (Some (nc,False)) in
     case check_subproofs_arr lno cpfs False
      fml_not_c id (id+1) of
       (fml',id') =>
       (case idopt of
         None =>
         let val u = rollback_arr fml' id id'
             val goals = core_subgoals s corels in
             if red_cond_check fmlls nc pfs dsubs goals
             then
               (fml',(rinds,id'))
             else raise Fail (format_failure_2 lno ("Dominance subproofs did not cover all subgoals") (print_subproofs_err dsubs goals))
         end
       | Some cid =>
         if check_contradiction_fml_arr False fml' cid then
           let val u = rollback_arr fml' id id' in
             (fml', (rinds,id'))
           end
         else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
    end)` |> append_prog;

Theorem check_dom_arr_spec:
  NUM lno lnov ∧
  PAIR_TYPE spo_TYPE (LIST_TYPE NUM) spo spov ∧
  obj_TYPE obj objv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  subst_TYPE s sv ∧
  pfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_dom_arr" (get_ml_prog_state()))
    [lnov; spov; objv; fmlv; indsv; idv;
      cv; sv; pfsv; idoptv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_dom_list spo obj fmlls inds id
              c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_dom_list spo obj fmlls inds id
              c s pfs idopt = NONE)))
Proof
  rw[]>>
  xcf "check_dom_arr" (get_ml_prog_state ())>>
  rw[]>>
  xlet_autop>>
  xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM)
        (LIST_TYPE constraint_TYPE)
        (reindex F fmlls inds) v)`
  >- (
    xapp>>xsimpl>>
    EVAL_TAC)>>
  Cases_on`reindex F fmlls inds`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet`(POSTve
    (λv.
      ARRAY fmlv fmllsv *
      &(case extract_clauses_list s F fmlls
        (do_dso spo s c obj) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
    (λe.
      ARRAY fmlv fmllsv *
      & (Fail_exn e ∧ extract_clauses_list s F fmlls
        (do_dso spo s c obj) pfs [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    CONJ_TAC >- EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[do_dso_def,check_dom_list_def]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>TOP_CASE_TAC>>simp[]>>
  fs[do_dso_def]>>
  strip_tac>>
  rpt xlet_autop>>
  xlet_auto>>
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
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_subproofs_list x F
            (update_resize fmlls NONE (SOME (not n,F)) id)
            id (id+1) of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') NUM res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_subproofs_list x F
            (update_resize fmlls NONE (SOME (not n,F)) id)
            id (id+1) = NONE)))`
  >- (
    xapp>>
    xsimpl>>
    CONJ_TAC >- EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[check_dom_list_def]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x'`>>fs[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  Cases_on`idopt`>>
  fs[OPTION_TYPE_def,do_dom_check_def,check_dom_list_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    reverse xif>>gs[]
    >- (
      rpt xlet_autop>>
      fs[red_cond_check_def]>>pairarg_tac>>fs[core_subgoals_def]>>
      xraise>>xsimpl>>
      fs[red_cond_check_def]>>rw[]>>
      metis_tac[ARRAY_refl,Fail_exn_def,NOT_EVERY])>>
    xlet_autop>>
    xcon>>xsimpl>>
    pairarg_tac>>fs[red_cond_check_def,core_subgoals_def]>>
    fs[PAIR_TYPE_def,OPTION_TYPE_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  rename1`check_contradiction_fml_list F A B`>>
  xlet`POSTv v.
    ARRAY fmlv' fmllsv' * &
    BOOL (check_contradiction_fml_list F A B) v`
  >- (
    xapp>>xsimpl>>
    EVAL_TAC)>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    rw[]>>fs[]>>
    metis_tac[ARRAY_refl,NOT_EVERY,Fail_exn_def])>>
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
val res = translate do_change_obj_check_def;

val check_change_obj_arr = process_topdecs `
  fun check_change_obj_arr lno fml id obj fc' pfs =
  case obj of None =>
    raise Fail (format_failure lno ("no objective to change"))
  | Some fc =>
    let
    val csubs = change_obj_subgoals fc fc'
    val b = True
    val e = []
    val cpfs = extract_clauses_arr lno emp_vec b fml csubs pfs e in
    case check_subproofs_arr lno cpfs b fml id id of
       (fml', id') =>
      let val u = rollback_arr fml' id id' in
        if do_change_obj_check pfs then
          (fml',id')
       else raise Fail (format_failure lno ("Objective change subproofs did not cover all subgoals. Expected: #[1-2]"))
       end
    end` |> append_prog

Theorem check_change_obj_arr_spec:
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  NUM id idv ∧
  obj_TYPE obj objv ∧
  (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT) fc fcv ∧
  pfs_TYPE pfs pfsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_change_obj_arr" (get_ml_prog_state()))
    [lnov; fmlv; idv; objv; fcv; pfsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_change_obj_list fmlls id obj fc pfs of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              NUM
              res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_change_obj_list fmlls id obj fc pfs = NONE)))
Proof
  rw[]>>
  xcf "check_change_obj_arr" (get_ml_prog_state ())>>
  simp[check_change_obj_list_def]>>
  Cases_on`obj`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_refl,Fail_exn_def])>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
  xlet`(POSTve
    (λv.
      ARRAY aa vv *
      &(case extract_clauses_list emp_vec T fmlls
          (change_obj_subgoals x fc) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
  (λe.
    ARRAY aa vv *
    & (Fail_exn e ∧
      extract_clauses_list emp_vec T fmlls (change_obj_subgoals x fc) pfs [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- metis_tac[]>>
    metis_tac[fetch "-" "emp_vec_v_thm"])
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>gvs[]>>
  strip_tac>>
  rename1`check_subproofs_list xx`>>
  xlet`(POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_subproofs_list xx T fmlls id id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv') NUM res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_subproofs_list xx T fmlls id id = NONE)))`
  >- (
    xapp>>xsimpl>>
    CONJ_TAC>-EVAL_TAC>>
    metis_tac[])
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>fs[]>>
  Cases_on`x'`>>fs[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>> xsimpl>>
  metis_tac[ARRAY_refl,Fail_exn_def]
QED

val _ = register_type ``:proof_conf``

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

(* TODO: update below here *)
val check_cstep_arr = process_topdecs`
  fun check_cstep_arr lno cstep fml inds pc =
  case cstep of
    Dom c s pfs idopt => (
    case get_ord pc of None =>
      raise Fail (format_failure lno "no order loaded for dominance step")
    | Some spo =>
      case check_dom_arr lno spo (get_obj pc)
        fml inds (get_id pc) c s pfs idopt of (fml',(rinds,id')) =>
      (Array.updateResize fml' None id' (Some (c,get_tcb pc)),
       (sorted_insert id' rinds,
       (set_id pc (id'+1)))))
  | Sstep sstep => (
    case check_sstep_arr lno sstep (get_ord pc) (get_obj pc)
      (get_tcb pc) fml inds (get_id pc) of
      (fml',(inds',id')) =>
      (fml',(inds',set_id pc id')))
  | Checkeddelete n s pfs idopt => (
    if check_tcb_idopt_pc pc idopt
    then
      case lookup_core_only_arr True fml n of None =>
        raise Fail (format_failure lno "invalid core deletion ID")
      | Some c => (
          (delete_arr n fml;
          case
            check_red_arr lno (get_ord pc) (get_obj pc) True
              (get_tcb pc) fml inds (get_id pc)
              c s pfs idopt of (fml',(inds',id')) =>
              (fml',(inds',set_id pc id'))))
    else raise Fail
      (format_failure lno
        "invalid proof state for checked deletion"))
  | Uncheckeddelete ls => (
    if check_tcb_ord pc then
      (list_delete_arr ls fml;
        (fml, (inds, set_chk pc False)))
    else
      case all_core_arr fml inds [] of None =>
        raise Fail (format_failure lno
        "not all constraints in core")
      | Some inds' =>
        (list_delete_arr ls fml;
          (fml, (inds', set_chk pc False))))
  | Transfer ls => (
      let val fml' = core_from_inds_arr lno fml ls in
        (fml', (inds, pc))
      end)
  | Strengthentocore b => (
    let val inds' = fst (reindex_arr False fml inds) in
      if b
      then (
        let val fml' = core_from_inds_arr lno fml inds' in
          (fml', (inds', set_tcb pc b))
        end)
      else
        (fml,(inds',set_tcb pc b))
    end)
  | Loadorder nn xs =>
    let val inds' = fst (reindex_arr False fml inds) in
    case Alist.lookup (get_orders pc) nn of
      None =>
        raise Fail (format_failure lno ("no such order: " ^ nn))
    | Some ord' =>
      if List.length xs = List.length (fst (snd ord')) then
        let val fml' = core_from_inds_arr lno fml inds' in
        (fml', (inds',set_ord pc (Some (ord',xs))))
        end
      else
        raise Fail
          (format_failure lno ("invalid order instantiation"))
    end
  | Unloadorder =>
    (case get_ord pc of None =>
     raise Fail (format_failure lno ("no order loaded"))
    | Some spo =>
      (fml,(inds, set_ord pc None)))
  | Storeorder name spo ws pfsr pfst =>
    if check_storeorder spo ws pfst pfsr
    then
     (fml, (inds, set_orders pc ((name,spo)::get_orders pc)))
    else
      raise Fail (format_failure lno ("invalid order definition"))
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
           (sorted_insert id inds,
           (obj_update pc (id+1) bound' dbound')))
        end
      else
        (fml, (inds, (obj_update pc (get_id pc) bound' dbound')))
    end
    )
  | Changeobj fc' pfs =>
    (case check_change_obj_arr lno fml
      (get_id pc) (get_obj pc) fc' pfs of
      (fml',id') =>
        (fml', (inds, (change_obj_update pc id' fc'))))`
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

Theorem EqualityType_ord_TYPE:
  EqualityType ord_TYPE
Proof
  metis_tac[EqualityType_OPTION_TYPE,EqualityType_PAIR_TYPE,EqualityType_LIST_TYPE,EqualityType_NUM_BOOL]
QED

(* TODO: Extremely slow *)
Theorem check_cstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_CSTEP_TYPE cstep cstepv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cstep_arr" (get_ml_prog_state()))
    [lnov; cstepv; fmlv; indsv; pcv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_cstep_list cstep fmlls inds pc of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                NPBC_CHECK_PROOF_CONF_TYPE)
                res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_cstep_list cstep fmlls inds pc = NONE)))
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
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    pairarg_tac>>fs[]>>
    rpt xlet_autop>>
    fs[get_id_def,get_obj_def]
    >- (
      xsimpl>>
      simp[check_dom_list_def]>>
      rw[]>>
      qmatch_goalsub_abbrev_tac`ARRAY A B`>>
      qexists_tac`A`>>qexists_tac`B`>>xsimpl>>
      fs[do_dom_check_def,AllCaseEqs()])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
    PairCases_on`x'`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    gvs[check_dom_list_def,AllCaseEqs()]>>
    xlet_auto>>
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
    fs[get_tcb_def,get_id_def,get_obj_def,get_ord_def]
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
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
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(
        OPTION_TYPE constraint_TYPE
        (lookup_core_only_list T fmlls n) v)`
    >- (
      xapp>>
      xsimpl)>>
    fs[check_tcb_idopt_pc_def]>>
    Cases_on`lookup_core_only_list T fmlls n`>>
    fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    fs[get_id_def,get_tcb_def,get_obj_def,get_ord_def]>>
    rename1`check_red_list ord obj T pc.tcb (delete_list n fmlls)
      inds pc.id c s pfs idopt`>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
        case check_red_list ord obj T pc.tcb (delete_list n fmlls)
          inds pc.id c s pfs idopt of NONE => F
        | SOME res =>
          PAIR_TYPE (λl v.
            LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
            v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
        ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list ord obj T pc.tcb (delete_list n fmlls)
            inds pc.id c s pfs idopt = NONE))`
    >- (
      xapp>>xsimpl>>
      CONJ_TAC >- EVAL_TAC>>
      metis_tac[])
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
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
        ARRAY fmlv fmllsv' * &NPBC_CHECK_PROOF_CONF_TYPE (set_chk pc F) v`
      >- (
        xapp>>xsimpl>>
        rw[]>>
        qexists_tac`F`>>
        qexists_tac`pc`>>simp[]>>
        EVAL_TAC)>>
      xlet_autop>>
      xcon>>xsimpl>>
      fs[]>>
      fs[PAIR_TYPE_def,set_chk_def]>>
      metis_tac[ARRAY_refl])>>
    xlet`POSTv v. ARRAY fmlv fmllsv * &(LIST_TYPE NUM [] v)`
    >- (
      xcon>>xsimpl>>
      EVAL_TAC)>>
    xlet_autop>>
    Cases_on`all_core_list fmlls inds []`>>
    fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v.
        ARRAY fmlv fmllsv' * &NPBC_CHECK_PROOF_CONF_TYPE (set_chk pc F) v`
    >- (
      xapp>>xsimpl>>
      rw[]>>
      qexists_tac`F`>>
      qexists_tac`pc`>>simp[]>>
      EVAL_TAC)>>
    xlet_autop>>
    xcon>>xsimpl >>
    fs[PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    fs[set_chk_def]>>
    xsimpl)
  >- ( (* Transfer *)
    xmatch>>
    xlet_autop
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    xlet_autop>>
    xcon>>every_case_tac>>fs[]>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* StrengthenToCore *)
    xmatch>>
    rpt xlet_autop>>
    xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex F fmlls inds) v)`
    >- (
      xapp>>xsimpl>>
      EVAL_TAC)>>
    rpt xlet_autop>>
    xif
    >- (
      xlet_autop>>xsimpl
      >-
        (metis_tac[ARRAY_refl])>>
      pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def,set_tcb_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,set_tcb_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* LoadOrder*)
    xmatch>>
    rpt xlet_autop>>
    xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex F fmlls inds) v)`
    >- (
      xapp>>xsimpl>>
      EVAL_TAC)>>
    rpt xlet_autop>>
    fs[get_orders_def]>>
    Cases_on`ALOOKUP pc.orders m`>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    xlet`POSTv v. ARRAY fmlv' fmllsv' *
      &NPBC_CHECK_PROOF_CONF_TYPE (set_ord pc (SOME (x,l))) v`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      qexists_tac`SOME (x,l)`>>simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
    xlet_autop>>
    xcon>>xsimpl>>
    every_case_tac>>
    gvs[AllCaseEqs(),PAIR_TYPE_def,OPTION_TYPE_def,set_ord_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* UnloadOrder *)
    xmatch>>
    xlet_autop>>fs[get_ord_def]>>
    Cases_on`pc.ord`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv *
      &NPBC_CHECK_PROOF_CONF_TYPE (set_ord pc NONE) v`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      qexists_tac`NONE`>>simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
    xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,OPTION_TYPE_def,set_ord_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* StoreOrder *)
    xmatch>>
    xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      every_case_tac>>
      gvs[check_storeorder_def,Fail_exn_def,AllCaseEqs()]>>
      metis_tac[ARRAY_refl])>>
    gvs[check_storeorder_def]>>
    every_case_tac>>fs[]>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv *
      &NPBC_CHECK_PROOF_CONF_TYPE (set_orders pc ((m,p')::pc.orders)) v`
    >- (
      xapp>>xsimpl>>simp[set_orders_def]>>
      asm_exists_tac>>
      qexists_tac`(m,p')::pc.orders`>>xsimpl>>
      fs[LIST_TYPE_def,PAIR_TYPE_def,get_orders_def])>>
    xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,OPTION_TYPE_def,LIST_TYPE_def,set_orders_def]>>
    asm_exists_tac>>simp[]>>
    metis_tac[ARRAY_refl])
  >- ( (* Obj *)
    xmatch>>
    rpt xlet_autop>>
    rename1`check_obj _ _ _ oo`>>
    fs[get_obj_def]>>
    Cases_on`check_obj pc.obj s (MAP SND (core_fmlls fmlls inds)) oo`>>
    fs[map_snd_def,OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
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
      metis_tac[ARRAY_refl])
    >- ( (* model improving *)
      rpt xlet_autop>>
      xlet_auto>>
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
    rpt xlet_autop
    >- (
      xsimpl>>
      fs[get_obj_def,get_id_def]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>> every_case_tac>>
    fs[get_id_def,get_obj_def]>>
    rw[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    fs[change_obj_update_def])
QED

val check_implies_fml_arr = process_topdecs`
  fun check_implies_fml_arr fml n c =
  case Array.lookup fml None n of
    None => False
  | Some (ci,b) => imp ci c
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

val check_hconcl_arr = process_topdecs`
  fun check_hconcl_arr fml obj fml' obj' bound' dbound' hconcl =
  case hconcl of
    Hnoconcl => True
  | Hdsat wopt => check_sat fml obj bound' wopt
  | Hdunsat n =>
    (dbound' = None andalso
      check_contradiction_fml_arr False fml' n)
  | Hobounds lbi ubi n wopt =>
    if opt_le lbi dbound' then
      check_ub fml obj bound' ubi wopt andalso
    (case lbi of
      None => check_contradiction_fml_arr False fml' n
    | Some lb => check_implies_fml_arr fml' n (lower_bound obj' lb)
    )
    else False` |> append_prog

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
        BOOL (check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 hconcl) v))
Proof
  rw[]>>
  xcf"check_hconcl_arr"(get_ml_prog_state ())>>
  Cases_on`hconcl`>>
  fs[npbc_listTheory.check_hconcl_list_def,NPBC_CHECK_HCONCL_TYPE_def]>>
  xmatch
  >- (* Hnoconcl *)
    (xcon>>xsimpl)
  >- (
    xapp_spec (fetch "-" "check_sat_v_thm" |> INST_TYPE[alpha|->``:int``])>>
    rpt(first_x_assum (irule_at Any))>>
    xsimpl>>
    simp[check_sat_def,EqualityType_NUM_BOOL])
  >- (
    rpt (xlet_autop)>>
    xlet`POSTv v. ARRAY fml1v fmllsv * &(BOOL(dbound1=NONE) v)`
    >- (
      xapp_spec (mlbasicsProgTheory.eq_v_thm |>
        INST_TYPE [alpha |-> ``:int option``])>>
      rpt(first_x_assum (irule_at Any))>>
      qexists_tac`NONE`>>xsimpl>>
      simp[OPTION_TYPE_def]>>
      metis_tac[EqualityType_OPTION_TYPE,EqualityType_NUM_BOOL])>>
    xlog>>IF_CASES_TAC>>gvs[]>>xsimpl>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    EVAL_TAC)>>
  xlet_autop>>
  reverse xif
  >- (xcon>>xsimpl)>>
  xlet_autop>>
  xlog>>
  reverse IF_CASES_TAC>>
  gvs[GSYM check_ub_def]
  >- xsimpl>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xapp >> xsimpl >> EVAL_TAC)>>
  xlet_autop>>
  xapp>>xsimpl
QED

val _ = export_theory();
