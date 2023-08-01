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
val list_delete_arr = process_topdecs`
  fun list_delete_arr ls fml =
    case ls of
      [] => ()
    | (i::is) =>
      if Array.length fml <= i then list_delete_arr is fml
      else
        (Array.update fml i None; list_delete_arr is fml)` |> append_prog

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
  xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  simp[delete_list_def]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (xapp >> xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto >- xsimpl>>
  xapp>>xsimpl>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]
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
  ∀fmlls inds mindel indsv fmlv fmllsv mindelv.
  NUM mindel mindelv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_less" (get_ml_prog_state()))
    [mindelv; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(BOOL
         (EVERY (λid. mindel ≤ id ∧
          lookup_core_only_list T fmlls id = NONE) inds) v))
Proof
  Induct_on`inds`>>
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

val check_lstep_arr = process_topdecs`
  fun check_lstep_arr lno step b fml inds mindel id =
  case step of
    Check n c =>
    (case Array.lookup fml None n of
      None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some (c',b) =>
      if c = c' then (fml, (inds, id))
      else raise Fail (format_failure lno (err_check_string c c')))
  | Noop => (fml, (inds, id))
  | Delete ls =>
      if every_less mindel fml ls then
        (list_delete_arr ls fml; (fml, (inds, id)))
      else
        raise Fail (format_failure lno ("Deletion not permitted for core constraints and constraint index < " ^ Int.toString mindel))
  | Cutting constr =>
    let val c = check_cutting_arr lno b fml constr
        val fml' = Array.updateResize fml None id (Some (c,b)) in
      (fml', (sorted_insert id inds,id+1))
    end
  | Con c pf n =>
    let
      val fml_not_c =
        Array.updateResize fml None id (Some (not_1 c,b))
    in
      (case check_lsteps_arr lno pf b fml_not_c
        (sorted_insert id inds) id (id+1) of
        (fml', (inds', id')) =>
          if check_contradiction_fml_arr b fml' n then
            let val u = rollback_arr fml' id id' in
              (Array.updateResize fml' None id' (Some (c,b)),
                (sorted_insert id' inds,
                id'+1))
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n)))
    end
  | _ => raise Fail (format_failure lno ("Proof step not supported"))
  and check_lsteps_arr lno steps b fml inds mindel id =
  case steps of
    [] => (fml, (inds, id))
  | s::ss =>
    case check_lstep_arr lno s b fml inds mindel id of
      (fml', (inds', id')) =>
        check_lsteps_arr lno ss b fml' inds' mindel id'
` |> append_prog

val NPBC_CHECK_LSTEP_TYPE_def = fetch "-" "NPBC_CHECK_LSTEP_TYPE_def";

Theorem ARRAY_refl:
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Theorem check_lstep_arr_spec_aux:
  (∀step b fmlls inds mindel id stepv lno lnov idv indsv fmlv fmllsv mindelv bv.
  NPBC_CHECK_LSTEP_TYPE step stepv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lstep_arr" (get_ml_prog_state()))
    [lnov; stepv; bv; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lstep_list step b fmlls inds mindel id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
        check_lstep_list step b fmlls inds mindel id = NONE)))) ∧
  (∀steps b fmlls inds mindel id stepsv lno lnov idv indsv fmlv fmllsv mindelv bv.
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE steps stepsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; bv; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lsteps_list steps b fmlls inds mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧ check_lsteps_list steps b fmlls inds mindel id = NONE))))
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
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      simp[check_lstep_list_def])
    >- ((* Cutting *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_auto >- (
        xsimpl>>
        metis_tac[ARRAY_refl])>>
      rpt xlet_autop>>
      xlet_auto >>
      rpt xlet_autop>>
      every_case_tac>>fs[]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ lss`>>
      qexists_tac`lss`>>xsimpl>>
      simp[Abbr`lss`]>>
      match_mp_tac LIST_REL_update_resize>>
      simp[OPTION_TYPE_def,PAIR_TYPE_def])
    >- ( (* Con *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet_auto>>
      rpt xlet_autop>>
      (* for some reason xapp doesn't work?? *)
      first_x_assum drule>>
      qpat_x_assum`NUM lno lnov` assume_tac>>
      rpt(disch_then drule)>>
      `LIST_REL (OPTION_TYPE bconstraint_TYPE)
        (update_resize fmlls NONE (SOME (not p',b)) id)
        (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
                (Conv (SOME (TypeStamp "Some" 2)) [Conv NONE [v;bv]]) id)` by (
        match_mp_tac LIST_REL_update_resize>>
        fs[OPTION_TYPE_def,PAIR_TYPE_def])>>
      disch_then drule>>
      disch_then drule>>
      strip_tac>>
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
        xlet_auto>>
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        qmatch_goalsub_abbrev_tac`ARRAY _ ls`>>
        qexists_tac`ls`>>xsimpl>>
        simp[Abbr`ls`]>>
        match_mp_tac LIST_REL_update_resize>>
        simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
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
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      xraise>>
      xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])
    >- ( (*No Op*)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
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

(* **** TODO FIXME BELOW **** *)

Definition mk_vacc_def:
  mk_vacc b core i v vacc =
    if core_only b core i then v::vacc else vacc
End

val r = translate mk_vacc_def;

val reindex_aux_arr = process_topdecs `
  fun reindex_aux_arr b core fml ls iacc vacc =
  case ls of
    [] => (List.rev iacc, vacc)
  | (i::is) =>
  case Array.lookup fml None i of
    None => reindex_aux_arr b core fml is iacc vacc
  | Some v =>
      reindex_aux_arr b core fml is (i::iacc)
        (mk_vacc b core i v vacc)` |> append_prog;

val reindex_arr = process_topdecs `
  fun reindex_arr b core fml is =
    reindex_aux_arr b core fml is [] []`
  |> append_prog;

Theorem reindex_aux_spec:
  ∀inds indsv b bv core corev fmlls fmlv iacc iaccv vacc vaccv.
  BOOL b bv ∧
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) iacc iaccv ∧
  (LIST_TYPE constraint_TYPE) vacc vaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_aux_arr" (get_ml_prog_state()))
    [bv; corev; fmlv; indsv; iaccv; vaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex_aux b core fmlls inds iacc vacc) v))
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
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[reindex_aux_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >-
    (xapp>>simp[])>>
  rpt xlet_autop>>
  xapp>>
  fs[LIST_TYPE_def,mk_vacc_def]
QED

Theorem reindex_arr_spec:
  ∀inds indsv fmlls fmlv.
  BOOL b bv ∧
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_arr" (get_ml_prog_state()))
    [bv; corev; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex b core fmlls inds) v))
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
  fun extract_clauses_arr lno s b core fml rsubs pfs acc =
  case pfs of [] => List.rev acc
  | cpf::pfs =>
    case cpf of
      (None,pf) =>
        extract_clauses_arr lno s b core fml rsubs pfs ((None,pf)::acc)
    | (Some (Inl n,i),pf) =>
      if core_only b core n then
        (case Array.lookup fml None n of
          None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
        | Some c => extract_clauses_arr lno s b core fml rsubs pfs ((Some ([not_1(subst_subst_fun s c)],i),pf)::acc))
      else
        raise Fail (format_failure lno ("invalid core constraint id: " ^ Int.toString n))
    | (Some (Inr u,i),pf) =>
      if u < List.length rsubs then
        extract_clauses_arr lno s b core fml rsubs pfs ((Some (List.nth rsubs u,i),pf)::acc)
      else raise Fail (format_failure lno ("invalid #proofgoal id: " ^ Int.toString u))
` |> append_prog;

Overload "subst_TYPE" = ``(VECTOR_TYPE (OPTION_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))))``

Overload "pfs_TYPE" = ``LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE))``

Theorem extract_clauses_arr_spec:
  ∀pfs pfsv s sv b bv core corev
    fmlls fmlv fmllsv rsubs rsubsv acc accv lno lnov.
  NUM lno lnov ∧
  subst_TYPE s sv ∧
  BOOL b bv ∧
  core_TYPE core corev ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  pfs_TYPE pfs pfsv ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) acc accv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extract_clauses_arr" (get_ml_prog_state()))
    [lnov; sv; bv; corev; fmlv; rsubsv; pfsv; accv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        &(case extract_clauses_list s b core fmlls rsubs pfs acc of
            NONE => F
          | SOME res =>
            LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          extract_clauses_list s b core fmlls rsubs pfs acc = NONE)))
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
    first_x_assum (irule_at Any)>>
    qexists_tac`(NONE,r)::acc`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def])>>
  Cases_on`x`>> Cases_on`q`>>
  fs[PAIR_TYPE_def,SUM_TYPE_def]>>xmatch
  >- (
    (* INL *)
    xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[extract_clauses_list_def]>>
      metis_tac[Fail_exn_def])>>
    xlet_autop>>
    xlet_auto>>
    `OPTION_TYPE constraint_TYPE (any_el x fmlls NONE) v'` by (
       rw[any_el_ALT]>>
       fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    qpat_x_assum`v' = _` (assume_tac o SYM)>>
    Cases_on`any_el x fmlls NONE`>>fs[OPTION_TYPE_def]
    >- (
      xmatch>>
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[extract_clauses_list_def]>>
      metis_tac[Fail_exn_def])>>
    xmatch>>
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    first_x_assum (irule_at Any)>>simp[]>>
    qmatch_goalsub_abbrev_tac`extract_clauses_list _ _ _ _ _ _ acc'`>>
    qexists_tac`acc'`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,Abbr`acc'`])>>
  (* INR *)
  rpt xlet_autop>>
  IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
  >- (
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    first_x_assum (irule_at Any)>>simp[]>>
    qmatch_goalsub_abbrev_tac`extract_clauses_list _ _ _ _ _ _ acc'`>>
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
  fun subst_indexes_arr s b core fml is =
  case is of [] => []
  | (i::is) =>
    if core_only b core i
    then
      (case Array.lookup fml None i of
        None => subst_indexes_arr s b core fml is
      | Some res =>
      (case subst_opt_subst_fun s res of
        None => subst_indexes_arr s b core fml is
      | Some c => (i,c)::subst_indexes_arr s b core fml is))
    else
      subst_indexes_arr s b core fml is`
    |> append_prog;

Theorem subst_indexes_arr_spec:
  ∀is isv s sv b bv core corev fmlls fmllsv fmlv.
  subst_TYPE s sv ∧
  BOOL b bv ∧
  core_TYPE core corev ∧
  LIST_TYPE NUM is isv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "subst_indexes_arr" (get_ml_prog_state()))
    [sv; bv; corev; fmlv; isv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) (subst_indexes s b core fmlls is) v))
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
  reverse xif
  >- (
    xapp>>xsimpl>>
    rpt(asm_exists_tac>>xsimpl)>>
    simp[subst_indexes_def])>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  simp[subst_indexes_def]>>
  Cases_on`any_el h fmlls NONE`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>xapp>>
    metis_tac[])>>
  xmatch>>
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
  fun list_insert_fml_arr ls b core id fml inds =
    case ls of
      [] => (id,(core,(fml,inds)))
    | (c::cs) =>
      list_insert_fml_arr cs b
      (update_core b id core)
      (id+1)
      (Array.updateResize fml None id (Some c))
      (sorted_insert id inds)` |> append_prog

Theorem list_insert_fml_arr_spec:
  ∀ls lsv b bv core corev fmlv fmlls fmllsv id idv inds indsv.
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  BOOL b bv ∧
  core_TYPE core corev ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_insert_fml_arr" (get_ml_prog_state()))
    [lsv; bv; corev; idv; fmlv; indsv;]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      SEP_EXISTS fmlv' fmllsv'.
      ARRAY fmlv' fmllsv' *
      &(PAIR_TYPE NUM
          (PAIR_TYPE core_TYPE
          (PAIR_TYPE (λl v.
          LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
          v = fmlv') (LIST_TYPE NUM)))
          (list_insert_fml_list ls b core id fmlls inds) resv))
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
  simp[OPTION_TYPE_def]
QED

val check_subproofs_arr = process_topdecs`
  fun check_subproofs_arr lno pfs b core fml inds mindel id =
  case pfs of
    [] => (fml,(id,core))
  | (cnopt,pf)::pfs =>
    (case cnopt of
      None =>
      (case check_lsteps_arr lno pf b core fml inds mindel id of
        (fml', (inds', (id',core'))) =>
          check_subproofs_arr lno pfs b core' fml' inds' mindel id')
    | Some (cs,n) =>
      case list_insert_fml_arr cs b core id fml inds of
        (cid, (ccore, (cfml, cinds))) =>
        (case check_lsteps_arr lno pf b ccore cfml cinds id cid of
          (fml', (inds', (id',core'))) =>
          if check_contradiction_fml_arr b core' fml' n then
            let val u = rollback_arr fml' id id' in
              check_subproofs_arr lno pfs b core fml' inds' mindel id'
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n))))` |> append_prog

Theorem check_subproofs_arr_spec:
  ∀pfs fmlls inds mindel id pfsv lno lnov idv indsv fmlv fmllsv mindelv b bv core corev.
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) pfs pfsv ∧
  BOOL b bv ∧
  core_TYPE core corev ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_subproofs_arr" (get_ml_prog_state()))
    [lnov; pfsv; bv; corev; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_subproofs_list pfs b core fmlls inds mindel id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE NUM core_TYPE) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_subproofs_list pfs b core fmlls inds mindel id = NONE)))
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
  drule list_insert_fml_arr_spec>>
  rpt (disch_then drule)>>
  strip_tac>>
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
  reverse IF_CASES_TAC>>xif>>asm_exists_tac>>xsimpl
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

val check_red_arr = process_topdecs`
  fun check_red_arr lno ord obj b core fml inds id c s pfs idopt =
  (case reindex_arr b core fml inds of (rinds,fmlls) =>
  let
    val nc = not_1 c
    val rsubs = do_rso ord s c obj
    val cpfs = extract_clauses_arr lno s b core fml rsubs pfs []
    val fml_not_c = Array.updateResize fml None id (Some nc)
    val core_not_c = update_core b id core in
     case check_subproofs_arr lno cpfs b core_not_c
       fml_not_c (sorted_insert id rinds) id (id+1) of
       (fml', (id', core')) =>
     (case idopt of
       None =>
       let val u = rollback_arr fml' id id'
           val goals = subst_indexes_arr s b core fml' rinds in
           if red_cond_check fmlls nc pfs rsubs goals
           then
             (fml', (rinds,id'))
           else raise Fail (format_failure_2 lno ("Redundancy subproofs did not cover all subgoals.") (print_subproofs_err rsubs goals))
       end
    | Some cid =>
      if check_contradiction_fml_arr b core' fml' cid then
        let val u = rollback_arr fml' id id' in
          (fml', (rinds, id'))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
    end)` |> append_prog;

(* Overloads all the _TYPEs that we will reuse *)
Overload "spo_TYPE" = ``PAIR_TYPE
      (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM))``

Overload "ord_TYPE" = ``
  OPTION_TYPE (PAIR_TYPE spo_TYPE (LIST_TYPE NUM))``

Overload "obj_TYPE" = ``
  OPTION_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)``

Theorem check_red_arr_spec:
  NUM lno lnov ∧
  ord_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  BOOL b bv ∧
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  subst_TYPE s sv ∧
  pfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr" (get_ml_prog_state()))
    [lnov; ordv; objv; bv; corev; fmlv; indsv; idv;
      cv; sv; pfsv; idoptv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_red_list ord obj b core fmlls inds id
              c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list ord obj b core fmlls inds id
              c s pfs idopt = NONE)))
Proof
  rw[]>>
  xcf "check_red_arr" (get_ml_prog_state ())>>
  rw[check_red_list_def]>>
  xlet_autop>>
  pairarg_tac>>gs[]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  qmatch_asmsub_abbrev_tac`VECTOR_TYPE _ s _`>>
  qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
  xlet`(POSTve
    (λv.
      ARRAY aa vv *
      &(case extract_clauses_list s b core fmlls
          (do_rso ord s c obj) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
  (λe.
    ARRAY aa vv *
    & (Fail_exn e ∧
      extract_clauses_list s b core fmlls (do_rso ord s c obj) pfs [] = NONE)))`
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
  `LIST_REL (OPTION_TYPE constraint_TYPE)
    (update_resize fmlls NONE (SOME (not n)) id)
    (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
            (Conv (SOME (TypeStamp "Some" 2)) [vvv]) id)` by
    (match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def])>>
  xlet_autop
  >- (
    xsimpl>>rw[]>>
    fs[do_rso_def]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x'`>>simp[PAIR_TYPE_def]>>
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
  fun check_sstep_arr lno step ord obj core fml inds id =
  case step of
    Lstep lstep =>
    (case check_lstep_arr lno lstep False core fml inds 0 id of
      (fml, (inds, (id, core))) =>
      (fml,(inds,id)))
  | Red c s pfs idopt =>
    (case check_red_arr lno ord obj False core
        fml inds id c s pfs idopt of (fml',(rinds,id')) =>
       (Array.updateResize fml' None id' (Some c),
        (sorted_insert id' rinds,(id'+1))))
  ` |> append_prog

val NPBC_CHECK_SSTEP_TYPE_def = theorem "NPBC_CHECK_SSTEP_TYPE_def";

Theorem check_sstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_SSTEP_TYPE step stepv ∧
  ord_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_sstep_arr" (get_ml_prog_state()))
    [lnov; stepv; ordv; objv; corev; fmlv; indsv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_sstep_list step ord obj core fmlls inds id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_sstep_list step ord obj core fmlls inds id = NONE)))
Proof
  rw[]>>
  xcf "check_sstep_arr" (get_ml_prog_state ())>>
  rw[check_sstep_list_def]>>
  Cases_on`step`>>fs[NPBC_CHECK_SSTEP_TYPE_def]
  >- ((* lstep *)
    xmatch>>
    xlet_autop>>
    xlet`
      POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lstep_list l F core fmlls inds 0 id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE NUM core_TYPE)) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
        check_lstep_list l F core fmlls inds 0 id = NONE))`
    >- (
      xapp>>xsimpl>>
      CONJ_TAC >-  EVAL_TAC>>
      metis_tac[])
    >- xsimpl>>
    pop_assum mp_tac>> TOP_CASE_TAC>> simp[]>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl)
  >- ((*Red*)
    xmatch>>
    xlet_autop>>
    rename1`check_red_list ord obj F core fmlls inds id
              c s pfs idopt`>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_red_list ord obj F core fmlls inds id
              c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list ord obj F core fmlls inds id
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
    simp[OPTION_TYPE_def])
QED

val read_coref_arr = process_topdecs`
  fun read_coref_arr ls fml =
  case ls of [] => []
  | i::is =>
    case Array.lookup fml None i of
      None => read_coref_arr is fml
    | Some res => (i,res) :: read_coref_arr is fml` |> append_prog

Theorem read_coref_arr_spec:
  ∀ls lsv.
  LIST_TYPE NUM ls lsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_coref_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * &(
        LIST_TYPE (PAIR_TYPE NUM constraint_TYPE)
          (read_coref_list ls fmlls) v
      ))
Proof
  Induct>>rw[read_coref_list_def]>>
  xcf "read_coref_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >-
    (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>gs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xapp>>
    fs[LIST_TYPE_def,PAIR_TYPE_def])>>
  first_x_assum drule>>
  rw[]>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  fs[LIST_TYPE_def,PAIR_TYPE_def]
QED

val res = translate lrnext_def;
val res = translate foldi_def;
val res = translate toAList_def;

val res = translate fromAList_def;

Definition mapfsttoalist_def:
  mapfsttoalist c = MAP FST (toAList c)
End

val res = translate mapfsttoalist_def;

val coref_arr = process_topdecs`
  fun coref_arr core fml =
  let val ids = mapfsttoalist core in
  fromalist (read_coref_arr ids fml)
  end` |> append_prog

Theorem coref_arr_spec:
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "coref_arr" (get_ml_prog_state()))
    [corev; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * &(
        SPTREE_SPT_TYPE constraint_TYPE
          (coref_list core fmlls) v
      ))
Proof
  xcf "coref_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp_spec (fetch "-" "fromalist_v_thm" |> INST_TYPE [alpha|->``:npbc``])>>
  asm_exists_tac>>xsimpl>>
  rw[coref_list_def]>>
  fs[mapfsttoalist_def]
QED

Definition all_core_every_def:
  all_core_every (core:num_set) (inds:num list) =
  (EVERY (λn. lookup n core ≠ NONE) inds)
End

val res = translate all_core_every_def;

val all_core_arr_def = process_topdecs `
  fun all_core_arr fml inds core =
  let val inds' = fst (reindex_arr False Ln fml inds) in
    (all_core_every core inds',inds')
  end` |> append_prog

Theorem all_core_arr_spec:
  core_TYPE core corev ∧
  LIST_TYPE NUM inds indsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_core_arr" (get_ml_prog_state()))
    [fmlv; indsv; corev]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * &(
        PAIR_TYPE BOOL (LIST_TYPE NUM)
          (all_core fmlls inds core) v
      ))
Proof
  xcf "all_core_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex F LN fmlls inds) v)`
  >- (
    xapp>>xsimpl>>
    EVAL_TAC)>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  fs[all_core_def,all_core_every_def,PAIR_TYPE_def]
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
  check_storeorder spo ws pfs ⇔
  check_good_ord spo ∧ check_ws spo ws ∧
  check_transitivity spo ws pfs
End

val res = translate check_storeorder_def;

Definition do_transfer_def:
  do_transfer core ls =
  FOLDL (λa b. insert b () a) core ls
End

val res = translate do_transfer_def;

val every_transfer_check = process_topdecs`
  fun every_transfer_check fml ls =
  case ls of
    [] => True
  | (id::ls) =>
    (case Array.lookup fml None id of
      None => False
    | Some u => every_transfer_check fml ls)` |> append_prog

Theorem every_transfer_check_spec:
  ∀ls lsv fmlv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_transfer_check" (get_ml_prog_state()))
    [fmlv; lsv;]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      ARRAY fmlv fmllsv *
      &(BOOL (EVERY (λid. any_el id fmlls NONE ≠ NONE) ls) resv))
Proof
  Induct>>
  rw[]>>
  xcf "every_transfer_check" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  Cases_on`any_el h fmlls NONE`>>fs[OPTION_TYPE_def]>>
  xmatch >- (xcon>>xsimpl)>>
  xapp>>simp[]
QED

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

Definition core_subgoals_def:
  core_subgoals s cf =
  toAList (map_opt (subst_opt (subst_fun s)) cf)
End

val res = translate npbc_checkTheory.map_opt_def;
val res = translate core_subgoals_def;

Definition do_core_del_def:
  do_core_del (core:num_set) ls =
  FOLDL (λa b. delete b a) core ls
End

val res = translate do_core_del_def;
val res = translate core_from_inds_def;

Definition check_change_obj_pure_def:
  check_change_obj_pure core chk obj ord fc' n1 fc c1 c2 =
  ((chk ∨ IS_SOME ord ⇒ sptree$lookup n1 core = SOME ()) ∧
  imp c1 (model_bounding fc fc') ∧
  imp c2 (model_bounding fc' fc))
End

val res = translate npbc_checkTheory.model_bounding_def;
val res = translate check_change_obj_pure_def;

val check_change_obj_arr = process_topdecs`
  fun check_change_obj_arr lno fml core chk obj ord fc' n1 n2 =
  case obj of None =>
    raise Fail (format_failure lno ("no objective loaded"))
  | Some fc =>
    (case Array.lookup fml None n1 of
      None => raise Fail (format_failure lno
          ("invalid constraint ID in objective update"))
    | Some c1 =>
      (case Array.lookup fml None n2 of
      None => raise Fail (format_failure lno
          ("invalid constraint ID in objective update"))
    | Some c2 =>
      if check_change_obj_pure core chk obj ord fc' n1 fc c1 c2
      then ()
      else
      raise Fail (format_failure lno ("objective update check failed"))))` |> append_prog;

Theorem check_change_obj_arr_spec:
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  core_TYPE core corev ∧
  BOOL chk chkv ∧
  obj_TYPE obj objv ∧
  ord_TYPE ord ordv ∧
  PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT fc fcv ∧
  NUM n1 n1vv ∧
  NUM n2 n2vv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_change_obj_arr" (get_ml_prog_state()))
    [lnov; fmlv; corev; chkv; objv; ordv; fcv; n1vv; n2vv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(check_change_obj_list fmlls core
          chk obj ord fc n1 n2))
      (λe.
      ARRAY fmlv fmllsv *
        &(Fail_exn e ∧
          ¬check_change_obj_list fmlls core
          chk obj ord fc n1 n2 )))
Proof
  rw[]>>
  xcf "check_change_obj_arr" (get_ml_prog_state ())>>
  simp[check_change_obj_list_def]>>
  Cases_on`obj`>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  rpt xlet_autop>>
  xlet_auto>>
  rename1`cv1 = any_el n1 _ _`>>
  `OPTION_TYPE constraint_TYPE (any_el n1 fmlls NONE) cv1` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`cv1 = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>
  fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  rpt xlet_autop>>
  xlet_auto>>
  rename1`cv2 = any_el n2 _ _`>>
  `OPTION_TYPE constraint_TYPE (any_el n2 fmlls NONE) cv2` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`cv2 = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>
  fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xlet_autop>>
  xif
  >- (
    fs[check_change_obj_pure_def] >>
    xcon>>xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  fs[check_change_obj_pure_def]>>
  metis_tac[Fail_exn_def]
QED

Definition check_dom_list_def:
  check_dom_list spo obj core fml inds id c s pfs idopt =
  let (rinds,fmlls) = reindex F LN fml inds in
  let nc = not c in
  let fml_not_c = update_resize fml NONE (SOME nc) id in
  let w = subst_fun s in
  let cf = coref_list core fml in
  let dsubs = dom_subgoals spo w c obj in
  case extract_clauses_list s F LN fml dsubs pfs [] of
    NONE => NONE
  | SOME cpfs =>
    (case check_subproofs_list cpfs F LN fml_not_c (sorted_insert id rinds) id (id+1) of
      NONE => NONE
    | SOME (fml',id',core') =>
      let rfml = rollback fml' id id' in
      if do_dom_check idopt fml' rfml w cf fmlls nc pfs dsubs then
        SOME (rfml,rinds,id')
      else NONE)
End

val check_dom_arr = process_topdecs`
  fun check_dom_arr lno spo obj core fml inds id c s pfs idopt =
  (case reindex_arr False Ln fml inds of (rinds,fmlls) =>
    let
    val cf = coref_arr core fml
    val dsubs = do_dso spo s c obj
    val cpfs = extract_clauses_arr lno s False Ln fml dsubs pfs []
    val nc = not_1 c
    val fml_not_c = Array.updateResize fml None id (Some nc) in
     case check_subproofs_arr lno cpfs False Ln
      fml_not_c (sorted_insert id rinds) id (id+1) of
       (fml',(id',core')) =>
       (case idopt of
         None =>
         let val u = rollback_arr fml' id id'
             val goals = core_subgoals s cf in
             if red_cond_check fmlls nc pfs dsubs goals
             then
               (fml',(rinds,id'))
             else raise Fail (format_failure_2 lno ("Dominance subproofs did not cover all subgoals") (print_subproofs_err dsubs goals))
         end
       | Some cid =>
         if check_contradiction_fml_arr False Ln fml' cid then
           let val u = rollback_arr fml' id id' in
             (fml', (rinds,id'))
           end
         else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
    end)` |> append_prog;

Theorem check_dom_arr_spec:
  NUM lno lnov ∧
  PAIR_TYPE spo_TYPE (LIST_TYPE NUM) spo spov ∧
  obj_TYPE obj objv ∧
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  constraint_TYPE c cv ∧
  subst_TYPE s sv ∧
  pfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_dom_arr" (get_ml_prog_state()))
    [lnov; spov; objv; corev; fmlv; indsv; idv;
      cv; sv; pfsv; idoptv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_dom_list spo obj core fmlls inds id
              c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_dom_list spo obj core fmlls inds id
              c s pfs idopt = NONE)))
Proof
  rw[]>>
  xcf "check_dom_arr" (get_ml_prog_state ())>>
  rw[check_dom_list_def]>>
  pairarg_tac>>
  rpt xlet_autop>>
  xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex F LN fmlls inds) v)`
  >- (
    xapp>>xsimpl>>
    EVAL_TAC)>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet`(POSTve
    (λv.
      ARRAY fmlv fmllsv *
      &(case extract_clauses_list s F LN fmlls
        (do_dso spo s c obj) pfs [] of
          NONE => F
        | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
    (λe.
      ARRAY fmlv fmllsv *
      & (Fail_exn e ∧ extract_clauses_list s F LN fmlls
        (do_dso spo s c obj) pfs [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- metis_tac[]>>
    EVAL_TAC)
  >- (
    xsimpl>>
    simp[do_dso_def]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>TOP_CASE_TAC>>simp[]>>
  fs[do_dso_def]>>
  strip_tac>>
  rpt xlet_autop>>
  xlet_auto>>
  rpt xlet_autop>>
  rename1`_ (not n) vvv`>>
  `LIST_REL (OPTION_TYPE constraint_TYPE)
    (update_resize fmlls NONE (SOME (not n)) id)
    (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
            (Conv (SOME (TypeStamp "Some" 2)) [vvv]) id)` by (
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def])>>
  xlet`(POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_subproofs_list x F LN
            (update_resize fmlls NONE (SOME (not n)) id)
            (sorted_insert id rinds) id (id+1) of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE NUM core_TYPE) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_subproofs_list x F LN
            (update_resize fmlls NONE (SOME (not n)) id)
            (sorted_insert id rinds) id (id+1) = NONE)))`
  >- (
    xapp>>
    xsimpl>>
    CONJ_TAC >- EVAL_TAC>>
    CONJ_TAC >- metis_tac[]>>
    EVAL_TAC)
  >- (
    xsimpl>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x'`>>simp[PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  Cases_on`idopt`>>
  fs[OPTION_TYPE_def,do_dom_check_def]>>
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
  rename1`check_contradiction_fml_list F LN A B`>>
  xlet`POSTv v.
    ARRAY fmlv' fmllsv' * &
    BOOL (check_contradiction_fml_list F LN A B) v`
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

(*
val load_coref_arr = process_topdecs`
  fun load_coref_arr ls fml newfml =
  case ls of [] => ()
  | i::is =>
    if Array.length fml <= i
    then load_coref_arr is fml newfml
    else
      (Array.update newfml i
        (Array.sub fml i);
        load_coref_arr is fml newfml)` |> append_prog;

Theorem LUPDATE_outside:
  ∀ls n.
  LENGTH ls ≤ n ⇒
  LUPDATE v n ls = ls
Proof
  Induct>>rw[LUPDATE_DEF]
QED

Theorem load_coref_arr_spec:
  ∀ls lsv nfmlls nfmllsv.
  LIST_TYPE NUM ls lsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) nfmlls nfmllsv ∧
  LENGTH fmlls = LENGTH nfmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "load_coref_arr" (get_ml_prog_state()))
    [lsv; fmlv; nfmlv]
    (ARRAY fmlv fmllsv * ARRAY nfmlv nfmllsv)
    (POSTv v.
      SEP_EXISTS nfmllsv'.
      ARRAY fmlv fmllsv *
      ARRAY nfmlv nfmllsv' *
      &(
        LIST_REL (OPTION_TYPE constraint_TYPE)
          (load_coref_list ls fmlls nfmlls)
          nfmllsv'))
Proof
  Induct>>rw[load_coref_list_def]>>
  xcf "load_coref_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >-
    (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xif
  >- (
    xapp>>xsimpl>>
    DEP_REWRITE_TAC[LUPDATE_outside]>>
    fs[LIST_REL_EL_EQN])>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    fs[LIST_REL_EL_EQN])>>
  xapp>>xsimpl>>
  qexists_tac`LUPDATE (EL h fmlls) h nfmlls`>>simp[]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  fs[LIST_REL_EL_EQN,any_el_ALT]
QED

val arr_from_core_arr = process_topdecs`
  fun arr_from_core_arr core fml =
  let val ids = mapfsttoalist core
  val nfml = Array.array (Array.length fml) None
  val u = load_coref_arr ids fml nfml in
  (nfml, ids)
  end` |> append_prog

Theorem arr_from_core_arr_spec:
  core_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "arr_from_core_arr" (get_ml_prog_state()))
    [corev; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      SEP_EXISTS nfmlv nfmllsv.
      ARRAY fmlv fmllsv *
      ARRAY nfmlv nfmllsv *
      &(
        PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l nfmllsv ∧
              v = nfmlv) (LIST_TYPE NUM)
          (arr_from_core_list core fmlls) v))
Proof
  xcf "arr_from_core_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  simp[arr_from_core_list_def]>>
  xlet`POSTv v. SEP_EXISTS nfmllsv'.
    ARRAY fmlv fmllsv * ARRAY av nfmllsv' *
    &LIST_REL (OPTION_TYPE constraint_TYPE)
      (load_coref_list (mapfsttoalist core)
        fmlls (REPLICATE (LENGTH fmlls) NONE)) nfmllsv'`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>simp[]>>
    first_assum (irule_at Any)>>simp[]>>
    qexists_tac`REPLICATE (LENGTH fmlls) NONE`>>simp[]>>
    `LENGTH fmlls  = LENGTH fmllsv` by
      fs[LIST_REL_EL_EQN]>>
    pop_assum SUBST_ALL_TAC>>
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def])>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  fs[mapfsttoalist_def]>>
  first_x_assum (irule_at Any)>>
  xsimpl
QED
*)

Definition mapsndtoalist_def:
  mapsndtoalist c = MAP SND (toAList c)
End

val res = translate mapsndtoalist_def;

val res = translate npbc_checkTheory.update_bound_def;

val check_cstep_arr = process_topdecs`
  fun check_cstep_arr lno cstep core chk obj bound
    ord orders fml inds id =
  case cstep of
    Dom c s pfs idopt => (
    case ord of None =>
      raise Fail (format_failure lno
        "no order loaded for dominance")
    | Some spo =>
      case check_dom_arr lno spo obj
        core fml inds id c s pfs idopt of (fml',(rinds,id')) =>
      (Array.updateResize fml' None id' (Some c),
       (sorted_insert id' rinds,
       (id'+1,
       (core,(chk,(obj,(bound,(ord,orders)))))))))
  | Loadorder nn xs =>
    let val inds' = fst (reindex_arr False Ln fml inds) in
    case Alist.lookup orders nn of
      None =>
        raise Fail (format_failure lno ("no such order: " ^ nn))
    | Some ord' =>
      if List.length xs = List.length (fst (snd ord')) then
        (fml,(inds',(id,(core_from_inds inds',
          (chk,(obj,(bound,(Some (ord',xs),orders))))))))
      else
        raise Fail
          (format_failure lno ("invalid order instantiation"))
    end
  | Unloadorder =>
    (case ord of None =>
     raise Fail (format_failure lno ("no order loaded"))
    | Some spo =>
      (fml,(inds,(id,(core,
        (chk,(obj,(bound,(None, orders)))))))))
  | Storeorder nn spo ws pfs => (
    if check_storeorder spo ws pfs then
      (fml,(inds,(id,(core,
        (chk,(obj,(bound,(ord,((nn,spo)::orders)))))))))
    else
     raise Fail (format_failure lno ("invalid order definition")))
  | Transfer ls => (
    if every_transfer_check fml ls
    then
      (fml, (inds, (id,
       (do_transfer core ls,
       (chk,(obj,(bound, (ord, orders))))))))
    else
     raise Fail (format_failure lno ("core transfer invalid ids")))
  | Checkeddelete n s pfs idopt => (
    case Array.lookup fml None n of None =>
      raise Fail (format_failure lno
        "invalid core deletion ID")
    | Some c => (
      if lookup_1 n core = Some () then
        (let
          val nc = delete_1 n core in
          (case
            check_red_arr lno ord obj True nc
            fml inds id c s pfs idopt of (fml',(inds',id')) =>
              (list_delete_arr [n] fml';
              (fml', (inds', (id',
                  (nc, (chk, (obj, (bound, (ord, orders))))))))))
        end)
      else raise Fail (format_failure lno
        "invalid core deletion ID (non-core)")
      ))
  | Uncheckeddelete ls => (
    if ord = None then
      (list_delete_arr ls fml;
        (fml, (inds, (id, (do_core_del core ls,
          (False,(obj,(bound, (ord, orders)))))))))
    else
      case all_core_arr fml inds core of (ac,inds') =>
      if ac then
        (list_delete_arr ls fml;
          (fml, (inds', (id, (do_core_del core ls,
            (False, (obj, (bound, (ord, orders)))))))))
      else
         raise Fail (format_failure lno ("not all constraints in core")))
  | Sstep sstep => (
    case check_sstep_arr lno sstep ord obj core fml inds id of
      (fml',(inds',id')) =>
      (fml',(inds',(id',(core,
        (chk,(obj,(bound,(ord,orders)))))))))
  | Obj w mi bopt => (
    case check_obj obj w
        (mapsndtoalist (coref_arr core fml)) bopt of
      None =>
       raise Fail (format_failure lno ("supplied assignment did not satisfy constraints or did not improve objective"))
    | Some new =>
      let val bound' = update_bound chk bound new in
      if mi
      then
        if not chk then
          raise Fail (format_failure lno ("cannot improve objective after unchecked core deletions"))
        else
        let val c = model_improving obj new in
          (Array.updateResize fml None id (Some c),
           (sorted_insert id inds,
           (id+1,
           (insert_1 id () core,
           (chk,(obj,(bound', (ord, orders))))))))
        end
      else
        (fml, (inds, (id,
           (core,(chk,(obj,(bound',(ord, orders))))))))
      end
    )
  | Changeobj fc' n1 n2 =>
    (check_change_obj_arr lno fml core chk obj ord fc' n1 n2;
      (fml, (inds, (id, (core, (chk,
        (Some fc', (bound, (ord, orders)))))))))`
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
  core_TYPE core corev ∧
  BOOL chk chkv ∧
  obj_TYPE obj objv ∧
  OPTION_TYPE INT bound boundv ∧
  ord_TYPE ord ordv ∧
  LIST_TYPE (PAIR_TYPE STRING_TYPE spo_TYPE) orders ordersv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cstep_arr" (get_ml_prog_state()))
    [lnov; cstepv; corev; chkv; objv; boundv; ordv; ordersv;
      fmlv; indsv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_cstep_list cstep core chk obj bound
            ord orders fmlls inds id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE NUM
                (PAIR_TYPE core_TYPE
                (PAIR_TYPE BOOL
                (PAIR_TYPE obj_TYPE
                (PAIR_TYPE (OPTION_TYPE INT)
                (PAIR_TYPE ord_TYPE
                  (LIST_TYPE (PAIR_TYPE STRING_TYPE spo_TYPE)))))))))
              res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_cstep_list cstep core chk obj bound ord orders fmlls inds id = NONE)))
Proof
  rw[]>>
  xcf "check_cstep_arr" (get_ml_prog_state ())>>
  rw[check_cstep_list_def]>>
  Cases_on`cstep`>>fs[NPBC_CHECK_CSTEP_TYPE_def]
  >- ( (* Dom*)
    xmatch>>
    Cases_on`ord`>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    pairarg_tac>>xlet_autop
    >- (
      xsimpl>>
      simp[check_dom_list_def]>>
      rw[]>>
      qexists_tac`x'`>>qexists_tac`x''`>>xsimpl>>
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
    unabbrev_all_tac>>
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def])
  >- ( (* LoadOrder*)
    xmatch>>
    rpt xlet_autop>>
    xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE)
        (reindex F LN fmlls inds) v)`
    >- (
      xapp>>xsimpl>>
      EVAL_TAC)>>
    rpt xlet_autop>>
    Cases_on`ALOOKUP orders m`>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    reverse(IF_CASES_TAC)>>gs[]>>
    xif>>asm_exists_tac>>simp[]
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* UnloadOrder *)
    xmatch>>
    Cases_on`ord`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,OPTION_TYPE_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* StoreOrder *)
    xmatch>>
    xlet_autop>>
    simp[GSYM check_storeorder_def]>>
    IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def,OPTION_TYPE_def,LIST_TYPE_def,check_storeorder_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xraise >> xsimpl>>
    fs[check_storeorder_def,Fail_exn_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* Transfer *)
    xmatch>>
    xlet_autop>>
    IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
    >- (
      reverse CONJ_TAC >-
        metis_tac[NOT_EXISTS,NOT_EVERY]>>
      rpt xlet_autop>>
      xcon>> xsimpl>>
      fs[PAIR_TYPE_def,OPTION_TYPE_def,LIST_TYPE_def,do_transfer_def]>>
      metis_tac[ARRAY_refl,NOT_EXISTS,NOT_EVERY])>>
    rw[]>>
    rpt xlet_autop>>
    xraise >> xsimpl>>
    fs[Fail_exn_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* CheckedDelete*)
    xmatch>>
    rpt xlet_autop>>
    xlet_auto>>
    rename1`cv = any_el n _ _`>>
    `OPTION_TYPE constraint_TYPE (any_el n fmlls NONE) cv` by (
      rw[any_el_ALT]>>
      fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    qpat_x_assum`cv = _` (assume_tac o SYM)>>
    Cases_on`any_el n fmlls NONE`>>
    fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (lookup n core = SOME()) v`
    >- (
      xapp_spec (mlbasicsProgTheory.eq_v_thm |> INST_TYPE [alpha |-> ``:unit option``])>>
      xsimpl>>
      first_x_assum (irule_at Any)>>
      qexists_tac`SOME ()`>>simp[OPTION_TYPE_def,BOOL_def]>>
      metis_tac[EqualityType_OPTION_TYPE,EqualityType_NUM_BOOL])>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    rename1`check_red_list ord obj T (delete n core) fmlls inds
      id c s pfs idopt`>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_red_list ord obj T (delete n core) fmlls
            inds id c s pfs idopt of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE (LIST_TYPE NUM) NUM) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_red_list ord obj T (delete n core) fmlls
            inds id c s pfs idopt = NONE))`
    >- (
      xapp>>xsimpl>>
      CONJ_TAC >- EVAL_TAC>>metis_tac[])>>
    xsimpl
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    strip_tac>>xmatch>>
    rpt xlet_autop>>
    xlet`POSTv resv.
         &UNIT_TYPE () resv *
         SEP_EXISTS fmllsv'.
           ARRAY fmlv' fmllsv' *
           &LIST_REL (OPTION_TYPE constraint_TYPE)
             (list_delete_list [n] x0) fmllsv'`
    >- (
      xapp>>
      simp[LIST_TYPE_def])>>
    rpt xlet_autop>>
    xcon>>xsimpl)
  >- ( (* Uncheckeddelete *)
    xmatch>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * &(BOOL (ord = NONE) v)`
    >- (
      xapp_spec (mlbasicsProgTheory.eq_v_thm |> INST_TYPE [alpha |-> ``:((((int # num) list # num) list # num list # num list) # num list) option``])>>
      xsimpl>>
      first_x_assum (irule_at Any)>>
      qexists_tac`NONE`>>simp[OPTION_TYPE_def]>>
      metis_tac[EqualityType_ord_TYPE])>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      fs[do_core_del_def]>>
      xsimpl)>>
    rpt xlet_autop>>
    pairarg_tac>>fs[PAIR_TYPE_def]>>
    xmatch>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      fs[do_core_del_def]>>
      xsimpl)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_refl])
  >- ( (* Sstep *)
    xmatch>>
    xlet_autop
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl)
  >- ( (* Obj *)
    xmatch>>
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`check_obj _ _ lss bopt`>>
    Cases_on`check_obj obj s lss bopt`>>
    fs[OPTION_TYPE_def,mapsndtoalist_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise >> xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    xlet_autop>>
    xif
    >- ( (* model improving *)
      xlet_autop>>
      xif >- (
        rpt xlet_autop>>
        xraise >> xsimpl>>
        fs[Fail_exn_def]>>
        metis_tac[ARRAY_refl])>>
      rpt xlet_autop>>
      xlet_auto>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
      qexists_tac`A`>>xsimpl>>
      unabbrev_all_tac>>
      reverse CONJ_TAC >-
        fs[]>>
      match_mp_tac LIST_REL_update_resize>>
      fs[OPTION_TYPE_def])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>xsimpl)
  >- ( (* ChangeObj *)
    xmatch>>
    rpt xlet_autop
    >- (
      xsimpl>>
      simp[Fail_exn_def]>>
      metis_tac[ARRAY_refl,Fail_exn_def])>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
    metis_tac[ARRAY_refl])
QED

val check_implies_fml_arr = process_topdecs`
  fun check_implies_fml_arr fml n c =
  case Array.lookup fml None n of
    None => False
  | Some ci => imp ci c
` |> append_prog

Theorem check_implies_fml_arr_spec:
  NUM n nv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
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
  `OPTION_TYPE constraint_TYPE (any_el n fmlls NONE) v'` by (
     rw[any_el_ALT]>>
     fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
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
  fun check_hconcl_arr fml obj fml' obj' bound' hconcl =
  case hconcl of
    Hnoconcl => True
  | Hdsat wopt => check_sat fml obj bound' wopt
  | Hdunsat n =>
    (bound' = None andalso
      check_contradiction_fml_arr False Ln fml' n)
  | Hobounds lbi ubi n wopt =>
    if opt_le lbi bound' then
      check_ub fml obj bound' ubi wopt andalso
    (case lbi of
      None => check_contradiction_fml_arr False Ln fml' n
    | Some lb => check_implies_fml_arr fml' n (lower_bound obj' lb)
    )
    else False` |> append_prog

val NPBC_CHECK_HCONCL_TYPE_def = theorem"NPBC_CHECK_HCONCL_TYPE_def";

Theorem check_hconcl_arr_spec:
  LIST_TYPE constraint_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  obj_TYPE obj1 obj1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  NPBC_CHECK_HCONCL_TYPE hconcl hconclv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_hconcl_arr" (get_ml_prog_state()))
    [fmlv; objv; fml1v; obj1v; bound1v; hconclv]
    (ARRAY fml1v fmllsv)
    (POSTv v.
        ARRAY fml1v fmllsv *
        &(
        BOOL (check_hconcl_list fml obj fmlls obj1
          bound1 hconcl) v))
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
    xlet`POSTv v. ARRAY fml1v fmllsv * &(BOOL(bound1=NONE) v)`
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
  >-
    (xcon>>xsimpl)>>
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
