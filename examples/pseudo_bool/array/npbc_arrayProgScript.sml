(*
  Refine npbc_list to npbc_array
*)
Theory npbc_arrayProg
Libs
  preamble basis MapProgLib
Ancestors
  UnsafeProg UnsafeProof npbc npbc_slot npbc_list pb_parse

val _ = hide_environments true;
val _ = translation_extends"UnsafeProg";

val _ = MapProgLib.add_fmap_for_cmp miscTheory.TotOrd_num_cmp;

Quote add_cakeml:
  exception Fail string;
End

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``«Fail»``

Definition Fail_exn_def:
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)
End

val _ = register_type ``:constr``

Theorem EqualityType_NPBC_CHECK_CONSTR_TYPE[simp]:
  EqualityType NPBC_CHECK_CONSTR_TYPE
Proof
  ‘EqualityType (APP_LIST_TYPE (PAIR_TYPE NUM (PBC_LIT_TYPE NUM)))’
    by simp (eq_lemmas())>>
  simp (eq_lemmas())
QED

val _ = register_type ``:lstep ``
val _ = register_type ``:sstep ``

Definition format_failure_def:
  format_failure (lno:num) s =
  «c Checking failed for top-level proof step starting at line: » ^ toString lno ^ « (error may be in subproofs). Reason: » ^ s ^ «\n»
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

Theorem multiply_eq[local]:
  multiply c k =
  if k = 1 then c else
  let (l,n) = c in
  if k = 0 then ([],0) else
    (MAP (λ(c,v). (c * &k,v)) l,n * &k)
Proof
  Cases_on `c`>>rw[multiply_def]>>
  fs[GSYM LAMBDA_PROD,MAP_ID]
QED

val r = translate multiply_eq;
val r = translate minus_def;

val r = translate IQ_def;
val r = translate div_ceiling_def;
val r = translate div_ceiling_up_def;
val r = translate divide_def;

val r = translate strip_zero_def;

val r = translate cg_offset_def;

val cg_offset_side_def = fetch "-" "cg_offset_side_def";

val cg_offset_side = Q.prove(
  `∀x y. y ≠ 0 ⇒ cg_offset_side x y`,
  ho_match_mp_tac cg_offset_ind>>
  rw[]>>
  simp[Once cg_offset_side_def]) |> update_precondition;

val r = translate var_divide_def;

val r = translate mir_coeff_def;

val r = translate mir_def;

val r = translate var_form_offset_def;
val r = translate integerTheory.INT_MIN;
val r = translate var_mir_coeff_def;

val var_mir_coeff_side = Q.prove(
  `∀x y z. y ≠ 0 ⇒ var_mir_coeff_side x y z`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate var_mir_def;

val divide_side = Q.prove(
  `∀x y. divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  intLib.ARITH_TAC
  ) |> update_precondition

val var_divide_side = Q.prove(
  `∀x y. var_divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  rw[]>>gvs[]
  >- (irule cg_offset_side>>fs[])
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- (irule cg_offset_side>>fs[])
  >- intLib.ARITH_TAC) |> update_precondition;

val mir_side = Q.prove(
  `∀x y. mir_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  rw[]>>gvs[]
  >- (irule INT_MOD_nat_nn>>fs[])
  >- intLib.ARITH_TAC
  >- (irule INT_MOD_nat_nn>>fs[])) |> update_precondition;

val var_mir_side = Q.prove(
  `∀x y. var_mir_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  rw[]>>gvs[]
  >- intLib.ARITH_TAC
  >- (irule INT_MOD_nat_nn>>fs[])) |> update_precondition;

val r = translate npbc_checkTheory.do_divide_def;

val do_divide_side = Q.prove(
  `do_divide_side dty x y ⇔ y ≠ 0`,
  EVAL_TAC>>
  Cases_on`dty`>>rw[]) |> update_precondition;

Definition sat_map_def:
  (sat_map (nn:int) [] = []) ∧
  (sat_map nn (cv::rest) =
    let
      rest' = sat_map nn rest;
      (c,v) = cv
    in
      if c < 0 then
        let nnn = -nn in
          if nnn <= c then
            if rest' = []
            then rest' else cv::rest'
          else
            (nnn,v)::
              if rest' = [] then rest else rest'
      else
        if c <= nn then
          if rest' = []
          then rest'
          else cv::rest'
        else
          (nn,v)::
            if rest' = [] then rest else rest')
End

Theorem sat_map_eq_MAP:
  ∀l l'.
  0 < nn ∧
  sat_map nn l = l' ⇒
  if sat_map nn l = []
  then
    MAP (λ(c,v). (abs_min c (Num (ABS nn)),v)) l = l
  else
    MAP (λ(c,v). (abs_min c (Num (ABS nn)),v)) l = l'
Proof
  Induct
  >- rw[sat_map_def]>>
  rpt gen_tac>> strip_tac>>
  Cases_on`h`>>
  rename1`(c,v)`>>
  gvs[sat_map_def,abs_min_def]>>
  every_case_tac>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem saturate_eq:
  saturate(l,n) =
  if n ≤ 0 then ([],n)
  else
    let l' = sat_map n l in
    if l' = [] then (l,n)
    else (l',n)
Proof
  rw[saturate_def]>>
  gvs[integerTheory.INT_NOT_LE]>>
  drule sat_map_eq_MAP>>
  disch_then (qspecl_then[`l`,`sat_map n l`] mp_tac)>>
  rw[]
QED

val r = translate sat_map_def;
val r = translate saturate_eq;

val r = translate integerTheory.INT_ABS;

val r = translate (weaken_aux_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

val r = translate weaken_def;

val res = translate npbc_checkTheory.mk_strict_aux_def;
val res = translate npbc_checkTheory.mk_strict_def;
val res = translate npbc_checkTheory.mk_strict_sorted_num_def;

val r = translate npbc_checkTheory.weaken_sorted_def;

val r = translate npbc_checkTheory.fuse_weaken_def;
val r = translate npbc_checkTheory.sing_lit_def;
val r = translate npbc_checkTheory.clean_triv_def;

val r = translate npbc_checkTheory.bal_add_round_def;
val r = translate npbc_checkTheory.bal_add_def;

Definition lookup_err_string_def:
  lookup_err_string b =
    if b then
      «invalid core constraint id: »
    else «invalid constraint id: »
End

val r = translate lookup_err_string_def;

(* Overload notation for long _TYPE relations *)
Overload "constraint_TYPE" = ``PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT``
Overload "bconstraint_TYPE" = ``PAIR_TYPE constraint_TYPE BOOL``

val NPBC_CHECK_CONSTR_TYPE_def = fetch "-" "NPBC_CHECK_CONSTR_TYPE_def";
val PBC_LIT_TYPE_def = fetch "-" "PBC_LIT_TYPE_def"

(* Stored constraints *)
val _ = register_type ``:slot``;

val SLOT_TYPE_def = fetch "-" "NPBC_SLOT_SLOT_TYPE_def";

(* A slot held in the formula array: its two vectors have the same length,
  which bounds the unchecked reads of the slot functions *)
Definition fslot_TYPE_def:
  fslot_TYPE s v ⇔ wf_slot s ∧ NPBC_SLOT_SLOT_TYPE s v
End

Theorem fslot_TYPE_Empty[simp]:
  fslot_TYPE Empty v ⇔ NPBC_SLOT_SLOT_TYPE Empty v
Proof
  simp[fslot_TYPE_def,wf_slot_def]
QED

Theorem LIST_REL_fslot_TYPE_wf:
  LIST_REL fslot_TYPE fmlls fmllsv ⇒ EVERY wf_slot fmlls
Proof
  rw[LIST_REL_EL_EQN,EVERY_EL,fslot_TYPE_def]
QED

Theorem LIST_TYPE_fslot_TYPE:
  ∀l v.
  LIST_TYPE fslot_TYPE l v ⇔
  LIST_TYPE NPBC_SLOT_SLOT_TYPE l v ∧ EVERY wf_slot l
Proof
  Induct>>rw[LIST_TYPE_def,fslot_TYPE_def]>>
  metis_tac[]
QED

Theorem LIST_REL_fslot_TYPE_any_el:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NPBC_SLOT_SLOT_TYPE Empty ev ⇒
  fslot_TYPE (any_el n fmlls Empty) (any_el n fmllsv ev)
Proof
  rw[any_el_ALT]>>
  gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def]
QED

val r = translate sum_max_abs_def;
val r = translate terms_fst_def;
val r = translate terms_snd_def;
val r = translate terms_neg_fst_def;
val r = translate enc_thm;

val r = translate dec_terms_def;
val r = translate dec_def;

Theorem dec_terms_side[local]:
  ∀i cs vs acc.
  i ≤ length cs ∧ i ≤ length vs ⇒ dec_terms_side cs vs i acc
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "dec_terms_side_def")]
QED

Theorem dec_side:
  wf_slot s ⇒ dec_side s
Proof
  Cases_on`s`>>
  rw[fetch "-" "dec_side_def",wf_slot_def]>>
  irule dec_terms_side>>
  simp[]
QED

Quote add_cakeml:
  fun lookup_core_only_arr b fml n =
  let val s = Array.lookup fml Empty n in
    case s of
      Empty => Empty
    | Stored cs vs d mc sm b' =>
      if not b orelse b' then s
      else Empty
  end
End

Theorem lookup_core_only_arr_spec:
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lookup_core_only_arr" (get_ml_prog_state()))
    [bv; fmlv; nv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &fslot_TYPE (lookup_core_only_list b fmlls n) v)
Proof
  rpt strip_tac>>
  simp[lookup_core_only_list_def]>>
  xcf"lookup_core_only_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `fslot_TYPE (any_el n fmlls Empty) v'` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el n fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def,core_slot_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    simp[wf_slot_def,SLOT_TYPE_def])>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (¬b ∨ b') v`
  >- (
    xlog>>xsimpl>>
    Cases_on`b`>>gvs[]>>
    xvar>>xsimpl)>>
  xif
  >- (
    xvar>>xsimpl>>
    simp[SLOT_TYPE_def])>>
  xcon>>xsimpl>>
  simp[wf_slot_def,SLOT_TYPE_def]
QED

Quote add_cakeml:
  fun lookup_core_only_err_arr lno b fml n =
  let val s = Array.lookup fml Empty n in
    case s of
      Empty =>
        raise Fail (format_failure lno (lookup_err_string b ^ Int.toString n))
    | Stored cs vs d mc sm b' =>
      if not b orelse b' then s
      else
        raise Fail (format_failure lno (lookup_err_string b ^ Int.toString n))
  end
End

Theorem lookup_core_only_err_arr_spec:
  NUM lno lnov ∧
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lookup_core_only_err_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; nv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(lookup_core_only_list b fmlls n ≠ Empty ∧
          fslot_TYPE (lookup_core_only_list b fmlls n) v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          lookup_core_only_list b fmlls n = Empty)))
Proof
  rpt strip_tac>>
  simp[lookup_core_only_list_def]>>
  xcf"lookup_core_only_err_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `fslot_TYPE (any_el n fmlls Empty) v'` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el n fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def,core_slot_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (¬b ∨ b') v`
  >- (
    xlog>>xsimpl>>
    Cases_on`b`>>gvs[]>>
    xvar>>xsimpl)>>
  xif
  >- (
    xvar>>xsimpl>>
    simp[SLOT_TYPE_def])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun lincomb_ids_arr lno b fml ids =
  case ids of
    [] => []
  | ((n,k)::ids) =>
    let val c = multiply (dec (lookup_core_only_err_arr lno b fml n)) k in
      c :: lincomb_ids_arr lno b fml ids
    end
End

Theorem lincomb_ids_arr_spec:
  ∀ids idsv lno lnov b bv fmlls fmllsv fmlv.
  LIST_TYPE (PAIR_TYPE NUM NUM) ids idsv ∧
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lincomb_ids_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; idsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case lookup_lincomb_list b fmlls ids of NONE => F
          | SOME x => LIST_TYPE constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          lookup_lincomb_list b fmlls ids = NONE)))
Proof
  Induct>>rw[]>>
  xcf "lincomb_ids_arr" (get_ml_prog_state ())
  >- (
    fs[LIST_TYPE_def,lookup_lincomb_list_def]>>
    xmatch>>xcon>>xsimpl>>
    simp[LIST_TYPE_def])>>
  Cases_on`h`>>
  rename1`LIST_TYPE _ ((n,k)::_) _`>>
  gvs[LIST_TYPE_def,PAIR_TYPE_def,lookup_lincomb_list_def,
    lookup_core_only_dec_def]>>
  xmatch>>
  xlet_autop >- (xsimpl>>simp[])>>
  qmatch_asmsub_abbrev_tac`fslot_TYPE s v`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &constraint_TYPE (dec s) v`
  >- (
    xapp>>xsimpl>>
    qexists_tac`s`>>
    fs[fslot_TYPE_def,dec_side])>>
  Cases_on`s`>>fs[]>>
  xlet_autop>>
  xlet_autop>>
  Cases_on`lookup_lincomb_list b fmlls ids`>>fs[]>>
  xcon>>xsimpl>>
  simp[LIST_TYPE_def]
QED

(* Throws an error *)
Quote add_cakeml:
  fun check_cutting_arr lno b fml constr =
  case constr of
    Id n =>
    dec (lookup_core_only_err_arr lno b fml n)
  | Add c1 c2 =>
    add (check_cutting_arr lno b fml c1)
      (check_cutting_arr lno b fml c2)
  | Mul c k =>
    multiply (check_cutting_arr lno b fml c) k
  | Div_1 dty c k =>
    if k <> 0 then
      do_divide dty (check_cutting_arr lno b fml c) k
    else raise Fail (format_failure lno ("divide by zero"))
  | Minus c k =>
    minus (check_cutting_arr lno b fml c) k
  | Sat c =>
    saturate (check_cutting_arr lno b fml c)
  | Lit l =>
    (case l of
      Pos v => ([(1,v)], 0)
    | Neg v => ([(~1,v)], 0))
  | Weak c vs =>
    weaken_sorted (check_cutting_arr lno b fml c) vs
  | Triv ls => (clean_triv ls)
  | Lincomb ids ns =>
    let val ic = bal_add (lincomb_ids_arr lno b fml ids)
        val ncs = check_cutting_nest_arr lno b fml ns in
      bal_add (ic :: ncs)
    end
  and check_cutting_nest_arr lno b fml ns =
  case ns of
    [] => []
  | ((c,k)::ns) =>
    let val c = multiply (check_cutting_arr lno b fml c) k in
      c :: check_cutting_nest_arr lno b fml ns
    end
End

Theorem check_cutting_arr_spec_aux:
  (∀b fmlls constr constrv lno lnov bv fmllsv fmlv.
  NPBC_CHECK_CONSTR_TYPE constr constrv ∧
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
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
          check_cutting_list b fmlls constr = NONE)))) ∧
  (∀b fmlls ns nsv lno lnov bv fmllsv fmlv.
  LIST_TYPE (PAIR_TYPE NPBC_CHECK_CONSTR_TYPE NUM) ns nsv ∧
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cutting_nest_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; nsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case check_cutting_list_nest b fmlls ns of NONE => F
          | SOME x => LIST_TYPE constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          check_cutting_list_nest b fmlls ns = NONE))))
Proof
  ho_match_mp_tac check_cutting_list_ind >> rw[]>>
  xcfs ["check_cutting_arr","check_cutting_nest_arr"] (get_ml_prog_state ())
  >~[`Lincomb`] >- (
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- (xsimpl>>simp[])>>
    Cases_on`lookup_lincomb_list b fmlls ids`>>fs[]>>
    rename1`lookup_lincomb_list _ _ _ = SOME ics`>>
    xlet_autop>>
    xlet_autop >- (xsimpl>>simp[])>>
    Cases_on`check_cutting_list_nest b fmlls ns`>>fs[]>>
    rename1`check_cutting_list_nest _ _ _ = SOME ncs`>>
    xlet_autop>>
    xapp>>xsimpl>>
    qexists_tac`bal_add ics::ncs`>>
    simp[LIST_TYPE_def])
  >~[`check_cutting_list_nest _ _ []`] >- (
    fs[check_cutting_list_def,LIST_TYPE_def]>>
    xmatch>>xcon>>xsimpl>>
    simp[LIST_TYPE_def])
  >~[`check_cutting_list_nest _ _ (_::_)`] >- (
    fs[check_cutting_list_def,LIST_TYPE_def,PAIR_TYPE_def]>>
    rename1`NPBC_CHECK_CONSTR_TYPE c _`>>
    xmatch>>
    xlet_autop >- (xsimpl>>simp[])>>
    Cases_on`check_cutting_list b fmlls c`>>fs[]>>
    xlet_autop>>
    xlet_autop >- (xsimpl>>simp[])>>
    Cases_on`check_cutting_list_nest b fmlls ns`>>fs[]>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def])
  >~[`Id`] >- (
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def,lookup_core_only_dec_def]>>
    xmatch>>
    xlet_autop >- (xsimpl>>simp[])>>
    xapp>>xsimpl>>
    qexists_tac`lookup_core_only_list b fmlls n`>>
    gvs[fslot_TYPE_def,dec_side]>>
    Cases_on`lookup_core_only_list b fmlls n`>>gvs[])
  >~[`Add`] >- (
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >~[`Mul`] >- (
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >~[`Div`] >- (
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
   >~[`Minus`] >- (
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >~[`Sat`] >- ( (* Sat *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop
    >- xsimpl>>
    xapp_spec
    (fetch "-" "saturate_v_thm" |> INST_TYPE [alpha|->``:num``])>>
    xsimpl>>
    gvs[AllCasePreds()]>>
    qexists_tac`x`>>qexists_tac`NUM`>>
    xsimpl>>
    simp (eq_lemmas()))
  >~[`Lit`] >- ( (* Lit *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    Cases_on`l`>>
    fs[PBC_LIT_TYPE_def]>>xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def,PAIR_TYPE_def])
  >~[`Weak`]>- ( (* Weak *)
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
  >~[`Triv`]>- ( (* Triv *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    metis_tac[]
  )
QED

Theorem check_cutting_arr_spec = CONJUNCT1 check_cutting_arr_spec_aux

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

Quote add_cakeml:
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
End

val res = translate npbc_checkTheory.constraint_of_spt_def;

Quote add_cakeml:
  fun check_cutting_alt_arr lno fml constr =
  constraint_of_spt (check_cutting_spt_arr lno fml constr)
End
*)

(* Translation for pb checking *)

val r = translate check_lslack_def;
val r = translate check_contradiction_def;

Quote add_cakeml:
  fun delete_arr i fml =
    if Array.length fml <= i then ()
    else
      (Unsafe.update fml i Empty)
End

Theorem delete_arr_spec:
  NUM i iv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_arr" (get_ml_prog_state()))
    [iv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL fslot_TYPE (delete_list i fmlls) fmllsv') )
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
  match_mp_tac EVERY2_LUPDATE_same>> simp[SLOT_TYPE_def]
QED

Quote add_cakeml:
  fun list_delete_arr ls fml =
    case ls of
      [] => ()
    | (i::is) =>
      (delete_arr i fml; list_delete_arr is fml)
End

Theorem list_delete_arr_spec:
  ∀ls lsv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_delete_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL fslot_TYPE (list_delete_list ls fmlls) fmllsv') )
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

Quote add_cakeml:
  fun rollback_arr fml id_start id_end =
  if id_start < id_end then
    (delete_arr id_start fml; rollback_arr fml (id_start + 1) id_end)
  else ()
End

Theorem rollback_arr_spec:
  ∀fmlls start end fmllsv startv.
  NUM start startv ∧
  NUM end endv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rollback_arr" (get_ml_prog_state()))
    [fmlv;startv; endv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL fslot_TYPE (rollback fmlls start end) fmllsv') )
Proof
  ho_match_mp_tac rollback_ind>>
  rw[]>>
  xcf"rollback_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  simp[Once rollback_def]>>
  reverse xif
  >- (xcon>>xsimpl>>metis_tac[])>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

val res = translate (not_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])
val res = translate sorted_insert_def;

val res = translate contr_slot_def;

Quote add_cakeml:
  fun check_contradiction_fml_arr b fml n =
    contr_slot (lookup_core_only_arr b fml n)
End

Theorem check_contradiction_fml_arr_spec:
  NUM n nv ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
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
  xcf "check_contradiction_fml_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>xsimpl>>
  gvs[fslot_TYPE_def]>>
  metis_tac[]
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

Definition err_check_string_def:
  err_check_string c c' =
  concat[
    «constraint id check failed. expect: »;
    npbc_constr_string c;
    « got (in checker): »;
    npbc_constr_string c']
End

Definition err_imp_string_def:
  err_imp_string c c' =
  concat[
    «imply-add for constraint id. expect: »;
    npbc_constr_string c;
    « from: »;
    npbc_constr_string c']
End

val res = translate coeff_lit_string_def;

val coeff_lit_string_side = Q.prove(
  `∀n. coeff_lit_string_side n ⇔ T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
) |> update_precondition;

val res = translate npbc_lhs_string_def;
val res = translate npbc_constr_string_def;
val res = translate npbc_string_def;
val res = translate err_check_string_def;
val res = translate err_imp_string_def;

Quote add_cakeml:
  fun delete_ids_arr mindel fml ls =
  case ls of [] => True
  | (i::is) =>
    (case Array.lookup fml Empty i of
      Empty => mindel <= i andalso delete_ids_arr mindel fml is
    | Stored cs vs d mc sm b =>
      if not b andalso mindel <= i then
        (Unsafe.update fml i Empty; delete_ids_arr mindel fml is)
      else False)
End

Theorem delete_ids_arr_spec:
  ∀ls lsv fmlls fmllsv.
  NUM mindel mindelv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM ls lsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_ids_arr" (get_ml_prog_state()))
    [mindelv; fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      SEP_EXISTS fmllsv'. ARRAY fmlv fmllsv' *
      &(case delete_ids_list mindel fmlls ls of
          NONE => BOOL F v
        | SOME fmlls' => BOOL T v ∧ LIST_REL fslot_TYPE fmlls' fmllsv'))
Proof
  Induct>>
  rw[]>>
  xcf "delete_ids_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl>>simp[delete_ids_list_def])>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el h fmllsv _`>>
  `fslot_TYPE (any_el h fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    `lookup_core_only_list T fmlls h = Empty` by
      simp[lookup_core_only_list_def,core_slot_def]>>
    `delete_list h fmlls = fmlls` by (
      rw[delete_list_def]>>gvs[any_el_ALT]>>
      rw[LIST_EQ_REWRITE,EL_LUPDATE]>>rw[])>>
    xlet_autop>>
    xlog>>xsimpl>>
    rw[]
    >- (simp[delete_ids_list_def]>>xapp>>metis_tac[])>>
    gvs[delete_ids_list_def])>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv bv. ARRAY fmlv fmllsv * &BOOL (¬b ∧ mindel ≤ h) bv`
  >- (
    xlog>>xsimpl>>rw[]>>gvs[]>>xapp>>xsimpl>>
    qexistsl_tac[`&h`,`&mindel`]>>gvs[NUM_def])>>
  `h < LENGTH fmlls ∧ LENGTH fmlls = LENGTH fmllsv` by (
    imp_res_tac LIST_REL_LENGTH>>
    gvs[any_el_ALT,AllCaseEqs()])>>
  xif
  >- (
    `lookup_core_only_list T fmlls h = Empty` by
      simp[lookup_core_only_list_def,core_slot_def]>>
    xlet_auto >- (xcon>>xsimpl)>>
    xlet_auto >- xsimpl>>
    simp[delete_ids_list_def,delete_list_def]>>
    xapp>>
    simp[]>>
    match_mp_tac EVERY2_LUPDATE_same>> simp[SLOT_TYPE_def])>>
  xcon>>xsimpl>>
  gvs[delete_ids_list_def,lookup_core_only_list_def,core_slot_def]
QED

(* The RUP assignment: an array of nums *)
Definition NUM_ARRAY_def:
  NUM_ARRAY av ls = SEP_EXISTS vs. ARRAY av vs * &LIST_REL NUM ls vs
End

Theorem NUM_ARRAY_refl:
  (NUM_ARRAY av ls ==>> NUM_ARRAY av ls) ∧
  (NUM_ARRAY av ls ==>> NUM_ARRAY av ls * GC)
Proof
  xsimpl
QED

Quote add_cakeml:
  fun grow_assg_arr assg st sz =
  if Array.length assg < sz then
    (Array.array (2 * sz) 0, 1)
  else
    (assg, st)
End

Theorem grow_assg_arr_spec:
  NUM st stv ∧
  NUM sz szv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "grow_assg_arr" (get_ml_prog_state()))
    [assgv; stv; szv]
    (NUM_ARRAY assgv assg)
    (POSTv v.
      SEP_EXISTS assgv' assg' st'.
      NUM_ARRAY assgv' assg' *
      &(PAIR_TYPE $= NUM (assgv',st') v ∧
        grow_assg assg st sz = (assg',st')))
Proof
  rw[]>>
  xcf "grow_assg_arr" (get_ml_prog_state ())>>
  xlet`POSTv lv. NUM_ARRAY assgv assg * &NUM (LENGTH assg) lv`
  >- (
    simp[NUM_ARRAY_def]>>xpull>>
    xapp>>xsimpl>>
    imp_res_tac LIST_REL_LENGTH>>simp[])>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    rpt xlet_autop>>
    xcon>>
    simp[grow_assg_def,PAIR_TYPE_def,NUM_ARRAY_def]>>
    xsimpl>>
    simp[LIST_REL_REPLICATE_same,NUM_def,INT_def])>>
  xcon>>
  simp[grow_assg_def,PAIR_TYPE_def]>>
  xsimpl
QED

(* Stores slot s, whose largest variable is mv *)
Quote add_cakeml:
  fun store_slot_arr fml s mv id assg st =
  case grow_assg_arr assg st (mv + 1) of (assg',st') =>
    (Array.updateResize fml Empty id s, (id+1, (assg', st')))
End

Theorem store_slot_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fslot_TYPE s sv ∧
  NUM mv mvv ∧
  NUM id idv ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "store_slot_arr" (get_ml_prog_state()))
    [fmlv; sv; mvv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTv v.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))
            (store_slot fmlls s mv id assg st) v))
Proof
  rw[store_slot_def]>>
  xcf "store_slot_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet`POSTv v.
    SEP_EXISTS assgv' assg' st'.
    ARRAY fmlv fmllsv * NUM_ARRAY assgv' assg' *
    &(PAIR_TYPE $= NUM (assgv',st') v ∧
      grow_assg assg st (mv + 1) = (assg',st'))`
  >- (
    xapp>>xsimpl>>
    first_assum (irule_at Any)>>
    first_assum (irule_at Any)>>
    qexists_tac`assg`>>
    xsimpl>>
    rw[]>>
    first_assum (irule_at Any)>>
    xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  match_mp_tac LIST_REL_update_resize>>
  simp[SLOT_TYPE_def]
QED

val r = translate enc_mv_def;
val r = translate neg_slot_def;

Quote add_cakeml:
  fun opt_update_arr fml c id assg st =
    case c of
      None => (fml,(id,(assg,st)))
    | Some (c,b) =>
      (case enc_mv c b of (s,mv) =>
        store_slot_arr fml s mv id assg st)
End

Quote add_cakeml:
  fun opt_update_neg_arr fml c b id assg st =
    case neg_slot c b of (s,mv) =>
      store_slot_arr fml s mv id assg st
End

Theorem ARRAY_refl:
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Theorem ARRAY_NUM_ARRAY_refl:
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg ==>> ARRAY fml fmllsv * NUM_ARRAY assgv assg ) ∧
  (NUM_ARRAY assgv assg * ARRAY fml fmllsv ==>> ARRAY fml fmllsv * NUM_ARRAY assgv assg) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg ==>> ARRAY fml fmllsv * NUM_ARRAY assgv assg * GC) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg ==>> NUM_ARRAY assgv assg * ARRAY fml fmllsv * GC) ∧
  (NUM_ARRAY assgv assg * ARRAY fml fmllsv ==>> ARRAY fml fmllsv * NUM_ARRAY assgv assg * GC) ∧
  (NUM_ARRAY assgv assg * ARRAY fml fmllsv * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv) ∧
  (NUM_ARRAY assgv assg * ARRAY fml fmllsv * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv * GC)  ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv * GC) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv ==>>
    NUM_ARRAY assgv assg * ARRAY fml fmllsv * ARRAY vimapv vimaplsv) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv ==>>
    NUM_ARRAY assgv assg * ARRAY fml fmllsv * ARRAY vimapv vimaplsv * GC) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv ==>>
    ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg * ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv ==>>
    ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg * ARRAY fml fmllsv * GC) ∧
  (ARRAY fml fmllsv * ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg ==>>
    ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg * ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv * ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg ==>>
    ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg * ARRAY fml fmllsv * GC) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv) ∧
  (ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv * GC) ∧
  (NUM_ARRAY assgv assg * ARRAY fml fmllsv * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv) ∧
  (NUM_ARRAY assgv assg * ARRAY fml fmllsv * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv * GC) ∧
  (ARRAY fml fmllsv * ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv) ∧
  (ARRAY fml fmllsv * ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv * GC) ∧
  (ARRAY vimapv vimaplsv * ARRAY fml fmllsv * NUM_ARRAY assgv assg *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv) ∧
  (ARRAY vimapv vimaplsv * ARRAY fml fmllsv * NUM_ARRAY assgv assg *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv * GC) ∧
  (ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg * ARRAY fml fmllsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv) ∧
  (ARRAY vimapv vimaplsv * NUM_ARRAY assgv assg * ARRAY fml fmllsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv * GC) ∧
  (NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv * ARRAY fml fmllsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv) ∧
  (NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv * ARRAY fml fmllsv *
    ARRAY bksv bkslsv ==>>
    ARRAY fml fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
    ARRAY bksv bkslsv * GC)
Proof
  rw[]>>
  xsimpl
QED

Theorem opt_update_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  OPTION_TYPE bconstraint_TYPE c cv ∧
  NUM id idv ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "opt_update_arr" (get_ml_prog_state()))
    [fmlv; cv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTv v.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))
            (opt_update fmlls c id assg st) v))
Proof
  Cases_on`c`>>rw[]>>
  xcf"opt_update_arr"(get_ml_prog_state ())>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac[`fmlv`,`fmllsv`,`assgv`,`assg`]>>
    simp[PAIR_TYPE_def]>>
    xsimpl)>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def]>>
  xmatch>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`st`,`enc q r`,`max_var (FST q)`,`id`,`fmlls`,`assg`]>>
  simp[fslot_TYPE_def,opt_update_def,enc_mv_enc]>>
  xsimpl>>
  rpt strip_tac>>
  first_x_assum (irule_at Any)>>
  xsimpl
QED

Theorem opt_update_neg_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  constraint_TYPE c cv ∧
  BOOL b bv ∧
  NUM id idv ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "opt_update_neg_arr" (get_ml_prog_state()))
    [fmlv; cv; bv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTv v.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))
            (opt_update_neg fmlls c b id assg st) v))
Proof
  rw[]>>
  xcf"opt_update_neg_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  gvs[neg_slot_enc,PAIR_TYPE_def]>>
  xmatch>>
  xapp>>
  xsimpl>>
  qexistsl_tac[`emp`,`st`,`enc (not c) b`,`max_var (FST c)`,`id`,`fmlls`,`assg`]>>
  simp[fslot_TYPE_def,opt_update_def,enc_mv_enc,max_var_not]>>
  xsimpl>>
  rpt strip_tac>>
  first_x_assum (irule_at Any)>>
  xsimpl
QED

Definition nabs_def:
  nabs i = Num (ABS i)
End

val res = translate nabs_def;

Definition w8z_def:
  w8z = (0w: word8)
End

Definition w8o_def:
  w8o = (1w: word8)
End

val w8z_v_thm = translate w8z_def;
val w8o_v_thm = translate w8o_def;

(* The slack of the constraint over its terms from index i down, stopping
  once it reaches lim *)
Quote add_cakeml:
  fun rup_pass1_arr assg st st1 cs vs lim i acc =
  if lim <= acc then acc
  else if i = 0 then acc
  else
    let
      val i1 = i - 1
      val n = Unsafe.vsub vs i1
      val c = Unsafe.vsub cs i1
      val v = Unsafe.sub assg n
    in
      if 0 <= c then
        rup_pass1_arr assg st st1 cs vs lim i1
          (if v < st orelse v = st1 then acc + c else acc)
      else
        rup_pass1_arr assg st st1 cs vs lim i1
          (if v = st1 then acc else acc - c)
    end
End

Theorem rup_pass1_arr_spec:
  ∀i acc iv accv.
  NUM st stv ∧
  NUM st1 st1v ∧
  VECTOR_TYPE INT cs csv ∧
  VECTOR_TYPE NUM vs vsv ∧
  NUM lim limv ∧
  NUM i iv ∧
  NUM acc accv ∧
  i ≤ length cs ∧ i ≤ length vs ∧
  rup_pass1_fast assg st st1 cs vs lim i acc = (acc',T)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rup_pass1_arr" (get_ml_prog_state()))
    [assgv; stv; st1v; csv; vsv; limv; iv; accv]
    (NUM_ARRAY assgv assg)
    (POSTv v.
      NUM_ARRAY assgv assg * &NUM acc' v)
Proof
  Induct
  >- (
    rw[]>>
    pop_assum mp_tac>> simp[Once rup_pass1_fast_def]>> strip_tac>>
    xcf "rup_pass1_arr" (get_ml_prog_state ())>>
    xlet_autop>>
    xif
    >- (xvar>>xsimpl>>gvs[])>>
    xlet_autop>>
    xif>>
    asm_exists_tac>>simp[]>>
    xvar>>xsimpl>>gvs[])>>
  rw[]>>
  pop_assum mp_tac>> simp[Once rup_pass1_fast_def]>> strip_tac>>
  xcf "rup_pass1_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (xvar>>xsimpl>>gvs[])>>
  xlet_autop>>
  xif>>
  asm_exists_tac>>simp[]>>
  rpt xlet_autop>>
  `sub vs i < LENGTH assg` by (CCONTR_TAC>>gvs[])>>
  gvs[]>>
  xlet`POSTv v. NUM_ARRAY assgv assg * &NUM (EL (sub vs i) assg) v`
  >- (
    simp[NUM_ARRAY_def]>>xpull>>
    xapp>>xsimpl>>
    qexists_tac`sub vs i`>>
    imp_res_tac LIST_REL_LENGTH>>
    gvs[LIST_REL_EL_EQN,NUM_def,INT_def])>>
  xlet_autop>>
  xif
  >- (
    gvs[]>>
    xlet_autop>>
    xlet`POSTv bv. NUM_ARRAY assgv assg *
      &BOOL (EL (sub vs i) assg < st ∨ EL (sub vs i) assg = st1) bv`
    >- (
      xlog>>xsimpl>>rw[]>>gvs[]>>
      xapp_spec (mlbasicsProgTheory.eq_v_thm |>
        INST_TYPE [alpha |-> ``:num``])>>
      xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      simp[EqualityType_NUM_BOOL])>>
    xlet`POSTv v. NUM_ARRAY assgv assg *
      &NUM (if EL (sub vs i) assg < st ∨ EL (sub vs i) assg = st1
            then acc + Num (sub cs i) else acc) v`
    >- (
      xif
      >- (
        xapp>>xsimpl>>
        qexistsl_tac[`sub cs i`,`&acc`]>>
        gvs[NUM_def]>>
        `&(acc + Num (sub cs i)) = &acc + sub cs i` by intLib.ARITH_TAC>>
        simp[])>>
      xvar>>xsimpl)>>
    xapp>>
    simp[PULL_EXISTS]>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  gvs[]>>
  xlet`POSTv bv. NUM_ARRAY assgv assg * &BOOL (EL (sub vs i) assg = st1) bv`
  >- (
    xapp_spec (mlbasicsProgTheory.eq_v_thm |>
      INST_TYPE [alpha |-> ``:num``])>>
    xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[EqualityType_NUM_BOOL])>>
  xlet`POSTv v. NUM_ARRAY assgv assg *
    &NUM (if EL (sub vs i) assg = st1 then acc
          else acc + Num (-sub cs i)) v`
  >- (
    xif
    >- (xvar>>xsimpl)>>
    xapp>>xsimpl>>
    qexistsl_tac[`sub cs i`,`&acc`]>>
    gvs[NUM_def]>>
    `&(acc + Num (-sub cs i)) = &acc - sub cs i` by intLib.ARITH_TAC>>
    simp[])>>
  xapp>>
  simp[PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

(* Assigns the unassigned variables that the slack forces, over the terms
  from index i down *)
Quote add_cakeml:
  fun rup_pass2_arr assg st st1 gap cs vs i =
  if i = 0 then ()
  else
    let
      val i1 = i - 1
      val n = Unsafe.vsub vs i1
    in
      if Unsafe.sub assg n < st then
        let val c = Unsafe.vsub cs i1 in
          if 0 <= c then
            if gap < c then
              (Unsafe.update assg n st1;
               rup_pass2_arr assg st st1 gap cs vs i1)
            else rup_pass2_arr assg st st1 gap cs vs i1
          else if gap < 0 - c then
            (Unsafe.update assg n st;
             rup_pass2_arr assg st st1 gap cs vs i1)
          else rup_pass2_arr assg st st1 gap cs vs i1
        end
      else rup_pass2_arr assg st st1 gap cs vs i1
    end
End

Theorem rup_pass2_arr_spec:
  ∀i assg iv.
  NUM st stv ∧
  NUM st1 st1v ∧
  NUM gap gapv ∧
  VECTOR_TYPE INT cs csv ∧
  VECTOR_TYPE NUM vs vsv ∧
  NUM i iv ∧
  i ≤ length cs ∧ i ≤ length vs ∧
  rup_pass2_fast assg st st1 gap cs vs i = (assg1,T)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rup_pass2_arr" (get_ml_prog_state()))
    [assgv; stv; st1v; gapv; csv; vsv; iv]
    (NUM_ARRAY assgv assg)
    (POSTv v.
      NUM_ARRAY assgv assg1 * &UNIT_TYPE () v)
Proof
  Induct
  >- (
    rw[]>>
    pop_assum mp_tac>> simp[Once rup_pass2_fast_def]>> strip_tac>>
    xcf "rup_pass2_arr" (get_ml_prog_state ())>>
    xlet_autop>>
    xif>>
    asm_exists_tac>>simp[]>>
    xcon>>xsimpl>>gvs[])>>
  rw[]>>
  pop_assum mp_tac>> simp[Once rup_pass2_fast_def]>> strip_tac>>
  xcf "rup_pass2_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>
  asm_exists_tac>>simp[]>>
  rpt xlet_autop>>
  `sub vs i < LENGTH assg` by (CCONTR_TAC>>gvs[])>>
  gvs[]>>
  xlet`POSTv v. NUM_ARRAY assgv assg * &NUM (EL (sub vs i) assg) v`
  >- (
    simp[NUM_ARRAY_def]>>xpull>>
    xapp>>xsimpl>>
    qexists_tac`sub vs i`>>
    imp_res_tac LIST_REL_LENGTH>>
    gvs[LIST_REL_EL_EQN,NUM_def,INT_def])>>
  xlet_autop>>
  reverse xif
  >- (xapp>>gvs[])>>
  gvs[]>>
  rpt xlet_autop>>
  xif
  >- (
    gvs[]>>
    xlet`POSTv bv. NUM_ARRAY assgv assg * &BOOL (gap < Num (sub cs i)) bv`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`sub cs i`,`&gap`]>>
      gvs[NUM_def]>>
      `&gap < sub cs i ⇔ gap < Num (sub cs i)` by intLib.ARITH_TAC>>
      simp[])>>
    xif
    >- (
      xlet`POSTv uv. NUM_ARRAY assgv (LUPDATE st1 (sub vs i) assg)`
      >- (
        simp[NUM_ARRAY_def]>>xpull>>
        xapp>>xsimpl>>
        qexists_tac`sub vs i`>>
        imp_res_tac LIST_REL_LENGTH>>
        gvs[NUM_def,INT_def,EVERY2_LUPDATE_same])>>
      xapp>>gvs[])>>
    xapp>>gvs[])>>
  gvs[]>>
  xlet_autop>>
  xlet`POSTv bv. NUM_ARRAY assgv assg * &BOOL (gap < Num (-sub cs i)) bv`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`-sub cs i`,`&gap`]>>
    gvs[NUM_def]>>
    `&gap < -sub cs i ⇔ gap < Num (-sub cs i)` by intLib.ARITH_TAC>>
    simp[])>>
  xif
  >- (
    xlet`POSTv uv. NUM_ARRAY assgv (LUPDATE st (sub vs i) assg)`
    >- (
      simp[NUM_ARRAY_def]>>xpull>>
      xapp>>xsimpl>>
      qexists_tac`sub vs i`>>
      imp_res_tac LIST_REL_LENGTH>>
      gvs[NUM_def,INT_def,EVERY2_LUPDATE_same])>>
    xapp>>gvs[])>>
  xapp>>gvs[]
QED

(* Returns true if the stored constraint with these fields is falsified
  under the assignment *)
Quote add_cakeml:
  fun update_assg_fields_arr assg st cs vs d mc =
  if d <= 0 then False
  else
    let
      val lim = d + mc
      val st1 = st + 1
      val len = Vector.length cs
      val max = rup_pass1_arr assg st st1 cs vs lim len 0
    in
      if lim <= max then False
      else if max < d then True
      else (rup_pass2_arr assg st st1 (max - d) cs vs len; False)
    end
End

Theorem update_assg_fields_arr_spec:
  VECTOR_TYPE INT cs csv ∧
  VECTOR_TYPE NUM vs vsv ∧
  INT d dv ∧
  NUM mc mcv ∧
  NUM st stv ∧
  length cs = length vs ∧
  update_assg_slot assg st (Stored cs vs d mc sm b) = (res,assg1,T)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "update_assg_fields_arr" (get_ml_prog_state()))
    [assgv; stv; csv; vsv; dv; mcv]
    (NUM_ARRAY assgv assg)
    (POSTv v.
      NUM_ARRAY assgv assg1 * &BOOL res v)
Proof
  rw[]>>
  gvs[GSYM update_assg_fast_eq,update_assg_fast_def]>>
  xcf "update_assg_fields_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (gvs[]>>xcon>>xsimpl)>>
  gvs[]>>
  rpt (pairarg_tac>>gvs[])>>
  `pre` by (every_case_tac>>gvs[])>>
  xlet`POSTv v. NUM_ARRAY assgv assg * &NUM (mc + Num d) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`&mc`,`d`]>>
    gvs[NUM_def]>>
    `&(mc + Num d) = d + &mc` by intLib.ARITH_TAC>>
    simp[])>>
  rpt xlet_autop>>
  xlet`POSTv v. NUM_ARRAY assgv assg * &NUM max' v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`cs`,`length vs`,`mc + Num d`,`st`,`st + 1`,`vs`]>>
    gvs[])>>
  xlet_autop>>
  xif
  >- (gvs[]>>xcon>>xsimpl)>>
  xlet`POSTv bv. NUM_ARRAY assgv assg * &BOOL (max' < Num d) bv`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`d`,`&max'`]>>
    gvs[NUM_def]>>
    `&max' < d ⇔ max' < Num d` by intLib.ARITH_TAC>>
    simp[])>>
  xif
  >- (gvs[]>>xcon>>xsimpl)>>
  xlet`POSTv v. NUM_ARRAY assgv assg * &NUM (max' − Num d) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`d`,`&max'`]>>
    gvs[NUM_def]>>
    `&(max' − Num d) = &max' − d` by intLib.ARITH_TAC>>
    simp[])>>
  xlet`POSTv uv. NUM_ARRAY assgv assg'`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`assg'`,`assg`,`cs`,`max' − Num d`,`length vs`,
      `st`,`st + 1`,`vs`]>>
    gvs[]>>xsimpl)>>
  gvs[]>>xcon>>xsimpl
QED

Quote add_cakeml:
  fun check_rup_loop_arr lno b nc fml assg st ls =
  case ls of
    [] =>
      raise Fail (format_failure lno ("contradiction not derived at end of hints"))
  | (n::ns) =>
    (case (if n = 0 then nc else Array.lookup fml Empty n) of
      Empty =>
        raise Fail (format_failure lno (lookup_err_string b ^ Int.toString n))
    | Stored cs vs d mc sm b' =>
      if n <> 0 andalso b andalso not b' then
        raise Fail (format_failure lno (lookup_err_string b ^ Int.toString n))
      else if update_assg_fields_arr assg st cs vs d mc then ()
      else check_rup_loop_arr lno b nc fml assg st ns)
End

Theorem check_rup_loop_arr_spec:
  ∀ns nsv assg res assg'.
  NUM lno lnov ∧
  BOOL b bv ∧
  fslot_TYPE nc ncv ∧ nc ≠ Empty ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM st stv ∧
  LIST_TYPE NUM ns nsv ∧
  check_rup_loop_list b nc fmlls assg st ns = (res,assg',T)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_rup_loop_arr" (get_ml_prog_state()))
    [lnov; bv; ncv; fmlv; assgv; stv; nsv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv * NUM_ARRAY assgv assg' *
        &(res ∧ UNIT_TYPE () v))
      (λe.
        ARRAY fmlv fmllsv * NUM_ARRAY assgv assg' *
        &(Fail_exn e ∧ ¬res)))
Proof
  Induct>>rw[]>>
  xcf "check_rup_loop_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def,check_rup_loop_list_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>metis_tac[])>>
  xmatch>>
  xlet_autop>>
  qabbrev_tac`s0 = if h = 0 then nc else any_el h fmlls Empty`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * &fslot_TYPE s0 v`
  >- (
    xif
    >- (xvar>>xsimpl>>gvs[Abbr`s0`])>>
    xlet_auto >- (xcon>>xsimpl)>>
    xapp>>xsimpl>>
    qexists_tac`h`>>
    rw[Abbr`s0`,any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  `get_rup_constraint_list b fmlls h nc =
    if h ≠ 0 ∧ b ∧ ¬core_slot s0 then Empty else s0` by (
    rw[Abbr`s0`,get_rup_constraint_list_def,lookup_core_only_list_def]>>
    gvs[])>>
  pop_assum SUBST_ALL_TAC>>
  Cases_on`s0`>>fs[fslot_TYPE_def,SLOT_TYPE_def,core_slot_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>metis_tac[])>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv bv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * &BOOL (h ≠ 0 ∧ b) bv`
  >- (
    xlog>>xsimpl>>
    Cases_on`h ≠ 0`>>gvs[]>>
    xvar>>xsimpl)>>
  xlet`POSTv bv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    &BOOL (h ≠ 0 ∧ b ∧ ¬b') bv`
  >- (
    xlog>>xsimpl>>
    Cases_on`h ≠ 0 ∧ b`>>gvs[]>>
    xapp>>xsimpl>>
    qexists_tac`b'`>>simp[])>>
  xif
  >- (
    gvs[]>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>metis_tac[])>>
  qpat_x_assum `(if _ then _ else _) = _` kall_tac>>
  qpat_x_assum `_ = (res,assg',T)` mp_tac>>
  IF_CASES_TAC
  >- metis_tac[]>>
  qpat_x_assum `_ ∨ _` kall_tac>>
  qpat_x_assum `¬(_ ∧ _)` kall_tac>>
  simp[]>>strip_tac>>
  rpt (pairarg_tac>>gvs[])>>
  `pre` by (every_case_tac>>gvs[])>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg'' * &BOOL done' v`
  >- (
    xapp>>xsimpl>>
    gvs[]>>
    first_assum (irule_at Any)>>
    gvs[wf_slot_def]>>
    qexists_tac`ARRAY fmlv fmllsv`>>xsimpl)>>
  xif
  >- (
    xcon>>xsimpl>>
    gvs[]>>
    xsimpl)>>
  gvs[]>>
  xapp>>xsimpl
QED

(* A fresh all-unassigned array of at least sz entries, or the stamp
  advanced by 2 *)
Quote add_cakeml:
  fun reset_dm_arr assg st sz =
  if Array.length assg < sz then
    (Array.array (2 * sz) 0, 1)
  else
    (assg, st + 2)
End

Theorem reset_dm_arr_spec:
  NUM st stv ∧
  NUM sz szv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reset_dm_arr" (get_ml_prog_state()))
    [assgv; stv; szv]
    (NUM_ARRAY assgv assg)
    (POSTv v.
      SEP_EXISTS assgv' assg' st'.
      NUM_ARRAY assgv' assg' *
      &(PAIR_TYPE $= NUM (assgv',st') v ∧
        reset_dm_list assg st sz = (assg',st')))
Proof
  rw[]>>
  xcf "reset_dm_arr" (get_ml_prog_state ())>>
  xlet`POSTv lv. NUM_ARRAY assgv assg * &NUM (LENGTH assg) lv`
  >- (
    simp[NUM_ARRAY_def]>>xpull>>
    xapp>>xsimpl>>
    imp_res_tac LIST_REL_LENGTH>>simp[])>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    rpt xlet_autop>>
    xcon>>
    simp[reset_dm_list_def,PAIR_TYPE_def,NUM_ARRAY_def]>>
    xsimpl>>
    simp[LIST_REL_REPLICATE_same,NUM_def,INT_def])>>
  xlet_autop>>
  xcon>>
  simp[reset_dm_list_def,PAIR_TYPE_def]>>
  xsimpl
QED

Quote add_cakeml:
  fun check_rup_arr lno b nc sz fml assg st ls =
  case reset_dm_arr assg st sz of (assg,st) =>
    (check_rup_loop_arr lno b nc fml assg st ls; (assg,st))
End

Theorem check_rup_arr_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  fslot_TYPE nc ncv ∧ nc ≠ Empty ∧
  NUM sz szv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM st stv ∧
  LIST_TYPE NUM ns nsv ∧
  check_rup_list b nc sz fmlls assg st ns = (res,assg1,st1,T)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_rup_arr" (get_ml_prog_state()))
    [lnov; bv; ncv; szv; fmlv; assgv; stv; nsv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS assgv'.
        NUM_ARRAY assgv' assg1 *
        &(res ∧ PAIR_TYPE $= NUM (assgv',st1) v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS assgv'.
        NUM_ARRAY assgv' assg1 *
        &(Fail_exn e ∧ ¬res)))
Proof
  rw[check_rup_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  xcf "check_rup_arr" (get_ml_prog_state ())>>
  xlet`POSTv v. SEP_EXISTS av.
    ARRAY fmlv fmllsv * NUM_ARRAY av assg' * &PAIR_TYPE $= NUM (av,st') v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY fmlv fmllsv`,`sz`,`st`,`assg`]>>
    simp[]>>
    xsimpl>>
    rw[]>>gvs[]>>
    first_x_assum (irule_at Any)>>
    xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTve
    (λv. ARRAY fmlv fmllsv * NUM_ARRAY av assg'' * &(res ∧ UNIT_TYPE () v))
    (λe. ARRAY fmlv fmllsv * NUM_ARRAY av assg'' * &(Fail_exn e ∧ ¬res))`
  >- (
    xapp>>xsimpl>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    qexists_tac`av`>>
    xsimpl)>>
  xcon>>xsimpl
QED

val res = translate npbc_checkTheory.map_app_list_def;
val res = translate npbc_checkTheory.mul_triv_def;
val res = translate SmartAppend_def;
val res = translate npbc_checkTheory.is_sum_def;
val res = translate npbc_checkTheory.mk_lincomb_def;
val res = translate npbc_checkTheory.to_triv_def;

Theorem to_triv_ind_thm[local]:
  to_triv_ind
Proof
  once_rewrite_tac [fetch "-" "to_triv_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = to_triv_ind_thm |> update_precondition;

val res = translate check_trivial_def;
val res = translate match_sign_def;
val res = translate imp_terms_def;
val res = translate check_imp_lists_def;
val res = translate check_imp_def;
val res = translate imp_def;

val res = translate eq_terms_def;
val res = translate eq_slot_def;
val res = translate check_lslack_slot_def;
val res = translate check_imp_slot_def;
val res = translate imp_slot_def;

Theorem eq_terms_side[local]:
  ∀cs vs n i l.
  n ≤ length cs ∧ n ≤ length vs ⇒ eq_terms_side cs vs n i l
Proof
  ho_match_mp_tac eq_terms_ind>>
  rw[]>>
  simp[Once (fetch "-" "eq_terms_side_def")]
QED

Theorem eq_slot_side:
  wf_slot s ⇒ eq_slot_side c s
Proof
  Cases_on`s`>>
  rw[fetch "-" "eq_slot_side_def",wf_slot_def]>>
  irule eq_terms_side>>
  simp[]
QED

Theorem check_lslack_slot_side[local]:
  ∀cs n i rhs.
  n ≤ length cs ⇒ check_lslack_slot_side cs n i rhs
Proof
  ho_match_mp_tac check_lslack_slot_ind>>
  rw[]>>
  simp[Once (fetch "-" "check_lslack_slot_side_def")]
QED

Theorem check_imp_slot_side[local]:
  ∀drhs cs vs n i ls rhs.
  n ≤ length cs ∧ n ≤ length vs ⇒
  check_imp_slot_side drhs cs vs n i ls rhs
Proof
  ho_match_mp_tac check_imp_slot_ind>>
  rw[]>>
  simp[Once (fetch "-" "check_imp_slot_side_def")]>>
  rw[check_lslack_slot_side]
QED

Theorem imp_slot_side:
  wf_slot s ⇒ imp_slot_side s c
Proof
  Cases_on`s`>>
  rw[fetch "-" "imp_slot_side_def",wf_slot_def]>>
  irule check_imp_slot_side>>
  simp[]
QED

Quote add_cakeml:
  fun check_lstep_arr lno step b fml mindel id assg st =
  case step of
    Check n c =>
      let val s = lookup_core_only_err_arr lno b fml n in
        if eq_slot c s then (fml, (None, (id, (assg, st))))
        else raise Fail (format_failure lno (err_check_string c (dec s)))
      end
  | Implyadd n c =>
      let val s = lookup_core_only_err_arr lno b fml n in
        if imp_slot s c then (fml, (Some(c,b), (id, (assg, st))))
        else raise Fail (format_failure lno (err_imp_string c (dec s)))
      end
  | Noop => (fml, (None, (id, (assg, st))))
  | Delete ls =>
      if delete_ids_arr mindel fml ls then
        (fml, (None, (id, (assg, st))))
      else
        raise Fail (format_failure lno ("deletion not permitted for core constraints and constraint index < " ^ Int.toString mindel))
  | Cutting constr =>
    let val c = check_cutting_arr lno b fml (to_triv constr) in
      (fml, (Some(c,b), (id, (assg, st))))
    end
  | Rup c ls =>
    (case neg_slot c b of (nc,mv) =>
      case check_rup_arr lno b nc (mv + 1) fml assg st ls of (assg,st) =>
        (fml, (Some(c,b), (id, (assg, st)))))
  | Con c pf n =>
    (case opt_update_neg_arr fml c b id assg st of
      (fml_not_c,(id',(assg,st))) =>
      (case check_lsteps_arr lno pf b fml_not_c id id' assg st of
        (fml', (id', (assg, st))) =>
          if check_contradiction_fml_arr b fml' n then
            let val u = rollback_arr fml' id id' in
              (fml', (Some (c,b), (id', (assg, st))))
            end
          else
            raise Fail (format_failure lno ("subproof did not derive contradiction from index: " ^ Int.toString n))))
  | _ => raise Fail (format_failure lno ("proof step not supported"))
  and check_lsteps_arr lno steps b fml mindel id assg st =
  case steps of
    [] => (fml, (id, (assg, st)))
  | s::ss =>
    (case check_lstep_arr lno s b fml mindel id assg st of
      (fml', (c, (id', (assg, st)))) =>
        (case opt_update_arr fml' c id' assg st of
          (fml'', (id'', (assg, st))) =>
        check_lsteps_arr lno ss b fml'' mindel id'' assg st))
End

val NPBC_CHECK_LSTEP_TYPE_def = fetch "-" "NPBC_CHECK_LSTEP_TYPE_def";

Theorem check_lstep_arr_spec_aux:
  (∀step b fmlls mindel id assg st stepv lno lnov idv fmlv fmllsv mindelv bv
    assgv stv.
  NPBC_CHECK_LSTEP_TYPE step stepv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lstep_arr" (get_ml_prog_state()))
    [lnov; stepv; bv; fmlv; mindelv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          case check_lstep_list step b fmlls mindel id assg st of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (OPTION_TYPE bconstraint_TYPE)
              (PAIR_TYPE NUM
                (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        & (Fail_exn e ∧
        check_lstep_list step b fmlls mindel id assg st = NONE)))) ∧
  (∀steps b fmlls mindel id assg st stepsv lno lnov idv fmlv fmllsv mindelv bv
    assgv stv.
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE steps stepsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; bv; fmlv; mindelv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          case check_lsteps_list steps b fmlls mindel id assg st of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE NUM
                (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM)) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        & (Fail_exn e ∧
          check_lsteps_list steps b fmlls mindel id assg st = NONE))))
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
      gvs[delete_ids_list_eq]>>
      reverse IF_CASES_TAC >>
      gs[]>>xif>>
      asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_lstep_list_def]>>
        xraise>>xsimpl>>
        simp[Fail_exn_def]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      simp[check_lstep_list_def])
    >- ( (* Cutting *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_autop>>
      xlet_autop >- (
        xsimpl>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      rpt xlet_autop>>
      every_case_tac>>fs[]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
      metis_tac[ARRAY_NUM_ARRAY_refl])
    >- ( (* Rup *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def,neg_slot_enc]>>
      xmatch>>
      xlet_autop>>
      gvs[neg_slot_enc,PAIR_TYPE_def]>>
      xmatch>>
      xlet_autop>>
      rpt (pairarg_tac>>gvs[])>>
      drule_at (Pos last) check_rup_list_pre>>
      impl_tac >- (
        imp_res_tac LIST_REL_fslot_TYPE_wf>>
        simp[]>>
        metis_tac[slot_bound_enc_max_var,max_var_not])>>
      strip_tac>>gvs[]>>
      xlet`POSTve
        (λv. ARRAY fmlv fmllsv * SEP_EXISTS av. NUM_ARRAY av assg' *
          &(res ∧ PAIR_TYPE $= NUM (av,st') v))
        (λe. ARRAY fmlv fmllsv * SEP_EXISTS av. NUM_ARRAY av assg' *
          &(Fail_exn e ∧ ¬res))`
      >- (
        xapp>>xsimpl>>
        conj_tac >- metis_tac[]>>
        qexistsl_tac[`b`,`fmlls`,`enc (not p') b`,`l`,`st`,`max_var (FST p') + 1`]>>
        simp[fslot_TYPE_def])
      >- (
        xsimpl>>
        rw[]>>
        qexistsl_tac[`fmlv`,`fmllsv`,`x`,`assg'`]>>
        xsimpl)>>
      gvs[PAIR_TYPE_def]>>
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[OPTION_TYPE_def,PAIR_TYPE_def])
    >- ( (* Con *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt (pairarg_tac>>gvs[])>>
      xlet`POSTv v. SEP_EXISTS fmlv1 fmllsv1 assgv1.
        ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg' *
        &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg' ∧ v = assgv1) NUM))
          (fml_not_c,id',assg',st') v`
      >- (
        xapp>>xsimpl>>
        qexistsl_tac[`emp`,`st`,`id`,`fmlls`,`p'`,`b`,`assg`]>>
        simp[]>>
        xsimpl>>
        rw[]>>
        gvs[PAIR_TYPE_def]>>
        xsimpl)>>
      gvs[PAIR_TYPE_def]>>
      xmatch>>
      drule_all fml_bound_opt_update>>
      strip_tac>>
      xlet_auto
      >- (
        xsimpl>>
        metis_tac[ARRAY_NUM_ARRAY_refl])
      >- (
        xsimpl>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      pop_assum mp_tac>> TOP_CASE_TAC>>
      fs[]>>
      PairCases_on`x`>>fs[PAIR_TYPE_def]>>
      rw[]
      >- (
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
      metis_tac[Fail_exn_def,ARRAY_NUM_ARRAY_refl])
    >- ( (* ImplyAdd *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_autop >- (
        xsimpl>>
        rw[]>>gvs[]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      Cases_on`lookup_core_only_list b fmlls n`>>gvs[]>>
      rename1`lookup_core_only_list b fmlls n = Stored cs vs d mc sm cb`>>
      xlet`POSTv bv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        &BOOL (imp_slot (Stored cs vs d mc sm cb) p') bv`
      >- (
        xapp>>xsimpl>>
        gvs[fslot_TYPE_def]>>
        qexistsl_tac[`p'`,`Stored cs vs d mc sm cb`]>>
        simp[imp_slot_side])>>
      xif
      >- (
        rpt xlet_autop>>
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      xlet`POSTv cv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        &constraint_TYPE (dec (Stored cs vs d mc sm cb)) cv`
      >- (
        xapp>>xsimpl>>
        gvs[fslot_TYPE_def]>>
        qexists_tac`Stored cs vs d mc sm cb`>>
        simp[dec_side])>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_NUM_ARRAY_refl])
    >- ( (* Check *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_autop >- (
        xsimpl>>
        rw[]>>gvs[]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      Cases_on`lookup_core_only_list b fmlls n`>>gvs[]>>
      rename1`lookup_core_only_list b fmlls n = Stored cs vs d mc sm cb`>>
      xlet`POSTv bv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        &BOOL (eq_slot p' (Stored cs vs d mc sm cb)) bv`
      >- (
        xapp>>xsimpl>>
        gvs[fslot_TYPE_def]>>
        qexistsl_tac[`p'`,`Stored cs vs d mc sm cb`]>>
        simp[eq_slot_side])>>
      xif
      >- (
        rpt xlet_autop>>
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      xlet`POSTv cv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        &constraint_TYPE (dec (Stored cs vs d mc sm cb)) cv`
      >- (
        xapp>>xsimpl>>
        gvs[fslot_TYPE_def]>>
        qexists_tac`Stored cs vs d mc sm cb`>>
        simp[dec_side])>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_NUM_ARRAY_refl])
    >- ( (* NoOp *)
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
      metis_tac[ARRAY_NUM_ARRAY_refl])
    >- (
      xsimpl>>
      rw[]>>simp[Once check_lstep_list_def]>>
      metis_tac[ARRAY_NUM_ARRAY_refl])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
    PairCases_on`x`>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    drule_all (CONJUNCT1 fml_bound_check_lstep_list)>>
    strip_tac>>
    `∃f1 i1 a1 s1. opt_update x0 x1 x2 assg' x4 = (f1,i1,a1,s1)` by
      metis_tac[PAIR]>>
    drule_all fml_bound_opt_update>>
    strip_tac>>
    xlet`POSTv v. SEP_EXISTS fmlv2 fmllsv2 assgv2.
      ARRAY fmlv2 fmllsv2 * NUM_ARRAY assgv2 a1 *
      &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv2 ∧ v = fmlv2)
        (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = a1 ∧ v = assgv2) NUM))
        (f1,i1,a1,s1) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`emp`,`x4`,`x2`,`x0`,`x1`,`assg'`]>>
      simp[]>>
      xsimpl>>
      rw[]>>
      gvs[PAIR_TYPE_def]>>
      xsimpl)>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    qexists_tac`lno`>>
    simp[Once check_lstep_list_def]>>
    rw[]
    >- (
      every_case_tac>>fs[]>>
      asm_exists_tac>>xsimpl)>>
    simp[Once check_lstep_list_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])
QED
Theorem check_lstep_arr_spec = CONJUNCT1 check_lstep_arr_spec_aux
Theorem check_lsteps_arr_spec = CONJUNCT2 check_lstep_arr_spec_aux

Quote add_cakeml:
  fun reindex_aux_arr fml ls iacc =
  case ls of
    [] => (List.rev iacc)
  | (i::is) =>
  case Array.lookup fml Empty i of
    Empty => reindex_aux_arr fml is iacc
  | _ =>
      reindex_aux_arr fml is (i::iacc)
End

Quote add_cakeml:
  fun reindex_arr fml is =
    reindex_aux_arr fml is []
End

Theorem reindex_aux_arr_spec:
  ∀inds indsv fmlls fmlv iacc iaccv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
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
  `fslot_TYPE (any_el h fmlls Empty) v'` by (
    gvs[]>>
    irule LIST_REL_fslot_TYPE_any_el>>
    gvs[SLOT_TYPE_def])>>
  rw[]>>
  simp[reindex_aux_def]>>
  Cases_on`any_el h fmlls Empty`>>gvs[fslot_TYPE_def,SLOT_TYPE_def]
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
  LIST_REL fslot_TYPE fmlls fmllsv ∧
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

(*
Quote add_cakeml:
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
        (mk_vacc b b' v vacc)
End

Quote add_cakeml:
  fun reindex_partial_arr b fml mini is =
  case mini of None => ([], ([], is))
  | Some mini =>
    reindex_partial_aux_arr b fml mini is [] []
End

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

val _ = register_type ``:'a lmap``;
val res = translate spt_to_vecTheory.bsearch_def;

Theorem bsearch_side[local]:
  ∀v n lo hi. hi ≤ length v ⇒ bsearch_side v n lo hi
Proof
  recInduct spt_to_vecTheory.bsearch_ind \\ rw []
  \\ simp [Once (fetch "-" "bsearch_side_def")]
  \\ strip_tac
  \\ ‘(hi + lo) DIV 2 < hi’ by simp [DIV_LT_X]
  \\ rw []
QED

val res = translate spt_to_vecTheory.map_lookup_def;

Theorem map_lookup_side[local]:
  map_lookup_side m n
Proof
  rw [fetch "-" "map_lookup_side_def"] \\ simp [bsearch_side]
QED

val _ = map_lookup_side |> update_precondition;

val res = translate npbc_checkTheory.subst_fun_def;

val res = translate subst_fun_slot_def;

Theorem subst_fun_slot_side[local]:
  subst_fun_slot_side s n
Proof
  rw [fetch "-" "subst_fun_slot_side_def"] \\ simp [bsearch_side]
QED

val _ = subst_fun_slot_side |> update_precondition;

val res = translate subst_aux_slot_def;
val res = translate subst_same_slot_def;
val res = translate subst_slot_def;
val res = translate subst_opt_slot_def;

Theorem subst_aux_slot_side[local]:
  ∀i f cs vs old new k.
  i ≤ length cs ∧ i ≤ length vs ⇒
  subst_aux_slot_side f cs vs i old new k
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "subst_aux_slot_side_def")]
QED

Theorem subst_same_slot_side[local]:
  ∀s cs vs i len.
  len ≤ length cs ∧ len ≤ length vs ⇒
  subst_same_slot_side s cs vs i len
Proof
  ho_match_mp_tac subst_same_slot_ind>>
  rw[]>>
  simp[Once (fetch "-" "subst_same_slot_side_def")]
QED

Theorem subst_slot_side:
  wf_slot s ⇒ subst_slot_side f s
Proof
  Cases_on`s`>>
  rw[fetch "-" "subst_slot_side_def",wf_slot_def]>>
  irule subst_aux_slot_side>>
  simp[]
QED

Theorem subst_opt_slot_side:
  wf_slot s ⇒ subst_opt_slot_side f s
Proof
  Cases_on`s`>>
  rw[fetch "-" "subst_opt_slot_side_def",wf_slot_def]>>
  metis_tac[subst_same_slot_side,subst_slot_side,imp_slot_side,
    wf_slot_def,LESS_EQ_REFL]
QED

Quote add_cakeml:
  fun extract_clauses_arr lno s b fml rsubs pfs acc =
  case pfs of [] => List.rev acc
  | cpf::pfs =>
    case cpf of
      (None,pf) =>
        extract_clauses_arr lno s b fml rsubs pfs ((None,pf)::acc)
    | (Some (Inl n,i),pf) =>
      let val c = lookup_core_only_err_arr lno b fml n in
        extract_clauses_arr lno s b fml rsubs pfs ((Some ([not_1(subst_slot s c)],i),pf)::acc)
      end
    | (Some (Inr u,i),pf) =>
      if u < List.length rsubs then
        extract_clauses_arr lno s b fml rsubs pfs ((Some (List.nth rsubs u,i),pf)::acc)
      else raise Fail (format_failure lno ("invalid #proofgoal id: " ^ Int.toString u))
End

Overload "subst_TYPE" = ``SPT_TO_VEC_LMAP_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))``

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
  LIST_REL fslot_TYPE fmlls fmllsv
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
    Cases_on`lookup_core_only_list b fmlls x`>>gvs[]>>
    rename1`lookup_core_only_list b fmlls x = Stored cs vs d mc sm cb`>>
    xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv *
      &constraint_TYPE (subst_slot s (Stored cs vs d mc sm cb)) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`Stored cs vs d mc sm cb`,`s`]>>
      gvs[fslot_TYPE_def,subst_slot_side])>>
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

Theorem el_side[local]:
  ∀xs n.
  n < LENGTH xs ⇒
  el_side n xs
Proof
  Induct>>
  rw[Once (fetch "-" "el_side_def")]
QED

val _ = el_side |> update_precondition;

Theorem mk_scope_side[local]:
  mk_scope_side x y
Proof
  EVAL_TAC>>rw[]>>
  metis_tac[el_side]
QED
val _ = mk_scope_side |> update_precondition;

Quote add_cakeml:
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
    end
End

Theorem extract_scopes_arr_spec:
  ∀pfs pfsv s sv b bv fmlls fmlv fmllsv
    rsubs rsubsv lno lnov.
  NUM lno lnov ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) scopes scopesv ∧
  subst_TYPE s sv ∧
  BOOL b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  scpfs_TYPE pfs pfsv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
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

Quote add_cakeml:
  fun subst_indexes_arr s b fml is =
  case is of [] => []
  | (i::is) =>
    case subst_opt_slot s (lookup_core_only_arr b fml i) of
      None => subst_indexes_arr s b fml is
    | Some c => (i,c)::subst_indexes_arr s b fml is
End

Theorem subst_indexes_arr_spec:
  ∀is isv s sv b bv fmlls fmllsv fmlv.
  subst_TYPE s sv ∧
  BOOL b bv ∧
  LIST_TYPE NUM is isv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
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
  xlet`POSTv v. ARRAY fmlv fmllsv *
    &OPTION_TYPE constraint_TYPE
      (subst_opt_slot s (lookup_core_only_list b fmlls h)) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`lookup_core_only_list b fmlls h`,`s`]>>
    gvs[fslot_TYPE_def,subst_opt_slot_side])>>
  simp[subst_indexes_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xapp>>
    metis_tac[])>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[LIST_TYPE_def,PAIR_TYPE_def]
QED

Quote add_cakeml:
  fun list_insert_fml_arr ls b id fml assg st =
    case ls of
      [] => (id,(fml,(assg,st)))
    | (c::cs) =>
      (case enc_mv c b of (s,mv) =>
      case store_slot_arr fml s mv id assg st of
        (fml',(id',(assg',st'))) =>
        list_insert_fml_arr cs b id' fml' assg' st')
End

Theorem list_insert_fml_arr_spec:
  ∀ls lsv b bv fmlv fmlls fmllsv id idv assg assgv st stv.
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  BOOL b bv ∧
  NUM id idv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_insert_fml_arr" (get_ml_prog_state()))
    [lsv; bv; idv; fmlv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTv resv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      &(PAIR_TYPE NUM
          (PAIR_TYPE
            (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))
          (list_insert_fml_list ls b id fmlls assg st) resv))
Proof
  Induct>>
  rw[]>>simp[list_insert_fml_list_def]>>
  xcf "list_insert_fml_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac[`fmlv`,`fmllsv`,`assgv`,`assg`]>>
    simp[PAIR_TYPE_def]>>
    xsimpl)>>
  xmatch>>
  xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def]>>
  xmatch>>
  `∃f1 i1 a1 s1.
    store_slot fmlls (enc h b) (max_var (FST h)) id assg st = (f1,i1,a1,s1)` by
    metis_tac[PAIR]>>
  xlet`POSTv v. SEP_EXISTS fmlv1 fmllsv1 assgv1.
    ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 a1 *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
      (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = a1 ∧ v = assgv1) NUM))
      (f1,i1,a1,s1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`st`,`enc h b`,`max_var (FST h)`,`id`,`fmlls`,`assg`]>>
    simp[fslot_TYPE_def]>>
    xsimpl>>
    rw[]>>
    gvs[PAIR_TYPE_def]>>
    xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xapp>>
  gvs[opt_update_def,enc_mv_enc]>>
  qexistsl_tac[`emp`,`s1`,`i1`,`fmllsv1`,`f1`,`b`,`a1`]>>
  simp[]>>
  xsimpl
QED

Quote add_cakeml:
  fun check_subproofs_arr lno pfs b fml mindel id assg st =
  case pfs of
    [] => (fml,(id,(assg,st)))
  | (cnopt,pf)::pfs =>
    (case cnopt of
      None =>
      (case check_lsteps_arr lno pf b fml mindel id assg st of
        (fml', (id', (assg', st'))) =>
        check_subproofs_arr lno pfs b fml' mindel id' assg' st')
    | Some (cs,n) =>
      case list_insert_fml_arr cs b id fml assg st of
        (cid, (cfml, (assg, st))) =>
        (case check_lsteps_arr lno pf b cfml id cid assg st of
          (fml', (id', (assg', st'))) =>
          if check_contradiction_fml_arr b fml' n then
          let val u = rollback_arr fml' id id' in
            check_subproofs_arr lno pfs b fml' mindel id' assg' st'
          end
          else
            raise Fail (format_failure lno ("subproof did not derive contradiction from index: " ^ Int.toString n))))
End

Theorem check_subproofs_arr_spec:
  ∀pfs fmlls mindel id assg st pfsv lno lnov idv fmlv fmllsv mindelv b bv
    assgv stv.
  check_subproof_TYPE pfs pfsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_subproofs_arr" (get_ml_prog_state()))
    [lnov; pfsv; bv; fmlv; mindelv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
        case check_subproofs_list pfs b fmlls mindel id assg st of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))
            res v
        ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        & (Fail_exn e ∧
          check_subproofs_list pfs b fmlls mindel id assg st = NONE)))
Proof
  Induct>>
  rw[]>>simp[check_subproofs_list_def]>>
  xcf "check_subproofs_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac[`fmlv`,`fmllsv`,`assgv`,`assg`]>>
    simp[PAIR_TYPE_def]>>
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
      metis_tac[ARRAY_NUM_ARRAY_refl])
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_NUM_ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    drule_all (CONJUNCT2 fml_bound_check_lstep_list)>>
    strip_tac>>
    xmatch>>
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`x3`,`mindel`,`x1`,`x0`,`b`,`assg'`,`lno`]>>
    simp[]>>
    xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  `∃cid cfml assg1 st1.
    list_insert_fml_list q b id fmlls assg st = (cid,cfml,assg1,st1)` by
    metis_tac[PAIR]>>
  drule_all fml_bound_list_insert_fml_list>>
  strip_tac>>
  xlet`POSTv v. SEP_EXISTS fmlv1 fmllsv1 assgv1.
    ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg1 *
    &PAIR_TYPE NUM
      (PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
        (PAIR_TYPE (λl v. l = assg1 ∧ v = assgv1) NUM))
      (cid,cfml,assg1,st1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`st`,`q`,`id`,`fmlls`,`b`,`assg`]>>
    simp[]>>
    xsimpl>>
    rw[]>>gvs[PAIR_TYPE_def]>>
    xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x`>>simp[PAIR_TYPE_def]>>
  strip_tac>>xmatch>>
  xlet_autop>>
  reverse xif>> xsimpl
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_NUM_ARRAY_refl])>>
  drule_all (CONJUNCT2 fml_bound_check_lstep_list)>>
  strip_tac>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[bound_rollback]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun check_scopes_arr lno pfs b fml mindel id assg st =
  case pfs of
    [] => (fml,(id,(assg,st)))
  | (scopt,pf)::pfs =>
    (case scopt of
      None =>
      (case check_subproofs_arr lno pf b fml mindel id assg st of
        (fml', (id', (assg', st'))) =>
        check_scopes_arr lno pfs b fml' mindel id' assg' st')
    | Some sc =>
      case list_insert_fml_arr sc b id fml assg st of
        (cid, (cfml, (assg, st))) =>
        (case check_subproofs_arr lno pf b cfml id cid assg st of
          (fml', (id', (assg', st'))) =>
          let val u = rollback_arr fml' id id' in
            check_scopes_arr lno pfs b fml' mindel id' assg' st'
          end))
End

Theorem check_scopes_arr_spec:
  ∀pfs fmlls mindel id assg st pfsv lno lnov idv fmlv fmllsv mindelv b bv
    assgv stv.
  check_scope_TYPE pfs pfsv ∧
  BOOL b bv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_scopes_arr" (get_ml_prog_state()))
    [lnov; pfsv; bv; fmlv; mindelv; idv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
        case check_scopes_list pfs b fmlls mindel id assg st of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))
            res v
        ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        & (Fail_exn e ∧
          check_scopes_list pfs b fmlls mindel id assg st = NONE)))
Proof
  Induct>>
  rw[]>>simp[check_scopes_list_def]>>
  xcf "check_scopes_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac[`fmlv`,`fmllsv`,`assgv`,`assg`]>>
    simp[PAIR_TYPE_def]>>
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
      metis_tac[ARRAY_NUM_ARRAY_refl])
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_NUM_ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    drule_all fml_bound_check_subproofs_list>>
    strip_tac>>
    xmatch>>
    xapp>>
    xsimpl>>
    qexistsl_tac[`emp`,`x3`,`mindel`,`x1`,`x0`,`b`,`assg'`,`lno`]>>
    simp[]>>
    xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xmatch>>
  `∃cid cfml assg1 st1.
    list_insert_fml_list x b id fmlls assg st = (cid,cfml,assg1,st1)` by
    metis_tac[PAIR]>>
  drule_all fml_bound_list_insert_fml_list>>
  strip_tac>>
  xlet`POSTv v. SEP_EXISTS fmlv1 fmllsv1 assgv1.
    ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg1 *
    &PAIR_TYPE NUM
      (PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
        (PAIR_TYPE (λl v. l = assg1 ∧ v = assgv1) NUM))
      (cid,cfml,assg1,st1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`st`,`x`,`id`,`fmlls`,`b`,`assg`]>>
    simp[]>>
    xsimpl>>
    rw[]>>gvs[PAIR_TYPE_def]>>
    xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  rename1`_ = SOME yy`>>
  PairCases_on`yy`>>simp[PAIR_TYPE_def]>>
  strip_tac>>xmatch>>
  drule_all fml_bound_check_subproofs_list>>
  strip_tac>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  gvs[bound_rollback]>>
  metis_tac[]
QED

val res = translate npbc_checkTheory.extract_pids_def;

val res = translate npbc_checkTheory.list_list_insert_def;
val res = translate npbcTheory.mk_lit_def;
val res = translate npbcTheory.mk_bit_lit_def;
val res = translate spt_to_vecTheory.vec_lookup_def;
val res = translate npbc_checkTheory.dom_subst_def;

val res = translate obj_single_aux_def;
val res = translate obj_single_def;
val res = translate full_obj_single_def;

val res = translate fast_obj_constraint_def;
val res = translate fast_red_subgoals_def;

Theorem fast_red_subgoals_side:
  wf_slot fc ⇒ fast_red_subgoals_side ord s sr fc obj vomap hs
Proof
  rw[fetch "-" "fast_red_subgoals_side_def",subst_slot_side]
QED

val res = translate npbc_checkTheory.list_pair_eq_def;
val res = translate npbc_checkTheory.equal_constraint_def;
val res = translate npbc_checkTheory.mem_constraint_def;

Definition lookup_hash_imp_def:
  lookup_hash_imp r c skipped (id,cs) =
  case sptree$lookup id r of
    NONE => check_hash_imp c cs ∨ MEM id skipped
  | SOME _ => T
End

Theorem check_hash_goals_eq:
  check_hash_goals c skipped r rsubs =
  EVERY (lookup_hash_imp r c skipped)
    (enumerate 0 rsubs)
Proof
  rw[npbc_checkTheory.check_hash_goals_def]>>
  irule EVERY_CONG >>rw[]>>
  rw[FUN_EQ_THM]>>
  pairarg_tac>>fs[lookup_hash_imp_def]>>
  every_case_tac>>gvs[]
QED

val res = translate npbc_checkTheory.check_hash_imp_def;
val res = translate miscTheory.enumerate_def;
val res = translate (lookup_hash_imp_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate check_hash_goals_eq;

val res = translate (lookup_hash_imp_slot_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate check_hash_goals_slot_def;

Theorem check_hash_goals_slot_side:
  wf_slot nfc ⇒ check_hash_goals_slot_side nfc skipped r rsubs
Proof
  rw[fetch "-" "check_hash_goals_slot_side_def",
    fetch "-" "lookup_hash_imp_slot_side_def",imp_slot_side]
QED

val hash_simps = [h_base_def, h_base_sq_def, h_mod_def];

val res = translate (hash_term_def |> REWRITE_RULE hash_simps);

Theorem hash_term_side[local]:
  hash_term_side i n
Proof
  rw[Once (fetch "-" "hash_term_side_def")]>>
  intLib.ARITH_TAC
QED

val _ = hash_term_side |> update_precondition;

val res = translate (hash_list_def |> REWRITE_RULE hash_simps);

Theorem hash_list_ind_thm[local]:
  hash_list_ind
Proof
  rw[fetch "-" "hash_list_ind_def"]>>
  qid_spec_tac`v5`>>
  Induct_on`v6`>>
  rw[]
QED

val _ = hash_list_ind_thm |> update_precondition;

val res = translate (hash_constraint_def |> REWRITE_RULE hash_simps);
val res = translate (hash_terms_slot_def |> REWRITE_RULE hash_simps);

Theorem hash_terms_slot_ind_thm[local]:
  hash_terms_slot_ind
Proof
  rw[fetch "-" "hash_terms_slot_ind_def"]>>
  `∀k v2 v5 v4 v3 v1. v4 - v3 = k ⇒ P v2 v5 v4 v3 v1`
    suffices_by metis_tac[]>>
  Induct>>
  rw[]
QED

val _ = hash_terms_slot_ind_thm |> update_precondition;

val res = translate (hash_slot_def |> REWRITE_RULE hash_simps);

Theorem hash_terms_slot_side[local]:
  ∀k cs vs n i acc.
  n - i = k ∧ n ≤ length cs ∧ n ≤ length vs ⇒
  hash_terms_slot_side cs vs n i acc
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "hash_terms_slot_side_def")]
QED

Theorem hash_slot_side:
  wf_slot s ⇒ hash_slot_side s
Proof
  Cases_on`s`>>
  rw[fetch "-" "hash_slot_side_def",wf_slot_def]>>
  irule hash_terms_slot_side>>
  simp[]
QED

(* The table (hw,a,d,tbl); its places are in an array *)
Definition ht_TYPE_def:
  ht_TYPE bksv bkslsv (ht:num # num # num # num list) v ⇔
  PAIR_TYPE NUM (PAIR_TYPE NUM (PAIR_TYPE NUM
    (λl v. LIST_REL NUM l bkslsv ∧ v = bksv))) ht v
End

val res = translate ht_next_def;

Quote add_cakeml:
  fun ht_put_arr i tbl j fuel =
  if fuel = 0 then ()
  else if Unsafe.sub tbl j = 0 then Unsafe.update tbl j i
  else ht_put_arr i tbl (ht_next (Array.length tbl) j) (fuel - 1)
End

Theorem ht_put_arr_spec:
  ∀fuel fuelv j jv tbllsv.
  NUM i iv ∧ NUM j jv ∧ NUM fuel fuelv ∧
  LIST_REL NUM tbl tbllsv ∧ j < LENGTH tbl
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_put_arr" (get_ml_prog_state()))
    [iv; tblv; jv; fuelv]
    (ARRAY tblv tbllsv)
    (POSTv v.
      SEP_EXISTS tbllsv'. ARRAY tblv tbllsv' *
      &(UNIT_TYPE () v ∧ LIST_REL NUM (ht_put i tbl j fuel) tbllsv'))
Proof
  Induct>>
  rw[]>>
  xcf "ht_put_arr" (get_ml_prog_state ())>>
  simp[Once ht_put_def]
  >- (
    xlet_autop>>
    xif>>
    qexists_tac`T`>>simp[]>>
    xcon>>xsimpl)>>
  xlet_autop>>
  xif>>
  qexists_tac`F`>>simp[]>>
  imp_res_tac LIST_REL_LENGTH>>
  `NUM (EL j tbl) (EL j tbllsv)` by fs[LIST_REL_EL_EQN]>>
  xlet`POSTv v. ARRAY tblv tbllsv * &(v = EL j tbllsv)`
  >- (
    xapp_spec UnsafeProofTheory.unsafe_array_sub_spec>>
    xsimpl>>
    metis_tac[])>>
  xlet_autop>>
  xif
  >- (
    xapp_spec UnsafeProofTheory.unsafe_array_update_spec>>
    xsimpl>>
    qexists_tac`j`>>
    simp[EVERY2_LUPDATE_same])>>
  rpt xlet_autop>>
  xapp>>
  gvs[ht_next_def]
QED

Quote add_cakeml:
  fun ht_mem_arr b fml c tbl j fuel =
  if fuel = 0 then False
  else
    let val i = Unsafe.sub tbl j in
      if i = 0 then False
      else
        (case lookup_core_only_arr b fml i of
          Empty => False
        | s => eq_slot c s) orelse
        ht_mem_arr b fml c tbl (ht_next (Array.length tbl) j) (fuel - 1)
    end
End

Theorem ht_mem_arr_spec:
  ∀fuel fuelv j jv.
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  constraint_TYPE c cv ∧
  NUM j jv ∧ NUM fuel fuelv ∧
  LIST_REL NUM tbl tbllsv ∧ j < LENGTH tbl
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_mem_arr" (get_ml_prog_state()))
    [bv; fmlv; cv; tblv; jv; fuelv]
    (ARRAY fmlv fmllsv * ARRAY tblv tbllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
      &BOOL (ht_mem b fmlls c tbl j fuel) v)
Proof
  Induct>>
  rw[]>>
  xcf "ht_mem_arr" (get_ml_prog_state ())>>
  simp[Once ht_mem_def]
  >- (
    xlet_autop>>
    xif>>
    qexists_tac`T`>>simp[]>>
    xcon>>xsimpl)>>
  xlet_autop>>
  xif>>
  qexists_tac`F`>>simp[]>>
  imp_res_tac LIST_REL_LENGTH>>
  `NUM (EL j tbl) (EL j tbllsv)` by fs[LIST_REL_EL_EQN]>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv * &(v = EL j tbllsv)`
  >- (
    xapp_spec UnsafeProofTheory.unsafe_array_sub_spec>>
    xsimpl>>
    metis_tac[])>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl)>>
  xlet_autop>>
  qpat_x_assum`fslot_TYPE (lookup_core_only_list _ _ _) _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  qabbrev_tac`s = lookup_core_only_list b fmlls (EL j tbl)`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    &BOOL (case s of Empty => F
      | Stored a1 a2 a3 a4 a5 a6 => eq_slot c (Stored a1 a2 a3 a4 a5 a6)) v`
  >- (
    Cases_on`s`>>
    gvs[SLOT_TYPE_def]>>
    xmatch
    >- (
      xcon>>xsimpl)>>
    rename1`lookup_core_only_list b fmlls _ = Stored cs vs d mc sm cb`>>
    xapp>>xsimpl>>
    qexistsl_tac[`c`,`Stored cs vs d mc sm cb`]>>
    simp[SLOT_TYPE_def,eq_slot_side])>>
  xlog>>
  xsimpl>>
  rw[]
  >- gvs[]>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  qexists_tac`ht_next (LENGTH tbllsv) j`>>
  rw[ht_next_def]
QED

Quote add_cakeml:
  fun ht_count_arr fml hw inds n =
  case inds of [] => n
  | i::is =>
    if i < hw then n
    else
      (case Array.lookup fml Empty i of
        Empty => ht_count_arr fml hw is n
      | _ => ht_count_arr fml hw is (n+1))
End

Theorem ht_count_arr_spec:
  ∀inds indsv n nv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM hw hwv ∧
  LIST_TYPE NUM inds indsv ∧
  NUM n nv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_count_arr" (get_ml_prog_state()))
    [fmlv; hwv; indsv; nv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &NUM (ht_count fmlls hw inds n) v)
Proof
  Induct>>
  rw[]>>
  xcf "ht_count_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,ht_count_def]>>
  xmatch
  >- (
    xvar>>xsimpl)>>
  xlet_autop>>
  xif
  >- (
    xvar>>xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto>>
  `fslot_TYPE (any_el h fmlls Empty) v'` by (
    gvs[]>>
    irule LIST_REL_fslot_TYPE_any_el>>
    gvs[SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  xmatch>>
  xlet_autop>>
  xapp>>simp[]
QED

(* As ht_insert; returns k plus the number of ids put *)
Quote add_cakeml:
  fun ht_insert_arr fml hw inds tbl k =
  case inds of [] => k
  | i::is =>
    if i < hw then k
    else
      (case Array.lookup fml Empty i of
        Empty => ht_insert_arr fml hw is tbl k
      | s =>
        let val n = Array.length tbl in
          (ht_put_arr i tbl (hash_slot s mod n) n;
           ht_insert_arr fml hw is tbl (k + 1))
        end)
End

Theorem ht_insert_arr_spec:
  ∀inds indsv tbl tbllsv k kv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM hw hwv ∧
  LIST_TYPE NUM inds indsv ∧
  tbl ≠ [] ∧
  LIST_REL NUM tbl tbllsv ∧
  NUM k kv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_insert_arr" (get_ml_prog_state()))
    [fmlv; hwv; indsv; tblv; kv]
    (ARRAY fmlv fmllsv * ARRAY tblv tbllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      SEP_EXISTS tbllsv'.
      ARRAY tblv tbllsv' *
      &(NUM (ht_count fmlls hw inds k) v ∧
        LIST_REL NUM (ht_insert fmlls hw inds tbl) tbllsv'))
Proof
  Induct>>
  rw[]>>
  xcf "ht_insert_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,ht_insert_def,ht_count_def]>>
  xmatch
  >- (
    xvar>>xsimpl)>>
  xlet_autop>>
  xif
  >- (
    xvar>>xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto >- xsimpl>>
  `fslot_TYPE (any_el h fmlls Empty) v'` by (
    gvs[]>>
    irule LIST_REL_fslot_TYPE_any_el>>
    gvs[SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  rename1`any_el h fmlls Empty = Stored cs vs d mc sm cb`>>
  imp_res_tac LIST_REL_LENGTH>>
  `LENGTH tbl ≠ 0` by (
    Cases_on`tbl`>>gvs[])>>
  qabbrev_tac`j = hash_slot (Stored cs vs d mc sm cb) MOD LENGTH tbl`>>
  `j < LENGTH tbl` by simp[Abbr`j`]>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    &NUM (hash_slot (Stored cs vs d mc sm cb)) v`
  >- (
    xapp>>xsimpl>>
    qexists_tac`Stored cs vs d mc sm cb`>>
    gvs[SLOT_TYPE_def,hash_slot_side])>>
  xlet_auto >- (xsimpl>>Cases_on`tbllsv`>>gvs[])>>
  `NUM j iv` by (
    simp[Abbr`j`]>>
    metis_tac[NUM_def,integerTheory.INT_MOD])>>
  xlet`POSTv u. ARRAY fmlv fmllsv * SEP_EXISTS tbllsv1. ARRAY tblv tbllsv1 *
    &LIST_REL NUM (ht_put h tbl j (LENGTH tbl)) tbllsv1`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`tbl`,`j`,`h`,`LENGTH tbl`]>>
    gvs[])>>
  xlet_autop>>
  xapp>>
  rw[]>>
  metis_tac[LENGTH_ht_put,LENGTH_NIL]
QED

(* With no table, or when the new ids would fill more than three quarters
  of its places, a new table replaces the old one *)
Quote add_cakeml:
  fun ht_fill_arr fml inds base ht =
  case ht of (hw,(a,(d,tbl))) =>
  let
    val new = ht_count_arr fml hw inds 0
    val n = Array.length tbl
  in
    if n = 0 orelse 3 * n < 4 * (a + new) then
      let
        val live = (if a < d then 0 else a - d) + new
        val tbl = Array.array (if live = 0 then 1 else 2 * live) 0
        val a' = ht_insert_arr fml 0 inds tbl 0
      in
        (base,(a',(0,tbl)))
      end
    else
      (ht_insert_arr fml hw inds tbl 0; (base,(a + new,(d,tbl))))
  end
End

Theorem ht_fill_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv ∧
  NUM base basev ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_fill_arr" (get_ml_prog_state()))
    [fmlv; indsv; basev; htv]
    (ARRAY fmlv fmllsv * ARRAY bksv bkslsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      SEP_EXISTS bksv' bkslsv'.
      ARRAY bksv' bkslsv' *
      &(ht_TYPE bksv' bkslsv' (ht_fill fmlls inds base ht) v ∧
        SND (SND (SND (ht_fill fmlls inds base ht))) ≠ []))
Proof
  rw[]>>
  PairCases_on`ht`>>
  gvs[ht_TYPE_def,PAIR_TYPE_def,ht_fill_def]>>
  xcf "ht_fill_arr" (get_ml_prog_state ())>>
  xmatch>>
  xlet_autop>>
  imp_res_tac LIST_REL_LENGTH>>
  qabbrev_tac`new = ht_count fmlls ht0 inds 0`>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv bkslsv *
    &BOOL (ht3 = [] ∨ 3 * LENGTH ht3 < 4 * (ht1 + new)) v`
  >- (
    xlog>>
    xsimpl>>
    IF_CASES_TAC
    >- gvs[]>>
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    qexistsl_tac[`&(4 * (ht1 + new))`,`&(3 * LENGTH bkslsv)`]>>
    `ht3 ≠ []` by (strip_tac>>gvs[])>>
    gvs[NUM_def,Abbr`new`])>>
  xif
  >- (
    qpat_x_assum`ht3 = [] ∨ _` kall_tac>>
    xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv bkslsv * &NUM (ht1 − ht2) v`
    >- (
      xif
      >- (
        xlit>>xsimpl)>>
      xapp>>xsimpl>>
      qexistsl_tac[`&ht2`,`&ht1`]>>
      fs[NUM_def,integerTheory.INT_SUB])>>
    xlet_autop>>
    xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv bkslsv *
      &NUM (MAX (2 * (ht1 − ht2 + new)) 1) v`
    >- (
      xif
      >- (
        xlit>>xsimpl>>
        fs[Abbr`new`,NUM_def,INT_def,MAX_DEF])>>
      xapp>>xsimpl>>
      qexists_tac`&(ht1 − ht2 + new)`>>
      fs[Abbr`new`,NUM_def,INT_def,MAX_DEF,integerTheory.INT_MUL])>>
    xlet_autop>>
    qmatch_goalsub_abbrev_tac`ARRAY av (REPLICATE sz zv)`>>
    `LIST_REL NUM (REPLICATE sz 0) (REPLICATE sz zv)` by
      (simp[Abbr`zv`,LIST_REL_EL_EQN,EL_REPLICATE]>>EVAL_TAC)>>
    `REPLICATE sz (0:num) ≠ []` by
      simp[Abbr`sz`,REPLICATE_NIL]>>
    `NUM 0 (Litv (IntLit 0i))` by EVAL_TAC>>
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv bkslsv *
      SEP_EXISTS ls1. ARRAY av ls1 *
      &(NUM (ht_count fmlls 0 inds 0) v ∧
        LIST_REL NUM (ht_insert fmlls 0 inds (REPLICATE sz 0)) ls1)`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`REPLICATE sz 0`,`inds`,`fmlls`]>>
      simp[])>>
    `ht_insert fmlls 0 inds (REPLICATE sz 0) ≠ []` by
      metis_tac[LENGTH_ht_insert,LENGTH_NIL]>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    qexists_tac`ls1`>>
    fs[Abbr`new`,Abbr`sz`]>>
    xsimpl>>
    gvs[markerTheory.Abbrev_def])>>
  xlet`POSTv u. ARRAY fmlv fmllsv * SEP_EXISTS bkslsv1. ARRAY bksv bkslsv1 *
    &LIST_REL NUM (ht_insert fmlls ht0 inds ht3) bkslsv1`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ht3`,`inds`,`ht0`,`fmlls`]>>
    simp[])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  qexists_tac`bkslsv1`>>
  gvs[Abbr`new`]>>
  conj_tac >- metis_tac[LENGTH_ht_insert,LENGTH_NIL]>>
  xsimpl
QED

Quote add_cakeml:
  fun ht_del_count_arr fml hw ls n =
  case ls of [] => n
  | i::is =>
    if i < hw then
      (case Array.lookup fml Empty i of
        Empty => ht_del_count_arr fml hw is n
      | _ => ht_del_count_arr fml hw is (n+1))
    else ht_del_count_arr fml hw is n
End

Theorem ht_del_count_arr_spec:
  ∀ls lsv n nv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM hw hwv ∧
  LIST_TYPE NUM ls lsv ∧
  NUM n nv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_del_count_arr" (get_ml_prog_state()))
    [fmlv; hwv; lsv; nv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &NUM (ht_del_count fmlls hw ls n) v)
Proof
  Induct>>
  rw[]>>
  xcf "ht_del_count_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,ht_del_count_def]>>
  xmatch
  >- (
    xvar>>xsimpl)>>
  xlet_autop>>
  reverse xif
  >- (
    xapp>>simp[])>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto>>
  `fslot_TYPE (any_el h fmlls Empty) v'` by (
    gvs[]>>
    irule LIST_REL_fslot_TYPE_any_el>>
    gvs[SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  xmatch>>
  xlet_autop>>
  xapp>>simp[]
QED

(* Before the ids ls are deleted from fml *)
Quote add_cakeml:
  fun ht_del_arr fml ls ht =
  case ht of (hw,(a,(d,bks))) =>
  if hw = 0 then ht
  else
    let val d = ht_del_count_arr fml hw ls d in
      if a < 2 * d then (0,(0,(0,Array.arrayEmpty ())))
      else (hw,(a,(d,bks)))
    end
End

Theorem ht_del_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM ls lsv ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_del_arr" (get_ml_prog_state()))
    [fmlv; lsv; htv]
    (ARRAY fmlv fmllsv * ARRAY bksv bkslsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      SEP_EXISTS bksv' bkslsv'.
      ARRAY bksv' bkslsv' *
      &ht_TYPE bksv' bkslsv' (ht_del fmlls ls ht) v)
Proof
  rw[]>>
  PairCases_on`ht`>>
  gvs[ht_TYPE_def,PAIR_TYPE_def,ht_del_def]>>
  xcf "ht_del_arr" (get_ml_prog_state ())>>
  xmatch>>
  xlet_autop>>
  xif
  >- (
    xvar>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    qexists_tac`bkslsv`>>
    gvs[]>>
    xsimpl)>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,ht_empty_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  qexists_tac`bkslsv`>>
  gvs[]>>
  xsimpl
QED

val res = translate split_goals_pure_def;

Theorem split_goals_pure_side:
  ∀goals lp lf.
  wf_slot extra ⇒ split_goals_pure_side proved extra goals lp lf
Proof
  Induct>>
  rw[Once (fetch "-" "split_goals_pure_side_def"),imp_slot_side]
QED

(* The first goal of ls that neither matches a slot (core only, if b) of
  fml in the table tbl nor is a proved goal of lp, printed *)
Quote add_cakeml:
  fun ht_goals_arr b fml lp tbl ls =
  case ls of [] => None
  | c::cs =>
    let val n = Array.length tbl in
      if ht_mem_arr b fml c tbl (hash_constraint c mod n) n orelse
        mem_constraint c lp
      then ht_goals_arr b fml lp tbl cs
      else Some (npbc_constr_string c)
    end
End

Theorem ht_goals_arr_spec:
  ∀ls lsv.
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE constraint_TYPE lp lpv ∧
  tbl ≠ [] ∧
  LIST_REL NUM tbl tbllsv ∧
  LIST_TYPE constraint_TYPE ls lsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_goals_arr" (get_ml_prog_state()))
    [bv; fmlv; lpv; tblv; lsv]
    (ARRAY fmlv fmllsv * ARRAY tblv tbllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
      & ∃err.
        OPTION_TYPE STRING_TYPE
          (if ht_goals b fmlls lp tbl ls then NONE else SOME err) v)
Proof
  Induct>>
  rw[]>>
  xcf "ht_goals_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,ht_goals_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def])>>
  imp_res_tac LIST_REL_LENGTH>>
  `tbllsv ≠ []` by (
    Cases_on`tbl`>>gvs[])>>
  rpt xlet_autop>>
  `hash_constraint h MOD LENGTH tbl < LENGTH tbl` by (
    Cases_on`tbl`>>gvs[])>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    &BOOL (ht_mem b fmlls h tbl (hash_constraint h MOD LENGTH tbl)
      (LENGTH tbl)) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`tbl`,`hash_constraint h MOD LENGTH tbl`,`LENGTH tbl`,
      `fmlls`,`h`,`b`]>>
    gvs[])>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    &BOOL (ht_mem b fmlls h tbl (hash_constraint h MOD LENGTH tbl)
      (LENGTH tbl) ∨ mem_constraint h lp) v`
  >- (
    xlog>>
    xsimpl>>
    rw[]
    >- gvs[]>>
    xapp>>xsimpl>>
    metis_tac[])>>
  xif
  >- (
    xapp>>xsimpl>>
    gvs[ht_probe_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  gvs[ht_probe_def,OPTION_TYPE_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun split_goals_hash_arr b fml inds base ht extra proved goals =
  case split_goals_pure proved extra goals [] [] of (lp,lf) =>
  case lf of [] => (None, ht)
  | _ =>
    let val ht = ht_fill_arr fml inds base ht in
      case ht of (hw,(a,(d,tbl))) =>
        (ht_goals_arr b fml lp tbl lf, ht)
    end
End

Theorem split_goals_hash_arr_spec:
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv ∧
  NUM base basev ∧
  ht_TYPE bksv bkslsv ht htv ∧
  fslot_TYPE extra extrav ∧
  SPTREE_SPT_TYPE UNIT_TYPE proved provedv ∧
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) goals goalsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "split_goals_hash_arr" (get_ml_prog_state()))
    [bv; fmlv; indsv; basev; htv; extrav; provedv; goalsv]
    (ARRAY fmlv fmllsv * ARRAY bksv bkslsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      SEP_EXISTS bksv' bkslsv'.
      ARRAY bksv' bkslsv' *
      & ∃err.
        PAIR_TYPE (OPTION_TYPE STRING_TYPE) (ht_TYPE bksv' bkslsv')
          ((if FST (split_goals_hash b fmlls inds base ht extra proved goals)
            then NONE else SOME err),
           SND (split_goals_hash b fmlls inds base ht extra proved goals)) v)
Proof
  rw[]>>
  xcf "split_goals_hash_arr" (get_ml_prog_state ())>>
  qpat_x_assum`fslot_TYPE extra _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv bkslsv *
    &PAIR_TYPE (LIST_TYPE constraint_TYPE)
      (LIST_TYPE constraint_TYPE) (split_goals_pure proved extra goals [] []) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`[]`,`[]`,`goals`,`extra`,`proved`]>>
    simp[LIST_TYPE_def,split_goals_pure_side])>>
  Cases_on`split_goals_pure proved extra goals [] []`>>
  rename1`_ = (lp,lf)`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  simp[split_goals_hash_def]>>
  Cases_on`lf`>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def]>>
    qexistsl_tac[`bksv`,`bkslsv`]>>
    xsimpl)>>
  xlet`POSTv v. ARRAY fmlv fmllsv * SEP_EXISTS bksv1 bkslsv1.
    ARRAY bksv1 bkslsv1 *
    &(ht_TYPE bksv1 bkslsv1 (ht_fill fmlls inds base ht) v ∧
      SND (SND (SND (ht_fill fmlls inds base ht))) ≠ [])`
  >- (
    xapp>>xsimpl)>>
  Cases_on`ht_fill fmlls inds base ht`>>
  PairCases_on`r`>>
  gvs[ht_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
    & ∃err. OPTION_TYPE STRING_TYPE
      (if ht_goals b fmlls lp r2 (h::t) then NONE else SOME err) v`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def])>>
  xcon>>xsimpl>>
  qexistsl_tac[`bksv1`,`bkslsv1`]>>
  simp[]>>
  conj_tac >- metis_tac[]>>
  xsimpl
QED

val res = translate npbc_checkTheory.extract_scope_val_def;
val res = translate npbc_checkTheory.extract_scoped_pids_def;

Quote add_cakeml:
  fun red_cond_check_arr b fml inds base ht extra pfs rsubs goals skipped =
  case extract_scoped_pids pfs Ln Ln of (l,r) =>
  if check_hash_goals_slot extra skipped r rsubs then
    split_goals_hash_arr b fml inds base ht extra l goals
  else (Some "not all # subgoals present", ht)
End

Theorem red_cond_check_spec:
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv ∧
  NUM base basev ∧
  ht_TYPE bksv bkslsv ht htv ∧
  fslot_TYPE extra extrav ∧
  scpfs_TYPE pfs pfsv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) goals goalsv ∧
  LIST_TYPE NUM skipped skippedv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "red_cond_check_arr" (get_ml_prog_state()))
    [bv; fmlv; indsv; basev; htv; extrav; pfsv; rsubsv; goalsv; skippedv]
    (ARRAY fmlv fmllsv * ARRAY bksv bkslsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      SEP_EXISTS bksv' bkslsv'.
      ARRAY bksv' bkslsv' *
      & ∃err.
        PAIR_TYPE (OPTION_TYPE STRING_TYPE) (ht_TYPE bksv' bkslsv')
          ((if FST (red_cond_check b fmlls inds base ht extra pfs rsubs goals
                skipped)
            then NONE else SOME err),
           SND (red_cond_check b fmlls inds base ht extra pfs rsubs goals
             skipped)) v)
Proof
  rw[red_cond_check_def]>>
  xcf "red_cond_check_arr" (get_ml_prog_state ())>>
  qpat_x_assum`fslot_TYPE extra _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  rpt xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv bkslsv *
    &PAIR_TYPE (SPTREE_SPT_TYPE UNIT_TYPE) (SPTREE_SPT_TYPE UNIT_TYPE)
      (extract_scoped_pids pfs LN LN) v`
  >- (
    xapp_spec (fetch "-" "extract_scoped_pids_v_thm" |>
      INST_TYPE [alpha|->``:num``,beta|->``:lstep list``])>>
    xsimpl>>
    qexistsl_tac[`LN`,`LN`,`pfs`]>>
    first_assum (irule_at Any)>>
    simp[]>>
    EVAL_TAC)>>
  Cases_on`extract_scoped_pids pfs LN LN`>>
  rename1`_ = (l,r)`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto >- (xsimpl>>simp[check_hash_goals_slot_side])>>
  xif
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`l`,`inds`,`ht`,`goals`,`fmlls`,`extra`,`bksv`,
      `bkslsv`,`base`,`b`]>>
    simp[fslot_TYPE_def]>>
    xsimpl>>
    simp[PAIR_TYPE_def]>>
    rw[]
    >- (
      qpat_assum`ht_TYPE _ _ (SND _) _` (irule_at Any)>>
      xsimpl)>>
    qpat_assum`ht_TYPE _ _ (SND _) _` (irule_at Any)>>
    qpat_assum`OPTION_TYPE _ (SOME _) _` (irule_at Any)>>
    xsimpl)>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def]>>
  qexistsl_tac[`bksv`,`bkslsv`]>>
  xsimpl
QED

(* Definition print_subgoal_def:
  (print_subgoal (INL n) = (toString (n:num))) ∧
  (print_subgoal (INR n) = («#» ^ toString (n:num)))
End

Definition print_subproofs_def:
  (print_subproofs ls =
    concatWith « » (MAP print_subgoal ls))
End *)

Definition print_expected_subproofs_def:
  (print_expected_subproofs rsubs (si: (num # 'a) list) =
    «#[1-» ^
    toString (LENGTH rsubs) ^ «] and » ^
    concatWith « » (MAP (toString o FST) si))
End

Definition print_subproofs_err_def:
  print_subproofs_err rsubs si =
  «Expected (including autoproved): » ^
  print_expected_subproofs rsubs si
  (* ^
  « Got: » ^
  print_subproofs pfs *)
End

(* val res = translate print_subgoal_def;
val res = translate print_subproofs_def; *)
val res = translate print_expected_subproofs_def;
val res = translate print_subproofs_err_def;

Definition format_failure_2_def:
  format_failure_2 (lno:num) s s2 =
  «c Checking failed for top-level proof step starting at line: » ^ toString lno ^ « Reason: » ^ s
  ^ « Info: » ^ s2 ^ «\n»
End

val r = translate format_failure_2_def;

val r = translate red_fast_def;

val res = translate neg_terms_def;
val res = translate not_slot_def;

Theorem neg_terms_side[local]:
  ∀i cs acc. i ≤ length cs ⇒ neg_terms_side cs i acc
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "neg_terms_side_def")]
QED

Theorem not_slot_side[local]:
  not_slot_side s b
Proof
  simp[fetch "-" "not_slot_side_def",neg_terms_side]
QED

val _ = not_slot_side |> update_precondition;

val res = translate max_var_vs_def;
val res = translate slot_max_var_def;

Theorem max_var_vs_side[local]:
  ∀i vs m. i ≤ length vs ⇒ max_var_vs_side vs i m
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "max_var_vs_side_def")]
QED

Theorem slot_max_var_side[local]:
  slot_max_var_side s
Proof
  simp[fetch "-" "slot_max_var_side_def",max_var_vs_side]
QED

val _ = slot_max_var_side |> update_precondition;

Quote add_cakeml:
  fun check_red_arr_fast lno b fml inds id fc mv pf cid vimap assg st ht =
  case store_slot_arr fml (not_slot fc b) mv id assg st of
    (fml_not_c,(id1,(assg,st))) =>
     case check_lsteps_arr lno pf b fml_not_c id id1 assg st of
       (fml', (id', (assg', st'))) =>
      if check_contradiction_fml_arr b fml' cid then
        let val u = rollback_arr fml' id id' in
          (fml', (inds, (vimap, (id', (assg', (st', ht))))))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index: " ^ Int.toString cid))
End

val _ = register_type ``:vent``;

val VENT_TYPE_def = fetch "-" "NPBC_LIST_VENT_TYPE_def";

Overload "vimapn_TYPE" = ``NPBC_LIST_VENT_TYPE``

Theorem check_red_arr_fast_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  fslot_TYPE fc fcv ∧
  NUM mv mvv ∧
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE pfs pfsv ∧
  NUM cid cidv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  slot_bound fc (mv + 1) ∧
  NUM st stv ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr_fast" (get_ml_prog_state()))
    [lnov; bv; fmlv; indsv; idv;
      fcv; mvv; pfsv; cidv; vimapv; assgv; stv; htv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_red_list_fast b fmlls inds id
              fc mv pfs cid vimap assg st ht of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                (PAIR_TYPE NUM
                  (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                    (PAIR_TYPE NUM (ht_TYPE bksv bkslsv)))))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_red_list_fast b fmlls inds id
              fc mv pfs cid vimap assg st ht = NONE)))
Proof
  rw[check_red_list_fast_def]>>
  xcf "check_red_arr_fast" (get_ml_prog_state ())>>
  qpat_x_assum`fslot_TYPE fc _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  xlet_autop>>
  qmatch_asmsub_rename_tac`NPBC_SLOT_SLOT_TYPE (not_slot fc b) ncv`>>
  `fslot_TYPE (not_slot fc b) ncv` by
    simp[fslot_TYPE_def,wf_slot_not_slot]>>
  xlet_auto
  >- (
    xsimpl>>rw[]>>
    first_assum (irule_at Any)>>
    xsimpl)>>
  `∃fml1 id1 assg1 st1.
    store_slot fmlls (not_slot fc b) mv id assg st = (fml1,id1,assg1,st1)` by
    metis_tac[PAIR]>>
  drule_at (Pos last) fml_bound_store_slot>>
  impl_tac >- simp[]>>
  strip_tac>>
  gvs[PAIR_TYPE_def]>>
  rename1`store_slot _ _ _ _ _ _ = (_,_,assg1,_)`>>
  xmatch>>
  xlet_auto
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_lsteps_list pfs b fml1 id id1 assg1 st1`>>gvs[]>>
  qmatch_asmsub_rename_tac`check_lsteps_list _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def]
QED

val res = translate restore_scan_def;
val res = translate restore_slot_def;

Theorem restore_scan_side[local]:
  ∀i cs vs x p q.
  i ≤ length cs ∧ i ≤ length vs ⇒ restore_scan_side cs vs x i p q
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "restore_scan_side_def")]
QED

Theorem restore_slot_side:
  wf_slot s ⇒ restore_slot_side x s
Proof
  Cases_on`s`>>
  rw[fetch "-" "restore_slot_side_def",wf_slot_def]>>
  irule restore_scan_side>>
  simp[]
QED

Quote add_cakeml:
  fun restore_aux_arr x fml ls lacc racc =
  case ls of
    [] => (List.rev lacc, List.rev racc)
  | (i::is) =>
  case Array.lookup fml Empty i of
    Empty => restore_aux_arr x fml is lacc racc
  | s =>
    (case restore_slot x s of (p,q) =>
    restore_aux_arr x fml is
      (if p then i::lacc else lacc)
      (if q then i::racc else racc))
End

Quote add_cakeml:
  fun restore_arr x fml is =
    restore_aux_arr x fml is [] []
End

Theorem restore_aux_arr_spec:
  ∀inds indsv fmlls fmlv lacc laccv racc raccv.
  NUM x xv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) lacc laccv ∧
  (LIST_TYPE NUM) racc raccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "restore_aux_arr" (get_ml_prog_state()))
    [xv; fmlv; indsv; laccv; raccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE
        (LIST_TYPE NUM) (LIST_TYPE NUM)
        (restore_aux x fmlls inds lacc racc) v))
Proof
  Induct>>
  rw[]>>
  xcf"restore_aux_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[restore_aux_def,LIST_TYPE_def,PAIR_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el h fmllsv _`>>
  `fslot_TYPE (any_el h fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  rw[]>>
  simp[restore_aux_def]>>
  Cases_on`any_el h fmlls Empty`>>gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  xmatch>>
  qmatch_asmsub_rename_tac`any_el h fmlls Empty = Stored cs vs d mc sm cb`>>
  xlet`POSTv pq. ARRAY fmlv fmllsv *
    &PAIR_TYPE BOOL BOOL (restore_slot x (Stored cs vs d mc sm cb)) pq`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`x`,`Stored cs vs d mc sm cb`]>>
    simp[SLOT_TYPE_def,restore_slot_side])>>
  Cases_on`restore_slot x (Stored cs vs d mc sm cb)`>>
  rename1`_ = (pp,qq)`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTv rv. ARRAY fmlv fmllsv *
    &LIST_TYPE NUM (if qq then h::racc else racc) rv`
  >- (
    xif>>gvs[]
    >- (xcon>>xsimpl>>simp[LIST_TYPE_def])>>
    xvar>>xsimpl)>>
  xlet`POSTv lv. ARRAY fmlv fmllsv *
    &LIST_TYPE NUM (if pp then h::lacc else lacc) lv`
  >- (
    xif>>gvs[]
    >- (xcon>>xsimpl>>simp[LIST_TYPE_def])>>
    xvar>>xsimpl)>>
  xapp>>xsimpl
QED

Theorem restore_arr_spec:
  ∀inds indsv fmlls fmlv.
  NUM x xv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "restore_arr" (get_ml_prog_state()))
    [xv; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE
        (LIST_TYPE NUM) (LIST_TYPE NUM)
        (restore x fmlls inds) v))
Proof
  rw[]>>
  xcf"restore_arr"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[restore_def]>>
  metis_tac[LIST_TYPE_def]
QED

val res = translate list_insert_def;
val res = translate get_inds_rhs_def;

Quote add_cakeml:
  fun do_reindex_rhs_arr fml rhs pinds ninds =
  case rhs of
    Inl b =>
    if b
    then (pinds, reindex_arr fml ninds)
    else (reindex_arr fml pinds, ninds)
  | Inr _ =>
    (reindex_arr fml pinds, reindex_arr fml ninds)
End

Theorem do_reindex_rhs_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  SUM_TYPE BOOL a rhs rhsv ∧
  LIST_TYPE NUM pinds pindsv ∧
  LIST_TYPE NUM ninds nindsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "do_reindex_rhs_arr" (get_ml_prog_state()))
    [fmlv; rhsv; pindsv; nindsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)
        (do_reindex_rhs fmlls rhs pinds ninds) v))
Proof
  rw[]>>
  xcf "do_reindex_rhs_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  Cases_on `rhs` >> gvs[SUM_TYPE_def,do_reindex_rhs_def]>>
  xmatch
  >- (
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def])
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]))
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def])
QED

Overload "subst_raw_TYPE" = ``LIST_TYPE (PAIR_TYPE NUM (SUM_TYPE BOOL (PBC_LIT_TYPE NUM)))``

Quote add_cakeml:
  fun check_get_inds_rhs_arr vimap ls =
  case ls of
    [] => True
  | ((n,rhs)::xs) =>
    case Array.lookup vimap Vnone n of
      Voverflow => False
    | _ => check_get_inds_rhs_arr vimap xs
End

Theorem check_get_inds_rhs_arr_spec:
  ∀ls lsv vimap vimaplsv vimapv.
  subst_raw_TYPE ls lsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_get_inds_rhs_arr" (get_ml_prog_state()))
    [vimapv; lsv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
      ARRAY vimapv vimaplsv *
      &(BOOL (check_get_inds_rhs vimap ls) v))
Proof
  Induct>>
  rw[]>>
  xcf "check_get_inds_rhs_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,check_get_inds_rhs_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  Cases_on`h`>>
  fs[PAIR_TYPE_def,check_get_inds_rhs_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`lv = any_el q vimaplsv _`>>
  `vimapn_TYPE (any_el q vimap Vnone) lv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,VENT_TYPE_def])>>
  Cases_on`any_el q vimap Vnone`>>
  gvs[VENT_TYPE_def]>>
  xmatch
  >~ [`cf_con _ _`] >- (xcon>>xsimpl)>>
  xapp>>simp[]
QED

Quote add_cakeml:
  fun fold_get_inds_rhs_arr fml ls t vimap =
  case ls of
    [] => (t, vimap)
  | ((n,rhs)::xs) =>
    case Array.lookup vimap Vnone n of
      Vnone => fold_get_inds_rhs_arr fml xs t vimap
    | Vtrack pinds ninds =>
      (case do_reindex_rhs_arr fml rhs pinds ninds of
        (pinds',ninds') =>
      let
        val t' = get_inds_rhs rhs pinds' ninds' t in
      fold_get_inds_rhs_arr fml xs t'
        (Array.updateResize vimap Vnone n (Vtrack pinds' ninds'))
      end)
    | Vcount k pinds ninds =>
      (case do_reindex_rhs_arr fml rhs pinds ninds of
        (pinds',ninds') =>
      let
        val t' = get_inds_rhs rhs pinds' ninds' t in
      fold_get_inds_rhs_arr fml xs t'
        (Array.updateResize vimap Vnone n (Vtrack pinds' ninds'))
      end)
    | Voverflow => (t, vimap)
End

Theorem fold_get_inds_rhs_arr_spec:
  ∀fmlls ls t vimap fmllsv tv lsv vimaplsv
    fmlv vimapv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  subst_raw_TYPE ls lsv ∧
  SPTREE_SPT_TYPE UNIT_TYPE t tv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fold_get_inds_rhs_arr" (get_ml_prog_state()))
    [fmlv; lsv; tv; vimapv]
    (ARRAY fmlv fmllsv * ARRAY vimapv vimaplsv)
    (POSTv v.
        SEP_EXISTS vimapv' vimaplsv'.
        ARRAY fmlv fmllsv * ARRAY vimapv' vimaplsv' *
        &(
          (PAIR_TYPE
            (SPTREE_SPT_TYPE UNIT_TYPE)
            (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv'))
            (fold_get_inds_rhs fmlls ls t vimap) v))
Proof
  ho_match_mp_tac fold_get_inds_rhs_ind>>
  rw[]>>
  xcf "fold_get_inds_rhs_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,PAIR_TYPE_def,fold_get_inds_rhs_def]>>
  xmatch
  >- (xcon>>xsimpl)>>
  xlet_autop>>
  xlet_autop>>
  qmatch_asmsub_rename_tac`lv = any_el n vimaplsv _`>>
  `vimapn_TYPE (any_el n vimap Vnone) lv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,VENT_TYPE_def])>>
  Cases_on`any_el n vimap Vnone`>>
  gvs[VENT_TYPE_def]>>
  xmatch
  >- (xapp>>xsimpl>>metis_tac[])
  >- (
    rpt xlet_autop>>
    pairarg_tac>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    irule LIST_REL_update_resize>>
    simp[VENT_TYPE_def])
  >- (
    rpt xlet_autop>>
    pairarg_tac>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    irule LIST_REL_update_resize>>
    simp[VENT_TYPE_def])>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  metis_tac[ARRAY_refl]
QED

Definition map_fst_def:
  map_fst ls = MAP FST ls
End

val res = translate map_fst_def;

Quote add_cakeml:
  fun get_set_indices_arr fml inds s vimap =
  case s of
    [] => ([], (inds, vimap))
  | [(n,rhs)] =>
    (case Array.lookup vimap Vnone n of
      Vnone => ([], (inds, vimap))
    | Vtrack pinds ninds =>
      (case do_reindex_rhs_arr fml rhs pinds ninds of (pinds,ninds) =>
      let
        val t = get_inds_rhs rhs pinds ninds Ln
        val rinds = map_fst (toalist t) in
      (rinds, (inds, Array.updateResize vimap Vnone n (Vtrack pinds ninds)))
      end)
    | Vcount k pinds ninds =>
      (case do_reindex_rhs_arr fml rhs pinds ninds of (pinds,ninds) =>
      let
        val t = get_inds_rhs rhs pinds ninds Ln
        val rinds = map_fst (toalist t) in
      (rinds, (inds, Array.updateResize vimap Vnone n (Vtrack pinds ninds)))
      end)
    | Voverflow =>
      (case restore_arr n fml inds of (pinds,ninds) =>
      let
        val t = get_inds_rhs rhs pinds ninds Ln
        val rinds = map_fst (toalist t) in
        (rinds, (inds, Array.updateResize vimap Vnone n (Vtrack pinds ninds)))
      end))
  | _ =>
    if check_get_inds_rhs_arr vimap s then
      case fold_get_inds_rhs_arr fml s Ln vimap of
        (t, vimap') =>
        (map_fst (toalist t), (inds, vimap'))
    else
      let val rinds = reindex_arr fml inds in
        (rinds, (rinds, vimap))
      end
End

Theorem spt_Ln[local,simp]:
  v = Conv (SOME (TypeStamp «Ln» 44)) [] ⇔
  SPTREE_SPT_TYPE UNIT_TYPE LN v
Proof
  EVAL_TAC
QED

Theorem get_set_indices_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  subst_raw_TYPE s sv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "get_set_indices_arr" (get_ml_prog_state()))
    [fmlv; indsv; sv; vimapv]
    (ARRAY fmlv fmllsv * ARRAY vimapv vimaplsv)
    (POSTv v.
        SEP_EXISTS vimapv' vimaplsv'.
        ARRAY fmlv fmllsv * ARRAY vimapv' vimaplsv' *
        &(
          PAIR_TYPE (LIST_TYPE NUM)
          (PAIR_TYPE
            (LIST_TYPE NUM)
            (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv'))
            (get_set_indices fmlls inds s vimap) v))
Proof
  rw[]>>
  xcf "get_set_indices_arr" (get_ml_prog_state ())>>
  simp[get_set_indices_def]>>
  Cases_on`s`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def]>>
    metis_tac[ARRAY_refl])>>
  rename1`subst_raw_TYPE t _`>>
  Cases_on`t`>>
  rename1`PAIR_TYPE _ _ h _`>>
  Cases_on`h`>>fs[PAIR_TYPE_def,LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    qmatch_asmsub_rename_tac`lv = any_el q vimaplsv _`>>
    `vimapn_TYPE (any_el q vimap Vnone) lv` by (
      rw[any_el_ALT]>>
      gvs[LIST_REL_EL_EQN,VENT_TYPE_def])>>
    Cases_on`any_el q vimap Vnone`>>
    gvs[VENT_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[LIST_TYPE_def,PAIR_TYPE_def]>>
      metis_tac[ARRAY_refl])>>
    (* Vtrack, Vcount and Voverflow: the new indices are stored *)
    (
      pairarg_tac>>fs[]>>
      xlet_autop>>
      fs[PAIR_TYPE_def]>>
      xmatch>>
      xlet_auto >- (xcon>>xsimpl>>EVAL_TAC)>>
      gvs[]>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[map_fst_def]>>
      irule LIST_REL_update_resize>>
      fs[VENT_TYPE_def]))>>
  xmatch>>
  qmatch_goalsub_abbrev_tac`fold_get_inds_rhs _ ls`>>
  xlet`POSTv v.
      ARRAY fmlv fmllsv * ARRAY vimapv vimaplsv *
      &(BOOL (check_get_inds_rhs vimap ls) v)`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    qexists_tac`ls`>>
    simp[Abbr`ls`,LIST_TYPE_def,PAIR_TYPE_def])>>
  xif
  >- (
    xlet_auto >-
      (xcon>>xsimpl>>EVAL_TAC)>>
    pairarg_tac>>gvs[]>>
    xlet `POSTv v.
        SEP_EXISTS vimapv' vimaplsv'.
        ARRAY fmlv fmllsv * ARRAY vimapv' vimaplsv' *
        &(
          (PAIR_TYPE
            (SPTREE_SPT_TYPE UNIT_TYPE)
            (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv'))
            (fold_get_inds_rhs fmlls ls LN vimap) v)`
    >- (
      xapp>>xsimpl>>
      gvs[LIST_TYPE_def,Abbr`ls`,PAIR_TYPE_def])>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[map_fst_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  metis_tac[ARRAY_refl]
QED

Overload "vomap_TYPE" = ``STRING_TYPE``

val r = translate spt_to_vecTheory.prepend_def;
val r = translate (spt_to_vecTheory.to_flat_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])

Theorem to_flat_ind[local]:
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
val res = translate spt_to_vecTheory.sorted_dedup_def;
val res = translate spt_to_vecTheory.has_at_least_def;
val res = translate spt_to_vecTheory.dense_ok_def;
val res = translate (spt_to_vecTheory.mk_map_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val res = translate npbc_checkTheory.mk_subst_def;

(*
Definition print_lno_mini_def:
  print_lno_mini (lno:num) mini =
  case mini of NONE => toString lno ^ « INF\n»
  | SOME (i:num) => toString lno ^ «  » ^ toString i ^ «\n»
End

val res = translate print_lno_mini_def; *)

val res = translate npbc_checkTheory.check_pres_def;

val res = translate npbc_checkTheory.untouched_order_impl_def;
val res = translate (npbc_checkTheory.skip_ord_subgoal_def |> SIMP_RULE std_ss [SUC_LEMMA]);

val res = translate check_fresh_aux_obj_vomap_def;
val res = translate (npbc_checkTheory.check_fresh_aux_constr_def);
val res = translate npbc_checkTheory.filter_map_inr_def;
val res = translate (npbc_checkTheory.check_fresh_aux_subst_def);

Quote add_cakeml:
  fun check_fresh_aux_fml_vimap_arr xs vimap =
  case xs of
    [] => True
  | (x::xs) =>
    case Array.lookup vimap Vnone x of
      Vnone => check_fresh_aux_fml_vimap_arr xs vimap
    | _ => False
End

Theorem check_fresh_aux_fml_vimap_arr_spec:
  ∀xs xsv.
  LIST_TYPE NUM xs xsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_fresh_aux_fml_vimap_arr" (get_ml_prog_state()))
    [xsv; vimapv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
      ARRAY vimapv vimaplsv *
      &(
        BOOL (check_fresh_aux_fml_vimap xs vimap) v
        ))
Proof
  Induct>>
  rw[]>>
  xcf "check_fresh_aux_fml_vimap_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,check_fresh_aux_fml_vimap_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`lv = any_el h vimaplsv _`>>
  `vimapn_TYPE (any_el h vimap Vnone) lv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,VENT_TYPE_def])>>
  Cases_on`any_el h vimap Vnone`>>
  gvs[VENT_TYPE_def]>>
  xmatch
  >- (xapp>>simp[])>>
  xcon>>xsimpl
QED

val res = translate fresh_vs_def;
val res = translate check_fresh_aux_constr_slot_def;

Theorem fresh_vs_side[local]:
  ∀i asv vs. i ≤ length vs ⇒ fresh_vs_side asv vs i
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "fresh_vs_side_def")]
QED

Theorem check_fresh_aux_constr_slot_side[local]:
  check_fresh_aux_constr_slot_side asv s
Proof
  simp[fetch "-" "check_fresh_aux_constr_slot_side_def",fresh_vs_side]
QED

val _ = check_fresh_aux_constr_slot_side |> update_precondition;

val res = translate mk_get_ord_def;

Quote add_cakeml:
  fun check_fresh_aspo_arr c s ord vimap vomap =
  case mk_get_ord c s ord vomap of
    None => False
  | Some res =>
    case res of
      Inl u => True
    | Inr xs => check_fresh_aux_fml_vimap_arr xs vimap
End

Quote add_cakeml:
  fun cond_check_fresh_aspo_arr hs untouched
    c s ord vimap vomap =
    if hs orelse not untouched then
      check_fresh_aspo_arr c s ord vimap vomap
    else True
End

(* Overloads all the _TYPEs that we will reuse *)
Overload "aspo_TYPE" = ``
  PAIR_TYPE
    (PAIR_TYPE (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE NUM)
      (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))))
    (LIST_TYPE (PAIR_TYPE NUM BOOL))``

Overload "ords_TYPE" = ``
  PAIR_TYPE aspo_TYPE
  (PAIR_TYPE (SPT_TO_VEC_LMAP_TYPE (PAIR_TYPE NUM BOOL))
  (PAIR_TYPE (SPT_TO_VEC_LMAP_TYPE (PAIR_TYPE NUM BOOL))
  (PAIR_TYPE (SPT_TO_VEC_LMAP_TYPE BOOL)
    (SPT_TO_VEC_LMAP_TYPE UNIT_TYPE)
  )))``

Overload "obj_TYPE" = ``
  OPTION_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)``

Overload "pres_TYPE" = ``OPTION_TYPE (SPTREE_SPT_TYPE UNIT_TYPE)``

Theorem OPTION_TYPE_SPLIT:
  OPTION_TYPE a x v ⇔
  (x = NONE ∧ v = Conv (SOME (TypeStamp «None» 2)) []) ∨
  (∃y vv. x = SOME y ∧ v = Conv (SOME (TypeStamp «Some» 2)) [vv] ∧ a y vv)
Proof
  Cases_on`x`>>rw[OPTION_TYPE_def]
QED

Theorem PAIR_TYPE_SPLIT:
  PAIR_TYPE a b x v ⇔
  ∃x1 x2 v1 v2. x = (x1,x2) ∧ v = Conv NONE [v1; v2] ∧ a x1 v1 ∧ b x2 v2
Proof
  Cases_on`x`>>EVAL_TAC>>rw[]
QED

Theorem check_fresh_aspo_arr_spec:
  NPBC_SLOT_SLOT_TYPE c cv ∧
  subst_raw_TYPE s sv ∧
  OPTION_TYPE ords_TYPE ord ordv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  vomap_TYPE vomap vomapv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_fresh_aspo_arr" (get_ml_prog_state()))
    [cv; sv; ordv; vimapv; vomapv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
      ARRAY vimapv vimaplsv *
      &(
        BOOL (check_fresh_aspo_list c s ord vimap vomap) v
        ))
Proof
  rw[check_fresh_aspo_list_mk_get_ord]>>
  xcf "check_fresh_aspo_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  Cases_on`mk_get_ord c s ord vomap`>>
  gvs[OPTION_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl)>>
  rename1`SUM_TYPE _ _ res _`>>
  Cases_on`res`>>
  gvs[SUM_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl)>>
  xapp>>xsimpl
QED

Theorem cond_check_fresh_aspo_arr_spec:
  BOOL hs hsv ∧
  BOOL untouched untouchedv ∧
  NPBC_SLOT_SLOT_TYPE c cv ∧
  subst_raw_TYPE s sv ∧
  OPTION_TYPE ords_TYPE ord ordv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  vomap_TYPE vomap vomapv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "cond_check_fresh_aspo_arr" (get_ml_prog_state()))
    [hsv; untouchedv; cv; sv; ordv; vimapv; vomapv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
      ARRAY vimapv vimaplsv *
      &(
        BOOL (hs ∨ ¬ untouched ⇒ check_fresh_aspo_list c s ord vimap vomap) v
        ))
Proof
  rw[]>>
  xcf "cond_check_fresh_aspo_arr" (get_ml_prog_state ())>>
  xlet`POSTv v. ARRAY vimapv vimaplsv * &BOOL (hs ∨ ¬ untouched) v`
  >- (
    xlog>>rw[]>>xsimpl>>
    xapp>>xsimpl>>
    metis_tac[])>>
  xif
  >- (xapp>>xsimpl)>>
  xcon>>xsimpl
QED

val res = translate npbc_checkTheory.has_scope_def;

Quote add_cakeml:
  fun check_red_arr lno pres ord obj b tcb fml inds id
    fc mv s pfs idopt vimap vomap assg st ht =
  if check_pres pres s then
  case red_fast idopt pfs of
  None =>
  (
  let
    val bortcb = b orelse tcb
    val hs = has_scope pfs in
    case get_set_indices_arr fml inds s vimap of (rinds, (inds',vimap')) =>
    let val ss = mk_subst rinds s in
    case fast_red_subgoals ord ss s fc obj vomap hs of (rsubs,rscopes) =>
  let
    val nfc = not_slot fc b
    val cpfs = extract_scopes_arr lno rscopes ss b fml rsubs pfs in
    case store_slot_arr fml nfc mv id assg st of
      (fml_not_c,(id1,(assg,st))) =>
    case check_scopes_arr lno cpfs b fml_not_c id id1 assg st of
      (fml', (id', (assg', st'))) =>
     (case idopt of
       None =>
       let val u = rollback_arr fml' id id'
           val goals = subst_indexes_arr ss bortcb fml' rinds in
           case skip_ord_subgoal s ord of (untouched,skipped) =>
           if cond_check_fresh_aspo_arr hs untouched fc s ord vimap' vomap
           then
             case red_cond_check_arr b fml' inds' id ht nfc pfs rsubs goals
                 skipped of
               (None, ht') =>
               (fml', (inds', (vimap', (id', (assg', (st', ht'))))))
             | (Some err, _) =>
             raise Fail (format_failure_2 lno ("redundancy subproofs did not cover all subgoals. Info: " ^ err ^ ".") (print_subproofs_err rsubs goals))
          else
             raise Fail (format_failure lno ("freshness check failed on auxiliary variables."))
       end
    | Some cid =>
      if check_contradiction_fml_arr b fml' cid then
        let val u = rollback_arr fml' id id' in
           (fml', (inds', (vimap', (id', (assg', (st', ht))))))
        end
      else raise Fail (format_failure lno ("did not derive contradiction from index: " ^ Int.toString cid)))
  end
  end
  end)
  | Some (pf,cid) =>
    check_red_arr_fast lno b fml inds id fc mv pf cid vimap assg st ht
  else raise Fail (format_failure lno ("domain of substitution must not mention projection set."))
End

Theorem check_red_arr_spec:
  NUM lno lnov ∧
  pres_TYPE pres presv ∧
  OPTION_TYPE ords_TYPE ord ordv ∧
  obj_TYPE obj objv ∧
  BOOL b bv ∧
  BOOL tcb tcbv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  fslot_TYPE fc fcv ∧
  NUM mv mvv ∧
  subst_raw_TYPE s sv ∧
  scpfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  fml_bound fmlls (LENGTH assg) ∧
  slot_bound fc (mv + 1) ∧
  NUM st stv ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_red_arr" (get_ml_prog_state()))
    [lnov; presv; ordv; objv; bv; tcbv; fmlv; indsv; idv;
      fcv; mvv; sv; pfsv; idoptv; vimapv; vomapv; assgv; stv; htv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        &(
          case check_red_list pres ord obj b tcb fmlls inds id
              fc mv s pfs idopt vimap vomap assg st ht of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                (PAIR_TYPE NUM
                  (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                    (PAIR_TYPE NUM (ht_TYPE bksv' bkslsv')))))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        & (Fail_exn e ∧
          check_red_list pres ord obj b tcb fmlls inds id
              fc mv s pfs idopt vimap vomap assg st ht = NONE)))
Proof
  rw[]>>
  xcf "check_red_arr" (get_ml_prog_state ())>>
  `NPBC_SLOT_SLOT_TYPE fc fcv ∧ wf_slot fc` by fs[fslot_TYPE_def]>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,check_red_list_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet_autop>>
  rw[check_red_list_def]>>
  reverse (Cases_on`red_fast idopt pfs`)
  >- (
    qmatch_asmsub_rename_tac`red_fast _ _ = SOME pc`>>
    PairCases_on`pc`>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    xmatch>>
    xapp>>
    qexists_tac`ARRAY bksv bkslsv`>>
    xsimpl>>
    qexistsl_tac[`vimap`,`st`,`pc0`,`mv`,`inds`,`id`,`ht`,`fmlls`,`fc`,`pc1`,
      `bksv`,`bkslsv`,`b`,`assg`,`lno`]>>
    simp[]>>
    rw[]>>
    metis_tac[ARRAY_NUM_ARRAY_refl,SEP_IMP_REFL])>>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv bkslsv * &BOOL (b ∨ tcb) v`
  >- (xlog>>xsimpl>>rw[]>>fs[]>>xvar>>xsimpl)>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>rw[]>>first_assum (irule_at Any)>>xsimpl)>>
  `∃rinds inds1 vimap1.
    get_set_indices fmlls inds s vimap = (rinds,inds1,vimap1)` by
    metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  qmatch_asmsub_rename_tac`LIST_REL vimapn_TYPE vimap1 vimaplsv1`>>
  qmatch_goalsub_rename_tac`ARRAY vimapv1 vimaplsv1`>>
  xmatch>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  xlet_auto
  >- (xsimpl>>simp[fast_red_subgoals_side])>>
  `∃rsubs rscopes.
    fast_red_subgoals ord (mk_subst rinds s) s fc obj vomap (has_scope pfs) =
    (rsubs,rscopes)` by
    metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  qmatch_asmsub_rename_tac`NPBC_SLOT_SLOT_TYPE (not_slot fc b) ncv`>>
  `∃fml1 id1 assg1 st1.
    store_slot fmlls (not_slot fc b) mv id assg st = (fml1,id1,assg1,st1)` by
    metis_tac[PAIR]>>
  simp[]>>
  xlet_auto
  >- xsimpl
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`extract_scopes_list rscopes (mk_subst rinds s) b fmlls rsubs pfs`>>
  gvs[]>>
  rename1`check_scope_TYPE cpfs _`>>
  `fslot_TYPE (not_slot fc b) ncv` by
    simp[fslot_TYPE_def,wf_slot_not_slot]>>
  xlet_auto
  >- (xsimpl>>rw[]>>first_assum (irule_at Any)>>xsimpl)>>
  drule_at (Pos last) fml_bound_store_slot>>
  impl_tac >- simp[]>>
  strip_tac>>
  gvs[PAIR_TYPE_def]>>
  rename1`store_slot _ _ _ _ _ _ = (_,_,assg1,_)`>>
  qmatch_asmsub_rename_tac`LIST_REL fslot_TYPE fml1 fmllsv1`>>
  xmatch>>
  xlet_auto
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_scopes_list cpfs b fml1 id id1 assg1 st1`>>gvs[]>>
  qmatch_asmsub_rename_tac`check_scopes_list _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  qmatch_asmsub_rename_tac
    `check_scopes_list _ _ _ _ _ _ _ = SOME (fml2,id2,assg2,st2)`>>
  qmatch_asmsub_rename_tac`LIST_REL fslot_TYPE fml2 fmllsv2`>>
  xmatch>>
  `∃untouched skipped. skip_ord_subgoal s ord = (untouched,skipped)` by
    metis_tac[PAIR]>>
  simp[do_red_check_def]>>
  Cases_on`idopt`>>gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    qmatch_goalsub_rename_tac`NUM_ARRAY assgv3 assg2 * ARRAY fmlv3 fmllsv2`>>
    rpt xlet_autop>>
    qmatch_asmsub_rename_tac`LIST_REL fslot_TYPE (rollback fml2 id id2) fmllsv3`>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`fmlv3`,`fmllsv3`,`assgv3`,`assg2`,`vimapv1`,`vimaplsv1`,
        `bksv`,`bkslsv`]>>
      xsimpl>>metis_tac[])>>
    xlet_auto
    >- (
      xsimpl>>
      rw[]>>
      qpat_assum`PAIR_TYPE _ _ _ _` (irule_at Any)>>
      xsimpl)>>
    qmatch_asmsub_abbrev_tac`PAIR_TYPE _ _ (_, SND rcc) _`>>
    PairCases_on`rcc`>>
    qpat_x_assum`Abbrev _`
      (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
    gvs[PAIR_TYPE_def]>>
    Cases_on`rcc0`>>
    gvs[OPTION_TYPE_def]
    >- (
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      qexistsl_tac[`fmlv3`,`fmllsv3`,`assgv3`,`assg2`,`vimapv1`,`vimaplsv1`,
        `bksv'`,`bkslsv'`]>>
      xsimpl>>
      gvs[PAIR_TYPE_def]>>
      IF_CASES_TAC>>gvs[PAIR_TYPE_def])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    qexistsl_tac[`fmlv3`,`fmllsv3`,`assgv3`,`assg2`,`vimapv1`,`vimaplsv1`,
      `bksv'`,`bkslsv'`]>>
    xsimpl>>
    IF_CASES_TAC>>gvs[]>>
    metis_tac[])>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def]
QED

val res = translate (opt_cons_def |> REWRITE_RULE [ind_lim_def]);

(* The variables of the slot are within vimap: unchecked updates *)
Quote add_cakeml:
  fun update_vimap_slot_aux_arr fresh vimap v cs vs i =
  if i = 0 then ()
  else
    let
      val i1 = i - 1
      val n = Unsafe.vsub vs i1
    in
      Unsafe.update vimap n
        (opt_cons fresh (Unsafe.vsub cs i1) v (Unsafe.sub vimap n));
      update_vimap_slot_aux_arr fresh vimap v cs vs i1
    end
End

Theorem update_vimap_slot_aux_arr_spec:
  ∀i vimap vimaplsv iv.
  BOOL fresh freshv ∧
  NUM id idv ∧
  VECTOR_TYPE INT cs csv ∧
  VECTOR_TYPE NUM vs vsv ∧
  NUM i iv ∧
  i ≤ length cs ∧ i ≤ length vs ∧
  (∀j. j < i ⇒ sub vs j < LENGTH vimap) ∧
  LIST_REL vimapn_TYPE vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "update_vimap_slot_aux_arr" (get_ml_prog_state()))
    [freshv; vimapv; idv; csv; vsv; iv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
      SEP_EXISTS vimaplsv'.
      ARRAY vimapv vimaplsv' *
      &(UNIT_TYPE () v ∧
        LIST_REL vimapn_TYPE
          (update_vimap_slot_aux fresh vimap id cs vs i) vimaplsv'))
Proof
  Induct>>
  rw[]>>
  xcf "update_vimap_slot_aux_arr" (get_ml_prog_state ())>>
  simp[Once update_vimap_slot_aux_def]>>
  xlet_autop>>
  xif>>asm_exists_tac>>simp[]
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  `sub vs i < LENGTH vimap` by simp[]>>
  imp_res_tac LIST_REL_LENGTH>>
  xlet_auto >- (xsimpl>>gvs[])>>
  `vimapn_TYPE (EL (sub vs i) vimap) (EL (sub vs i) vimaplsv)` by
    gvs[LIST_REL_EL_EQN]>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  rw[]>>gvs[]>>
  irule EVERY2_LUPDATE_same>>simp[]
QED

(* m bounds the variables of the slot: vimap is resized once *)
Quote add_cakeml:
  fun update_vimap_slot_arr fresh vimap v m s =
  case s of
    Empty => vimap
  | Stored cs vs d mc sm b =>
    let val vimap =
      if m < Array.length vimap then vimap
      else Array.updateResize vimap Vnone m Vnone
    in
      (update_vimap_slot_aux_arr fresh vimap v cs vs (Vector.length vs);
       vimap)
    end
End

Theorem update_vimap_slot_arr_spec:
  BOOL fresh freshv ∧
  NUM id idv ∧
  NUM m mv ∧
  fslot_TYPE s sv ∧
  slot_bound s (m + 1) ∧
  LIST_REL vimapn_TYPE vimap vimaplsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "update_vimap_slot_arr" (get_ml_prog_state()))
    [freshv; vimapv; idv; mv; sv]
    (ARRAY vimapv vimaplsv)
    (POSTv vimapv'.
      SEP_EXISTS vimaplsv'.
      ARRAY vimapv' vimaplsv' *
      &LIST_REL vimapn_TYPE
        (update_vimap_slot fresh vimap id m s) vimaplsv')
Proof
  rw[]>>
  xcf "update_vimap_slot_arr" (get_ml_prog_state ())>>
  Cases_on`s`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def,update_vimap_slot_def,wf_slot_def,
    slot_bound_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rename1`VECTOR_TYPE NUM vs _`>>
  rename1`VECTOR_TYPE INT cs _`>>
  rpt xlet_autop>>
  imp_res_tac LIST_REL_LENGTH>>
  qabbrev_tac`vimap1 =
    if m < LENGTH vimap then vimap else update_resize vimap Vnone Vnone m`>>
  `m < LENGTH vimap1` by
    rw[Abbr`vimap1`,update_resize_def]>>
  xlet`POSTv vimapv1. SEP_EXISTS vimaplsv1.
    ARRAY vimapv1 vimaplsv1 * &LIST_REL vimapn_TYPE vimap1 vimaplsv1`
  >- (
    xif
    >- (xvar>>xsimpl>>gvs[Abbr`vimap1`])>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    gvs[Abbr`vimap1`]>>
    qexists_tac`m`>>simp[]>>
    irule LIST_REL_update_resize>>
    simp[VENT_TYPE_def])>>
  xlet_autop>>
  xlet`POSTv u. SEP_EXISTS vimaplsv2. ARRAY vimapv1 vimaplsv2 *
    &LIST_REL vimapn_TYPE
      (update_vimap_slot_aux fresh vimap1 id cs vs (length vs)) vimaplsv2`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`vs`,`vimap1`,`id`,`length vs`,`fresh`,`cs`]>>
    rw[]>>
    first_x_assum drule>>
    simp[])>>
  xvar>>xsimpl
QED

(* Stores slot s, whose largest variable is mv, and indexes it *)
Quote add_cakeml:
  fun store_ind_arr fml s mv id inds vimap assg st =
  case store_slot_arr fml s mv id assg st of
    (fml',(id',(assg',st'))) =>
    (fml', (sorted_insert id inds,
      (update_vimap_slot_arr True vimap id mv s, (id', (assg', st')))))
End

Theorem store_ind_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fslot_TYPE s sv ∧
  NUM mv mvv ∧
  slot_bound s (mv + 1) ∧
  NUM id idv ∧
  (LIST_TYPE NUM) inds indsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "store_ind_arr" (get_ml_prog_state()))
    [fmlv; sv; mvv; idv; indsv; vimapv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv)
    (POSTv v.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' *
      &(PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
          (PAIR_TYPE (LIST_TYPE NUM)
            (PAIR_TYPE
              (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))))
          (store_ind fmlls s mv id inds vimap assg st) v))
Proof
  rw[store_ind_def]>>
  xcf "store_ind_arr" (get_ml_prog_state ())>>
  `∃fml1 id1 assg1 st1.
    store_slot fmlls s mv id assg st = (fml1,id1,assg1,st1)` by
    metis_tac[PAIR]>>
  simp[]>>
  xlet_auto
  >- (xsimpl>>rw[]>>first_assum (irule_at Any)>>xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rename1`store_slot _ _ _ _ _ _ = (_,_,assg1,_)`>>
  qmatch_goalsub_rename_tac`NUM_ARRAY assgv1 assg1 * ARRAY fmlv1 fmllsv1`>>
  rpt xlet_autop>>
  xlet`POSTv vimapv1.
    NUM_ARRAY assgv1 assg1 * ARRAY fmlv1 fmllsv1 *
    SEP_EXISTS vimaplsv1. ARRAY vimapv1 vimaplsv1 *
    &LIST_REL vimapn_TYPE (update_vimap_slot T vimap id mv s) vimaplsv1`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`vimap`,`s`,`mv`,`id`,`T`]>>
    simp[]>>
    EVAL_TAC)>>
  rpt xlet_autop>>
  xcon>>xsimpl
QED

Quote add_cakeml:
  fun opt_update_inds_arr fml c id inds vimap assg st =
  case c of
    None => (fml, (inds, (vimap, (id, (assg, st)))))
  | Some (c,b) =>
    (case enc_mv c b of (s,mv) =>
      store_ind_arr fml s mv id inds vimap assg st)
End

Theorem opt_update_inds_arr_spec:
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  OPTION_TYPE bconstraint_TYPE c cv ∧
  NUM id idv ∧
  (LIST_TYPE NUM) inds indsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "opt_update_inds_arr" (get_ml_prog_state()))
    [fmlv; cv; idv; indsv; vimapv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv)
    (POSTv v.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' *
      &(PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
          (PAIR_TYPE (LIST_TYPE NUM)
            (PAIR_TYPE
              (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))))
          (opt_update_inds fmlls c id inds vimap assg st) v))
Proof
  Cases_on`c`>>rw[]>>
  xcf "opt_update_inds_arr" (get_ml_prog_state ())>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac[`fmlv`,`fmllsv`,`assgv`,`assg`,`vimapv`,`vimaplsv`]>>
    simp[PAIR_TYPE_def,opt_update_inds_def]>>
    xsimpl)>>
  rename1`bconstraint_TYPE cb _`>>
  Cases_on`cb`>>fs[PAIR_TYPE_def]>>
  rename1`constraint_TYPE c _`>>
  rename1`BOOL b _`>>
  xmatch>>
  xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def]>>
  xmatch>>
  xapp>>xsimpl>>
  qexistsl_tac[`emp`,`vimap`,`st`,`enc c b`,`max_var (FST c)`,`inds`,`id`,
    `fmlls`,`assg`]>>
  simp[fslot_TYPE_def,opt_update_inds_def,enc_mv_enc,
    slot_bound_enc_max_var]>>
  xsimpl>>
  rpt strip_tac>>
  first_x_assum (irule_at Any)>>
  xsimpl
QED

val _ = register_type ``:proof_conf``

(* the configuration (pc, vomap, cw) of check_cstep_list *)
Overload "cfg_TYPE" = ``
  PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE (PAIR_TYPE vomap_TYPE NUM)``

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

Quote add_cakeml:
  fun check_sstep_arr lno step fml inds id vimap cfg assg st ht =
  case step of
    Lstep lstep =>
    let
      val ht' = (case lstep of Delete ls => ht_del_arr fml ls ht | _ => ht)
    in
    (case check_lstep_arr lno lstep False fml 0 id assg st of
      (rfml,(c,(id',(assg',st')))) =>
      case opt_update_inds_arr rfml c id' inds vimap assg' st' of
        (fml'',(inds'',(vimap'',(id'',(assg'',st''))))) =>
        (fml'',(inds'',(vimap'',(id'',(assg'',(st'',ht')))))))
    end
  | Red c s pfs idopt =>
    (case cfg of (pc,(vomap,_)) =>
    let val tcb = get_tcb pc in
    case enc_mv c tcb of (fc,mv) =>
    case check_red_arr lno (get_pres pc) (get_ord pc) (get_obj pc) False tcb
        fml inds id fc mv s pfs idopt vimap vomap assg st ht of
      (rfml,(rinds,(vimap',(id',(assg',(st',ht')))))) =>
      case store_ind_arr rfml fc mv id' rinds vimap' assg' st' of
        (fml'',(inds'',(vimap'',(id'',(assg'',st''))))) =>
        (fml'',(inds'',(vimap'',(id'',(assg'',(st'',ht'))))))
    end)
End

val NPBC_CHECK_SSTEP_TYPE_def = theorem "NPBC_CHECK_SSTEP_TYPE_def";

Theorem check_sstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_SSTEP_TYPE step stepv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  cfg_TYPE (pc,vomap,cw) cfgv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_sstep_arr" (get_ml_prog_state()))
    [lnov; stepv; fmlv; indsv; idv; vimapv; cfgv; assgv; stv; htv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        &(
          case check_sstep_list step pc.pres pc.ord pc.obj pc.tcb
            fmlls inds id vimap vomap assg st ht of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                (PAIR_TYPE NUM
                  (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                    (PAIR_TYPE NUM (ht_TYPE bksv' bkslsv')))))) res v))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        & (Fail_exn e ∧
          check_sstep_list step pc.pres pc.ord pc.obj pc.tcb
            fmlls inds id vimap vomap assg st ht = NONE)))
Proof
  rw[]>>
  xcf "check_sstep_arr" (get_ml_prog_state ())>>
  rw[check_sstep_list_def]>>
  Cases_on`step`>>fs[NPBC_CHECK_SSTEP_TYPE_def]
  >- (
    xmatch>>
    xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      ARRAY vimapv vimaplsv * SEP_EXISTS bksv1 bkslsv1. ARRAY bksv1 bkslsv1 *
      &ht_TYPE bksv1 bkslsv1 (ht_lstep fmlls l ht) v`
    >- (
      Cases_on`l`>>
      fs[NPBC_CHECK_LSTEP_TYPE_def,ht_lstep_def]>>
      xmatch
      >~ [`ht_del`] >- (
        xapp>>xsimpl>>
        qexistsl_tac[`NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv`,`l'`,`ht`,
          `fmlls`,`bksv`,`bkslsv`]>>
        xsimpl>>
        rw[]>>
        qpat_assum`ht_TYPE _ _ (ht_del _ _ _) _` (irule_at Any)>>
        xsimpl)>>
      xvar>>xsimpl>>
      qexistsl_tac[`bksv`,`bkslsv`]>>
      conj_tac >- first_assum ACCEPT_TAC>>
      xsimpl)>>
    xlet_autop>>
    xlet`POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv vimaplsv * ARRAY bksv1 bkslsv1 *
        &(case check_lstep_list l F fmlls 0 id assg st of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (OPTION_TYPE bconstraint_TYPE)
              (PAIR_TYPE NUM
                (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))) res v))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv vimaplsv * ARRAY bksv1 bkslsv1 *
        &(Fail_exn e ∧ check_lstep_list l F fmlls 0 id assg st = NONE))`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`ARRAY vimapv vimaplsv * ARRAY bksv1 bkslsv1`,`l`,`st`,
        `id`,`fmlls`,`F`,`assg`,`lno`]>>
      simp[]>>xsimpl>>
      rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
    >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
    Cases_on`check_lstep_list l F fmlls 0 id assg st`>>gvs[]>>
    qmatch_asmsub_rename_tac`check_lstep_list _ _ _ _ _ _ _ = SOME res`>>
    PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
    qmatch_asmsub_rename_tac
      `check_lstep_list _ _ _ _ _ _ _ = SOME (fml1,c1,id1,assg1,st1)`>>
    xmatch>>
    xlet`POSTv v.
      SEP_EXISTS fmlv2 fmllsv2 assgv2 assg2 vimapv2 vimaplsv2.
      ARRAY fmlv2 fmllsv2 * NUM_ARRAY assgv2 assg2 * ARRAY vimapv2 vimaplsv2 *
      ARRAY bksv1 bkslsv1 *
      &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv2 ∧ v = fmlv2)
        (PAIR_TYPE (LIST_TYPE NUM)
          (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv2 ∧ v = vimapv2)
            (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg2 ∧ v = assgv2) NUM))))
        (opt_update_inds fml1 c1 id1 inds vimap assg1 st1) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`ARRAY bksv1 bkslsv1`,`vimap`,`st1`,`inds`,`id1`,`fml1`,
        `c1`,`assg1`]>>
      simp[]>>xsimpl>>
      rw[]>>
      first_x_assum (irule_at Any)>>
      xsimpl)>>
    Cases_on`opt_update_inds fml1 c1 id1 inds vimap assg1 st1`>>
    PairCases_on`r`>>
    gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    qexistsl_tac[`bksv1`,`bkslsv1`]>>
    conj_tac >- first_assum ACCEPT_TAC>>
    xsimpl)>>
  xmatch>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[get_tcb_def]>>
  xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  gvs[get_pres_def,get_ord_def,get_obj_def]>>
  rename1`constraint_TYPE c _`>>
  rename1`subst_raw_TYPE s _`>>
  rename1`scpfs_TYPE pfs _`>>
  rename1`OPTION_TYPE NUM idopt _`>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
      &(case check_red_list pc.pres pc.ord pc.obj F pc.tcb fmlls inds id
          (enc c pc.tcb) (max_var (FST c)) s pfs idopt vimap vomap assg st
          ht of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE
                (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
              (PAIR_TYPE NUM
                (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                  (PAIR_TYPE NUM (ht_TYPE bksv' bkslsv')))))) res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
      &(Fail_exn e ∧
        check_red_list pc.pres pc.ord pc.obj F pc.tcb fmlls inds id
          (enc c pc.tcb) (max_var (FST c)) s pfs idopt vimap vomap assg st
          ht = NONE))`
  >- (
    xapp>>xsimpl>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
    conj_tac >- EVAL_TAC>>
    metis_tac[])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_red_list pc.pres pc.ord pc.obj F pc.tcb fmlls inds id
    (enc c pc.tcb) (max_var (FST c)) s pfs idopt vimap vomap assg st ht`>>
  gvs[]>>
  qmatch_asmsub_rename_tac
    `check_red_list _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  qmatch_asmsub_rename_tac
    `_ = SOME (fml1,inds1,vimap1,id1,assg1,st1,ht1)`>>
  xmatch>>
  xlet`POSTv v.
    SEP_EXISTS fmlv2 fmllsv2 assgv2 assg2 vimapv2 vimaplsv2.
    ARRAY fmlv2 fmllsv2 * NUM_ARRAY assgv2 assg2 * ARRAY vimapv2 vimaplsv2 *
    ARRAY bksv' bkslsv' *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv2 ∧ v = fmlv2)
      (PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv2 ∧ v = vimapv2)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg2 ∧ v = assgv2) NUM))))
      (store_ind fml1 (enc c pc.tcb) (max_var (FST c)) id1 inds1 vimap1
        assg1 st1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY bksv' bkslsv'`,`vimap1`,`st1`,`enc c pc.tcb`,
      `max_var (FST c)`,`inds1`,`id1`,`fml1`,`assg1`]>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    xsimpl)>>
  Cases_on`store_ind fml1 (enc c pc.tcb) (max_var (FST c)) id1 inds1 vimap1
    assg1 st1`>>
  PairCases_on`r`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  qexistsl_tac[`bksv'`,`bkslsv'`]>>
  conj_tac >- first_assum ACCEPT_TAC>>
  xsimpl
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
val res = translate npbc_checkTheory.lookup_lincomb_def;
val res = translate npbc_checkTheory.check_cutting_def;
val res = translate npbc_checkTheory.check_contradiction_fml_def;
val res = translate npbc_checkTheory.insert_fml_def;

val res = translate npbc_checkTheory.rup_pass1_def;
val res = translate (npbc_checkTheory.rup_pass2_def |> REWRITE_RULE [GSYM fmap_update_def]);
val res = translate npbc_checkTheory.update_assg_def;
val res = translate npbc_checkTheory.model_bounding_def;
val res = translate npbc_checkTheory.get_rup_constraint_def;
val res = translate npbc_checkTheory.check_rup_def;
val res = translate npbc_checkTheory.check_lstep_def;
val res = translate npbc_checkTheory.list_insert_fml_def;
val res = translate npbc_checkTheory.check_subproofs_def;

val res = translate insert_distinct_def;
val res = translate check_ws_fast_def;
val res = translate check_ws_eq;
val res = translate
  (npbc_checkTheory.check_transitivity_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate npbc_checkTheory.refl_subst_def;
val res = translate npbc_checkTheory.check_reflexivity_def;

val res = translate npbc_checkTheory.check_support_def;

Quote add_cakeml:
  fun check_spec_aux_arr lno aa fml inds id gs vimap assg st ht =
    case gs of [] => True
  | (c,(s,(pfs,idopt)))::gs =>
    if check_support aa s then
    (case enc_mv c False of (fc,mv) =>
    case
      check_red_arr lno None None None False False
        fml inds id fc mv s pfs idopt vimap "" assg st ht of
        (fml',(inds',(vimap',(id',(assg',(st',ht')))))) =>
      (case store_ind_arr fml' fc mv id' inds' vimap' assg' st' of
        (fml'',(inds'',(vimap'',(id'',(assg'',st''))))) =>
      check_spec_aux_arr lno aa fml'' inds'' id'' gs vimap'' assg'' st''
        ht'))
    else
      raise Fail (format_failure lno ("specification proof in order definition failed."))
End

Theorem check_spec_aux_arr_spec:
  ∀gs gsv fmlls fmllsv id idv vimap vimaplsv fmlv indsv vimapv inds
    assg assgv st stv ht htv bksv bkslsv.
  NUM lno lnov ∧
  SPT_TO_VEC_LMAP_TYPE UNIT_TYPE aa aav ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  LIST_TYPE
    (PAIR_TYPE constraint_TYPE
    (PAIR_TYPE subst_raw_TYPE
    (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM)))) gs gsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_spec_aux_arr" (get_ml_prog_state()))
    [lnov; aav; fmlv; indsv; idv; gsv; vimapv; assgv; stv; htv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv)
    (POSTve
      (λv.
        &(check_spec_aux_list aa fmlls inds id gs vimap assg st ht))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        & (Fail_exn e ∧
          ¬check_spec_aux_list aa fmlls inds id gs vimap assg st ht)))
Proof
  Induct>>rw[]>>
  xcf "check_spec_aux_arr" (get_ml_prog_state ())
  >- (
    gvs[LIST_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl>>
    simp[check_spec_aux_list_def])>>
  `∃c s pfs idopt. h = (c,s,pfs,idopt)` by metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def,LIST_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  simp[check_spec_aux_list_def]>>
  reverse xif>>simp[]
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv bkslsv *
    &PAIR_TYPE NPBC_SLOT_SLOT_TYPE NUM (enc_mv c F) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`F`,`c`]>>simp[]>>
    EVAL_TAC)>>
  gvs[enc_mv_enc,PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
      &(case check_red_list (NONE:num_set option) (NONE:ord_s option)
          NONE F F fmlls inds id
          (enc c F) (max_var (FST c)) s pfs idopt vimap «» assg st ht of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE
                (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
              (PAIR_TYPE NUM
                (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                  (PAIR_TYPE NUM (ht_TYPE bksv' bkslsv')))))) res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
      &(Fail_exn e ∧
        check_red_list (NONE:num_set option) (NONE:ord_s option)
          NONE F F fmlls inds id
          (enc c F) (max_var (FST c)) s pfs idopt vimap «» assg st ht =
        NONE))`
  >- (
    xapp>>xsimpl>>
    `BOOL F (Conv (SOME (TypeStamp «False» 0)) [])` by EVAL_TAC>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var,OPTION_TYPE_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>gvs[]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_red_list (NONE:num_set option) (NONE:ord_s option) NONE F F
    fmlls inds id (enc c F) (max_var (FST c)) s pfs idopt vimap «» assg st ht`>>
  gvs[]>>
  qmatch_asmsub_rename_tac
    `check_red_list _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  qmatch_asmsub_rename_tac`_ = SOME (fml1,inds1,vimap1,id1,assg1,st1,ht1)`>>
  drule_at (Pos last) fml_bound_check_red_list>>
  impl_tac >- simp[slot_bound_enc_max_var]>>
  strip_tac>>
  `∃fml2 inds2 vimap2 id2 assg2 st2.
    store_ind fml1 (enc c F) (max_var (FST c)) id1 inds1 vimap1 assg1 st1 =
    (fml2,inds2,vimap2,id2,assg2,st2)` by metis_tac[PAIR]>>
  drule_at (Pos last) fml_bound_store_ind>>
  impl_tac >- simp[slot_bound_enc_max_var]>>
  strip_tac>>
  xmatch>>
  xlet`POSTv v.
    SEP_EXISTS fmlv2 fmllsv2 assgv2 vimapv2 vimaplsv2.
    ARRAY fmlv2 fmllsv2 * NUM_ARRAY assgv2 assg2 * ARRAY vimapv2 vimaplsv2 *
    ARRAY bksv' bkslsv' *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv2 ∧ v = fmlv2)
      (PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv2 ∧ v = vimapv2)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg2 ∧ v = assgv2) NUM))))
      (fml2,inds2,vimap2,id2,assg2,st2) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY bksv' bkslsv'`,`vimap1`,`st1`,`enc c F`,
      `max_var (FST c)`,`inds1`,`id1`,`fml1`,`assg1`]>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
    xsimpl>>
    rpt strip_tac>>
    gvs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xapp>>xsimpl
QED

val res = translate npbc_checkTheory.mk_as_vec_def;

Quote add_cakeml:
  fun check_spec_arr lno vvs gs =
  (case vvs of (us,(vs,aa)) =>
  let
    val aa = mk_as_vec aa
    val fml = Array.array 0 Empty
    val vimap = Array.array 0 Vnone
    val assg = Array.array 0 0
    val ht = (0,(0,(0,Array.arrayEmpty ())))
  in
    (check_spec_aux_arr lno aa fml [] 1 gs vimap assg 1 ht; aa)
  end)
End

Theorem check_spec_arr_spec:
  NUM lno lnov ∧
  PAIR_TYPE (LIST_TYPE NUM)
    (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)) vvs vvsv ∧
  LIST_TYPE
    (PAIR_TYPE constraint_TYPE
    (PAIR_TYPE subst_raw_TYPE
    (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM)))) gs gsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_spec_arr" (get_ml_prog_state()))
    [lnov; vvsv; gsv]
    (emp)
    (POSTve
      (λv.
        SEP_EXISTS av.
        &(check_spec_list vvs gs = SOME av ∧
        SPT_TO_VEC_LMAP_TYPE UNIT_TYPE av v))
      (λe.
        & (Fail_exn e ∧ check_spec_list vvs gs = NONE)))
Proof
  rw[]>>
  xcf "check_spec_arr" (get_ml_prog_state ())>>
  PairCases_on`vvs`>>gvs[PAIR_TYPE_def,check_spec_list_def]>>
  xmatch>>
  rpt xlet_autop>>
  qmatch_goalsub_rename_tac`ARRAY bkv [] * _`>>
  qmatch_goalsub_abbrev_tac`check_spec_aux_list aa`>>
  xlet`POSTve (λv. &check_spec_aux_list aa [] [] 1 gs [] [] 1 ht_empty)
    (λe. &(Fail_exn e ∧ ¬check_spec_aux_list aa [] [] 1 gs [] [] 1 ht_empty))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`[]`,`ht_empty`,`gs`,`bkv`,`[]`,`[]`,`aa`,`lno`]>>
    gvs[LIST_TYPE_def,Abbr`aa`,npbc_checkTheory.mk_as_vec_def,fml_bound_def,NUM_ARRAY_def,
      any_el_ALT,slot_bound_def,ht_TYPE_def,ht_empty_def,PAIR_TYPE_def]>>
    xsimpl)
  >- xsimpl>>
  xvar>>xsimpl>>
  gvs[npbc_checkTheory.mk_as_vec_def]
QED

val res = translate npbc_checkTheory.mk_aord_def;
val res = translate check_good_aord_fast_def;
val res = translate check_good_aord_eq;

Quote add_cakeml:
  fun check_storeorder_arr lno vvs gs f pfst pfsr =
  let
    val asv = check_spec_arr lno vvs gs
    val aord = mk_aord vvs f gs in
    if check_good_aord aord
    then
      case check_transitivity aord pfst of
        None =>
          raise Fail (format_failure lno ("transitivity proof in order definition failed."))
      | Some id =>
        if check_reflexivity aord pfsr id then (aord,asv)
        else raise Fail (format_failure lno ("reflexivity proof in order definition failed."))
    else
      raise Fail (format_failure lno ("illegal variable usage in order definition."))
  end
End

Theorem check_storeorder_arr_spec:
  NUM lno lnov ∧
  PAIR_TYPE (LIST_TYPE NUM)
    (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)) vvs vvsv ∧
  LIST_TYPE
    (PAIR_TYPE constraint_TYPE
    (PAIR_TYPE subst_raw_TYPE
    (PAIR_TYPE scpfs_TYPE (OPTION_TYPE NUM)))) gs gsv ∧
  LIST_TYPE constraint_TYPE f fv ∧
  PAIR_TYPE (LIST_TYPE NUM)
      (PAIR_TYPE (LIST_TYPE NUM) (PAIR_TYPE (LIST_TYPE NUM) pfs_TYPE)) pfst pfstv ∧
  pfs_TYPE pfsr pfsrv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_storeorder_arr" (get_ml_prog_state()))
    [lnov; vvsv; gsv; fv; pfstv; pfsrv]
    (emp)
    (POSTve
      (λv.
        &(∃aord.
        check_storeorder vvs gs f pfst pfsr = SOME aord ∧
        PAIR_TYPE
          (PAIR_TYPE (LIST_TYPE constraint_TYPE)
           (PAIR_TYPE (LIST_TYPE constraint_TYPE)
              (PAIR_TYPE (LIST_TYPE NUM)
                 (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))))
          (SPT_TO_VEC_LMAP_TYPE UNIT_TYPE) aord v
        ))
      (λe.
        & (Fail_exn e ∧ check_storeorder vvs gs f pfst pfsr = NONE)))
Proof
  rw[]>>
  xcf "check_storeorder_arr" (get_ml_prog_state ())>>
  xlet_autop
  >- (xsimpl>>simp[check_storeorder_def])>>
  rpt xlet_autop>>
  simp[check_storeorder_def]>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xlet_autop>>
  TOP_CASE_TAC>>gvs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xcon>>xsimpl>>
  gvs[PAIR_TYPE_def]
QED

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

val res = translate npbc_checkTheory.satisfies_npbc_aux_def;

Theorem satisfies_npbc_compute:
  satisfies_npbc w xsn ⇔
    case xsn of (xs,n) =>
    if n ≤ 0 then T else satisfies_npbc_aux w xs (Num n)
Proof
  namedCases_on `xsn` ["xs n"] >> simp[satisfies_npbc_def] >>
  Cases_on `n ≤ 0` >- (simp[] >> intLib.ARITH_TAC) >>
  `0 < Num n ∧ n = &(Num n)` by intLib.ARITH_TAC >>
  simp[npbc_checkTheory.satisfies_npbc_aux_correct] >> intLib.ARITH_TAC
QED

val res = translate satisfies_npbc_compute;

Theorem satisfies_npbc_side[local]:
  satisfies_npbc_side w xsn
Proof
  simp[fetch "-" "satisfies_npbc_side_def"] >> rpt strip_tac >>
  intLib.ARITH_TAC
QED

val _ = satisfies_npbc_side |> update_precondition;

val r = translate npbc_checkTheory.to_flat_d_def;

val res = translate npbc_checkTheory.mk_obj_vec_def;

val res = translate npbc_checkTheory.vec_lookup_d_def;
val res = translate npbc_checkTheory.check_obj_def;

(* A translated function applied to one argument, whatever its result type *)
Theorem Arrow_app_one:
  (a --> b) f fv ⇒
  ∀x xv. a x xv ⇒
  app (p:'ffi ffi_proj) fv [xv] emp (POSTv v. &b (f x) v)
Proof
  rw[app_def]>>
  metis_tac[Arrow_IMP_app_basic]
QED

(* vec_lookup_d applied to its first two arguments returns a closure *)
Theorem vec_lookup_d_app:
  a d dv ∧ VECTOR_TYPE a wv wvv ⇒
  app (p:'ffi ffi_proj) vec_lookup_d_v [dv; wvv] emp
    (POSTv v. &(NUM --> a) (vec_lookup_d d wv) v)
Proof
  rw[app_def]>>
  assume_tac (fetch "-" "vec_lookup_d_v_thm")>>
  drule Arrow_IMP_app_basic>>
  disch_then drule>>
  strip_tac>>
  irule app_basic_weaken>>
  first_assum (irule_at (Pos last))>>
  Cases>>
  simp[cfHeapsBaseTheory.POSTv_def,cond_def,SEP_EXISTS_THM]>>
  rw[]>>
  qexists_tac`emp`>>
  simp[SEP_CLAUSES]>>
  drule Arrow_IMP_app_basic>>
  disch_then drule>>
  simp[cfHeapsBaseTheory.POSTv_def,cond_def]
QED

Theorem merge_compute:
  mergesort$merge R xs ys = REVERSE (merge_tail F R xs ys [])
Proof
  simp[mllistTheory.mergetail_merge]
QED

val res = translate mergesortTheory.merge_tail_def;
val res = translate merge_compute;
val res = translate npbc_checkTheory.mk_cube_vec_def;
val res = translate npbc_checkTheory.check_cube_aux_def;
val res = translate npbc_checkTheory.check_cube_def;

Theorem check_cube_side[local]:
  check_cube_side w xsn
Proof
  simp[fetch "-" "check_cube_side_def"] >> rpt strip_tac >>
  intLib.ARITH_TAC
QED

val _ = check_cube_side |> update_precondition;

val res = translate npbc_checkTheory.check_sol_def;

val res = translate npbc_checkTheory.model_improving_def;

val res = translate npbc_checkTheory.neg_dom_subst_def;
val res = translate npbc_checkTheory.dom_subgoals_def;

val res = translate sat_slot_aux_def;
val res = translate cube_slot_aux_def;
val res = translate sat_slot_def;
val res = translate cube_slot_def;
val res = translate sol_free_ok_def;
val res = translate sol_cw_ok_def;
val res = translate sol_fun_def;
val res = translate check_sol_slots_def;

Theorem sat_slot_aux_side[local]:
  ∀wv cs vs i len r.
  len ≤ length cs ∧ len ≤ length vs ⇒
  sat_slot_aux_side wv cs vs i len r
Proof
  ho_match_mp_tac sat_slot_aux_ind>>
  rw[]>>
  simp[Once (fetch "-" "sat_slot_aux_side_def")]>>
  rw[]>>
  gvs[ml_translatorTheory.FALSE_def]
QED

Theorem cube_slot_aux_side[local]:
  ∀cv cs vs i len r.
  len ≤ length cs ∧ len ≤ length vs ⇒
  cube_slot_aux_side cv cs vs i len r
Proof
  ho_match_mp_tac cube_slot_aux_ind>>
  rw[]>>
  simp[Once (fetch "-" "cube_slot_aux_side_def")]>>
  rw[]>>
  gvs[AllCaseEqs(),ml_translatorTheory.FALSE_def]
QED

Theorem sat_slot_side:
  wf_slot s ⇒ sat_slot_side wv s
Proof
  Cases_on`s`>>
  rw[fetch "-" "sat_slot_side_def",wf_slot_def]>>
  irule sat_slot_aux_side>>
  simp[]
QED

Theorem cube_slot_side:
  wf_slot s ⇒ cube_slot_side cv s
Proof
  Cases_on`s`>>
  rw[fetch "-" "cube_slot_side_def",wf_slot_def]>>
  irule cube_slot_aux_side>>
  simp[]
QED

Definition every_sat_slot_def:
  (every_sat_slot wv [] ⇔ T) ∧
  (every_sat_slot wv (s::ss) ⇔ sat_slot wv s ∧ every_sat_slot wv ss)
End

Theorem every_sat_slot_EVERY:
  ∀ss. every_sat_slot wv ss ⇔ EVERY (sat_slot wv) ss
Proof
  Induct>>rw[every_sat_slot_def]
QED

val res = translate every_sat_slot_def;

Theorem every_sat_slot_side:
  ∀ss. EVERY wf_slot ss ⇒ every_sat_slot_side wv ss
Proof
  Induct>>
  rw[]>>
  simp[Once (fetch "-" "every_sat_slot_side_def"),sat_slot_side]
QED

val res = translate
  (check_obj_slots_def |> REWRITE_RULE[GSYM every_sat_slot_EVERY]);

(* The objective and solution checks walk the index once and return it
  without the IDs of deleted constraints *)
Quote add_cakeml:
  fun sat_inds_arr lno wv fml inds =
  case inds of [] => []
  | (i::is) =>
    (case Array.lookup fml Empty i of
      Empty => sat_inds_arr lno wv fml is
    | Stored cs vs d mc sm b =>
      if not b orelse d <= 0 orelse
        sat_slot_aux wv cs vs 0 (Vector.length cs) d
      then i :: sat_inds_arr lno wv fml is
      else raise Fail (format_failure lno
        "supplied assignment did not satisfy constraints or did not improve objective"))
End

Theorem sat_inds_arr_spec:
  ∀inds indsv.
  NUM lno lnov ∧
  VECTOR_TYPE BOOL wv wvv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "sat_inds_arr" (get_ml_prog_state()))
    [lnov; wvv; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &(EVERY (λi. sat_slot wv (lookup_core_only_list T fmlls i)) inds ∧
          LIST_TYPE NUM (reindex fmlls inds) v))
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧
          ¬EVERY (λi. sat_slot wv (lookup_core_only_list T fmlls i)) inds)))
Proof
  Induct>>
  rw[]>>
  xcf "sat_inds_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl>>simp[reindex_characterize,LIST_TYPE_def])>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el h fmllsv _`>>
  `fslot_TYPE (any_el h fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>xsimpl>>
    simp[lookup_core_only_list_def,sat_slot_def,reindex_characterize])>>
  qmatch_asmsub_rename_tac`any_el h fmlls Empty = Stored cs vs d mc sm b`>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv bv. ARRAY fmlv fmllsv * &BOOL (¬b ∨ d ≤ 0) bv`
  >- (xlog>>xsimpl>>rw[]>>gvs[]>>xapp>>xsimpl>>qexists_tac`d`>>simp[])>>
  xlet`POSTv bv. ARRAY fmlv fmllsv *
    &BOOL (¬b ∨ d ≤ 0 ∨ sat_slot_aux wv cs vs 0 (length cs) d) bv`
  >- (
    xlog>>xsimpl>>rw[]>>gvs[]>>
    xlet_autop>>
    xapp>>xsimpl>>
    qexistsl_tac[`wv`,`vs`,`d`,`length cs`,`cs`]>>
    gvs[wf_slot_def,sat_slot_aux_side])>>
  xif
  >- (
    `sat_slot wv (lookup_core_only_list T fmlls h)` by
      (Cases_on`b`>>gvs[lookup_core_only_list_def,core_slot_def,sat_slot_def])>>
    xlet`POSTve
      (λv. ARRAY fmlv fmllsv *
        &(EVERY (λi. sat_slot wv (lookup_core_only_list T fmlls i)) inds ∧
          LIST_TYPE NUM (reindex fmlls inds) v))
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧
          ¬EVERY (λi. sat_slot wv (lookup_core_only_list T fmlls i)) inds))`
    >- (xapp>>xsimpl)
    >- (xsimpl>>simp[EXISTS_NOT_EVERY])>>
    xcon>>xsimpl>>
    gvs[reindex_characterize,LIST_TYPE_def])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def,lookup_core_only_list_def,core_slot_def,sat_slot_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun check_obj_core_arr lno obj wm fml inds bopt =
  let
    val wv = mk_obj_vec wm
    val w = vec_lookup_d False wv
    val new = eval_obj obj w
    val inds' = sat_inds_arr lno wv fml inds
  in
    case bopt of
      None => Some (new, (w, inds'))
    | Some b => if b = new then Some (new, (w, inds')) else None
  end
End

Theorem check_obj_core_arr_spec:
  NUM lno lnov ∧
  obj_TYPE obj objv ∧
  LIST_TYPE (PAIR_TYPE NUM BOOL) wm wmv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv ∧
  OPTION_TYPE INT bopt boptv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_obj_core_arr" (get_ml_prog_state()))
    [lnov; objv; wmv; fmlv; indsv; boptv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &OPTION_TYPE (PAIR_TYPE INT (PAIR_TYPE (NUM --> BOOL) (LIST_TYPE NUM)))
          (OPTION_MAP (λ(n,w). (n, w, reindex fmlls inds))
            (check_obj_core obj wm fmlls inds bopt)) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ check_obj_core obj wm fmlls inds bopt = NONE)))
Proof
  rw[]>>
  xcf "check_obj_core_arr" (get_ml_prog_state ())>>
  simp[check_obj_core_def]>>
  rpt xlet_autop>>
  qmatch_asmsub_rename_tac`fv = Conv (SOME (TypeStamp «False» _)) []`>>
  xlet`POSTv w. ARRAY fmlv fmllsv *
    &(NUM --> BOOL) (vec_lookup_d F (mk_obj_vec wm)) w`
  >- (
    xapp_spec (vec_lookup_d_app |> INST_TYPE [alpha|->``:bool``])>>
    qexistsl_tac[`ARRAY fmlv fmllsv`,`mk_obj_vec wm`,`F`,`BOOL`]>>
    simp[]>>xsimpl)>>
  xlet_autop>>
  xlet`POSTve
    (λv. ARRAY fmlv fmllsv *
      &(EVERY (λi. sat_slot (mk_obj_vec wm)
          (lookup_core_only_list T fmlls i)) inds ∧
        LIST_TYPE NUM (reindex fmlls inds) v))
    (λe. ARRAY fmlv fmllsv *
      &(Fail_exn e ∧
        ¬EVERY (λi. sat_slot (mk_obj_vec wm)
          (lookup_core_only_list T fmlls i)) inds))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`mk_obj_vec wm`,`inds`,`fmlls`,`lno`]>>
    simp[])
  >- (xsimpl>>rw[]>>gvs[EVERY_MEM,EXISTS_MEM])>>
  simp[]>>
  Cases_on`bopt`>>gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def,PAIR_TYPE_def])>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def]
QED

Quote add_cakeml:
  fun cube_inds_arr lno cv fml inds =
  case inds of [] => []
  | (i::is) =>
    (case Array.lookup fml Empty i of
      Empty => cube_inds_arr lno cv fml is
    | Stored cs vs d mc sm b =>
      if not b orelse d <= 0 orelse
        cube_slot_aux cv cs vs 0 (Vector.length cs) d
      then i :: cube_inds_arr lno cv fml is
      else raise Fail (format_failure lno
        "supplied solution cube has conflicting assignments or does not satisfy constraints"))
End

Theorem cube_inds_arr_spec:
  ∀inds indsv.
  NUM lno lnov ∧
  VECTOR_TYPE NUM cv cvv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "cube_inds_arr" (get_ml_prog_state()))
    [lnov; cvv; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &(EVERY (λi. cube_slot cv (lookup_core_only_list T fmlls i)) inds ∧
          LIST_TYPE NUM (reindex fmlls inds) v))
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧
          ¬EVERY (λi. cube_slot cv (lookup_core_only_list T fmlls i)) inds)))
Proof
  Induct>>
  rw[]>>
  xcf "cube_inds_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl>>simp[reindex_characterize,LIST_TYPE_def])>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el h fmllsv _`>>
  `fslot_TYPE (any_el h fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>xsimpl>>
    simp[lookup_core_only_list_def,cube_slot_def,reindex_characterize])>>
  qmatch_asmsub_rename_tac`any_el h fmlls Empty = Stored cs vs d mc sm b`>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv bv. ARRAY fmlv fmllsv * &BOOL (¬b ∨ d ≤ 0) bv`
  >- (xlog>>xsimpl>>rw[]>>gvs[]>>xapp>>xsimpl>>qexists_tac`d`>>simp[])>>
  xlet`POSTv bv. ARRAY fmlv fmllsv *
    &BOOL (¬b ∨ d ≤ 0 ∨ cube_slot_aux cv cs vs 0 (length cs) d) bv`
  >- (
    xlog>>xsimpl>>rw[]>>gvs[]>>
    xlet_autop>>
    xapp>>xsimpl>>
    qexistsl_tac[`vs`,`d`,`length cs`,`cv`,`cs`]>>
    gvs[wf_slot_def,cube_slot_aux_side])>>
  xif
  >- (
    `cube_slot cv (lookup_core_only_list T fmlls h)` by
      (Cases_on`b`>>gvs[lookup_core_only_list_def,core_slot_def,cube_slot_def])>>
    xlet`POSTve
      (λv. ARRAY fmlv fmllsv *
        &(EVERY (λi. cube_slot cv (lookup_core_only_list T fmlls i)) inds ∧
          LIST_TYPE NUM (reindex fmlls inds) v))
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧
          ¬EVERY (λi. cube_slot cv (lookup_core_only_list T fmlls i)) inds))`
    >- (xapp>>xsimpl)
    >- (xsimpl>>simp[EXISTS_NOT_EVERY])>>
    xcon>>xsimpl>>
    gvs[reindex_characterize,LIST_TYPE_def])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def,lookup_core_only_list_def,core_slot_def,cube_slot_def]>>
  metis_tac[]
QED

Quote add_cakeml:
  fun check_sol_core_arr lno wm free fml inds =
  if sol_free_ok wm free then
    let
      val cv = mk_cube_vec wm free
      val cw = vec_lookup_d 0 cv
    in
      if sol_cw_ok cw wm then
        let val inds' = cube_inds_arr lno cv fml inds in
          Some (sol_fun cw, inds')
        end
      else None
    end
  else None
End

Theorem check_sol_core_arr_spec:
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE NUM BOOL) wm wmv ∧
  SPTREE_SPT_TYPE UNIT_TYPE free freev ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  LIST_TYPE NUM inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_sol_core_arr" (get_ml_prog_state()))
    [lnov; wmv; freev; fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &OPTION_TYPE (PAIR_TYPE (NUM --> BOOL) (LIST_TYPE NUM))
          (OPTION_MAP (λf. (f, reindex fmlls inds))
            (check_sol_core wm free fmlls inds)) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ check_sol_core wm free fmlls inds = NONE)))
Proof
  rw[]>>
  xcf "check_sol_core_arr" (get_ml_prog_state ())>>
  simp[check_sol_core_def]>>
  xlet_autop>>
  reverse xif
  >- (xcon>>xsimpl>>simp[OPTION_TYPE_def])>>
  rpt xlet_autop>>
  xlet`POSTv cw. ARRAY fmlv fmllsv *
    &(NUM --> NUM) (vec_lookup_d 0 (mk_cube_vec wm free)) cw`
  >- (
    xapp_spec (vec_lookup_d_app |> INST_TYPE [alpha|->``:num``])>>
    qexistsl_tac[`ARRAY fmlv fmllsv`,`mk_cube_vec wm free`,`0`,`NUM`]>>
    xsimpl)>>
  xlet_autop>>
  reverse xif
  >- (xcon>>xsimpl>>simp[OPTION_TYPE_def])>>
  xlet`POSTve
    (λv. ARRAY fmlv fmllsv *
      &(EVERY (λi. cube_slot (mk_cube_vec wm free)
          (lookup_core_only_list T fmlls i)) inds ∧
        LIST_TYPE NUM (reindex fmlls inds) v))
    (λe. ARRAY fmlv fmllsv *
      &(Fail_exn e ∧
        ¬EVERY (λi. cube_slot (mk_cube_vec wm free)
          (lookup_core_only_list T fmlls i)) inds))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`inds`,`fmlls`,`mk_cube_vec wm free`,`lno`]>>
    simp[])
  >- (xsimpl>>rw[]>>gvs[EVERY_MEM,EXISTS_MEM])>>
  xlet`POSTv fv. ARRAY fmlv fmllsv *
    &(NUM --> BOOL)
      (sol_fun (vec_lookup_d 0 (mk_cube_vec wm free))) fv`
  >- (
    xapp_spec (MATCH_MP Arrow_app_one (fetch "-" "sol_fun_v_thm"))>>
    xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def,PAIR_TYPE_def]
QED

val res = translate npbc_checkTheory.find_scope_1_def;

val res = translate npbc_checkTheory.update_bound_def;
val res = translate npbc_checkTheory.update_dbound_def;

Quote add_cakeml:
  fun core_from_inds_arr lno fml is =
  case is of [] => fml
  | (i::is) =>
    (case Array.lookup fml Empty i of
      Empty => raise Fail (format_failure lno
        "core transfer given invalid ids")
    | Stored cs vs d mc sm b =>
      if b then core_from_inds_arr lno fml is
      else
        core_from_inds_arr lno
          (Array.updateResize fml Empty i (Stored cs vs d mc sm True)) is)
End

Theorem core_from_inds_arr_spec:
  ∀inds indsv fmlv fmlls fmllsv.
  NUM lno lnov ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
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
            (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv') res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
         core_from_inds fmlls inds = NONE)))
Proof
  simp[GSYM core_from_inds_skip_eq]>>
  Induct>>
  rw[]>>
  xcf "core_from_inds_arr" (get_ml_prog_state ())>>
  simp[core_from_inds_skip_def]>>
  fs[LIST_TYPE_def]>>xmatch
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el h fmllsv _`>>
  `fslot_TYPE (any_el h fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el h fmlls Empty`>>gvs[fslot_TYPE_def,SLOT_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_refl])>>
  xmatch>>
  simp[core_slot_def]>>
  xif
  >- (xapp>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  xapp>>
  simp[]>>
  irule LIST_REL_update_resize>>
  fs[wf_slot_def]>>
  simp[fslot_TYPE_def,SLOT_TYPE_def,set_core_slot_def,wf_slot_def]>>
  EVAL_TAC
QED

Quote add_cakeml:
  fun core_from_range_arr fml w id =
    if w < id andalso w < Array.length fml then
      ((case Unsafe.sub fml w of
        Empty => ()
      | Stored cs vs d mc sm b =>
        if b then ()
        else Unsafe.update fml w (Stored cs vs d mc sm True));
      core_from_range_arr fml (w + 1) id)
    else ()
End

Theorem core_from_range_arr_spec:
  ∀fmlls w id fmllsv wv.
  NUM w wv ∧
  NUM id idv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "core_from_range_arr" (get_ml_prog_state()))
    [fmlv; wv; idv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL fslot_TYPE (core_from_range fmlls w id) fmllsv') )
Proof
  ho_match_mp_tac core_from_range_ind>>
  rw[]>>
  xcf "core_from_range_arr" (get_ml_prog_state ())>>
  `LENGTH fmlls = LENGTH fmllsv` by metis_tac[LIST_REL_LENGTH]>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (w < id ∧ w < LENGTH fmlls) v`
  >- (
    xlog>>xsimpl>>
    rw[]
    >- (
      rpt xlet_autop>>
      xapp>>xsimpl>>
      qexistsl_tac[`&LENGTH fmllsv`,`&w`]>>
      gvs[NUM_def])>>
    gvs[])>>
  simp[Once core_from_range_def]>>
  reverse xif
  >- (xcon>>xsimpl)>>
  xlet_autop>>
  `any_el w fmlls Empty = EL w fmlls` by simp[any_el_ALT]>>
  `fslot_TYPE (EL w fmlls) (EL w fmllsv)` by gvs[LIST_REL_EL_EQN]>>
  namedCases_on`EL w fmlls`["","cs vs d mc sm b"]>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def,core_slot_def]
  >- (
    xlet`POSTv u. ARRAY fmlv fmllsv * &UNIT_TYPE () u`
    >- (xmatch>>xcon>>xsimpl)>>
    xlet_autop>>
    xapp>>xsimpl)>>
  Cases_on`b`>>gvs[]
  >- (
    xlet`POSTv u. ARRAY fmlv fmllsv * &UNIT_TYPE () u`
    >- (
      xmatch>>xif>>
      qexists_tac`T`>>simp[]>>
      xcon>>xsimpl)>>
    xlet_autop>>
    xapp>>xsimpl)>>
  xlet`POSTv u. SEP_EXISTS fmllsv'. ARRAY fmlv fmllsv' *
    &(UNIT_TYPE () u ∧
      LIST_REL fslot_TYPE
        (update_resize fmlls Empty (Stored cs vs d mc sm T) w) fmllsv')`
  >- (
    xmatch>>xif>>
    qexists_tac`F`>>simp[]>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    qexists_tac`w`>>
    simp[update_resize_def]>>
    rw[]>>
    match_mp_tac EVERY2_LUPDATE_same>>
    gvs[fslot_TYPE_def,SLOT_TYPE_def,wf_slot_def]>>
    EVAL_TAC)>>
  gvs[set_core_slot_def]>>
  xlet_autop>>
  xapp>>xsimpl
QED

Quote add_cakeml:
  fun all_core_arr fml ls iacc =
  case ls of
    [] => Some (List.rev iacc)
  | (i::is) =>
  case Array.lookup fml Empty i of
    Empty => all_core_arr fml is iacc
  | Stored cs vs d mc sm b' =>
      if b' then all_core_arr fml is (i::iacc)
      else None
End

Theorem all_core_arr_spec:
  ∀inds indsv fmlls fmlv iacc iaccv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
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
    simp[all_core_list_def,LIST_TYPE_def,OPTION_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el h fmllsv _`>>
  `fslot_TYPE (any_el h fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  simp[all_core_list_def]>>
  Cases_on`any_el h fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def,core_slot_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  xmatch>>
  xif>>rpt xlet_autop
  >- (
    xapp>>xsimpl>>
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

Quote add_cakeml:
  fun check_change_obj_arr lno b fml id obj fc' pfs assg st =
  case obj of None =>
    raise Fail (format_failure lno ("no objective to change"))
  | Some fc =>
    let
    val csubs = change_obj_subgoals (mk_tar_obj b fc) fc'
    val bb = True
    val e = []
    val cpfs = extract_clauses_arr lno emp_vec bb fml csubs pfs e in
    case check_subproofs_arr lno cpfs bb fml id id assg st of
       (fml', (id', (assg', st'))) =>
      let val u = rollback_arr fml' id id' in
        if do_change_check pfs csubs then
          (fml',(mk_diff_obj b fc fc', (id', (assg', st'))))
       else raise Fail (format_failure lno ("objective change subproofs did not cover all subgoals. Expected: #[1-2]"))
       end
    end
End

Theorem check_change_obj_arr_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM id idv ∧
  obj_TYPE obj objv ∧
  (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT) fc fcv ∧
  pfs_TYPE pfs pfsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_change_obj_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; idv; objv; fcv; pfsv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          case check_change_obj_list b fmlls id obj fc pfs assg st of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        & (Fail_exn e ∧
          check_change_obj_list b fmlls id obj fc pfs assg st = NONE)))
Proof
  rw[]>>
  xcf "check_change_obj_arr" (get_ml_prog_state ())>>
  simp[check_change_obj_list_def]>>
  namedCases_on`obj`["","ofc"]>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def])>>
  rpt xlet_autop>>
  xlet`POSTve
    (λv.
      ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      &(case extract_clauses_list emp_vec T fmlls
          (change_obj_subgoals (mk_tar_obj b ofc) fc) pfs [] of
          NONE => F
        | SOME res => check_subproof_TYPE res v))
    (λe.
      ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      &(Fail_exn e ∧
        extract_clauses_list emp_vec T fmlls
          (change_obj_subgoals (mk_tar_obj b ofc) fc) pfs [] = NONE))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp_vec`,`change_obj_subgoals (mk_tar_obj b ofc) fc`,`pfs`,
      `fmlls`,`T`,`[]`,`lno`]>>
    simp[LIST_TYPE_def,fetch "-" "emp_vec_v_thm"]>>
    EVAL_TAC)
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`extract_clauses_list emp_vec T fmlls
    (change_obj_subgoals (mk_tar_obj b ofc) fc) pfs []`>>gvs[]>>
  rename1`check_subproof_TYPE cpfs _`>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      &(case check_subproofs_list cpfs T fmlls id id assg st of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM)) res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      &(Fail_exn e ∧ check_subproofs_list cpfs T fmlls id id assg st = NONE))`
  >- (
    xapp>>xsimpl>>
    conj_tac >- EVAL_TAC>>
    metis_tac[])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_subproofs_list cpfs T fmlls id id assg st`>>gvs[]>>
  qmatch_asmsub_rename_tac`check_subproofs_list _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def]
QED


val res = translate npbc_checkTheory.add_lit_def;
val res = translate npbc_checkTheory.v_iff_npbc_def;
val res = translate npbc_checkTheory.change_pres_subgoals_def;
val res = translate npbc_checkTheory.pres_only_def;
val res = translate npbc_checkTheory.update_pres_def;

Quote add_cakeml:
  fun check_change_pres_arr lno b fml id pres v c pfs assg st =
  case pres of None =>
    raise Fail (format_failure lno ("no projection set to change"))
  | Some pres =>
    if pres_only c pres v then
    let
    val csubs = change_pres_subgoals v c
    val bb = True
    val e = []
    val cpfs = extract_clauses_arr lno emp_vec bb fml csubs pfs e in
    case check_subproofs_arr lno cpfs bb fml id id assg st of
       (fml', (id', (assg', st'))) =>
      let val u = rollback_arr fml' id id' in
        if do_change_check pfs csubs then
          (fml',(update_pres b v pres, (id', (assg', st'))))
       else raise Fail (format_failure lno ("projection set change subproofs did not cover all subgoals. Expected: #[1-2]"))
       end
    end
    else raise Fail (format_failure lno ("defining constraint must mention only variables in the projection set (less variable itself)"))
End

Theorem check_change_pres_arr_spec:
  NUM lno lnov ∧
  BOOL b bv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM id idv ∧
  pres_TYPE pres presv ∧
  NUM vx vxv ∧
  constraint_TYPE c cv ∧
  pfs_TYPE pfs pfsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_change_pres_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; idv; presv; vxv; cv; pfsv; assgv; stv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        &(
          case check_change_pres_list b fmlls id pres vx c pfs assg st of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (SPTREE_SPT_TYPE UNIT_TYPE)
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        & (Fail_exn e ∧
          check_change_pres_list b fmlls id pres vx c pfs assg st = NONE)))
Proof
  rw[]>>
  xcf "check_change_pres_arr" (get_ml_prog_state ())>>
  simp[check_change_pres_list_def]>>
  namedCases_on`pres`["","pr"]>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def])>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def])>>
  rpt xlet_autop>>
  xlet`POSTve
    (λv.
      ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      &(case extract_clauses_list emp_vec T fmlls
          (change_pres_subgoals vx c) pfs [] of
          NONE => F
        | SOME res => check_subproof_TYPE res v))
    (λe.
      ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      &(Fail_exn e ∧
        extract_clauses_list emp_vec T fmlls
          (change_pres_subgoals vx c) pfs [] = NONE))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp_vec`,`change_pres_subgoals vx c`,`pfs`,
      `fmlls`,`T`,`[]`,`lno`]>>
    simp[LIST_TYPE_def,fetch "-" "emp_vec_v_thm"]>>
    EVAL_TAC)
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`extract_clauses_list emp_vec T fmlls
    (change_pres_subgoals vx c) pfs []`>>gvs[]>>
  rename1`check_subproof_TYPE cpfs _`>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      &(case check_subproofs_list cpfs T fmlls id id assg st of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM)) res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      &(Fail_exn e ∧ check_subproofs_list cpfs T fmlls id id assg st = NONE))`
  >- (
    xapp>>xsimpl>>
    conj_tac >- EVAL_TAC>>
    metis_tac[])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_subproofs_list cpfs T fmlls id id assg st`>>gvs[]>>
  qmatch_asmsub_rename_tac`check_subproofs_list _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[ARRAY_NUM_ARRAY_refl,Fail_exn_def]
QED

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
  check_tcb_ord pc ⇔
    ¬pc.tcb ∧
    case pc.ord of NONE => T | SOME _ => F
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
  obj_update pc bound' dbound' =
    pc with
          <| bound := bound';
             dbound := dbound' |>
End

val res = translate obj_update_def;

Definition change_obj_update_def:
  change_obj_update pc fc' =
  pc with obj := SOME fc'
End

val res = translate change_obj_update_def;

Definition assert_obj_update_def:
  assert_obj_update pc dbound' =
  pc with dbound := dbound'
End

val res = translate assert_obj_update_def;

Definition change_pres_update_def:
  change_pres_update pc pres' =
  pc with pres := SOME pres'
End

val res = translate change_pres_update_def;

Definition sol_update_def:
  sol_update pc bound' dbound' count =
    pc with
          <| bound := bound';
             dbound := dbound';
             enum := pc.enum + count |>
End

val res = translate sol_update_def;

Definition npbc_obj_string_def:
  (npbc_obj_string (xs,i:int) =
    concat [
      npbc_lhs_string xs;
      « »;
      toString  i])
End

Definition err_obj_check_string_def:
  err_obj_check_string fc fc' =
  case fc of NONE => «objective check failed, no objective available»
  | SOME fc =>
    concat[
    «objective check failed, expect: »;
    npbc_obj_string fc';
    « got (in checker): »;
    npbc_obj_string fc]
End

val res = translate npbc_obj_string_def;
val res = translate err_obj_check_string_def;
val res = translate npbc_checkTheory.eq_obj_def;
val res = translate npbc_checkTheory.check_eq_obj_def;

Quote add_cakeml:
  fun fold_update_resize_bitset ls acc =
    case ls of
      [] => acc
    | (cx::xs) =>
      case cx of (c,x) =>
      if x < Word8Array.length acc
      then
        (Unsafe.w8update acc x w8o;
        fold_update_resize_bitset xs acc)
      else
        let
        val arr = Word8Array.array (2*x+1) w8z
        val u = Word8Array.copy acc 0 (Word8Array.length acc) arr 0 in
          (Unsafe.w8update arr x w8o;
          fold_update_resize_bitset xs arr)
        end
End

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

Quote add_cakeml:
  fun mk_vomap_arr n fc =
  let
  val acc = Word8Array.array n w8z
  val acc = fold_update_resize_bitset (fst fc) acc in
    Word8Array.substring acc 0 (Word8Array.length acc)
  end
End

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

val res = translate (npbc_checkTheory.guard_ord_t_def |> SIMP_RULE std_ss[MEMBER_INTRO]);

val res = translate (npbc_checkTheory.mk_ordsub_def);

Definition err_pres_check_string_def:
  err_pres_check_string (fc:num_set option) (fc':num_set) =
  case fc of NONE => «preserved set check failed, no preserved set available»
  | SOME fc =>
    concat[
    «preserved set check failed, expect: »;
    concatWith « » (MAP (toString o FST) (toSortedAList fc'));
    « got (in checker): »;
    concatWith « » (MAP (toString o FST) (toSortedAList fc))]
End

val res = translate err_pres_check_string_def;
val res = translate npbc_checkTheory.check_eq_pres_def;

Definition obj_check_def:
  obj_check on ⇔ on = NONE
End

val res = translate obj_check_def;

Definition obj_chk_check_def:
  obj_chk_check on chk ⇔ on = NONE ∧ chk
End

val res = translate obj_chk_check_def;

val res = translate sptreeTheory.difference_def;
val res = translate sptreeTheory.inter_def;
val res = translate sptreeTheory.size_def;
val res = translate npbc_checkTheory.model_banning_def;
val res = translate npbc_checkTheory.cube_count_def;
val res = translate sptreeTheory.subspt_eq;
val res = translate npbc_checkTheory.free_ok_def;

Quote add_cakeml:
  fun mk_perm_arr vimap ls =
  case ls of
    [] => vimap
  | (n::ns) =>
    (case Array.lookup vimap Vnone n of
      Vcount k pinds ninds =>
        mk_perm_arr (Array.updateResize vimap Vnone n (Vtrack pinds ninds)) ns
    | _ => mk_perm_arr vimap ns)
End

Theorem mk_perm_arr_spec:
  ∀ls lsv vimap vimaplsv vimapv .
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  (LIST_TYPE NUM) ls lsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "mk_perm_arr" (get_ml_prog_state()))
    [vimapv ; lsv]
    (ARRAY vimapv vimaplsv)
    (POSTv v.
        SEP_EXISTS vimapv' vimaplsv'.
        ARRAY v vimaplsv' *
        &(
          LIST_REL vimapn_TYPE
            (mk_perm vimap ls) vimaplsv'))
Proof
  Induct>>rw[]>>
  xcf "mk_perm_arr" (get_ml_prog_state ())>>
  fs[mk_perm_def,LIST_TYPE_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`lv = any_el h vimaplsv _`>>
  `vimapn_TYPE (any_el h vimap Vnone) lv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,VENT_TYPE_def])>>
  Cases_on`any_el h vimap Vnone`>>
  gvs[VENT_TYPE_def]>>
  xmatch
  >- (xapp>>xsimpl)
  >- (xapp>>xsimpl)
  >- (
    rpt xlet_autop>>
    xlet_auto>>
    xapp>>xsimpl>>
    irule LIST_REL_update_resize>>
    simp[VENT_TYPE_def])>>
  xapp>>xsimpl
QED

(* The final check of a dominance step after its subproofs; rolls back
  the subproofs' constraints and returns the table *)
Quote add_cakeml:
  fun dom_check_arr lno fml id id' inds ht nfc pfs dsubs goals dindex idopt =
  case idopt of
    None =>
    (rollback_arr fml id id';
     if find_scope_1 dindex pfs then
       case red_cond_check_arr False fml inds id ht nfc pfs dsubs goals
           [dindex] of
         (None, ht') => ht'
       | (Some err, _) =>
         raise Fail (format_failure_2 lno ("dominance subproofs did not cover all subgoals. Info: " ^ err ^ ".") (print_subproofs_err dsubs goals))
     else
       raise Fail (format_failure_2 lno ("dominance subproofs did not cover all subgoals. Info: missing geq scope proof.") (print_subproofs_err dsubs goals)))
  | Some cid =>
    if check_contradiction_fml_arr False fml cid then
      (rollback_arr fml id id'; ht)
    else
      raise Fail (format_failure lno ("did not derive contradiction from index: " ^ Int.toString cid))
End

Theorem do_dom_check_NONE[local]:
  do_dom_check NONE fml rfml inds base ht goals extra pfs dsubs dindex =
  if find_scope_1 dindex pfs then
    red_cond_check F rfml inds base ht extra pfs dsubs goals [dindex]
  else (F,ht)
Proof
  simp[do_dom_check_def,red_cond_check_def]>>
  pairarg_tac>>
  rw[]>>
  gvs[]
QED

Theorem dom_check_arr_spec:
  NUM lno lnov ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM id idv ∧
  NUM id' id'v ∧
  LIST_TYPE NUM inds indsv ∧
  ht_TYPE bksv bkslsv ht htv ∧
  fslot_TYPE nfc nfcv ∧
  scpfs_TYPE pfs pfsv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) dsubs dsubsv ∧
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) goals goalsv ∧
  NUM dindex dindexv ∧
  OPTION_TYPE NUM idopt idoptv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "dom_check_arr" (get_ml_prog_state()))
    [lnov; fmlv; idv; id'v; indsv; htv; nfcv; pfsv; dsubsv; goalsv; dindexv;
      idoptv]
    (ARRAY fmlv fmllsv * ARRAY bksv bkslsv)
    (POSTve
      (λv.
        SEP_EXISTS fmllsv' bksv' bkslsv'.
        ARRAY fmlv fmllsv' * ARRAY bksv' bkslsv' *
        &(LIST_REL fslot_TYPE (rollback fmlls id id') fmllsv' ∧
          FST (do_dom_check idopt fmlls (rollback fmlls id id') inds id ht
            goals nfc pfs dsubs dindex) ∧
          ht_TYPE bksv' bkslsv'
            (SND (do_dom_check idopt fmlls (rollback fmlls id id') inds id ht
              goals nfc pfs dsubs dindex)) v))
      (λe.
        SEP_EXISTS fmllsv' bksv' bkslsv'.
        ARRAY fmlv fmllsv' * ARRAY bksv' bkslsv' *
        &(Fail_exn e ∧
          ¬FST (do_dom_check idopt fmlls (rollback fmlls id id') inds id ht
            goals nfc pfs dsubs dindex))))
Proof
  rw[]>>
  xcf "dom_check_arr" (get_ml_prog_state ())>>
  namedCases_on`idopt` ["","cid"]>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    simp[do_dom_check_NONE]>>
    xlet_autop>>
    qmatch_asmsub_rename_tac
      `LIST_REL fslot_TYPE (rollback fmlls id id') fmllsv1`>>
    xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>
      qexistsl_tac[`bksv`,`bkslsv`]>>
      xsimpl>>
      metis_tac[])>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv1 * SEP_EXISTS bksv1 bkslsv1.
      ARRAY bksv1 bkslsv1 *
      & ∃err. PAIR_TYPE (OPTION_TYPE STRING_TYPE) (ht_TYPE bksv1 bkslsv1)
        ((if FST (red_cond_check F (rollback fmlls id id') inds id ht nfc pfs
            dsubs goals [dindex]) then NONE else SOME err),
         SND (red_cond_check F (rollback fmlls id id') inds id ht nfc pfs dsubs
           goals [dindex])) v`
    >- (
      xapp>>xsimpl>>
      simp[LIST_TYPE_def]>>
      EVAL_TAC)>>
    qmatch_asmsub_abbrev_tac`PAIR_TYPE _ _ (_, SND rcc) _`>>
    PairCases_on`rcc`>>
    qpat_x_assum`Abbrev _`
      (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
    gvs[PAIR_TYPE_def]>>
    Cases_on`rcc0`>>
    fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      xvar>>xsimpl>>
      qexistsl_tac[`bksv1`,`bkslsv1`]>>
      xsimpl)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    qexistsl_tac[`bksv1`,`bkslsv1`]>>
    xsimpl>>
    metis_tac[])>>
  simp[do_dom_check_def]>>
  xlet_autop>>
  xlet`POSTv bv. ARRAY fmlv fmllsv * ARRAY bksv bkslsv *
    &BOOL (check_contradiction_fml_list F fmlls cid) bv`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`cid`,`fmlls`,`F`]>>
    simp[]>>
    EVAL_TAC)>>
  xif
  >- (
    xlet_autop>>
    xvar>>xsimpl>>
    qexistsl_tac[`bksv`,`bkslsv`]>>
    xsimpl)>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  qexistsl_tac[`bksv`,`bkslsv`]>>
  xsimpl>>
  metis_tac[]
QED

val res = translate neg_pos_slot_def;

(* A dominance step *)
Quote add_cakeml:
  fun check_dom_arr lno fml assg st inds vimap id cfg ht c s pfs idopt =
  case cfg of (pc,(vomap,_)) =>
  case get_ord pc of
    None =>
    raise Fail (format_failure lno "no order loaded for dominance step")
  | Some spo =>
  case neg_pos_slot c (get_tcb pc) False of (fc,(nfc,mv)) =>
  if check_pres (get_pres pc) s then
  if check_fresh_aspo_arr fc s (get_ord pc) vimap vomap then
    case get_set_indices_arr fml inds s vimap of (rinds,(inds',vimap')) =>
    let
      val ss = mk_subst rinds s
      val w = subst_fun ss
      val goals =
        case idopt of
          None => subst_indexes_arr ss True fml rinds
        | Some cid => []
    in
    case dom_subgoals spo w c (get_obj pc) of (dsubs,(dscopes,dindex)) =>
    let val cpfs = extract_scopes_arr lno dscopes ss False fml dsubs pfs in
    case store_slot_arr fml nfc mv id assg st of
      (fml_not_c,(id1,(assg1,st1))) =>
    case check_scopes_arr lno cpfs False fml_not_c id id1 assg1 st1 of
      (fml',(id',(assg',st'))) =>
      let
        val ht' =
          dom_check_arr lno fml' id id' inds' ht nfc pfs dsubs goals dindex
            idopt
      in
      case store_ind_arr fml' fc mv id' inds' vimap' assg' st' of
        (fml'',(inds'',(vimap'',(id'',(assg'',st''))))) =>
        (fml'', (assg'', (st'', (inds'', (vimap'', (id'', (cfg, ht')))))))
      end
    end
    end
  else raise Fail (format_failure lno ("freshness check failed on auxiliary variables"))
  else raise Fail (format_failure lno ("domain of substitution must not mention projection set"))
End

val NPBC_CHECK_CSTEP_TYPE_def = theorem "NPBC_CHECK_CSTEP_TYPE_def";

Theorem check_dom_arr_spec:
  NUM lno lnov ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM st stv ∧
  (LIST_TYPE NUM) inds indsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  NUM id idv ∧
  cfg_TYPE (pc,vomap,cw) cfgv ∧
  constraint_TYPE c cv ∧
  subst_raw_TYPE s sv ∧
  scpfs_TYPE pfs pfsv ∧
  OPTION_TYPE NUM idopt idoptv ∧
  fml_bound fmlls (LENGTH assg) ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_dom_arr" (get_ml_prog_state()))
    [lnov; fmlv; assgv; stv; indsv; vimapv; idv; cfgv; htv; cv; sv; pfsv;
      idoptv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        &(
          case check_cstep_list (Dom c s pfs idopt)
            fmlls assg st inds vimap id (pc,vomap,cw) ht of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
              (PAIR_TYPE NUM
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                  (PAIR_TYPE NUM
                    (PAIR_TYPE cfg_TYPE (ht_TYPE bksv' bkslsv')))))))
                res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        & (Fail_exn e ∧
          check_cstep_list (Dom c s pfs idopt)
            fmlls assg st inds vimap id (pc,vomap,cw) ht = NONE)))
Proof
  rw[]>>
  xcf "check_dom_arr" (get_ml_prog_state ())>>
  simp[check_cstep_list_def]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[get_ord_def]>>
  Cases_on`pc.ord`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rename1`ords_TYPE spo _`>>
  rpt xlet_autop>>
  gvs[get_tcb_def]>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv bkslsv *
    &PAIR_TYPE NPBC_SLOT_SLOT_TYPE (PAIR_TYPE NPBC_SLOT_SLOT_TYPE NUM)
      (neg_pos_slot c pc.tcb F) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`F`,`pc.tcb`,`c`]>>
    simp[]>>
    EVAL_TAC)>>
  gvs[neg_pos_slot_enc,PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  gvs[get_pres_def]>>
  xlet_auto >- (xsimpl>>simp (eq_lemmas()))>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet_autop>>
  gvs[get_ord_def]>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet_auto
  >- (xsimpl>>rw[]>>first_assum (irule_at Any)>>xsimpl)>>
  `∃rinds inds1 vimap1.
    get_set_indices fmlls inds s vimap = (rinds,inds1,vimap1)` by
    metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  qmatch_asmsub_rename_tac`LIST_REL vimapn_TYPE vimap1 vimaplsv1`>>
  qmatch_goalsub_rename_tac`ARRAY vimapv1 vimaplsv1`>>
  xmatch>>
  xlet_auto >- (xsimpl>>simp (eq_lemmas()))>>
  xlet`POSTv wv. ARRAY vimapv1 vimaplsv1 * ARRAY fmlv fmllsv *
    NUM_ARRAY assgv assg * ARRAY bksv bkslsv *
    &(NUM --> OPTION_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM)))
      (subst_fun (mk_subst rinds s)) wv`
  >- (
    xapp_spec (MATCH_MP Arrow_app_one (fetch "-" "subst_fun_v_thm"))>>
    qexistsl_tac[
      `ARRAY vimapv1 vimaplsv1 * ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        ARRAY bksv bkslsv`,
      `mk_subst rinds s`]>>
    xsimpl)>>
  xlet`POSTv gv. ARRAY vimapv1 vimaplsv1 * ARRAY fmlv fmllsv *
    NUM_ARRAY assgv assg * ARRAY bksv bkslsv *
    &LIST_TYPE (PAIR_TYPE NUM constraint_TYPE)
      (case idopt of
        NONE => subst_indexes (mk_subst rinds s) T fmlls rinds
      | SOME _ => []) gv`
  >- (
    Cases_on`idopt`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      xlet_autop>>
      xapp>>xsimpl>>
      qexistsl_tac[`mk_subst rinds s`,`rinds`,`fmlls`,`T`]>>
      simp[]>>
      EVAL_TAC)>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def])>>
  xlet_autop>>
  gvs[get_obj_def]>>
  xlet_autop>>
  `∃dsubs dscopes dindex.
    dom_subgoals spo (subst_fun (mk_subst rinds s)) c pc.obj =
    (dsubs,dscopes,dindex)` by metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  `∃fml1 id1 assg1 st1.
    store_slot fmlls (enc (not c) F) (max_var (FST c)) id assg st =
    (fml1,id1,assg1,st1)` by metis_tac[PAIR]>>
  simp[]>>
  xlet`POSTve
    (λv. ARRAY vimapv1 vimaplsv1 * ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      ARRAY bksv bkslsv *
      &(case extract_scopes_list dscopes (mk_subst rinds s) F fmlls dsubs pfs of
          NONE => F
        | SOME res => check_scope_TYPE res v))
    (λe. ARRAY vimapv1 vimaplsv1 * ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      ARRAY bksv bkslsv *
      &(Fail_exn e ∧
        extract_scopes_list dscopes (mk_subst rinds s) F fmlls dsubs pfs = NONE))`
  >- (
    xapp>>xsimpl>>
    `BOOL F (Conv (SOME (TypeStamp «False» 0)) [])` by EVAL_TAC>>
    qexistsl_tac[`dscopes`,`mk_subst rinds s`,`dsubs`,`pfs`,`fmlls`,`F`,`lno`]>>
    simp[])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`extract_scopes_list dscopes (mk_subst rinds s) F fmlls dsubs pfs`>>
  gvs[]>>
  rename1`check_scope_TYPE cpfs _`>>
  qmatch_asmsub_rename_tac`NPBC_SLOT_SLOT_TYPE (enc (not c) F) ncv`>>
  `fslot_TYPE (enc (not c) F) ncv` by simp[fslot_TYPE_def]>>
  xlet_auto
  >- (xsimpl>>rw[]>>first_assum (irule_at Any)>>xsimpl)>>
  drule_at (Pos last) fml_bound_store_slot>>
  impl_tac >- metis_tac[slot_bound_enc_max_var,max_var_not]>>
  strip_tac>>
  gvs[PAIR_TYPE_def]>>
  rename1`store_slot _ _ _ _ _ _ = (_,_,assg1,_)`>>
  qmatch_asmsub_rename_tac`LIST_REL fslot_TYPE fml1 fmllsv1`>>
  xmatch>>
  xlet_autop>>
  qmatch_goalsub_rename_tac`NUM_ARRAY assgv1 assg1 * ARRAY fmlv1 fmllsv1`>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv1 vimaplsv1 * ARRAY bksv bkslsv *
      &(case check_scopes_list cpfs F fml1 id id1 assg1 st1 of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE NUM
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv') NUM)) res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv1 vimaplsv1 * ARRAY bksv bkslsv *
      &(Fail_exn e ∧
        check_scopes_list cpfs F fml1 id id1 assg1 st1 = NONE))`
  >- (
    xapp>>xsimpl>>
    `BOOL F (Conv (SOME (TypeStamp «False» 0)) [])` by EVAL_TAC>>
    qexistsl_tac[`ARRAY vimapv1 vimaplsv1 * ARRAY bksv bkslsv`,`st1`,`cpfs`,
      `id`,`id1`,`fml1`,
      `F`,`assg1`,`lno`]>>
    simp[]>>xsimpl>>
    rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_scopes_list cpfs F fml1 id id1 assg1 st1`>>gvs[]>>
  qmatch_asmsub_rename_tac`check_scopes_list _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
  qmatch_asmsub_rename_tac
    `check_scopes_list _ _ _ _ _ _ _ = SOME (fml2,id2,assg2,st2)`>>
  qmatch_asmsub_rename_tac`LIST_REL fslot_TYPE fml2 fmllsv2`>>
  xmatch>>
  qmatch_goalsub_rename_tac`ARRAY fmlv2 fmllsv2 * NUM_ARRAY assgv2 assg2`>>
  qabbrev_tac`goals =
    case idopt of
      NONE => subst_indexes (mk_subst rinds s) T fmlls rinds
    | SOME _ => []`>>
  rename1`NUM id0 idv`>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmllsv3 bksv3 bkslsv3.
      ARRAY fmlv2 fmllsv3 * NUM_ARRAY assgv2 assg2 * ARRAY vimapv1 vimaplsv1 *
      ARRAY bksv3 bkslsv3 *
      &(LIST_REL fslot_TYPE (rollback fml2 id0 id2) fmllsv3 ∧
        FST (do_dom_check idopt fml2 (rollback fml2 id0 id2) inds1 id0 ht
          goals (enc (not c) F) pfs dsubs dindex) ∧
        ht_TYPE bksv3 bkslsv3
          (SND (do_dom_check idopt fml2 (rollback fml2 id0 id2) inds1 id0 ht
            goals (enc (not c) F) pfs dsubs dindex)) v))
    (λe.
      SEP_EXISTS fmllsv3 bksv3 bkslsv3.
      ARRAY fmlv2 fmllsv3 * NUM_ARRAY assgv2 assg2 * ARRAY vimapv1 vimaplsv1 *
      ARRAY bksv3 bkslsv3 *
      &(Fail_exn e ∧
        ¬FST (do_dom_check idopt fml2 (rollback fml2 id0 id2) inds1 id0 ht
          goals (enc (not c) F) pfs dsubs dindex)))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`NUM_ARRAY assgv2 assg2 * ARRAY vimapv1 vimaplsv1`,`pfs`,
      `enc (not c) F`,`inds1`,`idopt`,`id2`,`id0`,`ht`,`goals`,`fml2`,`dsubs`,
      `dindex`,`bksv`,`bkslsv`,`lno`]>>
    simp[]>>xsimpl>>
    rw[]
    >- (
      qpat_assum`ht_TYPE _ _ (SND _) _` (irule_at Any)>>
      xsimpl)>>
    qmatch_goalsub_rename_tac`ARRAY bb bbl ==>> _`>>
    qexistsl_tac[`bb`,`bbl`]>>
    xsimpl)
  >- (
    xsimpl>>
    qx_genl_tac[`e`,`fl`,`bb`,`bbl`]>>
    strip_tac>>
    qexistsl_tac[`fmlv2`,`fl`,`assgv2`,`assg2`,`vimapv1`,`vimaplsv1`,`bb`,
      `bbl`]>>
    conj_tac >- (pairarg_tac>>gvs[])>>
    xsimpl)>>
  qmatch_asmsub_abbrev_tac`ht_TYPE _ _ (SND ddc) _`>>
  PairCases_on`ddc`>>
  qpat_x_assum`Abbrev _`
    (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
  gvs[]>>
  qmatch_asmsub_rename_tac
    `LIST_REL fslot_TYPE (rollback fml2 id0 id2) fmllsv3`>>
  `∃fml4 inds4 vimap4 id4 assg4 st4.
    store_ind (rollback fml2 id0 id2) (enc c pc.tcb) (max_var (FST c))
      id2 inds1 vimap1 assg2 st2 = (fml4,inds4,vimap4,id4,assg4,st4)` by
    metis_tac[PAIR]>>
  simp[]>>
  qmatch_asmsub_rename_tac`NPBC_SLOT_SLOT_TYPE (enc c pc.tcb) fcv`>>
  `fslot_TYPE (enc c pc.tcb) fcv` by simp[fslot_TYPE_def]>>
  xlet`POSTv v.
    SEP_EXISTS fmlv4 fmllsv4 assgv4 vimapv4 vimaplsv4.
    ARRAY fmlv4 fmllsv4 * NUM_ARRAY assgv4 assg4 * ARRAY vimapv4 vimaplsv4 *
    ARRAY bksv3 bkslsv3 *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv4 ∧ v = fmlv4)
      (PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv4 ∧ v = vimapv4)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg4 ∧ v = assgv4) NUM))))
      (fml4,inds4,vimap4,id4,assg4,st4) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY bksv3 bkslsv3`,`vimap1`,`st2`,`enc c pc.tcb`,
      `max_var (FST c)`,`inds1`,`id2`,`rollback fml2 id0 id2`,`assg2`]>>
    simp[slot_bound_enc_max_var]>>
    xsimpl>>
    rpt strip_tac>>
    gvs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  qexistsl_tac[`bksv3`,`bkslsv3`]>>
  xsimpl
QED

Quote add_cakeml:
  fun check_cstep_arr lno cstep fml assg st inds vimap id cfg ht =
  case cfg of (pc,(vomap,cw)) =>
  case cstep of
    Dom c s pfs idopt =>
      check_dom_arr lno fml assg st inds vimap id cfg ht c s pfs idopt
  | Sstep sstep => (
    case check_sstep_arr lno sstep fml inds id vimap cfg assg st ht of
      (fml',(inds',(vimap',(id',(assg',(st',ht')))))) =>
      (fml',(assg',(st',(inds',(vimap',(id', (cfg, ht'))))))))
  | Checkeddelete n s pfs idopt => (
    if check_tcb_idopt_pc pc idopt
    then
      let
        val fc = lookup_core_only_err_arr lno True fml n
        val ht = ht_del_arr fml [n] ht
      in
        (delete_arr n fml;
        case
          check_red_arr lno (get_pres pc) (get_ord pc) (get_obj pc) True
            (get_tcb pc) fml inds id
            fc (slot_max_var fc) s pfs idopt vimap vomap assg st ht of
            (fml',(inds',(vimap',(id',(assg',(st',ht')))))) =>
            (fml',(assg',(st',(inds',(vimap',(id', (cfg, ht'))))))))
      end
    else raise Fail
      (format_failure lno
        "invalid proof state for checked deletion"))
  | Uncheckeddelete ls => (
    let
      val cfg' =
        if get_chk pc then (set_chk pc False, (vomap, cw)) else cfg
      val ht' = ht_del_arr fml ls ht
    in
    if check_tcb_ord pc then
      (list_delete_arr ls fml;
        (fml, (assg, (st, (inds, (vimap, (id, (cfg', ht'))))))))
    else
      case all_core_arr fml inds [] of None =>
        raise Fail (format_failure lno
        "not all constraints in core")
      | Some inds' =>
        (list_delete_arr ls fml;
          (fml, (assg, (st, (inds', (vimap, (id, (cfg', ht'))))))))
    end)
  | Transfer ls => (
      let val fml' = core_from_inds_arr lno fml ls in
        (fml', (assg, (st, (inds, (vimap, (id, (cfg, ht)))))))
      end)
  | Strengthentocore b => (
      if b
      then
        (core_from_range_arr fml cw id;
          (fml, (assg, (st, (inds, (vimap, (id,
            ((set_tcb pc b, (vomap, id)), ht))))))))
      else
        (fml, (assg, (st, (inds, (vimap, (id,
          ((set_tcb pc b, (vomap, cw)), ht))))))))
  | Loadorder nn xs =>
    (case Alist.lookup (get_orders pc) nn of
      None =>
        raise Fail (format_failure lno ("no such order: " ^ nn))
    | Some ord' =>
      if guard_ord_t ord' xs then
        (core_from_range_arr fml cw id;
          (fml, (assg, (st, (inds, (mk_perm_arr vimap (map_fst xs),
            (id, ((set_ord pc (mk_ordsub ord' xs), (vomap, id)), ht))))))))
      else
        raise Fail
          (format_failure lno ("invalid order instantiation")))
  | Unloadorder =>
    (case get_ord pc of None =>
     raise Fail (format_failure lno ("no order loaded"))
    | Some spo =>
      (fml,(assg,(st,(inds,(vimap,(id,
        ((set_ord pc None, (vomap, cw)), ht))))))))
  | Storeorder name vars gspec f pfsr pfst =>
    let val aord = check_storeorder_arr lno vars gspec f pfst pfsr in
       (fml, (assg, (st, (inds, (vimap, (id,
         ((set_orders pc ((name,aord)::get_orders pc), (vomap, cw)),
           ht)))))))
    end
  | Obj w mi bopt => (
    let val obj = get_obj pc in
      case check_obj_core_arr lno obj w fml inds bopt of
      None =>
       raise Fail (format_failure lno
        ("supplied assignment did not satisfy constraints or did not improve objective"))
      | Some (new, (w', cinds)) =>
      let
        val bound' = update_bound (get_chk pc) (get_bound pc) new
        val dbound' = update_dbound (get_dbound pc) new
      in
      if mi
      then
        if obj_check obj
        then
          raise Fail (format_failure lno
            ("model improving not allowed with no objective"))
        else
        let
          val c = model_improving obj new in
          case enc_mv c True of (s,mv) =>
          case store_ind_arr fml s mv id cinds vimap assg st of
            (fml',(inds',(vimap',(id',(assg',st'))))) =>
          (fml', (assg', (st', (inds', (vimap', (id',
            ((obj_update pc bound' dbound', (vomap, cw)), ht)))))))
        end
      else
        (fml, (assg, (st, (cinds, (vimap, (id,
          ((obj_update pc bound' dbound', (vomap, cw)), ht)))))))
      end
    end
    )
  | Changeobj b fc' pfs =>
    (case check_change_obj_arr lno b fml
      id (get_obj pc) fc' pfs assg st of
      (fml',(fc',(id',(assg',st')))) =>
        (fml', (assg', (st', (inds, (vimap, (id',
          ((change_obj_update pc fc',
            (mk_vomap_arr (String.size vomap) fc', cw)), ht))))))))
  | Checkobj fc' =>
    if check_eq_obj (get_obj pc) fc'
    then (fml, (assg, (st, (inds, (vimap, (id, (cfg, ht)))))))
    else
      raise Fail (format_failure lno
        (err_obj_check_string (get_obj pc) fc'))
  | Assertobj i =>
    let
      val obj = get_obj pc
    in
    if obj_check obj
    then
      raise Fail (format_failure lno
        ("model improving not allowed with no objective"))
    else
      let
        val c = model_improving obj i
        val dbound' = update_dbound (get_dbound pc) i in
        case enc_mv c True of (s,mv) =>
        case store_ind_arr fml s mv id inds vimap assg st of
          (fml',(inds',(vimap',(id',(assg',st'))))) =>
        (fml', (assg', (st', (inds', (vimap', (id',
          ((assert_obj_update pc dbound', (vomap, cw)), ht)))))))
      end
    end
  | Changepres b v c pfs =>
    (case check_change_pres_arr lno b fml
      id (get_pres pc) v c pfs assg st of
      (fml',(pres',(id',(assg',st')))) =>
        (fml', (assg', (st', (inds, (vimap, (id',
          ((change_pres_update pc pres', (vomap, cw)), ht))))))))
  | Sol w free => (
    let
      val obj = get_obj pc
      val chk = get_chk pc
    in
      if obj_chk_check obj chk then
        if free_ok (get_pres pc) free then
          (case check_sol_core_arr lno w free fml inds of
          None =>
           raise Fail (format_failure lno
            ("supplied solution cube has conflicting assignments or does not satisfy constraints"))
          | Some (ww, cinds) =>
          let
            val bound' = update_bound chk (get_bound pc) 0
            val dbound' = update_dbound (get_dbound pc) 0
            val pres = get_pres pc
            val c = model_banning pres free ww
            val count = cube_count free in
            case enc_mv c True of (s,mv) =>
            case store_ind_arr fml s mv id cinds vimap assg st of
              (fml',(inds',(vimap',(id',(assg',st'))))) =>
            (fml', (assg', (st', (inds', (vimap', (id',
              ((sol_update pc bound' dbound' count, (vomap, cw)), ht)))))))
          end)
        else
          raise Fail (format_failure lno
            ("free variables of a solution must be preserved"))
      else
        raise Fail (format_failure lno
          ("solution exclusion not allowed after unchecked del (and no objective allowed)"))
    end)
  | Checkpres ls' =>
    if check_eq_pres (get_pres pc) ls'
    then (fml, (assg, (st, (inds, (vimap, (id, (cfg, ht)))))))
    else
      raise Fail (format_failure lno
        (err_pres_check_string (get_pres pc) ls'))
End

Theorem check_cstep_arr_spec:
  NUM lno lnov ∧
  NPBC_CHECK_CSTEP_TYPE cstep cstepv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM st stv ∧
  (LIST_TYPE NUM) inds indsv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  NUM id idv ∧
  cfg_TYPE (pc,vomap,cw) cfgv ∧
  fml_bound fmlls (LENGTH assg) ∧
  ht_TYPE bksv bkslsv ht htv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cstep_arr" (get_ml_prog_state()))
    [lnov; cstepv; fmlv; assgv; stv; indsv; vimapv; idv; cfgv; htv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        &(
          case check_cstep_list cstep fmlls assg st inds vimap id
            (pc,vomap,cw) ht of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
              (PAIR_TYPE NUM
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                  (PAIR_TYPE NUM
                    (PAIR_TYPE cfg_TYPE (ht_TYPE bksv' bkslsv')))))))
                res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'
          bksv' bkslsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' * ARRAY bksv' bkslsv' *
        & (Fail_exn e ∧
          check_cstep_list cstep fmlls assg st inds vimap id
            (pc,vomap,cw) ht = NONE)))
Proof
  rw[]>>
  xcf "check_cstep_arr" (get_ml_prog_state ())>>
  qpat_assum`PAIR_TYPE _ _ (pc,vomap,cw) _`
    (strip_assume_tac o SIMP_RULE std_ss [PAIR_TYPE_def])>>
  gvs[]>>
  xmatch>>
  Cases_on`cstep`>>fs[NPBC_CHECK_CSTEP_TYPE_def]
  >~ [`check_cstep_list (Dom _ _ _ _)`] >- suspend "Dom"
  >~ [`check_cstep_list (Sstep _)`] >- suspend "Sstep"
  >~ [`check_cstep_list (CheckedDelete _ _ _ _)`] >- suspend "Cdel"
  >~ [`check_cstep_list (UncheckedDelete _)`] >- suspend "Udel"
  >~ [`check_cstep_list (Transfer _)`] >- suspend "Transfer"
  >~ [`check_cstep_list (StrengthenToCore _)`] >- suspend "Stc"
  >~ [`check_cstep_list (LoadOrder _ _)`] >- suspend "Load"
  >~ [`check_cstep_list UnloadOrder`] >- suspend "Unload"
  >~ [`check_cstep_list (StoreOrder _ _ _ _ _ _)`] >- suspend "Store"
  >~ [`check_cstep_list (Obj _ _ _)`] >- suspend "Obj"
  >~ [`check_cstep_list (ChangeObj _ _ _)`] >- suspend "Cobj"
  >~ [`check_cstep_list (CheckObj _)`] >- suspend "Kobj"
  >~ [`check_cstep_list (AssertObj _)`] >- suspend "Aobj"
  >~ [`check_cstep_list (ChangePres _ _ _ _)`] >- suspend "Cpres"
  >~ [`check_cstep_list (Sol _ _)`] >- suspend "Sol"
  >~ [`check_cstep_list (CheckPres _)`] >- suspend "Kpres"
QED

Resume check_cstep_arr_spec[Dom]:
  xmatch>>
  xapp>>xsimpl>>
  metis_tac[]
QED

Resume check_cstep_arr_spec[Sstep]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' * ARRAY vimapv' vimaplsv' *
      ARRAY bksv' bkslsv' *
      &(case check_sstep_list s pc.pres pc.ord pc.obj pc.tcb fmlls inds id
          vimap vomap assg st ht of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                (PAIR_TYPE NUM
                  (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                    (PAIR_TYPE NUM (ht_TYPE bksv' bkslsv')))))) res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' * ARRAY vimapv' vimaplsv' *
      ARRAY bksv' bkslsv' *
      &(Fail_exn e ∧
        check_sstep_list s pc.pres pc.ord pc.obj pc.tcb fmlls inds id
          vimap vomap assg st ht = NONE))`
  >- (
    xapp>>xsimpl>>
    metis_tac[])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  pop_assum mp_tac>>
  every_case_tac>>
  rw[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  qexistsl_tac[`bksv'`,`bkslsv'`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Cdel]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet_autop>>
  fs[check_tcb_idopt_pc_def]>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  xlet_autop>>
  xlet`POSTve
    (λv. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv *
      &(lookup_core_only_list T fmlls n ≠ Empty ∧
        fslot_TYPE (lookup_core_only_list T fmlls n) v))
    (λe. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
      ARRAY bksv bkslsv *
      &(Fail_exn e ∧ lookup_core_only_list T fmlls n = Empty))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`n`,`fmlls`,`T`,`lno`]>>
    simp[])
  >- (xsimpl>>simp[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  qpat_x_assum`fslot_TYPE _ _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * SEP_EXISTS bksv1 bkslsv1. ARRAY bksv1 bkslsv1 *
    &ht_TYPE bksv1 bkslsv1 (ht_del fmlls [n] ht) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv`,`[n]`,`ht`,
      `fmlls`,`bksv`,`bkslsv`]>>
    simp[LIST_TYPE_def]>>
    xsimpl>>
    rw[]>>
    qpat_assum`ht_TYPE _ _ (ht_del _ _ _) _` (irule_at Any)>>
    xsimpl)>>
  rpt xlet_autop>>
  fs[get_pres_def,get_ord_def,get_obj_def,get_tcb_def,slot_CASE_default]>>
  `fml_bound (delete_list n fmlls) (LENGTH assg)` by
    metis_tac[bound_list_delete_list,list_delete_list_def]>>
  xlet`POSTve
    (λv.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' * ARRAY vimapv' vimaplsv' *
      ARRAY bksv' bkslsv' *
      &(case check_red_list pc.pres pc.ord pc.obj T pc.tcb (delete_list n fmlls)
          inds id (lookup_core_only_list T fmlls n)
          (slot_max_var (lookup_core_only_list T fmlls n)) l l0 o' vimap vomap
          assg st (ht_del fmlls [n] ht) of
          NONE => F
        | SOME res =>
          PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
              (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
                (PAIR_TYPE NUM (ht_TYPE bksv' bkslsv'))))))
            res v))
    (λe.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv' bksv' bkslsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' * ARRAY vimapv' vimaplsv' *
      ARRAY bksv' bkslsv' *
      &(Fail_exn e ∧
        check_red_list pc.pres pc.ord pc.obj T pc.tcb (delete_list n fmlls)
          inds id (lookup_core_only_list T fmlls n)
          (slot_max_var (lookup_core_only_list T fmlls n)) l l0 o' vimap vomap
          assg st (ht_del fmlls [n] ht) = NONE))`
  >- (
    xapp>>xsimpl>>
    simp[fslot_TYPE_def,slot_bound_slot_max_var]>>
    metis_tac[])
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  pop_assum mp_tac>>
  every_case_tac>>
  rw[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  qexistsl_tac[`bksv'`,`bkslsv'`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Udel]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet_autop>>
  fs[get_chk_def]>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv bkslsv *
    &cfg_TYPE (pc with chk := F,vomap,cw) v`
  >- (
    xif
    >- (
      `BOOL F (Conv (SOME (TypeStamp «False» 0)) [])` by EVAL_TAC>>
      rpt xlet_autop>>
      xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        ARRAY vimapv vimaplsv * ARRAY bksv bkslsv *
        &NPBC_CHECK_PROOF_CONF_TYPE (set_chk pc F) v`
      >- (xapp>>xsimpl>>qexistsl_tac[`F`,`pc`]>>simp[])>>
      xcon>>xsimpl>>
      gvs[PAIR_TYPE_def,set_chk_def])>>
    xvar>>xsimpl>>
    `pc with chk := F = pc` by
      simp[npbc_checkTheory.proof_conf_component_equality]>>
    gvs[PAIR_TYPE_def])>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * SEP_EXISTS bksv1 bkslsv1. ARRAY bksv1 bkslsv1 *
    &ht_TYPE bksv1 bkslsv1 (ht_del fmlls l ht) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv`,`l`,`ht`,
      `fmlls`,`bksv`,`bkslsv`]>>
    simp[]>>
    xsimpl>>
    rw[]>>
    qpat_assum`ht_TYPE _ _ (ht_del _ _ _) _` (irule_at Any)>>
    xsimpl)>>
  rpt xlet_autop>>
  `check_tcb_ord pc ⇔ ¬pc.tcb ∧ pc.ord = NONE` by
    (Cases_on`pc.ord`>>simp[check_tcb_ord_def])>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    gvs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv1 bkslsv1 * &LIST_TYPE NUM [] v`
  >- (xcon>>xsimpl>>simp[LIST_TYPE_def])>>
  xlet_autop>>
  Cases_on`all_core_list fmlls inds []`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  IF_CASES_TAC >- metis_tac[]>>
  simp[PAIR_TYPE_def]>>
  qexistsl_tac[`fmllsv'`,`vimaplsv`]>>
  gvs[]>>
  xsimpl>>
  gvs[PAIR_TYPE_def]>>
  qexistsl_tac[`bksv1`,`bkslsv1`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Transfer]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet_auto
  >- (xsimpl>>metis_tac[ARRAY_refl])
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xcon>>
  every_case_tac>>fs[]>>
  xsimpl>>
  simp[PAIR_TYPE_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Stc]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xif
  >- (
    xlet_auto >- xsimpl>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,set_tcb_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[PAIR_TYPE_def,set_tcb_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Load]:
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop>>
  fs[get_orders_def]>>
  rename1`ALOOKUP pc.orders nn`>>
  Cases_on`ALOOKUP pc.orders nn`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet_auto >- xsimpl>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  gvs[PAIR_TYPE_def,OPTION_TYPE_def,set_ord_def,map_fst_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Unload]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet_autop>>
  fs[get_ord_def]>>
  Cases_on`pc.ord`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv bkslsv *
    &NPBC_CHECK_PROOF_CONF_TYPE (set_ord pc NONE) v`
  >- (
    xapp>>xsimpl>>
    first_assum (irule_at Any)>>
    qexists_tac`NONE`>>simp[OPTION_TYPE_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[PAIR_TYPE_def,set_ord_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Store]:
  qmatch_goalsub_rename_tac`check_cstep_list (StoreOrder nn _ _ _ _ _)`>>
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  gvs[]>>
  rename1`check_storeorder _ _ _ _ _ = SOME aord`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
    ARRAY vimapv vimaplsv * ARRAY bksv bkslsv *
    &NPBC_CHECK_PROOF_CONF_TYPE (set_orders pc ((nn,aord)::pc.orders)) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`(nn,aord)::pc.orders`,`pc`]>>
    fs[LIST_TYPE_def,PAIR_TYPE_def,get_orders_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[PAIR_TYPE_def,set_orders_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Obj]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet_autop>>
  fs[get_obj_def]>>
  rename1`check_obj_core pc.obj wm fmlls inds bopt`>>
  xlet_auto
  >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_obj_core pc.obj wm fmlls inds bopt`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rename1`check_obj_core _ _ _ _ _ = SOME nw`>>
  PairCases_on`nw`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  fs[get_chk_def,get_bound_def,get_dbound_def]>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    gvs[PAIR_TYPE_def,obj_update_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  fs[obj_check_def]>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  gvs[]>>
  xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def]>>
  xmatch>>
  qabbrev_tac`c = model_improving pc.obj nw0`>>
  `∃fml1 inds1 vimap1 id1 assg1 st1.
    store_ind fmlls (enc c T) (max_var (FST c)) id (reindex fmlls inds)
      vimap assg st =
    (fml1,inds1,vimap1,id1,assg1,st1)` by metis_tac[PAIR]>>
  simp[]>>
  xlet`POSTv v.
    SEP_EXISTS fmlv1 fmllsv1 assgv1 vimapv1 vimaplsv1.
    ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg1 * ARRAY vimapv1 vimaplsv1 *
    ARRAY bksv bkslsv *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
      (PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv1 ∧ v = vimapv1)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg1 ∧ v = assgv1) NUM))))
      (fml1,inds1,vimap1,id1,assg1,st1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY bksv bkslsv`,`vimap`,`st`,`enc c T`,
      `max_var (FST c)`,`reindex fmlls inds`,`id`,`fmlls`,`assg`]>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
    xsimpl>>
    rpt strip_tac>>
    gvs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[obj_update_def]>>
  qexistsl_tac[`bksv`,`bkslsv`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Cobj]:
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop>>
  fs[get_obj_def]>>
  xlet_auto
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  pop_assum mp_tac>>
  every_case_tac>>
  rw[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[change_obj_update_def]>>
  qexistsl_tac[`bksv`,`bkslsv`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Kobj]:
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop>>
  fs[get_obj_def]>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Aobj]:
  qmatch_goalsub_rename_tac`check_cstep_list (AssertObj ai)`>>
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  fs[obj_check_def,get_obj_def]>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  gvs[]>>
  xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def,get_dbound_def]>>
  xmatch>>
  qabbrev_tac`c = model_improving pc.obj ai`>>
  `∃fml1 inds1 vimap1 id1 assg1 st1.
    store_ind fmlls (enc c T) (max_var (FST c)) id inds vimap assg st =
    (fml1,inds1,vimap1,id1,assg1,st1)` by metis_tac[PAIR]>>
  simp[]>>
  xlet`POSTv v.
    SEP_EXISTS fmlv1 fmllsv1 assgv1 vimapv1 vimaplsv1.
    ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg1 * ARRAY vimapv1 vimaplsv1 *
    ARRAY bksv bkslsv *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
      (PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv1 ∧ v = vimapv1)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg1 ∧ v = assgv1) NUM))))
      (fml1,inds1,vimap1,id1,assg1,st1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY bksv bkslsv`,`vimap`,`st`,`enc c T`,
      `max_var (FST c)`,`inds`,`id`,`fmlls`,`assg`]>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
    xsimpl>>
    rpt strip_tac>>
    gvs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[assert_obj_update_def]>>
  qexistsl_tac[`bksv`,`bkslsv`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Cpres]:
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop>>
  fs[get_pres_def]>>
  xlet_auto
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  pop_assum mp_tac>>
  every_case_tac>>
  rw[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  fs[change_pres_update_def]>>
  qexistsl_tac[`bksv`,`bkslsv`]>>
  xsimpl
QED

Resume check_cstep_arr_spec[Sol]:
  xmatch>>
  simp[check_cstep_list_def]>>
  rpt xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  xif>>fs[obj_chk_check_def,get_chk_def,get_obj_def]
  >- (
    rpt xlet_autop>>
    xif>>fs[get_pres_def]
    >- (
      rename1`check_sol_core wm free fmlls inds`>>
      xlet_auto
      >- (xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
      >- (xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
      Cases_on`check_sol_core wm free fmlls inds`>>
      fs[OPTION_TYPE_def]
      >- (
        xmatch>>
        rpt xlet_autop>>
        xraise>>xsimpl>>
        simp[Fail_exn_def]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      rename1`check_sol_core _ _ _ _ = SOME ww`>>
      gvs[PAIR_TYPE_def]>>
      xmatch>>
      rpt xlet_autop>>
      `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
      xlet_autop>>
      gvs[enc_mv_enc,PAIR_TYPE_def,get_pres_def,get_bound_def,
        get_dbound_def]>>
      xmatch>>
      qabbrev_tac`c = model_banning pc.pres free ww`>>
      `∃fml1 inds1 vimap1 id1 assg1 st1.
        store_ind fmlls (enc c T) (max_var (FST c)) id (reindex fmlls inds)
          vimap assg st =
        (fml1,inds1,vimap1,id1,assg1,st1)` by metis_tac[PAIR]>>
      simp[]>>
      xlet`POSTv v.
        SEP_EXISTS fmlv1 fmllsv1 assgv1 vimapv1 vimaplsv1.
        ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg1 * ARRAY vimapv1 vimaplsv1 *
        ARRAY bksv bkslsv *
        &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
          (PAIR_TYPE (LIST_TYPE NUM)
            (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv1 ∧ v = vimapv1)
              (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg1 ∧ v = assgv1) NUM))))
          (fml1,inds1,vimap1,id1,assg1,st1) v`
      >- (
        xapp>>xsimpl>>
        qexistsl_tac[`ARRAY bksv bkslsv`,`vimap`,`st`,`enc c T`,
          `max_var (FST c)`,`reindex fmlls inds`,`id`,`fmlls`,`assg`]>>
        simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
        xsimpl>>
        rpt strip_tac>>
        gvs[PAIR_TYPE_def]>>
        metis_tac[ARRAY_NUM_ARRAY_refl])>>
      gvs[PAIR_TYPE_def]>>
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[sol_update_def]>>
      qexistsl_tac[`bksv`,`bkslsv`]>>
      xsimpl)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Resume check_cstep_arr_spec[Kpres]:
  xmatch>>
  simp[check_cstep_list_def]>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp (eq_lemmas()))>>
  xif>>fs[get_pres_def]
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  metis_tac[ARRAY_NUM_ARRAY_refl]
QED

Finalise check_cstep_arr_spec;

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

Quote add_cakeml:
  fun check_implies_fml_arr fml n c =
  case Array.lookup fml Empty n of
    Empty => False
  | s => imp_slot s c
End

Theorem check_implies_fml_arr_spec:
  NUM n nv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
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
  rw[check_implies_fml_list_def]>>
  xcf "check_implies_fml_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  qmatch_asmsub_rename_tac`sv = any_el n fmllsv _`>>
  `fslot_TYPE (any_el n fmlls Empty) sv` by (
    rw[any_el_ALT]>>
    gvs[LIST_REL_EL_EQN,fslot_TYPE_def,wf_slot_def,SLOT_TYPE_def])>>
  Cases_on`any_el n fmlls Empty`>>
  gvs[fslot_TYPE_def,SLOT_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl>>EVAL_TAC)>>
  rename1`any_el n fmlls Empty = Stored cs vs d mc sm cb`>>
  xapp>>xsimpl>>
  qexistsl_tac[`c`,`Stored cs vs d mc sm cb`]>>
  simp[SLOT_TYPE_def,imp_slot_side]
QED

val res = translate check_sat_def;
val res = translate npbc_checkTheory.opt_le_def;
val res = translate check_ub_def;

Theorem check_obj_slots_side:
  EVERY wf_slot ss ⇒ check_obj_slots_side obj wm ss bopt
Proof
  rw[fetch "-" "check_obj_slots_side_def",every_sat_slot_side]
QED

Theorem check_sat_side:
  EVERY wf_slot fmls ⇒ check_sat_side fmls obj bound' wopt
Proof
  rw[fetch "-" "check_sat_side_def",check_obj_slots_side]
QED

Theorem check_ub_side:
  EVERY wf_slot fmls ⇒ check_ub_side fmls obj bound' ubi wopt
Proof
  rw[fetch "-" "check_ub_side_def",check_obj_slots_side]
QED

val _ = register_type ``:hconcl``

val res = translate npbc_checkTheory.lower_bound_def;

Definition hdsat_res_def:
  hdsat_res b =
  if b then NONE
  else SOME «conclusion SATISFIABLE check failed: [assignment check] T»
End

val res = translate hdsat_res_def;

Definition bool_to_string_def:
  bool_to_string b =
  if b then «T» else «F»
End

Definition hdunsat_res_def:
  hdunsat_res b1 b2 =
  if b1 ∧ b2 then NONE
  else SOME (
      «conclusion UNSATISFIABLE check failed:» ^
      « [dbound check] » ^ bool_to_string b1 ^
      « [contradiction check] » ^ bool_to_string b2
  )
End

val res = translate bool_to_string_def;
val res = translate hdunsat_res_def;

Definition hobounds_res_def:
  hobounds_res b1 b2 b3 =
  if b1 ∧ b2 ∧ b3 then NONE
  else SOME (
      «conclusion BOUNDS check failed:» ^
      « [lb <= dbound] » ^ bool_to_string b1 ^
      « [upper bound check] » ^ bool_to_string b2 ^
      « [lower bound check] » ^ bool_to_string b3
  )
End

val res = translate hobounds_res_def;

Definition heenum_res_def:
  heenum_res (obj:((int # num) list # int) option) (n:num) enum b3 b4 =
  let
    b1 = (obj = NONE);
    b2 = (n = enum)
  in
  if b1 ∧ b2 ∧ b3 ∧ b4 then NONE
  else SOME (
      «conclusion ENUMERATION check failed:» ^
      « [no objective] » ^ bool_to_string b1 ^
      « [enumeration claim] » ^ bool_to_string b2 ^
      « [complete hint present] » ^ bool_to_string b3 ^
      « [complete hint correct] » ^ bool_to_string b4
  )
End

val res = translate heenum_res_def;

Quote add_cakeml:
  fun check_hconcl_arr fml obj fml' obj' bound' dbound' enum hconcl =
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
  | Heenum n complete hint =>
    if complete
    then
      case hint of
        None => heenum_res obj n enum False True
      | Some i =>
        heenum_res obj n enum True (check_contradiction_fml_arr False fml' i)
    else
      heenum_res obj n enum True True
End

val NPBC_CHECK_HCONCL_TYPE_def = theorem"NPBC_CHECK_HCONCL_TYPE_def";

Theorem check_hconcl_arr_spec:
  LIST_TYPE fslot_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  obj_TYPE obj1 obj1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  NUM enum enumv ∧
  NPBC_CHECK_HCONCL_TYPE hconcl hconclv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_hconcl_arr" (get_ml_prog_state()))
    [fmlv; objv; fml1v; obj1v; bound1v; dbound1v; enumv; hconclv]
    (ARRAY fml1v fmllsv)
    (POSTv v.
        ARRAY fml1v fmllsv *
        &(
        ∃s.
        OPTION_TYPE STRING_TYPE
        (if check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 enum hconcl then NONE else SOME s) v))
Proof
  rw[]>>
  xcf"check_hconcl_arr"(get_ml_prog_state ())>>
  Cases_on`hconcl`>>
  fs[check_hconcl_list_def,NPBC_CHECK_HCONCL_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl>>simp[OPTION_TYPE_def])
  >- (
    gvs[LIST_TYPE_fslot_TYPE]>>
    xlet_auto
    >- (xsimpl>>simp[check_sat_side,EqualityType_NUM_BOOL])>>
    xapp>>xsimpl>>
    rw[hdsat_res_def]>>
    metis_tac[])
  >- (
    xlet_autop>>
    xlet`POSTv v. ARRAY fml1v fmllsv *
      &BOOL (check_contradiction_fml_list F fmlls n) v`
    >- (xapp>>xsimpl)>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fml1v fmllsv * &BOOL (dbound1 = NONE) v`
    >- (
      xapp_spec (mlbasicsProgTheory.eq_v_thm |>
        INST_TYPE [alpha |-> ``:int option``])>>
      rpt (first_x_assum (irule_at Any))>>
      qexists_tac`NONE`>>xsimpl>>
      simp[OPTION_TYPE_def]>>
      metis_tac[EqualityType_OPTION_TYPE,EqualityType_NUM_BOOL])>>
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    simp[hdunsat_res_def]>>rw[]>>
    metis_tac[])
  >- (
    gvs[LIST_TYPE_fslot_TYPE]>>
    xlet_autop>>
    xlet_auto
    >- (xsimpl>>simp[check_ub_side])>>
    rename1`opt_le lb dbound1`>>
    Cases_on`lb`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xlet`POSTv v. ARRAY fml1v fmllsv *
        &BOOL (check_contradiction_fml_list F fmlls n) v`
      >- (xapp>>xsimpl)>>
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      simp[hobounds_res_def]>>rw[]>>
      metis_tac[])>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    simp[hobounds_res_def]>>rw[]>>
    metis_tac[])>>
  xif>>
  rpt xlet_autop
  >- (
    rename1`OPTION_TYPE NUM hint _`>>
    Cases_on`hint`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xapp>>xsimpl>>
      qexistsl_tac[`T`,`F`]>>
      rpt (first_x_assum (irule_at Any))>>
      gvs[heenum_res_def]>>
      every_case_tac>>
      gvs[OPTION_TYPE_def]>>
      rw[]
      >- EVAL_TAC
      >- EVAL_TAC>>
      metis_tac[])>>
    rpt xlet_autop>>
    rename1`NUM x _`>>
    xlet`POSTv v. ARRAY fml1v fmllsv *
      &BOOL (check_contradiction_fml_list F fmlls x) v`
    >- (xapp>>xsimpl)>>
    xlet_autop>>
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    qexists_tac`T`>>
    gvs[heenum_res_def]>>
    every_case_tac>>
    gvs[OPTION_TYPE_def]>>
    rw[]
    >- EVAL_TAC
    >- EVAL_TAC>>
    metis_tac[])>>
  xapp>>xsimpl>>
  qexistsl_tac[`T`,`T`]>>
  rpt (first_x_assum (irule_at Any))>>
  gvs[heenum_res_def]>>
  every_case_tac>>
  gvs[OPTION_TYPE_def]>>
  rw[]
  >- EVAL_TAC
  >- EVAL_TAC>>
  metis_tac[]
QED

(* Output check against the table *)

(* The marks of the core slots: one byte per id *)
Definition marks_bytes_def:
  marks_bytes mk = MAP (λb. if b then w8o else w8z) mk
End

(* Marks every id from place j up to the first free place, trying at most
  fuel places, whose slot (core only) matches c; whether there is one, or
  found *)
Quote add_cakeml:
  fun ht_mark_arr fml c tbl j fuel mk found =
  if fuel = 0 then found
  else
    let val i = Unsafe.sub tbl j in
      if i = 0 then found
      else
        let
          val found =
            (case lookup_core_only_arr True fml i of
              Empty => found
            | s =>
              if eq_slot c s then
                ((if i < Word8Array.length mk then Unsafe.w8update mk i w8o
                  else ());
                 True)
              else found)
        in
          ht_mark_arr fml c tbl (ht_next (Array.length tbl) j) (fuel - 1) mk
            found
        end
    end
End

Theorem ht_mark_arr_spec:
  ∀fuel fuelv j jv mk found foundv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  constraint_TYPE c cv ∧
  NUM j jv ∧ NUM fuel fuelv ∧
  LIST_REL NUM tbl tbllsv ∧ j < LENGTH tbl ∧
  BOOL found foundv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_mark_arr" (get_ml_prog_state()))
    [fmlv; cv; tblv; jv; fuelv; mkv; foundv]
    (ARRAY fmlv fmllsv * ARRAY tblv tbllsv * W8ARRAY mkv (marks_bytes mk))
    (POSTv v.
      ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
      W8ARRAY mkv (marks_bytes (ht_mark fmlls c tbl j fuel mk)) *
      &BOOL (found ∨ ht_mem T fmlls c tbl j fuel) v)
Proof
  Induct>>
  rw[]>>
  xcf "ht_mark_arr" (get_ml_prog_state ())>>
  simp[Once ht_mark_def,Once ht_mem_def]
  >- (
    xlet_autop>>
    xif>>
    qexists_tac`T`>>simp[]>>
    xvar>>xsimpl)>>
  xlet_autop>>
  xif>>
  qexists_tac`F`>>simp[]>>
  imp_res_tac LIST_REL_LENGTH>>
  `NUM (EL j tbl) (EL j tbllsv)` by fs[LIST_REL_EL_EQN]>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    W8ARRAY mkv (marks_bytes mk) * &(v = EL j tbllsv)`
  >- (
    xapp_spec UnsafeProofTheory.unsafe_array_sub_spec>>
    xsimpl>>
    metis_tac[])>>
  xlet_autop>>
  xif
  >- (
    xvar>>xsimpl)>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  xlet_autop>>
  xlet_autop>>
  qpat_x_assum`fslot_TYPE (lookup_core_only_list _ _ _) _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  qabbrev_tac`i = EL j tbl`>>
  qabbrev_tac`s = lookup_core_only_list T fmlls i`>>
  qabbrev_tac`mk1 = case s of Empty => mk
    | Stored a1 a2 a3 a4 a5 a6 =>
      if eq_slot c (Stored a1 a2 a3 a4 a5 a6) then LUPDATE T i mk else mk`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    W8ARRAY mkv (marks_bytes mk1) *
    &BOOL (found ∨ case s of Empty => F
      | Stored a1 a2 a3 a4 a5 a6 => eq_slot c (Stored a1 a2 a3 a4 a5 a6)) v`
  >- (
    Cases_on`s`>>
    gvs[SLOT_TYPE_def,Abbr`mk1`]>>
    xmatch
    >- (
      xvar>>xsimpl)>>
    rename1`lookup_core_only_list T fmlls i = Stored cs vs d mc sm cb`>>
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
      W8ARRAY mkv (marks_bytes mk) *
      &BOOL (eq_slot c (Stored cs vs d mc sm cb)) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`c`,`Stored cs vs d mc sm cb`]>>
      simp[SLOT_TYPE_def,eq_slot_side])>>
    xif
    >- (
      xlet_auto
      >- (xsimpl>>metis_tac[])>>
      xlet_autop>>
      xlet`POSTv u. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
        W8ARRAY mkv (marks_bytes (LUPDATE T i mk))`
      >- (
        xif
        >- (
          assume_tac w8o_v_thm>>
          xapp>>xsimpl>>
          simp[marks_bytes_def,LUPDATE_MAP]>>
          qexistsl_tac[`w8o`,`i`]>>
          gvs[marks_bytes_def])>>
        `LUPDATE T i mk = mk` by
          gvs[LIST_EQ_REWRITE,EL_LUPDATE,marks_bytes_def]>>
        xcon>>xsimpl)>>
      xcon>>xsimpl)>>
    xvar>>xsimpl)>>
  rpt xlet_autop>>
  xapp>>
  qexistsl_tac[`emp`,`mk1`,`ht_next (LENGTH tbllsv) j`,
    `found ∨ case s of Empty => F
      | Stored a1 a2 a3 a4 a5 a6 => eq_slot c (Stored a1 a2 a3 a4 a5 a6)`]>>
  xsimpl>>
  gvs[ht_next_def]>>
  simp[DISJ_ASSOC]
QED

(* Marks every core slot in the table that matches a constraint of cs; res
  is the first constraint so far without a match, printed *)
Quote add_cakeml:
  fun ht_marks_arr fml tbl mk cs res =
  case cs of [] => res
  | c::cs =>
    let
      val n = Array.length tbl
      val found = ht_mark_arr fml c tbl (hash_constraint c mod n) n mk False
    in
      case res of
        None =>
        if found then ht_marks_arr fml tbl mk cs None
        else ht_marks_arr fml tbl mk cs (Some (npbc_constr_string c))
      | _ => ht_marks_arr fml tbl mk cs res
    end
End

Theorem ht_marks_arr_spec:
  ∀cs csv mk res resv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  tbl ≠ [] ∧
  LIST_REL NUM tbl tbllsv ∧
  LIST_TYPE constraint_TYPE cs csv ∧
  OPTION_TYPE STRING_TYPE res resv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "ht_marks_arr" (get_ml_prog_state()))
    [fmlv; tblv; mkv; csv; resv]
    (ARRAY fmlv fmllsv * ARRAY tblv tbllsv * W8ARRAY mkv (marks_bytes mk))
    (POSTv v.
      ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
      W8ARRAY mkv (marks_bytes (ht_marks fmlls tbl cs mk)) *
      & ∃err.
        OPTION_TYPE STRING_TYPE
          (if res = NONE ∧ ht_include fmlls tbl cs then NONE else SOME err) v)
Proof
  Induct>>
  rw[]>>
  xcf "ht_marks_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,ht_marks_def,ht_include_def]>>
  xmatch
  >- (
    xvar>>xsimpl>>
    Cases_on`res`>>gvs[OPTION_TYPE_def]>>
    metis_tac[])>>
  imp_res_tac LIST_REL_LENGTH>>
  `tbllsv ≠ []` by (
    Cases_on`tbl`>>gvs[])>>
  `hash_constraint h MOD LENGTH tbl < LENGTH tbl` by (
    Cases_on`tbl`>>gvs[])>>
  rpt xlet_autop>>
  qabbrev_tac`mk1 =
    ht_mark fmlls h tbl (hash_constraint h MOD LENGTH tbl) (LENGTH tbl) mk`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY tblv tbllsv *
    W8ARRAY mkv (marks_bytes mk1) *
    &BOOL (ht_probe T fmlls h (hash_constraint h) tbl) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`tbl`,`mk`,`hash_constraint h MOD LENGTH tbl`,`LENGTH tbl`,
      `F`,`fmlls`,`h`]>>
    simp[Abbr`mk1`,ht_probe_def]>>
    EVAL_TAC)>>
  Cases_on`res`>>gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xif
    >- (
      xlet_autop>>
      xapp>>
      qexistsl_tac[`emp`,`NONE`,`mk1`]>>
      simp[OPTION_TYPE_def]>>
      xsimpl>>
      metis_tac[])>>
    rpt xlet_autop>>
    xapp>>
    qexistsl_tac[`emp`,`SOME (npbc_constr_string h)`,`mk1`]>>
    simp[OPTION_TYPE_def]>>
    xsimpl>>
    metis_tac[])>>
  xapp>>
  qexistsl_tac[`emp`,`SOME x`,`mk1`]>>
  simp[OPTION_TYPE_def]>>
  xsimpl
QED

(* The core slot of the largest id below n that is not marked, printed *)
Quote add_cakeml:
  fun all_marked_arr fml mk n =
  if n = 0 then None
  else
    let val n1 = n - 1 in
      case lookup_core_only_arr True fml n1 of
        Empty => all_marked_arr fml mk n1
      | s =>
        if Word8Array.sub mk n1 = w8z then Some (npbc_constr_string (dec s))
        else all_marked_arr fml mk n1
    end
End

Theorem all_marked_arr_spec:
  ∀n nv.
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM n nv ∧
  n ≤ LENGTH mk
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_marked_arr" (get_ml_prog_state()))
    [fmlv; mkv; nv]
    (ARRAY fmlv fmllsv * W8ARRAY mkv (marks_bytes mk))
    (POSTv v.
      ARRAY fmlv fmllsv * W8ARRAY mkv (marks_bytes mk) *
      & ∃err.
        OPTION_TYPE STRING_TYPE
          (if all_marked fmlls mk n then NONE else SOME err) v)
Proof
  Induct
  >- (
    rw[]>>
    xcf "all_marked_arr" (get_ml_prog_state ())>>
    simp[Once all_marked_def]>>
    xlet_autop>>
    xif>>
    qexists_tac`T`>>simp[]>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def])>>
  rw[]>>
  xcf "all_marked_arr" (get_ml_prog_state ())>>
  simp[Once all_marked_def]>>
  xlet_autop>>
  xif>>
  qexists_tac`F`>>simp[]>>
  xlet_autop>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  xlet_autop>>
  xlet_autop>>
  qpat_x_assum`fslot_TYPE (lookup_core_only_list _ _ _) _`
    (strip_assume_tac o REWRITE_RULE[fslot_TYPE_def])>>
  Cases_on`lookup_core_only_list T fmlls n`>>
  gvs[SLOT_TYPE_def]
  >- (
    xmatch>>
    xapp>>simp[])>>
  rename1`lookup_core_only_list T fmlls n = Stored cs vs d mc sm cb`>>
  xmatch>>
  assume_tac w8z_v_thm>>
  xlet_auto
  >- (xsimpl>>simp[marks_bytes_def])>>
  xlet_autop>>
  `EL n (marks_bytes mk) = w8z ⇔ ¬EL n mk` by (
    simp[marks_bytes_def,EL_MAP]>>
    rw[]>>EVAL_TAC)>>
  gvs[]>>
  xif
  >- (
    xlet`POSTv cv. ARRAY fmlv fmllsv * W8ARRAY mkv (marks_bytes mk) *
      &constraint_TYPE (dec (Stored cs vs d mc sm cb)) cv`
    >- (
      xapp>>xsimpl>>
      qexists_tac`Stored cs vs d mc sm cb`>>
      simp[SLOT_TYPE_def,dec_side])>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def]>>
    metis_tac[])>>
  xapp>>xsimpl
QED

val _ = register_type ``:output``

Definition print_opt_string_def:
  (print_opt_string NONE = «T») ∧
  (print_opt_string (SOME s) = s)
End

val res = translate print_opt_string_def;

Definition derivable_res_def:
  derivable_res (dbound :int option) b2opt =
  let b1 = (dbound = NONE) in
  let b2 = (b2opt = NONE) in
  if b1 ∧ b2 then NONE
  else SOME (
      «output DERIVABLE check failed:» ^
      « [dbound = NONE] » ^ bool_to_string b1 ^
      « [core in output] » ^ print_opt_string b2opt)
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
      «output EQUISATISFIABLE check failed:» ^
      « [bound = NONE] » ^ bool_to_string b11 ^
      « [dbound = NONE] » ^ bool_to_string b12 ^
      « [checked deletion] » ^ bool_to_string chk ^
      « [core in output] » ^ print_opt_string b2opt ^
      « [output in core] » ^ print_opt_string b3opt
  )
End

val res = translate equisatisfiable_res_def;

val res = translate npbc_checkTheory.opt_eq_obj_def;

Definition opt_err_obj_check_string_def:
  (opt_err_obj_check_string (SOME fc) (SOME fc') =
    err_obj_check_string (SOME fc) fc') ∧
  (opt_err_obj_check_string _ _ = «missing objective»)
End

val res = translate opt_err_obj_check_string_def;

Definition equioptimal_res_def:
  equioptimal_res
    (bound:int option) (dbound:int option) chk
    obj obj' b2opt b3opt =
  let b11 = opt_le bound dbound in
  let b12 = opt_eq_obj obj obj' in
  let b12s =
    if b12 then «T» else opt_err_obj_check_string obj obj' in
  let b2 = (b2opt = NONE) in
  let b3 = (b3opt = NONE) in
  if b11 ∧ b12 ∧ chk ∧ b2 ∧ b3
  then NONE
    else SOME (
      «output EQUIOPTIMAL check failed:» ^
      « [bound <= dbound]: » ^ bool_to_string b11 ^
      « [obj = output obj]: » ^ b12s ^
      « [checked deletion]: » ^ bool_to_string chk ^
      « [core in output] » ^ print_opt_string b2opt ^
      « [output in core] » ^ print_opt_string b3opt
  )
End

val res = translate equioptimal_res_def;

Definition pres_string_def:
  (pres_string (xs:num_set) =
    concatWith « » (MAP (toString o FST) (toAList xs)))
End

(* Add a checking command? *)
Definition err_pres_string_def:
  err_pres_string pres pres' =
  case pres of NONE => «projection set check failed, no projection set available»
  | SOME pres =>
    concat[
    «projection set check failed, expect: »;
    pres_string pres';
    « got: »;
    pres_string pres]
End

Definition opt_err_pres_string_def:
  (opt_err_pres_string (SOME pres) (SOME pres') =
    err_pres_string (SOME pres) pres') ∧
  (opt_err_pres_string _ _ = «missing projection set»)
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
    if b12 then «T» else opt_err_obj_check_string obj obj' in
  let b2 = (b2opt = NONE) in
  let b3 = (b3opt = NONE) in
  let b4 = opt_eq_pres pres pres' in
  let b4s =
    if b4 then «T» else opt_err_pres_string pres pres' in
  if b11 ∧ b12 ∧ chk ∧ b2 ∧ b3 ∧ b4
  then NONE
    else SOME (
      «output EQUISOLVABLE check failed:» ^
      « [bound <= dbound]: » ^ bool_to_string b11 ^
      « [obj = output obj (if present)]: » ^ b12s ^
      « [pres = output pres]: » ^ b4s ^
      « [checked deletion]: » ^ bool_to_string chk ^
      « [core in output] » ^ print_opt_string b2opt ^
      « [output in core] » ^ print_opt_string b3opt
  )
End

val res = translate equisolvable_res_def;

Quote add_cakeml:
  fun check_output_arr fml inds id ht
    pres obj bound dbound chk fml' pres' obj' output =
  case output of
    Nooutput => None
  | _ =>
    (case ht_fill_arr fml inds id ht of (hw,(a,(d,tbl))) =>
    case output of
      Derivable =>
      (* no marks: ht_mark_arr marks only ids below the mark array's length *)
      derivable_res dbound
        (ht_marks_arr fml tbl (Word8Array.array 0 w8z) fml' None)
    | _ =>
      let
        val mk = Word8Array.array id w8z
        val b2 = ht_marks_arr fml tbl mk fml' None
        val b3 = all_marked_arr fml mk id
      in
        case output of
          Equisatisfiable => equisatisfiable_res bound dbound chk b2 b3
        | Equioptimal => equioptimal_res bound dbound chk obj obj' b2 b3
        | Equisolvable =>
          equisolvable_res bound dbound chk obj obj' pres pres' b2 b3
      end)
End

val PBC_OUTPUT_TYPE_def = theorem"PBC_OUTPUT_TYPE_def";

Theorem check_output_arr_spec:
  (LIST_TYPE NUM) inds indsv ∧
  NUM id idv ∧
  ht_TYPE bksv bkslsv ht htv ∧
  obj_TYPE obj objv ∧
  pres_TYPE pres presv ∧
  OPTION_TYPE INT bound boundv ∧
  OPTION_TYPE INT dbound dboundv ∧
  BOOL chk chkv ∧
  PBC_OUTPUT_TYPE output outputv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  pres_TYPE prest prestv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_output_arr" (get_ml_prog_state()))
    [fmlv; indsv; idv; htv; presv; objv; boundv; dboundv; chkv;
      fmltv; prestv; objtv; outputv]
    (ARRAY fmlv fmllsv * ARRAY bksv bkslsv)
    (POSTv v.
        ARRAY fmlv fmllsv *
        &(
        ∃s.
        OPTION_TYPE STRING_TYPE
        (if check_output_list fmlls inds id ht pres obj
          bound dbound chk fmlt prest objt output
         then NONE else SOME s) v))
Proof
  rw[]>>
  xcf"check_output_arr"(get_ml_prog_state ())>>
  Cases_on`output`>>
  fs[check_output_list_def,PBC_OUTPUT_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl>>simp[OPTION_TYPE_def])>>
  (
    xlet`POSTv v. ARRAY fmlv fmllsv * SEP_EXISTS bksv1 bkslsv1.
      ARRAY bksv1 bkslsv1 *
      &(ht_TYPE bksv1 bkslsv1 (ht_fill fmlls inds id ht) v ∧
        SND (SND (SND (ht_fill fmlls inds id ht))) ≠ [])`
    >- (
      xapp>>xsimpl))>>
  Cases_on`ht_fill fmlls inds id ht`>>
  PairCases_on`r`>>
  gvs[ht_TYPE_def,PAIR_TYPE_def]>>
  assume_tac w8z_v_thm>>
  xmatch>>
  xmatch
  >- (
    xlet_autop>>
    xlet_autop>>
    qmatch_goalsub_rename_tac`W8ARRAY mkv _`>>
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
      W8ARRAY mkv (marks_bytes (ht_marks fmlls r2 fmlt [])) *
      & ∃err. OPTION_TYPE STRING_TYPE
        (if ht_include fmlls r2 fmlt then NONE else SOME err) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`r2`,`NONE`,`[]`,`fmlls`,`fmlt`]>>
      simp[OPTION_TYPE_def,marks_bytes_def])>>
    xapp>>
    qexistsl_tac[`ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
        W8ARRAY mkv (marks_bytes (ht_marks fmlls r2 fmlt []))`,
      `if ht_include fmlls r2 fmlt then NONE else SOME err`,`dbound`]>>
    xsimpl>>
    rw[derivable_res_def]>>
    metis_tac[])>>
  xlet_autop>>
  `REPLICATE id w8z = marks_bytes (REPLICATE id F)` by
    simp[marks_bytes_def]>>
  xlet_autop>>
  qmatch_goalsub_rename_tac`W8ARRAY mkv _`>>
  qpat_x_assum`REPLICATE _ _ = _` SUBST_ALL_TAC>>
  (
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
      W8ARRAY mkv (marks_bytes (ht_marks fmlls r2 fmlt (REPLICATE id F))) *
      & ∃err. OPTION_TYPE STRING_TYPE
        (if ht_include fmlls r2 fmlt then NONE else SOME err) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`r2`,`NONE`,`REPLICATE id F`,`fmlls`,`fmlt`]>>
      simp[OPTION_TYPE_def]))>>
  qabbrev_tac`mk = ht_marks fmlls r2 fmlt (REPLICATE id F)`>>
  `id ≤ LENGTH mk` by
    simp[Abbr`mk`,LENGTH_ht_marks]>>
  (
    xlet`POSTv v. ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
      W8ARRAY mkv (marks_bytes mk) *
      & ∃err. OPTION_TYPE STRING_TYPE
        (if all_marked fmlls mk id then NONE else SOME err) v`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`id`,`mk`,`fmlls`]>>
      simp[]))>>
  xmatch>>
  xapp
  >- (
    qexistsl_tac[`ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
        W8ARRAY mkv (marks_bytes mk)`,
      `if all_marked fmlls mk id then NONE else SOME err'`,
      `if ht_include fmlls r2 fmlt then NONE else SOME err`,
      `chk`,`dbound`,`bound`]>>
    xsimpl>>
    rw[equisatisfiable_res_def]>>
    metis_tac[])
  >- (
    qexistsl_tac[`ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
        W8ARRAY mkv (marks_bytes mk)`,
      `if all_marked fmlls mk id then NONE else SOME err'`,
      `if ht_include fmlls r2 fmlt then NONE else SOME err`,
      `objt`,`obj`,`chk`,`dbound`,`bound`]>>
    xsimpl>>
    rw[equioptimal_res_def]>>
    metis_tac[])>>
  qexistsl_tac[`ARRAY fmlv fmllsv * ARRAY bksv1 bkslsv1 *
      W8ARRAY mkv (marks_bytes mk)`,
    `if all_marked fmlls mk id then NONE else SOME err'`,
    `if ht_include fmlls r2 fmlt then NONE else SOME err`,
    `prest`,`pres`,`objt`,`obj`,`chk`,`dbound`,`bound`]>>
  xsimpl>>
  rw[equisolvable_res_def]>>
  metis_tac[]
QED
