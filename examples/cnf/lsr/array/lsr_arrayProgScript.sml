(*
  This refines lsr_list to use arrays: the line-level steps
*)
Theory lsr_arrayProg
Ancestors
  misc mllist UnsafeProof ccnf_arith ccnf_arrayProg ccnf_parseProg cnf ccnf
  ccnf_list syntax_helper sr lsr lsr_list array_ofProof lsr_roundProg mlint
  mlvector
Libs
  preamble basis lsr_arrayLib

val _ = hide_environments true;

val _ = translation_extends "lsr_roundProg";

(***
  The walk over the group headers of a line
 ***)

(* Whether a formula slot holds the deleted-clause sentinel, tested as the
  core's unit_prop_one does *)
Quote add_cakeml:
  fun is_vcc_none_arr c =
  Vector.length c = 1 andalso int_eq_0 (Unsafe.vsub c 0)
End

Theorem is_vcc_none_arr_spec:
  vcclause_TYPE c cv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_vcc_none_arr" (get_ml_prog_state()))
    [cv]
    emp
    (POSTv bv. &BOOL (c = vcc_none) bv)
Proof
  strip_tac>>
  xcf "is_vcc_none_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlog>>
  simp[GSYM is_vcc_none]>>
  reverse IF_CASES_TAC>>gvs[]
  >- xsimpl>>
  xlet_auto
  >- (xsimpl>>gvs[UnsafeProgTheory.vsub_side_def])>>
  xapp>>
  xsimpl>>
  qexists_tac`sub c 0`>>
  simp[int_eq_0_def]
QED

Quote add_cakeml:
  fun walk_arr lno fml carr b piv sarr tally n s g prev cand =
  case parse_vb_int s g (String.size s) of (m,k) =>
  if m = 0 then cand
  else if 0 < m then
    raise Fail (format_failure lno "expected a group header")
  else
    let
      val d = 0 - m
      val cand = (if d <= prev then (if cand < 0 then cand else ~1 - cand)
                  else cand)
    in
    if d = n then
      walk_arr lno fml carr b piv sarr tally n s
        (skip_hints_vb s k (String.size s)) d (if cand < 0 then ~1 - k else k)
    else if Array.length fml <= d then
      walk_arr lno fml carr b piv sarr tally n s
        (skip_hints_vb s k (String.size s)) d cand
    else
      let val c = Unsafe.sub fml d in
      if is_vcc_none_arr c then
        walk_arr lno fml carr b piv sarr tally n s
          (skip_hints_vb s k (String.size s)) d cand
      else
        let
          val r = red_pass_arr lno fml carr b piv sarr tally c
                    (Vector.length c) s k
        in
          if r = 0 then
            raise Fail (format_failure lno "group round did not conflict")
          else
            walk_arr lno fml carr b piv sarr tally n s
              (skip_hints_vb s r (String.size s)) d cand
        end
      end
    end
End

(* The candidate's offset and whether the ids were increasing travel as one
  int: cand when they were, −cand−1 when not *)
Theorem cand_enc_lt_0:
  (if srt then &cand else -&cand - 1) < (0:int) ⇔ ¬srt
Proof
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem walk_arr_spec:
  ∀fmlls dml b rat piv sarr tally n s g len prev cand srt
   lnov bv pivv tallyv nv sv gv prevv candv.
  NUM lno lnov ∧ NUM b bv ∧
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  NUM n nv ∧ STRING_TYPE s sv ∧ NUM g gv ∧ len = strlen s ∧
  NUM prev prevv ∧ INT (if srt then &cand else -&cand - 1) candv ∧
  stamps_ok dml b ∧ bnd_fml fmlls (LENGTH dml) ∧
  bnd_fml fmlls (LENGTH sarr) ∧ img_bnd rat piv sarr ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  2 * LENGTH sarr ≤ LENGTH tally ∧ g ≤ len ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "walk_arr" (get_ml_prog_state()))
    [lnov; fmlv; carrv; bv; pivv; sarrv; tallyv; nv; sv; gv; prevv; candv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
     ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally)
    (POSTve
      (λv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS cand' srt' dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(walk_list fmlls dml b rat piv sarr tally n s g len prev cand srt =
              SOME (cand',srt',dml',tally') ∧
            INT (if srt' then &cand' else -&cand' - 1) v))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(Fail_exn e ∧
            walk_list fmlls dml b rat piv sarr tally n s g len prev cand srt =
              NONE)))
Proof
  ho_match_mp_tac walk_list_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  gvs[]>>
  xcf "walk_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>fs[parse_vb_int_side])>>
  Cases_on`parse_vb_int s g (strlen s)`>>
  rename1`parse_vb_int s g _ = (m,k)`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  `k ≤ strlen s` by metis_tac[parse_vb_int_le]>>
  once_rewrite_tac[walk_list_def]>>
  qpat_x_assum`parse_vb_int _ _ _ = _`
    (fn th => simp_tac (srw_ss()) [th,LET_THM] >> assume_tac th)>>
  xlet_autop>>
  xif
  >- (xvar>>xsimpl)>>
  xlet_autop>>
  xif
  >- suspend "Pos">>
  xlet`POSTv dv. &NUM (Num (-m)) dv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    xapp>>xsimpl>>
    qexists_tac`m`>>
    rw[NUM_def]>>
    `(&Num (-m):int) = 0 - m` by intLib.ARITH_TAC>>
    simp[])>>
  xlet_autop>>
  xlet`POSTv cv.
    &INT (if ¬(Num (-m) ≤ prev) ∧ srt then &cand else -&cand - 1) cv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    xif
    >- (
      xlet_autop>>
      xif
      >- (xvar>>xsimpl>>Cases_on`srt`>>gvs[])>>
      xapp>>xsimpl>>
      qexists_tac`if srt then &cand else -&cand - 1`>>
      Cases_on`srt`>>gvs[]
      >- (
        rw[]>>
        `-1 - &cand = -&cand - 1:int` by intLib.ARITH_TAC>>
        gvs[])>>
      `F` suffices_by simp[]>>
      qpat_x_assum`¬(_ < 0)` mp_tac>>
      intLib.ARITH_TAC)>>
    xvar>>xsimpl)>>
  xlet_autop>>
  xif
  >- suspend "Cand">>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` ARRAY_OF_length_spec))
  >- xsimpl>>
  xlet_autop>>
  xif
  >- suspend "Absent">>
  xlet`POSTv cv. &vcclause_TYPE (EL (Num (-m)) fmlls) cv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`vcclause_TYPE` ARRAY_OF_unsafe_sub_spec)>>
    qrefinel [`_`,`fmlls`,`Num (-m)`]>>
    xsimpl)>>
  `any_el (Num (-m)) fmlls vcc_none = EL (Num (-m)) fmlls`
    by simp[any_el_ALT]>>
  xlet_auto_spec (SOME is_vcc_none_arr_spec)
  >- xsimpl>>
  xif
  >- suspend "Dead">>
  qabbrev_tac`D = EL (Num (-m)) fmlls`>>
  `bnd_clause D (LENGTH sarr)` by (
    fs[bnd_fml_def]>>
    first_x_assum (qspec_then`Num (-m)` mp_tac)>>
    simp[])>>
  xlet_autop>>
  xlet`POSTve
    (λrv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      SEP_EXISTS r dml' tally'.
        ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
        &(red_pass_list fmlls dml b (piv ≠ 0) piv sarr tally D (length D)
            s k (strlen s) = SOME (r,dml',tally') ∧ NUM r rv))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      SEP_EXISTS dml' tally'.
        ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
        &(Fail_exn e ∧
          red_pass_list fmlls dml b (piv ≠ 0) piv sarr tally D (length D)
            s k (strlen s) = NONE))`
  >- (
    xapp_spec red_pass_arr_spec>>
    xsimpl>>
    rpt conj_tac
    >- (
      qpat_x_assum`bnd_clause D _` mp_tac>>
      simp[bnd_clause_def])
    >- fs[Abbr`D`]>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    metis_tac[SEP_IMP_REFL])>>
  `r ≤ strlen s` by metis_tac[red_pass_list_le]>>
  `stamps_ok dml' b` by metis_tac[stamps_ok_red_pass_list]>>
  `LENGTH dml' = LENGTH dml ∧ LENGTH tally' = LENGTH tally`
    by metis_tac[red_pass_list_LENGTH]>>
  xlet_autop>>
  xif
  >- suspend "Zr"
  >- suspend "Live"
QED

Resume walk_arr_spec[Live]:
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[skip_hints_vb_side])>>
  qpat_x_assum`_ ≠ 0 ⇒ _` (drule_then assume_tac)>>
  xapp>>
  xsimpl>>
  metis_tac[skip_hints_vb_le]
QED

Resume walk_arr_spec[Zr]:
  rpt xlet_autop>>
  xraise>>xsimpl>>
  gvs[Fail_exn_def]>>
  qexistsl_tac[`dml'`,`tally'`]>>
  conj_tac
  >- metis_tac[]>>
  xsimpl
QED

Resume walk_arr_spec[Absent]:
  `any_el (Num (-m)) fmlls vcc_none = vcc_none` by simp[any_el_ALT]>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[skip_hints_vb_side])>>
  qpat_x_assum`any_el _ _ _ = vcc_none ⇒ _` (drule_then assume_tac)>>
  xapp>>
  xsimpl>>
  metis_tac[skip_hints_vb_le]
QED

Resume walk_arr_spec[Dead]:
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[skip_hints_vb_side])>>
  qpat_x_assum`EL _ _ = vcc_none ⇒ _` (drule_then assume_tac)>>
  xapp>>
  xsimpl>>
  metis_tac[skip_hints_vb_le]
QED

Resume walk_arr_spec[Pos]:
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  qexistsl_tac[`dml`,`tally`]>>
  conj_tac
  >- metis_tac[]>>
  xsimpl
QED

Resume walk_arr_spec[Cand]:
  xlet_autop>>
  xlet`POSTv kv. &INT (if ¬(Num (-m) ≤ prev) ∧ srt then &k else -&k - 1) kv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    RULE_ASSUM_TAC (REWRITE_RULE [cand_enc_lt_0])>>
    xif
    >- (
      xapp>>xsimpl>>
      qexists_tac`&k`>>
      gvs[NUM_def]>>
      rw[]>>
      `-1 - &k = -&k - 1:int` by intLib.ARITH_TAC>>
      gvs[])>>
    xvar>>xsimpl>>
    gvs[NUM_def])>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[skip_hints_vb_side])>>
  qpat_x_assum`_ = n ⇒ _` (drule_then assume_tac)>>
  xapp>>
  xsimpl>>
  gvs[]>>
  metis_tac[skip_hints_vb_le]
QED

Finalise walk_arr_spec;

(***
  The candidate's round
 ***)

Quote add_cakeml:
  fun cand_pass_arr lno fml carr b piv sarr c i s k =
  if i = 0 then
    (if k = 0 then False
     else
       (case unit_prop_vb_arr lno fml carr b s k (String.size s) of
         None => True
       | Some j => False))
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 c
      val l = Unsafe.vsub c i1
      val y = img_code_arr piv sarr carr l
      val kk = Array.length carr
    in
      if Unsafe.Arith.eqWitness y kk carr then True
      else if Unsafe.Arith.eqWitness y (Unsafe.Arith.subWitness 0 kk carr) carr
      then cand_pass_arr lno fml carr b piv sarr c i1 s k
      else
        let
          val m = (if y = 0 then l else y)
          val n = var_arr carr m
          val bm = stamp_arr carr b m
          val st = Unsafe.sub carr n
        in
          if Unsafe.Arith.< st b then
            (Unsafe.update carr n bm;
             cand_pass_arr lno fml carr b piv sarr c i1 s k)
          else if Unsafe.Arith.= st bm then
            cand_pass_arr lno fml carr b piv sarr c i1 s k
          else True
        end
    end
End

val cl_tm = ``sub (C:int vector) (i − 1)``;
val cy_tm = ``img_code (piv ≠ 0) (piv:int) (sarr:int list) ^cl_tm``;
val cm_tm = ``if ^cy_tm = 0 then ^cl_tm else ^cy_tm``;
val cn_tm = ``Num (ABS ^cm_tm)``;
val cbm_tm = ``if ^cm_tm > 0 then b + 1 else (b:num)``;

Theorem cand_pass_arr_spec:
  ∀i dml fmlls b rat piv sarr C s k
   lnov bv pivv cv iv sv kv.
  NUM lno lnov ∧ NUM b bv ∧
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  vcclause_TYPE C cv ∧ NUM i iv ∧ STRING_TYPE s sv ∧ NUM k kv ∧
  stamps_ok dml b ∧ bnd_fml fmlls (LENGTH dml) ∧
  i ≤ length C ∧ (∀j. j < i ⇒ Num (ABS (sub C j)) < LENGTH sarr) ∧
  img_bnd rat piv sarr ∧ LENGTH sarr = LENGTH dml ∧
  Num (ABS piv) ≤ LENGTH sarr ∧ k ≤ strlen s ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "cand_pass_arr" (get_ml_prog_state()))
    [lnov; fmlv; carrv; bv; pivv; sarrv; cv; iv; sv; kv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
     ARRAY_OF INT sarrv (lit_sarr sarr))
    (POSTve
      (λv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS res dml'.
          ARRAY_OF NUM carrv dml' *
          &(cand_pass_list fmlls dml b rat piv sarr C i s k (strlen s) =
              SOME (res,dml') ∧ BOOL res v))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml'.
          ARRAY_OF NUM carrv dml' *
          &(Fail_exn e ∧
            cand_pass_list fmlls dml b rat piv sarr C i s k (strlen s) =
              NONE)))
Proof
  completeInduct_on`i`>>
  rpt strip_tac>>
  qpat_x_assum`rat ⇔ _` SUBST_ALL_TAC>>
  drule_then strip_assume_tac stamps_ok_bounds>>
  xcf "cand_pass_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- suspend "Base">>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[UnsafeProgTheory.vsub_side_def])>>
  `Num (ABS ^cl_tm) < LENGTH sarr` by simp[]>>
  xlet_auto_spec (SOME img_code_arr_spec)
  >- xsimpl>>
  xlet`POSTv kv'. &NUM (LENGTH dml) kv' * ARRAY_OF NUM carrv dml *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr)`,
      `dml`]>>
    xsimpl)>>
  `Num (ABS ^cy_tm) ≤ LENGTH sarr` by metis_tac[img_bnd_def]>>
  `LENGTH dml ≠ 0` by (strip_tac>>gvs[])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xif
  >- suspend "Top">>
  qpat_x_assum`∀m. m < i ⇒ ∀dml. _` (qspec_then`i − 1` mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>intLib.ARITH_TAC)>>
  xif
  >- suspend "Bot">>
  once_rewrite_tac[cand_pass_list_def]>>
  simp[]>>
  xlet_autop>>
  xlet`POSTv mv'. &INT (^cm_tm) mv' * ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr)`
  >- (
    xif>>
    xvar>>xsimpl)>>
  `^cn_tm < LENGTH dml` by (
    irule img_lit_bound>>
    qexists_tac`LENGTH dml`>>
    gvs[])>>
  xlet_auto_spec (SOME var_arr_spec)
  >- (xsimpl>>simp[])>>
  xlet_auto_spec (SOME stamp_arr_spec)
  >- (xsimpl>>simp[])>>
  xlet`POSTv stv. &NUM (EL ^cn_tm dml) stv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_sub_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr)`,
      `dml`,`^cn_tm`]>>
    xsimpl)>>
  xlet_auto_spec (SOME num_lt_spec)
  >- (xsimpl>>simp[])>>
  `any_el ^cn_tm dml 0 = EL ^cn_tm dml` by simp[any_el_ALT]>>
  xif
  >- suspend "Assign">>
  xlet_auto_spec (SOME num_eq_spec)
  >- (xsimpl>>rw[])>>
  xif
  >- suspend "Same">>
  xcon>>xsimpl>>
  simp[BOOL_def]>>
  EVAL_TAC
QED

Resume cand_pass_arr_spec[Base]:
  once_rewrite_tac[cand_pass_list_def]>>
  simp[]>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[BOOL_def]>>
    EVAL_TAC)>>
  xlet_autop>>
  `IS_SOME (unit_prop_vb_list' fmlls dml b s k (strlen s))`
    by simp[unit_prop_vb_list'_SOME]>>
  gvs[IS_SOME_EXISTS]>>
  rename1`unit_prop_vb_list' _ _ _ _ _ _ = SOME ures`>>
  drule unit_prop_vb_list'>>
  strip_tac>>
  xlet_auto
  >- (
    qexists_tac`ARRAY_OF INT sarrv (lit_sarr sarr)`>>
    xsimpl>>
    rpt strip_tac>>
    qexists_tac`x`>>
    xsimpl)
  >- (
    xsimpl>>
    metis_tac[SEP_IMP_REFL])>>
  gvs[]>>
  Cases_on`b'`>>gvs[OPTION_TYPE_def]>>
  xmatch>>
  xcon>>xsimpl>>
  simp[BOOL_def]>>
  EVAL_TAC
QED

Resume cand_pass_arr_spec[Top]:
  once_rewrite_tac[cand_pass_list_def]>>
  simp[]>>
  xcon>>xsimpl>>
  simp[BOOL_def]>>
  EVAL_TAC
QED

Resume cand_pass_arr_spec[Bot]:
  `dml ≠ []` by (strip_tac>>gvs[])>>
  once_rewrite_tac[cand_pass_list_def]>>
  simp[]>>
  xapp>>
  qexistsl_tac [`emp`,`sarr`,`s`,`piv`,`k`,`fmlls`,`dml`,`b`,`C`]>>
  xsimpl
QED

Resume cand_pass_arr_spec[Assign]:
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM carrv (LUPDATE (^cbm_tm) ^cn_tm dml) *
    ARRAY_OF INT sarrv (lit_sarr sarr)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr)`,
      `dml`,`^cbm_tm`,`^cn_tm`]>>
    xsimpl)>>
  `stamps_ok (LUPDATE (^cbm_tm) ^cn_tm dml) b` by
    simp[stamps_ok_LUPDATE_stamp]>>
  xapp>>
  simp[]
QED

Resume cand_pass_arr_spec[Same]:
  xapp>>
  simp[]
QED

Finalise cand_pass_arr_spec;

(***
  Occurrence counts below the watermark
 ***)

Definition dec_num_def:
  dec_num (x:num) = if x = 0 then 0 else x - 1
End

val res = translate dec_num_def;

Theorem dec_num_eq:
  dec_num x = x − 1
Proof
  rw[dec_num_def]
QED

Quote add_cakeml:
  fun add_counts_arr c i cnt =
  if i = 0 then ()
  else
    let val i1 = Unsafe.Arith.subWitness i 1 c in
      (inc_tally_arr cnt (lit_code_arr cnt (Unsafe.vsub c i1));
       add_counts_arr c i1 cnt)
    end
End

Theorem add_counts_arr_spec:
  ∀c i cnt cv iv.
  vcclause_TYPE c cv ∧ NUM i iv ∧ i ≤ length c ∧ codes_in c (LENGTH cnt) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "add_counts_arr" (get_ml_prog_state()))
    [cv; iv; cntv]
    (ARRAY_OF NUM cntv cnt)
    (POSTv uv. &UNIT_TYPE () uv * ARRAY_OF NUM cntv (add_counts c i cnt))
Proof
  ho_match_mp_tac add_counts_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  xcf "add_counts_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[Once add_counts_def,ARRAY_OF_refl])>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[UnsafeProgTheory.vsub_side_def])>>
  `lit_code (sub c (i − 1)) < LENGTH cnt` by fs[codes_in_def]>>
  xlet_auto_spec (SOME lit_code_arr_spec)
  >- (
    xsimpl>>
    qpat_x_assum`lit_code _ < _` mp_tac>>
    rw[lit_code_def])>>
  xlet_auto_spec (SOME inc_tally_arr_spec)
  >- xsimpl>>
  simp[Once add_counts_def]>>
  xapp>>
  qexists_tac`emp`>>
  simp[inc_tally_def]>>
  xsimpl
QED

Quote add_cakeml:
  fun sub_counts_arr c i cnt =
  if i = 0 then ()
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 c
      val k = lit_code_arr cnt (Unsafe.vsub c i1)
    in
      (Unsafe.update cnt k (dec_num (Unsafe.sub cnt k));
       sub_counts_arr c i1 cnt)
    end
End

Theorem sub_counts_arr_spec:
  ∀c i cnt cv iv.
  vcclause_TYPE c cv ∧ NUM i iv ∧ i ≤ length c ∧ codes_in c (LENGTH cnt) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "sub_counts_arr" (get_ml_prog_state()))
    [cv; iv; cntv]
    (ARRAY_OF NUM cntv cnt)
    (POSTv uv. &UNIT_TYPE () uv * ARRAY_OF NUM cntv (sub_counts c i cnt))
Proof
  ho_match_mp_tac sub_counts_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  xcf "sub_counts_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[Once sub_counts_def,ARRAY_OF_refl])>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[UnsafeProgTheory.vsub_side_def])>>
  `lit_code (sub c (i − 1)) < LENGTH cnt` by fs[codes_in_def]>>
  xlet_auto_spec (SOME lit_code_arr_spec)
  >- (
    xsimpl>>
    qpat_x_assum`lit_code _ < _` mp_tac>>
    rw[lit_code_def])>>
  xlet`POSTv xv. &NUM (EL (lit_code (sub c (i − 1))) cnt) xv *
    ARRAY_OF NUM cntv cnt`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_sub_spec)>>
    xsimpl)>>
  xlet_auto
  >- (
    qexists_tac`ARRAY_OF NUM cntv cnt`>>
    xsimpl)>>
  xlet`POSTv uv. ARRAY_OF NUM cntv
    (LUPDATE (EL (lit_code (sub c (i − 1))) cnt − 1)
      (lit_code (sub c (i − 1))) cnt)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
    xsimpl>>
    qexistsl_tac [`emp`,`cnt`,`EL (lit_code (sub c (i − 1))) cnt − 1`,
      `lit_code (sub c (i − 1))`]>>
    simp[dec_num_eq]>>
    xsimpl>>
    fs[dec_num_eq])>>
  simp[Once sub_counts_def]>>
  xapp>>
  simp[]
QED


Quote add_cakeml:
  fun catch_up_arr fml j lim cnt =
  if Unsafe.Arith.ltWitness j lim fml then
    let val c = Unsafe.sub fml j in
      (if is_vcc_none_arr c then ()
       else add_counts_arr c (Vector.length c) cnt;
       catch_up_arr fml (Unsafe.Arith.addWitness j 1 fml) lim cnt)
    end
  else ()
End

Theorem catch_up_arr_spec:
  ∀fmlls j lim cnt jv limv.
  NUM j jv ∧ NUM lim limv ∧
  j ≤ lim ∧ lim ≤ LENGTH fmlls ∧ codes_fml fmlls (LENGTH cnt) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "catch_up_arr" (get_ml_prog_state()))
    [fmlv; jv; limv; cntv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM cntv cnt)
    (POSTv uv. &UNIT_TYPE () uv * ARRAY_OF vcclause_TYPE fmlv fmlls *
      ARRAY_OF NUM cntv (catch_up fmlls j lim cnt))
Proof
  ho_match_mp_tac catch_up_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  xcf "catch_up_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` int_lt_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  once_rewrite_tac[catch_up_def]>>
  reverse xif
  >- (xcon>>xsimpl)>>
  `j < LENGTH fmlls` by simp[]>>
  `any_el j fmlls vcc_none = EL j fmlls` by simp[any_el_ALT]>>
  xlet`POSTv cv. &vcclause_TYPE (EL j fmlls) cv * ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM cntv cnt`
  >- (
    xapp_spec (Q.ISPEC`vcclause_TYPE` ARRAY_OF_unsafe_sub_spec)>>
    qrefinel [`_`,`fmlls`,`j`]>>
    xsimpl)>>
  xlet_auto_spec (SOME is_vcc_none_arr_spec)
  >- xsimpl>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM cntv (if EL j fmlls = vcc_none then cnt
      else add_counts (EL j fmlls) (length (EL j fmlls)) cnt)`
  >- (
    xif
    >- (xcon>>xsimpl>>simp[ARRAY_OF_refl])>>
    xlet_autop>>
    xapp_spec add_counts_arr_spec>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls`,`length (EL j fmlls)`,`cnt`,
      `EL j fmlls`]>>
    fs[codes_fml_def]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` num_add_arr_spec))
  >- xsimpl>>
  qpat_x_assum`_ < lim ⇒ _` (drule_then assume_tac)>>
  gvs[]>>
  Cases_on`EL j fmlls = vcc_none`>>
  gvs[]
  >- (xapp>>simp[])>>
  xapp>>
  simp[]
QED

Quote add_cakeml:
  fun insert_cnt_arr fml cnt wm n c =
  (if n < wm then add_counts_arr c (Vector.length c) cnt else ();
   insert_clause_arr fml n c)
End

Theorem insert_cnt_arr_spec:
  NUM wm wmv ∧ NUM n nv ∧ vcclause_TYPE c cv ∧
  codes_in c (LENGTH cnt) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "insert_cnt_arr" (get_ml_prog_state()))
    [fmlv; cntv; wmv; nv; cv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM cntv cnt)
    (POSTv fmlv'.
      ARRAY_OF vcclause_TYPE fmlv' (FST (insert_cnt_list fmlls cnt wm n c)) *
      ARRAY_OF NUM cntv (SND (insert_cnt_list fmlls cnt wm n c)))
Proof
  strip_tac>>
  simp[insert_cnt_list_def]>>
  xcf "insert_cnt_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM cntv (if n < wm then add_counts c (length c) cnt else cnt)`
  >- (
    xif
    >- (
      xlet_autop>>
      xapp_spec add_counts_arr_spec>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls`,`length c`,`cnt`,`c`]>>
      simp[]>>
      xsimpl)>>
    xcon>>xsimpl>>
    simp[ARRAY_OF_refl])>>
  xapp_spec insert_clause_arr_spec>>
  qrefinel [`_`,`c`,`n`,`fmlls`]>>
  xsimpl
QED

Quote add_cakeml:
  fun delete_cnt_arr fml cnt wm k =
  (if k < wm then
     let val c = Unsafe.sub fml k in
       if is_vcc_none_arr c then ()
       else sub_counts_arr c (Vector.length c) cnt
     end
   else ();
   delete_arr vcc_none fml k)
End

Theorem delete_cnt_arr_spec:
  NUM wm wmv ∧ NUM k kv ∧
  wm ≤ LENGTH fmlls ∧
  codes_fml fmlls (LENGTH cnt) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_cnt_arr" (get_ml_prog_state()))
    [fmlv; cntv; wmv; kv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM cntv cnt)
    (POSTv uv.
      ARRAY_OF vcclause_TYPE fmlv (FST (delete_cnt_list fmlls cnt wm k)) *
      ARRAY_OF NUM cntv (SND (delete_cnt_list fmlls cnt wm k)))
Proof
  strip_tac>>
  simp[delete_cnt_list_def]>>
  xcf "delete_cnt_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM cntv (if k < wm then
      (if EL k fmlls = vcc_none then cnt
       else sub_counts (EL k fmlls) (length (EL k fmlls)) cnt)
      else cnt)`
  >- (
    reverse xif
    >- (xcon>>xsimpl>>simp[ARRAY_OF_refl])>>
    xlet`POSTv cv. &vcclause_TYPE (EL k fmlls) cv * ARRAY_OF vcclause_TYPE fmlv fmlls *
      ARRAY_OF NUM cntv cnt`
    >- (
      xapp_spec (Q.ISPEC`vcclause_TYPE` ARRAY_OF_unsafe_sub_spec)>>
      qrefinel [`_`,`fmlls`,`k`]>>
      xsimpl)>>
    xlet_auto_spec (SOME is_vcc_none_arr_spec)
    >- xsimpl>>
    xif
    >- (xcon>>xsimpl>>simp[ARRAY_OF_refl])>>
    xlet_autop>>
    xapp_spec sub_counts_arr_spec>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls`,`length (EL k fmlls)`,`cnt`,
      `EL k fmlls`]>>
    fs[codes_fml_def]>>
    xsimpl)>>
  assume_tac vcc_none_v_thm>>
  xapp_spec (INST_TYPE [alpha |-> ``:int vector``] delete_arr_spec)>>
  qrefinel [`_`,`k`,`fmlls`,`vcc_none`,`vcclause_TYPE`]>>
  xsimpl
QED

Quote add_cakeml:
  fun delete_ids_cnt_arr fml cnt wm s i1 len =
  case parse_vb_int s i1 len of (m,i) =>
  if m <= 0 then ()
  else
    (delete_cnt_arr fml cnt wm m; delete_ids_cnt_arr fml cnt wm s i len)
End

Theorem delete_ids_cnt_arr_spec:
  ∀fmlls cnt wm s i len sv iv lenv.
  NUM wm wmv ∧ STRING_TYPE s sv ∧ NUM i iv ∧ NUM len lenv ∧
  len ≤ strlen s ∧ i ≤ len ∧
  count_rel fmlls cnt wm ∧
  codes_fml fmlls (LENGTH cnt) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_ids_cnt_arr" (get_ml_prog_state()))
    [fmlv; cntv; wmv; sv; iv; lenv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM cntv cnt)
    (POSTv uv.
      ARRAY_OF vcclause_TYPE fmlv
        (FST (delete_ids_cnt_list fmlls cnt wm s i len)) *
      ARRAY_OF NUM cntv (SND (delete_ids_cnt_list fmlls cnt wm s i len)))
Proof
  ho_match_mp_tac delete_ids_cnt_list_ind>>
  rpt strip_tac>>
  once_rewrite_tac[delete_ids_cnt_list_def]>>
  xcf "delete_ids_cnt_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (
    xsimpl>>
    fs[parse_vb_int_side])>>
  Cases_on`parse_vb_int s i len`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xif
  >- (xcon>>xsimpl)>>
  `∃n. q = &n` by (qexists_tac`Num q`>>intLib.ARITH_TAC)>>
  gvs[GSYM NUM_def]>>
  imp_res_tac parse_vb_int_le>>
  Cases_on`delete_cnt_list fmlls cnt wm n`>>
  rename1`delete_cnt_list _ _ _ _ = (fmlls1,cnt1)`>>
  simp[]>>
  `wm ≤ LENGTH fmlls` by fs[count_rel_def]>>
  drule_all count_rel_delete_cnt_list>>
  strip_tac>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls1 * ARRAY_OF NUM cntv cnt1`
  >- (
    xapp_spec delete_cnt_arr_spec>>
    xsimpl>>
    qexistsl_tac [`emp`,`wm`,`n`,`fmlls`,`cnt`]>>
    xsimpl)>>
  xapp>>
  gvs[]
QED

(***
  The substitution array, the certificate and the tally
 ***)

Overload w_TYPE = ``LIST_TYPE (PAIR_TYPE NUM (SUM_TYPE BOOL INT))``

(* Write each entry (v,x) of the witness into the array image of sarr: the
  image code of v at 2v and that of ¬v at 2v + 1; kk is the length of the
  map, the code of ⊤ *)
Quote add_cakeml:
  fun fill_subst_arr kk w sarr carr =
  case w of
    [] => ()
  | (vx::w) =>
    (case vx of (v,x) =>
      let
        val e = (case x of
                   Inl b => (if b then kk else Unsafe.Arith.subWitness 0 kk carr)
                 | Inr m => m)
        val c = Unsafe.Arith.addWitness v v carr
      in
        (Unsafe.update sarr c e;
         Unsafe.update sarr (Unsafe.Arith.addWitness c 1 carr)
           (Unsafe.Arith.subWitness 0 e carr);
         fill_subst_arr kk w sarr carr)
      end)
End

Theorem fill_subst_arr_spec:
  ∀w sarr wv.
  NUM (LENGTH dml) kkv ∧ LENGTH sarr = LENGTH dml ∧ w_TYPE w wv ∧
  w_bnd w (LENGTH dml) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fill_subst_arr" (get_ml_prog_state()))
    [kkv; wv; sarrv; carrv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml)
    (POSTv uv. &UNIT_TYPE () uv *
      ARRAY_OF INT sarrv (lit_sarr (fill_subst (LENGTH dml) w sarr)) *
      ARRAY_OF NUM carrv dml)
Proof
  Induct>>
  rpt strip_tac>>
  xcf "fill_subst_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (xmatch>>simp[fill_subst_def]>>xcon>>xsimpl)>>
  PairCases_on`h`>>
  fs[PAIR_TYPE_def,w_bnd_def]>>
  xmatch>>
  xmatch>>
  xlet`POSTv ev. &INT (enc_img (LENGTH dml) h1) ev *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml`
  >- (
    Cases_on`h1`>>
    fs[SUM_TYPE_def]>>
    xmatch
    >- (
      xif
      >- (xvar>>xsimpl>>fs[enc_img_def,NUM_def])>>
      xapp_prepare_goal>>
      irule cfAppTheory.app_wgframe>>
      irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
      qexistsl_tac [`&LENGTH dml`,`dml`,`0`,
        `ARRAY_OF INT sarrv (lit_sarr sarr)`]>>
      gvs[NUM_def,INT_def,enc_img_def]>>
      xsimpl>>
      intLib.ARITH_TAC)>>
    xvar>>xsimpl>>
    simp[enc_img_def])>>
  qabbrev_tac`e = enc_img (LENGTH dml) h1`>>
  `Num (ABS e) ≤ LENGTH dml` by (
    Cases_on`h1`>>
    rw[Abbr`e`,enc_img_def]>>
    fs[])>>
  xlet`POSTv cv. &NUM (2 * h0) cv * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM carrv dml`
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any (Q.ISPEC`NUM` int_add_arr_spec)>>
    qexistsl_tac [`&h0`,`dml`,`&h0`,`ARRAY_OF INT sarrv (lit_sarr sarr)`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl>>
    intLib.ARITH_TAC)>>
  xlet`POSTv uv. ARRAY_OF INT sarrv (LUPDATE e (2 * h0) (lit_sarr sarr)) *
    ARRAY_OF NUM carrv dml`
  >- (
    xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml`,`lit_sarr sarr`,`e`,`2 * h0`]>>
    simp[]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
  >- (xsimpl>>intLib.ARITH_TAC)>>
  xlet`POSTv cv. &NUM (2 * h0 + 1) cv *
    ARRAY_OF INT sarrv (LUPDATE e (2 * h0) (lit_sarr sarr)) *
    ARRAY_OF NUM carrv dml`
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any (Q.ISPEC`NUM` int_add_arr_spec)>>
    qexistsl_tac [`1`,`dml`,`&(2 * h0)`,
      `ARRAY_OF INT sarrv (LUPDATE e (2 * h0) (lit_sarr sarr))`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl>>
    intLib.ARITH_TAC)>>
  xlet`POSTv uv. ARRAY_OF INT sarrv (lit_sarr (LUPDATE e h0 sarr)) *
    ARRAY_OF NUM carrv dml`
  >- (
    xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml`,
      `LUPDATE e (2 * h0) (lit_sarr sarr)`,`-e`,`2 * h0 + 1`]>>
    simp[lit_sarr_LUPDATE,Abbr`e`]>>
    xsimpl)>>
  xapp>>
  qexistsl_tac [`emp`,`LUPDATE e h0 sarr`]>>
  simp[fill_subst_def,Abbr`e`]>>
  xsimpl
QED

(* Clearing the image of a substitution that was never filled changes
  nothing *)
Theorem clear_subst_zero:
  ∀w sarr. EVERY ($= 0) sarr ⇒ clear_subst w sarr = sarr
Proof
  Induct>>
  simp[clear_subst_def,FORALL_PROD]>>
  rw[]>>
  `LUPDATE 0 p_1 sarr = sarr` by (
    rw[LIST_EQ_REWRITE,EL_LUPDATE]>>
    rw[]>>
    gvs[EVERY_EL])>>
  simp[]
QED

(* Reset the tally entries of the witness's literals, and the array image
  of sarr unless the line is RAT (piv ≠ 0), whose substitution was never
  filled *)
Quote add_cakeml:
  fun clear_arr piv w sarr carr tally =
  case w of
    [] => ()
  | (vx::w) =>
    (case vx of (v,x) =>
      let
        val c = Unsafe.Arith.addWitness v v carr
        val c1 = Unsafe.Arith.addWitness c 1 carr
      in
        (Unsafe.update tally c 0;
         Unsafe.update tally c1 0;
         (if piv = 0 then (Unsafe.update sarr c 0; Unsafe.update sarr c1 0)
          else ());
         clear_arr piv w sarr carr tally)
      end)
End

Theorem clear_arr_spec:
  ∀w sarr tally wv.
  INT piv pivv ∧ (piv ≠ 0 ⇒ EVERY ($= 0) sarr) ∧
  LENGTH sarr = LENGTH dml ∧ 2 * LENGTH sarr ≤ LENGTH tally ∧
  w_TYPE w wv ∧ EVERY (λ(v,x). 0 < v ∧ v < LENGTH sarr) w ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "clear_arr" (get_ml_prog_state()))
    [pivv; wv; sarrv; carrv; tallyv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
     ARRAY_OF NUM tallyv tally)
    (POSTv uv. &UNIT_TYPE () uv *
      ARRAY_OF INT sarrv (lit_sarr (clear_subst w sarr)) *
      ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv (clear_tally w tally))
Proof
  Induct>>
  rpt strip_tac>>
  xcf "clear_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (xmatch>>simp[clear_subst_def,clear_tally_def]>>xcon>>xsimpl)>>
  PairCases_on`h`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xmatch>>
  xlet`POSTv cv. &NUM (2 * h0) cv * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any (Q.ISPEC`NUM` int_add_arr_spec)>>
    qexistsl_tac [`&h0`,`dml`,`&h0`,
      `ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl>>
    intLib.ARITH_TAC)>>
  xlet`POSTv cv. &NUM (2 * h0 + 1) cv * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any (Q.ISPEC`NUM` int_add_arr_spec)>>
    qexistsl_tac [`1`,`dml`,`&(2 * h0)`,
      `ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl>>
    intLib.ARITH_TAC)>>
  `lit_code (&h0) = 2 * h0 ∧ lit_code (-&h0) = 2 * h0 + 1`
    by simp[lit_code_def]>>
  qabbrev_tac`tally1 = LUPDATE 0 (2 * h0 + 1) (LUPDATE 0 (2 * h0) tally)`>>
  xlet`POSTv uv. ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
    ARRAY_OF NUM tallyv (LUPDATE 0 (2 * h0) tally)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml`,
      `tally`,`0`,`2 * h0`]>>
    simp[]>>
    xsimpl)>>
  xlet`POSTv uv. ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
    ARRAY_OF NUM tallyv tally1`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml`,
      `LUPDATE 0 (2 * h0) tally`,`0`,`2 * h0 + 1`]>>
    simp[Abbr`tally1`]>>
    xsimpl)>>
  xlet_autop>>
  xlet`POSTv uv.
    ARRAY_OF INT sarrv (lit_sarr (if piv = 0 then LUPDATE 0 h0 sarr else sarr)) *
    ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally1`
  >- (
    reverse xif
    >- (xcon>>xsimpl)>>
    xlet`POSTv uv.
      ARRAY_OF INT sarrv (LUPDATE 0 (2 * h0) (lit_sarr sarr)) *
      ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally1`
    >- (
      xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_update_spec)>>
      qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally1`,
        `lit_sarr sarr`,`0`,`2 * h0`]>>
      simp[]>>
      xsimpl)>>
    xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally1`,
      `LUPDATE 0 (2 * h0) (lit_sarr sarr)`,`0`,`2 * h0 + 1`]>>
    simp[lit_sarr_LUPDATE]>>
    xsimpl)>>
  `piv ≠ 0 ⇒ LUPDATE 0 h0 sarr = sarr` by (
    rw[LIST_EQ_REWRITE,EL_LUPDATE]>>
    rw[]>>
    gvs[EVERY_EL])>>
  xapp>>
  qexistsl_tac [`emp`,`tally1`,`if piv = 0 then LUPDATE 0 h0 sarr else sarr`]>>
  simp[clear_subst_def,clear_tally_def,Abbr`tally1`]>>
  IF_CASES_TAC>>
  gvs[]>>
  xsimpl
QED

(* The certificate for the literal l: its count equals its tally, unless σ
  leaves l alone or maps it to ⊤ *)
Quote add_cakeml:
  fun cert_lit_arr piv sarr carr cnt tally l =
  let val y = img_code_arr piv sarr carr l in
    if y = 0 then True
    else if Unsafe.Arith.eqWitness y l carr then True
    else if Unsafe.Arith.eqWitness y (Array.length carr) carr then True
    else
      let val c = lit_code_arr carr l in
        Unsafe.sub tally c = Unsafe.sub cnt c
      end
  end
End

Theorem cert_lit_arr_spec:
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧ INT l lv ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  img_bnd rat piv sarr ∧ Num (ABS l) < LENGTH sarr ∧
  2 * LENGTH sarr ≤ LENGTH tally ∧ 2 * LENGTH sarr ≤ LENGTH cnt ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "cert_lit_arr" (get_ml_prog_state()))
    [pivv; sarrv; carrv; cntv; tallyv; lv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
     ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally)
    (POSTv bv. &BOOL (cert_lit rat piv sarr cnt tally l) bv *
      ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
      ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally)
Proof
  strip_tac>>
  qpat_x_assum`rat ⇔ _` SUBST_ALL_TAC>>
  xcf "cert_lit_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME img_code_arr_spec)
  >- xsimpl>>
  qabbrev_tac`y = img_code (piv ≠ 0) piv sarr l`>>
  `Num (ABS y) ≤ LENGTH sarr` by metis_tac[img_bnd_def]>>
  simp[cert_lit_def]>>
  xlet_autop>>
  xif
  >- (xcon>>xsimpl>>simp[BOOL_def]>>EVAL_TAC)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[])>>
  xif
  >- (xcon>>xsimpl>>simp[BOOL_def]>>EVAL_TAC)>>
  xlet`POSTv kv. &NUM (LENGTH dml) kv * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM cntv cnt *
    ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM cntv cnt *
      ARRAY_OF NUM tallyv tally`,`dml`]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xif
  >- (xcon>>xsimpl>>simp[BOOL_def]>>EVAL_TAC)>>
  xlet_auto_spec (SOME lit_code_arr_spec)
  >- (xsimpl>>simp[])>>
  `lit_code l < 2 * LENGTH sarr` by simp[lit_code_bound]>>
  xlet`POSTv cv. &NUM (EL (lit_code l) cnt) cv * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM cntv cnt *
    ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_sub_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv tally`,`cnt`,`lit_code l`]>>
    xsimpl)>>
  xlet`POSTv tv. &NUM (EL (lit_code l) tally) tv * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM cntv cnt *
    ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_sub_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM cntv cnt`,`tally`,`lit_code l`]>>
    xsimpl)>>
  xapp_spec (MATCH_MP (DISCH_ALL mlbasicsProgTheory.eq_v_thm)
    (CONJUNCT1 EqualityType_NUM_BOOL))>>
  xsimpl>>
  qexistsl_tac [`EL (lit_code l) cnt`,`EL (lit_code l) tally`]>>
  simp[]
QED

Quote add_cakeml:
  fun cert_list_arr piv sarr carr cnt tally w =
  case w of
    [] => True
  | (vx::w) =>
    (case vx of (v,x) =>
      if cert_lit_arr piv sarr carr cnt tally v then
        (if cert_lit_arr piv sarr carr cnt tally
              (Unsafe.Arith.subWitness 0 v carr)
         then cert_list_arr piv sarr carr cnt tally w
         else False)
      else False)
End

Theorem cert_list_arr_spec:
  ∀w wv.
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧ w_TYPE w wv ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  img_bnd rat piv sarr ∧ EVERY (λ(v,x). v < LENGTH sarr) w ∧
  2 * LENGTH sarr ≤ LENGTH tally ∧ 2 * LENGTH sarr ≤ LENGTH cnt ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "cert_list_arr" (get_ml_prog_state()))
    [pivv; sarrv; carrv; cntv; tallyv; wv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
     ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally)
    (POSTv bv. &BOOL (cert_list rat piv sarr cnt tally w) bv *
      ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
      ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally)
Proof
  Induct>>
  rpt strip_tac>>
  xcf "cert_list_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def,cert_list_def]
  >- (xmatch>>xcon>>xsimpl>>EVAL_TAC)>>
  PairCases_on`h`>>
  gvs[PAIR_TYPE_def,cert_list_def]>>
  xmatch>>
  xmatch>>
  xlet`POSTv bv. &BOOL (cert_lit (piv ≠ 0) piv sarr cnt tally (&h0)) bv *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
    ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec cert_lit_arr_spec>>
    xsimpl>>
    gvs[NUM_def])>>
  reverse xif
  >- (xcon>>xsimpl>>EVAL_TAC)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xlet`POSTv bv. &BOOL (cert_lit (piv ≠ 0) piv sarr cnt tally (-&h0)) bv *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
    ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec cert_lit_arr_spec>>
    xsimpl>>
    qexistsl_tac [`emp`,`tally`,`sarr`,`piv`,`-&h0`,`dml`,`cnt`]>>
    xsimpl>>
    gvs[])>>
  reverse xif
  >- (xcon>>xsimpl>>EVAL_TAC)>>
  xapp>>
  simp[]
QED

(* aux holds the arrays indexed by literal code and the watermark. They grow
  with the map; otherwise aux itself is returned, so a line that grows
  nothing allocates nothing here. *)
Quote add_cakeml:
  fun grow_arr carr aux =
  case aux of (sarr, cnt, wm, tally) =>
  let val n2 = Unsafe.Arith.addWitness (Array.length carr)
                 (Array.length carr) carr in
  if Unsafe.Arith.ltWitness (Array.length cnt) n2 carr then
    let
      val cnt1 = Array.array n2 0
      val u = Array.copy cnt cnt1 0
    in
      (Array.array n2 0, cnt1, wm, Array.array n2 0)
    end
  else aux
  end
End

(* The heap image of aux: the array image of sarr, the counts, the
  watermark and the tally *)
Definition AUX_def:
  AUX (sarr:int list) cnt (wm:num) tally auxv =
  SEP_EXISTS sarrv cntv wmv tallyv.
    &(auxv = Conv NONE [sarrv; cntv; wmv; tallyv] ∧ NUM wm wmv) *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM cntv cnt *
    ARRAY_OF NUM tallyv tally
End

Theorem grow_arr_spec:
  LENGTH sarr ≤ LENGTH dml ∧ LENGTH cnt = 2 * LENGTH sarr ∧
  LENGTH tally = LENGTH cnt ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "grow_arr" (get_ml_prog_state()))
    [carrv; auxv]
    (ARRAY_OF NUM carrv dml * AUX sarr cnt wm tally auxv)
    (POSTv v.
      ARRAY_OF NUM carrv dml *
      AUX (FST (grow_list (LENGTH dml) sarr cnt tally))
        (FST (SND (grow_list (LENGTH dml) sarr cnt tally))) wm
        (SND (SND (grow_list (LENGTH dml) sarr cnt tally))) v * GC)
Proof
  strip_tac>>
  xcf "grow_arr" (get_ml_prog_state ())>>
  simp[AUX_def]>>
  xpull>>
  xmatch>>
  qabbrev_tac`frame = ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM cntv cnt *
    ARRAY_OF NUM tallyv tally`>>
  ntac 2 (
    xlet`POSTv kv. &NUM (LENGTH dml) kv * ARRAY_OF NUM carrv dml * frame`
    >- (
      xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
      qexistsl_tac [`frame`,`dml`]>>
      xsimpl))>>
  xlet`POSTv nv. &NUM (2 * LENGTH dml) nv * ARRAY_OF NUM carrv dml * frame`
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any (Q.ISPEC`NUM` int_add_arr_spec)>>
    qexistsl_tac [`&LENGTH dml`,`dml`,`&LENGTH dml`,`frame`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl>>
    intLib.ARITH_TAC)>>
  xlet`POSTv kv. &NUM (LENGTH cnt) kv * ARRAY_OF NUM carrv dml * frame`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv tally`,`cnt`]>>
    xsimpl>>
    simp[Abbr`frame`]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_lt_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  simp[grow_list_def]>>
  reverse xif
  >- (
    xvar>>xsimpl>>
    simp[Abbr`frame`,GC_STAR_GC]>>
    xsimpl)>>
  simp[Abbr`frame`]>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` ARRAY_OF_alloc_spec))
  >- xsimpl>>
  xlet`POSTv uv. ARRAY_OF NUM av (cnt ++ REPLICATE (2 * LENGTH dml − LENGTH cnt) 0) *
    ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_copy_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv tally`,`cnt`,`REPLICATE (LENGTH cnt) 0`,`[]`,
      `REPLICATE (2 * LENGTH dml − LENGTH cnt) 0`]>>
    simp[REPLICATE_APPEND,NUM_def,INT_def]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` ARRAY_OF_alloc_spec))
  >- xsimpl>>
  rename1`ARRAY_OF NUM tv (REPLICATE _ _)`>>
  xlet`POSTv sv. ARRAY_OF INT sv (REPLICATE (2 * LENGTH dml) 0) *
    ARRAY_OF NUM tv (REPLICATE (2 * LENGTH dml) 0) *
    ARRAY_OF NUM av (cnt ++ REPLICATE (2 * LENGTH dml − LENGTH cnt) 0) *
    ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`INT` ARRAY_OF_alloc_spec)>>
    qexistsl_tac [`ARRAY_OF NUM tv (REPLICATE (2 * LENGTH dml) 0) *
      ARRAY_OF NUM av (cnt ++ REPLICATE (2 * LENGTH dml − LENGTH cnt) 0) *
      ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM cntv cnt * ARRAY_OF NUM tallyv tally`,
      `0`,`2 * LENGTH dml`]>>
    xsimpl>>
    simp[INT_def])>>
  xcon>>
  xsimpl>>
  simp[lit_sarr_REPLICATE,GSYM STAR_ASSOC,GC_STAR_GC]>>
  xsimpl
QED

(***
  One step of the proof
 ***)

val _ = register_type ``:lsr``;

val LSR_LSR_TYPE_def = fetch "-" "LSR_LSR_TYPE_def";

(* The pivot of a RAT line, and 0 on any other line *)
Definition piv_of_def:
  (piv_of [(v,INL b)] = if b then (&v:int) else -&v) ∧
  (piv_of (w:(num # (bool + int)) list) = 0)
End

Theorem piv_of_rat_pivot:
  EVERY wf_entry w ⇒
  (case rat_pivot w of NONE => (F,0) | SOME p => (T,p)) =
  (piv_of w ≠ 0, piv_of w)
Proof
  Cases_on`w`>>simp[rat_pivot_def,piv_of_def]>>
  rename1`x::w`>>
  PairCases_on`x`>>
  Cases_on`x1`>>Cases_on`w`>>
  simp[rat_pivot_def,piv_of_def,wf_entry_def]>>
  rw[]
QED

Theorem piv_of_NZ:
  piv_of w ≠ 0 ⇒ ∃v b. w = [(v,INL b)]
Proof
  Cases_on`w`>>simp[piv_of_def]>>
  PairCases_on`h`>>Cases_on`h1`>>Cases_on`t`>>simp[piv_of_def]
QED

Quote add_cakeml:
  fun piv_of_arr w carr =
  case w of
    [(v, Inl b)] => (if b then v else Unsafe.Arith.subWitness 0 v carr)
  | _ => 0
End

Theorem piv_of_arr_spec:
  w_TYPE w wv ∧ w_bnd w (LENGTH dml) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "piv_of_arr" (get_ml_prog_state()))
    [wv; carrv]
    (ARRAY_OF NUM carrv dml)
    (POSTv v. &INT (piv_of w) v * ARRAY_OF NUM carrv dml)
Proof
  strip_tac>>
  xcf "piv_of_arr" (get_ml_prog_state ())>>
  Cases_on`w`>>gvs[LIST_TYPE_def]
  >- (xmatch>>xlit>>xsimpl>>simp[piv_of_def])>>
  PairCases_on`h`>>Cases_on`h1`>>Cases_on`t`>>
  gvs[LIST_TYPE_def,PAIR_TYPE_def,SUM_TYPE_def,piv_of_def,w_bnd_def]>>
  xmatch
  >- (
    xif
    >- (xvar>>xsimpl>>gvs[NUM_def])>>
    xapp_prepare_goal>>
    irule cfAppTheory.app_weaken>>
    irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
    qexistsl_tac [`&h0`,`0`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl)>>
  xlit>>xsimpl
QED

Quote add_cakeml:
  fun is_live_arr fml n =
  if n < Array.length fml then
    (if is_vcc_none_arr (Unsafe.sub fml n) then False else True)
  else False
End

Theorem is_live_arr_spec:
  NUM n nv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_live_arr" (get_ml_prog_state()))
    [fmlv; nv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls)
    (POSTv bv. &BOOL (any_el n fmlls vcc_none ≠ vcc_none) bv *
      ARRAY_OF vcclause_TYPE fmlv fmlls)
Proof
  strip_tac>>
  xcf "is_live_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` ARRAY_OF_length_spec))
  >- (qrefinel [`_`,`fmlls`]>>xsimpl)>>
  xlet_autop>>
  simp[any_el_ALT]>>
  reverse xif
  >- (xcon>>xsimpl)>>
  xlet`POSTv cv. &vcclause_TYPE (EL n fmlls) cv * ARRAY_OF vcclause_TYPE fmlv fmlls`
  >- (
    xapp_spec (Q.ISPEC`vcclause_TYPE` ARRAY_OF_unsafe_sub_spec)>>
    xsimpl)>>
  xlet_auto_spec (SOME is_vcc_none_arr_spec)
  >- xsimpl>>
  xif
  >- (xcon>>xsimpl)>>
  xcon>>xsimpl
QED

(***
  Group ids out of order: the line is accepted when no id repeats
 ***)

(* In a sorted list a repeated id appears twice in a row *)
Definition dup_sorted_def:
  (dup_sorted ((x:num)::y::ys) ⇔ x = y ∨ dup_sorted (y::ys)) ∧
  (dup_sorted _ ⇔ F)
End

Definition has_dup_def:
  has_dup (l:num list) ⇔ dup_sorted (sort $<= l)
End

val res = translate dup_sorted_def;
val res = translate has_dup_def;

Theorem dup_sorted_SORTED:
  ∀l. SORTED $<= l ⇒ (dup_sorted l ⇔ ¬ALL_DISTINCT l)
Proof
  ho_match_mp_tac dup_sorted_ind>>
  rw[dup_sorted_def]>>
  `transitive ($<= : num -> num -> bool)`
    by simp[relationTheory.transitive_def]>>
  gvs[SORTED_EQ]>>
  metis_tac[arithmeticTheory.LESS_EQUAL_ANTISYM]
QED

Theorem has_dup_ALL_DISTINCT:
  has_dup l ⇔ ¬ALL_DISTINCT l
Proof
  `SORTED $<= (sort $<= l)` by (
    irule sort_SORTED>>
    simp[relationTheory.transitive_def,relationTheory.total_def])>>
  simp[has_dup_def,dup_sorted_SORTED]>>
  metis_tac[ALL_DISTINCT_PERM,sort_PERM]
QED

(* The group ids from offset g, last first, onto acc *)
Quote add_cakeml:
  fun group_ids_arr s g acc =
  case parse_vb_int s g (String.size s) of (m,k) =>
  if 0 <= m then acc
  else group_ids_arr s (skip_hints_vb s k (String.size s)) ((0 - m) :: acc)
End

Theorem group_ids_arr_spec:
  ∀s g len acc sv gv accv.
  STRING_TYPE s sv ∧ NUM g gv ∧ len = strlen s ∧ g ≤ len ∧
  LIST_TYPE NUM acc accv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "group_ids_arr" (get_ml_prog_state()))
    [sv; gv; accv]
    emp
    (POSTv v. &LIST_TYPE NUM (REVERSE (group_ids s g len) ++ acc) v)
Proof
  ho_match_mp_tac group_ids_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  gvs[]>>
  xcf "group_ids_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>fs[parse_vb_int_side])>>
  Cases_on`parse_vb_int s g (strlen s)`>>
  rename1`parse_vb_int s g _ = (m,k)`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  `k ≤ strlen s` by metis_tac[parse_vb_int_le]>>
  once_rewrite_tac[group_ids_def]>>
  qpat_x_assum`parse_vb_int _ _ _ = _`
    (fn th => simp_tac (srw_ss()) [th,LET_THM] >> assume_tac th)>>
  xlet_autop>>
  xif
  >- (xvar>>xsimpl)>>
  xlet`POSTv dv. &NUM (Num (-m)) dv`
  >- (
    xapp>>xsimpl>>
    qexists_tac`m`>>
    rw[NUM_def]>>
    `(&Num (-m):int) = 0 - m` by intLib.ARITH_TAC>>
    simp[])>>
  xlet`POSTv lv. &LIST_TYPE NUM (Num (-m)::acc) lv`
  >- (xcon>>xsimpl>>simp[LIST_TYPE_def])>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[skip_hints_vb_side])>>
  qpat_x_assum`¬(0 ≤ m) ⇒ _` (drule_then assume_tac)>>
  xapp>>
  xsimpl>>
  qexists_tac`Num (-m)::acc`>>
  gvs[skip_hints_vb_le]>>
  once_rewrite_tac[GSYM APPEND_ASSOC]>>
  rewrite_tac[APPEND]
QED

(***
  The fallback when the certificate fails: a round without hints for every
  live clause outside the groups that has a literal of L
 ***)

val res = translate fb_hints_def;
val res = translate sort_ids_def;

(* Some literal of d below index i is in L *)
Quote add_cakeml:
  fun has_L_arr piv sarr carr d i =
  if i = 0 then False
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 d
      val l = Unsafe.vsub d i1
      val y = img_code_arr piv sarr carr l
    in
      if y = 0 then has_L_arr piv sarr carr d i1
      else if Unsafe.Arith.eqWitness y l carr then has_L_arr piv sarr carr d i1
      else if Unsafe.Arith.eqWitness y (Array.length carr) carr then
        has_L_arr piv sarr carr d i1
      else True
    end
End

Theorem has_L_arr_spec:
  ∀rat piv sarr D i pivv sarrv dv iv.
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  img_bnd rat piv sarr ∧
  vcclause_TYPE D dv ∧ NUM i iv ∧ i ≤ length D ∧
  (∀j. j < i ⇒ Num (ABS (sub D j)) < LENGTH sarr) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "has_L_arr" (get_ml_prog_state()))
    [pivv; sarrv; carrv; dv; iv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml)
    (POSTv v. &BOOL (has_L_list rat piv sarr D i) v *
      ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml)
Proof
  ho_match_mp_tac has_L_list_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  xcf "has_L_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    simp[Once has_L_list_def]>>
    xcon>>xsimpl)>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[UnsafeProgTheory.vsub_side_def])>>
  `Num (ABS (sub D (i − 1))) < LENGTH sarr` by simp[]>>
  simp[Once has_L_list_def]>>
  qabbrev_tac`l = sub D (i − 1)`>>
  qabbrev_tac`y = img_code (piv ≠ 0) piv sarr l`>>
  xlet`POSTv yv. &INT y yv *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml`
  >- (
    xapp_spec img_code_arr_spec>>
    xsimpl>>
    qexistsl_tac [`emp`,`sarr`,`piv`,`l`,`dml`]>>
    xsimpl>>
    simp[Abbr`y`])>>
  `Num (ABS y) ≤ LENGTH sarr` by gvs[img_bnd_def,Abbr`y`]>>
  xlet_autop>>
  xif
  >- (
    qpat_x_assum`_ ∨ _ ⇒ _` mp_tac>>
    impl_tac
    >- gvs[NUM_def]>>
    strip_tac>>
    xapp>>xsimpl>>gvs[])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[])>>
  xif
  >- (
    qpat_x_assum`_ ∨ _ ⇒ _` mp_tac>>
    impl_tac
    >- gvs[NUM_def]>>
    strip_tac>>
    xapp>>xsimpl>>gvs[])>>
  xlet`POSTv kv. &NUM (LENGTH dml) kv *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr)`,`dml`]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xif
  >- (
    qpat_x_assum`_ = &LENGTH dml ⇒ _` mp_tac>>
    impl_tac
    >- simp[]>>
    strip_tac>>
    xapp>>xsimpl>>gvs[])>>
  xcon>>xsimpl>>
  gvs[NUM_def]
QED

(* The round of the clause c outside the groups, as fb_clause_list *)
Quote add_cakeml:
  fun fb_clause_arr lno fml carr b piv sarr tally c =
  if is_vcc_none_arr c then ()
  else if has_L_arr piv sarr carr c (Vector.length c) then
    (if red_pass_arr lno fml carr b piv sarr tally c (Vector.length c)
          fb_hints 1 = 0
     then raise Fail (format_failure lno
       "a clause with a moved literal has no group and its reduct is not refuted")
     else ())
  else ()
End

Theorem fb_clause_arr_spec:
  NUM lno lnov ∧ NUM b bv ∧ INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  vcclause_TYPE c cv ∧
  stamps_ok dml b ∧ bnd_fml fmlls (LENGTH dml) ∧
  (c ≠ vcc_none ⇒ bnd_clause c (LENGTH sarr)) ∧ img_bnd rat piv sarr ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  2 * LENGTH sarr ≤ LENGTH tally ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fb_clause_arr" (get_ml_prog_state()))
    [lnov; fmlv; carrv; bv; pivv; sarrv; tallyv; cv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
     ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally)
    (POSTve
      (λv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(fb_clause_list fmlls dml b rat piv sarr tally c = SOME (dml',tally') ∧
            UNIT_TYPE () v))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(Fail_exn e ∧ fb_clause_list fmlls dml b rat piv sarr tally c = NONE)))
Proof
  strip_tac>>
  xcf "fb_clause_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME is_vcc_none_arr_spec)
  >- xsimpl>>
  xif
  >- (
    simp[fb_clause_list_def]>>
    xcon>>xsimpl)>>
  gvs[bnd_clause_def]>>
  xlet_autop>>
  xlet_auto_spec (SOME has_L_arr_spec)
  >- (
    xsimpl>>
    simp[])>>
  reverse xif
  >- (
    simp[fb_clause_list_def]>>
    xcon>>xsimpl)>>
  xlet_autop>>
  assume_tac (fetch "-" "fb_hints_v_thm")>>
  xlet`POSTve
    (λrv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      SEP_EXISTS r dml' tally'.
        ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
        &(red_pass_list fmlls dml b (piv ≠ 0) piv sarr tally c (length c)
            fb_hints 1 1 = SOME (r,dml',tally') ∧ NUM r rv))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      SEP_EXISTS dml' tally'.
        ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
        &(Fail_exn e ∧
          red_pass_list fmlls dml b (piv ≠ 0) piv sarr tally c (length c)
            fb_hints 1 1 = NONE))`
  >- (
    xapp_spec red_pass_arr_spec>>
    xsimpl>>
    qexistsl_tac [`emp`,`tally`,`sarr`,`fb_hints`,`piv`,`length c`,`fmlls`,`dml`,`b`,
      `c`,`lno`]>>
    xsimpl>>
    simp[fb_hints_def]>>
    rw[]>>
    xsimpl>>
    qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv dmlx * ARRAY_OF NUM tallyv tallyx`>>
    qexistsl_tac [`dmlx`,`tallyx`]>>
    xsimpl)
  >- (
    xsimpl>>
    rw[fb_clause_list_def]>>
    qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv dmlx * ARRAY_OF NUM tallyv tallyx`>>
    qexistsl_tac [`dmlx`,`tallyx`]>>
    xsimpl)>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[fb_clause_list_def,Fail_exn_def]>>
    qexistsl_tac [`dml'`,`tally'`]>>
    conj_tac
    >- metis_tac[]>>
    xsimpl)>>
  xcon>>xsimpl>>
  simp[fb_clause_list_def]>>
  xsimpl
QED

(* The scan over the ids from j below lim, skipping those in ids, as
  fb_list *)
Quote add_cakeml:
  fun fb_scan_arr lno fml carr b piv sarr tally ids j lim =
  if lim <= j then ()
  else
    case ids of
      x :: ids' =>
      if x <= j then
        fb_scan_arr lno fml carr b piv sarr tally ids'
          (if x = j then j + 1 else j) lim
      else
        (fb_clause_arr lno fml carr b piv sarr tally (Unsafe.sub fml j);
         fb_scan_arr lno fml carr b piv sarr tally ids (j + 1) lim)
    | [] =>
      (fb_clause_arr lno fml carr b piv sarr tally (Unsafe.sub fml j);
       fb_scan_arr lno fml carr b piv sarr tally ids (j + 1) lim)
End

Theorem fb_scan_arr_spec:
  ∀fmlls dml b rat piv sarr tally ids j lim
   lnov bv pivv tallyv idsv jv limv.
  NUM lno lnov ∧ NUM b bv ∧ INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  LIST_TYPE NUM ids idsv ∧ NUM j jv ∧ NUM lim limv ∧
  stamps_ok dml b ∧ bnd_fml fmlls (LENGTH dml) ∧
  bnd_fml fmlls (LENGTH sarr) ∧ img_bnd rat piv sarr ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  2 * LENGTH sarr ≤ LENGTH tally ∧ lim ≤ LENGTH fmlls ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "fb_scan_arr" (get_ml_prog_state()))
    [lnov; fmlv; carrv; bv; pivv; sarrv; tallyv; idsv; jv; limv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
     ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally)
    (POSTve
      (λv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(fb_list fmlls dml b rat piv sarr tally ids j lim = SOME (dml',tally') ∧
            UNIT_TYPE () v))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(Fail_exn e ∧ fb_list fmlls dml b rat piv sarr tally ids j lim = NONE)))
Proof
  ho_match_mp_tac fb_list_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  xcf "fb_scan_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    simp[Once fb_list_def]>>
    xcon>>xsimpl)>>
  reverse (Cases_on`ids`)>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >>> HEADGOAL (
    qmatch_goalsub_rename_tac`fb_list _ _ _ _ _ _ _ (x::ids1) j lim`>>
    xlet_autop>>
    xif
    >- (
      xlet_autop>>
      xlet`POSTv kv. &NUM (if x = j then j + 1 else j) kv *
        ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
        ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
      >- (
        xif
        >- (
          xapp>>xsimpl>>
          qexists_tac`&j`>>
          gvs[NUM_def,integerTheory.INT_ADD])>>
        xvar>>xsimpl)>>
      qpat_x_assum`x ≤ j ⇒ _` mp_tac>>
      simp[]>>
      strip_tac>>
      simp[Once fb_list_def]>>
      xapp>>
      xsimpl>>
      rpt strip_tac>>
      qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv dmlx * ARRAY_OF NUM tallyv tallyx`>>
      qexistsl_tac [`dmlx`,`tallyx`]>>
      simp[Once fb_list_def]>>
      xsimpl))
  >>> ALLGOALS (
    `j < LENGTH fmlls` by simp[]>>
    xlet`POSTv cv. &vcclause_TYPE (EL j fmlls) cv *
      ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
      ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
    >- (
      xapp_spec (Q.ISPEC`vcclause_TYPE` ARRAY_OF_unsafe_sub_spec)>>
      qrefinel [`_`,`fmlls`,`j`]>>
      xsimpl)>>
    `any_el j fmlls vcc_none = EL j fmlls` by simp[any_el_ALT]>>
    `EL j fmlls ≠ vcc_none ⇒ bnd_clause (EL j fmlls) (LENGTH sarr)` by (
      gvs[bnd_fml_def]>>
      metis_tac[])>>
    xlet`POSTve
      (λuv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml1 tally1.
          ARRAY_OF NUM carrv dml1 * ARRAY_OF NUM tallyv tally1 *
          &(fb_clause_list fmlls dml b (piv ≠ 0) piv sarr tally (EL j fmlls) =
              SOME (dml1,tally1)))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml1 tally1.
          ARRAY_OF NUM carrv dml1 * ARRAY_OF NUM tallyv tally1 *
          &(Fail_exn e ∧
            fb_clause_list fmlls dml b (piv ≠ 0) piv sarr tally (EL j fmlls) = NONE))`
    >- (
      xapp_spec fb_clause_arr_spec>>
      xsimpl>>
      qexistsl_tac [`emp`,`tally`,`sarr`,`piv`,`fmlls`,`dml`,`EL j fmlls`,`b`,`lno`]>>
      xsimpl>>
      rw[]>>
      qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv dmlx * ARRAY_OF NUM tallyv tallyx`>>
      qexistsl_tac [`dmlx`,`tallyx`]>>
      xsimpl)
    >- (
      xsimpl>>
      rw[]>>
      qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv dmlx * ARRAY_OF NUM tallyv tallyx`>>
      qexistsl_tac [`dmlx`,`tallyx`]>>
      simp[Once fb_list_def]>>
      xsimpl)>>
    `LENGTH dml1 = LENGTH dml ∧ LENGTH tally1 = LENGTH tally ∧ stamps_ok dml1 b` by (
      gvs[fb_clause_list_def,AllCaseEqs()]>>
      metis_tac[red_pass_list_LENGTH,stamps_ok_red_pass_list])>>
    xlet_autop>>
    qpat_x_assum`∀dml' tally'. _` (qspecl_then [`dml1`,`tally1`] mp_tac)>>
    simp[]>>
    strip_tac>>
    simp[Once fb_list_def]>>
    xapp>>
    xsimpl>>
    rpt strip_tac>>
    qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv dmlx * ARRAY_OF NUM tallyv tallyx`>>
    qexistsl_tac [`dmlx`,`tallyx`]>>
    simp[Once fb_list_def]>>
    xsimpl)
QED

(* The state is the formula, the map and its stamp, tp, and aux. A RUP line
  and a deletion return aux as it is; a non-RUP line moves the watermark to
  the catch-up limit. *)
Quote add_cakeml:
  fun check_lsr_arr lno lsr fml carr b tp aux =
  case lsr of
    Delvb s i =>
      (case aux of (sarr, cnt, wm, tally) =>
        (delete_ids_cnt_arr fml cnt wm s i (String.size s);
         (fml, carr, b, tp, aux)))
  | Lsrvb n c w h =>
    if is_live_arr fml n then
      raise Fail (format_failure lno "clause id already in use")
    else
    let val sz = sz_witness w (sz_lit_map (Vector.length c) c 0) in
    case reset_dm_arr carr b sz of (carr1, b1) =>
    let
      val aux1 = grow_arr carr1 aux
      val tp1 = (if tp <= n then n + 1 else tp)
    in
    case aux1 of (sarr1, cnt1, wm, tally1) =>
    case rup_dm_vb_arr lno fml carr1 b1 c h of
      None =>
        let val fml1 = insert_cnt_arr fml cnt1 wm n c in
          (fml1, carr1, b1, tp1, aux1)
        end
    | Some i0 =>
      let
        val piv = piv_of_arr w carr1
        val u = (if piv = 0
                 then fill_subst_arr (Array.length carr1) w sarr1 carr1
                 else ())
        val r = walk_arr lno fml carr1 b1 piv sarr1 tally1 n h i0 0 0
        val cand =
          (if r < 0 then
             (if has_dup (group_ids_arr h i0 []) then
                raise Fail (format_failure lno "duplicate group id")
              else ~1 - r)
           else r)
        val lim = (if tp < Array.length fml then tp else Array.length fml)
        val u2 = catch_up_arr fml wm lim cnt1
        val u4 =
          (if cert_list_arr piv sarr1 carr1 cnt1 tally1 w then ()
           else
             fb_scan_arr lno fml carr1 b1 piv sarr1 tally1
               (sort_ids (group_ids_arr h i0 [])) 0 lim)
      in
        if cand_pass_arr lno fml carr1 b1 piv sarr1 c (Vector.length c) h
             cand then
          let
            val fml1 = insert_cnt_arr fml cnt1 lim n c
            val u3 = clear_arr piv w sarr1 carr1 tally1
          in
            (fml1, carr1, b1, tp1, (sarr1, cnt1, lim, tally1))
          end
        else
          raise Fail (format_failure lno "candidate round did not conflict")
      end
    end
    end
End

(* A deletion record's offset is within the record *)
Definition lsr_vb_ok_def:
  (lsr_vb_ok (Delvb s i) ⇔ i ≤ strlen s) ∧
  (lsr_vb_ok (Lsrvb n c w h) ⇔ T)
End

Theorem parse_lsr_one_vb_ok:
  parse_lsr_one lines = SOME (SOME (step,rest)) ⇒
  lsr_vb_ok step
Proof
  rw[parse_lsr_one_def]>>
  gvs[CaseEqs["list","option","sum","prod"],lsr_vb_ok_def]>>
  pop_assum mp_tac>>
  rw[parse_lsr_chunk_def]>>
  gvs[UNCURRY,lsr_vb_ok_def]
  >- (
    Cases_on`parse_vb_num l 1 (strlen l)`>>
    drule parse_vb_num_le>>
    simp[])>>
  qpat_x_assum`_ = SOME (INL step)` mp_tac>>
  IF_CASES_TAC>>
  simp[]>>
  TOP_CASE_TAC>>
  simp[]
QED

Theorem check_lsr_arr_spec:
  NUM lno lnov ∧ LSR_LSR_TYPE lsr lsrv ∧
  NUM b bv ∧ NUM tp tpv ∧
  lsr_inv fmlls dml b sarr cnt wm tally tp ∧ wf_lsr lsr ∧ lsr_vb_ok lsr ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lsr_arr" (get_ml_prog_state()))
    [lnov; lsrv; fmlv; carrv; bv; tpv; auxv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml * AUX sarr cnt wm tally auxv)
    (POSTve
      (λv. SEP_EXISTS fmlv' carrv' bv' tpv' auxv'.
        &(v = Conv NONE [fmlv'; carrv'; bv'; tpv'; auxv']) *
        SEP_EXISTS res.
          &(check_lsr_list lsr fmlls dml b sarr cnt wm tally tp = SOME res) *
          (case res of (fmlls',dml',b',sarr',cnt',wm',tally',tp') =>
            ARRAY_OF vcclause_TYPE fmlv' fmlls' *
            ARRAY_OF NUM carrv' dml' * AUX sarr' cnt' wm' tally' auxv' *
            &(NUM b' bv' ∧ NUM tp' tpv')) * GC)
      (λe. SEP_EXISTS fmlls'. ARRAY_OF vcclause_TYPE fmlv fmlls' * GC *
        &(Fail_exn e ∧
          check_lsr_list lsr fmlls dml b sarr cnt wm tally tp = NONE)))
Proof
  strip_tac>>
  `codes_fml fmlls (LENGTH cnt)`
    by gvs[lsr_inv_def,dm_ok_def,bnd_fml_codes_fml]>>
  xcf "check_lsr_arr" (get_ml_prog_state ())>>
  Cases_on`lsr`>>
  gvs[LSR_LSR_TYPE_def,lsr_vb_ok_def]
  >- (
    xmatch>>
    simp[AUX_def]>>
    xpull>>
    xmatch>>
    xlet_autop>>
    `count_rel fmlls cnt wm` by gvs[lsr_inv_def]>>
    xlet`POSTv uv.
      ARRAY_OF vcclause_TYPE fmlv
        (FST (delete_ids_cnt_list fmlls cnt wm m n (strlen m))) *
      ARRAY_OF NUM cntv (SND (delete_ids_cnt_list fmlls cnt wm m n (strlen m))) *
      ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv tally`
    >- (
      xapp_spec delete_ids_cnt_arr_spec>>
      qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF INT sarrv (lit_sarr sarr) *
        ARRAY_OF NUM tallyv tally`,`wm`,`m`,`strlen m`,`n`,`fmlls`,
        `cnt`]>>
      xsimpl)>>
    xcon>>
    xsimpl>>
    simp[check_lsr_list_def,AUX_def]>>
    Cases_on`delete_ids_cnt_list fmlls cnt wm m n (strlen m)`>>
    gvs[]>>
    xsimpl>>
    simp[GC_STAR_GC]>>
    xsimpl)>>
  rename1`Lsrvb n C w h`>>
  xmatch>>
  xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[check_lsr_list_def,Fail_exn_def,GC_STAR_GC]>>
    qexists_tac`fmlls`>>
    conj_tac
    >- metis_tac[]>>
    simp[GSYM STAR_ASSOC,GC_STAR_GC]>>
    xsimpl)>>
  gvs[lsr_inv_def,dm_ok_def,wf_lsr_def]>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    simp[ccnf_arrayProgTheory.sz_lit_map_side])>>
  xlet_autop>>
  qabbrev_tac`sz = sz_witness w (sz_lit_map (length C) C 0)`>>
  xlet_auto_spec (SOME reset_dm_arr_spec)
  >- (
    xsimpl>>
    rpt strip_tac>>
    qexists_tac`x`>>
    xsimpl)>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rename1`reset_dm_list dml b sz = (dml1,b1)`>>
  `dm_rel FEMPTY dml1 b1 ∧ sz ≤ LENGTH dml1`
    by metis_tac[dm_rel_reset_dm_list]>>
  `LENGTH dml ≤ LENGTH dml1` by metis_tac[reset_dm_list_LENGTH]>>
  `stamps_ok dml1 b1` by metis_tac[stamps_ok_reset_dm_list]>>
  `bnd_fml fmlls (LENGTH dml1)` by metis_tac[bnd_fml_le]>>
  `sz_lit_map (length C) C 0 ≤ sz` by simp[Abbr`sz`,sz_witness_mono]>>
  `bnd_clause C (LENGTH dml1)` by (
    irule bnd_clause_le>>
    qexists_tac`sz_lit_map (length C) C 0`>>
    simp[sz_lit_map_bnd_clause])>>
  `w_bnd w (LENGTH dml1)` by (
    qspecl_then [`w`,`sz_lit_map (length C) C 0`] assume_tac sz_witness_bnd>>
    gvs[w_bnd_def,EVERY_MEM,FORALL_PROD]>>
    rw[]>>res_tac>>gvs[Abbr`sz`])>>
  rename1`ARRAY_OF NUM carrv1 dml1`>>
  xlet`POSTv aux1v. ARRAY_OF NUM carrv1 dml1 * ARRAY_OF vcclause_TYPE fmlv fmlls *
    AUX (FST (grow_list (LENGTH dml1) sarr cnt tally))
      (FST (SND (grow_list (LENGTH dml1) sarr cnt tally))) wm
      (SND (SND (grow_list (LENGTH dml1) sarr cnt tally))) aux1v * GC`
  >- (
    xapp_spec grow_arr_spec>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls`,`wm`,`tally`,`sarr`,`dml1`,`cnt`]>>
    simp[]>>
    xsimpl>>
    simp[GSYM STAR_ASSOC,GC_STAR_GC]>>
    xsimpl)>>
  Cases_on`grow_list (LENGTH dml1) sarr cnt tally`>>
  rename1`_ = (sarr1,cnt1t)`>>
  PairCases_on`cnt1t`>>
  rename1`_ = (sarr1,cnt1,tally1)`>>
  qspecl_then [`LENGTH dml1`,`sarr`,`cnt`,`tally`,`sarr1`,`cnt1`,`tally1`]
    mp_tac grow_list_inv>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  gvs[]>>
  xlet`POSTv bv'. &BOOL (tp ≤ n) bv' * ARRAY_OF NUM carrv1 dml1 *
    ARRAY_OF vcclause_TYPE fmlv fmlls * AUX sarr1 cnt1 wm tally1 aux1v`
  >- (
    xapp>>
    qexistsl_tac [`ARRAY_OF NUM carrv1 dml1 * ARRAY_OF vcclause_TYPE fmlv fmlls *
      AUX sarr1 cnt1 wm tally1 aux1v * GC`,`&n`,`&tp`]>>
    gvs[NUM_def]>>
    xsimpl)>>
  xlet`POSTv tv. &NUM (MAX tp (n + 1)) tv * ARRAY_OF NUM carrv1 dml1 *
    ARRAY_OF vcclause_TYPE fmlv fmlls * AUX sarr1 cnt1 wm tally1 aux1v`
  >- (
    xif
    >- (
      xapp>>
      xsimpl>>
      qexists_tac`&n`>>
      gvs[NUM_def,MAX_DEF,integerTheory.INT_ADD])>>
    xvar>>xsimpl>>
    rw[MAX_DEF])>>
  simp[AUX_def]>>
  xpull>>
  xmatch>>
  xlet`POSTve
    (λrv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr1) *
      ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM tallyv tally1 *
      SEP_EXISTS r dml2. ARRAY_OF NUM carrv1 dml2 *
        &(rup_dm_vb_list fmlls dml1 b1 C h = SOME (r,dml2) ∧
          OPTION_TYPE NUM r rv))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr1) *
      ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM tallyv tally1 *
      SEP_EXISTS dml2. ARRAY_OF NUM carrv1 dml2 *
        &(Fail_exn e ∧ rup_dm_vb_list fmlls dml1 b1 C h = NONE))`
  >- (
    xapp_spec rup_dm_vb_arr_spec>>
    xsimpl>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr1) * ARRAY_OF NUM cntv cnt1 *
      ARRAY_OF NUM tallyv tally1`,`C`,`h`,`fmlls`,`b1`,`dml1`,`lno`]>>
    xsimpl>>
    rpt strip_tac>>
    qexists_tac`x`>>
    xsimpl)
  >- (
    xsimpl>>
    rw[]>>
    fs[check_lsr_list_def,Abbr`sz`]>>
    qexists_tac`fmlls`>>
    xsimpl)>>
  `LENGTH dml2 = LENGTH dml1` by metis_tac[rup_dm_vb_list_LENGTH]>>
  `stamps_ok dml2 b1` by metis_tac[stamps_ok_rup_dm_vb_list]>>
  Cases_on`r`>>
  gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    `codes_in C (LENGTH cnt1)` by gvs[bnd_clause_codes_in]>>
    xlet`POSTv fmlv1.
      ARRAY_OF vcclause_TYPE fmlv1 (FST (insert_cnt_list fmlls cnt1 wm n C)) *
      ARRAY_OF NUM cntv (SND (insert_cnt_list fmlls cnt1 wm n C)) *
      ARRAY_OF INT sarrv (lit_sarr sarr1) * ARRAY_OF NUM tallyv tally1 *
      ARRAY_OF NUM carrv1 dml2`
    >- (
      xapp_spec insert_cnt_arr_spec>>
      xsimpl>>
      qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr1) * ARRAY_OF NUM tallyv tally1 *
        ARRAY_OF NUM carrv1 dml2`,`wm`,`n`,`fmlls`,`cnt1`,`C`]>>
      xsimpl)>>
    Cases_on`insert_cnt_list fmlls cnt1 wm n C`>>
    rename1`_ = (fmlls2,cnt2)`>>
    xcon>>
    xsimpl>>
    simp[check_lsr_list_def]>>
    gvs[]>>
    simp[GSYM STAR_ASSOC,GC_STAR_GC]>>
    xsimpl)>>
  rename1`rup_dm_vb_list _ _ _ _ _ = SOME (SOME i0,dml2)`>>
  `i0 ≤ strlen h` by (
    fs[rup_dm_vb_list_def]>>
    drule unit_prop_vb_list_SOME_le>>
    simp[])>>
  drule_then assume_tac piv_of_rat_pivot>>
  simp[check_lsr_list_def,Abbr`sz`]>>
  `w_bnd w (LENGTH dml2)` by simp[]>>
  xlet`POSTv pv. &INT (piv_of w) pv * ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF INT sarrv (lit_sarr sarr1) * ARRAY_OF NUM cntv cnt1 *
    ARRAY_OF NUM tallyv tally1 * ARRAY_OF NUM carrv1 dml2`
  >- (
    xapp_spec piv_of_arr_spec>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr1) *
      ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM tallyv tally1`,`w`,`dml2`]>>
    xsimpl)>>
  qabbrev_tac`sarr2 = if piv_of w ≠ 0 then sarr1
    else fill_subst (LENGTH dml1) w sarr1`>>
  xlet_autop>>
  xlet`POSTv uv. ARRAY_OF INT sarrv (lit_sarr sarr2) * ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM tallyv tally1 * ARRAY_OF NUM carrv1 dml2`
  >- (
    reverse xif
    >- (
      xcon>>
      simp[Abbr`sarr2`]>>
      xsimpl)>>
    xlet`POSTv kv. &NUM (LENGTH dml2) kv * ARRAY_OF vcclause_TYPE fmlv fmlls *
      ARRAY_OF INT sarrv (lit_sarr sarr1) * ARRAY_OF NUM cntv cnt1 *
      ARRAY_OF NUM tallyv tally1 * ARRAY_OF NUM carrv1 dml2`
    >- (
      xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr1) *
        ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM tallyv tally1`,`dml2`]>>
      xsimpl)>>
    xapp_spec fill_subst_arr_spec>>
    xsimpl>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM cntv cnt1 *
      ARRAY_OF NUM tallyv tally1`,`w`,`sarr1`,`dml2`]>>
    simp[Abbr`sarr2`]>>
    xsimpl)>>
  `img_bnd (piv_of w ≠ 0) (piv_of w) sarr2 ∧ LENGTH sarr2 = LENGTH dml2 ∧
   Num (ABS (piv_of w)) ≤ LENGTH sarr2 ∧ EVERY ($= 0) (clear_subst w sarr2)` by (
    `w_bnd w (LENGTH sarr1)` by simp[]>>
    Cases_on`piv_of w = 0`>>
    simp[Abbr`sarr2`]
    >- (
      drule_all img_bnd_fill_subst>>
      drule_all clear_fill_subst>>
      simp[])>>
    drule piv_of_NZ>>
    strip_tac>>
    gvs[piv_of_def,w_bnd_def,img_bnd_rat,clear_subst_zero]>>
    rw[])>>
  xlet`POSTve
    (λrv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt1 *
      SEP_EXISTS cand srt dml3 tally2.
        ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2 *
        &(walk_list fmlls dml2 b1 (piv_of w ≠ 0) (piv_of w) sarr2 tally1 n h i0
            (strlen h) 0 0 T = SOME (cand,srt,dml3,tally2) ∧
          INT (if srt then &cand else -&cand - 1) rv))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt1 *
      SEP_EXISTS dml3 tally2.
        ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2 *
        &(Fail_exn e ∧
          walk_list fmlls dml2 b1 (piv_of w ≠ 0) (piv_of w) sarr2 tally1 n h i0
            (strlen h) 0 0 T = NONE))`
  >- (
    xapp_spec walk_arr_spec>>
    qexistsl_tac [`ARRAY_OF NUM cntv cnt1`,`tally1`,`T`,`sarr2`,`h`,`piv_of w ≠ 0`,
      `0`,`piv_of w`,`n`,`strlen h`,`i0`,`fmlls`,`dml2`,`0`,`b1`]>>
    simp[NUM_def,INT_def]>>
    xsimpl>>
    qexists_tac`lno`>>
    fs[NUM_def,INT_def]>>
    rpt strip_tac>>
    qexistsl_tac [`x`,`x'`]>>
    xsimpl)
  >- (xsimpl>>rw[]>>qexists_tac`fmlls`>>xsimpl)>>
  `LENGTH dml3 = LENGTH dml2 ∧ LENGTH tally2 = LENGTH tally1` by (
    drule_at (Pos last) walk_list_LENGTH>>
    simp[])>>
  `stamps_ok dml3 b1` by metis_tac[stamps_ok_walk_list]>>
  `cand ≤ strlen h` by (
    drule walk_list_cand_le>>
    simp[])>>
  xlet_autop>>
  xlet`POSTve
    (λkv. &(NUM cand kv ∧ (¬srt ⇒ ALL_DISTINCT (group_ids h i0 (strlen h)))) *
      ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM carrv1 dml3 *
      ARRAY_OF NUM tallyv tally2)
    (λe. &(Fail_exn e ∧ ¬srt ∧ ¬ALL_DISTINCT (group_ids h i0 (strlen h))) *
      ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM carrv1 dml3 *
      ARRAY_OF NUM tallyv tally2)`
  >- (
    RULE_ASSUM_TAC (REWRITE_RULE [cand_enc_lt_0])>>
    reverse xif
    >- (xvar>>xsimpl>>gvs[NUM_def])>>
    xlet_autop>>
    xlet`POSTv lv. &LIST_TYPE NUM (REVERSE (group_ids h i0 (strlen h)) ++ []) lv *
      ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM carrv1 dml3 *
      ARRAY_OF NUM tallyv tally2`
    >- (
      xapp_spec group_ids_arr_spec>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
        ARRAY_OF NUM cntv cnt1 * ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2`,
        `h`,`strlen h`,`i0`,`[]`]>>
      xsimpl>>
      simp[LIST_TYPE_def])>>
    xlet_autop>>
    xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      gvs[Fail_exn_def,has_dup_ALL_DISTINCT,ALL_DISTINCT_REVERSE]>>
      first_assum (irule_at Any))>>
    xapp>>xsimpl>>
    qexists_tac`-&cand - 1`>>
    gvs[NUM_def,has_dup_ALL_DISTINCT,ALL_DISTINCT_REVERSE]>>
    rw[]>>
    `-1 - (-&cand - 1) = &cand:int` by intLib.ARITH_TAC>>
    gvs[])
  >- (xsimpl>>rw[]>>qexists_tac`fmlls`>>gvs[]>>xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` ARRAY_OF_length_spec))
  >- xsimpl>>
  xlet_autop>>
  xlet`POSTv lv. &NUM (MIN tp (LENGTH fmlls)) lv * ARRAY_OF vcclause_TYPE fmlv fmlls *
    ARRAY_OF INT sarrv (lit_sarr sarr2) * ARRAY_OF NUM cntv cnt1 *
    ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2`
  >- (
    xif
    >- (xvar>>xsimpl>>gvs[MIN_DEF])>>
    xapp_spec (Q.ISPEC`vcclause_TYPE` ARRAY_OF_length_spec)>>
    qrefinel [`_`,`fmlls`]>>
    xsimpl>>
    gvs[MIN_DEF])>>
  qabbrev_tac`lim = MIN tp (LENGTH fmlls)`>>
  `wm ≤ lim ∧ lim ≤ LENGTH fmlls` by gvs[Abbr`lim`,count_rel_def]>>
  `codes_fml fmlls (LENGTH cnt1)` by simp[bnd_fml_codes_fml]>>
  `count_rel fmlls (catch_up fmlls wm lim cnt1) lim ∧
   LENGTH (catch_up fmlls wm lim cnt1) = LENGTH cnt1` by (
    irule count_rel_catch_up>>
    simp[])>>
  qabbrev_tac`cnt2 = catch_up fmlls wm lim cnt1`>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
    ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2`
  >- (
    xapp_spec catch_up_arr_spec>>
    xsimpl>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr2) * ARRAY_OF NUM carrv1 dml3 *
      ARRAY_OF NUM tallyv tally2`,`lim`,`wm`,`fmlls`,`cnt1`]>>
    simp[Abbr`cnt2`]>>
    xsimpl)>>
  xlet`POSTv bv. &BOOL (cert_list (piv_of w ≠ 0) (piv_of w) sarr2 cnt2 tally2 w) bv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
    ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2`
  >- (
    xapp_spec cert_list_arr_spec>>
    xsimpl>>
    `EVERY (λ(v,x). v < LENGTH sarr2) w` by (
      irule w_bnd_vars>>
      gvs[])>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls`,`w`,`tally2`,`sarr2`,`piv_of w`,`dml3`,
      `cnt2`]>>
    gvs[]>>
    xsimpl)>>
  qabbrev_tac`fb = fb_list fmlls dml3 b1 (piv_of w ≠ 0) (piv_of w) sarr2 tally2
    (sort_ids (group_ids h i0 (strlen h))) 0 lim`>>
  xlet`POSTve
    (λuv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt2 *
      SEP_EXISTS dml5 tally3.
        ARRAY_OF NUM carrv1 dml5 * ARRAY_OF NUM tallyv tally3 *
        &((if cert_list (piv_of w ≠ 0) (piv_of w) sarr2 cnt2 tally2 w
           then SOME (dml3,tally2) else fb) = SOME (dml5,tally3)))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt2 *
      SEP_EXISTS dml5 tally3.
        ARRAY_OF NUM carrv1 dml5 * ARRAY_OF NUM tallyv tally3 *
        &(Fail_exn e ∧
          (if cert_list (piv_of w ≠ 0) (piv_of w) sarr2 cnt2 tally2 w
           then SOME (dml3,tally2) else fb) = NONE))`
  >- (
    xif
    >- (xcon>>xsimpl)>>
    xlet_autop>>
    xlet`POSTv lv. &LIST_TYPE NUM (REVERSE (group_ids h i0 (strlen h)) ++ []) lv *
      ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2`
    >- (
      xapp_spec group_ids_arr_spec>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
        ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM carrv1 dml3 * ARRAY_OF NUM tallyv tally2`,
        `h`,`strlen h`,`i0`,`[]`]>>
      xsimpl>>
      simp[LIST_TYPE_def])>>
    xlet_autop>>
    RULE_ASSUM_TAC (REWRITE_RULE [sort_ids_REVERSE])>>
    xapp_spec fb_scan_arr_spec>>
    xsimpl>>
    qexistsl_tac [`ARRAY_OF NUM cntv cnt2`,`tally2`,`sarr2`,`piv_of w`,`lim`,
      `sort_ids (group_ids h i0 (strlen h))`,`fmlls`,`dml3`,`b1`,`lno`]>>
    xsimpl>>
    simp[Abbr`fb`]>>
    rpt strip_tac>>
    qmatch_goalsub_rename_tac`ARRAY_OF NUM carrv1 dmlx * ARRAY_OF NUM tallyv tallyx`>>
    qexistsl_tac [`dmlx`,`tallyx`]>>
    xsimpl)
  >- (xsimpl>>rw[]>>qexists_tac`fmlls`>>xsimpl)>>
  `LENGTH dml5 = LENGTH dml3 ∧ LENGTH tally3 = LENGTH tally2 ∧ stamps_ok dml5 b1` by (
    Cases_on`cert_list (piv_of w ≠ 0) (piv_of w) sarr2 cnt2 tally2 w`>>
    gvs[Abbr`fb`]>>
    metis_tac[fb_list_LENGTH,stamps_ok_fb_list])>>
  xlet_autop>>
  `∀j. j < length C ⇒ Num (ABS (sub C j)) < LENGTH sarr2` by
    gvs[bnd_clause_def]>>
  xlet`POSTve
    (λbv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM tallyv tally3 *
      SEP_EXISTS res dml4. ARRAY_OF NUM carrv1 dml4 *
        &(cand_pass_list fmlls dml5 b1 (piv_of w ≠ 0) (piv_of w) sarr2 C
            (length C) h cand (strlen h) = SOME (res,dml4) ∧ BOOL res bv))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr2) *
      ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM tallyv tally3 *
      SEP_EXISTS dml4. ARRAY_OF NUM carrv1 dml4 *
        &(Fail_exn e ∧
          cand_pass_list fmlls dml5 b1 (piv_of w ≠ 0) (piv_of w) sarr2 C
            (length C) h cand (strlen h) = NONE))`
  >- (
    xapp_spec cand_pass_arr_spec>>
    xsimpl>>
    qexistsl_tac [`ARRAY_OF NUM cntv cnt2 * ARRAY_OF NUM tallyv tally3`,`sarr2`,`h`,
      `piv_of w`,`cand`,`length C`,`fmlls`,`dml5`,`b1`,`C`,`lno`]>>
    gvs[]>>
    xsimpl>>
    rpt strip_tac>>
    qexists_tac`x`>>
    xsimpl)
  >- (xsimpl>>rw[]>>qexists_tac`fmlls`>>xsimpl)>>
  `LENGTH dml4 = LENGTH dml5` by (
    drule_at (Pos last) cand_pass_list_LENGTH>>
    simp[])>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,GC_STAR_GC]>>
    qexists_tac`fmlls`>>
    conj_tac
    >- metis_tac[]>>
    simp[GSYM STAR_ASSOC,GC_STAR_GC]>>
    xsimpl)>>
  `codes_in C (LENGTH cnt2)` by gvs[bnd_clause_codes_in]>>
  xlet`POSTv fmlv1.
    ARRAY_OF vcclause_TYPE fmlv1 (FST (insert_cnt_list fmlls cnt2 lim n C)) *
    ARRAY_OF NUM cntv (SND (insert_cnt_list fmlls cnt2 lim n C)) *
    ARRAY_OF INT sarrv (lit_sarr sarr2) * ARRAY_OF NUM tallyv tally3 *
    ARRAY_OF NUM carrv1 dml4`
  >- (
    xapp_spec insert_cnt_arr_spec>>
    xsimpl>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr2) * ARRAY_OF NUM tallyv tally3 *
      ARRAY_OF NUM carrv1 dml4`,`lim`,`n`,`fmlls`,`cnt2`,`C`]>>
    xsimpl)>>
  Cases_on`insert_cnt_list fmlls cnt2 lim n C`>>
  rename1`insert_cnt_list _ _ _ _ _ = (fmlls3,cnt3)`>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv1 fmlls3 * ARRAY_OF NUM cntv cnt3 *
    ARRAY_OF INT sarrv (lit_sarr (clear_subst w sarr2)) *
    ARRAY_OF NUM carrv1 dml4 * ARRAY_OF NUM tallyv (clear_tally w tally3)`
  >- (
    xapp_spec clear_arr_spec>>
    xsimpl>>
    `EVERY (λ(v,x). v < LENGTH dml2) w` by metis_tac[w_bnd_vars]>>
    `EVERY (λ(v,x). 0 < v ∧ v < LENGTH sarr2) w` by (
      qpat_x_assum`EVERY (λ(v,x). v < _) w` mp_tac>>
      qpat_x_assum`EVERY wf_entry w` mp_tac>>
      simp[EVERY_MEM,FORALL_PROD,wf_entry_def]>>
      rpt strip_tac>>
      res_tac>>
      simp[])>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv1 fmlls3 * ARRAY_OF NUM cntv cnt3`,`w`,`tally3`,
      `sarr2`,`dml4`]>>
    simp[]>>
    qexists_tac`piv_of w`>>
    simp[Abbr`sarr2`]>>
    xsimpl)>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[GC_STAR_GC]>>
  xsimpl>>
  metis_tac[]
QED


(*** Reading and checking a proof file, one record at a time ***)

val res = translate parse_vb_cl_def;

Theorem parse_vb_cl_side[local]:
  ∀s i len p acc.
  len ≤ strlen s ∧ i ≤ len ⇒ parse_vb_cl_side s i len p acc
Proof
  ho_match_mp_tac parse_vb_cl_ind>>
  rpt strip_tac>>
  once_rewrite_tac[fetch "-" "parse_vb_cl_side_def"]>>
  simp[parse_vb_int_side]>>
  rpt strip_tac>>
  first_x_assum irule>>
  simp[]>>
  qpat_x_assum`parse_vb_int _ _ _ = _` assume_tac>>
  drule parse_vb_int_le>>
  simp[]
QED

val _ = parse_vb_cl_side |> update_precondition;

Theorem parse_vb_cl_le[local]:
  ∀s i len p acc cl j.
  parse_vb_cl s i len p acc = (cl,j) ∧ i ≤ len ⇒ j ≤ len
Proof
  ho_match_mp_tac parse_vb_cl_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`parse_vb_cl _ _ _ _ _ = _` mp_tac>>
  simp[Once parse_vb_cl_def]>>
  pairarg_tac>>gvs[]>>
  drule_all parse_vb_int_le>>
  rw[]>>
  metis_tac[]
QED

val res = translate top_entry_def;
val res = translate lsr_pairs_def;
val res = translate split_witness_def;
val res = translate parse_lsr_chunk_def;

Theorem parse_lsr_chunk_side[local]:
  ∀s. parse_lsr_chunk_side s
Proof
  rw[fetch "-" "parse_lsr_chunk_side_def"]>>
  simp[parse_vb_num_side]>>
  imp_res_tac parse_vb_num_le>>
  imp_res_tac parse_vb_int_le>>
  imp_res_tac parse_vb_cl_le>>
  gvs[parse_vb_int_side,parse_vb_cl_side,parse_vb_ilits_side]
QED

val _ = parse_lsr_chunk_side |> update_precondition;

Quote add_cakeml:
  fun parse_lsr_one_arr lno fd =
  case TextIO.inputLineWith nulc fd of
    None => None
  | Some l =>
    (case parse_lsr_chunk l of
      None =>
        raise Fail (format_failure lno "failed to parse compressed LSR record")
    | Some (Inl step) => Some step
    | Some (Inr idcw) =>
      case idcw of (id,(c,w)) =>
        (case TextIO.inputLineWith nulc fd of
          None => raise Fail (format_failure lno "missing LSR hints")
        | Some h => Some (Lsrvb id c w h)))
End

Theorem parse_lsr_one_arr_spec:
  NUM lno lnov ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsr_one_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES nulc fd fdv lines fs)
    (POSTve
      (λv.
        SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          &(parse_lsr_one lines ≠ NONE ∧
            OPTION_TYPE LSR_LSR_TYPE
              (OPTION_MAP FST (THE (parse_lsr_one lines))) v ∧
            (case THE (parse_lsr_one lines) of
              NONE => lines' = []
            | SOME res => lines' = SND res)))
      (λe.
        SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧ parse_lsr_one lines = NONE)))
Proof
  rw[]>>
  xcf "parse_lsr_one_arr" (get_ml_prog_state ())>>
  xlet `POSTv v.
    SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv (TL lines) (forwardFD fs fd k) *
      &OPTION_TYPE STRING_TYPE (oHD lines) v`
  >- (
    xapp>>
    simp[nulc_v_thm])>>
  simp[parse_lsr_one_def]>>
  Cases_on`lines`>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    sep_triv)>>
  xlet_autop>>
  Cases_on`parse_lsr_chunk h`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    first_x_assum (irule_at Any)>>
    sep_triv)>>
  rename1`parse_lsr_chunk h = SOME res`>>
  Cases_on`res`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def]>>
    sep_triv)>>
  rename1`INSTREAM_LINES nulc fd fdv lines`>>
  rename1`parse_lsr_chunk h = SOME (INR idcw)`>>
  PairCases_on`idcw`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet `POSTv v.
    SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv (TL lines) (forwardFD fs fd k) *
      &OPTION_TYPE STRING_TYPE (oHD lines) v`
  >- (
    xapp>>
    irule_at Any nulc_v_thm>>xsimpl>>
    qexistsl_tac [`lines`,`forwardFD fs fd k`,`fd`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    sep_triv)>>
  Cases_on`lines`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    first_x_assum (irule_at Any)>>
    sep_triv)>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def,LSR_LSR_TYPE_def]>>
  qexists_tac`k`>>
  xsimpl
QED

Definition parse_and_run_file_list_def:
  parse_and_run_file_list lines fmlls dml b sarr cnt wm tally tp =
  case parse_lsr_one lines of
    NONE => NONE
  | SOME NONE => SOME fmlls
  | SOME (SOME (step,rest)) =>
    (case check_lsr_list step fmlls dml b sarr cnt wm tally tp of
      NONE => NONE
    | SOME (fmlls',dml',b',sarr',cnt',wm',tally',tp') =>
      parse_and_run_file_list rest fmlls' dml' b' sarr' cnt' wm' tally' tp')
Termination
  WF_REL_TAC`measure (LENGTH o FST)`>>
  rw[]>>
  drule parse_lsr_one_LENGTH>>
  simp[]
End

Theorem parse_and_run_file_list_eq:
  ∀lines fmlls dml b sarr cnt wm tally tp.
  parse_and_run_file_list lines fmlls dml b sarr cnt wm tally tp =
  case parse_lsrs lines of
    NONE => NONE
  | SOME lsrs => check_lsrs_list lsrs fmlls dml b sarr cnt wm tally tp
Proof
  ho_match_mp_tac parse_and_run_file_list_ind>>
  rw[]>>
  simp[Once parse_and_run_file_list_def,Once parse_lsrs_def]>>
  every_case_tac>>
  gvs[check_lsrs_list_def]
QED

Quote add_cakeml:
  fun check_unsat'' fd lno fml carr b tp aux =
  case parse_lsr_one_arr lno fd of
    None => fml
  | Some step =>
    (case check_lsr_arr lno step fml carr b tp aux of
      (fml',carr',b',tp',aux') =>
      check_unsat'' fd (lno+1) fml' carr' b' tp' aux')
End

Theorem check_unsat''_spec:
  ∀lines fmlls dml b sarr cnt wm tally tp fs fmlv carrv auxv
   lno lnov bv tpv.
  NUM lno lnov ∧ NUM b bv ∧
  NUM tp tpv ∧ lsr_inv fmlls dml b sarr cnt wm tally tp ∧
  (∃fml. fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml)) ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; fmlv; carrv; bv; tpv; auxv]
    (STDIO fs * ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
     AUX sarr cnt wm tally auxv * INSTREAM_LINES nulc fd fdv lines fs)
    (POSTve
      (λv.
        SEP_EXISTS k fmlls'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv [] (forwardFD fs fd k) *
          ARRAY_OF vcclause_TYPE v fmlls' *
          &(parse_and_run_file_list lines fmlls dml b sarr cnt wm tally tp =
            SOME fmlls') * GC)
      (λe.
        SEP_EXISTS k fmlv' fmlls' lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          ARRAY_OF vcclause_TYPE fmlv' fmlls' *
          &(Fail_exn e ∧
            parse_and_run_file_list lines fmlls dml b sarr cnt wm tally tp =
              NONE) * GC))
Proof
  ho_match_mp_tac parse_and_run_file_list_ind>>
  rpt strip_tac>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_file_list_def]>>
  xlet `POSTve
    (λv.
      SEP_EXISTS k lines'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
        ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
        AUX sarr cnt wm tally auxv *
        &(parse_lsr_one lines ≠ NONE ∧
          OPTION_TYPE LSR_LSR_TYPE
            (OPTION_MAP FST (THE (parse_lsr_one lines))) v ∧
          (case THE (parse_lsr_one lines) of
            NONE => lines' = []
          | SOME res => lines' = SND res)))
    (λe.
      SEP_EXISTS k lines'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
        ARRAY_OF vcclause_TYPE fmlv fmlls *
        &(Fail_exn e ∧ parse_lsr_one lines = NONE))`
  >- (
    xapp_spec parse_lsr_one_arr_spec>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
      AUX sarr cnt wm tally auxv`,`lines`,`fs`,`fd`]>>
    xsimpl>>
    qexists_tac`lno`>>
    conj_tac
    >- simp[]>>
    conj_tac>>
    rpt strip_tac>>
    rename1`INSTREAM_LINES nulc fd fdv ls (forwardFD fs fd k)`>>
    qexistsl_tac [`k`,`ls`]>>
    simp[]>>
    xsimpl)
  >- (
    xsimpl>>
    rpt strip_tac>>
    rename1`INSTREAM_LINES nulc fd fdv ls (forwardFD fs fd k)`>>
    qexistsl_tac [`k`,`fmlv`,`fmlls`,`ls`]>>
    simp[Once parse_and_run_file_list_def]>>
    xsimpl)>>
  Cases_on`parse_lsr_one lines`>>gvs[]>>
  rename1`parse_lsr_one lines = SOME res`>>
  Cases_on`res`>>gvs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xvar>>xsimpl>>
    qexists_tac`k`>>xsimpl>>
    simp[GC_STAR_GC]>>
    xsimpl)>>
  rename1`parse_lsr_one lines = SOME (SOME stp)`>>
  PairCases_on`stp`>>
  rename1`parse_lsr_one lines = SOME (SOME (step,rest))`>>
  gvs[]>>
  `lsr_vb_ok step` by metis_tac[parse_lsr_one_vb_ok]>>
  `wf_lsr step` by metis_tac[parse_lsr_one_wf_lsr]>>
  xmatch>>
  xlet`POSTve
    (λv. STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv rest (forwardFD fs fd k) *
      SEP_EXISTS fmlv' carrv' bv' tpv' auxv'.
        &(v = Conv NONE [fmlv'; carrv'; bv'; tpv'; auxv']) *
        SEP_EXISTS res.
          &(check_lsr_list step fmlls dml b sarr cnt wm tally tp = SOME res) *
          (case res of (fmlls',dml',b',sarr',cnt',wm',tally',tp') =>
            ARRAY_OF vcclause_TYPE fmlv' fmlls' *
            ARRAY_OF NUM carrv' dml' * AUX sarr' cnt' wm' tally' auxv' *
            &(NUM b' bv' ∧ NUM tp' tpv')))
    (λe. STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv rest (forwardFD fs fd k) *
      SEP_EXISTS fmlls1. ARRAY_OF vcclause_TYPE fmlv fmlls1 *
        &(Fail_exn e ∧
          check_lsr_list step fmlls dml b sarr cnt wm tally tp = NONE))`
  >- (
    xapp_spec check_lsr_arr_spec>>
    xsimpl>>
    qexists_tac`STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv rest (forwardFD fs fd k)`>>
    qexistsl_tac [`wm`,`tp`,`tally`,`sarr`,`step`,`fmlls`,`dml`,`cnt`,`b`,
      `lno`]>>
    xsimpl>>
    rw[]>>
    metis_tac[SEP_IMP_REFL])
  >- (
    xsimpl>>
    rpt strip_tac>>
    rename1`ARRAY_OF vcclause_TYPE fmlv fmlls1`>>
    qexistsl_tac [`k`,`fmlv`,`fmlls1`,`rest`]>>
    simp[Once parse_and_run_file_list_def]>>
    xsimpl)>>
  PairCases_on`res`>>
  gvs[]>>
  xpull>>
  drule_all check_lsr_list>>
  strip_tac>>
  drule_all check_lsr_nz_vcfml>>
  strip_tac>>
  xmatch>>
  xlet_autop>>
  xapp>>
  qexistsl_tac [`emp`,`forwardFD fs fd k`]>>
  xsimpl>>
  qexistsl_tac [`fml'`,`lno + 1`]>>
  simp[]>>
  conj_tac>>
  rpt strip_tac
  >- (
    rename1`forwardFD (forwardFD fs fd k) fd k2`>>
    qexists_tac`k + k2`>>
    simp[forwardFD_o,Once parse_and_run_file_list_def]>>
    simp[GSYM STAR_ASSOC,GC_STAR_GC]>>
    xsimpl)>>
  rename1`INSTREAM_LINES nulc fd fdv ls (forwardFD (forwardFD fs fd k) fd k2)`>>
  rename1`ARRAY_OF vcclause_TYPE fv fl`>>
  qexistsl_tac [`k + k2`,`fv`,`fl`,`ls`]>>
  simp[forwardFD_o,Once parse_and_run_file_list_def]>>
  simp[GSYM STAR_ASSOC,GC_STAR_GC]>>
  xsimpl
QED

(* Checks the proof read from the open input stream (a file or stdin)
  against the formula vcfml *)
Quote add_cakeml:
  fun run_lsr_is vcfml is n nc =
  let
    val fml = build_cfml_arr nc 1 vcfml
    val carr = Array.array n 0
    val sarr = Array.array (2 * n) 0
    val cnt = Array.array (2 * n) 0
    val tally = Array.array (2 * n) 0
    val aux = (sarr, cnt, 0, tally)
    val tp = List.length vcfml + 1
    val chk = Inr (check_unsat'' is 1 fml carr 1 tp aux)
      handle Fail s => Inl s
  in
    case chk of
      Inl s => Inl s
    | Inr fml' => Inr (contains_emp_arr fml')
  end
End

Quote add_cakeml:
  fun check_unsat' vcfml fname n nc =
  let
    val fd = TextIO.openInSetBufferSize fname proof_buffer_size
    val chk = run_lsr_is vcfml fd n nc
    val close = TextIO.closeIn fd;
  in
    chk
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Quote add_cakeml:
  fun check_unsat_stdin' vcfml n nc =
  let
    val is = TextIO.openStdInSetBufferSize proof_buffer_size
  in
    run_lsr_is vcfml is n nc
  end
End

(* The input may hold vcc_none entries, loaded as deleted clauses; an
  accepted proof refutes the other entries *)
Theorem run_lsr_is_spec:
  NUM n nv ∧ NUM nc ncv ∧
  LIST_TYPE vcclause_TYPE vcfml vcfmlv ∧
  EVERY (λc. bnd_clause c n) vcfml ∧
  EVERY (λc. c ≠ vcc_none ⇒ ¬MEM 0 (toList c)) vcfml ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"run_lsr_is"(get_ml_prog_state()))
    [vcfmlv; isv; nv; ncv]
    (STDIO fs * INSTREAM_LINES nulc fd isv lines fs)
    (POSTv v.
      SEP_EXISTS k rest res.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES nulc fd isv rest (forwardFD fs fd k) *
        &(SUM_TYPE STRING_TYPE BOOL res v ∧
          (res = INR T ⇒
            ¬∃w. satisfies_vcfml w (set vcfml DIFF {vcc_none}))))
Proof
  rw[]>>
  xcf"run_lsr_is"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` ARRAY_OF_alloc_spec))
  >- xsimpl>>
  rename1`ARRAY_OF NUM carrv (REPLICATE n 0)`>>
  xlet_autop>>
  xlet`POSTv sarrv. ARRAY_OF INT sarrv (lit_sarr (REPLICATE n 0)) *
    ARRAY_OF NUM carrv (REPLICATE n 0) * ARRAY_OF vcclause_TYPE resv (build_cfml_list 1 vcfml nc) *
    INSTREAM_LINES nulc fd isv lines fs *
    STDIO fs`
  >- (
    xapp_spec (Q.ISPEC`INT` ARRAY_OF_alloc_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv (REPLICATE n 0) * ARRAY_OF vcclause_TYPE resv (build_cfml_list 1 vcfml nc) *
      INSTREAM_LINES nulc fd isv lines fs *
      STDIO fs`,`0`,`2 * n`]>>
    xsimpl>>
    simp[INT_def,lit_sarr_REPLICATE]>>
    xsimpl)>>
  xlet_autop>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` ARRAY_OF_alloc_spec))
  >- xsimpl>>
  xlet_autop>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` ARRAY_OF_alloc_spec))
  >- xsimpl>>
  rename1`ARRAY_OF NUM tallyv (REPLICATE _ 0) * ARRAY_OF NUM cntv (REPLICATE _ 0)`>>
  xlet`POSTv auxv. AUX (REPLICATE n 0) (REPLICATE (2 * n) 0) 0
      (REPLICATE (2 * n) 0) auxv *
    ARRAY_OF NUM carrv (REPLICATE n 0) * ARRAY_OF vcclause_TYPE resv (build_cfml_list 1 vcfml nc) *
    INSTREAM_LINES nulc fd isv lines fs *
    STDIO fs`
  >- (
    xcon>>
    simp[AUX_def]>>
    xsimpl>>
    simp[NUM_def,INT_def])>>
  xlet_autop>>
  xlet_autop>>
  qabbrev_tac`fmlls = build_cfml_list 1 vcfml nc`>>
  qabbrev_tac`tp0 = LENGTH vcfml + 1`>>
  `lsr_inv fmlls (REPLICATE n 0) 1 (REPLICATE n 0) (REPLICATE (2 * n) 0) 0
     (REPLICATE (2 * n) 0) tp0` by (
    irule lsr_inv_init>>
    `tp0 = 1 + LENGTH vcfml` by simp[Abbr`tp0`]>>
    qunabbrev_tac`fmlls`>>
    conj_tac
    >- (
      irule bnd_fml_build_cfml_list>>
      first_assum ACCEPT_TAC)>>
    qpat_x_assum`tp0 = _` SUBST1_TAC>>
    simp_tac bool_ss [top_ok_build_cfml_list])>>
  `∃fml. fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml)` by (
    drule build_cfml_list_none>>
    disch_then (qspecl_then [`1`,`nc`] strip_assume_tac)>>
    metis_tac[])>>
  xlet`POSTv resv.
    SEP_EXISTS v0 fmlls' fmlv' k rest.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd isv rest (forwardFD fs fd k) *
      ARRAY_OF vcclause_TYPE fmlv' fmlls' *
      &(case parse_and_run_file_list lines fmlls (REPLICATE n 0) 1
               (REPLICATE n 0) (REPLICATE (2 * n) 0) 0 (REPLICATE (2 * n) 0) tp0 of
          NONE =>
            resv = Conv (SOME (TypeStamp «Inl» 4)) [v0] ∧ ∃s. STRING_TYPE s v0
        | SOME res =>
            res = fmlls' ∧
            resv = Conv (SOME (TypeStamp «Inr» 4)) [fmlv'])`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS fmlv' fmlls' rest k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd isv rest (forwardFD fs fd k) *
          ARRAY_OF vcclause_TYPE fmlv' fmlls' *
          &(Fail_exn e ∧
            parse_and_run_file_list lines fmlls (REPLICATE n 0) 1
              (REPLICATE n 0) (REPLICATE (2 * n) 0) 0 (REPLICATE (2 * n) 0) tp0 =
              NONE)`
      >- (
        xlet`POSTe e.
          SEP_EXISTS k fmlv' fmlls' lines'.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES nulc fd isv lines'
              (forwardFD fs fd k) *
            ARRAY_OF vcclause_TYPE fmlv' fmlls' *
            &(Fail_exn e ∧
              parse_and_run_file_list lines fmlls (REPLICATE n 0) 1
                (REPLICATE n 0) (REPLICATE (2 * n) 0) 0 (REPLICATE (2 * n) 0) tp0 =
                NONE)`
        >- (
          xapp_spec check_unsat''_spec>>
          qexistsl_tac [`emp`,`0`,`tp0`,`REPLICATE (2 * n) 0`,`REPLICATE n 0`,
            `lines`,`fs`,`fmlls`,`fd`,`REPLICATE n 0`,
            `REPLICATE (2 * n) 0`,`1`]>>
          xsimpl>>
          qexists_tac`fml`>>
          simp[]>>
          rpt strip_tac>>
          metis_tac[SEP_IMP_REFL])
        >- (
          xsimpl>>
          rpt strip_tac>>
          rename1`ARRAY_OF vcclause_TYPE av1 al1`>>
          rename1`INSTREAM_LINES nulc fd isv ls
            (forwardFD fs fd k)`>>
          qexistsl_tac [`av1`,`al1`,`ls`,`k`]>>
          xsimpl))>>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      qexistsl_tac [`sv`,`fmlls'`,`fmlv'`,`k`,`rest`]>>
      xsimpl>>
      metis_tac[])
    >- (
      xhandle`POSTv v.
        SEP_EXISTS k rest fmlls'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd isv rest (forwardFD fs fd k) *
          (SEP_EXISTS fmlv'.
            &(v = Conv (SOME (TypeStamp «Inr» 4)) [fmlv']) *
            ARRAY_OF vcclause_TYPE fmlv' fmlls') *
          &(parse_and_run_file_list lines fmlls (REPLICATE n 0) 1
              (REPLICATE n 0) (REPLICATE (2 * n) 0) 0 (REPLICATE (2 * n) 0) tp0 =
            SOME fmlls')`
      >- (
        xlet`POSTv v.
          SEP_EXISTS k fmlls'.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES nulc fd isv [] (forwardFD fs fd k) *
            ARRAY_OF vcclause_TYPE v fmlls' *
            &(parse_and_run_file_list lines fmlls (REPLICATE n 0) 1
                (REPLICATE n 0) (REPLICATE (2 * n) 0) 0 (REPLICATE (2 * n) 0) tp0 =
              SOME fmlls')`
        >- (
          xapp_spec check_unsat''_spec>>
          qexistsl_tac [`emp`,`0`,`tp0`,`REPLICATE (2 * n) 0`,`REPLICATE n 0`,
            `lines`,`fs`,`fmlls`,`fd`,`REPLICATE n 0`,
            `REPLICATE (2 * n) 0`,`1`]>>
          xsimpl>>
          qexists_tac`fml`>>
          simp[]>>
          rpt strip_tac>>
          metis_tac[SEP_IMP_REFL])>>
        xcon>>xsimpl>>
        qexistsl_tac [`k`,`[]`]>>
        gvs[]>>
        xsimpl)>>
      xsimpl>>
      rpt strip_tac>>
      rename1`INSTREAM_LINES nulc fd isv ls1
        (forwardFD fs fd k1)`>>
      qexistsl_tac [`k1`,`ls1`]>>
      gvs[]>>
      xsimpl))>>
  qspecl_then [`lines`,`fmlls`,`REPLICATE n 0`,`1`,`REPLICATE n 0`,
    `REPLICATE (2 * n) 0`,`0`,`REPLICATE (2 * n) 0`,`tp0`]
    strip_assume_tac parse_and_run_file_list_eq>>
  gs[]>>
  pop_assum kall_tac>>
  Cases_on`parse_lsrs lines`>>fs[]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    qexistsl_tac [`k`,`rest`,`INL s`]>>
    simp[SUM_TYPE_def]>>
    xsimpl)>>
  rename1`parse_lsrs lines = SOME lsrs`>>
  Cases_on`check_lsrs_list lsrs fmlls (REPLICATE n 0) 1 (REPLICATE n 0)
    (REPLICATE (2 * n) 0) 0 (REPLICATE (2 * n) 0) tp0`>>fs[]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    qexistsl_tac [`k`,`rest`,`INL s`]>>
    simp[SUM_TYPE_def]>>
    xsimpl)>>
  gvs[]>>
  rename1`check_lsrs_list lsrs _ _ _ _ _ _ _ _ = SOME fmlls'`>>
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl>>
  qexistsl_tac [`k`,`rest`,`INR (contains_emp_list fmlls')`]>>
  reverse conj_tac
  >- xsimpl>>
  simp[SUM_TYPE_def]>>
  strip_tac>>
  `¬∃w. satisfies_vcfml w (set vcfml DIFF {vcc_none})` suffices_by
    metis_tac[]>>
  irule check_lsrs_unsat_list_sound_none>>
  conj_tac
  >- first_assum ACCEPT_TAC>>
  qexistsl_tac [`1`,`lsrs`,`n`,`nc`]>>
  `build_cfml_list 1 vcfml nc = fmlls` by simp[Abbr`fmlls`]>>
  simp[check_lsrs_unsat_list_def]>>
  metis_tac[parse_lsrs_wf_lsr]
QED

Theorem check_unsat'_spec:
  NUM n nv ∧ NUM nc ncv ∧
  LIST_TYPE vcclause_TYPE vcfml vcfmlv ∧
  FILENAME f fv ∧ hasFreeFD fs ∧
  EVERY (λc. bnd_clause c n) vcfml ∧
  EVERY (λc. c ≠ vcc_none ⇒ ¬MEM 0 (toList c)) vcfml ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
    [vcfmlv; fv; nv; ncv]
    (STDIO fs)
    (POSTv v.
      STDIO fs *
      SEP_EXISTS res.
        &(SUM_TYPE STRING_TYPE BOOL res v ∧
          (res = INR T ⇒
            ¬∃w. satisfies_vcfml w (set vcfml DIFF {vcc_none}))))
Proof
  rw[]>>
  xcf"check_unsat'"(get_ml_prog_state ())>>
  assume_tac proof_buffer_size_v_thm>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[])>>
  reverse (Cases_on `inFS_fname fs f`)>>simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >- (xlet_auto_spec (SOME openInSetBufferSize_STDIO_spec)>>xsimpl)>>
    fs[BadFileName_exn_def]>>
    xcases>>rw[]>>
    xlet_auto>>xsimpl>>
    xcon>>xsimpl>>
    qexists_tac`INL (notfound_string f)`>>
    simp[SUM_TYPE_def])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec
    (SOME (openInSetBufferSize_spec_lines |> Q.GEN `c0` |> Q.SPEC `nulc`))>>xsimpl>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  xlet`POSTv chk.
    SEP_EXISTS k rest res.
      STDIO (forwardFD fss (nextFD fs) k) *
      INSTREAM_LINES nulc (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
      &(SUM_TYPE STRING_TYPE BOOL res chk ∧
        (res = INR T ⇒
          ¬∃w. satisfies_vcfml w (set vcfml DIFF {vcc_none})))`
  >- (
    xapp_spec run_lsr_is_spec>>
    qexistsl_tac [`emp`,`vcfml`,`all_lines_file_gen nulc fs f`,`fss`,
      `nextFD fs`]>>
    xsimpl>>
    metis_tac[])>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec closeIn_spec_lines>>
    qexistsl_tac [`emp`,`rest`,`forwardFD fss (nextFD fs) k`,`nextFD fs`,
      `nulc`]>>
    conj_tac
    >- (
      fs [forwardFD_def,Abbr`fss`]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs [])>>
    `validFileFD (nextFD fs) (forwardFD fss (nextFD fs) k).infds` by (
      simp[validFileFD_forwardFD]>>simp[Abbr`fss`]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      match_mp_tac validFileFD_nextFD>>fs [])>>
    xsimpl>>rw []>>
    imp_res_tac (DECIDE ``a<b:num ==> a <= b``)>>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs []>>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD>>
    fs [Abbr`fss`]>>xsimpl)>>
  xvar>>
  xsimpl>>
  first_assum (irule_at Any)>>
  simp[]
QED

Theorem check_unsat_stdin'_spec:
  NUM n nv ∧ NUM nc ncv ∧
  LIST_TYPE vcclause_TYPE vcfml vcfmlv ∧
  stdin_content fs = SOME text ∧
  EVERY (λc. bnd_clause c n) vcfml ∧
  EVERY (λc. c ≠ vcc_none ⇒ ¬MEM 0 (toList c)) vcfml ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_stdin'"(get_ml_prog_state()))
    [vcfmlv; nv; ncv]
    (STDIO fs)
    (POSTv v.
      SEP_EXISTS k res.
        STDIO (forwardFD fs 0 k) *
        &(SUM_TYPE STRING_TYPE BOOL res v ∧
          (res = INR T ⇒
            ¬∃w. satisfies_vcfml w (set vcfml DIFF {vcc_none}))))
Proof
  rpt strip_tac>>
  xcf"check_unsat_stdin'"(get_ml_prog_state())>>
  assume_tac proof_buffer_size_v_thm>>
  xlet_auto_spec
    (SOME (openStdInSetBufferSize_spec_lines |> Q.GEN `c0` |> Q.SPEC `nulc`))>>
  xsimpl>>
  xapp_spec run_lsr_is_spec>>
  qexistsl_tac [`emp`,`vcfml`,`lines_of_gen nulc (implode text)`,`fs`,`0`]>>
  xsimpl>>
  qexistsl_tac [`n`,`nc`]>>
  rw[]>>
  qmatch_goalsub_rename_tac`STDIO (forwardFD fs 0 kk) * _ ==>> _`>>
  qmatch_asmsub_rename_tac`SUM_TYPE STRING_TYPE BOOL res v`>>
  qexistsl_tac [`kk`,`res`]>>
  simp[]>>
  xsimpl
QED
