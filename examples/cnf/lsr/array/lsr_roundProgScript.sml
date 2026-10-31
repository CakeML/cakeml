(*
  This refines lsr_list to use arrays: the RUP-level additions and the
  round for one clause of the formula
*)
Theory lsr_roundProg
Ancestors
  misc mllist UnsafeProof ccnf_arith ccnf_arrayProg ccnf_parseProg cnf ccnf
  ccnf_list syntax_helper sr lsr lsr_list array_ofProof mlint mlvector
Libs
  preamble basis lsr_arrayLib

val _ = hide_environments true;

val _ = translation_extends "ccnf_parseProg";

(***
  RUP-level additions
 ***)

val res = translate skip_hints_vb_def;

Theorem skip_hints_vb_side:
  ∀s i len. len ≤ strlen s ∧ i ≤ len ⇒ skip_hints_vb_side s i len
Proof
  ho_match_mp_tac skip_hints_vb_ind>>
  rw[]>>
  simp[Once (fetch "-" "skip_hints_vb_side_def"),parse_vb_int_side]>>
  rw[]>>
  first_x_assum irule>>
  metis_tac[parse_vb_int_le]
QED

val _ = skip_hints_vb_side |> update_precondition;

val res = translate sz_witness_def;

Quote add_cakeml:
  fun rup_dm_vb_arr lno fml carr b v s =
    (init_lit_map_arr (Vector.length v) v carr b;
     unit_prop_vb_arr lno fml carr b s 0 (String.size s))
End

Theorem rup_dm_vb_arr_spec:
  NUM lno lnov ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  vcclause_TYPE v vv ∧
  STRING_TYPE s sv ∧
  bnd_clause v (LENGTH Clist) ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rup_dm_vb_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; sv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM Carrv Clist)
    (POSTve
      (λres.
        ARRAY_OF vcclause_TYPE fmlv fmlls *
        SEP_EXISTS r Clist'.
        ARRAY_OF NUM Carrv Clist' *
        &(rup_dm_vb_list fmlls Clist b v s = SOME (r,Clist') ∧
          OPTION_TYPE NUM r res))
      (λe.
        ARRAY_OF vcclause_TYPE fmlv fmlls *
        SEP_EXISTS Clist'.
        ARRAY_OF NUM Carrv Clist' *
        &(Fail_exn e ∧ rup_dm_vb_list fmlls Clist b v s = NONE)))
Proof
  rw[rup_dm_vb_list_def]>>
  xcf "rup_dm_vb_arr" (get_ml_prog_state ())>>
  `b ≤ 2 ** 29 + 1` by fs[stamps_ok_def]>>
  `IS_SOME (init_lit_map_list' (length v) v Clist b)`
    by simp[init_lit_map_list'_SOME]>>
  gvs[IS_SOME_EXISTS]>>
  rename1`init_lit_map_list' _ _ _ _ = SOME Clist1`>>
  drule init_lit_map_list'>>
  strip_tac>>
  xlet_autop>>
  xlet_autop>>
  `LENGTH Clist1 = LENGTH Clist` by
    metis_tac[LENGTH_init_lit_map_list_bnd,LESS_EQ_REFL]>>
  `stamps_ok Clist1 b` by metis_tac[stamps_ok_init_lit_map_list]>>
  `IS_SOME (unit_prop_vb_list' fmlls Clist1 b s 0 (strlen s))`
    by simp[unit_prop_vb_list'_SOME]>>
  gvs[IS_SOME_EXISTS]>>
  drule unit_prop_vb_list'>>
  strip_tac>>
  xlet_autop>>
  xapp>>xsimpl>>
  qpat_x_assum`unit_prop_vb_list' _ _ _ _ _ _ = _` (irule_at Any)>>
  qpat_x_assum`NUM lno _` (irule_at Any)>>
  simp[]>>
  qexists_tac`emp`>>xsimpl>>
  metis_tac[ARRAY_OF_refl]
QED

Quote add_cakeml:
  fun unit_prop_vb_undo_arr lno fml carr b s i1 len =
    case parse_vb_int s i1 len of (m,i) =>
    if m <= 0 then 0
    else
      let val r = unit_prop_one lno fml carr b m in
        if int_eq_0 r then i
        else if Unsafe.Arith.ltWitness 0 r carr then
          let val j = unit_prop_vb_undo_arr lno fml carr b s i len in
            (Unsafe.update carr r 0; j)
          end
        else unit_prop_vb_undo_arr lno fml carr b s i len
      end
End

Theorem unit_prop_vb_undo_arr_spec:
  ∀fmlls Clist b s i l Carrv bv sv iv lv.
  NUM lno lnov ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  bnd_fml fmlls (LENGTH Clist) ∧
  STRING_TYPE s sv ∧
  NUM i iv ∧
  NUM l lv ∧
  l ≤ strlen s ∧ i ≤ l
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_vb_undo_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; sv; iv; lv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM Carrv Clist)
    (POSTve
      (λv.
        ARRAY_OF vcclause_TYPE fmlv fmlls *
        SEP_EXISTS j Clist'.
        ARRAY_OF NUM Carrv Clist' *
        &(unit_prop_vb_undo_list fmlls Clist b s i l = SOME (j,Clist') ∧
          NUM j v))
      (λe.
        ARRAY_OF vcclause_TYPE fmlv fmlls *
        SEP_EXISTS Clist'.
        ARRAY_OF NUM Carrv Clist' *
        &(Fail_exn e ∧ unit_prop_vb_undo_list fmlls Clist b s i l = NONE)))
Proof
  ho_match_mp_tac unit_prop_vb_undo_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  xcf "unit_prop_vb_undo_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (xsimpl>>fs[parse_vb_int_side])>>
  Cases_on`parse_vb_int s i l`>>
  rename1`parse_vb_int s i l = (m,i')`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  simp[Once unit_prop_vb_undo_list_def]>>
  xif
  >- (xlit>>xsimpl>>metis_tac[ARRAY_OF_refl])>>
  `IS_SOME (unit_prop_one' fmlls Clist b (Num m))`
    by simp[unit_prop_one'_SOME]>>
  gvs[IS_SOME_EXISTS]>>
  rename1`unit_prop_one' _ _ _ _ = SOME ures`>>
  drule unit_prop_one'>>
  strip_tac>>
  rename1`INT m mv`>>
  `NUM (Num m) mv` by (
    gvs[NUM_def]>>
    `&Num m = m` by intLib.ARITH_TAC>>
    simp[])>>
  xlet`POSTve
    (λv. ARRAY_OF vcclause_TYPE fmlv fmlls *
      SEP_EXISTS r Clist'. ARRAY_OF NUM Carrv Clist' *
      &(ures = SOME (r,Clist') ∧ INT r v))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls *
      SEP_EXISTS Clist'. ARRAY_OF NUM Carrv Clist' *
      &(Fail_exn e ∧ ures = NONE))`
  >- (
    xapp_spec unit_prop_one_spec>>
    xsimpl>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once unit_prop_vb_undo_list_def]>>
    metis_tac[ARRAY_OF_refl])>>
  gvs[]>>
  rename1`unit_prop_one _ _ _ _ = SOME (r,Clist1)`>>
  xlet_autop>>
  xif
  >- (
    gvs[int_eq_0_def]>>
    xvar>>xsimpl)>>
  gvs[int_eq_0_def]>>
  `LENGTH Clist1 = LENGTH Clist` by metis_tac[unit_prop_one_LENGTH]>>
  `Num (ABS r) < LENGTH Clist1` by metis_tac[unit_prop_one_bound]>>
  `stamps_ok Clist1 b` by metis_tac[stamps_ok_unit_prop_one]>>
  `i' ≤ l` by metis_tac[parse_vb_int_le]>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_lt_arr_spec))
  >- xsimpl>>
  xif
  >- (
    xlet`POSTve
      (λv. ARRAY_OF vcclause_TYPE fmlv fmlls *
        SEP_EXISTS j Clist2. ARRAY_OF NUM Carrv Clist2 *
        &(unit_prop_vb_undo_list fmlls Clist1 b s i' l = SOME (j,Clist2) ∧
          NUM j v))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls *
        SEP_EXISTS Clist2. ARRAY_OF NUM Carrv Clist2 *
        &(Fail_exn e ∧ unit_prop_vb_undo_list fmlls Clist1 b s i' l = NONE))`
    >- (xapp>>xsimpl)
    >- (
      xsimpl>>
      rw[]>>
      simp[Once unit_prop_vb_undo_list_def]>>
      metis_tac[ARRAY_OF_refl])>>
    (* clear the variable this hint wrote *)
    `LENGTH Clist2 = LENGTH Clist1` by
      metis_tac[unit_prop_vb_undo_list_LENGTH]>>
    `Num r < LENGTH Clist2 ∧ &Num r = r` by intLib.ARITH_TAC>>
    xlet`POSTv uv. ARRAY_OF NUM Carrv (LUPDATE 0 (Num r) Clist2) *
      ARRAY_OF vcclause_TYPE fmlv fmlls`
    >- (
      xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
      qrefinel [`_`,`Clist2`,`0`,`Num r`]>>
      xsimpl>>
      gvs[NUM_def,INT_def])>>
    xvar>>xsimpl)>>
  gvs[]>>
  xapp>>xsimpl>>
  rw[]>>
  simp[Once unit_prop_vb_undo_list_def]>>
  metis_tac[ARRAY_OF_refl]
QED

(***
  Literal codes and image codes. The array copy of sarr is indexed by literal
  code: the image code of v is at 2v and that of ¬v at 2v + 1, so the image
  code of a literal is a single load.
 ***)

Definition lit_sarr_def:
  lit_sarr (sarr:int list) =
  GENLIST (λi. if EVEN i then EL (i DIV 2) sarr else -EL (i DIV 2) sarr)
    (2 * LENGTH sarr)
End

Theorem LENGTH_lit_sarr[simp]:
  LENGTH (lit_sarr sarr) = 2 * LENGTH sarr
Proof
  simp[lit_sarr_def]
QED

Theorem EL_lit_sarr:
  v < LENGTH sarr ⇒
  EL (2 * v) (lit_sarr sarr) = EL v sarr ∧
  EL (2 * v + 1) (lit_sarr sarr) = -EL v sarr
Proof
  rw[lit_sarr_def,EL_GENLIST,EVEN_ADD,EVEN_DOUBLE]
QED

Theorem lit_sarr_LUPDATE:
  lit_sarr (LUPDATE e v sarr) =
  LUPDATE (-e) (2 * v + 1) (LUPDATE e (2 * v) (lit_sarr sarr))
Proof
  irule LIST_EQ>>
  simp[lit_sarr_def,EL_GENLIST,EL_LUPDATE]>>
  rpt strip_tac>>
  Cases_on`x DIV 2 = v`
  >- (
    `x = 2 * v ∨ x = 2 * v + 1` by intLib.COOPER_TAC>>
    gvs[EVEN_ADD,EVEN_DOUBLE])>>
  `x ≠ 2 * v ∧ x ≠ 2 * v + 1` by intLib.COOPER_TAC>>
  simp[]
QED

Theorem lit_sarr_REPLICATE:
  lit_sarr (REPLICATE n 0) = REPLICATE (2 * n) 0
Proof
  irule LIST_EQ>>
  simp[lit_sarr_def,EL_GENLIST]>>
  rpt strip_tac>>
  `x DIV 2 < n` by intLib.COOPER_TAC>>
  simp[EL_REPLICATE]
QED

(* The image code of a literal read at its code *)
Theorem EL_lit_sarr_img_code:
  Num (ABS l) < LENGTH sarr ⇒
  EL (lit_code l) (lit_sarr sarr) = img_code F p sarr l
Proof
  rw[img_code_def,lit_code_def,any_el_ALT,EL_lit_sarr]
QED

(* The code of l in integer arithmetic, and the magnitudes computed on the
  way to it *)
Theorem lit_code_INT:
  &(lit_code l) = (if l < 0 then 1 - (l + l) else l + l) ∧
  Num (ABS (l + l)) = 2 * Num (ABS l) ∧
  (l < 0 ⇒ Num (ABS (1 - (l + l))) = 2 * Num (ABS l) + 1)
Proof
  rw[lit_code_def]>>
  intLib.ARITH_TAC
QED

(* The code of l; w is any array at least as long as 2 |l| + 1 / 256 *)
Quote add_cakeml:
  fun lit_code_arr w l =
  if Unsafe.Arith.ltWitness l 0 w
  then Unsafe.Arith.subWitness 1 (Unsafe.Arith.addWitness l l w) w
  else Unsafe.Arith.addWitness l l w
End

Theorem lit_code_arr_spec:
  INT l lv ∧ 2 * Num (ABS l) + 1 ≤ 256 * LENGTH ls ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lit_code_arr" (get_ml_prog_state()))
    [wv; lv] (ARRAY_OF NUM wv ls)
    (POSTv v. &NUM (lit_code l) v * ARRAY_OF NUM wv ls)
Proof
  rw[]>>
  xcf "lit_code_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_lt_arr_spec))
  >- (xsimpl>>intLib.ARITH_TAC)>>
  `Num (ABS (l + l)) ≤ 256 * LENGTH ls` by simp[lit_code_INT]>>
  xif
  >- (
    `Num (ABS (1 - (l + l))) ≤ 256 * LENGTH ls` by simp[lit_code_INT]>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_add_arr_spec))
    >- xsimpl>>
    xapp_prepare_goal>>
    irule cfAppTheory.app_weaken>>
    irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
    qexistsl_tac [`l + l`,`1`]>>
    simp[INT_def]>>
    xsimpl>>
    simp[NUM_def,lit_code_INT])>>
  xapp_prepare_goal>>
  irule cfAppTheory.app_weaken>>
  irule_at Any (Q.ISPEC`NUM` int_add_arr_spec)>>
  qexistsl_tac [`l`,`l`]>>
  simp[]>>
  xsimpl>>
  simp[NUM_def,lit_code_INT]
QED

(* On a RAT line (piv ≠ 0) σ maps the pivot to ⊤ and nothing else; otherwise
  the image code is read from the array. ⊤ is the length of the assignment
  map, which is the length of sarr. *)
Quote add_cakeml:
  fun img_code_arr piv sarr carr l =
  if piv = 0 then Unsafe.sub sarr (lit_code_arr carr l)
  else if Unsafe.Arith.eqWitness l piv carr then Array.length carr
  else if Unsafe.Arith.eqWitness l (Unsafe.Arith.subWitness 0 piv carr) carr
  then Unsafe.Arith.subWitness 0 (Array.length carr) carr
  else 0
End

Theorem img_code_arr_spec:
  INT piv pivv ∧ INT l lv ∧ (rat ⇔ piv ≠ 0) ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS l) < LENGTH sarr ∧
  Num (ABS piv) ≤ LENGTH sarr ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "img_code_arr" (get_ml_prog_state()))
    [pivv; sarrv; carrv; lv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml)
    (POSTv v. &INT (img_code rat piv sarr l) v *
      ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml)
Proof
  rw[]>>
  xcf "img_code_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    xlet_auto_spec (SOME lit_code_arr_spec)
    >- (xsimpl>>simp[])>>
    `lit_code l < LENGTH (lit_sarr sarr)` by simp[lit_code_bound]>>
    xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_sub_spec)>>
    qexistsl_tac [`ARRAY_OF NUM carrv dml`,`lit_sarr sarr`,`lit_code l`]>>
    xsimpl>>
    metis_tac[EL_lit_sarr_img_code])>>
  simp[img_code_def]>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>simp[])>>
  xif
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr)`,`dml`]>>
    xsimpl>>
    simp[NUM_def])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
  >- (xsimpl>>intLib.ARITH_TAC)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>intLib.ARITH_TAC)>>
  xif
  >- (
    xlet`POSTv kv. &NUM (LENGTH dml) kv *
      ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml`
    >- (
      xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
      qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr)`,`dml`]>>
      xsimpl)>>
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
    qexistsl_tac [`&LENGTH dml`,`dml`,`0`,`ARRAY_OF INT sarrv (lit_sarr sarr)`]>>
    gvs[NUM_def,INT_def]>>
    xsimpl>>
    intLib.ARITH_TAC)>>
  xlit>>xsimpl
QED

(* The variable of the literal m, and the stamp that makes m false: b marks a
  variable true and b + 1 false *)
Quote add_cakeml:
  fun var_arr w m =
  if Unsafe.Arith.ltWitness m 0 w then Unsafe.Arith.subWitness 0 m w else m
End

Theorem var_arr_spec:
  INT m mv ∧ Num (ABS m) ≤ 256 * LENGTH ls ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "var_arr" (get_ml_prog_state()))
    [wv; mv] (ARRAY_OF NUM wv ls)
    (POSTv v. &NUM (Num (ABS m)) v * ARRAY_OF NUM wv ls)
Proof
  rw[]>>
  xcf "var_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_lt_arr_spec))
  >- (xsimpl>>simp[])>>
  xif
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_weaken>>
    irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
    qexistsl_tac [`m`,`0`]>>
    simp[INT_def]>>
    xsimpl>>
    simp[NUM_def]>>
    intLib.ARITH_TAC)>>
  xvar>>xsimpl>>
  `&Num (ABS m) = m` by intLib.ARITH_TAC>>
  simp[NUM_def]
QED

Quote add_cakeml:
  fun stamp_arr w b m =
  if Unsafe.Arith.gtWitness m 0 w then Unsafe.Arith.+ b 1 else b
End

Theorem stamp_arr_spec:
  NUM b bv ∧ INT m mv ∧ Num (ABS m) ≤ 256 * LENGTH ls ∧ b + 1 < 2 ** 30 ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "stamp_arr" (get_ml_prog_state()))
    [wv; bv; mv] (ARRAY_OF NUM wv ls)
    (POSTv v. &NUM (if m > 0 then b + 1 else b) v * ARRAY_OF NUM wv ls)
Proof
  strip_tac>>
  xcf "stamp_arr" (get_ml_prog_state ())>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_gt_arr_spec))
  >- (xsimpl>>simp[])>>
  xif
  >- (
    xapp_prepare_goal>>
    irule cfAppTheory.app_wgframe>>
    irule_at Any num_add_spec>>
    qexistsl_tac [`1`,`b`,`ARRAY_OF NUM wv ls`]>>
    simp[NUM_def,INT_def]>>
    xsimpl)>>
  xvar>>xsimpl
QED

Quote add_cakeml:
  fun inc_tally_arr tally c = Unsafe.update tally c (Unsafe.sub tally c + 1)
End

Theorem inc_tally_arr_spec:
  NUM c cv ∧ c < LENGTH tally ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "inc_tally_arr" (get_ml_prog_state()))
    [tallyv; cv]
    (ARRAY_OF NUM tallyv tally)
    (POSTv uv. &UNIT_TYPE () uv * ARRAY_OF NUM tallyv (inc_tally c tally))
Proof
  rw[]>>
  xcf "inc_tally_arr" (get_ml_prog_state ())>>
  xlet`POSTv xv. &NUM (EL c tally) xv * ARRAY_OF NUM tallyv tally`
  >- (xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_sub_spec)>>xsimpl)>>
  xlet_autop>>
  xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
  xsimpl>>
  qexistsl_tac [`emp`,`tally`,`EL c tally + 1`,`c`]>>
  simp[inc_tally_def]>>
  xsimpl
QED

(* Tally the moved literals of D below index i that are not mapped to ⊤ *)
Quote add_cakeml:
  fun tally_rest_arr piv sarr carr tally d i =
  if i = 0 then ()
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 d
      val l = Unsafe.vsub d i1
      val c = lit_code_arr carr l
      val y =
        (if piv = 0 then Unsafe.sub sarr c
         else if Unsafe.Arith.eqWitness l piv carr then Array.length carr
         else if Unsafe.Arith.eqWitness l
                   (Unsafe.Arith.subWitness 0 piv carr) carr
         then Unsafe.Arith.subWitness 0 (Array.length carr) carr
         else 0)
    in
      if y = 0 then tally_rest_arr piv sarr carr tally d i1
      else if Unsafe.Arith.eqWitness y l carr then
        tally_rest_arr piv sarr carr tally d i1
      else if Unsafe.Arith.eqWitness y (Array.length carr) carr then
        tally_rest_arr piv sarr carr tally d i1
      else
        (inc_tally_arr tally c;
         tally_rest_arr piv sarr carr tally d i1)
    end
End

Theorem tally_rest_arr_spec:
  ∀rat piv sarr D i tally pivv sarrv tallyv dv iv.
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  LENGTH sarr = LENGTH dml ∧ Num (ABS piv) ≤ LENGTH sarr ∧
  img_bnd rat piv sarr ∧
  vcclause_TYPE D dv ∧ NUM i iv ∧ i ≤ length D ∧
  (∀j. j < i ⇒ Num (ABS (sub D j)) < LENGTH sarr) ∧
  2 * LENGTH sarr ≤ LENGTH tally ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "tally_rest_arr" (get_ml_prog_state()))
    [pivv; sarrv; carrv; tallyv; dv; iv]
    (ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
     ARRAY_OF NUM tallyv tally)
    (POSTv v. &UNIT_TYPE () v * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM carrv dml *
      ARRAY_OF NUM tallyv (tally_rest rat piv sarr D i tally))
Proof
  ho_match_mp_tac tally_rest_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac>>
  xcf "tally_rest_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[Once tally_rest_def,ARRAY_OF_refl])>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[UnsafeProgTheory.vsub_side_def])>>
  `Num (ABS (sub D (i − 1))) < LENGTH sarr` by simp[]>>
  xlet_auto_spec (SOME lit_code_arr_spec)
  >- (xsimpl>>simp[])>>
  xlet_autop>>
  xlet`POSTv yv.
    &INT (img_code rat piv sarr (sub D (i − 1))) yv *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
    ARRAY_OF NUM tallyv tally`
  >- (
    xif
    >- (
      `lit_code (sub D (i − 1)) < LENGTH (lit_sarr sarr)` by
        simp[lit_code_bound]>>
      xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_sub_spec)>>
      qexistsl_tac [`ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally`,
        `lit_sarr sarr`,`lit_code (sub D (i − 1))`]>>
      xsimpl>>
      metis_tac[EL_lit_sarr_img_code])>>
    simp[img_code_def]>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
    >- (xsimpl>>gvs[])>>
    xif
    >- (
      xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
      qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`,
        `dml`]>>
      xsimpl>>
      simp[NUM_def])>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
    >- (xsimpl>>gvs[]>>intLib.ARITH_TAC)>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
    >- (xsimpl>>gvs[]>>intLib.ARITH_TAC)>>
    xif
    >- (
      xlet`POSTv kv. &NUM (LENGTH dml) kv * ARRAY_OF INT sarrv (lit_sarr sarr) *
        ARRAY_OF NUM carrv dml * ARRAY_OF NUM tallyv tally`
      >- (
        xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
        qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) *
          ARRAY_OF NUM tallyv tally`,`dml`]>>
        xsimpl)>>
      xapp_prepare_goal>>
      irule cfAppTheory.app_wgframe>>
      irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
      qexistsl_tac [`&LENGTH dml`,`dml`,`0`,
        `ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`]>>
      gvs[NUM_def,INT_def]>>
      xsimpl>>
      intLib.ARITH_TAC)>>
    xlit>>xsimpl)>>
  qpat_x_assum`_ ≠ 0 ⇒ _` (drule_then assume_tac)>>
  simp[Once tally_rest_def]>>
  qabbrev_tac`y = img_code rat piv sarr (sub D (i − 1))`>>
  `Num (ABS y) ≤ LENGTH sarr` by gvs[img_bnd_def,Abbr`y`]>>
  xlet_autop>>
  xif
  >- (xapp>>xsimpl>>gvs[])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[])>>
  xif
  >- (xapp>>xsimpl>>gvs[])>>
  xlet`POSTv kv. &NUM (LENGTH dml) kv * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`,
      `dml`]>>
    xsimpl)>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xif
  >- (xapp>>xsimpl>>gvs[])>>
  `lit_code (sub D (i − 1)) < LENGTH tally` by (
    irule LESS_LESS_EQ_TRANS>>
    first_assum (irule_at Any)>>
    simp[lit_code_bound])>>
  xlet_auto_spec (SOME inc_tally_arr_spec)
  >- xsimpl>>
  xapp>>xsimpl>>
  gvs[inc_tally_def]
QED

(***
  The round for one clause of the formula, with recursive undo
 ***)

(* c is the code of l and y its image code; ⊤ and ⊥ are ±kk, the length of
  the map. The stamp b marks a variable true and b + 1 false. *)
Quote add_cakeml:
  fun red_pass_arr lno fml carr b piv sarr tally d i s k =
  if i = 0 then unit_prop_vb_undo_arr lno fml carr b s k (String.size s)
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 d
      val l = Unsafe.vsub d i1
      val c = lit_code_arr carr l
      val y =
        (if piv = 0 then Unsafe.sub sarr c
         else if Unsafe.Arith.eqWitness l piv carr then Array.length carr
         else if Unsafe.Arith.eqWitness l
                   (Unsafe.Arith.subWitness 0 piv carr) carr
         then Unsafe.Arith.subWitness 0 (Array.length carr) carr
         else 0)
      val kk = Array.length carr
    in
      if Unsafe.Arith.eqWitness y kk carr then
        (tally_rest_arr piv sarr carr tally d i1; k)
      else
        let
          val mv =
            (if y = 0 then False
             else if Unsafe.Arith.eqWitness y l carr then False
             else True)
        in
          (if mv then inc_tally_arr tally c else ();
           if Unsafe.Arith.eqWitness y (Unsafe.Arith.subWitness 0 kk carr) carr
           then red_pass_arr lno fml carr b piv sarr tally d i1 s k
           else
             let
               val m = (if y = 0 then l else y)
               val n = var_arr carr m
               val bm = stamp_arr carr b m
               val st = Unsafe.sub carr n
             in
               if Unsafe.Arith.< st b then
                 (Unsafe.update carr n bm;
                  let
                    val r = red_pass_arr lno fml carr b piv sarr tally d i1 s k
                  in
                    (Unsafe.update carr n 0; r)
                  end)
               else if Unsafe.Arith.= st bm then
                 red_pass_arr lno fml carr b piv sarr tally d i1 s k
               else (tally_rest_arr piv sarr carr tally d i1; k)
             end)
        end
    end
End

val l_tm = ``sub (D:int vector) (i − 1)``;
val y_tm = ``img_code (piv ≠ 0) (piv:int) (sarr:int list) ^l_tm``;
val m_tm = ``if ^y_tm = 0 then ^l_tm else ^y_tm``;
val n_tm = ``Num (ABS ^m_tm)``;
val bm_tm = ``if ^m_tm > 0 then b + 1 else (b:num)``;
val mv_tm = ``^y_tm ≠ 0 ∧ ^y_tm ≠ ^l_tm``;
val tally1_tm =
  ``if ^mv_tm then inc_tally (lit_code ^l_tm) tally else (tally:num list)``;

Theorem red_pass_arr_spec:
  ∀fmlls dml b rat piv sarr tally D i s k
   lnov bv pivv tallyv dv iv sv kv.
  NUM lno lnov ∧ NUM b bv ∧
  INT piv pivv ∧ (rat ⇔ piv ≠ 0) ∧
  vcclause_TYPE D dv ∧ NUM i iv ∧ STRING_TYPE s sv ∧
  NUM k kv ∧
  stamps_ok dml b ∧ bnd_fml fmlls (LENGTH dml) ∧
  i ≤ length D ∧ (∀j. j < i ⇒ Num (ABS (sub D j)) < LENGTH sarr) ∧
  img_bnd rat piv sarr ∧ LENGTH sarr = LENGTH dml ∧
  Num (ABS piv) ≤ LENGTH sarr ∧
  2 * LENGTH sarr ≤ LENGTH tally ∧ k ≤ strlen s ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "red_pass_arr" (get_ml_prog_state()))
    [lnov; fmlv; carrv; bv; pivv; sarrv; tallyv; dv; iv; sv; kv]
    (ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
     ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally)
    (POSTve
      (λv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS r dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(red_pass_list fmlls dml b rat piv sarr tally D i s k
              (strlen s) = SOME (r,dml',tally') ∧ NUM r v))
      (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        SEP_EXISTS dml' tally'.
          ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
          &(Fail_exn e ∧
            red_pass_list fmlls dml b rat piv sarr tally D i s k
              (strlen s) = NONE)))
Proof
  completeInduct_on`i`>>
  rpt strip_tac>>
  qpat_x_assum`rat ⇔ _` SUBST_ALL_TAC>>
  drule_then strip_assume_tac stamps_ok_bounds>>
  xcf "red_pass_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- suspend "Base">>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[UnsafeProgTheory.vsub_side_def])>>
  `Num (ABS ^l_tm) < LENGTH sarr` by simp[]>>
  xlet_auto_spec (SOME lit_code_arr_spec)
  >- (xsimpl>>simp[])>>
  xlet_autop>>
  xlet`POSTv yv. &INT (^y_tm) yv * ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    xif
    >- (
      `lit_code ^l_tm < LENGTH (lit_sarr sarr)` by simp[lit_code_bound]>>
      xapp_spec (Q.ISPEC`INT` ARRAY_OF_unsafe_sub_spec)>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
        ARRAY_OF NUM tallyv tally`,`lit_sarr sarr`,`lit_code ^l_tm`]>>
      xsimpl>>
      metis_tac[EL_lit_sarr_img_code])>>
    simp[img_code_def]>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
    >- (xsimpl>>gvs[])>>
    xif
    >- (
      xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
        ARRAY_OF NUM tallyv tally`,`dml`]>>
      xsimpl>>
      simp[NUM_def])>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
    >- (xsimpl>>gvs[]>>intLib.ARITH_TAC)>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
    >- (xsimpl>>gvs[]>>intLib.ARITH_TAC)>>
    xif
    >- (
      xlet`POSTv kv. &NUM (LENGTH dml) kv * ARRAY_OF vcclause_TYPE fmlv fmlls *
        ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM carrv dml *
        ARRAY_OF NUM tallyv tally`
      >- (
        xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
        qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
          ARRAY_OF NUM tallyv tally`,`dml`]>>
        xsimpl)>>
      xapp_prepare_goal>>
      irule cfAppTheory.app_wgframe>>
      irule_at Any (Q.ISPEC`NUM` int_sub_arr_spec)>>
      qexistsl_tac [`&LENGTH dml`,`dml`,`0`,`ARRAY_OF vcclause_TYPE fmlv fmlls *
        ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`]>>
      gvs[NUM_def,INT_def]>>
      xsimpl>>
      intLib.ARITH_TAC)>>
    xlit>>xsimpl)>>
  xlet`POSTv kv. &NUM (LENGTH dml) kv * ARRAY_OF NUM carrv dml *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM tallyv tally`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_length_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv tally`,`dml`]>>
    xsimpl)>>
  `Num (ABS ^y_tm) ≤ LENGTH sarr` by metis_tac[img_bnd_def]>>
  `LENGTH dml ≠ 0` by (strip_tac>>gvs[])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xif
  >- suspend "Top">>
  xlet_autop>>
  xlet`POSTv mvv. &BOOL (^mv_tm) mvv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`
  >- (
    xif
    >- (xcon>>xsimpl)>>
    xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
    >- (xsimpl>>gvs[])>>
    xif
    >- (xcon>>xsimpl)>>
    xcon>>xsimpl)>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv (^tally1_tm)`
  >- (
    xif
    >- (
      `lit_code ^l_tm < LENGTH tally` by (
        irule LESS_LESS_EQ_TRANS>>
        first_assum (irule_at Any)>>
        simp[lit_code_bound])>>
      xapp_spec inc_tally_arr_spec>>
      qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
        ARRAY_OF INT sarrv (lit_sarr sarr)`,`tally`,`lit_code ^l_tm`]>>
      simp[]>>
      xsimpl)>>
    xcon>>xsimpl>>
    IF_CASES_TAC
    >- gvs[]>>
    xsimpl)>>
  `LENGTH (^tally1_tm) = LENGTH tally` by rw[inc_tally_def]>>
  qpat_x_assum`∀m. m < i ⇒ ∀fmlls. _` (qspec_then`i − 1` mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_sub_arr_spec))
  >- (xsimpl>>gvs[NUM_def])>>
  xlet_auto_spec (SOME (Q.ISPEC`NUM` int_eq_arr_spec))
  >- (xsimpl>>intLib.ARITH_TAC)>>
  xif
  >- suspend "Bot">>
  once_rewrite_tac[red_pass_list_def]>>
  simp[]>>
  xlet_autop>>
  xlet`POSTv mv'. &INT (^m_tm) mv' * ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv (^tally1_tm)`
  >- (
    xif>>
    xvar>>xsimpl)>>
  `^n_tm < LENGTH dml` by (
    irule img_lit_bound>>
    qexists_tac`LENGTH dml`>>
    gvs[])>>
  xlet_auto_spec (SOME var_arr_spec)
  >- (xsimpl>>simp[])>>
  xlet_auto_spec (SOME stamp_arr_spec)
  >- (xsimpl>>simp[])>>
  xlet`POSTv stv. &NUM (EL ^n_tm dml) stv *
    ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF NUM carrv dml *
    ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv (^tally1_tm)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_sub_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv (^tally1_tm)`,`dml`,`^n_tm`]>>
    xsimpl)>>
  xlet_auto_spec (SOME num_lt_spec)
  >- (xsimpl>>simp[])>>
  `any_el ^n_tm dml 0 = EL ^n_tm dml` by simp[any_el_ALT]>>
  xif
  >- suspend "Assign">>
  xlet_auto_spec (SOME num_eq_spec)
  >- (xsimpl>>rw[])>>
  xif
  >- suspend "Same">>
  xlet_auto_spec (SOME tally_rest_arr_spec)
  >- xsimpl>>
  xvar>>xsimpl
QED

Resume red_pass_arr_spec[Base]:
  simp[Once red_pass_list_def]>>
  xlet_autop>>
  xapp_spec unit_prop_vb_undo_arr_spec>>
  xsimpl>>
  qexistsl_tac [`ARRAY_OF INT sarrv (lit_sarr sarr) * ARRAY_OF NUM tallyv tally`,
    `s`,`strlen s`,`k`,`fmlls`,`b`,`dml`,`lno`]>>
  xsimpl>>
  rw[Once red_pass_list_def]>>
  qexistsl_tac [`x`,`tally`]>>
  xsimpl
QED

Resume red_pass_arr_spec[Top]:
  xlet_auto_spec (SOME tally_rest_arr_spec)
  >- xsimpl>>
  xvar>>xsimpl>>
  simp[Once red_pass_list_def]>>
  xsimpl
QED

Resume red_pass_arr_spec[Bot]:
  `dml ≠ []` by (strip_tac>>gvs[])>>
  once_rewrite_tac[red_pass_list_def]>>
  simp[]>>
  xapp>>
  qexistsl_tac [`emp`,
    `if -&LENGTH dml ≠ ^l_tm then inc_tally (lit_code ^l_tm) tally else tally`,
    `sarr`,`s`,`piv`,`k`,`fmlls`,`dml`,`b`,`D`]>>
  xsimpl>>
  rw[inc_tally_def]
QED

Resume red_pass_arr_spec[Assign]:
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM carrv (LUPDATE (^bm_tm) ^n_tm dml) *
    ARRAY_OF NUM tallyv (^tally1_tm)`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv (^tally1_tm)`,`dml`,`^bm_tm`,`^n_tm`]>>
    xsimpl)>>
  `stamps_ok (LUPDATE (^bm_tm) ^n_tm dml) b` by
    simp[stamps_ok_LUPDATE_stamp]>>
  xlet`POSTve
    (λrv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      SEP_EXISTS r dml' tally'.
        ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
        &(red_pass_list fmlls (LUPDATE (^bm_tm) ^n_tm dml) b (piv ≠ 0) piv
            sarr (^tally1_tm) D (i − 1) s k (strlen s) =
            SOME (r,dml',tally') ∧ NUM r rv))
    (λe. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      SEP_EXISTS dml' tally'.
        ARRAY_OF NUM carrv dml' * ARRAY_OF NUM tallyv tally' *
        &(Fail_exn e ∧
          red_pass_list fmlls (LUPDATE (^bm_tm) ^n_tm dml) b (piv ≠ 0) piv
            sarr (^tally1_tm) D (i − 1) s k (strlen s) = NONE))`
  >- (
    xapp>>
    qexistsl_tac [`emp`,`^tally1_tm`,`sarr`,`s`,`piv`,`k`,
      `fmlls`,`LUPDATE (^bm_tm) ^n_tm dml`,`b`,`D`]>>
    xsimpl)
  >- (
    xsimpl>>
    rw[]>>
    metis_tac[SEP_IMP_REFL])>>
  `LENGTH dml' = LENGTH dml` by (
    drule_at (Pos last) red_pass_list_LENGTH>>
    simp[])>>
  xlet`POSTv uv. ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
    ARRAY_OF NUM carrv (LUPDATE 0 ^n_tm dml') * ARRAY_OF NUM tallyv tally'`
  >- (
    xapp_spec (Q.ISPEC`NUM` ARRAY_OF_unsafe_update_spec)>>
    qexistsl_tac [`ARRAY_OF vcclause_TYPE fmlv fmlls * ARRAY_OF INT sarrv (lit_sarr sarr) *
      ARRAY_OF NUM tallyv tally'`,`dml'`,`0`,`^n_tm`]>>
    xsimpl)>>
  xvar>>xsimpl
QED

Resume red_pass_arr_spec[Same]:
  xapp>>
  simp[]
QED

Finalise red_pass_arr_spec;
