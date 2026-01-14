(*
  This refines ccnf_list to use arrays
*)
Theory ccnf_arrayProg
Ancestors
  UnsafeProg UnsafeProof
  ccnf ccnf_list mlint syntax_helper
Libs
  preamble basis blastLib

val _ = hide_environments true;

(* Default inheritance path, means all programs will use
  the unsafe primitives *)
val _ = translation_extends"UnsafeProg";

Overload "vcclause_TYPE" = ``VECTOR_TYPE INT``

(* TODO: MOVE? *)

Theorem OPTION_TYPE_SPLIT:
  OPTION_TYPE a x v ⇔
  (x = NONE ∧ v = Conv (SOME (TypeStamp (strlit "None") 2)) []) ∨
  (∃y vv. x = SOME y ∧ v = Conv (SOME (TypeStamp (strlit "Some") 2)) [vv] ∧ a y vv)
Proof
  Cases_on`x`>>rw[OPTION_TYPE_def]
QED

Theorem W8ARRAY_refl:
  (W8ARRAY fml fmllsv ==>> W8ARRAY fml fmllsv) ∧
  (W8ARRAY fml fmllsv ==>> W8ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Quote add_cakeml:
  exception Fail string;
End

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``strlit "Fail"``

Definition Fail_exn_def:
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)
End

Definition format_failure_def:
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val res = translate format_failure_def;

(* TODO:
  w8ult should be native,
  = on bytes should be efficient *)
Definition w8ult_def:
  w8ult (x:word8) (y:word8) ⇔
    w2n x < w2n y
End

Theorem w8ult_thm[simp]:
  w8ult x y ⇔ x <+ y
Proof
  rw[w8ult_def,WORD_LO]
QED

val res = translate w8ult_def;

Definition uvsub_def:
  uvsub v n = sub_unsafe v n
End

val res = translate uvsub_def;

val uvsub_side_def = fetch "-" "uvsub_side_def";

Quote add_cakeml:
  fun all_assigned_arr carr b v i =
  if i = 0 then True
  else
    let
      val i1 = i - 1
      val c = uvsub v i1
    in
      if c < 0
      then
        (if Unsafe.w8sub carr (~c) = b
        then
          all_assigned_arr carr b v i1
        else
          False)
      else
        (if w8ult b (Unsafe.w8sub carr c)
        then
          all_assigned_arr carr b v i1
        else False)
    end
End

Theorem uvsub_eq_sub[simp]:
  uvsub v n = sub v n
Proof
  simp[uvsub_def,oneline mlvectorTheory.sub_unsafe_def,oneline mlvectorTheory.sub_def]
QED


Theorem all_assigned_arr_spec:
  ∀Clist b vec i bv vecv iv Carrv.
  WORD8 b bv ∧
  vcclause_TYPE vec vecv ∧
  NUM i iv ∧
  all_assigned_list' Clist b vec i = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_assigned_arr" (get_ml_prog_state()))
    [Carrv; bv; vecv; iv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
      W8ARRAY Carrv Clist *
      &BOOL res v)
Proof
  ho_match_mp_tac all_assigned_list'_ind>>
  rw[]>>
  pop_assum mp_tac>> simp[Once all_assigned_list'_def]>>
  strip_tac>>
  xcf "all_assigned_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>fs[]
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[uvsub_side_def])>>
  xlet_autop>>
  xif>>fs[]
  >- (
    rpt xlet_autop>>
    xif>>fs[]
    >- (xapp>>xsimpl)>>
    xcon>>
    xsimpl)
  >- (
    xlet_auto
    >- (xsimpl>>intLib.ARITH_TAC)>>
    xlet_autop>>
    xif>>fs[]
    >- (xapp>>xsimpl)>>
    xcon>>
    xsimpl)
QED

Definition badd1_def[simp]:
  badd1 b = (b+1w):word8
End

val res = translate badd1_def;

Quote add_cakeml:
  fun delete_literals_sing_arr lno carr b v i =
  if i = 0 then True
  else
    let
      val i1 = i - 1
      val c = uvsub v i1
    in
      if c < 0
      then
        let
          val nc = ~c
        in
          if Unsafe.w8sub carr nc = b
          then
            delete_literals_sing_arr lno carr b v i1
          else
            if all_assigned_arr carr b v i1
            then
              (Unsafe.w8update carr nc (badd1 b); False)
            else
              raise Fail (format_failure lno "clause not empty or singleton after reduction")
        end
      else
        if w8ult b (Unsafe.w8sub carr c)
        then
          delete_literals_sing_arr lno carr b v i1
        else
          if all_assigned_arr carr b v i1
          then
            (Unsafe.w8update carr c b; False)
          else
            raise Fail (format_failure lno "clause not empty or singleton after reduction")
    end
End

Theorem delete_literals_sing_arr_spec:
  ∀Clist b vec i bv vecv iv Carrv res.
  NUM lno lnov ∧
  WORD8 b bv ∧
  VECTOR_TYPE INT vec vecv ∧
  NUM i iv ∧
  delete_literals_sing_list' Clist b vec i = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_literals_sing_arr" (get_ml_prog_state()))
    [lnov; Carrv; bv; vecv; iv]
    (W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS b' Clist'.
        W8ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        W8ARRAY Carrv Clist *
        &(Fail_exn e ∧ res = NONE))
    )
Proof
  ho_match_mp_tac delete_literals_sing_list'_ind>>
  rw[]>>
  pop_assum mp_tac>> simp[Once delete_literals_sing_list'_def]>>
  strip_tac>>
  xcf "delete_literals_sing_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[uvsub_side_def])>>
  rpt xlet_autop>>
  xif>>gvs[]
  >- (
    rpt xlet_autop>>
    xif>>gvs[]
    >- (xapp>>xsimpl)>>
    rpt xlet_autop>>
    xif>>gvs[]
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      EVAL_TAC)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xlet_auto
  >-  (xsimpl>>gvs[]>>intLib.ARITH_TAC)>>
  xlet_autop>>
  xif>>gvs[]
  >- (xapp>>xsimpl)>>
  xlet_autop>>
  xif>>fs[]
  >- (
    xlet_auto
    >- (xsimpl>>gvs[]>>intLib.ARITH_TAC)>>
    xcon>>xsimpl>>
    EVAL_TAC)>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[Fail_exn_def]
QED

Definition bw0_def[simp]:
  bw0 = (0w):word8
End

Definition bw1_def[simp]:
  bw1 = (1w):word8
End

Definition bw253_def[simp]:
  bw253 = (253w):word8
End

val bw0_v_thm = translate bw0_def;
val bw1_v_thm = translate bw1_def;
val bw253_v_thm = translate bw253_def;

Definition badd2_def[simp]:
  badd2 b = (b+2w):word8
End

val res = translate badd2_def;

Quote add_cakeml:
  fun reset_dm_arr carr b sz =
  let
    val len = Word8Array.length carr
  in
  if len < sz then
    (Word8Array.array (2 * sz) bw0, bw1)
  else
    if w8ult b bw253
    then (carr,badd2 b)
    else (Word8Array.array len bw0, bw1)
  end
End

Theorem reset_dm_arr_spec:
  NUM sz szv ∧
  WORD8 b bv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reset_dm_arr" (get_ml_prog_state()))
    [Carrv; bv; szv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
        SEP_EXISTS Carrv' b' Clist'.
        W8ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) WORD8 (Carrv', b') v ∧
          reset_dm_list Clist b sz = (Clist',b')))
Proof
  rw[]>>
  xcf "reset_dm_arr" (get_ml_prog_state ())>>
  assume_tac bw0_v_thm>>
  assume_tac bw253_v_thm>>
  rpt xlet_autop>>
  xif>>gvs[]
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[reset_dm_list_def,PAIR_TYPE_def]>>
    CONJ_TAC >- metis_tac[bw1_def,bw1_v_thm]>>
    xsimpl)>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[reset_dm_list_def,PAIR_TYPE_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[reset_dm_list_def,PAIR_TYPE_def]>>
  CONJ_TAC >- metis_tac[bw1_def,bw1_v_thm]>>
  xsimpl
QED

val res = translate sz_lit_map_def;

Theorem sz_lit_map_side:
  ∀i v m.
  i ≤ length v ⇒
  sz_lit_map_side i v m
Proof
  ho_match_mp_tac sz_lit_map_ind>>rw[]>>
  simp[Once (fetch "-" "sz_lit_map_side_def")]>>
  rw[]>>gvs[]
QED

val _ = sz_lit_map_side |> update_precondition;

Definition mk_bb_nc_def[simp]:
  mk_bb_nc d (b:word8) =
  if d > 0 then (b+1w, Num d) else (b,Num (-d))
End

val res = translate mk_bb_nc_def;

Theorem mk_bb_nc_side[local]:
  mk_bb_nc_side d b ⇔ T
Proof
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC
QED

val _ = mk_bb_nc_side |> update_precondition;

Quote add_cakeml:
  fun init_lit_map_arr i v carr b =
  if i = 0
  then ()
  else
    let
      val i1 = i - 1
      val d = uvsub v i1
    in
      case mk_bb_nc d b of (bb,nc) =>
        (Unsafe.w8update carr nc bb;
        init_lit_map_arr i1 v carr b)
    end
End

Theorem init_lit_map_arr_spec:
  ∀i vec Clist b bv vecv iv Carrv.
  WORD8 b bv ∧
  VECTOR_TYPE INT vec vecv ∧
  NUM i iv ∧
  init_lit_map_list' i vec Clist b = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "init_lit_map_arr" (get_ml_prog_state()))
    [iv; vecv; Carrv; bv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
      W8ARRAY Carrv res)
Proof
  ho_match_mp_tac init_lit_map_list'_ind>>
  rpt strip_tac>>
  pop_assum mp_tac>>
  simp[Once init_lit_map_list'_def]>>
  strip_tac>>
  xcf "init_lit_map_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>fs[]
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[uvsub_side_def])>>
  xlet_autop>>
  pairarg_tac>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xapp>>gvs[]
QED

Quote add_cakeml:
  fun prepare_rup carr b v =
  let
    val lv = Vector.length v
    val sz = sz_lit_map lv v 0
  in
    case reset_dm_arr carr b sz of (dml',b') =>
    (init_lit_map_arr lv v dml' b'; (dml',b'))
  end
End

Theorem prepare_rup_spec:
  WORD8 b bv ∧
  VECTOR_TYPE INT vec vecv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "prepare_rup" (get_ml_prog_state()))
    [Carrv; bv; vecv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
        SEP_EXISTS Carrv' b' Clist' bv'.
        W8ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) WORD8 (Carrv', b') v ∧
          prepare_rup Clist b vec = (Clist',b')))
Proof
  rw[]>>
  xcf "prepare_rup" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    irule sz_lit_map_side>>
    simp[])>>
  xlet_auto>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  simp[prepare_rup_def]>>
  rename1`init_lit_map_list (length vec) vec Clist' b'`>>
  `IS_SOME (init_lit_map_list' (length vec) vec Clist' b')` by (
    irule init_lit_map_list'_SOME>>
    simp[]>>
    drule reset_dm_list_LENGTH>>
    rw[]>>
    metis_tac[bnd_clause_le,sz_lit_map_bnd_clause])>>
  fs[IS_SOME_EXISTS]>>
  xlet_autop>>
  xcon>>xsimpl>>
  metis_tac[init_lit_map_list']
QED

Quote add_cakeml:
  fun unit_prop_one lno fml carr b i =
  if i < Array.length fml
  then
    case Unsafe.sub fml i of
      None =>
        raise Fail (format_failure lno ("invalid clause hint (maybe deleted): " ^ Int.toString i))
    | Some c =>
      delete_literals_sing_arr lno carr b c (Vector.length c)
  else
    raise Fail (format_failure lno ("invalid clause hint: " ^ Int.toString i))
End

Quote add_cakeml:
  fun unit_prop_arr lno fml carr b hints =
    case hints of
      [] => False
    | i::is =>
      if unit_prop_one lno fml carr b i
      then
        True
      else
        unit_prop_arr lno fml carr b is
End

Theorem unit_prop_one_spec:
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  NUM i iv ∧
  unit_prop_one' fmlls Clist b i = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_one" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; iv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Clist'.
        W8ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Clist'.
        W8ARRAY Carrv Clist' *
        &(Fail_exn e ∧ res = NONE))
    )
Proof
  simp[Once unit_prop_one'_def]>>
  strip_tac>>
  xcf "unit_prop_one" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  drule LIST_REL_LENGTH>>
  rw[]>>
  reverse xif>>gvs[any_el_ALT]
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  rename1`EL h fmlls`>>
  `OPTION_TYPE vcclause_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  rpt xlet_autop>>
  gvs[OPTION_TYPE_SPLIT]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt(first_x_assum $ irule_at Any>>xsimpl)
QED

Theorem unit_prop_arr_spec:
  ∀ls lsv Carrv Clist b bv res.
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  LIST_TYPE NUM ls lsv ∧
  unit_prop_list' fmlls Clist b ls = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; lsv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Clist'.
        W8ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Clist'.
        W8ARRAY Carrv Clist' *
        &(Fail_exn e ∧ res = NONE))
    )
Proof
  Induct>>rw[]>>
  pop_assum mp_tac>>
  simp[Once unit_prop_list'_def]>>
  strip_tac>>
  xcf "unit_prop_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xlet_autop
  >- (
    xsimpl>>
    gvs[AllCaseEqs()])>>
  xif>>gvs[]
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xapp>>xsimpl>>
  first_x_assum $ irule_at Any>>xsimpl
QED

val res = translate parse_vb_num_aux_def;

Theorem parse_vb_num_aux_side[local]:
  parse_vb_num_aux_side a b c d e ⇔ T
Proof
  cheat
QED

val _ = parse_vb_num_aux_side |> update_precondition;

val res = translate parse_vb_num_def;
val res = translate parse_vb_int_def;

Quote add_cakeml:
  fun unit_prop_vb_arr lno fml carr b s i1 len =
    case parse_vb_int s i1 len of (m,i) =>
    if m <= 0 then Some i1
    else
      if unit_prop_one lno fml carr b m
      then
        None
      else
        unit_prop_vb_arr lno fml carr b s i len
End

Theorem unit_prop_arr_vb_spec:
  ∀ls lsv Carrv Clist b bv res.
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  STRING_TYPE s sv ∧
  NUM i iv ∧
  NUM l lv ∧
  unit_prop_vb_list' fmlls Clist b s i l = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_vb_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; sv; iv; lv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Clist'.
        W8ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ OPTION_TYPE NUM b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Clist'.
        W8ARRAY Carrv Clist' *
        &(Fail_exn e ∧ res = NONE))
    )
Proof
  cheat
  (*
  Induct>>rw[]>>
  pop_assum mp_tac>>
  simp[Once unit_prop_list'_def]>>
  strip_tac>>
  xcf "unit_prop_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xlet_autop
  >- (
    xsimpl>>
    gvs[AllCaseEqs()])>>
  xif>>gvs[]
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xapp>>xsimpl>>
  first_x_assum $ irule_at Any>>xsimpl*)
QED

Quote add_cakeml:
  fun is_rup_arr lno fml carr b v hints =
  let val dmb = prepare_rup carr b v in
    case dmb of (carr',b') =>
    if unit_prop_arr lno fml carr' b' hints
    then dmb
    else
      raise Fail (format_failure lno ("unit propagation did not prove RUP"))
  end
End

(* Note, we will prove this spec in two parts *)
Theorem is_rup_arr_spec':
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  vcclause_TYPE v vv ∧
  LIST_TYPE NUM ls lsv ∧
  is_rup_list' fmlls Clist b v ls = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; lsv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        W8ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) WORD8 (Carrv', b') v ∧
          res = (T, (Clist',b'))))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Carrv' Clist'.
        W8ARRAY Carrv' Clist' *
        &(Fail_exn e ∧ FST res = F))
    )
Proof
  rw[]>>
  xcf "is_rup_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[W8ARRAY_refl])>>
  gvs[PAIR_TYPE_def,is_rup_list'_def]>>
  xmatch>>
  xlet_autop
  >- (
    xsimpl>>
    metis_tac[W8ARRAY_refl])>>
  xif
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xraise>>
  xsimpl>>
  metis_tac[Fail_exn_def,W8ARRAY_refl]
QED

Theorem is_rup_arr_spec:
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  vcclause_TYPE v vv ∧
  LIST_TYPE NUM ls lsv ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; lsv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λres.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        W8ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) WORD8 (Carrv', b') res ∧
          is_rup_list fmlls Clist b v ls = (T,(Clist',b'))))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Carrv' Clist'.
        W8ARRAY Carrv' Clist' *
        &(Fail_exn e ∧
          FST (is_rup_list fmlls Clist b v ls) = F))
    )
Proof
  rw[]>>
  drule is_rup_list'_SOME>>
  disch_then (qspecl_then [`v`,`ls`,`b`] assume_tac)>>
  fs[IS_SOME_EXISTS]>>
  drule_all is_rup_arr_spec'>>
  drule is_rup_list'>>
  rw[]
QED

(* TODO: define and prove is_rup_vb_arr_spec *)

Quote add_cakeml:
  fun delete_arr fml i =
    if Array.length fml <= i then ()
    else
      (Unsafe.update fml i None)
End

Theorem delete_arr_spec:
  NUM i iv ∧
  LIST_REL (OPTION_TYPE a) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_arr" (get_ml_prog_state()))
    [fmlv; iv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE a) (delete_list fmlls i) fmllsv') )
Proof
  rw[]>>
  xcf "delete_arr" (get_ml_prog_state ())>>
  simp[delete_list_def]>>
  rpt xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xif>-(xcon>>xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]
QED

Quote add_cakeml:
  fun delete_ids_arr fml ls =
    case ls of
      [] => ()
    | (i::is) =>
      (delete_arr fml i; delete_ids_arr fml is)
End

Theorem delete_ids_arr_spec:
  ∀ls lsv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE a) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_ids_arr" (get_ml_prog_state()))
    [fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE a) (delete_ids_list fmlls ls) fmllsv') )
Proof
  Induct>>
  rw[]>>fs[delete_ids_list_def]>>
  xcf "delete_ids_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (xcon>>xsimpl) >>
  xlet_autop>>
  xapp>>
  xsimpl
QED

(* Parsing helpers *)

(* TODO: Mostly copied from mlintTheory *)
val result = translate (fromChar_unsafe_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail b n str mul acc =
  if n ≤ b then acc
  else
    let m = n - 1 in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub str m) * mul)
Termination
  WF_REL_TAC`measure (λ(b,n,_). n)`>>
  rw[]
End

Theorem fromChars_range_unsafe_tail_eq:
  ∀n l s mul acc.
  fromChars_range_unsafe_tail l (n+l) s mul acc =
  (fromChars_range_unsafe l n s) * mul + acc
Proof
  Induct
  >-
    rw[Once fromChars_range_unsafe_tail_def,fromChars_range_unsafe_def]>>
  rw[]>>
  simp[Once fromChars_range_unsafe_tail_def,ADD1,fromChars_range_unsafe_def]>>
  fs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s =
  fromChars_range_unsafe_tail l (n+l) s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;

val fromchars_range_unsafe_tail_side_def = theorem"fromchars_range_unsafe_tail_side_def";

Theorem fromchars_range_unsafe_tail_side_def[allow_rebind]:
  ∀a1 a0 a2 a3 a4.
  fromchars_range_unsafe_tail_side a0 a1 a2 a3 a4 ⇔
   ¬(a1 ≤ a0) ⇒
   (T ∧ a1 < 1 + strlen a2 ∧ 0 < strlen a2) ∧
   fromchars_range_unsafe_tail_side a0 (a1 − 1) a2 (a3 * 10)
     (a4 + fromChar_unsafe (strsub a2 (a1 − 1)) * a3)
Proof
  Induct>>
  rw[Once fromchars_range_unsafe_tail_side_def]>>
  simp[]>>eq_tac>>rw[ADD1]>>
  gvs[]
QED

val result = translate fromChars_range_unsafe_alt;

val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

Theorem fromChars_unsafe_ind[local]:
  fromchars_unsafe_ind
Proof
  rewrite_tac [fetch "-" "fromchars_unsafe_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ fs [padLen_DEC_eq,ADD1]
QED

val _ = fromChars_unsafe_ind |> update_precondition;

val result = translate fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
val fromchars_range_unsafe_side_def = fetch "-" "fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm[local]:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def,fromchars_range_unsafe_tail_side_def]
QED

Theorem fromString_unsafe_side[local]:
  ∀x. fromstring_unsafe_side x = T
Proof
  Cases
  \\ rw[fromstring_unsafe_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_unsafe_side_thm
  \\ rw[]
QED

val _ = update_precondition fromString_unsafe_side;

val res = translate blanks_def;
val res = translate tokenize_def;

val res = translate mk_lit_def;

val res = translate parse_until_zero_aux_def;
val res = translate parse_until_zero_def;

val res = translate parse_until_zero_nn_aux_def;
val res = translate parse_until_zero_nn_def;

val res = translate is_int_def;
val res = translate tokenize_fast_def;

val res = translate starts_with_def;

