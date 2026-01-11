(*
  This refines ccnf_list to use arrays
*)
Theory ccnf_arrayProg
Ancestors
  UnsafeProg UnsafeProof
  ccnf ccnf_list
Libs
  preamble basis blastLib

val _ = hide_environments true;

val cakeml = append_prog o process_topdecs;

(* Default inheritance path, means all programs will use
  the unsafe primitives *)
val _ = translation_extends"UnsafeProg";

Overload "vcclause_TYPE" = ``VECTOR_TYPE INT``

(* TODO: MOVE? *)
Theorem OPTION_TYPE_SPLIT:
  OPTION_TYPE a x v ⇔
  (x = NONE ∧ v = Conv (SOME (TypeStamp "None" 2)) []) ∨
  (∃y vv. x = SOME y ∧ v = Conv (SOME (TypeStamp "Some" 2)) [vv] ∧ a y vv)
Proof
  Cases_on`x`>>rw[OPTION_TYPE_def]
QED

Theorem W8ARRAY_refl:
  (W8ARRAY fml fmllsv ==>> W8ARRAY fml fmllsv) ∧
  (W8ARRAY fml fmllsv ==>> W8ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Quote cakeml:
  exception Fail string;
End

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``"Fail"``

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

Quote cakeml:
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

Quote cakeml:
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

Quote cakeml:
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
        SEP_EXISTS Carrv' b' Clist' bv'.
        W8ARRAY Carrv' Clist' *
        &(v = Conv NONE [Carrv'; bv'] ∧
        WORD8 b' bv' ∧
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
    simp[reset_dm_list_def]>>
    metis_tac[bw1_def,bw1_v_thm])>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[reset_dm_list_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[reset_dm_list_def]>>
  metis_tac[bw1_def,bw1_v_thm]
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

Quote cakeml:
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

Quote cakeml:
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
        &(v = Conv NONE [Carrv'; bv'] ∧
        WORD8 b' bv' ∧
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

Quote cakeml:
  fun unit_prop_arr lno fml carr b hints =
    case hints of
      [] => False
    | i::is =>
      if i < Array.length fml
      then
        case Unsafe.sub fml i of
          None =>
            raise Fail (format_failure lno ("invalid clause hint (maybe deleted): " ^ Int.toString i))
        | Some c =>
          if delete_literals_sing_arr lno carr b c (Vector.length c)
          then
            True
          else
            unit_prop_arr lno fml carr b is
      else
        raise Fail (format_failure lno ("invalid clause hint: " ^ Int.toString i))
End

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
  rpt xlet_autop
  >- (
    xsimpl>>
    rw[]>>gvs[])>>
  xif>>gvs[]
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xapp>>xsimpl>>
  first_x_assum $ irule_at Any>>xsimpl
QED

Quote cakeml:
  fun is_rup_arr lno fml carr b v hints =
  case prepare_rup carr b v of (carr',b') =>
  if unit_prop_arr lno fml carr' b' hints
  then b'
  else
    raise Fail (format_failure lno ("unit propagation did not prove RUP"))
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
        &(res = (T,(Clist',b')) ∧
          WORD8 b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        W8ARRAY Carrv' Clist' *
        &(Fail_exn e ∧ FST res = F))
    )
Proof
  rw[]>>
  xcf "is_rup_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  gvs[is_rup_list'_def]>>
  xmatch>>
  xlet_autop
  >- (
    xsimpl>>
    metis_tac[W8ARRAY_refl])>>
  xif
  >- (
    xvar>>xsimpl>>
    metis_tac[W8ARRAY_refl])>>
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
        &(is_rup_list fmlls Clist b v ls = (T,(Clist',b')) ∧
          WORD8 b' res))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
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

