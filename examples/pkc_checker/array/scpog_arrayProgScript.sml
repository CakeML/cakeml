(*
  This refines scpog_list to use arrays
*)
open preamble basis UnsafeProofTheory cnf_scpogTheory scpog_listTheory scpog_parsingTheory blastLib;

val _ = new_theory "scpog_arrayProg"

val _ = diminish_srw_ss ["ABBREV"]

(* TODO: move *)
Theorem ALL_DISTINCT_MAP_FST_toSortedAList:
  ALL_DISTINCT (MAP FST (toSortedAList t))
Proof
  `SORTED $< (MAP FST (toSortedAList t))` by
    simp[SORTED_toSortedAList]>>
  pop_assum mp_tac>>
  match_mp_tac SORTED_ALL_DISTINCT>>
  simp[irreflexive_def]
QED

Theorem MAP_FST_enumerate:
  MAP FST (enumerate k ls) = GENLIST ($+ k) (LENGTH ls)
Proof
  rw[LIST_EQ_REWRITE,LENGTH_enumerate]>>
  simp[EL_MAP,LENGTH_enumerate,EL_enumerate]
QED

Theorem ALL_DISTINCT_MAP_FST_enumerate:
  ALL_DISTINCT (MAP FST (enumerate k ls))
Proof
  simp[MAP_FST_enumerate,ALL_DISTINCT_GENLIST]
QED

(* replace in miscTheory *)
Theorem MEM_enumerate_IMP:
  ∀ls k.
  MEM (i,e) (enumerate k ls) ⇒ MEM e ls
Proof
  Induct_on`ls`>>fs[miscTheory.enumerate_def]>>rw[]>>
  metis_tac[]
QED

Theorem ALOOKUP_enumerate:
  ∀ls k x.
  ALOOKUP (enumerate k ls) x =
  if k ≤ x ∧ x < LENGTH ls + k then SOME (EL (x-k) ls) else NONE
Proof
  Induct>>rw[miscTheory.enumerate_def]>>
  `x-k = SUC(x-(k+1))` by DECIDE_TAC>>
  simp[]
QED

val _ = translation_extends"UnsafeProg";

(* Pure translation of SCPOG checker *)
val _ = register_type``:scpstep``;
val _ = register_type``:'a spt``;

val _ = translate insert_def;

(* TODO: make sure these get inlined! *)
val _ = translate w8z_def;
val _ = translate w8o_def;
val _ = translate index_def;

val w8z_v_thm = fetch "-" "w8z_v_thm";
val w8o_v_thm = fetch "-" "w8o_v_thm";

val index_side_def = fetch "-" "index_side_def"

val index_side = Q.prove(`
  !x. index_side x ⇔ T`,
  simp[index_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

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

Definition eq_w8o_def:
  eq_w8o v ⇔ v = w8o
End

val _ = translate (eq_w8o_def |> SIMP_RULE std_ss [w8o_def]);

val every_one_arr = process_topdecs`
  fun every_one_arr carr cs =
  case cs of [] => True
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then every_one_arr carr cs
    else False` |> append_prog

Definition format_failure_def:
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val _ = translate format_failure_def;

Definition unwrap_TYPE_def:
  unwrap_TYPE P x y =
  ∃z. x = SOME z ∧ P z y
End

val delete_literals_sing_arr_def = process_topdecs`
  fun delete_literals_sing_arr lno i carr cs =
  case cs of
    [] => 0
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then
      delete_literals_sing_arr lno i carr cs
    else
      if every_one_arr carr cs then ~c
      else raise Fail (format_failure lno ("clause at index not empty or singleton after reduction: "  ^ Int.toString i))` |> append_prog

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Theorem update_resize_LUPDATE[simp]:
  LENGTH Clist > index h ⇒
  update_resize Clist w8z v (index h) = LUPDATE v (index h) Clist
Proof
  rw[update_resize_def]
QED

Theorem every_one_arr_spec:
  ∀ls lsv.
  (LIST_TYPE INT) ls lsv ∧
  EVERY ($> (LENGTH Clist) o index) ls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_one_arr" (get_ml_prog_state()))
    [Carrv; lsv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
      W8ARRAY Carrv Clist *
      &BOOL (EVERY (λi. any_el (index i) Clist w8z = w8o) ls) v)
Proof
  Induct>>rw[]>>
  xcf "every_one_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >-
    (xmatch>>xcon>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  fs[eq_w8o_def,any_el_ALT]>>
  xif
  >-
    (xapp>>xsimpl)>>
  xcon>> xsimpl
QED

val raise_tac =
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[unwrap_TYPE_def,Fail_exn_def]>>
  metis_tac[];

Theorem delete_literals_sing_arr_spec:
  ∀ls lsv lno lnov i iv.
  NUM lno lnov ∧
  NUM i iv ∧
  (LIST_TYPE INT) ls lsv ∧
  EVERY ($> (LENGTH Clist) o index) ls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_literals_sing_arr" (get_ml_prog_state()))
    [lnov; iv; Carrv; lsv]
    (W8ARRAY Carrv Clist)
    (POSTve
      (λv. W8ARRAY Carrv Clist *
        &unwrap_TYPE INT (delete_literals_sing_list Clist ls) v)
      (λe. &(Fail_exn e ∧ delete_literals_sing_list Clist ls = NONE)))
Proof
  Induct>>simp[delete_literals_sing_list_def]>>
  rpt strip_tac>>
  xcf "delete_literals_sing_arr" (get_ml_prog_state ())
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>>
    xlit
    >- (
      simp[unwrap_TYPE_def]>>
      xsimpl)>>
    xsimpl)>>
  fs[LIST_TYPE_def]>> xmatch>>
  rpt xlet_autop >>
  fs[eq_w8o_def,any_el_ALT]>>
  xif
  >- (
    xapp>>xsimpl>>
    metis_tac[])>>
  xlet_auto>>
  gvs[any_el_ALT]>>
  xif
  >- (
    xapp>>xsimpl>>simp[unwrap_TYPE_def]>>
    metis_tac[])>>
  IF_CASES_TAC>- metis_tac[NOT_EVERY]>>
  raise_tac
QED

val is_rup_arr_aux = process_topdecs`
  fun is_rup_arr_aux lno pred fml ls c carr =
    case ls of
      [] =>
        raise Fail (format_failure lno
          ("failed to derive clause by RUP"))
    | (i::is) =>
    if Array.length fml <= i then
      raise Fail (format_failure lno
        ("no clause at index: " ^ Int.toString i))
    else
    case Unsafe.sub fml i of
      None => raise Fail (format_failure lno
        ("no clause at index (maybe deleted): " ^ Int.toString i))
    | Some ct =>
      if pred ct then
        let val nl = delete_literals_sing_arr lno i carr (fst ct) in
        if nl = 0 then c
        else
          (Unsafe.w8update carr (index nl) w8o;
          is_rup_arr_aux lno pred fml is (nl::c) carr)
        end
      else
        raise Fail (format_failure lno
          ("wrong clause type at index: " ^ Int.toString i))
         ` |> append_prog

(* For every literal in every clause and their negations,
  the index is bounded above by n *)
Definition bounded_fml_def:
  bounded_fml n fmlls ⇔
  EVERY (λCopt.
    case Copt of
      NONE => T
    | SOME (C,t) => EVERY ($> n o index) C ∧ EVERY ($> n o index o $~) C
    ) fmlls
End

Theorem delete_literals_sing_list_MEM:
  ∀C.
  delete_literals_sing_list ls C = SOME x ∧ x ≠ 0
  ⇒
  MEM (-x) C
Proof
  Induct>>rw[delete_literals_sing_list_def] >> simp[] >>
  CCONTR_TAC >> fs [] >> rw []
QED

Overload "ctag_TYPE" = ``PAIR_TYPE (LIST_TYPE INT) NUM``
Overload "pred_TYPE" = ``ctag_TYPE --> BOOL``;

Theorem is_rup_arr_aux_spec:
  ∀ls lsv c cv fmlv fmlls fml Carrv Clist lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  pred_TYPE pred predv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr_aux" (get_ml_prog_state()))
    [lnov; predv; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &unwrap_TYPE ($= o SND)
          (is_rup_list_aux pred fmlls ls c Clist) Clist'
        ) *
        &unwrap_TYPE
          (LIST_TYPE INT o FST)
          (is_rup_list_aux pred fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ is_rup_list_aux pred fmlls ls c Clist = NONE)))
Proof
  Induct>>
  rw[]>>
  xcf "is_rup_arr_aux" (get_ml_prog_state ())>>
  simp[is_rup_list_aux_def]
  >- (
    fs[LIST_TYPE_def]>> xmatch>>
    raise_tac)>>
  fs[LIST_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    `any_el h fmlls NONE = NONE` by (
      simp[any_el_ALT]>>
      drule LIST_REL_LENGTH>>
      gvs[])>>
    raise_tac>>
    simp[unwrap_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  `OPTION_TYPE ctag_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC
  >- (
    fs[any_el_ALT]>>
    reverse (Cases_on`EL h fmlls`)>-
      (fs[IS_SOME_DEF]>>
      drule LIST_REL_LENGTH>>
      gvs[])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    raise_tac)>>
  fs[any_el_ALT,OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  reverse xif
  >- raise_tac>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` mp_tac)>>simp[]>>
    TOP_CASE_TAC>>rw[])
  >- (
    xsimpl>>rw[]>> simp[]>>
    metis_tac[])>>
  fs[unwrap_TYPE_def]>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  rpt xlet_autop>>
  `index z < LENGTH Clist ∧ WORD8 w8o w8o_v` by (
    fs[w8o_v_thm]>>
    fs[bounded_fml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` assume_tac)>>rfs[AllCasePreds()]>>
    drule delete_literals_sing_list_MEM>>fs[]>>
    simp[MEM_EL]>>
    rw[]>>
    pop_assum mp_tac>>
    rpt (first_x_assum drule)>>
    rw[]>>
    pop_assum sym_sub_tac>>fs[])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  qexists_tac`fmlls`>>qexists_tac`z::c`>>
  simp[LIST_TYPE_def]>>
  metis_tac[]
QED

val set_array = process_topdecs`
  fun set_array carr v cs =
  case cs of [] => ()
  | (c::cs) =>
    (Unsafe.w8update carr (index c) v;
    set_array carr v cs)` |> append_prog

Theorem set_array_spec:
  ∀c cv Carrv Clist.
  (LIST_TYPE INT) c cv ∧
  WORD8 v vv ∧
  EVERY ($> (LENGTH Clist) o index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "set_array" (get_ml_prog_state()))
    [Carrv; vv; cv]
    (W8ARRAY Carrv Clist)
    (POSTv uv.
          W8ARRAY Carrv (set_list Clist v c))
Proof
  Induct>>
  rw[]>>
  xcf "set_array" (get_ml_prog_state ())>>
  rw[set_list_def]>>
  fs[LIST_TYPE_def]
  >- (xmatch>>xcon>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xapp>>
  xsimpl
QED

val is_rup_arr = process_topdecs`
  fun is_rup_arr lno pred fml ls c carr =
    (set_array carr w8o c;
    set_array carr w8z (is_rup_arr_aux lno pred fml ls c carr);
    carr)`
    |> append_prog

Theorem LENGTH_set_list_bound[simp]:
  ∀c Clist.
  EVERY ($> (LENGTH Clist) ∘ index) c ⇒
  LENGTH (set_list Clist v c) = LENGTH Clist
Proof
  Induct>>simp[set_list_def]
QED

(* a version of this is true even if x, h are not bounded *)
Theorem update_resize_twice:
  index x < LENGTH Clist ∧ index h < LENGTH Clist ⇒
  update_resize (update_resize Clist w8z w8o (index x)) w8z w8o (index h) =
  update_resize (update_resize Clist w8z w8o (index h)) w8z w8o (index x)
Proof
  rw[update_resize_def]>>
  Cases_on`x=h`>>simp[]>>
  `index x ≠ index h` by metis_tac[index_11]>>
  metis_tac[LUPDATE_commutes]
QED

Theorem set_list_update_resize:
  ∀c Clist.
  index x < LENGTH Clist ∧ EVERY ($> (LENGTH Clist) ∘ index) c ⇒
  set_list Clist w8o (x::c) =
  update_resize (set_list Clist w8o c) w8z w8o (index x)
Proof
  Induct>>rw[]>>fs[set_list_def]>>
  Cases_on`x=h`>>simp[]
  >-
    (first_x_assum (qspec_then` LUPDATE w8o (index h) Clist` mp_tac)>>
    simp[])
  >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[LUPDATE_commutes]>>
  simp[index_11]
QED

Theorem is_rup_list_aux_length_bound:
  ∀ls c Clist.
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c ∧
  is_rup_list_aux pred fmlls ls c (set_list Clist w8o c) = SOME(d,r) ⇒
    Abbrev (r = set_list Clist w8o d ∧
    LENGTH r = LENGTH Clist ∧
    EVERY ($> (LENGTH Clist) ∘ index) d)
Proof
  Induct>>rw[is_rup_list_aux_def,set_list_def]>>simp[]>>
  gvs[AllCaseEqs()]
  >-
    simp[markerTheory.Abbrev_def]>>
  first_x_assum irule>>
  drule delete_literals_sing_list_MEM>> simp[]>>
  strip_tac>>
  fs[bounded_fml_def,EVERY_MEM,any_el_ALT]>>
  first_x_assum(qspec_then`EL h fmlls` mp_tac)>>
  impl_tac>- (
    `h < LENGTH fmlls` by fs[]>>
    metis_tac[MEM_EL])>>
  simp[]>>strip_tac>>
  qexists_tac`nl::c`>>
  gvs[AllCasePreds()]>>
  CONJ_TAC >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[set_list_update_resize]>>
    simp[EVERY_MEM]>>
    gvs[AllCasePreds()]>>
    pop_assum drule>>
    simp[]) >>
  simp[]>>
  rw[]
  >- (
    pop_assum drule>>
    simp[])>>
  metis_tac[]
QED

Theorem is_rup_arr_spec:
  ∀ls lsv c cv fmlv fmlls Carrv Clist lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  pred_TYPE pred predv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; predv; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(unwrap_TYPE $=
            (is_rup_list pred fmlls ls c Clist) Clist' ∧
            LENGTH Clist = LENGTH Clist')
          ) *
        &unwrap_TYPE
          (λv w. T)
          (is_rup_list pred fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ is_rup_list pred fmlls ls c Clist = NONE)))
Proof
  rw[]>>
  xcf "is_rup_arr" (get_ml_prog_state ())>>
  `WORD8 w8z w8z_v ∧ WORD8 w8o w8o_v` by
    simp[w8z_v_thm,w8o_v_thm]>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>fs[])
  >- (
    simp[is_rup_list_def]>>
    xsimpl>>
    rw[]>>simp[]>>
    metis_tac[])>>
  fs[unwrap_TYPE_def]>>
  simp[is_rup_list_def]>>
  rw[]>>fs[]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  drule is_rup_list_aux_length_bound>>
  rpt (disch_then drule)>>
  simp[markerTheory.Abbrev_def]>>
  strip_tac>>
  xlet_autop>>
  xvar>>xsimpl
QED

val _ = translate list_max_def;
val _ = translate list_max_index_def;

(* bump up the length to a large number *)
val resize_carr = process_topdecs`
  fun resize_carr c carr =
  let val lm = list_max_index c in
    if Word8Array.length carr <= lm
    then Word8Array.array (2*lm) w8z
    else carr
  end` |> append_prog

Theorem resize_carr_spec:
  (LIST_TYPE INT) c cv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_carr" (get_ml_prog_state()))
    [cv; Carrv]
    (W8ARRAY Carrv Clist)
    (POSTv carrv.
      W8ARRAY carrv (resize_Clist c Clist))
Proof
  rw[]>>
  xcf "resize_carr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  simp[resize_Clist_def]>>xif
  >- (
    xlet_autop>>xapp>>
    xsimpl>>
    metis_tac[w8z_v_thm])>>
  xvar>>
  xsimpl
QED

val insert_one_arr = process_topdecs`
  fun insert_one_arr lno tag fml i c =
  case Array.lookup fml None i of
    None =>
      Array.updateResize fml None i (Some (c,tag))
  | Some cc =>
    raise Fail (format_failure lno "cannot overwrite existing clause at id: "^ Int.toString i)` |> append_prog;

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

Theorem insert_one_arr_spec:
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  NUM tag tagv ∧
  (LIST_TYPE INT) c cv ∧
  NUM i iv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "insert_one_arr" (get_ml_prog_state()))
    [lnov; tagv; fmlv; iv; cv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmllsv'.
        ARRAY v fmllsv' *
        &(case insert_one_list tag fmlls i c of NONE => F
        | SOME fmlls' =>
          LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          insert_one_list tag fmlls i c  = NONE)))
Proof
  rw[insert_one_list_def]>>
  xcf"insert_one_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE ctag_TYPE (any_el i fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  reverse (Cases_on`any_el i fmlls NONE`)>>gvs[OPTION_TYPE_def]>>
  xmatch
  >- raise_tac>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  irule_at Any LIST_REL_update_resize>>
  gvs[OPTION_TYPE_def,PAIR_TYPE_def]
QED

val insert_list_arr = process_topdecs`
  fun insert_list_arr lno tag fml i ls =
  case ls of [] => fml
  | c::cs =>
    insert_list_arr lno tag (insert_one_arr lno tag fml i c) (i+1) cs` |> append_prog;

Theorem ARRAY_refl:
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Theorem insert_list_arr_spec:
  ∀ls lsv i iv fmlls fmllsv fmlv.
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  NUM tag tagv ∧
  LIST_TYPE (LIST_TYPE INT) ls lsv ∧
  NUM i iv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "insert_list_arr" (get_ml_prog_state()))
    [lnov; tagv; fmlv; iv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmllsv'.
        ARRAY v fmllsv' *
        &(case insert_list_list tag fmlls i ls of NONE => F
        | SOME fmlls' =>
          LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'))
      (λe.
        SEP_EXISTS fmlv fmllsv.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          insert_list_list tag fmlls i ls = NONE)))
Proof
  Induct>>
  rw[insert_list_list_def]>>
  xcf"insert_list_arr"(get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop
  >-(
    xsimpl>>
    rw[]>>
    metis_tac[ARRAY_refl])>>
  gvs[AllCasePreds()]>>
  xapp>>xsimpl
QED

val _ = register_type``:scpog_conf``;
val _ = register_type``:prob_conf``;

val res = translate var_lit_def;
val res = translate lookup_def;
val res = translate is_data_var_def;
val res = translate is_data_ext_lit_run_def;
val res = translate declare_root_def;

val res = translate is_structural_def;
val res = translate is_forward_def;
val res = translate is_strfwd_def;

Definition every_not_is_fresh_def:
  every_not_is_fresh pc sc c =
    EVERY (λi. ¬is_fresh pc sc (var_lit i)) c
End

val res = translate is_fresh_def;
val res = translate every_not_is_fresh_def;

val delete_arr = process_topdecs`
  fun delete_arr i fml =
    if Array.length fml <= i then ()
    else
      (Unsafe.update fml i None)` |> append_prog

Theorem LUPDATE_outside:
  ∀ls n.
  LENGTH ls ≤ n ⇒
  LUPDATE x n ls = ls
Proof
  Induct>>rw[LUPDATE_DEF]
QED

Theorem delete_arr_spec:
  NUM i iv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_arr" (get_ml_prog_state()))
    [iv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      ARRAY fmlv (LUPDATE (Conv (SOME (TypeStamp "None" 2)) []) i fmllsv))
Proof
  rw[]>>
  xcf "delete_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xif>- (
    xcon>>xsimpl>>
    DEP_REWRITE_TAC[LUPDATE_outside]>>
    simp[])>>
  xlet_auto >- (xcon>>xsimpl)>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

val res = translate is_adel_def;

Definition is_adel_sc_def:
  is_adel_sc sc = is_adel sc.root
End

val res = translate is_adel_sc_def;

val arb_delete_arr = process_topdecs`
  fun arb_delete_arr lno sc ls fml =
    case ls of [] => ()
  | (i::is) =>
    case Array.lookup fml None i of
    None =>
      raise Fail (format_failure lno "missing id for arbitrary deletion: "^ Int.toString i)
  | Some ctag =>
    if is_adel_sc sc ctag
    then
      (delete_arr i fml; arb_delete_arr lno sc is fml)
    else
    raise Fail (format_failure lno "invalid arbitrary deletion at id: "^ Int.toString i)` |> append_prog;

Theorem arb_delete_arr_spec:
  ∀ls lsv fmlls fmlv fmllsv.
  NUM lno lnov ∧
  CNF_SCPOG_SCPOG_CONF_TYPE sc scv ∧
  LIST_TYPE NUM ls lsv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "arb_delete_arr" (get_ml_prog_state()))
    [lnov; scv; lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmllsv'.
        ARRAY fmlv fmllsv' *
        &(UNIT_TYPE () v ∧
        case arb_delete_list sc ls fmlls of NONE => F
        | SOME fmlls' =>
          LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'))
      (λe.
        SEP_EXISTS fmllsv'.
        ARRAY fmlv fmllsv' *
        & (Fail_exn e ∧
          arb_delete_list sc ls fmlls = NONE)))
Proof
  Induct>>rw[arb_delete_list_def]>>
  xcf "arb_delete_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>xmatch
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE ctag_TYPE (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  gvs[OPTION_TYPE_SPLIT]>>xmatch
  >- raise_tac>>
  rpt xlet_autop>>
  gvs[is_adel_sc_def]>>
  reverse xif
  >- raise_tac>>
  xlet_autop>>
  xapp>>xsimpl>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[OPTION_TYPE_def]
QED

Definition mk_backward_def:
  mk_backward sc = is_backward sc.root
End

val res = translate is_root_def;
val res = translate is_backward_def;
val res = translate mk_backward_def;
val res = translate strfwd_tag_def;

Definition is_input_tag_def:
  is_input_tag tag = (tag = input_tag)
End

val res = translate is_input_tag_def;

val res = translate check_pro_def;
val res = translate FOLDL;
val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate inter_def;
val res = translate union_def;
val res = translate big_disjoint_union_def;
val res = translate get_node_vars_def;
val res = translate mk_Ev_disj_def;
val res = translate mk_sko_def;
val res = translate mk_pro_def;
val res = translate declare_pro_def;

val res = translate check_sum_def;
val res = translate mk_sum_def;
val res = translate big_union_def;
val res = translate mk_Ev_def;
val res = translate declare_sum_def;

val res = translate is_proj_lit_run_def;
val res = translate check_sko_def;
val res = translate declare_sko_def;

Definition mk_cl_def:
  mk_cl l1 (l2:int) = [-l1;-l2]
End
val res = translate mk_cl_def;

val check_scpstep_arr = process_topdecs`
  fun check_scpstep_arr lno scpstep pc fml sc carr =
  case scpstep of
    Skip => (fml,sc,carr)
  | Root l =>
      (case declare_root pc sc l of
        None => raise Fail (format_failure lno "invalid root declaration")
      | Some sc' => (fml,sc',carr))
  | Rupadd b n c i0 =>
    (let val carr = resize_carr c carr
        val u = is_rup_arr lno (is_strfwd b) fml i0 c carr in
      if every_not_is_fresh pc sc c
      then
        (insert_one_arr lno (strfwd_tag b) fml n c, sc, carr)
      else raise Fail (format_failure lno "clause has fresh variable")
    end)
  | Rupdel n i0 =>
    (case Array.lookup fml None n of
      None => raise Fail (format_failure lno "invalid RUP deletion")
    | Some (c,tag) =>
      if is_input_tag tag then
        let
          val u1 = delete_arr n fml
          val u2 = is_rup_arr lno (mk_backward sc) fml i0 c carr in
          (fml, sc, carr)
        end
      else raise Fail (format_failure lno "invalid deletion tag for clause"))
  | Arbdel ls =>
    (arb_delete_arr lno sc ls fml; (fml,sc,carr))
  | Declpro n v ls =>
    (case declare_pro pc sc v ls of
      Some (cs,sc') =>
        (insert_list_arr lno 1 fml n cs, sc', carr)
    | _ =>
      raise Fail (format_failure lno "Product node freshness/variable checks failed"))
  | Declsum n v l1 l2 i0 =>
    (let
      val c = mk_cl l1 l2
      val carr = resize_carr c carr
      val u = is_rup_arr lno is_structural fml i0 c carr in
      (case declare_sum pc sc v l1 l2 of
        Some (cs,sc') =>
          (insert_list_arr lno 1 fml n cs,sc',carr)
      | _ =>
        raise Fail (format_failure lno "Sum node freshness/variable checks failed"))
    end)
  | Declsko n v ls =>
    (case declare_sko pc sc v ls of
      Some (cT,csF,sc') =>
        (insert_list_arr lno 5 (insert_one_arr lno 0 fml n cT) (n+1) csF, sc',carr)
    | _ =>
      raise Fail (format_failure lno "Skolem node freshness/variable checks failed"))`
  |> append_prog;

val CNF_SCPOG_SCPSTEP_TYPE_def = fetch "-" "CNF_SCPOG_SCPSTEP_TYPE_def";

Theorem OPTION_TYPE_SPLIT:
  OPTION_TYPE a x v ⇔
  (x = NONE ∧ v = Conv (SOME (TypeStamp "None" 2)) []) ∨
  (∃y vv. x = SOME y ∧ v = Conv (SOME (TypeStamp "Some" 2)) [vv] ∧ a y vv)
Proof
  Cases_on`x`>>rw[OPTION_TYPE_def]
QED

Theorem PAIR_TYPE_SPLIT:
  PAIR_TYPE a b x v ⇔
  ∃x1 x2 v1 v2. x = (x1,x2) ∧ v = Conv NONE [v1; v2] ∧ a x1 v1 ∧ b x2 v2
Proof
  Cases_on`x`>>EVAL_TAC>>rw[]
QED

Theorem check_scpstep_arr_spec:
  NUM lno lnov ∧
  CNF_SCPOG_SCPSTEP_TYPE scpstep scpstepv ∧
  CNF_SCPOG_PROB_CONF_TYPE pc pcv ∧
  CNF_SCPOG_SCPOG_CONF_TYPE sc scv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_scpstep_arr" (get_ml_prog_state()))
    [lnov; scpstepv; pcv; fmlv; scv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3.
          &(v = Conv NONE [v1; v2; v3]) *
          (* v1 points to the array
             v2 is SCP config
             v3 points to the byte array
          *)
          (SEP_EXISTS fmllsv' clist'.
            ARRAY v1 fmllsv' *
            W8ARRAY v3 clist' *
            &(
            case check_scpstep_list scpstep pc fmlls sc Clist of
              NONE => F
            | SOME (fmlls', sc' , Clist') =>
                bounded_fml (LENGTH Clist') fmlls' ∧
                LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv' ∧
                Clist' = clist' ∧
                LENGTH Clist ≤ LENGTH Clist'
            ))
      )
      (λe.
        SEP_EXISTS fmllsv'.
        ARRAY fmlv fmllsv' *
        &(Fail_exn e ∧
        check_scpstep_list scpstep pc fmlls sc Clist = NONE)))
Proof
  rw[check_scpstep_list_def]>>
  xcf "check_scpstep_arr" (get_ml_prog_state ())>>
  Cases_on`scpstep`>>fs[CNF_SCPOG_SCPSTEP_TYPE_def]
  >- ( (* Skip *)
    xmatch >>
    xcon>>xsimpl)
  >- ( (* Root *)
    xmatch>>
    xlet_autop>>
    gvs[OPTION_TYPE_SPLIT]
    >- (
      xmatch>>
      raise_tac)>>
    xmatch>>
    xcon>>xsimpl)
  >- ( (* RupAdd *)
    xmatch>>
    xlet_autop>>
    xlet`(POSTv f.
      W8ARRAY carrv (resize_Clist l Clist) * ARRAY fmlv fmllsv * &(pred_TYPE (is_strfwd b) f))`
    >- (
      assume_tac (fetch "-" "is_strfwd_v_thm" |> Q.GEN`a` |> Q.ISPEC `LIST_TYPE INT`)>>
      drule Arrow_IMP_app_basic>>
      disch_then drule>>
      simp[GSYM app_def]>>
      simp[cf_app_def,local_def,PULL_EXISTS]>>rw[]>>
      first_x_assum (irule_at (Pos (el 4)))>>
      xsimpl>>
      CONJ_TAC >-
        metis_tac[ml_monad_translatorBaseTheory.EMP_STAR_GC,ml_monad_translatorBaseTheory.H_STAR_GC_SAT_IMP]>>
      EVAL_TAC)>>
    xlet_auto
    >- (
      xsimpl>>
      cheat)
    >- xsimpl>>
    xlet_autop>>
    fs[unwrap_TYPE_def,every_not_is_fresh_def]>>
    reverse xif
    >- (
      `¬EVERY (λi. ¬is_fresh pc sc (var_lit i)) l` by metis_tac[NOT_EVERY,o_DEF]>>
      raise_tac)>>
    xlet_autop>>
    xlet`POSTve
      (λv.
           SEP_EXISTS fmllsv'.
             ARRAY v fmllsv' * W8ARRAY carrv Clist' *
             &case insert_one_list (strfwd_tag b) fmlls n l of
               NONE => F
             | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv')
      (λe.
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ insert_one_list (strfwd_tag b) fmlls n l = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      simp[])
    >- xsimpl>>
    gvs[AllCasePreds()]>>
    xcon>>xsimpl>>
    cheat)
  >- ( (* RupDel *)
    xmatch>>
    rpt xlet_autop>>
    `OPTION_TYPE ctag_TYPE (any_el n fmlls NONE) v'` by (
      rw[any_el_ALT]>>
      fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    gvs[OPTION_TYPE_SPLIT,PAIR_TYPE_SPLIT]>>xmatch
    >- raise_tac>>
    xlet_autop>>
    gvs[is_input_tag_def]>>
    reverse xif
    >- raise_tac>>
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`ARRAY fmlv fmllsv'`>>
    xlet`(POSTv f.
      (ARRAY fmlv fmllsv' * W8ARRAY Carrv Clist) * &(pred_TYPE (is_backward sc.root) f))`
    >- (
      assume_tac (fetch "-" "mk_backward_v_thm")>>
      drule Arrow_IMP_app_basic>>
      disch_then drule>>
      simp[GSYM app_def]>>
      simp[cf_app_def,local_def,PULL_EXISTS,mk_backward_def]>>rw[]>>
      first_x_assum (irule_at (Pos (el 4)))>>
      xsimpl>>
      CONJ_TAC >-
        metis_tac[ml_monad_translatorBaseTheory.EMP_STAR_GC,ml_monad_translatorBaseTheory.H_STAR_GC_SAT_IMP]>>
      EVAL_TAC)>>
    qmatch_goalsub_abbrev_tac`is_rup_list pred _ ls c Clist`>>
    `bounded_fml (LENGTH Clist) (LUPDATE NONE n fmlls)` by cheat>>
    `LIST_REL (OPTION_TYPE ctag_TYPE) (LUPDATE NONE n fmlls) fmllsv'` by cheat>>
    xlet`POSTve
            (λv.
                 ARRAY fmlv fmllsv' *
                 (SEP_EXISTS Clist'.
                    W8ARRAY Carrv Clist' *
                    &(unwrap_TYPE $= (is_rup_list pred (LUPDATE NONE n fmlls) ls c Clist)
                       Clist' ∧ LENGTH Clist = LENGTH Clist')) *
                 &unwrap_TYPE (λv w. T) (is_rup_list pred (LUPDATE NONE n fmlls) ls c Clist) v)
            (λe.
                 ARRAY fmlv fmllsv' *
                 &(Fail_exn e ∧ is_rup_list pred (LUPDATE NONE n fmlls) ls c Clist = NONE))`
    >- (
      xapp>>xsimpl>>
      cheat)
    >- xsimpl>>
    gvs[unwrap_TYPE_def]>>
    xcon>>xsimpl)
  >- (  (* ArbDel *)
    xmatch>>
    xlet`
      POSTve
        (λv.
             SEP_EXISTS fmllsv'.
               ARRAY fmlv fmllsv' * W8ARRAY Carrv Clist *
               &(UNIT_TYPE () v ∧
                case arb_delete_list sc l fmlls of
                  NONE => F
                | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'))
        (λe.
             SEP_EXISTS fmllsv'.
               ARRAY fmlv fmllsv' *
               &(Fail_exn e ∧ arb_delete_list sc l fmlls = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      simp[])
    >- xsimpl>>
    gvs[AllCasePreds()]>>xcon>>xsimpl>>
    cheat)
  >- ( (* DeclPro *)
    xmatch>>
    rpt xlet_autop>>
    gvs[OPTION_TYPE_SPLIT,PAIR_TYPE_SPLIT]>>
    xmatch
    >- raise_tac>>
    xlet`POSTve
      (λv.
           SEP_EXISTS fmllsv'.
             ARRAY v fmllsv' * W8ARRAY Carrv Clist *
             &case insert_list_list 1 fmlls n x1 of
               NONE => F
             | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv')
      (λe.
           SEP_EXISTS fmlv' fmllsv'.
             ARRAY fmlv' fmllsv' *
             &(Fail_exn e ∧ insert_list_list 1 fmlls n x1 = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      simp[]>>
      rw[]>>
      qexists_tac`x`>>qexists_tac`x'`>>xsimpl)
    >-
      cheat)>>
  cheat
QED

val _ = export_theory();
