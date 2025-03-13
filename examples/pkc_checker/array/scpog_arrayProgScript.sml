(*
  This refines scpog_list to use arrays
*)
open preamble basis UnsafeProofTheory cnf_scpogTheory scpog_listTheory lpr_parsingTheory scpog_parsingTheory blastLib;

val _ = new_theory "scpog_arrayProg"

val _ = diminish_srw_ss ["ABBREV"]

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
  (ARRAY fml fmllsv * W8ARRAY zerosv zeros ==>> ARRAY fml fmllsv * GC) ∧
  (W8ARRAY zerosv zeros * ARRAY fml fmllsv ==>> ARRAY fml fmllsv * GC) ∧
  (W8ARRAY zerosv zeros * ARRAY fml fmllsv ==>> ARRAY fml fmllsv * W8ARRAY zerosv zeros * GC)
Proof
  xsimpl
QED

val raise_tac =
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[unwrap_TYPE_def,Fail_exn_def]>>
  metis_tac[ARRAY_refl,W8ARRAY_refl,ARRAY_W8ARRAY_refl];

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

Definition check_imp_def:
  check_imp b b' = (b ⇒ b')
End

val res = translate check_imp_def;

val is_rup_arr_aux = process_topdecs`
  fun is_rup_arr_aux lno is_struct fml ls c carr =
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
    | Some (c',t) =>
      if check_imp is_struct t then
        let val nl = delete_literals_sing_arr lno i carr c' in
        if nl = 0 then c
        else
          (Unsafe.w8update carr (index nl) w8o;
          is_rup_arr_aux lno is_struct fml is (nl::c) carr)
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

Overload "ctag_TYPE" = ``PAIR_TYPE (LIST_TYPE INT) BOOL``

Theorem is_rup_arr_aux_spec:
  ∀ls lsv c cv fmlv fmlls fml Carrv Clist lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  BOOL b bv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr_aux" (get_ml_prog_state()))
    [lnov; bv; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &unwrap_TYPE ($= o SND)
          (is_rup_list_aux b fmlls ls c Clist) Clist'
        ) *
        &unwrap_TYPE
          (LIST_TYPE INT o FST)
          (is_rup_list_aux b fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ is_rup_list_aux b fmlls ls c Clist = NONE)))
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
  TOP_CASE_TAC>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[check_imp_def]>>
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
  fun is_rup_arr lno is_struct fml ls c carr =
    (set_array carr w8o c;
    set_array carr w8z (is_rup_arr_aux lno is_struct fml ls c carr);
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
  is_rup_list_aux b fmlls ls c (set_list Clist w8o c) = SOME(d,r) ⇒
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
  BOOL b bv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; bv; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(unwrap_TYPE $=
            (is_rup_list b fmlls ls c Clist) Clist' ∧
            LENGTH Clist = LENGTH Clist')
          ) *
        &unwrap_TYPE
          (λv w. T)
          (is_rup_list b fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ is_rup_list b fmlls ls c Clist = NONE)))
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
  BOOL tag tagv ∧
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

Theorem insert_list_arr_spec:
  ∀ls lsv i iv fmlls fmllsv fmlv.
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  BOOL tag tagv ∧
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

val res = translate declare_root_def;

Definition every_not_is_fresh_def:
  every_not_is_fresh pc sc c =
    EVERY (λi. ¬is_fresh pc sc (var_lit i)) c
End

val res = translate lookup_def;
val res = translate is_fresh_def;
val res = translate var_lit_def;
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

val arb_delete_arr = process_topdecs`
  fun arb_delete_arr lno nc ls fml =
    case ls of [] => ()
  | (i::is) =>
  if i <= nc then
      raise Fail (format_failure lno "unable to delete an input clause index: "^ Int.toString i)
  else
  case Array.lookup fml None i of
    None =>
      raise Fail (format_failure lno "missing id for arbitrary deletion: "^ Int.toString i)
  | Some (c,tag) =>
    if tag
    then
     raise Fail (format_failure lno "invalid arbitrary deletion of structural clause at id: "^ Int.toString i)
    else
      (delete_arr i fml; arb_delete_arr lno nc is fml)
    ` |> append_prog;

Theorem OPTION_TYPE_SPLIT:
  OPTION_TYPE a x v ⇔
  (x = NONE ∧ v = Conv (SOME (TypeStamp "None" 2)) []) ∨
  (∃y vv. x = SOME y ∧ v = Conv (SOME (TypeStamp "Some" 2)) [vv] ∧ a y vv)
Proof
  Cases_on`x`>>rw[OPTION_TYPE_def]
QED

Theorem arb_delete_arr_spec:
  ∀ls lsv fmlls fmlv fmllsv.
  NUM lno lnov ∧
  NUM nc ncv ∧
  LIST_TYPE NUM ls lsv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "arb_delete_arr" (get_ml_prog_state()))
    [lnov; ncv; lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmllsv'.
        ARRAY fmlv fmllsv' *
        &(UNIT_TYPE () v ∧
        case arb_delete_list nc ls fmlls of NONE => F
        | SOME fmlls' =>
          LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'))
      (λe.
        SEP_EXISTS fmllsv'.
        ARRAY fmlv fmllsv' *
        & (Fail_exn e ∧
          arb_delete_list nc ls fmlls = NONE)))
Proof
  Induct>>rw[arb_delete_list_def]>>
  xcf "arb_delete_arr" (get_ml_prog_state ())>>
  gvs[LIST_TYPE_def]>>xmatch
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xif >> instantiate
  >- raise_tac>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE ctag_TYPE (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  gvs[OPTION_TYPE_SPLIT]
  >- (
    xmatch>>
    raise_tac)>>
  Cases_on`y`>>gvs[PAIR_TYPE_def]>>xmatch>>
  xif
  >- raise_tac>>
  xlet_autop>>
  xapp>>xsimpl>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[OPTION_TYPE_def]
QED

val res = translate is_data_var_def;
val res = translate is_data_ext_lit_run_def;
val res = translate check_pro_def;

val res = translate FOLDL;

(*
val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate inter_def;
val res = translate union_def;
val res = translate big_disjoint_union_def;
val res = translate get_node_vars_def;
val res = translate mk_Ev_disj_def; *)

val res = translate mk_sko_def;
val res = translate mk_pro_def;
val res = translate declare_pro_def;

val res = translate check_sum_def;
val res = translate mk_sum_def;

(*
val res = translate big_union_def;
val res = translate mk_Ev_def; *)

val res = translate declare_sum_def;

val res = translate is_proj_lit_run_def;
val res = translate check_sko_def;
val res = translate declare_sko_def;

Definition mk_cl_def:
  mk_cl l1 (l2:int) = [-l1;-l2]
End

val res = translate mk_cl_def;

Definition get_nc_def:
  get_nc pc = pc.nc
End

val res = translate get_nc_def;

val check_scpstep_arr = process_topdecs`
  fun check_scpstep_arr lno scpstep pc fml sc carr =
  case scpstep of
    Skip => (fml,sc,carr)
  | Root l =>
      (case declare_root sc l of
        None => raise Fail (format_failure lno "invalid root declaration")
      | Some sc' => (fml,sc',carr))
  | Rupadd b n c i0 =>
    (let val carr = resize_carr c carr
        val u = is_rup_arr lno b fml i0 c carr in
      if every_not_is_fresh pc sc c
      then
        (insert_one_arr lno b fml n c, sc, carr)
      else raise Fail (format_failure lno "clause has fresh variable")
    end)
  | Arbdel ls =>
    (arb_delete_arr lno (get_nc pc) ls fml; (fml,sc,carr))
  | Declpro n v ls =>
    (case declare_pro pc sc v ls of
      Some (cs,sc') =>
        (insert_list_arr lno True fml n cs, sc', carr)
    | _ =>
      raise Fail (format_failure lno "Product node freshness/variable checks failed"))
  | Declsum n v l1 l2 i0 =>
    (let
      val c = mk_cl l1 l2
      val carr = resize_carr c carr
      val u = is_rup_arr lno True fml i0 c carr in
      (case declare_sum pc sc v l1 l2 of
        Some (cs,sc') =>
          (insert_list_arr lno True fml n cs,sc',carr)
      | _ =>
        raise Fail (format_failure lno "Sum node freshness/variable checks failed"))
    end)
  | Declsko n v ls =>
    (case declare_sko pc sc v ls of
      Some (cT,sc') =>
        (insert_one_arr lno True fml n cT, sc',carr)
    | _ =>
      raise Fail (format_failure lno "Skolem node freshness/variable checks failed"))`
  |> append_prog;

val CNF_SCPOG_SCPSTEP_TYPE_def = fetch "-" "CNF_SCPOG_SCPSTEP_TYPE_def";

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
                CNF_SCPOG_SCPOG_CONF_TYPE sc' v2 ∧
                Clist' = clist' ∧
                LENGTH Clist ≤ LENGTH Clist'
            ))
      )
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
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
    xlet_auto
    >- (
      xsimpl>>
      cheat)
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    xlet_autop>>
    fs[unwrap_TYPE_def,every_not_is_fresh_def]>>
    reverse xif
    >- (
      `¬EVERY (λi. ¬is_fresh pc sc (var_lit i)) l` by metis_tac[NOT_EVERY,o_DEF]>>
      raise_tac)>>
    xlet`POSTve
      (λv.
           SEP_EXISTS fmllsv'.
             ARRAY v fmllsv' * W8ARRAY carrv Clist' *
             &case insert_one_list b fmlls n l of
               NONE => F
             | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv')
      (λe.
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ insert_one_list b fmlls n l = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      simp[])
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    gvs[AllCasePreds()]>>
    xcon>>xsimpl>>
    cheat)
  >- (  (* ArbDel *)
    xmatch>>
    xlet_autop>>
    xlet`
      POSTve
        (λv.
             SEP_EXISTS fmllsv'.
               ARRAY fmlv fmllsv' * W8ARRAY Carrv Clist *
               &(UNIT_TYPE () v ∧
                case arb_delete_list pc.nc l fmlls of
                  NONE => F
                | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'))
        (λe.
             SEP_EXISTS fmllsv'.
               ARRAY fmlv fmllsv' *
               &(Fail_exn e ∧ arb_delete_list pc.nc l fmlls = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt (first_x_assum (irule_at Any))>>
      gvs[get_nc_def])
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    gvs[AllCasePreds()]>>xcon>>xsimpl>>
    cheat)
  >- ( (* DeclPro *)
    xmatch>>
    rpt xlet_autop>>
    gvs[OPTION_TYPE_SPLIT,PAIR_TYPE_SPLIT]>>
    xmatch
    >- raise_tac>>
    xlet_autop>>
    xlet`POSTve
      (λv.
           SEP_EXISTS fmllsv'.
             ARRAY v fmllsv' * W8ARRAY Carrv Clist *
             &case insert_list_list T fmlls n x1 of
               NONE => F
             | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv')
      (λe.
           SEP_EXISTS fmlv' fmllsv'.
             ARRAY fmlv' fmllsv' *
             &(Fail_exn e ∧ insert_list_list T fmlls n x1 = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      qexists_tac`T`>>
      simp[]>>
      rw[]
      >- EVAL_TAC>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- xsimpl>>
    gvs[AllCasePreds()]>>
    xcon>>xsimpl>>
    cheat)
  >- ( (* DeclSum *)
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xlet`POSTv v. W8ARRAY carrv (resize_Clist (mk_cl i i0) Clist) * ARRAY fmlv fmllsv * &BOOL T v`
    >-
      (xcon>>xsimpl)>>
    gvs[mk_cl_def]>>
    xlet_auto
    >- (
      xsimpl>>
      cheat)
    >- (
      xsimpl>>rw[]>>
      metis_tac[ARRAY_refl])>>
    gvs[unwrap_TYPE_def]>>
    xlet_autop>>
    gvs[OPTION_TYPE_SPLIT,PAIR_TYPE_SPLIT]>>xmatch
    >-
      raise_tac>>
    xlet_autop>>
    xlet`POSTve
      (λv.
           SEP_EXISTS fmllsv'.
             ARRAY v fmllsv' * W8ARRAY carrv Clist' *
             &case insert_list_list T fmlls n x1 of
               NONE => F
             | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv')
      (λe.
           SEP_EXISTS fmlv' fmllsv'.
             ARRAY fmlv' fmllsv' *
             &(Fail_exn e ∧ insert_list_list T fmlls n x1 = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      qexists_tac`T`>>simp[]>>
      rw[]
      >- EVAL_TAC>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >-
      (xsimpl>>metis_tac[ARRAY_refl])>>
    gvs[AllCasePreds()]>>
    xcon>>xsimpl>>
    cheat)
  >- ( (* DeclSko *)
    xmatch>>
    rpt xlet_autop>>
    gvs[OPTION_TYPE_SPLIT,PAIR_TYPE_SPLIT]>>
    xmatch
    >- raise_tac>>
    xlet_autop>>
    xlet`POSTve
      (λv.
           SEP_EXISTS fmllsv'.
             ARRAY v fmllsv' * W8ARRAY Carrv Clist *
             &case insert_one_list T fmlls n x1 of
               NONE => F
             | SOME fmlls' => LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv')
      (λe.
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ insert_one_list T fmlls n x1 = NONE))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      qexists_tac`T`>>
      simp[]>>
      EVAL_TAC)
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    gvs[AllCasePreds()]>>
    xcon>>xsimpl>>
    cheat)
QED

(* Hooking up to parser *)
val res = translate parse_root_def;
val res = translate parse_until_nn_def;

val parse_until_nn_side_def = theorem "parse_until_nn_side_def"

val parse_until_nn_side = Q.prove(`
  !x y. parse_until_nn_side x y ⇔ T`,
  Induct>>
  simp[parse_until_nn_def,Once parse_until_nn_side_def]>>
  rw[]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition

val res = translate parse_nat_until_zero_def;
val res = translate parse_until_zero_def;
val res = translate parse_rup_add_def;
val res = translate parse_arb_del_def;
val res = translate parse_pro_aux_def;
val res = translate parse_pro_def;
val res = translate parse_sko_def;
val res = translate parse_sum_def;
val res = translate parse_scpstep_def;

Definition parse_and_run_list_def:
  parse_and_run_list pc fml sc Clist l =
  case parse_scpstep l of
    NONE => NONE
  | SOME scpstep =>
    check_scpstep_list scpstep pc fml sc Clist
End

val parse_and_run_arr = process_topdecs`
  fun parse_and_run_arr lno pc fml sc carr l =
  case parse_scpstep l of
    None => raise Fail (format_failure lno "failed to parse line")
  | Some scpstep =>
    check_scpstep_arr lno scpstep pc fml sc carr` |> append_prog

Theorem parse_and_run_arr_spec:
  NUM lno lnov ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) l lv ∧
  CNF_SCPOG_PROB_CONF_TYPE pc pcv ∧
  CNF_SCPOG_SCPOG_CONF_TYPE sc scv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_and_run_arr" (get_ml_prog_state()))
    [lnov; pcv; fmlv; scv; Carrv; lv]
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
            case parse_and_run_list pc fmlls sc Clist l of
              NONE => F
            | SOME (fmlls', sc' , Clist') =>
                bounded_fml (LENGTH Clist') fmlls' ∧
                LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv' ∧
                CNF_SCPOG_SCPOG_CONF_TYPE sc' v2 ∧
                Clist' = clist' ∧
                LENGTH Clist ≤ LENGTH Clist'
            ))
      )
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(Fail_exn e ∧
        parse_and_run_list pc fmlls sc Clist l = NONE)))
Proof
  rw[parse_and_run_list_def]>>
  xcf "parse_and_run_arr" (get_ml_prog_state ())>>
  rpt xlet_autop >>
  fs[OPTION_TYPE_SPLIT]>>
  xmatch
  >- raise_tac>>
  xapp>>xsimpl>>
  metis_tac[]
QED

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

val _ = translate blanks_def;
val _ = translate tokenize_def;

val check_unsat'' = process_topdecs `
  fun check_unsat'' fd lno pc fml sc carr =
    case TextIO.b_inputLineTokens #"\n" fd blanks tokenize of
      None => (fml,sc)
    | Some l =>
    case parse_and_run_arr lno pc fml sc carr l of
      (fml',sc',carr') =>
      check_unsat'' fd (lno+1) pc fml' sc' carr'`
      |> append_prog;

(* This says what happens to the STDIO *)
Definition check_unsat''_def:
  (check_unsat'' fd pc fml sc Clist fs [] =
    STDIO (fastForwardFD fs fd)) ∧
  (check_unsat'' fd pc fml sc Clist fs (ln::ls) =
    case parse_and_run_list pc fml sc Clist (toks ln) of
      NONE => STDIO (lineForwardFD fs fd)
    | SOME (fml', sc', Clist') =>
      check_unsat'' fd pc fml' sc' Clist'
        (lineForwardFD fs fd) ls)
End

Definition parse_and_run_file_list_def:
  (parse_and_run_file_list [] pc fml sc Clist =
    SOME (fml, sc)) ∧
  (parse_and_run_file_list (x::xs) pc fml sc Clist =
    case parse_and_run_list pc fml sc Clist (toks x) of
      NONE => NONE
    | SOME (fml', sc', Clist') =>
    parse_and_run_file_list xs pc fml' sc' Clist')
End

Theorem parse_and_run_file_list_eq:
  ∀ls pc fml sc Clist.
  parse_and_run_file_list ls pc fml sc Clist =
  case parse_scpsteps ls of
    NONE => NONE
  | SOME scpsteps =>
    OPTION_MAP (λ(a,b,c). (a,b))
      (check_scpsteps_list scpsteps pc fml sc Clist)
Proof
  Induct>>
  fs[parse_and_run_list_def,parse_scpsteps_def,parse_and_run_file_list_def,check_scpsteps_list_def]>>
  rw[]>>
  every_case_tac>>
  fs[toks_def]>>
  simp[check_scpsteps_list_def]
QED

Theorem linesFD_cons:
  lineFD fs fd = SOME x ⇒
  linesFD fs fd = x::linesFD (lineForwardFD fs fd) fd
Proof
  Cases_on`linesFD fs fd`>>
  fs[linesFD_nil_lineFD_NONE]>>
  drule linesFD_cons_imp>>
  fs[]
QED

val blanks_v_thm = theorem "blanks_v_thm";
val tokenize_v_thm = theorem "tokenize_v_thm";

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def];

Theorem check_unsat''_spec:
  !lines fs fmlv fmlls fmllsv Clist Carrv lno lnov pc pcv sc scv.
  NUM lno lnov ∧
  CNF_SCPOG_PROB_CONF_TYPE pc pcv ∧
  CNF_SCPOG_SCPOG_CONF_TYPE sc scv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; pcv; fmlv; scv; Carrv]
    (STDIO fs * ARRAY fmlv fmllsv *
      W8ARRAY Carrv Clist * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k v1 v2.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
           &(v = Conv NONE [v1; v2]) *
           (SEP_EXISTS fmllsv'.
            ARRAY v1 fmllsv' *
            &(unwrap_TYPE
              (λv fv.
              LIST_REL (OPTION_TYPE ctag_TYPE) (FST v) fv)
                 (parse_and_run_file_list lines pc fmlls sc Clist) fmllsv' ∧
              unwrap_TYPE
              (λv fv.
                CNF_SCPOG_SCPOG_CONF_TYPE (SND v) fv)
                 (parse_and_run_file_list lines pc fmlls sc Clist) v2
              ))
      )
      (λe.
         SEP_EXISTS k fmlv fmllsv lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list lines pc fmlls sc Clist = NONE)))
Proof
  Induct \\ rw []
  \\ xcf "check_unsat''" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY fmlv fmllsv *
                W8ARRAY Carrv Clist *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY fmlv fmllsv * W8ARRAY Carrv Clist’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ fs[OPTION_TYPE_def])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ xcon \\ xsimpl
    \\ fs [parse_and_run_file_list_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ fs [unwrap_TYPE_def])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY fmlv fmllsv *
                W8ARRAY Carrv Clist *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY fmlv fmllsv * W8ARRAY Carrv Clist’
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_auto >- (
    xsimpl>>simp[unwrap_TYPE_def]>>rw[]>>
    qexists_tac`x`>> qexists_tac`x'`>>xsimpl)
  >- (
    xsimpl>>
    simp[parse_and_run_file_list_def]>>
    xsimpl>>
    rw[]>>
    qexists_tac ‘k’>>
    rename1`ARRAY xx yy`>>
    qexists_tac`xx`>>qexists_tac`yy`>>
    xsimpl>>
    qexists_tac ‘lines’>>
    xsimpl>>
    metis_tac[])>>
  rveq \\ fs [] >>
  every_case_tac>>gvs[]>>
  xmatch>>
  xlet_autop >>
  xapp>>xsimpl>>
  rpt(first_x_assum (irule_at Any))>>
  fs [unwrap_TYPE_def]>>
  xsimpl>>
  qexists_tac ‘(forwardFD fs fd k)’>> xsimpl>>
  simp[parse_and_run_file_list_def]>>
  every_case_tac>> gvs[]>>
  rw[]>>gvs[forwardFD_o]
  >- (qexists_tac`k+x`>>xsimpl>>metis_tac[])>>
  qexists_tac ‘k+x’ \\ xsimpl >>
  rename1`INSTREAM_LINES _ _ _ A _ * ARRAY B C`>>
  qexists_tac`B`>>
  qexists_tac`C`>>
  qexists_tac`A`>>
  xsimpl
QED

(* We don't really care about the STDIO afterwards long as it gets closed *)
Theorem check_unsat''_eq:
  ∀ls fd fml fs sc Clist.
  ∃n.
    check_unsat'' fd pc fml sc Clist fs ls =
    case parse_and_run_file_list ls pc fml sc Clist of
     NONE => STDIO (forwardFD fs fd n)
   | SOME _ => STDIO (fastForwardFD fs fd)
Proof
  Induct>>rw[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC
  >-
    metis_tac[lineForwardFD_forwardFD]>>
  PairCases_on`x`>>fs[]>>
  rename1`check_unsat'' fd pc a b c _ ls`>>
  first_x_assum(qspecl_then[`fd`,`a`,`lineForwardFD fs fd`,`b`,`c`] strip_assume_tac)>>
  simp[]>>
  qspecl_then [`fs`,`fd`] strip_assume_tac lineForwardFD_forwardFD>>
  simp[forwardFD_o]>>
  metis_tac[]
QED

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

val iter_input_fml_arr = process_topdecs`
  fun iter_input_fml_arr i n fml p =
    if n < i then True
    else
    (case Array.lookup fml None i of
      None => iter_input_fml_arr (i+1) n fml p
    | Some (c,b) =>
      (p c andalso
      iter_input_fml_arr (i+1) n fml p))` |> append_prog;

Theorem iter_input_fml_arr_spec:
  ∀i n fmlls P fmlv fmllsv Pv iv nv.
  NUM i iv ∧
  NUM n nv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  (LIST_TYPE INT --> BOOL) P Pv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "iter_input_fml_arr" (get_ml_prog_state()))
    [iv; nv; fmlv; Pv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(BOOL (iter_input_fml i n fmlls P) v))
Proof
  ho_match_mp_tac iter_input_fml_ind>>rw[]>>
  simp[Once iter_input_fml_def]>>
  xcf "iter_input_fml_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE ctag_TYPE (any_el i fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  TOP_CASE_TAC>>gvs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xapp>>xsimpl)>>
  TOP_CASE_TAC>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlog>>rw[]
  >- (
    xlet_autop>>
    xapp>>xsimpl)>>
  xsimpl>>gvs[]
QED

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
val r = translate REV_DEF;
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

val res = translate split_lit_def;
val res = translate split_lits_def;
val res = translate mk_strict_aux_def;
val res = translate mk_strict_def;
val res = translate mk_strict_sorted_def;
val res = translate opt_hd_def;
val res = translate opt_chr_def;

val res = translate prepend_def;

val r = translate (to_flat_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def])

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

val res = translate (to_lit_string_def |> SIMP_RULE std_ss [GSYM implode_def]);

val to_lit_string_side_def = fetch "-" "to_lit_string_side_def";

Theorem to_lit_string_side:
  to_lit_string_side x ⇔ T
Proof
  rw[to_lit_string_side_def]>>
  drule (EVERY_opt_hd_mk_strict_sorted |> SIMP_RULE std_ss [EVERY_MEM])>>
  intLib.ARITH_TAC
QED

val _ = to_lit_string_side |> update_precondition;

val res = translate scpn_to_scpnv_def;
val res = translate map_scpnv_def;

val res = translate alist_to_vec_def;
val res = translate vec_lookup_def;
val res = translate falsify_lit_def;

Theorem falsify_lit_side:
  falsify_lit_side obs i ⇔ T
Proof
  Cases_on`obs`>> EVAL_TAC>>
  rw[]>>
  intLib.ARITH_TAC
QED

val _ = falsify_lit_side |> update_precondition;

val res = translate falsify_vec_def;

val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate clean_vec_def;
val res = translate (falsify_vec_sat_scpv_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (falsify_top_def);

Definition get_scp_def:
  get_scp sc = sc.scp
End

val r = translate get_scp_def;

(*
val r = translate spts_to_alist_add_pause_def;
val r = translate spt_left_def;
val r = translate spt_right_def;
val r = translate spt_center_def;
val r = translate spts_to_alist_aux_def;
val r = translate spts_to_alist_def;
val r = translate toSortedAList_def;
val r = translate spt_to_vec_def;
*)

val clean_arr = process_topdecs`
  fun clean_arr i fml =
  if Array.length fml <= i
  then ()
  else
    (Unsafe.update fml i None;
    clean_arr (i+1) fml)` |> append_prog;

Theorem check_arr_spec:
  ∀i fmlls iv fmllsv.
  NUM i iv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "clean_arr" (get_ml_prog_state()))
    [iv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &LIST_REL (OPTION_TYPE ctag_TYPE)
        (clean_list i fmlls) fmllsv')
Proof
  ho_match_mp_tac clean_list_ind>>
  rw[]>>
  xcf "clean_arr" (get_ml_prog_state ())>>
  simp[Once clean_list_def]>>
  rpt xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>gvs[]>>
    drule LIST_REL_LENGTH>>
    rw[])>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  drule LIST_REL_LENGTH>>
  rw[]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  fs[OPTION_TYPE_def]
QED

val res = translate get_node_vars_def;
val res = translate big_union_def;
val res = translate SORTED_DEF;
val res = translate mk_pro_vm_def;
val res = translate mk_strict_sorted_num_def;
val res = translate mk_sum_vm_def;
val res = translate mk_sko_vm_def;
val res = translate check_dec_def;

Definition dec_fail_str_def:
  dec_fail_str (v:num) =
  strlit "final condition check failed: input is not decomposable at " ^
  toString v ^ strlit"\n"
End
val res = translate dec_fail_str_def;

Definition check_dec_top_def:
  check_dec_top scp =
  case check_dec scp of INL v => INL (dec_fail_str v)
  | INR vs => INR ()
End

val res = translate check_dec_top_def;

val check_inputs_scp_arr = process_topdecs`
  fun check_inputs_scp_arr r pc scp fml =
  let val u = clean_arr (get_nc pc + 1) fml in
  case check_dec_top scp of
    Inl v => Inl v
  | Inr res =>
  if is_data_var pc (var_lit r)
  then
    if iter_input_fml_arr 0 (get_nc pc) fml (List.member r)
    then Inr (Inr (r,scp))
    else Inl ("final condition check failed: could not delete all input clauses using POG\n")
  else
    let
      val ns = map_scpnv pc scp
      val ov = alist_to_vec ns
      val iter = List.length scp
    in
      if iter_input_fml_arr 0 (get_nc pc) fml
        (falsify_top pc iter (var_lit r) ov)
      then Inr (Inr (r,scp))
      else Inl ("final condition check failed: could not delete all input clauses using POG\n")
    end
  end`|>append_prog;

Theorem EqualityType_INT:
  EqualityType INT
Proof
  simp[EqualityType_NUM_BOOL]
QED

Theorem EqualityType_LIST_TYPE_INT:
  EqualityType (LIST_TYPE INT)
Proof
  match_mp_tac EqualityType_LIST_TYPE>>
  simp[EqualityType_NUM_BOOL]
QED

(*
Theorem app_efalsify_vec_sat_scpv_v:
  NUM w wv ∧
  NUM x xv ∧
  VECTOR_TYPE (OPTION_TYPE CNF_SCPOG_SCPNV_TYPE) y yv ∧
  VECTOR_TYPE (OPTION_TYPE (VECTOR_TYPE (OPTION_TYPE UNIT_TYPE))) z zv ⇒
  app (p : 'ffi ffi_proj) efalsify_vec_sat_scpv_v [wv;xv;yv;zv] emp
    (POSTv v.
       &(LIST_TYPE INT --> BOOL)
         (efalsify_vec_sat_scpv w x y z) v)
Proof
  rw[]>>
  simp[app_def]>>
  `app_basic p efalsify_vec_sat_scpv_v wv emp
    (POSTv g. &app_basic p g xv emp
        (POSTv g. &app_basic p g yv emp
        (POSTv g. &app_basic p g zv emp
          (POSTv v. &(LIST_TYPE INT --> BOOL)
          (efalsify_vec_sat_scpv w x y z) v))))` by (
    assume_tac (fetch "-" "efalsify_vec_sat_scpv_v_thm")>>
    qpat_x_assum`NUM w wv` assume_tac>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond]>>
    drule Arrow_IMP_app_basic>>
    qpat_x_assum`NUM x xv` assume_tac>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond]>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond]>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    simp[])>>
  gvs[GSYM app_def]>>
  drule_then irule app_weaken>>
  xsimpl>> rw[]>>
  qexists_tac`emp`>>xsimpl>>
  drule_then irule app_weaken>>
  xsimpl>> rw[]>>
  qexists_tac`emp`>>xsimpl>>
  drule_then irule app_weaken>>
  xsimpl>> rw[]>>
  qexists_tac`emp`>>xsimpl
QED
*)

Theorem app_falsify_top_v:
  CNF_SCPOG_PROB_CONF_TYPE u uv ∧
  NUM w wv ∧
  NUM x xv ∧
  VECTOR_TYPE (OPTION_TYPE CNF_SCPOG_SCPNV_TYPE) y yv ⇒
  app (p : 'ffi ffi_proj) falsify_top_v [uv;wv;xv;yv] emp
    (POSTv v.
       &(LIST_TYPE INT --> BOOL)
         (falsify_top u w x y) v)
Proof
  rw[]>>
  simp[app_def]>>
  `app_basic p falsify_top_v uv emp
    (POSTv g. &app_basic p g wv emp
        (POSTv g. &app_basic p g xv emp
        (POSTv g. &app_basic p g yv emp
          (POSTv v. &(LIST_TYPE INT --> BOOL)
          (falsify_top u w x y) v))))` by (
    assume_tac (fetch "-" "falsify_top_v_thm")>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond]>>
    qpat_x_assum`NUM w wv` assume_tac>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond]>>
    drule Arrow_IMP_app_basic>>
    qpat_x_assum`NUM x xv` assume_tac>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond]>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    disch_then(qspec_then`p` mp_tac)>>
    ho_match_mp_tac app_basic_weaken>>
    rw[cfAppTheory.POSTv_cond])>>
  gvs[GSYM app_def]>>
  drule_then irule app_weaken>>
  xsimpl>> rw[]>>
  qexists_tac`emp`>>xsimpl>>
  drule_then irule app_weaken>>
  xsimpl>> rw[]>>
  qexists_tac`emp`>>xsimpl>>
  drule_then irule app_weaken>>
  xsimpl>> rw[]>>
  qexists_tac`emp`>>xsimpl
QED

Definition check_inputs_scp_list_err_def:
  check_inputs_scp_list_err r pc scp fmlls err =
  case check_inputs_scp_list r pc scp fmlls of
    NONE => INL err
  | SOME res => INR res
End

Overload "res_TYPE" = ``SUM_TYPE UNIT_TYPE (PAIR_TYPE INT (LIST_TYPE (PAIR_TYPE NUM CNF_SCPOG_SCPN_TYPE)))``

Theorem check_inputs_scp_arr_spec:
  INT r rv ∧
  CNF_SCPOG_PROB_CONF_TYPE pc pcv ∧
  LIST_TYPE (PAIR_TYPE NUM CNF_SCPOG_SCPN_TYPE) scp scpv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_inputs_scp_arr" (get_ml_prog_state()))
    [rv; pcv; scpv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      &(∃err.
        SUM_TYPE STRING_TYPE res_TYPE
        (check_inputs_scp_list_err r pc scp fmlls err) v))
Proof
  rw[]>>
  xcf "check_inputs_scp_arr" (get_ml_prog_state ())>>
  simp[check_inputs_scp_list_err_def,check_inputs_scp_list_def]>>
  rpt xlet_autop>>
  Cases_on`check_dec_top scp`>>
  gvs[SUM_TYPE_def,check_dec_top_def,AllCaseEqs()]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  xif
  >- (
    xlet`POSTv v. ARRAY fmlv fmllsv' *
      &( (LIST_TYPE INT --> BOOL) (MEM r) v)`
    >- (
      assume_tac (
        (ListProgTheory.member_v_thm |> DISCH_ALL |> MATCH_MP )
        EqualityType_INT)>>
      drule Arrow_IMP_app_basic>>
      disch_then drule>>
      simp[GSYM app_def]>>
      rw[]>>
      xapp>>xsimpl>>
      simp[MEMBER_INTRO])>>
    rpt xlet_autop>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      gvs[get_nc_def,SUM_TYPE_def,PAIR_TYPE_def])>>
    xcon>>xsimpl>>
    gvs[get_nc_def,SUM_TYPE_def,PAIR_TYPE_def])>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    gvs[get_nc_def,SUM_TYPE_def,PAIR_TYPE_def])>>
  xcon>>xsimpl>>
  gvs[get_nc_def,SUM_TYPE_def,PAIR_TYPE_def]
QED

val is_forward_clause_v_thm = translate is_forward_clause_def;

val is_forward_fml_arr = process_topdecs`
  fun is_forward_fml_arr arr c =
  Array.exists (is_forward_clause c) arr` |> append_prog;

Definition get_root_def:
  get_root sc = sc.root
End

val r = translate get_root_def;

Definition is_data_ext_lit_run_Ev_def:
  is_data_ext_lit_run_Ev pc sc r =
    is_data_ext_lit_run pc sc.Ev r
End

val r = translate is_data_ext_lit_run_Ev_def;

val check_final_arr = process_topdecs `
  fun check_final_arr pc sc fml =
  case get_root sc of
    None => Inl ("root not declared")
  | Some r =>
    if r = 0
    then
      if is_forward_fml_arr fml []
      then Inr (Inl ())
      else Inl ("did not find empty clause for UNSAT proof")
    else
      if is_forward_fml_arr fml [r]
      then
        if is_data_ext_lit_run_ev pc sc r
        then
          check_inputs_scp_arr r pc (get_scp sc) fml
        else Inl ("final condition check failed: invalid root declared\n")
      else Inl ("final condition check failed: root unit clause not found\n")
  ` |> append_prog;

val check_unsat' = process_topdecs `
  fun check_unsat' pc fml sc fname n =
  let
    val fd = TextIO.b_openIn fname
    val carr = Word8Array.array n w8z
    val chk = Inr (check_unsat'' fd 1 pc fml sc carr)
      handle Fail s => Inl s
    val close = TextIO.b_closeIn fd;
  in
    case chk of
      Inl s => Inl s
    | Inr res =>
      (case res of (fml,sc) =>
        check_final_arr pc sc fml)
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

(* TODO: COPIED from readerProg, should be moved *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

Theorem all_lines_gen_all_lines[simp]:
  all_lines_gen #"\n" fs f =
  all_lines fs f
Proof
  rw[all_lines_def,all_lines_gen_def,lines_of_def,lines_of_gen_def,splitlines_at_def,splitlines_def,str_def]
QED

Theorem check_final_arr_spec:
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  CNF_SCPOG_PROB_CONF_TYPE pc pcv ∧
  CNF_SCPOG_SCPOG_CONF_TYPE sc scv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_final_arr"(get_ml_prog_state()))
  [pcv; scv; fmlv]
  (ARRAY fmlv fmllsv)
  (POSTv v.
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE res_TYPE
      (case check_final_list pc sc fmlls of
        NONE => INL err
      | SOME res => INR res) v))
Proof
  rw[]>>
  xcf "check_final_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  gvs[get_root_def,check_final_list_def,OPTION_TYPE_SPLIT]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  xif
  >- (
    xlet`POSTv v. ARRAY fmlv fmllsv * &(LIST_TYPE INT [] v)`
    >- (xcon>>xsimpl>>simp[LIST_TYPE_def])>>
    xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (is_forward_fml_list fmlls []) v`
    >- (
      xapp_prepare_goal>>
      xcf "is_forward_fml_arr" (get_ml_prog_state ())>>
      assume_tac (
        (is_forward_clause_v_thm |> DISCH_ALL |> MATCH_MP )
        EqualityType_LIST_TYPE_INT |> Q.GEN`b` |> Q.ISPEC`BOOL`)>>
      drule Arrow_IMP_app_basic>>
      disch_then drule>>
      simp[GSYM app_def]>>
      rw[]>>
      xlet_autop>>
      simp[is_forward_fml_list_def]>>
      xapp>>xsimpl>>
      metis_tac[])>>
    xif>>xsimpl
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def])>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  rename1`is_forward_fml_list _ [r]`>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &(LIST_TYPE INT [r] v)`
  >- (
    xcon>>xsimpl>>simp[LIST_TYPE_def])>>
  xlet`POSTv v. ARRAY fmlv fmllsv * &BOOL (is_forward_fml_list fmlls [r]) v`
  >- (
    xapp_prepare_goal>>
    xcf "is_forward_fml_arr" (get_ml_prog_state ())>>
    assume_tac (
      (is_forward_clause_v_thm |> DISCH_ALL |> MATCH_MP)
        EqualityType_LIST_TYPE_INT |> Q.GEN`b` |> Q.ISPEC`BOOL`)>>
    drule Arrow_IMP_app_basic>>
    disch_then drule>>
    simp[GSYM app_def]>>
    rw[]>>
    xlet_autop>>
    simp[is_forward_fml_list_def]>>
    xapp>>xsimpl>>
    metis_tac[])>>
  reverse xif
  >- (
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  gvs[is_data_ext_lit_run_Ev_def]>>
  reverse xif
  >- (
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  simp[check_inputs_scp_list_err_def,get_scp_def]
QED

Theorem check_unsat'_spec:
  NUM n nv ∧
  LIST_REL (OPTION_TYPE ctag_TYPE) fmlls fmllsv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  CNF_SCPOG_PROB_CONF_TYPE pc pcv ∧
  CNF_SCPOG_SCPOG_CONF_TYPE sc scv ∧
  bounded_fml n fmlls
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [pcv; fmlv; scv; fv; nv]
  (STDIO fs * ARRAY fmlv fmllsv)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE res_TYPE)
      (if inFS_fname fs f then
        (case parse_scpsteps (all_lines fs f) of
         SOME scpsteps =>
           (case check_scp_final_list scpsteps pc fmlls sc (REPLICATE n w8z) of
             NONE => INL err
           | SOME res => INR res)
        | NONE => INL err)
      else
        INL err
      ) v)
Proof
  rw[]>>
  xcf"check_unsat'"(get_ml_prog_state()) >>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs *
      ARRAY fmlv fmllsv`
    >-
      (xlet_auto_spec (SOME b_openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (b_openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`)) \\ xsimpl >>
  `WORD8 w8z w8z_v` by fs[w8z_v_thm]>>
  xlet_autop >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qabbrev_tac`Clist = REPLICATE n w8z`>>
  xlet`POSTv resv.
   SEP_EXISTS v0 v1 v2 fmllsv' fmlv' k rest.
    STDIO (forwardFD fss (nextFD fs) k) *
    INSTREAM_LINES #"\n" (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
    ARRAY fmlv' fmllsv' *
    &(
      case
        parse_and_run_file_list (all_lines fs f) pc fmlls sc (REPLICATE n w8z)
      of
        NONE => resv =
          Conv (SOME (TypeStamp "Inl" 4)) [v0] ∧ ∃s. STRING_TYPE s v0
      | SOME(fmlls',sc') =>
        resv = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]] ∧
        v1 = fmlv' ∧
        CNF_SCPOG_SCPOG_CONF_TYPE sc' v2 ∧
        LIST_REL (OPTION_TYPE ctag_TYPE) fmlls' fmllsv'
    )`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS fmlv fmllsv rest k.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES #"\n" (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY fmlv fmllsv *
          &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) pc fmlls sc Clist = NONE)`
      >- (
        (* this used to be an xauto_let .. sigh *)
        xlet `POSTe e.
         SEP_EXISTS k fmlv fmllsv lines'.
           STDIO (forwardFD fss (nextFD fs) k) *
           INSTREAM_LINES #"\n" (nextFD fs) is lines' (forwardFD fss (nextFD fs) k) *
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) pc fmlls sc Clist = NONE)`
        THEN1 (
          xapp_spec check_unsat''_spec
          \\ xsimpl
          \\ rpt (first_x_assum (irule_at Any))
          \\ xsimpl \\ fs [Abbr`Clist`]
          \\ qexists_tac `all_lines fs f`
          \\ qexists_tac `fss`
          \\ qexists_tac `nextFD fs`
          \\ qexists_tac `emp`
          \\ xsimpl \\ fs [unwrap_TYPE_def]
          \\ rw[]
          \\ qexists_tac `x`
          \\ rename [`_ * INSTREAM_LINES _ _ _ xxx _ * ARRAY a1 a2`]
          \\ qexists_tac `a1`
          \\ qexists_tac `a2`
          \\ qexists_tac `xxx`
          \\ xsimpl)>>
        fs[unwrap_TYPE_def]>>
        xsimpl>>
        rw[]>>
        rename [`_ * INSTREAM_LINES _ _ _ xxx _ * ARRAY a1 a2`]
        \\ qexists_tac `a1`
        \\ qexists_tac `a2`
        \\ qexists_tac `xxx`
        \\ qexists_tac `x`
        \\ xsimpl)>>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>> simp[]>>
      rename [`_ * _ * ARRAY a1 a2`]>>
      qexists_tac `a2` >>
      qexists_tac `a1` >>
      qexists_tac `k` >>
      qexists_tac `rest` >> xsimpl) >>
    xhandle`(POSTv v.
        SEP_EXISTS v1 v2 k rest.
         STDIO (forwardFD fss (nextFD fs) k) *
         INSTREAM_LINES #"\n" (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
         &(v = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]]) *
         (SEP_EXISTS fmllsv'.
           ARRAY v1 fmllsv' *
           &(unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE ctag_TYPE) (FST v) fv)
                (parse_and_run_file_list (all_lines fs f) pc fmlls sc Clist) fmllsv' ∧
             unwrap_TYPE
             (λv fv. CNF_SCPOG_SCPOG_CONF_TYPE (SND v) fv)
                (parse_and_run_file_list (all_lines fs f) pc fmlls sc Clist ) v2)))`
    >- (
        xlet `POSTv v.
           SEP_EXISTS k v1 v2.
               STDIO (forwardFD fss (nextFD fs) k) *
               INSTREAM_LINES #"\n" (nextFD fs) is [] (forwardFD fss (nextFD fs) k) *
               &(v = Conv NONE [v1; v2]) *
               (SEP_EXISTS fmllsv'.
                    ARRAY v1 fmllsv' *
                    &(unwrap_TYPE
                     (λv fv. LIST_REL (OPTION_TYPE ctag_TYPE) (FST v) fv)
                        (parse_and_run_file_list (all_lines fs f) pc fmlls sc Clist) fmllsv' ∧
                     unwrap_TYPE
                     (λv fv. CNF_SCPOG_SCPOG_CONF_TYPE (SND v) fv)
                        (parse_and_run_file_list (all_lines fs f) pc fmlls sc Clist ) v2))`
        THEN1
         (xapp_spec check_unsat''_spec
          \\ xsimpl
          \\ rpt (first_x_assum (irule_at Any))
          \\ xsimpl \\ fs [Abbr`Clist`]
          \\ qexists_tac `all_lines fs f`
          \\ qexists_tac `fss`
          \\ qexists_tac `nextFD fs`
          \\ qexists_tac `emp`
          \\ xsimpl \\ fs [unwrap_TYPE_def]
          \\ rpt strip_tac
          \\ qexists_tac `x'`
          \\ xsimpl) >>
        fs[unwrap_TYPE_def]>>
        xcon >>
        xsimpl>>
        rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
        rename [`INSTREAM_LINES _ _ _ rr`] \\ qexists_tac `rr` \\ xsimpl) >>
      xsimpl>>simp[unwrap_TYPE_def]>>
      Cases_on`x`>>fs[]>>rw[]>>xsimpl >>
      rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
      rename [`INSTREAM_LINES _ _ _ rr`] \\ qexists_tac `rr` \\ xsimpl)>>
  qspecl_then [`all_lines fs f`,`pc`,`fmlls`,`sc`,`Clist`] strip_assume_tac parse_and_run_file_list_eq>>
  fs[]>>rw[]>>
  xlet `POSTv v. STDIO fs * ARRAY fmlv' fmllsv'`
  THEN1
   (xapp_spec b_closeIn_spec_lines >>
    rename [`_ * _ * ARRAY a1 a2`] >>
    qexists_tac `ARRAY a1 a2` >>
    qexists_tac `rest` >>
    qexists_tac `forwardFD fss (nextFD fs) k` >>
    qexists_tac `nextFD fs` >>
    qexists_tac `#"\n"` >>
    conj_tac THEN1
     (fs [forwardFD_def,Abbr`fss`]
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    `validFileFD (nextFD fs) (forwardFD fss (nextFD fs) k).infds` by
      (simp[validFileFD_forwardFD]>> simp[Abbr`fss`]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`] \\ xsimpl) >>
  Cases_on`parse_scpsteps (all_lines fs f)`>> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon >> xsimpl >>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  gvs[AllCasePreds(),check_scp_final_list_def]
  >- (
    xmatch >> xcon >>
    xsimpl>> simp[SUM_TYPE_def] >> metis_tac[])>>
  pairarg_tac>>gvs[]>>
  xmatch >> fs[]>>
  xmatch >> fs[]>>
  xapp>>
  rpt(first_x_assum (irule_at Any))>>
  xsimpl>>
  metis_tac[]
QED

val _ = export_theory();
