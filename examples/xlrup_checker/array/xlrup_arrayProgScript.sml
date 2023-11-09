(*
  This refines xlrup_list to use arrays
*)
open preamble basis UnsafeProofTheory xlrupTheory xlrup_listTheory xlrup_parsingTheory blastLib;

val _ = new_theory "xlrup_arrayProg"

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

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

(* Pure translation of LPR checker *)
val _ = register_type``:xlrup``;
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

val Fail_exn_def = Define `
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)`

val eq_w8o_def = Define`
  eq_w8o v ⇔ v = w8o`

val _ = translate (eq_w8o_def |> SIMP_RULE std_ss [w8o_def]);

val every_one_arr = process_topdecs`
  fun every_one_arr carr cs =
  case cs of [] => True
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then every_one_arr carr cs
    else False` |> append_prog

val format_failure_def = Define`
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val _ = translate format_failure_def;

val unwrap_TYPE_def = Define`
  unwrap_TYPE P x y =
  ∃z. x = SOME z ∧ P z y`

val delete_literals_sing_arr_def = process_topdecs`
  fun delete_literals_sing_arr lno carr cs =
  case cs of
    [] => 0
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then
      delete_literals_sing_arr lno carr cs
    else
      if every_one_arr carr cs then ~c
      else raise Fail (format_failure lno "clause not empty or singleton after reduction")` |> append_prog

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Theorem list_lookup_eq_EL[simp]:
  LENGTH Clist > index h ⇒
  list_lookup Clist w8z (index h) = EL (index h) Clist
Proof
  rw[list_lookup_def]
QED

Theorem resize_update_list_LUPDATE[simp]:
  LENGTH Clist > index h ⇒
  resize_update_list Clist w8z v (index h) = LUPDATE v (index h) Clist
Proof
  rw[resize_update_list_def]
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
      &BOOL (EVERY (λi. list_lookup Clist w8z (index i) = w8o) ls) v)
Proof
  Induct>>xcf "every_one_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >-
    (xmatch>>xcon>>xsimpl)
  >>
  xmatch>>
  rpt xlet_autop>>
  fs[eq_w8o_def]>>
  xif
  >-
    (xapp>>xsimpl)
  >>
  xcon>> xsimpl
QED

Theorem delete_literals_sing_arr_spec:
  ∀ls lsv lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE INT) ls lsv ∧
  EVERY ($> (LENGTH Clist) o index) ls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_literals_sing_arr" (get_ml_prog_state()))
    [lnov; Carrv; lsv]
    (W8ARRAY Carrv Clist)
    (POSTve
      (λv. W8ARRAY Carrv Clist *
        &unwrap_TYPE INT (delete_literals_sing_list Clist ls) v)
      (λe. &(Fail_exn e ∧ delete_literals_sing_list Clist ls = NONE)))
Proof
  Induct>>simp[delete_literals_sing_list_def]>>
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
  fs[eq_w8o_def]>>
  IF_CASES_TAC>>fs[] >- (
    xif>>instantiate>>
    xapp>>xsimpl>>
    metis_tac[])>>
  xif>>instantiate>>
  xlet_auto>>
  xif
  >- (
    xapp>>xsimpl>>simp[unwrap_TYPE_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  IF_CASES_TAC>-
    metis_tac[NOT_EVERY]>>
  simp[unwrap_TYPE_def,Fail_exn_def]>>
  metis_tac[]
QED

val is_rup_arr_aux = process_topdecs`
  fun is_rup_arr_aux lno fml ls c carr =
    case ls of
      [] =>
        raise Fail (format_failure lno ("failed to prove by RUP"))
    | (i::is) =>
    if Array.length fml <= i then
      raise Fail (format_failure lno ("clause index out of bounds: " ^ Int.toString i))
    else
    case Unsafe.sub fml i of
      None => raise Fail (format_failure lno ("clause index already deleted: " ^ Int.toString i))
    | Some ci =>
      let val nl = delete_literals_sing_arr lno carr ci in
      if nl = 0 then c
      else
        (Unsafe.w8update carr (index nl) w8o;
        is_rup_arr_aux lno fml is (nl::c) carr)
      end` |> append_prog

(* For every literal in every clause and their negations,
  the index is bounded above by n *)
val bounded_cfml_def = Define`
  bounded_cfml n fmlls ⇔
  EVERY (λCopt.
    case Copt of
      NONE => T
    | SOME C => EVERY ($> n o index) C ∧ EVERY ($> n o index o $~) C
    ) fmlls`

Theorem delete_literals_sing_list_MEM:
  ∀C.
  delete_literals_sing_list ls C = SOME x ∧ x ≠ 0
  ⇒
  MEM (-x) C
Proof
  Induct>>rw[delete_literals_sing_list_def] >> simp[] >>
  CCONTR_TAC >> fs [] >> rw []
QED

Theorem is_rup_arr_aux_spec:
  ∀ls lsv c cv fmlv fmlls fml Carrv Clist lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_cfml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr_aux" (get_ml_prog_state()))
    [lnov; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &unwrap_TYPE ($= o SND)
          (is_rup_list_aux fmlls ls c Clist) Clist'
        ) *
        &unwrap_TYPE
          (LIST_TYPE INT o FST)
          (is_rup_list_aux fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ is_rup_list_aux fmlls ls c Clist = NONE)))
Proof
  Induct>>xcf "is_rup_arr_aux" (get_ml_prog_state ())>>
  simp[is_rup_list_aux_def]
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  fs[LIST_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt (xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    `list_lookup fmlls NONE h = NONE` by
      (simp[list_lookup_def]>>
      metis_tac[LIST_REL_LENGTH])>>
    simp[unwrap_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC
  >- (
    fs[list_lookup_def]>>
    reverse (Cases_on`EL h fmlls`)>-
      (fs[IS_SOME_DEF]>>metis_tac[LIST_REL_LENGTH])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt(xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  fs[list_lookup_def,OPTION_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    fs[bounded_cfml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` mp_tac)>>simp[])
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
  `index z < LENGTH Clist ∧ WORD8 w8o w8o_v` by
    (fs[w8o_v_thm]>>
    fs[bounded_cfml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` assume_tac)>>rfs[]>>
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
  fun is_rup_arr lno fml ls c carr =
    (set_array carr w8o c;
    set_array carr w8z (is_rup_arr_aux lno fml ls c carr);
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
Theorem resize_update_list_twice:
  index x < LENGTH Clist ∧ index h < LENGTH Clist ⇒
  resize_update_list (resize_update_list Clist w8z w8o (index x)) w8z w8o (index h) =
  resize_update_list (resize_update_list Clist w8z w8o (index h)) w8z w8o (index x)
Proof
  rw[resize_update_list_def]>>
  Cases_on`x=h`>>simp[]>>
  `index x ≠ index h` by metis_tac[index_11]>>
  metis_tac[LUPDATE_commutes]
QED

Theorem set_list_resize_update_list:
  ∀c Clist.
  index x < LENGTH Clist ∧ EVERY ($> (LENGTH Clist) ∘ index) c ⇒
  set_list Clist w8o (x::c) =
  resize_update_list (set_list Clist w8o c) w8z w8o (index x)
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
  bounded_cfml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c ∧
  is_rup_list_aux fmlls ls c (set_list Clist w8o c) = SOME(d,r) ⇒
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
  fs[bounded_cfml_def,EVERY_MEM,list_lookup_def]>>
  first_x_assum(qspec_then`EL h fmlls` mp_tac)>>
  impl_tac>-
    (`h < LENGTH fmlls` by fs[]>>
    metis_tac[MEM_EL])>>
  simp[]>>strip_tac>>
  qexists_tac`nl::c`>>
  CONJ_TAC >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[set_list_resize_update_list]>>
    simp[EVERY_MEM]>>
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
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_cfml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(unwrap_TYPE $=
            (is_rup_list fmlls ls c Clist) Clist' ∧
            LENGTH Clist = LENGTH Clist')
          ) *
        &unwrap_TYPE
          (λv w. T)
          (is_rup_list fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ is_rup_list fmlls ls c Clist = NONE)))
Proof
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

val res = translate toByte_def;

val strxor_aux_c_arr = process_topdecs`
  fun strxor_aux_c_arr cs ds n =
  if n = 0 then cs
  else
  let
    val n1 = n - 1
    val c = Unsafe.w8sub cs n1
    val d = tobyte (String.sub ds n1)
    val x = Word8.xorb c d
    val u = Unsafe.w8update cs n1 x
  in
    strxor_aux_c_arr cs ds n1
  end` |> append_prog;

Theorem strxor_aux_c_arr_spec:
  ∀n nv cs csv ds dsv.
  NUM n nv ∧
  STRING_TYPE ds dsv ∧
  n ≤ strlen ds ∧ strlen ds ≤ LENGTH cs
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "strxor_aux_c_arr" (get_ml_prog_state()))
    [csv; dsv; nv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(strxor_aux_c cs ds n = cs'))
Proof
  Induct>>rw[]>>
  xcf "strxor_aux_c_arr" (get_ml_prog_state ())>>
  simp[Once strxor_aux_c_def]>>
  xlet_autop
  >- (
    xif>>asm_exists_tac>>simp[]>>
    xvar>>xsimpl)>>
  xif>>asm_exists_tac>>simp[]>>
  rpt xlet_autop>>
  xapp>>xsimpl
QED

val strxor_c_arr = process_topdecs`
  fun strxor_c_arr s t =
  let
    val lt = String.size t
    val ls = Word8Array.length s
  in
    if lt <= ls
    then strxor_aux_c_arr s t lt
    else
      let
        val ss = Word8Array.array lt w8z
        val u = Word8Array.copy s 0 ls ss 0
      in
        strxor_aux_c_arr ss t lt
      end
  end` |> append_prog;

Theorem strxor_c_arr_spec:
  STRING_TYPE ds dsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "strxor_c_arr" (get_ml_prog_state()))
    [csv; dsv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(strxor_c cs ds = cs'))
Proof
  rw[]>>
  xcf "strxor_c_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xif
  >- (
    simp[strxor_c_def]>>
    xapp>>xsimpl)>>
  assume_tac w8z_v_thm>>
  xlet_autop>>
  xlet_autop>>
  simp[strxor_c_def]>>
  xapp>>
  xsimpl>>
  qexists_tac`strlen ds`>>
  qexists_tac`ds`>>simp[]>>
  rw[w8z_def]
QED

val add_xors_aux_c_arr = process_topdecs`
  fun add_xors_aux_c_arr lno fml is s =
  case is of
    [] => s
  | i::is =>
    if Array.length fml <= i then
      raise Fail (format_failure lno ("xor index out of bounds: " ^ Int.toString i))
    else
    case Unsafe.sub fml i of
      None => raise Fail (format_failure lno ("xor index already deleted: " ^ Int.toString i))
    | Some x =>
      add_xors_aux_c_arr lno fml is (strxor_c_arr s x)` |> append_prog;

Theorem add_xors_aux_c_arr_spec:
  ∀ls lsv cs csv fmlv fmlls fmllsv lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "add_xors_aux_c_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; csv]
    (ARRAY fmlv fmllsv * W8ARRAY csv cs)
    (POSTve
      (λv. ARRAY fmlv fmllsv * SEP_EXISTS cs'.
        W8ARRAY v cs' *
        &(unwrap_TYPE $=
          (add_xors_aux_c_list fmlls ls cs) cs'))
       (λe.
        ARRAY fmlv fmllsv *
        &(Fail_exn e ∧ add_xors_aux_c_list fmlls ls cs = NONE)))
Proof
  Induct>>
  xcf "add_xors_aux_c_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (
    xvar>>xsimpl>>
    simp[unwrap_TYPE_def,add_xors_aux_c_list_def])>>
  rpt xlet_autop>>
  simp[add_xors_aux_c_list_def,list_lookup_def]>>
  drule LIST_REL_LENGTH>> simp[]>>
  strip_tac>>
  xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  `OPTION_TYPE STRING_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  xapp>>xsimpl>>
  metis_tac[]
QED

val eq_w8z_def = Define`
  eq_w8z v ⇔ v = w8z`

val _ = translate (eq_w8z_def |> SIMP_RULE std_ss [w8z_def]);

val is_emp_xor_arr_aux = process_topdecs`
  fun is_emp_xor_arr_aux lno arr n =
  if n > 0
  then
  let
  val n1 = n - 1 in
    if
      eq_w8z (Unsafe.w8sub arr n1)
    then
      is_emp_xor_arr_aux lno arr n1
    else
      raise Fail (format_failure lno ("Index : " ^ Int.toString n1 ^ " not canceled after summing XORs"))
  end
  else ()` |> append_prog;

Theorem is_emp_xor_arr_aux_spec:
  ∀n nv.
  NUM lno lnov ∧
  NUM n nv ∧ n <= LENGTH cs ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_emp_xor_arr_aux" (get_ml_prog_state()))
    [lnov; csv; nv]
    (W8ARRAY csv cs)
    (POSTve
      (λv. W8ARRAY csv cs *
        &(is_emp_xor_list (TAKE n cs)))
      (λe.
          W8ARRAY csv cs *
         &(Fail_exn e ∧ ¬is_emp_xor_list (TAKE n cs))))
Proof
  Induct>>fs[is_emp_xor_list_def]>>rw[]>>
  xcf "is_emp_xor_arr_aux" (get_ml_prog_state ())
  >- (
    xlet_autop>>xif>>
    asm_exists_tac>>xsimpl>>
    xcon>>xsimpl)>>
  xlet_autop>>
  xif>>
  asm_exists_tac>>xsimpl>>
  rpt xlet_autop>>
  DEP_REWRITE_TAC[GSYM SNOC_EL_TAKE]>>
  fs[EXISTS_SNOC,EVERY_SNOC,eq_w8z_def]>>
  xif
  >-
    (xapp>>fs[]>>xsimpl)>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  fs[Fail_exn_def]>>
  metis_tac[]
QED

val is_xor_arr = process_topdecs`
  fun is_xor_arr lno def fml is s =
  let
    val r = Word8Array.array def w8z
    val r = strxor_c_arr r s
    val res = add_xors_aux_c_arr lno fml is r
  in
    is_emp_xor_arr_aux lno res (Word8Array.length res)
  end` |> append_prog;

Theorem is_xor_arr_spec:
  NUM lno lnov ∧
  NUM def defv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) fmlls fmllsv ∧
  STRING_TYPE s sv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_xor_arr" (get_ml_prog_state()))
    [lnov; defv; fmlv; lsv; sv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &(is_xor_list def fmlls ls s))
      (λe.
         ARRAY fmlv fmllsv *
         &(Fail_exn e ∧ ¬is_xor_list def fmlls ls s)))
Proof
  xcf "is_xor_arr" (get_ml_prog_state ())>>
  rw[is_xor_list_def]>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop
  >-
    xsimpl>>
  TOP_CASE_TAC>>fs[unwrap_TYPE_def]>>
  rw[]>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>simp[]>>
  metis_tac[]
QED

val list_delete_arr = process_topdecs`
  fun list_delete_arr ls fml =
    case ls of
      [] => ()
    | (i::is) =>
      if Array.length fml <= i then list_delete_arr is fml
      else
        (Unsafe.update fml i None; list_delete_arr is fml)` |> append_prog

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
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (xapp >> xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto >- xsimpl>>
  xapp>>xsimpl>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]
QED

val resize_update_arr = process_topdecs`
  fun resize_update_arr v n fml =
  if n < Array.length fml then
    (Unsafe.update fml n v ; fml)
  else
    let val fml' = Array.array (2*n+1) None
        val u = Array.copy fml fml' 0
        val u = Unsafe.update fml' n v
    in
      fml'
    end` |> append_prog

Theorem resize_update_arr_spec:
  OPTION_TYPE vty v vv ∧
  NUM n nv ∧
  LIST_REL (OPTION_TYPE vty) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_update_arr" (get_ml_prog_state()))
    [vv; nv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' *
      &(LIST_REL (OPTION_TYPE vty) (resize_update_list fmlls NONE v n) fmllsv') )
Proof
  rw[] >>
  xcf "resize_update_arr" (get_ml_prog_state ())>>
  rpt (xlet_autop) >>
  xif
  >- (
    xlet_autop >>
    xvar>>xsimpl>>
    `LENGTH fmlls = LENGTH fmllsv` by
      metis_tac[LIST_REL_LENGTH]>>
    simp[resize_update_list_def]>>
    match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def])
  >>
  rpt (xlet_autop) >>
  xlet`POSTv uv. (* TODO: probably should be added to the basis spec for Array.copy: &UNIT_TYPE () uv * *)
    ARRAY av (fmllsv ++ REPLICATE (2*n+1-LENGTH fmllsv) (Conv (SOME (TypeStamp "None" 2)) []))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`REPLICATE (LENGTH fmllsv) (Conv (SOME (TypeStamp "None" 2)) [])`>>
    simp[]>>
    simp[REPLICATE_APPEND])
  >>
  xlet_autop >>
  xvar >>xsimpl>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  simp[resize_update_list_def]>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]>>
  match_mp_tac EVERY2_APPEND_suff>>simp[]>>
  simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]
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

Definition flip_bit_word'_def:
  flip_bit_word' (w:word8) n =
  let nw = var_word_lsl 1w n in
  let b = (w && nw = 0w) in
  if b then w ‖ nw else w && ¬nw
End

val res = translate flip_bit_word'_def;

Theorem flip_bit_word'_eq:
  n < 8 ⇒
  (flip_bit_word' (w:word8) n = flip_bit_word w n)
Proof
  simp[flip_bit_word_def,flip_bit_word'_def]>>
  strip_tac>>
  DEP_REWRITE_TAC[word_bit |> INST_TYPE[alpha |-> ``:8``] |> SIMP_RULE std_ss [word_bit_test] |> CONV_RULE (wordsLib.WORD_CONV)]>>
  fs[WORD_MUL_LSL |> Q.ISPEC`1w:word8` |> CONV_RULE (wordsLib.WORD_CONV) |> GSYM]
QED

val flip_bit_arr = process_topdecs`
  fun flip_bit_arr s n =
  let
    val q = n div 8
    val r = n mod 8
    val b = flip_bit_word' (Unsafe.w8sub s q) r in
    Unsafe.w8update s q b
  end` |> append_prog;

Theorem flip_bit_arr_spec:
  NUM n nv ∧ n DIV 8 < LENGTH cs ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "flip_bit_arr" (get_ml_prog_state()))
    [csv; nv]
    (W8ARRAY csv cs)
    (POSTv v.
      W8ARRAY csv (flip_bit_list cs n))
Proof
  xcf "flip_bit_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  simp[flip_bit_list_def]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  DEP_REWRITE_TAC[flip_bit_word'_eq]>>
  simp[]
QED

val extend_s_arr = process_topdecs`
  fun extend_s_arr s n =
  let val ls = Word8Array.length s in
  if n < ls
  then s
  else
  let
    val ss = Word8Array.array n w8z
    val u = Word8Array.copy s 0 ls ss 0
  in
    ss
  end
  end` |> append_prog;

Theorem extend_s_arr_spec:
  NUM n nv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extend_s_arr" (get_ml_prog_state()))
    [csv; nv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(extend_s_list cs n = cs'))
Proof
  xcf "extend_s_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  simp[extend_s_list_def]>>
  xif
  >-
    (xvar>>xsimpl)>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop>>
  xvar>>xsimpl>>
  EVAL_TAC
QED

Definition nabs_def:
  nabs x = Num (ABS x)
End

val res = translate nabs_def;

val conv_xor_aux_arr = process_topdecs`
  fun conv_xor_aux_arr s xs =
  case xs of [] => s
  | x::xs =>
  let
    val v = nabs x
    val s = extend_s_arr s (v div 8 + 1)
    val u = flip_bit_arr s v in
    if x > 0 then
      conv_xor_aux_arr s xs
    else
      (flip_bit_arr s 0;
      conv_xor_aux_arr s xs)
  end` |> append_prog;

Theorem conv_xor_aux_arr_spec:
  ∀xs xsv cs csv.
  LIST_TYPE INT xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "conv_xor_aux_arr" (get_ml_prog_state()))
    [csv; xsv]
    (W8ARRAY csv cs)
    (POSTv v.
      SEP_EXISTS cs'.
      W8ARRAY v cs' *
      &(conv_xor_aux_list cs xs = cs'))
Proof
  Induct>>
  xcf "conv_xor_aux_arr" (get_ml_prog_state ())>>
  fs[conv_xor_aux_list_def,LIST_TYPE_def]>>xmatch
  >-
    (xvar>>xsimpl)>>
  rpt xlet_autop>>
  gvs[nabs_def]>>
  xlet_auto>>
  xlet_auto
  >- (gvs[extend_s_list_def]>>rw[])>>
  xlet_autop>>
  xif>>fs[]
  >- (xapp>>xsimpl)>>
  xlet_auto
  >- (
    gvs[extend_s_list_def]>>rw[]>>
    fs[flip_bit_list_def])>>
  xapp>>xsimpl
QED

val conv_rawxor_arr = process_topdecs`
  fun conv_rawxor_arr mv x =
  let
    val r = Word8Array.array (max 1 mv) w8z
    val u = flip_bit_arr r 0
    val r = conv_xor_aux_arr r x
  in
    Word8Array.substring r 0 (Word8Array.length r)
  end` |> append_prog;

Theorem conv_rawxor_arr_spec:
  NUM n nv ∧
  LIST_TYPE INT xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "conv_rawxor_arr" (get_ml_prog_state()))
    [nv; xsv]
    (emp)
    (POSTv v.
      &(STRING_TYPE (conv_rawxor_list n xs) v))
Proof
  xcf "conv_rawxor_arr" (get_ml_prog_state ())>>
  assume_tac w8z_v_thm>>
  xlet_autop>>
  rpt xlet_auto
  >- xsimpl>>
  xapp>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  simp[conv_rawxor_list_def,implode_def]>>
  rw[]>>
  `fromByte = (CHR o w2n)` by
    rw[FUN_EQ_THM,fromByte_def]>>
  simp[]
QED

val strxor_imp_cclause_arr = process_topdecs`
  fun strxor_imp_cclause_arr lno mv s c =
  let
    val t = conv_rawxor_arr mv c
    val res = strxor_c_arr s t
  in
    is_emp_xor_arr_aux lno res (Word8Array.length res)
  end` |> append_prog;

Theorem strxor_imp_cclause_arr_spec:
  NUM lno lnov ∧
  NUM n nv ∧
  LIST_TYPE INT xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "strxor_imp_cclause_arr" (get_ml_prog_state()))
    [lnov; nv; csv; xsv]
    (W8ARRAY csv cs)
    (POSTve
      (λv. &(strxor_imp_cclause_list n cs xs))
      (λe.
         &(Fail_exn e ∧ ¬strxor_imp_cclause_list n cs xs)))
Proof
  rw[]>>
  xcf "strxor_imp_cclause_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  xlet_autop>>
  xapp>>
  first_x_assum(irule_at Any)>>xsimpl>>
  gvs[strxor_imp_cclause_list_def]>>
  metis_tac[]
QED

val is_cfromx_arr = process_topdecs`
  fun is_cfromx_arr lno def fml is c =
  let
    val r = Word8Array.array def w8z
    val res = add_xors_aux_c_arr lno fml is r
  in
    strxor_imp_cclause_arr lno def res c
  end` |> append_prog

Theorem is_cfromx_arr_spec:
  NUM lno lnov ∧
  NUM def defv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) fmlls fmllsv ∧
  LIST_TYPE INT s sv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_cfromx_arr" (get_ml_prog_state()))
    [lnov; defv; fmlv; lsv; sv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        &(is_cfromx_list def fmlls ls s))
      (λe.
         ARRAY fmlv fmllsv *
         &(Fail_exn e ∧ ¬is_cfromx_list def fmlls ls s)))
Proof
  xcf "is_cfromx_arr" (get_ml_prog_state ())>>
  rw[is_cfromx_list_def]>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop
  >-
    xsimpl>>
  TOP_CASE_TAC>>gvs[unwrap_TYPE_def]>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

val check_xlrup_arr = process_topdecs`
  fun check_xlrup_arr lno xlrup cfml xfml def carr =
  case xlrup of
    Del cl =>
      (list_delete_arr cl cfml; (cfml, xfml, def, carr))
  | Rup n c i0 =>
      let val carr = resize_carr c carr
          val u = is_rup_arr lno cfml i0 c carr in
        (resize_update_arr (Some c) n cfml, xfml, def, carr)
      end
  | Xadd n rx i0 =>
      let
        val x = conv_rawxor_arr def rx
        val u = is_xor_arr lno def xfml i0 x
      in
        (cfml, resize_update_arr (Some x) n xfml,
          max def (String.size x), carr)
      end
  | Xdel xl =>
      (list_delete_arr xl xfml; (cfml, xfml, def, carr))
  | Cfromx n c i0 =>
    let val carr = resize_carr c carr
        val u = is_cfromx_arr lno def xfml i0 c in
      (resize_update_arr (Some c) n cfml, xfml, def, carr)
    end
  | _ =>
      raise Fail (format_failure lno ("Step not supported yet"))
    ` |> append_prog

val XLRUP_XLRUP_TYPE_def = fetch "-" "XLRUP_XLRUP_TYPE_def";

Theorem bounded_cfml_list_delete_list:
  ∀l fmlls. bounded_cfml n fmlls ⇒
  bounded_cfml n (list_delete_list l fmlls)
Proof
  Induct>>rw[list_delete_list_def]>>
  first_x_assum match_mp_tac>>
  fs[bounded_cfml_def,EVERY_EL,EL_LUPDATE]>>
  rw[]>>fs[]
QED

Theorem list_max_index_bounded_clause:
  ∀l.
  list_max_index l < n ⇒
  EVERY ($> n o index) l ∧ EVERY ($> n o index o $~) l
Proof
  simp[list_max_index_def]>>
  Induct>>rw[list_max_def,index_def]>>
  intLib.ARITH_TAC
QED

Theorem bounded_cfml_resize_update_list:
  bounded_cfml m fmlls ∧
  EVERY ($> m o index) l ∧ EVERY ($> m o index o $~) l ⇒
  bounded_cfml m (resize_update_list fmlls NONE (SOME l) n)
Proof
  rw[bounded_cfml_def,EVERY_MEM]>>
  drule MEM_resize_update_list>>rw[]>>simp[]
QED

Theorem LENGTH_resize_Clist:
  LENGTH Clist ≤ LENGTH (resize_Clist l Clist)
Proof
  rw[resize_Clist_def]
QED

Theorem bounded_cfml_leq:
  bounded_cfml n fmlls ∧ n ≤ m ⇒
  bounded_cfml m fmlls
Proof
  rw[bounded_cfml_def,EVERY_MEM]>>
  first_x_assum drule>>every_case_tac>>simp[]>>
  rw[]>>rpt(first_x_assum drule)>>fs[]
QED

Theorem EVERY_index_resize_Clist:
  EVERY ($> (LENGTH (resize_Clist ls Clist)) ∘ index) ls ∧
  EVERY ($> (LENGTH (resize_Clist ls Clist)) ∘ index o $~) ls
Proof
  rw[]>>
  simp[resize_Clist_def,list_max_index_def]>>
  qmatch_goalsub_abbrev_tac`list_max lss`>>
  qspec_then `lss` assume_tac list_max_max>>
  fs[EVERY_MEM,Abbr`lss`,MEM_MAP,PULL_EXISTS]>>
  ntac 2 strip_tac>>first_x_assum drule>>
  rw[]>>simp[index_def]>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem check_xlrup_arr_spec:
  NUM lno lnov ∧
  XLRUP_XLRUP_TYPE xlrup xlrupv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) xfmlls xfmllsv ∧
  NUM def defv ∧
  bounded_cfml (LENGTH Clist) cfmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_xlrup_arr" (get_ml_prog_state()))
    [lnov; xlrupv; cfmlv; xfmlv; defv; Carrv]
    (ARRAY cfmlv cfmllsv *
    ARRAY xfmlv xfmllsv *
    W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3 v4.
          &(v = Conv NONE [v1; v2; v3; v4]) *
          (* v1,v2 are pointers to the formula arrays *)
          (SEP_EXISTS cfmllsv' xfmllsv' Clist'.
            ARRAY v1 cfmllsv' *
            ARRAY v2 xfmllsv' *
            W8ARRAY v4 Clist' *
            &(
            unwrap_TYPE
              (λv fv.
                bounded_cfml (LENGTH Clist') (FST v) ∧
                LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
              (check_xlrup_list xlrup cfmlls xfmlls def Clist) cfmllsv' ∧
            unwrap_TYPE
              (λv fv.
                LIST_REL (OPTION_TYPE STRING_TYPE) ((FST o SND) v) fv)
              (check_xlrup_list xlrup cfmlls xfmlls def Clist) xfmllsv' ∧
            unwrap_TYPE
              (λv fv.
                NUM ((FST o SND o SND) v) fv)
              (check_xlrup_list xlrup cfmlls xfmlls def Clist) v3 ∧
            unwrap_TYPE ($= o SND o SND o SND)
              (check_xlrup_list xlrup cfmlls xfmlls def Clist) Clist' ∧
            LENGTH Clist ≤ LENGTH Clist'
            ))
      )
      (λe. ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
        &(Fail_exn e ∧
        check_xlrup_list xlrup cfmlls xfmlls def Clist = NONE)))
Proof
  rw[check_xlrup_list_def]>>
  xcf "check_xlrup_arr" (get_ml_prog_state ())>>
  TOP_CASE_TAC>>fs[XLRUP_XLRUP_TYPE_def]
  >- ( (* Del *)
    xmatch>>
    xlet_autop >>
    xcon>>xsimpl>>
    simp[unwrap_TYPE_def]>>
    metis_tac[bounded_cfml_list_delete_list])
  >- ( (* Rup *)
    xmatch>>
    xlet_autop>>
    xlet_auto
    >- (
      xsimpl>>
      metis_tac[bounded_cfml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist])
    >- xsimpl>>
    xlet_autop>>
    fs[unwrap_TYPE_def]>>
    xlet`(POSTv resv.
        W8ARRAY carrv Clist' *
        SEP_EXISTS cfmllsv'.
        ARRAY resv cfmllsv' *
        ARRAY xfmlv xfmllsv *
        &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update_list cfmlls NONE (SOME l) n) cfmllsv'))`
    >- (
      xapp_spec (resize_update_arr_spec |> Q.GEN `vty` |> ISPEC ``(LIST_TYPE INT)``)>>
      xsimpl>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`SOME l`>>simp[OPTION_TYPE_def])>>
    xcon>>xsimpl>>
    gvs[]>>
    metis_tac[bounded_cfml_resize_update_list,bounded_cfml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist])
  >- ( (* XAdd *)
    xmatch>>
    xlet_autop>>
    (* xlet_auto creates the wrong frame here *)
    xlet` POSTve
          (λv.
               ARRAY xfmlv xfmllsv * ARRAY cfmlv cfmllsv *
               W8ARRAY Carrv Clist *
               &is_xor_list def xfmlls l0 (conv_rawxor_list def l))
          (λe.
               ARRAY xfmlv xfmllsv * ARRAY cfmlv cfmllsv *
               &(Fail_exn e ∧
                ¬is_xor_list def xfmlls l0 (conv_rawxor_list def l)))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>simp[])
    >-
      xsimpl>>
    rpt xlet_autop>>
    xlet`(POSTv resv.
        W8ARRAY Carrv Clist *
        SEP_EXISTS xfmllsv'.
        ARRAY cfmlv cfmllsv *
        ARRAY resv xfmllsv' *
        &(LIST_REL (OPTION_TYPE STRING_TYPE) (resize_update_list xfmlls NONE (SOME (conv_rawxor_list def l)) n) xfmllsv'))`
    >- (
      xapp_spec (resize_update_arr_spec |> Q.GEN `vty` |> ISPEC ``STRING_TYPE``)>>
      xsimpl>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`SOME (conv_rawxor_list def l)`>>
      simp[OPTION_TYPE_def])>>
    xcon>>xsimpl>>
    gvs[unwrap_TYPE_def])
  >- ( (* Xdel *)
    xmatch>>
    xlet_autop >>
    xcon>>xsimpl>>
    simp[unwrap_TYPE_def]>>
    metis_tac[bounded_cfml_list_delete_list])
  >- ( (* Cfromx *)
    xmatch>>
    xlet_autop>>
    (* xlet_auto creates the wrong frame here *)
    xlet` POSTve
          (λv.
               ARRAY xfmlv xfmllsv * ARRAY cfmlv cfmllsv *
               W8ARRAY carrv (resize_Clist l Clist) *
               &is_cfromx_list def xfmlls l0 l)
          (λe.
               ARRAY xfmlv xfmllsv * ARRAY cfmlv cfmllsv *
               &(Fail_exn e ∧
                ¬is_cfromx_list def xfmlls l0 l))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>simp[])
    >-
      xsimpl>>
    xlet_autop>>
    xlet`(POSTv resv.
        W8ARRAY carrv (resize_Clist l Clist) *
        SEP_EXISTS cfmllsv'.
        ARRAY resv cfmllsv' *
        ARRAY xfmlv xfmllsv *
        &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update_list cfmlls NONE (SOME l) n) cfmllsv'))`
    >- (
      xapp_spec (resize_update_arr_spec |> Q.GEN `vty` |> ISPEC ``(LIST_TYPE INT)``)>>
      xsimpl>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`SOME l`>>simp[OPTION_TYPE_def])>>
    xcon>>xsimpl>>
    simp[unwrap_TYPE_def]>>
    metis_tac[bounded_cfml_resize_update_list,bounded_cfml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist])
  >- ( (* Unimplemented *)
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])
QED

Definition is_empty_def:
  is_empty ls = (ls = [])
End

val res = translate is_empty_def;

val contains_emp_arr_aux = (append_prog o process_topdecs)`
  fun contains_emp_arr_aux cfml i =
  if i = 0 then False
  else
    let val i1 = i - 1 in
    case Unsafe.sub cfml i1 of
      None => contains_emp_arr_aux cfml i1
    | Some v =>
      is_empty v orelse
      contains_emp_arr_aux cfml i1
    end`

Theorem contains_emp_arr_aux_spec:
  ∀cfmlls i iv cfmlv cfmllsv.
  NUM i iv ∧
  i <= LENGTH cfmlls ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls cfmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "contains_emp_arr_aux" (get_ml_prog_state()))
    [cfmlv; iv]
    (ARRAY cfmlv cfmllsv)
    (POSTv resv.
      &(BOOL (contains_emp_list_aux cfmlls i) resv) *
      ARRAY cfmlv cfmllsv)
Proof
  ho_match_mp_tac contains_emp_list_aux_ind>>rw[]>>
  xcf "contains_emp_arr_aux" (get_ml_prog_state ())>>
  xlet_autop>>xif
  >- (
    xcon>>xsimpl>>
    simp[Once contains_emp_list_aux_def]>>
    EVAL_TAC)>>
  rpt xlet_autop>>
  simp[Once contains_emp_list_aux_def]>>
  `LENGTH cfmlls = LENGTH cfmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xlet_autop>>
  `OPTION_TYPE (LIST_TYPE INT) (EL (i-1) cfmlls) (EL (i-1) cfmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  simp[list_lookup_def]>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>xsimpl>>
    fs[list_lookup_def])>>
  xmatch>>
  xlet_auto
  >-
    (xsimpl>>simp[EqualityType_NUM_BOOL])>>
  xlog>>xsimpl>>
  fs[is_empty_def]>>rw[]>>
  last_x_assum assume_tac>>
  xapp>>xsimpl>>
  fs[list_lookup_def]
QED

val contains_emp_arr = (append_prog o process_topdecs)`
  fun contains_emp_arr cfml =
  contains_emp_arr_aux cfml (Array.length cfml)`

Theorem contains_emp_arr_spec:
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls cfmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "contains_emp_arr" (get_ml_prog_state()))
    [cfmlv]
    (ARRAY cfmlv cfmllsv)
    (POSTv resv.
      &(BOOL (contains_emp_list cfmlls) resv) *
      ARRAY cfmlv cfmllsv)
Proof
  xcf "contains_emp_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  fs[contains_emp_list_def,LIST_REL_EL_EQN]
QED

open mlintTheory;

(* TODO: Mostly copied from mlintTheory *)
val result = translate fromChar_unsafe_def;

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail b n str mul acc =
  if n ≤ b then acc
  else
    let m = sub_nocheck n 1 in
    fromChars_range_unsafe_tail b m str (mul * 10)
      (acc + fromChar_unsafe (strsub str m) * mul)
Termination
  WF_REL_TAC`measure (λ(b,n,_). n)`>>
  rw[sub_nocheck_def]
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
  simp[Once fromChars_range_unsafe_tail_def,ADD1,fromChars_range_unsafe_def,sub_nocheck_def]>>
  fs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s =
  fromChars_range_unsafe_tail l (n+l) s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;
val result = translate fromChars_range_unsafe_alt;

val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

Triviality fromChars_unsafe_ind:
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

val result = translate xlrup_parsingTheory.fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
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
  simp[sub_nocheck_def]>>eq_tac>>rw[ADD1]>>
  gvs[]
QED

val fromchars_range_unsafe_side_def = fetch "-" "fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def,fromchars_range_unsafe_tail_side_def]
QED

val fromString_unsafe_side = Q.prove(
  `∀x. fromstring_unsafe_side x = T`,
  Cases
  \\ rw[fromstring_unsafe_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_unsafe_side_thm
  \\ rw[]) |> update_precondition;

val _ = translate cnf_xorTheory.blanks_def;
val _ = translate cnf_xorTheory.tokenize_def;

val _ = translate is_lowercase_def;
val _ = translate tokenize_fast_def;

val tokenize_fast_side = Q.prove(
  `∀x. tokenize_fast_side x = T`,
  EVAL_TAC >> fs[]) |> update_precondition;

val _ = translate parse_until_zero_def;
val _ = translate parse_until_zero_nn_def;

val _ = translate parse_rest_def;
val _ = translate parse_id_rest_def;
val _ = translate parse_del_def;
val _ = translate parse_xlrup_def;

(* Hooking up to the parser and stuff *)
val parse_and_run_list_def = Define`
  parse_and_run_list cfml xfml def Clist l =
  case parse_xlrup l of
    NONE => NONE
  | SOME xlrup =>
    check_xlrup_list xlrup cfml xfml def Clist`

val parse_and_run_arr = process_topdecs`
  fun parse_and_run_arr lno cfml xfml def carr l =
  case parse_xlrup l of
    None => raise Fail (format_failure lno "failed to parse line")
  | Some xlrup =>
    check_xlrup_arr lno xlrup cfml xfml def carr` |> append_prog

Theorem parse_and_run_arr_spec:
  NUM lno lnov ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) l lv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) xfmlls xfmllsv ∧
  NUM def defv ∧
  bounded_cfml (LENGTH Clist) cfmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_and_run_arr" (get_ml_prog_state()))
    [lnov; cfmlv; xfmlv; defv; Carrv; lv]
    (ARRAY cfmlv cfmllsv *
    ARRAY xfmlv xfmllsv *
    W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3 v4.
          &(v = Conv NONE [v1; v2; v3; v4]) *
          (* v1,v2 are pointers to the formula arrays *)
          (SEP_EXISTS cfmllsv' xfmllsv' Clist'.
            ARRAY v1 cfmllsv' *
            ARRAY v2 xfmllsv' *
            W8ARRAY v4 Clist' *
            &(
            unwrap_TYPE
              (λv fv.
                bounded_cfml (LENGTH Clist') (FST v) ∧
                LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
              (parse_and_run_list cfmlls xfmlls def Clist l) cfmllsv' ∧
            unwrap_TYPE
              (λv fv.
                LIST_REL (OPTION_TYPE STRING_TYPE) ((FST o SND) v) fv)
              (parse_and_run_list cfmlls xfmlls def Clist l) xfmllsv' ∧
            unwrap_TYPE
              (λv fv.
                NUM ((FST o SND o SND) v) fv)
              (parse_and_run_list cfmlls xfmlls def Clist l) v3 ∧
            unwrap_TYPE ($= o SND o SND o SND)
              (parse_and_run_list cfmlls xfmlls def Clist l) Clist' ∧
            LENGTH Clist ≤ LENGTH Clist'
            ))
      )
      (λe. ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
        &(Fail_exn e ∧
        parse_and_run_list cfmlls xfmlls def Clist l = NONE)))
Proof
  rw[parse_and_run_list_def]>>
  xcf "parse_and_run_arr" (get_ml_prog_state ())>>
  assume_tac (fetch "-" "blanks_v_thm")>>
  rpt xlet_autop >>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[unwrap_TYPE_def,Fail_exn_def]>>
    metis_tac[])>>
  xapp>>fs[]>>
  xsimpl>>
  metis_tac[]
QED

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]`;

val r = translate noparse_string_def;

(*
val nocheck_string_def = Define`
  nocheck_string = strlit "cake_xlrup: XLRUP checking failed.\n"`;

val r = translate nocheck_string_def;
*)

(* TODO: possibly make this dump every 10000 lines or so *)
val check_unsat'' = process_topdecs `
  fun check_unsat'' fd lno cfml xfml def carr =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => (cfml, xfml)
    | Some l =>
    case parse_and_run_arr lno cfml xfml def carr l of
      (cfml',xfml',def',carr') =>
      check_unsat'' fd (lno+1) cfml' xfml' def' carr'`
      |> append_prog;

(* This says what happens to the STDIO *)
val check_unsat''_def = Define`
  (check_unsat'' fd cfml xfml def Clist fs [] =
    STDIO (fastForwardFD fs fd)) ∧
  (check_unsat'' fd cfml xfml def Clist fs (ln::ls) =
    case parse_and_run_list cfml xfml def Clist (toks_fast ln) of
      NONE => STDIO (lineForwardFD fs fd)
    | SOME (cfml', xfml', def', Clist') =>
      check_unsat'' fd cfml' xfml' def' Clist'
        (lineForwardFD fs fd) ls)`

(* This says what happens to cfml, xfml *)
val parse_and_run_file_list_def = Define`
  (parse_and_run_file_list [] cfml xfml def Clist =
    SOME (cfml, xfml)) ∧
  (parse_and_run_file_list (x::xs) cfml xfml def Clist =
    case parse_and_run_list cfml xfml def Clist (toks_fast x) of
      NONE => NONE
    | SOME (cfml', xfml', def',Clist') =>
    parse_and_run_file_list xs cfml' xfml' def' Clist')`

Theorem parse_and_run_file_list_eq:
  ∀ls cfml xfml def Clist.
  parse_and_run_file_list ls cfml xfml def Clist =
  case parse_xlrups ls of
    NONE => NONE
  | SOME xlrups =>
    OPTION_MAP (λ(a,b,c). (a,b))
      (check_xlrups_list xlrups cfml xfml def Clist)
Proof
  Induct>>
  fs[parse_and_run_list_def,parse_xlrups_def,parse_and_run_file_list_def,check_xlrups_list_def]>>
  rw[]>>
  every_case_tac>>fs[toks_fast_def]>>
  simp[check_xlrups_list_def]
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
val tokenize_fast_v_thm = theorem "tokenize_fast_v_thm";

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,cnf_xorTheory.blanks_def] ;

Theorem check_unsat''_spec:
  !lines fs cfmlv cfmlls cfmllsv xfmlv xfmlls xfmllsv Clist Carrv lno lnov def defv.
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) xfmlls xfmllsv ∧
  NUM def defv ∧
  bounded_cfml (LENGTH Clist) cfmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; cfmlv; xfmlv; defv; Carrv]
    (STDIO fs * ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv *
      W8ARRAY Carrv Clist * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k v1 v2.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
           &(v = Conv NONE [v1; v2]) *
           (SEP_EXISTS cfmllsv' xfmllsv'.
            ARRAY v1 cfmllsv' *
            ARRAY v2 xfmllsv' *
            &(unwrap_TYPE
              (λv fv.
              LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                 (parse_and_run_file_list lines cfmlls xfmlls def Clist) cfmllsv' ∧
              unwrap_TYPE
              (λv fv.
              LIST_REL (OPTION_TYPE STRING_TYPE) (SND v) fv)
                 (parse_and_run_file_list lines cfmlls xfmlls def Clist) xfmllsv'
              ))
      )
      (λe.
         SEP_EXISTS k cfmlv cfmllsv xfmlv xfmllsv lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           ARRAY cfmlv cfmllsv *
           ARRAY xfmlv xfmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list lines cfmlls xfmlls def Clist = NONE)))
Proof
  Induct \\ rw []
  \\ xcf "check_unsat''" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY cfmlv cfmllsv *
                ARRAY xfmlv xfmllsv *
                W8ARRAY Carrv Clist *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv * W8ARRAY Carrv Clist’
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
                ARRAY cfmlv cfmllsv *
                ARRAY xfmlv xfmllsv *
                W8ARRAY Carrv Clist *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv * W8ARRAY Carrv Clist’
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_fast_def])
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
    qexists_tac`cfmlv`>>qexists_tac`cfmllsv`>>
    qexists_tac`xfmlv`>>qexists_tac`xfmllsv`>>
    xsimpl>>
    qexists_tac ‘lines’>>
    xsimpl>>
    metis_tac[])>>
  rveq \\ fs [] >>
  xmatch>>
  xlet_autop >>
  xapp>>xsimpl>>
  fs [unwrap_TYPE_def]>>
  rpt(first_x_assum (irule_at Any))>>
  xsimpl>>
  qexists_tac ‘(forwardFD fs fd k)’>> xsimpl>>
  simp[parse_and_run_file_list_def]>>
  every_case_tac>> gvs[]>>
  rw[]>>gvs[forwardFD_o]
  >-
    (qexists_tac`k+x`>>xsimpl)>>
  qexists_tac ‘k+x’ \\ xsimpl >>
  rename1`INSTREAM_LINES _ _ A _ * ARRAY B C * ARRAY D E`>>
  qexists_tac`B`>>
  qexists_tac`C`>>
  qexists_tac`D`>>
  qexists_tac`E`>>
  qexists_tac`A`>>
  xsimpl
QED

(* We don't really care about the STDIO afterwards long as it gets closed *)
Theorem check_unsat''_eq:
  ∀ls fd cfml xfml fs def Clist.
  ∃n.
    check_unsat'' fd cfml xfml def Clist fs ls =
    case parse_and_run_file_list ls cfml xfml def Clist of
     NONE => STDIO (forwardFD fs fd n)
   | SOME _ => STDIO (fastForwardFD fs fd)
Proof
  Induct>>rw[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC
  >-
    metis_tac[lineForwardFD_forwardFD]>>
  PairCases_on`x`>>fs[]>>
  first_x_assum(qspecl_then[`fd`,`x0`,`x1`,`lineForwardFD fs fd`,`x2`,`x3`] strip_assume_tac)>>
  simp[]>>
  qspecl_then [`fs`,`fd`] strip_assume_tac lineForwardFD_forwardFD>>
  simp[forwardFD_o]>>
  metis_tac[]
QED

(* Implements the general unsat checking routine that can be called
   in several different ways
  Returns: Inl (error string)
  Otherwise: Inr (true/false result of checking clause inclusion)
*)
val notfound_string_def = Define`
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]`;

val r = translate notfound_string_def;

val check_unsat' = process_topdecs `
  fun check_unsat' cfml xfml def fname n =
  let
    val fd = TextIO.b_openIn fname
    val carr = Word8Array.array n w8z
    val chk = Inr (check_unsat'' fd 0 cfml xfml def carr)
      handle Fail s => Inl s
    val close = TextIO.b_closeIn fd;
  in
    case chk of
      Inl s => Inl s
    | Inr res =>
      (case res of (cfml', xfml') =>
      Inr (contains_emp_arr cfml'))
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

(* TODO: COPIED from readerProg, should be moved *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

Theorem check_unsat'_spec:
  NUM n nv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls cfmllsv ∧
  LIST_REL (OPTION_TYPE STRING_TYPE) xfmlls xfmllsv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  NUM def defv ∧
  bounded_cfml n cfmlls
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [cfmlv; xfmlv; defv; fv; nv]
  (STDIO fs * ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE BOOL)
      (if inFS_fname fs f then
        (case parse_xlrups (all_lines fs f) of
         SOME xlrup =>
           (case check_xlrups_list xlrup cfmlls xfmlls def (REPLICATE n w8z) of
             NONE => INL err
           | SOME (cfml', xfml') =>
            INR (contains_emp_list cfml'))
        | NONE => INL err)
      else
        INL err
      ) v)
Proof
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
      ARRAY cfmlv cfmllsv * ARRAY xfmlv xfmllsv`
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
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  `WORD8 w8z w8z_v` by fs[w8z_v_thm]>>
  xlet_autop >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qabbrev_tac`Clist = REPLICATE n w8z`>>
  xlet`POSTv resv.
   SEP_EXISTS v0 v1 v2 cfmllsv' cfmlv' xfmllsv' xfmlv' k rest.
    STDIO (forwardFD fss (nextFD fs) k) *
    INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
    ARRAY cfmlv' cfmllsv' *
    ARRAY xfmlv' xfmllsv' *
    &(
      case
        parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def (REPLICATE n w8z)
      of
        NONE => resv =
          Conv (SOME (TypeStamp "Inl" 4)) [v0] ∧ ∃s. STRING_TYPE s v0
      | SOME(cfmlls',xfmlls') =>
        resv = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]] ∧
        v1 = cfmlv' ∧
        v2 = xfmlv' ∧
        LIST_REL (OPTION_TYPE (LIST_TYPE INT)) cfmlls' cfmllsv' ∧
        LIST_REL (OPTION_TYPE STRING_TYPE) xfmlls' xfmllsv'
    )`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS cfmlv cfmllsv xfmlv xfmllsv rest k.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY cfmlv cfmllsv *
          ARRAY xfmlv xfmllsv *
          &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def Clist = NONE)`
      >- (
        (* this used to be an xauto_let .. sigh *)
        xlet `POSTe e.
         SEP_EXISTS k cfmlv cfmllsv xfmlv xfmllsv lines'.
           STDIO (forwardFD fss (nextFD fs) k) *
           INSTREAM_LINES (nextFD fs) is lines' (forwardFD fss (nextFD fs) k) *
           ARRAY cfmlv cfmllsv *
           ARRAY xfmlv xfmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def Clist = NONE)`
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
          \\ rw[]
          \\ qexists_tac `x`
          \\ rename [`_ * INSTREAM_LINES _ _ xxx _ * ARRAY a1 a2 * ARRAY b1 b2`]
          \\ qexists_tac `a1`
          \\ qexists_tac `a2`
          \\ qexists_tac `b1`
          \\ qexists_tac `b2`
          \\ qexists_tac `xxx`
          \\ xsimpl)>>
        fs[unwrap_TYPE_def]>>
        xsimpl>>
        rw[]>>
        rename [`_ * INSTREAM_LINES _ _ xxx _ * ARRAY a1 a2 * ARRAY b1 b2`]
        \\ qexists_tac `a1`
        \\ qexists_tac `a2`
        \\ qexists_tac `b1`
        \\ qexists_tac `b2`
        \\ qexists_tac `xxx`
        \\ qexists_tac `x`
        \\ xsimpl)>>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>> simp[]>>
      rename [`_ * _ * ARRAY a1 a2 * ARRAY b1 b2`]>>
      qexists_tac `a2` >>
      qexists_tac `a1` >>
      qexists_tac `b2` >>
      qexists_tac `b1` >>
      qexists_tac `k` >>
      qexists_tac `rest` >> xsimpl) >>
    xhandle`(POSTv v.
        SEP_EXISTS v1 v2 k rest.
         STDIO (forwardFD fss (nextFD fs) k) *
         INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
         &(v = Conv (SOME (TypeStamp "Inr" 4)) [Conv NONE [v1; v2]]) *
         (SEP_EXISTS cfmllsv' xfmllsv'.
           ARRAY v1 cfmllsv' *
           ARRAY v2 xfmllsv' *
           &(unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                (parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def Clist) cfmllsv' ∧
             unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE STRING_TYPE) (SND v) fv)
                (parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def Clist) xfmllsv')))`
    >- (
        xlet `POSTv v.
           SEP_EXISTS k v1 v2.
               STDIO (forwardFD fss (nextFD fs) k) *
               INSTREAM_LINES (nextFD fs) is [] (forwardFD fss (nextFD fs) k) *
               &(v = Conv NONE [v1; v2]) *
               (SEP_EXISTS cfmllsv' xfmllsv'.
                    ARRAY v1 cfmllsv' *
                    ARRAY v2 xfmllsv' *
                    &(unwrap_TYPE
                      (λv fv.
                           LIST_REL (OPTION_TYPE (LIST_TYPE INT))
                             (FST v) fv)
                      (parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def Clist) cfmllsv' ∧
                      unwrap_TYPE
                      (λv fv.
                           LIST_REL (OPTION_TYPE STRING_TYPE)
                             (SND v) fv)
                      (parse_and_run_file_list (all_lines fs f) cfmlls xfmlls def Clist) xfmllsv'))`
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
        rename [`INSTREAM_LINES _ _ rr`] \\ qexists_tac `rr` \\ xsimpl) >>
      xsimpl>>simp[unwrap_TYPE_def]>>
      Cases_on`x`>>fs[]>>rw[]>>xsimpl >>
      rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
      rename [`INSTREAM_LINES _ _ rr`] \\ qexists_tac `rr` \\ xsimpl)>>
  qspecl_then [`all_lines fs f`,`cfmlls`,`xfmlls`,`def`,`Clist`] strip_assume_tac parse_and_run_file_list_eq>>
  fs[]>>rw[]>>
  pop_assum kall_tac >>
  xlet `POSTv v. STDIO fs *
    ARRAY cfmlv' cfmllsv' * ARRAY xfmlv' xfmllsv'`
  THEN1
   (xapp_spec b_closeIn_spec_lines >>
    rename [`_ * _ * ARRAY a1 a2 * ARRAY b1 b2`] >>
    qexists_tac `ARRAY a1 a2 * ARRAY b1 b2` >>
    qexists_tac `rest` >>
    qexists_tac `forwardFD fss (nextFD fs) k` >>
    qexists_tac `nextFD fs` >>
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
  Cases_on`parse_xlrups (all_lines fs f)`>> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon >> xsimpl >>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  TOP_CASE_TAC>> fs[]
  >- (
    xmatch >> xcon >>
    xsimpl>> simp[SUM_TYPE_def] >> metis_tac[])>>
  PairCases_on`x'`>>gvs[]>>
  xmatch >> fs[]>>
  xmatch >> fs[]>>
  xlet_autop>>
  xcon >> xsimpl>>
  simp[SUM_TYPE_def] >> gvs[]
QED

val fill_arr = process_topdecs`
  fun fill_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_arr (resize_update_arr (Some v) i arr) (i+1) vs` |> append_prog

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv i iv.
  NUM i iv ∧
  LIST_TYPE a ls lsv ∧
  LIST_REL (OPTION_TYPE a) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE a)
    (FOLDL (λacc (i,v).  resize_update_list acc NONE (SOME v) i) arrls (enumerate i ls)) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop >>
  xlet`(POSTv resv.
      SEP_EXISTS cfmllsv'.
      ARRAY resv cfmllsv' *
      &(LIST_REL (OPTION_TYPE a) (resize_update_list arrls NONE (SOME h) i) cfmllsv') )`
  >- (
    xapp >> xsimpl>>
    simp[OPTION_TYPE_def] ) >>
  xapp>>
  xsimpl
QED

Theorem all_distinct_map_fst_rev:
  ALL_DISTINCT (MAP FST ls) ⇔ ALL_DISTINCT (MAP FST (REVERSE ls))
Proof
  fs[MAP_REVERSE]
QED

Theorem LENGTH_FOLDR_resize_update_list1:
  ∀ll.
  LENGTH (FOLDR (λx acc. (λ(i,v). resize_update_list acc NONE (SOME v) i) x) (REPLICATE n NONE) ll) ≥ n
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once resize_update_list_def]
QED

Theorem LENGTH_FOLDR_resize_update_list2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). resize_update_list acc NONE (SOME v) i) x) (REPLICATE n NONE) ll)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once resize_update_list_def]
  >- (
    first_x_assum drule>>
    simp[])>>
  first_x_assum drule>>simp[]
QED

Theorem FOLDL_resize_update_list_lookup:
  ∀ls.
  ALL_DISTINCT (MAP FST ls) ⇒
  ∀x.
  x < LENGTH (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  =
  ALOOKUP ls x
Proof
  simp[Once (GSYM EVERY_REVERSE), Once (GSYM MAP_REVERSE)]>>
  simp[FOLDL_FOLDR_REVERSE]>>
  simp[GSYM alookup_distinct_reverse]>>
  simp[Once all_distinct_map_fst_rev]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE ls`>>
  pop_assum kall_tac>>
  Induct_on`ll`>-
    simp[EL_REPLICATE]>>
  simp[FORALL_PROD]>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once resize_update_list_def]>>
  strip_tac>>
  simp[Once resize_update_list_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC >> simp[]>>
  simp[EL_APPEND_EQN]>>rw[]>>
  simp[EL_REPLICATE]>>
  CCONTR_TAC>>fs[]>>
  Cases_on`ALOOKUP ll x`>>fs[]>>
  drule ALOOKUP_MEM>>
  strip_tac>>
  drule LENGTH_FOLDR_resize_update_list2>>
  simp[]>>
  metis_tac[]
QED

Theorem SORTED_REVERSE:
  transitive P ⇒
  (SORTED P (REVERSE ls) ⇔ SORTED (λx y. P y x)  ls)
Proof
  rw[]>>
  DEP_REWRITE_TAC [SORTED_EL_LESS]>>
  fs[]>>
  CONJ_TAC>- (
    fs[transitive_def]>>
    metis_tac[])>>
  simp[EL_REVERSE]>>
  rw[EQ_IMP_THM]
  >- (
    first_x_assum (qspecl_then [`LENGTH ls-n-1`,`LENGTH ls-m-1`] mp_tac)>>
    simp[GSYM ADD1])>>
  first_x_assum match_mp_tac>>
  simp[]>>
  intLib.ARITH_TAC
QED

Theorem fml_rel_FOLDL_resize_update_list:
  fml_rel (build_fml k fml)
  (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
Proof
  rw[fml_rel_def]>>
  reverse IF_CASES_TAC
  >- (
    fs[lookup_build_fml]>>
    CCONTR_TAC>>fs[]>>
    `MEM x (MAP FST (enumerate k fml))` by
      (fs[MAP_FST_enumerate,MEM_GENLIST]>>
      intLib.ARITH_TAC)>>
    fs[MEM_MAP]>>
    fs[FOLDL_FOLDR_REVERSE]>>
    `MEM y (REVERSE (enumerate k fml))` by
      fs[MEM_REVERSE]>>
    drule LENGTH_FOLDR_resize_update_list2>>
    simp[]>>
    metis_tac[]) >>
  DEP_REWRITE_TAC [FOLDL_resize_update_list_lookup]>>
  simp[]>>
  CONJ_TAC >-
    simp[ALL_DISTINCT_MAP_FST_enumerate]>>
  simp[lookup_build_fml,ALOOKUP_enumerate]
QED

Theorem wf_cfml_build_fml:
  EVERY wf_clause ls ⇒
  wf_cfml (build_fml kc ls)
Proof
  simp[wf_cfml_def,values_build_fml,EVERY_MEM]
QED

(* TODO: Update for XORs *)
Theorem check_xlrups_unsat_list_sound:
  check_xlrups_unsat_list xlrups
    (FOLDL (λacc (i,v).
      resize_update_list acc NONE (SOME v) i) (REPLICATE nc NONE)
        (enumerate kc cfml))
    (FOLDL (λacc (i,v).
      resize_update_list acc NONE (SOME v) i) (REPLICATE nx NONE)
        (enumerate kx xfml))
    def
    Clist ∧
  EVERY wf_clause cfml ∧
  EVERY wf_xlrup xlrups ∧
  EVERY ($= w8z) Clist ⇒
  ¬ isatisfiable (set cfml,set xfml)
Proof
  rw[check_xlrups_unsat_list_def]>>
  every_case_tac>>fs[]>>
  Cases_on`r`>>fs[]>>
  assume_tac (GEN_ALL fml_rel_FOLDL_resize_update_list |>
    INST_TYPE [alpha |-> ``:int list``] |>
    Q.SPECL [`nc`,`kc`,`cfml`])>>
  assume_tac (GEN_ALL fml_rel_FOLDL_resize_update_list |>
    INST_TYPE [alpha |-> ``:mlstring``] |>
    Q.SPECL [`nx`,`kx`,`xfml`])>>
  drule fml_rel_check_xlrups_list>>
  rpt (disch_then (drule_at Any))>>
  simp[wf_cfml_build_fml]>>
  rw[]>>
  match_mp_tac (check_xlrups_unsat_sound |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL)>>
  simp[check_xlrups_unsat_def]>>
  qexists_tac`xlrups`>>
  qexists_tac`kx`>>
  qexists_tac`def`>>
  qexists_tac`kc`>>
  simp[]>>
  metis_tac[fml_rel_contains_emp_list]
QED

Definition rev_enum_def:
  rev_enum (s:num) (e:num) acc =
  if s < e then
    rev_enum (s+1) e (s::acc)
  else
    acc
Termination
  WF_REL_TAC`measure (λ(s,e,acc). e-s)`
End

Theorem rev_enum_rev_enumerate:
  ∀cfml k acc.
  rev_enum k (LENGTH cfml + k) acc =
  REVERSE (MAP FST (enumerate k cfml)) ++ acc
Proof
  Induct>>rw[Once rev_enum_def]>>
  simp[miscTheory.enumerate_def]>>
  first_x_assum(qspec_then`k+1` mp_tac)>>
  simp[ADD1]
QED

val _ = translate rev_enum_def;

Definition rev_enum_full_def:
  rev_enum_full k cfml =
  rev_enum k (LENGTH cfml + k) []
End

Theorem rev_enum_full_rev_enumerate:
  rev_enum_full k cfml =
  REVERSE (MAP FST (enumerate k cfml))
Proof
  rw[rev_enum_full_def,rev_enum_rev_enumerate]
QED

val _ = translate rev_enum_full_def;

val _ = export_theory();
