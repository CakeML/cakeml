(*
  This refines ccnf_list to use arrays
*)
Theory ccnf_arrayProg
Ancestors
  UnsafeProg UnsafeProof
  ccnf ccnf_list mlint syntax_helper ccnf_arith
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

Theorem NUM_ARRAY_alloc_zero_spec:
  ∀n nv zv.
  NUM n nv ∧ NUM 0 zv ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "Array.array" (get_ml_prog_state()))
    [nv; zv]
    emp (POSTv av. NUM_ARRAY av (REPLICATE n 0))
Proof
  rw[NUM_ARRAY_def]>>
  xapp>>xsimpl>>
  qexists_tac`n`>>
  simp[LIST_REL_REPLICATE_same]
QED

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

(* Carried by the Fail exception a checker step raises *)
Definition format_failure_def:
  format_failure (lno:num) s =
  «c Checking failed at line: » ^ toString lno ^ «. Reason: » ^ s ^ «\n»
End

val res = translate format_failure_def;

(* Used to state a spec whose result is only meaningful when the
  underlying list-level function succeeds *)
Definition unwrap_TYPE_def:
  unwrap_TYPE P x y = ∃z. x = SOME z ∧ P z y
End

Definition uvsub_def:
  uvsub v n = sub_unsafe v n
End

val res = translate uvsub_def;

val uvsub_side_def = fetch "-" "uvsub_side_def";

(* The absent-clause sentinel, allocated once *)
val vcc_none_v_thm = translate vcc_none_def;

Definition int_eq_0_def:
  int_eq_0 (i:int) ⇔ i = 0
End

val res = translate int_eq_0_def;

Quote add_cakeml:
  fun all_assigned_arr carr b k v i =
  if i = 0 then True
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 v
      val c = uvsub v i1
    in
      if Unsafe.Arith.ltWitness c 0 carr
      then
        (if Unsafe.Arith.= (Unsafe.sub carr (Unsafe.Arith.subWitness 0 c carr)) b
        then
          all_assigned_arr carr b k v i1
        else
          if Unsafe.Arith.eqWitness c k carr then all_assigned_arr carr b k v i1
          else False)
      else
        (if Unsafe.Arith.< b (Unsafe.sub carr c)
        then
          all_assigned_arr carr b k v i1
        else
          if Unsafe.Arith.eqWitness c k carr then all_assigned_arr carr b k v i1
          else False)
    end
End

Theorem uvsub_eq_sub[simp]:
  uvsub v n = sub v n
Proof
  simp[uvsub_def,oneline mlvectorTheory.sub_unsafe_def,oneline mlvectorTheory.sub_def]
QED


Theorem all_assigned_arr_spec:
  ∀Clist b k vec i bv kv vecv iv Carrv.
  NUM b bv ∧ stamps_ok Clist b ∧
  INT k kv ∧ Num (ABS k) < LENGTH Clist ∧
  vcclause_TYPE vec vecv ∧
  NUM i iv ∧
  all_assigned_list' Clist b k vec i = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_assigned_arr" (get_ml_prog_state()))
    [Carrv; bv; kv; vecv; iv]
    (NUM_ARRAY Carrv Clist)
    (POSTv v.
      NUM_ARRAY Carrv Clist *
      &BOOL res v)
Proof
  ho_match_mp_tac all_assigned_list'_ind>>
  rw[]>>
  drule_then strip_assume_tac stamps_ok_bounds>>
  drule_then assume_tac all_assigned_list'_lit>>
  qpat_x_assum`all_assigned_list' _ _ _ _ _ = _` mp_tac>>
  simp[Once all_assigned_list'_def]>>
  strip_tac>>
  xcf "all_assigned_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>fs[]
  >- (xcon>>xsimpl)>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[uvsub_side_def])>>
  xlet_auto_spec (SOME int_lt_numarr_spec)
  >- xsimpl>>
  xif>>fs[]
  >- (
    xlet_auto_spec (SOME int_sub_numarr_spec)
    >- xsimpl>>
    xlet`POSTv sv. NUM_ARRAY Carrv Clist *
      &NUM (EL (Num (-sub vec (i-1))) Clist) sv`
    >- (
      simp[NUM_ARRAY_def]>>xpull>>
      xapp>>xsimpl>>
      qexists_tac`Num (-sub vec (i-1))`>>
      gvs[LIST_REL_EL_EQN,NUM_def,INT_def])>>
    xlet_auto_spec (SOME num_eq_spec)
    >- xsimpl>>
    xif>>fs[]
    >- (xapp>>xsimpl)>>
    xlet_auto_spec (SOME int_eq_numarr_spec)
    >- xsimpl>>
    xif>>fs[]
    >- (xapp>>xsimpl)>>
    xcon>>
    xsimpl)
  >- (
    xlet`POSTv sv. NUM_ARRAY Carrv Clist *
      &NUM (EL (Num (sub vec (i-1))) Clist) sv`
    >- (
      simp[NUM_ARRAY_def]>>xpull>>
      xapp>>xsimpl>>
      qexists_tac`Num (sub vec (i-1))`>>
      gvs[LIST_REL_EL_EQN,NUM_def,INT_def,integerTheory.INT_NOT_LT])>>
    xlet_auto_spec (SOME num_lt_spec)
    >- xsimpl>>
    xif>>fs[]
    >- (xapp>>xsimpl)>>
    xlet_auto_spec (SOME int_eq_numarr_spec)
    >- xsimpl>>
    xif>>fs[]
    >- (xapp>>xsimpl)>>
    xcon>>
    xsimpl)
QED

Quote add_cakeml:
  fun delete_literals_sing_arr lno carr b v i =
  if i = 0 then True
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 v
      val c = uvsub v i1
    in
      if Unsafe.Arith.ltWitness c 0 carr
      then
        let
          val nc = Unsafe.Arith.subWitness 0 c carr
        in
          if Unsafe.Arith.= (Unsafe.sub carr nc) b
          then
            delete_literals_sing_arr lno carr b v i1
          else
            if all_assigned_arr carr b c v i1
            then
              (Unsafe.update carr nc (Unsafe.Arith.+ b 1); False)
            else
              raise Fail (format_failure lno "clause not empty or singleton after reduction")
        end
      else
        if Unsafe.Arith.< b (Unsafe.sub carr c)
        then
          delete_literals_sing_arr lno carr b v i1
        else
          if all_assigned_arr carr b c v i1
          then
            (Unsafe.update carr c b; False)
          else
            raise Fail (format_failure lno "clause not empty or singleton after reduction")
    end
End

Theorem delete_literals_sing_arr_spec:
  ∀Clist b vec i bv vecv iv Carrv res.
  NUM lno lnov ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  VECTOR_TYPE INT vec vecv ∧
  NUM i iv ∧
  delete_literals_sing_list' Clist b vec i = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_literals_sing_arr" (get_ml_prog_state()))
    [lnov; Carrv; bv; vecv; iv]
    (NUM_ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS b' Clist'.
        NUM_ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        NUM_ARRAY Carrv Clist *
        &(Fail_exn e ∧ res = NONE))
    )
Proof
  ho_match_mp_tac delete_literals_sing_list'_ind>>
  rw[]>>
  drule_then strip_assume_tac stamps_ok_bounds>>
  drule_then assume_tac delete_literals_sing_list'_lit>>
  qpat_x_assum`delete_literals_sing_list' _ _ _ _ = _` mp_tac>>
  simp[Once delete_literals_sing_list'_def]>>
  strip_tac>>
  xcf "delete_literals_sing_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>gvs[]
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[uvsub_side_def])>>
  xlet_auto_spec (SOME int_lt_numarr_spec)
  >- xsimpl>>
  xif>>gvs[]
  >- (
    xlet_auto_spec (SOME int_sub_numarr_spec)
    >- xsimpl>>
    xlet`POSTv sv. NUM_ARRAY Carrv Clist *
      &NUM (EL (Num (-sub vec (i-1))) Clist) sv`
    >- (
      simp[NUM_ARRAY_def]>>xpull>>
      xapp>>xsimpl>>
      qexists_tac`Num (-sub vec (i-1))`>>
      gvs[LIST_REL_EL_EQN,NUM_def,INT_def])>>
    xlet_auto_spec (SOME num_eq_spec)
    >- xsimpl>>
    xif>>gvs[]
    >- (xapp>>xsimpl)>>
    rpt xlet_autop>>
    xif>>gvs[]
    >- (
      xlet_auto_spec (SOME num_add_spec)
      >- xsimpl>>
      xlet`POSTv uv. NUM_ARRAY Carrv
        (LUPDATE (b+1) (Num (-sub vec (i-1))) Clist)`
      >- (
        simp[NUM_ARRAY_def]>>xpull>>
        xapp>>xsimpl>>
        qexists_tac`Num (-sub vec (i-1))`>>
        imp_res_tac LIST_REL_LENGTH>>
        gvs[NUM_def,INT_def,EVERY2_LUPDATE_same])>>
      xcon>>xsimpl>>
      EVAL_TAC)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def])>>
  xlet`POSTv sv. NUM_ARRAY Carrv Clist *
    &NUM (EL (Num (sub vec (i-1))) Clist) sv`
  >- (
    simp[NUM_ARRAY_def]>>xpull>>
    xapp>>xsimpl>>
    qexists_tac`Num (sub vec (i-1))`>>
    gvs[LIST_REL_EL_EQN,NUM_def,INT_def,integerTheory.INT_NOT_LT])>>
  xlet_auto_spec (SOME num_lt_spec)
  >- xsimpl>>
  xif>>gvs[]
  >- (xapp>>xsimpl)>>
  xlet_autop>>
  xif>>fs[]
  >- (
    xlet`POSTv uv. NUM_ARRAY Carrv
      (LUPDATE b (Num (sub vec (i-1))) Clist)`
    >- (
      simp[NUM_ARRAY_def]>>xpull>>
      xapp>>xsimpl>>
      qexists_tac`Num (sub vec (i-1))`>>
      imp_res_tac LIST_REL_LENGTH>>
      gvs[NUM_def,INT_def,EVERY2_LUPDATE_same,integerTheory.INT_NOT_LT])>>
    xcon>>xsimpl>>
    EVAL_TAC)>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[Fail_exn_def]
QED

Definition bw0_def[simp]:
  bw0 = (0w):word8
End

val bw0_v_thm = translate bw0_def;

Quote add_cakeml:
  fun reset_dm_arr carr b sz =
  let val len = Array.length carr in
  if len < sz then
    (Array.array (2 * sz) 0, 1)
  else if Unsafe.Arith.<= 536870912 b then
    (Array.array len 0, 1)
  else
    (carr, Unsafe.Arith.+ b 2)
  end
End

Theorem reset_dm_arr_spec:
  NUM sz szv ∧
  NUM b bv ∧ stamps_ok Clist b
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reset_dm_arr" (get_ml_prog_state()))
    [Carrv; bv; szv]
    (NUM_ARRAY Carrv Clist)
    (POSTv v.
        SEP_EXISTS Carrv' b' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') v ∧
          reset_dm_list Clist b sz = (Clist',b')))
Proof
  rw[]>>
  drule stamps_ok_bounds>>strip_tac>>
  xcf "reset_dm_arr" (get_ml_prog_state ())>>
  xlet`POSTv lv. NUM_ARRAY Carrv Clist * &NUM (LENGTH Clist) lv`
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
  xlet_auto_spec (SOME num_le_spec)
  >- xsimpl>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>
    simp[reset_dm_list_def,PAIR_TYPE_def,NUM_ARRAY_def]>>
    xsimpl>>
    simp[LIST_REL_REPLICATE_same,NUM_def,INT_def])>>
  xlet_auto_spec (SOME num_add_spec)
  >- xsimpl>>
  xcon>>
  simp[reset_dm_list_def,PAIR_TYPE_def]>>
  xsimpl
QED

Theorem sz_lit_map_small:
  sz_lit_map i v m =
  if i = 0
  then
    m
  else
    let i1 = smallnum_sub_vec i 1 v in
    let d = Num (ABS (sub_unsafe v i1)) in
    if d < m
    then
      sz_lit_map i1 v m
    else
      sz_lit_map i1 v (d+1)
Proof
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [sz_lit_map_def]))>>
  simp[smallnum_sub_vec_def]
QED

val res = translate_no_ind sz_lit_map_small;

Theorem sz_lit_map_ind_thm[local]:
  sz_lit_map_ind
Proof
  once_rewrite_tac [fetch "-" "sz_lit_map_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac ccnf_listTheory.sz_lit_map_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[smallnum_sub_vec_def]
QED

val _ = sz_lit_map_ind_thm |> update_precondition;

Theorem sz_lit_map_side:
  ∀i v m.
  i ≤ length v ⇒
  sz_lit_map_side i v m
Proof
  ho_match_mp_tac sz_lit_map_ind>>rw[]>>
  simp[Once (fetch "-" "sz_lit_map_side_def")]>>
  rw[]>>gvs[smallnum_sub_vec_def]
QED

val _ = sz_lit_map_side |> update_precondition;

Quote add_cakeml:
  fun init_lit_map_arr i v carr b =
  if i = 0
  then ()
  else
    let
      val i1 = Unsafe.Arith.subWitness i 1 v
      val d = uvsub v i1
    in
      if Unsafe.Arith.gtWitness d 0 carr
      then
        (Unsafe.update carr d (Unsafe.Arith.+ b 1);
        init_lit_map_arr i1 v carr b)
      else
        (Unsafe.update carr (Unsafe.Arith.subWitness 0 d carr) b;
        init_lit_map_arr i1 v carr b)
    end
End

Theorem init_lit_map_arr_spec:
  ∀i vec Clist b bv vecv iv Carrv.
  NUM b bv ∧ b ≤ 2 ** 29 + 1 ∧
  VECTOR_TYPE INT vec vecv ∧
  NUM i iv ∧
  init_lit_map_list' i vec Clist b = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "init_lit_map_arr" (get_ml_prog_state()))
    [iv; vecv; Carrv; bv]
    (NUM_ARRAY Carrv Clist)
    (POSTv v.
      NUM_ARRAY Carrv res)
Proof
  ho_match_mp_tac init_lit_map_list'_ind>>
  rpt strip_tac>>
  drule_then assume_tac init_lit_map_list'_lit>>
  qpat_x_assum`init_lit_map_list' _ _ _ _ = _` mp_tac>>
  simp[Once init_lit_map_list'_def]>>
  strip_tac>>
  xcf "init_lit_map_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif>>fs[]
  >- (xcon>>xsimpl)>>
  xlet_auto_spec (SOME num_sub_vec_spec)
  >- xsimpl>>
  xlet_auto
  >- (
    xsimpl>>
    gvs[uvsub_side_def])>>
  xlet_auto_spec (SOME int_gt_numarr_spec)
  >- xsimpl>>
  xif>>gvs[]
  >- (
    xlet_auto_spec (SOME num_add_spec)
    >- xsimpl>>
    xlet`POSTv uv. NUM_ARRAY Carrv (LUPDATE (b + 1) (Num (sub vec (i − 1))) Clist)`
    >- (
      simp[NUM_ARRAY_def]>>xpull>>
      xapp>>xsimpl>>
      qexists_tac`Num (sub vec (i − 1))`>>
      imp_res_tac LIST_REL_LENGTH>>
      `0 ≤ sub vec (i − 1)` by intLib.ARITH_TAC>>
      gvs[NUM_def,INT_def,EVERY2_LUPDATE_same])>>
    xapp>>gvs[])>>
  xlet_auto_spec (SOME int_sub_numarr_spec)
  >- xsimpl>>
  xlet`POSTv uv. NUM_ARRAY Carrv (LUPDATE b (Num (-sub vec (i − 1))) Clist)`
  >- (
    simp[NUM_ARRAY_def]>>xpull>>
    xapp>>xsimpl>>
    qexists_tac`Num (-sub vec (i − 1))`>>
    imp_res_tac LIST_REL_LENGTH>>
    `0 ≤ -sub vec (i − 1)` by intLib.ARITH_TAC>>
    gvs[NUM_def,INT_def,EVERY2_LUPDATE_same])>>
  xapp>>gvs[]
QED

Quote add_cakeml:
  fun resize_dm carr b v =
  let
    val lv = Vector.length v
    val sz = sz_lit_map lv v 0
  in
    reset_dm_arr carr b sz
  end
End

Theorem resize_dm_spec:
  NUM b bv ∧ stamps_ok Clist b ∧
  VECTOR_TYPE INT vec vecv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_dm" (get_ml_prog_state()))
    [Carrv; bv; vecv]
    (NUM_ARRAY Carrv Clist)
    (POSTv v.
        SEP_EXISTS Carrv' b' Clist' bv'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') v ∧
          resize_dm Clist b vec = (Clist',b')))
Proof
  rw[]>>
  xcf "resize_dm" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    irule sz_lit_map_side>>
    simp[])>>
  simp[resize_dm_def]>>
  xapp>>xsimpl>>
  rpt (first_x_assum $ irule_at Any)>>
  qexists_tac`emp`>>xsimpl>>
  rw[]>>
  first_x_assum (irule_at Any)>>
  xsimpl
QED

Quote add_cakeml:
  fun prepare_rup carr b v =
  case resize_dm carr b v of (dml',b') =>
  (init_lit_map_arr (Vector.length v) v dml' b';
    (dml',b'))
End

Theorem prepare_rup_spec:
  NUM b bv ∧ stamps_ok Clist b ∧
  VECTOR_TYPE INT vec vecv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "prepare_rup" (get_ml_prog_state()))
    [Carrv; bv; vecv]
    (NUM_ARRAY Carrv Clist)
    (POSTv v.
        SEP_EXISTS Carrv' b' Clist' bv'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') v ∧
          prepare_rup Clist b vec = (Clist',b')))
Proof
  rw[]>>
  xcf "prepare_rup" (get_ml_prog_state ())>>
  xlet_autop>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  simp[prepare_rup_def]>>
  rename1`init_lit_map_list (length vec) vec Clist' b'`>>
  `b' ≤ 2 ** 29 + 1` by (
    gvs[resize_dm_def]>>
    drule_all stamps_ok_reset_dm_list>>
    simp[stamps_ok_def])>>
  `IS_SOME (init_lit_map_list' (length vec) vec Clist' b')` by (
    irule init_lit_map_list'_SOME>>
    simp[]>>
    drule bnd_clause_resize_dm>>
    rw[])>>
  fs[IS_SOME_EXISTS]>>
  xlet_autop>>
  xlet_autop>>
  xcon>>xsimpl>>
  drule init_lit_map_list'>>
  rw[NUM_ARRAY_refl]
QED

Quote add_cakeml:
  fun unit_prop_one lno fml carr b i =
  if i < Array.length fml
  then
    let
      val c = Unsafe.sub fml i
      val n = Vector.length c
    in
      if n = 1 andalso int_eq_0 (uvsub c 0)
      then
        raise Fail (format_failure lno ("invalid clause hint (maybe deleted): " ^ Int.toString i))
      else
        delete_literals_sing_arr lno carr b c n
    end
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
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  NUM i iv ∧
  unit_prop_one' fmlls Clist b i = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_one" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; iv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Clist'.
        NUM_ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Clist'.
        NUM_ARRAY Carrv Clist' *
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
    metis_tac[Fail_exn_def,NUM_ARRAY_refl])>>
  rename1`EL h fmlls`>>
  `vcclause_TYPE (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  rpt xlet_autop>>
  xlet`POSTv bb.
    ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist *
    &BOOL (length (EL h fmlls) = 1 ∧ sub (EL h fmlls) 0 = 0) bb`
  >- (
    xlog>>
    reverse IF_CASES_TAC>>gvs[]
    >- xsimpl>>
    xlet_auto
    >- (xsimpl>>gvs[uvsub_side_def])>>
    xapp>>
    xsimpl>>
    qexists_tac`sub (EL h fmlls) 0`>>
    simp[int_eq_0_def])>>
  reverse xif
  >- (
    `EL h fmlls ≠ vcc_none` by metis_tac[is_vcc_none]>>
    gvs[]>>
    xapp>>xsimpl>>
    qpat_x_assum`delete_literals_sing_list' _ _ _ _ = _` $ irule_at Any>>
    qpat_x_assum`NUM lno _` $ irule_at Any>>
    xsimpl>>
    metis_tac[NUM_ARRAY_refl])>>
  `EL h fmlls = vcc_none` by metis_tac[is_vcc_none]>>
  gvs[]>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  metis_tac[Fail_exn_def,NUM_ARRAY_refl]
QED

Theorem unit_prop_arr_spec:
  ∀ls lsv Carrv Clist b bv res.
  NUM lno lnov ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  LIST_TYPE NUM ls lsv ∧
  unit_prop_list' fmlls Clist b ls = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; lsv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Clist'.
        NUM_ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Clist'.
        NUM_ARRAY Carrv Clist' *
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
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[NUM_ARRAY_refl])
  >- (
    xsimpl>>
    gvs[AllCaseEqs()]>>
    metis_tac[NUM_ARRAY_refl])>>
  xif>>gvs[]
  >- (
    xcon>>xsimpl>>
    EVAL_TAC)>>
  `stamps_ok Clist' b` by metis_tac[stamps_ok_unit_prop_one']>>
  xapp>>xsimpl>>
  first_x_assum $ irule_at Any>>xsimpl>>
  metis_tac[NUM_ARRAY_refl]
QED

Theorem parse_vb_num_aux_small:
  parse_vb_num_aux s i len ex n =
  if smallnum_lt_str i len s then
    let v = ORD (strsub_unsafe s i) in
      if smallnum_ge v 128 then
        parse_vb_num_aux s (smallnum_add_str i 1 s) len (ex*128)
          ((smallnum_sub v 128)*ex+n)
      else
        ((v*ex+n), smallnum_add_str i 1 s)
  else (0, i)
Proof
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [parse_vb_num_aux_def]))>>
  simp[smallnum_lt_str_def,smallnum_ge_def,smallnum_add_str_def,
    smallnum_sub_def]
QED

val res = translate_no_ind parse_vb_num_aux_small;

Theorem parse_vb_num_aux_ind_thm[local]:
  parse_vb_num_aux_ind
Proof
  once_rewrite_tac [fetch "-" "parse_vb_num_aux_ind_def"]>>
  rpt gen_tac>>
  rpt (disch_then strip_assume_tac)>>
  match_mp_tac syntax_helperTheory.parse_vb_num_aux_ind>>
  rpt strip_tac>>
  last_x_assum match_mp_tac>>
  rpt strip_tac>>
  gvs[smallnum_lt_str_def,smallnum_ge_def,smallnum_add_str_def,
    smallnum_sub_def]
QED

val _ = parse_vb_num_aux_ind_thm |> update_precondition;

val parse_vb_num_aux_side_def = theorem "parse_vb_num_aux_side_def"

Theorem parse_vb_num_aux_side:
 !a b c d e.
 c <= strlen a ∧ b ≤ c ==> parse_vb_num_aux_side a b c d e
Proof
 ho_match_mp_tac parse_vb_num_aux_ind >>
 rpt strip_tac >>
 simp[Once $ parse_vb_num_aux_side_def] >>
 strip_tac >>
 gvs[smallnum_lt_str_def,smallnum_ge_def,smallnum_add_str_def,
   smallnum_sub_def] >>
 assume_tac (Q.SPEC `strsub_unsafe a b` ORD_BOUND) >>
 rw[]
QED

val _ = parse_vb_num_aux_side |> update_precondition;

val res = translate parse_vb_num_def;

(* The decoding of a multi-byte number, after its first byte *)
Definition vb_int_hi_def:
  vb_int_hi s i len neg h =
  if smallnum_lt_str (smallnum_add_str i 1 s) len s then
    (let b = ORD (strsub_unsafe s (smallnum_add_str i 1 s)) in
     if smallnum_lt b 128 then
       (let h = smallnum_add h (smallnum_mul b 64) in
        ((if neg then smallint_sub 0 (&h) else &h), smallnum_add_str i 2 s))
     else if smallnum_lt_str (smallnum_add_str i 2 s) len s then
       (let h = smallnum_add h (smallnum_mul (smallnum_sub b 128) 64) in
        let b = ORD (strsub_unsafe s (smallnum_add_str i 2 s)) in
        if smallnum_lt b 128 then
          (let h = smallnum_add h (smallnum_mul b 8192) in
           ((if neg then smallint_sub 0 (&h) else &h), smallnum_add_str i 3 s))
        else if smallnum_lt_str (smallnum_add_str i 3 s) len s then
          (let h = smallnum_add h (smallnum_mul (smallnum_sub b 128) 8192) in
           let b = ORD (strsub_unsafe s (smallnum_add_str i 3 s)) in
           if smallnum_lt b 128 then
             (let h = smallnum_add h (smallnum_mul b 1048576) in
              ((if neg then smallint_sub 0 (&h) else &h),
               smallnum_add_str i 4 s))
           else
             (let h = smallnum_add h
                        (smallnum_mul (smallnum_sub b 128) 1048576) in
              let (m,j) =
                parse_vb_num_aux s (smallnum_add_str i 4 s) len 268435456
                  (smallnum_add (smallnum_mul 2 h) (if neg then 1 else 0)) in
              ((if m MOD 2 = 0n then (&(m DIV 2):int)
                else (-&(m DIV 2):int)), j)))
        else (0, smallnum_add_str i 3 s))
     else (0, smallnum_add_str i 2 s))
  else (0, smallnum_add_str i 1 s)
End

Theorem vb_int_lo_small:
  vb_int_lo s i len =
  if smallnum_lt_str i len s then
    (let c = strsub_unsafe s i in
     let b = ORD c in
     let w = char_to_word8 c in
     let neg = (w2n (w && 1w) = 1) in
     let h = w2n ((w && 127w) >>> 1) in
     if smallnum_lt b 128 then
       ((if neg then smallint_sub 0 (&h) else &h), smallnum_add_str i 1 s)
     else vb_int_hi s i len neg h)
  else (0, i)
Proof
  simp[vb_int_lo_def,vb_int_hi_def,vb_sgn_def,smallnum_lt_str_def,
    smallnum_lt_def,smallnum_add_str_def,smallnum_add_def,smallnum_mul_def,
    smallnum_sub_def,smallint_sub_def,integerTheory.INT_SUB_LZERO]
QED

val res = translate vb_int_hi_def;

(* Assumes ORD c < 256 and w2n w < dimword for every ORD and w2n term of the
  goal, so that byte arithmetic bounds become linear arithmetic *)
fun byte_bound_tac (asl,g) =
  let
    fun is_ord t = is_comb t andalso same_const (rator t) ``ORD``
    fun is_w2n t = is_comb t andalso is_const (rator t) andalso
                   #Name (dest_thy_const (rator t)) = "w2n"
    val ts = HOLset.listItems (HOLset.addList (empty_tmset,
               find_terms (fn t => is_ord t orelse is_w2n t) g))
    fun thm_of t = if is_ord t then ISPEC (rand t) ORD_BOUND
                   else ISPEC (rand t) wordsTheory.w2n_lt
  in MAP_EVERY (assume_tac o thm_of) ts (asl,g) end;

Theorem vb_int_hi_side[local]:
 !a b c d e.
 c <= strlen a ∧ b < c ∧ e < 256 ==> vb_int_hi_side a b c d e
Proof
 rw[definition "vb_int_hi_side_def"] >>
 gvs[smallnum_lt_str_def,smallnum_lt_def,smallnum_add_str_def,
   smallnum_add_def,smallnum_mul_def,smallnum_sub_def,smallint_sub_def] >>
 byte_bound_tac >>
 gvs[parse_vb_num_aux_side]
QED

val _ = vb_int_hi_side |> update_precondition;

val res = translate vb_int_lo_small;

Theorem vb_int_lo_side[local]:
 !a b c.
 c <= strlen a ∧ b ≤ c ==> vb_int_lo_side a b c
Proof
 rw[definition "vb_int_lo_side_def"] >>
 gvs[smallnum_lt_str_def,smallnum_lt_def,smallint_sub_def] >>
 byte_bound_tac >>
 gvs[vb_int_hi_side]
QED

val _ = vb_int_lo_side |> update_precondition;

val res = translate parse_vb_int_eq;

Theorem parse_vb_int_side:
 !s i len.
 len <= strlen s ∧ i ≤ len ==> parse_vb_int_side s i len
Proof
 rw[definition "parse_vb_int_side_def",vb_int_lo_side]
QED

val _ = parse_vb_int_side |> update_precondition;

val res = translate parse_vb_ilits_def;

Theorem parse_vb_ilits_side:
  ∀s i len acc.
  len ≤ strlen s ∧ i ≤ len ⇒ parse_vb_ilits_side s i len acc
Proof
  ho_match_mp_tac parse_vb_ilits_ind>>
  rw[]>>
  simp[Once (fetch "-" "parse_vb_ilits_side_def"),parse_vb_int_side]>>
  rw[]>>
  first_x_assum irule>>
  simp[]>>
  metis_tac[parse_vb_int_le]
QED

val _ = parse_vb_ilits_side |> update_precondition;

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
  ∀fmlls Clist b s i l iv bv res.
  NUM lno lnov ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  STRING_TYPE s sv ∧
  NUM i iv ∧
  NUM l lv ∧
  l <= strlen s /\ i ≤ l ∧
  unit_prop_vb_list' fmlls Clist b s i l = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "unit_prop_vb_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; sv; iv; lv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Clist'.
        NUM_ARRAY Carrv Clist' *
        &(res = SOME(b',Clist') ∧ OPTION_TYPE NUM b' v))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Clist'.
        NUM_ARRAY Carrv Clist' *
        &(Fail_exn e ∧ res = NONE))
    )
Proof
  ho_match_mp_tac unit_prop_vb_list'_ind >>
  rpt strip_tac >>
  pop_assum mp_tac>>
  simp[Once unit_prop_vb_list'_def]>>
  strip_tac>>
  xcf "unit_prop_vb_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (xsimpl >> fs[parse_vb_int_side]) >>
  gvs[UNCURRY_EQ,PAIR_TYPE_def] >> xmatch >>
  xlet_auto >- xsimpl >>
  xif >- (
      xcon >> xsimpl >>
      gvs[AllCaseEqs(),OPTION_TYPE_def] >>
      metis_tac[NUM_ARRAY_refl]) >>
  gvs[TypeBase.case_eq_of ``:bool``] >>
  xlet_auto
     >- (
       xsimpl >>
       conj_tac >- intLib.ARITH_TAC >>
       metis_tac[NUM_ARRAY_refl])
     >- (
       xsimpl >> rpt strip_tac >> rveq >> fs[] >>
       metis_tac[NUM_ARRAY_refl]) >>
  xif >- (
      xcon >> xsimpl >>
      gvs[AllCaseEqs(),OPTION_TYPE_def] >>
      metis_tac[NUM_ARRAY_refl]) >>
  gvs[] >>
  `stamps_ok Clist' b` by metis_tac[stamps_ok_unit_prop_one'] >>
  `i' ≤ l` by metis_tac[parse_vb_int_le] >>
  first_x_assum drule_all >>
  strip_tac >> xapp >>
  xsimpl
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
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  vcclause_TYPE v vv ∧
  LIST_TYPE NUM ls lsv ∧
  is_rup_list' fmlls Clist b v ls = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; lsv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') v ∧
          res = (T, (Clist',b'))))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(Fail_exn e ∧ FST res = F))
    )
Proof
  rw[]>>
  xcf "is_rup_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def,is_rup_list'_def]>>
  drule_all stamps_ok_prepare_rup>>strip_tac>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[NUM_ARRAY_refl])
  >- (
    xsimpl>>
    metis_tac[NUM_ARRAY_refl])>>
  xif
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xraise>>
  xsimpl>>
  metis_tac[Fail_exn_def,NUM_ARRAY_refl]
QED

Theorem is_rup_arr_spec:
  NUM lno lnov ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧
  vcclause_TYPE v vv ∧
  LIST_TYPE NUM ls lsv ∧
  dm_ok fmlls Clist b
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; lsv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λres.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') res ∧
          is_rup_list fmlls Clist b v ls = (T,(Clist',b'))))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(Fail_exn e ∧
          FST (is_rup_list fmlls Clist b v ls) = F))
    )
Proof
  rw[dm_ok_def]>>
  drule is_rup_list'_SOME>>
  disch_then (qspecl_then [`v`,`ls`,`b`] assume_tac)>>
  fs[IS_SOME_EXISTS]>>
  rename1`is_rup_list' _ _ _ _ _ = SOME res`>>
  mp_tac is_rup_arr_spec'>>
  impl_tac >- simp[]>>
  drule is_rup_list'>>
  rw[]
QED

Quote add_cakeml:
  fun is_rup_vb_arr lno fml carr b v s =
  let val dmb = prepare_rup carr b v
      val (carr',b') = dmb
  in
    case unit_prop_vb_arr lno fml carr' b' s 0 (String.size s) of
      (Some i) => raise Fail (format_failure lno ("unit propagation did not prove RUP"))
    | None => dmb
  end
End

Theorem is_rup_vb_arr_spec':
  NUM lno lnov ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧ stamps_ok Clist b ∧
  vcclause_TYPE v vv ∧
  STRING_TYPE s sv ∧
  is_rup_vb_list' fmlls Clist b v s = SOME res
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_vb_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; sv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') v ∧
          res = (T, (Clist',b'))))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(Fail_exn e ∧ FST res = F))
    )
Proof
  rw[]>>
  xcf "is_rup_vb_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (
    xsimpl>>
    metis_tac[NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def,is_rup_vb_list'_def]>>
  drule_all stamps_ok_prepare_rup>>strip_tac>>
  xmatch>>
  xlet_autop >>
  xlet_auto
  >- (xsimpl >> metis_tac[NUM_ARRAY_refl])
  >- (xsimpl >> metis_tac[NUM_ARRAY_refl]) >>
  Cases_on `b''` >> fs[OPTION_TYPE_def] >>
  xmatch
  >- (xvar >>xsimpl)
  >- (
     rpt xlet_autop >>xraise >>
     xsimpl >> simp[Fail_exn_def] >>
     metis_tac[NUM_ARRAY_refl])
QED

Theorem is_rup_vb_arr_spec:
  NUM lno lnov ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  NUM b bv ∧
  vcclause_TYPE v vv ∧
  STRING_TYPE s sv ∧
  dm_ok fmlls Clist b
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_rup_vb_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; bv; vv; sv]
    (ARRAY fmlv fmllsv * NUM_ARRAY Carrv Clist)
    (POSTve
      (λres.
        ARRAY fmlv fmllsv *
        SEP_EXISTS b' Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(PAIR_TYPE ($=) NUM (Carrv', b') res ∧
          is_rup_vb_list fmlls Clist b v s = (T,(Clist',b'))))
      (λe.
        ARRAY fmlv fmllsv *
        SEP_EXISTS Carrv' Clist'.
        NUM_ARRAY Carrv' Clist' *
        &(Fail_exn e ∧
          FST (is_rup_vb_list fmlls Clist b v s) = F))
    )
Proof
  rw[dm_ok_def]>>
  drule is_rup_vb_list'_SOME>>
  disch_then (qspecl_then [`v`,`s`,`b`] assume_tac)>>
  fs[IS_SOME_EXISTS]>>
  rename1`is_rup_vb_list' _ _ _ _ _ = SOME res`>>
  mp_tac is_rup_vb_arr_spec'>>
  impl_tac >- simp[]>>
  drule is_rup_vb_list'>>
  rw[]
QED


Quote add_cakeml:
  fun delete_arr d fml i =
    if Array.length fml <= i then ()
    else
      (Unsafe.update fml i d)
End

Theorem delete_arr_spec:
  A d dv ∧
  NUM i iv ∧
  LIST_REL A fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_arr" (get_ml_prog_state()))
    [dv; fmlv; iv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL A (delete_list d fmlls i) fmllsv') )
Proof
  rw[]>>
  xcf "delete_arr" (get_ml_prog_state ())>>
  simp[delete_list_def]>>
  rpt xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xif>-(xcon>>xsimpl)>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[]
QED

Quote add_cakeml:
  fun delete_ids_arr d fml ls =
    case ls of
      [] => ()
    | (i::is) =>
      (delete_arr d fml i; delete_ids_arr d fml is)
End

Theorem delete_ids_arr_spec:
  ∀ls lsv fmlls fmllsv.
  A d dv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL A fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_ids_arr" (get_ml_prog_state()))
    [dv; fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL A (delete_ids_list d fmlls ls) fmllsv') )
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

Quote add_cakeml:
  fun delete_ids_vb_arr d fml s i1 len =
    case parse_vb_int s i1 len of (m,i) =>
    if m <= 0 then ()
    else
      (delete_arr d fml m; delete_ids_vb_arr d fml s i len)
End

Theorem delete_ids_vb_arr_spec:
  ∀d fmlls s i l fmllsv sv iv lv.
  A d dv ∧
  LIST_REL A fmlls fmllsv ∧
  STRING_TYPE s sv ∧
  NUM i iv ∧
  NUM l lv ∧
  l ≤ strlen s ∧ i ≤ l
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_ids_vb_arr" (get_ml_prog_state()))
    [dv; fmlv; sv; iv; lv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL A (delete_ids_vb_list d fmlls s i l) fmllsv') )
Proof
  ho_match_mp_tac delete_ids_vb_list_ind>>
  rpt strip_tac>>
  simp[Once delete_ids_vb_list_def]>>
  xcf "delete_ids_vb_arr" (get_ml_prog_state ())>>
  xlet_auto
  >- (
    xsimpl>>
    fs[parse_vb_int_side])>>
  Cases_on`parse_vb_int s i l`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xif
  >- (xcon>>xsimpl)>>
  `∃n. q = &n` by (qexists_tac`Num q`>>intLib.ARITH_TAC)>>
  gvs[GSYM NUM_def]>>
  imp_res_tac parse_vb_int_le>>
  xlet_autop>>
  xapp>>
  fs[]
QED

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

(* Where a clause imported or derived by the proof enters the formula array;
  the initial formula is laid out by build_cfml_arr *)
Quote add_cakeml:
  fun insert_clause_arr fml n v =
    Array.updateResize fml vcc_none n v
End

Theorem insert_clause_arr_spec:
  NUM n nv ∧
  vcclause_TYPE v vv ∧
  LIST_REL vcclause_TYPE fmlls fmllsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"insert_clause_arr"(get_ml_prog_state()))
  [fmlv; nv; vv]
  (ARRAY fmlv fmllsv)
  (POSTv resv.
    SEP_EXISTS fmllsv'. ARRAY resv fmllsv' *
    &LIST_REL vcclause_TYPE (insert_vcc_list fmlls n v) fmllsv')
Proof
  rw[insert_vcc_list_def]>>
  xcf "insert_clause_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp_spec array_updateResize_spec>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  irule LIST_REL_update_resize>>
  gvs[vcc_none_v_thm]
QED

Definition is_empty_def:
  is_empty (ls:'a vector) = (length ls = 0)
End

val res = translate is_empty_def;

Quote add_cakeml:
  fun contains_emp_arr_aux fml i =
  if i = 0 then False
  else
    let val i1 = Unsafe.Arith.subWitness i 1 fml in
    is_empty (Unsafe.sub fml i1) orelse
    contains_emp_arr_aux fml i1
    end
End

Theorem contains_emp_arr_aux_spec:
  ∀fmlls i iv fmlv fmllsv.
  NUM i iv ∧
  i <= LENGTH fmlls ∧
  LIST_REL vcclause_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "contains_emp_arr_aux" (get_ml_prog_state()))
    [fmlv; iv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (contains_emp_list_aux fmlls i) resv) *
      ARRAY fmlv fmllsv)
Proof
  ho_match_mp_tac contains_emp_list_aux_ind>>rw[]>>
  xcf "contains_emp_arr_aux" (get_ml_prog_state ())>>
  xlet_autop>>xif
  >- (
    xcon>>xsimpl>>
    simp[Once contains_emp_list_aux_def]>>
    EVAL_TAC)>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xlet_auto_spec (SOME num_sub_arr_spec)
  >- xsimpl>>
  simp[Once contains_emp_list_aux_def]>>
  `vcclause_TYPE (EL (i-1) fmlls) (EL (i-1) fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  rpt xlet_autop>>
  simp[any_el_ALT]>>
  xlog>>xsimpl>>
  fs[is_empty_def]>>rw[]>>gvs[]>>
  last_x_assum assume_tac>>
  xapp>>xsimpl>>
  fs[any_el_ALT]
QED

Quote add_cakeml:
  fun contains_emp_arr fml =
  contains_emp_arr_aux fml (Array.length fml)
End

Theorem contains_emp_arr_spec:
  LIST_REL vcclause_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "contains_emp_arr" (get_ml_prog_state()))
    [fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (contains_emp_list fmlls) resv) *
      ARRAY fmlv fmllsv)
Proof
  rw[]>>
  xcf "contains_emp_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  fs[contains_emp_list_def,LIST_REL_EL_EQN]
QED
