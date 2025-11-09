(*
  This refines ccnf_list to use arrays
*)
Theory ccnf_arrayProg
Ancestors
  UnsafeProg UnsafeProof
  ccnf ccnf_list
Libs
  preamble basis blastLib

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val _ = hide_environments true;

Theorem update_resize_LUPDATE[simp]:
  n < LENGTH Clist ⇒
  update_resize Clist d v n =
    LUPDATE v n Clist
Proof
  rw[update_resize_def]
QED

(* Default inheritance path, means all programs will use
  the unsafe primitives *)
val _ = translation_extends"UnsafeProg";

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

Definition format_failure_def:
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val _ = translate format_failure_def;

(* TODO: Vector.sub should be unsafe,
  w8ult should be native,
  = on bytes should be efficient *)
Definition w8ult_def:
  w8ult (x:word8) (y:word8) ⇔
    w2n x < w2n y
End

Theorem w8ult_thm:
  w8ult x y ⇔ x <+ y
Proof
  rw[w8ult_def,WORD_LO]
QED

val res = translate w8ult_def;

val all_assigned_arr_def = process_topdecs`
  fun all_assigned_arr carr b v i =
  if i = 0 then True
  else
    let
      val i1 = i - 1
      val c = Vector.sub v i1
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
    end` |> append_prog;

Definition bnd_clause_def:
  bnd_clause n vec ⇔
  (∀j. j < length vec ⇒
    Num (ABS (sub vec j)) < n)
End

Theorem all_assigned_arr_spec:
  ∀Clist b vec i bv vecv iv Carrv.
  WORD8 b bv ∧
  VECTOR_TYPE INT vec vecv ∧
  NUM i iv ∧
  i ≤ length vec ∧
  bnd_clause (LENGTH Clist) vec
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_assigned_arr" (get_ml_prog_state()))
    [Carrv; bv; vecv; iv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
      W8ARRAY Carrv Clist *
      &BOOL (all_assigned_list Clist b vec i) v)
Proof
  ho_match_mp_tac all_assigned_list_ind>>
  rw[]>>
  xcf "all_assigned_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    xcon>>
    simp[Once all_assigned_list_def]>>
    xsimpl)>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    qmatch_asmsub_abbrev_tac`INT (-n) ivv`>>
    `ABS n = -n ∧ i-1 < length vec` by intLib.ARITH_TAC>>
    `(Num (-n)) < LENGTH Clist` by metis_tac[bnd_clause_def]>>
    rpt xlet_autop>>
    xif
    >- (
      xapp>>xsimpl>>
      gvs[any_el_ALT,Abbr`n`]>>
      rw[]>>
      simp[Once all_assigned_list_def]>>
      gvs[any_el_ALT])>>
    xcon>>
    simp[Once all_assigned_list_def]>>
    gvs[any_el_ALT]>>
    xsimpl)
  >- (
    qmatch_asmsub_abbrev_tac`INT n ivv`>>
    `ABS n = n ∧ i-1 < length vec` by intLib.ARITH_TAC>>
    `(Num n) < LENGTH Clist` by metis_tac[bnd_clause_def]>>
    xlet_auto
    >-
      (xsimpl>>intLib.ARITH_TAC)>>
    xlet_autop>>
    xif
    >- (
      xapp>>xsimpl>>
      gvs[any_el_ALT,Abbr`n`,w8ult_thm]>>
      rw[]>>
      simp[Once all_assigned_list_def]>>
      gvs[any_el_ALT])>>
    xcon>>
    simp[Once all_assigned_list_def]>>
    gvs[any_el_ALT,w8ult_thm]>>
    xsimpl)
QED

Definition badd1_def:
  badd1 b = (b+1w):word8
End

val res = translate badd1_def;

val delete_literals_sing_arr_def = process_topdecs`
  fun delete_literals_sing_arr lno carr b v i =
  if i = 0 then True
  else
    let
      val i1 = i - 1
      val c = Vector.sub v i1
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
    end` |> append_prog;

Theorem delete_literals_sing_arr_spec:
  ∀Clist b vec i bv vecv iv Carrv.
  NUM lno lnov ∧
  WORD8 b bv ∧
  VECTOR_TYPE INT vec vecv ∧
  NUM i iv ∧
  i ≤ length vec ∧
  bnd_clause (LENGTH Clist) vec
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_literals_sing_arr" (get_ml_prog_state()))
    [lnov; Carrv; bv; vecv; iv]
    (W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS b' Clist'.
        W8ARRAY Carrv Clist' *
        &(delete_literals_sing_list Clist b vec i =
          SOME(b',Clist') ∧ BOOL b' v))
      (λe.
        W8ARRAY Carrv Clist *
        &(Fail_exn e ∧
          delete_literals_sing_list Clist b vec i = NONE)
        ))
Proof
  ho_match_mp_tac delete_literals_sing_list_ind>>
  rw[]>>
  xcf "delete_literals_sing_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xif
  >- (
    simp[Once delete_literals_sing_list_def]>>
    simp[Once delete_literals_sing_list_def]>>
    xcon>>
    xsimpl>>xsimpl)>>
  rpt xlet_autop>>
  xif
  >- (
    rpt xlet_autop>>
    qmatch_asmsub_abbrev_tac`INT (-n) ivv`>>
    `ABS n = -n ∧ i-1 < length vec` by intLib.ARITH_TAC>>
    `(Num (-n)) < LENGTH Clist` by metis_tac[bnd_clause_def]>>
    rpt xlet_autop>>
    xif
    >- (
      xapp>>xsimpl>>
      gvs[any_el_ALT,Abbr`n`]>>
      rw[]>>
      simp[Once delete_literals_sing_list_def]>>
      gvs[any_el_ALT])>>
    xlet_auto>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        simp[Once delete_literals_sing_list_def]>>
        gvs[any_el_ALT,badd1_def]>>
        xsimpl)>>
      simp[Once delete_literals_sing_list_def]>>
      gvs[any_el_ALT,badd1_def])>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    CONJ_ASM1_TAC>>simp[]>>
    simp[Once delete_literals_sing_list_def]>>
    gvs[any_el_ALT,badd1_def]>>
    metis_tac[Fail_exn_def])>>
  qmatch_asmsub_abbrev_tac`INT n ivv`>>
  `ABS n = n ∧ i-1 < length vec` by intLib.ARITH_TAC>>
  `(Num n) < LENGTH Clist` by metis_tac[bnd_clause_def]>>
  xlet_auto
  >-  (xsimpl>>gvs[])>>
  xlet_autop>>
  xif
  >- (
    xapp>>xsimpl>>
    gvs[any_el_ALT,Abbr`n`,w8ult_thm]>>
    rw[]>>
    simp[Once delete_literals_sing_list_def]>>
    gvs[any_el_ALT])>>
  xlet_auto>>
  xif
  >- (
    xlet_auto
    >- (xsimpl>>gvs[])>>
    xcon>>xsimpl
    >- (
      simp[Once delete_literals_sing_list_def]>>
      gvs[any_el_ALT,w8ult_thm]>>
      xsimpl)>>
    simp[Once delete_literals_sing_list_def]>>
    gvs[any_el_ALT,w8ult_thm])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  CONJ_ASM1_TAC>>simp[]>>
  simp[Once delete_literals_sing_list_def]>>
  gvs[any_el_ALT,w8ult_thm]>>
  metis_tac[Fail_exn_def]
QED

