(*
  This refines distrup_list to use arrays
*)
Theory distrup_arrayProg
Libs
  preamble basis
Ancestors
  ccnf_arrayProg distrup distrup_list HashtableProof

val _ = hide_environments true;

val _ = translation_extends "ccnf_arrayProg";

val res = register_type``:distrup``;

Quote add_cakeml:
  fun check_distrup_arr lno distrup fml carr b =
  case distrup of
    Del ls =>
      (delete_ids_arr fml ls; (fml,carr,b))
  | Lrup n v hints =>
      (case is_rup_arr lno fml carr b v hints of (dml,b) =>
        (Array.updateResize fml None n (Some v), dml,b))
  | Import n v =>
      (case resize_dm carr b v of (dml,b) =>
      (Array.updateResize fml None n (Some v), dml,b))
  | Validateunsat =>
      if contains_emp_arr fml
      then
        (fml,carr,b)
      else
        raise Fail (format_failure lno "failed to validate UNSAT (no empty clause)")
End

val DISTRUP_DISTRUP_TYPE_def = fetch "-" "DISTRUP_DISTRUP_TYPE_def";

Theorem check_distrup_arr_spec:
  NUM lno lnov ∧
  DISTRUP_DISTRUP_TYPE distrup distrupv ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_distrup_arr" (get_ml_prog_state()))
    [lnov; distrupv; fmlv; Carrv; bv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λres.
        SEP_EXISTS v1 v2 v3.
        SEP_EXISTS fmlls' fmllsv' b' Clist'.
        ARRAY v1 fmllsv' *
        W8ARRAY v2 Clist' *
        &(res = Conv NONE [v1; v2; v3] ∧
          LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls' fmllsv' ∧
          WORD8 b' v3 ∧
          check_distrup_list distrup fmlls Clist b =
            SOME (fmlls', (Clist', b'))))
      (λe.
        &(Fail_exn e ∧ check_distrup_list distrup fmlls Clist b = NONE)))
Proof
  simp[check_distrup_list_def]>>strip_tac>>
  xcf "check_distrup_arr" (get_ml_prog_state ())>>
  Cases_on`distrup`>>fs[DISTRUP_DISTRUP_TYPE_def]>>
  xmatch
  >- ( (* Del *)
    xlet_autop >>
    xcon>>xsimpl)
  >- ( (* Rup *)
    xlet `
      POSTve
        (λres.
             (SEP_EXISTS b' Carrv' Clist'.
                W8ARRAY Carrv' Clist' *
                &(PAIR_TYPE $= WORD8 (Carrv',b') res ∧
                 is_rup_list fmlls Clist b v l = (T,Clist',b'))) *
             ARRAY fmlv fmllsv)
        (λe.
            &(Fail_exn e ∧ ¬FST (is_rup_list fmlls Clist b v l)))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      simp[PAIR_TYPE_def]>>rw[]>>
      xsimpl)
    >- (
      xsimpl>>
      simp[AllCaseEqs()]>>
      Cases_on`is_rup_list fmlls Clist b v l`>>simp[])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    irule LIST_REL_update_resize>>
    simp[OPTION_TYPE_def])
  >- (
    rpt xlet_autop>>
    xlet_auto
    >- (
      xsimpl>>
      rw[]>>metis_tac[W8ARRAY_refl])>>
    fs[PAIR_TYPE_def]>>
    xmatch>> rpt xlet_autop>>
    xcon>>xsimpl>>
    irule LIST_REL_update_resize>>
    simp[OPTION_TYPE_def])
  >- (
    xlet_autop>>
    xif
    >-
      (xcon>>xsimpl)>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    fs[Fail_exn_def]>>
    metis_tac[]
  )
QED

