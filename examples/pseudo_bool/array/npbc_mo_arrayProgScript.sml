(*
  Refine the multi-objective PB proof checker to CakeML
*)
Theory npbc_mo_arrayProg
Ancestors
  npbc_check pbc_mo npbc_mo npbc_mo_check npbc_slot npbc_list npbc_mo_list
  pb_parse pb_parse_mo pbc_normalise npbc_arrayProg npbc_parseProg
Libs
  preamble basis cfLib basisFunctionsLib

val _ = translation_extends "npbc_parseProg";

Overload "objs_TYPE" = ``
  LIST_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) INT)``

Overload "sols_TYPE" = ``LIST_TYPE (LIST_TYPE INT)``

(* Minimisation under the selected ordering *)

Theorem vec_le_eqn:
  (vec_le [] [] ⇔ T) ∧
  (vec_le [] (w::ws) ⇔ F) ∧
  (vec_le (v::vs) [] ⇔ F) ∧
  (vec_le (v::vs) (w::ws) ⇔ v ≤ w ∧ vec_le vs ws)
Proof
  rw[vec_le_def]
QED

val res = translate vec_le_eqn;

val res = translate lex_le_def;

val res = translate sort_desc_def;

val res = translate ord_le_def;

val res = translate ord_lt_def;

val res = translate ord_equiv_def;

val res = translate ord_dedup_def;

val res = translate ord_min_def;

val res = translate npbc_moTheory.obj_vecs_def;

(* The order check: the loaded order refines the ordering's reference *)

val res = translate mo_obj_vars_def;

val res = translate mo_vars_covered_def;

val res = translate var_le_def;

val res = translate rename_obj_def;

val res = translate vs_to_us_def;

val res = translate pareto_constrs_def;

val res = translate check_imp_any_def;

val res = translate miscTheory.any_el_def;

val res = translate npbc_lin_def;

val res = translate var_sum_def;

val res = translate thr_core_def;

val res = translate sort_core_def;

val res = translate lex_cmp_core_def;

val res = translate leximax_aux_len_def;

val res = translate leximax_constrs_def;

val res = translate sptreeTheory.union_def;

val res = translate subset_sums_def;

val res = translate dedup_sorted_def;

val res = translate mo_vals_def;

val res = translate (ref_core_def |> REWRITE_RULE [GSYM mllistTheory.drop_def]);

val res = translate ref_ord_ok_def;

val res = translate ord_ok_def;

(* The multi-objective side conditions on the delegated steps *)
Theorem mo_cstep_ok_eq:
  mo_cstep_ok mord objs cstep pc =
  case cstep of
    Sstep _ => (case pc.ord of NONE => F | SOME _ => T)
  | CheckedDelete _ _ _ _ => (case pc.ord of NONE => F | SOME _ => T)
  | LoadOrder nn xs =>
    (case ALOOKUP pc.orders nn of
      NONE => F
    | SOME aord => ord_ok mord objs aord xs)
  | _ => T
Proof
  Cases_on`cstep`>>rw[mo_cstep_ok_def]>>
  Cases_on`pc.ord`>>gvs[]
QED

val res = translate mo_cstep_ok_eq;

val res = translate get_sol_def;

Definition mo_sol_ok_def:
  mo_sol_ok objs (pc:proof_conf) (free:num_set) (ws:num_set) ⇔
    free = LN ∧ pc.chk ∧ mo_vars_covered objs ws
End

Theorem mo_sol_ok_eq:
  mo_sol_ok objs pc free ws =
  case free of
    LN => pc.chk ∧ mo_vars_covered objs ws
  | _ => F
Proof
  Cases_on`free`>>rw[mo_sol_ok_def]
QED

val res = translate mo_sol_ok_eq;

Definition mo_sol_update_def:
  mo_sol_update pc id' =
    pc with <| id := id'; enum := pc.enum + 1 |>
End

val res = translate mo_sol_update_def;

(* The multi-objective cstep checker: solution logging is bespoke,
  every other step is delegated to check_cstep_arr *)
Quote add_cakeml:
  fun check_mo_cstep_arr lno mord objs cstep fml assg st inds vimap vomap pc
    sols =
  case get_sol cstep of
    Some (w,free) =>
    let val ws = list_to_num_set (map_fst w) in
      if mo_sol_ok objs pc free ws then
        (case check_obj_core_arr lno None w fml inds None of
          None =>
            raise Fail (format_failure lno
              "logged solution does not satisfy the core constraints")
        | Some (new, (wsol, cinds)) =>
          let
            val id = get_id pc
            val c = model_banning (Some ws) free wsol
          in
            case enc_mv c True of (s,mv) =>
            case store_ind_arr fml s mv id cinds vimap assg st of
              (fml',(inds',(vimap',(id',(assg',st'))))) =>
            (fml', (assg', (st', (inds', (vimap', (vomap,
              (mo_sol_update pc id', obj_vecs objs wsol :: sols)))))))
          end)
      else
        raise Fail (format_failure lno
          "solution logging requires an unchecked-deletion-free proof state, no free variables and an assignment to every objective variable")
    end
  | None =>
    if mo_cstep_ok mord objs cstep pc then
      (case check_cstep_arr lno cstep fml assg st inds vimap vomap pc of
        (fml', (assg', (st', (inds', (vimap', (vomap', pc')))))) =>
        (fml', (assg', (st', (inds', (vimap', (vomap', (pc', sols))))))))
    else
      raise Fail (format_failure lno
        "step not permitted: redundance and checked deletion need a loaded order, and a loaded order must refine the selected objective ordering")
End


Theorem check_mo_cstep_arr_spec:
  NUM lno lnov ∧
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  objs_TYPE objs objsv ∧
  NPBC_CHECK_CSTEP_TYPE cstep cstepv ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  NUM st stv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  sols_TYPE sols solsv ∧
  fml_bound fmlls (LENGTH assg)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_mo_cstep_arr" (get_ml_prog_state()))
    [lnov; mordv; objsv; cstepv; fmlv; assgv; stv; indsv; vimapv; vomapv; pcv;
      solsv]
    (ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_mo_cstep_list mord objs cstep fmlls assg st inds vimap
            vomap pc sols of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
              (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
              (PAIR_TYPE NUM
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE
                  (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
                  (PAIR_TYPE vomap_TYPE
                    (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE sols_TYPE))))))
                res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_mo_cstep_list mord objs cstep fmlls assg st inds vimap vomap
            pc sols = NONE)))
Proof
  rw[]>>
  xcf "check_mo_cstep_arr" (get_ml_prog_state ())>>
  simp[check_mo_cstep_list_def]>>
  xlet_autop>>
  Cases_on`get_sol cstep`>>
  gvs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>
      metis_tac[ARRAY_NUM_ARRAY_refl])>>
    xlet_auto
    >- (
      rw[]>>xsimpl>>
      TOP_CASE_TAC>>rw[]>>
      metis_tac[ARRAY_NUM_ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_NUM_ARRAY_refl])>>
    gvs[AllCasePreds()]>>
    PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl)>>
  rename1`get_sol cstep = SOME wfr`>>
  PairCases_on`wfr`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  gvs[check_mo_cstep_sol_list_def,mo_sol_ok_def,map_fst_def]>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  `obj_TYPE NONE (Conv (SOME (TypeStamp «None» 2)) [])` by
    simp[OPTION_TYPE_def]>>
  `OPTION_TYPE INT NONE (Conv (SOME (TypeStamp «None» 2)) [])` by
    simp[OPTION_TYPE_def]>>
  ntac 2 xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>rw[]>>metis_tac[ARRAY_NUM_ARRAY_refl])
  >- (
    xsimpl>>metis_tac[ARRAY_NUM_ARRAY_refl])>>
  Cases_on`check_obj_core NONE wfr0 fmlls inds NONE`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  rename1`check_obj_core _ _ _ _ _ = SOME nw`>>
  PairCases_on`nw`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  qmatch_asmsub_rename_tac`SPTREE_SPT_TYPE UNIT_TYPE (list_to_num_set _) wsv`>>
  `pres_TYPE (SOME (list_to_num_set (MAP FST wfr0)))
    (Conv (SOME (TypeStamp «Some» 2)) [wsv])` by simp[OPTION_TYPE_def]>>
  xlet_autop>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  ntac 2 xlet_autop>>
  gvs[enc_mv_enc,PAIR_TYPE_def,get_id_def]>>
  xmatch>>
  qabbrev_tac`c = model_banning (SOME (list_to_num_set (MAP FST wfr0))) LN nw1`>>
  `∃fml1 inds1 vimap1 id1 assg1 st1.
    store_ind fmlls (enc c T) (max_var (FST c)) pc.id (reindex fmlls inds)
      vimap assg st =
    (fml1,inds1,vimap1,id1,assg1,st1)` by metis_tac[PAIR]>>
  simp[]>>
  xlet`POSTv v.
    SEP_EXISTS fmlv1 fmllsv1 assgv1 vimapv1 vimaplsv1.
    ARRAY fmlv1 fmllsv1 * NUM_ARRAY assgv1 assg1 * ARRAY vimapv1 vimaplsv1 *
    &PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv1 ∧ v = fmlv1)
      (PAIR_TYPE (LIST_TYPE NUM)
        (PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv1 ∧ v = vimapv1)
          (PAIR_TYPE NUM (PAIR_TYPE (λl v. l = assg1 ∧ v = assgv1) NUM))))
      (fml1,inds1,vimap1,id1,assg1,st1) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`emp`,`vimap`,`st`,`enc c T`,`max_var (FST c)`,
      `reindex fmlls inds`,`pc.id`,`fmlls`,`assg`]>>
    simp[fslot_TYPE_def,slot_bound_enc_max_var]>>
    xsimpl>>
    rpt strip_tac>>
    gvs[PAIR_TYPE_def]>>
    metis_tac[ARRAY_NUM_ARRAY_refl])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  gvs[LIST_TYPE_def,mo_sol_update_def]
QED

(* Repeatedly parse a line and run the multi-objective cstep checker,
  returning the last encountered state *)
Definition parse_and_run_mo_def:
  parse_and_run_mo mord objs fns ss
    fml assg st inds vimap vomap pc sols =
  case parse_cstep fns ss of
    NONE => NONE
  | SOME (INL s, fns', rest) =>
    SOME (rest, s, fns', fml, inds, pc, sols)
  | SOME (INR cstep, fns', rest) =>
    (case check_mo_cstep_list mord objs cstep fml assg st inds vimap vomap pc
      sols of
      SOME (fml', assg', st', inds', vimap', vomap', pc', sols') =>
        parse_and_run_mo mord objs fns' rest
          fml' assg' st' inds' vimap' vomap' pc' sols'
    | res => NONE)
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND o SND o SND)`>>
  rw[parse_cstep_def]>>
  gvs[AllCaseEqs()]>>
  imp_res_tac parse_sstep_LENGTH>>
  fs[parse_scope_def,parse_subproof_def]>>
  imp_res_tac parse_scope_aux_LENGTH>>
  imp_res_tac parse_pre_order_LENGTH>>
  imp_res_tac parse_subproof_aux_LENGTH>>
  fs[]
End

Quote add_cakeml:
  fun check_unsat_mo'' mord objs fns fd lno fml assg st inds vimap vomap pc
    sols =
    case parse_cstep fns fd lno of
      (Inl s, (fns', lno')) =>
      (lno', (s, (fns',
        (fml, (inds, (pc, sols))))))
    | (Inr cstep, (fns', lno')) =>
      (case check_mo_cstep_arr lno mord objs cstep fml assg st inds vimap vomap
        pc sols of
        (fml', (assg', (st', (inds', (vimap', (vomap', (pc', sols'))))))) =>
        check_unsat_mo'' mord objs fns' fd lno'
          fml' assg' st' inds' vimap' vomap' pc' sols')
End

Theorem check_unsat_mo''_spec:
  ∀mord objs fns ss fmlls assg st inds vimap vomap pc sols
    mordv objsv fnsv lno lnov fmllsv assgv stv indsv pcv solsv
    lines fs fmlv vimaplsv vimapv vomapv.
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  objs_TYPE objs objsv ∧
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_REL fslot_TYPE fmlls fmllsv ∧
  fml_bound fmlls (LENGTH assg) ∧
  NUM st stv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  LIST_REL vimapn_TYPE vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  sols_TYPE sols solsv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat_mo''" (get_ml_prog_state()))
    [mordv; objsv; fnsv; fdv; lnov; fmlv; assgv; stv; indsv; vimapv; vomapv;
      pcv; solsv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          parse_and_run_mo mord objs fns ss fmlls assg st inds vimap vomap pc
            sols =
            SOME (MAP toks_fast lines',res) ∧
            PAIR_TYPE NUM (
            PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (
            PAIR_TYPE (fns_TYPE a) (
            PAIR_TYPE (λl v.
              LIST_REL fslot_TYPE l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
                  sols_TYPE))))) (lno',res) v))
      (λe.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            parse_and_run_mo mord objs fns ss fmlls assg st inds vimap vomap pc
              sols = NONE)))
Proof
  ho_match_mp_tac (fetch "-" "parse_and_run_mo_ind")>>
  rw[]>>
  xcf "check_unsat_mo''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_mo_def]>>
  Cases_on`parse_cstep fns (MAP toks_fast lines)`>>fs[]
  >- (
    xlet `(POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e))`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
        ARRAY vimapv vimaplsv`,`lines`,`fs`,`fns`,`fd`,`a`,`lno`]>>
      xsimpl>>
      rw[]>>
      qmatch_goalsub_rename_tac
        `STDIO (forwardFD fs fd kk) * INSTREAM_LINES _ fd fdv ll _`>>
      qexistsl_tac[`kk`,`ll`,`fmlv`,`fmllsv`]>>
      xsimpl)>>
    xsimpl>>
    simp[Once parse_and_run_mo_def]>>
    rw[]>>
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  xlet `(POSTv v.
    SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv fmllsv * NUM_ARRAY assgv assg * ARRAY vimapv vimaplsv *
         &(
            case parse_cstep fns (MAP toks_fast lines) of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                    NPBC_CHECK_CSTEP_TYPE)
                  (PAIR_TYPE
                  (fns_TYPE a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`ARRAY fmlv fmllsv * NUM_ARRAY assgv assg *
      ARRAY vimapv vimaplsv`,`lines`,`fs`,`fns`,`fd`,`a`,`lno`]>>
    xsimpl>>
    rw[]>>
    asm_exists_tac>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  PairCases_on`x`>>
  rename1`parse_cstep _ _ = SOME (sc,fns1,rest)`>>
  Cases_on`sc`>>
  gs[SUM_TYPE_def,PAIR_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac[`k`,`lines'`,`lno'`,`fmlv`,`fmllsv`]>>
    simp[PAIR_TYPE_def]>>
    xsimpl)>>
  rename1`parse_cstep _ _ = SOME (INR cstep,fns1,rest)`>>
  xmatch>>
  xlet`POSTve
    (λv'.
      SEP_EXISTS fmlv' fmllsv' assgv' assg' vimapv' vimaplsv'.
      ARRAY fmlv' fmllsv' * NUM_ARRAY assgv' assg' *
      ARRAY vimapv' vimaplsv' * STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      &case check_mo_cstep_list mord objs cstep fmlls assg st inds vimap vomap
          pc sols of
        NONE => F
      | SOME res =>
        PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
          (PAIR_TYPE (λl v. l = assg' ∧ v = assgv')
          (PAIR_TYPE NUM
          (PAIR_TYPE (LIST_TYPE NUM)
            (PAIR_TYPE
              (λl v. LIST_REL vimapn_TYPE l vimaplsv' ∧ v = vimapv')
              (PAIR_TYPE vomap_TYPE
                (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE sols_TYPE)))))) res v')
    (λe.
      SEP_EXISTS fmlv' fmllsv'.
      ARRAY fmlv' fmllsv' * STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e ∧
        check_mo_cstep_list mord objs cstep fmlls assg st inds vimap vomap pc
          sols = NONE))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k)`,
      `vomap`,`vimap`,`st`,`sols`,`pc`,`objs`,`mord`,`inds`,`fmlls`,`cstep`,
      `assg`,`lno`]>>
    xsimpl>>
    rw[]
    >- (first_assum (irule_at Any)>>xsimpl)>>
    qmatch_goalsub_rename_tac`ARRAY aa bb * NUM_ARRAY _ _ * _ ==>> _`>>
    qexistsl_tac[`aa`,`bb`]>>
    xsimpl)
  >- (
    xsimpl>>rw[]>>
    simp[Once parse_and_run_mo_def]>>
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>simp[]>>strip_tac>>
  rename1`check_mo_cstep_list _ _ _ _ _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>
  drule_all fml_bound_check_mo_cstep_list>>
  strip_tac>>
  fs[PAIR_TYPE_def,PULL_EXISTS]>>
  xmatch>>
  xapp>>xsimpl>>
  qexistsl_tac[`emp`,`lines'`,`forwardFD fs fd k`,`lno'`]>>
  simp[]>>xsimpl>>
  rw[]>>simp[forwardFD_o]
  >- (
    qmatch_goalsub_rename_tac
      `STDIO (forwardFD fs fd (k + kk)) * INSTREAM_LINES _ fd fdv ll _ *
        ARRAY aa bb`>>
    qexistsl_tac[`k+kk`,`ll`]>>simp[]>>
    rpt (first_assum (irule_at Any))>>
    xsimpl)>>
  simp[Once parse_and_run_mo_def]>>
  metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl]
QED

(* The conclusion section. The accepted form carries the id of the
  contradiction that closes the run; the enumeration count is not used, and
  the id is checked against the formula by check_contradiction_fml. *)
Definition parse_mo_concl_def:
  parse_mo_concl s f_ns ls =
  case parse_output_concl s f_ns ls of
    NONE => NONE
  | SOME (output,concl) =>
    (case concl of
      HEEnum _ T (SOME n) => SOME n
    | _ => NONE)
End

val res = translate parse_mo_concl_def;

val inputAllTokens_specialize =
  inputAllTokens_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Quote add_cakeml:
  fun run_mo_concl_file mord fd f_ns lno s fml' pc' sols =
  let
    val ls = TextIO.inputAllTokens #"\n" fd blanks tokenize
  in
    case parse_mo_concl s f_ns ls of
      None => Inl (format_failure (sub_one lno) (mk_parse_err s))
    | Some n =>
      if get_chk pc' then
        if check_contradiction_fml_arr False fml' n
        then Inr (ord_min mord sols)
        else Inl (format_failure lno
          "the conclusion hint does not point at a contradiction")
      else Inl (format_failure lno
        "conclusion not allowed after unchecked deletion")
  end
End

Theorem run_mo_concl_file_spec:
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  fns_TYPE a fns fnsv ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) s sv ∧
  NUM lno lnov ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc1 pc1v ∧
  sols_TYPE sols solsv ∧
  LIST_REL fslot_TYPE fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "run_mo_concl_file" (get_ml_prog_state()))
    [mordv; fdv; fnsv; lnov; sv; fml1v; pc1v; solsv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * ARRAY fml1v fmllsv)
    (POSTv v.
       SEP_EXISTS res.
       STDIO (fastForwardFD fs fd) *
       INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
       &(
        SUM_TYPE STRING_TYPE sols_TYPE res v ∧
        case res of
          INR vs =>
          vs = ord_min mord sols ∧
          pc1.chk ∧
          ∃n. check_contradiction_fml_list F fmlls n
        | INL l => T))
Proof
  rw[]>>
  xcf "run_mo_concl_file" (get_ml_prog_state ())>>
  xlet ‘(POSTv v.
          STDIO (fastForwardFD fs fd) *
          INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
          ARRAY fml1v fmllsv *
          & LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (MAP (MAP tokenize o tokens blanks) lines) v
          )’
  >- (
    xapp_spec inputAllTokens_specialize
    \\ qexists_tac ‘ARRAY fml1v fmllsv’
    \\ xsimpl
    \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]) >>
  xlet_auto
  >- (
    xsimpl>>
    simp[EqualityType_NUM_BOOL])>>
  Cases_on`parse_mo_concl s fns (MAP (MAP tokenize ∘ tokens blanks) lines)`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    rename1`STRING_TYPE ss _`>>
    qexists_tac`INL ss`>>simp[SUM_TYPE_def])>>
  xmatch>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    rename1`STRING_TYPE ss _`>>
    qexists_tac`INL ss`>>simp[SUM_TYPE_def])>>
  xlet_autop>>
  rename1`bvv = Conv _ []`>>
  `BOOL F bvv` by (fs[]>>EVAL_TAC)>>
  xlet`POSTv v.
    STDIO (fastForwardFD fs fd) *
    INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
    ARRAY fml1v fmllsv *
    &BOOL (check_contradiction_fml_list F fmlls x) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`x`,`fmlls`,`F`]>>simp[]>>
    EVAL_TAC)>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    rename1`STRING_TYPE ss _`>>
    qexists_tac`INL ss`>>simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>xsimpl>>
  qexists_tac`INR (ord_min mord sols)`>>
  simp[SUM_TYPE_def,get_chk_def]>>
  qexists_tac`x`>>
  fs[get_chk_def]
QED

Quote add_cakeml:
  fun check_unsat_mo' mord objs fns fd lno fml =
  let
    val id = List.length fml + 1
    val arr = Array.array (2*id) Empty
    val arr = fill_arr arr 1 fml
    val inds = rev_enum_full 1 fml
    val vimap = Array.array 100000 Vnone
  in
    case mk_vimap_arr 1 fml vimap 0 of (vimap,mx) =>
    let
      val assg = Array.array (mx + 1) 0
      val pc = init_conf id True None None
    in
      (case check_unsat_mo'' mord objs fns fd lno arr assg 1 inds vimap "" pc
        [] of
        (lno', (s, (fns', (fml', (inds', (pc', sols')))))) =>
      run_mo_concl_file mord fd fns' lno' s fml' pc' sols')
      handle Fail s => Inl s
    end
  end
End

Theorem parse_and_run_mo_check_mo_csteps_list:
  ∀mord objs fns ss fml assg st inds vimap vomap pc sols
    rest s fns' fml' inds' pc' sols'.
  parse_and_run_mo mord objs fns ss fml assg st inds vimap vomap pc sols =
    SOME (rest, s, fns', (fml', inds', pc', sols')) ⇒
  ∃csteps assg' st' vimap' vomap'.
  check_mo_csteps_list mord objs csteps fml assg st inds vimap vomap pc sols =
    SOME (fml', assg', st', inds', vimap', vomap', pc', sols')
Proof
  ho_match_mp_tac parse_and_run_mo_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_and_run_mo_def]>>
  every_case_tac>>fs[]
  >- (
    rw[]>>
    qexists_tac`[]`>>
    simp[check_mo_csteps_list_def])>>
  rw[]>>
  first_x_assum drule_all>>
  rw[]>>
  qexists_tac`y::csteps`>>
  simp[check_mo_csteps_list_def]
QED

Theorem check_unsat_mo'_spec:
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  objs_TYPE objs objsv ∧
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE fslot_TYPE fmls fmlv ∧
  fmls = MAP (λc. enc c T) fml
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat_mo'" (get_ml_prog_state()))
    [mordv; objsv; fnsv; fdv; lnov; fmlv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
     SEP_EXISTS k lines' res.
     STDIO (forwardFD fs fd k) *
     INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
     &(
      SUM_TYPE STRING_TYPE sols_TYPE res v ∧
      case res of
        INR vs => is_front mord vs (nondom_set mord (set fml) objs)
      | INL l => T))
Proof
  rw[]>>
  reverse (Cases_on `
    ∃c off. get_file_content fs fd = SOME (c,off)`)
  >- (
    fs[INSTREAM_LINES_def,INSTREAM_STR_def]>>
    xpull)>>
  fs[]>>
  xcf "check_unsat_mo'" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY av avs`>>
  `LIST_REL fslot_TYPE (REPLICATE (2 * (LENGTH fml + 1)) Empty) avs` by (
    rw[Abbr`avs`,LIST_REL_REPLICATE_same,fslot_TYPE_def]>>
    EVAL_TAC)>>
  xlet`POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
      STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      &LIST_REL fslot_TYPE
        (FOLDL (λacc (i,v). update_resize acc Empty v i)
          (REPLICATE (2 * (LENGTH fml + 1)) Empty)
          (enumerate 1 (MAP (λc. enc c T) fml)))
        arrlsv'`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`MAP (λc. enc c T) fml`,
      `REPLICATE (2 * (LENGTH fml + 1)) Empty`]>>
    simp[])>>
  rpt xlet_autop>>
  xlet`POSTv v. SEP_EXISTS vimapv vimaplsv.
    ARRAY vimapv vimaplsv * ARRAY resv arrlsv' * STDIO fs *
    INSTREAM_LINES #"\n" fd fdv lines fs *
    &PAIR_TYPE (λl v. LIST_REL vimapn_TYPE l vimaplsv ∧ v = vimapv) NUM
      (mk_vimap (REPLICATE 100000 Vnone) 0
        (enumerate 1 (MAP (λc. enc c T) fml))) v`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac[`REPLICATE 100000 Vnone`,`MAP (λc. enc c T) fml`]>>
    conj_tac
    >- (irule (iffRL LIST_REL_REPLICATE_same)>>EVAL_TAC)>>
    conj_tac
    >- first_assum ACCEPT_TAC>>
    rpt strip_tac>>
    first_assum (irule_at Any)>>
    xsimpl)>>
  `∃vimap1 mx.
    mk_vimap (REPLICATE 100000 Vnone) 0
      (enumerate 1 (MAP (λc. enc c T) fml)) = (vimap1,mx)` by
    metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv assgv.
    NUM_ARRAY assgv (REPLICATE (mx+1) 0) * ARRAY vimapv vimaplsv *
    ARRAY resv arrlsv' * STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs`
  >- (
    simp[npbc_arrayProgTheory.NUM_ARRAY_def]>>
    xapp>>xsimpl>>
    qexists_tac`mx+1`>>
    simp[LIST_REL_REPLICATE_same]>>
    EVAL_TAC)>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  `pres_TYPE NONE (Conv (SOME (TypeStamp «None» 2)) [])` by
    simp[OPTION_TYPE_def]>>
  `obj_TYPE NONE (Conv (SOME (TypeStamp «None» 2)) [])` by
    simp[OPTION_TYPE_def]>>
  rpt xlet_autop>>
  `EVERY (λs. slot_bound s (mx+1)) (MAP (λc. enc c T) fml)` by (
    qspecl_then [`fml`,`1`,`REPLICATE 100000 Vnone`,`0`] mp_tac
      (INST [``b:bool``|->``T``,``b':bool``|->``T``]
        npbc_listTheory.mk_vimap_bound)>>
    simp[EVERY_MAP])>>
  `fml_bound
    (FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE (2 * (LENGTH fml + 1)) Empty)
      (enumerate 1 (MAP (λc. enc c T) fml)))
    (LENGTH (REPLICATE (mx+1) (0:num)))` by (
    simp[]>>
    irule npbc_listTheory.bound_FOLDL_update_resize>>
    simp[])>>
  qabbrev_tac`fmlls =
    FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE (2 * (LENGTH fml + 1)) Empty)
      (enumerate 1 (MAP (λc. enc c T) fml))`>>
  qabbrev_tac`inds = rev_enum_full 1 (MAP (λc. enc c T) fml)`>>
  qabbrev_tac`assg = REPLICATE (mx+1) (0:num)`>>
  `vomap_TYPE «» (Litv (StrLit «»))` by EVAL_TAC>>
  `sols_TYPE [] (Conv (SOME (TypeStamp «[]» 1)) [])` by EVAL_TAC>>
  Cases_on`
    parse_and_run_mo mord objs fns (MAP toks_fast lines) fmlls assg 1 inds
      vimap1 «» (init_conf (LENGTH fml + 1) T NONE NONE) []`
  >- (
    xhandle`POSTe e.
      SEP_EXISTS k lines' fmlv' fmllsv'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e)`
    >- (
      rpt xlet_autop>>
      xlet`POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e)`
      >- (
        xapp>>xsimpl>>
        qexistsl_tac[`emp`,`vimap1`,`[]`,
          `init_conf (LENGTH fml + 1) T NONE NONE`,`objs`,`mord`,`lines`,
          `inds`,`fs`,`fns`,`fmlls`,`fd`,`assg`,`a`,`lno`]>>
        xsimpl>>rw[]>>
        qmatch_goalsub_rename_tac
          `ARRAY _ _ * STDIO (forwardFD fs fd kk) *
            INSTREAM_LINES _ fd fdv ll _ ==>> _`>>
        qexistsl_tac[`kk`,`ll`]>>
        xsimpl)
      >- xsimpl)>>
    fs[Fail_exn_def]>>
    xcases>>
    xcon>>xsimpl>>
    CONV_TAC (RESORT_EXISTS_CONV (List.rev))>>
    qexists_tac`INL s`>>
    simp[SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xhandle`POSTv v.
     SEP_EXISTS k lines' res.
     STDIO (forwardFD fs fd k) *
     INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
     &(
      SUM_TYPE STRING_TYPE sols_TYPE res v ∧
      case res of
        INR vs => is_front mord vs (nondom_set mord (set fml) objs)
      | INL l => T)`
  >- (
    rpt xlet_autop>>
    xlet`POSTv v.
       SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          parse_and_run_mo mord objs fns (MAP toks_fast lines)
            fmlls assg 1 inds vimap1 «»
            (init_conf (LENGTH fml + 1) T NONE NONE) [] =
              SOME (MAP toks_fast lines',res) ∧
            PAIR_TYPE NUM (
            PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (
            PAIR_TYPE (fns_TYPE a) (
            PAIR_TYPE (λl v. LIST_REL fslot_TYPE l fmllsv' ∧ v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
                sols_TYPE))))) (lno',res) v)`
    >- (
      xapp>>xsimpl>>
      qexistsl_tac[`emp`,`vimap1`,`[]`,
        `init_conf (LENGTH fml + 1) T NONE NONE`,`objs`,`mord`,`lines`,
        `inds`,`fs`,`fns`,`fmlls`,`fd`,`assg`,`a`,`lno`]>>
      xsimpl>>rw[]>>
      qmatch_goalsub_rename_tac
        `STDIO (forwardFD fs fd kk) * INSTREAM_LINES _ fd fdv ll _ *
          ARRAY aa bb ==>> _`>>
      qexistsl_tac[`kk`,`ll`]>>simp[]>>
      rpt (first_assum (irule_at Any))>>
      xsimpl)>>
    gvs[]>>
    PairCases_on`res`>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[]>>
    irule_at Any STDIO_INSTREAM_LINES_refl_gc>>
    gvs[]>>
    qexists_tac`(res1,res2)`>>simp[PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    xsimpl>>rw[]>>
    `∃k'.
      fastForwardFD (forwardFD fs fd k) fd =
      forwardFD (forwardFD fs fd k) fd k'` by
      (match_mp_tac (GEN_ALL fast_forwardFD_forwardFD_exists)>>
      simp[fsFFIPropsTheory.get_file_content_forwardFD])>>
    simp[forwardFD_o]>>
    first_x_assum(irule_at Any)>>
    qexists_tac`k+k'`>>
    qexists_tac`[]`>>xsimpl>>
    gvs[AllCasePreds()]>>
    drule parse_and_run_mo_check_mo_csteps_list>>
    rw[]>>
    `vimap1 = FST (mk_vimap (REPLICATE 100000 Vnone) 0
      (enumerate 1 (MAP (λc. enc c T) fml)))` by simp[]>>
    pop_assum SUBST_ALL_TAC>>
    `«» = mk_vomap_opt (NONE:((int # num) list # int) option)` by
      simp[mk_vomap_opt_def]>>
    pop_assum SUBST_ALL_TAC>>
    unabbrev_all_tac>>
    fs[rev_enum_full_rev_enumerate]>>
    drule_at (Pos (el 4)) check_mo_csteps_list_concl>>
    disch_then irule>>
    simp[]>>
    metis_tac[npbc_slotTheory.dm_rel_FEMPTY_REPLICATE])>>
  xsimpl
QED

Quote add_cakeml:
  fun check_unsat_mo_top mord objs fns fml fname =
  let
    val fd = TextIO.openIn fname
  in
    case check_header fd of
      Some n =>
      (TextIO.closeIn fd;
      Inl (format_failure n "Unable to parse header"))
    | None =>
      let val res = (check_unsat_mo' mord objs fns fd 3 fml)
        val close = TextIO.closeIn fd;
      in
        res
      end
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem check_unsat_mo_top_spec:
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  objs_TYPE objs objsv ∧
  fns_TYPE a fns fnsv ∧
  LIST_TYPE fslot_TYPE fmls fmlv ∧
  fmls = MAP (λc. enc c T) fml ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_mo_top"(get_ml_prog_state()))
  [mordv; objsv; fnsv; fmlv; fv]
  (STDIO fs)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
      SUM_TYPE STRING_TYPE sols_TYPE res v ∧
      case res of
        INR vs => is_front mord vs (nondom_set mord (set fml) objs)
      | INL l => T))
Proof
  rw[]>>
  xcf"check_unsat_mo_top"(get_ml_prog_state()) >>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >-
      (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      qexists_tac`INL (notfound_string f)`>>
      simp[SUM_TYPE_def])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`)) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fd fdv lines fss`>>
  xlet`POSTv v.
    SEP_EXISTS k lines' res.
    STDIO (forwardFD fss fd k) *
    INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fss fd k) *
    &OPTION_TYPE NUM res v`
  >- (
    xapp>>
    qexists_tac`emp`>>
    xsimpl>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc,STAR_COMM])>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fd fdv _ fsss`>>
  reverse (Cases_on`res`)>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet `POSTv v. STDIO fs`
    >- (
      xapp_spec closeIn_spec_lines >>
      xsimpl>>
      qexists_tac `emp`>>
      qexists_tac `lines'` >>
      qexists_tac `fsss`>>
      qexists_tac `fd` >>
      qexists_tac `#"\n"` >>
      conj_tac THEN1
        (unabbrev_all_tac
        \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
        \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
      xsimpl>>
      `validFileFD fd fsss.infds` by
        (unabbrev_all_tac>> simp[validFileFD_forwardFD]
         \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
         \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
      xsimpl >> rw [] >>
      unabbrev_all_tac>>xsimpl>>
      simp[forwardFD_ADELKEY_same]>>
      DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
      xsimpl>>
      imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
      imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [])>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    rename1`STRING_TYPE s sv`>>
    qexists_tac`INL s`>>simp[SUM_TYPE_def])>>
  xlet`POSTv v. SEP_EXISTS k lines' res.
          STDIO (forwardFD fsss fd k) *
          INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fsss fd k) *
          &(
          SUM_TYPE STRING_TYPE sols_TYPE res v ∧
          case res of
            INR vs => is_front mord vs (nondom_set mord (set fml) objs)
          | INL l => T)`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any))>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec closeIn_spec_lines >>
    xsimpl>>
    qexists_tac `emp`>>
    qexists_tac `lines'` >>
    qexists_tac `forwardFD fsss fd k'`>>
    qexists_tac `fd` >>
    qexists_tac `#"\n"` >>
    conj_tac THEN1
      (unabbrev_all_tac
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    xsimpl>>
    `validFileFD fd (forwardFD fsss fd k').infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    unabbrev_all_tac>>xsimpl>>
    simp[forwardFD_ADELKEY_same]>>
    DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
    xsimpl>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [])>>
  xvar>>xsimpl>>
  asm_exists_tac>>fs[]
QED

(*
  A string pbc -> npbc normaliser frontend for multi-objective problems
*)

Theorem normalise_objs_eq:
  normalise_objs objs =
  MAP (λob. case normalise_obj (SOME ob) of NONE => ([],0i) | SOME ob' => ob')
    objs
Proof
  rw[normalise_objs_def,MAP_EQ_f]>>
  qspec_then `ob` strip_assume_tac normalise_obj_SOME>>
  simp[]
QED

val res = translate normalise_objs_eq;
val res = translate normalise_mo_prob_def;
val res = translate name_to_num_objs_def;
val res = translate name_to_num_mo_prob_def;

Definition normalise_full_mo_def:
  normalise_full_mo mprob =
  let s = init_state hash_str compare in
  let (mprob',t) = name_to_num_mo_prob mprob s in
  (normalise_mo_prob mprob', t)
End

val res = translate normalise_full_mo_def;

Quote add_cakeml:
  fun check_unsat_mo_top_norm mord mprob fname =
  case normalise_full_mo mprob of
    ((objs,fml),t) =>
    check_unsat_mo_top mord objs (name_to_num_var_nf,t) (enc_list fml) fname
End

Overload "mo_prob_TYPE" = ``
  PAIR_TYPE
  (LIST_TYPE
    (PAIR_TYPE
      (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
      INT))
  (LIST_TYPE
    (PAIR_TYPE (PBC_PBHD_TYPE STRING_TYPE)
      (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
        INT)))``

Theorem check_unsat_mo_top_norm_spec:
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  mo_prob_TYPE mprob mprobv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_mo_top_norm"
    (get_ml_prog_state()))
  [mordv; mprobv; fv]
  (STDIO fs)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
       SUM_TYPE STRING_TYPE sols_TYPE res v ∧
       case res of
         INR vs =>
         is_front mord vs
           (pbc_mo$nondom_set mord (set (SND mprob)) (FST mprob))
       | INL l => T))
Proof
  rw[]>>
  xcf"check_unsat_mo_top_norm"(get_ml_prog_state()) >>
  xlet_autop>>
  `∃objs fml t. normalise_full_mo mprob = ((objs,fml),t)` by
    metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xapp_spec (check_unsat_mo_top_spec |> INST_TYPE[alpha|->``:mlstring name_to_num_state``])>>
  qexistsl_tac[`emp`,`objs`,`mord`,`fs`,`fml`]>>
  xsimpl>>
  qexistsl_tac[`f`,`PBC_NORMALISE_NAME_TO_NUM_STATE_TYPE STRING_TYPE`,
    `(name_to_num_var_nf,t)`]>>
  CONJ_TAC >- (
    gvs[npbc_arrayProgTheory.LIST_TYPE_fslot_TYPE,enc_list_def,EVERY_MAP,
      PAIR_TYPE_def]>>
    metis_tac[fetch "npbc_parseProg" "name_to_num_var_nf_v_thm"])>>
  rw[]>>
  asm_exists_tac>>simp[]>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`mprob`>>
  gvs[normalise_full_mo_def]>>
  pairarg_tac>>gvs[]>>
  PairCases_on`mprob'`>>
  drule full_normalise_mo_nondom>>
  disch_then (drule_at (Pos last))>>
  disch_then (qspec_then `mord` mp_tac)>>
  impl_tac >- (
    simp[]>>
    match_mp_tac init_state_ok>>
    fs[TotOrd_compare])>>
  metis_tac[]
QED

(*** Shared by the frontends: selecting the ordering, printing the problem
  and printing the frontier ***)

val res = translate parse_mo_ord_def;

val res = translate mo_ord_name_def;

val res = translate print_mo_prob_def;

(* The verified front is printed one vector per semicolon-separated group *)
Definition print_vec_def:
  print_vec (v:int list) =
  concatWith « » (MAP (int_to_string #"-") v)
End

Definition print_front_str_def:
  print_front_str ord vs =
  concat [
    «s VERIFIED »; mo_ord_name ord; « FRONTIER: »;
    concatWith «; » (MAP print_vec vs);
    «\n»]
End

Definition map_front_to_string_def:
  (map_front_to_string ord (INL s) = (INL s)) ∧
  (map_front_to_string ord (INR vs) = INR (print_front_str ord vs))
End

val res = translate print_vec_def;
val res = translate print_front_str_def;
val res = translate map_front_to_string_def;
