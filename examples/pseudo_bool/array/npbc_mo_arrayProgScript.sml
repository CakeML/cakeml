(*
  Refine the multi-objective PB proof checker to CakeML
*)
Theory npbc_mo_arrayProg
Ancestors
  npbc_check pbc_mo npbc_mo npbc_mo_check npbc_list npbc_mo_list
  pb_parse pbc_normalise npbc_arrayProg npbc_parseProg
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

val res = translate ord_le_def;

val res = translate ord_lt_def;

val res = translate ord_equiv_def;

val res = translate ord_dedup_def;

val res = translate ord_min_def;

val res = translate npbc_moTheory.obj_vecs_def;

(* The Pareto dominance order check *)

val res = translate mo_obj_vars_def;

val res = translate mo_vars_covered_def;

val res = translate var_le_def;

val res = translate rename_obj_def;

val res = translate vs_to_us_def;

val res = translate pareto_constrs_def;

val res = translate check_imp_any_def;

val res = translate pareto_ord_ok_def;

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
  mo_sol_ok objs (pc:proof_conf) (ws:num_set) ⇔
    pc.chk ∧ mo_vars_covered objs ws
End

val res = translate mo_sol_ok_def;

Definition mo_sol_update_def:
  mo_sol_update pc id' =
    pc with <| id := id'; enum := pc.enum + 1 |>
End

val res = translate mo_sol_update_def;

(* The multi-objective cstep checker: solution logging is bespoke,
  every other step is delegated to check_cstep_arr *)
Quote add_cakeml:
  fun check_mo_cstep_arr lno mord objs cstep fml zeros inds vimap vomap pc sols =
  case get_sol cstep of
    Some w =>
    let val ws = list_to_num_set (map_fst w) in
      if mo_sol_ok objs pc ws then
        (case check_obj None w
          (map_snd (core_fmlls_arr fml inds)) None of
          None =>
            raise Fail (format_failure lno
              "logged solution does not satisfy the core constraints")
        | Some neww =>
          let
            val wsol = snd neww
            val id = get_id pc
            val c = model_banning (Some ws) wsol
          in
            (Array.updateResize fml None id (Some (c,True)),
            (zeros,
            (sorted_insert id inds,
            (update_vimap_arr True vimap id (fst c),
            (vomap,
            (mo_sol_update pc (id+1),
             obj_vecs objs wsol :: sols))))))
          end)
      else
        raise Fail (format_failure lno
          "solution logging requires an unchecked-deletion-free proof state and an assignment to every objective variable")
    end
  | None =>
    if mo_cstep_ok mord objs cstep pc then
      (case check_cstep_arr lno cstep fml zeros inds vimap vomap pc of
        (fml', (zeros', (inds', (vimap', (vomap', pc'))))) =>
        (fml', (zeros', (inds', (vimap', (vomap', (pc', sols)))))))
    else
      raise Fail (format_failure lno
        "step not permitted: redundance and checked deletion need a loaded order, and a loaded order must refine the selected objective ordering")
End


Theorem check_mo_cstep_arr_spec:
  NUM lno lnov ∧
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  objs_TYPE objs objsv ∧
  NPBC_CHECK_CSTEP_TYPE cstep cstepv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  sols_TYPE sols solsv ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_mo_cstep_arr" (get_ml_prog_state()))
    [lnov; mordv; objsv; cstepv; fmlv; zerosv; indsv; vimapv; vomapv; pcv; solsv]
    (ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        &(
          case check_mo_cstep_list mord objs cstep fmlls zeros inds vimap vomap
            pc sols of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE (λl v.
                    LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                    v = vimapv')
                  (PAIR_TYPE (vomap_TYPE)
                  (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
                    sols_TYPE)))))
                res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
          vimapv' vimaplsv'.
        ARRAY fmlv' fmllsv' * W8ARRAY zerosv' zeros' *
        ARRAY vimapv' vimaplsv' *
        & (Fail_exn e ∧
          check_mo_cstep_list mord objs cstep fmlls zeros inds vimap vomap
            pc sols = NONE)))
Proof
  rw[]>>
  xcf "check_mo_cstep_arr" (get_ml_prog_state ())>>
  simp[check_mo_cstep_list_def]>>
  xlet_autop>>
  Cases_on`get_sol cstep`>>
  gvs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      gvs[check_mo_cstep_sol_list_def,mo_sol_ok_def]>>
      metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
    xlet_auto
    >- (
      rw[]>>xsimpl>>
      TOP_CASE_TAC>>rw[]>>
      metis_tac[ARRAY_W8ARRAY_refl])
    >- (
      xsimpl>>
      metis_tac[ARRAY_W8ARRAY_refl])>>
    gvs[AllCasePreds()]>>
    PairCases_on`res`>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl)>>
  rpt xlet_autop>>
  gvs[check_mo_cstep_sol_list_def,mo_sol_ok_def,map_fst_def]>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    fs[Fail_exn_def]>>
    metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
  rpt xlet_autop>>
  xlet`(POSTv v.
       ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv *
       &OPTION_TYPE (PAIR_TYPE INT (NUM --> BOOL))
         (check_obj NONE x (map_snd (core_fmlls fmlls inds)) NONE) v)`
  >- (
    xapp>>xsimpl>>
    rpt $ first_x_assum (irule_at Any)>>
    qexists_tac`NONE`>>
    qexists_tac`NONE`>>
    xsimpl>>
    simp[OPTION_TYPE_def])>>
  Cases_on`check_obj NONE x (map_snd (core_fmlls fmlls inds)) NONE`>>
  gvs[OPTION_TYPE_def,map_snd_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_W8ARRAY_refl])>>
  rpt xlet_autop>>
  rename1`check_obj _ _ _ _ = SOME xxx`>>
  Cases_on`xxx`>>gvs[PAIR_TYPE_def]>>
  qmatch_goalsub_abbrev_tac`model_banning aaa bbb`>>
  xlet`POSTv v.
    ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv *
    &constraint_TYPE (model_banning aaa bbb) v`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    qexists_tac`aaa`>>
    simp[OPTION_TYPE_def,Abbr`aaa`])>>
  rpt xlet_autop>>
  rename1`bvv = Conv _ []`>>
  `BOOL T bvv` by
    (fs[]>>EVAL_TAC)>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  gvs[LIST_TYPE_def,mo_sol_update_def,get_id_def]>>
  match_mp_tac LIST_REL_update_resize>>
  fs[OPTION_TYPE_def,PAIR_TYPE_def]
QED

(* Repeatedly parse a line and run the multi-objective cstep checker,
  returning the last encountered state *)
Definition parse_and_run_mo_def:
  parse_and_run_mo mord objs fns ss
    fml zeros inds vimap vomap pc sols =
  case parse_cstep fns ss of
    NONE => NONE
  | SOME (INL s, fns', rest) =>
    SOME (rest, s, fns', fml, inds, pc, sols)
  | SOME (INR cstep, fns', rest) =>
    (case check_mo_cstep_list mord objs cstep fml zeros inds vimap vomap pc sols of
      SOME (fml', zeros', inds', vimap', vomap', pc', sols') =>
        parse_and_run_mo mord objs fns' rest
          fml' zeros' inds' vimap' vomap' pc' sols'
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
  fun check_unsat_mo'' mord objs fns fd lno fml zeros inds vimap vomap pc sols =
    case parse_cstep fns fd lno of
      (Inl s, (fns', lno')) =>
      (lno', (s, (fns',
        (fml, (inds, (pc, sols))))))
    | (Inr cstep, (fns', lno')) =>
      (case check_mo_cstep_arr lno mord objs cstep fml zeros inds vimap vomap pc sols of
        (fml', (zeros', (inds', (vimap', (vomap', (pc', sols')))))) =>
        check_unsat_mo'' mord objs fns' fd lno'
          fml' zeros' inds' vimap' vomap' pc' sols')
End

Theorem check_unsat_mo''_spec:
  ∀mord objs fns ss fmlls zeros inds vimap vomap pc sols
    mordv objsv fnsv lno lnov fmllsv zerosv indsv pcv solsv
    lines fs fmlv vimaplsv vimapv vomapv.
  PBC_MO_MO_ORD_TYPE mord mordv ∧
  objs_TYPE objs objsv ∧
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv ∧
  vomap_TYPE vomap vomapv ∧
  sols_TYPE sols solsv ∧
  EVERY (λw. w = 0w) zeros ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat_mo''" (get_ml_prog_state()))
    [mordv; objsv; fnsv; fdv; lnov; fmlv; zerosv; indsv; vimapv; vomapv; pcv; solsv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
      ARRAY vimapv vimaplsv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          parse_and_run_mo mord objs fns ss fmlls zeros inds vimap vomap pc sols =
            SOME (MAP toks_fast lines',res) ∧
            PAIR_TYPE NUM (
            PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (
            PAIR_TYPE (fns_TYPE a) (
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
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
            parse_and_run_mo mord objs fns ss fmlls zeros inds vimap vomap pc
              sols = NONE)))
Proof
  ho_match_mp_tac (fetch "-" "parse_and_run_mo_ind")>>
  rw[]>>
  xcf "check_unsat_mo''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_mo_def]>>
  Cases_on`parse_cstep fns (MAP toks_fast lines)`>>fs[]
  >- ((* parse_cstep NONE *)
    xlet `(POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e))`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv`>>
      qexists_tac`lines`>>simp[]>>
      qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
      rw[]>>
      qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
      qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)>>
    xsimpl>>
    simp[Once parse_and_run_mo_def]>>
    rw[]>>
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  (* parse_cstep SOME *)
  xlet `(POSTv v.
    SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv *
         &(
            case parse_cstep fns (MAP toks_fast lines) of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_CSTEP_TYPE)
                  (PAIR_TYPE
                  (fns_TYPE a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY fmlv fmllsv * W8ARRAY zerosv zeros * ARRAY vimapv vimaplsv`>>
    qexists_tac`lines`>>simp[]>>
    qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
    PairCases_on`x`>>fs[]>>rw[]>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  PairCases_on`x`>>
  Cases_on`x0`>>
  gs[SUM_TYPE_def,PAIR_TYPE_def]
  >- (
    (* INL *)
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def]
    >- (
      simp[]>>
      first_x_assum (irule_at Any)>>
      first_x_assum (irule_at Any)>>
      qexists_tac`lines'`>>
      qexists_tac`k`>>simp[]>>
      xsimpl)>>
    simp[Once parse_and_run_mo_def])>>
  (* INR *)
  xmatch>>
  xlet`
    POSTve
    (λv'.
         SEP_EXISTS fmlv' fmllsv' zerosv' zeros'
           vimapv' vimaplsv'.
           W8ARRAY zerosv' zeros' * ARRAY fmlv' fmllsv' *
           ARRAY vimapv' vimaplsv' * STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &case check_mo_cstep_list mord objs y fmlls zeros inds vimap vomap pc sols of
             NONE => F
           | SOME res =>
             PAIR_TYPE
               (λl v.
                    LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
                    v = fmlv')
               (PAIR_TYPE
                  (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros')
                  (PAIR_TYPE (LIST_TYPE NUM)
                     (PAIR_TYPE
                       (λl v.
                         LIST_REL (OPTION_TYPE vimapn_TYPE) l vimaplsv' ∧
                         v = vimapv')
                        (PAIR_TYPE vomap_TYPE
                          (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
                            sols_TYPE)))))
               res v')
    (λe.
         SEP_EXISTS fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            check_mo_cstep_list mord objs y fmlls zeros inds vimap vomap pc sols = NONE))`
  >- (
    xapp>>
    xsimpl>>reverse (rw[])>>
    rpt(first_x_assum (irule_at Any))>>
    xsimpl>>
    CONJ_TAC >-
      metis_tac[ARRAY_W8ARRAY_refl]>>
    rw[]>>
    rename1`ARRAY aa bb`>>
    qexists_tac`aa`>>qexists_tac`bb`>>xsimpl)
  >- (
    xsimpl>>rw[]>>
    simp[Once parse_and_run_mo_def]>>
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  pop_assum mp_tac>>TOP_CASE_TAC>>simp[]>>
  strip_tac>>
  PairCases_on`x`>>fs[PAIR_TYPE_def,PULL_EXISTS]>>
  xmatch>>
  xapp>>xsimpl>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>xsimpl>>
  qexists_tac`(forwardFD fs fd k)`>>
  xsimpl>>
  rw[]>>simp[forwardFD_o]
  >- (
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`x'`>>
    simp[]>>
    qexists_tac`k+x`>>
    xsimpl)>>
  simp[Once parse_and_run_mo_def]>>
  qexists_tac`k+x`>>qexists_tac`x'`>>xsimpl>>
  qmatch_goalsub_abbrev_tac`ARRAY A B`>>
  qexists_tac`A`>>qexists_tac`B`>>xsimpl
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
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
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
    val arr = Array.array (2*id) None
    val arr = fill_arr arr 1 fml
    val zeros = Word8Array.array 100000 w8z
    val inds = rev_enum_full 1 fml
    val vimap = Array.array 100000 None
    val vimap = fold_update_vimap_enum_arr 1 fml vimap
    val pc = init_conf id True None None
  in
    (case check_unsat_mo'' mord objs fns fd lno arr zeros inds vimap "" pc [] of
      (lno', (s, (fns', (fml', (inds', (pc', sols')))))) =>
    run_mo_concl_file mord fd fns' lno' s fml' pc' sols')
    handle Fail s => Inl s
  end
End

Theorem parse_and_run_mo_check_mo_csteps_list:
  ∀mord objs fns ss fml zeros inds vimap vomap pc sols
    rest s fns' fml' inds' pc' sols'.
  parse_and_run_mo mord objs fns ss fml zeros inds vimap vomap pc sols =
    SOME (rest, s, fns', (fml', inds', pc', sols')) ⇒
  ∃csteps zeros' vimap' vomap'.
  check_mo_csteps_list mord objs csteps fml zeros inds vimap vomap pc sols =
    SOME (fml', zeros', inds', vimap', vomap', pc', sols')
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
  LIST_TYPE constraint_TYPE fml fmlv
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
  `LIST_REL (OPTION_TYPE bconstraint_TYPE) (REPLICATE (2 * (LENGTH fml + 1)) NONE) avs` by
    simp[Abbr`avs`,LIST_REL_REPLICATE_same,OPTION_TYPE_def,PAIR_TYPE_def]>>
  xlet`
  (POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
      STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      & LIST_REL (OPTION_TYPE bconstraint_TYPE)
      (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE (2 * (LENGTH fml + 1)) NONE)
      (enumerate 1 fml)) arrlsv')`
  >- (
    xapp>>
    xsimpl>>
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>xsimpl)>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY cv cvs * _`>>
  `LIST_REL (OPTION_TYPE vimapn_TYPE) (REPLICATE 100000 NONE) cvs` by
    simp[Abbr`cvs`,LIST_REL_REPLICATE_same,OPTION_TYPE_def,PAIR_TYPE_def]>>
  xlet`POSTv vimapv. SEP_EXISTS vimaplsv.
    ARRAY vimapv vimaplsv * W8ARRAY v' (REPLICATE 100000 w8z) *
    ARRAY resv arrlsv' * STDIO fs *
    INSTREAM_LINES #"\n" fd fdv lines fs *
     &LIST_REL (OPTION_TYPE vimapn_TYPE)
       (mk_vimap (REPLICATE 100000 NONE) (enumerate 1 fml)) vimaplsv`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
  rpt xlet_autop>>
  gvs[]>>
  `pres_TYPE NONE (Conv (SOME (TypeStamp «None» 2)) [])` by
    simp[OPTION_TYPE_def]>>
  `obj_TYPE NONE (Conv (SOME (TypeStamp «None» 2)) [])` by
    simp[OPTION_TYPE_def]>>
  rpt xlet_autop>>
  qmatch_asmsub_abbrev_tac`LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv`>>
  qmatch_asmsub_abbrev_tac`LIST_TYPE _ inds indsv`>>
  qmatch_asmsub_abbrev_tac`LIST_REL (OPTION_TYPE vimapn_TYPE) vimap vimaplsv`>>
  qmatch_goalsub_abbrev_tac`W8ARRAY zerosv zeros`>>
  `EVERY (λw. w = 0w) zeros` by
    gvs[Abbr`zeros`,w8z_def]>>
  `vomap_TYPE «» (Litv (StrLit «»))` by EVAL_TAC>>
  `sols_TYPE [] (Conv (SOME (TypeStamp «[]» 1)) [])` by EVAL_TAC>>
  Cases_on`
    parse_and_run_mo mord objs fns (MAP toks_fast lines) fmlls zeros inds vimap
      «» (init_conf (LENGTH fml + 1) T NONE NONE) []`
  >- (
    (* fail to parse and run *)
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
        rpt(asm_exists_tac>>simp[])>>
        qexists_tac`emp`>>
        qexists_tac`lines`>>
        qexists_tac`fs`>>
        qexists_tac`fd`>>
        xsimpl>>
        rw[]>>
        qexists_tac`x`>>qexists_tac`x'`>>xsimpl)
      >- xsimpl) >>
    fs[Fail_exn_def]>>
    xcases>>
    xcon>> xsimpl>>
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
            fmlls zeros inds vimap «»
            (init_conf (LENGTH fml + 1) T NONE NONE) [] =
              SOME (MAP toks_fast lines',res) ∧
            PAIR_TYPE NUM (
            PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (
            PAIR_TYPE (fns_TYPE a) (
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE NPBC_CHECK_PROOF_CONF_TYPE
                sols_TYPE))))) (lno',res) v)`
    >- (
      xapp>>xsimpl>>
      rpt(asm_exists_tac>>simp[])>>
      qexists_tac`emp`>>
      qexists_tac`lines`>>
      qexists_tac`fs`>>
      qexists_tac`fd`>>
      xsimpl>>
      rw[]>>
      first_x_assum(irule_at Any)>>
      metis_tac[STDIO_INSTREAM_LINES_ARRAY_refl])>>
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
    match_mp_tac (GEN_ALL check_mo_csteps_list_concl)>>
    first_x_assum (irule_at Any)>>
    unabbrev_all_tac>>
    gs[rev_enum_full_rev_enumerate,w8z_def]>>
    pop_assum (irule_at Any)>>
    gvs[])>>
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
  LIST_TYPE constraint_TYPE fml fmlv ∧
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
    check_unsat_mo_top mord objs (name_to_num_var_nf,t) fml fname
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
  xlet_autop>>
  xapp_spec (check_unsat_mo_top_spec |> INST_TYPE[alpha|->``:mlstring name_to_num_state``])>>
  rpt(first_x_assum (irule_at Any))>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  qexists_tac`(name_to_num_var_nf,t)`>>
  qexists_tac`PBC_NORMALISE_NAME_TO_NUM_STATE_TYPE STRING_TYPE`>>
  qexists_tac`emp`>>
  xsimpl>>
  CONJ_TAC >- (
    simp[PAIR_TYPE_def]>>
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
