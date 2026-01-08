(*
   The top-level printing adjustment, as called by the REPL.
*)
Theory printTweaks
Ancestors
  addPrintVals addTypePP infer
Libs
  BasicProvers dep_rewrite[qualified]

Definition print_failure_message_def:
  print_failure_message (s:mlstring) =
  Dlet unknown_loc Pany (App Opapp [Var (Short «print_pp»);
        (App Opapp [Var (Long «PrettyPrinter» (Short «failure_message»));
            Lit (StrLit s)])])
End

Definition add_err_message_def:
  add_err_message s decs_ext st =
  (* something's gone wrong, try to add a message *)
  let (ienv, inf_st) = st in
  let pmsg = [print_failure_message s] in
  case infer_ds ienv pmsg inf_st of
  | (Success msg_ienv, inf_st2) =>
        (pmsg ++ decs_ext, (extend_dec_ienv msg_ienv ienv, inf_st2))
  (* if even that fails, skip it *)
  | (Failure _, _) => (decs_ext, (ienv, inf_st))
End

Definition add_print_from_opts_def:
  add_print_from_opts nm [] (decs_ext, st) =
  add_err_message («exhausted print options for » ^ nm) decs_ext st /\
  add_print_from_opts nm (print_opt :: xs) (decs_ext, st) =
  let (ienv, inf_st) = st in
  case infer_ds ienv [print_opt] inf_st of
  | (Success ienv2, inf_st2) =>
        (print_opt :: decs_ext, (extend_dec_ienv ienv2 ienv, inf_st2))
  | (Failure x, _) =>
  let (decs_ext, st) = add_err_message
        («adding val pretty-print: » ^ SND x) decs_ext st in
  add_print_from_opts nm xs (decs_ext, st)
End

(* really just FOLDR but the translator can't get that right *)
Definition add_prints_from_opts_def:
  add_prints_from_opts [] decs_plus_st = decs_plus_st /\
  add_prints_from_opts ((nm, opts) :: xs) decs_plus_st =
  add_prints_from_opts xs (add_print_from_opts nm opts decs_plus_st)
End

Definition add_print_features_def:
  add_print_features st decs =
  let (tn, ienv, next_id) = st in
  let decs2 = add_pp_decs tn.pp_fixes decs in
  case infer_ds ienv decs2 (init_infer_state <| next_id := next_id |>) of
  (Success decs_ienv, inf_st) =>
  let (prints, tn2) = val_prints tn ienv decs_ienv in
  let ienv2 = extend_dec_ienv decs_ienv ienv in
  let (print_decs_ext, i_st) = add_prints_from_opts prints ([], (ienv2, inf_st)) in
  (Success (decs2 ++ REVERSE print_decs_ext, (tn2, i_st)))
  | (Failure x, _) =>
  (* maybe the default pretty-printer decs are the problem *)
  (case infer_ds ienv decs (init_infer_state <| next_id := next_id |>) of
  (Success ienv3, inf_st3) =>
  let (decs_ext, i_st) = add_err_message («adding type pp funs: » ^ SND x)
        [] (extend_dec_ienv ienv3 ienv, inf_st3) in
  (Success (decs ++ REVERSE decs_ext, (tn, i_st)))
  | (Failure x, _) => Failure x
  )
End

Definition read_next_dec_def:
  read_next_dec =
    [Dlet (Locs UNKNOWNpt UNKNOWNpt) Pany
       (App Opapp
          [App Opderef [Var (Long «Repl» (Short «readNextString»))];
           Con NONE []])]
End

Definition add_print_then_read_def:
  add_print_then_read types decs =
    case add_print_features types decs of
    | Failure x => Failure x
    | Success (new_decs,(tn,ienv,inf_st)) =>
        case infer_ds ienv read_next_dec inf_st of
        | (Success read_ienv, inf_st2) =>
            (Success (new_decs ++ read_next_dec,
                      (tn,extend_dec_ienv read_ienv ienv, inf_st2.next_id)))
        | (Failure x, _) => Failure x
End

Theorem eq_inf_x[local] =
  ``(v1 with inf_v := v2.inf_v) = v2`` |> REWRITE_CONV [inf_env_component_equality]
    |> GSYM |> MATCH_MP EQ_IMPLIES

Theorem infer_ds_append:
  !xs ys ienv st. infer_ds ienv (xs ++ ys) st =
  (case infer_ds ienv xs st of
    (Failure x, y) => (Failure x, y)
  | (Success ienv2, st2) =>
  (case infer_ds (extend_dec_ienv ienv2 ienv) ys st2 of
    (Failure x, y) => (Failure x, y)
  | (Success ienv3, st3) => (Success (extend_dec_ienv ienv3 ienv2), st3)
  ))
Proof
  Induct
  >- (
    rw [infer_d_def, st_ex_return_def, extend_dec_ienv_def]
    \\ simp [eq_inf_x]
    \\ every_case_tac \\ simp []
  )
  >- (
    rw [infer_d_def, st_ex_return_def, st_ex_bind_def]
    \\ fs [extend_dec_ienv_def]
    \\ every_case_tac \\ fs []
  )
QED

Theorem add_err_message_infer:
  add_err_message s decs_ext (extend_dec_ienv ienv init_ienv, inf_st) =
    (decs_ext2, st2) /\
  infer_ds init_ienv (REVERSE decs_ext) init_inf_st = (Success ienv, inf_st) ==>
  ?ienv_res inf_st2 ienv2.
  st2 = (ienv_res, inf_st2) /\
  infer_ds init_ienv (REVERSE decs_ext2) init_inf_st = (Success ienv2, inf_st2) /\
  ienv_res = extend_dec_ienv ienv2 init_ienv
Proof
  simp [add_err_message_def]
  \\ every_case_tac
  \\ rw []
  \\ simp [infer_ds_append]
  \\ simp [extend_dec_ienv_def]
QED

Theorem add_print_from_opts_infer:
  !opts decs_ext ienv inf_st decs_ext2 ienv_res inf_st2.
  add_print_from_opts nm opts (decs_ext, (extend_dec_ienv ienv init_ienv, inf_st)) =
    (decs_ext2, st2) /\
  infer_ds init_ienv (REVERSE decs_ext) init_inf_st = (Success ienv, inf_st) ==>
  ?ienv_res inf_st2 ienv2.
  st2 = (ienv_res, inf_st2) /\
  infer_ds init_ienv (REVERSE decs_ext2) init_inf_st = (Success ienv2, inf_st2) /\
  ienv_res = extend_dec_ienv ienv2 init_ienv
Proof
  Induct
  \\ rw [add_print_from_opts_def]
  >- (
    drule_then drule add_err_message_infer
    \\ rw [] \\ simp []
  )
  \\ every_case_tac
  >- (
    gvs []
    \\ simp [infer_ds_append]
    \\ simp [extend_dec_ienv_def]
  )
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ drule_then drule add_err_message_infer
    \\ rw []
    \\ first_x_assum (drule_then drule)
    \\ simp []
  )
QED

Theorem add_prints_from_opts_infer[local]:
  !opts decs_ext ienv inf_st decs_ext2 st2 ienv_res inf_st2.
  add_prints_from_opts opts
    (decs_ext, (extend_dec_ienv ienv init_ienv, inf_st)) =
    (decs_ext2, st2) /\
  infer_ds init_ienv (REVERSE decs_ext) init_inf_st = (Success ienv, inf_st) ==>
  ?ienv_res inf_st2 ienv2.
  st2 = (ienv_res, inf_st2) /\
  infer_ds init_ienv (REVERSE decs_ext2) init_inf_st = (Success ienv2, inf_st2) /\
  ienv_res = extend_dec_ienv ienv2 init_ienv
Proof
  Induct \\ simp [pairTheory.FORALL_PROD, add_prints_from_opts_def] \\ rw [] \\ simp []
  \\ qmatch_asmsub_abbrev_tac `add_prints_from_opts _ tup`
  \\ Cases_on `tup`
  \\ gvs [markerTheory.Abbrev_def, Q.ISPEC `(_, _)` EQ_SYM_EQ]
  \\ drule_then drule add_print_from_opts_infer
  \\ rw []
  \\ first_x_assum (drule_then drule)
  \\ rw []
  \\ simp []
QED

Theorem extend_none[local]:
  extend_dec_ienv <|inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty|> ienv = ienv
Proof
  simp [extend_dec_ienv_def, inf_env_component_equality]
QED

Theorem add_err_message_infer2[local] = add_err_message_infer
    |> Q.GENL [`decs_ext`, `ienv`, `inf_st`] |> Q.SPEC `[]`
    |> SIMP_RULE (srw_ss ()) [infer_d_def, st_ex_return_def, extend_none]

Theorem add_prints_from_opts_infer2[local] =
    Q.SPECL [`xs`, `[]`] add_prints_from_opts_infer
    |> SIMP_RULE (srw_ss ()) [infer_d_def, st_ex_return_def, extend_none]

Theorem add_print_features_succ:
  add_print_features st decs = (infer$Success (decs2, st2)) ==>
  ?tn ienv next_id tn2 ienv2 inf_st2.
  st = (tn, ienv, next_id) /\ st2 = (tn2, extend_dec_ienv ienv2 ienv, inf_st2) /\
  infer_ds ienv decs2 (init_infer_state <| next_id := next_id |>) = (Success ienv2, inf_st2)
Proof
  fs [add_print_features_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [pairTheory.pair_case_eq, exc_case_eq]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ (drule add_prints_from_opts_infer2 ORELSE drule add_err_message_infer2)
  \\ rw []
  \\ simp [infer_ds_append]
  \\ simp [extend_dec_ienv_def]
QED

Theorem add_print_then_read_succ:
  add_print_then_read st decs = (infer$Success (decs2, st2)) ==>
  ?tn ienv next_id tn2 ienv2 inf_st2.
  st = (tn, ienv, next_id) /\ st2 = (tn2, extend_dec_ienv ienv2 ienv, inf_st2.next_id) /\
  infer_ds ienv decs2 (init_infer_state <| next_id := next_id |>) = (Success ienv2, inf_st2)
Proof
  fs [add_print_then_read_def,AllCaseEqs()]
  \\ rw []
  \\ drule add_print_features_succ
  \\ strip_tac
  \\ gvs []
  \\ simp [infer_ds_append]
  \\ simp [extend_dec_ienv_def]
QED

(* preservation of inference invariants will be needed in translation *)
Theorem print_features_infer_st_invs:
  (! env ds st x st2. infer_ds env ds st = (Success x, st2) /\ P st ==> P st2) ==>
  (! s ds env inf_st x y.
    printTweaks$add_err_message s ds (env, inf_st) = (x, y) /\ P inf_st ==>
        P (SND y))
  /\
  (! opts nm ds env inf_st x y.
  printTweaks$add_print_from_opts nm opts (ds, (env, inf_st)) = (x, y) /\ P inf_st ==>
    P (SND y))
  /\
  (! xs ds env inf_st x y.
  printTweaks$add_prints_from_opts xs (ds, (env, inf_st)) = (x, y) /\ P inf_st ==>
    P (SND y))
  /\
  (! st ds x. printTweaks$add_print_features st ds = Success x /\
    P (init_infer_state <| next_id := SND (SND st) |>) ==> P (SND (SND (SND x)))
  )
Proof
  disch_tac
  \\ rpt conj_asm1_tac
  >- (
    rw [add_err_message_def]
    \\ every_case_tac
    \\ gvs []
    \\ res_tac
  )
  >- (
    Induct
    \\ simp [pairTheory.FORALL_PROD, add_print_from_opts_def]
    \\ rw [exc_case_eq, pairTheory.pair_case_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ TRY (qmatch_asmsub_abbrev_tac `add_print_from_opts _ _ (_, tup) = _`
      \\ Cases_on `tup`)
    \\ res_tac \\ fs []
  )
  >- (
    Induct
    \\ simp [pairTheory.FORALL_PROD, add_prints_from_opts_def]
    \\ rw [exc_case_eq, pairTheory.pair_case_eq]
    \\ qmatch_asmsub_abbrev_tac `add_prints_from_opts _ tup`
    \\ PairCases_on `tup`
    \\ gvs [markerTheory.Abbrev_def, Q.ISPEC `(_, _)` EQ_SYM_EQ]
    \\ res_tac \\ fs []
  )
  >- (
    simp [pairTheory.FORALL_PROD, add_print_features_def]
    \\ rw [exc_case_eq, pairTheory.pair_case_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs []
    \\ res_tac
    \\ fs []
  )
QED

