(*
  Proofs for MonitorProg
*)

open preamble ml_progLib ml_translatorLib
     basisFunctionsLib
     cfTacticsLib cfLetAutoLib
     intervalArithTheory MonitorProgTheory botFFITheory
     Word8ArrayProofTheory
open cfHeapsBaseTheory blastLib ml_translatorTheory;

val _ = new_theory"MonitorProof";

(*"*)
(*
  We first give a functional spec of the sandbox, which we refine
  to a transition specified by the sandbox
*)

(*
  A step of the loop body can have 2 error cases and 1 success case
*)

val _ = Datatype`
  status = Success | PlantViol | DefViol `

(* prevent automatic rewrite *)
val hide_def = Define`
  hide f p r <=> if f then p else r`

val hideF = Q.prove(`
  hide F p r = r`, fs[hide_def])

val body_step_def = Define`
  body_step flg w w' <=>
  ∃ctrlplus_ls conf.
  LENGTH ctrlplus_ls = LENGTH w.wc.ctrlplus_names ∧
  let wi = w with wo := w.wo with ctrl_oracle := (λn. w.wo.ctrl_oracle (n+1)) in
  let ctrl =
     (ctrl_monitor w.wc.ctrl_monitor
     w.wc.const_names w.wc.ctrl_names w.wc.sensor_names w.wc.ctrlplus_names
     w.ws.const_vals w.ws.ctrl_vals w.ws.sensor_vals ctrlplus_ls
     w.wc.ctrlfixed_names w.wc.ctrlfixed_rhs w.wc.default) in
  case ctrl of SOME (_,ctrl) =>
    let plant =
       (plant_monitor w.wc.plant_monitor
       w.wc.const_names w.wc.sensor_names w.wc.ctrl_names w.wc.sensorplus_names
       w.ws.const_vals w.ws.sensor_vals ctrl w'.ws.sensor_vals) in
    (* Plant either succeeds or fails *)
    (hide plant (flg = Success) (flg = PlantViol)) ∧
    (* If control monitor succeeded, sandbox definitely actuates *)
    ffi_actuate conf (w32_to_w8 ctrl) wi = SOME (FFIreturn (w32_to_w8 ctrl) w')
  (* No actuation happens if a default violation is reported *)
  | _ => (flg = DefViol ∧ w' = wi)`

(* The sandbox body *)
val body_sandbox_def = Define`
  body_sandbox flg wc =
   Seq (AssignAnyPar wc.ctrlplus_names)
  (Seq (AssignVarPar wc.ctrlfixed_names wc.ctrlfixed_rhs)
  (Seq (Choice (Test wc.ctrl_monitor) (AssignPar wc.ctrlplus_names wc.default))
  (hide (flg = DefViol) Skip
    (Seq (AssignVarPar wc.ctrl_names wc.ctrlplus_names)
    (
      Seq (AssignAnyPar wc.sensorplus_names)
      (hide (flg = Success)
        (Seq (Test wc.plant_monitor)
             (AssignVarPar wc.sensor_names wc.sensorplus_names))
        Skip)
    )))))`

(*
  The state relation between an FFI state and a HP state
  - maps point FFI state to a point interval
*)
val state_rel_def = Define`
  state_rel w (hp_w:cwstate) ⇔
  let names = w.wc.sensor_names ++  w.wc.ctrl_names ++ w.wc.const_names in
  let vals  = w.ws.sensor_vals  ++  w.ws.ctrl_vals  ++ w.ws.const_vals  in
  let ffi_st = ZIP(names, ZIP(vals,vals)) in
    ∀x.
    MEM x names ⇒
    ALOOKUP ffi_st x = ALOOKUP hp_w x`

(*
  These are syntactic well-formedness condition on mach_config

*)
val wf_config_def = Define`
  wf_config wc ⇔
  (* Length sanity checks *)
  LENGTH wc.sensor_names = LENGTH wc.sensorplus_names ∧
  LENGTH wc.ctrl_names = LENGTH wc.ctrlplus_names ∧
  LENGTH wc.ctrl_names = LENGTH wc.default ∧
  LENGTH wc.ctrlfixed_names = LENGTH wc.ctrlfixed_rhs ∧
  (* Variable sets in each group must be distinct *)
  ALL_DISTINCT wc.const_names ∧
  ALL_DISTINCT wc.ctrl_names ∧
  ALL_DISTINCT wc.ctrlplus_names ∧
  ALL_DISTINCT wc.sensor_names ∧
  ALL_DISTINCT wc.sensorplus_names ∧
  ALL_DISTINCT wc.ctrlfixed_names ∧
  (* We never overwrite the constants *)
  no_overlap wc.const_names
    (wc.sensor_names ++ wc.sensorplus_names ++ wc.ctrl_names ++ wc.ctrlplus_names ++
     wc.ctrlfixed_names) ∧
  (* Parallel assignments cannot have overlaps *)
  no_overlap wc.ctrlfixed_names wc.ctrlfixed_rhs ∧
  no_overlap wc.ctrl_names (wc.sensorplus_names ++ wc.ctrlplus_names ++ wc.ctrlfixed_names) ∧
  no_overlap wc.sensor_names (wc.sensorplus_names ++ wc.ctrlplus_names ++ wc.ctrlfixed_names) ∧
  no_overlap wc.ctrlplus_names wc.ctrlfixed_names ∧
    (* The allowed variable dependencies *)
  let full_deps = wc.const_names ++ wc.ctrl_names ++ wc.sensor_names in
    EVERY (λx. MEM x full_deps) (FLAT (MAP fv_trm wc.default)) ∧
    EVERY (λx. MEM x full_deps) (fv_fml wc.init) ∧
    EVERY (λx. MEM x full_deps) wc.ctrlfixed_rhs ∧
  let plant_deps = wc.const_names ++ wc.sensor_names ++ wc.ctrl_names ++ wc.sensorplus_names in
    EVERY (λx. MEM x plant_deps) (fv_fml wc.plant_monitor) ∧
  let ctrl_deps = wc.const_names ++ wc.ctrl_names ++ wc.sensor_names ++ wc.ctrlplus_names ++ wc.ctrlfixed_names in
    EVERY (λx. MEM x ctrl_deps) (fv_fml wc.ctrl_monitor)`

(* Well-formed machs obey their config's lengths *)
val wf_mach_def = Define`
  wf_mach w ⇔
  let constlen = LENGTH w.wc.const_names in
  let sensorlen = LENGTH w.wc.sensor_names in
  let ctrllen = LENGTH w.wc.ctrl_names in
  LENGTH w.ws.const_vals = constlen ∧
  LENGTH w.ws.ctrl_vals = ctrllen ∧
  LENGTH w.ws.sensor_vals = sensorlen ∧
  (∀n inp.
    (*LENGTH inp = clen + slen ⇒ -- we could restrict it more... *)
    LENGTH (w.wo.ctrl_oracle n inp) = ctrllen) ∧
  (∀n inp.
    (* See above on the length restriction *)
    LENGTH (w.wo.transition_oracle n inp) = sensorlen)`

val MAP_ZIP2 = Q.prove(`
  LENGTH xs = LENGTH ys ⇒
  MAP (λ(x,t). (x,f t)) (ZIP (xs,ys)) =
  ZIP (xs, MAP f ys)`,
  fs[LIST_EQ_REWRITE] >>rw[EL_MAP,EL_ZIP]);

val ZIP_ID = Q.prove(`
  ZIP(ls,ls) = MAP (λx. x,x) ls`,
  fs[LIST_EQ_REWRITE,EL_ZIP,EL_MAP]);

val MEM_ALOOKUP_APPEND = Q.prove(`
  MEM x (MAP FST ls) ⇒
  ALOOKUP (ls++xs) x = ALOOKUP (ls++ys) x`,
  rw[ALOOKUP_APPEND]>>
  TOP_CASE_TAC>>fs[ALOOKUP_NONE]);

val MEM_ALOOKUP_APPEND_REV = Q.prove(`
  ALL_DISTINCT (MAP FST ls) ∧
  MEM x (MAP FST ls) ⇒
  ALOOKUP (ls++xs) x = ALOOKUP (REVERSE ls++ys) x`,
  rw[ALOOKUP_APPEND]>>
  TOP_CASE_TAC>>fs[ALOOKUP_NONE]>>
  simp[alookup_distinct_reverse]);

val NOT_MEM_ALOOKUP_APPEND = Q.prove(`
  ¬MEM x (MAP FST ls) ⇒
  ALOOKUP (ls++xs) x = ALOOKUP xs x`,
  rw[ALOOKUP_APPEND]>>
  TOP_CASE_TAC>>fs[]>>
  imp_res_tac ALOOKUP_MEM>>fs[MEM_MAP,FORALL_PROD]>>
  metis_tac[]);

val APPEND_ASSOC4 = Q.prove(`
  (a ++ b ++ c ++ d):'a list =
  (a++b) ++ (c++d)`,
  fs[]);

val no_overlap_APPEND = Q.prove(`
  no_overlap ls (xs++ys) ⇔
  no_overlap ls xs ∧ no_overlap ls ys`,
  fs[no_overlap_thm]>>
  metis_tac[]);

val state_rel_lookup_const = Q.prove(`
  wf_config w.wc ∧
  wf_mach w /\
  MEM x w.wc.const_names ∧
  state_rel w st ⇒
  ALOOKUP st x =
  ALOOKUP
  (ZIP (w.wc.const_names,MAP (λx. (x,x)) w.ws.const_vals)) x`,
  rw[]>>fs[state_rel_def,wf_config_def,wf_mach_def]>>
  pop_assum(qspec_then`x` assume_tac)>>
  rfs[]>>
  pop_assum sym_sub_tac>>
  simp[GSYM ZIP_APPEND]>>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
  fs[ZIP_ID,MAP_ZIP,no_overlap_thm]);

val state_rel_lookup_sensor = Q.prove(`
  wf_config w.wc ∧
  wf_mach w /\
  MEM x w.wc.sensor_names ∧
  state_rel w st ⇒
  ALOOKUP st x =
  ALOOKUP
  (ZIP (w.wc.sensor_names,MAP (λx. (x,x)) w.ws.sensor_vals)++rest) x`,
  rw[]>>fs[state_rel_def,wf_config_def,wf_mach_def]>>
  pop_assum(qspec_then`x` assume_tac)>>
  rfs[]>>
  pop_assum sym_sub_tac>>
  simp[GSYM ZIP_APPEND,ZIP_ID]>>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
  match_mp_tac MEM_ALOOKUP_APPEND>>
  fs[MAP_ZIP]);

val state_rel_lookup_full = Q.prove(`
  wf_config w.wc ∧
  wf_mach w /\
  (MEM x w.wc.const_names ∨ MEM x w.wc.ctrl_names ∨ MEM x w.wc.sensor_names) ∧
  state_rel w st ⇒
  ALOOKUP st x =
  ALOOKUP
  (ZIP (w.wc.sensor_names,MAP (λx. (x,x)) w.ws.sensor_vals) ++
   ZIP (w.wc.ctrl_names,MAP (λx. (x,x)) w.ws.ctrl_vals) ++
   ZIP (w.wc.const_names,MAP (λx. (x,x)) w.ws.const_vals)) x`,
  rw[]>>fs[state_rel_def,wf_config_def,wf_mach_def]>>
  pop_assum(qspec_then`x` assume_tac)>>
  rfs[]>>
  pop_assum sym_sub_tac>>
  simp[GSYM ZIP_APPEND,ZIP_ID]>>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
  match_mp_tac MEM_ALOOKUP_APPEND>>
  fs[MAP_ZIP]);

val state_rel_lookup_const2 = Q.prove(`
  wf_config w.wc ∧
  wf_mach w /\
  MEM x w.wc.const_names ∧
  state_rel w st ⇒
  ∃v. ALOOKUP st x = SOME (v,v) ∧
  ALOOKUP
  (ZIP (w.wc.sensor_names, w.ws.sensor_vals) ++
   ZIP (w.wc.ctrl_names, w.ws.ctrl_vals) ++
   ZIP (w.wc.const_names,w.ws.const_vals)) x = SOME v`,
  rw[]>>fs[state_rel_def,wf_config_def,wf_mach_def]>>
  pop_assum(qspec_then`x` assume_tac)>>
  rfs[]>>
  pop_assum sym_sub_tac>>
  simp[GSYM ZIP_APPEND,ZIP_ID]>>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
  CONJ_TAC>-
    (fs[MAP_ZIP,no_overlap_thm]>>
    metis_tac[EL_MEM])>>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
  CONJ_TAC>-
    (fs[MAP_ZIP,no_overlap_thm]>>
    metis_tac[EL_MEM])>>
  fs[ALOOKUP_ZIP_MAP_SND]>>
  simp[ALOOKUP_EXISTS_IFF,MEM_ZIP]>>
  metis_tac[MEM_EL]);

val state_rel_lookup_sensor2 = Q.prove(`
  wf_config w.wc ∧
  wf_mach w /\
  MEM x w.wc.sensor_names ∧
  state_rel w st ⇒
  ∃v. ALOOKUP st x = SOME (v,v) ∧
  ALOOKUP
  (ZIP (w.wc.sensor_names, w.ws.sensor_vals) ++
   ZIP (w.wc.ctrl_names, w.ws.ctrl_vals) ++
   ZIP (w.wc.const_names,w.ws.const_vals)) x = SOME v`,
  rw[]>>fs[state_rel_def,wf_config_def,wf_mach_def]>>
  pop_assum(qspec_then`x` assume_tac)>>
  rfs[]>>
  pop_assum sym_sub_tac>>
  simp[ZIP_ID]>>
  PURE_REWRITE_TAC [GSYM MAP_APPEND]>>
  simp[ALOOKUP_ZIP_MAP_SND]>>
  simp[GSYM ZIP_APPEND]>>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.SPEC `[]` (GEN_ALL MEM_ALOOKUP_APPEND)]>>
  simp[MAP_ZIP]>>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.SPEC `[]` (GEN_ALL MEM_ALOOKUP_APPEND)]>>
  simp[MAP_ZIP]>>
  simp[ALOOKUP_EXISTS_IFF,MEM_ZIP]>>
  metis_tac[MEM_EL]);

val state_rel_lookup_ctrl2 = Q.prove(`
  wf_config w.wc ∧
  wf_mach w /\
  MEM x w.wc.ctrl_names ∧
  state_rel w st ⇒
  ∃v. ALOOKUP st x = SOME (v,v) ∧
  ALOOKUP
  (ZIP (w.wc.sensor_names, w.ws.sensor_vals) ++
   ZIP (w.wc.ctrl_names, w.ws.ctrl_vals) ++
   ZIP (w.wc.const_names,w.ws.const_vals)) x = SOME v`,
  rw[]>>fs[state_rel_def,wf_config_def,wf_mach_def]>>
  pop_assum(qspec_then`x` assume_tac)>>
  rfs[]>>
  pop_assum sym_sub_tac>>
  simp[ZIP_ID]>>
  PURE_REWRITE_TAC [GSYM MAP_APPEND]>>
  simp[ALOOKUP_ZIP_MAP_SND]>>
  simp[GSYM ZIP_APPEND]>>
  simp[ALOOKUP_EXISTS_IFF,MEM_ZIP]>>
  metis_tac[MEM_EL]);

val MAP_lookup_var = Q.prove(`
  ALL_DISTINCT vars ∧ LENGTH vars = LENGTH vals ⇒
  MAP (lookup_var (REVERSE (ZIP(vars,vals)) ++ rest)) vars = vals`,
  rw[]>>
  fs[LIST_EQ_REWRITE]>>
  simp[EL_MAP,lookup_var_def]>>
  rw[]>>
  simp[ALOOKUP_APPEND]>>
  dep_rewrite.DEP_REWRITE_TAC [alookup_distinct_reverse]>>
  simp[MAP_ZIP]>>
  Q.ISPECL_THEN [`ZIP(vars,vals)`,`x`] assume_tac ALOOKUP_ALL_DISTINCT_EL>>
  rfs[MAP_ZIP,EL_ZIP]);

val is_point_MAP_cancel = Q.prove(`
  EVERY is_point ls ⇒
  MAP (λx. (x,x))
    (MAP FST ls) = ls`,
  rw[]>>simp[MAP_EQ_ID,MAP_MAP_o]>>fs[EVERY_MEM,is_point_def]>>
  metis_tac[FST,SND,PAIR]);

val ALOOKUP_REV_SAME_SKIP = Q.prove(`
  ALL_DISTINCT (MAP FST xs) ∧
  (¬MEM x (MAP FST xs) ⇒ ALOOKUP ls x = ALOOKUP rs x)
  ⇒
  ALOOKUP (REVERSE xs ++ ls) x = ALOOKUP (xs ++ rs) x`,
  rw[ALOOKUP_APPEND]>>
  simp[alookup_distinct_reverse]>>
  TOP_CASE_TAC>>fs[]>>
  first_x_assum match_mp_tac>>
  metis_tac[ALOOKUP_NONE]);

val w8_to_w32_w32_to_w8 = Q.store_thm("w8_to_w32_w32_to_w8",`
  ∀l. w8_to_w32 (w32_to_w8 l) = l`,
  Induct>>EVAL_TAC>>
  pop_assum mp_tac>>EVAL_TAC>>rw[]>>
  blastLib.FULL_BBLAST_TAC);

(* Relate body step to transitions of a particular HP *)
val body_step_state_rel = Q.store_thm("body_step_state_rel",`
  wf_config w.wc ∧
  wf_mach w ∧
  state_rel w st ∧
  body_step flg w w' ⇒
  ∃st'.
  hide (flg = Success) (state_rel w' st') T ∧
  cwpsem (body_sandbox flg w.wc) st st'`,
  rw[body_step_def,body_sandbox_def]>>
  fs[wf_config_def]>>
  simp[Once cwpsem_cases]>>
  simp[AssignAnyPar_sem]>>
  simp[PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["ws"]))>>
  qexists_tac`MAP (λx. (x,x)) ctrlplus_ls`>>
  simp[EVERY_MAP]>>
  simp[Once cwpsem_cases]>>
  qmatch_goalsub_abbrev_tac`cwpsem _ st1 _`>>
  simp[PULL_EXISTS]>>
  simp[AssignVarPar_sem]>>
  simp[Once cwpsem_cases]>>
  simp[Once cwpsem_cases]>>
  simp[PULL_EXISTS]>>
  simp[METIS_PROVE [] ``(A ∧ B ∧ (C ∨ D) ∧ E) ⇔ (A ∧ B ∧ C ∧ E) ∨ (A ∧ B ∧ D ∧ E)``]>>
  simp[EXISTS_OR_THM]>>
  qpat_x_assum`case _ of NONE =>_ | SOME _ => _` mp_tac>>
  full_case_tac>>simp[]
  >-
    (* default violation*)
    (strip_tac>>
    DISJ2_TAC>>simp[hide_def]>>
    fs[no_overlap_APPEND]>>
    `no_overlap w.wc.ctrlplus_names (FLAT (MAP fv_trm w.wc.default))` by
      (fs[no_overlap_thm,MEM_FLAT,MEM_MAP,EVERY_MEM]>>
      metis_tac[])>>
    rw[]>>
    simp[AssignPar_sem]>>
    simp[Skip_sem]>>
    fs[EVERY_MEM]>>rw[]>>
    fs[WORD_LESS_EQ_REFL])>>
  full_case_tac>>simp[]>>
  strip_tac>>
  `flg ≠ DefViol` by
    (fs[hide_def]>>every_case_tac>>fs[])>>
    simp[hideF]>>
  qpat_x_assum`_ = SOME (q,r)` mp_tac>>
  simp[ctrl_monitor_def,cwfsem_bi_val_def]>>
  (* Now we case split on the control choice made by the sandbox *)
  reverse IF_CASES_TAC
  >- (
    (* Fallback to the defaults, which succeeded *)
    full_case_tac>>simp[]>>
    rw[]>>
    DISJ2_TAC>>
    fs[no_overlap_APPEND]>>
    `no_overlap w.wc.ctrlplus_names (FLAT (MAP fv_trm w.wc.default))` by
      (fs[no_overlap_thm,MEM_FLAT,MEM_MAP,EVERY_MEM]>>
      metis_tac[])>>
    simp[AssignPar_sem]>>
    simp[Once cwpsem_cases]>>
    simp[AssignVarPar_sem]>>
    simp[Once cwpsem_cases]>>
    simp[AssignAnyPar_sem,PULL_EXISTS]>>
    fs[ffi_actuate_def]>>
    rpt (pairarg_tac>>fs[])>>
    rw[]>>fs[]>>
    qmatch_goalsub_abbrev_tac`w.ws with sensor_vals := ls`>>
    CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["ws"]))>>
    qexists_tac`MAP (\x. (x,x)) ls`>>simp[]>>
    `LENGTH ls = LENGTH w.wc.sensorplus_names` by
      (fs[wf_mach_def,get_oracle_def,Abbr`ls`]>>
      rpt(pairarg_tac>>fs[])>>
      metis_tac[])>>
    simp[EVERY_MEM,EVERY_MAP,WORD_LESS_EQ_REFL]>>
    reverse (Cases_on`flg = Success`)>>
    simp[hide_def]
    >-
      (* plant monitor fails *)
      simp[Skip_sem]
    >>
    simp[Once cwpsem_cases]>>
    simp[Once cwpsem_cases]>>
    simp[AssignVarPar_sem]>>
    fs[w8_to_w32_w32_to_w8]>>
    (* The updated dL state *)
    qmatch_goalsub_abbrev_tac`sensors ++ sensorplus ++ ctrl ++ ctrlplus++ ctrlfixed ++ st1`>>
    fs[wf_mach_def,evaluate_default_def]>>
    `LENGTH w.wc.ctrl_names = LENGTH r` by
      rw[]>>
    simp[state_rel_def]>>
    fs[ctrl_monitor_def,cwfsem_bi_val_def]>>
    rfs[GSYM ZIP_APPEND]>>
    fs[ZIP_ID]>>
    qmatch_goalsub_abbrev_tac`sensors1 ++ ctrl1 ++ consts`>>
    `sensors = REVERSE sensors1` by
      (unabbrev_all_tac>>fs[]>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      dep_rewrite.DEP_REWRITE_TAC [MAP_lookup_var]>>
      fs[get_oracle_def])>>
    `ctrl = REVERSE ctrl1` by
      (rw[]>>unabbrev_all_tac>>simp[]>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      dep_rewrite.DEP_REWRITE_TAC [MAP_lookup_var]>>
      fs[]>>
      simp[is_point_MAP_cancel]>>
      ntac 2 AP_TERM_TAC>>
      simp[MAP_EQ_f]>>rw[]>>
      match_mp_tac fv_trm_coincide>>
      simp[EVERY_MEM]>>rw[]>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (rfs[MAP_APPEND,MAP_REVERSE,MAP_ZIP,no_overlap_thm]>>
        fs[EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_MAP]>>
        metis_tac[])>>
      simp[GSYM ZIP_APPEND]>>
      match_mp_tac state_rel_lookup_full>>
      fs[wf_config_def,no_overlap_thm,wf_mach_def]>>
      fs[EVERY_MEM,MEM_FLAT,MEM_MAP]>>
      metis_tac[])>>
    rw[]
    >- (
      (* sensors *)
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
    >- (
      (* ctrl *)
      match_mp_tac EQ_SYM>>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      simp[CONJ_ASSOC]>>
      CONJ_TAC>-
        (unabbrev_all_tac>>fs[MAP_ZIP,MAP_REVERSE]>>
        fs[wf_mach_def,wf_config_def,no_overlap_thm])>>
      rw[]>>
      match_mp_tac EQ_SYM>>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
    >- (
      (* constants unchanged *)
      simp[Abbr`st1`]>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (unabbrev_all_tac>>simp[MAP_ZIP]>>
        fs[wf_mach_def,wf_config_def,no_overlap_thm])>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (unabbrev_all_tac>>simp[MAP_ZIP,MAP_REVERSE]>>
        fs[wf_mach_def,wf_config_def,no_overlap_thm])>>
      fs[Abbr`consts`]>>match_mp_tac EQ_SYM>>
      match_mp_tac state_rel_lookup_const>>
      fs[wf_config_def,wf_mach_def,no_overlap_thm])
    >>
    fs[hide_def]>>
    qpat_x_assum`plant_monitor _ _ _ _ _ _ _ _ _` mp_tac>>
    simp[plant_monitor_def,cwfsem_bi_val_def]>>
    TOP_CASE_TAC>>rw[]>>
    pop_assum sym_sub_tac>>
    match_mp_tac fv_fml_coincide>>
    rfs[GSYM ZIP_APPEND,ZIP_ID]>>
    qmatch_goalsub_abbrev_tac`sensorplus1 ++ ctrl1 ++ sensors ++ consts`>>
    `sensorplus = REVERSE sensorplus1` by
      (unabbrev_all_tac>>fs[])>>
    match_mp_tac EVERY_MEM_MONO>>
    HINT_EXISTS_TAC>>fs[]>>
    rw[]
    >- (
      (* consts *)
      simp[Abbr`st1`]>>
      dep_rewrite.DEP_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (unabbrev_all_tac>>
        fs[MAP_REVERSE,MAP_ZIP]>>
        metis_tac[no_overlap_thm])>>
      simp[Abbr`consts`]>>
      match_mp_tac state_rel_lookup_const>>
      fs[wf_config_def,wf_mach_def,no_overlap_thm])
    >- (
      (* sensors *)
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      CONJ_TAC>-
        simp[Abbr`sensorplus1`,MAP_ZIP]>>
      strip_tac>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      CONJ_TAC>-
        (fs[Abbr`ctrl1`]>>
        simp[MAP_ZIP])>>
      strip_tac>>
      fs[Abbr`st1`]>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (unabbrev_all_tac>> fs[MAP_ZIP,no_overlap_thm,MAP_REVERSE])>>
      unabbrev_all_tac>>
      match_mp_tac state_rel_lookup_sensor>>
      fs[wf_config_def,wf_mach_def,no_overlap_thm])
    >- (
      (* ctrl*)
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      CONJ_TAC>- simp[Abbr`sensorplus1`,MAP_ZIP]>>
      strip_tac>>
      match_mp_tac EQ_SYM>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
    >>
      (* sensorplus *)
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
      match_mp_tac EQ_SYM>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
  >>
    (* Normal control *)
    rw[]>>DISJ1_TAC>>
    qpat_x_assum`case _ of NONE => F | SOME v => v` mp_tac>>
    full_case_tac>>simp[]>>rw[]>>
    fs[no_overlap_APPEND]>>
    simp[Once cwpsem_cases]>>
    simp[Once cwpsem_cases]>>
    simp[AssignVarPar_sem]>>
    simp[Once cwpsem_cases]>>
    simp[AssignAnyPar_sem,PULL_EXISTS]>>
    fs[ffi_actuate_def]>>
    rpt (pairarg_tac>>fs[])>>
    rw[]>>fs[]>>
    qmatch_goalsub_abbrev_tac`w.ws with sensor_vals := ls`>>
    CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["ws"]))>>
    qexists_tac`MAP (\x. (x,x)) ls`>>simp[]>>
    `LENGTH ls = LENGTH w.wc.sensorplus_names` by
      (fs[wf_mach_def,get_oracle_def,Abbr`ls`]>>
      rpt(pairarg_tac>>fs[])>>
      metis_tac[])>>
    simp[EVERY_MEM,EVERY_MAP,WORD_LESS_EQ_REFL]>>
    qmatch_goalsub_abbrev_tac`cwfsem w.wc.ctrl_monitor lss`>>
    `cwfsem w.wc.ctrl_monitor lss = SOME T` by (
      fs[Abbr`lss`,wf_mach_def]>>
      EVERY_CASE_TAC>>fs[]>>
      qpat_x_assum`_ = SOME T` (sym_sub_tac)>>
      match_mp_tac fv_fml_coincide>>
      fs[]>>
      match_mp_tac EVERY_MEM_MONO>>
      HINT_EXISTS_TAC>>fs[]>>
      simp[ZIP_ID]>>
      fs[evaluate_default_def,lookup_fixed_def]>>
      simp[GSYM ZIP_APPEND]>>
      qmatch_goalsub_abbrev_tac`ctrlfixed ++ ctrlplus ++ sensor ++ ctrl ++ const`>>
      qmatch_goalsub_abbrev_tac`ctrlfixed1 ++ st1`>>
      `ctrlfixed1 = REVERSE ctrlfixed` by
        (unabbrev_all_tac>>simp[]>>
        simp[MAP_ZIP,MAP_MAP_o,o_DEF]>>
        rpt(AP_TERM_TAC)>>
        simp[MAP_EQ_f]>>rw[]>>
        simp[lookup_var_def]>>
        dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
        simp[MAP_REVERSE,MAP_ZIP]>>
        CONJ_TAC>-
          (fs[EVERY_MEM,no_overlap_thm]>>
          metis_tac[])>>
        fs[EVERY_MEM]>>
        first_assum drule>> strip_tac
        >-
          (imp_res_tac state_rel_lookup_const2>>
          fs[AND_IMP_INTRO]>>
          pop_assum mp_tac>>impl_tac>-
            fs[wf_mach_def,wf_config_def,EVERY_MEM,no_overlap_thm]>>
          rw[]>>fs[])
        >-
          (imp_res_tac state_rel_lookup_ctrl2>>
          fs[AND_IMP_INTRO]>>
          pop_assum mp_tac>>impl_tac>-
            fs[wf_mach_def,wf_config_def,EVERY_MEM,no_overlap_thm]>>
          rw[]>>fs[])
        >>
        imp_res_tac state_rel_lookup_sensor2>>
        fs[AND_IMP_INTRO]>>
        pop_assum mp_tac>>impl_tac>-
          fs[wf_mach_def,wf_config_def,EVERY_MEM,no_overlap_thm]>>
        rw[]>>fs[])>>
      rw[Abbr`st1`]
      >- (
        (* consts *)
        dep_rewrite.DEP_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
        CONJ_TAC>-
          (unabbrev_all_tac>>
          fs[MAP_REVERSE,MAP_ZIP]>>
          metis_tac[no_overlap_thm])>>
        simp[Abbr`const`]>>
        match_mp_tac state_rel_lookup_const>>
        fs[wf_config_def,wf_mach_def,no_overlap_thm])
      >- (
        (* ctrls *)
        PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
        match_mp_tac ALOOKUP_REV_SAME_SKIP>>
        CONJ_TAC>-
          simp[Abbr`ctrlfixed`,MAP_ZIP]>>
        strip_tac>>
        match_mp_tac ALOOKUP_REV_SAME_SKIP>>
        CONJ_TAC>-
          (fs[Abbr`ctrlplus`]>>
          simp[MAP_ZIP])>>
        strip_tac>>
        unabbrev_all_tac>>
        simp[APPEND_ASSOC]>>
        match_mp_tac state_rel_lookup_full>>
        fs[wf_config_def,wf_mach_def,no_overlap_thm])
      >- (
        (* sensors *)
        PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
        match_mp_tac ALOOKUP_REV_SAME_SKIP>>
        CONJ_TAC>-
          simp[Abbr`ctrlfixed`,MAP_ZIP]>>
        strip_tac>>
        match_mp_tac ALOOKUP_REV_SAME_SKIP>>
        CONJ_TAC>-
          (fs[Abbr`ctrlplus`]>>
          simp[MAP_ZIP])>>
        strip_tac>>
        unabbrev_all_tac>>
        match_mp_tac state_rel_lookup_sensor>>
        fs[wf_config_def,wf_mach_def,no_overlap_thm,MAP_ZIP])
      >-(
        (* ctrlplus *)
        PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
        match_mp_tac ALOOKUP_REV_SAME_SKIP>>
        CONJ_TAC>- (unabbrev_all_tac>>fs[MAP_ZIP])>>
        strip_tac>>
        match_mp_tac EQ_SYM>>
        match_mp_tac MEM_ALOOKUP_APPEND_REV>>
        unabbrev_all_tac>>fs[MAP_ZIP])
      >>
        (* ctrlfixed *)
        PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
        match_mp_tac EQ_SYM>>
        match_mp_tac MEM_ALOOKUP_APPEND_REV>>
        unabbrev_all_tac>>fs[MAP_ZIP])>>
    reverse (Cases_on`flg = Success`)>>
    simp[hide_def]
    >-
      (* plant monitor fails *)
      simp[Skip_sem]
    >>
    simp[Once cwpsem_cases]>>
    simp[Once cwpsem_cases]>>
    fs[no_overlap_APPEND]>>
    simp[AssignVarPar_sem]>>
    simp[state_rel_def]>>
    qmatch_goalsub_abbrev_tac`sensors ++ sensorplus ++ ctrl ++ ctrlfixed ++ st1`>>
    simp[ZIP_ID,w8_to_w32_w32_to_w8]>>
    fs[wf_mach_def,evaluate_default_def]>>
    rfs[GSYM ZIP_APPEND]>>
    qmatch_goalsub_abbrev_tac`sensors1 ++ ctrl1 ++ const`>>
    `sensors = REVERSE sensors1` by
      (unabbrev_all_tac>>fs[]>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      dep_rewrite.DEP_REWRITE_TAC [MAP_lookup_var]>>
      fs[get_oracle_def])>>
    `ctrl = REVERSE ctrl1` by
      (unabbrev_all_tac>>fs[]>>
      rpt(AP_TERM_TAC)>>
      rw[LIST_EQ_REWRITE,EL_MAP,lookup_var_def]>>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      simp[MAP_ZIP,MAP_REVERSE]>>
      CONJ_TAC>-
        (fs[no_overlap_thm]>>
        metis_tac[EL_MEM,MEM_EL])>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.SPEC `[]` (GEN_ALL MEM_ALOOKUP_APPEND)]>>
      simp[MAP_ZIP,MAP_REVERSE]>>
      CONJ_TAC>- metis_tac[EL_MEM]>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [alookup_distinct_reverse]>>
      fs[MAP_ZIP]>>
      qmatch_goalsub_abbrev_tac`ALOOKUP ls`>>
      Q.ISPECL_THEN [`ls`,`x`] assume_tac ALOOKUP_ALL_DISTINCT_EL>>
      rfs[Abbr`ls`,MAP_ZIP]>>
      rfs[EL_ZIP,EL_MAP])>>
    simp[]>>rw[]
    >-
      (* sensors *)
      (PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
    >- (* ctrl *)
      (PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac EQ_SYM>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      simp[CONJ_ASSOC]>>CONJ_TAC>-
        (unabbrev_all_tac>>fs[MAP_ZIP,MAP_REVERSE,no_overlap_thm])>>
      strip_tac>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac EQ_SYM>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
    >- (* consts *)
      (simp[Abbr`st1`]>>
      dep_rewrite.DEP_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (unabbrev_all_tac>>fs[MAP_ZIP,MAP_REVERSE,no_overlap_thm])>>
      match_mp_tac EQ_SYM>>unabbrev_all_tac>>
      match_mp_tac state_rel_lookup_const>>
      fs[wf_config_def,wf_mach_def,no_overlap_thm])
    >>
    fs[hide_def]>>
    qpat_x_assum`plant_monitor _ _ _ _ _ _ _ _ _` mp_tac>>
    simp[plant_monitor_def,cwfsem_bi_val_def]>>
    TOP_CASE_TAC>>rw[]>>
    pop_assum sym_sub_tac>>
    match_mp_tac fv_fml_coincide>>
    rfs[ZIP_ID]>>
    match_mp_tac EVERY_MEM_MONO>>
    HINT_EXISTS_TAC>>fs[]>>
    fs[wf_mach_def,evaluate_default_def]>>
    rfs[ctrl_monitor_def,cwfsem_bi_val_def]>>
    (* qpat_x_assum`case cwfsem _ _ of NONE => F | SOME v => v` mp_tac>>
    TOP_CASE_TAC>>simp[]>>
    strip_tac>> *)
    rfs[ZIP_ID,ZIP_APPEND]>>
    simp[GSYM ZIP_APPEND]>>
    rw[]
    >- (
      (* consts *)
      simp[Abbr`st1`]>>
      dep_rewrite.DEP_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      unabbrev_all_tac>>fs[MAP_ZIP,no_overlap_thm,MAP_REVERSE]>>
      match_mp_tac state_rel_lookup_const>>
      fs[wf_config_def,wf_mach_def,no_overlap_thm])
    >- (
      (* sensors *)
      simp[Abbr`sensorplus`]>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      CONJ_TAC>-
        simp[MAP_ZIP]>>
      strip_tac>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      CONJ_TAC>-
        (fs[Abbr`ctrl1`]>>
        simp[MAP_ZIP])>>
      strip_tac>>
      fs[Abbr`st1`,Abbr`lss`]>>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>
      CONJ_TAC>-
        (unabbrev_all_tac>> fs[MAP_ZIP,no_overlap_thm,MAP_REVERSE])>>
      unabbrev_all_tac>>
      match_mp_tac state_rel_lookup_sensor>>
      fs[wf_config_def,wf_mach_def,no_overlap_thm])
    >- (
      (* ctrl*)
      simp[Abbr`sensorplus`]>>
      PURE_REWRITE_TAC [GSYM APPEND_ASSOC]>>
      match_mp_tac ALOOKUP_REV_SAME_SKIP>>
      CONJ_TAC>- simp[MAP_ZIP]>>
      strip_tac>>
      match_mp_tac EQ_SYM>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP])
    >>
      simp[Abbr`sensorplus`]>>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
      match_mp_tac EQ_SYM>>
      match_mp_tac MEM_ALOOKUP_APPEND_REV>>
      unabbrev_all_tac>>fs[MAP_ZIP]);

val body_loop_def = Define`
  body_loop = (body_step Success)^*`

(* The first refinement : prove that the RTC of body_step corresponds
   to a the sandbox control loop
*)
val body_loop_state_rel = Q.store_thm("body_loop_state_rel",`
  ∀w w'.
  body_loop w w' ⇒
  ∀st.
  wf_config w.wc ∧
  wf_mach w ∧
  state_rel w st ⇒
  ∃st'.
  state_rel w' st' ∧
  cwpsem (Loop (body_sandbox Success w.wc)) st st'`,
  simp[body_loop_def]>>
  ho_match_mp_tac RTC_INDUCT>>
  rw[]
  >-
    (qexists_tac`st`>>simp[Once cwpsem_cases])
  >>
  drule (GEN_ALL body_step_state_rel)>>fs[]>>
  disch_then drule>>
  disch_then drule>>
  rw[hide_def]>>
  simp[Once cwpsem_cases]>>
  simp[METIS_PROVE [] ``(A ∧ (C ∨ D)) ⇔ (A ∧ C) ∨ (A ∧ D)``,EXISTS_OR_THM]>>
  DISJ2_TAC>>
  simp[PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["u"]))>>
  qexists_tac`st'`>>simp[]>>
  fs[body_step_def,ffi_actuate_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  fs[]>>
  first_x_assum match_mp_tac>>
  fs[state_rel_def,wf_mach_def,get_oracle_def,w8_to_w32_w32_to_w8,LENGTH_w32_to_w8]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  metis_tac[]);

val init_sandbox_def = Define`
  init_sandbox wc =
   Seq (AssignAnyPar wc.const_names)
  (Seq (AssignAnyPar wc.ctrl_names)
  (Seq (AssignAnyPar wc.sensor_names)
       (Test (wc.init))))`

val mk_state_def = Define`
  mk_state w =
  let names_ls = w.wc.sensor_names ++ w.wc.ctrl_names ++ w.wc.const_names in
  let st_ls = w.ws.sensor_vals ++ w.ws.ctrl_vals ++ w.ws.const_vals in
 (ZIP(names_ls,ZIP(st_ls,st_ls)))`

(* The initial world satisfies init *)
val init_step_def = Define`
  init_step w = cwfsem_bi_val w.wc.init (mk_state w)`

val ALL_DISTINCT_ALOOKUP_REV = Q.prove(`
  ALL_DISTINCT (MAP FST ls) ∧
  ALOOKUP xs x = ALOOKUP ys x ⇒
  ALOOKUP (ls++xs) x = ALOOKUP ((REVERSE ls)++ys) x`,
  rw[]>>
  Cases_on`MEM x (MAP FST ls)`
  >-
    metis_tac[MEM_ALOOKUP_APPEND_REV]
  >>
  dep_rewrite.DEP_REWRITE_TAC [NOT_MEM_ALOOKUP_APPEND]>>fs[MEM_MAP]);

val init_step_init_sandbox = Q.store_thm("init_step_init_sandbox",`
  wf_config w.wc ∧
  wf_mach w ∧
  state_rel w st ∧
  init_step w ⇒
  ∃st'.
  state_rel w st' ∧
  cwpsem (init_sandbox w.wc) st st'`,
  rw[init_step_def,init_sandbox_def,mk_state_def]>>
  fs[wf_config_def]>>
  simp[Once cwpsem_cases]>>
  simp[AssignAnyPar_sem,PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["ws"]))>>
  qexists_tac`MAP (λx. (x,x)) w.ws.const_vals` >>
  simp[Once cwpsem_cases]>>
  simp[AssignAnyPar_sem,PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["ws"]))>>
  qexists_tac`MAP (λx. (x,x)) w.ws.ctrl_vals` >>
  simp[EVERY_MAP,WORD_LESS_EQ_REFL]>>
  simp[Once cwpsem_cases]>>
  simp[AssignAnyPar_sem,PULL_EXISTS]>>
  CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["ws"]))>>
  qexists_tac`MAP (λx. (x,x)) w.ws.sensor_vals` >>
  simp[Once cwpsem_cases]>>
  rfs[wf_config_def,wf_mach_def]>>
  rw[]
  >- (
    simp[state_rel_def]>>
    simp[ZIP_ID,GSYM ZIP_APPEND]>>
    strip_tac>>
    qmatch_goalsub_abbrev_tac` P ⇒ _`>> strip_tac>>
    match_mp_tac EQ_SYM>>
    dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.SPEC `[]` (GEN_ALL MEM_ALOOKUP_APPEND)]>>
    simp[MAP_REVERSE,MAP_ZIP]>>
    match_mp_tac EQ_SYM>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    match_mp_tac ALL_DISTINCT_ALOOKUP_REV>>fs[MAP_ZIP]>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    match_mp_tac ALL_DISTINCT_ALOOKUP_REV>>fs[MAP_ZIP]>>
    match_mp_tac EQ_SYM>>
    match_mp_tac alookup_distinct_reverse>>
    fs[MAP_ZIP])
  >-
    simp[EVERY_MAP,WORD_LESS_EQ_REFL]
  >>
    fs[cwfsem_bi_val_def]>>EVERY_CASE_TAC>>fs[]>>
    qpat_x_assum `_=SOME T` sym_sub_tac>>
    match_mp_tac fv_fml_coincide>>
    fs[EVERY_MEM]>>
    simp[ZIP_ID,GSYM ZIP_APPEND]>>
    rw[]>>
    dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.SPEC `[]` (GEN_ALL MEM_ALOOKUP_APPEND)]>>
    simp[MAP_REVERSE,MAP_ZIP]>>
    CONJ_TAC>-
      metis_tac[]>>
    match_mp_tac EQ_SYM>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    match_mp_tac ALL_DISTINCT_ALOOKUP_REV>>fs[MAP_ZIP]>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    match_mp_tac ALL_DISTINCT_ALOOKUP_REV>>fs[MAP_ZIP]>>
    match_mp_tac EQ_SYM>>
    match_mp_tac alookup_distinct_reverse>>
    fs[MAP_ZIP]);

(* Now, we prove the refinement from CakeML into the functional spec *)
val _ = translation_extends "MonitorProg";

(* We now prove specs for each function added in MonitorProg *)

val bot_st = get_ml_prog_state();
val _ = overload_on ("WORD32",``WORD:word32 -> v -> bool``);

(* Helper lemmas *)
val MAP4_empty = Q.prove(`
  LENGTH ls < 4 ⇒
  MAP4 f ls = []`,
  Cases_on`ls`>>fs[MAP4_def]>>
  Cases_on`t`>>fs[MAP4_def]>>
  Cases_on`t'`>>fs[MAP4_def]>>
  Cases_on`t`>>fs[MAP4_def]);

val w32_to_w8_APPEND = Q.store_thm("w32_to_w8_APPEND",`
  ∀a b. w32_to_w8 (a ++ b) = w32_to_w8 a ++ w32_to_w8 b`,
  EVAL_TAC>>
  Induct_on`a`>>fs[FLAT_TUP_def,w32_to_le_bytes_def]);

val pack_w32_list_spec = Q.store_thm("pack_w32_list_spec",`
    ∀l lv.
    LIST_TYPE WORD32 l lv
    ==>
    app (p:'ffi ffi_proj) ^(fetch_v "pack_w32_list" bot_st) [lv]
      emp (POSTv av.
      W8ARRAY av (w32_to_w8 l))`,
  xcf "pack_w32_list" bot_st>>
  xfun_spec `f`
   `∀ls lsv i iv l_pre rest ar.
     NUM i iv /\
     LENGTH l_pre = i ∧
     LENGTH rest = 4 * LENGTH ls ∧
     LIST_TYPE WORD32 ls lsv
     ==>
     app p f [ar; lsv; iv]
      (W8ARRAY ar (l_pre ++ rest))
      (POSTv ar.
      W8ARRAY ar (l_pre ++ (FLAT_TUP (MAP w32_to_le_bytes ls))))`
  >-
    (Induct
    >- (
      rw[LIST_TYPE_def] \\
      first_x_assum match_mp_tac \\
      xmatch \\
      xret \\
      xsimpl \\ simp[FLAT_TUP_def])
    >>
      rw[LIST_TYPE_def] \\
      fs[terminationTheory.v_to_list_def] \\
      last_x_assum match_mp_tac \\
      xmatch \\
      xlet_auto >- xsimpl >>
      fs[w32_to_le_bytes_def]>>
      fs[PAIR_TYPE_def]>>
      ntac 3 xmatch \\
      rpt( xlet_auto >- xsimpl )>>
      xapp >> xsimpl>>
      simp[FLAT_TUP_def]>>
      fs[LUPDATE_APPEND2]>>
      `LENGTH rest = 4 + (4 * LENGTH ls)` by fs[ADD1]>>
      fs[quantHeuristicsTheory.LIST_LENGTH_4]>>
      simp[LUPDATE_compute])
  >>
    rpt(xlet_auto>- xsimpl)>>
    xlet_auto>>
    xapp >> xsimpl>>
    metis_tac[w32_to_w8_def]);

val unpack_w32_list_spec = Q.store_thm("unpack_w32_list_spec",`
    ∀l lv.
    app (p:'ffi ffi_proj) ^(fetch_v "unpack_w32_list" bot_st) [av]
      (W8ARRAY av a)
      (POSTv lv.
      W8ARRAY av a *
      &LIST_TYPE WORD32 (w8_to_w32 a) lv)`,
  xcf "unpack_w32_list" bot_st>>
  xfun_spec `f`
   `∀i iv l lv a av.
     NUM i iv /\
     NUM l lv /\
     l = LENGTH a
     ==>
     app p f [av; iv; lv]
      (W8ARRAY av a)
      (POSTv lv.
      W8ARRAY av a *
      &LIST_TYPE WORD32 (w8_to_w32 (DROP i a)) lv)`
  >- (
    ntac 3 strip_tac>>
    qid_spec_tac`iv`>>
    completeInduct_on`l-i`>>
    rw[]>> first_x_assum match_mp_tac>>
    xlet_auto >- xsimpl>>
    xlet_auto >- xsimpl>>
    reverse xif
    >-
      (xcon>>xsimpl>>simp[w8_to_w32_def,MAP4_empty,LIST_TYPE_def])
    >>
    xlet_auto>- xsimpl>>
    first_x_assum(qspec_then `LENGTH a - (i+4)` mp_tac)>>
    simp[]>>
    disch_then(qspecl_then [`LENGTH a`,`i+4`] mp_tac)>>simp[]>>
    rpt (disch_then drule)>>
    disch_then(qspecl_then[`a`,`av'`] assume_tac)>>fs[]>>
    (* xlet_auto fails... *)
    xlet `POSTv lv. W8ARRAY av' a * &LIST_TYPE WORD32 (w8_to_w32 (DROP (i + 4) a)) lv`
    >- (xapp>>xsimpl)>>
    rpt(xlet_auto >- xsimpl)>>
    xcon>>xsimpl>>
    fs[DROP_EL_CONS,MAP4_def,LIST_TYPE_def,w8_to_w32_def])
  >>
    xlet_auto >- xsimpl>>
    xapp>> xsimpl);

(* We now specify each of the functions *)

val IOBOT_def = Define `
  IOBOT w = IOx bot_ffi_part w * &(wf_mach w)`

(* TODO: remove once STRING_TYPE is fixed *)
val _ = overload_on ("CLSTRING_TYPE",``LIST_TYPE CHAR``);

val const_spec = Q.store_thm("const_spec",`
  ∀w vs ls.
  LIST_TYPE CLSTRING_TYPE ls vs ∧
  LENGTH ls = LENGTH w.wc.const_names
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "const" bot_st) [vs]
    (IOBOT w)
    (POSTv lv.
    IOBOT w *
    &LIST_TYPE WORD32 w.ws.const_vals lv)`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf "const" bot_st>>
  rpt(xlet_auto>- xsimpl)>>
  xlet `POSTv u.
         IOx bot_ffi_part w *
         W8ARRAY v' (w32_to_w8 w.ws.const_vals)`
  >-
    (xffi>>xsimpl>>
    simp[IOx_def,bot_ffi_part_def,mk_ffi_next_def,IO_def]>>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    map_every qexists_tac [`&wf_mach w`,  `s`, `u`, `ns`,`events`] >>
    xsimpl >>
    unabbrev_all_tac>>
    fs[mk_ffi_next_def,ffi_const_def,wf_mach_def]>>
    xsimpl>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl
    )
  >>
  xapp>>xsimpl>>
  simp[w8_to_w32_w32_to_w8]);

val ctrl_spec = Q.store_thm("ctrl_spec",`
  ∀w vs ls.
  LIST_TYPE CLSTRING_TYPE ls vs ∧
  LENGTH ls = LENGTH w.wc.ctrl_names
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "ctrl" bot_st) [vs]
    (IOBOT w)
    (POSTv lv.
    IOBOT w *
    &LIST_TYPE WORD32 w.ws.ctrl_vals lv)`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf "ctrl" bot_st>>
  rpt(xlet_auto>- xsimpl)>>
  xlet `POSTv u.
         IOx bot_ffi_part w *
         W8ARRAY v' (w32_to_w8 w.ws.ctrl_vals)`
  >-
    (xffi>>xsimpl>>
    simp[IOx_def,bot_ffi_part_def,mk_ffi_next_def,IO_def]>>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    map_every qexists_tac [`&wf_mach w`,  `s`, `u`, `ns`,`events`] >>
    xsimpl >>
    unabbrev_all_tac>>
    fs[mk_ffi_next_def,ffi_ctrl_def,wf_mach_def]>>
    xsimpl>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl)
  >>
  xapp>>xsimpl>>
  simp[w8_to_w32_w32_to_w8]);

val sense_spec = Q.store_thm("sense_spec",`
  ∀w vs ls.
  LIST_TYPE CLSTRING_TYPE ls vs ∧
  LENGTH ls = LENGTH w.wc.sensor_names
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "sense" bot_st) [vs]
    (IOBOT w)
    (POSTv lv.
    IOBOT w *
    &LIST_TYPE WORD32 w.ws.sensor_vals lv)`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf "sense" bot_st>>
  rpt(xlet_auto>- xsimpl)>>
  xlet `POSTv u.
         IOx bot_ffi_part w *
         W8ARRAY v' (w32_to_w8 w.ws.sensor_vals)`
  >-
    (xffi>>xsimpl>>
    simp[IOx_def,bot_ffi_part_def,mk_ffi_next_def,IO_def]>>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    map_every qexists_tac [`&wf_mach w`,  `s`, `u`, `ns`,`events`] >>
    xsimpl >>
    unabbrev_all_tac>>
    fs[mk_ffi_next_def,ffi_sense_def,wf_mach_def]>>
    xsimpl>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl)
  >>
  xapp>>xsimpl>>
  simp[w8_to_w32_w32_to_w8]);

val to_string_spec = Q.store_thm("to_string_spec",`
  app (p:'ffi ffi_proj) ^(fetch_v "to_string" bot_st) [ar]
    (W8ARRAY ar av)
    (POSTv v.
    &(STRING_TYPE (strlit (MAP (CHR o w2n) av)) v) * W8ARRAY ar av)`,
  xcf "to_string" bot_st>>
  xlet_auto >- xsimpl>>
  xapp>>
  xsimpl>>
  qexists_tac`LENGTH av`>>
  simp[]);

val extCtrl_spec = Q.store_thm("extCtrl_spec",`
  ∀w vs constv sensorv ls.
  LIST_TYPE CLSTRING_TYPE ls vs ∧
  LENGTH ls = LENGTH w.wc.ctrl_names ∧
  LIST_TYPE WORD32 w.ws.const_vals constv ∧
  LIST_TYPE WORD32 w.ws.sensor_vals sensorv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "extCtrl" bot_st) [vs;constv;sensorv]
    (IOBOT w)
    (POSTv lv.
    IOBOT (w with
      wo := w.wo with ctrl_oracle := (λn. w.wo.ctrl_oracle (n + 1)))*
    SEP_EXISTS vv.
    & (LENGTH vv = LENGTH w.wc.ctrl_names ∧
      LIST_TYPE WORD32 vv lv))`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf "extCtrl" bot_st>>
  rpt(xlet_auto>- ((TRY xcon)>>xsimpl))>>
  qmatch_asmsub_abbrev_tac`STRING_TYPE confstr sv`>>
  xlet`
  (POSTv u.
   IOx bot_ffi_part (w with
      wo := w.wo with ctrl_oracle := (λn. w.wo.ctrl_oracle (n + 1))) *
   W8ARRAY av (w32_to_w8 (w.ws.const_vals ⧺ w.ws.sensor_vals)) *
   SEP_EXISTS vv.
    &(LENGTH vv = LENGTH w.wc.ctrl_names) *
    W8ARRAY v'' (w32_to_w8 vv))`
  >- (
    xffi>>xsimpl>>
    simp[IO_def,IOx_def,bot_ffi_part_def,mk_ffi_next_def]>>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    qexists_tac `w32_to_w8 w.ws.const_vals ++ w32_to_w8 w.ws.sensor_vals`>>
    qexists_tac`W8ARRAY av (w32_to_w8 (w.ws.const_vals ⧺ w.ws.sensor_vals))`>> xsimpl>>
    map_every qexists_tac[`s`,`u`,`ns`,`events`]>>
    xsimpl>>
    unabbrev_all_tac>>
    simp[mk_ffi_next_def,ffi_extCtrl_def,get_oracle_def]>>
    fs[mlstringTheory.concat_def,ml_translatorTheory.STRING_TYPE_def,
      LENGTH_w32_to_w8,wf_mach_def,w32_to_w8_APPEND]>>
    xsimpl>>
    qmatch_goalsub_abbrev_tac`w32_to_w8 xxx = _`>>
    qexists_tac`xxx`>>simp[Abbr`xxx`]>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl)
  >>
    xapp>>xsimpl>>
    rw[]>>
    fs[w8_to_w32_w32_to_w8,wf_mach_def]>>
    metis_tac[]);

val string_ID = Q.store_thm("string_ID",`
  ∀s. MAP (CHR ∘ (w2n:word8->num)) (MAP (n2w ∘ ORD) s) = s`,
  fs[LIST_EQ_REWRITE,EL_MAP]>>rw[]>>
  `ORD (EL x s) MOD 256 = ORD (EL x s)` by
    fs[MOD_LESS,ORD_BOUND]>>
  metis_tac[CHR_ORD]);

val actuate_spec = Q.store_thm("actuate_spec",`
  LIST_TYPE WORD32 ctrl_vals ctrlv ∧
  STRING_TYPE strng strngv ∧
  LENGTH ctrl_vals = LENGTH w.wc.ctrl_names ∧
  wf_config w.wc ∧
  ¬(w.wo.stop_oracle 0)
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "actuate" bot_st) [strngv;ctrlv]
   (IOBOT w )
   (POSTv uv. &(UNIT_TYPE () uv) *
   SEP_EXISTS w'. IOBOT w'  *
   (* we use the full characterization here *)
   &(∃ss. ffi_actuate ss (w32_to_w8 ctrl_vals) w = SOME(FFIreturn (w32_to_w8 ctrl_vals) w')))`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf"actuate" bot_st>>
  xlet_auto >- xsimpl>>
  xlet`POSTv uv. W8ARRAY av (w32_to_w8 ctrl_vals) *
     SEP_EXISTS w'.
       IOx bot_ffi_part w' * &(wf_mach w') *
       &(∃ss. ffi_actuate ss (w32_to_w8 ctrl_vals) w = SOME(FFIreturn (w32_to_w8 ctrl_vals) w'))`
  >-
    (xffi >> xsimpl>>
    simp[IO_def,IOx_def,bot_ffi_part_def,mk_ffi_next_def]>>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    qexists_tac `MAP (n2w o ORD) (explode strng)`>>
    Cases_on`strng`>>fs[ml_translatorTheory.STRING_TYPE_def,string_ID]>>
    CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["s''","u'","ns'","events'"]))>>
    map_every qexists_tac [`s`,`u`,`ns`,`events`]>>
    simp[Abbr`u`,Abbr`ns`,mk_ffi_next_def]>>
    xsimpl>>
    simp[Abbr`s`]>>
    fs[ffi_actuate_def]>>rw[]>>
    rpt (pairarg_tac>>fs[])>>
    fs[LENGTH_w32_to_w8,get_oracle_def,wf_mach_def,w8_to_w32_w32_to_w8]>>
    xsimpl>>
    simp[]>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl>>
    rw[])
  >>
  xcon>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  metis_tac[]);

val comp_eq = [mach_component_equality,
               mach_config_component_equality,
               mach_state_component_equality,
               mach_oracle_component_equality];

val stop_spec = Q.store_thm("stop_spec",`
    UNIT_TYPE u uv
    ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "stop" bot_st) [uv]
      (IOBOT w)
      (POSTv bv.
      IOBOT w *
      &BOOL (w.wo.stop_oracle 0) bv)`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf "stop" bot_st>>
  fs[ml_translatorTheory.UNIT_TYPE_def]>>
  xmatch>>
  rpt(xlet_auto >- xsimpl)>>
  xlet `POSTv u.
         IOBOT w *
         W8ARRAY v' (if w.wo.stop_oracle 0 then [1w:word8] else [0w])`
  >-
    (xffi>>xsimpl>>
    simp[IO_def,IOx_def,bot_ffi_part_def,mk_ffi_next_def]>>
    xsimpl >>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    map_every qexists_tac [`emp`, `s`, `u`, `ns`, `events`] >>
    unabbrev_all_tac>>
    xsimpl >>
    simp[mk_ffi_next_def,ffi_stop_def]>>
    rw[]>>
    simp[IOBOT_def,IOx_def,bot_ffi_part_def,IO_def]>>
    xsimpl>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl>>
    rw[])
  >>
  rpt(xlet_auto>- xsimpl)>>
  xlet_auto>-
    (xsimpl>>
    rw[])>>
  xapp_spec (mlbasicsProgTheory.neq_v_thm |> INST_TYPE [alpha |-> ``:word8``])>>
  xsimpl>>
  qexists_tac`0w`>>
  qmatch_asmsub_abbrev_tac`WORD8 b v'''`>>
  qexists_tac`b`>>
  qexists_tac`WORD8`>>simp[Abbr`b`]>>rw[]>>
  simp[ml_translatorTheory.EqualityType_NUM_BOOL]>>
  simp[IOBOT_def]>>xsimpl);

(* eventually on oracle sequences *)
val eventually_def = Define`
  eventually P oracle ⇔
  ∃n.
    P(oracle n)`

val violation_spec = Q.store_thm("violation_spec",`
  STRING_TYPE strng strngv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "violation" bot_st) [strngv]
    (IOBOT w)
    (POSTv uv. &(UNIT_TYPE () uv) * IOBOT w)`,
  rw [IOBOT_def] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [bot_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q` >>
  xcf"violation"bot_st>>
  rpt(xlet_auto >- xsimpl)>>
  xlet`POSTv u. IOBOT w * SEP_EXISTS v'. W8ARRAY v' []`
  >-
    (simp[IOBOT_def]>>
    xffi>>xsimpl>>
    simp[IO_def,IOx_def,bot_ffi_part_def,mk_ffi_next_def]>>
    qmatch_goalsub_abbrev_tac`FFI_part s u ns` >>
    qexists_tac `MAP (n2w o ORD) (explode strng)`>>
    map_every qexists_tac [`emp`, `s`, `u`, `ns`,`events`] >>
    unabbrev_all_tac>>
    xsimpl >>
    simp[mk_ffi_next_def,ffi_violation_def]>>
    xsimpl>>
    simp[string_ID]>>
    Cases_on`strng`>>fs[ml_translatorTheory.STRING_TYPE_def]>>
    qmatch_goalsub_abbrev_tac`events++new_events`>>
    qexists_tac`events++new_events`>> xsimpl>>
    qexists_tac`v'`>>xsimpl)
  >>
  xcon>>simp[IOBOT_def]>>xsimpl);

(* refine the sandbox loop to the RTC of body_step *)
val monitor_loop_body_spec = Q.store_thm("monitor_loop_body_spec",`
  ∀w const_valsv ctrl_valsv sensor_valsv.
    (* These specify what the inputs should be *)
    INTERVALARITH_FML_TYPE w.wc.plant_monitor plantfv ∧
    INTERVALARITH_FML_TYPE w.wc.ctrl_monitor ctrlfv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.const_names const_namesv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.sensor_names sensor_namesv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.ctrlplus_names ctrlplus_namesv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.ctrl_names ctrl_namesv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.sensorplus_names sensorplus_namesv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.ctrlfixed_names ctrlfixed_namesv ∧
    LIST_TYPE CLSTRING_TYPE w.wc.ctrlfixed_rhs ctrlfixed_rhsv ∧
    LIST_TYPE INTERVALARITH_TRM_TYPE w.wc.default defaultv ∧
    LIST_TYPE WORD32 w.ws.const_vals const_valsv ∧
    LIST_TYPE WORD32 w.ws.ctrl_vals ctrl_valsv ∧
    LIST_TYPE WORD32 w.ws.sensor_vals sensor_valsv ∧
    (* Well-formed configurations *)
    wf_config w.wc ∧
    (* eventually stop *)
    eventually I w.wo.stop_oracle
    ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "monitor_loop_body" bot_st)
      [plantfv;ctrlfv;
      const_namesv;sensor_namesv;ctrlplus_namesv;ctrl_namesv;sensorplus_namesv;
      ctrlfixed_namesv; ctrlfixed_rhsv; defaultv;
      const_valsv;ctrl_valsv;sensor_valsv]
    (IOBOT w)
    (POSTv uv.  &(UNIT_TYPE () uv) *
      SEP_EXISTS w'. IOBOT w' *
      &((* Either we step to the end, or we reach the first plant violation *)
         (w'.wo.stop_oracle 0 ∧
         body_loop w w')
         ∨
         ∃v. body_loop w v ∧ (body_step DefViol v w' ∨ body_step PlantViol v w'))
    )`,
  fs[eventually_def,PULL_EXISTS]>>
  completeInduct_on`n`>>rw[]>>
  xcf"monitor_loop_body" bot_st>>
  rpt(xlet_auto>- ((TRY xcon)>>xsimpl))>>
  drule stop_spec>> strip_tac>>
  xlet_auto>> simp[]>>
  xif
  >-
    (xcon>>xsimpl>>
    qexists_tac`w`>>simp[]>>
    xsimpl>>
    simp[body_loop_def])
  >>
  reverse (Cases_on`wf_mach w`) >- (simp[IOBOT_def]>>xpull)>>
  fs[wf_config_def]>>
  rpt(xlet_auto>- (xsimpl>>metis_tac[]))>>
  qmatch_asmsub_abbrev_tac`OPTION_TYPE _ fls _`>>
  Cases_on`fls`>>
  fs[std_preludeTheory.OPTION_TYPE_def,markerTheory.Abbrev_def]
  >-
    (xmatch>>
    xsimpl>>
    xapp>>xsimpl>>
    qmatch_goalsub_abbrev_tac`IOBOT w'`>>
    qexists_tac`GC`>>qexists_tac`w'`>>xsimpl>>
    rw[]>>qexists_tac`w'`>>xsimpl>>
    DISJ2_TAC >>
    qexists_tac`w`>>simp[body_step_def,body_loop_def,hide_def]>>
    DISJ1_TAC>>qexists_tac`vv`>>fs[]>>
    qpat_x_assum`NONE = _` (assume_tac o SYM)>>
    simp[])>>
  Cases_on`x`>>
  fs[ml_translatorTheory.PAIR_TYPE_def]>>
  xmatch>>
  qpat_x_assum`SOME (q,r) = _` (assume_tac o SYM)>>fs[]>>
  drule (GEN_ALL actuate_spec)>>simp[]>>
  rpt(disch_then drule)>>
  qmatch_goalsub_abbrev_tac`IOBOT w'`>>
  disch_then(qspecl_then[`w'`,`p`] mp_tac)>>
  impl_tac>-
    (fs[Abbr`w'`,wf_config_def]>>
    fs[ctrl_monitor_def]>>EVERY_CASE_TAC>>
    fs[evaluate_default_def]>>
    rw[]>>fs[])>>
  strip_tac>>
  xlet`POSTv uv'.
            &UNIT_TYPE () uv' *
            SEP_EXISTS w''.
              IOBOT w'' *
              &(∃ss.
                    ffi_actuate ss (w32_to_w8 r) w' =
                    SOME (FFIreturn (w32_to_w8 r) w''))`
  >-
    (xapp>>xsimpl>>
    rw[]>>
    fs[Abbr`w'`])>>
  fs[]>>
  `w''.wc = w.wc` by
    (fs[ffi_actuate_def]>>
    rpt(pairarg_tac>>fs[])>>
    rw[Abbr`w'`])>>
  rpt(xlet_auto>-
    ((TRY xcon)>>xsimpl))>>
  reverse xif
  >-(
    xapp>>xsimpl>>
    qexists_tac`GC`>>qexists_tac`w''`>>xsimpl>>
    rw[]>>qexists_tac`w''`>>xsimpl>>
    DISJ2_TAC >>
    qexists_tac`w`>>simp[body_step_def,body_loop_def,hide_def]>>
    DISJ2_TAC>>qexists_tac`vv`>>fs[]>>
    metis_tac[])>>
  last_x_assum(qspec_then`n-1` mp_tac)>>simp[]>>
  impl_tac>-
    (Cases_on`n`>>fs[])>>
  disch_then (qspec_then `w''` mp_tac)>> simp[]>>
  `w''.ws.const_vals = w.ws.const_vals ∧ w''.wo.stop_oracle (n-1)` by
    (fs[ffi_actuate_def]>>
    rpt(pairarg_tac>>fs[])>>rw[Abbr`w'`]>>
    fs[get_oracle_def]>>rw[]>>
    Cases_on`n`>>fs[ADD1])>>
  fs[]>>
  disch_then drule>>
  `w''.ws.ctrl_vals = r` by
    (fs[ffi_actuate_def]>>
    rpt(pairarg_tac>>fs[])>>rw[Abbr`w'`]>>
    fs[w8_to_w32_w32_to_w8])>>
  rw[]>>
  pop_assum drule>>
  disch_then drule>>
  strip_tac>>
  rpt(xlet_auto>- (TRY(xcon)>>xsimpl))>>
  xapp>>  xsimpl>>
  `body_step Success w w''` by
    (fs[body_step_def,hide_def]>>
    qexists_tac`vv`>>rfs[]>>
    metis_tac[])>>
  rw[]
  >-
    (qexists_tac`x`>>simp[]>>xsimpl>>
    DISJ1_TAC>>
    simp[body_loop_def]>>
    fs[body_loop_def]>>
    metis_tac[RTC_RULES])
  >-
    (qexists_tac`x`>>simp[]>>xsimpl>>
    DISJ2_TAC>>
    qexists_tac`v'`>>simp[]>>
    fs[body_loop_def]>>
    metis_tac[RTC_RULES])
  >>
  qexists_tac`x`>>simp[]>>xsimpl>>
  DISJ2_TAC>>
  qexists_tac`v'`>>simp[]>>
  fs[body_loop_def]>>
  metis_tac[RTC_RULES]);

(* specify the full monitor *)
val monitor_loop_spec = Q.store_thm("monitor_loop_spec",`
  (* These specify what the inputs should be *)
  INTERVALARITH_FML_TYPE w.wc.init iv ∧
  INTERVALARITH_FML_TYPE w.wc.plant_monitor plantfv ∧
  INTERVALARITH_FML_TYPE w.wc.ctrl_monitor ctrlfv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.const_names const_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.sensor_names sensor_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrlplus_names ctrlplus_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrl_names ctrl_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.sensorplus_names sensorplus_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrlfixed_names ctrlfixed_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrlfixed_rhs ctrlfixed_rhsv ∧
  LIST_TYPE INTERVALARITH_TRM_TYPE w.wc.default defaultv ∧
  wf_config w.wc ∧
  eventually I w.wo.stop_oracle
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "monitor_loop" bot_st)
    [iv;plantfv;ctrlfv;const_namesv;sensor_namesv;ctrlplus_namesv;ctrl_namesv;sensorplus_namesv;ctrlfixed_namesv;ctrlfixed_rhsv;defaultv]
  (IOBOT w)
  (POSTv uv. &(UNIT_TYPE () uv) *
    SEP_EXISTS w'. IOBOT w' *
    & (
      (* Either the initial mach violates init immediately *)
      if ¬init_step w then
        w=w'
      else
      (w'.wo.stop_oracle 0 ∧
         body_loop w w')
         ∨
         ∃v. body_loop w v ∧ (body_step DefViol v w' ∨ body_step PlantViol v w')))`,
  rw[]>>
  xcf"monitor_loop" bot_st>>
  rpt(xlet_auto >- xsimpl)>>
  reverse xif
  >-
    (* init violated *)
    (reverse (Cases_on`wf_mach w`)
    >-
      (simp[IOBOT_def]>>xpull)>>
    xapp >> xsimpl>>
    qexists_tac`emp`>>qexists_tac`w`>>xsimpl>>
    rw[]>>xsimpl>>
    qexists_tac`w`>>simp[init_step_def]>>
    xsimpl>>
    fs[init_monitor_def,mk_state_def])
  >>
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    xsimpl>>
    rw[]
    >-
      (qexists_tac`x`>>
      xsimpl>>
      fs[init_step_def,init_monitor_def,mk_state_def])
    >>
      qexists_tac`x`>>
      xsimpl>>
      fs[init_step_def,init_monitor_def,mk_state_def]>>
      metis_tac[]);

val full_sandbox_def = Define`
  full_sandbox wc =
  Seq (init_sandbox wc) (Loop (body_sandbox Success wc))`

(* relating w to an abstract state via an intermediate
   concrete state *)
val state_rel_abs_def = Define`
  state_rel_abs w (st:wstate) ⇔
  ∃cst.
    state_rel w cst ∧
    st = abs_state cst`

(* Rewriting with the combined spec *)
val monitor_loop_full_spec = Q.store_thm("monitor_loop_full_spec",`
  (* These specify what the inputs should be *)
  INTERVALARITH_FML_TYPE w.wc.init iv ∧
  INTERVALARITH_FML_TYPE w.wc.plant_monitor plantfv ∧
  INTERVALARITH_FML_TYPE w.wc.ctrl_monitor ctrlfv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.const_names const_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.sensor_names sensor_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrlplus_names ctrlplus_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrl_names ctrl_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.sensorplus_names sensorplus_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrlfixed_names ctrlfixed_namesv ∧
  LIST_TYPE CLSTRING_TYPE w.wc.ctrlfixed_rhs ctrlfixed_rhsv ∧
  LIST_TYPE INTERVALARITH_TRM_TYPE w.wc.default defaultv ∧
  wf_config w.wc ∧
  state_rel_abs w st ∧
  eventually I w.wo.stop_oracle
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "monitor_loop" bot_st)
    [iv;plantfv;ctrlfv;const_namesv;sensor_namesv;ctrlplus_namesv;ctrl_namesv;sensorplus_namesv;ctrlfixed_namesv;ctrlfixed_rhsv;defaultv]
  (IOBOT w)
  (POSTv uv. &(UNIT_TYPE () uv) *
    SEP_EXISTS w'. IOBOT w' *
    & (
      if ¬init_step w then
      (* Case 1: the initial mach violates init immediately *)
        w = w'
      else
      (* Case 2: ran to completion, w' is obtained from w by RTC of body_step,
         and they correspond to a step of the full sandbox *)
      (w'.wo.stop_oracle 0 ∧ body_loop w w' ∧
        ∃st'. state_rel_abs w' st' ∧ wpsem (full_sandbox w.wc) st st') ∨
      (∃v sti.
        body_loop w v ∧
        state_rel_abs v sti ∧
        (* Case 3 and 4: ran successfully several loop iterations *)
        wpsem (full_sandbox w.wc) st sti ∧
        (* However, either an overflow or plant violation occurred at the last iteration *)
        (body_step DefViol v w' ∨ body_step PlantViol v w'))))`,
  strip_tac>>
  fs[state_rel_abs_def]>>
  reverse (Cases_on`wf_mach w`)
  >-
    (simp[IOBOT_def]>>xpull)>>
  drule monitor_loop_spec >>
  simp[]>>rw[]>>
  xapp>>xsimpl>>
  rw[]
  >-
    (* Case 1 *)
    xsimpl
  >-
    (* Case 2 *)
    (qexists_tac`x`>>xsimpl>>
    drule (GEN_ALL init_step_init_sandbox)>>
    simp[]>> disch_then drule>>rw[]>>

    drule body_loop_state_rel>>fs[init_step_def]>>
    disch_then drule>>
    rw[full_sandbox_def]>>
    DISJ1_TAC>> asm_exists_tac>>simp[]>>
    match_mp_tac cwpsem_wpsem>>
    simp[Once cwpsem_cases]>>
    metis_tac[])
  >>
    (* cases 3/4 *)
    qexists_tac`x`>>xsimpl>>
    drule (GEN_ALL init_step_init_sandbox)>>
    simp[] >> disch_then drule >> rw[]>>
    drule body_loop_state_rel>>fs[init_step_def]>>
    disch_then drule>>
    rw[full_sandbox_def]>>
    DISJ2_TAC>> asm_exists_tac >> simp[]>>
    asm_exists_tac>>simp[]>>
    match_mp_tac cwpsem_wpsem>>
    simp[Once cwpsem_cases]>>
    metis_tac[]);

val _ = export_theory();
