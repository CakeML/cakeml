(*
  Formalization of the CP to ILP phase (scheduling constraints)
*)
Theory cp_to_ilp_scheduling
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* ===================================================================== *)
(* Generic interval-disjointness kit, shared by Disjunctive (1 axis) and  *)
(* Disjunctive2D (2 axes). A "before" flag means task i finishes at/before *)
(* task j starts on some axis (pos_i + sz_i ≤ pos_j); a "zero" flag means  *)
(* a task has zero extent (sz_i ≤ 0). The flags are pinned by reify_flag.  *)
(* ===================================================================== *)

(* before flag for ordered pair (i,j) under annotation ann *)
Definition disj_before_def[simp]:
  disj_before name ann i j = INR (name, Indices [i;j] (SOME ann))
End

(* zero-extent flag for task i under annotation ann *)
Definition disj_zero_def[simp]:
  disj_zero name ann i = INR (name, Indices [i] (SOME ann))
End

(* before-links: for every ordered pair i≠j of possibly-active tasks,
     before(i,j) ⇔ pos_i + sz_i ≤ pos_j

   The task list ts = ZIP (ZIP (pos,sz), inactive) carries, per task, its
   position, size and static-inactivity flag.

  Inactive elements are those with length 0 (under non-strict semantics).
  *)
Definition mk_before_links_def:
  mk_before_links bnd name ann ts =
  flat_app (MAPi (λi ti.
    flat_app (MAPi (λj tj.
      if i = j ∨ SND ti ∨ SND tj then Nil
      else
        cbimply_var bnd (disj_before name ann i j)
            (mk_lin_constraint_ge
              [(1, FST (FST tj)); (-1, FST (FST ti)); (-1, SND (FST ti))] 0)
      ) ts)) ts)
End

Theorem mk_before_links_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mk_before_links bnd name ann ts)) ⇔
  ∀i j. i < LENGTH ts ∧ j < LENGTH ts ∧ i ≠ j ⇒
    let ((p_i,s_i),inact_i) = EL i ts in
    let ((p_j,s_j),inact_j) = EL j ts in
    ¬ inact_i ∧ ¬inact_j ⇒
    (wb (disj_before name ann i j) ⇔
      varc wi p_i + varc wi s_i ≤ varc wi p_j))
Proof
  strip_tac>>
  simp[mk_before_links_def, EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
  eq_tac>>rw[]
  >- (
    rpt (pairarg_tac>>gvs[])>>rw[]>>
    gvs[PULL_FORALL]>>
    first_x_assum(qspecl_then[`i`,`j`] mp_tac)>>
    simp[eval_iclin_term_def,iSUM_def]>>
    disch_then sym_sub_tac>>
    intLib.ARITH_TAC)
  >- (
    rw[]>>gvs[]>>
    first_x_assum drule_all>>
    rpt (pairarg_tac>>gvs[])>>rw[]>>
    simp[eval_iclin_term_def,iSUM_def]>>
    intLib.ARITH_TAC)
QED

(* zero-links: for every variable-size task, zero(i) ⇔ sz_i ≤ 0.
   Constant sizes get no zero flag (the comparison is decided statically). *)
Definition mk_zero_links_def:
  mk_zero_links bnd name ann sz =
  flat_app (MAPi (λi s.
    case s of
      INL v =>
          cbimply_var bnd (disj_zero name ann i)
            (mk_le s (INR 0))
    | INR c => Nil) sz)
End

Theorem mk_zero_links_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mk_zero_links bnd name ann sz)) ⇔
  ∀i v. i < LENGTH sz ∧ EL i sz = INL v ⇒
    (wb (disj_zero name ann i) ⇔ varc wi (EL i sz) ≤ 0))
Proof
  strip_tac>>
  simp[mk_zero_links_def, EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
  eq_tac>>rw[]
  >- (
    first_x_assum drule>>
    simp[varc_def]>>
    disch_then sym_sub_tac>>
    intLib.ARITH_TAC)
  >- (
    TOP_CASE_TAC>>gvs[varc_def]>>
    first_x_assum drule_all>>
    disch_then (fn th => simp[th])>>
    intLib.ARITH_TAC)
QED

(* separation clauses: for every ordered pair i≠j of possibly-active tasks,
   at-least-one of the before-orders (per pair-annotation) and the precomputed
   zero-escape literals of i and j. task_info element = (zero-lits, inactive). *)
Definition mk_sep_clauses_def:
  mk_sep_clauses name pair_anns task_info =
  flat_app (FLAT (MAPi (λi ii. FLAT (MAPi (λj jj.
    if i = j ∨ SND ii ∨ SND jj then []
    else
      [cat_least_one name (toString i ^ «_» ^ toString j ^ «sep») (
          FLAT (MAP (λa. [Pos (disj_before name a i j);
                          Pos (disj_before name a j i)]) pair_anns) ++
          FST ii ++ FST jj)]
    ) task_info)) task_info))
End

Theorem append_flat_app[local]:
  append (flat_app ls) = FLAT (MAP append ls)
Proof
  `∀acc. append (FOLDR Append acc ls) = FLAT (MAP append ls) ++ append acc` by
    (Induct_on `ls` >> rw[append_thm])>>
  simp[flat_app_def,append_thm]
QED

Theorem mk_sep_clauses_sem:
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mk_sep_clauses name pair_anns ts)) ⇔
  ∀i j. i < LENGTH ts ∧ j < LENGTH ts ∧ i ≠ j ⇒
    let (t_i,inact_i) = EL i ts in
    let (t_j,inact_j) = EL j ts in
    ¬ inact_i ∧ ¬inact_j ⇒
    (∃a. MEM a pair_anns ∧
       (wb (disj_before name a i j) ∨ wb (disj_before name a j i))) ∨
    (∃l. (MEM l t_i ∨ MEM l t_j) ∧ lit wb l))
Proof
  simp[mk_sep_clauses_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM]>>
  simp[MEM_FLAT,MEM_MAP,PULL_EXISTS,append_flat_app,MEM_MAPi]>>
  eq_tac>>rw[]
  >- (
    rpt (pairarg_tac>>gvs[])>>rw[]>>
    first_x_assum (drule_at (Pos (el 2)))>>
    qpat_x_assum`i < _` assume_tac>>
    disch_then drule>>rw[]>>
    gvs[MEM_FLAT,MEM_MAP]>>
    metis_tac[])>>
  pop_assum mp_tac>>rw[]>>gvs[]>>
  first_x_assum drule_all>>
  rpt (pairarg_tac>>gvs[])>>rw[]>>
  gvs[MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
  metis_tac[lit_def]
QED

(* Classification of a size varc:
   - statically inactive: a constant width ≤ 0 (the task can never conflict,
     so every separation clause / before-link touching it is dropped);
   - zero-escape literal(s): emitted only for a variable width — a constant
     width is decided at encode time, so it needs no reified zero flag. *)
Definition zsize_inactive_def:
  zsize_inactive s = case s of INR c => c ≤ 0 | INL v => F
End

Definition zsize_lit_def:
  zsize_lit name ann k s =
  case s of INL v => [Pos (disj_zero name ann k)] | INR c => []
End

(* Disjunctive *)
Definition cencode_disjunctive_def:
  cencode_disjunctive bnd xs ws strct name =
  if LENGTH xs ≠ LENGTH ws then cfalse_constr
  else
    let task_info =
      if strct then MAP (λs. ([],F)) ws
      else MAPi (λk s. (zsize_lit name «zw» k s, zsize_inactive s)) ws in
    Append (mk_before_links bnd name «bf»
      (ZIP (ZIP (xs,ws), (MAP SND task_info))))
    (Append (if strct then List [] else mk_zero_links bnd name «zw» ws)
      (mk_sep_clauses name [«bf»] task_info))
End

Definition encode_disjunctive_def:
  encode_disjunctive bnd xs ws strct name =
  abstr (cencode_disjunctive bnd xs ws strct name)
End

Theorem cencode_disjunctive_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive bnd xs ws strct name = es ⇒
  enc_rel wi es (encode_disjunctive bnd xs ws strct name) ec ec
Proof
  rw[encode_disjunctive_def]
QED

Theorem encode_disjunctive_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive xs ws strct)) ∧
  disjunctive_sem xs ws strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive bnd xs ws strct name)
Proof
  rw[]>>
  simp[encode_disjunctive_def,cencode_disjunctive_def]>>
  IF_CASES_TAC >- fs[disjunctive_sem_def]>>
  gvs[]>>
  CONJ_TAC >- (
    CONJ_TAC >- (
      (* before-links *)
      simp[mk_before_links_sem]>>
      rw[EL_ZIP]>>
      gvs[reify_avar_def,reify_flag_def])>>
    (* zero-links *)
    rw[mk_zero_links_sem]>>
    gvs[reify_avar_def,reify_flag_def])>>
  simp[mk_sep_clauses_sem]>>
  fs[disjunctive_sem_def]>>
  Cases_on`strct`
  >- ( (* strict: every pair active, no zero escapes *)
    rw[]>>
    rpt(pairarg_tac>>gvs[])>>
    rw[]>>gvs[EL_MAP]>>
    first_x_assum drule_all>>
    simp[reify_avar_def,reify_flag_def])>>
  (* non-strict: active pair ⇒ before order; inactive pair ⇒ the
     offending task is a variable whose zero-escape flag is set *)
  rw[]>>
  gvs[]>>
  first_x_assum (drule_at (Pos (el 3)))>>
  rw[]>>
  gvs[zsize_inactive_def,AllCasePreds(),zsize_lit_def,EL_MAP]>>
  every_case_tac>>
  gvs[reify_avar_def,reify_flag_def,SF DNF_ss, varc_INR]>>
  intLib.ARITH_TAC
QED

Theorem encode_disjunctive_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive bnd xs ws strct name) ⇒
  disjunctive_sem xs ws strct wi
Proof
  strip_tac>>
  `LENGTH xs = LENGTH ws` by (
    CCONTR_TAC>>
    gvs[encode_disjunctive_def,cencode_disjunctive_def,cfalse_constr_def])>>
  gvs[encode_disjunctive_def,cencode_disjunctive_def]>>
  Cases_on`strct`>>
  simp[disjunctive_sem_def]>>
  rw[]>>gvs[EL_MAP]
  >- ( (* strict: separation gives a before-order directly *)
    gvs[mk_sep_clauses_sem]>>
    first_x_assum drule_all>>
    gvs[mk_before_links_sem]>>
    first_assum drule_all>>
    pop_assum (assume_tac o GSYM)>>
    first_x_assum drule_all>>
    simp[EL_ZIP,EL_MAP])>>
  (* non-strict: both widths positive ⇒ neither inactive, zero-escapes ruled
     out by the zero-links, so the separation gives a before-order *)
  gvs[mk_sep_clauses_sem,mk_zero_links_sem,mk_before_links_sem]>>
  `¬zsize_inactive (EL i ws) ∧ ¬zsize_inactive (EL j ws)` by (
    Cases_on`EL i ws`>>Cases_on`EL j ws`>>
    gvs[zsize_inactive_def,varc_def]>>intLib.ARITH_TAC)>>
  qpat_x_assum`∀i' j'. _ ⇒ (λ((p_i,s_i),inact_i). _) _`(fn th =>
    mp_tac (Q.SPECL[`i`,`j`]th) >> mp_tac (Q.SPECL[`j`,`i`]th))>>
  simp[EL_ZIP,EL_MAPi,LENGTH_ZIP,LENGTH_MAPi]>>
  ntac 2 strip_tac>>
  qpat_x_assum`∀i' j'. _ ⇒ _ ⇒ _ ∨ ∃l. _`drule_all>>
  disch_then strip_assume_tac
  >- metis_tac[]
  >- metis_tac[]
  >> (* zero-escape literal set ⇒ zero flag ⇒ width ≤ 0, contradicting >0 *)
  gvs[zsize_lit_def]>>
  every_case_tac>>gvs[lit_def]>>
  first_x_assum (drule_at (Pat`_ = INL _`))>>
  gvs[varc_def]>>intLib.ARITH_TAC
QED

(* Disjunctive2D *)
Definition cencode_disjunctive2d_def:
  cencode_disjunctive2d bnd xs ys ws hs strct name =
  let n = LENGTH xs in
  if n ≠ LENGTH ys ∨ n ≠ LENGTH ws ∨ n ≠ LENGTH hs
  then cfalse_constr
  else
    let task_info =
      if strct then MAP (λs. ([],F)) ws
      else MAPi (λk wh.
         (zsize_lit name «zw» k (FST wh) ++ zsize_lit name «zh» k (SND wh),
          zsize_inactive (FST wh) ∨ zsize_inactive (SND wh))) (ZIP (ws,hs)) in
    let inactive = MAP SND task_info in
    Append (mk_before_links bnd name «bx»
        (ZIP (ZIP (xs,ws), inactive)))
    (Append (mk_before_links bnd name «by»
          (ZIP (ZIP (ys,hs), inactive)))
    (Append (if strct then List [] else mk_zero_links bnd name «zw» ws)
    (Append (if strct then List [] else mk_zero_links bnd name «zh» hs)
      (mk_sep_clauses name [«bx»;«by»] task_info))))
End

Definition encode_disjunctive2d_def:
  encode_disjunctive2d bnd xs ys ws hs strct name =
  abstr (cencode_disjunctive2d bnd xs ys ws hs strct name)
End

Theorem cencode_disjunctive2d_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive2d bnd xs ys ws hs strct name = es ⇒
  enc_rel wi es (encode_disjunctive2d bnd xs ys ws hs strct name) ec ec
Proof
  rw[encode_disjunctive2d_def]
QED

Theorem encode_disjunctive2d_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive2D xs ys ws hs strct)) ∧
  disjunctive2d_sem xs ys ws hs strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive2d bnd xs ys ws hs strct name)
Proof
  rw[]>>
  `LENGTH xs = LENGTH ys ∧ LENGTH ys = LENGTH ws ∧ LENGTH ws = LENGTH hs` by
    fs[disjunctive2d_sem_def]>>
  simp[encode_disjunctive2d_def,cencode_disjunctive2d_def]>>
  gvs[append_thm,EVERY_APPEND]>>
  rpt conj_tac
  >- ( (* before-links x *)
    simp[mk_before_links_sem]>>
    rw[EL_ZIP]>>
    gvs[reify_avar_def,reify_flag_def])
  >- ( (* before-links y *)
    simp[mk_before_links_sem]>>
    rw[EL_ZIP]>>
    gvs[reify_avar_def,reify_flag_def])
  >- ( (* zero-links w *)
    rw[mk_zero_links_sem]>>
    gvs[reify_avar_def,reify_flag_def])
  >- ( (* zero-links h *)
    rw[mk_zero_links_sem]>>
    gvs[reify_avar_def,reify_flag_def])
  >- ( (* separation clauses *)
    simp[mk_sep_clauses_sem]>>
    fs[disjunctive2d_sem_def]>>
    Cases_on`strct`
    >- ( (* strict: every pair active, no zero escapes *)
      rw[]>>
      gvs[EL_MAP,reify_avar_def,reify_flag_def,RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
      qpat_x_assum`∀i j. _ ⇒ _`(qspecl_then[`i`,`j`]mp_tac)>>
      simp[EL_MAP]>>intLib.ARITH_TAC)>>
    (* non-strict *)
    rw[]>>
    `i < LENGTH ws ∧ j < LENGTH ws` by gvs[LENGTH_MAPi,LENGTH_ZIP]>>
    `EL i (ZIP (ws,hs)) = (EL i ws,EL i hs) ∧
     EL j (ZIP (ws,hs)) = (EL j ws,EL j hs)` by (conj_tac>>irule EL_ZIP>>gvs[])>>
    gvs[EL_MAPi]>>
    qpat_x_assum`∀i j. _ ⇒ _`(qspecl_then[`i`,`j`]mp_tac)>>
    simp[EL_MAP]>>
    Cases_on`EL i ws`>>Cases_on`EL j ws`>>
    Cases_on`EL i hs`>>Cases_on`EL j hs`>>
    gvs[zsize_inactive_def,zsize_lit_def,reify_avar_def,reify_flag_def,
      lit_def,varc_INR,SF DNF_ss]>>
    intLib.ARITH_TAC)
QED

Theorem encode_disjunctive2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive2d bnd xs ys ws hs strct name) ⇒
  disjunctive2d_sem xs ys ws hs strct wi
Proof
  strip_tac>>
  `LENGTH xs = LENGTH ys ∧ LENGTH xs = LENGTH ws ∧ LENGTH xs = LENGTH hs` by (
    CCONTR_TAC>>
    gvs[encode_disjunctive2d_def,cencode_disjunctive2d_def,cfalse_constr_def])>>
  gvs[encode_disjunctive2d_def,cencode_disjunctive2d_def]>>
  gvs[append_thm,EVERY_APPEND]>>
  Cases_on`strct`>>
  gvs[mk_before_links_sem,mk_zero_links_sem,mk_sep_clauses_sem,
    LENGTH_MAPi,LENGTH_ZIP]>>
  simp[disjunctive2d_sem_def]>>
  rw[]>>gvs[EL_MAP]
  >- ( (* strict: separation gives a before-order on some axis *)
    qpat_x_assum`∀i' j'. _ ⇒ (λ((p_i,s_i),inact_i). _) _`(fn th =>
      mp_tac (Q.SPECL[`i`,`j`]th) >> mp_tac (Q.SPECL[`j`,`i`]th))>>
    qpat_x_assum`∀i' j'. _ ⇒ (λ((p_i,s_i),inact_i). _) _`(fn th =>
      mp_tac (Q.SPECL[`i`,`j`]th) >> mp_tac (Q.SPECL[`j`,`i`]th))>>
    simp[EL_ZIP,EL_MAP,LENGTH_ZIP,LENGTH_MAP]>>
    ntac 4 strip_tac>>
    qpat_x_assum`∀i' j'. _ ⇒ ∃a. _`drule_all>>
    disch_then strip_assume_tac>>gvs[]>>
    metis_tac[])>>
  (* non-strict: positive area ⇒ neither inactive, zero-escapes ruled out *)
  `¬zsize_inactive (EL i ws) ∧ ¬zsize_inactive (EL j ws) ∧
   ¬zsize_inactive (EL i hs) ∧ ¬zsize_inactive (EL j hs)` by (
    Cases_on`EL i ws`>>Cases_on`EL j ws`>>
    Cases_on`EL i hs`>>Cases_on`EL j hs`>>
    gvs[zsize_inactive_def,varc_def]>>intLib.ARITH_TAC)>>
  qpat_x_assum`∀i' j'. _ ⇒ (λ((p_i,s_i),inact_i). _) _`(fn th =>
    mp_tac (Q.SPECL[`i`,`j`]th) >> mp_tac (Q.SPECL[`j`,`i`]th))>>
  qpat_x_assum`∀i' j'. _ ⇒ (λ((p_i,s_i),inact_i). _) _`(fn th =>
    mp_tac (Q.SPECL[`i`,`j`]th) >> mp_tac (Q.SPECL[`j`,`i`]th))>>
  simp[EL_ZIP,EL_MAPi,EL_MAP,LENGTH_ZIP,LENGTH_MAPi]>>
  ntac 4 strip_tac>>
  qpat_x_assum`∀i' j'. _ ⇒ _ ⇒ _ ∨ ∃l. _`(qspecl_then[`i`,`j`]mp_tac)>>
  simp[EL_ZIP,EL_MAPi,EL_MAP,LENGTH_ZIP,LENGTH_MAPi]>>
  disch_then strip_assume_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >> (* zero-escape literal set ⇒ zero flag ⇒ width/height ≤ 0, contra >0 *)
  gvs[zsize_lit_def]>>
  every_case_tac>>gvs[lit_def]>>
  first_x_assum (drule_at (Pat`_ = INL _`))>>
  gvs[varc_def]>>intLib.ARITH_TAC
QED

(* Cumulative *)
Definition cencode_cumulative_def:
  cencode_cumulative bnd xs ws hs cap name =
  (* TODO *)
  cfalse_constr
End

Definition encode_cumulative_def:
  encode_cumulative bnd xs ws hs cap name =
  abstr (cencode_cumulative bnd xs ws hs cap name)
End

Theorem cencode_cumulative_sem:
  valid_assignment bnd wi ∧
  cencode_cumulative bnd xs ws hs cap name = es ⇒
  enc_rel wi es (encode_cumulative bnd xs ws hs cap name) ec ec
Proof
  rw[encode_cumulative_def]
QED

Theorem encode_cumulative_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Cumulative xs ws hs cap)) ∧
  cumulative_sem xs ws hs cap wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_cumulative bnd xs ws hs cap name)
Proof
  cheat
QED

Theorem encode_cumulative_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_cumulative bnd xs ws hs cap name) ⇒
  cumulative_sem xs ws hs cap wi
Proof
  cheat
QED

Definition encode_scheduling_constr_def:
  encode_scheduling_constr bnd c name =
  case c of
    Disjunctive xs ws strct =>
      encode_disjunctive bnd xs ws strct name
  | Disjunctive2D xs ys ws hs strct =>
      encode_disjunctive2d bnd xs ys ws hs strct name
  | Cumulative xs ws hs cap =>
      encode_cumulative bnd xs ws hs cap name
End

Definition cencode_scheduling_constr_def:
  cencode_scheduling_constr bnd c name ec =
  case c of
    Disjunctive xs ws strct =>
      (cencode_disjunctive bnd xs ws strct name, ec)
  | Disjunctive2D xs ys ws hs strct =>
      (cencode_disjunctive2d bnd xs ys ws hs strct name, ec)
  | Cumulative xs ws hs cap =>
      (cencode_cumulative bnd xs ws hs cap name, ec)
End

Theorem encode_scheduling_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling c) ∧
  scheduling_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_scheduling_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_scheduling_constr_def,scheduling_constr_sem_def]
  >- metis_tac[encode_disjunctive_sem_1]
  >- metis_tac[encode_disjunctive2d_sem_1]
  >- metis_tac[encode_cumulative_sem_1]
QED

Theorem encode_scheduling_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_scheduling_constr bnd c name) ⇒
  scheduling_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_scheduling_constr_def,scheduling_constr_sem_def]
  >- metis_tac[encode_disjunctive_sem_2]
  >- metis_tac[encode_disjunctive2d_sem_2]
  >- metis_tac[encode_cumulative_sem_2]
QED

Theorem cencode_scheduling_constr_sem:
  valid_assignment bnd wi ∧
  cencode_scheduling_constr bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_scheduling_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  rw[cencode_scheduling_constr_def,encode_scheduling_constr_def]>>
  metis_tac[cencode_disjunctive_sem,cencode_disjunctive2d_sem,
    cencode_cumulative_sem]
QED
