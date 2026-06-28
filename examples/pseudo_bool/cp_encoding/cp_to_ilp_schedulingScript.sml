(*
  Formalization of the CP to ILP phase (scheduling constraints)
*)
Theory cp_to_ilp_scheduling
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp int_bitwiseExtra

(* Generic interval-disjointness kit, shared by Disjunctive (1 axis) and
   Disjunctive2D (2 axes): a "before" flag means task i finishes at/before task
   j starts on some axis (pos_i + sz_i ≤ pos_j); a "zero" flag means a task has
   zero extent (sz_i ≤ 0).  Flags are pinned by reify_flag. *)

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
  cencode_disjunctive bnd Xs Ws strct name =
  if LENGTH Xs ≠ LENGTH Ws then cfalse_constr
  else
    let task_info =
      if strct then MAP (λs. ([],F)) Ws
      else MAPi (λk s. (zsize_lit name «zw» k s, zsize_inactive s)) Ws in
    Append (mk_before_links bnd name «bf»
      (ZIP (ZIP (Xs,Ws), (MAP SND task_info))))
    (Append (if strct then List [] else mk_zero_links bnd name «zw» Ws)
      (mk_sep_clauses name [«bf»] task_info))
End

Definition encode_disjunctive_def:
  encode_disjunctive bnd Xs Ws strct name =
  abstr (cencode_disjunctive bnd Xs Ws strct name)
End

Theorem cencode_disjunctive_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive bnd Xs Ws strct name = es ⇒
  enc_rel wi es (encode_disjunctive bnd Xs Ws strct name) ec ec
Proof
  rw[encode_disjunctive_def]
QED

Theorem encode_disjunctive_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive Xs Ws strct)) ∧
  disjunctive_sem Xs Ws strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive bnd Xs Ws strct name)
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
    (encode_disjunctive bnd Xs Ws strct name) ⇒
  disjunctive_sem Xs Ws strct wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ws` by (
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
  `¬zsize_inactive (EL i Ws) ∧ ¬zsize_inactive (EL j Ws)` by (
    Cases_on`EL i Ws`>>Cases_on`EL j Ws`>>
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
  cencode_disjunctive2d bnd Xs Ys Ws Hs strct name =
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys ∨ n ≠ LENGTH Ws ∨ n ≠ LENGTH Hs
  then cfalse_constr
  else
    let task_info =
      if strct then MAP (λs. ([],F)) Ws
      else MAPi (λk wh.
         (zsize_lit name «zw» k (FST wh) ++ zsize_lit name «zh» k (SND wh),
          zsize_inactive (FST wh) ∨ zsize_inactive (SND wh))) (ZIP (Ws,Hs)) in
    let inactive = MAP SND task_info in
    Append (mk_before_links bnd name «bx»
        (ZIP (ZIP (Xs,Ws), inactive)))
    (Append (mk_before_links bnd name «by»
          (ZIP (ZIP (Ys,Hs), inactive)))
    (Append (if strct then List [] else mk_zero_links bnd name «zw» Ws)
    (Append (if strct then List [] else mk_zero_links bnd name «zh» Hs)
      (mk_sep_clauses name [«bx»;«by»] task_info))))
End

Definition encode_disjunctive2d_def:
  encode_disjunctive2d bnd Xs Ys Ws Hs strct name =
  abstr (cencode_disjunctive2d bnd Xs Ys Ws Hs strct name)
End

Theorem cencode_disjunctive2d_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive2d bnd Xs Ys Ws Hs strct name = es ⇒
  enc_rel wi es (encode_disjunctive2d bnd Xs Ys Ws Hs strct name) ec ec
Proof
  rw[encode_disjunctive2d_def]
QED

Theorem encode_disjunctive2d_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive2D Xs Ys Ws Hs strct)) ∧
  disjunctive2d_sem Xs Ys Ws Hs strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive2d bnd Xs Ys Ws Hs strct name)
Proof
  rw[]>>
  `LENGTH Xs = LENGTH Ys ∧ LENGTH Ys = LENGTH Ws ∧ LENGTH Ws = LENGTH Hs` by
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
    `i < LENGTH Ws ∧ j < LENGTH Ws` by gvs[LENGTH_MAPi,LENGTH_ZIP]>>
    `EL i (ZIP (Ws,Hs)) = (EL i Ws,EL i Hs) ∧
     EL j (ZIP (Ws,Hs)) = (EL j Ws,EL j Hs)` by (conj_tac>>irule EL_ZIP>>gvs[])>>
    gvs[EL_MAPi]>>
    qpat_x_assum`∀i j. _ ⇒ _`(qspecl_then[`i`,`j`]mp_tac)>>
    simp[EL_MAP]>>
    Cases_on`EL i Ws`>>Cases_on`EL j Ws`>>
    Cases_on`EL i Hs`>>Cases_on`EL j Hs`>>
    gvs[zsize_inactive_def,zsize_lit_def,reify_avar_def,reify_flag_def,
      lit_def,varc_INR,SF DNF_ss]>>
    intLib.ARITH_TAC)
QED

Theorem encode_disjunctive2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive2d bnd Xs Ys Ws Hs strct name) ⇒
  disjunctive2d_sem Xs Ys Ws Hs strct wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ys ∧ LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs` by (
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
  `¬zsize_inactive (EL i Ws) ∧ ¬zsize_inactive (EL j Ws) ∧
   ¬zsize_inactive (EL i Hs) ∧ ¬zsize_inactive (EL j Hs)` by (
    Cases_on`EL i Ws`>>Cases_on`EL j Ws`>>
    Cases_on`EL i Hs`>>Cases_on`EL j Hs`>>
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

(* Cumulative: time-table encoding.  For each task i and time t in [tlo,thi],
   reified flags pin started (sᵢ ≤ t), not-finished (sᵢ + wsᵢ ≥ t+1) and running
   (active = before ∧ after).  A proof-only contrib(i,t) equals the task height
   when active and 0 otherwise; per time the contribs sum to ≤ capacity.  Heights
   and capacity are pinned ≥ 0 (a constant height < 0 makes its own ≥0 line
   unsatisfiable).  Bits go through BIT in reify_flag, so no width bound is
   threaded through the flags. *)

(* domain (lb,ub) of a varc under bnd *)
Definition varc_bnd_def:
  varc_bnd (bnd:'a -> int # int) vc =
  case vc of INL v => bnd v | INR c => (c,c)
End

Theorem varc_bnd_valid:
  valid_assignment bnd wi ⇒
  FST (varc_bnd bnd vc) ≤ varc wi vc ∧ varc wi vc ≤ SND (varc_bnd bnd vc)
Proof
  Cases_on`vc`>>rw[varc_bnd_def,varc_def]>>
  gvs[valid_assignment_def]>>
  first_x_assum(qspec_then`x`mp_tac)>>
  Cases_on`bnd x`>>simp[]
QED

(* per-(task,time) reified flags, carrying the int time t in a Values flag *)
Definition cumul_before_def[simp]:
  cumul_before name i t = INR (name, Values [&i; t] (SOME «cb»))
End
Definition cumul_after_def[simp]:
  cumul_after name i t = INR (name, Values [&i; t] (SOME «ca»))
End
Definition cumul_active_def[simp]:
  cumul_active name i t = INR (name, Values [&i; t] (SOME «cact»))
End
Definition cumul_cbit_def[simp]:
  cumul_cbit name i t b = INR (name, Values [&i; t; &b] (SOME «cc»))
End

(* weighted bit-sum for the proof-only contribution of task i at time t,
   wide enough to represent its height upper bound ubh *)
Definition cumul_ub_num_def:
  cumul_ub_num name i t (ubh:int) =
  GENLIST (λb. (&(2 ** b), Pos (cumul_cbit name i t b)))
    (LENGTH (bits_of_num (Num (if 0 ≤ ubh then ubh else 0))))
End

Theorem cumul_ub_num_num_of_bits:
  eval_lin_term wb (cumul_ub_num name i t ubh) =
  &num_of_bits (GENLIST (λb. wb (cumul_cbit name i t b))
    (LENGTH (bits_of_num (Num (if 0 ≤ ubh then ubh else 0)))))
Proof
  rw[num_of_bits_GENLIST,cumul_ub_num_def,eval_lin_term_def,MAP_GENLIST,o_DEF]
QED

Theorem eval_lin_term_MAP_neg:
  ∀bs. eval_lin_term wb (MAP (λ(a,l). (-a,l)) bs) = -eval_lin_term wb bs
Proof
  Induct>>gvs[eval_lin_term_def,iSUM_def]>>
  Cases_on`h`>>gvs[eval_term_def,eval_lin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

(* the three half-reified constraints relating a contribution bit-sum cb to
   a height varc h:  cb ≥ h ,  cb ≤ h ,  cb ≤ 0 *)
Definition cumul_contrib_ge_def:
  cumul_contrib_ge cb h =
  case h of INL v => ([(-1i,v)],cb,0i) | INR c => ([],cb,c)
End
Definition cumul_contrib_le_def:
  cumul_contrib_le cb h =
  case h of INL v => ([(1i,v)],MAP (λ(a,l). (-a,l)) cb,0i)
          | INR c => ([],MAP (λ(a,l). (-a,l)) cb,-c)
End
Definition cumul_contrib_le0_def:
  cumul_contrib_le0 cb = ([],MAP (λ(a,l). (-a,l)) cb,0i)
End

Theorem cumul_contrib_ge_sem[simp]:
  iconstraint_sem (cumul_contrib_ge cb h) (wi,wb) ⇔
  eval_lin_term wb cb ≥ varc wi h
Proof
  Cases_on`h`>>
  rw[cumul_contrib_ge_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def]>>
  intLib.ARITH_TAC
QED

Theorem cumul_contrib_le_sem[simp]:
  iconstraint_sem (cumul_contrib_le cb h) (wi,wb) ⇔
  eval_lin_term wb cb ≤ varc wi h
Proof
  Cases_on`h`>>
  rw[cumul_contrib_le_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def,
     eval_lin_term_MAP_neg]>>
  intLib.ARITH_TAC
QED

Theorem cumul_contrib_le0_sem[simp]:
  iconstraint_sem (cumul_contrib_le0 cb) (wi,wb) ⇔ eval_lin_term wb cb ≤ 0
Proof
  rw[cumul_contrib_le0_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,
     eval_lin_term_MAP_neg]>>
  intLib.ARITH_TAC
QED

(* active(i,t) ⇔ before(i,t) ∧ after(i,t) *)
Definition mk_cumul_active_def:
  mk_cumul_active name i t =
  let a = cumul_active name i t in
  let bf = cumul_before name i t in
  let af = cumul_after name i t in
  let pre = toString i ^ «_» ^ toString (intnum t) in
  flat_app [
    cat_least_one name (pre ^ «_acta») [Neg a; Pos bf];
    cat_least_one name (pre ^ «_actb») [Neg a; Pos af];
    cat_least_one name (pre ^ «_actc») [Pos a; Neg bf; Neg af]]
End

Theorem mk_cumul_active_sem:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (mk_cumul_active name i t)) ⇔
  (wb (cumul_active name i t) ⇔
   wb (cumul_before name i t) ∧ wb (cumul_after name i t))
Proof
  rw[mk_cumul_active_def,flat_app_def]>>
  simp[append_thm,at_least_one_sem,MEM,lit_def,RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  metis_tac[]
QED

(* contribution-defining lines for task i (height h) at time t *)
Definition mk_cumul_contrib_def:
  mk_cumul_contrib bnd name h i t =
  let ubh = SND (varc_bnd bnd h) in
  let cb = cumul_ub_num name i t ubh in
  let act = cumul_active name i t in
  let pre = toString i ^ «_» ^ toString (intnum t) in
  List (mk_annotate
    [mk_name name (pre ^ «_cge»); mk_name name (pre ^ «_cle»);
     mk_name name (pre ^ «_cz»)]
    [bits_imply bnd [Pos act] (cumul_contrib_ge cb h);
     bits_imply bnd [Pos act] (cumul_contrib_le cb h);
     bits_imply bnd [Neg act] (cumul_contrib_le0 cb)])
End

(* non-negativity good default: capacity ≥ 0 and each height ≥ 0 *)
Definition cumul_nonneg_def:
  cumul_nonneg name tasks cap =
  List (mk_annotate
    (mk_name name «cap_ge0» ::
     MAPi (λi (x,w,h). mk_name name («h_» ^ toString i ^ «_ge0»)) tasks)
    (mk_constraint_one_ge 1 cap 0 ::
     MAP (λ(x,w,h). mk_constraint_one_ge 1 h 0) tasks))
End

Theorem cumul_nonneg_sem:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cumul_nonneg name tasks cap)) ⇔
  0 ≤ varc wi cap ∧ EVERY (λ(x,w,h). 0 ≤ varc wi h) tasks
Proof
  rw[cumul_nonneg_def,abstrl_mk_annotate,EVERY_MAP]>>
  simp[integerTheory.INT_GE,LAMBDA_PROD]
QED

(* per-task active window: t ranges over [lb_x, ub_x + ub_w - 1] *)
Definition task_lo_def:
  task_lo bnd x = FST (varc_bnd bnd x)
End
Definition task_hi_def:
  task_hi bnd x w = SND (varc_bnd bnd x) + SND (varc_bnd bnd w) - 1
End
Definition cumul_covers_def:
  cumul_covers bnd x w t ⇔ task_lo bnd x ≤ t ∧ t ≤ task_hi bnd x w
End
Definition cumul_ts_task_def:
  cumul_ts_task bnd x w =
  GENLIST (λk. task_lo bnd x + &k)
    (if task_hi bnd x w < task_lo bnd x then 0
     else Num (task_hi bnd x w - task_lo bnd x + 1))
End

(* cap-line times: the deduplicated union of all per-task windows, built with
   the same sorted-set machinery as union_dom *)
Definition cumul_times_def:
  cumul_times bnd tasks =
  numset_to_intlist (FOLDL union LN
    (MAP (λ(x,w,h). list_to_num_set (MAP intnum (cumul_ts_task bnd x w))) tasks))
End

Theorem MEM_cumul_ts_task:
  MEM t (cumul_ts_task bnd x w) ⇔ cumul_covers bnd x w t
Proof
  rw[cumul_ts_task_def,cumul_covers_def,MEM_GENLIST]>>
  Cases_on ‘task_hi bnd x w < task_lo bnd x’>>gvs[]
  >- intLib.ARITH_TAC>>
  `0 ≤ task_hi bnd x w - task_lo bnd x + 1` by intLib.ARITH_TAC>>
  `&(Num (task_hi bnd x w - task_lo bnd x + 1)) =
     task_hi bnd x w - task_lo bnd x + 1` by metis_tac[integerTheory.INT_OF_NUM]>>
  eq_tac>>rw[]
  >- intLib.ARITH_TAC
  >- (
    `(&k):int < &(Num (task_hi bnd x w - task_lo bnd x + 1))` by
      simp[integerTheory.INT_LT]>>
    intLib.ARITH_TAC)>>
  qexists`Num (t - task_lo bnd x)`>>
  `0 ≤ t - task_lo bnd x` by intLib.ARITH_TAC>>
  `&(Num (t - task_lo bnd x)) = t - task_lo bnd x` by
    metis_tac[integerTheory.INT_OF_NUM]>>
  `(&(Num (t - task_lo bnd x))):int < &(Num (task_hi bnd x w - task_lo bnd x + 1))` by
    intLib.ARITH_TAC>>
  fs[integerTheory.INT_LT]>>
  intLib.ARITH_TAC
QED

Theorem MEM_cumul_times:
  MEM t (cumul_times bnd tasks) ⇔
  ∃x w h. MEM (x,w,h) tasks ∧ MEM t (cumul_ts_task bnd x w)
Proof
  rw[cumul_times_def,MEM_numset_to_intlist,domain_FOLDL_union,domain_def,
     MEM_MAP,PULL_EXISTS,domain_list_to_num_set,EXISTS_PROD]>>
  metis_tac[numint_intnum]
QED

(* an active task is covered by its own window *)
Theorem cumul_active_in_window:
  valid_assignment bnd wi ∧
  varc wi x ≤ t ∧ varc wi x + varc wi w ≥ t + 1 ⇒
  cumul_covers bnd x w t
Proof
  rw[cumul_covers_def,task_lo_def,task_hi_def]>>
  `FST (varc_bnd bnd x) ≤ varc wi x ∧ varc wi x ≤ SND (varc_bnd bnd x) ∧
   FST (varc_bnd bnd w) ≤ varc wi w ∧ varc wi w ≤ SND (varc_bnd bnd w)` by
    metis_tac[varc_bnd_valid]>>
  intLib.ARITH_TAC
QED

(* per-time capacity line: Σ contrib(i,t) ≤ cap, summed over the tasks whose
   window covers t *)
Definition cumul_cap_line_def:
  cumul_cap_line bnd name tasks cap t =
  let loadbs = FLAT (MAPi (λi (x,w,h).
      if cumul_covers bnd x w t
      then MAP (λ(a,l). (-a,l)) (cumul_ub_num name i t (SND (varc_bnd bnd h)))
      else []) tasks) in
  let lbl = mk_name name («cap_» ^ toString (intnum t)) in
  case cap of
    INR c => List [(SOME lbl, ([],loadbs,-c))]
  | INL v => List [(SOME lbl, ([(1i,v)],loadbs,0i))]
End

Theorem eval_lin_term_FLAT_MAPi_neg_if:
  ∀ls g P. eval_lin_term wb
    (FLAT (MAPi (λi (x,w,h).
       if P i x w h then MAP (λ(c,l). (-c,l)) (g i x w h) else []) ls)) =
  -iSUM (MAPi (λi (x,w,h).
       if P i x w h then eval_lin_term wb (g i x w h) else 0) ls)
Proof
  Induct
  >- rw[eval_lin_term_def,iSUM_def,indexedListsTheory.MAPi_def]
  >- (
    qx_gen_tac`e`>>PairCases_on`e`>>
    pop_assum (fn ih =>
      rw[indexedListsTheory.MAPi_def,combinTheory.o_DEF,iSUM_def,
         pbc_encodeTheory.eval_lin_term_append,eval_lin_term_MAP_neg,ih])>>
    intLib.ARITH_TAC)
QED

Theorem cumul_cap_line_sem:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cumul_cap_line bnd name tasks cap t)) ⇔
  iSUM (MAPi (λi (x,w,h).
    if cumul_covers bnd x w t
    then eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h)))
    else 0) tasks) ≤ varc wi cap
Proof
  rw[cumul_cap_line_def]>>
  CASE_TAC>>
  simp[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def,
       eval_lin_term_FLAT_MAPi_neg_if]>>
  intLib.ARITH_TAC
QED

Theorem num_of_bits_GENLIST_F[local]:
  num_of_bits (GENLIST (λb. F) w) = 0
Proof
  `num_of_bits (GENLIST (λb. BIT b 0) w) = 0` by simp[num_of_bits_GENLIST_BIT]>>
  fs[bitTheory.BIT_ZERO]
QED

(* under reify_avar the contribution bit-sum evaluates to the (non-negative)
   height when active and 0 otherwise *)
Theorem cumul_ub_num_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Cumulative Xs Ws Hs cap)) ∧
  i < LENGTH Hs ∧ 0 ≤ varc wi (EL i Hs) ⇒
  eval_lin_term (reify_avar cs wi)
    (cumul_ub_num name i t (SND (varc_bnd bnd (EL i Hs)))) =
  (if varc wi (EL i Xs) ≤ t ∧
      varc wi (EL i Xs) + varc wi (EL i Ws) ≥ t + 1
   then varc wi (EL i Hs) else 0)
Proof
  rw[cumul_ub_num_num_of_bits,reify_avar_def,reify_flag_def]>>
  simp[num_of_bits_GENLIST_F,num_of_bits_GENLIST_BIT]>>
  `0 ≤ SND (varc_bnd bnd (EL i Hs)) ∧
   varc wi (EL i Hs) ≤ SND (varc_bnd bnd (EL i Hs))` by
    metis_tac[varc_bnd_valid,integerTheory.INT_LE_TRANS]>>
  `(if 0 ≤ SND (varc_bnd bnd (EL i Hs)) then SND (varc_bnd bnd (EL i Hs)) else 0) =
   SND (varc_bnd bnd (EL i Hs))` by gvs[]>>
  pop_assum SUBST_ALL_TAC>>
  `&(Num (varc wi (EL i Hs))):int = varc wi (EL i Hs)` by
    metis_tac[integerTheory.INT_OF_NUM]>>
  `&(Num (SND (varc_bnd bnd (EL i Hs)))):int = SND (varc_bnd bnd (EL i Hs))` by
    metis_tac[integerTheory.INT_OF_NUM]>>
  `Num (varc wi (EL i Hs)) ≤ Num (SND (varc_bnd bnd (EL i Hs)))` by
    (`(&(Num (varc wi (EL i Hs)))):int ≤ &(Num (SND (varc_bnd bnd (EL i Hs))))` by
       intLib.ARITH_TAC>>
     fs[integerTheory.INT_LE])>>
  `Num (varc wi (EL i Hs)) <
   2 ** LENGTH (bits_of_num (Num (SND (varc_bnd bnd (EL i Hs)))))` by
    metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS,LESS_LENGTH_bits_of_num]>>
  gs[arithmeticTheory.LESS_MOD]>>
  metis_tac[integerTheory.INT_OF_NUM]
QED

Definition cencode_cumulative_def:
  cencode_cumulative bnd Xs Ws Hs cap name =
  if LENGTH Xs ≠ LENGTH Ws ∨ LENGTH Xs ≠ LENGTH Hs then cfalse_constr
  else
    let tasks = ZIP (Xs, ZIP (Ws, Hs)) in
    Append (cumul_nonneg name tasks cap)
    (Append
      (flat_app (MAPi (λi (x,w,h).
         flat_app (MAP (λt.
           Append
             (cbimply_var bnd (cumul_before name i t) (mk_le x (INR t)))
           (Append
             (cbimply_var bnd (cumul_after name i t)
               (mk_constraint_ge 1 x 1 w (t + 1)))
           (Append (mk_cumul_active name i t)
                   (mk_cumul_contrib bnd name h i t)))) (cumul_ts_task bnd x w))) tasks))
      (flat_app (MAP (λt. cumul_cap_line bnd name tasks cap t) (cumul_times bnd tasks))))
End

Definition encode_cumulative_def:
  encode_cumulative bnd Xs Ws Hs cap name =
  abstr (cencode_cumulative bnd Xs Ws Hs cap name)
End

Theorem cencode_cumulative_sem:
  valid_assignment bnd wi ∧
  cencode_cumulative bnd Xs Ws Hs cap name = es ⇒
  enc_rel wi es (encode_cumulative bnd Xs Ws Hs cap name) ec ec
Proof
  rw[encode_cumulative_def]
QED

Theorem encode_cumulative_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Cumulative Xs Ws Hs cap)) ∧
  cumulative_sem Xs Ws Hs cap wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_cumulative bnd Xs Ws Hs cap name)
Proof
  rw[]>>
  `LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs` by fs[cumulative_sem_def]>>
  simp[encode_cumulative_def,cencode_cumulative_def,append_thm,EVERY_APPEND]>>
  rpt conj_tac
  >- (
    simp[cumul_nonneg_sem]>>
    fs[cumulative_sem_def,EVERY_EL,EL_MAP]>>
    simp[EVERY_EL,LENGTH_ZIP,EL_ZIP,EL_MAP])
  >- (
    simp[EVERY_FLAT]>>
    simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
    rw[]>>
    Cases_on`EL n (ZIP (Xs,ZIP (Ws,Hs)))`>>Cases_on`r`>>
    gvs[combinTheory.o_DEF]>>
    `q = EL n Xs ∧ q' = EL n Ws ∧ r' = EL n Hs` by
      (qpat_x_assum`_ = (q,q',r')`mp_tac>>simp[EL_ZIP,LENGTH_ZIP])>>
    `0 ≤ varc wi (EL n Hs)` by fs[cumulative_sem_def,EVERY_EL,EL_MAP]>>
    gvs[]>>
    simp[append_flat_app,EVERY_FLAT,EVERY_MAP]>>
    simp[Once EVERY_MEM]>>
    rw[]
    >- (simp[EVERY_SND,abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,lit_def,
             reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT,varc_def]>>
        intLib.ARITH_TAC)
    >- (simp[EVERY_SND,abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,lit_def,
             reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT,varc_def]>>
        intLib.ARITH_TAC)
    >- simp[EVERY_SND,mk_cumul_active_sem,reify_avar_def,reify_flag_def,
            integerTheory.NUM_OF_INT]
    >- (simp[EVERY_SND,mk_cumul_contrib_def,abstrl_mk_annotate,bits_imply_sem,lit_def,
             reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]>>
        DEP_REWRITE_TAC[cumul_ub_num_reify]>>
        simp[]>>rw[]>>intLib.ARITH_TAC))
  >- (
    simp[EVERY_FLAT,EVERY_MAP]>>
    simp[Once EVERY_MEM]>>rw[]>>
    simp[EVERY_SND,cumul_cap_line_sem]>>
    `∀j. j < LENGTH Hs ⇒ 0 ≤ varc wi (EL j Hs)` by
      fs[cumulative_sem_def,EVERY_EL,EL_MAP]>>
    (* drop the covering guard: a non-covering task is inactive, so its
       contribution is 0 either way *)
    `iSUM (MAPi (λi (x,w,h).
        if cumul_covers bnd x w t
        then eval_lin_term (reify_avar cs wi)
               (cumul_ub_num name i t (SND (varc_bnd bnd h))) else 0)
       (ZIP (Xs,ZIP (Ws,Hs)))) =
     iSUM (MAPi (λi (x,w,h).
        eval_lin_term (reify_avar cs wi)
          (cumul_ub_num name i t (SND (varc_bnd bnd h)))) (ZIP (Xs,ZIP (Ws,Hs))))` by (
      AP_TERM_TAC>>irule LIST_EQ>>simp[LENGTH_MAPi,LENGTH_ZIP]>>rw[]>>
      `0 ≤ varc wi (EL x Hs)` by gs[]>>
      simp[EL_MAPi,EL_ZIP,EL_MAP]>>IF_CASES_TAC>>simp[]>>
      DEP_REWRITE_TAC[cumul_ub_num_reify]>>simp[]>>rw[]>>
      metis_tac[cumul_active_in_window])>>
    pop_assum SUBST1_TAC>>
    qpat_x_assum`cumulative_sem _ _ _ _ _`mp_tac>>
    simp[cumulative_sem_def]>>strip_tac>>
    first_x_assum(qspec_then`t`mp_tac)>>
    qmatch_goalsub_abbrev_tac`iSUM cumls ≤ vc ⇒ iSUM myls ≤ vc`>>
    `myls = cumls` suffices_by simp[]>>
    unabbrev_all_tac>>
    irule LIST_EQ>>
    simp[LENGTH_MAPi,LENGTH_ZIP,EL_MAPi,EL_ZIP,EL_MAP]>>
    rw[]>>
    `0 ≤ varc wi (EL x Hs)` by gs[]>>
    DEP_REWRITE_TAC[cumul_ub_num_reify]>>
    simp[EL_MAP]>>
    simp[intLib.ARITH_PROVE``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``])
QED

Theorem cumul_ub_num_nonneg:
  0 ≤ eval_lin_term wb (cumul_ub_num name i t ubh)
Proof
  rw[cumul_ub_num_num_of_bits]
QED

Theorem iSUM_GENLIST_0[local]:
  iSUM (GENLIST (λi. 0i) n) = 0
Proof
  Induct_on`n`>>rw[GENLIST_CONS,iSUM_def,combinTheory.o_DEF]
QED

(* the per-(task,time) block forces the contribution bit-sum to the (gated)
   height, for any wb satisfying it *)
Theorem cumul_taskt_sound:
  valid_assignment bnd wi ∧
  EVERY (λy. iconstraint_sem (SND y) (wi,wb))
    (append
      (Append (cbimply_var bnd (cumul_before name i t) (mk_le x (INR t)))
      (Append (cbimply_var bnd (cumul_after name i t)
                 (mk_constraint_ge 1 x 1 w (t + 1)))
      (Append (mk_cumul_active name i t)
              (mk_cumul_contrib bnd name h i t))))) ⇒
  eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h))) =
  (if varc wi x ≤ t ∧ varc wi x + varc wi w ≥ t + 1
   then varc wi h else 0)
Proof
  strip_tac>>
  `0 ≤ eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h)))` by
    simp[cumul_ub_num_nonneg]>>
  gvs[append_thm,EVERY_APPEND,EVERY_SND,abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,lit_def,
      mk_cumul_active_sem,mk_cumul_contrib_def,abstrl_mk_annotate,
      bits_imply_sem,varc_def]>>
  Cases_on`wb (INR (name,Values [&i; t] (SOME «cb»)))`>>
  Cases_on`wb (INR (name,Values [&i; t] (SOME «ca»)))`>>
  gvs[]>>intLib.ARITH_TAC
QED

(* a task's flag+contrib lines force its contribution bit-sum to its gated
   height, at every time in its own window *)
Theorem cumul_flags_contrib:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (flat_app (MAPi (λi (x,w,h).
       flat_app (MAP (λt.
         Append
           (cbimply_var bnd (cumul_before name i t) (mk_le x (INR t)))
         (Append
           (cbimply_var bnd (cumul_after name i t)
              (mk_constraint_ge 1 x 1 w (t + 1)))
         (Append (mk_cumul_active name i t)
                 (mk_cumul_contrib bnd name h i t)))) (cumul_ts_task bnd x w)))
       tasks))) ⇒
  ∀i x w h t. i < LENGTH tasks ∧ EL i tasks = (x,w,h) ∧
    MEM t (cumul_ts_task bnd x w) ⇒
    eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h))) =
    (if varc wi x ≤ t ∧ varc wi x + varc wi w ≥ t + 1 then varc wi h else 0)
Proof
  strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`EVERY _ (abstr _)`mp_tac>>
  simp[append_flat_app,EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_EL,LENGTH_MAPi]>>
  disch_then(qspec_then`i`mp_tac)>>simp[EL_MAPi]>>
  qpat_x_assum`EL i tasks = _`(fn th => simp[th])>>
  simp[append_flat_app,EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_MEM]>>
  disch_then(qspec_then`t`mp_tac)>>simp[]>>
  strip_tac>>
  irule cumul_taskt_sound>>
  gvs[]
QED

Theorem encode_cumulative_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_cumulative bnd Xs Ws Hs cap name) ⇒
  cumulative_sem Xs Ws Hs cap wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs` by
    (CCONTR_TAC>>gvs[encode_cumulative_def,cencode_cumulative_def,cfalse_constr_def])>>
  gvs[encode_cumulative_def,cencode_cumulative_def,append_thm,EVERY_APPEND]>>
  `0 ≤ varc wi cap ∧ EVERY (λ(x,w,h). 0 ≤ varc wi h) (ZIP (Xs,ZIP (Ws,Hs)))` by
    (qpat_x_assum`EVERY _ (abstr (cumul_nonneg _ _ _))`mp_tac>>simp[cumul_nonneg_sem])>>
  `∀j. j < LENGTH Hs ⇒ 0 ≤ varc wi (EL j Hs)` by
    (gvs[EVERY_EL,LENGTH_ZIP]>>rw[]>>first_x_assum drule>>simp[EL_ZIP])>>
  simp[cumulative_sem_def,LENGTH_MAP]>>
  rpt conj_tac
  >- (simp[EVERY_EL,EL_MAP]>>metis_tac[])
  >- (
    qmatch_asmsub_abbrev_tac`cumul_cap_line bnd name tasks cap`>>
    `∀i x w h t. i < LENGTH tasks ∧ EL i tasks = (x,w,h) ∧
       MEM t (cumul_ts_task bnd x w) ⇒
       eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h))) =
       (if varc wi x ≤ t ∧ varc wi x + varc wi w ≥ t + 1 then varc wi h else 0)` by (
      ho_match_mp_tac cumul_flags_contrib>>
      gvs[abstr_flat_app,combinTheory.o_DEF])>>
    `∀t. MEM t (cumul_times bnd tasks) ⇒
       iSUM (MAPi (λi (x,w,h).
         if cumul_covers bnd x w t
         then eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h)))
         else 0) tasks) ≤ varc wi cap` by (
      qpat_x_assum`EVERY _ (FLAT (MAP _ (MAP _ _)))`mp_tac>>
      simp[EVERY_FLAT,EVERY_MAP,EVERY_SND,cumul_cap_line_sem,EVERY_MEM])>>
    strip_tac>>
    reverse (Cases_on`MEM t (cumul_times bnd tasks)`)
    >- (
      (* uncovered: no task's window contains t, so every task is inactive *)
      `GENLIST (λi. if (MAP (varc wi) Xs)❲i❳ ≤ t ∧
              t < (MAP (varc wi) Xs)❲i❳ + (MAP (varc wi) Ws)❲i❳
            then (MAP (varc wi) Hs)❲i❳ else 0) (LENGTH Ws) =
       GENLIST (λi. 0i) (LENGTH Ws)` by (
        simp[GENLIST_FUN_EQ]>>rw[]>>
        `i < LENGTH Xs ∧ i < LENGTH Hs` by gs[]>>
        `MEM (EL i Xs,EL i Ws,EL i Hs) tasks` by
          (simp[Abbr`tasks`,MEM_EL]>>qexists`i`>>simp[EL_ZIP,LENGTH_ZIP])>>
        `varc wi (EL i Xs) ≤ t ∧ varc wi (EL i Xs) + varc wi (EL i Ws) ≥ t + 1` by
          (gvs[EL_MAP]>>
           simp[intLib.ARITH_PROVE``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``])>>
        `cumul_covers bnd (EL i Xs) (EL i Ws) t` by metis_tac[cumul_active_in_window]>>
        metis_tac[MEM_cumul_times,MEM_cumul_ts_task])>>
      simp[iSUM_GENLIST_0])
    >- (
      (* covered: the cap line at t bounds the (deduplicated) load *)
      qpat_x_assum`∀t. MEM t (cumul_times _ _) ⇒ iSUM _ ≤ _`drule>>strip_tac>>
      `iSUM (GENLIST (λi. if (MAP (varc wi) Xs)❲i❳ ≤ t ∧
              t < (MAP (varc wi) Xs)❲i❳ + (MAP (varc wi) Ws)❲i❳
            then (MAP (varc wi) Hs)❲i❳ else 0) (LENGTH Ws)) =
       iSUM (MAPi (λi (x,w,h).
         if cumul_covers bnd x w t
         then eval_lin_term wb (cumul_ub_num name i t (SND (varc_bnd bnd h)))
         else 0) tasks)` by (
        AP_TERM_TAC>>irule LIST_EQ>>
        simp[Abbr`tasks`,LENGTH_MAPi,LENGTH_ZIP]>>
        qx_gen_tac`n`>>strip_tac>>
        `0 ≤ varc wi (EL n Hs) ∧ n < LENGTH Hs` by gs[]>>
        simp[EL_MAPi,EL_ZIP,EL_MAP,LENGTH_ZIP]>>
        reverse (Cases_on`cumul_covers bnd (EL n Xs) (EL n Ws) t`)>>simp[]
        >- (
          `¬(varc wi (EL n Xs) ≤ t ∧ varc wi (EL n Xs) + varc wi (EL n Ws) ≥ t + 1)` by
            metis_tac[cumul_active_in_window]>>
          gvs[intLib.ARITH_PROVE``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``])>>
        `eval_lin_term wb (cumul_ub_num name n t (SND (varc_bnd bnd (EL n Hs)))) =
         (if varc wi (EL n Xs) ≤ t ∧ varc wi (EL n Xs) + varc wi (EL n Ws) ≥ t + 1
          then varc wi (EL n Hs) else 0)` by
          (first_x_assum irule>>simp[EL_ZIP,LENGTH_ZIP,MEM_cumul_ts_task])>>
        simp[intLib.ARITH_PROVE``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``])>>
      gvs[]))
QED

Definition encode_scheduling_constr_def:
  encode_scheduling_constr bnd c name =
  case c of
    Disjunctive Xs Ws strct =>
      encode_disjunctive bnd Xs Ws strct name
  | Disjunctive2D Xs Ys Ws Hs strct =>
      encode_disjunctive2d bnd Xs Ys Ws Hs strct name
  | Cumulative Xs Ws Hs cap =>
      encode_cumulative bnd Xs Ws Hs cap name
End

Definition cencode_scheduling_constr_def:
  cencode_scheduling_constr bnd c name ec =
  case c of
    Disjunctive Xs Ws strct =>
      (cencode_disjunctive bnd Xs Ws strct name, ec)
  | Disjunctive2D Xs Ys Ws Hs strct =>
      (cencode_disjunctive2d bnd Xs Ys Ws Hs strct name, ec)
  | Cumulative Xs Ws Hs cap =>
      (cencode_cumulative bnd Xs Ws Hs cap name, ec)
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
