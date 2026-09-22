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

(* Cumulative: start-checkpoint encoding.  For every ordered pair (i,j) of
   active tasks, i ≠ j, three fully reified flags pin
     sb(i,j) ⇔ s_i ≤ s_j,   sa(i,j) ⇔ s_i + l_i ≥ s_j + 1,   sact(i,j) ⇔ sb ∧ sa
   so sact(i,j) holds exactly when task i is running when task j starts, and
   one row per active task j bounds the load at its start by the capacity.
   A task whose length or height has a non-positive upper bound never runs
   with positive height; it contributes nothing and gets no flags.  A task of
   constant length is running at its own start, so its own height goes to the
   row's right-hand side (constant) or integer side (variable); a task of
   variable length gets the diagonal flag sact(j,j) ⇔ l_j ≥ 1 instead.
   A variable height h_i is summed bit by bit through
     scc(i,j,k) ⇔ sact(i,j) ∧ bit_k(h_i)     and     sccs(i,j) ⇔ sact(i,j) ∧ sign(h_i)
   over the Bit/Sign literals of h_i itself.  Heights and capacity are pinned
   ≥ 0. *)

Definition cumul_sb_def[simp]:
  cumul_sb name i j = INR (name, Values [&i; &j] (SOME «sb»))
End
Definition cumul_sa_def[simp]:
  cumul_sa name i j = INR (name, Values [&i; &j] (SOME «sa»))
End
Definition cumul_sact_def[simp]:
  cumul_sact name i j = INR (name, Values [&i; &j] (SOME «sact»))
End
Definition cumul_scc_def[simp]:
  cumul_scc name i j k = INR (name, Values [&i; &j; &k] (SOME «scc»))
End
Definition cumul_sccs_def[simp]:
  cumul_sccs name i j = INR (name, Values [&i; &j] (SOME «sccs»))
End

Definition cumul_task_active_def:
  cumul_task_active bnd w h ⇔
  0 < SND (varc_bnd bnd w) ∧ 0 < SND (varc_bnd bnd h)
End

(* pair flags for contributor i and checkpoint j, i ≠ j *)
Definition cumul_pair_def:
  cumul_pair bnd name i x_i w_i j x_j =
  Append (cbimply_var bnd (cumul_sb name i j) (mk_le x_i x_j))
  (Append (cbimply_var bnd (cumul_sa name i j)
            (mk_lin_constraint_ge [(1,x_i);(1,w_i);(-1,x_j)] 1))
    (cbimply_var bnd (cumul_sact name i j)
      ([],[(1,Pos (cumul_sb name i j));(1,Pos (cumul_sa name i j))],2)))
End

(* the load term of contributor i at checkpoint j *)
Definition cumul_contrib_def:
  cumul_contrib bnd name i j h =
  case h of
    INR c => [(c, Pos (cumul_sact name i j))]
  | INL hv =>
    let (comp,w) = bit_width bnd hv in
    let bits = pos_num (cumul_scc name i j) w in
    if comp then (-&(2**w), Pos (cumul_sccs name i j)) :: bits else bits
End

(* scc(i,j,k) ⇔ sact(i,j) ∧ bit_k(h), and the sign analogue *)
Definition cumul_gate_def:
  cumul_gate bnd name i j h =
  case h of
    INR c => Nil
  | INL hv =>
    let (comp,w) = bit_width bnd hv in
    let act = Pos (cumul_sact name i j) in
    Append
      (flat_app (GENLIST (λk.
         cbimply_var bnd (cumul_scc name i j k)
           ([],[(1,act);(1,Pos (INL (Bit hv k)))],2)) w))
      (if comp then
         cbimply_var bnd (cumul_sccs name i j)
           ([],[(1,act);(1,Pos (INL (Sign hv)))],2)
       else Nil)
End

(* checkpoint row of active task j:  Σ_i contrib(i,j) + own height ≤ cap *)
Definition cumul_scap_row_def:
  cumul_scap_row bnd name tasks cap j w_j h_j =
  let loadbs = FLAT (MAPi (λi (x,w,h).
      if cumul_task_active bnd w h ∧ (i ≠ j ∨ ISL w)
      then cumul_contrib bnd name i j h else []) tasks) in
  let (dis,dfix) =
      if ISL w_j then ([],0i)
      else (case h_j of INL hv => ([(-1i,hv)],0i) | INR c => ([],c)) in
  let (cis,rhs) =
      (case cap of INL v => ([(1i,v)],dfix) | INR c => ([],dfix - c)) in
  List [(SOME (mk_name name («scap_» ^ toString j)),
         (cis ++ dis, flip_coeffs loadbs, rhs))]
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

Definition cencode_cumulative_def:
  cencode_cumulative bnd Xs Ws Hs cap name =
  if LENGTH Xs ≠ LENGTH Ws ∨ LENGTH Xs ≠ LENGTH Hs then cfalse_constr
  else
    let tasks = ZIP (Xs, ZIP (Ws, Hs)) in
    Append (cumul_nonneg name tasks cap)
    (flat_app (MAPi (λj (x_j,w_j,h_j).
       if ¬cumul_task_active bnd w_j h_j then Nil
       else
         Append
           (flat_app (MAPi (λi (x_i,w_i,h_i).
              if ¬cumul_task_active bnd w_i h_i then Nil
              else if i = j then
                (if ISL w_j then
                   Append
                     (cbimply_var bnd (cumul_sact name j j)
                        (mk_constraint_one_ge 1 w_j 1))
                     (cumul_gate bnd name j j h_j)
                 else Nil)
              else
                Append (cumul_pair bnd name i x_i w_i j x_j)
                       (cumul_gate bnd name i j h_i)) tasks))
           (cumul_scap_row bnd name tasks cap j w_j h_j)) tasks))
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

Theorem cumul_pair_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
     (abstr (cumul_pair bnd name i x_i w_i j x_j)) ⇔
   (wb (cumul_sb name i j) ⇔ varc wi x_i ≤ varc wi x_j) ∧
   (wb (cumul_sa name i j) ⇔ varc wi x_i + varc wi w_i ≥ varc wi x_j + 1) ∧
   (wb (cumul_sact name i j) ⇔ wb (cumul_sb name i j) ∧ wb (cumul_sa name i j)))
Proof
  strip_tac>>
  simp[cumul_pair_def,append_thm,abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,
       lit_def,eval_iclin_term_def,iSUM_def]>>
  simp[intLib.ARITH_PROVE ``∀a b:int. a + -1 * b ≥ 0 ⇔ b ≤ a``,
       intLib.ARITH_PROVE ``∀a b c:int. a + (b + -1 * c) ≥ 1 ⇔ a + b ≥ c + 1``]>>
  metis_tac[]
QED

Theorem num_of_bits_GENLIST_F[local]:
  num_of_bits (GENLIST (λb. F) w) = 0
Proof
  `GENLIST (λb. F) w = GENLIST (λb. BIT b 0) w` by simp[bitTheory.BIT_ZERO]>>
  pop_assum SUBST1_TAC>>
  rewrite_tac[num_of_bits_GENLIST_BIT]>>
  simp[]
QED

(* the gate rows force the load term to the height when running, else 0 *)
Theorem cumul_gate_sem:
  valid_assignment bnd wi ∧ bit_faithful bnd wi wb ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cumul_gate bnd name i j h)) ⇒
  eval_lin_term wb (cumul_contrib bnd name i j h) =
  if wb (cumul_sact name i j) then varc wi h else 0
Proof
  strip_tac>>
  Cases_on`h`>>gvs[cumul_gate_def,cumul_contrib_def]
  >- (
    rename1 `bit_width bnd hv`>>
    `∃comp w. bit_width bnd hv = (comp,w)` by metis_tac[PAIR]>>
    gvs[]>>
    qpat_x_assum`EVERY _ (FLAT _)`mp_tac>>
    simp[MAP_GENLIST,combinTheory.o_DEF,abstr_cbimply_var]>>
    simp[EVERY_FLAT,EVERY_GENLIST,EVERY_REVERSE,bimply_bit_sem,lit_def]>>
    strip_tac>>
    `eval_lin_term wb (ivar_bits bnd hv) = wi hv` by simp[ivar_bits_sem]>>
    `GENLIST (λb. wb (INR (name,Values [&i; &j; &b] (SOME «scc»)))) w =
     GENLIST (λk. wb (INR (name,Values [&i; &j] (SOME «sact»))) ∧
                  wb (INL (Bit hv k))) w` by
      (irule GENLIST_CONG>>simp[])>>
    Cases_on`comp`>>
    gvs[ivar_bits_def,pos_num_num_of_bits,abstr_cbimply_var,EVERY_REVERSE,
        bimply_bit_sem,lit_def]>>
    Cases_on`wb (INR (name,Values [&i; &j] (SOME «sact»)))`>>
    gvs[varc_def,num_of_bits_GENLIST_F])>>
  rw[pbc_encodeTheory.b2i_alt,varc_def]
QED

(* under reify_avar the load term is the height of a running task, else 0 *)
Theorem cumul_contrib_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs cap)) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  eval_lin_term (reify_avar cs wi) (cumul_contrib bnd name i j (EL i Hs)) =
  if varc wi (EL i Xs) ≤ varc wi (EL j Xs) ∧
     varc wi (EL i Xs) + varc wi (EL i Ws) ≥ varc wi (EL j Xs) + 1
  then varc wi (EL i Hs) else 0
Proof
  strip_tac>>
  Cases_on`EL i Hs`>>
  gvs[cumul_contrib_def,reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT,
      pbc_encodeTheory.b2i_alt]
  >- (
    rename1 `bit_width bnd hv`>>
    `∃comp w. bit_width bnd hv = (comp,w)` by metis_tac[PAIR]>>
    `varc wi (INL hv) = wi hv` by simp[varc_def]>>
    `eval_lin_term (reify_avar cs wi) (ivar_bits bnd hv) = wi hv` by
      simp[ivar_bits_sem]>>
    gvs[ivar_bits_def,pos_num_num_of_bits,reify_avar_def,reify_reif_def,
        reify_flag_def,integerTheory.NUM_OF_INT]>>
    Cases_on`comp`>>
    gvs[pos_num_num_of_bits,reify_avar_def,reify_reif_def,reify_flag_def,
        integerTheory.NUM_OF_INT]>>
    IF_CASES_TAC>>gvs[num_of_bits_GENLIST_F])>>
  rw[varc_def]
QED

Theorem eval_lin_term_FLAT_MAPi_if[local]:
  ∀ls g P. eval_lin_term wb
    (FLAT (MAPi (λi (x,w,h). if P i x w h then g i x w h else []) ls)) =
  iSUM (MAPi (λi (x,w,h).
    if P i x w h then eval_lin_term wb (g i x w h) else 0) ls)
Proof
  Induct
  >- rw[eval_lin_term_def,iSUM_def,indexedListsTheory.MAPi_def]>>
  qx_gen_tac`e`>>PairCases_on`e`>>
  pop_assum (fn ih =>
    rw[indexedListsTheory.MAPi_def,combinTheory.o_DEF,iSUM_def,ih])>>
  intLib.ARITH_TAC
QED

Theorem cumul_scap_row_sem:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cumul_scap_row bnd name tasks cap j w_j h_j)) ⇔
  iSUM (MAPi (λi (x,w,h).
    if cumul_task_active bnd w h ∧ (i ≠ j ∨ ISL w)
    then eval_lin_term wb (cumul_contrib bnd name i j h) else 0) tasks) +
  (if ISL w_j then 0 else varc wi h_j) ≤ varc wi cap
Proof
  simp[cumul_scap_row_def]>>
  Cases_on`cap`>>Cases_on`w_j`>>Cases_on`h_j`>>
  gvs[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def,
      eval_lin_term_FLAT_MAPi_if]>>
  intLib.ARITH_TAC
QED

Theorem exists_max_int[local]:
  ∀(f:'a -> int) ls. ls ≠ [] ⇒ ∃m. MEM m ls ∧ ∀y. MEM y ls ⇒ f y ≤ f m
Proof
  gen_tac>>Induct>>simp[]>>
  qx_gen_tac`x`>>
  Cases_on`ls = []`>>gvs[]>>
  Cases_on`f x ≤ f m`
  >- (qexists`m`>>rw[]>>gvs[])>>
  qexists`x`>>rw[]>>res_tac>>intLib.ARITH_TAC
QED

Theorem iSUM_GENLIST_le[local]:
  (∀i. i < n ⇒ f i ≤ g i) ⇒
  iSUM (GENLIST f n) ≤ iSUM (GENLIST (g:num -> int) n)
Proof
  Induct_on`n`>>rw[GENLIST,SNOC_APPEND,iSUM_APPEND,iSUM_def]>>
  `iSUM (GENLIST f n) ≤ iSUM (GENLIST g n)` by simp[]>>
  `f n ≤ g n` by simp[]>>
  ntac 2 (pop_assum mp_tac)>>rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
QED

(* a positive load at time t is at most the load at the start of some task j
   that is running at t with positive height: the running task with the latest
   start *)
Theorem cumul_load_at_start[local]:
  LENGTH ss = n ∧ LENGTH ls = n ∧ LENGTH hs = n ∧ EVERY (λh. 0 ≤ h) hs ∧
  0 < iSUM (GENLIST (λi. if EL i ss ≤ t ∧ t < EL i ss + EL i ls
                         then EL i hs else 0) n) ⇒
  ∃j. j < n ∧ 0 < EL j ls ∧ 0 < EL j hs ∧
    iSUM (GENLIST (λi. if EL i ss ≤ t ∧ t < EL i ss + EL i ls
                       then EL i hs else 0) n) ≤
    iSUM (GENLIST (λi. if EL i ss ≤ EL j ss ∧ EL j ss < EL i ss + EL i ls
                       then EL i hs else 0) n)
Proof
  strip_tac>>
  qabbrev_tac`R = FILTER (λi. EL i ss ≤ t ∧ t < EL i ss + EL i ls ∧ 0 < EL i hs)
                    (COUNT_LIST n)`>>
  `R ≠ []` by (
    CCONTR_TAC>>gvs[Abbr`R`,FILTER_EQ_NIL,every_count_list]>>
    `iSUM (GENLIST (λi. if EL i ss ≤ t ∧ t < EL i ss + EL i ls then EL i hs else 0)
       (LENGTH ss)) ≤ 0` by (
      irule pbc_encodeTheory.iSUM_le_0>>
      simp[MEM_GENLIST,PULL_EXISTS]>>
      qx_gen_tac`k`>>strip_tac>>rw[]>>
      first_x_assum drule>>
      `0 ≤ EL k hs` by gvs[EVERY_EL]>>
      simp[]>>rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
    qpat_x_assum`0 < iSUM _`mp_tac>>
    pop_assum mp_tac>>
    rpt (pop_assum kall_tac)>>
    intLib.ARITH_TAC)>>
  qspecl_then [`λi. EL i ss`,`R`] mp_tac exists_max_int>>
  simp[]>>strip_tac>>
  gvs[Abbr`R`,MEM_FILTER,MEM_COUNT_LIST]>>
  qexists`m`>>
  `0 < EL m ls` by (
    qpat_x_assum`EL m ss ≤ t`mp_tac>>
    qpat_x_assum`t < EL m ss + EL m ls`mp_tac>>
    rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
  simp[]>>
  irule iSUM_GENLIST_le>>rw[]
  >- (
    Cases_on`0 < EL i hs`
    >- (
      `EL i ss ≤ EL m ss` by (first_x_assum irule>>simp[])>>
      qpat_x_assum`¬(EL i ss ≤ EL m ss ∧ _)`mp_tac>>
      pop_assum mp_tac>>
      qpat_x_assum`EL m ss ≤ t`mp_tac>>
      qpat_x_assum`t < EL i ss + EL i ls`mp_tac>>
      rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
    pop_assum mp_tac>>rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
  gvs[EVERY_EL]
QED

(* under reify_avar every gate, pair and diagonal row holds *)
Theorem cumul_gate_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs cap)) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (cumul_gate bnd name i j (EL i Hs)))
Proof
  strip_tac>>
  Cases_on`EL i Hs`>>gvs[cumul_gate_def]>>
  rename1`bit_width bnd hv`>>
  `∃comp w. bit_width bnd hv = (comp,w)` by metis_tac[PAIR]>>
  gvs[append_thm,MAP_GENLIST,combinTheory.o_DEF,abstr_cbimply_var]>>
  Cases_on`comp`>>
  gvs[abstr_cbimply_var,EVERY_FLAT,EVERY_GENLIST,EVERY_REVERSE,bimply_bit_sem,
      lit_def,reify_avar_def,reify_reif_def,reify_flag_def,
      integerTheory.NUM_OF_INT,varc_def]>>
  metis_tac[]
QED

Theorem cumul_pair_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs cap)) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (cumul_pair bnd name i (EL i Xs) (EL i Ws) j (EL j Xs)))
Proof
  strip_tac>>
  simp[cumul_pair_sem,reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

Theorem cumul_diag_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs cap)) ∧
  j < LENGTH Xs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (cbimply_var bnd (INR (name,Values [&j; &j] (SOME «sact»)))
             (mk_constraint_one_ge 1 (EL j Ws) 1)))
Proof
  strip_tac>>
  simp[abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,lit_def,reify_avar_def,
       reify_flag_def,integerTheory.NUM_OF_INT]>>
  rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
QED

(* a task that cannot be active never loads the resource *)
Theorem cumul_inactive_zero:
  valid_assignment bnd wi ∧ ¬cumul_task_active bnd w h ∧ 0 ≤ varc wi h ⇒
  (if varc wi x ≤ t ∧ t < varc wi x + varc wi w then varc wi h else 0) = 0
Proof
  strip_tac>>
  `varc wi w ≤ SND (varc_bnd bnd w) ∧ varc wi h ≤ SND (varc_bnd bnd h)` by
    metis_tac[varc_bnd_valid]>>
  gvs[cumul_task_active_def]>>rw[]>>
  rpt (qpat_x_assum`valid_assignment _ _`kall_tac)>>
  intLib.ARITH_TAC
QED

Theorem MAPi_ZIP3_GENLIST[local]:
  LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs ⇒
  MAPi f (ZIP (Xs,ZIP (Ws,Hs))) =
  GENLIST (λi. f i (EL i Xs,EL i Ws,EL i Hs)) (LENGTH Xs)
Proof
  rw[]>>irule LIST_EQ>>simp[LENGTH_MAPi,LENGTH_ZIP,EL_MAPi,EL_ZIP]
QED

(* termwise bound where one term additionally carries c *)
Theorem iSUM_GENLIST_le_add[local]:
  j < n ∧ (∀i. i < n ∧ i ≠ j ⇒ a i ≤ b i) ∧ a j + c ≤ (b j):int ⇒
  iSUM (GENLIST a n) + c ≤ iSUM (GENLIST b n)
Proof
  strip_tac>>
  `n = (n - j) + j` by decide_tac>>
  qpat_x_assum`n = _`(fn th => ONCE_REWRITE_TAC[th])>>
  `n - j = SUC (n - j - 1)` by decide_tac>>
  pop_assum SUBST1_TAC>>
  simp[GENLIST_APPEND,GENLIST_CONS,iSUM_APPEND,iSUM_def,combinTheory.o_DEF]>>
  `iSUM (GENLIST a j) ≤ iSUM (GENLIST b j)` by
    (irule iSUM_GENLIST_le>>rw[]>>first_x_assum irule>>simp[])>>
  `iSUM (GENLIST (λx. a (j + SUC x)) (n - (j + 1))) ≤
   iSUM (GENLIST (λx. b (j + SUC x)) (n - (j + 1)))` by
    (irule iSUM_GENLIST_le>>rw[]>>first_x_assum irule>>simp[])>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_x_assum`a j + c ≤ b j`mp_tac>>
  rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
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
  conj_tac
  >- (
    simp[cumul_nonneg_sem]>>
    fs[cumulative_sem_def,EVERY_EL,EL_MAP]>>
    simp[EVERY_EL,LENGTH_ZIP,EL_ZIP,EL_MAP])>>
  simp[abstr_flat_app,MAPi_ZIP3_GENLIST,MAP_GENLIST,EVERY_FLAT,EVERY_GENLIST,
       combinTheory.o_DEF]>>
  qx_gen_tac`j`>>strip_tac>>
  IF_CASES_TAC>>simp[append_thm]>>
  conj_tac
  >- (
    simp[MAP_GENLIST,combinTheory.o_DEF,EVERY_FLAT,EVERY_GENLIST]>>
    rw[append_thm,EVERY_APPEND]>>
    simp[cumul_pair_reify,cumul_gate_reify]>>
    simp[reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]>>
    rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
  simp[cumul_scap_row_sem,MAPi_ZIP3_GENLIST]>>
  qpat_x_assum`cumulative_sem _ _ _ _ _`mp_tac>>
  simp[cumulative_sem_def]>>strip_tac>>
  first_x_assum(qspec_then`varc wi (EL j Xs)`mp_tac)>>
  simp[EL_MAP]>>strip_tac>>
  irule integerTheory.INT_LE_TRANS>>
  first_x_assum (irule_at Any)>>
  irule iSUM_GENLIST_le_add>>
  qexists`j`>>
  simp[EL_MAP]>>
  `∀i. i < LENGTH Hs ⇒ 0 ≤ varc wi (EL i Hs)` by gvs[EVERY_EL,EL_MAP]>>
  simp[cumul_contrib_reify,
       intLib.ARITH_PROVE ``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``]>>
  conj_tac
  >- (
    rw[]>>simp[]>>
    `eval_lin_term (reify_avar cs wi) (cumul_contrib bnd name i j (EL i Hs)) =
     if varc wi (EL i Xs) ≤ varc wi (EL j Xs) ∧
        varc wi (EL i Xs) + varc wi (EL i Ws) ≥ varc wi (EL j Xs) + 1
     then varc wi (EL i Hs) else 0` by (irule cumul_contrib_reify>>simp[])>>
    pop_assum SUBST1_TAC>>
    simp[intLib.ARITH_PROVE ``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``]>>
    rw[])>>
  Cases_on`EL j Ws`>>gvs[cumul_task_active_def,varc_bnd_def,varc_def]>>
  `eval_lin_term (reify_avar cs wi) (cumul_contrib bnd name j j (EL j Hs)) =
   if varc wi (EL j Xs) ≤ varc wi (EL j Xs) ∧
      varc wi (EL j Xs) + varc wi (EL j Ws) ≥ varc wi (EL j Xs) + 1
   then varc wi (EL j Hs) else 0` by (irule cumul_contrib_reify>>simp[])>>
  pop_assum SUBST1_TAC>>
  simp[varc_def,intLib.ARITH_PROVE ``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``]
QED

Theorem iSUM_GENLIST_add_le[local]:
  j < n ∧ (∀i. i < n ∧ i ≠ j ⇒ a i ≤ b i) ∧ a j ≤ b j + (c:int) ⇒
  iSUM (GENLIST a n) ≤ iSUM (GENLIST b n) + c
Proof
  strip_tac>>
  `n = (n - j) + j` by decide_tac>>
  qpat_x_assum`n = _`(fn th => ONCE_REWRITE_TAC[th])>>
  `n - j = SUC (n - j - 1)` by decide_tac>>
  pop_assum SUBST1_TAC>>
  simp[GENLIST_APPEND,GENLIST_CONS,iSUM_APPEND,iSUM_def,combinTheory.o_DEF]>>
  `iSUM (GENLIST a j) ≤ iSUM (GENLIST b j)` by
    (irule iSUM_GENLIST_le>>rw[]>>first_x_assum irule>>simp[])>>
  `iSUM (GENLIST (λx. a (j + SUC x)) (n - (j + 1))) ≤
   iSUM (GENLIST (λx. b (j + SUC x)) (n - (j + 1)))` by
    (irule iSUM_GENLIST_le>>rw[]>>first_x_assum irule>>simp[])>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_x_assum`a j ≤ b j + c`mp_tac>>
  rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
QED

Theorem encode_cumulative_sem_2:
  valid_assignment bnd wi ∧ bit_faithful bnd wi wb ∧
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
  `∀j. j < LENGTH Hs ∧ cumul_task_active bnd (EL j Ws) (EL j Hs) ⇒
     iSUM (GENLIST (λi.
       if EL i (MAP (varc wi) Xs) ≤ EL j (MAP (varc wi) Xs) ∧
          EL j (MAP (varc wi) Xs) <
            EL i (MAP (varc wi) Xs) + EL i (MAP (varc wi) Ws)
       then EL i (MAP (varc wi) Hs) else 0) (LENGTH Hs)) ≤ varc wi cap` by (
    qpat_x_assum`EVERY _ (FLAT (MAPi _ _))`mp_tac>>
    simp[MAPi_ZIP3_GENLIST,MAP_GENLIST,EVERY_FLAT,EVERY_GENLIST,combinTheory.o_DEF]>>
    strip_tac>>
    rw[]>>
    qpat_x_assum`∀j. j < _ ⇒ EVERY _ _`(qspec_then`j`mp_tac)>>
    simp[append_thm,EVERY_APPEND,cumul_scap_row_sem,MAPi_ZIP3_GENLIST]>>
    strip_tac>>
    irule integerTheory.INT_LE_TRANS>>
    qpat_x_assum`iSUM _ + _ ≤ _`(fn th => irule_at Any th)>>
    irule iSUM_GENLIST_add_le>>
    qexists`j`>>
    simp[EL_MAP]>>
    qpat_x_assum`EVERY _ (FLAT _)`mp_tac>>
    simp[MAP_GENLIST,combinTheory.o_DEF,EVERY_FLAT,EVERY_GENLIST]>>
    strip_tac>>
    conj_tac
    >- (
      qx_gen_tac`i`>>strip_tac>>
      `0 ≤ varc wi (EL i Hs)` by simp[]>>
      qpat_x_assum`∀i. i < _ ⇒ EVERY _ _`(qspec_then`i`mp_tac)>>
      simp[]>>
      Cases_on`cumul_task_active bnd (EL i Ws) (EL i Hs)`>>simp[]
      >- (
        simp[cumul_pair_sem]>>strip_tac>>
        drule_all cumul_gate_sem>>
        simp[intLib.ARITH_PROVE ``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``])>>
      `(if varc wi (EL i Xs) ≤ varc wi (EL j Xs) ∧
           varc wi (EL j Xs) < varc wi (EL i Xs) + varc wi (EL i Ws)
        then varc wi (EL i Hs) else 0) = 0` by
        (irule cumul_inactive_zero>>first_assum (irule_at Any)>>simp[])>>
      simp[])>>
    first_x_assum(qspec_then`j`mp_tac)>>simp[]>>
    Cases_on`ISL (EL j Ws)`>>
    simp[append_thm,EVERY_APPEND,abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,
         lit_def]
    >- (
      strip_tac>>drule_all cumul_gate_sem>>simp[]>>rw[]>>
      `varc wi (EL j Ws) ≥ 1` by
        (qpat_x_assum`0 < varc wi (EL j Ws)`mp_tac>>rpt (pop_assum kall_tac)>>
         intLib.ARITH_TAC)>>
      gvs[])>>
    rw[])>>
  simp[cumulative_sem_def]>>
  conj_tac >- simp[EVERY_EL,EL_MAP]>>
  qx_gen_tac`t`>>
  qmatch_goalsub_abbrev_tac`iSUM ls ≤ _`>>
  Cases_on`iSUM ls ≤ 0`
  >- (irule integerTheory.INT_LE_TRANS>>qexists`0`>>simp[])>>
  gvs[integerTheory.INT_NOT_LE,Abbr`ls`]>>
  drule_at Any cumul_load_at_start>>
  simp[]>>
  impl_tac >- simp[EVERY_EL,EL_MAP]>>
  strip_tac>>
  irule integerTheory.INT_LE_TRANS>>
  first_x_assum (irule_at Any)>>
  first_x_assum irule>>
  simp[cumul_task_active_def]>>
  `varc wi (EL j Ws) ≤ SND (varc_bnd bnd (EL j Ws)) ∧
   varc wi (EL j Hs) ≤ SND (varc_bnd bnd (EL j Hs))` by metis_tac[varc_bnd_valid]>>
  gvs[EL_MAP]>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_x_assum`0 < varc wi (EL j Ws)`mp_tac>>
  qpat_x_assum`0 < varc wi (EL j Hs)`mp_tac>>
  rpt (pop_assum kall_tac)>>
  intLib.ARITH_TAC
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
  bit_faithful bnd wi wb ∧
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
