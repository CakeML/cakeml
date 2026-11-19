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

(* zero-links: for every possibly-active variable-size task,
   zero(i) ⇔ sz_i ≤ 0.

   The task list ts = ZIP (sz, inactive) carries, per task, its size and
   static-inactivity flag. Constant sizes get no zero flag (the comparison
   is decided statically). *)
Definition mk_zero_links_def:
  mk_zero_links bnd name ann ts =
  flat_app (MAPi (λi (s,inact).
    case s of
      INL v =>
        if inact then Nil
        else
          cbimply_var bnd (disj_zero name ann i)
            (mk_le s (INR 0))
    | INR c => Nil) ts)
End

Theorem mk_zero_links_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mk_zero_links bnd name ann ts)) ⇔
  ∀i v. i < LENGTH ts ∧ EL i ts = (INL v,F) ⇒
    (wb (disj_zero name ann i) ⇔ wi v ≤ 0))
Proof
  strip_tac>>
  simp[mk_zero_links_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
  eq_tac>>rw[]
  >- (
    first_x_assum drule>>
    simp[varc_def]>>
    disch_then sym_sub_tac>>
    intLib.ARITH_TAC)>>
  pairarg_tac>>gvs[]>>
  TOP_CASE_TAC>>rw[]>>gvs[varc_def]>>
  first_x_assum drule_all>>
  disch_then (fn th => simp[th])>>
  intLib.ARITH_TAC
QED

(* separation clauses: for every pair i<j of possibly-active tasks,
   at-least-one of the before-orders (per pair-annotation) and the precomputed
   zero-escape literals of i and j. task_info element = (zero-lits, inactive). *)
Definition mk_sep_clauses_def:
  mk_sep_clauses name pair_anns task_info =
  flat_app (FLAT (MAPi (λi ii. FLAT (MAPi (λj jj.
    if j ≤ i ∨ SND ii ∨ SND jj then []
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
    qpat_x_assum`∀ls i j. _`(assume_tac o SIMP_RULE (srw_ss()) [COND_RAND])>>
    Cases_on`i < j`
    >- (
      first_x_assum (qspecl_then [`i`,`j`] mp_tac)>>
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS]>>rw[]>>gvs[lit_def]>>
      metis_tac[])>>
    first_x_assum (qspecl_then [`j`,`i`] mp_tac)>>
    simp[MEM_FLAT,MEM_MAP,PULL_EXISTS]>>rw[]>>gvs[lit_def]>>
    metis_tac[])>>
  pop_assum mp_tac>>rw[]>>gvs[]>>
  first_x_assum (qspecl_then [`i`,`j`] mp_tac)>>simp[]>>
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

(* Presence of a task:
   - a constant 1: always present, so no literal;
   - any other constant: the task is dropped (0 is absent; any other value is
     refuted by the range rows);
   - a variable P: a literal on P's value joins the encoding — Disjunctive's
     separation clauses take the absence literal [P = 0], Cumulative's sact
     flags the presence literal [P = 1]. *)
Definition pres_inactive_def:
  pres_inactive P = case P of INR c => c ≠ 1 | INL v => F
End

(* The literal [P = v] of a variable presence P, where v = 1 if b and v = 0
   otherwise: the bit P[b0] (b) or its negation ~P[b0] (¬b) when P is
   declared 0..1, otherwise the atom [P = v]; none for a constant. *)
Definition val_lit_def:
  val_lit bnd b P =
  case P of
    INL v =>
      if bnd v = (0,1) then [if b then Pos (INL (Bit v 0)) else Neg (INL (Bit v 0))]
      else [Pos (INL (Eq P (if b then 1 else 0)))]
  | INR c => []
End

Theorem val_lit_sem:
  valid_assignment bnd wi ∧ bit_faithful bnd wi wb ∧
  (∀v. P = INL v ∧ bnd v ≠ (0,1) ⇒
    (wb (INL (Eq P (if b then 1 else 0))) ⇔ wi v = if b then 1 else 0)) ⇒
  ((∃l. MEM l (val_lit bnd b P) ∧ lit wb l) ⇔
   ∃v. P = INL v ∧ wi v = if b then 1 else 0)
Proof
  strip_tac>>
  Cases_on`P`>>simp[val_lit_def]>>
  rw[lit_def]>>
  gvs[bit_faithful_def,valid_assignment_def]>>
  qpat_x_assum`∀x lb ub. _`(drule_then strip_assume_tac)>>
  qpat_x_assum`∀X. _`(qspec_then`x`mp_tac)>>
  simp[bit_width_def,EVAL``bits_of_int 1``]>>
  strip_tac>>
  `wi x = 0 ∨ wi x = 1` by intLib.ARITH_TAC>>
  simp[EVAL``int_bit 0 0``,EVAL``int_bit 0 1``]
QED

(* a presence that is not a constant other than 1 is present iff its
   presence literal (if any) holds *)
Theorem val_lit_T_every:
  valid_assignment bnd wi ∧ bit_faithful bnd wi wb ∧ ¬pres_inactive P ∧
  (∀v. P = INL v ∧ bnd v ≠ (0,1) ⇒ (wb (INL (Eq P 1)) ⇔ wi v = 1)) ⇒
  (EVERY (lit wb) (val_lit bnd T P) ⇔ varc wi P = 1)
Proof
  strip_tac>>
  drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.INST [`b`|->`T`] val_lit_sem))>>
  Cases_on`P`>>gvs[val_lit_def,pres_inactive_def,varc_def]>>
  rw[]
QED

Theorem LENGTH_val_lit[simp]:
  LENGTH (val_lit bnd b P) ≤ 1
Proof
  Cases_on`P`>>rw[val_lit_def]
QED

Theorem NULL_val_lit[simp]:
  NULL (val_lit bnd b P) ⇔ ¬ISL P
Proof
  Cases_on`P`>>rw[val_lit_def]
QED

(* the [P = v] atom used by val_lit, defined by full_eq rows *)
Definition val_eq_def:
  val_eq bnd b P =
  case P of
    INL v => if bnd v = (0,1) then [] else [(P,if b then 1 else 0:int)]
  | INR c => []
End

(* range rows 0 ≤ P ≤ 1 for each presence, omitted when its declared bounds
   imply them *)
Definition mk_pres_range_def:
  mk_pres_range bnd name Ps =
  flat_app (MAPi (λk P.
    Append
      (cmk_lb bnd (mk_name name («p_» ^ toString k ^ «_ge0»)) P 0)
      (cmk_ub bnd (mk_name name («p_» ^ toString k ^ «_le1»)) P 1)) Ps)
End

Theorem mk_pres_range_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (mk_pres_range bnd name Ps)) ⇔
   EVERY (λp. p = 0 ∨ p = 1) (MAP (varc wi) Ps))
Proof
  strip_tac>>
  simp[mk_pres_range_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF,cmk_lb_sem,cmk_ub_sem]>>
  simp[EVERY_EL,EL_MAP,
    intLib.ARITH_PROVE``0 ≤ (p:int) ∧ p ≤ 1 ⇔ p = 0 ∨ p = 1``]
QED

(* Disjunctive *)

(* per task: the escape literals of its separation clauses (zero width in
   non-strict mode; absence) and whether it is statically inactive *)
Definition disj_task_info_def:
  disj_task_info bnd name strct Ws Ps =
  MAPi (λk (W,P).
    ((if strct then [] else zsize_lit name «zw» k W) ++ val_lit bnd F P,
     pres_inactive P ∨ (¬strct ∧ zsize_inactive W))) (ZIP (Ws,Ps))
End

Theorem LENGTH_disj_task_info[simp]:
  LENGTH (disj_task_info bnd name strct Ws Ps) = MIN (LENGTH Ws) (LENGTH Ps)
Proof
  simp[disj_task_info_def,LENGTH_ZIP_MIN]
QED

(* a present task that can conflict is not statically inactive *)
Theorem disj_task_active:
  k < LENGTH Ws ∧ LENGTH Ps = LENGTH Ws ∧
  varc wi (EL k Ps) = 1 ∧ (strct ∨ varc wi (EL k Ws) > 0) ⇒
  ¬SND (EL k (disj_task_info bnd name strct Ws Ps))
Proof
  rw[disj_task_info_def,EL_MAPi,EL_ZIP]>>
  Cases_on`EL k Ps`>>Cases_on`EL k Ws`>>
  gvs[pres_inactive_def,zsize_inactive_def,varc_def,
    integerTheory.INT_NOT_LE,integerTheory.int_gt]
QED

(* the [P = 0] atoms of the possibly-active tasks *)
Definition disj_pres_eqs_def:
  disj_pres_eqs bnd Ps ti =
  FLAT (MAP (λ(P,(l,inact)). if inact then [] else val_eq bnd F P) (ZIP (Ps,ti)))
End

Theorem MEM_disj_pres_eqs:
  LENGTH ti = LENGTH Ps ⇒
  (MEM e (disj_pres_eqs bnd Ps ti) ⇔
   ∃k. k < LENGTH Ps ∧ ¬SND (EL k ti) ∧ MEM e (val_eq bnd F (EL k Ps)))
Proof
  rw[disj_pres_eqs_def,MEM_FLAT,MEM_MAP,MEM_ZIP,PULL_EXISTS,pairTheory.UNCURRY]>>
  simp[COND_RAND]
QED

(* given the zero-width and [P = 0] rows, the escape literals of an active
   task hold iff it is absent or (non-strict) has zero width *)
Theorem disj_task_esc:
  valid_assignment bnd wi ∧ bit_faithful bnd wi wb ∧
  k < LENGTH Ws ∧ LENGTH Ps = LENGTH Ws ∧
  ¬SND (EL k (disj_task_info bnd name strct Ws Ps)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr
      (if strct then List []
       else
         mk_zero_links bnd name «zw»
           (ZIP (Ws,MAP SND (disj_task_info bnd name strct Ws Ps))))) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λ(X,v). encode_full_eq bnd X v)
      (disj_pres_eqs bnd Ps (disj_task_info bnd name strct Ws Ps)))) ⇒
  ((∃l. MEM l (FST (EL k (disj_task_info bnd name strct Ws Ps))) ∧ lit wb l) ⇔
   varc wi (EL k Ps) = 0 ∨ ¬strct ∧ varc wi (EL k Ws) ≤ 0)
Proof
  strip_tac>>
  drule_then (drule_then assume_tac) encode_full_eqs_sem_2>>
  `∀v. EL k Ps = INL v ∧ bnd v ≠ (0,1) ⇒
     (wb (INL (Eq (EL k Ps) 0)) ⇔ wi v = 0)` by (
    rw[]>>
    first_x_assum (qspecl_then[`INL v`,`0`]mp_tac)>>
    impl_tac >- (
      simp[MEM_disj_pres_eqs]>>
      qexists_tac`k`>>
      simp[val_eq_def])>>
    simp[varc_INL])>>
  `¬strct ⇒ ∀v. EL k Ws = INL v ⇒ (wb (disj_zero name «zw» k) ⇔ wi v ≤ 0)` by (
    rw[]>>
    gvs[mk_zero_links_sem]>>
    first_x_assum irule>>
    simp[EL_ZIP,EL_MAP])>>
  drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.INST [`b`|->`F`] val_lit_sem))>>
  gvs[disj_task_info_def,EL_MAPi,EL_ZIP]>>
  strip_tac>>
  simp[RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  Cases_on`EL k Ps`>>Cases_on`EL k Ws`>>
  gvs[pres_inactive_def,zsize_inactive_def,zsize_lit_def,varc_def,lit_def]>>
  Cases_on`strct`>>gvs[lit_def,DISJ_COMM]
QED

Definition cencode_disjunctive_rows_def:
  cencode_disjunctive_rows bnd Xs Ws strct name ti =
  let inactive = MAP SND ti in
  Append (mk_before_links bnd name «bf» (ZIP (ZIP (Xs,Ws),inactive)))
    (Append
      (if strct then List []
       else mk_zero_links bnd name «zw» (ZIP (Ws,inactive)))
      (mk_sep_clauses name [«bf»] ti))
End

(* Fewer than two possibly-active tasks: only the presence range rows. *)
Definition cencode_disjunctive_def:
  cencode_disjunctive bnd Xs Ws Ps strct name ec =
  if LENGTH Xs ≠ LENGTH Ws ∨ LENGTH Xs ≠ LENGTH Ps then (cfalse_constr,ec)
  else
    let ti = disj_task_info bnd name strct Ws Ps in
    let rng = mk_pres_range bnd name Ps in
    if LENGTH (FILTER (λt. ¬SND t) ti) < 2 then (rng,ec)
    else
      let (eqs,ec') = cencode_full_eqs bnd (disj_pres_eqs bnd Ps ti) ec in
      (Append rng
        (Append eqs (cencode_disjunctive_rows bnd Xs Ws strct name ti)),
       ec')
End

Definition encode_disjunctive_def:
  encode_disjunctive bnd Xs Ws Ps strct name =
  if LENGTH Xs ≠ LENGTH Ws ∨ LENGTH Xs ≠ LENGTH Ps then abstr cfalse_constr
  else
    let ti = disj_task_info bnd name strct Ws Ps in
    abstr (mk_pres_range bnd name Ps) ++
    if LENGTH (FILTER (λt. ¬SND t) ti) < 2 then []
    else
      FLAT (MAP (λ(X,v). encode_full_eq bnd X v) (disj_pres_eqs bnd Ps ti)) ++
      abstr (cencode_disjunctive_rows bnd Xs Ws strct name ti)
End

Theorem cencode_disjunctive_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive bnd Xs Ws Ps strct name ec = (es,ec') ⇒
  enc_rel wi es (encode_disjunctive bnd Xs Ws Ps strct name) ec ec'
Proof
  rw[cencode_disjunctive_def,encode_disjunctive_def]>>
  pairarg_tac>>gvs[]>>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  irule enc_rel_Append>>
  irule_at (Pos last) enc_rel_abstr>>
  irule enc_rel_cencode_full_eqs>>
  simp[]
QED

Theorem encode_disjunctive_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive Xs Ws Ps strct)) ∧
  disjunctive_sem Xs Ws Ps strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive bnd Xs Ws Ps strct name)
Proof
  rw[encode_disjunctive_def]>>
  gvs[disjunctive_sem_def,mk_pres_range_sem,encode_full_eqs_reify]>>
  simp[cencode_disjunctive_rows_def]>>
  PURE_REWRITE_TAC[GSYM CONJ_ASSOC]>>
  conj_tac
  >- (
    simp[mk_before_links_sem]>>
    rw[EL_ZIP,EL_MAP]>>
    gvs[reify_avar_def,reify_flag_def])>>
  CONJ_ASM1_TAC
  >- (
    rw[mk_zero_links_sem]>>
    gvs[EL_ZIP,EL_MAP,reify_avar_def,reify_flag_def,varc_def])>>
  simp[mk_sep_clauses_sem,UNCURRY,RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  rw[]>>
  DEP_REWRITE_TAC[disj_task_esc]>>
  simp[reify_avar_def,reify_flag_def,reify_reif_def,encode_full_eqs_reify]>>
  gvs[EVERY_EL,EL_MAP]>>
  qpat_x_assum`∀i j. _`(qspecl_then[`i`,`j`]mp_tac)>>
  qpat_assum`∀n. n < LENGTH Ps ⇒ _`(qspec_then`i`mp_tac)>>
  qpat_x_assum`∀n. n < LENGTH Ps ⇒ _`(qspec_then`j`mp_tac)>>
  Cases_on`strct`>>simp[EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_disjunctive_sem_2:
  valid_assignment bnd wi ∧
  bit_faithful bnd wi wb ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive bnd Xs Ws Ps strct name) ⇒
  disjunctive_sem Xs Ws Ps strct wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Ps` by (
    CCONTR_TAC>>
    gvs[encode_disjunctive_def,cfalse_constr_def])>>
  gvs[encode_disjunctive_def,mk_pres_range_sem]>>
  simp[disjunctive_sem_def]>>
  rw[]>>
  gvs[EL_MAP]>>
  qmatch_asmsub_abbrev_tac`FILTER _ ti`>>
  `¬SND (EL i ti) ∧ ¬SND (EL j ti) ∧ LENGTH ti = LENGTH Ws` by (
    simp[Abbr`ti`]>>
    metis_tac[disj_task_active])>>
  `¬(LENGTH (FILTER (λt. ¬SND t) ti) < 2)` by (
    simp[NOT_LESS,LENGTH_FILTER_two]>>
    metis_tac[])>>
  qunabbrev_tac`ti`>>
  gvs[cencode_disjunctive_rows_def,mk_before_links_sem,mk_sep_clauses_sem,
    UNCURRY,EL_ZIP,EL_MAP]>>
  qpat_x_assum`∀i j. _ ⇒ _ ⇒ _ ∨ ∃l. _`(qspecl_then[`i`,`j`]mp_tac)>>
  simp[RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  DEP_REWRITE_TAC[disj_task_esc]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* Disjunctive2D *)

(* a size that can never be positive: its declared upper bound is ≤ 0 *)
Definition zsize_ub_inactive_def:
  zsize_ub_inactive bnd s ⇔ SND (varc_bnd bnd s) ≤ 0
End

(* per rectangle: the escape literals of its separation clauses (zero width
   and zero height in non-strict mode; absence) and whether it is statically
   inactive *)
Definition disj2d_task_info_def:
  disj2d_task_info bnd name strct Ws Hs Ps =
  MAPi (λk (W,H,P).
    ((if strct then []
      else zsize_lit name «zw» k W ++ zsize_lit name «zh» k H) ++
     val_lit bnd F P,
     pres_inactive P ∨
     (¬strct ∧ (zsize_ub_inactive bnd W ∨ zsize_ub_inactive bnd H))))
    (ZIP (Ws,ZIP (Hs,Ps)))
End

Theorem LENGTH_disj2d_task_info[simp]:
  LENGTH (disj2d_task_info bnd name strct Ws Hs Ps) =
  MIN (LENGTH Ws) (MIN (LENGTH Hs) (LENGTH Ps))
Proof
  simp[disj2d_task_info_def,LENGTH_ZIP_MIN]
QED

(* a present rectangle that can conflict is not statically inactive *)
Theorem disj2d_task_active:
  valid_assignment bnd wi ∧
  k < LENGTH Ws ∧ LENGTH Hs = LENGTH Ws ∧ LENGTH Ps = LENGTH Ws ∧
  varc wi (EL k Ps) = 1 ∧
  (strct ∨ varc wi (EL k Ws) > 0 ∧ varc wi (EL k Hs) > 0) ⇒
  ¬SND (EL k (disj2d_task_info bnd name strct Ws Hs Ps))
Proof
  strip_tac>>
  drule_then (qspec_then`EL k Ws`assume_tac) varc_bnd_valid>>
  drule_then (qspec_then`EL k Hs`assume_tac) varc_bnd_valid>>
  simp[disj2d_task_info_def,EL_MAPi,EL_ZIP,zsize_ub_inactive_def]>>
  Cases_on`EL k Ps`>>gvs[pres_inactive_def,varc_def]>>
  disj2_tac>>
  intLib.ARITH_TAC
QED

(* given the zero-size and [P = 0] rows, the escape literals of an active
   rectangle hold iff it is absent or (non-strict) has a zero size *)
Theorem disj2d_task_esc:
  valid_assignment bnd wi ∧ bit_faithful bnd wi wb ∧
  k < LENGTH Ws ∧ LENGTH Hs = LENGTH Ws ∧ LENGTH Ps = LENGTH Ws ∧
  ¬SND (EL k (disj2d_task_info bnd name strct Ws Hs Ps)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr
      (if strct then List []
       else
         Append
           (mk_zero_links bnd name «zw»
             (ZIP (Ws,MAP SND (disj2d_task_info bnd name strct Ws Hs Ps))))
           (mk_zero_links bnd name «zh»
             (ZIP (Hs,MAP SND (disj2d_task_info bnd name strct Ws Hs Ps)))))) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λ(X,v). encode_full_eq bnd X v)
      (disj_pres_eqs bnd Ps (disj2d_task_info bnd name strct Ws Hs Ps)))) ⇒
  ((∃l. MEM l (FST (EL k (disj2d_task_info bnd name strct Ws Hs Ps))) ∧
     lit wb l) ⇔
   varc wi (EL k Ps) = 0 ∨
   ¬strct ∧ (varc wi (EL k Ws) ≤ 0 ∨ varc wi (EL k Hs) ≤ 0))
Proof
  strip_tac>>
  drule_then (drule_then assume_tac) encode_full_eqs_sem_2>>
  `∀v. EL k Ps = INL v ∧ bnd v ≠ (0,1) ⇒
     (wb (INL (Eq (EL k Ps) 0)) ⇔ wi v = 0)` by (
    rw[]>>
    first_x_assum (qspecl_then[`INL v`,`0`]mp_tac)>>
    impl_tac >- (
      simp[MEM_disj_pres_eqs]>>
      qexists_tac`k`>>
      simp[val_eq_def])>>
    simp[varc_INL])>>
  `¬strct ⇒
   (∀v. EL k Ws = INL v ⇒ (wb (disj_zero name «zw» k) ⇔ wi v ≤ 0)) ∧
   (∀v. EL k Hs = INL v ⇒ (wb (disj_zero name «zh» k) ⇔ wi v ≤ 0))` by (
    rw[]>>
    gvs[mk_zero_links_sem]>>
    first_x_assum irule>>
    simp[EL_ZIP,EL_MAP])>>
  drule_all (PURE_REWRITE_RULE [COND_CLAUSES] (Q.INST [`b`|->`F`] val_lit_sem))>>
  rpt (qpat_x_assum`EVERY _ _`kall_tac)>>
  qpat_x_assum`∀X v. _`kall_tac>>
  gvs[disj2d_task_info_def,EL_MAPi,EL_ZIP]>>
  strip_tac>>
  simp[RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  Cases_on`EL k Ps`>>Cases_on`EL k Ws`>>Cases_on`EL k Hs`>>
  gvs[pres_inactive_def,zsize_ub_inactive_def,varc_bnd_def,zsize_lit_def,
    varc_def,lit_def]>>
  Cases_on`strct`>>
  gvs[lit_def,RIGHT_AND_OVER_OR,EXISTS_OR_THM,AC DISJ_ASSOC DISJ_COMM]
QED

Definition cencode_disjunctive2d_rows_def:
  cencode_disjunctive2d_rows bnd Xs Ys Ws Hs strct name ti =
  let inactive = MAP SND ti in
  Append (mk_before_links bnd name «bx» (ZIP (ZIP (Xs,Ws),inactive)))
    (Append (mk_before_links bnd name «by» (ZIP (ZIP (Ys,Hs),inactive)))
      (Append
        (if strct then List []
         else
           Append (mk_zero_links bnd name «zw» (ZIP (Ws,inactive)))
             (mk_zero_links bnd name «zh» (ZIP (Hs,inactive))))
        (mk_sep_clauses name [«bx»;«by»] ti)))
End

(* Fewer than two possibly-active rectangles: only the presence range rows. *)
Definition cencode_disjunctive2d_def:
  cencode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name ec =
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys ∨ n ≠ LENGTH Ws ∨ n ≠ LENGTH Hs ∨ n ≠ LENGTH Ps
  then (cfalse_constr,ec)
  else
    let ti = disj2d_task_info bnd name strct Ws Hs Ps in
    let rng = mk_pres_range bnd name Ps in
    if LENGTH (FILTER (λt. ¬SND t) ti) < 2 then (rng,ec)
    else
      let (eqs,ec') = cencode_full_eqs bnd (disj_pres_eqs bnd Ps ti) ec in
      (Append rng
        (Append eqs (cencode_disjunctive2d_rows bnd Xs Ys Ws Hs strct name ti)),
       ec')
End

Definition encode_disjunctive2d_def:
  encode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name =
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys ∨ n ≠ LENGTH Ws ∨ n ≠ LENGTH Hs ∨ n ≠ LENGTH Ps
  then abstr cfalse_constr
  else
    let ti = disj2d_task_info bnd name strct Ws Hs Ps in
    abstr (mk_pres_range bnd name Ps) ++
    if LENGTH (FILTER (λt. ¬SND t) ti) < 2 then []
    else
      FLAT (MAP (λ(X,v). encode_full_eq bnd X v) (disj_pres_eqs bnd Ps ti)) ++
      abstr (cencode_disjunctive2d_rows bnd Xs Ys Ws Hs strct name ti)
End

Theorem cencode_disjunctive2d_sem:
  valid_assignment bnd wi ∧
  cencode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name ec = (es,ec') ⇒
  enc_rel wi es (encode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name) ec ec'
Proof
  rw[cencode_disjunctive2d_def,encode_disjunctive2d_def]>>
  pairarg_tac>>gvs[]>>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  irule enc_rel_Append>>
  irule_at (Pos last) enc_rel_abstr>>
  irule enc_rel_cencode_full_eqs>>
  simp[]
QED

Theorem encode_disjunctive2d_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Scheduling (Disjunctive2D Xs Ys Ws Hs Ps strct)) ∧
  disjunctive2d_sem Xs Ys Ws Hs Ps strct wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name)
Proof
  rw[encode_disjunctive2d_def]>>
  gvs[disjunctive2d_sem_def,mk_pres_range_sem,encode_full_eqs_reify]>>
  simp[cencode_disjunctive2d_rows_def]>>
  PURE_REWRITE_TAC[GSYM CONJ_ASSOC]>>
  conj_tac
  >- (
    simp[mk_before_links_sem]>>
    rw[EL_ZIP,EL_MAP]>>
    gvs[reify_avar_def,reify_flag_def])>>
  conj_tac
  >- (
    simp[mk_before_links_sem]>>
    rw[EL_ZIP,EL_MAP]>>
    gvs[reify_avar_def,reify_flag_def])>>
  CONJ_ASM1_TAC
  >- (
    rw[mk_zero_links_sem]>>
    gvs[EL_ZIP,EL_MAP,reify_avar_def,reify_flag_def,varc_def])>>
  simp[mk_sep_clauses_sem,UNCURRY,RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  rw[]>>
  DEP_REWRITE_TAC[disj2d_task_esc]>>
  simp[reify_avar_def,reify_flag_def,reify_reif_def,encode_full_eqs_reify]>>
  gvs[EVERY_EL,EL_MAP]>>
  qpat_x_assum`∀i j. _`(qspecl_then[`i`,`j`]mp_tac)>>
  qpat_assum`∀n. n < LENGTH Ps ⇒ _`(qspec_then`i`mp_tac)>>
  qpat_x_assum`∀n. n < LENGTH Ps ⇒ _`(qspec_then`j`mp_tac)>>
  Cases_on`strct`>>simp[EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_disjunctive2d_sem_2:
  valid_assignment bnd wi ∧
  bit_faithful bnd wi wb ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name) ⇒
  disjunctive2d_sem Xs Ys Ws Hs Ps strct wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ys ∧ LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs ∧
   LENGTH Xs = LENGTH Ps` by (
    CCONTR_TAC>>
    gvs[encode_disjunctive2d_def,cfalse_constr_def])>>
  gvs[encode_disjunctive2d_def,mk_pres_range_sem]>>
  simp[disjunctive2d_sem_def]>>
  rw[]>>
  gvs[EL_MAP]>>
  qmatch_asmsub_abbrev_tac`FILTER _ ti`>>
  `¬SND (EL i ti) ∧ ¬SND (EL j ti) ∧ LENGTH ti = LENGTH Ws` by (
    simp[Abbr`ti`]>>
    metis_tac[disj2d_task_active])>>
  `¬(LENGTH (FILTER (λt. ¬SND t) ti) < 2)` by (
    simp[NOT_LESS,LENGTH_FILTER_two]>>
    metis_tac[])>>
  qunabbrev_tac`ti`>>
  gvs[cencode_disjunctive2d_rows_def,mk_before_links_sem,mk_sep_clauses_sem,
    UNCURRY,EL_ZIP,EL_MAP]>>
  qpat_x_assum`∀i j. _ ⇒ _ ⇒ _ ∨ ∃l. _`(qspecl_then[`i`,`j`]mp_tac)>>
  simp[RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  DEP_REWRITE_TAC[disj2d_task_esc]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* Cumulative: start-checkpoint encoding.  For every ordered pair (i,j) of
   active tasks, i ≠ j, three fully reified flags pin
     sb(i,j) ⇔ s_i ≤ s_j,   sa(i,j) ⇔ s_i + l_i ≥ s_j + 1,
     sact(i,j) ⇔ sb ∧ sa ∧ [P_i = 1]
   so sact(i,j) holds exactly when task i is present and running when task j
   starts, and one row per active task j bounds the load at its start by the
   capacity.  A task whose length or height has a non-positive upper bound, or
   whose presence is a constant other than 1, never loads the resource; it
   contributes nothing and gets no flags.  A task of constant length and
   constant presence is running at its own start, so its own height goes to
   the row's right-hand side (constant) or integer side (variable); otherwise
   the task gets the diagonal flag sact(j,j) ⇔ l_j ≥ 1 ∧ [P_j = 1] instead.
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
  cumul_task_active bnd w h p ⇔
  0 < SND (varc_bnd bnd w) ∧ 0 < SND (varc_bnd bnd h) ∧ ¬pres_inactive p
End

(* pair flags for contributor i and checkpoint j, i ≠ j; pl is i's presence
   literal (none for a constant presence) *)
Definition cumul_pair_def:
  cumul_pair bnd name i x_i w_i pl j x_j =
  Append (cbimply_var bnd (cumul_sb name i j) (mk_le x_i x_j))
  (Append (cbimply_var bnd (cumul_sa name i j)
            (mk_lin_constraint_ge [(1,x_i);(1,w_i);(-1,x_j)] 1))
    (cbimply_var bnd (cumul_sact name i j)
      ([],[(1,Pos (cumul_sb name i j));(1,Pos (cumul_sa name i j))] ++
          MAP (λl. (1,l)) pl,
       2 + &LENGTH pl)))
End

(* the diagonal flag sact(j,j) ⇔ l_j ≥ 1 ∧ [P_j = 1]; pl is j's presence
   literal.  A variable length: l_j + ub(l_j)·[P_j = 1] ≥ 1 + ub(l_j) (just
   l_j ≥ 1 without a presence literal); a constant length (≥ 1 for an active
   task): [P_j = 1] ≥ 1, and no flag without a presence literal. *)
Definition cumul_diag_def:
  cumul_diag bnd name j w_j pl =
  case w_j of
    INL wv =>
      (let ub = SND (bnd wv) in
       cbimply_var bnd (cumul_sact name j j)
         ([(1,wv)],MAP (λl. (ub,l)) pl,1 + ub * &LENGTH pl))
  | INR c =>
      if NULL pl then Nil
      else
        cbimply_var bnd (cumul_sact name j j)
          ([],MAP (λl. (1,l)) pl,&LENGTH pl)
End

(* the diagonal rows pin sact(j,j) to "running at its own start and present"
   whenever they define it *)
Theorem cumul_diag_sem:
  valid_assignment bnd wi ∧ LENGTH pl ≤ 1 ∧ 0 < SND (varc_bnd bnd w) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cumul_diag bnd name j w pl)) ⇔
   (ISL w ∨ ¬NULL pl ⇒
    (wb (cumul_sact name j j) ⇔ 1 ≤ varc wi w ∧ EVERY (lit wb) pl)))
Proof
  strip_tac>>
  drule_then (qspec_then`w`strip_assume_tac) varc_bnd_valid>>
  `pl = [] ∨ ∃l. pl = [l]` by (Cases_on`pl`>>gvs[]>>Cases_on`t`>>gvs[])>>
  gvs[]>>
  Cases_on`w`>>
  gvs[cumul_diag_def,varc_bnd_def,varc_def,iconstraint_sem_def,
    eval_ilin_term_def,iSUM_def,lit_def]>>
  Cases_on`wb (INR (name,Values [&j; &j] (SOME «sact»)))`>>
  Cases_on`lit wb l`>>
  gvs[pbc_encodeTheory.b2i_alt]>>
  intLib.ARITH_TAC
QED

(* the bit width of a height (unused for a constant) *)
Definition cumul_hw_def:
  cumul_hw bnd h =
  case h of
    INL hv => bit_width bnd hv
  | INR c => (F,0n)
End

(* the active tasks from index k on, as (i,x,w,h,p,cumul_hw bnd h) *)
Definition cumul_active_def:
  (cumul_active bnd (k:num) [] = []) ∧
  (cumul_active bnd k ((x,w,h,p)::ts) =
    let rest = cumul_active bnd (k + 1) ts in
    if cumul_task_active bnd w h p
    then (k,x,w,h,p,cumul_hw bnd h)::rest
    else rest)
End

Theorem FLAT_MAP_cumul_active:
  ∀ts k f.
  FLAT (MAP f (cumul_active bnd k ts)) =
  FLAT (MAPi (λi (x,w,h,p).
    if cumul_task_active bnd w h p
    then f (i + k,x,w,h,p,cumul_hw bnd h)
    else []) ts)
Proof
  Induct>>simp[cumul_active_def]>>
  qx_gen_tac`t`>>PairCases_on`t`>>rpt gen_tac>>
  pop_assum (fn ih =>
    rw[cumul_active_def,indexedListsTheory.MAPi_def,combinTheory.o_DEF,ADD1,ih])>>
  `∀i. k + (i + 1) = i + (k + 1)` by simp[]>>
  asm_rewrite_tac[]
QED

(* the load term of contributor i at checkpoint j; hw = cumul_hw bnd h *)
Definition cumul_contrib_def:
  cumul_contrib name i j h hw =
  case h of
    INR c => [(c, Pos (cumul_sact name i j))]
  | INL hv =>
    let (comp,w) = hw in
    let bits = pos_num (cumul_scc name i j) w in
    if comp then (-&(2**w), Pos (cumul_sccs name i j)) :: bits else bits
End

(* scc(i,j,k) ⇔ sact(i,j) ∧ bit_k(h), and the sign analogue;
   hw = cumul_hw bnd h *)
Definition cumul_gate_def:
  cumul_gate bnd name i j h hw =
  case h of
    INR c => Nil
  | INL hv =>
    let (comp,w) = hw in
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

(* checkpoint row of active task j:  Σ_i contrib(i,j) + own height ≤ cap,
   over the active tasks act; j's own height is unconditional when j has no
   diagonal flag (constant length, constant presence) *)
Definition cumul_scap_row_def:
  cumul_scap_row name act cap j w_j h_j p_j =
  let loadbs = FLAT (MAP (λ(i,x,w,h,p,hw).
      if i ≠ j ∨ ISL w ∨ ISL p then cumul_contrib name i j h hw else [])
      act) in
  let (dis,dfix) =
      if ISL w_j ∨ ISL p_j then ([],0i)
      else (case h_j of INL hv => ([(-1i,hv)],0i) | INR c => ([],c)) in
  let (cis,rhs) =
      (case cap of INL v => ([(1i,v)],dfix) | INR c => ([],dfix - c)) in
  List [(SOME (mk_name name («scap_» ^ toString j)),
         (cis ++ dis, flip_coeffs loadbs, rhs))]
End

(* capacity ≥ 0 and each height ≥ 0; rows the declared bounds imply are omitted *)
Definition cumul_nonneg_def:
  cumul_nonneg bnd name tasks cap =
  Append (cmk_lb bnd (mk_name name «cap_ge0») cap 0)
    (flat_app (MAPi (λi (x,w,h,p).
       cmk_lb bnd (mk_name name («h_» ^ toString i ^ «_ge0»)) h 0) tasks))
End

Theorem cumul_nonneg_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cumul_nonneg bnd name tasks cap)) ⇔
   0 ≤ varc wi cap ∧ EVERY (λ(x,w,h,p). 0 ≤ varc wi h) tasks)
Proof
  strip_tac>>
  simp[cumul_nonneg_def,append_thm,cmk_lb_sem,EVERY_FLAT]>>
  simp[Once EVERY_EL]>>
  simp[indexedListsTheory.EL_MAPi,pairTheory.ELIM_UNCURRY,cmk_lb_sem]>>
  simp[EVERY_EL]
QED

(* the flag and checkpoint rows over the tasks (x,w,h,p) *)
Definition cencode_cumulative_rows_def:
  cencode_cumulative_rows bnd name tasks cap =
  let act = cumul_active bnd 0 tasks in
  Append (cumul_nonneg bnd name tasks cap)
  (flat_app (MAP (λ(j,x_j,w_j,h_j,p_j,hw_j).
     Append
       (flat_app (MAP (λ(i,x_i,w_i,h_i,p_i,hw_i).
          if i = j then
            (if ISL w_j ∨ ISL p_j then
               Append (cumul_diag bnd name j w_j (val_lit bnd T p_j))
                 (cumul_gate bnd name j j h_j hw_j)
             else Nil)
          else
            Append (cumul_pair bnd name i x_i w_i (val_lit bnd T p_i) j x_j)
                   (cumul_gate bnd name i j h_i hw_i)) act))
       (cumul_scap_row name act cap j w_j h_j p_j)) act))
End

(* the [P = 1] atoms of the active tasks *)
Definition cumul_pres_eqs_def:
  cumul_pres_eqs bnd tasks =
  FLAT (MAP (λ(x,w,h,p).
    if cumul_task_active bnd w h p then val_eq bnd T p else []) tasks)
End

Theorem MEM_cumul_pres_eqs:
  MEM e (cumul_pres_eqs bnd tasks) ⇔
  ∃x w h p. MEM (x,w,h,p) tasks ∧ cumul_task_active bnd w h p ∧
    MEM e (val_eq bnd T p)
Proof
  simp[cumul_pres_eqs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,pairTheory.EXISTS_PROD]>>
  simp[COND_RAND]
QED

Definition cencode_cumulative_def:
  cencode_cumulative bnd Xs Ws Hs Ps cap name ec =
  if LENGTH Xs ≠ LENGTH Ws ∨ LENGTH Xs ≠ LENGTH Hs ∨ LENGTH Xs ≠ LENGTH Ps
  then (cfalse_constr,ec)
  else
    let tasks = ZIP (Xs,ZIP (Ws,ZIP (Hs,Ps))) in
    let (eqs,ec') = cencode_full_eqs bnd (cumul_pres_eqs bnd tasks) ec in
    (Append (mk_pres_range bnd name Ps)
      (Append eqs (cencode_cumulative_rows bnd name tasks cap)),
     ec')
End

(* every task pair, skipping the inactive ones *)
Theorem cencode_cumulative_rows_ACTIVE:
  append (cencode_cumulative_rows bnd name tasks cap) =
  append (
    Append (cumul_nonneg bnd name tasks cap)
    (flat_app (MAPi (λj (x_j,w_j,h_j,p_j).
       if ¬cumul_task_active bnd w_j h_j p_j then Nil
       else
         Append
           (flat_app (MAPi (λi (x_i,w_i,h_i,p_i).
              if ¬cumul_task_active bnd w_i h_i p_i then Nil
              else if i = j then
                (if ISL w_j ∨ ISL p_j then
                   Append (cumul_diag bnd name j w_j (val_lit bnd T p_j))
                     (cumul_gate bnd name j j h_j (cumul_hw bnd h_j))
                 else Nil)
              else
                Append
                  (cumul_pair bnd name i x_i w_i (val_lit bnd T p_i) j x_j)
                  (cumul_gate bnd name i j h_i (cumul_hw bnd h_i))) tasks))
           (cumul_scap_row name (cumul_active bnd 0 tasks) cap j w_j h_j p_j))
       tasks)))
Proof
  rw[cencode_cumulative_rows_def,append_thm,append_flat_app,MAP_MAP_o,
     FLAT_MAP_cumul_active,indexedListsTheory.MAP_MAPi]>>
  AP_TERM_TAC>>irule indexedListsTheory.MAPi_CONG>>simp[]>>
  qx_genl_tac[`t`,`j`]>>strip_tac>>PairCases_on`t`>>
  simp[append_thm,append_flat_app,indexedListsTheory.MAP_MAPi]>>
  IF_CASES_TAC>>simp[append_thm,append_flat_app,indexedListsTheory.MAP_MAPi]>>
  AP_TERM_TAC>>
  irule indexedListsTheory.MAPi_CONG>>simp[]>>
  qx_genl_tac[`s`,`i`]>>strip_tac>>PairCases_on`s`>>
  rw[append_thm]
QED

Definition encode_cumulative_def:
  encode_cumulative bnd Xs Ws Hs Ps cap name =
  if LENGTH Xs ≠ LENGTH Ws ∨ LENGTH Xs ≠ LENGTH Hs ∨ LENGTH Xs ≠ LENGTH Ps
  then abstr cfalse_constr
  else
    let tasks = ZIP (Xs,ZIP (Ws,ZIP (Hs,Ps))) in
    abstr (mk_pres_range bnd name Ps) ++
    FLAT (MAP (λ(X,v). encode_full_eq bnd X v) (cumul_pres_eqs bnd tasks)) ++
    abstr (cencode_cumulative_rows bnd name tasks cap)
End

Theorem cencode_cumulative_sem:
  valid_assignment bnd wi ∧
  cencode_cumulative bnd Xs Ws Hs Ps cap name ec = (es,ec') ⇒
  enc_rel wi es (encode_cumulative bnd Xs Ws Hs Ps cap name) ec ec'
Proof
  rw[cencode_cumulative_def,encode_cumulative_def]>>
  pairarg_tac>>gvs[]>>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  irule enc_rel_Append>>
  irule_at (Pos last) enc_rel_abstr>>
  irule enc_rel_cencode_full_eqs>>
  simp[]
QED

(* a sum of literals with coefficient 1 is at most their number, and reaches
   it exactly when every literal holds *)
Theorem eval_lin_term_ones:
  ∀ls. eval_lin_term wb (MAP (λl. (1,l)) ls) ≤ &LENGTH ls ∧
    (&LENGTH ls ≤ eval_lin_term wb (MAP (λl. (1,l)) ls) ⇔ EVERY (lit wb) ls)
Proof
  Induct>>rw[]>>
  Cases_on`lit wb h`>>
  gvs[integerTheory.INT,
    intLib.ARITH_PROVE``∀a b:int. a + 1 ≤ 1 + b ⇔ a ≤ b``]>>
  intLib.ARITH_TAC
QED

Theorem cumul_pair_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
     (abstr (cumul_pair bnd name i x_i w_i pl j x_j)) ⇔
   (wb (cumul_sb name i j) ⇔ varc wi x_i ≤ varc wi x_j) ∧
   (wb (cumul_sa name i j) ⇔ varc wi x_i + varc wi w_i ≥ varc wi x_j + 1) ∧
   (wb (cumul_sact name i j) ⇔
      wb (cumul_sb name i j) ∧ wb (cumul_sa name i j) ∧ EVERY (lit wb) pl))
Proof
  strip_tac>>
  simp[cumul_pair_def,append_thm,abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,
       lit_def,eval_iclin_term_def,iSUM_def]>>
  simp[intLib.ARITH_PROVE ``∀a b:int. a + -1 * b ≥ 0 ⇔ b ≤ a``,
       intLib.ARITH_PROVE ``∀a b c:int. a + (b + -1 * c) ≥ 1 ⇔ a + b ≥ c + 1``]>>
  `∀a b. b2i a + (b2i b + eval_lin_term wb (MAP (λl. (1,l)) pl)) ≥
     2 + &LENGTH pl ⇔
   a ∧ b ∧ &LENGTH pl ≤ eval_lin_term wb (MAP (λl. (1,l)) pl)` by (
    qspec_then`pl`(assume_tac o CONJUNCT1) eval_lin_term_ones>>
    rw[]>>Cases_on`a`>>Cases_on`b`>>simp[pbc_encodeTheory.b2i_alt]>>
    intLib.ARITH_TAC)>>
  qspec_then`pl`strip_assume_tac eval_lin_term_ones>>
  simp[]>>
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
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cumul_gate bnd name i j h (cumul_hw bnd h))) ⇒
  eval_lin_term wb (cumul_contrib name i j h (cumul_hw bnd h)) =
  if wb (cumul_sact name i j) then varc wi h else 0
Proof
  strip_tac>>
  Cases_on`h`>>gvs[cumul_gate_def,cumul_contrib_def,cumul_hw_def]
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
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs Ps cap)) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  eval_lin_term (reify_avar cs wi)
    (cumul_contrib name i j (EL i Hs) (cumul_hw bnd (EL i Hs))) =
  if varc wi (EL i Xs) ≤ varc wi (EL j Xs) ∧
     varc wi (EL i Xs) + varc wi (EL i Ws) ≥ varc wi (EL j Xs) + 1 ∧
     varc wi (EL i Ps) = 1
  then varc wi (EL i Hs) else 0
Proof
  strip_tac>>
  Cases_on`EL i Hs`>>
  gvs[cumul_contrib_def,cumul_hw_def,reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT,
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
    Cases_on`varc wi (EL i Ps) = 1`>>gvs[num_of_bits_GENLIST_F]>>
    IF_CASES_TAC>>gvs[num_of_bits_GENLIST_F])>>
  rw[varc_def]
QED

Theorem eval_lin_term_FLAT_MAPi_if[local]:
  ∀ls g P. eval_lin_term wb
    (FLAT (MAPi (λi (x,w,h,p). if P i x w h p then g i x w h p else []) ls)) =
  iSUM (MAPi (λi (x,w,h,p).
    if P i x w h p then eval_lin_term wb (g i x w h p) else 0) ls)
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
    (abstr (cumul_scap_row name (cumul_active bnd 0 tasks) cap j w_j h_j p_j)) ⇔
  iSUM (MAPi (λi (x,w,h,p).
    if cumul_task_active bnd w h p ∧ (i ≠ j ∨ ISL w ∨ ISL p)
    then eval_lin_term wb (cumul_contrib name i j h (cumul_hw bnd h)) else 0) tasks) +
  (if ISL w_j ∨ ISL p_j then 0 else varc wi h_j) ≤ varc wi cap
Proof
  `∀B X. eval_lin_term wb (if B then X else []) =
     if B then eval_lin_term wb X else 0` by rw[eval_lin_term_NIL]>>
  `∀A B (e:int). (if A then if B then e else 0 else 0) = if A ∧ B then e else 0` by
    (Cases_on`A`>>simp[])>>
  simp[cumul_scap_row_def,FLAT_MAP_cumul_active]>>
  Cases_on`cap`>>Cases_on`w_j`>>Cases_on`h_j`>>Cases_on`p_j`>>
  gvs[iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def,
      eval_lin_term_FLAT_MAPi_if]>>
  rpt (pop_assum kall_tac)>>
  qmatch_goalsub_abbrev_tac`iSUM ld`>>
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
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs Ps cap)) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (cumul_gate bnd name i j (EL i Hs) (cumul_hw bnd (EL i Hs))))
Proof
  strip_tac>>
  Cases_on`EL i Hs`>>gvs[cumul_gate_def,cumul_hw_def]>>
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
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs Ps cap)) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ∧ ¬pres_inactive (EL i Ps) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (cumul_pair bnd name i (EL i Xs) (EL i Ws)
       (val_lit bnd T (EL i Ps)) j (EL j Xs)))
Proof
  strip_tac>>
  simp[cumul_pair_sem]>>
  DEP_REWRITE_TAC[val_lit_T_every]>>
  simp[reify_avar_def,reify_reif_def,reify_flag_def,integerTheory.NUM_OF_INT,
    varc_INL]
QED

Theorem cumul_diag_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs (name:mlstring) = SOME (Scheduling (Cumulative Xs Ws Hs Ps cap)) ∧
  j < LENGTH Xs ∧ j < LENGTH Ws ∧ j < LENGTH Hs ∧ j < LENGTH Ps ∧
  cumul_task_active bnd (EL j Ws) (EL j Hs) (EL j Ps) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr (cumul_diag bnd name j (EL j Ws) (val_lit bnd T (EL j Ps))))
Proof
  strip_tac>>
  gvs[cumul_task_active_def]>>
  DEP_REWRITE_TAC[cumul_diag_sem]>>
  simp[]>>
  DEP_REWRITE_TAC[val_lit_T_every]>>
  simp[reify_avar_def,reify_reif_def,reify_flag_def,integerTheory.NUM_OF_INT,
    varc_INL]>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* a task that cannot be active never loads the resource *)
Theorem cumul_inactive_zero:
  valid_assignment bnd wi ∧ ¬cumul_task_active bnd w h p ∧ 0 ≤ varc wi h ⇒
  (if varc wi x ≤ t ∧ t < varc wi x + varc wi w ∧ varc wi p = 1
   then varc wi h else 0) = 0
Proof
  strip_tac>>
  `varc wi w ≤ SND (varc_bnd bnd w) ∧ varc wi h ≤ SND (varc_bnd bnd h)` by
    metis_tac[varc_bnd_valid]>>
  gvs[cumul_task_active_def]>>rw[]>>
  Cases_on`p`>>gvs[pres_inactive_def,varc_def]>>
  rpt (qpat_x_assum`valid_assignment _ _`kall_tac)>>
  intLib.ARITH_TAC
QED

Theorem MAPi_ZIP4_GENLIST[local]:
  LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs ∧ LENGTH Xs = LENGTH Ps ⇒
  MAPi f (ZIP (Xs,ZIP (Ws,ZIP (Hs,Ps)))) =
  GENLIST (λi. f i (EL i Xs,EL i Ws,EL i Hs,EL i Ps)) (LENGTH Xs)
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
  ALOOKUP cs name = SOME (Scheduling (Cumulative Xs Ws Hs Ps cap)) ∧
  cumulative_sem Xs Ws Hs Ps cap wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_cumulative bnd Xs Ws Hs Ps cap name)
Proof
  rw[]>>
  `LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs ∧ LENGTH Xs = LENGTH Ps` by
    fs[cumulative_sem_def]>>
  simp[encode_cumulative_def,mk_pres_range_sem,encode_full_eqs_reify]>>
  conj_tac >- fs[cumulative_sem_def]>>
  simp[cencode_cumulative_rows_ACTIVE,append_thm,EVERY_APPEND]>>
  conj_tac
  >- (
    simp[cumul_nonneg_sem]>>
    fs[cumulative_sem_def,EVERY_EL,EL_MAP]>>
    simp[EVERY_EL,LENGTH_ZIP,EL_ZIP,EL_MAP])>>
  simp[abstr_flat_app,MAPi_ZIP4_GENLIST,MAP_GENLIST,EVERY_FLAT,EVERY_GENLIST,
       combinTheory.o_DEF]>>
  qx_gen_tac`j`>>strip_tac>>
  IF_CASES_TAC>>simp[append_thm]>>
  conj_tac
  >- (
    simp[MAP_GENLIST,combinTheory.o_DEF,EVERY_FLAT,EVERY_GENLIST]>>
    rw[append_thm,EVERY_APPEND]>>
    metis_tac[cumul_gate_reify,cumul_diag_reify,cumul_pair_reify,
      cumul_task_active_def])>>
  simp[cumul_scap_row_sem,MAPi_ZIP4_GENLIST]>>
  qpat_x_assum`cumulative_sem _ _ _ _ _ _`mp_tac>>
  simp[cumulative_sem_def]>>strip_tac>>
  first_x_assum(qspec_then`varc wi (EL j Xs)`mp_tac)>>
  simp[EL_MAP]>>strip_tac>>
  irule integerTheory.INT_LE_TRANS>>
  first_x_assum (irule_at Any)>>
  irule iSUM_GENLIST_le_add>>
  qexists`j`>>
  `∀i. i < LENGTH Hs ⇒ 0 ≤ varc wi (EL i Hs)` by gvs[EVERY_EL,EL_MAP]>>
  drule_then (drule_then assume_tac) cumul_contrib_reify>>
  simp[EL_MAP,
    intLib.ARITH_PROVE ``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``]>>
  rw[]>>gvs[]>>
  Cases_on`EL j Ws`>>Cases_on`EL j Ps`>>
  gvs[cumul_task_active_def,pres_inactive_def,varc_bnd_def,varc_def]
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
    (encode_cumulative bnd Xs Ws Hs Ps cap name) ⇒
  cumulative_sem Xs Ws Hs Ps cap wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ws ∧ LENGTH Xs = LENGTH Hs ∧ LENGTH Xs = LENGTH Ps` by
    (CCONTR_TAC>>gvs[encode_cumulative_def,cfalse_constr_def])>>
  gvs[encode_cumulative_def,cencode_cumulative_rows_ACTIVE,append_thm,
      EVERY_APPEND,mk_pres_range_sem]>>
  drule_then (drule_then assume_tac) encode_full_eqs_sem_2>>
  `0 ≤ varc wi cap ∧
   EVERY (λ(x,w,h,p). 0 ≤ varc wi h) (ZIP (Xs,ZIP (Ws,ZIP (Hs,Ps))))` by
    (qpat_x_assum`EVERY _ (abstr (cumul_nonneg _ _ _ _))`mp_tac>>
     simp[cumul_nonneg_sem])>>
  `∀j. j < LENGTH Hs ⇒ 0 ≤ varc wi (EL j Hs)` by
    (gvs[EVERY_EL,LENGTH_ZIP]>>rw[]>>first_x_assum drule>>simp[EL_ZIP])>>
  `∀i. i < LENGTH Ps ∧ cumul_task_active bnd (EL i Ws) (EL i Hs) (EL i Ps) ⇒
     (EVERY (lit wb) (val_lit bnd T (EL i Ps)) ⇔ varc wi (EL i Ps) = 1)` by (
    rw[]>>
    irule val_lit_T_every>>
    simp[]>>
    reverse conj_tac >- fs[cumul_task_active_def]>>
    rw[]>>
    first_x_assum (qspecl_then[`INL v`,`1`]mp_tac)>>
    impl_tac >- (
      simp[MEM_cumul_pres_eqs]>>
      qexistsl_tac[`EL i Xs`,`EL i Ws`,`EL i Hs`,`EL i Ps`]>>
      simp[val_eq_def,MEM_EL]>>
      qexists_tac`i`>>simp[EL_ZIP])>>
    simp[varc_INL])>>
  `∀j. j < LENGTH Hs ∧ cumul_task_active bnd (EL j Ws) (EL j Hs) (EL j Ps) ⇒
     iSUM (GENLIST (λi.
       if varc wi (EL i Xs) ≤ varc wi (EL j Xs) ∧
          varc wi (EL j Xs) < varc wi (EL i Xs) + varc wi (EL i Ws) ∧
          varc wi (EL i Ps) = 1
       then varc wi (EL i Hs) else 0) (LENGTH Hs)) ≤ varc wi cap` by (
    qpat_x_assum`EVERY _ (FLAT (MAPi _ _))`mp_tac>>
    simp[MAPi_ZIP4_GENLIST,MAP_GENLIST,EVERY_FLAT,EVERY_GENLIST,
         combinTheory.o_DEF]>>
    strip_tac>>
    rw[]>>
    qpat_x_assum`∀j. j < _ ⇒ EVERY _ _`(qspec_then`j`mp_tac)>>
    simp[append_thm,EVERY_APPEND,cumul_scap_row_sem,MAPi_ZIP4_GENLIST]>>
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
      qpat_x_assum`∀i'. i' < _ ⇒ EVERY _ _`(qspec_then`i`mp_tac)>>
      simp[]>>
      Cases_on`cumul_task_active bnd (EL i Ws) (EL i Hs) (EL i Ps)`>>simp[]
      >- (
        simp[cumul_pair_sem]>>strip_tac>>
        drule_all cumul_gate_sem>>
        simp[intLib.ARITH_PROVE ``∀a b t:int. (a + b ≥ t + 1) ⇔ (t < a + b)``])>>
      sg`(if varc wi (EL i Xs) ≤ varc wi (EL j Xs) ∧
           varc wi (EL j Xs) < varc wi (EL i Xs) + varc wi (EL i Ws) ∧
           varc wi (EL i Ps) = 1
        then varc wi (EL i Hs) else 0) = 0`
      >- (
        irule cumul_inactive_zero>>
        simp[]>>
        qexists_tac`bnd`>>
        simp[])>>
      simp[])>>
    qpat_x_assum`∀i'. i' < _ ⇒ EVERY _ _`(qspec_then`j`mp_tac)>>
    simp[]>>
    Cases_on`ISL (EL j Ws) ∨ ISL (EL j Ps)`>>simp[]
    >- (
      simp[append_thm,EVERY_APPEND]>>strip_tac>>
      drule_all cumul_gate_sem>>strip_tac>>
      `0 < SND (varc_bnd bnd (EL j Ws))` by fs[cumul_task_active_def]>>
      qpat_x_assum`EVERY _ (abstr (cumul_diag _ _ _ _ _))`mp_tac>>
      DEP_REWRITE_TAC[cumul_diag_sem]>>
      simp[intLib.ARITH_PROVE ``∀x:int. 1 ≤ x ⇔ 0 < x``])>>
    Cases_on`EL j Ws`>>Cases_on`EL j Ps`>>
    gvs[cumul_task_active_def,pres_inactive_def,varc_bnd_def,varc_def])>>
  simp[cumulative_sem_def]>>
  conj_tac >- simp[EVERY_MAP,EVERY_EL]>>
  simp[Cong GENLIST_CONG,EL_MAP]>>
  `∀s. GENLIST (λi.
         if varc wi (EL i Xs) ≤ s ∧ s < varc wi (EL i Xs) + varc wi (EL i Ws) ∧
            varc wi (EL i Ps) = 1
         then varc wi (EL i Hs) else 0) (LENGTH Hs) =
       GENLIST (λi.
         if EL i (MAP (varc wi) Xs) ≤ s ∧
            s < EL i (MAP (varc wi) Xs) + EL i (MAP (varc wi) Ws)
         then EL i (GENLIST (λi. if varc wi (EL i Ps) = 1 then varc wi (EL i Hs)
                                 else 0) (LENGTH Hs))
         else 0) (LENGTH Hs)` by (
    rw[GENLIST_FUN_EQ,EL_MAP]>>
    Cases_on`varc wi (EL i Ps) = 1`>>simp[])>>
  pop_assum (fn eq =>
    qpat_x_assum`∀j. _ ∧ _ ⇒ iSUM _ ≤ _`(assume_tac o REWRITE_RULE[eq])>>
    REWRITE_TAC[eq])>>
  gen_tac>>
  qmatch_goalsub_abbrev_tac`iSUM ld ≤ _`>>
  Cases_on`iSUM ld ≤ 0`
  >- (
    irule integerTheory.INT_LE_TRANS>>
    qexists`0`>>
    simp[])>>
  qunabbrev_tac`ld`>>
  qspecl_then [`MAP (varc wi) Xs`,`MAP (varc wi) Ws`,
    `GENLIST (λi. if varc wi (EL i Ps) = 1 then varc wi (EL i Hs) else 0)
       (LENGTH Hs)`,`LENGTH Hs`]
    mp_tac (Q.GENL [`ss`,`ls`,`hs`,`n`] cumul_load_at_start)>>
  impl_tac
  >- (
    fs[integerTheory.INT_NOT_LE,EVERY_GENLIST]>>
    rw[])>>
  strip_tac>>
  gvs[EL_MAP]>>
  Cases_on`varc wi (EL j Ps) = 1`>>gvs[]>>
  irule integerTheory.INT_LE_TRANS>>
  first_assum (irule_at Any)>>
  qpat_x_assum`∀j. _ ∧ _ ⇒ iSUM _ ≤ _`irule>>
  simp[cumul_task_active_def]>>
  rpt conj_tac
  >- metis_tac[varc_bnd_valid,integerTheory.INT_LTE_TRANS]
  >- metis_tac[varc_bnd_valid,integerTheory.INT_LTE_TRANS]>>
  Cases_on`EL j Ps`>>gvs[pres_inactive_def,varc_def]
QED

Definition encode_scheduling_constr_def:
  encode_scheduling_constr bnd c name =
  case c of
    Disjunctive Xs Ws Ps strct =>
      encode_disjunctive bnd Xs Ws Ps strct name
  | Disjunctive2D Xs Ys Ws Hs Ps strct =>
      encode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name
  | Cumulative Xs Ws Hs Ps cap =>
      encode_cumulative bnd Xs Ws Hs Ps cap name
End

Definition cencode_scheduling_constr_def:
  cencode_scheduling_constr bnd c name ec =
  case c of
    Disjunctive Xs Ws Ps strct =>
      cencode_disjunctive bnd Xs Ws Ps strct name ec
  | Disjunctive2D Xs Ys Ws Hs Ps strct =>
      cencode_disjunctive2d bnd Xs Ys Ws Hs Ps strct name ec
  | Cumulative Xs Ws Hs Ps cap =>
      cencode_cumulative bnd Xs Ws Hs Ps cap name ec
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
