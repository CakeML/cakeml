open preamble;

val _ = new_theory "parmove";

(* TODO: why isn't this inherited from miscTheory? *)
val _ = ParseExtras.temp_tight_equality();

(* TODO: move *)

val NULL_APPEND = Q.store_thm("NULL_APPEND[simp]",
  `NULL (l1 ++ l2) ⇔ NULL l1 ∧ NULL l2`,
  simp[NULL_LENGTH]);

(* -- *)

(* This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
     Tilting at windmills with Coq: formal verification of a compilation
     algorithm for parallel moves
   http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)

(* Non-deterministic algorithm *)

(* The state is three lists of moves:
   (to-process, being-processed, processed)
   each step (roughly) shifts some move from left to right in the state *)

(* NONE is a temporary register; real registers are SOME x. *)

val _ = temp_overload_on("NoRead",``λμ dn. ¬MEM dn (MAP FST μ)``);

fun replace_quote from to (QUOTE s) = QUOTE(replace_string from to s)
  | replace_quote _ _ x = x

val _ = add_infix("step",450,NONASSOC);

val (step_rules,step_ind,step_cases) = (Hol_reln o List.map(replace_quote "\226\150\183" "step"))`
  ((μ1++[(r,r)]++μ2,σ,τ) ▷ (μ1++μ2,σ,τ)) ∧
  ((μ1++[(s,d)]++μ2,[],τ) ▷ (μ1++μ2,[(s,d)],τ)) ∧
  ((μ1++[(d,r)]++μ2,[(s,d)]++σ,τ) ▷ (μ1++μ2,[(d,r);(s,d)]++σ,τ)) ∧
  ((μ,σ++[(s,d)],τ) ▷ (μ,σ++[(NONE,d)],[(s,NONE)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(sn,dn)]++σ++[(s0,d0)],τ) ▷ (μ,σ++[(s0,d0)],[(sn,dn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(s,d)],τ) ▷ (μ,[],[(s,d)]++τ))`;

val _ = Unicode.uset_fixity"\226\150\183"(Infix(NONASSOC,450));
val _ = Unicode.uoverload_on("\226\150\183",``$step``);
val _ = add_infix("\226\150\183*",450,NONASSOC);
val _ = overload_on("\226\150\183*",``RTC $▷``);

(* invariant on states *)

val windmill_def = Define `
  windmill (moves:('a # 'a) list) = ALL_DISTINCT (MAP SND moves)`;

val windmill_cons = Q.store_thm("windmill_cons",
  `windmill (x::ls) ⇔ ¬MEM (SND x) (MAP SND ls) ∧ windmill ls`,
  rw[windmill_def])

val path_def = Define`
  (path [] ⇔ T) ∧ (path [_] ⇔ T) ∧
  (path ((b',c)::(a,b)::p) ⇔
     (b = b') ∧ path ((a,b)::p))`;
val _ = export_rewrites["path_def"];

val path_change_start = Q.store_thm("path_change_start",
  `∀y z x. path (SNOC x y) ∧ SND x = SND z ⇒ path (SNOC z y)`,
  simp[SNOC_APPEND] >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases_on`y`>>fs[] >- (
    Cases >> Cases >> simp[] >> rw[] ) >>
  Cases_on`h`>>simp[] >> rw[] >> metis_tac[])

val path_tail = Q.store_thm("path_tail",
  `∀t h. path (h::t) ⇒ path t`,
  Induct >> simp[] >>
  Cases >> Cases >> simp[])

val path_imp_mem = Q.prove(
  `path (x::y) ⇒
   ¬NULL y ⇒ MEM (FST x) (MAP SND y)`,
  Induct_on`y`>>simp[]>>
  Cases_on`x`>>Cases>>fs[])

val path_imp_mem2 = Q.prove(
  `path x ⇒
   ∀y. MEM y (MAP FST x) ∧
       y ≠ FST(LAST x) ⇒
       MEM y (MAP SND x)`,
  Induct_on`x` >> simp[]>>
  Cases_on`x`>>Cases>>simp[]>>
  Cases_on`h`>>fs[] >>
  strip_tac >> fs[] >>
  rw[] >> metis_tac[])

val NoRead_path = Q.prove(
  `∀σ. path σ ∧ windmill σ ∧ LENGTH σ ≥ 2 ∧
   SND (HD σ) ≠ FST (LAST σ) ⇒
   NoRead (TL σ) (SND (HD σ))`,
  Induct >> simp[] >> Cases >> simp[] >>
  Cases_on`σ`>>fs[]>> Cases_on`h`>>fs[]>>
  strip_tac >> var_eq_tac >> fs[] >>
  fs[windmill_def] >>
  fsrw_tac[ARITH_ss][ADD1] >>
  imp_res_tac path_imp_mem >>
  Cases_on`NULL t`>-( Cases_on`t`>>fs[] ) >> fs[] >>
  conj_asm1_tac >- metis_tac[] >>
  strip_tac >>
  imp_res_tac path_imp_mem2 >>
  fs[] >> metis_tac[] )

val wf_def = Define`
  wf (μ,σ,τ) ⇔
    windmill (μ++σ) ∧
    EVERY IS_SOME (MAP FST μ) ∧
    EVERY IS_SOME (MAP SND μ) ∧
    (¬NULL σ ⇒ EVERY IS_SOME (MAP FST (FRONT σ))) ∧
    EVERY IS_SOME (MAP SND σ) ∧
    path σ`;
val _ = Unicode.uoverload_on(UnicodeChars.turnstile,``wf``);

val wf_init = Q.store_thm("wf_init",
  `windmill μ ∧
   EVERY IS_SOME (MAP FST μ) ∧
   EVERY IS_SOME (MAP SND μ) ⇒
   ⊢ (μ,[],[])`,
  rw[wf_def,path_def])

(* The invariant is preserved *)

val wf_step = Q.store_thm("wf_step",
  `∀s1 s2. s1 ▷ s2 ⇒ ⊢ s1 ⇒ ⊢ s2`,
  ho_match_mp_tac step_ind >> rw[] >>
  fs[wf_def,windmill_def,ALL_DISTINCT_APPEND] >>
  fs[GSYM SNOC_APPEND,FRONT_DEF] >>
  TRY (match_mp_tac path_change_start) >>
  metis_tac[SND,path_tail]);

val wf_steps = Q.store_thm("wf_steps",
  `∀s1 s2. ⊢ s1 ∧ s1 ▷* s2 ⇒ ⊢ s2`,
  ho_match_mp_tac RTC_lifts_invariants >>
  metis_tac[wf_step])

(* semantics of moves *)

val parsem_def = Define`
  parsem μ ρ = ρ =++ (ZIP(MAP SND μ, MAP (ρ o FST) μ))`;

val parsem_nil = Q.store_thm("parsem_nil[simp]",
  `parsem [] = I`,
  rw[parsem_def,FUN_EQ_THM,UPDATE_LIST_THM]);

val parsem_cons = Q.store_thm("parsem_cons",
  `¬MEM y (MAP SND μ) ⇒
   parsem ((x,y)::μ) ρ = (y =+ ρ x) (parsem μ ρ)`,
  rw[parsem_def,UPDATE_LIST_THM] >>
  simp[FUN_EQ_THM,APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[] >> BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,MEM_ZIP,FORALL_PROD] >>
  rw[] >> fs[MEM_EL,EL_MAP] >> metis_tac[PAIR,SND]);

val independence = Q.store_thm("independence",
  `∀μ1 s d μ2 μ.
      windmill μ ∧ μ = μ1 ++ [(s,d)] ++ μ2 ⇒
      parsem μ = parsem ([(s,d)]++μ1++μ2)`,
  Induct >> simp[] >> Cases >> rw[] >>
  full_simp_tac std_ss [windmill_cons] >>
  simp[parsem_cons,FUN_EQ_THM] >>
  `¬MEM d (MAP SND ((q,r)::(μ1 ++ μ2)))` by (
    fs[windmill_def,ALL_DISTINCT_APPEND] ) >>
  simp[parsem_cons] >>
  full_simp_tac std_ss [MAP,MEM] >>
  `¬MEM r (MAP SND (μ1 ++ μ2))` by fs[] >>
  simp[parsem_cons,APPLY_UPDATE_THM] >> rw[]);

val parsem_perm = Q.store_thm("parsem_perm",
  `windmill l1 ∧ PERM l1 l2 ⇒ parsem l1 = parsem l2`,
  rw[] >>
  Q.ISPEC_THEN`λl. if windmill l then parsem l else ARB`mp_tac
    PERM_lifts_equalities >>
  simp[] >>
  discharge_hyps >- (
    rpt (pop_assum kall_tac) >>
    rw[] >- (
      Induct_on`x2` >> simp[] >>
      Cases >> rw[] >>
      last_x_assum mp_tac >>
      simp[AND_IMP_INTRO] >>
      discharge_hyps >- (
        fs[windmill_def,ALL_DISTINCT_APPEND] >>
        metis_tac[] ) >>
      strip_tac >>
      REWRITE_TAC[Once CONS_APPEND] >> simp[] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once CONS_APPEND])) >> simp[] >>
      match_mp_tac EQ_TRANS >>
      qexists_tac`parsem ([(q,r)]++x1++x2++x3)` >>
      conj_tac >- (
        CONV_TAC(PATH_CONV"rr"(REWR_CONV (GSYM APPEND_ASSOC))) >>
        match_mp_tac independence >> simp[] >>
        metis_tac[CONS_APPEND,APPEND_ASSOC] ) >>
      match_mp_tac EQ_TRANS >>
      qexists_tac`parsem ([(q,r)]++x1++x3++x2)` >>
      conj_tac >- (
        simp[GSYM CONS_APPEND] >>
        `¬MEM r (MAP SND (x1++x2++x3)) ∧
         ¬MEM r (MAP SND (x1++x3++x2))` by (
          fs[windmill_def,ALL_DISTINCT_APPEND] >>
          metis_tac[] ) >>
        metis_tac[parsem_cons] ) >>
      match_mp_tac EQ_SYM >>
      CONV_TAC(PATH_CONV"rrlr"(REWR_CONV (GSYM APPEND_ASSOC))) >>
      match_mp_tac independence >> simp[] >>
      metis_tac[CONS_APPEND,APPEND_ASSOC]) >>
    fs[windmill_def] >>
    metis_tac[PERM_APPEND,APPEND_ASSOC,PERM_APPEND_IFF,ALL_DISTINCT_PERM]) >>
  `windmill l2` by metis_tac[windmill_def,ALL_DISTINCT_PERM,PERM_MAP] >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[])

val parsem_untouched = Q.store_thm("parsem_untouched",
  `∀ρ μ x. windmill μ ∧ ¬MEM x (MAP SND μ) ⇒ parsem μ ρ x = ρ x`,
  gen_tac >> Induct >> simp[] >>
  Cases >> rw[] >>
  `¬MEM r (MAP SND μ)` by fs[windmill_def] >>
  simp[parsem_cons,APPLY_UPDATE_THM] >>
  first_x_assum match_mp_tac >>
  fs[windmill_def])

val parsem_change_env = Q.store_thm("parsem_change_env",
  `(¬MEM x (MAP SND μ) ⇒ ρ1 x = ρ2 x) ∧
   MAP (ρ1 o FST) μ = MAP (ρ2 o FST) μ ⇒
   parsem μ ρ1 x = parsem μ ρ2 x`,
  rw[parsem_def,APPLY_UPDATE_LIST_ALOOKUP] >>
  BasicProvers.CASE_TAC >> first_x_assum match_mp_tac >>
  imp_res_tac ALOOKUP_FAILS >>
  fs[MEM_MAP,FORALL_PROD,MEM_ZIP,MEM_EL] >>
  metis_tac[EL_MAP,SND])

val parsem_NoRead = Q.store_thm("parsem_NoRead",
  `NoRead μ y ⇒
   parsem ((x,y)::μ) ρ = parsem μ ((y =+ ρ x) ρ)`,
  rw[parsem_def,APPLY_UPDATE_LIST_ALOOKUP,FUN_EQ_THM,ALOOKUP_APPEND,APPLY_UPDATE_THM,REVERSE_ZIP] >>
  simp[GSYM MAP_REVERSE,ALOOKUP_ZIP_MAP_SND] >>
  qpat_abbrev_tac`z = ALOOKUP X Y` >>
  Cases_on`z`>>rw[APPLY_UPDATE_THM] >>
  fs[markerTheory.Abbrev_def] >>
  pop_assum(assume_tac o SYM) >>
  imp_res_tac ALOOKUP_MEM >>
  qmatch_assum_rename_tac`NoRead μ (FST p)` >>
  Cases_on`p`>>fs[]>>
  fs[MAP_REVERSE,GSYM REVERSE_ZIP] >>
  fs[MEM_ZIP,MEM_MAP,MEM_EL,EXISTS_PROD] >>
  metis_tac[])

val seqsem_def = Define`
  (seqsem [] ρ = ρ) ∧
  (seqsem ((s,d)::τ) ρ = seqsem τ ((d =+ ρ s) ρ))`;

val seqsem_append = Q.store_thm("seqsem_append",
  `∀l1 l2. seqsem (l1 ++ l2) = seqsem l2 o seqsem l1`,
  Induct >> fs[FUN_EQ_THM,seqsem_def] >> Cases >> simp[seqsem_def])

(* semantics of the state *)

val sem_def = Define`
  sem (μ,σ,τ) ρ = parsem (μ++σ) (seqsem (REVERSE τ) ρ)`;

val sem_init = Q.store_thm("sem_init",
  `sem (μ,[],[]) = parsem μ`,
  rw[FUN_EQ_THM,sem_def,seqsem_def])

val sem_final = Q.store_thm("sem_final",
  `sem ([],[],τ) = seqsem (REVERSE τ)`,
  rw[sem_def,FUN_EQ_THM,parsem_def,UPDATE_LIST_THM])

(* semantic preservation *)

val eqenv_def = Define`
  eqenv ρ1 ρ2 ⇔ ∀r. IS_SOME r ⇒ (ρ1 r = ρ2 r)`;
val _ = Unicode.uset_fixity"\226\137\161"(Infix(NONASSOC,450));
val _ = Unicode.uoverload_on("\226\137\161",``eqenv``);

val eqenv_sym = Q.prove(
  `p1 ≡ p2 ⇒ p2 ≡ p1`, rw[eqenv_def]);

val step_sem = Q.prove(
  `∀s1 s2. s1 ▷ s2 ⇒ ⊢ s1 ⇒ (∀ρ. sem s1 ρ ≡ sem s2 ρ)`,
  ho_match_mp_tac step_ind >>
  conj_tac >- (
    rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >> rpt (AP_THM_TAC) >>
    match_mp_tac EQ_TRANS >>
    qexists_tac`parsem((r,r)::(μ1++μ2++σ))` >>
    conj_tac >- (
      match_mp_tac parsem_perm >> simp[] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once CONS_APPEND])) >>
      REWRITE_TAC[APPEND_ASSOC,PERM_APPEND_IFF,PERM_APPEND] ) >>
    `¬MEM r (MAP SND (μ1++μ2++σ))` by
      (fs[windmill_def,ALL_DISTINCT_APPEND]>>metis_tac[]) >>
    simp[parsem_cons,FUN_EQ_THM,APPLY_UPDATE_THM] >> rw[] >>
    match_mp_tac (GSYM parsem_untouched) >>
    fs[windmill_def,ALL_DISTINCT_APPEND] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >> rpt AP_THM_TAC >>
    match_mp_tac parsem_perm >>
    metis_tac[PERM_APPEND,PERM_APPEND_IFF,APPEND_ASSOC] ) >>
  conj_tac >- (
    rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >> rpt AP_THM_TAC >>
    match_mp_tac parsem_perm >>
    simp[PERM_APPEND_IFF] >>
    CONV_TAC(PATH_CONV"rr"(REWR_CONV(CONS_APPEND))) >>
    metis_tac[PERM_APPEND,PERM_APPEND_IFF,APPEND_ASSOC] ) >>
  conj_tac >- (
    rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >>
    `∀s. parsem (μ ++ σ ++ [(s,d)]) = parsem ((s,d)::(μ++σ))` by (
      gen_tac >> match_mp_tac parsem_perm >> simp[] >> fs[windmill_def] >>
      metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF] ) >>
    `¬MEM d (MAP SND (μ++σ))` by fs[windmill_def,ALL_DISTINCT_APPEND] >>
    simp[parsem_cons,APPLY_UPDATE_THM] >>
    rw[seqsem_append,seqsem_def,APPLY_UPDATE_THM] >>
    fs[GSYM SNOC_APPEND] >>
    match_mp_tac parsem_change_env >>
    simp[MAP_EQ_f,APPLY_UPDATE_THM] >>
    rw[] >> fs[EVERY_MAP] >> fs[EVERY_MEM] >>
    metis_tac[IS_SOME_DEF] ) >>
  conj_tac >- (
    rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >>
    `parsem (μ ++ [(sn,dn)] ++ σ ++ [(s0,d0)]) =
     parsem ((s0,d0)::((sn,dn)::(μ ++ σ)))` by (
      match_mp_tac parsem_perm >> simp[] >>
      match_mp_tac PERM_TRANS >>
      metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF]) >>
    pop_assum (SUBST1_TAC) >>
    `parsem (μ ++ σ ++ [(s0,d0)]) =
     parsem ((s0,d0)::(μ++σ))` by (
      match_mp_tac parsem_perm >> fs[windmill_def,ALL_DISTINCT_APPEND] >>
      metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF]) >>
    pop_assum (SUBST1_TAC) >>
    `¬MEM d0 (MAP SND (μ++σ)) ∧ ¬MEM d0 (MAP SND ((sn,dn)::(μ++σ)))` by (
      fs[windmill_def,ALL_DISTINCT_APPEND] ) >>
    simp[parsem_cons,APPLY_UPDATE_THM] >>
    rw[seqsem_append,seqsem_def,APPLY_UPDATE_THM] >>
    AP_THM_TAC >>
    match_mp_tac parsem_NoRead >>
    fs[] >>
    imp_res_tac NoRead_path >>
    fsrw_tac[ARITH_ss][ADD1] >> rfs[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    fs[windmill_def,ALL_DISTINCT_APPEND] >>
    simp[LAST_DEF] ) >>
  rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >>
  `parsem (μ ++ [(s,d)]) = parsem ((s,d)::μ)` by (
     match_mp_tac parsem_perm >> simp[] >>
     metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF]) >>
  pop_assum (SUBST1_TAC) >>
  simp[seqsem_append,seqsem_def,APPLY_UPDATE_THM] >>
  AP_THM_TAC >>
  match_mp_tac parsem_NoRead >>
  rw[]);

val steps_sem = Q.store_thm("steps_sem",
  `∀s1 s2. s1 ▷* s2 ∧ ⊢ s1 ⇒ (∀ρ. sem s1 ρ ≡ sem s2 ρ)`,
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_INDUCT >>
  conj_tac >- simp[eqenv_def] >>
  rw[] >>
  imp_res_tac wf_step >> fs[] >>
  imp_res_tac step_sem >>
  fs[eqenv_def] );

val steps_correct = Q.store_thm("steps_correct",
  `windmill μ ∧
   EVERY IS_SOME (MAP FST μ) ∧
   EVERY IS_SOME (MAP SND μ) ∧
   (μ,[],[]) ▷* ([],[],τ)
   ⇒
   ∀ρ. parsem μ ρ ≡ seqsem (REVERSE τ) ρ`,
  rw[] >>
  imp_res_tac steps_sem >>
  pop_assum mp_tac >>
  discharge_hyps >- simp[wf_def] >>
  simp[sem_def,seqsem_def]);

(* deterministic algorithm *)

val _ = add_infix("dstep",450,NONASSOC);

val (dstep_rules,dstep_ind,dstep_cases) = (Hol_reln o List.map(replace_quote "\226\134\170" "dstep"))`
  (([(r,r)]++μ,[],τ) ↪ (μ,[],τ)) ∧
  (s ≠ d ⇒
   ([(s,d)]++μ,[],τ) ↪ (μ,[(s,d)],τ)) ∧
  (NoRead μ1 d ⇒
   (μ1++[(d,r)]++μ2,[(s,d)]++σ,τ) ↪
   (μ1++μ2,[(d,r);(s,d)]++σ,τ)) ∧
  (NoRead μ r ⇒
   (μ,[(s,r)]++σ++[(r,d)],τ) ↪
   (μ,σ++[(NONE,d)],[(s,r);(r,NONE)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(sn,dn)]++σ++[(s0,d0)],τ) ↪
   (μ,σ++[(s0,d0)],[(sn,dn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(s,d)],τ) ↪ (μ,[],[(s,d)]++τ))`;

val _ = Unicode.uset_fixity"\226\134\170"(Infix(NONASSOC,450));
val _ = Unicode.uoverload_on("\226\134\170",``$dstep``);
val _ = add_infix("\226\134\170*",450,NONASSOC);
val _ = overload_on("\226\134\170*",``RTC $↪``);

(* ⊢ s1 condition not included in paper;
   not sure if necessary, but couldn't get
   their proof to work *)
val dstep_step = Q.prove(
  `∀s1 s2. s1 ↪ s2 ⇒ ⊢ s1 ⇒ s1 ▷* s2`,
  ho_match_mp_tac dstep_ind >> rw[] >>
  TRY(
    qpat_abbrev_tac`n = NONE` >>
    rw[Once RTC_CASES1,Abbr`n`] >>
    fs[wf_def] >>
    `r ≠ NONE` by (strip_tac >> fs[]) >>
    srw_tac[DNF_ss][step_cases]) >>
  match_mp_tac RTC_SUBSET >> rw[step_cases] >>
  metis_tac[CONS_APPEND,APPEND] );

val dsteps_steps = Q.store_thm("dsteps_steps",
  `∀s1 s2. s1 ↪* s2 ⇒ ⊢ s1 ⇒ s1 ▷* s2`,
  ho_match_mp_tac RTC_INDUCT >> rw[] >>
  metis_tac[dstep_step,wf_steps,RTC_CASES_RTC_TWICE])

(* functional algorithm *)

val fstep_def = Define`
  fstep st =
  case st of
  | ([],[],_) => st
  | ((s,d)::t,[],l) =>
    if s = d
    then (t,[],l)
    else (t,[(s,d)],l)
  | (t,(s,d)::b,l) =>
    splitAtPki (λi p. FST p = d)
      (λt1 rt2.
        case rt2 of
        | (dr::t2) => (t1++t2,dr::(s,d)::b,l)
        | [] => if NULL b then (t,[],(s,d)::l) else
                let (b',(s',d')) = (FRONT b,LAST b) in
                if s' = d
                then (t,SNOC (NONE,d') b',(s,d)::(d,NONE)::l)
                else (t,b,(s,d)::l))
      t`;

val not_or = METIS_PROVE[]``¬a ∨ b ⇔ a ⇒ b``;

val tac =
  simp[UNCURRY] >> rw[] >- (
      rw[dstep_cases] >>
      qexists_tac`[]` >> simp[] )
  >> (
  rw[splitAtPki_EQN] >>
  BasicProvers.CASE_TAC >- (
      rw[dstep_cases] >>
      TRY(map_every qexists_tac[`SND(LAST t')`,`FST(LAST t')`,`FRONT t'`]) >>
      rw[APPEND_FRONT_LAST] >>
      fs[whileTheory.OLEAST_def,MEM_MAP,MEM_EL] >>
      metis_tac[] ) >>
  fs[whileTheory.OLEAST_def] >>
  BasicProvers.CASE_TAC >- (
      fs[DROP_NIL] >> rw[] >>
      pop_assum mp_tac >>
      numLib.LEAST_ELIM_TAC >>
      conj_tac >- metis_tac[] >>
      rw[] >> decide_tac ) >>
  rw[dstep_cases] >>
  pop_assum mp_tac >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >> Cases_on`h`>>fs[] >>
  rfs[DROP_CONS_EL] >> fs[] >>
  qpat_abbrev_tac`qq = (q,_)` >>
  qexists_tac`qq::(TAKE n t)` >>
  simp[Abbr`qq`] >> rpt var_eq_tac >>
  conj_tac >- (
      qspec_then`SUC n`(CONV_TAC o LAND_CONV o REWR_CONV o GSYM)TAKE_DROP >>
      simp[ADD1] >>
      simp[TAKE_EL_SNOC] ) >>
  simp[MEM_MAP] >>
  simp[not_or] >>
  Cases >> rw[] >>
  simp[MEM_EL,not_or,EL_TAKE] >>
  rpt strip_tac >>
  res_tac >> fsrw_tac[ARITH_ss][] >>
  metis_tac[FST,PAIR])

val fstep_dstep = Q.prove(
  `(∀τ. s ≠ ([],[],τ)) ⇒ s ↪ fstep s`,
  rw[fstep_def] >>
  every_case_tac >> fs[NULL_LENGTH,LENGTH_NIL] >>
  simp[splitAtPki_DEF]
  >- ( simp[UNCURRY] >> simp[dstep_cases] )
  >- (
    simp[UNCURRY] >> rw[] >>
    simp[dstep_cases] >-
      metis_tac[APPEND_FRONT_LAST] >>
    Q.ISPEC_THEN`t`FULL_STRUCT_CASES_TAC SNOC_CASES >> fs[] >>
    Cases_on`x`>>fs[] )
  >> TRY (rw[dstep_cases]>>NO_TAC)
  >> tac)

val pmov_def = tDefine"pmov"`
  pmov s = case s of
    | ([],[],_) => s
    | _ => pmov (fstep s)`
  (WF_REL_TAC`measure (λ(μ,σ,τ). 2 * LENGTH μ + LENGTH σ)` >>
   rw[fstep_def] >- (
     fs[NULL_LENGTH,LENGTH_NIL,splitAtPki_DEF] >>
     simp[UNCURRY] >> rw[] >>
     simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL] )
   >- (
     simp[splitAtPki_DEF,UNCURRY] >>
     rw[] >> simp[] >>
     fs[NULL_LENGTH,LENGTH_NIL] >>
     simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL] )
   >> (
     every_case_tac >> simp[splitAtPki_DEF,UNCURRY] >>
     rw[] >> simp[splitAtPki_DEF,UNCURRY] >>
     simp[splitAtPki_EQN] >>
     every_case_tac >> simp[] >>
     TRY (
       fs[NULL_LENGTH,LENGTH_NIL] >>
       simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL] >>
       NO_TAC) >>
     fs[whileTheory.OLEAST_def] >> rw[] >>
     pop_assum mp_tac >>
     numLib.LEAST_ELIM_TAC >>
     conj_tac >- metis_tac[] >>
     rw[] >> simp[LENGTH_TAKE,ADD1] >>
     rfs[DROP_CONS_EL] >> rw[] >>
     simp[ADD1] >>
     metis_tac[]))

val pmov_ind = theorem"pmov_ind";

val pmov_dsteps = Q.prove(
  `∀s. s ↪* pmov s`,
  ho_match_mp_tac pmov_ind >>
  rw[] >> PairCases_on`s` >>
  ONCE_REWRITE_TAC[pmov_def] >>
  every_case_tac >> simp[] >> rw[] >> fs[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  match_mp_tac fstep_dstep >> simp[])

val pmov_final = Q.prove(
  `∀s. ∃τ. pmov s = ([],[],τ)`,
  ho_match_mp_tac pmov_ind >>
  rw[] >> PairCases_on`s` >>
  ONCE_REWRITE_TAC[pmov_def] >>
  every_case_tac >> simp[]);

(* The top-level parallel move compiler *)

val parmove_def = Define `
  parmove (xs:('a # 'a) list) =
    REVERSE(SND(SND(pmov (MAP (\(x,y). (SOME x, SOME y)) xs, [],[]))))`;

val parmove_correct = Q.store_thm("parmove_correct",
  `windmill xs ⇒
   ∀ρ. seqsem (parmove xs) ρ ≡
       parsem (MAP (\(x,y). (SOME x, SOME y)) xs) ρ`,
  rw[parmove_def] >>
  qpat_abbrev_tac`μ = MAP _ xs` >>
  `∃τ. pmov (μ,[],[]) = ([],[],τ)` by metis_tac[pmov_final] >>
  simp[] >>
  `(μ,[],[]) ↪* ([],[],τ)` by metis_tac[pmov_dsteps] >>
  imp_res_tac dsteps_steps >>
  pop_assum mp_tac >>
  discharge_hyps_keep >- (
    match_mp_tac wf_init >>
    simp[Abbr`μ`,EVERY_MAP,UNCURRY] >>
    fs[windmill_def] >>
    simp[MAP_MAP_o,o_DEF,UNCURRY] >>
    simp[GSYM MAP_MAP_o,GSYM o_DEF] >>
    match_mp_tac ALL_DISTINCT_MAP_INJ >>
    simp[] ) >>
  strip_tac >>
  match_mp_tac eqenv_sym >>
  match_mp_tac steps_correct >>
  fs[wf_def]);

val _ = export_theory();
