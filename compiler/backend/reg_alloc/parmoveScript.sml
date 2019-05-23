(*
  Compiling parallel moves.
  This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
    Tilting at windmills with Coq: formal verification of a compilation
    algorithm for parallel moves
  http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf
*)
open preamble;

val _ = new_theory "parmove";

(* Non-deterministic algorithm *)

(* The state is three lists of moves:
   (to-process, being-processed, processed)
   each step (roughly) shifts some move from left to right in the state *)

(* NONE is a temporary register; real registers are SOME x. *)

val _ = temp_overload_on("NoRead",``λμ dn. ¬MEM dn (MAP SND μ)``);

fun replace_quote from to (QUOTE s) = QUOTE(Portable.replace_string {from=from,to=to} s)
  | replace_quote _ _ x = x

val _ = add_infix("step",450,NONASSOC);

val (step_rules,step_ind,step_cases) = (Hol_reln o List.map(replace_quote "\226\150\183" "step"))`
  ((μ1++[(r,r)]++μ2,σ,τ) ▷ (μ1++μ2,σ,τ)) ∧
  ((μ1++[(d,s)]++μ2,[],τ) ▷ (μ1++μ2,[(d,s)],τ)) ∧
  ((μ1++[(r,d)]++μ2,[(d,s)]++σ,τ) ▷ (μ1++μ2,[(r,d);(d,s)]++σ,τ)) ∧
  ((μ,σ++[(d,s)],τ) ▷ (μ,σ++[(d,NONE)],[(NONE,s)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(dn,sn)]++σ++[(d0,s0)],τ) ▷ (μ,σ++[(d0,s0)],[(dn,sn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(d,s)],τ) ▷ (μ,[],[(d,s)]++τ))`;

val _ = set_fixity"\226\150\183"(Infix(NONASSOC,450));
val _ = overload_on("\226\150\183",``$step``);

val _ = set_fixity "\226\150\183*" (Infix(NONASSOC,450));
val _ = overload_on("\226\150\183*",``RTC $▷``);

(* invariant on states *)

val windmill_def = Define `
  windmill (moves:('a # 'a) list) = ALL_DISTINCT (MAP FST moves)`;

Theorem windmill_cons:
   windmill (x::ls) ⇔ ¬MEM (FST x) (MAP FST ls) ∧ windmill ls
Proof
  rw[windmill_def]
QED

val path_def = Define`
  (path [] ⇔ T) ∧ (path [_] ⇔ T) ∧
  (path ((c,b')::(b,a)::p) ⇔
     (b = b') ∧ path ((b,a)::p))`;
val _ = export_rewrites["path_def"];

Theorem path_change_start:
   ∀y z x. path (SNOC x y) ∧ FST x = FST z ⇒ path (SNOC z y)
Proof
  simp[SNOC_APPEND] >>
  Induct >> simp[] >>
  Cases >> simp[] >>
  Cases_on`y`>>fs[] >- (
    Cases >> Cases >> simp[] >> rw[] ) >>
  Cases_on`h`>>simp[] >> rw[] >> metis_tac[]
QED

Theorem path_tail:
   ∀t h. path (h::t) ⇒ path t
Proof
  Induct >> simp[] >>
  Cases >> Cases >> simp[]
QED

val path_imp_mem = Q.prove(
  `path (x::y) ⇒
   ¬NULL y ⇒ MEM (SND x) (MAP FST y)`,
  Induct_on`y`>>simp[]>>
  Cases_on`x`>>Cases>>fs[])

val path_imp_mem2 = Q.prove(
  `path x ⇒
   ∀y. MEM y (MAP SND x) ∧
       y ≠ SND(LAST x) ⇒
       MEM y (MAP FST x)`,
  Induct_on`x` >> simp[]>>
  Cases_on`x`>>Cases>>simp[]>>
  Cases_on`h`>>fs[] >>
  strip_tac >> fs[] >>
  rw[] >> metis_tac[])

val NoRead_path = Q.prove(
  `∀σ. path σ ∧ windmill σ ∧ LENGTH σ ≥ 2 ∧
   FST (HD σ) ≠ SND (LAST σ) ⇒
   NoRead (TL σ) (FST (HD σ))`,
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
    (¬NULL σ ⇒ EVERY IS_SOME (MAP SND (FRONT σ))) ∧
    EVERY IS_SOME (MAP FST σ) ∧
    path σ`;
val _ = overload_on(UnicodeChars.turnstile,``wf``);

Theorem wf_init:
   windmill μ ∧
   EVERY IS_SOME (MAP FST μ) ∧
   EVERY IS_SOME (MAP SND μ) ⇒
   ⊢ (μ,[],[])
Proof
  rw[wf_def,path_def]
QED

(* The invariant is preserved *)

Theorem wf_step:
   ∀s1 s2. s1 ▷ s2 ⇒ ⊢ s1 ⇒ ⊢ s2
Proof
  ho_match_mp_tac step_ind >> rw[] >>
  fs[wf_def,windmill_def,ALL_DISTINCT_APPEND] >>
  fs[GSYM SNOC_APPEND,FRONT_DEF] >>
  TRY (match_mp_tac path_change_start) >>
  metis_tac[FST,path_tail]
QED

Theorem wf_steps:
   ∀s1 s2. ⊢ s1 ∧ s1 ▷* s2 ⇒ ⊢ s2
Proof
  ho_match_mp_tac RTC_lifts_invariants >>
  metis_tac[wf_step]
QED

(* semantics of moves *)

val parsem_def = Define`
  parsem μ ρ = ρ =++ (ZIP(MAP FST μ, MAP (ρ o SND) μ))`;

Theorem parsem_nil[simp]:
   parsem [] = I
Proof
  rw[parsem_def,FUN_EQ_THM,UPDATE_LIST_THM]
QED

Theorem parsem_cons:
   ¬MEM x (MAP FST μ) ⇒
   parsem ((x,y)::μ) ρ = (x =+ ρ y) (parsem μ ρ)
Proof
  rw[parsem_def,UPDATE_LIST_THM] >>
  simp[FUN_EQ_THM,APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[] >> BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,MEM_ZIP,FORALL_PROD] >>
  rw[] >> fs[MEM_EL,EL_MAP] >> metis_tac[PAIR,FST]
QED

Theorem independence:
   ∀μ1 s d μ2 μ.
      windmill μ ∧ μ = μ1 ++ [(d,s)] ++ μ2 ⇒
      parsem μ = parsem ([(d,s)]++μ1++μ2)
Proof
  Induct >> simp[] >> Cases >> rw[] >>
  full_simp_tac std_ss [windmill_cons] >>
  simp[parsem_cons,FUN_EQ_THM] >>
  `¬MEM d (MAP FST ((q,r)::(μ1 ++ μ2)))` by (
    fs[windmill_def,ALL_DISTINCT_APPEND] ) >>
  simp[parsem_cons] >>
  full_simp_tac std_ss [MAP,MEM] >>
  `¬MEM q (MAP FST (μ1 ++ μ2))` by fs[] >>
  simp[parsem_cons,APPLY_UPDATE_THM] >> rw[]
QED

Theorem parsem_perm:
   windmill l1 ∧ PERM l1 l2 ⇒ parsem l1 = parsem l2
Proof
  rw[] >>
  Q.ISPEC_THEN`λl. if windmill l then parsem l else ARB`mp_tac
    PERM_lifts_equalities >>
  simp[] >>
  impl_tac >- (
    rpt (pop_assum kall_tac) >>
    rw[] >- (
      Induct_on`x2` >> simp[] >>
      Cases >> rw[] >>
      last_x_assum mp_tac >>
      simp[AND_IMP_INTRO] >>
      impl_tac >- (
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
        `¬MEM q (MAP FST (x1++x2++x3)) ∧
         ¬MEM q (MAP FST (x1++x3++x2))` by (
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
  simp[]
QED

Theorem parsem_untouched:
   ∀ρ μ x. windmill μ ∧ ¬MEM x (MAP FST μ) ⇒ parsem μ ρ x = ρ x
Proof
  gen_tac >> Induct >> simp[] >>
  Cases >> rw[] >>
  `¬MEM q (MAP FST μ)` by fs[windmill_def] >>
  simp[parsem_cons,APPLY_UPDATE_THM] >>
  first_x_assum match_mp_tac >>
  fs[windmill_def]
QED

Theorem parsem_change_env:
   (¬MEM x (MAP FST μ) ⇒ ρ1 x = ρ2 x) ∧
   MAP (ρ1 o SND) μ = MAP (ρ2 o SND) μ ⇒
   parsem μ ρ1 x = parsem μ ρ2 x
Proof
  rw[parsem_def,APPLY_UPDATE_LIST_ALOOKUP] >>
  BasicProvers.CASE_TAC >> first_x_assum match_mp_tac >>
  imp_res_tac ALOOKUP_FAILS >>
  fs[MEM_MAP,FORALL_PROD,MEM_ZIP,MEM_EL] >>
  metis_tac[EL_MAP,FST]
QED

Theorem parsem_NoRead:
   NoRead μ x ⇒
   parsem ((x,y)::μ) ρ = parsem μ ((x =+ ρ y) ρ)
Proof
  rw[parsem_def,APPLY_UPDATE_LIST_ALOOKUP,FUN_EQ_THM,ALOOKUP_APPEND,APPLY_UPDATE_THM,REVERSE_ZIP] >>
  simp[GSYM MAP_REVERSE,ALOOKUP_ZIP_MAP_SND] >>
  qpat_abbrev_tac`z = ALOOKUP X Y` >>
  Cases_on`z`>>rw[APPLY_UPDATE_THM] >>
  fs[markerTheory.Abbrev_def] >>
  pop_assum(assume_tac o SYM) >>
  imp_res_tac ALOOKUP_MEM >>
  qmatch_assum_rename_tac`NoRead μ (SND p)` >>
  Cases_on`p`>>fs[]>>
  fs[MAP_REVERSE,GSYM REVERSE_ZIP] >>
  fs[MEM_ZIP,MEM_MAP,MEM_EL,EXISTS_PROD] >>
  metis_tac[]
QED

Theorem parsem_MAP_INJ:
   ∀ms. windmill ms ∧
        INJ f (set (MAP FST ms ++ MAP SND ms)) UNIV ⇒
        ∀x. MEM x (MAP FST ms) ⇒ parsem (MAP (f ## f) ms) r (f x) = parsem ms (r o f) x
Proof
  simp[windmill_def]
  \\ Induct \\ simp[]
  \\ Cases \\ strip_tac \\ fs[]
  \\ qmatch_assum_rename_tac`¬MEM x (MAP FST ms)`
  \\ `¬MEM (f x) (MAP FST (MAP (f ## f) ms))`
  by (
    simp[MAP_MAP_o,o_PAIR_MAP] \\ fs[MEM_MAP]
    \\ spose_not_then strip_assume_tac
    \\ qhdtm_x_assum`INJ`mp_tac
    \\ simp[INJ_DEF]
    \\ simp[MEM_MAP]
    \\ metis_tac[] )
  \\ simp[parsem_cons]
  \\ simp[APPLY_UPDATE_THM]
  \\ qx_gen_tac`y`
  \\ strip_tac \\ rveq \\ simp[]
  \\ `f x =  f y ⇒ x = y`
  by  (
    qhdtm_x_assum`INJ`mp_tac
    \\ REWRITE_TAC[INJ_DEF,IN_INSERT,IN_UNION]
    \\ metis_tac[] )
  \\ rw[] \\ fs[]
  \\ first_x_assum(match_mp_tac o MP_CANON)
  \\ simp[]
  \\ qhdtm_x_assum`INJ`mp_tac
  \\ REWRITE_TAC[INJ_DEF,IN_INSERT,IN_UNION]
  \\ metis_tac[]
QED

val seqsem_def = Define`
  (seqsem [] ρ = ρ) ∧
  (seqsem ((d,s)::τ) ρ = seqsem τ ((d =+ ρ s) ρ))`;

val seqsem_ind = theorem"seqsem_ind";

Theorem seqsem_append:
   ∀l1 l2. seqsem (l1 ++ l2) = seqsem l2 o seqsem l1
Proof
  Induct >> fs[FUN_EQ_THM,seqsem_def] >> Cases >> simp[seqsem_def]
QED

Theorem seqsem_move_unchanged:
   ∀ms r. ¬MEM k (MAP FST ms) ⇒ seqsem ms r k = r k
Proof
  ho_match_mp_tac seqsem_ind
  \\ rw[seqsem_def,APPLY_UPDATE_THM]
QED

(* semantics of the state *)

val sem_def = Define`
  sem (μ,σ,τ) ρ = parsem (μ++σ) (seqsem (REVERSE τ) ρ)`;

Theorem sem_init:
   sem (μ,[],[]) = parsem μ
Proof
  rw[FUN_EQ_THM,sem_def,seqsem_def]
QED

Theorem sem_final:
   sem ([],[],τ) = seqsem (REVERSE τ)
Proof
  rw[sem_def,FUN_EQ_THM,parsem_def,UPDATE_LIST_THM]
QED

(* semantic preservation *)

val eqenv_def = Define`
  eqenv ρ1 ρ2 ⇔ ∀r. IS_SOME r ⇒ (ρ1 r = ρ2 r)`;
val _ = set_fixity"\226\137\161"(Infix(NONASSOC,450));
val _ = overload_on("\226\137\161",``eqenv``);

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
    `¬MEM r (MAP FST (μ1++μ2++σ))` by
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
    `∀s. parsem (μ ++ σ ++ [(d,s)]) = parsem ((d,s)::(μ++σ))` by (
      gen_tac >> match_mp_tac parsem_perm >> simp[] >> fs[windmill_def] >>
      metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF] ) >>
    `¬MEM d (MAP FST (μ++σ))` by fs[windmill_def,ALL_DISTINCT_APPEND] >>
    simp[parsem_cons,APPLY_UPDATE_THM] >>
    rw[seqsem_append,seqsem_def,APPLY_UPDATE_THM] >>
    fs[GSYM SNOC_APPEND] >>
    match_mp_tac parsem_change_env >>
    simp[MAP_EQ_f,APPLY_UPDATE_THM] >>
    rw[] >> fs[EVERY_MAP] >> fs[EVERY_MEM] >>
    metis_tac[IS_SOME_DEF] ) >>
  conj_tac >- (
    rw[sem_def,FUN_EQ_THM,wf_def,eqenv_def] >>
    `parsem (μ ++ [(dn,sn)] ++ σ ++ [(d0,s0)]) =
     parsem ((d0,s0)::((dn,sn)::(μ ++ σ)))` by (
      match_mp_tac parsem_perm >> simp[] >>
      match_mp_tac PERM_TRANS >>
      metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF]) >>
    pop_assum (SUBST1_TAC) >>
    `parsem (μ ++ σ ++ [(d0,s0)]) =
     parsem ((d0,s0)::(μ++σ))` by (
      match_mp_tac parsem_perm >> fs[windmill_def,ALL_DISTINCT_APPEND] >>
      metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF]) >>
    pop_assum (SUBST1_TAC) >>
    `¬MEM d0 (MAP FST (μ++σ)) ∧ ¬MEM d0 (MAP FST ((dn,sn)::(μ++σ)))` by (
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
  `parsem (μ ++ [(d,s)]) = parsem ((d,s)::μ)` by (
     match_mp_tac parsem_perm >> simp[] >>
     metis_tac[CONS_APPEND,APPEND_ASSOC,PERM_APPEND,PERM_APPEND_IFF]) >>
  pop_assum (SUBST1_TAC) >>
  simp[seqsem_append,seqsem_def,APPLY_UPDATE_THM] >>
  AP_THM_TAC >>
  match_mp_tac parsem_NoRead >>
  rw[]);

Theorem steps_sem:
   ∀s1 s2. s1 ▷* s2 ∧ ⊢ s1 ⇒ (∀ρ. sem s1 ρ ≡ sem s2 ρ)
Proof
  simp[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac RTC_INDUCT >>
  conj_tac >- simp[eqenv_def] >>
  rw[] >>
  imp_res_tac wf_step >> fs[] >>
  imp_res_tac step_sem >>
  fs[eqenv_def]
QED

Theorem steps_correct:
   windmill μ ∧
   EVERY IS_SOME (MAP FST μ) ∧
   EVERY IS_SOME (MAP SND μ) ∧
   (μ,[],[]) ▷* ([],[],τ)
   ⇒
   ∀ρ. parsem μ ρ ≡ seqsem (REVERSE τ) ρ
Proof
  rw[] >>
  imp_res_tac steps_sem >>
  pop_assum mp_tac >>
  impl_tac >- simp[wf_def] >>
  simp[sem_def,seqsem_def]
QED

(* deterministic algorithm *)

val _ = add_infix("dstep",450,NONASSOC);

val (dstep_rules,dstep_ind,dstep_cases) = (Hol_reln o List.map(replace_quote "\226\134\170" "dstep"))`
  (([(r,r)]++μ,[],τ) ↪ (μ,[],τ)) ∧
  (s ≠ d ⇒
   ([(d,s)]++μ,[],τ) ↪ (μ,[(d,s)],τ)) ∧
  (NoRead μ1 d ⇒
   (μ1++[(r,d)]++μ2,[(d,s)]++σ,τ) ↪
   (μ1++μ2,[(r,d);(d,s)]++σ,τ)) ∧
  (NoRead μ r ⇒
   (μ,[(r,s)]++σ++[(d,r)],τ) ↪
   (μ,σ++[(d,NONE)],[(r,s);(NONE,r)]++τ)) ∧
  (NoRead μ dn ∧ dn ≠ s0 ⇒
   (μ,[(dn,sn)]++σ++[(d0,s0)],τ) ↪
   (μ,σ++[(d0,s0)],[(dn,sn)]++τ)) ∧
  (NoRead μ d ⇒
   (μ,[(d,s)],τ) ↪ (μ,[],[(d,s)]++τ))`;

val _ = set_fixity"\226\134\170"(Infix(NONASSOC,450));
val _ = overload_on("\226\134\170",``$dstep``);

val _ = set_fixity "\226\134\170*" (Infix(NONASSOC,450));
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

Theorem dsteps_steps:
   ∀s1 s2. s1 ↪* s2 ⇒ ⊢ s1 ⇒ s1 ▷* s2
Proof
  ho_match_mp_tac RTC_INDUCT >> rw[] >>
  metis_tac[dstep_step,wf_steps,RTC_CASES_RTC_TWICE]
QED

(* functional algorithm *)

val fstep_def = Define`
  fstep st =
  case st of
  | ([],[],_) => st
  | ((d,s)::t,[],l) =>
    if s = d
    then (t,[],l)
    else (t,[(d,s)],l)
  | (t,(d,s)::b,l) =>
    splitAtPki (λi p. SND p = d)
      (λt1 rt2.
        case rt2 of
        | (rd::t2) => (t1++t2,rd::(d,s)::b,l)
        | [] => if NULL b then (t,[],(d,s)::l) else
                let (b',(d',s')) = (FRONT b,LAST b) in
                if s' = d
                then (t,SNOC (d',NONE) b',(d,s)::(NONE,d)::l)
                else (t,b,(d,s)::l))
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
      TRY(map_every qexists_tac[`FST(LAST t')`,`SND(LAST t')`,`FRONT t'`]) >>
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
  metis_tac[SND,PAIR])

Theorem fstep_dstep:
   (∀τ. s ≠ ([],[],τ)) ⇒ s ↪ fstep s
Proof
  rw[fstep_def] >>
  every_case_tac >> fs[NULL_LENGTH,LENGTH_NIL] >>
  simp[splitAtPki_def]
  >- ( simp[UNCURRY] >> simp[dstep_cases] )
  >- (
    simp[UNCURRY] >> rw[] >>
    simp[dstep_cases] >-
      metis_tac[APPEND_FRONT_LAST] >>
    Q.ISPEC_THEN`t`FULL_STRUCT_CASES_TAC SNOC_CASES >> fs[] >>
    Cases_on`x`>>fs[] )
  >> TRY (rw[dstep_cases]>>NO_TAC)
  >> tac
QED

val pmov_def = tDefine"pmov"`
  pmov s = case s of
    | ([],[],_) => s
    | _ => pmov (fstep s)`
  (WF_REL_TAC`measure (λ(μ,σ,τ). 2 * LENGTH μ + LENGTH σ)` >>
   rw[fstep_def] >- (
     fs[NULL_LENGTH,LENGTH_NIL,splitAtPki_def] >>
     simp[UNCURRY] >> rw[] >>
     simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL] )
   >- (
     simp[splitAtPki_def,UNCURRY] >>
     rw[] >> simp[] >>
     fs[NULL_LENGTH,LENGTH_NIL] >>
     simp[LENGTH_FRONT,PRE_SUB1,LENGTH_NOT_NULL,NULL_LENGTH,LENGTH_NIL] )
   >> (
     every_case_tac >> simp[splitAtPki_def,UNCURRY] >>
     rw[] >> simp[splitAtPki_def,UNCURRY] >>
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

Theorem pmov_dsteps:
   ∀s. s ↪* pmov s
Proof
  ho_match_mp_tac pmov_ind >>
  rw[] >> PairCases_on`s` >>
  ONCE_REWRITE_TAC[pmov_def] >>
  every_case_tac >> simp[] >> rw[] >> fs[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  match_mp_tac fstep_dstep >> simp[]
QED

Theorem pmov_final:
   ∀s. ∃τ. pmov s = ([],[],τ)
Proof
  ho_match_mp_tac pmov_ind >>
  rw[] >> PairCases_on`s` >>
  ONCE_REWRITE_TAC[pmov_def] >>
  every_case_tac >> simp[]
QED

(* The top-level parallel move compiler *)

val parmove_def = Define `
  parmove (xs:('a # 'a) list) =
    REVERSE(SND(SND(pmov (MAP (\(x,y). (SOME x, SOME y)) xs, [],[]))))`;

Theorem parmove_correct:
   windmill xs ⇒
   ∀ρ. seqsem (parmove xs) ρ ≡
       parsem (MAP (\(x,y). (SOME x, SOME y)) xs) ρ
Proof
  rw[parmove_def] >>
  qpat_abbrev_tac`μ = MAP _ xs` >>
  `∃τ. pmov (μ,[],[]) = ([],[],τ)` by metis_tac[pmov_final] >>
  simp[] >>
  `(μ,[],[]) ↪* ([],[],τ)` by metis_tac[pmov_dsteps] >>
  imp_res_tac dsteps_steps >>
  pop_assum mp_tac >>
  impl_keep_tac >- (
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
  fs[wf_def]
QED

(* the compiler does not invent new moves *)

Theorem MEM_MAP_FST_SND_SND_pmov:
   ∀p x.
    MEM (SOME x) (MAP FST (SND(SND(pmov p)))) ⇒
    MEM (SOME x) (MAP FST (FST p ++ FST(SND p) ++ SND(SND p)))
Proof
  ho_match_mp_tac pmov_ind
  \\ simp[]
  \\ gen_tac
  \\ PairCases_on`p`
  \\ simp[]
  \\ strip_tac
  \\ rpt gen_tac
  \\ simp[Once pmov_def]
  \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    strip_tac \\ fs[]
    \\ first_x_assum drule
    \\ simp[fstep_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    >- (rw[] \\ fs[])
    \\ simp[splitAtPki_def]
    \\ IF_CASES_TAC \\ simp[]
    >- ( rw[] \\ fs[] )
    \\ simp[splitAtPki_EQN]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[UNCURRY]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[] \\ fs[]
    \\ TRY (
      qmatch_assum_rename_tac`¬ NULL ls`
      \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES
      \\ fs[]
      \\ fs[MAP_SNOC] )
    \\ imp_res_tac OLEAST_SOME_IMP \\ fs[]
    >- ( fs[MEM_MAP] >> metis_tac[MEM_TAKE,LESS_IMP_LESS_OR_EQ])
    \\ ( fs[MEM_MAP] >> metis_tac[MEM_DROP,MEM,LESS_IMP_LESS_OR_EQ] ))
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ first_x_assum drule
  \\ simp[fstep_def]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ simp[splitAtPki_EQN]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  >- ( rw[] \\ fs[] )
  \\ simp[UNCURRY]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ rw[] \\ fs[]
  \\ qmatch_assum_rename_tac`¬ NULL ls`
  \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES
  \\ fs[]
  \\ fs[MAP_SNOC]
QED

Theorem MEM_MAP_FST_parmove:
   MEM (SOME x) (MAP FST (parmove mvs)) ⇒ MEM x (MAP FST mvs)
Proof
  rw[parmove_def]
  \\ fs[MEM_MAP]
  \\ imp_res_tac(SIMP_RULE std_ss [MEM_MAP,PULL_EXISTS] MEM_MAP_FST_SND_SND_pmov)
  \\ fs[MEM_MAP,UNCURRY]
  \\ rw[] \\ fs[]
  \\ metis_tac[]
QED

Theorem MEM_MAP_SND_SND_SND_pmov:
   ∀p x.
    MEM (SOME x) (MAP SND (SND(SND(pmov p)))) ⇒
    MEM (SOME x) (MAP SND (FST p ++ FST(SND p) ++ SND(SND p)))
Proof
  ho_match_mp_tac pmov_ind
  \\ simp[]
  \\ gen_tac
  \\ PairCases_on`p`
  \\ simp[]
  \\ strip_tac
  \\ rpt gen_tac
  \\ simp[Once pmov_def]
  \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
  >- (
    strip_tac \\ fs[]
    \\ first_x_assum drule
    \\ simp[fstep_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    >- (rw[] \\ fs[])
    \\ simp[splitAtPki_def]
    \\ IF_CASES_TAC \\ simp[]
    >- ( rw[] \\ fs[] )
    \\ simp[splitAtPki_EQN]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[UNCURRY]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[] \\ fs[]
    \\ TRY (
      qmatch_assum_rename_tac`¬ NULL ls`
      \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES
      \\ fs[]
      \\ fs[MAP_SNOC] )
    \\ imp_res_tac OLEAST_SOME_IMP \\ fs[]
    >- ( fs[MEM_MAP] >> metis_tac[MEM_TAKE,LESS_IMP_LESS_OR_EQ])
    \\ ( fs[MEM_MAP] >> metis_tac[MEM_DROP,MEM,LESS_IMP_LESS_OR_EQ] ))
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ first_x_assum drule
  \\ simp[fstep_def]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ simp[splitAtPki_EQN]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  >- ( rw[] \\ fs[] )
  \\ simp[UNCURRY]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ rw[] \\ fs[]
  \\ qmatch_assum_rename_tac`¬ NULL ls`
  \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES
  \\ fs[]
  \\ fs[MAP_SNOC]
QED

Theorem MEM_MAP_SND_parmove:
   MEM (SOME x) (MAP SND (parmove mvs)) ⇒ MEM x (MAP SND mvs)
Proof
  rw[parmove_def]
  \\ fs[MEM_MAP]
  \\ imp_res_tac(SIMP_RULE std_ss [MEM_MAP,PULL_EXISTS] MEM_MAP_SND_SND_SND_pmov)
  \\ fs[MEM_MAP,UNCURRY]
  \\ rw[] \\ fs[]
  \\ metis_tac[]
QED

(* the compiler does not use uninitialised temporaries *)

val not_use_temp_before_assign_def = Define`
   (not_use_temp_before_assign [] = T) ∧
   (not_use_temp_before_assign ((d,NONE)::ls) = F) ∧
   (not_use_temp_before_assign ((NONE,s)::ls) = T) ∧
   (not_use_temp_before_assign ((d,s)::ls) = not_use_temp_before_assign ls)`
val _ = export_rewrites["not_use_temp_before_assign_def"];

val not_use_temp_before_assign_ind = theorem"not_use_temp_before_assign_ind";

Theorem not_use_temp_before_assign_append:
   ∀l1 l2.
   (not_use_temp_before_assign (l1 ++ l2) ⇔
    not_use_temp_before_assign l1 ∧
    (EVERY IS_SOME (MAP FST l1) ⇒ not_use_temp_before_assign l2))
Proof
  ho_match_mp_tac not_use_temp_before_assign_ind \\ simp[]
QED

Theorem not_use_temp_before_assign_insert:
   ∀l1 l2.
   not_use_temp_before_assign (l1 ++ l2) ⇒
   not_use_temp_before_assign (l1 ++ [(SOME x, SOME y)] ++ l2)
Proof
  ho_match_mp_tac not_use_temp_before_assign_ind \\ simp[]
QED

Theorem not_use_temp_before_assign_thm:
   ∀ls. not_use_temp_before_assign ls =
    ∀i. find_index NONE (MAP SND ls) 0 = SOME i ⇒
      ∃j. find_index NONE (MAP FST ls) 0 = SOME j ∧ j < i
Proof
  ho_match_mp_tac not_use_temp_before_assign_ind
  \\ simp[]
  \\ simp[find_index_def]
  \\ rw[find_index_APPEND]
  >- (
    imp_res_tac find_index_LESS_LENGTH
    \\ decide_tac )
  \\ qpat_abbrev_tac`l1 = MAP FST ls`
  \\ qpat_abbrev_tac`l2 = MAP SND ls`
  \\ Q.ISPECL_THEN[`l1`]mp_tac find_index_shift_0
  \\ disch_then(qspecl_then[`NONE`,`1`]mp_tac)
  \\ disch_then SUBST_ALL_TAC
  \\ Q.ISPECL_THEN[`l2`]mp_tac find_index_shift_0
  \\ disch_then(qspecl_then[`NONE`,`1`]mp_tac)
  \\ disch_then SUBST_ALL_TAC
  \\ rw[EQ_IMP_THM,PULL_EXISTS]
QED

Theorem step_not_use_temp_before_assign:
   ∀s1 s2. s1 ▷ s2 ⇒
    ⊢ s1 ∧
    not_use_temp_before_assign (REVERSE(FST(SND s1) ++ SND(SND s1)))
    ⇒
    not_use_temp_before_assign (REVERSE(FST(SND s2) ++ SND(SND s2)))
Proof
  ho_match_mp_tac step_ind
  \\ simp[not_use_temp_before_assign_append]
  \\ simp[MAP_REVERSE,EVERY_REVERSE,REVERSE_APPEND]
  \\ conj_tac
  >- ( rw[] \\ fs[wf_def,IS_SOME_EXISTS])
  \\ conj_tac
  >- ( rw[] \\ fs[wf_def,IS_SOME_EXISTS])
  \\ conj_tac
  >- (
    rw[]
    \\ fs[wf_def,IS_SOME_EXISTS]
    \\ fs[not_use_temp_before_assign_append]
    \\ Cases_on`s` \\ fs[] )
  \\ rw[]
  \\ fs[wf_def,IS_SOME_EXISTS]
  \\ fs[not_use_temp_before_assign_append]
  \\ rfs[]
  \\ rw[]
  \\ fs[MAP_REVERSE,EVERY_REVERSE]
QED

Theorem steps_not_use_temp_before_assign:
   ∀s1 s2.
    (λs1. ⊢ s1 ∧ not_use_temp_before_assign (REVERSE (FST (SND s1) ++ SND (SND s1)))) s1 ∧
    s1 ▷* s2
    ⇒
    (λs1. ⊢ s1 ∧ not_use_temp_before_assign (REVERSE (FST (SND s1) ++ SND (SND s1)))) s2
Proof
  match_mp_tac RTC_lifts_invariants
  \\ simp[]
  \\ metis_tac[wf_step,step_not_use_temp_before_assign]
QED

Theorem pmov_not_use_temp_before_assign:
   ∀p i. ⊢ p ∧ not_use_temp_before_assign (REVERSE (FST (SND p) ++ SND (SND p)))
    ⇒ not_use_temp_before_assign (REVERSE (FST (SND (pmov p)) ++ SND (SND (pmov p))))
Proof
  rw[]
  \\ qspec_then`p`assume_tac pmov_dsteps
  \\ drule dsteps_steps
  \\ simp[] \\ strip_tac
  \\ drule (ONCE_REWRITE_RULE[CONJ_COMM] steps_not_use_temp_before_assign)
  \\ simp[]
QED

Theorem parmove_not_use_temp_before_assign:
   windmill mvs ⇒
   case find_index NONE (MAP SND (parmove mvs)) 0 of
      NONE => T
    | SOME i =>
      case find_index NONE (MAP FST (parmove mvs)) 0 of
        NONE => F
      | SOME j => ¬(i ≤ j)
Proof
  strip_tac
  \\ simp[parmove_def]
  \\ qpat_abbrev_tac`ls = REVERSE _`
  \\ `not_use_temp_before_assign ls`
  suffices_by (
    simp[not_use_temp_before_assign_thm]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ simp[] )
  \\ simp[Abbr`ls`]
  \\ qpat_abbrev_tac`p = (_,_)`
  \\ qspec_then`p`strip_assume_tac pmov_final
  \\ qspec_then`p`mp_tac pmov_not_use_temp_before_assign
  \\ fs[]
  \\ disch_then match_mp_tac
  \\ simp[Abbr`p`]
  \\ simp[wf_def,MAP_MAP_o,o_DEF,UNCURRY,EVERY_MAP]
  \\ fs[windmill_def]
  \\ simp[MAP_MAP_o,o_DEF,UNCURRY]
  \\ simp[GSYM MAP_MAP_o,GSYM o_DEF]
  \\ match_mp_tac ALL_DISTINCT_MAP_INJ
  \\ simp[]
QED

(* the compiler preserves all-distinct variables *)

Theorem ALL_DISTINCT_step:
   ∀s1 s2. s1 ▷ s2 ⇒
    ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++ (SND (SND s1))))) ⇒
    ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s2 ++ FST (SND s2) ++ (SND (SND s2)))))
Proof
  ho_match_mp_tac step_ind
  \\ simp[]
  \\ rpt conj_tac
  \\ simp[FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER]
  \\ rw[] \\ fs[ALL_DISTINCT_APPEND,MEM_FILTER]
  \\ metis_tac[IS_SOME_DEF]
QED

Theorem ALL_DISTINCT_steps:
   ∀s1 s2.
    (λs1. ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++ (SND (SND s1)))))) s1 ∧
    s1 ▷* s2
    ⇒
    (λs1. ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST s1 ++ FST (SND s1) ++ (SND (SND s1)))))) s2
Proof
  match_mp_tac RTC_lifts_invariants
  \\ simp[]
  \\ PROVE_TAC[ALL_DISTINCT_step,MAP_APPEND]
QED

Theorem ALL_DISTINCT_pmov:
   ∀p. ⊢p ∧ ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST p ++ FST (SND p) ++ SND (SND p)))) ⇒
       ALL_DISTINCT (FILTER IS_SOME (MAP FST (FST (pmov p) ++ FST (SND (pmov p)) ++ SND (SND (pmov p)))))
Proof
  rw[]
  \\ qspec_then`p`assume_tac pmov_dsteps
  \\ drule dsteps_steps
  \\ simp[] \\ strip_tac
  \\ drule (ONCE_REWRITE_RULE[CONJ_COMM] ALL_DISTINCT_steps)
  \\ simp[]
QED

Theorem ALL_DISTINCT_parmove:
   ALL_DISTINCT (MAP FST mvs) ⇒
   ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove mvs)))
Proof
  rw[parmove_def,
     FILTER_REVERSE,MAP_REVERSE,ALL_DISTINCT_REVERSE]
  \\ qmatch_goalsub_abbrev_tac`pmov p`
  \\ qspec_then`p`mp_tac ALL_DISTINCT_pmov
  \\ impl_tac
  >- (
    simp[Abbr`p`,wf_def,windmill_def]
    \\ simp[MAP_MAP_o,o_DEF,UNCURRY,EVERY_MAP,FILTER_MAP]
    \\ `FILTER (λx. T) mvs = mvs` by simp[FILTER_EQ_ID]
    \\ simp[]
    \\ simp[GSYM o_DEF,GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[] )
  \\ qspec_then`p`strip_assume_tac pmov_final
  \\ simp[]
QED

(* the compiler retains all non-trivial moves *)

val state_to_list_def = Define`
  state_to_list p = APPEND (FST p) (FST(SND p)) ++ SND(SND p)`;

Theorem step_preserves_moves:
   ∀s1 s2. s1 ▷ s2 ⇒
    ∀x. (∃y. MEM (x,y) (state_to_list s1) ∧ x ≠ y) ⇒
        (∃y. MEM (x,y) (state_to_list s2) ∧ x ≠ y)
Proof
  ho_match_mp_tac step_ind
  \\ rw[state_to_list_def] \\ metis_tac[]
QED

Theorem steps_preserves_moves:
   ∀s1 s2.
    (λs1. (∃y. MEM (x,y) (state_to_list s1) ∧ x ≠ y)) s1 ∧
    s1 ▷* s2
    ⇒
    (λs1. (∃y. MEM (x,y) (state_to_list s1) ∧ x ≠ y)) s2
Proof
  match_mp_tac RTC_lifts_invariants \\ simp[]
  \\ PROVE_TAC[step_preserves_moves]
QED

Theorem pmov_preserves_moves:
   ∀p. ⊢p ∧ MEM (x,y) (state_to_list p) ∧ x ≠ y ⇒
    MEM x (MAP FST (state_to_list (pmov p)))
Proof
  rw[]
  \\ qspec_then`p`assume_tac pmov_dsteps
  \\ drule dsteps_steps
  \\ simp[] \\ strip_tac
  \\ drule (ONCE_REWRITE_RULE[CONJ_COMM] steps_preserves_moves)
  \\ simp[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem parmove_preserves_moves:
   windmill moves ∧ MEM (x,y) moves ∧ x ≠ y ⇒ MEM (SOME x) (MAP FST (parmove moves))
Proof
  rw[parmove_def,MAP_REVERSE]
  \\ qmatch_goalsub_abbrev_tac`pmov p`
  \\ qspec_then`p`(mp_tac o Q.GENL[`x`,`y`]) pmov_preserves_moves
  \\ qspec_then`p`strip_assume_tac pmov_final
  \\ simp[state_to_list_def,Abbr`p`]
  \\ disch_then(qspecl_then[`SOME x`,`SOME y`]mp_tac)
  \\ impl_tac
  >- (
    simp[wf_def,EVERY_MAP,EVERY_MEM,IS_SOME_EXISTS,UNCURRY]
    \\ simp[MEM_MAP,UNCURRY,EXISTS_PROD]
    \\ fs[windmill_def]
    \\ simp[MAP_MAP_o,o_DEF,UNCURRY]
    \\ simp[GSYM o_DEF,GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[] )
  \\ simp[]
QED

(* mapping an injective function over compiled moves *)

val map_state_def = Define`
  map_state f = let m = MAP (f ## f) in m ## m ## m`;

val inj_on_state_def = Define`
  inj_on_state f p =
     let ls0 = state_to_list p in
     let ls = MAP FST ls0 ++ MAP SND ls0 in
     (∀x y. MEM x ls ∧ MEM y ls ∧ f x = f y ⇒ x = y) ∧
     (∀x. f x = NONE ⇔ x = NONE)`;

Theorem step_inj_on_state:
   ∀s1 s2. s1 ▷ s2 ⇒ inj_on_state f s1 ⇒ inj_on_state f s2
Proof
  ho_match_mp_tac step_ind
  \\ rpt conj_tac
  \\ simp[inj_on_state_def]
  \\ rw[]
  \\ TRY (
    first_x_assum match_mp_tac
    \\ fs[state_to_list_def]
    \\ NO_TAC)
  \\ (Cases_on`x=NONE` >- metis_tac[])
  \\ (Cases_on`y=NONE` >- metis_tac[])
  \\ first_x_assum match_mp_tac
  \\ fs[state_to_list_def]
QED

Theorem steps_inj_on_state:
   ∀s1 s2. inj_on_state f s1 ∧ s1 ▷* s2 ⇒ inj_on_state f s2
Proof
  match_mp_tac RTC_lifts_invariants \\ metis_tac[step_inj_on_state]
QED

Theorem step_MAP_INJ:
   ∀s1 s2. s1 ▷ s2 ⇒ inj_on_state f s1 ⇒ map_state f s1 ▷ map_state f s2
Proof
  ho_match_mp_tac step_ind
  \\ simp[map_state_def]
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ MATCH_ACCEPT_TAC (step_rules |> CONJUNCTS |> el 1))
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ MATCH_ACCEPT_TAC (step_rules |> CONJUNCTS |> el 2))
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ MATCH_ACCEPT_TAC (step_rules |> CONJUNCTS |> el 3 |> SIMP_RULE (srw_ss())[]))
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ `f NONE = NONE` by fs[inj_on_state_def,LET_THM] \\ simp[]
    \\ MATCH_ACCEPT_TAC (step_rules |> CONJUNCTS |> el 4 |> SIMP_RULE (srw_ss())[]))
  \\ conj_tac
  >- (
    rpt gen_tac \\ strip_tac
    \\ strip_tac
    \\ match_mp_tac (step_rules |> CONJUNCTS |> el 5 |> SIMP_RULE (srw_ss())[])
    \\ CCONTR_TAC \\ reverse(fs[])
    >- (
      fs[inj_on_state_def,LET_THM]
      \\ qpat_x_assum`_ ≠ _`mp_tac
      \\ simp[]
      \\ first_x_assum match_mp_tac
      \\ simp[]
      \\ simp[state_to_list_def] )
    \\ fs[MEM_MAP,EXISTS_PROD]
    \\ qmatch_assum_rename_tac`f a = f b`
    \\ `a = b` suffices_by metis_tac[]
    \\ fs[inj_on_state_def,LET_THM]
    \\ first_x_assum match_mp_tac
    \\ simp[]
    \\ simp[state_to_list_def]
    \\ simp[MEM_MAP,EXISTS_PROD]
    \\ metis_tac[] )
  \\ rpt gen_tac \\ ntac 2 strip_tac
  \\ match_mp_tac (step_rules |> CONJUNCTS |> el 6 |> SIMP_RULE (srw_ss())[])
  \\ fs[MEM_MAP,EXISTS_PROD]
  \\ spose_not_then strip_assume_tac
  \\ qmatch_assum_rename_tac`f a = f b`
  \\ `a = b` suffices_by metis_tac[]
  \\ fs[inj_on_state_def,LET_THM]
  \\ first_x_assum match_mp_tac
  \\ simp[]
  \\ simp[state_to_list_def]
  \\ simp[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[]
QED

val steps_MAP_INJ = Q.prove(
  `∀s1 s2. s1 ▷* s2 ⇒
    inj_on_state f s1 ⇒
    map_state f s1 ▷* map_state f s2`,
  ho_match_mp_tac RTC_INDUCT
  \\ rw[]
  \\ imp_res_tac step_inj_on_state
  \\ fs[]
  \\ metis_tac[step_MAP_INJ,RTC_RULES]);

Theorem fstep_MAP_INJ:
   ∀p. inj_on_state f p ⇒ fstep (map_state f p) = map_state f (fstep p)
Proof
  gen_tac \\ strip_tac
  \\ PairCases_on`p`
  \\ simp[fstep_def]
  \\ match_mp_tac EQ_SYM
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ simp[map_state_def]
  >- (
    BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ fs[inj_on_state_def,LET_THM]
    \\ qmatch_goalsub_rename_tac`f x = f y`
    \\ `f x = f y ⇔ x = y`
    by (
      rw[EQ_IMP_THM]
      \\ first_x_assum match_mp_tac
      \\ simp[state_to_list_def] )
    \\ rw[] )
  \\ CONV_TAC(LAND_CONV(REWR_CONV splitAtPki_RAND))
  \\ simp[splitAtPki_MAP]
  \\ qmatch_abbrev_tac`splitAtPki P1 k1 _ = splitAtPki P2 k2 _`
  \\ `splitAtPki P2 k2 p0 = splitAtPki P1 k2 p0`
  by (
    match_mp_tac splitAtPki_change_predicate
    \\ qhdtm_x_assum`inj_on_state`mp_tac
    \\ simp[Abbr`P1`,Abbr`P2`]
    \\ simp[inj_on_state_def]
    \\ rw[EQ_IMP_THM]
    \\ first_x_assum match_mp_tac
    \\ simp[]
    \\ simp[state_to_list_def]
    \\ simp[MEM_MAP,MEM_EL]
    \\ metis_tac[] )
  \\ simp[]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ unabbrev_all_tac
  \\ simp[FUN_EQ_THM]
  \\ rpt gen_tac
  \\ BasicProvers.TOP_CASE_TAC \\ simp[]
  \\ Cases_on`t`\\ simp[]
  \\ simp[UNCURRY]
  \\ CONV_TAC(LAND_CONV(REWR_CONV COND_RAND))
  \\ simp[]
  \\ simp[MAP_SNOC]
  \\ AP_THM_TAC
  \\ match_mp_tac(METIS_PROVE[]``x = x' ∧ y = y' ⇒ f x y = f x' y'``)
  \\ simp[]
  \\ REWRITE_TAC[GSYM MAP]
  \\ simp[LAST_MAP]
  \\ simp[MAP_FRONT]
  \\ qhdtm_x_assum`inj_on_state`mp_tac
  \\ simp[inj_on_state_def]
  \\ rw[EQ_IMP_THM]
  \\ first_x_assum match_mp_tac
  \\ simp[]
  \\ simp[state_to_list_def]
  \\ simp[MEM_MAP]
  \\ qmatch_goalsub_rename_tac`LAST (h::t)`
  \\ `MEM (LAST (h::t)) (h::t)` by simp[MEM_LAST]
  \\ fs[]
  \\ metis_tac[]
QED

Theorem pmov_MAP_INJ:
   ∀p. ⊢ p ∧ inj_on_state f p
  ⇒ pmov (map_state f p) = map_state f (pmov p)
Proof
  ho_match_mp_tac pmov_ind
  \\ gen_tac
  \\ PairCases_on`p`
  \\ simp[]
  \\ strip_tac
  \\ strip_tac
  \\ simp[Once pmov_def]
  \\ simp[Once pmov_def,SimpRHS]
  \\ match_mp_tac EQ_SYM
  \\ BasicProvers.TOP_CASE_TAC
  \\ TRY ( BasicProvers.TOP_CASE_TAC >- simp[map_state_def] )
  \\ qmatch_assum_abbrev_tac`⊢ p`
  \\ `p ▷* fstep p`
  by (
    match_mp_tac (MP_CANON dsteps_steps)
    \\ simp[]
    \\ match_mp_tac RTC_SUBSET
    \\ match_mp_tac fstep_dstep
    \\ simp[Abbr`p`] )
  >- (
    match_mp_tac EQ_SYM
    \\ simp[Once map_state_def,Abbr`p`]
    \\ simp[fstep_MAP_INJ]
    \\ first_x_assum (match_mp_tac o MP_CANON)
    \\ simp[]
    \\ metis_tac[steps_inj_on_state,wf_steps] )
  \\ fs[fstep_MAP_INJ]
  \\ fs[map_state_def,LET_THM,Abbr`p`]
  \\ match_mp_tac EQ_SYM
  \\ first_x_assum match_mp_tac
  \\ metis_tac[steps_inj_on_state,wf_steps]
QED

Theorem parmove_MAP_INJ:
   (let ls1 = MAP FST ls ++ MAP SND ls in (∀x y. MEM x ls1 ∧ MEM y ls1 ∧ f x = f y ⇒ x = y)) ∧
   windmill ls
   ⇒
   parmove (MAP (f ## f) ls) = MAP (OPTION_MAP f ## OPTION_MAP f) (parmove ls)
Proof
  rw[parmove_def,MAP_REVERSE]
  \\ match_mp_tac EQ_SYM
  \\ qmatch_goalsub_abbrev_tac`pmov p`
  \\ match_mp_tac EQ_SYM
  \\ qmatch_goalsub_abbrev_tac`pmov mp`
  \\ `mp = map_state (OPTION_MAP f) p`
  by (simp[Abbr`p`,Abbr`mp`,map_state_def,MAP_MAP_o,o_DEF,UNCURRY])
  \\ fs[Abbr`mp`]
  \\ `inj_on_state (OPTION_MAP f) p`
  by (
    simp[inj_on_state_def]
    \\ fs[Abbr`p`,LET_THM]
    \\ simp[state_to_list_def]
    \\ fs[MAP_MAP_o,o_DEF,UNCURRY]
    \\ fs[MEM_MAP,PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ rveq
    \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
    \\ metis_tac[])
  \\ `⊢ p` by (
    simp[Abbr`p`]
    \\ simp[wf_def,EVERY_MAP,UNCURRY]
    \\ fs[windmill_def,MAP_MAP_o]
    \\ simp[o_DEF,UNCURRY]
    \\ simp[GSYM o_DEF,GSYM MAP_MAP_o]
    \\ match_mp_tac ALL_DISTINCT_MAP_INJ
    \\ simp[] )
  \\ imp_res_tac pmov_MAP_INJ
  \\ simp[]
  \\ qspec_then`p`strip_assume_tac pmov_final
  \\ fs[]
  \\ simp[map_state_def]
QED

val _ = export_theory();
