(*
  General definitions and theorems that are useful within the proofs
  about the compiler backend.
*)
open preamble

val _ = new_theory"backendProps";

val state_cc_def = Define `
  state_cc f cc =
    (\(state,cfg) prog.
       let (state1,prog1) = f state prog in
         case cc cfg prog1 of
         | NONE => NONE
         | SOME (code,data,cfg1) => SOME (code,data,state1,cfg1))`;

val pure_cc_def = Define `
  pure_cc f cc =
    (\cfg prog.
       let prog1 = f prog in
         cc cfg prog1)`;

val state_co_def = Define `
  state_co f co =
     (λn.
        (let
           ((state,cfg),progs) = co n ;
           (state1,progs) = f state progs
         in
           (cfg,progs)))`;

Theorem FST_state_co
  `FST (state_co f co n) = SND(FST(co n))`
  (rw[state_co_def,UNCURRY]);

Theorem SND_state_co
  `SND (state_co f co n) = SND (f (FST(FST(co n))) (SND(co n)))`
  (EVAL_TAC \\ pairarg_tac \\ fs[] \\ rw[UNCURRY]);

val pure_co_def = Define `
  pure_co f = I ## f`;

Theorem SND_pure_co[simp]
  `SND (pure_co co x) = co (SND x)`
  (Cases_on`x` \\ EVAL_TAC);

Theorem FST_pure_co[simp]
  `FST (pure_co co x) = FST x`
  (Cases_on`x` \\ EVAL_TAC);

Theorem pure_co_comb_pure_co:
  pure_co f o pure_co g o co = pure_co (f o g) o co
Proof
  rw [FUN_EQ_THM, pure_co_def]
  \\ Cases_on `co x`
  \\ fs []
QED

Theorem pure_co_I:
  pure_co I = I
Proof
  fs [FUN_EQ_THM, FORALL_PROD, pure_co_def]
QED

Theorem pure_cc_I:
  pure_cc I = I
Proof
  fs [FUN_EQ_THM, FORALL_PROD, pure_cc_def]
QED

(* somewhat generic wrappers for defining standard properties about oracles *)

(* identifiers that appear in the initial state and in oracle steps
   increase monotonically in some sense. *)
val oracle_monotonic_def = Define`
  oracle_monotonic (f : 'a -> 'b set) (R : 'b -> 'b -> bool) (S : 'b set)
    (orac : num -> 'a) =
    ((!i j x y. i < j /\ x IN f (orac i) /\ y IN f (orac j) ==> R x y)
        /\ (! i x y. x IN S /\ y IN f (orac i) ==> R x y))`;

val conjs = MATCH_MP quotientTheory.EQ_IMPLIES (SPEC_ALL oracle_monotonic_def)
  |> UNDISCH_ALL |> CONJUNCTS |> map DISCH_ALL

Theorem oracle_monotonic_step = hd conjs;
Theorem oracle_monotonic_init = hd (tl conjs);

Theorem oracle_monotonic_step2:
  oracle_monotonic f R St orac ⇒
     ∀i j x y. x ∈ f (orac i) ∧ y ∈ f (orac j) ∧ i < j ⇒ R x y
Proof
  metis_tac [oracle_monotonic_step]
QED

Theorem oracle_monotonic_subset:
  ((St' ⊆ St) /\ (!n. f' (co' n) ⊆ f (co n))) ==>
  oracle_monotonic f R St co ==>
  oracle_monotonic f' R St' co'
Proof
  fs [oracle_monotonic_def, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem oracle_monotonic_shift_subset:
  ((St' ⊆ (IMAGE ((+) (i : num)) St ∪ count i)) /\
    (!n. f' (co' n) ⊆ (IMAGE ((+) i) (f (co n))))) ==>
  oracle_monotonic f (<) St co ==>
  oracle_monotonic f' (<) St' co'
Proof
  fs [oracle_monotonic_def]
  \\ rw []
  \\ fs [SUBSET_DEF]
  \\ rpt (first_x_assum (fn t => drule t \\ imp_res_tac t))
  \\ fs []
QED

Theorem oracle_monotonic_shift_seq:
  !i. (oracle_monotonic f R St co /\ i > 0 /\
    St' ⊆ f (co (i - 1)) ∪ St ==>
    oracle_monotonic f R St' (shift_seq i co)
  )
Proof
  rw [] \\ rw [oracle_monotonic_def]
  \\ fs [shift_seq_def]
  \\ imp_res_tac SUBSET_IMP
  \\ fs []
  \\ TRY (
    drule oracle_monotonic_step2
    \\ disch_then match_mp_tac
    \\ rpt (asm_exists_tac \\ fs [])
    \\ NO_TAC
  )
  \\ drule oracle_monotonic_init
  \\ disch_then match_mp_tac
  \\ rpt (asm_exists_tac \\ fs [])
QED

Theorem oracle_monotonic_DISJOINT_init:
  !i. oracle_monotonic f R St co /\ irreflexive R
    ==> DISJOINT St (f (co i))
Proof
  metis_tac [oracle_monotonic_init, irreflexive_def, IN_DISJOINT]
QED

(* check that an oracle with config values lists the config values that
   would be produced by the incremental compiler. *)
val is_state_oracle_def = Define`
  is_state_oracle compile_inc_f co init_state =
    ((FST (FST (co 0)) = init_state) /\ (!n. FST (FST (co (SUC n)))
        = FST (compile_inc_f (FST (FST (co n))) (SND (co n)))))`;

Theorem is_state_oracle_shift:
  is_state_oracle compile_inc_f co st =
  (FST (FST (co 0)) = st /\ is_state_oracle compile_inc_f (shift_seq 1 co)
        (FST (compile_inc_f st (SND (co 0)))))
Proof
  fs [is_state_oracle_def, shift_seq_def]
  \\ EQ_TAC \\ rw [] \\ fs [sptreeTheory.ADD_1_SUC]
  \\ full_simp_tac bool_ss [arithmeticTheory.ONE]
  \\ Cases_on `n`
  \\ fs []
QED

Theorem is_state_oracle_0:
  is_state_oracle comp_inc co st ==> FST (FST (co 0)) = st
Proof
  fs [is_state_oracle_def]
QED

Theorem is_state_oracle_k:
  !k. is_state_oracle compile_inc_f co st ==>
  ?st oth_st prog. co k = ((st, oth_st), prog)
    /\ FST (FST (co (SUC k))) = FST (compile_inc_f st prog)
Proof
  rw []
  \\ Cases_on `co k`
  \\ Cases_on `FST (co k)`
  \\ fs [is_state_oracle_def]
  \\ rfs []
QED

Theorem is_state_oracle_IMP_EQ:
  is_state_oracle inc_f co st ==>
  !st'. is_state_oracle inc_f co st' <=> (st' = st)
Proof
  fs [is_state_oracle_def] \\ metis_tac []
QED

(* inverse combinators for building up the config part of an oracle *)

val syntax_to_full_oracle_def = Define `
  syntax_to_full_oracle mk progs i = (mk progs i,progs i)`;

val state_orac_states_def = Define `
  state_orac_states f st progs 0 = st /\
  state_orac_states f st progs (SUC n) = let
    (st1, _) = f st (progs 0) in state_orac_states f st1 (shift_seq 1 progs) n`;

val state_co_progs_def = Define `
  state_co_progs f st orac = let
    states = state_orac_states f st orac;
  in \i. SND (f (states i) (orac i))`;

val add_state_co_def = Define `
  add_state_co f st mk progs = let
    states = state_orac_states f st progs;
    next_progs = state_co_progs f st progs;
    next_orac = mk next_progs in
    (\i. (states i, next_orac i))`;

Theorem state_co_add_state_co:
  state_co f (syntax_to_full_oracle (add_state_co f st mk) progs)
    = syntax_to_full_oracle mk (state_co_progs f st progs)
Proof
  rw [FUN_EQ_THM]
  \\ fs [state_co_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [syntax_to_full_oracle_def, add_state_co_def]
  \\ simp [state_co_progs_def]
QED

val pure_co_progs_def = Define `
  pure_co_progs f (orac : num -> 'a) = f o orac`;

Theorem pure_co_syntax_to_full_oracle:
  pure_co f o (syntax_to_full_oracle (mk o pure_co_progs f) progs) =
    syntax_to_full_oracle mk (pure_co_progs f progs)
Proof
  rw [FUN_EQ_THM]
  \\ fs [pure_co_def, syntax_to_full_oracle_def, pure_co_progs_def]
QED

Theorem state_orac_states_add:
  !i j progs st.
  state_orac_states f (state_orac_states f st progs i) (shift_seq i progs) j =
  state_orac_states f st progs (i + j)
Proof
  Induct
  \\ fs [state_orac_states_def, Q.SPEC `0` shift_seq_def, ETA_THM]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ first_x_assum (qspecl_then [`j`, `shift_seq 1 progs`] mp_tac)
  \\ fs [shift_seq_def, GSYM ADD1]
  \\ REWRITE_TAC [GSYM arithmeticTheory.ADD_SUC, state_orac_states_def]
  \\ fs [shift_seq_def, ADD1]
QED

Theorem is_state_oracle_add_state_co:
  is_state_oracle f (syntax_to_full_oracle (add_state_co f st mk) progs) st0
    <=> st0 = st
Proof
  fs [is_state_oracle_def, syntax_to_full_oracle_def, add_state_co_def]
  \\ fs [state_orac_states_def]
  \\ Cases_on `st0 = st` \\ fs []
  \\ rw []
  \\ pairarg_tac \\ fs []
  \\ Q.ISPECL_THEN [`f`, `n`, `1`, `progs`, `st`] mp_tac
    (GEN_ALL state_orac_states_add)
  \\ REWRITE_TAC [ONE, state_orac_states_def]
  \\ fs []
  \\ fs [GSYM ADD1, state_orac_states_def]
  \\ fs [shift_seq_def, UNCURRY]
QED

val _ = export_theory();
