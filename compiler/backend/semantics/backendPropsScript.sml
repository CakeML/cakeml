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

Theorem oracle_monotonic_subset:
  ((St' SUBSET St) /\ (!n. f' (co' n) SUBSET f (co n))) ==>
  oracle_monotonic f R St co ==>
  oracle_monotonic f' R St' co'
Proof
  fs [oracle_monotonic_def, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem oracle_monotonic_shift_subset:
  ((St' SUBSET (IMAGE ((+) (i : num)) St UNION count i)) /\
    (!n. f' (co' n) SUBSET (IMAGE ((+) i) (f (co n))))) ==>
  oracle_monotonic f (<) St co ==>
  oracle_monotonic f' (<) St' co'
Proof
  fs [oracle_monotonic_def]
  \\ rw []
  \\ fs [SUBSET_DEF]
  \\ rpt (first_x_assum (fn t => drule t \\ imp_res_tac t))
  \\ fs []
QED

(* oracles that carry around state values that can also be constructed by
   repeatedly applying the incremental compiler *)
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

val _ = export_theory();
