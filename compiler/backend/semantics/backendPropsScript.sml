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

val FST_state_co = Q.store_thm("FST_state_co",
  `FST (state_co f co n) = SND(FST(co n))`,
  rw[state_co_def,UNCURRY]);

val SND_state_co = Q.store_thm("SND_state_co",
  `SND (state_co f co n) = SND (f (FST(FST(co n))) (SND(co n)))`,
  EVAL_TAC \\ pairarg_tac \\ fs[] \\ rw[UNCURRY]);

val pure_co_def = Define `
  pure_co f = I ## f`;

val SND_pure_co = Q.store_thm("SND_pure_co[simp]",
  `SND (pure_co co x) = co (SND x)`,
  Cases_on`x` \\ EVAL_TAC);

val FST_pure_co = Q.store_thm("FST_pure_co[simp]",
  `FST (pure_co co x) = FST x`,
  Cases_on`x` \\ EVAL_TAC);

val _ = export_theory();
