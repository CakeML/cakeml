open preamble bvlTheory clos_to_bvlTheory;

val _ = new_theory "bvl_inline";

(* A function that inlines a function body *)

val inline_def = tDefine "inline" `
  (inline cs [] = []) /\
  (inline cs (x::y::xs) =
     HD (inline cs [x]) :: inline cs (y::xs)) /\
  (inline cs [Var v] = [Var v]) /\
  (inline cs [If x1 x2 x3] =
     [If (HD (inline cs [x1]))
         (HD (inline cs [x2]))
         (HD (inline cs [x3]))]) /\
  (inline cs [Let xs x2] =
     [Let (inline cs xs)
           (HD (inline cs [x2]))]) /\
  (inline cs [Raise x1] =
     [Raise (HD (inline cs [x1]))]) /\
  (inline cs [Handle x1 x2] =
     [Handle (HD (inline cs [x1]))
              (HD (inline cs [x2]))]) /\
  (inline cs [Op op xs] =
     [Op op (inline cs xs)]) /\
  (inline cs [Tick x] =
     [Tick (HD (inline cs [x]))]) /\
  (inline cs [Call ticks dest xs] =
     case dest of NONE => [Call ticks dest (inline cs xs)] | SOME n =>
     case lookup n cs of
     | NONE => [Call ticks dest (inline cs xs)]
     | SOME (arity,code) => [Let (inline cs xs) (mk_tick (SUC ticks) code)])`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val inline_ind = theorem"inline_ind";

val LENGTH_inline = store_thm("LENGTH_inline",
  ``!cs xs. LENGTH (inline cs xs) = LENGTH xs``,
  recInduct inline_ind \\ REPEAT STRIP_TAC
  \\ fs [Once inline_def,LET_DEF] \\ rw [] \\ every_case_tac \\ fs []);

val HD_inline = store_thm("HD_inline[simp]",
  ``[HD (inline cs [x])] = inline cs [x]``,
  `LENGTH (inline cs [x]) = LENGTH [x]` by SRW_TAC [] [LENGTH_inline]
  \\ Cases_on `inline cs [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC);

val _ = export_theory();
