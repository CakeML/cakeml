open preamble bvlTheory clos_to_bvlTheory;

val _ = new_theory "bvl_inline";

(* A function that inlines a function body *)

val inline_def = tDefine "inline" `
  (inline n code arity [] = []) /\
  (inline n code arity (x::y::xs) =
     HD (inline n code arity [x]) :: inline n code arity (y::xs)) /\
  (inline n code arity [Var v] = [Var v]) /\
  (inline n code arity [If x1 x2 x3] =
     [If (HD (inline n code arity [x1]))
         (HD (inline n code arity [x2]))
         (HD (inline n code arity [x3]))]) /\
  (inline n code arity [Let xs x2] =
     [Let (inline n code arity xs)
           (HD (inline n code arity [x2]))]) /\
  (inline n code arity [Raise x1] =
     [Raise (HD (inline n code arity [x1]))]) /\
  (inline n code arity [Handle x1 x2] =
     [Handle (HD (inline n code arity [x1]))
              (HD (inline n code arity [x2]))]) /\
  (inline n code arity [Op op xs] =
     [Op op (inline n code arity xs)]) /\
  (inline n code arity [Tick x] =
     [Tick (HD (inline n code arity [x]))]) /\
  (inline n code arity [Call ticks dest xs] =
     if (dest = SOME n) /\ (LENGTH xs = arity)
     then [Let (inline n code arity xs) (mk_tick (SUC ticks) code)]
     else [Call ticks dest (inline n code arity xs)])`
  (WF_REL_TAC `measure (exp1_size o SND o SND o SND)`);

val inline_ind = theorem"inline_ind";

val LENGTH_inline = store_thm("LENGTH_inline",
  ``!n code arity xs. LENGTH (inline n code arity xs) = LENGTH xs``,
  recInduct inline_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [Once inline_def,LET_DEF] \\ SRW_TAC [] []);

val HD_inline = store_thm("HD_inline",
  ``[HD (inline n code arity [x])] = inline n code arity [x]``,
  `LENGTH (inline n code arity [x]) = LENGTH [x]` by SRW_TAC [] [LENGTH_inline]
  \\ Cases_on `inline n code arity [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC);

val _ = export_theory();
