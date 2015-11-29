open preamble bvlTheory;

val _ = new_theory "bvl_handle";

(* BVL transformation that introduces a Let into each Handle
   body. This is preparation for BVL --> BVI compilation. *)

val compile_def = tDefine "compile" `
  (compile n [] = []) /\
  (compile n (x::y::xs) = compile n [x] ++ compile n (y::xs)) /\
  (compile n [Var v] = if v < n then [Var v]
                       else [Op (Const 0) []]) /\
  (compile n [If x1 x2 x3] =
     [If (HD (compile n [x1])) (HD (compile n [x2])) (HD (compile n [x3]))]) /\
  (compile n [Let xs x2] =
     [Let (compile n xs) (HD (compile (n + LENGTH xs) [x2]))]) /\
  (compile n [Raise x1] =
     [Raise (HD (compile n [x1]))]) /\
  (compile n [Handle x1 x2] =
     let y1 = HD (compile n [x1]) in
     let y2 = HD (compile (n+1) [x2]) in
       [Handle (Let (GENLIST Var n) y1) y2]) /\
  (compile n [Op op xs] = [Op op (compile n xs)]) /\
  (compile n [Tick x] = [Tick (HD (compile n [x]))]) /\
  (compile n [Call t dest xs] = [Call t dest (compile n xs)])`
 (WF_REL_TAC `measure (exp1_size o SND)`);

val compile_ind = theorem"compile_ind";

val compile_length = Q.store_thm("compile_length[simp]",
  `!n xs. LENGTH (compile n xs) = LENGTH xs`,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [compile_def,ADD1,LET_DEF]
  \\ SRW_TAC [] [] \\ DECIDE_TAC);

val compile_HD_SING = store_thm("compile_HD_SING",
  ``[HD (compile n [x])] = compile n [x]``,
  MP_TAC (Q.SPECL [`n`,`[x]`] compile_length)
  \\ Cases_on `compile n [x]` \\ fs [LENGTH_NIL]);

val _ = export_theory();
