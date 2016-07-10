open preamble bvlTheory db_varsTheory;

val _ = new_theory "bvl_handle";

(* BVL transformation that introduces a Let into each Handle
   body. This is preparation for BVL --> BVI compilation.  This phase
   also removes Handles in case the body cannot raise an exception. *)

val no_raise_def = tDefine "no_raise" `
  (no_raise [] <=> T) /\
  (no_raise (x::y::xs) <=> no_raise [x] /\ no_raise (y::xs)) /\
  (no_raise [Var v] <=> T) /\
  (no_raise [If x1 x2 x3] <=>
     no_raise [x1] /\ no_raise [x2] /\ no_raise [x3]) /\
  (no_raise [Let xs x2] <=>
     no_raise xs /\ no_raise [x2]) /\
  (no_raise [Raise x1] <=> F) /\
  (no_raise [Handle x1 x2] <=> no_raise [x2]) /\
  (no_raise [Op op xs] <=> no_raise xs) /\
  (no_raise [Tick x] <=> no_raise [x]) /\
  (no_raise [Call t dest xs] <=> F)`
 (WF_REL_TAC `measure exp1_size`);

val LetLet_def = Define `
  LetLet env_length fvs (body:bvl$exp) =
    let xs = GENLIST I env_length in
    let zs = FILTER (\n. has_var n fvs) xs in
    let ys = MAPi (\i x. (x,i)) zs in
    let long_list = GENLIST (\n. case ALOOKUP ys n of
                                 | NONE => Op (Const 0) []
                                 | SOME k => Var k) env_length in
      Let (MAP Var zs) (Let long_list body)`

val compile_def = tDefine "compile" `
  (compile n [] = ([]:bvl$exp list,Empty,0n)) /\
  (compile n (x::y::xs) =
     let (dx,lx,s1) = compile n [x] in
     let (dy,ly,s2) = compile n (y::xs) in
       (dx ++ dy, mk_Union lx ly, s1+s2)) /\
  (compile n [Var v] = if v < n then ([Var v],Var v,1)
                       else ([Op (Const 0) []],Empty,1)) /\
  (compile n [If x1 x2 x3] =
     let (x1,l1,s1) = compile n [x1] in
     let (x2,l2,s2) = compile n [x2] in
     let (x3,l3,s3) = compile n [x3] in
       ([If (HD x1) (HD x2) (HD x3)],mk_Union l1 (mk_Union l2 l3),s1+s2+s3+1)) /\
  (compile n [Let xs x2] =
     if LENGTH xs = 0 then
       compile n [x2]
     else
       let k = LENGTH xs in
       let (xs,l1,s1) = compile n xs in
       let (x2,l2,s2) = compile (n + k) [x2] in
         ([Let xs (HD x2)],mk_Union l1 (Shift k l2),s1+s2+1)) /\
  (compile n [Handle x1 x2] =
     let (y1,l1,s1) = compile n [x1] in
       if no_raise y1 then (y1,l1,s1) else
         let (y2,l2,s2) = compile (n+1) [x2] in
           ([Handle (LetLet n l1 (HD y1)) (HD y2)],
            mk_Union l1 (Shift 1 l2),
            s2 (* s1 intentionally left out because
                  it does not contrib to exp size in BVI *))) /\
  (compile n [Raise x1] =
     let (dx,lx,s1) = compile n [x1] in
       ([Raise (HD dx)],lx,s1+1)) /\
  (compile n [Op op xs] =
     let (ys,l,s1) = compile n xs in
       ([Op op ys],l,s1+1)) /\
  (compile n [Tick x] =
     let (y,l,s1) = compile n [x] in
       ([Tick (HD y)],l,s1)) /\
  (compile n [Call t dest xs] =
     let (ys,l,s1) = compile n xs in
       ([Call t dest ys],l,s1+1))`
 (WF_REL_TAC `measure (bvl$exp1_size o SND)`);

val compile_ind = theorem"compile_ind";

val compile_exp_def = Define `
  compile_exp arity e = HD (FST (compile arity [e]))`;

val compile_length = Q.store_thm("compile_length[simp]",
  `!n xs. LENGTH (FST (compile n xs)) = LENGTH xs`,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ fs [compile_def,ADD1,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []);

val compile_sing = store_thm("compile_sing",
  ``compile n [x] = (dx,l,s) ==> ?y. dx = [y]``,
  `LENGTH (FST (compile n [x])) = LENGTH [x]` by fs []
  \\ rpt strip_tac \\ full_simp_tac std_ss [LENGTH]
  \\ Cases_on `dx` \\ fs [LENGTH_NIL]);

val _ = export_theory();
