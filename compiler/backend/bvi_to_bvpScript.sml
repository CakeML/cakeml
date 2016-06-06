open preamble bviTheory bvpTheory
     bvp_simpTheory bvp_liveTheory bvp_spaceTheory;

val _ = new_theory "bvi_to_bvp";

(* compilation from BVI to BVP *)

val op_space_reset_def = Define `
  (op_space_reset Add = T) /\
  (op_space_reset Sub = T) /\
  (op_space_reset Mult = T) /\
  (op_space_reset Div = T) /\
  (op_space_reset Mod = T) /\
  (op_space_reset (FromList _) = T) /\
  (op_space_reset RefArray = T) /\
  (op_space_reset RefByte = T) /\
  (op_space_reset _ = F)`;

val op_requires_names_def = Define`
  op_requires_names op = (op_space_reset op ∨ (∃n. op = FFI n))`;

val op_requires_names_eqn = store_thm("op_requires_names_eqn",
  ``∀op. op_requires_names op =
    (op_space_reset op ∨ (case op of FFI n => T | _ => F))``,
    Cases>>fs[op_requires_names_def])

val iAssign_def = Define `
  iAssign n1 op vs live env =
    if op_requires_names op then
      Assign n1 op vs (SOME (list_to_num_set (vs++live++env)))
    else
      let k = op_space_req op (LENGTH vs) in
        if k = 0 then Assign n1 op vs NONE
          else Seq (MakeSpace k (list_to_num_set (vs++live++env)))
                   (Assign n1 op vs NONE)`;

val compile_def = tDefine "compile" `
  (compile (n:num) (env:num list) tail live [] =
    (Skip,[]:num list,n)) /\
  (compile n env tail live (x::y::xs) =
     let (c1,v1,n1) = compile n env F live [x] in
     let (c2,vs,n2) = compile n1 env F (HD v1::live) (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (compile n env tail live [(Var v):bvi$exp] =
     if tail
     then (Return (EL v env), [n], n+1)
     else (Move n (EL v env), [n], n+1)) /\
  (compile n env tail live [If x1 x2 x3] =
     let (c1,v1,n1) = compile n env F live [x1] in
     let (c2,v2,n2) = compile n1 env tail live [x2] in
     let (c3,v3,n3) = compile n2 env tail live [x3] in
       if tail then
         (Seq c1 (If (HD v1) c2 c3),[n3],n3+1)
       else
         (Seq c1 (If (HD v1) (Seq c2 (Move n3 (HD v2)))
                             (Seq c3 (Move n3 (HD v3)))),[n3],n3+1)) /\
  (compile n env tail live [Let xs x2] =
     let (c1,vs,n1) = compile n env F live xs in
     let (c2,v2,n2) = compile n1 (vs ++ env) tail live [x2] in
       (Seq c1 c2, v2, n2)) /\
  (compile n env tail live [Raise x1] =
     let (c1,v1,n1) = compile n env F live [x1] in
       (Seq c1 (Raise (HD v1)), v1, n1)) /\
  (compile n env tail live [Op op xs] =
     let (c1,vs,n1) = compile n env F live xs in
     let c2 = Seq c1 (iAssign n1 op (REVERSE vs) live env) in
       (if tail then Seq c2 (Return n1) else c2, [n1], n1+1)) /\
  (compile n env tail live [Tick x1] =
     let (c1,v1,n1) = compile n env tail live [x1] in
       (Seq Tick c1, v1, n1)) /\
  (compile n env tail live [Call ticks dest xs NONE] =
     let (c1,vs,n1) = compile n env F live xs in
     let ret = (if tail then NONE
                else SOME (n1, list_to_num_set (live ++ env))) in
       (Seq c1 (mk_ticks ticks (Call ret dest vs NONE)), [n1], n1+1)) /\
  (compile n env tail live [Call ticks dest xs (SOME handler)] =
     let (c1,vs,n1) = compile n env F live xs in
     let (c2,v,n2) = compile (n1+1) (n1::env) F live [handler] in
     let ret = SOME (HD v, list_to_num_set (live ++ env)) in
     let c3 = (if tail then Return (HD v) else Skip) in
       (Seq c1 (mk_ticks ticks (Seq (Call ret dest vs (SOME (n1,c2))) c3)), v, n2))`
 (WF_REL_TAC `measure (exp2_size o SND o SND o SND o SND)`);

val compile_ind = theorem"compile_ind";

val compile_LESS_EQ_lemma = prove(
  ``!n env tail live xs.
      n <= SND (SND (compile n env tail live xs))``,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

val compile_LESS_EQ = store_thm("compile_LESS_EQ",
  ``!n env tail live xs c vs new_var.
      (compile n env tail live xs = (c,vs,new_var)) ==> n <= new_var``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_LESS_EQ_lemma)
  \\ FULL_SIMP_TAC std_ss []);

val compile_LENGTH_lemma = prove(
  ``!n env tail live xs.
      (LENGTH (FST (SND (compile n env tail live xs))) = LENGTH xs)``,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []);

val compile_LENGTH = store_thm("compile_LENGTH",
  ``!n env tail live xs c vs new_var.
      (compile n env tail live xs = (c,vs,new_var)) ==> (LENGTH vs = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_LENGTH_lemma)
  \\ FULL_SIMP_TAC std_ss []);

val compile_SING_IMP = store_thm("compile_SING_IMP",
  ``(compile n env tail live [x] = (c,vs,new_var)) ==> ?t. vs = [t]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC compile_LENGTH
  \\ Cases_on `vs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []);

(* combine bvp optimisations *)

val optimise_def = Define `
  optimise prog = bvp_space$compile (simp (FST (bvp_live$compile prog LN)) Skip)`;

(* the top-level compiler includes the optimisations, because the correctness
   proofs are combined *)

val compile_exp = Define `
  compile_exp arg_count exp =
    optimise (FST (compile arg_count (COUNT_LIST arg_count) T [] [exp]))`

val compile_part = Define `
  compile_part (name:num, arg_count, exp) =
    (name, arg_count, compile_exp arg_count exp)`

val compile_prog_def = Define `
  compile_prog prog = MAP compile_part prog`;

val _ = export_theory();
