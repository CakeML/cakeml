(*
  A compiler phase that turns programs of the functional language BVI
  into the first imperative language of the CakeML compiler: dataLang.
*)
open preamble bviTheory dataLangTheory
     data_simpTheory data_liveTheory data_spaceTheory;

val _ = new_theory "bvi_to_data";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* compilation from BVI to dataLang *)

Theorem op_space_reset_pmatch:
  ! op.
  op_space_reset op =
    case op of
      Add => T
    | Sub => T
    | Mult => T
    | Div => T
    | Mod => T
    | Less => T
    | LessEq => T
    | Greater => T
    | GreaterEq => T
    | Equal => T
    | ListAppend => T
    | FromList _ => T
    | RefArray => T
    | RefByte _ => T
    | ConsExtend _ => T
    | CopyByte new_flag => new_flag
    | ConfigGC => T
    | FFI _ => T
    | _ => F
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> Cases_on `op` >> fs[op_space_reset_def]
QED

Theorem op_requires_names_eqn:
   ∀op. op_requires_names op =
    (op_space_reset op ∨ (dtcase op of
                          | FFI n => T
                          | Install => T
                          | CopyByte new_flag => T
                          | _ => F))
Proof
  Cases>>fs[op_requires_names_def]
QED

Theorem op_requires_names_pmatch:
   ∀op. op_requires_names op =
  (op_space_reset op ∨ (case op of
                        | FFI n => T
                        | Install => T
                        | CopyByte new_flag => T
                        | _ => F))
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)) >>
  fs[op_requires_names_eqn]
QED

val iAssign_def = Define `
  iAssign n1 op vs live env =
    if op_requires_names op then
      let xs = SOME (list_to_num_set (vs++live++env)) in
        if op = Greater then
          Assign n1 Less (REVERSE vs) xs
        else if op = GreaterEq then
          Assign n1 LessEq (REVERSE vs) xs
        else
          Assign n1 op vs xs
    else
      let k = op_space_req op (LENGTH vs) in
        if k = 0 then Assign n1 op vs NONE
          else Seq (MakeSpace k (list_to_num_set (vs++live++env)))
                   (Assign n1 op vs NONE)`;

val _ = Parse.hide"tail";

val compile_def = tDefine "compile" `
  (compile (n:num) (env:num list) tail live [] =
    (Skip,[]:num list,n)) /\
  (compile n env tail live (x::y::xs) =
     let (c1,v1,n1) = compile n env F live [x] in
     let (c2,vs,n2) = compile n1 env F (HD v1::live) (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (compile n env tail live [(Var v):bvi$exp] =
     let var = any_el v env 0n in
     if tail
     then (Return var, [n], n+1)
     else (Skip, [var], MAX n (var+1))) /\
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
     let ret = SOME (n2, list_to_num_set (live ++ env)) in
     let c3 = (if tail then Return n2 else Skip) in
       (Seq c1 (mk_ticks ticks (Seq (Call ret dest vs (SOME (n1,Seq c2 (Move n2 (HD v))))) c3)), [n2], n2+1))`
 (WF_REL_TAC `measure (exp2_size o SND o SND o SND o SND)`);

val compile_ind = theorem"compile_ind";

val compile_LESS_EQ_lemma = Q.prove(
  `!n env tail live xs.
      n <= SND (SND (compile n env tail live xs))`,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC);

Theorem compile_LESS_EQ:
   !n env tail live xs c vs new_var.
      (compile n env tail live xs = (c,vs,new_var)) ==> n <= new_var
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_LESS_EQ_lemma)
  \\ FULL_SIMP_TAC std_ss []
QED

val compile_LENGTH_lemma = Q.prove(
  `!n env tail live xs.
      (LENGTH (FST (SND (compile n env tail live xs))) = LENGTH xs)`,
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []);

Theorem compile_LENGTH:
   !n env tail live xs c vs new_var.
      (compile n env tail live xs = (c,vs,new_var)) ==> (LENGTH vs = LENGTH xs)
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_LENGTH_lemma)
  \\ FULL_SIMP_TAC std_ss []
QED

Theorem compile_SING_IMP:
   (compile n env tail live [x] = (c,vs,new_var)) ==> ?t. vs = [t]
Proof
  REPEAT STRIP_TAC \\ IMP_RES_TAC compile_LENGTH
  \\ Cases_on `vs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []
QED

(* combine dataLang optimisations *)

val optimise_def = Define `
  optimise prog = data_space$compile (simp (FST (data_live$compile prog LN)) Skip)`;

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
