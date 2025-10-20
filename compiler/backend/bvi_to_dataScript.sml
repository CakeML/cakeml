(*
  A compiler phase that turns programs of the functional language BVI
  into the first imperative language of the CakeML compiler: dataLang.
*)
Theory bvi_to_data
Ancestors
  bvi dataLang data_simp data_live data_space
Libs
  preamble

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(* compilation from BVI to dataLang *)

Theorem op_space_reset_pmatch:
  ! op.
  op_space_reset op =
    case op of
      IntOp Add => T
    | IntOp Sub => T
    | IntOp Mult => T
    | IntOp Div => T
    | IntOp Mod => T
    | IntOp Less => T
    | IntOp LessEq => T
    | IntOp Greater => T
    | IntOp GreaterEq => T
    | BlockOp Equal => T
    | BlockOp ListAppend => T
    | BlockOp (FromList _) => T
    | BlockOp (ConsExtend _) => T
    | MemOp RefArray => T
    | MemOp (RefByte _) => T
    | MemOp (CopyByte new_flag) => new_flag
    | MemOp ConfigGC => T
    | FFI _ => T
    | _ => F
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> rpt CASE_TAC >> fs[op_space_reset_def]
QED

Theorem op_requires_names_eqn:
   ∀op. op_requires_names op =
    (op_space_reset op ∨ (dtcase op of
                          | FFI n => T
                          | Install => T
                          | MemOp (CopyByte new_flag) => T
                          | MemOp XorByte => T
                          | _ => F))
Proof
  strip_tac >> rpt CASE_TAC >> fs[op_requires_names_def]
QED

Theorem op_requires_names_pmatch:
   ∀op. op_requires_names op =
  (op_space_reset op ∨ (case op of
                        | FFI n => T
                        | Install => T
                        | MemOp (CopyByte new_flag) => T
                        | MemOp XorByte => T
                        | _ => F))
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)) >>
  fs[op_requires_names_eqn]
QED

Definition iAssign_def:
  iAssign n1 op vs live env =
    if op_requires_names op then
      let xs = SOME (list_to_num_set (vs++live++env)) in
        if op = IntOp Greater then
          Assign n1 (IntOp Less) (REVERSE vs) xs
        else if op = IntOp GreaterEq then
          Assign n1 (IntOp LessEq) (REVERSE vs) xs
        else
          Assign n1 op vs xs
    else
      let k = op_space_req op (LENGTH vs) in
        if k = 0 then Assign n1 op vs NONE
          else Seq (MakeSpace k (list_to_num_set (vs++live++env)))
                   (Assign n1 op vs NONE)
End

val _ = Parse.hide"tail";

Definition compile_def:
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
  (compile n env tail live [Force loc v] =
     let var = any_el v env 0n in
     let ret = (if tail then NONE
                else SOME (n, list_to_num_set (live ++ env))) in
       (Force ret loc var, [n], MAX (n+1) (var+1))) ∧
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
       (Seq c1 (mk_ticks ticks (Seq (Call ret dest vs (SOME (n1,Seq c2 (Move n2 (HD v))))) c3)), [n2], n2+1))
End

Definition compile_sing_def:
  (compile_sing n env tail live ((Var v):bvi$exp) =
     let var = any_el v env 0n in
     if tail
     then (Return var, n, n+1)
     else (Skip, var, MAX n (var+1))) /\
  (compile_sing n env tail live (If x1 x2 x3) =
     let (c1,v1,n1) = compile_sing n env F live x1 in
     let (c2,v2,n2) = compile_sing n1 env tail live x2 in
     let (c3,v3,n3) = compile_sing n2 env tail live x3 in
       if tail then
         (Seq c1 (If v1 c2 c3),n3,n3+1)
       else
         (Seq c1 (If v1 (Seq c2 (Move n3 v2))
                           (Seq c3 (Move n3 v3))),n3,n3+1)) /\
  (compile_sing n env tail live (Let xs x2) =
     let (c1,vs,n1) = compile_list n env live xs in
     let (c2,v2,n2) = compile_sing n1 (vs ++ env) tail live x2 in
       (Seq c1 c2, v2, n2)) /\
  (compile_sing n env tail live (Raise x1) =
     let (c1,v1,n1) = compile_sing n env F live x1 in
       (Seq c1 (Raise v1), v1, n1)) /\
  (compile_sing n env tail live (Op op xs) =
     let (c1,vs,n1) = compile_list n env live xs in
     let c2 = Seq c1 (iAssign n1 op (REVERSE vs) live env) in
       (if tail then Seq c2 (Return n1) else c2, n1, n1+1)) /\
  (compile_sing n env tail live (Tick x1) =
     let (c1,v1,n1) = compile_sing n env tail live x1 in
       (Seq Tick c1, v1, n1)) /\
  (compile_sing n env tail live (Force loc v) =
     let var = any_el v env 0n in
     let ret = (if tail then NONE
                else SOME (n, list_to_num_set (live ++ env))) in
       (Force ret loc var, n, MAX (n+1) (var+1))) ∧
  (compile_sing n env tail live (Call ticks dest xs NONE) =
     let (c1,vs,n1) = compile_list n env live xs in
     let ret = (if tail then NONE
                else SOME (n1, list_to_num_set (live ++ env))) in
       (Seq c1 (mk_ticks ticks (Call ret dest vs NONE)), n1, n1+1)) /\
  (compile_sing n env tail live (Call ticks dest xs (SOME handler)) =
     let (c1,vs,n1) = compile_list n env live xs in
     let (c2,v,n2) = compile_sing (n1+1) (n1::env) F live handler in
     let ret = SOME (n2, list_to_num_set (live ++ env)) in
     let c3 = (if tail then Return n2 else Skip) in
       (Seq c1 (mk_ticks ticks
          (Seq (Call ret dest vs (SOME (n1,Seq c2 (Move n2 v)))) c3)),
        n2, n2+1)) /\
  (compile_list (n:num) (env:num list) live [] =
    (Skip,[]:num list,n)) /\
  (compile_list n env live (x::xs) =
     let (c1,v1,n1) = compile_sing n env F live x in
       if NULL xs then (c1,[v1],n1) else
         let (c2,vs,n2) = compile_list n1 env (v1::live) xs in
           (Seq c1 c2, v1 :: vs, n2))
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL (n,env,t,l,x) => exp_size x
                            | INR (n,env,l,xs) => list_size exp_size xs’
  \\ simp[]
End

Theorem compile_sing_eq:
  (∀n env t l x c1 v1 n1.
     compile_sing n env t l x = (c1,v1,n1) ⇒
     compile n env t l [x] = (c1,[v1],n1)) ∧
  (∀n env l xs.
     compile_list n env l xs =
     compile n env F l xs)
Proof
  ho_match_mp_tac compile_sing_ind \\ rw []
  \\ once_rewrite_tac [compile_sing_def,compile_def] \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [compile_sing_def]
  \\ rpt (IF_CASES_TAC \\ gvs [])
  \\ rpt (pairarg_tac \\ gvs [])
  \\ Cases_on ‘xs’ \\ gvs [compile_sing_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [compile_def]
QED

Triviality compile_LESS_EQ_lemma:
  !n env tail live xs.
      n <= SND (SND (compile n env tail live xs))
Proof
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [] \\ DECIDE_TAC
QED

Theorem compile_LESS_EQ:
   !n env tail live xs c vs new_var.
      (compile n env tail live xs = (c,vs,new_var)) ==> n <= new_var
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL compile_LESS_EQ_lemma)
  \\ FULL_SIMP_TAC std_ss []
QED

Triviality compile_LENGTH_lemma:
  !n env tail live xs.
      (LENGTH (FST (SND (compile n env tail live xs))) = LENGTH xs)
Proof
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [compile_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []
QED

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

Definition optimise_def:
  optimise prog = data_space$compile (simp (FST (data_live$compile prog LN)) Skip)
End

(* the top-level compiler includes the optimisations, because the correctness
   proofs are combined *)

Definition compile_exp_def:
  compile_exp arg_count exp =
    optimise (FST (compile arg_count (COUNT_LIST arg_count) T [] [exp]))
End

Definition compile_part_def:
  compile_part (name:num, arg_count, exp) =
    (name, arg_count, compile_exp arg_count exp)
End

Definition compile_prog_def:
  compile_prog prog = MAP compile_part prog
End

Theorem compile_exp_eq:
  compile_exp arg_count exp =
    optimise (FST (compile_sing arg_count (COUNT_LIST arg_count) T [] exp))
Proof
  ‘∃z. compile_sing arg_count (COUNT_LIST arg_count) T [] exp = z’ by fs []
  \\ PairCases_on ‘z’ \\ gvs []
  \\ drule $ cj 1 compile_sing_eq
  \\ gvs [compile_exp_def]
QED

