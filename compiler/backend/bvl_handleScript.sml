(*
  BVL transformation that introduces a Let into each Handle
  body. This is preparation for BVL --> BVI compilation.  This phase
  also removes Handles in case the body cannot raise an exception.
*)
open preamble bvlTheory db_varsTheory bvl_constTheory;

val _ = new_theory "bvl_handle";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val SmartLet_def = Define `
  SmartLet xs x = if NULL xs then x else Let xs x`

val LetLet_def = Define `
  LetLet env_length fvs (body:bvl$exp) =
    let xs = GENLIST I env_length in
    let zs = FILTER (\n. IS_SOME (lookup n fvs)) xs in
    let ys = MAPi (\i x. (x,i)) zs in
    let long_list = GENLIST (\n. dtcase ALOOKUP ys n of
                                 | NONE => Op (Const 0) []
                                 | SOME k => Var k) env_length in
      Let (MAP Var zs) (SmartLet long_list body)`;

val OptionalLetLet_def = Define `
  OptionalLetLet e env_size live s (limit:num) (nr:bool) =
    if s < limit then ([e],live,s,nr) else
      let fvs = db_to_set live in
      let flat_live = vars_from_list (MAP FST (toAList fvs)) in
        ([(Let [] (LetLet env_size fvs e))],flat_live,0n,nr)`;

val compile_def = tDefine "compile" `
  (compile l n [] = ([]:bvl$exp list,Empty,0n,T)) /\
  (compile l n (x::y::xs) =
     let (dx,lx,s1,nr1) = compile l n [x] in
     let (dy,ly,s2,nr2) = compile l n (y::xs) in
       (dx ++ dy, mk_Union lx ly, s1+s2, nr1 /\ nr2)) /\
  (compile l n [Var v] = if v < n then ([Var v],Var v,1,T)
                         else ([Op (Const 0) []],Empty,1,T)) /\
  (compile l n [If x1 x2 x3] =
     let (x1,l1,s1,nr1) = compile l n [x1] in
     let (x2,l2,s2,nr2) = compile l n [x2] in
     let (x3,l3,s3,nr3) = compile l n [x3] in
       OptionalLetLet (If (HD x1) (HD x2) (HD x3)) n
         (mk_Union l1 (mk_Union l2 l3)) (s1+s2+s3+1) l
         (nr1 /\ nr2 /\ nr3)) /\
  (compile l n [Let xs x2] =
     if NULL xs then
       compile l n [x2]
     else
       let k = LENGTH xs in
       let (xs,l1,s1,nr1) = compile l n xs in
       let (x2,l2,s2,nr2) = compile l (n + k) [x2] in
         OptionalLetLet (Let xs (HD x2)) n
           (mk_Union l1 (Shift k l2)) (s1+s2+1) l (nr1 /\ nr2)) /\
  (compile l n [Handle x1 x2] =
     let (y1,l1,s1,nr1) = compile l n [x1] in
       if nr1 then (y1,l1,s1,T) else
         let (y2,l2,s2,nr2) = compile l (n+1) [x2] in
           ([Handle (LetLet n (db_to_set l1) (HD y1)) (HD y2)],
            mk_Union l1 (Shift 1 l2),
            s2 (* s1 intentionally left out because
                  it does not contrib to exp size in BVI *), nr2)) /\
  (compile l n [Raise x1] =
     let (dx,lx,s1,nr1) = compile l n [x1] in
       OptionalLetLet (Raise (HD dx)) n lx (s1+1) l F) /\
  (compile l n [Op op xs] =
     let (ys,lx,s1,nr1) = compile l n xs in
       OptionalLetLet (Op op ys) n lx (s1+1) l nr1) /\
  (compile l n [Tick x] =
     let (y,lx,s1,nr1) = compile l n [x] in
       ([Tick (HD y)],lx,s1,nr1)) /\
  (compile l n [Call t dest xs] =
     let (ys,lx,s1,nr1) = compile l n xs in
       OptionalLetLet (Call t dest ys) n lx (s1+1) l F)`
 (WF_REL_TAC `measure (bvl$exp1_size o SND o SND)`);

val compile_ind = theorem"compile_ind";

val compile_exp_def = Define `
  compile_exp cut_size arity e =
    HD (FST (compile cut_size arity [bvl_const$compile_exp e]))`;

val dest_Seq_def = Define `
  (dest_Seq (Let [e1;e2] (Var 1)) = SOME (e1,e2)) /\
  (dest_Seq _ = NONE)`

Theorem dest_Seq_pmatch:
  ∀exp.
  dest_Seq exp =
    case exp of
      Let [e1;e2] (Var 1) => SOME (e1,e2)
     | _ => NONE
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[dest_Seq_def]
QED

val compile_seqs_def = tDefine "compile_seqs" `
  compile_seqs cut_size e acc =
    dtcase dest_Seq e of
    | NONE => (let new_e = compile_exp cut_size 0 e in
                 dtcase acc of
                 | NONE => new_e
                 | SOME rest => Let [new_e] (Let [] (Let [] rest)))
    | SOME (e1,e2) =>
        compile_seqs cut_size e1
          (SOME (compile_seqs cut_size e2 acc))`
  ((WF_REL_TAC ` measure (\(c,e,a). exp_size e) `
    \\ strip_tac \\ HO_MATCH_MP_TAC (fetch "-" "dest_Seq_ind")
    \\ fs [dest_Seq_def] \\ EVAL_TAC \\ fs []):tactic);

val compile_any_def = Define `
  compile_any split_seq cut_size arity e =
    if (arity = 0) /\ split_seq then
      compile_seqs cut_size e NONE
    else
      compile_exp cut_size arity e`;

Theorem compile_length[simp]:
   !l n xs. LENGTH (FST (compile l n xs)) = LENGTH xs
Proof
  HO_MATCH_MP_TAC compile_ind \\ REPEAT STRIP_TAC
  \\ fs [compile_def,ADD1,LET_DEF]
  \\ rpt (pairarg_tac \\ fs []) \\ rw [OptionalLetLet_def]
QED

Theorem compile_sing:
   compile l n [x] = (dx,lx,s) ==> ?y. dx = [y]
Proof
  `LENGTH (FST (compile l n [x])) = LENGTH [x]` by fs []
  \\ rpt strip_tac \\ full_simp_tac std_ss [LENGTH]
  \\ Cases_on `dx` \\ fs [LENGTH_NIL]
QED

val compile_seqs_compute = save_thm("compile_seqs_compute",
  LIST_CONJ [
    compile_seqs_def
    |> Q.SPECL [`e`,`c`,`NONE`]
    |> SIMP_RULE std_ss [LET_THM],
    compile_seqs_def
    |> Q.SPECL [`e`,`c`,`SOME y`]
    |> SIMP_RULE std_ss [LET_THM]]);

val _ = export_theory();
