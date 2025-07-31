(*
  BVL transformation that introduces a Let into each Handle
  body. This is preparation for BVL --> BVI compilation.  This phase
  also removes Handles in case the body cannot raise an exception.
*)
open preamble bvlTheory db_varsTheory bvl_constTheory;

val _ = new_theory "bvl_handle";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition can_raise_def:
  (can_raise (Var v) = F) ∧
  (can_raise (If x1 x2 x3) = (can_raise x1 ∨ can_raise x2 ∨ can_raise x3)) ∧
  (can_raise (Let xs x2) = (can_raise x2 ∨ can_raise1 xs)) ∧
  (can_raise (Handle x1 x2) = can_raise x2) ∧
  (can_raise (Raise x1) = T) ∧
  (can_raise (Op op xs) = (op = ThunkOp ForceThunk ∨ can_raise1 xs)) ∧
  (can_raise (Tick x) = can_raise x) ∧
  (can_raise (Call t dest xs) = T) ∧
  (can_raise1 [] = F) ∧
  (can_raise1 (x::xs) = (can_raise x ∨ can_raise1 xs))
End

Definition dest_handle_Raise_def:
  dest_handle_Raise (Raise x) = (if can_raise x then NONE else SOME x) ∧
  dest_handle_Raise _ = NONE
End

Definition dest_handle_Let_def:
  dest_handle_Let (Let xs x) = (if can_raise1 xs then NONE else SOME (xs,x)) ∧
  dest_handle_Let _ = NONE
End

Definition dest_handle_If_def:
  dest_handle_If (If x1 x2 x3) =
    (if can_raise x1 then NONE else
     if can_raise x2 then (if can_raise x3 then NONE else SOME (INL (x1,x2,x3))) else
     if can_raise x3 then (if can_raise x2 then NONE else SOME (INR (x1,x2,x3))) else
       NONE) ∧
  dest_handle_If _ = NONE
End

Definition handle_adj_vars_def:
  (handle_adj_vars l d (Var v) = Var (if v < l then v else v+d)) ∧
  (handle_adj_vars l d (If x1 x2 x3) =
     If (handle_adj_vars l d x1) (handle_adj_vars l d x2) (handle_adj_vars l d x3)) ∧
  (handle_adj_vars l d (Let xs x2) =
     Let (handle_adj_vars1 l d xs) (handle_adj_vars (l + LENGTH xs) d x2)) ∧
  (handle_adj_vars l d (Handle x1 x2) =
     Handle (handle_adj_vars l d x1) (handle_adj_vars (l + 1) d x2)) ∧
  (handle_adj_vars l d (Raise x1) = Raise (handle_adj_vars l d x1)) ∧
  (handle_adj_vars l d (Op op xs) = Op op (handle_adj_vars1 l d xs)) ∧
  (handle_adj_vars l d (Tick x) = Tick (handle_adj_vars l d x)) ∧
  (handle_adj_vars l d (Call t dest xs) =
     Call t dest (handle_adj_vars1 l d xs)) ∧
  (handle_adj_vars1 l d [] = []) ∧
  (handle_adj_vars1 l d (x::xs) = handle_adj_vars l d x :: handle_adj_vars1 l d xs)
End

Definition handle_size_def:
  (handle_size (Var v) = 1) ∧
  (handle_size (If x1 x2 x3) = 1 + handle_size x1 + handle_size x2 + handle_size x3) ∧
  (handle_size (Let xs x2) = 1 + handle_size x2 + handle_size1 xs) ∧
  (handle_size (Handle x1 x2) = 1 + 5 * (handle_size x1 + handle_size x2)) ∧
  (handle_size (Raise x1) = 1 + handle_size x1) ∧
  (handle_size (Op op xs) = 1 + handle_size1 xs) ∧
  (handle_size (Tick x) = 1 + handle_size x) ∧
  (handle_size (Call t dest xs) = 1 + handle_size1 xs) ∧
  (handle_size1 [] = 1:num) ∧
  (handle_size1 (x::xs) = 1 + handle_size x + handle_size1 xs)
End

Triviality handle_size_non_zero:
  0 < handle_size x
Proof
  Cases_on ‘x’ \\ fs [handle_size_def]
QED

Definition handle_simp_def:
  (handle_simp (Handle x1 x2) = make_handle x1 x2 0) /\
  (handle_simp (Var v) = Var v) /\
  (handle_simp (If x1 x2 x3) = If (handle_simp x1) (handle_simp x2) (handle_simp x3)) /\
  (handle_simp (Let xs x2) = Let (handle_simp_list xs) (handle_simp x2)) /\
  (handle_simp (Raise x1) = Raise (handle_simp x1)) /\
  (handle_simp (Op op xs) = Op op (handle_simp_list xs)) /\
  (handle_simp (Tick x) = Tick (handle_simp x)) /\
  (handle_simp (Call t dest xs) = Call t dest (handle_simp_list xs)) /\
  (handle_simp_list [] = ([]:bvl$exp list)) /\
  (handle_simp_list (x::xs) = handle_simp x :: handle_simp_list xs) /\
  (make_handle x1 x2 l =
     dtcase dest_handle_Raise x1 of
     | SOME r => Let [r] (handle_adj_vars 1 l (handle_simp x2))
     | NONE =>
     dtcase dest_handle_Let x1 of
     | SOME (xs,x) => Let (handle_simp_list xs) (make_handle x x2 (l + LENGTH xs))
     | NONE =>
     dtcase dest_handle_If x1 of
     | SOME (INR (b1,b2,b3)) => If (handle_simp b1)
                                   (handle_simp b2)
                                   (make_handle b3 x2 l)
     | SOME (INL (b1,b2,b3)) => If (handle_simp b1)
                                   (make_handle b2 x2 l)
                                   (handle_simp b3)
     | NONE => (Handle (handle_simp x1) (handle_adj_vars 1 l (handle_simp x2))))
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL a => handle_size a
                                    | INR (INL a) => handle_size1 a
                                    | INR (INR (a,b,_)) => handle_size a + handle_size b’
  \\ rpt conj_tac \\ rpt gen_tac
  \\ simp_tac std_ss []
  \\ fs [handle_size_def] \\ rw []
  \\ gvs [DefnBase.one_line_ify NONE dest_handle_If_def,AllCaseEqs()]
  \\ gvs [DefnBase.one_line_ify NONE dest_handle_Raise_def,AllCaseEqs()]
  \\ fs [handle_size_def] \\ rw []
  \\ fs [dest_handle_Let_def,handle_size_non_zero]
End

Definition SmartLet_def:
  SmartLet xs x = if NULL xs then x else Let xs x
End

Definition LetLet_def:
  LetLet env_length fvs (body:bvl$exp) =
    let xs = GENLIST I env_length in
    let zs = FILTER (\n. IS_SOME (lookup n fvs)) xs in
    let ys = MAPi (\i x. (x,i)) zs in
    let long_list = GENLIST (\n. dtcase ALOOKUP ys n of
                                 | NONE => Op (IntOp (Const 0)) []
                                 | SOME k => Var k) env_length in
      Let (MAP Var zs) (SmartLet long_list body)
End

Definition OptionalLetLet_def:
  OptionalLetLet e env_size live s (limit:num) (nr:bool) =
    if s < limit then ([e],live,s,nr) else
      let fvs = db_to_set live in
      let flat_live = vars_from_list (MAP FST (toAList fvs)) in
        ([(Let [] (LetLet env_size fvs e))],flat_live,0n,nr)
End

Definition OptionalLetLet_sing_def:
  OptionalLetLet_sing e env_size live s (limit:num) (nr:bool) =
    if s < limit then (e,live,s,nr) else
      let fvs = db_to_set live in
      let flat_live = vars_from_list (MAP FST (toAList fvs)) in
        ((Let [] (LetLet env_size fvs e)),flat_live,0n,nr)
End

Theorem OptionalLetLet_sing_eq:
  OptionalLetLet e sz lv s lim nr =
    (λ(d,l,s,nr). ([d],l,s,nr)) (OptionalLetLet_sing e sz lv s lim nr)
Proof
  rw[OptionalLetLet_def, OptionalLetLet_sing_def]
QED

Definition compile_def:
  (compile l n [] = ([]:bvl$exp list,Empty,0n,T)) /\
  (compile l n (x::y::xs) =
     let (dx,lx,s1,nr1) = compile l n [x] in
     let (dy,ly,s2,nr2) = compile l n (y::xs) in
       (dx ++ dy, mk_Union lx ly, s1+s2, nr1 /\ nr2)) /\
  (compile l n [Var v] = if v < n then ([Var v],Var v,1,T)
                         else ([Op (IntOp (Const 0)) []],Empty,1,T)) /\
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
       if op = ThunkOp ForceThunk then
         ([Op op ys],lx,s1+1,F)
       else
         OptionalLetLet (Op op ys) n lx (s1+1) l nr1) /\
  (compile l n [Tick x] =
     let (y,lx,s1,nr1) = compile l n [x] in
       ([Tick (HD y)],lx,s1,nr1)) /\
  (compile l n [Call t dest xs] =
     let (ys,lx,s1,nr1) = compile l n xs in
       OptionalLetLet (Call t dest ys) n lx (s1+1) l F)
End

val compile_ind = theorem"compile_ind";

Definition compile_sing_def:
  (compile_sing l n (Var v) = if v < n then (Var v,Var v,1,T)
                         else (Op (IntOp (Const 0)) [],Empty,1,T)) /\
  (compile_sing l n (If x1 x2 x3) =
     let (x1,l1,s1,nr1) = compile_sing l n x1 in
     let (x2,l2,s2,nr2) = compile_sing l n x2 in
     let (x3,l3,s3,nr3) = compile_sing l n x3 in
       OptionalLetLet_sing (If x1 x2 x3) n
         (mk_Union l1 (mk_Union l2 l3)) (s1+s2+s3+1) l
         (nr1 /\ nr2 /\ nr3)) /\
  (compile_sing l n (Let xs x2) =
     if NULL xs then
       compile_sing l n x2
     else
       let k = LENGTH xs in
       let (xs,l1,s1,nr1) = compile_list l n xs in
       let (x2,l2,s2,nr2) = compile_sing l (n + k) x2 in
         OptionalLetLet_sing (Let xs x2) n
           (mk_Union l1 (Shift k l2)) (s1+s2+1) l (nr1 /\ nr2)) /\
  (compile_sing l n (Handle x1 x2) =
     let (y1,l1,s1,nr1) = compile_sing l n x1 in
       if nr1 then (y1,l1,s1,T) else
         let (y2,l2,s2,nr2) = compile_sing l (n+1) x2 in
           (Handle (LetLet n (db_to_set l1) y1) y2,
            mk_Union l1 (Shift 1 l2),
            s2 (* s1 intentionally left out because
                  it does not contrib to exp size in BVI *), nr2)) /\
  (compile_sing l n (Raise x1) =
     let (dx,lx,s1,nr1) = compile_sing l n x1 in
       OptionalLetLet_sing (Raise dx) n lx (s1+1) l F) /\
  (compile_sing l n (Op op xs) =
     let (ys,lx,s1,nr1) = compile_list l n xs in
       if op = ThunkOp ForceThunk then
         (Op op ys,lx,s1+1,F)
       else
         OptionalLetLet_sing (Op op ys) n lx (s1+1) l nr1) /\
  (compile_sing l n (Tick x) =
     let (y,lx,s1,nr1) = compile_sing l n x in
       (Tick y,lx,s1,nr1)) /\
  (compile_sing l n (Call t dest xs) =
     let (ys,lx,s1,nr1) = compile_list l n xs in
       OptionalLetLet_sing (Call t dest ys) n lx (s1+1) l F) ∧

  (compile_list l n [] = ([]:bvl$exp list,Empty,0n,T)) /\
  (compile_list l n (x::xs) =
     let (dx,lx,s1,nr1) = compile_sing l n x in
     let (dy,ly,s2,nr2) = compile_list l n xs in
       (dx :: dy, mk_Union lx ly, s1+s2, nr1 /\ nr2))
End

Theorem compile_sing_eq:
  (∀e l n. compile l n [e] = (λ(d,l,s,nr). ([d],l,s,nr)) (compile_sing l n e)) ∧
  (∀es l n. compile l n es = compile_list l n es)
Proof
  Induct >> rw[compile_def, compile_sing_def, OptionalLetLet_sing_eq] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (TOP_CASE_TAC >> gvs[]) >>
  Cases_on `es` >> gvs[compile_def]
QED

Definition compile_exp_def:
  compile_exp cut_size arity e =
    HD (FST (compile cut_size arity [handle_simp (bvl_const$compile_exp e)]))
End

Theorem compile_exp_eq:
  compile_exp cut_size arity e =
    FST (compile_sing cut_size arity (handle_simp (bvl_const$compile_exp e)))
Proof
  rw[compile_exp_def, compile_sing_eq] >> pairarg_tac >> gvs[]
QED

val dest_Seq_def = PmatchHeuristics.with_classic_heuristic Define `
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

Definition compile_seqs_def:
  compile_seqs cut_size e acc =
    dtcase dest_Seq e of
    | NONE => (let new_e = compile_exp cut_size 0 e in
                 dtcase acc of
                 | NONE => new_e
                 | SOME rest => Let [new_e] (Let [] (Let [] rest)))
    | SOME (e1,e2) =>
        compile_seqs cut_size e1
          (SOME (compile_seqs cut_size e2 acc))
Termination
  (WF_REL_TAC ` measure (\(c,e,a). exp_size e) `
    \\ strip_tac \\ HO_MATCH_MP_TAC (fetch "-" "dest_Seq_ind")
    \\ fs [dest_Seq_def] \\ EVAL_TAC \\ fs []):tactic
End

Definition compile_any_def:
  compile_any split_seq cut_size arity e =
    if (arity = 0) /\ split_seq then
      compile_seqs cut_size e NONE
    else
      compile_exp cut_size arity e
End

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

Theorem compile_seqs_compute =
  LIST_CONJ [
    compile_seqs_def
    |> Q.SPECL [`e`,`c`,`NONE`]
    |> SIMP_RULE std_ss [LET_THM],
    compile_seqs_def
    |> Q.SPECL [`e`,`c`,`SOME y`]
    |> SIMP_RULE std_ss [LET_THM]]

val _ = export_theory();
