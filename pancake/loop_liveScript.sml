(*
  Liveness analysis for loopLang.
*)
Theory loop_live
Ancestors
  loopLang loop_call
Libs
  preamble


Definition vars_of_exp_def:
  vars_of_exp (loopLang$Var v) l = insert v () l ∧
  vars_of_exp (Const _) l = l ∧
  vars_of_exp (BaseAddr) l = l ∧
  vars_of_exp (TopAddr) l = l ∧
  vars_of_exp (Lookup _) l = l ∧
  vars_of_exp (Load a) l = vars_of_exp a l ∧
  vars_of_exp (Op x vs) l = vars_of_exp_list vs l ∧
  vars_of_exp (Shift _ x _) l = vars_of_exp x l ∧
  vars_of_exp_list xs l =
    (case xs of [] => l
     | (x::xs) => vars_of_exp x (vars_of_exp_list xs l))
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (x,_) => exp_size ARB x
                                   | INR (x,_) => list_size (exp_size ARB) x)’
End

Theorem size_mk_BN:
  ∀t1 t2. size (mk_BN t1 t2) = size (BN t1 t2)
Proof
  Cases \\ Cases \\ fs [mk_BN_def,size_def]
QED

Theorem size_mk_BS:
  ∀t1 t2 x. size (mk_BS t1 x t2) = size (BS t1 x t2)
Proof
  Cases \\ Cases \\ fs [mk_BS_def,size_def]
QED

Theorem size_inter:
  ∀l1 l2. size (inter l1 l2) <= size l1
Proof
  Induct \\ fs [inter_def]
  \\ Cases_on ‘l2’ \\ fs [size_mk_BN,size_mk_BS]
  \\ rewrite_tac [ADD_ASSOC,DECIDE “m+1≤n+1 ⇔ m ≤ n:num”]
  \\ metis_tac [DECIDE “n1 ≤ m1 ∧ n2 ≤ m2 ⇒ n1+n2 ≤ m1+m2:num ∧  n1+n2 ≤ m1+m2+1”]
QED


Definition arith_vars:
  arith_vars (LLongMul r1 r2 r3 r4) l =
  insert r3 () $ insert r4 () $ delete r1 $ delete r2 l ∧
  arith_vars (LDiv r1 r2 r3) l = insert r2 () $ insert r3 () $ delete r1 l ∧
  arith_vars (LLongDiv r1 r2 r3 r4 r5) l =
  insert r3 () $ insert r4 () $ insert r5 () $ delete r1 $ delete r2 l
End

(* This optimisation shrinks all cutsets and also deletes assignments
   to unused variables. The Loop case is the interesting one: an
   auxiliary function is used to find a fixed-point. *)

Definition shrink_def:
  (shrink b (Seq p1 p2) l =
     let (p2,l) = shrink b p2 l in
     let (p1,l) = shrink b p1 l in
       (Seq p1 p2, l)) /\
  (shrink b (Loop live_in body live_out) l =
     let l2 = inter live_out l in
       case fixedpoint live_in LN l2 body of
       | SOME (body,l0) =>
           (let l = inter live_in l0 in (Loop l body l2, l))
       | NONE => let (b,_) = shrink (live_in,l2) body l2 in
                   (Loop live_in b l2, live_in)) /\
  (shrink b (If x1 x2 x3 p1 p2 l1) l =
     let l = inter l l1 in
     let (p1,l1) = shrink b p1 l in
     let (p2,l2) = shrink b p2 l in
     let l3 = (case x3 of Reg r => insert r () LN | _ => LN) in
       (If x1 x2 x3 p1 p2 l, insert x2 () (union l3 (union l1 l2)))) /\
  (shrink b (Mark p1) l = shrink b p1 l) /\
  (shrink b Break l = (Break,SND b)) /\
  (shrink b Continue l = (Continue,FST b)) /\
  (shrink b Fail l = (Fail,LN)) /\
  (shrink b Skip l = (Skip,l)) /\
  (shrink b (Return v) l = (Return v, insert v () LN)) /\
  (shrink b (Raise v) l = (Raise v, insert v () LN)) /\
  (shrink b (Arith arith) l =
   (Arith arith, arith_vars arith l)
  ) ∧
  (shrink b (LocValue n m) l =
     case lookup n l of
     | NONE => (Skip,l)
     | SOME _ => (LocValue n m, delete n l)) ∧
  (shrink b (Assign n x) l =
     case lookup n l of
     | NONE => (Skip,l)
     | SOME _ => (Assign n x, vars_of_exp x (delete n l))) ∧
  (shrink b (ShMem op r ad) l =
   (ShMem op r ad, (*case lookup r l of
                     NONE => l
                   | _ => if is_load op
                          then vars_of_exp ad (insert r () l)
                          else l)*)
  vars_of_exp ad (insert r () l))) ∧
  (shrink b (Store e n) l =
    (Store e n, vars_of_exp e (insert n () l))) ∧
  (shrink b (SetGlobal name e) l =
    (SetGlobal name e, vars_of_exp e l)) ∧
  (shrink b (Call ret dest args handler) l =
     let a = fromAList (MAP (λx. (x,())) args) in
     case ret of
     | NONE => (Call NONE dest args NONE, union a l)
     | SOME (n,l1) =>
        case handler of
        | NONE => let l3 = (delete n (inter l l1)) in
                    (Call (SOME (n,l3)) dest args NONE, union a l3)
        | SOME (e,h,r,live_out) =>
            let (r,l2) = shrink b r l in
            let (h,l3) = shrink b h l in
            let l1 = inter l1 (union (delete n l2) (delete e l3)) in
              (Call (SOME (n,l1)) dest args (SOME (e,h,r,inter l live_out)),
               union a l1)) ∧
  (shrink b (FFI n r1 r2 r3 r4 l1) l =
   (FFI n r1 r2 r3 r4 (inter l1 l),
      insert r1 () (insert r2 () (insert r3 () (insert r4 () (inter l1 l)))))) ∧
  (shrink b (Load32 x y) l =
    (Load32 x y, insert x () (delete y l))) ∧
  (shrink b (LoadByte x y) l =
    (LoadByte x y, insert x () (delete y l))) ∧
  (shrink b (Store32 x y) l =
    (Store32 x y, insert x () (insert y () l))) ∧
  (shrink b (StoreByte x y) l =
    (StoreByte x y, insert x () (insert y () l))) ∧
  (shrink b prog l = (prog,l)) /\


  (fixedpoint live_in l1 l2 body =
     let (b,l0) = shrink (inter live_in l1,l2) body l2 in
     let l0' = inter live_in l0 in
       if l0' = l1 then (* fixed point found! *) SOME (b,l0) else
       if size l0' ≤ size l1 then (* no progress made, not possible *) NONE else
         fixedpoint live_in l0' l2 body)
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I LEX measure I)
               (λx. case x of
                    | INL (_,c,_) => (prog_size (K 0) c, 0:num, 0)
                    | INR (live_in,l1,l2,body) =>
                        (prog_size (K 0) body, 1, size live_in - size l1))`
  \\ rw []
  \\ fs [GSYM NOT_LESS]
  \\ qsuff_tac ‘size l1 < size live_in’ \\ fs []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ asm_exists_tac \\ fs [size_inter]
End

Theorem exp_ind = vars_of_exp_ind
  |> Q.SPECL [‘λx l. P x’,‘λx l. Q x’]
  |> SIMP_RULE std_ss []
  |> Q.GENL [‘P’,‘Q’];

Theorem fixedpoint_thm:
  ∀live_in l1 l2 (body:'a loopLang$prog) l0 b.
    fixedpoint live_in l1 l2 body = SOME (b, l0) ⇒
    shrink (inter live_in l0, l2) body l2 = (b, l0)
Proof
  qmatch_abbrev_tac ‘entire_goal’
  \\ qsuff_tac
    ‘(∀b (prog:'a loopLang$prog) l d. shrink b prog l = d ⇒ T) ∧ entire_goal’
  THEN1 fs []
  \\ unabbrev_all_tac
  \\ ho_match_mp_tac shrink_ind \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ once_rewrite_tac [shrink_def]
  \\ fs [] \\ pairarg_tac \\ fs []
  \\ fs [CaseEq"bool"] \\ rw [] \\ fs []
  \\ fs [inter_assoc]
  \\ pop_assum (fn th => rewrite_tac [GSYM th])
  \\ rpt AP_THM_TAC \\ AP_TERM_TAC \\ fs []
  \\ fs [lookup_inter_alt] \\ rw []
  \\ fs [domain_lookup]
  \\ Cases_on ‘lookup x live_in’ \\ fs []
QED

Definition mark_all_def:
  (mark_all (Seq p1 p2) =
     let (p1,t1) = mark_all p1 in
     let (p2,t2) = mark_all p2 in
     let t3 = (t1 /\ t2) in
       (if t3 then Mark (Seq p1 p2) else Seq p1 p2, t3)) /\
  (mark_all (Loop l1 body l2) =
     let (body,t1) = mark_all body in
       (Loop l1 body l2, F)) /\
  (mark_all (If x1 x2 x3 p1 p2 l1) =
     let (p1,t1) = mark_all p1 in
     let (p2,t2) = mark_all p2 in
     let p3 = If x1 x2 x3 p1 p2 l1 in
     let t3 = (t1 /\ t2) in
       (if t3 then Mark p3 else p3, t3)) /\
  (mark_all (Mark p1) = mark_all p1) /\
  (mark_all (Call ret dest args handler) =
     case handler of
     | NONE => (Mark (Call ret dest args handler), T)
     | SOME (n,p1,p2,l) =>
         let (p1,t1) = mark_all p1 in
         let (p2,t2) = mark_all p2 in
         let t3 = (t1 ∧ t2) in
         let p3 = Call ret dest args (SOME (n,p1,p2,l)) in
           (if t3 then Mark p3 else p3, t3)) /\
  (mark_all prog = (Mark prog,T))
End

Definition comp_def:
  comp prog = FST (mark_all (FST (shrink (LN,LN) prog LN)))
End


Definition optimise_def:
  optimise prog = (comp o FST o loop_call$comp LN) prog
End


