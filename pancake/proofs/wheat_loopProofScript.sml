(*
  Correctness proof for wheat_loop
*)

open preamble wheatLangTheory wheatSemTheory
local open wordSemTheory in end

val _ = new_theory"wheat_loopProof";

val _ = set_grammar_ancestry ["wheatSem"];

Definition every_prog_def:
  (every_prog p (Seq p1 p2) <=>
    p (Seq p1 p2) /\ every_prog p p1 /\ every_prog p p2) /\
  (every_prog p (Loop l1 body l2) <=>
    p (Loop l1 body l2) /\ every_prog p body) /\
  (every_prog p (If x1 x2 x3 p1 p2 l1) <=>
    p (If x1 x2 x3 p1 p2 l1) /\ every_prog p p1 /\ every_prog p p2) /\
  (every_prog p (Mark p1) <=>
    p (Mark p1) /\ every_prog p p1) /\
  (every_prog p (Call ret dest args handler) <=>
    p (Call ret dest args handler) /\
    (case handler of SOME (n,q) => every_prog p q | NONE => T)) /\
  (every_prog p prog <=> p prog)
End

Definition no_Loop_def:
  no_Loop = every_prog (\q. !l1 x l2. q <> Loop l1 x l2)
End

Definition comp_no_loop_def:
  (comp_no_loop p (Seq p1 p2) =
    Seq (comp_no_loop p p1) (comp_no_loop p p2)) /\
  (comp_no_loop p (If x1 x2 x3 p1 p2 l1) =
    If x1 x2 x3 (comp_no_loop p p1) (comp_no_loop p p2) l1) /\
  (comp_no_loop p (Call ret dest args handler) =
    Call ret dest args (case handler of
                        | SOME (n,q) => SOME (n,comp_no_loop p q)
                        | NONE => NONE)) /\
  (comp_no_loop p Break = FST p) /\
  (comp_no_loop p Continue = SND p) /\
  (comp_no_loop p (Mark prog) = comp_no_loop p prog) /\
  (comp_no_loop p prog = prog)
End

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
     | SOME (n,p1) =>
         let (p1,t1) = mark_all p1 in
         let p2 = Call ret dest args (SOME (n,p1)) in
           (if t1 then Mark p2 else p2, t1)) /\
  (mark_all prog = (Mark prog,T))
End

Theorem mark_all_correct:
  !prog q b.
     mark_all prog = (q,b) ==>
     b = no_Loop q /\
     every_prog (\p. !q. p = Mark q ==> no_Loop q) q
Proof
  recInduct mark_all_ind \\ reverse (rpt conj_tac)
  \\ rpt gen_tac \\ strip_tac



    \\ fs [every_prog_def,no_Loop_def,mark_all_def]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ fs [every_prog_def,no_Loop_def]
  \\ fs [] \\ rpt (pairarg_tac \\ fs [])


    \\ every_case_tac \\ fs []
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [] \\ rpt (pairarg_tac \\ fs [])
    \\ every_case_tac \\ fs []
    \\ fs [every_prog_def,no_Loop_def]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [every_prog_def,no_Loop_def]



    \\ pop_assum mp_tac
  \\ once_rewrite_tac [mark_all_def]
  \\ fs [] \\ rpt (pairarg_tac \\ fs [])
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ fs [every_prog_def,no_Loop_def]

    \\ fs [CaseEq"bool"]
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [every_prog_def,no_Loop_def]
    \\ cheat

    every_case_tac \\ fs []
    \\ fs [] \\ rpt (pairarg_tac \\ fs [])
    \\ fs [every_prog_def,no_Loop_def]


    Cases_on ‘t1’
    \\ rpt strip_tac \\ rveq \\ fs []
    \\ fs [every_prog_def,no_Loop_def]



val _ = export_theory();
