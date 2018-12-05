(*
  A function for generating efficient switch-like jumps in BVL.
*)
open preamble bvlTheory;

val _ = new_theory "bvl_jump";

val JumpList_def = tDefine "JumpList" `
  (JumpList n xs =
     let l = LENGTH xs in
       if l = 0 then Op (Const 0) [] else
       if l = 1 then HD xs else
         let k = l DIV 2 in
         let ys = TAKE k xs in
         let zs = DROP k xs in
         let lt = (if n + l < 1000000 /\ n + k < 1000000
                   then Op (LessConstSmall (n+k)) [Var 0]
                   else Op Less [Op (Const (&(n+k))) []; Var 0]) in
           If lt (JumpList n ys) (JumpList (n + k) zs))`
  (WF_REL_TAC `measure (LENGTH o SND)` \\ REPEAT STRIP_TAC
   \\ Q.ISPEC_THEN`xs`STRIP_ASSUME_TAC SPLIT_LIST \\ FULL_SIMP_TAC std_ss []
   \\ REPEAT STRIP_TAC \\ fs [rich_listTheory.TAKE_LENGTH_APPEND,
        rich_listTheory.DROP_LENGTH_APPEND]
   \\ rfs [DIV_EQ_X]  >>
   full_simp_tac std_ss [GSYM LENGTH_NIL] >>
   decide_tac);

val Jump_def = Define `
  Jump x xs = Let [x] (JumpList 0 xs)`;

val _ = export_theory();
