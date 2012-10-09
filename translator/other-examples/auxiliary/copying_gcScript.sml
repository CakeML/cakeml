open HolKernel Parse boolLib bossLib; val _ = new_theory "copying_gc";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory;


val _ = Hol_datatype `heap_address = H_ADDR of num | H_DATA of 'a`;

val _ = Hol_datatype `heap_element =
    H_EMP | H_REF of num | H_BLOCK of ('a heap_address) list # (num # 'b)`;

val getBLOCK_def = Define `
  (getBLOCK z (H_BLOCK y) = y) /\
  (getBLOCK z _ = z)`;

val rel_move_def = Define `
  (rel_move (H_DATA x,j,m,b,e,b2,e2) = (H_DATA x,j,m)) /\
  (rel_move (H_ADDR a,j,m,b,e,b2,e2) =
     case m a of
        H_EMP => (H_ADDR j,j,m)
      | H_REF i => (H_ADDR i,j,m)
      | H_BLOCK (xs,n,d) => let m = (a =+ H_REF j) m in
                            let m = (j =+ H_BLOCK (xs,n,d)) m in
                              (H_ADDR j,j + n + 1,m))`;

val rel_move_list_def = Define `
  (rel_move_list ([],j,m,b,e,b2,e2) = ([],j,m)) /\
  (rel_move_list (x::xs,j,m,b,e,b2,e2) =
     let (x,j,m) = rel_move (x,j,m,b,e,b2,e2) in
     let (xs,j,m) = rel_move_list (xs,j,m,b,e,b2,e2) in
       (x::xs,j,m))`;

val rel_gc_step_def = Define `
  rel_gc_step z (i,j,m,b,e,b2,e2) =
    let (xs,n,d) = getBLOCK z (m i) in
    let (ys,j,m) = rel_move_list (xs,j,m,b,e,b2,e2) in
    let m = (i =+ H_BLOCK (ys,n,d)) m in
    let i = i + n + 1 in
      (i,j,m)`;

val rel_gc_loop_def = tDefine "rel_gc_loop" `
  rel_gc_loop z (i,j,m,b,e,b2,e2) =
    if i = j then (i,m) else
    if ~(i < j /\ j <= e) then (i,m) else
      let (i,j,m) = rel_gc_step z (i,j,m,b,e,b2,e2) in
      let (i,m) = rel_gc_loop z (i,j,m,b,e,b2,e2) in
        (i,m)`
 (WF_REL_TAC `measure (\(z,i,j,m,b,e,b2,e2). e - i)`
  THEN SIMP_TAC std_ss [rel_gc_step_def,LET_DEF]
  THEN CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
  THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN DECIDE_TAC);

val RANGE_def = Define `RANGE(i:num,j) k = i <= k /\ k < j`;
val CUT_def = Define `CUT (i,j) m = \k. if RANGE (i,j) k then m k else H_EMP`;

val rel_gc_def = Define `
  rel_gc z (b:num,e:num,b2:num,e2:num,roots,m) =
    let (b2,e2,b,e) = (b,e,b2,e2) in
    let (roots,j,m) = rel_move_list (roots,b,m,b,e,b2,e2) in
    let (i,m) = rel_gc_loop z (b,j,m,b,e,b2,e2) in
    let m = CUT (b,i) m in
      (b,i,e,b2,e2,roots,m)`;

(*
val res = translate getBLOCK_def
val res = translate combinTheory.UPDATE_def
val res = translate rel_move_def
val res = translate rel_move_list_def
val res = translate rel_gc_step_def
val res = translate rel_gc_loop_def
val res = translate RANGE_def
val res = translate CUT_def
val res = translate rel_gc_def
*)

val _ = export_theory();
