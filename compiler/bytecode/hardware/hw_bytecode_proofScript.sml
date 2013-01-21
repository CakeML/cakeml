
open HolKernel Parse boolLib bossLib;

val _ = new_theory "hw_bytecode_proof";

open bytecodeTerminationTheory;
open hw_bytecodeTheory;
open listTheory;
open wordsTheory;
open wordsLib;
open arithmeticTheory;
open rich_listTheory;
open relationTheory;
open finite_mapTheory;
open pred_setTheory;

infix \\ val op \\ = op THEN;


(* -------------------------------------------------------------------------- *
    Definition of translation: bytecode --> hardware bytecode
 * -------------------------------------------------------------------------- *)

val push_imm_def = Define `
  push_imm n = if 2**32 <= n then [hwFail] else
               if n < 2**6 then [hwPushImm (n2w n)] else
                 push_imm (n DIV 2 ** 6) ++
                 [hwShiftAddImm (n2w (n MOD 2**6))]`;

val push_fixed_imm_def = Define `
  push_fixed_imm n =
    if 64 * 64 * 64 * 64 <= n then [hwFail] else
      let n1 = n2w (n MOD 64) in
      let n2 = n2w ((n DIV 64) MOD 64) in
      let n3 = n2w ((n DIV (64 * 64)) MOD 64) in
      let n4 = n2w ((n DIV (64 * 64 * 64)) MOD 64) in
        [hwPushImm n4; hwShiftAddImm n3; hwShiftAddImm n2; hwShiftAddImm n1]`;

val hwml_def = Define `
  (hwml (Stack Pop) = [hwPop]) /\
  (hwml (Stack (Pops n)) =
     if n = 0 then [(hwPushImm 0w); hwPop] else REPLICATE n hwPop1) /\
  (hwml (Stack (Shift m n)) =
     if m <= n then
       push_imm (n - 1) ++ REPLICATE m hwStackStore ++ [hwPop] ++
       REPLICATE (n - m) hwPop
     else
       push_imm (m - 1) ++ REPLICATE m hwStackLoad ++ [hwPop] ++
       push_imm (m + n - 1) ++ REPLICATE m hwStackStore ++ [hwPop] ++
       REPLICATE n hwPop) /\
  (hwml (Stack (PushInt i)) =
     if i < 0 then [hwFail] else push_imm (Num i)) /\
  (hwml (Stack (Cons tag len)) =
     if tag < 64 /\ len < 2 ** 26 then
       if len = 0 then [hwPushImm (n2w tag)] else
         REPLICATE len hwHeapAlloc ++ [hwHeapAddress; hwShiftAddImm (n2w tag)]
     else [hwFail]) /\
  (hwml (Stack (Load n)) = push_imm n ++ [hwStackLoad; hwPop]) /\
  (hwml (Stack (Store n)) = push_imm n ++ [hwStackStore; hwPop]) /\
  (hwml (Stack (El n)) = [hwShiftRight] ++ push_imm (n+1) ++ [hwSub; hwHeapLoad]) /\
  (hwml (Stack (TagEq tag)) = if tag < 2**6 then [hwLowerEqual (n2w tag)] else [hwFail]) /\
  (hwml (Stack Equal) = [hwFail]) /\
  (hwml (Stack Add) = [hwAdd]) /\
  (hwml (Stack Sub) = [hwSub]) /\
  (hwml (Stack Mult) = [hwFail]) /\
  (hwml (Stack Div) = [hwFail]) /\
  (hwml (Stack Mod) = [hwFail]) /\
  (hwml (Stack Less) = [hwLess]) /\
  (hwml (Jump (Addr n)) = push_fixed_imm n ++ [hwJump]) /\
  (hwml (JumpIf (Addr n)) = push_fixed_imm n ++ [hwJumpIfNotZero]) /\
  (hwml (Call (Addr n)) = push_fixed_imm n ++ [hwCall]) /\
  (hwml JumpPtr = [hwJump]) /\
  (hwml CallPtr = [hwCall]) /\
  (hwml Return = [hwSwap; hwJump]) /\
  (hwml Exception = [hwFail]) /\
  (hwml Ref = [hwHeapAddress; hwSwap; hwHeapAlloc]) /\
  (hwml Deref = [hwHeapLoad]) /\
  (hwml Update = [hwSwap; hwHeapStore; hwPop]) /\
  (hwml (Label _) = []) /\
  (hwml _ = [hwFail])`;

val full_hwml_def = Define `
  full_hwml xs = FLAT (MAP hwml xs)`;

val hwml_length_def = Define `
  hwml_length x = LENGTH (hwml x) - 1`;


(* -------------------------------------------------------------------------- *
    Correctness of translation: bytecode --> hardware bytecode
 * -------------------------------------------------------------------------- *)

val hw_val_lemma = prove(
  ``!xs x. MEM x xs ==> bc_value_size x < bc_value1_size xs``,
  Induct \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val hw_val_def = tDefine "hw_val" `
  (hw_val (Number i) w heap r = (w2n w = Num i) /\ 0 <= i) /\
  (hw_val (CodePtr p) w heap r = (w2n w = p)) /\
  (hw_val (RefPtr p) w heap r = (FLOOKUP r p = SOME (w2n w))) /\
  (hw_val (Block tag xs) (w:word32) heap r =
     (w2w w = n2w tag : 6 word) /\ tag < 64 /\
     (if xs = [] then (w = n2w tag) else
        let ptr = w2n (w >>> 6) in
          (LENGTH xs) <= ptr /\ ptr <= LENGTH (heap:word32 list) /\
          DISJOINT { n | ptr - LENGTH xs <= n /\ n < ptr  } (FRANGE r) /\
          EVERY2 (\x w. hw_val x w heap r) xs
                 (REVERSE (TAKE (LENGTH xs) (DROP (ptr - LENGTH xs) heap)))))`
 (WF_REL_TAC `measure (bc_value_size o FST)`
  \\ FULL_SIMP_TAC std_ss [MEM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC hw_val_lemma \\ DECIDE_TAC)

val F11_def = Define `
  F11 f = !x y z. (FLOOKUP f x = SOME z) /\ (FLOOKUP f y = SOME z) ==> (x = y)`;

val hw_refs_def = Define `
  hw_refs (r:num |-> num) (heap:word32 list) (refs:num |-> bc_value) =
    (FDOM r = FDOM refs) /\ F11 r /\
    FEVERY (\(n,m). m < LENGTH heap /\
                    ?x. (FLOOKUP refs n = SOME x) /\
                        hw_val x (EL m heap) heap r) r`;

val hw_inv_aux_def = Define `
  hw_inv_aux s s1 r =
    EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) s.stack s1.stack /\
    (s.inst_length = hwml_length) /\ (s1.pc = n2w s.pc) /\
    hw_refs r s1.heap s.refs`;

val MOD_lemma = prove(
  ``!w n. n <= w2n (w:word32) ==> (n MOD dimword (:32) = n)``,
  Cases \\ FULL_SIMP_TAC std_ss [w2n_n2w] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC LESS_EQ_LESS_TRANS \\ FULL_SIMP_TAC std_ss [LESS_MOD]);

val hw_steps_def = Define `
  (hw_steps [] s = s) /\
  (hw_steps (x::xs) s = hw_steps xs (hw_step x s))`;

val F_TAC =
  FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,inc_pc_def,overflow_def]

val hw_steps_APPEND = prove(
  ``!xs ys s. hw_steps (xs ++ ys) s = hw_steps ys (hw_steps xs s)``,
  Induct \\ FULL_SIMP_TAC std_ss [hw_steps_def,APPEND]);

val hw_step_error_IMP = prove(
  ``!x s. ~((hw_step x s).error) ==> ~(s.error)``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def] \\ EVAL_TAC \\ SRW_TAC [] []);

val hw_steps_error_IMP = prove(
  ``!xs x s. ~(hw_steps xs s).error ==> ~s.error``,
  Induct \\ FULL_SIMP_TAC std_ss [REPLICATE,hw_steps_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC hw_step_error_IMP);

val push_imm_lemma = prove(
  ``!n. ~(hw_steps (push_imm n) s1).error ==>
        (hw_steps (push_imm n) s1 = s1 with
           <| stack := n2w n :: s1.stack; pc := s1.pc + n2w (LENGTH (push_imm n)) |> ) /\
        n < 2**32 /\ ~s1.error``,
  HO_MATCH_MP_TAC (fetch "-" "push_imm_ind") \\ STRIP_TAC \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [push_imm_def]
  \\ Cases_on `2 ** 32 <= n` \\ FULL_SIMP_TAC std_ss [] THEN1 F_TAC
  \\ Cases_on `n < 64` \\ FULL_SIMP_TAC std_ss []
  THEN1
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,
         push_def,inc_pc_def,overflow_def,w2w_def,n2w_w2n]
    \\ Tactical.REVERSE (REPEAT STRIP_TAC) THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [hw_state_component_equality])
  \\ FULL_SIMP_TAC std_ss [hw_steps_APPEND,hw_steps_def]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC hw_step_error_IMP \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,
         push_def,inc_pc_def,overflow_def,w2w_def,n2w_w2n,arg_def]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [hw_state_component_equality]
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_add_n2w,word_mul_n2w]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [GSYM DIVISION]
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val divmod_def = zDefine`
  (divmod 0 n = 0) /\
  (divmod (SUC k) n = n MOD 64 + 64 * divmod k (n DIV 64))`;
val _ = computeLib.add_funs[numLib.SUC_RULE divmod_def]

val divmod_thm = prove(
  ``!k n. n < 64 ** k ==> (divmod k n = n)``,
  Induct \\ FULL_SIMP_TAC std_ss [divmod_def] THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [EXP] \\ REPEAT STRIP_TAC
  \\ `n DIV 64 < 64 ** k` by (FULL_SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ FULL_SIMP_TAC std_ss [GSYM DIVISION]);

val push_fixed_imm_lemma = prove(
  ``!n. ~(hw_steps (push_fixed_imm n) s1).error ==>
        (hw_steps (push_fixed_imm n) s1 = s1 with
           <| stack := n2w n :: s1.stack;
              pc := s1.pc + n2w (LENGTH (push_fixed_imm n)) |> ) /\
        n < 2**32 /\ ~s1.error``,
  FULL_SIMP_TAC (srw_ss()) [hw_steps_def,push_fixed_imm_def,LET_DEF,hw_step_def]
  \\ STRIP_TAC \\ Cases_on `16777216 <= n`
  \\ NTAC 10 (FULL_SIMP_TAC (srw_ss()) [Once hw_steps_def,hw_step_def,
       LET_DEF,inc_pc_def,arg_def,overflow_def,push_def])
  \\ FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w,WORD_MUL_LSL,
       word_add_n2w,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [EVAL ``divmod 4 n``
       |> SIMP_RULE std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC,ADD_ASSOC,DIV_DIV_DIV_MULT]
       |> GSYM]
  \\ `n < 64 ** 4` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC divmod_thm \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hw_state_component_equality]
  \\ DECIDE_TAC);

val _ = computeLib.del_consts[``divmod``]
val _ = delete_const "divmod"; (* remove temp definition *)

val Swap_Pop_heap = prove(
  ``!n s1. (hw_steps (REPLICATE n hwPop1) s1).heap = s1.heap``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE,FLAT,hw_steps_def,
    APPEND,hw_step_def,LET_DEF,arg_def,push_def,inc_pc_def,overflow_def]);

val EVERY2_APPEND_IMP = prove(
  ``!xs1 ys. EVERY2 P (xs1 ++ xs2) ys ==>
             ?ys1 ys2. (ys = ys1 ++ ys2) /\ (LENGTH xs1 = LENGTH ys1)``,
  Induct THEN1
   (Cases_on `ys` THEN1 (Cases_on `xs2`
    \\ FULL_SIMP_TAC (srw_ss()) [APPEND,EVERY2_def]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`[]`,`[]`] \\ EVAL_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`[]`,`h::t`] \\ EVAL_TAC)
  \\ REPEAT STRIP_TAC \\ Cases_on `ys`
  \\ FULL_SIMP_TAC (srw_ss()) [APPEND,EVERY2_def]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h'::ys1`,`ys2`] \\ EVAL_TAC);

val EVERY2_CONS_APPEND = prove(
  ``EVERY2 P (x::(xs1 ++ xs2)) ys ==>
    ?y ys1 ys2. (ys = y::ys1 ++ ys2) /\ (LENGTH xs1 = LENGTH ys1)``,
  Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,APPEND]
  \\ REPEAT STRIP_TAC \\ METIS_TAC [EVERY2_APPEND_IMP]);

val EVERY2_APPEND = prove(
  ``!xs ys xs2 ys2.
      (LENGTH xs = LENGTH ys) ==>
      (EVERY2 P (xs ++ xs2) (ys ++ ys2) = EVERY2 P xs ys /\ EVERY2 P xs2 ys2)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [CONJ_ASSOC]);

val EVERY2_APPEND_APPEND_IMP = prove(
  ``!ys zs xs ts.
      EVERY2 P (ys ++ zs ++ xs) ts ==>
      ?ys1 zs1 xs1. (ts = ys1 ++ zs1 ++ xs1) /\
                    (LENGTH ys1 = LENGTH ys) /\ (LENGTH zs1 = LENGTH zs)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EVERY2_APPEND_IMP
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC EVERY2_APPEND
  \\ NTAC 5 (POP_ASSUM (K ALL_TAC))
  \\ IMP_RES_TAC EVERY2_APPEND_IMP
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1'`,`ys2'`,`ys2`]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]);

val EVERY2_CONS_APPEND_CONS = prove(
  ``EVERY2 P (x::(xs1 ++ [x2] ++ xs2)) ys ==>
    ?y y2 ys1 ys2. (ys = y::ys1 ++ [y2] ++ ys2) /\ (LENGTH xs1 = LENGTH ys1)``,
  Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC EVERY2_APPEND_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_APPEND
  \\ Cases_on `ys2` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
  \\ METIS_TAC []);

val hw_steps_swap_pop_pc = prove(
  ``!ys1 ys2 y s1.
      ((hw_steps ((REPLICATE (LENGTH ys1) hwPop1)) s1).pc =
        s1.pc + n2w (LENGTH (((REPLICATE (LENGTH ys1) hwPop1)))))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,REPLICATE,LENGTH,FLAT,
    hw_steps_def,WORD_ADD_0,hw_steps_def,hw_step_def,LET_DEF,inc_pc_def,arg_def,
    overflow_def,push_def]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,AC WORD_ADD_ASSOC WORD_ADD_COMM]);

val hw_steps_swap_pop = prove(
  ``!ys1 ys2 y s1.
      (s1.stack = y::ys1 ++ ys2) ==>
      ((hw_steps (REPLICATE (LENGTH ys1) hwPop1) s1).stack = y::ys2)``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,REPLICATE,hw_steps_def,APPEND,WORD_ADD_0]
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,arg_def,push_def] \\ F_TAC);

val EVERY2_EL = prove(
  ``!xs ys n P. EVERY2 P xs ys /\ n < LENGTH xs ==> P (EL n xs) (EL n ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,LENGTH]
  \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) []);

val UPDATE_NTH_THM = prove(
  ``!xs ys. UPDATE_NTH (LENGTH xs) y (xs ++ x::ys) = xs ++ y::ys``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,UPDATE_NTH_def,APPEND]);

val WORD_LEMMA = prove(
  ``(w + -1w * v = w - v) /\ (-1w * v + w = w - v)``,
  SRW_TAC [] [])

val word_arith_lemma2 = prove(
  ``!n m. n2w n - (n2w m) :'a word =
      if n < m then (- (n2w (m-n))) else n2w (n-m)``,
  REPEAT STRIP_TAC \\ Cases_on `n < m` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC bool_ss [NOT_LESS,LESS_EQ]
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,ADD1,DECIDE ``n+1+p-n = 1+p:num``]
  \\ REWRITE_TAC [GSYM word_add_n2w,WORD_SUB_PLUS,WORD_SUB_REFL]
  \\ REWRITE_TAC [GSYM WORD_SUB_PLUS]
  \\ REWRITE_TAC [word_sub_def,WORD_ADD_0,DECIDE ``m+p-m=p:num``]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC] \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ REWRITE_TAC [GSYM word_sub_def,WORD_SUB_ADD]);

val EVERY2_TWO = prove(
  ``EVERY2 P (x1::x2::xs) zs ==> ?y1 y2 ys. zs = y1::y2::ys``,
  Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]);

val REPLICATE_hwHeapAlloc = prove(
  ``!ys1 s1.
      (s1.stack = ys1 ++ ys2) /\
      ~(hw_steps (REPLICATE (LENGTH ys1) hwHeapAlloc) s1).error ==>
      (hw_steps (REPLICATE (LENGTH ys1) hwHeapAlloc) s1 =
       s1 with <| pc := s1.pc + n2w (LENGTH ys1) ;
                  stack := ys2; heap := s1.heap ++ ys1 |>) /\ ~s1.error``,
  Induct \\ FULL_SIMP_TAC std_ss [hw_steps_def,LENGTH,REPLICATE,APPEND,
    APPEND_NIL,WORD_ADD_0]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [hw_state_component_equality])
  \\ NTAC 3 STRIP_TAC
  \\ Q.PAT_ASSUM `!x.bbb` (MP_TAC o Q.SPEC `hw_step hwHeapAlloc s1`)
  \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,LET_DEF,inc_pc_def,arg_def,heap_alloc_def,overflow_def]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,GSYM word_add_n2w,ADD1]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hw_state_component_equality]);

val EL_LENGTH = prove(
  ``!xs y ys. EL (LENGTH xs) (xs ++ y::ys) = y``,
  Induct \\ FULL_SIMP_TAC std_ss [EL,LENGTH,APPEND,HD,TL]);

val EVERY_IMP_LENGTH_EQ = prove(
  ``!xs ys P. EVERY2 P xs ys ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys`
  \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,LENGTH,ADD1] \\ METIS_TAC []);

val EVERY2_SNOC_NIL = prove(
  ``~EVERY2 P (SNOC x xs) []``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EVERY_IMP_LENGTH_EQ \\ FULL_SIMP_TAC (srw_ss()) [])

val EVERY2_SNOC_SNOC = prove(
  ``!P xs ys x y. EVERY2 P (SNOC x xs) (SNOC y ys) = P x y /\ EVERY2 P xs ys``,
  Induct_on `xs` \\ Cases_on `ys`
  \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,EVERY2_SNOC_NIL] \\ METIS_TAC []);

val EVERY2_REVERSE = prove(
  ``!P xs ys. EVERY2 P (REVERSE xs) (REVERSE ys) = EVERY2 P xs ys``,
  STRIP_TAC \\ Induct \\ Cases_on `ys`
  \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,REVERSE,EVERY2_SNOC_NIL]
  \\ FULL_SIMP_TAC std_ss [EVERY2_SNOC_SNOC]);

val EVERY2_IMP_EVERY2 = prove(
  ``!xs ys P Q.
      (!x y. MEM x xs /\ MEM y ys ==> P x y ==> Q x y) ==>
      EVERY2 P xs ys ==> EVERY2 Q xs ys``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [EVERY2_def,MEM] \\ METIS_TAC []);

val LESS_LENGTH_IMP = prove(
  ``!xs n. n < LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = n)``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH]);

val LESS_EQ_LENGTH_IMP = prove(
  ``!xs n. n <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = n)``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH]);

val CONS_SNOC = prove(
  ``!ys y x. x::SNOC y ys = SNOC y (x::ys)``,
  FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND]);

val LESS_EQ_LENGTH_IMP2 = prove(
  ``!xs n. n <= LENGTH xs ==> ?ys3 ys2. (xs = ys3 ++ ys2) /\ (LENGTH ys2 = n)``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND]
  THEN1 (Q.EXISTS_TAC `[]` \\ FULL_SIMP_TAC std_ss [APPEND])
  THEN1 (REPEAT STRIP_TAC \\ Q.EXISTS_TAC `h::xs` \\ FULL_SIMP_TAC std_ss [APPEND_NIL])
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`BUTLAST (h::ys3)`,`LAST (h::ys3) :: ys2`]
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ `(ys3 = []) \/ ?x xs. ys3 = SNOC x xs` by METIS_TAC [SNOC_CASES]
  THEN1 (FULL_SIMP_TAC std_ss [APPEND,FRONT_DEF,LAST_DEF])
  \\ FULL_SIMP_TAC std_ss [CONS_SNOC,FRONT_SNOC,LAST_SNOC]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);

val TAKE_DROP_ALT = prove(
  ``!xs m n. n <= m /\ m <= LENGTH xs ==>
             (TAKE n (DROP (m - n) xs) = DROP (m-n) (TAKE m xs))``,
  Induct THEN1 (FULL_SIMP_TAC std_ss [LENGTH] \\ EVAL_TAC) \\ NTAC 4 STRIP_TAC
  \\ Cases_on `m - n` \\ FULL_SIMP_TAC std_ss [DROP_def,DROP_0]
  THEN1 (`m = n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [ADD1]
  \\ Cases_on `m` THEN1 `F` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [TAKE_def,ADD1,DROP_def]
  \\ `n' = n'' - n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!m n. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ DECIDE_TAC);

val TAKE_DROP_THM = prove(
  ``!xs m n. n <= m /\ m < LENGTH xs ==>
             (TAKE n (DROP (m - n) xs) = DROP (m-n) (TAKE m xs))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC TAKE_DROP_ALT \\ DECIDE_TAC);

val hw_val_APPEND = prove(
  ``!x y heap r xs. hw_val x y heap r ==> hw_val x y (heap ++ xs) r``,
  HO_MATCH_MP_TAC (fetch "-" "hw_val_ind")
  \\ FULL_SIMP_TAC std_ss [hw_val_def,LET_DEF]
  \\ NTAC 8 STRIP_TAC
  \\ Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ STRIP_TAC THEN1 DECIDE_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC LESS_EQ_LENGTH_IMP
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,BUTFIRSTN_LENGTH_APPEND]
  \\ `LENGTH ys1 <= LENGTH (ys1 ++ ys2 ++ xs')` by
       (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ `LENGTH ys1 <= LENGTH (ys1 ++ ys2)` by
       (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ Q.PAT_ASSUM `EVERY2 P xx yy` MP_TAC
  \\ FULL_SIMP_TAC std_ss [TAKE_DROP_ALT]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,rich_listTheory.TAKE_LENGTH_APPEND]
  \\ MATCH_MP_TAC EVERY2_IMP_EVERY2 \\ FULL_SIMP_TAC std_ss []);

val hw_refs_APPEND = prove(
  ``!r xs ys refs. hw_refs r xs refs ==> hw_refs r (xs ++ ys) refs``,
  FULL_SIMP_TAC std_ss [hw_refs_def,FEVERY_DEF] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `FDOM r = FDOM refs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND] THEN1 DECIDE_TAC
  \\ IMP_RES_TAC EL_APPEND1 \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC hw_val_APPEND \\ FULL_SIMP_TAC std_ss []);

val EVERY2_EL = prove(
  ``!xs ys n. EVERY2 P xs ys /\ n < LENGTH xs ==> P (EL n xs) (EL n ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,LENGTH,EL,HD,TL]
  \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val bc_fetch_aux_NOT_Label = prove(
  ``!xs l n x. (bc_fetch_aux xs l n = SOME x) ==> ~is_Label x``,
  Induct \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [is_Label_def] \\ RES_TAC);

val bc_fetch_NOT_Label = prove(
  ``!s x. (bc_fetch s = SOME x) ==> ~is_Label x``,
  SIMP_TAC std_ss [bc_fetch_def] \\ METIS_TAC [bc_fetch_aux_NOT_Label]);

val hwml_length_lemma = prove(
  ``!x. ~is_Label x ==> (p + hwml_length x + 1 = p + LENGTH (hwml x))``,
  STRIP_TAC \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [hwml_length_def]
  \\ IMP_RES_TAC bc_fetch_NOT_Label
  \\ Tactical.REVERSE (`0 < LENGTH (hwml x)` by ALL_TAC)
  THEN1 DECIDE_TAC \\ Cases_on `x` \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ SRW_TAC [] [hwml_def,LENGTH,DECIDE ``0<n+1:num /\ 0<n+2:num``,Once push_imm_def]
  \\ TRY (Cases_on `n`)
  \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE,FLAT,LENGTH,LENGTH_APPEND,
       is_Label_def] \\ DECIDE_TAC);

val hwml_length_thm = prove(
  ``!x. (bc_fetch s = SOME x) ==>
        (p + hwml_length x + 1 = p + LENGTH (hwml x))``,
  METIS_TAC [bc_fetch_NOT_Label,hwml_length_lemma]);

val NOT_LESS_EQ = DECIDE ``~(m <= n) = n < m:num``

val push_imm_LESS = prove(
  ``!n. LENGTH (push_imm n) < 7``,
  NTAC 7 (ONCE_REWRITE_TAC [push_imm_def]) \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [DIV_DIV_DIV_MULT,DIV_LT_X,X_LE_DIV]
  \\ `F` by DECIDE_TAC);

val push_fixed_imm_LESS = prove(
  ``!n. LENGTH (push_fixed_imm n) < 7``,
  SIMP_TAC std_ss [push_fixed_imm_def] \\ SRW_TAC [] [LENGTH] \\ EVAL_TAC);

val hw_steps_pc = prove(
  ``!n s. ((hw_steps (REPLICATE n hwPop) s).pc = s.pc + n2w n) /\
          ((hw_steps (REPLICATE n hwStackStore) s).pc = s.pc + n2w n) /\
          ((hw_steps (REPLICATE n hwStackLoad) s).pc = s.pc + n2w n) /\
          ((hw_steps (REPLICATE n hwPop) s).heap = s.heap) /\
          ((hw_steps (REPLICATE n hwStackStore) s).heap = s.heap) /\
          ((hw_steps (REPLICATE n hwStackLoad) s).heap = s.heap)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE,hw_steps_def,hw_step_def] \\ EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,ADD1,AC ADD_COMM ADD_ASSOC]);

val hw_step_pc =
  hw_steps_pc |> Q.SPEC `SUC 0`
  |> REWRITE_RULE [REPLICATE,hw_steps_def] |> SIMP_RULE std_ss [ADD1]

val hw_step_pc_lemma = prove(
  ``(s.pc = k) ==> ((hw_step (hwShiftAddImm w) s).pc = k + 1w)``,
  EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val push_imm_pc = prove(
  ``!n s. ((hw_steps (push_imm n) s).pc = s.pc + n2w (LENGTH (push_imm n)))``,
  HO_MATCH_MP_TAC (fetch "-" "push_imm_ind") \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [push_imm_def] \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [] THEN1 EVAL_TAC THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hw_steps_APPEND,hw_steps_def]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ METIS_TAC [hw_step_pc_lemma]);

val push_imm_heap = prove(
  ``!n s. ((hw_steps (push_imm n) s).heap = s.heap)``,
  HO_MATCH_MP_TAC (fetch "-" "push_imm_ind") \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [push_imm_def] \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [] THEN1 EVAL_TAC THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [hw_steps_APPEND,hw_steps_def]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,push_def,LET_DEF,
       overflow_def,arg_def,inc_pc_def]);

val push_imm_stack = prove(
  ``~(hw_steps (push_imm n) s1).error ==>
    ((hw_steps (push_imm n) s1).stack = n2w n :: s1.stack) /\ n < 2**32``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC push_imm_lemma
  \\ FULL_SIMP_TAC (srw_ss()) []);

val StackLoad_stack = prove(
  ``LENGTH xs < 4294967296 ==>
    (s1.stack = n2w (LENGTH xs) :: (xs ++ [y] ++ ys)) ==>
    ((hw_step hwStackLoad s1).stack = n2w (LENGTH xs) :: y::(xs ++ [y] ++ ys))``,
  EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,GSYM APPEND_ASSOC,NULL_DEF,APPEND,HD])

val REPLICATE_hwStackLoad_stack = prove(
  ``!ys1 zs1 xs1 s2.
      LENGTH (xs1 ++ ys1) - 1 < 4294967296 ==>
      (s2.stack = n2w (LENGTH (xs1 ++ ys1) - 1)::(xs1 ++ ys1 ++ zs1)) ==>
      ((hw_steps (REPLICATE (LENGTH ys1) hwStackLoad) s2).stack =
        n2w (LENGTH (xs1 ++ ys1) - 1)::(ys1 ++ (xs1 ++ ys1) ++ zs1))``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ FULL_SIMP_TAC std_ss [APPEND,APPEND_NIL,LENGTH,REPLICATE,hw_steps_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND_ASSOC]
  \\ `(LENGTH (xs1 ++ ys1 ++ [x]) - 1 = LENGTH (xs1 ++ ys1)) /\
      (LENGTH (ys1 ++ [x]) = SUC (LENGTH ys1))` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH (xs1 ++ ys1) < 4294967296` by DECIDE_TAC
  \\ IMP_RES_TAC StackLoad_stack
  \\ FULL_SIMP_TAC std_ss [REPLICATE,hw_steps_def]
  \\ Q.PAT_ASSUM `!sz.bbb` (MP_TAC o Q.SPECL [`x::zs1`,`x::xs1`,`hw_step hwStackLoad s2`])
  \\ `(LENGTH (x::xs1 ++ ys1) = LENGTH (xs1 ++ ys1) + 1) /\
      LENGTH (xs1 ++ ys1) + 1 < 4294967297` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val StackStore_stack = prove(
  ``LENGTH xs < 4294967296 /\
    (s1.stack = n2w (LENGTH xs) :: x :: (xs ++ [y] ++ ys)) ==>
    ((hw_step hwStackStore s1).stack = n2w (LENGTH xs) :: (xs ++ [x] ++ ys))``,
  EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,UPDATE_NTH_THM])

val REPLICATE_hwStackStore_stack = prove(
  ``!qs1 ys1 zs1 xs1 s2.
      LENGTH (qs1 ++ xs1) - 1 < 4294967296 /\ (LENGTH ys1 = LENGTH qs1) ==>
      (s2.stack = n2w (LENGTH (qs1 ++ xs1) - 1)::(qs1 ++ xs1 ++ ys1 ++ zs1)) ==>
      ((hw_steps (REPLICATE (LENGTH qs1) hwStackStore) s2).stack =
        n2w (LENGTH (qs1 ++ xs1) - 1)::(xs1 ++ qs1 ++ zs1))``,
  Induct
  \\ FULL_SIMP_TAC std_ss [APPEND,APPEND_NIL,LENGTH,REPLICATE,hw_steps_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND_NIL] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,REPLICATE,hw_steps_def]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND]
  \\ `(LENGTH (qs1 ++ [x] ++ xs1 ++ ys1) - 1 = LENGTH (qs1 ++ xs1 ++ ys1))` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ Cases_on `ys1` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Q.PAT_ASSUM `!sz.bbb` (MP_TAC o Q.SPECL [`t`,`zs1`,`xs1 ++ [h]`,`hw_step hwStackStore s2`])
  \\ `LENGTH (qs1 ++ xs1 ++ [h]) < 4294967297` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ `LENGTH (qs1 ++ xs1 ++ [h]) - 1 = LENGTH (qs1 ++ xs1)` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC
  \\ ONCE_REWRITE_TAC [APPEND_ASSOC]
  \\ MATCH_MP_TAC (StackStore_stack |> REWRITE_RULE [GSYM APPEND_ASSOC,APPEND] |> GEN_ALL)
  \\ Q.EXISTS_TAC `h'` \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ DECIDE_TAC);

val hwPop_stack = prove(
  ``(s.stack = x::xs) ==> ((hw_step hwPop s).stack = xs)``,
  EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def]);

val REPLICATE_hwPop_stack = prove(
  ``!xs ys s.
      (s.stack = xs ++ ys) ==>
      ((hw_steps (REPLICATE (LENGTH xs) hwPop) s).stack = ys)``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,REPLICATE,hw_steps_def]
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bb` MATCH_MP_TAC
  \\ IMP_RES_TAC hwPop_stack \\ FULL_SIMP_TAC std_ss []);

val PULL_EXISTS = METIS_PROVE []
  ``((b ==> ?v. P v) = ?v. (b ==> P v)) /\ ((b /\ ?v. P v) = ?v. (b /\ P v))``

val INSERT_DISJOINT = prove(
  ``DISJOINT s (y INSERT t) = DISJOINT s t /\ ~(y IN s)``,
  FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF,EXTENSION] \\ METIS_TAC []);

val hw_val_FUPDATE = prove(
  ``!n x y heap r.
      hw_val x y heap r /\ ~(n IN FDOM r) ==> hw_val x y heap (r |+ (n,LENGTH heap))``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ STRIP_TAC
  \\ HO_MATCH_MP_TAC (fetch "-" "hw_val_ind")
  \\ FULL_SIMP_TAC (srw_ss()) [hw_val_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ REPEAT STRIP_TAC THEN1 (METIS_TAC [])
  \\ Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Tactical.REVERSE STRIP_TAC THEN1
   (MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] EVERY2_IMP_EVERY2)
    \\ Q.EXISTS_TAC `(\x w'. hw_val x w' heap r)`
    \\ FULL_SIMP_TAC std_ss [MEM_REVERSE])
  \\ FULL_SIMP_TAC std_ss [DOMSUB_NOT_IN_DOM,INSERT_DISJOINT]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val F11_FUPDATE = prove(
  ``F11 r /\ ~(x IN FDOM r) /\ ~(y IN FRANGE r) ==> F11 (r |+ (x,y))``,
  SRW_TAC [] [F11_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,FRANGE_DEF] \\ METIS_TAC []);

val IMP_NOT_IN_RANGE = prove(
  ``FEVERY (\(x,y). ~(z = y)) r ==> ~(z IN FRANGE r)``,
  FULL_SIMP_TAC (srw_ss()) [FEVERY_DEF,FRANGE_DEF] \\ METIS_TAC []);

val LENGTH_UPDATE_NTH = prove(
  ``!xs x y. LENGTH (UPDATE_NTH x y xs) = LENGTH xs``,
  Induct \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,UPDATE_NTH_def]);

val EL_UPDATE_NTH = prove(
  ``!ys n x. n < LENGTH ys ==> (EL n (UPDATE_NTH n x ys) = x)``,
  Induct \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,UPDATE_NTH_def]);

val EL_UPDATE_NTH_NEQ = prove(
  ``!ys n m x. ~(m = n) ==> (EL n (UPDATE_NTH m x ys) = EL n ys)``,
  Induct THEN1 (Cases_on `m` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,UPDATE_NTH_def])
  \\ Cases_on `m` THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_def,EL,TL])
  \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_def,EL,TL,HD]);

val DROP_UPDATE_NTH = prove(
  ``!xs m n x. m < n ==> (DROP n (UPDATE_NTH m x xs) = DROP n xs)``,
  Induct THEN1 (Cases_on `m` \\ FULL_SIMP_TAC std_ss [DROP_def,UPDATE_NTH_def])
  \\ Cases_on `m`
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [DROP_def,UPDATE_NTH_def])
  \\ Cases_on `n'` \\ FULL_SIMP_TAC (srw_ss()) [DROP_def,UPDATE_NTH_def]);

val TAKE_UPDATE_NTH = prove(
  ``!xs m n x. n <= m ==> (TAKE n (UPDATE_NTH m x xs) = TAKE n xs)``,
  Induct THEN1 (Cases_on `m` \\ FULL_SIMP_TAC std_ss [TAKE_def,UPDATE_NTH_def])
  \\ Cases_on `m`
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [TAKE_def,UPDATE_NTH_def])
  \\ Cases_on `n'` \\ FULL_SIMP_TAC (srw_ss()) [TAKE_def,UPDATE_NTH_def]);

val hw_val_UPDATE_NTH_lemma = prove(
  ``!x1 x2 heap r.
      hw_val (RefPtr ptr) y2 heap r ==>
      (hw_val x1 x2 (UPDATE_NTH (w2n y2) y1 heap) r = hw_val x1 x2 heap r)``,
  HO_MATCH_MP_TAC (fetch "-" "hw_val_ind") \\ FULL_SIMP_TAC std_ss [hw_val_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_UPDATE_NTH]
  \\ Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [CONJ_ASSOC]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(b ==> (c1 = c2)) ==> (b /\ c1 = b /\ c2)``)
  \\ REPEAT STRIP_TAC
  \\ `(TAKE (LENGTH xs)
        (DROP (w2n (x2 >>> 6) - LENGTH xs)
           (UPDATE_NTH (w2n y2) y1 heap))) =
      (TAKE (LENGTH xs) (DROP (w2n (x2 >>> 6) - LENGTH xs) heap))` by
   (Cases_on `w2n y2 < w2n (x2 >>> 6) - LENGTH xs`
    THEN1 FULL_SIMP_TAC std_ss [DROP_UPDATE_NTH]
    \\ Cases_on `w2n (x2 >>> 6) <= w2n y2`
    THEN1 FULL_SIMP_TAC std_ss [TAKE_DROP_ALT,TAKE_UPDATE_NTH,LENGTH_UPDATE_NTH]
    \\ FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF,FLOOKUP_DEF,EXTENSION,FRANGE_DEF]
    \\ `(~(w2n (x2 >>> 6) <= LENGTH xs + w2n y2) \/
         ~(w2n y2 < w2n (x2 >>> 6)))` by METIS_TAC []
    \\ `F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [EQ_IMP_THM]
  \\ STRIP_TAC \\ MATCH_MP_TAC EVERY2_IMP_EVERY2
  \\ FULL_SIMP_TAC std_ss []);

val hw_val_UPDATE_NTH = prove(
  ``hw_val (RefPtr ptr) y2 s1.heap r ==>
    !x1 x2. (hw_val x1 x2 (UPDATE_NTH (w2n y2) y1 s1.heap) r = hw_val x1 x2 s1.heap r)``,
  METIS_TAC [hw_val_UPDATE_NTH_lemma]);

val hw_steps_HEAP_LIMIT = prove(
  ``!n s1.
      ~(hw_steps (REPLICATE n hwHeapAlloc) s1).error /\ n <> 0 ==>
      LENGTH s1.heap + n < 2**26``,
  Induct \\ FULL_SIMP_TAC std_ss [REPLICATE,hw_steps_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [ADD1]
  \\ Cases_on `n` THEN1 (IMP_RES_TAC hw_steps_error_IMP
    \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,LET_DEF,inc_pc_def,arg_def,
         heap_alloc_def,overflow_def] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [ADD1]
  \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,LET_DEF,inc_pc_def,arg_def,
         heap_alloc_def,overflow_def] \\ DECIDE_TAC);

val hw_steps_hwml_lemma = prove(
  ``!s t.
      bc_next s t ==> !s1. s.pc < 2**32-100 /\ hw_inv_aux s s1 r /\ ~s1.error ==>
        let t1 = hw_steps (hwml (THE (bc_fetch s))) s1 in ~t1.error ==>
          hw_inv_aux t t1 (if bc_fetch s <> SOME Ref then r else
                             r |+ ((LEAST ptr. ptr NOTIN FDOM s.refs),LENGTH s1.heap))``,
  HO_MATCH_MP_TAC bc_next_ind \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`) \\ FULL_SIMP_TAC std_ss [hwml_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_stack_op_cases,LET_DEF]
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ TRY (F_TAC \\ NO_TAC)
  THEN1 (* Pop *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,arg_def,LET_DEF]
    \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,inc_pc_def,
         overflow_def,hwml_length_def,hwml_def,word_add_n2w] \\ STRIP_TAC
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC std_ss [EVERY2_def,NOT_CONS_NIL,TL]
    \\ REPEAT STRIP_TAC \\ DECIDE_TAC)
  THEN1 (* Pops *)
   (Cases_on `ys' = []` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,arg_def,
         inc_pc_def,push_def,overflow_def,bump_pc_def,hw_inv_aux_def,
         hwml_length_def,hwml_def,LENGTH_NIL,Swap_Pop_heap,word_add_n2w]
    \\ STRIP_TAC \\ IMP_RES_TAC EVERY2_CONS_APPEND
    \\ IMP_RES_TAC hw_steps_swap_pop
    \\ FULL_SIMP_TAC std_ss [EVERY2_def,APPEND,EVERY2_APPEND]
    \\ FULL_SIMP_TAC std_ss [hw_steps_swap_pop_pc]
    \\ FULL_SIMP_TAC std_ss [NOT_LESS_EQ,GSYM AND_IMP_INTRO]
    \\ Cases_on `ys1` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
    \\ FULL_SIMP_TAC std_ss [LENGTH,REPLICATE,FLAT,LENGTH,APPEND,ADD1,ADD_ASSOC,word_add_n2w])
  THEN1 (* Shift *)
   (Cases_on `LENGTH ys' <= LENGTH zs` \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [hw_steps_APPEND,hw_steps_def]
      \\ FULL_SIMP_TAC std_ss [hw_inv_aux_def]
      \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
      \\ IMP_RES_TAC EVERY2_APPEND_APPEND_IMP
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ `EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) ys' ys1 /\
          EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) zs zs1 /\
          EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) xs xs1` by
            (IMP_RES_TAC (GSYM EVERY2_APPEND) \\ FULL_SIMP_TAC std_ss [])
      \\ IMP_RES_TAC hw_steps_error_IMP
      \\ IMP_RES_TAC hw_step_error_IMP
      \\ IMP_RES_TAC hw_steps_error_IMP
      \\ ASM_SIMP_TAC (srw_ss()) [bump_pc_def]
      \\ ASM_SIMP_TAC std_ss [hw_step_pc,hw_steps_pc,push_imm_pc,push_imm_heap]
      \\ Q.PAT_ASSUM `bc_fetch s = SOME (Stack (Shift (LENGTH ys') (LENGTH zs)))` MP_TAC
      \\ SIMP_TAC std_ss [hwml_length_thm] \\ STRIP_TAC
      \\ ASM_SIMP_TAC std_ss [hwml_length_def,hwml_def,LENGTH_APPEND,LENGTH,
           word_add_n2w,GSYM WORD_ADD_ASSOC,LENGTH_REPLICATE,AC ADD_COMM ADD_ASSOC]
      \\ IMP_RES_TAC push_imm_stack
      \\ Q.ABBREV_TAC `s2 = hw_steps (push_imm (LENGTH zs - 1)) s1`
      \\ Q.PAT_ASSUM `s1.stack = ys1 ++ (zs1 ++ xs1)` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH ys1 <= LENGTH zs1` by DECIDE_TAC
      \\ Q.PAT_ASSUM `LENGTH ys' <= LENGTH zs` (K ALL_TAC)
      \\ IMP_RES_TAC LESS_EQ_LENGTH_IMP2
      \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
      \\ MP_TAC (REPLICATE_hwStackStore_stack
              |> Q.SPECL [`ys1`,`ys2`,`xs1`,`ys3`,`s2`])
      \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH (ys1 ++ ys3) = LENGTH zs` by ALL_TAC THEN1
       (`LENGTH zs1 = LENGTH (ys3 ++ ys2)` by FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ Q.ABBREV_TAC `s3 = hw_steps (REPLICATE (LENGTH ys') hwStackStore) s2`
      \\ STRIP_TAC
      \\ `(hw_step hwPop s3).stack = ys3 ++ ys1 ++ xs1` by ALL_TAC
      THEN1 (IMP_RES_TAC hwPop_stack \\ FULL_SIMP_TAC std_ss [])
      \\ Q.ABBREV_TAC `s4 = hw_step hwPop s3`
      \\ `LENGTH zs - LENGTH ys' = LENGTH ys3` by ALL_TAC
      THEN1 (IMP_RES_TAC EVERY2_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND])
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ IMP_RES_TAC REPLICATE_hwPop_stack
      \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND]
      \\ AP_TERM_TAC
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [hw_steps_APPEND,hw_steps_def]
    \\ FULL_SIMP_TAC std_ss [hw_inv_aux_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC EVERY2_APPEND_APPEND_IMP
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ `EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) ys' ys1 /\
        EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) zs zs1 /\
        EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) xs xs1` by
          (IMP_RES_TAC (GSYM EVERY2_APPEND) \\ FULL_SIMP_TAC std_ss [])
    \\ IMP_RES_TAC hw_steps_error_IMP
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC hw_steps_error_IMP
    \\ IMP_RES_TAC hw_steps_error_IMP
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC hw_steps_error_IMP
    \\ ASM_SIMP_TAC (srw_ss()) [bump_pc_def]
    \\ ASM_SIMP_TAC std_ss [hw_step_pc,hw_steps_pc,push_imm_pc,push_imm_heap]
    \\ ASM_SIMP_TAC std_ss [hwml_length_thm]
    \\ `~(LENGTH ys' <= LENGTH zs)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [hwml_length_def,hwml_def,LENGTH_APPEND,LENGTH,
         word_add_n2w,GSYM WORD_ADD_ASSOC,LENGTH_REPLICATE,AC ADD_COMM ADD_ASSOC]
    \\ IMP_RES_TAC push_imm_stack
    \\ Q.ABBREV_TAC `s2 = hw_steps (push_imm (LENGTH ys' - 1)) s1`
    \\ Q.PAT_ASSUM `s1.stack = ys1 ++ (zs1 ++ xs1)` ASSUME_TAC
    \\ Q.PAT_ASSUM `LENGTH ys1 = LENGTH ys'` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ MP_TAC (REPLICATE_hwStackLoad_stack
               |> Q.SPECL [`ys1`,`zs1 ++ xs1`,`[]`,`s2`])
    \\ `LENGTH ys1 < 4294967297` by ALL_TAC THEN1
      (IMP_RES_TAC push_imm_lemma \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [APPEND] \\ STRIP_TAC
    \\ Q.ABBREV_TAC `s3 = hw_steps (REPLICATE (LENGTH ys1) hwStackLoad) s2`
    \\ `(hw_step hwPop s3).stack = ys1 ++ ys1 ++ (zs1 ++ xs1)` by
          (IMP_RES_TAC hwPop_stack \\ FULL_SIMP_TAC std_ss [])
    \\ Q.ABBREV_TAC `s4 = hw_step hwPop s3`
    \\ Q.ABBREV_TAC `s5 = hw_steps (push_imm (LENGTH ys1 + LENGTH zs - 1)) s4`
    \\ FULL_SIMP_TAC std_ss []
    \\ `(ys1 ++ ys1 ++ (zs1 ++ xs1)) = (ys1 ++ (ys1 ++ zs1) ++ xs1)` by SIMP_TAC std_ss [APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [] \\ Q.ABBREV_TAC `ts = ys1 ++ zs1`
    \\ `LENGTH ys1 <= LENGTH ts` by ALL_TAC THEN1
         (Q.UNABBREV_TAC `ts` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND])
    \\ IMP_RES_TAC LESS_EQ_LENGTH_IMP2
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
    \\ (MP_TAC o Q.SPECL [`ys1`,`ys2`,`xs1`,`ys3`,`s5`]) REPLICATE_hwStackStore_stack
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ `LENGTH zs = LENGTH ys3` by ALL_TAC THEN1
     (`LENGTH (ys3 ++ ys2) = LENGTH (ys1 ++ zs1)` by METIS_TAC []
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ IMP_RES_TAC EVERY2_LENGTH \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH ys3 = LENGTH zs1` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `s6 = hw_steps (REPLICATE (LENGTH ys1) hwStackStore) s5`
    \\ STRIP_TAC
    \\ `(hw_step hwPop s6).stack = ys3 ++ ys1 ++ xs1` by ALL_TAC
    THEN1 (IMP_RES_TAC hwPop_stack \\ FULL_SIMP_TAC std_ss [])
    \\ Q.ABBREV_TAC `s7 = hw_step hwPop s6`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ `(hw_steps (REPLICATE (LENGTH ys3) hwPop) s7).stack = ys1 ++ xs1` by ALL_TAC
    THEN1 (IMP_RES_TAC REPLICATE_hwPop_stack \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND]
    \\ AP_TERM_TAC \\ DECIDE_TAC)
  THEN1 (* PushInt *)
   (Cases_on `i < 0` THEN1 F_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC push_imm_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def]
    \\ FULL_SIMP_TAC (srw_ss()) [hw_val_def,w2n_n2w]
    \\ IMP_RES_TAC hwml_length_thm \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,AC ADD_ASSOC ADD_COMM]
    \\ intLib.COOPER_TAC)
  THEN1 (* Cons *)
   (Tactical.REVERSE (Cases_on `n < 64`) THEN1 F_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Tactical.REVERSE (Cases_on `LENGTH ys' < 67108864`) THEN1 F_TAC
    \\ Cases_on `LENGTH ys' = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [LENGTH_NIL,REVERSE_DEF]
      \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
           hw_steps_APPEND,hw_steps_def]
      \\ NTAC 3 STRIP_TAC \\ NTAC 3 (IMP_RES_TAC hw_step_error_IMP)
      \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,arg_def,push_def,overflow_def,
           inc_pc_def,LET_DEF,heap_alloc_def,heap_address_def,EVERY2_APPEND]
      \\ IMP_RES_TAC hwml_length_thm \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [hwml_def,LENGTH_APPEND,LENGTH_REPLICATE,
           word_add_n2w,LENGTH,AC ADD_COMM ADD_ASSOC]
      \\ FULL_SIMP_TAC std_ss [hw_val_def]
      \\ `n < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [w2w_def])
    \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,hw_steps_APPEND,hw_steps_def]
    \\ NTAC 3 STRIP_TAC \\ NTAC 3 (IMP_RES_TAC hw_step_error_IMP)
    \\ IMP_RES_TAC EVERY2_APPEND_IMP
    \\ IMP_RES_TAC REPLICATE_hwHeapAlloc
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,arg_def,push_def,overflow_def,
         inc_pc_def,LET_DEF,heap_alloc_def,heap_address_def,EVERY2_APPEND]
    \\ IMP_RES_TAC hwml_length_thm \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [hw_val_def,LENGTH_REVERSE,REVERSE_EQ_NIL]
      \\ IMP_RES_TAC hw_steps_HEAP_LIMIT
      \\ `n2w (LENGTH s1.heap + LENGTH ys1) <+ n2w (2 ** 26):word32` by
       (FULL_SIMP_TAC std_ss []
        \\ `(LENGTH s1.heap + LENGTH ys1) < 4294967296` by DECIDE_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
      \\ `(((w2w:6 word -> word32) (n2w n) + n2w (LENGTH s1.heap + LENGTH ys1) << 6) >>> 6) =
          n2w (LENGTH s1.heap + LENGTH ys1):word32` by ALL_TAC THEN1
       (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ blastLib.BBLAST_TAC)
      \\ `w2n (((w2w:6 word -> word32) (n2w n) + n2w (LENGTH s1.heap + LENGTH ys1) << 6) >>> 6) =
          LENGTH s1.heap + LENGTH ys1` by ALL_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND,LENGTH_NIL]
      \\ `ys' <> []` by ALL_TAC THEN1
       (REPEAT STRIP_TAC \\ Cases_on `ys1` \\ FULL_SIMP_TAC (srw_ss()) [])
      \\ FULL_SIMP_TAC std_ss []
      \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [w2w_n2w,bitTheory.BITS_THM] \\ blastLib.BBLAST_TAC)
      \\ STRIP_TAC THEN1
       (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF,EXTENSION] \\ STRIP_TAC
        \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
        \\ `LENGTH s1.heap <= x` by DECIDE_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [hw_refs_def,FEVERY_DEF,FRANGE_DEF,GSYM NOT_LESS]
        \\ METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss [BUTFIRSTN_LENGTH_APPEND,GSYM APPEND_ASSOC,FIRSTN_LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [EVERY2_REVERSE,TAKE_LENGTH_ID]
      \\ Q.PAT_ASSUM `EVERY2 (\x1 x2. hw_val x1 x2 s1.heap r) ys' ys1` MP_TAC
      \\ MATCH_MP_TAC EVERY2_IMP_EVERY2
      \\ FULL_SIMP_TAC std_ss [hw_val_APPEND])
    THEN1
     (Q.PAT_ASSUM `EVERY2 ff xs ys2` MP_TAC
      \\ MATCH_MP_TAC EVERY2_IMP_EVERY2
      \\ FULL_SIMP_TAC std_ss [hw_val_APPEND])
    THEN1
     (FULL_SIMP_TAC std_ss [hwml_def,LENGTH_APPEND,LENGTH_REPLICATE,
        word_add_n2w,LENGTH,AC ADD_COMM ADD_ASSOC])
    \\ MATCH_MP_TAC hw_refs_APPEND
    \\ FULL_SIMP_TAC std_ss [])
  THEN1 (* Load *)
   (FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_imm_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ F_TAC \\ FULL_SIMP_TAC (srw_ss()) [arg_def,stack_load_def,push_def,LET_DEF]
    \\ F_TAC \\ FULL_SIMP_TAC (srw_ss()) [arg_def,stack_load_def,push_def,LET_DEF]
    \\ IMP_RES_TAC EVERY2_EL \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
  THEN1 (* Store *)
   (FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_imm_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ F_TAC \\ FULL_SIMP_TAC (srw_ss()) [arg_def,stack_store_def,push_def,LET_DEF,overflow_def]
    \\ IMP_RES_TAC EVERY2_CONS_APPEND_CONS
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,EVERY2_def,EVERY2_APPEND]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,EVERY2_APPEND,APPEND,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_THM]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,EVERY2_APPEND,APPEND,EVERY2_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM])
  THEN1 (* El *)
   (FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_imm_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [arg_def,stack_store_def,push_def,LET_DEF,
         overflow_def,hw_step_def,inc_pc_def,heap_load_def]
    \\ Cases_on `s1.stack`
    \\ FULL_SIMP_TAC (srw_ss()) [TL,HD,EVERY2_def,heap_load_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH,AC ADD_COMM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [WORD_LEMMA,hw_val_def]
    \\ `ys' <> []` by (CCONTR_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ Tactical.REVERSE STRIP_TAC THEN1 (AP_TERM_TAC \\ DECIDE_TAC)
    \\ Tactical.REVERSE (`EL (w2n (h >>> 6 - n2w (n+1))) s1.heap =
        EL n (REVERSE
           (TAKE (LENGTH ys') (DROP (w2n (h >>> 6) - LENGTH ys') s1.heap)))` by ALL_TAC)
    THEN1 (FULL_SIMP_TAC std_ss []
           \\ IMP_RES_TAC EVERY2_EL \\ FULL_SIMP_TAC std_ss [])
    \\ `w2n (h >>> 6) <= LENGTH s1.heap` by FULL_SIMP_TAC std_ss []
    \\ `LENGTH ys' <= w2n (h >>> 6)` by FULL_SIMP_TAC std_ss []
    \\ `n < LENGTH (TAKE (LENGTH ys') (DROP (w2n (h >>> 6) - LENGTH ys') s1.heap))` by
     (`LENGTH ys' <= LENGTH (DROP (w2n (h >>> 6) - LENGTH ys') s1.heap)` by ALL_TAC
      \\ FULL_SIMP_TAC std_ss [LENGTH_TAKE,LENGTH_DROP] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [EL_REVERSE,DECIDE ``PRE x = x - 1``]
    \\ `(LENGTH (TAKE (LENGTH ys') (DROP (w2n (h >>> 6) - LENGTH ys') s1.heap)) = LENGTH ys')` by
     (MATCH_MP_TAC LENGTH_TAKE
      \\ FULL_SIMP_TAC std_ss [LENGTH_DROP] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ `(LENGTH ys' - n - 1) < (LENGTH ys')` by DECIDE_TAC
    \\ `LENGTH ys' <= LENGTH (DROP (w2n (h >>> 6) - LENGTH ys') s1.heap)` by
     (FULL_SIMP_TAC std_ss [LENGTH_DROP] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [EL_FIRSTN]
    \\ `(LENGTH ys' - n - 1) + ((w2n (h >>> 6)) - LENGTH ys') < LENGTH s1.heap` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [EL_BUTFIRSTN]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ Cases_on `h >>> 6`
    \\ FULL_SIMP_TAC std_ss [w2n_n2w]
    \\ `~(n' < n + 1) /\ (n' - (n + 1)) < 4294967296` by
         (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma2]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `LENGTH ys' <= LENGTH s1.heap - (n' - LENGTH ys')` MP_TAC
    \\ Q.PAT_ASSUM `n' <= LENGTH s1.heap` MP_TAC
    \\ Q.PAT_ASSUM `n < LENGTH ys'` MP_TAC
    \\ Q.PAT_ASSUM `~(n' < n + 1)` MP_TAC
    \\ Q.PAT_ASSUM `LENGTH ys' <= n'` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ DECIDE_TAC)
  THEN1 (* TagEq *)
   (Tactical.REVERSE (Cases_on `n < 64`) THEN1 F_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,arg_def,LET_DEF,overflow_def,
         inc_pc_def,push_def,heap_load_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ FULL_SIMP_TAC (srw_ss()) [hw_val_def]
    \\ Cases_on `tag = n` \\ FULL_SIMP_TAC (srw_ss()) [bool_to_tag_def])
  THEN1 (* Add *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,
      overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC std_ss [EVERY2_def,NOT_CONS_NIL]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [EVERY2_def,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [HD,TL] \\ FULL_SIMP_TAC std_ss [hw_val_def]
    \\ Cases_on `h` \\ Cases_on `h'`
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EVAL ``dimword (:32)``]
    \\ `(n'' + n') < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [LESS_MOD]
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
    \\ intLib.COOPER_TAC)
  THEN1 (* Sub *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,
      overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC std_ss [EVERY2_def,NOT_CONS_NIL]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [EVERY2_def,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [HD,TL] \\ FULL_SIMP_TAC std_ss [hw_val_def]
    \\ Cases_on `h` \\ Cases_on `h'`
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_LEMMA,word_arith_lemma2]
    \\ `(n'' - n') < dimword (:32)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [w2n_n2w]
    \\ intLib.COOPER_TAC)
  THEN1 (* Less *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,
      overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ STRIP_TAC \\ IMP_RES_TAC EVERY2_TWO
    \\ FULL_SIMP_TAC std_ss [EVERY2_def,TL,HD,hw_val_def]
    \\ FULL_SIMP_TAC std_ss [WORD_LO]
    \\ `Num m < Num n = m < n` by intLib.COOPER_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `m < n` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ EVAL_TAC)
  THEN1 (* Jump Addr *)
   (FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def,hwml_def,bc_find_loc_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_fixed_imm_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ F_TAC \\ FULL_SIMP_TAC (srw_ss()) [arg_def])
  THEN1 (* JumpIf Addr *)
   (FULL_SIMP_TAC std_ss [bump_pc_def,bc_find_loc_def]
    \\ `bc_fetch (s with stack := xs) = SOME (JumpIf (Addr n))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_fetch_def])
    \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,hw_steps_APPEND,hw_steps_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_fixed_imm_lemma
    \\ FULL_SIMP_TAC std_ss [] \\ F_TAC \\ FULL_SIMP_TAC (srw_ss()) [arg_def]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ Cases_on `x = 0` \\ Cases_on `h = 0w`  \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,AC ADD_COMM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [bc_find_loc_def]
    \\ FULL_SIMP_TAC std_ss [hw_val_def]
    \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `LENGTH (push_fixed_imm n) < 7` by FULL_SIMP_TAC std_ss [push_fixed_imm_LESS]
    \\ `s.pc + LENGTH (push_fixed_imm n) + 1 < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [AC ADD_COMM ADD_ASSOC]
    \\ `F` by intLib.COOPER_TAC)
  THEN1 (* JumpIf Addr *)
   (FULL_SIMP_TAC std_ss [bump_pc_def,bc_find_loc_def]
    \\ `bc_fetch (s with stack := xs) = SOME (JumpIf (Addr n))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_fetch_def])
    \\ FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,hw_steps_APPEND,hw_steps_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_def,word_add_n2w,hwml_length_thm,
         LENGTH_APPEND,LENGTH_REPLICATE,LENGTH]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_fixed_imm_lemma
    \\ FULL_SIMP_TAC std_ss [] \\ F_TAC \\ FULL_SIMP_TAC (srw_ss()) [arg_def]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [hw_val_def]
    \\ Q.PAT_ASSUM `h = 0w` ASSUME_TAC \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,AC ADD_COMM ADD_ASSOC])
  THEN1 (* Call Addr *)
   (FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def,bc_find_loc_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ IMP_RES_TAC hw_step_error_IMP
    \\ IMP_RES_TAC push_fixed_imm_lemma
    \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,LET_DEF,inc_pc_def,
         arg_def,push_def,overflow_def]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hw_val_def,hwml_length_def,hwml_def,LENGTH_APPEND,LENGTH]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `s1.pc = n2w s.pc` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [word_add_n2w]
    \\ `LENGTH (push_fixed_imm n) < 7` by FULL_SIMP_TAC std_ss [push_fixed_imm_LESS]
    \\ `s.pc + LENGTH (push_fixed_imm n) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `LENGTH (push_fixed_imm n) + s.pc + 1 < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  THEN1 (* CallPtr *)
   (FULL_SIMP_TAC (srw_ss()) [hw_inv_aux_def,bump_pc_def,
      hw_steps_APPEND,hw_steps_def]
    \\ STRIP_TAC \\ IMP_RES_TAC EVERY2_TWO
    \\ FULL_SIMP_TAC std_ss [EVERY2_def,TL,HD,hw_val_def]
    \\ FULL_SIMP_TAC (srw_ss()) [hw_step_def,LET_DEF,inc_pc_def,
         arg_def,push_def,overflow_def]
    \\ Cases_on `y1` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ STRIP_TAC \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [hw_val_def,EVAL ``hwml_length CallPtr``,word_add_n2w]
    \\ DECIDE_TAC)
  THEN1 (* JumpPtr *)
   (FULL_SIMP_TAC (srw_ss()) [hw_step_def,LET_DEF,inc_pc_def,
      arg_def,push_def,overflow_def,hw_steps_def,hw_inv_aux_def] \\ STRIP_TAC
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [hw_val_def]
    \\ Q.PAT_ASSUM `w2n h = ptr` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* Return *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,
      overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def]
    \\ STRIP_TAC \\ IMP_RES_TAC EVERY2_TWO \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [hw_val_def]
    \\ Q.PAT_ASSUM `w2n h = ptr` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* Ref *)
   (FULL_SIMP_TAC std_ss [RIGHT_AND_OVER_OR]
    \\ Q.PAT_ASSUM `ptr = xxx` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,heap_load_def,
         overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def,
         heap_address_def,heap_alloc_def]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_length_thm,EVAL ``LENGTH (hwml Ref)``]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w] \\ REPEAT STRIP_TAC
    \\ `ptr NOTIN FDOM s.refs` by
      (`?p. (\p. ~(p IN FDOM s.refs)) p` by ALL_TAC THEN1
          (FULL_SIMP_TAC std_ss []
           \\ `~(FINITE (UNIV:num set))` by FULL_SIMP_TAC (srw_ss()) []
           \\ `FINITE (FDOM s.refs)` by FULL_SIMP_TAC (srw_ss()) []
       \\ IMP_RES_TAC IN_INFINITE_NOT_FINITE \\ METIS_TAC [])
       \\ IMP_RES_TAC whileTheory.LEAST_INTRO
       \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
    THEN1 (FULL_SIMP_TAC (srw_ss()) [hw_val_def,FLOOKUP_DEF] \\ DECIDE_TAC)
    THEN1
     (MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] EVERY2_IMP_EVERY2)
      \\ Q.EXISTS_TAC `(\x1 x2. hw_val x1 x2 s1.heap r)`
      \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC hw_val_APPEND
      \\ MATCH_MP_TAC hw_val_FUPDATE \\ FULL_SIMP_TAC std_ss [hw_refs_def])
    THEN1
     (FULL_SIMP_TAC std_ss [hw_refs_def,FDOM_FUPDATE] \\ REPEAT STRIP_TAC
      THEN1
       (MATCH_MP_TAC F11_FUPDATE \\ FULL_SIMP_TAC std_ss []
        \\ MATCH_MP_TAC IMP_NOT_IN_RANGE
        \\ FULL_SIMP_TAC std_ss [FEVERY_DEF] \\ REPEAT STRIP_TAC
        \\ Q.PAT_ASSUM `FDOM r = FDOM s.refs` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
        \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
      \\ FULL_SIMP_TAC (srw_ss()) [FEVERY_DEF] \\ STRIP_TAC
      \\ Cases_on `x' = ptr` \\ FULL_SIMP_TAC std_ss [] THEN1
       (FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,EL_APPEND2]
        \\ MATCH_MP_TAC hw_val_APPEND
        \\ MATCH_MP_TAC hw_val_FUPDATE \\ FULL_SIMP_TAC std_ss [hw_refs_def])
      \\ FULL_SIMP_TAC (srw_ss()) [FAPPLY_FUPDATE_THM,FLOOKUP_DEF]
      \\ Q.PAT_ASSUM `FDOM r = FDOM s.refs` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
      \\ STRIP_TAC \\ RES_TAC \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [EL_APPEND1]
      \\ MATCH_MP_TAC hw_val_APPEND
      \\ MATCH_MP_TAC hw_val_FUPDATE \\ FULL_SIMP_TAC std_ss [hw_refs_def]))
  THEN1 (* Deref *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,heap_load_def,
      overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def]
    \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_length_thm,EVAL ``LENGTH (hwml Deref)``]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [hw_refs_def,FEVERY_DEF]
    \\ `ptr IN FDOM r` by FULL_SIMP_TAC std_ss [] \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [hw_val_def,FLOOKUP_DEF] \\ METIS_TAC [])
  THEN1 (* Update *)
   (FULL_SIMP_TAC (srw_ss()) [hw_steps_def,hw_step_def,LET_DEF,heap_store_def,
      overflow_def,push_def,inc_pc_def,arg_def,hw_inv_aux_def,bump_pc_def]
    \\ STRIP_TAC \\ IMP_RES_TAC EVERY2_TWO \\ FULL_SIMP_TAC std_ss [EVERY2_def,TL,HD]
    \\ IMP_RES_TAC hwml_length_thm
    \\ FULL_SIMP_TAC std_ss [hwml_length_thm,EVAL ``LENGTH (hwml Update)``]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w] \\ REPEAT STRIP_TAC
    \\ ASSUME_TAC (UNDISCH hw_val_UPDATE_NTH) \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [hw_refs_def,LENGTH_UPDATE_NTH]
    \\ FULL_SIMP_TAC std_ss [FDOM_FUPDATE]
    \\ FULL_SIMP_TAC std_ss [hw_val_def,FLOOKUP_DEF]
    \\ STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [ABSORPTION]
    \\ FULL_SIMP_TAC std_ss [FEVERY_DEF,FDOM_FUPDATE,IN_INSERT]
    \\ NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
    \\ Cases_on `ptr = x'` \\ FULL_SIMP_TAC std_ss [EL_UPDATE_NTH] THEN1
     (`w2n y2 < LENGTH s1.heap` by METIS_TAC []
      \\ FULL_SIMP_TAC std_ss [EL_UPDATE_NTH])
    \\ Cases_on `(r ' x' = w2n y2)` \\ FULL_SIMP_TAC std_ss [EL_UPDATE_NTH_NEQ]
    \\ FULL_SIMP_TAC (srw_ss()) [F11_def,FLOOKUP_DEF] \\ METIS_TAC []));

val hw_inv_def = Define `
  hw_inv s s1 = ?r. hw_inv_aux s s1 r`;

val hw_steps_hwml = prove(
  ``!s t.
      bc_next s t ==> !s1. s.pc < 2**32-100 /\ hw_inv s s1 /\ ~s1.error ==>
        let t1 = hw_steps (hwml (THE (bc_fetch s))) s1 in ~t1.error ==> hw_inv t t1``,
  METIS_TAC [hw_steps_hwml_lemma,hw_inv_def]);

val hw_pc_next_def = Define `
  hw_pc_next i = !s. (hw_step i s).pc = s.pc + 1w`;

val EVERY_FRONT = prove(
  ``!xs P. EVERY P xs /\ ~(xs = []) ==> EVERY P (FRONT xs)``,
  Induct \\ FULL_SIMP_TAC std_ss [EVERY_DEF] \\ Cases_on `xs`
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,FRONT_DEF,NOT_CONS_NIL]);

val EVERY_REPLICATE = prove(
  ``!n P x. EVERY P (REPLICATE n x) = (n = 0) \/ P x``,
  Induct \\ FULL_SIMP_TAC std_ss [EVERY_DEF,REPLICATE,ADD1] \\ METIS_TAC []);

val push_imm_next = prove(
  ``!n. EVERY hw_pc_next (push_imm n)``,
  HO_MATCH_MP_TAC (fetch "-" "push_imm_ind")
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [push_imm_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val push_fixed_imm_next = prove(
  ``!n. EVERY hw_pc_next (push_fixed_imm n)``,
  SRW_TAC [] [push_fixed_imm_def] \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val hwml_next = prove(
  ``!x. ~is_Label x ==> EVERY hw_pc_next (FRONT (hwml x)) /\ ~(hwml x = [])``,
  Cases \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC std_ss [hwml_def,FRONT_DEF,EVERY_DEF,is_Label_def]
  \\ SRW_TAC [] []
  THEN1 (EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  THEN1
   (MATCH_MP_TAC EVERY_FRONT \\ STRIP_TAC THEN1
     (POP_ASSUM (K ALL_TAC) \\ Induct_on `n`
      \\ FULL_SIMP_TAC std_ss [REPLICATE,FLAT,APPEND,EVERY_DEF]
      \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE,FLAT])
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [REPLICATE,FLAT])
  \\ SIMP_TAC std_ss [REWRITE_RULE [SNOC_APPEND] FRONT_SNOC]
  \\ TRY (MATCH_MP_TAC EVERY_FRONT)
  \\ FULL_SIMP_TAC (srw_ss()) [EVERY_REPLICATE,push_imm_next,push_fixed_imm_next]
  \\ TRY (ONCE_REWRITE_TAC [push_imm_def] \\ SRW_TAC [] [] \\ NO_TAC)
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val hw_step_rel_lemma = prove(
  ``!ys xs zs s.
      EVERY hw_pc_next (FRONT ys) /\ ys <> [] /\
      (w2n s.pc = LENGTH xs) /\ LENGTH (xs ++ ys ++ zs) < 2**32-100 ==>
      RTC (hw_step_rel (xs ++ ys ++ zs)) s (hw_steps ys s)``,
  Induct \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL] \\ Cases_on `ys` THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [hw_steps_def] \\ MATCH_MP_TAC RTC_SINGLE
    \\ FULL_SIMP_TAC std_ss [hw_step_rel_def,LENGTH_APPEND,APPEND,LENGTH]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH_APPEND,NULL_DEF,HD] \\ DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [FRONT_DEF] \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,EVERY_DEF]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [hw_steps_def]
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE]
  \\ Q.EXISTS_TAC `hw_step h' s` \\ STRIP_TAC THEN1
   (MATCH_MP_TAC RTC_SINGLE
    \\ FULL_SIMP_TAC std_ss [hw_step_rel_def,LENGTH_APPEND,APPEND,LENGTH]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [EL_LENGTH_APPEND,NULL_DEF,HD] \\ DECIDE_TAC)
  \\ `xs ++ h'::h::t ++ zs = (xs ++ [h']) ++ h::t ++ zs` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [] \\ Q.PAT_ASSUM `!xss.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [hw_pc_next_def,LENGTH_APPEND,LENGTH]
  \\ Cases_on `s.pc` \\ FULL_SIMP_TAC (srw_ss()) [word_add_n2w]
  \\ DECIDE_TAC);

val bc_next_IMP_fetch = prove(
  ``!x y. bc_next x y ==> ?z. bc_fetch x = SOME z``,
  SIMP_TAC std_ss [bc_next_cases] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []);

val hwml_NOT_NIL_IMP = prove(
  ``!x. hwml x <> [] ==> ~is_Label x``,
  Cases \\ TRY (Cases_on `b`) \\ TRY (Cases_on `l`)
  \\ SRW_TAC [] [is_Label_def,hwml_def]);

val bc_next_IMP_RTC_hw_step_rel = prove(
  ``!s t s1.
      bc_next s t /\ hw_inv s s1 /\ ~s1.error ==>
      let code = full_hwml s.code in
        LENGTH code < 2**32-100 ==>
        ?t1. RTC (hw_step_rel code) s1 t1 /\ (~t1.error ==> hw_inv t t1)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC hw_steps_hwml \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `hw_steps (hwml (THE (bc_fetch s))) s1`
  \\ FULL_SIMP_TAC std_ss []
  \\ `?xs zs. (full_hwml s.code = xs ++ hwml (THE (bc_fetch s)) ++ zs) /\
              (LENGTH xs = s.pc)` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [hw_inv_aux_def,hw_inv_def] \\ IMP_RES_TAC bc_next_IMP_fetch
    \\ FULL_SIMP_TAC std_ss [bc_fetch_def]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Q.SPEC_TAC (`s.pc`,`n`) \\ Q.SPEC_TAC (`s.code`,`xs`)
    \\ Induct \\ TRY (STRIP_TAC \\ Cases_on `h`)
    \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_def] \\ SRW_TAC [] []
    \\ TRY (Q.LIST_EXISTS_TAC [`[]`,`full_hwml xs`] \\ EVAL_TAC \\ NO_TAC)
    \\ TRY (FULL_SIMP_TAC std_ss [full_hwml_def,MAP,hwml_def,FLAT,APPEND] \\ NO_TAC)
    \\ Q.PAT_ABBREV_TAC `h = (ttt:bc_inst)`
    \\ MP_TAC (Q.SPEC `h` hwml_length_lemma |> Q.GEN `p` |> Q.SPEC `0`) \\ STRIP_TAC
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [full_hwml_def,FLAT,MAP,APPEND_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`hwml h ++ xs'`,`zs`]
    \\ Q.UNABBREV_TAC `h` \\ FULL_SIMP_TAC std_ss [is_Label_def]
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
    \\ DECIDE_TAC)
  \\ `s.pc < 4294967196` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `hwml (THE (bc_fetch s)) = []`
  THEN1 (FULL_SIMP_TAC std_ss [hw_steps_def,RTC_REFL])
  \\ MATCH_MP_TAC hw_step_rel_lemma \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC hwml_NOT_NIL_IMP
  \\ IMP_RES_TAC hwml_next
  \\ FULL_SIMP_TAC std_ss [hw_inv_aux_def,hw_inv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val full_hw_inv_def = Define `
  full_hw_inv s s1 = (~s1.error ==> hw_inv s s1)`;

val bc_next_IMP_RTC_hw_step_rel_lemma = prove(
  ``!s t s1.
      bc_next s t /\ full_hw_inv s s1 ==>
      let code = full_hwml s.code in
        LENGTH code < 2**32-100 ==>
        ?t1. RTC (hw_step_rel code) s1 t1 /\ full_hw_inv t t1``,
  FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [full_hw_inv_def] \\ Cases_on `s1.error`
  THEN1 (Q.EXISTS_TAC `s1` \\ FULL_SIMP_TAC std_ss [RTC_REFL])
  \\ IMP_RES_TAC (bc_next_IMP_RTC_hw_step_rel |> SIMP_RULE std_ss [LET_DEF])
  \\ FULL_SIMP_TAC std_ss []) |> SIMP_RULE std_ss [LET_DEF];

val bc_next_code = prove(
  ``!s t. bc_next s t ==> (t.code = s.code)``,
  FULL_SIMP_TAC std_ss [bc_next_cases] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bump_pc_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC (srw_ss()) [bc_fetch_def]);

val hw_step_rel_correct = store_thm("hw_step_rel_correct",
  ``!s t.
      RTC bc_next s t ==>
      let code = full_hwml s.code in
        !s1. full_hw_inv s s1 /\ LENGTH code < 2**32-100 ==>
             ?t1. RTC (hw_step_rel code) s1 t1 /\ full_hw_inv t t1``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT STRIP_TAC THEN1 (Q.EXISTS_TAC `s1` \\ FULL_SIMP_TAC std_ss [RTC_REFL])
  \\ IMP_RES_TAC bc_next_IMP_RTC_hw_step_rel_lemma
  \\ IMP_RES_TAC bc_next_code \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ Q.EXISTS_TAC `t1''` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [RTC_CASES_RTC_TWICE] \\ METIS_TAC []);

val _ = export_theory();

