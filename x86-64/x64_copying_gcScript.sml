open HolKernel Parse boolLib bossLib lcsymtacs; val _ = new_theory "x64_copying_gc";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;
open prog_x64_extraTheory;

open ml_copying_gcTheory ml_heapTheory x64_compilerLib;
open set_sepTheory;
open helperLib;
open addressTheory

infix \\ val op \\ = op THEN;


(* invariant informally:
     Unused -- don't care
     ForwardPointer -- head contains ptr, rest don't care
     DataElement -- header + payload
   all pointers end in 111
   all data end in 0
*)

val x64_addr_def = Define `
  (x64_addr base (Pointer n) = base + n2w n << 3 - 1w) /\
  (x64_addr base (Data w) = (w2w:63 word -> word64) w << 1)`;

val one_list_def = Define `
  (one_list a [] = emp) /\
  (one_list a (x::xs) = one (a,x) * one_list (a+8w) xs)`;

val one_list_exists_def = Define `
  one_list_exists a n =
    SEP_EXISTS xs. one_list a xs * cond (LENGTH xs = n)`;

val b2w_def = Define `b2w b = if b then 1w else 0w`;

val x64_payload_def = Define `
  (x64_payload ys l (BlockTag n) qs base =
     let h = n2w l << 16 + n2w (n MOD 2**12) << 4 in
     let ts = MAP (x64_addr base) ys in
     let c = (qs = []) /\ (LENGTH ys = l) /\ l < 2 ** (64 - 16) in
       (h:word64,ts,c)) /\
  (x64_payload ys l (RefTag) qs base =
     let h = n2w l << 16 + 1w in
     let ts = MAP (x64_addr base) ys in
     let c = (qs = []) /\ (LENGTH ys = l) /\ (l < 2 ** (64 - 16)) in
       (h,ts,c)) /\
  (x64_payload ys l (NumTag b) qs base =
     let h = n2w l << 16 + 2w + b2w b in
     let ts = qs in
     let c = (ys = []) /\ (LENGTH qs = l) /\ l < 2 ** (64 - 16) in
       (h,ts,c)) /\
  (x64_payload ys l (BytesTag n) qs base =
     let h = n2w l << 16 + n2w (n MOD 8) << 13 + 6w in
     let ts = qs in
     let c = (ys = []) /\ (LENGTH qs = l) /\ l < 2 ** (64 - 16) in
       (h,ts,c))`;

val x64_el_def = Define `
  (x64_el a (Unused l) bf bd = one_list_exists a (l+1)) /\
  (x64_el a (ForwardPointer n l) bf bd =
     one (a,x64_addr bf (Pointer n)) * one_list_exists (a+8w) l) /\
  (x64_el a (DataElement ys l (tag,qs)) bf bd =
     let (h,ts,c) = x64_payload ys l tag qs bd in
       one (a,h) * one_list (a+8w) ts * cond c)`;

val x64_heap_def = Define `
  (x64_heap a [] bf bd = emp) /\
  (x64_heap a (x::xs) bf bd =
     x64_el a x bf bd * x64_heap (a + n2w (8 * el_length x)) xs bf bd)`;

(* implementation *)

val (res, x64_copy_data_def, x64_copy_data_pre_def) = x64_compile `
  x64_copy_data (r1:word64,r2:word64,r3:word64,dm:word64 set,m:word64->word64) =
    if r2 = 0w then (r1,dm,m) else
      let r2 = r2 - 1w in
      let r6 = m r3 in
      let m = (r1 =+ r6) m in
      let r3 = r3 + 8w in
      let r1 = r1 + 8w in
        x64_copy_data (r1,r2,r3,dm,m)`

val (res, x64_move_def, x64_move_pre_def) = x64_compile `
  x64_move (r0:word64,r1:word64,dm:word64 set,m:word64->word64) =
    if r0 && 1w = 0w (* data *) then (r0,r1,dm,m) else (* pointer *)
      let r2 = m (r0 + 1w) in
      let r3 = r2 && 7w in
        if r3 = 7w then (* is forward pointer *)
          let r0 = r2 in (r0,r1,dm,m)
        else (* is data element *)
          let r1 = r1 - 1w in
          let m = (r0+1w =+ r1) m in (* store new forward pointer *)
          let m = (r1+1w =+ r2) m in (* store head into new location *)
          let r3 = r0 + 9w in
          let r0 = r1 in
          let r1 = r1 + 9w in
          let r2 = r2 >>> 16 in
          let (r1,dm,m) = x64_copy_data (r1,r2,r3,dm,m) in
            (r0,r1,dm,m)`

val (res, x64_move_list_def, x64_move_list_pre_def) = x64_compile `
  x64_move_list (r1,r7:word64,r8:word64,dm,m) =
    if r7 = 0w then (r1,r8,dm,m) else
      let r7 = r7 - 1w in
      let r0 = m r8 in
      let (r0,r1,dm,m) = x64_move (r0,r1,dm,m) in
      let m = (r8 =+ r0) m in
      let r8 = r8 + 8w in
        x64_move_list (r1,r7,r8,dm,m)`

val (res, x64_move_loop_def, x64_move_loop_pre_def) = x64_compile `
  x64_move_loop (r1,r8:word64,dm,m) =
    if r1 = r8 then (r8,dm,m) else
      let r0 = m r8 in (* header of DataElement to be updated *)
      let r8 = r8 + 8w in
      let r7 = r0 >>> 16 in
        if (r0 && 2w) <> 0w then (* only data -- no pointers to update *)
          let r7 = r7 << 3 in
          let r8 = r8 + r7 in
            x64_move_loop (r1,r8,dm,m)
        else (* need to update pointers in payload *)
          let (r1,r8,dm,m) = x64_move_list (r1,r7,r8,dm,m) in
            x64_move_loop (r1,r8,dm,m)`

val _ = x64_codegenLib.add_compiled [x64_el_r0_r8,x64_lupdate_r0_r8]

val (res, x64_move_stack_def, x64_move_stack_pre_def) = x64_compile `
  x64_move_stack (r1,r8:word64,ss:word64 list,dm,m) =
    let r0 = EL (w2n r8 DIV 8) ss in
      if r0 = 1w then (r1,ss,dm,m) else
        let (r0,r1,dm,m) = x64_move (r0,r1,dm,m) in
        let ss = LUPDATE r0 (w2n r8 DIV 8) ss in
        let r8 = r8 + 8w in
          x64_move_stack (r1,r8,ss,dm,m)`

val (x64_full_gc_res, x64_full_gc_def, x64_full_gc_pre_def) = x64_compile `
  x64_full_gc (r7,ss,dm,m) =
    let r1 = r7 in
    let r8 = 0w in
    let (r1,ss,dm,m) = x64_move_stack (r1,r8,ss,dm,m) in
    let r8 = r7 in
    let (r8,dm,m) = x64_move_loop (r1,r8,dm,m) in
      (r8,ss,dm,m)`

val _ = save_thm("x64_full_gc_res",x64_full_gc_res);

(* verification *)

val x64_payload_length = prove(
  ``(x64_payload zs l q rs bd = (x1,x2,T)) ==> (LENGTH x2 = l)``,
  Cases_on `q` \\ FULL_SIMP_TAC std_ss [x64_payload_def,LET_DEF]
  \\ METIS_TAC [LENGTH_MAP]);

val align64_lemma = prove(
  ``(n2w base && 0x7w = 0x0w:word64) ==>
    (n2w (base + 8 * el_length h) && 0x7w = 0x0w:word64)``,
  FULL_SIMP_TAC std_ss [GSYM word_add_n2w,GSYM word_mul_n2w]
  \\ blastLib.BBLAST_TAC);

val x64_copy_data_thm = prove(
  ``!xs ys r1 r3 r m dm.
      (one_list r1 xs * one_list r3 ys * r) (fun2set (m,dm)) /\
      (r1 && 7w = 0w) /\ (r3 && 7w = 0w) /\ (LENGTH ys = LENGTH xs) /\
      LENGTH xs < 2**64 ==>
      ?m1. x64_copy_data_pre (r1,n2w (LENGTH xs),r3,dm,m) /\
           (x64_copy_data (r1,n2w (LENGTH xs),r3,dm,m) = (r1 + n2w (8 * (LENGTH xs)),dm,m1)) /\
           (one_list r1 ys * one_list r3 ys * r) (fun2set (m1,dm))``,
  Induct THEN1
   (FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL]
    \\ ONCE_REWRITE_TAC [x64_copy_data_def,x64_copy_data_pre_def]
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,one_list_def]
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t`)
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC (DECIDE ``n + 1 < k ==> n < k:num``)
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [x64_copy_data_def,x64_copy_data_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [GSYM word_sub_def,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ SEP_I_TAC "x64_copy_data"
  \\ POP_ASSUM (MP_TAC o Q.SPEC `one (r1,h) * one (r3,h) * r`)
  \\ SEP_R_TAC \\ SEP_W_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [word_arith_lemma1]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ blastLib.BBLAST_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]);

val blast_lemma = blastLib.BBLAST_PROVE ``
  (w << 1 && 0x1w = 0x0w:word64) /\
  ((b2 && 7w = 0w) ==> ((0x1w && b2 + (w << 3) - 0x1w) <> 0x0w)) /\
  ((b2 && 7w = 0w) ==> (0x7w && b2 + w << 3 - 0x1w = 0x7w))``

val blast_lemma2 = blastLib.BBLAST_PROVE ``
  (w + 8w && 7w = w && 7w:word64) /\
  (w + 8w * v && 7w = w && 7w:word64) /\
  (7w && w + 8w = 7w && w:word64) /\
  (7w && w + 8w * v = 7w && w :word64)``

val x64_payload_test = prove(
  ``!x1 x2 x3.
      (x64_payload ys l x qs base = (x1,x2,T)) ==>
      if x1 && 2w = 0w then (x2 = MAP (x64_addr base) ys) else (ys = []) /\
        ((?b. x = NumTag b) ∨ (?n. x = BytesTag n))``,
  Cases_on `x` \\ FULL_SIMP_TAC std_ss [x64_payload_def,LET_DEF]
  \\ REPEAT STRIP_TAC
  THEN1 (DISJ1_TAC \\ blastLib.BBLAST_TAC) THEN1 (DISJ1_TAC \\ blastLib.BBLAST_TAC)
  THEN1 (
    Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) [b2w_def]
  \\ POP_ASSUM MP_TAC \\ blastLib.BBLAST_TAC)
  \\ (
    REV_FULL_SIMP_TAC (srw_ss()) [GSYM word_add_n2w,GSYM word_mul_n2w]
    \\ rpt strip_tac >> spose_not_then strip_assume_tac
    \\ pop_assum kall_tac >> pop_assum mp_tac >> simp[]
    \\ blastLib.BBLAST_TAC));

val x64_payload_new = prove(
  ``(x64_payload ys l x qs base = (x1,x2,T)) /\ (x1 && 2w = 0w) /\
    (LENGTH ys2 = LENGTH ys) ==>
    (x64_payload ys2 l x qs base2 = (x1,MAP (x64_addr base2) ys2,T))``,
  Cases_on `x` \\ FULL_SIMP_TAC std_ss [x64_payload_def,LET_DEF]
  THEN1 (
    REPEAT STRIP_TAC \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [b2w_def]
  \\ REPEAT (POP_ASSUM MP_TAC) \\ blastLib.BBLAST_TAC)
  THEN (
    rw[] >> fs[LENGTH_NIL] >>
    spose_not_then kall_tac >>
    pop_assum kall_tac >> pop_assum mp_tac >>
    simp[] >>
    simp[GSYM word_mul_n2w,GSYM word_add_n2w] >>
    blastLib.BBLAST_TAC));

val x64_heap_APPEND = store_thm("x64_heap_APPEND",
  ``!xs ys a bf bd.
      x64_heap a (xs ++ ys) bf bd =
      x64_heap a xs bf bd * x64_heap (a + n2w (8 * heap_length xs)) ys bf bd``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,SEP_CLAUSES,x64_heap_def,word_arith_lemma1,
       heap_length_def,MAP,SUM,WORD_ADD_0,STAR_ASSOC,LEFT_ADD_DISTRIB]);

val x64_addr_AND_7 = prove(
  ``(0x7w && x64_addr b1 (Pointer ptr) = 0x7w) = (b1 && 7w = 0w)``,
  FULL_SIMP_TAC std_ss [x64_addr_def] \\ blastLib.BBLAST_TAC);

val x64_payload_not_ptr = prove(
  ``(x64_payload l n2 q r' b2 = (t1,t2:word64 list,T)) ==>
    ~(0x7w && t1 = 0x7w:word64) /\
    (t1 >>> 16 = n2w (LENGTH t2)) /\
    LENGTH l < 281474976710656``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [] \\ Cases_on `q`
  \\ FULL_SIMP_TAC std_ss [x64_payload_def,LET_DEF,LENGTH_MAP,LENGTH]
  \\ REPEAT STRIP_TAC \\ TRY (Cases_on `b:bool`) \\ FULL_SIMP_TAC std_ss [b2w_def]
  \\ TRY (POP_ASSUM MP_TAC \\ blastLib.BBLAST_TAC \\ NO_TAC)
  \\ `n2 < 18446744073709551616` by DECIDE_TAC
  \\ `n2w n2 <+ (n2w 281474976710656):word64` by FULL_SIMP_TAC (srw_ss()) [WORD_LO]
  \\ `n2w (n MOD 4096) <+ (n2w 4096) :word64` by
   (`n MOD 4096 < 4096` by FULL_SIMP_TAC (srw_ss()) []
    \\ `n MOD 4096 < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
  \\ `n2w (n MOD 8) = (w2w:3 word -> word64) (n2w (n MOD 8))` by (simp[w2w_def])
  \\ fs[GSYM word_add_n2w,GSYM word_mul_n2w]
  \\ pop_assum kall_tac
  \\ TRY (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ blastLib.BBLAST_TAC \\ NO_TAC)
  \\ qpat_assum`X = Y`mp_tac \\ fs[] \\ blastLib.BBLAST_TAC);

val LESS_EQ_APPEND = prove(
  ``!xs n. n <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = n)``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH_NIL,APPEND]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `h::ys1`
  \\ Q.EXISTS_TAC `ys2` \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,ADD1]);

val one_list_exists_ZERO = store_thm("one_list_exists_ZERO",
  ``one_list_exists a 0 = emp``,
  SIMP_TAC std_ss [FUN_EQ_THM,one_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM,
    cond_STAR,LENGTH_NIL,one_list_def]);

val one_list_exists_SUC = store_thm("one_list_exists_SUC",
  ``!n a. one_list_exists a (SUC n) =
          SEP_EXISTS t4. one (a,t4) * one_list_exists (a+8w) n``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,SEP_EXISTS_THM,one_list_exists_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,cond_STAR]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Cases_on `xs` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH]
    \\ FULL_SIMP_TAC std_ss [one_list_def] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `t4::xs` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH,one_list_def]);

val one_list_APPEND = store_thm("one_list_APPEND",
  ``!xs ys a.
      one_list a (xs ++ ys) = one_list a xs * one_list (a + n2w (8 * LENGTH xs)) ys``,
  Induct \\ FULL_SIMP_TAC std_ss [one_list_def,LENGTH,APPEND,SEP_CLAUSES,
    WORD_ADD_0,STAR_ASSOC,MULT_CLAUSES,word_arith_lemma1]);

val SUB1_ADD9 = prove(
  ``!w. w - 1w + 9w = w + 8w``,
  FULL_SIMP_TAC std_ss [word_arith_lemma3]);

val x64_move_thm = prove(
  ``!x2 heap n h2 c limit x1 heap' n' h2' r.
    (gc_move (x2,heap,b + heap_length heap,n,h2,c,limit) =
      (x1,heap',b + heap_length heap',n',h2',T)) /\
    (x64_heap (b1 + n2w (8 * b)) heap b2 b2 *
     one_list_exists (b1 + n2w (8 * b + 8 * heap_length heap)) n *
     x64_heap b2 h2 b1 b2 * r) (fun2set (m,dm)) /\
    (b2 && 7w = 0w) /\ (b1 && 7w = 0w) /\ limit < 2**64 ==>
    ?m1. x64_move_pre (x64_addr b2 x2,(b1 + n2w (8 * b + 8 * heap_length heap)),dm,m) /\
         (x64_move (x64_addr b2 x2,(b1 + n2w (8 * b + 8 * heap_length heap)),dm,m) =
           (x64_addr b1 x1,(b1 + n2w (8 * b + 8 * heap_length heap')),dm,m1)) /\ c /\
         (x64_heap (b1 + n2w (8 * b)) heap' b2 b2 *
          one_list_exists (b1 + n2w (8 * b + 8 * heap_length heap')) n' *
          x64_heap b2 h2' b1 b2 * r) (fun2set (m1,dm))``,

  NTAC 11 STRIP_TAC
  \\ REVERSE (Cases_on `x2`)
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [gc_move_def,x64_addr_def]
  \\ FULL_SIMP_TAC std_ss [x64_move_def, x64_move_pre_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [blast_lemma]
  \\ Cases_on `heap_lookup n'' h2` THEN1 (FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `x` THEN1 (FULL_SIMP_TAC (srw_ss()) [])
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV (srw_ss()) [blast_lemma]))
  \\ FULL_SIMP_TAC std_ss [blast_lemma,WORD_SUB_ADD] THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [AC WORD_AND_COMM WORD_AND_ASSOC,blast_lemma]
    \\ Q.MATCH_ASSUM_RENAME_TAC `heap_lookup n1 h2 = SOME (ForwardPointer ptr n2)` []
    \\ IMP_RES_TAC heap_lookup_SPLIT \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND]
    \\ FULL_SIMP_TAC std_ss [x64_heap_def,x64_el_def,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
    \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ FULL_SIMP_TAC std_ss [x64_addr_AND_7]
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ NTAC 2 (POP_ASSUM MP_TAC) \\ blastLib.BBLAST_TAC)
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC WORD_AND_COMM WORD_AND_ASSOC,blast_lemma]
  \\ Q.MATCH_ASSUM_RENAME_TAC `heap_lookup n1 h2 = SOME (DataElement l n2 b')` []
  \\ IMP_RES_TAC heap_lookup_SPLIT \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND]
  \\ Cases_on `b'` \\ FULL_SIMP_TAC std_ss [x64_heap_def,x64_el_def,STAR_ASSOC]
  \\ `?t1 t2 t3. x64_payload l n2 q r' b2 = (t1:word64,t2,t3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
  \\ REPEAT STRIP_TAC \\ SEP_R_TAC
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ IMP_RES_TAC x64_payload_not_ptr \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [gc_forward_ptr_thm,x64_heap_APPEND]
  \\ FULL_SIMP_TAC std_ss [x64_heap_def,x64_el_def,STAR_ASSOC,SEP_CLAUSES,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [el_length_def,LET_DEF,WORD_SUB_ADD]
  \\ Cases_on `n` THEN1 `F` by DECIDE_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `n2 + 1 <= SUC n` []
  \\ FULL_SIMP_TAC std_ss [one_list_exists_SUC,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ SEP_W_TAC
  \\ Q.ABBREV_TAC `m3 = (b1 + n2w (8 * b + 8 * heap_length heap) =+ t1)
               ((b2 + n2w (8 * heap_length ha) =+
                 b1 + n2w (8 * b + 8 * heap_length heap) - 1w) m)`
  \\ `b1 + n2w (8 * b + 8 * heap_length heap) - 0x1w + 0x9w =
      b1 + n2w (8 * b + 8 * heap_length heap) + 0x8w` by ALL_TAC THEN1
   (Q.SPEC_TAC (`b1 + n2w (8 * heap_length heap)`,`w`)
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3])
  \\ `b1 + n2w (8 * b + 8 * heap_length heap) - 0x1w =
      x64_addr b1 (Pointer (b + heap_length heap))` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [x64_addr_def,WORD_MUL_LSL,word_mul_n2w,LEFT_ADD_DISTRIB])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `xxx (fun2set (m,dm))` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [one_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ FULL_SIMP_TAC std_ss [ADD1]
  \\ `n2 <= LENGTH xs` by FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LESS_EQ_APPEND
  \\ Q.PAT_ASSUM `LENGTH ys1 = n2` (ASSUME_TAC o GSYM)
  \\ `LENGTH t2 = LENGTH ys1` by ALL_TAC THEN1
   (IMP_RES_TAC x64_payload_length \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [one_list_APPEND]
  \\ FULL_SIMP_TAC std_ss [SUB1_ADD9]
  \\ ASSUME_TAC x64_copy_data_thm
  \\ SEP_I_TAC "x64_copy_data"
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `t2`)
  \\ SEP_F_TAC \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [blast_lemma2,GSYM word_mul_n2w,LENGTH_APPEND,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES,GSYM word_add_n2w,GSYM ADD1,LEFT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [blast_lemma2,GSYM word_mul_n2w,LENGTH_APPEND,heap_length_APPEND]
  \\ FULL_SIMP_TAC std_ss [AC WORD_AND_COMM WORD_AND_ASSOC]
  \\ SEP_R_TAC \\ SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [blast_lemma2,GSYM word_mul_n2w,LENGTH_APPEND,GSYM word_add_n2w,WORD_ADD_ASSOC] \\ METIS_TAC [WORD_AND_COMM])
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w,LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [EVAL ``heap_length [DataElement l xs y]``,el_length_def,SUM,LEFT_ADD_DISTRIB,GSYM word_add_n2w]
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  \\ Q.EXISTS_TAC `ys2` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ Q.EXISTS_TAC `t2` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_ASSOC WORD_ADD_COMM]);

val x64_move_list_thm = prove(
  ``!xs2 heap n h2 c limit xs1 b heap' n' h2' a m r.
      (gc_move_list (xs2,heap,b + heap_length heap,n,h2,c,limit) =
        (xs1,heap',b + heap_length heap',n',h2',T)) /\
      (one_list a (MAP (x64_addr b2) xs2) *
       x64_heap (b1 + n2w (8 * b)) heap b2 b2 *
       one_list_exists (b1 + n2w (8 * b + 8 * heap_length heap)) n *
       x64_heap b2 h2 b1 b2 * r) (fun2set (m,dm)) /\
      (b2 && 7w = 0w) /\ (b1 && 7w = 0w) /\ limit < 2**64 /\
      LENGTH xs2 < 2**64 /\ (a && 7w = 0w) ==>
      ?m1. x64_move_list_pre ((b1 + n2w (8 * b + 8 * heap_length heap)),n2w (LENGTH xs2),a,dm,m) /\
           (x64_move_list ((b1 + n2w (8 * b + 8 * heap_length heap)),n2w (LENGTH xs2),a,dm,m) =
             ((b1 + n2w (8 * b + 8 * heap_length heap')),a + n2w (8 * LENGTH xs2),dm,m1)) /\ c /\
           (one_list a (MAP (x64_addr b1) xs1) *
            x64_heap (b1 + n2w (8 * b)) heap' b2 b2 *
            one_list_exists (b1 + n2w (8 * b + 8 * heap_length heap')) n' *
            x64_heap b2 h2' b1 b2 * r) (fun2set (m1,dm))``,
  Induct \\ FULL_SIMP_TAC std_ss [gc_move_list_def,MAP,LENGTH]
  \\ ONCE_REWRITE_TAC [x64_move_list_def,x64_move_list_pre_def]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,ADD1,LET_DEF]
  \\ SIMP_TAC std_ss [Once EQ_SYM_EQ] \\ REPEAT STRIP_TAC
  \\ `?x4 h24 a4 n4 heap4 c4. gc_move (h,heap,b + heap_length heap,n,h2,c,limit) =
      (x4,h24,a4,n4,heap4,c4)` by METIS_TAC [PAIR]
  \\ `?xs5 h25 a5 n5 heap5 c5. gc_move_list (xs2,h24,a4,n4,heap4,c4,limit) =
      (xs5,h25,a5,n5,heap5,c5)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [one_list_def] \\ SEP_R_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB,MAP,one_list_def]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ (x64_move_thm |> ASSUME_TAC)
  \\ SEP_I_TAC "x64_move"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`n`,`h2`,`c`,`limit`])
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ SEP_F_TAC
  \\ MATCH_MP_TAC IMP_IMP
  \\ `c4 /\ c5 /\ (a4 = b + heap_length h24)` by ALL_TAC THEN1
   (Cases_on `c5` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_list_ok \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_ok \\ POP_ASSUM (MP_TAC o Q.SPEC `b`)
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1 FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SEP_W_TAC \\ SEP_R_TAC
  \\ Q.ABBREV_TAC `m2 = (a =+ x64_addr b1 x4) m1`
  \\ SEP_I_TAC "x64_move_list"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`n4`,`heap4`,`c4`,`limit`])
  \\ `a5 = b + heap_length h25` by ALL_TAC THEN1
   (Cases_on `c5` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_list_ok \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM (MP_TAC o Q.SPEC `b`) \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [blast_lemma2,LEFT_ADD_DISTRIB,
       GSYM word_add_n2w,word_mul_n2w]
  \\ REPEAT STRIP_TAC \\ SEP_F_TAC
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val x64_move_stack_thm = prove(
  ``!xs2 xs0 heap n h2 c limit xs1 heap' n' h2' m r.
      (gc_move_list (xs2,heap,heap_length heap,n,h2,c,limit) =
        (xs1,heap',heap_length heap',n',h2',T)) /\
      (x64_heap b1 heap b2 b2 *
       one_list_exists (b1 + n2w (8 * heap_length heap)) n *
       x64_heap b2 h2 b1 b2 * r) (fun2set (m,dm)) /\
      (b2 && 7w = 0w) /\ (b1 && 7w = 0w) /\ limit < 2**64 /\
      8 * (LENGTH xs2 + LENGTH xs0) < 2**64 ==>
      ?m1. x64_move_stack_pre ((b1 + n2w (8 * heap_length heap)),n2w (8 * LENGTH xs0),xs0 ++ MAP (x64_addr b2) xs2 ++ 1w::stack,dm,m) /\
           (x64_move_stack ((b1 + n2w (8 * heap_length heap)),n2w (8 * LENGTH xs0),xs0 ++ MAP (x64_addr b2) xs2 ++ 1w::stack,dm,m) =
             ((b1 + n2w (8 * heap_length heap')),xs0 ++ MAP (x64_addr b1) xs1 ++ 1w::stack,dm,m1)) /\ c /\
           (x64_heap b1 heap' b2 b2 *
            one_list_exists (b1 + n2w (8 * heap_length heap')) n' *
            x64_heap b2 h2' b1 b2 * r) (fun2set (m1,dm))``,
  Induct
  \\ FULL_SIMP_TAC std_ss [gc_move_list_def,LENGTH,MAP,APPEND_NIL]
  \\ ONCE_REWRITE_TAC [x64_move_stack_def,x64_move_stack_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ `((w2n (n2w (8 * LENGTH xs0):word64) DIV 8) = LENGTH xs0) /\
      (w2n (n2w (8 * LENGTH xs0):word64) MOD 8 = 0)` by
   (`8 * (LENGTH xs0) < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ ONCE_REWRITE_TAC [MULT_COMM]
    \\ FULL_SIMP_TAC std_ss [MULT_DIV,MOD_EQ_0])
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND,NULL,HD,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ `x64_addr b2 h <> 0x1w` by
   (Cases_on `h` \\ Q.PAT_ASSUM `b2 && 7w = 0w` MP_TAC
    \\ FULL_SIMP_TAC std_ss [x64_addr_def] \\ blastLib.BBLAST_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `?x4 h24 a4 n4 heap4 c4. gc_move (h,heap,heap_length heap,n,h2,c,limit) =
      (x4,h24,a4,n4,heap4,c4)` by METIS_TAC [PAIR]
  \\ `?xs5 h25 a5 n5 heap5 c5. gc_move_list (xs2,h24,a4,n4,heap4,c4,limit) =
      (xs5,h25,a5,n5,heap5,c5)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ (x64_move_thm |> Q.INST [`b`|->`0`] |> SIMP_RULE std_ss [] |> ASSUME_TAC)
  \\ SEP_I_TAC "x64_move"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`n`,`h2`,`c`,`limit`])
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `r`)
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP
  \\ `c4 /\ c5 /\ (a4 = heap_length h24)` by ALL_TAC THEN1
   (Cases_on `c5` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_list_ok \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_ok \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC std_ss [])
  \\ STRIP_TAC THEN1 FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH]
  \\ `xs0 ++ x64_addr b1 x4::(MAP (x64_addr b2) xs2 ++ 0x1w::stack) =
      SNOC (x64_addr b1 x4) xs0 ++ (MAP (x64_addr b2) xs2 ++ 0x1w::stack)`
         by FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [word_add_n2w]
  \\ `8 * LENGTH xs0 + 8 = 8 * LENGTH (SNOC (x64_addr b1 x4) xs0)`
         by FULL_SIMP_TAC std_ss [LENGTH_SNOC,MULT_CLAUSES,AC ADD_COMM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_I_TAC "x64_move_stack"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`n4`,`heap4`,`c4`,`limit`])
  \\ `a5 = heap_length h25` by ALL_TAC THEN1
   (Cases_on `c5` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_list_ok \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM (MP_TAC o Q.SPEC `0`) \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `r`)
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1,AC ADD_COMM ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND,GSYM APPEND_ASSOC]
  \\ AP_TERM_TAC \\ Q.PAT_ASSUM `x4::xs5 = xs1` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [MAP,APPEND]);

val gc_move_list_LENGTH = prove(
  ``!l h b n h2 c limit ys3 xs3 n3 x3 heap3 c3.
      (gc_move_list (l,h,b,n,h2,c,limit) = (ys3,xs3,n3,x3,heap3,c3)) ==>
      (LENGTH l = LENGTH ys3)``,
  Induct \\ FULL_SIMP_TAC std_ss [gc_move_list_def] \\ REPEAT STRIP_TAC
  \\ `?x1 x2 x3 x4 x5 x6. gc_move (h,h',b,n,h2,c,limit) = (x1,x2,x3,x4,x5,x6)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `?y1 y2 y3 y4 y5 y6. gc_move_list (l,x2,x3',x4,x5,x6,limit) = (y1,y2,y3,y4,y5,y6)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ METIS_TAC [LENGTH]);

val x64_move_loop_thm = prove(
  ``!heap n h2 c xs1 b heap' n' h2' a r m.
      (gc_move_loop (h1,heap,heap_length h1 + heap_length heap,n,h2,c,limit) =
        (h1',heap_length h1',n',h2',T)) /\
      (x64_heap b1 h1 b1 b1 *
       x64_heap (b1 + n2w (8 * heap_length h1)) heap b2 b2 *
       one_list_exists (b1 + n2w (8 * heap_length (h1 ++ heap))) n *
       x64_heap b2 h2 b1 b2 * r) (fun2set (m,dm)) /\
      (b2 && 7w = 0w) /\ (b1 && 7w = 0w) /\ limit < 2**61 ==>
      ?m1. x64_move_loop_pre ((b1 + n2w (8 * heap_length (h1 ++ heap))),(b1 + n2w (8 * heap_length h1)),dm,m) /\
           (x64_move_loop ((b1 + n2w (8 * heap_length (h1 ++ heap))),(b1 + n2w (8 * heap_length h1)),dm,m) =
             ((b1 + n2w (8 * heap_length h1')),dm,m1)) /\ c /\
           (x64_heap b1 h1' b1 b1 *
            one_list_exists (b1 + n2w (8 * heap_length h1')) n' *
            x64_heap b2 h2' b1 b2 * r) (fun2set (m1,dm))``,
  completeInduct_on `limit - heap_length h1`
  \\ NTAC 3 STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL,AND_IMP_INTRO]
  \\ Cases THEN1
   (ONCE_REWRITE_TAC [x64_move_loop_def,x64_move_loop_pre_def]
    \\ SIMP_TAC (srw_ss()) [gc_move_loop_def,APPEND_NIL,x64_heap_def,SEP_CLAUSES,
         heap_length_def,GSYM AND_IMP_INTRO])
  \\ SIMP_TAC std_ss [gc_move_loop_def] \\ STRIP_TAC
  \\ Cases_on `limit < heap_length (h1 ++ h::t)` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [gc_move_list_ALT]
  \\ Q.ABBREV_TAC `b3 = heap_length h1 + heap_length (DataElement l n' b::t)`
  \\ NTAC 6 STRIP_TAC
  \\ `?ys3 xs3 a3 n3 heap3 c3.
        gc_move_list (l,[],b3,n,h2,c,limit) =
          (ys3,xs3,a3,n3,heap3,c3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,APPEND]
  \\ REPEAT STRIP_TAC
  \\ `?tag qs. b = (tag,qs)` by METIS_TAC [PAIR]
  \\ `?x1 x2 x3. x64_payload l n' tag qs b2 = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [x64_heap_def,x64_el_def,STAR_ASSOC,LET_DEF]
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ Cases_on `x3` \\ FULL_SIMP_TAC std_ss [el_length_def,LEFT_ADD_DISTRIB]
  \\ ONCE_REWRITE_TAC [x64_move_loop_def,x64_move_loop_pre_def]
  \\ `b1 + n2w (8 * heap_length (h1 ++ DataElement l n' (tag,qs)::t)) <>
      b1 + n2w (8 * heap_length h1)` by ALL_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [WORD_EQ_ADD_LCANCEL,NOT_LESS]
    \\ `(8 * heap_length (h1 ++ DataElement l n' (tag,qs)::t)) < 18446744073709551616` by DECIDE_TAC
    \\ Q.UNABBREV_TAC `b3` \\ FULL_SIMP_TAC std_ss [heap_length_APPEND]
    \\ `(8 * heap_length h1) < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def,LEFT_ADD_DISTRIB]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ SEP_R_TAC
  \\ IMP_RES_TAC x64_payload_test
  \\ IMP_RES_TAC x64_payload_not_ptr
  \\ IMP_RES_TAC x64_payload_length
  \\ REVERSE (Cases_on `x1 && 0x2w = 0x0w`) \\ FULL_SIMP_TAC std_ss [] THEN
  TRY
   (FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,blast_lemma2,
      AC WORD_AND_COMM WORD_AND_ASSOC]
    \\ Q.PAT_ABBREV_TAC `dd = DataElement [] n' xx : (bool[63], tag # bool[64] list) heap_element`
    \\ `(h1 ++ dd::t) = (SNOC dd h1 ++ t)` by
          FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_arith_lemma1]
    \\ `8 * heap_length h1 + 8 + 8 * n' = 8 * heap_length (SNOC dd h1)` by ALL_TAC THEN1
     (Q.UNABBREV_TAC `dd` \\ FULL_SIMP_TAC std_ss [heap_length_APPEND,SNOC_APPEND]
      \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def,LEFT_ADD_DISTRIB]
      \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC, AC MULT_COMM MULT_ASSOC])
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_I_TAC "x64_move_loop"
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`limit`,`n3`,`heap3`,`c3`,`n''`,`h2'`,`r`])
    \\ MATCH_MP_TAC IMP_IMP
    \\ REVERSE STRIP_TAC
    THEN1 (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC gc_move_list_ok)
    \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `dd`
      \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def,SNOC_APPEND,
           SUM_APPEND,NOT_LESS] \\ DECIDE_TAC)
    \\ `limit < 2305843009213693952` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `(ys3 = []) /\ (xs3 = [])` by ALL_TAC THEN1
          (FULL_SIMP_TAC std_ss [gc_move_list_def])
    \\ `heap_length (SNOC dd h1) + heap_length t = a3` by ALL_TAC THEN1
     (IMP_RES_TAC gc_move_list_ok
      \\ IMP_RES_TAC gc_move_loop_ok \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC gc_move_list_ok
      \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def]
      \\ Q.UNABBREV_TAC `b3`
      \\ FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND,SUM_APPEND,ADD_ASSOC])
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL,SNOC_APPEND]
    \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,SEP_CLAUSES]
    \\ Q.UNABBREV_TAC `dd` \\ FULL_SIMP_TAC std_ss [x64_el_def]
    \\ `x64_payload [] n' (NumTag b') qs b2 = x64_payload [] n' (NumTag b') qs b1` by
          FULL_SIMP_TAC std_ss [x64_payload_def]
    \\ `x64_payload [] n' (BytesTag n''') qs b2 = x64_payload [] n' (BytesTag n''') qs b1` by
          FULL_SIMP_TAC std_ss [x64_payload_def]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,STAR_ASSOC,SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_def,el_length_def,LEFT_ADD_DISTRIB]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
    \\ Q.PAT_ASSUM `xxx (fun2set yyy)` MP_TAC
    \\ FULL_SIMP_TAC std_ss [gc_move_list_def,word_arith_lemma1]
    \\ NO_TAC)
  \\ Q.MATCH_ASSUM_RENAME_TAC `LENGTH x2 = k` []
  \\ MP_TAC (Q.SPECL [`l`,`[]`,`n`,`h2`,`c`,`limit`,`ys3`,`b3`] x64_move_list_thm)
  \\ FULL_SIMP_TAC std_ss [EVAL ``heap_length []``,SUM,ADD_0]
  \\ Q.ABBREV_TAC `cc = (b1 + n2w (8 * heap_length h1) + 0x8w)`
  \\ STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`cc`,`m`])
  \\ FULL_SIMP_TAC std_ss [x64_heap_def,SEP_CLAUSES]
  \\ `(8 * heap_length (h1 ++ DataElement l k (tag,qs)::t)) = 8 * b3` by ALL_TAC
  THEN1 (Q.UNABBREV_TAC `b3` \\ FULL_SIMP_TAC std_ss [heap_length_APPEND])
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_F_TAC
  \\ Q.PAT_ASSUM `LENGTH x2 = k` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [AC WORD_AND_COMM WORD_AND_ASSOC]
    \\ Q.UNABBREV_TAC `cc`
    \\ FULL_SIMP_TAC std_ss [blast_lemma2,GSYM word_mul_n2w]
    \\ IMP_RES_TAC gc_move_loop_ok \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_list_ok
    \\ POP_ASSUM (MP_TAC o Q.SPEC `b3`)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def] \\ REPEAT STRIP_TAC
    \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_MAP]
  \\ Q.ABBREV_TAC `xx = DataElement ys3 (LENGTH l) (tag,qs) : (bool[63], tag # bool[64] list) heap_element`
  \\ Q.PAT_ASSUM `!x1 x2 x3. bbb` (MP_TAC o Q.SPECL
       [`limit`,`h1 ++ [xx]`,`t ++ xs3`,`n3`,`heap3`,`c3`])
  \\ IMP_RES_TAC gc_move_loop_ok \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC gc_move_list_ok
  \\ FULL_SIMP_TAC std_ss [EVAL ``heap_length []``,SUM]
  \\ `a3 = heap_length (h1 ++ [xx]) + heap_length (t ++ xs3)` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `b3` \\ Q.UNABBREV_TAC `xx`
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_def,el_length_def,SUM]
    \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`r`,`m1`])
  \\ `(8 * b3 + 8 * heap_length xs3 = 8 * heap_length (h1 ++ [xx] ++ (t ++ xs3))) /\
      (b1 + n2w (8 * heap_length (h1 ++ [xx])) = cc + n2w (8 * LENGTH l))` by
   (Q.UNABBREV_TAC `b3` \\ Q.UNABBREV_TAC `xx` \\ Q.UNABBREV_TAC `cc`
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_def,
         el_length_def,SUM,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (STRIP_TAC THEN1
     (Q.UNABBREV_TAC `xx`
      \\ FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_def,el_length_def,SUM]
      \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC] \\ DECIDE_TAC)
    \\ Q.UNABBREV_TAC `xx`
    \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,SEP_CLAUSES,x64_el_def]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_def,el_length_def,SUM]
    \\ FULL_SIMP_TAC std_ss [GSYM heap_length_def]
    \\ `x64_payload ys3 (LENGTH l) tag qs b1 = (x1,MAP (x64_addr b1) ys3,T)` by
     (MATCH_MP_TAC (x64_payload_new |> GEN_ALL)
      \\ Q.LIST_EXISTS_TAC [`l`,`MAP (x64_addr b2) l`,`b2`]
      \\ FULL_SIMP_TAC std_ss [AC WORD_AND_COMM WORD_AND_ASSOC]
      \\ IMP_RES_TAC gc_move_list_LENGTH \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES,STAR_ASSOC]
    \\ Q.UNABBREV_TAC `cc` \\ Q.UNABBREV_TAC `b3`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,AC ADD_COMM ADD_ASSOC,LEFT_ADD_DISTRIB]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,
       AC WORD_AND_COMM WORD_AND_ASSOC,blast_lemma2])
  |> Q.INST [`h1`|->`[]`]
  |> SIMP_RULE std_ss [EVAL ``heap_length []``,SUM,APPEND,WORD_ADD_0];

val x64_move_stack_lemma = x64_move_stack_thm
  |> Q.SPECL [`xs2`,`[]`,`[]`]
  |> SIMP_RULE std_ss [EVAL ``heap_length []``,LENGTH,SUM,APPEND,
       x64_heap_def,SEP_CLAUSES,WORD_ADD_0] |> Q.GEN `xs2`;

val x64_move_loop_lemma = x64_move_loop_thm
  |> SIMP_RULE std_ss [EVAL ``heap_length []``,LENGTH,SUM,APPEND,
       x64_heap_def,SEP_CLAUSES,WORD_ADD_0] |> Q.GEN `h1'`

val one_list_exists_ADD = prove(
  ``one_list_exists b (m + n) =
    one_list_exists b m * one_list_exists (b + n2w (8 * m)) n``,
  SIMP_TAC (std_ss++sep_cond_ss) [one_list_exists_def,SEP_EXISTS_THM,
    SEP_CLAUSES,FUN_EQ_THM,cond_STAR]
  \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `xs ++ xs'` \\ FULL_SIMP_TAC (srw_ss()) [one_list_APPEND])
  \\ Q.EXISTS_TAC `TAKE m xs` \\ Q.EXISTS_TAC `DROP m xs`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `m <= LENGTH xs` by DECIDE_TAC
  \\ IMP_RES_TAC LESS_EQ_APPEND
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.TAKE_LENGTH_APPEND,
       rich_listTheory.DROP_LENGTH_APPEND,one_list_APPEND]);

val x64_el_IMP = prove(
  ``(x64_el b h x y * r) s ==> (one_list_exists b (el_length h) * r) s``,
  Cases_on `h` \\ FULL_SIMP_TAC std_ss [x64_el_def,el_length_def]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,one_list_exists_SUC]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_EXISTS_THM] THEN1 (METIS_TAC [])
  \\ Cases_on `b'` \\ FULL_SIMP_TAC std_ss [x64_el_def]
  \\ `?x1 x2 x3. x64_payload l n q r' y = (x1,x2,x3)` by METIS_TAC [PAIR]
  \\ Cases_on `x3` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [SEP_F_def]
  \\ IMP_RES_TAC x64_payload_length \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `x1`
  \\ FULL_SIMP_TAC std_ss [one_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ Q.EXISTS_TAC `x2` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]);

val x64_heap_IMP = prove(
  ``!heap b r. (x64_heap b heap x y * r) s ==>
               (one_list_exists b (heap_length heap) * r) s``,
  Induct THEN1
   (SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_def,heap_length_def,MAP,SUM,
      one_list_exists_def,LENGTH_NIL,SEP_CLAUSES,one_list_def])
  \\ SIMP_TAC std_ss [x64_heap_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [heap_length_def,MAP,SUM,one_list_exists_ADD]
  \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ IMP_RES_TAC x64_el_IMP \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC]);

val x64_full_gc_thm = store_thm("x64_full_gc_thm",
  ``(full_gc (roots,heap,limit) = (roots2,heap2,a2,T)) /\
    (one_list_exists b1 limit * x64_heap b2 heap b1 b2 * r) (fun2set (m,dm)) /\
    (b2 && 0x7w = 0x0w) /\ (b1 && 0x7w = 0x0w) /\
    limit < 2305843009213693952 /\
    limit < 18446744073709551616 /\
    8 * LENGTH roots < 18446744073709551616 ==>
    ?m1. x64_full_gc_pre (b1,MAP (x64_addr b2) roots ++ 0x1w::stack,dm,m) /\
         (x64_full_gc (b1,MAP (x64_addr b2) roots ++ 0x1w::stack,dm,m) =
            (b1 + n2w (8 * heap_length heap2),
             MAP (x64_addr b1) roots2 ++ 0x1w::stack,dm,m1)) /\
         (x64_heap b1 heap2 b1 b1 *
          one_list_exists (b1 + n2w (8 * heap_length heap2)) (limit - a2) *
          one_list_exists b2 limit * r) (fun2set (m1,dm))``,
  SIMP_TAC std_ss [full_gc_def]
  \\ `?x1 x2 x3 x4 x5 x6. gc_move_list (roots,[],0,limit,heap,T,limit) =
      (x1,x2,x3,x4,x5,x6)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ `?y1 y2 y3 y4 y5. gc_move_loop ([],x2,x3,x4,x5,x6,limit) =
      (y1,y2,y3,y4,y5)` by METIS_TAC [PAIR] \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [x64_full_gc_def,x64_full_gc_pre_def,LET_DEF]
  \\ ASSUME_TAC x64_move_stack_lemma
  \\ SEP_I_TAC "x64_move_stack"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`limit`,`heap`,`T`,`limit`])
  \\ FULL_SIMP_TAC std_ss []
  \\ `(x3 = heap_length x2) /\ x6` by ALL_TAC THEN1
   (IMP_RES_TAC gc_move_loop_ok \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC gc_move_list_ok
    \\ FULL_SIMP_TAC std_ss [heap_length_def,MAP,SUM])
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `r`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC x64_move_loop_lemma
  \\ SEP_I_TAC "x64_move_loop"
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`heap2`,`x4`,`x5`,`T`])
  \\ `a2 = heap_length heap2` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `r`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []
  \\ `(x64_heap b2 y4 b1 b2 * (r *
        (x64_heap b1 heap2 b1 b1 *
         (one_list_exists (b1 + n2w (8 * heap_length heap2))
            (limit - heap_length heap2))))) (fun2set (m1',dm))` by
        FULL_SIMP_TAC (std_ss++star_ss) []
  \\ IMP_RES_TAC x64_heap_IMP
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val _ = export_theory();
