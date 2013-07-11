
open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_bignum";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;
open prog_x64_extraTheory;

open BytecodeTheory;

open x64_compilerLib set_sepTheory helperLib addressTheory;
open ml_copying_gcTheory x64_copying_gcTheory progTheory;

open x64_heapTheory x64_allocTheory;

infix \\ val op \\ = op THEN;

fun gg tm = (proofManagerLib.drop ();
             proofManagerLib.drop ();
             proofManagerLib.set_goal([],tm));

val w2w_ADD_sw2sw_SUB = prove(
  ``!x y. x <+ 0x20000000w /\ y <+ 0x20000000w ==>
          (w2w x + sw2sw (y - x) = (w2w:word32 -> word64) y)``,
  REPEAT GEN_TAC \\ blastLib.BBLAST_TAC);

(* Number size *)

val (x64_num_size1_res, x64_num_size1_def, x64_num_size1_pre_def) = x64_compile `
  x64_num_size1 (r0:word64,dm:word64 set,m:word64->word64) =
    if r0 && 1w = 0w then
      if r0 = 0w then let r14 = r0 in (r0,r14,dm,m)
                 else let r14 = 1w in (r0,r14,dm,m)
    else
      let r15 = m (r0 + 1w) in
      let r14 = r15 >>> 16 in
        (r0,r14:word64,dm,m)`

val (x64_num_size2_res, x64_num_size2_def, x64_num_size2_pre_def) = x64_compile `
  x64_num_size2 (r1:word64,r14,dm:word64 set,m:word64->word64) =
    if r1 && 1w = 0w then
      if r1 = 0w then (r1,r14,dm,m)
                 else let r14 = r14 + 1w in (r1,r14,dm,m)
    else
      let r15 = m (r1 + 1w) in
      let r15 = r15 >>> 16 in
      let r14 = r14 + r15 in
        (r1,r14:word64,dm,m)`

val (x64_num_size_res, x64_num_size_def, x64_num_size_pre_def) = x64_compile `
  x64_num_size (r0,r1,dm,m) =
    let (r0,r14,dm,m) = x64_num_size1 (r0,dm,m) in
    let (r1,r14,dm,m) = x64_num_size2 (r1,r14,dm,m) in
    let r14 = r14 + 2w in
    let r14 = r14 << 3 in
      (r0,r1,r14,dm,m)`

val num_size_def = Define `
  (num_size (Number i) = LENGTH ((mw (Num (ABS i))):word64 list)) /\
  (num_size _ = 0)`;

val x64_num_size1_EXPAND = prove(
  ``(x64_num_size1 (r0,dm,m) = (r0,FST (SND (x64_num_size1 (r0,dm,m))),dm,m))``,
  SIMP_TAC std_ss [x64_num_size1_def] \\ SRW_TAC [] []
  \\ UNABBREV_ALL_TAC \\ FULL_SIMP_TAC std_ss []);

val x64_num_size2_EXPAND = prove(
  ``(x64_num_size2 (r0,r14,dm,m) =
      (r0,r14 + FST (SND (x64_num_size1 (r0,dm,m))),dm,m))``,
  SIMP_TAC std_ss [x64_num_size1_def,x64_num_size2_def]
  \\ SRW_TAC [] [] \\ UNABBREV_ALL_TAC \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]);

val zHEAP_NUM_SIZE = let
  val th = x64_num_size_res
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals).
                vals.reg14 = n2w (8 * (num_size x1 + num_size x2 + 2)))``
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [x64_num_size_def]
    \\ ONCE_REWRITE_TAC [x64_num_size1_EXPAND]
    \\ ONCE_REWRITE_TAC [x64_num_size2_EXPAND]
    \\ SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM,zHEAP_def]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    THEN1 cheat
    \\ Q.EXISTS_TAC `vals with <|
         reg14 := (FST (SND (x64_num_size1 (x64_addr vs.current_heap
                     r1,vals.memory_domain,vals.memory))) +
                   FST (SND (x64_num_size1 (x64_addr vs.current_heap
                     r2,vals.memory_domain,vals.memory))) + 0x2w) << 3 ;
         reg15 := x |>`
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def]
      \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,APPEND,GSYM APPEND_ASSOC]
      \\ cheat)
    \\ POP_ASSUM (K ALL_TAC)
    \\ SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [APPEND,GSYM APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
    \\ `!x1 r1.
          bc_value_inv x1 (r1,f,heap) /\ isNumber x1 ==>
          (FST (SND (x64_num_size1 (x64_addr vs.current_heap r1,
                      vals.memory_domain,vals.memory))) =
           n2w (num_size x1))` by ALL_TAC THEN1
     (Cases \\ STRIP_TAC \\ SIMP_TAC std_ss [isNumber_def,bc_value_inv_def]
      \\ Cases_on `small_int i` \\ FULL_SIMP_TAC std_ss [x64_addr_def,num_size_def]
      \\ SIMP_TAC std_ss [x64_num_size1_def,LET_DEF]
      THEN1
       (REPEAT STRIP_TAC
        \\ `w2w (0x2w * (n2w (Num i)):62 word) << 1 && 0x1w = 0x0w:word64` by
              blastLib.BBLAST_TAC \\ FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC std_ss [small_int_def]
        \\ `(w2w (0x2w * n2w (Num i):62 word) << 1 = 0x0w:word64) = (i = 0)` by
          (FULL_SIMP_TAC (srw_ss()) [w2w_def,word_add_n2w,word_mul_n2w,
            WORD_MUL_LSL,w2n_n2w] \\ cheat)
        \\ FULL_SIMP_TAC std_ss []
        \\ Cases_on `i = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
         (`Num (ABS 0) = 0:num` by intLib.COOPER_TAC
          \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
        \\ ONCE_REWRITE_TAC [mw_def]
        \\ `Num (ABS (i:int)) <> 0:num` by intLib.COOPER_TAC
        \\ ASM_SIMP_TAC std_ss []
        \\ `Num (ABS i) < dimword (:64)` by ALL_TAC THEN1
             (FULL_SIMP_TAC (srw_ss()) [] \\ intLib.COOPER_TAC)
        \\ IMP_RES_TAC LESS_DIV_EQ_ZERO \\ ASM_SIMP_TAC std_ss []
        \\ SIMP_TAC std_ss [EVAL ``mw 0``,LENGTH])
      \\ cheat)
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,
         LEFT_ADD_DISTRIB])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;

(*
  val th = SPEC_COMPOSE_RULE [zHEAP_NUM_SIZE,zHEAP_ALLOC]
*)

(* Use of multiword library *)

val (bignum_th,code_abbrev_def) = let
  val (_,_,code,_) = x64_multiwordTheory.x64_iop_res |> concl |> dest_spec
  val temp_code_def = Define `temp_code (p:word64) = ^code`;
  val th = x64_multiwordTheory.x64_iop_res |> RW [GSYM temp_code_def]
  val th = th |> Q.INST [`p:word64 reln -> bool`|->`frame`]
  in (th,temp_code_def) end

val thA = let
  val tm = ``x64_iop (r0,r1,r3,xs,ys,zs,xa,ya,ss) = (r10i,xsi,ysi,zsi,xai,yai,ssi)``
  val th = DISCH tm bignum_th |> SIMP_RULE std_ss [LET_DEF] |> UNDISCH
  in th end


(* bignum header writer *)

val zBIGNUMS_HEADER_def = Define `
  zBIGNUMS_HEADER (xai,xsi,yai,ysi,z,za,zsi,frame) =
    zBIGNUMS (xai,xsi,yai,ysi,za,zsi,frame * one (za - 8w, z))`;

val thB = thA |> Q.INST [`frame`|->`frame * one (za - 8w, z)`]
              |> RW [GSYM zBIGNUMS_HEADER_def]

val (x64_big_header_res, x64_big_header_def, x64_big_header_pre_def) = x64_compile `
  x64_big_header (r10:word64,r15:word64,dm:word64 set,m:word64->word64) =
    let r0 = r15 - 9w in
    let r2 = r10 >>> 1 in
    let r2 = r10 << 16 in
    let r3 = m (r0 + 1w) in
    let r2 = r2 + 2w in
    let r1 = r10 && 1w in
    let r2 = r2 + r1 in
    let m = (r0 + 1w =+ r2) m in
      (r0,r3,dm,m)`

val zBIGNUM_HEADER_WRITE = let
  val th = x64_big_header_res |> Q.INST [`r15`|->`za`]
  val th = MATCH_MP SPEC_FRAME th |> Q.SPEC `zR 0xDw xa * zR 0xEw ya * cond
             (bignum_mem (frame * one (za - 8w, z)) dm m xa xs ya ys za zs /\
              (r10 = x64_header (q,qs)))`
  val pc = get_pc th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``(~zS * ^pc * zR 0x0w (za - 9w) * zR 0x3w z * ~zR 0x2w * ~zR 0x1w *
       zR 0xAw (x64_header (q,qs)) *
       zBIGNUMS_HEADER (xa,xs,ya,ys,n2w (LENGTH qs) << 16 + 2w+b2w q,za,zs,frame))``
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * ~zR 0x0w * ~zR 0x1w * ~zR 0x2w * ~zR 0x3w * zR 0xAw r10 *
       zBIGNUMS_HEADER (xa,xs,ya,ys,z,za,zs,frame) *
       cond (r10 = x64_header (q,qs)))``
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  in th end

val thC = SPEC_COMPOSE_RULE [thB,zBIGNUM_HEADER_WRITE]

(* bignum collapse small int *)

val (x64_big_small_res, x64_big_small_def, x64_big_small_pre_def) = x64_compile `
  x64_big_small (r0,r10:word64,r15,dm:word64 set,m:word64->word64) =
    if r10 = 0w then (* zero *)
      (r0,r15,dm,m)
    else if r10 = 2w then
      let r1 = m r15 in
      let r2 = 1w in
      let r2 = r2 << 62 in
        if r1 <+ r2 then (* can be repr as small_int *)
          let r0 = r1 << 2 in
            (r0,r15,dm,m)
        else (r0,r15,dm,m)
    else (r0,r15,dm,m)`

val zBIGNUM_BIG_SMALL = let
  val th = x64_big_small_res |> Q.INST [`r15`|->`za`,`r10`|->`x64_header (q,qs)`]
  val th = MATCH_MP SPEC_FRAME th |> Q.SPEC `zR 0xDw xa * zR 0xEw ya * cond
             (bignum_mem (frame * one (za - 8w, z)) dm m xa xs ya ys za zs /\
              (isPREFIX qs zs) /\ LENGTH qs < 2**32)`
  val pc = get_pc th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``(~zS * ^pc * zR 0x0w (if small_int (mw2i (q,qs))
                            then n2w (4 * (mw2n qs)) else za - 9w) *
       ~zR 0x1w * ~zR 0x2w * zR 0xAw (x64_header (q,qs)) *
       zBIGNUMS_HEADER (xa,xs,ya,ys,z,za,zs,frame))``
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zR 0x0w (za - 9w) * ~zR 0x1w * ~zR 0x2w *
       zR 0xAw (x64_header (q,qs)) *
       zBIGNUMS_HEADER (xa,xs,ya,ys,z,za,zs,frame) * cond
         ((isPREFIX qs zs) /\ LENGTH qs < dimword (:63)))``
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  in th end;

val thD = SPEC_COMPOSE_RULE [thC,zBIGNUM_BIG_SMALL] |> RW [STAR_ASSOC];

(* print string from stack *)

val blast_lemma = prove(
  ``r7 <+ 256w ==> (w2w ((w2w r7):word8) = r7:word64)``,
  blastLib.BBLAST_TAC) |> UNDISCH;

val lemma = prove(
  ``(r15 = po) ==>
    (zIO (pi,input,r15,output) = zIO (pi,input,po,output))``,
  SIMP_TAC std_ss []) |> UNDISCH;

val put_char_thm =
  SPEC_COMPOSE_RULE [x64_call_r15, x64_putchar_thm]
  |> Q.INST [`c`|->`w2w (r7:word64)`,`rip`|->`p`] |> RW [blast_lemma]
  |> RW1 [lemma] |> DISCH_ALL |> RW [AND_IMP_INTRO]
  |> RW [GSYM SPEC_MOVE_COND]

val th = let
  val q = put_char_thm |> concl |> rand
  val tm = ``output ++ [(w2w:word64->word8) r7]``
  val new_q = subst [tm|->``output:word8 list``] q
  val (th,goal) = SPEC_WEAKEN_RULE put_char_thm ``let output = ^tm in ^new_q``
  val lemma = prove(goal,SIMP_TAC std_ss [LET_DEF,SEP_IMP_REFL])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  val _ = decompilerLib.add_decompiled("print_r7",th,3,SOME 3);
  in th end

val th = let
  val th = x64_pop_r7
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``let (r7,ss) = (HD ss,TL ss) in
        (zPC (rip + 0x2w) * zR 0x7w r7 * zSTACK (base,ss))``
  val lemma = prove(goal,SIMP_TAC std_ss [LET_DEF,SEP_IMP_REFL])
  val th = MP th lemma
  val _ = decompilerLib.add_decompiled("pop_r7",th,2,SOME 2);
  in th end

fun x64_decompile name asm =
  decompilerLib.decompile_strings prog_x64Lib.x64_tools_64 name
    (x64_codegenLib.assemble asm);

val (res,x64_pop_def) = x64_decompile "x64_pop" `
  L1: insert pop_r7 `

val (res,x64_print_def) = x64_decompile "x64_print" `
  L1: insert print_r7 `

val (x64_print_stack_res,x64_print_stack_def) = x64_decompile "x64_print_stack" `
  L1: insert x64_pop
      test r7,r7
      je L2
      insert x64_print
      jmp L1
  L2: `

val x64_print_stack_thm = prove(
  ``!xs output.
      EVERY (\x. ORD x <> 0) xs /\ (r15 = po) ==>
      x64_print_stack_pre (r15,output,po,MAP (n2w o ORD) xs ++ 0w::ss) /\
      (x64_print_stack (r15,output,po,MAP (n2w o ORD) xs ++ 0w::ss) =
         (r15,output ++ MAP (n2w o ORD) xs,po,ss))``,
  Induct \\ ONCE_REWRITE_TAC [x64_print_stack_def]
  \\ SIMP_TAC std_ss [LET_DEF,x64_pop_def,MAP,APPEND,HD,TL,APPEND_NIL]
  \\ SIMP_TAC std_ss [x64_print_def,LET_DEF,EVERY_DEF]
  \\ SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ REPEAT STRIP_TAC
  \\ `ORD h < 256` by SIMP_TAC std_ss [ORD_BOUND]
  \\ `ORD h < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [w2w_def,n2w_w2n,WORD_LO]);

val zBIGNUMS_ALT_def = Define `
  zBIGNUMS_ALT (xa,xs,ya,ys,za,zs,p) =
    SEP_EXISTS dm m.
       zMEMORY64 dm m * cond (bignum_mem p dm m xa xs ya ys za zs)`;

val zBIGNUMS_ALT_THM = prove(
  ``zBIGNUMS (xa,xs,ya,ys,za,zs,p) =
    zBIGNUMS_ALT (xa,xs,ya,ys,za,zs,p) * zR 0xDw xa * zR 0xEw ya * zR 0xFw za``,
  SIMP_TAC std_ss [zBIGNUMS_ALT_def,x64_multiwordTheory.zBIGNUMS_def,SEP_CLAUSES]
  \\ SIMP_TAC (std_ss++sep_cond_ss) []);

val res1 = thD |> CONV_RULE (RAND_CONV
  (REWRITE_CONV [zBIGNUMS_HEADER_def,zBIGNUMS_ALT_THM]))
  |> SIMP_RULE std_ss [SEP_CLAUSES,STAR_ASSOC]

val res2 = compose_specs ["mov r15,r3"]

val res3 = x64_print_stack_res |> SIMP_RULE std_ss [LET_DEF]
           |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)

val thE = SPEC_COMPOSE_RULE [res1,res2,res3] |> RW [STAR_ASSOC]

val thF = SPEC_COMPOSE_RULE [thE,x64_pop_r1,x64_pop_r2,x64_pop_r3,
    x64_pop_r6,x64_pop_r7,x64_pop_r8,x64_pop_r9,x64_pop_r10,
    x64_pop_r11,x64_pop_r12,x64_pop_r13,x64_pop_r14,x64_pop_r15]

(* convert small to big *)

val (res, x64_bignum_mk_def, x64_bignum_mk_pre_def) = x64_compile `
  x64_bignum_mk (r2:word64,r15:word64,dm:word64 set,m:word64->word64) =
    if r2 && 1w = 0w then (* small int *)
      let r2 = r2 >>> 2 in
      let m = (r15 =+ r2) m in
        if r2 = 0w then (r2,r15,dm,m) else
          let r2 = 2w in (r2,r15,dm,m)
    else (* bignum *)
      let r15 = r2 + 9w in
      let r2 = m (r2 + 1w) in
        if r2 && 1w = 0w then
          let r2 = r2 >>> 15 in
            (r2,r15,dm,m)
        else
          let r2 = r2 >>> 15 in
          let r2 = r2 + 1w in
            (r2,r15,dm,m)`

val (x64_bignum_setup_res, x64_bignum_setup_def, x64_bignum_setup_pre_def) =
  x64_compile `
  x64_bignum_setup (r0,r1,r3:word64,r6:word64,r7:word64,r9:word64,dm,m,ss) =
    let r3 = r3 >> 2 in
    let r2 = r0 in
    let r15 = r7 - 16w in
    let (r2,r15,dm,m) = x64_bignum_mk (r2,r15,dm,m) in
    let r0 = r2 in
    let r13 = r15 in
    let r2 = r1 in
    let r15 = r7 - 8w in
    let (r2,r15,dm,m) = x64_bignum_mk (r2,r15,dm,m) in
    let r1 = r2 in
    let r2 = m (r9 + 24w) in
    let m = (r6 =+ r2) m in
    let r2 = 0w:word64 in
    let r14 = r15 in
    let r15 = r6 + 8w in
    let ss = r2 :: ss in
      (r0,r1,r3,r13,r14,r15,dm,m,ss)`

val res1 = x64_bignum_setup_res |> SIMP_RULE std_ss [LET_DEF]
           |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)

val res2 = thF |> SIMP_RULE (std_ss++sep_cond_ss) [zBIGNUMS_HEADER_def,
                    x64_multiwordTheory.zBIGNUMS_def,SEP_CLAUSES,
                    GSYM SPEC_PRE_EXISTS] |> SPEC_ALL

val thG = SPEC_COMPOSE_RULE [res1,res2]

val thH = SPEC_COMPOSE_RULE [x64_pop_r1, x64_pop_r2, x64_pop_r3,
                             x64_pop_r6, x64_pop_r7, x64_pop_r8,
                             x64_pop_r9, x64_pop_r10, x64_pop_r11,
                             x64_pop_r12, x64_pop_r13, x64_pop_r14,
                             x64_pop_r15, thG]

val thX = let
  val lemma = prove(
    ``(b ==> SPEC m p c q) ==> SPEC m (p * cond b) c (q * cond b)``,
    Cases_on `b` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]);
  val th = MATCH_MP lemma (thH |> DISCH_ALL)
  in th end

val n2iop_def = Define `
  n2iop (n:int) = if n = 0 then Add else
                  if n = 1 then Sub else
                  if n = 2 then Lt else
                  if n = 3 then Eq else
                  if n = 4 then Mul else
                  if n = 5 then Div else
                  if n = 6 then Mod else
                  if n = 7 then Dec else ARB`;

val zHEAP_PERFORM_BIGNUM = let
  val th = thX |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
               |> UNDISCH_ALL |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val inv = ``SOME (\(sp,vals:x64_vals). num_size x1 + num_size x2 + 2 <= sp:num)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++sep_cond_ss) [AC CONJ_COMM CONJ_ASSOC]
                         \\ SIMP_TAC std_ss [STAR_ASSOC] \\ cheat)
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
     Number (int_op (n2iop (getNumber x3)) (getNumber x1) (getNumber x2)),
     x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  in th end;

val zHEAP_CALL_BIGNUM = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r13, [r9+56]")
  val th = SPEC_COMPOSE_RULE [th,x64_call_r13,x64_pop_r13]
           |> SIMP_RULE std_ss [NOT_CONS_NIL,HD,TL,SEP_CLAUSES]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 56w) = cs.bignum_ptr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals).
                (p + 0x7w = vals.reg13))``
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ STRIP_TAC \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
      \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg13 := p + 7w |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_BIGNUM_OP = let
  val th1 = zHEAP_CALL_BIGNUM
  val th2 = SPEC_COMPOSE_RULE [zHEAP_NUM_SIZE,zHEAP_ALLOC,zHEAP_PERFORM_BIGNUM]
            |> RW [SPEC_MOVE_COND] |> UNDISCH_ALL
  val (th2,goal) = SPEC_STRENGTHEN_RULE th2 ``zHEAP
        (cs,x1,x2,x3,x4,refs,stack,s,
         SOME (\(sp,vals). ret = vals.reg13)) * ~zS * zPC p``
  val lemma = prove(goal,cheat)
  val th2 = MP th2 lemma
  val lemma = prove(``num_size x1 + num_size x2 + 2 < 4294967296``,cheat)
  val th = SPEC_COMPOSE_RULE [th1,th2]
           |> DISCH_ALL |> RW [AND_IMP_INTRO,lemma]
           |> RW [GSYM SPEC_MOVE_COND,fetch "-" "temp_code_def"]
  val th3 = zHEAP_JMP_r13
  val (th3,goal) = SPEC_WEAKEN_RULE th3 ``(zHEAP
        (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC ret)``
  val lemma = prove(goal,cheat)
  val th3 = MP th3 lemma |> Q.INST [`P`|->`\x.T`] |> SIMP_RULE std_ss []
  val (th,goal) = SPEC_WEAKEN_RULE th ``
    zHEAP
        (cs,
         Number
           (int_op (n2iop (getNumber x3)) (getNumber x1)
              (getNumber x2)),x2,x3,x4,refs,stack,s,
         SOME (\(sp,vals). vals.reg13 = p + 7w)) * ~zS *
      zPC (cs.bignum_ptr + 0xE79w) \/ zHEAP_ERROR (cs,s.output)``
  val lemma = prove(goal,cheat)
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [th,th3]
  (* package up code *)
  val th = th |> SIMP_RULE std_ss [word_arith_lemma1]
  val (_,_,c,_) = dest_spec (concl th)
  val tms = find_terms (can (match_term ``$INSERT (cs.bignum_ptr,xx)``)) c @
            find_terms (can (match_term ``$INSERT (cs.bignum_ptr+n2w n,xx)``)) c
  val i = ``I:(word64 # word8 list -> bool) -> word64 # word8 list -> bool``
  val c2 = subst (map (fn tm => tm |-> i) tms) c
           |> PURE_REWRITE_CONV [I_THM,UNION_EMPTY] |> concl |> rand
  val xs = list_dest pred_setSyntax.dest_insert c2
  val s = last xs
  val call = butlast xs
  val c1 = map rand tms
  val bignum = pred_setSyntax.mk_set c1 |> subst [``cs.bignum_ptr``|->``p:word64``]
  val bignum_code_def = Define `bignum_code (p:word64) = ^bignum`
  val call_set = pred_setSyntax.mk_set call
  val code = pred_setSyntax.mk_union(call_set,
               pred_setSyntax.mk_union(s,``bignum_code cs.bignum_ptr``))
  val th = MATCH_MP SPEC_SUBSET_CODE th |> SPEC code
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    REWRITE_TAC [bignum_code_def]
    \\ EVERY (map (fn tm => SPEC_TAC (tm,genvar(type_of tm)) THEN STRIP_TAC) c1)
    \\ ASM_REWRITE_TAC [SUBSET_DEF,IN_UNION,IN_INSERT,NOT_IN_EMPTY]
    \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [])
  val th = MP th lemma
  in th end

fun get_INT_OP n = let
  val th = zHEAP_Num3 |> Q.INST [`k`|->`^n`]
           |> SIMP_RULE (srw_ss()) [w2w_def,w2n_n2w,SEP_CLAUSES]
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH3,th,zHEAP_BIGNUM_OP,zHEAP_POP3]
  val th = th |> SIMP_RULE (srw_ss()) [NOT_CONS_NIL,SEP_CLAUSES,
             getNumber_def,n2iop_def,multiwordTheory.int_op_def,HD,TL]
  in th end;

val zHEAP_Add = get_INT_OP ``0:num``;
val zHEAP_Sub = get_INT_OP ``1:num``;
val zHEAP_Lt = get_INT_OP ``2:num``;
val zHEAP_Eq = get_INT_OP ``3:num``;
val zHEAP_Mul = get_INT_OP ``4:num``;
val zHEAP_Div = get_INT_OP ``5:num``;
val zHEAP_Mod = get_INT_OP ``6:num``;
val zHEAP_Dec = get_INT_OP ``7:num``;


val _ = export_theory();
