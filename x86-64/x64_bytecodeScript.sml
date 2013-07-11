
open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_bytecode";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;
open prog_x64_extraTheory;

open BytecodeTheory repl_funTheory;

open ml_copying_gcTheory x64_compilerLib;
open set_sepTheory;
open helperLib;
open addressTheory
open x64_copying_gcTheory;
open progTheory;

infix \\ val op \\ = op THEN;

fun gg tm = (proofManagerLib.drop ();
             proofManagerLib.drop ();
             proofManagerLib.set_goal([],tm));

val w2w_ADD_sw2sw_SUB = prove(
  ``!x y. x <+ 0x20000000w /\ y <+ 0x20000000w ==>
          (w2w x + sw2sw (y - x) = (w2w:word32 -> word64) y)``,
  REPEAT GEN_TAC \\ blastLib.BBLAST_TAC);


(* padding *)

val zHEAP_NOP = let
  val th = compose_specs ["xor r15,r15"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals with <| reg15 := 0w |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_NOP2 = let
  val th = compose_specs ["add r15,0"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val code_abbrevs_def = Define `
  code_abbrevs cs =
    bignum_code cs.bignum_ptr UNION
    alloc_code cs.alloc_ptr UNION
    error_code cs.error_ptr`;

(* --- translation from bytecode to x64 --- *)

fun MERGE_CODE th = let
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [LENGTH,ADD1])) th
  val th = RW [APPEND] th
  val _ = not (is_imp (concl th)) orelse fail()
  in MERGE_CODE th end handle HOL_ERR _ => th;

val SPEC_PULL_EXISTS = prove(
  ``(?x. SPEC m p c (q x)) ==> SPEC m p c (SEP_EXISTS x. q x)``,
  REPEAT STRIP_TAC \\ REVERSE (`SEP_IMP (q x) ((SEP_EXISTS x. q x))` by ALL_TAC)
  THEN1 (IMP_RES_TAC SPEC_WEAKEN)
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []);

val SPEC_REMOVE_POST = prove(
  ``SPEC m p c q ==> SPEC m p c (q \/ q2)``,
  `SEP_IMP q (q \/ q2)` by FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]
  \\ METIS_TAC [SPEC_WEAKEN]);

fun SPEC_EX q = HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC q

val SPEC_CODE_ABBREV = prove(
  ``SPEC m p (c INSERT d) q ==> !d2. d SUBSET d2 ==> SPEC m p (c INSERT d2) q``,
  REPEAT STRIP_TAC \\ REVERSE (`(c INSERT d2) = (c INSERT d) UNION d2` by ALL_TAC)
  THEN1 METIS_TAC [SPEC_ADD_CODE]
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION,SUBSET_DEF] \\ METIS_TAC []);

val (_,_,sts,_) = prog_x64Lib.x64_tools

fun lisp_pc_s th = let
  val (_,_,_,q) = dest_spec (concl th)
  val c = MOVE_OUT_CONV ``zPC`` THENC MOVE_OUT_CONV ``zS``
  val d = if can dest_star q then I else (RATOR_CONV o RAND_CONV)
  val c = PRE_CONV c THENC POST_CONV (d c)
  in CONV_RULE c th end

val pattern = ``(p1,xs1) INSERT (p2:word64,xs2:word8 list) INSERT s``
fun sort_swap_conv tm = let
  val m = fst (match_term pattern tm)
  val p1 = subst m (mk_var("p1",``:word64``))
  val p2 = subst m (mk_var("p2",``:word64``))
  fun foo tm = if is_var tm then 0 else tm |> cdr |> cdr |> numSyntax.int_of_term
  val _ = foo p2 < foo p1 orelse fail()
  val (x1,s1) = pred_setSyntax.dest_insert tm
  val (x2,s2) = pred_setSyntax.dest_insert s1
  in ISPECL [x1,x2,s2] INSERT_COMM end

fun SORT_CODE th = CONV_RULE (REDEPTH_CONV sort_swap_conv) th

val INSERT_UNION_INSERT = store_thm("INSERT_UNION_INSERT",
  ``x INSERT (y UNION (z INSERT t)) = x INSERT z INSERT (y UNION t)``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION] \\ METIS_TAC []);

fun fix_code th = th
  |> SIMP_RULE std_ss [INSERT_UNION_INSERT,UNION_EMPTY]
  |> SORT_CODE
  |> MERGE_CODE
  |> MATCH_MP SPEC_CODE_ABBREV |> Q.SPEC `code_abbrevs cs`
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss
       [SUBSET_DEF,NOT_IN_EMPTY,IN_UNION,code_abbrevs_def,DISJ_IMP])) |> RW []

fun get_code th = let
  val (_,_,c,_) = fix_code th |> UNDISCH_ALL |> concl |> dest_spec
  in c |> rator |> rand |> rand end

(* --- a lemma for each bytecode instruction --- *)

val zBC_Pop = zHEAP_POP1 |> fix_code
val zBC_Pops = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_POPS] |> fix_code
val zBC_Load = zHEAP_LOAD |> fix_code
val zBC_Store = zHEAP_STORE |> fix_code
val zBC_Error = zHEAP_TERMINATE_WITH_ERROR |> fix_code
val zBC_Ref = SPEC_COMPOSE_RULE [zHEAP_NEW_REF,zHEAP_NOP] |> fix_code
val zBC_Tick = zHEAP_NOP2 |> fix_code

(*

get_code zBC_Pops

compose_specs ["48E9"]

x64_encodeLib.x64_encode "je -50000"

 x64_spec "48E903000000"

*)

val zBC_Jump = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "48E9"
  val th = th |> RW [GSYM IMM32_def] |> Q.INST [`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS``
  in th end |> fix_code

val zBC_Return = zHEAP_RET |> fix_code

(* translation function *)

val small_offset_def = Define `
  small_offset n x =
    if n < 268435456:num then x else ^(get_code zBC_Error)`;

val x64_def = Define `
  (x64 i (Stack Pop) = ^(get_code zBC_Pop)) /\
  (x64 i (Stack (Pops k)) = small_offset k ^(get_code zBC_Pops)) /\
  (x64 i (Stack (Load k)) = small_offset k ^(get_code zBC_Load)) /\
  (x64 i (Stack (Store k)) = small_offset k ^(get_code zBC_Store)) /\
  (x64 i (Jump (Addr l)) =
     small_offset l (small_offset i
       (let imm32 = n2w (2 * l) - n2w i - 6w in ^(get_code zBC_Jump)))) /\
  (x64 i (Return) = ^(get_code zBC_Return)) /\
  (x64 i (Ref) = ^(get_code zBC_Ref)) /\
  (x64 i (Label l) = []) /\
  (x64 i (Tick) = ^(get_code zBC_Tick)) /\
  (x64 i _ = ^(get_code zBC_Error))`;

val x64_length_def = Define `
  x64_length bc = LENGTH (x64 0 bc)`;

val x64_inst_length_def = Define `
  x64_inst_length bc = (x64_length bc DIV 2) - 1`;

val EVEN_LENGTH_small_offset = prove(
  ``EVEN (LENGTH x) ==> EVEN (LENGTH (small_offset n x))``,
  SRW_TAC [] [small_offset_def]);

val x64_length_EVEN = prove(
  ``!bc. EVEN (x64_length bc)``,
  Cases \\ TRY (Cases_on `b:bc_stack_op`) \\ TRY (Cases_on `l:loc`)
  \\ SIMP_TAC std_ss [x64_length_def,x64_def,LENGTH,EVEN,LET_DEF]
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset)
  \\ FULL_SIMP_TAC std_ss [LENGTH,EVEN,IMM32_def]);

val x64_length_NOT_ZERO = prove(
  ``!bc. ~is_Label bc ==> x64_length bc <> 0``,
  Cases \\ TRY (Cases_on `b:bc_stack_op`) \\ TRY (Cases_on `l:loc`)
  \\ SIMP_TAC std_ss [x64_length_def,x64_def,LENGTH,EVEN,LET_DEF]
  \\ SRW_TAC [] [small_offset_def,is_Label_def]);

val x64_code_def = Define `
  (x64_code i [] = []) /\
  (x64_code i (b::bs) = x64 i b ++ x64_code (i + x64_length b) bs)`;

val x64_code_APPEND = prove(
  ``!xs1 xs2 p.
      x64_code p (xs1 ++ xs2) =
      x64_code p xs1 ++
      x64_code (p + SUM (MAP x64_length xs1)) xs2``,
  Induct \\ SIMP_TAC std_ss [APPEND,x64_code_def,MAP,SUM,WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC,LEFT_ADD_DISTRIB,ADD_ASSOC]);

val LENGTH_x64_code = prove(
  ``!xs p. LENGTH (x64_code p xs) = SUM (MAP x64_length xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [x64_code_def,SUM,MAP,LENGTH,
       LENGTH_APPEND,x64_length_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [x64_def]
  \\ TRY (Cases_on `b`) \\ FULL_SIMP_TAC std_ss [x64_def]
  \\ TRY (Cases_on `l`) \\ FULL_SIMP_TAC std_ss [x64_def,LET_DEF,LENGTH,IMM32_def]
  \\ cheat);

(* --- bytecode simulation --- *)

(* cb = code base, sb = stack base,ev *)

val bc_adjust_def = tDefine "bc_adjust" `
  (bc_adjust (cb,sb,ev) (CodePtr p) = CodePtr ((w2n (cb:word64) DIV 2) + p)) /\
  (bc_adjust (cb,sb,ev) (StackPtr i) = StackPtr ((w2n (sb:word64) DIV 2) + i)) /\
  (bc_adjust (cb,sb,ev) (Number n) = Number n) /\
  (bc_adjust (cb,sb,ev) (RefPtr r) = RefPtr (if ev then 2 * r else 2 * r + 1)) /\
  (bc_adjust (cb,sb,ev) (Block tag data) =
     Block tag (MAP (bc_adjust (cb,sb,ev)) data))`
  (WF_REL_TAC `measure (bc_value_size o SND)`
   \\ Induct_on `data` \\ FULL_SIMP_TAC (srw_ss()) [DISJ_IMP,bc_value_size_def]
   \\ REPEAT STRIP_TAC \\ RES_TAC \\ TRY (POP_ASSUM (MP_TAC o Q.SPEC `tag`))
   \\ DECIDE_TAC) |> CONV_RULE (DEPTH_CONV ETA_CONV);

val ref_adjust_def = Define `
  ref_adjust (cb,sb,ev) (refs1:num |-> bc_value) =
    let adj = (\n. if ev then 2 * n else 2 * n + 1) in
      FUN_FMAP (\n. bc_adjust (cb,sb,ev) (refs1 ' (n DIV 2)))
               (IMAGE adj (FDOM refs1))`;

val zBC_HEAP_def = Define `
  zBC_HEAP bs (x,cs,stack,s,out) (cb,sb,ev,f2) =
    SEP_EXISTS x2 x3.
      let ss = MAP (bc_adjust (cb,sb,ev)) bs.stack ++ (Number 0) :: stack in
        zHEAP (cs,HD ss,x2,x3,x,FUNION (ref_adjust (cb,sb,ev) bs.refs) f2,TL ss,
                  s with <| output := out ++ bs.output |>,NONE)`;

(*
  no tracking for the following:
    cons_names : (num # conN id) list;
*)

fun prepare th = let
  val th = th
    |> SIMP_RULE std_ss [SPEC_MOVE_COND] |> UNDISCH_ALL
    |> CONV_RULE (PRE_CONV (MOVE_OUT_CONV ``zPC``))
    |> CONV_RULE (PRE_CONV (MOVE_OUT_CONV ``zS``))
  val (_,pre,_,_) = th |> concl |> dest_spec
  val tm = ``(zHEAP
     (cs,HD (MAP (bc_adjust (cb,sb,ev)) s1.stack ++ Number 0::stack),x2,
      x3,x,FUNION (ref_adjust (cb,sb,ev) s1.refs) f2,
      TL (MAP (bc_adjust (cb,sb,ev)) s1.stack ++ Number 0::stack),
      s with output := STRCAT out s1.output,NONE) *
   zPC (cb + n2w (2 * s1.pc)) * ~zS)``
  val i = fst (match_term pre tm)
  val th = INST i th
  in th end;

val IMP_small_offset = prove(
  ``(n < 268435456 ==>
     SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (base + n2w (2 * s1.pc)) * ~zS)
     ((base + n2w (2 * s1.pc), xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR (cs,STRCAT out z))) ==>
    SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (base + n2w (2 * s1.pc)) * ~zS)
     ((base + n2w (2 * s1.pc), small_offset n xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR (cs,STRCAT out z))``,
  cheat);

val sw2sw_lemma =
  sw2sw_def |> INST_TYPE [``:'a``|->``:32``,``:'b``|->``:64``]
            |> SIMP_RULE (srw_ss()) [] |> GSYM

val EVEN_LEMMA = prove(
  ``EVEN n ==> (2 * (n DIV 2) = n:num)``,
  SIMP_TAC std_ss [RW1 [MULT_COMM] EVEN_EXISTS]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MULT_DIV]
  \\ SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]);

val zBC_HEAP_THM = prove(
  ``EVEN (w2n cb) ==>
    !s1 s2.
      bc_next s1 s2 ==> (s1.inst_length = x64_inst_length) ==>
      SPEC X64_MODEL
         (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
          zPC (cb + n2w (2 * s1.pc)) * ~zS)
        ((cb + n2w (2 * s1.pc),x64 (2 * s1.pc) (THE (bc_fetch s1)))
         INSERT code_abbrevs cs)
        (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
         zPC (cb + n2w (2 * s2.pc)) * ~zS \/
         zHEAP_ERROR (cs,out ++ s2.output))``,
  STRIP_TAC \\ HO_MATCH_MP_TAC bc_next_ind \\ REPEAT STRIP_TAC
  \\ TRY (Cases_on `b:bc_stack_op`)
  \\ TRY (Cases_on `l:loc`)
  \\ TRY (Q.PAT_ASSUM `bc_stack_op xxx s1.stack ys` MP_TAC)
  \\ ONCE_REWRITE_TAC [bc_stack_op_cases]
  \\ FULL_SIMP_TAC std_ss [bc_inst_distinct,bc_inst_11,
       bc_stack_op_distinct,bc_stack_op_11,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `bc_fetch s1 = SOME xx` MP_TAC
  \\ SIMP_TAC std_ss [x64_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ NTAC 3 (TRY (MATCH_MP_TAC IMP_small_offset \\ REPEAT STRIP_TAC))
  THEN1 (* Pop *)
   (SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Pop) |> SPEC_ALL
                  |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Pops *) cheat
  THEN1 (* Shift *) cheat
  THEN1 (* PushInt *) cheat
  THEN1 (* Cons *) cheat
  THEN1 (* Load *) cheat
  THEN1 (* Store *) cheat
  THEN1 (* LoadRev *) cheat
  THEN1 (* El *) cheat
  THEN1 (* TagEq *) cheat
  THEN1 (* Equal *) cheat
  THEN1 (* Add *) cheat
  THEN1 (* Sub *) cheat
  THEN1 (* Mult *) cheat
  THEN1 (* Div *) cheat
  THEN1 (* Mod *) cheat
  THEN1 (* Less *) cheat
  THEN1 (* Jump Lab *) cheat
  THEN1 (* Jump Addr *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Jump) |> SPEC_ALL
                     |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [bc_find_loc_def,GSYM word_add_n2w]
    \\ SIMP_TAC std_ss [sw2sw_lemma]
    \\ `cb + n2w (2 * s1.pc) +
         (0x6w + sw2sw (n2w (2 * n) - n2w (2 * s1.pc) - 0x6w:word32)) =
        cb + n2w (2 * n)` by ALL_TAC THEN1
     (SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC]
      \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,word_add_n2w,GSYM WORD_SUB_PLUS]
      \\ `(2 * s1.pc + 6) < 4294967296 /\ (2 * n) < 4294967296` by DECIDE_TAC
      \\ `n2w (2 * s1.pc + 6) = (w2w:word32->word64) (n2w (2 * s1.pc + 6))` by
            FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w]
      \\ `n2w (2 * n) = (w2w:word32->word64) (n2w (2 * n))` by
            FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w]
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC w2w_ADD_sw2sw_SUB
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO,w2n_n2w]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC) \\ SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* JumpIf -- Lab *) cheat
  THEN1 (* JumpIf -- Addr *) cheat
  THEN1 (* Call -- Lab *) cheat
  THEN1 (* Call -- Addr *) cheat
  THEN1 (* CallPtr *) cheat
  THEN1 (* JumpPtr *) cheat
  THEN1 (* PushPtr -- Lab *) cheat
  THEN1 (* PushPtr -- Addr *) cheat
  THEN1 (* Return *)
   (MATCH_MP_TAC SPEC_REMOVE_POST
    \\ SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Return) |> SPEC_ALL
                     |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [HD,TL,isCodePtr_def,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ SIMP_TAC std_ss [bc_adjust_def,isCodePtr_def,getCodePtr_def]
    \\ `zPC (n2w (2 * (w2n cb DIV 2 + n))) = zPC (cb + n2w (2 * n))` by ALL_TAC THEN1
     (AP_TERM_TAC \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB]
      \\ IMP_RES_TAC EVEN_LEMMA
      \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,n2w_w2n])
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* PushExn *) cheat
  THEN1 (* PopExn *) cheat
  THEN1 (* Ref *) cheat
  THEN1 (* Deref *) cheat
  THEN1 (* Update *) cheat
  THEN1 (* Tick *) cheat
  THEN1 (* Print *) cheat
  THEN1 (* PrintE *) cheat
  THEN1 (* PrintE *) cheat
  THEN1 (* PrintE *) cheat
  THEN1 (* PrintC *) cheat);

val bc_next_inst_length = prove(
  ``!s1 s2. bc_next s1 s2 ==> (s2.inst_length = s1.inst_length) /\
                              (s2.code = s1.code)``,
  HO_MATCH_MP_TAC bc_next_ind \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [bump_pc_def]
  \\ Cases_on `bc_fetch (s1 with stack := xs)` \\ SRW_TAC [] []);

val SPEC_COMPOSE_LEMMA = prove(
  ``SPEC m q c (q2 \/ r) ==> SPEC m p c (q \/ r) ==> SPEC m p c (q2 \/ r)``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_COMPOSE |> Q.SPECL [`x`,`p`,`c`,`m`,`c`]
                                |> RW [UNION_IDEMPOT] |> GEN_ALL)
  \\ Q.EXISTS_TAC `q \/ r` \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [progTheory.SPEC_PRE_DISJ_INTRO]) |> GEN_ALL;

val NOT_is_Label = prove(
  ``!h. ~is_Label h ==> ?n. x64_length h = (n + 1) * 2``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPEC `h` x64_length_EVEN)
  \\ SIMP_TAC std_ss [RW1[MULT_COMM]EVEN_EXISTS] \\ STRIP_TAC
  \\ IMP_RES_TAC x64_length_NOT_ZERO
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1] \\ Cases_on `m`
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val bc_fetch_SPLIT_LEMMA = prove(
  ``!code p.
      (bc_fetch_aux code x64_inst_length p = SOME x) ==>
      ?xs1 xs2. (code = xs1 ++ [x] ++ xs2) /\
                (SUM (MAP x64_length xs1) = 2 * p)``,
  Induct \\ SIMP_TAC std_ss [bc_fetch_aux_def] \\ STRIP_TAC
  \\ Cases_on `is_Label h` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
   (FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`h::xs1`,`xs2`]
    \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [is_Label_def]
    \\ FULL_SIMP_TAC std_ss [MAP,x64_length_def,APPEND,SUM,x64_def,LENGTH])
  \\ Cases_on `p = 0` \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `[]` \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11,MAP,SUM])
  \\ Cases_on `p < x64_inst_length h + 1` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Q.EXISTS_TAC `h::xs1` \\ Q.EXISTS_TAC `xs2`
  \\ FULL_SIMP_TAC std_ss [APPEND,MAP,SUM,x64_inst_length_def]
  \\ `?n. x64_length h = (n + 1) * 2` by METIS_TAC [NOT_is_Label]
  \\ FULL_SIMP_TAC std_ss [MULT_DIV]
  \\ DECIDE_TAC);

val bc_fetch_SPLIT = prove(
  ``(bc_fetch s1 = SOME x) /\ (x64_inst_length = s1.inst_length) ==>
    ?xs1 xs2. (s1.code = xs1 ++ [x] ++ xs2) /\
              (SUM (MAP x64_length xs1) = 2 * s1.pc)``,
  SIMP_TAC std_ss [bc_fetch_def] \\ METIS_TAC [bc_fetch_SPLIT_LEMMA]);

val bc_next_IMP_fetch = prove(
  ``!s1 s2. bc_next s1 s2 ==> ?x. bc_fetch s1 = SOME x``,
  HO_MATCH_MP_TAC bc_next_ind \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val zBC_HEAP_RTC = prove(
  ``EVEN (w2n cb) ==>
    !s1 s2.
      bc_next^* s1 s2 ==> (s1.inst_length = x64_inst_length) ==>
      SPEC X64_MODEL
        (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
         zPC (cb + n2w (2 * s1.pc)) * ~zS)
        ((cb, x64_code 0 s1.code) INSERT code_abbrevs cs)
        (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
         zPC (cb + n2w (2 * s2.pc)) * ~zS \/
         zHEAP_ERROR (cs,out ++ s2.output))``,
  STRIP_TAC
  \\ HO_MATCH_MP_TAC RTC_INDUCT \\ REPEAT STRIP_TAC
  THEN1 (MATCH_MP_TAC SPEC_REMOVE_POST \\ SIMP_TAC std_ss [SPEC_REFL])
  \\ IMP_RES_TAC bc_next_inst_length
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.MATCH_ASSUM_RENAME_TAC `bc_next s1 s3` []
  \\ MP_TAC (zBC_HEAP_THM |> UNDISCH |> Q.SPECL [`s1`,`s3`])
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `SPEC mm pp cc qq` (MP_TAC o MATCH_MP SPEC_COMPOSE_LEMMA)
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!b.xx` MATCH_MP_TAC
  \\ IMP_RES_TAC bc_next_IMP_fetch
  \\ IMP_RES_TAC bc_fetch_SPLIT
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [x64_code_APPEND]
  \\ REPEAT (MATCH_MP_TAC (prog_x64Theory.SPEC_X64_MERGE_CODE |> Q.GEN `a2`
       |> SIMP_RULE std_ss []))
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,x64_code_def,APPEND_NIL,LENGTH_x64_code]
  \\ Q.PAT_ASSUM `SPEC xx yy tt rr` MP_TAC
  \\ `STRCAT out s2.output = STRCAT out s3.output` by cheat
  \\ FULL_SIMP_TAC std_ss []
  \\ (SPEC_SUBSET_CODE |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
        |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO] |> MATCH_MP_TAC)
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ SIMP_TAC std_ss [SUBSET_DEF,IN_INSERT]);


val _ = export_theory();
