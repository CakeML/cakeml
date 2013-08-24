
open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_heap";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;
open prog_x64_extraTheory prog_x64Theory;

open BytecodeTheory (* repl_funTheory *);

open ml_copying_gcTheory ml_heapTheory x64_compilerLib;
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

(* define zHEAP *)

val _ = (Datatype.big_record_size := 40);

val _ = Hol_datatype ` (* called cs *)
  zheap_consts = <| heap_limit : num ;
                    heap_part1 : word64 ;
                    heap_part2 : word64 ;
                    ret_address : word64 ;         (* once code completes ret here *)
                    rest_of_stack : word64 list ;  (* to be preserved throughout *)
                    getchar_ptr : word64 ;
                    putchar_ptr : word64 ;
                    error_ptr : word64 ;
                    alloc_ptr : word64 ;
                    bignum_ptr : word64 ;
                    equal_ptr : word64 ;
                    print_ptr : word64 ;
                    code_heap_ptr : word64 ;
                    code_heap_length : num ;
                    stack_trunk : word64 |>`;

val _ = Hol_datatype ` (* called vs *)
  zheap_vars = <| current_heap : word64 ;
                  other_heap : word64 ;
                  base_ptr : word64 ;
                  code_ptr : word64 |>`;

val _ = Hol_datatype ` (* called s *)
  zheap_state = <| input : string ;
                   output : string ;
                   handler : num ;
                   base_offset : num ;
                   code_mode : bool option ;
                   code : word8 list |>`;

val _ = Hol_datatype ` (* called vals *)
  x64_vals = <| reg0 : word64 ;
                reg1 : word64 ;
                reg2 : word64 ;
                reg3 : word64 ;
                reg5 : word64 ;
                reg6 : word64 ;
                reg7 : word64 ;
                reg8 : word64 ;
                reg9 : word64 ;
                reg10 : word64 ;
                reg11 : word64 ;
                reg12 : word64 ;
                reg13 : word64 ;
                reg14 : word64 ;
                reg15 : word64 ;
                memory : word64 -> word64 ;
                memory_domain : word64 set ;
                stack : word64 list ;
                stack_bottom : word64 ;
                code_option : bool option ;
                code_list : word8 list ;
                input_stream : word8 list ;
                output_stream : word8 list |>`;

val heap_vars_ok_def = Define `
  heap_vars_ok vs =
    (vs.current_heap && 0x7w = 0x0w) /\
    (vs.other_heap && 0x7w = 0x0w) /\
    (vs.base_ptr && 0x7w = 0x0w)`;

val x64_store_def = Define `
  x64_store cs vs =
    one_list vs.base_ptr
      [vs.current_heap;        (* pointer to currently used heap half *)
       vs.other_heap;          (* pointer to the other heap half *)
       n2w (cs.heap_limit);    (* size of each heap half *)
       cs.putchar_ptr;         (* pointer to C's putchar method *)
       cs.getchar_ptr;         (* pointer to C's getchar method *)
       cs.error_ptr;           (* pointer to abort code which writes error message *)
       cs.alloc_ptr;           (* pointer to heap alloc routine *)
       cs.bignum_ptr;          (* pointer to entry point for bignum library *)
       cs.equal_ptr;           (* pointer to routine for rec equality check *)
       cs.print_ptr;           (* pointer to routine for rec printing of bc_value *)
       vs.code_ptr;            (* pointer to next free instruction slot *)
       n2w cs.code_heap_length (* size of code heap *)
      ]`;

val not_0w_def = Define `not_0w = ~0w`;

val stack_inv_def = Define `
  stack_inv (r5:word64) r11 trunk bottom base_offset handler
            (rest_of_stack:word64 list) =
    (r5 = trunk - n2w (8 * base_offset)) /\
    (r11 = trunk - n2w (8 * handler)) /\
    (bottom - n2w (8 * LENGTH rest_of_stack) - 16w = trunk) /\
    (trunk && 3w = 0w)`;

val code_heap_inv_def = Define `
  code_heap_inv cs_code_heap_length (cs_code_heap_ptr:word64)
                (vals_code_option:bool option) (vals_code_list:word8 list)
                s_code_mode s_code
                vs_code_ptr =
    cs_code_heap_length < (2**64):num /\
    (vals_code_option = s_code_mode) /\
    (vals_code_list = s_code) /\
    (cs_code_heap_ptr + n2w (LENGTH s_code) = vs_code_ptr)`;

val heap_inv_def = Define `
  heap_inv (cs,x1,x2,x3,x4,refs,stack,s:zheap_state,space) (vals:x64_vals) =
    ?vs r1 r2 r3 r4 roots heap a sp.
      abs_ml_inv ([x1;x2;x3;x4] ++ stack) refs
                 ([r1;r2;r3;r4] ++ roots,heap,a,sp) cs.heap_limit /\
      (space <> NONE ==> THE space (sp,vals)) /\
      (vals.reg0 = x64_addr vs.current_heap r1) /\
      (vals.reg1 = x64_addr vs.current_heap r2) /\
      (vals.reg2 = x64_addr vs.current_heap r3) /\
      (vals.reg3 = x64_addr vs.current_heap r4) /\
      (vals.reg6 = vs.current_heap + n2w (8 * a) - 1w) /\
      (vals.reg7 = vs.current_heap + n2w (8 * (a + sp)) - 1w) /\
      (vals.reg9 = vs.base_ptr) /\
      (vals.reg10 = HD (MAP (n2w o ORD) s.input ++ [not_0w])) /\
      stack_inv vals.reg5 vals.reg11 cs.stack_trunk
        vals.stack_bottom s.base_offset s.handler
            cs.rest_of_stack /\
      code_heap_inv cs.code_heap_length cs.code_heap_ptr
                vals.code_option vals.code_list
                s.code_mode s.code
                vs.code_ptr /\
      cs.heap_limit < 281474976710656 /\ (* 2**(64-16) *)
      (x64_heap vs.current_heap heap vs.current_heap vs.current_heap *
       one_list_exists vs.other_heap cs.heap_limit *
       x64_store cs vs) (fun2set (vals.memory,vals.memory_domain)) /\
      (vals.stack = MAP (x64_addr vs.current_heap) roots ++
                    0x1w::cs.ret_address::cs.rest_of_stack) /\
      (vals.input_stream = MAP (n2w o ORD) (DROP 1 s.input)) /\
      (vals.output_stream = MAP (n2w o ORD) s.output) /\
      heap_vars_ok vs`

val zOPTION_CODE_HEAP_def = Define `
  (zOPTION_CODE_HEAP NONE len a xs = emp) /\
  (zOPTION_CODE_HEAP (SOME safe) len a xs = zCODE_HEAP safe a xs len)`;

val zVALS_def = Define `
  zVALS cs (vals:x64_vals) =
    zR 0w vals.reg0 *
    zR 1w vals.reg1 *
    zR 2w vals.reg2 *
    zR 3w vals.reg3 *
    zR 5w vals.reg5 *
    zR 6w vals.reg6 *
    zR 7w vals.reg7 *
    zR 8w vals.reg8 *
    zR 9w vals.reg9 *
    zR 10w vals.reg10 *
    zR 11w vals.reg11 *
    zR 12w vals.reg12 *
    zR 13w vals.reg13 *
    zR 14w vals.reg14 *
    zR 15w vals.reg15 *
    zSTACK (vals.stack_bottom,vals.stack) *
    zMEMORY64 vals.memory_domain vals.memory *
    zOPTION_CODE_HEAP vals.code_option cs.code_heap_length
                      cs.code_heap_ptr vals.code_list *
    zIO (cs.getchar_ptr,vals.input_stream,
         cs.putchar_ptr,vals.output_stream)`;

val zHEAP_def = Define `
  zHEAP (cs,x1,x2,x3,x4,refs,stack,s,space) =
    SEP_EXISTS vals.
      zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,space) vals)`;

val zHEAP_OUTPUT_def = Define `
  zHEAP_OUTPUT (cs,output) =
    SEP_EXISTS vals. zVALS cs vals * zPC cs.ret_address * ~zS *
                     cond ((vals.stack = cs.rest_of_stack) /\
                           (vals.output_stream = MAP (n2w o ORD) output))`;

val error_msg_def = Define `
  error_msg = "\nERROR: resource bound hit, aborting\n"`;

val zHEAP_ERROR_def = Define `
  zHEAP_ERROR (cs,output) =
    SEP_EXISTS part. zHEAP_OUTPUT (cs,part ++ error_msg) *
                     cond (isPREFIX part output)`;


(* helpers theorems *)

val getTag_def = Define `(getTag (Block n x) = n)`;
val getContent_def= Define `(getContent (Block n x) = x)`
val getNumber_def = Define `
  (getNumber (Number i) = i) /\
  (getNumber _ = 0)`;

val isBlock_def = Define `(isBlock (Block n x) = T) /\ (isBlock _ = F)`;

val isNumber_def = Define `
  (isNumber (Number i) = T) /\
  (isNumber _ = F)`;

val isRefPtr_def = Define `
  (isRefPtr (RefPtr i) = T) /\
  (isRefPtr _ = F)`;

val getRefPtr_def = Define `(getRefPtr (RefPtr x) = x) /\ (getRefPtr _ = ARB)`;

val isCodePtr_def = Define `
  (isCodePtr (CodePtr _) = T) /\ (isCodePtr _ = F)`;

val getCodePtr_def = Define `
  (getCodePtr (CodePtr x) = x)`;

val canCompare_def = Define `
  (canCompare (Number _) = T) /\
  (canCompare (RefPtr _) = T) /\
  (canCompare (Block _ _) = T) /\
  (canCompare _ = F)`;

val DISJ_IMP = METIS_PROVE [] ``(x \/ y ==> z) <=> (x ==> z) /\ (y ==> z)``;

val SPEC_WEAKEN_LEMMA = prove(
  ``(b ==> SPEC m (p * cond i) c q1) ==>
    !q2. (i ==> b /\ SEP_IMP q1 q2) ==>
         SPEC m (p * cond i) c q2``,
  Cases_on `i` THEN Cases_on `b` THEN SIMP_TAC std_ss [SPEC_MOVE_COND]
  THEN METIS_TAC [SPEC_WEAKEN]);

val EVERY2_IMP_LENGTH = prove(
  ``!xs ys P. EVERY2 P xs ys ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ SRW_TAC [] [EVERY2_def] \\ METIS_TAC []);

val blast_align_lemma = prove(
  ``(8w + w && 7w = w && 7w:word64) /\
    (w + 8w && 7w = w && 7w:word64) /\
    (w + 8w * x && 7w = w && 7w:word64) /\
    (w + x * 8w && 7w = w && 7w:word64) /\
    (w - 8w * x && 7w = w && 7w:word64) /\
    (w - x * 8w && 7w = w && 7w:word64)``,
  REPEAT STRIP_TAC \\ blastLib.BBLAST_TAC);

val PULL_IMP_EXISTS = METIS_PROVE []
  ``(P ==> ?x. Q x) <=> ?x. P ==> Q x``


(* helper automation *)

fun get_pc th = let
  val (_,_,_,post) = UNDISCH_ALL th |> concl |> dest_spec
  in find_term (can (match_term ``zPC (p + n2w n)``)) post end;

fun expand_pre th target = let
  val th = SIMP_RULE std_ss [SPEC_MOVE_COND,
             REWRITE_CONV [SEP_HIDE_def] ``~(zR r)``] th |> UNDISCH_ALL
           |> CONV_RULE (PRE_CONV (SIMP_CONV std_ss [SEP_CLAUSES]))
           |> SIMP_RULE std_ss [GSYM SPEC_PRE_EXISTS] |> SPEC_ALL
  val (_,p,_,_) = dest_spec (concl th)
  val ps = list_dest dest_star p
  val target_thm = target |> REWRITE_CONV [zVALS_def]
  val tm = target_thm |> concl |> rand
  val ts = list_dest dest_star tm
  fun find_inst tm = let
    val j = first (can (match_term tm)) ts
    in fst (match_term tm j) end handle HOL_ERR _ => []
  val th = INST (flatten (map find_inst ps)) th
  val (_,p,_,post) = dest_spec (concl th)
  val ps = list_dest dest_star p
  val rs = set_diff (map get_sep_domain ts) (map get_sep_domain ps)
  val rs = filter (fn t => mem (get_sep_domain t) rs) ts
  val frame = list_mk_star rs (type_of (hd ps))
  val th = MATCH_MP SPEC_FRAME th |> SPEC frame
  val (th,goal) = SPEC_STRENGTHEN_RULE th target
  in (th,goal) end;

fun spec str = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode str)
  in th end

fun compose_specs strs = let
  val th = SPEC_COMPOSE_RULE (map spec strs)
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
              |> UNDISCH_ALL
  in th end

fun x64_decompile name asm =
  decompilerLib.decompile_strings prog_x64Lib.x64_tools_64 name
    (x64_codegenLib.assemble asm);

fun x64_decompile_no_status name asm =
  decompilerLib.decompile_strings prog_x64Lib.x64_tools_64_no_status name
    (x64_codegenLib.assemble asm);

val (_,_,sts,_) = prog_x64Lib.x64_tools


(* SNOC imm8 to code heap *)

val imm8_sw2sw = prove(
  ``!imm8. n2w (SIGN_EXTEND 8 64 (w2n (imm8:word8)) MOD 256):word8 = imm8``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,LET_DEF]
  \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0 < 256:num``)]
  \\ FULL_SIMP_TAC std_ss []);

val zHEAP_CODE_SNOC_IMM = let
  val th1 = compose_specs ["mov r15,[r9+80]"]
  val ((th,_,_),_) = prog_x64Lib.x64_spec "41C607"
  val th = SIMP_RULE std_ss [imm8_sw2sw,zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
           |> Q.INST [`r15`|->`a + n2w (LENGTH (xs:word8 list))`]
           |> Q.GENL [`g`,`dg`]
           |> MATCH_MP zCODE_HEAP_SNOC |> Q.INST [`xs`|->`code`]
           |> DISCH ``a + n2w (LENGTH (code:word8 list)) = r15:word64``
           |> SIMP_RULE std_ss [] |> UNDISCH
  val th2 = compose_specs ["inc r15","mov [r9+80],r15"]
  val th = SPEC_COMPOSE_RULE [th1,th,th2]
  val th = th |> RW [GSYM zOPTION_CODE_HEAP_def]
              |> DISCH ``SOME F = mode`` |> SIMP_RULE std_ss [] |> UNDISCH
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            LENGTH s.code < cs.code_heap_length /\ (s.code_mode = SOME F))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                           s with code := SNOC imm8 s.code,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [PULL_FORALL] \\ REPEAT GEN_TAC \\ STRIP_TAC
    \\ SIMP_TAC std_ss [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.EXISTS_TAC `vals with <| memory := (vals.reg9 + 0x50w =+
         vals.memory (vals.reg9 + 0x50w) + 0x1w) vals.memory ;
         reg15 := (vals.memory (vals.reg9 + 0x50w) + 0x1w) ;
         code_list := SNOC imm8 vals.code_list |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ d ==> b /\ (c ==> d)``)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs with code_ptr := vs.code_ptr + 1w`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC
    \\ STRIP_TAC
    THEN1 (Q.PAT_ASSUM `0x7w && vs.base_ptr = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ Q.ABBREV_TAC `dm = vals.memory_domain` \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `m = vals.memory` \\ POP_ASSUM (K ALL_TAC)
    \\ SEP_W_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `xx = vs.code_ptr` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w] \\ SRW_TAC [] [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (LENGTH s.code < cs.code_heap_length /\ (s.code_mode = SOME F))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* SNOC number to code heap *)

val zHEAP_CODE_SNOC_X2_BYTE = let
  val th1 = compose_specs ["mov r15,[r9+80]","mov r14,r1","shr r14,2"]
  val th = spec "mov [r15], r14b"
  val th = SIMP_RULE std_ss [imm8_sw2sw,zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
           |> Q.INST [`r15`|->`a + n2w (LENGTH (xs:word8 list))`]
           |> Q.GENL [`g`,`dg`]
           |> MATCH_MP zCODE_HEAP_SNOC |> Q.INST [`xs`|->`code`]
           |> DISCH ``a + n2w (LENGTH (code:word8 list)) = r15:word64``
           |> SIMP_RULE std_ss [] |> UNDISCH
  val th2 = compose_specs ["inc r15","mov [r9+80],r15"]
  val th = SPEC_COMPOSE_RULE [th1,th,th2]
  val th = th |> RW [GSYM zOPTION_CODE_HEAP_def]
              |> DISCH ``SOME F = mode`` |> SIMP_RULE std_ss [] |> UNDISCH
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            LENGTH s.code < cs.code_heap_length /\ (s.code_mode = SOME F) /\
            isNumber x2 /\ small_int (getNumber x2))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                 s with code := SNOC (n2w (Num (getNumber x2))) s.code,NONE) *
                         ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [PULL_FORALL] \\ REPEAT GEN_TAC \\ STRIP_TAC
    \\ SIMP_TAC std_ss [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.EXISTS_TAC `vals with <| memory := (vals.reg9 + 0x50w =+
         vals.memory (vals.reg9 + 0x50w) + 0x1w) vals.memory ;
         reg14 := (vals.reg1 >>> 2) ;
         reg15 := (vals.memory (vals.reg9 + 0x50w) + 0x1w) ;
         code_list := SNOC (w2w (vals.reg1 >>> 2)) vals.code_list |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ d ==> b /\ (c ==> d)``)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs with code_ptr := vs.code_ptr + 1w`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC
    \\ STRIP_TAC
    THEN1 (Q.PAT_ASSUM `0x7w && vs.base_ptr = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ Q.ABBREV_TAC `dm = vals.memory_domain` \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `m = vals.memory` \\ POP_ASSUM (K ALL_TAC)
    \\ SEP_W_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `xx = vs.code_ptr` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w] \\ SRW_TAC [] []
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNumber_def,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
         EVERY2_def,bc_value_inv_def,x64_addr_def]
    \\ `(n2w (Num i) = (w2w:63 word -> word8) (n2w (Num i)))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [w2w_n2w])
    \\ FULL_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`n2w (Num i):63 word`,`w`)
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (LENGTH s.code < cs.code_heap_length /\ (s.code_mode = SOME F) /\
            isNumber x2 /\ small_int (getNumber x2))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;

val zHEAP_CODE_SNOC_X2_IMM32 = let
  val th1 = compose_specs ["mov r15,[r9+80]","mov r14,r1","shr r14,2"]
  val th = spec "mov [r15], r14b"
  val th = SIMP_RULE std_ss [imm8_sw2sw,zBYTE_MEMORY_def,GSYM zBYTE_MEMORY_Z_def] th
           |> Q.INST [`r15`|->`a + n2w (LENGTH (xs:word8 list))`]
           |> Q.GENL [`g`,`dg`]
           |> MATCH_MP zCODE_HEAP_SNOC |> Q.INST [`xs`|->`code`]
           |> DISCH ``a + n2w (LENGTH (code:word8 list)) = r15:word64``
           |> SIMP_RULE std_ss [] |> UNDISCH
  val thi = compose_specs ["inc r15","shr r14,8"]
  val th2 = compose_specs ["inc r15","mov [r9+80],r15"]
  val th = th |> RW [GSYM zOPTION_CODE_HEAP_def]
              |> DISCH ``SOME F = mode`` |> SIMP_RULE std_ss [] |> UNDISCH
  val th = SPEC_COMPOSE_RULE [th1,th,thi,th,thi,th,thi,th,th2]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            LENGTH s.code + 4 <= cs.code_heap_length /\ (s.code_mode = SOME F) /\
            isNumber x2 /\ small_int (getNumber x2))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                 s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))),NONE) *
                         ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [PULL_FORALL] \\ REPEAT GEN_TAC \\ STRIP_TAC
    \\ SIMP_TAC std_ss [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ SIMP_TAC std_ss [LENGTH_SNOC]
    \\ Q.PAT_ABBREV_TAC `pp:word8 list = SNOC xx yy`
    \\ Q.EXISTS_TAC `vals with <| memory := (vals.reg9 + 0x50w =+
         vals.memory (vals.reg9 + 0x50w) + 0x4w) vals.memory ;
         reg14 := (vals.reg1 >>> 2 >>> 8 >>> 8 >>> 8) ;
         reg15 := (vals.memory (vals.reg9 + 0x50w) + 0x4w) ;
         code_list := pp |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ d ==> b /\ (c ==> d)``)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs with code_ptr := vs.code_ptr + 4w`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC
    \\ Q.ABBREV_TAC `dm = vals.memory_domain` \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `m = vals.memory` \\ POP_ASSUM (K ALL_TAC)
    \\ SEP_W_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    THEN1 (Q.PAT_ASSUM `0x7w && vs.base_ptr = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ Q.PAT_ASSUM `xx = vs.code_ptr` (ASSUME_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [IMM32_def,LENGTH]
    \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w] \\ SRW_TAC [] []
    \\ TRY DECIDE_TAC
    \\ Q.UNABBREV_TAC `pp`
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNumber_def,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
         EVERY2_def,bc_value_inv_def,x64_addr_def]
    \\ `(n2w (Num i) = (w2w:63 word -> word32) (n2w (Num i)))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [w2w_n2w])
    \\ FULL_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`n2w (Num i):63 word`,`w`)
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (LENGTH s.code + 4 <= cs.code_heap_length /\ (s.code_mode = SOME F) /\
            isNumber x2 /\ small_int (getNumber x2))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* moves *)

val move_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x1i,r1i);(x2i,r2i);(x3i,r3i);(x4i,r4i)]`]
  |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM,DISJ_IMP] |> GEN_ALL

fun zHEAP_Move ((ni,ri),(nj,rj)) = let
  (* x64_encodeLib.x64_encode "mov r0d,50000" *)
  val i = x64_encodeLib.x64_encode ("mov "^ri^" , "^rj)
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64 i
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH T
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val src = ``if ^nj = 1 then x1 else
              if ^nj = 2 then x2 else
              if ^nj = 3 then x3 else x4:bc_value``
  val th = th |> Q.SPEC
    `zHEAP (cs,if ^ni = 1 then ^src else x1,
               if ^ni = 2 then ^src else x2,
               if ^ni = 3 then ^src else x3,
               if ^ni = 4 then ^src else x4,
               refs,stack,s,NONE) * ~zS * ^pc`
  val vals_src = ``if ^nj = 1 then vals.reg0 else
                   if ^nj = 2 then vals.reg1 else
                   if ^nj = 3 then vals.reg2 else vals.reg3``
  val root_src = ``if ^nj = 1 then r1 else
                   if ^nj = 2 then r2 else
                   if ^nj = 3 then r3 else r4: 63 word heap_address``
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <|
         reg0 := if ^ni = 1 then ^vals_src else vals.reg0 ;
         reg1 := if ^ni = 2 then ^vals_src else vals.reg1 ;
         reg2 := if ^ni = 3 then ^vals_src else vals.reg2 ;
         reg3 := if ^ni = 4 then ^vals_src else vals.reg3 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
         `if ^ni = 1 then ^root_src else r1`,
         `if ^ni = 2 then ^root_src else r2`,
         `if ^ni = 3 then ^root_src else r3`,
         `if ^ni = 4 then ^root_src else r4`,
         `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
    \\ MATCH_MP_TAC move_lemma
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val x1 = (``1:num``,"r0")
val x2 = (``2:num``,"r1")
val x3 = (``3:num``,"r2")
val x4 = (``4:num``,"r3")

fun cross_prod [] ys = []
  | cross_prod (x::xs) ys = map (fn y => (x,y)) ys :: cross_prod xs ys

val all_moves = cross_prod [x1,x2,x3,x4] [x1,x2,x3,x4] |> Lib.flatten
                |> filter (fn (x,y) => (x <> y))

val moves = map zHEAP_Move all_moves;

val zHEAP_MOVE_12 = el 4 moves


(* load const number *)

val swap12_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x2,r2);(x1,r1);(x3,r3);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM,DISJ_IMP] |> GEN_ALL

val swap13_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x3,r3);(x2,r2);(x1,r1);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM,DISJ_IMP] |> GEN_ALL

val swap14_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x4,r4);(x2,r2);(x3,r3);(x1,r1)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM,DISJ_IMP] |> GEN_ALL

val swap_1_lemmas = LIST_CONJ [swap12_lemma,swap13_lemma,swap14_lemma];

val get_tag_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1)]`,`[]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM]

val abs_ml_inv_Num = prove(
  ``abs_ml_inv (x::stack) refs (r1::roots,heap,a,sp) l /\ n < 4611686018427387904 ==>
    abs_ml_inv (Number (&n)::stack) refs (Data (0x2w * n2w n)::roots,heap,a,sp) l``,
  REPEAT STRIP_TAC
  \\ `abs_ml_inv (stack) refs (roots,heap,a,sp) l` by ALL_TAC
  THEN1 (METIS_TAC [get_tag_lemma])
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM]
  \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss [EVERY2_def]
  \\ REPEAT STRIP_TAC THEN1
   (`small_int (&n)` by ALL_TAC
    THEN1 (SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ ASM_SIMP_TAC std_ss [bc_value_inv_def] \\ REPEAT AP_TERM_TAC
    \\  intLib.COOPER_TAC)
  \\ `reachable_refs stack refs n'` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM,PULL_EXISTS]
  \\ NTAC 3 (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]
  \\ METIS_TAC []) |> GEN_ALL;

fun zHEAP_Num (i,n) = let
  (* x64_encodeLib.x64_encode "mov r0d,50000" *)
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64 i
  val lemma = prove(
    ``4 * k < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (4 * k)):word32)) MOD 4294967296)) =
       n2w (4 * k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(4 * k) < 4294967296 /\ ~(2147483648 <= 4 * k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = th |> Q.INST [`rip`|->`p`,`imm32`|->`n2w (4 * k)`] |> RW [lemma]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            4 * (k:num) < 2**31)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,if ^n = 1 then Number (& k) else x1,
               if ^n = 2 then Number (& k) else x2,
               if ^n = 3 then Number (& k) else x3,
               if ^n = 4 then Number (& k) else x4,
               refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <|
         reg0 := if ^n = 1 then n2w (4 * k) else vals.reg0 ;
         reg1 := if ^n = 2 then n2w (4 * k) else vals.reg1 ;
         reg2 := if ^n = 3 then n2w (4 * k) else vals.reg2 ;
         reg3 := if ^n = 4 then n2w (4 * k) else vals.reg3 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
         `if ^n = 1 then Data (2w * n2w k) else r1`,
         `if ^n = 2 then Data (2w * n2w k) else r2`,
         `if ^n = 3 then Data (2w * n2w k) else r3`,
         `if ^n = 4 then Data (2w * n2w k) else r4`,
         `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REPEAT STRIP_TAC THEN1
     (`k < 4611686018427387904` by DECIDE_TAC
      \\ METIS_TAC [abs_ml_inv_Num,swap_1_lemmas])
    \\ `(2 * k) < 9223372036854775808` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [x64_addr_def,WORD_MUL_LSL,word_mul_n2w,
          w2w_def,w2n_n2w,MULT_ASSOC]);
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (4 * (k:num) < 2**31)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_Num1 = zHEAP_Num ("B8",``1:num``)
val zHEAP_Num2 = zHEAP_Num ("B9",``2:num``)
val zHEAP_Num3 = zHEAP_Num ("BA",``3:num``)
val zHEAP_Num4 = zHEAP_Num ("BB",``4:num``)

fun up_to 0 = [] | up_to k = up_to (k-1) @ [k-1]

fun derive_const_assign th k = let
  val th = th |> INST [``k:num``|->numLib.term_of_int k]
  val th = th |> SIMP_RULE (srw_ss()) [w2w_def,w2n_n2w,SEP_CLAUSES]
  val _ = x64_codegenLib.add_compiled [th];
  in () end;

val _ = map (derive_const_assign zHEAP_Num1) (up_to 256)
val _ = map (derive_const_assign zHEAP_Num2) (up_to 256)
val _ = map (derive_const_assign zHEAP_Num3) (up_to 256)
val _ = map (derive_const_assign zHEAP_Num4) (up_to 256)


(* cons with NIL *)

val abs_ml_inv_Block_NIL = prove(
  ``abs_ml_inv (x::stack) refs (r1::roots,heap,a,sp) l /\ n < 4611686018427387904 ==>
    abs_ml_inv (Block (&n) []::stack) refs
      (Data (n2w (2 * n + 1))::roots,heap,a,sp) l``,
  REPEAT STRIP_TAC
  \\ `abs_ml_inv (stack) refs (roots,heap,a,sp) l` by ALL_TAC
  THEN1 (METIS_TAC [get_tag_lemma])
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM]
  \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss [EVERY2_def]
  \\ ASM_SIMP_TAC std_ss [bc_value_inv_def,word_mul_n2w,word_add_n2w]
  \\ REPEAT STRIP_TAC
  \\ `reachable_refs stack refs n'` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM,PULL_EXISTS]
  \\ NTAC 3 (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,MAP,FLAT]
  \\ METIS_TAC []) |> GEN_ALL;

fun zHEAP_Nil (i,n) = let
  (* x64_encodeLib.x64_encode "mov r0d,50000" *)
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64 i
  val lemma = prove(
    ``4 * k + 2 < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (4 * k + 2)):word32)) MOD 4294967296)) =
       n2w (4 * k + 2):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(4 * k + 2) < 4294967296 /\ ~(2147483648 <= 4 * k + 2)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = th |> Q.INST [`rip`|->`p`,`imm32`|->`n2w (4 * k + 2)`] |> RW [lemma]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            4 * (k:num) + 2 < 2**31)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,if ^n = 1 then Block (& k) [] else x1,
               if ^n = 2 then Block (& k) [] else x2,
               if ^n = 3 then Block (& k) [] else x3,
               if ^n = 4 then Block (& k) [] else x4,
               refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <|
         reg0 := if ^n = 1 then n2w (4 * k + 2) else vals.reg0 ;
         reg1 := if ^n = 2 then n2w (4 * k + 2) else vals.reg1 ;
         reg2 := if ^n = 3 then n2w (4 * k + 2) else vals.reg2 ;
         reg3 := if ^n = 4 then n2w (4 * k + 2) else vals.reg3 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
         `if ^n = 1 then Data (2w * n2w k + 1w) else r1`,
         `if ^n = 2 then Data (2w * n2w k + 1w) else r2`,
         `if ^n = 3 then Data (2w * n2w k + 1w) else r3`,
         `if ^n = 4 then Data (2w * n2w k + 1w) else r4`,
         `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REPEAT STRIP_TAC THEN1
     (`k < 4611686018427387904` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
      \\ METIS_TAC [abs_ml_inv_Block_NIL,swap_1_lemmas])
    \\ `(2 * k + 1) < 9223372036854775808` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [x64_addr_def,WORD_MUL_LSL,word_mul_n2w,
          w2w_def,w2n_n2w,MULT_ASSOC,word_add_n2w,MULT_ASSOC]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]);
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (4 * (k:num) + 2 < 2**31)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val lemmas = CONJ (EVAL ``bool_to_val F``) (EVAL ``bool_to_val T``) |> GSYM;

fun foo th = let
  val th0 = Q.INST [`k`|->`0`] th
            |> SIMP_RULE (srw_ss()) [SEP_CLAUSES] |> RW [lemmas]
  val th1 = Q.INST [`k`|->`1`] th
            |> SIMP_RULE (srw_ss()) [SEP_CLAUSES] |> RW [lemmas]
  val _ = x64_codegenLib.add_compiled [th0];
  val _ = x64_codegenLib.add_compiled [th1];
  in th end

val zHEAP_Nil1 = zHEAP_Nil ("B8",``1:num``) |> foo
val zHEAP_Nil2 = zHEAP_Nil ("B9",``2:num``) |> foo
val zHEAP_Nil3 = zHEAP_Nil ("BA",``3:num``) |> foo
val zHEAP_Nil4 = zHEAP_Nil ("BB",``4:num``) |> foo


(* push x1,x2,x3,x4 *)

val push_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x1,r1);(x2,r2);(x3,r3);(x4,r4);(x5,r5)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM]

fun zHEAP_PUSH n = let
  val th = if n = ``1:num`` then x64_push_r0 else
           if n = ``2:num`` then x64_push_r1 else
           if n = ``3:num`` then x64_push_r2 else
           if n = ``4:num`` then x64_push_r3 else fail()
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,
                   (if ^n = 1 then x1 else
                    if ^n = 2 then x2 else
                    if ^n = 3 then x3 else
                    if ^n = 4 then x4 else ARB)::stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `(vals:x64_vals) with <| stack :=
         (if ^n = 1 then ((vals:x64_vals).reg0):word64 else
          if ^n = 2 then vals.reg1 else
          if ^n = 3 then vals.reg2 else
          if ^n = 4 then vals.reg3 else ARB)::vals.stack |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`
          (if ^n = 1 then r1 else
           if ^n = 2 then r2 else
           if ^n = 3 then r3 else
           if ^n = 4 then r4 else ARB)::roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,APPEND]
    \\ MATCH_MP_TAC push_lemma \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val zHEAP_PUSH1 = zHEAP_PUSH ``1:num``
val zHEAP_PUSH2 = zHEAP_PUSH ``2:num``
val zHEAP_PUSH3 = zHEAP_PUSH ``3:num``
val zHEAP_PUSH4 = zHEAP_PUSH ``4:num``


(* pop x1,x2,x3,x4 *)

val pop_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4);(x5,r5)]`,
              `[(x1',r1');(x2',r2');(x3',r3');(x4',r4')]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM] |> GEN_ALL

fun zHEAP_POP n = let
  val th = if n = ``1:num`` then x64_pop_r0 else
           if n = ``2:num`` then x64_pop_r1 else
           if n = ``3:num`` then x64_pop_r2 else
           if n = ``4:num`` then x64_pop_r3 else fail()
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ stack <> [])``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val hd_stack = ``(HD stack):bc_value``
  val x1 = if n = ``1:num`` then hd_stack else ``x1:bc_value``
  val x2 = if n = ``2:num`` then hd_stack else ``x2:bc_value``
  val x3 = if n = ``3:num`` then hd_stack else ``x3:bc_value``
  val x4 = if n = ``4:num`` then hd_stack else ``x4:bc_value``
  val th = th |> Q.SPEC `zHEAP (cs,^x1,^x2,^x3,^x4,refs,TL stack,s,NONE) * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val r0 = if n = ``1:num`` then ``HD vals.stack`` else ``vals.reg0``
  val r1 = if n = ``2:num`` then ``HD vals.stack`` else ``vals.reg1``
  val r2 = if n = ``3:num`` then ``HD vals.stack`` else ``vals.reg2``
  val r3 = if n = ``4:num`` then ``HD vals.stack`` else ``vals.reg3``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def] \\ Cases_on `roots`
      \\ FULL_SIMP_TAC std_ss [MAP,APPEND,NOT_CONS_NIL])
    \\ Q.EXISTS_TAC `vals with <| stack := TL vals.stack ;
                                  reg0 := ^r0 ;
                                  reg1 := ^r1 ;
                                  reg2 := ^r2 ;
                                  reg3 := ^r3 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,
         if n = ``1:num`` then `HD roots` else `r1`,
         if n = ``2:num`` then `HD roots` else `r2`,
         if n = ``3:num`` then `HD roots` else `r3`,
         if n = ``4:num`` then `HD roots` else `r4`,`TL roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL]
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `stack` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `roots` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,MAP,HD,TL,APPEND]
    \\ MATCH_MP_TAC pop_lemma \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
            |> DISCH ``(stack:bc_value list) <> []``
            |> SIMP_RULE std_ss [] |> UNDISCH
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val zHEAP_POP1 = zHEAP_POP ``1:num``
val zHEAP_POP2 = zHEAP_POP ``2:num``
val zHEAP_POP3 = zHEAP_POP ``3:num``
val zHEAP_POP4 = zHEAP_POP ``4:num``


(* pops *)

val pops_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]++ZIP (xs,ys)`,
              `[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM] |> GEN_ALL

val MAP_FST_ZIP = prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (MAP FST (ZIP(xs,ys)) = xs) /\ (MAP SND (ZIP(xs,ys)) = ys)``,
  Induct \\ Cases_on `ys` \\ SRW_TAC [] [LENGTH,ADD1,ZIP]);

val zHEAP_POPS = let
  val th = x64_pops |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            k <= LENGTH stack /\ k < 268435456)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,DROP k stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH
      \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `vals with <| stack := DROP k vals.stack |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`DROP k roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,APPEND,HD,TL]
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ `k <= LENGTH roots` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `stack = zs1 ++ zs2` []
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC]
    \\ Tactical.REVERSE STRIP_TAC
    THEN1 (METIS_TAC [rich_listTheory.DROP_LENGTH_APPEND,LENGTH_MAP])
    \\ `DROP k (ys1 ++ ys2) = ys2` by METIS_TAC [rich_listTheory.DROP_LENGTH_APPEND]
    \\ `DROP k (zs1 ++ zs2) = zs2` by METIS_TAC [rich_listTheory.DROP_LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC pops_lemma
    \\ ONCE_REWRITE_TAC [CONJ_COMM]
    \\ Q.LIST_EXISTS_TAC [`ys1`,`zs1`]
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ `LENGTH zs1 = LENGTH ys1` by FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MAP_FST_ZIP \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
            |> DISCH ``k <= LENGTH (stack:bc_value list)``
            |> DISCH ``k < 268435456:num``
            |> SIMP_RULE std_ss [] |> UNDISCH_ALL
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* load *)

val load_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x2,r2);(x3,r3);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM] |> GEN_ALL

val EL_LENGTH = prove(
  ``!xs. EL (LENGTH xs) (xs ++ y::ys) = y``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD,TL]);

val zHEAP_LOAD = let
  val th = x64_el_r0_imm |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            k < LENGTH stack /\ k < 268435456)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,EL k stack,x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH
      \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `vals with <| reg0 := EL k vals.stack |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`EL k roots`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,APPEND,HD,TL]
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ `k < LENGTH roots` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `stack = zs1 ++ z::zs2` []
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC,MAP]
    \\ Tactical.REVERSE STRIP_TAC
    THEN1 (METIS_TAC [EL_LENGTH,LENGTH_MAP,APPEND])
    \\ `EL k (ys1 ++ y::ys2) = y` by METIS_TAC [EL_LENGTH]
    \\ `EL k (zs1 ++ z::zs2) = z` by METIS_TAC [EL_LENGTH]
    \\ FULL_SIMP_TAC std_ss []
    \\ (move_thm
        |> Q.SPECL [`[x1]`,`[r1]`,`[x1]`,`[r1]`,`[x2;x3;x4]++xs`,`[r2;r3;r4]++rs`]
        |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC] |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC duplicate1_thm
    \\ (move_thm
        |> Q.SPECL [`[]`,`[]`,`[x2;x3;x4]++xs`,`[r2;r3;r4]++rs`,`[x1]`,`[r1]`]
        |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC] |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC load_lemma \\ METIS_TAC [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
            |> DISCH ``k < LENGTH (stack:bc_value list)``
            |> DISCH ``k < 268435456:num``
            |> SIMP_RULE std_ss [] |> UNDISCH_ALL
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* store *)

val store_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1)]`,`[]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM] |> GEN_ALL

val zHEAP_STORE = let
  val th = x64_lupdate_r0_imm |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            k < LENGTH stack /\ k < 268435456)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,LUPDATE x1 k stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH
      \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND] \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `vals with <| stack := LUPDATE vals.reg0 k vals.stack |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`LUPDATE r1 k roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,APPEND,HD,TL]
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ `k < LENGTH roots` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.MATCH_ASSUM_RENAME_TAC `stack = zs1 ++ z::zs2` []
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC,MAP]
    \\ `LUPDATE r1 k (ys1 ++ y::ys2) = ys1 ++ r1::ys2` by METIS_TAC [LUPDATE_LENGTH]
    \\ `LUPDATE x1 k (zs1 ++ z::zs2) = zs1 ++ x1::zs2` by METIS_TAC [LUPDATE_LENGTH]
    \\ FULL_SIMP_TAC std_ss []
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,APPEND]
      \\ `k = LENGTH (MAP (x64_addr vs.current_heap) ys1)` by
           FULL_SIMP_TAC std_ss [LENGTH_MAP]
      \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
      \\ SIMP_TAC std_ss [LUPDATE_LENGTH] \\ SRW_TAC [] [])
    \\ (move_thm
        |> Q.SPECL [`[x1]`,`[r1]`,`[x1]`,`[r1]`,`[x2;x3;x4]++xs`,`[r2;r3;r4]++rs`]
        |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC] |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC duplicate1_thm
    \\ MATCH_MP_TAC store_lemma
    \\ Q.LIST_EXISTS_TAC [`z`,`y`]
    \\ (move_thm
        |> Q.SPECL [`[]`,`[]`,`[x1;x2;x3;x4]++xs`,`[r1;r2;r3;r4]++rs`,`[z]`,`[y]`]
        |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC] |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
            |> DISCH ``k < LENGTH (stack:bc_value list)``
            |> DISCH ``k < 268435456:num``
            |> SIMP_RULE std_ss [] |> UNDISCH_ALL
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* push handler *)

val reintro_word_sub = SIMP_CONV (srw_ss()) [] ``-(n2w n):word64`` |> GSYM

val blast_lemma1 = prove(
  ``(w && 1w = 0w) ==> ((w >>> 1 << 1) = w:word64)``,
  blastLib.BBLAST_TAC)

val blast_lemma2 = prove(
  ``-(8w * w) + v && 1w = v && 1w:word64``,
  blastLib.BBLAST_TAC)

val zREAD_HANDLER = let
  val th = spec "mov r0,r11" |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
    StackPtr ((w2n (cs.stack_trunk - n2w (8 * s.handler))) DIV 2),
    x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg0 := vals.reg11`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ `cs.stack_trunk && 1w = 0w` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,stack_inv_def]
      \\ Q.PAT_ASSUM `cs.stack_trunk && 0x3w = 0x0w` MP_TAC
      \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,stack_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`Data (n2w (w2n (vals.reg11) DIV 2))`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,APPEND,HD,TL]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,reintro_word_sub]
    \\ FULL_SIMP_TAC std_ss [w2w_def,w2n_n2w]
    \\ `!w:word64. (w2n w DIV 2) < dimword (:63)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [DIV_LT_X] \\ EVAL_TAC
      \\ ASSUME_TAC (w2n_lt |> INST_TYPE [``:'a``|->``:64``])
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [w2n_lsr |> Q.SPECL [`w`,`1`] |>
         SIMP_RULE std_ss [] |> GSYM,n2w_w2n]
    \\ REVERSE STRIP_TAC THEN1
     (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ MATCH_MP_TAC blast_lemma1
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,blast_lemma2]
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,roots_ok_def]
    \\ FULL_SIMP_TAC (srw_ss()) [MEM]
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
    \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss [EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
    \\ REPEAT STRIP_TAC
    \\ FIRST_ASSUM MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
    \\ Q.LIST_EXISTS_TAC [`x`,`r`] \\ FULL_SIMP_TAC std_ss [MEM]
    \\ NTAC 2 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;

val x64_mov_r11_r4 = let
  val th = spec "mov r11,r4" |> Q.INST [`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``zSS stack *
             cond ((r4 && 0x7w = 0x0w) /\
                   (base = (r4:word64) + n2w (8 * LENGTH stack)))``
  val (th,goal) = SPEC_WEAKEN_RULE th
                  ``zPC (p + 0x3w) * zR 0xBw (base - n2w (8 * LENGTH stack)) *
                    zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,WORD_ADD_SUB])
  val th = MP th lemma
  val th = HIDE_PRE_RULE ``zR 4w`` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th
                  ``zPC p * zR 0xBw r11 * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `rsp`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,WORD_ADD_SUB])
  val th = MP th lemma
  in th end

val zWRITE_HANDLER = let
  val th = x64_mov_r11_r4
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
            s with handler := LENGTH stack,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg11 :=
         vals.stack_bottom - n2w (8 * LENGTH vals.stack)`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,stack_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,APPEND,HD,TL]
    \\ FULL_SIMP_TAC std_ss [reintro_word_sub]
    \\ Q.PAT_ASSUM `xxx = cs.stack_trunk` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD1,GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD1,GSYM word_add_n2w]
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ FULL_SIMP_TAC std_ss [WORD_NEG_ADD] \\ SRW_TAC [] [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;

val zBC_PushExc_raw =
  SPEC_COMPOSE_RULE [zHEAP_PUSH1,zREAD_HANDLER,zWRITE_HANDLER]


(* pop handler *)

val x64_mov_r4_r11 = prove(
  ``SPEC X64_MODEL
      (zPC p * zR 0xBw r11 * zSTACK (base,ss) *
       cond (w2n (base - r11) DIV 8 <= LENGTH ss))
      {(p,[0x49w; 0x8Bw; 0xE3w])}  (* mov r4,r11 *)
      (zPC (p + 0x3w) * zR 0xBw r11 *
        zSTACK (base,DROP (LENGTH ss - w2n (base - r11) DIV 8) ss))``,
  cheat);

val abs_ml_inv_PushExn = prove(
  ``abs_ml_inv
        (x1::x2::x3::x4::(l1 ++ StackPtr n::l2)) refs
        (r1::r2::r3::r4::roots,heap,a,sp) l ==>
    ?rr1 rr2.
       (roots = rr1 ++ Data (n2w n)::rr2) /\
       (LENGTH l1 = LENGTH rr1) /\
       (LENGTH l2 = LENGTH rr2)``,
  SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [EVERY2_def]
  \\ IMP_RES_TAC EVERY2_SPLIT_ALT \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`]
  \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss []);

val blast_lemma_sub_sub = prove(
  ``-1w * -w = w:word64``,
  blastLib.BBLAST_TAC);

val MOD_LESS_ALT = prove(
  ``0 < k /\ m < l ==> (m MOD k < l:num)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MOD_LESS_EQ
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `m`)
  \\ DECIDE_TAC);

val zBC_PopExc_raw = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "4981EB08000000"
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val th = SPEC_COMPOSE_RULE [th,x64_mov_r4_r11,x64_pop_r11]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) []
  val pc = get_pc th
  val sp = ``(w2n (cs.stack_trunk - n2w (8 * sp)) DIV 2)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,
                      l1 ++ StackPtr ^sp::l2,s,NONE) vals /\
            (LENGTH l2 = s.handler))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,l2,
            s with handler := sp,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ REPEAT GEN_TAC
    \\ STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ `w2n (vals.stack_bottom - (vals.reg11 - 0x8w)) DIV 8 =
        LENGTH cs.rest_of_stack + LENGTH l2 + 3` by ALL_TAC THEN1
     (FULL_SIMP_TAC (std_ss++sep_cond_ss) [heap_inv_def,stack_inv_def,cond_STAR]
      \\ Q.PAT_ASSUM `xx = cs.stack_trunk` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,stack_inv_def,LENGTH,LENGTH_APPEND]
      \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,WORD_SUB_SUB2]
      \\ SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
      \\ `(8 * LENGTH cs.rest_of_stack + (16 + (8 * LENGTH l2 + 8)))
            < dimword (:64)` by cheat \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ `(LENGTH vals.stack - (LENGTH cs.rest_of_stack + LENGTH l2 + 3)) =
        LENGTH l1` by ALL_TAC THEN1
     (FULL_SIMP_TAC (std_ss++sep_cond_ss) [heap_inv_def,stack_inv_def,cond_STAR]
      \\ FULL_SIMP_TAC std_ss [EVERY2_def,abs_ml_inv_def,APPEND,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC (GSYM EVERY2_IMP_LENGTH)
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.EXISTS_TAC `vals with <| stack := TL (DROP (LENGTH l1) vals.stack) ;
                                  reg11 := HD (DROP (LENGTH l1) vals.stack) |>`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,zVALS_def]
    \\ SIMP_TAC (srw_ss()++star_ss) []
    \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,stack_inv_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,
          `TL (DROP (LENGTH l1) roots)`,`heap`,`a`,`sp'`]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [reintro_word_sub]
    \\ IMP_RES_TAC abs_ml_inv_PushExn
    \\ FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,
         rich_listTheory.DROP_LENGTH_APPEND,TL,HD]
    \\ `LENGTH rr1 = LENGTH (MAP (x64_addr vs.current_heap) rr1)` by
         FULL_SIMP_TAC std_ss [LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,GSYM APPEND_ASSOC,
         rich_listTheory.DROP_LENGTH_APPEND,TL,HD,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def] \\ POP_ASSUM (K ALL_TAC)
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,roots_ok_def,MEM,MEM_APPEND]
      \\ STRIP_TAC THEN1 METIS_TAC []
      \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
      \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss [EVERY2_def]
      \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND,LENGTH_MAP,EVERY2_def]
      \\ REPEAT STRIP_TAC \\ FIRST_ASSUM MATCH_MP_TAC
      \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
      \\ Q.LIST_EXISTS_TAC [`x`,`r`]
      \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND])
    \\ FULL_SIMP_TAC std_ss [w2w_def,w2n_n2w]
    \\ `!w:word64. (w2n w DIV 2) < dimword (:63)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [DIV_LT_X] \\ EVAL_TAC
      \\ ASSUME_TAC (w2n_lt |> INST_TYPE [``:'a``|->``:64``])
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [w2n_lsr |> Q.SPECL [`w`,`1`] |>
         SIMP_RULE std_ss [] |> GSYM,n2w_w2n]
    \\ MATCH_MP_TAC blast_lemma1
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,blast_lemma2]
    \\ Q.PAT_ASSUM `3w && cs.stack_trunk = 0x0w` MP_TAC
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, l1 ++ StackPtr ^sp::l2, s, NONE) *
      ~zS * zPC p * cond (LENGTH l2 = s.handler)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* get tag *)

val (x64_get_tag_res, x64_get_tag_def, x64_get_tag_pre_def) = x64_compile `
  x64_get_tag (r0:word64,dm:word64 set,m:word64->word64) =
    if r0 && 1w = 0w then
      let r0 = r0 - 2w in (r0,dm,m)
    else
      let r0 = m (r0 + 1w) in
      let r0 = r0 && 65535w in
      let r0 = r0 >>> 2 in
        (r0,dm,m)`

val get_tag_blast = prove(
  ``!w1 w. w1 <+ 0x10000w ==> ((0x10000w * w + w1) && 0xFFFFw = w1:word64)``,
  blastLib.BBLAST_TAC);

val zHEAP_GET_TAG = let
  val th = x64_get_tag_res
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ isBlock x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (& (getTag x1)),x2,x3,x4,
                                refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isBlock_def,APPEND]
    \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss []
    THEN1
     (`(r1 = Data (2w * n2w n + 1w)) /\ n < 2**62` by ALL_TAC THEN1
         (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
            EVERY2_def,bc_value_inv_def])
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,x64_get_tag_pre_def,x64_get_tag_def]
      \\ `(w2w (0x2w * n2w n + 0x1w:63 word) << 1 && 0x1w = 0x0w:word64) /\
          (w2w (0x2w * n2w n + 0x1w:63 word) << 1 - 0x2w:word64 =
           w2w (0x2w * n2w n:63 word) << 1)` by ALL_TAC THEN1 blastLib.BBLAST_TAC
      \\ FULL_SIMP_TAC std_ss [LET_DEF,getTag_def]
      \\ REPEAT STRIP_TAC
      \\ Q.EXISTS_TAC `vals with <| reg0 := w2w ((0x2w:63 word) * n2w n) << 1 |>`
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
      \\ STRIP_TAC THEN1
       (POP_ASSUM (K ALL_TAC)
        \\ FULL_SIMP_TAC std_ss [heap_inv_def]
        \\ Q.LIST_EXISTS_TAC [`vs`,`Data (2w * n2w n)`,`r2`,`r3`,`r4`,
             `roots`,`heap`,`a`,`sp`]
        \\ FULL_SIMP_TAC (srw_ss()) [APPEND,x64_addr_def]
        \\ METIS_TAC [abs_ml_inv_Num])
      \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
      \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ FULL_SIMP_TAC (std_ss++star_ss) []
      \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
    \\ `?f. bc_value_inv (Block n l) (r1,f,heap)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
      \\ METIS_TAC []) \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [x64_get_tag_def,x64_get_tag_pre_def,LET_DEF]
    \\ `(x64_addr vs.current_heap (Pointer ptr) && 0x1w) <> 0x0w` by ALL_TAC
    THEN1 (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
           \\ FULL_SIMP_TAC std_ss [x64_addr_def,heap_vars_ok_def]
           \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC heap_lookup_SPLIT
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,BlockRep_def]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_mul_n2w,
        AC MULT_COMM MULT_ASSOC,WORD_ADD_0] \\ SEP_R_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ SIMP_TAC std_ss [blast_align_lemma]
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def])
    \\ FULL_SIMP_TAC std_ss [getTag_def,WORD_SUB_ADD,word_mul_n2w]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ `0x10000w * n2w (LENGTH xs) + 0x10w * n2w (n MOD 4096) &&
          0xFFFFw = 0x10w * n2w (n MOD 4096):word64` by ALL_TAC THEN1
     (MATCH_MP_TAC get_tag_blast \\ FULL_SIMP_TAC std_ss [word_mul_n2w,WORD_LO]
      \\ `n MOD 4096 < 4096` by FULL_SIMP_TAC std_ss [MOD_LESS]
      \\ `(16 * n MOD 4096 < 18446744073709551616)` by DECIDE_TAC
      \\ ASM_SIMP_TAC (srw_ss()) [w2n_n2w] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg0 := ((0x10w * n2w (n MOD 4096)) >>> 2) |>`
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ FULL_SIMP_TAC (srw_ss()++star_ss) [])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`Data (2w * n2w n)`,`r2`,`r3`,`r4`,`roots`,
                          `heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [word_mul_n2w] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,BlockRep_def]
    \\ `n < 4096` by cheat
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
      \\ `n < 4611686018427387904` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ METIS_TAC [abs_ml_inv_Num])
    \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `xxx (fun2set yyy)` MP_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC,
         heap_length_APPEND,LEFT_ADD_DISTRIB,GSYM word_add_n2w,heap_length_def,
         MAP,SUM]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [GSYM w2n_11]
    \\ FULL_SIMP_TAC std_ss [w2n_lsr]
    \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w,w2w_def,word_mul_n2w]
    \\ `(2 * n) < 9223372036854775808 /\
        (2 * (2 * n)) < 18446744073709551616 /\
        (16 * n) < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isBlock x1)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* get length *)

val (x64_get_length_res, x64_get_length_def, x64_get_length_pre_def) = x64_compile `
  x64_get_length (r0:word64,dm:word64 set,m:word64->word64) =
    if r0 && 1w = 0w then
      let r0 = 0w in (r0,dm,m)
    else
      let r0 = m (r0 + 1w) in
      let r0 = r0 >>> 16 in
      let r0 = r0 << 2 in
        (r0,dm,m)`

val get_length_blast = prove(
  ``!w1 w. 0x10w * w1 <+ 0x10000w /\ w <+ n2w (2**32) ==>
           ((0x10000w * w + 0x10w * w1) >>> 16 = w:word64)``,
  blastLib.BBLAST_TAC);

val zHEAP_GET_LENGTH = let
  val th = x64_get_length_res
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ isBlock x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (& (LENGTH (getContent x1))),x2,x3,x4,
                                refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isBlock_def,APPEND]
    \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss []
    THEN1
     (`(r1 = Data (2w * n2w n + 1w)) /\ n < 2**62` by ALL_TAC THEN1
         (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
            EVERY2_def,bc_value_inv_def])
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,
           x64_get_length_pre_def,x64_get_length_def]
      \\ `(w2w (0x2w * n2w n + 0x1w:63 word) << 1 && 0x1w = 0x0w:word64) /\
          (w2w (0x2w * n2w n + 0x1w:63 word) << 1 - 0x2w:word64 =
           w2w (0x2w * n2w n:63 word) << 1)` by ALL_TAC THEN1 blastLib.BBLAST_TAC
      \\ FULL_SIMP_TAC std_ss [LET_DEF,getContent_def]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [LENGTH,cond_STAR]
      \\ Q.EXISTS_TAC `vals with <| reg0 := w2w ((0x2w:63 word) * n2w 0) << 1 |>`
      \\ STRIP_TAC THEN1
       (POP_ASSUM (K ALL_TAC)
        \\ FULL_SIMP_TAC std_ss [heap_inv_def]
        \\ Q.LIST_EXISTS_TAC [`vs`,`Data (2w * n2w 0)`,`r2`,`r3`,`r4`,
             `roots`,`heap`,`a`,`sp`]
        \\ FULL_SIMP_TAC (srw_ss()) [APPEND,x64_addr_def]
        \\ MATCH_MP_TAC (abs_ml_inv_Num |> SPEC_ALL |> Q.INST [`n`|->`0`]
            |> SIMP_RULE std_ss [word_mul_n2w] |> GEN_ALL) \\ METIS_TAC [])
      \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
      \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ FULL_SIMP_TAC (std_ss++star_ss) []
      \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
    \\ `?f. bc_value_inv (Block n l) (r1,f,heap)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
      \\ METIS_TAC []) \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [x64_get_length_def,x64_get_length_pre_def,LET_DEF]
    \\ `(x64_addr vs.current_heap (Pointer ptr) && 0x1w) <> 0x0w` by ALL_TAC
    THEN1 (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
           \\ FULL_SIMP_TAC std_ss [x64_addr_def,heap_vars_ok_def]
           \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC heap_lookup_SPLIT
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,BlockRep_def]
    \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [word_arith_lemma3,word_mul_n2w,
        AC MULT_COMM MULT_ASSOC,WORD_ADD_0] \\ SEP_R_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ SIMP_TAC std_ss [blast_align_lemma]
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def])
    \\ FULL_SIMP_TAC std_ss [getTag_def,WORD_SUB_ADD,word_mul_n2w]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,getContent_def]
    \\ `((0x10000w * n2w (LENGTH xs) + 0x10w * n2w (n MOD 4096)) >>> 16):word64 =
        n2w (LENGTH xs)` by ALL_TAC THEN1
      (MATCH_MP_TAC get_length_blast \\ cheat)
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg0 := ((0x4w * n2w (LENGTH xs))) |>`
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ FULL_SIMP_TAC (srw_ss()++star_ss) [])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`Data (2w * n2w (LENGTH l))`,`r2`,`r3`,`r4`,`roots`,
                          `heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [word_mul_n2w] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,BlockRep_def]
    \\ `LENGTH l < 2 ** 32` by cheat
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH l < 4611686018427387904` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
      \\ METIS_TAC [abs_ml_inv_Num])
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss []
      \\ `(2 * LENGTH l) < 9223372036854775808` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w,word_mul_n2w]
      \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
      \\ `LENGTH xs = LENGTH l` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `abs_ml_inv xx yy tt rr` MP_TAC
      \\ SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
      \\ ASM_SIMP_TAC (srw_ss()) [bc_value_inv_def,BlockRep_def]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH
      \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [heap_length_APPEND,heap_length_def,MAP,
         SUM,LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
    \\ Q.PAT_ASSUM `xxx (fun2set (vals.memory,vals.memory_domain))` MP_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isBlock x1)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* el *)

val el_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2)]`,`[(x1,r1)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM] |> GEN_ALL

val zHEAP_EL = let
  val th = compose_specs ["mov r0,[r0+2*r1+9]"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isBlock x1 /\ isNumber x2 /\ 0 <= getNumber x2 /\
            getNumber x2 < & LENGTH (getContent x1))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,EL (Num (getNumber x2)) (getContent x1),x2,x3,x4,
                                refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isBlock_def,APPEND,getContent_def]
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNumber_def,APPEND,getNumber_def]
    \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FULL_SIMP_TAC std_ss [LENGTH] \\ `F` by intLib.COOPER_TAC)
    \\ `Num i < LENGTH l` by intLib.COOPER_TAC
    \\ IMP_RES_TAC (el_thm |> Q.INST [`i`|->`Num j`])
    \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
    \\ Q.PAT_ASSUM `heap_el r (Num i) heap = (y,T)` (ASSUME_TAC o GSYM)
    \\ Q.PAT_ASSUM `r1::r2::r3::r4::roots = r::roots2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [CONS_11]
    \\ `?f. bc_value_inv (Block n l) (r1,f,heap)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
      \\ METIS_TAC []) \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [heap_el_def]
    \\ FULL_SIMP_TAC (srw_ss()) [BlockRep_def]
    \\ Cases_on `Num i < LENGTH xs` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC heap_lookup_SPLIT
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,BlockRep_def]
    \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD]
    \\ `r2 = Data (2w * n2w (Num i))` by cheat
    \\ FULL_SIMP_TAC (srw_ss()) [x64_addr_def,WORD_MUL_LSL,w2w_def,word_mul_n2w]
    \\ `(2 * Num i) < 9223372036854775808` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ IMP_RES_TAC LESS_LENGTH \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ Q.MATCH_ASSUM_RENAME_TAC `xs = zs1 ++ z::zs2` []
    \\ FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,one_list_APPEND,one_list_def,
         LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC,
         AC WORD_MULT_ASSOC WORD_MULT_COMM]
    \\ SEP_R_TAC \\ STRIP_TAC THEN1
     (SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,blast_align_lemma]
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def])
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg0 := x64_addr vs.current_heap z |>`
    \\ Tactical.REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ FULL_SIMP_TAC (srw_ss()++star_ss) [])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`z`,`r2`,`r3`,`r4`,`roots`,
                          `heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [word_mul_n2w] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,BlockRep_def]
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `EL (Num i) (zs1 ++ z::zs2) = z` by METIS_TAC [EL_LENGTH]
      \\ FULL_SIMP_TAC std_ss [ADD1,AC ADD_COMM ADD_ASSOC]
      \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ METIS_TAC [el_lemma])
    \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
    \\ cheat)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isBlock x1 /\ isNumber x2 /\ 0 <= getNumber x2 /\
            getNumber x2 < & LENGTH (getContent x1))``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* sub1 *)

val isNumber_EXISTS = prove(
  ``!x. isNumber x <=> ?i. x = Number i``,
  Cases \\ SIMP_TAC (srw_ss()) [isNumber_def]);

fun zHEAP_SUB1 n = let
  val th = if n = ``1:num`` then compose_specs ["sub r0,4"] else
           if n = ``2:num`` then compose_specs ["sub r1,4"] else
           if n = ``3:num`` then compose_specs ["sub r2,4"] else
           if n = ``4:num`` then compose_specs ["sub r3,4"] else fail()
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            small_int (getNumber ^x) /\
            (getNumber ^x <> 0) /\ isNumber ^x)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       if ^n = 1 then Number (getNumber x1 - 1) else x1,
       if ^n = 2 then Number (getNumber x2 - 1) else x2,
       if ^n = 3 then Number (getNumber x3 - 1) else x3,
       if ^n = 4 then Number (getNumber x4 - 1) else x4,
       refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [isNumber_EXISTS]
    \\ FULL_SIMP_TAC std_ss [getNumber_def]
    \\ `if ^n = 1 then (r1 = Data (0x2w * n2w (Num i))) else
        if ^n = 2 then (r2 = Data (0x2w * n2w (Num i))) else
        if ^n = 3 then (r3 = Data (0x2w * n2w (Num i))) else
        if ^n = 4 then (r4 = Data (0x2w * n2w (Num i))) else ARB` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,APPEND,bc_stack_ref_inv_def,EVERY2_def]
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def])
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,WORD_MUL_LSL,w2w_def,word_mul_n2w]
    \\ `(2 * Num i) < dimword (:63)` by ALL_TAC THEN1
      (FULL_SIMP_TAC (srw_ss()) [small_int_def] \\ cheat) (* intLib.COOPER_TAC *)
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,MULT_ASSOC]
    \\ `n2w (4 * Num i) - 0x4w = n2w (4 * Num (i - 1)):word64` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [small_int_def]
      \\ `Num i <> 0` by intLib.COOPER_TAC
      \\ ASM_SIMP_TAC std_ss [word_arith_lemma2] \\ AP_TERM_TAC
      \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with
         <| reg0 := (if ^n = 1 then vals.reg0 - 4w else vals.reg0) ;
            reg1 := (if ^n = 2 then vals.reg1 - 4w else vals.reg1) ;
            reg2 := (if ^n = 3 then vals.reg2 - 4w else vals.reg2) ;
            reg3 := (if ^n = 4 then vals.reg3 - 4w else vals.reg3) |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
      \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC])
    \\ SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
          `if ^n = 1 then Data (n2w (2 * Num (i-1))) else r1`,
          `if ^n = 2 then Data (n2w (2 * Num (i-1))) else r2`,
          `if ^n = 3 then Data (n2w (2 * Num (i-1))) else r3`,
          `if ^n = 4 then Data (n2w (2 * Num (i-1))) else r4`,
          `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,WORD_MUL_LSL,w2w_def,w2n_n2w]
    \\ `(2 * Num (i - 1)) < 9223372036854775808` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def,word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ `i - 1 = & (Num (i - 1))` by
     (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ `Num (i - 1) < 4611686018427387904` by intLib.COOPER_TAC
    \\ METIS_TAC [swap_1_lemmas,abs_ml_inv_Num])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (small_int (getNumber ^x) /\
            (getNumber ^x <> 0) /\ isNumber ^x)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val sub1_1 = zHEAP_SUB1 ``1:num``;
val sub1_2 = zHEAP_SUB1 ``2:num``;
val sub1_3 = zHEAP_SUB1 ``3:num``;
val sub1_4 = zHEAP_SUB1 ``4:num``;


(* compare with zero *)

fun zHEAP_IS_ZERO n = let
  val th = if n = ``1:num`` then spec "test r0,r0" else
           if n = ``2:num`` then spec "test r1,r1" else
           if n = ``3:num`` then spec "test r2,r2" else
           if n = ``4:num`` then spec "test r3,r3" else fail()
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber ^x)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (getNumber ^x = 0)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val reg = ``if ^n = 1 then vals.reg0 else
              if ^n = 2 then vals.reg1 else
              if ^n = 3 then vals.reg2 else
              if ^n = 4 then vals.reg3 else ARB``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(getNumber ^x = 0) <=> (^reg = 0x0w)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [isNumber_EXISTS,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def]
      \\ REVERSE (Cases_on `small_int i`) \\ FULL_SIMP_TAC std_ss [] THEN1
       (`i <> 0` by ALL_TAC THEN1
          (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
        \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [x64_addr_def,heap_vars_ok_def]
        \\ blastLib.BBLAST_TAC)
      \\ Cases_on `i = 0`
      THEN1 (FULL_SIMP_TAC std_ss [x64_addr_def] \\ EVAL_TAC)
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
      \\ `(2 * Num i) < dimword (:63)` by cheat
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
      \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC]
      \\ `(4 * Num i) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber ^x)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val zHEAP_IS_ZERO_1 = zHEAP_IS_ZERO ``1:num``;
val zHEAP_IS_ZERO_2 = zHEAP_IS_ZERO ``2:num``;
val zHEAP_IS_ZERO_3 = zHEAP_IS_ZERO ``3:num``;
val zHEAP_IS_ZERO_4 = zHEAP_IS_ZERO ``4:num``;


(* compare with const *)

fun zHEAP_IS_CONST n k = let
  val k = k |> numSyntax.term_of_int
  val kk = ``^k * 4`` |> EVAL |> concl |> rand
  val kk_str = kk |> numSyntax.int_of_term |> int_to_string
  val th = if n = ``1:num`` then spec ("cmp r0," ^ kk_str) else
           if n = ``2:num`` then spec ("cmp r1," ^ kk_str) else
           if n = ``3:num`` then spec ("cmp r2," ^ kk_str) else
           if n = ``4:num`` then spec ("cmp r3," ^ kk_str) else fail()
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber ^x)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (getNumber ^x = &(^k))) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val reg = ``if ^n = 1 then vals.reg0 else
              if ^n = 2 then vals.reg1 else
              if ^n = 3 then vals.reg2 else
              if ^n = 4 then vals.reg3 else ARB``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(getNumber ^x = &(^k)) <=> (^reg = n2w (^kk))` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [isNumber_EXISTS,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def]
      \\ REVERSE (Cases_on `small_int i`) \\ FULL_SIMP_TAC std_ss [] THEN1
       (`i <> &(^k)` by ALL_TAC THEN1
          (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
        \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [x64_addr_def,heap_vars_ok_def]
        \\ blastLib.BBLAST_TAC)
      \\ Cases_on `i = &(^k)`
      THEN1 (FULL_SIMP_TAC std_ss [x64_addr_def] \\ EVAL_TAC)
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
      \\ `(2 * Num i) < dimword (:63)` by cheat
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
      \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC]
      \\ `(4 * Num i) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber ^x)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val _ = map (zHEAP_IS_CONST ``1:num``) (tl (up_to 10));
val _ = map (zHEAP_IS_CONST ``2:num``) (tl (up_to 10));
val _ = map (zHEAP_IS_CONST ``3:num``) (tl (up_to 10));
val _ = map (zHEAP_IS_CONST ``4:num``) (tl (up_to 10));


(* compare small_ints *)

fun zHEAP_CMP_SMALL_INT (i,j) = let
  val n = i |> numSyntax.term_of_int
  val m = j |> numSyntax.term_of_int
  val rn = i |> (fn n => "r" ^ int_to_string (n - 1))
  val rm = j |> (fn n => "r" ^ int_to_string (n - 1))
  val th = spec ("cmp " ^ rn ^ "," ^ rm)
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val y = ``if ^m = 1:num then x1 else
            if ^m = 2 then x2 else
            if ^m = 3 then x3 else
            if ^m = 4 then x4 else ARB:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            (~small_int (getNumber ^x) ==> small_int (getNumber ^y)) /\
            isNumber ^x /\ isNumber ^y)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (getNumber ^x = getNumber ^y)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val regn = ``if ^n = 1 then vals.reg0 else
               if ^n = 2 then vals.reg1 else
               if ^n = 3 then vals.reg2 else
               if ^n = 4 then vals.reg3 else ARB``
  val regm = ``if ^m = 1 then vals.reg0 else
               if ^m = 2 then vals.reg1 else
               if ^m = 3 then vals.reg2 else
               if ^m = 4 then vals.reg3 else ARB``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(getNumber ^x = getNumber ^y) <=> (^regn = ^regm)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [isNumber_EXISTS,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
      \\ Q.MATCH_ASSUM_RENAME_TAC `xxx = Number j` []
      \\ Cases_on `small_int i` \\ Cases_on `small_int j`
      \\ FULL_SIMP_TAC std_ss [] THEN1
       (`(2 * Num i) < dimword (:63)` by cheat
        \\ `(2 * Num j) < dimword (:63)` by cheat
        \\ FULL_SIMP_TAC std_ss [x64_addr_def]
        \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
        \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
        \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC]
        \\ `(4 * Num i) < 18446744073709551616` by DECIDE_TAC
        \\ `(4 * Num j) < 18446744073709551616` by DECIDE_TAC
        \\ FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
      \\ `i <> j` by (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
      \\ FULL_SIMP_TAC std_ss [x64_addr_def]
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond ((small_int (getNumber ^x) \/ small_int (getNumber ^y)) /\
            isNumber ^x /\ isNumber ^y)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM] \\ Cases_on `small_int (getNumber ^x)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x)
val regs = (up_to 4) |> map (fn n => n+1)
val reg_combs = map (fn n => map (fn m => (n,m)) (n_times n tl (tl (up_to 5)))) regs
  |> flatten

val zHEAP_CMP_SMALL_INT_12 = zHEAP_CMP_SMALL_INT (1,2)
val _ = map zHEAP_CMP_SMALL_INT reg_combs;


(* cmp against bool_to_val F *)

val zHEAP_CMP_FALSE = let
  val th = spec ("cmp r0,2")
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ isBlock x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (x1 = bool_to_val F)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(x1 = bool_to_val F) <=> (vals.reg0 = 2w)` by ALL_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `x1` \\ FULL_SIMP_TAC (srw_ss()) [isBlock_def]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
         bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
    \\ REVERSE (Cases_on `l = []`) \\ FULL_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [x64_addr_def]
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def]
      \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss [x64_addr_def]
    \\ Cases_on `n = 0` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
    \\ SIMP_TAC (srw_ss()) [word_add_n2w,w2w_def,w2n_n2w]
    \\ `(2 * n + 1) < 9223372036854775808 /\
        (2 * (2 * n + 1)) < 18446744073709551616` by cheat
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_MUL_LSL,word_mul_n2w,n2w_11])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isBlock x1)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* swaps *)

fun zHEAP_SWAP (i,j) = let
  val _ = (i < j) orelse fail()
  val n = i |> numSyntax.term_of_int
  val m = j |> numSyntax.term_of_int
  val rn = i |> (fn n => "r" ^ int_to_string (n - 1))
  val rm = j |> (fn n => "r" ^ int_to_string (n - 1))
  val th = spec ("xchg " ^ rm ^ "," ^ rn)
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val y = ``if ^m = 1:num then x1 else
            if ^m = 2 then x2 else
            if ^m = 3 then x3 else
            if ^m = 4 then x4 else ARB:bc_value``
  val target = ``zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       if ^n = 1 then ^y else if ^m = 1 then ^x else x1,
       if ^n = 2 then ^y else if ^m = 2 then ^x else x2,
       if ^n = 3 then ^y else if ^m = 3 then ^x else x3,
       if ^n = 4 then ^y else if ^m = 4 then ^x else x4,
       refs,stack,s,NONE) * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val regn = ``if ^n = 1 then vals.reg0 else
               if ^n = 2 then vals.reg1 else
               if ^n = 3 then vals.reg2 else
               if ^n = 4 then vals.reg3 else ARB``
  val regm = ``if ^m = 1 then vals.reg0 else
               if ^m = 2 then vals.reg1 else
               if ^m = 3 then vals.reg2 else
               if ^m = 4 then vals.reg3 else ARB``
  val rn =   ``if ^n = 1 then r1:63 word heap_address else
               if ^n = 2 then r2 else
               if ^n = 3 then r3 else
               if ^n = 4 then r4 else ARB``
  val rm =   ``if ^m = 1 then r1:63 word heap_address else
               if ^m = 2 then r2 else
               if ^m = 3 then r3 else
               if ^m = 4 then r4 else ARB``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with
        <| reg0 := if ^n = 1 then ^regm else if ^m = 1 then ^regn else vals.reg0 ;
           reg1 := if ^n = 2 then ^regm else if ^m = 2 then ^regn else vals.reg1 ;
           reg2 := if ^n = 3 then ^regm else if ^m = 3 then ^regn else vals.reg2 ;
           reg3 := if ^n = 4 then ^regm else if ^m = 4 then ^regn else vals.reg3 |>`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
          `if ^n = 1 then ^rm else if ^m = 1 then ^rn else r1`,
          `if ^n = 2 then ^rm else if ^m = 2 then ^rn else r2`,
          `if ^n = 3 then ^rm else if ^m = 3 then ^rn else r3`,
          `if ^n = 4 then ^rm else if ^m = 4 then ^rn else r4`,
          `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `abs_ml_inv xx yy tt rr` MP_TAC
    \\ MATCH_MP_TAC move_lemma
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

val _ = map zHEAP_SWAP reg_combs;


(* isBlock *)

val (x64_is_block_cert, x64_is_block_def) = x64_decompile_no_status "x64_is_block" `
  test r0, 1
  jne PTR
  mov r15,r0
  not r15
  test r15,2
  jmp EXIT
PTR:
  mov r15,[r0+1]
  test r15,7
EXIT: `;

val FST_IF = prove(
  ``!b. FST (if b then (x,y) else (x2,y2)) = if b then x else x2``,
  Cases \\ SIMP_TAC std_ss []);

val SND_IF = prove(
  ``!b. SND (if b then (x,y) else (x2,y2)) = if b then y else y2``,
  Cases \\ SIMP_TAC std_ss []);

val PULL_IMP_EXISTS = METIS_PROVE []
  ``(P ==> ?x. Q x) <=> ?x. P ==> Q x``

val heap_inv_ignore_reg15 = prove(
  ``heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) (vals with reg15 := w) =
    heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals``,
  SIMP_TAC (srw_ss()) [heap_inv_def]);

val zHEAP_isBlock = let
  val th =
    x64_is_block_cert
    |> SIMP_RULE std_ss [LET_DEF,x64_is_block_def]
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
    |> SIMP_RULE std_ss [FST_IF,SND_IF]
    |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
    |> UNDISCH
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``zPC p * ~zS * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            canCompare x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,
       refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (isBlock x1)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = METIS_PROVE []
    ``!p3. (p3 ==> p2) /\ p1 /\ p3 ==> p1 /\ p2``
  val blast_lemma = blastLib.BBLAST_PROVE
    ``(0x1w && w << 1) = 0x0w:word64``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ GEN_TAC
    \\ FULL_SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.PAT_ABBREV_TAC `pat = if vals.reg0 && 0x1w = 0x0w
                               then ~vals.reg0 else yy`
    \\ Q.EXISTS_TAC `vals with reg15 := pat`
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_ignore_reg15,SEP_CLAUSES,zVALS_def]
    \\ STRIP_TAC \\ MATCH_MP_TAC lemma
    \\ Q.EXISTS_TAC `
        (if 0x1w && vals.reg0 = 0x0w then SOME (0x2w && ~vals.reg0 = 0x0w)
         else SOME (0x7w && vals.memory (vals.reg0 + 0x1w) = 0x0w)) =
        SOME (isBlock x1)`
    \\ CONJ_TAC THEN1 FULL_SIMP_TAC (std_ss++star_ss) []
    \\ UNABBREV_ALL_TAC
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,APPEND,abs_ml_inv_def,
         bc_stack_ref_inv_def,EVERY2_def]
    \\ Q.PAT_ASSUM `bc_value_inv x1 (r1,f,heap)` ASSUME_TAC
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [canCompare_def,isBlock_def]
    THEN1 (Cases_on `small_int i`
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def,blast_lemma]
      THEN1 blastLib.BBLAST_TAC \\ SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ `(0x1w && vs.current_heap + n2w ptr << 3 - 0x1w) <> 0x0w /\
          (0x7w && vs.current_heap + n2w ptr << 3 = 0x0w)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
        \\ blastLib.BBLAST_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC heap_lookup_SPLIT
      \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,WORD_MUL_LSL,
           x64_el_def,DataOnly_def,x64_payload_def,LET_DEF,word_mul_n2w]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ Cases_on `i < 0:int` \\ ASM_SIMP_TAC std_ss [b2w_def]
      \\ blastLib.BBLAST_TAC)
    THEN1 (Cases_on `l = []`
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def,blast_lemma]
      THEN1 blastLib.BBLAST_TAC \\ SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ `(0x1w && vs.current_heap + n2w ptr << 3 - 0x1w) <> 0x0w /\
          (0x7w && vs.current_heap + n2w ptr << 3 = 0x0w)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
        \\ blastLib.BBLAST_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC heap_lookup_SPLIT
      \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,WORD_MUL_LSL,
           x64_el_def,BlockRep_def,x64_payload_def,LET_DEF,word_mul_n2w]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ blastLib.BBLAST_TAC)
    THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def,blast_lemma]
      \\ `(0x1w && vs.current_heap + n2w (f ' n) << 3 - 0x1w) <> 0x0w /\
          (0x7w && vs.current_heap + n2w (f ' n) << 3 = 0x0w)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
        \\ blastLib.BBLAST_TAC)
      \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ `reachable_refs (RefPtr n::x2::x3::x4::stack) refs n` by ALL_TAC THEN1
       (SIMP_TAC std_ss [reachable_refs_def]
        \\ FULL_SIMP_TAC std_ss [MEM] \\ Q.EXISTS_TAC `RefPtr n`
        \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,RTC_REFL])
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def]
      \\ IMP_RES_TAC heap_lookup_SPLIT
      \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,WORD_MUL_LSL,
           x64_el_def,RefBlock_def,x64_payload_def,LET_DEF,word_mul_n2w]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ EVAL_TAC))
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * zPC p *
      cond (canCompare x1) * ~zS``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end


(* isNumber *)

val (x64_is_number_cert, x64_is_number_def) = x64_decompile_no_status "x64_is_number" `
  test r0, 1
  jne PTR
  test r0,3
  jmp EXIT
PTR:
  mov r15,[r0+1]
  not r15
  test r15,2
EXIT: `;

val zHEAP_isNumber = let
  val th =
    x64_is_number_cert
    |> SIMP_RULE std_ss [LET_DEF,x64_is_number_def]
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
    |> SIMP_RULE std_ss [FST_IF,SND_IF]
    |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
    |> UNDISCH
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``zPC p * ~zS * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            canCompare x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,
       refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (isNumber x1)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = METIS_PROVE []
    ``!p3. (p3 ==> p2) /\ p1 /\ p3 ==> p1 /\ p2``
  val blast_lemma = blastLib.BBLAST_PROVE
    ``(0x1w && w << 1) = 0x0w:word64``
  val blast_lemma2 = blastLib.BBLAST_PROVE
    ``((0x2w && ~w) <> 0x0w:word64) <=> ~(w ' 1)``
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ GEN_TAC
    \\ FULL_SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.PAT_ABBREV_TAC `pat = if vals.reg0 && 0x1w = 0x0w
                               then vals.reg15 else yy`
    \\ Q.EXISTS_TAC `vals with reg15 := pat`
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_ignore_reg15,SEP_CLAUSES,zVALS_def]
    \\ STRIP_TAC \\ MATCH_MP_TAC lemma
    \\ Q.EXISTS_TAC `
        (if 0x1w && vals.reg0 = 0x0w then SOME (0x3w && vals.reg0 = 0x0w)
         else SOME (0x2w && (~vals.memory (vals.reg0 + 0x1w)) = 0x0w)) =
        SOME (isNumber x1)`
    \\ CONJ_TAC THEN1 FULL_SIMP_TAC (std_ss++star_ss) []
    \\ UNABBREV_ALL_TAC
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,APPEND,abs_ml_inv_def,
         bc_stack_ref_inv_def,EVERY2_def]
    \\ Q.PAT_ASSUM `bc_value_inv x1 (r1,f,heap)` ASSUME_TAC
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [canCompare_def,isNumber_def]
    THEN1 (Cases_on `small_int i`
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def,blast_lemma]
      THEN1 blastLib.BBLAST_TAC \\ SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ `(0x1w && vs.current_heap + n2w ptr << 3 - 0x1w) <> 0x0w /\
          (0x7w && vs.current_heap + n2w ptr << 3 = 0x0w)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
        \\ blastLib.BBLAST_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC heap_lookup_SPLIT
      \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,WORD_MUL_LSL,
           x64_el_def,DataOnly_def,x64_payload_def,LET_DEF,word_mul_n2w]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ Cases_on `i < 0:int` \\ ASM_SIMP_TAC std_ss [b2w_def]
      \\ blastLib.BBLAST_TAC)
    THEN1 (Cases_on `l = []`
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def,blast_lemma]
      THEN1 blastLib.BBLAST_TAC \\ SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ `(0x1w && vs.current_heap + n2w ptr << 3 - 0x1w) <> 0x0w /\
          (0x7w && vs.current_heap + n2w ptr << 3 = 0x0w)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
        \\ blastLib.BBLAST_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC heap_lookup_SPLIT
      \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,WORD_MUL_LSL,
           x64_el_def,BlockRep_def,x64_payload_def,LET_DEF,word_mul_n2w]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ SIMP_TAC std_ss [blast_lemma2] \\ blastLib.BBLAST_TAC)
    THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def,blast_lemma]
      \\ `(0x1w && vs.current_heap + n2w (f ' n) << 3 - 0x1w) <> 0x0w /\
          (0x7w && vs.current_heap + n2w (f ' n) << 3 = 0x0w)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
        \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
        \\ blastLib.BBLAST_TAC)
      \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ `reachable_refs (RefPtr n::x2::x3::x4::stack) refs n` by ALL_TAC THEN1
       (SIMP_TAC std_ss [reachable_refs_def]
        \\ FULL_SIMP_TAC std_ss [MEM] \\ Q.EXISTS_TAC `RefPtr n`
        \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,RTC_REFL])
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def]
      \\ IMP_RES_TAC heap_lookup_SPLIT
      \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,WORD_MUL_LSL,
           x64_el_def,RefBlock_def,x64_payload_def,LET_DEF,word_mul_n2w]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ EVAL_TAC))
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * zPC p *
      cond (canCompare x1) * ~zS``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end


(* isSmall *)

val isSmall_def = Define `
  (isSmall (Number i) = small_int i) /\
  (isSmall (Block tag l) = (l = [])) /\
  (isSmall _ = F)`;

val zHEAP_isSmall = let
  val th = spec "test r0,1"
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``zPC p * ~zS * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            canCompare x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,
       refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (isSmall x1)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ GEN_TAC
    \\ FULL_SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_CLAUSES,zVALS_def]
    \\ REPEAT STRIP_TAC
    \\ `isSmall x1 = (0x1w && vals.reg0 = 0x0w)` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `x1` \\ FULL_SIMP_TAC (srw_ss()) [canCompare_def,isSmall_def]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,
         bc_stack_ref_inv_def,APPEND,EVERY2_def]
    THEN1 (Cases_on `small_int i`
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def]
      THEN1 blastLib.BBLAST_TAC
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
      \\ blastLib.BBLAST_TAC)
    THEN1 (Cases_on `l = []`
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def]
      THEN1 blastLib.BBLAST_TAC \\ SIMP_TAC std_ss [WORD_SUB_ADD]
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
      \\ blastLib.BBLAST_TAC)
    THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def]
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def,WORD_MUL_LSL]
      \\ blastLib.BBLAST_TAC))
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * zPC p *
      cond (canCompare x1) * ~zS``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end


(* explode single Block *)

val (res,push_els_loop_def,push_els_loop_pre_def) = x64_compile `
  push_els_loop (x1,x2,x3,x4:bc_value,stack) =
    if getNumber x2 = 0 then (x1,x2,x3,x4,stack) else
      let x2 = Number (getNumber x2 - 1) in
      let x1 = x3 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in
      let stack = x1::stack in
      let x1 = Number 1 in
      let stack = x1::stack in
        push_els_loop (x1,x2,x3,x4,stack)`

val (push_els_cert,push_els_def,push_els_pre_def) = x64_compile `
  push_els (x1:bc_value,x4,stack) =
    let x3 = x1 in
    let x1 = Number (&LENGTH (getContent x1)) in
    let x2 = x1 in
    let (x1,x2,x3,x4,stack) = push_els_loop (x1,x2,x3,x4,stack) in
    let x1 = x2 in
      (x1,x2,x3,x4,stack)`

val TAKE_SUC = prove(
  ``!k l.
      k + 1 <= LENGTH l ==>
      (TAKE (k + 1) l = TAKE k l ++ [EL k l])``,
  Induct THEN1 (Cases_on `l` \\ EVAL_TAC) \\ Cases_on `l`
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [ADD1])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,rich_listTheory.TAKE,APPEND,CONS_11,EL,HD,TL]);

val push_els_loop_thm = prove(
  ``!k stack x1.
      k <= LENGTH l /\ small_int (& k) ==>
      ?x1i. push_els_loop_pre (x1,Number (& k),Block tag l,x4,stack) /\
           (push_els_loop (x1,Number (& k),Block tag l,x4,stack) =
             (x1i,Number 0, Block tag l,x4,
              FLAT (MAP (\x. [Number 1; x]) (TAKE k l)) ++ stack))``,
  Induct \\ SIMP_TAC std_ss [TAKE_0,MAP,FLAT,APPEND]
  \\ ONCE_REWRITE_TAC [push_els_loop_def,push_els_loop_pre_def]
  \\ FULL_SIMP_TAC std_ss [getNumber_def,isNumber_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [integerTheory.INT_EQ_CALCULATE,ADD1]
  \\ REPEAT STRIP_TAC
  \\ `(&(k + 1) - 1 = & k) /\ 0 <= &k /\ k <= LENGTH l /\
      small_int (&k) /\ k < LENGTH l /\
      &k < &LENGTH l /\ (Num (& k) = k)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss [getContent_def,isBlock_def]
  \\ IMP_RES_TAC TAKE_SUC
  \\ FULL_SIMP_TAC std_ss [MAP_APPEND,FLAT_APPEND,MAP,FLAT,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val push_els_thm = prove(
  ``isBlock x1 /\ small_int (& (LENGTH (getContent x1))) ==>
    push_els_pre (x1,x4,stack) /\
    (push_els (x1,x4,stack) =
       (Number 0,Number 0,x1,x4,
        FLAT (MAP (\x. [Number 1; x]) (getContent x1)) ++ stack))``,
  Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isBlock_def,getContent_def]
  \\ FULL_SIMP_TAC std_ss [push_els_def,push_els_pre_def,LET_DEF,
       isBlock_def,getContent_def]
  \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC (GEN_ALL push_els_loop_thm)
  \\ SEP_I_TAC "push_els_loop"
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TAKE_LENGTH_ID]);

val Block_size_small_int = prove(
  ``!x1. isBlock x1 /\ heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals ==>
         small_int (&LENGTH (getContent x1)) /\ small_int (& (getTag x1))``,
  Cases \\ SIMP_TAC std_ss [isBlock_def,getContent_def,getTag_def]
  \\ SIMP_TAC std_ss [heap_inv_def] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,APPEND,
       EVERY2_def,bc_value_inv_def]
  \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss [LENGTH] THEN1 cheat
  \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [BlockRep_def,x64_heap_APPEND,
       x64_el_def,x64_payload_def,LET_DEF,cond_STAR,x64_heap_def]
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [small_int_def]
  \\ STRIP_TAC THEN1 intLib.COOPER_TAC \\ cheat);

val zHEAP_EXPLODE_BLOCK = let
  val tm = push_els_thm |> concl |> dest_imp |> fst
  val th = DISCH tm push_els_cert
           |> SIMP_RULE std_ss [push_els_thm,LET_DEF,SEP_CLAUSES]
           |> SIMP_RULE std_ss [GSYM SPEC_MOVE_COND]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) *
      cond (isBlock x1))``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_IMP_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,cond_STAR,SEP_CLAUSES,
         SEP_EXISTS_THM,STAR_ASSOC] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC Block_size_small_int \\ ASM_SIMP_TAC std_ss [])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;

(* explode two Blocks *)

val (_,push_els2_loop_def,push_els2_loop_pre_def) = x64_compile `
  push_els2_loop (x1,x2,x3,x4:bc_value,stack) =
    if getNumber x2 = 0 then (x1,x2,x3,x4,stack) else
      let x2 = Number (getNumber x2 - 1) in
      let x1 = x3 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in
      let stack = x1::stack in
      let x1 = x4 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in
      let stack = x1::stack in
      let x1 = Number 1 in
      let stack = x1::stack in
        push_els2_loop (x1,x2,x3,x4,stack)`

val (push_els2_cert,push_els2_def,push_els2_pre_def) = x64_compile `
  push_els2 (x1:bc_value,x4,stack) =
    let x3 = x1 in
    let x1 = Number (&LENGTH (getContent x1)) in
    let x2 = x1 in
    let (x1,x2,x3,x4,stack) = push_els2_loop (x1,x2,x3,x4,stack) in
    let x1 = x2 in
      (x1,x2,x3,x4,stack)`

val TAKE_SUC2 = prove(
  ``!k l.
      k + 1 <= LENGTH l /\ (LENGTH l2 = LENGTH l) ==>
      (TAKE (k + 1) (ZIP (l,l2)) = TAKE k (ZIP (l,l2)) ++ [(EL k l,EL k l2)])``,
  REPEAT STRIP_TAC
  \\ `k + 1 <= LENGTH (ZIP(l,l2))` by METIS_TAC [LENGTH_ZIP]
  \\ IMP_RES_TAC TAKE_SUC
  \\ FULL_SIMP_TAC std_ss [] \\ AP_TERM_TAC
  \\ `k < LENGTH l` by cheat
  \\ SIMP_TAC std_ss [CONS_11]
  \\ MATCH_MP_TAC EL_ZIP
  \\ FULL_SIMP_TAC std_ss []);

val push_els2_loop_thm = prove(
  ``!k stack x1.
      k <= LENGTH l1 /\ small_int (& k) /\ (LENGTH l2 = LENGTH l1) ==>
      ?x1i. push_els2_loop_pre (x1,Number (& k),Block tag1 l1,Block tag2 l2,stack) /\
           (push_els2_loop (x1,Number (& k),Block tag1 l1,Block tag2 l2,stack) =
             (x1i,Number 0, Block tag1 l1,Block tag2 l2,
              FLAT (MAP (\(x,y). [Number 1; y; x])
                (TAKE k (ZIP(l1,l2)))) ++ stack))``,
  Induct \\ SIMP_TAC std_ss [TAKE_0,MAP,FLAT,APPEND]
  \\ ONCE_REWRITE_TAC [push_els2_loop_def,push_els2_loop_pre_def]
  \\ FULL_SIMP_TAC std_ss [getNumber_def,isNumber_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [integerTheory.INT_EQ_CALCULATE,ADD1]
  \\ REPEAT STRIP_TAC
  \\ `(&(k + 1) - 1 = & k) /\ 0 <= &k /\ k <= LENGTH l1 /\
      small_int (&k) /\ k < LENGTH l1 /\
      &k < &LENGTH l1 /\ (Num (& k) = k)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss [getContent_def,isBlock_def]
  \\ `k + 1 <= LENGTH (ZIP(l1,l2))` by METIS_TAC [LENGTH_ZIP]
  \\ IMP_RES_TAC TAKE_SUC2
  \\ FULL_SIMP_TAC std_ss [MAP_APPEND,FLAT_APPEND,MAP,FLAT,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val explode_result_def = Define `
  explode_result (x1,x4,stack) =
    (Number 0,Number 0,x1,x4,
        FLAT (MAP (\(x,y). [Number 1; y; x])
                ((ZIP(getContent x1,getContent x4)))) ++ stack)`;

val push_els2_thm = prove(
  ``isBlock x1 /\ isBlock x4 /\ small_int (& (LENGTH (getContent x1))) /\
    (LENGTH (getContent x1) = LENGTH (getContent x4)) ==>
    push_els2_pre (x1,x4,stack) /\
    (push_els2 (x1,x4,stack) = explode_result (x1,x4,stack))``,
  Cases_on `x1` \\ Cases_on `x4`
  \\ FULL_SIMP_TAC std_ss [isBlock_def,getContent_def,explode_result_def]
  \\ FULL_SIMP_TAC std_ss [push_els2_def,push_els2_pre_def,LET_DEF,
       isBlock_def,getContent_def]
  \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC (GEN_ALL push_els2_loop_thm)
  \\ SEP_I_TAC "push_els2_loop"
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ `LENGTH l' = LENGTH (ZIP (l,l'))` by METIS_TAC [LENGTH_ZIP]
  \\ FULL_SIMP_TAC std_ss [TAKE_LENGTH_ID]);

val zHEAP_EXPLODE_TWO_BLOCKS = let
  val tm = push_els2_thm |> concl |> dest_imp |> fst
  val th = DISCH tm push_els2_cert
           |> SIMP_RULE std_ss [push_els2_thm,SEP_CLAUSES]
           |> SIMP_RULE std_ss [GSYM SPEC_MOVE_COND]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) *
      cond (isBlock x1 /\ isBlock x4 /\
            (LENGTH (getContent x1) = LENGTH (getContent x4))))``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_IMP_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,cond_STAR,SEP_CLAUSES,
         SEP_EXISTS_THM,STAR_ASSOC] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC Block_size_small_int \\ METIS_TAC [])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* RefPtr equality *)

val RefPtrEq_def = Define `
  RefPtrEq x (y:bc_value) = (x = y)`;

val heap_lookup_IMP_heap_length = prove(
  ``(heap_lookup n heap = SOME x) ==>
    n <= heap_length heap``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def,heap_length_APPEND]);

val zHEAP_RefPtrEq = let
  val th = spec "cmp r0,r1"
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``zPC p * ~zS * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isRefPtr x1 /\ isRefPtr x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,
       refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (RefPtrEq x1 x2)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isRefPtr_def]
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isRefPtr_def]
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ GEN_TAC
    \\ FULL_SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_CLAUSES,zVALS_def,RefPtrEq_def]
    \\ REPEAT STRIP_TAC
    \\ `(n = n') = (vals.reg0 = vals.reg1)` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,
         bc_stack_ref_inv_def,APPEND,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL,word_sub_def]
    \\ FULL_SIMP_TAC std_ss [INJ_DEF]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (`f ' n = f ' n'` by ALL_TAC) THEN1 RES_TAC
    \\ `reachable_refs (RefPtr n::RefPtr n'::x3::x4::stack) refs n`  by
     (SIMP_TAC std_ss [reachable_refs_def] \\ Q.EXISTS_TAC `RefPtr n`
      \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,RTC_REFL])
    \\ `reachable_refs (RefPtr n::RefPtr n'::x3::x4::stack) refs n'`  by
     (SIMP_TAC std_ss [reachable_refs_def] \\ Q.EXISTS_TAC `RefPtr n'`
      \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,RTC_REFL])
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def,heap_ok_def,
         WORD_MUL_LSL,word_mul_n2w,n2w_11]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ `f ' n <= cs.heap_limit /\
        f ' n' <= cs.heap_limit` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [isSomeDataElement_def]
      \\ IMP_RES_TAC heap_lookup_IMP_heap_length \\ DECIDE_TAC)
    \\ `f ' n' <= cs.heap_limit` by cheat
    \\ `(8 * f ' n) < 18446744073709551616` by DECIDE_TAC
    \\ `(8 * f ' n') < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ DECIDE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * zPC p *
      cond (isRefPtr x1 /\ isRefPtr x2) * ~zS``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = x64_codegenLib.add_compiled [th];
  in th end


(* block length comparison *)

val (get_lengths_cert,get_lengths_def,get_lengths_pre_def) = x64_compile `
  get_lengths (x1,x2) =
    let x1 = Number (&LENGTH (getContent x1)) in
    let (x1,x2) = (x2,x1) in
    let x1 = Number (&LENGTH (getContent x1)) in
      (x1,x2)`

val zHEAP_LENGTH_COMPARE = let
  val th = get_lengths_cert
    |> SIMP_RULE std_ss [get_lengths_def,get_lengths_pre_def,LET_DEF]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_CMP_SMALL_INT_12]
  val th = th |> SIMP_RULE std_ss [isNumber_def,getNumber_def,
                   integerTheory.INT_EQ_CALCULATE,Once EQ_SYM_EQ]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) *
      cond (isBlock x1 /\ isBlock x2))``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_IMP_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,cond_STAR,SEP_CLAUSES,
         SEP_EXISTS_THM,STAR_ASSOC] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC Block_size_small_int \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_PUSH2,th,zHEAP_POP2,zHEAP_POP1]
  val th = th |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* block tag comparison *)

val (get_tags_cert,get_tags_def,get_tags_pre_def) = x64_compile `
  get_lengths (x1,x2) =
    let x1 = Number (& (getTag x1)) in
    let (x1,x2) = (x2,x1) in
    let x1 = Number (& (getTag x1)) in
      (x1,x2)`

val zHEAP_TAG_COMPARE = let
  val th = get_tags_cert
    |> SIMP_RULE std_ss [get_tags_def,get_tags_pre_def,LET_DEF]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_CMP_SMALL_INT_12]
  val th = th |> SIMP_RULE std_ss [isNumber_def,getNumber_def,
                   integerTheory.INT_EQ_CALCULATE,Once EQ_SYM_EQ]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) *
      cond (isBlock x1 /\ isBlock x2))``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_IMP_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,cond_STAR,SEP_CLAUSES,
         SEP_EXISTS_THM,STAR_ASSOC] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC Block_size_small_int \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_PUSH2,th,zHEAP_POP2,zHEAP_POP1]
  val th = th |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* number equality *)

val (_,array_eq_def,array_eq_pre_def) = x64_compile `
  array_eq (r0:word64,r14:word64,r15:word64,dm:word64 set,m:word64->word64) =
    if r0 = 0w then let r0 = 4w:word64 in (r0,r14,r15,dm,m) else
      let r12 = m r14 in
      let r13 = m r15 in
        if r12 <> r13 then
          let r0 = 0w in (r0,r14,r15,dm,m)
        else
          let r0 = r0 - 1w in
          let r14 = r14 + 8w in
          let r15 = r15 + 8w in
            array_eq (r0,r14,r15,dm,m)`

val (num_eq_cert,num_eq_def,num_eq_pre_def) = x64_compile `
  num_eq (r0:word64,r1,r12:word64,r13,dm:word64 set,m:word64->word64,ss) =
    let r14 = r0 + 1w in
    let r15 = r1 + 1w in
    let ss = r12::ss in
    let ss = r13::ss in
    let r12 = m r14 in
    let r13 = m r15 in
      if r12 <> r13 then
        let (r13,ss) = (HD ss, TL ss) in
        let (r12,ss) = (HD ss, TL ss) in
        let r0 = 0w in
          (r0,r1,r12,r13,dm,m,ss)
      else
        let r0 = r12 >>> 16 in
        let r14 = r14 + 8w in
        let r15 = r15 + 8w in
        let (r0,r14,r15,dm,m) = array_eq (r0,r14,r15,dm,m) in
        let (r13,ss) = (HD ss, TL ss) in
        let (r12,ss) = (HD ss, TL ss) in
          (r0,r1,r12,r13,dm,m,ss)`

val array_eq_thm = prove(
  ``!xs ys a b p1 p2.
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword(:64) /\
      (a && 0x7w = 0x0w) /\ (b && 0x7w = 0x0w) /\
      (one_list a xs * p1) (fun2set (m,dm)) /\
      (one_list b ys * p2) (fun2set (m,dm)) ==>
      ?r14' r15'.
        array_eq_pre (n2w (LENGTH xs), a, b, dm, m) /\
        (array_eq (n2w (LENGTH xs), a, b, dm, m) =
          (if xs = ys then 4w else 0w, r14', r15', dm, m))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [array_eq_def,array_eq_pre_def]
  \\ SIMP_TAC std_ss [CONS_11,n2w_11,ZERO_LT_dimword,LET_DEF,one_list_def]
  \\ REPEAT STRIP_TAC
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h' = h` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SEP_I_TAC "array_eq"
  \\ `LENGTH xs < dimword (:64)` by DECIDE_TAC
  \\ SEP_F_TAC \\ REPEAT STRIP_TAC
  \\ SEP_F_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [blast_align_lemma]);

val heap_lookup_DataOnly_IMP = prove(
  ``(x64_heap vs.current_heap heap vs.current_heap vs.current_heap *
        one_list_exists vs.other_heap cs.heap_limit * x64_store cs vs)
         (fun2set (vals.memory,vals.memory_domain)) /\
    (heap_lookup ptr heap = SOME (DataOnly x y)) ==>
    ?pp t1 t2. (x64_el (vs.current_heap + n2w (8 * ptr)) (DataOnly x y) t1 t2 * pp)
         (fun2set (vals.memory,vals.memory_domain))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,SEP_CLAUSES]
  \\ METIS_TAC [STAR_COMM,STAR_ASSOC]);

val SHIFT_LEMMA = prove(
  ``(y << 16 + 0x2w + b2w b1 = x << 16 + 0x2w + b2w b2) /\
    x <+ n2w (2**48) /\ y <+ n2w (2**48) ==>
    (x = y:word64) /\ (b1 = b2)``,
  Cases_on `b1` \\ Cases_on `b2` \\ FULL_SIMP_TAC std_ss [b2w_def]
  \\ blastLib.BBLAST_TAC) |> SIMP_RULE std_ss [];

val SHIFT_SHIFT_LEMMA = prove(
  ``w <+ n2w (2**48) ==> (((w:word64) << 16 + 0x2w + b2w b) >>> 16 = w)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [b2w_def] \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [];

val mw_thm = prove(
  ``mw = n2mw``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ HO_MATCH_MP_TAC mw_ind
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_def,multiwordTheory.n2mw_def]
  \\ SRW_TAC [] []);

val zHEAP_BigNumEq = let
  val th = num_eq_cert
  val pc = get_pc th
  val side = ``isNumber x1 /\ ~isSmall x1 /\ isNumber x2 /\ ~isSmall x2``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            ^side)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,Number (if getNumber x2 = getNumber x1 then 1 else 0),
               x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ `?r0 r1 r12 r13 dm m ss.
          num_eq
            (vals.reg0,vals.reg1,vals.reg12,vals.reg13,
             vals.memory_domain,vals.memory,vals.stack) =
          (r0,r1,r12,r13,dm,m,ss)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [PULL_EXISTS,PULL_FORALL] \\ NTAC 4 STRIP_TAC
    \\ SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.EXISTS_TAC `vals with <| reg0 := r0 ; reg1 := r1 ;
         reg12 := r12 ; reg13 := r13 ; reg14 := x' ; reg15 := x ;
         memory := m ; memory_domain := dm ; stack := ss |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ SIMP_TAC (srw_ss()++star_ss) [zVALS_def]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b1 /\ b3 ==> (b1 /\ (b2 ==> b3))``)
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isNumber_def]
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNumber_def]
    \\ FULL_SIMP_TAC std_ss [getNumber_def,isSmall_def]
    \\ Q.PAT_ASSUM `xx = yy` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`Data (if i = i' then 2w else 0w)`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss []
    \\ `abs_ml_inv (Number (if i' = i then 1 else 0)::Number i'::x3::x4::stack)
         refs (Data (if i = i' then 0x2w else 0x0w)::r2::r3::r4::roots,heap,a,sp)
          cs.heap_limit` by ALL_TAC THEN1
     (Cases_on `i' = i` \\ FULL_SIMP_TAC std_ss []
      \\ TRY (MATCH_MP_TAC (abs_ml_inv_Num |> SPEC_ALL |> Q.INST [`n`|->`1`]
                      |> SIMP_RULE std_ss [word_mul_n2w] |> GEN_ALL))
      \\ TRY (MATCH_MP_TAC (abs_ml_inv_Num |> SPEC_ALL |> Q.INST [`n`|->`0`]
                      |> SIMP_RULE std_ss [word_mul_n2w] |> GEN_ALL))
      \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
    \\ IMP_RES_TAC heap_lookup_DataOnly_IMP \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [DataOnly_def,x64_el_def,x64_payload_def,LET_DEF]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,x64_addr_def]
    \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
    \\ SIMP_TAC std_ss [num_eq_pre_def,num_eq_def,LET_DEF]
    \\ SIMP_TAC std_ss [HD,TL,NOT_CONS_NIL,WORD_SUB_ADD]
    \\ Cases_on `vals.memory (vs.current_heap + n2w (8 * ptr)) <>
                 vals.memory (vs.current_heap + n2w (8 * ptr'))`
    \\ FULL_SIMP_TAC std_ss [] THEN1
     (SEP_R_TAC \\ SIMP_TAC std_ss [blast_align_lemma,GSYM word_mul_n2w]
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ REPEAT STRIP_TAC
      \\ SRW_TAC [] [])
    \\ SEP_R_TAC \\ SIMP_TAC std_ss [blast_align_lemma,GSYM word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def]
    \\ Q.ABBREV_TAC `i1 = mw (Num (ABS i)):word64 list`
    \\ Q.ABBREV_TAC `i2 = mw (Num (ABS i')):word64 list`
    \\ `n2w (LENGTH i1) <+ 0x1000000000000w:word64 /\
        n2w (LENGTH i2) <+ 0x1000000000000w:word64` by
     (`LENGTH i1 < 18446744073709551616` by DECIDE_TAC
      \\ `LENGTH i2 < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
    \\ `(LENGTH i1 = LENGTH i2) /\ ((i' < 0) = (i < 0))` by ALL_TAC THEN1
     (IMP_RES_TAC SHIFT_LEMMA \\ REPEAT (Q.PAT_ASSUM `!xx.bb` (K ALL_TAC))
      \\ `LENGTH i1 < 18446744073709551616` by DECIDE_TAC
      \\ `LENGTH i2 < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
    \\ FULL_SIMP_TAC std_ss []
    \\ `(n2w (LENGTH i2) << 16 + 0x2w + b2w (i < 0)) >>> 16 =
        n2w (LENGTH i2):word64` by ALL_TAC THEN1
     (MATCH_MP_TAC SHIFT_SHIFT_LEMMA
      \\ `LENGTH i2 < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (array_eq_thm |> GEN_ALL)
    \\ Q.PAT_ASSUM `LENGTH i1 = LENGTH i2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_I_TAC "array_eq"
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `i2:word64 list`)
    \\ POP_ASSUM (MP_TAC o Q.SPECL [
         `one (vs.current_heap + n2w (8 * ptr),
            n2w (LENGTH (i1:word64 list)) << 16 + 0x2w + b2w (i < 0)) * pp'`,
         `one (vs.current_heap + n2w (8 * ptr'),
            n2w (LENGTH (i2:word64 list)) << 16 + 0x2w + b2w (i < 0)) * pp`])
    \\ MATCH_MP_TAC IMP_IMP \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (std_ss++star_ss) [blast_align_lemma,GSYM word_mul_n2w,
        AC WORD_ADD_COMM WORD_ADD_ASSOC]
      \\ SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ UNABBREV_ALL_TAC
    \\ FULL_SIMP_TAC std_ss [mw_thm,multiwordTheory.n2mw_11]
    \\ `(Num (ABS i) = Num (ABS i')) = (i = i')` by intLib.COOPER_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^side)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC,SEP_IMP_REFL])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* recursive equality *)

val (pop_all_cert,pop_all_def,pop_all_pre_def) = x64_compile `
  pop_all (stack:bc_value list) =
    let (x2,stack) = (HD stack, TL stack) in
      if getNumber x2 = 0 then
        (x2,stack)
      else
        let (x2,stack) = (HD stack, TL stack) in
        let (x2,stack) = (HD stack, TL stack) in
          pop_all stack`

val (_,equal_loop_def,equal_loop_pre_def) = x64_compile `
  equal_loop (x1:bc_value,x2,x3,x4,stack:bc_value list) =
    let (x1,stack) = (HD stack, TL stack) in
      if getNumber x1 = 0 then
        let x1 = bool_to_val T in
          (x1,x2,x3,x4,stack)
      else
        let (x2,stack) = (HD stack, TL stack) in
        let (x1,stack) = (HD stack, TL stack) in
          if isNumber x1 then (* number case *)
            let (x1,x2) = (x2,x1) in
            if ~(isNumber x1) then
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack)
            else
              if isSmall x1 then
                if getNumber x1 = getNumber x2 then
                  equal_loop (x1,x2,x3,x4,stack)
                else
                  let x1 = bool_to_val F in
                  let (x2,stack) = pop_all stack in
                    (x1,x2,x3,x4,stack)
              else
              let (x1,x2) = (x2,x1) in
              if isSmall x1 then
                let x1 = bool_to_val F in
                let (x2,stack) = pop_all stack in
                  (x1,x2,x3,x4,stack)
              else
                let x1 = Number (if getNumber x2 = getNumber x1 then 1 else 0) in
                  if getNumber x1 = 0 then
                    let x1 = bool_to_val F in
                    let (x2,stack) = pop_all stack in
                      (x1,x2,x3,x4,stack)
                  else
                    equal_loop (x1,x2,x3,x4,stack)
          else if isBlock x1 then (* block case *)
            let (x1,x2) = (x2,x1) in
            if ~isBlock x1 then
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack)
             else (* both are blocks *)
               if getTag x1 = getTag x2 then
                 let x3 = x1 in
                 let x1 = Number (& (getTag x1)) in
                 if getNumber x1 = 3 then
                   let x1 = Number 0 in
                   let (x2,stack) = pop_all stack in
                     (x1,x2,x3,x4,stack)
                 else
                   let x1 = x3 in
                     if LENGTH (getContent x1) = LENGTH (getContent x2) then
                       let x4 = x2 in
                       let (x1,x4) = (x4,x1) in
                       let (x1,x2,x3,x4,stack) = explode_result (x1,x4,stack) in
                         equal_loop (x1,x2,x3,x4,stack)
                     else
                       let x1 = bool_to_val F in
                       let (x2,stack) = pop_all stack in
                         (x1,x2,x3,x4,stack)
               else
                 let x1 = Number (& (getTag x1)) in
                 if getNumber x1 = 3 then
                   let x1 = Number 0 in
                   let (x2,stack) = pop_all stack in
                     (x1,x2,x3,x4,stack)
                 else
                   let x1 = x2 in
                   let x1 = Number (& (getTag x1)) in
                   if getNumber x1 = 3 then
                     let x1 = Number 0 in
                     let (x2,stack) = pop_all stack in
                       (x1,x2,x3,x4,stack)
                   else
                     let x1 = bool_to_val F in
                     let (x2,stack) = pop_all stack in
                       (x1,x2,x3,x4,stack)
          else (* ref case *)
            let (x1,x2) = (x2,x1) in
            if isNumber x1 \/ isBlock x1 then
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack)
            else if RefPtrEq x1 x2 then
              equal_loop (x1,x2,x3,x4,stack)
            else
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack:bc_value list)`

val (equal_full_cert,equal_full_def,equal_full_pre_def) = x64_compile `
  equal_full (x1,x2,x3,x4,stack) =
    let stack = x4::stack in
    let stack = x3::stack in
    let stack = x2::stack in
    let x3 = Number 0 in
    let stack = x3::stack in
    let stack = x2::stack in
    let stack = x1::stack in
    let x3 = Number 1 in
    let stack = x3::stack in
    let (x1,x2,x3,x4,stack) = equal_loop (x1,x2,x3,x4,stack) in
    let (x2,stack) = (HD stack, TL stack) in
    let (x3,stack) = (HD stack, TL stack) in
    let (x4,stack) = (HD stack, TL stack) in
      (x1,x2,x3,x4,stack)`

val eq_stack_def = Define `
  (eq_stack [] = [Number 0]) /\
  (eq_stack ((x,y)::xs) = Number 1 :: x :: y :: eq_stack xs)`;

val pop_all_eq_stack = prove(
  ``!xs stack. pop_all_pre (eq_stack xs ++ stack) /\
               (pop_all (eq_stack xs ++ stack) = (Number 0,stack))``,
  Induct \\ ONCE_REWRITE_TAC [pop_all_def,pop_all_pre_def] \\ TRY Cases
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,eq_stack_def,HD,APPEND,
       isNumber_def,getNumber_def,TL]);

val bc_equal_def = bytecodeTerminationTheory.bc_equal_def

val bc_equal_list_SING = prove(
  ``!x y. bc_equal_list [x] [y] = bc_equal x y``,
  Cases \\ Cases \\ SIMP_TAC (srw_ss()) [bc_equal_def]
  \\ SRW_TAC [] [] \\ Cases_on `bc_equal_list l l'` \\ SRW_TAC [] []);

val bc_equal_list_ZIP = prove(
  ``!l l' t.
      (LENGTH l' = LENGTH l) ==>
      ((case bc_equal_list l' l of
          Eq_val T => bc_equal_list (MAP FST t) (MAP SND t)
        | Eq_val F => Eq_val F
        | Eq_closure => Eq_closure
        | Eq_type_error => Eq_type_error) =
       bc_equal_list (MAP FST (ZIP(l',l) ++ t)) (MAP SND (ZIP(l',l) ++ t)))``,
  Induct \\ Cases_on `l'` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ SIMP_TAC (srw_ss()) [bc_equal_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `bc_equal h h'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) []);

val FLAT_MAP_APPEND = prove(
  ``!xs t.
      (FLAT (MAP (\(x,y). [Number 1; y; x]) xs) ++ eq_stack t =
       eq_stack ((MAP (\(x,y). (y,x)) xs) ++ t))``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [FORALL_PROD,eq_stack_def]);

val MAP_ZIP_SWAP = prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (MAP (\(x,y). (y,x)) (ZIP (xs,ys)) = ZIP (ys,xs))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP]);

val bc_value1_size_APPEND = prove(
  ``!xs ys. bc_value1_size (xs ++ ys) =
            bc_value1_size xs + bc_value1_size ys``,
  Induct \\ ASM_SIMP_TAC std_ss [bc_value_size_def,APPEND,ADD_ASSOC]);

val equal_loop_thm = prove(
  ``!xs res x1 x2 x3 x4 stack.
      (bc_equal_list (MAP FST xs) (MAP SND xs) <> Eq_type_error) ==>
      ?x2i x3i x4i.
        equal_loop_pre (x1,x2,x3,x4,eq_stack xs ++ stack) /\
        (equal_loop (x1,x2,x3,x4,eq_stack xs ++ stack) =
           (bc_equality_result_to_val
              (bc_equal_list (MAP FST xs) (MAP SND xs)),x2i,x3i,x4i,stack))``,
  STRIP_TAC \\ completeInduct_on `bc_value1_size (MAP FST xs)`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `xs` \\ SIMP_TAC std_ss [eq_stack_def,APPEND]
  THEN1 (ONCE_REWRITE_TAC [equal_loop_def,equal_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF,HD,TL,getNumber_def,isNumber_def] \\ EVAL_TAC)
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [eq_stack_def,MAP]
  \\ ONCE_REWRITE_TAC [equal_loop_def,equal_loop_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF,HD,TL,getNumber_def,isNumber_def]
  \\ SIMP_TAC (srw_ss()) [getNumber_def,isNumber_def]
  \\ Cases_on `isNumber r` \\ FULL_SIMP_TAC std_ss [] THEN1
   (REVERSE (Cases_on `isNumber q`)
    \\ FULL_SIMP_TAC std_ss [pop_all_eq_stack,bc_equal_def] THEN1
     (Cases_on `r` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def])
    \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
    \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
    \\ FULL_SIMP_TAC std_ss [getNumber_def,isSmall_def]
    \\ Q.ABBREV_TAC `j = i'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `small_int j` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Cases_on `i = j` \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def]
      \\ `bc_value1_size (MAP FST t) <
          bc_value1_size (Number j::MAP FST t)` by ALL_TAC
      THEN1 (EVAL_TAC \\ DECIDE_TAC)
      \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `t`)
      \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `small_int i` \\ FULL_SIMP_TAC std_ss [] THEN1
     (`i <> j` by ALL_TAC THEN1
         (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
      \\ FULL_SIMP_TAC std_ss [bc_equal_def] \\ EVAL_TAC)
    \\ REVERSE (Cases_on `i = j`)
    \\ FULL_SIMP_TAC std_ss [bc_equal_def,EVAL ``1=0:int``] THEN1 EVAL_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SEP_I_TAC "equal_loop" \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ EVAL_TAC \\ DECIDE_TAC)
  \\ Cases_on `isBlock r` \\ FULL_SIMP_TAC std_ss [] THEN1
   (REVERSE (Cases_on `isBlock q`)
    \\ FULL_SIMP_TAC std_ss [pop_all_eq_stack,bc_equal_def] THEN1
     (Cases_on `r` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def,isBlock_def])
    \\ Cases_on `r` \\ Cases_on `q`
    \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def,isBlock_def]
    \\ FULL_SIMP_TAC std_ss [getTag_def,getContent_def,bc_equal_def]
    \\ REVERSE (Cases_on `n' = n`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (Cases_on `n' = 3` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
      \\ Cases_on `n = 3` \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `n = 3` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
    \\ SIMP_TAC std_ss [explode_result_def,getContent_def]
    \\ REVERSE (Cases_on `LENGTH l' = LENGTH l`)
    \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
    \\ FULL_SIMP_TAC std_ss [bc_equal_list_ZIP,APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [FLAT_MAP_APPEND,MAP_ZIP_SWAP]
    \\ SEP_I_TAC "equal_loop" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [MAP_FST_ZIP,MAP_APPEND]
      \\ FULL_SIMP_TAC std_ss [bc_value_size_def,bc_value1_size_APPEND]
      \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `r` \\ Cases_on `q`
  \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def,isBlock_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def,pop_all_eq_stack,RefPtrEq_def]
  \\ REVERSE (Cases_on `n' = n`) \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [isRefPtr_def]
  \\ `bc_value1_size (MAP FST t) <
      bc_value1_size (RefPtr n::MAP FST t)` by ALL_TAC
  THEN1 (EVAL_TAC \\ DECIDE_TAC)
  \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `t`)
  \\ FULL_SIMP_TAC std_ss [])
  |> Q.SPEC `[(x1,x2)]`
  |> SIMP_RULE std_ss [eq_stack_def,MAP,APPEND,bc_equal_list_SING]

val equal_full_thm = prove(
  ``(bc_equal x1 x2 <> Eq_type_error) ==>
    equal_full_pre (x1,x2,x3,x4,stack) /\
    (equal_full (x1,x2,x3,x4,stack) =
       (bc_equality_result_to_val (bc_equal x1 x2),x2,x3,x4,stack))``,
  SIMP_TAC std_ss [equal_full_def,equal_full_pre_def,LET_DEF]
  \\ ASSUME_TAC (GEN_ALL equal_loop_thm) \\ SEP_I_TAC "equal_loop"
  \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [HD,TL]);

val zHEAP_RAW_EQUAL = equal_full_cert
  |> DISCH ``bc_equal x1 x2 <> Eq_type_error``
  |> SIMP_RULE std_ss [equal_full_thm,LET_DEF,SEP_CLAUSES]
  |> RW [GSYM SPEC_MOVE_COND];

(*
(* prove that GC is no-op *)

val _ = x64_codegenLib.add_compiled [x64_full_gc_res];

val (_,array_eq_def,array_eq_pre_def) = x64_compile `
  array_eq (r0:word64,r14:word64,r15:word64,dm:word64 set,m:word64->word64) =
    if r0 = 0w then let r0 = 4w:word64 in (r0,r14,r15,dm,m) else
      let r12 = m r14 in
      let r13 = m r15 in
        if r12 <> r13 then
          let r0 = 0w in (r0,r14,r15,dm,m)
        else
          let r0 = r0 - 1w in
          let r14 = r14 + 8w in
          let r15 = r15 + 8w in
            array_eq (r0,r14,r15,dm,m)`

val (num_eq_cert,num_eq_def,num_eq_pre_def) = x64_compile `
  num_eq (r0:word64,r1,r12:word64,r13,dm:word64 set,m:word64->word64,ss) =
    let r14 = r0 + 1w in
    let r15 = r1 + 1w in
    let ss = r12::ss in
    let ss = r13::ss in
    let r12 = m r14 in
    let r13 = m r15 in
      if r12 <> r13 then
        let (r13,ss) = (HD ss, TL ss) in
        let (r12,ss) = (HD ss, TL ss) in
        let r0 = 0w in
          (r0,r1,r12,r13,dm,m,ss)
      else
        let r0 = r12 >>> 16 in
        let r14 = r14 + 8w in
        let r15 = r15 + 8w in
        let (r0,r14,r15,dm,m) = array_eq (r0,r14,r15,dm,m) in
        let (r13,ss) = (HD ss, TL ss) in
        let (r12,ss) = (HD ss, TL ss) in
          (r0,r1,r12,r13,dm,m,ss)`

val array_eq_thm = prove(
  ``!xs ys a b p1 p2.
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword(:64) /\
      (a && 0x7w = 0x0w) /\ (b && 0x7w = 0x0w) /\
      (one_list a xs * p1) (fun2set (m,dm)) /\
      (one_list b ys * p2) (fun2set (m,dm)) ==>
      ?r14' r15'.
        array_eq_pre (n2w (LENGTH xs), a, b, dm, m) /\
        (array_eq (n2w (LENGTH xs), a, b, dm, m) =
          (if xs = ys then 4w else 0w, r14', r15', dm, m))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [array_eq_def,array_eq_pre_def]
  \\ SIMP_TAC std_ss [CONS_11,n2w_11,ZERO_LT_dimword,LET_DEF,one_list_def]
  \\ REPEAT STRIP_TAC
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h' = h` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SEP_I_TAC "array_eq"
  \\ `LENGTH xs < dimword (:64)` by DECIDE_TAC
  \\ SEP_F_TAC \\ REPEAT STRIP_TAC
  \\ SEP_F_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [blast_align_lemma]);

val heap_lookup_DataOnly_IMP = prove(
  ``(x64_heap vs.current_heap heap vs.current_heap vs.current_heap *
        one_list_exists vs.other_heap cs.heap_limit * x64_store cs vs)
         (fun2set (vals.memory,vals.memory_domain)) /\
    (heap_lookup ptr heap = SOME (DataOnly x y)) ==>
    ?pp t1 t2. (x64_el (vs.current_heap + n2w (8 * ptr)) (DataOnly x y) t1 t2 * pp)
         (fun2set (vals.memory,vals.memory_domain))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,SEP_CLAUSES]
  \\ METIS_TAC [STAR_COMM,STAR_ASSOC]);

val SHIFT_LEMMA = prove(
  ``(y << 16 + 0x2w + b2w b1 = x << 16 + 0x2w + b2w b2) /\
    x <+ n2w (2**48) /\ y <+ n2w (2**48) ==>
    (x = y:word64) /\ (b1 = b2)``,
  Cases_on `b1` \\ Cases_on `b2` \\ FULL_SIMP_TAC std_ss [b2w_def]
  \\ blastLib.BBLAST_TAC) |> SIMP_RULE std_ss [];

val SHIFT_SHIFT_LEMMA = prove(
  ``w <+ n2w (2**48) ==> (((w:word64) << 16 + 0x2w + b2w b) >>> 16 = w)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [b2w_def] \\ blastLib.BBLAST_TAC)
  |> SIMP_RULE std_ss [];

val mw_thm = prove(
  ``mw = n2mw``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ HO_MATCH_MP_TAC mw_ind
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_def,multiwordTheory.n2mw_def]
  \\ SRW_TAC [] []);

val zHEAP_BigNumEq = let
  val th = num_eq_cert
  val pc = get_pc th
  val side = ``isNumber x1 /\ ~isSmall x1 /\ isNumber x2 /\ ~isSmall x2``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            ^side)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,Number (if getNumber x2 = getNumber x1 then 1 else 0),
               x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ `?r0 r1 r12 r13 dm m ss.
          num_eq
            (vals.reg0,vals.reg1,vals.reg12,vals.reg13,
             vals.memory_domain,vals.memory,vals.stack) =
          (r0,r1,r12,r13,dm,m,ss)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [PULL_EXISTS,PULL_FORALL] \\ NTAC 4 STRIP_TAC
    \\ SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.EXISTS_TAC `vals with <| reg0 := r0 ; reg1 := r1 ;
         reg12 := r12 ; reg13 := r13 ; reg14 := x' ; reg15 := x ;
         memory := m ; memory_domain := dm ; stack := ss |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ SIMP_TAC (srw_ss()++star_ss) [zVALS_def]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b1 /\ b3 ==> (b1 /\ (b2 ==> b3))``)
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isNumber_def]
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNumber_def]
    \\ FULL_SIMP_TAC std_ss [getNumber_def,isSmall_def]
    \\ Q.PAT_ASSUM `xx = yy` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ SIMP_TAC std_ss [PULL_IMP_EXISTS,PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`Data (if i = i' then 2w else 0w)`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss []
    \\ `abs_ml_inv (Number (if i' = i then 1 else 0)::Number i'::x3::x4::stack)
         refs (Data (if i = i' then 0x2w else 0x0w)::r2::r3::r4::roots,heap,a,sp)
          cs.heap_limit` by ALL_TAC THEN1
     (Cases_on `i' = i` \\ FULL_SIMP_TAC std_ss []
      \\ TRY (MATCH_MP_TAC (abs_ml_inv_Num |> SPEC_ALL |> Q.INST [`n`|->`1`]
                      |> SIMP_RULE std_ss [word_mul_n2w] |> GEN_ALL))
      \\ TRY (MATCH_MP_TAC (abs_ml_inv_Num |> SPEC_ALL |> Q.INST [`n`|->`0`]
                      |> SIMP_RULE std_ss [word_mul_n2w] |> GEN_ALL))
      \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
    \\ IMP_RES_TAC heap_lookup_DataOnly_IMP \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [DataOnly_def,x64_el_def,x64_payload_def,LET_DEF]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,x64_addr_def]
    \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
    \\ SIMP_TAC std_ss [num_eq_pre_def,num_eq_def,LET_DEF]
    \\ SIMP_TAC std_ss [HD,TL,NOT_CONS_NIL,WORD_SUB_ADD]
    \\ Cases_on `vals.memory (vs.current_heap + n2w (8 * ptr)) <>
                 vals.memory (vs.current_heap + n2w (8 * ptr'))`
    \\ FULL_SIMP_TAC std_ss [] THEN1
     (SEP_R_TAC \\ SIMP_TAC std_ss [blast_align_lemma,GSYM word_mul_n2w]
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ REPEAT STRIP_TAC
      \\ SRW_TAC [] [])
    \\ SEP_R_TAC \\ SIMP_TAC std_ss [blast_align_lemma,GSYM word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def]
    \\ Q.ABBREV_TAC `i1 = mw (Num (ABS i)):word64 list`
    \\ Q.ABBREV_TAC `i2 = mw (Num (ABS i')):word64 list`
    \\ `n2w (LENGTH i1) <+ 0x1000000000000w:word64 /\
        n2w (LENGTH i2) <+ 0x1000000000000w:word64` by
     (`LENGTH i1 < 18446744073709551616` by DECIDE_TAC
      \\ `LENGTH i2 < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
    \\ `(LENGTH i1 = LENGTH i2) /\ ((i' < 0) = (i < 0))` by ALL_TAC THEN1
     (IMP_RES_TAC SHIFT_LEMMA \\ REPEAT (Q.PAT_ASSUM `!xx.bb` (K ALL_TAC))
      \\ `LENGTH i1 < 18446744073709551616` by DECIDE_TAC
      \\ `LENGTH i2 < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
    \\ FULL_SIMP_TAC std_ss []
    \\ `(n2w (LENGTH i2) << 16 + 0x2w + b2w (i < 0)) >>> 16 =
        n2w (LENGTH i2):word64` by ALL_TAC THEN1
     (MATCH_MP_TAC SHIFT_SHIFT_LEMMA
      \\ `LENGTH i2 < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO])
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (array_eq_thm |> GEN_ALL)
    \\ Q.PAT_ASSUM `LENGTH i1 = LENGTH i2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_I_TAC "array_eq"
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `i2:word64 list`)
    \\ POP_ASSUM (MP_TAC o Q.SPECL [
         `one (vs.current_heap + n2w (8 * ptr),
            n2w (LENGTH (i1:word64 list)) << 16 + 0x2w + b2w (i < 0)) * pp'`,
         `one (vs.current_heap + n2w (8 * ptr'),
            n2w (LENGTH (i2:word64 list)) << 16 + 0x2w + b2w (i < 0)) * pp`])
    \\ MATCH_MP_TAC IMP_IMP \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (std_ss++star_ss) [blast_align_lemma,GSYM word_mul_n2w,
        AC WORD_ADD_COMM WORD_ADD_ASSOC]
      \\ SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ UNABBREV_ALL_TAC
    \\ FULL_SIMP_TAC std_ss [mw_thm,multiwordTheory.n2mw_11]
    \\ `(Num (ABS i) = Num (ABS i')) = (i = i')` by intLib.COOPER_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ SRW_TAC [] [])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^side)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [AC CONJ_COMM CONJ_ASSOC,SEP_IMP_REFL])
  val th = MP th lemma
  val _ = x64_codegenLib.add_compiled [th];
  in th end;


(* recursive equality *)

val (pop_all_cert,pop_all_def,pop_all_pre_def) = x64_compile `
  pop_all (stack:bc_value list) =
    let (x2,stack) = (HD stack, TL stack) in
      if getNumber x2 = 0 then
        (x2,stack)
      else
        let (x2,stack) = (HD stack, TL stack) in
        let (x2,stack) = (HD stack, TL stack) in
          pop_all stack`

val (_,equal_loop_def,equal_loop_pre_def) = x64_compile `
  equal_loop (x1:bc_value,x2,x3,x4,stack:bc_value list) =
    let (x1,stack) = (HD stack, TL stack) in
      if getNumber x1 = 0 then
        let x1 = bool_to_val T in
          (x1,x2,x3,x4,stack)
      else
        let (x2,stack) = (HD stack, TL stack) in
        let (x1,stack) = (HD stack, TL stack) in
          if isNumber x1 then (* number case *)
            let (x1,x2) = (x2,x1) in
            if ~(isNumber x1) then
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack)
            else
              if isSmall x1 then
                if getNumber x1 = getNumber x2 then
                  equal_loop (x1,x2,x3,x4,stack)
                else
                  let x1 = bool_to_val F in
                  let (x2,stack) = pop_all stack in
                    (x1,x2,x3,x4,stack)
              else
              let (x1,x2) = (x2,x1) in
              if isSmall x1 then
                let x1 = bool_to_val F in
                let (x2,stack) = pop_all stack in
                  (x1,x2,x3,x4,stack)
              else
                let x1 = Number (if getNumber x2 = getNumber x1 then 1 else 0) in
                  if getNumber x1 = 0 then
                    let x1 = bool_to_val F in
                    let (x2,stack) = pop_all stack in
                      (x1,x2,x3,x4,stack)
                  else
                    equal_loop (x1,x2,x3,x4,stack)
          else if isBlock x1 then (* block case *)
            let (x1,x2) = (x2,x1) in
            if ~isBlock x1 then
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack)
             else (* both are blocks *)
               if getTag x1 = getTag x2 then
                 let x3 = x1 in
                 let x1 = Number (& (getTag x1)) in
                 if getNumber x1 = 3 then
                   let x1 = Number 0 in
                   let (x2,stack) = pop_all stack in
                     (x1,x2,x3,x4,stack)
                 else
                   let x1 = x3 in
                     if LENGTH (getContent x1) = LENGTH (getContent x2) then
                       let x4 = x2 in
                       let (x1,x4) = (x4,x1) in
                       let (x1,x2,x3,x4,stack) = explode_result (x1,x4,stack) in
                         equal_loop (x1,x2,x3,x4,stack)
                     else
                       let x1 = bool_to_val F in
                       let (x2,stack) = pop_all stack in
                         (x1,x2,x3,x4,stack)
               else
                 let x1 = Number (& (getTag x1)) in
                 if getNumber x1 = 3 then
                   let x1 = Number 0 in
                   let (x2,stack) = pop_all stack in
                     (x1,x2,x3,x4,stack)
                 else
                   let x1 = x2 in
                   let x1 = Number (& (getTag x1)) in
                   if getNumber x1 = 3 then
                     let x1 = Number 0 in
                     let (x2,stack) = pop_all stack in
                       (x1,x2,x3,x4,stack)
                   else
                     let x1 = bool_to_val F in
                     let (x2,stack) = pop_all stack in
                       (x1,x2,x3,x4,stack)
          else (* ref case *)
            let (x1,x2) = (x2,x1) in
            if isNumber x1 \/ isBlock x1 then
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack)
            else if RefPtrEq x1 x2 then
              equal_loop (x1,x2,x3,x4,stack)
            else
              let x1 = bool_to_val F in
              let (x2,stack) = pop_all stack in
                (x1,x2,x3,x4,stack:bc_value list)`

val (equal_full_cert,equal_full_def,equal_full_pre_def) = x64_compile `
  equal_full (x1,x2,x3,x4,stack) =
    let stack = x4::stack in
    let stack = x3::stack in
    let stack = x2::stack in
    let x3 = Number 0 in
    let stack = x3::stack in
    let stack = x2::stack in
    let stack = x1::stack in
    let x3 = Number 1 in
    let stack = x3::stack in
    let (x1,x2,x3,x4,stack) = equal_loop (x1,x2,x3,x4,stack) in
    let (x2,stack) = (HD stack, TL stack) in
    let (x3,stack) = (HD stack, TL stack) in
    let (x4,stack) = (HD stack, TL stack) in
      (x1,x2,x3,x4,stack)`

val eq_stack_def = Define `
  (eq_stack [] = [Number 0]) /\
  (eq_stack ((x,y)::xs) = Number 1 :: x :: y :: eq_stack xs)`;

val pop_all_eq_stack = prove(
  ``!xs stack. pop_all_pre (eq_stack xs ++ stack) /\
               (pop_all (eq_stack xs ++ stack) = (Number 0,stack))``,
  Induct \\ ONCE_REWRITE_TAC [pop_all_def,pop_all_pre_def] \\ TRY Cases
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,eq_stack_def,HD,APPEND,
       isNumber_def,getNumber_def,TL]);

val bc_equal_def = bytecodeTerminationTheory.bc_equal_def

val bc_equal_list_SING = prove(
  ``!x y. bc_equal_list [x] [y] = bc_equal x y``,
  Cases \\ Cases \\ SIMP_TAC (srw_ss()) [bc_equal_def]
  \\ SRW_TAC [] [] \\ Cases_on `bc_equal_list l l'` \\ SRW_TAC [] []);

val bc_equal_list_ZIP = prove(
  ``!l l' t.
      (LENGTH l' = LENGTH l) ==>
      ((case bc_equal_list l' l of
          Eq_val T => bc_equal_list (MAP FST t) (MAP SND t)
        | Eq_val F => Eq_val F
        | Eq_closure => Eq_closure
        | Eq_type_error => Eq_type_error) =
       bc_equal_list (MAP FST (ZIP(l',l) ++ t)) (MAP SND (ZIP(l',l) ++ t)))``,
  Induct \\ Cases_on `l'` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ SIMP_TAC (srw_ss()) [bc_equal_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `bc_equal h h'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) []);

val FLAT_MAP_APPEND = prove(
  ``!xs t.
      (FLAT (MAP (\(x,y). [Number 1; y; x]) xs) ++ eq_stack t =
       eq_stack ((MAP (\(x,y). (y,x)) xs) ++ t))``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [FORALL_PROD,eq_stack_def]);

val MAP_ZIP_SWAP = prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (MAP (\(x,y). (y,x)) (ZIP (xs,ys)) = ZIP (ys,xs))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP]);

val bc_value1_size_APPEND = prove(
  ``!xs ys. bc_value1_size (xs ++ ys) =
            bc_value1_size xs + bc_value1_size ys``,
  Induct \\ ASM_SIMP_TAC std_ss [bc_value_size_def,APPEND,ADD_ASSOC]);

val equal_loop_thm = prove(
  ``!xs res x1 x2 x3 x4 stack.
      (bc_equal_list (MAP FST xs) (MAP SND xs) <> Eq_type_error) ==>
      ?x2i x3i x4i.
        equal_loop_pre (x1,x2,x3,x4,eq_stack xs ++ stack) /\
        (equal_loop (x1,x2,x3,x4,eq_stack xs ++ stack) =
           (bc_equality_result_to_val
              (bc_equal_list (MAP FST xs) (MAP SND xs)),x2i,x3i,x4i,stack))``,
  STRIP_TAC \\ completeInduct_on `bc_value1_size (MAP FST xs)`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `xs` \\ SIMP_TAC std_ss [eq_stack_def,APPEND]
  THEN1 (ONCE_REWRITE_TAC [equal_loop_def,equal_loop_pre_def]
    \\ SIMP_TAC std_ss [LET_DEF,HD,TL,getNumber_def,isNumber_def] \\ EVAL_TAC)
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [eq_stack_def,MAP]
  \\ ONCE_REWRITE_TAC [equal_loop_def,equal_loop_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF,HD,TL,getNumber_def,isNumber_def]
  \\ SIMP_TAC (srw_ss()) [getNumber_def,isNumber_def]
  \\ Cases_on `isNumber r` \\ FULL_SIMP_TAC std_ss [] THEN1
   (REVERSE (Cases_on `isNumber q`)
    \\ FULL_SIMP_TAC std_ss [pop_all_eq_stack,bc_equal_def] THEN1
     (Cases_on `r` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def])
    \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
    \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
    \\ FULL_SIMP_TAC std_ss [getNumber_def,isSmall_def]
    \\ Q.ABBREV_TAC `j = i'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `small_int j` \\ FULL_SIMP_TAC std_ss [] THEN1
     (Cases_on `i = j` \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def]
      \\ `bc_value1_size (MAP FST t) <
          bc_value1_size (Number j::MAP FST t)` by ALL_TAC
      THEN1 (EVAL_TAC \\ DECIDE_TAC)
      \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `t`)
      \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `small_int i` \\ FULL_SIMP_TAC std_ss [] THEN1
     (`i <> j` by ALL_TAC THEN1
         (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
      \\ FULL_SIMP_TAC std_ss [bc_equal_def] \\ EVAL_TAC)
    \\ REVERSE (Cases_on `i = j`)
    \\ FULL_SIMP_TAC std_ss [bc_equal_def,EVAL ``1=0:int``] THEN1 EVAL_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SEP_I_TAC "equal_loop" \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ EVAL_TAC \\ DECIDE_TAC)
  \\ Cases_on `isBlock r` \\ FULL_SIMP_TAC std_ss [] THEN1
   (REVERSE (Cases_on `isBlock q`)
    \\ FULL_SIMP_TAC std_ss [pop_all_eq_stack,bc_equal_def] THEN1
     (Cases_on `r` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def]
      \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def,isBlock_def])
    \\ Cases_on `r` \\ Cases_on `q`
    \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def,isBlock_def]
    \\ FULL_SIMP_TAC std_ss [getTag_def,getContent_def,bc_equal_def]
    \\ REVERSE (Cases_on `n' = n`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (Cases_on `n' = 3` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
      \\ Cases_on `n = 3` \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
    \\ Cases_on `n = 3` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
    \\ SIMP_TAC std_ss [explode_result_def,getContent_def]
    \\ REVERSE (Cases_on `LENGTH l' = LENGTH l`)
    \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
    \\ FULL_SIMP_TAC std_ss [bc_equal_list_ZIP,APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [FLAT_MAP_APPEND,MAP_ZIP_SWAP]
    \\ SEP_I_TAC "equal_loop" \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [MAP_FST_ZIP,MAP_APPEND]
      \\ FULL_SIMP_TAC std_ss [bc_value_size_def,bc_value1_size_APPEND]
      \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `r` \\ Cases_on `q`
  \\ FULL_SIMP_TAC std_ss [isNumber_def,canCompare_def,isBlock_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bc_equal_def,pop_all_eq_stack,RefPtrEq_def]
  \\ REVERSE (Cases_on `n' = n`) \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [isRefPtr_def]
  \\ `bc_value1_size (MAP FST t) <
      bc_value1_size (RefPtr n::MAP FST t)` by ALL_TAC
  THEN1 (EVAL_TAC \\ DECIDE_TAC)
  \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPEC `t`)
  \\ FULL_SIMP_TAC std_ss [])
  |> Q.SPEC `[(x1,x2)]`
  |> SIMP_RULE std_ss [eq_stack_def,MAP,APPEND,bc_equal_list_SING]

val equal_full_thm = prove(
  ``(bc_equal x1 x2 <> Eq_type_error) ==>
    equal_full_pre (x1,x2,x3,x4,stack) /\
    (equal_full (x1,x2,x3,x4,stack) =
       (bc_equality_result_to_val (bc_equal x1 x2),x2,x3,x4,stack))``,
  SIMP_TAC std_ss [equal_full_def,equal_full_pre_def,LET_DEF]
  \\ ASSUME_TAC (GEN_ALL equal_loop_thm) \\ SEP_I_TAC "equal_loop"
  \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [HD,TL]);

val zHEAP_RAW_EQUAL = equal_full_cert
  |> DISCH ``bc_equal x1 x2 <> Eq_type_error``
  |> SIMP_RULE std_ss [equal_full_thm,LET_DEF,SEP_CLAUSES]
  |> RW [GSYM SPEC_MOVE_COND];
*)


(* prove that GC is no-op *)

val _ = x64_codegenLib.add_compiled [x64_full_gc_res];

val (x64_gc_op_res, x64_gc_op_def, x64_gc_op_pre_def) = x64_compile `
  x64_gc_op (r0,r1,r2,r3,r9:word64,ss:word64 list,dm,m) =
    let ss = r3 :: ss in
    let ss = r2 :: ss in
    let ss = r1 :: ss in
    let ss = r0 :: ss in
    let r8 = m r9 in
    let r7 = m (r9 + 8w) in
    let m = (r9 =+ r7) m in
    let m = (r9 + 8w =+ r8) m in
    let (r8,ss,dm,m) = x64_full_gc (r7,ss,dm,m) in
    let r0 = m r9 in
    let r7 = m (r9 + 16w) in
    let r7 = r7 << 3 in
    let r7 = r7 + r0 in
    let r7 = r7 - 1w in
    let (r0,ss) = (HD ss,TL ss) in
    let (r1,ss) = (HD ss,TL ss) in
    let (r2,ss) = (HD ss,TL ss) in
    let (r3,ss) = (HD ss,TL ss) in
    let r6 = r8 - 1w in
      (r0,r1,r2,r3,r6,r7,r8,r9,ss,dm,m)`

val x64_heap_IGNORE_bf = prove(
  ``!heap a.
      (FILTER isForwardPointer heap = []) ==>
      (x64_heap a heap bf bd = x64_heap a heap ARB bd)``,
  Induct \\ SIMP_TAC std_ss [x64_heap_def,x64_el_def]
  \\ Cases \\ ASM_SIMP_TAC std_ss [x64_heap_def,x64_el_def,
    isForwardPointer_def,FILTER,NOT_CONS_NIL]
  \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [x64_el_def]);

val zHEAP_GC = let
  val th = x64_gc_op_res
  val pc = get_pc th
  val inv = ``SOME (\(sp:num,vals).
    (ttt13 = vals.reg13) /\ (ttt14 = vals.reg14))``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val x64_heap_heap_expand = prove(
    ``x64_heap a (heap_expand n) x y = one_list_exists a n``,
    Cases_on `n` \\ ASM_SIMP_TAC (srw_ss()) [heap_expand_def,x64_heap_def,
       one_list_exists_def,LENGTH_NIL,SEP_CLAUSES,one_list_def,x64_el_def]
    \\ FULL_SIMP_TAC std_ss [ADD1]);
  val MAP_APPEND_LEMMA = prove(
    ``f x :: (MAP f xs ++ ys) = MAP f (x::xs) ++ ys``,
    FULL_SIMP_TAC std_ss [MAP,APPEND]);
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [x64_gc_op_def, x64_gc_op_pre_def,LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `(vals.memory (vs.base_ptr) = vs.current_heap)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [x64_store_def,one_list_def] \\ SEP_R_TAC)
    \\ `(vals.memory (vs.base_ptr + 0x8w) = vs.other_heap)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [x64_store_def,one_list_def] \\ SEP_R_TAC)
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND_LEMMA,APPEND]
    \\ Q.ABBREV_TAC `m1 = (vs.base_ptr + 0x8w =+ vs.current_heap)
         ((vs.base_ptr =+ vs.other_heap) vals.memory)`
    \\ Q.ABBREV_TAC `vals1 = vals with memory := m1`
    \\ `(vals.memory_domain = vals1.memory_domain) /\
        (m1 = vals1.memory)` by (Q.UNABBREV_TAC `vals1` \\ SRW_TAC [] [])
    \\  POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\  POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\ IMP_RES_TAC full_gc_thm
    \\ `x64_heap vs.current_heap heap vs.current_heap vs.current_heap =
        x64_heap vs.current_heap heap vs.other_heap vs.current_heap` by
      (FULL_SIMP_TAC std_ss [abs_ml_inv_def,heap_ok_def,x64_heap_IGNORE_bf])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `vs1 = (vs with <| current_heap := vs.other_heap;
           other_heap := vs.current_heap |>)`
    \\ `(x64_heap vs.current_heap heap vs.other_heap vs.current_heap *
         one_list_exists vs.other_heap cs.heap_limit *
         x64_store cs vs1)
           (fun2set (vals1.memory,vals1.memory_domain))` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES,STAR_ASSOC]
      \\ Q.ABBREV_TAC `m = vals.memory`
      \\ Q.ABBREV_TAC `dm = vals.memory_domain`
      \\ SEP_W_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []
      \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (x64_full_gc_thm |> GEN_ALL)
    \\ SEP_I_TAC "x64_full_gc"
    \\ POP_ASSUM (MP_TAC o Q.GEN `r` o
           Q.SPECL [`roots2`,`r`,`cs.heap_limit`,`heap2`,`heap`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ SEP_F_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ cheat (* stack length *))
    \\ `?t1 t2 t3 t4 roots3. roots2 = t1::t2::t3::t4::roots3` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ Cases_on `roots2` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
      \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
      \\ Cases_on `t'` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
      \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (UNABBREV_ALL_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
      \\ SEP_R_TAC \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,MAP,HD,TL]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_EXISTS_THM,zVALS_def]
    \\ `m1' (vs.base_ptr + 0x10w) << 3 + m1' vs.base_ptr =
        vs.other_heap + n2w (8 * cs.heap_limit)` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,word_arith_lemma1]
      \\ SEP_R_TAC
      \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
      \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
    \\ FULL_SIMP_TAC std_ss [MAP,HD,TL,APPEND]
    \\ Q.EXISTS_TAC `vals with
          <| reg0 := x64_addr vs.other_heap t1;
             reg1 := x64_addr vs.other_heap t2;
             reg2 := x64_addr vs.other_heap t3;
             reg3 := x64_addr vs.other_heap t4;
             reg6 := vs.other_heap + n2w (8 * heap_length heap2) - 1w;
             reg7 := vs.other_heap + n2w (8 * cs.heap_limit) - 1w;
             reg8 := (vs.other_heap + n2w (8 * heap_length heap2));
             reg9 := vs.base_ptr;
             stack := (MAP (x64_addr vs.other_heap) roots3 ++
                      0x1w::cs.ret_address::cs.rest_of_stack);
             memory := m1' |>`
    \\ SIMP_TAC (srw_ss()) []
    \\ `vals1.memory_domain = vals.memory_domain` by ALL_TAC
    THEN1 (Q.UNABBREV_TAC `vals1` \\ SRW_TAC [] [])
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,cond_STAR]
    \\ REVERSE STRIP_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) []
           \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_ASSOC WORD_ADD_COMM])
    \\ ASM_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs1`,`t1`,`t2`,`t3`,`t4`,`roots3`,
         `heap2 ++ heap_expand (cs.heap_limit - a2)`,`a2`,`cs.heap_limit - a2`]
    \\ `heap_vars_ok vs1` by ALL_TAC
    THEN1 (Q.UNABBREV_TAC `vs1` \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `vs1` \\ ASM_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [APPEND,x64_heap_APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [x64_heap_heap_expand]
    \\ FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def]
    \\ SEP_R_TAC
    \\ `a2 <= cs.heap_limit` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,heap_ok_def,heap_length_APPEND]
      \\ DECIDE_TAC)
    \\ IMP_RES_TAC (DECIDE ``n <= (m:num) ==> (n + (m - n) = m)``)
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> Q.INST [`ttt13`|->`r13`,`ttt14`|->`r14`]
  in th end;


(* next char -- calls getchar *)

val heap_inv_IMP = prove(
  ``heap_inv (cs,x1,x2,x3,x4,refs,stack,s,SOME f) vals ==> ?sp. f (sp,vals)``,
  SIMP_TAC std_ss [heap_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val x64_getchar_thm = prove(
  ``SPEC X64_MODEL
     (zPC pi * ~zR 0x0w * ~zR 0x7w * ~zR 0x3w * ~zR 0x1w * ~zR 0x2w *
      ~zR 0x6w * ~zR 0x8w * ~zR 0x9w * ~zR 0xAw * ~zR 0xBw *
      zR 0xCw r12 * zR 0xDw r13 * zR 0xEw r14 * zR 0xFw r15 *
      zIO (pi,input,po,output) * ~zS * zSTACK (base,x::stack)) {}
     (zPC x * zR 0x0w (HD (SNOC (~0w) (MAP w2w input))) * ~zR 0x7w *
      ~zR 0x3w * ~zR 0x1w * ~zR 0x2w * ~zR 0x6w * ~zR 0x8w * ~zR 0x9w *
      ~zR 0xAw * ~zR 0xBw * zR 0xCw r12 * zR 0xDw r13 * zR 0xEw r14 *
      zR 0xFw r15 * zIO (pi,DROP 1 input,po,output) * ~zS *
      zSTACK (base,stack))``,
  cheat);

val getchar_lemma = let
  val load_r0 = compose_specs ["mov r0,[r9+32]"]
  val mov_r10_r0 = compose_specs ["mov r10,r0"]
  val th1 = SPEC_COMPOSE_RULE [ x64_push_r0, x64_push_r1, x64_push_r2,
    x64_push_r3, x64_push_r6, x64_push_r7, x64_push_r8, x64_push_r9,
    x64_push_r11, load_r0, x64_call_r0, x64_getchar_thm,
    mov_r10_r0, x64_pop_r11, x64_pop_r9, x64_pop_r8,
    x64_pop_r7, x64_pop_r6, x64_pop_r3, x64_pop_r2, x64_pop_r1,
    x64_pop_r0]
    |> REWRITE_RULE [TL,HD,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
    |> SIMP_RULE (std_ss++sep_cond_ss) []
    |> Q.INST [`po`|->`cs.putchar_ptr`,
               `input`|->`MAP (n2w o ORD) (DROP 1 s.input)`,
               `output`|->`MAP (n2w o ORD) s.output`]
  in th1 end

val zHEAP_NEXT_INPUT = let
  val th = getchar_lemma |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL]
    \\ SIMP_TAC std_ss [STAR_ASSOC,SEP_IMP_def,cond_STAR]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC heap_inv_IMP
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,
         one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs, x1, x2, x3, x4, refs, stack,
    (s with input := DROP 1 s.input),NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
  gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| input_stream := DROP 1 vals.input_stream ;
          reg10 := (HD
             (SNOC (~0x0w)
                (MAP w2w (MAP ((n2w:num->word8) o ORD) (DROP 1 s.input))))) |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ `vals.memory (vs.base_ptr + 32w) = cs.getchar_ptr` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ Cases_on `s.input`
    \\ FULL_SIMP_TAC (srw_ss()) [DROP_def,MAP,HD,HD,APPEND,SNOC_APPEND,not_0w_def]
    \\ Cases_on `t`
    \\ FULL_SIMP_TAC (srw_ss()) [DROP_def,MAP,HD,HD,APPEND,SNOC_APPEND,not_0w_def]
    \\ `ORD h' < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ FULL_SIMP_TAC (srw_ss()) [w2w_def,n2w_w2n])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_READ_INPUT = let
  val th = compose_specs ["mov r0,r10","and r0,511","shl r0,2"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
    Number (if s.input = [] then 511 else & (ORD (HD s.input))),
    x2, x3, x4, refs, stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
  gg goal
*)
  val blast = blastLib.BBLAST_PROVE
    ``!w:word64. w <+ 512w ==> (0x7FCw && 0x4w * w = 0x4w * w)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MAP,HD,APPEND]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg0 := ((HD (MAP (n2w o ORD) s.input ++ [not_0w]) && 0x1FFw) << 2)`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC (std_ss++star_ss) [APPEND,GSYM APPEND_ASSOC])
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
         `Data (2w * n2w (if s.input = "" then 511 else (ORD (HD s.input))))`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ SIMP_TAC std_ss [x64_addr_def]
    \\ REVERSE STRIP_TAC THEN1
     (Cases_on `s.input` \\ SIMP_TAC std_ss [w2w_def,MAP,HD,APPEND] THEN1 EVAL_TAC
      \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
      \\ `2 * ORD h < 9223372036854775808` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,WORD_MUL_LSL,MULT_ASSOC]
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ MATCH_MP_TAC blast
      \\ `ORD h < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO,w2n_n2w] \\ DECIDE_TAC)
    \\ `(if s.input = "" then 511 else (&ORD (HD s.input))) =
        & (if s.input = "" then 511 else (ORD (HD s.input)))` by cheat
    \\ ASM_SIMP_TAC std_ss [] \\ MATCH_MP_TAC abs_ml_inv_Num
    \\ Q.LIST_EXISTS_TAC [`x1`,`r1`] \\ ASM_SIMP_TAC std_ss []
    \\ `ORD (HD s.input) < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ SRW_TAC [] [] \\ DECIDE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;



(* print char -- calls putchar *)

val load_char_lemma = let
  val ((r7,_,_),_) = prog_x64Lib.x64_spec "BF"
  val blast_lemma = blastLib.BBLAST_PROVE
    ``(w2w ((w2w imm8):word32) = imm8:word8) /\
      (w2w (((w2w imm8):word32) >>> 8) = 0w:word8) /\
      (w2w (((w2w imm8):word32) >>> 16) = 0w:word8) /\
      (w2w (((w2w imm8):word32) >>> 24) = 0w:word8)``
  val r7 = r7 |> Q.INST [`imm32`|->`w2w (c:word8)`] |> RW [blast_lemma]
  val lemma = prove(
    ``!c:word8. (n2w (SIGN_EXTEND 32 64 (w2n c) MOD 4294967296) = (w2w c):word64)``,
    Cases \\ FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,w2w_n2w,
        bitTheory.BITS_THM2,bitTheory.BIT_def]
    \\ `n < 4294967296 /\ ~(2147483648 <= n)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [LET_DEF,DIV_EQ_X]);
  val r7 = SIMP_RULE (srw_ss()) [w2n_w2w,lemma] r7
  in r7 end

val putchar_lemma = let
  val ((load_r0,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r0,[r9+24]")
  val th1 = SPEC_COMPOSE_RULE [ x64_push_r0, x64_push_r1, x64_push_r2,
    x64_push_r3, x64_push_r6, x64_push_r7, x64_push_r8, x64_push_r9,
    x64_push_r10, x64_push_r11, load_char_lemma, load_r0, x64_call_r0,
    x64_putchar_thm, x64_pop_r11, x64_pop_r10, x64_pop_r9, x64_pop_r8,
    x64_pop_r7, x64_pop_r6, x64_pop_r3, x64_pop_r2, x64_pop_r1, x64_pop_r0]
    |> REWRITE_RULE [TL,HD,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
    |> SIMP_RULE (std_ss++sep_cond_ss) []
    |> Q.INST [`pi`|->`cs.getchar_ptr`,
               `input`|->`MAP (n2w o ORD) (DROP 1 s.input)`,
               `output`|->`MAP (n2w o ORD) s.output`]
  in th1 end

val zHEAP_PUT_CHAR = let
  val th = putchar_lemma |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL]
    \\ SIMP_TAC std_ss [STAR_ASSOC,SEP_IMP_def,cond_STAR]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC heap_inv_IMP
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,
         one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs, x1, x2, x3, x4, refs, stack,
    (s with output := s.output ++ [CHR (w2n (c:word8))]),NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| output_stream := vals.output_stream ++ [c] |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ `vals.memory (vs.base_ptr + 0x18w) = cs.putchar_ptr` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ ASSUME_TAC (Q.ISPEC `c:word8` w2n_lt)
    \\ FULL_SIMP_TAC (srw_ss()) [ORD_CHR,STAR_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;


(* print error message *)

val error_msg = error_msg_def |> concl |> rand |> stringSyntax.fromHOLstring;

val print_error = let
  val th = SPEC_COMPOSE_RULE [load_char_lemma,x64_call_r15,x64_putchar_thm]
  val th = th |> Q.INST [`c`|->`n2w (ORD chr)`] |> Q.GEN `chr`
  fun spec_for_char c = th |> SPEC (stringSyntax.fromMLchar c)
  val th = SPEC_COMPOSE_RULE (map spec_for_char (explode error_msg))
  val lemma = prove(
    ``(n2w (ORD c) :: [] = MAP (n2w o ORD) [c]) /\
      (n2w (ORD c) :: MAP (n2w o ORD) cs = MAP (n2w o ORD) (c::cs))``,
    SIMP_TAC std_ss [MAP])
  val th = th |> SIMP_RULE std_ss [GSYM APPEND_ASSOC,APPEND]
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) []))
              |> RW [lemma]
  val print_error = th
  val ((load_r15,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r15,[r9+24]")
  val th1 = SPEC_COMPOSE_RULE [ x64_push_r0, x64_push_r1, x64_push_r2,
    x64_push_r3, x64_push_r6, x64_push_r7, x64_push_r8, x64_push_r9,
    x64_push_r10, x64_push_r11, x64_push_r15, load_r15, print_error,
    x64_pop_r15, x64_pop_r11, x64_pop_r10, x64_pop_r9, x64_pop_r8, x64_pop_r7,
    x64_pop_r6, x64_pop_r3, x64_pop_r2, x64_pop_r1, x64_pop_r0]
    |> REWRITE_RULE [TL,HD,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
    |> SIMP_RULE (std_ss++sep_cond_ss) []
    |> Q.INST [`pi`|->`cs.getchar_ptr`,
               `input`|->`MAP (n2w o ORD) (DROP 1 s.input)`,
               `output`|->`MAP (n2w o ORD) s.output`]
    |> RW [GSYM MAP_APPEND,GSYM error_msg_def]
  in th1 end;

val zHEAP_PRINT_ERROR_MSG = let
  val th = print_error |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL]
    \\ SIMP_TAC std_ss [STAR_ASSOC,SEP_IMP_def,cond_STAR]
    \\ REPEAT STRIP_TAC \\ IMP_RES_TAC heap_inv_IMP
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,
         one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs, x1, x2, x3, x4, refs, stack,
    (s with output := s.output ++ error_msg),NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| output_stream :=
         vals.output_stream ++ MAP (n2w o ORD) error_msg |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ `vals.memory (vs.base_ptr + 0x18w) = cs.putchar_ptr` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss []
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;


(* terminate, i.e. clean up and call return pointer *)

val (x64_pop_stack_res, x64_pop_stack_def, x64_pop_stack_pre_def) = x64_compile `
  x64_pop_stack (ss:word64 list) =
    let (r15,ss) = (HD ss,TL ss) in
      if r15 = 1w then let ss = r15::ss in (ss) else
        x64_pop_stack (ss)`

val x64_pop_stack_thm = prove(
  ``!xs ys.
      EVERY (\x. x <> 1w) xs ==>
      x64_pop_stack_pre (xs ++ 1w :: ys) /\
      (x64_pop_stack (xs ++ 1w :: ys) = 1w::ys)``,
  Induct \\ SIMP_TAC std_ss [APPEND,EVERY_DEF]
  \\ ONCE_REWRITE_TAC [x64_pop_stack_def, x64_pop_stack_pre_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,HD,TL,NOT_CONS_NIL]);

val x64_addr_NOT_1 = prove(
  ``!h a. (a && 7w = 0w) ==> x64_addr a h <> 0x1w``,
  Cases  \\ FULL_SIMP_TAC std_ss [x64_addr_def] \\ blastLib.BBLAST_TAC);

val zHEAP_POP_ENTIRE_STACK = let
  val th = x64_pop_stack_res
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,[],s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `EVERY (\x. x <> 1w) (MAP (x64_addr vs.current_heap) roots)` by
     (FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_EXISTS,heap_vars_ok_def]
      \\ METIS_TAC [x64_addr_NOT_1])
    \\ IMP_RES_TAC x64_pop_stack_thm \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals with <| stack := 1w::cs.ret_address::cs.rest_of_stack ;
                                  reg15 := x |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (pop_thm |> GEN_ALL)
    \\ Q.LIST_EXISTS_TAC [`stack`,`roots`]
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ FULL_SIMP_TAC std_ss []
    \\ (move_thm
        |> Q.SPECL [`[]`,`[]`] |> Q.INST [`stack`|->`[]`,`roots`|->`[]`]
        |> SIMP_RULE std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC,APPEND_NIL]
        |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_TERMINATE = let
  val th = SPEC_COMPOSE_RULE [x64_pop_r15,x64_ret]
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,[],s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP_OUTPUT (cs,s.output)`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ `LENGTH roots = 0` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,MAP,APPEND,HD,TL,NOT_CONS_NIL]
    \\ SIMP_TAC std_ss [zHEAP_OUTPUT_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals with <| stack := cs.rest_of_stack
                                                    ; reg15 := 1w |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,[],s,NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [zHEAP_POP_ENTIRE_STACK,th]
  in th end;


(* terminate with error message *)

val zHEAP_TERMINATE_WITH_ERROR = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "jmp [r9+40]")
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS *
                         zPC cs.error_ptr`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES] \\ STRIP_TAC
    \\ POP_ASSUM (fn th => MP_TAC th THEN ASSUME_TAC th)
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `(vals.memory (vs.base_ptr + 40w) = cs.error_ptr)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
           \\ SEP_R_TAC)
    \\ `(vs.base_ptr + 40w) IN vals.memory_domain` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
           \\ SEP_R_TAC) \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th1 = MP th lemma
  val th = SPEC_COMPOSE_RULE [zHEAP_PRINT_ERROR_MSG,zHEAP_TERMINATE]
  val (th,goal) = SPEC_WEAKEN_RULE th ``zHEAP_ERROR (cs,s.output)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zHEAP_ERROR_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `s.output`
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.IS_PREFIX_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val (_,_,code,_) = dest_spec (concl th)
  val error_code_def = Define `error_code (p:word64) = ^code`;
  val th = th |> RW [GSYM error_code_def]
  val th = SPEC_COMPOSE_RULE [th1,th]
  in th end;


(* allocator space test *)

val (zHEAP_ALLOC_TEST_SUCCESS,zHEAP_ALLOC_TEST_FAILURE) = let
  val ((th1,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r15,r7")
  val ((th2,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "sub r15,r6")
  val ((th3,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "cmp r15,r14")
  val ((th4,_,_),x) = prog_x64Lib.x64_spec_memory64 "73"
  val (th4i,_,_) = case x of SOME t => t | _ => fail()
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val thA = SPEC_COMPOSE_RULE [th1,th2,th3,th4]
  val thA = HIDE_STATUS_RULE true sts thA
  val thB = SPEC_COMPOSE_RULE [th1,th2,th3,th4i]
  val thB = HIDE_STATUS_RULE true sts thB
  (* success case *)
  val th = thA |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,precond_def]
               |> UNDISCH |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val inv = ``SOME (\(sp:num,vals).
                (vals.reg13 = ret) /\
                (vals.reg14 = n2w (8 * needed)) /\ needed <= sp /\
                 needed < 2 ** 32)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val rw_lemma = prove(``w - 1w - (v - 1w) = w - v:word64``,
                       blastLib.BBLAST_TAC);
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1
     (POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ SIMP_TAC std_ss [rw_lemma]
      \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,GSYM word_mul_n2w,
           WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
      \\ SIMP_TAC std_ss [Once WORD_ADD_COMM,WORD_ADD_SUB]
      \\ SIMP_TAC std_ss [word_mul_n2w,WORD_LO]
      \\ `(8 * sp) < 18446744073709551616` by cheat
      \\ `(8 * needed) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
      \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `vals with <| reg15 := vals.reg7 - vals.reg6 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  val thA = MP th lemma
  (* failure case *)
  val th = thB |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,precond_def]
               |> UNDISCH |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val inv = ``SOME (\(sp:num,vals).
                (vals.reg13 = ret) /\
                (vals.reg14 = n2w (8 * needed)) /\ ~(needed <= sp) /\
                 needed < 2 ** 32)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
set_goal([],goal)
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ SIMP_TAC std_ss [rw_lemma]
      \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,GSYM word_mul_n2w,
           WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
      \\ SIMP_TAC std_ss [Once WORD_ADD_COMM,WORD_ADD_SUB]
      \\ SIMP_TAC std_ss [word_mul_n2w,WORD_LO]
      \\ `(8 * sp) < 18446744073709551616` by cheat
      \\ `(8 * needed) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [w2n_n2w]
      \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `vals with <| reg15 := vals.reg7 - vals.reg6 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  val thB = MP th lemma
  in (thA,thB) end;

val heap_inv_IMP_NONE = prove(
  ``heap_inv (cs,x1,x2,x3,x4,refs,stack,s,x) vals ==>
    heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals``,
  SIMP_TAC std_ss [heap_inv_def] \\ STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
  \\ FULL_SIMP_TAC std_ss []);

val zHEAP_JMP_r13 = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "jmp r13")
  val inv = ``SOME (\(sp,vals). (vals.reg13 = ret) /\ P (sp:num,vals))``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * zPC ret`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_CALL_ALLOC = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r13, [r9+48]")
  val th = SPEC_COMPOSE_RULE [th,x64_call_r13,x64_pop_r13]
           |> SIMP_RULE std_ss [NOT_CONS_NIL,HD,TL,SEP_CLAUSES]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val inv1 = ``SOME (\(sp:num,vals). (n2w (8 * needed) = vals.reg14))``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv1) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 0x30w) = cs.alloc_ptr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals).
                (p + 0x7w = vals.reg13) /\
                (n2w (8 * needed) = vals.reg14))``
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
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv1) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_ALLOC_FAIL_OR_RETURN = let
  val th = zHEAP_ALLOC_TEST_FAILURE |> Q.INST [`imm8`|->`4w`]
  val pc = get_pc th
  val (th,goal) =
    SPEC_WEAKEN_RULE th ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zHEAP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC heap_inv_IMP_NONE)
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [th,zHEAP_TERMINATE_WITH_ERROR]
  val inv = th |> concl |> find_term (can (match_term ``SOME (x:'a)``))
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val thB = MP th lemma
  val th = zHEAP_ALLOC_TEST_SUCCESS |> Q.INST [`imm8`|->`4w`]
  val lemma = EVAL ``(9 + (2 + SIGN_EXTEND 8 64 (w2n (0x4w:word8))))``
  val th = th |> RW [lemma]
  val lemma = zHEAP_JMP_r13 |> Q.INST [`P`|->`\(sp,vals).
       (vals.reg14 = n2w (8 * needed)) /\ needed <= sp /\ needed < 2 ** 32`]
    |> SIMP_RULE std_ss []
  val th = SPEC_COMPOSE_RULE [th |> SIMP_RULE std_ss [],lemma]
  val inv = th |> concl |> find_term (can (match_term ``SOME (x:'a)``))
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val (th,goal) = SPEC_WEAKEN_RULE th ``(zHEAP
        (cs,x1,x2,x3,x4,refs,stack,s,
         SOME (\(sp,vals). needed <= sp)) * ~zS * zPC ret)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ METIS_TAC [])
  val thA = MP th lemma
  val lemma = SPEC_MERGE |> SPEC_ALL |> Q.INST [`m`|->`SEP_F`]
                         |> RW [SEP_CLAUSES]
  val th = MATCH_MP lemma (CONJ thA thB)
  val inv = ``SOME
           (\(sp:num,vals).
              (vals.reg13 = ret) /\ (vals.reg14 = n2w (8 * needed)) /\
              needed < 4294967296)``
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_CLAUSES,
         SEP_EXISTS_THM,cond_STAR]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ Cases_on `needed <= sp` THEN1
     (DISJ1_TAC
      \\ Q.EXISTS_TAC `vals` \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
      \\ FULL_SIMP_TAC std_ss []) THEN1
     (DISJ2_TAC
      \\ Q.EXISTS_TAC `vals` \\ FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
      \\ FULL_SIMP_TAC std_ss []))
  val th = MP th lemma
  val th = RW [INSERT_UNION_EQ,UNION_EMPTY] th
  val th = th |> DISCH ``needed < 4294967296n``
              |> SIMP_RULE std_ss [] |> UNDISCH_ALL
  val th = RW1 [EQ_SYM_EQ] th
  val th1 = zHEAP_GC |> Q.INST [`r13`|->`ret`,`r14`|->`n2w (8 * needed)`]
  val th = SPEC_COMPOSE_RULE [th1,th]
  val th = SPEC_COMPOSE_RULE [zHEAP_CALL_ALLOC,th]
  (* package up code *)
  val (_,_,c,_) = dest_spec (concl th)
  val tms = find_terms (can (match_term ``(cs.alloc_ptr,xx)``)) c @
            find_terms (can (match_term ``(cs.alloc_ptr+n2w n,xx)``)) c
  val xs = list_dest pred_setSyntax.dest_insert c
  val s = last xs
  fun f tm = can (match_term ``(cs.alloc_ptr, xx:'a)``) tm orelse
             can (match_term ``(cs.alloc_ptr + n2w n, xx:'a)``) tm
  val alloc_instr = filter f (butlast xs)
  val others = filter (not o f) (butlast xs)
  val call = pred_setSyntax.mk_set others
  val alloc = pred_setSyntax.mk_set alloc_instr
              |> subst [``cs.alloc_ptr``|->``p:word64``]
  val alloc_code_def = Define `alloc_code (p:word64) = ^alloc`
  val alloc = ``alloc_code cs.alloc_ptr``
  val code = pred_setSyntax.mk_union(call,pred_setSyntax.mk_union(alloc,s))
  val th = MATCH_MP SPEC_SUBSET_CODE th |> SPEC code
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [alloc_code_def,INSERT_SUBSET,IN_INSERT,IN_UNION]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [SUBSET_DEF,IN_UNION,IN_INSERT] \\ METIS_TAC [])
  val th = MP th lemma
  in th end;

val heap_inv_WEAKEN = prove(
  ``(!sp vals. p (sp,vals) ==> q (sp,vals)) ==>
    heap_inv (cs,x1,x2,x3,x4,refs,stack,s,SOME p) vals ==>
    heap_inv (cs,x1,x2,x3,x4,refs,stack,s,SOME q) vals``,
  FULL_SIMP_TAC std_ss [heap_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [])
  |> GEN_ALL;

val zHEAP_ALLOC = let
  val th1 = zHEAP_ALLOC_FAIL_OR_RETURN
  val th = zHEAP_ALLOC_TEST_FAILURE
  val pc = get_pc th
  val post = th1 |> concl |> rator |> rator |> rand
                 |> subst [``p:word64``|->(pc |> rand)]
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC heap_inv_WEAKEN
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val thGC = SPEC_COMPOSE_RULE [th,th1] |> Q.INST [`imm8`|->`7w`]
  val th = zHEAP_ALLOC_TEST_SUCCESS |> Q.INST [`imm8`|->`7w`]
  val lemma = EVAL ``(9 + (2 + SIGN_EXTEND 8 64 (w2n (0x7w:word8))))``
  val th = th |> RW [lemma]
  val (_,_,c,post) = thGC |> concl |> dest_spec
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma= prove(goal,
    SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ SIMP_TAC std_ss [SEP_DISJ_def] \\ DISJ1_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ MATCH_MP_TAC heap_inv_WEAKEN
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = MATCH_MP SPEC_SUBSET_CODE th |> SPEC c
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [INSERT_SUBSET,IN_INSERT,IN_UNION,EMPTY_SUBSET])
  val th = MP th lemma
  val th1 = thGC |> DISCH_ALL |> SIMP_RULE std_ss [] |> RW [GSYM SPEC_MOVE_COND]
                 |> Q.GEN `ret` |> Q.GEN `vals` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val th2 = th |> Q.GEN `ret` |> Q.GEN `vals` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val lemma = SPEC_MERGE |> SPEC_ALL
    |> Q.INST [`m`|->`SEP_F`,`c1`|->`c2`,`q1`|->`q2`]
    |> RW [SEP_CLAUSES,UNION_IDEMPOT]
  val th = MATCH_MP lemma (CONJ th1 th2)
  val inv = ``\(sp:num,vals). (vals.reg14 = n2w (8 * needed))``
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,SOME ^inv) * ~zS * zPC p *
      cond (needed < 2**32)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,heap_inv_def,SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`vals`,`vals.reg13`,`vals`,`vals.reg13`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ Cases_on `needed <= sp` \\ METIS_TAC [])
  val th = MP th lemma
  in th end;

val zHEAP_ALLOC_CONS_SPACE = let
  val ((set_r14,_,_),_) = prog_x64Lib.x64_spec_memory64 "41BE"
  val lemma = prove(
    ``8 * needed < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (8 * needed)):word32)) MOD 4294967296)) =
       n2w (8 * needed):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(8 * needed) < 4294967296 /\ ~(2147483648 <= 8 * needed)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = set_r14 |> Q.INST [`rip`|->`p`,`imm32`|->`n2w (8 * needed)`] |> RW [lemma]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH T
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals). vals.reg14 = n2w (8 * needed))``
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg14 := n2w (8 * needed)`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [th,zHEAP_ALLOC]
  val th = th |> DISCH_ALL |> SIMP_RULE std_ss [SPEC_MOVE_COND,AND_IMP_INTRO]
  val lemma =
    DECIDE ``8 * needed < 2147483648 /\
             needed < 4294967296 <=> needed < 268435456:num``
  val th = RW [lemma,GSYM SPEC_MOVE_COND] th
  in th end;

(* new ref *)

val heap_store_unused_IMP = prove(
  ``(heap_store_unused a sp x xs = (res,T)) ==>
    (heap_lookup a xs = SOME (Unused (sp - 1))) /\ el_length x <= sp``,
  SRW_TAC [] [heap_store_unused_def]);

val heap_lookup_SPLIT = prove(
  ``!heap a x. (heap_lookup a heap = SOME x) ==>
               ?ys1 ys2. (heap = ys1 ++ [x] ++ ys2) /\ (a = heap_length ys1)``,
  Induct \\ SIMP_TAC std_ss [heap_lookup_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `a = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.EXISTS_TAC `[]` \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11] \\ EVAL_TAC
    \\ SIMP_TAC std_ss [SUM])
  \\ Cases_on `a < el_length h` \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ Q.EXISTS_TAC `h::ys1` \\ FULL_SIMP_TAC (srw_ss()) [APPEND]
  \\ FULL_SIMP_TAC std_ss [heap_length_def,MAP,SUM] \\ DECIDE_TAC);

val x64_heap_heap_expand = prove(
  ``x64_heap a (heap_expand n) b b = one_list_exists a n``,
  Cases_on `n` \\ SIMP_TAC std_ss [x64_heap_def,heap_expand_def,SEP_CLAUSES,
     one_list_exists_def,LENGTH_NIL,one_list_def,ADD1,x64_el_def]);

val heap_length_heap_expand = prove(
  ``heap_length (heap_expand n) = n``,
  Cases_on `n` \\ SIMP_TAC std_ss [heap_length_def,ADD1,MAP] \\ EVAL_TAC
  \\ SIMP_TAC std_ss [SUM,MAP,el_length_def]);

val one_list_exists_ADD = prove(
  ``!m a n. one_list_exists a (m + n) =
            one_list_exists a m * one_list_exists (a + n2w (8 * m)) n``,
  Induct \\ ASM_SIMP_TAC std_ss [one_list_exists_ZERO,SEP_CLAUSES,STAR_ASSOC,
      WORD_ADD_0,ADD_CLAUSES,one_list_exists_SUC,word_arith_lemma1,MULT_CLAUSES]);

val heap_store_unused_STAR = prove(
  ``(heap_store_unused a sp x heap1 = (heap2,T)) ==>
    ?frame.
      let addr = (b + n2w (8 * (a + sp)) - n2w (8 * el_length x)) in
        (x64_heap b heap1 b b = frame * one_list_exists addr (el_length x)) /\
        (x64_heap b heap2 b b = frame * x64_el addr x b b)``,
  SIMP_TAC std_ss [heap_store_unused_def]
  \\ Cases_on `(heap_lookup a heap1 = SOME (Unused (sp - 1)))`
  \\ Cases_on `el_length x <= sp` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [heap_store_lemma]
  \\ Q.PAT_ASSUM `xxx = heap2` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND,x64_heap_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [heap_length_APPEND,el_length_def,x64_el_def]
  \\ FULL_SIMP_TAC std_ss [x64_heap_heap_expand]
  \\ `sp - 1 + 1 = sp` by ALL_TAC THEN1
   (Cases_on `x` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [heap_length_heap_expand]
  \\ `sp = ((sp - el_length x) + el_length x)` by DECIDE_TAC
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
  \\ FULL_SIMP_TAC std_ss [one_list_exists_ADD]
  \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,GSYM word_add_n2w]
  \\ `n2w (sp - el_length x) = n2w sp - n2w (el_length x):word64` by ALL_TAC THEN1
   (`~(sp < el_length x)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [word_arith_lemma2])
  \\ FULL_SIMP_TAC std_ss [WORD_LEFT_SUB_DISTRIB,WORD_LEFT_ADD_DISTRIB]
  \\ Q.EXISTS_TAC `x64_heap b ys1 b b *
       one_list_exists (b + 0x8w * n2w (heap_length ys1)) (sp - el_length x) *
       x64_heap (b + (0x8w * n2w (heap_length ys1) + 0x8w * n2w sp)) ys2 b b`
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC])
  |> SIMP_RULE std_ss [LET_DEF] |> GEN_ALL;

val one_list_exists_2 = prove(
  ``one_list_exists a 2 = SEP_EXISTS x1 x2. one (a,x1:word64) * one (a+8w,x2)``,
  SIMP_TAC std_ss [FUN_EQ_THM,one_list_exists_def,SEP_EXISTS_THM,cond_STAR]
  \\ `!xs. (LENGTH xs = 2) <=> ?x1 x2. xs = [x1;x2:word64]` by ALL_TAC THEN1
   (Cases \\ FULL_SIMP_TAC std_ss [LENGTH,NOT_CONS_NIL] \\ Cases_on `t`
    \\ FULL_SIMP_TAC std_ss [LENGTH,NOT_CONS_NIL,CONS_11,LENGTH_NIL])
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,one_list_def,SEP_CLAUSES]);

val zHEAP_NEW_REF = let
  val th1 = zHEAP_ALLOC_CONS_SPACE |> Q.INST [`needed`|->`2`]
    |> CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV) EVAL)
    |> SIMP_RULE std_ss [SEP_CLAUSES]
  val th = compose_specs [
    "sub r7,16",
    "mov r15d, 65537", (* ref tag *)
    "mov [r7+9],r0",
    "mov [r7+1],r15",
    "mov r0,r7"]
  val pc = get_pc th
  val inv = ``SOME (\(sp,vals:x64_vals). 2 <= sp:num)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals /\
            ~(ptr IN FDOM refs))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,RefPtr ptr,x2,x3,x4,
                                refs |+ (ptr,x1),stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def]
      \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
      \\ FULL_SIMP_TAC std_ss [APPEND]
      \\ `?r heap2. heap_store_unused a sp (RefBlock r) heap = (heap2,T)` by ALL_TAC
      THEN1 (IMP_RES_TAC new_ref_thm \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
      \\ IMP_RES_TAC heap_store_unused_STAR
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `vs.current_heap`)
      \\ FULL_SIMP_TAC std_ss [EVAL ``el_length (RefBlock r)``,one_list_exists_2]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,SEP_CLAUSES,SEP_EXISTS_THM]
      \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,heap_vars_ok_def]
      \\ Q.SPEC_TAC (`a+sp`,`aa`) \\ STRIP_TAC
      \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg7  := vals.reg7 - 16w ;
                                  reg0  := vals.reg7 - 16w ;
                                  reg15 := 0x10001w ;
                                  memory := ((vals.reg7 - 0xFw =+ 0x10001w)
            ((vals.reg7 - 0x7w =+ vals.reg0) vals.memory)) |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ IMP_RES_TAC new_ref_thm \\ NTAC 9 (POP_ASSUM (K ALL_TAC))
    \\ Q.PAT_ASSUM `r1::r2::r3::r4::roots = r::roots2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [CONS_11]
    \\ Q.LIST_EXISTS_TAC [`vs`,`Pointer (a + sp - 2)`,`r2`,`r3`,`r4`,
         `roots`,`heap2`,`a`,`sp-2`] \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (MATCH_MP_TAC (GEN_ALL pop_thm) \\ Q.LIST_EXISTS_TAC [`[x1]`,`[r1]`]
      \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH])
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC heap_store_unused_STAR
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `vs.current_heap`)
    \\ FULL_SIMP_TAC std_ss [EVAL ``el_length (RefBlock r1)``]
    \\ FULL_SIMP_TAC std_ss
         [x64_addr_def,WORD_MUL_LSL,GSYM word_add_n2w,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,GSYM word_add_n2w]
    \\ `(n2w (sp - 2) = n2w sp - 2w:word64) /\
        (n2w (a + sp - 2) = n2w (a + sp) - 2w:word64)` by
     (`~(sp < 2) /\ ~(a + sp < 2)` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma2])
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [x64_el_def,RefBlock_def,x64_payload_def,
         LET_DEF,LENGTH,SEP_CLAUSES,MAP,one_list_def,word_arith_lemma1,
         EVAL ``0x1w << 16 + 0x1w:word64``,one_list_exists_2,SEP_EXISTS_THM]
    \\ Q.ABBREV_TAC `dm = vals.memory_domain`
    \\ Q.ABBREV_TAC `m = vals.memory`
    \\ SEP_W_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv) * ~zS * zPC p *
      cond (~(ptr IN FDOM refs))``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [th1,th]
  in th end;

(* cons *)

val (x64_cons_loop_res, x64_cons_loop_def, x64_cons_loop_pre_def) = x64_compile `
  x64_cons_loop (r7,r14:word64,r15:word64,dm:word64 set,m:word64->word64,ss) =
    let (r0,ss) = (HD ss, TL ss) in
    let r7 = r7 - 8w in
    let m = (r7 + 1w =+ r0) m in
    let r15 = r15 - 1w in
      if r15 <> 0w then
          x64_cons_loop (r7,r14,r15,dm,m,ss)
      else
        let r7 = r7 - 8w in
        let m = (r7 + 1w =+ r14) m in
        let r0 = r7 in
          (r0,r7,r14,r15,dm,m,ss)`

val (x64_cons_res, x64_cons_def, x64_cons_pre_def) = x64_compile `
  x64_cons (r0,r7,r14,dm,m,ss) =
    let r15 = r14 >>> 16 in
    let (r0,r7,r14,r15,dm,m,ss) = x64_cons_loop (r7,r14,r15,dm,m,ss) in
      (r0,r7,r14,r15,dm,m,ss)`

val blast_lemma = blast_align_lemma;

val one_list_exists_1 = prove(
  ``one_list_exists a 1 = SEP_EXISTS x. one (a,x)``,
  ONCE_REWRITE_TAC [GSYM (EVAL ``SUC 0``)]
  \\ REWRITE_TAC [one_list_exists_SUC,one_list_exists_ZERO,SEP_CLAUSES]);

val x64_cons_loop_thm = prove(
  ``!xs m r.
      (one_list_exists r7 (SUC (LENGTH xs)) * r) (fun2set (m,dm)) /\ xs <> [] /\
      LENGTH xs < dimword (:64) /\ (r7 && 7w = 0w) ==>
      ?m1. (x64_cons_loop_pre (r7 + n2w (LENGTH xs * 8 + 8) - 1w,r14,
                               n2w (LENGTH xs),dm,m,xs++ss)) /\
           (x64_cons_loop (r7 + n2w (LENGTH xs * 8 + 8) - 1w,r14,
                           n2w (LENGTH xs),dm,m,xs++ss) =
             (r7 - 1w,r7 - 1w,r14,0w,dm,m1,ss)) /\
           (one_list r7 (r14::REVERSE xs) * r) (fun2set (m1,dm))``,
  Induct \\ STRIP_TAC
  \\ SIMP_TAC std_ss [NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [LENGTH,MULT_CLAUSES,LENGTH_SNOC]
  \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [x64_cons_loop_def, x64_cons_loop_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF,ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs < dimword (:64)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,LENGTH_NIL,HD,TL,
       APPEND,NOT_CONS_NIL]
  \\ Cases_on `xs = []` \\ FULL_SIMP_TAC std_ss [one_list_exists_2,LENGTH] THEN1
   (FULL_SIMP_TAC std_ss [SEP_EXISTS_THM,SEP_CLAUSES,one_list_def,SNOC_APPEND,
      APPEND,REVERSE_DEF,TL]
    \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SEP_R_TAC \\ SEP_W_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `0x7w && r7 = 0x0w` MP_TAC
    \\ blastLib.BBLAST_TAC)
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [word_arith_lemma3]
  \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [word_arith_lemma4]
  \\ ASM_SIMP_TAC std_ss [blast_lemma]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma4,GSYM word_mul_n2w]
  \\ SEP_I_TAC "x64_cons_loop"
  \\ FULL_SIMP_TAC std_ss [one_list_exists_ADD,one_list_exists_1,ADD1]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,LEFT_ADD_DISTRIB,word_add_n2w,
       word_mul_n2w,SEP_EXISTS_THM,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  \\ SEP_W_TAC \\ POP_ASSUM MP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`one (r7 + n2w (8 + LENGTH (xs:word64 list) * 8),h) * r`,`x'`])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC std_ss [REVERSE_DEF,one_list_def,one_list_APPEND,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE,GSYM word_mul_n2w,GSYM word_add_n2w,
       AC WORD_ADD_COMM WORD_ADD_ASSOC, AC WORD_MULT_COMM WORD_MULT_ASSOC]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val LENGTH_APPEND_11 = prove(
  ``!xs xs1 ys ys1.
     (LENGTH xs = LENGTH xs1) ==>
     ((xs ++ ys = xs1 ++ ys1) <=> (xs = xs1) /\ (ys = ys1))``,
  Induct \\ Cases_on `xs1`  \\ SRW_TAC [] [] \\ METIS_TAC []);

val cons_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x5,r5);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM]

val cons_rev_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`(ZIP(xs,ys))`,`REVERSE (ZIP(xs,ys))`]
  |> DISCH ``LENGTH (xs:bc_value list) = LENGTH (ys:'a word heap_address list)``
  |> SIMP_RULE std_ss [rich_listTheory.MAP_REVERSE,MAP_FST_ZIP]
  |> SIMP_RULE std_ss [SUBSET_DEF,MEM_REVERSE]

val zHEAP_BIG_CONS = let
  val ((set_r14,_,_),_) = prog_x64Lib.x64_spec_memory64 "41BE"
  val lemma = prove(
    ``imm < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (imm)):word32)) MOD 4294967296)) =
       n2w (imm):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(imm) < 4294967296 /\ ~(2147483648 <= imm)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = set_r14 |> Q.INST [`rip`|->`p`,`imm32`|->`n2w (imm)`] |> RW [lemma]
  val th = th |> Q.INST [`imm`|->`w2n (imm64:word64)`] |> RW [n2w_w2n]
  val th = SPEC_COMPOSE_RULE [th,x64_cons_res]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
              |> UNDISCH
  val pc = get_pc th
  val inv = ``SOME (\(sp,vals:x64_vals). l+1 <= sp:num)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^inv) vals /\
            (imm64:word64 = n2w l << 16 + n2w (n MOD 2 ** 12) << 4) /\
            l <= LENGTH stack /\ l < 2 ** 15 /\ l <> 0)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Block n (REVERSE (TAKE l stack)),x2,x3,x4,refs,
                                DROP l stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ `LENGTH roots = LENGTH stack` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND])
    \\ `l <= LENGTH roots` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ Q.MATCH_ASSUM_RENAME_TAC `stack = zs1 ++ zs2` []
    \\ FULL_SIMP_TAC std_ss []
    \\ `abs_ml_inv (zs1 ++ ([x1; x2; x3; x4] ++ zs2)) refs
         (ys1 ++ ([r1; r2; r3; r4] ++ ys2),heap,a,sp) cs.heap_limit` by
     (FULL_SIMP_TAC std_ss [APPEND_ASSOC]
      \\ MATCH_MP_TAC (move_thm |> Q.SPECL [`[]`,`[]`] |> RW [APPEND,LENGTH])
      \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ `abs_ml_inv (REVERSE zs1 ++ ([x1; x2; x3; x4] ++ zs2)) refs
        (REVERSE ys1 ++ ([r1; r2; r3; r4] ++ ys2),heap,a,sp) cs.heap_limit` by
      (POP_ASSUM MP_TAC \\ MATCH_MP_TAC cons_rev_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ STRIP_TAC
    \\ IMP_RES_TAC (cons_thm |> Q.INST [`stack`|->`x::ts ++ ys`])
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM MP_TAC
    \\ `l < sp` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `n`)
    \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EVAL ``el_length (BlockRep n rs)``]
    \\ Q.ABBREV_TAC `header = n2w l << 16 + (n2w (n MOD 4096) << 4) : word64`
    \\ `(TAKE l (zs1 ++ zs2) = zs1) /\ (DROP l (zs1 ++ zs2) = zs2)` by ALL_TAC
    THEN1 METIS_TAC [rich_listTheory.TAKE_LENGTH_APPEND,
                     rich_listTheory.DROP_LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss []
    \\ `(rs = REVERSE ys1) /\ (roots2 = [r1; r2; r3; r4] ++ ys2)` by
          METIS_TAC [LENGTH_APPEND_11,LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE] \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ `w2n header < 2147483648 /\ (header >>> 16 = n2w l)` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,w2n_n2w]
      \\ `n MOD 4096 < 4096` by FULL_SIMP_TAC std_ss [MOD_LESS]
      \\ `(65536 * l + 16 * n MOD 4096) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `n MOD 4096 < 4096` by FULL_SIMP_TAC std_ss [MOD_LESS]
      \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w,EVAL ``dimword(:64)``]
      \\ `(65536 * l + 16 * n MOD 4096) < 18446744073709551616 /\
          l < 18446744073709551616` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [MULT_COMM]
      \\ MATCH_MP_TAC (DIV_MULT |> SIMP_RULE std_ss [PULL_FORALL])
      \\ DECIDE_TAC)
    \\ ONCE_REWRITE_TAC [x64_cons_def,x64_cons_pre_def]
    \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ IMP_RES_TAC heap_store_unused_STAR
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `vs.current_heap`)
    \\ FULL_SIMP_TAC std_ss [EVAL ``el_length (BlockRep n ys1)``]
    \\ FULL_SIMP_TAC std_ss [MAP_APPEND,GSYM APPEND_ASSOC,APPEND]
    \\ Q.ABBREV_TAC `ts1 = MAP (x64_addr vs.current_heap) ys1`
    \\ Q.ABBREV_TAC `ts2 = MAP (x64_addr vs.current_heap) ys2 ++
                           0x1w::cs.ret_address::cs.rest_of_stack`
    \\ Q.ABBREV_TAC `r7 = vs.current_heap + n2w (8 * (a + sp)) -
                          n2w (LENGTH ts1 * 8 + 8)`
    \\ `vs.current_heap + n2w (8 * (a + sp)) - 0x1w =
        r7 + n2w (LENGTH ts1 * 8 + 8) - 0x1w` by ALL_TAC
    THEN1 (UNABBREV_ALL_TAC \\ SIMP_TAC std_ss [WORD_SUB_ADD])
    \\ `l = LENGTH ts1` by METIS_TAC [LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss []
    \\ `(vs.current_heap + n2w (8 * (a + sp)) -
          n2w (8 * (LENGTH ts1 + 1))) = r7` by ALL_TAC
    THEN1 (UNABBREV_ALL_TAC \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB]
           \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC])
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (x64_cons_loop_thm |> GEN_ALL)
    \\ SEP_I_TAC "x64_cons_loop"
    \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH_REVERSE] \\ SEP_F_TAC
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ FULL_SIMP_TAC std_ss [EVAL ``dimword (:64)``,GSYM LENGTH_NIL,LENGTH_MAP]
      \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ Q.PAT_ASSUM `heap_vars_ok vs`  MP_TAC
      \\ SIMP_TAC std_ss [GSYM MULT_CLAUSES]
      \\ SIMP_TAC std_ss [heap_vars_ok_def,GSYM word_mul_n2w,GSYM word_add_n2w]
      \\ FULL_SIMP_TAC std_ss [blast_lemma])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg0 := r7 - 1w ;
                                  reg7 := r7 - 1w ;
                                  reg14 := header ;
                                  reg15 := 0w ;
                                  memory := m1 ;
                                  stack := ts2 |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,zVALS_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
    \\ SIMP_TAC (srw_ss()++star_ss) [] \\ STRIP_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`Pointer (a + sp - (LENGTH ys1 + 1))`,`r2`,`r3`,
        `r4`,`ys2`,`heap2`,`a`,`sp - (LENGTH ys1 + 1)`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def] \\ Q.UNABBREV_TAC `ts2`
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ STRIP_TAC THEN1
     (MATCH_MP_TAC (GEN_ALL cons_lemma)
      \\ Q.LIST_EXISTS_TAC [`x1`,`r1`]
      \\ Q.PAT_ASSUM `abs_ml_inv (Block n (REVERSE zs1)::x1::x2::x3::x4::zs2) refs
           (Pointer (a + sp - (LENGTH ys1 + 1))::r1::r2::r3::r4::ys2,
            heap2,a,sp - (LENGTH ys1 + 1)) cs.heap_limit` MP_TAC
      \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (UNABBREV_ALL_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,WORD_MUL_LSL]
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w,GSYM word_add_n2w]
      \\ `(n2w (sp - (LENGTH ys1 + 1)) = n2w sp - n2w (LENGTH ys1 + 1):word64) /\
          (n2w (a + sp - (LENGTH ys1 + 1)) =
           n2w (a + sp) - n2w (LENGTH ys1 + 1):word64)` by ALL_TAC THEN1
       (SIMP_TAC std_ss [word_arith_lemma2]
        \\ SRW_TAC [] [] \\ `F` by DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LEFT_ADD_DISTRIB]
      \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC,
                               AC WORD_MULT_COMM WORD_MULT_ASSOC])
    \\ `LENGTH ts1 < 281474976710656` by ALL_TAC THEN1
      (UNABBREV_ALL_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_MAP] \\ DECIDE_TAC)
    \\ Q.UNABBREV_TAC `ts1`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_el_def,BlockRep_def,x64_payload_def,
         LET_DEF,one_list_def,cond_STAR,LENGTH_REVERSE]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [rich_listTheory.MAP_REVERSE])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [Once cond_CONJ,STAR_ASSOC] th
           |> RW1 [SPEC_MOVE_COND] |> UNDISCH
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^inv) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th1 = zHEAP_ALLOC_CONS_SPACE |> Q.INST [`needed`|->`l+1`]
    |> CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV) EVAL)
    |> SIMP_RULE std_ss [SEP_CLAUSES]
    |> RW1 [SPEC_MOVE_COND] |> UNDISCH
  val th = SPEC_COMPOSE_RULE [th1,th]
  in th end;

(* deref *)

val zHEAP_DEREF = let
  val th = compose_specs ["mov r0,[r0+9w]"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ isRefPtr x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,refs ' (getRefPtr x1),x2,x3,x4,
                                refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isRefPtr_def,APPEND]
    \\ IMP_RES_TAC deref_thm
    \\ `abs_ml_inv (refs ' n::x2::x3::x4::stack) refs
         (y::r2::r3::r4::roots,heap,a,sp) cs.heap_limit` by ALL_TAC
    THEN1 (MATCH_MP_TAC (cons_lemma |> GEN_ALL) \\ METIS_TAC [])
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ STRIP_TAC
    \\ Q.PAT_ASSUM `heap_el r 0 heap = (y,T)` (ASSUME_TAC o GSYM)
    \\ Q.PAT_ASSUM `r1::r2::r3::r4::roots = r::roots2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [heap_el_def,CONS_11]
    \\ `?f. (r1 = Pointer (f ' n)) /\ bc_ref_inv n refs (f,heap)` by ALL_TAC THEN1
      (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def,
        bc_value_inv_def] \\ Q.LIST_EXISTS_TAC [`f`]
      \\ ASM_SIMP_TAC std_ss []
      \\ `reachable_refs (RefPtr n::x2::x3::x4::stack) refs n` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [reachable_refs_def,MEM]
        \\ Q.LIST_EXISTS_TAC [`RefPtr n`,`n`]
        \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,RTC_REFL])
      \\ RES_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_el_def,bc_ref_inv_def,RefBlock_def]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC heap_lookup_SPLIT
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [word_arith_lemma3,word_mul_n2w,
        AC MULT_COMM MULT_ASSOC] \\ SEP_R_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ SIMP_TAC std_ss [blast_lemma] \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_mul_n2w,
         AC MULT_COMM MULT_ASSOC] \\ SEP_R_TAC
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg0 := x64_addr vs.current_heap y' |>`
    \\ FULL_SIMP_TAC std_ss [zVALS_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`y'`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [getRefPtr_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ Q.PAT_ASSUM `xxx (fun2set (vals.memory,vals.memory_domain))` MP_TAC
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,heap_length_APPEND,SUM,MAP,
         LEFT_ADD_DISTRIB,word_add_n2w,AC ADD_COMM ADD_ASSOC,heap_length_def]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) []
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,heap_length_APPEND,SUM,MAP,
         LEFT_ADD_DISTRIB,word_add_n2w,AC ADD_COMM ADD_ASSOC,heap_length_def]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) []
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isRefPtr x1)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  in th end;

(* update ref *)

val zHEAP_UPDATE_REF = let
  val th = compose_specs ["mov [r1+9w],r0"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ isRefPtr x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,
                                refs |+ (getRefPtr x2,x1),stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isRefPtr_def,APPEND]
    \\ IMP_RES_TAC update_ref_thm
    \\ Q.PAT_ASSUM `rrroots = r::Pointer p'::roots2` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [heap_el_def,CONS_11]
    \\ `?f. (r2 = Pointer (f ' n)) /\ bc_ref_inv n refs (f,heap)` by ALL_TAC THEN1
     (Q.PAT_ASSUM `abs_ml_inv (x1::RefPtr n::x3::x4::stack) (refs |+ (n,x1))
         (r1::r2::r3::r4::roots,heap2,a,sp) cs.heap_limit` (K ALL_TAC)
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def,
           bc_value_inv_def] \\ Q.LIST_EXISTS_TAC [`f`]
      \\ ASM_SIMP_TAC std_ss []
      \\ `reachable_refs (x1::RefPtr n::x3::x4::stack) refs n` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [reachable_refs_def,MEM]
        \\ Q.LIST_EXISTS_TAC [`RefPtr n`,`n`]
        \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM,RTC_REFL])
      \\ RES_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_store_def]
    \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def]
    \\ IMP_RES_TAC heap_lookup_SPLIT
    \\ FULL_SIMP_TAC std_ss [heap_el_def,bc_ref_inv_def,RefBlock_def]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL]
    \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [word_arith_lemma3,word_mul_n2w,
        AC MULT_COMM MULT_ASSOC] \\ SEP_R_TAC
      \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ SIMP_TAC std_ss [blast_lemma] \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def])
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_mul_n2w,
         AC MULT_COMM MULT_ASSOC] \\ SEP_R_TAC
    \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `addr = vs.current_heap + n2w (heap_length ys1 * 8) + 0x8w`
    \\ Q.EXISTS_TAC `vals with <| memory :=
         (addr =+ x64_addr vs.current_heap r1) vals.memory |>`
    \\ FULL_SIMP_TAC std_ss [zVALS_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ Q.UNABBREV_TAC `addr`
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ SIMP_TAC (srw_ss()) [getRefPtr_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap2`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,x64_addr_def,
         WORD_MUL_LSL,word_mul_n2w] \\ SIMP_TAC (srw_ss()) []
    \\ Q.PAT_ASSUM `xxx = (heap2,T)` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [heap_store_lemma]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_heap_APPEND,x64_heap_def,x64_el_def,
         x64_payload_def,SEP_CLAUSES,cond_STAR,MAP,LET_DEF,LENGTH,one_list_def,
         x64_addr_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
    \\ Q.ABBREV_TAC `m = vals.memory`
    \\ Q.ABBREV_TAC `dm = vals.memory_domain`
    \\ SEP_W_TAC \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [heap_length_APPEND,heap_length_def,el_length_def
         ,MAP,SUM] \\ FULL_SIMP_TAC (srw_ss()++star_ss) [AC MULT_COMM MULT_ASSOC]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isRefPtr x2)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  in th end;

(* swap *)

val swap_lemma =
  abs_ml_inv_stack_permute |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO]
  |> Q.SPECL [`[(x1i,r1i);(x2i,r2i);(x3i,r3i);(x4i,r4i)]`,
              `[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM]

val zHEAP_SWAP = let
  val th = compose_specs ["mov r15,r0","mov r0,r1","mov r1,r15"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x2,x1,x3,x4,
                                refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals with <| reg0 := vals.reg1 ; reg1 := vals.reg0;
                                  reg15 := vals.reg0 |>`
    \\ REVERSE STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def])
    \\ POP_ASSUM (K ALL_TAC) \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r2`,`r1`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `abs_ml_inv xx yy tt rr` MP_TAC
    \\ MATCH_MP_TAC swap_lemma \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES]);
  val th = MP th lemma
  in th end;


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
        \\ `w2w (0x2w * (n2w (Num i)):63 word) << 1 && 0x1w = 0x0w:word64` by
              blastLib.BBLAST_TAC \\ FULL_SIMP_TAC std_ss []
        \\ FULL_SIMP_TAC std_ss [small_int_def]
        \\ `(w2w (0x2w * n2w (Num i):63 word) << 1 = 0x0w:word64) = (i = 0)` by
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

val num_eq_def = Define `
  num_bool x y = Number (if x = y then 1 else 0)`;

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
val zHEAP_Lt  = get_INT_OP ``2:num``;
val zHEAP_Eq  = get_INT_OP ``3:num``;
val zHEAP_Mul = get_INT_OP ``4:num``;
val zHEAP_Div = get_INT_OP ``5:num``;
val zHEAP_Mod = get_INT_OP ``6:num``;
val zHEAP_Dec = get_INT_OP ``7:num``;

(* ret *)

val ret_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4);(x5,r5)]`,
              `[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM,DISJ_IMP] |> GEN_ALL

val zHEAP_RET = let
  val th = x64_ret
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            stack <> [] /\ isCodePtr (HD stack))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,x1,x2,x3,x4,refs,TL stack,s,NONE) * ~zS *
     zPC (2w * n2w (getCodePtr (HD stack)))`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    Cases_on `stack` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,HD,TL]
    \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [isCodePtr_def]
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [Once heap_inv_def,getCodePtr_def]
    \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [])
    \\ `?rs. (roots = Data (n2w n) :: rs)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
        APPEND,EVERY2_def] \\ Cases_on `roots`
      \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def,bc_value_inv_def,CONS_11])
    \\ FULL_SIMP_TAC std_ss [APPEND,HD,TL,MAP]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| stack := TL vals.stack |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ `x64_addr vs.current_heap (Data (n2w n)) = 2w * n2w n` by ALL_TAC THEN1
     (SIMP_TAC (srw_ss()) [x64_addr_def,WORD_MUL_LSL,w2w_def,word_mul_n2w,w2n_n2w]
      \\ FULL_SIMP_TAC (srw_ss()) [MOD_COMMON_FACTOR])
    \\ FULL_SIMP_TAC std_ss [TL]
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [x64_addr_def]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM APPEND_ASSOC,APPEND])
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`rs`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC ret_lemma \\ METIS_TAC [])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (stack <> [] /\ isCodePtr (HD stack))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;


(* call R15 *)

val zHEAP_CALL_R15 = let
  val th = x64_call_r15
  val th = SPEC_FRAME_RULE th ``~zS``
  val ss = ``SOME (\(sp:num,vals). vals.reg15 = r15)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^ss) vals /\ EVEN (w2n (p + 3w)))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,
                           CodePtr ((w2n (p+3w:word64)) DIV 2)::stack,s,NONE) * ~zS *
                           zPC r15`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals with stack := (p+3w) :: vals.stack`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ cheat)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^ss) * ~zS * zPC p * cond (EVEN (w2n (p + 3w)))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;


(* load equal_ptr *)

val zHEAP_LOAD_EQUAL_PTR = let
  val th = spec "mov r15, [r9+64]"
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 64w) = cs.equal_ptr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals). (cs.equal_ptr = vals.reg15))``
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
    \\ Q.EXISTS_TAC `vals with <| reg15 := cs.equal_ptr |>`
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
  in GSYM th end;


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


(* full EQUAL *)

val EVEN_w2n = prove(
  ``!w. EVEN (w2n w) = ~(w ' 0)``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [word_index,ZERO_LT_dimword,bitTheory.BIT_def,
    bitTheory.BITS_THM,EVEN_MOD2]
  \\ `n MOD 2 < 2` by FULL_SIMP_TAC std_ss [MOD_LESS]
  \\ DECIDE_TAC);

val EVEN_w2n_IMP = prove(
  ``!w. EVEN (w2n w) ==> (0x2w * n2w (w2n w DIV 2) = (w:word64))``,
  SIMP_TAC std_ss [EVEN_w2n,n2w_w2n,
    GSYM (w2n_lsr |> Q.SPECL [`w`,`1`] |> SIMP_RULE std_ss [])]
  \\ blastLib.BBLAST_TAC);

val zHEAP_EQUAL = let
  val th1 = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_LOAD_EQUAL_PTR,zHEAP_CALL_R15]
  val th = SPEC_COMPOSE_RULE [zHEAP_RAW_EQUAL,zHEAP_RET]
  val (_,_,code,_) = dest_spec (concl th)
  val equal_code_def = Define `equal_code (p:word64) = ^code`
  val th = RW [GSYM equal_code_def] th
  val th = SPEC_COMPOSE_RULE [th1,th]
  val lemma = prove(
    ``EVEN (w2n (w + 12w)) = EVEN (w2n (w:word64))``,
    SIMP_TAC std_ss [EVEN_w2n] \\ blastLib.BBLAST_TAC);
  val th = th |> RW [TL,HD,getCodePtr_def,NOT_CONS_NIL,isCodePtr_def,SEP_CLAUSES]
              |> SIMP_RULE (std_ss++sep_cond_ss) [EVEN_w2n_IMP,SPEC_MOVE_COND]
              |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val th = SPEC_COMPOSE_RULE [zHEAP_POP2,th] |> RW [lemma]
  in th end


(* jmp pointer *)

val zHEAP_JMP_PTR = let
  val th = spec "jmp r1"
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ isCodePtr x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS *
                         zPC (n2w (2 * getCodePtr x2))`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals` \\ FULL_SIMP_TAC std_ss []
    \\ `n2w (2 * getCodePtr x2) = vals.reg1` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zVALS_def]
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isCodePtr_def,getCodePtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [abs_ml_inv_def,bc_stack_ref_inv_def,
          EVERY2_def,bc_value_inv_def,x64_addr_def,w2w_def,WORD_MUL_LSL]
    \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
    \\ FULL_SIMP_TAC (srw_ss()) [n2w_11]
    \\ FULL_SIMP_TAC (srw_ss()) [MOD_COMMON_FACTOR])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p * cond (isCodePtr x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th1 = zHEAP_MOVE_12
  val th2 = zHEAP_POP1
  val th = SPEC_COMPOSE_RULE [th1,th2,th]
  in th end;


(* call pointer *)

val zHEAP_CALL_2 = let
  val th = x64_call_r1
  val th = SPEC_FRAME_RULE th ``~zS``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            EVEN (w2n (p + 3w)) /\ isCodePtr x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,
                           CodePtr ((w2n (p+3w:word64)) DIV 2)::stack,s,NONE) * ~zS *
                           zPC (n2w (2 * getCodePtr x2))`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals with stack := (p+3w) :: vals.stack`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ cheat)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p *
      cond (EVEN (w2n (p + 3w)) /\ isCodePtr x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;

val zHEAP_CALL_PTR =
  SPEC_COMPOSE_RULE [zHEAP_MOVE_12,zHEAP_POP1,zHEAP_CALL_2]


(* call instruction *)

val EVEN_LEMMA = prove(
  ``EVEN n ==> (2 * (n DIV 2) = n:num)``,
  SIMP_TAC std_ss [RW1 [MULT_COMM] EVEN_EXISTS]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MULT_DIV]
  \\ SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC]);

val zHEAP_CALL_IMM = let
  val th = x64_call_imm
  val th = th |> RW [GSYM IMM32_def] |> Q.INST [`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``~zS``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            EVEN (w2n (p+6w:word64)))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,
                           CodePtr ((w2n (p+6w:word64)) DIV 2)::stack,s,NONE) * ~zS *
                           zPC (p + 0x6w + sw2sw (imm32:word32))`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals with stack := (p+6w) :: vals.stack`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,
         `Data (n2w ((w2n (p + 6w:word64) DIV 2))) :: roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [MAP,MAP_APPEND,x64_addr_def,CONS_11]
    \\ SIMP_TAC std_ss [WORD_MUL_LSL,w2w_def,n2w_w2n,word_mul_n2w,w2n_n2w]
    \\ `(w2n (p + 0x6w) DIV 2) < dimword (:63)` by ALL_TAC THEN1
     (SIMP_TAC std_ss [DIV_LT_X] \\ EVAL_TAC
      \\ ASSUME_TAC (w2n_lt |> INST_TYPE [``:'a``|->``:64``])
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [EVEN_LEMMA]
    \\ SIMP_TAC std_ss [n2w_w2n]
    \\ FULL_SIMP_TAC (srw_ss()) [abs_ml_inv_def,roots_ok_def,MEM]
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
    \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss [EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
    \\ REPEAT STRIP_TAC
    \\ FIRST_ASSUM MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
    \\ Q.EXISTS_TAC `x` \\ Q.EXISTS_TAC `r` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MEM]
    \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p *
      cond (EVEN (w2n (p + 6w)))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;


(* load pointer *)

val sw2sw_lemma =
  sw2sw_def |> INST_TYPE [``:'a``|->``:32``,``:'b``|->``:64``]
            |> SIMP_RULE (srw_ss()) [] |> GSYM

val zHEAP_LOAD_PTR = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64 "4805"
  val th = HIDE_STATUS_RULE true sts th
  val th = th |> Q.INST [`rip`|->`p`]
  val th = RW [GSYM IMM32_def,sw2sw_lemma] th
  val th1 = x64_call_imm |> Q.INST [`imm32`|->`0w`]
      |> RW [EVAL ``(sw2sw:word32->word64) 0w``,EVAL ``IMM32 0w``,WORD_ADD_0]
  val th1 = SPEC_COMPOSE_RULE [th1,x64_pop_r0]
  val th1 = SIMP_RULE std_ss [NOT_CONS_NIL,TL,HD,SEP_CLAUSES] th1
  val th = SPEC_COMPOSE_RULE [th1,th]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            EVEN (w2n (p + 0x6w + sw2sw (imm32:word32))))``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,CodePtr (w2n ((p:word64) + 6w + sw2sw (imm32:word32)) DIV 2),x2,x3,
            x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg0 := p + 0x6w + sw2sw imm32`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`,`f`]
    \\ FULL_SIMP_TAC std_ss [APPEND,EVERY2_def,x64_addr_def,roots_ok_def]
    \\ FULL_SIMP_TAC (srw_ss()) [MEM] \\ STRIP_TAC THEN1 METIS_TAC []
    \\ REPEAT STRIP_TAC THEN1
     (FIRST_ASSUM MATCH_MP_TAC
      \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
      \\ Q.LIST_EXISTS_TAC [`x`,`r`] \\ FULL_SIMP_TAC std_ss []
      \\ NTAC 2 (POP_ASSUM MP_TAC)
      \\ FULL_SIMP_TAC std_ss [MEM]
      \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM])
    \\ SIMP_TAC std_ss [w2w_def,WORD_MUL_LSL,word_mul_n2w,w2n_n2w]
    \\ `(w2n (p + sw2sw (imm32:word32) + 0x6w) DIV 2) < dimword (:63)` by
     (SIMP_TAC std_ss [DIV_LT_X] \\ EVAL_TAC
      \\ ASSUME_TAC (w2n_lt |> INST_TYPE [``:'a``|->``:64``])
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [EVEN_LEMMA,n2w_w2n])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (EVEN (w2n (p + 0x6w + sw2sw (imm32:word32))))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;


(* collection of all code abbreviations *)

val code_abbrevs_def = Define `
  code_abbrevs cs =
    bignum_code cs.bignum_ptr UNION
    alloc_code cs.alloc_ptr UNION
    equal_code cs.equal_ptr UNION
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
val zBC_Deref = zHEAP_DEREF |> fix_code
val zBC_Tick = zHEAP_NOP2 |> fix_code
val zBC_Equal = zHEAP_EQUAL |> fix_code
val zBC_Update = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_UPDATE_REF,zHEAP_POP1] |> fix_code
val zBC_Return = zHEAP_RET |> fix_code
val zBC_PrintC = zHEAP_PUT_CHAR |> fix_code

val zBC_Jump = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "48E9"
  val th = th |> RW [GSYM IMM32_def] |> Q.INST [`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS``
  in th end |> fix_code

val zBC_JumpIf = let
  val SPEC_IF = prove(
    ``SPEC m (p * precond b) c (q q1 * t) /\ SPEC m (p * precond ~b) c (q q2 * t) ==>
      SPEC m p c (q (if b then q1 else q2) * t)``,
    Cases_on `b` \\ FULL_SIMP_TAC std_ss [precond_def,SEP_CLAUSES]);
  fun the (SOME x) = x | the _ = fail()
  val th1 = zHEAP_CMP_FALSE
  val th2 = zHEAP_POP1
  val ((th3,_,_),th3i) = prog_x64Lib.x64_spec_memory64 "0F85"
  val (th3i,_,_) = the th3i
  val th3 = MATCH_MP SPEC_IF (CONJ th3i th3)
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val th = RW [GSYM word_add_n2w] th
  in th end |> fix_code

val zBC_JumpPtr = zHEAP_JMP_PTR |> fix_code
val zBC_CallPtr = zHEAP_CALL_PTR |> fix_code
val zBC_Call = zHEAP_CALL_IMM |> fix_code
val zBC_PushPtr = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_LOAD_PTR] |> fix_code
val zBC_PushExc = zBC_PushExc |> fix_code
val zBC_PopExc = zBC_PopExc |> fix_code


(* translation function *)

val small_offset_def = Define `
  small_offset n x =
    if n < 268435456:num then x else ^(get_code zBC_Error)`;

val x64_def = Define `
  (x64 i (Stack Pop) = ^(get_code zBC_Pop)) /\
  (x64 i (Stack (Pops k)) = small_offset k ^(get_code zBC_Pops)) /\
  (x64 i (Stack (Load k)) = small_offset k ^(get_code zBC_Load)) /\
  (x64 i (Stack (Store k)) = small_offset k ^(get_code zBC_Store)) /\
  (x64 i (Stack Equal) = ^(get_code zBC_Equal)) /\
  (x64 i (Jump (Addr l)) =
     small_offset l (small_offset i
       (let imm32 = n2w (2 * l) - n2w i - 6w in ^(get_code zBC_Jump)))) /\
  (x64 i (JumpIf (Addr l)) =
     small_offset l (small_offset i
       (let imm32 = n2w (2 * l) - n2w i - 12w in ^(get_code zBC_JumpIf)))) /\
  (x64 i (JumpPtr) = ^(get_code zBC_JumpPtr)) /\
  (x64 i (Call (Addr l)) =
     small_offset l (small_offset i
       (let imm32 = n2w (2 * l) - n2w i - 6w in ^(get_code zBC_Call)))) /\
  (x64 i (PushPtr (Addr l)) =
     small_offset l (small_offset i
       (let imm32 = n2w (2 * l) - n2w i - 8w in ^(get_code zBC_PushPtr)))) /\
  (x64 i (CallPtr) = ^(get_code zBC_CallPtr)) /\
  (x64 i (Return) = ^(get_code zBC_Return)) /\
  (x64 i (Ref) = ^(get_code zBC_Ref)) /\
  (x64 i (Deref) = ^(get_code zBC_Deref)) /\
  (x64 i (Update) = ^(get_code zBC_Update)) /\
  (x64 i (PopExc) = ^(get_code zBC_PopExc)) /\
  (x64 i (PushExc) = ^(get_code zBC_PushExc)) /\
  (x64 i (Label l) = []) /\
  (x64 i (Tick) = ^(get_code zBC_Tick)) /\
  (x64 i (PrintC c) =
     (let c = n2w (ORD c):word8 in ^(get_code zBC_PrintC))) /\
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
  (bc_adjust (cb,sb,ev) (CodePtr p) =
     CodePtr ((w2n (cb:word64) DIV 2) + p)) /\
  (bc_adjust (cb,sb,ev) (StackPtr i) =
     StackPtr ((w2n ((sb:word64) - n2w (8 * i)) DIV 2))) /\
  (bc_adjust (cb,sb,ev) (Number n) = Number n) /\
  (bc_adjust (cb,sb,ev) (RefPtr r) =
     RefPtr (if ev then 2 * r else 2 * r + 1)) /\
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
                  s with <| output := out ++ bs.output ;
                            handler := bs.handler + SUC (LENGTH stack) |>,NONE)`;

(*
  no tracking for the following:
    cons_names : (num # conN id) list;
*)

fun prepare th = let
  val th = if can (find_term (fn tm => tm = ``zS``)) (concl th)
           then th else SPEC_FRAME_RULE th ``~zS``
  val th = th
    |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
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
  in th end

val IMP_small_offset = prove(
  ``(z = s1.output) /\
    (n < 268435456 ==>
     SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR (cs,STRCAT out z))) ==>
    SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), small_offset n xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR (cs,STRCAT out z))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [small_offset_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [x64_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
  \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) []
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Error) |> SPEC_ALL
                |> DISCH_ALL |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO]
                |> Q.INST [`base`|->`cb`])
  \\ FULL_SIMP_TAC (srw_ss()) [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]);

val EXISTS_NOT_FDOM_NUM = prove(
  ``!f. ?m:num. ~(m IN FDOM f)``,
  METIS_TAC [IN_INFINITE_NOT_FINITE,FDOM_FINITE,INFINITE_NUM_UNIV]);

val ODD_EVEN_SIMP = prove(
  ``!n. ~ODD (2 * n) /\ ~EVEN (2 * n + 1)``,
  ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC (srw_ss()) [EVEN_MOD2,ODD_EVEN,MOD_MULT,
       MOD_MULT |> Q.SPECL [`n`,`0`] |> RW [ADD_0]]);

val bc_fetch_ignore_stack = prove(
  ``bc_fetch (s with stack := ss) = bc_fetch s``,
  SIMP_TAC (srw_ss()) [bc_fetch_def]);

val ERROR_TAC =
  SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
  \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Error) |> SPEC_ALL
                |> DISCH_ALL |> RW [AND_IMP_INTRO])
  \\ FULL_SIMP_TAC (srw_ss()) [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [bc_fetch_ignore_stack]

val output_simp = prove(
  ``((bump_pc s1).output = s1.output) /\
    ((s with stack := xxx).output = s.output) /\
    ((s with pc := new_pc).output = s.output)``,
  Cases_on `bc_fetch s1` \\ ASM_SIMP_TAC (srw_ss()) [bump_pc_def]);

val EVERY2_CONS = prove(
  ``EVERY2 P (x::xs) ys <=>
    ?y ys'. P x y /\ EVERY2 P xs ys' /\ (ys = y::ys')``,
  Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]);

val reachable_refs_CodePtr = prove(
  ``(reachable_refs (x1::x2::x3::x4::CodePtr x::stack) refs n =
     reachable_refs (x1::x2::x3::x4::stack) refs n) /\
    (reachable_refs (CodePtr x::x2::x3::x4::stack) refs n =
     reachable_refs (x2::x3::x4::stack) refs n)``,
  SIMP_TAC std_ss [reachable_refs_def,MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ TRY (Q.PAT_ASSUM `x' = xxxx` ASSUME_TAC)
  \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM] \\ METIS_TAC []);

val zHEAP_CodePtr = prove(
  ``(zHEAP (cs,x1,x2,x3,x4,refs,CodePtr n::stack,s,space) =
     zHEAP (cs,x1,x2,x3,x4,refs,CodePtr (w2n ((n2w n):63 word))::stack,s,space)) /\
    (zHEAP (cs,CodePtr n,x2,x3,x4,refs,stack,s,space) =
     zHEAP (cs,CodePtr (w2n ((n2w n):63 word)),x2,x3,x4,refs,stack,s,space))``,
  SIMP_TAC std_ss [zHEAP_def,heap_inv_def,abs_ml_inv_def,
    APPEND,bc_stack_ref_inv_def,EVERY2_def,EVERY2_CONS,PULL_EXISTS]
  \\ SIMP_TAC std_ss [bc_value_inv_def,n2w_w2n,reachable_refs_CodePtr]);

val MOD64_DIV2_MOD63 = prove(
  ``(n MOD dimword (:64) DIV 2) MOD dimword (:63) =
    (n DIV 2) MOD dimword (:63)``,
  `dimword (:64) = dimword (:63) * 2` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [DIV_MOD_MOD_DIV,ZERO_LT_dimword]
  \\ `0 < dimword (:63) * 2` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,MOD_MOD]);

val HD_CONS_TL = prove(
  ``!xs. ~(xs = []) ==> (HD xs :: TL xs = xs)``,
  Cases \\ SRW_TAC [] []);

val word_sub_intro = prove(
  ``(-w + v = v - w) /\ (v + -w = v - w:'a word)``,
  SIMP_TAC std_ss [word_sub_def,AC WORD_ADD_COMM WORD_ADD_ASSOC]);

val SPEC_CONSEQ = prove(
  ``SPEC m p c q ==>
    !p1 q1. SEP_IMP p1 p /\ SEP_IMP q q1 ==> SPEC m p1 c q1``,
  METIS_TAC [SPEC_WEAKEN,SPEC_STRENGTHEN]);

val zBC_HEAP_THM = prove(
  ``EVEN (w2n cb) /\ (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) ==>
    !s1 s2.
      bc_next s1 s2 ==> (s1.inst_length = x64_inst_length) /\
      (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
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
  \\ NTAC 3 (TRY (MATCH_MP_TAC IMP_small_offset \\ REPEAT STRIP_TAC
                  \\ TRY (SRW_TAC [] [output_simp] \\ NO_TAC)))
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
  THEN1 (* Pops *)
   (SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Pops)
         |> Q.INST [`k`|->`n`] |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    THEN1 DECIDE_TAC
    \\ Q.PAT_ASSUM `n = xxx` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1,
         small_offset_def,LET_DEF,GSYM ADD_ASSOC,IMM32_def]
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ `DROP (LENGTH ys')
             (MAP (bc_adjust (cb,sb,ev)) ys' ++
              MAP (bc_adjust (cb,sb,ev)) xs ++ Number 0::stack) =
        MAP (bc_adjust (cb,sb,ev)) xs ++ Number 0::stack` by ALL_TAC
    THEN1 (METIS_TAC [rich_listTheory.DROP_LENGTH_APPEND,LENGTH_MAP,APPEND_ASSOC])
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Shift *) ERROR_TAC
  THEN1 (* PushInt *) ERROR_TAC
  THEN1 (* Cons *) ERROR_TAC
  THEN1 (* Load *) cheat
  THEN1 (* Store *) cheat
  THEN1 (* LoadRev *) cheat
  THEN1 (* El *) cheat
  THEN1 (* TagEq *) cheat
  THEN1 (* IsBlock *) cheat
  THEN1 (* Equal *) cheat
  THEN1 (* Add *) cheat
  THEN1 (* Sub *) cheat
  THEN1 (* Mult *) cheat
  THEN1 (* Div *) cheat
  THEN1 (* Mod *) cheat
  THEN1 (* Less *) cheat
  THEN1 (* Jump Lab *) ERROR_TAC
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
  THEN1 (* JumpIf -- Lab *) ERROR_TAC
  THEN1 (* JumpIf -- Addr *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_JumpIf) |> SPEC_ALL
                     |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [bc_find_loc_def,GSYM word_add_n2w]
    \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ EVAL_TAC)
    \\ `bc_fetch (s1 with stack := xs) = bc_fetch s1` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_fetch_def] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [MAP,HD,TL,APPEND,sw2sw_lemma]
    \\ `cb + n2w (2 * s1.pc) +
         (6w + (0x6w + sw2sw (n2w (2 * n) - n2w (2 * s1.pc) - 0xCw:word32))) =
        cb + n2w (2 * n)` by ALL_TAC THEN1
     (SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC]
      \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,word_add_n2w,GSYM WORD_SUB_PLUS]
      \\ SIMP_TAC std_ss [GSYM ADD_ASSOC]
      \\ `(2 * s1.pc + 12) < 4294967296 /\ (2 * n) < 4294967296` by DECIDE_TAC
      \\ `n2w (2 * s1.pc + 12) = (w2w:word32->word64) (n2w (2 * s1.pc + 12))` by
            FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w]
      \\ `n2w (2 * n) = (w2w:word32->word64) (n2w (2 * n))` by
            FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w]
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC w2w_ADD_sw2sw_SUB
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO,w2n_n2w]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `b` \\ FULL_SIMP_TAC (srw_ss()) [bc_adjust_def]
    \\ POP_ASSUM (K ALL_TAC)
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ Q.PAT_ASSUM `n' = n` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1,
         small_offset_def,LET_DEF,GSYM ADD_ASSOC])
  THEN1 (* Call -- Lab *) ERROR_TAC
  THEN1 (* Call -- Addr *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Call) |> SPEC_ALL
                     |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [bc_find_loc_def,GSYM word_add_n2w]
    \\ SIMP_TAC std_ss [sw2sw_lemma]
    \\ `cb + n2w (2 * s1.pc) +
         0x6w + sw2sw (n2w (2 * n) - n2w (2 * s1.pc) - 0x6w:word32) =
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
    \\ FULL_SIMP_TAC (srw_ss()) [HD,TL,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def,getCodePtr_def,isCodePtr_def]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,EVEN_LEMMA]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [EVEN_w2n] \\ Q.PAT_ASSUM `~cb ' 0` MP_TAC
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w] \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ `x64_inst_length (Call (Addr n)) = 2` by ALL_TAC THEN1
     (Q.PAT_ASSUM `n' = n` ASSUME_TAC \\ EVAL_TAC
      \\ FULL_SIMP_TAC std_ss [LENGTH])
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ `w2n cb DIV 2 + (s1.pc + 3) =
        (w2n cb + 2 * (s1.pc + 3)) DIV 2` by ALL_TAC THEN1
     (ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
      \\ SIMP_TAC std_ss [ADD_DIV_ADD_DIV])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `bbb s'` MP_TAC
    \\ ONCE_REWRITE_TAC [zHEAP_CodePtr]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ Cases_on `cb` \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [MOD64_DIV2_MOD63]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* CallPtr *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_CallPtr
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [HD,TL,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def,getCodePtr_def,isCodePtr_def]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,EVEN_LEMMA]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [EVEN_w2n] \\ Q.PAT_ASSUM `~cb ' 0` MP_TAC
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w] \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`CodePtr (w2n cb DIV 2 + ptr)`,`x3`]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [EVAL ``x64_inst_length CallPtr``]
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ POP_ASSUM MP_TAC
    \\ `w2n cb DIV 2 + (s1.pc + 4) =
        (w2n cb + 2 * (s1.pc + 4)) DIV 2` by ALL_TAC THEN1
     (ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
      \\ SIMP_TAC std_ss [ADD_DIV_ADD_DIV])
    \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [zHEAP_CodePtr]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ Cases_on `cb` \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_add_n2w]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [MOD64_DIV2_MOD63]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* JumpPtr *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_JumpPtr
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [HD,TL,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def,getCodePtr_def,isCodePtr_def]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,EVEN_LEMMA]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`CodePtr (w2n cb DIV 2 + ptr)`,`x3`]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* PushPtr -- Lab *) ERROR_TAC
  THEN1 (* PushPtr -- Addr *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_PushPtr) |> SPEC_ALL
                     |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ FULL_SIMP_TAC std_ss [bc_find_loc_def,GSYM word_add_n2w]
    \\ SIMP_TAC std_ss [sw2sw_lemma]
    \\ `cb + n2w (2 * s1.pc) +
         0x8w + sw2sw (n2w (2 * n) - n2w (2 * s1.pc) - 0x8w:word32) =
        cb + n2w (2 * n)` by ALL_TAC THEN1
     (SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC]
      \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,word_add_n2w,GSYM WORD_SUB_PLUS]
      \\ `(2 * s1.pc + 8) < 4294967296 /\ (2 * n) < 4294967296` by DECIDE_TAC
      \\ `n2w (2 * s1.pc + 8) = (w2w:word32->word64) (n2w (2 * s1.pc + 8))` by
            FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w]
      \\ `n2w (2 * n) = (w2w:word32->word64) (n2w (2 * n))` by
            FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w]
      \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC w2w_ADD_sw2sw_SUB
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO,w2n_n2w]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC) \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [HD,TL,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def,getCodePtr_def,isCodePtr_def]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,EVEN_LEMMA]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    THEN1 (FULL_SIMP_TAC std_ss [EVEN_w2n] \\ Q.PAT_ASSUM `~cb ' 0` MP_TAC
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w] \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ Q.PAT_ASSUM `n' = n` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [x64_inst_length_def,x64_length_def,x64_def,
         small_offset_def,LET_DEF,LENGTH,IMM32_def,word_arith_lemma1]
    \\ DISJ1_TAC
    \\ Q.PAT_ABBREV_TAC `pat = tt ++ Number 0::stack`
    \\ `HD pat :: TL pat = pat` by ALL_TAC THEN1
     (Cases_on `pat` \\ UNABBREV_ALL_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `s1.stack` \\ FULL_SIMP_TAC (srw_ss()) [MAP])
    \\ FULL_SIMP_TAC std_ss []
    \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
    \\ `w2n cb DIV 2 + n =
        (w2n cb + 2 * n) DIV 2` by ALL_TAC THEN1
     (ONCE_REWRITE_TAC [ADD_COMM] \\ ONCE_REWRITE_TAC [MULT_COMM]
      \\ SIMP_TAC std_ss [ADD_DIV_ADD_DIV])
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `bbb s'` MP_TAC
    \\ ONCE_REWRITE_TAC [zHEAP_CodePtr]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ Cases_on `cb` \\ FULL_SIMP_TAC std_ss [w2n_n2w,word_add_n2w]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [MOD64_DIV2_MOD63]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
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
  THEN1 (* PushExn *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_PushExc
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ ASM_SIMP_TAC (srw_ss()) [bc_adjust_def]
    \\ SIMP_TAC std_ss [reintro_word_sub]
    \\ `SUC (LENGTH (TL
         (MAP (bc_adjust (cb,sb,ev)) s1.stack ++
        Number 0::stack))) = LENGTH s1.stack + SUC (LENGTH stack)` by ALL_TAC
    THEN1 (Cases_on `s1.stack` \\ SRW_TAC [] [] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ SIMP_TAC (srw_ss()) [HD_CONS_TL] \\ SIMP_TAC std_ss [reintro_word_sub]
    \\ `-n2w (8 * s1.handler + 8 * SUC (LENGTH stack)) +
            cs.stack_trunk = sb + -n2w (8 * s1.handler)` by ALL_TAC THEN1
     (Q.PAT_ASSUM `bbb = sb` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,word_sub_intro]
      \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS] \\ SRW_TAC [] [])
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC std_ss [reintro_word_sub]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* PopExn *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (zBC_PopExc
         |> DISCH ``l1 ++ StackPtr (w2n (cs.stack_trunk -
                      n2w (8 * sp)) DIV 2)::l2 = xss``
         |> SIMP_RULE std_ss [] |> prepare
         |> Q.INST [`l1`|->`MAP (bc_adjust (cb,sb,ev)) l1`,
                    `l2`|->`MAP (bc_adjust (cb,sb,ev)) l2 ++ Number 0::stack`,
                    `x1`|->`bc_adjust (cb,sb,ev) x'`,
                    `sp`|->`sp + SUC (LENGTH (stack:bc_value list))`]
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ STRIP_TAC THEN1 cheat
    \\ FULL_SIMP_TAC (srw_ss()) [MAP,MAP_APPEND,HD,TL,APPEND]
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [reintro_word_sub]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC std_ss [reintro_word_sub]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Ref *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Ref
         |> Q.INST [`ptr`|->`if ev then 2 * ptr else 2 * ptr + 1`]
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,isCodePtr_def,APPEND,NOT_CONS_NIL]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def]
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [ref_adjust_def,LET_DEF]
      \\ `n = ptr` by (Cases_on `ev` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ `?x. (\x. x NOTIN FDOM s1.refs) x` by ALL_TAC
      THEN1 (FULL_SIMP_TAC std_ss [EXISTS_NOT_FDOM_NUM])
      \\ IMP_RES_TAC whileTheory.LEAST_INTRO
      \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [])
    THEN1 (RES_TAC \\ Cases_on `ev` \\ FULL_SIMP_TAC (srw_ss()) [ODD_EVEN_SIMP])
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ `FUNION (ref_adjust (cb,sb,ev) (s1.refs |+ (ptr,x'))) f2 =
        FUNION (ref_adjust (cb,sb,ev) s1.refs) f2 |+
           (if ev then 2 * ptr else 2 * ptr + 1,
            bc_adjust (cb,sb,ev) x')` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [ref_adjust_def,LET_DEF,FDOM_FUPDATE,
        IMAGE_INSERT,bc_adjust_def,FAPPLY_FUPDATE_THM]
    \\ ONCE_REWRITE_TAC [GSYM fmap_EQ]
    \\ FULL_SIMP_TAC (srw_ss()) [INSERT_UNION_EQ]
    \\ FULL_SIMP_TAC (srw_ss()) [FUN_EQ_THM,FUNION_DEF,FAPPLY_FUPDATE_THM]
    \\ STRIP_TAC
    \\ `(if ev then 2 * ptr else (2 * ptr + 1)) DIV 2 = ptr` by ALL_TAC
    THEN1 (SRW_TAC [] [DIV_EQ_X] \\ DECIDE_TAC)
    \\ Cases_on `x'' = if ev then 2 * ptr else 2 * ptr + 1`
    THEN1 FULL_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 ==> (x1 = x2)) /\ (y1 = y2) ==>
       ((if b1 then x1 else y1) = (if b1 then x2 else y2))``)
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF,IN_INSERT]
    \\ `(if ev then 2 * n else 2 * n + 1) IN
        IMAGE (\n. if ev then 2 * n else 2 * n + 1) (FDOM s1.refs)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [IN_IMAGE] \\ METIS_TAC [])
    \\ ASM_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF,IN_INSERT]
    \\ `n <> ptr` by (Cases_on `ev` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ `(if ev then 2 * n else (2 * n + 1)) DIV 2 <> ptr` by ALL_TAC
    THEN1 (SRW_TAC [] [DIV_EQ_X] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* Deref *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Deref
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ `FUNION (ref_adjust (cb,sb,ev) s1.refs) f2 '
           (if ev then 2 * ptr else 2 * ptr + 1) =
        bc_adjust (cb,sb,ev) (s1.refs ' ptr)` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC (srw_ss()) [ref_adjust_def,LET_DEF,FUNION_DEF]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ (x1 = y) ==> ((if b then x1 else x2) = y)``)
    \\ STRIP_TAC THEN1 METIS_TAC []
    \\ `FINITE (IMAGE (\n. if ev then 2 * n else 2 * n + 1) (FDOM s1.refs))` by ALL_TAC
    THEN1 SRW_TAC [] []
    \\ `(if ev then 2 * ptr else 2 * ptr + 1) IN
         (IMAGE (\n. if ev then 2 * n else 2 * n + 1) (FDOM s1.refs))` by ALL_TAC
    THEN1 (SRW_TAC [] [] \\ METIS_TAC [])
    \\ IMP_RES_TAC (FUN_FMAP_DEF |> INST_TYPE [``:'b``|->``:bc_value``])
    \\ FULL_SIMP_TAC std_ss [FUN_FMAP_DEF]
    \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ FULL_SIMP_TAC std_ss [DIV_EQ_X] \\ Cases_on `ev`
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  THEN1 (* Update *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Update
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`RefPtr (if ev then 2 * ptr else 2 * ptr + 1)`,`x3`]
    \\ `FUNION (ref_adjust (cb,sb,ev) (s1.refs |+ (ptr,x'))) f2 =
        FUNION (ref_adjust (cb,sb,ev) s1.refs) f2 |+
           (if ev then 2 * ptr else 2 * ptr + 1,
            bc_adjust (cb,sb,ev) x')` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [ref_adjust_def,LET_DEF,FDOM_FUPDATE,
        IMAGE_INSERT,bc_adjust_def,FAPPLY_FUPDATE_THM]
    \\ ONCE_REWRITE_TAC [GSYM fmap_EQ]
    \\ FULL_SIMP_TAC (srw_ss()) [INSERT_UNION_EQ]
    \\ FULL_SIMP_TAC (srw_ss()) [FUN_EQ_THM,FUNION_DEF,FAPPLY_FUPDATE_THM]
    \\ STRIP_TAC
    \\ `(if ev then 2 * ptr else (2 * ptr + 1)) DIV 2 = ptr` by ALL_TAC
    THEN1 (SRW_TAC [] [DIV_EQ_X] \\ DECIDE_TAC)
    \\ Cases_on `x'' = if ev then 2 * ptr else 2 * ptr + 1`
    THEN1 FULL_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 ==> (x1 = x2)) /\ (y1 = y2) ==>
       ((if b1 then x1 else y1) = (if b1 then x2 else y2))``)
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF,IN_INSERT]
    \\ `(if ev then 2 * n else 2 * n + 1) IN
        IMAGE (\n. if ev then 2 * n else 2 * n + 1) (FDOM s1.refs)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [IN_IMAGE] \\ METIS_TAC [])
    \\ ASM_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF,IN_INSERT]
    \\ `n <> ptr` by (Cases_on `ev` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ `(if ev then 2 * n else (2 * n + 1)) DIV 2 <> ptr` by ALL_TAC
    THEN1 (SRW_TAC [] [DIV_EQ_X] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* Tick *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Tick
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
  THEN1 (* Print *) cheat
  THEN1 (* PrintC *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_PrintC
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ `(CHR (ORD c MOD 256)) = c` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [ORD_BOUND,CHR_ORD])
    \\ FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND,bump_pc_def]
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,LET_DEF,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC]));

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

val bc_next_isPREFIX = prove(
  ``!s1 s2. bc_next s1 s2 ==> isPREFIX s1.output s2.output``,
  HO_MATCH_MP_TAC bc_next_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bump_pc_def] \\ SRW_TAC [] []
  \\ TRY BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.IS_PREFIX_APPEND,SNOC_APPEND]
  \\ METIS_TAC [APPEND_ASSOC]);

val isPREFIX_APPEND = prove(
  ``!part xs ys zs.
      isPREFIX part (xs ++ ys) /\ isPREFIX ys zs ==> isPREFIX part (xs ++ zs)``,
  FULL_SIMP_TAC std_ss [rich_listTheory.IS_PREFIX_APPEND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ METIS_TAC [APPEND_ASSOC]);

val zBC_HEAP_RTC = prove(
  ``EVEN (w2n cb) /\ (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) ==>
    !s1 s2.
      bc_next^* s1 s2 ==>
      isPREFIX s1.output s2.output /\
      ((s1.inst_length = x64_inst_length) ==>
       (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
       SPEC X64_MODEL
         (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
          zPC (cb + n2w (2 * s1.pc)) * ~zS)
         ((cb, x64_code 0 s1.code) INSERT code_abbrevs cs)
         (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
          zPC (cb + n2w (2 * s2.pc)) * ~zS \/
          zHEAP_ERROR (cs,out ++ s2.output)))``,
  STRIP_TAC
  \\ HO_MATCH_MP_TAC RTC_INDUCT \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.IS_PREFIX_REFL]
  THEN1 (MATCH_MP_TAC SPEC_REMOVE_POST \\ SIMP_TAC std_ss [SPEC_REFL])
  THEN1 (METIS_TAC [rich_listTheory.IS_PREFIX_TRANS,bc_next_isPREFIX])
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
  \\ (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
      |> MATCH_MP_TAC)
  \\ Q.EXISTS_TAC `(zBC_HEAP s3 (x,cs,stack,s,out) (cb,sb,ev,f2) *
       zPC (cb + n2w (2 * s3.pc)) * ~zS \/
       zHEAP_ERROR (cs,STRCAT out s3.output))`
  \\ REVERSE CONJ_TAC THEN1
   (MATCH_MP_TAC SEP_IMP_DISJ \\ FULL_SIMP_TAC std_ss [SEP_IMP_REFL]
    \\ FULL_SIMP_TAC std_ss [zHEAP_ERROR_def,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `part`
    \\ FULL_SIMP_TAC std_ss [cond_STAR] \\ METIS_TAC [isPREFIX_APPEND])
  \\ Q.PAT_ASSUM `SPEC xx yy tt rr` MP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ (SPEC_SUBSET_CODE |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
        |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO] |> MATCH_MP_TAC)
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ SIMP_TAC std_ss [SUBSET_DEF,IN_INSERT]);

val _ = export_theory();
