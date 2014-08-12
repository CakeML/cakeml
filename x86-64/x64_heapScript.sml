open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_heap";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;
open prog_x64_extraTheory prog_x64Theory temporalTheory;
open lexer_funTheory lexer_implTheory;
open lcsymtacs;

open bytecodeTheory bytecodeExtraTheory;

open ml_copying_gcTheory ml_heapTheory
open decompilerLib;
open x64_codegenLib;
open x64_compilerLib;
open set_sepTheory;
open helperLib;
open addressTheory
open x64_copying_gcTheory;
open progTheory;

val _ = (max_print_depth := 50);

infix \\ val op \\ = op THEN;

fun gg tm = (proofManagerLib.drop ();
             proofManagerLib.drop ();
             proofManagerLib.set_goal([],tm));

val w2w_ADD_sw2sw_SUB = prove(
  ``!x y. x <+ 0x20000000w /\ y <+ 0x20000000w ==>
          (w2w x + sw2sw (y - x) = (w2w:word32 -> word64) y)``,
  REPEAT GEN_TAC \\ blastLib.BBLAST_TAC);


(* define zHEAP *)

val _ = (Datatype.big_record_size := 100);

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
                    stack_trunk : word64 ;
                    repl_setup_ptr : word64 ;
                    repl_step_ptr : word64 ;
                    lex_ptr : word64 ;
                    install_and_run_ptr : word64 |>`;

val consts_zero = Define `
  consts_zero = <| heap_limit := 0 ;
                   heap_part1 := 0w ;
                   heap_part2 := 0w ;
                   ret_address := 0w ;
                   rest_of_stack := [] ;
                   getchar_ptr := 0w ;
                   putchar_ptr := 0w ;
                   error_ptr := 0w ;
                   alloc_ptr := 0w ;
                   bignum_ptr := 0w ;
                   equal_ptr := 0w ;
                   print_ptr := 0w ;
                   code_heap_ptr := 0w ;
                   code_heap_length := 0 ;
                   stack_trunk := 0w ;
                   repl_setup_ptr := 0w ;
                   repl_step_ptr := 0w ;
                   lex_ptr := 0w ;
                   install_and_run_ptr := 0w |>`;

val _ = Hol_datatype ` (* called local *)
  zheap_local = <| stop_addr : word64 ;
                   printing_on : word64 |> `;

val local_zero_def = Define `
  local_zero = <| stop_addr := 0w;
                  printing_on := 0w |>`;

val _ = Hol_datatype ` (* called vs *)
  zheap_vars = <| current_heap : word64 ;
                  other_heap : word64 ;
                  base_ptr : word64 ;
                  code_ptr : word64 ;
                  code_start_ptr : word64 ;
                  local : zheap_local |>`;

val _ = Hol_datatype ` (* called s *)
  zheap_state = <| input : string ;
                   output : string ;
                   handler : num ;
                   base_offset : num ;
                   code_mode : bool option ;
                   code : word8 list ;
                   code_start : word8 list ;
                   local : zheap_local |>`;

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
      [ vs.current_heap          (*   0 pointer to currently used heap half *)
      ; vs.other_heap            (*   8 pointer to the other heap half *)
      ; n2w (cs.heap_limit)      (*  16 size of each heap half *)
      ; cs.putchar_ptr           (*  24 pointer to C's putchar method *)
      ; cs.getchar_ptr           (*  32 pointer to C's getchar method *)
      ; cs.error_ptr             (*  40 pointer to abort code which writes error message *)
      ; cs.alloc_ptr             (*  48 pointer to heap alloc routine *)
      ; cs.bignum_ptr            (*  56 pointer to entry point for bignum library *)
      ; cs.equal_ptr             (*  64 pointer to routine for rec equality check *)
      ; cs.print_ptr             (*  72 pointer to routine for rec printing of bc_value *)
      ; vs.code_ptr              (*  80 pointer to next free instruction slot *)
      ; n2w cs.code_heap_length  (*  88 size of code heap *)
      ; cs.code_heap_ptr         (*  96 base of code heap *)
      ; vs.code_start_ptr        (* 104 bytecode execution will start here *)
      ; cs.repl_step_ptr         (* 112 pointer to repl_step routine *)
      ; cs.lex_ptr               (* 120 lexer *)
      ; cs.install_and_run_ptr   (* 128 install and run bytecode *)
      ; vs.local.stop_addr       (* 136 address where bc execution returns *)
      ; vs.local.printing_on     (* 144 whether printing should be done *)
      ; 0w                       (* 152 padding *)
      ; 0w                       (* 160 padding *)
      ; 0w                       (* 168 padding *)
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
                s_code_mode s_code s_code_start
                vs_code_ptr vs_code_start_ptr =
    cs_code_heap_length < (2**61):num /\
    (vals_code_option = s_code_mode) /\
    (vals_code_list = s_code) /\
    (cs_code_heap_ptr + n2w (LENGTH s_code) = vs_code_ptr) /\
    (cs_code_heap_ptr + n2w (LENGTH s_code_start) = vs_code_start_ptr)`;

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
                s.code_mode s.code s.code_start
                vs.code_ptr vs.code_start_ptr /\
      cs.heap_limit < 281474976710656 /\ (* 2**(64-16) *)
      (x64_heap vs.current_heap heap vs.current_heap vs.current_heap *
       one_list_exists vs.other_heap cs.heap_limit *
       x64_store cs vs) (fun2set (vals.memory,vals.memory_domain)) /\
      (vals.stack = MAP (x64_addr vs.current_heap) roots ++
                    0x1w::cs.ret_address::cs.rest_of_stack) /\
      (vals.input_stream = MAP (n2w o ORD) (DROP 1 s.input)) /\
      (vals.output_stream = MAP (n2w o ORD) s.output) /\
      (vs.local = s.local) /\
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
  zHEAP_ERROR cs =
    SEP_EXISTS output. zHEAP_OUTPUT (cs,output ++ error_msg)`;


(* define INIT_STATE *)

val _ = Hol_datatype ` (* called init *)
  zheap_init = <| init_heap_ptr : word64 ;
                  init_heap_size : word64 ;
                  init_code_heap_ptr : word64 ;
                  init_code_heap_size : word64 ;
                  init_putc_ptr : word64 ;
                  init_getc_ptr : word64 ;
                  init_input : string ;
                  init_ret_ptr : word64 ;
                  init_stack_bottom : word64 ;
                  init_stack : word64 list |>`;

(*

  heap[0] = HEAP_SIZE;
  heap[1] = (long) (& codeheap);
  heap[2] = CODE_HEAP_SIZE;
  heap[3] = (long) (& putchar);
  heap[4] = (long) (& getchar);

  - pointer to heap is in rax
  - ret address on top of stack

*)

val init_inv_def = Define `
  init_inv (cs:zheap_consts) (vals:x64_vals) (init:zheap_init) =
    (* heap pointer is in rax regsiter *)
    (vals.reg0 = init.init_heap_ptr) /\
    (* pointers are 64-bit aligned and sizes are < 2 ** 48 *)
    (init.init_heap_ptr && 7w = 0w) /\
    (init.init_code_heap_ptr && 7w = 0w) /\
    0x100 <= w2n init.init_heap_size /\
    (w2n init.init_heap_size MOD 16 = 0) /\
    w2n init.init_heap_size < 0x1000000000000 /\
    w2n init.init_code_heap_size < 0x1000000000000 /\
    (* stack contains ret pointer *)
    (vals.stack = init.init_ret_ptr :: init.init_stack) /\
    (vals.stack_bottom = init.init_stack_bottom) /\
    (* code heap is present but not clean *)
    (vals.code_option = SOME F) /\ (vals.code_list = []) /\
    (cs.code_heap_ptr = init.init_code_heap_ptr) /\
    (cs.code_heap_length = w2n init.init_code_heap_size) /\
    (* input_stream holds input and output is empty *)
    (cs.getchar_ptr = init.init_getc_ptr) /\
    (cs.putchar_ptr = init.init_putc_ptr) /\
    (vals.input_stream = MAP (n2w o ORD) init.init_input) /\
    (vals.output_stream = []) /\
    (* memory contains heap array with space for heaps *)
    ?space.
      (one_list init.init_heap_ptr ([init.init_heap_size;
                                     init.init_code_heap_ptr;
                                     init.init_code_heap_size;
                                     init.init_putc_ptr;
                                     init.init_getc_ptr] ++ space))
           (fun2set (vals.memory,vals.memory_domain)) /\
      (8 * (5 + LENGTH space) = w2n init.init_heap_size)`;

val INIT_STATE_def = Define `
  INIT_STATE init =
    SEP_EXISTS cs vals.
      zVALS cs vals * cond (init_inv cs vals init)`;


(* helpers theorems *)

fun take n [] = []
  | take 0 xs = []
  | take n (x::xs) = x::take (n-1) xs;

fun drop n [] = []
  | drop 0 xs = xs
  | drop n (x::xs) = drop (n-1) xs;

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

val reachable_refs_SIMP = prove(
  ``(reachable_refs (Number n::x1::x3::x4::stack) refs m =
     reachable_refs (x1::x3::x4::stack) refs m) /\
    (reachable_refs (x1::Number n::x3::x4::stack) refs m =
     reachable_refs (x1::x3::x4::stack) refs m) /\
    (reachable_refs (x1::x3::Number n::x4::stack) refs m =
     reachable_refs (x1::x3::x4::stack) refs m) /\
    (reachable_refs (x1::x3::x4::Number n::stack) refs m =
     reachable_refs (x1::x3::x4::stack) refs m)``,
  SIMP_TAC std_ss [reachable_refs_def,MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`x`,`r`] \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]);


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
  decompile_strings prog_x64Lib.x64_tools_64 name
    (assemble asm);

fun x64_decompile_no_status name asm =
  decompile_strings prog_x64Lib.x64_tools_64_no_status name
    (assemble asm);

val (_,_,sts,_) = prog_x64Lib.x64_tools

fun abbreviate_code name ptr = let
  val pat1 = ``(^ptr,xx:'a)``
  val pat2 = ``(^ptr + n2w n,xx:'a)``
  fun g tm = can (match_term pat1) tm orelse can (match_term pat2) tm
  val in_pat = ``x INSERT s``
  val in_in_pat = ``x INSERT y INSERT s``
  val in_union_pat = ``x INSERT s1 UNION s2``
  val PULL_INSERT_UNION = prove(
    ``((x INSERT s) UNION t = x INSERT (s UNION t)) /\
      (s UNION (x INSERT t) = x INSERT (s UNION t))``,
    SIMP_TAC (srw_ss()) [EXTENSION] \\ METIS_TAC []);
  val PUSH_INSERT_THM = prove(
    ``x INSERT (s UNION t) = s UNION (x INSERT t)``,
    SIMP_TAC (srw_ss()) [EXTENSION] \\ METIS_TAC []);
  val UNION_IDEMPOT_LEMMA = prove(
    ``(s UNION (s UNION t)) = s UNION t``,
    SIMP_TAC (srw_ss()) [EXTENSION] \\ METIS_TAC []);
  fun insert_final_empty_conv tm =
    if can (match_term in_pat) tm then
      RAND_CONV insert_final_empty_conv tm
    else if pred_setSyntax.is_union tm then
      RAND_CONV insert_final_empty_conv tm
    else UNION_EMPTY |> CONJUNCT2 |> GSYM |> ISPEC tm
  fun full_push_insert_conv g tm =
    if can (match_term in_pat) tm then let
      val x = tm |> rator |> rand
      fun push_insert_conv tm = (* assumes input of form x INSERT s such that g x *)
        if can (match_term in_in_pat) tm then let
          val x = tm |> rator |> rand
          val y = tm |> rand |> rator |> rand
          in if g y then ALL_CONV tm else
            (REWR_CONV INSERT_COMM THENC RAND_CONV push_insert_conv) tm
          end
        else if can (match_term in_union_pat) tm then
          (REWR_CONV PUSH_INSERT_THM THENC RAND_CONV push_insert_conv) tm
        else ALL_CONV tm
        in if g x then push_insert_conv tm else ALL_CONV tm end
    else ALL_CONV tm
  fun f tm = let
    val q = [QUOTE (name^"_code p = "),ANTIQUOTE (subst [ptr|->``p:word64``] tm)]
    in REWR_CONV (GSYM (Define q)) tm end
  fun modify_conv f g tm =
    if can (match_term in_pat) tm then let
      val x = tm |> rator |> rand
      in if g x then f tm else RAND_CONV (modify_conv f g) tm end
    else RAND_CONV (modify_conv f g) tm
  val c = (REWRITE_CONV [PULL_INSERT_UNION]
           THENC insert_final_empty_conv
           THENC DEPTH_CONV (full_push_insert_conv g)
           THENC modify_conv f g
           THENC SIMP_CONV std_ss [AC UNION_ASSOC UNION_COMM,UNION_IDEMPOT_LEMMA]
           THENC SIMP_CONV std_ss [UNION_EMPTY,UNION_ASSOC])
  in CONV_RULE ((RATOR_CONV o RAND_CONV) c) end


(* from INIT_STATE to zHEAP *)

val store_length =
  x64_store_def |> SPEC_ALL |> concl |> rand |> rand
    |> listSyntax.dest_list |> fst |> length |> numSyntax.term_of_int

val heap_len =
  ``((w2n init.init_heap_size - 8 * ^store_length) DIV 16)``

val first_s_def = Define `
  first_s (init:zheap_init) =
    <| input := " " ++ init.init_input ;
       output := "" ;
       handler := 0 ;
       base_offset := 0 ;
       code_mode := SOME F ;
       code := [] ;
       code_start := [] ;
       local := local_zero |>`

val first_cs_def = Define `
  first_cs (init:zheap_init) =
    consts_zero with
    <| heap_limit := ^heap_len
     ; ret_address := init.init_ret_ptr
     ; rest_of_stack := init.init_stack
     ; stack_trunk := init.init_stack_bottom - n2w (8 * LENGTH init.init_stack + 16)
     ; code_heap_ptr := init.init_code_heap_ptr
     ; code_heap_length := w2n init.init_code_heap_size
     ; getchar_ptr := init.init_getc_ptr
     ; putchar_ptr := init.init_putc_ptr |>`;

val reintro_word_sub64 = SIMP_CONV (srw_ss()) [] ``-(n2w n):word64`` |> GSYM
val reintro_word_sub63 = SIMP_CONV (srw_ss()) [] ``-(n2w n):63 word`` |> GSYM

val ID_def = Define `ID x = x`;

val n2w_lsr = prove(
  ``!n. n < 2**64 ==>
        (n2w n >>> k = n2w (n DIV 2 ** k):word64)``,
  SIMP_TAC std_ss [w2n_lsr,GSYM w2n_11,w2n_n2w] \\ REPEAT STRIP_TAC
  \\ `(n DIV 2 ** k) < dimword (:64)` by ALL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [DIV_LT_X]
  \\ Cases_on `(2:num) ** k` \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  \\ DECIDE_TAC) |> SIMP_RULE std_ss [];

val x64_heap_heap_expand = prove(
  ``x64_heap curr (heap_expand len) curr curr = one_list_exists curr len``,
  Cases_on `len` \\ ASM_SIMP_TAC std_ss [heap_expand_def]
  \\ SIMP_TAC std_ss [one_list_exists_def,FUN_EQ_THM,SEP_EXISTS_THM,ADD1,
      cond_STAR,LENGTH_NIL,one_list_def,x64_heap_def,SEP_CLAUSES,x64_el_def]);

val x64_heap_APPEND_one_list_exists = prove(
  ``x64_heap curr (heap_expand heap_len) curr curr *
    one_list_exists (curr + 0x8w * n2w heap_len) heap_len =
    one_list_exists curr (heap_len + heap_len)``,
  SIMP_TAC std_ss [x64_heap_heap_expand,one_list_exists_def,SEP_CLAUSES]
  \\ SIMP_TAC (std_ss++sep_cond_ss) [FUN_EQ_THM,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `xs ++ xs'`
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,one_list_APPEND,word_mul_n2w])
  \\ IMP_RES_TAC LENGTH_EQ_SUM \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`l1`,`l2`]
  \\ FULL_SIMP_TAC std_ss [one_list_APPEND,word_mul_n2w]);

val (x64_setup_res, x64_setup_def, x64_setup_pre_def) = x64_compile `
  x64_setup (r0:word64,dm:word64 set,m:word64->word64,ss:word64 list) =
    let r1 = 1w:word64 in
    let ss = r1 :: ss in
    let r1 = m r0 in
    let r12 = m (r0 + 0x08w) in (* code_heap_ptr *)
    let r13 = m (r0 + 0x10w) in (* code_heap_size *)
    let r3 = n2w ^store_length in
    let r3 = r3 << 3 in
    let r15 = r0 + r3 in (* v *)
    let r1 = r1 - r3 in
    let r1 = r1 >>> 4 in (* w *)
    let r9 = r0 in
    let r6 = r15 - 1w in
    let r7 = r1 << 3 in
    let r7 = r7 + r15 in
    let r7 = r7 - 1w in
    let r10 = 0x20w:word64 in
    let m = (r0 =+ r15) m in
    let r2 = r1 << 3 in
    let r15 = r15 + r2 in
    let r14 = 0w:word64 in
    let m = (r0 + 8w =+ r15) m in
    let m = (r0 + 0x10w =+ r1) m in
    let m = (r0 + 0x28w =+ r14) m in
    let m = (r0 + 0x30w =+ r14) m in
    let m = (r0 + 0x38w =+ r14) m in
    let m = (r0 + 0x40w =+ r14) m in
    let m = (r0 + 0x48w =+ r14) m in
    let m = (r0 + 0x58w =+ r13) m in
    let m = (r0 + 0x50w =+ r12) m in
    let m = (r0 + 0x60w =+ r12) m in
    let m = (r0 + 104w =+ r12) m in
    let r0 = r0 + 112w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r0 + 8w in
    let m = (r0 =+ r14) m in
    let r0 = r14 in
    let r1 = r14 in
    let r2 = r14 in
    let r3 = r14 in
    let r8 = r14 in
    let r12 = r14 in
    let r13 = r14 in
    let r15 = r14 in
      (r0,r1,r2,r3,r6,r7,r8,r9,r10,r12,r13,r14,r15,dm,m,ss)`

val stack_assum =
  ``(vals.reg5 = vals.stack_bottom - n2w (8 * LENGTH vals.stack + 8)) /\
    (vals.reg11 = vals.reg5) /\
    (vals.stack_bottom && 7w = 0w)``;

val init_inv_IMP_heap_inv = prove(
  ``init_inv cs vals init ==>
      x64_setup_pre (vals.reg0,vals.memory_domain,vals.memory,vals.stack) /\
     (^stack_assum ==>
      let x = Number 0 in
      let w = (vals.memory vals.reg0 - n2w (ID (8 * ^store_length))) >>> 4 in
      let c = (vals.memory (vals.reg0 + 8w)) in
      let v = vals.reg0 + n2w (8 * ^store_length) in
        heap_inv (first_cs init,x,x,x,x,FEMPTY,[],first_s init,NONE)
          (let (r0,r1,r2,r3,r6,r7,r8,r9,r10,r12,r13,r14,r15,dm,m,ss) =
            x64_setup (vals.reg0,vals.memory_domain,vals.memory,vals.stack) in
             vals with <| reg0 := r0 ;
                          reg1 := r1 ;
                          reg2 := r2 ;
                          reg3 := r3 ;
                          reg6 := r6 ;
                          reg7 := r7 ;
                          reg8 := r8 ;
                          reg9 := r9 ;
                          reg10 := r10 ;
                          reg12 := r12 ;
                          reg13 := r13 ;
                          reg14 := r14 ;
                          reg15 := r15 ;
                          stack := ss ;
                          memory := m ;
                          memory_domain := dm |>))``,
  ONCE_REWRITE_TAC [CONJ_COMM]
  \\ SIMP_TAC std_ss [LET_DEF,init_inv_def] \\ STRIP_TAC
  \\ Q.ABBREV_TAC `heap_len = ^heap_len`
  \\ Q.ABBREV_TAC `curr = init.init_heap_ptr + n2w (8 * ^store_length)`
  \\ `(vals.memory init.init_heap_ptr - n2w (ID 176)) >>> 4 = n2w heap_len` by
   (FULL_SIMP_TAC std_ss [one_list_def,APPEND] \\ SEP_R_TAC
    \\ UNABBREV_ALL_TAC \\ Cases_on `init.init_heap_size`
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,WORD_SUB_INTRO,ID_def]
    \\ `~(n < 8 * ^store_length)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma2]
    \\ `n - 8 * ^store_length < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss [EVAL ``8 * ^store_length``]
    \\ IMP_RES_TAC n2w_lsr
    \\ FULL_SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss []
  \\ `curr + n2w heap_len << 3 - 0x1w = (curr + n2w (8 * heap_len)) - 1w` by
   (FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_sub_def]
    \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [LET_DEF,heap_inv_def]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,PULL_IMP_EXISTS]
  \\ Q.LIST_EXISTS_TAC [`<| current_heap := curr;
                            other_heap := curr + n2w (8 * heap_len);
                            base_ptr := init.init_heap_ptr ;
                            code_ptr := init.init_code_heap_ptr ;
                            code_start_ptr := init.init_code_heap_ptr ;
                            local := local_zero |>`,
       `Data 0w`,`Data 0w`,`Data 0w`,`Data 0w`,`[]`,
       `heap_expand heap_len`,`0`,`heap_len`]
  \\ FULL_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [x64_addr_def,first_cs_def,heap_vars_ok_def]
  \\ REVERSE STRIP_TAC THEN1
   (`^store_length - 5 <= LENGTH space` by DECIDE_TAC
    \\ IMP_RES_TAC LESS_EQ_LENGTH
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `ys1` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ REVERSE (NTAC 10 (REPEAT (Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH])
               \\ REPEAT (Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH])))
    THEN1 (SIMP_TAC std_ss [ADD1] \\ `F` by DECIDE_TAC)
    \\ FULL_SIMP_TAC (srw_ss()++sep_cond_ss) [APPEND,one_list_def,x64_store_def,
         EVAL ``consts_zero``,STAR_ASSOC,SEP_CLAUSES,SEP_EXISTS_THM,
         one_list_exists_def,cond_STAR]
    \\ FULL_SIMP_TAC std_ss [x64_setup_pre_def,LET_DEF,word_arith_lemma1]
    \\ SEP_R_TAC \\ SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `0x7w && init.init_heap_ptr = 0x0w` MP_TAC
    \\ blastLib.BBLAST_TAC)
  \\ STRIP_TAC
  \\ STRIP_TAC THEN1
   (Cases_on `heap_len = 0` \\ FULL_SIMP_TAC std_ss [heap_expand_def]
    \\ EVAL_TAC \\ SIMP_TAC std_ss [SUM,PULL_EXISTS] \\ Q.EXISTS_TAC `FEMPTY`
    \\ SRW_TAC [] [INJ_DEF,get_refs_def] \\ TRY DECIDE_TAC \\
    Cases_on`x = Number 0` \\ SRW_TAC [][get_refs_def])
  \\ FULL_SIMP_TAC (srw_ss()) [init_inv_def,first_s_def,code_heap_inv_def,
       stack_inv_def] \\ FULL_SIMP_TAC std_ss [reintro_word_sub64]
  \\ `heap_len < 281474976710656 /\
      heap_len < 4611686018427387904` by ALL_TAC THEN1
    (UNABBREV_ALL_TAC \\ FULL_SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [x64_heap_APPEND_one_list_exists
       |> SIMP_RULE std_ss [word_mul_n2w]]
  \\ `0x7w && curr = 0x0w` by ALL_TAC THEN1
   (UNABBREV_ALL_TAC
    \\ Q.PAT_ASSUM `0x7w && init.init_heap_ptr = 0x0w` MP_TAC
    \\ blastLib.BBLAST_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ `0x7w && curr + n2w (8 * heap_len) = 0x0w` by ALL_TAC THEN1
   (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ blastLib.BBLAST_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [x64_setup_def,LET_DEF,ID_def,local_zero_def]
  \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [reintro_word_sub64,GSYM (EVAL ``-16w:word64``)]
    \\ SIMP_TAC std_ss [WORD_SUB_INTRO,GSYM WORD_SUB_PLUS,word_add_n2w]
    \\ `(8 * (SUC (LENGTH init.init_stack)) + 8 =
         8 * (LENGTH init.init_stack + 2)) /\
        (8 * (LENGTH init.init_stack) + 16 =
         8 * (LENGTH init.init_stack + 2))` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ Q.PAT_ASSUM `0x7w && init.init_stack_bottom = 0x0w` MP_TAC
    \\ blastLib.BBLAST_TAC)
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ `^store_length - 5 <= LENGTH space` by DECIDE_TAC
  \\ IMP_RES_TAC LESS_EQ_LENGTH
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `ys1` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ REVERSE (NTAC 10 (REPEAT (Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH])
              \\ REPEAT (Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH])))
  THEN1 (SIMP_TAC std_ss [ADD1] \\ `F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC (srw_ss()++sep_cond_ss) [APPEND,one_list_def,x64_store_def,
       EVAL ``consts_zero``,STAR_ASSOC,SEP_CLAUSES,SEP_EXISTS_THM,
       one_list_exists_def,cond_STAR]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ Q.EXISTS_TAC `ys2` \\ STRIP_TAC THEN1
   (UNABBREV_ALL_TAC \\ FULL_SIMP_TAC std_ss [ADD1,LEFT_ADD_DISTRIB]
    \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
    \\ Q.PAT_ASSUM `ww = w2n init.init_heap_size` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `(ppp + 8 * LENGTH ys2) MOD 16 = 0` MP_TAC
    \\ SIMP_TAC std_ss [Once (GSYM MOD_PLUS)]
    \\ ONCE_REWRITE_TAC [GSYM (EVAL ``8 * 2:num``)]
    \\ SIMP_TAC bool_ss [GSYM MOD_COMMON_FACTOR,DECIDE ``0 < 8:num /\ 0 < 2:num``]
    \\ SIMP_TAC std_ss [GSYM DIV_DIV_DIV_MULT,RW1 [MULT_COMM] MULT_DIV]
    \\ STRIP_ASSUME_TAC (Q.SPEC `LENGTH (ys2:word64 list)`
           (MATCH_MP DIVISION (DECIDE ``0<2:num``)) |> GSYM)
    \\ POP_ASSUM (K ALL_TAC)
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
  \\ Q.ABBREV_TAC `ptr = init.init_heap_ptr`
  \\ Q.ABBREV_TAC `m = vals.memory`
  \\ Q.ABBREV_TAC `dm = vals.memory_domain`
  \\ SEP_R_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_W_TAC
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ SIMP_TAC std_ss [STAR_ASSOC]
  \\ Q.PAT_ABBREV_TAC `pat = (ww:word64 =+ vv:word64) bbb`
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ SIMP_TAC std_ss [STAR_ASSOC])
  |> SPEC_ALL |> SIMP_RULE std_ss [LET_DEF];

val new_vals = init_inv_IMP_heap_inv |> concl |> rand |> rand |> rand

val zSTACK_SETUP = let
  val th = compose_specs ["mov r5,r4","sub r5,8","mov r11,r5"]
  val th = th |> Q.INST [`r4`|->`rsp`]
  val pc = get_pc th
  val th = SPEC_FRAME_RULE th ``zR1 zGhost_stack_top top *
       zR1 zGhost_stack_bottom base * zMEMORY64 dm m *
       cond (stack_ok rsp top base stack dm m)``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``^pc * zR 0xBw (base - n2w (8 * LENGTH stack + 8)) *
      zR 0x5w (base - n2w (8 * LENGTH stack + 8)) *
      ~zS * zSTACK (base,stack) * cond (base && 7w = 0w)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC std_ss [stack_ok_def]
    \\ Q.PAT_ASSUM `rsp + x = base` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [GSYM word_arith_lemma1,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma |> Q.GENL (rev [`rsp`,`top`,`dm`,`m`])
           |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
      ``zPC p * zR 0x5w r5 * zR 0xBw r11 * ~zS * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th end

val zHEAP_SETUP = let
  val lemma = prove(``cond = ID cond``, SIMP_TAC std_ss [ID_def]);
  val th = zSTACK_SETUP |> RW1 [lemma]
  val th = SPEC_COMPOSE_RULE [th,x64_setup_res] |> SIMP_RULE (std_ss++sep_cond_ss) []
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals * cond (init_inv cs vals init)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (first_cs init,Number 0,Number 0,
                                Number 0,Number 0,FEMPTY,[],
                                first_s init,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
  gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES] \\ NTAC 2 STRIP_TAC
    THEN1 (IMP_RES_TAC init_inv_IMP_heap_inv)
    \\ FULL_SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,ID_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def]
    \\ (init_inv_IMP_heap_inv
        |> Q.INST [`vals`|->`vals with
           <| reg5 := vals.stack_bottom − n2w (8 * LENGTH vals.stack + 8)
            ; reg11 := vals.stack_bottom − n2w (8 * LENGTH vals.stack + 8) |>`]
        |> SIMP_RULE (srw_ss()) [] |> UNDISCH
        |> CONJUNCT2 |> DISCH_ALL |> RW [AND_IMP_INTRO] |> MP_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [init_inv_def] \\ Q.EXISTS_TAC `space`
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ `?r0 r1 r2 r3 r6 r7 r8 r9 r10 r12 r13 r14 r15 dm m ss.
          x64_setup (vals.reg0,vals.memory_domain,vals.memory,vals.stack) =
            (r0,r1,r2,r3,r6,r7,r8,r9,r10,r12,r13,r14,r15,dm,m,ss)` by
               METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC
    \\ (fn (hyps,tm) => EXISTS_TAC (rand (hd hyps)) (hyps,tm))
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def,LET_DEF,ID_def,first_cs_def]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
    \\ Q.PAT_ASSUM `init_inv cs vals init` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [init_inv_def]
    \\ Q.PAT_ASSUM `xx s` MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) []
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val th = Q.GEN `cs` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``INIT_STATE init * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [INIT_STATE_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


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
            isNumber x2 /\ small_int (getNumber x2) /\ ~(getNumber x2 < 0))``
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
            isNumber x2 /\ small_int (getNumber x2) /\ ~(getNumber x2 < 0))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val _ = add_compiled [th]
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
            isNumber x2 /\ small_int (getNumber x2) /\ ~(getNumber x2 < 0))``
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
            isNumber x2 /\ small_int (getNumber x2) /\ ~(getNumber x2 < 0))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val _ = add_compiled [th]
  in th end;

val reintro_word_sub32 = SIMP_CONV (srw_ss()) [] ``-(n2w n):word32`` |> GSYM

val addr_calc_def = Define `
  addr_calc x1 x2 x3 = (n2w (Num (getNumber x2)) -
                        n2w (Num (getNumber x3)) -
                        n2w (Num (getNumber x1))) :word32`;

val zHEAP_CODE_SNOC_X2_X3_IMM32 = let
  val th1 = compose_specs ["mov r15,[r9+80]","mov r14,r1","sub r14,r2",
                           "sub r14,r0","shr r14,2"]
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
  val pre = ``LENGTH s.code + 4 <= cs.code_heap_length /\ (s.code_mode = SOME F) /\
              isNumber x1 /\ small_int (getNumber x1) /\ ~(getNumber x1 < 0) /\
              isNumber x2 /\ small_int (getNumber x2) /\ ~(getNumber x2 < 0) /\
              isNumber x3 /\ small_int (getNumber x3) /\ ~(getNumber x3 < 0)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                 s with code := s.code ++ IMM32 (n2w (Num (getNumber x2)) -
                                                 n2w (Num (getNumber x3)) -
                                                 n2w (Num (getNumber x1))),NONE) *
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
         reg14 := ((vals.reg1 - vals.reg2 - vals.reg0) >>> 2 >>> 8 >>> 8 >>> 8) ;
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
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isNumber_def,getNumber_def]
    \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isNumber_def,getNumber_def]
    \\ Cases_on `x3` \\ FULL_SIMP_TAC std_ss [isNumber_def,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
         EVERY2_def,bc_value_inv_def,x64_addr_def,reintro_word_sub32]
    \\ `(n2w (Num i) = (w2w:63 word -> word32) (n2w (Num i)))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [w2w_n2w])
    \\ `(n2w (Num i') = (w2w:63 word -> word32) (n2w (Num i')))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [w2w_n2w])
    \\ `(n2w (Num i'') = (w2w:63 word -> word32) (n2w (Num i'')))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [w2w_n2w])
    \\ FULL_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`n2w (Num i):63 word`,`w`)
    \\ FULL_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`n2w (Num i'):63 word`,`v`)
    \\ FULL_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`n2w (Num i''):63 word`,`xx`)
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val th = th |> RW [GSYM addr_calc_def]
  val _ = add_compiled [th]
  in th end;


(* rewind code heap by a byte *)

val zHEAP_CODE_FRONT = let
  val th = compose_specs ["sub QWORD [r9+80],1"]
  val th = SPEC_FRAME_RULE th ``zOPTION_CODE_HEAP vals.code_option
             cs.code_heap_length cs.code_heap_ptr vals.code_list``
  val lemma = prove(
    ``SPEC m p c (q * zOPTION_CODE_HEAP code_option code_heap_length
        code_heap_ptr code_list) ==>
      code_list <> [] ==>
      SPEC m p c (q * zOPTION_CODE_HEAP code_option code_heap_length
        code_heap_ptr (FRONT code_list))``,
    REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO] SPEC_WEAKEN)
    \\ Q.EXISTS_TAC `(q *
         zOPTION_CODE_HEAP code_option code_heap_length code_heap_ptr
           code_list)` \\ FULL_SIMP_TAC std_ss [SEP_IMP_def]
    \\ Cases_on `code_option`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zOPTION_CODE_HEAP_def,zCODE_HEAP_def,
         SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
    \\ `?y l. code_list = SNOC y l` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [FRONT_SNOC] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `y::ys`
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND,LENGTH]
    \\ DECIDE_TAC)
  val th = MATCH_MP lemma th |> UNDISCH
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            s.code <> [])``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                           s with code := FRONT s.code,NONE) * ~zS * ^pc`
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
         vals.memory (vals.reg9 + 0x50w) - 0x1w) vals.memory ;
         code_list := FRONT vals.code_list |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ d ==> b /\ (c ==> d)``)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs with <| code_ptr := vs.code_ptr - 1w |>`,
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
    \\ `?y l. s.code = SNOC y l` by METIS_TAC [SNOC_CASES]
    \\ FULL_SIMP_TAC std_ss [FRONT_SNOC]
    \\ SRW_TAC [] [ADD1,GSYM word_add_n2w])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (s.code <> [])``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  in th end;


(* read code length *)

val zHEAP_CODE_LENGTH = let
  val th = compose_specs ["mov r2,[r9+80]","sub r2,[r9+96]","shl r2,2"]
  val pc = get_pc th
  val pre = ``s.code_mode = SOME F``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,Number (& (LENGTH s.code)),
                                x4,refs,stack,s,NONE) * ~zS * ^pc`
  val blast_lemma5 = prove(
    ``(-1w * w) << 2 + v << 2 = (v - w:word64) << 2``,
    blastLib.BBLAST_TAC);
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
    \\ Q.EXISTS_TAC `vals with <| reg2 := (vals.memory (vals.reg9 + 0x50w) -
        vals.memory (vals.reg9 + 0x60w)) << 2 |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`Data (2w * n2w (LENGTH s.code))`,
         `r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC
    \\ STRIP_TAC
    THEN1 (Q.PAT_ASSUM `0x7w && vs.base_ptr = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss [zOPTION_CODE_HEAP_def,zCODE_HEAP_def]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
    \\ STRIP_TAC
    \\ `LENGTH s.code < 2**62` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ SIMP_TAC std_ss [blast_lemma5,x64_addr_def]
    \\ Q.PAT_ASSUM `bb = vs.code_ptr` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ REVERSE STRIP_TAC THEN1
       (WORD_EVAL_TAC
        \\ SIMP_TAC std_ss [bitTheory.BITS_ZERO3]
        \\ SIMP_TAC std_ss [bitTheory.TIMES_2EXP_def]
        \\ AP_TERM_TAC
        \\ Q.MATCH_ABBREV_TAC`(x * 4) MOD b = ((2 * x) MOD c * 2) MOD b`
        \\ `b = 2 * c` by ( SIMP_TAC std_ss [Abbr`b`,Abbr`c`] )
        \\ POP_ASSUM SUBST1_TAC \\ Q.UNABBREV_TAC`b`
        \\ `(2 * x) MOD c = 2 * x` by (MATCH_MP_TAC LESS_MOD
                                       \\ UNABBREV_ALL_TAC
                                       \\ DECIDE_TAC )
        \\ POP_ASSUM SUBST1_TAC
        \\ FULL_SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM])
    \\ FULL_SIMP_TAC (srw_ss()) [abs_ml_inv_def,roots_ok_def,MEM]
    \\ STRIP_TAC THEN1 (METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def] \\ Q.EXISTS_TAC `f`
    \\ `small_int (&LENGTH s.code)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss [EVERY2_def,bc_value_inv_def,reachable_refs_SIMP]
    \\ STRIP_TAC THEN1
      (SRW_TAC [] [] \\ REPEAT AP_TERM_TAC \\ intLib.COOPER_TAC)
    \\ REPEAT STRIP_TAC \\ FIRST_ASSUM MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
    \\ Q.LIST_EXISTS_TAC [`x`,`r`] \\ FULL_SIMP_TAC std_ss [MEM])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val _ = add_compiled [th]
  in th end;


(* set code_start *)

val zHEAP_SET_CODE_START = let
  val th = compose_specs ["mov r15,[r9+80]","mov [r9+104],r15"]
  val pc = get_pc th
  val pre = T
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s
    with <| code_start := s.code |>,NONE) * ~zS * ^pc`
  val blast_lemma5 = prove(
    ``(-1w * w) << 2 + v << 2 = (v - w:word64) << 2``,
    blastLib.BBLAST_TAC);
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
    \\ Q.EXISTS_TAC `vals with <| reg15 := (vals.memory (vals.reg9 + 0x50w)) ;
         memory := ((vals.reg9 + 0x68w =+
                        vals.memory (vals.reg9 + 0x50w))
                         vals.memory) |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ MATCH_MP_TAC (METIS_PROVE []
         ``(b ==> b2) /\ (c /\ b1) ==> c /\ (b ==> b1 /\ b2)``)
    \\ STRIP_TAC THEN1 (SIMP_TAC (std_ss++star_ss) [])
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs with code_start_ptr := vs.code_ptr`,`r1`,`r2`,`r3`,
         `r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC
    \\ STRIP_TAC
    THEN1 (Q.PAT_ASSUM `0x7w && vs.base_ptr = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ Q.ABBREV_TAC `m = vals.memory`
    \\ Q.ABBREV_TAC `dm = vals.memory_domain`
    \\ SEP_W_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND,SEP_CLAUSES]
  val _ = add_compiled [th]
  in th end;


(* jump to code_start *)

val zHEAP_JMP_CODE_START = let
  val th = compose_specs ["mov r15,[r9+104]","jmp r15"]
  val pre = T
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS *
                         zPC (cs.code_heap_ptr + n2w (LENGTH s.code_start))`
  val blast_lemma5 = prove(
    ``(-1w * w) << 2 + v << 2 = (v - w:word64) << 2``,
    blastLib.BBLAST_TAC);
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
    \\ Q.EXISTS_TAC `vals with <| reg15 := (vals.memory (vals.reg9 + 104w)) |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ `vals.memory (vals.reg9 + 0x68w) =
        n2w (LENGTH s.code_start) + cs.code_heap_ptr` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def]
      \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
      \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
      \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (METIS_PROVE []
         ``(b ==> b2) /\ (c /\ b1) ==> c /\ (b ==> b1 /\ b2)``)
    \\ STRIP_TAC THEN1 (SIMP_TAC (std_ss++star_ss) [])
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC (srw_ss()) [STAR_ASSOC,SEP_CLAUSES] \\ SEP_R_TAC
    \\ Q.PAT_ASSUM `0x7w && vs.base_ptr = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO]
              |> RW [GSYM SPEC_MOVE_COND,SEP_CLAUSES]
  in th end;


(* switch code_mode from SOME T to SOME F *)

val zHEAP_CODE_UNSAFE = let
  val th = zCODE_HEAP_UNSAFE |> RW [GSYM zOPTION_CODE_HEAP_def]
                             |> RW [ASSUME ``SOME T = mode``]
  val th1 = compose_specs ["xor r15,r15"]
  val th = SPEC_COMPOSE_RULE [th,th1]
  val pc = get_pc th
  val pre = ``s.code_mode = SOME T``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                                s with code_mode := SOME F,NONE) * ~zS * ^pc`
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
    \\ Q.EXISTS_TAC `vals with <| code_option := SOME F ; reg15 := 0w |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ d ==> b /\ (c ==> d)``)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val _ = add_compiled [th]
  in th end;


(* switch code_mode from SOME F to SOME T *)

val zHEAP_CODE_SAFE = let
  val th1 = compose_specs ["mov r15,r0","mov r14,r1","mov r13,r2",
                           "mov r12,r3","xor r0,r0"]
  val th2 = zCODE_HEAP_SAFE |> RW [GSYM zOPTION_CODE_HEAP_def]
  val th3 = compose_specs ["mov r0,r15","mov r1,r14","mov r2,r13","mov r3,r12"]
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = th |> RW [ASSUME ``SOME F = mode``]
  val pc = get_pc th
  val pre = ``s.code_mode = SOME F``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
                                s with code_mode := SOME T,NONE) * ~zS * ^pc`
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
    \\ Q.EXISTS_TAC `vals with <| code_option := SOME T ;
           reg15 := vals.reg0 ;
           reg14 := vals.reg1 ;
           reg13 := vals.reg2 ;
           reg12 := vals.reg3 |>`
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b /\ d ==> b /\ (c ==> d)``)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ ASM_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_IMP_EXISTS]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [code_heap_inv_def,heap_vars_ok_def])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
       AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val _ = add_compiled [th]
  in th end;


(* test for printing_on *)

val heap_inv_IGNORE_reg15 = prove(
  ``heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals ==>
    heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) (vals with reg15 := w)``,
  SIMP_TAC (srw_ss()) [heap_inv_def]);

val zHEAP_TEST_PRINTING_ON = let
  val th = spec "mov r15,DWORD [r9+144]"
  val th = SPEC_COMPOSE_RULE [th,spec "test r15,r15"]
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
              |> UNDISCH |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (s.local.printing_on = 0w)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ NTAC 2 STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,one_list_def,
        word_arith_lemma1,STAR_ASSOC] \\ SEP_R_TAC
      \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [heap_vars_ok_def]
      \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`vals with <| reg15 := vals.memory (vals.reg9 + 144w) |>`]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,zVALS_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ `(vals.memory (vals.reg9 + 0x90w)) = (s.local.printing_on)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,one_list_def,
        word_arith_lemma1,STAR_ASSOC] \\ SEP_R_TAC \\ SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC
    THEN1 FULL_SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC heap_inv_IGNORE_reg15 \\ ASM_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;


(* set printing_on to 1w *)

val zHEAP_SET_PRINTING_ON = let
  val th = compose_specs ["mov r15,1","mov [r9+144],r15"]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s with local := (s.local with printing_on := 1w),
       NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ NTAC 2 STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,one_list_def,
        word_arith_lemma1,STAR_ASSOC] \\ SEP_R_TAC
      \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [heap_vars_ok_def]
      \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`vals with <| reg15 := 1w ;
         memory := ((vals.reg9 + 0x90w =+ 0x1w) vals.memory) |>`]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,zVALS_def]
    \\ SIMP_TAC (srw_ss()) []
    \\ REVERSE STRIP_TAC
    THEN1 FULL_SIMP_TAC (std_ss++star_ss) []
    \\ MATCH_MP_TAC heap_inv_IGNORE_reg15
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs with local := (s.local with printing_on := 1w)`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,x64_store_def,one_list_def,
        word_arith_lemma1,STAR_ASSOC] \\ SEP_R_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def,SEP_CLAUSES]
    \\ Q.ABBREV_TAC `m = vals.memory`
    \\ Q.ABBREV_TAC `dm = vals.memory_domain`
    \\ SEP_W_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
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
  val _ = add_compiled [th];
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

val zHEAP_MOVE_12 = zHEAP_Move (x2,x1)
val zHEAP_MOVE_21 = el 1 moves
val zHEAP_MOVE_32 = el 5 moves
val zHEAP_MOVE_13 = zHEAP_Move (x3,x1)
val zHEAP_MOVE_31 = zHEAP_Move (x1,x3)
val zHEAP_MOVE_32 = zHEAP_Move (x2,x3)
val zHEAP_MOVE_23 = zHEAP_Move (x3,x2)
val zHEAP_MOVE_34 = zHEAP_Move (x4,x3)
val zHEAP_MOVE_14 = zHEAP_Move (x4,x1)
val zHEAP_MOVE_41 = zHEAP_Move (x1,x4)


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
  ``abs_ml_inv (x::stack) refs (r1::roots,heap,a,sp) l /\ n < 2305843009213693952 ==>
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
    \\ ASM_SIMP_TAC std_ss [bc_value_inv_def] \\ SRW_TAC [] [])
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
     (`k < 2305843009213693952` by DECIDE_TAC
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
  val _ = add_compiled [th];
  in () end;

val _ = map (derive_const_assign zHEAP_Num1) (up_to 256)
val _ = map (derive_const_assign zHEAP_Num2) (up_to 256)
val _ = map (derive_const_assign zHEAP_Num3) (up_to 256)
val _ = map (derive_const_assign zHEAP_Num4) (up_to 256)

(* cons with NIL *)

val abs_ml_inv_Block_NIL = prove(
  ``abs_ml_inv (x::stack) refs (r1::roots,heap,a,sp) l /\ n < 2305843009213693952 ==>
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
     (`k < 2305843009213693952` by DECIDE_TAC
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
  val _ = add_compiled [th0];
  val _ = add_compiled [th1];
  in th end

val zHEAP_Nil1 = zHEAP_Nil ("B8",``1:num``) |> foo
val zHEAP_Nil2 = zHEAP_Nil ("B9",``2:num``) |> foo
val zHEAP_Nil3 = zHEAP_Nil ("BA",``3:num``) |> foo
val zHEAP_Nil4 = zHEAP_Nil ("BB",``4:num``) |> foo

val zHEAP_Nil = zHEAP_Nil ("B8",``1:num``)

(* push x1,x2,x3,x4 *)

val push_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4)]`,
              `[(x1,r1);(x2,r2);(x3,r3);(x4,r4);(x5,r5)]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM]

val side = ``NONE :(num # x64_vals -> bool) option``
val gc_side = ``SOME (\((sp :num),(vals :x64_vals)).
                  (ttt13 = vals.reg13) /\ (ttt14 = vals.reg14))``

fun zHEAP_PUSH n side = let
  val th = if n = ``1:num`` then x64_push_r0 else
           if n = ``2:num`` then x64_push_r1 else
           if n = ``3:num`` then x64_push_r2 else
           if n = ``4:num`` then x64_push_r3 else fail()
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^side) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,
                   (if ^n = 1 then x1 else
                    if ^n = 2 then x2 else
                    if ^n = 3 then x3 else
                    if ^n = 4 then x4 else ARB)::stack,s,^side) * ~zS * ^pc`
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
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^side) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;

val zHEAP_PUSH1 = zHEAP_PUSH ``1:num`` side
val zHEAP_PUSH2 = zHEAP_PUSH ``2:num`` side
val zHEAP_PUSH3 = zHEAP_PUSH ``3:num`` side
val zHEAP_PUSH4 = zHEAP_PUSH ``4:num`` side

val _ = add_compiled [zHEAP_PUSH1,zHEAP_PUSH2,zHEAP_PUSH3,zHEAP_PUSH4];

val zHEAP_PUSH1_GC = zHEAP_PUSH ``1:num`` gc_side
val zHEAP_PUSH2_GC = zHEAP_PUSH ``2:num`` gc_side
val zHEAP_PUSH3_GC = zHEAP_PUSH ``3:num`` gc_side
val zHEAP_PUSH4_GC = zHEAP_PUSH ``4:num`` gc_side

(* pop x1,x2,x3,x4 *)

val pop_lemma =
  abs_ml_inv_stack_permute
  |> Q.SPECL [`[(x1,r1);(x2,r2);(x3,r3);(x4,r4);(x5,r5)]`,
              `[(x1',r1');(x2',r2');(x3',r3');(x4',r4')]`]
  |> SIMP_RULE std_ss [MAP,APPEND,SUBSET_DEF,MEM] |> GEN_ALL

fun zHEAP_POP n side = let
  val th = if n = ``1:num`` then x64_pop_r0 else
           if n = ``2:num`` then x64_pop_r1 else
           if n = ``3:num`` then x64_pop_r2 else
           if n = ``4:num`` then x64_pop_r3 else fail()
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val target = ``zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,^side) vals /\ stack <> [])``
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
  val th = th |> Q.SPEC `zHEAP (cs,^x1,^x2,^x3,^x4,refs,TL stack,s,^side) * ^pc`
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
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, ^side) * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  in th end;

val zHEAP_POP1 = zHEAP_POP ``1:num`` side
val zHEAP_POP2 = zHEAP_POP ``2:num`` side
val zHEAP_POP3 = zHEAP_POP ``3:num`` side
val zHEAP_POP4 = zHEAP_POP ``4:num`` side

val _ = add_compiled [zHEAP_POP1,zHEAP_POP2,zHEAP_POP3,zHEAP_POP4]

val zHEAP_POP1_GC = zHEAP_POP ``1:num`` gc_side
val zHEAP_POP2_GC = zHEAP_POP ``2:num`` gc_side
val zHEAP_POP3_GC = zHEAP_POP ``3:num`` gc_side
val zHEAP_POP4_GC = zHEAP_POP ``4:num`` gc_side


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

fun gen_load k = let
  val th = zHEAP_LOAD |> Q.INST [`k`|->k] |> SIMP_RULE (srw_ss()) [IMM32_def]
  val _ = add_compiled [th]
  in th end

val _ = map gen_load [`0:num`, `1:num`, `2:num`, `3:num`,
                      `4:num`, `5:num`, `6:num`, `7:num`]


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

val zHEAP_ID_1234 = let
  val (th,goal) = SPEC_WEAKEN_RULE zHEAP_NOP
    ``let (x1,x2,x3,x4) = ID (x1,x2,x3,x4) in
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ¬zS * zPC (p + 0x3w))``
  val lemma = prove(goal,FULL_SIMP_TAC std_ss [SEP_IMP_REFL,ID_def,LET_DEF])
  val th = MP th lemma
  val _ = add_compiled [th]
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


(* main part of Shift instruction *)

val NTIMES_def = Define `
  (NTIMES 0 xs = []) /\
  (NTIMES (SUC n) xs = xs ++ NTIMES n xs)`;

val n_times_def = Define `
  (n_times 0 f x = x) /\
  (n_times (SUC n) f x = n_times n f (f x))`;

val n_times_pre_def = Define `
  (n_times_pre 0 f g x = T) /\
  (n_times_pre (SUC n) f g x = g x /\ n_times_pre n f g (f x))`;

val LENGTH_NTIMES = prove(
  ``!k xs. LENGTH (NTIMES k xs) = k * LENGTH xs``,
  Induct \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,MULT_CLAUSES]
  \\ DECIDE_TAC);

val LENGTH_IMM32 = prove(
  ``LENGTH (IMM32 w) = 4``,
  EVAL_TAC);

val SPEC_NTIMES = prove(
  ``(!x t. SPEC X64_MODEL
                (p x * zPC t * cond (g x)) {(t,ys)}
                (p (f x) * zPC (t + n2w (LENGTH ys)))) ==>
    (!x t. SPEC X64_MODEL
                (p x * zPC t * cond (n_times_pre k f g x)) {(t,NTIMES k ys)}
                (p (n_times k f x) * zPC (t + n2w (LENGTH (NTIMES k ys)))))``,
  STRIP_TAC \\ Induct_on `k`
  \\ SIMP_TAC std_ss [n_times_pre_def,n_times_def,NTIMES_def,LENGTH,
      WORD_ADD_0,SEP_CLAUSES,SPEC_REFL]
  \\ FULL_SIMP_TAC std_ss [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (prog_x64Theory.SPEC_X64_MERGE_CODE
       |> RW [AND_IMP_INTRO] |> GEN_ALL)
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (SPEC_COMPOSE |> Q.SPECL [`x`,`p`,`{t}`,`m`,`{t'}`]
       |> RW [INSERT_UNION_EQ,UNION_EMPTY] |> GEN_ALL)
  \\ Q.EXISTS_TAC `(p (f x) * zPC (t + n2w (LENGTH ys)))`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,GSYM word_arith_lemma1,WORD_ADD_ASSOC])
  |> Q.INST [`k`|->`i`];

val n_stores_def = Define `
  n_stores i k x1 (stack:bc_value list) =
    (n_times i
       (\(x1,stack). (HD stack,LUPDATE (HD stack) k (TL stack)))
          (x1,stack))`;

val n_stores_pre_def = Define `
  n_stores_pre i k x1 (stack:bc_value list) =
    (n_times_pre i
             (λ(x1,stack). (HD stack,LUPDATE (HD stack) k (TL stack)))
             (λ(x1,stack).
                k < 268435456 ∧ k < LENGTH (TL stack) ∧ stack ≠ []) (x1,stack))`;

val zHEAP_SIMPLE_Shift = let
  val th = SPEC_COMPOSE_RULE [zHEAP_POP1,zHEAP_STORE]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [LENGTH,ADD1,IMM32_def])) th
  val th = SIMP_RULE std_ss [GSYM LENGTH_NIL,LENGTH_LUPDATE,APPEND] th
  val th = SIMP_RULE (std_ss++sep_cond_ss) [LENGTH_NIL] th
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``((\(x1,stack). zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS) (x1,stack) *
       zPC p * cond ((\(x1,stack). k < 268435456 /\
          k < LENGTH (TL stack) /\ stack <> []) (x1,stack)))``
  val th = MP th (prove(goal,
    SIMP_TAC (std_ss++star_ss) [SEP_IMP_def,cond_STAR,GSYM LENGTH_NIL]))
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``((\(x1,stack). zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS)
         ((\(x1,stack). (HD stack,
                         LUPDATE (HD stack) k (TL stack))) (x1:bc_value,stack))) *
       zPC (p + n2w (LENGTH (0x48w::0x58w::0x48w::0x89w::0x84w::
                             0x24w::IMM32 (n2w (8 * k)))))``
  val lemma = SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL,cond_STAR,
                 IMM32_def,LENGTH,APPEND] goal
  val th = RW [lemma] th
  val th = INST [``x1:bc_value``|->``FST (y:bc_value # bc_value list)``,
                 ``stack:bc_value list``|->``SND (y:bc_value # bc_value list)``] th
           |> RW [PAIR] |> Q.GENL [`p`,`y`]
  val th = HO_MATCH_MP SPEC_NTIMES th
  val th = th |> Q.SPEC `(x1,stack)`
              |> SIMP_RULE std_ss [LENGTH_NTIMES,LENGTH,LENGTH_APPEND,LENGTH_IMM32]
              |> RW [GSYM n_stores_def,GSYM n_stores_pre_def]
              |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
              |> Q.INST [`k`|->`n`] |> SPEC_ALL
  val th1 = SPEC_COMPOSE_RULE [zHEAP_POPS,zHEAP_MOVE_21]
  val th1 = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th1
            |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32]
  val th = SPEC_COMPOSE_RULE [zHEAP_MOVE_12,th,th1]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
           |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
           |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32,LENGTH_APPEND,LENGTH_NTIMES]
  in th end;

val SND_n_stores = prove(
  ``!xs ys ts zs n x1.
      (LENGTH ts = LENGTH xs) /\ (n = LENGTH (xs ++ ys) - 1) /\
      LENGTH (xs ++ ys) < 268435457 ==>
      n_stores_pre (LENGTH xs) n x1 (xs ++ ys ++ ts ++ zs) /\
      (SND (n_stores (LENGTH xs) n x1 (xs ++ ys ++ ts ++ zs)) =
       ys ++ xs ++ zs)``,
  SIMP_TAC std_ss [] \\ Induct
  \\ Cases_on `ts` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1] THEN1
   (FULL_SIMP_TAC std_ss [APPEND,APPEND_NIL,LENGTH] \\ EVAL_TAC
    \\ SIMP_TAC std_ss [rich_listTheory.DROP_LENGTH_APPEND])
  \\ REPEAT GEN_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [n_stores_def,n_stores_pre_def,GSYM ADD1]
  \\ SIMP_TAC std_ss [n_times_def,n_times_pre_def,HD,APPEND,TL,LENGTH,ADD1]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ REPEAT (STRIP_TAC THEN1 (SRW_TAC [] [] \\ DECIDE_TAC))
  \\ `LUPDATE h' (LENGTH (xs ++ ys)) (xs ++ ys ++ h::t ++ zs) =
      xs ++ ys ++ h'::t ++ zs` by ALL_TAC THEN1
   (`xs ++ ys ++ h::t ++ zs = (xs ++ ys) ++ h::(t ++ zs)` by ALL_TAC
    \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
  \\ FULL_SIMP_TAC std_ss []
  \\ `xs ++ ys ++ h'::t ++ zs = xs ++ (SNOC h' ys) ++ t ++ zs` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss []
  \\ `LENGTH (xs ++ SNOC h' ys) < 268435457` by ALL_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC) \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_SNOC]
  \\ REPEAT STRIP_TAC
  \\ `LENGTH xs + SUC (LENGTH ys) - 1 = LENGTH xs + LENGTH ys` by DECIDE_TAC
  \\ `!n. LENGTH xs + SUC (LENGTH ys) < 1 + n <=>
          LENGTH xs + LENGTH ys < n` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);


(* general case of Shift *)

val n_loads_def = Define `
  n_loads i k x1 (stack:bc_value list) =
    (n_times i (λ(x1,stack). (EL k stack,EL k stack::stack))
             (x1,stack))`

val n_loads_pre_def = Define `
  n_loads_pre i k x1 (stack:bc_value list) =
    (n_times_pre i (λ(x1,stack). (EL k stack,EL k stack::stack))
             (λ(x1,stack). k < 268435456 ∧ k < LENGTH stack)
             (x1,stack))`;

val SND_n_loads = prove(
  ``!xs ys stack x1.
      LENGTH (ys ++ xs) < 268435457 ==>
      n_loads_pre (LENGTH xs) (LENGTH (ys++xs) - 1) x1 (ys ++ xs ++ stack) /\
      (SND (n_loads (LENGTH xs) (LENGTH (ys++xs) - 1) x1 (ys ++ xs ++ stack)) =
         xs ++ ys ++ xs ++ stack)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ STRIP_TAC
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ REPEAT GEN_TAC \\ STRIP_TAC \\ REPEAT GEN_TAC
  \\ REPEAT GEN_TAC \\ STRIP_TAC \\ REPEAT GEN_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,n_loads_def,n_loads_pre_def,LENGTH_SNOC]
  \\ ONCE_REWRITE_TAC [n_times_def,n_times_pre_def]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ REPEAT (STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_SNOC]
       \\ SRW_TAC [] [] \\ DECIDE_TAC))
  \\ `LENGTH (ys ++ SNOC x xs) − 1 = LENGTH (ys ++ xs)` by ALL_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `(ys ++ (SNOC x xs ++ stack)) = (ys ++ xs) ++ x::stack` by ALL_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [EL_LENGTH]
  \\ `LENGTH (ys ++ xs) = LENGTH ((x::ys) ++ xs) - 1` by ALL_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x::ys`,`x::stack`,`x`])
  \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,SNOC_APPEND]
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_APPEND,LENGTH_SNOC,LENGTH,ADD1,
       AC ADD_COMM ADD_ASSOC,AC CONJ_COMM CONJ_ASSOC,
       METIS_PROVE [] ``p /\ p /\ q <=> p /\ q``])
  |> Q.SPECL [`xs`,`[]`] |> RW [APPEND_NIL,APPEND]

val zHEAP_GENERAL_Shift = let
  val th = SPEC_COMPOSE_RULE [zHEAP_LOAD,zHEAP_PUSH1]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [LENGTH,ADD1,IMM32_def])) th
  val th = SIMP_RULE std_ss [GSYM LENGTH_NIL,LENGTH_LUPDATE,APPEND] th
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``((\(x1,stack). zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS) (x1,stack) *
       zPC p * cond ((\(x1,stack). k < 268435456 /\
          k < LENGTH stack) (x1,stack)))``
  val th = MP th (prove(goal,
    SIMP_TAC (std_ss++star_ss) [SEP_IMP_def,cond_STAR,GSYM LENGTH_NIL]))
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``((\(x1,stack). zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS)
         ((\(x1,stack). (EL k stack,
                         EL k stack::stack)) (x1:bc_value,stack))) *
       zPC (p + n2w (LENGTH (0x48w::0x8Bw::0x84w::0x24w::
                             (IMM32 (n2w (8 * k)) ++ [0x48w; 0x50w]))))``
  val lemma = SIMP_CONV (std_ss++star_ss) [SEP_IMP_REFL,cond_STAR,
                 IMM32_def,LENGTH,APPEND] goal
  val th = RW [lemma] th
  val th = INST [``x1:bc_value``|->``FST (y:bc_value # bc_value list)``,
                 ``stack:bc_value list``|->``SND (y:bc_value # bc_value list)``] th
           |> RW [PAIR] |> Q.GENL [`p`,`y`]
  val th = HO_MATCH_MP SPEC_NTIMES th
  val th = th |> Q.SPEC `(x1,stack)`
              |> SIMP_RULE std_ss [LENGTH_NTIMES,LENGTH,LENGTH_APPEND,LENGTH_IMM32]
              |> RW [GSYM n_loads_def,GSYM n_loads_pre_def]
              |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
              |> Q.INST [`k`|->`n`] |> SPEC_ALL
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH1,th]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
            |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32]
            |> Q.INST [`i`|->`i1`,`n`|->`n1`]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_POP1]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
           |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32,LENGTH_APPEND,LENGTH_NTIMES]
  val th = SPEC_COMPOSE_RULE [zHEAP_NOP,th,zHEAP_SIMPLE_Shift]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
           |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32,LENGTH_APPEND,LENGTH_NTIMES]
  val th = MATCH_MP prog_x64Theory.SPEC_X64_MERGE_CODE th
           |> SIMP_RULE std_ss [LENGTH,LENGTH_IMM32,LENGTH_APPEND,LENGTH_NTIMES]
  val th = th |> RW [GSYM APPEND_ASSOC,APPEND]
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
  val th = spec "mov r11,r4" |> Q.INST [`rip`|->`p`,`r4`|->`rsp`]
  val th = SPEC_FRAME_RULE th ``zR1 zGhost_stack_top top *
       zR1 zGhost_stack_bottom base * zMEMORY64 dm m *
       cond (stack_ok rsp top base stack dm m)``
  val (th,goal) = SPEC_WEAKEN_RULE th
                  ``zPC (p + 0x3w) * zR 0xBw (base - n2w (8 * LENGTH stack)) *
                    zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC std_ss [stack_ok_def]
    \\ Q.PAT_ASSUM `rsp + xx = base` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_ADD_SUB,zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL (rev [`rsp`,`top`,`dm`,`m`])
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
                  ``zPC p * zR 0xBw r11 * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th end;

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

val LENGTH_LESS_EQ_ALT = prove(
  ``!xs m. m <= LENGTH xs ==> ?ys zs. (xs = ys ++ zs) /\ (LENGTH zs = m)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Cases_on `m` \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND,APPEND_NIL]
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`ys`,`zs ++ [x]`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,APPEND_ASSOC,LENGTH_APPEND,ADD1]);

val x64_mov_r4_r11 = let
  val th = compose_specs ["mov r4,r11"]
  val pre = ``w2n (base - r11:word64) DIV 8 <= LENGTH (ss:word64 list) /\
              (w2n (base - r11:word64) MOD 8 = 0)``
  val pc = get_pc th
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zMEMORY64 dm m *
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base ss dm m /\ ^pre)``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``^pc * zR 0xBw r11 *
        zSTACK (base,DROP (LENGTH ss - w2n (base - r11) DIV 8) ss)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`r11`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def] \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `base - r11` \\ FULL_SIMP_TAC (std_ss) [w2n_n2w]
    \\ MP_TAC (MATCH_MP DIVISION (DECIDE ``0 < 8:num``) |> Q.SPEC `n`)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.ABBREV_TAC `k = n DIV 8`
    \\ POP_ASSUM (K ALL_TAC) \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ `r11 = base - n2w (k * 8)` by ALL_TAC THEN1
      (Q.PAT_ASSUM `base - r11 = xx` (ASSUME_TAC o GSYM)
       \\ FULL_SIMP_TAC std_ss [WORD_SUB_SUB]
       \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
       \\ SIMP_TAC std_ss [WORD_ADD_SUB])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [stack_ok_def]
    \\ IMP_RES_TAC LENGTH_LESS_EQ_ALT
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD,AC MULT_ASSOC MULT_COMM]
    \\ STRIP_TAC THEN1
     (SIMP_TAC std_ss [GSYM word_mul_n2w]
      \\ Q.PAT_ASSUM `base && 0x7w = 0x0w` MP_TAC
      \\ blastLib.BBLAST_TAC)
    \\ Q.EXISTS_TAC `rest ++ ys`
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,AC ADD_COMM ADD_ASSOC,
         AC MULT_ASSOC MULT_COMM,APPEND_ASSOC] \\ SRW_TAC [] [])
  val th = MP th lemma
  val th = th |> Q.GENL (rev [`rsp`,`top`,`dm`,`m`])
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR 0xBw r11 * zSTACK (base,ss) * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th end;

val abs_ml_inv_PushExc = prove(
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

val STACK_LENGTH_LEMMA = prove(
  ``SPEC m (x * zVALS cs vals * cond g) c q <=>
    SPEC m (x * zVALS cs vals *
            cond (g /\ 8 * LENGTH vals.stack < 2 ** 64)) c q``,
  Cases_on `8 * LENGTH vals.stack < 2 ** 64` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
  \\ SIMP_TAC std_ss [zVALS_def,zSTACK_def]
  \\ `!rsp top dm m. ~stack_ok rsp top vals.stack_bottom vals.stack dm m` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]
  \\ SIMP_TAC std_ss [stack_ok_def] \\ REPEAT STRIP_TAC
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LEFT_ADD_DISTRIB]
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
  val th = RW1 [STACK_LENGTH_LEMMA] th
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
    \\ STRIP_TAC \\ Q.PAT_ASSUM `xx = yy` (ASSUME_TAC o GSYM)
    \\ Q.PAT_ASSUM `8 * LENGTH xx < yy` ASSUME_TAC
    \\ `w2n (vals.stack_bottom - (vals.reg11 - 0x8w)) =
        8 * (LENGTH cs.rest_of_stack + LENGTH l2 + 3)` by ALL_TAC THEN1
     (FULL_SIMP_TAC (std_ss++sep_cond_ss) [heap_inv_def,stack_inv_def,cond_STAR]
      \\ Q.PAT_ASSUM `xx = cs.stack_trunk` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,stack_inv_def,LENGTH,LENGTH_APPEND]
      \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,WORD_SUB_SUB2]
      \\ SIMP_TAC std_ss [word_add_n2w,w2n_n2w]
      \\ `(8 * LENGTH cs.rest_of_stack + (16 + (8 * LENGTH l2 + 8)))
            < dimword (:64)` by ALL_TAC THEN1
       (Q.PAT_ASSUM `8 * LENGTH xss < nnn` MP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [LEFT_ADD_DISTRIB,ADD1]
        \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
        \\ IMP_RES_TAC EVERY2_IMP_LENGTH
        \\ POP_ASSUM (MP_TAC o GSYM)
        \\ SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
        \\ REPEAT STRIP_TAC \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] (CONJ MULT_DIV MOD_EQ_0)]
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
    \\ IMP_RES_TAC abs_ml_inv_PushExc
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
  val th = RW1 [GSYM STACK_LENGTH_LEMMA] th
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


(* LoadRev *)

val sw2sw_lemma =
  sw2sw_def |> INST_TYPE [``:'a``|->``:32``,``:'b``|->``:64``]
            |> SIMP_RULE (srw_ss()) [] |> GSYM

val sub_imm32_lemma = prove(
  ``(offset:num) <= 2 ** 28 ==>
    (base + sw2sw (- (n2w:num->word32) (8 * offset)) =
     base - n2w (8 * offset):word64)``,
  SIMP_TAC (srw_ss()) [sw2sw_def] \\ REPEAT STRIP_TAC
  \\ `(8 * offset) < 4294967296` by DECIDE_TAC
  \\ `(8 * offset) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `offset = 0` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ `(4294967296 - 8 * offset) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [bitTheory.SIGN_EXTEND_def,LET_DEF]
  \\ Cases_on `BIT 31 (4294967296 - 8 * offset)`
  THEN1 (IMP_RES_TAC (DECIDE ``m < n ==> (k + (n - m) = (k+n) - m:num)``)
         \\ FULL_SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM2]
  \\ POP_ASSUM MP_TAC
  \\ `(4294967296 - 8 * offset) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [DIV_EQ_X]
  \\ REPEAT STRIP_TAC
  \\ DECIDE_TAC);

val x64_mov_r0_r5 = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec_memory64 "488B85"
  val th = th |> Q.INST [`rip`|->`p`,`imm32`|->`- n2w (8 * offset)`,`r5`|->`base`]
  val th = RW [GSYM IMM32_def,sw2sw_lemma,UNDISCH sub_imm32_lemma] th
  val th = th |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  val th = th |> Q.INST [`base`|->`base - extra`]
  val pc = get_pc th
  val pre = ``w2n (extra + n2w (8 * offset)) DIV 8 < LENGTH (stack:word64 list) /\
              (w2n ((extra:word64) + n2w (8 * offset)) MOD 8 = 0) /\
              offset <= 2 ** 28``
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`,
                         `base`|->`base-8w`]
  val th = SPEC_FRAME_RULE th ``zR1 RSP rsp *
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ ^pre)``
  val (th,goal) = SPEC_WEAKEN_RULE th ``(^pc * zR 0x5w (base - 8w - extra) *
      zR 0x0w (EL (w2n (extra + n2w (8 * offset)) DIV 8) (REVERSE stack)) *
      zSTACK (base,stack))``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_REV_EL
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def,WORD_SUB_PLUS])
  val th = MP th lemma
  val th = th |> Q.GENL (rev [`rsp`,`top`,`dm`,`m`])
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR 0x5w (base - 0x8w - extra) *
      zR 0x0w r0 * zSTACK (base,stack) * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_REV_EL
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def,WORD_SUB_PLUS])
  val th = MP th lemma
  in th end;

val LENGTH_LESS_REV = prove(
  ``!xs m. m < LENGTH xs ==> ?ys z zs. (xs = ys ++ z::zs) /\ (LENGTH zs = m)``,
  recInduct SNOC_INDUCT \\ SIMP_TAC std_ss [LENGTH,LENGTH_SNOC]
  \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Cases_on `m` \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND,CONS_11,APPEND_NIL]
  THEN1 (METIS_TAC []) \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`ys`,`z`,`zs ++ [x]`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC,LENGTH_APPEND,ADD1]);

val LENGTH_EQ_IMP_EL = prove(
  ``(LENGTH xs = k) ==> (EL k (REVERSE xs ++ y::ys) = y)``,
  METIS_TAC [EL_LENGTH,LENGTH_MAP,LENGTH_REVERSE]);

val LENGTH_EQ_IMP_EL_MAP = prove(
  ``(LENGTH xs = k) ==> (EL k (MAP f (REVERSE xs) ++ y::ys) = y)``,
  METIS_TAC [EL_LENGTH,LENGTH_MAP,LENGTH_REVERSE]);

val EL_APPEND_LEMMA = prove(
  ``(k = LENGTH xs + l) ==> (EL k (xs ++ ys) = EL l ys)``,
  FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2]);

val zHEAP_LoadRev = let
  val th = x64_mov_r0_r5
           |> DISCH ``base - 8w - extra = w:word64``
           |> SIMP_RULE std_ss [] |> RW [GSYM SPEC_MOVE_COND]
           |> Q.INST [`offset`|->`offset+1`]
  val pc = get_pc th
  val pre = ``offset + s.base_offset < LENGTH (stack:bc_value list) /\
              offset < 268435456``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = th |> Q.INST [`extra`|->`8w + n2w (8 * s.base_offset) + n2w (8 * LENGTH cs.rest_of_stack)`]
  val th = RW1 [STACK_LENGTH_LEMMA] th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,EL (offset + s.base_offset) (REVERSE stack),
                                x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
  gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [stack_inv_def]
    \\ Q.PAT_ASSUM `xxx = cs.stack_trunk` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [word_add_n2w]
    \\ `8 + 8 * s.base_offset + 8 * LENGTH cs.rest_of_stack + 8 * (offset + 1) =
        8 * (2 + s.base_offset + LENGTH cs.rest_of_stack + offset)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `8 * (2 + s.base_offset + LENGTH cs.rest_of_stack + offset) < 2**64` by
     (`LENGTH stack = LENGTH roots` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def,APPEND]
        \\ IMP_RES_TAC EVERY2_IMP_LENGTH)
      \\ Q.PAT_ASSUM `8 * LENGTH vals.stack < ll` MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,EVAL ``dimword (:64)``]
    \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] MOD_EQ_0]
    \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV]
    \\ STRIP_TAC THEN1
     (STRIP_TAC THEN1
        (SIMP_TAC std_ss [word_arith_lemma1] \\ NTAC 2 AP_TERM_TAC \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,LENGTH_MAP]
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,
           APPEND,EVERY2_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH \\ DECIDE_TAC)
    \\ `(EL (2 + s.base_offset + LENGTH cs.rest_of_stack + offset)
          (REVERSE (MAP (x64_addr vs.current_heap) roots ++
            0x1w::cs.ret_address::cs.rest_of_stack))) =
         EL (offset + s.base_offset)
          (REVERSE (MAP (x64_addr vs.current_heap) roots))` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [REVERSE_APPEND,APPEND]
      \\ MATCH_MP_TAC EL_APPEND_LEMMA
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg0 := (EL (offset + s.base_offset) (REVERSE (MAP
         (x64_addr vs.current_heap) roots)))`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC
    THEN1 (SIMP_TAC (srw_ss()) [zVALS_def] \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ POP_ASSUM (K ALL_TAC)
    \\ SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`EL (offset + s.base_offset) (REVERSE roots)`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,stack_inv_def]
    \\ SIMP_TAC std_ss [CONJ_ASSOC]
    \\ REVERSE STRIP_TAC
    THEN1 FULL_SIMP_TAC std_ss [word_sub_def,AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ REVERSE STRIP_TAC
    THEN1 FULL_SIMP_TAC std_ss [word_sub_def,AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SIMP_TAC std_ss [GSYM rich_listTheory.MAP_REVERSE]
    \\ `LENGTH stack = LENGTH roots` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
      \\ IMP_RES_TAC EVERY2_IMP_LENGTH)
    \\ `offset + s.base_offset < LENGTH roots` by DECIDE_TAC
    \\ IMP_RES_TAC LENGTH_LESS_REV
    \\ FULL_SIMP_TAC std_ss [REVERSE_APPEND,REVERSE_DEF]
    \\ SIMP_TAC std_ss [MAP_APPEND,MAP,GSYM APPEND_ASSOC,APPEND]
    \\ IMP_RES_TAC LENGTH_EQ_IMP_EL
    \\ ASM_SIMP_TAC std_ss [LENGTH_EQ_IMP_EL]
    \\ REVERSE STRIP_TAC
    THEN1 (MATCH_MP_TAC LENGTH_EQ_IMP_EL_MAP \\ FULL_SIMP_TAC std_ss [])
    \\ Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH]
    \\ `LENGTH ys' = LENGTH ys` by DECIDE_TAC
    \\ Q.PAT_ASSUM `LENGTH ys' = LENGTH ys` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [roots_ok_def,MEM,MEM_APPEND]
    THEN1 (FULL_SIMP_TAC std_ss [MEM_APPEND,SUBSET_DEF,MEM_MAP] \\ METIS_TAC [])
    \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_ASSUM `LENGTH ys' = LENGTH ys` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND,LENGTH_MAP,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM_APPEND,MEM_MAP,MEM]
    \\ METIS_TAC [])
  val th = MP th lemma
  val th = RW1 [GSYM STACK_LENGTH_LEMMA] th
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
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
     (`(r1 = Data (2w * n2w n + 1w)) /\ n < 2**61` by ALL_TAC THEN1
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
    \\ `0x10000w * n2w (LENGTH xs) + 0x10w * n2w (n) &&
          0xFFFFw = 0x10w * n2w (n):word64` by ALL_TAC THEN1
     (MATCH_MP_TAC get_tag_blast \\ FULL_SIMP_TAC std_ss [word_mul_n2w,WORD_LO]
      \\ `(16 * n < 18446744073709551616)` by DECIDE_TAC
      \\ ASM_SIMP_TAC (srw_ss()) [w2n_n2w] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg0 := ((0x10w * n2w n) >>> 2) |>`
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
    \\ Q.PAT_ASSUM `n < 4096` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
      \\ `n < 2305843009213693952` by DECIDE_TAC
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
  val _ = add_compiled [th];
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
     (`(r1 = Data (2w * n2w n + 1w)) /\ n < 2**61` by ALL_TAC THEN1
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
    \\ `LENGTH l < 2 ** 32` by ALL_TAC THEN1 (FULL_SIMP_TAC std_ss [])
    \\ `LENGTH xs < 2 ** 32` by ALL_TAC THEN1
      (IMP_RES_TAC EVERY2_IMP_LENGTH \\ FULL_SIMP_TAC std_ss [])
    \\ `((0x10000w * n2w (LENGTH xs) + 0x10w * n2w n) >>> 16):word64 =
        n2w (LENGTH xs)` by ALL_TAC THEN1
      (MATCH_MP_TAC get_length_blast
       \\ `(16 * n) < 18446744073709551616` by DECIDE_TAC
       \\ `LENGTH xs < 18446744073709551616` by DECIDE_TAC
       \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,WORD_LO]
       \\ DECIDE_TAC)
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
    \\ STRIP_TAC THEN1
     (Q.PAT_ASSUM `abs_ml_inv xx yy zz tt` MP_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `LENGTH l < 2305843009213693952` by DECIDE_TAC
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
  val _ = add_compiled [th];
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
    \\ `r2 = Data (2w * n2w (Num i))` by ALL_TAC THEN1
     (`small_int i /\ ~(i < 0)` by ALL_TAC THEN1
        (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def,
            bc_value_inv_def])
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
    \\ FULL_SIMP_TAC std_ss [ADD1,AC ADD_COMM ADD_ASSOC]
    \\ STRIP_TAC THEN1
      (FULL_SIMP_TAC (srw_ss()) [w2w_def,w2n_n2w,word_mul_n2w,MULT_ASSOC])
    \\ Q.PAT_ASSUM `xxx (fun2set (vals.memory,vals.memory_domain))` MP_TAC
    \\ NTAC 2 (FULL_SIMP_TAC (srw_ss()++star_ss) [one_list_APPEND,one_list_def]
      \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,SEP_CLAUSES,APPEND,GSYM APPEND_ASSOC]
      \\ FULL_SIMP_TAC std_ss [word_add_n2w,word_mul_n2w,LEFT_ADD_DISTRIB]
      \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,LEFT_ADD_DISTRIB,heap_length_APPEND,
           AC WORD_ADD_ASSOC WORD_ADD_COMM,word_mul_n2w,AC MULT_COMM MULT_ASSOC,
           heap_length_def]))
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
  val _ = add_compiled [th];
  in th end;


(* sub1 *)

val isNumber_EXISTS = prove(
  ``!x. isNumber x <=> ?i. x = Number i``,
  Cases \\ SIMP_TAC (srw_ss()) [isNumber_def]);

val small_int_IMP = prove(
  ``small_int i /\ ~(i < 0) ==> (2 * Num i) < dimword (:63)``,
  SIMP_TAC (srw_ss()) [small_int_def] \\ intLib.COOPER_TAC);

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
            (getNumber ^x <> 0) /\ ~(getNumber ^x < 0) /\ isNumber ^x)``
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
      \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [getNumber_def]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_value_inv_def])
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,WORD_MUL_LSL,w2w_def,word_mul_n2w]
    \\ IMP_RES_TAC small_int_IMP
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
    \\ `(2 * Num (i - 1)) < 4611686018427387904` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def,word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ `i - 1 = & (Num (i - 1))` by
     (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ `Num (i - 1) < 2305843009213693952` by intLib.COOPER_TAC
    \\ `(2 * Num (i − 1)) < 9223372036854775808` by intLib.COOPER_TAC
    \\ ASM_SIMP_TAC std_ss [MULT_ASSOC]
    \\ METIS_TAC [swap_1_lemmas,abs_ml_inv_Num])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (small_int (getNumber ^x) /\
            (getNumber ^x <> 0) /\ isNumber ^x /\ ~(getNumber ^x < 0))``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

val sub1_1 = zHEAP_SUB1 ``1:num``;
val sub1_2 = zHEAP_SUB1 ``2:num``;
val sub1_3 = zHEAP_SUB1 ``3:num``;
val sub1_4 = zHEAP_SUB1 ``4:num``;


(* add1 *)

fun zHEAP_ADD1 n = let
  val th = if n = ``1:num`` then compose_specs ["add r0,4"] else
           if n = ``2:num`` then compose_specs ["add r1,4"] else
           if n = ``3:num`` then compose_specs ["add r2,4"] else
           if n = ``4:num`` then compose_specs ["add r3,4"] else fail()
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            small_int (getNumber ^x) /\
            small_int (getNumber ^x + 1) /\ ~(getNumber ^x < 0) /\ isNumber ^x)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       if ^n = 1 then Number (getNumber x1 + 1) else x1,
       if ^n = 2 then Number (getNumber x2 + 1) else x2,
       if ^n = 3 then Number (getNumber x3 + 1) else x3,
       if ^n = 4 then Number (getNumber x4 + 1) else x4,
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
    \\ IMP_RES_TAC small_int_IMP
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,MULT_ASSOC]
    \\ `n2w (4 * Num i) + 0x4w = n2w (4 * Num (i + 1)):word64` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [small_int_def]
      \\ ASM_SIMP_TAC std_ss [word_arith_lemma1] \\ AP_TERM_TAC
      \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with
         <| reg0 := (if ^n = 1 then vals.reg0 + 4w else vals.reg0) ;
            reg1 := (if ^n = 2 then vals.reg1 + 4w else vals.reg1) ;
            reg2 := (if ^n = 3 then vals.reg2 + 4w else vals.reg2) ;
            reg3 := (if ^n = 4 then vals.reg3 + 4w else vals.reg3) |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
      \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC])
    \\ SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
          `if ^n = 1 then Data (n2w (2 * Num (i+1))) else r1`,
          `if ^n = 2 then Data (n2w (2 * Num (i+1))) else r2`,
          `if ^n = 3 then Data (n2w (2 * Num (i+1))) else r3`,
          `if ^n = 4 then Data (n2w (2 * Num (i+1))) else r4`,
          `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,WORD_MUL_LSL,w2w_def,w2n_n2w]
    \\ `(2 * Num (i + 1)) < 4611686018427387904` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def,word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ `i + 1 = & (Num (i + 1))` by
     (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ `Num (i + 1) < 2305843009213693952` by intLib.COOPER_TAC
    \\ `(2 * Num (i + 1)) < 9223372036854775808` by intLib.COOPER_TAC
    \\ ASM_SIMP_TAC std_ss [MULT_ASSOC]
    \\ METIS_TAC [swap_1_lemmas,abs_ml_inv_Num])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (small_int (getNumber ^x) /\ small_int (getNumber ^x + 1) /\
            ~(getNumber ^x < 0) /\ isNumber ^x)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

val add1_1 = zHEAP_ADD1 ``1:num``;
val add1_2 = zHEAP_ADD1 ``2:num``;
val add1_3 = zHEAP_ADD1 ``3:num``;
val add1_4 = zHEAP_ADD1 ``4:num``;


(* DIV 2 *)

val n2w_lsr = prove(
  ``!m n. n < dimword (:'a) ==> ((n2w n) >>> m = n2w (n DIV 2 ** m) :'a word)``,
  FULL_SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w] \\ REPEAT STRIP_TAC
  \\ `(n DIV 2 ** m) < dimword (:'a)` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss [DIV_LT_X]
  \\ `0 < (2:num)**m` by FULL_SIMP_TAC std_ss [bitTheory.ZERO_LT_TWOEXP]
  \\ Cases_on `(2:num)**m` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES]
  \\ DECIDE_TAC);

val NumDIV = prove(
  ``~(i < 0) ==> (4 * Num i DIV 8 = Num (i / 2))``,
  Cases_on `i` \\ SRW_TAC [] []
  \\ STRIP_ASSUME_TAC (MATCH_MP DIVISION (DECIDE ``0<2:num``) |> Q.SPEC `n`)
  \\ Q.PAT_ASSUM `n = kkk` (fn th => SIMP_TAC std_ss [Once th])
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SRW_TAC [] [RIGHT_ADD_DISTRIB]
  \\ SIMP_TAC std_ss [GSYM MULT_ASSOC]
  \\ MATCH_MP_TAC (MP_CANON DIV_MULT)
  \\ DECIDE_TAC);

fun zHEAP_DIV2 n = let
  val th = if n = ``1:num`` then compose_specs ["shr r0,3","shl r0,2"] else
           if n = ``2:num`` then compose_specs ["shr r1,3","shl r1,2"] else
           if n = ``3:num`` then compose_specs ["shr r2,3","shl r2,2"] else
           if n = ``4:num`` then compose_specs ["shr r3,3","shl r3,2"] else fail()
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            small_int (getNumber ^x) /\ ~(getNumber ^x < 0) /\ isNumber ^x)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       if ^n = 1 then Number (getNumber x1 / 2) else x1,
       if ^n = 2 then Number (getNumber x2 / 2) else x2,
       if ^n = 3 then Number (getNumber x3 / 2) else x3,
       if ^n = 4 then Number (getNumber x4 / 2) else x4,
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
    \\ IMP_RES_TAC small_int_IMP
    \\ FULL_SIMP_TAC std_ss [w2n_n2w,MULT_ASSOC]
    \\ `(0x4w * n2w (4 * Num i) >>> 3 = n2w (4 * Num (i / 2)):word64) /\
        (n2w (4 * Num i) >>> 3 << 2 = n2w (4 * Num (i / 2)):word64)` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) []
      \\ `4 * Num i < 2 * 9223372036854775808` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ `4 * Num i < dimword (:64)` by FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC n2w_lsr \\ FULL_SIMP_TAC std_ss [word_mul_n2w,WORD_MUL_LSL]
      \\ AP_TERM_TAC \\ AP_TERM_TAC
      \\ MATCH_MP_TAC NumDIV \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with
         <| reg0 := (if ^n = 1 then vals.reg0 >>> 3 << 2 else vals.reg0) ;
            reg1 := (if ^n = 2 then vals.reg1 >>> 3 << 2 else vals.reg1) ;
            reg2 := (if ^n = 3 then vals.reg2 >>> 3 << 2 else vals.reg2) ;
            reg3 := (if ^n = 4 then vals.reg3 >>> 3 << 2 else vals.reg3) |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
      \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC])
    \\ SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
          `if ^n = 1 then Data (n2w (2 * Num (i/2))) else r1`,
          `if ^n = 2 then Data (n2w (2 * Num (i/2))) else r2`,
          `if ^n = 3 then Data (n2w (2 * Num (i/2))) else r3`,
          `if ^n = 4 then Data (n2w (2 * Num (i/2))) else r4`,
          `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,WORD_MUL_LSL,w2w_def,w2n_n2w]
    \\ `(2 * Num (i / 2)) < 4611686018427387904` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def,word_mul_n2w]
    \\ `Num (i / 2) < 2305843009213693952` by intLib.COOPER_TAC
    \\ `(2 * Num (i / 2)) < 9223372036854775808` by intLib.COOPER_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ `i / 2 = & (Num (i / 2))` by
     (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
     \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
    \\ METIS_TAC [swap_1_lemmas,abs_ml_inv_Num])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (small_int (getNumber ^x) /\
            ~(getNumber ^x < 0) /\ isNumber ^x)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

val div2_1 = zHEAP_DIV2 ``1:num``;
val div2_2 = zHEAP_DIV2 ``2:num``;
val div2_3 = zHEAP_DIV2 ``3:num``;
val div2_4 = zHEAP_DIV2 ``4:num``;


(* is EVEN *)

val EVEN_SPLIT = prove(
  ``!n. n = 2 * (n DIV 2) + (if EVEN n then 0 else 1)``,
  ONCE_REWRITE_TAC [MULT_COMM] \\ REPEAT STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0<2:num``)))
  \\ Q.PAT_ASSUM `n = kkk` (fn th => SIMP_TAC std_ss [Once th])
  \\ SIMP_TAC std_ss [arithmeticTheory.EVEN_MOD2]
  \\ DECIDE_TAC);

val EVEN_LEMMA = prove(
  ``(0x4w && n2w (4 * n) = 0x0w:word64) <=> EVEN n``,
  `n = 2 * (n DIV 2) + (if EVEN n then 0 else 1)` by FULL_SIMP_TAC std_ss [EVEN_SPLIT]
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
  \\ Cases_on `EVEN n` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,GSYM word_add_n2w]
  \\ blastLib.BBLAST_TAC);

fun zHEAP_IS_EVEN n = let
  val th = if n = ``1:num`` then spec "test r0,4" else
           if n = ``2:num`` then spec "test r1,4" else
           if n = ``3:num`` then spec "test r2,4" else
           if n = ``4:num`` then spec "test r3,4" else fail()
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
            ~(getNumber ^x < 0) /\ small_int (getNumber ^x) /\ isNumber ^x)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (EVEN (Num (getNumber ^x)))) *
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
    \\ `EVEN (Num (getNumber ^x)) <=> (^reg && 4w = 0x0w)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [isNumber_EXISTS,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def]
      \\ FULL_SIMP_TAC std_ss [getNumber_def,x64_addr_def]
      \\ `(2 * (Num i)) < dimword (:63)` by IMP_RES_TAC small_int_IMP
      \\ REVERSE (Cases_on `i`) \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword,w2w_def]
      \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC] \\ METIS_TAC [EVEN_LEMMA])
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (~(getNumber ^x < 0) /\ small_int (getNumber ^x) /\ isNumber ^x)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

val zHEAP_IS_EVEN_1 = zHEAP_IS_EVEN ``1:num``;
val zHEAP_IS_EVEN_2 = zHEAP_IS_EVEN ``2:num``;
val zHEAP_IS_EVEN_3 = zHEAP_IS_EVEN ``3:num``;
val zHEAP_IS_EVEN_4 = zHEAP_IS_EVEN ``4:num``;


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
            ~(getNumber ^x < 0) /\ isNumber ^x)``
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
      \\ REVERSE (Cases_on `i`) \\ FULL_SIMP_TAC (srw_ss()) []
      THEN1 (FULL_SIMP_TAC (srw_ss()) [small_int_def,getNumber_def])
      \\ `(2 * n) < dimword (:63)` by IMP_RES_TAC small_int_IMP
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
      \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC]
      \\ `(4 * n) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (~(getNumber ^x < 0) /\ isNumber ^x)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
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
            ~(getNumber ^x < 0) /\ isNumber ^x)``
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
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,
           w2n_n2w,getNumber_def]
      \\ `(2 * Num i) < dimword (:63)` by IMP_RES_TAC small_int_IMP
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
      cond (~(getNumber ^x < 0) /\ isNumber ^x)``
  val lemma= prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

val _ = map (zHEAP_IS_CONST ``1:num``) (map ord (explode "let(struct)sig[end];"))
val _ = map (zHEAP_IS_CONST ``1:num``) (tl (up_to 60));
val _ = map (zHEAP_IS_CONST ``2:num``) (tl (up_to 10));
val _ = map (zHEAP_IS_CONST ``3:num``) (tl (up_to 10));
val _ = map (zHEAP_IS_CONST ``4:num``) (tl (up_to 10));

val _ = zHEAP_IS_CONST ``1:num`` 92;

val zHEAP_1EQ0 = zHEAP_IS_CONST ``1:num`` 0;
val zHEAP_2EQ0 = zHEAP_IS_CONST ``2:num`` 0;
val zHEAP_3EQ0 = zHEAP_IS_CONST ``3:num`` 0;
val zHEAP_4EQ0 = zHEAP_IS_CONST ``4:num`` 0;


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
       (FULL_SIMP_TAC std_ss [x64_addr_def]
        \\ REVERSE (Cases_on `i < 0:int`) \\ REVERSE (Cases_on `j < 0:int`)
        \\ FULL_SIMP_TAC std_ss [] THEN1
         (`(2 * Num i) < dimword (:63)` by IMP_RES_TAC small_int_IMP
          \\ `(2 * Num j) < dimword (:63)` by IMP_RES_TAC small_int_IMP
          \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
          \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
          \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC]
          \\ `(4 * Num i) < 18446744073709551616` by DECIDE_TAC
          \\ `(4 * Num j) < 18446744073709551616` by DECIDE_TAC
          \\ FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
        \\ `!k. ~(&k < 0:int)` by intLib.COOPER_TAC
        \\ FULL_SIMP_TAC std_ss [EVAL ``0<0:int``]
        THEN1
         (Cases_on `j` \\ FULL_SIMP_TAC (srw_ss()) [small_int_def]
          \\ FULL_SIMP_TAC std_ss [reintro_word_sub63]
          \\ `i <> -&n` by intLib.COOPER_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `Num i < 9223372036854775808` by intLib.COOPER_TAC
          \\ `n < 9223372036854775808` by DECIDE_TAC
          \\ `n2w (Num i) <+ 2305843009213693952w:63 word` by ALL_TAC
          THEN1 (FULL_SIMP_TAC (srw_ss()) [WORD_LO] \\ intLib.COOPER_TAC)
          \\ `n2w n <+ 2305843009213693952w:63 word` by ALL_TAC
          THEN1 (FULL_SIMP_TAC (srw_ss()) [WORD_LO] \\ intLib.COOPER_TAC)
          \\ `n2w n <> 0w : 63 word` by ALL_TAC
          THEN1 (FULL_SIMP_TAC (srw_ss()) [n2w_11] \\ intLib.COOPER_TAC)
          \\ NTAC 3 (POP_ASSUM MP_TAC)
          \\ Q.SPEC_TAC (`n2w (Num i) : 63 word`,`w1`)
          \\ Q.SPEC_TAC (`n2w n : 63 word`,`w2`)
          \\ blastLib.BBLAST_TAC)
        THEN1
         (Cases_on `i` \\ FULL_SIMP_TAC (srw_ss()) [small_int_def]
          \\ FULL_SIMP_TAC std_ss [reintro_word_sub63]
          \\ `j <> -&n` by intLib.COOPER_TAC \\ FULL_SIMP_TAC std_ss []
          \\ `Num j < 9223372036854775808` by intLib.COOPER_TAC
          \\ `n < 9223372036854775808` by DECIDE_TAC
          \\ `n2w (Num j) <+ 2305843009213693952w:63 word` by ALL_TAC
          THEN1 (FULL_SIMP_TAC (srw_ss()) [WORD_LO] \\ intLib.COOPER_TAC)
          \\ `n2w n <+ 2305843009213693952w:63 word` by ALL_TAC
          THEN1 (FULL_SIMP_TAC (srw_ss()) [WORD_LO] \\ intLib.COOPER_TAC)
          \\ `n2w n <> 0w : 63 word` by ALL_TAC
          THEN1 (FULL_SIMP_TAC (srw_ss()) [n2w_11] \\ intLib.COOPER_TAC)
          \\ NTAC 3 (POP_ASSUM MP_TAC)
          \\ Q.SPEC_TAC (`n2w (Num i) : 63 word`,`w1`)
          \\ Q.SPEC_TAC (`n2w n : 63 word`,`w2`)
          \\ blastLib.BBLAST_TAC)
        \\ FULL_SIMP_TAC (srw_ss()) [small_int_def]
        \\ Cases_on `i` \\ FULL_SIMP_TAC (srw_ss()) [small_int_def]
        \\ Cases_on `j` \\ FULL_SIMP_TAC (srw_ss()) [small_int_def]
        \\ FULL_SIMP_TAC std_ss [reintro_word_sub63]
        \\ `n < 9223372036854775808` by DECIDE_TAC
        \\ `n' < 9223372036854775808` by DECIDE_TAC
        \\ `(n = n') <=> (n2w n = (n2w n') : 63 word)` by ALL_TAC
        THEN1 (FULL_SIMP_TAC (srw_ss()) [n2w_11] \\ intLib.COOPER_TAC)
        \\ FULL_SIMP_TAC std_ss []
        \\ `n2w n <+ 2305843009213693952w:63 word` by ALL_TAC
        THEN1 (FULL_SIMP_TAC (srw_ss()) [WORD_LO] \\ intLib.COOPER_TAC)
        \\ `n2w n' <+ 2305843009213693952w:63 word` by ALL_TAC
        THEN1 (FULL_SIMP_TAC (srw_ss()) [WORD_LO] \\ intLib.COOPER_TAC)
        \\ `n2w n <> 0w : 63 word` by ALL_TAC
        THEN1 (FULL_SIMP_TAC (srw_ss()) [n2w_11] \\ intLib.COOPER_TAC)
        \\ `n2w n' <> 0w : 63 word` by ALL_TAC
        THEN1 (FULL_SIMP_TAC (srw_ss()) [n2w_11] \\ intLib.COOPER_TAC)
        \\ NTAC 4 (POP_ASSUM MP_TAC)
        \\ Q.SPEC_TAC (`n2w n' : 63 word`,`w1`)
        \\ Q.SPEC_TAC (`n2w n : 63 word`,`w2`)
        \\ blastLib.BBLAST_TAC)
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
  val _ = add_compiled [th];
  in th end;

fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x)
val regs = (up_to 4) |> map (fn n => n+1)
val reg_combs = map (fn n => map (fn m => (n,m)) (n_times n tl (tl (up_to 5)))) regs
  |> flatten

val zHEAP_CMP_SMALL_INT_12 = zHEAP_CMP_SMALL_INT (1,2)
val _ = map zHEAP_CMP_SMALL_INT reg_combs;


(* less-than for smallints *)

val zHEAP_SMALL_INT_LESS = let
  val th = spec ("cmp r1,r0")
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_ZF`` th
  val pc = get_pc th
  val x = ``x2:bc_value``
  val y = ``x1:bc_value``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            ~(getNumber ^x < 0) /\ ~(getNumber ^y < 0) /\
            small_int (getNumber ^x) /\ small_int (getNumber ^y) /\
            isNumber ^x /\ isNumber ^y)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_ZF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_CF (SOME (getNumber x2 < getNumber x1)) *
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
    \\ REVERSE (`(getNumber x2 < getNumber x1) <=> (vals.reg1 <+ vals.reg0)` by ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [isNumber_EXISTS,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
         bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
    \\ Q.MATCH_ASSUM_RENAME_TAC `xxx = Number j` []
    \\ Cases_on `small_int i` \\ Cases_on `small_int j`
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC small_int_IMP
    \\ FULL_SIMP_TAC std_ss [x64_addr_def]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
    \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
    \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC,WORD_LO]
    \\ `(4 * Num i) < 18446744073709551616` by DECIDE_TAC
    \\ `(4 * Num j) < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [small_int_def]
    \\ intLib.COOPER_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond ((small_int (getNumber x1) /\ small_int (getNumber x2)) /\
            ~(getNumber ^x < 0) /\ ~(getNumber ^y < 0) /\
            isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM] \\ Cases_on `small_int (getNumber ^x)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;


(* compare small_int with const *)

fun zHEAP_LESS_SMALL_INT_CONST (i,c) = let
  val n = i |> numSyntax.term_of_int
  val m = c |> numSyntax.term_of_int
  val rn = i |> (fn n => "r" ^ int_to_string (n - 1))
  val rm = c |> (fn n => int_to_string (n * 4))
  val th = spec ("cmp " ^ rn ^ "," ^ rm)
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_ZF`` th
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val pre = ``~(getNumber ^x < 0) /\ small_int (getNumber ^x) /\ isNumber ^x``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      zS1 Z_CF (SOME (getNumber ^x < & (^m))) * ~zS1 Z_OF *
      ~zS1 Z_SF * ~zS1 Z_ZF * ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val regn = ``if ^n = 1 then vals.reg0 else
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
    \\ `(getNumber ^x < & ^m) <=> (^regn <+ n2w (4 * ^m))` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [isNumber_EXISTS,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def,getNumber_def]
      \\ FULL_SIMP_TAC std_ss [x64_addr_def,word_mul_n2w,w2w_def,w2n_n2w]
      \\ Q.MATCH_ASSUM_RENAME_TAC `xxx = Number j` []
      \\ `(2 * Num j) < dimword (:63)` by ALL_TAC
      THEN1 (FULL_SIMP_TAC (srw_ss()) [small_int_def] \\ intLib.COOPER_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,n2w_11,ZERO_LT_dimword]
      \\ FULL_SIMP_TAC (srw_ss()) [MULT_ASSOC]
      \\ `(4 * Num j) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO]
      \\ FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM] \\ Cases_on `small_int (getNumber ^x)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

fun zHEAP_LESS_CONST c = let
  val _ = zHEAP_LESS_SMALL_INT_CONST (1,c)
  val _ = zHEAP_LESS_SMALL_INT_CONST (2,c)
  val _ = zHEAP_LESS_SMALL_INT_CONST (3,c)
  val _ = zHEAP_LESS_SMALL_INT_CONST (4,c)
  in () end

fun pow2 0 = 1
  | pow2 n = 2 * pow2 (n - 1)

val _ = map zHEAP_LESS_CONST [pow2 1, pow2 2, pow2 3, pow2 4,
                              pow2 8, pow2 12, pow2 15, pow2 28]


(* shift small_int *)

fun zHEAP_SHIFT_SMALL_INT (i,c) = let
  val n = i |> numSyntax.term_of_int
  val m = c |> numSyntax.term_of_int
  val rn = i |> (fn n => "r" ^ int_to_string (n - 1))
  val rm = c |> (fn n => int_to_string n)
  val th = compose_specs ["shl " ^ rn ^ "," ^ rm]
  val pc = get_pc th
  val x = ``if ^n = 1:num then x1 else
            if ^n = 2 then x2 else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB:bc_value``
  val res = ``getNumber ^x * & (2 ** ^m)``
  val pre = ``~(getNumber ^x < 0) /\
              small_int (getNumber ^x) /\ small_int ^res /\ isNumber ^x``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       if ^n = 1 then Number ^res else x1,
       if ^n = 2 then Number ^res else x2,
       if ^n = 3 then Number ^res else x3,
       if ^n = 4 then Number ^res else x4,
       refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
  val regn = ``if ^n = 1 then vals.reg0 else
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
    \\ Q.LIST_EXISTS_TAC [`vals with
          <| reg0 := if ^n = 1 then vals.reg0 << ^m else vals.reg0 ;
             reg1 := if ^n = 2 then vals.reg1 << ^m else vals.reg1 ;
             reg2 := if ^n = 3 then vals.reg2 << ^m else vals.reg2 ;
             reg3 := if ^n = 4 then vals.reg3 << ^m else vals.reg3 |> `]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Cases_on `if ^n = 1 then x1 else
                 if ^n = 2 then x2 else
                 if ^n = 3 then x3 else
                 if ^n = 4 then x4 else ARB`
    \\ FULL_SIMP_TAC std_ss [getNumber_def,isNumber_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
          `if ^n = 1 then Data (0x2w * n2w (Num i) << ^m) else r1`,
          `if ^n = 2 then Data (0x2w * n2w (Num i) << ^m) else r2`,
          `if ^n = 3 then Data (0x2w * n2w (Num i) << ^m) else r3`,
          `if ^n = 4 then Data (0x2w * n2w (Num i) << ^m) else r4`,
          `roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def]
    \\ SIMP_TAC std_ss [PULL_EXISTS]
    \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [reachable_refs_SIMP]
    \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [roots_ok_def]
    THEN1 (FULL_SIMP_TAC (srw_ss()) [MEM] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [word_mul_n2w,WORD_MUL_LSL]
    THEN1 (FULL_SIMP_TAC std_ss [small_int_def]
           \\ SRW_TAC [] [] THEN1 `F` by intLib.COOPER_TAC
           \\ FULL_SIMP_TAC std_ss [word_mul_n2w,WORD_MUL_LSL]
           \\ AP_TERM_TAC \\ intLib.COOPER_TAC)
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,WORD_MUL_LSL]
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM] \\ Cases_on `small_int (getNumber ^x)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end;

fun zHEAP_SHIFT_BY_INT c = let
  val _ = zHEAP_SHIFT_SMALL_INT (1,c)
  val _ = zHEAP_SHIFT_SMALL_INT (2,c)
  val _ = zHEAP_SHIFT_SMALL_INT (3,c)
  val _ = zHEAP_SHIFT_SMALL_INT (4,c)
  in () end

val _ = map zHEAP_SHIFT_BY_INT [1,2,3]


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
    \\ `(2 * n + 1) < 9223372036854775808` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_MUL_LSL,word_mul_n2w,n2w_11]
    \\ REWRITE_TAC [GSYM (EVAL ``(2:num) * 2**63``)]
    \\ `(0:num) < 2 /\ (0:num) < 2**63` by EVAL_TAC
    \\ IMP_RES_TAC MOD_COMMON_FACTOR
    \\ FULL_SIMP_TAC std_ss [])
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
  val _ = add_compiled [th];
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
  val _ = add_compiled [th];
  in th end;

val _ = map zHEAP_SWAP reg_combs;

val zHEAP_SWAP_12 = zHEAP_SWAP (1,2)


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
  val lemma = prove(goal,cheat)
(*
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
*)
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
  val _ = add_compiled [th];
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
  val lemma = prove(goal,cheat) (*
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
      \\ EVAL_TAC)) *)
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
  val _ = add_compiled [th];
  in th end


(* isSmall *)

val isSmall_def = Define `
  (isSmall (Number i) = small_int i) /\
  (isSmall (Block tag l) = (l = [])) /\
  (isSmall _ = F)`;

fun zHEAP_isSmall i = let
  val rn = "r" ^ ((i - 1) |> int_to_string)
  val n = i |> numSyntax.term_of_int
  val th = spec ("test "^rn^",1")
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val th = th |> Q.INST [`rip`|->`p`]
  val pc = get_pc th
  val x = ``if ^n = 1 then x1 else
            if ^n = 2 then (x2:bc_value) else
            if ^n = 3 then x3 else
            if ^n = 4 then x4 else ARB``
  val pre = ``canCompare ^x``
  val target = ``zPC p * ~zS * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,
       refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (isSmall ^x)) *
      ~zS1 Z_PF * ^pc`
  val reg = ``if ^n = 1 then vals.reg0 else
              if ^n = 2 then vals.reg1 else
              if ^n = 3 then vals.reg2 else
              if ^n = 4 then vals.reg3 else ARB``
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
    \\ `isSmall ^x = (0x1w && ^reg = 0x0w)` by ALL_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `^x` \\ FULL_SIMP_TAC (srw_ss()) [canCompare_def,isSmall_def]
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
      cond (^pre) * ~zS``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th
  val _ = add_compiled [th];
  in th end

val _ = map zHEAP_isSmall [1,2,3,4];


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
  \\ FULL_SIMP_TAC std_ss [integerTheory.INT_EQ_CALCULATE,ADD1,EVAL ``0<0:int``]
  \\ REPEAT STRIP_TAC
  \\ `(&(k + 1) - 1 = & k) /\ 0 <= &k /\ k <= LENGTH l /\
      small_int (&k) /\ k < LENGTH l /\ ~(&(k + 1) < 0:int) /\
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
  \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss [LENGTH]
  THEN1 (ASM_SIMP_TAC (srw_ss()) [small_int_def])
  \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [BlockRep_def,x64_heap_APPEND,
       x64_el_def,x64_payload_def,LET_DEF,cond_STAR,x64_heap_def]
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [small_int_def]
  \\ STRIP_TAC THEN1 intLib.COOPER_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [small_int_def]
  \\ DECIDE_TAC);

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
  val _ = add_compiled [th];
  in th end;


(* explode single Block in REVERSE *)

val (res,push_els2_loop_def,push_els2_loop_pre_def) = x64_compile `
  push_els2_loop (x1,x2,x3,x4:bc_value,stack) =
    if getNumber x2 = 0 then (x1,x2,x3,x4,stack) else
      let x2 = Number (getNumber x2 - 1) in
      let x1 = x3 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in
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

val TAKE_SUC = prove(
  ``!k l.
      k + 1 <= LENGTH l ==>
      (TAKE (k + 1) l = TAKE k l ++ [EL k l])``,
  Induct THEN1 (Cases_on `l` \\ EVAL_TAC) \\ Cases_on `l`
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [ADD1])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,rich_listTheory.TAKE,APPEND,CONS_11,EL,HD,TL]);

val push_els2_loop_thm = prove(
  ``!k stack x1.
      k <= LENGTH l /\ small_int (& k) ==>
      ?x1i. push_els2_loop_pre (x1,Number (& k),Block tag l,x4,stack) /\
           (push_els2_loop (x1,Number (& k),Block tag l,x4,stack) =
             (x1i,Number 0, Block tag l,x4,TAKE k l ++ stack))``,
  Induct \\ SIMP_TAC std_ss [TAKE_0,MAP,FLAT,APPEND]
  \\ ONCE_REWRITE_TAC [push_els2_loop_def,push_els2_loop_pre_def]
  \\ FULL_SIMP_TAC std_ss [getNumber_def,isNumber_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [integerTheory.INT_EQ_CALCULATE,ADD1,EVAL ``0<0:int``]
  \\ REPEAT STRIP_TAC
  \\ `(&(k + 1) - 1 = & k) /\ 0 <= &k /\ k <= LENGTH l /\
      small_int (&k) /\ k < LENGTH l /\ ~(&(k + 1) < 0:int) /\
      &k < &LENGTH l /\ (Num (& k) = k)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss [getContent_def,isBlock_def]
  \\ IMP_RES_TAC TAKE_SUC
  \\ FULL_SIMP_TAC std_ss [MAP_APPEND,FLAT_APPEND,MAP,FLAT,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val push_els2_thm = prove(
  ``isBlock x1 /\ small_int (& (LENGTH (getContent x1))) ==>
    push_els2_pre (x1,x4,stack) /\
    (push_els2 (x1,x4,stack) =
       (Number 0,Number 0,x1,x4,getContent x1 ++ stack))``,
  Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isBlock_def,getContent_def]
  \\ FULL_SIMP_TAC std_ss [push_els2_def,push_els2_pre_def,LET_DEF,
       isBlock_def,getContent_def]
  \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC (GEN_ALL push_els2_loop_thm)
  \\ SEP_I_TAC "push_els2_loop"
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [TAKE_LENGTH_ID]);

val zHEAP_EXPLODE_BLOCK_SIMPLE = let
  val tm = push_els2_thm |> concl |> dest_imp |> fst
  val th = DISCH tm push_els2_cert
           |> SIMP_RULE std_ss [push_els2_thm,LET_DEF,SEP_CLAUSES]
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
  val _ = add_compiled [th];
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
  \\ `k < LENGTH l` by DECIDE_TAC
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
  \\ FULL_SIMP_TAC std_ss [integerTheory.INT_EQ_CALCULATE,ADD1,EVAL ``0<0:int``]
  \\ REPEAT STRIP_TAC
  \\ `(&(k + 1) - 1 = & k) /\ 0 <= &k /\ k <= LENGTH l1 /\
      small_int (&k) /\ k < LENGTH l1 /\ ~(&(k + 1) < 0:int) /\
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
  val _ = add_compiled [th];
  in th end;


(* RefPtr equality *)

val RefPtrEq_def = Define `
  RefPtrEq x (y:bc_value) = (x = y)`;

val heap_lookup_IMP_heap_length = prove(
  ``(heap_lookup n heap = SOME x) ==>
    n <= heap_length heap``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def,heap_length_APPEND]
  \\ DECIDE_TAC);

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
  val _ = add_compiled [th];
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
    \\ IMP_RES_TAC Block_size_small_int \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_PUSH2,th,zHEAP_POP2,zHEAP_POP1]
  val th = th |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
  val _ = add_compiled [th];
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
    \\ IMP_RES_TAC Block_size_small_int \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [])
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_PUSH2,th,zHEAP_POP2,zHEAP_POP1]
  val th = th |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
  val _ = add_compiled [th];
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
  val _ = add_compiled [th];
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


(* small_int LESS *)

val (small_int_spec,small_lt_def,small_lt_pre_def) = x64_compile `
  small_lt (x1:bc_value,x2) =
    if getNumber x2 < getNumber x1 then
      let x1 = bool_to_val T in (x1,x2)
    else
      let x1 = bool_to_val F in (x1,x2)`

val small_lt_if = prove(
  ``small_lt (x1:bc_value,x2) =
    (bool_to_val (getNumber x2 < getNumber x1),x2)``,
  SRW_TAC [] [small_lt_def])

val small_lt_pre = prove(
  ``small_lt_pre (x1:bc_value,x2)``,
  cheat); (* bignum *)

val zHEAP_SMALL_INT = small_int_spec
  |> SIMP_RULE std_ss [LET_DEF,small_lt_if,small_lt_pre,SEP_CLAUSES]

val lemma = blastLib.BBLAST_PROVE
  ``w < v <=> w + 9223372036854775808w <+ v + 9223372036854775808w:word64``

(* more general

  ``!v w:'a word.
      v < w <=>
      v + n2w (dimword (:'a) DIV 2) <+ w + n2w (dimword (:'a) DIV 2)``,
  Cases \\ Cases
  \\ ASM_SIMP_TAC std_ss [WORD_LO,WORD_LT,word_add_n2w,w2n_n2w]
  \\ SIMP_TAC std_ss [word_msb_n2w,bitTheory.BIT_def,bitTheory.BITS_THM2,
       DECIDE ``SUC (n - 1) = 1``] ...

*)

val (x64_signed_less_res,x64_signed_less_def) = x64_decompile "x64_signed_less" `
      mov r15,9223372036854775808
      add r0,r15
      mov r14,r1
      add r14,r15
      cmp r14,r0
      jb L1
      mov r0,2
      jmp L2
  L1: mov r0,6
  L2:`

val zHEAP_SMALL_INT = let
  val th = x64_signed_less_res
  val pc = get_pc th
  val (th,goal) = SPEC_WEAKEN_RULE th ``(~zS * ^pc * zHEAP
        (cs,bool_to_val (getNumber x2 < getNumber x1),x2,x3,x4,refs,stack,s,NONE))``
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) *
       cond (isNumber x1 /\ isNumber x2))``
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val th = RW [fetch "-" "x64_signed_less_x64_def"] th
  in th end;

(*
[
  ``x64_signed_less (3w,4w)``
  |> (SIMP_CONV std_ss [x64_signed_less_def] THENC EVAL),
  ``x64_signed_less (4w,4w)``
  |> (SIMP_CONV std_ss [x64_signed_less_def] THENC EVAL),
  ``x64_signed_less (5w,4w)``
  |> (SIMP_CONV std_ss [x64_signed_less_def] THENC EVAL)
]
*)


(* prove that GC is no-op *)

val _ = add_compiled [x64_full_gc_res];

val (x64_gc_op_res, x64_gc_op_def, x64_gc_op_pre_def) = x64_compile `
  x64_gc_op (r0:word64,r1:word64,r2:word64,r3:word64,r9:word64,ss:word64 list,dm,m) =
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
    let r0 = 0w:word64 in
    let r1 = r0 in
    let r2 = r0 in
    let r3 = r0 in
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

val reachable_refs_Number = prove(
  ``reachable_refs (Number 0::stack) refs n =
    reachable_refs stack refs n``,
  SIMP_TAC std_ss [reachable_refs_def,MEM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ NTAC 2 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]
  \\ METIS_TAC []);

val push_num_lemma = prove(
  ``abs_ml_inv (Number 0::stack) refs (Data 0x0w::roots,x,a,k) l <=>
    abs_ml_inv stack refs (roots,x,a,k) l``,
  FULL_SIMP_TAC (srw_ss()) [abs_ml_inv_def,roots_ok_def,MEM,reachable_refs_Number,
    bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def,EVAL ``small_int 0``]);

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
  val th = RW1 [STACK_LENGTH_LEMMA] th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val n = ``Number 0``
  val th = th |> Q.SPEC `zHEAP (cs,^n,^n,^n,^n,refs,stack,s,^inv) * ~zS * ^pc`
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
    \\ IMP_RES_TAC (pop_thm
      |> Q.INST [`xs`|->`[x1;x2;x3;x4]`,`rs`|->`[r1;r2;r3;r4]`]
      |> SIMP_RULE std_ss [LENGTH,APPEND])
    \\ Q.PAT_ASSUM `abs_ml_inv (ss::sss) refs bla cs.heap_limit` (K ALL_TAC)
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
    THEN1 (FULL_SIMP_TAC std_ss [heap_vars_ok_def]
           \\ STRIP_TAC THEN1 DECIDE_TAC
           \\ STRIP_TAC THEN1 DECIDE_TAC
           \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
           \\ IMP_RES_TAC EVERY2_IMP_LENGTH
           \\ Q.PAT_ASSUM `8 * LENGTH vals.stack < nn` MP_TAC
           \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
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
          <| reg0 := 0w;
             reg1 := 0w;
             reg2 := 0w;
             reg3 := 0w;
             reg6 := vs.other_heap + n2w (8 * heap_length heap2) - 1w;
             reg7 := vs.other_heap + n2w (8 * cs.heap_limit) - 1w;
             reg8 := (vs.other_heap + n2w (8 * heap_length heap2));
             reg9 := vs.base_ptr;
             stack := (MAP (x64_addr vs.other_heap) roots2 ++
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
    \\ Q.LIST_EXISTS_TAC [`vs1`,`Data 0w`,`Data 0w`,`Data 0w`,`Data 0w`,`roots2`,
         `heap2 ++ heap_expand (cs.heap_limit - a2)`,`a2`,`cs.heap_limit - a2`]
    \\ `heap_vars_ok vs1` by ALL_TAC
    THEN1 (Q.UNABBREV_TAC `vs1` \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `vs1` \\ ASM_SIMP_TAC (srw_ss()) [x64_addr_def]
    \\ FULL_SIMP_TAC std_ss [APPEND,x64_heap_APPEND]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [x64_heap_heap_expand]
    \\ FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def]
    \\ SEP_R_TAC
    \\ `a2 <= cs.heap_limit` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [abs_ml_inv_def,heap_ok_def,heap_length_APPEND]
      \\ DECIDE_TAC)
    \\ IMP_RES_TAC (DECIDE ``n <= (m:num) ==> (n + (m - n) = m)``)
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [push_num_lemma])
  val th = MP th lemma
  val th = RW1 [GSYM STACK_LENGTH_LEMMA] th
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val th = th |> Q.INST [`ttt13`|->`r13`,`ttt14`|->`r14`]
  val th =
    SPEC_COMPOSE_RULE [zHEAP_PUSH1_GC, zHEAP_PUSH2_GC,
                       zHEAP_PUSH3_GC, zHEAP_PUSH4_GC, th,
                       zHEAP_POP4_GC, zHEAP_POP3_GC,
                       zHEAP_POP2_GC, zHEAP_POP1_GC]
  val th = th |> REWRITE_RULE [HD,TL,NOT_CONS_NIL,SEP_CLAUSES]
  in th end;


(* next char -- calls getchar *)

val heap_inv_IMP = prove(
  ``heap_inv (cs,x1,x2,x3,x4,refs,stack,s,SOME f) vals ==> ?sp. f (sp,vals)``,
  SIMP_TAC std_ss [heap_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val x64_getchar_thm = prog_x64_extraTheory.x64_getchar_thm;

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
         one_list_def,word_arith_lemma1,SEP_CLAUSES]
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
  val _ = add_compiled [th]
  in th end;

val zHEAP_READ_INPUT = let
  val th = compose_specs ["mov r0,r10","shl r0,2"]
  val pc = get_pc th
  val pre = ``s.input <> ""``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
    Number (& (ORD (HD s.input))),
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
    \\ Cases_on `s.input` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.EXISTS_TAC `vals with reg0 := (n2w (ORD h) << 2)`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC (std_ss++star_ss) [APPEND,GSYM APPEND_ASSOC])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
         `Data (2w * n2w ((ORD h)))`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ SIMP_TAC std_ss [x64_addr_def]
    \\ REVERSE STRIP_TAC THEN1
     (`ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
      \\ `2 * ORD h < 9223372036854775808` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,WORD_MUL_LSL,MULT_ASSOC,w2w_n2w,
          bitTheory.BITS_THM])
    \\ MATCH_MP_TAC abs_ml_inv_Num
    \\ Q.LIST_EXISTS_TAC [`x1`,`r1`] \\ ASM_SIMP_TAC std_ss []
    \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ SRW_TAC [] [] \\ DECIDE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
      AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val _ = add_compiled [th]
  in th end;

val zHEAP_READ_INPUT_DIGIT = let
  val th = compose_specs ["mov r0,r10","sub r0,48","shl r0,2"]
  val pc = get_pc th
  val pre = ``s.input <> "" /\ 48 <= ORD (HD s.input)``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
    Number (& (ORD (HD s.input) - 48)),
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
    \\ Cases_on `s.input` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.EXISTS_TAC `vals with reg0 := ((n2w (ORD h) - 48w) << 2)`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC (std_ss++star_ss) [APPEND,GSYM APPEND_ASSOC])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,
         `Data (2w * n2w ((ORD h) - 48))`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ SIMP_TAC std_ss [x64_addr_def]
    \\ REVERSE STRIP_TAC THEN1
     (`ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
      \\ `2 * (ORD h - 48) < 9223372036854775808` by DECIDE_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,WORD_MUL_LSL,MULT_ASSOC,w2w_n2w,
           bitTheory.BITS_THM,LEFT_SUB_DISTRIB]
      \\ `~(4 * ORD h < 192)` by DECIDE_TAC
      \\ IMP_RES_TAC (MATCH_MP (METIS_PROVE [] ``(x = if b then x1 else x2) ==>
                   (~b ==> (x2 = x))``) (word_arith_lemma2 |> SPEC_ALL
                      |> INST_TYPE [``:'a``|->``:64``]))
      \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ MATCH_MP_TAC abs_ml_inv_Num
    \\ Q.LIST_EXISTS_TAC [`x1`,`r1`] \\ ASM_SIMP_TAC std_ss []
    \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ SRW_TAC [] [] \\ DECIDE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
      AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val _ = add_compiled [th]
  in th end;

val zHEAP_CMP_INPUT = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "4981FA"
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_ZF`` th
  val lemma = prove(
    ``k < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (k)):word32)))) =
       n2w (k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(k) < 4294967296 /\ ~(2147483648 <= k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = th |> Q.INST [`imm32`|->`n2w k`] |> RW [lemma]
  val pc = get_pc th
  val pre = ``s.input <> "" /\ (k:num) < 2**31``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_ZF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_CF (SOME (ORD (HD s.input) < k)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(ORD (HD s.input) < k) <=> (vals.reg10 <+ n2w k)` by ALL_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def]
    \\ Cases_on `s.input` \\ FULL_SIMP_TAC std_ss [HD,MAP,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO]
    \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ `ORD h < 18446744073709551616 /\
        k < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th |> Q.GEN `k`
  fun store_cmp x =
    SPEC (numSyntax.term_of_int x) th |> SIMP_RULE (srw_ss()) [w2w_n2w]
    |> (fn th => (add_compiled [th]; th))
  val xs = map store_cmp (upto 1 255)
  in th end;

val zHEAP_INPUT_EQ = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "4981FA"
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_CF`` th
  val lemma = prove(
    ``k < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (k)):word32)))) =
       n2w (k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(k) < 4294967296 /\ ~(2147483648 <= k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = th |> Q.INST [`imm32`|->`n2w k`] |> RW [lemma]
  val pc = get_pc th
  val pre = ``s.input <> "" /\ (k:num) < 256``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_CF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_ZF (SOME (HD s.input = CHR k)) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC THEN1 DECIDE_TAC \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(HD s.input = CHR k) <=> (vals.reg10 = n2w k)` by ALL_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def]
    \\ Cases_on `s.input` \\ FULL_SIMP_TAC std_ss [HD,MAP,APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO]
    \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ `ORD h < 18446744073709551616 /\
        k < 18446744073709551616` by DECIDE_TAC
    \\ Cases_on `h`
    \\ FULL_SIMP_TAC std_ss [GSYM ORD_11,ORD_CHR])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma
  val th = SIMP_RULE std_ss [] th |> Q.GEN `k`
  fun store_cmp x =
    SPEC (numSyntax.term_of_int x) th |> SIMP_RULE (srw_ss()) [w2w_n2w]
    |> (fn th => (add_compiled [th]; th))
  val xs = map store_cmp (upto 0 255)
  in th end;

val zHEAP_EMPTY_INPUT = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "4981FA"
  val th = th |> Q.INST [`rip`|->`p`]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE false sts th
  val th = HIDE_POST_RULE ``zS1 Z_AF`` th
  val th = HIDE_POST_RULE ``zS1 Z_SF`` th
  val th = HIDE_POST_RULE ``zS1 Z_PF`` th
  val th = HIDE_POST_RULE ``zS1 Z_OF`` th
  val th = HIDE_POST_RULE ``zS1 Z_ZF`` th
  val lemma = prove(
    ``k < 2 ** 31 ==>
      ((n2w (SIGN_EXTEND 32 64 (w2n ((n2w (k)):word32)))) =
       n2w (k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(k) < 4294967296 /\ ~(2147483648 <= k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = th |> Q.INST [`imm32`|->`n2w k`] |> RW [lemma]
  val th = th |> Q.INST [`k`|->`256`]
  val pc = get_pc th
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T
                       |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
       x1,x2,x3,x4,refs,stack,s,NONE) * ~zS1 Z_AF *
      ~zS1 Z_ZF * ~zS1 Z_OF *
      ~zS1 Z_SF * zS1 Z_CF (SOME (s.input <> "")) *
      ~zS1 Z_PF * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`vals`]
    \\ `(s.input <> "") <=> (vals.reg10 <+ 256w)` by ALL_TAC
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC (srw_ss()) [zVALS_def,AC STAR_COMM STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def,abs_ml_inv_def,APPEND,
           bc_stack_ref_inv_def,EVERY2_def,bc_value_inv_def]
    \\ Cases_on `s.input` \\ FULL_SIMP_TAC std_ss [HD,MAP,APPEND]
    THEN1 EVAL_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_LO]
    \\ `ORD h < 256` by FULL_SIMP_TAC std_ss [ORD_BOUND]
    \\ `ORD h < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
         AC CONJ_ASSOC CONJ_COMM])
  val th = MP th lemma |> SIMP_RULE (srw_ss()) [w2w_n2w]
  val _ = add_compiled [th]
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

fun install_print_char c = let
  val th = zHEAP_PUT_CHAR
    |> INST [``c:word8``|->``n2w (^(numSyntax.term_of_int c)):word8``]
  in add_compiled [SIMP_RULE (srw_ss()) [] th] end

val _ = map install_print_char (upto 1 255);

val zHEAP_COND_PUT_CHAR = let
  val th1 = zHEAP_TEST_PRINTING_ON
  val ((th2,_,_),x) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "je 52")
  fun the (SOME x) = x | the _ = fail()
  val (th2a,_,_) = the x
  val th3 = zHEAP_PUT_CHAR
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val f = HIDE_STATUS_RULE true sts
  val g = RW [SPEC_MOVE_COND] o SIMP_RULE (std_ss++sep_cond_ss) [precond_def]
  val thA = SPEC_COMPOSE_RULE [SPEC_COMPOSE_RULE [th1,th2a] |> f, th3] |> g
  val thB = SPEC_COMPOSE_RULE [th1,th2] |> f |> g
  val pc = get_pc (UNDISCH_ALL thA)
  val c = thA |> concl |> rand |> rator |> rand
  val thB = MATCH_MP SPEC_SUBSET_CODE (thB |> UNDISCH) |> SPEC c
              |> SIMP_RULE (srw_ss()) [INSERT_SUBSET,EMPTY_SUBSET] |> DISCH_ALL
  val lemma = prove(
    ``(b ==> SPEC m p c q1) /\
      (~b ==> SPEC m p c q2) ==>
      SPEC m p c (if b then q1 else q2)``,
    Cases_on `b` \\ FULL_SIMP_TAC std_ss []);
  val th = MATCH_MP lemma (CONJ thB thA)
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zHEAP
          (cs,x1,x2,x3,x4,refs,stack,
           s with output := if s.local.printing_on = 0x0w then s.output else
             STRCAT s.output (STRING (CHR (w2n (c:word8))) ""),
           NONE) * ¬zS * ^pc``
  val lemma = prove(goal,
    SRW_TAC [] [SEP_IMP_REFL]
    \\ `(s with output := s.output) = s` by ALL_TAC THEN1
      (Cases_on `s` \\ SRW_TAC [] (TypeBase.updates_of ``:zheap_state``))
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL])
  val th = MP th lemma
  in th end;


(* put char from reg *)

val putchar_lemma = let
  val load_r7 = compose_specs ["mov r7,r0","shr r7,2"]
  val ((load_r0,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r0,[r9+24]")
  val th1 = SPEC_COMPOSE_RULE [x64_push_r0, x64_push_r1, x64_push_r2,
    x64_push_r3, x64_push_r6, x64_push_r7, x64_push_r8, x64_push_r9,
    x64_push_r10, x64_push_r11, load_r7, load_r0, x64_call_r0]
  val th1 = th1 |> DISCH ``r0 >>> 2 = w2w (c:word8):word64``
                |> SIMP_RULE std_ss [] |> RW [GSYM SPEC_MOVE_COND]
  val th1 = SPEC_COMPOSE_RULE [th1,x64_putchar_thm,
    x64_pop_r11, x64_pop_r10, x64_pop_r9, x64_pop_r8,
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
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ 0 <= getNumber x1 /\ getNumber x1 < 256)``
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
  val th = th |> Q.INST [`c`|->`n2w (Num (getNumber x1))`]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs, x1, x2, x3, x4, refs, stack,
    (s with output := s.output ++ [CHR (Num (getNumber x1))]),NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `vs.base_ptr + 0x18w IN vals.memory_domain /\
        (vs.base_ptr + 0x18w && 0x7w = 0x0w)` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SIMP_TAC std_ss [PULL_FORALL] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,APPEND,bc_stack_ref_inv_def,EVERY2_def]
    \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [isNumber_def,getNumber_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
    \\ `small_int i` by ALL_TAC
    THEN1 (FULL_SIMP_TAC std_ss [small_int_def] \\ intLib.COOPER_TAC)
    \\ `~(i < 0)` by intLib.COOPER_TAC
    \\ FULL_SIMP_TAC std_ss [x64_addr_def]
    \\ STRIP_TAC THEN1
     (Cases_on `i` \\ FULL_SIMP_TAC (srw_ss()) [small_int_def]
      \\ NTAC 250 (TRY (Cases_on `n`) \\ TRY (Cases_on `n'`)
                   \\ SIMP_TAC (srw_ss()) []
                   \\ FULL_SIMP_TAC std_ss [ADD1,GSYM ADD_ASSOC])
      \\ `F` by DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC
         `vals with <| output_stream := vals.output_stream ++ [n2w (Num i)] |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [x64_addr_def]
    \\ `vals.memory (vs.base_ptr + 0x18w) = cs.putchar_ptr` by ALL_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [x64_store_def,one_list_def,SEP_CLAUSES]
      \\ SEP_R_TAC \\ SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def,abs_ml_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,APPEND,bc_stack_ref_inv_def,EVERY2_def]
    \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,PULL_EXISTS]
    \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
    \\ `Num i < 256` by intLib.COOPER_TAC
    \\ IMP_RES_TAC ORD_CHR \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ 0 <= getNumber x1 /\ getNumber x1 < 256)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val _ = add_compiled [th]
  in th end;


(* print error message *)

fun zHEAP_PRINT_MSG msg = let
  val th = SPEC_COMPOSE_RULE [load_char_lemma,x64_call_r15,x64_putchar_thm]
  val th = th |> Q.INST [`c`|->`n2w (ORD chr)`] |> Q.GEN `chr`
  fun spec_for_char c = th |> SPEC (stringSyntax.fromMLchar c)
  val th = SPEC_COMPOSE_RULE (map spec_for_char (explode msg))
  val lemma = prove(
    ``(n2w (ORD c) :: [] = MAP (n2w o ORD) [c]) /\
      (n2w (ORD c) :: MAP (n2w o ORD) cs = MAP (n2w o ORD) (c::cs))``,
    SIMP_TAC std_ss [MAP])
  val th = th |> SIMP_RULE std_ss [GSYM APPEND_ASSOC,APPEND]
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) []))
              |> RW [lemma]
  val lemma = th
  val ((load_r15,_,_),_) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode "mov r15,[r9+24]")
  val th1 = SPEC_COMPOSE_RULE [ x64_push_r0, x64_push_r1, x64_push_r2,
    x64_push_r3, x64_push_r6, x64_push_r7, x64_push_r8, x64_push_r9,
    x64_push_r10, x64_push_r11, x64_push_r15, load_r15, lemma,
    x64_pop_r15, x64_pop_r11, x64_pop_r10, x64_pop_r9, x64_pop_r8, x64_pop_r7,
    x64_pop_r6, x64_pop_r3, x64_pop_r2, x64_pop_r1, x64_pop_r0]
    |> REWRITE_RULE [TL,HD,NOT_CONS_NIL,SEP_CLAUSES,STAR_ASSOC]
    |> SIMP_RULE (std_ss++sep_cond_ss) []
    |> Q.INST [`pi`|->`cs.getchar_ptr`,
               `input`|->`MAP (n2w o ORD) (DROP 1 s.input)`,
               `output`|->`MAP (n2w o ORD) s.output`]
    |> RW [GSYM MAP_APPEND]
  val th = th1 |> Q.INST [`rip`|->`p`]
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
  val msg_tm = stringSyntax.fromMLstring msg
  val th = th |> Q.SPEC `zHEAP (cs, x1, x2, x3, x4, refs, stack,
    (s with output := s.output ++ ^msg_tm),NONE) * ~zS * ^pc`
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
         vals.output_stream ++ MAP (n2w o ORD) ^msg_tm |>`
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
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  val _ = add_compiled [th]
  in th end;

val error_msg = error_msg_def |> concl |> rand |> stringSyntax.fromHOLstring;

val zHEAP_PRINT_ERROR_MSG = zHEAP_PRINT_MSG error_msg
                              |> RW [GSYM error_msg_def]

val print_fn = zHEAP_PRINT_MSG "<fn>"
val print_ref = zHEAP_PRINT_MSG "<ref>"
val print_true = zHEAP_PRINT_MSG "true"
val print_false = zHEAP_PRINT_MSG "false"
val print_cons = zHEAP_PRINT_MSG "<constructor>"

val _ = zHEAP_PRINT_MSG "\\n"
val _ = zHEAP_PRINT_MSG "\\t"
val _ = zHEAP_PRINT_MSG "\\\\"
val _ = zHEAP_PRINT_MSG "\""

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
  val (th,goal) = SPEC_WEAKEN_RULE th ``zHEAP_ERROR cs``
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

val heap_lookup_IMP_heap_length = prove(
  ``!heap a k. (heap_lookup a heap = SOME (Unused k)) ==>
               k < heap_length heap``,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def,heap_length_def,MAP,SUM]
  \\ SRW_TAC [] [el_length_def] \\ RES_TAC \\ DECIDE_TAC);

val abs_ml_inv_SP_LESS_LIMIT = prove(
  ``abs_ml_inv stack refs (roots,heap,a,sp) limit ==> sp <= limit``,
  Cases_on `sp = 0`
  \\ ASM_SIMP_TAC std_ss [abs_ml_inv_def,unused_space_inv_def,heap_ok_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC heap_lookup_IMP_heap_length
  \\ DECIDE_TAC);

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
      \\ `(8 * sp) < 18446744073709551616` by
        (IMP_RES_TAC abs_ml_inv_SP_LESS_LIMIT \\ DECIDE_TAC)
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
      \\ `(8 * sp) < 18446744073709551616` by
        (IMP_RES_TAC abs_ml_inv_SP_LESS_LIMIT \\ DECIDE_TAC)
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
  val th1 = zHEAP_GC |> Q.INST [`ttt13`|->`ret`,`ttt14`|->`n2w (8 * needed)`]
  val th = SPEC_COMPOSE_RULE [th1,th]
  val th = SPEC_COMPOSE_RULE [zHEAP_CALL_ALLOC,th]
  val th = abbreviate_code "alloc" ``cs.alloc_ptr`` th
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
  \\ SIMP_TAC std_ss [SUM,MAP,el_length_def,SUM_ACC_DEF]);

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
  val lemma = prove(goal,cheat)
(*
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
*)
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
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ SEP_R_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ Q.PAT_ASSUM `r7 && 0x7w = 0x0w` MP_TAC
  \\ blastLib.BBLAST_TAC);

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
            l <= LENGTH stack /\ l < 2 ** 15 /\ l <> 0 /\ n < 4096)``
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
    \\ `l < sp` by DECIDE_TAC
    \\ MP_TAC (cons_thm |> Q.INST [`stack`|->`([x1; x2; x3; x4] ++ zs2)`,
         `roots`|->`REVERSE ys1 ++ ([r1; r2; r3; r4] ++ ys2)`,
         `l`|->`LENGTH (REVERSE (zs1:bc_value list))`,
         `xs`|->`(REVERSE zs1)`,`limit`|->`cs.heap_limit`,`tag`|->`n`]
             |> INST_TYPE [``:'a``|->``:63``,``:'b``|->``:64``])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (ASM_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_REVERSE] \\ DECIDE_TAC)
    \\ STRIP_TAC
    \\ `LENGTH (REVERSE zs1) = l` by FULL_SIMP_TAC std_ss [LENGTH_REVERSE]
    \\ FULL_SIMP_TAC std_ss [EVAL ``el_length (BlockRep n rs)``]
    \\ Q.ABBREV_TAC `header = n2w l << 16 + (n2w n << 4) : word64`
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
      \\ `(65536 * l + 16 * n) < 18446744073709551616` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss []
      \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w,EVAL ``dimword(:64)``]
      \\ `(65536 * l + 16 * n) < 18446744073709551616 /\
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

(*
val zHEAP_DEREF = let
  val th = compose_specs ["mov r0,[r0+9]"]
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
*)

(* update ref *)

(*
val zHEAP_UPDATE_REF = let
  val th = compose_specs ["mov [r1+9],r0"]
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
*)

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


(* specific instances of CONS *)

fun tag_for "nil" = ``2n``
  | tag_for "::" = ``3n``
  | tag_for "Pair" = ``4n``
  | tag_for "Some" = ``5n``
  | tag_for "Inl" = ``6n``
  | tag_for "Inr" = ``7n``
  | tag_for "Errors" = ``8n``
  | tag_for "Others" = ``9n``
  | tag_for "Longs" = ``10n``
  | tag_for "Numbers" = ``11n``
  | tag_for "Strings" = ``12n``
  | tag_for _ = failwith "tag_for"

val nil_tag_def  = Define `nil_tag  = ^(tag_for "nil")`;
val cons_tag_def = Define `cons_tag = ^(tag_for "::")`;
val pair_tag_def = Define `pair_tag = ^(tag_for "Pair")`;

val BlockNil_def  = Define `BlockNil = Block nil_tag []`;
val BlockCons_def = Define `BlockCons (x,y) = Block cons_tag [x;y]`;
val BlockPair_def = Define `BlockPair (x,y) = Block pair_tag [x;y]`;

val BlockList_def = Define `
  (BlockList [] = BlockNil) /\
  (BlockList (x::xs) = BlockCons(x,BlockList xs))`;

val BlockBool_def = Define `BlockBool b = Block (bool_to_tag b) []`;
val BlockSome_def = Define `BlockSome x = Block ^(tag_for "Some") [x]`;

val BlockInl_def = Define `BlockInl x = Block ^(tag_for "Inl") [x]`;
val BlockInr_def = Define `BlockInr x = Block ^(tag_for "Inr") [x]`;

val errors_tag_def  = Define `errors_tag = ^(tag_for "Errors")`;
val others_tag_def  = Define `others_tag = ^(tag_for "Others")`;
val longs_tag_def   = Define `longs_tag = ^(tag_for "Longs")`;
val numbers_tag_def = Define `numbers_tag = ^(tag_for "Numbers")`;
val strings_tag_def = Define `strings_tag = ^(tag_for "Strings")`;

val BlockOtherS_def  = Define `BlockOtherS x  = Block others_tag [x]`;
val BlockLongS_def   = Define `BlockLongS x   = Block longs_tag [x]`;
val BlockNumberS_def = Define `BlockNumberS x = Block numbers_tag [x]`;
val BlockStringS_def = Define `BlockStringS x = Block strings_tag [x]`;
val BlockErrorS_def  = Define `BlockErrorS    = Block errors_tag []`;

val Chr_def = Define `Chr c = Number (& (ORD c))`;

val BlockSym_def = Define `
  (BlockSym (StringS s) = BlockStringS (BlockList (MAP Chr s))) /\
  (BlockSym (OtherS s) = BlockOtherS (BlockList (MAP Chr s))) /\
  (BlockSym (LongS s) = BlockLongS (BlockList (MAP Chr s))) /\
  (BlockSym (ErrorS) = BlockErrorS) /\
  (BlockSym (NumberS n) = BlockNumberS (Number n))`;

val BlockNum3_def = Define `
  BlockNum3 (x,y,z) =
    BlockPair (Number (&x), BlockPair (Number (&y),Number (&z)))`;

fun BlockConsPair tag (n,m) = let
  fun index_to_push 1 = zHEAP_PUSH1
    | index_to_push 2 = zHEAP_PUSH2
    | index_to_push 3 = zHEAP_PUSH3
    | index_to_push 4 = zHEAP_PUSH4
    | index_to_push _ = fail()
  val th1 =
    zHEAP_BIG_CONS |> Q.INST [`n`|->tag,`l`|->`2`]
     |> DISCH_ALL |> RW [AND_IMP_INTRO] |> CONV_RULE (RATOR_CONV EVAL)
     |> Q.GEN `imm64` |> SIMP_RULE (srw_ss()) [w2w_n2w]
     |> ONCE_REWRITE_RULE [GSYM n2w_mod]
     |> SIMP_RULE (srw_ss()) [GSYM SPEC_MOVE_COND]
  val th2 = index_to_push m
  val th3 = index_to_push n
  val th = SPEC_COMPOSE_RULE [th2,th3,th1]
           |> SIMP_RULE (srw_ss()) [DECIDE ``2 <= SUC (SUC n:num)``,
                SEP_CLAUSES,GSYM BlockCons_def,GSYM BlockPair_def]
  val _ = add_compiled [th]
  in th end

val _ = map (fn (n,m) =>
    (BlockConsPair `pair_tag` (n,m), BlockConsPair `cons_tag` (n,m)))
  (cross_prod [1,2,3,4] [1,2,3,4] |> Lib.flatten
      |> filter (fn (m,n) => m <> n))

fun Block1 tag = let
  val th1 =
    zHEAP_BIG_CONS |> Q.INST [`n`|->tag,`l`|->`1`]
     |> DISCH_ALL |> RW [AND_IMP_INTRO] |> CONV_RULE (RATOR_CONV EVAL)
     |> Q.GEN `imm64` |> SIMP_RULE (srw_ss()) [w2w_n2w]
     |> ONCE_REWRITE_RULE [GSYM n2w_mod]
     |> SIMP_RULE (srw_ss()) [GSYM SPEC_MOVE_COND]
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH1,th1]
           |> SIMP_RULE (srw_ss()) [DECIDE ``1 <= SUC (n:num)``,
                SEP_CLAUSES,GSYM BlockErrorS_def,
                            GSYM BlockLongS_def,
                            GSYM BlockOtherS_def,
                            GSYM BlockNumberS_def,
                            GSYM BlockStringS_def]
  val _ = add_compiled [th]
  in th end

val thms = map Block1
  [`others_tag`, `longs_tag`, `numbers_tag`, `strings_tag`]

fun GenBlockNil tag th = let
  val th = th |> Q.INST [`k`|->tag]
    |> SIMP_RULE (srw_ss()) [GSYM BlockNil_def,GSYM BlockErrorS_def]
    |> SIMP_RULE (srw_ss()) [w2w_n2w,nil_tag_def,SEP_CLAUSES,errors_tag_def]
  val _ = add_compiled [th]
  in th end;

val BlockNil1 = GenBlockNil `nil_tag` zHEAP_Nil1
val BlockNil2 = GenBlockNil `nil_tag` zHEAP_Nil2
val BlockNil3 = GenBlockNil `nil_tag` zHEAP_Nil3
val BlockNil4 = GenBlockNil `nil_tag` zHEAP_Nil4

val _ = map (GenBlockNil `errors_tag`) [zHEAP_Nil1,zHEAP_Nil2,zHEAP_Nil3,zHEAP_Nil4]


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
    \\ cheat) (* bignum *)
(*
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
      \\ cheat) (* bignum *)
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
            WORD_MUL_LSL,w2n_n2w] \\ cheat) (* bignum *)
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
      \\ cheat) (* bignum *)
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [WORD_MUL_LSL,word_mul_n2w,word_add_n2w,
         LEFT_ADD_DISTRIB])
*)
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
    let r2 = r2 << 16 in
    let r3 = m (r0 + 1w) in
    let r2 = r2 + 2w in
    let r1 = r10 && 1w in
    let r2 = r2 + r1 in
    let m = (r0 + 1w =+ r2) m in
      (r0,r3,r10,r15,dm,m)`

val zBIGNUM_HEADER_WRITE = let
  val th = x64_big_header_res |> Q.INST [`r15`|->`za`]
           |> RW [x64_big_header_def,x64_big_header_pre_def]
  val th = MATCH_MP SPEC_FRAME th |> Q.SPEC `zR 0xDw xa * zR 0xEw ya * cond
             (bignum_mem (frame * one (za - 8w, z)) dm m xa xs ya ys za zs /\
              (r10 = x64_header (q,qs)))`
  val pc = get_pc th
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``(~zS * ^pc * zR 0x0w (za - 9w) * zR 0x3w z * ~zR 0x2w * ~zR 0x1w *
       zR 0xAw (x64_header (q,qs)) *
       zBIGNUMS_HEADER (xa,xs,ya,ys,n2w (LENGTH qs) << 16 + 2w+b2w q,za,zs,frame))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [x64_multiwordTheory.zBIGNUMS_def,
        LET_DEF,SEP_IMP_def,cond_STAR,zBIGNUMS_HEADER_def]
    \\ SIMP_TAC std_ss [word_arith_lemma3,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`dm`,`((za - 0x8w =+ (r10 >>> 1) << 16 + 0x2w + (r10 && 0x1w)) m)`]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ `m (za − 0x8w) = z` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [x64_multiwordTheory.bignum_mem_def]
      \\ Cases_on `xa = ya` \\ FULL_SIMP_TAC std_ss [] \\ SEP_R_TAC)
    \\ Q.PAT_ASSUM `r10 = xxx` ASSUME_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ `((x64_header (q,qs) >>> 1) << 16 = n2w (LENGTH qs) << 16) /\
        (x64_header (q,qs) && 0x1w = b2w q)` by ALL_TAC THEN1
     (SIMP_TAC std_ss [x64_multiwordTheory.x64_header_def]
      \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,b2w_def]
      \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss [x64_multiwordTheory.bignum_mem_def]
    \\ Cases_on `xa = ya` \\ FULL_SIMP_TAC std_ss [] \\ SEP_R_TAC
    \\ SEP_W_TAC \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = th |> Q.GENL [`dm`,`m`] |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * ~zR 0x0w * ~zR 0x1w * ~zR 0x2w * ~zR 0x3w * zR 0xAw r10 *
       zBIGNUMS_HEADER (xa,xs,ya,ys,z,za,zs,frame) *
       cond (r10 = x64_header (q,qs)))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [x64_multiwordTheory.zBIGNUMS_def,
        LET_DEF,SEP_IMP_def,cond_STAR,zBIGNUMS_HEADER_def]
    \\ SIMP_TAC std_ss [word_arith_lemma3,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ NTAC 2 STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [x64_multiwordTheory.zBIGNUMS_def,
        LET_DEF,SEP_IMP_def,cond_STAR,zBIGNUMS_HEADER_def]
    \\ Q.LIST_EXISTS_TAC [`m`,`dm`]
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REPEAT STRIP_TAC
    \\ Cases_on `xa = ya`
    \\ FULL_SIMP_TAC std_ss [x64_multiwordTheory.bignum_mem_def]
    \\ SEP_R_TAC
    \\ Q.PAT_ASSUM `za && 0x7w = 0x0w` MP_TAC
    \\ blastLib.BBLAST_TAC)
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
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``(~zS * zPC p * zR 0x0w (za - 9w) * ~zR 0x1w * ~zR 0x2w *
       zR 0xAw (x64_header (q,qs)) *
       zBIGNUMS_HEADER (xa,xs,ya,ys,z,za,zs,frame) * cond
         ((isPREFIX qs zs) /\ LENGTH qs < dimword (:63)))``
  val lemma = prove(goal,cheat) (* bignum *)
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
  val _ = add_compiled [th];
  val _ = add_decompiled("print_r7",th,3,SOME 3);
  in th end

val th = let
  val th = x64_pop_r7
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``let (r7,ss) = (HD ss,TL ss) in
        (zPC (p + 0x2w) * zR 0x7w r7 * zSTACK (base,ss))``
  val lemma = prove(goal,SIMP_TAC std_ss [LET_DEF,SEP_IMP_REFL])
  val th = MP th lemma
  val _ = add_decompiled("pop_r7",th,2,SOME 2);
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

val _ = add_compiled [x64_print_stack_res]

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
  |> DISCH ``x64_print_stack (r15,output,po,ss) =
               (r15_p,output_p,po_p,ss_p)``
  |> SIMP_RULE std_ss [] |> UNDISCH

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
  |> DISCH ``x64_bignum_setup (r0,r1,r3,r6,r7,r9,dm,m,ss) =
               (r0_s,r1_s,r3_s,r13_s,r14_s,r15_s,dm_s,m_s,ss_s)``
  |> SIMP_RULE std_ss [] |> UNDISCH

val res2 = thF |> SIMP_RULE (std_ss++sep_cond_ss) [zBIGNUMS_HEADER_def,
                    x64_multiwordTheory.zBIGNUMS_def,SEP_CLAUSES,
                    GSYM SPEC_PRE_EXISTS] |> SPEC_ALL

val thG = SPEC_COMPOSE_RULE [res1,res2 |> Q.INST [`dm`|->`dm_s`,`m`|->`m_s`]]

val thH = SPEC_COMPOSE_RULE
   [x64_push_r15, x64_push_r14, x64_push_r13, x64_push_r12,
    x64_push_r11, x64_push_r10, x64_push_r9, x64_push_r8,
    x64_push_r7, x64_push_r6, x64_push_r3, x64_push_r2,
    x64_push_r1, thG]

val thX = let
  val lemma = prove(
    ``(b ==> SPEC m p c q) ==> SPEC m (p * cond b) c (q * cond b)``,
    Cases_on `b` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]);
  val th = MATCH_MP lemma (thH |> DISCH_ALL |> RW [AND_IMP_INTRO])
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
                         \\ SIMP_TAC std_ss [STAR_ASSOC] \\ cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,
     Number (int_op (n2iop (getNumber x3)) (getNumber x1) (getNumber x2)),
     x2,x3,x4,refs,stack,if n2iop (getNumber x3) <> Dec then s else
       s with output := s.output ++ int_to_str (getNumber (x1)),NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^inv) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
      AC CONJ_COMM CONJ_ASSOC])
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
  val lemma = prove(goal,cheat) (* bignum *)
  val th2 = MP th2 lemma
  val lemma = prove(``num_size x1 + num_size x2 + 2 < 4294967296``,cheat) (* bignum *)
  val th = SPEC_COMPOSE_RULE [th1,th2]
           |> DISCH_ALL |> RW [AND_IMP_INTRO,lemma]
           |> RW [GSYM SPEC_MOVE_COND,fetch "-" "temp_code_def"]
  val th3 = zHEAP_JMP_r13
  val (th3,goal) = SPEC_WEAKEN_RULE th3 ``(zHEAP
        (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC ret)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zHEAP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `vals` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC heap_inv_IMP_NONE)
  val th3 = MP th3 lemma |> Q.INST [`P`|->`\x.T`] |> SIMP_RULE std_ss []
  val pc = find_term (can (match_term ``zPC xxx``)) (th |> concl |> rand)
  val (th,goal) = SPEC_WEAKEN_RULE th ``
    zHEAP (cs,Number (int_op (n2iop (getNumber x3)) (getNumber x1) (getNumber x2)),
           x2,x3,x4,refs,stack,if n2iop (getNumber x3) <> Dec then s else
       s with output := s.output ++ int_to_str (getNumber (x1)),
       SOME (\(sp,vals). vals.reg13 = p + 7w)) * ~zS * ^pc
    \/ zHEAP_ERROR (cs)``
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val th = SPEC_COMPOSE_RULE [th,th3]
  val th = abbreviate_code "bignum" ``cs.bignum_ptr`` th
  in th end

fun get_INT_OP n = let
  val th = zHEAP_Num3 |> Q.INST [`k`|->`^n`]
           |> SIMP_RULE (srw_ss()) [w2w_def,w2n_n2w,SEP_CLAUSES]
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH3,th,zHEAP_BIGNUM_OP]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_POP3]
  val th = th |> SIMP_RULE (srw_ss()) [NOT_CONS_NIL,SEP_CLAUSES,
             getNumber_def,n2iop_def,multiwordTheory.int_op_def,HD,TL]
  in th end;

(* small number addition *)

val zHEAP_ADD_SMALL_INT = let
  val th = compose_specs ["add r0,r1"]
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (getNumber x1 + getNumber x2),
                                x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val th = th |> RW []
  val _ = add_compiled [th]
  in th end;


(* small number subtraction *)

val zHEAP_SUB_SMALL_INT = let
  val th = compose_specs ["sub r0,r1"]
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (getNumber x1 - getNumber x2),
                                   x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val th = th |> RW []
  in th end;


(* small number mult *)

val zHEAP_MUL_SMALL_INT = let
  val th = compose_specs ["shr r0,2","mov r15,r2","mul r1","mov r2,r15"]
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (getNumber x1 * getNumber x2),
                                   x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val th = th |> RW []
  in th end;


(* small number div *)

val zHEAP_DIV_SMALL_INT = let
  val th = compose_specs ["mov r15,r2","mov r14,r1",
                          "shr r0,2","shr r1,2","xchg r1,r0",
                          "mov r2,0","div r1",
                          "shl r0,2","mov r2,r15","mov r1,r14"]
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (getNumber x2 / getNumber x1),
                                   x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val th = th |> RW []
  in th end;


(* small number mod *)

val zHEAP_MOD_SMALL_INT = let
  val th = compose_specs ["mov r15,r2","mov r14,r1",
                          "shr r0,2","shr r1,2","xchg r1,r0",
                          "mov r2,0","div r1","mov r0,r2",
                          "shl r0,2","mov r2,r15","mov r1,r14"]
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1 /\ isNumber x2)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL |> DISCH T |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,Number (getNumber x2 % getNumber x1),
                                   x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1 /\ isNumber x2)``
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma
  val th = th |> RW []
  in th end;


(* print number small number *)

val (x64_single_div_res,x64_single_div_def) = x64_decompile "x64_single_div" `
  div r9`

val _ = add_compiled [x64_single_div_res]

val (res,x64_push_digits_def,x64_push_digits_pre_def) = x64_compile `
  x64_push_digits (r0:word64,r9:word64,ss:word64 list) =
    let r2 = 0w in
    let (r0,r2,r9) = x64_single_div (r0,r2,r9) in
    let r2 = r2 + 48w in
    let ss = r2 :: ss in
      if r0 = 0w then (r0,r2,r9,ss) else
        x64_push_digits (r0,r9,ss)`

val (res,x64_push_dec_def,x64_push_dec_pre_def) = x64_compile `
  x64_push_dec (r0,ss) =
    let r2 = 0w in
    let ss = r2 :: ss in
    let r9 = 10w in
    let (r0,r2,r9,ss) = x64_push_digits (r0,r9,ss) in
      (r0,r2,r9,ss)`

val (x64_print_small_int_res,
     x64_print_small_int_def,x64_print_small_int_pre_def) = x64_compile `
  x64_print_small_int (r0,r1,r2,r3,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,
                       output,po,ss:word64 list,dm:word64 set,m:word64 -> word64) =
    let ss = r0 :: ss in
    let ss = r1 :: ss in
    let ss = r2 :: ss in
    let ss = r3 :: ss in
    let ss = r6 :: ss in
    let ss = r7 :: ss in
    let ss = r8 :: ss in
    let ss = r9 :: ss in
    let ss = r10 :: ss in
    let ss = r11 :: ss in
    let ss = r12 :: ss in
    let ss = r13 :: ss in
    let ss = r14 :: ss in
    let ss = r15 :: ss in
    let r15 = m (r9 + 24w) in
    let r0 = r0 >>> 2 in
    let (r0,r2,r9,ss) = x64_push_dec (r0,ss) in
    let (r15,output,po,ss) = x64_print_stack (r15,output,po,ss) in
    let (r15, ss) = (HD ss, TL ss) in
    let (r14, ss) = (HD ss, TL ss) in
    let (r13, ss) = (HD ss, TL ss) in
    let (r12, ss) = (HD ss, TL ss) in
    let (r11, ss) = (HD ss, TL ss) in
    let (r10, ss) = (HD ss, TL ss) in
    let (r9, ss) = (HD ss, TL ss) in
    let (r8, ss) = (HD ss, TL ss) in
    let (r7, ss) = (HD ss, TL ss) in
    let (r6, ss) = (HD ss, TL ss) in
    let (r3, ss) = (HD ss, TL ss) in
    let (r2, ss) = (HD ss, TL ss) in
    let (r1, ss) = (HD ss, TL ss) in
    let (r0, ss) = (HD ss, TL ss) in
      (r0,r1,r2,r3,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,output,po,ss,dm,m)`

(*

val () = computeLib.add_funs [x64_print_small_int_def,x64_single_div_def,
           x64_push_digits_def,x64_pop_def,x64_push_dec_def,
           x64_print_stack_def,x64_print_def]

*)

val append_number_def = Define `
  append_number output x = output ++ int_to_string (getNumber x)`;

val zHEAP_PRINT_SMALL_INT = let
  val th = x64_print_small_int_res
  val th = th |> Q.INST [`rip`|->`p`]
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\
            isNumber x1)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,s with
         output := STRCAT s.output (int_to_string (getNumber x1)),NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,cheat) (* bignum *)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p *
      cond (isNumber x1)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC]
    \\ SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  val th = th |> RW [GSYM append_number_def]
  val _ = add_compiled [th]
  in th end;


(* number operations *)

(*
val zHEAP_Add = get_INT_OP ``0:num``;
val zHEAP_Sub = get_INT_OP ``1:num``;
val zHEAP_Lt  = get_INT_OP ``2:num``;
val zHEAP_Eq  = get_INT_OP ``3:num``;
val zHEAP_Mul = get_INT_OP ``4:num``;
val zHEAP_Div = get_INT_OP ``5:num``;
val zHEAP_Mod = get_INT_OP ``6:num``;
val zHEAP_Dec = get_INT_OP ``7:num``;
*)

val any_add_def = Define `any_add x1 x2 = Number (getNumber x1 + getNumber x2)`;
val any_sub_def = Define `any_sub x1 x2 = Number (getNumber x1 - getNumber x2)`;
val any_mul_def = Define `any_mul x1 x2 = Number (getNumber x1 * getNumber x2)`;

fun store_bignum_op th = let
  val th = th |> RW (map GSYM [any_add_def,any_sub_def,any_mul_def])
  in add_compiled [th] end

val _ = store_bignum_op zHEAP_ADD_SMALL_INT
val _ = store_bignum_op zHEAP_SUB_SMALL_INT
val _ = store_bignum_op zHEAP_MUL_SMALL_INT

(*
val _ = store_bignum_op zHEAP_Add
val _ = store_bignum_op zHEAP_Sub
val _ = store_bignum_op zHEAP_Mul
val _ = store_bignum_op zHEAP_Dec
*)

(* print string *)

val (bc_print_chars_res,bc_print_chars_def,bc_print_chars_pre_def) = x64_compile `
  bc_print_chars (x1,stack,s) =
    let (x1,stack) = (HD stack, TL stack) in
      if isBlock x1 then (x1,stack,s) else
      if getNumber x1 = 9 then
        let s = s with output := s.output ++ "\\t" in
          bc_print_chars (x1,stack,s)
      else if getNumber x1 = 10 then
        let s = s with output := s.output ++ "\\n" in
          bc_print_chars (x1,stack,s)
      else  if getNumber x1 = 92 then
        let s = s with output := s.output ++ "\\\\" in
          bc_print_chars (x1,stack,s)
      else
        let s = s with output := s.output ++ [CHR (Num (getNumber x1))] in
          bc_print_chars (x1,stack,s)`;

val only_chars_def = Define `
  (only_chars [] = T) /\
  (only_chars ((Number n)::xs) <=> 0 <= n /\ n < 256 /\ only_chars xs) /\
  (only_chars (x::xs) <=> F)`

val bc_print_chars = prove(
  ``!xs x1 b s.
      isBlock b /\ only_chars xs ==>
      bc_print_chars_pre (x1,xs ++ b::stack,s) /\
      (bc_print_chars (x1,xs ++ b::stack,s) =
       (b,stack,s with output := s.output ++
           string_escape (MAP (CHR o Num o getNumber) xs)))``,
  Induct THEN1
   (ONCE_REWRITE_TAC [bc_print_chars_def,bc_print_chars_pre_def]
    \\ NTAC 2 Cases \\ ASM_SIMP_TAC (srw_ss()) [APPEND,LET_DEF,HD,TL,
          canCompare_def,isBlock_def,only_chars_def,
          semanticPrimitivesTheory.string_escape_def]
    \\ Cases \\ SRW_TAC [] (TypeBase.updates_of ``:zheap_state``))
  \\ Cases \\ FULL_SIMP_TAC std_ss [only_chars_def,is_char_def,APPEND]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [bc_print_chars_def,bc_print_chars_pre_def]
  \\ ASM_SIMP_TAC (srw_ss()) [APPEND,LET_DEF,HD,TL,
          canCompare_def,isBlock_def,only_chars_def,getNumber_def]
  \\ Cases_on `i = 9` \\ Cases_on `i = 10` \\ Cases_on `i = 92`
  \\ FULL_SIMP_TAC (srw_ss()) [
        semanticPrimitivesTheory.string_escape_def,isNumber_def]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ `~(i < 0)` by intLib.COOPER_TAC
  \\ `CHR (Num i) <> #"\n" /\ CHR (Num i) <> #"\t" /\
      CHR (Num i) <> #"\\"` by ALL_TAC THEN1
   (Cases_on `i` \\ SRW_TAC [] [CHR_11]
    \\ TRY (`F` by intLib.COOPER_TAC)
    \\ `n < 256` by intLib.COOPER_TAC
    \\ FULL_SIMP_TAC std_ss [CHR_11] \\ intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]);

val zHEAP_PRINT_STRING_BLOCK = let
  val th0 = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_EXPLODE_BLOCK_SIMPLE]
  val th1 =
    bc_print_chars_res
    |> Q.INST [`stack`|->`xs++b::stack`]
    |> DISCH ``isBlock b /\ only_chars xs``
    |> SIMP_RULE std_ss [bc_print_chars,LET_DEF]
    |> RW [GSYM SPEC_MOVE_COND,SEP_CLAUSES]
  val th = SPEC_COMPOSE_RULE [th0,th1]
  val th = SPEC_COMPOSE_RULE [zHEAP_PUSH3,zHEAP_PUSH2,th,zHEAP_POP2,zHEAP_POP3]
    |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,CONJ_ASSOC,SEP_CLAUSES]
  val _ = add_compiled [th]
  in th end;

val (_,bc_print_str_def,bc_print_str_pre_def) = x64_compile `
  bc_print_str (x1,s) =
    let s = s with output := s.output ++ "\"" in
    let s = s with output := STRCAT s.output (string_escape
                (MAP (CHR o Num o getNumber) (getContent x1))) in
    let s = s with output := s.output ++ "\"" in
      (x1,s)`

(* print *)

val (bc_print_aux_res,bc_print_aux_def,bc_print_aux_pre_def) = x64_compile `
  bc_print_aux (x1:bc_value,x2:bc_value,s) =
    if s.local.printing_on = 0x0w then
      (x1,x2,s)
    else if isNumber x1 then
      let s = s with output := append_number s.output x1 in
        (x1,x2,s)
    else if isBlock x1 then
      let x2 = x1 in
      let x1 = Number (&getTag x1) in
        if getNumber x1 = 0 then (* true *)
          let s = s with output := STRCAT s.output "false" in (x1,x2,s)
        else if getNumber x1 = 1 then (* false *)
          let s = s with output := STRCAT s.output "true" in (x1,x2,s)
        else if getNumber x1 = 2 then (* unit_tag *)
          let s = s with output := STRCAT s.output "(" in
          let s = s with output := STRCAT s.output ")" in (x1,x2,s)
        else if getNumber x1 = 3 then (* closure_tag *)
          let s = s with output := STRCAT s.output "<fn>" in (x1,x2,s)
        else if getNumber x1 = 4 then (* string_tag *)
          let x1 = x2 in
          let (x1,s) = bc_print_str (x1,s) in (x1,x2,s)
        else (* constructor *)
          let s = s with output := STRCAT s.output "<constructor>" in (x1,x2,s)
    else (* RefPtr, since CodePtr and StackPtr forbidden *)
      let s = s with output := STRCAT s.output "<ref>" in
        (x1,x2,s)`

val (bc_print_res,bc_print_def,bc_print_pre_def) = x64_compile `
  bc_print (x1:bc_value,x2:bc_value,s) =
    let (x1,x2,s) = bc_print_aux (x1,x2,s) in
    let x1 = Number 0 in
    let x2 = x1 in
      (x1,x2,s)`;

val bc_value1_size_thm = store_thm("bc_value1_size_thm",
  ``!ls. bc_value1_size ls = SUM (MAP bc_value_size ls) + LENGTH ls``,
  Induct THEN1 FULL_SIMP_TAC (srw_ss()) [bytecodeTheory.bc_value_size_def]
  THEN SRW_TAC [ARITH_ss][bytecodeTheory.bc_value_size_def])

val bvs_to_chars_lemma = prove(
  ``!l xs.
       only_chars l ==> (bvs_to_chars l xs =
                           SOME (REVERSE xs ++ MAP (CHR o Num o getNumber) l))``,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ Cases \\ ASM_SIMP_TAC std_ss [only_chars_def,is_char_def,bvs_to_chars_def]
  \\ SRW_TAC [] [getNumber_def]
  \\ REPEAT AP_TERM_TAC
  \\ intLib.COOPER_TAC);

val bc_print_thm = prove(
  ``IS_SOME (bv_to_string x1) ==>
    bc_print_pre (x1,x2,s) /\
    (bc_print (x1,x2,s) =
      (Number 0,Number 0,
       if s.local.printing_on = 0x0w then s else
       s with output := s.output ++ THE (bv_to_string x1)))``,
  cheat (* printing *)
(*
  Cases_on `x1` \\ FULL_SIMP_TAC (srw_ss()) [canCompare_def,bc_print_aux_def,
    bc_print_def,bc_print_pre_def,isBlock_def,isNumber_def,LET_DEF,
    getNumber_def,better_bv_to_ov_def,ov_to_string_def,can_Print_def,
    semanticPrimitivesTheory.int_to_string_def,bc_print_aux_pre_def,
    multiwordTheory.int_to_str_def,getTag_def,append_number_def]
  \\ Cases_on `s.local.printing_on = 0x0w` \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE (Cases_on `n = 4`)
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [ov_to_string_def]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [bc_print_str_def,bc_print_str_pre_def,LET_DEF,
        is_Block_def,getContent_def] THEN1 EVAL_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bvs_to_chars_lemma,ov_to_string_def,
       semanticPrimitivesTheory.string_to_string_def] *))

val zHEAP_RAW_PRINT =
  bc_print_res
    |> DISCH ``IS_SOME (bv_to_string x1)``
    |> SIMP_RULE std_ss [bc_print_thm,SEP_CLAUSES,LET_DEF]
    |> RW [GSYM SPEC_MOVE_COND]


(* IsBlock instruction *)

val (bc_is_block_res,bc_is_block_def,bc_is_block_pre_def) = x64_compile `
  bc_is_block x1 =
    if isBlock x1 then
      let x1 = bool_to_val T in x1
    else
      let x1 = bool_to_val F in x1`

val bc_is_block_thm = prove(
  ``bc_is_block x1 = bool_to_val (isBlock x1)``,
  SRW_TAC [] [bc_is_block_def]);

val zHEAP_isBlock_Intr = bc_is_block_res
  |> SIMP_RULE std_ss [bc_is_block_thm,LET_DEF,bc_is_block_pre_def]


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

val EVEN_w2n = prove(
  ``!w. EVEN (w2n w) = ~(w ' 0)``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [word_index,ZERO_LT_dimword,bitTheory.BIT_def,
    bitTheory.BITS_THM,EVEN_MOD2]
  \\ `n MOD 2 < 2` by FULL_SIMP_TAC std_ss [MOD_LESS]
  \\ DECIDE_TAC);

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
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,
         `(Data (n2w (w2n (p+3w) DIV 2)))::roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [CONS_11,MAP]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [abs_ml_inv_def,roots_ok_def,MEM]
      \\ STRIP_TAC THEN1 METIS_TAC []
      \\ FULL_SIMP_TAC (srw_ss()) [bc_stack_ref_inv_def,EVERY2_def,
            reachable_refs_def,MEM]
      \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,w2w_def]
      \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,PULL_FORALL]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ NTAC 2 (POP_ASSUM MP_TAC)
      \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]
      \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [EVEN_w2n]
    \\ SIMP_TAC std_ss [x64_addr_def,GSYM w2w_def,
         w2n_lsr |> Q.SPECL [`w`,`1`] |> SIMP_RULE std_ss [] |> GSYM]
    \\ POP_ASSUM MP_TAC \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,^ss) * ~zS * zPC p * cond (EVEN (w2n (p + 3w)))``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
                                AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;


(* load stop_addr *)

val zHEAP_LOAD_STOP_ADDR = let
  val th = spec "mov r13, [r9+136]"
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 136w) = s.local.stop_addr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals). (s.local.stop_addr = vals.reg13))``
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
    \\ Q.EXISTS_TAC `vals with <| reg13 := s.local.stop_addr |>`
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
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in GSYM th end;

val zHEAP_JMP_STOP_ADDR = let
  val th = zHEAP_JMP_r13 |> Q.INST [`P`|->`\x.T`] |> SIMP_RULE std_ss []
  val th = SPEC_COMPOSE_RULE [zHEAP_LOAD_STOP_ADDR,th]
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ¬zS * zPC s.local.stop_addr``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR,zHEAP_def,SEP_CLAUSES]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `vals`
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ METIS_TAC [])
  val th = MP th lemma
  in th end


(* call-lex-ptr-pop-and-store stop_addr *)

val zHEAP_CALL_LEX_WITH_STOP_ADDR = let
  val th1 = compose_specs ["mov r15,[r9+120]"]
  val th2 = compose_specs ["mov [r9+136],r15"]
  val th = SPEC_COMPOSE_RULE [th1,x64_call_r15,x64_pop_r15,th2]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,HD,TL] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 0x78w) = cs.lex_ptr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
              s with local := (s.local with stop_addr := p+7w),NONE) * ~zS *^pc`
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
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg15 := p + 7w;
         memory := (vals.reg9 + 0x88w =+ p + 0x7w) vals.memory |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs with local := (s.local with stop_addr := p+7w)`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL,x64_store_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def,SEP_CLAUSES]
    \\ Q.ABBREV_TAC `f = vals.memory`
    \\ Q.ABBREV_TAC `df = vals.memory_domain`
    \\ SEP_WRITE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;


(* call-install-ptr-pop-and-store stop_addr *)

val zHEAP_CALL_INSTALL_WITH_STOP_ADDR = let
  val th1 = compose_specs ["mov r15,[r9+128]"]
  val th2 = compose_specs ["mov [r9+136],r15"]
  val th = SPEC_COMPOSE_RULE [th1,x64_call_r15,x64_pop_r15,th2]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,HD,TL] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 128w) = cs.install_and_run_ptr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
              s with local := (s.local with stop_addr := p + 10w),NONE) * ~zS *^pc`
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
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg15 := p + 10w;
         memory := (vals.reg9 + 0x88w =+ p + 10w) vals.memory |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs with local := (s.local with stop_addr := p + 10w)`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL,x64_store_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def,SEP_CLAUSES]
    \\ Q.ABBREV_TAC `f = vals.memory`
    \\ Q.ABBREV_TAC `df = vals.memory_domain`
    \\ SEP_WRITE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;


(* set stop_addr using jump *)

val zHEAP_SET_STOP_ADDR = let
  val th2 = compose_specs ["mov [r9+136],r15"]
  val th = SPEC_COMPOSE_RULE [x64_call_imm,x64_pop_r15,th2]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> DISCH_ALL |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,HD,TL,NOT_CONS_NIL] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
              s with local := (s.local with stop_addr := p+6w),NONE) * ~zS *^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
  gg goal
*)
  val lemma = prove(goal,
    fs []
    \\ SIMP_TAC std_ss [LET_DEF,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ STRIP_TAC \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [heap_inv_def,LENGTH_MAP,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
      \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.PAT_ASSUM `heap_vars_ok vs` MP_TAC
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg15 := p + 6w;
         memory := (vals.reg9 + 0x88w =+ p + 0x6w) vals.memory |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs with local := (s.local with stop_addr := p+6w)`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL,x64_store_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def,SEP_CLAUSES]
    \\ Q.ABBREV_TAC `f = vals.memory`
    \\ Q.ABBREV_TAC `df = vals.memory_domain`
    \\ SEP_WRITE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in th end;


(* set stop_addr to zero *)

val zHEAP_ZERO_STOP_ADDR = let
  val th = compose_specs ["mov r15,0","mov [r9+136], r15"]
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND,HD,TL] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (cs,x1,x2,x3,x4,refs,stack,
              s with local := (s.local with stop_addr := 0w),NONE) * ~zS *^pc`
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
      \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,heap_vars_ok_def] \\ blastLib.BBLAST_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with <| reg15 := 0w;
         memory := (vals.reg9 + 0x88w =+ 0w) vals.memory |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs with local := (s.local with stop_addr := 0w)`,
         `r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL,x64_store_def]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1]
    \\ SEP_R_TAC \\ FULL_SIMP_TAC (srw_ss()) [heap_vars_ok_def,SEP_CLAUSES]
    \\ Q.ABBREV_TAC `f = vals.memory`
    \\ Q.ABBREV_TAC `df = vals.memory_domain`
    \\ SEP_WRITE_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
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


(* load print_ptr *)

val zHEAP_LOAD_PRINT_PTR = let
  val th = spec "mov r15, [r9+72]"
  val th = th |> Q.INST [`rip`|->`p`]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = DISCH ``vals.memory (vals.reg9 + 72w) = cs.print_ptr`` th
              |> SIMP_RULE std_ss []
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val inv = ``SOME (\(sp:num,vals). (cs.print_ptr = vals.reg15))``
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
    \\ Q.EXISTS_TAC `vals with <| reg15 := cs.print_ptr |>`
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
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in GSYM th end;


(* full EQUAL *)

val EVEN_w2n_IMP = prove(
  ``!w. EVEN (w2n w) ==> (0x2w * n2w (w2n w DIV 2) = (w:word64))``,
  SIMP_TAC std_ss [EVEN_w2n,n2w_w2n,
    GSYM (w2n_lsr |> Q.SPECL [`w`,`1`] |> SIMP_RULE std_ss [])]
  \\ blastLib.BBLAST_TAC);

val zHEAP_EQUAL = let
  val th1 = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_LOAD_EQUAL_PTR,zHEAP_CALL_R15]
  val th = SPEC_COMPOSE_RULE [zHEAP_RAW_EQUAL,zHEAP_RET]
  val th = SPEC_COMPOSE_RULE [th1,th]
  val th = abbreviate_code "equal" ``cs.equal_ptr`` th
  val lemma = prove(
    ``EVEN (w2n (w + 12w)) = EVEN (w2n (w:word64))``,
    SIMP_TAC std_ss [EVEN_w2n] \\ blastLib.BBLAST_TAC);
  val th = th |> RW [TL,HD,getCodePtr_def,NOT_CONS_NIL,isCodePtr_def,SEP_CLAUSES]
              |> SIMP_RULE (std_ss++sep_cond_ss) [EVEN_w2n_IMP,SPEC_MOVE_COND]
              |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND]
  val th = SPEC_COMPOSE_RULE [zHEAP_POP2,th] |> RW [lemma]
  in th end


(* full PRINT *)

val zHEAP_PRINT = let
  val th1 = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_LOAD_PRINT_PTR,zHEAP_CALL_R15]
  val th = SPEC_COMPOSE_RULE [zHEAP_RAW_PRINT,zHEAP_RET]
  val th = th |> SIMP_RULE std_ss [word_arith_lemma1]
  val th = SPEC_COMPOSE_RULE [th1,th]
  val th = abbreviate_code "print" ``cs.print_ptr`` th
  val th = SIMP_RULE std_ss [NOT_CONS_NIL,TL,HD] th
  val lemma = prove(
    ``EVEN (w2n (w + 10w)) = EVEN (w2n (w:word64))``,
    SIMP_TAC std_ss [EVEN_w2n] \\ blastLib.BBLAST_TAC);
  val th = th |> RW [TL,HD,getCodePtr_def,NOT_CONS_NIL,isCodePtr_def,SEP_CLAUSES]
              |> SIMP_RULE (std_ss++sep_cond_ss) [EVEN_w2n_IMP,SPEC_MOVE_COND]
              |> RW [AND_IMP_INTRO] |> RW [GSYM SPEC_MOVE_COND,lemma]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_POP1]
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
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REVERSE STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [STAR_ASSOC] \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `x2` \\ FULL_SIMP_TAC std_ss [isCodePtr_def,getCodePtr_def]
      \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,EVERY2_def]
      \\ FULL_SIMP_TAC std_ss [bc_value_inv_def,x64_addr_def]
      \\ `(w2w:63 word -> word64) (n2w n) << 1 = n2w (2 * n)` by ALL_TAC THEN1
        (SIMP_TAC (srw_ss()) [w2w_def,WORD_MUL_LSL,word_mul_n2w,MOD_COMMON_FACTOR])
      \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,
         `(Data (n2w (w2n (p+3w) DIV 2)))::roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [CONS_11,MAP]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [abs_ml_inv_def,roots_ok_def,MEM]
      \\ STRIP_TAC THEN1 METIS_TAC []
      \\ FULL_SIMP_TAC (srw_ss()) [bc_stack_ref_inv_def,EVERY2_def,
            reachable_refs_def,MEM]
      \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,w2w_def]
      \\ FULL_SIMP_TAC std_ss [PULL_EXISTS,PULL_FORALL]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ NTAC 2 (POP_ASSUM MP_TAC)
      \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]
      \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [EVEN_w2n]
    \\ SIMP_TAC std_ss [x64_addr_def,GSYM w2w_def,
         w2n_lsr |> Q.SPECL [`w`,`1`] |> SIMP_RULE std_ss [] |> GSYM]
    \\ Q.PAT_ASSUM `~(p + 0x3w) ' 0` MP_TAC \\ blastLib.BBLAST_TAC)
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


(* load small const *)

val zHEAP_LOAD_IMM1 = let
  val th1 = spec "xor r0,r0"
  val ((th2,_,_),_) = prog_x64Lib.x64_spec_memory64 "05"
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val th = th |> SIMP_RULE (srw_ss()) [w2w_n2w]
  val lemma = prove(
    ``4 * k < 2 ** 31 ==>
      ((n2w (BITS 31 0 (SIGN_EXTEND 32 64 (w2n ((n2w (4 * k)):word32))
       MOD 4294967296))) = n2w (4 * k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(4 * k) < 4294967296 /\ ~(2147483648 <= 4 * k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = RW [lemma] (th |> Q.INST [`imm32`|->`n2w (4 * k)`,`rip`|->`p`])
           |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  val pc = get_pc th
  val pre = ``4 * (k:num) < 2 ** 31``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,Number (& k),x2,x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
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
    \\ Q.EXISTS_TAC `vals with reg0 := n2w (4 * k)`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`Data (n2w (2 * k))`,
         `r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def]
    \\ `BITS 62 0 (2 * k) = 2 * k` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [bitTheory.BITS_THM]
      \\ FULL_SIMP_TAC std_ss [small_int_def,integerTheory.INT_LT]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [w2w_n2w,WORD_MUL_LSL,word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ MATCH_MP_TAC abs_ml_inv_Num
    \\ Q.LIST_EXISTS_TAC [`x1`,`r1`]
    \\ FULL_SIMP_TAC std_ss []
    \\ DECIDE_TAC)
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
      AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;

val zHEAP_LOAD_IMM2 = let
  val th1 = spec "xor r1,r1"
  val ((th2,_,_),_) = prog_x64Lib.x64_spec_memory64 "4881C1"
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val th = th |> SIMP_RULE (srw_ss()) [w2w_n2w]
  val lemma = prove(
    ``4 * k < 2 ** 31 ==>
      ((n2w ( (SIGN_EXTEND 32 64 (w2n ((n2w (4 * k)):word32))))) =
       n2w (4 * k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(4 * k) < 4294967296 /\ ~(2147483648 <= 4 * k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = RW [lemma] (th |> Q.INST [`imm32`|->`n2w (4 * k)`,`rip`|->`p`])
           |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  val pc = get_pc th
  val pre = ``4 * k:num < 2 ** 31``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,x1,Number (& k),x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg1 := n2w (4 * k)`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`Data (n2w (2 * k))`,
         `r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def]
    \\ `BITS 62 0 (2 * k) = 2 * k` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [bitTheory.BITS_THM]
      \\ FULL_SIMP_TAC std_ss [small_int_def,integerTheory.INT_LT]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [w2w_n2w,WORD_MUL_LSL,word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ MATCH_MP_TAC swap12_lemma
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ MATCH_MP_TAC abs_ml_inv_Num
    \\ Q.LIST_EXISTS_TAC [`x2`,`r2`]
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [small_int_def,integerTheory.INT_LT]
    \\ MATCH_MP_TAC swap12_lemma
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
      AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;

val zHEAP_LOAD_IMM2_ALT = let
  val th1 = spec "xor r1,r1"
  val ((th2,_,_),_) = prog_x64Lib.x64_spec_memory64 "81C1"
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val th = th |> SIMP_RULE (srw_ss()) [w2w_n2w]
  val lemma = prove(
    ``4 * k < 2 ** 31 ==>
      ((n2w (BITS 31 0 (SIGN_EXTEND 32 64 (w2n ((n2w (4 * k)):word32))
       MOD 4294967296))) = n2w (4 * k):word64)``,
    FULL_SIMP_TAC (srw_ss()) [bitTheory.SIGN_EXTEND_def,
       LET_DEF,bitTheory.BIT_def,bitTheory.BITS_THM2]
    \\ REPEAT STRIP_TAC
    \\ `(4 * k) < 4294967296 /\ ~(2147483648 <= 4 * k)` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [DIV_EQ_X]) |> UNDISCH
  val th = RW [lemma] (th |> Q.INST [`imm32`|->`n2w (4 * k)`,`rip`|->`p`])
           |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]
  val pc = get_pc th
  val pre = ``4 * k:num < 2 ** 31``
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals /\ ^pre)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma |> DISCH_ALL
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC
    `zHEAP (cs,x1,Number (& k),x3,x4,refs,stack,s,NONE) * ~zS * ^pc`
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ SIMP_TAC std_ss [Once heap_inv_def] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [zHEAP_def,SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `vals with reg1 := n2w (4 * k)`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REVERSE STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()++star_ss) [zVALS_def])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_inv_def]
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`Data (n2w (2 * k))`,
         `r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [x64_addr_def]
    \\ `BITS 62 0 (2 * k) = 2 * k` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [bitTheory.BITS_THM]
      \\ FULL_SIMP_TAC std_ss [small_int_def,integerTheory.INT_LT]
      \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [w2w_n2w,WORD_MUL_LSL,word_mul_n2w]
    \\ FULL_SIMP_TAC std_ss [MULT_ASSOC]
    \\ MATCH_MP_TAC swap12_lemma
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ MATCH_MP_TAC abs_ml_inv_Num
    \\ Q.LIST_EXISTS_TAC [`x2`,`r2`]
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [small_int_def,integerTheory.INT_LT]
    \\ MATCH_MP_TAC swap12_lemma
    \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma |> DISCH_ALL |> RW [AND_IMP_INTRO]
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p * cond ^pre``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES,
      AC CONJ_COMM CONJ_ASSOC])
  val th = MP th lemma
  in th end;


(* TagEq *)

val (bc_tag_eq_res,bc_tag_eq_def,bc_tag_eq_pre_def) = x64_compile `
  bc_tag_eq (x1,x2) =
    let x1 = Number (&getTag x1) in
      if getNumber x1 = getNumber x2 then
        let x1 = bool_to_val T in (x1,x2)
      else
        let x1 = bool_to_val F in (x1,x2)`

val tag_eq_thm = prove(
  ``(bc_tag_eq (x1,Number (& n)) = (bool_to_val (getTag x1 = n), Number (& n)))``,
  SIMP_TAC (srw_ss()) [bc_tag_eq_def,LET_DEF,getNumber_def] \\ SRW_TAC [] []);

val zHEAP_TagEq =
  SPEC_COMPOSE_RULE [zHEAP_LOAD_IMM2_ALT,bc_tag_eq_res]
  |> SIMP_RULE std_ss [LET_DEF,tag_eq_thm]


(* El *)

val zHEAP_Block_El =
  SPEC_COMPOSE_RULE [zHEAP_LOAD_IMM2_ALT,zHEAP_EL]
  |> SIMP_RULE (srw_ss()) [getNumber_def,isNumber_def]


(* collection of bytecode code abbreviations *)

val code_abbrevs_def = Define `
  code_abbrevs cs =
    bignum_code cs.bignum_ptr UNION
    alloc_code cs.alloc_ptr UNION
    equal_code cs.equal_ptr UNION
    print_code cs.print_ptr UNION
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

fun fix_code th = let
  val th = th
  |> SIMP_RULE std_ss [INSERT_UNION_INSERT,UNION_EMPTY]
  |> SORT_CODE
  |> MERGE_CODE
  |> MATCH_MP SPEC_CODE_ABBREV |> Q.SPEC `code_abbrevs cs`
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss
       [SUBSET_DEF,NOT_IN_EMPTY,IN_UNION,code_abbrevs_def,DISJ_IMP])) |> RW []
  val code_length = th |> concl |> rator |> rand
                       |> find_term (can (match_term ``(p:word64,(x:word8)::xs)``))
                       |> rand |> listSyntax.dest_list |> fst |> length
                    handle HOL_ERR _ => 0
  val _ = if (code_length mod 2 = 0) then () else print "\nWARNING: odd length\n"
  in th end;

fun get_code th = let
  val (_,_,c,_) = fix_code th |> UNDISCH_ALL |> concl |> dest_spec
  in c |> rator |> rand |> rand end




(* --- a lemma for each bytecode instruction --- *)

val zBC_Pop = zHEAP_POP1 |> fix_code
val zBC_Pops = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_POPS] |> fix_code
val zBC_Load = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_LOAD] |> fix_code
val zBC_Store = SPEC_COMPOSE_RULE [zHEAP_STORE,zHEAP_POP1]
  |> RW [IMM32_def] |> fix_code

val zBC_Error = zHEAP_TERMINATE_WITH_ERROR |> fix_code

(*
val zBC_Ref = SPEC_COMPOSE_RULE [zHEAP_NEW_REF,zHEAP_NOP] |> fix_code
val zBC_Deref = zHEAP_DEREF |> fix_code
val zBC_Update = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_UPDATE_REF,zHEAP_POP1] |> fix_code
*)

val zBC_Tick = zHEAP_NOP2 |> fix_code
val zBC_Equal = zHEAP_EQUAL |> fix_code
val zBC_Return = zHEAP_RET |> fix_code
val zBC_PrintC = SPEC_COMPOSE_RULE [zHEAP_COND_PUT_CHAR,zHEAP_NOP] |> fix_code

val zBC_Jump = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "48E9"
  val th = th |> RW [GSYM IMM32_def] |> Q.INST [`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS``
  in th end |> fix_code

val zHEAP_JumpIf = let
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
  in th end

val zBC_JumpIf = zHEAP_JumpIf |> fix_code

val zBC_JumpPtr = zHEAP_JMP_PTR |> fix_code
val zBC_CallPtr = zHEAP_CALL_PTR |> fix_code
val zBC_Call = zHEAP_CALL_IMM |> fix_code
val zBC_PushPtr = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_LOAD_PTR] |> fix_code
val zBC_PushExc = zBC_PushExc_raw |> fix_code
val zBC_PopExc = zBC_PopExc_raw |> fix_code
val zBC_Print = zHEAP_PRINT |> fix_code
val zBC_IsBlock = zHEAP_isBlock_Intr |> fix_code
val zBC_TagEq = zHEAP_TagEq |> fix_code
val zBC_El = zHEAP_Block_El |> fix_code
val zBC_PushInt = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_LOAD_IMM1] |> fix_code

val zBC_ConsNil = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_Nil,zHEAP_NOP] |> fix_code
val zBC_ConsBig = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_BIG_CONS]
  |> DISCH_ALL |> Q.GEN `imm64` |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> RW [GSYM SPEC_MOVE_COND,GSYM CONJ_ASSOC] |> fix_code

val zBC_Add = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_ADD_SMALL_INT,zHEAP_NOP] |> fix_code
val zBC_Sub = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_SWAP_12,zHEAP_SUB_SMALL_INT] |> fix_code

val zBC_Mul = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_MUL_SMALL_INT,zHEAP_NOP] |> fix_code
val zBC_Div = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_DIV_SMALL_INT] |> fix_code
val zBC_Mod = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_MOD_SMALL_INT,zHEAP_NOP] |> fix_code
val zBC_Less = SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_SMALL_INT] |> fix_code

val zBC_Shift0 = SPEC_COMPOSE_RULE [zHEAP_POPS,zHEAP_POP1,zHEAP_NOP]
   |> RW [IMM32_def] |> fix_code
val zBC_Shift1 = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_POPS] |> fix_code
val zBC_Shift2 = SPEC_COMPOSE_RULE [zHEAP_NOP,zHEAP_SIMPLE_Shift] |> fix_code
val zBC_Shift3 = zHEAP_GENERAL_Shift |> fix_code

val zBC_Stop_T = SPEC_COMPOSE_RULE
   [zHEAP_PUSH1,zHEAP_NOP,
    zHEAP_Nil1 |> Q.INST [`k`|->`1`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
        |> RW [GSYM (EVAL ``bool_to_val T``)],
    zHEAP_JMP_STOP_ADDR] |> fix_code

val zBC_Stop_F = SPEC_COMPOSE_RULE
   [zHEAP_PUSH1,zHEAP_NOP,
    zHEAP_Nil1 |> Q.INST [`k`|->`0`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
        |> RW [GSYM (EVAL ``bool_to_val F``)],
    zHEAP_JMP_STOP_ADDR] |> fix_code

val (zBC_EndOfCode, end_of_code_def) = let
  val th = SPEC_COMPOSE_RULE
   [zHEAP_PUSH1,
    zHEAP_Nil1 |> Q.INST [`k`|->`0`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
        |> RW [GSYM (EVAL ``bool_to_val F``)],
    zHEAP_JMP_STOP_ADDR] |> fix_code
  val code = th |> concl |> rator |> rand |> rator |> rand |> rand
  val end_of_code_def = Define `end_of_code = ^code`;
  val th = RW [GSYM end_of_code_def] th
  in (th, end_of_code_def) end

val zBC_LoadRev = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_LoadRev,zHEAP_NOP]
   |> RW [IMM32_def] |> fix_code

val zBC_END_OF_CODE = SPEC_COMPOSE_RULE
   [zHEAP_PUSH1,
    zHEAP_LOAD_IMM1 |> Q.INST [`k`|->`0`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES],
    zHEAP_JMP_STOP_ADDR] |> fix_code

val zBC_Error6 = let
  val th = MATCH_MP SPEC_SUBSET_CODE zHEAP_TERMINATE_WITH_ERROR
           |> Q.SPEC `(p,[0x49w; 0xFFw; 0x61w; 0x28w]) INSERT
                      (p+4w,[0xFFw; 0xC0w]) INSERT error_code cs.error_ptr`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
  val th6 = MP th lemma
  in th6 |> fix_code end

val zBC_Error12 = let
  val th = MATCH_MP SPEC_SUBSET_CODE zHEAP_TERMINATE_WITH_ERROR
           |> Q.SPEC `(p,[0x49w; 0xFFw; 0x61w; 0x28w]) INSERT
                      (p+4w,[0xFFw; 0xC0w]) INSERT
                      (p+6w,[0xFFw; 0xC0w]) INSERT
                      (p+8w,[0xFFw; 0xC0w]) INSERT
                      (p+10w,[0xFFw; 0xC0w]) INSERT error_code cs.error_ptr`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
  val th6 = MP th lemma
  in th6 |> fix_code end

val zBC_Error16 = let
  val th = MATCH_MP SPEC_SUBSET_CODE zHEAP_TERMINATE_WITH_ERROR
           |> Q.SPEC `(p,[0x49w; 0xFFw; 0x61w; 0x28w]) INSERT
                      (p+4w,[0xFFw; 0xC0w]) INSERT
                      (p+6w,[0xFFw; 0xC0w]) INSERT
                      (p+8w,[0xFFw; 0xC0w]) INSERT
                      (p+10w,[0xFFw; 0xC0w]) INSERT
                      (p+12w,[0xFFw; 0xC0w]) INSERT
                      (p+14w,[0xFFw; 0xC0w]) INSERT error_code cs.error_ptr`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
  val th6 = MP th lemma
  in th6 |> fix_code end


(* translation function *)

val small_offset_def = Define `
  small_offset n x =
    if n < 268435456:num then x else ^(get_code zBC_Error)`;

val small_offset6_def = Define `
  small_offset6 n x =
    if n < 268435456:num then x else ^(get_code zBC_Error6)`;

val small_offset12_def = Define `
  small_offset12 n x =
    if n < 268435456:num then x else ^(get_code zBC_Error12)`;

val small_offset16_def = Define `
  small_offset16 n x =
    if n < 268435456:num then x else ^(get_code zBC_Error16)`;

val x64_def = Define `
  (x64 i (Stack Pop) = ^(get_code zBC_Pop)) /\
  (x64 i (Stack (Pops k)) = small_offset k ^(get_code zBC_Pops)) /\
  (x64 i (Stack (Load k)) = small_offset k ^(get_code zBC_Load)) /\
  (x64 i (Stack (Store k)) = small_offset k ^(get_code zBC_Store)) /\
  (x64 i (Stack Add) = ^(get_code zBC_Add)) /\
  (x64 i (Stack Sub) = ^(get_code zBC_Sub)) /\
  (x64 i (Stack Mult) = ^(get_code zBC_Mul)) /\
  (x64 i (Stack Div) = ^(get_code zBC_Div)) /\
  (x64 i (Stack Mod) = ^(get_code zBC_Mod)) /\
  (x64 i (Stack Less) = ^(get_code zBC_Less)) /\
  (x64 i (Stack Equal) = ^(get_code zBC_Equal)) /\
  (x64 i (Stack IsBlock) = ^(get_code zBC_IsBlock)) /\
  (x64 i (Stack (TagEq k)) = small_offset k (^(get_code zBC_TagEq))) /\
  (x64 i (Stack (El k)) = small_offset k (^(get_code zBC_El))) /\
(*
  (x64 i (Stack (LoadRev k)) =
    small_offset k (let offset = k in ^(get_code zBC_LoadRev))) /\
*)
  (x64 i (Stack (Cons tag len)) =
     if tag < 4096 /\ len < 32768 then
       (if len = 0 then
          let k = tag in ^(get_code zBC_ConsNil)
        else
          let l = len in let n = tag in ^(get_code zBC_ConsBig))
     else ^(get_code zBC_Error)) /\
  (x64 i (Stack (PushInt j)) =
     small_offset (Num (ABS j))
       (if j < 0 then ^(get_code zBC_Error) else
          let k = Num j in ^(get_code zBC_PushInt))) /\
  (x64 i (Jump (Addr l)) =
     small_offset6 l (small_offset6 i
       (let imm32 = n2w (2 * l) - n2w i - 6w in ^(get_code zBC_Jump)))) /\
  (x64 i (JumpIf (Addr l)) =
     small_offset12 l (small_offset12 i
       (let imm32 = n2w (2 * l) - n2w i - 12w in ^(get_code zBC_JumpIf)))) /\
  (x64 i (Call (Addr l)) =
     small_offset6 l (small_offset6 i
       (let imm32 = n2w (2 * l) - n2w i - 6w in ^(get_code zBC_Call)))) /\
  (x64 i (PushPtr (Addr l)) =
     small_offset16 l (small_offset16 i
       (let imm32 = n2w (2 * l) - n2w i - 8w in ^(get_code zBC_PushPtr)))) /\
  (x64 i (Jump (Lab _)) = ^(get_code zBC_Error6)) /\
  (x64 i (JumpIf (Lab _)) = ^(get_code zBC_Error12)) /\
  (x64 i (Call (Lab _)) = ^(get_code zBC_Error6)) /\
  (x64 i (PushPtr (Lab _)) = ^(get_code zBC_Error16)) /\
  (x64 i (CallPtr) = ^(get_code zBC_CallPtr)) /\
  (x64 i (Return) = ^(get_code zBC_Return)) /\
(*
  (x64 i (Ref) = ^(get_code zBC_Ref)) /\
  (x64 i (Deref) = ^(get_code zBC_Deref)) /\
  (x64 i (Update) = ^(get_code zBC_Update)) /\
*)
  (x64 i (PopExc) = ^(get_code zBC_PopExc)) /\
  (x64 i (PushExc) = ^(get_code zBC_PushExc)) /\
  (x64 i (Label l) = []) /\
  (x64 i (Tick) = ^(get_code zBC_Tick)) /\
  (x64 i (Print) = ^(get_code zBC_Print)) /\
  (x64 i (PrintC c) =
     (let c = n2w (ORD c):word8 in ^(get_code zBC_PrintC))) /\
  (x64 i (Stop T) = ^(get_code zBC_Stop_T)) /\
  (x64 i (Stop F) = ^(get_code zBC_Stop_F)) /\
  (x64 i _ = ^(get_code zBC_Error))`;

val x64_length_def = Define `
  x64_length bc = LENGTH (x64 0 bc)`;

val x64_inst_length_def = Define `
  x64_inst_length bc = (x64_length bc DIV 2) - 1`;

val LENGTH_IF = prove(
  ``(LENGTH (if b then xs else ys) = if b then LENGTH xs else LENGTH ys) /\
    ((if b then m else n) DIV 2 - 1 = if b then m DIV 2 - 1 else n DIV 2 - 1)``,
  SRW_TAC [] []);

val PushInt_SIMP = prove(
  ``(if Num (ABS v28) < 268435456 then if v28 < 0 then 1 else 4 else 1) =
    if v28 < 268435456 then if v28 < 0 then 1 else 4 else 1:num``,
  intLib.COOPER_TAC);

val x64_inst_length_thm = prove(
  ``!bc. x64_inst_length bc = case bc of (Label l) => 0
                                    | Stack Add => x64_inst_length (Stack Add)
                                    | Jump (Lab l) => x64_inst_length (Jump (Lab l))
                                    | JumpIf (Lab l) => x64_inst_length (JumpIf (Lab l))
                                    | Call (Lab l) => x64_inst_length (Call (Lab l))
                                    | PushPtr (Lab l) => x64_inst_length (PushPtr (Lab l))
                                    | i => x64_inst_length i``,
  Cases \\ EVAL_TAC \\ TRY (Cases_on `b`) \\ EVAL_TAC
  \\ TRY (Cases_on `l`) \\ EVAL_TAC)
  |> SPEC_ALL |> CONV_RULE (RAND_CONV (REWRITE_CONV [x64_inst_length_def,
       x64_length_def,x64_def,LENGTH]))
  |> SIMP_RULE std_ss [LET_DEF,LENGTH,small_offset_def,LENGTH_IF,
       small_offset16_def,small_offset12_def,small_offset6_def,PushInt_SIMP,
       IMM32_def,LENGTH_NTIMES,LENGTH_APPEND,ADD1,GSYM ADD_ASSOC];

val real_inst_length_thm = store_thm("real_inst_length_thm",
  ``x64_inst_length = real_inst_length``,
  cheat) (* fix def of real_inst_length *)
(*
  SIMP_TAC std_ss [FUN_EQ_THM] \\ Cases \\ TRY (Cases_on `b`)
  \\ SIMP_TAC (srw_ss()) [bytecodeExtraTheory.real_inst_length_def]
  \\ SIMP_TAC (srw_ss()) [x64_inst_length_def,x64_length_def,x64_def,
       small_offset_def,LET_DEF,LENGTH]
  \\ TRY (SRW_TAC [] [] \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []
          \\ intLib.COOPER_TAC)
  \\ TRY (Cases_on `l`)
  \\ SIMP_TAC (srw_ss()) [x64_inst_length_def,x64_length_def,x64_def,
       small_offset_def,LET_DEF,LENGTH] \\ EVAL_TAC
  \\ TRY (SRW_TAC [] [] \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []
          \\ intLib.COOPER_TAC));
*)

val EVEN_LENGTH_small_offset = prove(
  ``EVEN (LENGTH x) ==> EVEN (LENGTH (small_offset n x))``,
  SRW_TAC [] [small_offset_def]);

val EVEN_LENGTH_small_offset6 = prove(
  ``EVEN (LENGTH x) ==> EVEN (LENGTH (small_offset6 n x))``,
  SRW_TAC [] [small_offset6_def]);

val EVEN_LENGTH_small_offset12 = prove(
  ``EVEN (LENGTH x) ==> EVEN (LENGTH (small_offset12 n x))``,
  SRW_TAC [] [small_offset12_def]);

val EVEN_LENGTH_small_offset16 = prove(
  ``EVEN (LENGTH x) ==> EVEN (LENGTH (small_offset16 n x))``,
  SRW_TAC [] [small_offset16_def]);

val x64_length_EVEN = prove(
  ``!bc. EVEN (x64_length bc)``,
  Cases \\ TRY (Cases_on `b:bc_stack_op`) \\ TRY (Cases_on `l:loc`)
  \\ TRY (Cases_on `b:bool`)
  \\ SIMP_TAC std_ss [x64_length_def,x64_def,LENGTH,EVEN,LET_DEF]
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset6)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset6)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset12)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset12)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset16)
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset16)
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [LENGTH,EVEN,IMM32_def]
  \\ TRY (MATCH_MP_TAC EVEN_LENGTH_small_offset)
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [LENGTH,EVEN,IMM32_def]
  \\ FULL_SIMP_TAC std_ss [LENGTH_NTIMES,LENGTH]
  \\ FULL_SIMP_TAC std_ss [EVEN_ADD,EVEN_MULT]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [LENGTH,EVEN,IMM32_def]
  \\ FULL_SIMP_TAC std_ss [EVEN_ADD,EVEN_MULT]);

val x64_length_NOT_ZERO = prove(
  ``!bc. ~is_Label bc ==> x64_length bc <> 0``,
  Cases \\ TRY (Cases_on `b:bc_stack_op`) \\ TRY (Cases_on `l:loc`)
  \\ TRY (Cases_on `b:bool`)
  \\ SIMP_TAC std_ss [x64_length_def,x64_def,LENGTH,EVEN,LET_DEF]
  \\ EVAL_TAC \\ SRW_TAC [] [is_Label_def]);

val x64_code_def = zDefine `
  (x64_code i [] = []) /\
  (x64_code i (b::bs) = x64 i b ++ x64_code (i + x64_length b) bs)`;

val x64_code_APPEND = prove(
  ``!xs1 xs2 p.
      x64_code p (xs1 ++ xs2) =
      x64_code p xs1 ++
      x64_code (p + SUM (MAP x64_length xs1)) xs2``,
  Induct \\ SIMP_TAC std_ss [APPEND,x64_code_def,MAP,SUM,WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC,LEFT_ADD_DISTRIB,ADD_ASSOC]);

val LENGTH_x64_IGNORE = prove(
  ``!i n. LENGTH (x64 n i) = LENGTH (x64 0 i)``,
  Cases \\ TRY (Cases_on `b`)  \\ TRY (Cases_on `l`)
  \\ EVAL_TAC \\ SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC);

val LENGTH_x64_code = prove(
  ``!xs p. LENGTH (x64_code p xs) = SUM (MAP x64_length xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [x64_code_def,SUM,MAP,LENGTH,
       LENGTH_APPEND,x64_length_def,LENGTH_x64_IGNORE]);

val x64_code_ALT = store_thm("x64_code_ALT",
  ``!b. x64_code i (b::bs) =
          let c = x64 i b in c ++ x64_code (i + LENGTH c) bs``,
  SIMP_TAC std_ss [x64_code_def,LET_DEF,x64_length_def,LENGTH_x64_IGNORE]);

val LENGTH_small_offset = prove(
  ``LENGTH (small_offset n xs) =
      if n < 268435456 then LENGTH xs else 4``,
  SRW_TAC [] [small_offset_def]);

val LENGTH_IF = store_thm("LENGTH_IF",
  ``LENGTH (if b then xs else ys) = if b then LENGTH xs else LENGTH ys``,
  SRW_TAC [] []);

val APPEND_IF = store_thm("APPEND_IF",
  ``(if b then xs else ys) ++ zs = if b then xs ++ zs else ys ++ zs:'a list``,
  SRW_TAC [] []);

val IF_AND = store_thm("IF_AND",
  ``(if (b1 /\ b2) then c else d) =
    if b1 then (if b2 then c else d) else d``,
  SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val x64_code_eval = save_thm("x64_code_eval",
  ([],``!b. x64_code i (b::bs) =
          let c = x64 i b in c ++ x64_code (i + LENGTH c) bs``)
  |> (Cases \\ TRY (Cases_on `b'`) \\ TRY (Cases_on `l`)) |> fst
  |> map (SIMP_RULE std_ss [LET_DEF] o REWRITE_CONV [x64_code_ALT] o snd)
  |> (fn thms => LIST_CONJ (CONJUNCT1 x64_code_def::thms))
  |> SIMP_RULE std_ss [x64_def,LET_DEF,APPEND,LENGTH,small_offset_def,
       small_offset6_def,small_offset12_def,small_offset16_def,IMM32_def,LENGTH_IF]
  |> REWRITE_RULE [APPEND_IF,APPEND,IF_AND]
  |> SIMP_RULE std_ss []
  |> REWRITE_RULE [GSYM IF_AND])

val length_ok_x64_inst_length = prove(
  ``length_ok x64_inst_length``,
  SIMP_TAC std_ss [bytecodeLabelsTheory.length_ok_def]
  \\ Cases \\ Cases_on `ARB:loc`
  \\ SIMP_TAC (srw_ss()) [x64_inst_length_thm]);


(* install code *)

val append_imm_code_def = Define `
  (append_imm_code p [] = {}) /\
  (append_imm_code p (imm8::imms) =
      (p,[0x4Dw; 0x8Bw; 0x79w; 0x50w]) INSERT
      (p + 0x4w,[0x41w; 0xC6w; 0x7w; imm8]) INSERT
      (p + 0x8w,[0x49w; 0xFFw; 0xC7w]) INSERT
      (p + 0xBw,[0x4Dw; 0x89w; 0x79w; 0x50w]) INSERT
      append_imm_code (p + 0xFw) imms)`;

val INSERTS_LEMMA = prove(
  ``x1 INSERT x2 INSERT x3 INSERT x4 INSERT s = {x1;x2;x3;x4} UNION s``,
  SIMP_TAC (srw_ss()) [EXTENSION] \\ METIS_TAC []);

val append_imm_code = prove(
  ``!imms p s.
      LENGTH s.code + LENGTH imms <= cs.code_heap_length /\
      (s.code_mode = SOME F) ==>
      SPEC X64_MODEL
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p)
       (append_imm_code p imms)
       (zHEAP
        (cs,x1,x2,x3,x4,refs,stack,s with code := s.code ++ imms,
         NONE) * ~zS * zPC (p + n2w (15 * LENGTH imms)))``,
  Induct \\ SIMP_TAC std_ss [LENGTH,APPEND,WORD_ADD_0,APPEND_NIL]
  THEN1 (REPEAT STRIP_TAC \\ Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``)
    \\ FULL_SIMP_TAC std_ss [SPEC_REFL])
  \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [append_imm_code_def,Once INSERTS_LEMMA]
  \\ MATCH_MP_TAC SPEC_COMPOSE
  \\ Q.EXISTS_TAC `(zHEAP (cs,x1,x2,x3,x4,refs,stack,
       s with code := SNOC h s.code,NONE) * ~zS * zPC (p + 15w))`
  \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC (RW [SPEC_MOVE_COND] zHEAP_CODE_SNOC_IMM)
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`p + 15w`,`s with code := SNOC h s.code`])
  \\ SIMP_TAC (srw_ss()) [] \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES,GSYM word_add_n2w,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,
       AC WORD_ADD_COMM WORD_ADD_ASSOC])
  |> SIMP_RULE std_ss [GSYM SPEC_MOVE_COND];


(* code for installing no arg bytecode instructions *)

fun gen_code_for ins = let
  val name = (concat o map (fst o dest_const) o list_dest dest_comb) ins
  val ty = ``:zheap_state # zheap_consts -> zheap_state # zheap_consts``
  val v = mk_var("ic_" ^ name,ty)
  val x = ``x64 0 ^ins``
  val ev = EVAL x
  val th =
    append_imm_code |> SPEC x |> SPEC_ALL
      |> SIMP_RULE std_ss [ev,LENGTH,ADD1]
      |> PURE_REWRITE_RULE [append_imm_code_def,word_arith_lemma1]
      |> SIMP_RULE std_ss [] |> CONV_RULE (RAND_CONV (REWRITE_CONV [GSYM ev]))
  val _ = add_compiled [th]
  val (res,def,pre_def) = x64_compile `
    ^v (s:zheap_state,cs:zheap_consts) =
      let s = s with code := s.code ++ ^x in
        (s,cs)`
  in (ins, CONJ def pre_def |> SIMP_RULE std_ss [LET_DEF]) end

fun closed tm = (length (free_vars tm) = 0)
fun spec_all tm = let
  val vs = free_vars tm
  val i = map (fn v => v |-> (if type_of v = ``:num`` then ``0:num``
                              else if type_of v = ``:int`` then ``0:int``
                              else mk_arb (type_of v))) vs
  in subst i tm end

val no_arg_codes =
  x64_def |> SPEC_ALL |> CONJUNCTS |> map (dest_eq o concl)
          |> filter (closed o snd) |> map (spec_all o fst) |> map rand
          |> filter (fn tm => tm <> ``Label 0``)

fun index tm = ``FST (bc_num ^tm)`` |> EVAL |> concl |> rand

val ic_no_args_def = let
  val is_no_args = map gen_code_for no_arg_codes
  val rest = ``(x1:bc_value,s:zheap_state,cs:zheap_consts)``
  fun mk_ic_case ((ins,defs),rest) = let
    val lhs = defs |> CONJUNCT1 |> concl |> dest_eq |> fst
    in ``if getNumber x1 = & (^(index ins)) then
           let (s,cs) = ^lhs in (x1,s,cs)
         else ^rest`` end
  val tm = foldr mk_ic_case rest is_no_args
  val (res,def,pre_def) = x64_compile `ic_no_args ^rest = ^tm`
  val thms = map snd is_no_args
  val ic_no_args_def = CONJ def pre_def
                       |> REWRITE_RULE thms |> SIMP_RULE std_ss [LET_DEF]
  in ic_no_args_def end;


(* simple one arg *)

fun gen tm = let
  val th = append_imm_code |> SPEC tm |> SPEC_ALL
      |> SIMP_RULE std_ss [LENGTH,ADD1]
      |> PURE_REWRITE_RULE [append_imm_code_def,word_arith_lemma1]
      |> SIMP_RULE std_ss []
  val _ = add_compiled [th]
  in tm end;

(*
  EVAL ``x64 i (Stack (Pops k))``
*)

val pops = ``[0x4Dw; 0x31w; 0xFFw; 0x48w; 0x81w; 0xC4w]:word8 list`` |> gen
val err = ``[0x49w; 0xFFw; 0x61w; 0x28w]:word8 list`` |> gen

val (res,ic_Pops_def,ic_Pops_pre_def) = x64_compile `
  ic_Pops (x2,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
      let x2 = Number (getNumber x2 * 8) in
      let s = s with code := s.code ++ ^pops in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
        (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)`

(*
  EVAL ``x64 i (Stack (TagEq k))``
*)

val tageq1 = ``[0x48w; 0x31w; 0xC9w; 0x81w; 0xC1w]:word8 list`` |> gen
val tageq2 = ``[0x48w; 0xA9w; 0x1w; 0x0w; 0x0w;
      0x0w; 0x48w; 0x75w; 0x7w; 0x48w; 0x83w; 0xE8w; 0x2w; 0x48w; 0xEBw;
      0xEw; 0x48w; 0x8Bw; 0x40w; 0x1w; 0x48w; 0x25w; 0xFFw; 0xFFw; 0x0w;
      0x0w; 0x48w; 0xC1w; 0xE8w; 0x2w; 0x48w; 0x39w; 0xC8w; 0x48w;
      0x75w; 0x8w; 0xB8w; 0x6w; 0x0w; 0x0w; 0x0w; 0x48w; 0xEBw; 0x5w;
      0xB8w; 0x2w; 0x0w; 0x0w; 0x0w]:word8 list`` |> gen

val (res,ic_TagEq_def,ic_TagEq_pre_def) = x64_compile `
  ic_TagEq (x2,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
      let x2 = Number (getNumber x2 * 4) in
      let s = s with code := s.code ++ ^tageq1 in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
      let s = s with code := s.code ++ ^tageq2 in
        (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)`

(*
  EVAL ``x64 i (Stack (El k))``
*)

val el1 = ``[0x48w; 0x31w; 0xC9w; 0x81w; 0xC1w]:word8 list`` |> gen
val el2 = ``[0x48w; 0x8Bw; 0x44w; 0x48w; 0x9w]:word8 list`` |> gen

val (res,ic_El_def,ic_El_pre_def) = x64_compile `
  ic_El (x2,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
      let x2 = Number (getNumber x2 * 4) in
      let s = s with code := s.code ++ ^el1 in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
      let s = s with code := s.code ++ ^el2 in
        (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)`

(*
  EVAL ``x64 i (Stack (PushInt k))``
*)

val pushint = ``[0x48w; 0x50w; 0x48w; 0x31w; 0xC0w; 0x5w]:word8 list`` |> gen

val (res,ic_PushInt_def,ic_PushInt_pre_def) = x64_compile `
  ic_PushInt (x2,x3,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
    if getNumber x3 = 0 then
      let x2 = Number (getNumber x2 * 4) in
      let s = s with code := s.code ++ ^pushint in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
        (x2,x3,s,cs)
    else if getNumber x2 = 0 then
      let x2 = Number (getNumber x2 * 4) in
      let s = s with code := s.code ++ ^pushint in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
        (x2,x3,s,cs)
    else
      let s = s with code := s.code ++ ^err in (x2,x3,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,x3,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,x3,s,cs)`

(*
(*
  EVAL ``x64 i (Stack (LoadRev k))``
*)

val x1 = ``[0x48w; 0x50w; 0x48w; 0x8Bw; 0x85w]:word8 list`` |> gen
val x2 = ``[0x4Dw; 0x31w; 0xFFw]:word8 list`` |> gen

val (res,ic_LoadRev_def,ic_LoadRev_pre_def) = x64_compile `
  ic_LoadRev (x1,x2,x3,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
      let x1 = Number 0 in
      let x2 = Number (getNumber x2 + 1) in
      let x2 = Number (getNumber x2 * 8) in
      let x3 = x2 in
      let x2 = Number 0 in
      let s = s with code := s.code ++ ^x1 in
      let s = s with code := s.code ++ IMM32 (addr_calc x1 x2 x3) in
      let s = s with code := s.code ++ ^x2 in
        (x1,x2,x3,s,cs)
    else let s = s with code := s.code ++ ^err in (x1,x2,x3,s,cs)
    else let s = s with code := s.code ++ ^err in (x1,x2,x3,s,cs)`
*)

(*
  EVAL ``x64 i (PrintC c)``
*)

val printc1 = ``[0x4Dw; 0x8Bw; 0xB9w; 0x90w; 0x0w; 0x0w; 0x0w; 0x4Dw; 0x85w; 0xFFw;
    0x48w; 0x74w; 0x34w; 0x48w; 0x50w; 0x48w; 0x51w; 0x48w; 0x52w;
    0x48w; 0x53w; 0x48w; 0x56w; 0x48w; 0x57w; 0x49w; 0x50w; 0x49w;
    0x51w; 0x49w; 0x52w; 0x49w; 0x53w; 0xBFw]:word8 list`` |> gen
val printc2 = ``[0x0w; 0x0w;
    0x0w; 0x49w; 0x8Bw; 0x41w; 0x18w; 0x48w; 0xFFw; 0xD0w; 0x49w; 0x5Bw;
    0x49w; 0x5Aw; 0x49w; 0x59w; 0x49w; 0x58w; 0x48w; 0x5Fw; 0x48w;
    0x5Ew; 0x48w; 0x5Bw; 0x48w; 0x5Aw; 0x48w; 0x59w; 0x48w; 0x58w;
    0x4Dw; 0x31w; 0xFFw]:word8 list`` |> gen

val (res,ic_PrintC_test_def,ic_PrintC_test_pre_def) = x64_compile `
  ic_PrintC_test (x2) =
    if isSmall x2 then
      if getNumber x2 < 256 then x2 else let x2 = Number 0 in x2
    else let x2 = Number 0 in x2`;

val (res,ic_PrintC_def,ic_PrintC_pre_def) = x64_compile `
  ic_PrintC (x2,s,cs:zheap_consts) =
    let s = s with code := s.code ++ ^printc1 in
    let x2 = ic_PrintC_test x2 in
    let s = s with code := SNOC (n2w (Num (getNumber x2))) s.code in
    let s = s with code := s.code ++ ^printc2 in
      (x2,s,cs)`

(*
  EVAL ``x64 i (Stack (Store x))``
*)

val store1 = ``[0x48w; 0x89w; 0x84w; 0x24w]:word8 list`` |> gen
val store2 = ``[0x48w; 0x58w]:word8 list`` |> gen

val (res,ic_Store_def,ic_Store_pre_def) = x64_compile `
  ic_Store (x2,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
      let x2 = Number (getNumber x2 * 8) in
      let s = s with code := s.code ++ ^store1 in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
      let s = s with code := s.code ++ ^store2 in
        (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)`

(*
  EVAL ``x64 i (Stack (Load x))``
*)

val load = ``[0x48w; 0x50w; 0x48w; 0x8Bw; 0x84w; 0x24w]:word8 list`` |> gen

val (res,ic_Load_def,ic_Load_pre_def) = x64_compile `
  ic_Load (x2,s,cs:zheap_consts) =
    if isSmall x2 then
    if getNumber x2 < 268435456 then
      let x2 = Number (getNumber x2 * 8) in
      let s = s with code := s.code ++ ^load in
      let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
        (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)
    else let s = s with code := s.code ++ ^err in (x2,s,cs)`

(* complicated one args *)

(*
  ``x64 i (Jump (Addr a))`` |> SIMP_CONV std_ss [x64_def,small_offset_def,LET_DEF]
*)

val jmp = ``[0x48w;0xE9w]:word8 list`` |> gen
val err6 = ``[0x49w; 0xFFw; 0x61w; 0x28w; 0xFFw; 0xC0w]:word8 list`` |> gen

val _ = hide "ic_Jump"

val (res,ic_Jump_def,ic_Jump_pre_def) = x64_compile `
  ic_Jump (x1,x2,x3:bc_value,s,cs:zheap_consts) =
    let x3 = Number (&LENGTH s.code) in
    if ~isSmall x2 then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs) else
    if ~isSmall x3 then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs) else
    if ~(getNumber x2 < 268435456) then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs) else
    if ~(getNumber x3 < 268435456) then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs)
    else
      let x2 = Number (getNumber x2 * 2) in
      let x1 = Number 6 in
      let s = s with code := s.code ++ ^jmp in
      let s = s with code := s.code ++ IMM32 (addr_calc x1 x2 x3) in
        (x1,x2,x3,s,cs)`

(*
  ``x64 i (Call (Addr a))`` |> SIMP_CONV std_ss [x64_def,small_offset_def,LET_DEF]
*)

val call = ``[0x48w;0xE8w]:word8 list`` |> gen

val _ = hide "ic_Call"

val (res,ic_Call_def,ic_Call_pre_def) = x64_compile `
  ic_Call (x1,x2,x3:bc_value,s,cs:zheap_consts) =
    let x3 = Number (&LENGTH s.code) in
    if ~isSmall x2 then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs) else
    if ~isSmall x3 then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs) else
    if ~(getNumber x2 < 268435456) then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs) else
    if ~(getNumber x3 < 268435456) then
      let s = s with code := s.code ++ ^err6 in (x1,x2,x3,s,cs)
    else
      let x2 = Number (getNumber x2 * 2) in
      let x1 = Number 6 in
      let s = s with code := s.code ++ ^call in
      let s = s with code := s.code ++ IMM32 (addr_calc x1 x2 x3) in
        (x1,x2,x3,s,cs)`

(*
  ``x64 i (JumpIf (Addr a))`` |> SIMP_CONV std_ss [x64_def,small_offset_def,LET_DEF]
*)

val jumpif = ``[0x48w; 0x83w; 0xF8w; 0x2w; 0x48w; 0x58w; 0xFw;
                0x85w]:word8 list`` |> gen
val err12 = ``[0x49w; 0xFFw; 0x61w; 0x28w; 0xFFw; 0xC0w; 0xFFw;
               0xC0w; 0xFFw; 0xC0w; 0xFFw; 0xC0w]:word8 list`` |> gen

val _ = hide "ic_JumpIf"

val (res,ic_JumpIf_def,ic_JumpIf_pre_def) = x64_compile `
  ic_JumpIf (x1,x2,x3:bc_value,s,cs:zheap_consts) =
    let x3 = Number (&LENGTH s.code) in
    if ~isSmall x2 then
      let s = s with code := s.code ++ ^err12 in (x1,x2,x3,s,cs) else
    if ~isSmall x3 then
      let s = s with code := s.code ++ ^err12 in (x1,x2,x3,s,cs) else
    if ~(getNumber x2 < 268435456) then
      let s = s with code := s.code ++ ^err12 in (x1,x2,x3,s,cs) else
    if ~(getNumber x3 < 268435456) then
      let s = s with code := s.code ++ ^err12 in (x1,x2,x3,s,cs)
    else
      let x2 = Number (getNumber x2 * 2) in
      let x1 = Number 12 in
      let s = s with code := s.code ++ ^jumpif in
      let s = s with code := s.code ++ IMM32 (addr_calc x1 x2 x3) in
        (x1,x2,x3,s,cs)`

(*
  ``x64 i (PushPtr (Addr a))`` |> SIMP_CONV std_ss [x64_def,small_offset_def,LET_DEF]
*)

val pushptr = ``[0x48w; 0x50w; 0x48w; 0xE8w; 0x0w; 0x0w; 0x0w; 0x0w; 0x48w;
                 0x58w; 0x48w; 0x5w]:word8 list`` |> gen
val err16 = ``[0x49w; 0xFFw; 0x61w; 0x28w; 0xFFw; 0xC0w; 0xFFw;
               0xC0w; 0xFFw; 0xC0w; 0xFFw; 0xC0w; 0xFFw; 0xC0w;
               0xFFw; 0xC0w]:word8 list`` |> gen

val _ = hide "ic_PushPtr";

val (res,ic_PushPtr_def,ic_PushPtr_pre_def) = x64_compile `
  ic_PushPtr (x1,x2,x3:bc_value,s,cs:zheap_consts) =
    let x3 = Number (&LENGTH s.code) in
    if ~isSmall x2 then
      let s = s with code := s.code ++ ^err16 in (x1,x2,x3,s,cs) else
    if ~isSmall x3 then
      let s = s with code := s.code ++ ^err16 in (x1,x2,x3,s,cs) else
    if ~(getNumber x2 < 268435456) then
      let s = s with code := s.code ++ ^err16 in (x1,x2,x3,s,cs) else
    if ~(getNumber x3 < 268435456) then
      let s = s with code := s.code ++ ^err16 in (x1,x2,x3,s,cs)
    else
      let x2 = Number (getNumber x2 * 2) in
      let x1 = Number 8 in
      let s = s with code := s.code ++ ^pushptr in
      let s = s with code := s.code ++ IMM32 (addr_calc x1 x2 x3) in
        (x1,x2,x3,s,cs)`

(* two args *)

(*
  ``x64 i (Stack (Cons a b))`` |> SIMP_CONV std_ss [x64_def,small_offset_def,LET_DEF]
*)

val cons1 = ``[0x48w; 0x50w; 0xB8w]:word8 list`` |> gen
val cons2 = ``[0x4Dw; 0x31w; 0xFFw]:word8 list`` |> gen
val cons3 = ``[0x48w; 0x50w; 0x41w; 0xBEw]:word8 list`` |> gen
val cons4 = ``[0x4Cw; 0x8Bw; 0xFFw; 0x49w; 0x29w; 0xF7w; 0x4Dw; 0x39w;
               0xF7w; 0x73w; 0x7w; 0x4Dw; 0x8Bw; 0x69w; 0x30w; 0x49w; 0xFFw;
               0xD5w; 0x41w; 0xBEw]:word8 list`` |> gen
val cons5 = ``[0x4Dw; 0x8Bw; 0xFEw; 0x49w; 0xC1w; 0xEFw; 0x10w; 0x48w;
               0x58w; 0x48w; 0x83w; 0xEFw; 0x8w; 0x48w; 0x89w; 0x47w; 0x1w;
               0x49w; 0xFFw; 0xCFw; 0x49w; 0x83w; 0xFFw; 0x0w; 0x48w; 0x75w;
               0xECw; 0x48w; 0x83w; 0xEFw; 0x8w; 0x4Cw; 0x89w; 0x77w; 0x1w;
               0x48w; 0x8Bw; 0xC7w]:word8 list`` |> gen

val (res,ic_Cons_def,ic_Cons_pre_def) = x64_compile `
  ic_Cons (x1,x2,x3:bc_value,s,cs:zheap_consts) =
    if ~isSmall x2 then
      let s = s with code := s.code ++ ^err in (x1,x2,x3,s,cs) else
    if ~isSmall x3 then
      let s = s with code := s.code ++ ^err in (x1,x2,x3,s,cs) else
    if ~(getNumber x3 < 32768) then
      let s = s with code := s.code ++ ^err in (x1,x2,x3,s,cs) else
    if ~(getNumber x2 < 4096) then
      let s = s with code := s.code ++ ^err in (x1,x2,x3,s,cs)
    else
      if getNumber x3 = 0 then
        let x2 = Number (getNumber x2 * 4) in
        let x2 = Number (getNumber x2 + 1) in
        let x2 = Number (getNumber x2 + 1) in
        let s = s with code := s.code ++ ^cons1 in
        let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
        let s = s with code := s.code ++ ^cons2 in
          (x1:bc_value,x2,x3,s,cs)
      else
          let x1 = x2 in
          let x2 = x3 in
          let x2 = Number (getNumber x2 + 1) in
          let x2 = Number (getNumber x2 * 8) in
          let s = s with code := s.code ++ ^cons3 in
          let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
          let s = s with code := s.code ++ ^cons4 in
          let x1 = Number (getNumber x1 * 4) in
          let x1 = Number (getNumber x1 * 4) in
          let x2 = x3 in
          let x2 = Number (getNumber x2 * 8) in
          let x2 = Number (getNumber x2 * 8) in
          let x2 = Number (getNumber x2 * 8) in
          let x2 = Number (getNumber x2 * 8) in
          let x2 = Number (getNumber x2 * 8) in
          let x2 = Number (getNumber x2 * 2) in
          let x1 = Number (getNumber x1 + getNumber x2) in
          let x2 = x1 in
          let s = s with code := s.code ++ IMM32 (n2w (Num (getNumber x2))) in
          let s = s with code := s.code ++ ^cons5 in
            (x1:bc_value,x2,x3,s,cs)`

(*
  ``x64 i (Stack (Shift a b))`` |> SIMP_CONV std_ss [x64_def,small_offset_def,LET_DEF]
*)

(* putting them all together *)

val (res,ic_Any_def,ic_Any_pre_def) = x64_compile `
  ic_Any (x1,x2,x3,s,cs:zheap_consts) =
    if getNumber x1 = & ^(index ``Jump (Addr a)``) then
      let (x1,x2,x3,s,cs) = ic_Jump (x1,x2,x3,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``JumpIf (Addr a)``) then
      let (x1,x2,x3,s,cs) = ic_JumpIf (x1,x2,x3,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``PushPtr (Addr a)``) then
      let (x1,x2,x3,s,cs) = ic_PushPtr (x1,x2,x3,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Call (Addr a)``) then
      let (x1,x2,x3,s,cs) = ic_Call (x1,x2,x3,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (Pops a)``) then
      let (x2,s,cs) = ic_Pops (x2,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (Load a)``) then
      let (x2,s,cs) = ic_Load (x2,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (Store a)``) then
      let (x2,s,cs) = ic_Store (x2,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``PrintC c``) then
      let (x2,s,cs) = ic_PrintC (x2,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Label l``) then
      (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (TagEq a)``) then
      let (x2,s,cs) = ic_TagEq (x2,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (PushInt a)``) then
      let (x2,x3,s,cs) = ic_PushInt (x2,x3,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (El a)``) then
      let (x2,s,cs) = ic_El (x2,s,cs) in (x1,x2,x3,s,cs)
    else if getNumber x1 = & ^(index ``Stack (Cons a b)``) then
      let (x1,x2,x3,s,cs) = ic_Cons (x1,x2,x3,s,cs) in (x1,x2,x3,s,cs)
    else
      let (x1,s,cs) = ic_no_args (x1,s,cs) in (x1,x2,x3,s,cs)`;

val s_with_code = prove(
  ``!s. s = s with code := s.code``,
  Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``));

val ORD_BOUND_LARGE = prove(
  ``ORD c < 2305843009213693952``,
  ASSUME_TAC (Q.SPEC `c` ORD_BOUND) \\ DECIDE_TAC);

val lemma = prove(
  ``(Num ((&n + 1 + 1) * 8) = (n + 2) * 8) /\
    (Num ((&n + 1 + 1 + 1) * 8) = (n + 3) * 8) /\
    (Num (&(n * 4) + 1 + 1) = (n * 4) + 2) /\
    (Num ((&n0 + 1) * 8) = (n0 + 1) * 8) /\
    (Num (&m + &n) = m + n)``,
  intLib.COOPER_TAC);

val ic_PrintC_test_thm = prove(
  ``ic_PrintC_test_pre (Number (&n)) /\
    (Num (getNumber (ic_PrintC_test (Number (&n)))) = if n < 256 then n else 0) /\
    small_int (getNumber (ic_PrintC_test (Number (&n)))) /\
    isNumber (ic_PrintC_test (Number (&n))) /\
    ¬(getNumber (ic_PrintC_test (Number (&n))) < 0)``,
  SIMP_TAC (srw_ss()) [ic_PrintC_test_pre_def,ic_PrintC_test_def,
    getNumber_def,LET_DEF,isSmall_def,canCompare_def,small_int_def]
  \\ SRW_TAC [] [isNumber_def,getNumber_def] \\ intLib.COOPER_TAC);

val real_inst_length_limit = prove(
  ``!bc. real_inst_length bc < 35``,
  cheat); (* fix def of real_inst_length *)
(*
  Cases \\ SIMP_TAC (srw_ss()) [bytecodeExtraTheory.real_inst_length_def]
  \\ TRY (Cases_on `b`) \\ SRW_TAC [] []);
*)

fun ASSERT_TAC P goal = if P goal then ALL_TAC goal
                        else (print "ASSERT_TAC failed."; NO_TAC goal);

val ic_Any_thm = prove(
  ``!n1 n2 n3.
      LENGTH s.code + LENGTH (x64 (LENGTH s.code) (num_bc (n1,n2,n3))) <=
        cs.code_heap_length /\
      (s.code_mode = SOME F) ==>
      ?x1 x2 x3.
        ((* LENGTH s.code + 400 <= cs.code_heap_length ==> *)
         ic_Any_pre (Number (& n1),Number (& n2),Number (& n3),s,cs)) /\
        (ic_Any (Number (& n1),Number (& n2),Number (& n3),s,cs) =
           (x1,x2,x3,s with code := s.code ++ x64 (LENGTH s.code) (num_bc (n1,n2,n3)),cs))``,
  REVERSE (Cases \\ NTAC 22 (TRY (Cases_on `n`) \\ TRY (Cases_on `n'`)))
  \\ FULL_SIMP_TAC (srw_ss()) [ADD1,GSYM ADD_ASSOC]
  \\ FULL_SIMP_TAC (srw_ss()) [num_bc_def,DECIDE ``k < n ==> m + n <> k:num``]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ Q.ABBREV_TAC `k = n` \\ POP_ASSUM (K ALL_TAC)
  \\ Q.ABBREV_TAC `n = n2` \\ POP_ASSUM (K ALL_TAC)
  \\ Q.ABBREV_TAC `n0 = n3` \\ POP_ASSUM (K ALL_TAC)
  \\ SIMP_TAC (srw_ss()) [num_bc_def,LET_DEF,ic_Any_def,ic_Any_pre_def,
       getNumber_def,ic_no_args_def,isNumber_def,
       ic_Pops_def,ic_Pops_pre_def,
       ic_PrintC_def,ic_PrintC_pre_def,
       ic_Load_def,ic_Load_pre_def,
       ic_Store_def,ic_Store_pre_def,
       ic_El_def,ic_El_pre_def,
       ic_PushInt_def,ic_PushInt_pre_def,
       ic_TagEq_def,ic_TagEq_pre_def,
       isSmall_def,canCompare_def]
  \\ FULL_SIMP_TAC (srw_ss()) [num_bc_def,DECIDE ``k < n ==> m + n <> k:num``]
  \\ TRY (SIMP_TAC std_ss [x64_def,LENGTH,LET_DEF] \\ NO_TAC)
  \\ TRY (Cases_on `n < 268435456`
    \\ FULL_SIMP_TAC (srw_ss()) [small_int_def,x64_def,LET_DEF,addr_calc_def,
      small_offset_def,LENGTH,IMM32_def,APPEND_ASSOC,APPEND,ic_PrintC_test_thm,
      SNOC_APPEND,getNumber_def]
    \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,GSYM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,ORD_BOUND_LARGE,lemma]
    \\ CCONTR_TAC \\ intLib.COOPER_TAC)
  \\ TRY (SIMP_TAC std_ss [x64_def,APPEND_NIL,s_with_code] \\ NO_TAC)
  \\ TRY (Cases_on `n < 268435456` \\ Cases_on `LENGTH s.code < 268435456`
    \\ IMP_RES_TAC (DECIDE ``n < (268435456:num) ==> n < 2305843009213693952``)
    \\ FULL_SIMP_TAC (srw_ss()) [small_int_def,x64_def,
        small_offset_def, small_offset6_def, small_offset12_def, small_offset16_def,
        LENGTH,IMM32_def,APPEND_ASSOC,APPEND,
        ic_Jump_def,ic_Jump_pre_def,
        ic_JumpIf_def,ic_JumpIf_pre_def,
        ic_Call_def,ic_Call_pre_def,
        ic_PushPtr_def,ic_PushPtr_pre_def,
        LET_DEF,isSmall_def,
        isNumber_def,getNumber_def,canCompare_def,addr_calc_def,
        AC MULT_COMM MULT_ASSOC]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ REPEAT STRIP_TAC \\ intLib.COOPER_TAC)
  \\ cheat (* install code is broken *)
(*
  (* only Cons from here on *)
  \\ ASSERT_TAC (fn (_,goal) =>
       can (find_term (can (match_term ``Stack (Cons m n)``))) goal)
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ SIMP_TAC std_ss [x64_def]
  \\ Cases_on `n0 = 0` \\ FULL_SIMP_TAC std_ss [LET_DEF] THEN1
   (Cases_on `n < 4096`
    \\ FULL_SIMP_TAC (srw_ss()) [small_int_def,x64_def,LET_DEF,addr_calc_def,
         small_offset_def,LENGTH,IMM32_def,APPEND_ASSOC,APPEND,
         SNOC_APPEND,getNumber_def]
    \\ SIMP_TAC (srw_ss()) [bc_num_def,LET_DEF,ic_Any_def,ic_Any_pre_def,
         ic_Cons_def,ic_Cons_pre_def,isSmall_def,getNumber_def,
         canCompare_def,isNumber_def]
    \\ FULL_SIMP_TAC (srw_ss()) [small_int_def,x64_def,LET_DEF,addr_calc_def,
      small_offset_def,LENGTH,IMM32_def,APPEND_ASSOC,APPEND,
      SNOC_APPEND,getNumber_def]
    \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,GSYM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,ORD_BOUND_LARGE,lemma]
    \\ TRY (REPEAT STRIP_TAC \\ intLib.COOPER_TAC)
    \\ `F` by intLib.COOPER_TAC)
  THEN1
   (Cases_on `n < 4096` \\ Cases_on `n0 < 32768`
    \\ FULL_SIMP_TAC (srw_ss()) [small_int_def,x64_def,LET_DEF,addr_calc_def,
         small_offset_def,LENGTH,EVAL ``IMM32 (n2w n)``,
         APPEND_ASSOC,APPEND,SNOC_APPEND,getNumber_def]
    \\ ASM_SIMP_TAC (srw_ss()) [bc_num_def,LET_DEF,ic_Any_def,ic_Any_pre_def,
         ic_Cons_def,ic_Cons_pre_def,isSmall_def,getNumber_def,
         canCompare_def,isNumber_def]
    \\ `(n * 16 + n0 * 65536) < 18446744073709551616` by DECIDE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [small_int_def,x64_def,LET_DEF,addr_calc_def,
          ``IMM32 (n2w n) ++ xs`` |> REWRITE_CONV [IMM32_def,APPEND] |> GSYM,
          small_offset_def,LENGTH,EVAL ``IMM32 (n2w n)``,
          APPEND_ASSOC,APPEND,SNOC_APPEND,getNumber_def]
    \\ TRY (REPEAT STRIP_TAC \\ intLib.COOPER_TAC)
    \\ TRY (`F` by intLib.COOPER_TAC)
    \\ REPEAT STRIP_TAC
    \\ SRW_TAC [] [WORD_MUL_LSL,word_mul_n2w,w2n_n2w,word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,GSYM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC,ORD_BOUND_LARGE,lemma]
    \\ TRY (REPEAT STRIP_TAC \\ intLib.COOPER_TAC)
    \\ TRY (`F` by intLib.COOPER_TAC)) *));


(* code install that walks down a list *)

val (res,ic_List_def,ic_List_pre_def) = x64_compile `
  ic_List (x1,x2,x3,x4,s,cs:zheap_consts,stack) =
    if isSmall x4 then (x1,x2,x3,x4,s,cs,stack) else
      let x1 = x4 in
      let x2 = Number 0 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in (* HD *)
      let x3 = x1 in
      let x1 = x4 in
      let x2 = Number 1 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in (* TL *)
      let x4 = x1 in
      let x1 = x3 in
      let x2 = Number 0 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in (* FST o HD *)
      let stack = x1::stack in
      let x1 = x3 in
      let x2 = Number 1 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in (* SND o HD *)
      let x3 = x1 in
      let x2 = Number 0 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in (* FST o SND o HD *)
      let stack = x1::stack in
      let x1 = x3 in
      let x2 = Number 1 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in (* SND o SND o HD *)
      let x3 = x1 in
      let (x2,stack) = (HD stack,TL stack) in
      let (x1,stack) = (HD stack,TL stack) in
        if getNumber x1 = 18 then
          let s = s with code_start := s.code in
            ic_List (x1,x2,x3,x4,s,cs,stack)
        else
          let (x1,x2,x3,s,cs) = ic_Any (x1,x2,x3,s,cs) in
            ic_List (x1,x2,x3,x4,s,cs,stack)`

val install_x64_code_lists_def = Define `
  (install_x64_code_lists [] s = s) /\
  (install_x64_code_lists ((x:num # num # num)::xs) s =
     if FST x = 18 then
       install_x64_code_lists xs (s with code_start := s.code)
     else install_x64_code_lists xs
       (s with code := s.code ++ x64_code (LENGTH s.code) [num_bc x]))`;

val ic_List_thm = prove(
  ``!code x1 x2 x3 s cs stack.
      (s.code_mode = SOME F) ==>
      ?y1 y2 y3.
        (ic_List_pre (x1,x2,x3,BlockList (MAP BlockNum3 code),s,cs,stack)) /\
        (ic_List (x1,x2,x3,BlockList (MAP BlockNum3 code),s,cs,stack) =
           (y1,y2,y3,BlockList [],install_x64_code_lists code s,cs,stack))``,
  Induct \\ SIMP_TAC std_ss [MAP,APPEND] THEN1
   (FULL_SIMP_TAC std_ss [APPEND] \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [Once ic_List_def,Once ic_List_pre_def,BlockList_def]
    \\ FULL_SIMP_TAC std_ss [x64_code_def,APPEND_NIL,install_x64_code_lists_def]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,HD,TL,EVAL ``isSmall BlockNil``]
    \\ EVAL_TAC)
  \\ SIMP_TAC std_ss [Once ic_List_def,Once ic_List_pre_def]
  \\ SIMP_TAC std_ss [isSmall_def,x64_code_def,LET_DEF,
         APPEND_NIL,s_with_code,canCompare_def,NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [getNumber_def,getContent_def,BlockList_def,
       BlockNum3_def,isSmall_def,BlockCons_def]
  \\ SIMP_TAC (srw_ss()) [EVAL ``Num 0``,EVAL ``Num 1``,EL,HD,TL,getContent_def,
       isBlock_def,BlockNum3_def,isNumber_def,getNumber_def] \\ REPEAT STRIP_TAC
  \\ `?h1 h2 h3. h = (h1,h2,h3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [EVAL ``Num 0``,EVAL ``Num 1``,EL,HD,TL,getContent_def,
       isBlock_def,BlockNum3_def,isNumber_def,getNumber_def,canCompare_def,
       BlockPair_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `h1 = 18` \\ FULL_SIMP_TAC std_ss [] THEN1
   (SEP_I_TAC "ic_List" \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC (Q.SPECL [`h1`,`h2`,`h3`] ic_Any_thm)
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 cheat (* req. check for space in code heap *)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [install_x64_code_lists_def,x64_code_def,APPEND_NIL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x1`,`x2`,`x3`,
      `s with code := s.code ++ x64 (LENGTH s.code) (num_bc (h1:num,h2,h3))`,
      `cs`,`stack`])
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_x64_IGNORE,x64_length_def] \\ EVAL_TAC);

val (ic_full_res,ic_full_def,ic_full_pre_def) = x64_compile `
  ic_full (x1,x2,x3,x4,s,cs:zheap_consts,stack) =
    let stack = x1 :: stack in
    let stack = x2 :: stack in
    let stack = x3 :: stack in
    let (x1,x2,x3,x4,s,cs,stack) = ic_List (x1,x2,x3,x4,s,cs,stack) in
    let (x3,stack) = (HD stack, TL stack) in
    let (x2,stack) = (HD stack, TL stack) in
    let (x1,stack) = (HD stack, TL stack) in
    let x4 = x1 in
      (x1,x2,x3,x4,s,cs,stack)`

val ic_full_thm = prove(
  ``(s.code_mode = SOME F) ==>
    ic_full_pre (x1,x2,x3,BlockList (MAP BlockNum3 code),s,cs,stack) /\
    (ic_full (x1,x2,x3,BlockList (MAP BlockNum3 code),s,cs,stack) =
      (x1,x2,x3,x1,install_x64_code_lists code s,cs,stack))``,
  Q.SPEC_TAC (`x4`,`x4`) \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ic_full_def,ic_full_pre_def,LET_DEF]
  \\ MP_TAC (ic_List_thm |> SPEC_ALL |> Q.INST [`stack`|->`x3::x2::x1::stack`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []);

val install_x64_code_lists_code_mode = prove(
  ``!code s.
       ((install_x64_code_lists code s).code_mode = s.code_mode) /\
       (((install_x64_code_lists code s) with code_mode := mode) =
        ((install_x64_code_lists code (s with code_mode := mode))))``,
  Induct \\ SRW_TAC [] [install_x64_code_lists_def]);

(*
val zHEAP_WRITE_end_of_code = let
  val tm = ``end_of_code``
  val th = append_imm_code |> SPEC tm |> SPEC_ALL
      |> SIMP_RULE std_ss [LENGTH,ADD1,end_of_code_def]
      |> PURE_REWRITE_RULE [append_imm_code_def,word_arith_lemma1]
      |> SIMP_RULE std_ss [GSYM end_of_code_def]
  in th end;
*)

val zHEAP_INSTALL_CODE = let
  val th = ic_full_res
    |> DISCH ``(x4 = BlockList (MAP BlockNum3 code))``
    |> DISCH ``s.code_mode = SOME F``
    |> SIMP_RULE std_ss [ic_full_thm,LET_DEF,SEP_CLAUSES]
    |> GSYM |> SIMP_RULE std_ss []
    |> RW [GSYM SPEC_MOVE_COND] |> GSYM
  val th = SPEC_COMPOSE_RULE [zHEAP_CALL_INSTALL_WITH_STOP_ADDR,
             zHEAP_CODE_UNSAFE,th,
             zHEAP_CODE_SAFE,zHEAP_POP1,
             zHEAP_JMP_CODE_START]
  val th = th |> CONV_RULE (PRE_CONV (SIMP_CONV (srw_ss()) [SEP_CLAUSES,
                   install_x64_code_lists_code_mode]))
  val th = th |> CONV_RULE (POST_CONV (SIMP_CONV (srw_ss()) [SEP_CLAUSES,
                   install_x64_code_lists_code_mode]))
  val th = abbreviate_code "install_and_run" ``cs.install_and_run_ptr`` th
  in th end;


(* --- lexer --- *)

val bool2int_def = Define `
  bool2int b = if b then 1:int else 0`;

val s_with_input = prove(
  ``!s. s = s with input := s.input``,
  Cases_on `s` \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``));

val bool2int_thm = prove(
  ``!b. (bool2int b = 0) <=> ~b``,
  Cases \\ EVAL_TAC);

val DROP_1_CONS = EVAL ``DROP 1 (x::xs)``

(* isSpace *)

val (res,is_space_def,is_space_pre_def) = x64_compile `
  is_space (s:zheap_state) =
    let x1 = Number 1 in
      if HD s.input = CHR 32 then (x1,s) else
      if ~(ORD (HD s.input) < 9) /\ ORD (HD s.input) < 14 then (x1,s) else
        let x1 = Number 0 in (x1,s)`

val is_space_thm = prove(
  ``(is_space_pre s = s.input <> "") /\
    (is_space s = (Number (bool2int (isSpace (HD s.input))), s))``,
  SIMP_TAC std_ss [is_space_def,is_space_pre_def,LET_DEF,isSpace_def]
  \\ Cases_on `HD s.input` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [bool2int_def] \\ intLib.COOPER_TAC);

(* isDigit *)

val (res,is_digit_def,is_digit_pre_def) = x64_compile `
  is_digit (s:zheap_state) =
    if ORD (HD s.input) < 48 then let x1 = Number 0 in (x1,s) else
    if ORD (HD s.input) < 58 then let x1 = Number 1 in (x1,s) else
      let x1 = Number 0 in (x1,s)`

val is_digit_thm = prove(
  ``(is_digit_pre s = s.input <> "") /\
    (is_digit s = (Number (bool2int (isDigit (HD s.input))), s))``,
  SIMP_TAC std_ss [is_digit_def,is_digit_pre_def,LET_DEF,isDigit_def]
  \\ Cases_on `HD s.input` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [bool2int_def] \\ intLib.COOPER_TAC);

(* isAlpha *)

val (res,is_alpha_def,is_alpha_pre_def) = x64_compile `
  is_alpha (s:zheap_state) =
    if ORD (HD s.input) < 65 then let x1 = Number 0 in (x1,s) else
    if ORD (HD s.input) < 91 then let x1 = Number 1 in (x1,s) else
    if ORD (HD s.input) < 97 then let x1 = Number 0 in (x1,s) else
    if ORD (HD s.input) < 123 then let x1 = Number 1 in (x1,s) else
      let x1 = Number 0 in (x1,s)`

val is_alpha_thm = prove(
  ``(is_alpha_pre s = s.input <> "") /\
    (is_alpha s = (Number (bool2int (isAlpha (HD s.input))), s))``,
  SIMP_TAC std_ss [is_alpha_def,is_alpha_pre_def,LET_DEF,
    isAlpha_def,isLower_def,isUpper_def]
  \\ Cases_on `HD s.input` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [bool2int_def] \\ intLib.COOPER_TAC);

(* isAlphaNum *)

val (res,is_alphanum_def,is_alphanum_pre_def) = x64_compile `
  is_alphanum (s:zheap_state) =
    let (x1,s) = is_alpha s in
      if getNumber x1 = 1 then (x1,s) else
        let (x1,s) = is_digit s in (x1,s)`

val is_alphanum_thm = prove(
  ``(is_alphanum_pre s = s.input <> "") /\
    (is_alphanum s = (Number (bool2int (isAlphaNum (HD s.input))), s))``,
  SIMP_TAC std_ss [is_alphanum_def,is_alphanum_pre_def,LET_DEF,
    isAlphaNum_def,is_alpha_thm,is_digit_thm,getNumber_def,isNumber_def]
  \\ SRW_TAC [] [bool2int_def] \\ FULL_SIMP_TAC (srw_ss()) []);

(* isAlphaNumPrime *)

val (res,is_alphanumprime_def,is_alphanumprime_pre_def) = x64_compile `
  is_alphanumprime (s:zheap_state) =
    let x1 = Number 1 in
      if HD s.input = #"'" then (x1,s) else
      if HD s.input = #"_" then (x1,s) else
        let (x1,s) = is_alphanum s in
          (x1,s)`

val is_alphanumprime_thm = prove(
  ``(is_alphanumprime_pre s = s.input <> "") /\
    (is_alphanumprime s = (Number (bool2int (isAlphaNumPrime (HD s.input))), s))``,
  SIMP_TAC std_ss [is_alphanumprime_def,is_alphanumprime_pre_def,LET_DEF,
    isAlphaNumPrime_def,is_alphanum_thm,getNumber_def,isNumber_def]
  \\ SRW_TAC [] [bool2int_def] \\ FULL_SIMP_TAC (srw_ss()) []);

(* isSymbol *)

val (res,is_symbol_def,is_symbol_pre_def) = x64_compile `
  is_symbol (s:zheap_state) =
    let x1 = Number 1 in
      if HD s.input = CHR 96 then (x1,s) else
      if HD s.input = #"!" then (x1,s) else
      if HD s.input = #"%" then (x1,s) else
      if HD s.input = #"&" then (x1,s) else
      if HD s.input = #"$" then (x1,s) else
      if HD s.input = #"#" then (x1,s) else
      if HD s.input = #"+" then (x1,s) else
      if HD s.input = #"-" then (x1,s) else
      if HD s.input = #"/" then (x1,s) else
      if HD s.input = #":" then (x1,s) else
      if HD s.input = #"<" then (x1,s) else
      if HD s.input = #"=" then (x1,s) else
      if HD s.input = #">" then (x1,s) else
      if HD s.input = #"?" then (x1,s) else
      if HD s.input = #"@" then (x1,s) else
      if HD s.input = #"\\" then (x1,s) else
      if HD s.input = #"~" then (x1,s) else
      if HD s.input = CHR 94 then (x1,s) else
      if HD s.input = #"|" then (x1,s) else
      if HD s.input = #"*" then (x1,s) else
        let x1 = Number 0 in (x1,s)`

val is_symbol_thm = prove(
  ``(is_symbol_pre s = s.input <> "") /\
    (is_symbol s = (Number (bool2int (isSymbol (HD s.input))), s))``,
  SIMP_TAC std_ss [is_symbol_def,is_symbol_pre_def,LET_DEF,isSymbol_def]
  \\ SRW_TAC [] [bool2int_def] \\ FULL_SIMP_TAC (srw_ss()) []);

(* is_single_char_symbol *)

val (res,is_single_char_sym_def,is_single_char_sym_pre_def) = x64_compile `
  is_single_char_sym (s:zheap_state) =
    let x1 = Number 1 in
      if HD s.input = #"(" then (x1,s) else
      if HD s.input = #")" then (x1,s) else
      if HD s.input = #"[" then (x1,s) else
      if HD s.input = #"]" then (x1,s) else
      if HD s.input = #"{" then (x1,s) else
      if HD s.input = #"}" then (x1,s) else
      if HD s.input = #"," then (x1,s) else
      if HD s.input = #";" then (x1,s) else
        let x1 = Number 0 in (x1,s)`

val is_single_char_sym_thm = prove(
  ``(is_single_char_sym_pre s = s.input <> "") /\
    (is_single_char_sym s =
       (Number (bool2int (is_single_char_symbol (HD s.input))), s))``,
  SIMP_TAC std_ss [is_single_char_sym_def,is_single_char_sym_pre_def,
    LET_DEF,is_single_char_symbol_def]
  \\ SRW_TAC [] [bool2int_def] \\ FULL_SIMP_TAC (srw_ss()) []);

(* read_while IsAlhpaNumPrime *)

val (res,read_anp_def,read_anp_pre_def) = x64_compile `
  read_anp (s:zheap_state,stack) =
    if s.input = "" then (s,stack) else
      let (x1,s) = is_alphanumprime s in
        if getNumber x1 = 0 then (s,stack) else
          let x1 = Number (&ORD (HD s.input)) in
          let stack = x1::stack in
          let s = s with input := DROP 1 s.input in
            read_anp (s,stack)`

val read_anp_thm = prove(
  ``!xs s stack.
      (read_anp_pre (s,MAP Chr xs ++ stack) = T) /\
      (read_anp (s,MAP Chr xs ++ stack) =
        let (text,rest) = read_while isAlphaNumPrime s.input xs in
          (s with input := rest, MAP Chr (REVERSE text) ++ stack))``,
  Induct_on `s.input` \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [read_anp_def,read_anp_pre_def]
  THEN1 (FULL_SIMP_TAC std_ss [read_while_def,LET_DEF,s_with_input,
      stringTheory.IMPLODE_EXPLODE_I,REVERSE_REVERSE] \\ Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``))
  \\ NTAC 5 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,is_alphanumprime_thm,LET_DEF,
       getNumber_def,isNumber_def,HD,TL,bool2int_thm,read_while_def,DROP_1_CONS]
  \\ REVERSE (Cases_on `isAlphaNumPrime h`) \\ FULL_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC std_ss [read_while_def,LET_DEF,s_with_input,
      stringTheory.IMPLODE_EXPLODE_I,REVERSE_REVERSE] \\ Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``))
  \\ FULL_SIMP_TAC std_ss [EVAL ``bool2int T < 0``]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := v`)
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`h::xs`,`stack`])
  \\ FULL_SIMP_TAC (srw_ss()) [Chr_def]);

(* read_while IsSymbol *)

val (res,read_sym_def,read_sym_pre_def) = x64_compile `
  read_sym (s:zheap_state,stack) =
    if s.input = "" then (s,stack) else
      let (x1,s) = is_symbol s in
        if getNumber x1 = 0 then (s,stack) else
          let x1 = Number (&ORD (HD s.input)) in
          let stack = x1::stack in
          let s = s with input := DROP 1 s.input in
            read_sym (s,stack)`

val read_sym_thm = prove(
  ``!xs s stack.
      (read_sym_pre (s,MAP Chr xs ++ stack) = T) /\
      (read_sym (s,MAP Chr xs ++ stack) =
        let (text,rest) = read_while isSymbol s.input xs in
          (s with input := rest, MAP Chr (REVERSE text) ++ stack))``,
  Induct_on `s.input` \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [read_sym_def,read_sym_pre_def]
  THEN1 (FULL_SIMP_TAC std_ss [read_while_def,LET_DEF,s_with_input,
      stringTheory.IMPLODE_EXPLODE_I,REVERSE_REVERSE] \\ Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``))
  \\ NTAC 5 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,is_symbol_thm,LET_DEF,
       getNumber_def,isNumber_def,HD,TL,bool2int_thm,read_while_def,DROP_1_CONS]
  \\ REVERSE (Cases_on `isSymbol h`) \\ FULL_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC std_ss [read_while_def,LET_DEF,s_with_input,
      stringTheory.IMPLODE_EXPLODE_I,REVERSE_REVERSE] \\ Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``))
  \\ FULL_SIMP_TAC std_ss [EVAL ``bool2int T < 0``]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := v`)
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`h::xs`,`stack`])
  \\ FULL_SIMP_TAC (srw_ss()) [Chr_def]);

(* skip_comment *)

val (res,skip_com_def,skip_com_pre_def) = x64_compile `
  skip_com (x1:bc_value,x2:bc_value,s:zheap_state) =
    if s.input = "" then (x1,x2,s)
    else if HD s.input = #"(" then
           let s = s with input := DROP 1 s.input in
             if s.input = "" then (x1,x2,s) else
             if HD s.input <> #"*" then skip_com (x1,x2,s) else
               let x1 = any_add x1 x2 in
               let s = s with input := DROP 1 s.input in
                 skip_com (x1,x2,s)
    else if HD s.input = #"*" then
           let s = s with input := DROP 1 s.input in
             if s.input = "" then (x1,x2,s) else
             if HD s.input <> #")" then skip_com (x1,x2,s) else
               let s = s with input := DROP 1 s.input in
               if getNumber x1 = 0 then
                 let x2 = Number 0 in
                   (x1,x2,s)
               else
                 let x1 = any_sub x1 x2 in
                   skip_com (x1,x2,s)
    else let s = s with input := DROP 1 s.input in
           skip_com (x1,x2,s)`

val skip_com_thm = prove(
  ``!s d. 0 <= d ==>
      ?d'.
        skip_com_pre (Number d,Number 1,s) /\
        (skip_com (Number d,Number 1,s) =
          case skip_comment s.input d of
            NONE => (d',Number 1,s with input := "")
          | SOME rest => (Number 0,Number 0,s with input := rest))``,
  completeInduct_on `LENGTH s.input`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `s.input`
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ ONCE_REWRITE_TAC [skip_com_def,skip_com_pre_def]
  \\ SIMP_TAC std_ss [skip_comment_def]
  THEN1 (Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``))
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF] \\ Cases_on `t` THEN1
   (FULL_SIMP_TAC (srw_ss()) [LET_DEF,skip_comment_def]
    \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [skip_com_def,skip_com_pre_def]
    \\ SIMP_TAC std_ss [skip_comment_def]
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,skip_comment_def])
  \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,HD,TL,any_add_def,any_sub_def,getNumber_def]
  \\ SIMP_TAC std_ss [Once skip_comment_def]
  \\ FULL_SIMP_TAC (srw_ss()) [isNumber_def]
  \\ Q.MATCH_ASSUM_RENAME_TAC `s.input = STRING x1 (STRING x2 rest)` []
  \\ Cases_on `x1 = #"("` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Cases_on `x2 = #"*"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
     (FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := rest`)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `(d+1)`)
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `0 <= d + 1` by intLib.COOPER_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `d''` \\ FULL_SIMP_TAC std_ss [])
    THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := x2 :: rest`)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `d`)))
  \\ Cases_on `x1 = #"*"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (REVERSE (Cases_on `x2 = #")"`) \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := x2 :: rest`)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `d`))
    \\ Cases_on `d = 0` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := rest`)
      \\ FULL_SIMP_TAC (srw_ss()) []
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `(d-1)`)
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `0 <= d - 1 /\ ~(d < 0)` by intLib.COOPER_TAC \\ FULL_SIMP_TAC std_ss []
      \\ Q.EXISTS_TAC `d''` \\ FULL_SIMP_TAC std_ss []))
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s with input := x2 :: rest`)
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `d`)
  \\ FULL_SIMP_TAC (srw_ss()) [])

(* read_string *)

val (res,read_str_def,read_str_pre_def) = x64_compile `
  read_str (x2:bc_value,s:zheap_state,stack) =
    if s.input = "" then
      (x2:bc_value,s,stack) (* error *)
    else if HD s.input = #"\"" then
      let s = s with input := DROP 1 s.input in
      let x2 = Number 1 in (x2,s,stack) (* success *)
    else if HD s.input = #"\n" then
      let s = s with input := DROP 1 s.input in
        (x2,s,stack) (* error *)
    else if HD s.input <> #"\\" then
      let x1 = Number (&ORD (HD s.input)) in
      let stack = x1::stack in
      let s = s with input := DROP 1 s.input in
        read_str (x2,s,stack)
    else
      let s = s with input := DROP 1 s.input in
        if s.input = "" then
          (x2:bc_value,s,stack) (* error *)
        else if HD s.input = #"\\" then
          let x1 = Number (&ORD (HD s.input)) in
          let stack = x1::stack in
          let s = s with input := DROP 1 s.input in
            read_str (x2,s,stack)
        else if HD s.input = #"\"" then
          let x1 = Number (&ORD (HD s.input)) in
          let stack = x1::stack in
          let s = s with input := DROP 1 s.input in
            read_str (x2,s,stack)
        else if HD s.input = #"n" then
          let x1 = Number 10 in
          let stack = x1::stack in
          let s = s with input := DROP 1 s.input in
            read_str (x2,s,stack)
        else if HD s.input = #"t" then
          let x1 = Number 9 in
          let stack = x1::stack in
          let s = s with input := DROP 1 s.input in
            read_str (x2,s,stack)
        else
          (x2:bc_value,s,stack) (* error *)`

val read_str_thm = prove(
  ``!xs s stack.
      ?ts.
        read_str_pre (Number 0,s,MAP Chr (REVERSE xs) ++ stack) /\
        (read_str (Number 0,s,MAP Chr (REVERSE xs) ++ stack) =
           case read_string s.input xs of
           | (StringS text, rest) =>
               (Number 1,s with input := rest, MAP Chr (REVERSE text) ++ stack)
           | (_, rest) =>
               (Number 0,s with input := rest, MAP Chr (REVERSE ts) ++ stack))``,
  completeInduct_on `LENGTH s.input`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `s.input`
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ ONCE_REWRITE_TAC [read_str_def,read_str_pre_def]
  \\ SIMP_TAC std_ss [Once read_string_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN1 (Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``)
    \\ Q.EXISTS_TAC `xs` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `h = #"\""` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `h = #"\n"` \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (Q.EXISTS_TAC `xs` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ REVERSE (Cases_on `h = #"\\"`) \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s with input := t`,`xs ++ [h]`,`stack`])
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [Chr_def,REVERSE_APPEND,rich_listTheory.REVERSE]
    \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND,MAP,Chr_def]
    \\ Q.EXISTS_TAC `ts` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1 METIS_TAC []
  \\ Q.MATCH_ASSUM_RENAME_TAC `s.input = STRING #"\\" (STRING c rest)` []
  \\ Cases_on `c = #"\\"` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `c = #"\""` \\ FULL_SIMP_TAC (srw_ss()) []
  THEN TRY
   (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s with input := rest`,`xs ++ [c]`,`stack`])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [Chr_def,REVERSE_APPEND,rich_listTheory.REVERSE]
    \\ FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND,APPEND,MAP,Chr_def]
    \\ Q.EXISTS_TAC `ts` \\ FULL_SIMP_TAC std_ss [] \\ NO_TAC)
  \\ Cases_on `c = #"n"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s with input := rest`,`xs ++ [#"\n"]`,`stack`])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [Chr_def,REVERSE_APPEND,rich_listTheory.REVERSE]
    \\ FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND,APPEND,MAP,Chr_def]
    \\ Q.EXISTS_TAC `ts` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `c = #"t"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s with input := rest`,`xs ++ [#"\t"]`,`stack`])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [Chr_def,REVERSE_APPEND,rich_listTheory.REVERSE]
    \\ FULL_SIMP_TAC (srw_ss()) [SNOC_APPEND,APPEND,MAP,Chr_def]
    \\ Q.EXISTS_TAC `ts` \\ FULL_SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `xs` \\ FULL_SIMP_TAC std_ss [])

(* read number *)

val (res,read_num_def,read_num_pre_def) = x64_compile `
  read_num (x1:bc_value,x2:bc_value,s:zheap_state) =
    if s.input = "" then (x1,x2,s) else
    let (x1,s) = is_digit s in
    if getNumber x1 = 0 then (x1,x2,s) else
      let x1 = Number 10 in
      let x1 = any_mul x1 x2 in
      let x2 = x1 in
      let x1 = Number (&(ORD (HD s.input) - 48)) in
      let x1 = any_add x1 x2 in
      let x2 = x1 in
      let s = s with input := DROP 1 s.input in
        read_num (x1,x2,s)`

val l2n_n = prove(
  ``!n b. n < b ==> !ls. l2n b (ls ++ [n]) = l2n b ls + b ** (LENGTH ls) * n``,
  NTAC 2 GEN_TAC THEN STRIP_TAC THEN
  Induct THEN EVAL_TAC THEN SRW_TAC[ARITH_ss][ADD1] THEN
  SRW_TAC[ARITH_ss][LEFT_ADD_DISTRIB,GSYM ADD1,EXP])

val toNum_CONS = prove(
  ``isDigit h ==>
    (toNum (STRING h digits) =
     toNum digits + 10 ** STRLEN digits * (ORD h - 48))``,
  Cases_on`h`\\
  REPEAT (
  Cases_on`n`\\ EVAL_TAC \\ Cases_on`n'`\\EVAL_TAC \\
  FULL_SIMP_TAC (srw_ss()++ARITH_ss)[ADD1] ) THEN
  REPEAT (
  (Cases_on`n` ORELSE Cases_on`n'`)\\ EVAL_TAC \\
  FULL_SIMP_TAC (srw_ss()++ARITH_ss)[ADD1] THEN1 (
    Q.PAT_ABBREV_TAC`d = [x:char]` \\
    Q.ISPECL_THEN[`digits`,`d`]MP_TAC REV_REVERSE_LEM \\
    SRW_TAC[][Abbr`d`] \\ EVAL_TAC \\ SRW_TAC[ARITH_ss][l2n_n,GSYM REVERSE_REV] )));

val read_num_thm = prove(
  ``!digits k s x1.
      EVERY isDigit digits /\ ((rest <> []) ==> ~isDigit (HD rest)) ==>
      ?x1'.
        read_num_pre (x1,Number (& k),s with input := digits ++ rest) /\
        (read_num (x1,Number (& k),s with input := digits ++ rest) =
           (x1',Number (& (toNum digits + 10 ** (LENGTH digits) * k)),
            s with input := rest))``,
  Induct
  \\ SIMP_TAC (srw_ss()) [Once read_num_def,Once read_num_pre_def,LET_DEF] THEN1
   (Cases_on `rest` \\ FULL_SIMP_TAC (srw_ss()) [is_digit_thm,getNumber_def,
      bool2int_thm,any_mul_def,any_add_def,any_sub_def,isNumber_def])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [is_digit_thm,getNumber_def]
  \\ FULL_SIMP_TAC (srw_ss()) [is_digit_thm,getNumber_def,isNumber_def,
      bool2int_thm,any_mul_def,any_add_def,any_sub_def,isDigit_def]
  \\ `(& (ORD h)) - 48 = & (ORD h - 48)` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [integerTheory.INT_SUB]
  \\ FULL_SIMP_TAC std_ss [integerTheory.INT_ADD]
  \\ SEP_I_TAC "read_num" \\ FULL_SIMP_TAC (srw_ss()) [EXP]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,toNum_CONS,isDigit_def]
  \\ FULL_SIMP_TAC std_ss [EVAL ``bool2int T < 0``]
  \\ FULL_SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC, AC ADD_ASSOC ADD_COMM]);

(* next symbol *)

val (res,next_symbol_def,next_symbol_pre_def) = x64_compile `
  next_symbol (x1:bc_value,x2:bc_value,s:zheap_state,stack) =
    let stack = x1 :: stack in
    let stack = x2 :: stack in
    let (x1,stack) = (HD stack, TL stack) in
    let (x2,stack) = (HD stack, TL stack) in
    if s.input = "" then
      let x2 = Number 2 in let x1 = x2 in (x1,x2,s,stack)
    else
    let (x1,s) = is_space s in
    if getNumber x1 <> 0 then
      let s = s with input := DROP 1 s.input in
        next_symbol (x1,x2,s:zheap_state,stack)
    else if HD s.input = #"\"" then
      let s = s with input := DROP 1 s.input in
      let x2 = Number 0 in
      let (x2,s,stack) = read_str (x2,s,stack) in
      let x1 = x2 in
        (x1,x2,s,stack)
    else
    let (x1,s) = is_digit s in
    if getNumber x1 <> 0 then
      let x1 = Number 0 in
      let x2 = x1 in
      let (x1,x2,s) = read_num (x1,x2,s) in
      let stack = x2::stack in
      let x2 = Number 3 in
      let x1 = x2 in
        (x1,x2,s,stack)
    else if HD s.input = #"'" then
      let (s,stack) = read_anp (s,stack) in
      let x2 = Number 4 in
      let x1 = x2 in
        (x1,x2,s,stack)
    else if HD s.input = #"~" then
      let s = s with input := DROP 1 s.input in
      if s.input = "" then
        let x1 = Number 126 in
        let stack = x1 :: stack in
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else
      let (x1,s) = is_digit s in
      if getNumber x1 <> 0 then
        let x1 = Number 0 in
        let x2 = x1 in
        let (x1,x2,s) = read_num (x1,x2,s) in
        let x1 = Number 0 in
        let x1 = any_sub x1 x2 in
        let stack = x1::stack in
        let x2 = Number 3 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else (* store symbol *)
        let x1 = Number 126 in
        let stack = x1 :: stack in
        let (s,stack) = read_sym (s,stack) in
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
    else if HD s.input = #"*" then
      let s = s with input := DROP 1 s.input in
      if s.input = "" then
        let x1 = Number 42 in
        let stack = x1 :: stack in
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else if HD s.input = #")" then
        let s = s with input := DROP 1 s.input in
        let x2 = Number 0 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else
        let x1 = Number 42 in
        let stack = x1 :: stack in
        let (s,stack) = read_sym (s,stack) in
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
    else if HD s.input = #"(" then
      let s = s with input := DROP 1 s.input in
      if s.input = "" then
        let x1 = Number 40 in
        let stack = x1 :: stack in
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else if HD s.input = #"*" then
        let s = s with input := DROP 1 s.input in
        let x1 = Number 0 in
        let x2 = Number 1 in
        let (x1,x2,s) = skip_com (x1,x2,s) in
          if getNumber x2 = 0 then next_symbol (x1,x2,s:zheap_state,stack) else
            let x2 = Number 0 in
            let x1 = x2 in
              (x1,x2,s,stack)
      else
        let x1 = Number 40 in
        let stack = x1 :: stack in
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
    else
    let (x1,s) = is_single_char_sym s in
    if getNumber x1 <> 0 then
      let x1 = Number (&ORD (HD s.input)) in
      let stack = x1::stack in
      let s = s with input := DROP 1 s.input in
      let x2 = Number 4 in
      let x1 = x2 in
        (x1,x2,s,stack)
    else
    let (x1,s) = is_symbol s in
    if getNumber x1 <> 0 then
      let (s,stack) = read_sym (s,stack) in
      let x2 = Number 4 in
      let x1 = x2 in
        (x1,x2,s,stack)
    else if HD s.input = #"_" then
      let x1 = Number (&ORD (HD s.input)) in
      let stack = x1::stack in
      let s = s with input := DROP 1 s.input in
      let x2 = Number 4 in
      let x1 = x2 in
        (x1,x2,s,stack)
    else
    let (x1,s) = is_alpha s in
    if getNumber x1 = 0 then
      let s = s with input := DROP 1 s.input in
      let x2 = Number 0 in
      let x1 = x2 in
        (x1,x2,s,stack)
    else
      let (s,stack) = read_anp (s,stack) in
      if s.input = "" then
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else if HD (s.input) <> #"." then
        let x2 = Number 4 in
        let x1 = x2 in
          (x1,x2,s,stack)
      else
        let x1 = Number (&ORD (HD s.input)) in
        let stack = x1::stack in
        let s = s with input := DROP 1 s.input in
        if s.input = "" then
          let x2 = Number 0 in
          let x1 = x2 in
            (x1,x2,s,stack)
        else
        let (x1,s) = is_alpha s in
        if getNumber x1 <> 0 then
          let (s,stack) = read_anp (s,stack) in
          let x2 = Number 5 in
          let x1 = x2 in
            (x1,x2,s,stack)
        else
        let (x1,s) = is_symbol s in
        if getNumber x1 <> 0 then
          let (s,stack) = read_sym (s,stack) in
          let x2 = Number 5 in
          let x1 = x2 in
            (x1,x2,s,stack)
        else
          let s = s with input := DROP 1 s.input in
          let x2 = Number 0 in
          let x1 = x2 in
            (x1,x2,s,stack)`

val read_string_IMP = prove(
  ``!v x. (read_string v x = (res,r)) ==>
          (res = ErrorS) \/ ?s. res = StringS s``,
  HO_MATCH_MP_TAC read_string_ind
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [read_string_def]
  \\ SRW_TAC [] []
  \\ Cases_on `v`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC [PAIR_EQ]);

val LIST_PREFIX_PROP = prove(
  ``!xs P. ?xs1 xs2.
             EVERY P xs1 /\ (xs2 <> "" ==> ~P (HD xs2)) /\
             (xs = xs1 ++ xs2)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ Cases_on `P h` THEN1
   (FIRST_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `P`)
    \\ Q.LIST_EXISTS_TAC [`h::xs1`,`xs2`]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.EXISTS_TAC `[]` \\ Q.EXISTS_TAC `h::xs`
  \\ FULL_SIMP_TAC (srw_ss()) []);

val read_while_lemma = prove(
  ``!xs ys P.
      read_while P xs ys =
        let (zs,rest) = read_while P xs [] in (REVERSE ys ++ zs,rest)``,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [read_while_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `P h` \\ POP_ASSUM MP_TAC \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ SIMP_TAC std_ss [stringTheory.IMPLODE_EXPLODE_I]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ Cases_on `read_while P xs ""` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ SIMP_TAC (srw_ss()) [APPEND_NIL]);

val read_while_APPEND = prove(
  ``!xs res ys.
      EVERY P xs /\ (ys <> "" ==> ~(P (HD ys))) ==>
       (read_while P (xs ++ ys) res = (REVERSE res ++ xs, ys))``,
  Induct THEN1
   (Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ ONCE_REWRITE_TAC [read_while_def]
    \\ SIMP_TAC (srw_ss()) [stringTheory.IMPLODE_EXPLODE_I])
  \\ SIMP_TAC std_ss [APPEND] \\ ONCE_REWRITE_TAC [read_while_def]
  \\ FULL_SIMP_TAC (srw_ss()) []);

val LENGTH_skip_comment = prove(
  ``!d rest. (skip_comment xs d = SOME rest) ==> LENGTH rest <= LENGTH xs``,
  completeInduct_on `LENGTH xs` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ POP_ASSUM MP_TAC
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once skip_comment_def]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once skip_comment_def]
  \\ FULL_SIMP_TAC (srw_ss()) [AND_IMP_INTRO]
  \\ SRW_TAC [] [] \\ RES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val next_symbol_thm = prove(
  ``!xs s stack x1 x2.
      ?ts.
       next_symbol_pre (x1,x2,s,stack) /\
       (next_symbol (x1,x2,s,stack) =
        case next_sym s.input of
        | NONE => (Number 2,Number 2, s with input := "", stack)
        | SOME (StringS text, rest) =>
          (Number 1,Number 1,s with input := rest, MAP Chr (REVERSE text) ++ stack)
        | SOME (OtherS text, rest) =>
          (Number 4,Number 4,s with input := rest, MAP Chr (REVERSE text) ++ stack)
        | SOME (LongS text, rest) =>
          (Number 5,Number 5,s with input := rest, MAP Chr (REVERSE text) ++ stack)
        | SOME (ErrorS, rest) =>
          (Number 0,Number 0,s with input := rest, MAP Chr (REVERSE ts) ++ stack)
        | SOME (NumberS n, rest) =>
          (Number 3,Number 3,s with input := rest, Number n :: stack))``,
  completeInduct_on `LENGTH s.input` \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ Cases_on `s.input`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [next_sym_def,next_symbol_def,next_symbol_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,HD,TL] THEN1 (Cases_on `s`
    \\ FULL_SIMP_TAC (srw_ss()) (TypeBase.updates_of ``:zheap_state``))
  \\ Q.MATCH_ASSUM_RENAME_TAC `s.input = STRING h v` []
  \\ FULL_SIMP_TAC std_ss [is_symbol_thm,is_space_thm,is_alpha_thm,
       is_digit_thm,getNumber_def,is_single_char_sym_thm,HD,TL]
  \\ FULL_SIMP_TAC std_ss [bool2int_thm]
  \\ Cases_on `isSpace h` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC std_ss [PULL_FORALL] \\ SEP_I_TAC "next_symbol"
    \\ FULL_SIMP_TAC (srw_ss()) [isNumber_def,EVAL ``bool2int T < 0``]
    \\ Q.EXISTS_TAC `ts` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `h = #"\""` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [isDigit_def]
    \\ ASSUME_TAC (read_str_thm |> Q.SPEC `[]` |> RW [MAP,APPEND,REVERSE_DEF])
    \\ SEP_I_TAC "read_str" \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `read_string v ""` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC read_string_IMP
    \\ FULL_SIMP_TAC (srw_ss()) [isNumber_def] \\ METIS_TAC [])
  \\ Cases_on `isDigit h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (STRIP_ASSUME_TAC (LIST_PREFIX_PROP |> Q.SPECL [`h::v`,`isDigit`])
    \\ FULL_SIMP_TAC std_ss []
    \\ `s = s with input := s.input` by FULL_SIMP_TAC std_ss [s_with_input]
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ FULL_SIMP_TAC std_ss []
    \\ ASSUME_TAC (GEN_ALL read_num_thm)
    \\ SEP_I_TAC "read_num"
    \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [isNumber_def,EVAL ``bool2int T < 0``]
    \\ Cases_on `xs1` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 (Cases_on `xs2` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC (srw_ss()) [read_while_APPEND])
  \\ Cases_on `h = #"'"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (ASM_SIMP_TAC std_ss [read_anp_thm |> Q.SPEC `[]` |> RW [MAP,APPEND]]
    \\ SIMP_TAC std_ss [read_while_def,EVAL ``isAlphaNumPrime #"'"``]
    \\ Cases_on `read_while isAlphaNumPrime v "'"`
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,isNumber_def])
  \\ Cases_on `h = #"~"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Cases_on `v = ""` \\ FULL_SIMP_TAC std_ss []
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [] \\ SRW_TAC[][read_while_def] \\ EVAL_TAC)
    \\ Cases_on `isDigit (HD v)` \\ FULL_SIMP_TAC std_ss [] THEN1
     (STRIP_ASSUME_TAC (LIST_PREFIX_PROP |> Q.SPECL [`v`,`isDigit`])
      \\ FULL_SIMP_TAC std_ss []
      \\ ASSUME_TAC (GEN_ALL read_num_thm)
      \\ SEP_I_TAC "read_num"
      \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [EVAL ``bool2int T < 0``]
      \\ FULL_SIMP_TAC (srw_ss()) [read_while_APPEND,isNumber_def]
      \\ FULL_SIMP_TAC std_ss [any_sub_def,getNumber_def]
      \\ AP_TERM_TAC \\ intLib.COOPER_TAC)
    \\ SIMP_TAC std_ss [EVAL ``is_single_char_symbol #"~"``]
    \\ SIMP_TAC std_ss [EVAL ``isSymbol #"~"``]
    \\ ASSUME_TAC (read_sym_thm |> Q.SPEC `[]` |> RW [MAP,APPEND,REVERSE_DEF])
    \\ SEP_I_TAC "read_sym" \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,isNumber_def] \\ STRIP_TAC
    \\ Cases_on `read_while isSymbol v ""`
    \\ ONCE_REWRITE_TAC [read_while_lemma]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,EVAL ``REVERSE [x]``]
    \\ SIMP_TAC (srw_ss()) [Chr_def])
  \\ Cases_on `h = #"*"` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [EVAL ``is_single_char_symbol #"*"``]
    \\ SIMP_TAC std_ss [EVAL ``isSymbol #"*"``,isNumber_def]
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [] \\ SRW_TAC[][read_while_def] \\ EVAL_TAC)
    \\ Q.MATCH_ASSUM_RENAME_TAC `s.input = STRING #"*" (STRING x xs)` []
    \\ Cases_on `x = #")"` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FULL_SIMP_TAC (srw_ss()) [])
    \\ ASSUME_TAC (read_sym_thm |> Q.SPEC `[]` |> RW [MAP,APPEND,REVERSE_DEF])
    \\ SEP_I_TAC "read_sym" \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF] \\ STRIP_TAC
    \\ Cases_on `read_while isSymbol (x::xs) ""`
    \\ ONCE_REWRITE_TAC [read_while_lemma]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,EVAL ``REVERSE [x]``]
    \\ SIMP_TAC (srw_ss()) [Chr_def])
  \\ Cases_on `h = #"("` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ Q.MATCH_ASSUM_RENAME_TAC `s.input = STRING #"(" (STRING x xs)` []
    \\ REVERSE (Cases_on `x = #"*"`) \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ ASSUME_TAC skip_com_thm
    \\ SEP_I_TAC "skip_com"
    \\ Cases_on `skip_comment xs 0`
    \\ FULL_SIMP_TAC (srw_ss()) [getNumber_def,isNumber_def]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ Q.MATCH_ASSUM_RENAME_TAC `skip_comment xs 0 = SOME rest` []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
         [`s with input := rest`,`stack`,`Number 0`,`Number 0`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) []
      \\ IMP_RES_TAC LENGTH_skip_comment \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `ts` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `is_single_char_symbol h`
  \\ FULL_SIMP_TAC (srw_ss()) [Chr_def,isNumber_def,EVAL ``bool2int T < 0``]
  \\ Cases_on `isSymbol h` \\ FULL_SIMP_TAC (srw_ss()) [Chr_def] THEN1
   (ASSUME_TAC (read_sym_thm |> Q.SPEC `[]` |> RW [MAP,APPEND,REVERSE_DEF])
    \\ SEP_I_TAC "read_sym" \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,isNumber_def] \\ STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [read_while_def]
    \\ Cases_on `read_while isSymbol v [h]`
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `h = #"_"` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC std_ss [EVAL ``isAlpha #"_"``]
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ REVERSE (Cases_on `isAlpha h`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC std_ss [read_anp_thm |> Q.SPEC `[]` |> RW [MAP,APPEND,REVERSE_DEF]]
  \\ FULL_SIMP_TAC std_ss []
  \\ `isAlphaNumPrime h` by
       FULL_SIMP_TAC std_ss [isAlphaNumPrime_def,isAlphaNum_def]
  \\ ASM_SIMP_TAC std_ss [read_while_def]
  \\ Cases_on `(read_while isAlphaNumPrime v (STRING h ""))`
  \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,isNumber_def]
  \\ Q.MATCH_ASSUM_RENAME_TAC
      `read_while isAlphaNumPrime v (STRING h "") = (q,STRING h1 rest)` []
  \\ REVERSE (Cases_on `h1 = #"."`) THEN1 FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ Cases_on `rest` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  THEN1 (Q.EXISTS_TAC `q ++ [CHR 46]` \\ FULL_SIMP_TAC (srw_ss()) [Chr_def])
  \\ Cases_on `isAlpha h'` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (`isAlphaNumPrime h'` by
       FULL_SIMP_TAC std_ss [isAlphaNumPrime_def,isAlphaNum_def]
    \\ ASM_SIMP_TAC std_ss [read_while_def,isNumber_def]
    \\ Cases_on `read_while isAlphaNumPrime t (STRING h' "")`
    \\ FULL_SIMP_TAC (srw_ss()) [Chr_def])
  \\ SIMP_TAC std_ss [read_sym_thm |> Q.SPEC `[]` |> RW [MAP,APPEND,REVERSE_DEF]]
  \\ Cases_on `isSymbol h'` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (ASM_SIMP_TAC std_ss [read_while_def,LET_DEF,isNumber_def]
    \\ Cases_on `(read_while isSymbol t (STRING h' ""))`
    \\ FULL_SIMP_TAC (srw_ss()) [Chr_def])
  THEN1 (Q.EXISTS_TAC `q ++ [CHR 46]` \\ FULL_SIMP_TAC (srw_ss()) [Chr_def]))
  |> SIMP_RULE std_ss [];

(* cons list *)

val (res,cons_list_aux_def,cons_list_aux_pre_def) = x64_compile `
  cons_list_aux (x1,x2:bc_value,stack) =
    let x2 = x1 in
    let (x1,stack) = (HD stack, TL stack) in
      if isBlock x1 then (x1,x2,stack) else
        let x1 = BlockCons (x1,x2) in
          cons_list_aux (x1,x2,stack)`

val (res,cons_list_def,cons_list_pre_def) = x64_compile `
  cons_list (stack) =
    let x1 = BlockNil in
    let x2 = BlockNil in
    let (x1,x2,stack) = cons_list_aux (x1,x2,stack) in
      (x1,x2,stack)`

val cons_list_aux_thm = prove(
  ``!xs ys x2.
      cons_list_aux_pre (BlockList ys,x2,MAP Chr xs ++ BlockNil::stack) /\
      (cons_list_aux (BlockList ys,x2,MAP Chr xs ++ BlockNil::stack) =
         (BlockNil,BlockList (MAP Chr (REVERSE xs) ++ ys),stack))``,
  Induct \\ ONCE_REWRITE_TAC [cons_list_aux_def,cons_list_aux_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,EVAL ``isBlock BlockNil``]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,EVAL ``isBlock (Chr c)``]
  \\ SIMP_TAC std_ss [Once (GSYM BlockList_def)]
  \\ ASM_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ SIMP_TAC std_ss [Once (GSYM BlockList_def)]
  \\ ASM_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ EVAL_TAC \\ SIMP_TAC std_ss []) |> Q.SPECL [`xs`,`[]`]
  |> SIMP_RULE std_ss [BlockList_def,APPEND_NIL];

val cons_list_thm = prove(
  ``cons_list_pre (MAP Chr xs ++ BlockNil::stack) /\
    (cons_list (MAP Chr xs ++ BlockNil::stack) =
       (BlockNil,BlockList (MAP Chr (REVERSE xs)),stack))``,
  SIMP_TAC std_ss [cons_list_def,cons_list_pre_def,cons_list_aux_thm,LET_DEF]);

(* semi_sym *)

val semi_sym_def = Define `
  (semi_sym (OtherS s) =
    if s = ";" then Number 1 else
    if MEM s ["let";"struct";"sig";"("] then Number 2 else
    if MEM s [")";"end"] then Number 3 else Number 0) /\
  (semi_sym _ = Number 0)`;

val (res,semi_len_def,semi_len_pre_def) = x64_compile `
  semi_len (stack:bc_value list) =
    let x1 = HD stack in
    if isBlock x1 then let x1 = Number 0 in (x1,stack) else
    let x1 = EL 1 stack in
    if isBlock x1 then let x1 = Number 1 in (x1,stack) else
    let x1 = EL 2 stack in
    if isBlock x1 then let x1 = Number 2 in (x1,stack) else
    let x1 = EL 3 stack in
    if isBlock x1 then let x1 = Number 3 in (x1,stack) else
    let x1 = EL 4 stack in
    if isBlock x1 then let x1 = Number 4 in (x1,stack) else
    let x1 = EL 5 stack in
    if isBlock x1 then let x1 = Number 5 in (x1,stack) else
    let x1 = EL 6 stack in
    if isBlock x1 then let x1 = Number 6 in (x1,stack) else
      let x1 = Number 7 in (x1,stack)`

val LIST_CASES = prove(
  ``!xs. (xs = []:string) \/
         (?x1. xs = [x1]) \/
         (?x1 x2. xs = [x1;x2]) \/
         (?x1 x2 x3. xs = [x1;x2;x3]) \/
         (?x1 x2 x3 x4. xs = [x1;x2;x3;x4]) \/
         (?x1 x2 x3 x4 x5. xs = [x1;x2;x3;x4;x5]) \/
         (?x1 x2 x3 x4 x5 x6. xs = [x1;x2;x3;x4;x5;x6]) \/
         (?x1 x2 x3 x4 x5 x6 x7 ts. xs = x1::x2::x3::x4::x5::x6::x7::ts)``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT (Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []
             \\ Cases_on `t'` \\ FULL_SIMP_TAC (srw_ss()) []));

val APPEND_LEMMA = prove(
  ``(xs ++ ys ++ zs ++ qs = xs ++ (ys ++ zs) ++ qs:'a list) /\
    ([Chr c] = MAP Chr [c]) /\
    (Chr c :: MAP Chr cs = MAP Chr (c::cs))``,
  SIMP_TAC std_ss [APPEND_ASSOC,MAP]);

val semi_len_thm = prove(
  ``semi_len_pre (MAP Chr (REVERSE xs) ++ BlockNil::stack) /\
    (semi_len (MAP Chr (REVERSE xs) ++ BlockNil::stack) =
      (if LENGTH xs < 7 then Number (& (LENGTH xs))
       else Number 7,MAP Chr (REVERSE xs) ++ BlockNil::stack))``,
  SIMP_TAC std_ss [semi_len_def,semi_len_pre_def,LET_DEF]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ ASM_SIMP_TAC (srw_ss()) [Chr_def,getNumber_def,isBlock_def,
        BlockNil_def,canCompare_def,isNumber_def,ADD1,APPEND,GSYM ORD_11]
  \\ NTAC 4 (TRY (Cases_on `t`) \\ TRY (Cases_on `t'`)
      \\ ASM_SIMP_TAC (srw_ss()) [Chr_def,getNumber_def,isBlock_def,
           BlockNil_def,canCompare_def,isNumber_def,ADD1,APPEND,GSYM ORD_11]
      THEN1 DECIDE_TAC) THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM ADD_ASSOC,APPEND_LEMMA,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM Chr_def,APPEND_LEMMA]
  \\ (LIST_CASES |> Q.SPEC `REVERSE t` |> STRIP_ASSUME_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC \\ SRW_TAC [] [] \\ DECIDE_TAC);

val (res,semi_symbol_def,semi_symbol_pre_def) = x64_compile `
  semi_symbol (stack:bc_value list) =
    let x3 = Number 0 in
    let (x1,stack) = semi_len stack in
    if getNumber x1 = 0 then (x3,stack) else
    if getNumber x1 = 1 then
      let x1 = HD stack in
        if getNumber x1 = 59 (* ; *) then let x3 = Number 1 in (x3,stack) else
        if getNumber x1 = 40 (* ( *) then let x3 = Number 2 in (x3,stack) else
        if getNumber x1 = 41 (* ) *)then let x3 = Number 3 in (x3,stack) else
          (x3,stack) else
    if getNumber x1 = 2 then (x3,stack) else
    if getNumber x1 = 3 then
      let x1 = HD stack in
      if getNumber x1 = 116 (* t *) then
        let x1 = EL 1 stack in if getNumber x1 <> 101 (* e *) then (x3,stack) else
        let x1 = EL 2 stack in if getNumber x1 <> 108 (* l *) then (x3,stack) else
        let x3 = Number 2 in
          (x3,stack)
      else if getNumber x1 = 103 (* g *) then
        let x1 = EL 1 stack in if getNumber x1 <> 105 (* i *) then (x3,stack) else
        let x1 = EL 2 stack in if getNumber x1 <> 115 (* s *) then (x3,stack) else
        let x3 = Number 2 in
          (x3,stack)
      else if getNumber x1 = 100 (* d *) then
        let x1 = EL 1 stack in if getNumber x1 <> 110 (* n *) then (x3,stack) else
        let x1 = EL 2 stack in if getNumber x1 <> 101 (* e *) then (x3,stack) else
        let x3 = Number 3 in
          (x3,stack)
      else
        (x3,stack)
    else
    if getNumber x1 = 4 then (x3,stack) else
    if getNumber x1 = 5 then (x3,stack) else
    if getNumber x1 = 6 then
      let x1 = HD stack   in if getNumber x1 <> 116 (* t *) then (x3,stack) else
      let x1 = EL 1 stack in if getNumber x1 <>  99 (* c *) then (x3,stack) else
      let x1 = EL 2 stack in if getNumber x1 <> 117 (* u *) then (x3,stack) else
      let x1 = EL 3 stack in if getNumber x1 <> 114 (* r *) then (x3,stack) else
      let x1 = EL 4 stack in if getNumber x1 <> 116 (* t *) then (x3,stack) else
      let x1 = EL 5 stack in if getNumber x1 <> 115 (* s *) then (x3,stack) else
      let x3 = Number 2 in
        (x3,stack)
    else
      (x3,stack)`

val (res,semi_symbol'_def,semi_symbol'_pre_def) = x64_compile `
  semi_symbol' (stack:bc_value list) =
    let (x3,stack) = semi_symbol stack in
    let x1 = x3 in
      (x1,x3,stack)`

val semi_symbol_thm = prove(
  ``semi_symbol_pre (MAP Chr (REVERSE xs) ++ BlockNil::stack) /\
    (semi_symbol (MAP Chr (REVERSE xs) ++ BlockNil::stack) =
      (semi_sym (OtherS xs),MAP Chr (REVERSE xs) ++ BlockNil::stack))``,
  FULL_SIMP_TAC std_ss [semi_symbol_def,semi_symbol_pre_def,LET_DEF,
    semi_sym_def,semi_len_thm]
  \\ (LIST_CASES |> SPEC_ALL |> STRIP_ASSUME_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) [getNumber_def,isNumber_def]
  \\ `!k. ~(SUC (SUC (SUC (SUC (SUC (SUC (SUC k)))))) < 7)` by DECIDE_TAC
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [Chr_def,isNumber_def,
      getNumber_def,GSYM ORD_11] \\ TRY DECIDE_TAC
  \\ (LIST_CASES |> Q.SPEC `REVERSE ts` |> STRIP_ASSUME_TAC)
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [getNumber_def]);


(* next symbol -- final package up *)

val (res,next_sym_full_def,next_sym_full_pre_def) = x64_compile `
  next_sym_full (s,stack) =
    let x3 = Number 0 in
    let x1 = BlockNil in
    let x2 = x1 in
    let stack = x1::stack in
    let (x1,x2,s,stack) = next_symbol (x1,x2,s,stack) in
      if getNumber x1 = 2 then
        let (x1,stack) = (HD stack, TL stack) in
        let x2 = Number 0 in
          (x1,x2,x3,s,stack)
      else if getNumber x1 = 1 then
        let (x1,x2,stack) = cons_list stack in
        let x1 = x2 in
        let x1 = BlockStringS x1 in
        let x2 = Number 1 in
          (x1,x2,x3,s,stack)
      else if getNumber x1 = 4 then
        let (x1,x3,stack) = semi_symbol' stack in
        let (x1,x2,stack) = cons_list stack in
        let x1 = x2 in
        let x1 = BlockOtherS x1 in
        let x2 = Number 1 in
          (x1,x2,x3,s,stack)
      else if getNumber x1 = 5 then
        let (x1,x2,stack) = cons_list stack in
        let x1 = x2 in
        let x1 = BlockLongS x1 in
        let x2 = Number 1 in
          (x1,x2,x3,s,stack)
      else if getNumber x1 = 3 then
        let (x1,stack) = (HD stack, TL stack) in
        let x1 = BlockNumberS x1 in
        let (x2,stack) = (HD stack, TL stack) in
        let x2 = Number 1 in
          (x1,x2,x3,s,stack)
      else
        let (x1,x2,stack) = cons_list stack in
        let x1 = BlockErrorS in
        let x2 = Number 1 in
          (x1,x2,x3,s,stack)`

val next_sym_full_thm = prove(
  ``next_sym_full_pre (s,stack) /\
    (next_sym_full (s,stack) =
     case next_sym s.input of
     | NONE => (BlockNil, Number 0, Number 0, s with input := "", stack)
     | SOME (t,rest) => (BlockSym t, Number 1, semi_sym t,
                         s with input := rest, stack))``,
  SIMP_TAC std_ss [next_sym_full_def,next_sym_full_pre_def,LET_DEF]
  \\ ASSUME_TAC next_symbol_thm
  \\ SEP_I_TAC "next_symbol" \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `next_sym s.input` \\ FULL_SIMP_TAC std_ss [] THEN1 EVAL_TAC
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [getNumber_def]
  \\ FULL_SIMP_TAC (srw_ss()) [isNumber_def,BlockSym_def,
       cons_list_thm,semi_symbol_thm,semi_symbol'_def,semi_symbol'_pre_def]
  \\ FULL_SIMP_TAC std_ss [semi_sym_def,LET_DEF,MEM,cons_list_thm]
  \\ FULL_SIMP_TAC (srw_ss()) []);

(* lex_until *)

val (res,lex_until_def,lex_until_pre_def) = x64_compile `
  lex_until (x1,x2,x3,x4:bc_value,s,stack) =
    let (x1,x2,x3,x4) = ID (x1,x2,x3,x4) in
    let (x1,x2,x3,s,stack) = next_sym_full (s,stack) in
      if getNumber x2 = 0 then (* next_sym returned NONE *)
        (x1,x2,x3,x4,s,stack)
      else
        let stack = x1 :: stack in
          if getNumber x3 = 0 then (* nothing of interest *)
            lex_until (x1,x2,x3,x4,s,stack)
          else if getNumber x3 = 2 then (* some form of open paren *)
            let x1 = x4 in
            let x2 = Number 1 in
            let x1 = any_add x1 x2 in
            let x4 = x1 in
              lex_until (x1,x2,x3,x4,s,stack)
          else if getNumber x3 = 3 then (* some form of close paren *)
            if getNumber x4 = 0 then
              lex_until (x1,x2,x3,x4,s,stack)
            else
              let x1 = x4 in
              let x2 = Number 1 in
              let x1 = any_sub x1 x2 in
              let x4 = x1 in
                lex_until (x1,x2,x3,x4,s,stack)
          else (* must be a semicolon *)
            if getNumber x4 = 0 then
              let x2 = Number 1 in
                (x1,x2,x3,x4,s,stack)
            else
              lex_until (x1,x2,x3,x4,s,stack)`

val isNumber_semi_sym = prove(
  ``!q. isNumber (semi_sym q)``,
  Cases \\ EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC);

val getNumber_semi_sym = prove(
  ``(getNumber (semi_sym s) = k) <=> (semi_sym s = Number k)``,
  ASSUME_TAC (Q.SPEC `s` isNumber_semi_sym)
  \\ Cases_on `semi_sym s`
  \\ FULL_SIMP_TAC (srw_ss()) [isNumber_def,getNumber_def]);

val lex_until_thm = prove(
  ``!acc d xs s x1 x2 x3 stack. (xs = s.input) ==>
      ?y1 y2 y3 fs.
        lex_until_pre (x1,x2,x3,Number (& d),s,MAP BlockSym acc ++ stack) /\
        (lex_until (x1,x2,x3,Number (& d),s,MAP BlockSym acc ++ stack) =
          case lex_aux_alt acc d s.input of
          | NONE => (y1,Number 0,y2,y3,s with input := "",MAP BlockSym fs ++ stack)
          | SOME (ts,rest) => (y1,Number 1,y2,y3,s with input := rest,
                               MAP BlockSym (REVERSE ts) ++ stack))``,
  HO_MATCH_MP_TAC lex_aux_alt_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [lex_until_def,lex_until_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,ID_def]
  \\ ASM_SIMP_TAC std_ss [next_sym_full_thm,Once lex_aux_alt_def,LET_DEF]
  \\ Cases_on `next_sym s.input`
  \\ FULL_SIMP_TAC (srw_ss()) [getNumber_def,isNumber_def,isNumber_semi_sym]
  THEN1 (Q.EXISTS_TAC `acc` \\ FULL_SIMP_TAC std_ss [])
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [getNumber_def,isNumber_def]
  \\ REVERSE (Cases_on `?tt. q = OtherS tt`) THEN1
   (FULL_SIMP_TAC std_ss []
    \\ `getNumber (semi_sym q) = 0` by ALL_TAC THEN1
      (Cases_on `q` \\ EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [isNumber_semi_sym]
    \\ SEP_I_TAC "lex_until" \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`y1`,`y2`,`y3`,`fs`]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `((tt = ";") <=> (semi_sym (OtherS tt) = Number 1)) /\
      ((tt = "let") \/ (tt = "struct") \/ (tt = "sig") \/ (tt = "(")
       <=> (semi_sym (OtherS tt) = Number 2)) /\
      ((tt = ")") \/ (tt = "end") <=> (semi_sym (OtherS tt) = Number 3))` by ALL_TAC
  THEN1 (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [semi_sym_def] \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC (srw_ss()) [getNumber_semi_sym]
  \\ Cases_on `tt = ";"` THEN1
    (FULL_SIMP_TAC (srw_ss()) [semi_sym_def,getNumber_def,isNumber_def]
     \\ Cases_on `d = 0` \\ FULL_SIMP_TAC (srw_ss()) []
     \\ SEP_I_TAC "lex_until" \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Q.LIST_EXISTS_TAC [`y1`,`y2`,`y3`,`fs`]
     \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
  \\ Cases_on `semi_sym (OtherS tt) = Number 0`
  \\ FULL_SIMP_TAC (srw_ss()) [isNumber_def] THEN1
   (POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [semi_sym_def]
    \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_I_TAC "lex_until" \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`y1`,`y2`,`y3`,`fs`]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `semi_sym (OtherS tt) = Number 2`
  \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC std_ss [any_add_def,getNumber_def,integerTheory.INT_ADD]
    \\ SEP_I_TAC "lex_until" \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`y1`,`y2`,`y3`,`fs`]
    \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ `semi_sym (OtherS tt) = Number 3` by ALL_TAC THEN1
   (SRW_TAC [] [semi_sym_def,MEM] \\ FULL_SIMP_TAC (srw_ss()) [semi_sym_def,MEM])
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_FORALL]
  \\ Cases_on `d = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
   (SEP_I_TAC "lex_until" \\ POP_ASSUM MP_TAC \\ MATCH_MP_TAC IMP_IMP
    THEN1 (SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [semi_sym_def]))
  \\ FULL_SIMP_TAC std_ss [any_sub_def,getNumber_def,
       integerTheory.INT_SUB,DECIDE ``n <> 0 ==> 1 <= n:num``]
  \\ SEP_I_TAC "lex_until" \\ POP_ASSUM MP_TAC \\ MATCH_MP_TAC IMP_IMP
  THEN1 (SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [semi_sym_def]));

(* cons_list_alt *)

val (res,cons_list_alt_aux_def,cons_list_alt_aux_pre_def) = x64_compile `
  cons_list_alt_aux (x1,x2:bc_value,stack) =
    let x2 = x1 in
    let (x1,stack) = (HD stack, TL stack) in
      if ~isBlock x1 then (x1,x2,stack) else
        let x1 = BlockCons (x1,x2) in
          cons_list_alt_aux (x1,x2,stack)`

val (res,cons_list_alt_def,cons_list_alt_pre_def) = x64_compile `
  cons_list_alt (stack) =
    let x1 = BlockNil in
    let x2 = BlockNil in
    let (x1,x2,stack) = cons_list_alt_aux (x1,x2,stack) in
      (x1,x2,stack)`

val isBlock_BkockSym = prove(
  ``!s. isBlock (BlockSym s)``,
  Cases \\ EVAL_TAC);

val cons_list_alt_aux_thm = prove(
  ``!xs ys x2.
      cons_list_alt_aux_pre (BlockList ys,x2,MAP BlockSym xs ++ Number n::stack) /\
      (cons_list_alt_aux (BlockList ys,x2,MAP BlockSym xs ++ Number n::stack) =
         (Number n,BlockList (MAP BlockSym (REVERSE xs) ++ ys),stack))``,
  Induct \\ ONCE_REWRITE_TAC [cons_list_alt_aux_def,cons_list_alt_aux_pre_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,isBlock_BkockSym,isBlock_def,canCompare_def]
  \\ SIMP_TAC std_ss [Once (GSYM BlockList_def)]
  \\ ASM_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ SIMP_TAC std_ss [Once (GSYM BlockList_def)]
  \\ ASM_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []) |> Q.SPECL [`xs`,`[]`]
  |> SIMP_RULE std_ss [BlockList_def,APPEND_NIL];

val cons_list_alt_thm = prove(
  ``cons_list_alt_pre (MAP BlockSym xs ++ Number n::stack) /\
    (cons_list_alt (MAP BlockSym xs ++ Number n::stack) =
       (Number n,BlockList (MAP BlockSym (REVERSE xs)),stack))``,
  SIMP_TAC std_ss [cons_list_alt_def,cons_list_alt_pre_def,
    cons_list_alt_aux_thm,LET_DEF]);

(* lex_until_semi *)

val (lex_until_semi_res,lex_until_semi_def,lex_until_semi_pre_def) = x64_compile `
  lex_until_semi (x1,x3,s,stack) =
    let stack = x1 :: stack in
    let stack = x3 :: stack in
    let x1 = Number 0 in
    let stack = x1 :: stack in
    let x2 = x1 in
    let x3 = x1 in
    let x4 = x1 in
    let (x1,x2,x3,x4,s,stack) = lex_until (x1,x2,x3,x4,s,stack) in
    let x4 = x2 in
    let (x1,x2,stack) = cons_list_alt stack in
    let (x3,stack) = (HD stack,TL stack) in
    let (x1,stack) = (HD stack,TL stack) in
      if getNumber x4 = 0 then
        let x2 = x4 in (x1,x2,x3,x4,s,stack)
      else
        (x1,x2,x3,x4,s,stack)`

val lex_until_semi_thm = prove(
  ``lex_until_semi_pre (x1,x3,s,stack) /\
    (lex_until_semi (x1,x3,s,stack) =
      case lex_until_top_semicolon_alt s.input of
      | NONE => (x1,Number 0,x3,Number 0,s with input := "",stack)
      | SOME (ts,rest) => (x1,BlockList (MAP BlockSym ts),x3,Number 1,
                           s with input := rest,stack))``,
  SIMP_TAC std_ss [lex_until_semi_def,lex_until_semi_pre_def,LET_DEF]
  \\ ASSUME_TAC (lex_until_thm |> Q.SPECL [`[]`,`0`])
  \\ FULL_SIMP_TAC std_ss [MAP,APPEND]
  \\ SEP_I_TAC "lex_until" \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ SIMP_TAC std_ss [lex_until_top_semicolon_alt_def]
  \\ Cases_on `lex_aux_alt [] 0 s.input`
  \\ FULL_SIMP_TAC (srw_ss()) [cons_list_alt_thm,getNumber_def,isNumber_def]
  \\ Cases_on `x`
  \\ FULL_SIMP_TAC (srw_ss()) [cons_list_alt_thm,getNumber_def,isNumber_def]);

val lex_until_semi_res_def = Define `
  lex_until_semi_res input =
      case lex_until_top_semicolon_alt input of
      | NONE => Number 0
      | SOME (ts,rest) => BlockList (MAP BlockSym ts)`

val lex_until_semi_test_def = Define `
  lex_until_semi_test input =
      case lex_until_top_semicolon_alt input of
      | NONE => Number 0
      | SOME (ts,rest) => Number 1`

val lex_until_semi_state_def = Define `
  lex_until_semi_state input =
    case lex_until_top_semicolon_alt input of
      | NONE => ""
      | SOME (ts,rest) => rest`;

val lex_until_semi_thm = prove(
  ``lex_until_semi_pre (x1,x3,s,stack) /\
    (lex_until_semi (x1,x3,s,stack) =
       (x1,lex_until_semi_res s.input,x3,
           lex_until_semi_test s.input,
           s with input := lex_until_semi_state s.input,stack))``,
  SIMP_TAC std_ss [lex_until_semi_thm,lex_until_semi_res_def,
    lex_until_semi_test_def,lex_until_semi_state_def]
  \\ Cases_on `lex_until_top_semicolon_alt s.input`
  \\ SIMP_TAC (srw_ss()) [] \\ Cases_on `x` \\ SIMP_TAC (srw_ss()) []);

val zHEAP_LEX = let
  val th = lex_until_semi_res |> SIMP_RULE std_ss [lex_until_semi_thm,LET_DEF,SEP_CLAUSES]
  val th = SPEC_COMPOSE_RULE [zHEAP_CALL_LEX_WITH_STOP_ADDR,th,zHEAP_JMP_STOP_ADDR]
  val th = th |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
  val name = "lex"
  val ptr = ``cs.lex_ptr``
  val th = abbreviate_code name ptr th
  val th = SPEC_COMPOSE_RULE [th,zHEAP_ZERO_STOP_ADDR]
  val th = th |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) []))
  in th end;


(* set cs pointers *)

val full_code_abbrevs_def = Define `
  full_code_abbrevs cs =
     bignum_code cs.bignum_ptr UNION alloc_code cs.alloc_ptr UNION
     equal_code cs.equal_ptr UNION print_code cs.print_ptr UNION
     error_code cs.error_ptr UNION lex_code cs.lex_ptr UNION
     install_and_run_code cs.install_and_run_ptr`;

fun zHEAP_SET_CS i update = let
  val call_th = x64_call_imm
  val pop_th = x64_pop_r15
  val store_th = spec ("mov [r9+"^(int_to_string i)^"], r15")
  val th = SPEC_COMPOSE_RULE [call_th,pop_th,store_th]
  val th = th |> Q.INST [`rip`|->`p`] |> RW [HD,TL,NOT_CONS_NIL,SEP_CLAUSES]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND] |> UNDISCH_ALL
  val target = ``~zS * zPC p * zVALS cs vals *
      cond (heap_inv (cs,x1,x2,x3,x4,refs,stack,s,NONE) vals)``
  val (th,goal) = expand_pre th target
  val lemma = prove(goal, SIMP_TAC (std_ss++star_ss) [zVALS_def,SEP_IMP_REFL])
  val th = MP th lemma
  val th = th |> DISCH_ALL |> DISCH T
              |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  val pc = get_pc th
  val th = MATCH_MP SPEC_WEAKEN_LEMMA th
  val th = th |> Q.SPEC `zHEAP (^update (p+6w),
                                x1,x2,x3,x4,refs,stack,s,NONE) * ~zS *^pc`
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
    \\ Q.EXISTS_TAC `vals with <| reg15 := p + 6w ; memory :=
          (vals.reg9 + n2w ^(numSyntax.term_of_int i) =+ p + 0x6w) vals.memory |>`
    \\ SIMP_TAC (std_ss++sep_cond_ss) [zVALS_def,cond_STAR]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_inv_def] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`vs`,`r1`,`r2`,`r3`,`r4`,`roots`,`heap`,`a`,`sp`]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,HD,TL]
    \\ FULL_SIMP_TAC std_ss [x64_store_def,one_list_def,word_arith_lemma1,
         STAR_ASSOC] \\ FULL_SIMP_TAC (srw_ss()) [SEP_CLAUSES]
    \\ Q.ABBREV_TAC `m = vals.memory`
    \\ Q.ABBREV_TAC `dm = vals.memory_domain`
    \\ SEP_W_TAC)
  val th = MP th lemma
  val th = Q.GEN `vals` th |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zHEAP (cs, x1, x2, x3, x4, refs, stack, s, NONE) * ~zS * zPC p``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zHEAP_def,SEP_IMP_REFL,SEP_CLAUSES])
  val th = MP th lemma
  in GSYM th end;

val SET_CS_ERROR   = zHEAP_SET_CS  40 ``\w. cs with error_ptr := w``;
val SET_CS_ALLOC   = zHEAP_SET_CS  48 ``\w. cs with alloc_ptr := w``;
val SET_CS_BIGNUM  = zHEAP_SET_CS  56 ``\w. cs with bignum_ptr := w``;
val SET_CS_EQUAL   = zHEAP_SET_CS  64 ``\w. cs with equal_ptr := w``;
val SET_CS_PRINT   = zHEAP_SET_CS  72 ``\w. cs with print_ptr := w``;
val SET_CS_LEX     = zHEAP_SET_CS 120 ``\w. cs with lex_ptr := w``;
val SET_CS_INSTALL = zHEAP_SET_CS 128 ``\w. cs with install_and_run_ptr := w``;

fun guess_length name = let
  fun dest_code_pair tm = let
    val (x,y) = dest_pair tm
    val i = wordsSyntax.dest_word_add x |> snd |> rand |> numSyntax.int_of_term
    val l = listSyntax.dest_list y |> fst |> length
    in i + l end handle HOL_ERR _ => 0
  val list_max = foldl (fn (x,y) => if x <= y then y else x) 0
  in fetch "-" name |> concl |> find_terms pairSyntax.is_pair
                    |> map dest_code_pair |> list_max |> numSyntax.term_of_int end

val zHEAP_INIT = let
  fun set_cs (th,name) =
    th |> Q.INST [`imm32`|->`n2w ^(guess_length (name ^ "_code_def"))`]
       |> SIMP_RULE (srw_ss()) [IMM32_def]
  val th = map set_cs
           [(SET_CS_ERROR,"error"),
            (SET_CS_ALLOC,"alloc"),
            (SET_CS_BIGNUM,"bignum"),
            (SET_CS_EQUAL,"equal"),
            (SET_CS_PRINT,"print"),
            (SET_CS_LEX,"lex"),
            (SET_CS_INSTALL,"install_and_run")] |> SPEC_COMPOSE_RULE
  val th = SPEC_COMPOSE_RULE [zHEAP_SETUP,th]
  val l = th |> concl |> rand |> find_term (can (match_term ``zPC p``))
             |> rand |> rand |> rand |> numSyntax.int_of_term
  val th = if l mod 2 = 0 then th else SPEC_COMPOSE_RULE [th,zHEAP_NOP]
  val full_cs =
    th |> concl |> rand |> find_term (can (match_term ``zHEAP (x,yyy)``))
       |> rand |> rator |> rand
  val full_cs_def = Define `full_cs init p = ^full_cs` ;
  val th = th |> RW [GSYM full_cs_def]
  in th end

val zHEAP_ABBREVS = prove(
  ``SPEC X64_MODEL
      (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * zPC p)
      (full_code_abbrevs cs)
      (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * zPC p)``,
  SIMP_TAC std_ss [SPEC_REFL]);

val all_code_abbrevs =
  map (fetch "-") ["error_code_def", "alloc_code_def", "lex_code_def",
    "install_and_run_code_def", "bignum_code_def", "print_code_def",
    "equal_code_def"] |> LIST_CONJ


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
  ref_adjust (cb,sb,ev) (refs1:num |-> ref_value) =
    let adj = (\n. if ev then 2 * n else 2 * n + 1) in
      FUN_FMAP (\n. case refs1 ' (n DIV 2) of
                    | ValueArray vs => ValueArray (MAP (bc_adjust (cb,sb,ev)) vs)
                    | x => x)
               (IMAGE adj (FDOM refs1))`;

val zBC_HEAP_def = Define `
  zBC_HEAP bs (x,cs,stack,s,out) (cb,sb,ev,f2) =
    SEP_EXISTS x2 x3.
      let ss = MAP (bc_adjust (cb,sb,ev)) bs.stack ++ (Number 0) :: stack in
        zHEAP (cs,HD ss,x2,x3,x,FUNION (ref_adjust (cb,sb,ev) bs.refs) f2,TL ss,
                  s with <| output := (if s.local.printing_on = 0w then out
                                       else out ++ bs.output) ;
                            handler := bs.handler + SUC (LENGTH stack) |>,NONE)`;

val zBC_HEAP_1_def = Define `
  zBC_HEAP_1 bs y (x,cs,stack,s,out) (cb,sb,ev,f2) =
    SEP_EXISTS x2 x3.
      zHEAP (cs,y,x2,x3,x,FUNION (ref_adjust (cb,sb,ev) bs.refs) f2,
             MAP (bc_adjust (cb,sb,ev)) bs.stack ++ (Number 0) :: stack,
                s with <| output := (if s.local.printing_on = 0w then out
                                     else out ++ bs.output) ;
                          handler := bs.handler + SUC (LENGTH stack) |>,NONE)`;

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
      s with <| output := if s.local.printing_on = 0x0w then out
          else STRCAT out s1.output ; handler := h |>,NONE) *
     zPC (cb + n2w (2 * s1.pc)) * ~zS)``
  val i = fst (match_term pre tm)
  val th = INST i th
  in th end

val IMP_small_offset = prove(
  ``(n < 268435456 ==>
     SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)) ==>
    SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), small_offset n xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)``,
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

val IMP_small_offset6 = prove(
  ``(n < 268435456 ==>
     SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)) ==>
    SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), small_offset6 n xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [small_offset6_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [x64_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
  \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) []
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Error6) |> SPEC_ALL
                |> DISCH_ALL |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO]
                |> Q.INST [`base`|->`cb`])
  \\ FULL_SIMP_TAC (srw_ss()) [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]);

val IMP_small_offset12 = prove(
  ``(n < 268435456 ==>
     SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)) ==>
    SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), small_offset12 n xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [small_offset12_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [x64_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
  \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) []
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Error12) |> SPEC_ALL
                |> DISCH_ALL |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO]
                |> Q.INST [`base`|->`cb`])
  \\ FULL_SIMP_TAC (srw_ss()) [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]);

val IMP_small_offset16 = prove(
  ``(n < 268435456 ==>
     SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)) ==>
    SPEC X64_MODEL
     (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
      zPC (cb + n2w (2 * s1.pc)) * ~zS)
     ((cb + n2w (2 * s1.pc), small_offset16 n xs) INSERT code_abbrevs cs)
     (post \/
      zHEAP_ERROR cs)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [small_offset16_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [x64_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
  \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ SIMP_TAC (srw_ss()) []
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Error16) |> SPEC_ALL
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

fun ANY_ERROR_TAC error_th =
  SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
  \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare error_th) |> SPEC_ALL
                |> DISCH_ALL |> RW [AND_IMP_INTRO])
  \\ FULL_SIMP_TAC (srw_ss()) [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [bc_fetch_ignore_stack]

val ERROR_TAC =
  TRY (ANY_ERROR_TAC zBC_Error \\ NO_TAC) \\
  TRY (ANY_ERROR_TAC zBC_Error6 \\ NO_TAC) \\
  TRY (ANY_ERROR_TAC zBC_Error12 \\ NO_TAC) \\
  TRY (ANY_ERROR_TAC zBC_Error16 \\ NO_TAC) \\
  NO_TAC

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

val bc_equal_sym = prove(
  ``(!x1 x2. bc_equal x1 x2 = bc_equal x2 x1) /\
    (!xs1 xs2. bc_equal_list xs1 xs2 = bc_equal_list xs2 xs1)``,
  HO_MATCH_MP_TAC bytecodeTerminationTheory.bc_equal_ind
  \\ REPEAT ( STRIP_TAC THEN1 ( GEN_TAC \\ Cases \\ SRW_TAC[][bc_equal_def] ))
  \\ NTAC 8 ( STRIP_TAC THEN1 ( SRW_TAC[][bc_equal_def,EQ_IMP_THM] ) )
  \\ STRIP_TAC THEN1 (
    SRW_TAC[][] \\
    SRW_TAC[][bc_equal_def] \\
    REV_FULL_SIMP_TAC std_ss [] )
  \\ STRIP_TAC THEN1 ( SRW_TAC[][bc_equal_def,EQ_IMP_THM] )
  \\ STRIP_TAC THEN1 (
    SRW_TAC[][bc_equal_def] \\
    Cases_on`bc_equal x1 x2` \\ FULL_SIMP_TAC (srw_ss())[] \\
    Cases_on`bc_equal x2 x1` \\ FULL_SIMP_TAC (srw_ss())[] \\
    BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[] )
  \\ STRIP_TAC THEN1 ( GEN_TAC \\ Cases \\ SRW_TAC[][bc_equal_def] )
  \\ SRW_TAC[][bc_equal_def]) |> CONJUNCT1;

val bc_equal_adjust = prove(
  ``(!x1 x2.
      bc_equal x1 x2 <> Eq_type_error ==>
      (bc_equal (bc_adjust (cb,sb,ev) x2) (bc_adjust (cb,sb,ev) x1) =
       bc_equal x2 x1)) /\
    (!x1 x2.
      bc_equal_list x1 x2 <> Eq_type_error ==>
      (bc_equal_list (MAP (bc_adjust (cb,sb,ev)) x2) (MAP (bc_adjust (cb,sb,ev)) x1) =
       bc_equal_list x2 x1))``,
  HO_MATCH_MP_TAC bytecodeTerminationTheory.bc_equal_ind
  \\ REPEAT (STRIP_TAC THEN1 ( GEN_TAC \\ Cases \\ SRW_TAC[][bc_equal_def,bc_adjust_def]))
  \\ NTAC 3 ( STRIP_TAC THEN1 ( SRW_TAC[ARITH_ss][bc_equal_def,bc_adjust_def] ) )
  \\ STRIP_TAC THEN1 (
    SRW_TAC[][bc_adjust_def] \\
    FULL_SIMP_TAC (srw_ss()) [bc_equal_def] \\
    SRW_TAC[][] \\
    REV_FULL_SIMP_TAC (srw_ss()) [] )
  \\ STRIP_TAC THEN1 ( SRW_TAC[ARITH_ss][bc_equal_def,bc_adjust_def] )
  \\ STRIP_TAC THEN1 (
    SRW_TAC[][bc_adjust_def] \\
    FULL_SIMP_TAC (srw_ss()) [bc_equal_def] \\
    Cases_on`bc_equal x1 x2` \\ FULL_SIMP_TAC (srw_ss())[] \\
    Cases_on`bc_equal x2 x1` \\ FULL_SIMP_TAC (srw_ss())[] \\
    ASSUME_TAC (SPEC_ALL bc_equal_sym) \\
    REV_FULL_SIMP_TAC (srw_ss())[] \\
    SRW_TAC[][] \\ FULL_SIMP_TAC (srw_ss())[] )
  \\ STRIP_TAC THEN1 ( SRW_TAC[ARITH_ss][bc_equal_def,bc_adjust_def] )
  \\ STRIP_TAC THEN1 ( SRW_TAC[ARITH_ss][bc_equal_def,bc_adjust_def] )) |> CONJUNCT1;

val DROP_MAP_APPEND = prove(
  ``DROP (LENGTH xs) (MAP f xs ++ ys) = ys``,
  METIS_TAC [rich_listTheory.DROP_LENGTH_APPEND,LENGTH_MAP]);

val LESS_EQ_LENGTH_ALT = prove(
  ``!n xs. n <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys2 = n)``,
  Induct_on `xs` \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `(ys1 = []) \/ ?x l. ys1 = SNOC x l` by METIS_TAC [SNOC_CASES]
  THEN1 (Q.EXISTS_TAC `[]` \\ FULL_SIMP_TAC (srw_ss()) [APPEND])
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ Q.EXISTS_TAC `h::l` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `x::ys2` \\ FULL_SIMP_TAC (srw_ss()) []);

val LENGTH_TL_APPEND = prove(
  ``!xs. LENGTH (TL (xs ++ y::ys)) = LENGTH xs + LENGTH ys``,
  Cases \\ SRW_TAC [] [ADD1] \\ DECIDE_TAC);

val HD_TL = prove(
  ``!xs y ys. HD (xs ++ y::ys) :: TL (xs ++ y::ys) = xs ++ y::ys``,
  Cases \\ SRW_TAC [] []);

val LoadRev_LEMMA = prove(
  ``n < LENGTH xs ==>
    (EL (n + (LENGTH stack + 1)) (REVERSE ((MAP f xs) ++ Number 0::stack)) =
     f (EL n (REVERSE xs)))``,
  SRW_TAC [] [REVERSE_APPEND,rich_listTheory.EL_APPEND2] \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`n`,`n`) \\ Q.SPEC_TAC (`xs`,`xs`) \\ recInduct SNOC_INDUCT
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_SNOC]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [MAP_SNOC,REVERSE_SNOC]
  \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) []);

val bvs_to_chars_bc_adjust = prove(
  ``!ys xs. bvs_to_chars (MAP (bc_adjust (cb,sb,ev)) ys) xs =
            bvs_to_chars ys xs``,
  Induct \\ EVAL_TAC \\ SIMP_TAC std_ss [] \\ Cases
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val only_chars_bc_adjust = prove(
  ``!data. only_chars data ==>
           (MAP (bc_adjust (cb,sb,ev)) data = data)``,
  Induct \\ EVAL_TAC \\ Cases \\ EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [only_chars_def,is_char_def]);

val bvs_to_chars_bc_adjust = prove(
  ``!l acc.
      bvs_to_chars (MAP (bc_adjust (cb,sb,ev)) l) acc =
      bvs_to_chars l acc``,
  Induct \\ FULL_SIMP_TAC std_ss [MAP,bc_adjust_def,bvs_to_chars_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [MAP,bc_adjust_def,bvs_to_chars_def]);

val bv_to_string_bc_adjust = prove(
  ``!v. bv_to_string (bc_adjust (cb,sb,ev) v) = bv_to_string v``,
  Cases \\ FULL_SIMP_TAC std_ss [bc_adjust_def,bv_to_string_def]
  \\ SRW_TAC [] [bvs_to_chars_bc_adjust]);

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
          zHEAP_ERROR cs)``,

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
  \\ NTAC 3 (TRY (MATCH_MP_TAC IMP_small_offset6 \\ REPEAT STRIP_TAC
                  \\ TRY (SRW_TAC [] [output_simp] \\ NO_TAC)))
  \\ NTAC 3 (TRY (MATCH_MP_TAC IMP_small_offset12 \\ REPEAT STRIP_TAC
                  \\ TRY (SRW_TAC [] [output_simp] \\ NO_TAC)))
  \\ NTAC 3 (TRY (MATCH_MP_TAC IMP_small_offset16 \\ REPEAT STRIP_TAC
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
  THEN1 (* PushInt *)
   (Cases_on `i < 0` \\ FULL_SIMP_TAC std_ss [] THEN1 ERROR_TAC
    \\ SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_PushInt
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL]
    \\ STRIP_TAC THEN1 intLib.COOPER_TAC
    \\ `&Num i = i` by intLib.COOPER_TAC
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_length_def,x64_def,
        small_offset_def,IMM32_def,LENGTH,GSYM ADD_ASSOC,LET_DEF]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_DISJ_def]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
  THEN1 (* Cons *)
   (Q.MATCH_ASSUM_RENAME_TAC `bc_fetch s1 = SOME (Stack (Cons tag len))` []
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.stack = ts ++ xs` []
    \\ REVERSE (Cases_on `tag < 4096`)
    THEN1 (FULL_SIMP_TAC std_ss [] \\ ERROR_TAC)
    \\ REVERSE (Cases_on `len < 32768`)
    THEN1 (FULL_SIMP_TAC std_ss [] \\ ERROR_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (Cases_on `len = 0`) \\ FULL_SIMP_TAC std_ss [] THEN1
     (`LENGTH ts < 32768 /\ LENGTH ts <> 0` by DECIDE_TAC
      \\ SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
      \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
      \\ ASM_SIMP_TAC std_ss []
      \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `len = LENGTH ts` (ASSUME_TAC o GSYM)
      \\ Q.PAT_ASSUM `s1.stack = ts ++ xs` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss []
      \\ (prepare zBC_ConsBig
           |> DISCH ``n < 4096:num`` |> SIMP_RULE std_ss [] |> UNDISCH
           |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
           |> DISCH_ALL |> RW [AND_IMP_INTRO]
           |> MATCH_MP_TAC)
      \\ POP_ASSUM (MP_TAC o GSYM)
      \\ POP_ASSUM (MP_TAC o GSYM)
      \\ NTAC 2 STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
           isRefPtr_def,getRefPtr_def]
      \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL]
      \\ FULL_SIMP_TAC std_ss [LENGTH_NIL]
      \\ Cases_on `ts` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ `LENGTH t = LENGTH (MAP (bc_adjust (cb,sb,ev)) t)` by
           FULL_SIMP_TAC std_ss [LENGTH_MAP]
      \\ FULL_SIMP_TAC std_ss [rich_listTheory.TAKE_LENGTH_APPEND,
           rich_listTheory.DROP_LENGTH_APPEND,GSYM APPEND_ASSOC,bc_adjust_def,
           MAP_APPEND,MAP,rich_listTheory.MAP_REVERSE]
      \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_length_def,x64_def,
          small_offset_def,IMM32_def,LENGTH,GSYM ADD_ASSOC,LET_DEF,ADD1]
      \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,word_arith_lemma1]
      \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_DISJ_def]
      \\ REPEAT STRIP_TAC
      \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
    \\ NTAC 3 (TRY (MATCH_MP_TAC IMP_small_offset \\ REPEAT STRIP_TAC
                    \\ TRY (SRW_TAC [] [output_simp] \\ NO_TAC)))
    \\ Cases_on `ts` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,REVERSE_DEF,APPEND]
    \\ SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_ConsNil
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL]
    \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def,MAP]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_length_def,x64_def,
        small_offset_def,IMM32_def,LENGTH,GSYM ADD_ASSOC,LET_DEF,ADD1]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_DISJ_def]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
  THEN1 (* Cons2 *) ERROR_TAC
  THEN1 (* Load *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Load
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL]
    \\ STRIP_TAC THEN1
     (Cases_on `s1.stack`
      \\ FULL_SIMP_TAC std_ss [LENGTH,MAP,TL,APPEND,LENGTH_APPEND,LENGTH_MAP]
      \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_length_def,x64_def,
        small_offset_def,IMM32_def,LENGTH,GSYM ADD_ASSOC]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ IMP_RES_TAC LESS_LENGTH
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,EL_LENGTH,APPEND,GSYM APPEND_ASSOC,
         EL_LENGTH |> Q.SPEC `MAP f xs` |> RW [LENGTH_MAP]]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_DISJ_def] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
  THEN1 (* Store *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Store
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH_LUPDATE]
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [MAP,MAP_APPEND,EL_LENGTH,APPEND,GSYM APPEND_ASSOC,
         LUPDATE_LENGTH |> Q.SPEC `MAP f xs` |> RW [LENGTH_MAP]]
    \\ Q.PAT_ASSUM `n = LENGTH ys'` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_length_def,x64_def,
        small_offset_def,IMM32_def,LENGTH,GSYM ADD_ASSOC]
    \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,SEP_DISJ_def] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
  THEN1 (* LengthBlock *) ERROR_TAC
  THEN1 (* El *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_El
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.stack = Block tag ts::xs` []
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [bc_tag_eq_pre_def,isNumber_def,LET_DEF,LENGTH_MAP,
        isBlock_def,getNumber_def,small_int_def,getTag_def,getContent_def]
      \\ intLib.COOPER_TAC)
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,EL_MAP]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`Number (&n)`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC,bc_adjust_def,
         MAP,getTag_def])
  THEN1 (* El2 *) ERROR_TAC
  THEN1 (* TagEq *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_TagEq
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.stack = Block tag ts::xs` []
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH] \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [bc_tag_eq_pre_def,isNumber_def,LET_DEF,
        isBlock_def,getNumber_def,small_int_def,getTag_def]
      \\ intLib.COOPER_TAC)
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`Number (&n)`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC,bc_adjust_def,
         MAP,getTag_def])
  THEN1 (* IsBlock *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_IsBlock
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.stack = y::xs` []
    \\ SIMP_TAC std_ss [EVAL ``x64_inst_length (Stack IsBlock)``,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1]
    \\ STRIP_TAC
    THEN1 (Cases_on `y` \\ FULL_SIMP_TAC (srw_ss()) [] \\ EVAL_TAC)
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC]
    \\ Cases_on `y` \\ FULL_SIMP_TAC (srw_ss()) [isBlock_def,bc_adjust_def])
  THEN1 (* Equal *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Equal
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.stack = x2::x1::xs` []
    \\ FULL_SIMP_TAC std_ss [bc_equal_adjust]
    \\ (bc_equal_sym |> GSYM |> SPEC_ALL |> ASSUME_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [EVEN_w2n] \\ Q.PAT_ASSUM `~cb ' 0` MP_TAC
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w] \\ blastLib.BBLAST_TAC)
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ `bc_adjust (cb,sb,ev) (bc_equality_result_to_val (bc_equal x1 x2)) =
        bc_equality_result_to_val (bc_equal x1 x2)` by ALL_TAC THEN1
         (Cases_on `bc_equal x1 x2` \\ EVAL_TAC) \\ FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`bc_adjust (cb,sb,ev) x1`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [EVAL ``x64_inst_length (Stack Equal)``,
         LEFT_ADD_DISTRIB,word_arith_lemma1])
  THEN1 (* Add *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Add
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,isNumber_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH,getNumber_def]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,
         SEP_DISJ_def,bc_adjust_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [AC integerTheory.INT_ADD_ASSOC
         integerTheory.INT_ADD_COMM]
    \\ Q.LIST_EXISTS_TAC [`Number m`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Sub *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Sub
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,isNumber_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH,getNumber_def]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,
         SEP_DISJ_def,bc_adjust_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [AC integerTheory.INT_ADD_ASSOC
         integerTheory.INT_ADD_COMM]
    \\ Q.LIST_EXISTS_TAC [`Number n`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Mult *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Mul
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,isNumber_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH,getNumber_def]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,
         SEP_DISJ_def,bc_adjust_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [AC integerTheory.INT_MUL_ASSOC
         integerTheory.INT_MUL_COMM]
    \\ Q.LIST_EXISTS_TAC [`Number m`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Div *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Div
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,isNumber_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH,getNumber_def]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,
         SEP_DISJ_def,bc_adjust_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`Number m`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Mod *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Mod
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,isNumber_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH,getNumber_def]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,
         SEP_DISJ_def,bc_adjust_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`Number m`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  THEN1 (* Less *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Less
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,isNumber_def]
    \\ ASM_SIMP_TAC std_ss [x64_inst_length_def,x64_def,small_offset_def,
         LEFT_ADD_DISTRIB,GSYM ADD_ASSOC,word_arith_lemma1,x64_length_def,
         LENGTH,getNumber_def]
    \\ ASM_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,getContent_def,
         SEP_DISJ_def,bc_adjust_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.LIST_EXISTS_TAC [`Number m`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
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
         small_offset12_def,LET_DEF,GSYM ADD_ASSOC])
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
         small_offset16_def,LET_DEF,LENGTH,IMM32_def,word_arith_lemma1]
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
  THEN1 (* PushExc *)
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
  THEN1 (* PopExc *)
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
    \\ STRIP_TAC THEN1
     (ASM_SIMP_TAC std_ss [MAP,APPEND,HD,TL,MAP_APPEND,APPEND_11,
        GSYM APPEND_ASSOC,CONS_11]
      \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [])
      \\ Q.PAT_ASSUM `xx = sb` (ASSUME_TAC o GSYM)
      \\ ASM_SIMP_TAC std_ss [bc_adjust_def]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,LEFT_ADD_DISTRIB]
      \\ FULL_SIMP_TAC std_ss [MULT_CLAUSES,AC ADD_COMM ADD_ASSOC])
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
  THEN1 (* Ref *) ERROR_TAC
(*
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
*)
  THEN1 (* RefByte *) ERROR_TAC
  THEN1 (* Deref *) ERROR_TAC
(*
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
*)
  THEN1 (* DerefByte *) ERROR_TAC
  THEN1 (* Update *) ERROR_TAC
(*
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
*)
  THEN1 (* UpdateByte *) ERROR_TAC
  THEN1 (* Length *) ERROR_TAC
  THEN1 (* LengthByte *) ERROR_TAC
  THEN1 (* Galloc *)
    ERROR_TAC
  THEN1 (* Gupdate *)
    ERROR_TAC
  THEN1 (* Gread *)
    ERROR_TAC
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
  THEN1 (* Print *)
   (SIMP_TAC std_ss [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ (prepare zBC_Print
         |> MATCH_MP SPEC_WEAKEN |> SPEC_ALL
         |> DISCH_ALL |> RW [AND_IMP_INTRO]
         |> MATCH_MP_TAC)
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def,bv_to_string_bc_adjust]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w]
    \\ Q.MATCH_ASSUM_RENAME_TAC `s1.stack = y::xs` []
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [EVEN_w2n] \\ Q.PAT_ASSUM `~cb ' 0` MP_TAC
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w] \\ blastLib.BBLAST_TAC)
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Cases_on `s.local.printing_on = 0x0w`
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    THEN1 (Q.LIST_EXISTS_TAC [`Number 0`,`x3`]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
    \\ Q.LIST_EXISTS_TAC [`Number 0`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC])
  THEN1 (* PrintWord8 *) ERROR_TAC
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
    \\ Cases_on `s.local.printing_on = 0x0w`
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ADD_ASSOC]));

val zBC_HEAP_Stop = prove(
  ``(bc_fetch s1 = SOME (Stop b)) ==>
    SPEC X64_MODEL
       (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
        zPC (cb + n2w (2 * s1.pc)) * ~zS)
      ((cb + n2w (2 * s1.pc),x64 (2 * s1.pc) (THE (bc_fetch s1)))
       INSERT code_abbrevs cs)
      (zBC_HEAP (s1 with stack := bool_to_val b::s1.stack)
         (x,cs,stack,s,out) (cb,sb,ev,f2) *
       zPC s.local.stop_addr * ~zS \/ zHEAP_ERROR cs)``,
  Cases_on `b` \\ fs [x64_def]
  THEN1 (* Stop T *)
   (SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Stop_T) |> SPEC_ALL
                  |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL])
  THEN1 (* Stop F *)
   (SIMP_TAC (srw_ss()) [x64_def,bump_pc_def,zBC_HEAP_def,LET_DEF,MAP_APPEND,MAP]
    \\ SIMP_TAC std_ss [APPEND,HD,TL,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN (prepare zBC_Stop_F) |> SPEC_ALL
                  |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC (srw_ss()) []
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,TL,HD,x64_length_def,x64_def,
         LENGTH,x64_inst_length_def,LEFT_ADD_DISTRIB,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [SEP_DISJ_def]
    \\ Q.LIST_EXISTS_TAC [`x2`,`x3`]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ FULL_SIMP_TAC std_ss [HD,TL,bc_adjust_def,MAP,APPEND,
         isRefPtr_def,getRefPtr_def]
    \\ FULL_SIMP_TAC (srw_ss()) [word_mul_n2w,HD_CONS_TL]));

val LATER_def = Define `
  LATER p = NEXT (EVENTUALLY p)`;

val N_NEXT_def = Define `
  (N_NEXT 0 = I) /\
  (N_NEXT (SUC n) = NEXT o N_NEXT n)`;

val N_NEXT_THM = prove(
  ``!k p f s. N_NEXT k p f s <=> p f (\n. s (n + k))``,
  Induct \\ ASM_SIMP_TAC std_ss [N_NEXT_def,LATER_def,NEXT_def,EVENTUALLY_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  THEN1 (CONV_TAC (DEPTH_CONV ETA_CONV) \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC (srw_ss()) [ADD1,AC ADD_COMM ADD_ASSOC]);

val T_DISJ_def = Define `
  T_DISJ p q f s = (p f s) \/ (q f s):bool`;

val T_CONJ_def = Define `
  T_CONJ p q f s = (p f s) /\ (q f s):bool`;

(* SPEC_1 theorem *)

val zBC_HEAP_1 = prove(
  ``EVEN (w2n cb) /\ (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) ==>
    !s1 s2.
      bc_next s1 s2 ==> (s1.inst_length = x64_inst_length) /\
      (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
      SPEC_1 X64_MODEL
         (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
          zPC (cb + n2w (2 * s1.pc)) * ~zS)
        ((cb,x64_code 0 s1.code)
         INSERT code_abbrevs cs)
        (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
         zPC (cb + n2w (2 * s2.pc)) * ~zS) (zHEAP_ERROR cs)``,
  cheat) (* same as above but with SPEC_1 instead of SPEC *)
  |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM PULL_FORALL,GSYM CONJ_ASSOC]

val SPEC_N_def = Define `
  SPEC_N n model pre code post err <=>
     TEMPORAL model code
       (T_IMPLIES (NOW pre) (T_OR_F (N_NEXT n (EVENTUALLY (NOW post))) err))`

val zBC_HEAP_N = prove(
  ``!n s1 s2.
      NRC bc_next n s1 s2 ==> EVEN (w2n cb) /\
      (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) /\
      (s1.inst_length = x64_inst_length) /\
      (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
      SPEC_N n X64_MODEL
        (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
         zPC (cb + n2w (2 * s1.pc)) * ~zS)
        ((cb,x64_code 0 s1.code) INSERT code_abbrevs cs)
        (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
         zPC (cb + n2w (2 * s2.pc)) * ~zS) (zHEAP_ERROR cs)``,
  cheat) (* req some lemmas, but otherwise easy induction *)

val T_OR_F_thm = prove(
  ``T_OR_F p post = T_DISJ p (EVENTUALLY (NOW post))``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,T_OR_F_def,T_DISJ_def]);

val SPEC_IMP_SPEC_N = prove(
  ``SPEC model p c (q \/ err) ==> SPEC_N 0 model p c q err``,
  fs [SPEC_EQ_TEMPORAL,SPEC_N_def,N_NEXT_def,T_OR_F_thm,TEMPORAL_def]
  \\ PairCases_on `model` \\ fs [TEMPORAL_def,LET_DEF]
  \\ fs [T_IMPLIES_def,FUN_EQ_THM,EVENTUALLY_def,T_DISJ_def,NOW_def,SEP_CLAUSES]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1 METIS_TAC []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`state`,`seq'`,`r`]) \\ fs []
  \\ REVERSE (REPEAT STRIP_TAC) THEN1 METIS_TAC []
  \\ fs [SEP_REFINE_def,SEP_DISJ_def] \\ METIS_TAC []);

val SPEC_N_Stop =
  MATCH_MP SPEC_IMP_SPEC_N (UNDISCH zBC_HEAP_Stop)

val N_NEXT_thm = prove(
  ``!k p f s. N_NEXT k p f s = p f (\n. s (n + k))``,
  Induct \\ fs [N_NEXT_def,NEXT_def,ADD1,AC ADD_COMM ADD_ASSOC]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []);

val rel_sequence_shift = prove(
  ``!n seq' s. rel_sequence n seq' s ==> !i. rel_sequence n (\j. seq' (i + j)) (seq' i)``,
  REWRITE_TAC [rel_sequence_def] \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss []
  \\ Cases_on `?s. n (seq' (i + n')) s` \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [ADD1,ADD_ASSOC] \\ METIS_TAC []);

val SPEC_N_COMPOSE = prove(
  ``SPEC_N m model p2 c p3 err ==>
    SPEC_N n model p1 c p2 err ==>
    SPEC_N (m+n) model p1 c p3 err``,
  PairCases_on `model`
  \\ fs [SPEC_N_def,T_OR_F_thm,TEMPORAL_def,LET_DEF]
  \\ fs [T_IMPLIES_def,T_DISJ_def,EVENTUALLY_def,NOW_def]
  \\ fs [N_NEXT_thm,EVENTUALLY_def,NOW_def]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1 METIS_TAC []
  \\ Q.MATCH_ASSUM_RENAME_TAC `rel_sequence model1 s state` []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`state`,`s`,`r`]) \\ fs []
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC [] THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ IMP_RES_TAC rel_sequence_shift
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `k + n`)
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(s (k + n:num))`,`\j. s (k + n + j:num)`,`r`])
  \\ fs [] \\ REPEAT STRIP_TAC
  THEN1 (DISJ1_TAC \\ Q.EXISTS_TAC `k+k'` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (DISJ2_TAC \\ METIS_TAC [])
  THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `k+k'+n` \\ fs [AC ADD_COMM ADD_ASSOC])
  THEN1 (DISJ2_TAC \\ METIS_TAC []));

val zBYTECODE_DIVERGED_def = Define `
  zBYTECODE_DIVERGED output (cs,cb) =
    ALWAYS
     (EVENTUALLY
       (NOW (SEP_EXISTS bs x stack s sb ev f2.
               zBC_HEAP bs (x,cs,stack,s,output) (cb,sb,ev,f2) *
               zPC (cb + n2w (2 * bs.pc)) * ~zS)))`;

val EVENTUALLY_EVENTUALLY = prove(
  ``EVENTUALLY (EVENTUALLY p) = EVENTUALLY p``,
  SIMP_TAC std_ss [FUN_EQ_THM,EVENTUALLY_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `k' + k` \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ Q.LIST_EXISTS_TAC [`k`,`0`] \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]);

val TEMPORAL_WEAKEN_LEMMA = prove(
  ``TEMPORAL X64_MODEL code
      (T_IMPLIES p (T_DISJ (N_NEXT n (EVENTUALLY (NOW q1))) q2)) /\
    (!r1 r2 t2. SEP_REFINE (q1 * r1 * r2) X64_ICACHE x64_2set t2 ==>
                SEP_REFINE (q3 * r1 * r2) X64_ICACHE x64_2set t2) ==>
    TEMPORAL X64_MODEL code
      (T_IMPLIES p (T_DISJ (N_NEXT n (EVENTUALLY (NOW q3))) q2))``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [X64_MODEL_def]
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,T_DISJ_def,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,SEP_IMP_def,
       N_NEXT_THM,NOW_def,SPEC_N_def,T_OR_F_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC [])
  |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO]

val SPEC_N_WEAKEN = prove(
  ``(!r1 r2 t2.
      SEP_REFINE (q1 * r1 * r2) X64_ICACHE x64_2set t2 ==>
      SEP_REFINE (q3 * r1 * r2) X64_ICACHE x64_2set t2) /\
    SPEC_N n X64_MODEL p code q1 q2 ==>
    SPEC_N n X64_MODEL p code q3 q2``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [X64_MODEL_def]
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,T_DISJ_def,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def,SEP_IMP_def,
       N_NEXT_THM,NOW_def,SPEC_N_def,T_OR_F_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ METIS_TAC []);

val FORALL_TEMPORAL_N_NEXT_IMP_ALWAYS = prove(
  ``(!n. TEMPORAL model code (T_IMPLIES p (T_DISJ (N_NEXT n q) r))) ==>
    TEMPORAL model code (T_IMPLIES p (T_DISJ (ALWAYS q) r))``,
  REPEAT STRIP_TAC
  \\ `?x1 x2 x3 x4 x5. model = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [TEMPORAL_def,LET_DEF,PULL_FORALL,T_DISJ_def,
       AND_IMP_INTRO,T_IMPLIES_def,ALWAYS_def,EVENTUALLY_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `r (\p state. SEP_REFINE (p * CODE_POOL x3 code * r')
                    x4 x1 state \/ x5 state) seq'` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [N_NEXT_THM]);

val bc_diverges_def = Define `
  bc_diverges s = !n. ?s2. NRC bc_next n s s2`;

val zBC_HEAP_DIVERGES = let
  val lemma =
    SPEC_N_WEAKEN
    |> Q.INST [`q1`|->`zBC_HEAP bs (x,cs,stack,s,output) (cb,sb,ev,f2) *
                       zPC (cb + n2w (2 * bs.pc)) * ~zS`]
    |> Q.INST [`q3`|->`SEP_EXISTS bs x stack s sb ev f2.
                         zBC_HEAP bs (x,cs,stack,s,output) (cb,sb,ev,f2) *
                         zPC (cb + n2w (2 * bs.pc)) * ~zS`]
    |> RW [GSYM AND_IMP_INTRO]
  val lemma2 = prove(lemma |> concl |> dest_imp |> fst,
    fs [SEP_REFINE_def,SEP_CLAUSES,SEP_EXISTS_THM] \\ METIS_TAC []);
  val lemma3 = MP lemma lemma2
  val lemma4 = prove(
    ``(!n s2. NRC bc_next n s1 s2 ==> P n s1) ==>
      ((!n. ?s2. NRC bc_next n s1 s2) ==> !n. P n s1)``,
    METIS_TAC []);
  in
  zBC_HEAP_N
  |> SPEC_ALL
  |> UNDISCH_ALL
  |> MATCH_MP lemma3
  |> DISCH ``NRC bc_next n s1 s2``
  |> Q.GENL [`s2`,`n`]
  |> HO_MATCH_MP lemma4
  |> RW [GSYM bc_diverges_def]
  |> UNDISCH_ALL
  |> RW [SPEC_N_def,T_OR_F_thm]
  |> MATCH_MP FORALL_TEMPORAL_N_NEXT_IMP_ALWAYS
  |> RW [GSYM zBYTECODE_DIVERGED_def]
  end

val full_s_def = Define `
  full_s init = first_s init with
    <|handler := 1;
      local := (first_s init).local with printing_on := 0x1w|>`;

val init_bc_state_def = Define `
  init_bc_state s =
    s with <| stack := [];
              handler := 0;
              refs := FEMPTY;
              output := "" |>`

val ref_adjust_FEMPTY = prove(
  ``ref_adjust (p,x,ev) FEMPTY = FEMPTY``,
  SIMP_TAC (srw_ss()) [ref_adjust_def,LET_DEF]);

val zHEAP_SET_STOP_TO_TERMINATE = let
  val (_,_,code1,_) = zHEAP_TERMINATE |> Q.INST [`p`|->`p+6w`]
    |> SIMP_RULE (srw_ss()) [] |> concl |> dest_spec
  val (_,_,code2,_) = zHEAP_SET_STOP_ADDR
    |> SIMP_RULE (srw_ss()) [] |> concl |> dest_spec
in
  zHEAP_SET_STOP_ADDR
  |> MATCH_MP SPEC_SUBSET_CODE
  |> SPEC ``^code1 UNION ^code2``
  |> SIMP_RULE (srw_ss()) [INSERT_SUBSET,INSERT_UNION_EQ]
  |> Q.INST [`imm32`|->`15w`]
  |> SIMP_RULE (srw_ss()) [IMM32_def]
  |> SORT_CODE
end

val full_s_with_stop_def = Define `
  full_s_with_stop init stop_addr =
    full_s init with
         local := (full_s init).local with stop_addr := stop_addr`;

val zBC_HEAP_INIT = let
  val th0 = SPEC_COMPOSE_RULE [zHEAP_INIT,zHEAP_ABBREVS,zHEAP_PUSH1,
              zHEAP_SET_PRINTING_ON,zWRITE_HANDLER,zHEAP_POP1,zHEAP_SET_STOP_TO_TERMINATE]
            |> SIMP_RULE std_ss [LENGTH,HD,TL,NOT_CONS_NIL,SEP_CLAUSES,GSYM full_s_def,
                 GSYM full_s_with_stop_def]
  val tm = find_term (can (match_term ``full_s_with_stop xx yy``)) (concl th0)
  val pc = get_pc th0
  val (th,goal) = SPEC_WEAKEN_RULE th0
    ``(zBC_HEAP (init_bc_state i) (Number 0,full_cs init p,[],^tm,"")
              (cb,cs.stack_trunk - 0x8w,ev,FEMPTY) * ^pc * ~zS)``
(*
  gg goal
*)
  val lemma = prove(goal,
    fs [zBC_HEAP_def,SEP_CLAUSES,init_bc_state_def,LET_DEF,HD,TL,ref_adjust_FEMPTY]
    \\ fs [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`Number 0`,`Number 0`] \\ fs []
    \\ `^tm with <|output := ""; handler := 1|> = ^tm` by ALL_TAC
    THEN1 EVAL_TAC \\ fs [AC STAR_ASSOC STAR_COMM]);
  val th = MP th lemma
  in th end



(*

  zBC_HEAP_DIVERGES |> DISCH_ALL |> Q.GEN `sb`
  |> Q.INST [`stack`|->`[]`,`f2`|->`FEMPTY`]
  |> SIMP_RULE std_ss [LENGTH,FDOM_FEMPTY,NOT_IN_EMPTY]

  zBC_HEAP_INIT





  zBC_HEAP_def

  first_s_def
  local_zero_def

fetch "-" "full_cs_def"
fetch "-" "first_cs_def"

*)

(* COMMENT

zHEAP_TERMINATE

val TEMPORAL_zBC_HEAP_THM = prove(
  ``EVEN (w2n cb) /\
    (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) ==>
    !s1 s2.
      bc_next s1 s2 ==>
      (s1.inst_length = x64_inst_length) /\
      (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
      TEMPORAL X64_MODEL
        ((cb, x64_code 0 s1.code) INSERT code_abbrevs cs)
        (T_IMPLIES
          (NOW
             (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
              zPC (cb + n2w (2 * s1.pc)) * ~zS))
          (LATER
             (NOW
                (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
                 zPC (cb + n2w (2 * s2.pc)) * ~zS \/ zHEAP_ERROR cs))))``,
  cheat); (* with a few hacks, this should follow from theorem above *)

val TEMPORAL_zBC_HEAP_ALT = prove(
  ``EVEN (w2n cb) /\ (cb = cs.code_heap_ptr) /\
    (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) /\
    (s.code = x64_code 0 s1.code ++ extra) /\
    (s.code_mode = SOME T) ==>
    !s1 s2.
      bc_next s1 s2 ==>
      (s1.inst_length = x64_inst_length) /\
      (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
      TEMPORAL X64_MODEL (code_abbrevs cs)
        (T_IMPLIES
          (NOW
             (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
              zPC (cb + n2w (2 * s1.pc)) * ~zS))
          (LATER
             (NOW
                (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
                 zPC (cb + n2w (2 * s2.pc)) * ~zS \/ zHEAP_ERROR cs))))``,
  cheat); (* with a few hacks, this should follow from theorem above *)

val TEMPORAL_NRC_zBC_HEAP_THM = prove(
  ``EVEN (w2n cb) /\ (cb = cs.code_heap_ptr) /\
    (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) /\
    (s.code = x64_code 0 s1.code ++ end_of_code) /\
    (s.code_mode = SOME T) ==>
    !n s1 s2.
      NRC bc_next n s1 s2 ==>
      (s1.inst_length = x64_inst_length) /\
      (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
      TEMPORAL X64_MODEL (code_abbrevs cs)
        (T_IMPLIES
          (NOW
             (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
              zPC (cb + n2w (2 * s1.pc)) * ~zS))
          (T_DISJ (N_NEXT n
             (EVENTUALLY (NOW
                (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
                 zPC (cb + n2w (2 * s2.pc)) * ~zS))))
             (EVENTUALLY (NOW (zHEAP_ERROR cs)))))``,
  cheat); (* with a few hacks, this should follow from theorem above *)

val zBC_HEAP_DIVERGES = prove(
  ``(!n. ?s2. NRC bc_next n s1 s2 /\ (s2.output = "")) ==>
    (cb = cs.code_heap_ptr) /\ EVEN (w2n cb) /\
    (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) /\
    (s.code = x64_code 0 s1.code ++ end_of_code) /\
    (s.code_mode = SOME T) /\
    (s1.inst_length = x64_inst_length) /\
    (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
    TEMPORAL X64_MODEL (code_abbrevs cs)
      (T_IMPLIES
        (NOW
           (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
            zPC (cb + n2w (2 * s1.pc)) * ~zS))
        (T_DISJ (zREPL_DIVERGED out (cs,cb))
                (EVENTUALLY (NOW (zHEAP_ERROR cs)))))``,
  SIMP_TAC std_ss [zREPL_DIVERGED_def]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC FORALL_TEMPORAL_N_NEXT_IMP_ALWAYS
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC
  \\ FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `n:num`)
  \\ REPEAT STRIP_TAC
  \\ MP_TAC (TEMPORAL_NRC_zBC_HEAP_THM |> SIMP_RULE std_ss [PULL_FORALL]
               |> SPEC_ALL |> Q.INST [`s1'`|->`s1`])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC TEMPORAL_WEAKEN_LEMMA
  \\ SIMP_TAC std_ss [SEP_REFINE_def]
  \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `s'`
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
  \\ METIS_TAC []);

val zBC_HEAP_TERMINATES_end_of_code = prove(
  ``(bc_eval s1 <> NONE) /\ code_executes_ok s1 ==>
    (cb = cs.code_heap_ptr) /\ EVEN (w2n cb) /\
    (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) /\
    (s.code = x64_code 0 s1.code ++ end_of_code) /\
    (s.code_mode = SOME T) /\
    (s1.inst_length = x64_inst_length) /\
    (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
    TEMPORAL X64_MODEL (code_abbrevs cs)
      (T_IMPLIES
        (NOW
           (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
            zPC (cb + n2w (2 * s1.pc)) * ~zS))
        (EVENTUALLY (NOW
           (zBC_HEAP_1 (THE (bc_eval s1))
              (bool_to_val (bc_fetch (THE (bc_eval s1)) = SOME Stop))
              (x,cs,stack,s,out) (cb,sb,ev,f2) *
            zPC s.local.stop_addr * ~zS * cond (bc_eval s1 <> NONE) \/
            zHEAP_ERROR cs))))``,
  cheat); (* easy-ish *)

val TEMPORAL_COMBINE_LEMMA = prove(
  ``(b_div ==> bb ==> TEMPORAL model code (T_IMPLIES p q1)) /\
    (b_term /\ code_ok ==> bb ==> TEMPORAL model code (T_IMPLIES p q2)) ==>
    (code_ok ==> b_div \/ b_term) ==>
    code_ok /\ bb ==>
    TEMPORAL model code (T_IMPLIES p (T_DISJ q1 q2))``,
  Q.SPEC_TAC (`model`,`model`)
  \\ SIMP_TAC std_ss [TEMPORAL_def,FORALL_PROD,T_IMPLIES_def,T_DISJ_def,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC []);

val code_executes_ok_lemma = prove(
  ``(s1.output = "") ==>
    code_executes_ok s1 ==>
    (!n. ?s2. NRC bc_next n s1 s2 /\ (s2.output = "")) \/
    bc_eval s1 <> NONE``,
  SIMP_TAC std_ss [repl_fun_alt_proofTheory.code_executes_ok_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ DISJ2_TAC
  \\ `!s3. ~(bc_next s2 s3)` by ALL_TAC
  \\ IMP_RES_TAC bytecodeEvalTheory.RTC_bc_next_bc_eval
  \\ FULL_SIMP_TAC std_ss []
  THEN1 (ONCE_REWRITE_TAC [bc_next_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ REVERSE (`bc_fetch s2 = NONE` by ALL_TAC)
  THEN1 (ONCE_REWRITE_TAC [bc_next_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ ASM_SIMP_TAC std_ss [bc_fetch_def]
  \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_preserves
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.SPEC_TAC (`s1.inst_length`,`l`)
  \\ Q.SPEC_TAC (`s1.code`,`xs`)
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct \\ FULL_SIMP_TAC std_ss [bc_fetch_aux_def,MAP,SUM]);

val TEMPORAL_FULL_BC_EXEC = let
  val lemma = MATCH_MP TEMPORAL_COMBINE_LEMMA
      (CONJ zBC_HEAP_DIVERGES zBC_HEAP_TERMINATES_end_of_code)
  val th = MATCH_MP lemma (UNDISCH code_executes_ok_lemma)
             |> DISCH_ALL |> RW [AND_IMP_INTRO]
  in th end

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
  ``EVEN (w2n cb) /\ (cs.stack_trunk - n2w (8 * SUC (LENGTH stack)) = sb) ==>
    !s1 s2.
      bc_next^* s1 s2 ==>
      ((s1.inst_length = x64_inst_length) ==>
       (!r. r IN FDOM f2 ==> if ev then ODD r else EVEN r) ==>
       SPEC X64_MODEL
         (zBC_HEAP s1 (x,cs,stack,s,out) (cb,sb,ev,f2) *
          zPC (cb + n2w (2 * s1.pc)) * ~zS)
         ((cb, x64_code 0 s1.code) INSERT code_abbrevs cs)
         (zBC_HEAP s2 (x,cs,stack,s,out) (cb,sb,ev,f2) *
          zPC (cb + n2w (2 * s2.pc)) * ~zS \/
          zHEAP_ERROR cs))``,
  cheat);
(*
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
  \\ (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
      |> MATCH_MP_TAC)
  \\ Q.EXISTS_TAC `(zBC_HEAP s3 (x,cs,stack,s,out) (cb,sb,ev,f2) *
       zPC (cb + n2w (2 * s3.pc)) * ~zS \/ zHEAP_ERROR (cs))`
  \\ REVERSE CONJ_TAC THEN1
   (MATCH_MP_TAC SEP_IMP_DISJ \\ FULL_SIMP_TAC std_ss [SEP_IMP_REFL]
    \\ FULL_SIMP_TAC std_ss [zHEAP_ERROR_def,SEP_IMP_def,SEP_EXISTS_THM])
  \\ Q.PAT_ASSUM `SPEC xx yy tt rr` MP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ (SPEC_SUBSET_CODE |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
        |> RW1 [CONJ_COMM] |> RW [GSYM AND_IMP_INTRO] |> MATCH_MP_TAC)
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,IN_INSERT]
  \\ SIMP_TAC std_ss [SUBSET_DEF,IN_INSERT]);
*)

(* printing a string (the error message, e.g. type error) *)

val (x64_print_str_spec,x64_print_str_def,x64_print_str_pre_def) = x64_compile `
  x64_print_str (x1,x2,x3,s) =
    if isSmall x1 then (x1,x2,x3,s) else
      let x3 = x1 in
      let x2 = Number 0 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in
      let s = s with output :=
           STRCAT s.output (STRING (CHR (Num (getNumber x1))) "") in
      let x1 = x3 in
      let x2 = Number 1 in
      let x1 = EL (Num (getNumber x2)) (getContent x1) in
      let x3 = Number 1 in
        x64_print_str (x1,x2,x3,s)`

val x64_print_str_thm = prove(
  ``!xs x2 x3 s. ?y2 y3.
      x64_print_str_pre (BlockList (MAP Chr xs),x2,x3,s) /\
      (x64_print_str (BlockList (MAP Chr xs),x2,x3,s) =
         (BlockList [],y2,y3,s with output := STRCAT s.output xs))``,
  Induct THEN1
   (ONCE_REWRITE_TAC [x64_print_str_def,x64_print_str_pre_def]
    \\ SIMP_TAC std_ss [isSmall_def,BlockList_def,MAP,BlockNil_def]
    \\ EVAL_TAC \\ Cases \\ SRW_TAC [] (TypeBase.updates_of ``:zheap_state``))
  \\ SIMP_TAC std_ss [BlockList_def,MAP,Chr_def,BlockCons_def]
  \\ ONCE_REWRITE_TAC [x64_print_str_def,x64_print_str_pre_def]
  \\ SIMP_TAC std_ss [isSmall_def,BlockList_def,MAP,BlockNil_def]
  \\ SIMP_TAC (srw_ss()) [LET_DEF,getNumber_def,getContent_def,EL,isBlock_def,
       canCompare_def,isNumber_def,ORD_BOUND]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o
       Q.SPECL [`Number 1`,`Number 1`,
       `s with output := STRCAT s.output (STRING (CHR (ORD h)) "")`])
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [BlockList_def,BlockNil_def]
  \\ Cases_on `s` \\ SIMP_TAC std_ss [CHR_ORD]
  \\ SRW_TAC [] (TypeBase.updates_of ``:zheap_state``));

val (x64_print_string_spec,x64_print_string_def,x64_print_string_pre_def) = x64_compile `
  x64_print_string (x1,x2,x3,s,stack) =
    let stack = x2::stack in
    let stack = x3::stack in
    let (x1,x2,x3,s) = x64_print_str (x1,x2,x3,s) in
    let (x3,stack) = (HD stack, TL stack) in
    let (x2,stack) = (HD stack, TL stack) in
      (x1,x2,x3,s,stack)`

val x64_print_string_thm = prove(
  ``(x1 = BlockList (MAP Chr xs)) ==>
    x64_print_string_pre (x1,x2,x3,s,stack) /\
    (x64_print_string (x1,x2,x3,s,stack) =
       (BlockList [],x2,x3,s with output := STRCAT s.output xs,stack))``,
  SIMP_TAC std_ss [x64_print_string_def,LET_DEF,x64_print_string_pre_def,HD,TL]
  \\ REPEAT STRIP_TAC
  \\ ASSUME_TAC x64_print_str_thm \\ SEP_I_TAC "x64_print_str"
  \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL]);

val zHEAP_PRINT_STRING = x64_print_string_spec
    |> RW [UNDISCH x64_print_string_thm]
    |> SIMP_RULE std_ss [LET_DEF,SEP_CLAUSES]
    |> DISCH_ALL |> RW [GSYM SPEC_MOVE_COND]



(* eval bootstrap i.e. repl_decs *)

val ref_adjust_FEMPTY = prove(
  ``ref_adjust (p,x,ev) FEMPTY = FEMPTY``,
  SIMP_TAC (srw_ss()) [ref_adjust_def,LET_DEF]);

val repl_decs_inst_lemma = prove(
  ``(!s2.
       EVEN (w2n p) ∧ bc_next^* (strip_labels bs) s2 ∧
       (bs.inst_length = x64_inst_length) ∧
       (bs.code = REVERSE bootstrap_lcode) ∧ (bs.pc = 0) ∧ (bs.stack = []) ∧
       (bs.clock = NONE) ∧ (bs.refs = FEMPTY) ⇒
       SPEC m pre c (q s2.pc s2)) ==>
    EVEN (w2n p) ∧
    (bs.inst_length = x64_inst_length) ∧
    (bs.code = REVERSE bootstrap_lcode) ∧ (bs.pc = 0) ∧ (bs.stack = []) ∧
    (bs.clock = NONE) ∧ (bs.refs = FEMPTY) ⇒
    SPEC m pre c (SEP_EXISTS rd s2.
       q (next_addr bs.inst_length (strip_labels bs).code) (strip_labels s2) *
       cond (env_rs [] (repl_decs_cenv ++ init_envC) (0,repl_decs_s)
               repl_decs_env new_compiler_state 0 rd s2 /\
             (s2.inst_length = x64_inst_length)))``,
  REPEAT STRIP_TAC
  \\ MP_TAC (bootstrap_lemmasTheory.bc_eval_bootstrap_lcode |> Q.SPEC `bs`)
  \\ FULL_SIMP_TAC std_ss [length_ok_x64_inst_length]
  \\ REPEAT STRIP_TAC
  \\ `bc_next^* (strip_labels bs) (strip_labels bs')` by ALL_TAC
  THEN1 (IMP_RES_TAC bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next)
  \\ RES_TAC
  \\ (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO]
      |> GEN_ALL |> MATCH_MP_TAC)
  \\ Q.EXISTS_TAC `(q bs'.pc (strip_labels bs'))`
  \\ FULL_SIMP_TAC std_ss []
  \\ `(strip_labels bs').pc = bs'.pc` by
       FULL_SIMP_TAC (srw_ss()) [bytecodeLabelsTheory.strip_labels_def]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC THEN1 METIS_TAC []
  \\ Q.LIST_EXISTS_TAC [`rd`,`bs'`]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_preserves
  \\ FULL_SIMP_TAC (srw_ss()) [bytecodeLabelsTheory.strip_labels_def]);

val first_s_lemma = prove(
  ``first_s init with <|output := ""; handler := 2|> = first_s init``,
  cheat); (* first_s needs adjusting to have handler = 2 *)

val x64_bootstrap_code_def = Define `
  x64_bootstrap_code =
    x64_code 0 (code_labels x64_inst_length (REVERSE bootstrap_lcode))`

val next_addr_x64_inst_length_bootstrap = prove(
  ``(2 * next_addr x64_inst_length (REVERSE bootstrap_lcode) =
    LENGTH x64_bootstrap_code) /\
    (2 * next_addr x64_inst_length
      (code_labels x64_inst_length (REVERSE bootstrap_lcode)) =
    LENGTH x64_bootstrap_code)``,
  cheat);

val zBC_HEAP_with_code = prove(
  ``zBC_HEAP (s2 with code := xx) = zBC_HEAP s2``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [zBC_HEAP_def]);

val SPEC_repl_decs =
  zBC_HEAP_RTC
    |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL |> Q.GEN `sb`
    |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
    |> Q.INST [`cb`|->`p`,`s1`|->`(strip_labels bs)`,`stack`|->`[Number 0]`,`f2`|->`FEMPTY`,
               `s`|->`first_s init`,`ev`|->`T`,`out`|->`""`]
    |> SIMP_RULE std_ss [LENGTH,Once zBC_HEAP_def]
    |> UNDISCH
    |> DISCH ``(bs.code = REVERSE bootstrap_lcode) /\
               (bs.pc = 0) /\ (bs.stack = []) /\ (bs.clock = NONE) /\
               (bs.refs = FEMPTY)``
    |> SIMP_RULE (srw_ss()) [bytecodeLabelsTheory.strip_labels_def,LET_DEF]
    |> DISCH_ALL
    |> SIMP_RULE (srw_ss()) [SEP_CLAUSES,GSYM SPEC_PRE_EXISTS,ref_adjust_FEMPTY,
          EVAL ``(first_s init).local.printing_on``,PULL_FORALL] |> SPEC_ALL
    |> RW [AND_IMP_INTRO,GSYM CONJ_ASSOC,
           SIMP_CONV (srw_ss()) [bytecodeLabelsTheory.strip_labels_def]
             ``(strip_labels bs).inst_length``] |> Q.GEN `s2`
    |> HO_MATCH_MP repl_decs_inst_lemma
    |> Q.INST [`bs`|->`<| inst_length := x64_inst_length ;
                          code := REVERSE bootstrap_lcode ; handler := 0 ;
                          pc := 0; stack := [] ; clock := NONE ; refs := FEMPTY |>`]
    |> SIMP_RULE (srw_ss()) [bytecodeLabelsTheory.strip_labels_def,first_s_lemma]
    |> RW [GSYM SPEC_MOVE_COND,GSYM x64_bootstrap_code_def,
         next_addr_x64_inst_length_bootstrap]
    |> SIMP_RULE std_ss [SEP_CLAUSES,zBC_HEAP_with_code]


(* instantiation of lcode *)

val COMPILER_RUN_INV_IMP = prove(
  ``((bs.code = REVERSE bootstrap_lcode ++ REVERSE call_lcode ++ [Stack Pop]) ==>
     b) ==>
    (COMPILER_RUN_INV bs inp outp ==> b)``,
  SIMP_TAC std_ss [bootstrap_lemmasTheory.COMPILER_RUN_INV_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC);

val x64_code_eval_lemmas = LIST_CONJ [
    ``x64_code n [Stack Pop]``
    |> SIMP_CONV std_ss [x64_code_eval],
    ``x64_code n (REVERSE call_lcode)``
    |> (SIMP_CONV std_ss [compileCallReplStepDecTheory.call_lcode_def,
          x64_code_eval,REVERSE_DEF,APPEND,GSYM APPEND_ASSOC] THENC EVAL),
    ``2 * next_addr x64_inst_length (REVERSE call_lcode)``
    |> (SIMP_CONV std_ss [compileCallReplStepDecTheory.call_lcode_def,
          x64_code_eval,REVERSE_DEF,APPEND,GSYM APPEND_ASSOC] THENC EVAL),
    ``2 * next_addr x64_inst_length [Stack Pop]``
    |> (SIMP_CONV std_ss [compileCallReplStepDecTheory.call_lcode_def,
          x64_code_eval,REVERSE_DEF,APPEND,GSYM APPEND_ASSOC] THENC EVAL)]

val strip_labels_code =
  ``(strip_labels bs).code``
  |> SIMP_CONV (srw_ss()) [bytecodeLabelsTheory.strip_labels_def,LET_DEF]

val code_labels_APPEND_CALL = prove(
  ``code_labels l (xs ++ (REVERSE call_lcode ++ [Stack Pop])) =
    code_labels l xs ++ (REVERSE call_lcode ++ [Stack Pop])``,
  cheat);

val strip_labels_ignore = prove(
  ``((strip_labels bs).inst_length = bs.inst_length) /\
    ((strip_labels bs).pc = bs.pc)``,
  SRW_TAC [] [bytecodeLabelsTheory.strip_labels_def]);

val zBC_HEAP_strip = prove(
  ``(zBC_HEAP (strip_labels bs) = zBC_HEAP bs) /\
    (zBC_HEAP (bs with pc := code_start bs) = zBC_HEAP bs) /\
    ((strip_labels (bs with pc := code_start bs)).code = (strip_labels bs).code) /\
    ((strip_labels (bs with pc := code_start bs)).inst_length = bs.inst_length) /\
    ((strip_labels (bs with pc := code_start bs)).pc = code_start bs)``,
  SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [zBC_HEAP_def,
       bytecodeLabelsTheory.strip_labels_def]);

val SPEC_X64_SEPARATE_CODE = prove(
  ``SPEC X64_MODEL p ((a1,xs ++ ys) INSERT s) q ==>
    SPEC X64_MODEL p ((a1,xs) INSERT (a1 + n2w (LENGTH xs),ys) INSERT s) q``,
  cheat);

val COMPILER_RUN_INV_OUTPUT_def = Define `
  COMPILER_RUN_INV_OUTPUT bs2 x =
    ?inp2 out2. COMPILER_RUN_INV bs2 inp2 out2 /\
                OUTPUT_TYPE x out2`;

val v_no_sp_def = tDefine "v_no_sp" `
  (v_no_sp (StackPtr s) = F) /\
  (v_no_sp (Block tag xs) = EVERY v_no_sp xs) /\
  (v_no_sp _ = T)`
 (WF_REL_TAC `measure (bc_value_size)`
  \\ Induct_on `xs`
  \\ FULL_SIMP_TAC (srw_ss()) [bc_value_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (ASSUME_TAC o SPEC_ALL)
  \\ DECIDE_TAC)

val v_no_sp_ind = fetch "-" "v_no_sp_ind"

val v_no_ref_def = tDefine "v_no_ref" `
  (v_no_ref (RefPtr s) = F) /\
  (v_no_ref (Block tag xs) = EVERY v_no_ref xs) /\
  (v_no_ref _ = T)`
 (WF_REL_TAC `measure (bc_value_size)`
  \\ Induct_on `xs`
  \\ FULL_SIMP_TAC (srw_ss()) [bc_value_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (ASSUME_TAC o SPEC_ALL)
  \\ DECIDE_TAC)

val bs_no_sp_def = Define `
  bs_no_sp bs =
    EVERY v_no_sp bs.stack /\ FEVERY (v_no_sp o SND) bs.refs`;

val v_no_sp_bc_adjust = prove(
  ``!v. v_no_sp v ==> (bc_adjust (cb,sb,ev) v = bc_adjust (cb,0w,ev) v)``,
  HO_MATCH_MP_TAC v_no_sp_ind
  \\ FULL_SIMP_TAC (srw_ss()) [bc_adjust_def,v_no_sp_def,EVERY_MEM,MAP_EQ_f]);

val bs_no_sp_zBC_HEAP = prove(
  ``bs_no_sp bs ==>
      (zBC_HEAP bs (x,cs,stack,s,out) (cb,sb,ev,f2) =
       zBC_HEAP bs (x,cs,stack,s,out) (cb,0w,ev,f2))``,
  STRIP_TAC \\ SIMP_TAC std_ss [zBC_HEAP_def,LET_DEF]
  \\ `(ref_adjust (cb,sb,ev) bs.refs =
       ref_adjust (cb,0w,ev) bs.refs) /\
      (MAP (bc_adjust (cb,sb,ev)) bs.stack =
       MAP (bc_adjust (cb,0x0w,ev)) bs.stack)` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ref_adjust_def,LET_DEF,MAP_EQ_f,
       bs_no_sp_def,EVERY_MEM,FEVERY_DEF,v_no_sp_bc_adjust]
  \\ FULL_SIMP_TAC std_ss [fmap_EXT]
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [])
  \\ REPEAT STRIP_TAC
  \\ `x IN (IMAGE (\n. if ev then 2 * n else 2 * n + 1) (FDOM bs.refs))` by
       (FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  \\ `FINITE (IMAGE (\n. if ev then 2 * n else 2 * n + 1) (FDOM bs.refs))` by
       (FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [FUN_FMAP_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `((if ev then 2 * n else (2 * n + 1)) DIV 2) = n` by ALL_TAC THEN1
   (Cases_on `ev` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [v_no_sp_bc_adjust]);

val repl_decs_step_inst_lemma = prove(
  ``(!s2.
       INPUT_TYPE x1 inp ∧ bs_no_sp bs /\
       COMPILER_RUN_INV bs inp outp ∧ EVEN (w2n p) ∧
       bc_next^* (strip_labels (bs with pc := code_start bs)) s2 ∧
       (bs.inst_length = x64_inst_length) ∧ (∀r. r ∈ FDOM f2 ⇒ ODD r) ⇒
       SPEC m pre c (q s2.pc s2)) ==>
    INPUT_TYPE x1 inp ∧ bs_no_sp bs /\ COMPILER_RUN_INV bs inp outp ∧ EVEN (w2n p) ∧
    (bs.inst_length = x64_inst_length) ∧ (∀r. r ∈ FDOM f2 ⇒ ODD r) ⇒
    SPEC m pre c (SEP_EXISTS bs2.
       q (code_end bs) (strip_labels bs2) *
       cond (COMPILER_RUN_INV_OUTPUT bs2 (repl_step x1) /\
             (bs2.inst_length = x64_inst_length) /\ bs_no_sp bs2))``,
  REPEAT STRIP_TAC
  \\ MP_TAC (bootstrap_lemmasTheory.COMPILER_RUN_INV_repl_step
             |> Q.INST [`x`|->`x1`,`bs1`|->`bs`,`inp1`|->`inp`,`out1`|->`outp`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ IMP_RES_TAC bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next
  \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC bytecodeLabelsTheory.bc_next_strip_labels_RTC
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [length_ok_x64_inst_length]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ POP_ASSUM MP_TAC
  \\ `(strip_labels bs2).pc = bs2.pc` by
       FULL_SIMP_TAC (srw_ss()) [bytecodeLabelsTheory.strip_labels_def]
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ (SPEC_WEAKEN |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO] |> GEN_ALL
       |> MATCH_MP_TAC)
  \\ Q.EXISTS_TAC `(q bs2.pc (strip_labels bs2))` \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR,
       COMPILER_RUN_INV_OUTPUT_def,PULL_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`bs2`,`inp2`,`out2`]
  \\ IMP_RES_TAC bytecodeExtraTheory.RTC_bc_next_preserves
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ cheat (* COMPILER_RUN_INV_repl_step needs to assert `bs_no_sp bs2` *));

val next_addr_APPEND = prove(
  ``!xs ys. next_addr l (xs ++ ys) = next_addr l xs + next_addr l ys``,
  Induct \\ SRW_TAC [] [ADD_ASSOC]);

val zBC_HEAP_remove_sb = prove(
  ``(zBC_HEAP bs2 (x,cs,stack,s,out) (pp,anything,T,f2) * zPC p * ¬zS \/
     zHEAP_ERROR cs) * cond (b1 ∧ b2 ∧ bs_no_sp bs2) =
    (zBC_HEAP bs2 (x,cs,stack,s,out) (pp,0w,T,f2) * zPC p * ¬zS \/
     zHEAP_ERROR cs) * cond (b1 ∧ b2 ∧ bs_no_sp bs2)``,
  Cases_on `bs_no_sp bs2` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ METIS_TAC [bs_no_sp_zBC_HEAP]);

val SPEC_repl_step =
  zBC_HEAP_RTC
    |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL |> Q.GEN `sb`
    |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
    |> Q.INST [`ev`|->`T`,`s1`|->
         `(strip_labels (bs with pc := code_start bs))`,
          `cb`|->`p`]
    |> SIMP_RULE std_ss [zBC_HEAP_strip]
    |> SIMP_RULE std_ss [code_start_def,next_addr_x64_inst_length_bootstrap]
    |> DISCH ``(bs.code = REVERSE bootstrap_lcode ++
                 REVERSE call_lcode ++ [Stack Pop])``
    |> SIMP_RULE std_ss [strip_labels_code,GSYM APPEND_ASSOC,code_labels_APPEND_CALL]
    |> SIMP_RULE std_ss [code_labels_APPEND_CALL]
    |> SIMP_RULE std_ss [x64_code_APPEND,x64_code_eval_lemmas,APPEND]
    |> SIMP_RULE std_ss [APPEND_ASSOC]
    |> MATCH_MP COMPILER_RUN_INV_IMP
    |> SIMP_RULE std_ss [strip_labels_ignore,GSYM x64_bootstrap_code_def]
    |> SIMP_RULE std_ss [GSYM code_start_def]
    |> DISCH ``INPUT_TYPE x1 inp /\ bs_no_sp bs``
    |> SIMP_RULE std_ss [Once bs_no_sp_zBC_HEAP]
    |> RW [AND_IMP_INTRO,GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> MATCH_MP SPEC_X64_SEPARATE_CODE |> DISCH_ALL |> Q.GEN `s2`
    |> HO_MATCH_MP repl_decs_step_inst_lemma
    |> SIMP_RULE std_ss [code_end_def,next_addr_APPEND,LEFT_ADD_DISTRIB]
    |> RW [next_addr_x64_inst_length_bootstrap,x64_code_eval_lemmas]
    |> SIMP_RULE std_ss [GSYM ADD_ASSOC]
    |> RW [GSYM word_arith_lemma1]
    |> RW [GSYM SPEC_MOVE_COND]
    |> Q.INST [`p`|->`p - n2w (LENGTH x64_bootstrap_code)`]
    |> RW [WORD_SUB_ADD,zBC_HEAP_strip]
    |> RW1 [zBC_HEAP_remove_sb]

(*
SPEC_repl_step
    |> RW [zBC_HEAP_def]
    |> SIMP_RULE std_ss [SEP_CLAUSES]
*)

fun new_write_code_to_file filename th = let
  val _ = print ("Extracting code to file \"" ^ filename ^ "\" ... ")
  (* extract code from th *)
  val (m,pre,c,post) = (dest_spec o concl) th
  val cs = (list_dest pred_setSyntax.dest_insert c)
  val _ = pred_setSyntax.is_empty (last cs) orelse
          (print ("\n\nCode does not end in empty set. Found:\n\n"^
                  (term_to_string (last cs)) ^"\n\n"); fail())
  val cs = butlast cs
  (* turn into ML *)
  val p = hd cs |> rator |> free_vars |> hd
  val pat = ``^p + n2w m``
  fun dest_pc_plus_offset tm =
    if tm = p then 0 else
      let
        val (x,y) = wordsSyntax.dest_word_add tm
        val _ = if x = p then () else fail ()
        val n = y |> wordsSyntax.dest_n2w |> fst |> numSyntax.int_of_term
      in n end handle HOL_ERR _ =>
        failwith ("Unable to read offset from " ^ (term_to_string tm))
  val minus_zero = ``-1w:word8``
  fun dest_byte_list tm =
    listSyntax.dest_list tm |> fst
       |> map (fn tm => if tm = minus_zero then 255
                        else numSyntax.int_of_term (rand tm) mod 256)
  fun dest_code_pair tm = let
    val (x,y) = pairSyntax.dest_pair tm
    val n = dest_pc_plus_offset x
    in (n, dest_byte_list y) end
    handle HOL_ERR _ => (print "\n\n"; print_term tm; print "\n\n";
                         failwith "unable to extract code_pair")
  val code_pairs = map dest_code_pair cs
  (* sort, delete duplicates, check for overlaps etc. *)
  val vs = sort (fn (x,_) => fn (y:int,_) => x <= y) code_pairs
  fun del_repetations [] = []
    | del_repetations [x] = [x]
    | del_repetations (x::y::xs) = if x = y then del_repetations (x::xs) else
                                            x :: del_repetations (y::xs)
  val vs = del_repetations vs
  fun no_holes i [] = true
    | no_holes i ((j,c)::xs) =
       if i = j then no_holes (i + length c) xs else
       if i < j then failwith ("Gap in the code at location " ^ (int_to_string i))
       else failwith ("Duplicate code at location " ^ (int_to_string j))
  val _ = no_holes 0 vs
  (* compute size *)
  fun sum f [] k = k
    | sum f (n::ns) k = sum f ns (k + f n)
  val total = sum (length o snd) vs 0
  fun fill c d n s = if size s < n then fill c d n (c ^ s ^ d) else s
  fun num_to_string n =
    if n < 1000 then int_to_string n else
      num_to_string (n div 1000) ^ "," ^ fill "0" "" 3 (int_to_string (n mod 1000))
  val code_size_str = num_to_string total ^ " bytes"
  val _ = print (code_size_str ^ " ... ")
  (* produce output *)
  val t = TextIO.openOut(filename)
  fun ex str = TextIO.output(t,str)
  fun print_bytes [] = ()
    | print_bytes [b] = ex (int_to_string b)
    | print_bytes (b::bs) = (ex (int_to_string b); ex ", "; print_bytes bs)
  fun print_lines [] = ()
    | print_lines ((n,bs)::rest) = let
    val _ = ex "\t.byte\t"
    val _ = print_bytes bs
    val _ = ex "\n"
    in print_lines rest end
  val l1 = "Machine code automatically extracted from a HOL4 theorem."
  val l2 = "The code size: " ^ code_size_str
  val l3 = "End of automatically extracted machine code."
  val _ = ex ("\n\t/*  " ^ l1 ^ "  */\n")
  val _ = ex ("\t/*  " ^ fill "" " " (size l1) l2 ^ "  */\n\n")
  val _ = print_lines vs
  val _ = ex ("\n\t/*  " ^ fill "" " " (size l1) l3 ^ "  */\n")
  val _ = TextIO.closeOut(t)
  val _ = print "done.\n"
  in () end;

val EVEN_w2n_EXTRA = blastLib.BBLAST_PROVE
  ``(((p + offset) ' 0) = (p ' 0 <> (offset:word64) ' 0))``

(* running repl_decs

  val th0 = SPEC_COMPOSE_RULE [zHEAP_INIT,zHEAP_ABBREVS]
  val th1 = SPEC_COMPOSE_RULE [th0,SPEC_repl_decs]
  val th2 = th1 |> SIMP_RULE std_ss [EVEN_w2n,EVEN_w2n_EXTRA]
                |> CONV_RULE (PRE_CONV (RAND_CONV (RAND_CONV EVAL)))
                |> SIMP_RULE std_ss [GSYM EVEN_w2n,x64_code_LENGTH_evaluated]
  val p = get_pc th2 |> rand
  val th3 = zHEAP_TERMINATE |> INST [``p:word64``|->p]
     |> SIMP_RULE std_ss [word_arith_lemma1]
  val th = MATCH_MP FAKE_COMPOSE (CONJ th2 th3)
  val _ = print " [2]\n "
  val th = th |> SIMP_RULE (srw_ss()) [code_abbrevs_def,first_cs_def]
              |> SIMP_RULE (srw_ss()) [full_code_abbrevs_def,fetch "-" "full_cs_def"]
              |> RW [all_code_abbrevs,word_arith_lemma1]
              |> RW [INSERT_UNION_EQ,UNION_EMPTY]
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV ANY_ADD_EVAL_CONV))
  val _ = print " [3]\n "
  val th = th |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                    [first_cs_def,first_s_def]))
  val lemma = x64_code_evaluated
              |> CONV_RULE (RATOR_CONV (REWRITE_CONV [GSYM x64_bootstrap_code_def]))
  val th = th |> RW1 [lemma]
  val _ = print " [4]\n "
  val _ = time (new_write_code_to_file "wrapper/asm_code.s") th

*)


(* running repl_decs then repl_step   WORKS!

  val th1 = SPEC_repl_decs
  val th2 = SPEC_repl_step |> Q.INST [`p`|->`p + n2w (LENGTH x64_bootstrap_code)`]
    |> RW [WORD_ADD_SUB,word_arith_lemma1,x64_code_LENGTH_evaluated]
  val th = MATCH_MP FAKE_COMPOSE (CONJ th1 th2)
  (* val th = th1 *)
  val th0 = SPEC_COMPOSE_RULE [zHEAP_INIT,zHEAP_ABBREVS,zHEAP_PUSH1]

,
              zHEAP_MOV_RBP_RSP,zHEAP_MOV_RBP_RSP]
  (* val th0 = SPEC_COMPOSE_RULE [zHEAP_INIT,zHEAP_ABBREVS] *)
  val th1 = SPEC_COMPOSE_RULE [th0,th]
  val th2 = th1 |> SIMP_RULE std_ss [EVEN_w2n,EVEN_w2n_EXTRA]
                |> CONV_RULE (PRE_CONV (RAND_CONV (RAND_CONV EVAL)))
                |> SIMP_RULE std_ss [GSYM EVEN_w2n,x64_code_LENGTH_evaluated]
  val p = get_pc th2 |> rand
  val th3 = zHEAP_TERMINATE |> INST [``p:word64``|->p]
     |> SIMP_RULE std_ss [word_arith_lemma1]
  val th = MATCH_MP FAKE_COMPOSE (CONJ th2 th3)
  val _ = print " [2]\n "
  val th = th |> SIMP_RULE (srw_ss()) [code_abbrevs_def,first_cs_def]
              |> SIMP_RULE (srw_ss()) [full_code_abbrevs_def,fetch "-" "full_cs_def"]
              |> RW [all_code_abbrevs,word_arith_lemma1]
              |> RW [INSERT_UNION_EQ,UNION_EMPTY]
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV ANY_ADD_EVAL_CONV))
  val _ = print " [3]\n "
  val th = th |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss())
                    [first_cs_def,first_s_def]))
  val lemma = x64_code_evaluated
              |> CONV_RULE (RATOR_CONV (REWRITE_CONV [GSYM x64_bootstrap_code_def]))
  val th = th |> RW1 [lemma]
  val _ = print " [4]\n "
  val _ = time (new_write_code_to_file "wrapper/asm_code.s") th

*)





(*

local
  val pat = ``NUMERAL m + (NUMERAL n):num``
  fun ANY_ADD_EVAL_CONV tm =
    if can (match_term pat) tm then EVAL tm else NO_CONV tm
  val th0 = SPEC_COMPOSE_RULE [zHEAP_INIT,zHEAP_ABBREVS,
              zHEAP_SET_PRINTING_ON,zHEAP_SET_PRINTING_ON]
in
  fun generate_test th1 = let
    val _ = print " [1]\n "
    val th = SPEC_COMPOSE_RULE [th0,th1,zHEAP_TERMINATE]
    val _ = print " [2]\n "
    val th = th |> SIMP_RULE (srw_ss()) [code_abbrevs_def,first_cs_def]
              |> SIMP_RULE (srw_ss()) [full_code_abbrevs_def,fetch "-" "full_cs_def"]
              |> RW [all_code_abbrevs,word_arith_lemma1]
              |> RW [INSERT_UNION_EQ,UNION_EMPTY]
              |> CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV ANY_ADD_EVAL_CONV))
    val _ = print " [3]\n "
    val th = th |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [first_cs_def,first_s_def]))
    val _ = print " [4]\n "
    val _ = time (new_write_code_to_file "wrapper/asm_code.s") th
    in th end
end




local
  val x64_code_EVAL_NIL = x64_code_def |> CONJUNCTS |> hd |> SPEC_ALL
  val x64_code_EVAL_CONS = prove(
    ``x64_code i (x::xs) =
        (\c. (\l. c ++ x64_code l xs) (i + LENGTH c)) (x64 i x)``,
    SIMP_TAC std_ss [x64_code_def,x64_length_def,LENGTH_x64_IGNORE])
  val APPEND_NIL = APPEND |> CONJUNCTS |> hd |> SPEC_ALL
  val APPEND_CONS = APPEND |> CONJUNCTS |> last |> SPEC_ALL
  fun eval_append_conv f tm =
    (REWR_CONV APPEND_NIL THENC f) tm
    handle HOL_ERR _ =>
    (REWR_CONV APPEND_CONS THENC RAND_CONV (eval_append_conv f)) tm
in
  fun eval_x64_code_conv tm =
    if tm |> rand |> listSyntax.is_nil then
      REWR_CONV x64_code_EVAL_NIL tm
    else
      (REWR_CONV x64_code_EVAL_CONS THENC (RAND_CONV EVAL)
       THENC BETA_CONV THENC (RAND_CONV EVAL) THENC BETA_CONV
       THENC eval_append_conv eval_x64_code_conv) tm
end

  val push_int = SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_LOAD_IMM1]
  val th9 = push_int |> Q.INST [`k`|->`9`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th8 = push_int |> Q.INST [`k`|->`8`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th7 = push_int |> Q.INST [`k`|->`7`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th6 = push_int |> Q.INST [`k`|->`6`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th5 = push_int |> Q.INST [`k`|->`5`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th4 = push_int |> Q.INST [`k`|->`4`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th3 = push_int |> Q.INST [`k`|->`3`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th2 = push_int |> Q.INST [`k`|->`2`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th1 = push_int |> Q.INST [`k`|->`1`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val th0 = push_int |> Q.INST [`k`|->`0`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
  val push_10 = SPEC_COMPOSE_RULE [th0,th1,th2,th3,th4,th5,th6,th7,th8,th9]
  val th = generate_test th0

do a bit of arithmetic:

  val th = SPEC_COMPOSE_RULE [th4,th3,zBC_Less,zBC_Print]
  val th = generate_test th

push a few numbers:

  val push_10 = SPEC_COMPOSE_RULE [th0,th1,th2,th3,th4,th5,th6,th7,th8,th9]
  val th = generate_test push_10

print "A\n":

  val thA = zBC_PrintC |> Q.INST [`c`|->`65w`] |> SIMP_RULE (srw_ss()) []
  val thNL = zBC_PrintC |> Q.INST [`c`|->`10w`] |> SIMP_RULE (srw_ss()) []
  val th = SPEC_COMPOSE_RULE [thA]
  val th = generate_test th

push 10 numbers onto stack:

  val thA = zBC_PrintC |> Q.INST [`c`|->`65w`] |> SIMP_RULE (srw_ss()) []
  val thNL = zBC_PrintC |> Q.INST [`c`|->`10w`] |> SIMP_RULE (srw_ss()) []
  val th = SPEC_COMPOSE_RULE [th0,th0,thA,thA,thNL]
  val th = generate_test th

print some numbers:

  val th = SPEC_COMPOSE_RULE [push_10,zHEAP_POP2,zHEAP_ADD_SMALL_INT,zBC_Print,thNL,zBC_Print,zBC_Print,zBC_Print,zBC_Print]
  val th = generate_test th

val load_rev_1 = zHEAP_LoadRev |> Q.INST [`k`|->`1+2`]
  |> SIMP_RULE (srw_ss()) [IMM32_def] |> CONV_RULE (RATOR_CONV (RAND_CONV EVAL))

  val th = SPEC_COMPOSE_RULE [zHEAP_Store_Base,th0,th2,th1,th2,zHEAP_MOV_RBP_RSP,th3,th4,th5,zHEAP_Load_Base,load_rev_1,zBC_Print]
  val th = generate_test th

  (* must align to 16 bytes *)


try running bytecode:

val tm =
   ``[PushPtr (Addr 0); PushExc; Jump (Addr 27); Stack (Cons 5 0); PopExc;
   Return; Stack (PushInt 6); Stack (PushInt 0); Ref; PushPtr (Addr 15);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"t"; PrintC #"e"; PrintC #"s"; PrintC #"t";
   PrintC #"1"; PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0);
   Print; PrintC #"\n"]``

more code:

val tm =
   ``[PushPtr (Addr 0); PushExc; Jump (Addr 27); Stack (Cons 5 0); PopExc;
   Return; Stack (PushInt 6); Stack (PushInt 0); Ref; PushPtr (Addr 15);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"f"; PrintC #"o"; PrintC #"o"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n";
   PushPtr (Addr 0); PushExc; Jump (Addr 614); Stack (Cons 5 0); PopExc;
   Return; Stack (LoadRev 0); Stack (PushInt 0); Ref;
   PushPtr (Addr 602); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"b";
   PrintC #"a"; PrintC #"r"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"]``

even more code:

val tm =
   ``[PushPtr (Addr 0); PushExc; Jump (Addr 53); Stack (Load 2);
   Stack (Pops 1); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 15); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Pops 1);
   Stack (PushInt 0); Ref; PushPtr (Addr 41); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"f"; PrintC #"o"; PrintC #"o"; PrintC #"_"; PrintC #"1";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 803);
   Stack (Cons 5 0); PopExc; Return; Stack (LoadRev 0);
   Stack (PushInt 5); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (PushInt 0); Ref;
   PushPtr (Addr 791); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"b";
   PrintC #"a"; PrintC #"r"; PrintC #"_"; PrintC #"1"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n"]``

fib of 31:

val tm =
   ``[PushPtr (Addr 0); PushExc; Jump (Addr 198); Stack (Load 2);
   Stack (PushInt 2); Stack Less; JumpIf (Addr 46); Jump (Addr 75);
   Stack (Load 2); Stack (Pops 1); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Jump (Addr 198); Stack (Load 3);
   Stack (Load 3); Stack (PushInt 1); Stack Sub; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 4); Stack (Load 4); Stack (PushInt 2); Stack Sub;
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack Add; Stack (Pops 1); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Stack (PushInt 0); Ref; PushPtr (Addr 15);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"f";
   PrintC #"i"; PrintC #"b"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0); PushExc;
   Jump (Addr 765); Stack (Cons 5 0); PopExc; Return; Stack (LoadRev 0);
   Stack (PushInt 31);
   Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (PushInt 0); Ref;
   PushPtr (Addr 753); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"k";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"]``

fib of 31 six times:

val tm =
   ``[PushPtr (Addr 0); PushExc; Jump (Addr 198); Stack (Load 2);
   Stack (PushInt 2); Stack Less; JumpIf (Addr 46); Jump (Addr 75);
   Stack (Load 2); Stack (Pops 1); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Jump (Addr 198); Stack (Load 3);
   Stack (Load 3); Stack (PushInt 1); Stack Sub; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 4); Stack (Load 4); Stack (PushInt 2); Stack Sub;
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack Add; Stack (Pops 1); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Stack (PushInt 0); Ref; PushPtr (Addr 15);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"f";
   PrintC #"i"; PrintC #"b"; PrintC #"_"; PrintC #"2"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n";
   PushPtr (Addr 0); PushExc; Jump (Addr 817); Stack (Cons 5 0); PopExc;
   Return; Stack (PushInt 31); Stack (LoadRev 0); Stack (Load 1);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (LoadRev 0); Stack (Load 2); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack Add;
   Stack (LoadRev 0); Stack (Load 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack Add;
   Stack (LoadRev 0); Stack (Load 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack Add;
   Stack (LoadRev 0); Stack (Load 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack Add;
   Stack (LoadRev 0); Stack (Load 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack Add;
   Stack (Pops 1); Stack (PushInt 0); Ref; PushPtr (Addr 805);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"k"; PrintC #"_"; PrintC #"2"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n"]``

QSORT (<=) (mk_list 1000 ++ mk_list 1000)

val tm =
   ``[PushPtr (Addr 0); PushExc; Stack (Cons 4 0); Stack Pop;
   Stack (Cons 0 0); PopExc; Stack (Pops 1); Stack Pop; PrintC #"P";
   PrintC #"a"; PrintC #"i"; PrintC #"r"; PrintC #" "; PrintC #"=";
   PrintC #" "; PrintC #"<"; PrintC #"c"; PrintC #"o"; PrintC #"n";
   PrintC #"s"; PrintC #"t"; PrintC #"r"; PrintC #"u"; PrintC #"c";
   PrintC #"t"; PrintC #"o"; PrintC #"r"; PrintC #">"; PrintC #"\n";
   PushPtr (Addr 0); PushExc; Jump (Addr 2355); Stack (PushInt 0); Ref;
   PushPtr (Addr 768); Stack (Load 0); Stack (Load 6); Stack (Load 6);
   Stack (Cons 0 2); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 2); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Stack (PushInt 0); Ref; PushPtr (Addr 959); Stack (Load 0);
   Stack (Load 5); Stack (Load 4); Stack (El 0); Stack (Load 5);
   Stack (El 1); Stack (Cons 0 3); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 0); Stack (Pops 2); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Stack (PushInt 0); Ref; PushPtr (Addr 1162);
   Stack (Load 0); Stack (Load 3); Stack (El 0); Stack (Load 4);
   Stack (El 1); Stack (Load 5); Stack (El 2); Stack (Load 8);
   Stack (Cons 0 4); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 2); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Stack (Load 0); Stack (El 0); Stack (PushInt 0); Ref;
   PushPtr (Addr 1533); Stack (Load 0); Stack (Load 3); Stack (Load 5);
   Stack (El 1); Stack (Load 6); Stack (El 2); Stack (Load 7);
   Stack (El 3); Stack (Load 10); Stack (Cons 0 5); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 1399);
   Jump (Addr 1475); Stack (Load 2); Stack (El 3); Stack (Load 5);
   Stack (Cons 10 2); Stack (Pops 3); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Jump (Addr 1533); Stack (Load 0);
   Stack (Load 4); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 6); Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 2343); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (El 0);
   Stack (TagEq 9); JumpIf (Addr 1689); Jump (Addr 2285);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 5); Stack (El 2); Stack (Load 3); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   JumpIf (Addr 1793); Jump (Addr 2039); Stack (Load 5); Stack (El 1);
   Stack (Load 6); Stack (El 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 3); Stack (Load 7); Stack (El 3);
   Stack (Cons 9 2); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Load 6); Stack (El 4);
   Stack (Load 8); Stack (Load 2); Stack (El 0); Stack (Load 3);
   Stack (El 1); Stack (Shift 5 8); Tick; Return; Jump (Addr 2282);
   Stack (Load 5); Stack (El 1); Stack (Load 6); Stack (El 2);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 1); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 6);
   Stack (El 3); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Load 3); Stack (Load 7);
   Stack (El 4); Stack (Cons 9 2); Stack (Load 8); Stack (Load 2);
   Stack (El 0); Stack (Load 3); Stack (El 1); Stack (Shift 5 8); Tick;
   Return; Jump (Addr 2343); Stack (Load 0); Stack (Load 3);
   Stack (Load 1); Stack (El 0); Stack (Load 2); Stack (El 1);
   Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 596); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"p"; PrintC #"a"; PrintC #"r"; PrintC #"t";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 3316);
   Stack (PushInt 0); Ref; PushPtr (Addr 3115); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (Load 6); Stack (Cons 0 2);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Pops 2);
   Stack (Load 1); Stack (Store 3); Stack (Pops 2); Return;
   Stack (Load 0); Stack (El 0); Stack (Load 1); Stack (El 1);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 3); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Cons 8 0);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Cons 8 0); Stack (Load 3); Stack (Load 2);
   Stack (El 0); Stack (Load 3); Stack (El 1); Stack (Shift 5 4); Tick;
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 2936); Stack (Load 0); Stack (LoadRev 0);
   Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 1); Stack (PushInt 0); Ref; PushPtr (Addr 3304);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"p"; PrintC #"a"; PrintC #"r"; PrintC #"t";
   PrintC #"i"; PrintC #"t"; PrintC #"i"; PrintC #"o"; PrintC #"n";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 5093);
   Stack (PushInt 0); Ref; PushPtr (Addr 4366); Stack (Load 0);
   Stack (Load 5); Stack (Load 7); Stack (Cons 0 2); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Pops 2); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Stack (Load 0);
   Stack (El 0); Stack (PushInt 0); Ref; PushPtr (Addr 4666);
   Stack (Load 0); Stack (Load 3); Stack (Load 5); Stack (El 1);
   Stack (Load 8); Stack (Cons 0 3); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 4579);
   Jump (Addr 4608); Stack (Load 4); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 4666);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 5081); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 4822); Jump (Addr 5023);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 2); Stack (Load 6); Stack (El 1); Stack (Load 2);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 7); Stack (El 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Cons 9 2);
   Stack (Pops 6); Stack (Load 1); Stack (Store 2); Stack (Pops 1);
   Return; Jump (Addr 5081); Stack (Load 0); Stack (Load 3);
   Stack (Load 1); Stack (El 0); Stack (Load 2); Stack (El 1);
   Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 4194); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"a"; PrintC #"p"; PrintC #"p"; PrintC #"e";
   PrintC #"n"; PrintC #"d"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0); PushExc;
   Jump (Addr 7540); Stack (PushInt 0); Ref; PushPtr (Addr 5922);
   Stack (Load 0); Stack (Load 3); Stack (El 0); Stack (Load 4);
   Stack (El 1); Stack (Load 8); Stack (Load 8); Stack (Cons 0 4);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Pops 2);
   Stack (Load 1); Stack (Store 3); Stack (Pops 2); Return;
   Stack (Load 2); Stack (PushInt 0); Ref; PushPtr (Addr 6246);
   Stack (Load 0); Stack (Load 3); Stack (Load 5); Stack (El 0);
   Stack (Load 6); Stack (El 1); Stack (Load 7); Stack (El 2);
   Stack (Load 8); Stack (El 3); Stack (Cons 0 5); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 6159);
   Jump (Addr 6188); Stack (Cons 8 0); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 6246);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 7397); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 6402); Jump (Addr 7339);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 5); Stack (El 1); Stack (PushInt 0); Ref;
   PushPtr (Addr 7409); Stack (Load 0); Stack (Load 9); Stack (El 4);
   Stack (Load 7); Stack (Cons 0 2); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 0); Stack (Pops 1); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 0); Stack (PushInt 0); Ref; PushPtr (Addr 7528);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 10); JumpIf (Addr 6844);
   Jump (Addr 7278); Stack (Load 1); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 1); Stack (Load 0); Stack (Load 12);
   Stack (El 2); Stack (Load 13); Stack (El 2); Stack (Load 14);
   Stack (El 3); Stack (Load 15); Stack (El 4); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 5); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 11);
   Stack (Cons 8 0); Stack (Cons 9 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 13); Stack (El 3); Stack (Load 14); Stack (El 4);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 15);
   Stack (Load 2); Stack (El 0); Stack (Load 3); Stack (El 1);
   Stack (Shift 5 15); Tick; Return; Jump (Addr 7336); Stack (Load 0);
   Stack (Load 10); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 11); Return; Jump (Addr 7397);
   Stack (Load 0); Stack (Load 3); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 4); Return;
   Stack (Cons 5 0); PopExc; Return; Stack (Load 0); Stack (El 0);
   Stack (Load 3); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Load 1); Stack (El 1);
   Stack (Load 3); Stack (Load 2); Stack (El 0); Stack (Load 3);
   Stack (El 1); Stack (Shift 5 4); Tick; Return; Stack (Cons 5 0);
   PopExc; Return; Stack (PushInt 0); Ref; PushPtr (Addr 5726);
   Stack (Load 0); Stack (LoadRev 1); Stack (LoadRev 2);
   Stack (Cons 0 2); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"q"; PrintC #"s"; PrintC #"o"; PrintC #"r";
   PrintC #"t"; PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0);
   Print; PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 8417);
   Stack (Load 2); Stack (PushInt 0); Stack Sub; Stack (PushInt 1);
   Stack Less; JumpIf (Addr 8229); Jump (Addr 8258); Stack (Cons 8 0);
   Stack (Pops 1); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Jump (Addr 8417); Stack (Load 2); Stack (Load 4);
   Stack (Load 4); Stack (PushInt 1); Stack Sub; Stack (Load 0);
   Stack (PushInt 0); Stack Less; JumpIf (Addr 8313); Jump (Addr 8321);
   Stack (PushInt 0); Jump (Addr 8326); Stack (Load 0); Stack (Pops 1);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Cons 9 2); Stack (Pops 1); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 8189); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Cons 4 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"m"; PrintC #"k"; PrintC #"_"; PrintC #"l"; PrintC #"i";
   PrintC #"s"; PrintC #"t"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0); PushExc;
   Jump (Addr 9314); Stack (PushInt 0); Ref; PushPtr (Addr 9243);
   Stack (Load 0); Stack (Load 5); Stack (Cons 0 1); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Pops 2); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Stack (Load 0);
   Stack (El 0); Stack (Load 3); Stack Sub; Stack (PushInt 1);
   Stack Less; Stack (Pops 1); Stack (Load 1); Stack (Store 3);
   Stack (Pops 2); Return; Stack (Cons 5 0); PopExc; Return;
   Stack (LoadRev 3); Stack (PushInt 0); Ref; PushPtr (Addr 9076);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 0); Stack (Pops 1); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (LoadRev 2);
   Stack (LoadRev 4); Stack (PushInt 1000); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (LoadRev 4); Stack (PushInt 1000); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (PushInt 0); Ref; PushPtr (Addr 9302); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"u"; PrintC #"s"; PrintC #"e"; PrintC #"_"; PrintC #"q";
   PrintC #"s"; PrintC #"o"; PrintC #"r"; PrintC #"t"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n"]``

Batched queue:

val tm =
   ``[PushPtr (Addr 0); PushExc; Stack (Cons 4 0); Stack Pop;
   Stack (Cons 0 0); PopExc; Stack (Pops 1); Stack Pop; PrintC #"Q";
   PrintC #"u"; PrintC #"e"; PrintC #"u"; PrintC #"e"; PrintC #" ";
   PrintC #"="; PrintC #" "; PrintC #"<"; PrintC #"c"; PrintC #"o";
   PrintC #"n"; PrintC #"s"; PrintC #"t"; PrintC #"r"; PrintC #"u";
   PrintC #"c"; PrintC #"t"; PrintC #"o"; PrintC #"r"; PrintC #">";
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 634);
   Stack (Cons 5 0); PopExc; Return; Stack (Cons 8 0); Stack (Cons 8 0);
   Stack (Cons 10 2); Stack (PushInt 0); Ref; PushPtr (Addr 622);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"e"; PrintC #"m"; PrintC #"p"; PrintC #"t";
   PrintC #"y"; PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0);
   Print; PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 2153);
   Stack (Load 2); Stack (PushInt 0); Ref; PushPtr (Addr 1826);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 10); JumpIf (Addr 1455);
   Jump (Addr 1768); Stack (Load 1); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 1); Stack (Load 0); Stack (Load 2);
   Stack (PushInt 0); Ref; PushPtr (Addr 1838); Stack (Load 0);
   Stack (Load 3); Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 1678);
   Jump (Addr 1707); Stack (Cons 1 0); Stack (Pops 9); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 1765);
   Stack (Load 0); Stack (Load 10); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 12); Return;
   Jump (Addr 1826); Stack (Load 0); Stack (Load 4); Stack (Load 1);
   Stack (El 0); Stack (Load 2); Stack (El 1); Stack (Shift 4 6);
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 2129); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (El 0);
   Stack (TagEq 9); JumpIf (Addr 1994); Jump (Addr 2071);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Cons 0 0); Stack (Pops 6); Stack (Load 1); Stack (Store 2);
   Stack (Pops 1); Return; Jump (Addr 2129); Stack (Load 0);
   Stack (Load 3); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc;
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 1301); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Pops 1);
   Stack (PushInt 0); Ref; PushPtr (Addr 2141); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"i"; PrintC #"s"; PrintC #"_"; PrintC #"e"; PrintC #"m";
   PrintC #"p"; PrintC #"t"; PrintC #"y"; PrintC #" "; PrintC #"=";
   PrintC #" "; Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0);
   PushExc; Jump (Addr 3877); Stack (PushInt 0); Ref;
   PushPtr (Addr 3141); Stack (Load 0); Stack (Load 5); Stack (Load 7);
   Stack (Cons 0 2); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 2); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Stack (Load 0); Stack (El 0); Stack (PushInt 0); Ref;
   PushPtr (Addr 3441); Stack (Load 0); Stack (Load 3); Stack (Load 5);
   Stack (El 1); Stack (Load 8); Stack (Cons 0 3); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 3354);
   Jump (Addr 3383); Stack (Load 4); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 3441);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 3865); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 3597); Jump (Addr 3807);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 5); Stack (El 1); Stack (Load 1); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 3); Stack (Load 7); Stack (El 2); Stack (Cons 9 2);
   Stack (Load 8); Stack (Load 2); Stack (El 0); Stack (Load 3);
   Stack (El 1); Stack (Shift 5 8); Tick; Return; Jump (Addr 3865);
   Stack (Load 0); Stack (Load 3); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 4); Return;
   Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 2969); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Cons 4 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"r"; PrintC #"e"; PrintC #"v"; PrintC #" "; PrintC #"=";
   PrintC #" "; Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0);
   PushExc; Jump (Addr 4556); Stack (Load 0); Stack (El 0);
   Stack (Load 3); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Cons 8 0); Stack (Load 3);
   Stack (Load 2); Stack (El 0); Stack (Load 3); Stack (El 1);
   Stack (Shift 5 4); Tick; Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 4432); Stack (Load 0);
   Stack (LoadRev 2); Stack (Cons 0 1); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Pops 1); Stack (PushInt 0);
   Ref; PushPtr (Addr 4544); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"r";
   PrintC #"e"; PrintC #"v"; PrintC #"e"; PrintC #"r"; PrintC #"s";
   PrintC #"e"; PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0);
   Print; PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 6408);
   Stack (Load 2); Stack (PushInt 0); Ref; PushPtr (Addr 5994);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 10); JumpIf (Addr 5536);
   Jump (Addr 5936); Stack (Load 1); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 1); Stack (Load 0); Stack (Load 2);
   Stack (PushInt 0); Ref; PushPtr (Addr 6006); Stack (Load 0);
   Stack (Load 3); Stack (Load 5); Stack (Cons 0 2); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 5764);
   Jump (Addr 5875); Stack (Load 8); Stack (El 0); Stack (Load 3);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Cons 8 0); Stack (Cons 10 2); Stack (Pops 9);
   Stack (Load 1); Stack (Store 3); Stack (Pops 2); Return;
   Jump (Addr 5933); Stack (Load 0); Stack (Load 10); Stack (Load 1);
   Stack (El 0); Stack (Load 2); Stack (El 1); Stack (Shift 4 12);
   Return; Jump (Addr 5994); Stack (Load 0); Stack (Load 4);
   Stack (Load 1); Stack (El 0); Stack (Load 2); Stack (El 1);
   Stack (Shift 4 6); Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 6384); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 6162); Jump (Addr 6326);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 2); Stack (Load 1); Stack (Cons 9 2); Stack (Load 6);
   Stack (El 1); Stack (Cons 10 2); Stack (Pops 6); Stack (Load 1);
   Stack (Store 2); Stack (Pops 1); Return; Jump (Addr 6384);
   Stack (Load 0); Stack (Load 3); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 4); Return;
   Stack (Cons 5 0); PopExc; Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 5382); Stack (Load 0);
   Stack (LoadRev 3); Stack (Cons 0 1); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Pops 1); Stack (PushInt 0);
   Ref; PushPtr (Addr 6396); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"c";
   PrintC #"h"; PrintC #"e"; PrintC #"c"; PrintC #"k"; PrintC #"f";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 7824);
   Stack (PushInt 0); Ref; PushPtr (Addr 7387); Stack (Load 0);
   Stack (Load 5); Stack (Load 4); Stack (El 0); Stack (Cons 0 2);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Pops 2);
   Stack (Load 1); Stack (Store 3); Stack (Pops 2); Return;
   Stack (Load 0); Stack (El 0); Stack (PushInt 0); Ref;
   PushPtr (Addr 7800); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (TagEq 10);
   JumpIf (Addr 7548); Jump (Addr 7742); Stack (Load 1); Stack (El 0);
   Stack (Load 0); Stack (Load 3); Stack (El 1); Stack (Load 0);
   Stack (Load 6); Stack (El 1); Stack (Load 3); Stack (Load 10);
   Stack (Load 3); Stack (Cons 9 2); Stack (Cons 10 2); Stack (Load 9);
   Stack (Load 2); Stack (El 0); Stack (Load 3); Stack (El 1);
   Stack (Shift 5 10); Tick; Return; Jump (Addr 7800); Stack (Load 0);
   Stack (Load 4); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 6); Return; Stack (Cons 5 0); PopExc;
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 7208); Stack (Load 0); Stack (LoadRev 4);
   Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 1); Stack (PushInt 0); Ref; PushPtr (Addr 7812);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"s"; PrintC #"n"; PrintC #"o"; PrintC #"c";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 9410);
   Stack (Load 2); Stack (PushInt 0); Ref; PushPtr (Addr 9083);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 10); JumpIf (Addr 8726);
   Jump (Addr 9025); Stack (Load 1); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 1); Stack (Load 0); Stack (Load 2);
   Stack (PushInt 0); Ref; PushPtr (Addr 9095); Stack (Load 0);
   Stack (Load 3); Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 8949);
   Jump (Addr 8964); Stack (Cons 5 0); PopExc; Return; Jump (Addr 9022);
   Stack (Load 0); Stack (Load 10); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 12); Return;
   Jump (Addr 9083); Stack (Load 0); Stack (Load 4); Stack (Load 1);
   Stack (El 0); Stack (Load 2); Stack (El 1); Stack (Shift 4 6);
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 9386); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (El 0);
   Stack (TagEq 9); JumpIf (Addr 9251); Jump (Addr 9328);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 2); Stack (Pops 6); Stack (Load 1); Stack (Store 2);
   Stack (Pops 1); Return; Jump (Addr 9386); Stack (Load 0);
   Stack (Load 3); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc;
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 8572); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Pops 1);
   Stack (PushInt 0); Ref; PushPtr (Addr 9398); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"h"; PrintC #"e"; PrintC #"a"; PrintC #"d"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n";
   PushPtr (Addr 0); PushExc; Jump (Addr 11075); Stack (Load 2);
   Stack (PushInt 0); Ref; PushPtr (Addr 10650); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (TagEq 10); JumpIf (Addr 10276); Jump (Addr 10592);
   Stack (Load 1); Stack (El 0); Stack (Load 0); Stack (Load 3);
   Stack (El 1); Stack (Load 0); Stack (Load 2); Stack (PushInt 0); Ref;
   PushPtr (Addr 10662); Stack (Load 0); Stack (Load 3);
   Stack (Load 11); Stack (El 0); Stack (Load 6); Stack (Cons 0 3);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 1); Stack (TagEq 8);
   JumpIf (Addr 10516); Jump (Addr 10531); Stack (Cons 5 0); PopExc;
   Return; Jump (Addr 10589); Stack (Load 0); Stack (Load 10);
   Stack (Load 1); Stack (El 0); Stack (Load 2); Stack (El 1);
   Stack (Shift 4 12); Return; Jump (Addr 10650); Stack (Load 0);
   Stack (Load 4); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 6); Return; Stack (Cons 5 0); PopExc;
   Return; Stack (PushInt 0); Ref; PushPtr (Addr 11051); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 10818);
   Jump (Addr 10993); Stack (Load 1); Stack (El 0); Stack (El 0);
   Stack (Load 0); Stack (Load 3); Stack (El 0); Stack (El 1);
   Stack (Load 0); Stack (Load 5); Stack (El 1); Stack (Load 1);
   Stack (Load 7); Stack (El 2); Stack (Cons 10 2); Stack (Load 8);
   Stack (Load 2); Stack (El 0); Stack (Load 3); Stack (El 1);
   Stack (Shift 5 8); Tick; Return; Jump (Addr 11051); Stack (Load 0);
   Stack (Load 3); Stack (Load 1); Stack (El 0); Stack (Load 2);
   Stack (El 1); Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc;
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 10122); Stack (Load 0); Stack (LoadRev 4);
   Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 1); Stack (PushInt 0); Ref; PushPtr (Addr 11063);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"t"; PrintC #"a"; PrintC #"i"; PrintC #"l";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 12598);
   Stack (PushInt 0); Ref; PushPtr (Addr 12019); Stack (Load 0);
   Stack (Load 6); Stack (Load 4); Stack (El 0); Stack (Load 5);
   Stack (El 1); Stack (Load 8); Stack (Cons 0 4); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Pops 2); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Stack (Load 0);
   Stack (El 3); Stack (PushInt 0); Stack Sub; Stack (PushInt 1);
   Stack Less; JumpIf (Addr 12066); Jump (Addr 12095); Stack (Load 2);
   Stack (Pops 1); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Jump (Addr 12598); Stack (Load 0); Stack (El 0);
   Stack (Load 1); Stack (El 3); Stack (PushInt 1); Stack Sub;
   Stack (Load 0); Stack (PushInt 0); Stack Less; JumpIf (Addr 12159);
   Jump (Addr 12167); Stack (PushInt 0); Jump (Addr 12172);
   Stack (Load 0); Stack (Pops 1); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 2); Stack (Load 3);
   Stack (El 2); Stack (Load 6); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 4);
   Stack (El 3); Stack (PushInt 1); Stack Sub; Stack (Load 0);
   Stack (PushInt 0); Stack Less; JumpIf (Addr 12330);
   Jump (Addr 12338); Stack (PushInt 0); Jump (Addr 12343);
   Stack (Load 0); Stack (Pops 1); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 3); Stack (El 3); Stack (PushInt 1); Stack Sub;
   Stack (Load 0); Stack (PushInt 0); Stack Less; JumpIf (Addr 12460);
   Jump (Addr 12468); Stack (PushInt 0); Jump (Addr 12473);
   Stack (Load 0); Stack (Pops 1); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 3); Stack (Load 2); Stack (El 0); Stack (Load 3);
   Stack (El 1); Stack (Shift 5 4); Tick; Return; Stack (PushInt 0);
   Ref; PushPtr (Addr 11823); Stack (Load 0); Stack (LoadRev 7);
   Stack (LoadRev 5); Stack (Cons 0 2); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1); Stack (Load 0);
   Stack (Load 0); Stack (El 0); Stack (Store 1); Stack Pop;
   PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" "; PrintC #"u";
   PrintC #"s"; PrintC #"e"; PrintC #"_"; PrintC #"q"; PrintC #"u";
   PrintC #"e"; PrintC #"u"; PrintC #"e"; PrintC #" "; PrintC #"=";
   PrintC #" "; Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0);
   PushExc; Jump (Addr 13363); Stack (Cons 5 0); PopExc; Return;
   Stack (LoadRev 6); Stack (LoadRev 8); Stack (PushInt 1000000);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (LoadRev 0); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (PushInt 0); Ref; PushPtr (Addr 13351); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"r"; PrintC #"u"; PrintC #"n"; PrintC #"_"; PrintC #"q";
   PrintC #"u"; PrintC #"e"; PrintC #"u"; PrintC #"e"; PrintC #" ";
   PrintC #"="; PrintC #" "; Stack (Load 0); Print; PrintC #"\n"]``;

tree_sort:

val tm =
   ``[PushPtr (Addr 0); PushExc; Jump (Addr 914); Stack (PushInt 0); Ref;
   PushPtr (Addr 187); Stack (Load 0); Stack (Load 5); Stack (Load 7);
   Stack (Cons 0 2); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 2); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Stack (Load 0); Stack (El 0); Stack (PushInt 0); Ref;
   PushPtr (Addr 487); Stack (Load 0); Stack (Load 3); Stack (Load 5);
   Stack (El 1); Stack (Load 8); Stack (Cons 0 3); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 400);
   Jump (Addr 429); Stack (Load 4); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 487);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 902); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 643); Jump (Addr 844);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 2); Stack (Load 6); Stack (El 1); Stack (Load 2);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 7); Stack (El 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Cons 9 2);
   Stack (Pops 6); Stack (Load 1); Stack (Store 2); Stack (Pops 1);
   Return; Jump (Addr 902); Stack (Load 0); Stack (Load 3);
   Stack (Load 1); Stack (El 0); Stack (Load 2); Stack (El 1);
   Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 15); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"a"; PrintC #"p"; PrintC #"p"; PrintC #"e";
   PrintC #"n"; PrintC #"d"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0); PushExc;
   Stack (Cons 4 0); Stack Pop; Stack (Cons 0 0); PopExc;
   Stack (Pops 1); Stack Pop; PrintC #"B"; PrintC #"r"; PrintC #"a";
   PrintC #"n"; PrintC #"c"; PrintC #"h"; PrintC #" "; PrintC #"=";
   PrintC #" "; PrintC #"<"; PrintC #"c"; PrintC #"o"; PrintC #"n";
   PrintC #"s"; PrintC #"t"; PrintC #"r"; PrintC #"u"; PrintC #"c";
   PrintC #"t"; PrintC #"o"; PrintC #"r"; PrintC #">"; PrintC #"\n";
   PrintC #"L"; PrintC #"e"; PrintC #"a"; PrintC #"f"; PrintC #" ";
   PrintC #"="; PrintC #" "; PrintC #"<"; PrintC #"c"; PrintC #"o";
   PrintC #"n"; PrintC #"s"; PrintC #"t"; PrintC #"r"; PrintC #"u";
   PrintC #"c"; PrintC #"t"; PrintC #"o"; PrintC #"r"; PrintC #">";
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 4014);
   Stack (PushInt 0); Ref; PushPtr (Addr 2898); Stack (Load 0);
   Stack (Load 6); Stack (Load 6); Stack (Cons 0 2); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 0); Stack (Pops 2); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Stack (Load 2);
   Stack (PushInt 0); Ref; PushPtr (Addr 3250); Stack (Load 0);
   Stack (Load 3); Stack (Load 5); Stack (El 0); Stack (Load 6);
   Stack (El 1); Stack (Cons 0 3); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 11); JumpIf (Addr 3111);
   Jump (Addr 3192); Stack (Cons 11 0); Stack (Load 3); Stack (El 1);
   Stack (Cons 11 0); Stack (Cons 10 3); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 3250);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 4002); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 10); JumpIf (Addr 3406); Jump (Addr 3944);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 5); Stack (El 0); Stack (El 2); Stack (Load 0);
   Stack (Load 7); Stack (El 2); Stack (Load 3); Stack Less;
   JumpIf (Addr 3516); Jump (Addr 3674); Stack (Load 7); Stack (El 1);
   Stack (Load 8); Stack (El 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 5);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 3); Stack (Load 2); Stack (Cons 10 3);
   Stack (Pops 8); Stack (Load 1); Stack (Store 2); Stack (Pops 1);
   Return; Jump (Addr 3941); Stack (Load 2); Stack (Load 8);
   Stack (El 2); Stack Less; JumpIf (Addr 3712); Jump (Addr 3870);
   Stack (Load 4); Stack (Load 3); Stack (Load 9); Stack (El 1);
   Stack (Load 10); Stack (El 2); Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 3);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Cons 10 3); Stack (Pops 8); Stack (Load 1);
   Stack (Store 2); Stack (Pops 1); Return; Jump (Addr 3941);
   Stack (Load 4); Stack (Load 3); Stack (Load 2); Stack (Cons 10 3);
   Stack (Pops 8); Stack (Load 1); Stack (Store 2); Stack (Pops 1);
   Return; Jump (Addr 4002); Stack (Load 0); Stack (Load 3);
   Stack (Load 1); Stack (El 0); Stack (Load 2); Stack (El 1);
   Stack (Shift 4 4); Return; Stack (Cons 5 0); PopExc; Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 2726); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"i"; PrintC #"n"; PrintC #"s"; PrintC #"e";
   PrintC #"r"; PrintC #"t"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0); PushExc;
   Jump (Addr 5371); Stack (Load 2); Stack (PushInt 0); Ref;
   PushPtr (Addr 4940); Stack (Load 0); Stack (Load 3); Stack (Load 5);
   Stack (El 0); Stack (Load 9); Stack (Cons 0 3); Stack (Cons 3 2);
   Stack (Store 0); Stack (Load 1); Stack (Load 1); Update;
   Stack (Store 0); Stack (Load 1); Stack (TagEq 8); JumpIf (Addr 4853);
   Jump (Addr 4882); Stack (Cons 11 0); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 4940);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 5359); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 9); JumpIf (Addr 5096); Jump (Addr 5301);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 5); Stack (El 1); Stack (Load 3); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 6); Stack (El 2); Stack (Load 2); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 8); Stack (Load 2); Stack (El 0); Stack (Load 3);
   Stack (El 1); Stack (Shift 5 8); Tick; Return; Jump (Addr 5359);
   Stack (Load 0); Stack (Load 3); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 4); Return;
   Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 4647); Stack (Load 0); Stack (LoadRev 1);
   Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"b"; PrintC #"u"; PrintC #"i"; PrintC #"l";
   PrintC #"d"; PrintC #"_"; PrintC #"t"; PrintC #"r"; PrintC #"e";
   PrintC #"e"; PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0);
   Print; PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 7051);
   Stack (Load 2); Stack (PushInt 0); Ref; PushPtr (Addr 6437);
   Stack (Load 0); Stack (Load 3); Stack (Load 5); Stack (El 0);
   Stack (Load 9); Stack (Cons 0 3); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (TagEq 11); JumpIf (Addr 6350);
   Jump (Addr 6379); Stack (Cons 8 0); Stack (Pops 3); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Jump (Addr 6437);
   Stack (Load 0); Stack (Load 4); Stack (Load 1); Stack (El 0);
   Stack (Load 2); Stack (El 1); Stack (Shift 4 6); Return;
   Stack (PushInt 0); Ref; PushPtr (Addr 7039); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (El 0); Stack (TagEq 10); JumpIf (Addr 6593); Jump (Addr 6981);
   Stack (Load 1); Stack (El 0); Stack (El 0); Stack (Load 0);
   Stack (Load 3); Stack (El 0); Stack (El 1); Stack (Load 0);
   Stack (Load 5); Stack (El 0); Stack (El 2); Stack (Load 0);
   Stack (Load 7); Stack (El 1); Stack (Load 8); Stack (El 1);
   Stack (Load 9); Stack (El 2); Stack (Load 7); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 4); Stack (Cons 8 0); Stack (Cons 9 2);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0);
   Tick; CallPtr; Stack (Load 8); Stack (El 2); Stack (Load 2);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Load 10); Stack (Load 2); Stack (El 0);
   Stack (Load 3); Stack (El 1); Stack (Shift 5 10); Tick; Return;
   Jump (Addr 7039); Stack (Load 0); Stack (Load 3); Stack (Load 1);
   Stack (El 0); Stack (Load 2); Stack (El 1); Stack (Shift 4 4);
   Return; Stack (Cons 5 0); PopExc; Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 6144); Stack (Load 0); Stack (LoadRev 0);
   Stack (Cons 0 1); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Cons 4 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"f"; PrintC #"l"; PrintC #"a"; PrintC #"t";
   PrintC #"t"; PrintC #"e"; PrintC #"n"; PrintC #" "; PrintC #"=";
   PrintC #" "; Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0);
   PushExc; Jump (Addr 7877); Stack (Load 0); Stack (El 0);
   Stack (Load 1); Stack (El 1); Stack (Load 4); Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (Load 3); Stack (Load 2); Stack (El 0); Stack (Load 3);
   Stack (El 1); Stack (Shift 5 4); Tick; Return; Stack (Cons 5 0);
   PopExc; Return; Stack (PushInt 0); Ref; PushPtr (Addr 7746);
   Stack (Load 0); Stack (LoadRev 3); Stack (LoadRev 2);
   Stack (Cons 0 2); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 0);
   Stack (Pops 1); Stack (PushInt 0); Ref; PushPtr (Addr 7865);
   Stack (Load 0); Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0);
   Stack (Load 1); Stack (Load 1); Update; Stack (Store 0);
   Stack (Load 1); Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Pops 1); Stack (Load 0); Stack (Load 0);
   Stack (El 0); Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc;
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l";
   PrintC #" "; PrintC #"t"; PrintC #"r"; PrintC #"e"; PrintC #"e";
   PrintC #"_"; PrintC #"s"; PrintC #"o"; PrintC #"r"; PrintC #"t";
   PrintC #" "; PrintC #"="; PrintC #" "; Stack (Load 0); Print;
   PrintC #"\n"; PushPtr (Addr 0); PushExc; Jump (Addr 8989);
   Stack (Load 2); Stack (PushInt 0); Stack Sub; Stack (PushInt 1);
   Stack Less; JumpIf (Addr 8801); Jump (Addr 8830); Stack (Cons 8 0);
   Stack (Pops 1); Stack (Load 1); Stack (Store 3); Stack (Pops 2);
   Return; Jump (Addr 8989); Stack (Load 2); Stack (Load 4);
   Stack (Load 4); Stack (PushInt 1); Stack Sub; Stack (Load 0);
   Stack (PushInt 0); Stack Less; JumpIf (Addr 8885); Jump (Addr 8893);
   Stack (PushInt 0); Jump (Addr 8898); Stack (Load 0); Stack (Pops 1);
   Stack (Load 1); Stack (El 1); Stack (Load 2); Stack (El 0); Tick;
   CallPtr; Stack (Cons 9 2); Stack (Pops 1); Stack (Load 1);
   Stack (Store 3); Stack (Pops 2); Return; Stack (PushInt 0); Ref;
   PushPtr (Addr 8761); Stack (Load 0); Stack (Cons 0 0);
   Stack (Cons 3 2); Stack (Store 0); Stack (Load 1); Stack (Load 1);
   Update; Stack (Store 0); Stack (Load 0); Stack (Cons 4 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"m"; PrintC #"k"; PrintC #"_"; PrintC #"l"; PrintC #"i";
   PrintC #"s"; PrintC #"t"; PrintC #" "; PrintC #"="; PrintC #" ";
   Stack (Load 0); Print; PrintC #"\n"; PushPtr (Addr 0); PushExc;
   Jump (Addr 9660); Stack (Cons 5 0); PopExc; Return;
   Stack (LoadRev 4); Stack (LoadRev 0); Stack (LoadRev 5);
   Stack (PushInt 1000); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (LoadRev 5);
   Stack (PushInt 1000); Stack (Load 1); Stack (El 1); Stack (Load 2);
   Stack (El 0); Tick; CallPtr; Stack (Load 1); Stack (El 1);
   Stack (Load 2); Stack (El 0); Tick; CallPtr; Stack (Load 1);
   Stack (El 1); Stack (Load 2); Stack (El 0); Tick; CallPtr;
   Stack (PushInt 0); Ref; PushPtr (Addr 9648); Stack (Load 0);
   Stack (Cons 0 0); Stack (Cons 3 2); Stack (Store 0); Stack (Load 1);
   Stack (Load 1); Update; Stack (Store 0); Stack (Load 1);
   Stack (Load 0); Stack (Cons 4 1); Stack (Pops 1); Stack (Pops 1);
   Stack (Pops 1); Stack (Load 0); Stack (Load 0); Stack (El 0);
   Stack (Store 1); Stack Pop; Stack (Cons 0 1); PopExc; Stack (Pops 1);
   Stack (Load 0); Stack (Load 0); Stack (El 0); Stack (Store 1);
   Stack Pop; PrintC #"v"; PrintC #"a"; PrintC #"l"; PrintC #" ";
   PrintC #"u"; PrintC #"s"; PrintC #"e"; PrintC #"_"; PrintC #"t";
   PrintC #"r"; PrintC #"e"; PrintC #"e"; PrintC #" "; PrintC #"=";
   PrintC #" "; Stack (Load 0); Print; PrintC #"\n"]``;


let
  val code = ``x64_code 0 ^tm``
  val code_EVAL = eval_x64_code_conv code
  val len = ``LENGTH ^code + 3``
            |> (ONCE_REWRITE_CONV [code_EVAL] THENC EVAL) |> concl |> rand
  val zHEAP_RUN_CODE = prove(
  ``SPEC X64_MODEL
     (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p)
     {(p,0x48w::0x8Bw::0xECw::^(code_EVAL |> concl |> rand))}
     (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC (p + n2w ^len))``,
  cheat)
  val _ = generate_test zHEAP_RUN_CODE
in
  ()
end


-----------------

BENCHMARK 1: fib

TIMES: CakeML 0.141s, PolyML 0.096s, Ocaml 0.440s, Ocamlopt 0.056s

0.440 / 0.141
0.440 / 0.096
0.440 / 0.056

BENCHMARK 2: qsort

TIMES: CakeML 0.253s, PolyML 0.016s, Ocaml 0.161s, Ocamlopt 0.052s

0.161 / 0.253
0.161 / 0.016
0.161 / 0.052

BENCHMARK 3: batched queue

TIMES: CakeML 0.822s, PolyML 0.028s, Ocaml 0.361s, Ocamlopt 0.179s

0.361 / 0.822
0.361 / 0.028
0.361 / 0.179

BENCHMARK 4: binary tree

TIMES: CakeML 0.125s, PolyML 0.012s, Ocaml 0.069s, Ocamlopt 0.016s

0.069 / 0.125
0.069 / 0.012
0.069 / 0.016

-----------------

(* testing infrastructure *)

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory;
open test_compilerLib

(* ... *)

val dlets = let
  fun get_dlet suffix =
    [fetch "-" ("scratch_decls_" ^ suffix) |> concl |> rand |> rator |> rand |> mk_Tdec]
    handle HOL_ERR _ => []
  in get_dlet "0" @
     get_dlet "1" @
     get_dlet "2" @
     get_dlet "3" @
     get_dlet "4" @
     get_dlet "5" @
     get_dlet "6" @
     get_dlet "7" @
     get_dlet "8" @
     get_dlet "9" @
     get_dlet "10" @
     get_dlet "11" @
     get_dlet "12" @
     get_dlet "13" @
     get_dlet "14" @
     get_dlet "15" @
     get_dlet "16" @
     get_dlet "17" @
     get_dlet "18" @
     get_dlet "19" end

fun get_bs dlets = let
  val (bs,rs) = real_inits
  fun foo ((bs,rs),[]) = bs
    | foo ((bs,rs),x::xs) = let
    val (rs,(rsf,c)) = compile_top rs x
    val bs = add_code c bs
    in foo ((bs,rs),xs) end
  in foo ((bs,rs),dlets) end

val tm = bs_to_term (get_bs dlets)

*)

val zHEAP_COND_TERMINATE = let
  val l = 0x8 + 2
  val (_,_,sts,_) = prog_x64Lib.x64_tools
  val th = zHEAP_TERMINATE |> RW [sts]
  val str = "jne " ^ int_to_string l
  val ((th1,_,_),th2x) = prog_x64Lib.x64_spec_memory64
          (x64_encodeLib.x64_encode str)
  val th2 = case th2x of SOME (x,_,_) => x | _ => fail()
  val thA = SPEC_COMPOSE_RULE [zHEAP_4EQ0,th2,th] |> RW [STAR_ASSOC]
             |> SIMP_RULE (std_ss++sep_cond_ss) [SEP_CLAUSES,precond_def]
             |> RW [SPEC_MOVE_COND] |> Q.INST [`rip`|->`p`]
  val th1 = SPEC_FRAME_RULE th1 ``zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) *
      ¬zS1 Z_CF * ¬zS1 Z_PF * ¬zS1 Z_AF * ¬zS1 Z_SF * ¬zS1 Z_OF``
  val th1 = HIDE_POST_RULE ``zS1 Z_ZF`` th1
  val th1 = SPEC_COMPOSE_RULE [zHEAP_4EQ0,th1]
  val th1 = HIDE_STATUS_RULE true sts th1
  val thB = th1 |> SIMP_RULE (std_ss++sep_cond_ss) [SEP_CLAUSES,precond_def]
             |> RW [SPEC_MOVE_COND] |> Q.INST [`rip`|->`p`]
  val ss = SIMP_RULE (std_ss++star_ss) []
  val lemma = prove(
    ``(~b /\ d ==> (SPEC m p c1 q1)) /\
      (b /\ d ==> (SPEC m p c2 q2)) ==>
      c1 SUBSET c2 ==>
      (d ==> SPEC m p c2 (if b then q2 else q1))``,
    Cases_on `b` \\ Cases_on `d`
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [SPEC_SUBSET_CODE])
  val th = MATCH_MP lemma (CONJ (ss thB) (ss thA))
  val th = th |> SIMP_RULE std_ss [STAR_ASSOC,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET]
              |> RW [GSYM SPEC_MOVE_COND]
  in th end

val getNumber_lex_until_semi_test = prove(
  ``~(getNumber (lex_until_semi_test input) < 0) /\
    isNumber (lex_until_semi_test input) /\
    ((getNumber (lex_until_semi_test input) = 0) =
      (lex_until_top_semicolon_alt input = NONE))``,
  SIMP_TAC std_ss [lex_until_semi_test_def]
  \\ Cases_on `lex_until_top_semicolon_alt input`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ EVAL_TAC);

val IF_SEP_DISJ = prove(
  ``((if b then c else d) \/ x) = if b then c \/ x else SEP_DISJ d x``,
  Cases_on `b` \\ SIMP_TAC std_ss [SEP_DISJ_def]);

val zHEAP_LEX_THEN_COND_TERMINATE =
  SPEC_COMPOSE_RULE [zHEAP_LEX,zHEAP_COND_TERMINATE]
  |> SIMP_RULE (srw_ss()) [getNumber_lex_until_semi_test,SEP_CLAUSES,IF_SEP_DISJ]

val zHEAP_BlockSome = let
  val tag = BlockSome_def |> SPEC_ALL |> concl |> rand |> rator |> rand
  val th1 =
    zHEAP_BIG_CONS
    |> Q.INST [`l`|->`1`,`n`|->`^tag`,`stack`|->`x::stack`]
    |> RW [GSYM BlockSome_def,EVAL ``REVERSE (TAKE 1 (x::xs))``,
         EVAL ``DROP 1 (x::xs)``] |> DISCH_ALL |> GEN_ALL
    |> SIMP_RULE (srw_ss()) [DECIDE ``1 <= SUC n:num``] |> SPEC_ALL
  in SPEC_COMPOSE_RULE [zHEAP_PUSH1,th1] end

val zHEAP_BlockPair = let
  val th1 =
    zHEAP_BIG_CONS
    |> Q.INST [`l`|->`2`,`n`|->`pair_tag`,`stack`|->`y::x::stack`]
    |> RW [EVAL ``REVERSE (TAKE 2 (y::x::xs))``,
         EVAL ``DROP 2 (y::x::xs)``] |> DISCH_ALL |> GEN_ALL
    |> SIMP_RULE (srw_ss()) [pair_tag_def,DECIDE ``2 <= SUC (SUC n):num``]
    |> SPEC_ALL |> RW [GSYM pair_tag_def,GSYM BlockPair_def]
  in SPEC_COMPOSE_RULE [zHEAP_PUSH2,zHEAP_PUSH1,th1] end

val zHEAP_ERASE_end_of_code = let
  val n = EVAL ``LENGTH end_of_code`` |> concl |> rand |> numLib.int_of_term
  fun rpt 0 x = [] | rpt n x = x :: rpt (n-1) x
  val f = foldr (fn (th1,th2) =>
            SPEC_COMPOSE_RULE [th1,th2] |> SIMP_RULE (srw_ss()) [])
  val th = f zHEAP_CODE_FRONT (rpt (n-1) zHEAP_CODE_FRONT)
  val lemma = prove(
    ``xs ++ y1::ys = SNOC y1 xs ++ ys``,
    SRW_TAC [] []);
  val th = th
    |> DISCH ``s.code = code ++ end_of_code``
    |> SIMP_RULE (srw_ss()) [end_of_code_def]
    |> RW [lemma,FRONT_SNOC,APPEND_NIL,rich_listTheory.NOT_SNOC_NIL,SEP_CLAUSES]
    |> RW [SNOC_APPEND,APPEND,GSYM APPEND_ASSOC]
    |> RW [GSYM end_of_code_def]
    |> RW [GSYM SPEC_MOVE_COND]
  in th end;

val zHEAP_LEX_THEN_COND_TERMINATE_UPDATE_JUMP = let
  val th1 = zHEAP_LEX_THEN_COND_TERMINATE
  val ((jmp_th,_,_),_) = prog_x64Lib.x64_spec_memory64 "E9"
  val th2 = SPEC_COMPOSE_RULE [zHEAP_BlockPair,zHEAP_BlockSome,
    zHEAP_MOVE_32,zHEAP_UPDATE_REF,zHEAP_SET_PRINTING_ON,
    zHEAP_POP4,zHEAP_POP1,jmp_th]
    |> SIMP_RULE std_ss [ADD_ASSOC]
  (* composing th1 and th2 *)
  val tm = ``lex_until_top_semicolon_alt s.input = NONE``
  val lemma = prove(``~(getNumber (lex_until_semi_test s.input) < 0)``,
    Cases_on `lex_until_top_semicolon_alt s.input`
    \\ ASM_SIMP_TAC (srw_ss()) [lex_until_semi_test_def] \\ EVAL_TAC)
  val thA = DISCH tm th1 |> SIMP_RULE std_ss [lemma,SEP_CLAUSES] |> UNDISCH
  val thB = DISCH (mk_neg tm) th1 |> SIMP_RULE std_ss [lemma,SEP_CLAUSES] |> UNDISCH
  val thB = SPEC_COMPOSE_RULE [thB, th2]
            |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
  val (_,_,c,_) = dest_spec (concl thB |> rand)
  val thA = SPEC c (MATCH_MP SPEC_SUBSET_CODE thA)
  val lemma = prove(thA |> concl |> dest_imp |> fst,
    SIMP_TAC std_ss [SUBSET_DEF,IN_INSERT,IN_UNION]
    \\ REPEAT STRIP_TAC \\ ASM_REWRITE_TAC [] \\ FULL_SIMP_TAC std_ss [])
  val thA = MP thA lemma
  val lemma = prove(
    ``(b1 ==> SPEC m p c q1) /\ (~b1 ==> b2 ==> SPEC m p c q2) ==>
      b2 ==> SPEC m p c (if b1 then q1 else q2)``,
    Cases_on `b2` \\ Cases_on `b1` \\ FULL_SIMP_TAC std_ss [])
  val th = MATCH_MP lemma (CONJ (DISCH_ALL thA) (DISCH_ALL thB))
           |> SIMP_RULE (srw_ss()) [ADD_ASSOC,GSYM SPEC_MOVE_COND]
  in th end

val zEL0 = zHEAP_Block_El |> Q.INST [`k`|->`0`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]
val zEL1 = zHEAP_Block_El |> Q.INST [`k`|->`1`] |> SIMP_RULE (srw_ss()) [SEP_CLAUSES]

val bool_to_val_11 = prove(
  ``!b1 b2. (bool_to_val b1 = bool_to_val b2) = (b1 = b2)``,
  Cases \\ Cases \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC);

val inl_tag = BlockInl_def |> SPEC_ALL |> concl |> rand |> rator |> rand

val zHEAP_IF_INL_JUMP =
  SPEC_COMPOSE_RULE [zHEAP_PUSH1,zHEAP_TagEq,zHEAP_JumpIf]
  |> Q.INST [`k`|->`^inl_tag`,`imm32`|->`inl_jump`] (* BlockInl_def *)
  |> SIMP_RULE (srw_ss()) [HD,TL,bool_to_val_11,NOT_CONS_NIL,isBlock_def,
       SEP_CLAUSES,bc_tag_eq_pre_def,getTag_def,isNumber_def,getNumber_def,
       LET_DEF,EVAL ``small_int (& (^inl_tag))``]

val zHEAP_IF_INL_JUMP_FALSE =
  zHEAP_IF_INL_JUMP |> DISCH ``getTag x1 <> ^inl_tag``
  |> SIMP_RULE std_ss [] |> RW [GSYM SPEC_MOVE_COND]

val zHEAP_IF_INL_JUMP_TRUE =
  zHEAP_IF_INL_JUMP |> DISCH ``getTag x1 = ^inl_tag``
  |> SIMP_RULE std_ss [] |> RW [GSYM SPEC_MOVE_COND]

val zHEAP_INR_CASE_RAW = let (* COMPILER_RUN_INV_INR *)
  val FLOOKUP_SOME_IMP = prove(
    ``(FLOOKUP refs a = SOME x) ==> (refs ' a = x)``,
    SRW_TAC [] [FLOOKUP_DEF])
  val lemma = MATCH_MP FLOOKUP_SOME_IMP (ASSUME ``(FLOOKUP refs (outp_ptr:num) =
      SOME (BlockInr (BlockPair (BlockList (MAP Chr msg),s_bc_val))))``)
  val th =
    SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_POP3,zHEAP_PUSH3,
      zHEAP_PUSH2,zHEAP_PUSH1,zHEAP_MOVE_21,zHEAP_DEREF,zHEAP_IF_INL_JUMP_FALSE,zEL0,
      zHEAP_PUSH1,zEL0,zHEAP_PRINT_STRING,zHEAP_POP1,zEL1,zHEAP_PUSH4]
    |> Q.INST [`stack`|->`RefPtr outp_ptr::RefPtr inp_ptr::rest`,`xs`|->`msg`]
    |> SIMP_RULE (srw_ss()) [SEP_CLAUSES,getRefPtr_def,isRefPtr_def]
    |> CONV_RULE (DEPTH_CONV (fn tm =>
         if tm = (concl lemma |> rator |> rand) then lemma else fail()))
    |> SIMP_RULE std_ss [BlockInr_def,BlockPair_def,EVAL ``EL 1 (x::y::xs)``,
         getContent_def,isBlock_def,HD,TL,LENGTH,SEP_CLAUSES,getTag_def]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_LEX_THEN_COND_TERMINATE_UPDATE_JUMP]
  val th = th |> SIMP_RULE (srw_ss()) [getRefPtr_def,isRefPtr_def,ADD_ASSOC,
                   SEP_CLAUSES]
  in th end;

val jump_inst = let
  val (_,_,code,_) = dest_spec (concl zHEAP_INR_CASE_RAW)
  val pat = ``(p,[0xFw; 0x85w; x;y;z; w2w (imm32 >>> 24)])``
  val x = (find_term (can (match_term pat)) code |> rator |> rand
            |> rand |> rand |> numSyntax.int_of_term) + 6
  fun dest_code_pair tm = let
    val (x,y) = dest_pair tm
    val i = wordsSyntax.dest_word_add x |> snd |> rand |> numSyntax.int_of_term
    val l = listSyntax.dest_list y |> fst |> length
    in i + l end handle HOL_ERR _ => 0
  val list_max = foldl (fn (x,y) => if x <= y then y else x) 0
  val len = code |> find_terms pairSyntax.is_pair
                 |> map dest_code_pair |> list_max
  val jump_len = (len - x) |> numSyntax.term_of_int
  in SIMP_RULE (srw_ss()) [] o
     INST [``inl_jump:word32``|->``(n2w ^jump_len):word32``] end

val zHEAP_INR_CASE = jump_inst zHEAP_INR_CASE_RAW

val zHEAP_INR_CASE_REAL = let
  val p = get_pc SPEC_repl_step |> rand |> rand |> rand
  val q = get_pc zHEAP_INR_CASE
  val n = find_term (can (match_term ``p + n2w (NUMERAL n + x)``)) q
          |> rand |> rand |> rator |> rand
  in Q.INST [`imm32`|->`0w - n2w ^n - n2w ^p`] zHEAP_INR_CASE
       |> SIMP_RULE (srw_ss()) []
       |> CONV_RULE (RAND_CONV (SIMP_CONV (std_ss++WORD_SUB_ss) [])) end

val TAKE_REV_LEMMA = prove(
  ``n <= LENGTH xs ==> (TAKE n (REVERSE (TAKE n xs) ++ ys) = REVERSE (TAKE n xs))``,
  METIS_TAC [rich_listTheory.TAKE_LENGTH_APPEND,LENGTH_REVERSE,LENGTH_TAKE]);

val DROP_REV_LEMMA = prove(
  ``n <= LENGTH xs ==> (DROP n (REVERSE (TAKE n xs) ++ ys) = ys)``,
  METIS_TAC [rich_listTheory.DROP_LENGTH_APPEND,LENGTH_REVERSE,LENGTH_TAKE]);

val repl_decs_pack = let
  val stack_length = ``repl_decs_stack_length+1:num`` |> EVAL |> concl |> rand
  val th = zHEAP_BIG_CONS |> DISCH_ALL |> Q.GEN `imm64`
    |> Q.INST [`n`|->`0`,`l`|->`repl_decs_stack_length+1`]
    |> SIMP_RULE (srw_ss()) [repl_decs_stack_length_def]
    |> RW [GSYM SPEC_MOVE_COND]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_PUSH2,zHEAP_PUSH3,
             zHEAP_EXPLODE_BLOCK_SIMPLE,th,zHEAP_POP3,zHEAP_POP2]
           |> DISCH ``^stack_length <= LENGTH (stack:bc_value list)``
           |> SIMP_RULE std_ss [getContent_def,isBlock_def,HD,TL,
                 REVERSE_REVERSE,TAKE_REV_LEMMA,DROP_REV_LEMMA,NOT_CONS_NIL,
                 LENGTH_APPEND,LENGTH_REVERSE,LENGTH_TAKE,SEP_CLAUSES]
           |> RW [GSYM SPEC_MOVE_COND]
  in SPEC_COMPOSE_RULE [zHEAP_MOVE_12,th,zHEAP_BlockPair] end

val zHEAP_Load_Base = prove(
    ``SPEC X64_MODEL (* x64_encodeLib.x64_encode "mov r5,[r9+152]" *)
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p)
       {(p,[0x49w; 0x8Bw; 0xA9w; 0x98w; 0x00w; 0x00w; 0x00w])}
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC (p+7w))``,
    cheat); (* stack cheat *)

val zHEAP_INL_CASE_UP_TO_BC_EVAL = let (* COMPILER_RUN_INV_INL *)
  val FLOOKUP_SOME_IMP = prove(
    ``(FLOOKUP refs a = SOME x) ==> (refs ' a = x)``,
    SRW_TAC [] [FLOOKUP_DEF])
  val lemma = MATCH_MP FLOOKUP_SOME_IMP (ASSUME ``(FLOOKUP refs (outp_ptr:num) =
      SOME
        (BlockInl
           (BlockPair
              (m_bc_val,
               BlockPair (BlockList (MAP BlockNum3 code),s_bc_val)))))``)
  val th =
    SPEC_COMPOSE_RULE [zHEAP_POP2,zHEAP_POP3,zHEAP_PUSH3,
      zHEAP_PUSH2,zHEAP_PUSH1,zHEAP_MOVE_21,zHEAP_DEREF,zHEAP_IF_INL_JUMP_TRUE,
      zEL0,zEL1,zHEAP_PUSH1,zEL0,zHEAP_MOVE_14,zHEAP_POP1,zEL1,repl_decs_pack,
      zHEAP_Load_Base,zHEAP_INSTALL_CODE]
    |> jump_inst
    |> Q.INST [`stack`|->`RefPtr outp_ptr::RefPtr inp_ptr::rest`]
    |> SIMP_RULE (srw_ss()) [SEP_CLAUSES,getRefPtr_def,isRefPtr_def]
    |> CONV_RULE (DEPTH_CONV (fn tm =>
         if tm = (concl lemma |> rator |> rand) then lemma else fail()))
    |> SIMP_RULE std_ss [BlockInl_def,BlockPair_def,EVAL ``EL 1 (x::y::xs)``,
         getContent_def,isBlock_def,HD,TL,LENGTH,SEP_CLAUSES,getTag_def]
    |> SIMP_RULE std_ss [GSYM BlockPair_def]
  in th end;

val zHEAP_MOV_RBP_RSP = prove(
    ``SPEC X64_MODEL (* x64_encodeLib.x64_encode "mov r5,r4" *)
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p)
       {(p,[0x48w; 0x8Bw; 0xECw])}
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC (p+3w))``,
    cheat); (* stack cheat *)

val zHEAP_Base_ADD8 = prove(
    ``SPEC X64_MODEL (* x64_encodeLib.x64_encode "add r5,8" *)
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC p)
       {(p,[0x48w; 0x83w; 0xC5w; 0x08w])}
       (zHEAP (cs,x1,x2,x3,x4,refs,stack,s,NONE) * ~zS * zPC (p+4w))``,
    cheat); (* stack cheat *)

val zHEAP_INL_CASE_AFTER_BC_EVAL = let (* COMPILER_RUN_INV_INL *)
  val lemma = prove(
    ``SEP_DISJ (if b then x \/ error else y \/ error) error =
      if b then x \/ error else y \/ error``,
    Cases_on `b` \\ SIMP_TAC std_ss [FUN_EQ_THM,SEP_DISJ_def] \\ METIS_TAC [])
  val old_state = ``x1::RefPtr outp_ptr::RefPtr inp_ptr::rest``
  val th = zHEAP_ERASE_end_of_code
           |> Q.INST [`x1`|->`stop`,`x4`|->`BlockPair (s_bc_val,Block 0 ^old_state)`]
  val th = SPEC_COMPOSE_RULE [th,zHEAP_MOV_RBP_RSP,zHEAP_Base_ADD8, (* maybe SUB? *)
              zHEAP_MOVE_13,zHEAP_MOVE_41,zEL0,zHEAP_MOVE_32,zHEAP_BlockPair,
              zHEAP_MOVE_13,zHEAP_MOVE_41,zHEAP_MOVE_34,zEL1,zHEAP_MOVE_23,
              zHEAP_EXPLODE_BLOCK_SIMPLE,zHEAP_POP1,zHEAP_POP2,zHEAP_POP3,
              zHEAP_PUSH3,zHEAP_PUSH2,zHEAP_PUSH1,zHEAP_PUSH1,zHEAP_MOVE_41,
              zHEAP_LEX_THEN_COND_TERMINATE_UPDATE_JUMP]
           |> SIMP_RULE std_ss [BlockPair_def,getContent_def,HD,TL,NOT_CONS_NIL,
                EVAL ``EL 1 [x;y]``,TL,HD,APPEND,isBlock_def,LENGTH,SEP_CLAUSES,
                getRefPtr_def,isRefPtr_def] |> RW [GSYM BlockPair_def]
           |> CONV_RULE (SIMP_CONV (srw_ss()) [ADD_ASSOC,lemma])
  in th end;

val ref_adjust_IMP_ODD = prove(
  ``!r. r IN FDOM (ref_adjust (cb2,sb2,F) bs2.refs) ==> ODD r``,
  SIMP_TAC (srw_ss()) [ref_adjust_def,LET_DEF,PULL_EXISTS]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,ODD,EVEN_DOUBLE,GSYM EVEN_ODD]);

val ref_adjust_IMP_EVEN = prove(
  ``!r. r IN FDOM (ref_adjust (cb2,sb2,T) bs2.refs) ==> EVEN r``,
  SIMP_TAC (srw_ss()) [ref_adjust_def,LET_DEF,PULL_EXISTS]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,ODD,EVEN_DOUBLE,GSYM EVEN_ODD]);

val zREPL_INV_def = Define `
  zREPL_INV bs2 (x,s,out,stack,cs,cb2,sb2,x1,p) =
    SEP_EXISTS bs inp outp.
      zBC_HEAP bs
        (x,cs,MAP (bc_adjust (cb2,sb2,F)) bs2.stack ++ Number 0::stack,s,out)
        (p − n2w (LENGTH x64_bootstrap_code),0w,T,
         ref_adjust (cb2,sb2,F) bs2.refs) * zPC p * ¬zS *
      cond
        (INPUT_TYPE x1 inp ∧ bs_no_sp bs ∧ COMPILER_RUN_INV bs inp outp ∧
         EVEN (w2n (p − n2w (LENGTH x64_bootstrap_code))) ∧
         (bs.inst_length = x64_inst_length))`;

val zREPL_STEP_RES_def = Define `
  zREPL_STEP_RES y pc (bs2,cb2,cs,out,p,s,sb2,stack,x) =
    SEP_EXISTS bs2'.
        zBC_HEAP bs2'
           (x,cs,MAP (bc_adjust (cb2,sb2,F)) bs2.stack ++ Number 0::stack,s,out)
           (p − n2w (LENGTH x64_bootstrap_code),0x0w,T,
            ref_adjust (cb2,sb2,F) bs2.refs) * zPC pc * ¬zS *
        cond
          (COMPILER_RUN_INV_OUTPUT bs2' y ∧
           (bs2'.inst_length = x64_inst_length) ∧ bs_no_sp bs2')`;

val repl_step_pc = ``(p + 0x54w):word64``

val SPEC_repl_step_REPL_INV = let
  val th = SPEC_repl_step
    |> Q.INST [`f2`|->`ref_adjust (cb2,sb2,F) bs2.refs`]
    |> RW [ref_adjust_IMP_ODD]
    |> Q.INST [`stack`|->`MAP (bc_adjust (cb2,sb2,F)) bs2.stack ++ Number 0::stack`]
    |> RW [LENGTH_APPEND,LENGTH_MAP,LENGTH,ADD_CLAUSES]
    |> Q.GENL (rev [`bs`,`inp`,`outp`])
    |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
    |> CONV_RULE (PRE_CONV (REWR_CONV (GSYM zREPL_INV_def)))
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zREPL_STEP_RES (repl_step x1) ^repl_step_pc (bs2,cb2,cs,out,p,s,sb2,stack,x) \/
      zHEAP_ERROR cs``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zREPL_STEP_RES_def,SEP_IMP_def,SEP_EXISTS_THM,
      SEP_DISJ_def,cond_STAR] \\ METIS_TAC [])
  val th = MP th lemma
  in th end

(*
  transform:
    zHEAP_INR_CASE_REAL
  target pre:
    zREPL_STEP_RES (INR (msg,s)) ^repl_step_pc
        (bs2,cb2,cs,out,p,s,sb2,stack,x)
  target post:
    if lex_until_top_semicolon_alt s.input = NONE then
      zHEAP_OUTPUT (cs,STRCAT s.output msg) ∨ zHEAP_ERROR cs
    else
      zREPL_INV bs2 (x,s,out,stack,cs,cb2,sb2,x1,p) ∨ zHEAP_ERROR cs
*)

val SPEC_IMP_LEMMA = prove(
  ``(!x. SPEC m (p * cond (P x)) c (q x)) ==>
    SPEC m (p * cond (?x. P x)) c (SEP_EXISTS x. q x)``,
  SIMP_TAC std_ss [SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC SPEC_WEAKEN
  \\ POP_ASSUM MATCH_MP_TAC
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
  \\ METIS_TAC []);

val SPEC_LEMMA2 = prove(
  ``SPEC m (p * cond b1 * cond b2) c q ==>
    (b1 ==> b2) ==>
    SPEC m (p * cond b1) c q``,
  Cases_on `b2` \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_FALSE_PRE]);

val SEP_EXISTS_PRE_POST = prove(
  ``(!x. SPEC m (p x) c (q x)) ==>
    (SPEC m (SEP_EXISTS x. p x) c (SEP_EXISTS x. q x))``,
  SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM (ASSUME_TAC o SPEC_ALL)
  \\ IMP_RES_TAC SPEC_WEAKEN
  \\ POP_ASSUM MATCH_MP_TAC
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
  \\ METIS_TAC []);

val SPEC_PUSH_PRE = prove(
  ``SPEC m (p * cond b) c q ==>
    SPEC m (p * cond b) c (q * cond b)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [SPEC_FALSE_PRE,SEP_CLAUSES]);

val bc_adjust_BlockList = prove(
  ``!msg. bc_adjust (cb,sb,ev) (BlockList (MAP Chr msg)) =
          BlockList (MAP Chr msg)``,
  Induct \\ FULL_SIMP_TAC std_ss [BlockList_def,MAP,bc_adjust_def,
    BlockCons_def,Chr_def,BlockNil_def]);

val zREPL_INV_INR = let
  val th = zHEAP_INR_CASE_REAL
           |> Q.INST [`p`|->`^repl_step_pc`]
           |> RW [WORD_ADD_SUB]
           |> DISCH ``RefPtr outp_ptr::RefPtr inp_ptr::rest = ss``
           |> SIMP_RULE std_ss [] |> UNDISCH_ALL
  val lemma = ``zREPL_STEP_RES (INR (msg,state)) ^repl_step_pc
                 (bs2,cb2,cs,out,p,s,sb2,stack,x)``
              |> SIMP_CONV std_ss [zREPL_STEP_RES_def,zBC_HEAP_def,
                   LET_DEF,SEP_CLAUSES]
  val tm = lemma |> concl |> rand
  val vs = list_dest dest_sep_exists tm
  val tm = last vs
  val vs = butlast vs
  val (pre,c) = dest_star tm
  val b = c |> rand
  val (_,p,_,_) = dest_spec (concl th)
  val m = fst (match_term p pre)
  val th = INST m th
  val th = SPEC_BOOL_FRAME_RULE th b
  val th = th |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
  val th = th |> ONCE_REWRITE_RULE [GSYM SPEC_MOVE_COND]
  val th = MATCH_MP SPEC_PUSH_PRE th
  val th = Q.GEN `rest` th |> HO_MATCH_MP SPEC_IMP_LEMMA
  val th = Q.GEN `inp_ptr` th |> HO_MATCH_MP SPEC_IMP_LEMMA
  val th = Q.GEN `outp_ptr` th |> HO_MATCH_MP SPEC_IMP_LEMMA
  val th = MATCH_MP SPEC_LEMMA2 th
  val goal = th |> concl |> dest_imp |> fst
(*
gg goal
*)
  val lem = prove(goal,
    SIMP_TAC std_ss [COMPILER_RUN_INV_OUTPUT_def] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC COMPILER_RUN_INV_INR
    \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND,TL,bc_adjust_def,CONS_11,bc_value_11]
    \\ FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FUNION_DEF,ref_adjust_def,LET_DEF]
    \\ Q.ABBREV_TAC `ww = p - n2w (LENGTH x64_bootstrap_code)`
    \\ ASM_SIMP_TAC (srw_ss()) [FUN_FMAP_DEF]
    \\ `2 * outp_ptr DIV 2 = outp_ptr` by
         (FULL_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [bc_adjust_def]
    \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [bc_adjust_BlockList]
    \\ cheat) (* s_bc_val needs to be handled more carefully *)
  val th = MP th lem
  val th = HO_MATCH_MP SEP_EXISTS_PRE_POST (GEN (el 3 vs) th)
  val th = HO_MATCH_MP SEP_EXISTS_PRE_POST (GEN (el 2 vs) th)
  val th = HO_MATCH_MP SEP_EXISTS_PRE_POST (GEN (el 1 vs) th)
  val th = CONV_RULE (PRE_CONV (REWR_CONV (GSYM lemma))) th
  (* target precondition reached *)
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``if lex_until_top_semicolon_alt s.input = NONE then
        zHEAP_OUTPUT (cs,STRCAT out msg) \/ zHEAP_ERROR cs
      else
        zREPL_INV bs2 (x,s with <|
            input := lex_until_semi_state s.input;
            local := <|stop_addr := 0x0w; printing_on := 0x1w|> |>,
          STRCAT out msg,stack,cs,cb2,sb2,
          (SOME (FST (THE (lex_until_top_semicolon_alt s.input)),state)),p)
        \/ zHEAP_ERROR cs``
(*
  gg goal
*)
  val lemma = prove(goal,
    Cases_on `lex_until_top_semicolon_alt s.input = NONE` THEN1
     (FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM,cond_STAR]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ `bs2'.output = ""` by cheat (* repl step doesn't produce output *)
      \\ FULL_SIMP_TAC std_ss [APPEND_NIL])
    \\ Q.ABBREV_TAC `pp = p - n2w (LENGTH x64_bootstrap_code)`
    \\ ASM_SIMP_TAC (srw_ss()) [zREPL_INV_def,zBC_HEAP_def,SEP_CLAUSES,LET_DEF]
    \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM,
         cond_STAR,SEP_DISJ_def]
    \\ REPEAT STRIP_TAC
    \\ `bs2'.output = ""` by cheat (* repl step doesn't produce output *)
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL,COMPILER_RUN_INV_OUTPUT_def]
    \\ IMP_RES_TAC COMPILER_RUN_INV_INR
    \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [LET_DEF]
    \\ Cases_on `lex_until_top_semicolon_alt s.input`
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `x''`
    \\ Q.MATCH_ASSUM_RENAME_TAC `lex_until_top_semicolon_alt s.input =
         SOME (ts,rest_of_input)` []
    \\ FULL_SIMP_TAC std_ss []
    \\ FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `ts`)
    \\ Q.ABBREV_TAC `bs3 = (bs2' with
          refs :=
            bs2'.refs |+
            (inp_ptr',
             BlockSome
               (BlockPair (BlockList (MAP BlockSym ts),s_bc_val'))))`
    \\ `bs3.output = ""` by cheat (* repl step doesn't produce output *)
    \\ Q.LIST_EXISTS_TAC [`bs3`,`new_inp`,`out2`,`RefPtr inp_ptr`,`RefPtr inp_ptr`]
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
    \\ DISJ1_TAC \\ STRIP_TAC THEN1 cheat (* silly side conditions *)
    \\ Q.PAT_ASSUM `xx s'` MP_TAC
    \\ MATCH_MP_TAC (METIS_PROVE [] ``(x=y) ==> (x ==> y)``)
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ REPEAT AP_THM_TAC
    \\ REPEAT AP_TERM_TAC
    \\ `bs3.stack = bs2'.stack` by FULL_SIMP_TAC (srw_ss()) [Abbr `bs3`]
    \\ `bs3.handler = bs2'.handler` by FULL_SIMP_TAC (srw_ss()) [Abbr `bs3`]
    \\ FULL_SIMP_TAC std_ss []
    \\ cheat) (* inp_ptr needs to be instantiated with 2 * inp_ptr *)
  val th = MP th lemma
  val th = th |> SIMP_RULE std_ss [word_arith_lemma1]
  in th end

val env_rs_init = prove(
  ``env_rs [] (repl_decs_cenv ++ init_envC) (0,repl_decs_s)
        repl_decs_env new_compiler_state 0 rd s2 ==>
    ?inp outp.
      INPUT_TYPE NONE inp ∧ bs_no_sp s2 ∧ COMPILER_RUN_INV s2 inp outp``,
  cheat); (* needs to move to bootstrap_lemmasTheory *)

val zREPL_INV_INIT = let
  val th = SPEC_COMPOSE_RULE [zHEAP_INIT,zHEAP_PUSH1,SPEC_repl_decs]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``INIT_STATE init * ¬zS * zPC p * cond (EVEN (w2n p))``
  val lemma = prove(goal,
    ONCE_REWRITE_TAC [STAR_COMM]
    \\ Q.SPEC_TAC (`INIT_STATE init * ¬zS * zPC p`,`r`)
    \\ MATCH_MP_TAC SEP_IMP_FRAME
    \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,cond_def]
    \\ SIMP_TAC std_ss [EVEN_w2n] \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val pc = get_pc th
  val th = MATCH_MP SPEC_PUSH_PRE th
  val th = SPEC_BOOL_FRAME_RULE th
             ``EVEN (w2n ((p:word64) - n2w (LENGTH x64_bootstrap_code)))``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zREPL_INV empty_bc_state (Number 0,first_s init,"",[],
        full_cs init p,cb2,sb2,NONE,^(pc |> rand)) \/
      zHEAP_ERROR (full_cs init p)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zREPL_INV_def,SEP_IMP_def,cond_STAR,SEP_IMP_def,
       SEP_DISJ_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ DISJ1_TAC
    \\ IMP_RES_TAC env_rs_init
    \\ Q.LIST_EXISTS_TAC [`s2`,`inp`,`outp`]
    \\ FULL_SIMP_TAC std_ss [EVAL ``empty_bc_state.refs``,
         EVAL ``empty_bc_state.stack``,MAP,APPEND,ref_adjust_FEMPTY]
    \\ FULL_SIMP_TAC std_ss [GSYM word_arith_lemma1,WORD_ADD_SUB]
    \\ ASM_SIMP_TAC std_ss [Once bs_no_sp_zBC_HEAP]
    \\ Q.PAT_ASSUM `xxx s` MP_TAC
    \\ ASM_SIMP_TAC std_ss [Once bs_no_sp_zBC_HEAP]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `EVEN (w2n p)` MP_TAC
    \\ FULL_SIMP_TAC std_ss [EVEN_w2n] \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  in th end

val TEMPORAL_FULL_BC_EXEC_TUNED = let
  val th = TEMPORAL_FULL_BC_EXEC |> Q.GENL [`cb`,`sb`]
           |> Q.INST [`stack`|->`[]`,`ev`|->`F`]
           |> SIMP_RULE std_ss [LENGTH]
  in th end

(*

bc_next_rules

  zREPL_INV_INIT
  |> RW [SPEC_EQ_TEMPORAL]

  SPEC_repl_step_REPL_INV

  zREPL_INV_INR

  zHEAP_INL_CASE_UP_TO_BC_EVAL
  TEMPORAL_FULL_BC_EXEC
  zHEAP_INL_CASE_AFTER_BC_EVAL

  COMPILER_RUN_INV_INL
  repl_fun_alt_proofTheory.main_loop_alt'_def
  repl_fun_alt_proofTheory.repl_fun_alt'_def

  print_match ["arithmetic"] ``~(ODD n)``

open sptreeTheory

  insert_def
  lookup_def

  if EVEN (Num (getNumber x2)) then ... else ...
  let x2 = x2 DIV 2 in
  let x2 = Number (getNumber x2 − 1) in
  if getNumber x2 = 0 then _ else _
  if getNumber x2 = 0 then _ else _


  X64_MODEL:  let x1 = BlockNil in _
  X64_MODEL:  let x1 = BlockCons (x1,x2) in _
  X64_MODEL:  let x1 = BlockCons (x1,x3) in _
  X64_MODEL:  let x1 = BlockCons (x1,x4) in _
  X64_MODEL:  let x1 = BlockCons (x2,x1) in _
  X64_MODEL:  let x1 = BlockCons (x2,x3) in _
  X64_MODEL:  let x1 = BlockCons (x2,x4) in _
  X64_MODEL:  let x1 = BlockCons (x3,x1) in _
  X64_MODEL:  let x1 = BlockCons (x3,x2) in _
  X64_MODEL:  let x1 = BlockCons (x3,x4) in _
  X64_MODEL:  let x1 = BlockCons (x4,x1) in _
  X64_MODEL:  let x1 = BlockCons (x4,x2) in _
  X64_MODEL:  let x1 = BlockCons (x4,x3) in _
  X64_MODEL:  let x1 = BlockErrorS in _
  X64_MODEL:  let x1 = BlockLongS x1 in _
  X64_MODEL:  let x1 = BlockNumberS x1 in _
  X64_MODEL:  let x1 = BlockOtherS x1 in _
  X64_MODEL:  let x1 = BlockPair (x1,x2) in _
  X64_MODEL:  let x1 = BlockPair (x1,x3) in _
  X64_MODEL:  let x1 = BlockPair (x1,x4) in _
  X64_MODEL:  let x1 = BlockPair (x2,x1) in _
  X64_MODEL:  let x1 = BlockPair (x2,x3) in _
  X64_MODEL:  let x1 = BlockPair (x2,x4) in _
  X64_MODEL:  let x1 = BlockPair (x3,x1) in _
  X64_MODEL:  let x1 = BlockPair (x3,x2) in _
  X64_MODEL:  let x1 = BlockPair (x3,x4) in _
  X64_MODEL:  let x1 = BlockPair (x4,x1) in _
  X64_MODEL:  let x1 = BlockPair (x4,x2) in _
  X64_MODEL:  let x1 = BlockPair (x4,x3) in _

val spt_to_bv_def = Define `
  (spt_to_bv LN = BlockNil) /\
  (spt_to_bv (LS x) = BlockSome x) /\
  (spt_to_bv (BN t1 t2) =
    BlockPair (Number 1, BlockPair (spt_to_bv t1, spt_to_bv t2))) /\
  (spt_to_bv (BS t1 x t2) =
    BlockCons (x, BlockPair (spt_to_bv t1, spt_to_bv t2)))`;



*)

print_compiler_grammar()

*)

val _ = export_theory();
