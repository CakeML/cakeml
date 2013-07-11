open prelude;

val _ = new_theory "x64_heap";

open x64_copying_gcTheory;


(* definition of zHEAP *)

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
                    equal_ptr : word64 |>`;

val _ = Hol_datatype ` (* called vs *)
  zheap_vars = <| current_heap : word64 ;
                  other_heap : word64 ;
                  base_ptr : word64 ;
                  handler_ptr : word64 |>`;

val _ = Hol_datatype ` (* called s *)
  zheap_state = <| input : string ;
                   output : string ;
                   handler : word64 |>`;

val _ = Hol_datatype ` (* called vals *)
  x64_vals = <| reg0 : word64 ;
                reg1 : word64 ;
                reg2 : word64 ;
                reg3 : word64 ;
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
      [vs.current_heap;      (* pointer to currently used heap half *)
       vs.other_heap;        (* pointer to the other heap half *)
       n2w (cs.heap_limit);  (* size of each heap half *)
       cs.putchar_ptr;       (* pointer to C's putchar method *)
       cs.getchar_ptr;       (* pointer to C's getchar method *)
       cs.error_ptr;         (* pointer to abort code which writes error message *)
       cs.alloc_ptr;         (* pointer to heap alloc routine *)
       cs.bignum_ptr;        (* pointer to entry point for bignum library *)
       cs.equal_ptr;         (* pointer to routine for rec equality check *)
       vs.handler_ptr
      ]`;

val not_0w_def = Define `not_0w = ~0w`;

val heap_inv_def = Define `
  heap_inv (cs,x1,x2,x3,x4,refs,stack,s:zheap_state,space) vals =
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
      (vs.handler_ptr = s.handler) /\
      cs.heap_limit < 281474976710656 /\ (* 2**(64-16) *)
      (x64_heap vs.current_heap heap vs.current_heap vs.current_heap *
       one_list_exists vs.other_heap cs.heap_limit *
       x64_store cs vs) (fun2set (vals.memory,vals.memory_domain)) /\
      (vals.stack = MAP (x64_addr vs.current_heap) roots ++
                    0x1w::cs.ret_address::cs.rest_of_stack) /\
      (vals.input_stream = MAP (n2w o ORD) (DROP 1 s.input)) /\
      (vals.output_stream = MAP (n2w o ORD) s.output) /\
      heap_vars_ok vs`

val zVALS_def = Define `
  zVALS cs vals =
    zR 0w vals.reg0 *
    zR 1w vals.reg1 *
    zR 2w vals.reg2 *
    zR 3w vals.reg3 *
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
    zSTACK (ARB,vals.stack) *
    zMEMORY64 vals.memory_domain vals.memory *
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
  zHEAP_ERROR (cs,output) = zHEAP_OUTPUT (cs,output ++ error_msg)`;


(* generic lemmas *)

val SPEC_WEAKEN_LEMMA = store_thm("SPEC_WEAKEN_LEMMA",
  ``(b ==> SPEC m (p * cond i) c q1) ==>
    !q2. (i ==> b /\ SEP_IMP q1 q2) ==>
         SPEC m (p * cond i) c q2``,
  Cases_on `i` THEN Cases_on `b` THEN SIMP_TAC std_ss [SPEC_MOVE_COND]
  THEN METIS_TAC [SPEC_WEAKEN]);

val w2w_ADD_sw2sw_SUB = store_thm("w2w_ADD_sw2sw_SUB",
  ``!x y. x <+ 0x20000000w /\ y <+ 0x20000000w ==>
          (w2w x + sw2sw (y - x) = (w2w:word32 -> word64) y)``,
  REPEAT GEN_TAC THEN blastLib.BBLAST_TAC);


val _ = export_theory();
