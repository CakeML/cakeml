(*
  The formal semantics of prewordLang
*)
open preamble prewordLangTheory;
local open alignmentTheory ffiTheory in end;

val _ = new_theory"prewordSem";
val _ = set_grammar_ancestry [
  "prewordLang", "alignment",
  "finite_map", "misc",
  "ffi", "machine_ieee" (* for FP *)
]

Datatype:
  word_loc = Word ('a word) | Loc num num
End

Definition mem_load_byte_aux_def:
  mem_load_byte_aux m dm be w =
    case m (byte_align w) of
    | Loc _ _ => NONE
    | Word v =>
        if byte_align w IN dm
        then SOME (get_byte w v be) else NONE
End

Definition mem_store_byte_aux_def:
  mem_store_byte_aux m dm be w b =
    case m (byte_align w) of
    | Word v =>
        if byte_align w IN dm
        then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
        else NONE
    | _ => NONE
End

Definition write_bytearray_def:
  (write_bytearray a [] m dm be = m) /\
  (write_bytearray a (b::bs) m dm be =
     case mem_store_byte_aux (write_bytearray (a+1w) bs m dm be) dm be a b of
     | SOME m => m
     | NONE => m)
End

Datatype:
  state =
    <| locals  : ('a word_loc) num_map
     ; fp_regs : num |-> word64 (* FP regs are treated "globally" *)
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; clock   : num
     ; code    : (num # ('a prewordLang$prog)) num_map
     ; be      : bool
     ; ffi     : 'ffi ffi_state |>
End


val state_component_equality = theorem"state_component_equality";

Datatype:
  result = Result    ('w word_loc)
         | Exception ('w word_loc)
         | TimeOut
         | FinalFFI final_event
         | Error   (* should we add Continue and Break *)
End


val s = ``(s:('a,'ffi) prewordSem$state)``

Definition dec_clock_def:
  dec_clock ^s = s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res,new_s) =
    (res,new_s with
      <| clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)
End

Definition is_word_def:
  (is_word (Word w) = T) /\
  (is_word _ = F)
End

Definition get_word_def:
  get_word (Word w) = w
End

val _ = export_rewrites["is_word_def","get_word_def"];

Definition mem_store_def:
  mem_store (addr:'a word) (w:'a word_loc) ^s =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE
End

Definition mem_load_def:
  mem_load (addr:'a word) ^s =
    if addr IN s.mdomain then
      SOME (s.memory addr)
    else NONE
End

Definition the_words_def:
  (the_words [] = SOME []) /\
  (the_words (w::ws) =
     case (w,the_words ws) of
      | SOME (Word x), SOME xs => SOME (x::xs)
      | _ => NONE)
End

Definition word_exp_def:
  (word_exp ^s (Const w) = SOME (Word w)) /\
  (word_exp s (Var v) = lookup v s.locals) /\
  (word_exp s (Load addr) =
     case word_exp s addr of
     | SOME (Word w) => mem_load w s
     | _ => NONE) /\
  (word_exp s (Op op wexps) =
     case the_words (MAP (word_exp s) wexps) of
     | SOME ws => (OPTION_MAP Word (word_op op ws))
     | _ => NONE) /\
  (word_exp s (Shift sh wexp n) =
     case word_exp s wexp of
     | SOME (Word w) => OPTION_MAP Word (word_sh sh w n)
     | _ => NONE)
Termination
  (WF_REL_TAC `measure (exp_size ARB o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ DECIDE_TAC)
End

(*
val get_var_def = Define `
  get_var v ^s = sptree$lookup v s.locals`;
*)

Definition get_vars_def:
  (get_vars [] ^s = SOME []) /\
  (get_vars (v::vs) s =
     case sptree$lookup v s.locals of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))
End

Definition set_var_def:
  set_var v x ^s =
  (s with locals := (insert v x s.locals))
End

Definition set_vars_def:
  set_vars vs xs ^s =
  (s with locals := (alist_insert vs xs s.locals))
End

Definition find_code_def:
  (find_code (SOME p) args code =
     case sptree$lookup p code of
     | NONE => NONE
     | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp)
                                                    else NONE) /\
  (find_code NONE args code =
     if args = [] then NONE else
       case LAST args of
       | Loc loc 0 =>
           (case lookup loc code of
            | NONE => NONE
            | SOME (arity,exp) => if LENGTH args = arity + 1
                                  then SOME (FRONT args,exp)
                                  else NONE)
      | other => NONE)
End

Definition assign_def:
  assign reg exp ^s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg w s)
End

Definition get_fp_var_def:
  get_fp_var v (s:('a,'ffi) prewordSem$state) = FLOOKUP s.fp_regs v
End

Definition set_fp_var_def:
  set_fp_var v x (s:('a,'ffi) prewordSem$state) =
  (s with fp_regs := (s.fp_regs |+ (v,x)))
End

Definition inst_def:
  inst i ^s =
    case i of
    | Skip => SOME s
    | Const reg w => assign reg (Const w) s
    | Arith (Binop bop r1 r2 ri) =>
        assign r1
          (Op bop [Var r2; case ri of Reg r3 => Var r3
                                    | Imm w => Const w]) s
    | Arith (Shift sh r1 r2 n) =>
        assign r1
        (Shift sh (Var r2) n) s
    | Arith (Div r1 r2 r3) =>
       (let vs = get_vars[r3;r2] s in
       case vs of
       SOME [Word q;Word w2] =>
         if q ≠ 0w then
           SOME (set_var r1 (Word (w2 / q)) s)
         else NONE
       | _ => NONE)
    | Arith (AddCarry r1 r2 r3 r4) =>
        (let vs = get_vars [r2;r3;r4] s in
        case vs of
        SOME [Word l;Word r;Word c] =>
          let res = w2n l + w2n r + if c = (0w:'a word) then 0 else 1 in
            SOME (set_var r4 (Word (if dimword(:'a) ≤ res then (1w:'a word) else 0w))
                 (set_var r1 (Word (n2w res)) s))

        | _ => NONE)
    | Arith (AddOverflow r1 r2 r3 r4) =>
        (let vs = get_vars [r2;r3] s in
        case vs of
        SOME [Word w2;Word w3] =>
          SOME (set_var r4 (Word (if w2i (w2 + w3) ≠ w2i w2 + w2i w3 then 1w else 0w))
                 (set_var r1 (Word (w2 + w3)) s))
        | _ => NONE)
    | Arith (SubOverflow r1 r2 r3 r4) =>
        (let vs = get_vars [r2;r3] s in
        case vs of
        SOME [Word w2;Word w3] =>
          SOME (set_var r4 (Word (if w2i (w2 - w3) ≠ w2i w2 - w2i w3 then 1w else 0w))
                 (set_var r1 (Word (w2 - w3)) s))
        | _ => NONE)
    | Arith (LongMul r1 r2 r3 r4) =>
        (let vs = get_vars [r3;r4] s in
        case vs of
        SOME [Word w3;Word w4] =>
         let r = w2n w3 * w2n w4 in
           SOME (set_var r2 (Word (n2w r)) (set_var r1 (Word (n2w (r DIV dimword(:'a)))) s))
        | _ => NONE)
   | Arith (LongDiv r1 r2 r3 r4 r5) =>
       (let vs = get_vars [r3;r4;r5] s in
       case vs of
       SOME [Word w3;Word w4;Word w5] =>
         let n = w2n w3 * dimword (:'a) + w2n w4 in
         let d = w2n w5 in
         let q = n DIV d in
         if (d ≠ 0 ∧ q < dimword(:'a)) then
           SOME (set_var r1 (Word (n2w q)) (set_var r2 (Word (n2w (n MOD d))) s))
         else NONE
      | _ => NONE)
    | Mem Load r (Addr a w) =>
       (case word_exp s (Op Add [Var a; Const w]) of
        | SOME (Word w) =>
           (case mem_load w s of
            | NONE => NONE
            | SOME w => SOME (set_var r w s))
        | _ => NONE)
    | Mem Load8 r (Addr a w) =>
       (case word_exp s (Op Add [Var a; Const w]) of
        | SOME (Word w) =>
           (case mem_load_byte_aux s.memory s.mdomain s.be w of
            | NONE => NONE
            | SOME w => SOME (set_var r (Word (w2w w)) s))
           | _ => NONE)
    | Mem Store r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), lookup r s.locals) of
        | (SOME (Word a), SOME w) =>
            (case mem_store a w s of
             | SOME s1 => SOME s1
             | NONE => NONE)
        | _ => NONE)
    | Mem Store8 r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), lookup r s.locals) of
        | (SOME (Word a), SOME (Word w)) =>
            (case mem_store_byte_aux s.memory s.mdomain s.be a (w2w w) of
             | SOME new_m => SOME (s with memory := new_m)
             | NONE => NONE)
        | _ => NONE)
    | FP (FPLess r d1 d2) =>
      (case (get_fp_var d1 s,get_fp_var d2 s) of
      | (SOME f1 ,SOME f2) =>
        SOME (set_var r
          (Word (if fp64_lessThan f1 f2
                 then 1w
                 else 0w)) s)
      | _ => NONE)
    | FP (FPLessEqual r d1 d2) =>
      (case (get_fp_var d1 s,get_fp_var d2 s) of
      | (SOME f1, SOME f2) =>
        SOME (set_var r
          (Word (if fp64_lessEqual f1 f2
                 then 1w
                 else 0w)) s)
      | _ => NONE)
    | FP (FPEqual r d1 d2) =>
      (case (get_fp_var d1 s,get_fp_var d2 s) of
      | (SOME f1, SOME f2) =>
        SOME (set_var r
          (Word (if fp64_equal f1 f2
                 then 1w
                 else 0w)) s)
      | _ => NONE)
    | FP (FPMov d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 f s)
      | _ => NONE)
    | FP (FPAbs d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 (fp64_abs f) s)
      | _ => NONE)
    | FP (FPNeg d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 (fp64_negate f) s)
      | _ => NONE)
    | FP (FPSqrt d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 (fp64_sqrt roundTiesToEven f) s)
      | _ => NONE)
    | FP (FPAdd d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPSub d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPMul d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPDiv d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPFma d1 d2 d3) =>
      (case (get_fp_var d1 s, get_fp_var d2 s, get_fp_var d3 s) of
      | (SOME f1, SOME f2, SOME f3) =>
        SOME (set_fp_var d1 (fpSem$fpfma f1 f2 f3) s)
      | _ => NONE)
    | FP (FPMovToReg r1 r2 d) =>
      (case get_fp_var d s of
      | SOME v =>
        if dimindex(:'a) = 64 then
          SOME (set_var r1 (Word (w2w v)) s)
        else
          SOME (set_var r2 (Word ((63 >< 32) v)) (set_var r1 (Word ((31 >< 0) v)) s))
      | _ => NONE)
    | FP (FPMovFromReg d r1 r2) =>
      (if dimindex(:'a) = 64 then
        case lookup r1 s.locals of
          SOME (Word w1) => SOME (set_fp_var d (w2w w1) s)
        | _ => NONE
      else
        case (lookup r1 s.locals,lookup r2 s.locals) of
          (SOME (Word w1),SOME (Word w2)) => SOME (set_fp_var d (w2 @@ w1) s)
        | _ => NONE)
    | FP (FPToInt d1 d2) =>
      (case get_fp_var d2 s of
        NONE => NONE
      | SOME f =>
      case fp64_to_int roundTiesToEven f of
        NONE => NONE
      | SOME i =>
        let w = i2w i : word32 in
        if w2i w = i then
          (if dimindex(:'a) = 64 then
             SOME (set_fp_var d1 (w2w w) s)
           else
           case get_fp_var (d1 DIV 2) s of
             NONE => NONE
           | SOME f =>
             let (h, l) = if ODD d1 then (63, 32) else (31, 0) in
                  SOME (set_fp_var (d1 DIV 2) (bit_field_insert h l w f) s))
        else
          NONE)
    | FP (FPFromInt d1 d2) =>
      if dimindex(:'a) = 64 then
        case get_fp_var d2 s of
        | SOME f =>
          let i =  w2i ((31 >< 0) f : word32) in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
      else
        case get_fp_var (d2 DIV 2) s of
        | SOME v =>
          let i =  w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : 'a word) in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
    | _ => NONE
End

Definition get_var_imm_def:
  (get_var_imm ((Reg n):'a reg_imm) ^s = sptree$lookup n s.locals) ∧
  (get_var_imm (Imm w) s = SOME(Word w))
End

Theorem fix_clock_IMP_LESS_EQ:
  !x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock
Proof
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] \\
  srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Definition call_env_def:
  call_env args ^s =
    s with <| locals := fromList args |>
End

Definition evaluate_def:
  (evaluate (Skip:'a prewordLang$prog,^s) = (NONE,s)) /\
  (evaluate (Assign v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v w s)) /\
  (evaluate (Store exp v,s) =
     case (word_exp s exp, lookup v s.locals) of
     | (SOME (Word adr), SOME w) =>
         (case mem_store adr w s of
          | SOME st => (NONE, st)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (StoreGlob exp v,s) =
     ARB) /\
  (evaluate (LoadGlob exp v,s) =
     ARB) /\
  (evaluate (Inst i,s) =
     case inst i s of
     | SOME s1 => (NONE, s1)
     | NONE => (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If cmp r1 ri c1 c2,s) =
    (case (lookup r1 s.locals,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then evaluate (c1,s)
                          else evaluate (c2,s)
    | _ => (SOME Error,s))) /\
  (evaluate (Raise n,s) =
     case lookup n s.locals of
     | NONE => (SOME Error,s)
     | SOME w => (SOME (Exception w),s)) /\
  (evaluate (Return n,s) =
     case lookup n s.locals of
     | SOME v => (SOME (Result v),call_env [] s)
     | _ => (SOME Error,s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s)
     else (NONE,dec_clock s)) /\
  (evaluate (LocValue v v',s) = ARB) /\
  (evaluate (Call ret dest argvars handler,s) =
    case get_vars argvars s of
    | NONE => (SOME Error,s)
    | SOME argvals =>
      if (dest = NONE /\ argvals = []) then (SOME Error,s)
      else
        case find_code dest argvals s.code of
        | NONE => (SOME Error,s)
        | SOME (args,prog) =>
          case ret of
          | NONE (* tail call *) =>
            if handler = NONE then
             if s.clock = 0 then (SOME TimeOut,call_env [] s)
             else (case evaluate (prog, call_env args (dec_clock s)) of
                    | (NONE,s) => (SOME Error,s)
                    | (SOME res,s) => (SOME res,s))
           else (SOME Error,s) (* tail-call requires no handler *)
          | SOME n (* returning call, returns into var n *) =>
              if s.clock = 0 then (SOME TimeOut,call_env [] s)
              else (case fix_clock (call_env args (dec_clock s))
                                   (evaluate (prog, call_env args (dec_clock s))) of
                      | (NONE,st) => (SOME Error,st)
                      | (SOME (Result retv),st) => (NONE, set_var n retv st)
                      | (SOME (Exception exn),st) =>
                          (case handler of (* if handler is present, then handle exc *)
                            | NONE => (SOME (Exception exn),st)
                            | SOME (n,h) => evaluate (h, set_var n exn st))
                          | res => res)) /\
  (evaluate (FFI ffi_index ptr1 len1 ptr2 len2,s) =
    case (lookup len1 s.locals, lookup ptr1 s.locals, lookup len2 s.locals, lookup ptr2 s.locals) of
    | SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4) =>
       (case (read_bytearray w2 (w2n w) (mem_load_byte_aux s.memory s.mdomain s.be),
               read_bytearray w4 (w2n w3) (mem_load_byte_aux s.memory s.mdomain s.be))
               of
          | SOME bytes,SOME bytes2 =>
             (case call_FFI s.ffi ffi_index bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),call_env [] s)
              | FFI_return new_ffi new_bytes =>
                let new_m = write_bytearray w4 new_bytes s.memory s.mdomain s.be in
                  (NONE, s with <| memory := new_m ;
                                   ffi := new_ffi |>))
          | _ => (SOME Error,s))
    | res => (SOME Error,s))
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure (prog_size (K 0)))
               (\(xs,^s). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac (GSYM fix_clock_IMP_LESS_EQ)
  \\ full_simp_tac(srw_ss())[set_var_def,call_env_def,dec_clock_def, LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ decide_tac
End




val evaluate_ind = theorem"evaluate_ind";

(*
(* We prove that the clock never increases and that termdep is constant. *)

Theorem gc_clock:
   !s1 s2. (gc s1 = SOME s2) ==> s2.clock <= s1.clock /\ s2.termdep = s1.termdep
Proof
  full_simp_tac(srw_ss())[gc_def,LET_DEF] \\ SRW_TAC [] []
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
QED

Theorem alloc_clock:
   !xs s1 vs s2. (alloc x names s1 = (vs,s2)) ==>
                  s2.clock <= s1.clock /\ s2.termdep = s1.termdep
Proof
  SIMP_TAC std_ss [alloc_def] \\ rpt gen_tac
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac gc_clock
  \\ rpt (disch_then strip_assume_tac)
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[push_env_def,set_store_def,call_env_def
                            ,LET_THM,pop_env_def,flush_state_def]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
QED

val inst_clock = Q.prove(
  `inst i s = SOME s2 ==> s2.clock <= s.clock /\ s2.termdep = s.termdep`,
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,get_vars_def,LET_THM]
  \\ every_case_tac
  \\ SRW_TAC [] [set_var_def] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[mem_store_def] \\ SRW_TAC [] []
  \\ EVAL_TAC \\ fs[]);

Theorem evaluate_clock:
   !xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==>
                 s2.clock <= s1.clock /\ s2.termdep = s1.termdep
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ rpt (disch_then strip_assume_tac)
  \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt (pop_assum mp_tac)
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  \\ rpt (disch_then strip_assume_tac)
  \\ imp_res_tac alloc_clock \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[set_vars_def,set_var_def,set_store_def]
  \\ imp_res_tac inst_clock \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[mem_store_def,call_env_def,dec_clock_def,flush_state_def]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[jump_exc_def,pop_env_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac LESS_EQ_TRANS \\ full_simp_tac(srw_ss())[]
  \\ TRY (Cases_on `handler`)
  \\ TRY (PairCases_on `x`)
  \\ TRY (PairCases_on `x''`)
  \\ full_simp_tac(srw_ss())[push_env_def,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ decide_tac
QED

val fix_clock_evaluate = Q.prove(
  `fix_clock s (evaluate (c1,s)) = evaluate (c1,s)`,
  Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[fix_clock_def]
  \\ imp_res_tac evaluate_clock \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]
  \\ full_simp_tac(srw_ss())[state_component_equality]);

(* We store the theorems without fix_clock *)

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

(* observational semantics *)

val semantics_def = Define `
  semantics ^s start =
  let prog = Call NONE (SOME start) [0] NONE in
  if ∃k. case FST(evaluate (prog,s with clock := k)) of
         | SOME (Exception _ _) => T
         | SOME (Result ret _) => ret <> Loc 1 0
         | SOME Error => T
         | NONE => T
         | _ => F
  then Fail
  else
    case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (r,t) ∧
        (case r of
         | (SOME (FinalFFI e)) => outcome = FFI_outcome e
         | (SOME (Result _ _)) => outcome = Success
         | (SOME NotEnoughSpace) => outcome = Resource_limit_hit
         | _ => F) ∧
        res = Terminate outcome t.ffi.io_events
      of
    | SOME res => res
    | NONE =>
      Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList
              (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))`;

Definition word_lang_safe_for_space_def:
  word_lang_safe_for_space (s:('a,'c,'ffi) wordSem$state) start =
    let prog = Call NONE (SOME start) [0] NONE in
      (!k res t. wordSem$evaluate (prog, s with clock := k) = (res,t) ==>
        ?max. t.stack_max = SOME max /\ max <= t.stack_limit)
End
*)

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
