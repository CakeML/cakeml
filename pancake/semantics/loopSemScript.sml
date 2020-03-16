(*
  The formal semantics of loopLang
*)
open preamble loopLangTheory;
local open
   alignmentTheory
   wordSemTheory
   ffiTheory in end;

val _ = new_theory"loopSem";
val _ = set_grammar_ancestry [
  "loopLang", "alignment",
  "finite_map", "misc", "wordSem",
  "ffi", "machine_ieee" (* for FP *)
]

Datatype:
  state =
    <| locals  : ('a word_loc) num_map
     ; globals : 5 word  |-> 'a word_loc
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; clock   : num
     ; code    : (num list # ('a loopLang$prog)) num_map
     ; be      : bool
     ; ffi     : 'ffi ffi_state |>
End

val state_component_equality = theorem "state_component_equality";

Datatype:
  result = Result    ('w word_loc)
         | Exception ('w word_loc)
         | Break
         | Continue
         | TimeOut
         | FinalFFI final_event
         | Error
End

val s = ``(s:('a,'ffi) loopSem$state)``

Definition dec_clock_def:
  dec_clock ^s = s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res,new_s) =
    (res,new_s with
      <| clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)
End

Definition set_global_def:
  set_global gv w ^s =
    (s with globals := s.globals |+ (gv,w))
End

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

Definition eval_def:
  (eval ^s ((Const w):'a loopLang$exp) = SOME (Word w)) /\
  (eval s (Var v) = lookup v s.locals) /\
  (eval s (Lookup name) = FLOOKUP s.globals name) /\
  (eval s (Load addr) =
     case eval s addr of
     | SOME (Word w) => mem_load w s
     | _ => NONE) /\
  (eval s (Op op wexps) =
     case the_words (MAP (eval s) wexps) of
     | SOME ws => (OPTION_MAP Word (word_op op ws))
     | _ => NONE) /\
  (eval s (Shift sh wexp n) =
     case eval s wexp of
     | SOME (Word w) => OPTION_MAP Word (word_sh sh w n)
     | _ => NONE)
Termination
  WF_REL_TAC `measure (exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC
End

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
     | SOME (params,exp) => if LENGTH args = LENGTH params
                            then SOME (fromAList (ZIP (params, args)),exp) else NONE) /\
  (find_code NONE args code =
     if args = [] then NONE else
       case LAST args of
       | Loc loc 0 =>
           (case lookup loc code of
            | NONE => NONE
            | SOME (params,exp) => if LENGTH args = LENGTH params + 1
                                   then SOME (fromAList (ZIP (params, FRONT args)),exp)
                                   else NONE)
      | other => NONE)
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

Definition cut_state_def:
  cut_state live s =
    if domain live SUBSET domain s.locals then
      SOME (s with locals := inter s.locals live)
    else NONE
End

Definition cut_res_def:
  cut_res live (res,s) =
    if res ≠ NONE then (res,s) else
      case cut_state live s of
      | NONE => (SOME Error,s)
      | SOME s => if s.clock = 0 then (SOME TimeOut,s with locals := LN)
                  else (res,dec_clock s)
End

Definition evaluate_def:
  (evaluate (Skip:'a loopLang$prog,^s) = (NONE, s)) /\
  (evaluate (Fail:'a loopLang$prog,^s) = (SOME Error, s)) /\
  (evaluate (Assign v exp,s) =
     case eval s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v w s)) /\
  (evaluate (Store exp v,s) =
     case (eval s exp, lookup v s.locals) of
     | (SOME (Word adr), SOME w) =>
         (case mem_store adr w s of
          | SOME st => (NONE, st)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (SetGlobal dst exp,s) =
     case eval s exp of
     | SOME w => (NONE, set_global dst w s)
     | _ => (SOME Error, s)) /\
  (evaluate (LoadByte dst src,s) = (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If cmp r1 ri c1 c2 live_out,s) =
    (case (lookup r1 s.locals,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
        let b = word_cmp cmp x y in
          cut_res live_out (evaluate (if b then c1 else c2,s))
    | _ => (SOME Error,s))) /\
  (evaluate (Mark p,s) = evaluate (p,s)) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\
  (evaluate (Loop live_in body live_out,s) =
    (case cut_res live_in (NONE,s) of
     | (NONE,s) =>
        (case fix_clock s (evaluate (body,s)) of
         | (SOME Continue,s) => evaluate (Loop live_in body live_out,s)
         | (SOME Break,s) => cut_res live_out (NONE,s)
         | (NONE,s) => (SOME Error,s)
         | res => res)
     | res => res)) /\
  (evaluate (Raise n,s) =
     case lookup n s.locals of
     | NONE => (SOME Error,s)
     | SOME w => (SOME (Exception w),call_env [] s)) /\
  (evaluate (Return n,s) =
     case lookup n s.locals of
     | SOME v => (SOME (Result v),call_env [] s)
     | _ => (SOME Error,s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,s with locals := LN)
     else (NONE,dec_clock s)) /\
  (evaluate (LocValue r l1,s) =
     if l1 ∈ domain s.code then
       (NONE,set_var r (Loc l1 0) s)
     else (SOME Error,s)) /\
  (evaluate (Call ret dest argvars handler,s) =
    case get_vars argvars s of
    | NONE => (SOME Error,s)
    | SOME argvals =>
       (case find_code dest argvals s.code of
        | NONE => (SOME Error,s)
        | SOME (env,prog) =>
         (case ret of
          | NONE (* tail call *) =>
            (if handler <> NONE then (SOME Error,s) else
               if s.clock = 0 then (SOME TimeOut,s with locals := LN)
               else (case evaluate (prog, dec_clock s with locals := env) of
                     | (NONE,s) => (SOME Error,s)
                     | (SOME Continue,s) => (SOME Error,s)
                     | (SOME Break,s) => (SOME Error,s)
                     | (SOME res,s) => (SOME res,s)))
          | SOME (n,live) =>
            (case cut_res live (NONE,s) of
             | (NONE,s) =>
                 (case fix_clock (s with locals := env)
                         (evaluate (prog, s with locals := env))
                   of (SOME (Result retv),st) =>
                        (case handler of (* if handler is present, then finalise *)
                         | NONE => (NONE, set_var n retv (st with locals := s.locals))
                         | SOME (_,_,r,live_out) =>
                             cut_res live_out
                               (evaluate (r, set_var n retv (st with locals := s.locals))))
                    | (SOME (Exception exn),st) =>
                        (case handler of (* if handler is present, then handle exc *)
                         | NONE => (SOME (Exception exn),(st with locals := LN))
                         | SOME (n,h,_,live_out) =>
                             cut_res live_out
                               (evaluate (h, set_var n exn (st with locals := s.locals))))
                    | (SOME Continue,st) => (SOME Error, st)
                    | (SOME Break,st) => (SOME Error, st)
                    | (NONE,st) => (SOME Error, st)
                    | res => res)
             | res => res)))) /\
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
  \\ full_simp_tac(srw_ss())[set_var_def,call_env_def,dec_clock_def,set_global_def,
       LET_THM,cut_res_def,CaseEq"option",pair_case_eq,CaseEq"bool"]
  \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ fs [cut_state_def]
  \\ every_case_tac \\ rveq \\ full_simp_tac(srw_ss())[]
  \\ decide_tac
End

(* We prove that the clock never increases *)

Theorem evaluate_clock:
  !xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  recInduct evaluate_ind \\ rpt strip_tac
  \\ pop_assum mp_tac \\ once_rewrite_tac [evaluate_def]
  \\ rpt (disch_then strip_assume_tac)
  \\ fs [] \\ rveq \\ fs []
  \\ fs [CaseEq"option",pair_case_eq] \\ rveq \\ fs []
  \\ fs [cut_res_def]
  \\ fs [CaseEq"option",pair_case_eq,CaseEq"bool"] \\ rveq \\ fs []
  \\ fs [CaseEq"option",CaseEq"word_loc",mem_store_def,CaseEq"bool",set_global_def,
         cut_state_def,pair_case_eq,CaseEq"ffi_result",cut_res_def,CaseEq"word_loc"]
  \\ fs [] \\ rveq \\ fs [set_var_def,set_global_def,dec_clock_def,call_env_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [CaseEq"option",CaseEq"word_loc",mem_store_def,CaseEq"bool",CaseEq"result",
         pair_case_eq,cut_res_def]
  \\ fs [] \\ rveq \\ fs [set_var_def,set_global_def]
  \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ fs []
  \\ rename [‘cut_res _ xx’] \\ PairCases_on ‘xx’ \\ fs []
  \\ fs [cut_res_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [cut_state_def]
  \\ rveq \\ fs [cut_state_def,dec_clock_def]
QED

Theorem fix_clock_evaluate:
  fix_clock s (evaluate (c1,s)) = evaluate (c1,s)
Proof
  Cases_on ‘evaluate (c1,s)’ \\ rw [fix_clock_def]
  \\ imp_res_tac evaluate_clock \\ fs [state_component_equality]
QED

(* We store the theorems without fix_clock *)

Theorem evaluate_ind = REWRITE_RULE [fix_clock_evaluate] evaluate_ind;
Theorem evaluate_def = REWRITE_RULE [fix_clock_evaluate] evaluate_def;

val _ = export_theory();
