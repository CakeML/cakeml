(*
  The formal semantics of panLang
*)
open preamble panLangTheory;
local open alignmentTheory ffiTheory in end;

val _ = new_theory"panSem";
val _ = set_grammar_ancestry [
  "panLang", "alignment",
  "finite_map", "misc", "ffi"
]

val _ = Datatype `
  word_loc = Word ('a word) | Loc num num `;

val mem_load_byte_aux_def = Define `
  mem_load_byte_aux m dm be w =
    case m (byte_align w) of
    | Loc _ _ => NONE
    | Word v =>
        if byte_align w IN dm
        then SOME (get_byte w v be) else NONE`

val mem_store_byte_aux_def = Define `
  mem_store_byte_aux m dm be w b =
    case m (byte_align w) of
    | Word v =>
        if byte_align w IN dm
        then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
        else NONE
    | _ => NONE`

val write_bytearray_def = Define `
  (write_bytearray a [] m dm be = m) /\
  (write_bytearray a (b::bs) m dm be =
     case mem_store_byte_aux (write_bytearray (a+1w) bs m dm be) dm be a b of
     | SOME m => m
     | NONE => m)`;


val _ = Datatype `
  state =
    <| locals    : ('a word_loc) num_map
     ; memory    : 'a word -> 'a word_loc
     ; memaddrs  : ('a word) set
     ; clock     : num
     ; be        : bool
     ; code      : (num # ('a panLang$prog)) num_map
     ; ffi       : 'ffi ffi_state |> `

val state_component_equality = theorem"state_component_equality";

val _ = Datatype `
  result = Return ('w word_loc)
         | Exception ('w word_loc)
         | TimeOut
         | FinalFFI final_event
         | Break  (* should we have a constructor, or reuse Error? *)
         | Continue
         | Error `

val s = ``(s:('a,'ffi) panSem$state)``

val dec_clock_def = Define `
  dec_clock ^s = s with clock := s.clock - 1`;

val fix_clock_def = Define `
  fix_clock old_s (res,new_s) =
    (res,new_s with
      <| clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)`

val is_word_def = Define `
  (is_word (Word w) = T) /\
  (is_word _ = F)`

val get_word_def = Define `
  get_word (Word w) = w`

val _ = export_rewrites["is_word_def","get_word_def"];

val mem_store_def = Define `
  mem_store (addr:'a word) (w:'a word_loc) ^s =
    if addr IN s.memaddrs then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) ^s =
    if addr IN s.memaddrs then
      SOME (s.memory addr)
    else NONE`

val the_words_def = Define `
  (the_words [] = SOME []) /\
  (the_words (w::ws) =
     case (w,the_words ws) of
     | SOME (Word x), SOME xs => SOME (x::xs)
     | _ => NONE)`

val word_exp_def = tDefine "word_exp"`
  (word_exp ^s (Const w) = SOME (Word w)) /\
  (word_exp s (Var v) = lookup v s.locals) /\
  (word_exp s (Load addr) =
     case word_exp s addr of
     | SOME (Word w) => mem_load w s
     | _ => NONE) /\
  (word_exp s (LoadByte addr) =
     case word_exp s addr of
     | SOME (Word w) =>
        (case mem_load_byte_aux s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (Word (w2w w)))
     | _ => NONE) /\
  (word_exp s (Op op wexps) =
     case the_words (MAP (word_exp s) wexps) of
     | SOME ws => (OPTION_MAP Word (word_op op ws))
     | _ => NONE) /\
  (word_exp s (Shift sh wexp n) =
     case word_exp s wexp of
     | SOME (Word w) => OPTION_MAP Word (word_sh sh w n)
     | _ => NONE)`
  (WF_REL_TAC `measure (exp_size ARB o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ DECIDE_TAC)

val get_var_def = Define `
  get_var v ^s = sptree$lookup v s.locals`;

val get_vars_def = Define `
  (get_vars [] ^s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val set_var_def = Define `
  set_var v x ^s =
    (s with locals := (insert v x s.locals))`;

val set_vars_def = Define `
  set_vars vs xs ^s =
    (s with locals := (alist_insert vs xs s.locals))`;


val find_code_def = Define `
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
       | other => NONE)`


val assign_def = Define `
  assign reg exp ^s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg w s)`;

val fix_clock_IMP_LESS_EQ = Q.prove(
  `!x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock`,
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac);

(*Avoid case split*)
val bad_dest_args_def = Define`
  bad_dest_args dest args ⇔ dest = NONE ∧ args = []`


val call_env_def = Define `
  call_env args ^s =
    s with <| locals := fromList args |>`;


(* only being used in FFI *)
val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (inter env name_set)
    else NONE`

val get_var_imm_def = Define`
  (get_var_imm ((Str n):'a var_imm) s = get_var n s) /\
  (get_var_imm (Imm w) s = SOME(Word w))`


val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip:'a panLang$prog,^s) = (NONE,s)) /\
  (evaluate (Assign v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v w s)) /\
  (evaluate (Store exp v,s) =
     case (word_exp s exp, get_var v s) of
     | (SOME (Word adr), SOME w) =>
         (case mem_store adr w s of
          | SOME st => (NONE, st)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (StoreByte exp v,s) = (* v should contain only a Word, not a Label *)
     case (word_exp s exp, get_var v s) of
       | (SOME (Word adr), SOME (Word w)) =>
           (case mem_store_byte_aux s.memory s.memaddrs s.be adr (w2w w) of
              | SOME m => (NONE, s with memory := m)
              | NONE => (SOME Error, s))
       | _ => (SOME Error, s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s)
                    else (NONE,dec_clock s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If cmp r1 r2 c1 c2,s) =
    (case (get_var r1 s,get_var r2 s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then evaluate (c1,s)
                          else evaluate (c2,s)
    | _ => (SOME Error,s))) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\


  (evaluate (While cmp r1 ri c,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y
      then let (res,s1) = fix_clock s (evaluate (c,s)) in
             if s1.clock = 0 then (SOME TimeOut,call_env [] s1) else
             case res of
	       | SOME Continue => evaluate (While cmp r1 ri c,dec_clock s1)
	       | NONE => evaluate (While cmp r1 ri c,dec_clock s1)
	       | _ => (res,s1)
      else (NONE,s)
    | _ => (SOME Error,s))) /\
  (evaluate (Return n,s) =  (* Return encodes the value in the result and clear the local varaibles   *)
     case get_var n s of    (* it does not remove the stack frame, Call removes the stack frame if the result is Return*)
     | SOME v => (SOME (Return v),call_env [] s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w => (SOME (Exception w),s)) /\
  (evaluate (FFI ffi_index ptr1 len1 ptr2 len2 names,s) =
    case (get_var len1 s, get_var ptr1 s, get_var len2 s, get_var ptr2 s) of
    | SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4) =>
      (case cut_env names s.locals of
      | NONE => (SOME Error,s)
      | SOME env =>
        (case (read_bytearray w2 (w2n w) (mem_load_byte_aux s.memory s.memaddrs s.be),
               read_bytearray w4 (w2n w3) (mem_load_byte_aux s.memory s.memaddrs s.be))
               of
          | SOME bytes,SOME bytes2 =>
             (case call_FFI s.ffi ffi_index bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),
                                      call_env [] s)
              | FFI_return new_ffi new_bytes =>
                let new_m = write_bytearray w4 new_bytes s.memory s.memaddrs s.be in
                  (NONE, s with <| memory := new_m ;
                                   locals := env ;
                                   ffi := new_ffi |>))
          | _ => (SOME Error,s)))
    | res => (SOME Error,s)) /\
  (evaluate (Call (ret: num option) (dest: (num option)) (argvars : (num list)) handler,s) =
    case get_vars argvars s of
    | NONE => (SOME Error,s)
    | SOME argvals =>
      if bad_dest_args dest argvars then (SOME Error,s)
      else
        case find_code dest argvals s.code of
        | NONE => (SOME Error,s)
        | SOME (args,prog) =>
          case ret of
          | NONE (* tail call *) =>
            if handler = NONE then
             if s.clock = 0 then (SOME TimeOut,call_env [] s)
             else (case evaluate (prog, call_env args (dec_clock s)) of
                    | (NONE,s) => (SOME Error,s)  (* the called function must return a value or it should end in an exception,
                                                     it should not end in a result without execution *)
                    | (SOME res,s) => (SOME res,s))
           else (SOME Error,s) (* tail-call requires no handler *)
          | SOME n (* returning call, returns into var n *) =>
              if s.clock = 0 then (SOME TimeOut,call_env [] s)
              else (case fix_clock (call_env args (dec_clock s))
                                   (evaluate (prog, call_env args (dec_clock s))) of
                      | (NONE,st) => (SOME Error,st)
                      | (SOME (Return retv),st) => (NONE, set_var n retv st)
                      | (SOME (Exception exn),st) =>
                          (case handler of (* if handler is present, then handle exc *)
                            | NONE => (SOME (Exception exn),st)
                            | SOME (n,h) => evaluate (h, set_var n exn st))
                      | res => res))`
  (WF_REL_TAC `(inv_image (measure I LEX measure (prog_size (K 0)))
                  (\(xs,^s). (s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
   \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ full_simp_tac(srw_ss())[]
   \\ imp_res_tac (GSYM fix_clock_IMP_LESS_EQ)
   \\ full_simp_tac(srw_ss())[set_var_def,call_env_def,dec_clock_def, LET_THM]
   \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
   \\ every_case_tac \\ full_simp_tac(srw_ss())[]
   \\ decide_tac)


(*
val jump_exc_def = Define `
  jump_exc ^s =
    if s.handler < LENGTH s.stack then
      case LASTN (s.handler+1) s.stack of
      | StackFrame m e (SOME (n,l1,l2)) :: xs =>
          SOME (s with <| handler := n ; locals := fromAList e ; stack := xs; locals_size := m |>,l1,l2)
      | _ => NONE
    else NONE`;



(evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME (s,l1,l2) => (SOME (Exception (Loc l1 l2) w)),s)) /\
*)
val evaluate_ind = theorem"evaluate_ind";


Theorem evaluate_clock:
   !prog s r s'. (evaluate (prog,s) = (r,s')) ==>
                 s'.clock <= s.clock
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ rw [] \\ every_case_tac
  \\ fs [set_vars_def,set_var_def, mem_store_def,call_env_def,dec_clock_def, LET_THM]
  \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rveq
  \\ imp_res_tac fix_clock_IMP_LESS_EQ
  \\ imp_res_tac LESS_EQ_TRANS \\ fs []
QED

val fix_clock_evaluate = Q.prove(
  `fix_clock s (evaluate (prog,s)) = evaluate (prog,s)`,
  Cases_on `evaluate (prog,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock \\ fs [GSYM NOT_LESS, state_component_equality]);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
