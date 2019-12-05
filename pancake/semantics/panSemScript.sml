(*
  Semantics of panLang
*)
open preamble panLangTheory;
local open alignmentTheory wordSemTheory ffiTheory in end;

val _ = new_theory"panSem";
val _ = set_grammar_ancestry [
  "panLang", "alignment",
  "finite_map", "misc", "wordSem", "ffi"
]

val _ = Datatype `
  state =
    <| locals    : ('a word_loc) num_map   (* TOASK: why do we need Loc num num? function labels *)
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
         | Break
         | Continue
         | Error `

val s = ``(s:('a,'ffi) panSem$state)``

val dec_clock_def = Define `
  dec_clock ^s = s with clock := s.clock - 1`;

val fix_clock_def = Define `
  fix_clock old_s (res,new_s) =
    (res,new_s with
      <| clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)`

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


val word_exp_def = tDefine "word_exp"`
  (word_exp ^s (Const w) = SOME (Word w)) /\
  (word_exp s (Var v) = lookup v s.locals) /\
  (word_exp s (Loc l) = lookup l s.locals) /\  (* TOASK: have to confirm design of Call from Magnus *)
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


val word_exps_def = Define `
  (word_exps ^s [] = SOME []) /\
  (word_exps s (v::vs) =
     case word_exp s v of
     | NONE => NONE
     | SOME x => (case word_exps s vs of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val bool_bexp_def = Define `
  (bool_bexp ^s (Bconst b) = SOME b) /\
  (bool_bexp s (Bcomp cmp aexp1 aexp2) =
    case (word_exp s aexp1, word_exp s aexp2) of
     | (SOME (Word w1), SOME (Word w2)) => SOME (word_cmp cmp w1 w2)
     | _ => NONE) /\
  (bool_bexp s (Bbinop f bexp1 bexp2) =
    case (bool_bexp s bexp1, bool_bexp s bexp2) of
     | (SOME b1, SOME b2) => SOME (f b1 b2)
     | _ => NONE) /\
  (bool_bexp s (Bnot bexp) =
    case (bool_bexp s bexp) of
     | (SOME b) => SOME (~b)
     | NONE => NONE)`

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


val fix_clock_IMP_LESS_EQ = Q.prove(
  `!x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock`,
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac);


val call_env_def = Define `
  call_env args ^s =
    s with <| locals := fromList args |>`;


(* only being used in FFI *)
val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (inter env name_set)
    else NONE`


val find_code_def = Define `
  (find_code p args code =
     case sptree$lookup p code of
     | NONE => NONE
     | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp)
                                                  else NONE)`

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip:'a panLang$prog,^s) = (NONE,s)) /\
  (evaluate (Assign dstexp srcexp,s) =
     case (dstexp, word_exp s srcexp) of
     | (Var n, SOME w) => (NONE, set_var n w s)
     | (_, NONE) => (SOME Error, s)) /\
  (evaluate (Store dstexp srcexp,s) =
     case srcexp of
       | (Var n) =>
          (case (word_exp s dstexp, get_var n s) of
            | (SOME (Word adr), SOME w) =>
               (case mem_store adr w s of
                 | SOME st => (NONE, st)
                 | NONE => (SOME Error, s))
            | _ => (SOME Error, s))
       | _ => (SOME Error, s)) /\
  (evaluate (StoreByte dstexp srcexp,s) =
     case srcexp of
       | (Var n) =>
          (case (word_exp s dstexp, get_var n s) of
            | (SOME (Word adr), SOME (Word w)) =>
               (case mem_store_byte_aux s.memory s.memaddrs s.be adr (w2w w) of
                 | SOME m => (NONE, s with memory := m)
                 | NONE => (SOME Error, s))
            | _ => (SOME Error, s))
       | _ => (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If bexp c1 c2,s) =
     (case (bool_bexp s bexp) of
     | SOME b =>
       if b then evaluate (c1,s)
            else evaluate (c2,s)
     | _ => (SOME Error,s))) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\
  (evaluate (While bexp c,s) =
    case (bool_bexp s bexp) of
    | SOME b =>
      if b then
        let (res,s1) = fix_clock s (evaluate (c,s)) in
          if s1.clock = 0 then (SOME TimeOut,call_env [] s1)
          else
            case res of
             | SOME Continue => evaluate (While bexp c,dec_clock s1)
             | NONE => evaluate (While bexp c,dec_clock s1)
             | _ => (res,s1)
      else (NONE,s)
    | _ => (SOME Error,s)) /\
  (evaluate (Return aexp,s) =  (* TOASK: moving around old def right now, to update after discussing with Magnus *)
     case aexp of
       | Var n  =>
         (case get_var n s of
           | SOME v => (SOME (Return v),call_env [] s)
           | _ => (SOME Error,s))
       | _ =>  (SOME Error,s)) /\
  (evaluate (Raise aexp,s) =
    case aexp of
       | Var n  =>
         (case get_var n s of
           | SOME v => (SOME (Exception v),s)
           | _ => (SOME Error,s))
       | _ =>  (SOME Error,s)) /\
 (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s)
                    else (NONE,dec_clock s)) /\
 (evaluate (Call ret dest argexps,s) =
    case (dest, word_exps s argexps) of
     | (Var p, SOME argvals) =>
        (case find_code p argvals s.code of
          | NONE => (SOME Error,s)
          | SOME (args,prog) =>
            (case ret of
              | NoRet =>
                if s.clock = 0 then (SOME TimeOut,call_env [] s)
                else (case evaluate (prog, call_env args (dec_clock s)) of
                       | (NONE,s) => (SOME Error,s)
                       | (SOME res,s) => (SOME res,s))
              | Ret rt =>
                if s.clock = 0 then (SOME TimeOut,call_env [] s)
                else (case fix_clock (call_env args (dec_clock s))
                                     (evaluate (prog, call_env args (dec_clock s))) of
                       | (NONE,st) => (SOME Error,(st with locals := s.locals))
                       | (SOME (Return retv),st) => (NONE, set_var rt retv (st with locals := s.locals))
                       | (SOME (Exception exn),st) => (SOME (Exception exn),(st with locals := s.locals))
                       | res => res)
              | Hndl rt n p =>
                if s.clock = 0 then (SOME TimeOut,call_env [] s)
                else (case fix_clock (call_env args (dec_clock s))
                                     (evaluate (prog, call_env args (dec_clock s))) of
                       | (NONE,st) => (SOME Error,(st with locals := s.locals))
                       | (SOME (Return retv),st) => (NONE, set_var rt retv (st with locals := s.locals))
                       | (SOME (Exception exn),st) => evaluate (p, set_var n exn (st with locals := s.locals))
                       | res => res)))
    | (_, _) => (SOME Error,s))
(*
  (evaluate (Handle c1 (n, c2),s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     case res of
       | SOME (Exception exn) => evaluate (c2, set_var n exn s1) (* should we do dec clock here, clock is being fixed already *)
       | _ => (res, s1) ) /\
   /\
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
    | res => (SOME Error,s)) *)`
  (WF_REL_TAC `(inv_image (measure I LEX measure (prog_size (K 0)))
                  (\(xs,^s). (s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
   \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ full_simp_tac(srw_ss())[]
   \\ imp_res_tac (GSYM fix_clock_IMP_LESS_EQ)
   \\ full_simp_tac(srw_ss())[set_var_def,call_env_def,dec_clock_def, LET_THM]
   \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
   \\ every_case_tac \\ full_simp_tac(srw_ss())[]
   \\ decide_tac)

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
