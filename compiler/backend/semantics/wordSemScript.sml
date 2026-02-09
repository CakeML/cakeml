(*
  The formal semantics of wordLang
*)
Theory wordSem
Libs
  preamble
Ancestors
  mllist wordLang alignment[qualified] finite_map[qualified]
  misc[qualified] asm[qualified] fpSem[qualified]
  ffi[qualified] (* for call_FFI *)
  lprefix_lub[qualified] (* for build_lprefix_lub *)
  machine_ieee[qualified] (* for FP *)

Datatype:
  buffer =
    <| position   : 'a word
     ; buffer     : 'b word list
     ; space_left : num |>
End

Definition buffer_flush_def:
  buffer_flush cb (w1:'a word) w2 =
    if cb.position = w1 ∧ cb.position + (n2w(dimindex(:'b) DIV 8)) * n2w(LENGTH cb.buffer) = w2 then
      SOME ((cb.buffer:'b word list),
            cb with <| position := w2 ; buffer := [] |>)
    else NONE
End

Definition buffer_write_def:
  buffer_write cb (w:'a word) (b:'b word) =
    if cb.position + (n2w(dimindex(:'b) DIV 8)) * n2w(LENGTH cb.buffer) = w ∧ 0 < cb.space_left then
      SOME (cb with <| buffer := cb.buffer++[b] ; space_left := cb.space_left-1|>)
    else NONE
End

Definition is_fwd_ptr_def:
  (is_fwd_ptr (Word w) = ((w && 3w) = 0w)) /\
  (is_fwd_ptr _ = F)
End

Definition theWord_def:
  theWord (Word w) = w
End

Definition isWord_def:
  (isWord (Word w) = T) /\ (isWord _ = F)
End

Theorem isWord_exists:
   isWord x ⇔ ∃w. x = Word w
Proof
  Cases_on`x` \\ rw[isWord_def]
QED

Definition word_cmp_def:
  (word_cmp Equal    (Word w1) (Word w2) = SOME (w1 = w2)) /\
  (word_cmp Less     (Word w1) (Word w2) = SOME (w1 < w2)) /\
  (word_cmp Lower    (Word w1) (Word w2) = SOME (w1 <+ w2)) /\
  (word_cmp Test     (Word w1) (Word w2) = SOME ((w1 && w2) = 0w)) /\
  (word_cmp Test     (Loc _ n) (Word w2) = if n ≠ 0 then NONE else if w2 = 1w then SOME T else NONE) /\
  (word_cmp NotEqual (Word w1) (Word w2) = SOME (w1 <> w2)) /\
  (word_cmp NotLess  (Word w1) (Word w2) = SOME (~(w1 < w2))) /\
  (word_cmp NotLower (Word w1) (Word w2) = SOME (~(w1 <+ w2))) /\
  (word_cmp NotTest  (Word w1) (Word w2) = SOME ((w1 && w2) <> 0w)) /\
  (word_cmp NotTest  (Loc _ n) (Word w2) = if n ≠ 0 then NONE else if w2 = 1w then SOME F else NONE) /\
  (word_cmp _ _ _ = NONE)
End

Definition mem_load_32_def:
  mem_load_32 m dm be (w:'a word) =
  if aligned 2 w
  then case m (byte_align w) of
       | Loc _ _ => NONE
       | Word v =>
           if byte_align w IN dm
           then
             let b0 = get_byte w v be in
             let b1 = get_byte (w + 1w) v be in
             let b2 = get_byte (w + 2w) v be in
             let b3 = get_byte (w + 3w) v be in
               let v' =
                   (if be
                    then
                      (w2w b0) ≪ 24 ‖ (w2w b1) ≪ 16 ‖ (w2w b2) ≪ 8 ‖ (w2w b3)
                    else
                      (w2w b0) ‖ (w2w b1) ≪ 8 ‖ (w2w b2) ≪ 16 ‖ (w2w b3) ≪ 24)
             in SOME (v': word32)
           else NONE
  else NONE
End

Definition mem_store_32_def:
  mem_store_32 m dm be (w:'a word) (hw: word32) =
  if aligned 2 w
  then case m (byte_align w) of
       | Word v =>
           if byte_align w IN dm
           then
             if be
             then
               let v0 = set_byte w (w2w (hw ⋙  24)) v be in
               let v1 = set_byte (w + 1w) (w2w (hw ⋙  16)) v0 be in
               let v2 = set_byte (w + 2w) (w2w (hw ⋙  8)) v1 be in
               let v3 = set_byte (w + 3w) (w2w hw) v2 be in
                 SOME ((byte_align w =+ Word v3) m)
             else
               let v0 = set_byte w (w2w hw) v be in
               let v1 = set_byte (w + 1w) (w2w (hw ⋙  8)) v0 be in
               let v2 = set_byte (w + 2w) (w2w (hw ⋙  16)) v1 be in
               let v3 = set_byte (w + 3w) (w2w (hw ⋙  24)) v2 be in
                 SOME ((byte_align w =+ Word v3) m)
           else NONE
       | _ => NONE
  else NONE
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
  stack_frame = StackFrame (num option)
                           ((num # ('a word_loc)) list) (* non-GCed cutset *)
                           ((num # ('a word_loc)) list) (* GCed cutset *)
                           ((num # num # num)option)
End

Type gc_fun_type =
  ``: ('a word_loc list) # (('a word) -> ('a word_loc)) # ('a word) set #
      (store_name |-> 'a word_loc) ->
      (('a word_loc list) # (('a word) -> ('a word_loc)) #
      (store_name |-> 'a word_loc)) option``

Definition gc_bij_ok_def:
  gc_bij_ok (seq':num->num->num) = !n. BIJ (seq' n) UNIV UNIV
End

Datatype:
  state =
    <| locals  : ('a word_loc) num_map
     ; locals_size : num option (* size of locals when pushed to stack, NONE if unbounded *)
     ; fp_regs : num |-> word64 (* FP regs are treated "globally" *)
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a stack_frame) list
     ; stack_limit : num (* max stack size *)
     ; stack_max : num option (* largest stack seen so far, NONE if unbounded *)
     ; stack_size : num num_map (* stack frame size of function, unbounded if unmapped *)
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; sh_mdomain : ('a word) set
     ; permute : num -> num -> num (* sequence of bijective mappings *)
     ; compile : 'c -> (num # num # 'a wordLang$prog) list -> (word8 list # 'a word list # 'c) option
     ; compile_oracle : num -> 'c # (num # num # 'a wordLang$prog) list
     ; code_buffer : ('a,8) buffer
     ; data_buffer : ('a,'a) buffer
     ; gc_fun  : 'a gc_fun_type
     ; handler : num (*position of current handle frame on stack*)
     ; clock   : num
     ; termdep : num (* count of how many MustTerminates we can still enter *)
     ; code    : (num # ('a wordLang$prog)) num_map
     ; be      : bool (*is big-endian*)
     ; ffi     : 'ffi ffi_state |>
End

Definition stack_size_frame_def:
  stack_size_frame (StackFrame n _ _ NONE) = n /\
  stack_size_frame (StackFrame n _ _ (SOME _)) = OPTION_MAP ($+ 3) n
End

Definition stack_size_def:
  stack_size = FOLDR (OPTION_MAP2 $+ ∘ stack_size_frame) (SOME 1)
End

val state_component_equality = theorem"state_component_equality";

Datatype:
  result = Result ('w word_loc) (('w word_loc) list)
         | Exception ('w word_loc) ('w word_loc)
         | TimeOut
         | NotEnoughSpace
         | FinalFFI final_event
         | Error
End

Definition isResult_def:
  (isResult (Result a b) = T) /\ (isResult _ = F)
End

Definition isException_def:
  (isException (Exception a b) = T) /\ (isException _ = F)
End

val s = ``(s:('a,'c,'ffi) wordSem$state)``

Definition dec_clock_def:
  dec_clock ^s = s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res,new_s) =
    (res,new_s with
      <| clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock ;
         termdep := old_s.termdep |>)
End

Definition is_word_def[simp]:
  (is_word (Word w) = T) /\
  (is_word _ = F)
End

Definition get_word_def[simp]:
  get_word (Word w) = w
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

Definition the_words_def:
  (the_words [] = SOME []) /\
  (the_words (w::ws) =
     case (w,the_words ws) of
     | SOME (Word x), SOME xs => SOME (x::xs)
     | _ => NONE)
End

Definition get_var_def:
  get_var v ^s = sptree$lookup v s.locals
End

Definition get_vars_def:
  (get_vars [] ^s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))
End

Definition set_var_def:
  set_var v x ^s =
    (s with locals := (insert v x s.locals))
End

Definition unset_var_def:
  unset_var v ^s = (s with locals := delete v s.locals)
End

Definition set_vars_def:
  set_vars vs xs ^s =
    (s with locals := (alist_insert vs xs s.locals))
End

Definition get_store_def:
  get_store v ^s = (FLOOKUP s.store v)
End

Definition set_store_def:
  set_store v x ^s = (s with store := s.store |+ (v,x))
End

Definition word_exp_def:
  (word_exp ^s (Const w) = SOME (Word w)) /\
  (word_exp s (Var v) = get_var v s) /\
  (word_exp s (Lookup name) = get_store name s) /\
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
  WF_REL_TAC `measure (exp_size ARB o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ DECIDE_TAC
End

(* Flushes the locals and (optionally) the store *)
Definition flush_state_def:
   flush_state T ^s = s with <| locals := LN
                              ; stack := []
                              ; store := FEMPTY
                              ; locals_size := SOME 0 |>
/\ flush_state F ^s = s with <| locals := LN
                              ; locals_size := SOME 0 |>
End

Definition sh_mem_store_def:
  sh_mem_store (a:'a word) (w:'a word) ^s =
    if a IN s.sh_mdomain then
      case call_FFI s.ffi (SharedMem MappedWrite) [0w:word8]
                    (word_to_bytes w F ++ word_to_bytes a F) of
      | FFI_final outcome => (SOME (FinalFFI outcome), flush_state T s)
      | FFI_return new_ffi new_bytes => (NONE, (s with ffi := new_ffi))
    else (SOME Error, s)
End

Definition sh_mem_load_def:
  sh_mem_load (a:'a word) ^s =
    if a IN s.sh_mdomain then
      SOME $ call_FFI s.ffi (SharedMem MappedRead) [0w:word8]
                    (word_to_bytes a F)
    else NONE
End

Definition sh_mem_store_byte_def:
  sh_mem_store_byte (a:'a word) (w:'a word) ^s =
    if byte_align a IN s.sh_mdomain then
      case call_FFI s.ffi (SharedMem MappedWrite) [1w:word8]
                    ([get_byte 0w w F] ++ word_to_bytes a F) of
        FFI_final outcome => (SOME (FinalFFI outcome), flush_state T s)
      | FFI_return new_ffi new_bytes => (NONE, (s with ffi := new_ffi))
    else (SOME Error, s)
End

Definition sh_mem_store16_def:
  sh_mem_store16 (a:'a word) (w:'a word) ^s =
    if byte_align a IN s.sh_mdomain then
      case call_FFI s.ffi (SharedMem MappedWrite) [2w:word8]
                    (TAKE 2 (word_to_bytes w F) ++ word_to_bytes a F) of
        FFI_final outcome => (SOME (FinalFFI outcome), flush_state T s)
      | FFI_return new_ffi new_bytes => (NONE, (s with ffi := new_ffi))
    else (SOME Error, s)
End

Definition sh_mem_store32_def:
  sh_mem_store32 (a:'a word) (w:'a word) ^s =
    if byte_align a IN s.sh_mdomain then
      case call_FFI s.ffi (SharedMem MappedWrite) [4w:word8]
                    (TAKE 4 (word_to_bytes w F) ++ word_to_bytes a F) of
        FFI_final outcome => (SOME (FinalFFI outcome), flush_state T s)
      | FFI_return new_ffi new_bytes => (NONE, (s with ffi := new_ffi))
    else (SOME Error, s)
End

Definition sh_mem_load_byte_def:
  sh_mem_load_byte (a:'a word) ^s =
    if byte_align a IN s.sh_mdomain then
      SOME $ call_FFI s.ffi (SharedMem MappedRead) [1w:word8]
                    (word_to_bytes a F)
    else NONE
End

Definition sh_mem_load16_def:
  sh_mem_load16 (a:'a word) ^s =
    if byte_align a IN s.sh_mdomain then
      SOME $ call_FFI s.ffi (SharedMem MappedRead) [2w:word8]
                    (word_to_bytes a F)
    else NONE
End

Definition sh_mem_load32_def:
  sh_mem_load32 (a:'a word) ^s =
    if byte_align a IN s.sh_mdomain then
      SOME $ call_FFI s.ffi (SharedMem MappedRead) [4w:word8]
                    (word_to_bytes a F)
    else NONE
End

(* set variable given the output from ShareLoad(Byte) *)
Definition sh_mem_set_var_def:
  (sh_mem_set_var (SOME (FFI_final outcome)) _ ^s = (SOME (FinalFFI outcome), flush_state T s)) /\
  (sh_mem_set_var (SOME (FFI_return new_ffi new_bytes)) v s = (NONE, set_var v (Word (word_of_bytes F 0w new_bytes)) (s with ffi := new_ffi))) /\
  (sh_mem_set_var _ _ s = (SOME Error, s))
End

Definition share_inst_def:
  (share_inst Load v ad s = sh_mem_set_var (sh_mem_load ad s) v s) /\
  (share_inst Load8 v ad s = sh_mem_set_var (sh_mem_load_byte ad s) v s) /\
  (share_inst Load16 v ad s = sh_mem_set_var (sh_mem_load16 ad s) v s) /\
  (share_inst Load32 v ad s = sh_mem_set_var (sh_mem_load32 ad s) v s) /\
  (share_inst Store v ad s = case get_var v s of
    | SOME (Word v) => sh_mem_store ad v s
    | _ => (SOME Error,s)) /\
  (share_inst Store8 v ad s = case get_var v s of
    | SOME (Word v) => sh_mem_store_byte ad v s
    | _ => (SOME Error,s)) /\
  (share_inst Store16 v ad s = case get_var v s of
    | SOME (Word v) => sh_mem_store16 ad v s
    | _ => (SOME Error,s)) /\
  (share_inst Store32 v ad s = case get_var v s of
    | SOME (Word v) => sh_mem_store32 ad v s
    | _ => (SOME Error,s))
End

Definition call_env_def:
  call_env args size ^s =
    s with <| locals := fromList2 args; locals_size := size;
              stack_max := OPTION_MAP2 MAX s.stack_max (OPTION_MAP2 $+ (stack_size s.stack) size)
            |>
End

Definition list_rearrange_def:
  list_rearrange mover xs =
    (* if the mover function is actually a permutation,
     i.e. it bijects (or injects) the keys 0...n-1 to 0...n-1
     use it *)
    if (BIJ mover (count (LENGTH xs)) (count (LENGTH xs))) then
      GENLIST (\i. EL (mover i) xs) (LENGTH xs)
    else (* if it isn't well-formed, just pretend it is I *)
      xs
End

(* Compare on keys, if keys match (never), then compare on
   the word_loc vals. Treat Words as < Locs *)
Definition key_val_compare_def:
  key_val_compare x y =
    let (a:num,b) = x in
    let (a':num,b') = y in
      (a > a') \/
      (a = a' /\
        case b of
          Word x => (case b' of Word y => x <= y | _ => T)
        | Loc a b => case b' of Loc a' b' => (a>a') \/ (a=a' /\ b>=b') | _ => F)
End

(*
EVAL ``key_val_compare (1,Loc 3 4) (1,Loc 1 2)``
*)

Definition env_to_list_def:
  env_to_list env (bij_seq:num->num->num) =
    let mover = bij_seq 0 in
    let permute = (\n. bij_seq (n + 1)) in
    let l = toAList env in
    let l = mllist$sort key_val_compare l in
    let l = list_rearrange mover l in
      (l,permute)
End

Definition push_env_def:
  (push_env envs NONE ^s =
    let l0 = toAList (FST envs);
        (l,permute) = env_to_list (SND envs) s.permute;
        stack = StackFrame s.locals_size l0 l NONE :: s.stack
    in
      s with <| stack := stack
              ; stack_max := OPTION_MAP2 MAX s.stack_max (stack_size stack)
              ; permute := permute|>) ∧
  (push_env envs (SOME (w:num,h:'a wordLang$prog,l1,l2)) s =
    let l0 = toAList (FST envs);
        (l,permute) = env_to_list (SND envs) s.permute;
        handler = SOME (s.handler,l1,l2);
        stack = StackFrame s.locals_size l0 l handler :: s.stack
    in
      s with <| stack := stack
              ; stack_max := OPTION_MAP2 MAX s.stack_max (stack_size stack)
              ; permute := permute
              ; handler := LENGTH s.stack|>)
End

Definition pop_env_def:
  pop_env ^s =
    case s.stack of
    | (StackFrame m e0 e NONE::xs) =>
         SOME (s with <| locals := union (fromAList e) (fromAList e0); stack := xs ; locals_size := m
                       |>)
    | (StackFrame m e0 e (SOME (n,_,_))::xs) =>
         SOME (s with <| locals := union (fromAList e) (fromAList e0); stack := xs ; locals_size := m ; handler := n |>)
    | _ => NONE
End

Theorem push_env_clock[local]:
  (wordSem$push_env env b ^s).clock = s.clock
Proof
  Cases_on `b` \\ TRY(PairCases_on`x`) \\ full_simp_tac(srw_ss())[push_env_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
QED

Theorem pop_env_clock[local]:
  (wordSem$pop_env ^s = SOME s1) ==> (s1.clock = s.clock)
Proof
  full_simp_tac(srw_ss())[pop_env_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
QED

Definition jump_exc_def:
  jump_exc ^s =
    if s.handler < LENGTH s.stack then
      case LASTN (s.handler+1) s.stack of
      | StackFrame m e0 e (SOME (n,l1,l2)) :: xs =>
          SOME (s with <| handler := n ;
                          locals := union (fromAList e) (fromAList e0);
                          stack := xs;
                          locals_size := m |>,l1,l2)
      | _ => NONE
    else NONE
End

Definition cut_names_def:
  cut_names name_set env =
      if domain name_set SUBSET domain env
      then SOME (inter env name_set)
      else NONE
End

Definition cut_envs_def:
  cut_envs (name_sets:cutsets) env =
    case cut_names (FST name_sets) env, cut_names (SND name_sets) env of
    | (SOME e1, SOME e2) => SOME (e1, e2)
    | _ => NONE
End

Definition cut_env_def:
  cut_env (name_sets:cutsets) env =
    case cut_envs name_sets env of
    | SOME (e1, e2) => SOME (union e2 e1)
    | _ => NONE
End
(* -- *)

Definition cut_state_def:
  cut_state names ^s =
    case cut_env names s.locals of
    | NONE => NONE
    | SOME env => SOME (s with locals := env)
End

Definition cut_state_opt_def:
  cut_state_opt names ^s =
    case names of
    | NONE => SOME s
    | SOME names => cut_state names s
End

Definition find_code_def:
  (find_code (SOME p) args code ssize =
     case sptree$lookup p code of
     | NONE => NONE
     | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp,sptree$lookup p ssize)
                                                  else NONE) /\
  (find_code NONE args code ssize =
     if args = [] then NONE else
       case LAST args of
       | Loc loc 0 =>
           (case lookup loc code of
            | NONE => NONE
            | SOME (arity,exp) => if LENGTH args = arity + 1
                                  then SOME (FRONT args,exp,sptree$lookup loc ssize)
                                  else NONE)
       | other => NONE)
End

Definition enc_stack_def:
  (enc_stack [] = []) /\
  (enc_stack ((StackFrame n _ l handler :: st)) = MAP SND l ++ enc_stack st)
End

Definition dec_stack_def:
  (dec_stack [] [] = SOME []) /\
  (dec_stack xs ((StackFrame n l0 l handler :: st)) =
     if LENGTH xs < LENGTH l then NONE else
       case dec_stack (DROP (LENGTH l) xs) st of
       | NONE => NONE
       | SOME s => SOME (StackFrame n l0
           (ZIP (MAP FST l,TAKE (LENGTH l) xs)) handler :: s)) /\
  (dec_stack _ _ = NONE)
End

Definition gc_def:
  (* gc runs the garbage collector algorithm *)
  gc ^s =
    let wl_list = enc_stack s.stack in
      case s.gc_fun (wl_list, s.memory, s.mdomain, s.store) of
      | NONE => NONE
      | SOME (wl,m,st) =>
       (case dec_stack wl s.stack of
        | NONE => NONE
        | SOME stack =>
            SOME (s with <| stack := stack
                          ; store := st
                          ; memory := m |>))
End

Definition has_space_def:
  has_space wl ^s =
    case (wl, get_store NextFree s, get_store TriggerGC s) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE
End

(* to_ask: should we not update stack size here?  *)
Definition alloc_def:
  alloc (w:'a word) names ^s =
    (* prune local names *)
    case cut_envs names s.locals of
    | NONE => (SOME (Error:'a result),flush_state T s)
    | SOME envs =>
     (* perform garbage collection *)
     (case gc (push_env envs (NONE:(num # 'a wordLang$prog # num # num) option) (set_store AllocSize (Word w) s)) of
      | NONE => (SOME Error,flush_state T s)
      | SOME s =>
       (* restore local variables *)
       (case pop_env s of
        (* Here flush_state is ok because the stack must
           be empty for pop_env to return NONE *)
        | NONE => (SOME Error, flush_state T s)
        | SOME s =>
         (* read how much space should be allocated *)
         (case get_store AllocSize s of
          | NONE => (SOME Error, s)
          | SOME w =>
           (* check how much space there is *)
           (case has_space w s of
            | NONE => (SOME Error, s)
            | SOME T => (* success there is that much space *)
                        (NONE,s)
            | SOME F => (* fail, GC didn't free up enough space *)
                        (SOME NotEnoughSpace,flush_state T s)))))
End

Definition assign_def:
  assign reg exp ^s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg w s)
End

Definition get_fp_var_def:
  get_fp_var v (s:('a,'c,'ffi) wordSem$state) = FLOOKUP s.fp_regs v
End

Definition set_fp_var_def:
  set_fp_var v x (s:('a,'c,'ffi) wordSem$state) =
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
    | Mem Load16 _ _ => NONE
    | Mem Load32 r (Addr a w) =>
       (case word_exp s (Op Add [Var a; Const w]) of
        | SOME (Word w) =>
           (case mem_load_32 s.memory s.mdomain s.be w of
            | NONE => NONE
            | SOME w => SOME (set_var r (Word (w2w w)) s))
        | _ => NONE)
    | Mem Store r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), get_var r s) of
        | (SOME (Word a), SOME w) =>
            (case mem_store a w s of
             | SOME s1 => SOME s1
             | NONE => NONE)
        | _ => NONE)
    | Mem Store8 r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), get_var r s) of
        | (SOME (Word a), SOME (Word w)) =>
            (case mem_store_byte_aux s.memory s.mdomain s.be a (w2w w) of
             | SOME new_m => SOME (s with memory := new_m)
             | NONE => NONE)
        | _ => NONE)
    | Mem Store16 _ _ => NONE
    | Mem Store32 r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), get_var r s) of
        | (SOME (Word a), SOME (Word w)) =>
            (case mem_store_32 s.memory s.mdomain s.be a (w2w w) of
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
        case get_var r1 s of
          SOME (Word w1) => SOME (set_fp_var d (w2w w1) s)
        | _ => NONE
      else
        case (get_var r1 s,get_var r2 s) of
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
  (get_var_imm ((Reg n):'a reg_imm) ^s = get_var n s) ∧
  (get_var_imm (Imm w) s = SOME(Word w))
End

Definition add_ret_loc_def:
  (add_ret_loc NONE xs = xs) /\
  (add_ret_loc (SOME (n,names,ret_handler,l1,l2)) xs = (Loc l1 l2)::xs)
End

(*Avoid case split*)
Definition bad_dest_args_def:
  bad_dest_args dest args ⇔ dest = NONE ∧ args = []
End

Theorem termdep_rw[local]:
  ((call_env p_1 ss ^s).termdep = s.termdep) /\
    ((dec_clock s).termdep = s.termdep) /\
    ((set_var n v s).termdep = s.termdep)
Proof
  EVAL_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem fix_clock_IMP_LESS_EQ[local]:
  !x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock /\ s1.termdep = s.termdep
Proof
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac
QED

Definition MustTerminate_limit_def[nocompute]:
  MustTerminate_limit (:'a) =
    (* This is just a number that's large enough for our purposes.
       It stated in a way that makes proofs easy. *)
    2 * dimword (:'a) +
    dimword (:'a) * dimword (:'a) +
    dimword (:'a) ** dimword (:'a) +
    dimword (:'a) ** dimword (:'a) ** dimword (:'a)
End

Definition const_addresses_def:
  const_addresses a [] d = T ∧
  const_addresses a (x::xs) d =
    (a IN d ∧ const_addresses (a + bytes_in_word) xs d)
End

Definition const_writes_def:
  const_writes a off [] m = m ∧
  const_writes (a:'a word) off ((b,x:'a word)::xs) m =
    const_writes (a + bytes_in_word) off xs
      ((a =+ Word (if b then x + off else x)) m)
End

Definition evaluate_def:
  (evaluate (Skip:'a wordLang$prog,^s) = (NONE,s)) /\
  (evaluate (Alloc n names,s) =
     case get_var n s of
     | SOME (Word w) => alloc w names s
     | _ => (SOME Error,s)) /\
  (evaluate (StoreConsts t1 t2 addr offset words,s) =
     case (get_var addr s, get_var offset s) of
     | (SOME (Word a), SOME (Word off)) =>
        (if ~ const_addresses a words s.mdomain then
           (SOME Error,s)
         else
           let s = s with memory := const_writes a off words s.memory in
           let s = set_var offset (Word off) (unset_var t1 (unset_var t2 s)) in
             (NONE, set_var addr (Word (a + bytes_in_word * n2w (LENGTH words))) s))
     | _ => (SOME Error,s)) /\
  (evaluate (Move pri moves,s) =
     if ALL_DISTINCT (MAP FST moves) then
       case get_vars (MAP SND moves) s of
       | NONE => (SOME Error,s)
       | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
     else (SOME Error,s)) /\
  (evaluate (Inst i,s) =
     case inst i s of
     | SOME s1 => (NONE, s1)
     | NONE => (SOME Error, s)) /\
  (evaluate (Assign v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v w s)) /\
  (evaluate (Get v name,s) =
     case get_store name s of
     | NONE => (SOME Error, s)
     | SOME x => (NONE, set_var v x s)) /\
  (evaluate (Set v exp,s) =
     if v = Handler ∨ v = BitmapBase then (SOME Error,s)
     else
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_store v w s)) /\
  (evaluate (OpCurrHeap b dst src,s) =
     case word_exp s (Op b [Var src; Lookup CurrHeap]) of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var dst w s)) /\
  (evaluate (Store exp v,s) =
     case (word_exp s exp, get_var v s) of
     | (SOME (Word a), SOME w) =>
         (case mem_store a w s of
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,flush_state T s)
                    else (NONE,dec_clock s)) /\
  (evaluate (MustTerminate p,s) =
     if s.termdep = 0 then (SOME Error, s) else
       let (res,s1) = evaluate (p,s with
                                  <| clock := MustTerminate_limit (:'a);
                                     termdep := s.termdep-1 |>) in
         if res = SOME TimeOut then (SOME Error, s)
         else (res,s1 with <| clock := s.clock; termdep := s.termdep |>)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (Return n ms,s) =
     case (get_var n s, get_vars ms s) of
     | (SOME (Loc l1 l2),SOME ys) => (SOME (Result (Loc l1 l2) ys),flush_state F s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME (s,l1,l2) => (SOME (Exception (Loc l1 l2) w)),s)) /\
  (evaluate (If cmp r1 ri c1 c2,s) =
    (case (get_var r1 s,get_var_imm ri s) of
    | SOME x,SOME y =>
     (case word_cmp cmp x y of
      | SOME T => evaluate (c1,s)
      | SOME F => evaluate (c2,s)
      | NONE => (SOME Error,s))
    | _ => (SOME Error,s))) /\
  (evaluate (LocValue r l1,s) =
     if l1 ∈ domain s.code then
       (NONE,set_var r (Loc l1 0) s)
     else (SOME Error,s)) /\
  (evaluate (Install ptr len dptr dlen names,s) =
    case cut_env names s.locals of
    | NONE => (SOME Error,s)
    | SOME env =>
    case (get_var ptr s, get_var len s, get_var dptr s, get_var dlen s) of
    | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
       let (cfg,progs) = s.compile_oracle 0 in
       (case (buffer_flush s.code_buffer w1 w2
             ,buffer_flush s.data_buffer w3 w4) of
         SOME (bytes, cb), SOME (data, db) =>
        let new_oracle = shift_seq 1 s.compile_oracle in
        (case s.compile cfg progs, progs of
          | SOME (bytes',data',cfg'), (k,prog)::_ =>
            if bytes = bytes' ∧ data = data' ∧ FST(new_oracle 0) = cfg' then
            let s' =
                s with <|
                  code_buffer := cb
                ; data_buffer := db
                ; code := union s.code (fromAList progs)
                (* This order is convenient because it means all of s.code's entries are preserved *)
                ; locals := insert ptr (Loc k 0) env
                ; compile_oracle := new_oracle
                ; stack_max := NONE (* Install is not safe for space *)
                ; stack_size := LN
                (* For convenience --- stack size of installed code,
                   or any other code for that matter, doesn't matter
                   after Install. *)
                |> in
              (NONE,s')
            else (SOME Error,s)
          | _ => (SOME Error,s))
        | _ => (SOME Error,s))
      | _ => (SOME Error,s)) /\
  (evaluate (CodeBufferWrite r1 r2,s) =
    (case (get_var r1 s,get_var r2 s) of
        | (SOME (Word w1), SOME (Word w2)) =>
          (case buffer_write s.code_buffer w1 (w2w w2) of
          | SOME new_cb =>
            (NONE,s with code_buffer:=new_cb)
          | _ => (SOME Error,s))
        | _ => (SOME Error,s))) /\
  (evaluate (DataBufferWrite r1 r2,s) =
    (case (get_var r1 s,get_var r2 s) of
        | (SOME (Word w1), SOME (Word w2)) =>
          (case buffer_write s.data_buffer w1 w2 of
          | SOME new_db =>
            (NONE,s with data_buffer:=new_db)
          | _ => (SOME Error,s))
        | _ => (SOME Error,s))) /\
  (evaluate (FFI ffi_index ptr1 len1 ptr2 len2 names,s) =
    case (get_var len1 s, get_var ptr1 s, get_var len2 s, get_var ptr2 s) of
    | SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4) =>
      (case cut_env names s.locals of
      | NONE => (SOME Error,s)
      | SOME env =>
        (case (read_bytearray w2 (w2n w) (mem_load_byte_aux s.memory s.mdomain s.be),
               read_bytearray w4 (w2n w3) (mem_load_byte_aux s.memory s.mdomain s.be))
               of
          | SOME bytes,SOME bytes2 =>
             (case call_FFI s.ffi (ExtCall ffi_index) bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),flush_state T s)
              | FFI_return new_ffi new_bytes =>
                let new_m = write_bytearray w4 new_bytes s.memory s.mdomain s.be in
                  (NONE, s with <| memory := new_m ;
                                   locals := env ;
                                   ffi := new_ffi |>))
          | _ => (SOME Error,s)))
    | res => (SOME Error,s)) /\
  (evaluate (ShareInst op v exp, s) =
    (case word_exp s exp of
    | SOME (Word ad) => share_inst op v ad s
    | _ => (SOME Error,s))) /\
  (evaluate (Call ret dest args handler,s) =
   case get_vars args s of
   | NONE => (SOME Error,s)
   | SOME xs =>
       if bad_dest_args dest args then (SOME Error,s)
       else
         case find_code dest (add_ret_loc ret xs) s.code s.stack_size of
         | NONE => (SOME Error,s)
         | SOME (args1,prog,ss) =>
             case ret of
             | NONE (* tail call *) =>
                 if handler = NONE then
                   if s.clock = 0 then (SOME TimeOut,flush_state T s)
                   else (case evaluate (prog, call_env args1 ss (dec_clock s)) of
                         | (NONE,s) => (SOME Error,s)
                         | (SOME res,s) => (SOME res,s))
                 else (SOME Error,s)
             | SOME (n,names,ret_handler,l1,l2) (* returning call, returns into var n *) =>
                 if domain (FST names) = {} ∨ ¬ALL_DISTINCT n then (SOME Error,s)
                 else
                   (case cut_envs names s.locals of
                    | NONE => (SOME Error,s)
                    | SOME envs =>
                        if s.clock = 0 then
                          (SOME TimeOut,
                           flush_state T
                                       (s with <|stack := [];
                                                 stack_max := (call_env args1 ss
                                                               (push_env envs handler s)
                                                              ).stack_max|>))
                        else
                          (case fix_clock (call_env args1 ss (push_env envs handler (dec_clock s)))
                                          (evaluate (prog, call_env args1 ss
                                                                    (push_env envs handler (dec_clock s)))) of
                           | (SOME (Result x ys),s2) =>
                               if x ≠ Loc l1 l2 ∨ LENGTH ys ≠ LENGTH n then (SOME Error,s2)
                               else
                                 (case pop_env s2 of
                                  | NONE => (SOME Error,s2)
                                  | SOME s1 =>
                                      (if domain s1.locals = domain (FST envs) UNION domain (SND envs)
                                       then evaluate(ret_handler,set_vars n ys s1)
                                       else (SOME Error,s1)))
                           | (SOME (Exception x y),s2) =>
                               (case handler of (* if handler is present, then handle exc *)
                                | NONE => (SOME (Exception x y),s2)
                                | SOME (n,h,l1,l2) =>
                                    if x ≠ Loc l1 l2 then (SOME Error,s2)
                                    else
                                      (if domain s2.locals = domain (FST envs) UNION domain (SND envs)
                                       then evaluate (h, set_var n y s2)
                                       else (SOME Error,s2)))
                           | (NONE,s) => (SOME Error,s)
                           | res => res)))
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure I LEX measure (prog_size (K 0)))
               (\(xs,^s). (s.termdep,s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
  \\ full_simp_tac(srw_ss())[termdep_rw] \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac (GSYM fix_clock_IMP_LESS_EQ)
  \\ TRY (Cases_on `handler`) \\ TRY (PairCases_on `x`)
  \\ full_simp_tac(srw_ss())[set_var_def,set_vars_def,push_env_def,call_env_def,dec_clock_def,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[pop_env_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ decide_tac
End

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

Theorem sh_mem_set_var_clock:
  !v s1 v2 s2 res.
    (sh_mem_set_var res v s1 = (v2,s2)) ==>
    s2.clock <= s1.clock /\ s2.termdep = s1.termdep
Proof
  Cases_on `res` >>
  simp[sh_mem_set_var_def] >>
  Cases_on `x` >>
  simp[sh_mem_set_var_def,set_var_def,flush_state_def]
QED

Theorem share_inst_clock:
  !op v ad s1 v1 s2.
    (share_inst op v ad s1 = (v2, s2)) ==>
    s2.clock <= s1.clock /\ s2.termdep = s1.termdep
Proof
  Cases_on `op` >>
  simp[share_inst_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(),sh_mem_store_def,sh_mem_store_byte_def,flush_state_def,
      sh_mem_store32_def,sh_mem_store16_def
     ] >>
  drule sh_mem_set_var_clock >>
  simp[]
QED

Theorem inst_clock[local]:
  inst i s = SOME s2 ==> s2.clock <= s.clock /\ s2.termdep = s.termdep
Proof
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,get_vars_def,LET_THM]
  \\ every_case_tac
  \\ SRW_TAC [] [set_var_def] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[mem_store_def] \\ SRW_TAC [] []
  \\ EVAL_TAC \\ fs[]
QED

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
  \\ full_simp_tac(srw_ss())[set_vars_def,set_var_def,set_store_def,unset_var_def]
  \\ imp_res_tac inst_clock \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac share_inst_clock
  \\ fs[mem_store_def,call_env_def,dec_clock_def,flush_state_def]
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

Theorem fix_clock_evaluate[local]:
  fix_clock s (evaluate (c1,s)) = evaluate (c1,s)
Proof
  Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[fix_clock_def]
  \\ imp_res_tac evaluate_clock \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]
  \\ full_simp_tac(srw_ss())[state_component_equality]
QED

(* We store the theorems without fix_clock *)

Theorem evaluate_ind[allow_rebind] =
        REWRITE_RULE [fix_clock_evaluate] evaluate_ind;
Theorem evaluate_def[allow_rebind] =
        REWRITE_RULE [fix_clock_evaluate] evaluate_def;

(* observational semantics *)

Definition semantics_def:
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
              (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
End

Definition word_lang_safe_for_space_def:
  word_lang_safe_for_space (s:('a,'c,'ffi) wordSem$state) start =
    let prog = Call NONE (SOME start) [0] NONE in
      (∀k res t. wordSem$evaluate (prog, s with clock := k) = (res,t) ==>
        ∃max. t.stack_max = SOME max /\ max <= t.stack_limit)
End

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];
