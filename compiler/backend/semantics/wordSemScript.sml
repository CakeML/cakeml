(*
  The formal semantics of wordLang
*)
open preamble wordLangTheory;
local open alignmentTheory asmTheory ffiTheory in end;

val _ = new_theory"wordSem";
val _ = set_grammar_ancestry [
  "wordLang", "alignment", "finite_map", "misc", "asm",
  "ffi", (* for call_FFI *)
  "lprefix_lub", (* for build_lprefix_lub *)
  "machine_ieee" (* for FP*)
]

val _ = Datatype `
  buffer =
    <| position   : 'a word
     ; buffer     : 'b word list
     ; space_left : num |>`

val buffer_flush_def = Define`
  buffer_flush cb (w1:'a word) w2 =
    if cb.position = w1 ∧ cb.position + (n2w(dimindex(:'b) DIV 8)) * n2w(LENGTH cb.buffer) = w2 then
      SOME ((cb.buffer:'b word list),
            cb with <| position := w2 ; buffer := [] |>)
    else NONE`;

val buffer_write_def = Define`
  buffer_write cb (w:'a word) (b:'b word) =
    if cb.position + (n2w(dimindex(:'b) DIV 8)) * n2w(LENGTH cb.buffer) = w ∧ 0 < cb.space_left then
      SOME (cb with <| buffer := cb.buffer++[b] ; space_left := cb.space_left-1|>)
    else NONE`;

val _ = Datatype `
  word_loc = Word ('a word) | Loc num num `;


val is_fwd_ptr_def = Define `
  (is_fwd_ptr (Word w) = ((w && 3w) = 0w)) /\
  (is_fwd_ptr _ = F)`;

val theWord_def = Define `
  theWord (Word w) = w`

val isWord_def = Define `
  (isWord (Word w) = T) /\ (isWord _ = F)`;

Theorem isWord_exists:
   isWord x ⇔ ∃w. x = Word w
Proof
  Cases_on`x` \\ rw[isWord_def]
QED

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
  stack_frame = StackFrame ((num # ('a word_loc)) list) ((num # num # num)option) `;

val _ = type_abbrev("gc_fun_type",
  ``: ('a word_loc list) # (('a word) -> ('a word_loc)) # ('a word) set #
      (store_name |-> 'a word_loc) ->
      (('a word_loc list) # (('a word) -> ('a word_loc)) #
      (store_name |-> 'a word_loc)) option``);

val gc_bij_ok_def = Define `
  gc_bij_ok (seq':num->num->num) = !n. BIJ (seq' n) UNIV UNIV`;

val _ = Datatype `
  state =
    <| locals  : ('a word_loc) num_map
     ; fp_regs : num |-> word64 (* FP regs are treated "globally" *)
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a stack_frame) list
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
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
     ; ffi     : 'ffi ffi_state |> `

val state_component_equality = theorem"state_component_equality";

val _ = Datatype `
  result = Result ('w word_loc) ('w word_loc)
         | Exception ('w word_loc) ('w word_loc)
         | TimeOut
         | NotEnoughSpace
         | FinalFFI final_event
         | Error `

val isResult_def = Define `
  (isResult (Result a b) = T) /\ (isResult _ = F)`;

val isException_def = Define `
  (isException (Exception a b) = T) /\ (isException _ = F)`;

val s = ``(s:('a,'c,'ffi) wordSem$state)``

val dec_clock_def = Define `
  dec_clock ^s = s with clock := s.clock - 1`;

val fix_clock_def = Define `
  fix_clock old_s (res,new_s) =
    (res,new_s with
      <| clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock ;
         termdep := old_s.termdep |>)`

val is_word_def = Define `
  (is_word (Word w) = T) /\
  (is_word _ = F)`

val get_word_def = Define `
  get_word (Word w) = w`

val _ = export_rewrites["is_word_def","get_word_def"];

val mem_store_def = Define `
  mem_store (addr:'a word) (w:'a word_loc) ^s =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) ^s =
    if addr IN s.mdomain then
      SOME (s.memory addr)
    else NONE`

val the_words_def = Define `
  (the_words [] = SOME []) /\
  (the_words (w::ws) =
     case (w,the_words ws) of
     | SOME (Word x), SOME xs => SOME (x::xs)
     | _ => NONE)`

val word_exp_def = tDefine "word_exp" `
  (word_exp ^s (Const w) = SOME (Word w)) /\
  (word_exp s (Var v) = lookup v s.locals) /\
  (word_exp s (Lookup name) = FLOOKUP s.store name) /\
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

val set_store_def = Define `
  set_store v x ^s = (s with store := s.store |+ (v,x))`;

val call_env_def = Define `
  call_env args ^s =
    s with <| locals := fromList2 args |>`;

val list_rearrange_def = Define `
  list_rearrange mover xs =
    (* if the mover function is actually a permutation,
     i.e. it bijects (or injects) the keys 0...n-1 to 0...n-1
     use it *)
    if (BIJ mover (count (LENGTH xs)) (count (LENGTH xs))) then
      GENLIST (\i. EL (mover i) xs) (LENGTH xs)
    else (* if it isn't well-formed, just pretend it is I *)
      xs`

(* Compare on keys, if keys match (never), then compare on
   the word_loc vals. Treat Words as < Locs *)
val key_val_compare_def = Define `
  key_val_compare x y =
    let (a:num,b) = x in
    let (a':num,b') = y in
      (a > a') \/
      (a = a' /\
        case b of
          Word x => (case b' of Word y => x <= y | _ => T)
        | Loc a b => case b' of Loc a' b' => (a>a') \/ (a=a' /\ b>=b') | _ => F)`

(*
EVAL ``key_val_compare (1,Loc 3 4) (1,Loc 1 2)``
*)

val env_to_list_def = Define `
  env_to_list env (bij_seq:num->num->num) =
    let mover = bij_seq 0 in
    let permute = (\n. bij_seq (n + 1)) in
    let l = toAList env in
    let l = QSORT key_val_compare l in
    let l = list_rearrange mover l in
      (l,permute)`

val push_env_def = Define `
  (push_env env NONE ^s =
    let (l,permute) = env_to_list env s.permute in
      s with <| stack := StackFrame l NONE :: s.stack
              ; permute := permute|>) ∧
  (push_env env (SOME (w:num,h:'a wordLang$prog,l1,l2)) s =
    let (l,permute) = env_to_list env s.permute in
      let handler = SOME (s.handler,l1,l2) in
      s with <| stack := StackFrame l handler :: s.stack
              ; permute := permute
              ; handler := LENGTH s.stack|>)`;

val pop_env_def = Define `
  pop_env ^s =
    case s.stack of
    | (StackFrame e NONE::xs) =>
         SOME (s with <| locals := fromAList e ; stack := xs |>)
    | (StackFrame e (SOME (n,_,_))::xs) =>
         SOME (s with <| locals := fromAList e ; stack := xs ; handler := n |>)
    | _ => NONE`;

val push_env_clock = Q.prove(
  `(wordSem$push_env env b ^s).clock = s.clock`,
  Cases_on `b` \\ TRY(PairCases_on`x`) \\ full_simp_tac(srw_ss())[push_env_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val pop_env_clock = Q.prove(
  `(wordSem$pop_env ^s = SOME s1) ==> (s1.clock = s.clock)`,
  full_simp_tac(srw_ss())[pop_env_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val jump_exc_def = Define `
  jump_exc ^s =
    if s.handler < LENGTH s.stack then
      case LASTN (s.handler+1) s.stack of
      | StackFrame e (SOME (n,l1,l2)) :: xs =>
          SOME (s with <| handler := n ; locals := fromAList e ; stack := xs |>,l1,l2)
      | _ => NONE
    else NONE`;

(* TODO: reuse this from dataSem? *)
val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (inter env name_set)
    else NONE`
(* -- *)

val cut_state_def = Define `
  cut_state names ^s =
    case cut_env names s.locals of
    | NONE => NONE
    | SOME env => SOME (s with locals := env)`;

val cut_state_opt_def = Define `
  cut_state_opt names ^s =
    case names of
    | NONE => SOME s
    | SOME names => cut_state names s`;

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

val enc_stack_def = Define `
  (enc_stack [] = []) /\
  (enc_stack ((StackFrame l handler :: st)) = MAP SND l ++ enc_stack st)`;

val dec_stack_def = Define `
  (dec_stack [] [] = SOME []) /\
  (dec_stack xs ((StackFrame l handler :: st)) =
     if LENGTH xs < LENGTH l then NONE else
       case dec_stack (DROP (LENGTH l) xs) st of
       | NONE => NONE
       | SOME s => SOME (StackFrame
           (ZIP (MAP FST l,TAKE (LENGTH l) xs)) handler :: s)) /\
  (dec_stack _ _ = NONE)`

val gc_def = Define `  (* gc runs the garbage collector algorithm *)
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
                          ; memory := m |>))`

val has_space_def = Define `
  has_space wl ^s =
    case (wl, FLOOKUP s.store NextFree, FLOOKUP s.store TriggerGC) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE`

val alloc_def = Define `
  alloc (w:'a word) names ^s =
    (* prune local names *)
    case cut_env names s.locals of
    | NONE => (SOME (Error:'a result),s)
    | SOME env =>
     (* perform garbage collection *)
     (case gc (push_env env (NONE:(num # 'a wordLang$prog # num # num) option) (set_store AllocSize (Word w) s)) of
      | NONE => (SOME Error,s)
      | SOME s =>
       (* restore local variables *)
       (case pop_env s of
        | NONE => (SOME Error, call_env [] s)
        | SOME s =>
         (* read how much space should be allocated *)
         (case FLOOKUP s.store AllocSize of
          | NONE => (SOME Error, s)
          | SOME w =>
           (* check how much space there is *)
           (case has_space w s of
            | NONE => (SOME Error, s)
            | SOME T => (* success there is that much space *)
                        (NONE,s)
            | SOME F => (* fail, GC didn't free up enough space *)
                        (SOME NotEnoughSpace,call_env [] s with stack:= [])))))`

val assign_def = Define `
  assign reg exp ^s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg w s)`;

val get_fp_var_def = Define`
  get_fp_var v (s:('a,'c,'ffi) wordSem$state) = FLOOKUP s.fp_regs v`

val set_fp_var_def = Define `
  set_fp_var v x (s:('a,'c,'ffi) wordSem$state) =
    (s with fp_regs := (s.fp_regs |+ (v,x)))`;

val inst_def = Define `
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
    | _ => NONE`

val get_var_imm_def = Define`
  (get_var_imm ((Reg n):'a reg_imm) ^s = get_var n s) ∧
  (get_var_imm (Imm w) s = SOME(Word w))`

val add_ret_loc_def = Define `
  (add_ret_loc NONE xs = xs) /\
  (add_ret_loc (SOME (n,names,ret_handler,l1,l2)) xs = (Loc l1 l2)::xs)`

(*Avoid case split*)
val bad_dest_args_def = Define`
  bad_dest_args dest args ⇔ dest = NONE ∧ args = []`

val termdep_rw = Q.prove(
  `((call_env p_1 ^s).termdep = s.termdep) /\
    ((dec_clock s).termdep = s.termdep) /\
    ((set_var n v s).termdep = s.termdep)`,
  EVAL_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val fix_clock_IMP_LESS_EQ = Q.prove(
  `!x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock /\ s1.termdep = s.termdep`,
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ decide_tac);

val MustTerminate_limit_def = zDefine `
  MustTerminate_limit (:'a) =
    (* This is just a number that's large enough for our purposes.
       It stated in a way that makes proofs easy. *)
    2 * dimword (:'a) +
    dimword (:'a) * dimword (:'a) +
    dimword (:'a) ** dimword (:'a) +
    dimword (:'a) ** dimword (:'a) ** dimword (:'a)`;

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip:'a wordLang$prog,^s) = (NONE,s)) /\
  (evaluate (Alloc n names,s) =
     case get_var n s of
     | SOME (Word w) => alloc w names s
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
     case FLOOKUP s.store name of
     | NONE => (SOME Error, s)
     | SOME x => (NONE, set_var v x s)) /\
  (evaluate (Set v exp,s) =
     if v = Handler ∨ v = BitmapBase then (SOME Error,s)
     else
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_store v w s)) /\
  (evaluate (Store exp v,s) =
     case (word_exp s exp, get_var v s) of
     | (SOME (Word a), SOME w) =>
         (case mem_store a w s of
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := [])
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
  (evaluate (Return n m,s) =
     case (get_var n s ,get_var m s) of
     | (SOME (Loc l1 l2),SOME y) => (SOME (Result (Loc l1 l2) y),call_env [] s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME (s,l1,l2) => (SOME (Exception (Loc l1 l2) w)),s)) /\
  (evaluate (If cmp r1 ri c1 c2,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then evaluate (c1,s)
                          else evaluate (c2,s)
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
             (case call_FFI s.ffi ffi_index bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),
                                      call_env [] s with stack := [])
              | FFI_return new_ffi new_bytes =>
                let new_m = write_bytearray w4 new_bytes s.memory s.mdomain s.be in
                  (NONE, s with <| memory := new_m ;
                                   locals := env ;
                                   ffi := new_ffi |>))
          | _ => (SOME Error,s)))
    | res => (SOME Error,s)) /\
  (evaluate (Call ret dest args handler,s) =
    case get_vars args s of
    | NONE => (SOME Error,s)
    | SOME xs =>
    if bad_dest_args dest args then (SOME Error,s)
    else
    case find_code dest (add_ret_loc ret xs) s.code of
          | NONE => (SOME Error,s)
          | SOME (args1,prog) =>
          case ret of
          | NONE (* tail call *) =>
      if handler = NONE then
        if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := [])
        else (case evaluate (prog, call_env args1 (dec_clock s)) of
         | (NONE,s) => (SOME Error,s)
         | (SOME res,s) => (SOME res,s))
      else (SOME Error,s)
          | SOME (n,names,ret_handler,l1,l2) (* returning call, returns into var n *) =>
    if domain names = {} then (SOME Error,s)
    else
          (case cut_env names s.locals of
                | NONE => (SOME Error,s)
                | SOME env =>
               if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := []) else
               (case fix_clock (call_env args1 (push_env env handler (dec_clock s)))
                       (evaluate (prog, call_env args1
                               (push_env env handler (dec_clock s)))) of
                | (SOME (Result x y),s2) =>
      if x ≠ Loc l1 l2 then (SOME Error,s2)
      else
                   (case pop_env s2 of
                    | NONE => (SOME Error,s2)
                    | SOME s1 =>
                        (if domain s1.locals = domain env
                         then evaluate(ret_handler,set_var n y s1)
                         else (SOME Error,s1)))
                | (SOME (Exception x y),s2) =>
                   (case handler of (* if handler is present, then handle exc *)
                    | NONE => (SOME (Exception x y),s2)
                    | SOME (n,h,l1,l2) =>
        if x ≠ Loc l1 l2 then (SOME Error,s2)
        else
          (if domain s2.locals = domain env
           then evaluate (h, set_var n y s2)
           else (SOME Error,s2)))
        | (NONE,s) => (SOME Error,s)
                | res => res)))`
  (WF_REL_TAC `(inv_image (measure I LEX measure I LEX measure (prog_size (K 0)))
                  (\(xs,^s). (s.termdep,s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY (full_simp_tac(srw_ss())[] \\ DECIDE_TAC)
   \\ full_simp_tac(srw_ss())[termdep_rw] \\ imp_res_tac fix_clock_IMP_LESS_EQ \\ full_simp_tac(srw_ss())[]
   \\ imp_res_tac (GSYM fix_clock_IMP_LESS_EQ)
   \\ TRY (Cases_on `handler`) \\ TRY (PairCases_on `x`)
   \\ full_simp_tac(srw_ss())[set_var_def,push_env_def,call_env_def,dec_clock_def,LET_THM]
   \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
   \\ full_simp_tac(srw_ss())[pop_env_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
   \\ decide_tac)

val evaluate_ind = theorem"evaluate_ind";

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
  \\ full_simp_tac(srw_ss())[push_env_def,set_store_def,call_env_def,LET_THM,pop_env_def]
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
  \\ full_simp_tac(srw_ss())[mem_store_def,call_env_def,dec_clock_def]
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

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
