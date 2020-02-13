(*
  Semantics of panLang
*)

open preamble structLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory in end;

val _ = new_theory"structSem";
val _ = set_grammar_ancestry [
  "structLang", "alignment",
  "finite_map", "misc", "wordLang",  "ffi"]


Datatype:
  v = WordVal ('a word)
    | LabelVal funname
    | StructVal (v list)
End

Datatype:
  word_lab = Word ('a word)
           | Label funname
End

Datatype:
  state =
    <| locals      : varname |-> ('a v)
     ; code        : funname |-> (num # varname list # ('a structLang$prog))  (* function arity, arguments, body *) (* should include shape *)
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; clock       : num
     ; be          : bool
     ; ffi         : 'ffi ffi_state |>
End

val state_component_equality = theorem"state_component_equality";

Datatype:
  result = Error
         | TimeOut
         | Break
         | Continue
         | Return    ('a v)
         | Exception ('a v)
         | FinalFFI final_event
End

val s = ``(s:('a,'ffi) structSem$state)``

Definition is_structval_def:
  is_structval v =
    case v of
     | StructVal sv => T
     | _ => F
End

Definition strip_struct_def:
  strip_struct vs =
    FLAT (MAP (\v. case v of StructVal sv => sv) (FILTER is_structval vs))
End

Definition lookup_struct_def:
  (lookup_struct [] index = NONE) /\
  (lookup_struct v index =
     let len = LENGTH v in
       if index < len then SOME (EL index v)
       else lookup_struct (strip_struct v) (index - len))
Termination
  wf_rel_tac `measure SND` >>
  rpt strip_tac >> fs [LENGTH]
End

(* TODISC: what about address overflow *)
Definition addrs_touched_def:
  (addrs_touched [] addr = []) /\
  (addrs_touched (One::shapes) addr = addr :: addrs_touched shapes (addr + 1w)) /\
  (addrs_touched (Comb shape::shapes) addr =
     addrs_touched shape addr ++ addrs_touched shapes (addr + LAST (addrs_touched shape addr)))
Termination
  cheat
End

(*
Definition mem_load_def:
  mem_load (addr:'a word) ^s =
    if addr IN s.memaddrs
    then SOME (s.memory addr) else NONE
End
*)

Definition mem_load_comb_def:
  (mem_load_comb [] addr memory = []) /\
  (mem_load_comb (One::shapes) addr memory =
    (case memory addr of
      | Word w => WordVal w
      | Label lab => LabelVal lab) :: mem_load_comb shapes (addr + 1w) memory) /\
  (mem_load_comb (Comb shape::shapes) addr memory =
     StructVal (mem_load_comb shape addr memory) ::
       mem_load_comb shapes (addr + LAST (addrs_touched shape addr)) memory)
Termination
  cheat
End


Definition mem_load_struct:
  (mem_load_struct ^s addr One =
    if addr IN s.memaddrs
    then
      (case s.memory addr of
        | Word w => SOME (WordVal w)
        | Label lab => SOME (LabelVal lab))
    else NONE) /\
 (mem_load_struct s addr (Comb shape) =
    if set (addrs_touched shape addr) ⊆ s.memaddrs
    then SOME (StructVal (mem_load_comb shape addr s.memory))
    else NONE)
End


Definition eval_def:
  (eval ^s (Const w) = SOME (WordVal w)) /\
  (eval s  (Var v) =
    case FLOOKUP s.locals v of
     | SOME (WordVal w) => SOME (WordVal w)
     | _ => NONE) /\
  (eval s (Label fname) =
    case FLOOKUP s.locals fname of
     | SOME (LabelVal lab) => SOME (LabelVal lab)
     | _ => NONE) /\
  (eval s (Struct sname shape) = (* TODISC: not using shape for anything right now *)
    case FLOOKUP s.locals sname of
     | SOME (StructVal vs) => SOME (StructVal vs)
     | _ => NONE) /\
  (eval s (Lookup sname shape index) = (* TODISC: not using shape for anything right now *)
    case FLOOKUP s.locals sname of
     | SOME (StructVal vs) => lookup_struct vs index
     | _ => NONE) /\
  (eval s (Load addr shape) =
    case eval s addr of
     | SOME (WordVal w) => mem_load_struct s w shape
     | _ => NONE) /\
  (eval s (LoadByte addr) =
    case eval s addr of
     | SOME (WordVal w) =>
        (case mem_load_byte s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (WordVal (w2w w)))
        | _ => NONE) /\
  (eval s (Op op es) = (* TODISC: op are binops, logically they should work on Words, no struct or label. Is it right? *)
    case the_words (MAP (eval s) es) of
      | SOME ws => (OPTION_MAP WordVal (word_op op ws))
      | _ => NONE) /\
  (eval s (Cmp cmp e1 e2) =
    case (eval s e1, eval s e2) of
     | (SOME (WordVal w1), SOME (WordVal w2)) => SOME (WordVal (v2w [word_cmp cmp w1 w2]))
     | _ => NONE) /\
  (eval s (Shift sh e n) =
    case eval s e of
     | SOME (WordVal w) => OPTION_MAP WordVal (word_sh sh w n)
     | _ => NONE)
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
  \\ rpt strip_tac \\ imp_res_tac MEM_IMP_exp_size
  \\ TRY (first_x_assum (assume_tac o Q.SPEC `ARB`))
  \\ decide_tac
End


Definition shape_value_rel_def:
  (shape_value_rel (WordVal w)    One = T) /\
  (shape_value_rel (LabelVal lab) One = T) /\
  (shape_value_rel (StructVal []) (Comb []) = T) /\
  (shape_value_rel (StructVal (sv::svs)) (Comb (c::cs)) =
    (shape_value_rel sv c /\ shape_value_rel (StructVal svs) (Comb cs)))
End


Definition mem_store_def:
  mem_store (addr:'a word) (w:'a word_lab) ^s =
    if addr IN s.memaddrs then
    SOME (s with memory := (addr =+ w) s.memory)
    else NONE
End


Definition mem_store_byte_def:
  mem_store_byte m dm be w b =
  case m (byte_align w) of
   | Word v =>
     if byte_align w IN dm
     then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
     else NONE
   | Label _ => NONE
End

Definition write_bytearray_def:
  (write_bytearray a [] m dm be = m) /\
  (write_bytearray a (b::bs) m dm be =
    case mem_store_byte (write_bytearray (a+1w) bs m dm be) dm be a b of
     | SOME m => m
     | NONE => m)
End

Definition mem_load_byte_def:
  mem_load_byte m dm be w =
  case m (byte_align w) of
    | Label _ => NONE
    | Word v =>
       if byte_align w IN dm
       then SOME (get_byte w v be) else NONE
End

Definition the_words_def:
  (the_words [] = SOME []) /\
  (the_words (w::ws) =
     case (w,the_words ws) of
      | SOME (WordVal x), SOME xs => SOME (x::xs)
      | _ => NONE)
End

(*
Definition get_var_def:
  get_var v ^s = FLOOKUP s.locals v
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
*)


Definition set_var_def:
  set_var v value ^s =
    (s with locals := s.locals |+ (v,value))
End

Definition upd_locals_def:
   upd_locals varargs ^s =
     s with <| locals := FEMPTY |++ varargs  |>
End

Definition empty_locals_def:
   empty_locals ^s =
     s with <| locals := FEMPTY |>
End

(*
(* gv: global variable *)
Definition set_globals_def:
  set_globals gv w ^s =
    (s with globals := s.globals |+ (gv,w))
End


Definition lookup_code_def:
  lookup_code code fname args len =
    case (FLOOKUP code fname) of
      | SOME (arity, vlist, prog) =>
         if len = arity /\ LENGTH vlist = LENGTH args
         then SOME (prog, alist_to_fmap (ZIP (vlist,args))) else NONE
      | _ => NONE
End
*)


Definition dec_clock_def:
  dec_clock ^s =
   s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res, new_s) =
    (res, new_s with <|clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)
End

Theorem fix_clock_IMP_LESS_EQ:
  !x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock
Proof
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> decide_tac
QED


Definition mem_write_def:
  mem_write adr value shape mem domain be = mem
End

(* Next steps: define a function to store structs to memory,
    to have a lookup functions *)

Definition evaluate_def:
  (evaluate (Skip:'a structLang$prog,^s) = (NONE,s)) /\
  (evaluate (Assign v shape src,s) =
    case (eval s src) of
     | SOME value =>
        if shape_value_rel value shape then (NONE, set_var v value s)
        else (SOME Error, s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Store dst shape src,s) =
    case (eval s dst, eval s src) of
     | (SOME (WordVal adr), SOME value) =>
        if shape_value_rel value shape then
          (NONE, s with memory := mem_write adr value shape s.memory s.memaddrs s.be)
        else (SOME Error, s)
     | _ => (SOME Error, s)) /\
  (evaluate (StoreByte dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (WordVal adr), SOME (WordVal w)) =>
        (case mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If e c1 c2,s) =
    case (eval s e) of
     | SOME (WordVal w) =>
        evaluate (if w <> 0w then c1 else c2, s)  (* False is 0, True is everything else *)
        | _ => (SOME Error,s)) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\
  (evaluate (While e c,s) =
    case (eval s e) of
     | SOME (WordVal w) =>
       if (w <> 0w) then
        let (res,s1) = fix_clock s (evaluate (c,s)) in
          if s1.clock = 0 then (SOME TimeOut,empty_locals s1)
          else
           case res of
            | SOME Continue => evaluate (While e c,dec_clock s1)
            | NONE => evaluate (While e c,dec_clock s1)
            | SOME Break => (NONE,s1)
            | _ => (res,s1)
       else (NONE,s)
       | _ => (SOME Error,s)) /\
  (evaluate (Return shape e,s) =
    case (eval s e) of
     | SOME value =>
       if shape_value_rel value shape then (SOME (Return value),empty_locals s)
           else (SOME Error, s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise shape e,s) =
    case (eval s e) of
     | SOME value =>
       if shape_value_rel value shape then (SOME (Exception value),empty_locals s)
           else (SOME Error, s)
     | _ => (SOME Error,s)) /\
 (evaluate (Tick,s) =
   if s.clock = 0 then (SOME TimeOut,empty_locals s)
   else (NONE,dec_clock s))
Termination
 cheat
End


(*
/\
 (evaluate (Call caltyp trgt argexps,s) =
   case (eval s trgt, OPT_MMAP (eval s) argexps) of
    | (SOME (Label fname), SOME args) =>
       (case lookup_code s.code fname args (LENGTH args) of
         | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s) else
           let eval_prog = fix_clock ((dec_clock s) with locals:= newlocals)
                                     (evaluate (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
	      | (NONE,st) => (SOME Error,st)
              | (SOME Break,st) => (SOME Error,st)
              | (SOME Continue,st) => (SOME Error,st)
	      | (SOME (Return retv),st) =>
                  (case caltyp of
                    | Tail    => (SOME (Return retv),st)
                    | Ret rt  => (NONE, set_var rt retv (st with locals := s.locals))
                    | Handle rt evar p => (NONE, set_var rt retv (st with locals := s.locals)))
              | (SOME (Exception exn),st) =>
                  (case caltyp of
                    | Tail    => (SOME (Exception exn),st)
                    | Ret rt  => (SOME (Exception exn), st with locals := s.locals)
                    | Handle rt evar p =>  evaluate (p, set_var evar exn (st with locals := s.locals)))
              | (res,st) =>
                  (case caltyp of
                    | Tail => (res,st)
                    | _  => (res,st with locals := s.locals)))
         | _ => (SOME Error,s))
    | (_, _) => (SOME Error,s)) /\
  (evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
   case (FLOOKUP s.locals len1, FLOOKUP s.locals ptr1, FLOOKUP s.locals len2, FLOOKUP s.locals ptr2) of
    | SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4) =>
       (case (read_bytearray w2 (w2n w) (mem_load_byte s.memory s.memaddrs s.be),
              read_bytearray w4 (w2n w3) (mem_load_byte s.memory s.memaddrs s.be)) of
         | SOME bytes,SOME bytes2 =>
            (case call_FFI s.ffi (explode ffi_index) bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),s)
              | FFI_return new_ffi new_bytes =>
                   (NONE, s with <| memory := write_bytearray w4 new_bytes s.memory s.memaddrs s.be
                                              ;ffi := new_ffi |>))
         | _ => (SOME Error,s))
       | res => (SOME Error,s))
Termination
  wf_rel_tac `(inv_image (measure I LEX measure (prog_size (K 0)))
               (\(xs,^s). (s.clock,xs)))` >>
  rpt strip_tac >> TRY (full_simp_tac(srw_ss())[] >> DECIDE_TAC) >>
  imp_res_tac fix_clock_IMP_LESS_EQ >> full_simp_tac(srw_ss())[] >>
  imp_res_tac (GSYM fix_clock_IMP_LESS_EQ) >>
  full_simp_tac(srw_ss())[set_var_def,set_globals_def,upd_locals_def,dec_clock_def, LET_THM] >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  decide_tac
End


val evaluate_ind = theorem"evaluate_ind";


Theorem evaluate_clock:
   !prog s r s'. (evaluate (prog,s) = (r,s')) ==>
                 s'.clock <= s.clock
Proof
  (*recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ rw [] \\ every_case_tac
  \\ fs [set_var_def, mem_store_def,call_env_def,dec_clock_def, LET_THM]
  \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rveq
  \\ imp_res_tac fix_clock_IMP_LESS_EQ
  \\ imp_res_tac LESS_EQ_TRANS \\ fs []*)
  cheat
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
*)
val _ = export_theory();
