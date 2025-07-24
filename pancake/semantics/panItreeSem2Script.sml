(* *)
open preamble panLangTheory itreeTauTheory panSemTheory;
open wordLangTheory ffiTheory;

val _ = new_theory "panItreeSem2";
(*
Datatype:
  result = Termination
         | Error
         | FinalFFI (ffiname # word8 list # word8 list) ffi_outcome
End

Definition pan_itree_unfold_err_def:
  pan_itree_unfold_err f =
  itreeTau$itree_unfold_err f
      ((λ(_,_,ws) r. LENGTH ws = LENGTH r),
      FinalFFI, (λe. FinalFFI e FFI_failed))
End
*)
Datatype:
  bstate =
    <| locals      : varname |-> 'a v
     ; code        : funname |-> ((varname # shape) list # ('a panLang$prog))
                     (* arguments (with shape), body *)
     ; eshapes     : eid |-> shape
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; sh_memaddrs    : ('a word) set
     ; be          : bool
     ; base_addr   : 'a word |>
End

val s = ``(s:'a panItreeSem2$bstate)``

Definition empty_locals_def:
   empty_locals ^s =
     s with <| locals := FEMPTY |>
End

Theorem empty_locals_defs = CONJ panSemTheory.empty_locals_def empty_locals_def;

Definition set_var_def:
  set_var v value ^s =
    (s with locals := s.locals |+ (v,value))
End

Theorem set_var_defs = CONJ panSemTheory.set_var_def set_var_def;

Definition eval_def:
  (eval ^s (Const w) = SOME (ValWord w)) /\
  (eval s  (Var v) = FLOOKUP s.locals v) /\
  (eval s (Label fname) =
    case FLOOKUP s.code fname of
     | SOME _ => SOME (ValLabel fname)
     | _ => NONE) /\
(*
  (eval s (GetAddr dname) =
    OPTION_MAP ValWord (FLOOKUP s.gaddrs dname)) /\ *)

  (eval s (Struct es) =
    case (OPT_MMAP (eval s) es) of
     | SOME vs => SOME (Struct vs)
     | NONE => NONE) /\
  (eval s (Field index e) =
    case eval s e of
     | SOME (Struct vs) =>
       if index < LENGTH vs then SOME (EL index vs)
       else NONE
     | _ => NONE) /\
  (eval s (Load shape addr) =
    case eval s addr of
     | SOME (ValWord w) => mem_load shape w s.memaddrs s.memory
     | _ => NONE) /\
  (eval s (Load32 addr) =
    case eval s addr of
     | SOME (ValWord w) =>
        (case mem_load_32 s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (ValWord (w2w w)))
        | _ => NONE) /\
  (eval s (LoadByte addr) =
    case eval s addr of
     | SOME (ValWord w) =>
        (case mem_load_byte s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (ValWord (w2w w)))
        | _ => NONE) /\
  (eval s (Op op es) =
    case (OPT_MMAP (eval s) es) of
     | SOME ws =>
       if (EVERY (\w. case w of (ValWord _) => T | _ => F) ws)
       then OPTION_MAP ValWord
            (word_op op (MAP (\w. case w of ValWord n => n) ws)) else NONE
      | _ => NONE) /\
  (eval s (Panop op es) =
    case (OPT_MMAP (eval s) es) of
     | SOME ws =>
       if (EVERY (\w. case w of (ValWord _) => T | _ => F) ws)
       then OPTION_MAP ValWord
            (pan_op op (MAP (\w. case w of ValWord n => n) ws)) else NONE
      | _ => NONE) /\
  (eval s (Cmp cmp e1 e2) =
    case (eval s e1, eval s e2) of
     | (SOME (ValWord w1), SOME (ValWord w2)) =>
          SOME (ValWord (if word_cmp cmp w1 w2 then 1w else 0w))
     | _ => NONE) /\
  (eval s (Shift sh e n) =
    case eval s e of
     | SOME (ValWord w) => OPTION_MAP ValWord (word_sh sh w n)
     | _ => NONE) /\
  (eval s BaseAddr =
        SOME (ValWord s.base_addr)) /\
  (eval s BytesInWord =
        SOME (ValWord bytes_in_word))
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
  \\ rpt strip_tac \\ imp_res_tac MEM_IMP_exp_size
  \\ TRY (first_x_assum (assume_tac o Q.SPEC `ARB`))
  \\ decide_tac
End

(*********)
(*
Datatype:
  step_result =
  | Pstep ('a prog # 'a bstate)
  | Pdone
  | Perror
  | Praise ('a exp)
  | Pffi ('a bstate)
      (ffiname # word8 list # word8 list)
End

Definition step_def:
  (step (Skip:'a panLang$prog,^s) c = (Pdone, s)) /\
  (step (Dec v e prog, s) c =
    case (eval s e) of
     | SOME value =>
         Dstep (prog,s with locals := s.locals |+ (v,value))
(*        (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))*)
        | NONE => Perror) /\
  (step (Assign v src,s) =
    case (eval s src) of
     | SOME value =>
        if is_valid_value s.locals v value
        then (NONE, s with locals := s.locals |+ (v,value))
        else (SOME Error, s)
        | NONE => (SOME Error, s)) /\
  (step (Store dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord addr), SOME value) =>
       (case mem_stores addr (flatten value) s.memaddrs s.memory of
         | SOME m => (NONE, s with memory := m)
         | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (step (Store32 dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord adr), SOME (ValWord w)) =>
        (case mem_store_32 s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (step (StoreByte dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord adr), SOME (ValWord w)) =>
        (case mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (step (ShMemLoad op v ad,s) =
    case eval s ad of
    | SOME (ValWord addr) =>
        (case FLOOKUP s.locals v of
           SOME (Val _) => sh_mem_load v addr (nb_op op) s
         | _ => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (step (ShMemStore op ad e,s) =
     case (eval s ad,eval s e) of
     | (SOME (ValWord addr), SOME (ValWord bytes)) => sh_mem_store bytes addr (nb_op op) s
     | _ => (SOME Error, s)) /\
  (step (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (step (c1,s)) in
     if res = NONE then step (c2,s1) else (res,s1)) /\
  (step (If e c1 c2,s) =
    case (eval s e) of
     | SOME (ValWord w) =>
        step (if w <> 0w then c1 else c2, s)  (* False is 0, True is everything else *)
     | _ => (SOME Error,s)) /\
  (step (Break,s) = (SOME Break,s)) /\
  (step (Continue,s) = (SOME Continue,s)) /\
  (step (While e c,s) =
    case (eval s e) of
     | SOME (ValWord w) =>
       if (w <> 0w) then
       (if s.clock = 0 then (SOME TimeOut,empty_locals s) else
         let (res,s1) = fix_clock (dec_clock s) (step (c,dec_clock s)) in
         case res of
          | SOME Continue => step (While e c,s1)
          | NONE => step (While e c,s1)
          | SOME Break => (NONE,s1)
          | _ => (res,s1))
        else (NONE,s)
     | _ => (SOME Error,s)) /\
  (step (Return e,s) =
    case (eval s e) of
      | SOME value =>
         if size_of_shape (shape_of value) <= 32
         then (SOME (Return value),empty_locals s)
         else (SOME Error,s)
      | _ => (SOME Error,s)) /\
  (step (Raise eid e,s) =
    case (FLOOKUP s.eshapes eid, eval s e) of
      | (SOME sh, SOME value) =>
         if shape_of value = sh ∧
            size_of_shape (shape_of value) <= 32
         then (SOME (Exception eid value),empty_locals s)
         else (SOME Error,s)
     | _ => (SOME Error,s)) /\
  (step (Tick,s) =
    if s.clock = 0 then (SOME TimeOut,empty_locals s)
    else (NONE,dec_clock s)) /\
  (step (Annot _ _,s) = (NONE, s)) /\
  (step (Call caltyp trgt argexps,s) =
    case (eval s trgt, OPT_MMAP (eval s) argexps) of
     | (SOME (ValLabel fname), SOME args) =>
        (case lookup_code s.code fname args of
          | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s)
           else
           let eval_prog = fix_clock ((dec_clock s) with locals := newlocals)
                                     (step (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,st)
              | (SOME Break,st) => (SOME Error,st)
              | (SOME Continue,st) => (SOME Error,st)
              | (SOME (Return retv),st) =>
                  (case caltyp of
                    | NONE      => (SOME (Return retv),empty_locals st)
                    | SOME (NONE, _) => (NONE, st with locals := s.locals)
                    | SOME (SOME rt,  _) =>
                       if is_valid_value s.locals rt retv
                       then (NONE, set_var rt retv (st with locals := s.locals))
                       else (SOME Error,st))
              | (SOME (Exception eid exn),st) =>
                  (case caltyp of
                    | NONE        => (SOME (Exception eid exn),empty_locals st)
                    | SOME (_, NONE) => (SOME (Exception eid exn),empty_locals st)
                    | SOME (_, (SOME (eid', evar, p))) =>
                      if eid = eid' then
                       case FLOOKUP s.eshapes eid of
                        | SOME sh =>
                            if shape_of exn = sh ∧ is_valid_value s.locals evar exn then
                              step (p, set_var evar exn (st with locals := s.locals))
                            else (SOME Error,st)
                        | NONE => (SOME Error,st)
                      else (SOME (Exception eid exn), empty_locals st))
              | (res,st) => (res,empty_locals st))
         | _ => (SOME Error,s))
     | (_, _) => (SOME Error,s))/\
  (step (DecCall rt shape trgt argexps prog1,s) =
    case (eval s trgt, OPT_MMAP (eval s) argexps) of
     | (SOME (ValLabel fname), SOME args) =>
        (case lookup_code s.code fname args of
          | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s)
           else
           let eval_prog = fix_clock ((dec_clock s) with locals := newlocals)
                                     (step (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,st)
              | (SOME Break,st) => (SOME Error,st)
              | (SOME Continue,st) => (SOME Error,st)
              | (SOME (Return retv),st) =>
                  if shape_of retv = shape then
                    let (res',st') = step (prog1, set_var rt retv (st with locals := s.locals)) in
                      (res',st' with locals := res_var st'.locals (rt, FLOOKUP s.locals rt))
                  else
                    (SOME Error, st)
              | (res,st) => (res,empty_locals st))
           | _ => (SOME Error,s))
     | (_, _) => (SOME Error,s)) /\
  (step (ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
   case (eval s ptr1, eval s len1, eval s ptr2, eval s len2) of
      | SOME (ValWord sz1),SOME (ValWord ad1),SOME (ValWord sz2),SOME (ValWord ad2) =>
        (case (read_bytearray sz1 (w2n ad1) (mem_load_byte s.memory s.memaddrs s.be),
               read_bytearray sz2 (w2n ad2) (mem_load_byte s.memory s.memaddrs s.be)) of
         | SOME bytes,SOME bytes2 =>
           (case call_FFI s.ffi (ExtCall (explode ffi_index)) bytes bytes2 of
            | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
            | FFI_return new_ffi new_bytes =>
                let nmem = write_bytearray sz2 new_bytes s.memory s.memaddrs s.be in
                 (NONE, s with <| memory := nmem; ffi := new_ffi |>))
         | _ => (SOME Error,s))
      | res => (SOME Error,s))
End

*)

(***************)

Type ev[pp] = “:ffiname # word8 list # word8 list”;

val rh = “rh:'a -> ('b, 'g + ev, 'b) itree”;
(*
val rh = “rh:'a panLang$prog # 'a bstate -> (ffi_outcome + word8 list, 'a panLang$prog # 'a bstate + ev, result) itree”;
*)

val rh = “rh:'a panLang$prog # 'a bstate -> ('a panSem$result option # 'a bstate, 'a panLang$prog # 'a bstate + ev, 'a panSem$result option # 'a bstate) itree”;

val rh = “rh:'a panLang$prog # 'a bstate -> ('a panSem$result option # 'a bstate, 'a panLang$prog # 'a bstate + ev, 'a panSem$result option # 'a bstate) itree”;

Definition mrec_def:
  mrec rh =
  itreeTau$itree_iter
  (λt. case t of
            | Ret r => Ret (INR r)
            | Tau t => Ret (INL t)
            | Vis (INL d) k => Ret (INL (itree_bind (rh d) k))
            | Vis (INR e) k => Vis e (Ret o INL o k))
End

Definition h_prog_dec_def:
  h_prog_dec vname e p ^s =
  case (eval s e) of
  | SOME value =>
      Vis (INL (p,s with locals := s.locals |+ (vname,value)))
          (λa. case a of
               | INL _ => Ret (INR (SOME Error, s))
               | INR (res,s') =>
                   Ret (INR (res,s' with locals := res_var s'.locals (vname, FLOOKUP s.locals vname))))
  | NONE => Ret (INR (SOME Error,s))
End

Definition h_prog_seq_def:
  h_prog_seq p1 p2 ^s =
  Vis (INL (p1,s))
      (λa. case a of
           | INL _ => Ret (INR (SOME Error, s))
           | INR (res,s') =>
               if res = NONE
               then Vis (INL (p2,s'))
                        (λa. case a of
                             | INL _ => Ret (INR (SOME Error, s))
                             | INR (res,s') => Ret (INR (res, s')))
               else Ret (INR (res,s')))
End

Definition h_prog_assign_def:
  h_prog_assign vname e ^s =
  case eval s e of
   | SOME value =>
      if is_valid_value s.locals vname value
      then Ret (INR (NONE,s with locals := s.locals |+ (vname,value)))
      else Ret (INR (SOME Error,s))
   | NONE => Ret (INR (SOME Error,s))
End

Definition h_prog_store_def:
  h_prog_store dst src ^s =
  case (eval s dst,eval s src) of
   | (SOME (ValWord addr),SOME value) =>
      (case mem_stores addr (flatten value) s.memaddrs s.memory of
        | SOME m => Ret (INR (NONE,s with memory := m))
        | NONE => Ret (INR (SOME Error,s)))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_store_byte_def:
  h_prog_store_byte dst src ^s =
  case (eval s dst,eval s src) of
   | (SOME (ValWord addr),SOME (ValWord w)) =>
      (case mem_store_byte s.memory s.memaddrs s.be addr (w2w w) of
        | SOME m => Ret (INR (NONE,s with memory := m))
        | NONE => Ret (INR (SOME Error,s)))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_store_32_def:
  h_prog_store_32 dst src ^s =
  case (eval s dst,eval s src) of
   | (SOME (ValWord addr),SOME (ValWord w)) =>
      (case mem_store_32 s.memory s.memaddrs s.be addr (w2w w) of
        | SOME m => Ret (INR (NONE,s with memory := m))
        | NONE => Ret (INR (SOME Error,s)))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_cond_def:
  h_prog_cond gexp p1 p2 ^s =
  case (eval s gexp) of
   | SOME (ValWord g) =>
       Vis (INL (if g ≠ 0w then p1 else p2,s))
           (λa. case a of
                | INL _ => Ret (INR (SOME Error, s))
                | INR (res,s') => Ret (INR (res, s')))
   | _ => Ret (INR (SOME Error,s))
End

(* NB The design of this while denotation restricts the type of Vis at this level of the semantics
 to having k-trees of: (res,bstate) -> (a,b,c) itree. *)
(* This is converted to the desired state in the top-level semantics. *)

(* Inf ITree of Vis nodes, with inf many branches allowing
 termination of the loop; when the guard is false. *)
Definition h_prog_while_def:
  h_prog_while g p ^s =
  itree_iter
  (λ(p,s). case (eval s g) of
           | SOME (ValWord w) =>
               if (w ≠ 0w)
               then (Vis (INL (p,s))
                         (λa. case a of
                              | INL _ => Ret (INR (INR (SOME Error,s)))
                              | INR (res,s') =>
                                  (case res of
                                   | SOME Break => Ret (INR (INR (NONE,s')))
                                   | SOME Continue => Ret (INL (p,s'))
                                   | NONE => Ret (INL (p,s'))
                                   | _ => Ret (INR (INR (res,s'))))))
               else Ret (INR (INR (NONE,s)))
           | _ => Ret (INR (INR (SOME Error,s))))
  (p,s)
End

val s' = ``(s':'a panItreeSem2$bstate)``

(* Handles the return value and exception passing of function calls. *)
Definition h_handle_call_ret_def:
  (h_handle_call_ret calltyp ^s (INL _) = Ret (INR (SOME Error,s))) ∧
  (h_handle_call_ret calltyp ^s (INR (NONE,s':'a bstate)) =
   Ret (INR (SOME Error,s'))) ∧
  (h_handle_call_ret calltyp s (INR (SOME Break,s')) =
   Ret (INR (SOME Error,s'))) ∧
  (h_handle_call_ret calltyp s (INR (SOME Continue,s')) =
   Ret (INR (SOME Error,s'))) ∧
  (h_handle_call_ret calltyp s (INR (SOME (Return retv),s')) =
   case calltyp of
     NONE => Ret (INR (SOME (Return retv),empty_locals s'))
   | SOME (NONE, _) => Ret (INR (NONE, s' with locals := s.locals))
   | SOME (SOME rt,_) =>
       if is_valid_value s.locals rt retv
       then Ret (INR (NONE,set_var rt retv (s' with locals := s.locals)))
       else Ret (INR (SOME Error,s'))) ∧
  (h_handle_call_ret calltyp s (INR (SOME (Exception eid exn),s')) =
   case calltyp of
     NONE => Ret (INR (SOME (Exception eid exn),empty_locals s'))
   | SOME (_,NONE) => Ret (INR (SOME (Exception eid exn),empty_locals s'))
   | SOME (_,(SOME (eid', evar, p))) =>
       if eid = eid'
       then
         (case FLOOKUP s.eshapes eid of
            SOME sh =>
              if shape_of exn = sh ∧ is_valid_value s.locals evar exn
              then Vis (INL (p,set_var evar exn (s' with locals := s.locals)))
                       (λa. case a of
                              | INL _ => Ret (INR (SOME Error, s'))
                              | INR (res, s') => Ret (INR (res, s')))
              else Ret (INR (SOME Error,s'))
          | NONE => Ret (INR (SOME Error,s')))
       else Ret (INR (SOME (Exception eid exn),empty_locals s'))) ∧
  (h_handle_call_ret calltyp s (INR (res,s')) = Ret (INR (res,empty_locals s')))
End

Definition h_prog_call_def:
  h_prog_call calltyp tgtexp argexps ^s =
  case (eval s tgtexp,OPT_MMAP (eval s) argexps) of
   | (SOME (ValLabel fname),SOME args) =>
      (case lookup_code s.code fname args of
        | SOME (callee_prog,newlocals) =>
           Vis (INL (callee_prog,s with locals := newlocals)) (h_handle_call_ret calltyp s)
        | _ => Ret (INR (SOME Error,s)))
   | (_,_) => Ret (INR (SOME Error,s))
End

(* Handles the return value and exception passing of function dec calls. *)
Definition h_handle_deccall_ret_def:
  (h_handle_deccall_ret rt shape prog1 ^s (INL _) = Ret (INR (SOME Error,s))) ∧
  (h_handle_deccall_ret rt shape prog1 ^s (INR (NONE,s':'a bstate)) = Ret (INR (SOME Error,s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (SOME Break,s')) = Ret (INR (SOME Error,s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (SOME Continue,s')) = Ret (INR (SOME Error,s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (SOME (Return retv),s')) =
   if shape_of retv = shape then
     Vis (INL (prog1, set_var rt retv (s' with locals := s.locals)))
         (λa. case a of
              | INL _ => Ret (INR (SOME Error, s'))
              | INR (res', s') =>
                  Ret (INR (res',s' with locals := res_var s'.locals (rt, FLOOKUP s.locals rt))))
   else Ret (INR (SOME Error, s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (res,s')) = Ret (INR (res,empty_locals s')))
End

Definition h_prog_deccall_def:
  h_prog_deccall rt shape tgtexp argexps prog1 ^s =
  case (eval s tgtexp,OPT_MMAP (eval s) argexps) of
   | (SOME (ValLabel fname),SOME args) =>
      (case lookup_code s.code fname args of
        | SOME (callee_prog,newlocals) =>
           Vis (INL (callee_prog,s with locals := newlocals)) (h_handle_deccall_ret rt shape prog1 s)
        | _ => Ret (INR (SOME Error,s)))
   | (_,_) => Ret (INR (SOME Error,s))
End

Definition h_prog_ext_call_def:
  h_prog_ext_call ffi_name conf_ptr conf_len array_ptr array_len ^s =
  case (eval s conf_ptr,eval s conf_len,eval s array_ptr,eval s array_len) of
    (SOME (ValWord conf_ptr_adr),SOME (ValWord conf_sz),
     SOME (ValWord array_ptr_adr),SOME (ValWord array_sz)) =>
     (case (read_bytearray conf_ptr_adr (w2n conf_sz) (mem_load_byte s.memory s.memaddrs s.be),
            read_bytearray array_ptr_adr (w2n array_sz) (mem_load_byte s.memory s.memaddrs s.be)) of
        (SOME conf_bytes,SOME array_bytes) =>
         (if explode ffi_name ≠ "" then
           Vis (INR (ExtCall (explode ffi_name), conf_bytes, array_bytes))
               (λres. case res of
                        INL (INL outcome) =>
                          Ret (INR (SOME (FinalFFI (Final_event (ExtCall (explode ffi_name)) conf_bytes array_bytes outcome)),empty_locals s))
                      | INL (INR new_bytes) =>
                          if LENGTH new_bytes = LENGTH array_bytes
                          then
                            (let nmem = write_bytearray array_ptr_adr new_bytes s.memory s.memaddrs s.be in
                               Ret (INR (NONE,s with memory := nmem)))
                          else
                            Ret (INR (SOME (FinalFFI (Final_event (ExtCall (explode ffi_name)) conf_bytes array_bytes FFI_failed)),empty_locals s))
                      | INR _ => Ret (INR (SOME Error,s)))
          else Ret (INR (NONE,s)))
      | _ => Ret (INR (SOME Error,s)))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_raise_def:
  h_prog_raise eid e ^s =
  case (FLOOKUP s.eshapes eid, eval s e) of
   | (SOME sh, SOME value) =>
      if shape_of value = sh ∧
         size_of_shape (shape_of value) <= 32
      then Ret (INR (SOME (Exception eid value),empty_locals s))
      else Ret (INR (SOME Error,s))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_return_def:
  h_prog_return e ^s =
  case (eval s e) of
   | SOME value =>
      if size_of_shape (shape_of value) <= 32
      then Ret (INR (SOME (Return value),empty_locals s))
      else Ret (INR (SOME Error,s))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_sh_mem_load_def:
  h_prog_sh_mem_load op v ad ^s =
  case eval s ad of
    SOME (ValWord addr) =>
     (case FLOOKUP s.locals v of
        SOME (Val _) =>
          (let nb = nb_op op in
           let bytes = word_to_bytes addr F in
             if nb = 0 then
               (if addr IN s.sh_memaddrs
                then
                  Vis (INR (SharedMem MappedRead, [n2w nb], bytes))
                      (λres. case res of
                               INL (INL outcome) =>
                                 Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes outcome)),empty_locals s))
                             | INL (INR new_bytes) =>
                                 if LENGTH new_bytes = LENGTH bytes
                                 then
                                   Ret (INR (NONE, (set_var v (ValWord (word_of_bytes F 0w new_bytes)) s)))
                                 else
                                   Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes FFI_failed)),empty_locals s))
                             | INR _ => Ret (INR (SOME Error,s)))
                else Ret (INR (SOME Error,s)))
             else
               (if (byte_align addr) IN s.sh_memaddrs then
                  Vis (INR (SharedMem MappedRead, [n2w nb], bytes))
                      (λres. case res of
                               INL (INL outcome) =>
                                 Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes outcome)),empty_locals s))
                             | INL (INR new_bytes) =>
                                 if LENGTH new_bytes = LENGTH bytes
                                 then
                                   Ret (INR (NONE,(set_var v (ValWord (word_of_bytes F 0w new_bytes)) s)))
                                 else
                                   Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes FFI_failed)),empty_locals s))
                             | INR _ => Ret (INR (SOME Error,s)))
                else Ret (INR (SOME Error,s))))
      | _ => Ret (INR (SOME Error, s)))
  | _ => Ret (INR (SOME Error, s))
End

Definition h_prog_sh_mem_store_def:
  h_prog_sh_mem_store op ad e ^s =
  case (eval s ad, eval s e) of
    (SOME (ValWord addr), SOME (ValWord w)) =>
      (let nb = nb_op op in
         if nb = 0 then
           (if addr IN s.sh_memaddrs then
              let bytes = word_to_bytes w F ++ word_to_bytes addr F in
                Vis (INR (SharedMem MappedWrite, [n2w nb], bytes))
                    (λres. case res of
                             INL (INL outcome) =>
                               Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes outcome)),s))
                           | INL (INR new_bytes) =>
                               if LENGTH new_bytes = LENGTH bytes
                               then
                                 Ret (INR (NONE,s))
                               else
                                 Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes FFI_failed)),s))
                           | INR _ => Ret (INR (SOME Error,s)))
            else Ret (INR (SOME Error,s)))
         else
           (if (byte_align addr) IN s.sh_memaddrs then
              let bytes = TAKE nb (word_to_bytes w F) ++ word_to_bytes addr F in
                Vis (INR (SharedMem MappedWrite, [n2w nb], bytes))
                    (λres. case res of
                             INL (INL outcome) =>
                               Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes outcome)),s))
                           | INL (INR new_bytes) =>
                               if LENGTH new_bytes = LENGTH bytes
                               then
                                 Ret (INR (NONE,s))
                               else
                                 Ret (INR (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes FFI_failed)),s))
                         | INR _ => Ret (INR (SOME Error,s)))
            else Ret (INR (SOME Error,s))))
   | _ => Ret (INR (SOME Error, s))
End

(* Recursive event handler for program commands *)
Definition h_prog_def:
  (h_prog (Skip,s) = Ret (INR (NONE,s))) ∧
  (h_prog (Annot _ _,s) = Ret (INR (NONE,s))) ∧
  (h_prog (Dec vname e p,s) = h_prog_dec vname e p s) ∧
  (h_prog (Assign vname e,s) = h_prog_assign vname e s) ∧
  (h_prog (Store dst src,s) = h_prog_store dst src s) ∧
  (h_prog (Store32 dst src,s) = h_prog_store_32 dst src s) ∧
  (h_prog (StoreByte dst src,s) = h_prog_store_byte dst src s) ∧
  (h_prog (ShMemLoad op v ad,s) = h_prog_sh_mem_load op v ad s) ∧
  (h_prog (ShMemStore op ad e,s) = h_prog_sh_mem_store op ad e s) ∧
  (h_prog (Seq p1 p2,s) = h_prog_seq p1 p2 s) ∧
  (h_prog (If gexp p1 p2,s) = h_prog_cond gexp p1 p2 s) ∧
  (h_prog (While gexp p,s) = h_prog_while gexp p s) ∧
  (h_prog (Break,s) = Ret (INR (SOME Break,s))) ∧
  (h_prog (Continue,s) = Ret (INR (SOME Continue,s))) ∧
  (h_prog (Call calltyp tgtexp argexps,s) = h_prog_call calltyp tgtexp argexps s) ∧
  (h_prog (DecCall rt shape tgtexp argexps prog1,s) = h_prog_deccall rt shape tgtexp argexps prog1 s) ∧
  (h_prog (ExtCall ffi_name conf_ptr conf_len array_ptr array_len,s) =
          h_prog_ext_call ffi_name conf_ptr conf_len array_ptr array_len s) ∧
  (h_prog (Raise eid e,s) = h_prog_raise eid e s) ∧
  (h_prog (Return e,s) = h_prog_return e s) ∧
  (h_prog (Tick,s) = Ret (INR (NONE,s)))
End

(*** imap for itreeTauTheory ***)


Definition imap_def:
  imap g itr =
  itree_unfold (λx. case x of
                      Ret r => Ret' (g r)
                    | Tau t => Tau' t
                    | Vis e f => Vis' e f
               ) itr
End

(******)


Definition temp_def:
  temp itre =
  imap (λx. case x of INR (r:'a) => r | INL (l:'b) => (ARB:'a)) itre
End
(*
Definition itree_semantics_def:
  itree_semantics (p:'a panLang$prog, ^s) =
  temp (mrec h_prog (h_prog (p, s)))
End
*)

