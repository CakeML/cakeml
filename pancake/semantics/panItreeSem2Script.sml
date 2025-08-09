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

(*** mrec ***)

Definition mrec_def:
  mrec rh =
  itreeTau$itree_iter
  (λt. case t of
            | Ret r => Ret (INR r)
            | Tau t => Ret (INL t)
            | Vis (INL d) k => Ret (INL (itree_bind (rh d) k))
            | Vis (INR e) k => Vis e (Ret o INL o k))
End

Theorem mrec_simps[simp]:
  (mrec rh (Ret r) = Ret r) ∧
  (mrec rh (Tau u) = Tau (mrec rh u)) ∧
  (mrec rh (Vis (INL seed) k) =
   Tau (mrec rh (itree_bind (rh seed) k))) ∧
  (mrec rh (Vis (INR e) k) = (Vis e (Tau o mrec rh o k)))
Proof
  rw [mrec_def] >>
  rw [Once itreeTauTheory.itree_iter_thm] >>
  CONV_TAC FUN_EQ_CONV >> rw []
QED

Theorem mrec_bind:
  mrec rh (itree_bind ht (k:'a -> ('a,'d+'b,'a) itree)) =
  itree_bind (mrec rh ht) (mrec rh o k)
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists ‘CURRY ({(mrec rh (itree_bind ht (k:'a->('a,'d+'b,'a)itree)),
                    itree_bind (mrec rh ht) (mrec rh ∘ k)) | ht, k |T}
           ∪ {(Tau $ mrec rh (itree_bind ht (k:'a->('a,'d+'b,'a)itree)),
               Tau $ itree_bind (mrec rh ht) (mrec rh ∘ k)) | ht, k | T})’ >>
  conj_tac >- (rw[EXISTS_PROD] >>  metis_tac[]) >>
  rw[]
  >- (Cases_on ‘ht’ >> gvs[mrec_simps] >>
      rename1 ‘Vis e’ >> Cases_on ‘e’ >> gvs[mrec_simps])
  >- (Cases_on ‘ht’ >> gvs[mrec_simps,PULL_EXISTS,EXISTS_PROD]
      >- metis_tac[]
      >- metis_tac[] >>
      rename1 ‘Vis e’ >> Cases_on ‘e’ >> gvs[mrec_simps] >>
      metis_tac[itree_bind_assoc])
  >- metis_tac[] >>
  Cases_on ‘ht’ >> gvs[mrec_simps,PULL_EXISTS,EXISTS_PROD]
  >- metis_tac[] >>
  rename1 ‘mrec rh (Vis e _)’ >>
  Cases_on ‘e’ >>
  gvs[mrec_simps] >>
  metis_tac[]
QED



(*** handler ***)

Definition h_prog_dec_def:
  h_prog_dec vname e p ^s =
  case (eval s e) of
  | SOME value =>
      Vis (INL (p,s with locals := s.locals |+ (vname,value)))
          (λa. Ret (INR (case a of
               | INL _ => (SOME Error, s)
               | INR (res,s') =>
                   (res,s' with locals := res_var s'.locals (vname, FLOOKUP s.locals vname)))))
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
                        (λa. Ret (INR (case a of
                             | INL _ => (SOME Error, s)
                             | INR (res,s') => (res, s'))))
               else Ret (INR (res,s')))
End

Definition h_prog_assign_def:
  h_prog_assign vname e ^s =
  Ret (INR (case eval s e of
            | SOME value =>
                if is_valid_value s.locals vname value
                then (NONE,s with locals := s.locals |+ (vname,value))
                else (SOME Error,s)
            | NONE => (SOME Error,s)))
End

Definition h_prog_store_def:
  h_prog_store dst src ^s =
  Ret (INR (case (eval s dst,eval s src) of
            | (SOME (ValWord addr),SOME value) =>
                (case mem_stores addr (flatten value) s.memaddrs s.memory of
                 | SOME m => (NONE,s with memory := m)
                 | NONE => (SOME Error,s))
            | _ => (SOME Error,s)))
End

Definition h_prog_store_byte_def:
  h_prog_store_byte dst src ^s =
  Ret (INR (case (eval s dst,eval s src) of
            | (SOME (ValWord addr),SOME (ValWord w)) =>
                (case mem_store_byte s.memory s.memaddrs s.be addr (w2w w) of
                 | SOME m => (NONE,s with memory := m)
                 | NONE => (SOME Error,s))
            | _ => (SOME Error,s)))
End

Definition h_prog_store_32_def:
  h_prog_store_32 dst src ^s =
  Ret (INR (case (eval s dst,eval s src) of
            | (SOME (ValWord addr),SOME (ValWord w)) =>
                (case mem_store_32 s.memory s.memaddrs s.be addr (w2w w) of
                 | SOME m => (NONE,s with memory := m)
                 | NONE => (SOME Error,s))
            | _ => (SOME Error,s)))
End

Definition h_prog_cond_def:
  h_prog_cond gexp p1 p2 ^s =
  case (eval s gexp) of
   | SOME (ValWord g) =>
       Vis (INL (if g ≠ 0w then p1 else p2,s))
           (λa. Ret (INR (case a of
                          | INL _ => (SOME Error, s)
                          | INR (res,s') => (res, s'))))
   | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_while_def:
  h_prog_while g p ^s =
  itree_iter
  (λ(p,s). case (eval s g) of
           | SOME (ValWord w) =>
               if (w ≠ 0w)
               then (Vis (INL (p,s))
                         (λa. Ret (case a of
                                   | INL _ => INR (INR (SOME Error,s))
                                   | INR (res,s') =>
                                       (case res of
                                        | SOME Break => INR (INR (NONE,s'))
                                        | SOME Continue => INL (p,s')
                                        | NONE => INL (p,s')
                                        | _ => INR (INR (res,s'))))))
               else Ret (INR (INR (NONE,s)))
           | _ => Ret (INR (INR (SOME Error,s))))
  (p,s)
End

val s' = ``(s':'a panItreeSem2$bstate)``

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
                       (λa. Ret (INR (case a of
                                      | INL _ => (SOME Error, s')
                                      | INR (res, s') => (res, s'))))
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

Definition h_handle_deccall_ret_def:
  (h_handle_deccall_ret rt shape prog1 ^s (INL _) = Ret (INR (SOME Error,s))) ∧
  (h_handle_deccall_ret rt shape prog1 ^s (INR (NONE,s':'a bstate)) = Ret (INR (SOME Error,s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (SOME Break,s')) = Ret (INR (SOME Error,s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (SOME Continue,s')) = Ret (INR (SOME Error,s'))) ∧
  (h_handle_deccall_ret rt shape prog1 s (INR (SOME (Return retv),s')) =
   if shape_of retv = shape then
     Vis (INL (prog1, set_var rt retv (s' with locals := s.locals)))
         (λa. Ret (INR (case a of
                        | INL _ => (SOME Error, s')
                        | INR (res', s') =>
                            (res',s' with locals := res_var s'.locals (rt, FLOOKUP s.locals rt)))))
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
               (λres. Ret (INR
                           (case res of
                              INL x =>
                                (case x of
                                   INL outcome =>
                                     (SOME (FinalFFI (Final_event (ExtCall (explode ffi_name)) conf_bytes array_bytes outcome)),empty_locals s)
                                 | INR new_bytes =>
                                     (if LENGTH new_bytes = LENGTH array_bytes
                                      then
                                        (let nmem = write_bytearray array_ptr_adr new_bytes s.memory s.memaddrs s.be in
                                           (NONE,s with memory := nmem))
                                      else
                                        (SOME (FinalFFI (Final_event (ExtCall (explode ffi_name)) conf_bytes array_bytes FFI_failed)),empty_locals s)))
                            | INR _ => (SOME Error,s))))
          else Ret (INR
                    (NONE, s with memory := write_bytearray array_ptr_adr array_bytes s.memory s.memaddrs s.be)))
      | _ => Ret (INR (SOME Error,s)))
  | _ => Ret (INR (SOME Error,s))
End

Definition h_prog_raise_def:
  h_prog_raise eid e ^s =
  Ret (INR (case (FLOOKUP s.eshapes eid, eval s e) of
            | (SOME sh, SOME value) =>
                if shape_of value = sh ∧
                   size_of_shape (shape_of value) <= 32
                then (SOME (Exception eid value),empty_locals s)
                else (SOME Error,s)
            | _ => (SOME Error,s)))
End

Definition h_prog_return_def:
  h_prog_return e ^s =
  Ret (INR (case (eval s e) of
            | SOME value =>
                if size_of_shape (shape_of value) <= 32
                then (SOME (Return value),empty_locals s)
                else (SOME Error,s)
            | _ => (SOME Error,s)))
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
                      (λres. Ret (INR
                                  (case res of
                                     INL x =>
                                       (case x of
                                          INL outcome =>
                                            (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes outcome)),empty_locals s)
                                        | INR new_bytes =>
                                            (if LENGTH new_bytes = LENGTH bytes
                                             then
                                               (NONE, (set_var v (ValWord (word_of_bytes F 0w new_bytes)) s))
                                             else
                                               (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes FFI_failed)),empty_locals s)))
                                   | INR _ => (SOME Error,s))))
                else Ret (INR (SOME Error,s)))
             else
               (if (byte_align addr) IN s.sh_memaddrs then
                  Vis (INR (SharedMem MappedRead, [n2w nb], bytes))
                      (λres. Ret (INR
                                  (case res of
                                     INL x =>
                                       (case x of
                                          INL outcome =>
                                            (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes outcome)),empty_locals s)
                                        | INR new_bytes =>
                                            (if LENGTH new_bytes = LENGTH bytes
                                             then
                                               (NONE,(set_var v (ValWord (word_of_bytes F 0w new_bytes)) s))
                                             else
                                               (SOME (FinalFFI (Final_event (SharedMem MappedRead) [n2w nb] bytes FFI_failed)),empty_locals s)))
                                   | INR _ => (SOME Error,s))))
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
                    (λres. Ret (INR
                                (case res of
                                   INL x =>
                                     (case x of
                                        INL outcome =>
                                          (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes outcome)),s)
                                      | INR new_bytes =>
                                          (if LENGTH new_bytes = LENGTH bytes
                                           then (NONE,s)
                                           else
                                             (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes FFI_failed)),s)))
                                 | INR _ => (SOME Error,s))))
            else Ret (INR (SOME Error,s)))
         else
           (if (byte_align addr) IN s.sh_memaddrs then
              let bytes = TAKE nb (word_to_bytes w F) ++ word_to_bytes addr F in
                Vis (INR (SharedMem MappedWrite, [n2w nb], bytes))
                    (λres. Ret (INR
                                (case res of
                                   INL x =>
                                     (case x of
                                        INL outcome =>
                                          (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes outcome)),s)
                                      | INR new_bytes =>
                                          (if LENGTH new_bytes = LENGTH bytes
                                           then (NONE,s)
                                           else
                                             (SOME (FinalFFI (Final_event (SharedMem MappedWrite) [n2w nb] bytes FFI_failed)),s)))
                                 | INR _ => (SOME Error,s))))
            else Ret (INR (SOME Error,s))))
   | _ => Ret (INR (SOME Error, s))
End

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


(*** maps for itreeTauTheory ***)

Definition Ret_map_def:
  Ret_map g itr =
  itree_unfold (λx. case x of
                      Ret r => Ret' (g r)
                    | Tau t => Tau' t
                    | Vis e f => Vis' e f
               ) itr
End

Definition Vis_dom_INR_def:
  Vis_dom_INR itr =
  itree_unfold (λx. case x of
                      Ret r => Ret' r
                    | Tau t => Tau' t
                    | Vis e f => Vis' e (λx. f (INR x))
               ) itr
End

(******)

Definition itree_semantics_def:
  itree_semantics (p:'a panLang$prog, ^s) =
  let g= (λx. case x of
              | INR (r:'a result option # 'a bstate) => r
              | INL (l:ffi_outcome + word8 list) =>
                  (ARB:'a result option # 'a bstate)) in
  itree_unfold (λx. case x of
                      Ret r => Ret' (g r)
                    | Tau t => Tau' t
                    | Vis e f => Vis' e (λx. f (INL x)))
               (mrec h_prog (h_prog (p, s)))
End

val h_prog_ss = simpLib.named_rewrites "h_prog_ss" [
    h_prog_def,
    h_prog_assign_def,
    h_prog_store_def,
    h_prog_store_32_def,
    h_prog_store_byte_def,
(*    h_prog_cond_def,*)
    h_prog_raise_def,
    h_prog_return_def]

(*** traces ***)

Definition trace_prefix_def:
  trace_prefix 0 (oracle, ffi_st) itree = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Ret r) = ([], SOME r) ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Tau t) = trace_prefix n (oracle, ffi_st) t ∧
  trace_prefix (SUC n) (oracle, ffi_st) (Vis (s, conf, ws) f) =
    case oracle s ffi_st conf ws of
    | Oracle_return ffi_st' ws' =>
        let (io, res) = trace_prefix n (oracle, ffi_st') (f $ INR ws') in
        if LENGTH ws ≠ LENGTH ws' then (io, res)
        else (IO_event s conf (ZIP (ws,ws'))::io, res)
    | Oracle_final outcome => trace_prefix n (oracle, ffi_st) (f $ INL outcome)
End

Triviality trace_prefix_Ret[simp]:
  FST (trace_prefix n (or, ffi) (Ret r)) = []
Proof
  Cases_on ‘n’>>simp[trace_prefix_def]
QED

(****)

Definition ext_def:
  ext ^s k ffi =
    <| locals      := s.locals
     ; code        := s.code
     ; eshapes     := s.eshapes
     ; memory      := s.memory
     ; memaddrs    := s.memaddrs
     ; sh_memaddrs := s.sh_memaddrs
     ; be          := s.be
     ; ffi         := ffi
     ; base_addr   := s.base_addr
     ; clock       := k
|>
End

Theorem ext_access[simp]:
  (ext t k ffi).locals = t.locals ∧
  (ext t k ffi).code = t.code ∧
  (ext t k ffi).eshapes = t.eshapes ∧
  (ext t k ffi).memory = t.memory ∧
  (ext t k ffi).memaddrs = t.memaddrs ∧
  (ext t k ffi).sh_memaddrs = t.sh_memaddrs ∧
  (ext t k ffi).be = t.be ∧
  (ext t k ffi).ffi = ffi ∧
  (ext t k ffi).base_addr = t.base_addr ∧
  (ext t k ffi).clock = k
Proof
  rw[ext_def]
QED

Theorem eval_ext[simp]:
  eval (ext s t ffi) e = eval s e
Proof
  map_every qid_spec_tac [‘t’,‘ffi’,‘e’,‘s’]>>
  recInduct eval_ind>>rw[]>>
  simp[eval_def,panSemTheory.eval_def]>>
  TRY (simp[ext_def]>>NO_TAC)>>
  ‘OPT_MMAP (λe. eval (ext s t ffi) e) es = OPT_MMAP (λe. eval s e) es’ by
    (pop_assum mp_tac>>
     qid_spec_tac ‘es’>>Induct>>rw[])>>
  fs[]
QED

Theorem opt_mmap_eval_ext[simp]:
  OPT_MMAP (eval (ext s t ffi)) es = OPT_MMAP (eval s) es
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN]
QED

Theorem ext_normalise[simp]:
  ext s t f with locals := x = ext (s with locals := x) t f ∧
  ext s t f with memory := m = ext (s with memory := m) t f ∧
  dec_clock (ext s k f) = ext s (k - 1) f
Proof
  simp[ext_def,dec_clock_def]
QED

(****)

Definition bst_def:
  bst (s:('a,'b) panSem$state) =
    <| locals      := s.locals
     ; code        := s.code
     ; eshapes     := s.eshapes
     ; memory      := s.memory
     ; memaddrs    := s.memaddrs
     ; sh_memaddrs := s.sh_memaddrs
     ; be          := s.be
     ; base_addr   := s.base_addr
|>
End

Theorem bst_access[simp]:
  (bst t).locals = t.locals ∧
  (bst t).code = t.code ∧
  (bst t).eshapes = t.eshapes ∧
  (bst t).memory = t.memory ∧
  (bst t).memaddrs = t.memaddrs ∧
  (bst t).sh_memaddrs = t.sh_memaddrs ∧
  (bst t).be = t.be ∧
  (bst t).base_addr = t.base_addr
Proof
  rw[bst_def]
QED

Theorem bst_normalise[simp]:
  bst s with locals := x = bst (s with locals := x) ∧
  bst s with memory := m = bst (s with memory := m)
Proof
  simp[bst_def]
QED

Theorem eval_bst[simp]:
  eval (bst s) e = eval s e
Proof
  map_every qid_spec_tac [‘e’,‘s’]>>
  recInduct panSemTheory.eval_ind>>rw[]>>
  simp[eval_def,panSemTheory.eval_def]>>
  TRY (simp[bst_def]>>NO_TAC)>>
  ‘OPT_MMAP (λe. eval (bst s) e) es = OPT_MMAP (λe. eval s e) es’ by
    (pop_assum mp_tac>>
     qid_spec_tac ‘es’>>Induct>>rw[])>>
  fs[]
QED

Theorem opt_mmap_eval_bst[simp]:
  OPT_MMAP (eval (bst s)) es = OPT_MMAP (eval s) es
Proof
  rw [] >>
  match_mp_tac IMP_OPT_MMAP_EQ >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN]
QED

(***)

Theorem ext_bst_id[simp]:
  ext (bst s) s.clock s.ffi = s ∧
  ext (bst s with locals := x) s.clock s.ffi = s with locals := x ∧
  ext (bst s with memory := m) s.clock s.ffi = s with memory := m ∧
  ext (empty_locals (bst s)) s.clock s.ffi = empty_locals s
Proof
  simp[bst_def,ext_def,state_component_equality,empty_locals_defs]
QED

Theorem bst_ext_id[simp]:
  bst (ext s t f) = s ∧
  bst (ext s t f with locals := x) = s with locals := x ∧
  bst (ext s t f with memory := m) = s with memory := m ∧
  bst (empty_locals (ext s k ffi)) = empty_locals s ∧
  bst (dec_clock (ext s k ffi)) = s
Proof
  simp[bst_def,ext_def,fetch "-" "bstate_component_equality",
       empty_locals_defs,dec_clock_def]
QED

(***)

Theorem mrec_Ret_INR:
  mrec h_prog (h_prog (p,s)) = Ret x ⇒ ∃y. x = INR y
Proof
  map_every qid_spec_tac [‘x’,‘s’,‘p’]>>
  Induct>>rw[]
  >~[‘While’]>-
   (fs[h_prog_def,h_prog_while_def]>>
    fs[Once itree_iter_thm]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[])
  >~[‘ExtCall’]>-
   (fs[h_prog_def,h_prog_ext_call_def]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[])>>
  fs[SF h_prog_ss,h_prog_call_def,h_prog_deccall_def,
     h_prog_dec_def,h_prog_seq_def,h_prog_cond_def,
     h_prog_ext_call_def,h_prog_sh_mem_load_def,h_prog_sh_mem_store_def]>>
  rpt (FULL_CASE_TAC>>fs[mrec_simps])>>gvs[]
QED

Type ptree = “:((ffi_outcome + word8 list) + α result option # α bstate, ev,
     (ffi_outcome + word8 list) + α result option # α bstate) itree”;

Theorem mrec_While:
  (mrec h_prog (h_prog (While e p,s)):'a ptree) =
  case eval s e of
    SOME (ValWord w) =>
      if w = 0w then Ret (INR (NONE, s))
      else
        Tau (itree_bind
             ((mrec h_prog (h_prog (p,s))):'a ptree)
             (λa.
                case a of
                  INL l => Ret (INR (SOME Error, s))
                | INR (res,s') =>
                    case res of
                      NONE => Tau (mrec h_prog (h_prog (While e p, s')))
                    | SOME Break => Ret (INR (NONE, s'))
                    | SOME Continue => Tau (mrec h_prog (h_prog (While e p, s')))
                    | _ => Ret (INR (res, s'))))
  | _ => Ret (INR (SOME Error, s))
Proof
  simp[SimpLHS,h_prog_def,h_prog_while_def]>>
  simp[Once itree_iter_thm]>>
  CASE_TAC>>fs[]>>
  rpt (CASE_TAC>>fs[])>>fs[mrec_bind]>>
  qpat_abbrev_tac ‘Y = mrec _ _’>>
  Cases_on ‘Y’>>simp[itree_bind_thm]
  >| [fs[markerTheory.Abbrev_def]>>
      pop_assum $ assume_tac o GSYM>>      
      imp_res_tac mrec_Ret_INR>>fs[],
      AP_TERM_TAC>>
      simp[FUN_EQ_THM]>>strip_tac,
      simp[FUN_EQ_THM]>>strip_tac>>
      AP_TERM_TAC>>
      simp[FUN_EQ_THM]>>strip_tac]>>
  rpt (CASE_TAC>>fs[])>>
  simp[GSYM h_prog_while_def,h_prog_def]
QED

(** move to itreeTauTheory **)
Theorem bind_FUNPOW_Ret':
  itree_bind ht k = FUNPOW Tau n (Ret x) ⇒ ∃r n'. ht = FUNPOW Tau n' (Ret r)
Proof
  Cases_on ‘∃t. strip_tau ht t’>>rw[]>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>rw[]>>fs[FUNPOW_Tau_bind]>>
      Cases_on ‘t’>>fs[itree_bind_thm]>>metis_tac[])>>
  imp_res_tac strip_tau_spin>>rw[]>>fs[spin_bind]>>
  pop_assum mp_tac>>
  rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>rw[]>>
  fs[Tau_INJ,FUNPOW_eq_elim]>>fs[Once spin]
QED

Theorem FUNPOW_Tau_Ret_eq_simp[simp]:
  FUNPOW Tau n (Ret x) = FUNPOW Tau m (Ret y) ⇔
    (n = m /\ x = y)
Proof
  EQ_TAC>>strip_tac>>fs[]>>
  Cases_on ‘n < m’>>fs[NOT_LESS]
  >- (fs[FUNPOW_min_cancel,Tau_INJ]>>
      Cases_on ‘m - n’>>fs[FUNPOW_SUC])>>
  last_x_assum $ assume_tac o GSYM>>
  rfs[FUNPOW_min_cancel,Tau_INJ]>>
  Cases_on ‘n - m’>>fs[FUNPOW_SUC]
QED

Theorem FUNPOW_Ret_strip:
  FUNPOW Tau n t = FUNPOW Tau m (Ret x) ⇒ n ≤ m ∧ t = FUNPOW Tau (m-n) (Ret x)
Proof
  strip_tac>>
  Cases_on ‘n ≤ m’>>fs[]
  >- (fs[LESS_OR_EQ]
      >- (fs[FUNPOW_min_cancel,Tau_INJ]>>metis_tac[])>>
      fs[FUNPOW_eq_elim]>>metis_tac[FUNPOW])>>
  fs[NOT_LESS_EQUAL]>>
  last_x_assum $ assume_tac o GSYM>>
  rfs[FUNPOW_min_cancel,Tau_INJ]>>
  Cases_on ‘n-m’>>fs[FUNPOW_SUC]
QED

Theorem bind_FUNPOW_Ret:
  itree_bind ht k = FUNPOW Tau n (Ret x) ⇒ ∃r n'. ht = FUNPOW Tau n' (Ret r) ∧ n' ≤ n
Proof
  rw[]>>
  imp_res_tac bind_FUNPOW_Ret'>>fs[FUNPOW_Tau_bind]>>
  imp_res_tac FUNPOW_Ret_strip
QED
(***)

Theorem mrec_FUNPOW_Ret_INR:
  (mrec h_prog (h_prog (p,s)):'a ptree) = FUNPOW Tau n (Ret x) ⇒ ∃y. x = INR y
Proof
  map_every qid_spec_tac [‘x’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’>>fs[]
  >- (imp_res_tac mrec_Ret_INR>>metis_tac[])>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘x’,‘s’,‘n’,‘p’]>>
  Induct>>rw[]
  >~[‘While’]>-
   (fs[Once mrec_While]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW]>>
    imp_res_tac FUNPOW_Ret_strip>>
    first_x_assum $ qspec_then ‘n' - SUC n''’ assume_tac>>fs[]>>
    res_tac>>fs[])
   >~[‘Dec’]>-
   (fs[h_prog_def,h_prog_dec_def,FUNPOW_SUC]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW])
   >~[‘Seq’]>-
   (fs[h_prog_def,h_prog_seq_def,FUNPOW_SUC]>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    TRY (imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW])>>
    imp_res_tac FUNPOW_Ret_strip>>fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW])
   >~[‘If’]>-
   (fs[h_prog_def,h_prog_cond_def,FUNPOW_SUC]>>
    fs[mrec_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[mrec_bind]
    >- (imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
        rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
        imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW])>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW])
   >~[‘Call’]>-
   (fs[h_prog_def,h_prog_call_def,FUNPOW_SUC]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    imp_res_tac FUNPOW_Ret_strip>>fs[mrec_bind]>>
    Cases_on ‘r'’>>fs[h_handle_call_ret_def]
    >- (Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])>>
    rename1 ‘INR y’>>Cases_on ‘y’>>
    rename1 ‘INR (q',r')’>>Cases_on ‘q'’>>fs[h_handle_call_ret_def]
    >- (Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])>>
    rename1 ‘INR (SOME x'',_)’>>Cases_on ‘x''’>>
    Cases_on ‘o'’>>fs[h_handle_call_ret_def]>>
    TRY (Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>gvs[]>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW])
   >~[‘DecCall’]>-
   (fs[h_prog_def,h_prog_deccall_def,FUNPOW_SUC]>>
    fs[mrec_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    imp_res_tac FUNPOW_Ret_strip>>fs[mrec_bind]>>
    Cases_on ‘r'’>>fs[h_handle_deccall_ret_def]
    >- (Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])>>
    rename1 ‘INR y’>>Cases_on ‘y’>>
    rename1 ‘INR (q',r')’>>Cases_on ‘q'’>>fs[h_handle_deccall_ret_def]
    >- (Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])>>
    rename1 ‘INR (SOME x'',_)’>>Cases_on ‘x''’>>fs[h_handle_deccall_ret_def]>>
    TRY (Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>gvs[]>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW]>>
    rpt (FULL_CASE_TAC>>fs[])>>fs[]>>
    imp_res_tac FUNPOW_Tau_Ret_eq>>gvs[GSYM FUNPOW]>>
    Cases_on ‘n'-n''’>>fs[FUNPOW_SUC]>>gvs[])
  >~[‘ExtCall’]>-
   (fs[h_prog_def,h_prog_ext_call_def,FUNPOW_SUC]>>
    fs[mrec_bind]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>fs[mrec_bind])>>
  fs[SF h_prog_ss,FUNPOW_SUC,h_prog_sh_mem_load_def,h_prog_sh_mem_store_def]>>
  rpt (FULL_CASE_TAC>>fs[])
QED

(***)

Theorem mrec_Skip_loop_spin:
  (mrec h_prog (h_prog (While (Const 1w) Skip, ^s)):'a ptree) = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY ({(mrec h_prog (h_prog (While (Const 1w) Skip, t)), spin)|T}
    ∪ {(Tau (mrec h_prog (h_prog (While (Const 1w) Skip, t))), spin)|T})’>>
  rw[]>- metis_tac[]
  >- fs[Once mrec_While,eval_def]
  >- (pop_assum mp_tac>>
      rewrite_tac[Once mrec_While,eval_def]>>
      fs[Once h_prog_def]>>strip_tac>>
      irule_at Any OR_INTRO_THM2>>
      gvs[]>>
      irule_at Any EQ_REFL>>
      irule_at (Pos last) (GSYM spin)>>fs[])
  >- (irule_at Any OR_INTRO_THM1>>
      irule_at Any EQ_REFL>>
      irule_at Any EQ_REFL>>
      irule spin)>>
  pop_assum mp_tac>>
  rewrite_tac[Once mrec_While,eval_def]>>
  simp[]
QED

Theorem Skip_loop_spin:
  itree_semantics (While (Const 1w) Skip, ^s) = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY ({(itree_semantics (While (Const 1w) Skip, t), spin)|T}
    ∪ {(Tau (itree_semantics (While (Const 1w) Skip, t)), spin)|T})’>>
  rw[]>- metis_tac[]
  >- (fs[itree_semantics_def,mrec_Skip_loop_spin]>>
      fs[Once itree_unfold,Once spin])
  >- (fs[itree_semantics_def,mrec_Skip_loop_spin]>>
      pop_assum mp_tac>>
      rewrite_tac[Once itree_unfold,Once spin]>>
      CASE_TAC>>fs[]>>strip_tac>>
      irule_at Any OR_INTRO_THM1>>
      irule_at (Pos last) (GSYM spin)>>fs[])
  >- (irule_at Any OR_INTRO_THM1>>
      irule_at Any EQ_REFL>>
      irule_at Any EQ_REFL>>
      irule spin)>>
  fs[itree_semantics_def,mrec_Skip_loop_spin]>>
  pop_assum mp_tac>>
  rewrite_tac[Once itree_unfold,Once spin]>>
  CASE_TAC>>fs[]
QED

