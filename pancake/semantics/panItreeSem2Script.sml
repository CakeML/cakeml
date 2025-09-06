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

Definition itree_evaluate_def:
  itree_evaluate (p:'a panLang$prog, ^s) =
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

(******)

Type ptree[pp] = “:((ffi_outcome + word8 list) + α result option # α bstate, ev,
     (ffi_outcome + word8 list) + α result option # α bstate) itree”;

Type rtree[pp] = “:((ffi_outcome + word8 list) + α result option # α bstate,
                    α panLang$prog # α bstate + ev,
     (ffi_outcome + word8 list) + α result option # α bstate) itree”;

Type fst[pp] = “:(ffiname -> β -> word8 list -> word8 list -> β oracle_result) # β”;


(******)

Theorem itree_unfold_FUNPOW_Tau:
  (∀u. f (Tau u) = Tau' u) ⇒
  itree_unfold f (FUNPOW Tau n t) = FUNPOW Tau n (itree_unfold f t)
Proof
  qid_spec_tac ‘n’>>Induct>>rw[FUNPOW_SUC]>>
  simp[Once itree_unfold]
QED

(***)

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
  bst s with memory := m = bst (s with memory := m) ∧
  bst (s with <|locals := x;clock :=k|>) = bst (s with locals := x) ∧
  bst (s with <|memory := m;clock :=k|>) = bst (s with memory := m) ∧
  bst (s with clock := k) = bst s
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

Theorem FUNPOW_Tau_Vis_eq_simp[simp]:
  FUNPOW Tau n (Vis e k) = FUNPOW Tau m (Vis e' k') ⇔
    (n = m /\ e = e' ∧ k = k')
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

Theorem FUNPOW_Ret_simp:
  (FUNPOW Tau n t = FUNPOW Tau m (Ret x)) ⇔ (n ≤ m ∧ t = FUNPOW Tau (m-n) (Ret x))
Proof
  EQ_TAC>>strip_tac
  >- (irule FUNPOW_Ret_strip>>simp[])>>
  fs[GSYM FUNPOW_ADD]
QED

Theorem FUNPOW_Vis_strip:
  FUNPOW Tau n t = FUNPOW Tau m (Vis e k) ⇒ n ≤ m ∧ t = FUNPOW Tau (m-n) (Vis e k)
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

Theorem FUNPOW_Vis_simp:
  (FUNPOW Tau n t = FUNPOW Tau m (Vis e k)) ⇔ (n ≤ m ∧ t = FUNPOW Tau (m-n) (Vis e k))
Proof
  EQ_TAC>>strip_tac
  >- (irule FUNPOW_Vis_strip>>simp[])>>
  fs[GSYM FUNPOW_ADD]
QED

Theorem bind_FUNPOW_Ret:
  itree_bind ht k = FUNPOW Tau n (Ret x) ⇒ ∃r n'. ht = FUNPOW Tau n' (Ret r) ∧ n' ≤ n
Proof
  rw[]>>
  imp_res_tac bind_FUNPOW_Ret'>>fs[FUNPOW_Tau_bind]>>
  imp_res_tac FUNPOW_Ret_strip
QED

Theorem bind_FUNPOW_Vis:
  itree_bind ht t = FUNPOW Tau n (Vis e k) ⇒
  (∃g. ht = FUNPOW Tau n (Vis e g) ∧ k = (λx. itree_bind (g x) t))
  ∨ (∃x m. ht = FUNPOW Tau m (Ret x) ∧ t x = FUNPOW Tau (n - m) (Vis e k)
           ∧ m ≤ n)
Proof
  Cases_on ‘∃t. strip_tau ht t’>>rw[]>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>rw[]>>fs[FUNPOW_Tau_bind]>>
      Cases_on ‘t'’>>fs[itree_bind_thm]>>
      fs[FUNPOW_Vis_simp])>>
  imp_res_tac strip_tau_spin>>rw[]>>fs[spin_bind]>>
  pop_assum mp_tac>>
  rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>rw[]>>
  fs[Tau_INJ,FUNPOW_eq_elim]>>fs[Once spin]
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
  itree_evaluate (While (Const 1w) Skip, ^s) = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY ({(itree_evaluate (While (Const 1w) Skip, t), spin)|T}
    ∪ {(Tau (itree_evaluate (While (Const 1w) Skip, t)), spin)|T})’>>
  rw[]>- metis_tac[]
  >- (fs[itree_evaluate_def,mrec_Skip_loop_spin]>>
      fs[Once itree_unfold,Once spin])
  >- (fs[itree_evaluate_def,mrec_Skip_loop_spin]>>
      pop_assum mp_tac>>
      rewrite_tac[Once itree_unfold,Once spin]>>
      CASE_TAC>>fs[]>>strip_tac>>
      irule_at Any OR_INTRO_THM1>>
      irule_at (Pos last) (GSYM spin)>>fs[])
  >- (irule_at Any OR_INTRO_THM1>>
      irule_at Any EQ_REFL>>
      irule_at Any EQ_REFL>>
      irule spin)>>
  fs[itree_evaluate_def,mrec_Skip_loop_spin]>>
  pop_assum mp_tac>>
  rewrite_tac[Once itree_unfold,Once spin]>>
  CASE_TAC>>fs[]
QED

(*** simp rules ***)

Theorem mrec_Seq:
  (mrec h_prog (h_prog (Seq p q, s)):'a ptree) =
  Tau (itree_bind
       (mrec h_prog (h_prog (p, s)):'a ptree)
       (λa. case a of
              INL l => Ret (INR (SOME Error, s))
            | INR (NONE,s') =>
                Tau (itree_bind (mrec h_prog (h_prog (q, s')):'a ptree)
                                (λa.
                                   Ret (INR
                                   (case a of
                                      INL v => (SOME Error,s)
                                    | INR (res,s') => (res,s')))))
            | INR (SOME res, s') => Ret (INR (SOME res, s'))))
Proof
  simp[h_prog_seq_def,h_prog_def,mrec_bind]>>
  AP_TERM_TAC>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])>>fs[mrec_bind]>>
  simp[o_DEF]>>
  AP_TERM_TAC>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_Dec:
  (mrec h_prog (h_prog (Dec x e p, s)):'a ptree) =
  case eval s e of
    SOME v =>
      Tau (itree_bind
           (mrec h_prog (h_prog (p,s with locals := s.locals |+ (x,v))):'a ptree)
           (λa. Ret (INR (case a of
                            INL l => (SOME Error, s)
                          | INR (res,s') =>
                              (res, s' with
                     locals := res_var s'.locals (x,FLOOKUP s.locals x))))))
  | _ => Ret (INR (SOME Error, s))
Proof
  simp[h_prog_dec_def,h_prog_def,mrec_bind]>>
  rpt (CASE_TAC>>fs[])>>fs[mrec_bind]>>
  AP_TERM_TAC>>fs[o_DEF]>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])>>fs[mrec_bind]
QED

Theorem mrec_Assign:
  (mrec h_prog (h_prog (Assign x v, s)):'a ptree) =
  case eval s v of
    SOME v =>
      Ret (INR (if is_valid_value s.locals x v then
                  (NONE, s with locals := s.locals |+ (x,v))
                else (SOME Error, s)))
  | _ => Ret (INR (SOME Error, s))
Proof
  simp[h_prog_assign_def,h_prog_def,mrec_bind]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_If:
  (mrec h_prog (h_prog (If e p q, s)):'a ptree) =
  case eval s e of
    SOME (ValWord v) =>
      Tau (itree_bind (mrec h_prog (h_prog (if v ≠ 0w then p else q,s)):'a ptree)
                      (λa. Ret (INR (case a of
                                       INL l => (SOME Error,s)
                                     | INR (res,s') => (res,s')))))
  | _ => Ret (INR (SOME Error, s))
Proof
  simp[h_prog_cond_def,h_prog_def,mrec_bind]>>
  rpt (CASE_TAC>>fs[mrec_bind])>>simp[o_DEF]>>
  AP_TERM_TAC>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_Store:
  (mrec h_prog (h_prog (Store dst src, s)):'a ptree) =
  Ret (INR (case (eval s dst, eval s src) of
    (NONE, v3) => (SOME Error, s)
  | (SOME (ValWord ad), NONE) => (SOME Error, s)
  | (SOME (ValWord ad), SOME v) =>
      (case mem_stores ad (flatten v) s.memaddrs s.memory of
         NONE => (SOME Error, s)
       | SOME m => (NONE, s with memory := m))
  | _ => (SOME Error, s)))
Proof
  simp[h_prog_store_def,h_prog_def,mrec_bind]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_StoreByte:
  (mrec h_prog (h_prog (StoreByte dst src, s)):'a ptree) =
  Ret (INR (case (eval s dst, eval s src) of
              (NONE, v3) => (SOME Error, s)
            | (SOME (ValWord ad), NONE) => (SOME Error, s)
            | (SOME (ValWord ad), SOME (ValWord v)) =>
                (case mem_store_byte s.memory s.memaddrs s.be ad (w2w v) of
                   NONE => (SOME Error, s)
                 | SOME m => (NONE, s with memory := m))
            | _ => (SOME Error, s)))
Proof
  simp[h_prog_store_byte_def,h_prog_def,mrec_bind]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_Store32:
  (mrec h_prog (h_prog (Store32 dst src, s)):'a ptree) =
  Ret (INR (case (eval s dst, eval s src) of
              (NONE, v3) => (SOME Error, s)
            | (SOME (ValWord ad), NONE) => (SOME Error, s)
            | (SOME (ValWord ad), SOME (ValWord v)) =>
                (case mem_store_32 s.memory s.memaddrs s.be ad (w2w v) of
                   NONE => (SOME Error, s)
                 | SOME m => (NONE, s with memory := m))
            | _ => (SOME Error, s)))
Proof
  simp[h_prog_store_32_def,h_prog_def,mrec_bind]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_ShMemLoad:
  (mrec h_prog (h_prog (ShMemLoad op v addr, s)):'a ptree) =
  case (eval s addr, FLOOKUP s.locals v) of
    (SOME (ValWord ad), SOME (Val _)) =>
      (if nb_op op = 0 then
         (if ad ∈ s.sh_memaddrs then
            Vis (SharedMem MappedRead,[0w],word_to_bytes ad F)
                (Tau o mrec h_prog o
                     (λres.
                        Ret
                        (INR
                         (case res of
                            INL (INL outcome) =>
                              (SOME
                               (FinalFFI
                                (Final_event (SharedMem MappedRead) [0w]
                                             (word_to_bytes ad F) outcome)),
                               empty_locals s)
                          | INL (INR new_bytes) =>
                              if LENGTH new_bytes = dimindex (:α) DIV 8 then
                                (NONE,
                                 set_var v
                                         (ValWord (word_of_bytes F 0w new_bytes)) s)
                              else
                                (SOME
                                 (FinalFFI
                                  (Final_event (SharedMem MappedRead) [0w]
                                               (word_to_bytes ad F) FFI_failed)),
                                 empty_locals s)
                          | INR _ => (SOME Error,s)))))
          else Ret (INR (SOME Error,s)))
       else if byte_align ad ∈ s.sh_memaddrs then
         Vis (SharedMem MappedRead,[n2w (nb_op op)],word_to_bytes ad F)
             (Tau o mrec h_prog o
                  (λres.
                     Ret
                     (INR
                      (case res of
                         INL (INL outcome) =>
                           (SOME
                            (FinalFFI
                             (Final_event (SharedMem MappedRead)
                                          [n2w (nb_op op)] (word_to_bytes ad F)
                                          outcome)),empty_locals s)
                       | INL (INR new_bytes) =>
                           if LENGTH new_bytes = dimindex (:α) DIV 8 then
                             (NONE,
                              set_var v
                                      (ValWord (word_of_bytes F 0w new_bytes)) s)
                           else
                             (SOME
                              (FinalFFI
                               (Final_event (SharedMem MappedRead)
                                            [n2w (nb_op op)] (word_to_bytes ad F)
                                            FFI_failed)),empty_locals s)
                       | INR _ => (SOME Error,s)))))
       else Ret (INR (SOME Error,s)))
  | _ => Ret (INR (SOME Error, s))
Proof
  simp[h_prog_sh_mem_load_def,h_prog_def,mrec_bind]>>
  rpt (TOP_CASE_TAC>>fs[])
QED

Theorem mrec_ShMemStore:
  (mrec h_prog (h_prog (ShMemStore op addr e, s)):'a ptree) =
  case (eval s addr, eval s e) of
    (SOME (ValWord ad), SOME (ValWord w)) =>
      if nb_op op = 0 then
        if ad ∈ s.sh_memaddrs then
          Vis
          (SharedMem MappedWrite,[0w],word_to_bytes w F ++ word_to_bytes ad F)
          (Tau ∘ mrec h_prog ∘
               (λres.
                  Ret
                  (INR
                   (case res of
                      INL (INL outcome) =>
                        (SOME
                         (FinalFFI
                          (Final_event (SharedMem MappedWrite) [0w]
                                       (word_to_bytes w F ++ word_to_bytes ad F)
                                       outcome)),s)
                    | INL (INR new_bytes) =>
                        if LENGTH new_bytes = 2 * (dimindex (:α) DIV 8) then
                          (NONE,s)
                        else
                          (SOME
                           (FinalFFI
                            (Final_event (SharedMem MappedWrite) [0w]
                                         (word_to_bytes w F ++ word_to_bytes ad F)
                                         FFI_failed)),s)
                    | INR _ => (SOME Error,s)))))
        else Ret (INR (SOME Error,s))
      else if byte_align ad ∈ s.sh_memaddrs then
        Vis (SharedMem MappedWrite,[n2w (nb_op op)],
             TAKE (nb_op op) (word_to_bytes w F) ++ word_to_bytes ad F)
            (Tau ∘ mrec h_prog ∘
                 (λres.
                    Ret
                    (INR
                     (case res of
                        INL (INL outcome) =>
                          (SOME
                           (FinalFFI
                            (Final_event (SharedMem MappedWrite)
                                         [n2w (nb_op op)]
                                         (TAKE (nb_op op) (word_to_bytes w F) ++
                                          word_to_bytes ad F) outcome)),s)
                      | INL (INR new_bytes) =>
                          if
                          LENGTH new_bytes =
                          LENGTH (TAKE (nb_op op) (word_to_bytes w F)) +
                          dimindex (:α) DIV 8
                          then
                            (NONE,s)
                          else
                            (SOME
                             (FinalFFI
                              (Final_event (SharedMem MappedWrite)
                                           [n2w (nb_op op)]
                                           (TAKE (nb_op op) (word_to_bytes w F) ++
                                            word_to_bytes ad F) FFI_failed)),s)
                      | INR v1 => (SOME Error,s)))))
      else Ret (INR (SOME Error,s))
  | _ => Ret (INR (SOME Error,s))
Proof
  simp[h_prog_sh_mem_store_def,h_prog_def,mrec_bind]>>
  rpt (TOP_CASE_TAC>>fs[])
QED

Theorem mrec_prog_triv:
  mrec h_prog (h_prog (Skip,s)) = Ret (INR (NONE,s)) ∧
  mrec h_prog (h_prog (Break,s)) = Ret (INR (SOME Break,s)) ∧
  mrec h_prog (h_prog (Tick,s)) = Ret (INR (NONE,s)) ∧
  mrec h_prog (h_prog (Annot x y,s)) = Ret (INR (NONE,s)) ∧
  mrec h_prog (h_prog (Continue,s)) = Ret (INR (SOME Continue,s))
Proof
  simp[h_prog_def]
QED

Theorem mrec_Return:
  mrec h_prog (h_prog (Return e,s)) =
  Ret (INR (case eval s e of
              NONE => (SOME Error,s)
            | SOME v =>
                if size_of_shape (shape_of v) ≤ 32 then
                  (SOME (Return v), empty_locals s)
                else (SOME Error,s)))
Proof
  simp[mrec_simps,h_prog_def,h_prog_return_def]
QED

Theorem mrec_Raise:
  mrec h_prog (h_prog (Raise eid e,s)) =
  Ret (INR (case (FLOOKUP s.eshapes eid, eval s e) of
            | (SOME sh, SOME v) =>
                if shape_of v = sh ∧ size_of_shape (shape_of v) ≤ 32 then
                  (SOME (Exception eid v), empty_locals s)
                else (SOME Error,s)
            | _ => (SOME Error,s)))
Proof
  simp[mrec_simps,h_prog_def,h_prog_raise_def]
QED

val mrec_prog_simps =
  LIST_CONJ [mrec_prog_triv,mrec_Return,mrec_Raise,mrec_Dec,mrec_Assign,
             mrec_Store,mrec_Store32,mrec_StoreByte];

Theorem mrec_Call:
 (mrec h_prog (h_prog (Call typ texp aexps,s)):'a ptree) =
   (case eval s texp of
      | SOME (ValLabel fname) =>
        (case OPT_MMAP (eval s) aexps of
           NONE => Ret (INR (SOME Error,s))
         | SOME args =>
           case lookup_code s.code fname args of
             NONE => Ret (INR (SOME Error,s))
           | SOME (q,r) =>
               Tau
               (itree_bind (mrec h_prog (h_prog (q,s with locals := r)):'a ptree)
                           (mrec h_prog o (h_handle_call_ret typ s)))
           | _ => Ret (INR (SOME Error,s)))
      | _ => Ret (INR (SOME Error,s)))
Proof
  simp[h_prog_def,h_prog_call_def,mrec_simps]>>
  rpt (CASE_TAC>>fs[])>>simp[mrec_bind]
QED

Theorem mrec_DecCall:
  mrec h_prog (h_prog (DecCall rt sh texp aexps prog,s)):'a ptree =
   (case eval s texp of
      | SOME (ValLabel fname) =>
        (case OPT_MMAP (eval s) aexps of
           NONE => Ret (INR (SOME Error,s))
         | SOME args =>
           case lookup_code s.code fname args of
             NONE => Ret (INR (SOME Error,s))
           | SOME (q,r) =>
               Tau
               (itree_bind (mrec h_prog (h_prog (q,s with locals := r)):'a ptree)
                           (mrec h_prog o (h_handle_deccall_ret rt sh prog s))))
      | _ => Ret (INR (SOME Error,s)))

Proof
  simp[h_prog_def,h_prog_deccall_def,mrec_simps]>>
  rpt (CASE_TAC>>fs[])>>simp[mrec_bind]
QED

Theorem mrec_h_handle_call_ret_lemma:
  mrec h_prog (h_handle_call_ret ct s res) :'a ptree =
  case res of
  | INR (NONE,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Break,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Continue,s') => Ret (INR (SOME Error,s'))
  | INR (SOME (Exception eid exn),s') =>
      (case ct of
         SOME (_, SOME (eid', evar, p)) =>
           (if eid' = eid
            then
              (case FLOOKUP s.eshapes eid of
                 SOME sh =>
                   (if shape_of exn = sh ∧ is_valid_value s.locals evar exn
                    then Tau (itree_bind
                              (mrec h_prog (h_prog (p,set_var evar exn (s' with locals := s.locals))):'a ptree)
                              (mrec h_prog o (λa. Ret (INR
                                                      (case a of
                                                         INL _ => (SOME Error,s')
                                                       | INR (q,t) => (q,t))))))
                    else Ret (INR (SOME Error,s')))
               | NONE => Ret (INR (SOME Error,s')))
            else Ret (INR (SOME (Exception eid exn),empty_locals s')))
       | _ => Ret (INR (SOME (Exception eid exn),empty_locals s')))
  | INR (SOME (Return retv), s') =>
      (case ct of
         NONE => Ret (INR (SOME (Return retv),empty_locals s'))
       | SOME (NONE, _) => Ret (INR (NONE, s' with locals := s.locals))
       | SOME (SOME rt, _) =>
              if is_valid_value s.locals rt retv
              then Ret (INR (NONE,set_var rt retv (s' with locals := s.locals)))
              else Ret (INR (SOME Error,s')))
  | INR (res,s') => Ret (INR (res,empty_locals s'))
  | INL _ => Ret (INR (SOME Error,s)):'a ptree
Proof
  simp[oneline h_handle_call_ret_def]>>
  rpt (CASE_TAC>>fs[mrec_bind])
QED

Theorem mrec_h_handle_deccall_ret_lemma:
  mrec h_prog (h_handle_deccall_ret rt sh p s res) :'a ptree =
  case res of
  | INR (NONE,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Break,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Continue,s') => Ret (INR (SOME Error,s'))
  | INR (SOME (Return retv), s') =>
      (if shape_of retv = sh then
         Tau
         (itree_bind
          (mrec h_prog (h_prog (p,set_var rt retv (s' with locals := s.locals))):'a ptree)
          (mrec h_prog o
                (λa. Ret
                     (INR
                      (case a of
                         INL v => (SOME Error,s')
                       | INR (q,r') =>
                           (q, r' with locals := res_var r'.locals (rt, FLOOKUP s.locals rt)))))))
       else Ret (INR (SOME Error, s')))
  | INR (res,s') => Ret (INR (res,empty_locals s'))
  | INL _ => Ret (INR (SOME Error,s)):'a ptree
Proof
  simp[oneline h_handle_deccall_ret_def]>>
  rpt (CASE_TAC>>fs[mrec_bind])
QED

Theorem mrec_ExtCall:
  mrec h_prog (h_prog (ExtCall ffiname cptr clen aptr alen, s)) =
  case (eval s alen, eval s aptr, eval s clen, eval s cptr) of
    (SOME (ValWord c), SOME (ValWord c'), SOME (ValWord c2), SOME (ValWord c3)) =>
      (case read_bytearray c' (w2n c) (mem_load_byte s.memory s.memaddrs s.be) of
         SOME x =>
           (case read_bytearray c3 (w2n c2) (mem_load_byte s.memory s.memaddrs s.be) of
              SOME x' =>
                if explode ffiname ≠ ""
                then
                   Vis (ExtCall (explode ffiname),x',x)
                      (Tau o mrec h_prog o
                           (λres.
                              (Ret
                               (INR
                                (case res of
                                   INL (INL outcome) =>
                                     (SOME
                                      (FinalFFI
                                       (Final_event (ExtCall (explode ffiname)) x' x outcome)),empty_locals s)
                                 | INL (INR new_bytes) =>
                                     if LENGTH new_bytes = LENGTH x then
                                       (NONE,
                                        s with
                                          memory :=
                                        write_bytearray c' new_bytes s.memory
                                                        s.memaddrs s.be)
                                     else
                                       (SOME
                                        (FinalFFI
                                         (Final_event (ExtCall (explode ffiname)) x' x FFI_failed)),empty_locals s)
                                 | INR _ => (SOME Error,s))))))
                else Ret (INR (NONE, s with memory := write_bytearray c' x s.memory s.memaddrs s.be))
            | _ => Ret (INR (SOME Error,s)))
       | _ => Ret (INR (SOME Error,s)))
  | _ => Ret (INR (SOME Error,s))
Proof
  simp[h_prog_def,h_prog_ext_call_def,mrec_simps]>>
  rpt (PURE_CASE_TAC>>fs[])>>simp[mrec_bind]
QED

val mrec_prog_nonrec =
  LIST_CONJ [mrec_prog_simps,mrec_ShMemStore,mrec_ShMemLoad,mrec_Seq,
            mrec_Call,mrec_DecCall];


(*** retry ***)

Definition ltree_def:
  (ltree (fs:'b fst) (t:'a ptree)) =
  itree_iter
  (λ(t,st).
     case t of
       Ret r => Ret (INR r)
     | Tau u => Ret (INL (u,st))
     | Vis (s,c,ws) g =>
         (case (FST fs) s st c ws of
            Oracle_return fs' ws' => Ret (INL (g (INL (INR ws')), fs'))
(*          | Oracle_final outcome => Ret (INL (g (INL (INR ws)), st))))*)
          | Oracle_final outcome => Ret (INL (g (INL (INL outcome)), st))))
  (t,SND fs)
End

Theorem ltree_simps[simp]:
  (ltree fs (Ret r) = Ret r) ∧
  (ltree fs (Tau u) = Tau (ltree fs u)) ∧
  (ltree fs (Vis (s,c,ws) g) =
         (case (FST fs) s (SND fs) c ws of
            Oracle_return fs' ws' =>
              Tau (ltree (FST fs,fs') (g (INL (INR ws'))))
          | Oracle_final outcome =>
              Tau (ltree fs (g (INL (INL outcome))))))
Proof
  rw[]>>simp[ltree_def,Once itree_iter_thm]>>
  CASE_TAC>>simp[itree_bind_thm]>>
  simp[Once ltree_def]
QED

Theorem ltree_FUNPOW_Tau[simp]:
  ltree fs (FUNPOW Tau n t) = FUNPOW Tau n (ltree fs t)
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]
QED

Theorem ltree_not_Vis[simp]:
  ∀n e k. ltree fs t ≠ FUNPOW Tau n (Vis e k)
Proof
  qid_spec_tac ‘t’>>simp[Once SWAP_FORALL_THM]>>
  qid_spec_tac ‘fs’>>simp[Once SWAP_FORALL_THM]>>
  Induct>>rw[]
  >- (Cases_on ‘t’>>fs[]>>
      PairCases_on ‘a’>>simp[]>>
      CASE_TAC>>simp[])>>
  Cases_on ‘t’>>fs[FUNPOW_SUC]>>
  PairCases_on ‘a’>>simp[]>>
  CASE_TAC>>simp[]
QED

(***)

Definition comp_ffi_def:
  comp_ffi fs (t:'a ptree) =
  WHILE
    (λ(t,st). case t of Ret _ => F | _ => T)
    (λ(t,st).
        case t of
        | Ret _ => (t,st)
        | Tau t => (t,st)
        | Vis (s,c,ws) g =>
            case (FST fs) s st c ws of
              Oracle_return fs' ws' => (g (INL (INR ws')), fs')
            | Oracle_final outcome => (g (INL (INL outcome)), st)
    )
    (t,SND fs)
End

Theorem comp_ffi_simps[simp]:
  comp_ffi fs (Ret r) = (Ret r, SND fs) ∧
  comp_ffi fs (Tau t) = comp_ffi fs t ∧
  comp_ffi fs (Vis (s,c,ws) g) =
  case (FST fs) s (SND fs) c ws of
    Oracle_return fs' ws' => comp_ffi (FST fs,fs') (g (INL (INR ws')))
  | Oracle_final outcome => comp_ffi fs (g (INL (INL outcome)))
Proof
  rw[comp_ffi_def]>>simp[Once whileTheory.WHILE] >>
  rw[ELIM_UNCURRY] >>
  PURE_TOP_CASE_TAC >> rw[]
QED        

Theorem comp_ffi_FUNPOW_Tau[simp]:
comp_ffi fs (FUNPOW Tau n t) = comp_ffi fs t
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]
QED

Theorem ltree_bind[simp]:
  ltree (fs:'b fst) (itree_bind t k) =
  itree_bind (ltree fs t) (ltree (FST fs,SND (comp_ffi fs t)) o k)
Proof
  simp[Once itree_strong_bisimulation] >>
  qexists ‘CURRY {(ltree (fs:'b fst) (itree_bind t k),
                   itree_bind (ltree fs t) (ltree (FST fs, SND (comp_ffi fs t)) o k))|T}’ >>
  rw[EXISTS_PROD]>-metis_tac[PAIR]>>
  rename [‘ltree _ (itree_bind t _)’]
  >- (Cases_on ‘t’>>fs[itree_bind_thm]>>
      PairCases_on ‘a’>>simp[]>>
      CASE_TAC>>fs[])
  >- (Cases_on ‘t’ >>fs[itree_bind_thm]
      >- metis_tac[]
      >- metis_tac[]>>
      PairCases_on ‘a’>>fs[]>>
      CASE_TAC>>fs[]>>
      metis_tac[])>>
  Cases_on ‘t’ >>fs[itree_bind_thm]
  >- metis_tac[]>>
  PairCases_on ‘a'’>>fs[]>>
  CASE_TAC>>fs[]
QED

(***************************)

Definition div_def:
  div (fs:'b fst) t =
  ∀n r. ltree fs t ≠ FUNPOW Tau n (Ret r):'a ptree
End

Theorem div_FUNPOW_Tau[simp]:
  div fs (FUNPOW Tau n X) = div fs X
Proof
  eq_tac>>
  Cases_on ‘fs’>>rw[div_def]
  >- (first_x_assum $ qspecl_then [‘n+n'’,‘r'’] assume_tac>>
      fs[FUNPOW_ADD,FUNPOW_eq_elim])>>
  strip_tac>>
  fs[FUNPOW_Ret_simp]
QED

Theorem ltree_div_bind[simp]:
  div fs X ⇒
  ltree fs (itree_bind X k) = ltree fs X:'a ptree
Proof
  strip_tac>>
  irule EQ_SYM>>
  rewrite_tac[Once itree_bisimulation]>>
  qexists ‘CURRY {(ltree fs X, ltree fs (itree_bind X k):'a ptree) | div fs X}’ >>
  fs[div_def]>>rw[EXISTS_PROD]>- metis_tac[PAIR]
  >- metis_tac[FUNPOW]
  >- (rename1 ‘ltree _ t’>>
      Cases_on ‘t’>>fs[]>>
      TRY (PairCases_on ‘a’>>fs[])>>
      rpt (CASE_TAC>>fs[])>>
      irule_at Any EQ_REFL>>
      irule_at Any EQ_REFL>>
      rpt strip_tac>>fs[GSYM FUNPOW_SUC])>>
  rename1 ‘ltree _ t’>>
  Cases_on ‘t’>>fs[]>>
  PairCases_on ‘a'’>>fs[]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem div_bind1[simp]:
  div fs (X:'a ptree) ⇒ div fs (itree_bind X Y)
Proof
  rw[div_def]
QED

Theorem nondiv_eq_Ret[simp]:
  (¬ div fs X) = (∃n r. ltree fs X = FUNPOW Tau n (Ret r):'a ptree)
Proof
  simp[div_def]>>metis_tac[]
QED

Theorem div_bind2[simp]:
  ltree fs X = FUNPOW Tau n (Ret r):'a ptree ⇒
  div fs (itree_bind X Y) = div (FST fs, SND (comp_ffi fs X)) (Y r)
Proof
  rw[]>>
  simp[]>>eq_tac>>rw[div_def]>>gs[FUNPOW_Tau_bind]>>
  strip_tac>>fs[]
  >- metis_tac[FUNPOW_ADD]>>
  fs[FUNPOW_Ret_simp]
QED

Theorem div_Tau[simp]:
  div fs (Tau u) = div fs u
Proof
  simp[div_def]>>
  EQ_TAC>>rpt strip_tac>>fs[]
  >- fs[GSYM FUNPOW_SUC]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]
QED

Theorem div_Ret[simp]:
  div fs (Ret r) = F
Proof
  simp[div_def]>>metis_tac[FUNPOW]
QED

Theorem div_imp_spin:
  div fs t ⇒ ltree fs t = spin:'a ptree
Proof
  rw[]>>
  irule EQ_SYM>>
  simp[Once itree_bisimulation] >>
  qexists ‘CURRY {(spin,ltree fs t)|fs,t| div fs t}’>>
  rw[EXISTS_PROD]>- metis_tac[PAIR]>>
  TRY (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin]>>NO_TAC)>>
  last_x_assum kall_tac>>
  rename1 ‘ltree fs t’ >>
  Cases_on ‘t’ >>fs[]
  >- (qpat_x_assum ‘_ = spin’ mp_tac>>simp[Once spin]>>rw[]>>
      Cases_on ‘fs’>>fs[]>>
      first_x_assum $ irule_at Any>>simp[])>>
  PairCases_on ‘a’>>fs[]>>
  CASE_TAC>>fs[]>>
  qpat_x_assum ‘_ = spin’ mp_tac>>simp[Once spin]>>
  Cases_on ‘fs’>>fs[div_def]>>
  metis_tac[FUNPOW_SUC]
QED

(**************************)

Theorem nondiv_INR:
  ltree fs (mrec h_prog (h_prog (p,s))) = FUNPOW Tau n (Ret r): 'a ptree ⇒
  ∃x. r = INR x
Proof
  map_every qid_spec_tac [‘r’,‘fs’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>fs[]>>
  Cases_on ‘n’>>rw[]
  >- (rpt (pop_assum mp_tac)>>
      map_every qid_spec_tac [‘r’,‘fs’,‘s’,‘p’]>>
      Induct>>
      rw[mrec_prog_simps,mrec_If,Once mrec_While,mrec_Call,mrec_DecCall,
         mrec_Seq]>>
      TRY (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>NO_TAC)>>
      fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>
      gvs[]>>
      FULL_CASE_TAC>>fs[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>rename1 ‘FUNPOW Tau n _’>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>rename1 ‘FUNPOW Tau n _’>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘r’,‘fs’,‘s’,‘p’]>>
  rename1 ‘SUC n’>>fs[FUNPOW_SUC]>>
  Induct>>
  rw[mrec_prog_simps]>>
  TRY (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>NO_TAC)
  >~ [‘ExtCall’]>-
   (fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])
  >~ [‘ShMemLoad’]>-
   (fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])
  >~ [‘ShMemStore’]>-
   (fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])
  (* Dec *) >-
   (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>gvs[])
  >~ [‘Seq’] >-
   (fs[mrec_Seq]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[GSYM FUNPOW]>>
    fs[FUNPOW_Ret_simp]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ Y) _’>>
    Cases_on ‘div (FST fs, SND (comp_ffi fs X)) Y’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>gvs[])
  >~ [‘If’] >-
   (fs[mrec_If]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]>>
    fs[FUNPOW_Tau_bind]>>gvs[]>>
    imp_res_tac div_imp_spin>>fs[spin_bind]
    >- (qhdtm_x_assum ‘FUNPOW’ mp_tac>>  (* ??? *)
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    qhdtm_x_assum ‘FUNPOW’ mp_tac>>
    rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
    rw[]>>fs[FUNPOW_Ret_simp])
  >~ [‘While’] >-
   (fs[Once mrec_While]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    fs[GSYM FUNPOW]>>
    fs[FUNPOW_Ret_simp]>>
    ‘n - SUC n' < SUC n’ by simp[]>>
    res_tac>>gvs[])
  (* Call / DecCall *)
  >- (fs[mrec_Call,mrec_DecCall]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
      (Cases_on ‘div fs X’>>fs[]
       >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
           qhdtm_x_assum ‘FUNPOW’ mp_tac>>
           rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
           rw[]>>fs[FUNPOW_Ret_simp]))>>
      fs[FUNPOW_Tau_bind]>>
      fs[mrec_h_handle_call_ret_lemma]>>
      fs[mrec_h_handle_deccall_ret_lemma]>>
      (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      fs[GSYM FUNPOW]>>
      fs[FUNPOW_Ret_simp]>>
      qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ Y) _’>>
      Cases_on ‘div (FST fs, SND (comp_ffi fs X)) Y’>>fs[]>>
      fs[FUNPOW_Tau_bind]>>gvs[]>>
      imp_res_tac div_imp_spin>>fs[spin_bind]
       >- (qhdtm_x_assum ‘FUNPOW’ mp_tac>>
           rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
           rw[]>>fs[FUNPOW_Ret_simp]))>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
      rw[]>>fs[FUNPOW_Ret_simp])>>
  (fs[mrec_Call,mrec_DecCall]>>
   rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
   qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
   (Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp]))>>
   fs[FUNPOW_Tau_bind]>>
   fs[mrec_h_handle_call_ret_lemma]>>
   fs[mrec_h_handle_deccall_ret_lemma]>>
   (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
   fs[GSYM FUNPOW]>>
   fs[FUNPOW_Ret_simp]>>
   qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ Y) _’>>
   Cases_on ‘div (FST fs, SND (comp_ffi fs X)) Y’>>fs[]>>
   fs[FUNPOW_Tau_bind]>>gvs[]>>
   (imp_res_tac div_imp_spin>>fs[spin_bind]
    >- (qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])))>>
   qhdtm_x_assum ‘FUNPOW’ mp_tac>>
   rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
   rw[]>>fs[FUNPOW_Ret_simp])
QED

Theorem test:
  ltree fs t = FUNPOW Tau n (Ret r) ⇒
  comp_ffi fs t = (X,

Theorem comp_ffi_bind_div[simp]:
  div fs t ⇒
  comp_ffi fs (itree_bind t k) = comp_ffi fs t
Proof
  simp[div_def]>>
  simp[Once (GSYM CONTRAPOS_THM)]>>rw[]>>
  CCONTR_TAC>>fs[]>>
  map_every qid_spec_tac [‘t’,‘fs’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>
  Cases_on ‘t’>>fs[]>>
  PairCases_on ‘a’>>fs[]>>
  CASE_TAC>>fs[]
QED

Theorem comp_ffi_bind[simp]:
  ltree fs t = FUNPOW Tau n (Ret r) ⇒
  comp_ffi fs (itree_bind t k) =
  comp_ffi (FST fs, SND (comp_ffi fs t)) (k r)
Proof
  map_every qid_spec_tac [‘t’,‘fs’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>
  Cases_on ‘t’>>fs[]>>
  PairCases_on ‘a’>>fs[]>>
  CASE_TAC>>fs[]
QED

Theorem comp_ffi_evaluate[simp]:
  evaluate (p,s) = (res,t) ⇒
  SND (comp_ffi (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s)))) = t.ffi.ffi_state
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac >> simp[]>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>



  >~ [‘ExtCall’]>- cheat>>
  rpt (CASE_TAC>>fs[])>>rw[]
  simp[mrec_prog_simps]


  simp[mrec_Dec]>>
  rpt (CASE_TAC>>fs[])>>rw[]>>
  rpt (pairarg_tac>>fs[])>>

  gvs[res_var_def]



QED


Theorem evaluate_mrec_Ret_corres:
  evaluate (p, s) = (res,t) ∧ res ≠ SOME TimeOut ⇒
        ∃n. ltree (s.ffi.oracle, s.ffi.ffi_state)
                  (mrec h_prog (h_prog (p, bst s))) =
            FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac >> simp[]>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>rw[]
  >~[‘ShMemLoad’]>-
   (simp[mrec_ShMemLoad]>>
    rpt (CASE_TAC>>fs[])>>
    fs[call_FFI_def,set_var_defs,empty_locals_defs]>>
    gvs[bst_def]>>metis_tac[FUNPOW])
  >~[‘ShMemStore’]>-
   (simp[mrec_ShMemStore]>>
    rpt (CASE_TAC>>fs[])>>gvs[]>>rw[]>>
    fs[call_FFI_def,set_var_defs,empty_locals_defs]>>
    gvs[bst_def]>>metis_tac[FUNPOW])
  >~[‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    fs[call_FFI_def,set_var_defs,empty_locals_defs]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[bst_def]>>
    metis_tac[FUNPOW])
  >~[‘Dec’]>-
   (fs[mrec_Dec]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])
    >- metis_tac[FUNPOW]>>
    gvs[FUNPOW_Tau_bind]>>
    metis_tac[FUNPOW_SUC])
  >~[‘If’]>-
   (fs[mrec_If]>>
    rpt (CASE_TAC>>fs[])
    >>~- ([‘res = SOME Error’],metis_tac[FUNPOW])>>
    gvs[FUNPOW_Tau_bind]>>
    metis_tac[FUNPOW_SUC])
  >~[‘While’]>-
   (simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[])
    >>~- ([‘res = SOME Error’],metis_tac[FUNPOW])>>
    TRY (qexists ‘0’>>simp[FUNPOW]>>NO_TAC)>>

    pairarg_tac>>fs[]>>
    Cases_on ‘s.clock=0’>>fs[dec_clock_def]

    >- (qpat_x_assum ‘_ = (NONE,t)’ mp_tac>>
        rpt (CASE_TAC>>fs[])>>
(*NONE*)
        simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC,GSYM FUNPOW]>>
        simp[Once evaluate_def]>>
        rpt (CASE_TAC>>fs[])>>rw[]>>gs[]>>

        rpt (FULL_CASE_TAC>>fs[])>>simp[comp_ffi_def]>>
        simp[R


        first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k-1’] assume_tac>>
        rw[]>>imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        gvs[IS_PREFIX_ANTISYM]>>simp[FUNPOW_Tau_bind]
        >~ [‘Break’]>- (gvs[]>>metis_tac[GSYM FUNPOW_SUC])>>
        qpat_x_assum ‘evaluate (While _ _,_)=_’ mp_tac>>
        simp[Once evaluate_def]>>
        rpt (CASE_TAC>>fs[])>>rw[]>>
        TRY (pairarg_tac>>fs[])>>
        rpt (FULL_CASE_TAC>>fs[])>>
        first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
        rfs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW_SUC,GSYM FUNPOW]>>
        metis_tac[GSYM FUNPOW_ADD])>>
    qpat_x_assum ‘_ = (SOME _,t)’ mp_tac>>
    rpt (CASE_TAC>>fs[])>>
    first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k-1’] assume_tac>>
    rw[]>>imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM]>>simp[FUNPOW_Tau_bind]>>
    TRY (qpat_x_assum ‘evaluate (While _ _,_)=_’ mp_tac>>
         simp[Once evaluate_def]>>
         rpt (CASE_TAC>>fs[])>>rw[]>>
         TRY (pairarg_tac>>fs[])>>
         rpt (FULL_CASE_TAC>>fs[])>>
         first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
         rfs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind]>>
         simp[GSYM FUNPOW_SUC,GSYM FUNPOW]>>
         metis_tac[GSYM FUNPOW_ADD])>>
    rw[]>>gvs[]>>metis_tac[GSYM FUNPOW_SUC])
  >~[‘Seq’]>-
   (fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[]>>
    rpt (CASE_TAC>>fs[])>>
    TRY (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    simp[Once itree_unfold,call_FFI_def]>>rw[]
    >- (qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
        first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k’] assume_tac>>
        imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        rfs[]>>fs[IS_PREFIX_ANTISYM,FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW]>>
        first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
        gvs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
        qexists ‘n' + SUC n’>>fs[GSYM FUNPOW_ADD])>>
    qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
    first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k’] assume_tac>>
    fs[FUNPOW_Tau_bind]>>
    rpt (CASE_TAC>>fs[]))
  >~[‘Call’]>-
   (simp[mrec_Call]>>
    rpt (CASE_TAC>>fs[])
    >~[‘TimeOut’]>-
     (Cases_on ‘k=0’>>fs[]>>
      FULL_CASE_TAC>>fs[]
      >- (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
          first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
          gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
          simp[h_handle_call_ret_def]>>
          gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[set_var_defs]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
      rpt (CASE_TAC>>fs[])>>
      simp[h_handle_call_ret_def,mrec_bind,set_var_defs]>>
      rpt (FULL_CASE_TAC>>fs[])
          (*      >>~[‘itree_bind __’]>-*)
          >>~- ([‘itree_bind __’],
                gvs[set_var_defs]>>
                first_x_assum $ qspecl_then [‘bst r' with locals := s'.locals |+(q'',v)’,‘r'.ffi’,‘r'.clock’] assume_tac>>
                imp_res_tac panPropsTheory.evaluate_io_events_mono>>
                gvs[IS_PREFIX_ANTISYM]>>rw[]>>fs[]>>
                simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
                simp[h_handle_call_ret_def,mrec_bind,set_var_defs]>>
                simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
                simp[GSYM FUNPOW_ADD])>>
      gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘DecCall’]>-
   (simp[mrec_DecCall]>>
    rpt (CASE_TAC>>fs[])
    >~[‘TimeOut’]>-
     (Cases_on ‘k=0’>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      fs[FUNPOW_Tau_bind]>>gvs[]>>
      fs[h_handle_deccall_ret_def,mrec_bind,set_var_defs,res_var_def]
      >~ [‘TimeOut’]>-
       (pairarg_tac>>fs[]>>
        first_x_assum $ qspecl_then [‘bst r' with locals := s'.locals |+ (rt,v)’,‘r'.ffi’,‘r'.clock’] assume_tac>>
        imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        gvs[IS_PREFIX_ANTISYM]>>rw[]>>fs[FUNPOW_Tau_bind]>>
        simp[h_handle_deccall_ret_def,mrec_bind,set_var_defs]>>
        fs[FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW_SUC]>>simp[GSYM FUNPOW_ADD])>>
      gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
    gvs[]>>metis_tac[FUNPOW])>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[]>>
  rpt (CASE_TAC>>fs[])>>
  TRY (pairarg_tac>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>
  simp[Once itree_unfold,call_FFI_def]>>rw[]>>
  TRY (metis_tac[FUNPOW])
QED




(**************************)
(**************************)
(**************************)
(*** evaluate -> itree (no ffi) ***)

Theorem evaluate_mrec_Ret_weak_io_events:
  evaluate (p, s0) = (res,t) ∧ s0 = ext s k ffi ∧ t.ffi.io_events = ffi.io_events ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. mrec h_prog (h_prog (p, s)) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  map_every qid_spec_tac [‘k’,‘ffi’, ‘res’,‘t’,‘s’,‘s0’, ‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac >> simp[]>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]
  >~[‘ShMemLoad’]>-
   (simp[mrec_ShMemLoad]>>fs[call_FFI_def,set_var_defs]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘ShMemStore’]>-
   (simp[mrec_ShMemStore]>>fs[call_FFI_def,set_var_defs]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    fs[call_FFI_def,set_var_defs]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]
    >>~- ([‘Error’],metis_tac[FUNPOW])>>
    qexists ‘0’>>simp[FUNPOW]>>
    simp[bst_def,ext_def,fetch "-" "bstate_component_equality"])
  >~[‘Dec’]>-
   (fs[mrec_Dec]>>
    rpt (CASE_TAC>>fs[])
    >- (gvs[]>>metis_tac[FUNPOW])>>
    pairarg_tac>>fs[]>>
    simp[Once itree_unfold]>>rw[]>>
    qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
    qpat_abbrev_tac ‘X = s' with locals := _’>>
    first_x_assum $ qspecl_then [‘X’,‘ffi’,‘k’] assume_tac>>
    rfs[]>>fs[FUNPOW_Tau_bind])
  >~[‘If’]>-
   (fs[mrec_If]>>rw[]>>
    rpt (CASE_TAC>>fs[])>>
    TRY (qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
         res_tac>>
         pop_assum kall_tac>>
         first_x_assum $ qspecl_then [‘s'’,‘k’,‘ffi’] assume_tac>>
         rfs[]>>fs[FUNPOW_Tau_bind]>>NO_TAC)>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘While’]>-
   (simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[])
    >| [gvs[]>>metis_tac[FUNPOW],all_tac,
        gvs[]>>metis_tac[FUNPOW],all_tac,
        gvs[]>>metis_tac[FUNPOW],gvs[]>>metis_tac[FUNPOW]]>>
    pairarg_tac>>fs[]>>
    Cases_on ‘k=0’>>fs[]
    >- (qpat_x_assum ‘_ = (NONE,t)’ mp_tac>>
        rpt (CASE_TAC>>fs[])>>
        first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k-1’] assume_tac>>
        rw[]>>imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        gvs[IS_PREFIX_ANTISYM]>>simp[FUNPOW_Tau_bind]
        >~ [‘Break’]>- (gvs[]>>metis_tac[GSYM FUNPOW_SUC])>>
        qpat_x_assum ‘evaluate (While _ _,_)=_’ mp_tac>>
        simp[Once evaluate_def]>>
        rpt (CASE_TAC>>fs[])>>rw[]>>
        TRY (pairarg_tac>>fs[])>>
        rpt (FULL_CASE_TAC>>fs[])>>
        first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
        rfs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW_SUC,GSYM FUNPOW]>>
        metis_tac[GSYM FUNPOW_ADD])>>
    qpat_x_assum ‘_ = (SOME _,t)’ mp_tac>>
    rpt (CASE_TAC>>fs[])>>
    first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k-1’] assume_tac>>
    rw[]>>imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM]>>simp[FUNPOW_Tau_bind]>>
    TRY (qpat_x_assum ‘evaluate (While _ _,_)=_’ mp_tac>>
         simp[Once evaluate_def]>>
         rpt (CASE_TAC>>fs[])>>rw[]>>
         TRY (pairarg_tac>>fs[])>>
         rpt (FULL_CASE_TAC>>fs[])>>
         first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
         rfs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind]>>
         simp[GSYM FUNPOW_SUC,GSYM FUNPOW]>>
         metis_tac[GSYM FUNPOW_ADD])>>
    rw[]>>gvs[]>>metis_tac[GSYM FUNPOW_SUC])
  >~[‘Seq’]>-
   (fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[]>>
    rpt (CASE_TAC>>fs[])>>
    TRY (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    simp[Once itree_unfold,call_FFI_def]>>rw[]
    >- (qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
        first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k’] assume_tac>>
        imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        rfs[]>>fs[IS_PREFIX_ANTISYM,FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW]>>
        first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
        gvs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
        qexists ‘n' + SUC n’>>fs[GSYM FUNPOW_ADD])>>
    qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
    first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k’] assume_tac>>
    fs[FUNPOW_Tau_bind]>>
    rpt (CASE_TAC>>fs[]))
  >~[‘Call’]>-
   (simp[mrec_Call]>>
    rpt (CASE_TAC>>fs[])
    >~[‘TimeOut’]>-
     (Cases_on ‘k=0’>>fs[]>>
      FULL_CASE_TAC>>fs[]
      >- (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
          first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
          gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
          simp[h_handle_call_ret_def]>>
          gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[set_var_defs]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
      rpt (CASE_TAC>>fs[])>>
      simp[h_handle_call_ret_def,mrec_bind,set_var_defs]>>
      rpt (FULL_CASE_TAC>>fs[])
          (*      >>~[‘itree_bind __’]>-*)
          >>~- ([‘itree_bind __’],
                gvs[set_var_defs]>>
                first_x_assum $ qspecl_then [‘bst r' with locals := s'.locals |+(q'',v)’,‘r'.ffi’,‘r'.clock’] assume_tac>>
                imp_res_tac panPropsTheory.evaluate_io_events_mono>>
                gvs[IS_PREFIX_ANTISYM]>>rw[]>>fs[]>>
                simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
                simp[h_handle_call_ret_def,mrec_bind,set_var_defs]>>
                simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
                simp[GSYM FUNPOW_ADD])>>
      gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘DecCall’]>-
   (simp[mrec_DecCall]>>
    rpt (CASE_TAC>>fs[])
    >~[‘TimeOut’]>-
     (Cases_on ‘k=0’>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      fs[FUNPOW_Tau_bind]>>gvs[]>>
      fs[h_handle_deccall_ret_def,mrec_bind,set_var_defs,res_var_def]
      >~ [‘TimeOut’]>-
       (pairarg_tac>>fs[]>>
        first_x_assum $ qspecl_then [‘bst r' with locals := s'.locals |+ (rt,v)’,‘r'.ffi’,‘r'.clock’] assume_tac>>
        imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        gvs[IS_PREFIX_ANTISYM]>>rw[]>>fs[FUNPOW_Tau_bind]>>
        simp[h_handle_deccall_ret_def,mrec_bind,set_var_defs]>>
        fs[FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW_SUC]>>simp[GSYM FUNPOW_ADD])>>
      gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
    gvs[]>>metis_tac[FUNPOW])>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[]>>
  rpt (CASE_TAC>>fs[])>>
  TRY (pairarg_tac>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>
  simp[Once itree_unfold,call_FFI_def]>>rw[]>>
  TRY (metis_tac[FUNPOW])
QED

Theorem io_event_eq_imp_ffi_eq:
  evaluate (p, s) = (res, t) ∧ s.ffi.io_events = t.ffi.io_events ⇒
  t.ffi = s.ffi
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘_ = (res,t)’ mp_tac
  >~ [‘ShMemLoad’] >-
   (simp[Once evaluate_def]>>
    fs[sh_mem_load_def,sh_mem_store_def,call_FFI_def]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[set_var_defs,empty_locals_defs,dec_clock_def]>>
    gvs[state_component_equality,ffi_state_component_equality])
  >~ [‘ShMemStore’] >-
   (simp[Once evaluate_def]>>
    fs[sh_mem_load_def,sh_mem_store_def,call_FFI_def]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[set_var_defs,empty_locals_defs,dec_clock_def]>>
    gvs[state_component_equality,ffi_state_component_equality])
  >~ [‘Call’] >-
   (simp[Once evaluate_def]>>
    fs[call_FFI_def]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>rw[]>>
    gvs[set_var_defs,empty_locals_defs,dec_clock_def]>>
    gvs[state_component_equality,ffi_state_component_equality]>>
    imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM])
  >~ [‘DecCall’] >-
   (simp[Once evaluate_def]>>
    fs[call_FFI_def]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>rw[]>>
    gvs[set_var_defs,empty_locals_defs,dec_clock_def]>>
    gvs[state_component_equality,ffi_state_component_equality]>>
    imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM])
  >~ [‘Seq’] >-
   (simp[Once evaluate_def]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>rw[]>>gvs[]>>
    imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM,dec_clock_def])
  >~ [‘ExtCall’] >-
   (simp[Once evaluate_def]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    fs[call_FFI_def]>>
    rpt (FULL_CASE_TAC>>fs[])>>rw[]>>
    gvs[set_var_defs,empty_locals_defs,dec_clock_def,
        state_component_equality,ffi_state_component_equality]>>
    imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM,dec_clock_def,IS_PREFIX_TRANS])
  >~ [‘While’] >-
   (simp[Once evaluate_def]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    rpt (CASE_TAC>>fs[])>>rw[]>>
    fs[dec_clock_def,empty_locals_defs]>>
     imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM,dec_clock_def,IS_PREFIX_TRANS])>>
  simp[Once evaluate_def]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  rpt (pairarg_tac>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>rw[]>>
  gvs[empty_locals_defs,dec_clock_def]
QED

Theorem evaluate_mrec_Ret_weak:
  evaluate (p, s0) = (res,t) ∧ s0 = ext s k ffi ∧ t.ffi = ffi ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. mrec h_prog (h_prog (p, s)) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  rw[]>>irule evaluate_mrec_Ret_weak_io_events>>rw[]>>metis_tac[]
QED

Theorem evaluate_itree_Ret_weak:
  evaluate (p, s0) = (res,t) ∧ s0 = ext s k ffi ∧ t.ffi = ffi ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. itree_evaluate (p, s) = FUNPOW Tau n (Ret (res,bst t))
Proof
  simp[itree_evaluate_def]>>strip_tac>>
  drule_all evaluate_mrec_Ret_weak>>rw[]>>simp[]>>
  simp[itree_unfold_FUNPOW_Tau]>>
  simp[Once itree_unfold]
QED

(*** itree Ret -> evaluate (no ffi) ***)

Theorem mrec_Ret_evaluate:
  mrec h_prog (h_prog (p,s)) = Ret (INR (res, t)):'a ptree ⇒
  ∃k k'. ∀ffi.
    evaluate (p,ext s k ffi) = (res,ext t k' ffi) ∧
    res ≠ SOME TimeOut ∧ (∀fe. res ≠ SOME (FinalFFI fe)) ∧ k' ≤ k
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[]>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If,mrec_ExtCall]
  >~[‘ExtCall’]>-
   (simp[Once evaluate_def]>>
    pop_assum mp_tac>>
    rpt (PURE_CASE_TAC>>fs[])>>rw[]>>
    gvs[ext_def,call_FFI_def])
  >~[‘While’]>-
   (simp[Once evaluate_def]>>
    pop_assum mp_tac>>
    rpt (CASE_TAC>>fs[])>>gvs[ext_def])>>
  simp[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>
  pop_assum mp_tac>>
  fs[ext_def,empty_locals_defs,dec_clock_def]>>
  rpt (CASE_TAC>>fs[])>>rw[]>>gvs[]>>
  qexistsl [‘2’,‘1’]>>fs[dec_clock_def]
QED

Theorem ext_clock_update[simp]:
  ext s k ffi with clock := k' = ext s k' ffi
Proof
  simp[ext_def]
QED

Theorem mrec_Ret_not_TimeOut:
  mrec h_prog (h_prog (p,s)) = FUNPOW Tau n (Ret (INR (res, t))):'a ptree ⇒
  res ≠ SOME TimeOut
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’
  >- (fs[FUNPOW]>>imp_res_tac mrec_Ret_evaluate>>fs[])>>
  rename1 ‘SUC n’>>rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘n’,‘s’,‘p’]>>
  Induct>>rw[]>>
  pop_assum mp_tac
  >~[‘Dec’]>-
   (simp[mrec_Dec]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    FULL_CASE_TAC>>gvs[]>>
    strip_tac>>fs[]>>
    ‘n < SUC n’ by simp[]>>res_tac)
  >~[‘Seq’]>-
   (simp[mrec_Seq]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>
    fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>gvs[]>>
    strip_tac>>fs[]>>
    ‘n - SUC n' < SUC n’ by simp[]>>res_tac>>
    ‘n < SUC n’ by simp[]>>res_tac)
  >~[‘If’]>-
   (simp[mrec_If]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>
    fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
    strip_tac>>fs[]>>
    ‘n < SUC n’ by simp[]>>res_tac)
  >~[‘While’]>-
   (simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>
    fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
    strip_tac>>fs[]>>
    ‘n - SUC n'< SUC n’ by simp[]>>res_tac)
  >~[‘Call’]>-
   (simp[mrec_Call]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rename1 ‘h_handle_call_ret _ s (INR (qq,_))’>>Cases_on ‘qq’>>fs[]>>
    TRY (rename1 ‘h_handle_call_ret _ s (INR (SOME xx,_))’>>
         Cases_on ‘xx’)>>fs[]>>
    fs[h_handle_call_ret_def,set_var_defs]>>
    (Cases_on ‘n - n'’>| [fs[FUNPOW],fs[FUNPOW_SUC]])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac LESS_EQUAL_ANTISYM>>fs[empty_locals_defs]>>
    TRY strip_tac>>gvs[]>>
    ‘n < SUC n’ by simp[]>>res_tac>>
    ‘n'' < SUC n’ by simp[]>>res_tac)
  >~[‘DecCall’]>-
   (simp[mrec_DecCall]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rename1 ‘h_handle_deccall_ret _ _ _ _ (INR (qq,_))’>>Cases_on ‘qq’>>fs[]>>
    TRY (rename1 ‘h_handle_deccall_ret _ _ _ _ (INR (SOME xx,_))’>>
         Cases_on ‘xx’)>>fs[]>>
    fs[h_handle_deccall_ret_def,set_var_defs]>>
    (Cases_on ‘n - n'’>| [fs[FUNPOW],fs[FUNPOW_SUC]])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac LESS_EQUAL_ANTISYM>>fs[empty_locals_defs]>>
    TRY strip_tac>>gvs[]>>
    ‘n < SUC n’ by simp[]>>res_tac>>
    ‘n'' < SUC n’ by simp[]>>res_tac)
  >~[‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC])>>
  simp[mrec_prog_nonrec,mrec_ShMemLoad,mrec_ShMemStore]>>
  rpt (CASE_TAC>>fs[])>>
  simp[FUNPOW_SUC]
QED

Theorem mrec_Ret_not_FinalFFI:
  mrec h_prog (h_prog (p,s)) = FUNPOW Tau n (Ret (INR (x, t))) :'a ptree ⇒
  ∀fe. x ≠ SOME (FinalFFI fe)
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’
  >- (fs[FUNPOW]>>imp_res_tac mrec_Ret_evaluate>>fs[])>>
  rename1 ‘SUC n’>>rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘n’,‘s’,‘p’]>>
  Induct>>rw[]>>
  pop_assum mp_tac
  >~[‘Dec’]>-
   (simp[mrec_Dec]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    FULL_CASE_TAC>>gvs[]>>
    strip_tac>>fs[]>>
    ‘n < SUC n’ by simp[]>>res_tac)
  >~[‘Seq’]>-
   (simp[mrec_Seq]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>
    fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>gvs[]>>
    strip_tac>>fs[]>>
    ‘n - SUC n' < SUC n’ by simp[]>>res_tac>>
    ‘n < SUC n’ by simp[]>>res_tac)
  >~[‘If’]>-
   (simp[mrec_If]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>
    fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
    strip_tac>>fs[]>>
    ‘n < SUC n’ by simp[]>>res_tac)
  >~[‘While’]>-
   (simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>gvs[])>>
    fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
    strip_tac>>fs[]>>
    ‘n - SUC n'< SUC n’ by simp[]>>res_tac)
  >~[‘Call’]>-
   (simp[mrec_Call]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rename1 ‘h_handle_call_ret _ s (INR (qq,_))’>>Cases_on ‘qq’>>fs[]>>
    TRY (rename1 ‘h_handle_call_ret _ s (INR (SOME xx,_))’>>
         Cases_on ‘xx’)>>fs[]>>
    fs[h_handle_call_ret_def,set_var_defs]>>
    (Cases_on ‘n - n'’>| [fs[FUNPOW],fs[FUNPOW_SUC]])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac LESS_EQUAL_ANTISYM>>fs[empty_locals_defs]>>
    TRY strip_tac>>gvs[]>>
    ‘n < SUC n’ by simp[]>>res_tac>>
    ‘n'' < SUC n’ by simp[]>>res_tac)
  >~[‘DecCall’]>-
   (simp[mrec_DecCall]>>
    rpt (CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rename1 ‘h_handle_deccall_ret _ _ _ _ (INR (qq,_))’>>Cases_on ‘qq’>>fs[]>>
    TRY (rename1 ‘h_handle_deccall_ret _ _ _ _ (INR (SOME xx,_))’>>
         Cases_on ‘xx’)>>fs[]>>
    fs[h_handle_deccall_ret_def,set_var_defs]>>
    (Cases_on ‘n - n'’>| [fs[FUNPOW],fs[FUNPOW_SUC]])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac LESS_EQUAL_ANTISYM>>fs[empty_locals_defs]>>
    TRY strip_tac>>gvs[]>>
    ‘n < SUC n’ by simp[]>>res_tac>>
    ‘n'' < SUC n’ by simp[]>>res_tac)
  >~[‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC])>>
  simp[mrec_prog_nonrec,mrec_ShMemLoad,mrec_ShMemStore]>>
  rpt (CASE_TAC>>fs[])>>
  simp[FUNPOW_SUC]
QED

(* move *)
Theorem evaluate_min_clock:
  evaluate (prog,s) = (q,r) ∧ q ≠ SOME TimeOut ⇒
  ∃k. evaluate (prog,s with clock := k) = (q,r with clock := 0)
Proof
  qabbrev_tac ‘x = r with clock := 0’>>
  ‘r = x with clock := x.clock + r.clock’
    by simp[state_component_equality,Abbr‘x’]>>
  pop_assum (fn h => rewrite_tac[Once h])>>strip_tac>>
  drule_all panPropsTheory.evaluate_clock_sub>>
  strip_tac>>fs[]>>metis_tac[]
QED

(* fix this so that the end state has clock = 0 *)
Theorem mrec_Ret_evaluate_weak:
  mrec h_prog (h_prog (p,s)) = FUNPOW Tau n (Ret (INR (res, t))):'a ptree ⇒
  ∃k k'. ∀ffi.
           evaluate (p,ext s k ffi) = (res,ext t k' ffi) ∧
           res ≠ SOME TimeOut ∧ (∀fe. res ≠ SOME (FinalFFI fe)) ∧ k' ≤ k
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’
  >- (fs[FUNPOW]>>irule mrec_Ret_evaluate>>fs[])>>
  rename1 ‘SUC n’>>rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]
  >~ [‘Dec’] >-
   (pop_assum mp_tac>>fs[mrec_Dec]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    ‘n < SUC n’ by simp[]>>
    res_tac>>fs[]>>
    imp_res_tac mrec_Ret_not_TimeOut>>
    imp_res_tac mrec_Ret_not_FinalFFI>>gvs[]>>
    qexistsl [‘k’,‘k'’]>>fs[])
  >~ [‘Seq’] >-
   (pop_assum mp_tac>>fs[mrec_Seq]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])
    >- (fs[GSYM FUNPOW]>>fs[FUNPOW_Ret_simp]>>
        imp_res_tac bind_FUNPOW_Ret>>
        imp_res_tac mrec_FUNPOW_Ret_INR>>
        fs[FUNPOW_Tau_bind]>>gvs[]>>
        FULL_CASE_TAC>>fs[]>>
        ‘n' < SUC n’ by simp[]>>
        ‘n - SUC n' < SUC n’ by simp[]>>
        res_tac>>fs[]>>
        (Cases_on ‘k''' ≤ k’
         >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
             qexistsl [‘k'' + p''’,‘k'’]>>strip_tac>>fs[]>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>
             fs[]>>
             rev_drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘p''’ assume_tac>>gvs[]))>>
        fs[NOT_LESS_EQUAL]>>
        drule LESS_ADD>>
        disch_then $ assume_tac o GSYM>>fs[]>>
        qexistsl [‘k''’,‘k' + p''’]>>strip_tac>>fs[]>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        fs[]>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘p''’ assume_tac>>fs[])>>
    ‘n < SUC n’ by simp[]>>
    res_tac>>
    qexistsl [‘k’,‘k'’]>>strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>gvs[])
  >~ [‘If’] >-
   (pop_assum mp_tac>>fs[mrec_If]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    ‘n < SUC n’ by simp[]>>
    res_tac>>fs[])
  >~ [‘Call’] >-
   (pop_assum mp_tac>>fs[mrec_Call]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    fs[FUNPOW_Ret_simp]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rename1 ‘h_handle_call_ret _ s (INR (qq,_))’>>Cases_on ‘qq’>>fs[]>>
    TRY (rename1 ‘h_handle_call_ret _ s (INR (SOME xx,_))’>>
         Cases_on ‘xx’)>>fs[]>>
    fs[h_handle_call_ret_def,set_var_defs]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    (Cases_on ‘n - n'’>| [fs[FUNPOW],fs[FUNPOW_SUC]])>>
    imp_res_tac LESS_EQUAL_ANTISYM>>fs[]>>
    ‘n < SUC n’ by simp[]>>
    res_tac>>gvs[empty_locals_defs]>>
    TRY (qexistsl [‘SUC k’,‘k'’]>>strip_tac>>fs[empty_locals_defs]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         rpt (CASE_TAC>>fs[])>>gvs[]>>NO_TAC)>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>
    FULL_CASE_TAC>>gvs[]>>
    ‘n' < SUC n’ by simp[]>>
    ‘n'' < SUC n’ by simp[]>>
    res_tac>>
    (Cases_on ‘k''' ≤ k’
     >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
         qexistsl [‘SUC (k'' + p)’,‘k'’]>>strip_tac>>fs[]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         fs[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘p’ assume_tac>>fs[]))>>
    fs[NOT_LESS_EQUAL]>>
    drule LESS_ADD>>
    disch_then $ assume_tac o GSYM>>fs[]>>
    qexistsl [‘SUC k''’,‘k' + p’]>>strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    fs[]>>
    drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘p’ assume_tac>>fs[])
  >~ [‘DecCall’] >-
   (pop_assum mp_tac>>fs[mrec_DecCall]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    fs[FUNPOW_Ret_simp]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rename1 ‘h_handle_deccall_ret _ _ _ _ (INR (qq,_))’>>Cases_on ‘qq’>>fs[]>>
    TRY (rename1 ‘h_handle_deccall_ret _ _ _ _ (INR (SOME xx,_))’>>
         Cases_on ‘xx’)>>fs[]>>
    fs[h_handle_deccall_ret_def,set_var_defs]>>
    rpt (FULL_CASE_TAC>>fs[])>>
         (Cases_on ‘n - n'’>| [fs[FUNPOW],fs[FUNPOW_SUC]])>>
    imp_res_tac LESS_EQUAL_ANTISYM>>fs[]>>
    ‘n < SUC n’ by simp[]>>
    res_tac>>gvs[empty_locals_defs]>>
    TRY (qexistsl [‘SUC k’,‘k'’]>>strip_tac>>fs[empty_locals_defs]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         rpt (CASE_TAC>>fs[])>>gvs[]>>NO_TAC)>>
    fs[mrec_bind]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>
    FULL_CASE_TAC>>gvs[]>>
    ‘n' < SUC n’ by simp[]>>
    ‘n'' < SUC n’ by simp[]>>
    res_tac>>
    (Cases_on ‘k''' ≤ k’
     >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
         qexistsl [‘SUC (k'' + p')’,‘k'’]>>strip_tac>>fs[]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         fs[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘p'’ assume_tac>>fs[]))>>
    fs[NOT_LESS_EQUAL]>>
    drule LESS_ADD>>
    disch_then $ assume_tac o GSYM>>fs[]>>
    qexistsl [‘SUC k''’,‘k' + p'’]>>strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    fs[]>>
    drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘p'’ assume_tac>>fs[])
  >~[‘ExtCall’]>-
   (pop_assum mp_tac>>fs[mrec_ExtCall]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    (Cases_on ‘n’>| [simp[FUNPOW],simp[FUNPOW_SUC]])>>
    rw[]>>gvs[ext_def,call_FFI_def])
  >~[‘While’]>-
   (pop_assum mp_tac>>simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[])>>simp[FUNPOW_SUC]
    >- (* NONE *)
     (rw[]>>imp_res_tac bind_FUNPOW_Ret>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      fs[FUNPOW_Tau_bind]>>
      rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      pop_assum mp_tac
      >~[‘INR (SOME Break,_)’]>-
       (strip_tac>>gvs[]>>
        ‘n < SUC n’ by simp[]>>
        res_tac>>
        qexistsl [‘SUC k’,‘k'’]>>simp[]>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        gvs[])>>
      strip_tac>>
      fs[GSYM FUNPOW]>>imp_res_tac FUNPOW_Ret_strip>>
      ‘n - SUC n' < SUC n’ by simp[]>>
      ‘n' < SUC n’ by simp[]>>
      res_tac>>
      (Cases_on ‘k' ≤ k''’
       >- (drule LESS_EQUAL_ADD>>rw[]>>
           qexistsl [‘SUC (k + p')’,‘k'''’]>>strip_tac>>fs[]>>
           first_x_assum $ qspec_then ‘ffi’ assume_tac>>
           first_x_assum $ qspec_then ‘ffi’ assume_tac>>
           fs[]>>
           drule panPropsTheory.evaluate_add_clock_eq>>
           disch_then $ qspec_then ‘p'’ assume_tac>>fs[]))>>
      fs[NOT_LESS_EQUAL]>>
      drule LESS_ADD>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      qexistsl [‘SUC k’,‘k''' + p'’]>>strip_tac>>fs[]>>
      first_x_assum $ qspec_then ‘ffi’ assume_tac>>
      first_x_assum $ qspec_then ‘ffi’ assume_tac>>
      fs[]>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘p'’ assume_tac>>fs[])>>
    (* SOME x *)
    rw[]>>imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>fs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    pop_assum mp_tac
    >~[‘INR (SOME TimeOut,_)’]>-
     (imp_res_tac mrec_Ret_not_TimeOut>>gvs[])
    >~[‘INR (SOME (FinalFFI _),_)’]>-
     (imp_res_tac mrec_Ret_not_FinalFFI>>gvs[])>>
    TRY (strip_tac>>gvs[]>>
         ‘n < SUC n’ by simp[]>>
         res_tac>>
         qexistsl [‘SUC k’,‘k'’]>>simp[]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         gvs[]>>NO_TAC)>>
    strip_tac>>
    fs[GSYM FUNPOW]>>imp_res_tac FUNPOW_Ret_strip>>
    ‘n - SUC n' < SUC n’ by simp[]>>
    ‘n' < SUC n’ by simp[]>>
    res_tac>>
    (Cases_on ‘k' ≤ k''’
     >- (drule LESS_EQUAL_ADD>>rw[]>>
         qexistsl [‘SUC (k + p')’,‘k'''’]>>strip_tac>>fs[]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         fs[]>>
         drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘p'’ assume_tac>>fs[]))>>
    fs[NOT_LESS_EQUAL]>>
    drule LESS_ADD>>
    disch_then $ assume_tac o GSYM>>fs[]>>
    qexistsl [‘SUC k’,‘k''' + p'’]>>strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    fs[]>>
    rev_drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘p'’ assume_tac>>fs[])>>
  pop_assum mp_tac>>
  fs[mrec_prog_nonrec,mrec_If,empty_locals_defs]>>
  rpt (CASE_TAC>>fs[])>>
  simp[FUNPOW_SUC]>>gvs[]
QED


(*** ffi case ***)

Theorem evaluate_ffi_lemma:
  evaluate (p,s) = (res, s') ⇒
  (s.ffi = s'.ffi ⇔ s.ffi.io_events = s'.ffi.io_events)
Proof
  strip_tac>>eq_tac>>rw[]>>metis_tac[io_event_eq_imp_ffi_eq]
QED

(*** evaluate -> itree (ffi) ***)

Theorem mrec_Vis_evaluate:
  mrec h_prog (h_prog (p, bst s)) = (Vis e g:'a ptree) ∧
  evaluate (p, s) = (res, s') ∧ res ≠ SOME TimeOut ⇒
  (s.ffi.io_events ≠ s'.ffi.io_events ∧ ∀fe. res ≠ SOME (FinalFFI fe))
   ∨ (s.ffi.io_events = s'.ffi.io_events ∧ ∃fe. res = SOME (FinalFFI fe))
Proof
  map_every qid_spec_tac [‘res’,‘s'’,‘e’,‘g’,‘s’,‘p’]>>
  Induct>>rw[]>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If,mrec_ExtCall]>>
  pop_assum mp_tac>>
  gvs[AllCaseEqs()]>>rw[]>>
  fs[Once evaluate_def]>>
  fs[sh_mem_load_def,sh_mem_store_def]>>
  fs[panPropsTheory.eval_upd_clock_eq,empty_locals_defs]>>
  gvs[call_FFI_def]>>
  gvs[AllCaseEqs()]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  fs[state_component_equality,ffi_state_component_equality]
QED

Theorem mrec_Vis_evaluate2:
  mrec h_prog (h_prog (p, bst s)) = (Vis e g:'a ptree) ∧
  evaluate (p, s) = (res, s') ∧ s.ffi.io_events ≠ s'.ffi.io_events ⇒
  res = X
Proof
  map_every qid_spec_tac [‘res’,‘s'’,‘e’,‘g’,‘s’,‘p’]>>
  Induct>>rw[]>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If,mrec_ExtCall]>>
  pop_assum mp_tac>>
  gvs[AllCaseEqs()]>>rw[]>>
  fs[Once evaluate_def]>>
  fs[sh_mem_load_def,sh_mem_store_def]>>
  fs[panPropsTheory.eval_upd_clock_eq,empty_locals_defs]>>
  gvs[call_FFI_def]>>
  gvs[AllCaseEqs()]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  fs[state_component_equality,ffi_state_component_equality]
QED

(*** evaluate -> itree (ffi) ***)

Theorem evaluate_mrec_Vis_weak:
  evaluate (p, s) = (res, s') ∧ res ≠ SOME TimeOut ∧
  (s.ffi.io_events ≠ s'.ffi.io_events ∨ ∃fe. res = SOME (FinalFFI fe)) ⇒
    ∃n e g. mrec h_prog (h_prog (p, bst s)) = FUNPOW Tau n (Vis e g:'a ptree)
Proof
  map_every qid_spec_tac [‘res’,‘s'’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  simp[mrec_prog_simps,mrec_If,mrec_ShMemLoad,mrec_ShMemStore,
       mrec_ExtCall,mrec_Call,mrec_DecCall]>>
  qhdtm_x_assum ‘evaluate’ mp_tac>>
  simp[Once evaluate_def]>>
  simp[sh_mem_load_def,sh_mem_store_def,call_FFI_def]>>
  simp[panPropsTheory.eval_upd_clock_eq,empty_locals_defs]>>rw[]>>
  gvs[AllCaseEqs()]>>rw[]>>
  rpt (pairarg_tac>>fs[])>>
  gvs[set_var_defs,dec_clock_def,res_var_def]>>simp[FUNPOW_Tau_bind]>>
  TRY (simp[GSYM FUNPOW_SUC]>>NO_TAC)>>
  TRY (simp[state_component_equality,ffi_state_component_equality]>>NO_TAC)>>
  TRY (qexists ‘0’>>simp[FUNPOW]>>NO_TAC)
>~ [‘While’]>-
   (simp[Once mrec_While]>>
    Cases_on ‘s.ffi.io_events = s1.ffi.io_events ∧ ∀fe. res' ≠ SOME (FinalFFI fe)’>>fs[]
      >- (rev_drule (iffRL evaluate_ffi_lemma)>>
          simp[]>>rw[]>>rfs[]>>
          rev_drule evaluate_mrec_Ret_weak>>
          disch_then $ qspecl_then [‘bst s’,‘s.clock-1’,‘s.ffi’] mp_tac>>
          fs[]>>gvs[]>>
          impl_tac>-
           (simp[ext_def,bst_def,state_component_equality]>>
            rpt (FULL_CASE_TAC>>fs[]))>>
          rw[]>>simp[FUNPOW_Tau_bind,itree_bind_thm]>>
          simp[GSYM FUNPOW_SUC]>>
          rpt (PURE_CASE_TAC>>fs[])>>gvs[]>>
          fs[GSYM FUNPOW]>>simp[GSYM FUNPOW_ADD])>>
      ‘res' ≠ SOME TimeOut’
        by (rpt (FULL_CASE_TAC>>fs[]))>>fs[]>>
      fs[FUNPOW_Tau_bind,itree_bind_thm]>>
      fs[GSYM FUNPOW_SUC])
>~ [‘Seq’]>-
   (simp[mrec_Seq]>>
    FULL_CASE_TAC>>fs[]
    >- (Cases_on ‘s.ffi.io_events = s1.ffi.io_events’>>fs[]
        >- (drule_all (iffRL evaluate_ffi_lemma)>>rw[]>>
            drule evaluate_mrec_Ret_weak>>
            disch_then $ qspecl_then [‘bst s’,‘s.clock’,‘s.ffi’] assume_tac>>
            fs[]>>gvs[]>>
            simp[FUNPOW_Tau_bind,itree_bind_thm]>>
            simp[GSYM FUNPOW_SUC]>>fs[GSYM FUNPOW_ADD])>>
        qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>
        simp[FUNPOW_Tau_bind,itree_bind_thm])>>
    qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>
    simp[FUNPOW_Tau_bind,itree_bind_thm])
  (* Call *)
  >~ [‘h_handle_call_ret’]
  >- (Cases_on ‘s.ffi.io_events = st.ffi.io_events’>>fs[]
      >- (rev_drule (iffRL evaluate_ffi_lemma)>>
          simp[]>>rw[]>>rfs[]>>
          rev_drule evaluate_mrec_Ret_weak>>
          disch_then $ qspecl_then [‘bst (s with locals:=newlocals)’,‘s.clock-1’,‘s.ffi’] mp_tac>>
          fs[]>>gvs[]>>
          impl_tac>-
           simp[ext_def,bst_def,state_component_equality]>>
          rw[]>>simp[FUNPOW_Tau_bind,itree_bind_thm]>>
          simp[GSYM FUNPOW_SUC]>>
          simp[mrec_h_handle_call_ret_lemma]>>
          simp[o_DEF,set_var_defs]>>
          simp[FUNPOW_Tau_bind,itree_bind_thm]>>
          simp[GSYM FUNPOW_SUC]>>simp[GSYM FUNPOW_ADD])>>
      simp[FUNPOW_Tau_bind,itree_bind_thm]>>
      simp[GSYM FUNPOW_SUC])>>
  (* DecCall *)
  Cases_on ‘s.ffi.io_events = st.ffi.io_events’>>fs[]
      >- (rev_drule (iffRL evaluate_ffi_lemma)>>
          simp[]>>rw[]>>rfs[]>>
          rev_drule evaluate_mrec_Ret_weak>>
          disch_then $ qspecl_then [‘bst (s with locals:=newlocals)’,‘s.clock-1’,‘s.ffi’] mp_tac>>
          fs[]>>gvs[]>>
          impl_tac>-
           simp[ext_def,bst_def,state_component_equality]>>
          rw[]>>simp[FUNPOW_Tau_bind,itree_bind_thm]>>
          simp[GSYM FUNPOW_SUC]>>
          simp[mrec_h_handle_deccall_ret_lemma]>>
          simp[o_DEF,set_var_defs]>>
          simp[FUNPOW_Tau_bind,itree_bind_thm]>>
          simp[GSYM FUNPOW_SUC]>>simp[GSYM FUNPOW_ADD])>>
      simp[FUNPOW_Tau_bind,itree_bind_thm]>>
      simp[GSYM FUNPOW_SUC]
QED


(*** traces ***)

Definition trace_prefix'_def:
  trace_prefix' (x,x') (th:'a ptree) =
  LFLATTEN $ LUNFOLD
  (λ(fs,t). case t of
               Ret r => NONE
             | Tau u => SOME ((fs,u),LNIL)
             | Vis (s,conf,ws) k =>
                 (case x s fs conf ws of
                  | Oracle_return fs' ws' =>
                      if LENGTH ws ≠ LENGTH ws'
                      then SOME ((fs', k (INL (INR ws'))),LNIL)
                      else
                        SOME ((fs',k (INL (INR ws'))),[|IO_event s conf (ZIP (ws,ws'))|])
                  | Oracle_final outcome =>
                      SOME ((fs, k (INL (INR ws))),LNIL)))
  (x',th)
End

Theorem trace_prefix_simps[simp]:
  trace_prefix' (x,x') (Ret r) = [||] ∧
  trace_prefix' (x,x') (Tau u) = trace_prefix' (x,x') u ∧
  trace_prefix' (x,x') (Vis (s,c,ws) k) =
    case x s x' c ws of
    | Oracle_return fs' ws' =>
        if LENGTH ws ≠ LENGTH ws'
        then trace_prefix' (x,fs') (k (INL (INR ws')))
        else
          IO_event s c (ZIP (ws,ws')):::trace_prefix' (x,fs') (k (INL (INR ws')))
    | Oracle_final outcome => trace_prefix' (x,x') (k (INL (INR ws)))
Proof
  rw[trace_prefix'_def]>>
  simp[Once LUNFOLD]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]
QED

(****)

Theorem trace_prefix_bind_append:
  (∃n. ltree (x,x') t = FUNPOW Tau n (Ret r)) ⇒
  trace_prefix' (x,x') (itree_bind t k) =
    LAPPEND (trace_prefix' (x,x') t) (trace_prefix' (x,SND (comp_ffi (x,x') t)) (k r))
Proof
  simp[PULL_EXISTS]>>
  map_every qid_spec_tac [‘x'’,‘r’,‘k’,‘t’] >>
  Induct_on ‘n’ >>
  rw[FUNPOW_SUC]
  >- (Cases_on ‘t’ >> fs[]>>
      PairCases_on ‘a’>>fs[]>>
      CASE_TAC>>fs[])>>
  Cases_on ‘t’ >> fs[] >>
  PairCases_on ‘a’>>fs[]>>
  rpt (CASE_TAC>>fs[])
QED

(***************************)

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

Theorem trace_prefix_Ret_FST[simp]:
  FST (trace_prefix n (or, ffi) (Ret r)) = []
Proof
  Cases_on ‘n’>>simp[trace_prefix_def]
QED

Theorem trace_prefix_Ret_SND[simp]:
  n ≠ 0 ⇒ SND (trace_prefix n (or, ffi) (Ret r)) = SOME r
Proof
  Cases_on ‘n’>>simp[trace_prefix_def]
QED

Theorem trace_prefix_Ret_simp[simp]:
  trace_prefix n (or,ffi) (Ret r) = ([], if n = 0 then NONE else SOME r)
Proof
  Cases_on ‘n’>>simp[trace_prefix_def]
QED

Theorem trace_prefix_FUNPOW_Tau:
  trace_prefix n x (FUNPOW Tau m ht) = trace_prefix (n - m) x ht
Proof
  map_every qid_spec_tac [‘ht’,‘m’,‘n’]>>
  Induct>>rw[]>>Cases_on ‘x’
  >- simp[trace_prefix_def]>>
  Cases_on ‘m’>>fs[FUNPOW_SUC]>>
  simp[trace_prefix_def]
QED

Theorem trace_prefix_Vis[simp]:
  trace_prefix n (x,x') (Vis a g) =
  (case n of
     0 => ([],NONE)
   | SUC n =>
       (case x (FST a) x' (FST(SND a)) (SND(SND a)) of
          Oracle_final f => trace_prefix n (x,x') (g (INL f))
        | Oracle_return f l =>
            (let (io,res) = trace_prefix n (x,f) (g (INR l))
             in
               if LENGTH (SND(SND a)) ≠ LENGTH l
               then (io,res)
               else (IO_event (FST a) (FST(SND a)) (ZIP (SND(SND a),l))::io,res))))
Proof
  Cases_on ‘n’>>simp[trace_prefix_def]>>
  simp[trace_prefix_def]>>
  PairCases_on ‘a’>>simp[]>>
  CASE_TAC>>
  simp[trace_prefix_def]>>
  rpt (pairarg_tac>>fs[])
QED

Definition trace_prefix0_def:
  trace_prefix0 0 (oracle, ffi_st) (itr:'a ptree) = ([], NONE) ∧
  trace_prefix0 (SUC n) (oracle, ffi_st) (Ret (INL l)) = ([], SOME ARB) ∧
  trace_prefix0 (SUC n) (oracle, ffi_st) (Ret (INR r)) = ([], SOME r) ∧
  trace_prefix0 (SUC n) (oracle, ffi_st) (Tau t) = trace_prefix0 n (oracle, ffi_st) t ∧
  trace_prefix0 (SUC n) (oracle, ffi_st) ((Vis (s, conf, ws) f):'a ptree) =
    case oracle s ffi_st conf ws of
    | Oracle_return ffi_st' ws' =>
        let (io, res) = trace_prefix0 n (oracle, ffi_st') (f $ INL $ INR ws') in
        if LENGTH ws ≠ LENGTH ws' then (io, res)
        else (IO_event s conf (ZIP (ws,ws'))::io, res)
    | Oracle_final outcome => trace_prefix0 n (oracle, ffi_st) (f $ INL $ INL outcome)
End

Theorem trace_prefix0_Ret[simp]:
  FST (trace_prefix0 n (or, ffi) (Ret r)) = []
Proof
  Cases_on ‘n’>>Cases_on ‘r’>>simp[trace_prefix0_def]
QED

Theorem trace_prefix0_Ret_SND[simp]:
  n ≠ 0 ⇒ SND (trace_prefix0 n (or, ffi) (Ret (INR r))) = SOME r
Proof
  Cases_on ‘n’>>simp[trace_prefix0_def]
QED

Theorem trace_prefix0_Ret_simp[simp]:
  trace_prefix0 n (or,ffi) (Ret x) =
  ([], if n = 0 then NONE
       else (case x of INL _ => SOME ARB | INR r => SOME r))
Proof
  Cases_on ‘n’>>Cases_on ‘x’>>simp[trace_prefix0_def]
QED

Theorem trace_prefix0_FUNPOW_Tau:
  trace_prefix0 n x (FUNPOW Tau m ht) = trace_prefix0 (n - m) x ht
Proof
  map_every qid_spec_tac [‘ht’,‘m’,‘n’]>>
  Induct>>rw[]>>Cases_on ‘x’
  >- simp[trace_prefix0_def]>>
  Cases_on ‘m’>>fs[FUNPOW_SUC]>>
  simp[trace_prefix0_def]
QED

Theorem trace_prefix0_Vis[simp]:
  trace_prefix0 n (x,x') (Vis a g) =
  (case n of
     0 => ([],NONE)
   | SUC n =>
       (case x (FST a) x' (FST(SND a)) (SND(SND a)) of
          Oracle_final f => trace_prefix0 n (x,x') (g (INL (INL f)))
        | Oracle_return f l =>
            (let (io,res) = trace_prefix0 n (x,f) (g (INL (INR l)))
             in
               if LENGTH (SND(SND a)) ≠ LENGTH l
               then (io,res)
               else (IO_event (FST a) (FST(SND a)) (ZIP (SND(SND a),l))::io,res))))
Proof
  Cases_on ‘n’>>simp[trace_prefix0_def]>>
  PairCases_on ‘a’>>simp[]>>
  CASE_TAC>>
  simp[trace_prefix0_def]
QED

Theorem trace_prefix_eq0:
  trace_prefix n (x,x')
  (itree_unfold
   (λx.
      case x of
        Ret r => Ret' (case r of INL l => ARB | INR r => r)
      | Tau t => Tau' t
      | Vis e f => Vis' e (λx. f (INL x))) ht) =
  trace_prefix0 n (x,x') ht
Proof
  map_every qid_spec_tac [‘ht’,‘x’,‘x'’,‘p’,‘s’,‘n’]>>
  completeInduct_on ‘n’>>
  Cases_on ‘n’>>rw[]
  >-simp[trace_prefix_def,trace_prefix0_def]>>
  Cases_on ‘∃t. strip_tau ht t’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      simp[itree_unfold_FUNPOW_Tau,trace_prefix_FUNPOW_Tau,
           trace_prefix0_FUNPOW_Tau,FUNPOW_Tau_bind]>>
      Cases_on ‘t’>>fs[]>>
      simp[Once itree_unfold]>>
      simp[trace_prefix_def,trace_prefix0_def]
      >- FULL_CASE_TAC>>
      Cases_on ‘SUC n' - n’>>
      PairCases_on ‘a’>>fs[])>>
  imp_res_tac strip_tau_spin>>fs[]>>
  once_rewrite_tac[spin]>>
  simp[Once itree_unfold]>>
  simp[trace_prefix_def,trace_prefix0_def]
QED

Theorem trace_prefix0_prefix:
  ∀n m oracle ffi t io res io' res'. n ≤ m ∧
    trace_prefix0 n (oracle,ffi) t = (io,res) ∧
    trace_prefix0 m (oracle,ffi) t = (io',res')
  ⇒ io ≼ io'
Proof
  Induct >> rw[] >> gvs[trace_prefix0_def] >>
  Cases_on `m` >> gvs[] >> rename1 `_ ≤ m` >>
  first_x_assum drule >> rw[] >>
  Cases_on `t` >> gvs[trace_prefix0_def]
  >- res_tac>>
  PairCases_on `a` >> gvs[trace_prefix0_def] >>
  every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >> res_tac
QED

Theorem trace_prefix0_bind_Ret[simp]:
  FST (trace_prefix0 n (x,x') (itree_bind t (λa. Ret (f a))))
  = FST (trace_prefix0 n (x,x') t)
Proof
  map_every qid_spec_tac [‘t’,‘x'’,‘f’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’>>fs[trace_prefix0_def]>>
  Cases_on ‘∃t'. strip_tau t t'’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      simp[FUNPOW_Tau_bind,trace_prefix0_FUNPOW_Tau]>>
      Cases_on ‘t'’>>fs[]>>
      TOP_CASE_TAC>>fs[]>>
      CASE_TAC>>fs[]>>
      pairarg_tac>>fs[]>>
      pairarg_tac>>fs[]>>
      last_x_assum $ qspec_then ‘n''’ assume_tac>>fs[]>>
      ‘n'' < SUC n'’ by simp[]>>fs[]>>
      first_x_assum $ qspecl_then [‘f’,‘f'’,‘g(INL(INR l))’] assume_tac>>fs[]>>
      CASE_TAC>>gvs[])>>
  imp_res_tac strip_tau_spin>>fs[spin_bind]
QED

Theorem trace_prefix0_spin[simp]:
  trace_prefix0 n (x,x') spin = ([],NONE)
Proof
  rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>
  simp[trace_prefix0_FUNPOW_Tau]>>
  simp[trace_prefix0_def]
QED

Theorem trace_prefix0_length:
  LENGTH (FST (trace_prefix0 n (x,x') t)) ≤ n
Proof
  map_every qid_spec_tac [‘t’,‘x’,‘x'’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>fs[trace_prefix0_def]>>
  Cases_on ‘n’>>fs[trace_prefix0_def]>>
  rename1 ‘SUC n’>>
  Cases_on ‘∃t'. strip_tau t t'’>>fs[]
  >- (
  imp_res_tac strip_tau_FUNPOW>>
  Cases_on ‘n'’>>fs[]
  >- (
    Cases_on ‘t'’>>fs[]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>
    last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
    TRY (last_x_assum $ qspecl_then [‘f’,‘x’,‘g(INL(INR l))’] assume_tac>>
         gvs[]>>NO_TAC)>>
    last_x_assum $ qspecl_then [‘x'’,‘x’,‘g(INL(INL f))’] assume_tac>>
    gvs[])>>
  simp[FUNPOW_Tau_bind,trace_prefix0_FUNPOW_Tau]>>
  irule LESS_EQ_TRANS>>
  last_x_assum $ irule_at Any>>
  simp[])>>
  imp_res_tac strip_tau_spin>>simp[]
QED

(***)



(***)

Theorem trace_prefix0_Ret_bind[simp]:
  FST (trace_prefix0 k (x,x') (itree_bind (Ret r) g))
  = FST (trace_prefix0 k (x,x') (g r))
Proof
  simp[]
QED


Theorem trace_prefix0_Nil_cases:
  FST (trace_prefix0 n (x,x') t) = [] ⇔
    (∃r m. t = FUNPOW Tau m (Ret r)) ∨ n = 0 ∨ t = spin ∨
    (∃e g m. t = FUNPOW Tau m (Vis e g) ∧
             (m < n ⇒
              let (s,c,w) = e in
              case x s x' c w of
                Oracle_return x'' w' =>
                  LENGTH w ≠ LENGTH w' ∧
                  FST (trace_prefix0 (n - SUC m) (x,x'') (g (INL (INR w')))) = []
              | Oracle_final oc =>
                  FST (trace_prefix0 (n - SUC m) (x,x') (g (INL (INL oc)))) = []))
Proof
  EQ_TAC
  >- (map_every qid_spec_tac [‘t’,‘x'’,‘n’]>>
      completeInduct_on ‘n’>>
      Cases_on ‘n’>>rw[trace_prefix0_def]>>
      rename1 ‘SUC n’>>
      Cases_on ‘∃t'. strip_tau t t'’>>fs[]
      >- (
       imp_res_tac strip_tau_FUNPOW>>
       Cases_on ‘t'’>>fs[]>>rw[]>>
       fs[trace_prefix0_FUNPOW_Tau]>>
       irule OR_INTRO_THM2>>
       Cases_on ‘SUC n - n'’>>gvs[]>>
       pairarg_tac>>fs[]>>
       CASE_TAC>>fs[]
       >- (pairarg_tac>>fs[]>>
           FULL_CASE_TAC>>fs[]>>
           ‘n - n' = n''’ by gvs[]>>fs[])>>
       ‘n - n' = n''’ by gvs[]>>fs[])>>
      imp_res_tac strip_tau_spin>>fs[])>>
  rw[]>>simp[trace_prefix0_def,trace_prefix0_FUNPOW_Tau]>>
  TOP_CASE_TAC>>fs[]>>
  rpt (CASE_TAC>>fs[])>>
  rpt (pairarg_tac>>fs[])>>
  ‘n - SUC m = n'’ by gvs[]>>fs[]
QED

Theorem trace_prefix0_bind_Ret:
  (∀a. ∃x. strip_tau (h a) (Ret (INR x))) ⇒
  ∃m. FST (trace_prefix0 m (or,f) (itree_bind t h)) =
      FST (trace_prefix0 n (or,f) t)
Proof
  rw[]>>irule_at Any EQ_SYM>>pop_assum mp_tac>>
  map_every qid_spec_tac [‘h’,‘t’,‘f’,‘or’,‘n’]>>
  recInduct trace_prefix0_ind>>
  rw[]
  >- (qexists ‘0’>>simp[trace_prefix0_def])
  >- (qexists ‘0’>>simp[trace_prefix0_def])
  >- (qexists ‘0’>>simp[trace_prefix0_def])
  >- (qrefine ‘SUC m’>>simp[trace_prefix0_def])>>
  qrefine ‘SUC m’>>simp[]>>
  FULL_CASE_TAC>>fs[]>>
  rpt (pairarg_tac>>fs[])>>
  FULL_CASE_TAC>>fs[]
  >- simp[GSYM LAMBDA_PROD]>>
  qmatch_goalsub_abbrev_tac ‘FST (X _)’>>
  ‘X =((λx. IO_event s conf (ZIP (ws,l))::x) ## I)’
    by simp[Abbr‘X’,FUN_EQ_THM,FORALL_PROD]>>
  simp[]
QED

Theorem test:
  FST (trace_prefix0 (SUC n) (x,x') (Vis e (λa. itree_bind (g a) g'))) =
  (let (e1,e2,e3) = e in
     case x e1 x' e2 e3 of
       Oracle_return f l =>
         if LENGTH e3 ≠ LENGTH l then
           FST (trace_prefix0 n (x,f) (itree_bind (g (INL (INR l))) g'))
         else
           (IO_event e1 e2 (ZIP (e3,l)))::
              FST (trace_prefix0 n (x,f) (itree_bind (g (INL (INR l))) g'))
       | Oracle_final f =>
           FST (trace_prefix0 n (x,x') (itree_bind (g (INL (INR l))) g')))
Proof
  map_every qid_spec_tac [‘g’,‘g'’,‘e’,‘x'’,‘n’]>>
  Induct>-simp[]>>simp[Excl "trace_prefix0_Vis"]>>rw[]>>
  first_x_assum $ qspecl_then [‘x'’, ‘e’,‘g'’,‘g’] assume_tac>>
  rpt (CASE_TAC>>fs[Excl "trace_prefix0_Vis"])>>
  rpt (pairarg_tac>>fs[Excl "trace_prefix0_Vis"])>>
  CASE_TAC>>fs[]>>

  last_x_assum mp_tac>>simp[]>>
  TOP_CASE_TAC>>fs[]>>
  pairarg_tac>>fs[]>>rw[]>>
  qmatch_goalsub_abbrev_tac ‘_ = FST X’>>Cases_on ‘X’>>gvs[]

  FULL_CASE_TAC>>fs[]>>
  FULL_CASE_TAC>>fs[]
  
QED
                      
(*********************************************)

(**** divergence ****)

Theorem evaluate_io_events_lprefix_chain:
  lprefix_chain
  (IMAGE
   (λk. fromList (SND (evaluate (p,s with clock := k))).ffi.io_events)
   𝕌(:num))
Proof
  ‘∀x. x ∈ UNIV ⇒ (λk. llist$fromList (SND (evaluate (p,s with clock := k))).ffi.io_events) x =
                  (fromList o (λk. (SND (evaluate (p,s with clock := k))).ffi.io_events)) x’
    by simp[o_DEF]>>
  ‘(UNIV:num->bool)=UNIV’ by simp[]>>
  drule_then drule IMAGE_CONG>>strip_tac>>
  pop_assum (fn h => pure_rewrite_tac[h])>>
  simp[IMAGE_COMPOSE]>>
  irule prefix_chain_lprefix_chain>>
  simp[prefix_chain_def]>>
  rpt (pop_assum kall_tac)>>
  rw[]>>
  Cases_on ‘k < k'’>>fs[NOT_LESS]
  >- (imp_res_tac (GSYM LESS_ADD)>>
      simp[]>>
      irule OR_INTRO_THM1>>
      irule IS_PREFIX_TRANS>>
      irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
      qexists ‘p'’>>simp[])>>
  imp_res_tac LESS_EQUAL_ADD>>
  simp[]>>
  irule OR_INTRO_THM2>>
  irule IS_PREFIX_TRANS>>
  irule_at Any panPropsTheory.evaluate_add_clock_io_events_mono>>
  qexists ‘p'’>>simp[]
QED

Theorem trace_prefix0_lprefix_chain:
  lprefix_chain
  (IMAGE
   (λn.
      fromList
      (FST
       (trace_prefix0 n (x,x')
                      (mrec h_prog (h_prog (p,s)))))) 𝕌(:num))
Proof
  ‘∀m. m ∈ UNIV ⇒
       (λn. llist$fromList
            (FST
             (trace_prefix0 n (x,x')
                            (mrec h_prog (h_prog (p,s)))))) m =
       (fromList o (λn. FST
                        (trace_prefix0 n (x,x')
                                       (mrec h_prog (h_prog (p,s)))))) m’
    by simp[o_DEF]>>
  ‘(UNIV:num->bool)=UNIV’ by simp[]>>
  drule_then drule IMAGE_CONG>>strip_tac>>
  pop_assum (fn h => pure_rewrite_tac[h])>>
  simp[IMAGE_COMPOSE]>>
  irule prefix_chain_lprefix_chain>>
  simp[prefix_chain_def]>>
  rpt (pop_assum kall_tac)>>
  rw[]>>
  Cases_on ‘n < n'’>>fs[NOT_LESS]
  >- (irule OR_INTRO_THM1>>
      imp_res_tac LESS_IMP_LESS_OR_EQ>>
      qmatch_goalsub_abbrev_tac ‘FST X ≼ FST Y’>>
      Cases_on ‘X’>>Cases_on ‘Y’>>fs[]>>
      drule_all trace_prefix0_prefix>>simp[])>>
  irule OR_INTRO_THM2>>
  qmatch_goalsub_abbrev_tac ‘FST X ≼ FST Y’>>
  Cases_on ‘X’>>Cases_on ‘Y’>>fs[]>>
  drule_all trace_prefix0_prefix>>simp[]
QED


(*** bounded case ***)


Theorem bounded_trace_eq:
 (∀k. (SND(evaluate(p,s))).ffi.io_events =
      (SND(evaluate(p,s with clock:= s.clock + k))).ffi.io_events) ∧
 (∀r n. ¬(ltree (s.ffi.oracle,s.ffi.ffi_state) ((mrec h_prog (h_prog (p,bst s))):'a ptree) = FUNPOW Tau n (Ret r))) ⇒
  LAPPEND (fromList (s.ffi.io_events)) (trace_prefix' (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s)))) =
  fromList (SND (evaluate (p, s))).ffi.io_events
Proof
  MAP_EVERY qid_spec_tac [‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]
  >~ [‘ExtCall’] >- (
  simp[Once evaluate_def,mrec_ExtCall,
       panPropsTheory.eval_upd_clock_eq,call_FFI_def,
       panPropsTheory.opt_mmap_eval_upd_clock_eq,
       empty_locals_defs,dec_clock_def]>>
  rpt (PURE_CASE_TAC>>fs[])>>
  simp[LAPPEND_NIL_2ND,GSYM LAPPEND_fromList])
(*
*)
  >~ [‘Call’]>-cheat
(*   (simp[Once evaluate_def,
         panPropsTheory.eval_upd_clock_eq,call_FFI_def,
         panPropsTheory.opt_mmap_eval_upd_clock_eq,
         empty_locals_defs,dec_clock_def]>>
    fs[mrec_Call]>>
    rpt (CASE_TAC>>fs[])>>
    TRY (qpat_x_assum ‘∀a b. _ ≠ _’
              (qspec_then ‘0’ assume_tac o SRULE [Once SWAP_FORALL_THM])>>
         fs[FUNPOW]>>NO_TAC)>>
  simp[h_handle_call_ret_def]
*)
  >~ [‘DecCall’]>-cheat
  >~ [‘While’]>-cheat
  >~ [‘Dec’]>-cheat
  >~ [‘Seq’]>-cheat
  >~ [‘If’]>-
   (simp[Once evaluate_def,mrec_If,
         panPropsTheory.eval_upd_clock_eq,
         LAPPEND_NIL_2ND,
         empty_locals_defs,dec_clock_def]>>
(*    fs[mrec_If]>>*)
    rpt (CASE_TAC>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    simp[LAPPEND_NIL_2ND,GSYM LAPPEND_fromList]
    >- (last_x_assum mp_tac>>
        simp[evaluate_def,
             panPropsTheory.eval_upd_clock_eq]>>rw[]>>fs[]>>
        fs[mrec_If]>>
        
    




cheat>>
  simp[Once evaluate_def,mrec_prog_simps,mrec_ShMemLoad,
         mrec_ShMemStore,
         panPropsTheory.eval_upd_clock_eq,call_FFI_def,
         LAPPEND_NIL_2ND,sh_mem_load_def,sh_mem_store_def,
         panPropsTheory.opt_mmap_eval_upd_clock_eq,
         empty_locals_defs,dec_clock_def]>>
  rpt (CASE_TAC>>fs[])>>
  simp[LAPPEND_NIL_2ND,GSYM LAPPEND_fromList]




  TRY (simp[Once evaluate_def,mrec_prog_simps,
            panPropsTheory.eval_upd_clock_eq,
            empty_locals_defs,dec_clock_def]>>
       rpt (CASE_TAC>>fs[])>>NO_TAC)
  >- (
  simp[Once evaluate_def,mrec_Dec,
       panPropsTheory.eval_upd_clock_eq,
       empty_locals_defs,dec_clock_def]>>
  rpt (CASE_TAC>>fs[])>>
  pairarg_tac>>fs[]>>
  qrefine ‘SUC n’>>simp[trace_prefix0_def]>>
  qpat_x_assum ‘_ ⇒ _’ mp_tac>>
  impl_tac >- (
    last_x_assum mp_tac>>once_rewrite_tac[evaluate_def]>>
    simp[panPropsTheory.eval_upd_clock_eq]>>rw[]>>
    first_x_assum $ qspec_then ‘k'’ assume_tac>>fs[]>>
    pairarg_tac>>fs[])>>rw[]>>
  qexists ‘n’>>fs[PULL_FORALL]>>strip_tac>>strip_tac>>
  Cases_on ‘m’>>simp[trace_prefix0_def]>>gvs[])
  >- (
  simp[Once evaluate_def,mrec_ShMemLoad,
       panPropsTheory.eval_upd_clock_eq,
       empty_locals_defs,dec_clock_def]>>
  rpt (CASE_TAC>>fs[])>>
  last_x_assum mp_tac>>
  simp[evaluate_def,sh_mem_load_def,empty_locals_defs]>>
  simp[panPropsTheory.eval_upd_clock_eq,call_FFI_def]>>
  rpt (CASE_TAC>>fs[])>>
  qexists ‘SUC (SUC n)’>>fs[trace_prefix0_def]>>
  rw[]>>
  CASE_TAC>>simp[trace_prefix0_def]>>
  Cases_on ‘n'’>>simp[trace_prefix0_def])
  >- ((* ShMemStore *)
  simp[Once evaluate_def,mrec_ShMemStore,
       panPropsTheory.eval_upd_clock_eq,
       empty_locals_defs,dec_clock_def]>>
  rpt (CASE_TAC>>fs[])>>
  last_x_assum mp_tac>>
  simp[evaluate_def,sh_mem_store_def,empty_locals_defs]>>
  simp[panPropsTheory.eval_upd_clock_eq,call_FFI_def]>>
  rpt (CASE_TAC>>fs[])>>
  qexists ‘SUC (SUC n)’>>fs[trace_prefix0_def]>>
  rw[]>>
  CASE_TAC>>simp[trace_prefix0_def]>>
  Cases_on ‘n'’>>simp[trace_prefix0_def])
  >- ((* Seq *)
  simp[Once evaluate_def,mrec_Seq,
       panPropsTheory.eval_upd_clock_eq,
       empty_locals_defs,dec_clock_def]>>
  rpt (CASE_TAC>>fs[])>>
  first_x_assum mp_tac>>
  simp[evaluate_def,empty_locals_defs]>>
  rpt (pairarg_tac>>fs[])>>
  CASE_TAC>>fs[]
  >- ((* NONE *)
    Cases_on ‘evaluate(c2,s1)’>>
    imp_res_tac panPropsTheory.evaluate_add_clock_eq>>fs[]>>
(*    imp_res_tac evaluate_min_clock>>fs[]>>*)
    rw[]>>
 
   Cases_on ‘s.ffi.io_events = s1.ffi.io_events’>>fs[]
    >- (drule_all io_event_eq_imp_ffi_eq>>strip_tac>>fs[]>>
        rev_drule evaluate_mrec_Ret_weak>>simp[]>>
        disch_then $ qspecl_then [‘bst s’,‘s.clock’] assume_tac>>
        fs[FUNPOW_Tau_bind,trace_prefix0_FUNPOW_Tau]>>res_tac>>
        simp[GSYM FUNPOW]>>
        qrefine ‘SUC n'''’>>simp[trace_prefix0_def]>>
        fs[trace_prefix0_FUNPOW_Tau]>>
        qexists ‘n' + SUC n''’>>simp[]>>rw[]>>
(*        ‘SUC (n' + n'') - n'' = SUC n'’by gvs[]>>
        pop_assum (fn h => rewrite_tac[h])>>
        simp[trace_prefix0_def]>>
        strip_tac>>*)
        Cases_on ‘m’>>simp[trace_prefix0_def]>>gvs[]>>
        simp[trace_prefix0_FUNPOW_Tau])>>
(*        Cases_on ‘n-n''’>>simp[trace_prefix0_def])>>*)
    rev_drule evaluate_mrec_Vis_weak>>simp[]>>rw[]>>
    simp[GSYM FUNPOW_SUC]>>
    fs[FUNPOW_Tau_bind,trace_prefix0_FUNPOW_Tau]>>
    imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    fs[IS_PREFIX_APPEND]>>gvs[]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (pairarg_tac>>fs[])>>

    qexists ‘n’>>fs[]
    qrefine ‘SUC n'''’>>simp[trace_prefix0_def]>>
    simp[trace_prefix0_FUNPOW_Tau]>>


    Cases_on ‘q ≠ SOME TimeOut’>>fs[]
    >- (qrefine ‘SUC n''’>>simp[trace_prefix0_def]>>
        




Cases_on ‘∃fe. q = SOME (FinalFFI fe)’>>fs[]
      
    rpt (CASE_TAC>>fs[])>>

        >- (gvs[]>>
        mp_tac (Q.SPECL [‘c2’,‘s1’] panPropsTheory.evaluate_add_clock_io_events_mono>>


  qexists ‘SUC (SUC n)’>>fs[trace_prefix0_def]>>
  rw[]>>
  CASE_TAC>>simp[trace_prefix0_def]>>
  Cases_on ‘n'’>>simp[trace_prefix0_def])
  


  qpat_x_assum ‘_ ⇒ _’ mp_tac>>
  impl_tac >- (
    last_x_assum mp_tac>>once_rewrite_tac[evaluate_def]>>
    simp[panPropsTheory.eval_upd_clock_eq]>>rw[]>>
    first_x_assum $ qspec_then ‘k'’ assume_tac>>fs[]>>
    pairarg_tac>>fs[])>>rw[]>>
  qexists ‘n’>>fs[PULL_FORALL]>>strip_tac>>strip_tac>>
  Cases_on ‘m’>>simp[trace_prefix0_def]>>gvs[])



  >- (
  simp[Once evaluate_def,mrec_prog_simps,
            panPropsTheory.eval_upd_clock_eq,
            empty_locals_defs,dec_clock_def]>>
       rpt (CASE_TAC>>fs[])>>


)


QED

Theorem unbounded_trace_prefix:
  ¬(∀k'. (SND(evaluate(p,s))).ffi.io_events
         = (SND(evaluate(p,s with clock:=s.clock + k'))).ffi.io_events) ⇒
  ∃n. (SND (evaluate (p, s))).ffi.io_events ≼
      s.ffi.io_events ++
      FST (trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s)):'a ptree))
Proof
  MAP_EVERY qid_spec_tac [‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]
  >~ [‘ExtCall’]>-cheat
  >~ [‘Call’]>-cheat
  >~ [‘DecCall’]>-cheat>>
  TRY (simp[Once evaluate_def,mrec_prog_simps,
            panPropsTheory.eval_upd_clock_eq,
            empty_locals_defs,dec_clock_def]>>
       rpt (CASE_TAC>>fs[])>>NO_TAC)
  >- (
  


QED

Theorem timeout1:
  (∀k. ∃s'. evaluate(p,s with clock := k) = (SOME TimeOut,s')) ⇒
  let t = mrec h_prog (h_prog (p,s)) in
    t = spin ∨
    (∀n. ∃n'. trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state) t

Theorem mrec_evaluate_eq:
  ∃n.
    (SND (evaluate (p,s with clock := k))).ffi.io_events =
    FST (trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state)
                       (mrec h_prog (h_prog (p,bst s))))
Proof



cheat
QED

(* move *)
Theorem lprefix_rel_refl:
  lprefix_rel ls ls
Proof
  rw[lprefix_rel_def]>>
  pop_assum $ irule_at Any>>
  irule LPREFIX_REFL
QED

Theorem evaluate_mrec_lprefix_rel:
   lprefix_rel
     (IMAGE
        (λk. fromList (SND (evaluate (p,s with clock := k))).ffi.io_events)
        𝕌(:num))
     (IMAGE
        (λn.
             fromList
               (FST
                  (trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state)
                     (mrec h_prog (h_prog (p,bst s)))))) 𝕌(:num))
Proof
  simp[lprefix_rel_def]>>rw[]>>simp[PULL_EXISTS]>>
  mp_tac (Q.SPECL [‘s’,‘p’,‘k’] (GEN_ALL mrec_evaluate_eq))>>rw[]>>
  simp[]>>irule_at Any LPREFIX_REFL
QED

Theorem mrec_evaluate_lprefix_rel:
              lprefix_rel
          (IMAGE
             (λn.
                  fromList
                    (FST
                       (trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state)
                          (mrec h_prog (h_prog (p,bst s)))))) 𝕌(:num))
          (IMAGE
             (λk.
                  fromList
                    (SND (evaluate (p,s with clock := k))).ffi.io_events)
             𝕌(:num))
Proof
  simp[lprefix_rel_def]>>rw[]>>simp[PULL_EXISTS]>>
  mp_tac (Q.SPECL [‘s’,‘p’,‘k’] (GEN_ALL mrec_evaluate_eq))>>rw[]>>
  simp[]>>irule_at Any LPREFIX_REFL
QED

Theorem divergence_lemma:
  LUB (IMAGE (λk. fromList ((SND (evaluate (p,s with clock := k))).ffi.io_events)) UNIV)
  = LUB (IMAGE (λn. fromList (FST (trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p, bst s)))))) UNIV)
Proof
  irule IMP_build_lprefix_lub_EQ>>
  irule_at Any evaluate_io_events_lprefix_chain>>
  irule_at Any trace_prefix0_lprefix_chain>>
  simp[mrec_evaluate_eq]
  irule_at Any evaluate_mrec_lprefix_rel>>
  irule_at Any mrec_evaluate_lprefix_rel
QED



Theorem trace_prefix0_itree_bind:
  FST (trace_prefix0 n (x,x') (itree_bind t1 k))
  = X
Proof
  map_every qid_spec_tac [‘x’,‘x'’,‘t1’,‘k’,‘n’]>>
  completeInduct_on ‘n’>>
  Cases_on ‘n’>>simp[trace_prefix0_def]>-cheat>>
  rw[]>>
  Cases_on ‘∃t'. strip_tau t1 t'’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      Cases_on ‘t'’>>fs[FUNPOW_Tau_bind,trace_prefix0_FUNPOW_Tau]
      >- (‘n < n'’ by cheat >>fs[]>>
          ‘SUC n' - n = SUC (n' - n)’ by simp[]>>fs[]>>
          CASE_TAC>>
          pairarg_tac>>fs[]>>
          CASE_TAC>>

  
  
QED

Theorem trace_prefix0_simp[simp]:
  FST (trace_prefix0 n (x,x') (itree_bind (t:'a ptree)
              (λa.
                     Ret
                       (INR
                          (case a of
                             INL v => (SOME Error,bst s)
                           | INR (res,s') => (res,s')))))) =
  FST (trace_prefix0 m (x,x') t)
Proof
  Cases_on ‘∃t'. strip_tau t t'’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      Cases_on ‘t'’>>fs[FUNPOW_Tau_bind,trace_prefix0_FUNPOW_Tau]>>
      Cases_on ‘m- n'’>>fs[]
      >- (Cases_on ‘n-n'’>>fs[]>>
          CASE_TAC>>fs[]
          >- (pairarg_tac>>fs[]>>
              CASE_TAC>>fs[]

cheat






QED
  
Theorem trace_prefix0_Seq_append:
(*  evaluate (p,s) = (NONE,s) ⇒*)
  FST (trace_prefix0 n (or,ffi_st) ((mrec h_prog (h_prog (Seq p q,bst s))):'a ptree)) =
  FST (trace_prefix0 m (or,ffi_st) ((mrec h_prog (h_prog (p,bst s))):'a ptree)) ++
  FST (trace_prefix0 m' (or,ffi_st) X)
Proof
  simp[mrec_Seq]>>
  Cases_on ‘n’>>simp[FUNPOW_SUC,trace_prefix0_def]>>
  Cases_on ‘mrec h_prog (h_prog (p,bst s)):'a ptree’>>fs[]

  >- (imp_res_tac mrec_Ret_INR>>fs[]>>rw[]>>
      Cases_on ‘y’>>fs[]>>
      Cases_on ‘q'’>>fs[]>>
  Cases_on ‘n'’>>simp[FUNPOW_SUC,trace_prefix0_def]>>


      fs[itree_bind_thm]>>

fs[]



QED
  


Theorem evaluate_trace_prefix:
  evaluate (p, s) = (res,s') ∧ res ≠ SOME TimeOut ⇒
  ∃n. s'.ffi.io_events =
      s.ffi.io_events ++ 
             (FST (trace_prefix0 n (s.ffi.oracle,s.ffi.ffi_state)
                           (mrec h_prog (h_prog (p,bst s)))))
Proof
  MAP_EVERY qid_spec_tac [‘s'’,‘res’,‘s’, ‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  imp_res_tac panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>
  qpat_x_assum ‘evaluate _ = _’ mp_tac>>
  simp[Once evaluate_def]>>
  rw[]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>

TRY (simp[mrec_prog_nonrec]>>
  gvs[AllCaseEqs()]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  simp[Once itree_unfold]>>gvs[]>>NO_TAC)

>- ((* Dec *)
  simp[mrec_Dec]>>
  gvs[AllCaseEqs()]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  qrefine ‘SUC n'’>>
  simp[trace_prefix0_def]>>
  qmatch_goalsub_abbrev_tac ‘itree_bind t X’>>
  ‘∀a. ∃x. strip_tau (X a) (Ret (INR x))’
    by rw[Abbr‘X’]>>
  irule (GSYM trace_prefix0_bind_Ret)>>simp[])
>- ((* ShMemLoad *)
  simp[mrec_ShMemLoad]>>fs[sh_mem_load_def,call_FFI_def]>>
  gvs[AllCaseEqs(),empty_locals_defs]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  qrefine ‘SUC n'’>>
  simp[trace_prefix0_def]>>
  qrefine ‘SUC n'’>>
  simp[trace_prefix0_def])
  >- (simp[mrec_ShMemStore]>>fs[sh_mem_store_def,call_FFI_def]>>
      gvs[AllCaseEqs(),empty_locals_defs]>>
      rpt (pairarg_tac>>fs[])>>gvs[]>>
      qrefine ‘SUC n'’>>
      simp[trace_prefix0_def]>>
      qrefine ‘SUC n'’>>
      simp[trace_prefix0_def])
  >- (simp[mrec_Seq]>>
      gvs[AllCaseEqs(),empty_locals_defs]>>
      rpt (pairarg_tac>>fs[])>>gvs[]>>
      qrefine ‘SUC n'’>>
      simp[trace_prefix0_def]>>
      qrefine ‘SUC n'’>>
      simp[trace_prefix0_def])


  qmatch_goalsub_abbrev_tac ‘itree_bind t X’>>
  ‘∀a. ∃x. strip_tau (X a) (Ret (INR x))’
    by rw[Abbr‘X’]>>
  irule (GSYM trace_prefix0_bind_Ret)>>simp[])


  

    Cases_on ‘n’>>
    >- (qexists ‘0’>>fs[trace_prefix_def])>>

       fs[trace_prefix_def]


  gvs[]>>

  TRY (drule panPropsTheory.evaluate_io_events_mono>>strip_tac)>>
  fs[LPREFIX_APPEND]>> (* why APPEND?? *)
  TRY (simp[GSYM LAPPEND_fromList]>>
       simp[Once LAPPEND_ASSOC]>>
       simp[LFINITE_fromList, LAPPEND11_FINITE1]>>
       gvs[AllCaseEqs()]>>rpt (pairarg_tac>>gvs[])>>NO_TAC)


QED
                        
Theorem divergence_lemma0:
  (∀k. FST (evaluate (p, s with clock := k)) = SOME TimeOut) ⇒
    (mrec h_prog (h_prog (p,bst s)) = spin :'a ptree)
Proof
  map_every qid_spec_tac [‘s’,‘p’]>>
(*  recInduct evaluate_ind>>rw[]>>*)
  Induct>>rw[]>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>
  simp[mrec_prog_nonrec,Once mrec_While,mrec_If]>>
  fs[panPropsTheory.eval_upd_clock_eq,empty_locals_defs]>>
  rpt (CASE_TAC>>fs[])>>
  rpt (pairarg_tac>>fs[])>>
  TRY (rpt (FULL_CASE_TAC>>
            fs[empty_locals_defs,set_var_defs,
               panPropsTheory.opt_mmap_eval_upd_clock_eq1])>>NO_TAC)>>
  fs[panPropsTheory.eval_upd_clock_eq,empty_locals_defs,set_var_defs]
  
(* TRY (rename1 ‘SharedMem _’>>rpt (FULL_CASE_TAC>>fs[]))*)

  (* Dec *)
  >- (last_x_assum $ qspec_then ‘s with locals := s.locals |+ (m,x)’ mp_tac>>
      impl_tac>-
       (strip_tac>>
        first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
        pairarg_tac>>fs[])>>
      rw[]>>fs[spin_bind]>>irule (GSYM spin))

  (* Seq *)
  >- (Cases_on ‘∀k. FST (evaluate (p,s with clock := k)) = SOME TimeOut’
      >- (res_tac>>fs[spin_bind]>>irule (GSYM spin))>>
      fs[]>>
      Cases_on ‘evaluate (p, s with clock := k)’>>fs[]>>
      first_assum $ qspec_then ‘k’ mp_tac>>
      first_assum (fn h => rewrite_tac[h])>>simp[]>>
      CASE_TAC>>rw[]>>
      last_x_assum kall_tac>>
      Cases_on ‘evaluate (p',r)’>>fs[]>>
      rev_drule evaluate_min_clock>>rw[]
      last_x_assum $ qspec_then ‘r with clock := 0’ mp_tac>>
      impl_tac >-
       (strip_tac>>simp[]>>
        last_x_assum $ qspec_then ‘k'+ k''’ assume_tac>>
        drule panPropsTheory.evaluate_add_clock_eq>>rw[]>>
        first_assum $ qspec_then ‘k''’ assume_tac>>
        fs[])>>rw[]>>
cheat

(* If *)
  >- (res_tac>>fs[spin_bind]>>irule (GSYM spin))
  >- (res_tac>>fs[spin_bind]>>irule (GSYM spin))
>- cheat
  >- (rpt (FULL_CASE_TAC>>fs[spin_bind])>>irule (GSYM spin))
  >- (last_x_assum $ qspec_then ‘1’ assume_tac>>fs[])

(* Call *)
  >- (rpt (FULL_CASE_TAC>>fs[empty_locals_defs,set_var_defs,dec_clock_def,
                             panPropsTheory.opt_mmap_eval_upd_clock_eq1])>>
      Cases_on ‘evaluate (q, s with locals := r)’>>fs[]>>
      first_x_assum $ qspec_then ‘SUC s.clock’ assume_tac>>fs[]>>
      ‘s with <|locals := r; clock := s.clock|> = s with locals := r’
      by simp[state_component_equality]>>gvs[]>>
      rpt (FULL_CASE_TAC>>fs[])
      gvs[]

      gvs[panPropsTheory.eval_upd_clock_eq]>>

  >- rpt (FULL_CASE_TAC>>fs[empty_locals_defs,set_var_defs])





)>>
      rw[]>>fs[spin_bind]>>irule (GSYM spin))
  
  
   

last_x_assum $ qspec_then ‘s with locals := s.locals |+ (v,x)’ mp_tac>>
      impl_tac>- (gvs[]>>strip_tac>>
                  last_x_assum $ qspec_then ‘k’ assume_tac>>
                  pairarg_tac>>fs[])>>
      strip_tac>>fs[spin_bind]>>irule (GSYM spin))

(* Seq *)
      (Cases_on ‘∃h. strip_tau (mrec h_prog (h_prog (p,bst s)):'a ptree) (h:'a ptree)’>>fs[]
       >- (Cases_on ‘h’>>fs[]>>imp_res_tac strip_tau_FUNPOW>>
           imp_res_tac mrec_FUNPOW_Ret_INR>>fs[FUNPOW_Tau_bind]>>
           rpt (FULL_CASE_TAC>>fs[])>>

           >- (imp_res_tac mrec_Ret_evaluate_weak>>fs[]>>
               first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
               ‘ext (bst s) k s.ffi = s with clock := k’
                 by simp[bst_def,ext_def,state_component_equality]>>fs[]>>
               ‘mrec h_prog (h_prog (p',bst (ext r k' s.ffi))) = spin’
                 by (first_x_assum $ qspec_then ‘ext r k' s.ffi’ mp_tac>>
                     impl_tac>-
                      (strip_tac>>
                       Cases_on ‘k''≤ k'’>>fs[]
                       >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
                           first_x_assum $ qspec_then ‘k-p''’ mp_tac>>fs[]>>
                           imp_res_tac 
                           
)>>
                     

first_x_assum irule
               ‘∃t. evaluate (p',ext r k' s.ffi) = (SOME TimeOut,t)’
               by (first_x_assum $ qspec_then ‘k’ mp_tac>>fs[])>>

       fs[itree_bind_thm]>>
       rpt (CASE_TAC>>fs[])>>
       TRY (imp_res_tac mrec_Ret_INR>>gvs[])
       >- (imp_res_tac mrec_Ret_evaluate>>fs[]>>
           first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
           first_assum $ qspec_then ‘k’ assume_tac>>
           ‘ext (bst s) k s.ffi = s with clock := k’
             by simp[bst_def,ext_def,state_component_equality]>>fs[]>>
           gvs[]>>
           first_x_assum $ qspec_then ‘ext r k' s.ffi’ mp_tac>>
           impl_tac>-
            (rw[]>>
             Cases_on ‘’
             
           



QED

Theorem non_divergence_lemma:
  (∃k res t. evaluate (p, s with clock := k) = (res,t) ∧ res ≠ SOME TimeOut) ⇔
    (mrec h_prog (h_prog (p, bst s))):'a ptree ≠ spin
Proof
  simp[EQ_IMP_THM,PULL_EXISTS]>>rw[]
  >- (strip_tac>>


  >- (Cases_on ‘∃h:'a ptree. strip_tau (mrec h_prog (h_prog (p,bst s))) h’>>fs[]
      >- (Cases_on ‘h’>>imp_res_tac strip_tau_FUNPOW>>fs[]
          >- (imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
              rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>fs[]>>
              imp_res_tac mrec_Ret_evaluate_weak>>
              first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>fs[]>>
              qexists ‘k’>>
              ‘ext (bst s) k s.ffi = s with clock :=k’
                by simp[ext_def,bst_def,state_component_equality]>>
              fs[])>>
          cheat)>>
    drule strip_tau_spin>>fs[])
QED         

              
  





(* panSem observational semantics, modified for any prog *)

Definition semantics_prog_def:
  semantics_prog (prog, s) =
  if ∃k. case FST (evaluate (prog,s with clock := k)) of
         | SOME TimeOut => F
         | SOME (FinalFFI _) => F
         | SOME (Return _) => F
         | _ => T
  then Fail
  else
    case some res.
           ∃k t r outcome.
             evaluate (prog, s with clock := k) = (r,t) ∧
             (case r of
              | (SOME (FinalFFI e)) => outcome = FFI_outcome e
              | (SOME (Return _))   => outcome = Success
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

Definition itree_semantics_def:
  

Theorem bounded_trace_eq:
  (∀k'. s.clock < k' ⇒
        (SND(evaluate(prog:'a prog,s))).ffi.io_events
        = (SND(evaluate(prog,s with clock:=k'))).ffi.io_events) ∧
  good_dimindex (:'a) ⇒
  LAPPEND (fromList (s.ffi.io_events)) (stree_trace query_oracle event_filter s.ffi (to_stree (mrec_sem (h_prog (prog,unclock s))))) =
  fromList (SND (evaluate (prog, s))).ffi.io_events
Proof
QED


Theorem itree_Ret_evaluate:
  itree_evaluate (p,s) = Ret (res, t) ⇒
  ∃k ffi k' ffi'. evaluate (p,ext s k ffi) = (res,ext t k' ffi') ∧ res ≠ SOME TimeOut
Proof
  simp[itree_evaluate_def]>>
  simp[Once itree_unfold]>>strip_tac>>
  FULL_CASE_TAC>>fs[]>>
  imp_res_tac mrec_Ret_INR>>fs[]>>
  simp[mrec_Ret_evaluate]
QED

Theorem mrec_Ret_evaluate_weak:
  mrec h_prog (h_prog (p,s)) = FUNPOW Tau n (Ret (INR (res, t))):'a ptree ⇒
  ∃k ffi k' ffi'. evaluate (p,ext s k ffi) = (res,ext t k' ffi') ∧ res ≠ SOME TimeOut
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’>-fs[FUNPOW,mrec_Ret_evaluate]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[itree_evaluate_def,Once evaluate_def,sh_mem_load_def,sh_mem_store_def]
  >~[‘ExtCall’]>-cheat
(*   (pop_assum mp_tac>>simp[Once itree_unfold]>>strip_tac>>
    rpt (PURE_CASE_TAC>>fs[])>>fs[mrec_ExtCall]>>
    gvs[ext_def,call_FFI_def]>>
    FULL_CASE_TAC>>gvs[])*)
  >~[‘While’]>-cheat>>
(*   (pop_assum mp_tac>>simp[Once itree_unfold]>>strip_tac>>
    rpt (PURE_CASE_TAC>>fs[])>>gvs[Once mrec_While,ext_def])>>*)
  pop_assum mp_tac>>gvs[mrec_prog_nonrec,mrec_If,FUNPOW_SUC]>>
  rpt (CASE_TAC>>fs[])>>strip_tac>>
  (**)
  imp_res_tac bind_FUNPOW_Ret>>
  imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
  Cases_on ‘y’>>
  fs[FUNPOW_Tau_bind]>>
  ‘n'' < SUC n'’ by simp[]>>
  res_tac>>
  qexistsl [‘k’,‘ffi’,‘k'’,‘ffi'’]>>fs[]>>
  pairarg_tac>>fs[ext_def]>>gvs[]

(* Seq *)
  imp_res_tac bind_FUNPOW_Ret>>
  imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
  Cases_on ‘y’>>
  fs[FUNPOW_Tau_bind]>>
  rpt (FULL_CASE_TAC>>fs[])
  >- (fs[GSYM FUNPOW]>>fs[FUNPOW_SUC]>>
      Cases_on ‘n'’>-fs[FUNPOW]>>fs[FUNPOW_SUC]>>
      imp_res_tac FUNPOW_Ret_strip>>
      imp_res_tac bind_FUNPOW_Ret>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>gvs[]>>
      Cases_on ‘y’>>
      fs[FUNPOW_Tau_bind]>>fs[GSYM FUNPOW_ADD]>>
      ‘n'' < SUC (SUC n)’ by simp[]>>
      res_tac>>
      qexistsl [‘k’,‘ffi’]>>fs[]>>
      gvs[]>>
      ‘n - n'' < SUC (SUC n)’ by simp[]>>
      res_tac>>
      qexistsl [‘k'’,‘ffi'’]>>fs[]>>


  ‘n'' < SUC n'’ by simp[]>>
  res_tac>>
  qexistsl [‘k’,‘ffi’,‘k'’,‘ffi'’]>>fs[]>>
  pairarg_tac>>fs[ext_def]>>gvs[]

metis_tac[]

)

Theorem itree_Ret_evaluate_weak:
  itree_evaluate (p,s) = FUNPOW Tau n (Ret (res, t)) ⇒
  ∃k ffi k' ffi'. evaluate (p,ext s k ffi) = (res,ext t k' ffi') ∧ res ≠ SOME TimeOut
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’>-simp[FUNPOW,itree_Ret_evaluate]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[itree_evaluate_def,Once evaluate_def,sh_mem_load_def,sh_mem_store_def]
  >~[‘ExtCall’]>-cheat
(*   (pop_assum mp_tac>>simp[Once itree_unfold]>>strip_tac>>
    rpt (PURE_CASE_TAC>>fs[])>>fs[mrec_ExtCall]>>
    gvs[ext_def,call_FFI_def]>>
    FULL_CASE_TAC>>gvs[])*)
  >~[‘While’]>-cheat>>
(*   (pop_assum mp_tac>>simp[Once itree_unfold]>>strip_tac>>
    rpt (PURE_CASE_TAC>>fs[])>>gvs[Once mrec_While,ext_def])>>*)
  pop_assum mp_tac>>simp[Once itree_unfold]>>strip_tac>>
  rpt (CASE_TAC>>fs[])>>
  gvs[mrec_prog_nonrec,mrec_If,FUNPOW_SUC]>>
  rpt (FULL_CASE_TAC>>fs[])
  >- (imp_res_tac itree_bind_ret_inv>>
      imp_res_tac mrec_Ret_INR>>rfs[])


(* Dec *)
  pop_assum mp_tac>>simp[Once itree_unfold]>>
  gvs[mrec_prog_nonrec,mrec_If,FUNPOW_SUC]>>
  rpt (CASE_TAC>>fs[])>>strip_ta
  >- (imp_res_tac itree_bind_ret_inv>>
      imp_res_tac mrec_Ret_INR>>rfs[])
  >- (imp_res_tac itree_bind_ret_inv>>
      imp_res_tac mrec_Ret_INR>>rfs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      Cases_on ‘n'’>>fs[FUNPOW]>>gvs[]
      FULL_CASE_TAC>>fs[]>>


)


  gvs[mrec_prog_nonrec,mrec_If,ext_def,empty_locals_defs]
  >- (FULL_CASE_TAC>>gvs[empty_locals_defs,ext_def])>>
  qexists ‘2’>>fs[]>>qexistsl [‘ffi’,‘1’,‘ffi’]>>fs[dec_clock_def]
QED

(* itree_evaluate ≠ Ret ⇒ evaluate  = (SOME TimeOut, ) *)
Theorem isem_nonret_timeout:
  (∀n x. itree_evaluate (p,s) ≠ FUNPOW Tau n (Ret x)) ⇒
  ∃k ffi s'. evaluate (p,ext s k ffi) = (SOME TimeOut,s')
Proof
  map_every qid_spec_tac [‘s’,‘p’]>>
  Induct>>rw[]>>
  pop_assum mp_tac
  >~[‘ExtCall’]>-cheat
  >~[‘While’]>-cheat>>
  simp[itree_evaluate_def,mrec_prog_nonrec,mrec_If]>>
  rpt (CASE_TAC>>fs[])>>
  simp[Once itree_unfold]>>
  rw[]>>first_x_assum $ qspec_then ‘0’ assume_tac>>
  fs[FUNPOW]



Cases_on ‘∃m y. itree_evaluate (p,s with locals := s.locals |+ (m,x)) = FUNPOW Tau m (Ret y)’
  simp[Once itree_wbisim_cases]


  rpt (CASE_TAC>>fs[])>>

TRY (gvs[ext_def,empty_locals_defs]>>NO_TAC)>>
  simp[Once itree_unfold,evaluate_def]>>

  qexistsl [‘k’,‘ffi’]>>
  pairarg_tac>>gvs[]


(*  simp[semF_mrec_simp]>>
  simp[GSYM semF_def]*)
  qmatch_goalsub_abbrev_tac ‘Vis Y _’>>

  irule EQ_TRANS>>
  qexists ‘Vis Y (itree_unfold
               (λx.
                    case x of
                      Ret r => Ret' (case r of INL l => ARB | INR r => r)
                    | Tau t => Tau' t
                    | Vis e f => Vis' e (λx. f (INL x))) ∘
             (λx'.
                  Tau
                  (case x' of
                     INL outcome =>
                       Ret
                       (INR
                        (SOME
                         (FinalFFI
                          (Final_event (SharedMem MappedRead)
                                       [4w] (word_to_bytes y F) outcome)),
                         empty_locals s))
                   | INR new_bytes =>
                       if LENGTH new_bytes = dimindex (:α) DIV 8 then
                         Ret
                         (INR
                          (NONE,
                           set_var x
                                   (ValWord (word_of_bytes F 0w new_bytes))
                                   s))
                       else
                         Ret
                         (INR
                          (SOME
                           (FinalFFI
                            (Final_event (SharedMem MappedRead)
                                         [4w] (word_to_bytes y F) FFI_failed)),
                           empty_locals s)))))’>>
  rw[] >-
   (simp[o_DEF,Once itree_unfold]>>
    simp[FUN_EQ_THM]>>strip_tac>>
    simp[Once itree_unfold]>>
    rpt (CASE_TAC>>fs[])>>

        simp[Once itree_unfold]>>
        simp[Once itree_unfold]>>


QED




CASE_TAC>>fs[]
(*
Definition semF_def:
  semF = (λx.
            case x of
              Ret r =>
                Ret' (case r of INL l => ARB | INR r => r)
            | Tau t => Tau' t
            | Vis e f => Vis' e (λx. f (INL x)))
End

Theorem semF_simps[simp]:
  (itree_unfold semF (Ret (INL _)) = Ret ARB) ∧
  (itree_unfold semF (Ret (INR r)) = Ret r) ∧
  (itree_unfold semF (Ret r) = (case r of INL l => Ret ARB | INR r => Ret r)) ∧
  (itree_unfold semF (Tau u) = Tau (itree_unfold semF u)) ∧
  (itree_unfold semF (Vis e g) = Vis e (itree_unfold semF o g o INL ))
Proof
  rw[]>>
  simp[Once itree_unfold, semF_def]>>
  simp[Once itree_unfold, semF_def]>>
  rpt (CASE_TAC>>fs[])>>fs[o_DEF]
QED

Theorem semF_mrec_simp:
  semF ((mrec h_prog t):'a ptree) =
  case t of
    Ret (INL l) => Ret' ARB
  | Ret (INR r) => Ret' r
  | Tau u => Tau' (mrec h_prog u)
  | Vis (INL l') g => Tau' (itree_bind (mrec h_prog (h_prog l')) (mrec h_prog o g))
  | Vis (INR r') g => Vis' r' (Tau o mrec h_prog o g o INL)
Proof
  Cases_on ‘t’>>fs[]>>
  rpt (CASE_TAC>>fs[])>>fs[semF_def,mrec_bind,o_DEF]
QED
*)
(******************************)


val temp = TypeBase.case_rand_of “:('a,'b) sum”;

(*    SCONV (GSYM (ISPEC ``Ret`` it))*)


Theorem test:
  FLOOKUP s.locals x = SOME (Val w) ∧ byte_align y ∈ s.sh_memaddrs ⇒
  itree_evaluate (ShMemLoad Op32 x (Const y), ^s) = X
Proof
  strip_tac>>
  simp[itree_evaluate_def,mrec_ShMemLoad]>>
(*  simp[GSYM semF_def]>>*)
  fs[nb_op_def,eval_def]>>
  simp[Once itree_unfold]>>
  simp[o_DEF]>>
  simp[Once itree_unfold]>>
  simp[Once itree_unfold]>>

QED

Theorem test:
  FLOOKUP s.locals x = SOME (Val w) ∧ byte_align y ∈ s.sh_memaddrs ⇒
  mrec h_prog (h_prog (ShMemLoad Op32 x (Const y), ^s)) = X
Proof
  strip_tac>>
  simp[itree_evaluate_def,h_prog_def,h_prog_sh_mem_load_def]>>
  fs[nb_op_def,eval_def]>>
  simp[o_DEF]>>
  simp[Once itree_unfold]>>
  simp[o_DEF]>>
  simp[Once itree_unfold]>>
QED

Theorem test:
  FLOOKUP s.locals x = SOME (Val w) ∧ byte_align y ∈ s.sh_memaddrs ⇒
  itree_evaluate (Seq (ShMemLoad Op32 x (Const y)) (Assign n (Const y)), ^s) = X
Proof
  strip_tac>>
  simp[itree_evaluate_def,mrec_Seq]>>
  simp[Once itree_unfold]>>
  simp[itree_evaluate_def,mrec_ShMemLoad,mrec_Seq]>>
  fs[nb_op_def,eval_def]>>
  simp[Once itree_unfold]>>

  simp[itree_evaluate_def,mrec_ShMemLoad,mrec_Seq,mrec_Assign]>>
  simp[Once itree_unfold]>>
  simp[o_DEF]>>
  simp[Once itree_unfold]>>
  simp[mrec_bind]>>
  simp[o_DEF]>>cheat
QED

Theorem test:
  is_valid_value s.locals n (ValWord y) ∧
  byte_align x ∈ s.memaddrs ∧ byte_align y ∈ s.memaddrs ⇒
  itree_evaluate (Seq (Assign n (Const y)) (Store (Const y) (Const x)), ^s) = X
Proof
  strip_tac>>
  simp[itree_evaluate_def, SF h_prog_ss, h_prog_seq_def]>>
  fs[eval_def,mrec_bind]>>
  fs[SF h_prog_ss,mem_stores_def,eval_def]>>
  CASE_TAC>>fs[]>>
  simp[Once itree_unfold]>>
  simp[Once itree_unfold]>>
  simp[Once itree_unfold]>>cheat
QED

Theorem test:
  itree_evaluate (Dec x (Const 2w) (While (Var x) (Assign x (panLang$Op Sub [Var x;Const 1w]))) , s:64 bstate) =
Tau
     (Tau
        (Tau
           (Tau
              (Tau
                 (Ret
                    (NONE,
                     s with
                     locals :=
                       res_var (s.locals |+ (x,ValWord 0w))
                         (x,FLOOKUP s.locals x)))))))
Proof

  simp[itree_evaluate_def]>>
  simp[itree_evaluate_def, mrec_Dec]>>
  fs[eval_def,mrec_bind]>>
  fs[Once mrec_While,eval_def,FLOOKUP_UPDATE]>>
  fs[mrec_Assign,eval_def,FLOOKUP_UPDATE]>>
  fs[word_op_def]>>
  fs[is_valid_value_def]>>
  fs[FLOOKUP_UPDATE,shape_of_def]>>
  simp[Once mrec_While,eval_def]>>
  simp[mrec_bind,FLOOKUP_UPDATE]>>
  fs[mrec_Assign,eval_def,FLOOKUP_UPDATE]>>
  fs[word_op_def]>>
  fs[is_valid_value_def]>>
  fs[FLOOKUP_UPDATE,shape_of_def]>>
  simp[Once mrec_While,eval_def]>>
  simp[mrec_bind,FLOOKUP_UPDATE]>>
  ntac 5 (simp[Once itree_unfold])>>
  simp[Once itree_unfold]
QED

Theorem test:
  itree_evaluate (Dec x (Const 2w)
                       (While (Var x) (Seq (ShMemLoad Op32 y (Var x))
                                           (Assign x (panLang$Op Sub [Var x;Const 1w])))) , s:64 bstate) = X
Proof
  simp[itree_evaluate_def]>>
  fs[eval_def,mrec_bind]>>
  fs[Once mrec_While,eval_def,FLOOKUP_UPDATE]>>
  fs[h_prog_def,h_prog_seq_def,h_prog_sh_mem_load_def]>>
  fs[SF h_prog_ss,eval_def,FLOOKUP_UPDATE]>>
  fs[eval_def,mrec_bind]>>

  IF_CASES_TAC>>fs[nb_op_def]>>
  IF_CASES_TAC>>fs[nb_op_def]>>

  simp[o_DEF]
  ntac 4 (simp[Once itree_unfold])>>
  simp[o_DEF]>>
  simp[Once itree_unfold]
      simp[Once itree_unfold]
     simp[]
QED
Theorem test:
  FLOOKUP s.locals y = SOME (ValWord 1w) ∧ FLOOKUP s.locals x = SOME (ValWord 1w)
  ∧ FLOOKUP s.locals z = SOME (ValWord ad)
  ∧ byte_align ad ∈ s.sh_memaddrs ⇒
  mrec h_prog (h_prog (While (Var x) (ShMemLoad Op32 y (Var z)) , s:64 bstate)) = X : 64 ptree
Proof
  strip_tac>>
  simp[Once mrec_While]>>
  fs[eval_def,mrec_bind,nb_op_def]>>
  simp[mrec_ShMemLoad]>>
  fs[eval_def,mrec_bind,nb_op_def]>>
  simp[Once itree_unfold]>>
  simp[Once itree_unfold]>>
  simp[mrec_ShMemLoad]>>
  fs[eval_def,nb_op_def]>>
  simp[Once itree_unfold]>>
  simp[o_DEF,Once itree_unfold]>>
  CASE_TAC>>fs[]

  fs[Once mrec_While,eval_def,FLOOKUP_UPDATE]>>
  fs[h_prog_def,h_prog_seq_def,h_prog_sh_mem_load_def]>>
  fs[SF h_prog_ss,eval_def,FLOOKUP_UPDATE]>>
  fs[eval_def,mrec_bind]>>

  IF_CASES_TAC>>fs[nb_op_def]>>
  IF_CASES_TAC>>fs[nb_op_def]>>

  simp[o_DEF]
  ntac 4 (simp[Once itree_unfold])>>
  simp[o_DEF]>>
  simp[Once itree_unfold]
      simp[Once itree_unfold]
     simp[]
QED


(******************************)


val th1 = TypeBase.case_rand_of “:('a,'b) sum” |> ISPEC “Ret” |> GSYM;
val th2 = TypeBase.case_rand_of “:('a,'b) prod” |> ISPEC “Ret” |> GSYM;

simp[th1,th2]
val th1 = TypeBase.case_rand_of “:('a,'b) sum”;
val t = “(λa.
     mrec h_prog
          (case a of
             INL v => Ret (INR (SOME Error,s))
           | INR (res,s') =>
               Ret
               (INR
                (res,
                 s' with
                    locals :=
                 res_var s'.locals
                         (y,FLOOKUP s.locals y)))))”



Theorem test:
  (λa.
     mrec h_prog
          (case a of
             INL v => Ret (INR (SOME Error,s))
           | INR (res,s') =>
               Ret
               (INR
                (res,
                 s' with
                    locals :=
                 res_var s'.locals
                         (yy,FLOOKUP s.locals yy)))))
  = X
Proof
  [th1,th2]
QED

Theorem test:
  (λa.
     mrec h_prog
          (case a of
             INL v => Ret (INR (SOME Error,s))
           | INR x =>
               Ret
               (INR
                (FST x,
                 (SND x) with
                    locals :=
                 res_var (SND x).locals
                         (yy,FLOOKUP s.locals yy)))))
  = X
Proof
simp[th1]
QED


Theorem mrec_tail_simp[simp]:
  (mrec h_prog
          (case a of
             INL v => Ret (INR (SOME Error,s))
           | INR (res,s') => Ret (INR (res,s''))):'a ptree)
  = Ret (case a of
                INL v => INR (SOME Error,s)
              | INR (res,s') => INR (res,s''))
Proof
(*  simp[FUN_EQ_THM]>>strip_tac>>*)
  rpt (CASE_TAC>>fs[])
QED

Theorem bind_INR_simp:
  (mrec h_prog (h_prog (p,s)):'a ptree) = Ret x ⇒
  itree_bind (mrec h_prog (h_prog (p,s)):'a ptree)
  (λa.
     Ret (case a of
            INL v => INR (SOME Error,s)
          | INR (res,s') => INR (res,s')))
  = (mrec h_prog (h_prog (p,s)):'a ptree)
Proof
  strip_tac>>
  imp_res_tac mrec_Ret_INR>>fs[]>>
  rpt (CASE_TAC>>fs[])
QED


(* Seq should proceed to the second prog only when the first prog returns with NONE *)

Theorem test:
  FLOOKUP s.locals x = SOME (Val w) ∧ byte_align y ∈ s.sh_memaddrs ⇒
  FST (trace_prefix (SUC (SUC (SUC 0))) (or, x) (itree_evaluate (Seq (ShMemLoad Op32 x (Const y)) (Assign n (Const y)), ^s))) =
  [IO_event (SharedMem MappedRead) [4w] (ZIP (word_to_bytes y F,l))]
Proof
  simp[itree_evaluate_def]>>
  simp[mrec_Seq,mrec_Assign]>>
  simp[eval_def,is_valid_value_def,shape_of_def]>>
  simp[Once itree_unfold]>>
  simp[Once h_prog_def,h_prog_sh_mem_load_def,eval_def,nb_op_def,set_var_def]>>
  simp[Once itree_unfold]>>simp[o_DEF]>>
  simp[Once itree_unfold]>>simp[o_DEF]>>
  rw[]>>
  ‘3 = SUC 2’ by simp[]>>
  pop_assum (fn h => rewrite_tac[h])>>
  simp[trace_prefix_def]>>
  rewrite_tac[TWO]>>
  simp[trace_prefix_def]>>
  (CASE_TAC>>fs[])>>rw[]>>TRY (pairarg_tac>>fs[])>>

  fs[Once itree_unfold]>>
  fs[Once itree_unfold]>>
  FULL_CASE_TAC>>fs[]>>

  pop_assum mp_tac>>rewrite_tac[ONE]>>
  simp[trace_prefix_def]>>rw[]>>cheat>>
  fs[Once itree_unfold]>>
  pop_assum mp_tac>>rewrite_tac[ONE]>>
  simp[trace_prefix_def]>>rw[]>>

  fs[shape_of_def]>>FULL_CASE_TAC>>fs[]>>


Theorem evaluate_trace:
  evaluate (p, ss) = (res,s') ∧
  ss = ext ^s ss.clock ss.ffi ∧ res ≠ SOME TimeOut ∧
  itree_evaluate (p,^s) = Ret (res', s'') ⇒
  res' = res ∧ s' = ext s'' s'.clock s'.ffi
Proof
(*  map_every qid_spec_tac [‘res’,‘s'’,‘x’,‘ffi’,‘s’,‘ss’,‘p’,‘k’]>>
  Induct_on ‘k’>>rw[]>>*)
  map_every qid_spec_tac [‘res'’, ‘res’,‘s'’,‘s''’,‘s’,‘ss’,‘p’]>>
  Induct_on ‘p’>>strip_tac>>rpt gen_tac>>strip_tac
  >~[‘Seq’]>-
   (rpt gen_tac>>strip_tac>>
    fs[itree_evaluate_def, mrec_Seq, mrec_bind]>>
    pop_assum mp_tac>>
    simp[Once itree_unfold])

  >- (fs[evaluate_def,itree_evaluate_def,SF h_prog_ss]>>
      fs[Once itree_unfold]>>gvs[])
  >- (fs[evaluate_def,itree_evaluate_def,mrec_Dec]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[eval_ext]>>
      TRY (pairarg_tac>>fs[])>>
      gvs[eval_ext]>>gvs[]
      fs[Once itree_unfold]>>gvs[])

    fs[evaluate_def]>>
    pairarg_tac>>gvs[]>>simp[]>>
    FULL_CASE_TAC>>fs[]
    >- (res_tac>>fs[]




Theorem evaluate_trace:
  evaluate (p, ss) = (res,s') ∧
  ss = ext ^s k ffi ∧ res ≠ SOME TimeOut ⇒
  ∃n. FST (trace_prefix n (ffi.oracle,x) (itree_evaluate (p,^s))) ++ ss.ffi.io_events = s'.ffi.io_events
Proof
(*  map_every qid_spec_tac [‘res’,‘s'’,‘x’,‘ffi’,‘s’,‘ss’,‘p’,‘k’]>>
  Induct_on ‘k’>>rw[]>>*)
  map_every qid_spec_tac [‘res’,‘s'’,‘x’,‘ffi’,‘s’,‘ss’,‘k’,‘p’]>>
  Induct_on ‘p’>>rw[]
  >~[‘Seq’]>-
   (rw[itree_evaluate_def, mrec_Seq, mrec_bind]>>
    simp[Once itree_unfold]>>
    fs[evaluate_def]>>
    pairarg_tac>>gvs[]>>simp[]>>
    FULL_CASE_TAC>>fs[]
    >- (res_tac>>fs[]


  >~[‘Dec’]>-
   (rw[itree_evaluate_def, mrec_simps,SF h_prog_ss,h_prog_dec_def]>>
    fs[evaluate_def]>>
    CASE_TAC>>fs[mrec_simps]>-gvs[ext_def,Once itree_unfold]>>
    pairarg_tac>>gvs[]>>simp[mrec_bind]>>rfs[]>>
    ‘ext s k ffi with locals := s.locals |+ (m,x') =
     ext (s with locals := s.locals |+ (m,x')) k ffi’
      by simp[ext_def]>>fs[]>>
    res_tac>>
    first_x_assum $ qspec_then ‘x’ strip_assume_tac>>
    irule_at Any EQ_TRANS>>
    first_x_assum $ irule_at Any>>
    qmatch_asmsub_abbrev_tac ‘_ = ext t _ _’>>
    first_x_assum $ qspecl_then [‘n’,‘t’,‘ffi’,‘x’,‘st’,]
    simp[itree_evaluate_def]>>
    qpat_abbrev_tac ‘X = mrec h_prog _’>>
    Cases_on ‘X’>>
    simp[SimpRHS, Once itree_unfold]>>
    simp[itree_bind_thm,trace_prefix_def]

    >- (qexists ‘0’>>simp[trace_prefix_def])
    >- simp[SimpLHS, Once itree_unfold]


  TRY (rw[itree_evaluate_def, mrec_simps,SF h_prog_ss]>>fs[evaluate_def]>>
       rpt (CASE_TAC>>fs[mrec_simps])>>
       simp[Once itree_unfold,trace_prefix_def]>>gvs[ext_def,empty_locals_defs]
       >>NO_TAC)







  qabbrev_tac ‘ss= ext s (SUC k) ffi’>>
  rpt $ pop_assum mp_tac>>
  map_every qid_spec_tac [‘res’,‘s'’,‘x’,‘ffi’,‘k’,‘s’,‘ss’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>

(* SKIP *)
  TRY (rw[itree_evaluate_def, mrec_simps,SF h_prog_ss]>>
       qexists ‘SUC k’>>
       simp[Once itree_unfold,trace_prefix_def]>>
       gvs[ext_def,evaluate_def,Abbr‘s’]>>NO_TAC)

(* Dec *)
      rw[itree_evaluate_def, mrec_simps,SF h_prog_ss,h_prog_dec_def]>>
  CASE_TAC>>fs[evaluate_def,Abbr ‘s’]
  >- (qexists ‘SUC k’>>gvs[Once itree_unfold,mrec_simps,trace_prefix_def])>>
  pairarg_tac>>fs[mrec_simps]>>

  simp[Once itree_unfold,mrec_simps]>>simp[mrec_bind]>>
  res_tac>>
  first_x_assum $ qspecl_then [‘s' with locals := s'.locals |+ (v,x')’,‘ffi’] assume_tac>>
  pop_assum mp_tac>>impl_tac>-fs[ext_def]>>
  ‘st.ffi = s''.ffi’ by gvs[state_component_equality]>>fs[]>>
  disch_then $ qspec_then ‘x’ strip_assume_tac>>
  qexists ‘n’>>
  irule EQ_TRANS>>
  first_x_assum $ irule_at Any>>
  simp[]>>>
  rw[itree_evaluate_def]>>
  qpat_abbrev_tac ‘X = mrec h_prog _’>>
  Cases_on ‘X’>>simp[itree_bind_thm]>>
  simp[SimpRHS,Once itree_unfold]
  >- (CASE_TAC>>simp[trace_prefix_def,mrec_simps]
      >- (simp[Once itree_unfold]>>
          Cases_on ‘n’>>fs[trace_prefix_def]>>
          cheat (* Ret imp [] *))>>
      CASE_TAC>>fs[mrec_simps]>>
      simp[Once itree_unfold]>>
Cases_on ‘n’>>fs[trace_prefix_def]>>
      cheat (* Ret imp [] *))
  >- (simp[Once itree_unfold,mrec_bind]>>
      Cases_on ‘u’>>fs[itree_bind_thm]
      >- (CASE_TAC>>simp[mrec_simps,Once itree_unfold]>>
      simp[Once itree_unfold]>>
      Cases_on ‘n’>>fs[trace_prefix_def]>>
      Cases_on ‘n'’>>fs[trace_prefix_def]>>
      cheat (* Ret imp [] *))
      >- (
>>
  Cases
  simp[h_prog_def,mrec_def]

QED

