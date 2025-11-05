(*
  An itree semantics for Pancake.
*)
Theory pan_itreeSem
Ancestors
  panLang itreeTau panSem panProps
  wordLang ffi
Libs
  preamble

(*****)

Datatype:
  bstate =
    <| locals      : varname |-> 'a v
     ; globals     : varname |-> 'a v
     ; code        : funname |-> ((varname # shape) list # ('a panLang$prog))
                     (* arguments (with shape), body *)
     ; eshapes     : eid |-> shape
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; sh_memaddrs    : ('a word) set
     ; be          : bool
     ; base_addr   : 'a word
     ; top_addr    : 'a word
 |>
End

val s = ``(s:'a pan_itreeSem$bstate)``

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

Definition set_global_def:
  set_global v value ^s =
    (s with globals := s.globals |+ (v,value))
End

Theorem set_global_defs = CONJ panSemTheory.set_global_def set_global_def;

Definition set_kvar_def:
  set_kvar vk v value ^s =
  case vk of Local => set_var v value s | Global => set_global v value s
End

Theorem set_kvar_defs = CONJ panSemTheory.set_kvar_def set_kvar_def;

Definition lookup_kvar_def:
  lookup_kvar vk v ^s =
  case vk of Local => FLOOKUP s.locals v | Global => FLOOKUP s.globals v
End

Theorem lookup_kvar_defs = CONJ panSemTheory.lookup_kvar_def lookup_kvar_def;

Definition is_valid_value_def:
  is_valid_value ^s vk v value =
    case lookup_kvar vk v s of
     | SOME w => shape_of value = shape_of w
     | NONE => F
End

Theorem is_valid_value_defs = CONJ panSemTheory.is_valid_value_def is_valid_value_def;

Theorem kvar_defs2 = LIST_CONJ [is_valid_value_defs,set_kvar_defs,set_var_defs,
                                  set_global_defs, lookup_kvar_defs];

Definition eval_def:
  (eval ^s (Const w) = SOME (ValWord w)) /\
  (eval s  (Var Local v) = FLOOKUP s.locals v) /\
  (eval s  (Var Global v) = FLOOKUP s.globals v) /\
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
  (eval s TopAddr =
        SOME (ValWord s.top_addr)) /\
  (eval s BytesInWord =
        SOME (ValWord bytes_in_word))
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
  \\ rpt strip_tac \\ imp_res_tac MEM_IMP_exp_size
  \\ TRY (first_x_assum (assume_tac o Q.SPEC `ARB`))
  \\ decide_tac
End

(***************)

Type ev[pp] = “:ffiname # word8 list # word8 list”;

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

Theorem mrec_bind[simp]:
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
  h_prog_dec vname sh e p ^s =
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
  h_prog_assign vk vname e ^s =
   Ret (INR (case eval s e of
             | SOME value =>
                 if is_valid_value s vk vname value
                 then (NONE,set_kvar vk vname value s)
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

val s' = ``(s':'a bstate)``

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
   | SOME (SOME (rk, rt),_) =>
       if is_valid_value s rk rt retv
       then Ret (INR (NONE,set_kvar rk rt retv (s' with locals := s.locals)))
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
              if shape_of exn = sh ∧ is_valid_value s Local evar exn
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
  h_prog_call calltyp fname argexps ^s =
  case OPT_MMAP (eval s) argexps of
   | SOME args =>
      (case lookup_code s.code fname args of
        | SOME (callee_prog,newlocals) =>
           Vis (INL (callee_prog,s with locals := newlocals)) (h_handle_call_ret calltyp s)
        | _ => Ret (INR (SOME Error,s)))
   | _ => Ret (INR (SOME Error,s))
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
  h_prog_deccall rt shape fname argexps prog1 ^s =
  case OPT_MMAP (eval s) argexps of
   | SOME args =>
      (case lookup_code s.code fname args of
        | SOME (callee_prog,newlocals) =>
           Vis (INL (callee_prog,s with locals := newlocals)) (h_handle_deccall_ret rt shape prog1 s)
        | _ => Ret (INR (SOME Error,s)))
   | _ => Ret (INR (SOME Error,s))
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
  h_prog_sh_mem_load op vk v ad ^s =
  case eval s ad of
    SOME (ValWord addr) =>
     (case lookup_kvar vk v s of
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
                                               (NONE, (set_kvar vk v (ValWord (word_of_bytes F 0w new_bytes)) s))
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
                                               (NONE,(set_kvar vk v (ValWord (word_of_bytes F 0w new_bytes)) s))
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
  (h_prog (Dec vname sh e p,s) = h_prog_dec vname sh e p s) ∧
  (h_prog (Assign vk vname e,s) = h_prog_assign vk vname e s) ∧
  (h_prog (Store dst src,s) = h_prog_store dst src s) ∧
  (h_prog (Store32 dst src,s) = h_prog_store_32 dst src s) ∧
  (h_prog (StoreByte dst src,s) = h_prog_store_byte dst src s) ∧
  (h_prog (ShMemLoad op vk v ad,s) = h_prog_sh_mem_load op vk v ad s) ∧
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

Theorem h_prog_simple_defs = LIST_CONJ [
    h_prog_def,
    h_prog_assign_def,
    h_prog_store_def,
    h_prog_store_32_def,
    h_prog_store_byte_def,
    h_prog_raise_def,
    h_prog_return_def]

(******)

Type ptree[pp] = “:((ffi_outcome + word8 list) + α result option # α bstate, ev,
     (ffi_outcome + word8 list) + α result option # α bstate) itree”;

Type fst[pp] = “:(ffiname -> β -> word8 list -> word8 list -> β oracle_result) # β”;

(******)

(* move to itreeTauTheory *)
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
     ; globals      := s.globals
     ; code        := s.code
     ; eshapes     := s.eshapes
     ; memory      := s.memory
     ; memaddrs    := s.memaddrs
     ; sh_memaddrs := s.sh_memaddrs
     ; be          := s.be
     ; ffi         := ffi
     ; base_addr   := s.base_addr
     ; top_addr    := s.top_addr
     ; clock       := k
|>
End

Theorem ext_access[simp]:
  (ext t k ffi).locals = t.locals ∧
  (ext t k ffi).globals = t.globals ∧
  (ext t k ffi).code = t.code ∧
  (ext t k ffi).eshapes = t.eshapes ∧
  (ext t k ffi).memory = t.memory ∧
  (ext t k ffi).memaddrs = t.memaddrs ∧
  (ext t k ffi).sh_memaddrs = t.sh_memaddrs ∧
  (ext t k ffi).be = t.be ∧
  (ext t k ffi).ffi = ffi ∧
  (ext t k ffi).base_addr = t.base_addr ∧
  (ext t k ffi).top_addr = t.top_addr ∧
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
  ext s k ffi with clock := k' = ext s k' ffi ∧
  ext s k ffi with ffi := ffi' = ext s k ffi' ∧
  dec_clock (ext s k f) = ext s (k - 1) f
Proof
  simp[ext_def,dec_clock_def,state_component_equality]
QED

(****)

Definition bst_def:
  bst (s:('a,'b) panSem$state) =
    <| locals      := s.locals
     ; globals     := s.globals
     ; code        := s.code
     ; eshapes     := s.eshapes
     ; memory      := s.memory
     ; memaddrs    := s.memaddrs
     ; sh_memaddrs := s.sh_memaddrs
     ; be          := s.be
     ; base_addr   := s.base_addr
     ; top_addr    := s.top_addr
|>
End

Theorem bst_access[simp]:
  (bst t).locals = t.locals ∧
  (bst t).globals = t.globals ∧
  (bst t).code = t.code ∧
  (bst t).eshapes = t.eshapes ∧
  (bst t).memory = t.memory ∧
  (bst t).memaddrs = t.memaddrs ∧
  (bst t).sh_memaddrs = t.sh_memaddrs ∧
  (bst t).be = t.be ∧
  (bst t).base_addr = t.base_addr ∧
  (bst t).top_addr = t.top_addr
Proof
  rw[bst_def]
QED

Theorem bst_normalise[simp]:
  bst s with locals := x = bst (s with locals := x) ∧
  bst s with globals := x = bst (s with globals := x) ∧
  bst s with memory := m = bst (s with memory := m) ∧
  bst (s with <|locals := x;clock :=k|>) = bst (s with locals := x) ∧
  bst (s with <|globals := x;clock :=k|>) = bst (s with globals := x) ∧
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
  ext (bst s with globals := x) s.clock s.ffi = s with globals := x ∧
  ext (bst s with memory := m) s.clock s.ffi = s with memory := m ∧
  ext (empty_locals (bst s)) s.clock s.ffi = empty_locals s ∧
  ext (bst s) k s.ffi = s with clock := k ∧
  ext (bst s) s.clock ffi = s with ffi := ffi ∧
  ext (bst s) k ffi = s with <|clock := k; ffi := ffi|>
Proof
  simp[bst_def,ext_def,state_component_equality,empty_locals_defs]
QED

Theorem bst_ext_id[simp]:
  bst (ext s t f) = s ∧
  bst (ext s t f with locals := x) = s with locals := x ∧
  bst (ext s t f with globals := x) = s with globals := x ∧
  bst (ext s t f with memory := m) = s with memory := m ∧
  bst (empty_locals (ext s k ffi)) = empty_locals s ∧
  bst (dec_clock (ext s k ffi)) = s
Proof
  simp[bst_def,ext_def,fetch "-" "bstate_component_equality",
       empty_locals_defs,dec_clock_def]
QED

Theorem eval_eq[simp]:
  (s = bst s' ⇒ eval s e = eval s' e) ∧
  (∀t f. s' = ext s t f ⇒ eval s e = eval s' e)
Proof
  rw[]
QED

(***)

Overload mrec_sem = “λp s. mrec h_prog (h_prog (p,s))”

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
  fs[h_prog_simple_defs,h_prog_call_def,h_prog_deccall_def,
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
  rpt (CASE_TAC>>fs[])>>
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

Theorem bind_FUNPOW_Ret:
  itree_bind ht k = FUNPOW Tau n (Ret x) ⇒
  ∃r n' m. ht = FUNPOW Tau n' (Ret r) ∧ k r = FUNPOW Tau m (Ret x) ∧ n = n' + m
Proof
  Cases_on ‘∃t. strip_tau ht t’>>rw[]>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>rw[]>>fs[FUNPOW_Tau_bind]>>
      Cases_on ‘t’>>fs[itree_bind_thm,FUNPOW_Ret_simp])>>
  imp_res_tac strip_tau_spin>>rw[]>>fs[spin_bind]>>
  pop_assum mp_tac>>
  rewrite_tac[Once (Q.SPEC ‘n’ spin_FUNPOW_Tau)]>>rw[]>>
  fs[Tau_INJ,FUNPOW_eq_elim]>>fs[Once spin]
QED

Theorem FUNPOW_Ret_simp2[simp]:
  (FUNPOW Tau n (Ret x) = Ret r ⇔ n = 0 ∧ x = r) ∧
  (Ret r = FUNPOW Tau n (Ret x) ⇔ n = 0 ∧ r = x)
Proof
  Cases_on ‘n’>>simp[FUNPOW_SUC]
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

Theorem itree_bind_cases:
  itree_bind t k = t' ⇔ (∃r n. t = FUNPOW Tau n (Ret r) ∧ t' = FUNPOW Tau n (k r)) ∨
                        (∃a g n. t = FUNPOW Tau n (Vis a g) ∧
                                 t' = FUNPOW Tau n (Vis a (λx. itree_bind (g x) k))) ∨
                         (t = spin ∧ t' = spin)
Proof
  Cases_on ‘∃ht. strip_tau t ht’>>rw[]>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>rw[]>>fs[FUNPOW_Tau_bind]>>
      Cases_on ‘ht’>>fs[itree_bind_thm]>>eq_tac>>rw[]>>
      pop_assum mp_tac>>
      once_rewrite_tac[Q.SPEC ‘SUC n’ spin_FUNPOW_Tau]>>rw[FUNPOW]>>
      fs[Tau_INJ,FUNPOW_eq_elim])>>
  imp_res_tac strip_tau_spin>>eq_tac>>rw[]>>fs[spin_bind]>>
  pop_assum mp_tac>>
  once_rewrite_tac[Q.SPEC ‘SUC n’ spin_FUNPOW_Tau]>>rw[FUNPOW]>>
  fs[Tau_INJ,FUNPOW_eq_elim]
QED

(*** end of move ***)

Theorem mrec_FUNPOW_Ret_INR:
  (mrec h_prog (h_prog (p,s)):'a ptree) = FUNPOW Tau n (Ret x) ⇒ ∃y. x = INR y
Proof
  map_every qid_spec_tac [‘x’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  Cases_on ‘n’>>fs[]
  >- (imp_res_tac mrec_Ret_INR>>metis_tac[])>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘x’,‘s’,‘n’,‘p’]>>
  Induct>>rw[]>>
  TRY (fs[h_prog_def,h_prog_cond_def,h_prog_simple_defs,FUNPOW_SUC,h_prog_dec_def,
          h_prog_sh_mem_load_def,h_prog_sh_mem_store_def]>>
       rpt (FULL_CASE_TAC>>fs[])>>
       imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>NO_TAC)
  >~[‘While’]>-
   (fs[Once mrec_While,AllCaseEqs()]>>
    gvs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind,AllCaseEqs()]>>gvs[]>>
    Cases_on ‘m’>>gvs[FUNPOW_SUC]>>
    first_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
    res_tac>>fs[])
   >~[‘Seq’]>-
   (fs[h_prog_def,h_prog_seq_def,FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    fs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
    Cases_on ‘m’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind])
   >~[‘Call’]>-
   (fs[h_prog_def,h_prog_call_def,FUNPOW_SUC]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rename [‘h_handle_call_ret _ _ r'’]>>
    Cases_on ‘r'’>>fs[h_handle_call_ret_def]>>
    rename1 ‘INR y’>>Cases_on ‘y’>>
    rename1 ‘INR (q',r')’>>Cases_on ‘q'’>>fs[h_handle_call_ret_def]>>
    rename1 ‘INR (SOME x'',_)’>>Cases_on ‘x''’>>
    Cases_on ‘o'’>>fs[h_handle_call_ret_def]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    Cases_on ‘m'’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind])
   >~[‘DecCall’]>-
   (fs[h_prog_def,h_prog_deccall_def,FUNPOW_SUC]>>
    rpt (FULL_CASE_TAC>>fs[])>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind]>>
    rename [‘h_handle_deccall_ret _ _ _ _ r'’]>>
    Cases_on ‘r'’>>fs[h_handle_deccall_ret_def]>>
    rename1 ‘INR y’>>Cases_on ‘y’>>
    rename1 ‘INR (q',r')’>>Cases_on ‘q'’>>fs[h_handle_deccall_ret_def]>>
    rename1 ‘INR (SOME x'',_)’>>Cases_on ‘x''’>>fs[h_handle_deccall_ret_def]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    Cases_on ‘m'’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>fs[FUNPOW_Tau_bind])>>
  fs[h_prog_def,h_prog_ext_call_def,FUNPOW_SUC]>>
  rpt (PURE_FULL_CASE_TAC>>fs[])
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
  simp[h_prog_seq_def,h_prog_def]>>
  AP_TERM_TAC>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])>>
  simp[o_DEF]>>
  AP_TERM_TAC>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_Dec:
  (mrec h_prog (h_prog (Dec x sh e p, s)):'a ptree) =
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
  simp[h_prog_dec_def,h_prog_def]>>
  rpt (CASE_TAC>>fs[])>>
  AP_TERM_TAC>>fs[o_DEF]>>
  simp[FUN_EQ_THM]>>strip_tac>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_Assign:
  (mrec h_prog (h_prog (Assign vk x v, s)):'a ptree) =
  case eval s v of
    SOME v =>
      Ret (INR (if is_valid_value s vk x v then
                  (NONE, set_kvar vk x v s)
                else (SOME Error, s)))
  | _ => Ret (INR (SOME Error, s))
Proof
  simp[h_prog_assign_def,h_prog_def]>>
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
  simp[h_prog_cond_def,h_prog_def]>>
  rpt (CASE_TAC>>fs[])>>simp[o_DEF]>>
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
  simp[h_prog_store_def,h_prog_def]>>
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
  simp[h_prog_store_byte_def,h_prog_def]>>
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
  simp[h_prog_store_32_def,h_prog_def]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_ShMemLoad:
  (mrec h_prog (h_prog (ShMemLoad op vk v addr, s)):'a ptree) =
  case (eval s addr, lookup_kvar vk v s) of
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
                                 set_kvar vk v
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
                              set_kvar vk v
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
  simp[h_prog_sh_mem_load_def,h_prog_def]>>
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
  simp[h_prog_sh_mem_store_def,h_prog_def]>>
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
  simp[h_prog_def,h_prog_return_def]
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
  simp[h_prog_def,h_prog_raise_def]
QED

Theorem mrec_prog_simps =
  LIST_CONJ [mrec_prog_triv,mrec_Return,mrec_Raise,mrec_Dec,mrec_Assign,
             mrec_Store,mrec_Store32,mrec_StoreByte];

Theorem mrec_Call:
 (mrec h_prog (h_prog (Call typ fname aexps,s)):'a ptree) =
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
Proof
  simp[h_prog_def,h_prog_call_def]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_DecCall:
  mrec h_prog (h_prog (DecCall rt sh fname aexps prog,s)):'a ptree =
  (case OPT_MMAP (eval s) aexps of
     NONE => Ret (INR (SOME Error,s))
   | SOME args =>
       case lookup_code s.code fname args of
         NONE => Ret (INR (SOME Error,s))
       | SOME (q,r) =>
           Tau
           (itree_bind (mrec h_prog (h_prog (q,s with locals := r)):'a ptree)
                       (mrec h_prog o (h_handle_deccall_ret rt sh prog s))))
Proof
  simp[h_prog_def,h_prog_deccall_def]>>
  rpt (CASE_TAC>>fs[])
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
                   (if shape_of exn = sh ∧ is_valid_value s Local evar exn
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
       | SOME (SOME (rk,rt), _) =>
              if is_valid_value s rk rt retv
              then Ret (INR (NONE,set_kvar rk rt retv (s' with locals := s.locals)))
              else Ret (INR (SOME Error,s')))
  | INR (res,s') => Ret (INR (res,empty_locals s'))
  | INL _ => Ret (INR (SOME Error,s)):'a ptree
Proof
  simp[oneline h_handle_call_ret_def]>>
  rpt (CASE_TAC>>fs[])
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
  rpt (CASE_TAC>>fs[])
QED

Theorem mrec_ExtCall:
  mrec h_prog (h_prog (ExtCall ffiname cptr clen aptr alen, s)) =
  case (eval s cptr, eval s clen, eval s aptr, eval s alen) of
    (SOME (ValWord c3), SOME (ValWord c2), SOME (ValWord c'), SOME (ValWord c)) =>
      (case read_bytearray c3 (w2n c2) (mem_load_byte s.memory s.memaddrs s.be) of
         SOME x' =>
           (case read_bytearray c' (w2n c) (mem_load_byte s.memory s.memaddrs s.be) of
              SOME x =>
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
  simp[h_prog_def,h_prog_ext_call_def]>>
  rpt (PURE_CASE_TAC>>fs[])
QED

Theorem mrec_prog_nonrec =
  LIST_CONJ [mrec_prog_simps,mrec_ShMemStore,mrec_ShMemLoad,mrec_Seq,
            mrec_Call,mrec_DecCall];


(*** ltree / comp_ffi / div ***)

Definition ltree_def:
  (ltree (fs:'b fst) (t:'a ptree)) =
  itree_iter
  (λ(t,st).
     case t of
       Ret r => Ret (INR r)
     | Tau u => Ret (INL (u,st))
     | Vis (s,c,ws) g =>
         (case (FST fs) s st c ws of
            Oracle_return fs' ws' =>
              if LENGTH ws = LENGTH ws'
              then Ret (INL (g (INL (INR ws')), fs'))
              else Ret (INL (g (INL (INL FFI_failed)),st))
          | Oracle_final outcome => Ret (INL (g (INL (INL outcome)), st))))
  (t,SND fs)
End

Theorem ltree_simps[simp]:
  (ltree fs (Ret r) = Ret r) ∧
  (ltree fs (Tau u) = Tau (ltree fs u)) ∧
  (ltree fs (Vis (s,c,ws) g) =
         (case (FST fs) s (SND fs) c ws of
            Oracle_return fs' ws' =>
              if LENGTH ws = LENGTH ws' then
                Tau (ltree (FST fs,fs') (g (INL (INR ws'))))
              else Tau (ltree fs (g (INL (INL FFI_failed))))
          | Oracle_final outcome =>
              Tau (ltree fs (g (INL (INL outcome))))))
Proof
  rw[]>>simp[ltree_def,Once itree_iter_thm]>>
  CASE_TAC>>simp[itree_bind_thm]>>
  simp[Once ltree_def]>>
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
              Oracle_return fs' ws' =>
                if LENGTH ws = LENGTH ws' then
                  (g (INL (INR ws')), fs')
                else (g (INL (INL FFI_failed)),st)
            | Oracle_final outcome => (g (INL (INL outcome)), st)
    )
    (t,SND fs)
End

Theorem comp_ffi_simps[simp]:
  comp_ffi fs (Ret r) = (Ret r, SND fs) ∧
  comp_ffi fs (Tau t) = comp_ffi fs t ∧
  comp_ffi fs (Vis (s,c,ws) g) =
  case (FST fs) s (SND fs) c ws of
    Oracle_return fs' ws' =>
      if LENGTH ws = LENGTH ws'
      then comp_ffi (FST fs,fs') (g (INL (INR ws')))
      else comp_ffi fs (g (INL (INL FFI_failed)))
  | Oracle_final outcome => comp_ffi fs (g (INL (INL outcome)))
Proof
  rw[comp_ffi_def]>>simp[Once WhileTheory.WHILE] >>
  rw[ELIM_UNCURRY] >>
  PURE_TOP_CASE_TAC >> rw[]
QED        

(***)

Definition div_def:
  div (fs:'b fst) t =
  ∀n r. ltree fs t ≠ FUNPOW Tau n (Ret r):'a ptree
End

Theorem nondiv_eq_Ret[simp]:
  (¬ div fs X) = (∃n r. ltree fs X = FUNPOW Tau n (Ret r):'a ptree)
Proof
  simp[div_def]>>metis_tac[]
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

(********* trace_prefix *********)

Definition trace_prefix_def:
  trace_prefix fs (th:'a ptree) =
  LFLATTEN $ LUNFOLD
  (λ(fst,t). case t of
               Ret r => NONE
             | Tau u => SOME ((fst,u),LNIL)
             | Vis (s,conf,ws) k =>
                 (case (FST fs) s fst conf ws of
                  | Oracle_return fs' ws' =>
                      if LENGTH ws ≠ LENGTH ws'
                      then SOME ((fst, k (INL (INL FFI_failed))),LNIL)
                      else
                        SOME ((fs',k (INL (INR ws'))),[|IO_event s conf (ZIP (ws,ws'))|])
                  | Oracle_final outcome =>
                      SOME ((fst, k (INL (INL outcome))),LNIL)))
  (SND fs,th)
End

Theorem trace_prefix_simps[simp]:
  trace_prefix fs (Ret r) = [||] ∧
  trace_prefix fs (Tau u) = trace_prefix fs u ∧
  trace_prefix fs (Vis (s,c,ws) k) =
    case (FST fs) s (SND fs) c ws of
    | Oracle_return fs' ws' =>
        if LENGTH ws ≠ LENGTH ws'
        then trace_prefix fs (k (INL (INL FFI_failed)))
        else
          IO_event s c (ZIP (ws,ws')):::trace_prefix (FST fs,fs') (k (INL (INR ws')))
    | Oracle_final outcome => trace_prefix fs (k (INL (INL outcome)))
Proof
  rw[trace_prefix_def]>>
  simp[Once LUNFOLD]>>
  rpt (CASE_TAC>>fs[])
QED

Definition trace_prefix0_def:
  trace_prefix0 fs th =
  LFLATTEN $ LUNFOLD
  (λ(fst,t). case t of
               Ret r => NONE
             | Tau u => SOME ((fst,u),LNIL)
             | Vis (s,conf,ws) k =>
                 (case (FST fs) s fst conf ws of
                  | Oracle_return fs' ws' =>
                      if LENGTH ws ≠ LENGTH ws'
                      then SOME ((fst, k (INL FFI_failed)),LNIL)
                      else
                        SOME ((fs',k (INR ws')),[|IO_event s conf (ZIP (ws,ws'))|])
                  | Oracle_final outcome =>
                      SOME ((fst, k (INL outcome)),LNIL)))
  (SND fs,th)
End

Theorem trace_prefix0_simps[simp]:
  trace_prefix0 fs (Ret r) = [||] ∧
  trace_prefix0 fs (Tau u) = trace_prefix0 fs u ∧
  trace_prefix0 fs (Vis (s,c,ws) k) =
    case (FST fs) s (SND fs) c ws of
    | Oracle_return fs' ws' =>
        if LENGTH ws ≠ LENGTH ws'
        then trace_prefix0 fs (k (INL FFI_failed))
        else
          IO_event s c (ZIP (ws,ws')):::trace_prefix0 (FST fs,fs') (k (INR ws'))
    | Oracle_final outcome => trace_prefix0 fs (k (INL outcome))
Proof
  rw[trace_prefix0_def]>>
  simp[Once LUNFOLD]>>
  rpt (CASE_TAC>>fs[])
QED
