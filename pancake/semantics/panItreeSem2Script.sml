(*
An itree semantics for Pancake.
*)
Theory panItreeSem2
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

val mrec_prog_simps =
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

val mrec_prog_nonrec =
  LIST_CONJ [mrec_prog_simps,mrec_ShMemStore,mrec_ShMemLoad,mrec_Seq,
            mrec_Call,mrec_DecCall];


(*** ltree / div ***)

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
      CASE_TAC>>simp[]>>
      CASE_TAC>>simp[])>>
  Cases_on ‘t’>>fs[FUNPOW_SUC]>>
  PairCases_on ‘a’>>simp[]>>
  CASE_TAC>>simp[]>>
  CASE_TAC>>simp[]
QED

Theorem ltree_spin:
  ltree fs spin = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY {(ltree fs spin, spin)|T}’>>
  rw[]>>simp[]>- metis_tac[]>>
  pop_assum mp_tac>>simp[Once spin]>>rw[]>>
  irule_at Any (GSYM spin)>>metis_tac[]
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
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[])
  >- (Cases_on ‘t’ >>fs[itree_bind_thm]
      >- metis_tac[]
      >- metis_tac[]>>
      PairCases_on ‘a’>>fs[]>>
      rpt (CASE_TAC>>fs[])>>
      metis_tac[])>>
  Cases_on ‘t’ >>fs[itree_bind_thm]
  >- metis_tac[]>>
  PairCases_on ‘a'’>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]
QED

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

(* this should be the first to try with div + itree_bind case *)
Theorem div_bind_cases:
  div fs (itree_bind X k:'a ptree) =
  (div fs (X:'a ptree) ∨
   (∃n r. ltree fs X = FUNPOW Tau n (Ret r) :'a ptree ∧
          div (FST fs, SND (comp_ffi fs X)) (k r)))
Proof
  EQ_TAC>>strip_tac
  >- (Cases_on ‘div fs X’ >- simp[] >>
      irule OR_INTRO_THM2>>fs[]>>
      imp_res_tac div_bind2)
  >- simp[]>>
  simp[div_def,FUNPOW_Tau_bind]>>rw[]>>strip_tac>>
  fs[FUNPOW_Ret_simp]>>
  fs[div_def]
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

Theorem div_eq_ltree_spin:
  div fs t ⇔ ltree fs t = spin:'a ptree
Proof
  EQ_TAC >- metis_tac[div_imp_spin]>>
  simp[div_def]>>rw[]>>strip_tac>>
  pop_assum mp_tac>>
  rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
  strip_tac>>gvs[FUNPOW_Ret_simp]
QED

Theorem nondiv_ltree_bind_lemma:
  itree_bind (ltree fs t) (ltree (FST fs,SND (comp_ffi fs t)) ∘ k) =
  FUNPOW Tau n (Ret r) : 'a ptree ⇒
  ∃n' r'.
    ltree fs t = FUNPOW Tau n' (Ret r') : 'a ptree ∧
    ∃n''.
      ltree (FST fs,SND (comp_ffi fs t)) (k r') = FUNPOW Tau n'' (Ret r) : 'a ptree
      ∧ n' + n'' = n
Proof
  strip_tac>>
  Cases_on ‘div fs t’>>fs[]
  >- (imp_res_tac ltree_div_bind>>fs[div_def])>>
  fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]
QED

Theorem nondiv_ltree_bind_lemma':
  itree_bind (ltree fs t) (ltree fs' ∘ k) =
  FUNPOW Tau n (Ret r) : 'a ptree
  ∧ fs' = (FST fs,SND (comp_ffi fs t)) ⇒
  ∃n' r'.
    ltree fs t = FUNPOW Tau n' (Ret r') : 'a ptree ∧
    ∃n''.
      ltree (FST fs,SND (comp_ffi fs t)) (k r') = FUNPOW Tau n'' (Ret r) : 'a ptree
      ∧ n' + n'' = n
Proof
  rw[]>>
  imp_res_tac nondiv_ltree_bind_lemma>>
  gvs[]
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

Theorem comp_ffi_bind[simp]:
  ltree fs t = FUNPOW Tau n (Ret r) ⇒
  comp_ffi fs (itree_bind t k) =
  comp_ffi (FST fs, SND (comp_ffi fs t)) (k r)
Proof
  map_every qid_spec_tac [‘t’,‘fs’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>
  Cases_on ‘t’>>fs[]>>
  PairCases_on ‘a’>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]
QED

Theorem evaluate_invariant_oracle = cj 7 panPropsTheory.evaluate_invariants;

Theorem nondiv_evaluate:
  ltree (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) =
  FUNPOW Tau n (Ret (INR r)) : 'a ptree
  ∧ evaluate (p,s with clock := k) = (res, t) ∧ res ≠ SOME TimeOut ⇒
  res = FST r ∧ bst t = SND r ∧
  t.ffi.ffi_state = SND (comp_ffi (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))))
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘r’,‘k’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>
  rpt gen_tac>>strip_tac>>
  Cases_on ‘p’>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]
  >~ [‘ExtCall’]>-
   (fs[mrec_ExtCall,call_FFI_def]>>
    rpt (PURE_TOP_CASE_TAC>>fs[])>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    gvs[set_var_defs,bst_def,empty_locals_defs])>>
  fs[mrec_prog_simps,mrec_Seq,mrec_If,Once mrec_While,mrec_Call,
     mrec_DecCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
     empty_locals_defs,dec_clock_def,kvar_defs2]>>gvs[FUNPOW_SUC]>>
  TRY (gvs[AllCaseEqs()]>>NO_TAC)
  (* Dec *)
  >- (rpt (CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[FUNPOW_SUC]>>
      Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      FULL_CASE_TAC>>gvs[]>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      rename [‘ltree _ _ = FUNPOW _ _ (Ret (INR (q, r)))’]>>
      qmatch_asmsub_abbrev_tac ‘ltree _ (mrec _ (h_prog (pp, bst ss))) = _’>>
      disch_then $ qspecl_then [‘pp’,‘ss’,‘k’,‘(q,r)’,‘st’,‘res’] mp_tac>>
      simp[Abbr‘ss’,Abbr‘pp’]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* Seq *)
  >- (rpt (pairarg_tac>>fs[])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[FUNPOW_SUC]>>
      (* NONE *)
      Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      (rpt (FULL_CASE_TAC>>fs[])
       >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
           Cases_on ‘n’>>fs[FUNPOW_SUC]>>
           drule nondiv_ltree_bind_lemma'>>simp[]>>
           strip_tac>>fs[FUNPOW_Tau_bind]>>
           drule nondiv_INR>>strip_tac>>gs[]>>
           FULL_CASE_TAC>>fs[]>>gvs[]>>
           (*rename [‘Ret _ = FUNPOW Tau n _’]>>
           Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>*)
           rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
           last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
           disch_then $ drule_at Any>>
           disch_then $ drule_at Any>>
           strip_tac>>gvs[]>>
           rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
           last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
           pop_assum $ assume_tac o GSYM>>fs[]>>
           drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
           fs[]>>
           disch_then $ drule_at Any>>
           disch_then $ drule_at Any>>
           disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
           ‘s1 with clock := s1.clock = s1’
             by simp[state_component_equality]>>
           fs[]>>strip_tac>>
           imp_res_tac comp_ffi_bind>>gvs[]))>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      strip_tac>>res_tac>>fs[]>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* If *)
  >- (rpt (FULL_CASE_TAC>>fs[])>>
      gvs[AllCaseEqs()]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      drule nondiv_INR>>strip_tac>>gs[]>>
      FULL_CASE_TAC>>fs[]>>gvs[]>>
      rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      strip_tac>>gvs[]>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* While *)
  >- (rewrite_tac[Once mrec_While]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>

      rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      strip_tac>>gvs[]>>
      FULL_CASE_TAC>>fs[]>>gvs[]>>
      TRY (imp_res_tac comp_ffi_bind>>gvs[]>>NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      qpat_x_assum ‘_ = SND _’ $ assume_tac o GSYM>>fs[]>>
      qpat_x_assum ‘evaluate (p',_)=_’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      disch_then $ rev_drule_at Any>>
      disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
      ‘s1 with clock := s1.clock = s1’
        by simp[state_component_equality]>>
      fs[]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* Call *)
  >- (
  rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>
  Cases_on ‘k=0’>>fs[]>>
  rename [‘Tau _ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
  drule nondiv_ltree_bind_lemma'>>simp[]>>
  strip_tac>>fs[FUNPOW_Tau_bind]>>
  imp_res_tac nondiv_INR>>fs[]>>gs[]>>
  gvs[]>>
  qpat_x_assum ‘_ = (res,t)’ mp_tac>>
  qpat_abbrev_tac ‘Y = evaluate _’>>
  rpt (TOP_CASE_TAC>>fs[])>>
  rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
  last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
  disch_then $ qspecl_then [‘q’,‘s with locals := r'’] mp_tac>>
  simp[]>>
  disch_then $ drule_at Any>>
  strip_tac>>gvs[]>>
  gvs[mrec_h_handle_call_ret_lemma,o_DEF,kvar_defs2,AllCaseEqs()]>>
  rpt (PURE_TOP_CASE_TAC>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>rw[]>>gvs[]>>
  TRY (imp_res_tac comp_ffi_bind>>gvs[]>>
       rw[]>>gvs[empty_locals_defs,set_var_defs]>>
       NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gvs[]>>
      FULL_CASE_TAC>>fs[]>>
      rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      qpat_x_assum ‘_ = SND _’ $ assume_tac o GSYM>>fs[]>>
      qpat_x_assum ‘evaluate _ = (SOME (Exception _ _), _)’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,s1)=(res,t)’>>
      ‘r''.ffi = s1.ffi’ by simp[Abbr‘s1’]>>fs[]>>
      fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
      disch_then $ rev_drule_at Any>>
      ‘s1 with clock := s1.clock = s1’
        by simp[state_component_equality]>>
      fs[]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* DecCall *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>
      Cases_on ‘k=0’>>fs[]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      gvs[]>>
      qpat_x_assum ‘_ = (res,t)’ mp_tac>>
      qpat_abbrev_tac ‘Y = evaluate _’>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ qspecl_then [‘q’,‘s with locals := r'’] mp_tac>>
      simp[]>>
      disch_then $ drule_at Any>>
      strip_tac>>gvs[]>>
      gvs[mrec_h_handle_deccall_ret_lemma,o_DEF,set_var_defs]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>rw[]>>gvs[]>>
      TRY (imp_res_tac comp_ffi_bind>>gvs[]>>
           rw[]>>gvs[empty_locals_defs,set_var_defs]>>
           NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gvs[]>>
      FULL_CASE_TAC>>fs[]>>
      rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      qpat_x_assum ‘_ = SND _’ $ assume_tac o GSYM>>fs[]>>
      qpat_x_assum ‘evaluate _ = (SOME (Return _), _)’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,s1)=(res,t)’>>
      ‘r''.ffi = s1.ffi’ by simp[Abbr‘s1’]>>fs[]>>
      fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
      disch_then $ rev_drule_at Any>>
      ‘s1 with clock := s1.clock = s1’
        by simp[state_component_equality]>>
      fs[]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  >- (rpt (FULL_CASE_TAC>>fs[])>>gvs[])>>
  (* ShMemLoad / ShMemStore *)
  rpt (TOP_CASE_TAC>>fs[])>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  gvs[set_var_defs,bst_def,AllCaseEqs()]
QED

Theorem nondiv_evaluate':
  ltree fs (mrec h_prog (h_prog (p,bst s))) =
  FUNPOW Tau n (Ret (INR r)) : 'a ptree
  ∧ evaluate (p,s with clock := k) = (res, t) ∧ res ≠ SOME TimeOut ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
  res = FST r ∧ bst t = SND r ∧
  t.ffi.ffi_state = SND (comp_ffi (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))))
Proof
  strip_tac>>
  Cases_on ‘fs’>>gs[]>>
  imp_res_tac nondiv_evaluate>>gvs[]
QED

(**************************)

Theorem evaluate_imp_nondiv:
  evaluate (p,s) = (res,t) ∧ res ≠ SOME TimeOut ⇒
  ∃n. ltree (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘evaluate _ = (_,_)’ mp_tac>>
  simp[Once evaluate_def,mrec_prog_simps]>>strip_tac>>
  TRY (rpt (TOP_CASE_TAC>>fs[empty_locals_defs,kvar_defs2])>>
       qexists ‘0’>>simp[FUNPOW]>>NO_TAC)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      pairarg_tac>>fs[]>>gvs[]>>
      qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>
      gvs[FUNPOW_Tau_bind])
  >- (* shmemload *)
   (simp[mrec_ShMemLoad]>>
    fs[sh_mem_load_def,call_FFI_def,kvar_defs2,AllCaseEqs()]>>
    gvs[bst_def,empty_locals_defs]>>
    metis_tac[FUNPOW])
  >- (* shmemstore *)
   (simp[mrec_ShMemStore]>>
    fs[sh_mem_store_def,call_FFI_def,set_var_defs,AllCaseEqs()]>>
    gvs[bst_def,empty_locals_defs]>>
    metis_tac[FUNPOW])
  >~ [‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    fs[sh_mem_store_def,call_FFI_def,set_var_defs,AllCaseEqs()]>>
    rpt (TOP_CASE_TAC>>fs[])>>
    gvs[empty_locals_defs,bst_def]>>
    metis_tac[FUNPOW])
  >- (* Seq *)
   (rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    simp[mrec_Seq,FUNPOW_Tau_bind]>>
    drule nondiv_evaluate>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘evaluate (c1,_) = (rr,tt)’>>
    disch_then $ qspecl_then [‘tt’,‘rr’,‘s.clock’] mp_tac>>
    ‘s with clock := s.clock = s’ by simp[state_component_equality]>>
    simp[]>>
    fs[]>>strip_tac>>TRY (fs[Abbr‘rr’])>>
    pop_assum $ assume_tac o GSYM>>fs[]>>
    ‘s.ffi.oracle = tt.ffi.oracle’ by
      (irule EQ_SYM>>irule evaluate_invariant_oracle>>metis_tac[])>>
    gvs[FUNPOW_Tau_bind]>>
    simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
    rpt (FULL_CASE_TAC>>fs[]))
   >- (* If *)
    (simp[mrec_If]>>
     rpt (TOP_CASE_TAC>>fs[])>>gvs[FUNPOW_Tau_bind]>>
     metis_tac[FUNPOW,FUNPOW_SUC])
  >- (* While *)
   (simp[Once mrec_While,dec_clock_def]>>
    TOP_CASE_TAC>>fs[]>>
    reverse TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[dec_clock_def,FUNPOW_Tau_bind]>>
    TRY (simp[GSYM FUNPOW_SUC]>>qrefine ‘SUC n'’>>simp[]>>NO_TAC)>>
    qpat_x_assum ‘ltree (s.ffi.oracle,_) _ = _’ assume_tac>>
    drule nondiv_evaluate'>>gvs[]>>
    disch_then $ drule_at Any>>
    simp[]>>strip_tac>>
    pop_assum $ assume_tac o GSYM>>fs[]>>
    ‘(s with clock := s.clock -1).ffi.oracle = s1.ffi.oracle’ by
      (irule EQ_SYM>>irule evaluate_invariant_oracle>>metis_tac[])>>
    gvs[FUNPOW_Tau_bind]>>
    simp[GSYM FUNPOW_SUC]>>rewrite_tac[GSYM FUNPOW_ADD]>>
    metis_tac[FUNPOW_SUC])
  >- (rpt (FULL_CASE_TAC>>fs[])>>
      gvs[dec_clock_def,empty_locals_defs]>>
      metis_tac[FUNPOW])>>
  (* Call / DecCall *)
  simp[mrec_Call,mrec_DecCall]>>
  fs[AllCaseEqs(),kvar_defs2,
     empty_locals_defs,dec_clock_def,FUNPOW_Tau_bind]>>
  rpt (pairarg_tac>>fs[])>>
  simp[mrec_h_handle_call_ret_lemma]>>
  gvs[FUNPOW_Tau_bind]>>
  TRY (qexists ‘0’>>simp[FUNPOW]>>NO_TAC)>>
  drule nondiv_evaluate'>>gvs[]>>
  disch_then $ drule_at Any>>
  strip_tac>>fs[]>>
  pop_assum $ assume_tac o GSYM>>fs[]>>
  ‘(s with <|locals :=newlocals;clock :=s.clock -1|>).ffi.oracle = st.ffi.oracle’ by
    (irule EQ_SYM>>irule evaluate_invariant_oracle>>metis_tac[])>>
  simp[mrec_h_handle_call_ret_lemma,empty_locals_defs,kvar_defs2,
       mrec_h_handle_deccall_ret_lemma]>>
  gvs[FUNPOW_Tau_bind]>>
  TRY (TOP_CASE_TAC>>fs[])>>
  simp[GSYM FUNPOW_SUC]>>rewrite_tac[GSYM FUNPOW_ADD]>>
  metis_tac[FUNPOW_SUC]
QED

Theorem nondiv_not_timeout:
  ltree fs (mrec h_prog (h_prog (p,s))) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree ⇒
  res ≠ SOME TimeOut
Proof
  map_every qid_spec_tac [‘res’,‘fs’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>strip_tac>>
  Cases_on ‘p’
  >~ [‘ExtCall’]>- 
   (fs[mrec_ExtCall,call_FFI_def]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>
    rename [‘_ = FUNPOW Tau n _’]>>
    Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    gvs[set_var_defs,bst_def,empty_locals_defs])>>
  fs[mrec_prog_simps,mrec_Seq,mrec_If,Once mrec_While,mrec_Call,
     mrec_DecCall,
     mrec_ExtCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  rpt (FULL_CASE_TAC>>fs[])>>fs[FUNPOW_SUC]>>
  TRY (rename [‘Tau _ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
       drule nondiv_ltree_bind_lemma'>>
       simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
       imp_res_tac nondiv_INR>>fs[]>>
       FULL_CASE_TAC>>fs[]>>
       rename [‘ltree _ _ = FUNPOW Tau n _’]>>
       qmatch_asmsub_abbrev_tac ‘h_prog (pp,ss)’>>
       qmatch_asmsub_abbrev_tac ‘ltree _ _ = FUNPOW _ n (Ret (INR (q,rr)))’>>
       last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
       first_x_assum $ qspecl_then [‘pp’,‘ss’,‘rr’,‘fs’] assume_tac>>fs[]>>
       gvs[])
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])
      (* NONE *)
      >- (rename [‘_ _ = FUNPOW Tau n _’]>>
          Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
          drule nondiv_ltree_bind_lemma'>>
          simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
          fs[GSYM FUNPOW_ADD]>>gs[]>>
          imp_res_tac nondiv_INR>>fs[]>>
          FULL_CASE_TAC>>fs[]>>
          rename [‘ltree _ _ = FUNPOW Tau n _’]>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>gvs[]>>
          qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (q,rr)))’>>
          first_x_assum $ qspecl_then [‘p0’,‘r’,‘rr’,‘fs'’] assume_tac>>
          gvs[])>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>gvs[]>>
      metis_tac[])
  (* While *)
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      gvs[GSYM FUNPOW_SUC]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      rename [‘ltree (_, SND _ ) _ = FUNPOW Tau n _’]>>
      qmatch_asmsub_abbrev_tac ‘h_prog (While _ _,rr)’>>
      qmatch_asmsub_abbrev_tac ‘h_prog (pp,rr)’>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (qq,tt)))’>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
      first_x_assum $ qspecl_then [‘pp’,‘rr’,‘tt’,‘fs'’] assume_tac>>
      gvs[Abbr‘qq’])
  (* call *)
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      fs[mrec_h_handle_call_ret_lemma]>>
      rename [‘FUNPOW _ n (Ret (INR (res,t)))’]>>
      qpat_x_assum ‘_ = FUNPOW _ n _’ mp_tac>>
      rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>rw[]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      FULL_CASE_TAC>>fs[]>>gvs[]>>
      fs[set_var_defs]>>
      rename [‘ltree (_, SND _ ) _ = FUNPOW Tau n _’]>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (qq,tt)))’>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' (_ _ (_ (pp,rr)))’>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
      first_x_assum $ qspecl_then [‘pp’,‘rr’,‘tt’,‘fs'’] assume_tac>>
      gvs[])
  (* deccall *)
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs]>>
      rename [‘FUNPOW _ n (Ret (INR (res,t)))’]>>
      qpat_x_assum ‘_ = FUNPOW _ n _’ mp_tac>>
      rpt (TOP_CASE_TAC>>fs[])>>rw[]
      >- (fs[]>>‘n'' < SUC n''’ by simp[]>>res_tac)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      FULL_CASE_TAC>>gvs[set_var_defs]>>
      rename [‘ltree (_, SND _ ) _ = FUNPOW Tau n _’]>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (qq,tt)))’>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' (_ _ (_ (pp,rr)))’>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
      first_x_assum $ qspecl_then [‘pp’,‘rr’,‘tt’,‘fs'’] assume_tac>>
      gvs[])>>
  rename [‘_ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  gvs[set_var_defs,bst_def,empty_locals_defs]
QED

Theorem nondiv_imp_evaluate:
  ltree (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree ⇒
    ∃k t'. evaluate (p,s with clock := k) = (res,t')
           ∧ bst t' = t
         ∧ res ≠ SOME TimeOut
Proof
  strip_tac>>
  imp_res_tac nondiv_not_timeout>>
  pop_assum mp_tac>>
  pop_assum mp_tac>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>ntac 2 strip_tac>>
  Cases_on ‘p’
  >~ [‘ExtCall’] >-
   (fs[Once evaluate_def,mrec_ExtCall,call_FFI_def,
       panPropsTheory.eval_upd_clock_eq]>>
    rpt (PURE_CASE_TAC>>fs[])>>gvs[]>>
    gvs[dec_clock_def,empty_locals_defs]>>
    rpt (rename [‘FUNPOW Tau n _’]>>
         Cases_on ‘n’>>gvs[FUNPOW_SUC])>>
    simp[bst_def,empty_locals_defs,set_var_defs])>>
  fs[mrec_prog_simps,mrec_Seq,mrec_If,Once mrec_While,mrec_Call,
     mrec_DecCall,Once evaluate_def,
     mrec_ExtCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
     panPropsTheory.eval_upd_clock_eq,
     sh_mem_load_def,sh_mem_store_def,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  gvs[FUNPOW_SUC]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>gvs[empty_locals_defs,kvar_defs2]>>
       rename [‘Ret _ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>
       TRY (rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>
            rename [‘_ _ = FUNPOW Tau n _’]>>
            Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])>>NO_TAC)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>fs[]>>
      qmatch_asmsub_abbrev_tac ‘h_prog (pp,bst ss)’>>
      qmatch_asmsub_abbrev_tac ‘Ret (INR (res,rr))’>>
      disch_then $ qspecl_then [‘pp’,‘ss’,‘rr’,‘res’] assume_tac>>
      gvs[Abbr‘ss’]>>
      qexists ‘k’>>fs[])
  (* Seq *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])
      >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
          Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
          drule nondiv_ltree_bind_lemma'>>
          simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
          imp_res_tac nondiv_INR>>fs[]>>
          rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
          last_assum $ qspec_then ‘n''’ mp_tac>>
          (impl_tac >- simp[])>>
          disch_then drule>>strip_tac>>fs[]>>
          dxrule evaluate_min_clock>>
          strip_tac>>fs[]>>
          drule_then drule nondiv_evaluate'>>simp[]>>strip_tac>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          imp_res_tac evaluate_invariant_oracle>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          qhdtm_x_assum ‘bst’ $ assume_tac o GSYM>>fs[]>>
          rename [‘ltree _ _ = FUNPOW Tau n _’]>>
          last_x_assum $ qspec_then ‘n’ mp_tac>>
          (impl_tac >- simp[])>>
          disch_then rev_drule>>simp[]>>
          strip_tac>>fs[]>>
          dxrule evaluate_min_clock>>simp[]>>
          strip_tac>>fs[]>>
          qexists ‘k' + k''’>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          disch_then $ qspec_then ‘k''’ assume_tac>>fs[])>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      disch_then drule>>strip_tac>>gvs[]>>
      qexists ‘k’>>simp[])
  >- (rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      Cases_on ‘n'''’>>fs[FUNPOW_SUC]>>gvs[])
  (* While *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[dec_clock_def]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      disch_then drule>>strip_tac>>fs[]>>
      TRY (qexists ‘SUC k’>>fs[]>>NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      dxrule evaluate_min_clock>>
      strip_tac>>fs[]>>
      drule_then drule nondiv_evaluate'>>simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      imp_res_tac evaluate_invariant_oracle>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      rename1 ‘ltree (_,t''.ffi.ffi_state) _ = FUNPOW Tau n _’>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      disch_then drule>>simp[]>>
      strip_tac>>fs[]>>
      dxrule evaluate_min_clock>>simp[]>>
      strip_tac>>fs[]>>
      qexists ‘SUC (k' + k'')’>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘k''’ assume_tac>>fs[])
  (* call *)
  >- (rpt (PURE_CASE_TAC>>fs[])>>gvs[dec_clock_def,empty_locals_defs]>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[]>> 
      fs[mrec_h_handle_call_ret_lemma,kvar_defs2]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      rename [‘_ = FUNPOW Tau n _’]>>
      TRY (last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
           ‘s.ffi = (s with locals := r).ffi’ by simp[]>>
           rename [‘h_prog (q, bst _)’]>>
           disch_then $ qspecl_then [‘q’,‘s with locals := r’] mp_tac>>
           fs[]>>strip_tac>>
           qexists ‘SUC k’>>gvs[bst_def]>>NO_TAC)>>
      TRY (rename [‘Tau _ = FUNPOW Tau n _’]>>
           Cases_on ‘n’>>gvs[FUNPOW_SUC,empty_locals_defs]>>
           drule nondiv_ltree_bind_lemma'>>
           simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
           fs[GSYM FUNPOW_ADD]>>gs[]>>
           imp_res_tac nondiv_INR>>fs[]>>
           rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[])>>
      rename1 ‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’>>
      last_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      rename [‘h_prog (q, bst _)’]>>
      disch_then $ qspecl_then [‘q’,‘s with locals := r’] mp_tac>>
      disch_then $ mp_tac o SIMP_RULE (srw_ss()) []>>
      disch_then drule>>strip_tac>>fs[]>>
      dxrule evaluate_min_clock>>strip_tac>>gvs[]>>
      TRY (qexists ‘SUC k'’>>simp[]>>
           rpt (FULL_CASE_TAC>>fs[])>>gvs[kvar_defs2]>>NO_TAC)>>
      rev_drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      fs[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      imp_res_tac evaluate_invariant_oracle>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      rename1 ‘ltree (_,t''.ffi.ffi_state) _ = FUNPOW Tau n' _’>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>
      (impl_tac >- simp[])>>
      fs[set_var_defs]>>
      TRY (qhdtm_x_assum ‘bst’ $ assume_tac o GSYM)>>fs[]>>
      qpat_x_assum ‘ltree _ _ = FUNPOW _ _ (Ret _)’ assume_tac>>
      qmatch_asmsub_abbrev_tac ‘h_prog (rrr, bst X)’>>
      ‘t''.ffi = X.ffi’ by simp[Abbr‘X’]>>fs[]>>
      disch_then drule>>strip_tac>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>pop_assum kall_tac>>
      strip_tac>>gvs[Abbr‘X’]>>
      qexists ‘SUC (k' + k'')’>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>fs[]>>
      disch_then $ qspec_then ‘k''’ assume_tac>>fs[])
  (* deccall *)
  >- (rpt (PURE_CASE_TAC>>fs[])>>gvs[dec_clock_def,empty_locals_defs]>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[]>> 
      fs[mrec_h_handle_deccall_ret_lemma]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      TRY (last_x_assum $ qspec_then ‘n''’ mp_tac>>simp[]>>
           ‘s.ffi = (s with locals := r).ffi’ by simp[]>>
           rename [‘h_prog (q, bst _)’]>>
           disch_then $ qspecl_then [‘q’,‘s with locals := r’] mp_tac>>
           fs[]>>strip_tac>>
           qexists ‘SUC k’>>gvs[bst_def]>>NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>gvs[FUNPOW_SUC,empty_locals_defs]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[]>>
      rename1 ‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’>>
      last_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      rename [‘h_prog (q, bst _)’]>>
      qpat_x_assum ‘ltree _ _ = FUNPOW _ n (Ret _)’ assume_tac>>
      qmatch_asmsub_abbrev_tac ‘h_prog (pp, bst X)’>>
      disch_then $ qspecl_then [‘pp’,‘X’] mp_tac>>
      ‘X.ffi = s.ffi’ by fs[Abbr‘X’]>>
      pop_assum (fn h => rewrite_tac[h])>>
      disch_then drule>>rw[]>>
      dxrule evaluate_min_clock>>strip_tac>>gvs[]>>
      rev_drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      fs[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      imp_res_tac evaluate_invariant_oracle>>
      pop_assum $ assume_tac o GSYM>>fs[Abbr‘X’]>>
      rename1 ‘ltree (_,t''.ffi.ffi_state) _ = FUNPOW Tau n' _’>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      fs[set_var_defs]>>
      qmatch_asmsub_abbrev_tac ‘h_prog (p', bst X)’>>
      ‘t''.ffi = X.ffi’ by simp[Abbr‘X’]>>fs[]>>
      disch_then drule>>strip_tac>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>pop_assum kall_tac>>
      strip_tac>>gvs[Abbr‘X’]>>
      qexists ‘SUC (k' + k'')’>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>fs[]>>
      disch_then $ qspec_then ‘k''’ assume_tac>>fs[])>>
  rpt (PURE_CASE_TAC>>fs[])>>
(*  rename [‘_ _ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>*)
  gvs[dec_clock_def,empty_locals_defs,kvar_defs2]>>
  rpt (PURE_CASE_TAC>>fs[])>>
  rpt (rename [‘FUNPOW Tau n _’]>>
       Cases_on ‘n’>>gvs[FUNPOW_SUC])>>
  simp[bst_def,empty_locals_defs,set_var_defs]>>
  qexists ‘SUC 0’>>gvs[]
QED

Theorem nondiv_imp_evaluate':
  ltree fs (mrec h_prog (h_prog (p,bst s))) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree
  ∧ FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
    ∃k t'. evaluate (p,s with clock := k) = (res,t')
           ∧ bst t' = t
         ∧ res ≠ SOME TimeOut
Proof
  Cases_on ‘fs’>>rw[]>>metis_tac[nondiv_imp_evaluate]
QED

(**************************)

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

(* move to HOL - llistTheory? *)
Definition lnil_def:
 lnil = LUNFOLD (λu. SOME ((),[||])) ()
End

Theorem lnil:
  [||]:::lnil = lnil
Proof
  simp[lnil_def]>>
  simp[SimpR“$=”,Once LUNFOLD]
QED

(* end of move *)

Theorem trace_prefix_spin:
  trace_prefix fs spin = [||]
Proof
  Cases_on ‘fs’>>
  simp[trace_prefix_def]>>
  simp[LFLATTEN_EQ_NIL]>>
  irule every_coind>>
  qexists ‘{lnil}’>>
  simp[]>>rw[]>>
  TRY (fs[Once (GSYM lnil)]>>NO_TAC)>>
  simp[lnil_def]>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qexists ‘CURRY {((r,spin),())|fs|T}’>>
  rw[] >>
  simp[Once spin]   
QED

(****)

Theorem trace_prefix_bind_append:
  (∃n. ltree fs t = FUNPOW Tau n (Ret r)) ⇒
  trace_prefix fs (itree_bind t k) =
    LAPPEND (trace_prefix fs t) (trace_prefix (FST fs,SND (comp_ffi fs t)) (k r))
Proof
  simp[PULL_EXISTS]>>
  map_every qid_spec_tac [‘fs’,‘r’,‘k’,‘t’] >>
  Induct_on ‘n’ >>
  rw[FUNPOW_SUC]
  >- (Cases_on ‘t’ >> fs[]>>
      PairCases_on ‘a’>>fs[]>>
      rpt (CASE_TAC>>fs[]))>>
  Cases_on ‘t’ >> fs[] >>
  PairCases_on ‘a’>>fs[]>>
  rpt (CASE_TAC>>fs[])>>
  last_x_assum $ qspecl_then [‘g (INL (INR l))’,‘k’,‘r’,‘(FST fs,f)’] assume_tac>>gvs[]
QED

Theorem trace_prefix_FUNPOW_Tau[simp]:
  trace_prefix fs (FUNPOW Tau n t) = trace_prefix fs t
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>simp[]
QED

Theorem trace_prefix_bind_div:
  div fs t ⇒
  trace_prefix fs (itree_bind t k) = trace_prefix fs t
Proof
  rw[trace_prefix_def]>>
  Cases_on ‘fs’>>rename [‘(x,x')’]>>
  AP_TERM_TAC>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qexists ‘CURRY {((x', itree_bind t k),(x',t))| div (x,x') t}’>>
  rw[EXISTS_PROD] >>simp[]>>
  last_x_assum kall_tac>>
  rpt (CASE_TAC>>fs[])>>
  gvs[div_def]>>rw[]>>
  first_assum $ qspec_then ‘SUC n’ assume_tac>>
  fs[FUNPOW_SUC]
QED

(**************************)

Theorem div_imp_timeout:
  div fs (mrec h_prog (h_prog (p,bst s))) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
  ∀k. ∃t. evaluate (p,s with clock := k) = (SOME TimeOut,t)
Proof
  CCONTR_TAC>>fs[]>>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,ss)’>>
  ‘bst s = bst ss ∧ s.ffi = ss.ffi’
    by simp[bst_def,Abbr‘ss’]>>fs[]>>
  Cases_on ‘evaluate (p,ss)’>>fs[]>>
  drule_all evaluate_imp_nondiv>>strip_tac>>
  last_x_assum mp_tac>>gvs[]>>
  Cases_on ‘fs’>>gs[]
QED

Theorem evaluate_nondiv_trace_eq:
  evaluate (p,s) = (r,t) ∧ r ≠ SOME TimeOut ⇒
  fromList t.ffi.io_events =
  LAPPEND (fromList s.ffi.io_events)
          (trace_prefix (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))))
Proof
  map_every qid_spec_tac [‘r’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘evaluate _ = _’ mp_tac
  >~ [‘ExtCall’] >-
   (simp[Once evaluate_def,mrec_ExtCall,call_FFI_def]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    strip_tac>>gvs[LAPPEND_NIL_2ND]>>
    fs[LAPPEND_NIL_2ND,dec_clock_def,
       empty_locals_defs,GSYM LAPPEND_fromList])>>
  simp[mrec_prog_simps,
       mrec_If,
       Once evaluate_def,kvar_defs2,
       mrec_ExtCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
       panPropsTheory.eval_upd_clock_eq,
       sh_mem_load_def,sh_mem_store_def,
       panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  gvs[FUNPOW_SUC,LAPPEND_NIL_2ND]
  >~ [‘Seq’] >-
   (pairarg_tac>>fs[]>>
    simp[mrec_Seq]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    strip_tac>>gvs[]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    imp_res_tac trace_prefix_bind_append>>fs[]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]
    >- (AP_TERM_TAC>>
        rev_drule nondiv_evaluate'>>
        disch_then $ qspecl_then [‘s1’,‘NONE’,‘s.clock’] assume_tac>>
        fs[]>>
        ‘s with clock := s.clock = s’
          by simp[state_component_equality]>>
        gs[]>>pop_assum kall_tac>>
        pop_assum (assume_tac o GSYM)>>fs[]>>
        rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
        fs[]>>
        simp[LAPPEND_NIL_2ND])>>
    CASE_TAC>>fs[]>>
    simp[LAPPEND_NIL_2ND])
  >~ [‘While’] >-
   (fs[dec_clock_def,empty_locals_defs]>>
    simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    rpt (pairarg_tac>>fs[])>>gvs[]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    rpt (CASE_TAC>>fs[])>>
    strip_tac>>gvs[LAPPEND_NIL_2ND]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]>>
    imp_res_tac trace_prefix_bind_append>>gs[]>>
    simp[LAPPEND_NIL_2ND]>>
    rev_drule nondiv_evaluate'>>
    qmatch_asmsub_abbrev_tac ‘evaluate _ = (res0,s1)’>>
    disch_then $ qspecl_then [‘s1’,‘res0’,‘s.clock-1’] assume_tac>>
    fs[]>>
    gs[Abbr‘res0’]>>
    pop_assum (assume_tac o GSYM)>>fs[]>>
    rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
    fs[])
  >~ [‘Call’]>-
   (simp[mrec_Call,empty_locals_defs,dec_clock_def]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    rpt (pairarg_tac>>fs[])>>gvs[dec_clock_def]>>
    strip_tac>>
    gvs[LAPPEND_NIL_2ND,dec_clock_def,set_var_defs]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    imp_res_tac trace_prefix_bind_append>>gs[]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]>>
    gvs[mrec_h_handle_call_ret_lemma,LAPPEND_NIL_2ND,kvar_defs2,LAPPEND_ASSOC]>>
    rpt (CASE_TAC>>fs[])>>fs[LAPPEND_NIL_2ND]>>
    qpat_x_assum ‘evaluate (q'',_) = _’ assume_tac>>
    rev_drule nondiv_evaluate'>>
    qmatch_asmsub_abbrev_tac ‘evaluate (q'',_) = (res0,s1)’>>
    disch_then $ qspecl_then [‘s1’,‘res0’,‘s.clock-1’] assume_tac>>
    gvs[Abbr‘res0’]>>
    pop_assum (assume_tac o GSYM)>>fs[]>>
    drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
    fs[LAPPEND_NIL_2ND])
  >~ [‘DecCall’]>-
   (simp[mrec_DecCall,empty_locals_defs,set_var_defs,dec_clock_def]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    rpt (pairarg_tac>>fs[])>>gvs[dec_clock_def]>>
    strip_tac>>
    gvs[LAPPEND_NIL_2ND,dec_clock_def,set_var_defs]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    imp_res_tac trace_prefix_bind_append>>gs[]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]>>
    gvs[mrec_h_handle_deccall_ret_lemma,
        LAPPEND_NIL_2ND,set_var_defs]>>
    qpat_x_assum ‘evaluate (q,_) = _’ assume_tac>>
    rev_drule nondiv_evaluate'>>
    qmatch_asmsub_abbrev_tac ‘evaluate (q,_) = (res0,s1)’>>
    disch_then $ qspecl_then [‘s1’,‘res0’,‘s.clock-1’] assume_tac>>
    gvs[Abbr‘res0’]>>
    pop_assum (assume_tac o GSYM)>>fs[]>>
    drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
    fs[LAPPEND_NIL_2ND])>>
  rpt (CASE_TAC>>fs[])>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  rpt (PURE_FULL_CASE_TAC>>fs[])>>
  strip_tac>>gvs[LAPPEND_NIL_2ND]>>
  imp_res_tac evaluate_imp_nondiv>>
  imp_res_tac trace_prefix_bind_append>>
  fs[LAPPEND_NIL_2ND,dec_clock_def,
     empty_locals_defs,GSYM LAPPEND_fromList]
QED

(**** divergence ****)

Theorem nondiv_timeout_add_clock:
  evaluate (p,s) = (SOME TimeOut, t) ∧
  ltree fs ((mrec h_prog (h_prog (p,bst s))):'a ptree) =
  FUNPOW Tau n (Ret r): 'a ptree ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
  ∃k q t'. evaluate (p,s with clock := s.clock + k) = (q, t') ∧
           r = INR (q, bst t') ∧ q ≠ SOME TimeOut ∧
           ∃l. t'.ffi.io_events = t.ffi.io_events ++ l
Proof
  rw[]>>
  imp_res_tac nondiv_INR>>fs[]>>
  rename [‘INR x’]>>Cases_on ‘x’>>
  Cases_on ‘fs’>>fs[]>>
  drule nondiv_imp_evaluate>>rw[]>>
  Cases_on ‘s.clock < k’>>fs[NOT_LESS]
  >- (imp_res_tac (GSYM LESS_ADD)>>
  mp_tac (Q.SPECL [‘p’,‘s’,‘p'’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
      rw[IS_PREFIX_APPEND]>>gvs[]>>
      qexists ‘p'’>>metis_tac[])>>
  imp_res_tac (GSYM LESS_EQUAL_ADD)>>fs[]>>
  drule panPropsTheory.evaluate_add_clock_eq>>
  disch_then $ qspec_then ‘p'’ assume_tac>>fs[]>>
  gvs[]>>
  ‘s with clock := s.clock = s’
  by simp[state_component_equality]>>gvs[]
QED

Theorem timeout_div_LPREFIX:
  evaluate (p,s) = (SOME TimeOut, t) ∧
  div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) ⇒
  LPREFIX
  (fromList t.ffi.io_events)
  (LAPPEND (fromList s.ffi.io_events)
           (trace_prefix (s.ffi.oracle,s.ffi.ffi_state) ((mrec h_prog (h_prog (p,bst s))):'a ptree)))
Proof
  map_every qid_spec_tac [‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘evaluate _ = _’ mp_tac>>
  simp[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>
  fs[mrec_prog_simps,kvar_defs2]>>
  TRY (
    rpt (TOP_CASE_TAC>>fs[])>>
    strip_tac>>
    rpt (pairarg_tac>>fs[])>>gvs[]>>NO_TAC)
  >- (rpt (CASE_TAC>>fs[])>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘X ⇒ _’>>
      Cases_on ‘X’>>fs[]
      >- (imp_res_tac trace_prefix_bind_div>>fs[])>>
      imp_res_tac div_bind2>>fs[])

  (* Seq *)
  >- (qhdtm_x_assum ‘div’ mp_tac>>
      simp[mrec_Seq]>>
      rpt (pairarg_tac>>fs[])>>
      rpt (CASE_TAC>>fs[])>>strip_tac>>strip_tac
      >- (imp_res_tac evaluate_imp_nondiv>>fs[]>>
          drule_all (iffLR div_bind2)>>strip_tac>>gvs[]>>
          drule nondiv_evaluate'>>
          disch_then $ qspecl_then [‘s1’,‘NONE’,‘s.clock’] mp_tac>>
          ‘s with clock := s.clock = s’
            by simp[state_component_equality]>>gvs[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          fs[LAPPEND_ASSOC]>>
          gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>fs[]>>
          gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          qmatch_goalsub_abbrev_tac ‘trace_prefix fs _’>>
          qmatch_goalsub_abbrev_tac ‘itree_bind X _’>>
          Cases_on ‘div fs X’>>fs[]
          >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
              metis_tac[])>>
          fs[Abbr‘fs’,Abbr‘X’]>>
          drule_then drule nondiv_timeout_add_clock>>rw[]>>
          mp_tac (Q.SPECL [‘c2’,‘s1’,‘k’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
          rw[IS_PREFIX_APPEND]>>
          drule (SRULE [PULL_EXISTS] trace_prefix_bind_append)>>
          rw[LAPPEND_NIL_2ND]>>
          drule_all evaluate_nondiv_trace_eq>>
          rw[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[LAPPEND_ASSOC]>>
          gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          pop_assum $ assume_tac o GSYM>>fs[]>>metis_tac[])>>
      gvs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[])>>
      drule_then drule nondiv_timeout_add_clock>>rw[]>>fs[]>>
      FULL_CASE_TAC>>fs[]>>
      drule nondiv_evaluate'>>
      disch_then $ drule_at Any>>simp[]>>rw[]>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      fs[LAPPEND_ASSOC]>>
      gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      qhdtm_x_assum ‘LAPPEND’ $ assume_tac o GSYM>>fs[]>>
      gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      fs[LAPPEND_ASSOC]>>
      gs[LFINITE_fromList,LAPPEND11_FINITE1])
  >- (fs[mrec_If]>>
      rpt (CASE_TAC>>fs[])>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘X ⇒ _’>>
      (Cases_on ‘X’>>fs[]
       >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
      imp_res_tac div_bind2>>fs[])
  (* While *)
  >- (pop_assum mp_tac>>
      once_rewrite_tac[mrec_While]>>
      rpt (TOP_CASE_TAC>>fs[])
      >- (rw[]>>gvs[empty_locals_defs]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1])>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>
      rpt (CASE_TAC>>fs[])>>
      strip_tac>>fs[empty_locals_defs,dec_clock_def]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      imp_res_tac IS_PREFIX_APPEND>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]
      >-
       (rev_drule evaluate_imp_nondiv>>
        simp[]>>strip_tac>>
        imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
        imp_res_tac trace_prefix_bind_append>>gvs[]>>
        fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
        fs[LAPPEND_ASSOC]>>
        fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
        qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
        simp[LAPPEND_ASSOC]>>
        fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
        drule div_bind2>>strip_tac>>fs[]>>
        drule_then drule nondiv_evaluate'>>
        simp[]>>strip_tac>>
        pop_assum $ assume_tac o GSYM>>fs[]>>
        rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
        gs[]>>metis_tac[])
      >-
       (gvs[div_bind_cases]
        >- (imp_res_tac trace_prefix_bind_div>>fs[]>>metis_tac[])>>
        drule nondiv_timeout_add_clock>>simp[]>>
        disch_then $ drule_at Any>>rw[]>>fs[]>>
        FULL_CASE_TAC>>fs[]>>
        drule nondiv_evaluate'>>
        disch_then $ drule_at Any>>simp[]>>rw[]>>
        pop_assum $ assume_tac o GSYM>>fs[]>>
        drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
        fs[]>>
        drule_then assume_tac panPropsTheory.evaluate_io_events_mono>>
        fs[IS_PREFIX_APPEND]>>gvs[]>>
        imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
        imp_res_tac trace_prefix_bind_append>>gvs[]>>
        fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
        fs[LAPPEND_ASSOC]>>
        fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
        qhdtm_x_assum ‘LAPPEND’ $ assume_tac o GSYM>>fs[]>>
        fs[LAPPEND_ASSOC]>>
        metis_tac[])>>
      rev_drule evaluate_imp_nondiv>>simp[]>>
      strip_tac>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      simp[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      drule div_bind2>>strip_tac>>fs[]>>
      drule_then drule nondiv_evaluate'>>
      simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      gs[]>>metis_tac[])>>
  (* Call / DecCall *)
  (pop_assum mp_tac>>
   simp[mrec_Call,mrec_DecCall]>>
   rpt (TOP_CASE_TAC>>fs[])
   >- (rw[]>>gvs[empty_locals_defs]>>
       fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
       fs[LFINITE_fromList,LAPPEND11_FINITE1])>>
   rw[]>>fs[dec_clock_def,empty_locals_defs,set_var_defs]
   >-
    ((gvs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
     drule nondiv_timeout_add_clock>>simp[]>>
     disch_then $ drule_at Any>>rw[]>>
     drule nondiv_evaluate'>>
     disch_then $ drule_at Any>>
     disch_then $ qspecl_then [‘t'’,‘k + s.clock - 1’] mp_tac>>gs[]>>
     disch_then $ assume_tac o GSYM>>fs[]>>
     drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
     fs[]>>
     imp_res_tac panPropsTheory.evaluate_io_events_mono>>
     fs[IS_PREFIX_APPEND]>>gvs[]>>
     imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
     imp_res_tac trace_prefix_bind_append>>gvs[]>>
     fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
     fs[LAPPEND_ASSOC]>>
     fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
     qhdtm_x_assum ‘LAPPEND’ $ assume_tac o GSYM>>
     simp[LAPPEND_ASSOC]>>
     fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
     fs[mrec_h_handle_call_ret_lemma,
        mrec_h_handle_deccall_ret_lemma,kvar_defs2])>>
   rpt (pairarg_tac>>fs[])>>
   rev_drule evaluate_imp_nondiv>>
   simp[]>>strip_tac>>
   imp_res_tac panPropsTheory.evaluate_io_events_mono>>
   fs[IS_PREFIX_APPEND]>>gvs[]>>
   imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
   imp_res_tac trace_prefix_bind_append>>gvs[]>>
   fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
   fs[LAPPEND_ASSOC]>>
   fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
   qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
   simp[LAPPEND_ASSOC]>>
   fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
   drule_then dxrule (iffLR div_bind2)>>strip_tac>>fs[]>>
   gvs[mrec_h_handle_call_ret_lemma,
       mrec_h_handle_deccall_ret_lemma,kvar_defs2]>>
   drule nondiv_evaluate'>>fs[]>>
   disch_then $ drule_at Any>>
   simp[]>>strip_tac>>
   pop_assum $ assume_tac o GSYM>>fs[]>>
   rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
   fs[]>>
   (gvs[div_bind_cases]
    >- (imp_res_tac trace_prefix_bind_div>>fs[]>>metis_tac[])))
QED

Theorem not_less_opt_lemma:
  (∀k. ¬less_opt
       n (SOME
          (LENGTH
           (SND (evaluate (prog:'a panLang$prog,s with clock := k))).ffi.io_events))) ⇒
  ∃k'. (∀k. k' ≤ k ⇒
            LENGTH
            (SND (evaluate (prog,s with clock := k))).ffi.io_events =
            LENGTH
            (SND (evaluate (prog,s with clock := k'))).ffi.io_events)
Proof
  strip_tac>>
  fs[less_opt_def,NOT_LESS]>>
  qabbrev_tac ‘f = (λx. LENGTH (SND (evaluate (prog:'a panLang$prog,s with clock := x))).ffi.io_events)’>>
  fs[]>>
  ‘∀k k'. k ≤ k' ⇒ f k ≤ f k'’
    by (fs[Abbr‘f’]>>
        rpt strip_tac>>
        drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
        assume_tac (Q.SPECL [‘prog’,‘s with clock := k’,‘p’]
                     panPropsTheory.evaluate_add_clock_io_events_mono)>>
        fs[IS_PREFIX_APPEND])>>
  ‘∃k. ∀k'. k ≤ k' ⇒ f k' ≤  f k’ by
    (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
     last_x_assum mp_tac>>fs[NOT_LESS_EQUAL]>>
     Cases_on ‘n < f k’>>fs[NOT_LESS]>- metis_tac[]>>
     drule LESS_EQUAL_ADD>>strip_tac>>
     gvs[]>>
     pop_assum mp_tac>>
     qid_spec_tac ‘p’>>
     Induct>>rw[]
     >- (first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
         qexists ‘k'’>>rw[])>>
     fs[PULL_FORALL]>>
     first_x_assum $ qspec_then ‘k'’ assume_tac>>fs[]>>
     simp[GSYM ADD_SUC,GSYM LESS_EQ_IFF_LESS_SUC]>>
     irule_at Any LESS_LESS_EQ_TRANS>>
     irule_at Any (iffRL LESS_MONO_EQ)>>
     first_assum $ irule_at Any>>
     simp[LESS_EQ_IFF_LESS_SUC]>>
     metis_tac[])>>
  qexists ‘k’>>rw[]>>
  metis_tac[LESS_EQUAL_ANTISYM]
QED

(*** some analysis on termination at Vis ***)

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
  fs[ext_def,empty_locals_defs,dec_clock_def,kvar_defs2]>>
  rpt (CASE_TAC>>fs[])>>rw[]>>gvs[]>>
  qexistsl [‘2’,‘1’]>>fs[dec_clock_def]
QED

(* move to HOL - llistTheory *)
Theorem LFINITE_LAPPEND_EQ_NIL:
  LFINITE ll ⇒ (LAPPEND ll l1 = ll ⇔ l1 = [||])
Proof
  rw[EQ_IMP_THM] >- metis_tac[LFINITE_LAPPEND_IMP_NIL]>>
  simp[LAPPEND_NIL_2ND]
QED

Theorem mrec_FUNPOW_Ret_evaluate:
  mrec h_prog (h_prog (p,s)) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree ⇒
  ∃k k'. (∀ffi. evaluate (p,ext s k ffi) = (res, ext t k' ffi)) ∧ k' ≤ k ∧
             res ≠ SOME TimeOut ∧ (∀fe. res ≠ SOME (FinalFFI fe))
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>strip_tac>>
  Cases_on ‘n’>>fs[FUNPOW]
  >- (imp_res_tac mrec_Ret_evaluate>>gvs[]>>metis_tac[])>>
  rename1 ‘SUC n’>>
  fs[GSYM FUNPOW,FUNPOW_SUC]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[]>>
  pop_assum mp_tac>>
  once_rewrite_tac[evaluate_def]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  fs[mrec_prog_simps,mrec_If,empty_locals_defs,mrec_ExtCall,
     panPropsTheory.eval_upd_clock_eq,call_FFI_def,kvar_defs2,
     iterateTheory.LAMBDA_PAIR,mrec_ShMemLoad,mrec_ShMemStore,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       rpt (pairarg_tac>>fs[])>>rw[]>>
       fs[FUNPOW_SUC]>>gvs[]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
       simp[ext_def]>>NO_TAC)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>rw[]>>
      simp[FUNPOW_SUC]>>gvs[]>>
      imp_res_tac bind_FUNPOW_Ret>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>gvs[]>>
      fs[FUNPOW_Tau_bind]>>
      rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
      first_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ drule>>rw[]>>gvs[]>>
      qexistsl [‘k’,‘k'’]>>strip_tac>>
      first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[])
  >~ [‘Seq’] >-
   (fs[mrec_Seq]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]
    >- (Cases_on ‘m’>>fs[FUNPOW_SUC]>>
        imp_res_tac bind_FUNPOW_Ret>>
        imp_res_tac mrec_FUNPOW_Ret_INR>>gvs[]>>
        rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
        fs[FUNPOW_Tau_bind]>>gvs[]>>
        first_assum $ qspec_then ‘n’ mp_tac>>
        first_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
        disch_then drule>>strip_tac>>
        disch_then drule>>strip_tac>>gvs[]>>
        (Cases_on ‘k' ≤ k''’
         >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
             qexistsl [‘k+p''’,‘k'''’]>>simp[]>>
             strip_tac>>fs[]>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘p''’ assume_tac>>gvs[]))>>
        fs[NOT_LESS_EQUAL]>>
        drule LESS_ADD>>
        disch_then $ assume_tac o GSYM>>fs[]>>
        qexistsl [‘k’,‘k''' + p''’]>>simp[]>>
        strip_tac>>fs[]>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
        rev_drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘p''’ assume_tac>>fs[])>>
    ‘n' < SUC n'’ by simp[]>>
    res_tac>>
    qexistsl [‘k’,‘k'’]>>fs[]>>gvs[])
   (* If *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
      imp_res_tac bind_FUNPOW_Ret>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
      fs[FUNPOW_Tau_bind])
  >~ [‘Call’] >-
   (simp[mrec_Call,empty_locals_defs]>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    TRY (TOP_CASE_TAC>>fs[])>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>
    fs[FUNPOW_Ret_simp]>>
    fs[mrec_h_handle_call_ret_lemma,empty_locals_defs,
       kvar_defs2]>>
    gvs[AllCaseEqs()]>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         ‘n < SUC n’ by simp[]>>
         res_tac>>gvs[]>>
         qexistsl [‘SUC k’,‘k'’]>>simp[]>>
         rpt (PURE_CASE_TAC>>fs[])>>NO_TAC)
    >- (rename [‘_ = FUNPOW Tau n _’]>>
        ‘n < SUC n’ by simp[]>>
        last_x_assum drule>>
        disch_then drule>>simp[]>>rw[]>>
        qexistsl [‘SUC k’,‘k'’]>>simp[]>>
        simp[ext_def])>>
    rename [‘Tau _ = FUNPOW Tau n _’]>>
    Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>gvs[]>>
    FULL_CASE_TAC>>gvs[]>>
    rename1 ‘_ = FUNPOW Tau n (Ret (INR (q'',r'')))’>>
    rename1 ‘_ = FUNPOW Tau n' (Ret (INR (SOME (Exception _ _),_)))’>>
    last_assum $ qspec_then ‘n’ mp_tac>>
    last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
    disch_then drule>>strip_tac>>
    disch_then drule>>strip_tac>>gvs[]>>
    (Cases_on ‘k' ≤ k''’
     >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
         rename1 ‘k'' = k' + pp’>>
         qexistsl [‘SUC (k+pp)’,‘k'''’]>>simp[]>>
         strip_tac>>fs[]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
         drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘pp’ assume_tac>>gvs[]))>>
    fs[NOT_LESS_EQUAL]>>
    drule LESS_ADD>>
    disch_then $ assume_tac o GSYM>>fs[]>>
    rename1 ‘k' = k'' + pp’>>
    qexistsl [‘SUC k’,‘k''' + pp’]>>simp[]>>
    strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
    rev_drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘pp’ assume_tac>>fs[])
  >~ [‘DecCall’] >-
   (simp[mrec_DecCall,empty_locals_defs]>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>
    fs[FUNPOW_Ret_simp]>>
    fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,
       kvar_defs2]>>
    gvs[AllCaseEqs()]>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         ‘n < SUC n’ by simp[]>>
         res_tac>>TRY (gvs[]>>NO_TAC)>>
         qexistsl [‘SUC k’,‘k'’]>>simp[]>>gvs[]>>
         rpt (FULL_CASE_TAC>>fs[])>>NO_TAC)>>
    rename [‘Tau _ = FUNPOW Tau n _’]>>
    Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>gvs[]>>
    rename1 ‘_ = FUNPOW Tau n (Ret (INR (q',_)))’>>
    rename1 ‘_ = FUNPOW Tau n' (Ret (INR (SOME (Return _),_)))’>>
    last_assum $ qspec_then ‘n’ mp_tac>>
    last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
    disch_then drule>>strip_tac>>
    disch_then drule>>strip_tac>>gvs[]>>
        (Cases_on ‘k' ≤ k''’
         >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
             rename1 ‘k'' = k' + pp’>>
             qexistsl [‘SUC (k+pp)’,‘k'''’]>>simp[]>>
             strip_tac>>fs[]>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘pp’ assume_tac>>gvs[]))>>
        fs[NOT_LESS_EQUAL]>>
        drule LESS_ADD>>
        disch_then $ assume_tac o GSYM>>fs[]>>
        qexistsl [‘SUC k’,‘k''' + p'’]>>simp[]>>
        strip_tac>>fs[]>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
        rev_drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘p'’ assume_tac>>fs[])>>
  (* While *)
  simp[Once mrec_While]>>
  rpt (TOP_CASE_TAC>>fs[])>>simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
  imp_res_tac bind_FUNPOW_Ret>>
  imp_res_tac mrec_FUNPOW_Ret_INR>>
  fs[FUNPOW_Tau_bind]>>
  fs[FUNPOW_Ret_simp]>>
  rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  TRY (rename [‘mrec _ _ = FUNPOW Tau n (Ret _)’]>>
       ‘n < SUC n’ by simp[]>>
       res_tac>>gvs[]>>
       qexistsl [‘SUC k’,‘k'’]>>simp[]>>gvs[]>>NO_TAC)>>
  rename [‘Tau _ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
  rename1 ‘mrec _ (_ (While _ _,_)) = FUNPOW Tau n _’>>
  rename1 ‘mrec _ (_ (p,_)) = FUNPOW Tau n' _’>>
  first_assum $ qspec_then ‘n’ mp_tac>>
  first_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
  disch_then drule>>strip_tac>>
  disch_then drule>>strip_tac>>gvs[]>>
  (Cases_on ‘k' ≤ k''’
   >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
       qexistsl [‘SUC (k+p')’,‘k'''’]>>simp[]>>
       strip_tac>>fs[]>>
       first_x_assum $ qspec_then ‘ffi’ assume_tac>>
       first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
       drule panPropsTheory.evaluate_add_clock_eq>>
       disch_then $ qspec_then ‘p'’ assume_tac>>gvs[]))>>
  fs[NOT_LESS_EQUAL]>>
  drule LESS_ADD>>
  disch_then $ assume_tac o GSYM>>fs[]>>
  qexistsl [‘SUC k’,‘k''' + p'’]>>simp[]>>
  strip_tac>>fs[]>>
  first_x_assum $ qspec_then ‘ffi’ assume_tac>>
  first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
  rev_drule panPropsTheory.evaluate_add_clock_eq>>
  disch_then $ qspec_then ‘p'’ assume_tac>>fs[]
QED

(********)

Theorem mrec_Vis_no_trace_lemma:
  mrec h_prog (h_prog (p, bst s)) = FUNPOW Tau n (Vis a g:'a ptree) ∧
  (∀k. s.ffi.io_events =
       (SND (evaluate(p,s with clock := k + s.clock))).ffi.io_events) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ∧ s.clock = 0 ∧
  (FST fs) (FST a) (SND fs) (FST (SND a)) (SND (SND a)) = X ⇒
  (∃f l. X = Oracle_return f l ∧ LENGTH (SND (SND a)) ≠ LENGTH l) ∨
  (∃f. X = Oracle_final f)
Proof
  simp[]>>rw[]>>
  ‘∀k. s.ffi = (SND (evaluate (p, s with clock := k + s.clock))).ffi’
    by (strip_tac>>
        Cases_on ‘evaluate (p, s with clock := k + s.clock)’>>fs[]>>
        drule io_events_eq_imp_ffi_eq>>
        first_assum $ qspec_then ‘k’ assume_tac>>simp[]>>gvs[])>>
  qpat_x_assum ‘∀x. s.ffi.io_events = _’ kall_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’]>>
  Induct>>rw[]>>
  ntac 5 (pop_assum mp_tac)>>
  simp[Once evaluate_def]>>
  simp[mrec_prog_simps,mrec_If,mrec_Dec,
       mrec_ShMemLoad,mrec_ShMemStore]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  fs[panPropsTheory.eval_upd_clock_eq,call_FFI_def,
     iterateTheory.LAMBDA_PAIR,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       simp[FUNPOW_Ret_simp]>>NO_TAC)>>
  TRY (simp[mrec_ExtCall]>>
       rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
       gvs[empty_locals_defs,set_var_defs]>>
       gvs[AllCaseEqs()]>>
       gvs[ffi_state_component_equality]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>NO_TAC)
  >- (CASE_TAC>>fs[]>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then drule>>simp[])
  >- (simp[mrec_Seq]>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
      >- (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
          disch_then drule>>simp[]>>
          disch_then drule>>simp[]>>
          impl_tac >-
           (strip_tac>>
            first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>
            qmatch_goalsub_abbrev_tac ‘FST X’>>
            Cases_on ‘X’>>gvs[]>>
            FULL_CASE_TAC>>gvs[]>>
            qmatch_goalsub_abbrev_tac ‘SND X’>>
            Cases_on ‘X’>>gvs[]>>
            imp_res_tac panPropsTheory.evaluate_io_events_mono>>
            fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
            drule_all io_events_eq_imp_ffi_eq>>rw[])>>rw[])>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      Cases_on ‘q’>>fs[]>>
      Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
      ‘s with <|clock := k; ffi := s.ffi|> = s with clock := k’
        by simp[state_component_equality]>>fs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      ‘n < SUC n'’ by simp[]>>
      first_x_assum drule>>
      disch_then $ qspecl_then [‘p'’,‘ext r 0 s.ffi’,‘g'’,‘a’,‘fs’] mp_tac>>
      simp[]>>
      impl_tac>-
       (strip_tac>>
        first_x_assum $ qspec_then ‘k''+k'''’ mp_tac>>simp[]>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘k'''’ assume_tac>>fs[]>>
        qmatch_goalsub_abbrev_tac ‘SND X’>>
        Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[])
  (* If *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then drule>>simp[])
  >~ [‘While’]>-
   (simp[Once mrec_While]>>       
    rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
    Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    (imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
     >- (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
         disch_then drule>>simp[]>>
         disch_then drule>>simp[]>>
         (impl_tac >-
           (strip_tac>>
            first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[]>>
            qmatch_goalsub_abbrev_tac ‘FST X’>>
            Cases_on ‘X’>>gvs[empty_locals_defs,dec_clock_def]>>
            rpt (FULL_CASE_TAC>>gvs[])>>
            qmatch_goalsub_abbrev_tac ‘SND X’>>
            Cases_on ‘X’>>gvs[]>>
            imp_res_tac panPropsTheory.evaluate_io_events_mono>>
            fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
            drule_all io_events_eq_imp_ffi_eq>>rw[])>>rw[])))>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
    rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
    Cases_on ‘q’>>fs[]>>
    TRY (rename [‘INR (SOME xx,_)’]>>Cases_on ‘xx’>>fs[])>>
    Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
    imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
    first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
    ‘s with <|clock := k; ffi := s.ffi|> = s with clock := k’
      by simp[state_component_equality]>>fs[]>>
    dxrule evaluate_min_clock>>rw[]>>
    ‘n < SUC n'’ by simp[]>>
    first_x_assum drule>>
    disch_then $ qspecl_then [‘While e p’,‘ext r 0 s.ffi’,‘g’,‘a’,‘fs’] mp_tac>>
    simp[]>>
    (impl_tac>-
      (strip_tac>>
       first_x_assum $ qspec_then ‘SUC (k''+k''')’ mp_tac>>simp[]>>
       drule panPropsTheory.evaluate_add_clock_eq>>
       disch_then $ qspec_then ‘k'''’ assume_tac>>fs[dec_clock_def]>>
       qmatch_goalsub_abbrev_tac ‘SND X’>>
       Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[]))
  >~ [‘Call’] >-
   (simp[mrec_Call,empty_locals_defs,kvar_defs]>>
    rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
    Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
    TRY (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
         disch_then drule>>simp[]>>
         disch_then drule>>simp[]>>
         (impl_tac >-
           (strip_tac>>
            first_x_assum $ qspec_then ‘SUC k’ mp_tac>>fs[dec_clock_def]>>
            rpt (CASE_TAC>>gvs[])>>rw[]>>
            qmatch_goalsub_abbrev_tac ‘SND X’>>
            Cases_on ‘X’>>gvs[]>>
            imp_res_tac panPropsTheory.evaluate_io_events_mono>>
            fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
            drule io_events_eq_imp_ffi_eq>>rw[])>>rw[]))>>
    TRY (imp_res_tac mrec_FUNPOW_Ret_INR>>
         rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
         fs[mrec_h_handle_call_ret_lemma,empty_locals_defs,
            kvar_defs2]>>
         gvs[AllCaseEqs()])>>
    Cases_on ‘n' - m'’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
    imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
    first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
    ‘s with <|locals:=r;clock := k; ffi := s.ffi|> =
     s with <|locals:=r;clock := k|>’
      by simp[state_component_equality]>>fs[]>>
    dxrule evaluate_min_clock>>rw[]>>
    ‘n < SUC n'’ by simp[]>>
    first_x_assum drule>>
    qmatch_asmsub_abbrev_tac ‘mrec _ (_ (pp,ss)) = FUNPOW _ _ (Vis a g')’>>
    disch_then $ qspecl_then [‘pp’,‘ext ss 0 s.ffi’,‘g'’,‘a’,‘fs’] mp_tac>>
    simp[Abbr‘ss’,Abbr‘pp’]>>
    (impl_tac>-
      (strip_tac>>
       first_x_assum $ qspec_then ‘SUC (k''+k''')’ mp_tac>>simp[]>>
       drule panPropsTheory.evaluate_add_clock_eq>>
       disch_then $ qspec_then ‘k'''’ assume_tac>>fs[dec_clock_def]>>
       qmatch_goalsub_abbrev_tac ‘SND X’>>
       Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[]))>>
  (* DecCall *)
  simp[mrec_DecCall,empty_locals_defs,set_var_defs]>>
  rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>
  imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
  >- (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then drule>>simp[]>>
      (impl_tac >-
        (strip_tac>>
         first_x_assum $ qspec_then ‘SUC k’ mp_tac>>fs[dec_clock_def]>>
         rpt (CASE_TAC>>gvs[])>>rw[]>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>
         Cases_on ‘X’>>gvs[]>>
         imp_res_tac panPropsTheory.evaluate_io_events_mono>>
         fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
         drule io_events_eq_imp_ffi_eq>>rw[])>>rw[]))>>
  imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
  rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
  fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,
     kvar_defs2]>>
  gvs[AllCaseEqs()]>>
  Cases_on ‘n' - m'’>>fs[FUNPOW_SUC]>>
  imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
  imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
  first_x_assum $ qspec_then ‘s'.ffi’ assume_tac>>
  ‘s' with <|locals:=r;clock := k; ffi := s'.ffi|> =
   s' with <|locals:=r;clock := k|>’
    by simp[state_component_equality]>>fs[]>>
  dxrule evaluate_min_clock>>rw[]>>
  ‘n < SUC n'’ by simp[]>>
  first_x_assum drule>>
  qmatch_asmsub_abbrev_tac ‘mrec _ (_ (pp,ss)) = FUNPOW _ _ (Vis a g')’>>
  disch_then $ qspecl_then [‘pp’,‘ext ss 0 s'.ffi’,‘g'’,‘a’,‘fs’] mp_tac>>
  simp[Abbr‘ss’,Abbr‘pp’]>>
  (impl_tac>-
    (strip_tac>>
     first_x_assum $ qspec_then ‘SUC (k''+k''')’ mp_tac>>simp[]>>
     drule panPropsTheory.evaluate_add_clock_eq>>
     disch_then $ qspec_then ‘k'''’ assume_tac>>fs[dec_clock_def]>>
     qmatch_goalsub_abbrev_tac ‘SND X’>>
     Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[])
QED

(*** evaluate -> itree (no ffi update) ***)

Theorem evaluate_mrec_FUNPOW_Ret_io_events:
  evaluate (p, s0) = (res,t) ∧ s0 = ext s k ffi ∧ t.ffi.io_events = ffi.io_events ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. mrec h_prog (h_prog (p, s)) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  map_every qid_spec_tac [‘k’,‘ffi’, ‘res’,‘t’,‘s’,‘s0’, ‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac >> simp[]>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]
  >~[‘ShMemLoad’]>-
   (simp[mrec_ShMemLoad]>>fs[call_FFI_def,kvar_defs2]>>
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
    rpt (CASE_TAC>>fs[])>>gvs[]>>
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
     (Cases_on ‘k=0’>>fs[]>>rw[]>>
      FULL_CASE_TAC>>fs[]
      >- (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
          first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
          gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
          simp[h_handle_call_ret_def]>>
          gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[kvar_defs2]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
      rpt (CASE_TAC>>fs[])>>
      simp[h_handle_call_ret_def,mrec_bind,kvar_defs2]>>
      rpt (FULL_CASE_TAC>>fs[])>>simp[empty_locals_defs]>>
      TRY (irule_at Any (GSYM FUNPOW_SUC))>>
      TRY (simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
           simp[h_handle_call_ret_def,mrec_bind,kvar_defs2])>>

      imp_res_tac panPropsTheory.evaluate_io_events_mono>>gvs[]>>
      drule_all IS_PREFIX_ANTISYM>>rw[]>>fs[]>>
      simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
      simp[h_handle_call_ret_def,mrec_bind,kvar_defs2]>>

      qmatch_goalsub_abbrev_tac ‘h_prog (_,ss)’>>
      first_x_assum $ qspecl_then [‘ss’,‘r'.ffi’,‘r'.clock’] mp_tac>>
      (impl_tac >- fs[Abbr‘ss’,state_component_equality])>>rw[]>>
      simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
      simp[GSYM FUNPOW_ADD])>>
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
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[kvar_defs2]>>
  rpt (CASE_TAC>>fs[])>>
  TRY (pairarg_tac>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>
  simp[Once itree_unfold,call_FFI_def]>>rw[]>>
  TRY (metis_tac[FUNPOW])
QED

Theorem evaluate_mrec_FUNPOW_Ret:
  evaluate (p, s) = (res,t) ∧ t.ffi = s.ffi ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. mrec h_prog (h_prog (p, bst s)) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  rw[]>>irule evaluate_mrec_FUNPOW_Ret_io_events>>rw[]>>
  irule_at Any EQ_REFL>>
  qexists ‘s.clock’>>
  qmatch_goalsub_abbrev_tac ‘evaluate (_, ss) = _’>>
  ‘ss = s’ by simp[Abbr‘ss’,state_component_equality]>>simp[]
QED

(*****)

(* this needs some speedup *)
Theorem mrec_Vis_nondiv_lemma:
  mrec h_prog (h_prog (p,bst s)) = FUNPOW Tau n (Vis a g) :'a ptree ∧
  (∀k. s.ffi.io_events =
       (SND (evaluate (p,s with clock := k + s.clock))).ffi.io_events) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ∧ s.clock = 0 ⇒
  ¬ div fs (mrec h_prog (h_prog (p,bst s)))
Proof
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>
  disch_then assume_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’]>>
  Induct>>rw[]>>
  ntac 5 (pop_assum mp_tac)>>
  simp[Once evaluate_def]>>
  simp[mrec_prog_simps,mrec_If,mrec_Dec,
       mrec_ShMemLoad,mrec_ShMemStore]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  fs[panPropsTheory.eval_upd_clock_eq,call_FFI_def,
     iterateTheory.LAMBDA_PAIR,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       simp[FUNPOW_Ret_simp]>>NO_TAC)
  >- ((* Dec *)
  CASE_TAC>>fs[]>>rw[]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>
  imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
  ‘n' < SUC n'’ by simp[]>>
  first_assum drule>>
  disch_then drule>>
  disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>strip_tac>>
  fs[FUNPOW_Ret_simp]>>
  drule mrec_Vis_no_trace_lemma>>simp[]>>
  disch_then drule>>simp[]>>rw[]>>
  PairCases_on ‘a’>>gvs[]>>
  Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
  simp[FUNPOW_Tau_bind]>>
  simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD])
  >~ [‘Seq’]
  >- (simp[mrec_Seq]>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
      >- (‘n' < SUC n'’ by simp[]>>
          first_assum drule>>
          disch_then drule>>simp[]>>
          disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>
          ‘∀k. s.ffi.io_events =
               (SND (evaluate (p,s with clock := k))).ffi.io_events’ by
            (strip_tac>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>
             CASE_TAC>>fs[]>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             imp_res_tac panPropsTheory.evaluate_io_events_mono>>
             fs[IS_PREFIX_APPEND])>>rw[]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          ‘ltree fs (mrec h_prog (h_prog (p,bst s))) =
           FUNPOW Tau n'' (Ret r):'a ptree’
            by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
          imp_res_tac nondiv_INR>>
          rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
          drule nondiv_evaluate'>>
          drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
          disch_then drule>>simp[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          drule mrec_Vis_no_trace_lemma>>
          disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
          PairCases_on ‘a’>>gvs[]>>
          Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          Cases_on ‘fs’>>fs[]>>
          (rpt (CASE_TAC>>fs[])
           >- (drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
               ‘s.ffi = t'.ffi’ by
                 (first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>
                  drule io_events_eq_imp_ffi_eq>>rw[])>>rw[])>>
           irule_at Any LESS_EQ_REFL>>simp[FUNPOW]))>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      (* write a lemma on ext (bst s) k s.ffi = s with clock := k *)
(*      ‘∀k. ext (bst s) k s.ffi = s with clock := k’
        by simp[state_component_equality]>>fs[]>>*)
      rpt (FULL_CASE_TAC>>fs[])>>
      Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_x_assum drule>>
      ‘(ext r 0 s.ffi).clock = 0’ by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>simp[]>>
      ‘∀k. s.ffi.io_events =
           (SND (evaluate (p',ext r k s.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
         first_assum $ qspec_then ‘k''’ assume_tac>>
         first_x_assum $ qspec_then ‘k'' + k'''’ assume_tac>>gs[]>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[]>>gvs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      ‘ltree fs (mrec h_prog (h_prog (p',bst (ext r 0 s.ffi)))) =
       FUNPOW Tau n'' (Ret r'):'a ptree’
        by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
      imp_res_tac nondiv_INR>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[Excl"bst_ext_id"]>>
      drule nondiv_evaluate'>>
      drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
      disch_then drule>>simp[]>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      ‘(ext r 0 s.ffi).clock = 0’ by simp[]>>
      drule_at Any mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n’>>fs[FUNPOW_SUC]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      Cases_on ‘fs’>>fs[]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])
  (* If *)
  >- (rpt (CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n' < SUC n'’ by simp[]>>
      first_x_assum drule>>
      disch_then drule>>gs[]>>
      disch_then $ qspec_then ‘fs’ assume_tac>>gvs[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>simp[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
      simp[FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD])
  >~ [‘While’]
  >- (simp[Once mrec_While]>>
      rpt (CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
      (* p: Vis *)
      >- (‘n' < SUC n'’ by simp[]>>
          first_assum drule>>
          disch_then drule>>simp[]>>
          disch_then $ qspec_then ‘fs’ mp_tac>>
          fs[dec_clock_def,empty_locals_defs]>>
          ‘∀k. s.ffi.io_events =
               (SND (evaluate (p,s with clock := k))).ffi.io_events’ by
            (strip_tac>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[]>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
             imp_res_tac panPropsTheory.evaluate_io_events_mono>>
             fs[IS_PREFIX_APPEND])>>rw[]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          ‘ltree fs (mrec h_prog (h_prog (p,bst s))) =
           FUNPOW Tau n'' (Ret r):'a ptree’
            by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
          imp_res_tac nondiv_INR>>
          rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
          drule nondiv_evaluate'>>
          drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
          disch_then drule>>simp[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          drule mrec_Vis_no_trace_lemma>>
          disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
          PairCases_on ‘a’>>gvs[]>>
          Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          rpt (CASE_TAC>>fs[])>>
          TRY (irule_at Any LESS_EQ_REFL>>simp[FUNPOW])>>
          drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
          first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>
          drule io_events_eq_imp_ffi_eq>>rw[])>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_x_assum drule>>
      ‘(ext r 0 s.ffi).clock = 0’ by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>simp[]>>
      ‘∀k. s.ffi.io_events =
           (SND (evaluate (While e p,ext r k s.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[dec_clock_def]>>
         first_assum $ qspec_then ‘SUC k''’ assume_tac>>
         first_x_assum $ qspec_then ‘SUC (k'' + k''')’ assume_tac>>gs[]>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[]>>gvs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])
  >~ [‘Call’]
  >- (simp[mrec_Call,kvar_defs2]>>
      ntac 4 (TOP_CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      TRY (‘n' < SUC n'’ by simp[]>>
           first_assum drule>>
           disch_then drule>>simp[]>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[dec_clock_def,empty_locals_defs]>>
           ‘∀k. s.ffi.io_events =
                (SND (evaluate (q,s with <|locals:=r;clock := k|>))).ffi.io_events’ by
             (strip_tac>>
              first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[set_var_defs]>>
              rpt (CASE_TAC>>fs[])>>
              qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              fs[IS_PREFIX_APPEND]>>
              rw[]>>gvs[])>>rw[]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           ‘ltree fs (mrec h_prog (h_prog (q,bst (s with locals := r)))) =
            FUNPOW Tau n'' (Ret r'):'a ptree’
             by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
           imp_res_tac nondiv_INR>>
           rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
           drule nondiv_evaluate'>>
           drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
           disch_then drule>>simp[]>>
           disch_then $ assume_tac o GSYM>>fs[]>>
           drule mrec_Vis_no_trace_lemma>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
           PairCases_on ‘a’>>gvs[]>>
           Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
           Cases_on ‘fs’>>
           fs[mrec_h_handle_call_ret_lemma,empty_locals_defs,kvar_defs2]>>
           rpt (CASE_TAC>>fs[])>>
           irule_at Any LESS_EQ_REFL>>simp[FUNPOW] (* )*) >>
           drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
           first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[]>>rw[]>>
           qmatch_asmsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
           imp_res_tac panPropsTheory.evaluate_io_events_mono>>
           fs[IS_PREFIX_APPEND]>>gvs[]>>
           rev_drule io_events_eq_imp_ffi_eq>>rw[])>>
      TRY (first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>NO_TAC)>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      qpat_x_assum ‘mrec _ _ = FUNPOW _ _ (Vis _ _)’ mp_tac>>
      simp[mrec_h_handle_call_ret_lemma,empty_locals_defs,kvar_defs2]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rw[]>>
      Cases_on ‘n'-m'’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_assum drule>>
      ‘(ext (r' with locals := s.locals |+ (q''',v)) 0 s.ffi).clock = 0’
        by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then $ qspec_then ‘fs’ mp_tac>>
      fs[dec_clock_def,empty_locals_defs,set_var_defs]>>
      ‘s with <|locals := r; clock := k''; ffi := s.ffi|> =
       s with <|locals := r; clock := k''|>’
        by simp[state_component_equality]>>fs[]>>
      pop_assum kall_tac>>
      ‘∀k. s.ffi.io_events =
           (SND (evaluate (r''',ext (r' with locals:=s.locals |+ (q''',v)) k s.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[dec_clock_def]>>
         first_assum $ qspec_then ‘SUC k''’ mp_tac>>
         first_x_assum $ qspec_then ‘SUC (k'' + k''')’ mp_tac>>simp[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      ‘ltree fs (mrec h_prog (h_prog (r''',bst (ext (r' with locals:=s.locals|+(q''',v)) 0 s.ffi)))) =
       FUNPOW Tau n'' (Ret r''):'a ptree’
        by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
      imp_res_tac nondiv_INR>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[Excl"bst_ext_id"]>>
      drule nondiv_evaluate'>>
      drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
      disch_then drule>>simp[]>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      ‘(ext (r' with locals := s.locals |+ (q''',v)) 0 s.ffi).clock = 0’ by simp[]>>
      drule_at Any mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n’>>fs[FUNPOW_SUC]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      Cases_on ‘fs’>>fs[]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])
 >~ [‘DecCall’]
  >- (simp[mrec_DecCall]>>
      rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      TRY (‘n' < SUC n'’ by simp[]>>
           first_assum drule>>
           disch_then drule>>simp[]>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[dec_clock_def,empty_locals_defs]>>
           ‘∀k. s'.ffi.io_events =
                (SND (evaluate (q,s' with <|locals:=r;clock := k|>))).ffi.io_events’ by
             (strip_tac>>
              first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[set_var_defs]>>
              rpt (CASE_TAC>>fs[])>>
              qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              fs[IS_PREFIX_APPEND]>>
              rw[]>>gvs[])>>rw[]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           ‘ltree fs (mrec h_prog (h_prog (q,bst (s' with locals := r)))) =
            FUNPOW Tau n'' (Ret r'):'a ptree’
             by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
           imp_res_tac nondiv_INR>>
           rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
           drule nondiv_evaluate'>>
           drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
           disch_then drule>>simp[]>>
           disch_then $ assume_tac o GSYM>>fs[]>>
           drule mrec_Vis_no_trace_lemma>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
           PairCases_on ‘a’>>gvs[]>>
           Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
           Cases_on ‘fs’>>
           fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,set_var_defs]>>
           rpt (CASE_TAC>>fs[])>>
           irule_at Any LESS_EQ_REFL>>simp[FUNPOW]>>
           drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
           first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>
           rev_drule io_events_eq_imp_ffi_eq>>rw[])>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s'.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      qpat_x_assum ‘mrec _ _ = FUNPOW _ _ (Vis _ _)’ mp_tac>>
      simp[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,set_var_defs]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rw[]>>
      Cases_on ‘n'-m'’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_assum drule>>
      ‘(ext (r' with locals := s'.locals |+ (m0,v)) 0 s'.ffi).clock = 0’
        by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then $ qspec_then ‘fs’ mp_tac>>
      fs[dec_clock_def,empty_locals_defs,set_var_defs]>>
      ‘s' with <|locals := r; clock := k''; ffi := s'.ffi|> =
       s' with <|locals := r; clock := k''|>’
        by simp[state_component_equality]>>fs[]>>
      pop_assum kall_tac>>
      ‘∀k. s'.ffi.io_events =
           (SND (evaluate (p,ext (r' with locals:=s'.locals |+ (m0,v)) k s'.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[dec_clock_def]>>
         first_assum $ qspec_then ‘SUC k''’ mp_tac>>
         first_x_assum $ qspec_then ‘SUC (k'' + k''')’ mp_tac>>simp[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      ‘ltree fs (mrec h_prog (h_prog (p,bst (ext (r' with locals:=s'.locals|+(m0,v)) 0 s'.ffi)))) =
       FUNPOW Tau n'' (Ret r''):'a ptree’
        by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
      imp_res_tac nondiv_INR>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[Excl"bst_ext_id"]>>
      drule nondiv_evaluate'>>
      drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
      disch_then drule>>simp[]>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      ‘(ext (r' with locals := s'.locals |+ (m0,v)) 0 s'.ffi).clock = 0’ by simp[]>>
      drule_at Any mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n’>>fs[FUNPOW_SUC]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      Cases_on ‘fs’>>fs[]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])>>
  simp[mrec_ExtCall]>>
  rw[]>>gvs[AllCaseEqs()]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[empty_locals_defs]>>
  rpt (CASE_TAC>>fs[])>>qexists ‘SUC (SUC 0)’>>simp[FUNPOW]
QED

Theorem div_no_trace_LNIL:
  div fs (mrec h_prog (h_prog (p,bst s)):'a ptree) ∧
  (∀k. s.ffi.io_events =
       (SND (evaluate(p,s with clock := k + s.clock))).ffi.io_events) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ∧ s.clock = 0 ⇒
  trace_prefix fs (mrec h_prog (h_prog (p,bst s))) = [||]
Proof
  rw[]>>
  Cases_on ‘∃t. strip_tau (mrec h_prog (h_prog (p,bst s))) (t:'a ptree)’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      Cases_on ‘t’>>fs[]>>
      drule mrec_Vis_nondiv_lemma>>
      disch_then $ qspec_then ‘fs’ assume_tac>>
      gvs[div_def,FUNPOW_Ret_simp])>>
  imp_res_tac strip_tau_spin>>gvs[trace_prefix_spin]
QED

Theorem bounded_trace_eq:
  (∀k'. (SND(evaluate(p,s))).ffi.io_events
        = (SND(evaluate(p,s with clock:=k' + s.clock))).ffi.io_events) ∧
  div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) ⇒
  LAPPEND (fromList (s.ffi.io_events)) (trace_prefix (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s)))) =
  fromList (SND (evaluate (p, s:('a,'b) state))).ffi.io_events
Proof
  map_every qid_spec_tac [‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac>>
  pop_assum mp_tac>>
  once_rewrite_tac[evaluate_def]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  simp[mrec_prog_simps,mrec_Dec,mrec_If,mrec_ExtCall,
       mrec_ShMemLoad,mrec_ShMemStore]>>
  fs[panPropsTheory.eval_upd_clock_eq,call_FFI_def,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       rpt (pairarg_tac>>fs[])>>
       rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
       imp_res_tac trace_prefix_bind_div>>
       fs[LFINITE_fromList,GSYM LAPPEND_fromList,
          LAPPEND_NIL_2ND,empty_locals_defs]>>NO_TAC)
(* Dec *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
      (fs[div_bind_cases]
       >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
      imp_res_tac div_bind2>>fs[])
  (* Seq *)
  >~ [‘Seq’]
  >- (simp[mrec_Seq]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]
      >- (imp_res_tac evaluate_imp_nondiv>>gs[]>>
          fs[div_bind_cases]>- gvs[div_def]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          drule nondiv_evaluate'>>
          disch_then $ qspecl_then [‘s1’,‘NONE’,‘s.clock’] mp_tac>>gs[]>>
          ‘s with clock := s.clock = s’
            by simp[state_component_equality]>>gvs[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          imp_res_tac trace_prefix_bind_div>>fs[]>>
          first_assum irule>>
          rw[]>>
          imp_res_tac panPropsTheory.evaluate_add_clock_eq>>fs[]>>
          first_x_assum $ qspec_then ‘k' - s1.clock’ assume_tac>>
          first_x_assum $ qspec_then ‘k'- s1.clock + s.clock’ assume_tac>>
          gvs[])>>
      fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          first_x_assum irule>>rw[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>
          imp_res_tac div_imp_timeout>>fs[]>>
          first_x_assum $ qspec_then ‘k' + s.clock’ assume_tac>>
          gvs[])>>
      Cases_on ‘res ≠ SOME TimeOut’>>fs[]
      >- (imp_res_tac nondiv_INR>>gvs[]>>
          Cases_on ‘x’>>fs[]>>
          Cases_on ‘q’>>fs[]>>
          imp_res_tac nondiv_imp_evaluate>>fs[]>>
          Cases_on ‘s.clock < k’>>fs[NOT_LESS]
          >- (dxrule (GSYM LESS_ADD)>>strip_tac>>
              rev_drule panPropsTheory.evaluate_add_clock_eq>>simp[]>>
              disch_then $ qspec_then ‘p’ assume_tac>>fs[])>>
          dxrule LESS_EQUAL_ADD>>strip_tac>>
          drule panPropsTheory.evaluate_add_clock_eq>>simp[]>>
          disch_then $ qspec_then ‘p’ assume_tac>>
          ‘s with clock := s.clock = s’
            by simp[state_component_equality]>>gvs[])>>
      gvs[div_bind_cases]>>
      drule_then drule nondiv_timeout_add_clock>>rw[]>>fs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      Cases_on ‘q’>>fs[]>>
      gvs[div_bind_cases]>>
      Cases_on ‘evaluate (c2,t' with clock := 0)’>>fs[]>>
      drule evaluate_add_clock_or_timeout>>simp[]>>
      disch_then $ qspecl_then [‘s1’,‘SOME TimeOut’,‘s.clock’] mp_tac>>
      ‘s with clock := s.clock = s’ by simp[state_component_equality]>>
      fs[]>>rw[]>>
      ‘s1.ffi.io_events = r.ffi.io_events’ by
        (first_x_assum $ qspec_then ‘k' - s.clock’ mp_tac>>gvs[])>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      drule nondiv_evaluate'>>
      disch_then $ drule_at Any>>rw[]>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      fs[]>>
      drule trace_prefix_bind_div>>rw[]>>fs[]>>
      qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>fs[]>>
      ‘(t' with clock := 0).clock = 0’ by simp[]>>
      drule_at Any div_no_trace_LNIL>>simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      impl_tac >-
       (strip_tac>>
      first_x_assum $ qspec_then ‘k + k' - s.clock’ assume_tac>>fs[]>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘k’ assume_tac>>gvs[])>>rw[])
     (* If (the same as Dec) *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
      (fs[div_bind_cases]
       >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
      imp_res_tac div_bind2>>fs[])
  >- (once_rewrite_tac[mrec_While]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
      fs[dec_clock_def,empty_locals_defs]>>
      fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_assum $ qspec_then ‘0’ assume_tac>>fs[]>>
          last_assum $ qspec_then ‘SUC 0’ mp_tac>>
          strip_tac>>gvs[]>>
          drule div_no_trace_LNIL>>fs[]>>
          impl_tac >-
           (strip_tac>>
            first_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
            last_assum $ qspec_then ‘SUC k’ mp_tac>>
            strip_tac>>fs[])>>
          strip_tac>>gvs[LAPPEND_NIL_2ND])
      >- (imp_res_tac nondiv_INR>>fs[]>>
          Cases_on ‘x’>>fs[]>>
          imp_res_tac nondiv_imp_evaluate>>gvs[]>>
          dxrule evaluate_min_clock>>rw[]>>
          Cases_on ‘q’>>fs[]>>
          TRY (rename [‘evaluate _ = (SOME x,_)’]>>Cases_on ‘x’)>>gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          simp[LAPPEND_ASSOC]>>
          last_assum $ qspec_then ‘SUC k'’ mp_tac>>
          strip_tac>>fs[]>>gvs[]>>
          drule nondiv_evaluate'>>fs[]>>
          disch_then $ drule_at Any>>
          simp[]>>strip_tac>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_assum $ qspec_then ‘0’ assume_tac>>fs[]>>
          drule_then mp_tac panPropsTheory.evaluate_io_events_mono>>
          simp[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          ‘(t' with clock := 0).clock = 0’ by simp[]>>
          drule_at Any div_no_trace_LNIL>>simp[]>>
          disch_then $ drule_at Any>>simp[]>>
          (impl_tac >-
            (strip_tac>>
             last_x_assum $ qspec_then ‘SUC (k' + k)’ (mp_tac o GSYM)>>
             simp[]>>
             rev_drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘k’ assume_tac>>fs[]))>>rw[])
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_x_assum $ qspec_then ‘s.clock - 1’ assume_tac>>gvs[]>>
          last_assum $ irule>>
          strip_tac>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_x_assum $ qspec_then ‘k' + s.clock - 1’ assume_tac>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[])>>
      imp_res_tac nondiv_INR>>fs[]>>
      Cases_on ‘x’>>fs[]>>
      imp_res_tac nondiv_imp_evaluate>>gvs[]>>
      Cases_on ‘q’>>fs[]>>
      TRY (rename [‘evaluate _ = (SOME x,_)’]>>Cases_on ‘x’)>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,s with clock := k) = (X,t')’>>
      (Cases_on ‘res ≠ SOME TimeOut’>>fs[]
      >- (‘res = X ∧ t' = s1 with clock := t'.clock’ by
            ((Cases_on ‘s.clock - 1 < k’
             >- (dxrule (GSYM LESS_ADD)>>strip_tac>>
                 rev_drule panPropsTheory.evaluate_add_clock_eq>>
                 disch_then $ qspec_then ‘p’ assume_tac>>fs[]>>
                 gvs[]))>>
             fs[NOT_LESS]>>dxrule LESS_EQUAL_ADD>>strip_tac>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘p’ assume_tac>>fs[]>>
             gvs[state_component_equality,Abbr‘X’])>>
          gvs[]>>
          ‘bst t' = bst s1’ by
            (pop_assum (fn h => rewrite_tac[Once h])>>simp[bst_def])>>
          fs[]>>
          qpat_x_assum ‘_ = (X,t')’ kall_tac>>
          qpat_x_assum ‘t' = _’ kall_tac>>
          pop_assum kall_tac>>fs[Abbr‘X’]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          drule nondiv_evaluate'>>
          disch_then $ drule_at Any>>rw[]>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          imp_res_tac div_imp_timeout>>gvs[]>>
          first_x_assum $ qspec_then ‘s1.clock’ assume_tac>>fs[]>>
          ‘s1 with clock := s1.clock = s1’
            by simp[state_component_equality]>>gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          last_x_assum irule>>
          strip_tac>>
          drule div_imp_timeout>>rw[]>>
          first_x_assum $ qspec_then ‘k' + s1.clock’ assume_tac>>fs[]>>
          last_x_assum $ qspec_then ‘k'’ mp_tac>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]))>>
      gvs[]>>
      dxrule evaluate_min_clock>>
      ‘X ≠ SOME TimeOut’ by simp[Abbr‘X’]>>rw[]>>
      drule evaluate_add_clock_or_timeout>>
      disch_then $ qspecl_then [‘s1’,‘SOME TimeOut’,‘s.clock - 1’] mp_tac>>
      simp[]>>rw[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘X’]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      drule nondiv_evaluate'>>
      disch_then $ drule_at Any>>rw[]>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      gvs[]>>
      imp_res_tac div_imp_timeout>>fs[]>>
      first_x_assum $ qspec_then ‘0’ assume_tac>>fs[]>>
      ‘t.ffi.io_events = s.ffi.io_events ++ l'’ by
        (last_x_assum $ qspec_then ‘k' - (s.clock - 1)’ mp_tac>>simp[])>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      assume_tac (Q.SPECL [‘c’,‘s with clock := s.clock -1’,‘k' - (s.clock - 1)’]
                   panPropsTheory.evaluate_add_clock_io_events_mono)>>
      gvs[]>>
      fs[IS_PREFIX_APPEND]>>
      simp[LFINITE_LAPPEND_EQ_NIL]>>
      ‘(t' with clock := 0).clock = 0’ by simp[]>>
      drule_at Any div_no_trace_LNIL>>simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      (impl_tac >-
        (strip_tac>>
         first_x_assum $ qspec_then ‘k + k' - (s.clock - 1)’ mp_tac>>fs[]>>
         qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
         drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k’ assume_tac>>gvs[])>>rw[]))
(* Call *)
  >- (simp[mrec_Call,empty_locals_defs,kvar_defs2]>>
      ntac 4 (TOP_CASE_TAC>>fs[])
      >- (rw[]>>fs[div_bind_cases]
          >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
              imp_res_tac div_imp_timeout>>fs[]>>
              drule div_no_trace_LNIL>>simp[]>>
              impl_tac >-
               (strip_tac>>
                last_x_assum $ qspec_then ‘SUC k’ mp_tac>>
                simp[dec_clock_def]>>
                first_x_assum $ qspec_then ‘k’ assume_tac>>fs[])>>
              first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              strip_tac>>fs[LAPPEND_NIL_2ND])>>
          imp_res_tac nondiv_INR>>fs[]>>
          rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
          imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
          dxrule evaluate_min_clock>>rw[]>>
          rename [‘s with <|locals:=r;clock := k|>’]>>
          drule nondiv_evaluate'>>fs[]>>
          disch_then $ drule_at Any>>
          disch_then $ drule_at Any>>
          simp[]>>strip_tac>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>

          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          last_assum $ qspec_then ‘SUC k’ (mp_tac o GSYM)>>
          rpt (TOP_CASE_TAC>>
               fs[kvar_defs2,empty_locals_defs,dec_clock_def,
                  div_bind_cases,kvar_defs2,
                  mrec_h_handle_call_ret_lemma])>>
          imp_res_tac trace_prefix_bind_div>>gvs[]>>
          (drule evaluate_add_clock_or_timeout>>fs[]>>
           disch_then $ drule_at Any>>strip_tac>>fs[])
          (** 3 goals **)
          >- (qmatch_goalsub_abbrev_tac ‘evaluate (_,tt)’>>
              qpat_abbrev_tac ‘X = evaluate _’>>
              Cases_on ‘X’>>fs[]>>rw[]>>
              drule panPropsTheory.evaluate_io_events_mono>>
              simp[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
              simp[LFINITE_LAPPEND_EQ_NIL]>>
              ‘tt.clock = 0’ by simp[Abbr‘tt’]>>
              drule_at Any div_no_trace_LNIL>>simp[]>>fs[Abbr‘tt’]>>
              disch_then $ drule_at Any>>simp[]>>
              impl_tac >-
               (strip_tac>>
                drule div_imp_timeout>>
                disch_then $ qspec_then ‘k'’ assume_tac>>fs[]>>
                first_x_assum $ qspec_then ‘SUC (k + k')’ mp_tac>>
                fs[]>>
                qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
                drule panPropsTheory.evaluate_add_clock_eq>>
                disch_then $ qspec_then ‘k'’ assume_tac>>rw[]>>gvs[])>>rw[])>>
          (** the remaining two **)
          imp_res_tac div_imp_timeout>>fs[]>>
          first_assum $ qspec_then ‘0’ mp_tac>>
          first_x_assum $ qspec_then ‘k' - (k + 1)’ mp_tac>>simp[]>>rw[]>>
          gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          first_assum $ qspec_then ‘SUC k’ (mp_tac o SIMP_RULE (srw_ss())[])>>
          simp[]>>rw[]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_,t'')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>
          drule_at Any div_no_trace_LNIL>>simp[]>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          (impl_tac >-
            (strip_tac>>
             drule div_imp_timeout>>
             disch_then $ qspec_then ‘k''’ assume_tac>>fs[]>>
             first_x_assum $ qspec_then ‘SUC (k + k'')’ mp_tac>>
             fs[]>>
             qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘k''’ assume_tac>>rw[]>>gvs[])>>rw[]))>>
      (** s.clock ≠ 0 **)
      rw[]>>fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[dec_clock_def]>>
          drule div_imp_timeout>>simp[]>>
          disch_then $ qspec_then ‘s.clock - 1’ assume_tac>>fs[]>>
          gvs[]>>
          first_x_assum irule>>
          strip_tac>>
          drule div_imp_timeout>>simp[]>>
          disch_then $ qspec_then ‘k' + s.clock - 1’ assume_tac>>fs[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[])>>
      imp_res_tac nondiv_INR>>fs[dec_clock_def]>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
      imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      (**)
      qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>rw[]>>
      qabbrev_tac ‘tt = s.clock -1’>>
      Cases_on ‘k' ≤ tt’>>fs[NOT_LESS_EQUAL]
      >- (dxrule_then strip_assume_tac LESS_EQUAL_ADD>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          disch_then $ qspec_then ‘p’ assume_tac>>gvs[]>>
          rpt (TOP_CASE_TAC>>
               fs[kvar_defs2,empty_locals_defs,dec_clock_def,
                  div_bind_cases,
                  mrec_h_handle_call_ret_lemma])>>
          imp_res_tac trace_prefix_bind_div>>gvs[]>>
          (drule evaluate_add_clock_or_timeout>>fs[]>>
           disch_then $ drule_at Any>>strip_tac>>fs[])>>gvs[]>>
          qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          last_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
          qpat_x_assum ‘evaluate (q,_) = _’ assume_tac>>
          first_assum (fn h => rewrite_tac[h])>>simp[]>>
          qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          first_x_assum irule>>
          strip_tac>>
          last_x_assum $ qspec_then ‘k'''’ mp_tac>>gvs[]>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          disch_then $ qspec_then ‘k''' + p’ assume_tac>>rw[]>>
          ‘k' + k''' + p = k''' + s.clock - 1’ by gvs[]>>gvs[])>>
      (** timeout at s.clock - 1 **)
      drule evaluate_add_clock_or_timeout>>fs[]>>
      disch_then $ drule_at Any>>strip_tac>>fs[]>>
      drule panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      first_assum $ qspec_then ‘k' - tt’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      ‘k' - tt + s.clock - 1 = k'’ by gvs[Abbr‘tt’]>>
      pop_assum (fn h => rewrite_tac[h])>>simp[]>>
      rpt (TOP_CASE_TAC>>
           fs[kvar_defs2,empty_locals_defs,dec_clock_def,
              div_bind_cases,
              mrec_h_handle_call_ret_lemma])>>
      imp_res_tac trace_prefix_bind_div>>gvs[]>>
      qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := _ + s.clock - 1|>) = _’ assume_tac>>
      (drule evaluate_add_clock_or_timeout>>fs[]>>
       disch_then $ drule_at Any>>strip_tac>>fs[])>>
      fs[div_bind_cases]>>
      imp_res_tac trace_prefix_bind_div>>gvs[]
      (*** 3 goals *)
      >- (qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
                       panPropsTheory.evaluate_add_clock_io_events_mono)>>
          gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
          first_assum $ qspec_then ‘0’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
          qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := s.clock - 1|>) = _’ assume_tac>>
          first_assum (fn h => rewrite_tac[h])>>simp[]>>
          rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, r''')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
          drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          impl_tac >-
           (strip_tac>>
            irule EQ_TRANS>>first_x_assum $ irule_at Any>>
            qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
            rev_drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[])>>rw[])
      (**2/3*)
      >- (qmatch_goalsub_abbrev_tac ‘_ = (SND X).ffi.io_events’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
                       panPropsTheory.evaluate_add_clock_io_events_mono)>>
          gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
          first_assum $ qspec_then ‘0’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
          qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := s.clock - 1|>) = _’ assume_tac>>
          first_assum (fn h => rewrite_tac[h])>>simp[]>>
          rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, r'')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
          drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          impl_tac >-
           (strip_tac>>
            irule EQ_TRANS>>first_x_assum $ irule_at Any>>
            qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
            rev_drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[])>>rw[])>>
      (**1/3*)
      rpt (FULL_CASE_TAC>>gvs[]))>>
  (* DecCall *)
  simp[mrec_DecCall,empty_locals_defs]>>
  ntac 4 (TOP_CASE_TAC>>fs[])
  >- (rw[]>>fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          imp_res_tac div_imp_timeout>>fs[]>>
          drule div_no_trace_LNIL>>simp[]>>
          impl_tac >-
           (strip_tac>>
            last_x_assum $ qspec_then ‘SUC k’ mp_tac>>
            simp[dec_clock_def]>>
            first_x_assum $ qspec_then ‘k’ assume_tac>>fs[])>>
          first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          strip_tac>>fs[LAPPEND_NIL_2ND])>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
      imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      rename [‘s with <|locals:=r;clock := k|>’]>>
      drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>

      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      last_assum $ qspec_then ‘SUC k’ (mp_tac o GSYM)>>
      rpt (TOP_CASE_TAC>>
           fs[kvar_defs2,empty_locals_defs,dec_clock_def,
              div_bind_cases,
              mrec_h_handle_deccall_ret_lemma])>>
      imp_res_tac trace_prefix_bind_div>>gvs[]>>
      (drule evaluate_add_clock_or_timeout>>fs[]>>
       disch_then $ drule_at Any>>strip_tac>>fs[])
      >- (qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          drule panPropsTheory.evaluate_io_events_mono>>
          simp[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, r')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
          drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          impl_tac >-
           (strip_tac>>
            irule EQ_TRANS>>first_x_assum $ irule_at Any>>
            qexists ‘SUC (k + k')’>>simp[]>>
            rev_drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘k'’ assume_tac>>rw[]>>gvs[]>>
            pairarg_tac>>fs[])>>rw[])>>
      (* 2/3 & 3/3 *)
      rpt (pairarg_tac>>fs[])>>rw[]>>gvs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      first_assum $ qspec_then ‘SUC k’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      simp[]>>rw[]>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, st')’>>
      ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
      drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
      disch_then $ drule_at Any>>simp[]>>
      (impl_tac >-
        (strip_tac>>
         irule EQ_TRANS>>first_x_assum $ irule_at Any>>
         qexists ‘SUC (k'' + k)’>>simp[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k''’ assume_tac>>rw[]>>
         gvs[]>>pairarg_tac>>fs[])>>rw[]))>>
  (* s.clock ≠ 0 *)
  rw[]>>fs[div_bind_cases]
  >- (imp_res_tac trace_prefix_bind_div>>fs[dec_clock_def]>>
      drule div_imp_timeout>>simp[]>>
      disch_then $ qspec_then ‘s.clock - 1’ assume_tac>>fs[]>>
      drule panPropsTheory.evaluate_io_events_mono>>
      simp[IS_PREFIX_APPEND]>>rw[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      first_x_assum irule>>
      strip_tac>>
      drule div_imp_timeout>>simp[]>>
      disch_then $ qspec_then ‘k' + s.clock - 1’ assume_tac>>fs[]>>
      first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[])>>
  imp_res_tac nondiv_INR>>fs[dec_clock_def]>>
  rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
  imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
  dxrule evaluate_min_clock>>rw[]>>
  drule nondiv_evaluate'>>fs[]>>
  disch_then $ drule_at Any>>
  disch_then $ drule_at Any>>
  simp[]>>strip_tac>>
  pop_assum $ assume_tac o GSYM>>fs[]>>
  drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
  fs[]>>
  imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
  imp_res_tac trace_prefix_bind_append>>fs[]>>
  imp_res_tac panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>gvs[]>>
  fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
  qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
  fs[LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
  (**)
  qpat_abbrev_tac ‘X = evaluate _’>>
  Cases_on ‘X’>>fs[]>>rw[]>>
  qabbrev_tac ‘tt = s.clock -1’>>
  Cases_on ‘k' ≤ tt’>>fs[NOT_LESS_EQUAL]
  >- (dxrule_then strip_assume_tac LESS_EQUAL_ADD>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘p’ assume_tac>>gvs[]>>
      
      rpt (TOP_CASE_TAC>>
           fs[kvar_defs2,empty_locals_defs,dec_clock_def,
              div_bind_cases,
              mrec_h_handle_deccall_ret_lemma])>>
      imp_res_tac trace_prefix_bind_div>>gvs[]>>
      (drule evaluate_add_clock_or_timeout>>fs[]>>
       disch_then $ drule_at Any>>strip_tac>>fs[])>>gvs[]>>
      qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>rw[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>

      last_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      qpat_x_assum ‘evaluate (q,_) = _’ assume_tac>>
      first_assum (fn h => rewrite_tac[h])>>simp[]>>
      qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>rw[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      first_x_assum irule>>
      strip_tac>>
      last_x_assum $ qspec_then ‘k'''’ mp_tac>>gvs[]>>

      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘k''' + p’ assume_tac>>rw[]>>
      ‘k' + k''' + p = k''' + s.clock - 1’ by gvs[]>>gvs[]>>
      pairarg_tac>>fs[])>>
  (** timeout at s.clock - 1 **)
  drule evaluate_add_clock_or_timeout>>fs[]>>
  disch_then $ drule_at Any>>strip_tac>>fs[]>>
  drule panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>
  fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
  first_assum $ qspec_then ‘k' - tt’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
  ‘k' - tt + s.clock - 1 = k'’ by gvs[Abbr‘tt’]>>
  pop_assum (fn h => rewrite_tac[h])>>simp[]>>
  rpt (TOP_CASE_TAC>>
       fs[kvar_defs2,empty_locals_defs,dec_clock_def,
          div_bind_cases,
          mrec_h_handle_deccall_ret_lemma])>>
  imp_res_tac trace_prefix_bind_div>>gvs[]>>
  qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := _ + s.clock - 1|>) = _’ assume_tac>>
  drule evaluate_add_clock_or_timeout>>fs[]>>
  disch_then $ drule_at Any>>strip_tac>>fs[]>>
  fs[div_bind_cases]>>
  imp_res_tac trace_prefix_bind_div>>gvs[]
  (*** 2 goals ***)
  >- (pairarg_tac>>fs[]>>
      assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
                   panPropsTheory.evaluate_add_clock_io_events_mono)>>
      gvs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
      rw[]>>gvs[]>>
      first_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := k'' + s.clock - 1|>) = _’ assume_tac>>
      first_assum (fn h => rewrite_tac[h])>>simp[]>>
      rw[]>>gvs[]>>
      simp[LFINITE_LAPPEND_EQ_NIL]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, st')’>>
      ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
      drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
      disch_then $ drule_at Any>>simp[]>>
      impl_tac >-
       (strip_tac>>
        irule EQ_TRANS>>first_x_assum $ irule_at Any>>
        qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
        qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := k'|>) = _’ assume_tac>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[]>>
        pairarg_tac>>fs[])>>rw[])>>
  (** last **)
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
               panPropsTheory.evaluate_add_clock_io_events_mono)>>
  gvs[]>>
  imp_res_tac panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>gvs[]>>
  fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
  first_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
  qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := k'' + s.clock - 1|>) = _’ assume_tac>>
  first_assum (fn h => rewrite_tac[h])>>simp[]>>
  rw[]>>gvs[]>>
  simp[LFINITE_LAPPEND_EQ_NIL]>>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_,st'')’>>
  ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
  drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
  disch_then $ drule_at Any>>simp[]>>
  impl_tac >-
   (strip_tac>>
    irule EQ_TRANS>>first_x_assum $ irule_at Any>>
    qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
    qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
    drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[]>>
    pairarg_tac>>fs[])>>rw[]
QED

(**************************)

Definition evaluate_behaviour_def:
  evaluate_behaviour (prog,s) =
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

Definition itree_behaviour_def:
  itree_behaviour pre fs (prog, s) =
  let trace = trace_prefix fs (mrec h_prog (h_prog (prog,s))) in
    case some r.
           ∃n s'. ltree fs (mrec h_prog (h_prog (prog,s)))
               = FUNPOW Tau n (Ret (INR (r, s'))): 'a ptree
    of
      SOME r =>
        (case r of
           SOME (FinalFFI e) =>
             (case llist$toList trace of
                NONE => Fail
              | SOME io => Terminate (FFI_outcome e) (pre++io))
         | SOME (Return _) =>
             (case llist$toList trace of
                NONE => Fail
              | SOME io => Terminate Success (pre++io))
         | _ => Fail)
    | NONE => Diverge (LAPPEND (fromList pre) trace)
End

Theorem evaluate_imp_itree:
  evaluate_behaviour (prog,s) =
  itree_behaviour s.ffi.io_events (s.ffi.oracle,s.ffi.ffi_state) (prog,bst s)
Proof
  simp[evaluate_behaviour_def,itree_behaviour_def]>>
  rw[]>>
  DEEP_INTRO_TAC some_intro>>
  rw[]
  (* Fail *)
  >- (imp_res_tac nondiv_imp_evaluate>>
      dxrule evaluate_min_clock>>strip_tac>>gs[]>>
      Cases_on ‘evaluate (prog, s with clock := k)’>>fs[]>>
      ‘q ≠ SOME TimeOut ⇒ k'' ≤ k’ by
        (strip_tac>>
         CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
         imp_res_tac (GSYM LESS_ADD)>>fs[]>>
         drule panPropsTheory.evaluate_add_clock_eq>>fs[]>>
         qexists ‘p’>>strip_tac>>gvs[state_component_equality])>>
      rpt (FULL_CASE_TAC>>fs[])>>
      imp_res_tac LESS_EQUAL_ADD>>fs[]>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘p’ assume_tac>>fs[])
  >- (Cases_on ‘evaluate (prog, s with clock := k)’>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      imp_res_tac evaluate_imp_nondiv>>gvs[])
  >- (fs[]>>
      first_x_assum $ qspec_then ‘k’ assume_tac>>
      gvs[]>>
      Cases_on ‘r’>>fs[]>>
      rename [‘(SOME x,_)’]>>
      Cases_on ‘x’>>fs[]>>
      imp_res_tac evaluate_imp_nondiv>>gvs[]>>
      drule evaluate_nondiv_trace_eq>>fs[]>>
      strip_tac>>simp[]>>
      ‘LFINITE (fromList t.ffi.io_events)’
        by simp[LFINITE_fromList]>>
      pop_assum mp_tac>>
      first_assum (fn h => rewrite_tac[h])>>
      rewrite_tac[LFINITE_APPEND]>>strip_tac>>
      imp_res_tac to_fromList>>fs[from_toList]>>gvs[]>>
      qpat_x_assum ‘fromList _ = LAPPEND _ _’ mp_tac>>
      first_assum (fn h => once_rewrite_tac[GSYM h])>>
      rewrite_tac[LAPPEND_fromList]>>
      rewrite_tac[fromList_11]>>strip_tac>>
      simp[from_toList])>>
  DEEP_INTRO_TAC some_intro>>
  rw[]
  >- (rpt (CASE_TAC>>fs[])>>
      imp_res_tac nondiv_imp_evaluate>>gvs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>
  irule EQ_SYM>>
  irule (iffLR lprefix_lubTheory.build_prefix_lub_intro)>>
  irule_at Any evaluate_io_events_lprefix_chain>>
  simp[lprefix_lubTheory.lprefix_lub_def]>>fs[]>>
  conj_asm1_tac>>rpt strip_tac>>gvs[]
  >- (qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>
      ‘div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (prog,bst s)):'a ptree)’
        by (gvs[div_def]>>rw[]>>
            strip_tac>>
            imp_res_tac nondiv_INR>>gvs[]>>
            rename [‘Ret (INR x)’]>>Cases_on ‘x’>>gvs[])>>
      drule div_imp_timeout>>
      disch_then $ qspec_then ‘k’ assume_tac>>gvs[]>>
      drule timeout_div_LPREFIX>>simp[])>>
  (* least upper bound *)
  Cases_on ‘∀n. (∃k. less_opt n (SOME (LENGTH (SND (evaluate(prog,s with clock := k))).ffi.io_events)))’>>fs[]
  >- fs[LPREFIX_NTH]>>
  (* evaluate traces are bounded *)
  dxrule not_less_opt_lemma>>
  strip_tac>>gvs[]>>
  qabbrev_tac ‘x= s with clock := k'’>>
  ‘∀k. x.clock < k ⇒
       (SND (evaluate (prog,x))).ffi.io_events =
       (SND (evaluate (prog,x with clock := k))).ffi.io_events’
    by (rpt strip_tac>>
        first_x_assum $ qspec_then ‘k’ assume_tac>>
        qspecl_then [‘prog’,‘x’,‘k-x.clock’] assume_tac (panPropsTheory.evaluate_add_clock_io_events_mono)>>
        rfs[Abbr‘x’]>>
        gvs[GSYM IS_PREFIX_LENGTH_ANTI])>>
  ‘div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (prog,bst s)):'a ptree)’
    by (gvs[div_def]>>rw[]>>
        strip_tac>>
        imp_res_tac nondiv_INR>>gvs[]>>
        rename [‘Ret (INR x)’]>>Cases_on ‘x’>>gvs[])>>
  ‘∀k. (SND (evaluate (prog,x))).ffi.io_events =
       (SND (evaluate (prog,x with clock := k + x.clock))).ffi.io_events’
    by (strip_tac>>
        Cases_on ‘k’>>simp[state_component_equality,Abbr‘x’])>>
  drule bounded_trace_eq>>fs[Abbr‘x’]>>
  strip_tac>>simp[]>>
  first_assum irule>>metis_tac[]
QED

(**************************)
(**************************)
