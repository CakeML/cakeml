(*
  An abstracted itree semantics for Pancake.
*)
Theory panItreeAbsSem
Ancestors
  itreeTau panLang panSem
  pan_itreeSem pan_itreeProps
Libs
  preamble

val _ = monadsyntax.enable_monadsyntax();
val _ = declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
                      ignorebind = NONE,
                      choice = NONE,
                      fail = NONE,
                      guard = NONE});
val _ = enable_monad "itree";

(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;


Definition itree_semantics_def:
  itree_semantics = mrec h_prog o h_prog
End

val res = “res:(ffi_outcome + word8 list) + 'a result option # 'a bstate”

Definition itree_deccall_handler_def:
  itree_deccall_handler rt shape s ^res tree1 =
  case res of
  | INR (NONE,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Break,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Continue,s') => Ret (INR (SOME Error,s'))
  | INR (SOME (Return retv), s') =>
      (if shape_of retv = shape then
         Tau
         (tree1
          (set_var rt retv (s' with locals := s.locals)) >>=
                (λ^res. Ret
                     (INR
                      (case res of
                         INL v => (SOME Error,s')
                       | INR (q,r') =>
                           (q, r' with locals := res_var r'.locals (rt, FLOOKUP s.locals rt))))))
       else Ret (INR (SOME Error, s')))
  | INR (res,s') => Ret (INR (res,empty_locals s'))
  | INL _ => Ret (INR (SOME Error,s))
End

Definition itree_call_handler_def:
  itree_call_handler calltyp s ^res =
  case res of
  | INR (NONE,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Break,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Continue,s') => Ret (INR (SOME Error,s'))
  | INR (SOME (Exception eid exn),s') =>
      (case calltyp of
         SOME (_, SOME (eid', evar, p)) =>
           (if eid' = eid
            then
              (case FLOOKUP s.eshapes eid of
                 SOME sh =>
                   (if shape_of exn = sh ∧ is_valid_value s Local evar exn
                    then Tau (itree_bind
                              ((itree_semantics (p,set_var evar exn (s' with locals := s.locals))):'a ptree)
                              (λ^res. Ret (INR
                                        (case res of
                                           INL _ => (SOME Error,s')
                                         | INR (q,t) => (q,t)))))
                    else Ret (INR (SOME Error,s')))
               | NONE => Ret (INR (SOME Error,s')))
            else Ret (INR (SOME (Exception eid exn),empty_locals s')))
       | _ => Ret (INR (SOME (Exception eid exn),empty_locals s')))
  | INR (SOME (Return retv), s') =>
      (case calltyp of
         NONE => Ret (INR (SOME (Return retv),empty_locals s'))
       | SOME (NONE, _) => Ret (INR (NONE, s' with locals := s.locals))
       | SOME (SOME (rk,rt), _) =>
           if is_valid_value s rk rt retv
           then Ret (INR (NONE,set_kvar rk rt retv (s' with locals := s.locals)))
           else Ret (INR (SOME Error,s')))
  | INR (res,s') => Ret (INR (res,empty_locals s'))
  | INL _ => Ret (INR (SOME Error,s))
End

Theorem itree_bind_bisim_intro:
  t = t' ∧ k = k' ⇒ (t >>= k) = (t' >>= k')
Proof
  rpt strip_tac
  \\ rw[]
QED

Theorem itree_semantics_While:
  ((itree_semantics (While e p,s)):'a ptree) =
  case eval s e of
    SOME (ValWord w) =>
      if w = 0w then Ret (INR (NONE, s))
      else
        Tau ((((itree_semantics (p,s))):'a ptree) >>=
             (λa.
                case a of
                  INL l => Ret (INR (SOME Error, s))
                | INR (res,s') =>
                    case res of
                      NONE => Tau (itree_semantics (While e p, s'))
                    | SOME Break => Ret (INR (NONE, s'))
                    | SOME Continue => Tau (itree_semantics (While e p, s'))
                    | _ => Ret (INR (res, s'))))
  | _ => Ret (INR (SOME Error, s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF]
  \\ fs[SimpLHS, h_prog_def, h_prog_while_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
  \\ rpt (CASE_TAC \\ fs[GSYM h_prog_while_def,h_prog_def])
QED

Theorem itree_semantics_Seq:
  ((itree_semantics (Seq p q, s)):'a ptree) =
  Tau (itree_bind
       ((itree_semantics (p, s)):'a ptree)
       (λa. case a of
              INL l => Ret (INR (SOME Error, s))
            | INR (NONE,s') =>
                Tau (((itree_semantics (q, s')):'a ptree) >>=
                                (λa.
                                   Ret (INR
                                   (case a of
                                      INL v => (SOME Error,s)
                                    | INR (res,s') => (res,s')))))
            | INR (SOME res, s') => Ret (INR (SOME res, s'))))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_seq_def, Once itree_iter_thm]
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
  \\ rpt (CASE_TAC \\ fs[h_prog_def])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_Dec:
  ((itree_semantics (Dec x sh e p, s)):'a ptree) =
  case eval s e of
    SOME v =>
      Tau (((itree_semantics (p,s with locals := s.locals |+ (x,v))):'a ptree) >>=
           (λa. Ret (INR (case a of
                            INL l => (SOME Error, s)
                          | INR (res,s') =>
                              (res, s' with
                     locals := res_var s'.locals (x,FLOOKUP s.locals x))))))
  | _ => Ret (INR (SOME Error, s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_dec_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_Assign:
  ((itree_semantics (Assign vk x v, s)):'a ptree) =
  case eval s v of
    SOME v =>
      Ret (INR (if is_valid_value s vk x v then
                  (NONE, set_kvar vk x v s)
                else (SOME Error, s)))
  | _ => Ret (INR (SOME Error, s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_assign_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
QED

Theorem itree_semantics_If:
  ((itree_semantics (If e p q, s)):'a ptree) =
  case eval s e of
    SOME (ValWord v) =>
      Tau (((itree_semantics (if v ≠ 0w then p else q,s)):'a ptree) >>=
                      (λa. Ret (INR (case a of
                                       INL l => (SOME Error,s)
                                     | INR (res,s') => (res,s')))))
  | _ => Ret (INR (SOME Error, s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_cond_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_Store:
  ((itree_semantics (Store dst src, s)):'a ptree) =
  Ret (INR (case (eval s dst, eval s src) of
    (NONE, v3) => (SOME Error, s)
  | (SOME (ValWord ad), NONE) => (SOME Error, s)
  | (SOME (ValWord ad), SOME v) =>
      (case mem_stores ad (flatten v) s.memaddrs s.memory of
         NONE => (SOME Error, s)
       | SOME m => (NONE, s with memory := m))
  | _ => (SOME Error, s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
QED

Theorem itree_semantics_StoreByte:
  ((itree_semantics (StoreByte dst src, s)):'a ptree) =
  Ret (INR (case (eval s dst, eval s src) of
              (NONE, v3) => (SOME Error, s)
            | (SOME (ValWord ad), NONE) => (SOME Error, s)
            | (SOME (ValWord ad), SOME (ValWord v)) =>
                (case mem_store_byte s.memory s.memaddrs s.be ad (w2w v) of
                   NONE => (SOME Error, s)
                 | SOME m => (NONE, s with memory := m))
            | _ => (SOME Error, s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_byte_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
QED

Theorem itree_semantics_Store32:
  ((itree_semantics (Store32 dst src, s)):'a ptree) =
  Ret (INR (case (eval s dst, eval s src) of
              (NONE, v3) => (SOME Error, s)
            | (SOME (ValWord ad), NONE) => (SOME Error, s)
            | (SOME (ValWord ad), SOME (ValWord v)) =>
                (case mem_store_32 s.memory s.memaddrs s.be ad (w2w v) of
                   NONE => (SOME Error, s)
                 | SOME m => (NONE, s with memory := m))
            | _ => (SOME Error, s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_32_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
QED

Theorem itree_semantics_ShMemLoad:
  ((itree_semantics (ShMemLoad op vk v addr, s)):'a ptree) =
  case (eval s addr, lookup_kvar vk v s) of
    (SOME (ValWord ad), SOME (Val _)) =>
      (if nb_op op = 0 then
         (if ad ∈ s.sh_memaddrs then
            Vis (SharedMem MappedRead,[0w],word_to_bytes ad F)
                (λres.
                   Tau (Ret
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
             (λres.
                Tau (Ret
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
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_sh_mem_load_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_ShMemStore:
  ((itree_semantics (ShMemStore op addr e, s)):'a ptree) =
  case (eval s addr, eval s e) of
    (SOME (ValWord ad), SOME (ValWord w)) =>
      if nb_op op = 0 then
        if ad ∈ s.sh_memaddrs then
          Vis
          (SharedMem MappedWrite,[0w],word_to_bytes w F ++ word_to_bytes ad F)
          (λres.
             Tau (Ret
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
            (λres.
               Tau (Ret
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
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_sh_mem_store_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_Skip:
  itree_semantics (Skip,s) = Ret (INR (NONE,s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def]
QED

Theorem itree_semantics_Break:
  itree_semantics (Break,s) = Ret (INR (SOME Break,s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def]
QED

Theorem itree_semantics_Tick:
  itree_semantics (Tick,s) = Ret (INR (NONE,s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def]
QED

Theorem itree_semantics_Annot:
  itree_semantics (Annot x y,s) = Ret (INR (NONE,s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def]
QED

Theorem itree_semantics_Continue:
  itree_semantics (Continue,s) = Ret (INR (SOME Continue,s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def]
QED

Theorem itree_semantics_Return:
  itree_semantics (Return e,s) =
  Ret (INR (case eval s e of
              NONE => (SOME Error,s)
            | SOME v =>
                if size_of_shape (shape_of v) ≤ 32 then
                  (SOME (Return v), empty_locals s)
                else (SOME Error,s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def, h_prog_return_def]
QED

Theorem itree_semantics_Raise:
  itree_semantics (Raise eid e,s) =
  Ret (INR (case (FLOOKUP s.eshapes eid, eval s e) of
            | (SOME sh, SOME v) =>
                if shape_of v = sh ∧ size_of_shape (shape_of v) ≤ 32 then
                  (SOME (Exception eid v), empty_locals s)
                else (SOME Error,s)
            | _ => (SOME Error,s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def, h_prog_raise_def]
QED

Theorem itree_semantics_Call:
 ((itree_semantics (Call calltyp fname aexps,s)):'a ptree) =
   (case OPT_MMAP (eval s) aexps of
      NONE => Ret (INR (SOME Error,s))
    | SOME args =>
        case lookup_code s.code fname args of
          NONE => Ret (INR (SOME Error,s))
        | SOME (q,r) =>
            Tau
            (((itree_semantics (q,s with locals := r)):'a ptree) >>=
                        (λres. itree_call_handler calltyp s res))
        | _ => Ret (INR (SOME Error,s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF, itree_call_handler_def] \\ BETA_TAC
  \\ fs[h_prog_def, h_prog_call_def]
  \\ rpt (CASE_TAC \\ fs[])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
  \\ EVERY_CASE_TAC \\ rw[h_handle_call_ret_def]
  \\ irule itree_bind_bisim_intro \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_DecCall:
  (itree_semantics (DecCall rt sh fname aexps prog,s)):'a ptree =
  (case OPT_MMAP (eval s) aexps of
     NONE => Ret (INR (SOME Error,s))
   | SOME args =>
       case lookup_code s.code fname args of
         NONE => Ret (INR (SOME Error,s))
       | SOME (q,r) =>
           Tau
           (((itree_semantics (q,s with locals := r)):'a ptree) >>=
                       (λres. itree_deccall_handler rt sh s res (λs1. itree_semantics (prog, s1)))))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF, itree_deccall_handler_def] \\ BETA_TAC
  \\ fs[h_prog_def, h_prog_deccall_def]
  \\ rpt (CASE_TAC \\ fs[])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
  \\ EVERY_CASE_TAC \\ rw[h_handle_deccall_ret_def, o_DEF]
  \\ irule itree_bind_bisim_intro \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_ExtCall:
  (itree_semantics (ExtCall ffiname cptr clen aptr alen, s)) =
  case (eval s cptr, eval s clen, eval s aptr, eval s alen) of
    (SOME (ValWord c3), SOME (ValWord c2), SOME (ValWord c'), SOME (ValWord c)) =>
      (case read_bytearray c3 (w2n c2) (mem_load_byte s.memory s.memaddrs s.be) of
         SOME x' =>
           (case read_bytearray c' (w2n c) (mem_load_byte s.memory s.memaddrs s.be) of
              SOME x =>
                if explode ffiname ≠ ""
                then
                   Vis (ExtCall (explode ffiname),x',x)
                       (λres.
                          Tau (Ret
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
                                 | INR _ => (SOME Error,s)))))
                else Ret (INR (NONE, s with memory := write_bytearray c' x s.memory s.memaddrs s.be))
            | _ => Ret (INR (SOME Error,s)))
       | _ => Ret (INR (SOME Error,s)))
  | _ => Ret (INR (SOME Error,s))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[h_prog_def,h_prog_ext_call_def]
  \\ rpt (PURE_CASE_TAC \\ fs[])
  \\ rw[FUN_EQ_THM]
QED

Definition vesp_valword_def:
  (vesp_valword (s:('a, 'b) state) (Var Local v) = [∃lw. FLOOKUP s.locals v = SOME (ValWord lw)]) ∧
  (vesp_valword s (Var Global v) = [∃lw. FLOOKUP s.globals v = SOME (ValWord lw)]) ∧
  (vesp_valword s _ = [])
End

Definition vesp_mem_load_def:
  (vesp_mem_load (sh:shape) (addr:'a word) (dm:'a word -> bool) (m:'a word -> 'a word_lab) =
   case sh of
     One => [addr ∈ dm]
   | Comb shapes => vesp_mem_loads shapes addr dm m) ∧
  (vesp_mem_loads [] (addr:'a word) (dm:'a word -> bool) (m:'a word -> 'a word_lab) = []) ∧
  (vesp_mem_loads (shape::shapes) addr dm m =
   (vesp_mem_load shape addr dm m) ++ (vesp_mem_loads shapes (addr + bytes_in_word * n2w (size_of_shape shape)) dm m))
Termination
  wf_rel_tac ‘measure (\x. case ISR x of
                            | T => list_size shape_size (FST (OUTR x))
                            | F => shape_size (FST (OUTL x)))’
  \\ rw []
End

Theorem vesp_mem_load_some:
  (∀s (addr:'a word) dm m. EVERY (λx. x) (vesp_mem_load s addr dm m) ⇒ ∃x. mem_load s addr dm m = SOME x) ∧
  (∀l (addr:'a word) dm m. EVERY (λx. x) (vesp_mem_loads l addr dm m) ⇒ ∃x'. mem_loads l addr dm m = SOME x')
Proof
  ho_match_mp_tac shape_induction
  \\ rpt strip_tac
  >- fs[mem_load_def, vesp_mem_load_def]
  >- (fs[mem_load_def, vesp_mem_load_def]
      \\ first_x_assum $ qspecl_then [‘addr’, ‘dm’, ‘m’] assume_tac
      \\ rfs[]
     )
  >- fs[mem_load_def, vesp_mem_load_def]
  \\ fs[mem_load_def, vesp_mem_load_def]
  \\ first_x_assum $ qspecl_then [‘(addr + bytes_in_word * n2w (size_of_shape s))’, ‘dm’, ‘m’] assume_tac
  \\ rfs[]
  \\ Cases_on ‘s’ \\ gvs[]
  \\ first_x_assum $ qspecl_then [‘addr’, ‘dm’, ‘m’] assume_tac
  \\ gvs[]
QED

Theorem vesp_mem_load_some_val_struct:
  (∀s (addr:'a word) dm m. EVERY (λx. x) (vesp_mem_load One addr dm m) ⇒ ∃x. mem_load One addr dm m = SOME (ValWord x)) ∧
  (∀ls (addr:'a word) dm m. EVERY (λx. x) (vesp_mem_load (Comb ls) addr dm m) ⇒ ∃x'. mem_load (Comb ls) addr dm m = SOME (Struct x'))
Proof
  rpt strip_tac
  >- (drule $ cj 1 vesp_mem_load_some
      \\ rpt strip_tac
      \\ gvs[mem_load_def, vesp_mem_load_def]
      \\ Cases_on ‘m addr’ \\ gvs[]
     )
  \\ gvs[mem_load_def, vesp_mem_load_def]
  \\ drule $ cj 2 vesp_mem_load_some
  \\ rpt strip_tac
  \\ rw[]
QED

Theorem mem_load_some_impl_vesp:
  (∀s (addr:'a word) dm m x. mem_load s addr dm m = SOME x ⇒ EVERY (λx. x) (vesp_mem_load s addr dm m)) ∧
  (∀l (addr:'a word) dm m vs. mem_loads l addr dm m = SOME vs ⇒ EVERY (λx. x) (vesp_mem_loads l addr dm m))
Proof
  ho_match_mp_tac shape_induction
  \\ rpt strip_tac
  >- fs[mem_load_def, vesp_mem_load_def]
  >- (fs[mem_load_def, vesp_mem_load_def]
      \\ FULL_CASE_TAC \\ gvs[]
     )
  >- fs[mem_load_def, vesp_mem_load_def]
  \\ fs[mem_load_def, vesp_mem_load_def]
  \\ rpt FULL_CASE_TAC \\ gvs[]
QED

Definition vesp_mem_load_32_def:
  (vesp_mem_load_32 (m:'a word -> 'a word_lab) (dm:'a word -> bool) (be:bool) (w:'a word) =
   [aligned 2 w; ∃v. m (byte_align w) = Word v; byte_align w ∈ dm])
End

Theorem vesp_mem_load_32_some:
  EVERY (λx. x) (vesp_mem_load_32 m dm be w) ⇒ ∃x. mem_load_32 m dm be w = SOME x
Proof
  rpt strip_tac
  \\ gvs[mem_load_32_def, vesp_mem_load_32_def]
QED

Theorem mem_load_32_some_vesp:
  mem_load_32 m dm be w = SOME x ⇒ EVERY (λx. x) (vesp_mem_load_32 m dm be w)
Proof
  rpt strip_tac
  \\ gvs[mem_load_32_def, vesp_mem_load_32_def]
  \\ rpt FULL_CASE_TAC \\ gvs[]
QED

Definition vesp_mem_load_byte_def:
  (vesp_mem_load_byte (m:'a word -> 'a word_lab) (dm:'a word -> bool) (be:bool) (w:'a word) =
   [∃v. m (byte_align w) = Word v; byte_align w ∈ dm])
End

Theorem vesp_mem_load_byte_some:
  EVERY (λx. x) (vesp_mem_load_byte m dm be w) ⇒ ∃x. mem_load_byte m dm be w = SOME x
Proof
  rpt strip_tac
  \\ gvs[mem_load_byte_def, vesp_mem_load_byte_def]
QED

Theorem mem_load_byte_some_vesp:
  mem_load_byte m dm be w = SOME x ⇒ EVERY (λx. x) (vesp_mem_load_byte m dm be w)
Proof
  rpt strip_tac
  \\ gvs[mem_load_byte_def, vesp_mem_load_byte_def]
  \\ rpt FULL_CASE_TAC \\ gvs[]
QED

Definition vesp_word_sh_def:
  vesp_word_sh (sh:shift) (w:'a word) (n:num) = [n = 0 ∨ n < dimindex (:α)]
End

Theorem vesp_word_sh_some:
  EVERY (λx. x) (vesp_word_sh sh w n) ⇒ ∃x. word_sh sh w n = SOME x
Proof
  rpt strip_tac
  \\ gvs[wordLangTheory.word_sh_def, vesp_word_sh_def]
  \\ FULL_CASE_TAC \\ gvs[]
QED

Theorem word_sh_some_vesp:
  word_sh sh w n = SOME x ⇒ EVERY (λx. x) (vesp_word_sh sh w n)
Proof
  rpt strip_tac
  \\ gvs[wordLangTheory.word_sh_def, vesp_word_sh_def]
  \\ FULL_CASE_TAC \\ gvs[]
QED

Definition vesp_word_op_def:
  (vesp_word_op Add (ws:'a word list) = []) ∧
  (vesp_word_op And (ws:'a word list) = []) ∧
  (vesp_word_op Or (ws:'a word list) = []) ∧
  (vesp_word_op Xor (ws:'a word list) = []) ∧
  (vesp_word_op Sub (ws:'a word list) = [∃w1 w2. ws = [w1;w2]])
End

Theorem vesp_word_op_some:
  EVERY (λx. x) (vesp_word_op op ws) ⇒ ∃x. word_op op ws = SOME x
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs[wordLangTheory.word_op_def, vesp_word_op_def]
QED

Theorem word_op_some_vesp:
  word_op op ws = SOME x ⇒ EVERY (λx. x) (vesp_word_op op ws)
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs[wordLangTheory.word_op_def, vesp_word_op_def]
  \\ rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
  \\ rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
  \\ rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
QED

Theorem vesp_word_op_non_sub_tail:
  EVERY (λx. x) (vesp_word_op op (h::ws)) ∧ op ≠ Sub ⇒  EVERY (λx. x) (vesp_word_op op ws)
Proof
  Induct_on ‘ws’ \\ rw[]
  >- (Cases_on ‘op’
      \\ gvs[vesp_word_op_def]
     )
  \\ Cases_on ‘op’
  \\ gvs[vesp_word_op_def]
QED

Theorem vesp_word_op_non_sub_cons:
  EVERY (λx. x) (vesp_word_op op ws) ∧ op ≠ Sub ⇒ EVERY (λx. x) (vesp_word_op op (h::ws))
Proof
  Induct_on ‘ws’ \\ rw[]
  >- (Cases_on ‘op’
      \\ gvs[vesp_word_op_def]
     )
  \\ Cases_on ‘op’
  \\ gvs[vesp_word_op_def]
QED

Definition vesp_pan_op_def:
  (vesp_pan_op Mul (ws:'a word list) = [∃w1 w2. ws = [w1; w2]])
End

Theorem vesp_pan_op_some:
  EVERY (λx. x) (vesp_pan_op op ws) ⇒ ∃x. pan_op op ws = SOME x
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs[pan_op_def, vesp_pan_op_def]
QED

Theorem pan_op_some_vesp:
  pan_op op ws = SOME x ⇒ EVERY (λx. x) (vesp_pan_op op ws)
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs[pan_op_def, vesp_pan_op_def]
  \\ Cases_on ‘ws’ \\ gvs[pan_op_def]
  \\ Cases_on ‘t’ \\ gvs[pan_op_def]
  \\ Cases_on ‘t'’ \\ gvs[pan_op_def]
QED

(* valid-expression state-precondition: the preconditions of a state that make an exp valid *)
Datatype:
  vesp_type =
  EqValWord
  | EqStruct
  | General
End

Definition vesp_def:
  (vesp s (Const _) EqValWord = []) ∧
  (vesp s (Const _) EqStruct = [F]) ∧
  (vesp s (Const _) General = []) ∧
  (vesp s (Var Local v) EqValWord = [∃lw. FLOOKUP s.locals v = SOME (ValWord lw)]) ∧
  (vesp s (Var Local v) EqStruct = [∃ls. FLOOKUP s.locals v = SOME (Struct ls)]) ∧
  (vesp s (Var Local v) General = [∃vv. FLOOKUP s.locals v = SOME vv]) ∧
  (vesp s (Var Global v) EqValWord = [∃gw. FLOOKUP s.globals v = SOME (ValWord gw)]) ∧
  (vesp s (Var Global v) EqStruct = [∃gs. FLOOKUP s.globals v = SOME (Struct gs)]) ∧
  (vesp s (Var Global v) General = [∃vv. FLOOKUP s.globals v = SOME vv]) ∧
  (vesp s (Struct es) EqValWord = [F]) ∧
  (vesp s (Struct es) EqStruct = FLAT (MAP (λx. vesp s x General) es)) ∧
  (vesp s (Struct es) General = FLAT (MAP (λx. vesp s x General) es)) ∧
  (vesp s (Field index e) EqValWord = [∃st_v est. EL index est = ValWord st_v ∧ eval s e = SOME (Struct est) ∧ index < LENGTH est]
                                         ++ (vesp s e EqStruct)) ∧
  (vesp s (Field index e) EqStruct = [∃st_v est. EL index est = Struct st_v ∧ eval s e = SOME (Struct est) ∧ index < LENGTH est]
                                         ++ (vesp s e EqStruct)) ∧
  (vesp s (Field index e) General = [∃est. eval s e = SOME (Struct est) ∧ index < LENGTH est]
                                     ++ (vesp s e EqStruct)) ∧
  (vesp s (Load shape addr) EqValWord = [shape = One; ∃wv addr_v. s.memory addr_v = Word wv ∧ eval s addr = SOME (ValWord addr_v) ∧
                                                                   EVERY (λx. x) (vesp_mem_load shape addr_v s.memaddrs s.memory)]
                                         ++ (vesp s addr EqValWord)) ∧
  (vesp s (Load shape addr) EqStruct =  [∃ls. shape = Comb ls ∧
                                               if ls = [] then T else
                                                 ∃addr_v. eval s addr = SOME (ValWord addr_v) ∧
                                                          EVERY (λx. x) (vesp_mem_load shape addr_v s.memaddrs s.memory)]
                                         ++ (vesp s addr EqValWord)) ∧
  (vesp s (Load shape addr) General =  [if shape = Comb [] then T else
                                           ∃addr_v. eval s addr = SOME (ValWord addr_v) ∧
                                                    EVERY (λx. x) (vesp_mem_load shape addr_v s.memaddrs s.memory)]
                                        ++ (vesp s addr EqValWord)) ∧
  (vesp s (Load32 addr) EqValWord = [∃addr_v. eval s addr = SOME (ValWord addr_v) ∧
                                               EVERY (λx. x) (vesp_mem_load_32 s.memory s.memaddrs s.be addr_v)]
                                     ++ (vesp s addr EqValWord)) ∧
  (vesp s (Load32 addr) EqStruct = [F]) ∧
  (vesp s (Load32 addr) General = [∃addr_v. eval s addr = SOME (ValWord addr_v) ∧
                                             EVERY (λx. x) (vesp_mem_load_32 s.memory s.memaddrs s.be addr_v)]
                                     ++ (vesp s addr EqValWord)) ∧
  (vesp s (LoadByte addr) EqValWord = [∃addr_v. eval s addr = SOME (ValWord addr_v) ∧
                                             EVERY (λx. x) (vesp_mem_load_byte s.memory s.memaddrs s.be addr_v)]
                                     ++ (vesp s addr EqValWord)) ∧
  (vesp s (LoadByte addr) EqStruct = [F]) ∧
  (vesp s (LoadByte addr) General = [∃addr_v. eval s addr = SOME (ValWord addr_v) ∧
                                             EVERY (λx. x) (vesp_mem_load_byte s.memory s.memaddrs s.be addr_v)]
                                     ++ (vesp s addr EqValWord)) ∧
  (vesp s (Op op es) EqValWord =  [∃vs. OPT_MMAP (λa. eval s a) es = SOME vs ∧
                                        EVERY (λx. x) (vesp_word_op op (MAP (λw. case w of ValWord n => n | Struct v1 => ARB) vs))]
                                   ++ (FLAT (MAP (λx. vesp s x EqValWord) es))) ∧
  (vesp s (Op op es) EqStruct =  [F]) ∧
  (vesp s (Op op es) General =  [∃vs. OPT_MMAP (λa. eval s a) es = SOME vs ∧
                                        EVERY (λx. x) (vesp_word_op op (MAP (λw. case w of ValWord n => n | Struct v1 => ARB) vs))]
                                   ++ (FLAT (MAP (λx. vesp s x EqValWord) es))) ∧
  (vesp s (Panop op es) EqValWord = [∃vs. OPT_MMAP (λa. eval s a) es = SOME vs ∧
                                        EVERY (λx. x) (vesp_pan_op op (MAP (λw. case w of ValWord n => n | Struct v1 => ARB) vs))]
                                       ++ (FLAT (MAP (λx. vesp s x EqValWord) es))) ∧
  (vesp s (Panop op es) EqStruct =  [F]) ∧
  (vesp s (Panop op es) General =  [∃vs. OPT_MMAP (λa. eval s a) es = SOME vs ∧
                                        EVERY (λx. x) (vesp_pan_op op (MAP (λw. case w of ValWord n => n | Struct v1 => ARB) vs))]
                                       ++ (FLAT (MAP (λx. vesp s x EqValWord) es))) ∧
  (vesp s (Cmp cmp e1 e2) EqValWord =  vesp s e1 EqValWord ++ vesp s e2 EqValWord) ∧
  (vesp s (Cmp cmp e1 e2) EqStruct =  [F]) ∧
  (vesp s (Cmp cmp e1 e2) General =  vesp s e1 EqValWord ++ vesp s e2 EqValWord) ∧
  (vesp s (Shift sh e n) EqValWord = [∃ev. eval s e = SOME (ValWord ev) ∧
                                      EVERY (λx. x) (vesp_word_sh sh ev n)]
                                      ++ vesp s e EqValWord) ∧
  (vesp s (Shift sh e n) EqStruct = [F]) ∧
  (vesp s (Shift sh e n) General = [∃ev. eval s e = SOME (ValWord ev) ∧
                                      EVERY (λx. x) (vesp_word_sh sh ev n)]
                                    ++ vesp s e EqValWord) ∧
  (vesp s BaseAddr EqValWord = []) ∧
  (vesp s BaseAddr EqStruct = [F]) ∧
  (vesp s BaseAddr General = []) ∧
  (vesp s TopAddr EqValWord = []) ∧
  (vesp s TopAddr EqStruct = [F]) ∧
  (vesp s TopAddr General = []) ∧
  (vesp s BytesInWord EqValWord = []) ∧
  (vesp s BytesInWord EqStruct = [F]) ∧
  (vesp s BytesInWord General = [])
End

Theorem vesp_valid_exp:
  ∀s exp. (EVERY (λx. x) (vesp s exp General) ⇒ ∃v. eval s exp = SOME v) ∧
          (EVERY (λx. x) (vesp s exp EqValWord) ⇒ ∃vw. eval s exp = SOME (ValWord vw)) ∧
          (EVERY (λx. x) (vesp s exp EqStruct) ⇒ ∃vs. eval s exp = SOME (Struct vs))
Proof
  ho_match_mp_tac eval_ind
  \\ rpt strip_tac
  >>~- ([‘vesp _ (Struct _)’],
        Induct_on ‘es’
        >- rw[eval_def, vesp_def]
        \\ rpt strip_tac \\ fs[]
        \\ gvs[eval_def, vesp_def]
        \\ first_x_assum $ qspec_then ‘h’ assume_tac
        \\ rfs[]
        \\ Cases_on ‘OPT_MMAP (λa. eval s a) es’ \\ gvs[]
       )
  >>~ [‘vesp _ (Load _ _)’]
  >- (gvs[eval_def, vesp_def]
      >- rw[mem_load_def]
      \\ drule $ cj 1 vesp_mem_load_some
      \\ metis_tac[]
     )
  >- gvs[eval_def, vesp_def, mem_load_def, vesp_mem_load_def]
  >- (gvs[eval_def, vesp_def]
      >- rw[mem_load_def]
      \\ drule $ cj 2 vesp_mem_load_some_val_struct
      \\ metis_tac[]
     )
  >>~- ([‘vesp _ (Load32 _)’],
        gvs[eval_def, vesp_def]
        \\ drule vesp_mem_load_32_some
        \\ rpt strip_tac
        \\ rw[]
       )
  >>~- ([‘vesp _ (LoadByte _)’],
        gvs[eval_def, vesp_def]
        \\ drule vesp_mem_load_byte_some
        \\ rpt strip_tac
        \\ rw[]
       )
  >>~ [‘vesp _ (Op _ _)’]
  >- (Induct_on ‘es’
      >- (rw[eval_def, vesp_def]
          \\ drule vesp_word_op_some
          \\ rw[]
         )
      \\ rpt strip_tac \\ gvs[eval_def, vesp_def]
      \\ Cases_on ‘op’
      >~ [‘Sub’]
      >- (Cases_on ‘t’ \\ gvs[vesp_word_op_def]
          \\ Cases_on ‘es’ \\ gvs[]
          \\ Cases_on ‘t’ \\ gvs[]
          \\ first_assum $ qspec_then ‘h’ assume_tac
          \\ first_x_assum $ qspec_then ‘h'''’ assume_tac
          \\ gvs[wordLangTheory.word_op_def]
         )
      \\ first_x_assum $ qspec_then ‘h’ assume_tac \\ gvs[]
      \\ drule vesp_word_op_non_sub_tail
      \\ rpt strip_tac
      \\ gvs[wordLangTheory.word_op_def]
  )
  >- (Induct_on ‘es’
      >- (rw[eval_def, vesp_def]
          \\ drule vesp_word_op_some
          \\ rw[]
         )
      \\ rpt strip_tac \\ gvs[eval_def, vesp_def]
      \\ Cases_on ‘op’
      >~ [‘Sub’]
      >- (Cases_on ‘t’ \\ gvs[vesp_word_op_def]
          \\ Cases_on ‘es’ \\ gvs[]
          \\ Cases_on ‘t’ \\ gvs[]
          \\ first_assum $ qspec_then ‘h’ assume_tac
          \\ first_x_assum $ qspec_then ‘h'''’ assume_tac
          \\ gvs[wordLangTheory.word_op_def]
         )
      \\ first_x_assum $ qspec_then ‘h’ assume_tac \\ gvs[]
      \\ drule vesp_word_op_non_sub_tail
      \\ rpt strip_tac
      \\ gvs[wordLangTheory.word_op_def]
     )
  >- gvs[eval_def, vesp_def]
  >>~ [‘vesp _ (Panop _ _)’]
  >- (Cases_on ‘op’
      \\ Cases_on ‘es’ \\ gvs[vesp_def, vesp_pan_op_def]
      \\ Cases_on ‘t’ \\ gvs[vesp_def, vesp_pan_op_def]
      \\ Cases_on ‘t'’ \\ gvs[vesp_def, vesp_pan_op_def]
      \\ first_assum $ qspec_then ‘h’ assume_tac
      \\ first_x_assum $ qspec_then ‘h''’ assume_tac
      \\ gvs[eval_def, pan_op_def]
     )
  >- (Cases_on ‘op’
      \\ Cases_on ‘es’ \\ gvs[vesp_def, vesp_pan_op_def]
      \\ Cases_on ‘t’ \\ gvs[vesp_def, vesp_pan_op_def]
      \\ Cases_on ‘t'’ \\ gvs[vesp_def, vesp_pan_op_def]
      \\ first_assum $ qspec_then ‘h’ assume_tac
      \\ first_x_assum $ qspec_then ‘h''’ assume_tac
      \\ gvs[eval_def, pan_op_def]
     )
  >- gvs[eval_def, vesp_def]
  >>~- ([‘vesp _ (Shift _ _ _)’],
       gvs[eval_def, vesp_def]
       \\ drule vesp_word_sh_some
       \\ metis_tac[]
      )
  \\ gvs[eval_def, vesp_def]
QED

Theorem eval_struct_compose:
  eval s h = SOME v ∧ eval s (Struct es) = SOME (Struct vs) ⇔ eval s (Struct (h::es)) = SOME (Struct (v::vs))
Proof
  iff_tac
  >- (rpt strip_tac
      \\ gvs[eval_def]
      \\ FULL_CASE_TAC \\ gvs[]
     )
  \\ rpt strip_tac
  \\ gvs[eval_def]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem valid_exp_vesp:
  ∀s exp v vw vs. ((∃v. eval s exp = SOME v) ⇒ EVERY (λx. x) (vesp s exp General)) ∧
                  ((∃vw. eval s exp = SOME (ValWord vw)) ⇒ EVERY (λx. x) (vesp s exp EqValWord)) ∧
                  ((∃vs. eval s exp = SOME (Struct vs)) ⇒ EVERY (λx. x) (vesp s exp EqStruct))
Proof
  ho_match_mp_tac eval_ind
  \\ rpt strip_tac
  >>~ [‘vesp _ (Struct _)’]
  >- (pop_assum $ mp_tac
      \\ qid_spec_tac ‘v’
      \\ Induct_on ‘es’
      >- rw[eval_def, vesp_def]
      \\ rpt strip_tac \\ fs[]
      \\ Cases_on ‘eval s h’
      >- gvs[eval_def]
      \\ Cases_on ‘eval s (Struct es)’
      >- (gvs[eval_def]
          \\ Cases_on ‘OPT_MMAP (λa. eval s a) es’ \\ gvs[]
         )
      \\ Cases_on ‘x'’
      >- (gvs[eval_def]
          \\ rpt FULL_CASE_TAC \\ gvs[]
         )
      \\ assume_tac $ GEN_ALL $ iffLR eval_struct_compose
      \\ pop_assum $ qspecl_then [‘l’, ‘x’, ‘s’, ‘h’, ‘es’] assume_tac
      \\ gvs[]
      \\ gvs[eval_def, vesp_def]
      \\ rpt FULL_CASE_TAC \\ gvs[]
     )
  >- (gvs[eval_def, vesp_def]
      \\ FULL_CASE_TAC \\ gvs[]
     )
  >- (pop_assum $ mp_tac
      \\ qid_spec_tac ‘vs’
      \\ Induct_on ‘es’
      >- rw[eval_def, vesp_def]
      \\ rpt strip_tac \\ fs[]
      \\ Cases_on ‘eval s h’
      >- gvs[eval_def]
      \\ Cases_on ‘eval s (Struct es)’
      >- (gvs[eval_def]
          \\ Cases_on ‘OPT_MMAP (λa. eval s a) es’ \\ gvs[]
         )
      \\ Cases_on ‘x'’
      >- (gvs[eval_def]
          \\ rpt FULL_CASE_TAC \\ gvs[]
         )
      \\ assume_tac $ GEN_ALL $ iffLR eval_struct_compose
      \\ pop_assum $ qspecl_then [‘l’, ‘x’, ‘s’, ‘h’, ‘es’] assume_tac
      \\ gvs[]
      \\ gvs[eval_def, vesp_def]
     )
  >>~- ([‘vesp _ (Field _ _)’],
        gvs[eval_def, vesp_def]
        \\ Cases_on ‘eval s exp’ \\ gvs[]
        \\ Cases_on ‘x’ \\ gvs[]
       )
  >>~ [‘vesp _ (Load _ _)’]
  >- (gvs[eval_def, vesp_def]
      \\ Cases_on ‘eval s exp’ \\ gvs[]
      \\ Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘w’ \\ gvs[]
      \\ drule $ cj 1 mem_load_some_impl_vesp
      \\ metis_tac[]
     )
  >- (gvs[eval_def, vesp_def]
      \\ Cases_on ‘eval s exp’ \\ gvs[]
      \\ Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘w’ \\ gvs[]
      \\ drule $ cj 1 mem_load_some_impl_vesp
      \\ fs[]
      \\ strip_tac
      \\ Cases_on ‘shape’ \\ gvs[mem_load_def]
      \\ rpt FULL_CASE_TAC \\ gvs[]
     )
  >- (gvs[eval_def, vesp_def]
      \\ Cases_on ‘eval s exp’ \\ gvs[]
      \\ Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘w’ \\ gvs[]
      \\ drule $ cj 1 mem_load_some_impl_vesp
      \\ fs[]
      \\ strip_tac
      \\ Cases_on ‘shape’ \\ gvs[mem_load_def]
     )
  >>~- ([‘vesp _ (Load32 _)’],
        gvs[eval_def, vesp_def]
        \\ Cases_on ‘eval s exp’ \\ gvs[]
        \\ Cases_on ‘x’ \\ gvs[]
        \\ Cases_on ‘w’ \\ gvs[]
        \\ Cases_on ‘mem_load_32 s.memory s.memaddrs s.be c’ \\ gvs[]
        \\ drule mem_load_32_some_vesp
        \\ rw[]
       )
  >>~- ([‘vesp _ (LoadByte _)’],
        gvs[eval_def, vesp_def]
        \\ Cases_on ‘eval s exp’ \\ gvs[]
        \\ Cases_on ‘x’ \\ gvs[]
        \\ Cases_on ‘w’ \\ gvs[]
        \\ Cases_on ‘mem_load_byte s.memory s.memaddrs s.be c’ \\ gvs[]
        \\ drule mem_load_byte_some_vesp
        \\ rw[]
       )
  >>~ [‘vesp _ (Op _ _)’]
  >- (pop_assum $ mp_tac
      \\ qid_spec_tac ‘v’
      \\ Induct_on ‘es’
      >- (rw[eval_def, vesp_def]
          \\ drule word_op_some_vesp
          \\ rw[]
         )
      \\ rpt strip_tac
      \\ Cases_on ‘op’
      >~ [‘Sub’]
      >- (Cases_on ‘es’ \\ gvs[eval_def]
          >- (rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
             )
          \\ reverse $ Cases_on ‘t’ \\ gvs[]
          >- (rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
             )
          \\ rpt FULL_CASE_TAC \\ gvs[]
          \\ rpt FULL_CASE_TAC \\ gvs[]
          \\ rpt FULL_CASE_TAC \\ gvs[]
          \\ drule word_op_some_vesp
          \\ gvs[vesp_def]
         )
      \\ gvs[eval_def, vesp_def]
      \\ rpt FULL_CASE_TAC \\ gvs[]
      \\ rpt FULL_CASE_TAC \\ gvs[]
      \\ gvs[wordLangTheory.word_op_def]
      \\ drule vesp_word_op_non_sub_cons
      \\ rw[]
  )
  >- (pop_assum $ mp_tac
      \\ qid_spec_tac ‘vw’
      \\ Induct_on ‘es’
       >- (rw[eval_def, vesp_def]
          \\ drule word_op_some_vesp
          \\ rw[]
         )
      \\ rpt strip_tac
      \\ Cases_on ‘op’
      >~ [‘Sub’]
      >- (Cases_on ‘es’ \\ gvs[eval_def]
          >- (rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
             )
          \\ reverse $ Cases_on ‘t’ \\ gvs[]
          >- (rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
             )
          \\ rpt FULL_CASE_TAC \\ gvs[]
          \\ rpt FULL_CASE_TAC \\ gvs[]
          \\ rpt FULL_CASE_TAC \\ gvs[]
          \\ drule word_op_some_vesp
          \\ gvs[vesp_def]
         )
      \\ gvs[eval_def, vesp_def]
      \\ rpt FULL_CASE_TAC \\ gvs[]
      \\ rpt FULL_CASE_TAC \\ gvs[]
      \\ gvs[wordLangTheory.word_op_def]
      \\ drule vesp_word_op_non_sub_cons
      \\ rw[]
     )
  >- (gvs[eval_def, vesp_def]
      \\ rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
     )
  >>~- ([‘vesp _ (Panop _ _)’],
        Cases_on ‘op’
        \\ Cases_on ‘es’ \\ gvs[vesp_def, vesp_pan_op_def, eval_def, pan_op_def]
        \\ rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
        \\ Cases_on ‘t'’ \\ gvs[vesp_def, vesp_pan_op_def, pan_op_def]
        \\ Cases_on ‘t''’ \\ gvs[vesp_def, vesp_pan_op_def, pan_op_def]
        \\ rpt FULL_CASE_TAC \\ gvs[wordLangTheory.word_op_def]
        \\ Cases_on ‘t’ \\ gvs[OPT_MMAP_def]
        \\ Cases_on ‘t'’ \\ gvs[OPT_MMAP_def]
        \\ first_assum $ qspec_then ‘h’ assume_tac
        \\ first_x_assum $ qspec_then ‘h'’ assume_tac
        \\ gvs[eval_def, pan_op_def]
        \\ Cases_on ‘w’ \\ gvs[]
        \\ Cases_on ‘w'’ \\ gvs[]
       )
  >>~- ([‘vesp _ (Cmp _ _ _)’],
        gvs[eval_def, vesp_def]
        \\ rpt FULL_CASE_TAC \\ gvs[]
        \\ rpt FULL_CASE_TAC \\ gvs[]
        \\ rpt FULL_CASE_TAC \\ gvs[]
       )
  >>~- ([‘vesp _ (Shift _ _ _)’],
        gvs[eval_def, vesp_def]
        \\ rpt FULL_CASE_TAC \\ gvs[]
        \\ rpt FULL_CASE_TAC \\ gvs[]
        \\ rpt FULL_CASE_TAC \\ gvs[]
        \\ drule word_sh_some_vesp
        \\ metis_tac[]
      )
  \\ gvs[eval_def, vesp_def]
QED

(* expression is valid iff every assumption in vesp is T *)
Theorem valid_exp_iff_vesp:
  ∀s exp v vw vs. ((∃v. eval s exp = SOME v) ⇔ EVERY (λx. x) (vesp s exp General)) ∧
                  ((∃vw. eval s exp = SOME (ValWord vw)) ⇔ EVERY (λx. x) (vesp s exp EqValWord)) ∧
                  ((∃vs. eval s exp = SOME (Struct vs)) ⇔ EVERY (λx. x) (vesp s exp EqStruct))
Proof
  metis_tac[vesp_valid_exp, valid_exp_vesp]
QED
