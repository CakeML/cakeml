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

val res = “res:(ffi_outcome + word8 list) + 'a result option # 'a bstate”

val ret_func = “Ret:(ffi_outcome + word8 list) + 'a result option # 'a bstate -> 'a ptree”

Definition itree_semantics_def:
  itree_semantics:('a panLang$prog # 'a bstate -> 'a ptree) = mrec h_prog o h_prog
End
        
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

Definition word_of_val_def:
  word_of_val (ValWord w) = w ∧
  word_of_val _ = ARB
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

Theorem itree_semantics_While_with_pre:
  (∃w. eval s e = SOME (ValWord w)) ⇒
  ((itree_semantics (While e p,s)):'a ptree) =
  let valword_w = THE (eval s e) in
      if valword_w = ValWord 0w then Ret (INR (NONE, s))
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
Proof
  rpt strip_tac
  \\ PURE_REWRITE_TAC[itree_semantics_def, o_DEF]
  \\ fs[SimpLHS, h_prog_def, h_prog_while_def, Once itree_iter_thm]
  \\ gvs[word_of_val_def]
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

Theorem itree_semantics_Dec_with_pre:
  (∃v. eval s e = SOME v) ⇒
  ((itree_semantics (Dec x sh e p, s)):'a ptree) =
  let v = THE (eval s e) in
      Tau (((itree_semantics (p,s with locals := s.locals |+ (x,v))):'a ptree) >>=
           (λa. Ret (INR (case a of
                            INL l => (SOME Error, s)
                          | INR (res,s') =>
                              (res, s' with
                     locals := res_var s'.locals (x,FLOOKUP s.locals x))))))
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

(*
Theorem itree_semantics_Assign_with_pre_bu:
  (∃v. eval s e = SOME v ∧ is_valid_value s vk x v) ⇒
  ((itree_semantics (Assign vk x e, s)):'a ptree) =
  let v = THE (eval s e) in
      Ret (INR ((NONE, set_kvar vk x v s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_assign_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ rw[]
QED

*)
        
Theorem itree_semantics_Assign_with_pre:
  (∃v. eval s e = SOME v) ⇒
  (let v = THE (eval s e) in is_valid_value s vk x v) ⇒
  itree_semantics (Assign vk x e,s) =
  (let v = THE (eval s e) in Ret (INR (NONE,set_kvar vk x v s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_assign_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[])
  \\ rw[]
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

Theorem itree_semantics_If_with_pre:
  (∃vw. eval s e = SOME (ValWord vw)) ⇒
  ((itree_semantics (If e p q, s)):'a ptree) =
  let valword_v = THE (eval s e) in
    if valword_v ≠ ValWord 0w then
      Tau (((itree_semantics (p,s)):'a ptree)
           >>= (λa. Ret (INR (case a of
                                INL l => (SOME Error,s)
                              | INR (res,s') => (res,s')))))
    else
      Tau (((itree_semantics (q,s)):'a ptree)
           >>= (λa. Ret (INR (case a of
                                INL l => (SOME Error,s)
                              | INR (res,s') => (res,s')))))
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

(*
Theorem itree_semantics_Store_with_pre_bu:
  (∃ad v m. eval s dst = SOME (ValWord ad) ∧
            eval s src = SOME v ∧
            mem_stores ad (flatten v) s.memaddrs s.memory = SOME m) ⇒
  ((itree_semantics (Store dst src, s)):'a ptree) =
  let ad = word_of_val (THE (eval s dst)) in
    let v = THE (eval s src) in
      let m = THE (mem_stores ad (flatten v) s.memaddrs s.memory) in
        Ret (INR (NONE, s with memory := m))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[word_of_val_def])
QED
*)

Theorem itree_semantics_Store_with_pre:
  (∃ad. eval s dst = SOME (ValWord ad)) ⇒
  (∃v. eval s src = SOME v) ⇒
  (let
     ad = word_of_val (THE (eval s dst));
     v = THE (eval s src)
   in
     ∃m. mem_stores ad (flatten v) s.memaddrs s.memory = SOME m) ⇒
  itree_semantics (Store dst src,s) =
  (let
     ad = word_of_val (THE (eval s dst));
     v = THE (eval s src);
     m = THE (mem_stores ad (flatten v) s.memaddrs s.memory)
   in
     Ret (INR (NONE,s with memory := m)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[word_of_val_def])
QED

Theorem itree_semantics_StoreByte:
  itree_semantics (StoreByte dst src,s) =
  Ret
    (INR
       (case (eval s dst,eval s src) of
          (NONE,v3) => (SOME Error,s)
        | (SOME (Val v10),NONE) => (SOME Error,s)
        | (SOME (ValWord ad),SOME (ValWord v)) =>
          (case mem_store_byte s.memory s.memaddrs s.be ad (w2w v) of
             NONE => (SOME Error,s)
           | SOME m => (NONE,s with memory := m))
        | (SOME (Val v10),SOME (Struct v19)) => (SOME Error,s)
        | (SOME (Struct v11),v3) => (SOME Error,s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_byte_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[word_of_val_def])
QED

Theorem itree_semantics_StoreByte_with_pre:
  (∃ad. eval s dst = SOME (ValWord ad)) ⇒
     (∃v. eval s src = SOME (ValWord v)) ⇒
     (let
        ad = word_of_val (THE (eval s dst));
        v = word_of_val (THE (eval s src))
      in
        ∃m. mem_store_byte s.memory s.memaddrs s.be ad (w2w v) = SOME m) ⇒
     itree_semantics (StoreByte dst src,s) =
     (let
        ad = word_of_val (THE (eval s dst));
        v = word_of_val (THE (eval s src));
        m = THE (mem_store_byte s.memory s.memaddrs s.be ad (w2w v))
      in
        Ret (INR (NONE,s with memory := m)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_byte_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[word_of_val_def])
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


Theorem itree_semantics_Store32_with_pre:
  (∃ad. eval s dst = SOME (ValWord ad)) ⇒
  (∃v. eval s src = SOME (ValWord v)) ⇒
  (let
     ad = word_of_val (THE (eval s dst));
     v = word_of_val (THE (eval s src))
   in
     ∃m. mem_store_32 s.memory s.memaddrs s.be ad (w2w v) = SOME m) ⇒
  itree_semantics (Store32 dst src,s) =
  (let
     ad = word_of_val (THE (eval s dst));
     v = word_of_val (THE (eval s src));
     m = THE (mem_store_32 s.memory s.memaddrs s.be ad (w2w v))
   in
     Ret (INR (NONE,s with memory := m)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_store_32_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[word_of_val_def])
QED

        
Theorem itree_semantics_ShMemLoad_with_pre:
  (∃ad. eval s addr = SOME (ValWord ad)) ⇒
  (∃vl. lookup_kvar vk v s = SOME (Val vl)) ⇒
  (let ad = word_of_val (THE (eval s addr)) in
     if nb_op op = 0 then ad ∈ s.sh_memaddrs else byte_align ad ∈ s.sh_memaddrs) ⇒
  ((itree_semantics (ShMemLoad op vk v addr, s)):'a ptree) =
  let ad = word_of_val (THE (eval s addr)) in
    Vis (SharedMem MappedRead,[n2w (nb_op op)],word_to_bytes ad F)
      (λres.
           Tau
             (Ret
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
                    | INR v2 => (SOME Error,s)))))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_sh_mem_load_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[word_of_val_def])
  \\ rw[FUN_EQ_THM]
QED
        
Theorem itree_semantics_ShMemLoad:
  ((itree_semantics (ShMemLoad op vk v addr, s)):'a ptree) =  case (eval s addr, lookup_kvar vk v s) of
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

Theorem itree_semantics_ShMemStore_with_pre:
  (∃ad. eval s addr = SOME (ValWord ad)) ⇒
  (∃w. eval s e = SOME (ValWord w)) ⇒
  (let ad = word_of_val (THE (eval s addr)) in
     if nb_op op = 0 then ad ∈ s.sh_memaddrs else byte_align ad ∈ s.sh_memaddrs) ⇒
  ((itree_semantics (ShMemStore op addr e, s)):'a ptree) =
  let ad = word_of_val (THE (eval s addr)) in
    let w = word_of_val (THE (eval s e)) in
      if nb_op op = 0 then
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
      else
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
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[SimpLHS, h_prog_def, h_prog_sh_mem_store_def, Once itree_iter_thm]
  \\ rpt (CASE_TAC \\ fs[TAKE_def, word_of_val_def])
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

(*
Theorem itree_semantics_Return_with_pre_bu:
  (∃v. eval s e = SOME v ∧ size_of_shape (shape_of v) ≤ 32) ⇒
  itree_semantics (Return e,s) =
  let v = THE (eval s e) in
    Ret (INR ((SOME (Return v), empty_locals s)))
Proof
  rw[]
  \\ PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def, h_prog_return_def]
QED
*)
        
Theorem itree_semantics_Return_with_pre:
  (∃v. eval s e = SOME v) ⇒
  (let
     v = THE (eval s e)
   in
     size_of_shape (shape_of v) ≤ 32) ⇒
  itree_semantics (Return e,s) =
  let v = THE (eval s e) in
    Ret (INR ((SOME (Return v), empty_locals s)))
Proof
  rw[]
  \\ PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ gvs[h_prog_def, h_prog_return_def]
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

(*
Theorem itree_semantics_Raise_with_pre_bu:
  (∃sh v. FLOOKUP s.eshapes eid = SOME sh ∧
          eval s e = SOME v ∧ shape_of v = sh ∧
          size_of_shape (shape_of v) ≤ 32) ⇒
  itree_semantics (Raise eid e,s) =
  let sh = THE (FLOOKUP s.eshapes eid) in
    let v = THE (eval s e) in        
      Ret (INR ((SOME (Exception eid v), empty_locals s)))
Proof
  rw[]
  \\ PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def, h_prog_raise_def]
QED
*)

Theorem itree_semantics_Raise_with_pre:
  (∃sh. FLOOKUP s.eshapes eid = SOME sh) ⇒
  (∃v. eval s e = SOME v) ⇒
  (let
     sh = THE (FLOOKUP s.eshapes eid);
     v = THE (eval s e)
   in
     shape_of v = sh ∧ size_of_shape (shape_of v) ≤ 32) ⇒
  itree_semantics (Raise eid e,s) =
  let sh = THE (FLOOKUP s.eshapes eid) in
    let v = THE (eval s e) in        
      Ret (INR ((SOME (Exception eid v), empty_locals s)))
Proof
  rw[]
  \\ PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ gvs[h_prog_def, h_prog_raise_def]
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

        
Theorem itree_semantics_Call_with_pre:
  (∃args q r. OPT_MMAP (eval s) aexps = SOME args ∧ lookup_code s.code fname args = SOME (q,r)) ⇒
  ((itree_semantics (Call calltyp fname aexps,s)):'a ptree) =
  let args = THE (OPT_MMAP (eval s) aexps) in
    let (q, r) = THE (lookup_code s.code fname args) in
      Tau (((itree_semantics (q,s with locals := r)):'a ptree)
           >>= (λres. itree_call_handler calltyp s res))
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

Theorem itree_semantics_DecCall_with_pre:
  (∃args q r. OPT_MMAP (eval s) aexps = SOME args ∧ lookup_code s.code fname args = SOME (q,r)) ⇒
  (itree_semantics (DecCall rt sh fname aexps prog,s)):'a ptree =
  let args = THE (OPT_MMAP (eval s) aexps) in
    let (q, r) = THE (lookup_code s.code fname args) in
      Tau (((itree_semantics (q,s with locals := r)):'a ptree)
           >>= (λres. itree_deccall_handler rt sh s res (λs1. itree_semantics (prog, s1))))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF, itree_deccall_handler_def] \\ BETA_TAC
  \\ fs[h_prog_def, h_prog_deccall_def]
  \\ rpt (CASE_TAC \\ fs[])
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
  \\ EVERY_CASE_TAC \\ rw[h_handle_deccall_ret_def, o_DEF]
  \\ irule itree_bind_bisim_intro \\ rw[FUN_EQ_THM]
QED

Theorem itree_semantics_ExtCall_with_pre:
  (∃c3 c2 x'.
        eval s cptr = SOME (ValWord c3) ∧ eval s clen = SOME (ValWord c2) ∧
        read_bytearray c3 (w2n c2) (mem_load_byte s.memory s.memaddrs s.be) =
        SOME x') ⇒
     (∃c' c x.
        eval s aptr = SOME (ValWord c') ∧ eval s alen = SOME (ValWord c) ∧
        read_bytearray c' (w2n c) (mem_load_byte s.memory s.memaddrs s.be) =
        SOME x) ⇒
     itree_semantics (ExtCall ffiname cptr clen aptr alen,s) =
     (let
        c3 = word_of_val (THE (eval s cptr));
        c2 = word_of_val (THE (eval s clen));
        c' = word_of_val (THE (eval s aptr));
        c = word_of_val (THE (eval s alen));
        mb = (mem_load_byte s.memory s.memaddrs s.be);
        x' = THE (read_bytearray c3 (w2n c2) mb);
        x = THE (read_bytearray c' (w2n c) mb)
      in
        if explode ffiname ≠ "" then
          Vis (ExtCall (explode ffiname),x',x)
            (λres.
                 Tau
                   (Ret
                      (INR
                         (case res of
                            INL (INL outcome) =>
                              (SOME
                                 (FinalFFI
                                    (Final_event (ExtCall (explode ffiname))
                                       x' x outcome)),empty_locals s)
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
                                    (Final_event (ExtCall (explode ffiname))
                                       x' x FFI_failed)),empty_locals s)
                          | INR v1 => (SOME Error,s)))))
        else
          Ret
            (INR
               (NONE,
                s with
                memory := write_bytearray c' x s.memory s.memaddrs s.be)))
Proof
  rw[]
  \\ PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[h_prog_def,h_prog_ext_call_def]
  \\ rpt (PURE_CASE_TAC \\ fs[word_of_val_def])
  \\ rw[FUN_EQ_THM, word_of_val_def]
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

(*
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

(* well-formed rules*)
Definition is_valid_value_wfp_def:
  (is_valid_value_wfp s Local v value = [∃w. FLOOKUP s.locals v = SOME w ∧ shape_of value = shape_of w]) ∧
  (is_valid_value_wfp s Global v value = [∃w. FLOOKUP s.globals v = SOME w ∧ shape_of value = shape_of w])
End

Theorem is_valid_value_wfp_T:
  EVERY (λx. x) (is_valid_value_wfp s k v value) ⇔ is_valid_value s k v value = T
Proof
  Cases_on ‘k’
  \\ rw[is_valid_value_wfp_def, is_valid_value_defs, lookup_kvar_defs]
  \\ FULL_CASE_TAC \\ gvs[]
QED

Definition lookup_kvar_wfp_def:
  (lookup_kvar_wfp Local v s = [∃x. FLOOKUP s.locals v = SOME x]) ∧
  (lookup_kvar_wfp Global v s = [∃x. FLOOKUP s.globals v = SOME x])
End

Theorem lookup_kvar_wfp_some:
  EVERY (λx. x) (lookup_kvar_wfp vk v s) ⇒ ∃x. lookup_kvar vk v s = SOME x
Proof
  Cases_on ‘vk’ \\ rw[lookup_kvar_wfp_def, lookup_kvar_defs]
QED

Definition lookup_kvar_valword_wfp_def:
  (lookup_kvar_valword_wfp Local v s = [∃x. FLOOKUP s.locals v = SOME (ValWord x)]) ∧
  (lookup_kvar_valword_wfp Global v s = [∃x. FLOOKUP s.globals v = SOME (ValWord x)])
End

Theorem lookup_kvar_valword_wfp_some:
  EVERY (λx. x) (lookup_kvar_valword_wfp vk v s) ⇒ ∃x. lookup_kvar vk v s = SOME (ValWord x)
Proof
  Cases_on ‘vk’ \\ rw[lookup_kvar_valword_wfp_def, lookup_kvar_def]
QED

Definition mem_stores_wfp_def:
  (mem_stores_wfp a [] dm m = []) ∧
  (mem_stores_wfp a (w::ws) dm m = (a ∈ dm)::(mem_stores_wfp (a + bytes_in_word) ws dm m⦇a ↦ w⦈))
End

Theorem mem_stores_wfp_some:
  EVERY (λx. x) (mem_stores_wfp a ws dm m) ⇒ ∃x. mem_stores a ws dm m = SOME x
Proof
  qid_spec_tac ‘m’
  \\ qid_spec_tac ‘a’
  \\ Induct_on ‘ws’ \\ rw[mem_store_def, mem_stores_def, mem_stores_wfp_def]
QED

Definition mem_store_32_wfp_def:
  mem_store_32_wfp m dm be w hw = [aligned 2 w; ∃v. m (byte_align w) = Word v; byte_align w ∈ dm]
End

Theorem mem_store_32_wfp_some:
  EVERY (λx. x) (mem_store_32_wfp m dm be w hw) ⇒ ∃x. mem_store_32 m dm be w hw = SOME x
Proof
  fs[mem_store_32_wfp_def, mem_store_32_def]
  \\ rpt FULL_CASE_TAC \\ fs[]
QED

Definition mem_store_byte_wfp_def:
  mem_store_byte_wfp m dm be w hw = [∃v. m (byte_align w) = Word v; byte_align w ∈ dm]
End

Theorem mem_store_byte_wfp_some:
  EVERY (λx. x) (mem_store_byte_wfp m dm be w hw) ⇒ ∃x. mem_store_byte m dm be w hw = SOME x
Proof
  fs[mem_store_byte_wfp_def, mem_store_byte_def]
  \\ rpt FULL_CASE_TAC \\ fs[]
QED

(* non-error one (level) program state pre-condition *)
Definition pswfp_def:
  (pswfp (Assign k vname e) s = (∃v. eval s e = SOME v ∧ EVERY (λx. x) (is_valid_value_wfp s k vname v))
                                                 ::(vesp s e General)) ∧
  (pswfp (Call calltyp fname argexps) s = (∃args vshapes prog. OPT_MMAP (eval s) argexps = SOME args ∧
                                                               FLOOKUP s.code fname = SOME (vshapes,prog) ∧
                                                               ALL_DISTINCT (MAP FST vshapes) ∧
                                                               LIST_REL (λvshape arg. SND vshape = shape_of arg) vshapes args)
                                          ::(FLAT (MAP (λx. vesp s x General) argexps))) ∧
  (pswfp (If gexp p1 p2) s = vesp s gexp EqValWord) ∧
  (pswfp (Dec vname sh e p) s = vesp s e General
                                ++ [∃value. eval s e = SOME value ∧
                                            EVERY (λx. x) (pswfp p (s with locals := s.locals |+ (vname,value)))]) ∧
  (pswfp (DecCall rt shape fname argexps prog1) s = (∃args vshapes prog. OPT_MMAP (eval s) argexps = SOME args ∧
                                                                         FLOOKUP s.code fname = SOME (vshapes,prog) ∧
                                                                         ALL_DISTINCT (MAP FST vshapes) ∧
                                                                         LIST_REL (λvshape arg. SND vshape = shape_of arg) vshapes args)
                                                    ::(FLAT (MAP (λx. vesp s x General) argexps))) ∧
  (pswfp (ExtCall ffi_name conf_ptr conf_len array_ptr array_len) s =
   (FLAT (MAP (λx. vesp s x EqValWord) [conf_ptr; conf_len; array_ptr; array_len]))) ∧
  (pswfp (Raise eid e) s = (∃sh val. FLOOKUP s.eshapes eid = SOME sh ∧ eval s e = SOME val ∧
                                     shape_of val = sh ∧ size_of_shape (shape_of val) ≤ 32)::(vesp s e General)) ∧
  (pswfp (Return e) s = (∃val. eval s e = SOME val ∧ size_of_shape (shape_of val) ≤ 32)::(vesp s e General)) ∧
  (pswfp (ShMemLoad op vk v ad) s = vesp s ad EqValWord ++ lookup_kvar_valword_wfp vk v s
                                    ++ [∃addr. eval s ad = SOME (ValWord addr) ∧
                                               if nb_op op = 0
                                               then addr ∈ s.sh_memaddrs
                                               else byte_align addr ∈ s.sh_memaddrs]) ∧
  (pswfp (ShMemStore op ad e) s = vesp s ad EqValWord ++ vesp s e EqValWord
                                    ++ [∃addr. eval s ad = SOME (ValWord addr) ∧
                                               if nb_op op = 0
                                               then addr ∈ s.sh_memaddrs
                                               else byte_align addr ∈ s.sh_memaddrs]) ∧
  (pswfp (Store dst src) s = vesp s dst EqValWord ++ vesp s src General
                             ++ [∃addr val. eval s dst = SOME (ValWord addr) ∧ eval s src = SOME val ∧
                                            EVERY (λx. x) (mem_stores_wfp addr (flatten val) s.memaddrs s.memory)]) ∧
  (pswfp (Store32 dst src) s = vesp s dst EqValWord ++ vesp s src EqValWord
                               ++ [∃addr w. eval s dst = SOME (ValWord addr) ∧ eval s src = SOME (ValWord w) ∧
                                            EVERY (λx. x) (mem_store_32_wfp s.memory s.memaddrs s.be addr ((w2w w):32 word))]) ∧
  (pswfp (StoreByte dst src) s = vesp s dst EqValWord ++ vesp s src EqValWord
                                 ++ [∃addr w. eval s dst = SOME (ValWord addr) ∧ eval s src = SOME (ValWord w) ∧
                                              EVERY (λx. x) (mem_store_byte_wfp s.memory s.memaddrs s.be addr ((w2w w):8 word))]) ∧
  (pswfp (While gexp p) s = vesp s gexp EqValWord) ∧
  (pswfp _ _ = [])
End

Theorem ret_wbisim_ret_iff_sbisim:
  Ret x ≈ Ret y ⇔ Ret x = Ret y
Proof
  iff_tac
  >- (rpt strip_tac
      \\ dxrule_then assume_tac itree_wbisim_Ret_FUNPOW
      \\ fs[]
     )
  \\ rw[itree_wbisim_refl]
QED

Theorem flat_map_vesp_opt_mmap_eval_some:
  (∃x. OPT_MMAP (eval s) argexps = SOME x) ⇔
  EVERY (λx. x) (FLAT (MAP (λx. vesp s x General) argexps))
Proof
  Induct_on ‘argexps’ \\ fs[]
  \\ rpt strip_tac
  \\ iff_tac
  >- (rpt strip_tac
      \\ metis_tac[valid_exp_iff_vesp]
     )
  \\ rpt strip_tac
  \\ metis_tac[valid_exp_iff_vesp]
QED

Theorem pswfp_iff_assign_non_error:
  EVERY (λx. x) (pswfp (Assign k vname e) s) ⇔ ∀s'. ¬(itree_semantics (Assign k vname e, s) ≈ Ret (INR (SOME Error, s')))
Proof
  iff_tac
  >- (rpt strip_tac
      \\ gvs[itree_semantics_Assign, pswfp_def, is_valid_value_wfp_def,
             is_valid_value_wfp_T]
      \\ dxrule_then assume_tac $ iffLR ret_wbisim_ret_iff_sbisim
      \\ fs[]
     )
  \\ rpt strip_tac
  \\ gvs[itree_semantics_Assign, pswfp_def, is_valid_value_wfp_def,
         is_valid_value_wfp_T]
  \\ EVERY_CASE_TAC \\ fs[]
  >- (pop_assum $ qspec_then ‘s’ assume_tac
      \\ fs[ret_wbisim_ret_iff_sbisim]
     )
  >- metis_tac[valid_exp_iff_vesp]
  \\ first_x_assum $ qspec_then ‘s’ assume_tac
  \\ fs[ret_wbisim_ret_iff_sbisim]
QED

Theorem call_non_error_pswfp:
  (∀s'. ¬(itree_semantics (Call calltyp fname argexps, s) ≈ Ret (INR (SOME Error, s')))) ⇒
  EVERY (λx. x) (pswfp (Call calltyp fname argexps) s)
Proof
  rpt strip_tac
  \\ gvs[itree_semantics_Call, pswfp_def, lookup_code_def]
  \\ EVERY_CASE_TAC \\ fs[]
  >- metis_tac[itree_wbisim_refl]
  >- metis_tac[itree_wbisim_refl]
  >- metis_tac[itree_wbisim_refl]
  >- metis_tac[flat_map_vesp_opt_mmap_eval_some]
  \\ metis_tac[itree_wbisim_refl]
QED

Theorem pswfp_inner_non_error_call_non_error:
  EVERY (λx. x) (pswfp (Call calltyp fname argexps) s) ⇒
  (∃args callee_prog new_locals.
     OPT_MMAP (eval s) argexps = SOME args ∧
     lookup_code s.code fname args = SOME (callee_prog, new_locals) ∧
     (∀s'. ¬(itree_semantics (callee_prog,s with locals := new_locals) >>=
                             (λres. itree_call_handler calltyp s res) ≈ ^ret_func (INR (SOME Error, s'))))
     ⇒ (∀s'. ¬(itree_semantics (Call calltyp fname argexps, s) ≈ Ret (INR (SOME Error, s'))))
  )
Proof
  rpt strip_tac
  \\ fs[pswfp_def, lookup_code_def]
  \\ qexistsl [‘args’, ‘prog’, ‘FEMPTY |++ ZIP (MAP FST vshapes,args) ’] \\ simp[]
  \\ rpt strip_tac
  \\ pop_assum $ assume_tac o SRULE [Once itree_semantics_Call]
  \\ rfs[lookup_code_def]
QED
*)

CoInductive ret_satisfy:
  (P v ⇒ ret_satisfy P (Ret v)) ∧
  (ret_satisfy P t ⇒ ret_satisfy P (Tau t)) ∧
  ((∀r. ret_satisfy P (k r)) ⇒ ret_satisfy P (Vis e k))
End

Theorem ret_satisfy_bind:
  ret_satisfy P t ∧ (∀r. ret_satisfy P (k r)) ⇒ ret_satisfy P (t >>= k)
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘λt. ret_satisfy P t ∨
                  (∃t' k. t = t' >>= k ∧ ret_satisfy P t' ∧
                          ∀r. ret_satisfy P (k r))’
  \\ rpt conj_tac
  >- metis_tac[]
  \\ rpt strip_tac
  \\ Cases_on ‘a0’ \\ fs[]
  >- (pop_assum $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ simp[]
     )
  >- (Cases_on ‘t'’ \\ fs[]
      \\ qpat_x_assum ‘Ret _ = _’ $ assume_tac o GSYM
      \\ first_x_assum $ qspec_then ‘x'’ assume_tac
      \\ pop_assum $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ gvs[]
     )
  >- (pop_assum $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ simp[]
     )
  >- (Cases_on ‘t'’ \\ fs[]
      >- (qpat_x_assum ‘Tau _ = _’ $ assume_tac o GSYM
          \\ first_x_assum $ qspec_then ‘x’ assume_tac
          \\ pop_assum $ assume_tac o SRULE [Once ret_satisfy_cases]
          \\ gvs[]
         )
      \\ qpat_x_assum ‘ret_satisfy _ (Tau _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ metis_tac[]
     )
  >- (pop_assum $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ simp[]
     )
  \\ Cases_on ‘t'’ \\ fs[]
  >- (qpat_x_assum ‘Vis _ _ = _’ $ assume_tac o GSYM
      \\ first_x_assum $ qspec_then ‘x’ assume_tac
      \\ pop_assum $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ gvs[]
     )
  \\ qpat_x_assum ‘ret_satisfy _ (Vis _ _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
  \\ metis_tac[]
QED

Theorem ret_satisfy_prog_eq:
  (∀r. P r ⇒ k r = k' r ) ⇒
  ret_satisfy P t ⇒
  t >>= k = t >>= k'
Proof
  rpt strip_tac
  \\ irule $ iffRL itree_strong_bisimulation
  \\ qexists ‘CURRY ({(t, t) | t | T } ∪ {(t >>= k, t >>= k') | t, k, k' | ret_satisfy P t ∧ (∀r. P r ⇒ k r = k' r ) })’
  \\ rw[]
  >- metis_tac[]
  >- (Cases_on ‘t''’ \\ gvs[]
      \\ qpat_x_assum ‘ret_satisfy _ (Ret _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ rw[]
     )
  >- (Cases_on ‘t''’ \\ gvs[]
      >- (qpat_x_assum ‘Tau _ = _’ $ assume_tac o GSYM
          \\ qpat_x_assum ‘ret_satisfy _ (Ret _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
          \\ first_x_assum $ qspec_then ‘x’ assume_tac
          \\ gvs[]
         )
      \\ qpat_x_assum ‘ret_satisfy _ (Tau _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ metis_tac[]
     )
  \\ Cases_on ‘t''’ \\ fs[]
  >- (qpat_x_assum ‘Vis _ _ = _’ $ assume_tac o GSYM
      \\ qpat_x_assum ‘ret_satisfy _ (Ret _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
      \\ first_x_assum $ qspec_then ‘x’ assume_tac
      \\ gvs[]
     )
  \\ qpat_x_assum ‘ret_satisfy _ (Vis _ _)’ $ assume_tac o SRULE [Once ret_satisfy_cases]
  \\ metis_tac[]
QED

Theorem ret_satisfy_strengthen:
  (∀r. P r ⇒ Q r) ⇒ ret_satisfy P t ⇒ ret_satisfy Q t
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘ret_satisfy P’
  \\ rpt conj_tac
  >- pop_assum $ irule
  \\ rpt strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
  \\ fs[]
QED

Theorem ret_satisfy_F_spin:
  ret_satisfy (λr. F) spin
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘λx. x = spin’
  \\ rpt conj_tac
  >- simp[]
  \\ rpt strip_tac
  \\ fs[spin]
QED

CoInductive event_satisfy:
  (event_satisfy P (Ret v)) ∧
  (event_satisfy P t ⇒ event_satisfy P (Tau t)) ∧
  (P e ∧ (∀r. event_satisfy P (k r)) ⇒ event_satisfy P (Vis e k))
End

Theorem event_satisfy_bind:
  event_satisfy P t ∧ (∀r. event_satisfy P (k r)) ⇒ event_satisfy P (t >>= k)
Proof
  rpt strip_tac
  \\ irule event_satisfy_coind
  \\ qexists ‘λt. event_satisfy P t ∨
                  (∃t' k. t = t' >>= k ∧ event_satisfy P t' ∧
                          ∀r. event_satisfy P (k r))’
  \\ rpt conj_tac
  >- metis_tac[]
  \\ rpt strip_tac
  \\ Cases_on ‘a0’ \\ fs[]
  >- (pop_assum $ assume_tac o SRULE [Once event_satisfy_cases]
      \\ simp[]
     )
  >- (Cases_on ‘t'’ \\ fs[]
      >- (qpat_x_assum ‘Tau _ = _’ $ assume_tac o GSYM
          \\ first_x_assum $ qspec_then ‘x’ assume_tac
          \\ pop_assum $ assume_tac o SRULE [Once event_satisfy_cases]
          \\ gvs[]
         )
      \\ qpat_x_assum ‘event_satisfy _ (Tau _)’ $ assume_tac o SRULE [Once event_satisfy_cases]
      \\ metis_tac[]
     )
  >- (pop_assum $ assume_tac o SRULE [Once event_satisfy_cases]
      \\ simp[]
     )
  \\ Cases_on ‘t'’ \\ fs[]
  >- (qpat_x_assum ‘Vis _ _ = _’ $ assume_tac o GSYM
      \\ first_x_assum $ qspec_then ‘x’ assume_tac
      \\ pop_assum $ assume_tac o SRULE [Once event_satisfy_cases]
      \\ gvs[]
     )
  \\ qpat_x_assum ‘event_satisfy _ (Vis _ _)’ $ assume_tac o SRULE [Once event_satisfy_cases]
  \\ metis_tac[]
QED


Theorem event_satisfy_strengthen:
  (∀r. P r ⇒ Q r) ⇒ event_satisfy P t ⇒ event_satisfy Q t
Proof
  rpt strip_tac
  \\ irule event_satisfy_coind
  \\ qexists ‘event_satisfy P’
  \\ rpt conj_tac
  >- pop_assum $ irule
  \\ rpt strip_tac
  \\ pop_assum $ assume_tac o SRULE[Once event_satisfy_cases]
  \\ fs[]
QED

Theorem event_satisfy_F_spin:
  event_satisfy (λr. F) spin
Proof
  rpt strip_tac
  \\ irule event_satisfy_coind
  \\ qexists ‘λx. x = spin’
  \\ rpt conj_tac
  >- simp[]
  \\ rpt strip_tac
  \\ fs[spin]
QED

Theorem event_satisfy_F_non_vis:
  t ≈ Ret v ⇒ event_satisfy (λr. F) t
Proof
  rpt strip_tac
  \\ irule event_satisfy_coind
  \\ qexists ‘λx. x ≈ Ret v’
  \\ rpt conj_tac
  >- simp[]
  \\ rpt strip_tac
  \\ fs[]
  \\ Cases_on ‘a0’ \\ fs[]
  \\ pop_assum $ assume_tac o SRULE[Once itree_wbisim_cases]
  \\ fs[]
QED

(* 
Theorem pswfp_inner_ret_non_error_call_ret_non_error:
  EVERY (λx. x) (pswfp (Call calltyp fname argexps) s) ⇒
  (∃args callee_prog new_locals.
     OPT_MMAP (eval s) argexps = SOME args ∧
     lookup_code s.code fname args = SOME (callee_prog, new_locals) ∧
     (ret_satisfy (λx. ¬∃s'. (x:(ffi_outcome + word8 list) + 'a result option # 'a bstate) = INR (SOME Error, s'))
                  (itree_semantics (callee_prog,s with locals := new_locals) >>=
                                   (λres. itree_call_handler calltyp s res)))
     ⇒ (ret_satisfy (λx. ¬∃s'. x = INR (SOME Error, s'))
                    (itree_semantics (Call calltyp fname argexps, s)))
  )
Proof
  rpt strip_tac
  \\ fs[pswfp_def, lookup_code_def]
  \\ qexistsl [‘args’, ‘prog’, ‘FEMPTY |++ ZIP (MAP FST vshapes,args) ’] \\ simp[]
  \\ rpt strip_tac
  \\ fs[Once itree_semantics_Call]
  \\ rfs[lookup_code_def, ret_satisfy_rules]
QED
*)


Definition struct_of_val_def:
  struct_of_val (ValWord w) = ARB ∧ struct_of_val (Struct v1) = v1
End

CoInductive ret_vis_satisfy:
  (P_r v ⇒ ret_vis_satisfy P_r P_v (Ret v)) ∧
  (ret_vis_satisfy P_r P_v t ⇒ ret_vis_satisfy P_r P_v (Tau t)) ∧
  ((∀r. P_v e r ∧ ret_vis_satisfy P_r P_v (k r)) ⇒ ret_vis_satisfy P_r P_v (Vis e k))
End

Theorem ret_vis_satisfy_Tau:
  ret_vis_satisfy P_r P_v (Tau u) ⇔ ret_vis_satisfy P_r P_v u
Proof
  iff_tac \\ fs[ret_vis_satisfy_rules]
  \\ rw[Once ret_vis_satisfy_cases]
QED

Theorem ret_vis_satisfy_Ret:
  ret_vis_satisfy P_r P_v (Ret v) ⇔ P_r v
Proof
  iff_tac \\ fs[ret_vis_satisfy_rules]
  \\ rw[Once ret_vis_satisfy_cases]
QED


Theorem ret_vis_satisfy_Vis:
  ret_vis_satisfy P_r P_v (Vis e k) ⇔ ∀r. P_v e r ∧ ret_vis_satisfy P_r P_v (k r)
Proof
  iff_tac \\ fs[ret_vis_satisfy_rules]
  \\ rw[Once ret_vis_satisfy_cases]
QED

CoInductive itree_wbisim_up_to_ev_res:
  (t ≈ t' ⇒ itree_wbisim_up_to_ev_res P t t') ∧
  ((∀r. P e r ⇒ itree_wbisim_up_to_ev_res P (k r) (k' r)) ⇒ itree_wbisim_up_to_ev_res P (Vis e k) (Vis e k'))
End
(*
Theorem itree_semantics_ShMemLoad_with_pre:
  (∀e r. P e r ⇔ ∃nb. r = INL (INR nb) ∧ LENGTH nb = dimindex (:α) DIV 8) ⇒
  (∃ad. eval s addr = SOME (ValWord ad)) ⇒
  (∃vl. lookup_kvar vk v s = SOME (Val vl)) ⇒
  (let
     ad = word_of_val (THE (eval s addr))
   in
     if nb_op op = 0 then ad ∈ s.sh_memaddrs
     else byte_align ad ∈ s.sh_memaddrs) ⇒
  itree_wbisim_up_to_ev_res P
  (itree_semantics (ShMemLoad op vk v addr,s):'a ptree)
  (let
     ad = word_of_val (THE (eval s addr))
   in
     Vis (SharedMem MappedRead,[n2w (nb_op op)],word_to_bytes ad F)
       (λres.
            Tau
              (Ret
                 (INR
                    (case res of
                       INL (INL outcome) => ARB
                     | INL (INR new_bytes) =>
                         (NONE,
                          set_kvar vk v
                            (ValWord (word_of_bytes F 0w new_bytes)) s)
                     | INR v2 => ARB)))))
Proof
  gvs[itree_semantics_ShMemLoad]
  \\ EVERY_CASE_TAC \\ gvs[]
  \\ rw[Once itree_wbisim_up_to_ev_res_cases, word_of_val_def]
  \\ disj2_tac
  \\ rw[Once itree_wbisim_up_to_ev_res_cases]
  \\ EVERY_CASE_TAC \\ gvs[itree_wbisim_refl]
QED
*)
        
Theorem ret_satisfy_Tau:
  ret_satisfy P (Tau u) ⇔ ret_satisfy P u
Proof
  iff_tac \\ fs[ret_satisfy_rules]
  \\ rw[Once ret_satisfy_cases]
QED

Theorem ret_satisfy_Ret:
  ret_satisfy P (Ret v) ⇔ P v
Proof
  iff_tac \\ fs[ret_satisfy_rules]
  \\ rw[Once ret_satisfy_cases]
QED


Theorem ret_satisfy_Vis:
  ret_satisfy P (Vis e k) ⇔ ∀r. ret_satisfy P (k r)
Proof
  iff_tac \\ fs[ret_satisfy_rules]
  \\ rw[Once ret_satisfy_cases]
QED

Theorem res_var_case:
  res_var lc (n, optv) =
  case optv of NONE => lc \\ n | SOME v => lc |+ (n, v)
Proof
  FULL_CASE_TAC \\ rw[res_var_def]
QED

Definition res_var_list_def:
  res_var_list lc [x] = res_var lc x ∧
  res_var_list lc (x::xs) = res_var_list (res_var lc x) xs
End

Theorem res_var_list_thm:
  res_var_list lc [(n,NONE)] = (lc \\ n) ∧
  res_var_list lc [(n,SOME v)] = (lc |+ (n, v)) ∧
  res_var_list lc ((n,NONE)::y::ys) = res_var_list (lc \\ n) (y::ys) ∧
  res_var_list lc ((n,SOME v)::y::ys) = res_var_list (lc |+ (n, v)) (y::ys)
Proof
  rw[res_var_list_def, res_var_def]
QED
                

Definition del_annot_def:
  del_annot (Seq (Annot _ _) (p : 'a panLang$prog)) = del_annot p ∧
  del_annot (Seq a b) = (Seq (del_annot a) (del_annot b)) ∧
  del_annot (Dec vname sh e p) = (Dec vname sh e (del_annot p)) ∧
  del_annot (DecCall rt shape fname argexps p) = (DecCall rt shape fname argexps (del_annot p)) ∧
  del_annot (If gexp p1 p2) = (If gexp (del_annot p1) (del_annot p2)) ∧
  del_annot (While gexp p) = (While gexp (del_annot p)) ∧
  del_annot (Annot _ _) = Skip ∧
  del_annot p = p
End

Theorem while_weak_bisim_upfrom_abs:
  (∀s. itree_semantics (p, s) ≈ itree_semantics (p', s))
  ⇒ ∀s. weak_bisim_upfrom_abs ((λs. itree_semantics (While g p, s)), (λs. itree_semantics (While g p', s)))
                                               (itree_semantics (While g p, s)) (itree_semantics (While g p', s))
Proof
  rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘weak_bisim_upfrom_abs (abs, abs') _ _’
  \\ PURE_ONCE_REWRITE_TAC[itree_semantics_While]
  \\ Cases_on ‘eval s g’ \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ reverse $ Cases_on ‘x’ \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ reverse $ Cases_on ‘w’ \\ gvs[]
  \\ FULL_CASE_TAC \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ last_x_assum $ qspec_then ‘s’ assume_tac
  \\ PURE_ONCE_REWRITE_TAC[GSYM itree_bind_thm]
  \\ irule weak_bisim_upfrom_abs_wbisim_bind
  \\ rw[]
  \\ Cases_on ‘r’ \\ gvs[]
  >- metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2]
  \\ Cases_on ‘y’ \\ gvs[]
  \\ Cases_on ‘q’ \\ gvs[]
  >- metis_tac[FUNPOW, weak_bisim_upfrom_abs_rules]
  \\ Cases_on ‘x’ \\ gvs[]
  \\ metis_tac[weak_bisim_upfrom_abs_rules, strip_tau_simps2, GSYM FUNPOW_SUC, GSYM FUNPOW]
QED
        
Theorem while_bisim:
  (∀s. itree_semantics (p, s) ≈ itree_semantics (p', s))
   ⇒ ∀s. itree_semantics (While g p, s) ≈ itree_semantics (While g p', s)
Proof
  disch_tac
  \\ ‘∀s. (λs. itree_semantics (While g p, s)) s ≈ (λs. itree_semantics (While g p', s)) s’ suffices_by metis_tac[]
  \\ irule $ iffLR cyclic_weak_bisim_upfrom_abs
  \\ rw[while_weak_bisim_upfrom_abs]
QED

Theorem panprog_induct:
  ∀P.
    P Skip ∧ (∀p. P p ⇒ ∀s e m. P (Dec m s e p)) ∧
    (∀v m e. P (Assign v m e)) ∧ (∀e e0. P (Store e e0)) ∧
    (∀e e0. P (Store32 e e0)) ∧
    (∀e e0. P (StoreByte e e0)) ∧ (∀p p0. P p ∧ P p0 ⇒ P (Seq p p0)) ∧
    (∀p p0. P p ∧ P p0 ⇒ ∀e. P (If e p p0)) ∧
    (∀p. P p ⇒ ∀e. P (While e p)) ∧ P Break ∧ P Continue ∧
    (∀$o l e. P (Call $o e l)) ∧
    (∀p. P p ⇒ ∀l e s m. P (DecCall m s e l p)) ∧
    (∀m e e0 e1 e2. P (ExtCall m e e0 e1 e2)) ∧ (∀m e. P (Raise m e)) ∧
    (∀e. P (Return e)) ∧ (∀$o v m e. P (ShMemLoad $o v m e)) ∧
    (∀$o e e0. P (ShMemStore $o e e0)) ∧ P Tick ∧
    (∀m m0. P (Annot m m0))
    ⇒ ∀p. P (p : 'a panLang$prog)
Proof
  strip_tac >>
  qspecl_then [‘P’,‘K T’,‘K T’,‘K T’,‘K T’,‘K T’]
              strip_assume_tac (cj 1 panLangTheory.prog_induction) >>
  rw[]
QED

Theorem itree_semantics_While_ret_satisfy_INR:
  (∀s. ret_satisfy (λx. ∃rv. x = INR rv) (itree_semantics (prog, s))) ⇒
  ret_satisfy (λx. ∃rv. x = INR rv) (itree_semantics (While e prog, s))
Proof
  rpt strip_tac
  \\ rw[Once itree_semantics_While]
  \\ EVERY_CASE_TAC \\ gvs[ret_satisfy_rules]
  \\ irule $ cj 2 ret_satisfy_rules
  \\ irule ret_satisfy_coind
  \\ qexists ‘λx. (∃t st. x = ((t:'a ptree) >>= (λa.
                                                   case a of
                                                     INL l => Ret (INR (SOME Error,st))
                                                   | INR (res,s') =>
                                                       case res of
                                                         NONE => Tau (itree_semantics (While e prog,s'))
                                                       | SOME Error => Ret (INR (res,s'))
                                                       | SOME TimeOut => Ret (INR (res,s'))
                                                       | SOME Break => Ret (INR (NONE,s'))
                                                       | SOME Continue =>
                                                           Tau (itree_semantics (While e prog,s'))
                                                       | SOME (Return v6) => Ret (INR (res,s'))
                                                       | SOME (Exception v7 v8) => Ret (INR (res,s'))
                                                       | SOME (FinalFFI v9) => Ret (INR (res,s'))))) ∨
                  (∃s'. x = (itree_semantics (While e prog,s')))’
  \\ rpt conj_tac
  >- metis_tac[]
  \\ rpt strip_tac
  \\ Cases_on ‘a0’ \\ rfs[]
  >- (pop_assum $ assume_tac o GSYM
      \\ drule itree_bind_ret_inv
      \\ rw[]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (pop_assum $ assume_tac o GSYM
      \\ fs[Once itree_semantics_While]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (Cases_on ‘t’ \\ gvs[]
      \\ EVERY_CASE_TAC \\ gvs[]
      \\ metis_tac[]
      \\ gvs[Once itree_semantics_While]
      \\ EVERY_CASE_TAC \\ gvs[]
     )
  >- (pop_assum $ assume_tac o SRULE[Once itree_semantics_While]
      \\ EVERY_CASE_TAC \\ gvs[]
      \\ metis_tac[]
     )
  >- (Cases_on ‘t’ \\ gvs[]
      >- (EVERY_CASE_TAC \\ gvs[]
          \\ metis_tac[]
         )
      \\ metis_tac[]
     )
  \\ gvs[Once itree_semantics_While]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem ret_satisfy_bind_k_wrap:
  (∀r. ret_satisfy P (k r)) ⇒ ret_satisfy P (t >>= k)
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘λx. (∃t. x = t >>= k) ∨ (ret_satisfy P x)’
  \\ rw[]
  >- metis_tac[]
  >- (Cases_on ‘t’ \\ fs[]
      >- (pop_assum $ qspec_then ‘x’ assume_tac
          \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
          \\ rfs[]
         )
      >- metis_tac[]
      \\ metis_tac[]
     )
  \\ Cases_on ‘a0’ \\ fs[]
  >- (pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ pop_assum $ irule
     )
  >- (pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ disj2_tac
      \\ pop_assum $ irule
     )
  \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
  \\ fs[]
QED

Theorem ret_satisfy_bind_unchanged:
  ret_satisfy (λx. k x = Ret x) t ⇒ (t >>= k) = t
Proof
  rpt strip_tac
  \\ irule $ iffRL itree_bisimulation
  \\ qexists ‘CURRY {t >>= k, t | t, k | ret_satisfy (λx. k x = Ret x) t}’
  \\ rw[]
  >- (qexists ‘(t, k)’
      \\ rw[]
     )
  >- (Cases_on ‘x'’ \\ gvs[]
      \\ Cases_on ‘q’ \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ simp[]
     )
  >- (Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘q’ \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ gvs[]
      \\ qexists ‘(u', r)’ \\ gvs[]
     )
  >- (Cases_on ‘x’ \\ gvs[]
      \\ Cases_on ‘q’ \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ gvs[]
      \\ rpt strip_tac
      \\ qexists ‘(g s, r)’ \\ gvs[]
     )
QED

Theorem ret_satisfy_INR_itree_semantics:
  ∀prog s. ret_satisfy (λx. ∃rv. x = INR rv) (itree_semantics (prog,s))
Proof
  ho_match_mp_tac panprog_induct
  \\ rw[ret_satisfy_rules, itree_semantics_Annot, itree_semantics_Tick, itree_semantics_Raise, itree_semantics_Return, itree_semantics_Skip,
        itree_semantics_StoreByte, itree_semantics_Store32, itree_semantics_Store, itree_semantics_Continue, itree_semantics_Break]
  >- (rw[itree_semantics_Dec]
      \\ FULL_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
     )
  >- (fs[itree_semantics_Assign]
      \\ FULL_CASE_TAC \\ fs[ret_satisfy_rules]
     )
  >- (fs[itree_semantics_Seq]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
     )
  >- (rw[itree_semantics_If]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
     )
  >- fs[itree_semantics_While_ret_satisfy_INR]
  >- (rw[itree_semantics_Call]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules, itree_call_handler_def]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r'’ \\ fs[ret_satisfy_rules]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r''’ \\ fs[ret_satisfy_rules]
     )
  >- (rw[itree_semantics_DecCall]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules, itree_deccall_handler_def]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r'’ \\ fs[ret_satisfy_rules]
      \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ irule $ cj 2 ret_satisfy_rules
      \\ irule ret_satisfy_bind_k_wrap
      \\ rpt strip_tac
      \\ Cases_on ‘r''’ \\ fs[ret_satisfy_rules]
     )
  \\ rw[itree_semantics_ExtCall, itree_semantics_ShMemStore, itree_semantics_ShMemLoad, itree_semantics_Return]
  \\ EVERY_CASE_TAC \\ fs[ret_satisfy_rules, itree_semantics_Return]
QED

Theorem itree_bisim_impl_wbisim:
  t = t' ⇒ t ≈ t'
Proof rw[itree_wbisim_refl]
QED

Theorem del_annot_preserve_semantics:
  ∀prog s. itree_semantics (prog, s) ≈ itree_semantics (del_annot prog, s)
Proof
  ho_match_mp_tac panprog_induct
  \\ fs[del_annot_def, while_bisim, itree_wbisim_refl]
  \\ rpt strip_tac
  >~ [‘Seq’]
  >- (Cases_on ‘prog’ \\ fs[del_annot_def]
      >~ [‘Seq (Annot _ _)’]
      >- (fs[del_annot_def, itree_semantics_Seq, itree_semantics_Annot]
          \\ irule itree_wbisim_trans
          \\ pop_assum $ irule_at Any
          \\ irule itree_bisim_impl_wbisim
          \\ irule ret_satisfy_bind_unchanged
          \\ irule ret_satisfy_strengthen
          \\ irule_at Any ret_satisfy_INR_itree_semantics
          \\ rw[]
          \\ FULL_CASE_TAC \\ fs[]
         )
      \\ fs[del_annot_def, itree_semantics_Seq, itree_semantics_Skip, itree_semantics_Annot]
      \\ irule itree_bind_resp_wbisim
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
      \\ rpt strip_tac
      \\ EVERY_CASE_TAC
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
      \\ irule itree_bind_resp_wbisim
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
  )
  >- (fs[itree_semantics_Dec]
      \\ FULL_CASE_TAC
      \\ fs[itree_wbisim_refl]
      \\ irule itree_bind_resp_t_wbisim
      \\ rw[]
     )
  >- (Cases_on ‘e’ \\ fs[itree_semantics_If]
      \\ EVERY_CASE_TAC \\ gvs[eval_def, itree_wbisim_refl]
      \\ irule itree_bind_resp_wbisim
      \\ fs[FUN_EQ_THM, itree_wbisim_refl]
     )
  >- (fs[itree_semantics_DecCall, itree_deccall_handler_def]
      \\ EVERY_CASE_TAC
      \\ fs[itree_wbisim_refl]
      \\ irule itree_bind_resp_k_wbisim
      \\ rpt strip_tac
      \\ Cases_on ‘r'’ \\ rw[]
      \\ EVERY_CASE_TAC \\ fs[itree_wbisim_refl]
      \\ irule itree_bind_resp_t_wbisim \\ fs[itree_wbisim_refl]
     )
  \\ fs[itree_semantics_Skip, itree_semantics_Annot, itree_wbisim_refl]
QED

Theorem shape_of_eq_one_valword:
  shape_of x = One ⇔ ∃vx. x = ValWord vx
Proof
  Cases_on ‘x’ \\ fs[shape_of_def]
  \\ Cases_on ‘w’ \\ fs[shape_of_def]
QED


Theorem state_update_locals_locals:
  (s with locals := a).locals = a ∧ (s with locals := a).locals = a
Proof
  EVAL_TAC
QED
        
Theorem empty_locals_with_locals:
  empty_locals s with locals := new_locals = s with locals := new_locals
Proof
  rw[empty_locals_defs]
  \\ irule $ iffRL bstate_component_equality
  \\ rw[]
QED

Theorem locals_emmpty_locals:
  (empty_locals s).locals = FEMPTY
Proof
  rw[empty_locals_defs]
QED

Theorem itree_bind_assoc_tuple:
  t >>= k >>= k' = t >>= (λ(x, y). k (x, y) >>= k')
Proof
  rw[Once itree_bind_assoc]
  \\ irule itree_bind_bisim_intro
  \\ rw[FUN_EQ_THM]
  \\ Cases_on ‘x’ \\ gvs[]
QED


Theorem itree_bind_option_case_assoc:
  option_CASE a (b:(α,β,γ) itree) c >>= d = option_CASE a (b >>= d) (λx. c x >>= d)
Proof
  FULL_CASE_TAC
QED

Theorem itree_bind_pair_case_assoc:
  pair_CASE a b >>= d = pair_CASE a (λx y. b x y >>= d)
Proof
  FULL_CASE_TAC
QED

Theorem itree_bind_v_case_assoc:
  v_CASE a b c >>= d = v_CASE a (λx. b x >>= d) (λx. c x >>= d)
Proof
  FULL_CASE_TAC
QED

Theorem itree_bind_sum_case_assoc:
  sum_CASE a b c >>= d = sum_CASE a (λx. b x >>= d) (λx. c x >>= d)
Proof
  FULL_CASE_TAC
QED

Theorem itree_bind_cond_assoc:
  COND bexp tc ec >>= d = COND bexp (tc >>= d) (ec >>= d)
Proof
  rw[]
QED

Theorem itree_bind_let_assoc:
  LET f v >>= d = LET (λx. f x >>= d) v
Proof
  rw[]
QED

Theorem tau_let_assoc:
  Tau (LET f v) = LET (λx. Tau (f x)) v
Proof
  rw[]
QED

Theorem upds_multi_locals:
  s with <|locals := a; locals := b|> = s with locals := a
Proof
  EVAL_TAC
QED

Theorem itree_bind_result_case_def:
  result_CASE rs v v1 v2 v3 f f1 f2 >>= k =
  result_CASE rs (v >>= k) (v1 >>= k) (v2 >>= k) (v3 >>= k) (λx. f x >>= k) (λx y. f1 x y >>= k) (λx. f2 x >>= k)
Proof FULL_CASE_TAC
QED
        
Theorem con_dif:
  ((if bexp then t else e) ≠ 0w) ⇔ (if bexp then (t ≠ 0w) else (e ≠ 0w))
Proof
  rw[]
QED

Theorem neq_1w_0w:
  1w ≠ 0w ∧ 0w ≠ 1w
Proof
  rw[]
QED

Theorem bool_case_rev_ID:
  (if x then F else T) = ¬x
Proof
  rw[]
QED

Theorem option_case_same:
  (case x of NONE => NONE | SOME a => SOME a) = option_CASE x NONE SOME
Proof
  EVERY_CASE_TAC \\ gvs[]
QED

Theorem upds_multi_memory:
  s with <|memory := a; memory := b|> = s with memory := a
Proof
  EVAL_TAC
QED

Theorem itree_bind_ffi_result_CASE_assoc:
  ffi_result_CASE res a b >>= d = case res of
                                    FFI_return new_ffi new_bytes => a new_ffi new_bytes >>= d
                                  | FFI_final outcome => b outcome >>= d
Proof
  Cases_on ‘res’ \\ fs[ffiTheory.ffi_result_case_def]
QED

        
Theorem pair_CASE_same:
  pair_CASE x (λres s'. (res,s')) = x
Proof
  Cases_on ‘x’ \\ gvs[]
QED

        
Theorem itree_semantics_Seq_ret_satisfy_pres:
  ((∀s. itree_semantics (p1, s) = t1 s) ⇒
  (∀s. itree_semantics (p2, s) = t2 s) ⇒
  (∀s. itree_semantics (Seq p1 p2, s) = Tau (t1 s >>= (λa.
                                                         case a of
                                                           INL l => Ret (INR (SOME Error,s))
                                                         | INR (NONE,s') =>
                                                             Tau
                                                             (t2 s' >>= (λa.
                                                                           Ret
                                                                           (INR
                                                                            (case a of
                                                                               INL v => (SOME Error,s)
                                                                             | INR (res,s') => (res,s')))))
                                                         | INR (SOME res,s') => Ret (INR (SOME res,s'))))))
  ∧
  ((∀s. itree_semantics (p1, s) = t1 s) ⇒
  (∀s. Pre2 s ⇒ itree_semantics (p2, s) = t2 s) ⇒
  (∀s. ret_satisfy (λx. ∃rv s'. x = INR (rv, s') ∧ (rv = NONE ⇒ Pre2 s')) (t1 s) ⇒
       itree_semantics (Seq p1 p2, s) = Tau (t1 s >>= (λa.
                                                         case a of
                                                           INL l => Ret (INR (SOME Error,s))
                                                         | INR (NONE,s') =>
                                                             Tau
                                                             (t2 s' >>= (λa.
                                                                           Ret
                                                                           (INR
                                                                            (case a of
                                                                               INL v => (SOME Error,s)
                                                                             | INR (res,s') => (res,s')))))
                                                         | INR (SOME res,s') => Ret (INR (SOME res,s'))))))
  ∧
  ((∀s. Pre1 s ⇒ itree_semantics (p1, s) = t1 s) ⇒
  (∀s. itree_semantics (p2, s) = t2 s) ⇒
  (∀s. Pre1 s ⇒
       itree_semantics (Seq p1 p2, s) = Tau (t1 s >>= (λa.
                                                         case a of
                                                           INL l => Ret (INR (SOME Error,s))
                                                         | INR (NONE,s') =>
                                                             Tau
                                                             (t2 s' >>= (λa.
                                                                           Ret
                                                                           (INR
                                                                            (case a of
                                                                               INL v => (SOME Error,s)
                                                                             | INR (res,s') => (res,s')))))
                                                         | INR (SOME res,s') => Ret (INR (SOME res,s'))))))
  ∧
  ((∀s. Pre1 s ⇒ itree_semantics (p1, s) = t1 s) ⇒
  (∀s. Pre2 s ⇒ itree_semantics (p2, s) = t2 s) ⇒
  (∀s. Pre1 s ⇒ ret_satisfy (λx. ∃rv s'. x = INR (rv, s') ∧ (rv = NONE ⇒ Pre2 s')) (t1 s) ⇒
       itree_semantics (Seq p1 p2, s) = Tau (t1 s >>= (λa.
                                                         case a of
                                                           INL l => Ret (INR (SOME Error,s))
                                                         | INR (NONE,s') =>
                                                             Tau
                                                             (t2 s' >>= (λa.
                                                                           Ret
                                                                           (INR
                                                                            (case a of
                                                                               INL v => (SOME Error,s)
                                                                             | INR (res,s') => (res,s')))))
                                                         | INR (SOME res,s') => Ret (INR (SOME res,s'))))))
Proof
  rpt conj_tac
  \\ rpt strip_tac
  \\ rw[itree_semantics_Seq]
  \\ irule ret_satisfy_prog_eq
  \\ pop_assum $ irule_at Any
  \\ rpt strip_tac
  \\ rw[FUN_EQ_THM]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

        
Theorem ret_satisfy_T:
  ret_satisfy (λx. T) t
Proof
  irule ret_satisfy_coind
  \\ qexists ‘λt. T’
  \\ conj_tac
  >- metis_tac[]
  \\ rw[]
  \\ Cases_on ‘a0’ \\ fs[]
QED


Theorem ret_satisfy_prog_k_eq:
  t = t' ∧ (∀r. P r ⇒ k r = k' r) ⇒ ret_satisfy P t ⇒ t >>= k = t' >>= k'
Proof
  rpt strip_tac
  \\ rfs[]
  \\ irule ret_satisfy_prog_eq
  \\ pop_assum $ irule_at Any
  \\ fs[]
QED

Theorem itree_semantics_While_with_pre_T:
  (∀s. P_loop s ⇒ itree_semantics (p, s) = loop_t s) ⇒
  (let valword_w = THE (eval s e) in
     if valword_w = ValWord 0w then T
     else P_loop s) ⇒
  (∃w. eval s e = SOME (ValWord w)) ⇒
  itree_semantics (While e p,s) =
  (let
     valword_w = THE (eval s e)
   in
     if valword_w = ValWord 0w then Ret (INR (NONE,s))
     else
       Tau
         (loop_t s >>=
          (λa.
               case a of
                 INL l => Ret (INR (SOME Error,s))
               | INR (res,s') =>
                 case res of
                   NONE => Tau (itree_semantics (While e p,s'))
                 | SOME Error => Ret (INR (res,s'))
                 | SOME TimeOut => Ret (INR (res,s'))
                 | SOME Break => Ret (INR (NONE,s'))
                 | SOME Continue => Tau (itree_semantics (While e p,s'))
                 | SOME (Return v6) => Ret (INR (res,s'))
                 | SOME (Exception v7 v8) => Ret (INR (res,s'))
                 | SOME (FinalFFI v9) => Ret (INR (res,s')))))
Proof
  rpt strip_tac
  \\ rw[Once itree_semantics_While]
  \\ gvs[]
QED

Theorem itree_semantics_If_with_pre_T:
  (∀s. P_p s ⇒ itree_semantics (p, s) = p_t s) ⇒
  (∀s. P_q s ⇒ itree_semantics (q, s) = q_t s) ⇒
  (let valword_w = THE (eval s e) in
     if valword_w ≠ ValWord 0w then P_p s
     else P_q s) ⇒
  (∃vw. eval s e = SOME (ValWord vw)) ⇒
  itree_semantics (If e p q,s) =
  (let
     valword_v = THE (eval s e)
   in
     if valword_v ≠ ValWord 0w then
       Tau
         (p_t s >>=
          (λa.
               Ret
                 (INR
                    (case a of
                       INL l => (SOME Error,s)
                     | INR (res,s') => (res,s')))))
     else
       Tau
         (q_t s >>=
          (λa.
               Ret
                 (INR
                    (case a of
                       INL l => (SOME Error,s)
                     | INR (res,s') => (res,s'))))))
Proof
  rpt strip_tac
  \\ rw[itree_semantics_If]
  \\ gvs[]
QED

Theorem LET_same_value_CONG:
  ∀f g N. (∀x. x = N ⇒ f x = g x) ⇒ LET f N = LET g N
Proof
  rw[LET_CONG]
QED

Theorem LET_same_value_every_CONG:
  ∀f g N. (∀x. f x = g x) ⇒ LET f N = LET g N
Proof
  rw[LET_CONG]
QED

Theorem itree_semantics_Dec_with_pre_let:
  ((∀s. itree_semantics (p,s) = t s) ⇒
  (∃v. eval s e = SOME v) ⇒
  itree_semantics (Dec x sh e p,s) =
  (let
     v = THE (eval s e)
   in
     Tau
       (t (s with locals := s.locals |+ (x,v)) >>=
        (λa.
             Ret
               (INR
                  (case a of
                     INL l => (SOME Error,s)
                   | INR (res,s') =>
                     (res,
                      s' with
                      locals := res_var s'.locals (x,FLOOKUP s.locals x))))))))
  ∧
  ((∀s. Pre s ⇒ itree_semantics (p,s) = t s) ⇒
  (∃v. eval s e = SOME v) ⇒
  (let
     v = THE (eval s e)
   in
     Pre (s with locals := s.locals |+ (x,v))
   ) ⇒
  itree_semantics (Dec x sh e p,s) =
  (let
     v = THE (eval s e)
   in
     Tau
       (t (s with locals := s.locals |+ (x,v)) >>=
        (λa.
             Ret
               (INR
                  (case a of
                     INL l => (SOME Error,s)
                   | INR (res,s') =>
                     (res,
                      s' with
                      locals := res_var s'.locals (x,FLOOKUP s.locals x))))))))
Proof
  rpt strip_tac
  \\ gvs[itree_semantics_Dec, LET_THM]
QED

Theorem LET_LET_same_value:
  LET (λx. LET g v) v = LET g v
Proof
  rw[LET_THM]
QED

Theorem LET_AND_split:
  (LET (λx. P x ∧ Q) v = (LET P v ∧ Q)) ∧
  (LET (λx. P' ∧ Q' x) v = (P' ∧ LET Q' v))
Proof
  rw[LET_THM]
QED

Theorem LET_OR_split:
  (LET (λx. P x ∨ Q) v = (LET P v ∨ Q)) ∧
  (LET (λx. P' ∨ Q' x) v = (P' ∨ LET Q' v))
Proof
  rw[LET_THM]
QED

Theorem LET_ValWord:
  LET f (ValWord v) = f (ValWord v)
Proof
  rw[]
QED

Theorem ret_satisfy_LET:
  ret_satisfy P (LET f v) = LET (λx. ret_satisfy P (f x)) v
Proof
  rw[]
QED



Theorem sum_CASE_eq_pair:
  sum_CASE v f1 f2 = (a, b) ⇔ sum_CASE v (λx. f1 x = (a, b)) (λx. f2 x = (a, b))
Proof
  FULL_CASE_TAC
QED

Theorem COND_eq_pair:
  COND e t f = (a, b) ⇔ COND e (t  = (a, b)) (f = (a, b))
Proof
  FULL_CASE_TAC
QED


Theorem sum_CASE_and:
  ((sum_CASE v f1 f2) ∧ P) ⇔ sum_CASE v (λx. f1 x ∧ P) (λx. f2 x ∧ P)
Proof
  FULL_CASE_TAC
QED

Theorem COND_and:
  ((COND e t f) ∧ P) = COND e (t ∧ P) (f ∧ P)
Proof
  FULL_CASE_TAC
QED

Theorem AND_IMPL_EQ_DISJ:
  (P ∧ (Q ⇒ R)) ⇔ ((P ∧ ¬Q) ∨ (P ∧ R))
Proof
  Cases_on ‘P’ \\ rw[]
  \\ Cases_on ‘Q’ \\ rw[]
QED



Theorem OPTION_EQ_AND_IMPL_simp:
  (((rv = NONE ∧ P) ∧ (rv = NONE ⇒ Q)) ⇔ (rv = NONE ∧ P ∧ Q)) ∧
  (((NONE = rv ∧ P) ∧ (rv = NONE ⇒ Q)) ⇔ (rv = NONE ∧ P ∧ Q)) ∧
  (((rv = SOME v ∧ P) ∧ (rv = NONE ⇒ Q)) ⇔ (rv = SOME v ∧ P)) ∧
  (((SOME v = rv ∧ P) ∧ (rv = NONE ⇒ Q)) ⇔ (rv = SOME v ∧ P))
Proof
  Cases_on ‘rv’ \\ gvs[]
  \\ Cases_on ‘P’ \\ gvs[]
  \\ iff_tac \\ rw[EQ_SYM]
QED

Theorem EXISTS_sum_CASE_THM:
  (∃x. sum_CASE res (P x) (Q x)) ⇔ sum_CASE res (λv. ∃x. (P x) v) (λv. ∃x. (Q x) v)
Proof
  FULL_CASE_TAC
QED

    
Theorem EXISTS_COND_THM:
  (∃x. COND b (P x) (Q x)) ⇔ COND b (∃x. P x) (∃x. Q x)
Proof
  FULL_CASE_TAC
QED


(*
Theorem itree_semantics_ShMemStore_with_pre:
  (∃ad. eval s addr = SOME (ValWord ad)) ⇒
  (∃vl. eval s e = SOME (ValWord w)) ⇒
  (let
     ad = word_of_val (THE (eval s addr))
   in
     if nb_op op = 0 then ad ∈ s.sh_memaddrs
     else byte_align ad ∈ s.sh_memaddrs) ⇒
  ((itree_semantics (ShMemStore op addr e,s)):'a ptree) =
  (let
     ad = word_of_val (THE (eval s addr));
     w = word_of_val (THE (eval s e))
   in
     if nb_op op = 0 then
       Vis
       (SharedMem MappedWrite,[0w],word_to_bytes w F ++ word_to_bytes ad F)
       (λres.
          Tau
          (Ret
           (INR
            (case res of
               INL (INL outcome) =>
                 (SOME
                  (FinalFFI
                   (Final_event (SharedMem MappedWrite) [0w]
                                (word_to_bytes w F ++ word_to_bytes ad F)
                                outcome)),s)
             | INL (INR new_bytes) =>
                 if
                 LENGTH new_bytes = 2 * (dimindex (:α) DIV 8)
                 then
                   (NONE,s)
                 else
                   (SOME
                    (FinalFFI
                     (Final_event (SharedMem MappedWrite) [0w]
                                  (word_to_bytes w F ++ word_to_bytes ad F)
                                  FFI_failed)),s)
             | INR v1 => (SOME Error,s)))))
     else
       Vis
       (SharedMem MappedWrite,[n2w (nb_op op)],
        TAKE (nb_op op) (word_to_bytes w F) ++ word_to_bytes ad F)
       (λres.
          Tau
          (Ret
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
             | INR v1 => (SOME Error,s))))))
Proof
  rw[itree_semantics_ShMemStore, word_of_val_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, FUN_EQ_THM]
  \\ Cases_on ‘op’ \\ gvs[nb_op_def]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem itree_semantics_ShMemLoad_with_pre:
  (∃ad. eval s addr = SOME (ValWord ad)) ⇒
  (∃vl. lookup_kvar vk v s = SOME (Val vl)) ⇒
  (let
     ad = word_of_val (THE (eval s addr))
   in
     if nb_op op = 0 then ad ∈ s.sh_memaddrs
     else byte_align ad ∈ s.sh_memaddrs) ⇒
  (itree_semantics (ShMemLoad op vk v addr,s):'a ptree) =
  (let ad = word_of_val (THE (eval s addr)) in
     Vis (SharedMem MappedRead,[n2w (nb_op op)],word_to_bytes ad F)
         (λres.
            Tau
            (Ret
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
               | INR v2 => (SOME Error,s))))))
Proof
  rw[itree_semantics_ShMemLoad, word_of_val_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, FUN_EQ_THM]
  \\ Cases_on ‘op’ \\ gvs[nb_op_def]
  \\ rpt strip_tac \\ EVERY_CASE_TAC \\ gvs[]
QED
*)

Theorem pair_CASE_sum_CASE_assoc:
  pair_CASE (sum_CASE v f1 f2) f' = sum_CASE v (λv. pair_CASE (f1 v) f') (λv. pair_CASE (f2 v) f')
Proof
  Cases_on ‘v’ \\ gvs[]
QED


Theorem pair_CASE_if_assoc:
  pair_CASE (if be then tb else eb) f' = if be then (pair_CASE tb f') else (pair_CASE eb f')
Proof
  Cases_on ‘be’ \\ gvs[]
QED

Theorem LET_v_LET:
  LET f (LET f' v) = LET (λx. f (f' x)) v
Proof
  rw[]
QED

        
Theorem eval_SOME_Val_impl_eval_SOME:
  (∃v. eval s e = SOME (ValWord v)) ⇒ (∃vv. eval s e = SOME vv)
Proof
  metis_tac[]
QED

    
Theorem pair_LET_pair:
  LET f (v1, v2) =  f (v1, v2)
Proof
  rw[]
QED

           
Theorem itree_semantics_DecCall_with_pre_ret_satisfy:
  ((∀s. itree_semantics (prog1,s) = t s) ∧
  (∃args q r.
        OPT_MMAP (eval s) aexps = SOME args ∧
        lookup_code s.code fname args = SOME (q,r)) ⇒
  itree_semantics (DecCall rt sh fname aexps prog1,s) =
  (let
     args = THE (OPT_MMAP (eval s) aexps);
     (q,r) = THE (lookup_code s.code fname args)
   in
     Tau
     (itree_semantics (q,s with locals := r) >>=
                      (λres. itree_deccall_handler rt sh s res t)))) ∧
  ((∀s. Pre_next s ⇒ itree_semantics (prog1,s) = t s) ∧
  (∃args q r.
        OPT_MMAP (eval s) aexps = SOME args ∧
        lookup_code s.code fname args = SOME (q,r) ∧
        ret_satisfy
        (λx.
           ∃r s'.
             x = INR (SOME r,s') ∧
             ∀retv.
               r = Return retv ⇒
               Pre_next (set_var rt retv (s' with locals := s.locals)))
        (itree_semantics (q,s with locals := r))) ⇒
  itree_semantics (DecCall rt sh fname aexps prog1,s) =
  (let
     args = THE (OPT_MMAP (eval s) aexps);
     (q,r) = THE (lookup_code s.code fname args)
   in
     Tau
     (itree_semantics (q,s with locals := r) >>=
                      (λres. itree_deccall_handler rt sh s res t))))
Proof
  conj_tac
  >- (rpt strip_tac
      \\ rw[itree_semantics_DecCall]
      \\ irule itree_bind_bisim_intro
      \\ rw[FUN_EQ_THM, itree_deccall_handler_def]
     )
  \\ rpt strip_tac
  \\ rw[itree_semantics_DecCall]
  \\ irule ret_satisfy_prog_eq
  \\ pop_assum $ irule_at Any
  \\ rw[FUN_EQ_THM, itree_deccall_handler_def]
  \\ EVERY_CASE_TAC \\ gvs[]
QED

Theorem sum_CASE_same:
  sum_CASE x (λv. P) (λv. P) = P
Proof
  FULL_CASE_TAC
QED

        
Theorem eval_simps:
  (∀w s. eval s (Const w) = SOME (ValWord w)) ∧
  (∀v s. eval s (Var Local v) = FLOOKUP s.locals v) ∧
  (∀v s. eval s (Var Global v) = FLOOKUP s.globals v) ∧
  (∀s. eval s BaseAddr = SOME (ValWord s.base_addr)) ∧
  (∀s. eval s TopAddr = SOME (ValWord s.top_addr)) ∧
  ∀s. eval s BytesInWord = SOME (ValWord bytes_in_word)
Proof
  rw[eval_def]
QED

Theorem eval_eq_SOME_strip_eval:
  ((∃w. eval s (Load One addr) = SOME (ValWord w)) ⇔
     (∃wa. eval s addr = SOME (ValWord wa)) ∧ (let wa = word_of_val (THE (eval s addr)) in wa ∈ s.memaddrs)) ∧
  ((∃w. eval s (Load32 addr) = SOME (ValWord w)) ⇔
     (∃wa. eval s addr = SOME (ValWord wa) ∧
           (let wa = word_of_val (THE (eval s addr)) in aligned 2 wa ∧ (∃vb. s.memory (byte_align wa) = Word vb)
                                                        ∧ byte_align wa ∈ s.memaddrs))) ∧
  ((∃w. eval s (LoadByte addr) = SOME (ValWord w)) ⇔
     (∃wa. eval s addr = SOME (ValWord wa) ∧
              (let wa = word_of_val (THE (eval s addr)) in (∃vb. s.memory (byte_align wa) = Word vb) ∧ byte_align wa ∈ s.memaddrs))) ∧
  ((∃w. eval s (Op Sub [exp1; exp2]) = SOME (ValWord w)) ⇔
     ((∃v1. eval s exp1 = SOME (ValWord v1)) ∧ (∃v2. eval s exp2 = SOME (ValWord v2)))) ∧
  ((∃w. eval s (Panop Mul [exp1; exp2]) = SOME (ValWord w)) ⇔
    ((∃v1. eval s exp1 = SOME (ValWord v1)) ∧ (∃v2. eval s exp2 = SOME (ValWord v2)))) ∧
  ((∃w. eval s (Cmp cmp exp1 exp2) = SOME (ValWord w)) ⇔
     ((∃v1. eval s exp1 = SOME (ValWord v1)) ∧ (∃v2. eval s exp2 = SOME (ValWord v2)))) ∧
  ((∃w. eval (s:'a bstate) (Shift sh exp n) = SOME (ValWord w)) ⇔
     ((∃v. eval s exp = SOME (ValWord v)) ∧ (let v = word_of_val (THE (eval s exp)) in(n = 0 ∨ n < dimindex (:'a)))))
Proof
  rpt conj_tac
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def, mem_load_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, mem_load_def]
      \\ Cases_on ‘s.memory wa’
      \\ rw[]
     )
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def, mem_load_32_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, mem_load_32_def]
     )
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def, mem_load_byte_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, mem_load_byte_def]
     )
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def, wordLangTheory.word_op_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
          \\ EVERY_CASE_TAC \\ gvs[]
          \\ Cases_on ‘w’ \\ rw[]
          \\ Cases_on ‘w'’ \\ rw[]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, wordLangTheory.word_op_def]
     )
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def, pan_op_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
          \\ EVERY_CASE_TAC \\ gvs[]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, pan_op_def]
     )
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, pan_op_def]
     )
  >- (iff_tac
      >- (rpt strip_tac
          \\ gvs[eval_def, word_of_val_def, wordLangTheory.word_sh_def]
          \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
         )
      \\ rpt strip_tac
      \\ gvs[word_of_val_def, eval_def, wordLangTheory.word_sh_def]
      \\ EVERY_CASE_TAC
     )
QED

Definition word_of_Word_def:
  word_of_Word (Word w) = w
End

Theorem eval_eq_SOME_eval_to_let:
  ((∃w. eval s (Load One addr) = SOME (ValWord w)) ⇒
   eval s (Load One addr) = LET (λwa. SOME (Val (s.memory wa))) (word_of_val (THE (eval s addr)))) ∧
  ((∃w. eval s (Load32 addr) = SOME (ValWord w)) ⇒
   eval s (Load32 addr) =
   (let
      wa = word_of_val (THE (eval s addr));
      v = word_of_Word (s.memory (byte_align wa));
      b0 = get_byte wa v s.be;
      b1 = get_byte (wa + 1w) v s.be;
      b2 = get_byte (wa + 2w) v s.be;
      b3 = get_byte (wa + 3w) v s.be;
      (v':word32) =
      if s.be then w2w b0 ≪ 24 ‖ w2w b1 ≪ 16 ‖ w2w b2 ≪ 8 ‖ w2w b3
      else w2w b0 ‖ w2w b1 ≪ 8 ‖ w2w b2 ≪ 16 ‖ w2w b3 ≪ 24
    in
      SOME (ValWord (w2w v')))) ∧
  ((∃w. eval s (LoadByte addr) = SOME (ValWord w)) ⇒
   eval s (LoadByte addr) =
   (let
      wa = word_of_val (THE (eval s addr));
      v = word_of_Word (s.memory (byte_align wa));
      (v':word8) = get_byte wa v s.be
    in
      SOME (ValWord (w2w v')))) ∧
  ((∃w. eval s (Op Sub [exp1; exp2]) = SOME (ValWord w)) ⇒
   eval s (Op Sub [exp1; exp2]) =
   (let
      v1 = word_of_val (THE (eval s exp1));
      v2 = word_of_val (THE (eval s exp2))
    in SOME (ValWord (v1 - v2)))) ∧
  ((∃w. eval s (Panop Mul [exp1; exp2]) = SOME (ValWord w)) ⇒
     eval s (Panop Mul [exp1; exp2]) =
     (let
        v1 = word_of_val (THE (eval s exp1));
        v2 = word_of_val (THE (eval s exp2))
      in SOME (ValWord (v1 * v2)))) ∧
   ((∃w. eval s (Cmp cmp exp1 exp2) = SOME (ValWord w)) ⇒
    eval s (Cmp cmp exp1 exp2) =
    (let
        v1 = word_of_val (THE (eval s exp1));
        v2 = word_of_val (THE (eval s exp2))
     in SOME (ValWord (if word_cmp cmp v1 v2 then 1w else 0w)))) ∧
   ((∃w. eval (s:'a bstate) (Shift sh exp n) = SOME (ValWord w)) ⇒
    eval s (Shift sh exp n) =
    (let
       w = word_of_val (THE (eval s exp));
       v = case sh of
             Lsl => (w ≪ n)
           | Lsr => (w ⋙ n)
           | Asr => (w ≫ n)
           | Ror => (w ⇄ n)
     in SOME (ValWord v)))
Proof
  rpt conj_tac
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, mem_load_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
     )
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, mem_load_32_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
      \\ rw[]
     )
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, mem_load_byte_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
      \\ rw[]
     )
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, wordLangTheory.word_op_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
     )
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, pan_op_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def, pan_op_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
     )
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, asmTheory.word_cmp_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
     )
  >- (rpt strip_tac
      \\ gvs[eval_def, word_of_val_def, wordLangTheory.word_sh_def]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
     )
QED

Theorem val_mem_valword:
  ∃wv. Val (s.memory wa) = ValWord wv
Proof
  Cases_on ‘s.memory wa’ \\ rw[]
QED
        
Theorem val_mem_valword_LET:
  let v = Val (s.memory wa) in
    ∃wv. v = ValWord wv
Proof
  Cases_on ‘s.memory wa’ \\ rw[]
QED
        
Theorem THE_LET_in:
  THE (LET f v) = LET (λx. THE (f x)) v
Proof
  rw[]
QED

        
Theorem word_of_val_LET_in:
  word_of_val (LET f v) = LET (λx. word_of_val (f x)) v
Proof
  rw[]
QED

Theorem exists_LET:
  $? (λe. LET (f e) v) = LET (λx. $? (λe. f e x)) v
Proof
  rw[]
QED

Theorem LET_AND:
  LET (λx. P x ∧ Q x) v = (LET P v ∧ LET Q v)
Proof
  rw[]
QED

Theorem EQ_SAME:
  x = y ∧ z = y ⇒ x = z
Proof
  rw[]
QED



Theorem LET_concrete:
  LET (λx. c) v = c
Proof
  rw[]
QED
        
Theorem LET_v_LET_in:
  LET f (LET f' v) = LET (λx. LET f (f' x)) v
Proof
  rw[]
QED


Theorem eval_exists_strengthen:
  ((∃v. eval s (Const w) = SOME v) ⇔ (eval s (Const w) = SOME (ValWord w))) ∧
  ((∃v. eval s (Struct es) = SOME v) ⇔ (∃es'. eval s (Struct es) = SOME (Struct es'))) ∧
  ((∃v. eval s (Load One addr) = SOME v) ⇔ (∃w. eval s (Load One addr) = SOME (ValWord w))) ∧
  ((∃v. eval s (Load32 addr) = SOME v) ⇔ (∃w. eval s (Load32 addr) = SOME (ValWord w))) ∧
  ((∃v. eval s (LoadByte addr) = SOME v) ⇔ (∃w. eval s (LoadByte addr) = SOME (ValWord w))) ∧
  ((∃v. eval s (Op op es) = SOME v) ⇔ (∃w. eval s (Op op es) = SOME (ValWord w))) ∧
  ((∃v. eval s (Panop p_op es) = SOME v) ⇔ (∃w. eval s (Panop p_op es) = SOME (ValWord w))) ∧
  ((∃v. eval s (Cmp cmp e1 e2) = SOME v) ⇔ (∃w. eval s (Cmp cmp e1 e2) = SOME (ValWord w))) ∧
  ((∃v. eval s (Shift sh e n) = SOME v) ⇔ (∃w. eval s (Shift sh e n) = SOME (ValWord w)))
Proof
  rpt conj_tac
  \\  iff_tac
  \\ rw[eval_def]
  \\ EVERY_CASE_TAC \\ gvs[mem_load_32_def, mem_load_byte_def, wordLangTheory.word_op_def, pan_op_def,
                           asmTheory.word_cmp_def, wordLangTheory.word_sh_def, mem_load_def]
  \\ Cases_on ‘s.memory c’ \\ gvs[]
QED

Theorem exists_val_struct_weakening:
  ((∃w. P = SOME (ValWord w)) ⇒ (∃v. P = SOME v)) ∧
  ((∃w. P = SOME (ValWord w)) ⇒ (∃v. P = SOME v ∧ shape_of v = One)) ∧
  ((∃w. P = SOME (Struct w)) ⇒ (∃v. P = SOME v))
Proof
  rpt strip_tac
  \\ gvs[shape_of_def]
QED

Theorem if_then_else_word_simp:
  ((if b then 1w else 0w) = 1w ⇔ b) ∧
  ((if b then 1w else 0w) = 0w ⇔ ¬b)
Proof
  rw[]
QED


Theorem ret_satisfy_if:
  ret_satisfy P (COND t t1 t2) ⇔ COND t (ret_satisfy P t1) (ret_satisfy P t2)
Proof
  rw[]
QED

Theorem ret_satisfy_FUNPOW_Tau:
  ret_satisfy P t ⇔ ret_satisfy P (FUNPOW Tau n t)
Proof
  Induct_on ‘n’ \\ gvs[]
  \\ rw[FUNPOW_SUC, ret_satisfy_Tau]
QED


Theorem ret_satisfy_wbisim_impl:
  t ≈ t' ⇒ ret_satisfy P t ⇒ ret_satisfy P t'
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘λt'. ∃t''. t' ≈ t'' ∧ ret_satisfy P t''’
  \\ rw[]
  >- metis_tac[itree_wbisim_sym]
  \\ qpat_x_assum ‘a0 ≈ _’ $ assume_tac o SRULE[Once itree_wbisim_strip_tau_cases]
  \\ gvs[]
  >- (disj2_tac
      \\ disj1_tac
      \\ metis_tac[spin, itree_wbisim_refl]
     )
  >- (imp_res_tac strip_tau_FUNPOW
      \\ gvs[GSYM ret_satisfy_FUNPOW_Tau, ret_satisfy_Ret]
      \\ Cases_on ‘n'’ \\ gvs[FUNPOW_SUC]
      \\ qexists ‘Ret r’
      \\ rw[FUNPOW_Tau_wbisim, ret_satisfy_Ret]
     )
  \\ imp_res_tac strip_tau_FUNPOW
  \\ gvs[GSYM ret_satisfy_FUNPOW_Tau, ret_satisfy_Vis]
  \\ Cases_on ‘n'’ \\ gvs[FUNPOW_SUC]
  >- (rpt strip_tac
      \\ qexists ‘k' r’ \\ rw[]
     )
  \\ qexists ‘Vis e k'’ \\ rw[ret_satisfy_Vis]
  \\ ‘FUNPOW Tau n'' (Vis e k) ≈ FUNPOW Tau 0 (Vis e k')’ suffices_by rw[]
  \\ irule FUNPOW_Tau_wbisim_intro
  \\ rw[itree_wbisim_vis_vis]
QED

Theorem ret_satisfy_wbisim_biim:
  t ≈ t' ⇒ (ret_satisfy P t ⇔ ret_satisfy P t')
Proof
  rpt strip_tac
  \\ iff_tac
  \\  metis_tac[itree_wbisim_sym, ret_satisfy_wbisim_impl]
QED

Theorem eval_op_impl_let:
  (∃wv. eval s (Op op es) = SOME (ValWord wv)) ⇒
  eval s (Op op es) =
  let ws = THE (OPT_MMAP (λa. eval s a) es) in
    (OPTION_MAP (λw. ValWord w) (word_op op (MAP (λw. case w of ValWord n => n | Struct v1 => ARB) ws)))
Proof
  rw[eval_def]
  \\ EVERY_CASE_TAC \\ gvs[word_of_val_def]
QED


  
Theorem itree_semantics_While_with_pre_conj:
  (∀s. P_loop s ⇒ itree_semantics (p,s) = loop_t s) ⇒
  ((let
      valword_w = THE (eval s e)
    in
      valword_w = ValWord 0w) ⇒
   (∃w. eval s e = SOME (ValWord w)) ⇒
   itree_semantics (While e p,s) = Ret (INR (NONE,s))) ∧
  ((let
      valword_w = THE (eval s e)
    in
      valword_w ≠ ValWord 0w) ⇒
   P_loop s ⇒
   (∃w. eval s e = SOME (ValWord w)) ⇒
   itree_semantics (While e p,s) =
   Tau
   (loop_t s >>=
           (λa.
              case a of
                INL l => Ret (INR (SOME Error,s))
              | INR (res,s') =>
                  case res of
                    NONE => Tau (itree_semantics (While e p,s'))
                  | SOME Error => Ret (INR (res,s'))
                  | SOME TimeOut => Ret (INR (res,s'))
                  | SOME Break => Ret (INR (NONE,s'))
                  | SOME Continue => Tau (itree_semantics (While e p,s'))
                  | SOME (Return v6) => Ret (INR (res,s'))
                  | SOME (Exception v7 v8) => Ret (INR (res,s'))
                  | SOME (FinalFFI v9) => Ret (INR (res,s')))))
Proof
  rpt strip_tac
  \\ rw[Once itree_semantics_While]
  \\ gvs[]
QED

Theorem itree_semantics_If_with_pre_conj:
  (∀s. P_p s ⇒ itree_semantics (p, s) = p_t s) ⇒
  (∀s. P_q s ⇒ itree_semantics (q, s) = q_t s) ⇒
  ((let
      valword_w = THE (eval s e)
    in
      valword_w ≠ ValWord 0w) ⇒
   P_p s ⇒
   (∃w. eval s e = SOME (ValWord w)) ⇒
   itree_semantics (If e p q,s) =
   Tau
   (p_t s >>=
        (λa.
           Ret
           (INR
            (case a of
               INL l => (SOME Error,s)
             | INR (res,s') => (res,s')))))) ∧
  ((let
      valword_w = THE (eval s e)
    in
      valword_w = ValWord 0w) ⇒
   P_q s ⇒
   (∃w. eval s e = SOME (ValWord w)) ⇒
   itree_semantics (If e p q,s) =
   Tau
   (q_t s >>=
        (λa.
           Ret
           (INR
            (case a of
               INL l => (SOME Error,s)
             | INR (res,s') => (res,s'))))))
Proof
  rpt strip_tac
  \\ rw[itree_semantics_If]
  \\ gvs[]
QED


Theorem strong_bisim_upfrom_abs_FUNPOW_Tau_SUC_abs_intro:
  (∃r. abs r = t ∧ abs' r = t') ⇒
  strong_bisim_upfrom_abs (abs,abs') (FUNPOW Tau (SUC n) t)
  (FUNPOW Tau (SUC n) t')
Proof
  rpt strip_tac
  \\ rpt (pop_assum (fn x => rw[GSYM x]))
  \\ rw[strong_bisim_upfrom_abs_FUNPOW_Tau_SUC_abs]
QED

Theorem FUNPOW_bind_FUNPOW_Tau_comm:
  FUNPOW (λx. x >>= k) n (FUNPOW Tau n' t) = FUNPOW Tau n' (FUNPOW (λx. x >>= k) n t)
Proof
  Induct_on ‘n’
  >- rw[FUNPOW]
  \\ rw[FUNPOW_SUC, GSYM FUNPOW_Tau_bind]
QED

        
Theorem itree_bisim_FUNPOW_Tau_SUC_self_bind_spin:
  t = FUNPOW Tau (SUC n) (t >>= k) ⇔ t = spin 
Proof
  iff_tac
  >- (rpt strip_tac
      \\ rw[GSYM wbisim_spin_eq]
      \\ irule itree_wbisim_coind
      \\ qexists ‘CURRY {(FUNPOW (λx. x >>= k) n (FUNPOW Tau n' t), spin)| n, n' | T }’
      \\ reverse $ rw[]
      >- (qexists ‘(0,0)’
          \\ rw[FUNPOW]
         )
      \\ disj1_tac
      \\ Cases_on ‘x’
      \\ gvs[]
      \\ first_assum (fn x => rw[Once x])
      \\ rw[GSYM FUNPOW_ADD, GSYM FUNPOW_Tau_bind]
      \\ ‘(λx. x >>= k) (FUNPOW Tau (r + SUC n) t) = (FUNPOW Tau (r + SUC n) t) >>= k’ by rw[]
      \\ pop_assum (fn x => PURE_ONCE_REWRITE_TAC[GSYM x])
      \\ PURE_REWRITE_TAC[GSYM (cj 2 FUNPOW)]
      \\ rw[FUNPOW_bind_FUNPOW_Tau_comm, GSYM ADD_SUC]
      \\ rw[Once FUNPOW_SUC, Once spin]
      \\ qexists ‘(SUC q, n + r)’
      \\ rw[]
     )
  \\ rw[spin_bind]
  \\ irule EQ_SYM
  \\ irule $ iffRL FUNPOW_Tau_SUC_cyclic_spin
  \\ irule EQ_REFL
QED

Theorem itree_bisim_FUNPOW_Tau_neq_zero_self_bind_spin:
  n ≠ 0 ⇒ (t = FUNPOW Tau n (t >>= k) ⇔ t = spin)
Proof
  rpt strip_tac
  \\ Cases_on ‘n’ \\ gvs[itree_bisim_FUNPOW_Tau_SUC_self_bind_spin]
QED

Theorem FUNPOW_Tau_neq_zero_cyclic_spin:
  n ≠ 0 ⇒ (t = FUNPOW Tau n t ⇔ t = spin)
Proof
  rpt strip_tac
  \\ Cases_on ‘n’ \\ gvs[FUNPOW_Tau_SUC_cyclic_spin]
QED


Theorem FUNPOW_Tau_SUC_self_bind_abs:
  (∀s. ∃s' n k. t s = FUNPOW Tau (SUC n) (t s' >>= k)) ⇒ t s = spin
Proof
  rpt strip_tac
  \\ rw[GSYM wbisim_spin_eq]
  \\ irule itree_wbisim_coind
  \\ qexists ‘CURRY {(FUNPOW Tau n (t s) >>= k , spin) | n, s, k | T }’
  \\ reverse $ rw[]
  >- (qexists ‘(0,s,Ret)’
      \\ rw[]
     )
  \\ disj1_tac
  \\ Cases_on ‘x’ \\ gvs[]
  \\ Cases_on ‘r’ \\ gvs[]
  \\ first_assum $ qspec_then ‘q'’ mp_tac
  \\ rpt strip_tac
  \\ rw[GSYM ADD_SUC, GSYM FUNPOW_ADD, GSYM FUNPOW_Tau_bind, itree_bind_assoc, Once spin]
  \\ rw[FUNPOW_SUC]
  \\ qexists ‘(n + q, s', (λx. k x >>= r'))’
  \\ rw[]
QED

Theorem FUNPOW_Tau_SUC_self_bind_abs_with_pre:
  (∀s. Pre s ⇒ Pre (f s)) ⇒ (∀s. Pre s ⇒ ∃s' n k. t s = FUNPOW Tau (SUC n) (t (f s) >>= k)) ⇒ Pre s ⇒ t s = spin
Proof
  rpt strip_tac
  \\ rw[GSYM wbisim_spin_eq]
  \\ irule itree_wbisim_coind
  \\ qexists ‘CURRY {(FUNPOW Tau n (t s) >>= k , spin) | n, s, k | Pre s }’
  \\ reverse $ rw[]
  >- (qexists ‘(0,s,Ret)’
      \\ rw[]
     )
  \\ disj1_tac
  \\ Cases_on ‘x’ \\ gvs[]
  \\ Cases_on ‘r’ \\ gvs[]
  \\ first_x_assum $ drule_then assume_tac
  \\ gvs[]
  \\ first_x_assum $ drule_then assume_tac
  \\ rw[GSYM ADD_SUC, GSYM FUNPOW_ADD, GSYM FUNPOW_Tau_bind, itree_bind_assoc, Once spin]
  \\ rw[FUNPOW_SUC]
  \\ qexists ‘(n + q, f q', (λx. k x >>= r'))’
  \\ rw[]
QED


Theorem FUNPOW_Tau_1:
  FUNPOW Tau (SUC 0) t = Tau t
Proof
  rw[]
QED

        
Theorem itree_eq_imp_wbisim:
  t = t' ⇒ t ≈ t'
Proof
  rw[itree_wbisim_refl]
QED
  

Theorem FUNPOW_Tau_2:
  FUNPOW Tau (SUC 1) x = Tau (Tau x)
Proof
  rw[FUNPOW]
QED


(*
Theorem funpow_tau_conv_thm:
   t ≈ FUNPOW Tau (SUC n) x ⇒ t ≈ FUNPOW Tau n x
Proof
  gvs[FUNPOW_SUC]
QED
*)
        
Theorem funpow_tau_conv_thm:
   t ≈ FUNPOW Tau n x ⇒ t ≈ x
Proof
  rpt strip_tac
  \\ dxrule itree_wbisim_trans
  \\ rpt strip_tac
  \\ pop_assum $ qspec_then ‘x’ irule
  \\ rw[FUNPOW_Tau_wbisim]
QED

Theorem tau_conv_thm:
  b ≈ (Tau a) ⇒ b ≈ a
Proof
  rw[]
QED
        
Theorem tau_ret_conv_thm:
  b ≈ (Tau (Ret a)) ⇒ b ≈ (Ret a)
Proof
  disch_tac
  \\ irule itree_wbisim_trans
  \\ qexists ‘(Tau (Ret a))’ \\ rw[itree_wbisim_refl]
QED


        
Theorem tau_vis_conv_thm:
  b ≈ (Tau (Vis e k)) ⇒ b ≈ (Vis e k)
Proof
  disch_tac
  \\ irule itree_wbisim_trans
  \\ qexists ‘(Tau (Vis e k))’ \\ rw[itree_wbisim_refl]
QED

Theorem option_CASE_wbisim_cong:
  (a ≈ b) ∧ (∀x. (f1 x) ≈ (f2 x)) ⇒ ∀x. (option_CASE x a f1) ≈ (option_CASE x b f2)
Proof
  rpt strip_tac
  \\ Cases_on ‘x’ \\ rw[]
QED


Theorem v_CASE_wbisim_cong:
  (∀x. (f1 x) ≈ (f3 x)) ∧ (∀x. (f2 x) ≈ (f4 x)) ⇒ ∀x. (v_CASE x f1 f2) ≈ (v_CASE x f3 f4)
Proof
  rpt strip_tac
  \\ Cases_on ‘x’ \\ rw[]
QED


Theorem word_lab_case_wbisim_cong:
  (∀x. (f1 x) ≈ (f2 x)) ⇒ ∀x. (word_lab_CASE x f1) ≈ (word_lab_CASE x f2)
Proof
  rpt strip_tac
  \\ Cases_on ‘x’ \\ rw[]
QED


Theorem COND_wbisim_cong:
  (a ≈ b) ∧ (c ≈ d) ⇒ (COND x a c) ≈ (COND x b d)
Proof
  rpt strip_tac
  \\ Cases_on ‘x’ \\ rw[]
QED


Theorem sum_CASE_wbisim_cong:
  (∀x. f1 x ≈ f3 x) ∧ (∀x. f2 x ≈ f4 x) ⇒
  ∀x. sum_CASE x f1 f2 ≈ sum_CASE x f3 f4
Proof
  rpt strip_tac
  \\ Cases_on ‘x’ \\ gvs[]
QED
