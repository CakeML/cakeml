(*
  Theorems of Pancake interaction tree semantics
  with preconditions of expressions.
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
  itree_deccall_handler rt shape s rsh ^res tree1 =
  case res of
  | INR (NONE,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Break,s') => Ret (INR (SOME Error,s'))
  | INR (SOME Continue,s') => Ret (INR (SOME Error,s'))
  | INR (SOME (Return retv), s') =>
      (if shape_of retv = shape ∧ shape_of retv = rsh then
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
  itree_call_handler calltyp rsh s ^res =
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
      if shape_of retv ≠ rsh then Ret (INR (SOME Error,s'))
      else
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
      if sh = shape_of v then
        Tau (((itree_semantics (p,s with locals := s.locals |+ (x,v))):'a ptree) >>=
             (λa. Ret (INR (case a of
                              INL l => (SOME Error, s)
                            | INR (res,s') =>
                                (res, s' with
                       locals := res_var s'.locals (x,FLOOKUP s.locals x))))))
      else Ret (INR (SOME Error, s))
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
  (let v = THE (eval s e) in sh = shape_of v) ⇒
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
  \\ rpt strip_tac
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
        | (SOME (Val v12),NONE) => (SOME Error,s)
        | (SOME (ValWord ad),SOME (ValWord v)) =>
          (case mem_store_byte s.memory s.memaddrs s.be ad (w2w v) of
             NONE => (SOME Error,s)
           | SOME m => (NONE,s with memory := m))
        | (SOME (Val v12),SOME (RStruct v25)) => (SOME Error,s)
        | (SOME (Val v12),SOME (NStruct v26 v27)) => (SOME Error,s)
        | (SOME (RStruct v13),v3) => (SOME Error,s)
        | (SOME (NStruct v14 v15),v3) => (SOME Error,s)))
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
                  if size_of_sh_with_ctxt s.structs (shape_of v) ≤ 32 then
                    (SOME (Return v), empty_locals s)
                  else (SOME Error,s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def, h_prog_return_def]
QED

Theorem itree_semantics_Return_with_pre:
  (∃v. eval s e = SOME v) ⇒
  (let
     v = THE (eval s e)
   in
     size_of_sh_with_ctxt s.structs (shape_of v) ≤ 32) ⇒
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
                if shape_of v = sh ∧ size_of_sh_with_ctxt s.structs (shape_of v) ≤ 32 then
                  (SOME (Exception eid v), empty_locals s)
                else (SOME Error,s)
            | _ => (SOME Error,s)))
Proof
  PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ simp[h_prog_def, h_prog_raise_def]
QED

Theorem itree_semantics_Raise_with_pre:
  (∃sh. FLOOKUP s.eshapes eid = SOME sh) ⇒
  (∃v. eval s e = SOME v) ⇒
  (let
     sh = THE (FLOOKUP s.eshapes eid);
     v = THE (eval s e)
   in
     shape_of v = sh ∧ size_of_sh_with_ctxt s.structs (shape_of v) ≤ 32) ⇒
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
        | SOME (q,r,rsh) =>
            Tau
            (((itree_semantics (q,s with locals := r)):'a ptree) >>=
                        (λres. itree_call_handler calltyp rsh s res))
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
  (∃args q r rsh. OPT_MMAP (eval s) aexps = SOME args ∧ lookup_code s.code fname args = SOME (q,r,rsh)) ⇒
  ((itree_semantics (Call calltyp fname aexps,s)):'a ptree) =
  let args = THE (OPT_MMAP (eval s) aexps) in
    let (q, r, rsh) = THE (lookup_code s.code fname args) in
      Tau (((itree_semantics (q,s with locals := r)):'a ptree)
           >>= (λres. itree_call_handler calltyp rsh s res))
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
       | SOME (q,r,rsh) =>
           Tau
           (((itree_semantics (q,s with locals := r)):'a ptree) >>=
                       (λres. itree_deccall_handler rt sh s rsh res (λs1. itree_semantics (prog, s1)))))
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
  (∃args q r rsh. OPT_MMAP (eval s) aexps = SOME args ∧ lookup_code s.code fname args = SOME (q,r,rsh)) ⇒
  (itree_semantics (DecCall rt sh fname aexps prog,s)):'a ptree =
  let args = THE (OPT_MMAP (eval s) aexps) in
    let (q, r, rsh) = THE (lookup_code s.code fname args) in
      Tau (((itree_semantics (q,s with locals := r)):'a ptree)
           >>= (λres. itree_deccall_handler rt sh s rsh res (λs1. itree_semantics (prog, s1))))
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
          Vis (ExtCall ffiname,x',x)
            (λres.
                 Tau
                   (Ret
                      (INR
                         (case res of
                            INL (INL outcome) =>
                              (SOME
                                 (FinalFFI
                                    (Final_event (ExtCall ffiname)
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
                                    (Final_event (ExtCall ffiname)
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
                   Vis (ExtCall ffiname,x',x)
                       (λres.
                          Tau (Ret
                               (INR
                                (case res of
                                   INL (INL outcome) =>
                                     (SOME
                                      (FinalFFI
                                       (Final_event (ExtCall ffiname) x' x outcome)),empty_locals s)
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
                                         (Final_event (ExtCall ffiname) x' x FFI_failed)),empty_locals s)
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

Theorem itree_semantics_Primitive:
  (itree_semantics (Primitive vname pop es, s)) =
  Ret
    (INR
       (case OPT_MMAP (eval s) es of
          NONE => (SOME Error,s)
        | SOME vs =>
          case pan_primop pop vs of
            NONE => (SOME Error,s)
          | SOME value =>
            if is_valid_value s Local vname value then
              (NONE,set_var vname value s)
            else (SOME Error,s)))
Proof
   PURE_REWRITE_TAC[itree_semantics_def, o_DEF] \\ BETA_TAC
  \\ fs[h_prog_def, h_prog_primitive_def]
QED

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

Theorem ret_satisfy_impl_bind_impl:
  ret_satisfy P t ⇒
  (∀r. P r ⇒ ret_satisfy Q (k r)) ⇒
  ret_satisfy Q (t >>= k)
Proof
  rpt strip_tac
  \\ irule ret_satisfy_coind
  \\ qexists ‘λt. ret_satisfy Q t ∨ (∃t'. t = t' >>= k ∧ ret_satisfy P t')’
  \\ rw[]
  >- metis_tac[]
  >- (pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ gvs[]
     )
  \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
  \\ gvs[]
  >- (first_x_assum $ qspec_then ‘v’ assume_tac
      \\ gvs[]
      \\ pop_assum $ assume_tac o SRULE[Once ret_satisfy_cases]
      \\ gvs[]
     )
  >- metis_tac[]
  \\ metis_tac[]
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

Definition rstruct_of_val_def:
  rstruct_of_val (RStruct v1) = v1 ∧
  rstruct_of_val _ = ARB
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
    (∀v m e. P (Assign v m e)) ∧ (∀m p l. P (Primitive m p l)) ∧
    (∀e e0. P (Store e e0)) ∧ (∀e e0. P (Store32 e e0)) ∧
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
  \\ rw[ret_satisfy_rules, itree_semantics_Annot, itree_semantics_Tick, itree_semantics_Raise,
        itree_semantics_Return, itree_semantics_Skip, itree_semantics_StoreByte, itree_semantics_Store32,
        itree_semantics_Store, itree_semantics_Continue, itree_semantics_Break]
  >- (rw[itree_semantics_Dec]
      \\ FULL_CASE_TAC \\ fs[ret_satisfy_rules]
      \\ FULL_CASE_TAC >> gvs[]
      >- (irule $ cj 2 ret_satisfy_rules
          \\ irule ret_satisfy_bind_k_wrap
          \\ rpt strip_tac
          \\ Cases_on ‘r’ \\ fs[ret_satisfy_rules]
         )
      >> fs[ret_satisfy_rules]
     )
  >- (fs[itree_semantics_Assign]
      \\ FULL_CASE_TAC \\ fs[ret_satisfy_rules]
     )
  >- (fs[itree_semantics_Primitive]
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
      \\ Cases_on ‘r'’ \\ fs[ret_satisfy_rules]
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
      \\ Cases_on ‘r'’ \\ fs[ret_satisfy_rules]
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
      \\ FULL_CASE_TAC \\ gvs[]
      >- (irule itree_bind_resp_t_wbisim
          \\ rw[]
         )
      \\ irule itree_wbisim_refl
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
  v_CASE a b c d >>= e = v_CASE a (λx. b x >>= e) (λx. c x >>= e) (λn x. d n x >>= e)
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
   (let
      v = THE (eval s e)
    in
      sh = shape_of v
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
  ∧
  ((∀s. Pre s ⇒ itree_semantics (p,s) = t s) ⇒
   (∃v. eval s e = SOME v) ⇒
   (let
      v = THE (eval s e)
    in
      Pre (s with locals := s.locals |+ (x,v)) ∧ sh = shape_of v
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
     (q,r,rsh) = THE (lookup_code s.code fname args)
   in
     Tau
     (itree_semantics (q,s with locals := r) >>=
                      (λres. itree_deccall_handler rt sh s rsh res t)))) ∧
  ((∀s. Pre_next s ⇒ itree_semantics (prog1,s) = t s) ∧
  (∃args q r rsh.
        OPT_MMAP (eval s) aexps = SOME args ∧
        lookup_code s.code fname args = SOME (q,r,rsh) ∧
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
     (q,r,rsh) = THE (lookup_code s.code fname args)
   in
     Tau
     (itree_semantics (q,s with locals := r) >>=
                      (λres. itree_deccall_handler rt sh s rsh res t))))
Proof
  conj_tac
  >- (rpt strip_tac
      \\ rw[itree_semantics_DecCall]
      \\ FULL_CASE_TAC \\ gvs[]
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
     ((∃wa. eval s addr = SOME (ValWord wa)) ∧
           (let wa = word_of_val (THE (eval s addr)) in aligned 2 wa ∧ (∃vb. s.memory (byte_align wa) = Word vb)
                                                        ∧ byte_align wa ∈ s.memaddrs))) ∧
  ((∃w. eval s (LoadByte addr) = SOME (ValWord w)) ⇔
     ((∃wa. eval s addr = SOME (ValWord wa)) ∧
              (let wa = word_of_val (THE (eval s addr)) in (∃vb. s.memory (byte_align wa) = Word vb) ∧ byte_align wa ∈ s.memaddrs))) ∧
  ((∃w. eval s (Op Sub [exp1; exp2]) = SOME (ValWord w)) ⇔
     ((∃v1. eval s exp1 = SOME (ValWord v1)) ∧ (∃v2. eval s exp2 = SOME (ValWord v2)))) ∧
  ((∃w. eval s (Panop Mul [exp1; exp2]) = SOME (ValWord w)) ⇔
    ((∃v1. eval s exp1 = SOME (ValWord v1)) ∧ (∃v2. eval s exp2 = SOME (ValWord v2)))) ∧
  ((∃w. eval s (Cmp cmp exp1 exp2) = SOME (ValWord w)) ⇔
     ((∃v1. eval s exp1 = SOME (ValWord v1)) ∧ (∃v2. eval s exp2 = SOME (ValWord v2)))) ∧
  ((∃w. eval (s:'a bstate) (Shift sh e1 e2) = SOME (ValWord w)) ⇔
     ((∃v. eval s e1 = SOME (ValWord v)) ∧ (∃v. eval s e2 = SOME (ValWord v)) ∧
      (let w1 = word_of_val (THE (eval s e1));
           w2 = word_of_val (THE (eval s e2));
           n = w2n w2;
       in
         n = 0 ∨ n < dimindex (:'a))))
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
      \\ rw[is_wf_shape_def]
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
   ((∃w. eval (s:'a bstate) (Shift sh e1 e2) = SOME (ValWord w)) ⇒
    eval s (Shift sh e1 e2) =
    (let
       w = word_of_val (THE (eval s e1));
       w' = word_of_val (THE (eval s e2));
       n = w2n w';
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
      \\ gvs[eval_def, word_of_val_def, mem_load_32_alt]
      \\ EVERY_CASE_TAC \\ gvs[word_of_val_def, word_of_Word_def]
      \\ rw[w2w_def]
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
  ((∃v. eval s (RStruct es) = SOME v) ⇔ (∃es'. eval s (RStruct es) = SOME (RStruct es'))) ∧
  ((∃v. eval s (NStruct nm ls) = SOME v) ⇔ (∃ls'. eval s (NStruct nm ls) = SOME (NStruct nm ls'))) ∧
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
  >- (Cases_on ‘UNZIP ls’ \\ gvs[]
      \\ Cases_on ‘UNZIP x.fields’ \\ gvs[]
      \\ FULL_CASE_TAC \\ gvs[]
     )
  \\ Cases_on ‘s.memory c’ \\ gvs[]
QED

Theorem exists_val_struct_weakening:
  ((∃w. P = SOME (ValWord w)) ⇒ (∃v. P = SOME v)) ∧
  ((∃w. P = SOME (ValWord w)) ⇒ (∃v. P = SOME v ∧ shape_of v = One)) ∧
  ((∃w. P = SOME (RStruct w)) ⇒ (∃v. P = SOME v)) ∧
  ((∃w. P = SOME (NStruct nm w)) ⇒ (∃v. P = SOME v))
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
    (OPTION_MAP (λw. ValWord w) (word_op op (MAP (λw. case w of ValWord n => n | _ => ARB) ws)))
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
  (∀x. (f1 x) ≈ (f4 x)) ∧ (∀x. (f2 x) ≈ (f5 x)) ∧ (∀n x. (f3 n x) ≈ (f6 n x)) ⇒
  ∀x. (v_CASE x f1 f2 f3) ≈ (v_CASE x f4 f5 f6)
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


Theorem word_lab_exists_word:
  ∃wv. w = Word wv
Proof
  Cases_on ‘w’
  \\ rw[]
QED



(* Filter function out *)
Definition is_func_def:
  is_func (Function _) = T ∧
  is_func _ = F
End

Definition dest_func_def:
  dest_func (Function f) = f ∧
  dest_func _ = ARB
End



Definition file_code_def:
  file_code fundecs = FEMPTY |++ (MAP (λx. (x.name, (x.params, del_annot x.body, x.return))) (fundecs))
End

Definition funcname_bodies_def:
  funcname_bodies fundecs = MAP (λx. (x.name, del_annot x.body)) fundecs
End

Definition funcname_params_list_def:
  funcname_params_list fundecs = MAP (λx. (x.name, (x.params, del_annot x.body))) fundecs
End
