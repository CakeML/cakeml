(*
An itree semantics for Pancake.
*)

open preamble panLangTheory
              panSemTheory;
local open alignmentTheory
        miscTheory     (* for read_bytearray *)
        wordLangTheory (* for word_op and word_sh *)
        ffiTheory
        itreeTauTheory in end;

val _ = new_theory "panItreeSem";

(* Extension of itreeTauTheory *)
enable_monadsyntax();
declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
            ignorebind = NONE,
            choice = NONE,
            fail = NONE,
            guard = NONE});
enable_monad "itree";

(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;

val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;

Datatype:
  sem_vis_event = FFI_call ffiname (word8 list) (word8 list)
End

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

(* removes clock and ffi by converting state to bstate *)
Definition to_bstate_def:
  to_bstate (s:('a,'b) panSem$state) =
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

(* restores bstate to state, setting clock to 0
 and ffi to argument *)
Definition from_bstate_def:
  from_bstate (s:'a bstate) (fs:'ffi ffi_state) =
    <| locals      := s.locals
     ; code        := s.code
     ; eshapes     := s.eshapes
     ; memory      := s.memory
     ; memaddrs    := s.memaddrs
     ; sh_memaddrs := s.sh_memaddrs
     ; be          := s.be
     ; ffi         := fs
     ; base_addr   := s.base_addr
     ; clock       := 0
|>
End

Definition dummy_oracle_f_def:
  dummy_oracle_f (f:unit) by1 by2 = Oracle_return f []
End

Definition dummy_oracle_def:
  dummy_oracle name = dummy_oracle_f
End

Definition from_bstate_noffi_def:
  from_bstate_noffi (s:'a bstate) =
  <| locals      := s.locals
     ; code        := s.code
     ; eshapes     := s.eshapes
     ; memory      := s.memory
     ; memaddrs    := s.memaddrs
     ; sh_memaddrs := s.sh_memaddrs
     ; be          := s.be
     ; ffi         := <| oracle := dummy_oracle; ffi_state := (); io_events := [] |>
     ; base_addr   := s.base_addr
     ; clock       := 0
  |>
End

Theorem to_bstate_from_bstate_simps[simp]:
  (∀s fs. to_bstate (from_bstate s fs) = s) ∧
  (∀s fs. from_bstate (to_bstate s) fs = s with <| clock := 0; ffi := fs |>) ∧
  (∀s k. to_bstate (s with clock := k) = to_bstate s) ∧
  (∀s k. to_bstate (dec_clock s) = to_bstate s)
Proof
  rw[to_bstate_def,from_bstate_def,panSemTheory.state_component_equality,
     fetch "-" "bstate_component_equality",panSemTheory.dec_clock_def]
QED

Theorem to_from_bstate_access[simp]:
  (to_bstate s).locals = s.locals ∧
  (to_bstate s).code = s.code ∧
  (to_bstate s).eshapes = s.eshapes ∧
  (to_bstate s).memory = s.memory ∧
  (to_bstate s).memaddrs = s.memaddrs ∧
  (to_bstate s).sh_memaddrs = s.sh_memaddrs ∧
  (to_bstate s).be = s.be ∧
  (to_bstate s).base_addr = s.base_addr ∧
  (from_bstate t fs).locals = t.locals ∧
  (from_bstate t fs).code = t.code ∧
  (from_bstate t fs).eshapes = t.eshapes ∧
  (from_bstate t fs).memory = t.memory ∧
  (from_bstate t fs).memaddrs = t.memaddrs ∧
  (from_bstate t fs).sh_memaddrs = t.sh_memaddrs ∧
  (from_bstate t fs).be = t.be ∧
  (from_bstate t fs).ffi = fs ∧
  (from_bstate t fs).base_addr = t.base_addr ∧
  (from_bstate t fs).clock = 0
Proof
  rw[to_bstate_def,from_bstate_def]
QED

(* TODO: Confirm this still works with ffi removed. *)
Theorem to_from_bstate_update[simp]:
  (∀f. to_bstate (locals_fupd f s) = locals_fupd f (to_bstate s)) ∧
  (∀f. to_bstate (code_fupd f s) = code_fupd f (to_bstate s)) ∧
  (∀f. to_bstate (eshapes_fupd f s) = eshapes_fupd f (to_bstate s)) ∧
  (∀f. to_bstate (memory_fupd f s) = memory_fupd f (to_bstate s)) ∧
  (∀f. to_bstate (memaddrs_fupd f s) = memaddrs_fupd f (to_bstate s)) ∧
  (∀f. to_bstate (sh_memaddrs_fupd f s) = sh_memaddrs_fupd f (to_bstate s)) ∧
  (∀f. to_bstate (be_fupd f s) = be_fupd f (to_bstate s)) ∧
  (* (∀f. to_bstate (ffi_fupd f s) = ffi_fupd f (to_bstate s)) ∧ *)
  (∀f. to_bstate (base_addr_fupd f s) = base_addr_fupd f (to_bstate s)) ∧
  (∀f fs. from_bstate (locals_fupd f t) fs = locals_fupd f (from_bstate t fs)) ∧
  (∀f fs. from_bstate (code_fupd f t) fs = code_fupd f (from_bstate t fs)) ∧
  (∀f fs. from_bstate (eshapes_fupd f t) fs = eshapes_fupd f (from_bstate t fs)) ∧
  (∀f fs. from_bstate (memory_fupd f t) fs = memory_fupd f (from_bstate t fs)) ∧
  (∀f fs. from_bstate (memaddrs_fupd f t) fs = memaddrs_fupd f (from_bstate t fs)) ∧
  (∀f fs. from_bstate (sh_memaddrs_fupd f t) fs = sh_memaddrs_fupd f (from_bstate t fs)) ∧
  (∀f fs. from_bstate (be_fupd f t) fs = be_fupd f (from_bstate t fs)) ∧
  (* (∀f fs. from_bstate (ffi_fupd f t) fs = ffi_fupd f (from_bstate t fs)) ∧ *)
  (∀f fs. from_bstate (base_addr_fupd f t) fs = base_addr_fupd f (from_bstate t fs))
Proof
  rw[to_bstate_def,from_bstate_def] >>
  rw[state_component_equality,fetch "-" "bstate_component_equality"]
QED

Definition empty_locals_def:
  empty_locals = to_bstate ∘ (panSem$empty_locals) o from_bstate_noffi
End

Theorem empty_locals_defs = CONJ panSemTheory.empty_locals_def empty_locals_def;

Definition set_var_def:
  set_var x v = to_bstate ∘ (panSem$set_var x v) o from_bstate_noffi
End

Theorem set_var_defs = CONJ panSemTheory.set_var_def set_var_def;


Type htree_ret[pp] = “:'a result option # 'a bstate”;

(* mtrees *)
Type mtree[pp] = “:('a htree_ret,
                    sem_vis_event # ('ffi ffi_result -> 'a htree_ret),
                    'a htree_ret) itree”;

(* htrees *)
Type htree_seed[pp] = “:'a panLang$prog # 'a bstate”;

Type htree[pp] = “:('a htree_ret,
                    'a htree_seed + sem_vis_event # ('ffi ffi_result -> 'a htree_ret),
                    'a htree_ret) itree”;

Type hktree[pp] = “:'a htree_ret -> ('a,'ffi) htree”;

(* ltrees *)
Type ltree[pp] = “:(unit,unit,'a htree_ret) itree”;

Type lktree[pp] = “:'a htree_ret -> 'a ltree”;

(* strees *)
Type stree[pp] = “:('ffi ffi_result, sem_vis_event, 'a htree_ret) itree”;

(* semtrees *)
(* Type semtree[pp] = “:('b ffi_result, sem_vis_event, 'a result option) itree”; *)
(* Type sem8tree[pp] = “:('b ffi_result, sem_vis_event, 8 result option) itree”; *)
(* Type sem16tree[pp] = “:('b ffi_result, sem_vis_event, 16 result option) itree”; *)

Definition mrec_iter_body_def:
  mrec_iter_body rh t =
  case t of
   | Ret r => Ret (INR r)
   | Tau t => Ret (INL t)
   | Vis (INL seed') k => Ret (INL (itree_bind (rh seed') k))
   | Vis (INR e) k => Vis e (Ret o INL o k)
End

Definition itree_mrec_def:
  itree_mrec rh seed =
  itree_iter (mrec_iter_body rh) (rh seed)
End

(* mrec theory *)

(* Characterisation of infinite itree:s in terms of their paths. *)
Definition itree_finite_def:
  itree_finite t = ∃p x. itree_el t p = Return x
End

Definition itree_infinite_def:
  itree_infinite t = ¬(itree_finite t)
End

(* Simp rules for characteristics predicates of
 ITrees *)
Theorem itree_char_simps[simp,compute]:
  (∀r. ¬(itree_infinite $ Ret r))
Proof
  rw [itree_infinite_def,itree_finite_def] >>
  qexists_tac ‘[]’  >>
  qexists_tac ‘r’ >>
  rw [itreeTauTheory.itree_el_def]
QED

(* The rules for the recursive event handler, that decide
 how to evaluate each term of the program command grammar. *)
Definition h_prog_rule_dec_def:
  h_prog_rule_dec vname e p s =
  case (eval (from_bstate_noffi s) e) of
   | SOME value => Vis (INL (p,s with locals := s.locals |+ (vname,value)))
                       (λ(res,s'). Ret (res, s' with locals :=
                                             res_var s'.locals (vname, FLOOKUP s.locals vname)))
   | NONE => Ret (SOME Error,s)
End

Definition h_prog_rule_seq_def:
  h_prog_rule_seq p1 p2 s = Vis (INL (p1,s))
                                (λ(res,s'). if res = NONE
                                            then Vis (INL (p2,s')) Ret
                                            else Ret (res,s'))
End

Definition h_prog_rule_assign_def:
  h_prog_rule_assign vname e s =
  case eval (from_bstate_noffi s) e of
   | SOME value =>
      if is_valid_value s.locals vname value
      then Ret (NONE,s with locals := s.locals |+ (vname,value))
      else Ret (SOME Error,s)
   | NONE => Ret (SOME Error,s)
End

Definition h_prog_rule_store_def:
  h_prog_rule_store dst src s =
  case (eval (from_bstate_noffi s) dst,eval (from_bstate_noffi s) src) of
   | (SOME (ValWord addr),SOME value) =>
      (case mem_stores addr (flatten value) s.memaddrs s.memory of
        | SOME m => Ret (NONE,s with memory := m)
        | NONE => Ret (SOME Error,s))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_store_byte_def:
  h_prog_rule_store_byte dst src s =
  case (eval (from_bstate_noffi s) dst,eval (from_bstate_noffi s) src) of
   | (SOME (ValWord addr),SOME (ValWord w)) =>
      (case mem_store_byte s.memory s.memaddrs s.be addr (w2w w) of
        | SOME m => Ret (NONE,s with memory := m)
        | NONE => Ret (SOME Error,s))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_cond_def:
  h_prog_rule_cond gexp p1 p2 s =
  case (eval (from_bstate_noffi s) gexp) of
   | SOME (ValWord g) => Vis (INL (if g ≠ 0w then p1 else p2,s)) Ret
   | _ => Ret (SOME Error,s)
End

(* NB The design of this while denotation restricts the type of Vis at this level of the semantics
 to having k-trees of: (res,bstate) -> (a,b,c) itree. *)
(* This is converted to the desired state in the top-level semantics. *)

(* Inf ITree of Vis nodes, with inf many branches allowing
 termination of the loop; when the guard is false. *)
Definition h_prog_rule_while_def:
  h_prog_rule_while g p s = itree_iter
                               (λ(p,s). case (eval (from_bstate_noffi s) g) of
                                        | SOME (ValWord w) =>
                                           if (w ≠ 0w)
                                           then (Vis (INL (p,s))
                                                 (λ(res,s'). case res of
                                                              | SOME Break => Ret (INR (NONE,s'))
                                                              | SOME Continue => Ret (INL (p,s'))
                                                              | NONE => Ret (INL (p,s'))
                                                              | _ => Ret (INR (res,s'))))
                                           else Ret (INR (NONE,s))
                                        | _ => Ret (INR (SOME Error,s)))
                               (p,s)
End

(* Handles the return value and exception passing of function calls. *)
Definition h_handle_call_ret_def:
  (h_handle_call_ret calltyp s (NONE,(s' : 'a bstate)) = Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME Break,s') = Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME Continue,s') = Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME (Return retv),s') = case calltyp of
                                                  NONE => Ret (SOME (Return retv),empty_locals s')
                                                 | SOME (rt,_) =>
                                                    if is_valid_value s.locals rt retv
                                                    then Ret (NONE,set_var rt retv (s' with locals := s.locals))
                                                    else Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME (Exception eid exn),s') = case calltyp of
                                                        NONE => Ret (SOME (Exception eid exn),empty_locals s')
                                                       | SOME (_,NONE) => Ret (SOME (Exception eid exn),empty_locals s')
                                                       | SOME (_,(SOME (eid', evar, p))) =>
                                                          if eid = eid'
                                                          then
                                                            (case FLOOKUP s.eshapes eid of
                                                              SOME sh =>
                                                               if shape_of exn = sh ∧ is_valid_value s.locals evar exn
                                                               then Vis (INL (p,set_var evar exn (s' with locals := s.locals))) Ret
                                                               else Ret (SOME Error,s')
                                                             | NONE => Ret (SOME Error,s'))
                                                          else Ret (SOME (Exception eid exn),empty_locals s')) ∧
  (h_handle_call_ret calltyp s (res,s') = Ret (res,empty_locals s'))
End

(* TODO: Fix this *)
Definition h_prog_rule_call_def:
  h_prog_rule_call calltyp tgtexp argexps s =
  case (eval (from_bstate_noffi s) tgtexp,OPT_MMAP (eval (from_bstate_noffi s)) argexps) of
   | (SOME (ValLabel fname),SOME args) =>
      (case lookup_code s.code fname args of
        | SOME (callee_prog,newlocals) =>
           Vis (INL (callee_prog,s with locals := newlocals)) (h_handle_call_ret calltyp s)
        | _ => Ret (SOME Error,s))
   | (_,_) => Ret (SOME Error,s)
End

Definition h_prog_rule_ext_call_def:
  h_prog_rule_ext_call ffi_name conf_ptr conf_len array_ptr array_len s =
  case (eval (from_bstate_noffi s) conf_ptr,eval (from_bstate_noffi s) conf_len,eval (from_bstate_noffi s) array_ptr,eval (from_bstate_noffi s) array_len) of
    (SOME (ValWord conf_ptr_adr),SOME (ValWord conf_sz),
     SOME (ValWord array_ptr_adr),SOME (ValWord array_sz)) =>
     (case (read_bytearray conf_ptr_adr (w2n conf_sz) (mem_load_byte s.memory s.memaddrs s.be),
            read_bytearray array_ptr_adr (w2n array_sz) (mem_load_byte s.memory s.memaddrs s.be)) of
        (SOME conf_bytes,SOME array_bytes) =>
         (if explode ffi_name ≠ "" then
           Vis (INR (FFI_call (ExtCall (explode ffi_name)) conf_bytes array_bytes,
                     (λres. case res of
                              FFI_final outcome => (SOME (FinalFFI outcome),empty_locals s):('a result option # 'a bstate)
                             | FFI_return new_ffi new_bytes =>
                                let nmem = write_bytearray array_ptr_adr new_bytes s.memory s.memaddrs s.be in
                                (NONE,s with <| memory := nmem |>)))) Ret
          else Ret (NONE,s))
       | _ => Ret (SOME Error,s))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_raise_def:
  h_prog_rule_raise eid e s =
  case (FLOOKUP s.eshapes eid, eval (from_bstate_noffi s) e) of
   | (SOME sh, SOME value) =>
      if shape_of value = sh ∧
         size_of_shape (shape_of value) <= 32
      then Ret (SOME (Exception eid value),empty_locals s)
      else Ret (SOME Error,s)
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_return_def:
  h_prog_rule_return e s =
  case (eval (from_bstate_noffi s) e) of
   | SOME value =>
      if size_of_shape (shape_of value) <= 32
      then Ret (SOME (Return value),empty_locals s)
      else Ret (SOME Error,s)
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_sh_mem_load_def:
  h_prog_rule_sh_mem_load v (addr:'a word) nb s =
  if nb = 0 then
    (if addr IN s.sh_memaddrs then
       Vis (INR (FFI_call (SharedMem MappedRead) [n2w nb] (word_to_bytes addr F),
                 (λres. case res of
                          FFI_final outcome => (SOME (FinalFFI outcome),empty_locals s)
                         | FFI_return new_ffi new_bytes =>
                            (NONE, (set_var v (ValWord (word_of_bytes F 0w new_bytes)) s))))) Ret
     else Ret (SOME Error,s))
  else
    (if (byte_align addr) IN s.sh_memaddrs then
       Vis (INR (FFI_call (SharedMem MappedRead) [n2w nb] (word_to_bytes addr F),
       (λres. case res of
                FFI_final outcome => (SOME (FinalFFI outcome),empty_locals s)
               | FFI_return new_ffi new_bytes =>
                  (NONE,(set_var v (ValWord (word_of_bytes F 0w new_bytes)) s))))) Ret
     else Ret (SOME Error,s))
End

Definition h_prog_rule_sh_mem_store_def:
  h_prog_rule_sh_mem_store v (addr:'a word) nb s =
  case FLOOKUP s.locals v of
    SOME (ValWord w) =>
     (if nb = 0 then
        (if addr IN s.sh_memaddrs then
           Vis (INR (FFI_call (SharedMem MappedWrite) [n2w nb]
                              (word_to_bytes w F ++ word_to_bytes addr F),
                (λres. case res of
                         FFI_final outcome => (SOME (FinalFFI outcome),s)
                        | FFI_return new_ffi new_bytes => (NONE,s)))) Ret
         else Ret (SOME Error,s))
      else
        (if (byte_align addr) IN s.sh_memaddrs then
           Vis (INR (FFI_call (SharedMem MappedWrite) [n2w nb]
                              (TAKE nb (word_to_bytes w F) ++ word_to_bytes addr F),
                (λres. case res of
                         FFI_final outcome => (SOME (FinalFFI outcome),s)
                        | FFI_return new_ffi new_bytes =>
                           (NONE,s)))) Ret
         else Ret (SOME Error,s)))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_sh_mem_op_def:
  (h_prog_rule_sh_mem_op Load r (ad:'a word) (s:'a bstate) =
   h_prog_rule_sh_mem_load r ad 0 s) ∧
  (h_prog_rule_sh_mem_op Store r ad s = h_prog_rule_sh_mem_store r ad 0 s) ∧
  (h_prog_rule_sh_mem_op Load8 r ad s = h_prog_rule_sh_mem_load r ad 1 s) ∧
  (h_prog_rule_sh_mem_op Store8 r ad s = h_prog_rule_sh_mem_store r ad 1 s)
End

Definition h_prog_rule_sh_mem_def:
  h_prog_rule_sh_mem op v ad s =
  case eval (from_bstate_noffi s) ad of
    SOME (ValWord addr) =>
     (if is_load op
      then (case FLOOKUP s.locals v of
              SOME (Val _) => h_prog_rule_sh_mem_op op v addr s
             | _ => Ret (SOME Error, s))
      else (case FLOOKUP s.locals v of
              SOME (ValWord _) => h_prog_rule_sh_mem_op op v addr s
             | _ => Ret (SOME Error, s)))
   | _ => Ret (SOME Error, s)
End

(* Recursive event handler for program commands *)
Definition h_prog_def:
  (h_prog (Skip,s) = Ret (NONE,s)) ∧
  (h_prog (Dec vname e p,s) = h_prog_rule_dec vname e p s) ∧
  (h_prog (Assign vname e,s) = h_prog_rule_assign vname e s) ∧
  (h_prog (Store dst src,s) = h_prog_rule_store dst src s) ∧
  (h_prog (StoreByte dst src,s) = h_prog_rule_store_byte dst src s) ∧
  (h_prog (ShMem op v ad,s) = h_prog_rule_sh_mem op v ad s) ∧
  (h_prog (Seq p1 p2,s) = h_prog_rule_seq p1 p2 s) ∧
  (h_prog (If gexp p1 p2,s) = h_prog_rule_cond gexp p1 p2 s) ∧
  (h_prog (While gexp p,s) = h_prog_rule_while gexp p s) ∧
  (h_prog (Break,s) = Ret (SOME Break,s)) ∧
  (h_prog (Continue,s) = Ret (SOME Continue,s)) ∧
  (h_prog (Call calltyp tgtexp argexps,s) = h_prog_rule_call calltyp tgtexp argexps s) ∧
  (h_prog (ExtCall ffi_name conf_ptr conf_len array_ptr array_len,s) =
          h_prog_rule_ext_call ffi_name conf_ptr conf_len array_ptr array_len s) ∧
  (h_prog (Raise eid e,s) = h_prog_rule_raise eid e s) ∧
  (h_prog (Return e,s) = h_prog_rule_return e s) ∧
  (h_prog (Tick,s) = Ret (NONE,s))
End

(* Converts mtree into stree *)
Definition to_stree_def:
  to_stree =
  itree_unfold
  (λmt. case mt of
         Ret r => Ret' r
        | Tau t => Tau' t
        | Vis (e,k) g => Vis' e (g o k))
End

(* Converts stree into semtree *)
Definition to_semtree_def:
  to_semtree =
  itree_unfold
  (λstree. case stree of
         Ret (res,s) => Ret' res
        | Tau t => Tau' t
        | Vis e k => Vis' e k)
End

(* ITree semantics for program commands *)
Definition itree_evaluate_def:
  itree_evaluate p s =
  to_stree (itree_mrec h_prog (p,s))
End

(* Observational ITree semantics *)
val s = ``(s:'a bstate)``;

(* XXX: We may want to remove this as it only corresponds
 to the FBS semantics function that assumes single entrypoint. *)
Definition itree_semantics_def:
  itree_semantics s entry =
  let prog = Call NONE (Label entry) [] in
  to_semtree (itree_evaluate prog s)
End

Definition mrec_sem_def:
  mrec_sem (seed : ('a,'b) htree) =
  itree_iter (mrec_iter_body h_prog) seed
End

Theorem mrec_iter_body_simp[simp]:
  mrec_iter_body h_prog =
  (λt. case t of
         Ret r => Ret (INR r)
        | Tau t => Ret (INL t)
        | Vis (INL seed') k => Ret (INL (monad_bind (h_prog seed') k))
        | Vis (INR e) k => Vis e (Ret ∘ INL ∘ k))
Proof
  rw [FUN_EQ_THM] >>
  rw [mrec_iter_body_def]
QED

Theorem mrec_sem_simps:
  (mrec_sem (Vis (INL seed) k) =
   Tau (mrec_sem (itree_bind (h_prog seed) k))) ∧
  (mrec_sem (Vis (INR e) k) = (Vis e (Tau o mrec_sem o k))) ∧
  (mrec_sem (Ret r) = Ret r) ∧
  (mrec_sem (Tau u) = Tau (mrec_sem u))
Proof
  rw [mrec_sem_def,mrec_iter_body_def] >>
  rw [Once itreeTauTheory.itree_iter_thm] >>
  CONV_TAC FUN_EQ_CONV >> rw [] >>
  rw [mrec_sem_def]
QED

val _ = export_theory();
