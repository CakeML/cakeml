(*
  Semantics of panLang
*)

open preamble panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory
           itreeTauTheory in end;

val _ = new_theory"panSem";
val _ = set_grammar_ancestry [
  "panLang", "itreeTau", "alignment",
  "finite_map", "misc", "wordLang",  "ffi", "lprefix_lub"]

Datatype:
  word_lab = Word ('a word)
           | Label funname
End

Datatype:
  v = Val ('a word_lab)
    | Struct (v list)
End

Overload ValWord  = “\w. Val (Word w)”
Overload ValLabel = “\l. Val (Label l)”

Datatype:
  state =
    <| locals      : varname |-> 'a v
     ; code        : funname |-> ((varname # shape) list # ('a panLang$prog))
                     (* arguments (with shape), body *)
     ; eshapes     : eid |-> shape
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; clock       : num
     ; be          : bool
     ; ffi         : 'ffi ffi_state
     ; base_addr   : 'a word
  (* ; gaddrs      : decname |-> ('a word) (* num? *) *)
  (* TODISC: this maps decname to its starting address in the memory and relative size *)|>
End

val state_component_equality = theorem"state_component_equality";

Datatype:
  result = Error
         | TimeOut
         | Break
         | Continue
         | Return    ('a v)
         | Exception mlstring ('a v)
         | FinalFFI final_event
End

val s = ``(s:('a,'ffi) panSem$state)``


Theorem MEM_IMP_v_size:
   !xs a. MEM a xs ==> (v_size l a < 1 + v1_size l xs)
Proof
  Induct >> fs [] >>
  rpt strip_tac >> rw [fetch "-" "v_size_def"] >>
  res_tac >> decide_tac
QED

Definition shape_of_def:
  shape_of (ValWord _) = One /\
  shape_of (ValLabel _) = One /\
  shape_of (Struct vs) = Comb (MAP shape_of vs)
Termination
  wf_rel_tac `measure (\v. v_size ARB v)` >>
  fs [MEM_IMP_v_size]
End

Overload bytes_in_word = “byte$bytes_in_word”

Definition mem_load_byte_def:
  mem_load_byte m dm be w =
  case m (byte_align w) of
    | Label _ => NONE
    | Word v =>
       if byte_align w IN dm
       then SOME (get_byte w v be) else NONE
End

Definition mem_load_def:
  (mem_load sh addr dm (m: 'a word -> 'a word_lab) =
   case sh of
   | One =>
     if addr IN dm
     then SOME (Val (m addr))
     else NONE
   | Comb shapes =>
     case mem_loads shapes addr dm m of
      | SOME vs => SOME (Struct vs)
      | NONE => NONE) /\

  (mem_loads [] addr dm m = SOME []) /\
  (mem_loads (shape::shapes) addr dm m =
   case (mem_load shape addr dm m,
         mem_loads shapes (addr + bytes_in_word * n2w (size_of_shape shape)) dm m) of
    | SOME v, SOME vs => SOME (v :: vs)
    | _ => NONE)
Termination
  wf_rel_tac ‘measure (\x. case ISR x of
                            | T => list_size shape_size (FST (OUTR x))
                            | F => shape_size (FST (OUTL x)))’ >>
  rw []
  >- (
   qid_spec_tac ‘shapes’ >>
   Induct >> rw [] >> fs [list_size_def, shape_size_def]) >>
  fs [list_size_def, shape_size_def] >>
  fs [list_size_def, shape_size_def]
End

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
        SOME (ValWord s.base_addr))
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
  \\ rpt strip_tac \\ imp_res_tac MEM_IMP_exp_size
  \\ TRY (first_x_assum (assume_tac o Q.SPEC `ARB`))
  \\ decide_tac
End


(* TODISC: why NONE is returned here on write failure *)
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

(*
Definition write_bytearray_def:
  (write_bytearray a [] m dm be = SOME m) /\
  (write_bytearray a (b::bs) m dm be =
     case mem_store_byte m dm be a b of
     | SOME m => write_bytearray (a+1w) bs m dm be
     | NONE => NONE)
End
*)

Definition mem_store_def:
  mem_store (addr:'a word) (w:'a word_lab) dm m =
    if addr IN dm then
    SOME ((addr =+ w) m)
    else NONE
End

Definition mem_stores_def:
  (mem_stores a [] dm m = SOME m) /\
  (mem_stores a (w::ws) dm m =
   case mem_store a w dm m of
    | SOME m' => mem_stores (a + bytes_in_word) ws dm m'
    | NONE => NONE)
End

Definition flatten_def:
  (flatten (Val w) = [w]) ∧
  (flatten (Struct vs) = FLAT (MAP flatten vs))
Termination
  wf_rel_tac `measure (\v. v_size ARB v)` >>
  fs [MEM_IMP_v_size]
End

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

Definition lookup_code_def:
  lookup_code code fname args =
    case (FLOOKUP code fname) of
      | SOME (vshapes, prog) =>
         if ALL_DISTINCT (MAP FST vshapes) ∧
            LIST_REL (\vshape arg. SND vshape = shape_of arg) vshapes args
         then SOME (prog, FEMPTY |++ ZIP (MAP FST vshapes,args))
         else NONE
      | _ => NONE
End

Definition is_valid_value_def:
  is_valid_value locals v value =
    case FLOOKUP locals v of
     | SOME w => shape_of value = shape_of w
     | NONE => F
End

Definition res_var_def:
  (res_var lc (n, NONE) = lc \\ n) /\
  (res_var lc (n, SOME v) = lc |+ (n,v))
End

Definition evaluate_def:
  (evaluate (Skip:'a panLang$prog,^s) = (NONE,s)) /\
  (evaluate (Dec v e prog, s) =
    case (eval s e) of
     | SOME value =>
        let (res,st) = evaluate (prog,s with locals := s.locals |+ (v,value)) in
        (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))
        | NONE => (SOME Error, s)) /\
  (evaluate (Assign v src,s) =
    case (eval s src) of
     | SOME value =>
        if is_valid_value s.locals v value
        then (NONE, s with locals := s.locals |+ (v,value))
        else (SOME Error, s)
        | NONE => (SOME Error, s)) /\
  (evaluate (Store dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord addr), SOME value) =>
       (case mem_stores addr (flatten value) s.memaddrs s.memory of
         | SOME m => (NONE, s with memory := m)
         | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (StoreByte dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord adr), SOME (ValWord w)) =>
        (case mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If e c1 c2,s) =
    case (eval s e) of
     | SOME (ValWord w) =>
        evaluate (if w <> 0w then c1 else c2, s)  (* False is 0, True is everything else *)
     | _ => (SOME Error,s)) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\
  (evaluate (While e c,s) =
    case (eval s e) of
     | SOME (ValWord w) =>
       if (w <> 0w) then
       (if s.clock = 0 then (SOME TimeOut,empty_locals s) else
         let (res,s1) = fix_clock (dec_clock s) (evaluate (c,dec_clock s)) in
         case res of
          | SOME Continue => evaluate (While e c,s1)
          | NONE => evaluate (While e c,s1)
          | SOME Break => (NONE,s1)
          | _ => (res,s1))
        else (NONE,s)
     | _ => (SOME Error,s)) /\
  (evaluate (Return e,s) =
    case (eval s e) of
      | SOME value =>
         if size_of_shape (shape_of value) <= 32
         then (SOME (Return value),empty_locals s)
         else (SOME Error,s)
      | _ => (SOME Error,s)) /\
  (evaluate (Raise eid e,s) =
    case (FLOOKUP s.eshapes eid, eval s e) of
      | (SOME sh, SOME value) =>
         if shape_of value = sh ∧
            size_of_shape (shape_of value) <= 32
         then (SOME (Exception eid value),empty_locals s)
         else (SOME Error,s)
     | _ => (SOME Error,s)) /\
  (evaluate (Tick,s) =
    if s.clock = 0 then (SOME TimeOut,empty_locals s)
    else (NONE,dec_clock s)) /\
  (evaluate (Call caltyp trgt argexps,s) =
    case (eval s trgt, OPT_MMAP (eval s) argexps) of
     | (SOME (ValLabel fname), SOME args) =>
        (case lookup_code s.code fname args of
          | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s)
           else
           let eval_prog = fix_clock ((dec_clock s) with locals := newlocals)
                                     (evaluate (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,st)
              | (SOME Break,st) => (SOME Error,st)
              | (SOME Continue,st) => (SOME Error,st)
              | (SOME (Return retv),st) =>
                  (case caltyp of
                    | Tail      => (SOME (Return retv),empty_locals st)
                    | Ret rt  _ =>
                       if is_valid_value s.locals rt retv
                       then (NONE, set_var rt retv (st with locals := s.locals))
                       else (SOME Error,st))
              | (SOME (Exception eid exn),st) =>
                  (case caltyp of
                    | Tail        => (SOME (Exception eid exn),empty_locals st)
                    | Ret _ NONE => (SOME (Exception eid exn),empty_locals st)
                    | Ret _ (SOME (Handle eid' evar p)) =>
                      if eid = eid' then
                       case FLOOKUP s.eshapes eid of
                        | SOME sh =>
                            if shape_of exn = sh ∧ is_valid_value s.locals evar exn then
                              evaluate (p, set_var evar exn (st with locals := s.locals))
                            else (SOME Error,st)
                        | NONE => (SOME Error,st)
                      else (SOME (Exception eid exn), empty_locals st))
              | (res,st) => (res,empty_locals st))
         | _ => (SOME Error,s))
    | (_, _) => (SOME Error,s)) /\
  (evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
   case (FLOOKUP s.locals len1, FLOOKUP s.locals ptr1, FLOOKUP s.locals len2, FLOOKUP s.locals ptr2) of
    | SOME (ValWord sz1),SOME (ValWord ad1),SOME (ValWord sz2),SOME (ValWord ad2) =>
       (case (read_bytearray ad1 (w2n sz1) (mem_load_byte s.memory s.memaddrs s.be),
              read_bytearray ad2 (w2n sz2) (mem_load_byte s.memory s.memaddrs s.be)) of
         | SOME bytes,SOME bytes2 =>
            (case call_FFI s.ffi (explode ffi_index) bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
              | FFI_return new_ffi new_bytes =>
                let nmem = write_bytearray ad2 new_bytes s.memory s.memaddrs s.be in
                  (NONE, s with <| memory := nmem; ffi := new_ffi |>))
         | _ => (SOME Error,s))
       | res => (SOME Error,s))
Termination
  wf_rel_tac `(inv_image (measure I LEX measure (prog_size (K 0)))
               (\(xs,^s). (s.clock,xs)))` >>
  rpt strip_tac >> TRY (full_simp_tac(srw_ss())[] >> DECIDE_TAC) >>
  imp_res_tac fix_clock_IMP_LESS_EQ >> full_simp_tac(srw_ss())[] >>
  imp_res_tac (GSYM fix_clock_IMP_LESS_EQ) >>
  full_simp_tac(srw_ss())[set_var_def,upd_locals_def,dec_clock_def, LET_THM] >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  decide_tac
End

val evaluate_ind = theorem"evaluate_ind";

(* Infrastructure for ITree-semantics-based program verification. *)
val dummy_ffi_state = “<| oracle := (λs x y z. Oracle_final FFI_failed):unit oracle;
                        ffi_state := ();
                        io_events := NIL |>”;

val sem_self_rec_st = “<| locals := FEMPTY;
                          code := FEMPTY |+ («main»,(NIL:(varname # shape) list, panLang$Call Tail (Label «main») (NIL:('a panLang$exp) list)));
                          eshapes := FEMPTY;
                          memory := λw:('a word). Word w;
                          memaddrs := EMPTY;
                          clock := 0:num;
                          be := F;
                          ffi := ^dummy_ffi_state;
                          base_addr := ARB |>”;

val sem_no_code = “<| locals := FEMPTY;
                      code := FEMPTY;
                      eshapes := FEMPTY;
                      memory := λw:('a word). Word w;
                      memaddrs := EMPTY;
                      clock := 0:num;
                      be := F;
                      ffi := ^dummy_ffi_state;
                      base_addr := ARB |>”;

(* Extension of itreeTauTheory *)
val _ = temp_set_fixity "\226\139\134" (Infixl 500);
Overload "\226\139\134" = “itree_bind”;

Definition itree_trigger_def:
  itree_trigger event = Vis event Ret
End

Definition itree_mrec_def:
  itree_mrec rh seed =
  itree_iter
  (λt. case t of
        | Ret r => Ret (INR r)
        | Tau t => Ret (INL t)
        | Vis (INL seed') k => Ret (INL (itree_bind (rh seed') k))
        | Vis (INR e) k => Vis e (λx. Ret (INL (k x))))
  (rh seed)
End

(* Theorem itree_mrec_cases: *)
(*   case h s of *)
(*     Vis (INL s') k => itree_mrec h s = itree_mrec (λs. itree_bind (h s) k) s' *)
(*    | Ret r => itree_mrec h s = Ret r *)
(*    | Tau t => itree_mrec h s = Tau (itree_mrec (λs. (h s)) t) *)
(*    | Vis (INR e) k => itree_mrec h s = Vis e (λx. Tau (itree_mrec (λs. k s) x)) *)
(* Proof *)
(* QED *)

Theorem itree_mrec_simps[simp]:
  (itree_mrec Ret s = Ret s)
Proof
  rw [itree_mrec_def] >>
  rw [itreeTauTheory.itree_iter_def] >>
  rw [Once itreeTauTheory.itree_unfold]
QED

Theorem itree_mrec_recurse_once[simp]:
  (h s) = Vis (INL seed') k ⇔
  itree_mrec h s = Tau (itree_mrec (λs. itree_bind (h s) k) seed')
Proof
  rw [itree_mrec_def] >>
  rw [itreeTauTheory.itree_iter_def] >>
  rw [Once itreeTauTheory.itree_unfold] >>
  (* needs proof that k' = k and then itree_bind_right_identity *)
  cheat
QED

(* weak termination-exclusive bisimulation *)
Inductive strip_tau_vis:
  (strip_tau_vis t t' ⇒ strip_tau_vis (Tau t) t') ∧
  ((strip_tau_vis t t') ∧ (∀s. (k s) = t) ⇒ strip_tau_vis (Vis e k) t') ∧
  (strip_tau_vis (Ret v) (Ret v))
End

Theorem strip_tau_vis_simps[simp]:
  (strip_tau_vis (Tau u) t = strip_tau_vis u t) ∧
  (strip_tau_vis (Vis e k) (Ret r) = ∀s. strip_tau_vis (k s) (Ret r))
Proof
  cheat
QED

CoInductive itree_vwbisim:
  (strip_tau_vis t t' ⇒ itree_vwbisim t t')
End

Theorem itree_vwbisim_refl:
  itree_vwbisim t t
Proof
  rw [Once itree_vwbisim_cases] >>
  rw [Once strip_tau_vis_cases] >>
  cheat
QED

(* mrec theory *)

(* Show that mrec Vis (INL) nodes are equivalent to one step of general recursion *)
Definition simple_rec_def:
  (simple_rec (0:num) = 0) ∧
  (simple_rec (SUC a) = 1 + (simple_rec a))
End

Theorem itree_mrec_one_rec_event:
  itree_mrec
  (λseed. if seed = 0 then Vis (INL 1) Ret else Ret seed)
  0 = Tau (Ret 1)
Proof
  rw [itree_mrec_def] >>
  rw [itreeTauTheory.itree_iter_def,itreeTauTheory.itree_bind_def] >>
  rpt (rw [Once itreeTauTheory.itree_unfold])
QED

(* Two approaches to reasoning about ITrees as processes:
  - As an equational theory over the itree datatype (the abstraction).
  - As a function on finite paths to :itree_el terms (the representation).

  Each may have their own merits.
 *)

(* Characterisation of infinite itree:s in terms of their paths. *)
Definition itree_finite_def:
  itree_finite t = ∃p x. itree_el t p = Return x
End

Definition itree_infinite_def:
  itree_infinite t = ¬(itree_finite t)
End

(* To prove an ITree is infinite, it suffices to show there is no sequence of events
 after which the tree returns some value. *)
Theorem itree_mrec_inf_event:
  itree_infinite (itree_mrec (λx. Vis (INL rc) Ret) seed)
Proof
  rw [itree_infinite_def,itree_finite_def] >>
  rw [itree_mrec_def]  >>
  rw [itreeTauTheory.itree_iter_def,
        itreeTauTheory.itree_bind_right_identity] >>
  Induct_on ‘p’ >>
  rw [Once itreeTauTheory.itree_unfold,
      itreeTauTheory.itree_bind_right_identity] >>
  Cases_on ‘h’ >>
  rw [itreeTauTheory.itree_el_def]
QED

(* Semantics validation functions *)
(* The rules for the recursive event handler, that decide
 how to evaluate each term of the program command grammar. *)

Definition h_prog_rule_dec_def:
  h_prog_rule_dec vname e p s =
  case (eval s e) of
   | SOME value => Vis (INL (p,s with locals := s.locals |+ (vname,value)))
                       (λ(res,s'). Ret (res,s' with locals := res_var s'.locals (vname, FLOOKUP s.locals vname)))
   | NONE => Ret (SOME Error,s)
End

Definition h_prog_rule_seq_def:
  h_prog_rule_seq p1 p2 s = Vis (INL (p1,s))
                                (λ(res,s'). if res = NONE
                                            then itree_trigger (INL (p2,s'))
                                            else Ret (res,s'))
End

Definition h_prog_rule_assign_def:
  h_prog_rule_assign vname e s =
  case (eval s e) of
   | SOME value =>
      if is_valid_value s.locals vname value
      then Ret (NONE,s with locals := s.locals |+ (vname,value))
      else Ret (SOME Error,s)
   | NONE => Ret (SOME Error,s)
End

Definition h_prog_rule_store_def:
  h_prog_rule_store dst src s =
  case (eval s dst,eval s src) of
   | (SOME (ValWord addr),SOME value) =>
      (case mem_stores addr (flatten value) s.memaddrs s.memory of
        | SOME m => Ret (NONE,s with memory := m)
        | NONE => Ret (SOME Error,s))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_store_byte_def:
  h_prog_rule_store_byte dst src s =
  case (eval s dst,eval s src) of
   | (SOME (ValWord addr),SOME (ValWord w)) =>
      (case mem_store_byte s.memory s.memaddrs s.be addr (w2w w) of
        | SOME m => Ret (NONE,s with memory := m)
        | NONE => Ret (SOME Error,s))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_cond_def:
  h_prog_rule_cond gexp p1 p2 s =
  case (eval s gexp) of
   | SOME (ValWord g) => Vis (INL (if g ≠ 0w then p1 else p2,s)) Ret
   | _ => Ret (SOME Error,s)
End

(* NB The design of this while denotation restricts the type of Vis at this level of the semantics
 to having k-trees of: (res,state) -> (a,b,c) itree. *)
(* This is converted to the desired state in the top-level semantics. *)

(* Inf ITree of Vis nodes, with inf many branches allowing
 termination of the loop; when the guard is false. *)
Definition h_prog_rule_while_def:
  h_prog_rule_while gexp p s = itree_iter
                               (λseed. Vis (INL seed)
                                           (λ(res,s'). case res of
                                                        | SOME Break => Ret (INR (NONE,s'))
                                                        | SOME Continue => Ret (INL (p,s'))
                                                        | NONE => (case (eval s' gexp) of
                                                                    | SOME (ValWord w) =>
                                                                       if w ≠ 0w
                                                                       then Ret (INL (p,s'))
                                                                       else Ret (INR (res,s'))
                                                                    | _ => Ret (INR (SOME Error,s')))
                                                        | _ => Ret (INR (res,s'))))
                               (p,s)
End

(* Handles the return value and exception passing of function calls. *)
Definition h_handle_call_ret_def:
  (h_handle_call_ret calltyp s (NONE,s') = Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME Break,s') = Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME Continue,s') = Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME (Return retv),s') = case calltyp of
                                                  Tail => Ret (SOME (Return retv),empty_locals s')
                                                 | Ret dvar _ =>
                                                    if is_valid_value s.locals dvar retv
                                                    then Ret (NONE,set_var dvar retv (s' with locals := s.locals))
                                                    else Ret (SOME Error,s')) ∧
  (h_handle_call_ret calltyp s (SOME (Exception eid exn),s') = case calltyp of
                                                       | Tail => Ret (SOME (Exception eid exn),empty_locals s')
                                                       | Ret _ NONE => Ret (SOME (Exception eid exn),empty_locals s')
                                                       | Ret _ (SOME (Handle eid' evar p)) =>
                                                          if eid = eid'
                                                          then (case FLOOKUP s.eshapes eid of
                                                                  SOME sh =>
                                                                   if shape_of exn = sh ∧ is_valid_value s.locals evar exn
                                                                   then Vis (INL (p,set_var evar exn (s' with locals := s.locals))) Ret
                                                                   else Ret (SOME Error,s')
                                                                 | NONE => Ret (SOME Error,s'))
                                                          else Ret (SOME (Exception eid exn),empty_locals s')) ∧
  (h_handle_call_ret calltyp s (res,s') = Ret (res,empty_locals s'))
End

Definition h_prog_rule_call_def:
  h_prog_rule_call calltyp tgtexp argexps s =
  case (eval s tgtexp,OPT_MMAP (eval s) argexps) of
   | (SOME (ValLabel fname),SOME args) =>
      (case lookup_code s.code fname args of
        | SOME (callee_prog,newlocals) =>
           Vis (INL (callee_prog,s)) (h_handle_call_ret calltyp s)
        | _ => Ret (SOME Error,s))
   | (_,_) => Ret (SOME Error,s)
End

(* The type of visible events in the ITree semantics. *)
Type ktree = “:α -> (α,β,γ) itree”

Datatype:
  sem_vis_event = FFI_call ('ffi ffi_state) string (word8 list) (word8 list)
End

Definition h_prog_rule_ext_call_def:
  h_prog_rule_ext_call ffi_name conf_ptr conf_len array_ptr array_len s =
  case (FLOOKUP s.locals conf_len,FLOOKUP s.locals conf_ptr,FLOOKUP s.locals array_len,FLOOKUP s.locals array_ptr) of
    (SOME (ValWord conf_sz),SOME (ValWord conf_ptr_adr),
           SOME (ValWord array_sz),SOME (ValWord array_ptr_adr)) =>
                                    (case (read_bytearray conf_ptr_adr (w2n conf_sz) (mem_load_byte s.memory s.memaddrs s.be),
                                           read_bytearray array_ptr_adr (w2n array_sz) (mem_load_byte s.memory s.memaddrs s.be)) of
                                       (SOME conf_bytes,SOME array_bytes) =>
                                        Vis (INR (FFI_call s.ffi (explode ffi_name) conf_bytes array_bytes,
                                            (λres. case res of
                                                     FFI_final outcome => Ret (SOME (FinalFFI outcome),empty_locals s)
                                                    | FFI_return new_ffi new_bytes =>
                                                       let nmem = write_bytearray array_ptr_adr new_bytes s.memory s.memaddrs s.be in
                                                       Ret (NONE,s with <| memory := nmem; ffi := new_ffi |>)
                                                       | _ => Ret (SOME Error,s))))
                                            (λx. case call_FFI s.ffi (explode ffi_name) conf_bytes array_bytes of
                                                   FFI_final outcome => Ret (SOME (FinalFFI outcome),empty_locals s)
                                                  | FFI_return new_ffi new_bytes =>
                                                     let nmem = write_bytearray array_ptr_adr new_bytes s.memory s.memaddrs s.be in
                                                     Ret (NONE,s with <| memory := nmem; ffi := new_ffi |>))
                                      | _ => Ret (SOME Error,s))
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_raise_def:
  h_prog_rule_raise eid e s =
  case (FLOOKUP s.eshapes eid, eval s e) of
   | (SOME sh, SOME value) =>
      if shape_of value = sh ∧
         size_of_shape (shape_of value) <= 32
      then Ret (SOME (Exception eid value),empty_locals s)
      else Ret (SOME Error,s)
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_return_def:
  h_prog_rule_return e s =
  case (eval s e) of
   | SOME value =>
      if size_of_shape (shape_of value) <= 32
      then Ret (SOME (Return value),empty_locals s)
      else Ret (SOME Error,s)
   | _ => Ret (SOME Error,s)
End

Definition h_prog_rule_tick_def:
  h_prog_rule_tick s =
  case s.clock of
    0 => Ret (SOME TimeOut,empty_locals s)
   | _ => Ret (NONE,dec_clock s)
End

(* Recursive event handler for program commands *)
Definition h_prog_def:
  (h_prog (Skip,s) = Ret (NONE,s)) ∧
  (h_prog (Dec vname e p,s) = h_prog_rule_dec vname e p s) ∧
  (h_prog (Assign vname e,s) = h_prog_rule_assign vname e s) ∧
  (h_prog (Store dst src,s) = h_prog_rule_store dst src s) ∧
  (h_prog (StoreByte dst src,s) = h_prog_rule_store_byte dst src s) ∧
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
  (h_prog (Tick,s) = h_prog_rule_tick s)
End

(* XXX: This won't work. *)
Theorem h_prog_evaluate_eq:
  h_prog (p,s) = Ret (evaluate (p,s))
Proof
  rw [Once itreeTauTheory.itree_bisimulation] >>
  qexists_tac ‘strip_tau_vis’ >>
  conj_tac >> cheat
QED

(* Solution to While Loop semantics is to construct an infinite Vis object - using some mechanism - whereby
 the K-tree in each is the original Vis object when the loop guard is true and otherwise produces a Ret. *)

(* Perhaps another solution is to have multiple layers of handler, one for looping constructs and then
 the mrec combinator. Use func comp to define the semantics: sem = (mrec o looper) ... *)

(* A third option is to define ITrees to represent the chain of events that manipulate state.
 Vis events represent handlers of some sort and k-trees the handlers that manipulate state? *)
(* This seems to be what's described in S 2.2.1 of the dissertation *)

(* ITree semantics for program commands *)
Definition evaluate_itree_def:
  evaluate_itree p s = itree_mrec h_prog (p,s)
End

(* Observational ITree semantics *)
(* TODO: Need a combinator over the type of itree returned from: evaluate_itree p s
 that produces the final ITree by converting the type of Vis nodes into the proper type
      and by removing state from the Ret type. *)

Definition semantics_itree_def:
  semantics_itree ^s entry =
  let prog = Call Tail (Label entry) [] in
  itree_unfold
  (λt. case t of
         INL (Ret (res,s)) => Ret' res
        | INL (Tau t) => Tau' (INL t)
        | INL (Vis (e,k) g) => Vis' e (λr. INR (k r))
        | INR (Ret (res,s)) => Ret' res
        | INR (Tau t) => Tau' (INR t)
        | INR (Vis e g) => Vis' e (INR o g))
  (INL (evaluate_itree prog ^s))
End

(* Reasoning about ITree reps *)

(* itree_el can be used to take the abs form of an ITree and reason
 about its components by path reference. *)
Theorem itree_rep_simp_eq:
  itree_el (Tau (Ret 1)) [NONE] = Return 1
Proof
  rw [itreeTauTheory.itree_el_def]
QED

(* Proof of isomorphism with operational semantics *)
Theorem itree_sem_evaluate_biject_skip:
  (case itree_el (evaluate_itree Skip s) [] of
      Event v2 => ARB
    | Return r => r
    | Silence => ARB) = evaluate (Skip,s)
Proof
  rw [evaluate_itree_def,itree_mrec_def] >>
  rw [itreeTauTheory.itree_el_def,itreeTauTheory.itree_iter_def] >>
  rw [h_prog_def] >>
  rw [Once itreeTauTheory.itree_unfold] >>
  rw [evaluate_def]
QED

(* TODO: Requires recursive proof *)
(* How can one appeal to the future assumption that the current theorem is proven
 in order to continue a proof without very many nested cases *)

(* TODO: Possibly need a relation on prog x state such that members have the property that
h_prog generates an itree for (prog x state) that when applied to itree_mrec produces an itree
that has in every leaf the same result as in evaluate (prog x state). *)

(* Path-based proof of isomorphism between semantics *)

(* the mrec combinator theory *)
(* prove useful identities over "mrec handler seed" *)

(* TODO: Proof that mrec Vis (INL) events are equivalent to the clock-bounded recursion
 used in evaluate *)

(* Bisimulation proof of isomorphism between semantics *)
(* Can be interred once the evaluate_biject is proven by itree_el_eqv. *)

(* NOTE: Because the intermediate semantics has Vis nodes with constant ktrees,
 we can prove the bijection that our semantics produces in every branch a Ret node
    containing the result identical to that produced by the operational semantics. *)
(* The outer-most semantics then modifies this shape by allowing Vis nodes to have ktrees
 dependent on FFI results. *)

(* XXX: Equality will not work.
Need to prove evaluate produces a fininte prefix of the equivalent tree
 and every tree is in some way equivalent to evaluate.

 Don't use a direct equality!.
*)
(* Theorem semantics_evaluate_wbisim: *)
(*   evaluate_itree p s = Ret (evaluate (p,s)) *)
(* Proof *)
(*   rw [Once itreeTauTheory.itree_bisimulation] >> *)
(*   qexists_tac ‘strip_tau_vis’ >> *)
(*   conj_tac *)
(*   (* Proving the results of both semantics are in the relation *) *)
(*   >- (Cases_on ‘p’ >> *)
(*       rw [evaluate_itree_def,Once evaluate_def] >> *)
(*       rw [itree_mrec_def,h_prog_def] >> *)
(*       rw [itreeTauTheory.itree_iter_def] *)
(*       (* Skip *) *)
(*       >- (rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rw [strip_tau_vis_rules]) *)
(*       (* Dec *) *)
(*       >- (rw [h_prog_rule_dec_def] >> *)
(*           Cases_on ‘eval s e’ >> rw [] *)
(*           (* (eval s e) = NONE *) *)
(*           >- (rw [Once itreeTauTheory.itree_unfold] >> *)
(*               rw [strip_tau_vis_rules]) *)
(*           (* (eval s e) = SOME x *) *)
(*           (* recursion at this point *) *)
(*           >> cheat) *)
(*       (* Assign *) *)
(*       >- (rw [h_prog_rule_assign_def] >> *)
(*           Cases_on ‘eval s e’ >> rw[] >> *)
(*           rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rw [strip_tau_vis_rules]) *)
(*          (* Store *) *)
(*       >- (rw [h_prog_rule_store_def] >> *)
(*           Cases_on ‘eval s e’ >> *)
(*           Cases_on ‘eval s e0’ >> *)
(*           rw [mem_stores_def] >> *)
(*           rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rw [strip_tau_vis_rules] >> *)
(*           (* eval definition is recursive at this point *) *)
(*           cheat) *)
(*       (* Store Byte *) *)
(*       >- (rw [h_prog_rule_store_byte_def] >> *)
(*           Cases_on ‘eval s e’ >> *)
(*           Cases_on ‘eval s e0’ *)
(*           >- (rw [mem_store_byte_def] >> *)
(*               rw [Once itreeTauTheory.itree_unfold] >> *)
(*               rw [strip_tau_vis_rules]) *)
(*           >- (rw [mem_store_byte_def] >> *)
(*               rw [Once itreeTauTheory.itree_unfold] >> *)
(*               rw [strip_tau_vis_rules]) *)
(*           >- (rw [mem_store_byte_def] >> *)
(*               rw [Once itreeTauTheory.itree_unfold] >> *)
(*               (* store byte def is recursive at this point *) *)
(*               cheat) >> cheat) *)
(*       (* Seq *) *)
(*       >- (rw [h_prog_rule_seq_def] >> *)
(*           (* recursive at this point *) *)
(*           cheat) *)
(*       (* Cond *) *)
(*       >- (cheat) *)
(*       (* While *) *)
(*       >- (cheat) *)
(*       >- (cheat) *)
(*          (* Continue *) *)
(*       >- (rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rw [strip_tau_vis_rules]) *)
(*       (* Break *) *)
(*       >- (rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rw [strip_tau_vis_rules]) *)
(*       (* ExtCall *) *)
(*       >- (cheat) *)
(*       (* Call *) *)
(*       >- (cheat) *)
(*          (* Raise *) *)
(*       >- (rw [h_prog_rule_raise_def] >> *)
(*           rw [Once itreeTauTheory.itree_unfold] >> *)
(*           Cases_on ‘FLOOKUP s.eshapes m’ >> *)
(*           rw [strip_tau_vis_rules] >> *)
(*           Cases_on ‘eval s e’ >> rw [] >> *)
(*           rpt (rw [strip_tau_vis_rules])) *)
(*       (* Return *) *)
(*       >- (rw [h_prog_rule_return_def] >> *)
(*           Cases_on ‘eval s e’ >> *)
(*           rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rpt (rw [strip_tau_vis_rules])) *)
(*       (* Tick *) *)
(*       (* s.clock = 0 *) *)
(*       >- (rw [h_prog_rule_tick_def] >> *)
(*           rw [Once itreeTauTheory.itree_unfold] >> *)
(*           rw [strip_tau_vis_rules]) *)
(*       >- (rw [h_prog_rule_tick_def] >> *)
(*           Induct_on ‘s.clock’ >> cheat)) *)
(*           (* s.clock = 0 *) *)
(*           (* >- (rw [Once itreeTauTheory.itree_unfold] >> *) *)
(*           (*     rw [strip_tau_vis_rules]) *) *)
(*           (* (* s.clock = SUC v *) *) *)
(*           (* >- (rw [h_prog_rule_tick_def])) *) *)
(* QED *)

(* Proof of correspondence between operational and ITree semantics *)
(* observational big-step semantics has three possible outcomes, defined in ffi$behaviour
 - Terminate
 - Diverge
 - Fail

 The isomorphism can be such that:

 Diverge equates to an ITree with infinitely many Tau:s, i.e. t = Tau t

 Terminate requires the outcome of both semantics to be the same (the return value)

 Fail should only happen when it occurs in the other semantics.

 In other words, these behaviours are the properties preserved by the isomorphism.
 *)

(* The ITree branches represent choices for the ExtCall return value.
    The oracle mechanism used in the op semantics makes this choice.
    Hence we need an "oracle choice" function which produces the leaf of an ITree
    by choosing the correct branch at every Vis.

    This "oracle choice" forms the basis of the isomorphism.
 *)

(* converts a tree t into a Tau-Ret tree s.t. if the final tree
 is terminal then the tree t had a terminal path when the oracle or
    chooses branches; otherwise the final tree with be an infinite (divergent) tau
    tree, indicating the tree t was divergent. *)
Definition itree_oracle_walk_def:
  itree_oracle_walk oracle t =
  itree_iter
  (λt'. case t' of
         Ret r => Ret (INR r)
        | Tau u => Ret (INL u)
        | Vis e k => Ret (INL (k (oracle e))))
  t
End

Theorem itree_oracle_walk_cases:
  itree_el (itree_oracle_walk or t) path ≠ Event e
Proof
  Induct_on ‘path’ >>
  Cases_on ‘t’ >>
  rw [itree_oracle_walk_def] >>
  rw [itreeTauTheory.itree_iter_def] >>
  rw [Once itreeTauTheory.itree_unfold]
  >- (Cases_on ‘h’ >>
      rw[])
  >- (Cases_on ‘h’ >>
      Induct_on ‘path’ >>
     (* TODO *)
        cheat
     )
  >> cheat
QED

Definition ext_call_oracle_h_def:
  ext_call_oracle_h (FFI_call fs name args bytes) = call_FFI fs name args bytes
End

Definition itree_diverges_def:
  itree_diverges t ⇔ t = Tau t
End

Definition itree_fails_def:
  itree_fails t = (∃p. case itree_el (itree_oracle_walk ext_call_oracle_h t) p of
                         Return (SOME TimeOut) => F
                        | Return (SOME (FinalFFI _)) => F
                        | Return (SOME (Return _)) => F
                        | _ => T)
End

Definition itree_terminates_def:
  itree_terminates t ⇔ ∃p v. itree_el (itree_oracle_walk ext_call_oracle_h t) p = Return (SOME (Return v))
End

(* Correspondence theorem *)
Theorem semantics_corr:
  ((semantics s start = Diverge e) ⇔ itree_diverges (semantics_itree s start)) ∧
  ((semantics s start = Fail) ⇔ itree_fails (semantics_itree s start)) ∧
  ((semantics s start = (Terminate oc evt)) ⇔ itree_terminates (semantics_itree s start))
Proof
QED

Theorem vshapes_args_rel_imp_eq_len_MAP:
  !vshapes args.
    LIST_REL (\vshape arg. SND vshape = shape_of arg)  vshapes args ==>
     LENGTH vshapes = LENGTH args /\ MAP SND vshapes = MAP shape_of args
Proof
  ho_match_mp_tac LIST_REL_ind >> rw []
QED

(*
Definition evaluate_main_def:
  (evaluate_main (Decl dname str,^s) = ARB) /\
  (evaluate_main (Func fname rettyp partyp prog,s) = ARB)
End
*)

Theorem evaluate_clock:
   !prog s r s'. (evaluate (prog,s) = (r,s')) ==>
                 s'.clock <= s.clock
Proof
  recInduct evaluate_ind >>
  REPEAT STRIP_TAC >>
  POP_ASSUM MP_TAC >> ONCE_REWRITE_TAC [evaluate_def] >>
  rw [] >> every_case_tac >>
  fs [set_var_def, upd_locals_def, empty_locals_def, dec_clock_def, LET_THM] >>
  rveq >> fs [] >>
  rpt (pairarg_tac >> fs []) >>
  every_case_tac >> fs [] >> rveq >>
  imp_res_tac fix_clock_IMP_LESS_EQ >>
  imp_res_tac LESS_EQ_TRANS >> fs [] >> rfs [] >>
  ‘s.clock <= s.clock + 1’ by DECIDE_TAC >>
  res_tac >> fs []
QED

Theorem fix_clock_evaluate:
  fix_clock s (evaluate (prog,s)) = evaluate (prog,s)
Proof
  Cases_on `evaluate (prog,s)` >> fs [fix_clock_def] >>
  imp_res_tac evaluate_clock >>
  fs [GSYM NOT_LESS, state_component_equality]
QED

(* we save evaluate theorems without fix_clock *)
val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

(* observational semantics *)

Definition semantics_def:
  semantics ^s start =
   let prog = Call Tail (Label start) [] in
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


val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
