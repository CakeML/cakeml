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

(* Extension of itreeTauTheory *)
val _ = temp_set_fixity "\226\139\134" (Infixl 500);
Overload "\226\139\134" = “itree_bind”;

Definition itree_trigger_def:
  itree_trigger event = Vis event Ret
End

(* Definition itree_cat_def: *)
(*   itree_cat t1 t2 = itree_bind t1 (λx. t2) *)
(* End *)

(* val _ = set_fixity "\226\140\162" (Infixl 500); *)
(* Overload "\226\140\162" = “itree_cat”; *)

Definition itree_mrec_def:
  itree_mrec rh seed =
  itree_iter
  (λt. case t of
        | Ret r => Ret (INR r)
        | Tau t => Ret (INL t)
        | Vis (INL seed') k => Ret (INL (itree_bind (rh seed') k))
        | Vis (INR e) k => itree_bind (itree_trigger e) (λx. Ret (INL (k x))))
  (rh seed)
End

(* Semantics validation functions *)
Definition handle_call_ret_def:
  handle_call_ret calltyp (res,s) = ARB
End

Definition make_vis_def:
  make_vis p s = Vis (INL (p,s)) k
End

(* Inf ITree of Vis nodes, with inf many branches allowing
 termination of the loop; when the guard is false. *)
Definition while_vis_def:
  while_vis g p s = itree_iter
                     (λseed'. (Vis (INL seed')
                               (λ(res,s'). case (eval s' g) of
                                            | SOME (ValWord w) =>
                                               if (w ≠ 0w)
                                               then Ret (INL (p,s'))
                                               else Ret (INR (res,s'))
                                            | _ => Ret (INR (SOME Error,s')))))
                     (p,s)
End

(* Recursive event handler for program commands *)
Definition h_prog_def:
  (h_prog ((Seq p1 p2),s) = itree_trigger (INL (p1,s)) ⋆ λ(r,s'). itree_trigger (INL (p2,s'))) ∧
  (h_prog (Assign v e,s) =
   case (eval s e) of
    | SOME value =>
       if is_valid_value s.locals v value
       then Ret (NONE,s with locals := s.locals |+ (v,value))
       else Ret (SOME Error,s)
    | NONE => Ret (SOME Error,s)) ∧
  (h_prog ((Call calltyp tgtexp argexps),s) =
   case (eval s tgtexp, OPT_MMAP (eval s) argexps) of
     | (SOME (ValLabel fname), SOME args) =>
        (case lookup_code s.code fname args of
          | SOME (callee_prog, newlocals) =>
             itree_trigger (INL (callee_prog,s)) ⋆ (handle_call_ret calltyp)
          | _ => Ret (SOME Error,s))
     | (_,_) => Ret (SOME Error,s)) ∧
  (h_prog ((While gexp p),s) = while_vis gexp p s)
End

(* Solution to While Loop semantics is to construct an infinite Vis object - using some mechanism - whereby
 the K-tree in each is the original Vis object when the loop guard is true and otherwise produces a Ret. *)

Definition special_vis_def:
  special_vis = itree_iter
                (K (Vis () (λx. Ret (INL ()))))
                ()
End

Theorem special_vis_tau:
  special_vis = Vis () f ⇒ ∀x. f x = Tau special_vis
Proof
  rw [special_vis_def]
QED

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
Definition semantics_itree_def:
  semantics_itree ^s entry =
  let prog = Call Tail (Label entry) [] in
  evaluate_itree prog s ⋆ (Ret o FST)
End

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

(* Need to know how FUN_FMAP works in order to prove this *)
Triviality flookup_ne_fun_name:
  FLOOKUP FEMPTY «foo» = NONE
Proof
  rw [FLOOKUP_DEF]
QED

(* Non-existent functions cannot be called. *)
Theorem sem_tail_call_undefined:
  (eval_prog_itree (panLang$Call Tail (Label «foo») NIL)) ^sem_no_code = Ret (SOME Error, ^sem_no_code)
Proof
  rw [eval_prog_itree_def, Once itreeTauTheory.itree_unfold, eval_def]
QED

Theorem set_membership:
  2:num ∈ { x:num | x <= 2 }
Proof
  rw [IN_DEF]
QED

Theorem fun_fmap_app:
  (FEMPTY |+ (3,4)) ' 3 = 4
Proof
  rw []
QED

Theorem fun_fmap_complex_app:
  (FEMPTY |+ («main»,(NIL:(varname # shape) list, panLang$Call Tail (Label «main») (NIL:('a panLang$exp) list)))) ' «main» =
  (NIL:(varname # shape) list, panLang$Call Tail (Label «main») (NIL:('a panLang$exp) list))
Proof
  rw []
QED

Theorem itree_eq:
  ∀x. Tau (Ret x) = Tau (Ret x)
Proof
  rw []
QED

(* Self-recursing functions produce infinite skinny trees of Tau:s *)
(* TODO: Requires proof that in recursive self-call scenario the two unfolds with accumulating call stack
 do in fact produce the same tree. Then itree_wbisim_tau will apply.*)
Theorem sem_recursive_self_tail_call:
  ((eval_prog_itree (panLang$Call Tail (Label «main») NIL)) ^sem_self_rec_st) =
  Tau ((eval_prog_itree (panLang$Call Tail (Label «main») NIL)) ^sem_self_rec_st)
Proof
  rw [Once itreeTauTheory.itree_bisimulation] >>
  qexists_tac ‘itree_wbisim’ >>
  rw [] >>
  rw [itreeTauTheory.itree_wbisim_tau] >>
  rw [eval_prog_itree_def]
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
