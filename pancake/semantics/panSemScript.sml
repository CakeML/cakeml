(*
  Semantics of panLang
*)

open preamble panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory in end;

val _ = new_theory"panSem";
val _ = set_grammar_ancestry [
  "panLang", "alignment",
  "finite_map", "misc", "wordLang",  "ffi"]

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
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; clock       : num
     ; be          : bool
     ; ffi         : 'ffi ffi_state
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
         | Exception ('a v)
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
  (mem_load One addr dm m =
    if addr IN dm
    then SOME (Val (m addr))
    else NONE) /\
  (mem_load (Comb shapes) addr dm m =
   case mem_loads shapes addr dm m of
    | SOME vs => SOME (Struct vs)
    | NONE => NONE) /\

  (mem_loads [] addr dm m = SOME []) /\
  (mem_loads (shape::shapes) addr dm m =
   case (mem_load shape addr dm m,
         mem_loads shapes (addr + bytes_in_word * n2w (size_of_shape shape)) dm m) of
    | SOME v, SOME vs => SOME (v :: vs)
    | _ => NONE)
End


Definition the_words_def:
  (the_words [] = SOME []) /\
  (the_words (w::ws) =
     case (w,the_words ws) of
      | SOME (ValWord x), SOME xs => SOME (x::xs)
      | _ => NONE)
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
     | _ => NONE)
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
  (write_bytearray a [] m dm be = SOME m) /\
  (write_bytearray a (b::bs) m dm be =
     case mem_store_byte m dm be a b of
     | SOME m => write_bytearray (a+1w) bs m dm be
     | NONE => NONE)
End

Definition mem_store_def:
  (mem_store (Val w) addr dm m =
    if addr IN dm
    then SOME ((addr =+ w) m)
    else NONE) /\
  (mem_store (Struct vs) addr dm m =
    mem_stores vs addr dm m) /\

  (mem_stores [] addr dm m = SOME m) /\
  (mem_stores (v::vs) addr dm m =
   case mem_store v addr dm m of
    | SOME m' =>
       mem_stores vs (addr + bytes_in_word * n2w (size_of_shape (shape_of v))) dm m'
    | NONE => NONE)
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
         if LIST_REL (\vshape arg. SND vshape = shape_of arg)  vshapes args
         then SOME (prog, alist_to_fmap (ZIP (MAP FST vshapes,args)))
         else NONE
      | _ => NONE
End

(*
  restore variable to its previously declared value if any,
  otherwise destroy it
*)
Definition res_var_def:
  res_var v locals locals' =
    case FLOOKUP locals v of
     | SOME value => locals' |+ (v,value)
     | NONE => locals' \\ v
End

Definition is_valid_value_def:
  is_valid_value locals v value =
    case FLOOKUP locals v of
     | SOME w => shape_of value = shape_of w
     | NONE => F
End

Definition evaluate_def:
  (evaluate (Skip:'a panLang$prog,^s) = (NONE,s)) /\
  (evaluate (Dec v e prog, s) =
    case (eval s e) of
     | SOME value =>
        let (res,st) = evaluate (prog,set_var v value s) in
        (res, st with locals := res_var v s.locals st.locals)
     | NONE => (SOME Error, s)) /\
  (evaluate (Assign v src,s) =
    case (eval s src) of
     | SOME value =>
        if is_valid_value s.locals v value
        then (NONE, set_var v value s)
        else (SOME Error, s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Store dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord addr), SOME value) =>
       (case  mem_store value addr s.memaddrs s.memory of
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
        let (res,s1) = fix_clock s (evaluate (c,s)) in
        case res of
        | SOME Continue =>
            if s1.clock = 0 then (SOME TimeOut,empty_locals s1)
            else evaluate (While e c,dec_clock s1)
        | NONE =>
          if s1.clock = 0 then (SOME TimeOut,empty_locals s1)
          else evaluate (While e c,dec_clock s1)
        | SOME Break => (NONE,s1)
        | _ => (res,s1)
       else (NONE,s)
       | _ => (SOME Error,s)) /\
  (evaluate (Return e,s) =
    case (eval s e) of
     | SOME value => (SOME (Return value),empty_locals s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise e,s) =
    case (eval s e) of
     | SOME value => (SOME (Exception value),empty_locals s)
     | _ => (SOME Error,s)) /\
  (evaluate (Tick,s) =
    if s.clock = 0 then (SOME TimeOut,empty_locals s)
    else (NONE,dec_clock s)) /\
  (evaluate (Call caltyp trgt argexps,s) =
    case (eval s trgt, OPT_MMAP (eval s) argexps) of
     | (SOME (ValLabel fname), SOME args) =>
        (case lookup_code s.code fname args of
         | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s) else
           let eval_prog = fix_clock ((dec_clock s) with locals:= newlocals)
                                     (evaluate (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,s)
              | (SOME Break,st) => (SOME Error,s)
              | (SOME Continue,st) => (SOME Error,s)
              | (SOME (Return retv),st) =>
                  (case caltyp of
                    | Tail    => (SOME (Return retv),empty_locals st)
                    | Ret rt  =>
                       if is_valid_value s.locals rt retv
                       then (NONE, set_var rt retv (st with locals := s.locals))
                       else (SOME Error,s)
                    | Handle rt evar shape p =>
                       if is_valid_value s.locals rt retv
                       then (NONE, set_var rt retv (st with locals := s.locals))
                       else (SOME Error,s))
              | (SOME (Exception exn),st) =>
                  (case caltyp of
                    | Tail    => (SOME (Exception exn),empty_locals st)
                    | Ret rt  => (SOME (Exception exn), empty_locals st (*st with locals := s.locals*))
                    | Handle rt evar shape p =>
                       if shape_of exn = shape then
                       evaluate (p, set_var evar exn (st with locals := s.locals))
                       else (SOME (Exception exn), empty_locals st))
                      (* shape mismatch means we raise the exception and thus pass it on *)
              | (res,st) => (res,empty_locals st)
               (* (case caltyp of
                    | Tail => (res,st)
                    | _  => (res,st with locals := s.locals)) *) )
         | _ => (SOME Error,s))
    | (_, _) => (SOME Error,s)) /\
  (evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
   case (FLOOKUP s.locals len1, FLOOKUP s.locals ptr1, FLOOKUP s.locals len2, FLOOKUP s.locals ptr2) of
    | SOME (ValWord w),SOME (ValWord w2),SOME (ValWord w3),SOME (ValWord w4) =>
       (case (read_bytearray w2 (w2n w) (mem_load_byte s.memory s.memaddrs s.be),
              read_bytearray w4 (w2n w3) (mem_load_byte s.memory s.memaddrs s.be)) of
         | SOME bytes,SOME bytes2 =>
            (case call_FFI s.ffi (explode ffi_index) bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
              | FFI_return new_ffi new_bytes =>
                (case write_bytearray w4 new_bytes s.memory s.memaddrs s.be of
                  | SOME m => (NONE, s with <| memory := m;ffi := new_ffi |>)
                  | NONE => (SOME Error,s)))
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
  recInduct evaluate_ind >> REPEAT STRIP_TAC >>
  POP_ASSUM MP_TAC >> ONCE_REWRITE_TAC [evaluate_def] >>
  rw [] >> every_case_tac >>
  fs [set_var_def, upd_locals_def, empty_locals_def, dec_clock_def, LET_THM] >>
  rveq >> fs [] >>
  rpt (pairarg_tac >> fs []) >>
  every_case_tac >> fs [] >> rveq >>
  imp_res_tac fix_clock_IMP_LESS_EQ >>
  imp_res_tac LESS_EQ_TRANS >> fs [] >> rfs []
QED

Theorem fix_clock_evaluate:
  fix_clock s (evaluate (prog,s)) = evaluate (prog,s)
Proof
  Cases_on `evaluate (prog,s)` >> fs [fix_clock_def] >>
  imp_res_tac evaluate_clock >>
  fs [GSYM NOT_LESS, state_component_equality]
QED

(* we save evaluate theroems without fix_clock *)
val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
