(*
  The formal semantics of closLang
*)
Theory closSem
Ancestors
  backend_common closLang flatLang
  semanticPrimitivesProps (* for opw_lookup_def and others *)
Libs
  preamble

(* differs from store_v by removing the single value Refv,
   also, adds flag to ByteArray for equality semantics *)
Datatype:
  ref = ValueArray ('a list)
      | ByteArray (word8 list)
      | Thunk thunk_mode 'a
End

(* --- Semantics of ClosLang --- *)

Datatype:
  v =
    Number int
  | Word64 word64
  | Block num (v list)
  | ByteVector (word8 list)
  | RefPtr bool num
  | Closure (num option) (v list) (v list) num closLang$exp
  | Recclosure (num option) (v list) (v list) ((num # closLang$exp) list) num
End

Type clos_co = ``:num -> 'c # clos_prog``

Datatype:
  state =
    <| globals : (closSem$v option) list
     ; refs    : num |-> closSem$v ref
     ; ffi     : 'ffi ffi_state
     ; clock   : num
     ; compile : 'c clos_cc
     ; compile_oracle : 'c clos_co
     ; code    : num |-> (num # closLang$exp)
     ; max_app : num
    |>
End

(* helper functions *)

Definition get_global_def:
  get_global n globals =
    if n < LENGTH globals then SOME (EL n globals) else NONE
End

Definition Boolv_def:
  (Boolv b = Block (if b then true_tag else false_tag) [])
End

Definition do_eq_def:
  (do_eq x y =
     case x of
     | Number i =>
         (case y of
          | Number j => Eq_val (i = j)
          | _ => Eq_type_error)
     | Word64 v =>
         (case y of
          | Word64 w => Eq_val (v = w)
          | _ => Eq_type_error)
     | Block t1 xs =>
         (case y of
          | Block t2 ys => if (t1 = t2) /\ (LENGTH xs = LENGTH ys) then
                             do_eq_list xs ys
                           else Eq_val F
          | _ => Eq_type_error)
     | ByteVector cs =>
         (case y of
          | ByteVector ds => Eq_val (cs = ds)
          | _ => Eq_type_error)
     | RefPtr bi i =>
         (case y of
          | RefPtr bj j => (if bi ∧ bj then Eq_val (i = j) else Eq_type_error)
          | _ => Eq_type_error)
     | _ =>
         (case y of
          | Number _ => Eq_type_error
          | Word64 _ => Eq_type_error
          | Block _ _ => Eq_type_error
          | ByteVector _ => Eq_type_error
          | RefPtr _ _ => Eq_type_error
          | _ => Eq_val T)) /\
  (do_eq_list [] [] = Eq_val T) /\
  (do_eq_list (x::xs) (y::ys) =
     case do_eq x y of
     | Eq_val T => do_eq_list xs ys
     | res => res) /\
  (do_eq_list _ _ = Eq_val F)
End

Definition v_to_list_def:
  (v_to_list (Block tag []) =
     if tag = nil_tag then SOME [] else NONE) ∧
  (v_to_list (Block tag [h;bt]) =
     if tag = cons_tag then
       (case v_to_list bt of
        | SOME t => SOME (h::t)
        | _ => NONE )
     else NONE) ∧
  (v_to_list _ = NONE)
End

Definition list_to_v_def:
  list_to_v [] = Block nil_tag [] /\
  list_to_v (x::xs) = Block cons_tag [x; list_to_v xs]
End

Definition Unit_def:
  Unit = Block tuple_tag []
End

Overload Error[local] =
  ``(Rerr(Rabort Rtype_error)):(closSem$v#(('c,'ffi) closSem$state), closSem$v)result``

Definition v_to_bytes_def:
  v_to_bytes lv = some ns:word8 list.
                    v_to_list lv = SOME (MAP (Number o $& o w2n) ns)
End

Definition v_to_words_def:
  v_to_words lv = some ns. v_to_list lv = SOME (MAP Word64 ns)
End

val s = ``s:('c,'ffi)closSem$state``;

Definition do_install_def:
  do_install vs ^s =
      (case vs of
       | [v1;v2] =>
           (case (v_to_bytes v1, v_to_words v2) of
            | (SOME bytes, SOME data) =>
               let (cfg,progs) = s.compile_oracle 0 in
               let new_oracle = shift_seq 1 s.compile_oracle in
                (if DISJOINT (FDOM s.code) (set (MAP FST (SND progs))) /\
                    ALL_DISTINCT (MAP FST (SND progs)) then
                 (case s.compile cfg progs, progs of
                  | SOME (bytes',data',cfg'), (exps,aux) =>
                      if bytes = bytes' ∧ data = data' ∧
                         FST(new_oracle 0) = cfg' ∧ exps <> [] then
                       (let s' =
                          s with <|
                             code := s.code |++ aux
                           ; compile_oracle := new_oracle
                           ; clock := s.clock - 1
                           |>
                        in
                          if s.clock = 0
                          then (Rerr(Rabort Rtimeout_error),s')
                          else (Rval exps, s'))
                      else ((Rerr(Rabort Rtype_error):(closLang$exp list,v)result),s)
                  | _ => (Rerr(Rabort Rtype_error),s))
                  else (Rerr(Rabort Rtype_error),s))
            | _ => (Rerr(Rabort Rtype_error),s))
       | _ => (Rerr(Rabort Rtype_error),s))
End

Definition make_const_def:
  make_const (ConstInt i) = Number i ∧
  make_const (ConstStr s) = ByteVector (MAP (n2w o ORD) (mlstring$explode s)) ∧
  make_const (ConstWord64 w) = Word64 w ∧
  make_const (ConstCons t cs) = Block t (MAP make_const cs)
Termination
  WF_REL_TAC ‘measure const_size’
  \\ Induct_on ‘cs’ \\ rw []
  \\ fs [const_size_def] \\ res_tac
  \\ pop_assum (qspec_then ‘t’ assume_tac) \\ fs []
End

Definition do_int_app_def:
  do_int_app (Const n) [] = SOME (Number n) /\
  do_int_app (Add) [Number n1;Number n2] = SOME (Number (n1 + n2)) /\
  do_int_app (Sub) [Number n1;Number n2] = SOME (Number (n1 - n2)) /\
  do_int_app (Mult) [Number n1;Number n2] = SOME (Number (n1 * n2)) /\
  do_int_app (Div) [Number n1;Number n2] =
      (if n2 = 0 then NONE else SOME (Number (n1 / n2))) /\
  do_int_app (Mod) [Number n1;Number n2] =
      (if n2 = 0 then NONE else SOME (Number (n1 % n2))) /\
  do_int_app (Less) [Number n1;Number n2] = SOME (Boolv (n1 < n2)) /\
  do_int_app (LessEq) [Number n1;Number n2] = SOME (Boolv (n1 <= n2)) /\
  do_int_app (Greater) [Number n1;Number n2] = SOME (Boolv (n1 > n2)) /\
  do_int_app (GreaterEq) [Number n1;Number n2] = SOME (Boolv (n1 >= n2)) /\
  do_int_app (LessConstSmall n) [Number i] =
        (if 0 <= i /\ i <= 1000000 /\ n < 1000000 then
          SOME (Boolv (i < &n)) else NONE) /\
  do_int_app (op:closLang$int_op) (vs:closSem$v list) = NONE
End

Definition opw_lookup_def[simp]:
  (opw_lookup Andw = word_and) ∧
  (opw_lookup Orw = word_or) ∧
  (opw_lookup Xor = word_xor) ∧
  (opw_lookup Add = word_add) ∧
  (opw_lookup Sub = word_sub)
End

Definition do_word_app_def:
  (do_word_app (WordOpw W8 opw) [Number n1; Number n2] =
       (case some (w1:word8,w2:word8). n1 = &(w2n w1) ∧ n2 = &(w2n w2) of
        | NONE => NONE
        | SOME (w1,w2) => SOME (Number &(w2n (opw_lookup opw w1 w2))))) /\
  do_word_app (WordOpw W64 opw) [Word64 w1; Word64 w2] =
        SOME (Word64 (opw_lookup opw w1 w2)) /\
  do_word_app (WordTest W8 test) [Number n1; Number n2] =
       (if 0 ≤ n1 ∧ n1 < 256 ∧ 0 ≤ n2 ∧ n2 < 256 then
          (case test of
           | Equal       => SOME (Boolv (n1 = n2))
           | Compare cmp => SOME (Boolv (int_cmp cmp n1 n2))
           | _           => NONE)
        else NONE) /\
  do_word_app (WordShift W8 sh n) [Number i] =
       (case some (w:word8). i = &(w2n w) of
        | NONE => NONE
        | SOME w => SOME (Number &(w2n (shift_lookup sh w n)))) /\
  do_word_app (WordShift W64 sh n) [Word64 w] =
       SOME (Word64 (shift_lookup sh w n)) /\
  do_word_app (WordFromInt) [Number i] =
       SOME (Word64 (i2w i)) /\
  do_word_app WordToInt [Word64 w] =
       SOME (Number (&(w2n w))) /\
  do_word_app (WordFromWord T) [Word64 w] =
       SOME (Number (&(w2n ((w2w:word64->word8) w)))) /\
  do_word_app (WordFromWord F) [Number n] =
       (case some (w:word8). n = &(w2n w) of
        | NONE => NONE
        | SOME w => SOME (Word64 (w2w w))) /\
  do_word_app (FP_top t_op) ws =
        (case ws of
         | [Word64 w1; Word64 w2; Word64 w3] =>
             (SOME (Word64 (fp_top_comp t_op w1 w2 w3)))
         | _ => NONE) /\
  do_word_app (FP_bop bop) ws =
        (case ws of
         | [Word64 w1; Word64 w2] => (SOME (Word64 (fp_bop_comp bop w1 w2)))
         | _ => NONE) /\
  do_word_app (FP_uop uop) ws =
        (case ws of
         | [Word64 w] => (SOME (Word64 (fp_uop_comp uop w)))
         | _ => NONE) /\
  do_word_app (FP_cmp cmp) ws =
        (case ws of
         | [Word64 w1; Word64 w2] => (SOME (Boolv (fp_cmp_comp cmp w1 w2)))
         | _ => NONE) /\
  do_word_app (op:closLang$word_op) (vs:closSem$v list) = NONE
End

Definition do_app_def:
  do_app (op:closLang$op) (vs:closSem$v list) ^s =
    case (op,vs) of
    | (GlobOp (Global n),[]:closSem$v list) =>
        (case get_global n s.globals of
         | SOME (SOME v) => (Rval (v,s))
         | _ => Error)
    | (GlobOp (Global _),[Number i]) =>
        (if i < 0 then Error else
         case get_global (Num i) s.globals of
         | SOME (SOME v) => (Rval (v,s))
         | _ => Error)
    | (GlobOp (SetGlobal n),[v]) =>
        (case get_global n s.globals of
         | SOME NONE => Rval (Unit,
             s with globals := (LUPDATE (SOME v) n s.globals))
         | _ => Error)
    | (GlobOp AllocGlobal,[Number i]) =>
        (if i < 0 then Error
         else Rval (Unit, s with globals := s.globals ++ REPLICATE (Num i) NONE))
    | (BlockOp (Constant c),[]) => Rval (make_const c, s)
    | (BlockOp (Cons tag),xs) => Rval (Block tag xs, s)
    | (BlockOp (ConsExtend tag), Block _ xs'::Number lower::Number len::Number tot::xs) =>
        if lower < 0 ∨ len < 0 ∨ &LENGTH xs' < lower + len ∨
           tot = 0 ∨ tot ≠ &LENGTH xs + len then
          Error
        else
          Rval (Block tag (xs++TAKE (Num len) (DROP (Num lower) xs')), s)
    | (BlockOp (ConsExtend tag),_) => Error
    | (MemOp El,[Block tag xs; Number i]) =>
        if 0 ≤ i ∧ Num i < LENGTH xs then Rval (EL (Num i) xs, s) else Error
    | (MemOp El,[RefPtr _ ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (EL (Num i) xs, s)
             else Error)
         | _ => Error)
    | (BlockOp (BoolTest test),[v1;v2]) =>
        (if (v1 ≠ Boolv T ∧ v1 ≠ Boolv F) then Error else
         if (v2 ≠ Boolv T ∧ v2 ≠ Boolv F) then Error else
           Rval (Boolv (v1 = v2), s))
    | (BlockOp BoolNot,[v1]) =>
        (if v1 = Boolv T then Rval (Boolv F, s) else
         if v1 = Boolv F then Rval (Boolv T, s) else Error)
    | (BlockOp (ElemAt n),[Block tag xs]) =>
        if n < LENGTH xs then Rval (EL n xs, s) else Error
    | (BlockOp ListAppend, [x1; x2]) =>
        (case (v_to_list x1, v_to_list x2) of
        | (SOME xs, SOME ys) => Rval (list_to_v (xs ++ ys), s)
        | _ => Error)
    | (BlockOp LengthBlock,[Block tag xs]) =>
        Rval (Number (&LENGTH xs), s)
    | (MemOp Length,[RefPtr _ ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ValueArray xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (MemOp LengthByte,[RefPtr _ ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ByteArray xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (MemOp (RefByte F),[Number i;Number b]) =>
         if 0 ≤ i ∧ (∃w:word8. b = & (w2n w)) then
           let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
             Rval (RefPtr T ptr, s with refs := s.refs |+
               (ptr,ByteArray (REPLICATE (Num i) (i2w b))))
         else Error
    | (MemOp RefArray,[Number i;v]) =>
        if 0 ≤ i then
          let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
            Rval (RefPtr T ptr, s with refs := s.refs |+
              (ptr,ValueArray (REPLICATE (Num i) v)))
         else Error
    | (MemOp DerefByte,[RefPtr _ ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray ws) =>
            (if 0 ≤ i ∧ i < &LENGTH ws
             then Rval (Number (& (w2n (EL (Num i) ws))),s)
             else Error)
         | _ => Error)
    | (MemOp UpdateByte,[RefPtr _ ptr; Number i; Number b]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ (∃w:word8. b = & (w2n w))
             then
               Rval (Unit, s with refs := s.refs |+
                 (ptr, ByteArray (LUPDATE (i2w b) (Num i) bs)))
             else Error)
         | _ => Error)
    | (MemOp ConcatByteVec,[lv]) =>
        (case (some wss. v_to_list lv = SOME (MAP ByteVector wss)) of
         | SOME wss => Rval (ByteVector (FLAT wss), s)
         | _ => Error)
    | (BlockOp (FromList n),[lv]) =>
        (case v_to_list lv of
         | SOME vs => Rval (Block n vs, s)
         | _ => Error)
    | (MemOp FromListByte,[lv]) =>
        (case some ns. v_to_list lv = SOME (MAP (Number o $&) ns) ∧ EVERY (λn. n < 256) ns of
         | SOME ns => Rval (ByteVector (MAP n2w ns), s)
         | NONE => Error)
    | (MemOp ToListByte,[ByteVector bs]) =>
        (Rval (list_to_v (MAP (\b. Number (& (w2n b))) bs), s))
    | (MemOp LengthByteVec,[ByteVector bs]) =>
        (Rval (Number (& LENGTH bs), s))
    | (MemOp DerefByteVec,[ByteVector bs; Number i]) =>
        (if 0 ≤ i ∧ i < &LENGTH bs then
           Rval (Number (&(w2n(EL (Num i) bs))), s)
         else Error)
    | (MemOp (CopyByte F),[ByteVector ws; Number srcoff; Number len; RefPtr _ dst; Number dstoff]) =>
        (case FLOOKUP s.refs dst of
         | SOME (ByteArray ds) =>
           (case copy_array (ws,srcoff) len (SOME(ds,dstoff)) of
            | SOME ds => Rval (Unit, s with refs := s.refs |+ (dst, ByteArray ds))
            | NONE => Error)
         | _ => Error)
    | (MemOp (CopyByte F),[RefPtr _ src; Number srcoff; Number len; RefPtr _ dst; Number dstoff]) =>
        (case (FLOOKUP s.refs src, FLOOKUP s.refs dst) of
         | (SOME (ByteArray ws), SOME (ByteArray ds)) =>
           (case copy_array (ws,srcoff) len (SOME(ds,dstoff)) of
            | SOME ds => Rval (Unit, s with refs := s.refs |+ (dst, ByteArray ds))
            | NONE => Error)
         | _ => Error)
    | (MemOp (CopyByte T),[ByteVector ws; Number srcoff; Number len]) =>
       (case copy_array (ws,srcoff) len NONE of
        | SOME ds => Rval (ByteVector ds, s)
        | _ => Error)
    | (MemOp (CopyByte T),[RefPtr _ src; Number srcoff; Number len]) =>
       (case FLOOKUP s.refs src of
        | SOME (ByteArray ws) =>
          (case copy_array (ws,srcoff) len NONE of
           | SOME ds => Rval (ByteVector ds, s)
           | _ => Error)
        | _ => Error)
    | (MemOp XorByte,[RefPtr _ dst; ByteVector ws]) =>
       (case FLOOKUP s.refs dst of
        | SOME (ByteArray ds) =>
          (case xor_bytes ws ds of
           | SOME ds1 => Rval (Unit, s with refs := s.refs |+ (dst, ByteArray ds1))
           | _ => Error)
        | _ => Error)
    | (BlockOp (TagEq n),[Block tag xs]) =>
        Rval (Boolv (tag = n), s)
    | (BlockOp (LenEq l),[Block tag xs]) =>
        Rval (Boolv (LENGTH xs = l),s)
    | (BlockOp (TagLenEq n l),[Block tag xs]) =>
        Rval (Boolv (tag = n ∧ LENGTH xs = l),s)
    | (BlockOp (EqualConst p),[x1]) =>
        (case p of
         | Int i => (case x1 of Number j => Rval (Boolv (i = j), s) | _ => Error)
         | W64 i => (case x1 of Word64 j => Rval (Boolv (i = j), s) | _ => Error)
         | Str i => (case x1 of
                     | ByteVector j => Rval (Boolv (j = MAP (n2w ∘ ORD) (explode i)), s)
                     | _ => Error)
         | _ => Error)
    | (BlockOp Equal,[x1;x2]) =>
        (case do_eq x1 x2 of
         | Eq_val b => Rval (Boolv b, s)
         | _ => Error)
    | (MemOp Ref,xs) =>
        let ptr = (LEAST ptr. ~(ptr IN FDOM s.refs)) in
          Rval (RefPtr T ptr, s with refs := s.refs |+ (ptr,ValueArray xs))
    | (MemOp Update,[RefPtr _ ptr; Number i; x]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (Unit, s with refs := s.refs |+
                              (ptr,ValueArray (LUPDATE x (Num i) xs)))
             else Error)
         | _ => Error)
    | (IntOp int_op, vs) =>
        (case do_int_app int_op vs of
        | SOME res => Rval (res ,s)
        | _ => Error)
    | (WordOp word_op, vs) =>
        (case do_word_app word_op vs of
        | SOME res => Rval (res ,s)
        | _ => Error)
    | (FFI n, [ByteVector conf; RefPtr _ ptr]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray ws) =>
           (case call_FFI s.ffi (ExtCall n) conf ws of
            | FFI_return ffi' ws' =>
                Rval (Unit,
                      s with <| refs := s.refs |+ (ptr,ByteArray ws')
                              ; ffi   := ffi'|>)
            | FFI_final outcome =>
                Rerr (Rabort (Rffi_error outcome)))
         | _ => Error)
    | (BlockOp BoundsCheckBlock,[Block tag ys; Number i]) =>
        Rval (Boolv (0 <= i /\ i < & LENGTH ys),s)
    | (MemOp (BoundsCheckByte loose),[ByteVector bs; Number i]) =>
        Rval (Boolv (0 <= i /\ (if loose then $<= else $<) i (& LENGTH bs)),s)
    | (MemOp (BoundsCheckByte loose),[RefPtr _ ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray ws) =>
             Rval (Boolv (0 <= i /\ (if loose then $<= else $<) i (& LENGTH ws)),s)
         | _ => Error)
    | (MemOp BoundsCheckArray,[RefPtr _ ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray ws) =>
             Rval (Boolv (0 <= i /\ i < & LENGTH ws),s)
         | _ => Error)
    | (MemOp ConfigGC,[Number _; Number _]) => (Rval (Unit, s))
    | (ThunkOp th_op, vs) =>
        (case (th_op,vs) of
         | (AllocThunk m, [v]) =>
             (let ptr = (LEAST ptr. ~(ptr IN FDOM s.refs)) in
                Rval (RefPtr F ptr, s with refs := s.refs |+ (ptr,Thunk m v)))
         | (UpdateThunk m, [RefPtr _ ptr; v]) =>
             (case FLOOKUP s.refs ptr of
              | SOME (Thunk NotEvaluated _) =>
                 Rval (Unit, s with refs := s.refs |+ (ptr,Thunk m v))
              | _ => Error)
         | _ => Error)
    | _ => Error
End

Definition dec_clock_def:
  dec_clock n ^s = s with clock := s.clock - n
End

Theorem LESS_EQ_dec_clock[local]:
  (r:('c,'ffi) closSem$state).clock <= (dec_clock n s).clock ==> r.clock <= s.clock
Proof
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC
QED

Definition find_code_def:
  find_code p args code =
    case FLOOKUP code p of
    | NONE => NONE
    | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp)
                                                 else NONE
End

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

(* Proving termination of the evaluator directly is tricky. We make
   our life simpler by forcing the clock to stay good using
   fix_clock. At the bottom of this file, we remove all occurrences
   of fix_clock. *)

Definition fix_clock_def:
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)
End

Theorem fix_clock_IMP[local]:
  fix_clock s x = (res,s1) ==> s1.clock <= s.clock
Proof
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []
QED

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of clos_exp expressions. *)

Definition check_loc_def:
  (check_loc (max_app:num) NONE loc num_params num_args so_far ⇔
    num_args ≤ max_app) /\
  (check_loc max_app (SOME p) loc num_params num_args so_far ⇔
    num_params = num_args ∧ so_far = (0:num) ∧ SOME p = loc)
End

Datatype:
  app_kind =
    | Partial_app closSem$v
    | Full_app closLang$exp (closSem$v list) (closSem$v list)
End

Definition dest_closure_def:
  dest_closure max_app loc_opt f args =
    case f of
    | Closure loc arg_env clo_env num_args exp =>
        if check_loc max_app loc_opt loc num_args (LENGTH args) (LENGTH arg_env) ∧ LENGTH arg_env < num_args then
          if ¬(LENGTH args + LENGTH arg_env < num_args) then
            SOME (Full_app exp
                           (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE args))++
                            arg_env++clo_env)
                           (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
          else
            SOME (Partial_app (Closure loc (args++arg_env) clo_env num_args exp))
        else
          NONE
    | Recclosure loc arg_env clo_env fns i =>
        let (num_args,exp) = EL i fns in
          if LENGTH fns <= i \/
             ~check_loc max_app
                        loc_opt
                        (OPTION_MAP ((+) (2*i)) loc) num_args
                        (LENGTH args)
                        (LENGTH arg_env) ∨
             ¬(LENGTH arg_env < num_args)
          then NONE
          else
            let rs = GENLIST (Recclosure loc [] clo_env fns) (LENGTH fns) in
              if ¬(LENGTH args + LENGTH arg_env < num_args) then
                SOME (Full_app exp
                               (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE args))++
                                arg_env++rs++clo_env)
                               (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
              else
                SOME (Partial_app (Recclosure loc (args++arg_env) clo_env fns i))
    | _ => NONE
End

Theorem dest_closure_length:
  ∀max_app loc_opt f args exp args1 args2 so_far.
    dest_closure max_app loc_opt f args = SOME (Full_app exp args1 args2)
    ⇒
    LENGTH args2 < LENGTH args
Proof
  rw [dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  rw [] >>
  TRY decide_tac >>
  Cases_on `EL n l1` >>
  fs [LET_THM] >>
  Cases_on `LENGTH args + LENGTH l < q` >>
  fs [] >>
  rw [] >>
  decide_tac
QED

Definition clos_env_def:
  clos_env restrict names env =
    if restrict then lookup_vars names env else SOME env
End

Definition build_recc_def:
  build_recc restrict loc env names fns =
    case clos_env restrict names env of
    | SOME env1 => SOME (GENLIST (Recclosure loc [] env1 fns) (LENGTH fns))
    | NONE => NONE
End

Theorem case_eq_thms = LIST_CONJ (
  CaseEq"const_part" ::
  closLangTheory.op_case_eq ::
  closLangTheory.int_op_case_eq ::
  closLangTheory.word_op_case_eq ::
  closLangTheory.block_op_case_eq ::
  closLangTheory.glob_op_case_eq ::
  closLangTheory.mem_op_case_eq ::
  astTheory.thunk_op_case_eq :: map CaseEq
  ["list","option","v","ref",
   "result","error_result","eq_result","app_kind","word_size"]);

Theorem do_install_clock:
   do_install vs s = (Rval e,s') ⇒ 0 < s.clock ∧ s'.clock = s.clock-1
Proof
  rw[do_install_def,case_eq_thms]
  \\ pairarg_tac \\ gvs[case_eq_thms,pair_case_eq,bool_case_eq]
QED

Theorem do_install_clock_less_eq:
   do_install vs s = (res,s') ⇒ s'.clock <= s.clock
Proof
  rw[do_install_def,case_eq_thms] \\ fs []
  \\ pairarg_tac \\ gvs[case_eq_thms,pair_case_eq,bool_case_eq]
QED

Datatype:
  dest_thunk_ret
    = BadRef
    | NotThunk
    | IsThunk thunk_mode v
End

Definition dest_thunk_def:
  dest_thunk [RefPtr _ ptr] refs =
    (case FLOOKUP refs ptr of
     | NONE => BadRef
     | SOME (Thunk Evaluated v) => IsThunk Evaluated v
     | SOME (Thunk NotEvaluated v) => IsThunk NotEvaluated v
     | SOME _ => NotThunk) ∧
  dest_thunk vs refs = NotThunk
End

Definition store_thunk_def:
  store_thunk ptr v refs =
    case FLOOKUP refs ptr of
    | SOME (Thunk NotEvaluated _) => SOME (refs |+ (ptr,v))
    | _ => NONE
End

Definition update_thunk_def:
  update_thunk [RefPtr _ ptr] refs [v] =
    (case dest_thunk [v] refs of
     | NotThunk => store_thunk ptr (Thunk Evaluated v) refs
     | _ => NONE) ∧
  update_thunk _ _ _ = NONE
End

Definition AppUnit_def:
  AppUnit x = closLang$App None NONE x [Op None (BlockOp (Cons 0)) []]
End

Definition exp_alt_size_def[simp]:
  exp_alt_size (Var a0 a1) = 1 + (tra_size a0 + a1) ∧
  exp_alt_size (If a0 a1 a2 a3) =
  1 + (tra_size a0 + (exp_alt_size a1 + (exp_alt_size a2 + exp_alt_size a3))) ∧
  exp_alt_size (Let a0 a1 a2) =
  1 + (tra_size a0 + (exp3_alt_size a1 + exp_alt_size a2)) ∧
  exp_alt_size (Raise a0 a1) = 1 + (tra_size a0 + exp_alt_size a1) ∧
  exp_alt_size (Handle a0 a1 a2) =
  1 + (tra_size a0 + (exp_alt_size a1 + exp_alt_size a2)) ∧
  exp_alt_size (Tick a0 a1) = 1 + (tra_size a0 + exp_alt_size a1) ∧
  exp_alt_size (Call a0 a1 a2 a3) =
  1 + (tra_size a0 + (a1 + (a2 + exp3_alt_size a3))) ∧
  exp_alt_size (App a0 a1 a2 a3) =
  1 +
  (tra_size a0 + (option_size (λx. x) a1 + (exp_alt_size a2 + exp3_alt_size a3))) ∧
  exp_alt_size (Fn a0 a1 a2 a3 a4) =
  1 +
  (mlstring_size a0 +
   (option_size (λx. x) a1 +
    (option_size (list_size (λx. x)) a2 + (a3 + exp_alt_size a4)))) ∧
  exp_alt_size (Letrec a0 a1 a2 a3 a4) =
  1 +
  (list_size mlstring_size a0 +
   (option_size (λx. x) a1 +
    (option_size (list_size (λx. x)) a2 + (exp1_alt_size a3 + exp_alt_size a4)))) ∧
  exp_alt_size (Op a0 a1 a2) = 1 + (tra_size a0 + (op_size a1 + exp3_alt_size a2))
    + (if a1 = ThunkOp ForceThunk then 100 else 0) ∧
  exp1_alt_size [] = 0 ∧
  exp1_alt_size (a0::a1) = 1 + (exp2_alt_size a0 + exp1_alt_size a1) ∧
  exp2_alt_size (a0,a1) = 1 + (a0 + exp_alt_size a1) ∧ exp3_alt_size [] = 0 ∧
  exp3_alt_size (a0::a1) = 1 + (exp_alt_size a0 + exp3_alt_size a1)
End

Theorem exp3_alt_size[local,simp]:
  exp3_alt_size xs = list_size exp_alt_size xs
Proof
  Induct_on `xs` \\ simp []
QED

Definition evaluate_def[nocompute]:
  (evaluate ([],env:closSem$v list,^s) = (Rval [],s)) /\
  (evaluate (x::y::xs,env,s) =
     case fix_clock s (evaluate ([x],env,s)) of
     | (Rval v1,s1) =>
         (case evaluate (y::xs,env,s1) of
          | (Rval vs,s2) => (Rval (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (evaluate ([Var _ n],env,s) =
     if n < LENGTH env then (Rval [EL n env],s) else (Rerr(Rabort Rtype_error),s)) /\
  (evaluate ([If _ x1 x2 x3],env,s) =
     case fix_clock s (evaluate ([x1],env,s)) of
     | (Rval vs,s1) =>
          if Boolv T = HD vs then evaluate ([x2],env,s1) else
          if Boolv F = HD vs then evaluate ([x3],env,s1) else
            (Rerr(Rabort Rtype_error),s1)
     | res => res) /\
  (evaluate ([Let _ xs x2],env,s) =
     case fix_clock s (evaluate (xs,env,s)) of
     | (Rval vs,s1) => evaluate ([x2],vs++env,s1)
     | res => res) /\
  (evaluate ([Raise _ x1],env,s) =
     case evaluate ([x1],env,s) of
     | (Rval vs,s) => (Rerr(Rraise (HD vs)),s)
     | res => res) /\
  (evaluate ([Handle _ x1 x2],env,s1) =
     case fix_clock s1 (evaluate ([x1],env,s1)) of
     | (Rerr(Rraise v),s) => evaluate ([x2],v::env,s)
     | res => res) /\
  (evaluate ([Op _ op xs],env,s) =
     case fix_clock s (evaluate (xs,env,s)) of
     | (Rval vs,s) =>
       if op = Install then
       (case do_install (REVERSE vs) s of
        | (Rval es,s) =>
            (case evaluate (es,[],s) of
             | (Rval vs,s) => (Rval [LAST vs],s)
             | res => res)
        | (Rerr err,s) => (Rerr err,s))
       else if op = ThunkOp ForceThunk then
         (case dest_thunk vs s.refs of
          | BadRef => (Rerr (Rabort Rtype_error),s)
          | NotThunk => (Rerr (Rabort Rtype_error),s)
          | IsThunk Evaluated v => (Rval [v],s)
          | IsThunk NotEvaluated f =>
             (case evaluate ([AppUnit (Var None 0)],[f],s) of
              | (Rval vs2,s) =>
                 (case update_thunk vs s.refs vs2 of
                  | NONE => (Rerr (Rabort Rtype_error),s)
                  | SOME refs => (Rval vs2,s with refs := refs))
              | (Rerr e,s) => (Rerr e,s)))
       else
       (case do_app op (REVERSE vs) s of
        | Rerr err => (Rerr err,s)
        | Rval (v,s) => (Rval [v],s))
     | res => res) /\
  (evaluate ([Fn _ loc vsopt num_args exp],env,s) =
     if num_args ≤ s.max_app ∧ num_args ≠ 0 then
       case vsopt of
         | NONE => (Rval [Closure loc [] env num_args exp], s)
         | SOME vs =>
           (case lookup_vars vs env of
              | NONE => (Rerr(Rabort Rtype_error),s)
              | SOME env' => (Rval [Closure loc [] env' num_args exp], s))
     else
       (Rerr(Rabort Rtype_error), s)) /\
  (evaluate ([Letrec _ loc namesopt fns exp],env,s) =
     if EVERY (\(num_args,e). num_args ≤ s.max_app ∧ num_args ≠ 0) fns then
       let
         build_rc e = GENLIST (Recclosure loc [] e fns) (LENGTH fns) in
       let
         envdelta =
           case namesopt of
           | NONE => SOME (build_rc env)
           | SOME names => OPTION_MAP build_rc (lookup_vars names env)
       in
         case envdelta of
             NONE => (Rerr(Rabort Rtype_error),s)
           | SOME ed => evaluate ([exp],ed ++ env,s)
     else
       (Rerr(Rabort Rtype_error), s)) /\
  (evaluate ([App _ loc_opt x1 args],env,s) =
     if LENGTH args > 0 then
       (case fix_clock s (evaluate (args,env,s)) of
        | (Rval y2,s1) =>
          (case fix_clock s1 (evaluate ([x1],env,s1)) of
           | (Rval y1,s2) => evaluate_app loc_opt (HD y1) y2 s2
           | res => res)
        | res => res)
     else
       (Rerr(Rabort Rtype_error), s)) /\
  (evaluate ([Tick _ x],env,s) =
     if s.clock = 0 then (Rerr(Rabort Rtimeout_error),s) else evaluate ([x],env,dec_clock 1 s)) /\
  (evaluate ([Call _ ticks dest xs],env,s1) =
     case fix_clock s1 (evaluate (xs,env,s1)) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if (s.clock < ticks+1) then (Rerr(Rabort Rtimeout_error),s with clock := 0) else
                  evaluate ([exp],args,dec_clock (ticks+1) s))
     | res => res) ∧
  (evaluate_app loc_opt f [] s = (Rval [f], s)) ∧
  (evaluate_app loc_opt f args s =
     case dest_closure s.max_app loc_opt f args of
     | NONE => (Rerr(Rabort Rtype_error),s)
     | SOME (Partial_app v) =>
         if s.clock < LENGTH args
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else (Rval [v], dec_clock (LENGTH args) s)
     | SOME (Full_app exp env rest_args) =>
         if s.clock < (LENGTH args - LENGTH rest_args)
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else
             case fix_clock (dec_clock (LENGTH args - LENGTH rest_args) s)
                    (evaluate ([exp],env,dec_clock (LENGTH args - LENGTH rest_args) s)) of
           | (Rval [v], s1) =>
               evaluate_app loc_opt v rest_args s1
           | res => res)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure I LEX measure I)
                (\x. case x of INL (xs,env,s) => (s.clock,list_size exp_alt_size xs,0)
                             | INR (l,f,args,s) => (s.clock,0,LENGTH args)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ imp_res_tac fix_clock_IMP
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ TRY DECIDE_TAC
  \\ imp_res_tac do_install_clock
  \\ imp_res_tac dest_closure_length
  \\ imp_res_tac LESS_EQ_dec_clock
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ simp [AppUnit_def]
  \\ IF_CASES_TAC \\ gvs []
End

Theorem evaluate_app_NIL[simp] =
  ``evaluate_app loc v [] s`` |> SIMP_CONV (srw_ss()) [evaluate_def]

(* We prove that the clock never increases. *)

Theorem do_app_const:
   (do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock) /\
    (s2.max_app = s1.max_app) /\
    (s2.code = s1.code) /\
    (s2.compile_oracle = s1.compile_oracle) /\
    (s2.compile = s1.compile)
Proof
  simp[do_app_def,case_eq_thms]
  \\ strip_tac \\ fs[] \\ rveq \\ fs[]
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
QED

Theorem evaluate_clock_help[local]:
  (!tup vs (s2:('c,'ffi) closSem$state).
      (evaluate tup = (vs,s2)) ==> s2.clock <= (SND (SND tup)).clock) ∧
    (!loc_opt f args (s1:('c,'ffi) closSem$state) vs s2.
      (evaluate_app loc_opt f args s1 = (vs,s2)) ==> s2.clock <= s1.clock)
Proof
  ho_match_mp_tac evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [LET_THM] \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ RES_TAC \\ IMP_RES_TAC fix_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC fix_clock_IMP
  \\ IMP_RES_TAC do_app_const
  \\ IMP_RES_TAC do_install_clock_less_eq
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
QED

Theorem evaluate_clock:
 (!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock) ∧
    (!loc_opt f args s1 vs s2.
      (evaluate_app loc_opt f args s1 = (vs,s2)) ==> s2.clock <= s1.clock)
Proof
  metis_tac [evaluate_clock_help, SND]
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate (xs,env,s)) = evaluate (xs,env,s)
Proof
  Cases_on `evaluate (xs,env,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]
QED

(* Finally, we remove fix_clock from the induction and definition theorems. *)

Theorem evaluate_def[compute,allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_def;

Theorem evaluate_ind[allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind;

(* observational semantics *)

Definition initial_state_def:
  initial_state ffi ma code co cc k = <|
    max_app := ma;
    clock := k;
    ffi := ffi;
    code := code;
    compile := cc;
    compile_oracle := co;
    globals := [];
    refs := FEMPTY
  |>
End

Definition semantics_def:
  semantics ffi ma code co cc es =
    let st = initial_state ffi ma code co cc in
      if ∃k. FST (evaluate (es,[],st k)) = Rerr (Rabort Rtype_error)
        then Fail
      else
      case some res.
        ∃k r s outcome.
          evaluate (es,[],st k) = (r,s) ∧
          (case r of
           | Rerr (Rabort Rtimeout_error) => F
           | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
           | _ => outcome = Success) ∧
          res = Terminate outcome s.ffi.io_events
      of SOME res => res
       | NONE =>
         Diverge
           (build_lprefix_lub
             (IMAGE (λk. fromList
                (SND (evaluate (es,[],st k))).ffi.io_events) UNIV))
End
