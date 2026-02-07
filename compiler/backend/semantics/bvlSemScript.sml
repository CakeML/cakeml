(*
  The formal semantics of BVL
*)
Theory bvlSem
Ancestors
  bvl closSem
  clos_to_bvl (* for closure_tag and num_added_globals *)
  backendProps[qualified]
Libs
  preamble

val _ = Parse.hide "str";

(* --- Semantics of BVL --- *)

Datatype:
  ref = ValueArray ('a list)
      | ByteArray bool (word8 list)
               (* T = compare-by-contents, immutable
                  F = compare-by-pointer, mutable *)
               (* in closLang all are ByteArray F,
                  ByteArray T introduced in BVL to implement ByteVector *)
      | Thunk thunk_mode 'a
End

(* these parts are shared by bytecode and, if bytecode is to be supported, need
   to move to a common ancestor *)

Datatype:
  v =
    Number int          (* integer *)
  | Word64 word64       (* 64-bit word *)
  | Block num (v list)  (* cons block: tag and payload *)
  | CodePtr num         (* code pointer *)
  | RefPtr bool num     (* pointer to ref cell, bool is T if Eq test is allows *)
End

Definition Boolv_def:
  Boolv b = bvlSem$Block (bool_to_tag b) []
End

Definition Unit_def:
  Unit = bvlSem$Block (tuple_tag) []
End

(* -- *)

Datatype:
  state =
    <| globals : (bvlSem$v option) list
     ; refs    : num |-> bvlSem$v ref
     ; clock   : num
     ; compile : 'c -> (num # num # bvl$exp) list -> (word8 list # word64 list # 'c) option
     ; compile_oracle : num -> 'c # (num # num # bvl$exp) list
     ; code    : (num # bvl$exp) num_map
     ; ffi     : 'ffi ffi_state |>
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
  list_to_v (v::vs) = Block cons_tag [v; list_to_v vs]
End

Definition isClos_def:
  isClos t1 l1 = (((t1 = closure_tag) \/ (t1 = partial_app_tag)) /\ l1 <> [])
End

Definition do_eq_def[simp]:
  (do_eq _ (CodePtr _) _ = Eq_type_error) ∧
  (do_eq _ _ (CodePtr _) = Eq_type_error) ∧
  (do_eq _ (Number n1) (Number n2) = (Eq_val (n1 = n2))) ∧
  (do_eq _ (Number _) _ = Eq_type_error) ∧
  (do_eq _ _ (Number _) = Eq_type_error) ∧
  (do_eq _ (Word64 w1) (Word64 w2) = (Eq_val (w1 = w2))) ∧
  (do_eq _ (Word64 _) _ = Eq_type_error) ∧
  (do_eq _ _ (Word64 _) = Eq_type_error) ∧
  (do_eq refs (RefPtr b1 n1) (RefPtr b2 n2) =
    if b1 ∧ b2 then
     (case (FLOOKUP refs n1, FLOOKUP refs n2) of
        (SOME (ByteArray T bs1), SOME (ByteArray T bs2))
          => Eq_val (bs1 = bs2)
      | (SOME (ByteArray T bs1), _) => Eq_type_error
      | (_, SOME (ByteArray T bs2)) => Eq_type_error
      | _ => Eq_val (n1 = n2))
    else Eq_type_error) ∧
  (do_eq _ (RefPtr _ _) _ = Eq_type_error) ∧
  (do_eq _ _ (RefPtr _ _) = Eq_type_error) ∧
  (do_eq refs (Block t1 l1) (Block t2 l2) =
   if isClos t1 l1 \/ isClos t2 l2
   then if isClos t1 l1 /\ isClos t2 l2 then Eq_val T else Eq_type_error
   else if (t1 = t2) ∧ (LENGTH l1 = LENGTH l2)
        then do_eq_list refs l1 l2
        else Eq_val F) ∧
  (do_eq_list _ [] [] = Eq_val T) ∧
  (do_eq_list refs (v1::vs1) (v2::vs2) =
   case do_eq refs v1 v2 of
   | Eq_val T => do_eq_list refs vs1 vs2
   | Eq_val F => Eq_val F
   | bad => bad) ∧
  (do_eq_list _ _ _ = Eq_val F)
End

Overload Error[local] = ``(Rerr(Rabort Rtype_error)):(bvlSem$v#('c,'ffi) bvlSem$state, bvlSem$v)result``

Definition v_to_bytes_def:
  v_to_bytes lv = some ns:word8 list.
                    v_to_list lv = SOME (MAP (Number o $& o w2n) ns)
End

Definition v_to_words_def:
  v_to_words lv = some ns. v_to_list lv = SOME (MAP Word64 ns)
End

val s = ``(s:('c,'ffi) bvlSem$state)``

Definition do_install_def:
  do_install vs ^s =
      (case vs of
       | [v1;v2] =>
           (case (v_to_bytes v1, v_to_words v2) of
            | (SOME bytes, SOME data) =>
               let (cfg,progs) = s.compile_oracle 0 in
               let new_oracle = shift_seq 1 s.compile_oracle in
                (if DISJOINT (domain s.code) (set (MAP FST progs)) /\
                    ALL_DISTINCT (MAP FST progs) then
                 (case s.compile cfg progs, progs of
                  | SOME (bytes',data',cfg'), (k,prog)::_ =>
                      if bytes = bytes' ∧ data = data' ∧ FST(new_oracle 0) = cfg' then
                        let s' =
                          s with <|
                             code := union s.code (fromAList progs)
                           ; compile_oracle := new_oracle |>
                        in
                          Rval (CodePtr k, s')
                      else Rerr(Rabort Rtype_error)
                  | _ => Rerr(Rabort Rtype_error))
                  else Rerr(Rabort Rtype_error))
            | _ => Rerr(Rabort Rtype_error))
       | _ => Rerr(Rabort Rtype_error))
End

Definition do_part_def:
  do_part m (Int i) refs = (Number i, refs) ∧
  do_part m (W64 w) refs = (Word64 w, refs) ∧
  do_part m (Con t ns) refs = (Block t (MAP m ns), refs) ∧
  do_part m (Str t) refs =
    let ptr = (LEAST ptr. ¬(ptr IN FDOM refs)) in
    let bytes = MAP (n2w o ORD) (mlstring$explode t) in
      (RefPtr T ptr, refs |+ (ptr,(ByteArray T bytes):v ref))
End

Definition do_build_def:
  do_build m i [] refs = (m (i-1), refs) ∧
  do_build m i (p::rest) refs =
    let (x,refs1) = do_part m p refs in
      do_build ((i =+ x) m) (i+1) rest refs1
End

Definition do_build_const_def:
  do_build_const xs refs = do_build (λx. Number 0) 0 xs refs
End
(* same as closSem$do_int_app *)
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
  do_int_app (op:closLang$int_op) (vs:bvlSem$v list) = NONE
End

(* same as closSem$do_word_app *)
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
  do_word_app (op:closLang$word_op) (vs:bvlSem$v list) = NONE
End

(* same as closSem$do_app, except:
    - LengthByteVec and DerefByteVec are removed
    - FromListByte, ToListByte, String, ConcatByteVec, and
      CopyByte work on ByteArrays rather than ByteVectors
    - Build now has full semantics, i.e. can handle all cases
    - Label is added *)

Definition do_app_def:
  do_app op vs ^s =
    case (op,vs) of
    | (GlobOp (Global n),[]) =>
        (case get_global n s.globals of
         | SOME (SOME v) => Rval (v,s)
         | _ => Error)
    | (GlobOp (Global _),[Number i]) =>
        (if i < 0 then Error else
         case get_global (Num i + num_added_globals) s.globals of
         | SOME (SOME v) => Rval (v,s)
         | _ => Error)
    | (GlobOp (SetGlobal n),[v]) =>
        (case get_global n s.globals of
         | SOME _ => Rval (Unit,
             s with globals := (LUPDATE (SOME v) n s.globals))
         | _ => Error)
    | (GlobOp AllocGlobal,[Number i]) =>
        (if i < 0 then Error
         else Rval (Unit, s with globals := s.globals ++ REPLICATE (Num i) NONE))
    | (Install,vs) => do_install vs s
    | (BlockOp (Cons tag),xs) => Rval (Block tag xs, s)
    | (BlockOp (BoolTest test),[v1;v2]) =>
        (if (v1 ≠ Boolv T ∧ v1 ≠ Boolv F) then Error else
         if (v2 ≠ Boolv T ∧ v2 ≠ Boolv F) then Error else
           Rval (Boolv (v1 = v2), s))
    | (BlockOp BoolNot,[v1]) =>
        (if v1 = Boolv T then Rval (Boolv F, s) else
         if v1 = Boolv F then Rval (Boolv T, s) else Error)
    | (BlockOp (Build parts),[]) =>
        (let (v,rs) = do_build_const parts s.refs in Rval (v, s with refs := rs))
    | (BlockOp (ConsExtend tag),Block _ xs'::Number lower::Number len::Number tot::xs) =>
        if lower < 0 ∨ len < 0 ∨ lower + len > &LENGTH xs' ∨
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
    | (BlockOp (ElemAt n),[Block tag xs]) =>
        if n < LENGTH xs then Rval (EL n xs, s) else Error
    | (BlockOp (ElemAt n),[RefPtr _ ptr]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if n < LENGTH xs
             then Rval (EL n xs, s)
             else Error)
         | _ => Error)
    | (BlockOp ListAppend,[x1;x2]) =>
        (case (v_to_list x1, v_to_list x2) of
         | (SOME xs, SOME ys) => Rval (list_to_v (xs ++ ys),s)
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
          | SOME (ByteArray _ xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (MemOp (RefByte F),[Number i;Number b]) =>
         if 0 ≤ i ∧ (∃w:word8. b = & (w2n w)) then
           let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
             Rval (RefPtr T ptr, s with refs := s.refs |+
               (ptr,ByteArray F (REPLICATE (Num i) (i2w b))))
         else Error
    | (MemOp RefArray,[Number i;v]) =>
        if 0 ≤ i then
          let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
            Rval (RefPtr T ptr, s with refs := s.refs |+
              (ptr,ValueArray (REPLICATE (Num i) v)))
         else Error
    | (MemOp DerefByte,[RefPtr _ ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray _ ws) =>
            (if 0 ≤ i ∧ i < &LENGTH ws
             then Rval (Number (& (w2n (EL (Num i) ws))),s)
             else Error)
         | _ => Error)
    | (MemOp UpdateByte,[RefPtr _ ptr; Number i; Number b]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray f bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ (∃w:word8. b = & (w2n w))
             then
               Rval (Unit, s with refs := s.refs |+
                 (ptr, ByteArray f (LUPDATE (i2w b) (Num i) bs)))
             else Error)
         | _ => Error)
    | (MemOp ConcatByteVec,[lv]) =>
         (case
            (some wss. ∃ps.
              v_to_list lv = SOME (MAP (RefPtr T) ps) ∧
              MAP (FLOOKUP s.refs) ps = MAP (SOME o ByteArray T) wss)
          of SOME wss =>
            let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
              Rval (RefPtr T ptr, s with refs := s.refs |+
                       (ptr,ByteArray T (FLAT wss)))
          | _ => Error)
    | (BlockOp (FromList n),[lv]) =>
        (case v_to_list lv of
         | SOME vs => Rval (Block n vs, s)
         | _ => Error)
    | (MemOp FromListByte,[lv]) =>
        (case some ns. v_to_list lv = SOME (MAP (Number o $&) ns) ∧ EVERY (λn. n < 256) ns of
          | SOME ns => let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
                         Rval (RefPtr T ptr, s with refs := s.refs |+
                           (ptr,ByteArray T (MAP n2w ns)))
          | NONE => Error)
    | (MemOp ToListByte,[RefPtr _ ptr]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray f bs) =>
            (Rval (list_to_v (MAP (\b. Number (& (w2n b))) bs), s))
         | _ => Error)
    | (MemOp (CopyByte F),[RefPtr _ src; Number srcoff; Number len; RefPtr _ dst; Number dstoff]) =>
        (case (FLOOKUP s.refs src, FLOOKUP s.refs dst) of
         | (SOME (ByteArray _ ws), SOME (ByteArray fl ds)) =>
           (case copy_array (ws,srcoff) len (SOME(ds,dstoff)) of
            | SOME ds => Rval (Unit, s with refs := s.refs |+ (dst, ByteArray fl ds))
            | NONE => Error)
         | _ => Error)
    | (MemOp (CopyByte T),[RefPtr _ src; Number srcoff; Number len]) =>
       (case (FLOOKUP s.refs src) of
        | SOME (ByteArray _ ws) =>
           (case copy_array (ws,srcoff) len NONE of
            | SOME ds =>
              let ptr = (LEAST ptr. ~(ptr IN FDOM s.refs)) in
              Rval (RefPtr T ptr, s with
                    refs := s.refs |+ (ptr, ByteArray T ds))
            | _ => Error)
        | _ => Error)
    | (MemOp XorByte,[RefPtr _ dst; RefPtr _ src]) =>
        (case (FLOOKUP s.refs src, FLOOKUP s.refs dst) of
         | (SOME (ByteArray _ ws), SOME (ByteArray fl ds)) =>
           (case xor_bytes ws ds of
            | SOME ds1 => Rval (Unit, s with refs := s.refs |+ (dst, ByteArray fl ds1))
            | NONE => Error)
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
         | Str i => (case x1 of RefPtr _ p =>
                       (case FLOOKUP s.refs p of SOME (ByteArray T j) =>
                          Rval (Boolv (j = MAP (n2w ∘ ORD) (explode i)), s)
                        | _ => Error)
                     | _ => Error)
         | _ => Error)
    | (BlockOp Equal,[x1;x2]) =>
        (case do_eq s.refs x1 x2 of
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
    | (Label n,[]) =>
        if n IN domain s.code then Rval (CodePtr n, s) else Error
    | (IntOp intop, vs) =>
        (case do_int_app intop vs of
        | SOME res => Rval (res ,s)
        | _ => Error)
    | (WordOp wordop, vs) =>
        (case do_word_app wordop vs of
        | SOME res => Rval (res ,s)
        | _ => Error)
    | (FFI n, [RefPtr _ cptr; RefPtr _ ptr]) =>
        (case (FLOOKUP s.refs cptr, FLOOKUP s.refs ptr) of
         | SOME (ByteArray T cws), SOME (ByteArray F ws) =>
           (case call_FFI s.ffi (ExtCall n) cws ws of
            | FFI_return ffi' ws' =>
                Rval (Unit,
                      s with <| refs := s.refs |+ (ptr,ByteArray F ws')
                              ; ffi   := ffi'|>)
            | FFI_final outcome =>
                Rerr (Rabort (Rffi_error outcome)))
         | _ => Error)
    | (BlockOp BoundsCheckBlock,xs) =>
        (case xs of
         | [Block tag ys; Number i] =>
               Rval (Boolv (0 <= i /\ i < & LENGTH ys),s)
         | _ => Error)
    | (MemOp (BoundsCheckByte loose),xs) =>
        (case xs of
         | [RefPtr _ ptr; Number i] =>
          (case FLOOKUP s.refs ptr of
           | SOME (ByteArray _ ws) =>
               Rval (Boolv (0 <= i /\ (if loose then $<= else $<) i (& LENGTH ws)),s)
           | _ => Error)
         | _ => Error)
    | (MemOp BoundsCheckArray,xs) =>
        (case xs of
         | [RefPtr _ ptr; Number i] =>
          (case FLOOKUP s.refs ptr of
           | SOME (ValueArray ws) =>
               Rval (Boolv (0 <= i /\ i < & LENGTH ws),s)
           | _ => Error)
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
  dec_clock n s = s with clock := s.clock - n
End

(* Functions for looking up function definitions *)

Definition find_code_def:
  (find_code (SOME p) args code =
     case lookup p code of
     | NONE => NONE
     | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp)
                                                  else NONE) /\
  (find_code NONE args code =
     if args = [] then NONE else
       case LAST args of
       | CodePtr loc =>
           (case sptree$lookup loc code of
            | NONE => NONE
            | SOME (arity,exp) => if LENGTH args = arity + 1
                                  then SOME (FRONT args,exp)
                                  else NONE)
       | other => NONE)
End

(* Functions for working with thunks *)

Datatype:
  dest_thunk_ret
    = BadRef
    | NotThunk
    | IsThunk thunk_mode v
End

Definition dest_thunk_def:
  dest_thunk (RefPtr _ ptr) refs =
    (case FLOOKUP refs ptr of
     | NONE => BadRef
     | SOME (Thunk Evaluated v) => IsThunk Evaluated v
     | SOME (Thunk NotEvaluated v) => IsThunk NotEvaluated v
     | SOME _ => NotThunk) ∧
  dest_thunk _ refs = NotThunk
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
   defined to evaluate a list of exp expressions. *)

Definition evaluate_def:
  (evaluate ([],env,^s) = (Rval [],s)) /\
  (evaluate (x::y::xs,env,s) =
     case fix_clock s (evaluate ([x],env,s)) of
     | (Rval v1,s1) =>
         (case evaluate (y::xs,env,s1) of
          | (Rval vs,s2) => (Rval (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (evaluate ([Var n],env,s) =
     if n < LENGTH env then (Rval [EL n env],s) else (Rerr(Rabort Rtype_error),s)) /\
  (evaluate ([If x1 x2 x3],env,s) =
     case fix_clock s (evaluate ([x1],env,s)) of
     | (Rval vs,s1) =>
          if Boolv T = HD vs then evaluate([x2],env,s1) else
          if Boolv F = HD vs then evaluate([x3],env,s1) else
            (Rerr(Rabort Rtype_error),s1)
     | res => res) /\
  (evaluate ([Let xs x2],env,s) =
     case fix_clock s (evaluate (xs,env,s)) of
     | (Rval vs,s1) => evaluate ([x2],vs++env,s1)
     | res => res) /\
  (evaluate ([Raise x1],env,s) =
     case evaluate ([x1],env,s) of
     | (Rval vs,s) => (Rerr(Rraise (HD vs)),s)
     | res => res) /\
  (evaluate ([Handle x1 x2],env,s1) =
     case fix_clock s1 (evaluate ([x1],env,s1)) of
     | (Rerr(Rraise v),s) => evaluate ([x2],v::env,s)
     | res => res) /\
  (evaluate ([Op op xs],env,s) =
     case fix_clock s (evaluate (xs,env,s)) of
     | (Rval vs,s) =>
         (case do_app op (REVERSE vs) s of
          | Rerr err => (Rerr err,s)
          | Rval (v,s) => (Rval [v],s))
     | res => res) /\
  (evaluate ([Tick x],env,s) =
     if s.clock = 0 then (Rerr(Rabort Rtimeout_error),s)
     else evaluate ([x],env,dec_clock 1 s)) /\
  (evaluate ([Force force_loc n],env,s) =
     if ~(n < LENGTH env) then (Rerr(Rabort Rtype_error),s) else
       let thunk_v = EL n env in
         case dest_thunk thunk_v s.refs of
         | BadRef => (Rerr (Rabort Rtype_error),s)
         | NotThunk => (Rerr (Rabort Rtype_error),s)
         | IsThunk Evaluated v => (Rval [v],s)
         | IsThunk NotEvaluated f =>
             (case find_code (SOME force_loc) [thunk_v; f] s.code of
              | NONE => (Rerr(Rabort Rtype_error),s)
              | SOME (args,exp) =>
                  if s.clock = 0 then
                    (Rerr(Rabort Rtimeout_error),s with clock := 0)
                  else
                    evaluate ([exp],args,dec_clock 1 s))) /\
  (evaluate ([Call ticks dest xs],env,s1) =
     case fix_clock s1 (evaluate (xs,env,s1)) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if s.clock < ticks + 1 then (Rerr(Rabort Rtimeout_error),s with clock := 0) else
                  evaluate ([exp],args,dec_clock (ticks + 1) s))
     | res => res)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure (list_size exp_size))
                         (\(xs,env,s). (s.clock,xs)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ imp_res_tac fix_clock_IMP
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ decide_tac
End

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def };
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def };
val op_thms = { nchotomy = closLangTheory.op_nchotomy, case_def = closLangTheory.op_case_def };
val word_op_thms = { nchotomy = closLangTheory.word_op_nchotomy, case_def = closLangTheory.word_op_case_def };
val block_op_thms = { nchotomy = closLangTheory.block_op_nchotomy, case_def = closLangTheory.block_op_case_def };
val glob_op_thms = { nchotomy = closLangTheory.glob_op_nchotomy, case_def = closLangTheory.glob_op_case_def };
val mem_op_thms = { nchotomy = closLangTheory.mem_op_nchotomy, case_def = closLangTheory.mem_op_case_def };
val v_thms = { nchotomy = theorem"v_nchotomy", case_def = definition"v_case_def" };
val ref_thms = { nchotomy = ref_nchotomy, case_def = ref_case_def };
val ffi_result_thms = { nchotomy = ffiTheory.ffi_result_nchotomy, case_def = ffiTheory.ffi_result_case_def };
val word_size_thms = { nchotomy = astTheory.word_size_nchotomy, case_def = astTheory.word_size_case_def };
val eq_result_thms = { nchotomy = semanticPrimitivesTheory.eq_result_nchotomy, case_def = semanticPrimitivesTheory.eq_result_case_def };
Theorem case_eq_thms =
  (pair_case_eq::
   bool_case_eq::
   (List.map prove_case_eq_thm
             [list_thms, option_thms, op_thms, v_thms, ref_thms,
              word_op_thms, block_op_thms, glob_op_thms, mem_op_thms,
              word_size_thms, eq_result_thms, ffi_result_thms]))
  |> LIST_CONJ;

Theorem do_app_const:
   (bvlSem$do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock) /\
    (op <> Install ==> s2.code = s1.code /\
                       s2.compile = s1.compile /\
                       s2.compile_oracle = s1.compile_oracle)
Proof
  rw[do_app_def,AllCaseEqs(),PULL_EXISTS,do_install_def,UNCURRY] \\ rw[]
QED

Theorem bvl_do_app_Ref[simp]:
   do_app (MemOp Ref) vs s = Rval
     (RefPtr T (LEAST ptr. ptr ∉ FDOM s.refs),
      s with refs :=
        s.refs |+ ((LEAST ptr. ptr ∉ FDOM s.refs),ValueArray vs))
Proof
  fs [do_app_def,LET_THM] \\ every_case_tac \\ fs []
QED

Theorem bvl_do_app_Cons[simp]:
   do_app (BlockOp (Cons tag)) vs s = Rval (Block tag vs,s)
Proof
  fs [do_app_def,LET_THM] \\ every_case_tac \\ fs []
QED

Theorem evaluate_clock:
   !xs env s1 vs s2.
     (evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  recInduct evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  imp_res_tac do_app_const >> fs[]
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
  initial_state ffi code co cc k = <|
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
  semantics init_ffi code co cc start =
  let es = [Call 0 (SOME start) []] in
  let init = initial_state init_ffi code co cc in
    if ∃k. FST (evaluate (es,[],init k)) = Rerr (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate (es,[],init k) = (r,s) ∧
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
              (SND (evaluate (es,[],init k))).ffi.io_events) UNIV))
End

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];
