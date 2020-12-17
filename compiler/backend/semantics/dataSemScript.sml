(*
  The formal semantics of dataLang
*)
open preamble data_simpTheory data_liveTheory data_spaceTheory dataLangTheory closSemTheory
     data_to_wordTheory (* TODO: immoral, semantics shouldn't depend on compiler *);

val _ = new_theory"dataSem";

val _ = Datatype `
  v = Number int              (* integer *)
    | Word64 word64
    | Block num num (v list)  (* cons block: timestamp, tag and payload *)
    | CodePtr num             (* code pointer *)
    | RefPtr num              (* pointer to ref cell *)`;

val Boolv_def = Define`
  Boolv b = Block 0 (bool_to_tag b) []`

val Unit_def = Define`
  Unit = Block 0 (tuple_tag) []`

(* Stack frame with:
   -  A stack frame size `ss` (NONE when unbounded)
   -  The local environment `env`
   -  Possibly a `handler`

  *)
val _ = Datatype `
       (* Env  ss           env  *)
  stack = Env (num option) (v num_map)
       (* Exc  ss           env        handler*)
        | Exc (num option) (v num_map) num`;

val _ = Datatype `
  limits =
    <| heap_limit   : num;    (* number of words in the heap *)
       length_limit : num;    (* length field in a Block *)
       stack_limit  : num;    (* max stack size *)
       arch_64_bit  : bool;   (* the arch is either 64-bit or 32-bit *)
       has_fp_ops   : bool;   (* the arch supports float ops *)
       has_fp_tops  : bool    (* the arch supports float ops *)
       |> `

val _ = Datatype `
  state =
    <| locals      : v num_map
     ; locals_size : num option  (* size of locals when pushed to stack, NONE if unbounded *)
     ; stack       : stack list
     ; stack_max   : num option  (* largest stack seen so far, NONE if unbounded *)
     ; stack_frame_sizes : num num_map (* stack frame sizes, unbounded if unmapped *)
     ; global      : num option
     ; handler     : num
     ; refs        : v ref num_map
     ; compile     : 'c -> (num # num # dataLang$prog) list -> (word8 list # word64 list # 'c) option
     ; clock       : num
     ; code        : (num # dataLang$prog) num_map
     ; ffi         : 'ffi ffi_state
     ; space       : num
     ; tstamps     : num option
     ; limits      : limits
     ; safe_for_space   : bool
     ; peak_heap_length : num
     ; compile_oracle   : num -> 'c # (num # num # dataLang$prog) list |> `

val s = ``(s:('c,'ffi) dataSem$state)``
val vs = ``(vs:dataSem$v list)``

Definition arch_size_def:
  arch_size lims = if lims.arch_64_bit then 64 else 32:num
End

Definition check_res_def:
  check_res r (n, refs, seen) =
    if size refs <= size r then (n, refs, seen) else (n, r, seen)
End

Theorem check_res_IMP:
  !y. (n,r,s) = check_res t y ==> size r <= size t
Proof
  fs [FORALL_PROD,check_res_def] \\ rw []
QED

Definition small_num_def:
  small_num arch64 (i:int) =
    if arch64 then -(2 ** 61) <= i /\ i < (2 ** 61)
              else -(2 ** 29) <= i /\ i < (2 ** 29)
End

Definition bignum_digits_def:
  bignum_digits arch64 n =
    if n = 0 then 0 else
      let d = if arch64 then 64 else 32 in
        1n + bignum_digits arch64 (n DIV 2 ** d)
End

Definition bignum_size_def:
  bignum_size arch64 i =
    1 + bignum_digits arch64 (Num (ABS i))
End

Definition small_num_def:
  small_num arch64 (i:int) =
    if arch64 then -(2 ** 61) <= i /\ i < (2 ** 61)
              else -(2 ** 29) <= i /\ i < (2 ** 29)
End

Definition bignum_digits_def:
  bignum_digits arch64 n =
    if n = 0 then 0 else
      let d = if arch64 then 64 else 32 in
        1n + bignum_digits arch64 (n DIV 2 ** d)
End

Definition bignum_size_def:
  bignum_size arch64 i =
    1 + bignum_digits arch64 (Num (ABS i))
End

Definition size_of_def:
  (size_of lims [] refs seen = (0, refs, seen)) /\
  (size_of lims (x::y::ys) refs seen =
    let (n1,refs1,seen1) = check_res refs (size_of lims (y::ys) refs seen) in
    let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
      (n1+n2,refs2,seen2)) /\
  (size_of lims [Word64 _] refs seen = (3, refs, seen)) /\
  (size_of lims [Number i] refs seen =
    (if small_num lims.arch_64_bit i then 0 else bignum_size lims.arch_64_bit i, refs, seen)) /\
  (size_of lims [CodePtr _] refs seen = (0, refs, seen)) /\
  (size_of lims [RefPtr r] refs seen =
     case lookup r refs of
     | NONE => (0, refs, seen)
     | SOME (ByteArray _ bs) => (LENGTH bs DIV (arch_size lims DIV 8) + 2, delete r refs, seen)
     | SOME (ValueArray vs) => let (n,refs,seen) = size_of lims vs (delete r refs) seen in
                                 (n + LENGTH vs + 1, refs, seen)) /\
  (size_of lims [Block ts tag []]) refs seen = (0, refs, seen) /\
  (size_of lims [Block ts tag vs] refs seen =
     if IS_SOME (lookup ts seen) then (0, refs, seen) else
       let (n,refs,seen) = size_of lims vs refs (insert ts () seen) in
         (n + LENGTH vs + 1, refs, seen))
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure v1_size)
                          (\(lims,vs,refs,seen). (sptree$size refs,vs)))`
  \\ rpt strip_tac \\ fs [sptreeTheory.size_delete]
  \\ imp_res_tac miscTheory.lookup_zero \\ fs []
  \\ rw [] \\ fs []
  \\ imp_res_tac check_res_IMP \\ fs []
End

Triviality check_res_size_of:
  check_res refs (size_of lims vs refs seen) = size_of lims vs refs seen
Proof
  qsuff_tac
    `!lims vs refs seen. size (( \ (n,refs,seen). refs) (size_of lims vs refs seen)) <= size refs`
  THEN1 (rw [] \\ pop_assum (assume_tac o SPEC_ALL) \\ pairarg_tac \\ fs [check_res_def])
  \\ ho_match_mp_tac size_of_ind \\ fs [size_of_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs[]
  \\ fs [check_res_def,bool_case_eq,option_case_eq,pair_case_eq,CaseEq"ref"]
  \\ rveq \\ fs [] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs[] \\ fs [size_delete]
QED

Theorem size_of_def[compute] = REWRITE_RULE [check_res_size_of] size_of_def
Theorem size_of_ind = REWRITE_RULE [check_res_size_of] size_of_ind

Definition extract_stack_def:
  extract_stack (Env _ env) = toList env /\
  extract_stack (Exc _ env _) = toList env
End

Definition global_to_vs_def:
  global_to_vs NONE = [] /\
  global_to_vs (SOME n) = [RefPtr n]
End

Definition stack_to_vs_def:
  stack_to_vs ^s =
    toList s.locals ++ FLAT (MAP extract_stack s.stack) ++ global_to_vs s.global
End

(* Measures the amount of space everything in a dataLang "heap" would need
   to fit in wordLang memory (over-approximation) *)
Definition size_of_heap_def:
  size_of_heap ^s =
    let (n,_,_) = size_of s.limits (stack_to_vs ^s) ^s.refs LN in
      n
End

Overload add_space_safe =
  ``λk ^s. s.safe_for_space
           ∧ size_of_heap s + k <= s.limits.heap_limit``

Overload heap_peak =
  ``λk ^s. MAX (s.peak_heap_length) (size_of_heap s + k)``

val add_space_def = Define `
  add_space ^s k =
    s with <| space := k
            ; safe_for_space   := add_space_safe k s
            ; peak_heap_length := heap_peak k s |>
`;

val consume_space_def = Define `
  consume_space k ^s =
    if s.space < k then NONE else SOME (s with space := s.space - k)`;

(* Determines which operations are safe for space *)
Definition allowed_op_def:
  allowed_op op _ = (op <> closLang$Install)
End

val v_to_list_def = Define`
  (v_to_list (Block ts tag []) =
     if tag = nil_tag then SOME [] else NONE) ∧
  (v_to_list (Block ts tag [h;bt]) =
     if tag = cons_tag then
       (case v_to_list bt of
        | SOME t => SOME (h::t)
        | _ => NONE )
     else NONE) ∧
  (v_to_list _ = NONE)`

Overload bignum_limit[local] =
  ``\i1 i2 s.
      let il = bignum_size s.limits.arch_64_bit i1 in
      let jl = bignum_size s.limits.arch_64_bit i2 in
        2 * il + 2 * jl``

(* Gives an upper bound to the memory consuption of an operation *)
val space_consumed_def = Define `
  (space_consumed ^s (ConsExtend tag) (Block _ _ xs'::Number lower::Number len::Number tot::xs) =
   LENGTH (xs++TAKE (Num len) (DROP (Num lower) xs')) + 1
  ) /\
  (space_consumed s RefArray [Number len; _] = Num len + 1) /\
  (space_consumed s (RefByte _) [Number len; _] = Num len DIV (arch_size s.limits DIV 8) + 2) /\
  (space_consumed s (FromList n) [Number len;lv] = Num len + 1) /\
  (space_consumed s Add [Number i1; Number i2] =
    if small_num s.limits.arch_64_bit i1 /\
       small_num s.limits.arch_64_bit i2 /\
       small_num s.limits.arch_64_bit (i1 + i2)
    then 0 else bignum_limit i1 i2 s) /\
  (space_consumed s Sub [Number i1; Number i2] =
    if small_num s.limits.arch_64_bit i1 /\
       small_num s.limits.arch_64_bit i2 /\
       small_num s.limits.arch_64_bit (i1 - i2)
    then 0 else bignum_limit i1 i2 s) /\
  (space_consumed s Mult [Number i1; Number i2] =
    if small_num s.limits.arch_64_bit i1 /\ 0 <= i1 /\
       small_num s.limits.arch_64_bit i2 /\ 0 <= i2 /\
       small_num s.limits.arch_64_bit (i1 * i2)
    then 0 else bignum_limit i1 i2 s) /\
  (space_consumed s Div [Number i1; Number i2] =
    if small_num s.limits.arch_64_bit i1 /\ 0 <= i1 /\
       small_num s.limits.arch_64_bit i2 /\ 0 <= i2 /\
       small_num s.limits.arch_64_bit (i1 / i2)
    then 0 else bignum_limit i1 i2 s) /\
  (space_consumed s Mod [Number i1; Number i2] =
    if small_num s.limits.arch_64_bit i1 /\ 0 <= i1 /\
       small_num s.limits.arch_64_bit i2 /\ 0 <= i2 /\
       small_num s.limits.arch_64_bit (i1 % i2)
    then 0 else bignum_limit i1 i2 s) /\
  (space_consumed s ListAppend [lv1; lv2] =
   case v_to_list lv1 of
    SOME l => SUC(LENGTH l) * 3
   | NONE => 0
  ) /\
  (space_consumed s (op:closLang$op) (vs:v list) = 0:num)
`

val vb_size_def = tDefine"vb_size"`
  (vb_size (Block ts t ls) = 1 + t + SUM (MAP vb_size ls) + LENGTH ls) ∧
  (vb_size _ = 1n)`
(WF_REL_TAC`measure v_size` \\
 ntac 2 gen_tac \\ Induct \\ rw[fetch "-" "v_size_def"] \\ rw[]
 \\ res_tac \\ rw[]);

val vs_depth_def = tDefine"vs_depth"`
  (vs_depth (Block ts t ls) = vs_depth_list ls) ∧
  (vs_depth _ = 0) ∧
  (vs_depth_list [] = 0) ∧
  (vs_depth_list (x::xs) = MAX (1 + vs_depth x) (vs_depth_list xs))`
(WF_REL_TAC`measure (λx. sum_CASE x v_size v1_size)`);

Definition eq_code_stack_max_def:
  eq_code_stack_max n tsz =
  OPTION_MAP ($* n)
    (OPTION_MAP2 MAX
      (lookup Equal_location tsz)
      (OPTION_MAP2 MAX
        (lookup Equal1_location tsz)
        (lookup Compare1_location tsz)))
End

Definition stack_consumed_def:
  (stack_consumed  sfs lims (CopyByte _) vs =
    OPTION_MAP2 MAX
     (lookup ByteCopy_location sfs)
     (OPTION_MAP2 MAX
        (lookup ByteCopyAdd_location sfs)
        (lookup ByteCopySub_location sfs))) /\
  (stack_consumed sfs lims (RefByte _) vs =
    OPTION_MAP2 MAX
     (lookup RefByte_location sfs)
     (lookup Replicate_location sfs)) /\
  (stack_consumed sfs lims (RefArray) vs =
    OPTION_MAP2 MAX
     (lookup RefArray_location sfs)
     (lookup Replicate_location sfs)) /\
  (stack_consumed sfs lims (ConsExtend _) vs =
    lookup MemCopy_location sfs) /\
    (* MemCopy looks not always necessary. Could be refined for more precise bounds. *)
  (stack_consumed sfs lims (FromList _) vs =
    OPTION_MAP2 MAX
     (lookup FromList_location sfs)
     (lookup FromList1_location sfs)) /\
  (stack_consumed sfs lims ListAppend vs =
    OPTION_MAP2 MAX
     (lookup Append_location sfs)
     (OPTION_MAP2 MAX
       (lookup AppendLenLoop_location sfs)
       (lookup AppendMainLoop_location sfs))
  ) /\
  (stack_consumed sfs lims (Div) [Number n1; Number n2] =
    if small_num lims.arch_64_bit n1 /\ 0 <= n1 /\
       small_num lims.arch_64_bit n2 /\ 0 <= n2 /\
       small_num lims.arch_64_bit (n1 / n2)
    then
      OPTION_MAP2 MAX
        (lookup LongDiv_location sfs)
        (lookup LongDiv1_location sfs)
    else
      OPTION_MAP2 MAX (lookup Div_location sfs)
        (max_depth sfs AnyArith_call_tree)) /\
  (stack_consumed sfs lims (Mod) [Number n1; Number n2] =
    if small_num lims.arch_64_bit n1 /\ 0 <= n1 /\
       small_num lims.arch_64_bit n2 /\ 0 <= n2 /\
       small_num lims.arch_64_bit (n1 % n2)
    then
      OPTION_MAP2 MAX
        (lookup LongDiv_location sfs)
        (lookup LongDiv1_location sfs)
    else
      OPTION_MAP2 MAX (lookup Mod_location sfs)
        (max_depth sfs AnyArith_call_tree)) /\
  (stack_consumed sfs lims (Mult) [Number n1; Number n2] =
    if small_num lims.arch_64_bit n1 /\ 0 <= n1 /\
       small_num lims.arch_64_bit n2 /\ 0 <= n2 /\
       small_num lims.arch_64_bit (n1 * n2)
    then SOME 0 else
      OPTION_MAP2 MAX (lookup Mul_location sfs)
        (max_depth sfs AnyArith_call_tree)) /\
  (stack_consumed sfs lims (Equal) [v1;v2] =
   (eq_code_stack_max (MIN (vs_depth v1 + 1) (vs_depth v2 + 1)) sfs)) /\
  (stack_consumed sfs lims (Sub) [Number n1; Number n2] =
    if small_num lims.arch_64_bit n1 /\
       small_num lims.arch_64_bit n2 /\
       small_num lims.arch_64_bit (n1 - n2)
    then SOME 0 else
      OPTION_MAP2 MAX (lookup Sub_location sfs)
        (max_depth sfs AnyArith_call_tree)) /\
  (stack_consumed sfs lims (Add) [Number n1; Number n2] =
    if small_num lims.arch_64_bit n1 /\
       small_num lims.arch_64_bit n2 /\
       small_num lims.arch_64_bit (n1 + n2)
    then SOME 0 else
      OPTION_MAP2 MAX (lookup Add_location sfs)
        (max_depth sfs AnyArith_call_tree)) /\
  (stack_consumed sfs lims (LessEq) vs =
    (* This is a conservative estimate --- no calls happen for smallnums *)
    OPTION_MAP2 MAX
     (lookup Compare_location sfs)
     (lookup Compare1_location sfs)) /\
  (stack_consumed sfs lims (Less) vs =
    (* This is a conservative estimate --- no calls happen for smallnums *)
    OPTION_MAP2 MAX
     (lookup Compare_location sfs)
     (lookup Compare1_location sfs)) /\
  (* TODO: add more clauses as the need arises *)
  (stack_consumed sfs lims p vs =
     if allowed_op p (LENGTH vs) then SOME 0 else NONE)
End

Overload do_space_safe =
  ``λop vs ^s. if op_space_reset op
              then s.safe_for_space
                   ∧ size_of_heap s + space_consumed s op vs <= s.limits.heap_limit
              else s.safe_for_space``

Overload do_space_peak =
  ``λop vs ^s. if op_space_reset op
              then heap_peak (space_consumed s op vs) s
              else s.peak_heap_length``

val do_space_def = Define `
  do_space op vs ^s =
    if op_space_reset op
    then  SOME (s with <| space := 0
                        ; safe_for_space := do_space_safe op vs s
                        ; peak_heap_length := do_space_peak op vs s
                        |>)
    else if op_space_req op (LENGTH vs) = 0 then SOME s
         else consume_space (op_space_req op (LENGTH vs)) s`;

Definition size_of_stack_frame_def:
  size_of_stack_frame (Env n _)  = n
∧ size_of_stack_frame (Exc n _ _) = OPTION_MAP ($+ 3) n
End

Definition size_of_stack_def:
  size_of_stack = FOLDR (OPTION_MAP2 $+ o size_of_stack_frame) (SOME 1)
End

val do_stack_def = Define `
  do_stack op vs ^s =
  let new_stack = OPTION_MAP2 $+ (stack_consumed s.stack_frame_sizes s.limits op vs)
                      (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size)
  in
    s with <| safe_for_space := (s.safe_for_space
                                ∧ the F (OPTION_MAP ($> s.limits.stack_limit) new_stack))
              ; stack_max := OPTION_MAP2 MAX s.stack_max new_stack |>`

val v_to_bytes_def = Define `
  v_to_bytes lv = some ns:word8 list.
                    v_to_list lv = SOME (MAP (Number o $& o w2n) ns)`;

val v_to_words_def = Define `
  v_to_words lv = some ns. v_to_list lv = SOME (MAP Word64 ns)`;

(* TODO: move this stuff *)
val isClos_def = Define `
  isClos t1 l1 = (((t1 = closure_tag) \/ (t1 = partial_app_tag)) /\ l1 <> [])`;

val do_eq_def = tDefine"do_eq"`
  (do_eq _ (CodePtr _) _ = Eq_type_error) ∧
  (do_eq _ _ (CodePtr _) = Eq_type_error) ∧
  (do_eq _ (Number n1) (Number n2) = (Eq_val (n1 = n2))) ∧
  (do_eq _ (Number _) _ = Eq_type_error) ∧
  (do_eq _ _ (Number _) = Eq_type_error) ∧
  (do_eq _ (Word64 w1) (Word64 w2) = (Eq_val (w1 = w2))) ∧
  (do_eq _ (Word64 _) _ = Eq_type_error) ∧
  (do_eq _ _ (Word64 _) = Eq_type_error) ∧
  (do_eq refs (RefPtr n1) (RefPtr n2) =
    case (lookup n1 refs, lookup n2 refs) of
      (SOME (ByteArray T bs1), SOME (ByteArray T bs2))
        => Eq_val (bs1 = bs2)
    | (SOME (ByteArray T bs1), _) => Eq_type_error
    | (_, SOME (ByteArray T bs2)) => Eq_type_error
    | _ => Eq_val (n1 = n2)) ∧
  (do_eq _ (RefPtr _) _ = Eq_type_error) ∧
  (do_eq _ _ (RefPtr _) = Eq_type_error) ∧
  (* TODO: How time-stamps impact equality between blocks? *)
  (do_eq refs (Block _ t1 l1) (Block _ t2 l2) =
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
  (do_eq_list _ _ _ = Eq_val F)`
  (WF_REL_TAC `measure (\x. case x of INL (_,v1,v2) => v_size v1 | INR (_,vs1,vs2) => v1_size vs1)`);
val _ = export_rewrites["do_eq_def"];

Overload Error[local] =
  ``(Rerr(Rabort Rtype_error)):(dataSem$v#('c,'ffi) dataSem$state, dataSem$v)result``

val do_install_def = Define `
  do_install vs ^s =
      (case vs of
       | [v1;v2;vl1;vl2] =>
           (case (v_to_bytes v1, v_to_words v2) of
            | (SOME bytes, SOME data) =>
               if vl1 <> Number (& LENGTH bytes) \/
                  vl2 <> Number (& LENGTH data)
               then Rerr(Rabort Rtype_error) else
               let (cfg,progs) = s.compile_oracle 0 in
               let new_oracle = shift_seq 1 s.compile_oracle in
                 (case s.compile cfg progs, progs of
                  | SOME (bytes',data',cfg'), (k,prog)::_ =>
                      if bytes = bytes' ∧ data = data' ∧ FST(new_oracle 0) = cfg' then
                        let s' =
                          s with <|
                             safe_for_space := F ;
                             code := union s.code (fromAList progs) ;
                             compile_oracle := new_oracle |>
                        in
                          Rval (CodePtr k, s')
                      else Rerr(Rabort Rtype_error)
                  | _ => Rerr(Rabort Rtype_error))
            | _ => Rerr(Rabort Rtype_error))
       | _ => Rerr(Rabort Rtype_error))`;

val list_to_v_def = Define`
  list_to_v ts t [] = t ∧
  list_to_v ts t (h::l) = Block ts cons_tag [h; list_to_v (ts+1) t l]`;

Overload Block_nil = ``Block 0 nil_tag []``

val with_fresh_ts_def = Define`
  with_fresh_ts ^s n f = case s.tstamps of
                           SOME ts => f ts (s with <| tstamps := SOME (ts + n) |>)
                         | NONE    => f 0 s
`;

Definition lim_safe_def[simp]:
  (lim_safe lims (Cons tag) xs = if xs = []
                             then tag < 2 ** (arch_size lims) DIV 16
                             else
                               LENGTH xs < 2 ** lims.length_limit /\
                               LENGTH xs < 2 ** (arch_size lims - 4) /\
                               4 * tag < 2 ** (arch_size lims) DIV 16 /\
                               4 * tag < 2 ** (arch_size lims - lims.length_limit - 2)
                               )
∧ (lim_safe lims (FromList tag) xs = (case xs of
                                 | [len;lv] =>
                                   (case v_to_list lv of
                                   | SOME n  =>
                                       if len = Number (& (LENGTH n))
                                       then small_num lims.arch_64_bit (&(LENGTH n)) /\
                                            LENGTH n < 2 ** lims.length_limit /\
                                            LENGTH n < arch_size lims DIV 16 /\
                                            4 * tag < 2 ** (arch_size lims - lims.length_limit - 2) /\
                                            4 * tag < 2 ** (arch_size lims) DIV 16
                                       else T
                                   | _ => T)
                                 | _ => T))
∧ (lim_safe lims ListAppend [x1;x2] =
        (case (v_to_list x1, v_to_list x2) of
         | (SOME xs, SOME ys) =>
             1 < lims.length_limit /\
             3 * (SUC (LENGTH xs)) < 2 ** (arch_size lims) DIV 8
         | _ => T))
∧ (lim_safe lims (ConsExtend tag) (Block _ _ xs'::Number lower::Number len::Number tot::xs) =
        if lower < 0 ∨ len < 0 ∨ lower + len > &LENGTH xs' ∨
           tot = 0 ∨ tot ≠ &LENGTH xs + len then T
        else LENGTH (xs++TAKE (Num len) (DROP (Num lower) xs')) < 2 ** lims.length_limit /\
             LENGTH (xs++TAKE (Num len) (DROP (Num lower) xs')) < 2 ** (arch_size lims) DIV 16 /\
             4 * tag < 2 ** (arch_size lims) DIV 16 /\
             4 * tag < 2 ** (arch_size lims - lims.length_limit - 2))
∧ (lim_safe lims Add [Number i1; Number i2] =
   (if small_num lims.arch_64_bit i1 /\
       small_num lims.arch_64_bit i2 /\
       small_num lims.arch_64_bit (i1 + i2)
    then T else
      let il = bignum_size lims.arch_64_bit i1 in
      let jl = bignum_size lims.arch_64_bit i2 in
        il + jl <= 2 ** lims.length_limit)
  )
∧ (lim_safe lims Sub [Number i1; Number i2] =
   (if small_num lims.arch_64_bit i1 /\
       small_num lims.arch_64_bit i2 /\
       small_num lims.arch_64_bit (i1 - i2)
    then T else
      let il = bignum_size lims.arch_64_bit i1 in
      let jl = bignum_size lims.arch_64_bit i2 in
        il + jl <= 2 ** lims.length_limit)
  )
∧ (lim_safe lims Mult [Number i1; Number i2] =
   (if small_num lims.arch_64_bit i1 /\ 0 <= i1 /\
       small_num lims.arch_64_bit i2 /\ 0 <= i2 /\
       small_num lims.arch_64_bit (i1 * i2)
    then T else
      let il = bignum_size lims.arch_64_bit i1 in
      let jl = bignum_size lims.arch_64_bit i2 in
        il + jl <= 2 ** lims.length_limit)
  )
∧ (lim_safe lims Div [Number i1; Number i2] =
   (if small_num lims.arch_64_bit i1 /\ 0 <= i1 /\
       small_num lims.arch_64_bit i2 /\ 0 <= i2 /\
       small_num lims.arch_64_bit (i1 / i2)
    then T else
      let il = bignum_size lims.arch_64_bit i1 in
      let jl = bignum_size lims.arch_64_bit i2 in
        il + jl <= 2 ** lims.length_limit)
  )
∧ (lim_safe lims Mod [Number i1; Number i2] =
   (if small_num lims.arch_64_bit i1 /\ 0 <= i1 /\
       small_num lims.arch_64_bit i2 /\ 0 <= i2 /\
       small_num lims.arch_64_bit (i1 % i2)
    then T else
      let il = bignum_size lims.arch_64_bit i1 in
      let jl = bignum_size lims.arch_64_bit i2 in
        il + jl <= 2 ** lims.length_limit)
  )
∧ (lim_safe lims RefArray [Number i; v] =
   (0 <= i /\
    Num i < 2 ** (arch_size lims) DIV 16 /\
    Num i < 2 ** lims.length_limit)
  )
∧ (lim_safe lims (RefByte _) (Number i::xs) =
   (0 <= i /\
    Num i DIV (arch_size lims DIV 8) < 2 ** (arch_size lims) DIV arch_size lims /\
    Num i DIV (arch_size lims DIV 8) + 1 < 2 ** lims.length_limit /\
    small_num lims.arch_64_bit i)
  )
∧ (lim_safe lims Ref xs =
   (LENGTH xs < 2 ** lims.length_limit /\
    LENGTH xs < 2 ** arch_size lims DIV 16)
  )
∧ (lim_safe lims WordToInt _ =
   (1 < lims.length_limit)
  )
∧ (lim_safe lims WordFromInt _ =
   (1 < lims.length_limit)
  )
∧ (lim_safe lims (WordOp W64 _) _ =
   (1 < lims.length_limit)
  )
∧ (lim_safe lims (WordShift W64 _ _) _ =
   (1 < lims.length_limit)
  )
∧ (lim_safe lims (WordFromWord _) _ =
   (1 < lims.length_limit)
  )
∧ (lim_safe lims (FP_cmp _) _ =
   lims.has_fp_ops
  )
∧ (lim_safe lims (FP_uop _) _ =
   (lims.has_fp_ops /\ (lims.arch_64_bit \/ 1 < lims.length_limit))
  )
∧ (lim_safe lims (FP_bop _) _ =
   (lims.has_fp_ops /\ (lims.arch_64_bit \/ 1 < lims.length_limit))
  )
∧ (lim_safe lims (FP_top _) _ =
   (lims.has_fp_ops /\ lims.has_fp_tops /\ (lims.arch_64_bit \/ 1 < lims.length_limit))
  )
∧ (lim_safe lims _ _ = T)
End

Definition do_lim_safe[simp]:
  do_lim_safe ^s op vs =
  s with safe_for_space := (lim_safe s.limits op vs
                            ∧ s.safe_for_space)
End

Definition check_lim_def:
  check_lim ^s n =
     s with safe_for_space := (n < 2 ** s.limits.length_limit ∧
                               s.safe_for_space)
End

val do_app_aux_def = Define `
  do_app_aux op ^vs ^s =
    case (op,vs) of
    (* bvi part *)
    | (Const i,xs) => if small_enough_int i then
                        Rval (Number i : v, s)
                      else Error
    | (Label l,xs) => (case xs of
                       | [] => if l IN domain s.code then
                                 Rval (CodePtr l, s)
                               else Error
                       | _ => Error)
    | (GlobalsPtr,xs) =>
        (case xs of
         | [] => (case s.global of
                  | SOME p => Rval (RefPtr p, s)
                  | NONE => Error)
         | _ => Error)
    | (Global n,xs) =>
        (case xs of
         | [] => (case s.global of
                  | SOME ptr =>
                      (case lookup ptr s.refs of
                       | SOME (ValueArray xs) =>
                           (if n < LENGTH xs
                            then Rval (EL n xs, s)
                            else Error)
                       | _ => Error)
                  | NONE => Error)
         | _ => Error)
    | (SetGlobal n,xs) =>
        (case xs of
         | [x] => (case s.global of
                   | SOME ptr =>
                       (case lookup ptr s.refs of
                        | SOME (ValueArray xs) =>
                            (if n < LENGTH xs
                             then Rval (Unit, s with refs := insert ptr
                                          (ValueArray (LUPDATE x n xs)) s.refs)
                             else Error)
                        | _ => Error)
                   | NONE => Error)
         | _ => Error)
    | (SetGlobalsPtr,xs) =>
        (case xs of
         | [RefPtr p] => Rval (Unit, s with global := SOME p)
         | _ => Error)
    | (FromList n, xs) =>
        (case xs of
         | [len;lv] =>
            (case v_to_list lv of
             | SOME [] => if len = Number 0
                          then Rval (Block 0 n [],s)
                          else Error
             | SOME vs => if len = Number (& (LENGTH vs))
                          then with_fresh_ts s 1
                            (λts s'. Rval (Block ts n vs,
                                          check_lim (s') (LENGTH vs)))
                          else Error
             | _ => Error)
         | _ => Error)
    | (RefByte f, xs) =>
        (case xs of
          | [Number i; Number b] =>
            if 0 ≤ i ∧ (∃w:word8. b = & (w2n w)) then
              let ptr = (LEAST ptr. ¬(ptr IN domain s.refs)) in
                Rval (RefPtr ptr, s with <|refs := insert ptr
                  (ByteArray f (REPLICATE (Num i) (i2w b))) s.refs|>)
            else Rerr (Rabort Rtype_error)
          | _ => Rerr (Rabort Rtype_error))
    | (AllocGlobal, _)   => Rerr (Rabort Rtype_error)
    | (String _, _)      => Rerr (Rabort Rtype_error)
    | (FromListByte, _)  => Rerr (Rabort Rtype_error)
    | (ConcatByteVec, _) => Rerr (Rabort Rtype_error)
    | (CopyByte T, _)    => Rerr (Rabort Rtype_error)
    (* bvl part *)
    | (Cons tag,xs) => (if xs = []
                        then  Rval (Block 0 tag [],s)
                        else with_fresh_ts s 1
                               (λts s'. Rval (Block ts tag xs,
                                              check_lim s' (LENGTH xs))))
    | (ConsExtend tag,Block x y xs'::Number lower::Number len::Number tot::xs) =>
        if lower < 0 ∨ len < 0 ∨ lower + len > &LENGTH xs' ∨
           tot = 0 ∨ tot ≠ &LENGTH xs + len then
          Error
        else with_fresh_ts s 1
                           (λts s'.
                                    let l = (xs++TAKE (Num len) (DROP (Num lower) xs'))
                                    in Rval (Block ts tag l,
                                             check_lim s' (LENGTH l)))
    | (ConsExtend tag,_) => Error
    | (El,[Block _ tag xs; Number i]) =>
        if 0 ≤ i ∧ Num i < LENGTH xs then Rval (EL (Num i) xs, s) else Error
    | (El,[RefPtr ptr; Number i]) =>
        (case lookup ptr s.refs of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (EL (Num i) xs, s)
             else Error)
         | _ => Error)
    | (ElemAt n,[Block _ tag xs]) =>
        if n < LENGTH xs then Rval (EL n xs, s) else Error
    | (ElemAt n,[RefPtr ptr]) =>
        (case lookup ptr s.refs of
         | SOME (ValueArray xs) =>
            (if n < LENGTH xs
             then Rval (EL n xs, s)
             else Error)
         | _ => Error)
    | (ListAppend,[x1;x2]) =>
        (case (v_to_list x1, v_to_list x2) of
         | (SOME xs, SOME ys) =>
             with_fresh_ts ^s (LENGTH xs)
             (λts s'. Rval (list_to_v ts x2 xs,
                           check_lim (s') 2))
         | _ => Error)
    | (LengthBlock,[Block _ tag xs]) =>
        Rval (Number (&LENGTH xs), s)
    | (Length,[RefPtr ptr]) =>
        (case lookup ptr s.refs of
          | SOME (ValueArray xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (LengthByte,[RefPtr ptr]) =>
        (case lookup ptr s.refs of
          | SOME (ByteArray _ xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (RefArray,[Number i;v]) =>
        if 0 ≤ i then
          let ptr = (LEAST ptr. ¬(ptr IN domain s.refs)) in
            Rval (RefPtr ptr,
                  s with <|refs := insert ptr
                                          (ValueArray (REPLICATE (Num i) v)) s.refs|>)
         else Error
    | (DerefByte,[RefPtr ptr; Number i]) =>
        (case lookup ptr s.refs of
         | SOME (ByteArray _ ws) =>
            (if 0 ≤ i ∧ i < &LENGTH ws
             then Rval (Number (& (w2n (EL (Num i) ws))),s)
             else Error)
         | _ => Error)
    | (UpdateByte,[RefPtr ptr; Number i; Number b]) =>
        (case lookup ptr s.refs of
         | SOME (ByteArray f bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ (∃w:word8. b = & (w2n w))
             then
               Rval (Unit, s with refs := insert ptr
                 (ByteArray f (LUPDATE (i2w b) (Num i) bs)) s.refs)
             else Error)
         | _ => Error)
    | (CopyByte F,[RefPtr src; Number srcoff; Number len; RefPtr dst; Number dstoff]) =>
        (case (lookup src s.refs, lookup dst s.refs) of
         | (SOME (ByteArray _ ws), SOME (ByteArray fl ds)) =>
           (case copy_array (ws,srcoff) len (SOME(ds,dstoff)) of
                              (* no time-stamp *)
            | SOME ds => Rval (Unit, s with refs := insert dst (ByteArray fl ds) s.refs)
            | NONE => Error)
         | _ => Error)
    | (TagEq n,[Block _ tag xs]) =>
        Rval (Boolv (tag = n), s)
    | (LenEq l,[Block _ tag xs]) =>
        Rval (Boolv (LENGTH xs = l),s)
    | (TagLenEq n l,[Block _ tag xs]) =>
        Rval (Boolv (tag = n ∧ LENGTH xs = l),s)
    | (EqualInt i,[x1]) =>
        (case x1 of
         | Number j => Rval (Boolv (i = j), s)
         | _ => Error)
    | (Equal,[x1;x2]) =>
        (case do_eq s.refs x1 x2 of
         | Eq_val b => Rval (Boolv b, s)
         | _ => Error)
    | (Ref,xs) =>
        let ptr = (LEAST ptr. ~(ptr IN domain s.refs)) in
          Rval (RefPtr ptr, s with <| refs := insert ptr (ValueArray xs) s.refs|>)
    | (Update,[RefPtr ptr; Number i; x]) =>
        (case lookup ptr s.refs of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (Unit, s with refs := insert ptr
                              (ValueArray (LUPDATE x (Num i) xs)) s.refs)
             else Error)
         | _ => Error)
    | (Add,[Number n1; Number n2]) => Rval (Number (n1 + n2),s)
    | (Sub,[Number n1; Number n2]) => Rval (Number (n1 - n2),s)
    | (Mult,[Number n1; Number n2]) => Rval (Number (n1 * n2),s)
    | (Div,[Number n1; Number n2]) =>
         if n2 = 0 then Error else Rval (Number (n1 / n2),s)
    | (Mod,[Number n1; Number n2]) =>
         if n2 = 0 then Error else Rval (Number (n1 % n2),s)
    | (Less,[Number n1; Number n2]) =>
         Rval (Boolv (n1 < n2),s)
    | (LessEq,[Number n1; Number n2]) =>
         Rval (Boolv (n1 <= n2),s)
    | (Greater,[Number n1; Number n2]) =>
         Rval (Boolv (n1 > n2),s)
    | (GreaterEq,[Number n1; Number n2]) =>
         Rval (Boolv (n1 >= n2),s)
    | (WordOp W8 opw,[Number n1; Number n2]) =>
       (case some (w1:word8,w2:word8). n1 = &(w2n w1) ∧ n2 = &(w2n w2) of
        | NONE => Error
        | SOME (w1,w2) => Rval (Number &(w2n (opw_lookup opw w1 w2)),s))
    | (WordOp W64 opw,[Word64 w1; Word64 w2]) =>
        Rval (Word64 (opw_lookup opw w1 w2),s)
    | (WordShift W8 sh n, [Number i]) =>
       (case some (w:word8). i = &(w2n w) of
        | NONE => Error
        | SOME w => Rval (Number &(w2n (shift_lookup sh w n)),s))
    | (WordShift W64 sh n, [Word64 w]) =>
        Rval (Word64 (shift_lookup sh w n),s)
    | (WordFromInt, [Number i]) =>
        Rval (Word64 (i2w i),s)
    | (WordToInt, [Word64 w]) =>
        Rval (Number (&(w2n w)),s)
    | (WordFromWord T, [Word64 w]) =>
        Rval (Number (&(w2n ((w2w:word64->word8) w))),s)
    | (WordFromWord F, [Number n]) =>
       (case some (w:word8). n = &(w2n w) of
        | NONE => Error
        | SOME w => Rval (Word64 (w2w w),s))
    | (FFI n, [RefPtr cptr; RefPtr ptr]) =>
        (case (lookup cptr s.refs, lookup ptr s.refs) of
         | SOME (ByteArray T cws), SOME (ByteArray F ws) =>
           (case call_FFI s.ffi n cws ws of
            | FFI_return ffi' ws' =>
                Rval (Unit,
                      s with <| refs := insert ptr (ByteArray F ws') s.refs
                              ; ffi   := ffi'|>)
            | FFI_final outcome =>
                Rerr (Rabort (Rffi_error outcome)))
         | _ => Error)
    | (FP_top t_op, ws) =>
        (case ws of
         | [Word64 w1; Word64 w2; Word64 w3] =>
            (Rval (Word64 (fp_top t_op w1 w2 w3),s))
         | _ => Error)
    | (FP_bop bop, ws) =>
        (case ws of
         | [Word64 w1; Word64 w2] => (Rval (Word64 (fp_bop bop w1 w2),s))
         | _ => Error)
    | (FP_uop uop, ws) =>
        (case ws of
         | [Word64 w] => (Rval (Word64 (fp_uop uop w),s))
         | _ => Error)
    | (FP_cmp cmp, ws) =>
        (case ws of
         | [Word64 w1; Word64 w2] => (Rval (Boolv (fp_cmp cmp w1 w2),s))
         | _ => Error)
    | (BoundsCheckBlock,xs) =>
        (case xs of
         | [Block _ tag ys; Number i] =>
               Rval (Boolv (0 <= i /\ i < & LENGTH ys),s)
         | _ => Error)
    | (BoundsCheckByte loose,xs) =>
        (case xs of
         | [RefPtr ptr; Number i] =>
          (case lookup ptr s.refs of
           | SOME (ByteArray _ ws) =>
               Rval (Boolv (0 <= i /\ (if loose then $<= else $<) i (& LENGTH ws)),s)
           | _ => Error)
         | _ => Error)
    | (BoundsCheckArray,xs) =>
        (case xs of
         | [RefPtr ptr; Number i] =>
          (case lookup ptr s.refs of
           | SOME (ValueArray ws) =>
               Rval (Boolv (0 <= i /\ i < & LENGTH ws),s)
           | _ => Error)
         | _ => Error)
    | (LessConstSmall n,xs) =>
        (case xs of
         | [Number i] => if 0 <= i /\ i <= 1000000 /\ n < 1000000
                         then Rval (Boolv (i < &n),s) else Error
         | _ => Error)
    | (ConfigGC,[Number _; Number _]) => (Rval (Unit, s))
    | _ => Error`;

Overload do_app_safe =
  ``λop vs s. if allowed_op op (LENGTH vs)
              then (do_space_safe op vs s ∧ lim_safe s.limits op vs
                    ∧ the F (OPTION_MAP ($> s.limits.stack_limit)
                           (OPTION_MAP2 $+ (stack_consumed s.stack_frame_sizes s.limits op vs)
                             (OPTION_MAP2 $+ (size_of_stack s.stack) s.locals_size))))
              else F
              ``

Overload do_app_peak =
  ``λop vs s. if op = Install
              then s.peak_heap_length
              else if MEM op [Greater; GreaterEq] then s.peak_heap_length
              else do_space_peak op vs s``


val do_app_def = Define `
  do_app op vs ^s =
    if op = Install then do_install vs (s with <|stack_max := NONE; stack_frame_sizes := LN|>) else
    if MEM op [Greater; GreaterEq] then Error else
    case do_space op vs s of
    | NONE => Error
    | SOME s1 => do_app_aux op vs (do_stack op vs (do_lim_safe s1 op vs))`

val get_var_def = Define `
  get_var v = lookup v`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val set_var_def = Define `
set_var v x s = (s with locals := (insert v x s.locals))`;

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val LESS_EQ_dec_clock = Q.prove(
  `r.clock <= (dec_clock s).clock ==> r.clock <= s.clock`,
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC);

Definition flush_state_def:
   flush_state T ^s = s with <| locals := LN
                              ; stack := []
                              ; locals_size := SOME 0 |>
∧  flush_state F ^s = s with <| locals := LN
                              ; locals_size := SOME 0 |>
End

Definition call_env_def:
  call_env args size ^s =
    let new_stack_max  = OPTION_MAP2 MAX s.stack_max
                             (OPTION_MAP2 $+ (size_of_stack s.stack) size);
        stack_safe = the F (OPTION_MAP ($> s.limits.stack_limit) new_stack_max)
    in
      s with <| locals := fromList args
              ; locals_size := size
              ; stack_max := new_stack_max
              ; safe_for_space := (s.safe_for_space ∧ stack_safe)
                               |>
End

Definition push_env_def:
  (push_env env F ^s =
    let stack      = Env s.locals_size env :: s.stack;
        stack_max  = OPTION_MAP2 MAX s.stack_max (size_of_stack stack);
        stack_safe = the F (OPTION_MAP ($> s.limits.stack_limit) stack_max)
    in s with <| stack := stack
               ; stack_max := stack_max
               ; safe_for_space := (s.safe_for_space ∧ stack_safe) |>)
∧ (push_env env T ^s =
   let stack     = Exc s.locals_size env s.handler :: s.stack;
       stack_max = OPTION_MAP2 MAX s.stack_max (size_of_stack stack);
       stack_safe = the F (OPTION_MAP ($> s.limits.stack_limit) stack_max)
   in s with <| stack := stack
              ; stack_max := stack_max
              ; handler := LENGTH s.stack
              ; safe_for_space := (s.safe_for_space ∧ stack_safe) |>)
End

val pop_env_def = Define `
  pop_env ^s =
    case s.stack of
    | (Env ss e::xs) =>
        SOME (s with <| locals      := e
                      ; stack       := xs
                      ; locals_size := ss |>)
    | (Exc ss e n::xs) =>
        SOME (s with <| locals      := e
                      ; stack       := xs
                      ; locals_size := ss
                      ; handler     := n |>)
    | _ => NONE`;

val jump_exc_def = Define `
  jump_exc ^s =
    if s.handler < LENGTH s.stack then
      case LASTN (s.handler+1) s.stack of
      | Exc ss e n :: xs =>
          SOME (s with <| handler     := n
                        ; locals      := e
                        ; stack       := xs
                        ; locals_size := ss|>)
      | _ => NONE
    else NONE`;

val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (mk_wf (inter env name_set))
    else NONE`

val cut_state_def = Define `
  cut_state names ^s =
    case cut_env names s.locals of
    | NONE => NONE
    | SOME env => SOME (s with locals := env)`;

val cut_state_opt_def = Define `
  cut_state_opt names s =
    case names of
    | NONE => SOME s
    | SOME names => cut_state names s`;

val pop_env_clock = Q.prove(
  `(pop_env s = SOME s1) ==> (s1.clock = s.clock)`,
  full_simp_tac(srw_ss())[pop_env_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val push_env_clock = Q.prove(
  `(push_env env b s).clock = s.clock`,
  Cases_on `b` \\ full_simp_tac(srw_ss())[push_env_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val find_code_def = Define `
  (find_code (SOME p) args code ssize =
     case lookup p code of
     | NONE => NONE
     | SOME (arity,exp) =>
        if LENGTH args = arity
        then SOME (args,exp,lookup p ssize)
        else NONE)
∧ (find_code NONE args code ssize =
     if args = [] then NONE else
       case LAST args of
       | CodePtr loc =>
           (case sptree$lookup loc code of
            | NONE => NONE
            | SOME (arity,exp) =>
               if LENGTH args = arity + 1
               then SOME (FRONT args,exp,lookup loc ssize)
               else NONE)
       | other => NONE)`

val isBool_def = Define`
  isBool b (Block _ tag []) = (bool_to_tag b = tag)
∧ isBool _ _                = F
`;

Definition install_sfs_def[simp]:
  install_sfs op ^s = s with safe_for_space := (op ≠ closLang$Install ∧ s.safe_for_space)
End

Definition evaluate_def:
  (evaluate (Skip,^s) = (NONE,s)) /\
  (evaluate (Move dest src,s) =
     case get_var src s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME v => (NONE, set_var dest v s)) /\
  (evaluate (Assign dest op args names_opt,s) =
     if op_requires_names op /\ IS_NONE names_opt then (SOME (Rerr(Rabort Rtype_error)),s) else
     case cut_state_opt names_opt s of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME s =>
       (case get_vars args s.locals of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME xs => (case do_app op xs s of
                      | Rerr e => (SOME (Rerr e),flush_state T (install_sfs op s))
                      | Rval (v,s) =>
                        (NONE, set_var dest v (install_sfs op s))))) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),flush_state T s)
                    else (NONE,dec_clock s)) /\
  (evaluate (MakeSpace k names,s) =
     case cut_env names s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME env => (NONE,add_space (s with locals := env) k)) /\
  (evaluate (Raise n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x =>
       (case jump_exc s of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME s => (SOME (Rerr(Rraise x)),s))) /\
  (evaluate (Return n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x => (SOME (Rval x),flush_state F s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If n c1 c2,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
                        (* no time stamp *)
     | SOME x => if isBool T x then evaluate (c1,s) else
                 if isBool F x then evaluate (c2,s) else
                   (SOME (Rerr(Rabort Rtype_error)),s)) /\
  (evaluate (Call ret dest args handler,s) =
     case get_vars args s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME xs =>
       (case find_code dest xs s.code s.stack_frame_sizes of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME (args1,prog,ss) =>
          (case ret of
           | NONE (* tail call *) =>
             if handler = NONE then
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     flush_state T s)
               else
                 (case evaluate (prog, call_env args1 ss (dec_clock s)) of
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME (Rerr(Rabort Rtype_error)),s)
           | SOME (n,names) (* returning call, returns into var n *) =>
             (case cut_env names s.locals of
              | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
              | SOME env =>
                let s1 = call_env args1 ss
                        (push_env env (IS_SOME handler) (dec_clock s))
                in if s.clock = 0
                   then (SOME (Rerr(Rabort Rtimeout_error)),
                        s1 with <| stack := [] ; locals := LN |>)
                   else (case fix_clock s1 (evaluate (prog, s1)) of
                         | (SOME (Rval x),s2) =>
                           (case pop_env s2 of
                            | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                            | SOME s1 => (NONE, set_var n x s1))
                         | (SOME (Rerr(Rraise x)),s2) =>
                           (* if handler is present, then handle exc *)
                           (case handler of
                            | NONE => (SOME (Rerr(Rraise x)),s2)
                            | SOME (n,h) => evaluate (h, set_var n x s2))
                         | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                         | res => res)))))
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure prog_size)
                          (\(xs,s). (s.clock,xs)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ imp_res_tac fix_clock_IMP
  \\ imp_res_tac (GSYM fix_clock_IMP)
  \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,push_env_clock, call_env_def,LET_THM]
  >- fs [LESS_OR_EQ,dec_clock_def]
  \\ decide_tac
End

val evaluate_ind = theorem"evaluate_ind";

val evaluate_safe_def = Define`
  evaluate_safe c s = let (x,s1) = evaluate (c,s)
                      in s1.safe_for_space
`;

val evaluate_peak_def = Define`
  evaluate_peak c s = let (x,s1) = evaluate (c,s)
                      in s1.peak_heap_length
`;

(* We prove that the clock never increases. *)

val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def };
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def };
val op_thms = { nchotomy = closLangTheory.op_nchotomy, case_def = closLangTheory.op_case_def };
val v_thms = { nchotomy = theorem"v_nchotomy", case_def = definition"v_case_def" };
val ref_thms = { nchotomy = closSemTheory.ref_nchotomy, case_def = closSemTheory.ref_case_def };
val ffi_result_thms = { nchotomy = ffiTheory.ffi_result_nchotomy, case_def = ffiTheory.ffi_result_case_def };
val word_size_thms = { nchotomy = astTheory.word_size_nchotomy, case_def = astTheory.word_size_case_def };
val eq_result_thms = { nchotomy = semanticPrimitivesTheory.eq_result_nchotomy, case_def = semanticPrimitivesTheory.eq_result_case_def };
val case_eq_thms = LIST_CONJ (pair_case_eq::bool_case_eq::(List.map prove_case_eq_thm
  [list_thms, option_thms, op_thms, v_thms, ref_thms, word_size_thms, eq_result_thms,
   ffi_result_thms]))
  |> curry save_thm"case_eq_thms";

Theorem do_stack_clock:
   (dataSem$do_stack op args s1).clock = s1.clock
Proof
  rw[do_stack_def] >>
  PURE_TOP_CASE_TAC >> rw[] >>
  PURE_TOP_CASE_TAC >> rw[]
QED

Theorem do_app_clock:
   (dataSem$do_app op args s1 = Rval (res,s2)) ==> s2.clock <= s1.clock
Proof
  rw[ do_app_def
    , do_app_aux_def
    , do_space_def
    , consume_space_def
    , do_install_def
    , case_eq_thms
    , PULL_EXISTS
    , with_fresh_ts_def
    , UNCURRY
    , check_lim_def
    ]
  \\ rw[do_stack_clock]
QED

Theorem evaluate_clock:
 !xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  recInduct evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[ set_var_def  , cut_state_opt_def , cut_state_def
                         , call_env_def , dec_clock_def     , add_space_def
                         , jump_exc_def , push_env_clock    , flush_state_def]
  \\ rw[] >> rfs[]
  \\ fs [CaseEq"option"] \\ rw [] \\ fs [] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  imp_res_tac pop_env_clock >>
  imp_res_tac do_app_clock >>
  imp_res_tac do_app_clock >> fs[] >>
  every_case_tac >> rw[] >> simp[] >> rfs[]
  \\ rpt (pairarg_tac \\ fs [CaseEq"bool"]) \\ rveq \\ fs []
  \\ imp_res_tac fix_clock_IMP >> fs[]
  \\ full_simp_tac(srw_ss())[ set_var_def  , cut_state_opt_def , cut_state_def
                            , call_env_def , dec_clock_def     , add_space_def
                            , jump_exc_def , push_env_clock    , flush_state_def]
  \\ fs []
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate (xs,s)) = evaluate (xs,s)
Proof
  Cases_on `evaluate (xs,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]
QED

(* Finally, we remove fix_clock from the induction and definition theorems. *)

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

(* observational semantics *)

val initial_state_def = Define`
  initial_state ffi code coracle cc stamps lims ss k = <|
    locals := LN
  ; locals_size := SOME 0
  ; stack := []
  ; stack_max := SOME 1
  ; global := NONE
  ; handler := 0
  ; refs := LN
  ; clock := k
  ; code := code
  ; compile := cc
  ; compile_oracle := coracle
  ; ffi := ffi
  ; space := 0
  ; tstamps := if stamps then SOME 0 else NONE
  ; safe_for_space := if stamps then T else F
  ; peak_heap_length := 0
  ; stack_frame_sizes := ss
  ; limits := lims
  |>`;

val semantics_def = Define`
  semantics init_ffi code coracle cc lims ss start  =
  let p = Call NONE (SOME start) [] NONE in
  let init = initial_state init_ffi code coracle cc T lims ss in
    if ∃k. case FST(evaluate (p,init k)) of
             | SOME (Rerr e) => e ≠ Rabort Rtimeout_error /\ (!f. e ≠ Rabort(Rffi_error f))
             | NONE => T | _ => F
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate (p,init k) = (SOME r,s) ∧
        (case r of
         | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
         | Rval _ => outcome = Success
         | _ => F) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND (evaluate (p,init k))).ffi.io_events) UNIV))`;

Definition data_lang_safe_for_space_def:
  data_lang_safe_for_space init_ffi code (lims:dataSem$limits) (ss:num num_map) start =
    !ck.
      let p = Call NONE (SOME start) [] NONE in
      let init = initial_state init_ffi code ARB ARB T lims ss in
      let (res,s) = dataSem$evaluate (p,(init ck): (unit,'ffi) dataSem$state) in
        s.safe_for_space
End

Definition compute_limits_def:
  compute_limits len_bits a64 fpops fptops stack_heap_limit =
     <| stack_limit := FST stack_heap_limit
      ; heap_limit := SND stack_heap_limit
      ; length_limit := len_bits
      ; arch_64_bit := a64
      ; has_fp_ops := fpops
      ; has_fp_tops := fptops
      |>
End

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
