(*
  The formal semantics of dataLang
*)
open preamble data_simpTheory data_liveTheory data_spaceTheory dataLangTheory closSemTheory;


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

val _ = Datatype `
  stack = Env (v num_map)
        | Exc (v num_map) num`;

val _ = Datatype `
  state =
    <| locals  : v num_map
     ; stack   : stack list
     ; global  : num option
     ; handler : num
     ; refs    : num |-> v ref
     ; compile : 'c -> (num # num # dataLang$prog) list -> (word8 list # word64 list # 'c) option
     ; compile_oracle : num -> 'c # (num # num # dataLang$prog) list
     ; clock   : num
     ; code    : (num # dataLang$prog) num_map
     ; ffi     : 'ffi ffi_state
     ; space   : num
     ; tstamps : num option |> `

val s = ``(s:('c,'ffi) dataSem$state)``

val vs = ``(vs:dataSem$v list)``


val add_space_def = Define `
  add_space ^s k = s with space := k`;

val consume_space_def = Define `
  consume_space k ^s =
    if s.space < k then NONE else SOME (s with space := s.space - k)`;

val do_space_def = Define `
  do_space op l ^s =
    if op_space_reset op then SOME (s with space := 0)
    else if op_space_req op l = 0 then SOME s
         else consume_space (op_space_req op l) s`;

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
    case (FLOOKUP refs n1, FLOOKUP refs n2) of
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

val _ = Parse.temp_overload_on("Error",``(Rerr(Rabort Rtype_error)):(dataSem$v#('c,'ffi) dataSem$state, dataSem$v)result``)

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
                             code := union s.code (fromAList progs)
                           ; compile_oracle := new_oracle |>
                        in
                          Rval (CodePtr k, s')
                      else Rerr(Rabort Rtype_error)
                  | _ => Rerr(Rabort Rtype_error))
            | _ => Rerr(Rabort Rtype_error))
       | _ => Rerr(Rabort Rtype_error))`;

val list_to_v_def = Define `
  list_to_v [] = Block 0 nil_tag [] /\
  list_to_v (v::vs) = Block 0 cons_tag [v; list_to_v vs]`;

val list_to_v_alt_def = Define`
  list_to_v_alt t [] = t
∧ list_to_v_alt t (h::l) = Block 0 cons_tag [h;list_to_v_alt t l]`;

val with_fresh_ts_def = Define`
  with_fresh_ts ^s f = case s.tstamps of
                          SOME ts => f ts (s with <| tstamps := SOME (ts + 1) |>)
                        | NONE    => f 0 s
`;

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
                          then with_fresh_ts s (λts s'. Rval (Block ts n vs, s'))
                          else Error
             | _ => Error)
         | _ => Error)
    | (RefByte f, xs) =>
        (case xs of
          | [Number i; Number b] =>
            if 0 ≤ i ∧ (∃w:word8. b = & (w2n w)) then
              let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
                Rval (RefPtr ptr, s with refs := s.refs |+
                  (ptr, ByteArray f (REPLICATE (Num i) (i2w b))))
            else Rerr (Rabort Rtype_error)
          | _ => Rerr (Rabort Rtype_error))
    | (Global n, _)      => Rerr (Rabort Rtype_error)
    | (SetGlobal n, _)   => Rerr (Rabort Rtype_error)
    | (AllocGlobal, _)   => Rerr (Rabort Rtype_error)
    | (String _, _)      => Rerr (Rabort Rtype_error)
    | (FromListByte, _)  => Rerr (Rabort Rtype_error)
    | (ConcatByteVec, _) => Rerr (Rabort Rtype_error)
    | (CopyByte T, _)    => Rerr (Rabort Rtype_error)
    (* bvl part *)
    | (Cons tag,xs) => (if xs = []
                        then Rval (Block 0 tag [],s)
                        else with_fresh_ts s (λts s'. Rval (Block ts tag xs, s')))
    | (ConsExtend tag,Block _ _ xs'::Number lower::Number len::Number tot::xs) =>
        if lower < 0 ∨ len < 0 ∨ lower + len > &LENGTH xs' ∨
           tot = 0 ∨ tot ≠ &LENGTH xs + len then
          Error
        else with_fresh_ts s (λts s'.
          Rval (Block ts tag (xs++TAKE (Num len) (DROP (Num lower) xs')), s'))
    | (ConsExtend tag,_) => Error
    | (El,[Block _ tag xs;Number i]) =>
        if 0 ≤ i ∧ Num i < LENGTH xs then Rval (EL (Num i) xs, s) else Error
    | (ListAppend,[x1;x2]) =>
        (case (v_to_list x1, v_to_list x2) of
         | (SOME xs, SOME ys) => Rval (list_to_v (xs ++ ys),s)
         | _ => Error)
    | (LengthBlock,[Block _ tag xs]) =>
        Rval (Number (&LENGTH xs), s)
    | (Length,[RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ValueArray xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (LengthByte,[RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ByteArray _ xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (RefArray,[Number i;v]) =>
        if 0 ≤ i then
          let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
            Rval (RefPtr ptr, s with refs := s.refs |+
              (ptr,ValueArray (REPLICATE (Num i) v)))
         else Error
    | (DerefByte,[RefPtr ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray _ ws) =>
            (if 0 ≤ i ∧ i < &LENGTH ws
             then Rval (Number (& (w2n (EL (Num i) ws))),s)
             else Error)
         | _ => Error)
    | (UpdateByte,[RefPtr ptr; Number i; Number b]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray f bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ (∃w:word8. b = & (w2n w))
             then
               Rval (Unit, s with refs := s.refs |+
                 (ptr, ByteArray f (LUPDATE (i2w b) (Num i) bs)))
             else Error)
         | _ => Error)
    | (CopyByte F,[RefPtr src; Number srcoff; Number len; RefPtr dst; Number dstoff]) =>
        (case (FLOOKUP s.refs src, FLOOKUP s.refs dst) of
         | (SOME (ByteArray _ ws), SOME (ByteArray fl ds)) =>
           (case copy_array (ws,srcoff) len (SOME(ds,dstoff)) of
                              (* no time-stamp *)
            | SOME ds => Rval (Unit, s with refs := s.refs |+ (dst, ByteArray fl ds))
            | NONE => Error)
         | _ => Error)
    | (TagEq n,[Block _ tag xs]) =>
        Rval (Boolv (tag = n), s)
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
        let ptr = (LEAST ptr. ~(ptr IN FDOM s.refs)) in
          Rval (RefPtr ptr, s with refs := s.refs |+ (ptr,ValueArray xs))
    | (Deref,[RefPtr ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (EL (Num i) xs, s)
             else Error)
         | _ => Error)
    | (Update,[RefPtr ptr; Number i; x]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (Unit, s with refs := s.refs |+
                              (ptr,ValueArray (LUPDATE x (Num i) xs)))
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
        (case (FLOOKUP s.refs cptr, FLOOKUP s.refs ptr) of
         | SOME (ByteArray T cws), SOME (ByteArray F ws) =>
           (case call_FFI s.ffi n cws ws of
            | FFI_return ffi' ws' =>
                Rval (Unit,
                      s with <| refs := s.refs |+ (ptr,ByteArray F ws')
                              ; ffi   := ffi'|>)
            | FFI_final outcome =>
                Rerr (Rabort (Rffi_error outcome)))
         | _ => Error)
    | (FP_top top, ws) =>
        (case ws of
         | [Word64 w1; Word64 w2; Word64 w3] =>
            (Rval (Word64 (fp_top top w1 w2 w3),s))
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
          (case FLOOKUP s.refs ptr of
           | SOME (ByteArray _ ws) =>
               Rval (Boolv (0 <= i /\ (if loose then $<= else $<) i (& LENGTH ws)),s)
           | _ => Error)
         | _ => Error)
    | (BoundsCheckArray,xs) =>
        (case xs of
         | [RefPtr ptr; Number i] =>
          (case FLOOKUP s.refs ptr of
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


val do_app_def = Define `
  do_app op vs ^s =
    if op = Install then do_install vs s else
    if MEM op [Greater; GreaterEq] then Error else
    case do_space op (LENGTH vs) s of
    | NONE => Error
    | SOME s1 => do_app_aux op vs s1`


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

val call_env_def = Define `
  call_env args ^s =
    s with <| locals := fromList args |>`;

val push_env_def = Define `
  (push_env env F ^s = s with <| stack := Env env :: s.stack |>) /\
  (push_env env T ^s = s with <| stack := Exc env s.handler :: s.stack
                               ; handler := LENGTH s.stack |>)`;

val pop_env_def = Define `
  pop_env ^s =
    case s.stack of
    | (Env e::xs) => SOME (s with <| locals := e ; stack := xs |>)
    | (Exc e n::xs) => SOME (s with <| locals := e; stack := xs ; handler := n |>)
    | _ => NONE`;

val jump_exc_def = Define `
  jump_exc ^s =
    if s.handler < LENGTH s.stack then
      case LASTN (s.handler+1) s.stack of
      | Exc e n :: xs =>
          SOME (s with <| handler := n ; locals := e ; stack := xs |>)
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
       | other => NONE)`

val isBool_def = Define`
  isBool b (Block _ tag []) = (bool_to_tag b = tag)
∧ isBool _ _                = F
`;

val evaluate_def = tDefine "evaluate" `
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
                      | Rerr e => (SOME (Rerr e),call_env [] s with stack := [])
                      | Rval (v,s) =>
                        (NONE, set_var dest v s)))) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (evaluate (MakeSpace k names,s) =
     case cut_env names s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME env => (NONE,add_space s k with locals := env)) /\
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
     | SOME x => (SOME (Rval x),call_env [] s)) /\
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
       (case find_code dest xs s.code of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME (args1,prog) =>
          (case ret of
           | NONE (* tail call *) =>
             if handler = NONE then
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     call_env [] s with stack := [])
               else
                 (case evaluate (prog, call_env args1 (dec_clock s)) of
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME (Rerr(Rabort Rtype_error)),s)
           | SOME (n,names) (* returning call, returns into var n *) =>
             (case cut_env names s.locals of
              | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
              | SOME env =>
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     call_env [] s with stack := [])
               else
                 (case fix_clock s (evaluate (prog, call_env args1
                        (push_env env (IS_SOME handler) (dec_clock s)))) of
                  | (SOME (Rval x),s2) =>
                     (case pop_env s2 of
                      | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                      | SOME s1 => (NONE, set_var n x s1))
                  | (SOME (Rerr(Rraise x)),s2) =>
                     (case handler of (* if handler is present, then handle exc *)
                      | NONE => (SOME (Rerr(Rraise x)),s2)
                      | SOME (n,h) => evaluate (h, set_var n x s2))
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | res => res)))))`
  (WF_REL_TAC `(inv_image (measure I LEX measure prog_size)
                          (\(xs,s). (s.clock,xs)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ imp_res_tac fix_clock_IMP
  \\ imp_res_tac (GSYM fix_clock_IMP)
  \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,push_env_clock, call_env_def]
  \\ decide_tac);

val evaluate_ind = theorem"evaluate_ind";

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
    ,UNCURRY]
  \\ rw[]
QED

Theorem evaluate_clock:
 !xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  recInduct evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[set_var_def,cut_state_opt_def,cut_state_def,call_env_def,dec_clock_def,add_space_def,jump_exc_def,push_env_clock] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  imp_res_tac pop_env_clock >>
  imp_res_tac do_app_clock >>
  imp_res_tac do_app_clock >> fs[] >>
  every_case_tac >> rw[] >> simp[] >> rfs[] >>
  first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ imp_res_tac fix_clock_IMP >> full_simp_tac(srw_ss())[] >> simp[] >> rfs[]
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate (xs,s)) = evaluate (xs,s)
Proof
  Cases_on `evaluate (xs,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]
QED

Theorem fix_clock_evaluate_call:
   fix_clock s (evaluate (prog,call_env args1 (push_env env h (dec_clock s)))) =
   (evaluate (prog,call_env args1 (push_env env h (dec_clock s))))
Proof
  Cases_on `(evaluate (prog,call_env args1 (push_env env h (dec_clock s))))`
  >> fs [fix_clock_def]
  >> imp_res_tac evaluate_clock
  >> fs[MIN_DEF,theorem "state_component_equality",call_env_def,dec_clock_def,push_env_clock]
  >> imp_res_tac push_env_clock
QED

(* Finally, we remove fix_clock from the induction and definition theorems. *)

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate,fix_clock_evaluate_call] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate,fix_clock_evaluate_call] evaluate_ind);

(* observational semantics *)

val initial_state_def = Define`
  initial_state ffi code coracle cc k = <|
    locals := LN
  ; stack := []
  ; global := NONE
  ; handler := 0
  ; refs := FEMPTY
  ; clock := k
  ; code := code
  ; compile := cc
  ; compile_oracle := coracle
  ; ffi := ffi
  ; space := 0
  |>`;

val semantics_def = Define`
  semantics init_ffi code coracle cc start =
  let p = Call NONE (SOME start) [] NONE in
  let init = initial_state init_ffi code coracle cc in
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

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
