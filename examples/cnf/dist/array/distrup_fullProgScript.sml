(*
  The full setup around distrup core
*)
Theory distrup_fullProg
Libs
  preamble basis wordsLib
Ancestors
  distrup_arrayProg words byte

val _ = hide_environments true;

val _ = translation_extends "distrup_arrayProg";

(* Helper functions *)
Definition string_to_int_def:
  string_to_int s =
  let
    b0 = &ORD (strsub s 0);
    b1 = &ORD (strsub s 1);
    b2 = &ORD (strsub s 2);
    b3 = &ORD (strsub s 3);
    raw = b0 + b1 * 256 + b2 * 65536 + b3 * (16777216:int)
  in
    if b3 >= 128 then raw - 4294967296 else raw
End

val res = translate string_to_int_def;

Theorem string_to_int_pre:
  string_to_int_side s ⇔
  4 ≤ strlen s
Proof
  rw[fetch "-" "string_to_int_side_def"]
QED

val _ = string_to_int_pre |> update_precondition;

(* Array-level helpers *)
Quote add_cakeml:
  fun get_byte arr i = Word8.toInt (Unsafe.w8sub arr i);

  (* Little-endian: read 4 bytes as signed int starting at index i *)
  fun get_int arr i =
    let
      val b3 = get_byte arr (i+3)
      val raw = get_byte arr i +
                get_byte arr (i+1) * 256 +
                get_byte arr (i+2) * 65536 +
                b3 * 16777216
    in
      if b3 >= 128
      then raw - 4294967296
      else raw
    end;

  fun read_ints arr len i =
    if i >= len then [] else get_int arr (i * 4) :: read_ints arr len (i + 1);

  fun get_u64 arr i =
    get_byte arr i +
    get_byte arr (i+1) * 256 +
    get_byte arr (i+2) * 65536 +
    get_byte arr (i+3) * 16777216 +
    get_byte arr (i+4) * 4294967296 +
    get_byte arr (i+5) * 1099511627776 +
    get_byte arr (i+6) * 281474976710656 +
    get_byte arr (i+7) * 72057594037927936;

  fun read_ids arr len i =
    if i >= len then [] else get_u64 arr (i * 8) :: read_ids arr len (i + 1);

  fun ensure_size buf_arr needed =
    if Word8Array.length buf_arr < needed
    then Word8Array.array needed (Word8.fromInt 0)
    else buf_arr;
End

(* get_clause and get_hints read from the respective buffers,
  growing them as necessary *)
Quote add_cakeml:
  fun get_clause buf_arr trusted count_str =
    let
      val len = string_to_int count_str
      val arr = ensure_size buf_arr (len * 4)
      val hdr = String.str (Char.chr (if trusted then 1 else 0)) ^ count_str
      val _ = #(clause) hdr arr
    in
      (arr, Vector.fromList (read_ints arr len 0))
    end;

  fun get_hints buf_arr count_str =
    let
      val len = string_to_int count_str
      val arr = ensure_size buf_arr (len * 8)
      val _ = #(hints) count_str arr
    in
      (arr, read_ids arr len 0)
    end;
End

(* Fully parse a single step *)
Quote add_cakeml:
  fun parse_step step_arr buf_arr =
    let
      val _ = #(step) "" step_arr
      val c = Char.fromByte (Word8Array.sub step_arr 0)
    in
      case c of
        #"a" => (* PRODUCE *)
          let
            val id = get_u64 step_arr 1
            val nb_lits_str = Word8Array.substring step_arr 9 4
            val nb_hints_str = Word8Array.substring step_arr 13 4
            val (buf_arr, cl) = get_clause buf_arr False nb_lits_str
            val (buf_arr, hints) = get_hints buf_arr nb_hints_str
          in
            (buf_arr, Some (Lrup id cl hints))
          end
      | #"i" => (* IMPORT *)
          let
            val id = get_u64 step_arr 1
            val nb_lits_str = Word8Array.substring step_arr 9 4
            val (buf_arr, cl) = get_clause buf_arr True nb_lits_str
          in
            (buf_arr, Some (Import id cl))
          end
      | #"d" => (* DELETE *)
          let
            val nb_hints_str = Word8Array.substring step_arr 1 4
            val (buf_arr, hints) = get_hints buf_arr nb_hints_str
          in
            (buf_arr, Some (Del hints))
          end
      | #"V" => (buf_arr, Some Validateunsat)
      | _ => (buf_arr, None) (* Terminate or unknown *)
    end;
End

Definition pp_distrup_def:
  pp_distrup distrup =
  case distrup of
  | Del ls =>
      strlit"Del: IDs [" ^ concatWith (strlit " ") (MAP toString ls) ^ strlit "]"
  | Lrup n vc hints =>
      strlit"Lrup: ID " ^ toString n ^
      strlit " Clause [" ^ concatWith (strlit " ") (MAP toString (toList vc)) ^ strlit "]"^
      strlit " Hints [" ^ concatWith (strlit " ") (MAP toString hints) ^ strlit "]"
  | Import n vc =>
      strlit"Import: ID " ^ toString n ^
      strlit " Clause [" ^ concatWith (strlit " ") (MAP toString (toList vc)) ^ strlit "]"
  | ValidateUnsat =>
      strlit"ValidateUnsat"
End

val res = translate pp_distrup_def;

(* Wraps and removes exception handling *)
Quote add_cakeml:
  fun check_top lno instr st =
    (case st of
      None => (None, "")
    | Some (fml, carr, b) =>
        (case check_distrup_arr lno instr fml carr b of
          (fml, carr, b) => (Some (fml, carr, b), ""))
        handle Fail err =>
        (None, err));
End

(* The main loop *)
Quote add_cakeml:

fun do_callback res step_arr =
  let
    val _ = #(callback) res step_arr
  in
    ()
  end

fun loop step_arr buf_arr st lno =
  let
    val (buf_arr, result) = parse_step step_arr buf_arr
  in
    case result of
      None => () (* Terminate: C handles response after cml_main returns *)
    | Some instr =>
        let
          val (st, msg) = check_top lno instr st
          val res = case st of None => "0" ^ msg | Some _ => "1"
          val _ = do_callback res step_arr
        in
          loop step_arr buf_arr st (lno + 1)
        end
  end;

fun main () =
  let
    val step_arr = Word8Array.array 17 (Word8.fromInt 0)
    val buf_arr = Word8Array.array 0 (Word8.fromInt 0)
    val fml = Array.array 4096 None
    val carr = Word8Array.array 1024 (Word8.fromInt 0)
    val b = Word8.fromInt 1
  in
    loop step_arr buf_arr (Some (fml, carr, b)) 1
  end;

End

val main_call = ``Dlet unknown_loc Pany (App Opapp [Var (Short (strlit "main")); Con NONE []]) ``;;

val prog = get_ml_prog_state () |> get_prog;

val prog_tm = ``SNOC ^main_call ^prog`` |> EVAL |> rconc;

Definition distrup_prog_def:
  distrup_prog = ^prog_tm
End

(*----------------------------------------------------------------------*
   FFI model:
    - the state consists of two parts
       + what to wait for as the next C call
       + the list of pending inputs
    - we need to encode and decode this into/from the ‘:ffi’ type
 *----------------------------------------------------------------------*)

Type w8s = “:word8 list”;

(* what to wait for as the next C call *)
Datatype:
  wait_for = Step
           | Produce_clause w8s w8s
           | Produce_hints w8s
           | Produce_callback
           | Import_clause w8s
           | Import_callback
           | Delete_hints w8s
           | Delete_callback
           | Validate_UNSAT_callback
           | Terminate
End

(* each input is one of: *)
Datatype:
  input = Produce w8s w8s w8s
        | Import w8s w8s
        | Delete w8s w8s
        | Validate_UNSAT w8s
End

(* the state of the C code*)
Type state = “:wait_for # input list”;

(* encoding *)

Definition Bytes_def:
  Bytes (xs:word8 list) = List (MAP (Num o w2n) xs)
End

Definition Int_def:
  Int i = if i < 0 then Cons (Num (Num (ABS i))) (Num 0) else Num (Num i)
End

Definition WaitFor_def:
  WaitFor wf =
    case wf of
    | Step => Str (strlit "Step")
    | Produce_clause xs ys => Cons (Str (strlit "Produce_clause")) (Cons (Bytes xs) (Bytes ys))
    | Produce_hints xs => Cons (Str (strlit "Produce_hints")) (Bytes xs)
    | Produce_callback => Str (strlit "Produce_callback")
    | Import_clause xs => Cons (Str (strlit "Import_clause")) (Bytes xs)
    | Import_callback => Str (strlit "Import_callback")
    | Delete_hints xs => Cons (Str (strlit "Delete_hints")) (Bytes xs)
    | Delete_callback => Str (strlit "Delete_callback")
    | Validate_UNSAT_callback => Str (strlit "Validate_UNSAT_callback")
    | Terminate => Str (strlit "Terminate")
End

Definition Input_def:
  Input (Produce xs ys zs)  = Cons (Str (strlit "Produce"))
                                   (Cons (Bytes xs) (Cons (Bytes ys) (Bytes zs))) ∧
  Input (Import xs ys)      = Cons (Str (strlit "Import"))
                                   (Cons (Bytes xs) (Bytes ys)) ∧
  Input (Delete xs ys)      = Cons (Str (strlit "Delete"))
                                   (Cons (Bytes xs) (Bytes ys)) ∧
  Input (Validate_UNSAT xs) = Cons (Str (strlit "Validate_UNSAT")) (Bytes xs)
End

Definition State_def:
  State waif_for inputs =
    Cons (WaitFor waif_for)
         (List (MAP Input inputs))
End

Theorem Bytes_11:
  Bytes x = Bytes y ⇔ x = y
Proof
  gvs [Bytes_def] \\ eq_tac
  \\ rw [] \\ drule_at Any MAP_EQ_MAP_IMP \\ gvs []
QED

Theorem Int_11:
  Int x = Int y ⇔ x = y
Proof
  gvs [Int_def] \\ eq_tac \\ rw []
  \\ intLib.COOPER_TAC
QED

Theorem Input_11:
  Input x = Input y ⇔ x = y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [Input_def,Bytes_11,Int_11]
QED

Theorem WaitFor_11:
  WaitFor x = WaitFor y ⇔ x = y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [WaitFor_def,Bytes_11,Int_11]
QED

Theorem State_11:
  State x y = State x1 y1 ⇒ x = x1 ∧ y = y1
Proof
  fs [State_def] \\ gvs [WaitFor_11]
  \\ rw [] \\ drule_at Any MAP_EQ_MAP_IMP
  \\ gvs [Input_11]
QED

(* decoding *)

Definition dest_State_def:
  dest_State (x:ffi) = some res. State (FST res) (SND res) = x
End

Theorem dest_State_State[simp]:
  dest_State (State w inputs) = SOME (w, inputs)
Proof
  rewrite_tac [dest_State_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ reverse $ rw [FORALL_PROD]
  >- (irule_at Any EQ_REFL)
  \\ rename [‘FST x’] \\ Cases_on ‘x’ \\ gvs []
  \\ imp_res_tac State_11 \\ fs []
QED

(* next state *)

val imm_arg = “imm_arg:word8 list”
val arr_arg = “arr_arg:word8 list”

Definition write_bytes_def:
  write_bytes [] xs = [] ∧
  write_bytes xs [] = xs ∧
  write_bytes (x::xs) (y::ys) = (y:word8) :: write_bytes xs ys
End

Definition update_step_def:
  update_step ^imm_arg ^arr_arg Step inputs =
    (if LENGTH imm_arg ≠ 0 ∨ LENGTH arr_arg ≠ 17 then NONE else
       case inputs of
       | [] => SOME (FFIreturn (0w :: TL arr_arg) (State Terminate inputs))
       | (i::is) =>
         case i of
         | Produce xs ys zs =>
             let res = write_bytes arr_arg (n2w (ORD #"a") :: xs) in
               SOME (FFIreturn res (State (Produce_clause ys zs) is))
         | Import xs ys =>
             let res = write_bytes arr_arg (n2w (ORD #"i") :: xs) in
               SOME (FFIreturn res (State (Import_clause ys) is))
         | Delete xs ys =>
             let res = write_bytes arr_arg (n2w (ORD #"d") :: xs) in
               SOME (FFIreturn res (State (Delete_hints ys) is))
         | Validate_UNSAT xs =>
             let res = write_bytes arr_arg (n2w (ORD #"V") :: xs) in
               SOME (FFIreturn res (State Validate_UNSAT_callback is))) ∧
  update_step ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_clause_def:
  update_clause ^imm_arg ^arr_arg (Produce_clause ys zs) inputs =
    (SOME (FFIreturn (write_bytes arr_arg ys)
                     (State (Produce_hints zs) inputs))) ∧
  update_clause ^imm_arg ^arr_arg (Import_clause ys) inputs =
    (SOME (FFIreturn (write_bytes arr_arg ys)
                     (State Import_callback inputs))) ∧
  update_clause ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_hints_def:
  update_hints ^imm_arg ^arr_arg (Produce_hints zs) inputs =
    (SOME (FFIreturn (write_bytes arr_arg zs)
                     (State Produce_callback inputs))) ∧
  update_hints ^imm_arg ^arr_arg (Delete_hints zs) inputs =
    (SOME (FFIreturn (write_bytes arr_arg zs)
                     (State Delete_callback inputs))) ∧
  update_hints ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_callback_def:
  update_callback ^imm_arg ^arr_arg Produce_callback inputs =
    (SOME (FFIreturn arr_arg (State Step inputs))) ∧
  update_callback ^imm_arg ^arr_arg Import_callback inputs =
    (SOME (FFIreturn arr_arg (State Step inputs))) ∧
  update_callback ^imm_arg ^arr_arg Delete_callback inputs =
    (SOME (FFIreturn arr_arg (State Step inputs))) ∧
  update_callback ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_def:
  update ffi_name imm_arg arr_arg s =
    case dest_State s of
    | NONE => NONE
    | SOME (waif_for, inputs) =>
        if ffi_name = strlit "step" then
          update_step imm_arg arr_arg waif_for inputs
        else if ffi_name = strlit "clause" then
          update_clause imm_arg arr_arg waif_for inputs
        else if ffi_name = strlit "hints" then
          update_hints imm_arg arr_arg waif_for inputs
        else if ffi_name = strlit "callback" then
          update_callback imm_arg arr_arg waif_for inputs
        else NONE
End

(* definition of separation logic assertion CUSTOM_FFI *)

Definition names_def:
  names = [«step»; «clause»; «hints»; «callback»]
End

Definition CUSTOM_FFI_def:
  CUSTOM_FFI waif_for inputs events =
    one (FFI_part (State waif_for inputs) update names events)
End

(* verification of FFI calling functions *)

Definition is_final_event_def:
  is_final_event event ⇔
    ∃xs. event = IO_event (ExtCall «step») [] xs ∧ SND (HD xs) = 0w
End

Theorem parse_step_NIL:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step [] events *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 final_event.
         CUSTOM_FFI Terminate [] (events ++ [final_event]) *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ is_final_event final_event ∧
               ∃none.
                 OPTION_TYPE INT NONE none ∧
                 res = Conv NONE [buf_arrv; none]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘final_event = IO_event (ExtCall «step») [] (ZIP (step_arr,0w::TL step_arr))’ >>
  xlet ‘POSTv res.
    CUSTOM_FFI Terminate [] (events ++ [final_event]) * W8ARRAY step_arrv (0w :: TL step_arr)’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘emp’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet ‘POSTv res. W8ARRAY step_arrv (0w::TL step_arr) *
           CUSTOM_FFI Terminate [] (events ++ [final_event]) *
           cond (OPTION_TYPE INT NONE res)’
  >- (xcon >> gvs [OPTION_TYPE_def] >> xsimpl) >>
  xcon >>
  xsimpl >>
  gvs [LENGTH_EQ_NUM_compute] >>
  qexists_tac ‘final_event’ >>
  xsimpl >>
  unabbrev_all_tac >>
  gvs [is_final_event_def]
QED

Definition is_unsat_event_def:
  is_unsat_event event ⇔
    ∃xs. event = IO_event (ExtCall «step») [] xs ∧ SND (HD xs) = n2w (ORD #"V")
End

Theorem parse_step_Validate_UNSAT:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Validate_UNSAT xs :: inputs) events *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 unsat_event.
         CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ is_unsat_event unsat_event ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME ValidateUnsat) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘unsat_event = IO_event (ExtCall «step») [] (ZIP (step_arr,write_bytes step_arr (86w::xs)))’ >>
  xlet ‘POSTv res.
    CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
    W8ARRAY step_arrv (write_bytes step_arr (n2w (ORD #"V")::xs))’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘emp’  >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  Cases_on ‘step_arr’ >> gvs [write_bytes_def] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet ‘POSTv res. CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
           W8ARRAY step_arrv (86w::write_bytes t xs) *
           cond (DISTRUP_DISTRUP_TYPE ValidateUnsat res)’
  >- (xcon >> gvs [DISTRUP_DISTRUP_TYPE_def] >> xsimpl) >>
  xlet_auto >- (xsimpl >> xcon >> xsimpl) >>
  xcon >>
  xsimpl >>
  gvs [LENGTH_EQ_NUM_compute] >>
  qexists_tac ‘unsat_event’ >>
  xsimpl >>
  unabbrev_all_tac >>
  rewrite_tac [OPTION_TYPE_def] >>
  gvs [is_unsat_event_def] >>
  cheat (* easy *)
QED

Theorem get_u64_spec:
  ∀xs k ys nv.
    NUM k nv ∧ k = LENGTH xs ⇒
    app (p:'ffi ffi_proj) get_u64_v [step_arrv; nv]
        (W8ARRAY step_arrv (xs ++ word_to_bytes (id : word64) F ++ ys))
        (POSTv res.
          W8ARRAY step_arrv (xs ++ word_to_bytes id F ++ ys) *
          cond (NUM (w2n id) res))
Proof
  cheat
QED

Definition read_ints_def:
  read_ints k xs =
    if k = 0:num then [] else
      w2i (word_of_bytes F 0w (TAKE 4 xs) : word32) :: read_ints (k-1) (DROP 4 xs)
End

Definition is_produce_events_def:
  is_produce_events id cl produce_events ⇔
    ∃xs1 xs2 xs3 clen.
      produce_events = [IO_event (ExtCall «step»)   [] xs1;
                        IO_event (ExtCall «clause») [] xs2;
                        IO_event (ExtCall «hints»)  [] xs3] ∧
      LENGTH xs1 = 17 ∧
      SND (HD xs1) = n2w (ORD #"a") ∧
      word_to_bytes (n2w id : word64) F = MAP SND (TAKE 8 (DROP 1 xs1)) ∧
      word_to_bytes (clen   : word32) F = MAP SND (TAKE 4 (DROP 9 xs1)) ∧
      w2n clen * 4 ≤ LENGTH xs2 ∧
      cl = Vector (read_ints (w2n clen) (MAP SND xs2))
End

Theorem parse_step_Produce:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Produce xs ys zs :: inputs) events *
     W8ARRAY buf_arrv buf_arr *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 buf_arrv buf_arr produce_events cl hs id.
         CUSTOM_FFI Produce_callback inputs (events ++ produce_events) *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧
               is_produce_events id cl produce_events ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Lrup id cl hs)) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  cheat (*
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘a1 = [n2w (ORD #"a")] ++
                    word_to_bytes (id : word64) F ++
                    word_to_bytes (n2w (LENGTH c) : word32) F ++
                    word_to_bytes (n2w (LENGTH h) : word32) F’ >>
  qabbrev_tac ‘event1 = IO_event (ExtCall «step») [] (ZIP (step_arr,a1))’ >>
  xlet ‘POSTv res.
      CUSTOM_FFI (Produce_clause id c h) inputs (events ++ [event1]) *
      W8ARRAY buf_arrv buf_arr *
      W8ARRAY step_arrv a1’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘W8ARRAY buf_arrv buf_arr’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet ‘POSTv res.
    W8ARRAY step_arrv a1 *
    W8ARRAY buf_arrv buf_arr *
    CUSTOM_FFI (Produce_clause id c h) inputs (events ++ [event1]) *
    cond (NUM (w2n id) res)’
  >-
   (xapp >> xsimpl >>
    gvs [LENGTH_EQ_NUM_compute,PULL_EXISTS,Abbr‘a1’] >>
    rewrite_tac [GSYM APPEND_ASSOC] >>
    irule_at Any EQ_REFL >> fs []) >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- (xcon \\ xsimpl) >>
  xlet ‘POSTv res.
    SEP_EXISTS buf_arrv1 buf_arr1 cl event2.
      W8ARRAY step_arrv a1 *
      W8ARRAY buf_arrv1 buf_arr1 *
      CUSTOM_FFI (Produce_hints id h) inputs (events ++ [event1; event2]) *
      cond (∃v. res = Conv NONE [buf_arrv1; v] ∧
                VECTOR_TYPE INT cl v)’
  >- cheat >>
  gvs [] >>
  xmatch >>
  xlet ‘POSTv res.
    SEP_EXISTS buf_arrv1 buf_arr1 hs event3.
      W8ARRAY step_arrv a1 *
      W8ARRAY buf_arrv1 buf_arr1 *
      CUSTOM_FFI (Produce_callback id) inputs (events ++ [event1; event2; event3]) *
      cond (∃v. res = Conv NONE [buf_arrv1; v] ∧
                LIST_TYPE NUM hs v)’
  >- cheat >>
  gvs [] >>
  xmatch >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xcon >> xsimpl >>
  simp [PULL_EXISTS] >> xsimpl >>
  qexists ‘[event1; event2; event3]’ >> xsimpl >>
  gvs [] >>
  gvs [OPTION_TYPE_def, DISTRUP_DISTRUP_TYPE_def] >>
  first_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any >>
  simp [GSYM PULL_EXISTS] >>
  conj_tac
  >-
   (unabbrev_all_tac >>
    gvs [word_to_bytes_def] >>
    simp [EVAL “word_to_bytes_aux 8 id F”,
          EVAL “word_to_bytes_aux 4 id F”]) >>
  gvs [is_produce_events_def,Abbr‘event1’] >>
  cheat *)
QED

Inductive events_ok:
[~init:]
  events_ok [] (REPLICATE n NONE, REPLICATE k 0w, b)
[~produce:]
  events_ok events (fmlls, Clist, b) ∧
  is_produce_events n vc produce_events ∧
  (* TODO: constrain output_event *)
  check_distrup_list (Lrup n vc hints) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  events_ok (events ++ produce_events ++ [output_event]) (fmlls', Clist', b')
End

Definition full_events_ok_def:
  full_events_ok events ⇔
    ∃xs final fmlls Clist b.
      events = xs ++ [final] ∧
      events_ok xs (fmlls, Clist, b) ∧
      is_final_event final
End

Theorem loop_spec:
  ∀inputs lno lnov events fmlls fmllsv Clist step_arr step_arrv buf_arrv stv.
    NUM lno lnov ∧
    LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
    bnd_fml fmlls (LENGTH Clist) ∧
    events_ok events (fmlls, Clist, b) ∧
    LENGTH step_arr = 17 ⇒
    app (p:'ffi ffi_proj) loop_v [step_arrv; buf_arrv; stv; lnov]
        (CUSTOM_FFI Step inputs events *
         ARRAY fmlv fmllsv *
         W8ARRAY Carrv Clist *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr)
        (POSTv res.
           SEP_EXISTS step_arr1 buf_arrv buf_arr new_events fmlls1 Clist1 b1.
             CUSTOM_FFI Terminate [] new_events *
             ARRAY fmlv fmllsv *
             W8ARRAY Carrv Clist *
             W8ARRAY buf_arrv buf_arr *
             W8ARRAY step_arrv step_arr1 *
             cond (full_events_ok new_events))
Proof
  Induct
  >-
   (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet_auto_spec (SOME parse_step_NIL)
    >-
     (xsimpl >>
      rw [PULL_EXISTS] >>
      first_x_assum $ irule_at Any >> xsimpl) >>
    gvs [] >> xmatch >>
    gvs [OPTION_TYPE_def] >>
    xmatch >> xcon >>
    xsimpl >>
    qexistsl [‘buf_arrv’,‘buf_arr’,‘(events ++ [final_event])’] >>
    xsimpl >>
    simp [full_events_ok_def] >>
    first_x_assum $ irule_at Any) >>
  Cases_on ‘h’
  >~ [‘Produce xs ys zs’] >-
   (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr produce_events cl hs i.
              CUSTOM_FFI Produce_callback inputs (events ++ produce_events) *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              ARRAY fmlv fmllsv *
              W8ARRAY Carrv Clist *
              cond (LENGTH step_arr1 = 17 ∧
                    is_produce_events i cl produce_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Lrup i cl hs)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Produce >>
      qrefinel [‘_’,‘zs’,‘ys’,‘xs’,‘step_arr’,‘inputs’,‘events’,‘buf_arr’] >>
      xsimpl >>
      rw [] >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any >>
      xsimpl) >>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    cheat)
  >~ [‘Import xs ys’] >- cheat
  >~ [‘Delete xs ys’] >- cheat
  >~ [‘Validate_UNSAT’] >- cheat
QED

Theorem main_spec:
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
    (CUSTOM_FFI Step inputs [])
    (POSTv res.
       SEP_EXISTS events.
         CUSTOM_FFI Terminate [] events *
         cond (full_events_ok events))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xmatch  >> gvs [] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xapp >>
  qexists ‘emp’ >> xsimpl >>
  qrefinel [‘inputs’,‘_’,‘_’,‘[]’] >>
  xsimpl >>
  qexists ‘av’ >>
  qexists ‘REPLICATE 4096 (Conv (SOME (TypeStamp «None» 2)) [])’ >>
  xsimpl >>
  irule_at Any SEP_IMP_REFL >>
  qexists ‘REPLICATE 4096 NONE’ >>
  simp [Once events_ok_cases] >>
  conj_tac >-
   (gvs [ccnf_listTheory.bnd_fml_def,miscTheory.any_el_ALT,EL_REPLICATE, SF CONJ_ss]) >>
  conj_tac >- metis_tac [] >>
  conj_tac >-
   (gvs [LIST_REL_EL_EQN,OPTION_TYPE_def,EL_REPLICATE]) >>
  rw [] >> rename [‘CUSTOM_FFI Terminate [] xx’] >>
  pop_assum $ irule_at Any >>
  xsimpl
QED
