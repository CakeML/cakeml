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

Type id = “:word64”;
Type clause = “:word32 list”;
Type hints = “:word64 list”;

(* what to wait for as the next C call *)
Datatype:
  wait_for = Step
           | Produce_clause id clause hints
           | Produce_hints id hints
           | Produce_callback id
           | Import_clause id clause
           | Import_callback id
           | Delete_hints hints
           | Delete_callback
           | Validate_UNSAT_callback
           | Terminate
End

(* each input is one of: *)
Datatype:
  input = Produce id clause hints
        | Import id clause
        | Delete hints
        | Validate_UNSAT
End

(* the state of the C code*)
Type state = “:wait_for # input list”;

(* encoding *)

Definition Clause_def:
  Clause (xs:clause) = List (MAP (Num o w2n) xs)
End

Definition Hints_def:
  Hints (xs:hints) = List (MAP (Num o w2n) xs)
End

Definition WaitFor_def:
  WaitFor wf =
    case wf of
    | Step => Str (strlit "Step")
    | Produce_clause i c h => Cons (Str (strlit "Produce_clause")) (Cons (Num (w2n i)) (Cons (Clause c) (Hints h)))
    | Produce_hints i h => Cons (Str (strlit "Produce_hints")) (Cons (Num (w2n i)) (Hints h))
    | Produce_callback i => Cons (Str (strlit "Produce_callback")) (Num (w2n i))
    | Import_clause i c => Cons (Str (strlit "Import_clause")) (Cons (Num (w2n i)) (Clause c))
    | Import_callback i => Cons (Str (strlit "Import_callback")) (Num (w2n i))
    | Delete_hints h => Cons (Str (strlit "Delete_hints")) (Hints h)
    | Delete_callback => Str (strlit "Delete_callback")
    | Validate_UNSAT_callback => Str (strlit "Validate_UNSAT_callback")
    | Terminate => Str (strlit "Terminate")
End

Definition Input_def:
  Input (Produce i c h) = Cons (Str (strlit "Produce"))
                               (Cons (Num (w2n i)) (Cons (Clause c) (Hints h))) ∧
  Input (Import i c)    = Cons (Str (strlit "Import"))
                               (Cons (Num (w2n i)) (Clause c)) ∧
  Input (Delete h)      = Cons (Str (strlit "Delete")) (Hints h) ∧
  Input Validate_UNSAT  = Str (strlit "Validate_UNSAT")
End

Definition State_def:
  State waif_for inputs =
    Cons (WaitFor waif_for)
         (List (MAP Input inputs))
End

Theorem Clause_11:
  Clause x = Clause y ⇔ x = y
Proof
  gvs [Clause_def] \\ eq_tac
  \\ rw [] \\ drule_at Any MAP_EQ_MAP_IMP \\ gvs []
QED

Theorem Hints_11:
  Hints x = Hints y ⇔ x = y
Proof
  gvs [Hints_def] \\ eq_tac
  \\ rw [] \\ drule_at Any MAP_EQ_MAP_IMP \\ gvs []
QED

Theorem Input_11:
  Input x = Input y ⇔ x = y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [Input_def,Clause_11,Hints_11]
QED

Theorem WaitFor_11:
  WaitFor x = WaitFor y ⇔ x = y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [WaitFor_def,Clause_11,Hints_11]
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

Definition update_step_def:
  update_step ^imm_arg ^arr_arg Step inputs =
    (if LENGTH imm_arg ≠ 0 ∨ LENGTH arr_arg ≠ 17 then NONE else
       case inputs of
       | [] => SOME (FFIreturn (0w :: TL arr_arg) (State Terminate inputs))
       | (i::is) =>
         case i of
         | Produce id c h =>
             SOME (FFIreturn ([n2w (ORD #"a")] ++
                              word_to_bytes (id : word64) F ++
                              word_to_bytes (n2w (LENGTH c) : word32) F ++
                              word_to_bytes (n2w (LENGTH h) : word32) F)
                             (State (Produce_clause id c h) is))
         | Import id c =>
             SOME (FFIreturn ([n2w (ORD #"i")] ++
                              word_to_bytes (id : word64) F ++
                              word_to_bytes (n2w (LENGTH c) : word32) F ++
                              DROP 13 arr_arg)
                             (State (Import_clause id c) is))
         | Delete h =>
             SOME (FFIreturn ([n2w (ORD #"d")] ++
                              word_to_bytes (n2w (LENGTH h) : word32) F ++
                              DROP 5 arr_arg)
                             (State (Delete_hints h) is))
         | Validate_UNSAT =>
             SOME (FFIreturn ([n2w (ORD #"V")] ++ TL arr_arg)
                             (State Validate_UNSAT_callback is))) ∧
  update_step ^imm_arg ^arr_arg _ _ = NONE
End

Definition write_bytes_def:
  write_bytes [] xs = [] ∧
  write_bytes xs [] = xs ∧
  write_bytes (x::xs) (y::ys) = (y:word8) :: write_bytes xs ys
End

Definition update_clause_def:
  update_clause ^imm_arg ^arr_arg (Produce_clause id c h) inputs =
    (SOME (FFIreturn (write_bytes arr_arg (FLAT (MAP (λw. word_to_bytes w F) c)))
                     (State (Produce_hints id h) inputs))) ∧
  update_clause ^imm_arg ^arr_arg (Import_clause id c) inputs =
    (SOME (FFIreturn (write_bytes arr_arg (FLAT (MAP (λw. word_to_bytes w F) c)))
                     (State (Import_callback id) inputs))) ∧
  update_clause ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_hints_def:
  update_hints ^imm_arg ^arr_arg (Produce_hints id h) inputs =
    (SOME (FFIreturn (write_bytes arr_arg (FLAT (MAP (λw. word_to_bytes w F) h)))
                     (State (Produce_callback id) inputs))) ∧
  update_hints ^imm_arg ^arr_arg (Delete_hints h) inputs =
    (SOME (FFIreturn (write_bytes arr_arg (FLAT (MAP (λw. word_to_bytes w F) h)))
                     (State Delete_callback inputs))) ∧
  update_hints ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_callback_def:
  update_callback ^imm_arg ^arr_arg (Produce_callback id) inputs =
    (SOME (FFIreturn arr_arg (State Step inputs))) ∧
  update_callback ^imm_arg ^arr_arg (Import_callback id) inputs =
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
    (CUSTOM_FFI Step (Validate_UNSAT :: inputs) events *
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
  qabbrev_tac ‘unsat_event = IO_event (ExtCall «step») [] (ZIP (step_arr,n2w (ORD #"V")::TL step_arr))’ >>
  xlet ‘POSTv res.
    CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) * W8ARRAY step_arrv (n2w (ORD #"V") :: TL step_arr)’
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
  xlet ‘POSTv res. CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
           W8ARRAY step_arrv (n2w (ORD #"V") :: TL step_arr) *
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
  gvs [is_unsat_event_def]
QED

(*
Theorem aim:
  ∀inputs.
    app p main (CUSTOM_FFI Step inputs [] * CL ...)
               (SEP_EXISTS trace.
                  CUSTOM_FFI Terminate [] trace * CL ... *
                  cond (trace_ok trace))
Proof
*)
