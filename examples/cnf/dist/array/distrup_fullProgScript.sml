(*
  The full setup around distrup core
*)
Theory distrup_fullProg
Libs
  preamble basis
Ancestors
  distrup_arrayProg

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

Definition w8z_def:
  w8z = (0w:word8)
End

val _ = translate w8z_def;

(* Array-level helpers *)
Quote add_cakeml:
  fun get_byte arr i = Word8.toInt (Word8Array.sub arr i);

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

  (* Read 8 bytes from arr at offset, dropping trailing zero bytes *)
  fun read_id arr offset =
    let
      fun find_last i =
        if i = 0 then 0
        else
        let
          val i1 = i - 1 in
          if Word8Array.sub arr (offset + i1) = w8z
          then find_last i1
          else i
        end
    in
      Word8Array.substring arr offset (find_last 8)
    end;

  fun read_id_strs arr len i =
    if i >= len then [] else read_id arr (i * 8) :: read_id_strs arr len (i + 1);

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
      (arr, read_id_strs arr len 0)
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
            val id = read_id step_arr 1
            val nb_lits_str = Word8Array.substring step_arr 9 4
            val nb_hints_str = Word8Array.substring step_arr 13 4
            val (buf_arr, cl) = get_clause buf_arr False nb_lits_str
            val (buf_arr, hints) = get_hints buf_arr nb_hints_str
          in
            (buf_arr, Some (Lrup id cl hints))
          end
      | #"i" => (* IMPORT *)
          let
            val id = read_id step_arr 1
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

(* Wraps and removes exception handling *)
Quote add_cakeml:
  fun check_top lno instr fml st =
    (case st of
      None => (None, "")
    | Some (carr, b) =>
        (case check_distrup_ht lno instr fml carr b of
          (carr, b) => (Some (carr, b), ""))
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

fun loop step_arr buf_arr fml st lno =
  let
    val (buf_arr, result) = parse_step step_arr buf_arr
  in
    case result of
      None => () (* Terminate: C handles response after cml_main returns *)
    | Some instr =>
        let
          val (st, msg) = check_top lno instr fml st
          val res = case st of None => "0" ^ msg | Some _ => "1"
          val _ = do_callback res step_arr
        in
          loop step_arr buf_arr fml st (lno + 1)
        end
  end;

fun main () =
  let
    val step_arr = Word8Array.array 17 (Word8.fromInt 0)
    val buf_arr = Word8Array.array 0 (Word8.fromInt 0)
    val fml = Hashtable.empty 1024 hash_str String.compare
    val carr = Word8Array.array 0 (Word8.fromInt 0)
    val b = Word8.fromInt 1
  in
    loop step_arr buf_arr fml (Some (carr, b)) 1
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

(*
Theorem aim:
  ∀inputs.
    app p main (CUSTOM_FFI Step inputs [] * CL ...)
               (SEP_EXISTS trace.
                  CUSTOM_FFI Terminate [] trace * CL ... *
                  cond (trace_ok trace))
Proof
*)

Type clause = “:word32 list”;
Type hints = “:word64 list”;

(* what to wait for as the next C call *)
Datatype:
  wait_for = Step
           | Produce_clause clause hints
           | Produce_hints hints
           | Produce_callback
           | Import_clause clause
           | Import_callback
           | Delete_hints hints
           | Delete_callback
           | Validate_UNSAT_callback
           | Terminate
End

(* each input is one of: *)
Datatype:
  input = Produce clause hints
        | Import clause
        | Delete hints
        | Validate_UNSAT
End

(* the state of the C code*)
Type state = “:wait_for # input list”;

(* encoding *)

Definition WaitFor_def:
  WaitFor Step = Str (strlit "Step") : ffi ∧
  WaitFor _ = Str (strlit "Produce_clause")
End

Definition Input_def:
  Input (Produce _ _) = Str (strlit "Produce") : ffi ∧ (* TODO fix *)
  Input _ = Str (strlit "Import")
End

Definition State_def:
  State waif_for inputs =
    Cons (WaitFor waif_for)
         (List (MAP Input inputs))
End

(* decoding *)

Definition dest_WaitFor_def:
  dest_WaitFor (x:ffi) = NONE : wait_for option
End

Definition dest_Input_def:
  dest_Input _ = NONE : input option
End

Definition dest_State_def:
  dest_State (x:ffi) =
    case destCons x of NONE => NONE | SOME (x, y) =>
    case dest_WaitFor x of NONE => NONE | SOME wait_for =>
    case destList x of NONE => NONE | SOME l =>
    let opt_inputs = MAP dest_Input l in
    if MEM NONE opt_inputs then NONE else
      SOME (wait_for, MAP THE opt_inputs) : state option
End

(* next state *)

val imm_arg = “imm_arg:word8 list”
val arr_arg = “arr_arg:word8 list”

Definition update_step_def:
  update_step ^imm_arg ^arr_arg Step inputs =
    (if LENGTH imm_arg ≠ 0 ∨ LENGTH arr_arg ≠ 17 then NONE else
       case inputs of
       | [] => SOME (FFIreturn arr_arg (State Terminate inputs))
       | (i::is) => NONE
    ) ∧
  update_step ^imm_arg ^arr_arg _ _ = NONE
End

Definition update_def:
  update ffi_name imm_arg arr_arg s =
    case dest_State s of
    | NONE => NONE
    | SOME (waif_for, inputs) =>
        if ffi_name = strlit "step" then
          update_step imm_arg arr_arg waif_for inputs
        else if ffi_name = ARB then NONE else NONE
End

(* definition of separation logic assertion CUSTOM_FFI *)

Definition names_def:
  names = [«step»; «clause»; «hints»; «callback»]
End

Definition CUSTOM_FFI_def:
  CUSTOM_FFI waif_for inputs events =
    one (FFI_part (State waif_for inputs) update names events)
End
