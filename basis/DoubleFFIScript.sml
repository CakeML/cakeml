(*
  Logical model of the FFI calls for functions to-/fromString in
  the Double module.
*)

open preamble cfFFITypeTheory cfHeapsBaseTheory DoubleProgTheory;

val _ = new_theory "DoubleFFI";

(* TODO Add the remaining functions from the Double FFI *)
Datatype:
  doubleFuns = <|
    fromString : string -> word64 option;
    toString : word64 -> string;
  |>
End

(* a valid argument is a non-empty string with no null bytes *)

Definition validArg_def:
  validArg s <=> strlen s > 0 /\ ~MEM (CHR 0) (explode s)
End

Definition into_bytes_def:
  (into_bytes 0 w = []) /\
  (into_bytes (SUC n) w = ((w2w w):word8) :: into_bytes n (w >>> 8))
End

Definition ffi_fromString_def:
  ffi_fromString (conf:word8 list) (bytes: word8 list) doubleFns =
    if LENGTH bytes = 8 then
      case doubleFns.fromString (MAP (CHR o w2n) conf) of
      | NONE => NONE
      | SOME bs => SOME (FFIreturn (into_bytes 8 bs) doubleFns)
    else NONE
End

Definition ffi_toString_def:
  ffi_toString (conf:word8 list) (bytes: word8 list) doubleFns =
    if LENGTH bytes = 256 then
      let str = doubleFns.toString (concat_word_list (TAKE 8 bytes)) ++
                [CHR 0] in
      SOME (FFIreturn (MAP (n2w o ORD) str ++
                       DROP (LENGTH str) bytes) doubleFns)
    else NONE
End

Definition dest_iNum_def:
  dest_iNum (iNum n) = n
End

(* FFI part for Double *)
Definition encode_def:
  encode doubleFns =
    Cons
      (Fun (\ x:ffi_inner. Num (
        case doubleFns.fromString (dest_iStr x) of
        | NONE => 0
        | SOME x => w2n x + 1)))
      (Fun (\ x:ffi_inner. Str (doubleFns.toString (n2w (dest_iNum x)))))
End

Theorem encode_11[local]:
  !x y. encode x = encode y <=> x = y
Proof
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw []
  \\ fs[FUN_EQ_THM, fetch "-" "doubleFuns_component_equality"] \\ conj_tac
  >- (
    fs[FUN_EQ_THM] \\ rpt strip_tac
    \\ last_x_assum (qspec_then `iStr x'` mp_tac)
    \\ gs [CaseEq "option", dest_iStr_def]
    \\ rw [] \\ gs [])
  \\ fs[FUN_EQ_THM] \\ rpt strip_tac
  \\ first_x_assum (qspec_then `iNum (w2n x')` mp_tac)
  \\ fs[dest_iNum_def]
QED

Theorem encode_decode_exists[local]:
  ?decode. !cls. decode (encode cls) = SOME cls
Proof
  qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]
QED

Theorem decode_encode = new_specification(
  "decode_encode",
  ["decode"],
  encode_decode_exists);
val _ = export_rewrites ["decode_encode"];

Definition double_ffi_part_def:
  double_ffi_part = (encode,decode,
    [("double_fromString",ffi_fromString);
     ("double_toString",ffi_toString)])
End

val _ = export_theory ();
