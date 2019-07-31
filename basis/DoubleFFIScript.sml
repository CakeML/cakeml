(*
  Specifies behaviour of FFI calls from/toString for doubles
*)
open preamble
    cfFFITypeTheory
     cfHeapsBaseTheory DoubleProgTheory;

val _ = new_theory"DoubleFFI";

val _ = Datatype `
  doubleFuns = <| fromString:string -> word64;
                  toString : word64 -> string |>`;

(* a valid argument is a non-empty string with no null bytes *)

val validArg_def = Define`
    validArg s <=> strlen s > 0 /\ ~MEM (CHR 0) (explode s)`;

val into_bytes_def = Define `
  (into_bytes 0 w = []) /\
  (into_bytes (SUC n) w = ((w2w w):word8) :: into_bytes n (w >>> 8))`;

(* there are 2 FFI functions over the commandline state: *)
val ffi_fromString_def = Define `
  ffi_fromString (conf:word8 list) (bytes: word8 list) doubleFns =
    if LENGTH bytes = 8 then
      SOME (FFIreturn
        (into_bytes 8 (doubleFns.fromString (MAP (CHR o w2n) conf)))
        doubleFns)
    else NONE`;

val ffi_toString_def = Define `
  ffi_toString (conf:word8 list) (bytes: word8 list) doubleFns =
    if LENGTH bytes = 256 then
      let
        str = (doubleFns.toString
            (concat_all (EL 0 bytes) (EL 1 bytes) (EL 2 bytes) (EL 3 bytes)
                        (EL 4 bytes) (EL 5 bytes) (EL 6 bytes) (EL 7 bytes)))
            ++ [CHR 0];
      in
        SOME (FFIreturn
                (MAP (n2w o ORD) str ++ DROP (LENGTH str) bytes)
                doubleFns)
    else NONE`;

(* TODO: Move *)
val dest_iNum_def = Define `
  dest_iNum (iNum n) = n `;

(* FFI part for the commandline *)
val encode_def = Define `encode doubleFns =
  Cons
    (Fun (\ x:ffi_inner. Num (w2n (doubleFns.fromString (dest_iStr x)))))
    (Fun (\ x:ffi_inner. Str (doubleFns.toString (n2w (dest_iNum x)))))`;

val encode_11 = prove(
  ``!x y. encode x = encode y <=> x = y``,
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw []
  \\ fs[FUN_EQ_THM, fetch "-" "doubleFuns_component_equality"] \\ conj_tac
  >- (fs[FUN_EQ_THM] \\ rpt strip_tac
      \\ last_x_assum (qspec_then `iStr x'` mp_tac)
      \\ fs[dest_iStr_def])
  \\ fs[FUN_EQ_THM] \\ rpt strip_tac
  \\ first_x_assum (qspec_then `iNum (w2n x')` mp_tac)
  \\ fs[dest_iNum_def]);

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val double_ffi_part_def = Define`
  double_ffi_part = (encode,decode,
    [("double_fromString",ffi_fromString);
     ("double_toString",ffi_toString)])`;

val _ = export_theory();
