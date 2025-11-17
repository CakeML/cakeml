(*
  Logical model of the FFI calls for functions to-/fromString in
  the Double module.
*)
Theory DoubleFFI
Ancestors
  cfFFIType cfHeapsBase DoubleProg
Libs
  preamble


Datatype:
  doubleFuns = <|
    fromString : string -> word64 option;
    toString : word64 -> string;
    fromInt : num -> word64;
    toInt : word64 -> num;
    power : word64 -> word64 -> word64;
    ln : word64 -> word64;
    exp : word64 -> word64;
    floor : word64 -> word64;
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
  ffi_fromString (conf: word8 list) (bytes: word8 list) doubleFns =
    if LENGTH bytes = 8 then
      case doubleFns.fromString (MAP (CHR o w2n) conf) of
      | NONE => NONE
      | SOME bs => SOME (FFIreturn (into_bytes 8 bs) doubleFns)
    else NONE
End

Definition ffi_toString_def:
  ffi_toString (conf: word8 list) (bytes: word8 list) doubleFns =
    if LENGTH bytes = 256 then
      let str = doubleFns.toString (concat_word_list (TAKE 8 bytes)) ++
                [CHR 0] in
      SOME (FFIreturn (MAP (n2w o ORD) str ++
                       DROP (LENGTH str) bytes) doubleFns)
    else NONE
End

Definition ffi_toInt_def:
  ffi_toInt (conf: word8 list) (bytes: word8 list) doubleFns =
    NONE: doubleFuns ffi_result option
End

Definition ffi_fromInt_def:
  ffi_fromInt (conf: word8 list) (bytes: word8 list) doubleFns =
    NONE: doubleFuns ffi_result option
End

Definition ffi_pow_def:
  ffi_pow (conf: word8 list) (bytes: word8 list) doubleFns =
    NONE: doubleFuns ffi_result option
End

Definition ffi_ln_def:
  ffi_ln (conf: word8 list) (bytes: word8 list) doubleFns =
    NONE: doubleFuns ffi_result option
End

Definition ffi_exp_def:
  ffi_exp (conf: word8 list) (bytes: word8 list) doubleFns =
    NONE: doubleFuns ffi_result option
End

Definition ffi_floor_def:
  ffi_floor (conf: word8 list) (bytes: word8 list) doubleFns =
    NONE: doubleFuns ffi_result option
End

Definition dest_iNum_def:
  dest_iNum (iNum n) = n
End

(* FFI part for Double *)
Definition encode_def:
  encode doubleFns =
    FOLDL Cons
          (Fun (\x.
            case doubleFns.fromString (dest_iStr x) of
            | NONE => Cons (Num 0) (Num 0)
            | SOME x => Cons (Num 1) (Num (w2n x + 1))))
          [Fun (\x. Str (doubleFns.toString (n2w (dest_iNum x))));
           Fun (\x. Num (w2n (doubleFns.fromInt (dest_iNum x))));
           Fun (\x. Num (doubleFns.toInt (n2w (dest_iNum x))));
           Fun (\x. Fun (\y. Num (w2n (doubleFns.power (n2w (dest_iNum x))
                                                       (n2w (dest_iNum y))))));
           Fun (\x. Num (w2n (doubleFns.ln (n2w (dest_iNum x)))));
           Fun (\x. Num (w2n (doubleFns.exp (n2w (dest_iNum x)))));
           Fun (\x. Num (w2n (doubleFns.floor (n2w (dest_iNum x)))))]
End

Theorem encode_11[local]:
  !x y. encode x = encode y <=> x = y
Proof
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw []
  \\ fs[FUN_EQ_THM, fetch "-" "doubleFuns_component_equality"]
  \\ rw []
  >- (
    last_x_assum (qspec_then `iStr x'` mp_tac)
    \\ gs [CaseEq "option", dest_iStr_def]
    \\ rw [] \\ gs [])
  \\ metis_tac [dest_iNum_def, dest_iStr_def, n2w_w2n]
QED

Theorem encode_decode_exists[local]:
  ?decode. !cls. decode (encode cls) = SOME cls
Proof
  qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]
QED

val decode_encode_name = "decode_encode";
val decode_encode = new_specification(
  decode_encode_name,
  ["decode"],
  encode_decode_exists);
val _ = export_rewrites [decode_encode_name];

Definition double_ffi_part_def:
  double_ffi_part = (encode,decode,
    [("double_fromString",ffi_fromString);
     ("double_toString",ffi_toString);
     ("double_fromInt",ffi_fromInt);
     ("double_toInt",ffi_toInt);
     ("double_pow",ffi_pow);
     ("double_exp",ffi_exp);
     ("double_ln",ffi_ln);
     ("double_floor",ffi_floor)])
End
