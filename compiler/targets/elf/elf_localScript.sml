open HolKernel Parse boolLib bossLib;

open ASCIInumbersTheory integerTheory listTheory numTheory wordsTheory;

val _ = numLib.prefer_num();

val _ = new_theory "elf_local";

(* Conversions between integers and strings *)

val int_from_dec_string_def = Define `
  int_from_dec_string i =
    if i = "" then
      0
    else if HD i = #"-" then
      0i - &(num_from_dec_string (TL i))
    else
      &(num_from_dec_string i)`

val int_to_dec_string_def = Define `
  int_to_dec_string i =
    if i < 0 then
      "-" ++ num_to_dec_string (Num (- i))
    else
      num_to_dec_string (Num i)`

(* ELF specific fixed-width types and conversions back and forth between bytes *)

val _ = type_abbrev ("unsigned_char", ``:word8``)
val _ = type_abbrev ("byte", ``:word8``)
val _ = type_abbrev ("uint16", ``:word16``)
val _ = type_abbrev ("uint32", ``:word32``)
val _ = type_abbrev ("uint64", ``:word64``)
val _ = type_abbrev ("sint32", ``:word32``)
val _ = type_abbrev ("sint64", ``:word64``)

val uint16_of_dual_def = Define `
  uint16_of_dual (b1 : byte) (b2 : byte) : uint16 = b1 @@ b2`

val dual_of_uint16_def = Define `
  dual_of_uint16 (u : uint16) : byte # byte =
    ((0 >< 7) u, (8 >< 15) u)`

val uint32_of_quad_def = Define `
  uint32_of_quad (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) : uint32 =
    let (upper : word16) = b1 @@ b2 in
    let (lower : word16) = b3 @@ b4 in
    	upper @@ lower`

val quad_of_uint32_def = Define `
  quad_of_uint32 (u : uint32) : byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u)`

val sint32_of_quad_def = Define `
  sint32_of_quad (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) : uint32 =
    let (upper : word16) = b1 @@ b2 in
    let (lower : word16) = b3 @@ b4 in
    	upper @@ lower`

val quad_of_sint32_def = Define `
  quad_of_sint32 (u : sint32) : byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u)`

val uint64_of_oct_def = Define `
  uint64_of_oct_def (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) (b5 : byte) (b6 : byte) (b7 : byte) (b8 : byte) : uint64 =
    let (upper : word32) = ((b1 @@ b2) : word16) @@ ((b4 @@ b4) : word16) in
    let (lower : word32) = ((b5 @@ b6) : word16) @@ ((b7 @@ b8) : word16) in
      upper @@ lower`

val oct_of_uint64_def = Define `
  oct_of_uint64_def (u : uint64) : byte # byte # byte # byte # byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u, (32 >< 39) u, (40 >< 47) u, (48 >< 55) u, (56 >< 63) u)`

val sint64_of_oct_def = Define `
  sint64_of_oct_def (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) (b5 : byte) (b6 : byte) (b7 : byte) (b8 : byte) : uint64 =
    let (upper : word32) = ((b1 @@ b2) : word16) @@ ((b4 @@ b4) : word16) in
    let (lower : word32) = ((b5 @@ b6) : word16) @@ ((b7 @@ b8) : word16) in
      upper @@ lower`

val oct_of_sint64_def = Define `
  oct_of_sint64_def (u : sint64) : byte # byte # byte # byte # byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u, (32 >< 39) u, (40 >< 47) u, (48 >< 55) u, (56 >< 63) u)`

(* String operations *)

val uint16_of_dual_def = Define `
  uint16_of_dual (b1 : byte) (b2 : byte) : uint16 = b1 @@ b2`

val dual_of_uint16_def = Define `
  dual_of_uint16 (u : uint16) : byte # byte =
    ((0 >< 7) u, (8 >< 15) u)`

val uint32_of_quad_def = Define `
  uint32_of_quad (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) : uint32 =
    let (upper : word16) = b1 @@ b2 in
    let (lower : word16) = b3 @@ b4 in
    	upper @@ lower`

val quad_of_uint32_def = Define `
  quad_of_uint32 (u : uint32) : byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u)`

val sint32_of_quad_def = Define `
  sint32_of_quad (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) : uint32 =
    let (upper : word16) = b1 @@ b2 in
    let (lower : word16) = b3 @@ b4 in
    	upper @@ lower`

val quad_of_sint32_def = Define `
  quad_of_sint32 (u : sint32) : byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u)`

val uint64_of_oct_def = Define `
  uint64_of_oct (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) (b5 : byte) (b6 : byte) (b7 : byte) (b8 : byte) : uint64 =
    let (upper : word32) = ((b1 @@ b2) : word16) @@ ((b4 @@ b4) : word16) in
    let (lower : word32) = ((b5 @@ b6) : word16) @@ ((b7 @@ b8) : word16) in
      upper @@ lower`

val oct_of_uint64_def = Define `
  oct_of_uint64 (u : uint64) : byte # byte # byte # byte # byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u, (32 >< 39) u, (40 >< 47) u, (48 >< 55) u, (56 >< 63) u)`

val sint64_of_oct_def = Define `
  sint64_of_oct (b1 : byte) (b2 : byte) (b3 : byte) (b4 : byte) (b5 : byte) (b6 : byte) (b7 : byte) (b8 : byte) : uint64 =
    let (upper : word32) = ((b1 @@ b2) : word16) @@ ((b4 @@ b4) : word16) in
    let (lower : word32) = ((b5 @@ b6) : word16) @@ ((b7 @@ b8) : word16) in
      upper @@ lower`

val oct_of_sint64_def = Define `
  oct_of_sint64 (u : sint64) : byte # byte # byte # byte # byte # byte # byte # byte =
    ((0 >< 7) u, (8 >< 15) u, (16 >< 23) u, (24 >< 31) u, (32 >< 39) u, (40 >< 47) u, (48 >< 55) u, (56 >< 63) u)`

(* String operations *)

val string_suffix_def = Define `
  string_suffix (m : num) (ss : string) =
    case (m, ss) of
      (0,         s) => SOME s
    | (SUC m,    []) => NONE
    | (SUC m, x::xs) =>
      (case string_suffix m xs of
         NONE    => NONE
       | SOME tl => SOME (x::tl))`

val _ = export_theory();


