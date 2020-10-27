(*
  A library for packing theorems, terms, and types as theorems (which can
  thereby be saved in theories).
*)

structure packLib =
struct

open HolKernel boolLib bossLib;
local
open ThyDataSexp
in

fun ERR f msg = mk_HOL_ERR "packLib" f msg

fun pack_type ty = Type ty
fun unpack_type (Type ty) = ty
  | unpack_type _ = raise ERR "unpack_type" "Not a type"

fun pack_term tm = Term tm;
fun unpack_term (Term tm) = tm
  | unpack_term _ = raise ERR "unpack_term" "Not a term"

local
  val abbrev_insert = CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))
  val abbrev_remove = CONV_RULE (REWR_CONV markerTheory.Abbrev_def)
in
  fun pack_thm th = Thm th
  fun unpack_thm (Thm th) = th
    | unpack_thm _ = raise ERR "unpack_thm" "Not a theorem"
end

fun pack_string s = String s
fun unpack_string (String s) = s
  | unpack_string _ = raise ERR "unpack_string" "Not a string"

fun pack_list f xs = List (map f xs)
fun unpack_list f (List vs) = map f vs
  | unpack_list _ _ = raise ERR "unpack_list" "Not a list"

fun pack_pair f1 f2 (x1,x2) = pack_list I [f1 x1, f2 x2]
fun unpack_pair f1 f2 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x)) end

fun pack_option f1 NONE = Option NONE
  | pack_option f1 (SOME x) = Option (SOME (f1 x))
fun unpack_option f1 (Option optv) = Option.map f1 optv
  | unpack_option _ _ = raise ERR "unpack_option" "Not an option"

fun pack_triple f1 f2 f3 (x1,x2,x3) = pack_list I [f1 x1, f2 x2, f3 x3]
fun unpack_triple f1 f2 f3 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x)) end

fun pack_4tuple f1 f2 f3 f4 (x1,x2,x3,x4) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4]
fun unpack_4tuple f1 f2 f3 f4 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x)) end

fun pack_5tuple f1 f2 f3 f4 f5 (x1,x2,x3,x4,x5) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4, f5 x5]
fun unpack_5tuple f1 f2 f3 f4 f5 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x), f5 (el 5 x)) end

fun pack_6tuple f1 f2 f3 f4 f5 f6 (x1,x2,x3,x4,x5,x6) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6]
fun unpack_6tuple f1 f2 f3 f4 f5 f6 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x), f5 (el 5 x), f6 (el 6 x)) end
end (* local *)
end
