(*
  A library for packing theorems, terms, and types as theorems (which can
  thereby be saved in theories).
*)

structure packLib =
struct

open HolKernel boolLib bossLib;

fun pack_type ty = REFL (mk_var("ty",ty));
fun unpack_type th = th |> concl |> dest_eq |> fst |> type_of;

fun pack_term tm = REFL tm;
fun unpack_term th = th |> concl |> dest_eq |> fst;

local
  val abbrev_insert = CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))
  val abbrev_remove = CONV_RULE (REWR_CONV markerTheory.Abbrev_def)
in
  fun pack_thm th = th |> abbrev_insert |> DISCH_ALL;
  fun unpack_thm th = th |> UNDISCH_ALL |> abbrev_remove;
end

fun pack_string s = REFL (mk_var(s,bool))
fun unpack_string th = th |> concl |> dest_eq |> fst |> dest_var |> fst

fun pack_list f xs = TRUTH :: map f xs |> LIST_CONJ |> PURE_ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def];
fun unpack_list f th = th |> PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def] |> CONJUNCTS |> tl |> map f;

fun pack_pair f1 f2 (x1,x2) = pack_list I [f1 x1, f2 x2]
fun unpack_pair f1 f2 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x)) end

fun pack_option f1 NONE = pack_list I []
  | pack_option f1 (SOME x) = pack_list I [f1 x]
fun unpack_option f1 th =
  let val x = unpack_list I th in
    case x of [] => NONE | (x::xs) => SOME (f1 x) end

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

end
