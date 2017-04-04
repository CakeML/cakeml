structure cfHeapsBaseSyntax = struct

open preamble
open set_sepTheory helperLib
open cfHeapsBaseTheory

val ffi_proj_format = packLib.unpack_type ffi_proj_pack
val ffi_varty = mk_vartype "'ffi"

fun mk_ffi_proj_ty arg_ty =
  type_subst [ffi_varty |-> arg_ty] ffi_proj_format

fun dest_ffi_proj ty =
  if can (match_type ffi_proj_format) ty then hd (type_vars ty)
  else fail()

fun is_ffi_proj ty = can dest_ffi_proj ty

val heap_part_ty =
  mk_thy_type {Thy = "cfHeapsBase", Tyop = "heap_part", Args = []}
val res_ty =
  mk_thy_type {Thy = "cfHeapsBase", Tyop = "res", Args = []}
val heap_ty = packLib.unpack_type heap_pack
val hprop_ty = packLib.unpack_type hprop_pack

fun dest_sep_imp tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) SEP_IMP_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_cell tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) cell_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_REF tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) REF_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_ARRAY tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) ARRAY_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_W8ARRAY tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) W8ARRAY_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun dest_IO tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) IO_def
  in if can (match_term format) tm then (cdr (car (car tm)), cdr (car tm), cdr tm)
     else fail() end

fun is_cell tm = can dest_cell tm
fun is_REF tm = can dest_REF tm
fun is_ARRAY tm = can dest_ARRAY tm
fun is_W8ARRAY tm = can dest_W8ARRAY tm
fun is_IO tm = can dest_IO tm

fun is_sep_imp tm = can dest_sep_imp tm

fun is_sep_imppost tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) SEP_IMPPOST_def
  in can (match_term format) tm end

fun is_cond tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) cond_def
  in can (match_term format) tm end

fun is_sep_exists tm = let
  val se = (fst o dest_eq o concl o SPEC_ALL) SEP_EXISTS
  in (ignore (match_term se (dest_comb tm |> fst)); true)
     handle HOL_ERR _ => false
  end

fun mk_cond t =
  SPEC t (INST_TYPE [alpha |-> heap_part_ty] cond_def)
  |> concl |> lhs

val emp_tm =
  inst [alpha |-> heap_part_ty]
    (emp_def |> concl |> lhs)

end
