(*
  Functions that aid in dealing with syntax of CF-style separation logic.
*)
structure cfHeapsBaseSyntax = struct

open preamble
open set_sepTheory helperLib
open cfHeapsBaseTheory

val ERR = mk_HOL_ERR"cfHeapsBaseSyntax";

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

val postv_tm = prim_mk_const{Name="POSTv",Thy="cfHeapsBase"};
val dest_postv = dest_binder postv_tm (ERR "dest_postv" "Not a POSTv abstraction");
val is_postv = can dest_postv;
fun mk_postv (postv_v, c) = mk_binder postv_tm "mk_postv" (postv_v, c);

val poste_tm = prim_mk_const{Name="POSTe",Thy="cfHeapsBase"};
val dest_poste = dest_binder poste_tm (ERR "dest_poste" "Not a POSTe abstraction");
val is_poste = can dest_poste;
fun mk_poste (poste_v, c) = mk_binder poste_tm "mk_poste" (poste_v, c);

val postf_tm = prim_mk_const{Name="POSTf",Thy="cfHeapsBase"};
val dest_postf = dest_binder postf_tm (ERR "dest_postf" "Not a POSTf abstraction");
val is_postf = can dest_postf;
(* TODO fun mk_postf (postf_v, c) = mk_binder postf_tm "mk_postf" (postf_v, c);*)

val postd_tm = prim_mk_const{Name="POSTd",Thy="cfHeapsBase"};
val dest_postd = dest_binder postd_tm (ERR "dest_postd" "Not a POSTd abstraction");
val is_postd = can dest_postd;
fun mk_postd (postd_io, c) = mk_binder postd_tm "mk_postd" (postd_io, c);

val postve_tm = prim_mk_const{Name="POSTve",Thy="cfHeapsBase"};
fun dest_postve c =
  let
      val (c', poste_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      if same_const ptm postve_tm then
          let
              val (postv_v, postv_pred) = dest_abs postv_abs
              val (poste_v, poste_pred) = dest_abs poste_abs
          in
             (postv_v, postv_pred, poste_v, poste_pred)
          end
      else
          raise (ERR "" "")
  end
  handle HOL_ERR _ => raise (ERR "dest_postve" "Not a POSTve abstraction");
fun is_postve c =
  let
      val (c', poste_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      same_const ptm postve_tm
  end
  handle HOL_ERR _ => false;
fun mk_postve (postv_v, postv_abs, poste_v, poste_abs) =
  let
      val postv_pred = mk_abs (postv_v, postv_abs)
      val poste_pred = mk_abs (poste_v, poste_abs)
  in
      foldl (mk_comb o swap) postve_tm [postv_pred, poste_pred]
  end;

val postvd_tm = prim_mk_const{Name="POSTvd",Thy="cfHeapsBase"};
fun dest_postvd c =
  let
      val (c', postd_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      if same_const ptm postvd_tm then
          let
              val (postv_v, postv_pred) = dest_abs postv_abs
              val (postd_io, postd_pred) = dest_abs postd_abs
          in
             (postv_v, postv_pred, postd_io, postd_pred)
          end
      else
          raise (ERR "" "")
  end
  handle HOL_ERR _ => raise (ERR "destvd_post" "Not a POSTvd abstraction");
fun is_postvd c =
  let
      val (c', postd_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      same_const ptm postvd_tm
  end
  handle HOL_ERR _ => false;
fun mk_postvd (postv_v, postv_abs, postd_io, postd_abs) =
  let
      val postv_pred = mk_abs (postv_v, postv_abs)
      val postd_pred = mk_abs (postd_io, postd_abs)
  in
      foldl (mk_comb o swap) postvd_tm [postv_pred, postd_pred]
  end;

val posted_tm = prim_mk_const{Name="POSTed",Thy="cfHeapsBase"};
fun dest_posted c =
  let
      val (c', postd_abs) = dest_comb c
      val (ptm, poste_abs) = dest_comb c'
  in
      if same_const ptm posted_tm then
          let
              val (poste_v, poste_pred) = dest_abs poste_abs
              val (postd_io, postd_pred) = dest_abs postd_abs
          in
             (poste_v, poste_pred, postd_io, postd_pred)
          end
      else
          raise (ERR "" "")
  end
  handle HOL_ERR _ => raise (ERR "dested_post" "Not a POSTed abstraction");
fun is_posted c =
  let
      val (c', postd_abs) = dest_comb c
      val (ptm, poste_abs) = dest_comb c'
  in
      same_const ptm posted_tm
  end
  handle HOL_ERR _ => false;
fun mk_posted (poste_v, poste_abs, postd_io, postd_abs) =
  let
      val poste_pred = mk_abs (poste_v, poste_abs)
      val postd_pred = mk_abs (postd_io, postd_abs)
  in
      foldl (mk_comb o swap) posted_tm [poste_pred, postd_pred]
  end;

val post_tm = prim_mk_const{Name="POST",Thy="cfHeapsBase"};
fun dest_post c =
  let
      val (c', postd_abs) = dest_comb c
      val (c'', postf_abs) = dest_comb c'
      val (c''', poste_abs) = dest_comb c''
      val (ptm, postv_abs) = dest_comb c'''
  in
      if same_const ptm post_tm then
          let
              val (postv_v, postv_pred) = dest_abs postv_abs
              val (poste_v, poste_pred) = dest_abs poste_abs
              val (postf_name, postf_abs') = dest_abs postf_abs
              val (postf_conf, postf_abs'') = dest_abs postf_abs'
              val (postf_bytes, postf_pred) = dest_abs postf_abs''
              val (postd_io, postd_pred) = dest_abs postd_abs
          in
             (postv_v, postv_pred, poste_v, poste_pred,
              [postf_name, postf_conf, postf_bytes], postf_pred,
              postd_io, postd_pred)
          end
      else
          raise (ERR "" "")
  end
  handle HOL_ERR _ => raise (ERR "dest_post" "Not a POST abstraction");
fun is_post c =
  let
      val (c', postd_abs) = dest_comb c
      val (c'', postf_abs) = dest_comb c'
      val (c''', poste_abs) = dest_comb c''
      val (ptm, postv_abs) = dest_comb c'''
  in
      same_const ptm post_tm
  end
  handle HOL_ERR _ => false;
fun mk_post (postv_v, postv_abs, poste_v, poste_abs, postf_vl, postf_abs, postd_io, postd_abs) =
  let
      val postv_pred = mk_abs (postv_v, postv_abs)
      val poste_pred = mk_abs (poste_v, poste_abs)
      val postf_pred = foldr mk_abs postf_abs postf_vl
      val postd_pred = mk_abs (postd_io, postd_abs)
  in
      foldl (mk_comb o swap) post_tm [postv_pred, poste_pred, postf_pred, postd_pred]
  end;


end
