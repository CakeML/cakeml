(*
  Functions that aid in dealing with syntax of CF-style separation logic.
*)
structure cfHeapsBaseSyntax = struct

open preamble
open set_sepTheory helperLib
open cfHeapsBaseTheory

val ERR = mk_HOL_ERR "cfHeapsBaseSyntax";

local
  structure Parse = struct
    open Parse
     val (Type,Term) =
         parse_from_grammars $ valOf $ grammarDB {thyname = "cfHeapsBase"}
  end
  open Parse
in
val ffi_proj_format = “:'ffi ffi_proj”
val heap_ty = “:heap”
val hprop_ty = “:hprop”
end (* local *)

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

local
val sep_imp = prim_mk_const {Name = "SEP_IMP", Thy = "set_sep"}
in
val dest_sep_imp = dest_binop sep_imp (ERR "dest_sep_imp" "")
end

local
val cell = prim_mk_const {Name = "cell", Thy = "cfHeapsBase"}
in
val dest_cell = dest_binop cell (ERR "dest_cell" "")
end

local
val REF = prim_mk_const {Name = "REF", Thy = "cfHeapsBase"}
in
val dest_REF = dest_binop REF (ERR "dest_REF" "")
end

local
val ARRAY = prim_mk_const {Name = "ARRAY", Thy = "cfHeapsBase"}
in
val dest_ARRAY = dest_binop ARRAY (ERR "dest_ARRAY" "")
end

local
val W8ARRAY = prim_mk_const {Name = "W8ARRAY", Thy = "cfHeapsBase"}
in
val dest_W8ARRAY = dest_binop W8ARRAY (ERR "dest_W8ARRAY" "")
end

local
val IO = prim_mk_const {Name = "IO", Thy = "cfHeapsBase"}
in
val dest_IO = dest_triop IO (ERR "dest_W8ARRAY" "")
end

fun is_cell tm = can dest_cell tm
fun is_REF tm = can dest_REF tm
fun is_ARRAY tm = can dest_ARRAY tm
fun is_W8ARRAY tm = can dest_W8ARRAY tm
fun is_IO tm = can dest_IO tm

fun is_sep_imp tm = can dest_sep_imp tm

local
val SEP_IMPPOST = prim_mk_const {Name = "SEP_IMPPOST", Thy = "cfHeapsBase"}
val dest_sep_imppost = dest_binop SEP_IMPPOST (ERR "is_sep_imppost" "")
in
val is_sep_imppost = can dest_sep_imppost
end

local
val cond_tm = inst [alpha |-> heap_part_ty]
              (prim_mk_const {Name = "cond", Thy = "set_sep"})
in
val is_cond = can (dest_monop cond_tm (ERR "is_cond" ""))
fun mk_cond tm = mk_comb (cond_tm,tm)
                 handle HOL_ERR _ => raise (ERR "mk_cond" "")
end

local
val se = (fst o dest_eq o concl o SPEC_ALL) SEP_EXISTS
in
fun is_sep_exists tm = (same_const se (dest_comb tm |> fst))
                       handle HOL_ERR _ => false
end

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
