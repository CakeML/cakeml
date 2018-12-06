(*
  Helper functions for syntax from cfTheory.
*)
structure cfSyntax :> cfSyntax = struct
open Abbrev

local
  open HolKernel boolLib bossLib cfTheory

  fun make5 tm (a,b,c,d,e) =
    list_mk_icomb (tm, [a, b, c, d, e])

  fun dest5 c e tm =
    case with_exn strip_comb tm e of
        (t, [t1, t2, t3, t4, t5]) =>
        if same_const t c then (t1, t2, t3, t4, t5) else raise e
      | _ => raise e

  fun make6 tm (a,b,c,d,e,f) =
    list_mk_icomb (tm, [a, b, c, d, e, f])

  fun dest6 c e tm =
    case with_exn strip_comb tm e of
        (t, [t1, t2, t3, t4, t5, t6]) =>
        if same_const t c then (t1, t2, t3, t4, t5, t6) else raise e
      | _ => raise e

  fun make8 tm (a,b,c,d,e,f,g,h) =
    list_mk_icomb (tm, [a, b, c, d, e, f, g, h])

  fun dest8 c e tm =
    case with_exn strip_comb tm e of
        (t, [t1, t2, t3, t4, t5, t6, t7, t8]) =>
        if same_const t c then (t1, t2, t3, t4, t5, t6, t7, t8) else raise e
      | _ => raise e

  val s4 = HolKernel.syntax_fns4 "cf"
  val s5 = HolKernel.syntax_fns {n = 5, make = make5, dest = dest5} "cf"
  val s6 = HolKernel.syntax_fns {n = 6, make = make6, dest = dest6} "cf"
  val s8 = HolKernel.syntax_fns {n = 8, make = make8, dest = dest8} "cf"
in

val (cf_let_tm, mk_cf_let, dest_cf_let, is_cf_let) = s6 "cf_let"
val (cf_lit_tm, mk_cf_lit, dest_cf_lit, is_cf_lit) = s4 "cf_lit"
val (cf_con_tm, mk_cf_con, dest_cf_con, is_cf_con) = s5 "cf_con"
val (cf_var_tm, mk_cf_var, dest_cf_var, is_cf_var) = s4 "cf_var"
val (cf_fun_tm, mk_cf_fun, dest_cf_fun, is_cf_fun) = s8 "cf_fun"
val (cf_fun_rec_tm, mk_cf_fun_rec, dest_cf_fun_rec, is_cf_fun_rec) = s6 "cf_fun_rec"
val (cf_app_tm, mk_cf_app, dest_cf_app, is_cf_app) = s6 "cf_app"

end

end
