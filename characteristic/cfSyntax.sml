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

  val s4 = HolKernel.syntax_fns4 "cf"
  val s5 = HolKernel.syntax_fns {n = 5, make = make5, dest = dest5} "cf"
in

val (cf_lit_tm, mk_cf_lit, dest_cf_lit, is_cf_lit) = s4 "cf_lit"
val (cf_con_tm, mk_cf_con, dest_cf_con, is_cf_con) = s5 "cf_con"
val (cf_var_tm, mk_cf_var, dest_cf_var, is_cf_var) = s4 "cf_var"

end

end
