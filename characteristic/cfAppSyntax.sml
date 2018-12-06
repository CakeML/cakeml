(*
  Helper functions that construct/destruct syntax from cfAppTheory.
*)
structure cfAppSyntax :> cfAppSyntax = struct
open Abbrev

local
  open HolKernel boolLib bossLib cfAppTheory

  fun make5 tm (a,b,c,d,e) =
    list_mk_icomb (tm, [a, b, c, d, e])

  fun dest5 c e tm =
    case with_exn strip_comb tm e of
        (t, [t1, t2, t3, t4, t5]) =>
        if same_const t c then (t1, t2, t3, t4, t5) else raise e
      | _ => raise e

  val s3 = HolKernel.syntax_fns3 "cfApp"
  val s5 = HolKernel.syntax_fns {n = 5, make = make5, dest = dest5} "cfApp"
in

val (app_basic_tm, mk_app_basic, dest_app_basic, is_app_basic) = s5 "app_basic"
val (app_tm, mk_app, dest_app, is_app) = s5 "app"
val (curried_tm, mk_curried, dest_curried, is_curried) = s3 "curried"

end

end
