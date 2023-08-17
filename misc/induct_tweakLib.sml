(*
  Code for adjusting and improving induction theorems.
*)

(* induct_tweakLib.list_single_induct : thm -> thm

  adjusts a typical induction theorem produced from a function declaration,
  with a conclusion like this:
  (!x. P1 x) /\ (!xs. P2 xs)
  by instantiating P1 with `\x. P2 [x]` and dropping the P1 clause from
  the conclusion.
*)

structure induct_tweakLib =
struct

open HolKernel boolLib bossLib;

fun select_conjs sels t =
  zip sels (CONJUNCTS t) |> filter fst |> map snd |> LIST_CONJ

fun build_by_singleton typ P = let
    val (arg_typs, _) = strip_fun typ
    val (P_arg_typs, _) = strip_fun (type_of P)
    val _ = length arg_typs = length P_arg_typs orelse raise Option
    val args = mapi (fn i => fn ty => mk_var ("v" ^ Int.toString i, ty))
        arg_typs
    fun strip_list_type typ = case total listSyntax.dest_list_type typ of
        NONE => (0, typ)
      | SOME typ => apfst (fn i => i + 1) (strip_list_type typ)
    fun mk_sing 0 x = x
      | mk_sing i x = mk_sing (i - 1) (listSyntax.mk_list ([x], type_of x))
    fun coerce arg typ = let
        val (i, arg_typ) = strip_list_type (type_of arg)
        val (j, typ) = strip_list_type typ
        val _ = arg_typ = typ orelse raise Option
        val _ = i <= j orelse raise Option
      in mk_sing (j - i) arg end
    val coerced_args = map2 coerce args P_arg_typs
  in list_mk_abs (args, list_mk_comb (P, coerced_args)) end

fun list_single_induct t = let
    val (Ps, _) = strip_forall (concl t)
    fun get_adj P = get_first (total (pair P o build_by_singleton (type_of P)))
        (filter (not o term_eq P) Ps)
    val (P, subs) = valOf (get_first get_adj Ps)
    val t2 = SPECL (map (fn P2 => if term_eq P P2 then subs else P2) Ps) t
      |> CONV_RULE (DEPTH_CONV BETA_CONV)
      |> UNDISCH
      |> select_conjs (map (not o term_eq P) Ps)
      |> DISCH_ALL
      |> GENL (filter (not o term_eq P) Ps)
  in list_single_induct t2 end handle Option => t

end


