(*
  Library code for applying the type-dec to pp-dec functions
  to the ml_progLib state. Used in the basis to install
  default pretty-printers for some of the basis types.
*)
structure addPrettyPrintersLib = struct

open ml_progLib astSyntax listSyntax
  HolKernel bossLib boolSyntax Drule
local open typeDecToPPTheory namespaceTheory in end

val no_decs = mk_list ([], dec_ty)

val empty_local = mk_Dlocal (no_decs, no_decs)

fun dec_global_only t = if is_Dmod t
    then empty_local
    else if is_Dlocal t
    then empty_local
    else let
      val (f, xs) = strip_comb t
    in list_mk_comb (f, map dec_global_only xs) end

val pps_for_dec_tm = typeDecToPPTheory.pps_for_dec_def |> BODY_CONJUNCTS |> hd
    |> concl |> lhs |> strip_comb |> fst

val ns_ty = pps_for_dec_tm |> type_of |> dom_rng |> fst

val nsEmpty1 = namespaceTheory.nsEmpty_def |> concl |> lhs
val nsEmpty = nsEmpty1 |> inst (match_type (type_of nsEmpty1) ns_ty)

val pps_for_dec_empty = mk_icomb (pps_for_dec_tm, nsEmpty)

fun pps_of_global_tys prog = let
    val gl = dec_global_only prog
    val app = mk_flat (mk_map (pps_for_dec_empty, gl))
    val eval = EVAL app
    val res = rhs (concl eval)
    val (pp_decs, _) = dest_list res
  in pp_decs end

fun add_pps pps prog_st = foldl (fn (pp, prog_st) => add_dec pp I prog_st) prog_st pps

end

