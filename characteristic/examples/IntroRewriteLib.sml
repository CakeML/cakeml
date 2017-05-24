structure IntroRewrite :> IntroRewrite =
struct

open Thm Tactical

(* INTRO_REWRITE_CONV *)
fun INTRO_REWRITE_CONV thl asl =
    let
	val assumed_asl = map ASSUME asl
	val disj_thl = List.concat (List.map CONJUNCTS thl) 
	fun match_on_asl th = mapfilter (MATCH_MP th) assumed_asl
	fun is_rw_th th = SPEC_ALL th |> concl |> is_eq
	fun generate_rewrites thl =
	  let
	      val (rewrite_thl, thl') = List.partition is_rw_th thl
	      val thl'' = List.concat (mapfilter match_on_asl thl')
	  in
	      case thl'' of
		  [] => rewrite_thl
		| _ => List.revAppend (generate_rewrites thl'', rewrite_thl)
	  end
	val rw_thms = generate_rewrites disj_thl
    in
	SIMP_CONV bool_ss rw_thms
    end;

(* INTRO_REWRITE_TAC *)
fun INTRO_REWRITE_TAC rws (g as (asl, w)) = CONV_TAC (INTRO_REWRITE_CONV rws asl) g;

end
