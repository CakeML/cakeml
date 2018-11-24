(*
  Defines ELIM_UNKWN_CONV conversion
*)
structure eqSolveRewriteLib :> eqSolveRewriteLib =
struct

open HolKernel boolLib Conv helperLib
(* TODO: helperLib is used for list_dest - it should be added to HOL more prominently *)

fun xor x y = (x orelse y) andalso (not (x andalso y));

(* [is_known]
   Return true if the given term contains an unknown variable, false otherwise.
 *)
fun is_knwn knwn_vars tm =
  case (dest_term tm) of
      VAR _ => HOLset.member (knwn_vars, tm)
    | CONST _ => true
    | COMB (tm1, tm2) => is_knwn knwn_vars tm1 andalso is_knwn knwn_vars tm2
    | LAMB (v, tm') => is_knwn (HOLset.add (knwn_vars, v)) tm';

(* [find_possible_rws]
   Return the list of equalities between known and unknown terms.
*)
fun find_possible_rws knwn_vars tm =
  let
      val clauses = list_dest dest_conj tm
      fun unkwn_def_eq e =
	if is_eq e then
	    let
		val (t1, t2) = dest_eq e
		val (b1, b2) = (is_knwn knwn_vars t1, is_knwn knwn_vars t2)
	    in
		xor b1 b2
	    end
	else
	    false
  in
      List.partition unkwn_def_eq clauses
  end;

(* [reconstruct_conj]
   Reconstruct a conjunction so that the selected clause is moved to the first position.
*)
fun reconstruct_conj knwn_vars tm eq clauses =
  let
      val recon_tm = mk_conj (eq, list_mk mk_conj clauses ``T``)

      (* Prove that this new term is egal to the original one *)
      val conv_th = AC_CONV (CONJ_ASSOC, CONJ_SYM) (mk_eq (tm, recon_tm)) |> EQT_ELIM

      (* If necessary, invert the equality *)
      val must_inverse = let val (x, y) = dest_eq eq in
			     (is_knwn knwn_vars x, is_knwn knwn_vars y) = (true, false) end
      val final_th = if must_inverse then CONV_RULE (PATH_CONV "rlr" SYM_CONV) conv_th else conv_th
  in
      final_th
  end;

(* [rewrite_with_first]  *)
fun rewrite_with_first t =
  let
      val eq_clause = dest_conj t |> fst
      val eq_thm = ASSUME eq_clause

      val conv_equiv = CHANGED_CONV (RAND_CONV(PURE_REWRITE_CONV [eq_thm])) t
      val (imp, recip) = EQ_IMP_RULE conv_equiv

      fun prove_imp imp =
	let
	    val t = dest_imp (concl imp) |> fst
	    val t_imp_eq = ASSUME t |> CONJUNCT1
	    val t_imp = MP (DISCH_ALL imp) t_imp_eq
	in
	    DISCH_ALL (UNDISCH_ALL t_imp)
	end

      val (imp', recip') = (prove_imp imp, prove_imp recip)
      val final_eq = IMP_ANTISYM_RULE imp' recip'
  in
      final_eq
  end;

(* [ELIM_UNKWN_ONCE] *)
fun ELIM_UNKWN_ONCE knwn_vars t =
  let
      val (eq_clauses, other_clauses) = find_possible_rws knwn_vars t
      fun try_elim eq clauses =
	let
	    val conv1 = reconstruct_conj knwn_vars t eq clauses
	    val t' = concl conv1 |> dest_eq |> snd
	    val conv2 = rewrite_with_first t'
	    val conv3 = Thm.TRANS conv1 conv2
	in
	    conv3
	end

      fun try_all_elim (eq::eqs) clauses =
	(try_elim eq (List.revAppend(eqs, clauses)) handle _ => try_all_elim eqs (eq::clauses))
	| try_all_elim [] clauses = failwith ""

      val t' = try_all_elim eq_clauses other_clauses
  in
      t'
  end
  handle _ => failwith "ELIM_UNKWN_ONCE"

(* [ELIM_UNKWN_CONV] *)
fun ELIM_UNKWN_CONV knwn_vars t =
  let
      val conv_t = ELIM_UNKWN_ONCE knwn_vars t
  in
      let
	  val conv_t' = ELIM_UNKWN_CONV knwn_vars (concl conv_t |> dest_eq |> snd)
	  val conv_t'' = Thm.TRANS conv_t conv_t'
      in
	  conv_t''
      end
      handle _ => conv_t
  end
  handle _ => Thm.REFL t;

end
