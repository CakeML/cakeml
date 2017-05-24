(* 
   MP_ASSUM:

   (!a in T'. T |= a)      T' |= g
   ===============================
               T |= g
  *)
fun MP_ASSUM thl th =
  let
      val conclList = List.map (fn x => (concl x, x)) thl
      val conclMap = Redblackmap.fromList Term.compare conclList
      val num_hyps = List.length (hyp th)
      val th' = DISCH_ALL th
			  
      fun rec_mp th n =
	if n > 0 then
	    let
		val h = concl th |> dest_imp |> fst
		val hyp_th = Redblackmap.find (conclMap, h)
		val th' = MP th hyp_th 
	    in
		rec_mp th' (n-1)
	    end
	else th
  in
      rec_mp th' num_hyps
  end;
(*
   CONV_ASSUM: use a conversion to rewrite an assumption list so that:
   (!a' in T'. T |= a') /\ (!a in T. T' |= a)
   Returns the list of theorems: !a' in T'. T |= a'
*)
fun CONV_ASSUM sset rws asl =
  let
      val tautl = List.map ASSUME asl |> List.map CONJUNCTS |> List.concat
			   
      fun try_conv conv th =
	let
	    
	    val th' = CONV_RULE (CHANGED_CONV conv) th
	in
	    (th', true)
	end
	handle _ => (th, false)

      fun rec_conv thl =
	if List.length thl > 0 then
	    let
		val convThPairs = List.map (try_conv (SIMP_CONV sset rws)) thl
		val (changedThPairs, sameThPairs) = List.partition (fn (_, b) => b) convThPairs
		val sameThl = List.map (fn (x, _) => x) sameThPairs
		val changedThl = List.map (fn (x, _) => x) changedThPairs
		val changedThl' = List.map CONJUNCTS changedThl |> List.concat |> rec_conv
	    in
		List.revAppend (sameThl, changedThl')
	    end
	else
	    []
  in
      rec_conv tautl
  end;


