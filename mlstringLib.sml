structure mlstringLib :> mlstringLib = struct

open HolKernel boolLib bossLib lcsymtacs

fun smart_dest_mlstring_case tm =
  let
    val (discriminee, strabs) = mlstringSyntax.dest_mlstring_case tm
    val (v, strcase) = dest_abs strabs
    val (v, strips) = TypeBase.strip_case strcase
    val (strs,vars) = partition (null o free_vars o fst) strips
    val (emps,strs) = partition (stringSyntax.is_emptystring o fst) strs
    val (strs,varstrips) =
      let val losers = emps@vars in
        if null(tl(mk_set(map snd losers)))
          then (strs,losers)
        else (hd emps::strs,vars)
      end
    val (x,y) = hd varstrips
  in
    (discriminee,strs,y)
  end

fun mlstring_case_conv tm =
  let
    val (realt,ls,d) = smart_dest_mlstring_case tm
    val t = mk_var("t",type_of realt)
    val l = length ls
    val ty = type_of d
    val xs = List.tabulate(l, fn i => mk_var("x"^(Int.toString i),ty))
    val xd = mk_var("x"^(Int.toString l),ty)
    val x = mk_var("x",type_of t)
    val varls = zip (map fst ls) xs
    val r =
      boolSyntax.mk_let(mk_abs(x,
        List.foldl (fn ((s,xn),tm) =>
          boolSyntax.mk_cond(mk_eq(x,mlstringSyntax.mk_strlit s),xn,tm))
        xd varls)
                       ,t)
    val mlvarls = map (fn (x,y) => (mlstringSyntax.mk_strlit x,y)) varls
    val l = TypeBase.mk_pattern_fn (mlvarls@[(mk_var("_",mlstringSyntax.mlstring_ty),xd)])
    val g = list_mk_forall(t::xd::xs,mk_eq(beta_conv(mk_comb(l,t)),r))
    val the_ss =
      boolSimps.bool_ss++stringSimps.STRING_ss++listSimps.LIST_ss++
      (simpLib.std_conv_ss{conv=stringLib.char_EQ_CONV,
                           name="char_EQ_CONV",
                           pats=[``x:char = y``]})
    val the_rws = [
      mlstringTheory.mlstring_11,
      mlstringTheory.mlstring_case_def]
    val th = prove(g, (* (set_goal([],g)) *)
      rpt gen_tac >>
      CONV_TAC(RAND_CONV(PairedLambda.let_CONV)) >>
      BasicProvers.PURE_CASE_TAC >>
      SIMP_TAC pure_ss the_rws >>
      rpt(BasicProvers.PURE_CASE_TAC >> FULL_SIMP_TAC the_ss []))
    val ith = SPECL (realt::d::(map snd ls)) th
    val sth = CONV_RULE (RAND_CONV(PURE_REWRITE_CONV[boolTheory.bool_case_ID])) ith
    val g2 = mk_eq(tm,lhs(concl sth))
    val th1 = prove(g2, SIMP_TAC bool_ss [])
  in
    TRANS th1 sth
  end

end
