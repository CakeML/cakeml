(* Stuff used for manual inlining of encoders *)

structure inliningLib =
struct
  open preamble

  (*simple CSE *)
  fun lrthm strip th = th |> SPEC_ALL |> concl |> dest_eq |> (fn (x,y) => (strip x,y))

  fun count_terms tlist =
    foldl (fn (t,d) => case Redblackmap.peek(d,t) of
        SOME n => Redblackmap.insert (d,t,n+1)
      |  _ => Redblackmap.insert (d,t,1)) (Redblackmap.mkDict Term.compare) tlist

  fun is_subterm x y =
    patternMatchesSyntax.has_subterm (fn t => t = x) y

  fun mostgen x [] acc = (x,acc)
  |   mostgen x (y::ys) acc =
    if is_subterm x y then mostgen y ys acc
    else if is_subterm y x then mostgen x ys acc
    else mostgen x ys (y::acc)

  fun filsubs [] = []
  |   filsubs (x::xs) =
    let val (k,vs) = mostgen x xs [] in
      k :: filsubs vs
    end

  fun is_fun_type t =
    (can dom_rng (type_of t))

  fun let_abs v t tt =
    mk_let (mk_abs(v,subst [(t |-> v)] tt),t)

  fun cse lim t =
    let val fvt = free_vars t
        val foo = count_terms (find_terms (fn tt =>
          let val fvs = free_vars tt in
            all (fn v => mem v fvt) fvs andalso
            fvs <> [] andalso
            not(is_fun_type tt) andalso
            not(is_var tt)
          end) t)
        val tlist = map fst (filter (fn (k,v) => v > lim) (Redblackmap.listItems foo))
        val toabs = filsubs tlist
        val name = "cse" in
        #2(foldl (fn (t,(i,tt)) => (i+1,let_abs (mk_var (name^Int.toString i,type_of t)) t tt))
          (0,t) toabs)
    end

  fun csethm lim th =
    let val (l,r) = lrthm I th
        val goal = mk_eq(l,cse lim r) in
        prove(goal, simp[th])
    end

  (*x64_enc i = case i of ... each of ths is one branch*)
  (* reconstructs a case goal *)
  fun reconstruct_case t strip ths =
    let val rhs = TypeBase.mk_case (strip t,map (lrthm strip) ths)
    in
      prove(mk_forall (strip t,mk_eq (t,rhs)),Cases >> simp ths) |> SPEC_ALL
    end
end
