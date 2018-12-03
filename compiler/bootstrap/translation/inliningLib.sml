(*
  Stuff used for manual inlining of encoders
*)

structure inliningLib =
struct
  open preamble blastLib;

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

  (* bit-blasts away trivial if splits *)
  fun bconv_gen print avoidp = fn th => th |> SPEC_ALL |>
              RIGHT_CONV_RULE (Conv.DEPTH_CONV (
                (fn t => if type_of t <> ``:bool``orelse avoidp t then NO_CONV t else ALL_CONV t)
                THENC blastLib.BBLAST_CONV
                THENC (if print then PRINT_CONV else ALL_CONV)
                THENC (fn t => if t = boolSyntax.T orelse t = boolSyntax.F then
                                  ALL_CONV t
                               else
                                  NO_CONV t))) |>
              SIMP_RULE (srw_ss()) []

  val bconv = bconv_gen false (fn t => false)

  val spec64 = INST_TYPE[alpha|->``:64``]

  val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

  val spec32 = INST_TYPE[alpha|->``:32``]

  val conv32_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec32 o SPEC_ALL

  (* word_concat *)
  val wc_simp = CONV_RULE (wordsLib.WORD_CONV) o SIMP_RULE std_ss [word_concat_def,word_join_def,w2w_w2w,LET_THM]
  (* word_extract *)
  val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

  val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)
  val econv = CONV_RULE wordsLib.WORD_EVAL_CONV


end
