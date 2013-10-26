structure labels_computeLib = struct
open HolKernel patriciaLib repl_computeLib bytecodeLabelsTheory labels_computeTheory permLib

fun collect_labels code l =
  let
    fun f [] p acc = acc
      | f (x::xs) p acc =
        let
          val (con,args) = strip_comb x
        in
          if fst(dest_const con) = "Label"
            then
              let
                val n = numSyntax.dest_numeral(hd args)
              in
                f xs p (patriciaLib.add acc (n,p))
              end
          else
            let
              val p = numSyntax.mk_suc(numSyntax.mk_plus(p,mk_comb(l,x)))
            in
              f xs (rhs(concl(EVAL p))) acc
            end
        end
  in
    patriciaLib.mk_ptree
      (f (fst(listSyntax.dest_list code)) numSyntax.zero_tm patriciaLib.empty)
  end

val stringDict : (string,thm) Redblackmap.dict = Redblackmap.mkDict String.compare

val good_label_map_tm = ``good_label_map``
val good_label_map_nil = CONJUNCT1 good_label_map_def
val good_label_map_Label = good_label_map_def |> CONJUNCT2 |> CONJUNCT1
val cases = good_label_map_def |> CONJUNCT2 |> CONJUNCT2 |> CONJUNCTS
val good_label_map_others =
  foldl (fn (th,n) =>
    let
      val tm = th |> concl |> strip_forall |> snd |> lhs |> strip_comb |> snd |> hd |> rator |> rand
      val name = tm |> strip_comb |> fst |> dest_const |> fst
    in
      Redblackmap.insert
        (n
        ,name
        ,th)
    end)
  stringDict cases

val and1 = CONJUNCT1 (SPEC_ALL AND_CLAUSES)

fun good_label_map_conv ptdef map =
  let
    fun f tm =
      let
        val (_,[ls,p,l,pf,ks]) = strip_comb tm
        val conv =
          let
            val (x,xs) = listSyntax.dest_cons ls
            val (con,args) = strip_comb x
            val name = fst(dest_const con)
          in
            if name = "Label"
              then
                REWR_CONV good_label_map_Label
                THENC LAND_CONV
                  (LAND_CONV
                     (RATOR_CONV(RAND_CONV(REWR_CONV ptdef))
                      THENC patriciaLib.PTREE_CONV)
                   THENC REWR_CONV REFL_CLAUSE)
                THENC REWR_CONV and1
            else
              REWR_CONV (Redblackmap.find(good_label_map_others,name))
              THENC RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV EVAL)))
          end
          handle e as HOL_ERR _ =>
            if listSyntax.is_nil ls
              then raise e
            else
              let
                val name = fst(dest_const ls)
                val _ = print (" expanding "^name)
              in
                Redblackmap.find(map,name) |> REWR_CONV |> RAND_CONV
                  |> RATOR_CONV |> RATOR_CONV |> RATOR_CONV |> RATOR_CONV
              end
      in
        (conv THENC f) tm
      end
      handle HOL_ERR _ =>
        (REWR_CONV good_label_map_nil
         THENC RATOR_CONV(RAND_CONV (RAND_CONV(REWR_CONV ptdef) THENC EVAL))
         THENC permLib.PERM_NORMALISE_CONV)
        tm
  in f
  end

fun hide_list_chunks_conv chunk_size tm =
  let
    fun f n tm =
      if listSyntax.is_nil tm
        then (REFL tm, stringDict)
      else
        let
          val (x,xs) = listSyntax.dest_cons tm
        in
          if n < chunk_size
            then
              let
                val (th,net) = f (n+1) xs
              in
                (AP_TERM(mk_icomb(listSyntax.cons_tm,x)) th
                ,net)
              end
          else
            let
              val (th,net) = f 0 xs
              val def = mk_def (listSyntax.mk_cons(x,rhs(concl th)))
              val const = lhs(concl def)
              val th = (REWR_CONV def THENC (RAND_CONV (REWR_CONV (SYM th)))) const
            in
              (SYM th
              ,Redblackmap.insert(net,fst(dest_const const),def))
            end
        end
  in
    f 0 tm
  end

val inst_labels_fn_nil = CONJUNCT1 inst_labels_fn_def
val (inst_labels_fn_other,inst_labels_fn_Lab) =
  foldl (fn (th,(d1,d2)) =>
    let
      val tm = th |> concl |> strip_forall |> snd |> lhs |> rand |> rator |> rand
      val (con,args) = strip_comb tm
      val argname = (args |> hd |> strip_comb |> fst |> dest_const |> fst) handle _ => ""
    in
      if argname = "Addr"
        then (d1,d2)
      else
        let
          val k = con |> dest_const |> fst
          fun ins d = Redblackmap.insert (d,k,th)
        in
          if argname = "Lab"
            then (d1, ins d2)
          else (ins d1, d2)
        end
    end)
  (stringDict,stringDict)
  (CONJUNCTS(CONJUNCT2 inst_labels_fn_def))

val option_CASE_2 = CONJUNCT2 optionTheory.option_case_def

fun inst_labels_fn_conv ptdef map =
  let
    fun ilconv tm =
      let
        val (_,[f,ls]) = strip_comb tm
      in
        if listSyntax.is_nil ls
          then SPEC f inst_labels_fn_nil
        else
          let
            val (x,xs) = listSyntax.dest_cons ls
            val name = fst(dest_const(fst(strip_comb x)))
            val conv =
              let
                val th = Redblackmap.find(inst_labels_fn_Lab,name)
                val conv =
                  RATOR_CONV(RAND_CONV(RAND_CONV
                    (RATOR_CONV(RATOR_CONV(RAND_CONV
                      (RATOR_CONV(RAND_CONV(REWR_CONV ptdef))
                       THENC patriciaLib.PTREE_CONV)))
                     THENC REWR_CONV option_CASE_2
                     THENC BETA_CONV)))
              in
                REWR_CONV th
                THENC conv
                THENC (RAND_CONV ilconv)
              end
              handle NotFound =>
                let
                  val th = Redblackmap.find(inst_labels_fn_other,name)
                in
                  REWR_CONV th
                  THENC (if name = "Label"
                           then ilconv
                         else RAND_CONV ilconv)
                end
          in
            conv tm
          end
          handle HOL_ERR e =>
            let
              val name = fst(dest_const ls)
              val _ = print (" expanding "^name)
              val def = Redblackmap.find(map,fst(dest_const ls))
            in
              (RAND_CONV(REWR_CONV def)
               THENC ilconv)
              tm
            end
            handle HOL_ERR _ => raise HOL_ERR e
      end
  in
    ilconv
  end

fun code_labels_conv tm =
  let
    val (_,[l,code]) = strip_comb tm
    val pt = collect_labels code l
    val _ = print "proving IS_PTREE hypothesis: "
    val th1 = time
                (with_flag(patriciaLib.is_ptree_term_size_limit,~1)
                   patriciaLib.PTREE_IS_PTREE_CONV)
                (patriciaSyntax.mk_is_ptree pt)
              |> EQT_ELIM
    val (codeth,map) = hide_list_chunks_conv 20 code
    val codeabb = rhs(concl codeth)
    val ptdef = mk_def pt
    val ptabb = lhs(concl ptdef)
    val tm2 = list_mk_comb
                (good_label_map_tm,
                 [codeabb,
                  numSyntax.zero_tm,
                  l,
                  ptabb,
                  listSyntax.mk_nil numSyntax.num])
    val _ = print "proving good_label_map hypothesis: "
    val th2 = time (good_label_map_conv ptdef map) tm2 |> EQT_ELIM
    val th3 = SPECL [ptabb,l,codeabb] inst_labels_fn_intro
    val th0 = CONV_RULE(RAND_CONV(REWR_CONV(SYM ptdef))) th1
    val th4 = PROVE_HYP (CONJ th2 th0) (UNDISCH th3)
    val th5 = CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV(SYM codeth)))) th4
    val _ = print "evaluating inst_labels_fn: "
    val th6 = time (RIGHT_CONV_RULE (inst_labels_fn_conv ptdef map)) th5
    val _ = Redblackmap.app (delete_const o fst) map
    val _ = delete_const (fst (dest_const ptabb))
  in
    th6
  end

(*
val collect_labels_nil = CONJUNCT1 collect_labels_def
val collect_labels_Label = CONJUNCT2 collect_labels_def |> SPEC ``Label l`` |> SIMP_RULE(srw_ss())[] |> GEN_ALL
val cases = CONJUNCT2 collect_labels_def |> SPEC_ALL |> concl |> rhs |> TypeBase.strip_case
  |> snd |> map fst |> filter (fn tm => fst(dest_const(fst(strip_comb tm))) <> "Label")
val collect_labels_others =
  foldl (fn (t,n) => Redblackmap.insert
    (n
    ,fst(dest_const(fst(strip_comb t)))
    ,CONJUNCT2 collect_labels_def |> SPEC t |> SIMP_RULE(srw_ss())[] |> GEN_ALL))
  (Redblackmap.mkDict String.compare) cases

fun collect_labels_conv net =
  let
    fun clconv tm =
      let
        val (_,[xs,p,l]) = strip_comb tm
      in
        if listSyntax.is_nil xs
          then SPECL[p,l]collect_labels_nil
        else if listSyntax.is_cons xs
          then
            let
              val (x,xs) = listSyntax.dest_cons xs
              val (con,args) = strip_comb x
              val name = fst(dest_const con)
              val conv =
                if name = "Label"
                  then
                    ((fn tm => SPECL [hd args,xs,p,l] collect_labels_Label)
                     THENC (RATOR_CONV(RAND_CONV(clconv))))
                else
                  let
                    val th = Redblackmap.find(collect_labels_others,name)
                  in
                    ((fn tm => SPECL (args@[xs,p,l]) th)
                     THENC (RATOR_CONV(RAND_CONV(EVAL)))
                     THENC clconv)
                  end
            in
              conv tm
            end
        else
          let
            val def = Redblackmap.find(net,fst(dest_const xs))
            val conv =
              ((RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV def))))
               THENC clconv)
          in
            conv tm
          end
      end
  in
    clconv
  end

fun all_labels_conv net = REWR_CONV all_labels_def THENC (collect_labels_conv net)

val inst_labels_nil = CONJUNCT1 inst_labels_def
val inst_labels_cons =
  foldl (fn (th,n) =>
    let
      val tm = th |> concl |> strip_forall |> snd |> lhs |> rand |> rator |> rand
      val (con,args) = strip_comb tm
      val is_Addr = (args |> hd |> strip_comb |> fst |> dest_const |> fst |> equal "Addr") handle _ => false
    in
      if is_Addr
        then n
      else
        Redblackmap.insert
          (n
          ,con |> dest_const |> fst
          ,th)
    end)
  (Redblackmap.mkDict String.compare)
  (CONJUNCTS(CONJUNCT2 inst_labels_def))

val ffconv = flookup_fupdate_conv numeq_conv
fun inst_labels_conv fm_def net =
  let
    fun ilconv tm =
      let
        val (_,[f,ls]) = strip_comb tm
      in
        if listSyntax.is_nil ls
          then SPEC f inst_labels_nil
        else if listSyntax.is_cons ls
          then
            let
              val (x,xs) = listSyntax.dest_cons ls
              val name = fst(dest_const(fst(strip_comb x)))
              val th = Redblackmap.find(inst_labels_cons,name)
              val conv =
                if name = "Label"
                  then ilconv
                else RATOR_CONV(
                       RAND_CONV(
                         TRY_CONV(
                           RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(
                             RATOR_CONV(RAND_CONV(REWR_CONV fm_def))
                             THENC ffconv)))))))
                     THENC (RAND_CONV ilconv)
            in
              (REWR_CONV th
               THENC conv)
              tm
            end
        else
          let
            val def = Redblackmap.find(net,fst(dest_const ls))
          in
            (RAND_CONV(REWR_CONV def)
             THENC ilconv)
            tm
          end
      end
  in
    ilconv
  end

fun code_labels_conv tm = let
  val (_,[l,code]) = strip_comb tm
  val (codeth,net) = hide_list_chunks_conv 20 code
  val th = (RAND_CONV(K codeth)
            THENC REWR_CONV code_labels_def
            THENC (RATOR_CONV(RAND_CONV (all_labels_conv net))))
           tm
  val fm_def = mk_def(rand(rator(rhs(concl(th)))))
  val new_th = RIGHT_CONV_RULE (RATOR_CONV(RAND_CONV(REWR_CONV(SYM fm_def)))) th
  val th2 = RIGHT_CONV_RULE (inst_labels_conv fm_def net) new_th
  val th3 = ALL_HYP_CONV_RULE numeq_conv th2
  val _ = Redblackmap.app (delete_const o fst) net
in
  th3
end
*)

(*
local
  val bc_inst = ``:bc_inst``
  val Label = ``Label``
  val Jump = ``Jump``
  val Lab = ``Lab``
  fun mk_Label tm = mk_comb(Label,tm)
  fun mk_Jump n = mk_comb(Jump,mk_comb(Lab,n))
  fun f n ls = if n < 0 then ls else
    let
      val ntm = numSyntax.term_of_int n
    in
      f (n-1) (listSyntax.mk_cons(mk_Jump ntm,listSyntax.mk_cons(mk_Label ntm,ls)))
    end
in
  fun genls n = f n (listSyntax.mk_nil bc_inst)
end

val ls = genls 1000
val l =``(K 0):bc_inst -> num``
val tm = ``code_labels ^l ^ls``

patriciaLib.is_ptree_term_size_limit := ~1
val pt = patriciaLib.mk_ptree (collect_labels ls l)
val th1 = patriciaLib.PTREE_IS_PTREE_CONV(patriciaSyntax.mk_is_ptree pt)

val tm = ``code_labels (K 0) ^ls``
val th = time code_labels_conv tm

*)
end
