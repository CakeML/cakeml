structure labels_computeLib = struct
open HolKernel repl_computeLib bytecodeLabelsTheory

fun hide_list_chunks_conv chunk_size tm =
  let
    fun f n tm =
      if listSyntax.is_nil tm
        then (REFL tm, Redblackmap.mkDict(String.compare))
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
                else RATOR_CONV(RAND_CONV(TRY_CONV(RATOR_CONV(RAND_CONV(REWR_CONV fm_def))
                                                   THENC ffconv)))
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
val tm = ``code_labels (K 0) ^ls``
val th = time code_labels_conv tm

*)
end
