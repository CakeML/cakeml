structure compute_bytecodeLib = struct
  open HolKernel boolLib bossLib lcsymtacs bytecodeLabelsTheory labels_computeTheory patriciaLib


val bc_fetch_aux_0_thm = prove(
  ``∀code pc. bc_fetch_aux code (K 0) pc =
    if no_labels code then
      if pc < LENGTH code then SOME (EL pc code) else NONE
    else FAIL (bc_fetch_aux code (K 0) pc) "code has labels"``,
  REWRITE_TAC[bytecodeLabelsTheory.no_labels_def] >>
  Induct >> simp[bytecodeTheory.bc_fetch_aux_def] >>
  rw[] >> fs[combinTheory.FAIL_DEF] >>
  simp[rich_listTheory.EL_CONS,arithmeticTheory.PRE_SUB1])

  val SUC_TO_NUMERAL_RULE = CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)

val eval_real_inst_length =
  let
    val compset = reduceLib.num_compset()
    val () = intReduce.add_int_compset compset
    val () = computeLib.add_thms [bytecodeExtraTheory.real_inst_length_compute] compset
  in
    computeLib.CBV_CONV compset
  end


  fun add_bytecode_compset compset = let

    local open bytecodeTheory in
      val () = computeLib.add_thms
        [bool_to_tag_def
        ,unit_tag_def
        ,closure_tag_def
        ,string_tag_def
        ,block_tag_def
        ,bump_pc_def
        ,bc_fetch_def
        ,bv_to_string_def
        ,bvs_to_chars_def
        ,bc_equality_result_to_val_def
        ,bool_to_val_def
        ,bool_to_tag_def
        ,bc_find_loc_def
        ,bytecodeTerminationTheory.bc_equal_def
        ] compset
    end

    local open bytecodeEvalTheory in
      val () = computeLib.add_thms
        [bc_eval_compute
        ,bc_eval1_def
        ,bc_eval_stack_def
        ,bc_fetch_aux_0_thm
        ,SUC_TO_NUMERAL_RULE bc_evaln_def
        ,listTheory.LUPDATE_compute
        ] compset
    end
    val () = computeLib.add_datatype_info compset (valOf(TypeBase.fetch``:bc_state``))
    val () = computeLib.add_datatype_info compset (valOf(TypeBase.fetch``:bc_value``))
    val () = computeLib.add_conv(``real_inst_length``,1,eval_real_inst_length) compset
    (*val () = computeLib.add_datatype_info compset (valOf(TypeBase.fetch``:bc_inst``))*)
  in () end

  val Addr_tm = ``Addr``
  fun mk_Addr x = mk_comb(Addr_tm,x)

  val quiet = ref false
  fun info s = if !quiet then () else HOL_MESG s
  fun time x = if !quiet then x else Lib.time x

  fun ml_code_labels lconv code l =
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
                  f xs p (patriciaLib.add acc (n,numSyntax.mk_numeral p))
                end
            else
              let
                val lx = numSyntax.dest_numeral(rhs(concl(lconv(mk_comb(l,x)))))
              in
                f xs (Arbnum.+(p,Arbnum.plus1(lx))) acc
              end
          end
      val (codels,ty) = listSyntax.dest_list code
      val pt = f codels Arbnum.zero patriciaLib.empty
      fun g [] acc = List.rev acc
        | g (x::xs) acc =
          let
            val (con,args) = strip_comb x
          in
            if fst(dest_const con) = "Label"
              then g xs acc
            else
              let
                val [arg] = args
                val (lab,[n]) = strip_comb arg
                val ("Lab",_) = dest_const lab
                val SOME m = patriciaLib.peek pt (numSyntax.dest_numeral n)
              in
                g xs ((mk_comb(con,mk_Addr m))::acc)
              end
              handle Bind => g xs (x::acc)
          end
    in
      (patriciaLib.mk_ptree pt
      ,listSyntax.mk_list(g codels [],ty))
    end

  val good_label_map_tm = ``good_label_map``
  val good_label_map_nil = CONJUNCT1 good_label_map_clauses
  val good_label_map_Label = CONJUNCT1 (CONJUNCT2 good_label_map_clauses)
  val good_label_map_Lab =
    good_label_map_clauses
    |> CONJUNCT2 |> CONJUNCT2 |> CONJUNCTS
    |> zip ["PushPtr","Call","Jump","JumpIf"]
  val good_label_map_others =
    good_label_map_def
    |> SIMP_RULE (srw_ss()) []
    |> CONJUNCTS |> tl
    |> filter (not o is_neg o snd o strip_forall o concl)
    |> filter (not o C mem ["Label","PushPtr","Call","Jump","JumpIf"] o fst o dest_const o fst o strip_comb o rand o rator
               o rand o rator o rator o rator o rator o lhs o snd o strip_forall o concl)
    |> map (fn th =>
         let
           val tm = th |> concl |> strip_forall |> snd |> rhs |> rator |> rand |> lhs
         in
           (fst(dest_const(fst(strip_comb tm)))
           ,th |> SPEC_ALL |> Q.GEN`u` |> SPEC tm |> SIMP_RULE (srw_ss()) [])
         end)

  val and1 = CONJUNCT1 (SPEC_ALL AND_CLAUSES)

  val memoref = ref (Redblackmap.mkDict Arbnum.compare)

  fun peekconv ptdef =
    let
      val conv =
            (RATOR_CONV(RAND_CONV(REWR_CONV ptdef))
             THENC patriciaLib.PTREE_PEEK_CONV)
      fun f tm =
        let
          val memo = !memoref
          val (_,[pt,nt]) = strip_comb tm
          val n = numSyntax.dest_numeral nt
        in
          case Redblackmap.peek(memo,n) of
            SOME th => th
          | NONE =>
            let
              val th = conv tm
              val _ = memoref := Redblackmap.insert(memo,n,th)
            in
              th
            end
        end
    in f
    end

  fun good_label_map_conv lconv ptdef =
    let
      val _ = memoref := Redblackmap.mkDict Arbnum.compare
      val ptconv =
            LAND_CONV
              (LAND_CONV (peekconv ptdef)
               THENC REWR_CONV REFL_CLAUSE)
            THENC REWR_CONV and1
      val pconv =
            RATOR_CONV
              (RATOR_CONV
                 (RAND_CONV
                    (RAND_CONV(RAND_CONV lconv)
                     THENC numLib.REDUCE_CONV)))
      fun f count tm =
        let
          val _ = if count mod 1000 = 0 then info ((Int.toString count)^"..") else ()
          val (_,[ls,us,p,l,pt]) = strip_comb tm
          val conv =
            let
              val (x,xs) = listSyntax.dest_cons ls
              val (con,args) = strip_comb x
              val name = fst(dest_const con)
            in
              if name = "Label"
                then
                  REWR_CONV good_label_map_Label
                  THENC ptconv
              else
                REWR_CONV (assoc name good_label_map_others)
                THENC pconv
                handle
                  HOL_ERR _ =>
                    REWR_CONV (assoc name good_label_map_Lab)
                    THENC ptconv
                    THENC pconv
            end
        in
          (conv THENC (f (count+1))) tm
        end
        handle HOL_ERR _ =>
          REWR_CONV good_label_map_nil tm
    in f 0
    end

  val init_db = Net.insert (rand(concl(code_labels_ok_nil)),code_labels_ok_nil) Net.empty
  val db = ref init_db

  val quiet = quiet

  fun reset_code_labels_ok_db () = db := init_db
  fun add_code_labels_ok_thm th =
    let
      val (f,tm) = dest_comb (concl th)
      val _ = assert (same_const ``code_labels_ok``) f
    in
      if null (Net.index tm (!db)) then
        db := Net.insert(tm,th) (!db)
      else ()
    end
  val last_code_not_found = ref listSyntax.nil_tm
  fun get_code_labels_ok_thm tm =
    case Net.index tm (!db) of th::_ => th
    | [] =>
      ( last_code_not_found := tm
      ; raise (mk_HOL_ERR "compute_bytecode_Lib" "get_code_labels_ok_thm" "code_labels_ok theorem not found."))
  fun code_labels_ok_thms() = Net.listItems(!db)

  val mk_def = let
    val iref = ref 0
  in
    fn t => let
      val i = !iref
      val _ = iref := !iref + 1;
      val nm = "internal" ^ Int.toString (!iref)
    in
      new_definition(nm ^ "_def", mk_eq(mk_var(nm, type_of t), t))
    end
  end

  fun code_labels_conv lconv tm =
    let
      val (_,[l,code]) = strip_comb tm
      val th0 = get_code_labels_ok_thm code
      val (pt,us) = ml_code_labels lconv code l
      val pt = inst[alpha|->numSyntax.num] pt (* in case pt is empty *)
      val ptdef = mk_def pt
      val ptabb = lhs(concl ptdef)
      val th = SPECL [ptabb,l,code,us] code_labels_elim
      val tm2 = list_mk_comb
                  (good_label_map_tm,
                   [code, us,
                    numSyntax.zero_tm,
                    l, ptabb])
      val _ = info "proving good_label_map hypothesis: "
      val th2 = time (good_label_map_conv lconv ptdef) tm2 |> EQT_ELIM
      val _ = delete_const (fst (dest_const ptabb))
    in
      MP th (CONJ th2 th0)
    end


  fun add_labels_compset compset = let
    val () = reset_code_labels_ok_db()
    val () = computeLib.add_conv (``code_labels``,2,code_labels_conv eval_real_inst_length) compset
     in () end

  fun the_bytecode_compset() = let
    val c = wordsLib.words_compset ()
    val () = compute_basicLib.add_basic_compset c
    val () = compute_semanticsLib.add_ast_compset c
    val () = add_bytecode_compset c
    val () = add_labels_compset c
  in
    c
  end


end

