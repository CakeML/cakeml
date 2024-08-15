(*
  Implementation of the xcf tactic.
 *)

structure xcf :> xcf =
struct

  open preamble;
  open alistTheory cfAppTheory cfHeapsTheory cfTheory cfAppTheory cfHeapsTheory
       cfTheory cfTacticsTheory cfNormaliseTheory stringTheory xcfTheory;
  open astSyntax cfAppSyntax semanticPrimitivesSyntax stringSyntax;

  fun THENCC (l, r) = ConseqConv.THEN_CONSEQ_CONV l r;
  infix THENCC

  (*
  load "stringLib";
  load "cfHeapsBaseSyntax";
  load "cfSyntax";
  load "cfTacticsBaseLib";
  *)

  val ERR = mk_HOL_ERR "xcf" "xcf";

  (* -----------------------------------------------------------------------
     Terms
   * ----------------------------------------------------------------------- *)

  val naryClosure_tm =
    prim_mk_const {Name = "naryClosure", Thy = "cf"};
  val naryRecclosure_tm =
    prim_mk_const {Name = "naryRecclosure", Thy = "cf"};
  val find_recfun_tm =
    prim_mk_const {Name = "find_recfun", Thy = "semanticPrimitives"};
  val letrec_pull_params_tm =
    prim_mk_const {Name = "letrec_pull_params", Thy = "cf"};
  val local_tm =
    prim_mk_const {Name = "local", Thy = "cfHeaps"};
  val STOP_tm =
    prim_mk_const {Name = "STOP", Thy = "xcf"};

  (* -----------------------------------------------------------------------
     General destructors
   * ----------------------------------------------------------------------- *)

  local
    fun list_dest acc tm =
      let
        val (fx, x) = dest_comb tm
      in
        list_dest (x::acc) fx
      end
      handle HOL_ERR _ => tm::acc;
  in
    val list_dest_comb = list_dest [];
  end (* local *)

  local
    fun list_dest acc tm =
      let
        val (v, b) = dest_forall tm
      in
        list_dest (v::acc) b
      end
      handle HOL_ERR _ => List.rev acc;
  in
    val list_dest_forall = list_dest [];
  end (* local *)

  (* -----------------------------------------------------------------------
     Destructors
   * ----------------------------------------------------------------------- *)

  (*
  val tm = ``naryClosure env vs bod``;
  *)
  fun dest_naryClosure tm =
    case list_dest_comb tm of
      [f, env, vs, bod] =>
        if same_const f naryClosure_tm then (env, vs, bod)
        else fail ()
    | _ => fail ()
  val is_naryClosure = can dest_naryClosure;

  (*
  val tm = ``naryRecclosure env naryfuns f``;
  *)
  fun dest_naryRecclosure tm =
    case list_dest_comb tm of
      [f, env, naryfuns, g] =>
        if same_const f naryRecclosure_tm then (env, naryfuns, g)
        else fail ()
    | _ => fail ()
  val is_naryRecclosure = can dest_naryRecclosure;

  (* -----------------------------------------------------------------------
     xcf_cleanup_conv
   * ----------------------------------------------------------------------- *)

  (*
   * Reduce ``cf p ...`` terms; for example, ``cf p (Var v)`` becomes
   * ``cf_var v``.
   *)

  val cf_cleanup_conv =
    ONCE_REWRITE_CONV [cf_STOP_thm] THENC
    computeLib.compset_conv (listLib.list_compset ()) [
      computeLib.Defs [
        is_bound_Fun_def,
        Fun_body_def,
        dest_opapp_def,
        cf_STOP_rewrite
      ],
      computeLib.Tys [
        optionSyntax.mk_option alpha,
        exp_ty, op_ty, v_ty, pat_ty, word_size_ty],
      computeLib.Extenders [
        pairLib.add_pair_compset,
        (fn cs => computeLib.set_skip cs STOP_tm (SOME 1))
      ]
    ] THENC
    ONCE_REWRITE_CONV [STOP_def] THENC
    PATH_CONV "lll" (REWRITE_CONV [ETA_THM]);

  (* -----------------------------------------------------------------------
     xcf
   * ----------------------------------------------------------------------- *)

  (*
  val tm = ``[1;2;] <> []``;
  val tm = ``LENGTH [1;2;3] = LENGTH [a;b;c]``;
  LIST_EVAL_CONV tm;
  *)
  val LIST_EVAL_CONV =
    EQT_ELIM o computeLib.compset_conv (listLib.list_compset ()) [];

  (*
  val tm = ``app p (naryClosure env [n1;n2;] bod) [a1;a2] H Q``;
  *)
  fun nary_clos_app_cconv tm =
    let
      val (p, nc, xs, h, q) = dest_app tm
      val (env, ns, bod) = dest_naryClosure nc
      val th = SPECL [ns, env, bod, xs, h, q] app_of_cf
      val th = MP_CONV LIST_EVAL_CONV th
      val th = MP_CONV LIST_EVAL_CONV th
    in
      th
    end;

  (*
  val tm = ``Fun v1 (Fun v2 (Fun v3 b))``
  *)
  local
    val naryFun_tm = prim_mk_const {Name = "naryFun", Thy = "cf"};
    fun mk_naryFun ns bod = list_mk_comb (naryFun_tm, [ns, bod]);
    fun build acc tm =
      case total dest_Fun tm of
        NONE => mk_naryFun (listSyntax.mk_list (List.rev acc, string_ty)) tm
      | SOME (n, e) => build (n::acc) e;
    val cnv =
      computeLib.compset_conv (listLib.list_compset()) [
        computeLib.Defs [naryFun_def]
        ];
  in
    fun nary_fun_conv tm = EQT_ELIM (cnv (mk_eq (tm, build [] tm)))
  end (* local *)

  (*
  val tm = ``Closure env v (Fun v1 (Fun v2 (Fun v3 b)))``
  *)
  val nary_clos_conv =
    RAND_CONV nary_fun_conv THENC
    REWR_CONV (GSYM naryClosure_def);

  (*
  val tm = ``app (p: 'ffi ffi_proj) (Closure env v (Fun v1 (Fun v2 (Fun v3 b)))) [a;a1;a2;a3] H Q``;
  *)
  fun xcf_closure_conv defth =
    PATH_CONV "lllr" (REWR_CONV defth) THENCC
    PATH_CONV "lllr" nary_clos_conv THENCC
    nary_clos_app_cconv;

  (*
  val tm = ``find_recfun "f1" (letrec_pull_params [("f1","v1",Fun "v2" (Var v)); ("f2","v2",e2)])``;
  find_recfun_conv tm
  *)
  val find_recfun_conv =
    computeLib.compset_conv (listLib.list_compset ()) [
      computeLib.Defs [
        ALOOKUP_def, Fun_body_def, Fun_params_def, letrec_pull_params_def,
        semanticPrimitivesPropsTheory.find_recfun_ALOOKUP
      ],
      computeLib.Tys [
        optionSyntax.mk_option alpha
      ],
      computeLib.Extenders [
        stringLib.add_string_compset
      ]
    ];

  (*
  val tm = ``ALL_DISTINCT ["f",a,b; "g",c,d; "o",e,r]``;
  LIST_EVAL_CONV2 tm
  *)
  val LIST_EVAL_CONV2 =
    computeLib.compset_conv (reduceLib.num_compset ()) [
      computeLib.Defs [
        listTheory.ALL_DISTINCT, listTheory.MEM, listTheory.MAP
      ],
      computeLib.Tys [
        listSyntax.mk_list_type alpha
      ],
      computeLib.Extenders [
        stringLib.add_string_compset,
        pairLib.add_pair_compset
      ]
    ];

  (*
  val tm = ``app p (naryRecclosure env (letrec_pull_params [("f1","v1",Fun "v2" (Var v)); ("f2","v2",e2)]) "f1") [v1;v2] H Q``
  *)
  fun nary_recclos_app_cconv tm =
    let
      val (p, nc, xs, h, q) = cfAppSyntax.dest_app tm
      val (env, lpp_funs, f) = dest_naryRecclosure nc
      val funs = rand lpp_funs
      (* Compute find_recfun f (letrec_pull_params funs) *)
      val fth = find_recfun_conv (boolSyntax.list_mk_icomb (find_recfun_tm, [f, lpp_funs]))
      val (vs, bod) = (concl fth |> rhs |> optionSyntax.dest_some
                       |> pairSyntax.dest_pair)
                      handle HOL_ERR _ => raise ERR "frf lpp lookup failed"
      (* Instantiate theorem: *)
      val th = SPECL [f, vs, bod, funs, xs, env, h, q] app_rec_of_cf
      val th = MP_CONV LIST_EVAL_CONV th
      val th = MP_CONV LIST_EVAL_CONV th
      val th = MP_CONV LIST_EVAL_CONV2 th
      val th = MP th fth
      val th = CONV_RULE (PATH_CONV "lrllrllll" LIST_EVAL_CONV2) th
    in
      th
    end;

  (*
  val tm = ``app (p: 'ffi ffi_proj) (Recclosure env [("f1","v1",Fun "v2" (Var v)); ("f2","v2",e2)] "f1") [v1;v2] H Q``
  *)
  local
    val cnv1 = REWR_CONV (GSYM letrec_pull_params_repack)
    fun cnv2 defs =
      SIMP_CONV list_ss (letrec_pull_params_repack::List.map GSYM defs)
  in
    fun xcf_recclosure_conv defs tm =
      let
        (* Rewrite using the definition, and put the term into shape for
         * nary_recclos_app_cconv: *)
        val th1 =
          (EVERY_CONV (List.map (fn th =>
                                   TRY_CONV (PATH_CONV "lllr" (REWR_CONV th)))
                                defs) THENC
           PATH_CONV "lllr" cnv1) tm
        val th2 = nary_recclos_app_cconv (rhs (concl th1))
        (* Simplify the environment argument of the cf term: *)
        val th3 = CONV_RULE (PATH_CONV "lrllr" (cnv2 defs)) th2
      in
        (* Restore the original app-goal so that we can irule the theorem: *)
        CONV_RULE (RAND_CONV (REWR_CONV (SYM th1))) th3
      end
  end (* local *)

  (*
   * Top-level conversion for xcf.
   *)
  fun xcf_cconv defth tm =
    let
      val (ptm, defn, args, _, _) =
        cfAppSyntax.dest_app tm handle HOL_ERR _ =>
        raise ERR "Not an app"
      val _ =
        type_of ptm = cfHeapsBaseSyntax.ffi_proj_format orelse
        raise ERR (term_to_string ptm ^ " must have type :'ffi ffi_proj")
      val _ =
        same_const (lhs (concl defth)) defn orelse
        raise ERR ("theorem does not define " ^ term_to_string defn)
      val vtm = rhs (concl defth)
    in
      if semanticPrimitivesSyntax.is_Recclosure vtm then
        xcf_recclosure_conv [defth] tm
      else (* Closure *)
        xcf_closure_conv defth tm
    end;

  (*
   * Top-level conversion for xcfs.
   *)
  fun xcfs_cconv defs tm =
    let
      val (ptm, defn, args, _, _) =
        cfAppSyntax.dest_app tm handle HOL_ERR _ =>
        raise ERR "Not an app"
      val _ =
        type_of ptm = cfHeapsBaseSyntax.ffi_proj_format orelse
        raise ERR (term_to_string ptm ^ " must have type :'ffi ffi_proj")
      val _ =
        List.exists (fn th => same_const (lhs (concl th)) defn) defs orelse
        raise ERR ("none of the theorems define " ^ term_to_string defn)
    in
      xcf_recclosure_conv defs tm
    end;

  fun xcf_with_def defth (g as (_, tm)) =
    (irule (xcf_cconv defth tm) THEN
     CONV_TAC cf_cleanup_conv) g;

  fun xcf_with_defs defs (g as (_, tm)) =
    (irule (xcfs_cconv defs tm) THEN
     CONV_TAC cf_cleanup_conv) g;

  fun xcf name st =
    xcf_with_def (cfTacticsBaseLib.fetch_def name st);

  fun xcfs names st =
    xcf_with_defs (List.map (fn n => cfTacticsBaseLib.fetch_def n st) names);

end (* struct *)

