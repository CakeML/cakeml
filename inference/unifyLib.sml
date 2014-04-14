structure unifyLib = struct
local
  open HolKernel boolLib bossLib lcsymtacs

  val t_unify_wfs = prove(
   ``t_wfs s ∧ (t_unify s t1 t2 = SOME sx) ==> t_wfs sx``,
   metis_tac[unifyTheory.t_unify_unifier])

  val t_wfs_FEMPTY = prove(
    ``t_wfs FEMPTY``,
    rw[unifyTheory.t_wfs_def])

  val funs =
    [unifyTheory.t_walk_eqn
    ,unifyTheory.t_ext_s_check_eqn
    ]

  val init_db = Net.insert (rand(concl(t_wfs_FEMPTY)),t_wfs_FEMPTY) Net.empty
  val db = ref init_db
  fun get_wfs s =
    case Net.index s (!db) of
      (th::_) => th
    | _ => raise mk_HOL_ERR "unifyLib" "get_wfs" (term_to_string s)

in

  fun reset_wfs_thms() = db := init_db
  fun wfs_thms() = Net.listItems(!db)

  fun t_unify_conv eval tm = let
    val (_,[s,t1,t2]) = strip_comb tm
    val wfs_s = get_wfs s
    val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_unify_eqn wfs_s)
    val th2 = eval (rhs(concl th1))
    val th3 = TRANS th1 th2
    val res = rhs(concl th2)
    val _ = if optionSyntax.is_some res then
            let val key = rand res in
              if null (Net.index key (!db)) then
                db := Net.insert
                  (key, PROVE[wfs_s,t_unify_wfs,th3]
                        (mk_comb(rator(concl wfs_s),key)))
                  (!db)
              else ()
            end
            else ()
    in th3 end
  fun t_vwalk_conv eval tm = let
    val (_,[s,t]) = strip_comb tm
    val wfs_s = get_wfs s
    val th1 = SPEC t (MATCH_MP unifyTheory.t_vwalk_eqn wfs_s)
    val th2 = eval (rhs(concl th1))
    in TRANS th1 th2 end
  fun t_oc_conv eval tm = let
    val (_,[s,t1,t2]) = strip_comb tm
    val wfs_s = get_wfs s
    val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_oc_eqn wfs_s)
    val th2 = eval (rhs(concl th1))
    in TRANS th1 th2 end
  fun t_walkstar_conv eval tm = let
    val (_,[s,t]) = strip_comb tm
    val wfs_s = get_wfs s
    val th1 = SPEC t (MATCH_MP unifyTheory.t_walkstar_eqn wfs_s)
    val th2 = eval (rhs(concl th1))
    in TRANS th1 th2 end

  local
    fun convs eval =
    [(``t_unify``,3,t_unify_conv eval)
    ,(``t_vwalk``,2,t_vwalk_conv eval)
    ,(``t_walkstar``,2,t_walkstar_conv eval)
    ,(``t_oc``,3,t_oc_conv eval)
    ]
  in
    fun add_unify_compset compset =
      (computeLib.add_thms funs compset
      ;List.app (Lib.C computeLib.add_conv compset) (convs (computeLib.CBV_CONV compset))
      )
  end

end
end
