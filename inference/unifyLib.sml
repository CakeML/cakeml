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
  ,computeLib.lazyfy_thm(bytecodeEvalTheory.bc_eval_def)
  ]

val db = ref (Net.insert (rand(concl(t_wfs_FEMPTY)),t_wfs_FEMPTY) Net.empty)
fun t_unify_conv tm = let
  val (_,[s,t1,t2]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_unify_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  val th3 = TRANS th1 th2
  val res = rhs(concl th2)
  val _ = if optionSyntax.is_some res then
          db := Net.insert (rand res,PROVE[wfs_s,t_unify_wfs,th3]``^(rator(concl wfs_s)) ^(rand res)``) (!db)
          else ()
  in th3 end
fun t_vwalk_conv tm = let
  val (_,[s,t]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPEC t (MATCH_MP unifyTheory.t_vwalk_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end
fun t_oc_conv tm = let
  val (_,[s,t1,t2]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPECL [t1,t2] (MATCH_MP unifyTheory.t_oc_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end
fun t_walkstar_conv tm = let
  val (_,[s,t]) = strip_comb tm
  val wfs_s = hd(Net.index s (!db))
  val th1 = SPEC t (MATCH_MP unifyTheory.t_walkstar_eqn wfs_s)
  val th2 = EVAL (rhs(concl th1))
  in TRANS th1 th2 end

val convs =
[(``t_unify``,3,t_unify_conv)
,(``t_vwalk``,2,t_vwalk_conv)
,(``t_walkstar``,2,t_walkstar_conv)
,(``t_oc``,3,t_oc_conv)
]

in

fun add_unify_compset compset =
  (computeLib.add_thms funs compset
  ;List.app (Lib.C computeLib.add_conv compset) convs
  )

end
end
