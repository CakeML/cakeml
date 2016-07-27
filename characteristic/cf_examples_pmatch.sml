open preamble
     set_sepTheory helperLib
     ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfHeapsLib
open cfTheory cfTacticsBaseLib cfTacticsLib

val initial_prog = EVAL ``basis_program`` |> concl |> rand
val initial_st = ml_progLib.add_prog initial_prog pick_name ml_progLib.init_state

val lnull = parse_topdecl
  "fun lnull l = case l of [] => true | x::xs => false"

val st = ml_progLib.add_prog lnull pick_name initial_st

(* TODO: should move to astSyntax *)
fun mk_pat_bindings pat = ``ast$pat_bindings ^pat []``;
fun mk_v_of_pat_norest pat ls = ``v_of_pat_norest envC ^pat ^ls``

fun PMATCH_ROW_v_of_norest_n_goal n =
  let
    val pat = mk_var("pat",astSyntax.pat_ty)
    val vs = List.tabulate(n, fn n => mk_var("v"^(Int.toString n), stringSyntax.string_ty))
    val ls = listSyntax.mk_list (vs, stringSyntax.string_ty)
    val pbh = mk_eq(mk_pat_bindings pat,ls)
    val insts = mk_var("insts",listSyntax.mk_list_type semanticPrimitivesSyntax.v_ty)
    val Q = mk_var("Q",type_of insts --> alpha)
    val p1 = mk_abs(insts,mk_v_of_pat_norest pat insts)
    val g1 = mk_abs(mk_var("_",type_of insts),T)
    val r1 = mk_abs(insts,mk_comb(Q,insts))
    val inp = optionSyntax.mk_some(mk_var("lv",semanticPrimitivesSyntax.v_ty))
    val row1 = mk_comb(patternMatchesSyntax.mk_PMATCH_ROW(p1,g1,r1),inp)
    val vvs = map (fn v => mk_var(#1(dest_var v), semanticPrimitivesSyntax.v_ty)) vs
    val vls = listSyntax.mk_list (vvs, semanticPrimitivesSyntax.v_ty)
    val tup = if n = 0 then mk_var("uv",oneSyntax.one_ty) else pairSyntax.list_mk_pair vvs
    val p2 = mk_pabs(tup,mk_v_of_pat_norest pat vls)
    val g2 = mk_pabs(tup,T)
    val r2 = mk_pabs(tup,mk_comb(Q,vls))
    val row2 = mk_comb(patternMatchesSyntax.mk_PMATCH_ROW(p2,g2,r2),inp)
  in
    mk_imp(pbh,mk_eq(row1,row2))
  end

fun PMATCH_ROW_v_of_pat_norest_n_thm n =
  prove(PMATCH_ROW_v_of_norest_n_goal n,
    rw[patternMatchesTheory.PMATCH_ROW_def]
    \\ DEEP_INTRO_TAC some_intro \\ simp[]
    \\ DEEP_INTRO_TAC some_intro \\ simp[]
    \\ simp[patternMatchesTheory.PMATCH_ROW_COND_def]
    \\ rpt strip_tac
    \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
    \\ imp_res_tac v_of_pat_norest_insts_unique \\ fs[]
    >- metis_tac[]
    \\ imp_res_tac v_of_pat_norest_insts_length \\ rfs[]
    \\ fs[LENGTH_EQ_NUM_compute] \\ rw[]
    \\ fs[FORALL_PROD]
    \\ metis_tac[]);

val PMATCH_ROW_v_of_pat_norest_0 = PMATCH_ROW_v_of_pat_norest_n_thm 0
val PMATCH_ROW_v_of_pat_norest_2 = PMATCH_ROW_v_of_pat_norest_n_thm 2

local
  val cs = listLib.list_compset()
  val () = basicComputeLib.add_basic_compset cs
  val () = semanticsComputeLib.add_semantics_compset cs
  val eval = computeLib.CBV_CONV cs
in
fun compute_pat_bindings_tac (g as (asl,w)) =
  let
    fun finder tm =
      let
        val (name,pat) = markerSyntax.dest_abbrev tm
        val _ = assert(equal"pat")name
      in pat end
    val pat = tryfind finder asl
  in
    assume_tac(eval(mk_pat_bindings pat))
  end g
end

val lnull_spec = Q.prove (
  `!lv a l.
     app (p:'ffi ffi_proj) ^(fetch_v "lnull" st) [lv]
       (cond (LIST_TYPE a l lv))
       (\bv. cond (BOOL (l = []) bv))`,

  xcf "lnull" st \\
  fs [cf_mat_def] \\ irule local_elim \\ reduce_tac \\
  strip_tac THEN1 cheat (* nvm that for the moment *) \\
  fs [PMATCH_ROW_of_pat_def]
  (* - first row:
         + pat = Pcon (SOME (Short "nil") [])
         + pat_bindings pat [] = []
         therefore, insts can be replaced by ()
         (PMATCH_ROW (\insts. P insts) (\_. T) (\insts. Q insts) becomes
          PMATCH_ROW (\(uv: unit). P []) (\_. T) (\(uv: unit). Q []))
     - second row:
         + pat = Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"]
         + pat_bindings pat [] = ["xs"; "x"]
         therefore, insts can be replaced by (vx, vxs)
         (PMATCH_ROW (\insts. P insts) (\_. T) (\insts. Q insts) becomes
          PMATCH_ROW (\(vx, vxs). P [vx; vxs]) (\_. T) (\(vx, vxs). Q [vx; vxs]))
  *)
  \\ simp[patternMatchesTheory.PMATCH_def]
  \\ qpat_abbrev_tac`pat = Pcon _ []`
  \\ compute_pat_bindings_tac \\ rfs[]
  \\ simp[PMATCH_ROW_v_of_pat_norest_0]
  \\ qunabbrev_tac`pat`
  \\ qpat_abbrev_tac`pat = Pcon _ [_; _]`
  \\ compute_pat_bindings_tac \\ rfs[]
  \\ simp[PMATCH_ROW_v_of_pat_norest_2]
  \\ cheat
)
