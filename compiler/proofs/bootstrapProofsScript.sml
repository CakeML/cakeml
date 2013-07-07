open HolKernel boolLib bossLib lcsymtacs
open finite_mapTheory
open CompilerTheory compilerTerminationTheory toBytecodeProofsTheory compilerProofsTheory
val _ = new_theory"bootstrapProofs"

val env_rs_empty = store_thm("env_rs_empty",
  ``bs.stack = [] ∧ bs.clock = NONE ∧ rd.sm = [] ∧ rd.cls = FEMPTY ⇒
    env_rs [] [] [] init_compiler_state rd (ck,[]) bs``,
  simp[env_rs_def,init_compiler_state_def,intLangExtraTheory.good_cmap_def,FLOOKUP_UPDATE
      ,good_contab_def,IntLangTheory.tuple_cn_def,toIntLangProofsTheory.cmap_linv_def] >>
  simp[pmatchTheory.env_to_Cenv_MAP,intLangExtraTheory.all_vlabs_menv_def
      ,intLangExtraTheory.vlabs_menv_def,pred_setTheory.SUM_IMAGE_THM] >>
  strip_tac >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_DEF])

val closed_context_empty = store_thm("closed_context_empty",
  ``closed_context [] [] [] []``,
  simp[closed_context_def,toIntLangProofsTheory.closed_under_cenv_def,closed_under_menv_def])

val call_decl_thm = store_thm("call_decl_thm",
``let decs = ds++[Dlet (Pvar fun) (Fun _a _b)] in
  evaluate_decs (SOME mn) [] [] [] [] decs ([],cenv,Rval env) ∧
  FV_decs decs = {} ∧
  "" ∉ new_decs_cns decs ∧
  decs_cns mn decs = {} ∧
  (∀i tds.
    i < LENGTH decs ∧ EL i decs = Dtype tds ⇒
    check_dup_ctors (SOME mn) (decs_to_cenv (SOME mn) (TAKE i decs)) tds) ∧
  compile_decs mn decs (init_compiler_state,[]) = (rs,REVERSE code) ∧
  bs0.code = code ∧
  bs0.pc = 0 ∧
  bs0.stack = [] ∧
  bs0.clock = NONE
⇒
  ∃ptr benv st str rf h rd.
  let cl = Block closure_tag [CodePtr ptr;benv] in
  let bs1 = bs0 with <| pc := next_addr bs0.inst_length bs0.code
                      ; stack := cl::st
                      ; output := str
                      ; refs := rf
                      ; handler := h
                      |> in
  bc_eval bs0 = SOME bs1 ∧
  env_rs [] cenv env rs rd (0,[]) bs1 ∧
  ∀bs ret mid barg cenv arg v.
    bs.code = [CallPtr] ∧
    bs.pc = 0 ∧            (* it would be nice if possible to have [] instead of mid++st *)
    bs.stack = CodePtr ptr::benv::barg::cl::mid++st ∧
    bs.handler = h ∧
    bs.clock = NONE ∧
    Cenv_bs rd FEMPTY (0,[]) Cenv FEMPTY (MAP (CTDec o SND) rs.renv) rs.rsz rs.rsz bs ∧ (* not true!
      the call stuff on the stack gets in the way, and
      the rs.renv probably needs to know about "x", and
      need to connect cenv to Cenv and env to rs.renv *)
    evaluate F [] cenv (0,[]) (("x",arg)::env) (App Opapp (Var (Short fun)) (Var(Short "x"))) ((0,[]),Rval v)
                (* this should provably be the same as [("x",arg);(fun,lookup fun env)] *)
   (* use do_app instead of evaluate? *)
   (* just need something that says: lookup fun env applied to arg returns v, semantically *)
    ⇒
    ∃bv rf'.
    let bs' = bs with <| stack := bv::mid++st
                       ; pc := next_addr bs.inst_length bs.code
                       ; refs := rf'
                       |> in
    Cenv_bs rd FEMPTY (0,[]) Cenv FEMPTY (MAP (CTDec o SND) rs.renv) rs.rsz rs.rsz bs' ∧
    bc_eval bs = SOME bs' ∧
    Cv_bv (mk_pp rd bs') (v_to_Cv FEMPTY (cmap rs.contab) v) bv``,
cheat)

val _ = export_theory()
