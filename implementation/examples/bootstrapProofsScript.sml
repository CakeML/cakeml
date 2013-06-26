open HolKernel boolLib bossLib
val _ = new_theory"bootstrapProofs"

(*
let code = unStopCons (compile_decs init_compiler_state (decls++[Dlet (Pvar fname) (Fun ...)]) stop_NIL) in
  bs0.code = code ∧
  bs0.pc = 0 ∧
  bs0.stack = [] ∧
  bs0.clock = NONE
⇒
  ∃ptr env st str rf h.
  let cl = Block closure_tag [CodePtr ptr;env] in
  let bs1 = bs0 with <| pc := next_addr bs0.inst_length bs0.code
                      ; stack := cl::st (* or wherever fname is *)
                      ; output := str
                      ; refs := rf
                      ; handler := h
                      |> in
  bc_eval bs0 = SOME bs1 ∧
  refs_ok ?? rf ∧
  ∀bs ret mid arg cenv env v.
    bs.code = [CallPtr] ∧
    bs.pc = 0 ∧
    bs.stack = CodePtr ptr::env::arg::cl::mid++st ∧
    bs.handler = h ∧
    refs_ok ?? bs.refs ∧
    Cv_bv (v_to_Cv ??? (lookup "x" in env)) arg ∧ (* should be for everything in env, not just x *)
    evaluate [] cenv [] env (App Opapp (Var (Short fname)) (Var(Short "x"))) ([],Rval v)
    ⇒
    ∃bv rf'.
    let bs' = bs with <| stack := bv::mid++st
                       ; pc := next_addr bs.inst_length bs.code
                       ; refs := rf'
                       |> in
    refs_ok ?? rf' ∧
    bc_eval bs = SOME bs' ∧
    Cv_bv (v_to_Cv ??? v) bv
*)

val _ = export_theory()
