open preamble compilerTheory compilerTerminationTheory

val _ = new_theory "repl_compute";

val compile_dec1_def = Define`
  compile_dec1 mn menv (ct,m,env,rsz,cs) dec =
    let (vso,cs) = compile_dec menv m env rsz cs dec in
    let ct = dec_to_contab mn ct dec in
    let vs = case vso of NONE => [] | SOME vs => vs in
    let n = LENGTH vs in
    let m = m with <|cnmap := cmap ct; bvars := vs ++ m.bvars|> in
    let env = GENLIST (λi. CTDec (rsz+n-1-i)) n ++ env in
    let rsz = rsz + n in
    let cs = compile_news cs 0 vs in
    (ct,m,env,rsz,cs)`

val compile_decs_FOLDL = store_thm(
  "compile_decs_FOLDL",
  ``∀mn menv ct m env rsz cs decs.
      compile_decs mn menv ct m env rsz cs decs =
      let (ct,m,env,rsz,cs) = FOLDL (compile_dec1 mn menv) (ct,m,env,rsz,cs) decs in
      (ct,m,rsz,cs)``,
  Induct_on `decs` >- rw[compile_decs_def] >>
  fs[LET_THM] >>
  simp[compile_dec1_def] >>
  simp[compile_decs_def] >>
  simp[UNCURRY]);

val _ = export_theory()
