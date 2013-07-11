open HolKernel bossLib boolLib lcsymtacs ml_translatorLib ml_translatorTheory
open toIntLangProofsTheory compilerProofsTheory bootstrapProofsTheory ml_repl_stepTheory compile_repl_stepTheory sideTheory
val _ = new_theory"bootstrap"

val _ = Globals.max_print_depth := 25

val _ = translation_extends"ml_repl_step"

val (Eval_peic,peic_side_def) = get_cert"parse_elaborate_infertype_compile"

val FOLDL_compile_decs = SIMP_RULE(srw_ss())[LET_THM,UNCURRY]compile_decs_FOLDL 
SIMP_RULE 

val ml_repl_step_DeclAssumC =
DeclAssumC_def
|> Q.SPECL[`ml_repl_step_decls`,`envC`,`envE`]
|> EQ_IMP_RULE
|> fst
|> UNDISCH

EXISTS

|> SIMP_RULE bool_ss [GSYM LEFT_FORALL_IMP_THM]
|> Q.SPEC`[]`

``FV_decs ml_repl_step_decls = {}``

env_rs_empty

val ml_repl_step_compiler_correctness1 =
compile_decs_thm
|> CONV_RULE (RESORT_FORALL_CONV(List.rev))
|> Q.SPEC`(s2,envC,Rval envE)`
|> SIMP_RULE (srw_ss()) []
|> SIMP_RULE (srw_ss()) [compile_decs_FOLDL]
|> CONV_RULE (RESORT_FORALL_CONV(List.rev))
|> Q.SPECL[`NONE`,`[]`,`[]`,`empty_store`,`[]`,`ml_repl_step_decls`]
|> SIMP_RULE (srw_ss()) [GSYM DeclsC_def]
|> UNDISCH
|> SIMP_RULE (srw_ss()) [closed_context_def,empty_store_def,closed_under_cenv_def,closed_under_menv_def]


val (ck,t) = dest_exists(concl ml_repl_step_compiler_correctness1)
val ml_repl_step_compiler_correctness =
ASSUME t
|> Q.SPECL[`<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap init_compiler_state.contab|>`,`<|out:=[];next_label:=4|>`]
|> SIMP_RULE(srw_ss())[]
|> CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))
|> Q.SPECL[`init_compiler_state`]
|> SIMP_RULE(srw_ss())[CompilerTheory.init_compiler_state_def]

SIMP_CONV(srw_ss())[CompilerTheory.init_compiler_state_def](lhs(concl(compiled)))
env_rs_empty
|> CHOOSE (``s2:store``,ml_repl_step_DeclAssumC) 

hyp ml_repl_step_compiler_correctness
ml_repl_step_DeclAssumC
hyp ml_repl_step_DeclAssumC
|> CHOOSE (

AND_IMP_INTRO
LEFT_FORALL_IMP_THM
RIGHT_FORALL_IMP_THM
LEFT_EXISTS_IMP_THM
RIGHT_EXISTS_IMP_THM

FORALL_AND_THM
SKOLEM_THM

|> UNDISCH

hyp it

help"CHOOSE"

CHOOSE (v,|- ?x. s) (s[v/x]|-t) = |- t
EXISTS (?x. p, u)   |- p[u/x]   = |- ?x. p

|> MP ml_repl_step_DeclAssumC

print_find"DeclsC"

|> UNDISCH

CHOOSE
DeclAssum_def
DeclAssumC_def
DeclsC_def
Eval_def

type_of ``evaluate_decs``

compiled
val FOLDL_compile_decs_thm = SIMP_RULE(srw_ss())

Eval_peic
Eval_IMP_EvalC
DeclAssumC_thm
print_find"DeclAssumC"

val compiled_decs = CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM compile_decs_FOLDL])) compiled


val Eval_peic1 = SIMP_RULE(srw_ss())[Eval_def] Eval_peic
compile_
hyp Eval_peic
Eval_def
print_apropos``EqualityType EXP_TYPE``

EVAL(rhs(concl(repl_step_side_def)))
val repl_step_side_def = SIMP_RULE(srw_ss())[FORALL_PROD](repl_step_side_def')
parse_elaborate_infertype_compile_side_def

val th = update_precondition ml_repl_stepTheory.repl_step_side_def
hyp Eval_repl_step
EqualityType_def

type_of ``parse_elaborate_infertype_compile``
print_find"repl_step_side"
type_of ``repl_step``
hyp th1
DeclAssum_def
Decls_def
Eval_def

val bootstrap_result_def = Define`
  bootstrap_result = ^(rhs(concl(compiled)))`

compile_decs_FOLDL
val bootstrap_rs_def = Define`
  bootstrap_rs =
    let (ct,m,env,rsz,cs) = bootstrap_result in
    <|contab := ct
     ;renv := ZIP(m.bvars,GENLIST I rsz)
     ;rmenv := FEMPTY
     ;rsz := rsz
     ;rnext_label := cs.next_label
     |>`


val 

compiled
compile_decs_FOLDL
bootstrap_result
compile_decs_thm

EVAL ``LAST ^(rhs(concl(ml_repl_step_decls)))``
val bootstrap_envC_def = Define`
  bootstrap_envC = 3`
  print_find"DeclAssum"

val env_rs_bootstrap = store_thm("env_rs_bootstrap",
  ``env_rs [] bootstrap_envC bootstrap_envE bootstrap_rs 

``DeclAssum ml_repl_step_decls env ⇒
  

val _ = export_theory()
