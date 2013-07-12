open HolKernel bossLib boolLib lcsymtacs
(*
open ml_translatorLib ml_translatorTheory
open toIntLangProofsTheory compilerProofsTheory bootstrapProofsTheory ml_repl_stepTheory compile_repl_stepTheory sideTheory
*)
val _ = new_theory"bootstrap"

(*
val _ = Globals.max_print_depth := 25

val _ = translation_extends"ml_repl_step"

val (Eval_peic,peic_side_def) = get_cert"parse_elaborate_infertype_compile"

val ml_repl_step_DeclAssumC =
DeclAssumC_def
|> Q.SPECL[`ml_repl_step_decls`,`envC`,`envE`]
|> EQ_IMP_RULE
|> fst
|> UNDISCH

val FV_decs_ml_repl_step_decls = prove(``FV_decs ml_repl_step_decls = {}``,cheat)
val decs_cns_ml_repl_step_decls = prove(``decs_cns NONE ml_repl_step_decls = {}``,cheat)
val check_dup_ctors_ml_repl_step_decs = prove(
``(∀i tds. i < LENGTH ml_repl_step_decls ∧ EL i ml_repl_step_decls = Dtype tds ⇒
     check_dup_ctors NONE (decs_to_cenv NONE (TAKE i ml_repl_step_decls)) tds)``,cheat)

val bootstrap_result_def = Define`
  bootstrap_result = ^(rhs(concl(compiled)))`

val bootstrap_ct = Define`
  bootstrap_ct = FST(bootstrap_result)`

val bootstrap_cs = Define`
  bootstrap_cs = (SND(SND(SND(SND(bootstrap_result)))))`

val bootstrap_m = Define`
  bootstrap_m = (FST(SND(bootstrap_result)))`

val bootstrap_env = Define`
  bootstrap_env = (FST(SND(SND(bootstrap_result))))`

val bootstrap_rsz = Define`
  bootstrap_rsz = (FST(SND(SND(SND(bootstrap_result)))))`

val compiled1 = ONCE_REWRITE_RULE[GSYM bootstrap_result_def]compiled

val bootstrap_result_split = prove(
  ``bootstrap_result = (bootstrap_ct,bootstrap_m,bootstrap_env,bootstrap_rsz,bootstrap_cs)``,
  rw[bootstrap_ct,bootstrap_cs,bootstrap_m,bootstrap_env,bootstrap_rsz])

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
|> SIMP_RULE (srw_ss()) [closed_context_def,empty_store_def,closed_under_cenv_def,closed_under_menv_def
                        ,decs_cns_ml_repl_step_decls,FV_decs_ml_repl_step_decls,check_dup_ctors_ml_repl_step_decs]

val (ck,t) = dest_exists(concl ml_repl_step_compiler_correctness1)
val ml_repl_step_compiler_correctness2 =
ASSUME t
|> Q.SPECL[`<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap init_compiler_state.contab|>`,`<|out:=[];next_label:=4|>`]
|> SIMP_RULE(srw_ss())[]
|> CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))
|> Q.SPECL[`init_compiler_state`,`0`,`<|sm:=[];cls:=FEMPTY|>`
          ,`bs with <|clock := SOME ck; pc := 0; stack := []; code := bootstrap_cs.out|>`,`[]`]
|> SIMP_RULE(srw_ss())[CompilerTheory.init_compiler_state_def,good_labels_def]
|> SIMP_RULE(srw_ss())[(SIMP_RULE(srw_ss())[CompilerTheory.init_compiler_state_def]env_rs_empty)]
|> ONCE_REWRITE_RULE[CONV_RULE(LAND_CONV(SIMP_CONV(srw_ss())[CompilerTheory.init_compiler_state_def]))compiled1]
|> SIMP_RULE(srw_ss())[bootstrap_result_split]
|> ONCE_REWRITE_RULE[LET_THM]
|> PairRules.PBETA_RULE
|> SIMP_RULE pure_ss [PAIR_EQ]

pairTheory.

val ml_repl_step_compiler_correctness3 =
ml_repl_step_compiler_correctness2
|> SIMP_[LET_THM]
compiled
LET_SS

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
  
*)
val _ = export_theory()
