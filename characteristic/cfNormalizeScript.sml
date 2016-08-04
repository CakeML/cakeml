open preamble
open set_sepTheory helperLib ml_translatorTheory ConseqConv
open semanticPrimitivesTheory cfHeapsTheory
open cfHeapsBaseLib cfStoreTheory

val _ = new_theory "cfNormalize"

fun rpt_drule_then thm_tac thm =
  drule thm \\ rpt (disch_then drule) \\ disch_then thm_tac

fun progress thm = rpt_drule_then strip_assume_tac thm

(*------------------------------------------------------------------*)
(** The [cf] function assumes that programs are in "normal form"
    (which is close to ANF). We currently do not have a normalization
    function, only lemmas that exploit the fact that some program is
    in normal form.
*)

val exp2v_def = Define `
  exp2v _ (Lit l) = SOME (Litv l) /\
  exp2v env (Var name) = lookup_var_id name env /\
  exp2v _ _ = NONE`

val exp2v_evaluate = store_thm ("exp2v_evaluate",
  ``!e env st v. exp2v env e = SOME v ==>
    evaluate F env st e (st, Rval v)``,
  Induct \\ fs [exp2v_def] \\ prove_tac [bigStepTheory.evaluate_rules]
)

val exp2v_list_def = Define `
  exp2v_list env [] = SOME [] /\
  exp2v_list env (x :: xs) =
    (case exp2v env x of
      | NONE => NONE
      | SOME v =>
        (case exp2v_list env xs of
          | NONE => NONE
          | SOME vs => SOME (v :: vs)))`

val exp2v_list_evaluate = store_thm ("exp2v_list_evaluate",
  ``!l lv env st. exp2v_list env l = SOME lv ==>
    evaluate_list F env st l (st, Rval lv)``,
  Induct
  THEN1 (fs [exp2v_list_def] \\ prove_tac [bigStepTheory.evaluate_rules])
  THEN1 (
    rpt strip_tac \\ fs [exp2v_list_def] \\
    Cases_on `exp2v env h` \\ fs [] \\
    Cases_on `exp2v_list env l` \\ fs [] \\
    qpat_assum `_::_ = _` (assume_tac o GSYM) \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    qexists_tac `st` \\ fs [exp2v_evaluate]
  )
)

val evaluate_list_rcons = store_thm ("evaluate_list_rcons",
  ``!env st st' st'' l x lv v.
     evaluate_list F env st l (st', Rval lv) /\
     evaluate F env st' x (st'', Rval v) ==>
     evaluate_list F env st (l ++ [x]) (st'', Rval (lv ++ [v]))``,

  Induct_on `l`
  THEN1 (
    rpt strip_tac \\ fs [] \\
    qpat_assum `evaluate_list _ _ _ _ _` mp_tac \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    rpt strip_tac \\ qexists_tac `st''` \\ fs [] \\
    prove_tac [bigStepTheory.evaluate_rules]
  )
  THEN1 (
    rpt strip_tac \\ fs [] \\
    qpat_assum `evaluate_list _ _ _ _ _` mp_tac \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    rpt strip_tac \\
    Q.LIST_EXISTS_TAC [`v'`, `vs ++ [v]`] \\ fs [] \\
    asm_exists_tac \\ fs [] \\
    metis_tac []
  )
)

val exp2v_list_REVERSE = store_thm ("exp2v_list_REVERSE",
  ``!l (st: 'ffi state) lv env. exp2v_list env l = SOME lv ==>
    evaluate_list F env st (REVERSE l) (st, Rval (REVERSE lv))``,
  Induct \\ rpt gen_tac \\ disch_then (assume_tac o GSYM) \\
  fs [exp2v_list_def]
  THEN1 (prove_tac [bigStepTheory.evaluate_rules])
  THEN1 (
    Cases_on `exp2v env h` \\ Cases_on `exp2v_list env l` \\ fs [] \\
    first_assum progress \\ irule evaluate_list_rcons \\
    metis_tac [exp2v_evaluate]
  )
)

val exp2v_list_rcons = store_thm ("exp2v_list_rcons",
  ``!xs x l env.
     exp2v_list env (xs ++ [x]) = SOME l ==>
     ?xvs xv.
       l = xvs ++ [xv] /\
       exp2v_list env xs = SOME xvs /\
       exp2v env x = SOME xv``,
  Induct_on `xs` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ fs [] \\
  first_assum progress \\ fs [] \\ rw []
)

val exp2v_list_LENGTH = store_thm ("exp2v_list_LENGTH",
  ``!l lv env. exp2v_list env l = SOME lv ==> LENGTH l = LENGTH lv``,
  Induct_on `l` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ res_tac \\ fs [] \\ rw []
)

val _ = export_theory ()
