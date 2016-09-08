open preamble
open set_sepTheory helperLib ml_translatorTheory ConseqConv
open semanticPrimitivesTheory cfHeapsTheory
open cfHeapsBaseLib cfStoreTheory
open cfTacticsBaseLib
open funBigStepTheory

val _ = new_theory "cfNormalize"

(*------------------------------------------------------------------*)
(** The [cf] function assumes that programs are in "normal form"
    (which is close to ANF). These lemmas exploit the fact that some
    program is in normal form.
*)

val exp2v_def = Define `
  exp2v _ (Lit l) = SOME (Litv l) /\
  exp2v env (Var name) = lookup_var_id name env /\
  exp2v _ _ = NONE`

val exp2v_evaluate = store_thm ("exp2v_evaluate",
  ``!e env st v. exp2v env e = SOME v ==>
    evaluate st env [e] = (st, Rval [v])``,
  Induct \\ fs [exp2v_def, terminationTheory.evaluate_def]
);

val exp2v_list_def = Define `
  exp2v_list env [] = SOME [] /\
  exp2v_list env (x :: xs) =
    (case exp2v env x of
      | NONE => NONE
      | SOME v =>
        (case exp2v_list env xs of
          | NONE => NONE
          | SOME vs => SOME (v :: vs)))`;

val exp2v_list_evaluate = store_thm ("exp2v_list_evaluate",
  ``!l lv env st. exp2v_list env l = SOME lv ==>
    evaluate st env l = (st, Rval lv)``,
  Induct
  THEN1 (fs [exp2v_list_def, terminationTheory.evaluate_def])
  THEN1 (
    rpt strip_tac \\ fs [exp2v_list_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ progress exp2v_evaluate \\
    Cases_on `l` \\ fs [terminationTheory.evaluate_def]
  )
);

val evaluate_list_rcons = store_thm ("evaluate_rcons",
  ``!env st st' st'' l x lv v.
     evaluate st env l = (st', Rval lv) /\
     evaluate st' env [x] = (st'', Rval [v]) ==>
     evaluate st env (l ++ [x]) = (st'', Rval (lv ++ [v]))``,

  Induct_on `l`
  THEN1 (
    rpt strip_tac \\ fs [terminationTheory.evaluate_def]
  )
  THEN1 (
    rpt strip_tac \\ fs [terminationTheory.evaluate_def] \\
    Cases_on `l` \\ fs []
    THEN1 (
      fs [terminationTheory.evaluate_def] \\
      last_assum (fn t =>
        progress_with t
          (CONJ_PAIR funBigStepPropsTheory.evaluate_length |> fst)) \\
      fs [LENGTH_EQ_NUM_compute]
    )
    THEN1 (
      qpat_x_assum `evaluate _ _ (_::_::_) = _`
        (assume_tac o REWRITE_RULE [terminationTheory.evaluate_def]) \\
      every_case_tac \\ fs [] \\ rw [] \\ first_assum progress \\
      simp [terminationTheory.evaluate_def]
    )
  )
);

val exp2v_list_REVERSE = store_thm ("exp2v_list_REVERSE",
  ``!l (st: 'ffi semanticPrimitives$state) lv env. exp2v_list env l = SOME lv ==>
    evaluate st env (REVERSE l) = (st, Rval (REVERSE lv))``,
  Induct \\ rpt gen_tac \\ disch_then (assume_tac o GSYM) \\
  fs [exp2v_list_def, terminationTheory.evaluate_def] \\
  every_case_tac \\ fs [] \\ rw [] \\ irule evaluate_list_rcons \\
  metis_tac [exp2v_evaluate]
);

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
);

val exp2v_list_LENGTH = store_thm ("exp2v_list_LENGTH",
  ``!l lv env. exp2v_list env l = SOME lv ==> LENGTH l = LENGTH lv``,
  Induct_on `l` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ res_tac \\ fs [] \\ rw []
);

(*------------------------------------------------------------------*)
(* [normalise] *)

val normalise_def = Define `
  normalise x = (x:exp)` (* TODO: actually implement this without going into closures *)

val evaluate_normalise = store_thm("evaluate_normalise",
  ``evaluate s env [normalise exp] = evaluate s env [exp]``,
  fs [normalise_def]);

val _ = export_theory ()
