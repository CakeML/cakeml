open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory ConseqConv
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormalizeTheory cfAppTheory
open patternMatchesTheory

val _ = new_theory "cf"

(* TODO: clean & generalize *)
fun instantiate g =
  rpt ((asm_exists_tac \\ fs []) ORELSE
       (once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs []))
      g

fun progress_then thm_tac thm =
  drule thm \\ rpt (disch_then drule) \\ disch_then thm_tac

fun progress thm = progress_then strip_assume_tac thm

fun progress_with_then thm_tac thm' thm =
  mp_tac (MATCH_MP thm thm') \\ rpt (disch_then drule) \\ disch_then thm_tac

fun progress_with thm' thm = progress_with_then strip_assume_tac thm' thm

(* imperfect as it changes the position of the matched assumption in the
   assumption stack *)
fun qpat_assum_keep q thm_tac =
  qpat_assum q (fn asm => thm_tac asm \\ assume_tac asm)

fun sing x = [x]

fun try_finally tac = TRY (tac \\ NO_TAC)

(*------------------------------------------------------------------*)
(* Machinery for dealing with n-ary applications/functions in cf.

   Applications and ((mutually)recursive)functions are unary in
   CakeML's AST.
   Some machinery is therefore needed to walk down the AST and extract
   multiple arguments (for an application), or multiple parameters and
   the final function body (for functions).
*)

(** 1) n-ary applications *)

(* [dest_opapp]: destruct an n-ary application. *)
val dest_opapp_def = Define `
  dest_opapp (App Opapp l) =
       (case l of
          | [f; x] =>
            (case dest_opapp f of
               | SOME (f', args) => SOME (f', args ++ [x])
               | NONE => SOME (f, [x]))
          | _ => NONE) /\
  dest_opapp _ = NONE`

val dest_opapp_not_empty_arglist = Q.prove (
  `!e f args. dest_opapp e = SOME (f, args) ==> args <> []`,
  Cases \\ fs [dest_opapp_def] \\ rename1 `App op _` \\
  Cases_on `op` \\ fs [dest_opapp_def] \\ every_case_tac \\
  fs []
)

(** 2) n-ary single non-recursive functions *)

(* An auxiliary definition *)
val is_bound_Fun_def = Define `
  is_bound_Fun (SOME _) (Fun _ _) = T /\
  is_bound_Fun _ _ = F`

(* [Fun_body]: walk down successive lambdas and return the inner
   function body *)
val Fun_body_def = Define `
  Fun_body (Fun _ body) =
    (case Fun_body body of
       | NONE => SOME body
       | SOME body' => SOME body') /\
  Fun_body _ = NONE`

val Fun_body_exp_size = Q.prove (
  `!e e'. Fun_body e = SOME e' ==> exp_size e' < exp_size e`,
  Induct \\ fs [Fun_body_def] \\ every_case_tac \\
  fs [astTheory.exp_size_def]
)

val is_bound_Fun_unfold = Q.prove (
  `!opt e. is_bound_Fun opt e ==> (?n body. e = Fun n body)`,
  Cases_on `e` \\ fs [is_bound_Fun_def]
)

(* [Fun_params]: walk down successive lambdas and return the list of
   parameters *)
val Fun_params_def = Define `
  Fun_params (Fun n body) =
    n :: (Fun_params body) /\
  Fun_params _ =
    []`

val Fun_params_Fun_body_NONE = Q.prove (
  `!e. Fun_body e = NONE ==> Fun_params e = []`,
  Cases \\ fs [Fun_body_def, Fun_params_def] \\ every_case_tac
)

(* [naryFun]: build the AST for a n-ary function *)
val naryFun_def = Define `
  naryFun [] body = body /\
  naryFun (n::ns) body = Fun n (naryFun ns body)`

val Fun_params_Fun_body_repack = Q.prove (
  `!e e'.
     Fun_body e = SOME e' ==>
     naryFun (Fun_params e) e' = e`,
  Induct \\ fs [Fun_body_def, Fun_params_def] \\ every_case_tac \\
  rpt strip_tac \\ fs [Once naryFun_def] \\ TRY every_case_tac \\
  TRY (fs [Fun_params_Fun_body_NONE, Once naryFun_def] \\ NO_TAC) \\
  once_rewrite_tac [naryFun_def] \\ fs []
)

(** 3) n-ary (mutually)recursive functions *)

(** Mutually recursive definitions (and closures) use a list of tuples
    (function name, parameter name, body). [letrec_pull_params] returns the
    "n-ary" version of this list, that is, a list of tuples:
    (function name, parameters names, inner body)
*)
val letrec_pull_params_def = Define `
  letrec_pull_params [] = [] /\
  letrec_pull_params ((f, n, body)::funs) =
    (case Fun_body body of
       | NONE => (f, [n], body)
       | SOME body' => (f, n::Fun_params body, body')) ::
    (letrec_pull_params funs)`

val letrec_pull_params_names = store_thm ("letrec_pull_params_names",
  ``!funs P.
     MAP (\ (f,_,_). P f) (letrec_pull_params funs) =
     MAP (\ (f,_,_). P f) funs``,
  Induct \\ fs [letrec_pull_params_def] \\ rpt strip_tac \\
  rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs []
)

val letrec_pull_params_LENGTH = store_thm ("letrec_pull_params_LENGTH",
  ``!funs. LENGTH (letrec_pull_params funs) = LENGTH funs``,
  Induct \\ fs [letrec_pull_params_def] \\ rpt strip_tac \\
  rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs []
)

val letrec_pull_params_append = store_thm ("letrec_pull_params_append",
  ``!l l'.
     letrec_pull_params (l ++ l') =
     letrec_pull_params l ++ letrec_pull_params l'``,
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def] \\
  rename1 `ftuple::_` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_def]
)

val letrec_pull_params_cancel = store_thm ("letrec_pull_params_cancel",
  ``!funs.
     MAP (\ (f,ns,body). (f, HD ns, naryFun (TL ns) body))
         (letrec_pull_params funs) =
     funs``,
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def] \\
  rename1 `ftuple::_` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  fs [Fun_params_Fun_body_repack]
)

val letrec_pull_params_nonnil_params = store_thm ("letrec_pull_params_nonnil_params",
  ``!funs f ns body.
     MEM (f,ns,body) (letrec_pull_params funs) ==>
     ns <> []``,
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def, MEM] \\
  rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  rename1 `(f',n',body')::funs` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  metis_tac []
)

val find_recfun_letrec_pull_params = store_thm ("find_recfun_letrec_pull_params",
  ``!funs f n ns body.
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     find_recfun f funs = SOME (n, naryFun ns body)``,
  Induct \\ fs [letrec_pull_params_def]
  THEN1 (fs [Once find_recfun_def]) \\
  rpt strip_tac \\ rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  rename1 `(f',n',body')` \\ fs [letrec_pull_params_def] \\
  every_case_tac \\ pop_assum mp_tac \\
  once_rewrite_tac [find_recfun_def] \\ fs [] \\
  every_case_tac \\ rw [] \\ fs [naryFun_def, Fun_params_Fun_body_repack]
)

(*------------------------------------------------------------------*)
(* The semantic counterpart of n-ary functions: n-ary closures

   Also, dealing with environments.
*)

(* [naryClosure] *)
val naryClosure_def = Define `
  naryClosure env (n::ns) body = Closure env n (naryFun ns body)`

(* Properties of [naryClosure] *)

val app_one_naryClosure = store_thm ("app_one_naryClosure",
  ``!env n ns x xs body H Q.
     ns <> [] ==> xs <> [] ==>
     app (p:'ffi ffi_proj) (naryClosure env (n::ns) body) (x::xs) H Q ==>
     app (p:'ffi ffi_proj) (naryClosure (env with v := (n, x)::env.v) ns body) xs H Q``,

  rpt strip_tac \\ Cases_on `ns` \\ Cases_on `xs` \\ fs [] \\
  rename1 `app _ (naryClosure _ (n::n'::ns) _) (x::x'::xs) _ _` \\
  Cases_on `xs` THENL [all_tac, rename1 `_::_::x''::xs`] \\
  fs [app_def, naryClosure_def, naryFun_def] \\
  fs [app_basic_def] \\ rpt strip_tac \\ first_x_assum progress \\
  fs [SEP_EXISTS, cond_def, STAR_def, SPLIT_emp2] \\
  qpat_assum `do_opapp _ = _` (assume_tac o REWRITE_RULE [do_opapp_def]) \\
  fs [] \\ qpat_assum `Fun _ _ = _` (assume_tac o GSYM) \\ fs [] \\
  qpat_assum `evaluate _ _ _ _ _`
    (assume_tac o ONCE_REWRITE_RULE [bigStepTheory.evaluate_cases]) \\
  fs [do_opapp_def] \\
  progress SPLIT_of_SPLIT3_2u3 \\ first_assum progress \\
  rename1 `SPLIT3 (st2heap _ st'') (h_f'', h_g'', h_g' UNION h_k)` \\
  `SPLIT3 (st2heap (p:'ffi ffi_proj) st'') (h_f'', h_g' UNION h_g'', h_k)` by SPLIT_TAC
  \\ instantiate
)

val curried_naryClosure = store_thm ("curried_naryClosure",
  ``!env len ns body.
     ns <> [] ==> len = LENGTH ns ==>
     curried (p:'ffi ffi_proj) len (naryClosure env ns body)``,

  Induct_on `ns` \\ fs [naryClosure_def, naryFun_def] \\ Cases_on `ns`
  THEN1 (once_rewrite_tac [ONE] \\ fs [Once curried_def])
  THEN1 (
    rpt strip_tac \\ fs [naryClosure_def, naryFun_def] \\
    rw [Once curried_def] \\ fs [app_basic_def] \\ rpt strip_tac \\
    fs [emp_def, cond_def, do_opapp_def] \\
    rename1 `SPLIT (st2heap _ st) ({}, h_k)` \\
    `SPLIT3 (st2heap (p:'ffi ffi_proj) st) ({}, {}, h_k)` by SPLIT_TAC \\
    instantiate \\ rename1 `(n, x) :: _` \\
    first_x_assum (qspecl_then [`env with v := (n,x)::env.v`, `body`]
      assume_tac) \\
    rpt (asm_exists_tac \\ fs []) \\ rpt strip_tac \\
    fs [Once bigStepTheory.evaluate_cases] \\
    fs [GSYM naryFun_def, GSYM naryClosure_def] \\
    irule app_one_naryClosure \\ Cases_on `xs` \\ fs []
  )
)

(* [naryRecclosure] *)
val naryRecclosure_def = Define `
  naryRecclosure env naryfuns f =
    Recclosure env
    (MAP (\ (f, ns, body). (f, HD ns, naryFun (TL ns) body)) naryfuns)
    f`

(* Properties of [naryRecclosure] *)

val do_opapp_naryRecclosure = store_thm ("do_opapp_naryRecclosure",
  ``!funs f n ns body x env env' exp.
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     (do_opapp [naryRecclosure env (letrec_pull_params funs) f; x] =
      SOME (env', exp)
     <=>
     (ALL_DISTINCT (MAP (\ (f,_,_). f) funs) /\
      env' = (env with v := (n, x)::build_rec_env funs env env.v) /\
      exp = naryFun ns body))``,
  rpt strip_tac \\ progress find_recfun_letrec_pull_params \\
  fs [naryRecclosure_def, do_opapp_def, letrec_pull_params_cancel] \\
  eq_tac \\ every_case_tac \\ fs []
)

val app_one_naryRecclosure = store_thm ("app_one_naryRecclosure",
  ``!funs f n ns body x xs env H Q.
     ns <> [] ==> xs <> [] ==>
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     (app (p:'ffi ffi_proj) (naryRecclosure env (letrec_pull_params funs) f) (x::xs) H Q ==>
      app (p:'ffi ffi_proj)
        (naryClosure
          (env with v := (n, x)::build_rec_env funs env env.v)
          ns body) xs H Q)``,

  rpt strip_tac \\ Cases_on `ns` \\ Cases_on `xs` \\ fs [] \\
  rename1 `SOME (n::n'::ns, _)` \\ rename1 `app _ _ (x::x'::xs)` \\
  Cases_on `xs` THENL [all_tac, rename1 `_::_::x''::xs`] \\
  fs [app_def, naryClosure_def, naryFun_def] \\
  fs [app_basic_def] \\ rpt strip_tac \\ first_x_assum progress \\
  fs [SEP_EXISTS, cond_def, STAR_def, SPLIT_emp2] \\
  progress_then (fs o sing) do_opapp_naryRecclosure \\ rw [] \\
  fs [naryFun_def] \\
  qpat_assum `evaluate _ _ _ _ _`
    (assume_tac o ONCE_REWRITE_RULE [bigStepTheory.evaluate_cases]) \\ rw [] \\
  fs [do_opapp_def] \\ progress SPLIT_of_SPLIT3_2u3 \\ first_x_assum progress \\
  rename1 `SPLIT3 (st2heap _ st') (h_f'', h_g'', h_g' UNION h_k)` \\
  `SPLIT3 (st2heap (p:'ffi ffi_proj) st') (h_f'', h_g' UNION h_g'', h_k)` by SPLIT_TAC \\
  instantiate
)

val curried_naryRecclosure = store_thm ("curried_naryRecclosure",
  ``!env funs f len ns body.
     ALL_DISTINCT (MAP (\ (f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (ns, body) ==>
     len = LENGTH ns ==>
     curried (p:'ffi ffi_proj) len (naryRecclosure env (letrec_pull_params funs) f)``,

  rpt strip_tac \\ Cases_on `ns` \\ fs []
  THEN1 (
    fs [curried_def, evalPropsTheory.find_recfun_ALOOKUP] \\
    progress ALOOKUP_MEM \\ progress letrec_pull_params_nonnil_params \\ fs []
  )
  THEN1 (
    rename1 `n::ns` \\ Cases_on `ns` \\ fs [Once curried_def] \\
    rename1 `n::n'::ns` \\ strip_tac \\ fs [app_basic_def] \\ rpt strip_tac \\
    fs [emp_def, cond_def] \\
    progress_then (fs o sing) do_opapp_naryRecclosure \\ rw [] \\
    Q.LIST_EXISTS_TAC [
      `naryClosure (env with v := (n, x)::build_rec_env funs env env.v)
                   (n'::ns) body`,
      `{}`, `st`
    ] \\ rpt strip_tac
    THEN1 SPLIT_TAC
    THEN1 (irule curried_naryClosure \\ fs [])
    THEN1 (irule app_one_naryRecclosure \\ fs [LENGTH_CONS] \\ metis_tac [])
    THEN1 (fs [naryFun_def, naryClosure_def, Once bigStepTheory.evaluate_cases])
  )
)

val letrec_pull_params_repack = store_thm ("letrec_pull_params_repack",
  ``!funs f env.
     naryRecclosure env (letrec_pull_params funs) f =
     Recclosure env funs f``,
  Induct \\ rpt strip_tac \\ fs [naryRecclosure_def, letrec_pull_params_def] \\
  rename1 `ftuple::_` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  fs [Fun_params_Fun_body_repack]
)

(** Extending environments *)

(* [extend_env] *)
val extend_env_v_def = Define `
  extend_env_v [] [] env_v = env_v /\
  extend_env_v (n::ns) (xv::xvs) env_v =
    extend_env_v ns xvs ((n,xv)::env_v)`

val extend_env_def = Define `
  extend_env ns xvs env = (env with v := extend_env_v ns xvs env.v)`

val extend_env_v_rcons = store_thm ("extend_env_v_rcons",
  ``!ns xvs n xv env_v.
     LENGTH ns = LENGTH xvs ==>
     extend_env_v (ns ++ [n]) (xvs ++ [xv]) env_v =
     (n,xv) :: extend_env_v ns xvs env_v``,
  Induct \\ rpt strip_tac \\ first_assum (assume_tac o GSYM) \\
  fs [LENGTH_NIL, LENGTH_CONS, extend_env_v_def]
)

val extend_env_v_zip = store_thm ("extend_env_v_zip",
  ``!ns xvs env_v.
    LENGTH ns = LENGTH xvs ==>
    extend_env_v ns xvs env_v = ZIP (REVERSE ns, REVERSE xvs) ++ env_v``,
  Induct \\ rpt strip_tac \\ first_assum (assume_tac o GSYM) \\
  fs [LENGTH_NIL, LENGTH_CONS, extend_env_v_def, GSYM ZIP_APPEND]
)

(* [build_rec_env_aux] *)
val build_rec_env_aux_def = Define `
  build_rec_env_aux funs (fs: (tvarN, tvarN # exp) alist) env add_to_env =
    FOLDR
      (\ (f,x,e) env'. (f, Recclosure env funs f) :: env')
      add_to_env
      fs`

val build_rec_env_zip_aux = Q.prove (
  `!(fs: (tvarN, tvarN # exp) alist) funs env env_v.
    ZIP (MAP (\ (f,_,_). f) fs,
         MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) fs)
      ++ env_v =
    FOLDR (\ (f,x,e) env'. (f,Recclosure env funs f)::env') env_v fs`,
  Induct \\ rpt strip_tac THEN1 (fs []) \\
  rename1 `ftuple::fs` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_repack]
)

val build_rec_env_zip = store_thm ("build_rec_env_zip",
  ``!funs env env_v.
     ZIP (MAP (\ (f,_,_). f) funs,
          MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
       ++ env_v =
     build_rec_env funs env env_v``,
  fs [build_rec_env_def, build_rec_env_zip_aux]
)

(* [extend_env_rec] *)
val extend_env_v_rec_def = Define `
  extend_env_v_rec rec_ns rec_xvs ns xvs env_v =
    extend_env_v ns xvs (ZIP (rec_ns, rec_xvs) ++ env_v)`

val extend_env_rec_def = Define `
  extend_env_rec rec_ns rec_xvs ns xvs env =
    env with v := extend_env_v_rec rec_ns rec_xvs ns xvs env.v`

val extend_env_rec_build_rec_env = store_thm ("extend_env_rec_build_rec_env",
  ``!funs env env_v.
     extend_env_v_rec
       (MAP (\ (f,_,_). f) funs)
       (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
       [] [] env_v =
     build_rec_env funs env env_v``,
  rpt strip_tac \\ fs [extend_env_v_rec_def, extend_env_v_def, build_rec_env_zip]
)

(*------------------------------------------------------------------*)
(** Pattern matching.

    CakeML pattern-matching is translated to pattern-matching in HOL
    using the src/pattern_matching library, by Tuerk et al.

    Restrictions:
    - the CakeML pattern-matching must "typecheck" (does not raise
      Match_type_error)
    - patterns that use [Pref] are not currently supported
*)

val pat_bindings_def = astTheory.pat_bindings_def
val pmatch_def = terminationTheory.pmatch_def
val pmatch_ind = terminationTheory.pmatch_ind

(* [v_of_pat]: from a pattern and a list of instantiations for the pattern
   variables, produce a semantic value
*)

val v_of_matching_pat_aux_measure_def = Define `
  v_of_matching_pat_aux_measure x =
    sum_CASE x
      (\(_,p,_). pat_size p)
      (\(_,ps,_). list_size pat_size ps)`

val v_of_pat_def = tDefine "v_of_pat" `
  v_of_pat envC (Pvar x) insts =
    (case insts of
         xv::rest => SOME (xv, rest)
       | _ => NONE) /\
  v_of_pat envC (Plit l) insts = SOME (Litv l, insts) /\
  v_of_pat envC (Pcon c args) insts =
    (case v_of_pat_list envC args insts of
         SOME (argsv, insts_rest) =>
         (case c of
              NONE => SOME (Conv NONE argsv, insts_rest)
            | SOME id =>
              case lookup_alist_mod_env id envC of
                  NONE => NONE
                | SOME (len, t) =>
                  if len = LENGTH argsv then
                    SOME (Conv (SOME (id_to_n id,t)) argsv, insts_rest)
                  else NONE)
      | NONE => NONE) /\
  v_of_pat _ (Pref pat) _ =
    NONE (* unsupported *) /\
  v_of_pat _ _ _ = NONE /\

  v_of_pat_list _ [] insts = SOME ([], insts) /\
  v_of_pat_list envC (p::argspat) insts =
    (case v_of_pat envC p insts of
         SOME (v, insts_rest) =>
         (case v_of_pat_list envC argspat insts_rest of
              SOME (vs, insts_rest') => SOME (v::vs, insts_rest')
            | NONE => NONE)
       | NONE => NONE) /\
  v_of_pat_list _ _ _ = NONE`

  (WF_REL_TAC `measure v_of_matching_pat_aux_measure` \\
   fs [v_of_matching_pat_aux_measure_def, list_size_def,
       astTheory.pat_size_def] \\
   gen_tac \\ Induct \\ fs [list_size_def, astTheory.pat_size_def])

val v_of_pat_ind = fetch "-" "v_of_pat_ind"

val v_of_pat_list_length = store_thm ("v_of_pat_list_length",
  ``!envC pats insts vs rest.
      v_of_pat_list envC pats insts = SOME (vs, rest) ==>
      LENGTH pats = LENGTH vs``,
  Induct_on `pats` \\ fs [v_of_pat_def] \\ rpt strip_tac \\
  every_case_tac \\ fs [] \\ rw [] \\ first_assum irule \\ instantiate
)

val v_of_pat_insts_length = store_thm ("v_of_pat_insts_length",
  ``(!envC pat insts v insts_rest.
       v_of_pat envC pat insts = SOME (v, insts_rest) ==>
       (LENGTH insts = LENGTH (pat_bindings pat []) + LENGTH insts_rest)) /\
    (!envC pats insts vs insts_rest.
       v_of_pat_list envC pats insts = SOME (vs, insts_rest) ==>
       (LENGTH insts = LENGTH (pats_bindings pats []) + LENGTH insts_rest))``,

  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  fs [v_of_pat_def, pat_bindings_def, LENGTH_NIL] \\ rw []
  THEN1 (every_case_tac \\ fs [LENGTH_NIL])
  THEN1 (every_case_tac \\ fs [])
  THEN1 (
    every_case_tac \\ fs [] \\ rw [] \\
    once_rewrite_tac [evalPropsTheory.pat_bindings_accum] \\ fs []
  )
)

val v_of_pat_extend_insts = store_thm ("v_of_pat_extend_insts",
  ``(!envC pat insts v rest insts'.
       v_of_pat envC pat insts = SOME (v, rest) ==>
       v_of_pat envC pat (insts ++ insts') = SOME (v, rest ++ insts')) /\
    (!envC pats insts vs rest insts'.
       v_of_pat_list envC pats insts = SOME (vs, rest) ==>
       v_of_pat_list envC pats (insts ++ insts') = SOME (vs, rest ++ insts'))``,

  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c`
    THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [])
    THEN1 (
      fs [v_of_pat_def] \\ every_case_tac \\ rw [] \\
      TRY (qpat_assum `LENGTH _ = LENGTH _` (K all_tac)) \\ fs [] \\
      rw []
    )
  )
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
)

val v_of_pat_NONE_extend_insts = store_thm ("v_of_pat_NONE_extend_insts",
  ``(!envC pat insts insts'.
       v_of_pat envC pat insts = NONE ==>
       LENGTH insts >= LENGTH (pat_bindings pat []) ==>
       v_of_pat envC pat (insts ++ insts') = NONE) /\
    (!envC pats insts insts'.
       v_of_pat_list envC pats insts = NONE ==>
       LENGTH insts >= LENGTH (pats_bindings pats []) ==>
       v_of_pat_list envC pats (insts ++ insts') = NONE)``,

  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def, pat_bindings_def])
  THEN1 (fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [])
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c`
    THEN1 (fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [])
    THEN1 (
      fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [] \\ rw [] \\
      metis_tac [v_of_pat_list_length]
    )
  )
  THEN1 (
    fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [] \\
    fs [Once (snd (CONJ_PAIR evalPropsTheory.pat_bindings_accum))]
    THEN1 (
      `LENGTH insts >= LENGTH (pat_bindings pat [])` by (fs []) \\ fs []
    )
    THEN1 (
      rw [] \\ progress (fst (CONJ_PAIR v_of_pat_insts_length)) \\
      rename1 `LENGTH insts = _ + LENGTH rest2` \\
      `LENGTH rest2 >= LENGTH (pats_bindings pats [])` by (fs []) \\ fs [] \\
      progress (fst (CONJ_PAIR v_of_pat_extend_insts)) \\
      pop_assum (qspec_then `insts'` assume_tac) \\ fs [] \\ rw [] \\ fs []
    )
  )
)

val v_of_pat_remove_rest_insts = store_thm ("v_of_pat_remove_rest_insts",
  ``(!pat envC insts v rest.
       v_of_pat envC pat insts = SOME (v, rest) ==>
       ?insts'.
         insts = insts' ++ rest /\
         LENGTH insts' = LENGTH (pat_bindings pat []) /\
         v_of_pat envC pat insts' = SOME (v, [])) /\
    (!pats envC insts vs rest.
       v_of_pat_list envC pats insts = SOME (vs, rest) ==>
       ?insts'.
         insts = insts' ++ rest /\
         LENGTH insts' = LENGTH (pats_bindings pats []) /\
         v_of_pat_list envC pats insts' = SOME (vs, []))``,

  HO_MATCH_MP_TAC astTheory.pat_induction \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def, pat_bindings_def])
  THEN1 (fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [])
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c` \\
    fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ rw []
  )
  THEN1 (fs [v_of_pat_def, pat_bindings_def, LENGTH_NIL])
  THEN1 (
    fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    qpat_assum_keep `v_of_pat _ _ _ = _` (first_assum o progress_with) \\
    qpat_assum_keep `v_of_pat_list _ _ _ = _` (first_assum o progress_with) \\
    rw []
    THEN1 (
      once_rewrite_tac [snd (CONJ_PAIR evalPropsTheory.pat_bindings_accum)] \\
      fs []
    )
    THEN1 (
      rename1 `LENGTH insts_pats = LENGTH (pats_bindings pats [])` \\
      rename1 `LENGTH insts_pat = LENGTH (pat_bindings pat [])` \\
      rename1 `v_of_pat_list _ _ (_ ++ rest)` \\
      fs [APPEND_ASSOC] \\ every_case_tac \\ fs []
      THEN1 (
        progress_then (qspec_then `rest` assume_tac)
          (fst (CONJ_PAIR v_of_pat_NONE_extend_insts)) \\
        `LENGTH (insts_pat ++ insts_pats) >= LENGTH (pat_bindings pat [])`
          by (fs []) \\ fs []
      ) \\
      rename1 `v_of_pat_list _ _ rest' = _` \\
      qpat_assum `v_of_pat _ _ (_ ++ _) = _` (first_assum o progress_with) \\
      `rest' = insts_pats` by (metis_tac [APPEND_11_LENGTH]) \\ fs []
    )
  )
)

val v_of_pat_insts_unique = store_thm ("v_of_pat_insts_unique",
  ``(!envC pat insts rest v.
       v_of_pat envC pat insts = SOME (v, rest) ==>
       (!insts'. v_of_pat envC pat insts' = SOME (v, rest) <=> (insts' = insts))) /\
    (!envC pats insts rest vs.
       v_of_pat_list envC pats insts = SOME (vs, rest) ==>
       (!insts'. v_of_pat_list envC pats insts' = SOME (vs, rest) <=> (insts' = insts)))``,

  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (
    fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    TRY (first_assum (qspec_then `insts'` assume_tac)) \\
    TRY (strip_tac \\ rw [] \\ fs []) \\
    TRY (qpat_assum `LENGTH _ = LENGTH _` (K all_tac)) (* otherwise fs[] loops? *) \\
    TRY (eq_tac \\ strip_tac \\ rw [] \\ fs []) \\ rw []
  )
  THEN1 (
    fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    TRY (strip_tac \\ rw [] \\ fs []) \\ rw [] \\ fs [] \\
    eq_tac \\ rw [] \\ fs [] \\ rw [] \\ fs []
  )
)

(* [v_of_pat_norest]: Wrapper that checks that there are no remaining
   instantiations
*)

val v_of_pat_norest_def = Define `
  v_of_pat_norest envC pat insts =
    case v_of_pat envC pat insts of
        SOME (v, []) => SOME v
      | _ => NONE`

val v_of_pat_norest_insts_length = store_thm ("v_of_pat_norest_insts_length",
  ``!envC pat insts v.
      v_of_pat_norest envC pat insts = SOME v ==>
      LENGTH insts = LENGTH (pat_bindings pat [])``,
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\ every_case_tac \\ fs [] \\
  rw [] \\ progress (fst (CONJ_PAIR v_of_pat_insts_length)) \\ fs []
)

val v_of_pat_norest_insts_unique = store_thm ("v_of_pat_norest_insts_unique",
  ``!envC pat insts v.
      v_of_pat_norest envC pat insts = SOME v ==>
      (!insts'. v_of_pat_norest envC pat insts' = SOME v <=> (insts' = insts))``,
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\
  every_case_tac \\ fs [] \\ rw [] \\ 
  try_finally (strip_tac \\ rw [] \\ fs []) \\
  eq_tac \\ rw [] \\ fs [] \\
  progress (fst (CONJ_PAIR (v_of_pat_insts_unique))) \\ fs []
)


(* Predicates that discriminate the patterns we want to deal
   with. [validate_pat] packs them all up.
*)

val pat_typechecks_def = Define `
  pat_typechecks envC s pat v env =
    (pmatch envC s pat v env <> Match_type_error)`

val pat_without_Pref_def = tDefine "pat_without_Pref" `
  pat_without_Pref (Pvar _) = T /\
  pat_without_Pref (Plit _) = T /\
  pat_without_Pref (Pcon _ args) =
    EVERY pat_without_Pref args /\
  pat_without_Pref (Pref _) = F`

  (WF_REL_TAC `measure pat_size` \\
   Cases \\ Induct \\ fs [basicSizeTheory.option_size_def] \\
   fs [list_size_def, astTheory.pat_size_def] \\ rpt strip_tac \\ fs [] \\
   first_assum progress \\ fs [])

val validate_pat_def = Define `
  validate_pat envC s pat v env =
    (pat_typechecks envC s pat v env /\
     pat_without_Pref pat /\
     ALL_DISTINCT (pat_bindings pat []))`


(* [PMATCH_ROW_of_pat]: the instance of [PMATCH_ROW] that corresponds to a
   CakeML pattern
*)

val PMATCH_ROW_of_pat_def = Define `
  PMATCH_ROW_of_pat pat branch_cf env =
    PMATCH_ROW
      (\insts. v_of_pat_norest env.c pat insts)
      (\_. T)
      (\insts.
         \env. branch_cf (extend_env (REVERSE (pat_bindings pat [])) insts env))`


(* Lemmas that relate [v_of_pat] and [pmatch], the pattern-matching function
   from the semantics.
*)

val pmatch_list_match_length = store_thm ("pmatch_list_match_length",
  ``!envC s pats args env env'.
     pmatch_list envC s pats args env = Match env' ==>
     LENGTH pats = LENGTH args``,
  Induct_on `pats` \\ Cases_on `args` \\ fs [pmatch_def] \\
  rpt strip_tac \\ every_case_tac \\ fs [] \\ first_assum irule \\ instantiate
)

val v_of_pat_pmatch = store_thm ("v_of_pat_pmatch",
  ``(!envC s pat v env_v insts.
      v_of_pat envC pat insts = SOME (v, []) ==>
      pmatch envC s pat v env_v = Match
        (ZIP (pat_bindings pat [], REVERSE insts) ++ env_v)) /\
    (!envC s pats vs env_v insts.
      v_of_pat_list envC pats insts = SOME (vs, []) ==>
      pmatch_list envC s pats vs env_v = Match
        (ZIP (pats_bindings pats [], REVERSE insts) ++ env_v))``,

  HO_MATCH_MP_TAC pmatch_ind \\ rpt strip_tac \\ rw [] \\
  try_finally (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs [] \\
    every_case_tac \\ fs []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs [] \\ rw []
    THEN1 (progress v_of_pat_list_length \\ fs []) \\
    `!(n:tvarN) t. same_ctor (n, t) (n, t)` by (
      Cases_on `n` \\ Cases_on `t` \\ fs [same_ctor_def]
    ) \\ fs []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    progress v_of_pat_list_length \\ fs []
  )
  THEN1 (
    fs [pmatch_def, pat_bindings_def, v_of_pat_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    try_finally (
      progress (fst (CONJ_PAIR v_of_pat_remove_rest_insts)) \\ rw [] \\
      rename1 `insts' ++ rest` \\ first_assum (qspec_then `insts'` (fs o sing))
    ) \\
    once_rewrite_tac [snd (CONJ_PAIR evalPropsTheory.pat_bindings_accum)] \\
    fs [] \\ progress (fst (CONJ_PAIR v_of_pat_remove_rest_insts)) \\ rw [] \\
    fs [REVERSE_APPEND] \\ progress (snd (CONJ_PAIR v_of_pat_insts_length)) \\
    fs [GSYM ZIP_APPEND] \\ once_rewrite_tac [GSYM APPEND_ASSOC] \\
    rpt (first_x_assum progress) \\ rw []
  )
)

val v_of_pat_norest_pmatch = store_thm ("v_of_pat_norest_pmatch",
  ``!envC s pat v env_v insts.
     v_of_pat_norest envC pat insts = SOME v ==>
     pmatch envC s pat v env_v = Match
       (ZIP (pat_bindings pat [], REVERSE insts) ++ env_v)``,
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\
  every_case_tac \\ fs [v_of_pat_pmatch]
)

val pmatch_v_of_pat = store_thm ("pmatch_v_of_pat",
  ``(!envC s pat v env_v env_v'.
      pmatch envC s pat v env_v = Match env_v' ==>
      pat_without_Pref pat ==>
      ?insts.
        env_v' = ZIP (pat_bindings pat [], REVERSE insts) ++ env_v /\
        v_of_pat envC pat insts = SOME (v, [])) /\
    (!envC s pats vs env_v env_v'.
      pmatch_list envC s pats vs env_v = Match env_v' ==>
      EVERY (\pat. pat_without_Pref pat) pats ==>
      ?insts.
        env_v' = ZIP (pats_bindings pats [], REVERSE insts) ++ env_v /\
        v_of_pat_list envC pats insts = SOME (vs, []))``,

  HO_MATCH_MP_TAC pmatch_ind \\ rpt strip_tac \\ rw [] \\
  try_finally (fs [pmatch_def, v_of_pat_def, pat_bindings_def])
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    qpat_assum `_ = _` (fs o sing o GSYM) \\
    rename1 `[(x,xv)]` \\ qexists_tac `[xv]` \\ fs []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs []
  )
  THEN1 (
    fs [pmatch_def, pat_without_Pref_def] \\ every_case_tac \\ fs [] \\
    fs [pat_bindings_def] \\ qexists_tac `insts` \\ fs [] \\
    rename1 `same_ctor (id_to_n id1, t1) (n2, t2)` \\
    `t1 = t2 /\ id_to_n id1 = n2` by
      (irule evalPropsTheory.same_ctor_and_same_tid \\ fs []) \\ rw [] \\
    rewrite_tac [v_of_pat_def] \\ fs [] \\ progress v_of_pat_list_length
  )
  THEN1 (
    fs [pmatch_def, pat_without_Pref_def] \\ every_case_tac \\ fs [] \\
    fs [pat_bindings_def] \\ qexists_tac `insts` \\ fs [] \\
    rewrite_tac [v_of_pat_def] \\ every_case_tac \\ fs []
  )
  THEN1 (fs [pat_without_Pref_def])
  THEN1 (
    fs [pmatch_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ rw [] \\ fs [pat_bindings_def] \\
    once_rewrite_tac [evalPropsTheory.pat_bindings_accum] \\ fs [] \\
    rename1 `ZIP (pat_bindings pat [], REVERSE insts)` \\
    rename1 `ZIP (pats_bindings pats [], REVERSE insts')` \\
    qexists_tac `insts ++ insts'` \\
    progress (fst (CONJ_PAIR v_of_pat_insts_length)) \\
    progress (snd (CONJ_PAIR v_of_pat_insts_length)) \\ fs [ZIP_APPEND] \\
    progress_then (qspec_then `insts'` assume_tac)
      (fst (CONJ_PAIR v_of_pat_extend_insts)) \\
    progress_then (qspec_then `insts'` assume_tac)
      (snd (CONJ_PAIR v_of_pat_extend_insts)) \\
    fs [v_of_pat_def]
  )
)

val pmatch_v_of_pat_norest = store_thm ("pmatch_v_of_pat_norest",
  ``!envC s pat v env_v env_v'.
      pmatch envC s pat v env_v = Match env_v' ==>
      pat_without_Pref pat ==>
      ?insts.
        env_v' = ZIP (pat_bindings pat [], REVERSE insts) ++ env_v /\
        v_of_pat_norest envC pat insts = SOME v``,
  rpt strip_tac \\ progress (fst (CONJ_PAIR pmatch_v_of_pat)) \\ fs [] \\
  qexists_tac `insts` \\ fs [v_of_pat_norest_def]
)

val v_of_pat_Con_cons = Q.prove (
  `!envC env_v s pat v env_v' pats vs insts insts'.
     pmatch envC s pat v env_v = Match env_v' ==>
     pat_without_Pref pat ==>
     v_of_pat envC (Pcon NONE pats) insts' = SOME (Conv NONE vs, []) ==>
     ?insts.
       env_v' = ZIP (pat_bindings pat [], REVERSE insts) ++ env_v /\
       v_of_pat envC (Pcon NONE (pat::pats)) (insts ++ insts') = SOME (Conv NONE (v::vs), [])`,

  rpt strip_tac \\ progress (fst (CONJ_PAIR pmatch_v_of_pat)) \\ rw [] \\
  rename1 `ZIP (pat_bindings pat [], REVERSE insts)` \\ qexists_tac `insts` \\
  progress_then (qspec_then `insts'` assume_tac)
    (fst (CONJ_PAIR v_of_pat_extend_insts)) \\ fs [] \\
  qpat_assum `v_of_pat _ (Pcon _ pats) _ = _`
    (assume_tac o SIMP_RULE std_ss [v_of_pat_def]) \\ every_case_tac \\ rw [] \\
  fs [build_conv_def] \\ rw [] \\
  progress_then (qspec_then `insts'` assume_tac)
    (snd (CONJ_PAIR v_of_pat_extend_insts)) \\ fs [] \\
  rewrite_tac [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw []
)


(* Lemmas relating our [PMATCH_ROW]s with the semantic pattern-matching [pmatch]
*)

val PMATCH_ROW_pmatch = store_thm ("PMATCH_ROW_pmatch",
  ``!pat bcf s env v cf H Q.
     PMATCH_ROW_of_pat pat bcf env (SOME v) = SOME cf ==>
     cf env H Q ==>
     ?env_v'.
       pmatch env.c s pat v env.v = Match env_v' /\
       bcf (env with v := env_v') H Q``,

  rpt strip_tac \\
  fs [PMATCH_ROW_of_pat_def, PMATCH_ROW_def, PMATCH_ROW_COND_def, some_def] \\
  rw [] \\ fs [] \\
  progress v_of_pat_norest_insts_length \\
  progress_then (qspecl_then [`s`, `env.v`] assume_tac) v_of_pat_norest_pmatch \\
  instantiate \\ progress v_of_pat_norest_insts_unique \\ fs [SELECT_UNIQUE] \\
  fs [extend_env_def, extend_env_v_zip] 
)

val PMATCH_ROW_of_pat_matching_Con_NONE = Q.prove (
  `!env pcname pcnum pctid vcname vcn vctid pats args bcf.
   lookup_alist_mod_env pcname env.c = SOME (pcnum, pctid) ==>
   vcname = (vcn, vctid) ==>
   pctid = vctid /\ id_to_n pcname = vcn ==>
   LENGTH pats = pcnum ==>
   PMATCH_ROW_of_pat (Pcon (SOME pcname) pats) bcf env (SOME (Conv (SOME vcname) args)) = NONE ==>
   PMATCH_ROW_of_pat (Pcon NONE pats) bcf env (SOME (Conv NONE args)) = NONE`,

  rpt strip_tac \\
  fs [PMATCH_ROW_of_pat_def, PMATCH_ROW_def, PMATCH_ROW_COND_def, some_def] \\
  qx_gen_tac `inst` \\ pop_assum (qspec_then `inst` assume_tac) \\ rw [] \\
  fs [v_of_pat_norest_def] \\ every_case_tac \\ fs [] \\
  fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [] \\
  progress v_of_pat_list_length
)

val PMATCH_ROW_of_pat_con_cons_NONE = Q.prove (
  `!env s pat v env_v' pats args bcf.
     pmatch env.c s pat v env.v = Match env_v' ==>
     pat_without_Pref pat ==>
     PMATCH_ROW_of_pat (Pcon NONE (pat::pats)) bcf env
       (SOME (Conv NONE (v::args))) = NONE ==>
     PMATCH_ROW_of_pat (Pcon NONE pats) bcf (env with v := env_v')
       (SOME (Conv NONE args)) = NONE`,

  rpt strip_tac \\
  fs [PMATCH_ROW_of_pat_def, PMATCH_ROW_def, PMATCH_ROW_COND_def, some_def] \\
  qx_gen_tac `insts` \\ rewrite_tac [v_of_pat_norest_def] \\
  every_case_tac \\ fs [] \\ strip_tac \\ first_x_assum irule \\ rw [] \\
  progress v_of_pat_Con_cons \\ rw [] \\
  rename1 `v_of_pat _ (Pcon _ (_::_)) (insts_pat ++ insts_pats)` \\
  qexists_tac `insts_pat ++ insts_pats` \\ 
  fs [v_of_pat_norest_def] \\ every_case_tac \\ fs []
)

val PMATCH_ROW_pmatch_nomatch = store_thm ("PMATCH_ROW_pmatch_nomatch",
  ``(!pat env s v (branch_cf: v environment -> 'a).
      pat_without_Pref pat ==>
      pmatch env.c s pat v env.v <> Match_type_error ==>
      PMATCH_ROW_of_pat pat branch_cf env (SOME v) = NONE ==>
      pmatch env.c s pat v env.v = No_match) /\
    (!pats env s vs (branch_cf: v environment -> 'a) cname pcname.
      EVERY (\pat. pat_without_Pref pat) pats ==>
      pmatch env.c s (Pcon NONE pats) (Conv NONE vs) env.v <> Match_type_error ==>
      PMATCH_ROW_of_pat (Pcon NONE pats) branch_cf env (SOME (Conv NONE vs)) = NONE ==>
      pmatch_list env.c s pats vs env.v = No_match)``,

  HO_MATCH_MP_TAC astTheory.pat_induction \\
  rpt strip_tac
  THEN1 (
    fs [PMATCH_ROW_of_pat_def, PMATCH_ROW_def, PMATCH_ROW_COND_def, some_def] \\
    first_assum (qspec_then `[v]` assume_tac) \\
    fs [v_of_pat_norest_def, v_of_pat_def]
  )
  THEN1 (
    fs [PMATCH_ROW_of_pat_def, PMATCH_ROW_def, PMATCH_ROW_COND_def, some_def] \\
    first_x_assum (qspec_then `[]` assume_tac) \\
    fs [v_of_pat_norest_def, v_of_pat_def] \\ rename1 `Litv l <> v` \\
    Cases_on `v` \\ fs [pmatch_def] \\ every_case_tac \\ fs []
  )
  THEN1 (
    qpat_assum `pmatch _ _ _ _ _ <> _` mp_tac \\
    Cases_on `v` \\ try_finally (fs [pmatch_def] \\ every_case_tac) \\
    rename1 `Conv name_opt args` \\ rename1 `Pcon pname_opt _` \\
    Cases_on `name_opt` \\ Cases_on `pname_opt` \\ try_finally (fs [pmatch_def])
    THEN1 (
      fs [pmatch_def] \\ every_case_tac \\ fs [] \\ strip_tac \\
      first_assum irule \\ fs [pat_without_Pref_def] \\ instantiate
    )
    THEN1 (
      rename1 `Conv (SOME cname) _` \\ Cases_on `cname` \\
      fs [pat_without_Pref_def] \\
      (* At this point:
         - either the constructors are differents (and in this case, pmatch ... = No_match,
           which proves the goal)... *)
      fs [pmatch_def] \\ every_case_tac \\ strip_tac \\
      (* - or the constructors are the same, and:
           - pmatch_list ... = No_match, which proves the goal
           - pmatch_list ... = Match, then we know LENGTH pats = LENGTH args, and
             modulo additional lemmas we can use the induction hypothesis to prove
             pmatch_list ... = No_match, proving the goal that became F *)
      Cases_on `pmatch_list env.c s pats args env.v` \\ fs [] \\ rw [] \\
      progress pmatch_list_match_length \\
      `pmatch_list env.c s pats args env.v = No_match` by (
        first_assum irule
        THEN1 (every_case_tac \\ fs [])
        THEN1 (
          qexists_tac `branch_cf` \\
          irule PMATCH_ROW_of_pat_matching_Con_NONE \\ instantiate \\
          rename1 `same_ctor (id_to_n id1, tid1) (n2, tid2)` \\
          qsuff_tac `tid1 = tid2 /\ id_to_n id1 = n2`
            THEN1 (fs [CONJ_COMM, EQ_SYM]) \\
          irule evalPropsTheory.same_ctor_and_same_tid \\ fs []
        )
      ) \\ fs []
    )
  )
  THEN1 (
    fs [pat_without_Pref_def]
  )
  THEN1 (
    Cases_on `vs` \\ fs [pmatch_def] \\
    fs [PMATCH_ROW_of_pat_def, PMATCH_ROW_def, PMATCH_ROW_COND_def, some_def] \\
    first_x_assum (qspec_then `[]` assume_tac) \\
    fs [v_of_pat_norest_def, v_of_pat_def, build_conv_def]
  )
  THEN1 (
    Cases_on `vs` \\ fs [pmatch_def] \\ every_case_tac \\ fs [] \\
    progress (fst (CONJ_PAIR evalPropsTheory.pmatch_extend)) \\ rw [] \\
    rename1 `pmatch_list _ _ _ args (matched_env ++ env.v)` \\
    qsuff_tac `pmatch_list (env with v := matched_env ++ env.v).c s pats args
                           (env with v := matched_env ++ env.v).v = No_match`
      THEN1 (fs []) \\
    first_assum irule \\ fs [] \\ qexists_tac `branch_cf` \\
    irule PMATCH_ROW_of_pat_con_cons_NONE \\ instantiate
  )
)

(*------------------------------------------------------------------*)
(* Definition of the [cf] functions, that generates the characteristic
   formula of a cakeml expression *)

val cf_bottom_def = Define `
  cf_bottom = \env. local (\H Q. F)`

val app_ref_def = Define `
  app_ref (x: v) H Q =
    !(r: num). H * r ~~> Refv x ==>> Q (Loc r)`

val app_assign_def = Define `
  app_assign (r: num) (x: v) H Q =
    ?x' F.
      (H ==>> F * r ~~> Refv x') /\
      (F * r ~~> Refv x ==>> Q (Conv NONE []))`

val app_deref_def = Define `
  app_deref (r: num) H Q =
    ?x F.
      (H ==>> F * r ~~> Refv x) /\
      (H ==>> Q x)`

val app_aalloc_def = Define `
  app_aalloc (n: int) v H Q =
    !(loc: num).
      n >= 0 /\
      (H * loc ~~> Varray (REPLICATE (Num (ABS n)) v) ==>> Q (Loc loc))`

val app_asub_def = Define `
  app_asub (loc: num) (i: int) H Q =
    ?vs F.
      let n = Num (ABS i) in
      0 <= i /\ n < LENGTH vs /\
      (H ==>> F * loc ~~> Varray vs) /\
      (H ==>> Q (EL n vs))`

val app_alength_def = Define `
  app_alength (loc: num) H Q =
    ?vs F.
      (H ==>> F * loc ~~> Varray vs) /\
      (H ==>> Q (Litv (IntLit (int_of_num (LENGTH vs)))))`

val app_aupdate_def = Define `
  app_aupdate (loc: num) (i: int) v H Q =
    ?vs F.
      let n = Num (ABS i) in
      0 <= i /\ n < LENGTH vs /\
      (H ==>> F * loc ~~> Varray vs) /\
      (F * loc ~~> Varray (LUPDATE v n vs) ==>> Q (Conv NONE []))`

val app_aw8alloc_def = Define `
  app_aw8alloc (n: int) w H Q =
    !(loc: num).
      n >= 0 /\
      (H * loc ~~> W8array (REPLICATE (Num (ABS n)) w) ==>> Q (Loc loc))`

val app_aw8sub_def = Define `
  app_aw8sub (loc: num) (i: int) H Q =
    ?ws F.
      let n = Num (ABS i) in
      0 <= i /\ n < LENGTH ws /\
      (H ==>> F * loc ~~> W8array ws) /\
      (H ==>> Q (Litv (Word8 (EL n ws))))`

val app_aw8length_def = Define `
  app_aw8length (loc: num) H Q =
    ?ws F.
      (H ==>> F * loc ~~> W8array ws) /\
      (H ==>> Q (Litv (IntLit (int_of_num (LENGTH ws)))))`

val app_aw8update_def = Define `
  app_aw8update (loc: num) (i: int) w H Q =
    ?ws F.
      let n = Num (ABS i) in
      0 <= i /\ n < LENGTH ws /\
      (H ==>> F * loc ~~> W8array ws) /\
      (F * loc ~~> W8array (LUPDATE w n ws) ==>> Q (Conv NONE []))`

val app_opn_def = Define `
  app_opn opn i1 i2 H Q =
    ((if opn = Divide \/ opn = Modulo then i2 <> 0 else T) /\
     (H ==>> Q (Litv (IntLit (opn_lookup opn i1 i2)))))`

val app_opb_def = Define `
  app_opb opb i1 i2 H Q =
    H ==>> Q (Boolv (opb_lookup opb i1 i2))`


val cf_lit_def = Define `
  cf_lit l = \env. local (\H Q. H ==>> Q (Litv l))`

val cf_con_def = Define `
  cf_con cn args = \env. local (\H Q.
    ?argsv cv.
      do_con_check env.c cn (LENGTH args) /\
      (build_conv env.c cn argsv = SOME cv) /\
      (exp2v_list env args = SOME argsv) /\
      (H ==>> Q cv))`

val cf_var_def = Define `
  cf_var name = \env. local (\H Q.
    !h. H h ==> ?v. lookup_var_id name env = SOME v /\ Q v h)`

val cf_let_def = Define `
  cf_let n F1 F2 = \env. local (\H Q.
    ?Q'. F1 env H Q' /\
         !xv. F2 (env with <| v := opt_bind n xv env.v |>) (Q' xv) Q)`

val cf_opn_def = Define `
  cf_opn opn x1 x2 = \env. local (\H Q.
    ?i1 i2.
      exp2v env x1 = SOME (Litv (IntLit i1)) /\
      exp2v env x2 = SOME (Litv (IntLit i2)) /\
      app_opn opn i1 i2 H Q)`

val cf_opb_def = Define `
  cf_opb opb x1 x2 = \env. local (\H Q.
    ?i1 i2.
      exp2v env x1 = SOME (Litv (IntLit i1)) /\
      exp2v env x2 = SOME (Litv (IntLit i2)) /\
      app_opb opb i1 i2 H Q)`

val cf_app_def = Define `
  cf_app (p:'ffi ffi_proj) f args = \env. local (\H Q.
    ?fv argsv.
      exp2v env f = SOME fv /\
      exp2v_list env args = SOME argsv /\
      app (p:'ffi ffi_proj) fv argsv H Q)`

val cf_fundecl_def = Define `
  cf_fundecl (p:'ffi ffi_proj) f ns F1 F2 = \env. local (\H Q.
    !fv.
      curried (p:'ffi ffi_proj) (LENGTH ns) fv /\
      (!xvs H' Q'.
        LENGTH xvs = LENGTH ns ==>
        F1 (extend_env ns xvs env) H' Q' ==>
        app (p:'ffi ffi_proj) fv xvs H' Q')
      ==>
      F2 (env with v := (f, fv)::env.v) H Q)`

val fundecl_rec_aux_def = Define `
  fundecl_rec_aux (p:'ffi ffi_proj) fs fvs [] [] [] F2 env H Q =
    (F2 (extend_env_rec fs fvs [] [] env) H Q) /\
  fundecl_rec_aux (p:'ffi ffi_proj) fs fvs (ns::ns_acc) (fv::fv_acc) (Fbody::Fs) F2 env H Q =
    (curried (p:'ffi ffi_proj) (LENGTH ns) fv /\
     (!xvs H' Q'.
        LENGTH xvs = LENGTH ns ==>
        Fbody (extend_env_rec fs fvs ns xvs env) H' Q' ==>
        app (p:'ffi ffi_proj) fv xvs H' Q')
     ==>
     (fundecl_rec_aux (p:'ffi ffi_proj) fs fvs ns_acc fv_acc Fs F2 env H Q)) /\
  fundecl_rec_aux _ _ _ _ _ _ _ _ _ _ = F`

val cf_fundecl_rec_def = Define `
  cf_fundecl_rec (p:'ffi ffi_proj) fs Fs F2 = \env. local (\H Q.
    let f_names = MAP (\ (f,_,_). f) fs in
    let f_args = MAP (\ (_,ns,_). ns) fs in
    !(fvs: v list).
      LENGTH fvs = LENGTH fs ==>
      ALL_DISTINCT f_names /\
      fundecl_rec_aux (p:'ffi ffi_proj) f_names fvs f_args fvs Fs F2 env H Q)`

val cf_ref_def = Define `
  cf_ref x = \env. local (\H Q.
    ?xv.
      exp2v env x = SOME xv /\
      app_ref xv H Q)`

val cf_assign_def = Define `
  cf_assign r x = \env. local (\H Q.
    ?rv xv.
      exp2v env r = SOME (Loc rv) /\
      exp2v env x = SOME xv /\
      app_assign rv xv H Q)`

val cf_deref_def = Define `
  cf_deref r = \env. local (\H Q.
    ?rv.
      exp2v env r = SOME (Loc rv) /\
      app_deref rv H Q)`

val cf_aalloc_def = Define `
  cf_aalloc xn xv = \env. local (\H Q.
    ?n v.
      exp2v env xn = SOME (Litv (IntLit n)) /\
      exp2v env xv = SOME v /\
      app_aalloc n v H Q)`

val cf_asub_def = Define `
  cf_asub xl xi = \env. local (\H Q.
    ?l i.
      exp2v env xl = SOME (Loc l) /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_asub l i H Q)`

val cf_alength_def = Define `
  cf_alength xl = \env. local (\H Q.
    ?l.
      exp2v env xl = SOME (Loc l) /\
      app_alength l H Q)`

val cf_aupdate_def = Define `
  cf_aupdate xl xi xv = \env. local (\H Q.
    ?l i v.
      exp2v env xl = SOME (Loc l) /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      exp2v env xv = SOME v /\
      app_aupdate l i v H Q)`

val cf_aw8alloc_def = Define `
  cf_aw8alloc xn xw = \env. local (\H Q.
    ?n w.
      exp2v env xn = SOME (Litv (IntLit n)) /\
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_aw8alloc n w H Q)`

val cf_aw8sub_def = Define `
  cf_aw8sub xl xi = \env. local (\H Q.
    ?l i.
      exp2v env xl = SOME (Loc l) /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_aw8sub l i H Q)`

val cf_aw8length_def = Define `
  cf_aw8length xl = \env. local (\H Q.
    ?l.
      exp2v env xl = SOME (Loc l) /\
      app_aw8length l H Q)`

val cf_aw8update_def = Define `
  cf_aw8update xl xi xw = \env. local (\H Q.
    ?l i w.
      exp2v env xl = SOME (Loc l) /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_aw8update l i w H Q)`

val cf_mat_def = Define `
  cf_mat e pats branches = \env. local (\H Q.
    ?v branch_cf.
      exp2v env e = SOME v /\
      (!s. EVERY (\pat. validate_pat env.c s pat v env.v) pats) /\
      PMATCH (SOME v) branches = branch_cf /\
      branch_cf <> PMATCH_INCOMPLETE /\
      branch_cf env H Q)`

(* todo: replace by THE *)
val SOME_val_def = Define `
  SOME_val (SOME x) = x`

val cf_def = tDefine "cf" `
  cf (p:'ffi ffi_proj) (Lit l) = cf_lit l /\
  cf (p:'ffi ffi_proj) (Con opt args) = cf_con opt args /\
  cf (p:'ffi ffi_proj) (Var name) = cf_var name /\
  cf (p:'ffi ffi_proj) (Let opt e1 e2) =
    (if is_bound_Fun opt e1 then
       (case Fun_body e1 of
          | SOME body =>
            cf_fundecl (p:'ffi ffi_proj) (SOME_val opt) (Fun_params e1)
              (cf (p:'ffi ffi_proj) body) (cf (p:'ffi ffi_proj) e2)
          | NONE => cf_bottom)
     else
       cf_let opt (cf (p:'ffi ffi_proj) e1) (cf (p:'ffi ffi_proj) e2)) /\
  cf (p:'ffi ffi_proj) (Letrec funs e) =
    (cf_fundecl_rec (p:'ffi ffi_proj) (letrec_pull_params funs)
       (MAP (\x. cf (p:'ffi ffi_proj) (SND (SND x))) (letrec_pull_params funs))
       (cf (p:'ffi ffi_proj) e)) /\
  cf (p:'ffi ffi_proj) (App op args) =
    (case op of
        | Opn opn =>
          (case args of
            | [x1; x2] => cf_opn opn x1 x2
            | _ => cf_bottom)
        | Opb opb =>
          (case args of
            | [x1; x2] => cf_opb opb x1 x2
            | _ => cf_bottom)
        | Opapp =>
          (case dest_opapp (App op args) of
            | SOME (f, xs) => cf_app (p:'ffi ffi_proj) f xs
            | NONE => cf_bottom)
        | Opref =>
          (case args of
             | [x] => cf_ref x
             | _ => cf_bottom)
        | Opassign =>
          (case args of
             | [r; x] => cf_assign r x
             | _ => cf_bottom)
        | Opderef =>
          (case args of
             | [r] => cf_deref r
             | _ => cf_bottom)
        | Aalloc =>
          (case args of
            | [n; v] => cf_aalloc n v
            | _ => cf_bottom)
        | Asub =>
          (case args of
            | [l; n] => cf_asub l n
            | _ => cf_bottom)
        | Alength =>
          (case args of
            | [l] => cf_alength l
            | _ => cf_bottom)
        | Aupdate =>
          (case args of
            | [l; n; v] => cf_aupdate l n v
            | _ => cf_bottom)
        | Aw8alloc =>
          (case args of
             | [n; w] => cf_aw8alloc n w
             | _ => cf_bottom)
        | Aw8sub =>
          (case args of
             | [l; n] => cf_aw8sub l n
             | _ => cf_bottom)
        | Aw8length =>
          (case args of
             | [l] => cf_aw8length l
             | _ => cf_bottom)
        | Aw8update =>
          (case args of
             | [l; n; w] => cf_aw8update l n w
             | _ => cf_bottom)
        | _ => cf_bottom) /\
  cf (p:'ffi ffi_proj) (Mat e branches) =
    (\env.
       cf_mat e
         (MAP FST branches)
         (MAP (\b. PMATCH_ROW_of_pat (FST b) (cf p (SND b)) env) branches)
         env) /\
  cf _ _ = cf_bottom`

  (WF_REL_TAC `measure (exp_size o SND)` \\ rw []
     THEN1 (
       Cases_on `opt` \\ Cases_on `e1` \\ fs [is_bound_Fun_def] \\
       drule Fun_body_exp_size \\ strip_tac \\ fs [astTheory.exp_size_def]
     )
     THEN1 (
       Induct_on `funs` \\ fs [MEM, letrec_pull_params_def] \\ rpt strip_tac \\
       rename1 `f::funs` \\ PairCases_on `f` \\ rename1 `(f,ns,body)::funs` \\
       fs [letrec_pull_params_def] \\ fs [astTheory.exp_size_def] \\
       every_case_tac \\ fs [astTheory.exp_size_def] \\
       drule Fun_body_exp_size \\ strip_tac \\ fs [astTheory.exp_size_def]
     )
     THEN1 (
       Induct_on `branches` \\ fs [MEM] \\ rpt strip_tac \\ rw [] \\
       fs [astTheory.exp_size_def]
     )
  )

val cf_ind = fetch "-" "cf_ind"

val cf_defs = [cf_def, cf_lit_def, cf_con_def, cf_var_def, cf_fundecl_def, cf_let_def,
               cf_opn_def, cf_opb_def, cf_aalloc_def, cf_asub_def, cf_alength_def,
               cf_aupdate_def, cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def,
               cf_aw8update_def, cf_app_def, cf_ref_def, cf_assign_def, cf_deref_def,
               cf_fundecl_rec_def, cf_bottom_def, cf_mat_def]

(*------------------------------------------------------------------*)
(** Properties about [cf]. The main result is the proof of soundness,
    [cf_sound] *)

val cf_local = store_thm ("cf_local",
  ``!e. is_local (cf (p:'ffi ffi_proj) e env)``,
  Q.SPEC_TAC (`p`,`p`) \\
  recInduct cf_ind \\ rpt strip_tac \\
  fs (local_local :: local_is_local :: cf_defs)
  THEN1 (
    Cases_on `opt` \\ Cases_on `e1` \\ fs [is_bound_Fun_def, local_is_local] \\
    fs [Fun_body_def] \\ every_case_tac \\ fs [local_is_local]
  )
  THEN1 (
    Cases_on `op` \\ fs [local_is_local] \\
    every_case_tac \\ fs [local_is_local]
  )
)

(* Soundness of cf *)

val sound_def = Define `
  sound (p:'ffi ffi_proj) e R =
    !env H Q. R env H Q ==>
    !st h_i h_k. SPLIT (st2heap (p:'ffi ffi_proj) st) (h_i, h_k) ==>
    H h_i ==>
      ?v st' h_f h_g.
        SPLIT3 (st2heap (p:'ffi ffi_proj) st') (h_f, h_k, h_g) /\
        evaluate F env st e (st', Rval v) /\
        Q v h_f`

val star_split = Q.prove (
  `!H1 H2 H3 H4 h1 h2 h3 h4.
     ((H1 * H2) (h1 UNION h2) ==> (H3 * H4) (h3 UNION h4)) ==>
     DISJOINT h1 h2 ==> H1 h1 ==> H2 h2 ==>
     ?u v. H3 u /\ H4 v /\ SPLIT (h3 UNION h4) (u, v)`,
  fs [STAR_def] \\ rpt strip_tac \\
  `SPLIT (h1 UNION h2) (h1, h2)` by SPLIT_TAC \\
  metis_tac []
)

val sound_local = store_thm ("sound_local",
  ``!e R. sound (p:'ffi ffi_proj) e R ==> sound (p:'ffi ffi_proj) e (\env. local (R env))``,
  rpt strip_tac \\ rewrite_tac [sound_def] \\ fs [local_def] \\ rpt strip_tac \\
  res_tac \\ rename1 `(H_i * H_k) h_i` \\ rename1 `R env H_i Q_f` \\
  rename1 `SEP_IMPPOST (Q_f *+ H_k) (Q *+ H_g)` \\
  fs [STAR_def] \\ rename1 `H_i h'_i` \\ rename1 `H_k h'_k` \\
  `SPLIT (st2heap (p:'ffi ffi_proj) st) (h'_i, h_k UNION h'_k)` by SPLIT_TAC \\
  qpat_assum `sound _ _ _` (progress o REWRITE_RULE [sound_def]) \\
  rename1 `SPLIT3 _ (h'_f, _, h'_g)` \\
  fs [SEP_IMPPOST_def, STARPOST_def, SEP_IMP_def, STAR_def] \\
  first_x_assum (qspecl_then [`v`, `h'_f UNION h'_k`] assume_tac) \\
  `DISJOINT h'_f h'_k` by SPLIT_TAC \\
  `?h_f h''_g. Q v h_f /\ H_g h''_g /\ SPLIT (h'_f UNION h'_k) (h_f, h''_g)` by
    metis_tac [star_split] \\
  Q.LIST_EXISTS_TAC [`v`, `st'`, `h_f`, `h'_g UNION h''_g`] \\ fs [] \\
  SPLIT_TAC
)

val sound_false = store_thm ("sound_false",
  ``!e. sound (p:'ffi ffi_proj) e (\env H Q. F)``,
  rewrite_tac [sound_def]
)

val sound_local_false = Q.prove (
  `!e. sound (p:'ffi ffi_proj) e (\env. local (\H Q. F))`,
  strip_tac \\ HO_MATCH_MP_TAC sound_local \\ fs [sound_false]
)

val cf_base_case_tac =
  HO_MATCH_MP_TAC sound_local \\ rewrite_tac [sound_def] \\
  rpt strip_tac \\ fs [] \\ res_tac \\
  rename1 `SPLIT (st2heap _ st) (h_i, h_k)` \\
  progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
  once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [SEP_IMP_def]

val cf_strip_sound_tac =
  TRY (HO_MATCH_MP_TAC sound_local) \\ rewrite_tac [sound_def] \\
  rpt strip_tac \\ fs []

val cf_evaluate_step_tac =
  once_rewrite_tac [bigStepTheory.evaluate_cases] \\
  fs [libTheory.opt_bind_def, PULL_EXISTS]

val cf_strip_sound_full_tac = cf_strip_sound_tac \\ cf_evaluate_step_tac

fun cf_evaluate_list_tac [] = prove_tac [bigStepTheory.evaluate_rules]
  | cf_evaluate_list_tac (st::sts) =
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    qexists_tac st \\ strip_tac THENL [fs [exp2v_evaluate], all_tac] \\
    cf_evaluate_list_tac sts

val app_basic_of_sound_cf = Q.prove (
  `!clos body x env env' v H Q.
    do_opapp [clos; x] = SOME (env', body) ==>
    sound (p:'ffi ffi_proj) body (cf (p:'ffi ffi_proj) body) ==>
    cf (p:'ffi ffi_proj) body env' H Q ==>
    app_basic (p:'ffi ffi_proj) clos x H Q`,
  fs [app_basic_def, sound_def] \\ rpt strip_tac \\ first_x_assum progress \\
  instantiate \\ SPLIT_TAC
)

val app_of_sound_cf = Q.prove (
  `!ns xvs env body H Q.
     ns <> [] ==>
     LENGTH ns = LENGTH xvs ==>
     sound (p:'ffi ffi_proj) body (cf (p:'ffi ffi_proj) body) ==>
     cf (p:'ffi ffi_proj) body (extend_env ns xvs env) H Q ==>
     app (p:'ffi ffi_proj) (naryClosure env ns body) xvs H Q`,

  Induct \\ rpt strip_tac \\ fs [naryClosure_def, LENGTH_CONS] \\ rw [] \\
  rename1 `extend_env (n::ns) (xv::xvs) _` \\ Cases_on `ns` \\
  fs [LENGTH_NIL, LENGTH_CONS] \\ rw [] \\
  rfs [extend_env_def, Once extend_env_v_def, naryFun_def, app_def]
  THEN1 (irule app_basic_of_sound_cf \\ fs [extend_env_v_def, do_opapp_def])
  THEN1 (
    rename1 `extend_env_v (n'::ns) (xv'::xvs) _` \\
    fs [app_basic_def] \\ rpt strip_tac \\ fs [do_opapp_def] \\
    fs [SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS, SPLIT_emp2] \\
    fs [naryFun_def, naryClosure_def, Once bigStepTheory.evaluate_cases] \\
    first_assum progress \\ instantiate \\ qexists_tac `{}` \\ SPLIT_TAC
  )
)

val find_recfun_map = Q.prove (
  `!l a b c f u v.
     (!a b c. FST (f (a, b, c)) = a) ==>
     f (a, b, c) = (a, u, v) ==>
     find_recfun a l = SOME (b, c) ==>
     find_recfun a (MAP f l) = SOME (u, v)`,
  Induct_on `l`
  THEN1 (fs [find_recfun_def]) \\ rpt gen_tac \\
  NTAC 2 DISCH_TAC \\
  rename1 `x::_` \\ PairCases_on `x` \\ rename1 `(a',b',c')` \\
  rewrite_tac [Once find_recfun_def] \\ fs [] \\
  Cases_on `a' = a` \\ fs [] \\ rpt strip_tac
  THEN1 (fs [Once find_recfun_def])
  THEN1 (
    rewrite_tac [Once find_recfun_def] \\ fs [] \\
    `?u' v'. f (a', b', c') = (a', u', v')` by (
      first_assum (qspecl_then [`a'`, `b'`, `c'`] assume_tac) \\
      qabbrev_tac `x' = f (a',b',c')` \\ PairCases_on `x'` \\ fs []
    ) \\ fs [] \\
    fs [Once find_recfun_def]
  )
)

val app_rec_of_sound_cf_aux = Q.prove (
  `!f body params xvs funs naryfuns env H Q fvs.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     naryfuns = letrec_pull_params funs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) naryfuns) ==>
     find_recfun f naryfuns = SOME (params, body) ==>
     sound (p:'ffi ffi_proj) body (cf (p:'ffi ffi_proj) body) ==>
     fvs = MAP (\ (f,_,_). naryRecclosure env naryfuns f) naryfuns ==>
     cf (p:'ffi ffi_proj) body
       (extend_env_rec (MAP (\ (f,_,_). f) naryfuns) fvs params xvs env) H Q ==>
     app (p:'ffi ffi_proj) (naryRecclosure env naryfuns f) xvs H Q`,

  Cases_on `params` \\ rpt strip_tac \\ rw [] \\
  fs [LENGTH_CONS] \\ rfs [] \\ qpat_assum `xvs = _` (K all_tac) \\
  rename1 `extend_env_rec _ _ (n::params) (xv::xvs) _` \\
  Cases_on `params` \\ rfs [LENGTH_NIL, LENGTH_CONS] \\
  fs [extend_env_rec_def, extend_env_v_rec_def] \\
  fs [extend_env_def, extend_env_v_def, app_def]
  THEN1 (
    irule app_basic_of_sound_cf \\
    progress_then (fs o sing) do_opapp_naryRecclosure \\
    fs [naryFun_def, letrec_pull_params_names, build_rec_env_zip]
  )
  THEN1 (
    rw [] \\ rename1 `extend_env_v (n'::params) (xv'::xvs) _` \\
    fs [app_basic_def] \\ rpt strip_tac \\
    progress_then (fs o sing) do_opapp_naryRecclosure \\
    fs [SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS, SPLIT_emp2] \\
    rename1 `SPLIT _ (h, i)` \\
    `SPLIT3 (st2heap (p:'ffi ffi_proj) st) (h, {}, i)` by SPLIT_TAC \\ instantiate \\
    (* fixme *)
    qexists_tac `naryClosure
      (env with v := (n,xv)::(ZIP (MAP (\ (f,_,_). f) (letrec_pull_params funs),
        MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f)
            (letrec_pull_params funs)) ++ env.v))
      (n'::params) body` \\ strip_tac
    THEN1 (irule app_of_sound_cf \\ fs [extend_env_def])
    THEN1 (
      fs [naryFun_def, naryClosure_def, Once bigStepTheory.evaluate_cases] \\
      fs [letrec_pull_params_cancel, letrec_pull_params_names] \\
      fs [build_rec_env_zip]
    )
  )
)

val app_rec_of_sound_cf = Q.prove (
  `!f params body funs xvs env H Q.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (params, body) ==>
     sound (p:'ffi ffi_proj) body (cf (p:'ffi ffi_proj) body) ==>
     cf (p:'ffi ffi_proj) body
       (extend_env_rec
          (MAP (\ (f,_,_). f) funs)
          (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
          params xvs env)
        H Q ==>
     app (p:'ffi ffi_proj) (naryRecclosure env (letrec_pull_params funs) f) xvs H Q`,
  rpt strip_tac \\ irule app_rec_of_sound_cf_aux
  THEN1 (fs [letrec_pull_params_names])
  THEN1 (qexists_tac `funs` \\ fs [])
  THEN1 (instantiate \\ fs [letrec_pull_params_names])
)

val DROP_EL_CONS = Q.prove (
  `!l n.
    n < LENGTH l ==>
    DROP n l = EL n l :: DROP (SUC n) l`,
  Induct \\ rpt strip_tac \\ fs [] \\ every_case_tac \\ fs [] \\
  Cases_on `n` \\ fs []
)

val cf_letrec_sound_aux = Q.prove (
  `!funs e.
     let naryfuns = letrec_pull_params funs in
     (∀x. MEM x naryfuns ==>
          sound (p:'ffi ffi_proj) (SND (SND x)) (cf (p:'ffi ffi_proj) (SND (SND x)))) ==>
     sound (p:'ffi ffi_proj) e (cf (p:'ffi ffi_proj) e) ==>
     !fns rest.
       funs = rest ++ fns ==>
       let naryrest = letrec_pull_params rest in
       let naryfns = letrec_pull_params fns in
       sound (p:'ffi ffi_proj) (Letrec funs e)
         (\env H Q.
            let fvs = MAP (\ (f,_,_). naryRecclosure env naryfuns f) naryfuns in
            ALL_DISTINCT (MAP (\ (f,_,_). f) naryfuns) /\
            fundecl_rec_aux (p:'ffi ffi_proj)
              (MAP (\ (f,_,_). f) naryfuns) fvs
              (MAP (\ (_,ns,_). ns) naryfns)
              (DROP (LENGTH naryrest) fvs)
              (MAP (\x. cf (p:'ffi ffi_proj) (SND (SND x))) naryfns)
              (cf (p:'ffi ffi_proj) e) env H Q)`,

  rpt gen_tac \\ rpt (CONV_TAC let_CONV) \\ rpt DISCH_TAC \\ Induct
  THEN1 (
    rpt strip_tac \\ fs [letrec_pull_params_def, DROP_LENGTH_TOO_LONG] \\
    fs [fundecl_rec_aux_def] \\
    qpat_assum `_ = rest` (mp_tac o GSYM) \\ rw [] \\
    cf_strip_sound_full_tac \\ qpat_assum `sound _ e _` mp_tac \\
    fs [extend_env_rec_def] \\
    fs [letrec_pull_params_names, extend_env_rec_build_rec_env] \\
    rewrite_tac [sound_def] \\ disch_then progress \\ instantiate
  )
  THEN1 (
    qx_gen_tac `ftuple` \\ PairCases_on `ftuple` \\ rename1 `(f, n, body)` \\
    rpt strip_tac \\
    (* rest := rest ++ [(f,n,body)] *)
    (fn x => first_x_assum (qspec_then x mp_tac))
      `rest ++ [(f, n, body)]` \\ impl_tac THEN1 (fs []) \\ strip_tac \\
    qpat_assum `funs = _` (assume_tac o GSYM) \\ rpt (CONV_TAC let_CONV) \\
    rewrite_tac [sound_def] \\ BETA_TAC \\ rpt gen_tac \\
    qmatch_abbrev_tac `(LET _ fvs) ==> _` \\ fs [] \\
    (* unfold letrec_pull_params (_::_); extract the body/params *)
    rewrite_tac [letrec_pull_params_def] \\
    fs [Q.prove(`!opt a b c a' b' c'.
       (case opt of NONE => (a,b,c) | SOME x => (a', b', c' x)) =
       ((case opt of NONE => a | SOME x => a'),
        (case opt of NONE => b | SOME x => b'),
        (case opt of NONE => c | SOME x => c' x))`,
      rpt strip_tac \\ every_case_tac \\ fs [])] \\
    qmatch_goalsub_abbrev_tac `cf _ inner_body::_ _` \\
    qmatch_goalsub_abbrev_tac `fundecl_rec_aux _ _ _ (params::_)` \\
    (* unfold "sound _ (Letrec _ _)" in the goal *)
    cf_strip_sound_full_tac \\
    qpat_assum `fundecl_rec_aux _ _ _ _ _ _ _ _ _ _` mp_tac \\
    (* Rewrite (DROP _ _) to a (_::DROP _ _) *)
    qpat_abbrev_tac `tail = DROP _ _` \\
    `tail = (naryRecclosure env (letrec_pull_params funs) f) ::
            DROP (LENGTH (letrec_pull_params rest) + 1) fvs` by (
      qunabbrev_tac `tail` \\ rewrite_tac [GSYM ADD1] \\
      fs [letrec_pull_params_LENGTH] \\
      mp_tac (Q.ISPECL [`fvs: v list`,
                        `LENGTH (rest: (tvarN, tvarN # exp) alist)`]
              DROP_EL_CONS) \\
      impl_tac THEN1 (
        qunabbrev_tac `fvs` \\ qpat_assum `_ = funs` (assume_tac o GSYM) \\
        fs [letrec_pull_params_LENGTH]
      ) \\
      fs [] \\ strip_tac \\ qunabbrev_tac `fvs` \\
      fs [letrec_pull_params_names] \\
      qpat_abbrev_tac `naryfuns = letrec_pull_params funs` \\
      `LENGTH rest < LENGTH funs` by (
        qpat_assum `_ = funs` (assume_tac o GSYM) \\ fs []) \\
      fs [EL_MAP] \\ qpat_assum `_ = funs` (assume_tac o GSYM) \\
      fs [el_append3, ADD1]
    ) \\ fs [] \\
    (* We can now unfold fundecl_rec_aux *)
    fs [fundecl_rec_aux_def] \\ rewrite_tac [ONE] \\
    fs [LENGTH_CONS, LENGTH_NIL, PULL_EXISTS] \\
    fs [letrec_pull_params_LENGTH, letrec_pull_params_names] \\
    impl_tac
    THEN1 (
      `MEM (f, params, inner_body) (letrec_pull_params funs)` by (
         qpat_assum `_ = funs` (assume_tac o GSYM) \\
         fs [letrec_pull_params_append, letrec_pull_params_def] \\
         qunabbrev_tac `params` \\ qunabbrev_tac `inner_body` \\
         every_case_tac \\ fs []
      ) \\
      `find_recfun f (letrec_pull_params funs) = SOME (params, inner_body)` by (
        fs [evalPropsTheory.find_recfun_ALOOKUP] \\
        irule ALOOKUP_ALL_DISTINCT_MEM \\ fs [] \\
        `FST = (\ ((f:tvarN),(_:tvarN list),(_:exp)). f)` by (
          irule EQ_EXT \\ qx_gen_tac `x` \\ PairCases_on `x` \\ fs []) \\
        fs [letrec_pull_params_names]
      ) \\
      rpt strip_tac
      THEN1 (irule curried_naryRecclosure \\ fs [])
      THEN1 (
        irule app_rec_of_sound_cf \\ fs [letrec_pull_params_names] \\
        first_assum progress \\ qunabbrev_tac `params` \\ every_case_tac \\
        fs []
      )
    ) \\ strip_tac \\
    qpat_assum `sound _ (Letrec _ _) _` (mp_tac o REWRITE_RULE [sound_def]) \\
    fs [] \\ disch_then (qspecl_then [`env`, `H`, `Q`] mp_tac) \\ fs [] \\
    disch_then progress \\ instantiate \\ fs [Once bigStepTheory.evaluate_cases]
  )
)

val cf_letrec_sound = Q.prove (
  `!funs e.
    (!x. MEM x (letrec_pull_params funs) ==>
         sound (p:'ffi ffi_proj) (SND (SND x)) (cf (p:'ffi ffi_proj) (SND (SND x)))) ==>
    sound (p:'ffi ffi_proj) e (cf (p:'ffi ffi_proj) e) ==>
    sound (p:'ffi ffi_proj) (Letrec funs e)
      (\env H Q.
        let fvs = MAP
          (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f)
          funs in
        ALL_DISTINCT (MAP (\ (f,_,_). f) funs) /\
        fundecl_rec_aux (p:'ffi ffi_proj)
          (MAP (\ (f,_,_). f) funs) fvs
          (MAP (\ (_,ns,_). ns) (letrec_pull_params funs)) fvs
          (MAP (\x. cf (p:'ffi ffi_proj) (SND (SND x))) (letrec_pull_params funs))
          (cf (p:'ffi ffi_proj) e) env H Q)`,
  rpt strip_tac \\ mp_tac (Q.SPECL [`funs`, `e`] cf_letrec_sound_aux) \\
  fs [] \\ disch_then (qspecl_then [`funs`, `[]`] mp_tac) \\
  fs [letrec_pull_params_names, letrec_pull_params_def]
)

val PMATCH_EVAL_PMATCH_ROW_of_pat =
  let
    val pmatch_row_tm =
        concl PMATCH_EVAL |> rand |> lhs |> rand |> rator |> rand
    val pmatch_row_of_pat_tm =
        PMATCH_ROW_of_pat_def |> SPEC_ALL |> concl |> rhs
    val (tmsubst, tysubst) = match_term pmatch_row_tm pmatch_row_of_pat_tm
    val thm = PMATCH_EVAL |> INST_TYPE tysubst |> INST tmsubst
  in
    SPEC_ALL (REWRITE_RULE [GSYM PMATCH_ROW_of_pat_def] thm)
  end

val PMATCH_evaluate_match = store_thm ("PMATCH_evaluate_match",
  ``!v env H Q pats exps cfs branch_cf p exp st h_i h_k bind_exn_v.
      LENGTH pats = LENGTH exps ==>
      LENGTH exps = LENGTH cfs ==>
      (!s. EVERY (\pat. validate_pat env.c s pat v env.v) pats) ==>
      PMATCH (SOME v) (MAP2 (\pat cf. PMATCH_ROW_of_pat pat cf env) pats cfs) = branch_cf ==>
      branch_cf <> PMATCH_INCOMPLETE ==>
      branch_cf env H Q ==>
      EVERY2 (\exp cf. sound p exp cf) exps cfs ==>
      SPLIT (st2heap p st) (h_i, h_k) ==> H h_i ==>
      ?v' st' h_f h_g.
        bigStep$evaluate_match F env st v (ZIP (pats, exps)) bind_exn_v (st', Rval v') /\
        Q v' h_f /\ SPLIT3 (st2heap p st') (h_f, h_k, h_g)``,
  Induct_on `pats` \\ fs [] \\ rpt strip_tac
  THEN1 (
    rpt (qpat_assum `0 = LENGTH _` (assume_tac o GSYM) \\ fs [LENGTH_NIL]) \\ rw [] \\
    fs [PMATCH_def]
  ) \\

  fs [LENGTH_CONS] \\ rename1 `exps = exp::exps'` \\ rw [] \\
  fs [LENGTH_CONS] \\ rename1 `cfs = exp_cf::cfs'` \\ rw [] \\ fs [] \\
  rename1 `PMATCH_ROW_of_pat pat _ _` \\
  fs [PMATCH_def, option_case_compute] \\ full_case_tac
  THEN1 (
    first_assum (qspec_then `st.refs` strip_assume_tac) \\
    fs [validate_pat_def, IS_SOME_EXISTS] \\ fs [THE_DEF] \\
    fs [Once bigStepTheory.evaluate_cases] \\
    progress_then (qspec_then `st.refs` strip_assume_tac) PMATCH_ROW_pmatch \\
    fs [] \\ qpat_assum `sound _ _ exp_cf` (progress o REWRITE_RULE [sound_def]) \\
    instantiate
  )
  THEN1 (
    fs [NOT_IS_SOME_EQ_NONE] \\
    first_assum (qspec_then `st.refs` assume_tac) \\
    fs [validate_pat_def, pat_typechecks_def] \\
    mp_tac (fst (CONJ_PAIR PMATCH_ROW_pmatch_nomatch)
            |> INST_TYPE [alpha |-> ``:hprop -> (v -> hprop) -> bool``]) \\ (* ? *)
    disch_then progress \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    first_assum irule \\ fs [] \\ instantiate
  )
)

val cf_sound = store_thm ("cf_sound",
  ``!p e. sound (p:'ffi ffi_proj) e (cf (p:'ffi ffi_proj) e)``,
  recInduct cf_ind \\ rpt strip_tac \\
  rewrite_tac cf_defs \\ fs [sound_local, sound_false]
  THEN1 (* Lit *) cf_base_case_tac
  THEN1 (
    (* Con *)
    cf_base_case_tac \\ fs [PULL_EXISTS, st2heap_def] \\
    progress exp2v_list_REVERSE \\ Q.LIST_EXISTS_TAC [`cv`, `REVERSE argsv`] \\
    fs []
  )
  THEN1 (* Var *) cf_base_case_tac
  THEN1 (
    (* Let *)
    Cases_on `is_bound_Fun opt e1` \\ fs []
    THEN1 (
      (* function declaration *)
      (* Eliminate the impossible case (Fun_body _ = NONE), then we call
        cf_strip_sound_tac *)
      progress is_bound_Fun_unfold \\ fs [Fun_body_def] \\
      BasicProvers.TOP_CASE_TAC \\ cf_strip_sound_tac \\
      (* Instantiate the hypothesis with the closure *)
      rename1 `(case Fun_body _ of _ => _) = SOME inner_body` \\
      (fn tm => first_x_assum (qspec_then tm mp_tac))
        `naryClosure env (Fun_params (Fun n body)) inner_body` \\
      impl_tac \\ strip_tac
      THEN1 (irule curried_naryClosure \\ fs [Fun_params_def])
      THEN1 (fs [Fun_params_def, app_of_sound_cf]) \\
      qpat_assum `sound _ e2 _` (progress o REWRITE_RULE [sound_def]) \\
      cf_evaluate_step_tac \\ Cases_on `opt` \\
      fs [is_bound_Fun_def, SOME_val_def, Fun_params_def] \\ instantiate \\
      every_case_tac \\ qpat_assum `_ = inner_body` (assume_tac o GSYM) \\
      fs [naryClosure_def, naryFun_def, Fun_params_Fun_body_NONE,
          Fun_params_Fun_body_repack, Once bigStepTheory.evaluate_cases]
    )
    THEN1 (
      (* other cases of let-binding *)
      cf_strip_sound_full_tac \\
      qpat_assum `sound _ e1 _` (progress o REWRITE_RULE [sound_def]) \\
      first_assum (qspec_then `v` assume_tac) \\
      `SPLIT (st2heap (p:'ffi ffi_proj) st') (h_f, h_k UNION h_g)` by SPLIT_TAC \\
      qpat_assum `sound _ e2 _` (progress o REWRITE_RULE [sound_def]) \\
      `SPLIT3 (st2heap (p:'ffi ffi_proj) st'') (h_f',h_k, h_g UNION h_g')` by SPLIT_TAC \\
      instantiate
    )
  )
  THEN1 (
    (* Letrec *)
    HO_MATCH_MP_TAC sound_local \\
    mp_tac (Q.SPECL [`funs`, `e`] cf_letrec_sound) \\
    fs [letrec_pull_params_LENGTH, letrec_pull_params_names] \\
    rewrite_tac [sound_def] \\ rpt strip_tac \\ fs [] \\
    first_assum (qspecl_then [`env`, `H`, `Q`] assume_tac) \\
    (fn x => first_assum (qspec_then x assume_tac))
      `MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs` \\
    fs [letrec_pull_params_LENGTH] \\ res_tac \\ instantiate
  )
  THEN1 (
    (* App *)
    Cases_on `op` \\ fs [] \\ TRY (MATCH_ACCEPT_TAC sound_local_false) \\
    (every_case_tac \\ TRY (MATCH_ACCEPT_TAC sound_local_false)) \\
    cf_strip_sound_tac \\
    (rename1 `(App Opapp _)` ORELSE cf_evaluate_step_tac) \\
    TRY (
      (* Opn & Opb *)
      (rename1 `app_opn op` ORELSE rename1 `app_opb op`) \\
      fs [app_opn_def, app_opb_def, st2heap_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      GEN_EXISTS_TAC "vs" `[Litv (IntLit i2); Litv (IntLit i1)]` \\
      Cases_on `op` \\ fs [do_app_def] \\
      qexists_tac `st` \\ rpt strip_tac \\ fs [SEP_IMP_def] \\
      cf_evaluate_list_tac [`st`, `st`]
    )
    THEN1 (
      (* Opapp *)
      rename1 `dest_opapp _ = SOME (f, xs)` \\
      schneiderUtils.UNDISCH_ALL_TAC \\ SPEC_ALL_TAC \\
      CONV_TAC (RESORT_FORALL_CONV (fn l =>
        (op @) (partition (fn v => fst (dest_var v) = "xs") l))) \\
      gen_tac \\ completeInduct_on `LENGTH xs` \\ rpt strip_tac \\
      fs [] \\ qpat_assum `dest_opapp _ = _` mp_tac \\
      rewrite_tac [dest_opapp_def] \\ every_case_tac \\ fs [] \\
      rpt strip_tac \\ qpat_assum `_ = xs` (assume_tac o GSYM) \\ fs []
      (* 1 argument *)
      THEN1 (
        rename1 `xs = [x]` \\ fs [exp2v_list_def] \\ full_case_tac \\ fs [] \\
        qpat_assum `_ = argsv` (assume_tac o GSYM) \\ rename1 `argsv = [xv]` \\
        cf_evaluate_step_tac \\ GEN_EXISTS_TAC "vs" `[xv; fv]` \\
        fs [app_def, app_basic_def] \\ res_tac \\
        rename1 `SPLIT3 (st2heap _ st') (h_f, h_g, h_k)` \\
        progress SPLIT3_swap23 \\ instantiate \\
        cf_evaluate_list_tac [`st`, `st`]
      )
      (* 2+ arguments *)
      THEN1 (
        rename1 `dest_opapp papp_ = SOME (f, pxs)` \\
        rename1 `xs = pxs ++ [x]` \\ fs [LENGTH] \\
        progress exp2v_list_rcons \\ fs [] \\
        (* Do some unfolding, by definition of dest_opapp *)
        `?papp. papp_ = App Opapp papp` by (
          Cases_on `papp_` \\ TRY (fs [dest_opapp_def] \\ NO_TAC) \\
          rename1 `dest_opapp (App op _)` \\
          Cases_on `op` \\ TRY (fs [dest_opapp_def] \\ NO_TAC)
        ) \\ fs [] \\
        (* Prepare for, and apply lemma [app_alt_ind_w] to split app *)
        progress dest_opapp_not_empty_arglist \\
        `xvs <> []` by (progress exp2v_list_LENGTH \\ strip_tac \\
                       first_assum irule \\ fs [LENGTH_NIL]) \\
        progress app_alt_ind_w \\
        (* Specialize induction hypothesis with xs := pxs *)
        `LENGTH pxs < LENGTH pxs + 1` by (fs []) \\
        last_assum drule \\ disch_then (qspec_then `pxs` mp_tac) \\ fs [] \\
        disch_then progress \\ fs [SEP_EXISTS, cond_def, STAR_def] \\
        (* Cleanup *)
        rename1 `app_basic _ g xv H' Q` \\ fs [SPLIT_emp2] \\
        (* Start unfolding the goal and instantiating exists *)
        cf_evaluate_step_tac \\ GEN_EXISTS_TAC "vs" `[xv; g]` \\
        GEN_EXISTS_TAC "s2" `st'` \\ progress SPLIT_of_SPLIT3_2u3 \\ rw [] \\
        (* Exploit the [app_basic (p:'ffi ffi_proj) g xv H' Q] we got from the ind. hyp. *)
        fs [app_basic_def] \\ first_assum progress \\
        (* Prove the goal *)
        rename1 `SPLIT3 (st2heap _ st'') (h_f', h_g', _)` \\
        `SPLIT3 (st2heap (p:'ffi ffi_proj) st'') (h_f', h_k, h_g' UNION h_g)` by SPLIT_TAC
        \\ instantiate \\ cf_evaluate_list_tac [`st`, `st'`]
      )
    )
    THEN1 (
      (* Opassign *)
      fs [app_assign_def, SEP_IMP_def,STAR_def,cell_def,one_def] \\
      `evaluate_list F env st [h'; h] (st, Rval [xv; Loc rv])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\ instantiate \\
      first_assum progress \\
      rename1 `SPLIT h_i (h_i', _)` \\ rename1 `FF h_i'` \\
      fs [do_app_def, store_assign_def] \\
      `Mem rv (Refv x') IN (st2heap p st)` by SPLIT_TAC \\
      `Mem rv (Refv x') IN (store2heap st.refs)` by
          fs [st2heap_def,Mem_NOT_IN_ffi2heap] \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      `store_v_same_type (EL rv st.refs) (Refv xv)` by
        (fs [store_v_same_type_def]) \\ fs [] \\
      `SPLIT3 (store2heap (LUPDATE (Refv xv) rv st.refs) ∪ ffi2heap p st.ffi)
         (Mem rv (Refv xv) INSERT h_i', h_k, {})` by
       (progress_then (fs o sing) store2heap_LUPDATE \\
        drule store2heap_IN_unique_key \\
        fs [st2heap_def,SPLIT3_def,SPLIT_def] \\ rw [] \\
        assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\ SPLIT_TAC)
      \\ fs [st2heap_def]
      \\ instantiate \\ first_assum irule \\ instantiate
      \\ drule store2heap_IN_unique_key \\ rw []
      \\ `!x y. Mem x y IN h_i ==> Mem x y IN store2heap st.refs` by
       (rw [] \\ CCONTR_TAC \\ fs [] \\ fs [SPLIT_def,EXTENSION]
        \\ metis_tac [Mem_NOT_IN_ffi2heap])
      \\ SPLIT_TAC)
    THEN1 (
      (* Opref *)
      fs [do_app_def, store_alloc_def] \\
      fs [st2heap_def, app_ref_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      `evaluate_list F env st [h] (st, Rval [xv])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\ instantiate \\
      (fn l => first_x_assum (qspecl_then l mp_tac))
        [`LENGTH st.refs`, `Mem (LENGTH st.refs)(Refv xv) INSERT h_i`] \\
      assume_tac store2heap_alloc_disjoint \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      impl_tac
      THEN1 (qexists_tac `h_i` \\ SPLIT_TAC)
      THEN1 (
        strip_tac \\ instantiate \\ fs [store2heap_append] \\
        qexists_tac `{}` \\ SPLIT_TAC
      )
    )
    THEN1 (
      (* Opderef *)
      `evaluate_list F env st [h] (st, Rval [Loc rv])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_deref_def, SEP_IMP_def,STAR_def,one_def,cell_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\
      fs [do_app_def, store_lookup_def] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      `Mem rv (Refv x) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\ fs []
    )
    THEN1 (
      (* Aw8alloc *)
      `evaluate_list F env st [h'; h] (st, Rval [Litv (Word8 w); Litv (IntLit n)])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\ instantiate \\
      fs [do_app_def, store_alloc_def, st2heap_def, app_aw8alloc_def] \\
      fs [SEP_IMP_def, STAR_def, one_def, cell_def] \\
      first_x_assum (qspecl_then [`LENGTH st.refs`] strip_assume_tac) \\
      (fn l => first_x_assum (qspecl_then l mp_tac))
        [`Mem (LENGTH st.refs) (W8array (REPLICATE (Num (ABS n)) w)) INSERT h_i`] \\
      assume_tac store2heap_alloc_disjoint \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      impl_tac
      THEN1 (instantiate \\ SPLIT_TAC)
      THEN1 (
        rpt strip_tac \\ every_case_tac \\
        rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) [] \\ instantiate \\
        fs [store2heap_append] \\ qexists_tac `{}` \\ SPLIT_TAC
      )
    )
    THEN1 (
      (* Aw8sub *)
      `evaluate_list F env st [h'; h] (st, Rval [Litv (IntLit i); Loc l])`
        by (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_aw8sub_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      fs [do_app_def, store_lookup_def] \\
      `Mem l (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\ fs [] \\
      instantiate \\ every_case_tac \\
      rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) []
    )
    THEN1 (
      (* Aw8length *)
      `evaluate_list F env st [h] (st, Rval [Loc l])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_aw8length_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\
      fs [do_app_def, store_lookup_def] \\
      `Mem l (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\ fs []
    )
    THEN1 (
      (* Aw8update *)
      `evaluate_list F env st [h''; h'; h]
         (st, Rval [Litv (Word8 w); Litv (IntLit i); Loc l])`
          by (cf_evaluate_list_tac [`st`, `st`, `st`]) \\ instantiate \\
      fs [app_aw8update_def, SEP_IMP_def, STAR_def, one_def, cell_def, st2heap_def] \\
      first_x_assum progress \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      `Mem l (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [do_app_def, store_lookup_def, store_assign_def, store_v_same_type_def] \\
      every_case_tac \\ rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) [] \\
      qexists_tac `Mem l (W8array (LUPDATE w (Num (ABS i)) ws)) INSERT u` \\
      qexists_tac `{}` \\ mp_tac store2heap_IN_unique_key \\ rpt strip_tac
      THEN1 (first_assum irule \\ instantiate \\ SPLIT_TAC)
      THEN1 (progress_then (fs o sing) store2heap_LUPDATE \\ SPLIT_TAC)
    )
    THEN1 (
      (* Aalloc *)
      `evaluate_list F env st [h'; h] (st, Rval [v; Litv (IntLit n)])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\ instantiate \\
      fs [do_app_def, store_alloc_def, st2heap_def, app_aalloc_def] \\
      fs [SEP_IMP_def, STAR_def, one_def, cell_def] \\
      first_x_assum (qspecl_then [`LENGTH st.refs`] strip_assume_tac) \\
      (fn l => first_x_assum (qspecl_then l mp_tac))
        [`Mem (LENGTH st.refs) (Varray (REPLICATE (Num (ABS n)) v)) INSERT h_i`] \\
      assume_tac store2heap_alloc_disjoint \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      impl_tac
      THEN1 (instantiate \\ SPLIT_TAC)
      THEN1 (
        rpt strip_tac \\ every_case_tac \\
        rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) [] \\ instantiate \\
        fs [store2heap_append] \\ qexists_tac `{}` \\ SPLIT_TAC
      )
    )
    THEN1 (
      (* Asub *)
      `evaluate_list F env st [h'; h] (st, Rval [Litv (IntLit i); Loc l])`
        by (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_asub_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      fs [do_app_def, store_lookup_def] \\
      `Mem l (Varray vs) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\ fs [] \\
      instantiate \\ every_case_tac \\
      rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) []
    )
    THEN1 (
      (* Alength *)
      `evaluate_list F env st [h] (st, Rval [Loc l])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_alength_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\
      fs [do_app_def, store_lookup_def] \\
      `Mem l (Varray vs) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\ fs []
    )
    THEN1 (
      (* Aupdate *)
      `evaluate_list F env st [h''; h'; h]
         (st, Rval [v; Litv (IntLit i); Loc l])`
          by (cf_evaluate_list_tac [`st`, `st`, `st`]) \\ instantiate \\
      fs [app_aupdate_def, SEP_IMP_def, STAR_def, one_def, cell_def, st2heap_def] \\
      first_x_assum progress \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      `Mem l (Varray vs) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [do_app_def, store_lookup_def, store_assign_def, store_v_same_type_def] \\
      every_case_tac \\ rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) [] \\
      qexists_tac `Mem l (Varray (LUPDATE v (Num (ABS i)) vs)) INSERT u` \\
      qexists_tac `{}` \\ mp_tac store2heap_IN_unique_key \\ rpt strip_tac
      THEN1 (first_assum irule \\ instantiate \\ SPLIT_TAC)
      THEN1 (progress_then (fs o sing) store2heap_LUPDATE \\ SPLIT_TAC)
    )
  )
  THEN1 (
    (* Mat *)
    cf_strip_sound_full_tac \\
    `evaluate F env st e (st, Rval v)` by (fs [exp2v_evaluate]) \\
    instantiate \\
    `branches = ZIP (MAP FST branches, MAP SND branches)`
      by (fs [GSYM UNZIP_MAP, ZIP_UNZIP]) \\ pop_assum (fs o sing o Once) \\
    fs [GSYM CONJ_ASSOC] \\ irule PMATCH_evaluate_match \\ fs [MAP_ZIP] \\
    GEN_EXISTS_TAC "cfs" `MAP (\b. cf p (SND b)) branches` \\
    fs [MAP2_ZIP] \\ instantiate \\ rpt strip_tac \\
    try_finally (
      Induct_on `branches` \\ fs [] \\ rpt strip_tac \\
      fs [PMATCH_EVAL_PMATCH_ROW_of_pat] \\ every_case_tac \\ fs []
    )
    THEN1 (
      fs [LIST_REL_EVERY_ZIP] \\ fs [EVERY_MEM, MEM_ZIP] \\ rpt strip_tac \\
      rename1 `_ exp_cf_pair` \\ Cases_on `exp_cf_pair` \\
      fs [EL_MAP] \\ first_assum irule \\ instantiate \\ fs [EL_MAP]
    )
  )
)

val cf_sound' = store_thm ("cf_sound'",
  ``!e env H Q st.
     cf (p:'ffi ffi_proj) e env H Q ==> H (st2heap (p:'ffi ffi_proj) st) ==>
     ?st' h_f h_g v.
       evaluate F env st e (st', Rval v) /\
       SPLIT (st2heap (p:'ffi ffi_proj) st') (h_f, h_g) /\
       Q v h_f``,
  rpt strip_tac \\ qspecl_then [`(p:'ffi ffi_proj)`, `e`] assume_tac cf_sound \\
  fs [sound_def] \\
  `SPLIT (st2heap p st) (st2heap p st, {})` by SPLIT_TAC \\
  res_tac \\ rename1 `SPLIT3 (st2heap p st') (h_f, {}, h_g)` \\
  `SPLIT (st2heap p st') (h_f, h_g)` by SPLIT_TAC \\ instantiate
)

val cf_sound_local = store_thm ("cf_sound_local",
  ``!e env H Q h i st.
     cf (p:'ffi ffi_proj) e env H Q ==>
     SPLIT (st2heap (p:'ffi ffi_proj) st) (h, i) ==>
     H h ==>
     ?st' h' g v.
       evaluate F env st e (st', Rval v) /\
       SPLIT3 (st2heap (p:'ffi ffi_proj) st') (h', g, i) /\
       Q v h'``,
  rpt strip_tac \\
  `sound (p:'ffi ffi_proj) e (\env. (local (cf (p:'ffi ffi_proj) e env)))` by
    (match_mp_tac sound_local \\ fs [cf_sound]) \\
  fs [sound_def, st2heap_def] \\
  `local (cf (p:'ffi ffi_proj) e env) H Q` by
    (fs [REWRITE_RULE [is_local_def] cf_local |> GSYM]) \\
  res_tac \\ progress SPLIT3_swap23 \\ instantiate
)

val app_basic_of_cf = store_thm ("app_basic_of_cf",
  ``!clos body x env env' v H Q.
     do_opapp [clos; x] = SOME (env', body) ==>
     cf (p:'ffi ffi_proj) body env' H Q ==>
     app_basic (p:'ffi ffi_proj) clos x H Q``,
  fs [app_basic_of_sound_cf, cf_sound]
)

val app_of_cf = store_thm ("app_of_cf",
  ``!ns env body xvs env' H Q.
     ns <> [] ==>
     LENGTH xvs = LENGTH ns ==>
     cf (p:'ffi ffi_proj) body (extend_env ns xvs env) H Q ==>
     app (p:'ffi ffi_proj) (naryClosure env ns body) xvs H Q``,
  fs [app_of_sound_cf, cf_sound]
)

val app_rec_of_cf = store_thm ("app_rec_of_cf",
  ``!f params body funs xvs env H Q.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (params, body) ==>
     cf (p:'ffi ffi_proj) body
       (extend_env_rec
          (MAP (\ (f,_,_). f) funs) 
          (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
          params xvs env)
        H Q ==>
     app (p:'ffi ffi_proj) (naryRecclosure env (letrec_pull_params funs) f) xvs H Q``,
  fs [app_rec_of_sound_cf, cf_sound]
)

val _ = export_theory()
