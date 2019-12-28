(*
  Defines the characteristic formula (CF) function cf_def and proves
  that it is sound w.r.t. the evaluate semantics of CakeML.
*)
open preamble
open set_sepTheory helperLib ml_translatorTheory ConseqConv
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib

val _ = new_theory "cf"

val _ = set_grammar_ancestry
  ["cfHeapsBase","cfHeaps","cfStore","cfNormalise","cfApp",
   "ml_translator", "ffi"];

val _ = monadsyntax.temp_disable_monadsyntax()

(*------------------------------------------------------------------*)
(* Characteristic formula for not-implemented or impossible cases *)

val cf_bottom_def = Define `
  cf_bottom = \env. local (\H Q. F)`

(*------------------------------------------------------------------*)
(* Machinery for dealing with n-ary applications/functions in cf.

   Applications and ((mutually)recursive)functions are unary in
   CakeML's AST.
   Some machinery is therefore needed to walk down the AST and extract
   multiple arguments (for an application), or multiple parameters and
   the final function body (for functions).
*)

(** 1) n-ary applications *)

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

Theorem letrec_pull_params_names:
   !funs P.
     MAP (\ (f,_,_). P f) (letrec_pull_params funs) =
     MAP (\ (f,_,_). P f) funs
Proof
  Induct \\ fs [letrec_pull_params_def] \\ rpt strip_tac \\
  rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs []
QED

Theorem letrec_pull_params_LENGTH:
   !funs. LENGTH (letrec_pull_params funs) = LENGTH funs
Proof
  Induct \\ fs [letrec_pull_params_def] \\ rpt strip_tac \\
  rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs []
QED

Theorem letrec_pull_params_append:
   !l l'.
     letrec_pull_params (l ++ l') =
     letrec_pull_params l ++ letrec_pull_params l'
Proof
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def] \\
  rename1 `ftuple::_` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_def]
QED

Theorem letrec_pull_params_cancel:
   !funs.
     MAP (\ (f,ns,body). (f, HD ns, naryFun (TL ns) body))
         (letrec_pull_params funs) =
     funs
Proof
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def] \\
  rename1 `ftuple::_` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  fs [Fun_params_Fun_body_repack]
QED

Theorem letrec_pull_params_nonnil_params:
   !funs f ns body.
     MEM (f,ns,body) (letrec_pull_params funs) ==>
     ns <> []
Proof
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def, MEM] \\
  rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  rename1 `(f',n',body')::funs` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  metis_tac []
QED

Theorem find_recfun_letrec_pull_params:
   !funs f n ns body.
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     find_recfun f funs = SOME (n, naryFun ns body)
Proof
  Induct \\ fs [letrec_pull_params_def]
  THEN1 (fs [Once find_recfun_def]) \\
  rpt strip_tac \\ rename1 `ftuple::funs` \\ PairCases_on `ftuple` \\
  rename1 `(f',n',body')` \\ fs [letrec_pull_params_def] \\
  every_case_tac \\ pop_assum mp_tac \\
  once_rewrite_tac [find_recfun_def] \\ fs [] \\
  every_case_tac \\ rw [] \\ fs [naryFun_def, Fun_params_Fun_body_repack]
QED

(*------------------------------------------------------------------*)
(* The semantic counterpart of n-ary functions: n-ary closures

   Also, dealing with environments.
*)

(* [naryClosure] *)
val naryClosure_def = Define `
  naryClosure env (n::ns) body = Closure env n (naryFun ns body)`

(* Properties of [naryClosure] *)

val with_clock_clock = Q.prove(
  `(s with clock := k).clock = k`,
  EVAL_TAC);
val with_clock_with_clock = Q.prove(
  `((s with clock := k1) with clock := k2) = s with clock := k2`,
  EVAL_TAC);
val with_clock_self = Q.prove(
  `(s with clock := s.clock) = s`,
  fs [state_component_equality]);
val with_clock_self_eq = Q.prove(
  `!ck. (s with clock := ck) = s <=> ck = s.clock`,
  fs [state_component_equality]);

val evaluate_to_heap_with_clock = prove(
  ``evaluate_to_heap (st with clock := ck) = evaluate_to_heap st``,
  fs [evaluate_to_heap_def,FUN_EQ_THM,evaluate_ck_def]);

Theorem app_one_naryClosure:
   !env n ns x xs body H Q.
     ns <> [] ==> xs <> [] ==>
     app (p:'ffi ffi_proj) (naryClosure env (n::ns) body) (x::xs) H Q ==>
     app (p:'ffi ffi_proj) (naryClosure (env with v := nsBind n x env.v) ns body) xs H Q
Proof
  rpt strip_tac \\ Cases_on `ns` \\ Cases_on `xs` \\ fs [] \\
  rename1 `app _ (naryClosure _ (n::n'::ns) _) (x::x'::xs) _ _` \\
  Cases_on `xs` THENL [all_tac, rename1 `_::_::x''::xs`] \\
  fs [app_def, naryClosure_def, naryFun_def] \\
  fs [app_basic_def] \\ rpt strip_tac \\ first_x_assum progress \\
  Cases_on `r` \\ fs [POSTv_def, cond_def] \\
  pop_assum mp_tac \\
  simp [Once evaluate_to_heap_def] \\
  strip_tac \\ rveq \\ fs [] \\
  fs [SEP_EXISTS, cond_def, STAR_def, SPLIT_emp2, PULL_EXISTS] \\
  qpat_x_assum `do_opapp _ = _` (assume_tac o REWRITE_RULE [do_opapp_def]) \\
  fs [] \\ qpat_x_assum `Fun _ _ = _` (assume_tac o GSYM) \\ fs [] \\
  fs [evaluate_ck_def, terminationTheory.evaluate_def] \\ rw [] \\
  fs [do_opapp_def] \\
  progress SPLIT_of_SPLIT3_2u3 \\ first_x_assum progress \\
  once_rewrite_tac [CONJ_COMM] \\
  asm_exists_tac \\ fs [evaluate_to_heap_with_clock] \\
  asm_exists_tac \\ fs [evaluate_to_heap_with_clock] \\
  rename1 `SPLIT3 heap1 (h_f', h_k UNION h_g, h_g')` \\
  `SPLIT3 heap1 (h_f', h_k, h_g UNION h_g')`
    by SPLIT_TAC \\
  asm_exists_tac \\ fs []
QED

Theorem curried_naryClosure:
   !env len ns body.
     ns <> [] ==> len = LENGTH ns ==>
     curried (p:'ffi ffi_proj) len (naryClosure env ns body)
Proof
  Induct_on `ns` \\ fs [naryClosure_def, naryFun_def] \\ Cases_on `ns`
  THEN1 (once_rewrite_tac [ONE] \\ fs [Once curried_def]) \\
  rpt strip_tac \\ fs [naryClosure_def, naryFun_def] \\
  rw [Once curried_def] \\ fs [app_basic_def] \\ rpt strip_tac \\
  fs [emp_def, cond_def, do_opapp_def, POSTv_def,evaluate_to_heap_def] \\
  rename1 `SPLIT (st2heap _ st) ({}, h_k)` \\
  `SPLIT3 (st2heap (p:'ffi ffi_proj) st) ({}, h_k, {})` by SPLIT_TAC \\
  instantiate \\ rename1 `nsBind n x  _` \\
  first_x_assum (qspecl_then [`env with v := nsBind n x env.v`, `body`]
    assume_tac) \\
  qmatch_assum_abbrev_tac `curried _ _ v` \\ qexists_tac `Val v` \\
  qunabbrev_tac `v` \\ fs [] \\
  fs [evaluate_ck_def, terminationTheory.evaluate_def] \\
  fs [LENGTH_CONS, PULL_EXISTS] \\
  qexists_tac `st.clock` \\ fs [with_clock_self] \\
  fs [GSYM naryFun_def, GSYM naryClosure_def] \\ rpt strip_tac \\
  irule app_one_naryClosure \\ fs []
QED

(* [naryRecclosure] *)
val naryRecclosure_def = Define `
  naryRecclosure env naryfuns f =
    Recclosure env
    (MAP (\ (f, ns, body). (f, HD ns, naryFun (TL ns) body)) naryfuns)
    f`;

(* Properties of [naryRecclosure] *)

Theorem do_opapp_naryRecclosure:
   !funs f n ns body x env env' exp.
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     (do_opapp [naryRecclosure env (letrec_pull_params funs) f; x] =
      SOME (env', exp)
     <=>
     (ALL_DISTINCT (MAP (\ (f,_,_). f) funs) /\
      env' = (env with v := nsBind n x (build_rec_env funs env env.v)) /\
      exp = naryFun ns body))
Proof
  rpt strip_tac \\ progress find_recfun_letrec_pull_params \\
  fs [naryRecclosure_def, do_opapp_def, letrec_pull_params_cancel] \\
  eq_tac \\ every_case_tac \\ fs []
QED

Theorem app_one_naryRecclosure:
   !funs f n ns body x xs env H Q.
     ns <> [] ==> xs <> [] ==>
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     (app (p:'ffi ffi_proj) (naryRecclosure env (letrec_pull_params funs) f) (x::xs) H Q ==>
      app (p:'ffi ffi_proj)
        (naryClosure
          (env with v := nsBind n x (build_rec_env funs env env.v))
          ns body) xs H Q)
Proof
  rpt strip_tac \\ Cases_on `ns` \\ Cases_on `xs` \\ fs [] \\
  rename1 `SOME (n::n'::ns, _)` \\ rename1 `app _ _ (x::x'::xs)` \\
  Cases_on `xs` THENL [all_tac, rename1 `_::_::x''::xs`] \\
  fs [app_def, naryClosure_def, naryFun_def] \\
  fs [app_basic_def] \\
  rpt strip_tac \\ first_x_assum progress \\
  Cases_on `r` \\ fs [POSTv_def, SEP_EXISTS, cond_def, STAR_def, SPLIT_emp2] \\
  pop_assum mp_tac \\
  simp [Once evaluate_to_heap_def] \\ rw [] \\ rveq \\ fs [] \\
  progress_then (fs o sing) do_opapp_naryRecclosure \\ rw [] \\
  fs [naryFun_def, evaluate_ck_def, terminationTheory.evaluate_def] \\ rw [] \\
  fs [do_opapp_def] \\ progress SPLIT_of_SPLIT3_2u3 \\ first_x_assum progress \\
  fs [evaluate_to_heap_with_clock] \\
  once_rewrite_tac [CONJ_COMM] \\
  asm_exists_tac \\ fs [evaluate_to_heap_with_clock] \\
  asm_exists_tac \\ fs [evaluate_to_heap_with_clock] \\
  rename1 `SPLIT3 heap1 (h_f', h_k UNION h_g, h_g')` \\
  `SPLIT3 heap1 (h_f', h_k, h_g UNION h_g')`
    by SPLIT_TAC \\
  asm_exists_tac \\ fs []
QED

Theorem curried_naryRecclosure:
   !env funs f len ns body.
     ALL_DISTINCT (MAP (\ (f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (ns, body) ==>
     len = LENGTH ns ==>
     curried (p:'ffi ffi_proj) len (naryRecclosure env (letrec_pull_params funs) f)
Proof
  rpt strip_tac \\ Cases_on `ns` \\ fs []
  THEN1 (
    fs [curried_def, semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] \\
    progress ALOOKUP_MEM \\ progress letrec_pull_params_nonnil_params \\ fs []
  ) \\
  rename1 `n::ns` \\ Cases_on `ns` \\ fs [Once curried_def] \\
  rename1 `n::n'::ns` \\ strip_tac \\ fs [app_basic_def] \\ rpt strip_tac \\
  fs [POSTv_def, emp_def, cond_def, evaluate_to_heap_def] \\
  progress_then (fs o sing) do_opapp_naryRecclosure \\ rw [] \\
  qexists_tac
    `Val (naryClosure (env with v := nsBind n x (build_rec_env funs env env.v))
                      (n'::ns) body)` \\
  simp [PULL_EXISTS] \\
  Q.LIST_EXISTS_TAC [`{}`, `st.clock`, `st`] \\ simp [] \\ rpt strip_tac
  THEN1 SPLIT_TAC
  THEN1 (irule curried_naryClosure \\ fs [])
  THEN1 (irule app_one_naryRecclosure \\ fs [LENGTH_CONS] \\ metis_tac []) \\
  fs [naryFun_def, naryClosure_def] \\
  fs [evaluate_ck_def, terminationTheory.evaluate_def, with_clock_self]
QED

Theorem letrec_pull_params_repack:
   !funs f env.
     naryRecclosure env (letrec_pull_params funs) f =
     Recclosure env funs f
Proof
  Induct \\ rpt strip_tac \\ fs [naryRecclosure_def, letrec_pull_params_def] \\
  rename1 `ftuple::_` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  fs [Fun_params_Fun_body_repack]
QED

(** Extending environments *)

(* TODO: there's a version of this already defined ...*)
(* [extend_env] *)
val extend_env_v_def = Define `
  extend_env_v [] [] env_v = env_v /\
  extend_env_v (n::ns) (xv::xvs) env_v =
    extend_env_v ns xvs (nsBind n xv env_v)`;

val extend_env_def = Define `
  extend_env ns xvs (env:'v sem_env) = (env with v := extend_env_v ns xvs env.v)`;

Theorem extend_env_v_rcons:
   !ns xvs n xv env_v.
     LENGTH ns = LENGTH xvs ==>
     extend_env_v (ns ++ [n]) (xvs ++ [xv]) env_v =
     nsBind n xv (extend_env_v ns xvs env_v)
Proof
  Induct \\ rpt strip_tac \\ first_assum (assume_tac o GSYM) \\
  fs [LENGTH_NIL, LENGTH_CONS, extend_env_v_def]
QED

Theorem extend_env_v_zip:
   !ns xvs env_v.
    LENGTH ns = LENGTH xvs ==>
    extend_env_v ns xvs env_v = nsAppend (alist_to_ns (ZIP (REVERSE ns, REVERSE xvs))) env_v
Proof
  Induct \\ rpt strip_tac \\ first_assum (assume_tac o GSYM) \\
  fs [LENGTH_NIL, LENGTH_CONS, extend_env_v_def, GSYM ZIP_APPEND] \\
  FULL_SIMP_TAC std_ss [Once (GSYM namespacePropsTheory.nsAppend_alist_to_ns),Once (GSYM (namespacePropsTheory.nsAppend_assoc))] \\
  Cases_on`env_v`>> EVAL_TAC
QED

(* [build_rec_env_aux] *)
val build_rec_env_aux_def = Define `
  build_rec_env_aux funs (fs: (tvarN, tvarN # exp) alist) env add_to_env =
    FOLDR
      (\ (f,x,e) env'. nsBind f (Recclosure env funs f) env')
      add_to_env
      fs`;

val build_rec_env_zip_aux = Q.prove (
  `!(fs: (tvarN, tvarN # exp) alist) funs env env_v.
    nsAppend
    (alist_to_ns
      (ZIP (MAP (\ (f,_,_). f) fs,
         MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) fs)))
      env_v =
    FOLDR (\ (f,x,e) env'. nsBind f (Recclosure env funs f) env') env_v fs`,
  Induct \\ rpt strip_tac THEN1 (fs []) \\
  rename1 `ftuple::fs` \\ PairCases_on `ftuple` \\ rename1 `(f,n,body)` \\
  fs [letrec_pull_params_repack]
);

Theorem build_rec_env_zip:
   !funs env env_v.
     nsAppend
     (alist_to_ns
       (ZIP (MAP (\ (f,_,_). f) funs,
          MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)))
       env_v =
     build_rec_env funs env env_v
Proof
  fs [build_rec_env_def, build_rec_env_zip_aux]
QED

(* [extend_env_rec] *)
val extend_env_v_rec_def = Define `
  extend_env_v_rec rec_ns rec_xvs ns xvs env_v =
    extend_env_v ns xvs (nsAppend (alist_to_ns (ZIP (rec_ns, rec_xvs))) env_v)`;

val extend_env_rec_def = Define `
  extend_env_rec rec_ns rec_xvs ns xvs (env:'v sem_env) =
    env with v := extend_env_v_rec rec_ns rec_xvs ns xvs env.v`;

Theorem extend_env_rec_build_rec_env:
   !funs env env_v.
     extend_env_v_rec
       (MAP (\ (f,_,_). f) funs)
       (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
       [] [] env_v =
     build_rec_env funs env env_v
Proof
  rpt strip_tac \\ fs [extend_env_v_rec_def, extend_env_v_def, build_rec_env_zip]
QED

(*------------------------------------------------------------------*)
(** Pattern matching.

    Restrictions:
    - the CakeML pattern-matching must "typecheck" (does not raise
      Match_type_error)
    - patterns that use [Pref] are not currently supported
*)

val pat_bindings_def = astTheory.pat_bindings_def
val pmatch_def = terminationTheory.pmatch_def
val pmatch_ind = terminationTheory.pmatch_ind

(* [pat_wildcards]: computes the number of wildcards a pattern contains. *)

val pat_wildcards_def = tDefine "pat_wildcards" `
  pat_wildcards Pany = 1n /\
  pat_wildcards (Pvar _) = 0n /\
  pat_wildcards (Plit _) = 0n /\
  pat_wildcards (Pref _) = 0n /\
  pat_wildcards (Pcon _ args) = pats_wildcards args /\
  pat_wildcards (Ptannot p _) = pat_wildcards p /\

  pats_wildcards [] = 0n /\
  pats_wildcards (p::ps) =
    (pat_wildcards p) + (pats_wildcards ps)`

  (WF_REL_TAC `measure pat_size`)

(* [v_of_pat]: from a pattern and a list of instantiations for the pattern
   variables, produce a semantic value
*)

val v_of_matching_pat_aux_measure_def = Define `
  v_of_matching_pat_aux_measure x =
    sum_CASE x
      (\(_,p,_,_). pat_size p)
      (\(_,ps,_,_). list_size pat_size ps)`;

val v_of_pat_def = tDefine "v_of_pat" `
  v_of_pat envC (Pvar x) insts wildcards =
    (case insts of
         xv::rest => SOME (xv, rest, wildcards)
       | _ => NONE) /\
  v_of_pat envC Pany insts wildcards =
    (case wildcards of
         xv::rest => SOME (xv, insts, rest)
       | _ => NONE) /\
  v_of_pat envC (Plit l) insts wildcards =
    SOME (Litv l, insts, wildcards) /\
  v_of_pat envC (Pcon c args) insts wildcards =
    (case v_of_pat_list envC args insts wildcards of
         SOME (argsv, insts_rest, wildcards_rest) =>
         (case c of
              NONE => SOME (Conv NONE argsv, insts_rest, wildcards_rest)
            | SOME id =>
              case nsLookup envC id of
                  NONE => NONE
                | SOME (len, t) =>
                  if len = LENGTH argsv then
                    SOME (Conv (SOME t) argsv, insts_rest, wildcards_rest)
                  else NONE)
      | NONE => NONE) /\
  v_of_pat _ (Pref pat) _ _ =
    NONE (* unsupported *) /\
  v_of_pat envC (Ptannot p _) insts wildcards =
    v_of_pat envC p insts wildcards /\
  v_of_pat _ _ _ _ = NONE /\

  v_of_pat_list _ [] insts wildcards = SOME ([], insts, wildcards) /\
  v_of_pat_list envC (p::argspat) insts wildcards =
    (case v_of_pat envC p insts wildcards of
         SOME (v, insts_rest, wildcards_rest) =>
         (case v_of_pat_list envC argspat insts_rest wildcards_rest of
              SOME (vs, insts_rest', wildcards_rest') =>
                SOME (v::vs, insts_rest', wildcards_rest')
            | NONE => NONE)
       | NONE => NONE) /\
  v_of_pat_list _ _ _ _ = NONE`

  (WF_REL_TAC `measure v_of_matching_pat_aux_measure` \\
   fs [v_of_matching_pat_aux_measure_def, list_size_def,
       astTheory.pat_size_def] \\
   gen_tac \\ Induct \\ fs [list_size_def, astTheory.pat_size_def]);

val v_of_pat_ind = fetch "-" "v_of_pat_ind";

Theorem v_of_pat_list_length:
   !envC pats insts wildcards vs rest.
      v_of_pat_list envC pats insts wildcards = SOME (vs, rest, wrest) ==>
      LENGTH pats = LENGTH vs
Proof
  Induct_on `pats` \\ fs [v_of_pat_def] \\ rpt strip_tac \\
  every_case_tac \\ fs [] \\ rw [] \\ first_assum irule \\ instantiate
QED

Theorem v_of_pat_insts_length:
   (!envC pat insts wildcards v insts_rest wildcards_rest.
       v_of_pat envC pat insts wildcards = SOME (v, insts_rest, wildcards_rest) ==>
       (LENGTH insts = LENGTH (pat_bindings pat []) + LENGTH insts_rest)) /\
    (!envC pats insts wildcards vs insts_rest wildcards_rest.
       v_of_pat_list envC pats insts wildcards = SOME (vs, insts_rest, wildcards_rest) ==>
       (LENGTH insts = LENGTH (pats_bindings pats []) + LENGTH insts_rest))
Proof
  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  fs [v_of_pat_def, pat_bindings_def, LENGTH_NIL] \\ rw []
  THEN1 (every_case_tac \\ fs [LENGTH_NIL])
  THEN1 (every_case_tac \\ fs [])
  THEN1 (
    (* v_of_pat _ (Pcon _ _) _ _ *)
    every_case_tac \\ fs [] \\ rw [] \\
    once_rewrite_tac [semanticPrimitivesPropsTheory.pat_bindings_accum] \\ fs []
  )
  THEN1 (
    (* v_of_pat_list _ (_::_) _ _ *)
    every_case_tac \\ fs [] \\ rw [] \\
    once_rewrite_tac [semanticPrimitivesPropsTheory.pat_bindings_accum] \\ fs []
  )
QED

Theorem v_of_pat_wildcards_count:
   (!envC pat insts wildcards v insts_rest wildcards_rest.
       v_of_pat envC pat insts wildcards = SOME (v, insts_rest, wildcards_rest) ==>
       (LENGTH wildcards = pat_wildcards pat + LENGTH wildcards_rest)) /\
    (!envC pats insts wildcards vs insts_rest wildcards_rest.
       v_of_pat_list envC pats insts wildcards = SOME (vs, insts_rest, wildcards_rest) ==>
       (LENGTH wildcards = pats_wildcards pats + LENGTH wildcards_rest))
Proof
  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  fs [v_of_pat_def, pat_bindings_def, pat_wildcards_def, LENGTH_NIL] \\ rw [] \\
  every_case_tac \\ fs [] \\ rw []
QED

Theorem v_of_pat_extend_insts:
   (!envC pat insts wildcards v rest wildcards_rest insts'.
       v_of_pat envC pat insts wildcards = SOME (v, rest, wildcards_rest) ==>
       v_of_pat envC pat (insts ++ insts') wildcards = SOME (v, rest ++ insts', wildcards_rest)) /\
    (!envC pats insts wildcards vs rest wildcards_rest insts'.
       v_of_pat_list envC pats insts wildcards = SOME (vs, rest, wildcards_rest) ==>
       v_of_pat_list envC pats (insts ++ insts') wildcards = SOME (vs, rest ++ insts', wildcards_rest))
Proof
  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c`
    THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [])
    THEN1 (
      fs [v_of_pat_def] \\ every_case_tac \\ rw [] \\
      TRY (qpat_x_assum `LENGTH _ = LENGTH _` (K all_tac)) \\ fs [] \\
      rw []
    )
  )
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
QED

Theorem v_of_pat_extend_wildcards:
   (!envC pat insts wildcards v rest wildcards_rest wildcards'.
       v_of_pat envC pat insts wildcards = SOME (v, rest, wildcards_rest) ==>
       v_of_pat envC pat insts (wildcards ++ wildcards') = SOME (v, rest, wildcards_rest ++ wildcards')) /\
    (!envC pats insts wildcards vs rest wildcards_rest wildcards'.
       v_of_pat_list envC pats insts wildcards = SOME (vs, rest, wildcards_rest) ==>
       v_of_pat_list envC pats insts (wildcards ++ wildcards') = SOME (vs, rest, wildcards_rest ++ wildcards'))
Proof
  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c`
    THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [])
    THEN1 (
      first_x_assum (assume_tac o (SIMP_RULE std_ss [v_of_pat_def])) \\
      every_case_tac \\ fs [] \\ rw [] \\ fs [v_of_pat_def]
    )
  )
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
QED

Theorem v_of_pat_NONE_extend_insts:
   (!envC pat insts wildcards insts'.
       v_of_pat envC pat insts wildcards = NONE ==>
       LENGTH insts >= LENGTH (pat_bindings pat []) ==>
       LENGTH wildcards >= pat_wildcards pat ==>
       v_of_pat envC pat (insts ++ insts') wildcards = NONE) /\
    (!envC pats insts wildcards insts'.
       v_of_pat_list envC pats insts wildcards = NONE ==>
       LENGTH insts >= LENGTH (pats_bindings pats []) ==>
       LENGTH wildcards >= pats_wildcards pats ==>
       v_of_pat_list envC pats (insts ++ insts') wildcards = NONE)
Proof
  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (
    fs [v_of_pat_def, pat_bindings_def, pat_wildcards_def] \\
    every_case_tac \\ fs []
  )
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c`
    THEN1 (
      fs [v_of_pat_def, pat_bindings_def, pat_wildcards_def] \\
      every_case_tac \\ fs []
    )
    THEN1 (
      fs [v_of_pat_def, pat_bindings_def, pat_wildcards_def] \\
      every_case_tac \\ fs [] \\ rw [] \\
      metis_tac [v_of_pat_list_length]
    )
  )
  THEN1 (
    fs [v_of_pat_def, pat_bindings_def, pat_wildcards_def] \\
    every_case_tac \\ fs [] \\
    fs [Once (snd (CONJ_PAIR semanticPrimitivesPropsTheory.pat_bindings_accum))]
    THEN1 (
      `LENGTH insts >= LENGTH (pat_bindings pat [])` by (fs []) \\
      `LENGTH wildcards >= pat_wildcards pat` by (fs []) \\
      fs []
    )
    THEN1 (
      rw [] \\
      progress (fst (CONJ_PAIR v_of_pat_insts_length)) \\
      progress (fst (CONJ_PAIR v_of_pat_wildcards_count)) \\
      rename1 `LENGTH insts = _ + LENGTH rest2` \\
      rename1 `LENGTH wildcards = _ + LENGTH w_rest2` \\
      `LENGTH rest2 >= LENGTH (pats_bindings pats [])` by (fs []) \\
      `LENGTH w_rest2 >= pats_wildcards pats` by (fs []) \\ fs [] \\
      progress (fst (CONJ_PAIR v_of_pat_extend_insts)) \\
      pop_assum (qspec_then `insts'` assume_tac) \\ fs [] \\ rw [] \\ fs []
    )
  )
QED

Theorem v_of_pat_remove_rest_insts:
   (!pat envC insts wildcards v rest wildcards_rest.
       v_of_pat envC pat insts wildcards = SOME (v, rest, wildcards_rest) ==>
       ?insts'.
         insts = insts' ++ rest /\
         LENGTH insts' = LENGTH (pat_bindings pat []) /\
         v_of_pat envC pat insts' wildcards = SOME (v, [], wildcards_rest)) /\
    (!pats envC insts wildcards vs rest wildcards_rest.
       v_of_pat_list envC pats insts wildcards = SOME (vs, rest, wildcards_rest) ==>
       ?insts'.
         insts = insts' ++ rest /\
         LENGTH insts' = LENGTH (pats_bindings pats []) /\
         v_of_pat_list envC pats insts' wildcards = SOME (vs, [], wildcards_rest))
Proof
  HO_MATCH_MP_TAC astTheory.pat_induction \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def, pat_bindings_def])
  THEN1 (fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [])
  THEN1 (fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [])
  THEN1 (
    rename1 `Pcon c _` \\ Cases_on `c` \\
    fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ rw []
  )
  THEN1 (
    fs [v_of_pat_def, pat_bindings_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    qpat_assum `v_of_pat _ _ _ _ = _` (first_assum o progress_with) \\
    qpat_assum `v_of_pat_list _ _ _ _ = _` (first_assum o progress_with) \\
    rw []
    THEN1 (
      once_rewrite_tac [snd (CONJ_PAIR semanticPrimitivesPropsTheory.pat_bindings_accum)] \\
      fs []
    )
    THEN1 (
      rename1 `LENGTH insts_pats = LENGTH (pats_bindings pats [])` \\
      rename1 `LENGTH insts_pat = LENGTH (pat_bindings pat [])` \\
      rename1 `v_of_pat_list _ _ (_ ++ rest) _` \\
      fs [APPEND_ASSOC] \\ every_case_tac \\ fs []
      THEN1 (
        progress_then (qspec_then `rest` assume_tac)
          (fst (CONJ_PAIR v_of_pat_NONE_extend_insts)) \\
        `LENGTH (insts_pat ++ insts_pats) >= LENGTH (pat_bindings pat [])`
          by (fs []) \\
        `LENGTH wildcards >= pat_wildcards pat` by (
          progress (fst (CONJ_PAIR v_of_pat_wildcards_count)) \\ fs []
        ) \\ fs []
      ) \\
      rename1 `v_of_pat_list _ _ rest' _ = _` \\
      qpat_x_assum `v_of_pat _ _ (_ ++ _) _ = _` (first_assum o progress_with) \\
      `rest' = insts_pats` by (metis_tac [APPEND_11_LENGTH]) \\ fs [] \\ rw [] \\ fs []
    )
  )
QED

Theorem v_of_pat_insts_unique:
   (!envC pat insts wildcards rest wildcards_rest v.
       v_of_pat envC pat insts wildcards = SOME (v, rest, wildcards_rest) ==>
       (!insts' wildcards'. v_of_pat envC pat insts' wildcards' = SOME (v, rest, wildcards_rest) <=> (insts' = insts /\ wildcards' = wildcards))) /\
    (!envC pats insts wildcards rest wildcards_rest vs.
       v_of_pat_list envC pats insts wildcards = SOME (vs, rest, wildcards_rest) ==>
       (!insts' wildcards'. v_of_pat_list envC pats insts' wildcards' = SOME (vs, rest, wildcards_rest) <=> (insts' = insts /\ wildcards' = wildcards)))
Proof
  HO_MATCH_MP_TAC v_of_pat_ind \\ rpt strip_tac \\
  try_finally (fs [v_of_pat_def] \\ every_case_tac \\ fs [])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ metis_tac [])
  THEN1 (fs [v_of_pat_def] \\ every_case_tac \\ fs [] \\ metis_tac [])
  THEN1 (
    reverse eq_tac THEN1 (rw []) \\ fs [v_of_pat_def] \\ strip_tac \\
    every_case_tac \\ fs [] \\ rw [] \\
    first_x_assum (qspecl_then [`insts'`, `wildcards'`] assume_tac) \\
    fs []
  )
  THEN1 (
    reverse eq_tac THEN1 (rw []) \\ strip_tac \\ fs [v_of_pat_def] \\
    every_case_tac \\ fs [] \\ rw [] \\ fs []
  )
QED

(* [v_of_pat_norest]: Wrapper that checks that there are no remaining
   instantiations and wildcards instantiations
*)

val v_of_pat_norest_def = Define `
  v_of_pat_norest envC pat insts wildcards =
    case v_of_pat envC pat insts wildcards of
        SOME (v, [], []) => SOME v
      | _ => NONE`;

Theorem v_of_pat_norest_insts_length:
   !envC pat insts wildcards v.
      v_of_pat_norest envC pat insts wildcards = SOME v ==>
      LENGTH insts = LENGTH (pat_bindings pat [])
Proof
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\ every_case_tac \\ fs [] \\
  rw [] \\ progress (fst (CONJ_PAIR v_of_pat_insts_length)) \\ fs []
QED

Theorem v_of_pat_norest_wildcards_count:
   !envC pat insts wildcards v.
      v_of_pat_norest envC pat insts wildcards = SOME v ==>
      LENGTH wildcards = pat_wildcards pat
Proof
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\ every_case_tac \\ fs [] \\
  rw [] \\ progress (fst (CONJ_PAIR v_of_pat_wildcards_count)) \\ fs []
QED

Theorem v_of_pat_norest_insts_unique:
   !envC pat insts wildcards v.
      v_of_pat_norest envC pat insts wildcards = SOME v ==>
      (!insts' wildcards'. v_of_pat_norest envC pat insts' wildcards' = SOME v <=> (insts' = insts /\ wildcards' = wildcards))
Proof
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\
  every_case_tac \\ fs [] \\ rw [] \\
  try_finally (
    CONV_TAC quantHeuristicsTools.OR_NOT_CONV \\
    strip_tac \\ rw [] \\ fs []
  ) \\
  progress_then
    (qspecl_then [`insts'`, `wildcards'`] assume_tac)
    (fst (CONJ_PAIR (v_of_pat_insts_unique))) \\
  fs [] \\
  eq_tac \\ rw [] \\ fs []
QED

(* Predicates that discriminate the patterns we want to deal
   with. [validate_pat] packs them all up.
*)

(* might be wrong *)
val pat_typechecks_def = Define `
  pat_typechecks envC s pat v =
    (pmatch envC s pat v [] <> Match_type_error)`;

val pat_without_Pref_def = tDefine "pat_without_Pref" `
  pat_without_Pref (Pvar _) = T /\
  pat_without_Pref Pany = T /\
  pat_without_Pref (Plit _) = T /\
  pat_without_Pref (Pcon _ args) =
    EVERY pat_without_Pref args /\
  pat_without_Pref (Pref _) = F /\
  pat_without_Pref (Ptannot p _) = pat_without_Pref p`

  (WF_REL_TAC `measure pat_size` \\ simp[] \\
   Cases \\ Induct \\ fs [basicSizeTheory.option_size_def] \\
   fs [list_size_def, astTheory.pat_size_def] \\ rpt strip_tac \\ fs [] \\
   first_assum progress \\ fs []);

val validate_pat_def = Define `
  validate_pat envC s pat v env =
    (pat_typechecks envC s pat v /\
     pat_without_Pref pat /\
     ALL_DISTINCT (pat_bindings pat []))`;

(* Lemmas that relate [v_of_pat] and [pmatch], the pattern-matching function
   from the semantics.
*)

Theorem same_type_EQ_same_ctor[simp]:
   same_type r r <=> same_ctor r r
Proof
  Cases_on `r` \\ fs [same_type_def] \\ fs [same_ctor_def]
QED

Theorem same_ctor_REFL[simp]:
   same_ctor r r
Proof
  fs [same_ctor_def]
QED

Theorem v_of_pat_pmatch:
   (!envC s pat v env_v insts wildcards wildcards_rest.
      v_of_pat envC pat insts wildcards = SOME (v, [], wildcards_rest) ==>
      pmatch envC s pat v env_v = Match
        (ZIP (pat_bindings pat [], REVERSE insts) ++ env_v)) /\
    (!envC s pats vs env_v insts wildcards wildcards_rest.
      v_of_pat_list envC pats insts wildcards = SOME (vs, [], wildcards_rest) ==>
      pmatch_list envC s pats vs env_v = Match
        (ZIP (pats_bindings pats [], REVERSE insts) ++ env_v))
Proof
  HO_MATCH_MP_TAC pmatch_ind \\ rpt strip_tac \\ rw [] \\
  try_finally (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    CHANGED_TAC every_case_tac \\ fs [] \\
    CHANGED_TAC every_case_tac \\ fs []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs [] \\ rw []
    THEN1 (progress v_of_pat_list_length \\ first_assum progress)
    THEN1 (progress v_of_pat_list_length \\ fs [])
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    progress v_of_pat_list_length \\ first_assum progress \\ fs []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs [] \\ rw [] \\ first_assum progress
  )
  THEN1 (
    fs [pmatch_def, pat_bindings_def, v_of_pat_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    try_finally (
      progress (fst (CONJ_PAIR v_of_pat_remove_rest_insts)) \\ rw [] \\
      rename1 `insts' ++ rest` \\ first_assum (qspec_then `insts'` (fs o sing))
    ) \\
    once_rewrite_tac [snd (CONJ_PAIR semanticPrimitivesPropsTheory.pat_bindings_accum)] \\
    fs [] \\ progress (fst (CONJ_PAIR v_of_pat_remove_rest_insts)) \\ rw [] \\
    fs [REVERSE_APPEND] \\ progress (snd (CONJ_PAIR v_of_pat_insts_length)) \\
    fs [GSYM ZIP_APPEND] \\ once_rewrite_tac [GSYM APPEND_ASSOC] \\
    rpt (first_x_assum progress) \\ rw []
  )
QED

Theorem v_of_pat_norest_pmatch:
   !envC s pat v env_v insts wildcards.
     v_of_pat_norest envC pat insts wildcards = SOME v ==>
     pmatch envC s pat v env_v = Match
       (ZIP (pat_bindings pat [], REVERSE insts) ++ env_v)
Proof
  rpt strip_tac \\ fs [v_of_pat_norest_def] \\
  irule (fst (CONJ_PAIR v_of_pat_pmatch)) \\
  every_case_tac \\ rw [] \\ instantiate
QED

Theorem pmatch_v_of_pat:
   (!envC s pat v env_v env_v'.
      pmatch envC s pat v env_v = Match env_v' ==>
      pat_without_Pref pat ==>
      ?insts wildcards.
        env_v' = ZIP (pat_bindings pat [], REVERSE insts) ++ env_v /\
        v_of_pat envC pat insts wildcards = SOME (v, [], [])) /\
    (!envC s pats vs env_v env_v'.
      pmatch_list envC s pats vs env_v = Match env_v' ==>
      EVERY (\pat. pat_without_Pref pat) pats ==>
      ?insts wildcards.
        env_v' = ZIP (pats_bindings pats [], REVERSE insts) ++ env_v /\
        v_of_pat_list envC pats insts wildcards = SOME (vs, [], []))
Proof
  HO_MATCH_MP_TAC pmatch_ind \\ rpt strip_tac \\ rw [] \\
  try_finally (fs [pmatch_def, v_of_pat_def, pat_bindings_def])
  THEN1 (
    qexists_tac `[]` \\ Q.REFINE_EXISTS_TAC `w::ws` \\
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\ rw []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    qpat_x_assum `_ = _` (fs o sing o GSYM) \\
    rename1 `[(x,xv)]` \\ qexists_tac `[xv]` \\ fs []
  )
  THEN1 (
    fs [pmatch_def, v_of_pat_def, pat_bindings_def] \\
    every_case_tac \\ fs []
  )
  THEN1 (
    fs [pmatch_def, pat_without_Pref_def] \\ every_case_tac \\ fs [] \\
    fs [pat_bindings_def] \\ Q.LIST_EXISTS_TAC [`insts`, `wildcards`] \\
    rename1 `same_ctor t1 t2` \\ fs [] \\
    rewrite_tac [v_of_pat_def] \\ fs [] \\ progress v_of_pat_list_length \\
    fs [same_ctor_def]
  )
  THEN1 (
    fs [pmatch_def, pat_without_Pref_def] \\ every_case_tac \\ fs [] \\
    fs [pat_bindings_def] \\ Q.LIST_EXISTS_TAC [`insts`, `wildcards`] \\ fs [] \\
    rewrite_tac [v_of_pat_def] \\ every_case_tac \\ fs []
  )
  THEN1 (fs [pat_without_Pref_def])
  THEN1 (fs [pat_without_Pref_def,pat_bindings_def,v_of_pat_def,pmatch_def]
         \\ metis_tac[])
  THEN1 (
    fs [pmatch_def] \\ every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ rw [] \\ fs [pat_bindings_def] \\
    once_rewrite_tac [semanticPrimitivesPropsTheory.pat_bindings_accum] \\ fs [] \\
    rename1 `v_of_pat _ _ insts wildcards = _` \\
    rename1 `v_of_pat_list _ _ insts' wildcards' = _` \\
    qexists_tac `insts ++ insts'` \\ qexists_tac `wildcards ++ wildcards'` \\
    progress (fst (CONJ_PAIR v_of_pat_insts_length)) \\
    progress (snd (CONJ_PAIR v_of_pat_insts_length)) \\ fs [ZIP_APPEND] \\
    progress_then (qspec_then `insts'` assume_tac)
      (fst (CONJ_PAIR v_of_pat_extend_insts)) \\
    progress_then (qspec_then `wildcards'` assume_tac)
      (fst (CONJ_PAIR v_of_pat_extend_wildcards)) \\
    progress_then (qspec_then `insts'` assume_tac)
      (snd (CONJ_PAIR v_of_pat_extend_insts)) \\
    progress_then (qspec_then `wildcards'` assume_tac)
      (snd (CONJ_PAIR v_of_pat_extend_insts)) \\
    fs [v_of_pat_def]
  )
QED

Theorem pmatch_v_of_pat_norest:
   !envC s pat v env_v env_v'.
      pmatch envC s pat v env_v = Match env_v' ==>
      pat_without_Pref pat ==>
      ?insts wildcards.
        env_v' = ZIP (pat_bindings pat [], REVERSE insts) ++ env_v /\
        v_of_pat_norest envC pat insts wildcards = SOME v
Proof
  rpt strip_tac \\ progress (fst (CONJ_PAIR pmatch_v_of_pat)) \\ fs [] \\
  Q.LIST_EXISTS_TAC [`insts`, `wildcards`] \\ fs [v_of_pat_norest_def]
QED

(* The nested ifs corresponding to a list of patterns *)

val cf_cases_def = Define `
  cf_cases v nomatch_exn [] env H Q =
    local (\H Q. H ==>> Q (Exn nomatch_exn) /\ Q =~e> POST_F) H Q /\
  cf_cases v nomatch_exn ((pat, row_cf)::rows) env H Q =
    local (\H Q.
      ((if (?insts wildcards. v_of_pat_norest env.c pat insts wildcards = SOME v) then
          (!insts wildcards. v_of_pat_norest env.c pat insts wildcards = SOME v ==>
             can_pmatch_all env.c [] (MAP FST rows) v /\
             row_cf (extend_env (REVERSE (pat_bindings pat [])) insts env) H Q)
        else cf_cases v nomatch_exn rows env H Q) /\
       (!s. validate_pat env.c s pat v env.v))
    ) H Q`;

fun NETA_CONV t = let
    val (params, body) = strip_abs t
    val t' = List.foldl (fn (_, t') => fst (dest_comb t')) body params
in
    prove (
        mk_eq (t, t'),
        NTAC (length params) (irule EQ_EXT \\ gen_tac) \\ fs []
    )
end

Theorem cf_cases_local:
   !v nomatch_exn rows env.
      is_local (cf_cases v nomatch_exn rows env)
Proof
  rpt strip_tac \\
  `cf_cases v nomatch_exn rows env =
   (\H Q. cf_cases v nomatch_exn rows env H Q)` by (
    NTAC 2 (irule EQ_EXT \\ gen_tac) \\ fs [] \\ NO_TAC) \\
  pop_assum (once_rewrite_tac o sing) \\
  Induct_on `rows`
  THEN1 (
    fs [cf_cases_def] \\
    CONV_TAC (RAND_CONV NETA_CONV) \\
    fs [local_is_local]
  )
  THEN1 (
    qx_gen_tac `p` \\ Cases_on `p` \\ fs [cf_cases_def] \\
    CONV_TAC (RAND_CONV NETA_CONV) \\ fs [local_is_local]
  )
QED


(*------------------------------------------------------------------*)
(* Soundness predicate & lemmas *)

(* States that a hoare triple {H} e {Q} is valid in environment [env] *)
val htriple_valid_def = Define `
  htriple_valid (p:'ffi ffi_proj) e env H Q =
    !st h_i h_k.
      SPLIT (st2heap p st) (h_i, h_k) ==>
      H h_i ==>
      ?r h_f h_g heap.
        SPLIT3 heap (h_f, h_k, h_g) /\ Q r h_f /\
        evaluate_to_heap st env e p heap r`;

(* Not used, but interesting: app_basic as an instance of htriple_valid *)
Theorem app_basic_iff_htriple_valid:
   ∀env exp. do_opapp [fv; argv] = SOME (env,exp) ⇒
   (app_basic p fv argv H Q ⇔ htriple_valid p exp env H Q)
Proof
  rw[EQ_IMP_THM,app_basic_def,htriple_valid_def]
  \\ res_tac \\ rpt (asm_exists_tac \\ rw[])
QED

Theorem app_basic_eq_htriple_valid:
   app_basic (p:'ffi ffi_proj) (f: v) (x: v) H Q <=>
    case do_opapp [f; x] of
       SOME (env, exp) => htriple_valid p exp env H Q
     | NONE => ∀st h1 h2. SPLIT (st2heap p st) (h1,h2) ⇒ ¬ H h1
Proof
  reverse CASE_TAC
  >- ( CASE_TAC \\ rw[app_basic_iff_htriple_valid] )
  \\ rw[app_basic_def] \\ metis_tac[]
QED

(* Soundness for relation [R] *)
val sound_def = Define `
  sound (p:'ffi ffi_proj) e R =
    !env H Q.
      R env H Q ==>
      htriple_valid p e env H Q`;


val star_split = Q.prove (
  `!H1 H2 H3 H4 h1 h2 h3 h4.
     ((H1 * H2) (h1 UNION h2) ==> (H3 * H4) (h3 UNION h4)) ==>
     DISJOINT h1 h2 ==> H1 h1 ==> H2 h2 ==>
     ?u v. H3 u /\ H4 v /\ SPLIT (h3 UNION h4) (u, v)`,
  fs [STAR_def] \\ rpt strip_tac \\
  `SPLIT (h1 UNION h2) (h1, h2)` by SPLIT_TAC \\
  metis_tac []
);

Theorem sound_local:
   !e R. sound (p:'ffi ffi_proj) e R ==> sound (p:'ffi ffi_proj) e (\env. local (R env))
Proof
  rpt strip_tac \\ rewrite_tac [sound_def, htriple_valid_def] \\
  fs [local_def] \\ rpt strip_tac \\
  res_tac \\ rename1 `(H_i * H_k) h_i` \\ rename1 `R env H_i Q_f` \\
  rename1 `SEP_IMPPOST (Q_f *+ H_k) (Q *+ H_g)` \\
  fs [STAR_def] \\ rename1 `H_i h'_i` \\ rename1 `H_k h'_k` \\
  `SPLIT (st2heap (p:'ffi ffi_proj) st) (h'_i, h_k UNION h'_k)` by SPLIT_TAC \\
  qpat_x_assum `sound _ _ _` (progress o REWRITE_RULE [sound_def, htriple_valid_def]) \\
  rename1 `SPLIT3 _ (h'_f, _, h'_g)` \\
  fs [SEP_IMPPOST_def, STARPOST_def, SEP_IMP_def, STAR_def] \\
  first_x_assum (qspecl_then [`r`, `h'_f UNION h'_k`] assume_tac) \\
  `DISJOINT h'_f h'_k` by SPLIT_TAC \\
  `?h_f h''_g. Q r h_f /\ H_g h''_g /\ SPLIT (h'_f UNION h'_k) (h_f, h''_g)` by
    metis_tac [star_split] \\
  Q.LIST_EXISTS_TAC [`r`, `h_f`, `h'_g UNION h''_g`, `heap`] \\ fs [] \\
  SPLIT_TAC
QED

Theorem sound_false:
   !e. sound (p:'ffi ffi_proj) e (\env H Q. F)
Proof
  rewrite_tac [sound_def]
QED

val sound_local_false = Q.prove (
  `!e. sound (p:'ffi ffi_proj) e (\env. local (\H Q. F))`,
  strip_tac \\ HO_MATCH_MP_TAC sound_local \\ fs [sound_false]
);

(*------------------------------------------------------------------*)
(* Lemmas relating [app], and [htriple_valid] (usually on the
   expression composing the body of the applied function).
*)

val app_basic_of_htriple_valid = Q.prove (
  `!clos body x env v H Q.
    do_opapp [clos; x] = SOME (env, body) ==>
    htriple_valid (p:'ffi ffi_proj) body env H Q ==>
    app_basic (p:'ffi ffi_proj) clos x H Q`,
  fs [app_basic_def, htriple_valid_def] \\ rpt strip_tac \\
  first_x_assum progress \\ instantiate \\ SPLIT_TAC);

val app_of_htriple_valid = Q.prove (
  `!ns xvs env body H Q.
     ns <> [] ==>
     LENGTH ns = LENGTH xvs ==>
     htriple_valid (p:'ffi ffi_proj) body (extend_env ns xvs env) H Q ==>
     app (p:'ffi ffi_proj) (naryClosure env ns body) xvs H Q`,
  Induct \\ rpt strip_tac \\ fs [naryClosure_def, LENGTH_CONS] \\ rw [] \\
  rename1 `extend_env (n::ns) (xv::xvs) _` \\
  Cases_on `ns` \\ fs [LENGTH_NIL, LENGTH_CONS, PULL_EXISTS] \\ rw [] \\
  fs [extend_env_def, extend_env_v_def, naryFun_def, app_def]
  THEN1 (irule app_basic_of_htriple_valid \\ fs [do_opapp_def]) \\
  fs [app_basic_def] \\ rpt strip_tac \\ fs [do_opapp_def] \\
  fs [POSTv_def, SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS, SPLIT_emp2] \\
  Q.REFINE_EXISTS_TAC `Val v` \\ simp [evaluate_to_heap_def] \\
  fs [POSTv_def, SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS, SPLIT_emp2] \\
  fs [evaluate_ck_def, terminationTheory.evaluate_def, st2heap_clock] \\
  progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\ fs [naryClosure_def]);

val app_rec_of_htriple_valid_aux = Q.prove (
  `!f body params xvs funs naryfuns env H Q fvs.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     naryfuns = letrec_pull_params funs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) naryfuns) ==>
     find_recfun f naryfuns = SOME (params, body) ==>
     htriple_valid (p:'ffi ffi_proj) body
       (extend_env_rec (MAP (\ (f,_,_). f) naryfuns) fvs params xvs env)
       H Q ==>
     fvs = MAP (\ (f,_,_). naryRecclosure env naryfuns f) naryfuns ==>
     app (p:'ffi ffi_proj) (naryRecclosure env naryfuns f) xvs H Q`,
  Cases_on `params` \\ rpt strip_tac \\ rw [] \\
  fs [LENGTH_CONS] \\ rfs [] \\ qpat_x_assum `xvs = _` (K all_tac) \\
  rename1 `extend_env_rec _ _ (n::params) (xv::xvs) _` \\
  Cases_on `params` \\ rfs [LENGTH_NIL, LENGTH_CONS] \\
  fs [extend_env_rec_def, extend_env_v_rec_def] \\
  fs [extend_env_def, extend_env_v_def, app_def]
  THEN1 (
    irule app_basic_of_htriple_valid \\
    progress_then (fs o sing) do_opapp_naryRecclosure \\
    fs [naryFun_def, letrec_pull_params_names, build_rec_env_zip]
  ) \\
  rw [] \\ rename1 `extend_env_v (n'::params) (xv'::xvs) _` \\
  fs [app_basic_def] \\ rpt strip_tac \\
  progress_then (fs o sing) do_opapp_naryRecclosure \\
  Q.REFINE_EXISTS_TAC `Val v` \\ simp [evaluate_to_heap_def] \\
  fs [POSTv_def, SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS, SPLIT_emp2] \\
  progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
  (* fixme *)
  qexists_tac `naryClosure
    (env with v := nsBind n xv (nsAppend (alist_to_ns (ZIP (MAP (\ (f,_,_). f) (letrec_pull_params funs),
      MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f)
          (letrec_pull_params funs)))) env.v))
    (n'::params) body` \\
  qexists_tac `st.clock` \\
  rpt strip_tac \\
  fs [letrec_pull_params_names |> Q.SPEC `x` |> Q.ISPECL [`I:'a->'a`]
      |> SIMP_RULE std_ss []]
  THEN1 (irule app_of_htriple_valid \\ fs [extend_env_def]) \\
  fs [naryFun_def, naryClosure_def] \\
  fs [evaluate_ck_def, terminationTheory.evaluate_def, with_clock_self] \\
  fs [letrec_pull_params_cancel, letrec_pull_params_names] \\
  fs [build_rec_env_zip]);

val app_rec_of_htriple_valid = Q.prove (
  `!f params body funs xvs env H Q.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (params, body) ==>
     htriple_valid (p:'ffi ffi_proj) body
       (extend_env_rec
          (MAP (\ (f,_,_). f) funs)
          (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
          params xvs env)
        H Q ==>
     app (p:'ffi ffi_proj) (naryRecclosure env (letrec_pull_params funs) f) xvs H Q`,
  rpt strip_tac \\ irule app_rec_of_htriple_valid_aux \\ rpt conj_tac
  THEN1 (fs [letrec_pull_params_names])
  THEN1 (qexists_tac `funs` \\ fs [])
  THEN1 (instantiate \\ fs [letrec_pull_params_names]));

(*------------------------------------------------------------------*)
(* Lemmas used in the soundness proof of FFI *)

Theorem SPLIT_SING_2:
   SPLIT s (x,{y}) <=> (s = y INSERT x) /\ ~(y IN x)
Proof
  SPLIT_TAC
QED

val SUBSET_IN = Q.prove(
  `!s t x. s SUBSET t /\ x IN s ==> x IN t`,
  fs [SUBSET_DEF] \\ metis_tac []);

Theorem SPLIT_FFI_SET_IMP_DISJOINT:
   SPLIT (st2heap p st) (c,{FFI_part s u ns ts}) ==>
    !s1 ts1. ~(FFI_part s1 u ns ts1 IN c)
Proof
  fs [SPLIT_def] \\ rw [] \\ fs [EXTENSION,st2heap_def,DISJOINT_DEF]
  \\ CCONTR_TAC \\ fs []
  \\ `FFI_part s1 u ns ts1 IN ffi2heap p st.ffi /\
      FFI_part s u ns ts IN ffi2heap p st.ffi` by
          metis_tac [FFI_part_NOT_IN_store2heap]
  \\ PairCases_on `p`
  \\ fs [ffi2heap_def]
  \\ pop_assum mp_tac \\ IF_CASES_TAC \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ Cases_on `s = s1` \\ fs []
  \\ Cases_on `ns` \\ fs []
  \\ metis_tac []
QED

Theorem SPLIT_IMP_Mem_NOT_IN:
   SPLIT (st2heap p st) ({Mem y xs},c) ==>
    !ys. ~(Mem y ys IN c)
Proof
  fs [SPLIT_def] \\ rw [] \\ fs [EXTENSION,st2heap_def]
  \\ CCONTR_TAC \\ fs []
  \\ `Mem y ys ∈ store2heap st.refs` by metis_tac [Mem_NOT_IN_ffi2heap]
  \\ `Mem y xs ∈ store2heap st.refs` by metis_tac [Mem_NOT_IN_ffi2heap]
  \\ imp_res_tac store2heap_IN_unique_key \\ fs []
QED

Theorem SPLIT_Mem_IMP_Mem_NOT_IN:
   SPLIT (st2heap p st) (c1,c2) ==>
    !y xs. Mem y xs IN c1 ==>
    !ys. ~(Mem y ys IN c2)
Proof
  fs [SPLIT_def] \\ rw [] \\ fs [EXTENSION,st2heap_def]
  \\ CCONTR_TAC \\ fs []
  \\ `Mem y ys ∈ store2heap st.refs` by metis_tac [Mem_NOT_IN_ffi2heap]
  \\ `Mem y xs ∈ store2heap st.refs` by metis_tac [Mem_NOT_IN_ffi2heap]
  \\ imp_res_tac store2heap_IN_unique_key \\ fs []
  \\ fs[DISJOINT_DEF]
  \\ metis_tac[IN_INTER,NOT_IN_EMPTY]
QED

Theorem FLOOKUP_FUPDATE_LIST:
   !ns f. FLOOKUP (f |++ MAP (λn. (n,s)) ns) m =
           if MEM m ns then SOME s else FLOOKUP f m
Proof
  Induct \\ fs [FUPDATE_LIST] \\ rw [] \\ fs []
  \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
QED

Theorem FIND_IMP_pred:
  FIND P l = SOME e ==> P e
Proof
  Induct_on `l` >> rw[mllistTheory.FIND_thm] >> rw[]
QED

Theorem MEM_ALL_DISTINCT_FIND:
  !sigs sig.
  MEM sig sigs /\ ALL_DISTINCT (MAP (λn. n.mlname) sigs)
  ==> FIND (λsig'. sig'.mlname = sig.mlname) sigs = SOME sig
Proof
  Induct >> rw[mllistTheory.FIND_thm] >> fs[MEM_MAP,PULL_EXISTS] \\ metis_tac[]
QED

(* TODO: move? *)
Theorem FIND_IMP_MEM:
  FIND P l = SOME e ==> MEM e l
Proof
  Induct_on `l` >> rw[mllistTheory.FIND_thm]
QED

Theorem FLOOKUP_FUPDATE_mlname_LIST:
   ∀sigs f.
     ALL_DISTINCT (MAP (λn. n.mlname) sigs) ==>
     FLOOKUP (f |++ MAP (λn. (n.mlname,s,n)) sigs) name =
     (case FIND (λn. n.mlname = name) sigs of
      | NONE => FLOOKUP f name
      | SOME sig => SOME(s,sig))
Proof
  Induct \\ fs [mllistTheory.FIND_thm,FUPDATE_LIST_THM] \\ rw [] \\ fs [] \\ rw [FLOOKUP_UPDATE] \\
  TOP_CASE_TAC >> imp_res_tac FIND_IMP_MEM \\ imp_res_tac FIND_IMP_pred \\
  fs[MEM_MAP,PULL_EXISTS] \\ metis_tac[]
QED

Theorem ALL_DISTINCT_FLAT_MEM_IMP:
   !p2. ALL_DISTINCT (FLAT p2) /\ MEM ns' p2 /\ MEM ns p2 /\
         MEM m ns' /\ MEM m ns ==> ns = ns'
Proof
  Induct \\ fs [ALL_DISTINCT_APPEND] \\ rw [] \\ fs []
  \\ res_tac \\ fs [MEM_FLAT] \\ metis_tac []
QED

Theorem ALL_DISTINCT_FLAT_FST_IMP:
   !p2. ALL_DISTINCT (FLAT (MAP FST p2)) /\
         MEM (ns,u') p2 /\ MEM (ns,u) p2 /\ ns <> [] ==> u = u'
Proof
  Induct \\ fs [ALL_DISTINCT_APPEND] \\ rw [] \\ fs []
  \\ fs [MEM_FLAT,MEM_MAP,FORALL_PROD]
  \\ Cases_on `ns` \\ fs []
  \\ first_x_assum (qspec_then `h` mp_tac) \\ fs []
  \\ disch_then (qspec_then `h::t` mp_tac) \\ fs []
  \\ rw [] \\ fs []
QED

Theorem ALL_DISTINCT_FLAT_MAP_FST_IMP:
!p1.
ALL_DISTINCT (FLAT (MAP (MAP f ∘ FST) p1)) /\
MEM (ns,u) p1 /\ MEM(ns',u') p1 /\ MEM e ns /\ MEM e' ns' /\ f e = f e'
==> ns = ns'
Proof
  Induct \\ fs [ALL_DISTINCT_APPEND] \\ rw [] \\ fs []
  \\ fs [MEM_FLAT,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ res_tac
  \\ metis_tac[]
QED

Theorem ALL_DISTINCT_FLAT_MAP_FST_IMP2:
!p1.
ALL_DISTINCT (FLAT (MAP (MAP f ∘ FST) p1)) /\
MEM (ns,u) p1 /\ MEM(ns',u') p1 /\ MEM e ns /\ MEM e' ns' /\ f e = f e'
==> u = u'
Proof
  Induct \\ fs [ALL_DISTINCT_APPEND] \\ rw [] \\ fs []
  \\ fs [MEM_FLAT,MEM_MAP,FORALL_PROD,PULL_EXISTS,PULL_FORALL]
  \\ res_tac
  \\ metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_MEM:
  !l.
  ALL_DISTINCT (MAP f l) /\ MEM e l /\ MEM e' l /\ f e = f e' ==>
  e = e'
Proof
  Induct \\ fs [ALL_DISTINCT_APPEND] \\ rw [] \\ fs []
  \\ fs [MEM_FLAT,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem ALL_DISTINCT_FLAT_MAP_FST_IMP3:
!p1.
ALL_DISTINCT (FLAT (MAP (MAP f ∘ FST) p1)) /\
MEM (ns,u) p1 /\ MEM(ns',u') p1 /\ MEM e ns /\ MEM e' ns' /\ f e = f e'
==> e = e'
Proof
  rpt strip_tac \\
  drule_all(GEN_ALL ALL_DISTINCT_FLAT_MAP_FST_IMP) \\
  strip_tac \\
  rveq \\
  `u = u'` by(metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP2]) \\
  rveq \\
  CCONTR_TAC \\ fs[] \\
  drule ALL_DISTINCT_FLAT_EVERY \\ strip_tac \\
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS] \\
  res_tac \\
  fs[] \\
  metis_tac[ALL_DISTINCT_MAP_MEM]
QED

Theorem FIND_NONE_EXISTS:
  FIND P l = NONE <=> ~EXISTS P l
Proof
  Induct_on `l` >> rw[mllistTheory.FIND_thm]
QED

(*------------------------------------------------------------------*)
(* Definition of the [cf] functions, that generates the characteristic
   formula of a cakeml expression *)

val app_ref_def = Define `
  app_ref (x: v) H Q =
    ((!r. H * r ~~> x ==>> Q (Val r)) /\
     Q =~v> POST_F)`

val app_assign_def = Define `
  app_assign r (x: v) H Q =
    ((?x' F.
        (H ==>> F * r ~~> x') /\
        (F * r ~~> x ==>> Q (Val (Conv NONE [])))) /\
     Q =~v> POST_F)`

val app_deref_def = Define `
  app_deref r H Q =
    ((?x F.
        (H ==>> F * r ~~> x) /\
        (H ==>> Q (Val x))) /\
     Q =~v> POST_F)`

val app_aalloc_def = Define `
  app_aalloc (n: int) v H Q =
    ((!a.
        n >= 0 /\
        (H * ARRAY a (REPLICATE (Num n) v) ==>> Q (Val a))) /\
     Q =~v> POST_F)`

val app_asub_def = Define `
  app_asub a (i: int) H Q =
    ((?vs F.
        0 <= i /\ (Num i) < LENGTH vs /\
        (H ==>> F * ARRAY a vs) /\
        (H ==>> Q (Val (EL (Num i) vs)))) /\
     Q =~v> POST_F)`

val app_alength_def = Define `
  app_alength a H Q =
    ((?vs F.
        (H ==>> F * ARRAY a vs) /\
        (H ==>> Q (Val (Litv (IntLit (& LENGTH vs)))))) /\
     Q =~v> POST_F)`

val app_aupdate_def = Define `
  app_aupdate a (i: int) v H Q =
    ((?vs F.
        0 <= i /\ (Num i) < LENGTH vs /\
        (H ==>> F * ARRAY a vs) /\
        (F * ARRAY a (LUPDATE v (Num i) vs) ==>> Q (Val (Conv NONE [])))) /\
     Q =~v> POST_F)`

val app_aw8alloc_def = Define `
  app_aw8alloc (n: int) w H Q =
    ((!a.
        n >= 0 /\
        (H * W8ARRAY a (REPLICATE (Num n) w) ==>> Q (Val a))) /\
     Q =~v> POST_F)`

val app_aw8sub_def = Define `
  app_aw8sub a (i: int) H Q =
    ((?ws F.
        0 <= i /\ (Num i) < LENGTH ws /\
        (H ==>> F * W8ARRAY a ws) /\
        (H ==>> Q (Val (Litv (Word8 (EL (Num i) ws)))))) /\
     Q =~v> POST_F)`

val app_aw8length_def = Define `
  app_aw8length a H Q =
    ((?ws F.
        (H ==>> F * W8ARRAY a ws) /\
        (H ==>> Q (Val (Litv (IntLit (& LENGTH ws)))))) /\
     Q =~v> POST_F)`

val app_aw8update_def = Define `
  app_aw8update a (i: int) w H Q =
    ((?ws F.
        0 <= i /\ (Num i) < LENGTH ws /\
        (H ==>> F * W8ARRAY a ws) /\
        (F * W8ARRAY a (LUPDATE w (Num i) ws) ==>> Q (Val (Conv NONE [])))) /\
     Q =~v> POST_F)`

val app_copyaw8aw8_def = Define `
  app_copyaw8aw8 s so l d do' H Q =
    ((?ws wd F.
        0 <= do' /\ 0 <= so /\ 0 <= l /\
        (Num do' + Num l) <= LENGTH wd /\(Num so + Num l) <= LENGTH ws /\
        (H ==>> F * W8ARRAY s ws * W8ARRAY d wd) /\
        (F * W8ARRAY s ws *
             W8ARRAY d (TAKE (Num do') wd ⧺
                        TAKE (Num l) (DROP (Num so) ws) ⧺
                        DROP (Num do' + Num l) wd)
            ==>> Q (Val (Conv NONE [])))) /\
     Q =~v> POST_F)`

val app_copystraw8_def = Define `
  app_copystraw8 s so l d do' H Q =
    ((?wd F.
        0 <= do' /\ 0 <= so /\ 0 <= l /\
        (Num do' + Num l) <= LENGTH wd /\(Num so + Num l) <= LENGTH s /\
        (H ==>> F * W8ARRAY d wd) /\
        (F * W8ARRAY d (TAKE (Num do') wd ⧺
                        MAP (n2w o ORD) (TAKE (Num l) (DROP (Num so) s)) ⧺
                        DROP (Num do' + Num l) wd)
            ==>> Q (Val (Conv NONE [])))) /\
     Q =~v> POST_F)`

val app_copyaw8str_def = Define `
  app_copyaw8str s so l H Q =
    ((?ws F.
        0 <= so /\ 0 <= l /\
        (Num so + Num l) <= LENGTH ws /\
        (H ==>> F * W8ARRAY s ws) /\
        (F * W8ARRAY s ws
            ==>> Q (Val (Litv (StrLit (MAP (CHR o w2n) (TAKE (Num l) (DROP (Num so) ws)))))))) /\
     Q =~v> POST_F)`

val app_wordFromInt_W8_def = Define `
  app_wordFromInt_W8 (i: int) H Q =
    (H ==>> Q (Val (Litv (Word8 (i2w i)))) /\
     Q =~v> POST_F)`

val app_wordFromInt_W64_def = Define `
  app_wordFromInt_W64 (i: int) H Q =
    (H ==>> Q (Val (Litv (Word64 (i2w i)))) /\
     Q =~v> POST_F)`

val app_wordToInt_def = Define `
  app_wordToInt w H Q =
    (H ==>> Q (Val (Litv (IntLit (& w2n w)))) /\
     Q =~v> POST_F)`

(*
val app_opn_def = Define `
  app_opn opn i1 i2 H Q =
    if (opn = Divide \/ opn = Modulo) /\ i2 = 0 then
      H ==>> Q (Exn (prim_exn "Div"))
    else
      H ==>> Q (Val (Litv (IntLit (opn_lookup opn i1 i2))))
*)

val app_opn_def = Define `
  app_opn opn i1 i2 H Q =
    ((if opn = Divide \/ opn = Modulo then i2 <> 0 else T) /\
     H ==>> Q (Val (Litv (IntLit (opn_lookup opn i1 i2)))) /\
     Q =~v> POST_F)`

val app_opb_def = Define `
  app_opb opb i1 i2 H Q =
    (H ==>> Q (Val (Boolv (opb_lookup opb i1 i2))) /\
     Q =~v> POST_F)`

val app_equality_def = Define `
  app_equality v1 v2 H Q =
    (no_closures v1 /\ no_closures v2 /\
     types_match v1 v2 /\
     H ==>> Q (Val (Boolv (v1 = v2))) /\
     Q =~v> POST_F)`

val cf_lit_def = Define `
  cf_lit l = \env. local (\H Q.
    H ==>> Q (Val (Litv l)) /\
    Q =~v> POST_F)`

val cf_con_def = Define `
  cf_con cn args = \env. local (\H Q.
    (?argsv cv.
       do_con_check env.c cn (LENGTH args) /\
       (build_conv env.c cn argsv = SOME cv) /\
       (exp2v_list env args = SOME argsv) /\
       H ==>> Q (Val cv)) /\
    Q =~v> POST_F)`

val cf_var_def = Define `
  cf_var name = \env. local (\H Q.
    (?v.
       nsLookup env.v name = SOME v /\
       H ==>> Q (Val v)) /\
    Q =~v> POST_F)`

val cf_let_def = Define `
  cf_let n F1 F2 = \env. local (\H Q.
    ?Q'. (F1 env H Q' /\ Q' =~v> Q) /\
         (!xv. F2 (env with <| v := nsOptBind n xv env.v |>) (Q' (Val xv)) Q))`

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

val cf_equality_def = Define `
  cf_equality x1 x2 = \env. local (\H Q.
    ?v1 v2.
      exp2v env x1 = SOME v1 /\
      exp2v env x2 = SOME v2 /\
      app_equality v1 v2 H Q)`

val cf_app_def = Define `
  cf_app (p:'ffi ffi_proj) f args = \env. local (\H Q.
    ?fv argsv.
      exp2v env f = SOME fv /\
      exp2v_list env args = SOME argsv /\
      app (p:'ffi ffi_proj) fv argsv H Q)`

val cf_fun_def = Define `
  cf_fun (p:'ffi ffi_proj) f ns F1 F2 = \env. local (\H Q.
    !fv.
      curried (p:'ffi ffi_proj) (LENGTH ns) fv /\
      (!xvs H' Q'.
        LENGTH xvs = LENGTH ns ==>
        F1 (extend_env ns xvs env) H' Q' ==>
        app (p:'ffi ffi_proj) fv xvs H' Q')
      ==>
      F2 (env with v := nsBind f fv env.v) H Q)`

val fun_rec_aux_def = Define `
  fun_rec_aux (p:'ffi ffi_proj) fs fvs [] [] [] F2 env H Q =
    (F2 (extend_env_rec fs fvs [] [] env) H Q) /\
  fun_rec_aux (p:'ffi ffi_proj) fs fvs (ns::ns_acc) (fv::fv_acc) (Fbody::Fs) F2 env H Q =
    (curried (p:'ffi ffi_proj) (LENGTH ns) fv /\
     (!xvs H' Q'.
        LENGTH xvs = LENGTH ns ==>
        Fbody (extend_env_rec fs fvs ns xvs env) H' Q' ==>
        app (p:'ffi ffi_proj) fv xvs H' Q')
     ==>
     (fun_rec_aux (p:'ffi ffi_proj) fs fvs ns_acc fv_acc Fs F2 env H Q)) /\
  fun_rec_aux _ _ _ _ _ _ _ _ _ _ = F`

val cf_fun_rec_def = Define `
  cf_fun_rec (p:'ffi ffi_proj) fs_Fs F2 = \env. local (\H Q.
    let fs = MAP (\ (f, _). f) fs_Fs in
    let Fs = MAP (\ (_, F). F) fs_Fs in
    let f_names = MAP (\ (f,_,_). f) fs in
    let f_args = MAP (\ (_,ns,_). ns) fs in
    !(fvs: v list).
      LENGTH fvs = LENGTH fs ==>
      ALL_DISTINCT f_names /\
      fun_rec_aux (p:'ffi ffi_proj) f_names fvs f_args fvs Fs F2 env H Q)`

val cf_ref_def = Define `
  cf_ref x = \env. local (\H Q.
    ?xv.
      exp2v env x = SOME xv /\
      app_ref xv H Q)`

val cf_assign_def = Define `
  cf_assign r x = \env. local (\H Q.
    ?rv xv.
      exp2v env r = SOME rv /\
      exp2v env x = SOME xv /\
      app_assign rv xv H Q)`

val cf_deref_def = Define `
  cf_deref r = \env. local (\H Q.
    ?rv.
      exp2v env r = SOME rv /\
      app_deref rv H Q)`

val cf_aalloc_def = Define `
  cf_aalloc xn xv = \env. local (\H Q.
    ?n v.
      exp2v env xn = SOME (Litv (IntLit n)) /\
      exp2v env xv = SOME v /\
      app_aalloc n v H Q)`

val cf_aalloc_empty_def = Define `
  cf_aalloc_empty xu = \env. local (\H Q.
    exp2v env xu = SOME (Conv NONE []) /\
    app_aalloc (&0) (Litv (IntLit &0)) H Q)`;

val cf_asub_def = Define `
  cf_asub xa xi = \env. local (\H Q.
    ?a i.
      exp2v env xa = SOME a /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_asub a i H Q)`

val cf_alength_def = Define `
  cf_alength xa = \env. local (\H Q.
    ?a.
      exp2v env xa = SOME a /\
      app_alength a H Q)`

val cf_aupdate_def = Define `
  cf_aupdate xa xi xv = \env. local (\H Q.
    ?a i v.
      exp2v env xa = SOME a /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      exp2v env xv = SOME v /\
      app_aupdate a i v H Q)`

val cf_aw8alloc_def = Define `
  cf_aw8alloc xn xw = \env. local (\H Q.
    ?n w.
      exp2v env xn = SOME (Litv (IntLit n)) /\
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_aw8alloc n w H Q)`

val cf_aw8sub_def = Define `
  cf_aw8sub xa xi = \env. local (\H Q.
    ?a i.
      exp2v env xa = SOME a /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_aw8sub a i H Q)`

val cf_aw8length_def = Define `
  cf_aw8length xa = \env. local (\H Q.
    ?a.
      exp2v env xa = SOME a /\
      app_aw8length a H Q)`

val cf_aw8update_def = Define `
  cf_aw8update xa xi xw = \env. local (\H Q.
    ?a i w.
      exp2v env xa = SOME a /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_aw8update a i w H Q)`

val cf_copyaw8aw8_def = Define `
  cf_copyaw8aw8 xs xso xl xd xdo = \env. local (\H Q.
    ?s so l d do'.
      exp2v env xs = SOME s /\
      exp2v env xd = SOME d /\
      exp2v env xl = SOME (Litv (IntLit l)) /\
      exp2v env xso = SOME (Litv (IntLit so)) /\
      exp2v env xdo = SOME (Litv (IntLit do')) /\
      app_copyaw8aw8 s so l d do' H Q)`

val cf_copystraw8_def = Define `
  cf_copystraw8 xs xso xl xd xdo = \env. local (\H Q.
    ?s so l d do'.
      exp2v env xs = SOME (Litv (StrLit s)) /\
      exp2v env xd = SOME d /\
      exp2v env xl = SOME (Litv (IntLit l)) /\
      exp2v env xso = SOME (Litv (IntLit so)) /\
      exp2v env xdo = SOME (Litv (IntLit do')) /\
      app_copystraw8 s so l d do' H Q)`

val cf_copyaw8str_def = Define `
  cf_copyaw8str xs xso xl = \env. local (\H Q.
    ?s so l.
      exp2v env xs = SOME s /\
      exp2v env xso = SOME (Litv (IntLit so)) /\
      exp2v env xl = SOME (Litv (IntLit l)) /\
      app_copyaw8str s so l H Q)`

val cf_wordFromInt_W8_def = Define `
  cf_wordFromInt_W8 xi = \env. local (\H Q.
    ?i.
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_wordFromInt_W8 i H Q)`

val cf_wordFromInt_W64_def = Define `
  cf_wordFromInt_W64 xi = \env. local (\H Q.
    ?i.
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_wordFromInt_W64 i H Q)`

val cf_wordToInt_W8_def = Define `
  cf_wordToInt_W8 xw = \env. local (\H Q.
    ?w.
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_wordToInt w H Q)`

val cf_wordToInt_W64_def = Define `
  cf_wordToInt_W64 xw = \env. local (\H Q.
    ?w.
      exp2v env xw = SOME (Litv (Word64 w)) /\
      app_wordToInt w H Q)`

val remdups_def = Define `
  (remdups [] = []) /\
  (remdups (f::r) = f::FILTER ($<> f) (remdups r))`

Theorem MEM_remdups:
  MEM x s ==> MEM x (remdups s)
Proof
  Induct_on `s` >> rw[remdups_def,MEM_FILTER] >> metis_tac[]
QED

Theorem remdups_MEM:
  MEM x (remdups s) ==> MEM x s
Proof
  Induct_on `s` >> rw[remdups_def,MEM_FILTER] >> metis_tac[]
QED

Theorem set_remdups:
  LIST_TO_SET(remdups s) = LIST_TO_SET s
Proof
  rw[SET_EQ_SUBSET,SUBSET_DEF,MEM_remdups,remdups_MEM]
QED

Theorem ALL_DISTINCT_remdups:
  !l. ALL_DISTINCT(remdups l)
Proof
  Induct_on `l` >> rw[remdups_def] >>
  fs[ALL_DISTINCT_FILTER,FILTER_FILTER,MEM_FILTER] >>
  rpt strip_tac >> res_tac >>
  fs[FILTER_EQ_CONS,FILTER_EQ_NIL] >>
  qexists_tac `l1` >>   qexists_tac `l2` >>
  fs[] >>
  conj_tac >>
  match_mp_tac(MP_CANON EVERY_MONOTONIC) >>
  PURE_ONCE_REWRITE_TAC[CONJ_SYM] >>
  asm_exists_tac >>
  rw[]
QED

Theorem remdups_MAP:
  (!x y. MEM x l /\ MEM y l /\ f x = f y ==> x = y) ==>
  remdups(MAP f l) = MAP f (remdups l)
Proof
  Induct_on `l` >> rw[remdups_def] >>
  simp[FILTER_MAP,o_DEF] >>
  qmatch_goalsub_abbrev_tac `MAP _ a1 = MAP _ a2` >>
  `a1 = a2` suffices_by simp[] >>
  unabbrev_all_tac >>
  rw[FILTER_EQ,EQ_IMP_THM] >>
  first_x_assum match_mp_tac >> fs[set_remdups]
QED

Theorem ALL_DISTINCT_MAP_FST_FILTER:
  ALL_DISTINCT(MAP FST l) ==>
  ALL_DISTINCT(MAP FST(FILTER f l))
Proof
  Induct_on `l` >> rw[MEM_MAP,MEM_FILTER] >> metis_tac[]
QED

Theorem ALL_DISTINCT_remdups_distinct_keys:
  (!m ws. MEM (m,ws) l ==>
   !ws'. MEM (m,ws') l ==> ws = ws') ==>
  ALL_DISTINCT(MAP FST(remdups l))
Proof
  Induct_on `l` >> Ho_Rewrite.PURE_REWRITE_TAC[FORALL_PROD] >> rw[remdups_def,MEM_MAP,MEM_FILTER,set_remdups] >-
    (CCONTR_TAC >> fs[] >> Cases_on `y` >> fs[] >> fs[] >> metis_tac[]) >>
  match_mp_tac ALL_DISTINCT_MAP_FST_FILTER >>
  first_x_assum match_mp_tac >>
  metis_tac[]
QED

Theorem MAP_FILTER_strong:
  !P f l. (∀x. MEM x l ==> (P (f x) ⇔ P x)) ⇒ MAP f (FILTER P l) = FILTER P (MAP f l)
Proof
  Induct_on `l` >> rw[DISJ_IMP_THM,FORALL_AND_THM]
QED

Theorem MAP_FST_remdups_distinct_keys:
  !l l'.
  MAP FST l = MAP FST l' /\
  (!m ws. MEM (m,ws) l' ==>
   !ws'. MEM (m,ws') l' ==> ws = ws') /\
  (!m ws. MEM (m,ws) l ==>
   !ws'. MEM (m,ws') l ==> ws = ws') ==>
  MAP FST(remdups l) = MAP FST(remdups l')
Proof
  Induct_on `l` >> Cases_on `l'` >> rw[remdups_def,MEM_MAP,MEM_FILTER,set_remdups] >>
  first_x_assum drule >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  fs[DISJ_IMP_THM,FORALL_AND_THM] >>
  `FILTER (λy. h ≠ y) (remdups t)
   = FILTER ((λy. y <> FST h) o FST) (remdups t)`
    by(rw[FILTER_EQ,set_remdups] >>
       CCONTR_TAC >> fs[] >>
       Cases_on `y` >> Cases_on `h` >> fs[] >>
       metis_tac[]) >>
  simp[] >> pop_assum kall_tac >>
  `FILTER (λy. h' ≠ y) (remdups l)
   = FILTER ((λy. y <> FST h) o FST) (remdups l)`
    by(rw[FILTER_EQ,set_remdups] >>
       CCONTR_TAC >> fs[] >>
       Cases_on `y` >> Cases_on `h'` >> fs[] >>
       metis_tac[]) >>
  simp[] >> pop_assum kall_tac >>
  simp[GSYM FILTER_MAP]
QED

Theorem W8ARRAYS_FILTER_EQ:
  ALL_DISTINCT l ==>
  W8ARRAY arg h * FOLDR $* emp
        (MAP (UNCURRY W8ARRAY)
             (FILTER ($<> (arg,h)) l)) =
  if MEM (arg,h) l then
    FOLDR $* emp
      (MAP (UNCURRY W8ARRAY) l)
  else
    W8ARRAY arg h * FOLDR $* emp
      (MAP (UNCURRY W8ARRAY) l)
Proof
  Induct_on `l` >>
  rw[] >> fs[] >>
  rename1 `UNCURRY W8ARRAY ah` >>
  Cases_on `ah` >>
  rw[] >>
  metis_tac[STAR_ASSOC,STAR_COMM]
QED

val W8ARRAYS_def =
Define `
 W8ARRAYS sigargs args wss =
  FOLDR STAR emp (MAP (UNCURRY W8ARRAY) (remdups(ZIP (get_mut_args sigargs args, wss))))`

Theorem W8ARRAYS_unique:
  W8ARRAYS sigargs argvs wss v /\ W8ARRAYS sigargs argvs wss v'
  ==> v = v'
Proof
  rw[W8ARRAYS_def] >>
  rename1 `remdups l` >>
  rpt(pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`v`,`v'`,`l`] >>
  Induct >- rw[remdups_def,emp_def] >>
  Cases >> rw[remdups_def] >>
  Q.ISPEC_THEN `l` assume_tac ALL_DISTINCT_remdups \\
  fs[W8ARRAYS_FILTER_EQ] \\
  PURE_FULL_CASE_TAC \\ fs[] \\ rveq \\
  fs[STAR_def,SPLIT_def] >> rveq >>
  first_x_assum (dxrule_all_then assume_tac) >> rveq >>
  fs[W8ARRAY_def,SEP_EXISTS,cell_def,cond_def,STAR_def,one_def,SPLIT_SING_2] >>
  fs[]
QED

val get_carg_heap_def = Define `
  (get_carg_heap _ (C_array conf) (Litv(StrLit s)) =
    if conf.mutable then
      NONE
    else
      SOME (C_arrayv(MAP (\ c .  n2w(ORD c)) (EXPLODE s))))
/\ (get_carg_heap (ws::_) (C_array conf) (Loc lnum) =
     if conf.mutable then
       SOME(C_arrayv ws)
     else NONE)
/\ (get_carg_heap _ C_bool v =
     if v = Boolv T then
       SOME(C_primv(C_boolv T))
     else if v = Boolv F then
       SOME(C_primv(C_boolv F))
     else NONE)
/\ (get_carg_heap _ C_int (Litv(IntLit n)) =
     SOME(C_primv(C_intv n)))
/\ (get_carg_heap _ _ _ = NONE)`

val get_cargs_heap_def = Define
  `(get_cargs_heap s [] [] = SOME [])
/\ (get_cargs_heap s (ty::tys) (arg::args) =
     OPTION_MAP2 CONS (get_carg_heap s ty arg)
                 (get_cargs_heap (if is_mutty ty then TL s else s) tys args))
/\ (get_cargs_heap _ _ _ = NONE)
`

val get_cargs_heap_ind = fetch "-" "get_cargs_heap_ind"

val app_ffi_def = Define `
  app_ffi ffi_index args H Q =
    ((?wss frame s u sign sigs cargs events.
         MEM sign sigs /\
         FIND (λx. x.mlname = sign.mlname) sigs = SOME sign /\
         ffi_index = sign.mlname /\
         LENGTH wss = LENGTH(get_mut_args sign.args args) /\
         (H ==>> frame * W8ARRAYS sign.args args wss * one (FFI_part s u sigs events) *
                 cond (FIND (λx. x.mlname = "") sigs = NONE) *
                 cond (get_cargs_heap wss sign.args args = SOME cargs)) /\
         (case u ffi_index cargs (als_args sign.args args) s of
            SOME(FFIreturn vs retv s') =>
             (frame * W8ARRAYS sign.args args vs * one (FFI_part s' u sigs
                 (events ++ [IO_event ffi_index cargs vs retv]))) ==>> Q (Val (get_ret_val retv))
          | SOME(FFIdiverge) =>
             (frame * W8ARRAYS sign.args args wss * one (FFI_part s u sigs events)) ==>> Q (FFIDiv ffi_index cargs)
          | NONE => F)) /\
     Q ==e> POST_F /\ Q ==d> POST_F)`

val cf_ffi_def = Define `
  cf_ffi ffi_index exps = \env. local (\H Q.
    ?args. exp2v_list env exps = SOME args /\
     app_ffi ffi_index args H Q)`

val cf_log_def = Define `
  cf_log lop e1 cf2 = \env. local (\H Q.
    ?v b.
      exp2v env e1 = SOME v /\
      BOOL b v /\
      (case (lop, b) of
           (And, T) => cf2 env H Q
         | (Or, F) => cf2 env H Q
         | (Or, T) => (H ==>> Q (Val v) /\ Q =~v> POST_F)
         | (And, F) => (H ==>> Q (Val v) /\ Q =~v> POST_F)))`

val cf_if_def = Define `
  cf_if cond cf1 cf2 = \env. local (\H Q.
    ?condv b.
      exp2v env cond = SOME condv /\
      BOOL b condv /\
      (b = T ==> cf1 env H Q) /\
      (b = F ==> cf2 env H Q))`

val cf_match_def = Define `
  cf_match e rows = \env. local (\H Q.
    ?v.
      exp2v env e = SOME v /\
      cf_cases v bind_exn_v rows env H Q)`

val cf_raise_def = Define `
  cf_raise e = \env. local (\H Q.
    ?v.
      exp2v env e = SOME v /\
      H ==>> Q (Exn v) /\
      Q =~e> POST_F)`

val cf_handle_def = Define `
  cf_handle Fe rows = \env. local (\H Q.
    ?Q'.
      (Fe env H Q' /\ Q' =~e> Q) /\
      (!ev. cf_cases ev ev rows env (Q' (Exn ev)) Q))`;

val cf_def = tDefine "cf" `
  cf (p:'ffi ffi_proj) (Lit l) = cf_lit l /\
  cf (p:'ffi ffi_proj) (Con opt args) = cf_con opt args /\
  cf (p:'ffi ffi_proj) (Var name) = cf_var name /\
  cf (p:'ffi ffi_proj) (Let opt e1 e2) =
    (if is_bound_Fun opt e1 then
       (case Fun_body e1 of
          | SOME body =>
            cf_fun (p:'ffi ffi_proj) (THE opt) (Fun_params e1)
              (cf (p:'ffi ffi_proj) body) (cf (p:'ffi ffi_proj) e2)
          | NONE => cf_bottom)
     else
       cf_let opt (cf (p:'ffi ffi_proj) e1) (cf (p:'ffi ffi_proj) e2)) /\
  cf (p:'ffi ffi_proj) (Letrec funs e) =
    (cf_fun_rec (p:'ffi ffi_proj)
       (MAP (\x. (x, cf p (SND (SND x)))) (letrec_pull_params funs))
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
        | Equality =>
          (case args of
            | [x1; x2] => cf_equality x1 x2
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
        | AallocEmpty =>
          (case args of
            | [u] => cf_aalloc_empty u
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
        | CopyAw8Aw8 =>
          (case args of
             | [s; so; l; d; do'] => cf_copyaw8aw8 s so l d do'
             | _ => cf_bottom)
        | CopyStrAw8 =>
          (case args of
             | [s; so; l; d; do'] => cf_copystraw8 s so l d do'
             | _ => cf_bottom)
        | CopyAw8Str =>
          (case args of
             | [s; so; l] => cf_copyaw8str s so l
             | _ => cf_bottom)
        | WordFromInt W8 =>
          (case args of
             | [i] => cf_wordFromInt_W8 i
             | _ => cf_bottom)
        | WordFromInt W64 =>
          (case args of
             | [i] => cf_wordFromInt_W64 i
             | _ => cf_bottom)
        | WordToInt W8 =>
          (case args of
             | [w] => cf_wordToInt_W8 w
             | _ => cf_bottom)
        | WordToInt W64 =>
          (case args of
             | [w] => cf_wordToInt_W64 w
             | _ => cf_bottom)
        | FFI ffi_index =>
          (cf_ffi ffi_index args)
        | _ => cf_bottom) /\
  cf (p:'ffi ffi_proj) (Log lop e1 e2) =
    cf_log lop e1 (cf p e2) /\
  cf (p:'ffi ffi_proj) (If cond e1 e2) =
    cf_if cond (cf p e1) (cf p e2) /\
  cf (p:'ffi ffi_proj) (Mat e branches) =
    cf_match e (MAP (\b. (FST b, cf p (SND b))) branches) /\
  cf (p:'ffi ffi_proj) (Raise e) = cf_raise e /\
  cf (p:'ffi ffi_proj) (Handle e branches) =
    cf_handle (cf p e) (MAP (\b. (FST b, cf p (SND b))) branches) /\
  cf (p:'ffi ffi_proj) (Lannot e _) = cf p e /\
  cf (p:'ffi ffi_proj) (Tannot e _) = cf p e /\
  cf _ _ = cf_bottom
`
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
     THEN1 (
       Induct_on `branches` \\ fs [MEM] \\ rpt strip_tac \\ rw [] \\
       fs [astTheory.exp_size_def]
     )
  )

val cf_ind = fetch "-" "cf_ind"

val cf_defs = [
  cf_def,
  cf_lit_def,
  cf_con_def,
  cf_var_def,
  cf_fun_def,
  cf_let_def,
  cf_opn_def,
  cf_opb_def,
  cf_equality_def,
  cf_aalloc_def,
  cf_aalloc_empty_def,
  cf_asub_def,
  cf_alength_def,
  cf_aupdate_def,
  cf_aw8alloc_def,
  cf_aw8sub_def,
  cf_aw8length_def,
  cf_aw8update_def,
  cf_copyaw8aw8_def,
  cf_copystraw8_def,
  cf_copyaw8str_def,
  cf_wordFromInt_W8_def,
  cf_wordFromInt_W64_def,
  cf_wordToInt_W8_def,
  cf_wordToInt_W64_def,
  cf_app_def,
  cf_ref_def,
  cf_assign_def,
  cf_deref_def,
  cf_fun_rec_def,
  cf_bottom_def,
  cf_log_def,
  cf_if_def,
  cf_match_def,
  cf_ffi_def,
  cf_raise_def,
  cf_handle_def
]

(*------------------------------------------------------------------*)
(** Properties about [cf]. The main result is the proof of soundness,
    [cf_sound] *)

Theorem cf_local:
   !e. is_local (cf (p:'ffi ffi_proj) e env)
Proof
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
QED

val cf_base_case_tac =
  HO_MATCH_MP_TAC sound_local \\ rewrite_tac [sound_def, htriple_valid_def, evaluate_to_heap_def] \\
  rpt strip_tac \\ Q.REFINE_EXISTS_TAC `Val v` \\
  simp [PULL_EXISTS] \\ fs [] \\ res_tac \\
  rename1 `SPLIT (st2heap _ st) (h_i, h_k)` \\
  progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
  simp [evaluate_ck_def, terminationTheory.evaluate_def, with_clock_self_eq] \\
  fs [SEP_IMP_def]

val cf_strip_sound_tac =
  TRY (HO_MATCH_MP_TAC sound_local) \\ rewrite_tac [sound_def, htriple_valid_def] \\
  rpt strip_tac \\ fs []

val cf_evaluate_step_tac =
  simp [evaluate_to_heap_def, evaluate_ck_def, terminationTheory.evaluate_def] \\
  fs [libTheory.opt_bind_def, PULL_EXISTS]

val cf_strip_sound_full_tac = cf_strip_sound_tac \\ cf_evaluate_step_tac

fun cf_exp2v_evaluate_tac st =
  rpt (
    first_x_assum (fn asm =>
      MATCH_MP exp2v_evaluate asm
      |> INST_TYPE [alpha |-> ``:'ffi``]
      |> Q.SPEC st
      |> assume_tac
    )
  ) \\ rw []

val DROP_EL_CONS = Q.prove (
  `!l n.
    n < LENGTH l ==>
    DROP n l = EL n l :: DROP (SUC n) l`,
  Induct \\ rpt strip_tac \\ fs [] \\ every_case_tac \\ fs [] \\
  Cases_on `n` \\ fs []
);

val FST_rw = Q.prove(
  `(\(x,_,_). x) = FST`,
  fs [FUN_EQ_THM,FORALL_PROD]);

val _ = print "Proving cf_letrec_sound_aux\n";
val cf_letrec_sound_aux = Q.prove (
  `!funs e.
     let naryfuns = letrec_pull_params funs in
     (∀x. MEM x naryfuns ==>
          sound (p:'ffi ffi_proj) (SND (SND x))
            (cf (p:'ffi ffi_proj) (SND (SND x)))) ==>
     sound (p:'ffi ffi_proj) e (cf (p:'ffi ffi_proj) e) ==>
     !fns rest.
       funs = rest ++ fns ==>
       let naryrest = letrec_pull_params rest in
       let naryfns = letrec_pull_params fns in
       sound (p:'ffi ffi_proj) (Letrec funs e)
         (\env H Q.
            let fvs = MAP (\ (f,_,_). naryRecclosure env naryfuns f) naryfuns in
            ALL_DISTINCT (MAP (\ (f,_,_). f) naryfuns) /\
            fun_rec_aux (p:'ffi ffi_proj)
              (MAP (\ (f,_,_). f) naryfuns) fvs
              (MAP (\ (_,ns,_). ns) naryfns)
              (DROP (LENGTH naryrest) fvs)
              (MAP (\x. cf (p:'ffi ffi_proj) (SND (SND x))) naryfns)
              (cf (p:'ffi ffi_proj) e) env H Q)`,
  rpt gen_tac \\ rpt (CONV_TAC let_CONV) \\ rpt DISCH_TAC \\ Induct
  THEN1 (
    rpt strip_tac \\ fs [letrec_pull_params_def, DROP_LENGTH_TOO_LONG] \\
    fs [fun_rec_aux_def] \\
    qpat_x_assum `_ = rest` (mp_tac o GSYM) \\ rw [] \\
    cf_strip_sound_full_tac \\ qpat_x_assum `sound _ e _` mp_tac \\
    fs [extend_env_rec_def] \\
    fs [letrec_pull_params_names, extend_env_rec_build_rec_env] \\
    rewrite_tac [sound_def, htriple_valid_def] \\ disch_then progress \\
    fs [evaluate_to_heap_def, evaluate_ck_def] \\ instantiate
  )
  THEN1 (
    qx_gen_tac `ftuple` \\ PairCases_on `ftuple` \\ rename1 `(f, n, body)` \\
    rpt strip_tac \\
    (* rest := rest ++ [(f,n,body)] *)
    (fn x => first_x_assum (qspec_then x mp_tac))
      `rest ++ [(f, n, body)]` \\ impl_tac THEN1 (fs []) \\ strip_tac \\
    qpat_x_assum `funs = _` (assume_tac o GSYM) \\ rpt (CONV_TAC let_CONV) \\
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
    qmatch_goalsub_abbrev_tac `fun_rec_aux _ _ _ (params::_)` \\
    (* unfold "sound _ (Letrec _ _)" in the goal *)
    cf_strip_sound_full_tac \\
    qpat_x_assum `fun_rec_aux _ _ _ _ _ _ _ _ _ _` mp_tac \\
    (* Rewrite (DROP _ _) to a (_::DROP _ _) *)
    qpat_abbrev_tac `til = DROP _ _` \\
    `til = (naryRecclosure env (letrec_pull_params funs) f) ::
            DROP (LENGTH (letrec_pull_params rest) + 1) fvs` by (
      qunabbrev_tac `til` \\ rewrite_tac [GSYM ADD1] \\
      fs [letrec_pull_params_LENGTH] \\
      mp_tac (Q.ISPECL [`fvs: v list`,
                        `LENGTH (rest: (tvarN, tvarN # exp) alist)`]
              DROP_EL_CONS) \\
      impl_tac THEN1 (
        qunabbrev_tac `fvs` \\ qpat_x_assum `_ = funs` (assume_tac o GSYM) \\
        fs [letrec_pull_params_LENGTH]
      ) \\
      fs [] \\ strip_tac \\ qunabbrev_tac `fvs` \\
      fs [letrec_pull_params_names] \\
      qpat_abbrev_tac `naryfuns = letrec_pull_params funs` \\
      `LENGTH rest < LENGTH funs` by (
        qpat_x_assum `_ = funs` (assume_tac o GSYM) \\ fs []) \\
      fs [EL_MAP] \\ qpat_x_assum `_ = funs` (assume_tac o GSYM) \\
      fs [el_append3, ADD1] \\ NO_TAC
    ) \\ fs [] \\
    (* We can now unfold fun_rec_aux *)
    fs [fun_rec_aux_def] \\ rewrite_tac [ONE] \\
    fs [LENGTH_CONS, LENGTH_NIL, PULL_EXISTS] \\
    fs [letrec_pull_params_LENGTH, letrec_pull_params_names] \\
    impl_tac

    THEN1 (
      sg `MEM (f, params, inner_body) (letrec_pull_params funs)`
      THEN1 (
        qpat_assum `_ = funs` (assume_tac o GSYM) \\
        fs [letrec_pull_params_append, letrec_pull_params_def] \\
        DISJ1_TAC \\ DISJ2_TAC \\
        Cases_on `Fun_body body` \\ fs []
      ) \\
      sg `find_recfun f (letrec_pull_params funs) = SOME (params, inner_body)`
      THEN1 (
        fs [semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] \\
        irule ALOOKUP_ALL_DISTINCT_MEM \\ fs [GSYM FST_rw] \\
        fs [letrec_pull_params_names]
      ) \\
      rpt strip_tac
      THEN1 (
        irule curried_naryRecclosure \\ fs []
      )
      THEN1 (
        sg `sound p inner_body (cf p inner_body)`
        THEN1 (first_assum progress \\ fs []) \\
        pop_assum (progress o REWRITE_RULE [sound_def]) \\
        irule app_rec_of_htriple_valid \\ fs [] \\
        qunabbrev_tac `params` \\ full_case_tac
      )
    ) \\ strip_tac \\
    qpat_x_assum `sound _ (Letrec _ _) _`
      (mp_tac o REWRITE_RULE [sound_def, htriple_valid_def]) \\
    fs [] \\ disch_then (qspecl_then [`env`, `H`, `Q`] mp_tac) \\
    fs [evaluate_to_heap_def, evaluate_ck_def] \\
    disch_then progress \\ instantiate \\
    rfs [terminationTheory.evaluate_def]
  ));

val _ = print "Proving cf_letrec_sound\n";
val cf_letrec_sound = Q.prove (
  `!funs e.
    (!x. MEM x (letrec_pull_params funs) ==>
         sound (p:'ffi ffi_proj) (SND (SND x))
           (cf (p:'ffi ffi_proj) (SND (SND x)))) ==>
    sound (p:'ffi ffi_proj) e (cf (p:'ffi ffi_proj) e) ==>
    sound (p:'ffi ffi_proj) (Letrec funs e)
      (\env H Q.
        let fvs = MAP
          (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f)
          funs in
        ALL_DISTINCT (MAP (\ (f,_,_). f) funs) /\
        fun_rec_aux (p:'ffi ffi_proj)
          (MAP (\ (f,_,_). f) funs) fvs
          (MAP (\ (_,ns,_). ns) (letrec_pull_params funs)) fvs
          (MAP (\x. cf (p:'ffi ffi_proj) (SND (SND x)))
             (letrec_pull_params funs))
          (cf (p:'ffi ffi_proj) e) env H Q)`,
  rpt strip_tac \\ mp_tac (Q.SPECL [`funs`, `e`] cf_letrec_sound_aux) \\
  fs [] \\ disch_then (qspecl_then [`funs`, `[]`] mp_tac) \\
  fs [letrec_pull_params_names, letrec_pull_params_def]
);

Theorem pmatch_NIL_IMP:
  (!envC refs p v env.
    pmatch envC [] p v env <> Match_type_error ==>
    pmatch envC refs p v env = pmatch envC [] p v env) /\
  (!envC refs ps vs env.
    pmatch_list envC [] ps vs env <> Match_type_error ==>
    pmatch_list envC refs ps vs env = pmatch_list envC [] ps vs env)
Proof
  ho_match_mp_tac pmatch_ind
  \\ fs [pmatch_def] \\ rw []
  \\ rpt (CASE_TAC \\ fs [store_lookup_def])
  \\ every_case_tac \\ fs []
QED

val _ = print "Proving cf_cases_evaluate_match\n";
val cf_cases_evaluate_match = Q.prove (
  `!v env H Q nomatch_exn rows p st h_i h_k.
    EVERY (\b. sound p (SND b) (cf p (SND b))) rows ==>
    cf_cases v nomatch_exn (MAP (\r. (FST r, cf p (SND r))) rows) env H Q ==>
    SPLIT (st2heap p st) (h_i, h_k) ==> H h_i ==>
    ?r h_f h_g heap.
      can_pmatch_all env.c st.refs (MAP FST rows) v /\
      SPLIT3 heap (h_f, h_k, h_g) /\
      Q r h_f /\
      case r of
        | Val v' => ?ck st'.
          evaluate_match (st with clock := ck) env v rows nomatch_exn =
          (st', Rval [v']) /\
          st2heap p st' = heap
        | Exn e => ?ck st'.
          evaluate_match (st with clock := ck) env v rows nomatch_exn =
          (st', Rerr (Rraise e)) /\
          st2heap p st' = heap
        | FFIDiv name args => ∃ck st'.
          evaluate_match (st with clock := ck) env v rows nomatch_exn =
          (st', Rerr (Rabort (Rffi_error (Final_event name args FFI_diverged)))) /\
          st2heap p st' = heap
        | Div io =>
          (∀ck. ?st'. evaluate_match (st with clock := ck) env v rows nomatch_exn =
              (st', Rerr (Rabort Rtimeout_error))) /\
          lprefix_lub$lprefix_lub (IMAGE (\ck. fromList (FST(evaluate_match (st with clock := ck) env v rows nomatch_exn)).ffi.io_events) UNIV) io`,

  Induct_on `rows` \\ rpt gen_tac
  \\ rpt (disch_then assume_tac)
  \\ fs [cf_cases_def,evaluatePropsTheory.can_pmatch_all_EVERY]
  THEN1 (
    fs [local_def] \\ first_x_assum progress \\
    fs [terminationTheory.evaluate_def] \\
    Q.REFINE_EXISTS_TAC `Exn v` \\ fs [] \\
    fs [STAR_def, STARPOST_def, SEP_IMPPOST_def, SEP_IMP_def] \\
    GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
    rename1 `SPLIT h_i (h1, h2)` \\ first_assum progress \\
    first_assum (qspecl_then [`Exn nomatch_exn`, `h_i`] mp_tac) \\
    impl_tac THEN1 instantiate \\ strip_tac \\ instantiate \\
    rename1 `SPLIT h_i (h1', h2')` \\ qexists_tac `h2'` \\ SPLIT_TAC
  ) \\

  fs [local_def] \\ first_x_assum progress \\
  rename1 `(H1 * H2) h_i` \\ fs [STAR_def] \\
  rename1 `H1 h1` \\ rename1 `H2 h2` \\
  fs [STARPOST_def, SEP_IMPPOST_def, SEP_IMP_def, STAR_def] \\
  `SPLIT (st2heap p st) (h1, h2 UNION h_k)` by SPLIT_TAC \\

  rename1 `v_of_pat_norest _ (FST row) _` \\ Cases_on `row` \\ fs [] \\
  rename1 `v_of_pat_norest _ pat _` \\ rename1 `sound _ row_cf _` \\
  first_assum (qspec_then `st.refs` assume_tac) \\
  qpat_x_assum `validate_pat _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [validate_pat_def]) \\
  simp [terminationTheory.evaluate_def] \\
  full_case_tac \\ fs []
  THEN1 ((* No_match *)
    every_case_tac \\ fs []
    THEN1 (progress v_of_pat_norest_pmatch \\ fs [])
    THEN1 (
      last_assum progress \\ qexists_tac `r` \\ instantiate \\
      first_assum (qspecl_then [`r`, `h_f UNION h2`] mp_tac) \\
      impl_tac THEN1 (instantiate \\ SPLIT_TAC) \\ strip_tac \\
      instantiate \\ fs [GC_def, SEP_EXISTS] \\
      rename1 `SPLIT (h_f UNION h2) (h_f', h_g')` \\
      qexists_tac `h_g UNION h_g'` \\ SPLIT_TAC
    )
  )
  THEN1 ((* Match_type_error *) fs [pat_typechecks_def]) \\
  (* Match *)
  every_case_tac \\ fs [] THEN_LT REVERSE_LT
  THEN1 (
    progress pmatch_v_of_pat_norest \\ fs [] \\ rw [] \\
    metis_tac []
  ) \\
  first_x_assum progress \\ progress pmatch_v_of_pat_norest \\ rw [] \\
  progress v_of_pat_norest_insts_unique \\
  pop_assum (qspecl_then [`insts`, `wildcards`] assume_tac) \\ rfs [] \\ rw [] \\
  qpat_x_assum `sound _ _ _`
    (assume_tac o REWRITE_RULE [sound_def, htriple_valid_def]) \\
  pop_assum progress \\
  progress v_of_pat_norest_insts_length \\
  fs [extend_env_def, extend_env_v_zip, evaluate_to_heap_def, evaluate_ck_def] \\ instantiate \\
  first_assum (qspecl_then [`r`, `h_f UNION h2`] mp_tac) \\
  impl_tac THEN1 (instantiate \\ SPLIT_TAC) \\ strip_tac \\
  instantiate \\ fs [GC_def, SEP_EXISTS] \\
  fs [MAP_MAP_o,o_DEF] \\
  rename1 `SPLIT (h_f UNION h2) (h_f', h_g')` \\
  qexists_tac `h_g UNION h_g'` \\
  reverse conj_tac THEN1 SPLIT_TAC \\
  fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS] \\ rw [] \\ res_tac \\
  imp_res_tac (CONJUNCT1 pmatch_NIL_IMP) \\ fs []);

Theorem FIND_signature_FFI_part:
  FIND (λx. x.mlname = sign.mlname) sigs = SOME sign /\
  FFI_part s u sigs events ∈ st2heap p st
  ==> FIND (λx. x.mlname = sign.mlname) st.ffi.signatures = SOME sign
Proof
  Cases_on `p` >> rw[st2heap_def,FFI_part_NOT_IN_store2heap,ffi2heap_def,parts_ok_def] >>
  imp_res_tac FIND_IMP_MEM >> res_tac
QED

Theorem get_cargs_heap_IMP_get_cargs_sem:
get_cargs_heap wss sign.args argvs = SOME cargs /\
W8ARRAYS sign.args argvs wss v /\
v ⊆ store2heap st.refs /\
LENGTH wss =  LENGTH (get_mut_args sign.args argvs)(* /\
parts_ok st.ffi p*)
==>
get_cargs_sem st.refs sign.args argvs = SOME cargs
Proof
  PURE_REWRITE_TAC[GSYM AND_IMP_INTRO,ffiTheory.get_mut_args_def,W8ARRAYS_def] \\
  rename1 `get_cargs_heap _ sargs` \\
  MAP_EVERY qid_spec_tac [`v`,`p`,`st`,`cargs`,`argvs`,`sargs`,`wss`] \\
  ho_match_mp_tac get_cargs_heap_ind \\
  rw[get_cargs_heap_def,get_cargs_sem_def]
  >- (Cases_on `wss` \\ fs[remdups_def] \\
      conj_tac >-
        (Cases_on `ty` >> Cases_on `arg` >> fs[fetch "-" "get_carg_heap_def",bool_case_eq] >>
         rveq >> fs[ffiTheory.is_mutty_def,fetch "-" "get_carg_heap_def"] >> rveq >>
         TRY(rename1 `Litv lv` >> Cases_on `lv` >> fs[fetch "-" "get_carg_heap_def"]) >>
         fs[get_carg_sem_def] >>
         fs[STAR_def,SPLIT_def,W8ARRAY_def,cell_def,SEP_EXISTS_THM,cond_def,one_def] >>
         rveq >> fs[UNION_SUBSET] >>
         imp_res_tac store2heap_IN_LENGTH >>
         imp_res_tac store2heap_IN_EL >>
         simp[store_lookup_def]
        ) >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      qmatch_asmsub_abbrev_tac `remdups a1` >>
      Q.ISPEC_THEN `a1` assume_tac ALL_DISTINCT_remdups >>
      fs[W8ARRAYS_FILTER_EQ] >>
      every_case_tac >> fs[STAR_def,SPLIT_def] >>
      asm_exists_tac >> simp[] >>
      rveq >> fs[UNION_SUBSET]
     ) >>
  conj_tac >-
    (Cases_on `ty` >> Cases_on `arg` >> fs[fetch "-" "get_carg_heap_def",bool_case_eq] >>
     rveq >> fs[ffiTheory.is_mutty_def,fetch "-" "get_carg_heap_def"] >> rveq >>
     TRY(rename1 `Litv lv` >> Cases_on `lv` >> fs[fetch "-" "get_carg_heap_def"]) >>
     fs[get_carg_sem_def] >> Cases_on `wss` >> fs[fetch "-" "get_carg_heap_def"]) >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  HINT_EXISTS_TAC >> simp[]
QED

Theorem W8ARRAYS_Mem:
  W8ARRAYS sign argvs wss v
  ==> !e. e IN v ==> ?rv x. e = Mem rv x
Proof
  rw[W8ARRAYS_def,FOLDR_MAP] >>
  rename1 `FOLDR _ _ l` >>
  rpt(pop_assum mp_tac) >>
  qid_spec_tac `v` >>
  Induct_on `l` >> rw[W8ARRAY_def,emp_def] >>
  qpat_x_assum `(_ * _) v` mp_tac >>
  PURE_ONCE_REWRITE_TAC [STAR_def] >>
  rw[SPLIT_def] >>
  fs[IN_UNION,ELIM_UNCURRY,emp_def] >>
  res_tac >>
  fs[W8ARRAY_def,STAR_def,SPLIT_def,SEP_EXISTS,cell_def,one_def,cond_def] >>
  rveq >> fs[]
QED

(* TODO: move *)
Theorem store_cargs_SOME_same_loc_alt =
  (semanticPrimitivesPropsTheory.store_cargs_SOME_same_loc
   |> SPEC_ALL |> Q.INST [`ty` |-> `sign.args`] |> REWRITE_RULE [] |> GEN_ALL)

val dest_loc_def = Define `
  loc_of(Loc loc) = loc`

Theorem get_cargs_heap_get_mut_args_loc:
  !wss sigargs argvs cargs.
  get_cargs_heap wss sigargs argvs = SOME cargs ==>
  !v. MEM v (get_mut_args sigargs argvs) ==> ?loc. v = Loc loc
Proof
  ho_match_mp_tac get_cargs_heap_ind \\
  rw[get_cargs_heap_def,ffiTheory.get_mut_args_def] \\
  fs[ffiTheory.is_mutty_def] \\ every_case_tac \\ fs[] \\
  Cases_on `arg` \\ fs[get_carg_heap_def] \\
  rename1 `Litv l` \\ Cases_on `l` \\ fs[get_carg_heap_def]
QED

Theorem W8ARRAYS_expl:
  LENGTH (get_mut_args sigargs argvs) = LENGTH vs /\
  (!v. MEM v (get_mut_args sigargs argvs) ==> ?loc. v = Loc loc)
  ==>
  W8ARRAYS sigargs argvs vs
          (set
             (MAP2 (λx y. Mem (loc_of x) (W8array y))
                (get_mut_args sigargs argvs) vs))
Proof
  rw[W8ARRAYS_def,MAP2_ZIP] >>
  `(!v. MEM v (MAP FST(ZIP(get_mut_args sigargs argvs,vs))) ==> ?loc. v = Loc loc)`
    by(rw[MEM_MAP] >> rfs[MEM_ZIP] >> metis_tac[EL_MEM]) >>
  pop_assum mp_tac >>
  rename1 `remdups a1` >> rpt(pop_assum kall_tac) >>
  Induct_on `a1`
  >- rw[remdups_def,emp_def] >>
  rw[remdups_def] >>
  Q.ISPEC_THEN `a1` assume_tac ALL_DISTINCT_remdups >>
  rename1 `UNCURRY W8ARRAY tup` >>
  Cases_on `tup` >>
  rename1 `UNCURRY W8ARRAY (arg,h)` >>
  drule W8ARRAYS_FILTER_EQ \\
  simp[] \\ disch_then kall_tac \\
  rw[]
  >- (drule_then assume_tac remdups_MEM \\
      `Mem (loc_of arg) (W8array h) IN (set (MAP (λ(x,y). Mem (loc_of x) (W8array y)) a1))`
        by(simp[MEM_MAP,ELIM_UNCURRY] \\ HINT_EXISTS_TAC \\ simp[]) \\
      imp_res_tac ABSORPTION \\ simp[]) \\
  simp[STAR_def,SPLIT_def,DISJOINT_DEF] \\
  qmatch_goalsub_abbrev_tac `a2 INSERT a3` \\
  qexists_tac `{a2}` \\
  qexists_tac `a3` \\
  unabbrev_all_tac \\
  simp[GSYM INSERT_SING_UNION] \\
  simp[W8ARRAY_def,SEP_EXISTS,cell_def,cond_def,one_def,STAR_def,SPLIT_def,DISJOINT_DEF] \\
  drule_then assume_tac (CONTRAPOS MEM_remdups) \\
  simp[INTER_DEF,MEM_MAP,PULL_EXISTS,ELIM_UNCURRY,FUN_EQ_THM] \\
  fs[DISJ_IMP_THM,FORALL_AND_THM,fetch "-" "loc_of_def"] \\
  rveq \\
  Cases \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[MEM_MAP,PULL_EXISTS] \\
  first_x_assum (drule_then strip_assume_tac) \\
  fs[fetch "-" "loc_of_def"]
QED

Theorem W8ARRAYS_eq_expl:
  W8ARRAYS sigargs argvs vs v /\
  LENGTH (get_mut_args sigargs argvs) = LENGTH vs /\
  (!v. MEM v (get_mut_args sigargs argvs) ==> ?loc. v = Loc loc)
  ==>
  v = (set
         (MAP2 (λx y. Mem (loc_of x) (W8array y))
           (get_mut_args sigargs argvs) vs))
Proof
  metis_tac[W8ARRAYS_unique,W8ARRAYS_expl]
QED

Theorem MEM_ZIP_SWAP_LEFT:
  !ll lr l r lr'.
  MEM (l,r) (ZIP (ll,lr)) /\
  LENGTH ll = LENGTH lr /\
  LENGTH lr = LENGTH lr' ==>
  ?r'. MEM (l,r') (ZIP(ll,lr'))
Proof
  Induct >> rw[] >> fs[] >>
  Cases_on `lr` >> Cases_on `lr'` >> fs[] >>
  metis_tac[]
QED

Theorem store_cargs_sem_update:
  !muts vs refs x.
  store_cargs_sem muts vs refs = SOME x /\ LENGTH muts = LENGTH vs /\
  (!v. MEM v muts ==> ?loc. v = Loc loc)
  ==>
  x = FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) refs (ZIP(muts,vs))
Proof
  ho_match_mp_tac store_cargs_sem_ind >>
  rw[store_cargs_sem_def,CaseEq "option"] >>
  Cases_on `marg` >>
  fs[store_carg_sem_def,DISJ_IMP_THM,FORALL_AND_THM,fetch "-" "loc_of_def",store_assign_def,
     store_v_same_type_def]
QED

(* TODO: move *)
Theorem get_cargs_sem_length:
  !st sigargs argvs cargs.
  get_cargs_sem st sigargs argvs = SOME cargs ==>
  LENGTH(mut_len sigargs cargs) =
  LENGTH(get_mut_args sigargs argvs)
Proof
  ho_match_mp_tac get_cargs_sem_ind >>
  rw[get_cargs_sem_def,ffiTheory.mut_len_def,ffiTheory.get_mut_args_def] >>
  rpt(PURE_FULL_CASE_TAC >> fs[ffiTheory.is_mutty_def] >> rveq) >> fs[]
QED

Theorem get_cargs_sem_length2:
  !st sigargs argvs cargs.
  get_cargs_sem st sigargs argvs = SOME cargs ==>
  LENGTH sigargs = LENGTH argvs /\
  LENGTH cargs = LENGTH argvs
Proof
  ho_match_mp_tac get_cargs_sem_ind >>
  rw[get_cargs_sem_def,ffiTheory.mut_len_def,ffiTheory.get_mut_args_def] >>
  rpt(PURE_FULL_CASE_TAC >> fs[ffiTheory.is_mutty_def] >> rveq) >> fs[]
QED

val LUPDATES_skip1 = Q.prove(`
  !l s x y.
  (!a b. MEM (a,b) l ==> !c. MEM (a,c) l ==> b = c) /\
  MEM (x,y) l
  ==>
  FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) (LUPDATE (W8array y) (loc_of x) s) l
  = FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) s l`,
  Induct >> rw[] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM,semanticPrimitivesPropsTheory.LUPDATE_LUPDATE_same] >>
  pairarg_tac >> fs[] >> rveq >>
  Cases_on `loc_of x = loc_of x'` >> fs[semanticPrimitivesPropsTheory.LUPDATE_LUPDATE_same] >>
  fs[LUPDATE_commutes] >>
  first_x_assum match_mp_tac >>
  rw[] >> metis_tac[]);

val LUPDATES_skip2 = Q.prove(`
  !l s x y.
  (!a b. MEM (a,b) l ==> !c. MEM (a,c) l ==> b = c) /\
  (∀a b. MEM (a,b) l ⇒ ∃loc. a = Loc loc)
  ==>
  FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) (LUPDATE (W8array y) (loc_of x) s) (FILTER (λy'. (x,y) ≠ y') l)
  = FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) (LUPDATE (W8array y) (loc_of x) s) l`,
  Induct >> rw[] >>
  fs[DISJ_IMP_THM,FORALL_AND_THM,IMP_CONJ_THM,semanticPrimitivesPropsTheory.LUPDATE_LUPDATE_same] >>
  TRY(pairarg_tac >> fs[] >> rveq) >>
  fs[] >> res_tac >> rveq >> rfs[] >>
  fs[semanticPrimitivesPropsTheory.LUPDATE_LUPDATE_same,LUPDATE_commutes] >>
  fs[semanticPrimitivesPropsTheory.LUPDATE_LUPDATE_same] >>
  fs[LUPDATE_commutes] >>
  (reverse(Cases_on `MEM (x,y) l`) >-
     (`FILTER (λy'. (x,y) ≠ y') l = l`
        by(rw[FILTER_EQ_ID,EVERY_MEM]) >>
      simp[] >>
      metis_tac[])) >>
  rveq >> res_tac >>
  rveq >> fs[fetch "-" "loc_of_def"] >>
  rename1 `MEM (Loc loco,y) l` >>
  `loco <> loc` by metis_tac[] >>
  fs[CONV_RULE(STRIP_QUANT_CONV (RAND_CONV SYM_CONV)) LUPDATE_commutes] >>
  first_x_assum(qspecl_then [`y`, `Loc loco`] mp_tac) >>
  fs[fetch "-" "loc_of_def"]);

val LUPDATES_skip3 = Q.prove(`
  !l s x y.
  (!a b. MEM (a,b) l ==> !c. MEM (a,c) l ==> b = c) /\
  (∀a b. MEM (a,b) l ⇒ ∃loc. a = Loc loc) /\
  MEM (x,y) l
  ==>
  FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) (LUPDATE (W8array y) (loc_of x) s) (FILTER (λy'. (x,y) ≠ y') l)
  = FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) s l`,
 metis_tac[LUPDATES_skip1,LUPDATES_skip2])

Theorem LUPDATES_remdups:
  !l s.
  (!a b. MEM (a,b) l ==> !c. MEM (a,c) l ==> b = c) /\
  (∀a b. MEM (a,b) l ⇒ ∃loc. a = Loc loc)
  ==>
  FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) s l
  = FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) s (remdups l)
Proof
  Induct >> rw[remdups_def] >>
  pairarg_tac >> rveq >>
  fs[DISJ_IMP_THM,FORALL_AND_THM,IMP_CONJ_THM] >>
  reverse(Cases_on `MEM (x,y) (remdups l)`) >-
    (`FILTER (λy'. (x,y) ≠ y') (remdups l) = remdups l`
       by(rw[FILTER_EQ_ID,EVERY_MEM]) >>
     simp[] >>
     metis_tac[]) >>
  imp_res_tac remdups_MEM >>
  drule_all LUPDATES_skip1 >>
  simp[] >> disch_then kall_tac >>
  last_x_assum(drule_all) >> simp[] >> disch_then kall_tac >>
  match_mp_tac EQ_SYM >>
  match_mp_tac LUPDATES_skip3 >>
  rfs[] >>
  metis_tac[remdups_MEM,MEM_remdups]
QED

Theorem als_ok_IMP_unique_keys:
  !vs sigargs argvs.
   als_ok vs (als_args sigargs argvs) /\
   LENGTH (get_mut_args sigargs argvs) = LENGTH vs /\
   LENGTH sigargs = LENGTH argvs ==>
   !m ws. MEM (m,ws) (ZIP (get_mut_args sigargs argvs,vs)) ==>
    !ws'. MEM (m,ws') (ZIP (get_mut_args sigargs argvs,vs)) ==>
     ws = ws'
Proof
  rw[ffiTheory.get_mut_args_def,ffiTheory.als_ok_def,ffiTheory.als_args_def,o_DEF,
     MAP_FILTER,EVERY_MAP,EVERY_MEM,MEM_MAP,PULL_EXISTS,ZIP_MAP,MEM_ZIP,MEM_FILTER,
     ELIM_UNCURRY,MEM_MAPi,PULL_FORALL,FORALL_PROD
    ] >>
  rfs[EL_MAP,FORALL_AND_THM] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `SND a1` >>
  qexists_tac `FST a1` >> simp[Abbr `a1`] >>
  ho_match_mp_tac (MEM_FILTER |> Ho_Rewrite.REWRITE_RULE[EQ_IMP_THM,FORALL_AND_THM] |> CONJUNCT1) >>
  simp[EL_MEM]
QED

Theorem store2heap_LUPDATES:
   !s v sigargs argvs wss vs.
      v SUBSET (store2heap s) /\ W8ARRAYS sigargs argvs wss v /\
      LENGTH (get_mut_args sigargs argvs) = LENGTH vs /\
      LENGTH (get_mut_args sigargs argvs) = LENGTH wss /\
      als_ok vs (als_args sigargs argvs) /\
      LENGTH sigargs = LENGTH argvs /\
      (∀v. MEM v (get_mut_args sigargs argvs) ⇒ ∃loc. v = Loc loc) ==>
      store2heap (FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) s
                 (ZIP (get_mut_args sigargs argvs,vs))) =
      set (MAP2 (λx y. Mem (loc_of x) (W8array y)) (get_mut_args sigargs argvs) vs)
       UNION (store2heap s DIFF v)
Proof
  rw[] \\
  drule_all_then assume_tac W8ARRAYS_eq_expl \\
  rveq \\
  qhdtm_x_assum `W8ARRAYS` kall_tac \\
  fs[MAP2_MAP] \\
  `!m ws. MEM (m,ws) (ZIP (get_mut_args sigargs argvs,wss)) ==> !ws'. MEM (m,ws') (ZIP (get_mut_args sigargs argvs,wss)) ==> ws = ws'`
    by(rw[] \\
       `?loc. m = Loc loc /\ Mem loc (W8array ws) IN store2heap s`
         by(imp_res_tac regexpTheory.MEM_ZIP_IMP >>
            res_tac >> rveq >>
            fs[SUBSET_DEF] >>
            first_x_assum match_mp_tac >>
            fs[MEM_MAP,ELIM_UNCURRY,EXISTS_PROD] >>
            metis_tac[fetch "-" "loc_of_def"]) \\
       `Mem loc (W8array ws') IN store2heap s`
         by(imp_res_tac regexpTheory.MEM_ZIP_IMP >>
            res_tac >> rveq >>
            fs[SUBSET_DEF] >>
            first_x_assum match_mp_tac >>
            fs[MEM_MAP,ELIM_UNCURRY,EXISTS_PROD] >>
            metis_tac[fetch "-" "loc_of_def"]) >>
       imp_res_tac store2heap_IN_unique_key >> fs[]) \\
  `!m ws. MEM (m,ws) (ZIP (get_mut_args sigargs argvs,vs)) ==> !ws'. MEM (m,ws') (ZIP (get_mut_args sigargs argvs,vs)) ==> ws = ws'`
    by(rw[] \\
       dxrule_then match_mp_tac als_ok_IMP_unique_keys \\
       simp[] \\ metis_tac[]) \\
  qpat_x_assum `LENGTH sigargs = LENGTH argvs` kall_tac \\
  qhdtm_x_assum `als_ok` kall_tac \\
  rename1 `ZIP (muts,_)` \\
  `MAP FST (ZIP(muts,vs)) = MAP FST (ZIP(muts,wss))` by fs[MAP_ZIP] \\
  drule_all_then assume_tac ALL_DISTINCT_remdups_distinct_keys \\
  drule_all_then assume_tac MAP_FST_remdups_distinct_keys \\
  `∀v. MEM v (MAP FST (remdups(ZIP (muts,wss)))) ⇒ ∃loc. v = Loc loc`
    by(fs[MEM_MAP,PULL_EXISTS,set_remdups,FORALL_PROD] \\ metis_tac[regexpTheory.MEM_ZIP_IMP]) \\
  rpt(qpat_x_assum `LENGTH _ = LENGTH _` kall_tac) \\
  qpat_x_assum `_ SUBSET _` mp_tac \\
  PURE_ONCE_REWRITE_TAC[GSYM set_remdups] \\
  `remdups (MAP (λ(x,y). Mem (loc_of x) (W8array y)) (ZIP (muts,vs))) =
   MAP (λ(x,y). Mem (loc_of x) (W8array y)) (remdups (ZIP (muts,vs)))
  `
    by(match_mp_tac remdups_MAP \\ rw[] \\ rpt(pairarg_tac \\ rveq >> fs[]) \\
       imp_res_tac regexpTheory.MEM_ZIP_IMP \\
       res_tac \\ rveq \\ fs[fetch "-" "loc_of_def"]) \\
  `remdups (MAP (λ(x,y). Mem (loc_of x) (W8array y)) (ZIP (muts,wss))) =
   MAP (λ(x,y). Mem (loc_of x) (W8array y)) (remdups (ZIP (muts,wss)))
  `
    by(match_mp_tac remdups_MAP \\ rw[] \\ rpt(pairarg_tac \\ rveq >> fs[]) \\
       imp_res_tac regexpTheory.MEM_ZIP_IMP \\
       res_tac \\ rveq \\ fs[fetch "-" "loc_of_def"]) \\
  simp[] \\
  ntac 2 (pop_assum kall_tac) \\
  strip_tac \\
  dxrule (INST_TYPE [alpha |-> ``:v``] LUPDATES_remdups) \\
  simp[GSYM PULL_FORALL] \\
  impl_tac >- (rw[] \\ imp_res_tac regexpTheory.MEM_ZIP_IMP \\ metis_tac[]) \\
  simp[] \\
  disch_then kall_tac \\
  qpat_x_assum `!v. MEM _ muts => _` kall_tac \\
  qpat_abbrev_tac `l1 = remdups(ZIP (muts,vs))` \\ pop_assum kall_tac \\
  qpat_abbrev_tac `l2 = remdups(ZIP (muts,wss))` \\ pop_assum kall_tac \\
  qpat_x_assum `!a b. _ ==> _` kall_tac \\
  qpat_x_assum `MAP FST (ZIP _) = _` kall_tac \\
  rpt(pop_assum mp_tac) \\
  SPEC_ALL_TAC \\
  ho_match_mp_tac SNOC_INDUCT \\
  rw[SNOC_APPEND,FOLDL_APPEND] \\
  Q.ISPEC_THEN `l2` assume_tac SNOC_CASES \\
  rpt(pairarg_tac \\ fs[] \\ rveq) \\
  fs[] \\
  rename1 `MAP FST l1 = MAP FST l2` \\
  fs[DISJ_IMP_THM,FORALL_AND_THM] \\ rveq \\
  fs[ALL_DISTINCT_APPEND,fetch "-" "loc_of_def"] \\
  first_x_assum(qspec_then `l2` mp_tac) \\ simp[] \\
  disch_then drule \\ strip_tac \\
  rename1 `Mem _ (W8array warr) ∈ store2heap s` \\
  `Mem loc (W8array warr) ∈ store2heap (FOLDL (λst (x,y). LUPDATE (W8array y) (loc_of x) st) s l1)`
    by(pop_assum kall_tac \\ rpt(pop_assum mp_tac) \\
       SPEC_ALL_TAC \\
       ho_match_mp_tac SNOC_INDUCT \\
       rw[SNOC_APPEND,FOLDL_APPEND] \\
       Q.ISPEC_THEN `l2` assume_tac SNOC_CASES \\
       rpt(pairarg_tac \\ fs[] \\ rveq) \\
       fs[] \\
       rename1 `MAP FST l1 = MAP FST l2` \\
       fs[DISJ_IMP_THM,FORALL_AND_THM] \\ rveq \\
       fs[ALL_DISTINCT_APPEND,fetch "-" "loc_of_def"] \\
       rpt(pairarg_tac \\ fs[] \\ rveq) \\
       fs[fetch "-" "loc_of_def"] \\
       first_assum drule \\
       disch_then(qspec_then `loc'` mp_tac) \\
       rpt(disch_then drule) \\
       simp[] \\ rpt(disch_then drule) \\
       strip_tac \\
       drule store2heap_LUPDATE \\ simp[] \\ disch_then kall_tac \\
       first_x_assum(match_mp_tac o MP_CANON) \\
       metis_tac[fetch "-" "loc_of_def"]) \\
  drule store2heap_LUPDATE \\
  simp[] \\ disch_then kall_tac \\
  rw[FUN_EQ_THM,EQ_IMP_THM] \\ fs[] \\ rpt(pairarg_tac \\ fs[] \\ rveq) \\
  disj2_tac \\ CCONTR_TAC \\ fs[] \\ rveq \\
  fs[MEM_MAP] \\ rpt(pairarg_tac \\ fs[] \\ rveq) \\
  rename1 `MEM (lc,warr) l1` \\
  `MEM lc (MAP FST l1)` by(fs[MEM_MAP,EXISTS_PROD] \\ metis_tac[]) \\
  rfs[PULL_EXISTS] \\
  res_tac \\
  fs[MEM_MAP,PULL_EXISTS] \\
  res_tac \\ fs[] \\ rveq \\
  metis_tac[fetch "-" "loc_of_def"]
QED


val _ = print "Proving cf_ffi_sound\n";
val cf_ffi_sound = Q.prove (
  `sound (p:'ffi ffi_proj) (App (FFI ffi_index) args) (\env. local (\H Q.
     ?argvs. exp2v_list env args = SOME argvs /\
            app_ffi ffi_index argvs H Q))`,
   cf_strip_sound_tac \\
   fs[app_ffi_def] \\
   FULL_CASE_TAC
   >- fs[] \\
   qmatch_asmsub_abbrev_tac `u ffi_index cargs a2 s = SOME a1` \\
   pop_assum kall_tac \\ reverse (Cases_on `a1`)
   THEN1 (
     qpat_assum `u ffi_index cargs a2 s = SOME FFIdiverge` kall_tac \\
     qexists_tac `FFIDiv ffi_index cargs` \\
     MAP_EVERY qexists_tac [`h_i`, `{}`, `st2heap p st`] \\
     conj_tac >- (res_tac >> fs[SPLIT3_def,SPLIT_def]) \\
     conj_tac >- (fs[SEP_IMP_def] \\ rfs[] \\
                  first_x_assum(match_mp_tac o MP_CANON) \\
                  first_x_assum drule \\
                  simp[cond_STAR]) \\
     cf_evaluate_step_tac \\
     MAP_EVERY qexists_tac [`st.clock`, `st`] \\
     fs [do_app_def,app_ffi_def,W8ARRAY_def] \\
     drule_then (qspec_then `st with clock := st.clock` assume_tac) exp2v_list_REVERSE \\
     fs [do_app_def,do_ffi_def,app_ffi_def,SEP_IMP_def,W8ARRAY_def,SEP_EXISTS] \\
     fs [STAR_def,cell_def,one_def,cond_def] \\
     first_assum progress \\ fs [SPLIT_emp1] \\ rveq \\
     fs [SPLIT_SING_2] \\ rveq \\
     `sign.mlname <> ""` by(CCONTR_TAC \\ fs[]) \\
     rw[mllistTheory.FIND_thm,ffiTheory.debug_sig_def] \\
     fs[SPLIT_emp2] \\
     rveq \\
     `FIND (λx. x.mlname = sign.mlname) st.ffi.signatures = SOME sign`
       by(`FFI_part s u sigs events ∈ st2heap p st`
            by(fs[INSERT_DEF,UNION_DEF,SPLIT_def,IN_DEF,GSPEC_ETA] \\ metis_tac[]) \\
          imp_res_tac FIND_signature_FFI_part) \\
     simp[] \\
     `v ⊆ store2heap st.refs`
       by(rw[SUBSET_DEF] >>
          drule_all_then strip_assume_tac (MP_CANON W8ARRAYS_Mem) >>
          rveq >> Cases_on `p` >>
          fs[st2heap_def,SPLIT_def,SUBSET_DEF,UNION_DEF,INSERT_DEF,GSPEC_ETA,FUN_EQ_THM] >>
          rename1 `Mem rv xx` >>
          rpt(first_x_assum(qspec_then `Mem rv xx` assume_tac)) >>
          rfs[IN_DEF] >> metis_tac[Mem_NOT_IN_ffi2heap,IN_DEF]) \\
     drule_all_then assume_tac get_cargs_heap_IMP_get_cargs_sem \\ simp[] \\
     simp[ffiTheory.call_FFI_def] \\
     fs [SEP_EXISTS_THM,cond_STAR] \\ rveq \\
     fs [one_def] \\ rveq \\
     fs [st2heap_def,
            FFI_split_NOT_IN_store2heap,
            FFI_part_NOT_IN_store2heap,
            FFI_full_NOT_IN_store2heap,Mem_NOT_IN_ffi2heap] \\
     fs [SPLIT_SING_2] \\ rveq \\
     `FFI_part s u sigs events IN store2heap st.refs ∪ ffi2heap p st.ffi` by SPLIT_TAC \\
     fs [FFI_part_NOT_IN_store2heap] \\
     pop_assum mp_tac \\
     PairCases_on `p` \\
     simp [Once ffi2heap_def] \\
     IF_CASES_TAC \\ fs [] \\ strip_tac \\
     first_assum drule \\ simp_tac std_ss [FLOOKUP_DEF] \\
     rpt strip_tac \\ rveq \\
     qpat_x_assum `parts_ok st.ffi (p0,p1)`
           (fn th => mp_tac th \\ assume_tac th) \\
     simp_tac std_ss [parts_ok_def] \\ strip_tac \\
     qpat_x_assum `!x. _ ==> _` kall_tac \\
     imp_res_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
     rpt(first_x_assum progress) \\
     fs[IMPLODE_EXPLODE_I,MAP_MAP_o,o_DEF,state_component_equality]
      ) \\
   rename1 `_ = SOME (FFIreturn vs retv s')` \\
   Q.REFINE_EXISTS_TAC `Val v` \\
   cf_evaluate_step_tac \\
   GEN_EXISTS_TAC "ck" `st.clock` \\
   drule_then (qspec_then `st with clock := st.clock` assume_tac) exp2v_list_REVERSE \\
   fs [with_clock_self] \\
   fs [do_app_def,do_ffi_def,app_ffi_def,SEP_IMP_def,W8ARRAY_def,SEP_EXISTS] \\
   fs [STAR_def,cell_def,one_def,cond_def] \\
   first_assum progress \\ fs [SPLIT_emp1] \\ rveq \\
   fs [SPLIT_SING_2] \\ rveq \\
   `sign.mlname <> ""` by(CCONTR_TAC \\ fs[]) \\
   rw[mllistTheory.FIND_thm,ffiTheory.debug_sig_def] \\
   fs[SPLIT_emp2] \\
     rveq \\
     `FIND (λx. x.mlname = sign.mlname) st.ffi.signatures = SOME sign`
       by(`FFI_part s u sigs events ∈ st2heap p st`
            by(fs[INSERT_DEF,UNION_DEF,SPLIT_def,IN_DEF,GSPEC_ETA] \\ metis_tac[]) \\
          imp_res_tac FIND_signature_FFI_part) \\
     simp[] \\
     `v ⊆ store2heap st.refs`
       by(rw[SUBSET_DEF] >>
          drule_all_then strip_assume_tac (MP_CANON W8ARRAYS_Mem) >>
          rveq >> Cases_on `p` >>
          fs[st2heap_def,SPLIT_def,SUBSET_DEF,UNION_DEF,INSERT_DEF,GSPEC_ETA,FUN_EQ_THM] >>
          rename1 `Mem rv xx` >>
          rpt(first_x_assum(qspec_then `Mem rv xx` assume_tac)) >>
          rfs[IN_DEF] >> metis_tac[Mem_NOT_IN_ffi2heap,IN_DEF]) \\
   drule_all_then assume_tac get_cargs_heap_IMP_get_cargs_sem \\ simp[] \\
   simp[ffiTheory.call_FFI_def] \\
   fs [SEP_EXISTS_THM,cond_STAR] \\ rveq \\
   fs [one_def] \\ rveq \\
   fs [st2heap_def,
       FFI_split_NOT_IN_store2heap,
       FFI_part_NOT_IN_store2heap,
       FFI_full_NOT_IN_store2heap,Mem_NOT_IN_ffi2heap] \\
   fs [SPLIT_SING_2] \\ rveq \\
   `FFI_part s u sigs events IN store2heap st.refs ∪ ffi2heap p st.ffi` by SPLIT_TAC \\
   fs [FFI_part_NOT_IN_store2heap] \\
   pop_assum mp_tac \\
   PairCases_on `p` \\
   simp [Once ffi2heap_def] \\
   IF_CASES_TAC \\ fs [] \\ strip_tac \\
   first_assum drule \\ simp_tac std_ss [FLOOKUP_DEF] \\
   rpt strip_tac \\ rveq \\
   qpat_x_assum `parts_ok st.ffi (p0,p1)`
         (fn th => mp_tac th \\ assume_tac th) \\
   simp_tac std_ss [parts_ok_def] \\ strip_tac \\
   qpat_x_assum `!x. _ ==> _` kall_tac \\
   `sign.mlname ≠ ""` by (strip_tac \\ fs []) \\ fs [] \\
   imp_res_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
   first_x_assum progress \\
   first_x_assum(qspecl_then [`st.ffi.ffi_state`,`a2`] mp_tac) \\
   simp[] \\ rpt strip_tac \\ simp[] \\
   drule_then (qspec_then `vs` assume_tac) store_cargs_SOME_same_loc_alt \\
   fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] \\
   rename1 `frame u2` \\
   qabbrev_tac `events1 = (FILTER (ffi_has_index_in (MAP (λx. x.mlname) sigs)) st.ffi.io_events)` \\
   qabbrev_tac `new_events = events1 ++ [IO_event
                                           sign.mlname
                                           cargs
                                           vs
                                           retv]` \\
   qexists_tac `
      (FFI_part s' u sigs new_events INSERT
       (set(MAP2 (λx y. Mem (loc_of x) (W8array y)) (get_mut_args sign.args argvs) vs)
        UNION u2))` \\
   qexists_tac `{}` \\
   `SPLIT (store2heap st.refs UNION ffi2heap (p0,p1) st.ffi)
    (v UNION u2 UNION h_k,
     {FFI_part (FST(p0 st.ffi.ffi_state ' sign.mlname)) u sigs events1}) /\
     SPLIT (store2heap st.refs UNION ffi2heap (p0,p1) st.ffi)
     (v,
      u2 UNION h_k UNION
      {FFI_part (FST(p0 st.ffi.ffi_state ' sign.mlname)) u sigs events1})` by SPLIT_TAC \\
   fs [GSYM st2heap_def] \\
   drule SPLIT_FFI_SET_IMP_DISJOINT \\
   drule(GEN_ALL SPLIT_Mem_IMP_Mem_NOT_IN) \\
   ntac 2 strip_tac \\
   reverse conj_tac >-
     (first_x_assum match_mp_tac \\
      qexists_tac `set(MAP2 (λx y. Mem (loc_of x) (W8array y)) (get_mut_args sign.args argvs) vs)
                   UNION u2` \\
      simp[] \\
      imp_res_tac store_cargs_sem_refs_length_eq \\
      imp_res_tac get_cargs_sem_length \\
      rpt conj_tac
      >- (rfs[] >> fs[MAP2_ZIP,MEM_MAP,ELIM_UNCURRY])
      >- rfs[]
      >- (rfs[] >> fs[SPLIT_def] >> rveq >>
          qmatch_goalsub_abbrev_tac `as1 UNION as2` \\
          MAP_EVERY qexists_tac [`as2`,`as1`] \\
          MAP_EVERY qunabbrev_tac [`as2`,`as1`] \\
          simp[UNION_COMM] \\
          reverse conj_tac >-
            (match_mp_tac W8ARRAYS_expl \\
             rw[] \\
             drule_then assume_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
             metis_tac[get_cargs_heap_get_mut_args_loc]) \\
          drule W8ARRAYS_eq_expl \\
          impl_tac >-
            (simp[] \\ rw[] \\
             drule_then assume_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
             metis_tac[get_cargs_heap_get_mut_args_loc]) \\
          strip_tac \\
          rveq \\
          simp[REWRITE_RULE [Once DISJOINT_SYM] DISJOINT_ALT] \\
          qpat_x_assum `LENGTH wss = LENGTH _` assume_tac \\
          fs[MAP2_ZIP,MEM_MAP,ELIM_UNCURRY,PULL_EXISTS] \\
          rw[] \\
          rename1 `Mem (loc_of (FST vw))` \\
          Cases_on `vw` \\
          rename1 `FST(v,warr)` \\
          simp[] \\
          drule (REWRITE_RULE [Once CONJ_SYM] MEM_ZIP_MEM_MAP) \\
          impl_tac >- fs[] \\
          simp[] \\ strip_tac \\
          drule (INST_TYPE [gamma |-> ``:word8 list``] MEM_ZIP_SWAP_LEFT) \\
          simp[] \\
          disch_then(qspec_then `wss` mp_tac) \\
          impl_tac >- simp[] \\
          strip_tac \\
          first_x_assum dxrule \\
          simp[])) \\
   simp[SPLIT3_emp3] \\
   imp_res_tac store_cargs_sem_refs_length_eq \\
   imp_res_tac get_cargs_sem_length \\
   drule store_cargs_sem_update \\
   impl_tac >-
     (rfs[] \\ rw[] \\
      drule_then assume_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
      metis_tac[get_cargs_heap_get_mut_args_loc]) \\
   strip_tac \\
   rveq \\
   drule store2heap_LUPDATES \\
   disch_then drule \\
   disch_then(qspec_then `vs` mp_tac) \\
   impl_tac >-
     (simp[] \\ rfs[] \\ fs[ffiTheory.args_ok_def] \\
      imp_res_tac LIST_REL_LENGTH \\ fs[] \\
      imp_res_tac get_cargs_sem_length2 \\ fs[] \\
      metis_tac[get_cargs_heap_get_mut_args_loc]) \\
   simp[] \\ disch_then kall_tac \\
   qpat_abbrev_tac `f1 = ffi2heap (p0,p1) _` \\
   sg `f1 = (ffi2heap (p0,p1) st.ffi DELETE
          FFI_part (FST(p0 st.ffi.ffi_state ' sign.mlname)) u sigs events1)
         UNION {FFI_part s' u sigs new_events}` THEN1
     (unabbrev_all_tac \\ fs [ffi2heap_def] \\
      reverse IF_CASES_TAC THEN1
       (sg `F` \\ pop_assum mp_tac \\ fs [] \\
        fs [parts_ok_def] \\ conj_tac THEN1
         (fs [ffi_has_index_in_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
          \\ qexists_tac `sign` \\ fs[]
          \\ asm_exists_tac \\ fs [])
        \\ reverse(rpt conj_tac)
        >- metis_tac[]
        >- metis_tac[]
        >- (rw [] \\ qpat_x_assum `_ = p0 y` (fn th => fs [GSYM th])
            \\ Cases_on `sigs = sigs'` \\ fs [] THEN1
            (rveq
             \\ `ALL_DISTINCT (MAP (λn. n.mlname) sigs)`
                 by(fs[MAP_FLAT,MAP_MAP_o] \\
                    imp_res_tac ALL_DISTINCT_FLAT_EVERY \\
                    fs[EVERY_MEM,o_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD] \\
                    metis_tac[])
             \\ fs[FLOOKUP_FUPDATE_mlname_LIST]
             \\ fs[MEM_ALL_DISTINCT_FIND]
             \\ metis_tac[])
           \\ qpat_assum `∀ns u. MEM (ns,u) p1 ⇒ _` drule
           \\ rw[] \\ qexists_tac `s''` \\ rw []
           \\ `ALL_DISTINCT (MAP (λn. n.mlname) sigs)`
                 by(fs[MAP_FLAT,MAP_MAP_o] \\
                    imp_res_tac ALL_DISTINCT_FLAT_EVERY \\
                    fs[EVERY_MEM,o_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD] \\
                    metis_tac[])
           \\ fs [FLOOKUP_FUPDATE_mlname_LIST]
           \\ rw[CaseEq "option"]
           \\ disj1_tac \\ CCONTR_TAC
           \\ fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
           \\ imp_res_tac FIND_IMP_MEM
           \\ imp_res_tac FIND_IMP_pred
           \\ fs[]
           \\ fs[MAP_FLAT,MAP_MAP_o]
           \\ metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP])
        >- metis_tac[]) \\
      `ALL_DISTINCT (MAP (λn. n.mlname) sigs)`
        by(fs[MAP_FLAT,MAP_MAP_o] \\
           imp_res_tac ALL_DISTINCT_FLAT_EVERY \\
           fs[EVERY_MEM,o_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD] \\
           metis_tac[]) \\
      fs [EXTENSION] \\ reverse (rw [] \\ EQ_TAC \\ rw [] \\ rw[])
      THEN1
       (qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC >-
          (fs[FIND_NONE_EXISTS,EVERY_MEM] >> metis_tac[]) \\
        imp_res_tac FIND_IMP_MEM \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        imp_res_tac ALL_DISTINCT_FLAT_EVERY \\
        fs[EVERY_MEM,MEM_MAP,o_DEF,PULL_EXISTS] \\
        first_x_assum progress \\
        imp_res_tac FIND_IMP_pred \\
        fs[] \\
        Q.ISPEC_THEN `(λx. x.mlname)` match_mp_tac (GEN_ALL ALL_DISTINCT_MAP_MEM) \\
        metis_tac[])
      THEN1
       (qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC >-
          (fs[FIND_NONE_EXISTS,EVERY_MEM] >> metis_tac[]) \\
        imp_res_tac FIND_IMP_MEM \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        imp_res_tac ALL_DISTINCT_FLAT_EVERY \\
        fs[EVERY_MEM,MEM_MAP,o_DEF,PULL_EXISTS] \\
        first_x_assum progress \\
        imp_res_tac FIND_IMP_pred \\
        fs[] \\
        Q.ISPEC_THEN `(λx. x.mlname)` match_mp_tac (GEN_ALL ALL_DISTINCT_MAP_MEM) \\
        metis_tac[])
      THEN1
       (`sigs <> sigs'` by(CCONTR_TAC >> fs[]) \\
        qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC \\
        imp_res_tac FIND_IMP_MEM \\
        imp_res_tac FIND_IMP_pred \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP])
      THEN1
       (`sigs <> sigs'` by(CCONTR_TAC \\ fs[])
        \\ fs [FLOOKUP_FUPDATE_LIST,FILTER_APPEND,ffi_has_index_in_def]
        \\ TOP_CASE_TAC
        \\ fs[MEM_MAP,PULL_EXISTS]
        \\ fs[MAP_FLAT,MAP_MAP_o]
        \\ metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP])
      THEN1
       (`sigs <> sigs'` by(CCONTR_TAC >> fs[]) \\
        qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC \\
        imp_res_tac FIND_IMP_MEM \\
        imp_res_tac FIND_IMP_pred \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP])
      THEN1
       (`sigs <> sigs'` by(CCONTR_TAC \\ fs[])
        \\ fs [FLOOKUP_FUPDATE_LIST,FILTER_APPEND,ffi_has_index_in_def]
        \\ TOP_CASE_TAC
        \\ fs[MEM_MAP,PULL_EXISTS]
        \\ fs[MAP_FLAT,MAP_MAP_o]
        \\ metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP])
      THEN1
       (qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC \\
        imp_res_tac FIND_IMP_MEM \\
        imp_res_tac FIND_IMP_pred \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP2])
      THEN1
       (fs [FLOOKUP_FUPDATE_LIST,FILTER_APPEND,ffi_has_index_in_def]
        \\ TOP_CASE_TAC
        \\ fs[MEM_MAP,PULL_EXISTS]
        \\ fs[MAP_FLAT,MAP_MAP_o]
        \\ metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP2])
      THEN1
       (qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC \\
        imp_res_tac FIND_IMP_MEM \\
        imp_res_tac FIND_IMP_pred \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        reverse conj_asm2_tac >- metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP3] \\
        rveq \\
        `sigs = sigs'` by(metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP]) \\
        rveq \\
        qpat_x_assum `MEM sign sigs` assume_tac \\
        first_x_assum drule \\
        qpat_x_assum `_ ' _ = _` mp_tac \\
        fs[flookup_thm])
      THEN1
       (qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th]) \\
        fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def,MEM_MAP] \\
        TOP_CASE_TAC \\
        imp_res_tac FIND_IMP_MEM \\
        imp_res_tac FIND_IMP_pred \\
        fs[MAP_FLAT,MAP_MAP_o] \\
        `sigs = sigs'` by(metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP]) \\
        rveq \\
        qpat_x_assum `MEM sign sigs` assume_tac \\
        first_x_assum drule \\
        qpat_x_assum `_ ' _ = _` mp_tac \\
        fs[flookup_thm])
      \\ Cases_on `sigs = sigs'` \\ fs [] THEN1
       (rveq  \\ first_x_assum drule
        \\ qpat_x_assum `_ = p0 y'` (fn th => fs [GSYM th])
        \\ fs [FLOOKUP_FUPDATE_mlname_LIST] \\ rw [] \\ disj2_tac
        \\ fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def]
        \\ `u = u'` by(fs[MAP_FLAT,MAP_MAP_o] \\ metis_tac[GEN_ALL ALL_DISTINCT_FLAT_MAP_FST_IMP2])
        \\ rw[MEM_MAP,PULL_EXISTS] \\ metis_tac[])
      \\ fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def]
      \\ conj_tac >- (rw[MEM_MAP,PULL_EXISTS] \\ fs[MAP_FLAT,MAP_MAP_o] \\
                      metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP])
      \\ rw [] \\ first_assum drule
      \\ qpat_x_assum `_ = p0 y'` (fn th => simp_tac std_ss [GSYM th])
      \\ fs [FLOOKUP_FUPDATE_mlname_LIST,FILTER_APPEND,ffi_has_index_in_def]
      \\ TOP_CASE_TAC
      \\ imp_res_tac FIND_IMP_MEM
      \\ imp_res_tac FIND_IMP_pred
      \\ fs[MAP_FLAT,MAP_MAP_o]
      \\ metis_tac[ALL_DISTINCT_FLAT_MAP_FST_IMP]) \\
   pop_assum (fn th => simp [th]) \\
   pop_assum kall_tac \\
   fs [st2heap_def] \\
   simp [SPLIT_def] \\ reverse (rw [])
   THEN1 SPLIT_TAC
   THEN1 (rw[IN_DISJOINT] \\ rfs[] \\ fs[MAP2_ZIP] \\
          spose_not_then strip_assume_tac \\
          fs[MEM_MAP,PULL_EXISTS] \\ pairarg_tac \\ rveq \\ fs[] \\
          rename1 `MEM (lx,wx) _` \\
          `?wx'. Mem (loc_of lx) (W8array wx') IN v`
            by(drule W8ARRAYS_eq_expl \\
               impl_tac >-
                 (simp[] \\ rw[] \\
                  drule_then assume_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
                  metis_tac[get_cargs_heap_get_mut_args_loc]) \\
                  rw[] \\ fs[MAP2_ZIP] \\
                  simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] \\
                  CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac `lx` \\ simp[] \\
                  fs[MEM_EL] \\
                  CONV_TAC(SWAP_EXISTS_CONV) \\ rename1 `idx < LENGTH vs` \\ qexists_tac `idx` \\
                  rfs[] \\ fs[EL_ZIP] \\ rfs[EL_ZIP]) \\
          SPLIT_TAC) \\
   fs [EXTENSION] \\ rw [] \\ EQ_TAC \\ rw [] \\ fs []
   THEN1 SPLIT_TAC
   THEN1 SPLIT_TAC
   THEN1
     (CCONTR_TAC \\ fs [] \\
      `x = FFI_part (FST(p0 st.ffi.ffi_state ' sign.mlname)) u sigs events1` by SPLIT_TAC \\
      rveq \\ fs [FFI_part_NOT_IN_store2heap]
     )
   THEN1
     (CCONTR_TAC \\ fs [] \\
      `x IN u2 ∪ h_k ∪ {FFI_part (FST(p0 st.ffi.ffi_state ' sign.mlname)) u sigs events1}
         UNION v` by SPLIT_TAC \\
      pop_assum mp_tac \\
      fs [] \\
      drule W8ARRAYS_eq_expl \\
      impl_tac >-
        (simp[] \\ rw[] \\
         drule_then assume_tac semanticPrimitivesPropsTheory.get_cargs_sem_SOME_IMP_args_ok \\
         metis_tac[get_cargs_heap_get_mut_args_loc]) \\
      rw[] \\ fs[MAP2_ZIP] \\
      fs[ffi2heap_def] \\ rfs[MEM_MAP,ELIM_UNCURRY]
     ));

val _ = print "Proving evaluate_add_to_clock_lemma\n";
val evaluate_add_to_clock_lemma = Q.prove (
  `!extra p (s: 'ffi semanticPrimitives$state) s' r e.
     evaluate s e p = (s', r) ==>
     r <> Rerr (Rabort Rtimeout_error) ==>
     evaluate (s with clock := s.clock + extra) e p =
     (s' with clock := s'.clock + extra, r)`,
  fs [evaluatePropsTheory.evaluate_add_to_clock]
);

val _ = print "Proving evaluate_match_add_to_clock_lemma\n";
val evaluate_match_add_to_clock_lemma = Q.prove (
  `!extra (s: 'ffi semanticPrimitives$state) env v rows err_v s' r.
     evaluate_match s env v rows err_v = (s', r) ==>
     r <> Rerr (Rabort Rtimeout_error) ==>
     evaluate_match (s with clock := s.clock + extra) env v rows err_v =
     (s' with clock := s'.clock + extra, r)`,
  fs [evaluatePropsTheory.evaluate_match_add_to_clock]
);

fun add_to_clock qtm th g =
  ((fn g =>
      progress_with_then (qspec_then qtm assume_tac)
        th evaluate_add_to_clock_lemma g)
   ORELSE
   (fn g =>
      progress_with_then (qspec_then qtm assume_tac)
        th evaluate_match_add_to_clock_lemma g))
  g;

Theorem lprefix_lub_subset:
   lprefix_lub$lprefix_lub s l /\ s SUBSET t /\
   (!x. x IN t /\ ~(x IN s) ==> ?y. y IN s /\ LPREFIX x y) ==>
   lprefix_lub$lprefix_lub t l
Proof
  fs [lprefix_lubTheory.lprefix_lub_def] \\ rw []
  THEN1 (
    Cases_on `ll IN s`
    THEN1 (last_x_assum irule \\ rw [])
    \\ first_x_assum (qspec_then `ll` mp_tac) \\ rw []
    \\ last_x_assum (qspec_then `y` mp_tac) \\ rw []
    \\ irule LPREFIX_TRANS \\ instantiate)
  \\ last_x_assum irule \\ rw []
  \\ first_x_assum irule \\ fs [SUBSET_DEF]
QED

Theorem LPREFIX_fromList_fromList:
   LPREFIX (fromList x) (fromList y) = (x ≼ y)
Proof
  rw [LPREFIX_def, from_toList]
QED

Theorem isPREFIX_TRANS:
   !x y z. x ≼ y /\ y ≼ z ==> x ≼ z
Proof
  Induct_on `x` \\ Induct_on `y` \\ Induct_on `z`
  \\ fs [isPREFIX] \\ rw []
  \\ last_x_assum irule
  \\ instantiate
QED

Theorem can_pmatch_all_NIL_IMP:
  !ps envC v.
    can_pmatch_all envC [] ps v ==>
    ∀refs. can_pmatch_all envC refs ps v
Proof
  fs [evaluatePropsTheory.can_pmatch_all_EVERY,EVERY_MEM]
  \\ rw [] \\ res_tac \\ fs [pmatch_NIL_IMP]
QED

Theorem cf_sound:
   !p e. sound (p:'ffi ffi_proj) e (cf (p:'ffi ffi_proj) e)
Proof
  recInduct cf_ind \\ rpt strip_tac \\
  rewrite_tac cf_defs \\ fs [sound_local, sound_false]

  THEN1 (* Lit *) cf_base_case_tac

  THEN1 (
    (* Con *)
    cf_base_case_tac \\ progress exp2v_list_REVERSE \\
    fs [with_clock_self_eq]
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
      THEN1
       (rw []
        \\ qpat_assum `sound _ inner_body _`
             (assume_tac o REWRITE_RULE [sound_def])
        \\ pop_assum progress
        \\ irule app_of_htriple_valid
        \\ fs [Fun_params_def]) \\
      qpat_x_assum `sound _ e2 _`
        (progress o REWRITE_RULE [sound_def, htriple_valid_def]) \\
      qexists_tac `r` \\ Cases_on `r` \\ fs [] \\
      cf_evaluate_step_tac \\ Cases_on `opt` \\
      fs [is_bound_Fun_def, THE_DEF, Fun_params_def, evaluate_to_heap_def] \\ instantiate \\
      every_case_tac \\ fs[] \\ qpat_x_assum `_ = inner_body` (assume_tac o GSYM) \\
      fs [naryClosure_def, naryFun_def, Fun_params_Fun_body_NONE] \\
      fs [Fun_params_Fun_body_repack, evaluate_ck_def, terminationTheory.evaluate_def] \\
      fs [namespaceTheory.nsOptBind_def] \\
      instantiate
    )
    THEN1 (
      (* other cases of let-binding *)
      cf_strip_sound_full_tac \\
      qpat_x_assum `sound _ e1 _`
        (progress o REWRITE_RULE [sound_def, htriple_valid_def]) \\
      Cases_on `r` \\ fs [evaluate_to_heap_def, evaluate_ck_def]
      THEN1 (
        (* e1 ~> Rval v *)
        rename1 `evaluate _ _ [e1] = (_, Rval [v])` \\
        first_x_assum (qspec_then `v` assume_tac) \\
        progress SPLIT_of_SPLIT3_2u3 \\
        fs [sound_def, htriple_valid_def] \\
        first_x_assum (qspecl_then
          [`env with v := nsOptBind opt v env.v`, `Q' (Val v)`, `Q`]
          mp_tac) \\ rw [] \\
        first_x_assum (qspecl_then
          [`st'`, `h_f`, `h_k UNION h_g`] mp_tac) \\ rw [] \\
        fs [evaluate_to_heap_def, evaluate_ck_def] \\
        qexists_tac `r` \\ reverse (Cases_on `r`) \\ fs []
        THEN1 (
          `SPLIT3 heap (h_f',h_k, h_g UNION h_g')`
            by SPLIT_TAC
          \\ rveq \\ instantiate \\ rpt strip_tac
          THEN1 (
            drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
            \\ disch_then (qspec_then `ck'` strip_assume_tac) \\ fs []
          )
          \\ match_mp_tac (GEN_ALL lprefix_lub_subset)
          \\ asm_exists_tac \\ simp [SUBSET_DEF]
          \\ rw []
          THEN1 (
            drule evaluatePropsTheory.evaluate_set_clock \\ fs []
            \\ disch_then (qspec_then `ck'` strip_assume_tac)
            \\ qexists_tac `ck1` \\ fs [])
          \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
          \\ disch_then (qspec_then `ck'` mp_tac) \\ rw []
          THEN1 (first_x_assum (qspec_then `ck''` mp_tac) \\ fs [])
          \\ fs []
          \\ last_x_assum (qspec_then `ck2` strip_assume_tac)
          \\ rename1 `_ = (st2, _)`
          \\ qexists_tac `fromList st2.ffi.io_events` \\ rw []
          THEN1 (qexists_tac `ck2` \\ rw [])
          \\ `st'.ffi.io_events ≼ st2.ffi.io_events` by (
            drule (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono_imp)
            \\ rw [evaluatePropsTheory.io_events_mono_def])
          \\ rw [LPREFIX_fromList_fromList]
          \\ irule isPREFIX_TRANS
          \\ instantiate
          \\ fs [evaluatePropsTheory.io_events_mono_def]
        )
        THEN (
          (* e2 ~> Rval v' || e2 ~> Rerr (Rraise v') *)
          fs [PULL_EXISTS]
          \\ rename1 `st2heap _ st2 = heap`
          \\ GEN_EXISTS_TAC "st'" `st2 with clock := st'.clock + st2.clock`
          \\ `SPLIT3 (st2heap (p:'ffi ffi_proj) st2) (h_f',h_k, h_g UNION h_g')`
            by SPLIT_TAC
          \\ simp [st2heap_clock] \\ rveq \\ instantiate
          \\ qexists_tac `ck + ck'`
          \\ qpat_assum `evaluate _ _ [e1] = _` (add_to_clock `ck'`)
          \\ qpat_assum `evaluate _ _ [e2] = _` (add_to_clock `st'.clock`)
          \\ fs [with_clock_with_clock]
        )
      )
      THEN1 (
        (* e1 ~> Rerr (Rraise v) *)
        rename1 `evaluate _ _ [e1] = (_, Rerr (Rraise v))` \\
        fs [SEP_IMPPOST_VARIANTS, SEP_IMP_def] \\ first_assum progress \\
        qexists_tac `Exn v` \\ instantiate \\ qexists_tac `ck` \\ rw []
      )
      THEN1 (
        (* e1 ~> FFI diverge *)
        rename1 `evaluate _ _ [e1] = (_, Rerr (Rabort (Rffi_error (Final_event name cargs FFI_diverged))))` \\
        fs [SEP_IMPPOST_VARIANTS, SEP_IMP_def] \\ first_assum progress \\
        qexists_tac `FFIDiv name cargs` \\
        instantiate \\ qexists_tac `ck` \\ rw []
      )
      THEN1 (
        (* e1 ~> timeout *)
        rename1 `evaluate _ _ [e1] = (_, Rerr (Rabort Rtimeout_error))`
        \\ fs [SEP_IMPPOST_VARIANTS, SEP_IMP_def] \\ first_assum progress
        \\ rename1 `Q (Div io) h_f` \\ qexists_tac `Div io`
        \\ instantiate \\ rpt strip_tac
        THEN1 (
          first_assum (qspec_then `ck` mp_tac) \\ strip_tac
          \\ qexists_tac `st'` \\ rw [])
        \\ fs [lprefix_lubTheory.lprefix_lub_def] \\ rpt strip_tac
        THEN1 (
          qpat_assum `!ll. _ => LPREFIX ll io` (qspec_then `ll` irule)
          \\ qexists_tac `ck`
          \\ qpat_assum `!ck. ?st'. _` (qspec_then `ck` mp_tac)
          \\ strip_tac \\ rw [])
        \\ qpat_assum `!ub. _ => LPREFIX io ub` (qspec_then `ub` irule)
        \\ rpt strip_tac
        \\ qpat_assum `!ll. _ => LPREFIX ll ub` (qspec_then `ll` irule)
        \\ qexists_tac `ck`
        \\ qpat_assum `!ck. ?st'. _` (qspec_then `ck` mp_tac)
        \\ strip_tac \\ rw []
      )
    )
  )

  THEN1 (
    (* Letrec; the bulk of the proof is done in [cf_letrec_sound] *)
    HO_MATCH_MP_TAC sound_local \\ simp [MAP_MAP_o, o_DEF, LAMBDA_PROD] \\
    mp_tac (Q.SPECL [`funs`, `e`] cf_letrec_sound) \\
    fs [LAMBDA_PROD, letrec_pull_params_LENGTH, letrec_pull_params_names] \\
    rewrite_tac [sound_def] \\ rpt strip_tac \\ fs [] \\
    first_assum (qspecl_then [`env`, `H`, `Q`] assume_tac) \\
    (fn x => first_assum (qspec_then x assume_tac))
      `MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs` \\
    fs [letrec_pull_params_LENGTH] \\ res_tac \\ instantiate
  )

  THEN1 (
    (* App *)
    Cases_on `?ffi_index. op = FFI ffi_index` THEN1 (
      (* FFI *)
      fs [] \\ rveq \\
      (every_case_tac \\ TRY (MATCH_ACCEPT_TAC sound_local_false)) \\
      irule cf_ffi_sound
    ) \\
    Cases_on `op` \\ fs [] \\ TRY (MATCH_ACCEPT_TAC sound_local_false) \\
    (every_case_tac \\ TRY (MATCH_ACCEPT_TAC sound_local_false)) \\
    cf_strip_sound_tac \\
    TRY (
      (* Opn & Opb *)
      (rename1 `app_opn op` ORELSE rename1 `app_opb op`) \\
      Q.REFINE_EXISTS_TAC `Val v` \\ simp [] \\ cf_evaluate_step_tac \\
      fs [app_opn_def, app_opb_def, st2heap_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      Cases_on `op` \\ fs [do_app_def] \\ fs [SEP_IMP_def] \\
      fs [state_component_equality]
    )
    THEN1 (
      (* Equality *)
      Q.REFINE_EXISTS_TAC `Val v` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\ fs [do_app_def, app_equality_def] \\
      progress (fst (CONJ_PAIR type_match_implies_do_eq_succeeds)) \\ fs [] \\
      fs [SEP_IMP_def] \\ first_assum progress \\ instantiate \\
      qexists_tac `{}` \\ fs [st2heap_def] \\ SPLIT_TAC
    )
    THEN1 (
      (* Opapp *)
      rename1 `dest_opapp _ = SOME (f, xs)` \\
      schneiderUtils.UNDISCH_ALL_TAC \\ SPEC_ALL_TAC \\
      CONV_TAC (RESORT_FORALL_CONV (fn l =>
        (op @) (partition (fn v => fst (dest_var v) = "xs") l))) \\
      gen_tac \\ completeInduct_on `LENGTH xs` \\ rpt strip_tac \\
      fs [] \\ qpat_x_assum `dest_opapp _ = _` mp_tac \\
      rewrite_tac [dest_opapp_def] \\ every_case_tac \\ fs [] \\
      rpt strip_tac \\ qpat_x_assum `_ = xs` (assume_tac o GSYM) \\ fs []
      (* 1 argument *)
      THEN1 (
        rename1 `xs = [x]` \\ fs [exp2v_list_def] \\ full_case_tac \\ fs [] \\
        qpat_x_assum `_ = argsv` (assume_tac o GSYM) \\ rename1 `argsv = [xv]` \\
        cf_evaluate_step_tac \\
        fs [app_def, app_basic_def] \\ first_assum progress \\
        fs [evaluate_to_heap_def, evaluate_ck_def] \\
        rename1 `SPLIT3 heap (h_f, h_k, h_g)` \\
        progress SPLIT3_swap23 \\ instantiate \\
        reverse (Cases_on `r`) \\ fs []
        THEN1 (
          rpt strip_tac
          THEN1 (
            cf_exp2v_evaluate_tac `st with clock := ck`
            \\ fs [evaluateTheory.dec_clock_def]
          )
          \\ irule lprefix_lub_subset
          \\ qexists_tac `IMAGE (λck. fromList (FST (evaluate (st with clock := ck) env' [exp])).ffi.io_events) UNIV`
          \\ fs [SUBSET_DEF]
          \\ rpt strip_tac
          THEN1 (
            cf_exp2v_evaluate_tac `st with clock := ck`
            THEN1 (
              qexists_tac `fromList (FST (evaluate st env' [exp])).ffi.io_events`
              \\ rw [LPREFIX_fromList_fromList]
              THEN1 (
                qexists_tac `st.clock`
                \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
              )
              \\ qspecl_then [`st`, `env'`, `[exp]`] strip_assume_tac
                (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono)
              \\ fs [evaluatePropsTheory.io_events_mono_def]
            )
            \\ qexists_tac `fromList (FST (evaluate (st with clock := ck - 1) env' [exp])).ffi.io_events`
            \\ rw [LPREFIX_fromList_fromList]
            THEN1 (qexists_tac `ck - 1` \\ fs [])
            \\ qspecl_then [`st with clock := ck - 1`, `env'`, `[exp]`] strip_assume_tac
              (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono)
            \\ fs [evaluatePropsTheory.io_events_mono_def, evaluateTheory.dec_clock_def]
          )
          \\ qexists_tac `ck + 1`
          \\ cf_exp2v_evaluate_tac `st with clock := ck + 1`
          \\ fs [evaluateTheory.dec_clock_def]
        )
        \\ qexists_tac `ck + 1`
        \\ cf_exp2v_evaluate_tac `st with clock := ck + 1`
        \\ fs [evaluateTheory.dec_clock_def]
      )
      (* 2+ arguments *)
      THEN1 (
        rename1 `dest_opapp papp_ = SOME (f, pxs)` \\
        rename1 `xs = pxs ++ [x]` \\ fs [LENGTH] \\
        progress exp2v_list_rcons \\ fs [] \\ rw [] \\
        (* Do some unfolding, by definition of dest_opapp *)
        `?papp. papp_ = App Opapp papp` by (
          Cases_on `papp_` \\ TRY (fs [dest_opapp_def] \\ NO_TAC) \\
          rename1 `dest_opapp (App op _)` \\
          Cases_on `op` \\ TRY (fs [dest_opapp_def] \\ NO_TAC) \\
          NO_TAC
        ) \\ fs [] \\
        (* Prepare for, and apply lemma [app_alt_ind_w] to split app *)
        progress dest_opapp_not_empty_arglist \\
        `xvs <> []` by (progress exp2v_list_LENGTH \\ strip_tac \\
                       first_assum irule \\ fs [LENGTH_NIL] \\ NO_TAC) \\
        progress app_alt_ind_w \\
        (* Specialize induction hypothesis with xs := pxs *)
        `LENGTH pxs < LENGTH pxs + 1` by (fs []) \\
        last_assum drule \\ disch_then (qspec_then `pxs` mp_tac) \\ fs [] \\
        disch_then progress \\ fs [POSTv_def, POST_def, SEP_EXISTS, cond_def, STAR_def] \\
        (* Cleanup *)
        Cases_on `r` \\ fs [] \\
        rename1 `app_basic _ g xv H' Q` \\ fs [SPLIT_emp2] \\ rw [] \\
        (* Exploit the [app_basic (p:'ffi ffi_proj) g xv H' Q] we got from the ind. hyp. *)
        progress SPLIT_of_SPLIT3_2u3 \\
        fs [app_basic_def, evaluate_to_heap_def, evaluate_ck_def] \\ rveq \\
        first_x_assum progress \\
        (* Instantiate the result value, case split on it *)
        qexists_tac `r` \\ reverse (Cases_on `r`) \\ fs [] \\ rveq
        THEN1 (
          rename1 `SPLIT3 heap (h_f', _, h_g')`
          \\ `SPLIT3 heap (h_f', h_k, h_g' UNION h_g)` by SPLIT_TAC
          \\ instantiate \\ rw []
          THEN1 (
            NTAC 2 (simp [Once terminationTheory.evaluate_def])
            \\ cf_exp2v_evaluate_tac `st with clock := ck'` \\ fs []
            \\ NTAC 2 (pop_assum (K ALL_TAC))
            \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
            \\ disch_then (qspec_then `ck'` mp_tac) \\ rw [] \\ fs []
            \\ Cases_on `ck'' = 0` \\ fs [evaluateTheory.dec_clock_def]
          )
          \\ match_mp_tac (GEN_ALL lprefix_lub_subset)
          \\ asm_exists_tac \\ simp [SUBSET_DEF]
          \\ rw []
          THEN1 (
            NTAC 2 (simp [Once terminationTheory.evaluate_def])
            \\ drule evaluatePropsTheory.evaluate_set_clock \\ fs []
            \\ disch_then (qspec_then `ck' + 1` strip_assume_tac)
            \\ cf_exp2v_evaluate_tac `st with clock := ck1`
            \\ qexists_tac `ck1` \\ fs [evaluateTheory.dec_clock_def]
          )
          \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
          \\ disch_then (qspec_then `ck'` mp_tac) \\ rw []
          THEN1 (
            NTAC 2 (simp [Once terminationTheory.evaluate_def])
            \\ cf_exp2v_evaluate_tac `st with clock := ck'`
            THEN1 (
              qexists_tac `fromList (FST (evaluate st' env' [exp])).ffi.io_events`
              \\ rw [LPREFIX_fromList_fromList]
              THEN1 (
                qexists_tac `st'.clock`
                \\ fs [semanticPrimitivesPropsTheory.with_same_clock]
              )
              \\ qspecl_then [`st'`, `env'`, `[exp]`] strip_assume_tac
                (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono)
              \\ fs [evaluatePropsTheory.io_events_mono_def]
            )
            \\ fs [evaluateTheory.dec_clock_def]
            \\ qpat_x_assum `!ck. ?st. _` (qspec_then `ck'' - 1` strip_assume_tac) \\ fs []
            \\ qexists_tac `fromList st''.ffi.io_events` \\ rw []
            \\ qexists_tac `ck'' - 1` \\ rw []
          )
          \\ qpat_x_assum `!ck. ?st. _` (qspec_then `ck2` strip_assume_tac)
          \\ rename1 `_ = (st2, _)`
          \\ qexists_tac `fromList st2.ffi.io_events` \\ rw []
          THEN1 (qexists_tac `ck2` \\ rw [])
          \\ `st'.ffi.io_events ≼ st2.ffi.io_events` by (
            drule (CONJUNCT1 evaluatePropsTheory.evaluate_io_events_mono_imp)
            \\ rw [evaluatePropsTheory.io_events_mono_def])
          \\ rw [LPREFIX_fromList_fromList]
          \\ irule isPREFIX_TRANS
          \\ instantiate
          \\ fs [evaluatePropsTheory.io_events_mono_def]
          \\ NTAC 2 (simp [Once terminationTheory.evaluate_def])
          \\ cf_exp2v_evaluate_tac `st with clock := ck'`
        )
        THEN (
          (* res = Val _ || res = Exn _ *)
          rename1 `SPLIT3 (st2heap _ st2) (h_f', _, h_g')` \\
          `SPLIT3 (st2heap (p:'ffi ffi_proj) st2) (h_f', h_k, h_g' UNION h_g)`
            by SPLIT_TAC \\
          instantiate \\
          NTAC 2 (simp [Once terminationTheory.evaluate_def]) \\
          (* Instantiate the clock, cleanup *)
          cf_exp2v_evaluate_tac `st with clock := ck + ck' + 1` \\
          qexists_tac `ck + ck' + 1` \\ rw [] \\
          qpat_assum `evaluate _ _ [App Opapp papp] = _` (add_to_clock `ck' + 1`) \\
          fs [with_clock_with_clock] \\
          (* Finish proving the goal *)
          rename1 `SPLIT (st2heap _ st1)` \\
          qexists_tac `st2 with clock := st2.clock + st1.clock` \\
          fs [st2heap_clock, evaluateTheory.dec_clock_def] \\
          qpat_assum `evaluate (st1 with clock := _) _ _ = _` (add_to_clock `st1.clock`) \\
          fs [with_clock_with_clock]
        )
      )
    )
    THEN1 (
      (* Opassign *)
      Q.REFINE_EXISTS_TAC `Val v` \\ simp [] \\ cf_evaluate_step_tac \\
      fs [app_assign_def, REF_def, SEP_EXISTS, cond_def] \\
      fs [SEP_IMP_def,STAR_def,cell_def,one_def] \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\ first_assum progress \\
      rename1 `SPLIT h_i (h_i', _)` \\ rename1 `FF h_i'` \\
      fs [do_app_def, store_assign_def] \\
      rename1 `rv = Loc r` \\ rw [] \\
      `Mem r (Refv x') IN (st2heap p st)` by SPLIT_TAC \\
      `Mem r (Refv x') IN (store2heap st.refs)` by
          fs [st2heap_def,Mem_NOT_IN_ffi2heap] \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      `store_v_same_type (EL r st.refs) (Refv xv)` by
        (fs [store_v_same_type_def]) \\ fs [] \\
      `SPLIT3 (store2heap (LUPDATE (Refv xv) r st.refs) ∪ ffi2heap p st.ffi)
         (Mem r (Refv xv) INSERT h_i', h_k, {})` by
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
      Q.REFINE_EXISTS_TAC `Val v` \\ simp [] \\ cf_evaluate_step_tac \\
      fs [do_app_def, store_alloc_def, app_ref_def, REF_def, SEP_EXISTS] \\
      fs [st2heap_def, cond_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      first_x_assum (qspec_then `Loc (LENGTH st.refs)` strip_assume_tac) \\
      first_x_assum (qspec_then `Mem (LENGTH st.refs) (Refv xv) INSERT h_i` mp_tac) \\
      assume_tac store2heap_alloc_disjoint \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      impl_tac
      THEN1 (qexists_tac `h_i` \\ fs [SPLIT_emp1] \\ SPLIT_TAC)
      THEN1 (
        strip_tac \\ instantiate \\ fs [store2heap_append] \\
        qexists_tac `{}` \\ SPLIT_TAC
      )
    )
    THEN1 (
      (* Opderef *)
      Q.REFINE_EXISTS_TAC `Val v` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def, app_deref_def, REF_def, SEP_EXISTS, cond_def] \\
      fs [SEP_IMP_def, STAR_def, one_def, cell_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\
      fs [do_app_def, store_lookup_def] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      rename1 `rv = Loc r` \\ rw [] \\
      `Mem r (Refv x) IN (store2heap st.refs)` by SPLIT_TAC \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [state_component_equality]
    ) \\
    try_finally (
      (* Aw8alloc & Aalloc *)
      Q.REFINE_EXISTS_TAC `Val tv` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [do_app_def, store_alloc_def, st2heap_def] \\
      fs [app_aalloc_def, app_aw8alloc_def, W8ARRAY_def, ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, cell_def, one_def] \\
      first_x_assum (qspec_then `Loc (LENGTH st.refs)` strip_assume_tac) \\
      qmatch_asmsub_rename_tac(`REPLICATE (Num n) vv`) \\
      ((rename1 `W8array _` \\ (fn l => first_x_assum (qspecl_then l mp_tac))
          [`Mem (LENGTH st.refs) (W8array (REPLICATE (Num n) vv)) INSERT h_i`])
        ORELSE (fn l => first_x_assum (qspecl_then l mp_tac))
          [`Mem (LENGTH st.refs) (Varray (REPLICATE (Num n) vv)) INSERT h_i`]) \\
      fs [integerTheory.INT_ABS] \\
      assume_tac store2heap_alloc_disjoint \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      impl_tac
      THEN1 (instantiate \\ fs [SPLIT_emp1] \\ SPLIT_TAC)
      THEN1 (
        rpt strip_tac \\ every_case_tac
        THEN1 (irule FALSITY \\ intLib.ARITH_TAC) \\
        instantiate \\ fs [integerTheory.INT_ABS, store2heap_append] \\
        qexists_tac `{}` \\ SPLIT_TAC
      )
    ) \\
    try_finally (
      (* Aalloc_empty *)
      Q.REFINE_EXISTS_TAC `Val v'` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [do_app_def, store_alloc_def, st2heap_def] \\
      fs [app_aalloc_def, app_aw8alloc_def, W8ARRAY_def, ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, cell_def, one_def] \\
      first_x_assum (qspec_then `Loc (LENGTH st.refs)` strip_assume_tac) \\
      ((rename1 `W8array _` \\ (fn l => first_x_assum (qspecl_then l mp_tac))
          [`Mem (LENGTH st.refs) (W8array []) INSERT h_i`])
        ORELSE (fn l => first_x_assum (qspecl_then l mp_tac))
          [`Mem (LENGTH st.refs) (Varray []) INSERT h_i`]) \\
      fs [integerTheory.INT_ABS] \\
      assume_tac store2heap_alloc_disjoint \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      impl_tac >>
      simp [REPLICATE]
      THEN1 (instantiate \\ fs [SPLIT_emp1] \\ SPLIT_TAC)
      THEN1 (
        rpt strip_tac \\ every_case_tac \\
        instantiate \\ fs [integerTheory.INT_ABS, store2heap_append] \\
        qexists_tac `{}` \\ SPLIT_TAC
      )
    ) \\
    try_finally (
      (* Aw8sub & Asub *)
      Q.REFINE_EXISTS_TAC `Val v'` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def, app_aw8sub_def, app_asub_def, W8ARRAY_def, ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\ rename1 `a = Loc l` \\ rw [] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      fs [do_app_def, store_lookup_def] \\
      ((`Mem l (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC) ORELSE
       (`Mem l (Varray vs) IN (store2heap st.refs)` by SPLIT_TAC)) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\ fs [] \\
      instantiate \\ fs [integerTheory.INT_ABS] \\
      full_case_tac THEN1 (irule FALSITY \\ intLib.ARITH_TAC) \\
      fs [state_component_equality]
    ) \\
    try_finally (
      (* Aw8length & Alength *)
      Q.REFINE_EXISTS_TAC `Val v'` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def, app_aw8length_def, app_alength_def] \\
      fs [W8ARRAY_def, ARRAY_def] \\
      fs [SEP_EXISTS, SEP_IMP_def, STAR_def, one_def, cell_def, cond_def] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
      rpt (first_x_assum progress) \\ rename1 `a = Loc l` \\ rw [] \\
      fs [do_app_def, store_lookup_def] \\
      ((`Mem l (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC) ORELSE
       (`Mem l (Varray vs) IN (store2heap st.refs)` by SPLIT_TAC)) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [state_component_equality]
    ) \\
    try_finally (
      (* Aw8update & Aupdate *)
      Q.REFINE_EXISTS_TAC `Val tv` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def, app_aw8update_def, app_aupdate_def] \\
      fs [W8ARRAY_def, ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      first_x_assum progress \\ rename1 `a = Loc l` \\ rw [] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      ((rename1 `W8array _` \\
        `Mem l (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC) ORELSE
       (`Mem l (Varray vs) IN (store2heap st.refs)` by SPLIT_TAC)) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [do_app_def, store_lookup_def, store_assign_def, store_v_same_type_def] \\
      fs [integerTheory.INT_ABS] \\
      full_case_tac THEN1 (irule FALSITY \\ intLib.ARITH_TAC) \\
      fs [evaluateTheory.list_result_def] \\
      rename1`LUPDATE vv (Num i) ws` \\
      ((rename1 `W8array _` \\
        qexists_tac `Mem l (W8array (LUPDATE vv (Num i) ws)) INSERT u`) ORELSE
       qexists_tac `Mem l (Varray (LUPDATE vv (Num i) ws)) INSERT u`) \\
      qexists_tac `{}` \\ mp_tac store2heap_IN_unique_key \\ rpt strip_tac
      THEN1 (progress_then (fs o sing) store2heap_LUPDATE \\ SPLIT_TAC)
      THEN1 (first_assum irule \\ instantiate \\ SPLIT_TAC)
    ) \\
    try_finally (
      (* WordFromInt W8, WordFromInt W64, WordToInt W8, WordToInt W64 *)
      Q.REFINE_EXISTS_TAC `Val v` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\ fs [do_app_def] \\
      fs [app_wordFromInt_W8_def, app_wordFromInt_W64_def, app_wordToInt_def] \\
      fs [SEP_IMP_def, st2heap_def] \\ res_tac \\
      progress SPLIT3_of_SPLIT_emp3 \\ instantiate
    ) \\
    try_finally (
      (* CopyStrAw8 *)
      Q.REFINE_EXISTS_TAC `Val v'` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def,app_copystraw8_def] \\
      fs [W8ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      first_x_assum progress
      \\ rename1 `d = Loc ld` \\ rw [] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      (rename1 `W8array _` \\
        `Mem ld (W8array wd) IN (store2heap st.refs)` by SPLIT_TAC) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [do_app_def, store_lookup_def, store_assign_def, store_v_same_type_def, IMPLODE_EXPLODE_I] \\
      fs[copy_array_def,integerTheory.INT_ABS] \\
      rpt(full_case_tac THEN1 (irule FALSITY \\ intLib.ARITH_TAC)) \\
      IF_CASES_TAC \\ fs[] \\ TRY (`F` by intLib.ARITH_TAC) \\
      IF_CASES_TAC \\ fs[ws_to_chars_def,chars_to_ws_def] \\ TRY (`F` by intLib.ARITH_TAC) \\
      fs [evaluateTheory.list_result_def] \\
      qmatch_goalsub_abbrev_tac`W8array wd'` \\
      qexists_tac `Mem ld (W8array wd') INSERT u` \\
      qexists_tac `{}` \\ mp_tac store2heap_IN_unique_key \\ rpt strip_tac
      THEN1 (progress_then (fs o sing) store2heap_LUPDATE \\ SPLIT_TAC) \\
      first_assum irule \\
      qexists_tac`u` \\
      qexists_tac`{Mem ld (W8array wd')}` \\ fs[Abbr`wd'`] \\
      rename1`TAKE (Num l) (DROP (Num so) _)` \\
      rename1`TAKE (Num do) (MAP _ wd)` \\
      `Num do + Num l = Num (do +l)` by intLib.ARITH_TAC \\
      simp[MAP_TAKE,MAP_DROP,MAP_MAP_o,o_DEF,integer_wordTheory.i2w_pos] \\
      simp[GSYM o_DEF,n2w_ORD_CHR_w2n] \\
      SPLIT_TAC
    ) \\
    try_finally (
      (* CopyAw8Str *)
      Q.REFINE_EXISTS_TAC `Val v'` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def,app_copyaw8str_def] \\
      fs [W8ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      first_x_assum progress
      \\ rename1 `s = Loc ls` \\ rw [] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      (rename1 `W8array _` \\
        `Mem ls (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [do_app_def, store_lookup_def, store_assign_def, store_v_same_type_def, IMPLODE_EXPLODE_I] \\
      fs[copy_array_def,integerTheory.INT_ABS] \\
      rpt(full_case_tac THEN1 (irule FALSITY \\ intLib.ARITH_TAC)) \\
      fs[ws_to_chars_def,chars_to_ws_def] \\
      fs [evaluateTheory.list_result_def] \\
      qexists_tac `Mem ls (W8array ws) INSERT u` \\
      qexists_tac `{}` \\ mp_tac store2heap_IN_unique_key \\ rpt strip_tac
      THEN1 (progress_then (fs o sing) store2heap_LUPDATE \\ SPLIT_TAC) \\
      fs[o_DEF] \\
      first_assum irule \\
      SPLIT_TAC
    ) \\
    try_finally (
      (* CopyAw8Aw8 *)
      Q.REFINE_EXISTS_TAC `Val v'` \\ simp [] \\ cf_evaluate_step_tac \\
      GEN_EXISTS_TAC "ck" `st.clock` \\ fs [with_clock_self] \\
      cf_exp2v_evaluate_tac `st` \\
      fs [st2heap_def,app_copyaw8aw8_def] \\
      fs [W8ARRAY_def] \\
      fs [SEP_EXISTS, cond_def, SEP_IMP_def, STAR_def, one_def, cell_def] \\
      first_x_assum progress
      \\ rename1 `s = Loc ls` \\ rename1 `d = Loc ld` \\ rw [] \\
      assume_tac (GEN_ALL Mem_NOT_IN_ffi2heap) \\
      rename1`Mem ls (W8array ws)` \\
      (rename1 `W8array _` \\
        `Mem ls (W8array ws) IN (store2heap st.refs)` by SPLIT_TAC) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      (rename1 `W8array _` \\
        `Mem ld (W8array wd) IN (store2heap st.refs)` by SPLIT_TAC) \\
      progress store2heap_IN_LENGTH \\ progress store2heap_IN_EL \\
      fs [do_app_def, store_lookup_def, store_assign_def, store_v_same_type_def] \\
      fs[copy_array_def,integerTheory.INT_ABS] \\
      rpt(full_case_tac THEN1 (irule FALSITY \\ intLib.ARITH_TAC)) \\
      fs [evaluateTheory.list_result_def] \\
      qmatch_goalsub_abbrev_tac`W8array wd'` \\
      qexists_tac `Mem ld (W8array wd') INSERT (Mem ls (W8array ws) INSERT u)` \\
      qexists_tac `{}` \\ mp_tac store2heap_IN_unique_key \\ rpt strip_tac
      THEN1 (progress_then (fs o sing) store2heap_LUPDATE \\ SPLIT_TAC) \\
      first_assum irule \\
      qexists_tac`Mem ls (W8array ws) INSERT u` \\
      qexists_tac`{Mem ld (W8array wd')}` \\ fs[Abbr`wd'`] \\
      rename1`TAKE (Num do) wd ++ TAKE (Num l) (DROP (Num so) ws)` \\
      `Num do + Num l = Num (do +l)` by intLib.ARITH_TAC \\
      SPLIT_TAC
    )
  )

  THEN1 (
    (* Log *)
    cf_strip_sound_full_tac \\
    fs [sound_def, htriple_valid_def, evaluate_to_heap_def, evaluate_ck_def] \\
    Cases_on `lop` \\ Cases_on `b` \\ fs [BOOL_def, Boolv_def] \\ rw [] \\
    fs [SEP_IMP_def] \\ first_x_assum progress \\ instantiate \\
    try_finally (
      reverse (Cases_on `r`) \\ fs []
      THEN1 (
        rpt strip_tac
        THEN1 (
          cf_exp2v_evaluate_tac `st with clock := ck`
          \\ fs [do_log_def, Boolv_def]
        )
        \\ fs [lprefix_lubTheory.lprefix_lub_def]
        \\ rpt strip_tac
        THEN1 (
          qpat_assum `!ll. _ => LPREFIX ll l` (qspec_then `ll` irule)
          \\ qexists_tac `ck`
          \\ cf_exp2v_evaluate_tac `st with clock := ck`
          \\ fs [do_log_def, Boolv_def]
        )
        \\ qpat_assum `!ub. _ => LPREFIX l ub` (qspec_then `ub` irule)
        \\ rpt strip_tac
        \\ qpat_assum `!ll. _ => LPREFIX ll ub` (qspec_then `ll` irule)
        \\ qexists_tac `ck`
        \\ cf_exp2v_evaluate_tac `st with clock := ck`
        \\ fs [do_log_def, Boolv_def]
      )
      \\ qexists_tac `ck`
      \\ cf_exp2v_evaluate_tac `st with clock := ck`
      \\ fs [do_log_def, Boolv_def]
    ) \\
    try_finally (
      Q.LIST_EXISTS_TAC [`{}`, `st2heap p st`]
      \\ progress SPLIT3_of_SPLIT_emp3 \\ rw []
      \\ Q.LIST_EXISTS_TAC [`st.clock`, `st`] \\ fs [with_clock_self]
      \\ cf_exp2v_evaluate_tac `st` \\ fs [do_log_def, Boolv_def]
    )
  )

  THEN1 (
    (* If *)
    cf_strip_sound_full_tac \\ fs [do_if_def]
    \\ Cases_on `b` \\ fs [sound_def, htriple_valid_def]
    \\ first_assum progress
    \\ fs [evaluate_to_heap_def, evaluate_ck_def, Boolv_def, BOOL_def]
    \\ instantiate
    THEN (
      reverse (Cases_on `r`) \\ fs []
      THEN1 (
        rpt strip_tac
        THEN1 cf_exp2v_evaluate_tac `st with clock := ck`
        \\ fs [lprefix_lubTheory.lprefix_lub_def]
        \\ rpt strip_tac
        THEN1 (
          qpat_assum `!ll. _ => LPREFIX ll l` (qspec_then `ll` irule)
          \\ qexists_tac `ck`
          \\ cf_exp2v_evaluate_tac `st with clock := ck`
        )
        \\ qpat_assum `!ub. _ => LPREFIX l ub` (qspec_then `ub` irule)
        \\ rpt strip_tac
        \\ qpat_assum `!ll. _ => LPREFIX ll ub` (qspec_then `ll` irule)
        \\ qexists_tac `ck`
        \\ cf_exp2v_evaluate_tac `st with clock := ck`
      )
      \\ qexists_tac `ck`
      \\ cf_exp2v_evaluate_tac `st with clock := ck`
    )
  )

  THEN1 (
    (* Mat: the bulk of the proof is done in [cf_cases_evaluate_match] *)
    cf_strip_sound_full_tac
    \\ `EVERY (\b. sound p (SND b) (cf p (SND b))) branches` by
         (fs [EVERY_MAP, EVERY_MEM] \\ NO_TAC)
    \\ progress cf_cases_evaluate_match
    \\ instantiate
    THEN (
      reverse (Cases_on `r`) \\ fs []
      THEN1 (
        rpt strip_tac
        THEN1 cf_exp2v_evaluate_tac `st with clock := ck`
        \\ fs [lprefix_lubTheory.lprefix_lub_def]
        \\ rpt strip_tac
        THEN1 (
          qpat_assum `!ll. _ => LPREFIX ll l` (qspec_then `ll` irule)
          \\ qexists_tac `ck`
          \\ cf_exp2v_evaluate_tac `st with clock := ck`
        )
        \\ qpat_assum `!ub. _ => LPREFIX l ub` (qspec_then `ub` irule)
        \\ rpt strip_tac
        \\ qpat_assum `!ll. _ => LPREFIX ll ub` (qspec_then `ll` irule)
        \\ qexists_tac `ck`
        \\ cf_exp2v_evaluate_tac `st with clock := ck`
      )
      \\ qexists_tac `ck`
      \\ cf_exp2v_evaluate_tac `st with clock := ck`
    )
  )

  THEN1 (
    (* Raise *)
    cf_strip_sound_full_tac \\ qexists_tac `Exn v` \\ fs [] \\
    fs [SEP_IMP_def] \\ res_tac \\ instantiate \\
    progress SPLIT3_of_SPLIT_emp3 \\ instantiate \\
    qexists_tac `st.clock` \\
    cf_exp2v_evaluate_tac `st with clock := st.clock` \\ fs [with_clock_self]
  )

  THEN1 (
    (* Handle *)
    cf_strip_sound_full_tac \\
    qpat_x_assum `sound _ e _`
      (progress o REWRITE_RULE [sound_def, htriple_valid_def]) \\
    Cases_on `r` \\ fs [evaluate_to_heap_def]
    THEN1 (
      (* e ~> Rval v *)
      rename1 `evaluate_ck _ _ _ [e] = (_, Rval [v])` \\
      fs [SEP_IMPPOST_VARIANTS, SEP_IMP_def] \\ first_assum progress \\
      qexists_tac `Val v` \\ fs [] \\ instantiate \\
      fs [evaluate_ck_def] \\ qexists_tac `ck` \\ fs []
    )
    THEN1 (
      (* e ~> Rerr (Rraise v) *)
      rename1 `evaluate_ck _ _ _ [e] = (_, Rerr (Rraise v))` \\
      first_x_assum (qspec_then `v` assume_tac) \\
      fs [] \\
      `EVERY (\b. sound p (SND b) (cf p (SND b))) branches` by
        (fs [EVERY_MAP, EVERY_MEM] \\ NO_TAC) \\
      progress SPLIT_of_SPLIT3_2u3 \\
      drule cf_cases_evaluate_match \\
      disch_then (qspecl_then
        [`v`, `env`, `Q' (Exn v)`, `Q`, `v`, `st'`, `h_f`, `h_k UNION h_g`]
        mp_tac) \\ rw [] \\
      qexists_tac `r` \\ reverse (Cases_on `r`) \\ fs [] \\ rveq
      THEN1 (
        rename1 `SPLIT3 heap (h_f', _, h_g')`
        \\ `SPLIT3 heap (h_f', h_k, h_g' UNION h_g)` by SPLIT_TAC
        \\ instantiate \\ rw []
        THEN1 (
          fs [evaluate_ck_def]
          \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
          \\ disch_then (qspec_then `ck'` strip_assume_tac) \\ fs [])
        \\ match_mp_tac (GEN_ALL lprefix_lub_subset)
        \\ asm_exists_tac \\ simp [SUBSET_DEF]
        \\ rw [] \\ fs [evaluate_ck_def]
        THEN1 (
          drule evaluatePropsTheory.evaluate_set_clock \\ fs []
          \\ disch_then (qspec_then `ck'` strip_assume_tac)
          \\ qexists_tac `ck1` \\ fs [])
        \\ drule evaluatePropsTheory.evaluate_set_init_clock \\ fs []
        \\ disch_then (qspec_then `ck'` mp_tac) \\ rw []
        THEN1 (first_x_assum (qspec_then `ck''` mp_tac) \\ fs [])
        \\ fs []
        \\ qpat_x_assum `!ck. ?st''. _` (qspec_then `ck2` strip_assume_tac)
        \\ rename1 `_ = (st2, _)`
        \\ qexists_tac `fromList st2.ffi.io_events` \\ rw []
        THEN1 (qexists_tac `ck2` \\ rw [])
        \\ `st'.ffi.io_events ≼ st2.ffi.io_events` by (
          drule (CONJUNCT2 evaluatePropsTheory.evaluate_io_events_mono_imp)
          \\ rw [evaluatePropsTheory.io_events_mono_def])
        \\ rw [LPREFIX_fromList_fromList]
        \\ irule isPREFIX_TRANS
        \\ instantiate
        \\ fs [evaluatePropsTheory.io_events_mono_def]
      )
      THEN (
        rename1 `SPLIT3 (st2heap _ st'') (h_f', h_k UNION h_g, h_g')` \\
        fs [PULL_EXISTS] \\
        Q.LIST_EXISTS_TAC [`h_f'`, `h_g UNION h_g'`, `ck + ck'`,
          `st'' with clock := st''.clock + st'.clock`] \\ rw []
        THEN1 (fs [st2heap_def] \\ SPLIT_TAC) \\
        fs [evaluate_ck_def] \\
        qpat_assum `evaluate _ _ [e] = _` (add_to_clock `ck'`) \\
        qpat_assum `evaluate_match _ _ _ branches _ = _` (add_to_clock `st'.clock`) \\
        fs [with_clock_with_clock]
      )
    )
    THEN1 (
      (* e ~> FFI diverge *)
      rename1 `evaluate_ck _ _ _ [e] = (_, Rerr (Rabort (Rffi_error (Final_event s cargs _))))` \\
      asm_exists_tac \\
      qexists_tac `FFIDiv s cargs` \\
      fs[evaluate_ck_def,SEP_IMPPOST_VARIANTS,SEP_IMP_def] \\
      qexists_tac `ck` \\ fs []
    )
    THEN1 (
      (* e -> Rtimeout_error *)
      rename1 `lprefix_lub$lprefix_lub _ io` \\
      asm_exists_tac \\ qexists_tac `Div io` \\
      fs [evaluate_ck_def, SEP_IMPPOST_VARIANTS, SEP_IMP_def] \\
      fs[SKOLEM_THM] >>
      reverse conj_tac >-
        (rename1 `evaluate _ _ _ = (f _,_)` >>
         `f = \i. FST(evaluate (st with clock := i) env [e])`
           by simp[ETA_THM] >>
         pop_assum(fn thm => REWRITE_TAC [thm]) >>
         metis_tac[]) >>
      metis_tac[]
    )
  )

  THEN1 (
    (* Lannot *)
    cf_strip_sound_full_tac \\ fs [sound_def, htriple_valid_def] \\
    first_assum progress \\ fs [evaluate_to_heap_def, evaluate_ck_def] \\
    metis_tac[]
  )

  THEN1 (
    (* Tannot *)
    cf_strip_sound_full_tac \\ fs [sound_def, htriple_valid_def] \\
    first_assum progress \\ fs [evaluate_to_heap_def, evaluate_ck_def] \\
    metis_tac[]
  )
QED

Theorem cf_sound':
   !e env H Q st.
     cf (p:'ffi ffi_proj) e env H Q ==> H (st2heap (p:'ffi ffi_proj) st) ==>
     ?r h_f h_g heap.
       SPLIT heap (h_f, h_g) /\
       Q r h_f /\
       case r of
          | Val v => ?ck st'.
            evaluate (st with clock := ck) env [e] = (st', Rval [v]) /\
            st2heap p st' = heap
          | Exn v => ?ck st'.
            evaluate (st with clock := ck) env [e] = (st', Rerr (Rraise v)) /\
            st2heap p st' = heap
          | FFIDiv name cargs => ∃ck st'.
            evaluate (st with clock := ck) env [e] =
            (st', Rerr (Rabort (Rffi_error (Final_event name cargs FFI_diverged)))) /\
            st2heap p st' = heap
          | Div io =>
            (∀ck. ?st'. evaluate (st with clock := ck) env [e] =
            (st', Rerr (Rabort Rtimeout_error))) /\
            lprefix_lub$lprefix_lub (IMAGE (\ck. fromList (FST(evaluate (st with clock := ck) env [e])).ffi.io_events) UNIV) io
Proof
  rpt strip_tac \\ qspecl_then [`(p:'ffi ffi_proj)`, `e`] assume_tac cf_sound \\
  fs [sound_def, evaluate_to_heap_def, evaluate_ck_def, htriple_valid_def] \\
  `SPLIT (st2heap p st) (st2heap p st, {})` by SPLIT_TAC \\
  res_tac \\ rename1 `SPLIT3 heap (h_f, {}, h_g)` \\
  `SPLIT heap (h_f, h_g)` by SPLIT_TAC \\ instantiate
QED

Theorem cf_sound_local:
   !e env H Q h i st.
     cf (p:'ffi ffi_proj) e env H Q ==>
     SPLIT (st2heap (p:'ffi ffi_proj) st) (h, i) ==>
     H h ==>
     ?r h' g heap.
       SPLIT3 heap (h', g, i) /\
       Q r h' /\
       case r of
          | Val v => ?ck st'.
            evaluate (st with clock := ck) env [e] = (st', Rval [v]) /\
            st2heap p st' = heap
          | Exn v => ?ck st'.
            evaluate (st with clock := ck) env [e] = (st', Rerr (Rraise v)) /\
            st2heap p st' = heap
          | FFIDiv name cargs => ∃ck st'.
            evaluate (st with clock := ck) env [e] =
            (st', Rerr (Rabort (Rffi_error (Final_event name cargs FFI_diverged)))) /\
            st2heap p st' = heap
          | Div io =>
            (∀ck. ?st'. evaluate (st with clock := ck) env [e] =
            (st', Rerr (Rabort Rtimeout_error))) /\
            lprefix_lub$lprefix_lub (IMAGE (\ck. fromList (FST(evaluate (st with clock := ck) env [e])).ffi.io_events) UNIV) io
Proof
  rpt strip_tac \\
  `sound (p:'ffi ffi_proj) e (\env. (local (cf (p:'ffi ffi_proj) e env)))` by
    (match_mp_tac sound_local \\ fs [cf_sound]) \\
  fs [sound_def, evaluate_to_heap_def, evaluate_ck_def, htriple_valid_def, st2heap_def] \\
  `local (cf (p:'ffi ffi_proj) e env) H Q` by
    (fs [REWRITE_RULE [is_local_def] cf_local |> GSYM]) \\
  res_tac \\ progress SPLIT3_swap23 \\ instantiate
QED

Theorem app_basic_of_cf:
   !clos body x env env' v H Q.
     do_opapp [clos; x] = SOME (env', body) ==>
     cf (p:'ffi ffi_proj) body env' H Q ==>
     app_basic (p:'ffi ffi_proj) clos x H Q
Proof
  rpt strip_tac \\ irule app_basic_of_htriple_valid \\
  progress (REWRITE_RULE [sound_def] cf_sound) \\
  instantiate
QED

Theorem app_of_cf:
   !ns env body xvs env' H Q.
     ns <> [] ==>
     LENGTH xvs = LENGTH ns ==>
     cf (p:'ffi ffi_proj) body (extend_env ns xvs env) H Q ==>
     app (p:'ffi ffi_proj) (naryClosure env ns body) xvs H Q
Proof
  rpt strip_tac \\ irule app_of_htriple_valid \\ fs [] \\
  progress (REWRITE_RULE [sound_def] cf_sound)
QED

Theorem app_rec_of_cf:
   !f params body funs xvs env H Q.
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
     app (p:'ffi ffi_proj) (naryRecclosure env (letrec_pull_params funs) f) xvs H Q
Proof
  rpt strip_tac \\ irule app_rec_of_htriple_valid \\ fs [] \\
  progress (REWRITE_RULE [sound_def] cf_sound)
QED

val _ = export_theory();
