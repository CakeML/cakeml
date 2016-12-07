open preamble
open set_sepTheory helperLib ml_translatorTheory ConseqConv
open semanticPrimitivesTheory cfHeapsTheory
open cfHeapsBaseLib cfStoreTheory
open cfTacticsBaseLib;
open terminationTheory
open ASCIInumbersTheory

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

val exp2v_evaluate = Q.store_thm ("exp2v_evaluate",
  `!e env st v. exp2v env e = SOME v ==>
    evaluate st env [e] = (st, Rval [v])`,
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

val exp2v_list_evaluate = Q.store_thm ("exp2v_list_evaluate",
  `!l lv env st. exp2v_list env l = SOME lv ==>
    evaluate st env l = (st, Rval lv)`,
  Induct
  THEN1 (fs [exp2v_list_def, terminationTheory.evaluate_def])
  THEN1 (
    rpt strip_tac \\ fs [exp2v_list_def] \\
    every_case_tac \\ fs [] \\ rw [] \\
    first_assum progress \\ progress exp2v_evaluate \\
    Cases_on `l` \\ fs [terminationTheory.evaluate_def]
  )
);

val evaluate_list_rcons = Q.store_thm ("evaluate_rcons",
  `!env st st' st'' l x lv v.
     evaluate st env l = (st', Rval lv) /\
     evaluate st' env [x] = (st'', Rval [v]) ==>
     evaluate st env (l ++ [x]) = (st'', Rval (lv ++ [v]))`,

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
          (CONJ_PAIR evaluatePropsTheory.evaluate_length |> fst)) \\
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

val exp2v_list_REVERSE = Q.store_thm ("exp2v_list_REVERSE",
  `!l (st: 'ffi semanticPrimitives$state) lv env. exp2v_list env l = SOME lv ==>
    evaluate st env (REVERSE l) = (st, Rval (REVERSE lv))`,
  Induct \\ rpt gen_tac \\ disch_then (assume_tac o GSYM) \\
  fs [exp2v_list_def, terminationTheory.evaluate_def] \\
  every_case_tac \\ fs [] \\ rw [] \\ irule evaluate_list_rcons \\
  metis_tac [exp2v_evaluate]
);

val exp2v_list_rcons = Q.store_thm ("exp2v_list_rcons",
  `!xs x l env.
     exp2v_list env (xs ++ [x]) = SOME l ==>
     ?xvs xv.
       l = xvs ++ [xv] /\
       exp2v_list env xs = SOME xvs /\
       exp2v env x = SOME xv`,
  Induct_on `xs` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ fs [] \\
  first_assum progress \\ fs [] \\ rw []
);

val exp2v_list_LENGTH = Q.store_thm ("exp2v_list_LENGTH",
  `!l lv env. exp2v_list env l = SOME lv ==> LENGTH l = LENGTH lv`,
  Induct_on `l` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ res_tac \\ fs [] \\ rw []
);

(*------------------------------------------------------------------*)
(* [normalise] *)

val normalise_def = Define `
  normalise x = (x:exp)` (* TODO: actually implement this without going into closures *)

val evaluate_normalise = Q.store_thm("evaluate_normalise",
  `evaluate s env [normalise exp] = evaluate s env [exp]`,
  fs [normalise_def]);


(*------------------------------------------------------------------*)
(* [full_normalise] *)

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

val mk_opapp_def = tDefine "mk_opapp" `
  mk_opapp xs =
    if LENGTH xs < 2 then HD xs else
      App Opapp [mk_opapp (FRONT xs); LAST xs]`
 (WF_REL_TAC `measure LENGTH`
  \\ fs [LENGTH_FRONT] \\ Cases \\ fs []);

val MEM_exp_size = Q.prove(
  `!args a. MEM a args ==> exp_size a <= exp6_size args`,
  Induct \\ fs [astTheory.exp_size_def] \\ rw [] \\ res_tac \\ fs []);

val MEM_exp1_size = Q.prove(
  `!rs. MEM (v,a,e') rs ==> exp_size e' < exp1_size rs`,
  Induct \\ fs [astTheory.exp_size_def] \\ rw [] \\ res_tac \\ fs []
  \\ fs [astTheory.exp_size_def]);

val get_name_aux_def = tDefine "get_name_aux" `
  get_name_aux n vs =
    let v = "t" ++ num_to_dec_string n in
      if MEM v vs then get_name_aux (n+1) (FILTER (\x. v <> x) vs) else v`
 (WF_REL_TAC `measure (\(n,vs). LENGTH vs)`
  \\ rw [] \\ fs [MEM_SPLIT,FILTER_APPEND]
  \\ match_mp_tac (DECIDE ``m <= m1 /\ n <= n1 ==> m + n < m1 + (n1 + 1n)``)
  \\ fs [LENGTH_FILTER_LEQ]);

val alpha = EVAL ``GENLIST (\n. CHR (n + ORD #"a")) 26`` |> concl |> rand

val alpha_def = Define `alpha = ^alpha`;

val get_name_def = Define `
  get_name vs =
    let ws = FILTER (\s. ~(MEM [s] vs)) alpha in
      if NULL ws then get_name_aux 0 vs else [HD ws]`;

val Lets_def = Define `
  Lets [] e = e /\
  Lets ((n,x)::xs) e = Let (SOME n) x (Lets xs e)`

val exp6_size_lemma = Q.prove(
  `!xs ys. exp6_size (xs ++ ys) = exp6_size xs + exp6_size ys`,
  Induct \\ fs [astTheory.exp_size_def]);

val dest_opapp_size = Q.prove(
  `!xs p_1 p_2.
      dest_opapp xs = SOME (p_1,p_2) ==>
      exp_size p_1 + exp6_size p_2 < exp_size xs`,
  recInduct (theorem "dest_opapp_ind") \\ fs [dest_opapp_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [astTheory.exp_size_def]
  \\ res_tac \\ fs [exp6_size_lemma,astTheory.exp_size_def]);

val wrap_if_needed_def = Define `
  wrap_if_needed needs_wrapping ns e b =
    if needs_wrapping then (
      let x = get_name ns in
      (Var (Short x), x::ns, (x,e)::b)
    ) else (
      (e, ns, b)
    )`;

val norm_def = tDefine "norm" `
  norm (is_named: bool) (as_value: bool) (ns: string list) (Lit l) = (Lit l, ns, ([]: (string # exp) list)) /\
  norm is_named as_value ns (Var (Short name)) = (Var (Short name), name::ns, []) /\
  norm is_named as_value ns (Var long) = (Var long, ns, []) /\
  norm is_named as_value ns (Let opt e1 e2) =
    (case opt of
         SOME x =>
         (let (e1',ns,b1) = norm T F ns e1 in
          let (e2',ns) = protect F ns e2 in
          let e' = Lets b1 (Lets [(x, e1')] e2') in
          wrap_if_needed as_value (x::ns) e' [])
       | NONE =>
         (let (e1', ns, b1) = norm F F ns e1 in
          let (e2', ns) = protect F ns e2 in
          wrap_if_needed as_value ns (Let NONE e1' e2') b1)) /\
  norm is_named as_value ns (App Opapp args) =
    (case dest_opapp (App Opapp args) of
         SOME (f, args) =>
         (let (f', ns, b0) = norm F T ns f in
          let (args', ns, bi) = norm_list F T ns args in
          let e' = mk_opapp (f' :: args') in
          let b' = FLAT (REVERSE (b0 :: bi)) (* right-to-left evaluation *) in
          wrap_if_needed as_value ns e' b')
       | NONE => ARB) /\
  norm is_named as_value ns (App op args) =
    (let (args', ns, bi) = norm_list F T ns args in
     let b' = FLAT (REVERSE bi) in (* right-to-left evaluation *)
     wrap_if_needed as_value ns (App op args') b') /\
  norm is_named as_value ns (Con x args) =
    (let (args', ns, bi) = norm_list F T ns args in
     let b = FLAT (REVERSE bi) in (* right-to-left evaluation *)
     wrap_if_needed as_value ns (Con x args') b) /\
  norm is_named as_value ns (Raise e) =
    (let (e',ns,b) = norm F T ns e in
     wrap_if_needed as_value ns (Raise e') b) /\
  norm is_named as_value ns (Log l e1 e2) =
    (let (e1', n1, b1) = norm F T ns e1 in
     let (e2', n2, b2) = norm F T n1 e2 in
     if b2 = [] then (
       if b1 = [] then (
         (* produce: <e1> op <e2> *)
         (Log l e1' e2', n2, [])
       ) else (
         (* produce: let <b1> in <e1> op <e2> *)
         wrap_if_needed as_value n2 (Log l e1' e2') b1
       )
     ) else (
       let (e2', n2, b2) = norm F F n1 e2 in
       case l of
           And =>
           (* produce: let <b1> in <e1'> andalso (lets <b2> in <e2'>) *)
           wrap_if_needed as_value n2 (Log And e1' (Lets b2 e2')) b1
         | Or =>
           (* produce: let <b1> in <e1'> orelse (let <b2> in <e2'>) *)
           wrap_if_needed as_value n2 (Log Or e1' (Lets b2 e2')) b1
     )) /\
  norm is_named as_value ns (Fun v e) =
    (let (e', ns) = protect is_named (v::ns) e in
     wrap_if_needed (as_value \/ ~is_named) ns (Fun v e') []) /\
  norm is_named as_value ns (Mat e1 e2) =
    (let (e1',n1,b1) = norm F T ns e1 in
     let (rows', ni) = norm_rows n1 e2 in
     let e' = Mat e1' rows' in
     wrap_if_needed as_value ni e' b1) /\
  norm is_named as_value ns (Handle e1 e2) =
    (let (e1',n1) = protect F ns e1 in
     let (rows', ni) = norm_rows n1 e2 in
     let e' = Handle e1' rows' in
     wrap_if_needed as_value ni e' []) /\
  norm is_named as_value ns (If e1 e2 e3) =
    (let (e1', ns, b) = norm F T ns e1 in
     let (e2', ns) = protect F ns e2 in
     let (e3', ns) = protect F ns e3 in
     wrap_if_needed as_value ns (If e1' e2' e3') b) /\
  norm is_named as_value ns (Letrec rs e) =
    (let (rs', ns) = norm_letrec_branches ns rs in
     let (e', ns) = protect F ns e in
     wrap_if_needed as_value ns (Letrec rs' e') []) /\
  norm_list is_named as_value ns ([]: exp list) = ([], ns, []) /\
  norm_list is_named as_value ns (e::es) =
    (let (e', ns', b) = norm is_named as_value ns e in
     let (es', ns'', bs) = norm_list is_named as_value ns' es in
     (e' :: es', ns'', b::bs)) /\
  norm_rows ns ([]: (pat, exp) alist) = ([], ns) /\
  norm_rows ns (row :: rows) =
    (let (row', ns') = protect_row F ns row in
     let (rows', ns'') = norm_rows ns' rows in
     (row' :: rows', ns'')) /\
  norm_letrec_branches ns ([]: (string, string # exp) alist) = ([], ns) /\
  norm_letrec_branches ns (branch :: branches) =
    (let (branch', ns') = protect_letrec_branch T ns branch in
     let (branches', ns'') = norm_letrec_branches ns' branches in
     (branch' :: branches', ns'')) /\
  protect is_named ns e =
    (let (e',ns',b) = norm is_named F ns e in
     (Lets b e', ns')) /\
  protect_row is_named ns row =
    (let (row_e', ns') = protect is_named ns (SND row) in
     ((FST row, row_e'), ns')) /\
  protect_letrec_branch is_named ns branch =
    (let (branch_e', ns') = protect is_named ns (SND (SND branch)) in
     ((FST branch, FST (SND branch), branch_e'), ns'))`
 cheat;

val full_normalise_def = Define `
  full_normalise ns e = FST (protect T ns e)`;

val MEM_v_size = Q.prove(
  `!xs. MEM a xs ==> v_size a < v6_size xs`,
  Induct  \\ fs [v_size_def] \\ rw [] \\ res_tac \\ fs []);

val norm_exp_rel_def = Define `
  norm_exp_rel ns e1 e2 <=> (e1 = e2) \/
                            (full_normalise ns e1 = e2)`

val free_in_def = Define ` (* TODO: complete *)
  free_in (Lit l) v = T /\
  free_in (Var w) v = (w = v) /\
  free_in (Let NONE e1 e2) v = (free_in e1 v \/ free_in e2 v) /\
  free_in (Let (SOME x) e1 e2) v = (free_in e1 v \/ (free_in e2 v /\ v <> Short x))`

val (norm_rel_rules,norm_rel_ind,norm_rel_cases) = Hol_reln `
  (!i.
     norm_rel (Litv i) (Litv i)) /\
  (!i.
     norm_rel (Loc i) (Loc i)) /\
  (!xs ys.
     EVERY2 norm_rel xs ys ==>
     norm_rel (Vectorv xs) (Vectorv ys)) /\
  (!xs ys t.
     EVERY2 norm_rel xs ys ==>
     norm_rel (Conv t xs) (Conv t ys)) /\
  (!v env1 env2 ns e1 e2.
     norm_exp_rel ns e1 e2 /\ (free_in e1 = free_in e2) /\
     env_rel (free_in e1 DELETE Short v1) env1 env2 ==>
     norm_rel (Closure env1 v e1) (Closure env2 v e2)) /\
  (!v env1 env2 ns es1 es2.
     EVERY2 (\(n1,v1,e1) (n2,v2,e2).
       n1 = n2 /\ v1 = v2 /\ norm_exp_rel ns e1 e2 /\ (free_in e1 = free_in e2) /\
       env_rel (free_in e1 DELETE Short v1) env1 env2) es1 es2 ==>
     norm_rel (Recclosure env1 es1 v) (Recclosure env2 es2 v)) /\
  (!env1 env2 s.
     (!v x y. v IN s /\
              lookup_var_id v env1 = SOME x /\
              lookup_var_id v env2 = SOME y ==>
              norm_rel x y) ==>
     env_rel s env1 env2)`

val (norm_ref_rel_rules,norm_ref_rel_ind,norm_ref_rel_cases) = Hol_reln `
  (!v1 v2. norm_rel v1 v2 ==> norm_ref_rel (Refv v1) (Refv v2)) /\
  (!v1 v2. EVERY2 norm_rel v1 v2 ==> norm_ref_rel (Varray v1) (Varray v2)) /\
  (!b. norm_ref_rel (W8array b) (W8array b))`

val (norm_res_rel_rules,norm_res_rel_ind,norm_res_rel_cases) = Hol_reln `
  (!v1 v2. norm_rel v1 v2 ==> norm_res_rel (Rval v1) (Rval v2)) /\
  (!v1 v2. norm_rel v1 v2 ==> norm_res_rel (Rerr (Rraise v1)) (Rerr (Rraise v2))) /\
  (!a. norm_rel v1 v2 ==> norm_res_rel (Rerr (Rabort a)) (Rerr (Rabort a)))`

val norm_state_rel_def = Define `
  norm_state_rel s1 s2 <=>
     s1.clock = s2.clock ∧
     EVERY2 norm_ref_rel s1.refs s2.refs ∧
     s1.ffi = s2.ffi ∧
     s1.defined_types = s2.defined_types ∧
     s1.defined_mods = s2.defined_mods`

(*
val full_normalise_correct = Q.store_thm("full_normalise_correct",
  `env_rel (free_in e) env1 env2 /\ norm_state_rel s1 s2 /\
    evaluate ck env1 s1 e1 (rs1,res1) /\ norm_exp_rel e1 e2 ==>
    ?rs2 res2. evaluate ck env2 s2 e2 (rs2,res2) /\
               norm_state_rel rs1 rs2 /\ norm_res_rel res1 res2`,
  ... ); TODO
*)

val full_normalise_exp_def = Define `
  full_normalise_exp exp = full_normalise [] exp`

val full_normalise_decl_def = Define `
  full_normalise_decl (Dlet pat exp) =
    Dlet pat (full_normalise [] exp) /\
  full_normalise_decl (Dletrec l) =
    Dletrec (MAP (\ (f, n, e). (f, n, full_normalise [f; n] e)) l) /\
  full_normalise_decl decl = decl`;

val full_normalise_top_def = Define `
  full_normalise_top (Tdec decl) = Tdec (full_normalise_decl decl) /\
  full_normalise_top top = top`;

val full_normalise_prog_def = Define `
  full_normalise_prog prog = MAP full_normalise_top prog`;

val _ = export_theory ()
