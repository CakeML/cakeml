open preamble
open set_sepTheory helperLib ml_translatorTheory ConseqConv
open semanticPrimitivesTheory cfHeapsTheory
open cfHeapsBaseLib cfStoreTheory
open cfTacticsBaseLib
open funBigStepTheory
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


(*------------------------------------------------------------------*)
(* [full_normalise] *)

val MEM_exp_size = prove(
  ``!args a. MEM a args ==> exp_size a <= exp6_size args``,
  Induct \\ fs [astTheory.exp_size_def] \\ rw [] \\ res_tac \\ fs []);

val MEM_exp1_size = prove(
  ``!rs. MEM (v,a,e') rs ==> exp_size e' < exp1_size rs``,
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

val get_name_def = Define `
  get_name vs = get_name_aux 0 vs`;

val get_names_def = Define `
  (get_names vs [] = []) /\
  (get_names vs (x::xs) =
     let v = get_name vs in
       (v,x)::get_names (v::vs) xs)`

val isVarLit_def = Define `
  isVarLit (Var v) = T /\
  isVarLit (Lit l) = T /\
  isVarLit _ = F`

val Lets_def = Define `
  Lets [] e = e /\
  Lets ((INL _)::xs) e = Lets xs e /\
  Lets ((INR (n,x))::xs) e = Let (SOME n) x (Lets xs e)`

val delete_opt_def = Define `
  delete_opt NONE xs = xs /\
  delete_opt (SOME v) xs = FILTER (\x. v <> x) xs`

val bind_lets_def = Define `
  bind_lets xs =
    let ns = FLAT (MAP SND xs) in
    let ys = get_names ns xs in
    let ys = MAP (\(n,e,ns). (if isVarLit e then INL e else INR (n,e))) ys in
    let new_args = MAP (\x. case x of INL e => e | INR (n,e) => Var (Short n)) ys in
      (ns,ys,new_args)`

val bind_let2_def = Define `
  bind_let2 x y =
    let (ns,ys,new_args) = bind_lets [x;y] in
      (ns,ys,HD new_args, HD (TL new_args))`;

val bind_let_def = Define `
  bind_let x =
    let (ns,ys,new_args) = bind_lets [x] in
      (ns,ys,HD new_args)`;

val norm_def = tDefine "norm" `
  norm (Lit l) = (Lit l,[]) /\
  norm (Var (Short name)) = (Var (Short name),[name]) /\
  norm (Var long) = (Var long,[]) /\
  norm (Let opt e1 e2) =
    (let (e1,n1) = norm e1 in
     let (e2,n2) = norm e2 in
       (Let opt e1 e2,n1 ++ delete_opt opt n2)) /\
  norm (App op args) =
    (let (ns,ys,new_args) = bind_lets (MAP norm args) in
       (Lets ys (App op new_args),ns)) /\
  norm (Con x args) =
    (let (ns,ys,new_args) = bind_lets (MAP norm args) in
       (Lets ys (Con x new_args),ns)) /\
  norm (Raise e) =
    (let (ns,ys,new_e) = bind_let (norm e) in
       (Lets ys (Raise new_e),ns)) /\
  norm (Log l e1 e2) =
    (let (ns,ys,e1,e2) = bind_let2 (norm e1) (norm e2) in
       (Lets ys (Log l e1 e2),ns)) /\
  norm (Fun v e) =
    (let (e,n) = norm e in
       (Fun v e,delete_opt (SOME v) n)) /\
  norm (Mat e1 e2) =
    (let (e1,n1) = norm e1 in
     let (e2,n2) = norm_pat e2 in
       (Mat e1 e2,n1 ++ n2)) /\
  norm (Handle e1 e2) =
    (let (e1,n1) = norm e1 in
     let (e2,n2) = norm_pat e2 in
       (Handle e1 e2,n1 ++ n2)) /\
  norm (If e1 e2 e3) =
    (let (e1,n1) = norm e1 in
     let (e2,n2) = norm e2 in
     let (e3,n3) = norm e3 in
       if isVarLit e1 then
         (If e1 e2 e3, n1++n2++n3)
       else
         let v = get_name (n2++n3) in
           (Let (SOME v) e1 (If (Var (Short v)) e2 e3),n1++n2++n3)) /\
  norm (Letrec rs e) =
    (let xs = MAP (\(v,a,e). (v,a,norm e)) rs in
     let rs = MAP (\(v,a,e,_). (v,a,e)) xs in
     let ns = FLAT (MAP (\(v,a,e,n). n) xs) in
     let (e,n) = norm e in
       (Letrec rs e,n)) /\
  norm_pat [] = ([],[]) /\
  norm_pat ((pat,x)::xs) =
    (let (e1,n1) = norm x in
     let (e2,n2) = norm_pat xs in
       ((pat,e1)::e2,n1 ++ n2))`
 (WF_REL_TAC `measure (\x. case x of INL v => exp_size v
                                   | INR v => exp3_size v)`
  \\ fs [] \\ rw [] \\ imp_res_tac MEM_exp_size \\ fs []
  \\ imp_res_tac MEM_exp1_size \\ fs [])

val full_normalise_def = Define `
  full_normalise e = FST (norm e)`;

val MEM_v_size = prove(
  ``!xs. MEM a xs ==> v_size a < v6_size xs``,
  Induct  \\ fs [v_size_def] \\ rw [] \\ res_tac \\ fs []);

val norm_exp_rel_def = Define `
  norm_exp_rel e1 e2 <=> (e1 = e2) \/
                         (e1 = full_normalise e2) \/
                         (full_normalise e1 = e2)`

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
  (!v env1 env2 e1 e2.
     norm_exp_rel e1 e2 /\ (free_in e1 = free_in e2) /\
     env_rel (free_in e1 DELETE Short v1) env1 env2 ==>
     norm_rel (Closure env1 v e1) (Closure env2 v e2)) /\
  (!v env1 env2 es1 es2.
     EVERY2 (\(n1,v1,e1) (n2,v2,e2).
       n1 = n2 /\ v1 = v2 /\ norm_exp_rel e1 e2 /\ (free_in e1 = free_in e2) /\
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
val full_normalise_correct = store_thm("full_normalise_correct",
  ``env_rel (free_in e) env1 env2 /\ norm_state_rel s1 s2 /\
    evaluate ck env1 s1 e (rs1,res1) ==>
    ?rs2 res2. evaluate ck env2 s2 (full_normalise e) (rs2,res2) /\
               norm_state_rel rs1 rs2 /\ norm_res_rel res1 res2``,
  ... ); TODO
*)

val _ = export_theory ()
