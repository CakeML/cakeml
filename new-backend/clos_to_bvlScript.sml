open HolKernel Parse boolLib bossLib;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open rich_listTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory bvlTheory bvl_jumpTheory;
open sptreeTheory bvl_inlineTheory intLib miscLib;

val el_append2 = Q.prove (
`∀l x. EL (LENGTH l) (l++[x]) = x`,
 Induct_on `l` >>
 rw []);

val take1 = Q.prove (
`!l. l ≠ [] ⇒ TAKE 1 l = [EL 0 l]`,
 Induct_on `l` >>
 rw []);

val hd_drop = Q.prove (
`!n l. n < LENGTH l ⇒ HD (DROP n l) = EL n l`,
 Induct_on `l` >>
 rw [] >>
 `n - 1 < LENGTH l` by decide_tac >>
 res_tac >>
 `0 < n` by decide_tac >>
 rw [EL_CONS] >>
 `n - 1 = PRE n` by decide_tac >>
 rw []);

val _ = new_theory "clos_to_bvl";

(* compiler definition *)
val mk_const_def = Define `
  mk_const n : bvl_exp = Op (Const (&n)) []`;

val mk_label_def = Define `
  mk_label n : bvl_exp = Op (Label n) []`;

val mk_el_def = Define `
  mk_el b i : bvl_exp = Op El [i; b]`;

val _ = export_rewrites ["mk_const_def", "mk_label_def", "mk_el_def"];

val free_let_def = Define `
  free_let cl n = (GENLIST (\n. mk_el cl (mk_const (n+2))) n) : bvl_exp list`;

val code_for_recc_case_def = Define `
  code_for_recc_case n num_args (c:bvl_exp) =
    Let [mk_el (Var 0) (mk_const 2)]
      (Let (GENLIST (\a. Var (a + 2)) num_args ++ GENLIST (\i. Op Deref [mk_const i; Var 0]) n) c)`

val build_aux_def = Define `
  (build_aux i [] aux = (i:num,aux)) /\
  (build_aux i ((x:bvl_exp)::xs) aux = build_aux (i+1) xs ((i,ARB,x) :: aux))`;

val recc_Let_def = Define `
  recc_Let n num_args i =
    Let [mk_el (Var 0) (mk_const 2)]
     (Let [Op (Cons closure_tag) [Var 0; mk_const num_args; mk_label n]]
       (Let [Op Update [Var 0; mk_const i; Var 1]]
         (Var 1 : bvl_exp)))`;

val recc_Lets_def = Define `
  recc_Lets n nargs k rest =
    if k = 0:num then rest else
      let k = k - 1 in
        Let [recc_Let (n + k) (HD nargs) k] (recc_Lets n (TL nargs) k rest)`;

val recc_Let0_def = Define `
  recc_Let0 n i =
    Let [Op (Cons closure_tag) [Var 0; mk_label n]]
      (Let [Op Update [Var 0; mk_const i; Var 1]] (Var 1 : bvl_exp))`;

val build_recc_lets_def = Define `
  build_recc_lets (nargs:num list) vs n1 fns_l (c3:bvl_exp) =
    Let [Let [Op Ref (REVERSE (MAP (K (mk_const 0)) nargs ++ MAP Var vs))]
           (recc_Let0 (n1 + (fns_l - 1)) (fns_l - 1))]
      (recc_Lets n1 nargs (fns_l - 1) c3)`;

val num_stubs_def = Define `
  num_stubs = max_app * max_app + max_app`;

val mk_cl_call_def = Define `
  mk_cl_call cl args =
    If (Op Equal [mk_const (LENGTH args - 1); mk_el cl (mk_const 1)])
       (Call (LENGTH args - 1) NONE (args ++ [cl] ++ [mk_el cl (mk_const 0)]))
       (Call 0 (SOME (LENGTH args - 1)) (args ++ [cl]))`;

val partial_app_fn_location_def = Define `
  partial_app_fn_location m n = max_app + max_app * m + n`;

(* Generic application of a function to n+1 arguments *)
val generate_generic_app_def = Define `
  generate_generic_app n =
    Let [Op Sub [mk_const (n+1); mk_el (Var (n+1)) (mk_const 1)]] (* The number of arguments remaining - 1 *)
        (If (Op Less [mk_const 0; Var 0])
            (* Over application *)
            (Jump (mk_el (Var (n+2)) (mk_const 1))
              (GENLIST (\num_args. 
                 Let [Call num_args
                           NONE (GENLIST (\arg. Var (arg + 2 + n - num_args)) (num_args + 1) ++
                                 [Var (n + 3)] ++
                                 [mk_el (Var (n + 3)) (mk_const 0)])]
                   (mk_cl_call (Var 0) (GENLIST (\n. Var (n + 4)) (n - num_args))))
               max_app))
            (* Partial application *)
            (mk_tick n
            (If (Op (TagEq closure_tag) [Var (n+2)])
                (* Partial application of a normal closure *)
                (Op (Cons partial_app_tag)
                    (REVERSE 
                      (Jump (mk_el (Var (n+2)) (mk_const 1))
                        (GENLIST (\total_args. 
                          mk_label (partial_app_fn_location total_args n)) 
                         max_app) ::
                       Var 0 ::
                       Var (n + 2) ::
                       GENLIST (\n. Var (n + 1)) (n + 1))))
                (* Partial application of a partially applied closure *)
                (Jump (Op Sub [mk_const 4; Op LengthBlock [Var (n+2)]])
                  (GENLIST (\prev_args.
                    Op (Cons partial_app_tag)
                       (REVERSE
                         (Jump (Op Add [mk_const (n + prev_args + 2); Var 1])
                            (GENLIST (\total_args.
                              mk_label (partial_app_fn_location total_args (n + prev_args + 1)))
                             max_app) ::
                          Var 1 ::
                          mk_el (Var (n+3)) (mk_const 2) ::
                          GENLIST (\this_arg. Var (this_arg + 2)) (n+1) ++
                          GENLIST (\prev_arg.
                            mk_el (Var (n+3)) (mk_const (prev_arg + 3))) (prev_args + 1))))
                    max_app)))))`;

(* The functions to complete the application of a partial closure *)
val generate_partial_app_closure_fn_def = Define `
  generate_partial_app_closure_fn total_args prev_args = 
    Let [mk_el (Var 0) (mk_const 2)]
      (Call (total_args - prev_args - 1)
        NONE 
        (Var 0 ::
         GENLIST (\this_arg. Var (this_arg + 2)) (total_args - prev_args) ++
         GENLIST (\prev_arg.
           mk_el (Var 1) (mk_const (prev_arg + 3))) (prev_args + 1) ++
         [mk_el (Var 0) (mk_const 0)]))`;

val init_code_def = Define `
  init_code = 
    GENLIST (\n. (n + 2, generate_generic_app n)) max_app ++ 
    FLAT (GENLIST (\m. GENLIST (\n. (m - n + 1, 
                                     generate_partial_app_closure_fn m n)) max_app) max_app)`;

val cCompOp_def = Define`
  cCompOp (Cons tag) = (Cons (if tag < closure_tag then tag else tag+1)) ∧
  cCompOp (TagEq tag) = (TagEq (if tag < closure_tag then tag else tag+1)) ∧
  cCompOp x = x`
val _ = export_rewrites["cCompOp_def"];

val cComp_def = tDefine "cComp" `
  (cComp [] aux = ([],aux)) /\
  (cComp ((x:clos_exp)::y::xs) aux =
     let (c1,aux1) = cComp [x] aux in
     let (c2,aux2) = cComp (y::xs) aux1 in
       (c1 ++ c2, aux2)) /\
  (cComp [Var v] aux = ([(Var v):bvl_exp], aux)) /\
  (cComp [If x1 x2 x3] aux =
     let (c1,aux1) = cComp [x1] aux in
     let (c2,aux2) = cComp [x2] aux1 in
     let (c3,aux3) = cComp [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3)) /\
  (cComp [Let xs x2] aux =
     let (c1,aux1) = cComp xs aux in
     let (c2,aux2) = cComp [x2] aux1 in
       ([Let c1 (HD c2)], aux2)) /\
  (cComp [Raise x1] aux =
     let (c1,aux1) = cComp [x1] aux in
       ([Raise (HD c1)], aux1)) /\
  (cComp [Tick x1] aux =
     let (c1,aux1) = cComp [x1] aux in
       ([Tick (HD c1)], aux1)) /\
  (cComp [Op op xs] aux =
     let (c1,aux1) = cComp xs aux in
       ([Op (cCompOp op) c1],aux1)) /\
  (cComp [App loc_opt x1 xs2] aux =
     let (c1,aux1) = cComp [x1] aux in
     let (c2,aux2) = cComp xs2 aux1 in
       ([case loc_opt of
         | NONE => 
             Let (c2++c1) (mk_cl_call (Var (LENGTH c2)) (GENLIST Var (LENGTH c2)))
         | SOME loc => 
             (Call (LENGTH c2 - 1) (SOME (loc + num_stubs)) (c2 ++ c1))],
        aux2)) /\
  (cComp [Fn loc vs num_args x1] aux =
     let (c1,aux1) = cComp [x1] aux in
     let c2 = 
       Let (GENLIST Var num_args ++ free_let (Var num_args) (LENGTH vs)) 
           (HD c1) 
     in
       ([Op (Cons closure_tag)
            (REVERSE (mk_label (loc + num_stubs) :: mk_const (num_args - 1) :: MAP Var vs))],
        (loc + num_stubs,num_args+1,c2) :: aux1)) /\
  (cComp [Letrec loc vs fns x1] aux =
     case fns of
     | [] => cComp [x1] aux
     | [(num_args, exp)] =>
         let (c1,aux1) = cComp [exp] aux in
         let c3 = Let (GENLIST Var num_args ++ [Var num_args] ++ free_let (Var num_args) (LENGTH vs)) (HD c1) in
         let (c2,aux2) = cComp [x1] ((loc + num_stubs,num_args+1,c3)::aux1) in
         let c4 = 
           Op (Cons closure_tag) 
              (REVERSE (mk_label (loc + num_stubs) :: mk_const (num_args - 1) :: MAP Var vs)) 
         in
           ([Let [c4] (HD c2)], aux2)
     | _ =>
         let fns_l = LENGTH fns in
         let l = fns_l + LENGTH vs in
         let (cs,aux1) = cComp (MAP SND fns) aux in
         let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs in
         let (n2,aux2) = build_aux (loc + num_stubs) cs1 aux1 in
         let (c3,aux3) = cComp [x1] aux2 in
         let c4 = build_recc_lets (MAP FST fns) vs (loc + num_stubs) fns_l (HD c3) in
           ([c4],aux3)) /\
  (cComp [Handle x1 x2] aux =
     let (c1,aux1) = cComp [x1] aux in
     let (c2,aux2) = cComp [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2)) /\
  (cComp [Call dest xs] aux =
     let (c1,aux1) = cComp xs aux in
       ([Call 0 (SOME (dest + num_stubs)) c1],aux1))`
 (WF_REL_TAC `measure (clos_exp3_size o FST)` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  `!l. clos_exp3_size (MAP SND l) <= clos_exp1_size l` 
           by (Induct_on `l` >>
               rw [clos_exp_size_def] >>
               PairCases_on `h` >>
               full_simp_tac (srw_ss()++ARITH_ss) [clos_exp_size_def]) >>
 pop_assum (qspec_then `v7` assume_tac) >>
 decide_tac);


(* correctness proof *)

(* -------------- Begin proofs for partial/over application --------------- *)

val bEval_length_imp = Q.prove (
`!xs env s1 vs s2.
  bEval (xs, env, s1) = (Result vs, s2)
  ⇒
  LENGTH xs = LENGTH vs`,
 rw [] >>
 assume_tac (Q.SPECL [`xs`, `env`, `s1`] bEval_LENGTH) >>
 rfs []);

val take_drop_lem = Q.prove (
`!skip env. 
  skip < LENGTH env ∧
  skip + SUC n ≤ LENGTH env ∧
  DROP skip env ≠ [] ⇒
  EL skip env::TAKE n (DROP (1 + skip) env) = TAKE (n + 1) (DROP skip env)`,
 Induct_on `n` >>
 rw [take1, hd_drop] >>
 `skip + SUC n ≤ LENGTH env` by decide_tac >>
 res_tac >>
 `LENGTH (DROP skip env) = LENGTH env - skip` by rw [LENGTH_DROP] >>
 `SUC n < LENGTH (DROP skip env)` by decide_tac >>
 `LENGTH (DROP (1 + skip) env) = LENGTH env - (1 + skip)` by rw [LENGTH_DROP] >>
 `n < LENGTH (DROP (1 + skip) env)` by decide_tac >>
 rw [TAKE_EL_SNOC, ADD1] >>
 `n + (1 + skip) < LENGTH env` by decide_tac >>
 `(n+1) + skip < LENGTH env` by decide_tac >>
 rw [EL_DROP] >>
 srw_tac [ARITH_ss] []);

val bEval_genlist_vars = Q.prove (
`!skip env n st.
  n + skip ≤ LENGTH env ⇒
  bEval (GENLIST (λarg. Var (arg + skip)) n, env, st)
  =
  (Result (TAKE n (DROP skip env)), st)`,
 Induct_on `n` >>
 rw [bEval_def, DROP_LENGTH_NIL, GSYM ADD1] >>
 rw [Once GENLIST_CONS] >>
 rw [Once bEval_CONS, bEval_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 first_x_assum (qspecl_then [`skip + 1`, `env`] mp_tac) >>
 rw [] >>
 `n + (skip + 1) ≤ LENGTH env` by decide_tac >>
 fs [] >>
 rw [combinTheory.o_DEF, ADD1, GSYM ADD_ASSOC] >>
 `skip + 1 = 1 + skip ` by decide_tac >>
 fs [] >>
 `LENGTH (DROP skip env) = LENGTH env - skip` by rw [LENGTH_DROP] >>
 `n < LENGTH env - skip` by decide_tac >>
 `DROP skip env ≠ []` 
       by (Cases_on `DROP skip env` >>
           fs [] >>
           decide_tac) >>
 metis_tac [take_drop_lem]);

val bEval_var_reverse = Q.prove (
`!xs env n ys st.
 bEval (MAP Var xs, env, st) = (Result ys, st)
 ⇒
 bEval (REVERSE (MAP Var xs), env, st) = (Result (REVERSE ys), st)`,
 Induct_on `xs` >>
 rw [bEval_def] >>
 fs [bEval_APPEND] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once bEval_CONS]) >>
 rw [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [bEval_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 rw [] >>
 res_tac >>
 fs []);

val bEval_genlist_vars_rev = Q.prove (
`!skip env n st.
  n + skip ≤ LENGTH env ⇒
  bEval (REVERSE (GENLIST (λarg. Var (arg + skip)) n), env, st) =
  (Result (REVERSE (TAKE n (DROP skip env))), st)`,
 rw [] >>
 imp_res_tac bEval_genlist_vars >>
 pop_assum (qspec_then `st` assume_tac) >>
 `GENLIST (λarg. Var (arg + skip):bvl_exp) n = MAP Var (GENLIST (\arg. arg + skip) n)`
          by rw [MAP_GENLIST, combinTheory.o_DEF] >>
 fs [] >>
 metis_tac [bEval_var_reverse]);


 (*
val bEval_genlist_vars = Q.prove (
`!x st args. 
  bEval (REVERSE (GENLIST (\n. Var (n+LENGTH x)) (LENGTH args)), x++args,st) = 
  (Result (REVERSE args), st)`,
 Induct_on `args` >>
 rw [bEval_def, GENLIST_CONS] >>
 rw [bEval_APPEND, bEval_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 pop_assum (qspecl_then [`x++[h]`] mp_tac) >>
 srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
 `x ++ h :: args = x ++ [h] ++ args` by metis_tac [APPEND, APPEND_ASSOC] >>
 rw [el_append3]);

val bEval_genlist_vars1 = Q.prove (
`!x st args. 
  bEval (REVERSE (GENLIST (\n. Var (n+1)) (LENGTH args)), x::args,st) = 
  (Result (REVERSE args), st)`,
 metis_tac [bEval_genlist_vars, APPEND, LENGTH, DECIDE ``SUC 0 = 1``]);

val bEval_genlist_vars2 = Q.prove (
`!x y st args. 
  bEval (REVERSE (GENLIST (\n. Var (n+2)) (LENGTH args)), x::y::args,st) = 
  (Result (REVERSE args), st)`,
 metis_tac [bEval_genlist_vars, APPEND, LENGTH, DECIDE ``SUC (SUC 0) = 2``]);

val bEval_genlist_vars3 = Q.prove (
`!x y z st args. 
  bEval (REVERSE (GENLIST (\n. Var (n+3)) (LENGTH args)), x::y::z::args,st) = 
  (Result (REVERSE args), st)`,
 metis_tac [bEval_genlist_vars, APPEND, LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``]);

val bEval_genlist_vars_no_rev = Q.prove (
`!x st args. 
  bEval (GENLIST (\n. Var (n+LENGTH x)) (LENGTH args), x++args,st) = 
  (Result args, st)`,
 Induct_on `args` >>
 rw [bEval_def, GENLIST_CONS] >>
 rw [Once bEval_CONS, bEval_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 pop_assum (qspecl_then [`x++[h]`] mp_tac) >>
 srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
 `x ++ h :: args = x ++ [h] ++ args` by metis_tac [APPEND, APPEND_ASSOC] >>
 rw [el_append3]);

val bEval_genlist_vars2_no_rev = Q.prove (
`!x y st args. 
  bEval (GENLIST (\n. Var (n+2)) (LENGTH args), x::y::args,st) = 
  (Result args, st)`,
 metis_tac [bEval_genlist_vars_no_rev, APPEND, LENGTH, DECIDE ``SUC (SUC 0) = 2``]);

val bEval_genlist_vars_skip_lem = Q.prove (
`!skip x rem_args.
  skip < LENGTH x ⇒ 
  EL skip x :: TAKE (rem_args + 1) (DROP (1 + skip) x) = TAKE (rem_args + 2) (DROP skip x)`,
 Induct_on `x` >>
 srw_tac [ARITH_ss] [EL_CONS] >>
 `PRE skip = skip - 1` by decide_tac >>
 rw [] >>
 fs [ADD1] >>
 first_x_assum (qspecl_then [`skip -1`, `rem_args`] mp_tac) >>
 rw [] >>
 `skip < 1 + LENGTH x ∧ 0 < LENGTH x` by decide_tac >>
 fs [] >>
 `1 + (skip - 1) = skip` by decide_tac >>
 fs []);

val bEval_genlist_vars_skip = Q.prove (
`!arg_list rem_args st skip x.
  skip + rem_args < LENGTH arg_list + LENGTH x ∧
  LENGTH x ≤ skip
  ⇒
  bEval (GENLIST (λarg. Var (arg + skip)) (rem_args + 1),
         x++arg_list,
         st)
  =
  (Result (TAKE (rem_args + 1) (DROP skip (x++arg_list))), st)`,
 Induct_on `rem_args` >>
 rw [bEval_def, DROP_LENGTH_NIL, GSYM ADD1] >>
 rw [Once GENLIST_CONS] >>
 rw [Once bEval_CONS, bEval_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) []
 >- (rw [EL_APPEND2, DROP_APPEND2] >>
     `DROP (skip-LENGTH x) arg_list ≠ []` 
           by (rw [DROP_NIL] >>
               decide_tac) >>
     rw [take1] >>
     `skip - LENGTH x < LENGTH arg_list` by decide_tac >>
     rw [hd_drop])
 >- (rw [ADD1] >>
     first_x_assum (qspecl_then [`arg_list`, `st`, `skip + 1`, `x`] mp_tac) >>
     rw [ADD1, combinTheory.o_DEF, GSYM ADD_ASSOC] >>
     `skip + 1 = 1 + skip ` by decide_tac >>
     fs [] >>
     `rem_args + (1 + skip) < LENGTH arg_list + LENGTH x` by decide_tac >>
     `LENGTH x ≤ 1 + skip` by decide_tac >>
     fs [] >>
     rw [] >>
     match_mp_tac bEval_genlist_vars_skip_lem >>
     rw [] >>
     decide_tac));
     *)

val bEval_genlist_prev_args = Q.prove (
`!prev_args z x tag p n cl arg_list st.
  bEval (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + LENGTH z))) []; Var (LENGTH x)]) (LENGTH prev_args)),
         x++(Block tag (z++prev_args))::arg_list,
         st)
  =
  (Result (REVERSE prev_args),st)`,
 Induct_on `prev_args` >>
 rw [bEval_def, GENLIST_CONS] >>
 rw [bEval_APPEND, bEval_def, bEvalOp_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw [] >>
 pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
 srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
 `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
 rw [el_append3] >>
 `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
         by metis_tac [APPEND, APPEND_ASSOC] >>
 rw [el_append3] >>
 decide_tac);

val bEval_genlist_prev_args1 = Q.prove (
`!prev_args x y tag p n cl args st.
  bEval (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var (LENGTH args + 2)]) (LENGTH prev_args)),
         x::y::(args++[Block tag (p::n::cl::prev_args)]),
         st)
  =
  (Result (REVERSE prev_args),st)`,
 rw [] >>
 assume_tac (Q.SPECL [`prev_args`, `[p;n;cl]`, `x::y::args`] bEval_genlist_prev_args) >>
 full_simp_tac (srw_ss()++ARITH_ss) [ADD1]);

 (*
val bEval_genlist_prev_args1 = Q.prove (
`!prev_args z tag p n cl arg_list st.
  bEval (REVERSE (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var 1]) (LENGTH prev_args)),
         z::(Block tag (p::n::cl::prev_args))::arg_list,
         st)
  =
  (Result (REVERSE prev_args),st)`,
 metis_tac [bEval_genlist_prev_args, APPEND, LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``,
            DECIDE ``(SUC 0) = 1``]);

val bEval_genlist_prev_args_no_rev = Q.prove (
`!prev_args z x tag p n cl arg_list st.
  bEval (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + LENGTH z))) []; Var (LENGTH x)]) (LENGTH prev_args),
         x++(Block tag (z++prev_args))::arg_list,
         st)
  =
  (Result prev_args,st)`,
 Induct_on `prev_args` >>
 rw [bEval_def, GENLIST_CONS] >>
 rw [Once bEval_CONS, bEval_def, bEvalOp_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw [] >>
 pop_assum (qspecl_then [`z++[h]`] mp_tac) >>
 srw_tac [ARITH_ss] [combinTheory.o_DEF, ADD1] >>
 `z ++ h :: prev_args = z ++ [h] ++ prev_args` by metis_tac [APPEND, APPEND_ASSOC] >>
 rw [el_append3] >>
 `x ++ Block tag (z ++ [h] ++ prev_args)::arg_list = x ++ [Block tag (z ++ [h] ++ prev_args)] ++ arg_list`
         by metis_tac [APPEND, APPEND_ASSOC] >>
 rw [el_append3] >>
 decide_tac);

val bEval_genlist_prev_args1_no_rev = Q.prove (
`!prev_args z tag p n cl arg_list st.
  bEval (GENLIST (λprev_arg. Op El [Op (Const (&(prev_arg + 3))) []; Var 1]) (LENGTH prev_args),
         z::(Block tag (p::n::cl::prev_args))::arg_list,
         st)
  =
  (Result prev_args,st)`,
 metis_tac [bEval_genlist_prev_args_no_rev, APPEND, LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``,
            DECIDE ``(SUC 0) = 1``]);
            *)

val bEval_generic_app_helper = Q.prove (
`!n args.
  n+1 = LENGTH args
  ⇒
  EL (SUC n) (args ++ [x]) = x`,
 Induct_on `args` >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [ADD1, el_append2]);

val dec_clock_code = Q.store_thm ("dec_clock_code",
`!n (s:bvl_state). (dec_clock n s).code = s.code`,
 rw [dec_clock_def]);

val dec_clock_refs = Q.store_thm ("dec_clock_refs",
`!n (s:bvl_state). (dec_clock n s).refs = s.refs`,
 rw [dec_clock_def]);

val _ = export_rewrites ["dec_clock_refs", "dec_clock_code"];

val bEval_generic_app1 = Q.prove (
`!n args st total_args l fvs cl.
  partial_app_fn_location total_args n ∈ domain st.code ∧
  n < total_args ∧
  total_args < max_app ∧
  n + 1 = LENGTH args ∧
  cl = Block closure_tag (CodePtr l :: Number (&total_args) :: fvs)
  ⇒
  bEval ([generate_generic_app n], args++[cl], st) = 
    if st.clock < n then
      (TimeOut, st with clock := 0)
    else
      (Result [Block partial_app_tag (CodePtr (partial_app_fn_location total_args n) ::
                                      Number (&(total_args - (n + 1))) ::
                                      cl::
                                      args)],
       dec_clock n st)`,
 rw [generate_generic_app_def] >>
 rw [bEval_def, bEvalOp_def] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
 `~(&total_args − &(n+1) < 0)` by intLib.ARITH_TAC >>
 rw [] >>
 rfs [bEval_mk_tick, bEval_def, bEvalOp_def] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [el_append2] >>
 rw [DECIDE ``x + 2 = SUC (SUC x)``, bEval_generic_app_helper, bEval_APPEND] >>
 srw_tac [ARITH_ss] [ADD1, bEval_genlist_vars_rev, bEval_def] >>
 `bEval ([Op El [Op (Const (1:int)) []; Var (LENGTH args + 1)]],
         Number (&total_args − &(LENGTH args))::(args++[Block 5 (CodePtr l::Number (&total_args)::fvs)]),
         dec_clock n st) =
   (Result [Number (&total_args)], dec_clock n st)`
         by (srw_tac [ARITH_ss] [bEval_def, bEvalOp_def, int_arithTheory.INT_NUM_SUB] >>
             srw_tac [ARITH_ss][PRE_SUB1, EL_CONS, el_append2]) >>
 imp_res_tac bEval_Jump >>
 rfs [] >>
 srw_tac [ARITH_ss] [LENGTH_GENLIST, bEval_def, bEvalOp_def, bEval_APPEND] >>
 rw [bEval_def, bEvalOp_def, int_arithTheory.INT_NUM_SUB, el_append2, 
     TAKE_LENGTH_APPEND] >> 
 decide_tac);

val bEval_generic_app2 = Q.prove (
`!n args st rem_args prev_args l clo cl.
  partial_app_fn_location (rem_args + LENGTH prev_args) (n + LENGTH prev_args) ∈ domain st.code ∧
  n < rem_args ∧
  n + 1 = LENGTH args ∧
  LENGTH prev_args > 0 ∧
  rem_args + LENGTH prev_args < max_app ∧
  cl = Block partial_app_tag (CodePtr l :: Number (&rem_args) :: clo :: prev_args)
  ⇒
  bEval ([generate_generic_app n], args++[cl], st) = 
    if st.clock < n then
      (TimeOut, st with clock := 0)
    else
      (Result [Block partial_app_tag (CodePtr (partial_app_fn_location (rem_args + LENGTH prev_args) (n + LENGTH prev_args)) ::
                                      Number (&rem_args - &(n+1)) ::
                                      clo ::
                                      args ++ 
                                      prev_args)],
       dec_clock n st)`,
 rw [generate_generic_app_def, mk_const_def] >>
 rw [bEval_def, bEvalOp_def] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [bytecodeTheory.partial_app_tag_def] >>
 `~(&rem_args − &(n+1) < 0)` by intLib.ARITH_TAC >>
 rw [el_append2] >>
 rfs [bEval_mk_tick] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw [bEval_def, bEvalOp_def] >>
 rw [DECIDE ``x + 2 = SUC (SUC x)``, bEval_generic_app_helper, bEval_APPEND] >>
 rw [ADD1] >>
 `bEval ([Op Sub [Op (Const 4) []; Op LengthBlock [Var (LENGTH args + 1)]]],
         Number (&rem_args − &LENGTH args)::(args++[Block 6 (CodePtr l::Number (&rem_args)::clo::prev_args)]),dec_clock n st) =
   (Result [Number (&(LENGTH prev_args - 1))], dec_clock n st)`
         by (srw_tac [ARITH_ss] [bEval_def, bEvalOp_def, int_arithTheory.INT_NUM_SUB] >>
             srw_tac [ARITH_ss] [EL_CONS, GSYM ADD1, el_append2] >>
             intLib.ARITH_TAC) >>
 imp_res_tac bEval_Jump >>
 rfs [] >>
 srw_tac [ARITH_ss] [bEval_APPEND, LENGTH_GENLIST, bEval_def, bEvalOp_def] >>
 rw [REVERSE_APPEND, bEval_APPEND] >>
 `n + 3 = LENGTH args + 2` by decide_tac >>
 rw [bEval_genlist_prev_args1] >>
 srw_tac [ARITH_ss] [bEval_genlist_vars_rev, EL_CONS, PRE_SUB1, el_append2] >>
 `bEval ([Op Add [Op (Const (&(n + (LENGTH prev_args + 1)))) []; Var 1]],
         Number (&(LENGTH prev_args − 1))::Number (&rem_args − &LENGTH args)::(args++[Block partial_app_tag (CodePtr l::Number (&rem_args)::clo::prev_args)]),
         dec_clock n st) =
   (Result [Number (&(LENGTH prev_args + rem_args))], dec_clock n st)`
         by (srw_tac [ARITH_ss] [bytecodeTheory.partial_app_tag_def, bEval_def, bEvalOp_def, int_arithTheory.INT_NUM_SUB] >>
             intLib.ARITH_TAC) >>
 imp_res_tac bEval_Jump >>
 `LENGTH prev_args - 1 < max_app` by decide_tac >>
 fs [bytecodeTheory.partial_app_tag_def] >>
 srw_tac [ARITH_ss] [bEval_APPEND, REVERSE_APPEND, TAKE_LENGTH_APPEND, LENGTH_GENLIST, bEval_def, bEvalOp_def, mk_label_def]);

val (unpack_closure_rules, unpack_closure_ind, unpack_closure_cases) = Hol_reln `
(total_args ≥ 0
 ⇒
 unpack_closure (Block closure_tag (CodePtr l :: Number total_args :: fvs))
       ([], Num total_args, Block closure_tag (CodePtr l :: Number total_args :: fvs))) ∧
(prev_args ≠ [] ∧
 rem_args ≥ 0
 ⇒
 unpack_closure (Block partial_app_tag (CodePtr l :: Number rem_args :: clo :: prev_args)) 
       (prev_args, Num rem_args + LENGTH prev_args, clo))`;

val bEval_generic_app_partial = Q.prove (
`!total_args prev_args st args cl sub_cl.
  partial_app_fn_location total_args (LENGTH prev_args + (LENGTH args - 1)) ∈ domain st.code ∧
  total_args < max_app ∧
  LENGTH args < (total_args + 1) - LENGTH prev_args ∧
  LENGTH args ≠ 0 ∧
  unpack_closure cl (prev_args, total_args, sub_cl)
  ⇒
  bEval ([generate_generic_app (LENGTH args - 1)], args++[cl], st) = 
    if st.clock < LENGTH args - 1 then
      (TimeOut, st with clock := 0)
    else
      (Result [Block partial_app_tag (CodePtr (partial_app_fn_location total_args (LENGTH prev_args + (LENGTH args - 1))) ::
                                      Number (&(total_args - (LENGTH prev_args + LENGTH args))) ::
                                      sub_cl::
                                      args++
                                      prev_args)],
       dec_clock (LENGTH args - 1) st)`,
 rpt GEN_TAC >>
 strip_tac >>
 fs [unpack_closure_cases]
 >- (mp_tac (Q.SPECL [`LENGTH (args : bc_value list) - 1`, `args`, `st`, `total_args`] bEval_generic_app1) >>
     srw_tac [ARITH_ss] [] >>
     rfs [] >>
     `&Num total_args' = total_args'` by ARITH_TAC >>
     fs [] >>
     rw [])
 >- (mp_tac (Q.SPECL [`LENGTH (args : bc_value list) - 1`, `args`, `st`, `Num rem_args`, `prev_args`] bEval_generic_app2) >>
     full_simp_tac (srw_ss()++ARITH_ss) [] >>
     srw_tac [ARITH_ss] [] >>
     Cases_on `prev_args` >>
     fs [] >>
     rw [] >>
     `&Num rem_args = rem_args` by ARITH_TAC >>
     fs [] >>
     rw [int_arithTheory.INT_NUM_SUB] >>
     ARITH_TAC));

val bEval_generic_app3_lem = Q.prove (
`!rem_args arg_list.
 LENGTH arg_list > rem_args
 ⇒
 TAKE (rem_args + 1) (DROP (LENGTH arg_list − (rem_args + 1)) (arg_list ++ stuff)) =
 DROP (LENGTH arg_list − (rem_args + 1)) arg_list`,
 Induct_on `arg_list` >>
 rw [] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [ADD1, TAKE_LENGTH_APPEND] >>
 `LENGTH arg_list = rem_args` by decide_tac >>
 rw [] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [ADD1, TAKE_LENGTH_APPEND]);

val bEval_generic_app_full = Q.prove (
`!n args st rem_args vs l tag exp clo.
  lookup l st.code = SOME (rem_args + 2, exp) ∧
  n + 1 = LENGTH args ∧
  n > rem_args ∧
  rem_args < max_app
  ⇒
  bEval ([generate_generic_app n], args++[Block tag (CodePtr l :: Number (&rem_args) :: vs)], st) = 
  if st.clock < rem_args + 1 then (TimeOut, st with clock := 0) else
    case bEval ([exp],
                DROP (LENGTH args − (rem_args + 1)) args ++
                [Block tag (CodePtr l::Number (&rem_args)::vs)],
                dec_clock (rem_args + 1) st) of
      | (Result [v], st') =>
          (case
             bEval
               ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 4)) (n − rem_args))],
                v::Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                    args++[Block tag (CodePtr l::Number (&rem_args)::vs)],
                st')
           of
             (Result v,s2) => (Result [HD v],s2)
           | x => x)
      | x => x`,
 rw [generate_generic_app_def, mk_const_def] >>
 rw [bEval_def, bEvalOp_def, el_append2] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [bytecodeTheory.partial_app_tag_def] >>
 `(&rem_args − &(LENGTH args) < 0)` by intLib.ARITH_TAC >>
 rw [] >>
 `bEval ([Op El [Op (Const (1:int)) []; Var (LENGTH args + 1)]],
         Number (&rem_args − &LENGTH args):: (args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)]),
         st) =
   (Result [Number (&rem_args)], st)`
         by srw_tac [ARITH_ss] [bEval_def, bEvalOp_def, PRE_SUB1, EL_CONS, el_append2] >>
 `n + 2 = LENGTH args + 1` by decide_tac >>
 fs [] >>
 imp_res_tac bEval_Jump >>
 srw_tac [ARITH_ss] [LENGTH_GENLIST, bEval_def, bEvalOp_def] >>
 srw_tac [ARITH_ss] [bEval_APPEND, bEvalOp_def, bEval_def] >>
 srw_tac [ARITH_ss] [Once bEval_CONS, bEval_def, bEval_APPEND] >>
 fs [] >>
 `(rem_args + 1) + ((LENGTH args + 1) - rem_args) ≤ 
    LENGTH (Number (&rem_args)::Number (&rem_args − &LENGTH args)::
                (args ++
                 [Block tag (CodePtr l::Number (&rem_args)::vs)]))`
            by (rw [] >>
                decide_tac) >> 
 imp_res_tac bEval_genlist_vars >>
 pop_assum (qspec_then `st` mp_tac) >>
 `LENGTH args + 1 - rem_args = (LENGTH args + 1) - rem_args` by decide_tac >>
 simp [] >>
 rw [] >>
 simp [EL_CONS, PRE_SUB1, el_append2, find_code_def, bvl_state_explode, FRONT_APPEND] >>
 `LENGTH args > rem_args` by decide_tac >>
 rw [bEval_generic_app3_lem] >>
 qabbrev_tac `res1 = 
   bEval
     ([exp],
      DROP (LENGTH args − (rem_args + 1)) args ++ [Block tag (CodePtr l::Number (&rem_args)::vs)],
      dec_clock (rem_args + 1) st)` >> 
 Cases_on `res1` >>
 fs [] >>
 Cases_on `q` >>
 fs [] >>
 `LENGTH a = 1` by metis_tac [bEval_length_imp, LENGTH, DECIDE ``SUC 0 = 1``] >>
 Cases_on `a` >>
 fs [] >>
 Cases_on `t` >>
 fs [] >>
 BasicProvers.FULL_CASE_TAC >>
 BasicProvers.FULL_CASE_TAC >>
 `LENGTH a = 1` by metis_tac [bEval_length_imp, LENGTH, DECIDE ``SUC 0 = 1``] >>
 Cases_on `a` >>
 fs [] >>
 Cases_on `t` >>
 fs []);

val mk_cl_lem = Q.prove (
`l < LENGTH env
 ⇒
 bEval (GENLIST (λn. Var (n + 4)) l, a::b::c::env, st) = 
 bEval (GENLIST (λn. Var (n + 2)) l, a::env, st)`,
 rw [] >>
 `l + 4 ≤ LENGTH (a::b::c::env)` by srw_tac [ARITH_ss] [ADD1] >>
 `l + 2 ≤ LENGTH (a::env)` by srw_tac [ARITH_ss] [ADD1] >>
 imp_res_tac bEval_genlist_vars >>
 rw []);
  
val bEval_mk_cl_simpl = Q.prove (
`bEval ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 4)) (LENGTH args' − (n + 1)))],
                             v::a::b::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                             st')
 =
 bEval ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 2)) (LENGTH args' − (n + 1)))],
                             v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                             st')`,
 rw [mk_cl_call_def, bEval_def, bEvalOp_def] >>
 Cases_on `v` >>
 rw [] >>
 BasicProvers.FULL_CASE_TAC >>
 rw [bEval_APPEND] >>
 ntac 2 (pop_assum (mp_tac o GSYM)) >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [bEval_def, bEvalOp_def] >>
 `LENGTH args' - (n + 1) < LENGTH (args' ++ [Block tag (CodePtr p::Number (&n)::xs)])` 
             by srw_tac [ARITH_ss] [] >>
 srw_tac [ARITH_ss] [mk_cl_lem]);

val _ = augment_srw_ss[rewrites[bytecodeTerminationTheory.bc_equal_def]];

val bEval_mk_cl_call = Q.prove (
`!cl env s tag p n args args' exp exp2 xs.
  bEval ([cl],env,s) = (Result [Block tag (CodePtr p::Number &n::xs)], s) ∧
  bEval (args,env,s) = (Result args', s) ∧
  lookup p s.code = SOME (n+2, exp) ∧
  lookup (LENGTH args' - 1) s.code = SOME (LENGTH args' + 1, generate_generic_app (LENGTH args' - 1)) ∧
  LENGTH args' - 1 ≥ n ∧
  n < max_app ∧
  LENGTH args ≠ 0
  ⇒ 
  bEval ([mk_cl_call cl args],env,s) =
   if n = LENGTH args - 1 then
     if s.clock < LENGTH args 
     then (TimeOut,s with clock := 0)
     else bEval ([exp], 
                 args' ++ [Block tag (CodePtr p::Number (&(LENGTH args − 1))::xs)], 
                 dec_clock (LENGTH args) s) 
   else
       if s.clock < n + 2
       then (TimeOut,s with clock := 0)
       else
       case bEval ([exp], 
                   DROP (LENGTH args' − (n + 1)) args' ++ [Block tag (CodePtr p::Number (&n)::xs)], 
                   dec_clock (n + 2) s)
         of
          | (Result [v],st') =>
              (case bEval ([mk_cl_call (Var 0) (GENLIST (λn. Var (n + 2)) (LENGTH args' − (n + 1)))],
                            v::(args' ++ [Block tag (CodePtr p::Number (&n)::xs)]),
                            st') of
                  | (Result v,s2) => (Result [HD v],s2)
                  | x => x)
          | x => x`,
 rw [Once mk_cl_call_def, bEval_def, bEvalOp_def] >>
 fs [ADD1] >>
 Cases_on `n = &(LENGTH args − 1)` >>
 rw [bEval_APPEND, bEval_def, bEvalOp_def, find_code_def, FRONT_APPEND] >>
 simp [] >>
 imp_res_tac bEval_length_imp >>
 rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
 `LENGTH args' - 1 + 1 = LENGTH args'` by decide_tac >>
 `lookup p (dec_clock 1 s).code = SOME (n+2,exp)` by rw [] >>
 imp_res_tac bEval_generic_app_full >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def] >>
 simp [bEval_mk_cl_simpl]);

 (*
val bEval_partial_app_fn = Q.prove (
`!args prev_args tag num tag' num' l l' fvs st exp.
  LENGTH prev_args > 0 ∧
  lookup l' st.code = SOME (LENGTH args + LENGTH prev_args + 1, exp)
  ⇒
  bEval ([generate_partial_app_closure_fn (LENGTH prev_args + LENGTH args - 1) (LENGTH prev_args - 1)],
         Block tag (l::num::Block tag' (CodePtr l'::num'::fvs)::prev_args) :: args,
         st) =
  if st.clock = 0 then (TimeOut, st) else
  bEval ([exp],
         Block tag' (CodePtr l'::num'::fvs)::(args ++ prev_args),
         dec_clock st)`,
 rw [bEval_def, generate_partial_app_closure_fn_def, mk_const_def, bEvalOp_def] >>
 full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
 rw [Once bEval_CONS, bEval_def, bEval_APPEND, bEval_genlist_vars2_no_rev] >>
 rw [bEval_genlist_prev_args1_no_rev, bEvalOp_def, find_code_def] >>
 rw [LAST_DEF, FRONT_DEF, FRONT_APPEND] >>
 full_simp_tac (srw_ss()++ARITH_ss) []);
 *)

(* --------------- end partial/over application ----------------------- *)

val code_installed_def = Define `
  code_installed aux code =
    EVERY (\(n,num_args,exp). lookup n code = SOME (num_args,exp)) aux`;

(*
val closure_code_installed_def = Define `
  closure_code_installed code exps_ps (env:clos_val list) =
    EVERY (\(exp,p).
      ?aux c aux1.
        (cComp [exp] aux = ([c],aux1)) /\
        (lookup p code = SOME (2:num,code_for_recc_case
              (LENGTH env + LENGTH exps_ps) c)) /\
        code_installed aux1 code) exps_ps`
        *)

val (cl_rel_rules,cl_rel_ind,cl_rel_cases) = Hol_reln `
(
  num_args ≤ max_app ∧
  num_args ≠ 0 ∧
  (cComp [x] aux = ([c],aux1)) /\
  code_installed aux1 code /\
  (lookup (p + num_stubs) code = 
    SOME (num_args + 1:num,Let (GENLIST Var num_args++free_let (Var num_args) (LENGTH env)) c))
 ⇒
 cl_rel f refs code 
        (env,ys)
        (Closure p [] env num_args x) 
        (Block closure_tag (CodePtr (p + num_stubs) :: Number (&(num_args-1)) :: ys))) ∧
(
  num_args ≤ max_app ∧
  num_args ≠ 0 ∧
  cComp [x] aux = ([c],aux1) /\
  code_installed aux1 code /\
  lookup (p + num_stubs) code = 
    SOME (num_args + 1:num,Let (GENLIST Var (num_args+1)++free_let (Var num_args) (LENGTH env)) c)
  ⇒
  cl_rel f refs code (env,ys)
         (Recclosure p [] env [(num_args, x)] 0) 
         (Block closure_tag (CodePtr (p + num_stubs) :: Number (&(num_args-1)) :: ys)))`;
(*
  /\
  ((exps = MAP FST exps_ps) /\
   (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + n) (LENGTH exps_ps)) /\
   (rs = MAP (\p. Block closure_tag [CodePtr p; RefPtr r]) ps) /\
   ~(r IN FRANGE f) /\
   (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
   EVERY2 (val_rel f refs code) env ys /\
   1 < LENGTH exps /\ k < LENGTH exps /\
   closure_code_installed code exps_ps env ==>
   val_rel f refs code (Recclosure loc env exps k) (EL k rs))*)

val add_args_def = Define `
(add_args (Closure loc_opt args env num_args exp : clos_val) args' =
  SOME (Closure loc_opt (args'++args) env num_args exp)) ∧
(add_args (Recclosure loc_opt args env funs i : clos_val) args' =
  SOME (Recclosure loc_opt (args'++args) env funs i)) ∧
(add_args _ _ = NONE)`;

val get_num_args_def = Define `
(get_num_args (Closure loc_opt args env num_args exp : clos_val) = 
  SOME num_args) ∧
(get_num_args (Recclosure loc_opt args env funs i : clos_val) = 
  SOME (FST (EL i funs))) ∧
(get_num_args _ = NONE)`;

val (val_rel_rules,val_rel_ind,val_rel_cases) = Hol_reln `
  (val_rel f refs code (Number n) (Number n))
  /\
  (EVERY2 (val_rel f refs code) xs (ys:bc_value list) /\
   (t' = if t < closure_tag then t else t+1) ==>
   val_rel f refs code (Block t xs) (Block t' ys))
  /\
  ((FLOOKUP f r1 = SOME r2) ==>
   val_rel f refs code (RefPtr r1) (RefPtr r2))
  /\
  (EVERY2 (val_rel f refs code) env ys ∧
   cl_rel f refs code (env,ys) cl (Block closure_tag (CodePtr p :: Number n :: ys))
   ⇒
   val_rel f refs code cl (Block closure_tag (CodePtr p :: Number n :: ys)))
  /\
  (EVERY2 (val_rel f refs code) env fvs /\
   EVERY2 (val_rel f refs code) arg_env ys ∧
   arg_env ≠ [] ∧
   LENGTH arg_env < num_args ∧
   (lookup (partial_app_fn_location (num_args - 1) (LENGTH ys - 1)) code =
     SOME (num_args - LENGTH arg_env + 1, generate_partial_app_closure_fn (num_args-1) (LENGTH ys - 1))) ∧
   add_args cl arg_env = SOME cl_app ∧
   get_num_args cl = SOME num_args ∧
   cl_rel f refs code (env,fvs) cl cl'
   ⇒
   val_rel f refs code cl_app 
                       (Block partial_app_tag 
                              (CodePtr (partial_app_fn_location (num_args - 1) (LENGTH ys - 1)) :: 
                               Number (&(num_args - 1 - LENGTH arg_env)) :: cl' :: ys)))`;

val opt_val_rel_def = Define `
  (opt_val_rel f refs code NONE NONE = T) /\
  (opt_val_rel f refs code (SOME x) (SOME y) = val_rel f refs code x y) /\
  (opt_val_rel f refs code _ _ = F)`;

val opt_val_rel_elim = store_thm("opt_val_rel_elim",
  ``opt_val_rel f refs code = OPTION_REL (val_rel f refs code)``,
  simp[FUN_EQ_THM] >> Cases >> Cases >> simp[opt_val_rel_def,optionTheory.OPTREL_def])

val (res_rel_rules,res_rel_ind,res_rel_cases) = Hol_reln `
  (EVERY2 (val_rel f refs code) xs (ys:bc_value list) ==>
   res_rel f refs code (Result xs) (Result ys)) /\
  (val_rel f refs code x y ==>
   res_rel f refs code (Exception x) (Exception y)) /\
  (res_rel f refs code TimeOut TimeOut) /\
  (res_rel f refs code Error Error)`

val env_rel_def = Define `
  (env_rel f refs code [] [] = T) /\
  (env_rel f refs code [] ys = T) /\   (* bvl env allowed to contain extra stuff *)
  (env_rel f refs code (x::xs) [] = F) /\
  (env_rel f refs code (x::xs) (y::ys) <=>
     val_rel f refs code x y /\ env_rel f refs code xs ys)`;

val (ref_rel_rules,ref_rel_ind,ref_rel_cases) = Hol_reln `
  (EVERY2 (val_rel f refs code) xs ys ==>
   ref_rel f refs code (ValueArray xs) (ValueArray ys))`

val state_rel_def = Define `
  state_rel f (s:clos_state) (t:bvl_state) <=>
    (s.clock = t.clock) /\
    (s.output = t.output) /\
    s.restrict_envs /\
    (EVERY2 (opt_val_rel f t.refs t.code) s.globals t.globals /\
    INJ ($' f) (FDOM f) (FRANGE f) /\
    (FDOM f = FDOM s.refs) /\
    (FRANGE f SUBSET FDOM t.refs) /\
    (!n x. (FLOOKUP s.refs n = SOME x) ==>
           ?y m. (FLOOKUP f n = SOME m) /\
                 (FLOOKUP t.refs m = SOME y) /\
                 ref_rel f t.refs t.code x y) /\
    (!n. n < max_app ⇒ lookup n t.code = SOME (n + 2, generate_generic_app n)) ∧
    (!m n. m < max_app ∧ n < max_app ⇒ 
      lookup (partial_app_fn_location m n) t.code = SOME (m - n + 1, generate_partial_app_closure_fn m n)) ∧
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?aux1 c2 aux2.
        (cComp [c] aux1 = ([c2],aux2)) /\
        (lookup (name + num_stubs) t.code = SOME (arity,c2)) /\
        code_installed aux2 t.code))`;

val FDIFF_def = Define `
  FDIFF f1 f2 = DRESTRICT f1 (COMPL (FRANGE f2))`;

val state_rel_clocks = Q.prove (
`!s t x. state_rel f s t ⇒ state_rel f (s with clock := x) (t with clock := x)`,
 rw [state_rel_def]);

val cl_rel_SUBMAP = Q.prove (
`cl_rel f1 refs1 code (env,ys) x y ∧
 f1 SUBMAP f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
 cl_rel f2 refs2 code (env,ys) x y`,
 rw [cl_rel_cases]);
         (* Proabably for letrec 
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`) \\ fs []*)

val ETA2_THM = Q.prove (
`(\x y. f a b c x y) = f a b c`,
rw [FUN_EQ_THM]);

val val_rel_SUBMAP = prove(
  ``!x y. val_rel f1 refs1 code x y ==>
      f1 SUBMAP f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
      val_rel f2 refs2 code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (fs [SUBMAP_DEF,FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         disj1_tac >>
         qexists_tac `env` >>
         fs [ETA2_THM])
  THEN1 (imp_res_tac cl_rel_SUBMAP >>
         disj2_tac >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val env_rel_SUBMAP = prove(
  ``!env1 env2.
      env_rel f1 refs1 code env1 env2 /\
      f1 SUBMAP f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
      env_rel f2 refs2 code env1 env2``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC val_rel_SUBMAP) |> GEN_ALL;

val cl_rel_NEW_REF = Q.prove (
`!x y. cl_rel f1 refs1 code (env,ys) x y ==> ~(r IN FDOM refs1) ==>
       cl_rel f1 (refs1 |+ (r,t)) code (env,ys) x y`,
 rw [cl_rel_cases]);
         (* For letrec
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ fs [FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ fs []*)

val val_rel_NEW_REF = prove(
  ``!x y. val_rel f1 refs1 code x y ==> ~(r IN FDOM refs1) ==>
          val_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         disj1_tac >>
         qexists_tac `env` >>
         fs [ETA2_THM])
  THEN1 (imp_res_tac cl_rel_NEW_REF >>
         disj2_tac >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val cl_rel_UPDATE_REF = prove(
  ``!x y. cl_rel f1 refs1 code (env,ys) x y ==>
          (r IN FRANGE f1) ==>
          cl_rel f1 (refs1 |+ (r,t)) code (env,ys) x y``,
 rw [cl_rel_cases]);
         (* for letrec
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ fs [FAPPLY_FUPDATE_THM] \\ SRW_TAC [] []
  \\ fs [FRANGE_DEF] \\ METIS_TAC []*)

val val_rel_UPDATE_REF = prove(
  ``!x y. val_rel f1 refs1 code x y ==>
          (r IN FRANGE f1) ==>
          val_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         disj1_tac >>
         qexists_tac `env` >>
         fs [ETA2_THM])
  THEN1 (imp_res_tac cl_rel_UPDATE_REF >>
         disj2_tac >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val opt_val_rel_NEW_REF = prove(
  ``opt_val_rel f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
    opt_val_rel f1 (refs1 |+ (r,t)) code x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [opt_val_rel_def,val_rel_NEW_REF]);

val opt_val_rel_UPDATE_REF = prove(
  ``opt_val_rel f1 refs1 code x y /\ r IN FRANGE f1 ==>
    opt_val_rel f1 (refs1 |+ (r,t)) code x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [opt_val_rel_def,val_rel_UPDATE_REF]);

val env_rel_NEW_REF = prove(
  ``!x y.
      env_rel f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
      env_rel f1 (refs1 |+ (r,t)) code x y``,
  Induct \\ Cases_on `y` \\ fs [env_rel_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC val_rel_NEW_REF \\ fs []);

val FLOOKUP_FAPPLY = prove(
  ``FLOOKUP (f |+ (x,y)) n = if n = x then SOME y else FLOOKUP f n``,
  fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ fs []);

val cl_rel_NEW_F = prove(
  ``!x y.
      cl_rel f2 t2.refs t2.code (env,ys) x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      cl_rel (f2 |+ (pp,qq)) t2.refs t2.code (env,ys) x y``,
 rw [cl_rel_cases]);
         (* For letrec
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] []
  \\ fs [FLOOKUP_DEF]
  \\ fs [FRANGE_DEF,DOMSUB_FAPPLY_THM] \\ rfs []
  \\ METIS_TAC []*)

val val_rel_NEW_F = prove(
  ``!x y.
      val_rel f2 t2.refs t2.code x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      val_rel (f2 |+ (pp,qq)) t2.refs t2.code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (fs [FLOOKUP_FAPPLY] \\ SRW_TAC [] [] \\ fs [FLOOKUP_DEF])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         disj1_tac >>
         qexists_tac `env` >>
         fs [ETA2_THM])
  THEN1 (imp_res_tac cl_rel_NEW_F >>
         disj2_tac >>
         disj2_tac >>
         fs [ETA2_THM] >>
         metis_tac [] ))
  |> SPEC_ALL |> MP_CANON;

val opt_val_rel_NEW_F = prove(
  ``opt_val_rel f2 t2.refs t2.code x y ==>
    ~(pp IN FDOM f2) ==>
    ~(qq IN FDOM t2.refs) ==>
    opt_val_rel (f2 |+ (pp,qq)) t2.refs t2.code x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [opt_val_rel_def]
  \\ METIS_TAC [val_rel_NEW_F]) |> MP_CANON

val LESS_LENGTH_env_rel_IMP = prove(
  ``!env env2 n.
      n < LENGTH env /\ env_rel f refs code env env2 ==>
      n < LENGTH env2 /\ val_rel f refs code (EL n env) (EL n env2)``,
  Induct \\ fs [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases_on `n` \\ fs []);

val lookup_vars_IMP = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel f refs code env env2 ==>
      ?ys. (bEval (MAP Var vs,env2,t1) = (Result ys,t1)) /\
           EVERY2 (val_rel f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)``,
  Induct \\ fs [lookup_vars_def,bEval_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ fs [] \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [bEval_CONS]
  \\ fs [bEval_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\ fs []);

val build_aux_lemma = prove(
  ``!k n aux. ?aux1. SND (build_aux n k aux) = aux1 ++ aux``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`n+1`,`(n,ARB,h)::aux`]) \\ fs []);

val cComp_lem1 = Q.prove (
`!f x. (\(a,b). f a b) x = f (FST x) (SND x)`,
 rw [] >>
 PairCases_on `x` >>
 fs []);

val cComp_lem2 = Q.prove (
`!x y z. (x,y) = z ⇔ x = FST z ∧ y = SND z`,
 rw [] >>
 PairCases_on `z` >>
 rw []);

val cComp_lemma = prove(
  ``!xs aux.
      let (c,aux1) = cComp xs aux in
        (LENGTH c = LENGTH xs) /\ ?ys. aux1 = ys ++ aux``,
  recInduct (fetch "-" "cComp_ind") \\ REPEAT STRIP_TAC
  \\ fs [cComp_def] \\ SRW_TAC [] [] \\ fs [LET_DEF,ADD1]
  \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ BasicProvers.EVERY_CASE_TAC \\ rfs [] \\ fs [cComp_lem1] >>
  rw [] >>
  fs [cComp_lem2] >>
  rfs [cComp_def, LET_THM] >>
  fs [cComp_lem1, cComp_lem2] >>
  metis_tac [build_aux_lemma, APPEND_ASSOC]);

val cComp_LENGTH = prove(
  ``(cComp xs aux = (c,aux1)) ==> (LENGTH c = LENGTH xs)``,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`xs`,`aux`] cComp_lemma)
  \\ rfs [LET_DEF]);

val cComp_SING = prove(
  ``(cComp [x] aux = (c,aux1)) ==> ?d. c = [d]``,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`[x]`,`aux`] cComp_lemma) \\ rfs [LET_DEF]
  \\ Cases_on `c` \\ fs [] \\ Cases_on `t` \\ fs []);

val res_rel_Result =
  ``res_rel f refs code (Result x) (Result y)``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val res_rel_Result1 =
  ``res_rel f refs code (Result x) y``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val res_rel_Ex =
  ``res_rel f refs code (Exception x) y``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val val_rel_Closure =
  ``val_rel f refs code (Closure loc args env num_args exp) y``
  |> SIMP_CONV (srw_ss()) [val_rel_cases, cl_rel_cases]

val val_rel_SIMP = LIST_CONJ
  [``val_rel f refs code (RefPtr p) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases, cl_rel_cases],
   ``val_rel f refs code (Block tag xs) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases, cl_rel_cases],
   ``val_rel f refs code (Number i) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases, cl_rel_cases],
   ``val_rel f refs code (Closure loc args env num_args exp) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases, cl_rel_cases],
   ``val_rel f refs code (Recclosure loc args env exp k) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases, cl_rel_cases]]
  |> curry save_thm "val_rel_SIMP"

val bEval_free_let_Block = Q.prove (
`!ys zs.
  bEval ([x],env,s) = (Result [Block n (y::z::ys ++ zs)], s)
  ⇒
  bEval (free_let x (LENGTH ys),env,s) = (Result ys,s)`,
 ho_match_mp_tac SNOC_INDUCT >>
 rw [free_let_def, bEval_def] >>
 fs [SNOC_APPEND] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] >>
 res_tac >>
 fs [GENLIST, bEval_SNOC, bEvalOp_def, bEval_def] >>
 simp [EL_CONS, PRE_SUB1, el_append3])
  |> Q.SPECL [`ys`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];

val list_rel_IMP_env_rel = prove(
  ``!xs ys.
      LIST_REL (val_rel f refs code) xs ys ==>
      env_rel f refs code xs (ys ++ ts)``,
  Induct \\ Cases_on `ys` \\ fs [env_rel_def]
  \\ Cases_on `ts` \\ fs [env_rel_def]);

val cComp_IMP_code_installed = prove(
  ``(cComp xs aux = (c,aux1)) /\
    code_installed aux1 code ==>
    code_installed aux code``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL cComp_lemma) \\ fs [LET_DEF]
  \\ REPEAT STRIP_TAC \\ fs [code_installed_def]);

val IMP_IMP = save_thm("IMP_IMP",
  METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``);

val FLOOKUP_SUBMAP_IMP = prove(
  ``(FLOOKUP refs2 r = SOME x) /\ r NOTIN FRANGE f2 /\
    FDIFF refs2 f2 SUBMAP FDIFF refs6 f6 ==>
    (FLOOKUP refs6 r = SOME x) /\ r NOTIN FRANGE f6``,
  fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF] \\ METIS_TAC []);

  (*
val bEval_ValueArray_lemma = prove(
  ``!zs s r ts.
      (FLOOKUP s.refs r = SOME (ValueArray (zs ++ ts))) ==>
      (bEval
        (GENLIST (\i. Op Deref [Var 0; Op (Const (&i)) []]) (LENGTH zs),
         RefPtr r::env,s) = (Result zs,s))``,
  recInduct SNOC_INDUCT \\ REPEAT STRIP_TAC \\ fs [bEval_def,GENLIST]
  \\ fs [bEval_SNOC] \\ fs [bEval_def,bEvalOp_def]
  \\ fs [DECIDE ``n < SUC n + m:num``,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]);

val bEval_ValueArray = prove(
  ``(FLOOKUP s.refs r = SOME (ValueArray zs)) /\ (n = LENGTH zs) ==>
    (bEval
      (GENLIST (\i. Op Deref [Var 0; Op (Const (&i)) []]) n,
       RefPtr r::env,s) = (Result zs,s))``,
  REPEAT STRIP_TAC \\ fs []
  \\ MATCH_MP_TAC bEval_ValueArray_lemma
  \\ Q.EXISTS_TAC `[]` \\ fs []);
  *)

val bEval_MAP_Const = prove(
  ``!exps.
      bEval (MAP (K (Op (Const 0) [])) (exps:'a list),env,t1) =
        (Result (MAP (K (Number 0)) exps),t1)``,
  Induct \\ fs [bEval_def,bEval_CONS,bEvalOp_def]);

  (*
val bEval_recc_Lets = prove(
  ``!ll n n7 rr env' t1 ys c8.
     EVERY (\n. n7 + n IN domain t1.code) (GENLIST I (LENGTH ll)) ==>
     (bEval
       ([recc_Lets n7 (LENGTH ll) (HD c8)],
        Block closure_tag [CodePtr (n7 + LENGTH ll); RefPtr rr]::env',
        t1 with refs := t1.refs |+ (rr,
               ValueArray
               (MAP (K (Number 0)) ll ++
                Block closure_tag [CodePtr (n7 + LENGTH ll); RefPtr rr]::ys))) =
      bEval
       ([HD c8],
        GENLIST (\n. Block closure_tag [CodePtr (n7 + n); RefPtr rr])
                  (LENGTH ll + 1) ++ env',
        t1 with refs := t1.refs |+ (rr,
               ValueArray
               (GENLIST (\n. Block closure_tag [CodePtr (n7 + n); RefPtr rr])
                  (LENGTH ll + 1) ++ ys))))``,
  recInduct SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [recc_Lets_def] \\ fs [LET_DEF]
  \\ fs [bEval_def,recc_Let_def,bEvalOp_def]
  \\ fs [DECIDE ``0 < k + SUC n:num``,EVERY_SNOC,GENLIST]
  \\ fs [FLOOKUP_FAPPLY,DECIDE ``n < SUC n + m``,DECIDE ``0 < 1 + SUC n``,
         DECIDE ``0 < 1 + n:num``,DECIDE ``2 < 1 + (1 + (1 + n:num))``]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,MAP_APPEND,MAP]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ `LENGTH l = LENGTH ((MAP (K (Number 0)) l) : bc_value list)` by fs []
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
  \\ SIMP_TAC std_ss [LUPDATE_LENGTH] \\ fs []
  \\ FULL_SIMP_TAC std_ss [DECIDE ``SUC n + 1 = SUC (n+1)``,GENLIST]
  \\ FULL_SIMP_TAC std_ss [ADD1,SNOC_APPEND]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]) |> SPEC_ALL;
  *)

val NUM_NOT_IN_FDOM =
  MATCH_MP IN_INFINITE_NOT_FINITE (CONJ INFINITE_NUM_UNIV
    (Q.ISPEC `f:num|->'a` FDOM_FINITE))
  |> SIMP_RULE std_ss [IN_UNIV]

val EXISTS_NOT_IN_refs = prove(
  ``?x. ~(x IN FDOM (t1:bvl_state).refs)``,
  METIS_TAC [NUM_NOT_IN_FDOM])

val env_rel_APPEND = prove(
  ``!xs1 xs2.
      EVERY2 (val_rel f1 refs code) xs1 xs2 /\
      env_rel f1 refs code ys1 ys2 ==>
      env_rel f1 refs code (xs1 ++ ys1) (xs2 ++ ys2)``,
  Induct \\ Cases_on `xs2` \\ fs [env_rel_def]);

val EVERY2_GENLIST = prove(
  ``!n.
      (!k. k < n ==> P (f k) (g k)) ==>
      EVERY2 P (GENLIST f n) (GENLIST g n)``,
  Induct \\ fs [GENLIST] \\ REPEAT STRIP_TAC
  \\ fs [LIST_REL_APPEND_SING,SNOC_APPEND]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ DECIDE_TAC);

val MAP_FST_ZIP = prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (MAP FST (ZIP (xs,ys)) = xs) /\
      (MAP SND (ZIP (xs,ys)) = ys)``,
  Induct \\ Cases_on `ys` \\ fs []);

val EVERY_ZIP_GENLIST = prove(
  ``!xs.
      (!i. i < LENGTH xs ==> P (EL i xs,f i)) ==>
      EVERY P (ZIP (xs,GENLIST f (LENGTH xs)))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ fs [GENLIST] \\ REPEAT STRIP_TAC
  \\ fs [ZIP_SNOC,EVERY_SNOC] \\ REPEAT STRIP_TAC
  THEN1
   (FIRST_X_ASSUM MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EL_SNOC \\ fs []
    \\ `i < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC \\ METIS_TAC [])
  \\ `LENGTH xs < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
  \\ fs [SNOC_APPEND,EL_LENGTH_APPEND]);

  (*
val build_aux_MEM = prove(
  ``!c n aux n7 aux7.
       (build_aux n c aux = (n7,aux7)) ==>
       !k. k < LENGTH c ==> ?d. MEM (n + k,d) aux7``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+1`,`(n,h)::aux`]) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `k` \\ fs []
  THEN1 (MP_TAC (Q.SPECL [`c`,`n+1`,`(n,h)::aux`] build_aux_lemma) \\ fs []
         \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [])
  \\ RES_TAC \\ fs [ADD1,AC ADD_COMM ADD_ASSOC] \\ METIS_TAC []);
  *)

val cComp_CONS = store_thm("cComp_CONS",
  ``!xs x aux.
      cComp (x::xs) aux =
      (let (c1,aux1) = cComp [x] aux in
       let (c2,aux2) = cComp xs aux1 in
         (c1 ++ c2,aux2))``,
  Cases_on `xs` \\ fs[cComp_def] \\ fs [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val cComp_SNOC = store_thm("cComp_SNOC",
  ``!xs x aux.
      cComp (SNOC x xs) aux =
      (let (c1,aux1) = cComp xs aux in
       let (c2,aux2) = cComp [x] aux1 in
         (c1 ++ c2,aux2))``,
  Induct THEN1
   (fs [cComp_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ ONCE_REWRITE_TAC [cComp_CONS]
  \\ ASM_SIMP_TAC std_ss [cComp_def,LET_DEF,APPEND_NIL]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val build_aux_APPEND = prove(
  ``!xs x n aux.
      build_aux n (xs ++ [x]) aux =
        let (n1,aux1) = build_aux n xs aux in
          (n1+1,(n1,ARB,x)::aux1)``,
  Induct \\ fs [build_aux_def,LET_DEF]);

val build_aux_MOVE = prove(
  ``!xs n aux n1 aux1.
      (build_aux n xs aux = (n1,aux1)) <=>
      ?aux2. (build_aux n xs [] = (n1,aux2)) /\ (aux1 = aux2 ++ aux)``,
  Induct THEN1 (fs [build_aux_def] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [build_aux_def]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ fs [PULL_EXISTS]);

val build_aux_LENGTH = prove(
  ``!l n aux n1 t.
      (build_aux n l aux = (n1,t)) ==> (n1 = n + LENGTH l)``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

  (*
val cComp_LIST_IMP_cComp_EL = prove(
  ``!exps aux1 c7 aux7 i n8 n4 aux5.
      (cComp exps aux1 = (c7,aux7)) /\ i < LENGTH exps /\
      (build_aux n8 (MAP (code_for_recc_case k) c7) aux7 = (n4,aux5)) /\
      code_installed aux5 t1.code ==>
      ?aux c aux1'.
        cComp [EL i exps] aux = ([c],aux1') /\
        lookup (i + n8) t1.code =
        SOME (2,code_for_recc_case k c) /\
        code_installed aux1' t1.code``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = LENGTH exps` \\ fs [] THEN1
   (fs [SNOC_APPEND,EL_LENGTH_APPEND]
    \\ fs [GSYM SNOC_APPEND,cComp_SNOC]
    \\ `?c1 aux2. cComp exps aux1 = (c1,aux2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3. cComp [x] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Q.LIST_EXISTS_TAC [`aux2`] \\ fs []
    \\ IMP_RES_TAC cComp_SING \\ fs []
    \\ fs [build_aux_APPEND]
    \\ IMP_RES_TAC cComp_LENGTH \\ fs []
    \\ Cases_on `build_aux n8 (MAP (code_for_recc_case k) c1) aux3`
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ fs [code_installed_def]
    \\ IMP_RES_TAC build_aux_LENGTH
    \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ MP_TAC (Q.SPECL [`MAP (code_for_recc_case k) c1`,`n8`,`aux3`]
           build_aux_lemma) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [])
  \\ `i < LENGTH exps` by DECIDE_TAC
  \\ fs [EL_SNOC]
  \\ fs [cComp_SNOC]
  \\ `?c1 aux2. cComp exps aux1 = (c1,aux2)` by METIS_TAC [PAIR]
  \\ `?c3 aux3. cComp [x] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
  \\ fs [LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
  \\ SRW_TAC [] [] \\ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`n8`])
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC cComp_SING \\ SRW_TAC [] []
  \\ fs [MAP,build_aux_APPEND]
  \\ Cases_on `build_aux n8 (MAP (code_for_recc_case k) c1) aux3`
  \\ fs [LET_DEF] \\ NTAC 2 (POP_ASSUM MP_TAC)
  \\ MP_TAC (Q.SPECL [`[x]`,`aux2`] cComp_lemma)
  \\ fs [LET_DEF] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [build_aux_MOVE]
  \\ REPEAT STRIP_TAC \\ fs []
  \\ fs [code_installed_def]) |> SPEC_ALL;
  *)

val bEval_SING = prove(
  ``(bEval ([x],env,s) = (Result a,p1)) ==> ?d1. a = [d1]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC bEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs [LENGTH_NIL]);

val env_rel_IMP_LENGTH = prove(
  ``!env1 env2.
      env_rel f refs code env1 env2 ==>
      LENGTH env1 <= LENGTH env2``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]);

val env_rel_IMP_EL = prove(
  ``!env1 env2 n.
      env_rel f refs code env1 env2 /\ n < LENGTH env1 ==>
      val_rel f refs code (EL n env1) (EL n env2)``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ fs []);

val FDOM_FDIFF = prove(
  ``x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN FRANGE f2)``,
  fs [FDIFF_def,DRESTRICT_DEF]);

val EXISTS_NOT_IN_FDOM_LEMMA = prove(
  ``?x. ~(x IN FDOM (refs:num|->'a))``,
  METIS_TAC [NUM_NOT_IN_FDOM]);

val LEAST_NO_IN_FDOM = prove(
  ``(LEAST ptr. ptr NOTIN FDOM (refs:num|->'a)) NOTIN FDOM refs``,
  ASSUME_TAC (EXISTS_NOT_IN_FDOM_LEMMA |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs []);

val EVERY2_LUPDATE = prove(
  ``!xs ys P x y n.
      P x y /\ EVERY2 P xs ys ==>
      EVERY2 P (LUPDATE x n xs) (LUPDATE y n ys)``,
  Induct \\ Cases_on `ys` \\ fs [LUPDATE_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ fs [LUPDATE_def]);

val EL_index_ps = prove(
  ``!exps_ps index exp p.
      (MAP SND exps_ps = GENLIST (\n. n0 + n) (LENGTH exps_ps)) /\
      index < LENGTH exps_ps /\ (EL index exps_ps = (exp,p)) ==>
      n0 + index = p``,
  recInduct SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ fs [GENLIST,GSYM ADD1]
  \\ Cases_on `index = LENGTH l` \\ fs [EL_LENGTH_SNOC]
  \\ `index < LENGTH l` by DECIDE_TAC \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ fs [SNOC_APPEND,EL_APPEND1]);

val closure_ptr_def = Define `
  (closure_ptr (Closure loc _ _ _ _) = loc) /\
  (closure_ptr (Recclosure loc _ _ _ k) = loc + k)`;

val state_rel_globals = prove(
  ``state_rel f s t ⇒
    LIST_REL (opt_val_rel f t.refs t.code) s.globals t.globals``,
  rw[state_rel_def]);

(*
val bc_equal_clos_equal = prove(
  ``INJ ($' f) (FDOM f) (FRANGE f) ⇒
    (∀x y x1 y1.
           val_rel f r c x x1 ∧
           val_rel f r c y y1 ⇒
           clos_equal x y = bc_equal x1 y1) ∧
    (∀x y x1 y1.
           LIST_REL (val_rel f r c) x x1 ∧
           LIST_REL (val_rel f r c) y y1 ⇒
           clos_equal_list x y = bc_equal_list x1 y1)``,
  strip_tac >>
  HO_MATCH_MP_TAC clos_equal_ind >>
  rw[clos_equal_def] >> rw[clos_equal_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[val_rel_SIMP] >> rw[] >>
  fs[Q.SPECL[`f`,`r`,`c`,`Block a b`]val_rel_cases] >>
  simp[EL_MAP] >> rw[] >> fs[] >> rfs[EL_MAP] >>
  imp_res_tac LIST_REL_LENGTH >> fs[PULL_EXISTS] >>
  TRY (
    CHANGED_TAC(rw[EQ_IMP_THM]) >> fs[INJ_DEF] >>
    fs[FLOOKUP_DEF] >> NO_TAC) >>
  fs[GSYM AND_IMP_INTRO] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  Cases_on`n<3`>>fsrw_tac[ARITH_ss][]>>rfs[])
  *)

val clos_to_chars_thm = store_thm("clos_to_chars_thm",
  ``∀ls acc. clos_to_chars ls acc =
         if EVERY (λx. ∃i. x = Number i ∧ 0 ≤ i ∧ i < 256) ls then
           SOME (STRCAT (REVERSE acc) (MAP (CHR o Num o (λx. @i. x = Number i)) ls))
         else NONE``,
  ho_match_mp_tac clos_to_chars_ind >>
  rw[clos_to_chars_def] >> fs[] >>
  `i = ABS i` by intLib.COOPER_TAC >>
  PROVE_TAC[]);

  (*
val bv_to_string_clos_to_string = prove(
  ``∀x y. val_rel f r c x y ⇒ clos_to_string x = bv_to_string y``,
  ho_match_mp_tac (theorem"val_rel_strongind") >>
  rw[clos_to_string_def,bytecodeTheory.bv_to_string_def] >>
  fsrw_tac[ARITH_ss][EL_MAP,bytecodeTheory.bv_to_string_def] >>
  fs[bytecodeExtraTheory.bvs_to_chars_thm,clos_to_chars_thm] >>
  rw[bytecodeExtraTheory.is_Char_def,stringTheory.IMPLODE_EXPLODE_I,EVERY_MEM] >>
  rpt AP_TERM_TAC >>
  fs[LIST_REL_EL_EQN] >>
  simp[LIST_EQ_REWRITE,EL_MAP] >> rw[] >>
  rpt AP_TERM_TAC >>
  rfs[PULL_EXISTS,MEM_EL] >> res_tac >>
  fs[bytecodeExtraTheory.is_Char_def] >- (
    Cases_on`EL x ys`>>fs[bytecodeExtraTheory.is_Char_def] >>
    rfs[val_rel_SIMP] >>
    intLib.COOPER_TAC ) >>
  rw[] >>
  Cases_on`EL n ys`>> rfs[val_rel_SIMP] >>
  TRY intLib.COOPER_TAC >>
  Cases_on`EL n xs`>>fs[val_rel_SIMP]>>fs[EL_MAP]>>
  fs[val_rel_cases])
  *)

val cEvalOp_correct = prove(
  ``(cEvalOp op xs s1 = SOME (v,s2)) /\
    state_rel f s1 t1 /\
    LIST_REL (val_rel f t1.refs t1.code) xs ys /\
    (op <> RefArray) /\
    (op <> RefByte) /\ (op <> UpdateByte) /\
    (op <> Ref) /\ (op <> Update) ==>
    ?w t2.
      (bEvalOp (cCompOp op) ys t1 = SOME (w,t2)) /\
      val_rel f t1.refs t1.code v w /\
      state_rel f s2 t2 /\
      (t1.refs = t2.refs) /\ (t1.code = t2.code)``,
  Cases_on`op`>>rw[cEvalOp_def,bEvalOp_def]
  >- (
    imp_res_tac state_rel_globals >>
    fs[LIST_REL_EL_EQN] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[get_global_def,closLangTheory.get_global_def]>>
    first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))>> rw[] >>
    rfs[opt_val_rel_elim,optionTheory.OPTREL_def] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[]>> rw[val_rel_SIMP] >>
    fs[state_rel_def,opt_val_rel_def] )
  >- (
    imp_res_tac state_rel_globals >>
    fs[LIST_REL_EL_EQN] >>
    BasicProvers.EVERY_CASE_TAC >> rfs[get_global_def,closLangTheory.get_global_def]>>
    rw[val_rel_SIMP] >>
    first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))>> rw[] >>
    rfs[opt_val_rel_def] >>
    fs[state_rel_def] >>
    MATCH_MP_TAC EVERY2_LUPDATE_same >>
    rfs[opt_val_rel_def] )
  >- ( simp[val_rel_cases] )
  >- fs[]
  >- (
    BasicProvers.EVERY_CASE_TAC >>
    fs[val_rel_SIMP] >> rw[] >>
    TRY(fs[val_rel_cases]>>NO_TAC) >>
    fs[Q.SPECL[`f`,`refs`,`code`,`Block a b`,`Block c d`]val_rel_cases,LIST_REL_EL_EQN] >>
    rfs[] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    TRY(fs[val_rel_cases]>>NO_TAC) >>
    rw[val_rel_SIMP] >>
    fs[Q.SPECL[`f`,`refs`,`code`,`Block a b`,`Block c d`]val_rel_cases,LIST_REL_EL_EQN] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[val_rel_SIMP]>>rw[]>>
    TRY(fs[val_rel_cases]>>NO_TAC)>>
    fs[Q.SPECL[`f`,`refs`,`code`,`Block a b`,`Block c d`]val_rel_cases] >>
    fs[LIST_REL_EL_EQN] >> rfs[add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[val_rel_SIMP]>>rw[]>>
    TRY(fs[val_rel_cases]>>NO_TAC)>>
    simp[val_rel_SIMP] >>
    fs[Q.SPECL[`f`,`refs`,`code`,`Block a b`,`Block c d`]val_rel_cases] >>
    fs[LIST_REL_EL_EQN] >> rfs[add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    rfs[state_rel_def] >> res_tac >> fs[ref_rel_cases] >>
    rw[] >> fs[] >> fs[LIST_REL_EL_EQN, add_args_def] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    rfs[state_rel_def] >> res_tac >> fs[ref_rel_cases] )
  >- (
    BasicProvers.EVERY_CASE_TAC >>
    fs[LET_THM] >>
    fs [val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    rfs[state_rel_def] >> res_tac >>
    fs[ref_rel_cases] )
  >- cheat (* FromList *)
  >- cheat (* ToList *)
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rw[val_rel_SIMP] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    TRY(fs[val_rel_cases]>>NO_TAC) >>
    fs[Q.SPECL[`f`,`refs`,`code`,`Block a b`,`Block c d`]val_rel_cases, add_args_def] >>
    rw[]>>fsrw_tac[ARITH_ss][bool_to_val_def] >>
    TRY(fs[val_rel_cases]>>NO_TAC) >>
    Cases_on`n=n''`>> rw[bool_to_val_def,val_rel_cases] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    TRY(fs[val_rel_cases]>>NO_TAC) >>
    fs[Q.SPECL[`f`,`refs`,`code`,`Block a b`,`Block c d`]val_rel_cases, add_args_def] >>
    rw[]>>fsrw_tac[ARITH_ss][bool_to_val_def] >>
    TRY(fs[val_rel_cases]>>NO_TAC) >>
    Cases_on`n=n''`>> rw[bool_to_val_def,val_rel_cases] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[bool_to_val_def,val_rel_SIMP] >>
    rw[val_rel_SIMP] >> fs[val_rel_cases, add_args_def] )
  >- (
      cheat (* TODO : equal, has to do with the tag incrementing *)
      (*
    `INJ ($' f) (FDOM f) (FRANGE f)` by fs[state_rel_def] >>
    Cases_on`xs`>>fs[]>>rw[]>>
    Cases_on`t`>>fs[]>>rw[]>>
    Cases_on`t'`>>fs[]>>rw[]>>
    imp_res_tac (Q.SPECL[`t1.code`,`t1.refs`](Q.GENL[`r`,`c`]bc_equal_clos_equal)) >>
    ntac 2 (pop_assum kall_tac) >> fs[] >>
    BasicProvers.CASE_TAC >> fs[]>>rw[val_rel_SIMP] >>
    Cases_on`b`>>simp[bool_to_val_def]>>
    simp[val_rel_cases] *))
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >>
    fs[val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    rfs[state_rel_def] >> res_tac >> fs[ref_rel_cases] >>
    rw[] >> fs[] >> fs[LIST_REL_EL_EQN] >>
    rw[] >> fs[add_args_def] >>
    first_x_assum match_mp_tac >>
    intLib.COOPER_TAC)
  >- (
    cheat (* TODO : to string. has to do with the tag incrementing *)
    (*
    BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
    imp_res_tac bv_to_string_clos_to_string >> fs[] >>
    fs[state_rel_def] *))
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[val_rel_SIMP] >>
    fs[state_rel_def] )
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >> fs[val_rel_SIMP, add_args_def] >>
    rw[val_rel_SIMP] >> fs [add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >> fs[val_rel_SIMP, add_args_def] >>
    rw[val_rel_SIMP] >> fs [add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >> fs[val_rel_SIMP, add_args_def] >>
    rw[val_rel_SIMP] >> fs [add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >> fs[val_rel_SIMP, add_args_def] >>
    rw[val_rel_SIMP] >> fs [add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >> fs[val_rel_SIMP, add_args_def] >>
    rw[val_rel_SIMP] >> fs [add_args_def])
  >- (
    BasicProvers.EVERY_CASE_TAC >> fs [] >> fs[val_rel_SIMP] >>
    rw[val_rel_SIMP] >>
    Cases_on`i < i'`>> rw[bool_to_val_def,val_rel_cases] >>
    fs [add_args_def] ));

val bEval_rev_var = Q.prove (
`!vs env s ys s'. 
  bEval (MAP Var vs, env, s) = (Result ys, s')
  ⇒
  bEval (REVERSE (MAP Var vs), env, s) = (Result (REVERSE ys), s')`,
 Induct_on `vs` >>
 rw [bEval_def] >>
 rw [bEval_APPEND] >>
 fs [Once bEval_CONS, bEval_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 rw [] >>
 res_tac >>
 fs []);

val bEval_app_helper = Q.prove (
`(!x. r ≠ Result x) ∧ bEval (c8,env,s) = (r,s')
  ⇒
  bEval ([case loc of
            NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
          | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs)) (c8++[c7])],env,s) = (r, s')`,
 rw [] >>
 Cases_on `loc` >>
 rw [bEval_def, bEval_APPEND] >>
 Cases_on `r` >>
 rw []);

val bEval_app_helper2 = Q.prove (
`(!x. r ≠ Result x) ∧ bEval (c8,env,s) = (Result x, s') ∧ bEval ([c7],env,s') = (r,s'')
  ⇒
  bEval ([case loc of
            NONE => Let (c8++[c7]) (mk_cl_call (Var (LENGTH c8)) (GENLIST Var (LENGTH c8)))
          | SOME loc => Call (LENGTH c8 - 1) (SOME (loc + num_stubs)) (c8++[c7])],env,s) = (r, s'')`,
 rw [] >>
 Cases_on `loc` >>
 rw [bEval_def, bEval_APPEND] >>
 Cases_on `r` >>
 rw []);

val bEval_simple_genlist_vars = Q.prove (
`!env1 env2 s.
  0 < LENGTH env1
  ⇒
  bEval (GENLIST Var (LENGTH env1), env1++env2, s) = (Result env1, s)`,
 rw [] >>
 assume_tac (Q.SPECL [`0`, `env1++env2`, `LENGTH (env1:bc_value list)`, `s`] bEval_genlist_vars) >>
 rfs [] >>
 rpt (pop_assum mp_tac) >>
 srw_tac [ARITH_ss] [TAKE_LENGTH_APPEND] >>
 metis_tac []);

val num_remaining_args_def = Define `
(num_remaining_args (Closure loc_opt args env num_args exp : clos_val) = 
  SOME (num_args - LENGTH args)) ∧
(num_remaining_args (Recclosure loc_opt args env funs i : clos_val) = 
  SOME (FST (EL i funs) - LENGTH args)) ∧
(num_remaining_args _ = NONE)`;

val dest_closure_part_app = Q.prove (
`!loc_opt func args c f1 t1.
  LENGTH args ≠ 0 ∧
  dest_closure loc_opt func args = SOME (Partial_app c)
  ⇒
  loc_opt = NONE ∧
  SOME c = add_args func args ∧
  ?n. num_remaining_args func = SOME n ∧ LENGTH args < n ∧ LENGTH args ≤ max_app`,
 rw [dest_closure_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [add_args_def, LET_THM, num_remaining_args_def] >>
 TRY (Cases_on `EL n l1`) >>
 fs [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 Cases_on `loc_opt` >>
 fs [check_loc_def] >>
 decide_tac);

val val_rel_num_rem_args = Q.prove (
`!f refs code v1 v2 n.
  val_rel f refs code v1 v2 ∧
  num_remaining_args v1 = SOME n
  ⇒
  ?tag ptr rest exp. 
    v2 = Block tag (CodePtr ptr::Number (&n-1)::rest) ∧
    n ≠ 0 ∧
    lookup ptr code = SOME (n+1, exp)`,
 rw [val_rel_cases] >>
 fs [num_remaining_args_def]
 >- (fs [cl_rel_cases] >>
     rw [] >>
     fs [num_remaining_args_def, int_arithTheory.INT_NUM_SUB])
 >- (fs [cl_rel_cases] >>
     rw [] >>
     fs [get_num_args_def, add_args_def] >>
     rw [] >>
     fs [num_remaining_args_def, int_arithTheory.INT_NUM_SUB] >>
     ARITH_TAC));

val unpack_closure_thm = Q.prove (
`val_rel f1 t1.refs t1.code func (Block tag (ptr::Number (&n-1)::rest)) ∧
 num_remaining_args func = SOME n
 ⇒
 ?prev_args total_args clo. 
   unpack_closure (Block tag (ptr::Number (&n-1)::rest)) (prev_args, total_args, clo) ∧
   total_args < max_app ∧
   n = total_args − LENGTH prev_args + 1  ∧
   (tag = closure_tag ⇒ prev_args = [] ∧ clo = Block tag (ptr::Number (&n-1)::rest))`,
 rw [unpack_closure_cases, val_rel_cases, cl_rel_cases, num_remaining_args_def] >>
 fs [num_remaining_args_def] >>
 rw_tac bool_ss [] >>
 TRY ARITH_TAC >>
 srw_tac [boolSimps.DNF_ss] [bytecodeTheory.partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [add_args_def, get_num_args_def] >>
 TRY ARITH_TAC >>
 srw_tac [boolSimps.DNF_ss] [bytecodeTheory.partial_app_tag_def, int_arithTheory.INT_NUM_SUB] >>
 TRY decide_tac >>
 Cases_on `ys` >>
 fs [ADD1, num_remaining_args_def] >>
 srw_tac [ARITH_ss] [integerTheory.int_ge, integerTheory.INT_LE_SUB_LADD, integerTheory.INT_LE_LT1]);

val cl_rel_get_num_args = Q.prove (
`cl_rel f1 refs code (env,ys) func (Block tag (p::Number (&(total_args) - 1)::ys))
 ⇒
 get_num_args func = SOME total_args`,
 rw [cl_rel_cases] >>
 fs [get_num_args_def, int_arithTheory.INT_NUM_SUB] >>
 ARITH_TAC);

val get_loc_def = Define `
  (get_loc (Closure loc args env num_args exp) = SOME loc) ∧
  (get_loc (Recclosure loc args env fns i) = SOME (loc + i)) ∧
  (get_loc _ = NONE)`;

val cl_rel_get_loc = Q.prove (
`cl_rel f1 refs code (env,ys) func (Block tag (CodePtr p::n::ys))
 ⇒
 num_stubs ≤ p ∧
 get_loc func = SOME (p-num_stubs)`,
 rw [cl_rel_cases] >>
 rw [get_loc_def]);

val get_old_args_def = Define `
  (get_old_args (Closure loc args env num_args exp) = SOME args) ∧
  (get_old_args (Recclosure loc args env fns i) = SOME args) ∧
  (get_old_args _ = NONE)`;

val get_cl_env_def = Define `
  (get_cl_env (Closure loc args env num_args exp) = SOME env) ∧
  (get_cl_env (Recclosure loc args env fns i) = SOME env) ∧
  (get_cl_env _ = NONE)`;

val dest_closure_full_app = Q.prove (
`!loc_opt func args c f1 t1 exp args1 args2.
  dest_closure loc_opt func args = SOME (Full_app exp args1 args2)
  ⇒
  ?rem_args loc num_args old_args cl_env.
    get_loc func = SOME loc ∧
    num_remaining_args func = SOME rem_args ∧
    get_num_args func = SOME num_args ∧
    get_old_args func = SOME old_args ∧
    get_cl_env func = SOME cl_env ∧
    rem_args ≤ LENGTH args ∧
    rem_args ≤ num_args ∧
    LENGTH args2 = LENGTH args - rem_args ∧
    check_loc loc_opt loc num_args (LENGTH args) (num_args - rem_args)`,
 rw [dest_closure_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 TRY (Cases_on `EL n l1`) >>
 fs [LET_THM] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [get_cl_env_def, get_old_args_def, get_loc_def, num_remaining_args_def, get_num_args_def] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw [] >>
 decide_tac);

 (*
val cl_rel_loc = Q.prove (

val val_rel_loc = Q.prove (
`
 val_rel f refs code func func' ∧
 get_num_args func = SOME num_args ∧
 num_remaining_args func = SOME rem_args ∧
 get_loc func = SOME loc
 ⇒
 ?exp tag xs loc'. 
   lookup loc' code = SOME (args' + 1, exp) ∧
   func' = Block tag (CodePtr loc'::Number (&(args-1))::xs)`,
 rw [val_rel_cases] >>
 fs [num_remaining_args_def, get_num_args_def]
 *)

val add_args_append = Q.prove (
`add_args cl arg_env = SOME func
 ⇒
 add_args cl (args ++ arg_env) = add_args func args`,
 Cases_on `cl` >>
 rw [add_args_def] >>
 rw [add_args_def]);

val no_partial_args = Q.prove (
`num_remaining_args func = SOME x ∧
 get_num_args func = SOME x ∧
 x ≠ 0 ∧
 add_args cl arg_env = SOME func
 ⇒
 arg_env = []`,
 Cases_on `cl` >>
 rw [add_args_def] >>
 fs [get_num_args_def, num_remaining_args_def] >>
 rw [] >>
 Cases_on `arg_env` >>
 fs [] >>
 decide_tac);

val cl_rel_run_lemma = Q.prove (
`LENGTH env1 ≠ 0 ⇒ 
 bEval (GENLIST Var (LENGTH env1 + 1),env1++[x],s) = (Result (env1++[x]),s)`,
 strip_tac >>
 `0 < LENGTH env1 + 1` by decide_tac >>
 `LENGTH env1 + 1 = LENGTH (env1++[x])` by rw [] >>
 metis_tac [bEval_simple_genlist_vars, APPEND_NIL]);

val cl_rel_run = Q.prove (
`!f1 (refs : num|-> ref_value) code args args' env env' ptr body new_env func func' t1 rest.
  func' = Block 5 (CodePtr ptr::Number (&LENGTH args' − 1)::env') ∧
  (dest_closure (SOME (ptr − num_stubs)) func args = SOME (Full_app body new_env rest) ∨ 
   dest_closure NONE func args = SOME (Full_app body new_env rest)) ∧ 
  val_rel f1 refs code func func' ∧
  cl_rel f1 refs code (env,env') func func' ∧
  LIST_REL (val_rel f1 refs code) args args'
  ⇒
  ∃body' aux1 aux2 new_env' exp'.
    lookup ptr code = SOME (LENGTH args' + 1,exp') ∧
    cComp [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
    env_rel f1 refs code new_env new_env' ∧
    bEval ([exp'], args'++[func'], t1) = bEval ([body'], new_env', t1)`,
 rw [cl_rel_cases, dest_closure_def] >>
 `LIST_REL (val_rel f1 refs code) env env'`
         by fs [val_rel_cases, cl_rel_cases, bytecodeTheory.partial_app_tag_def] >>
 fs [int_arithTheory.INT_NUM_SUB] >>
 rfs [] >>
 `num_args = LENGTH args'` by ARITH_TAC >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [check_loc_def, LET_THM] >>
 rw [] >>
 qexists_tac `c` >>
 qexists_tac `aux` >>
 qexists_tac `aux1` >>
 imp_res_tac EVERY2_LENGTH >>
 fs [] >>
 rw [bEval_def, bEval_APPEND] >>
 qabbrev_tac `func' = Block 5 (CodePtr (p + num_stubs)::Number (&LENGTH args' − 1):: env')` >>
 `0 < LENGTH (args'++[func'])` by (rw [] >> decide_tac) >>
 simp [bEval_simple_genlist_vars, cl_rel_run_lemma] >>
 `bEval ([Var (LENGTH args)], args'++[func'],t1) = (Result [func'],t1)`
         by rw [bEval_def, EL_LENGTH_APPEND] >>
 unabbrev_all_tac >>
 imp_res_tac bEval_free_let_Block >>
 rfs [] >>
 qabbrev_tac `func' = Block 5 (CodePtr (p + num_stubs)::Number (&LENGTH args' − 1):: env')` >>
 simp [TAKE_REVERSE] >>
 metis_tac [list_rel_IMP_env_rel, APPEND_ASSOC, LASTN_LENGTH_ID, env_rel_APPEND, LIST_REL_def]);

val val_rel_run = Q.prove (
`!f1 (refs : num|-> ref_value) code args args' env' ptr body new_env func func' t1 rest tag.
  func' = Block tag (CodePtr ptr::Number (&LENGTH args' − 1)::env') ∧
  dest_closure NONE func args = SOME (Full_app body new_env rest) ∧ 
  val_rel f1 refs code func func' ∧
  LIST_REL (val_rel f1 refs code) args args'
  ⇒
  ∃body' aux1 aux2 new_env' exp'.
    lookup ptr code = SOME (LENGTH args' + 1,exp') ∧
    cComp [body] aux1 = ([body'],aux2) ∧ code_installed aux2 code ∧
    env_rel f1 refs code new_env new_env' ∧
    bEval ([exp'], args'++[func'], t1) = bEval ([body'], new_env', t1)`,
 rw [] >>
 qpat_assum `val_rel x0 x1 x2 x3 x4` (fn x => mp_tac x >> simp [val_rel_cases] >> assume_tac x) >>
 rw [] >>
 imp_res_tac EVERY2_LENGTH >>
 imp_res_tac cl_rel_get_loc
 >- metis_tac [cl_rel_run] >>
 (* TODO: case for a partial application *)
 cheat);

val arith_helper_lem = Q.prove (
`LENGTH args' ≠ 0 ⇒ x − 1 − (LENGTH args' − 1) = x − LENGTH args'`,
decide_tac);

val arith_helper_lem2 = Q.prove (
`&(total_args + 1) − &LENGTH prev_args − 1 = &num_args − 1 − &LENGTH prev_args
 ⇒ 
 num_args = total_args + 1`,
 ARITH_TAC);

val arith_helper_lem3 = Q.prove (
`LENGTH args' ≠ 0
 ⇒
 total_args − (LENGTH args' + LENGTH prev_args − 1) =
 total_args + 1 − (LENGTH args' + LENGTH prev_args)`,
 ARITH_TAC);

val cComp_correct = store_thm("cComp_correct",
  ``(!tmp xs env s1 aux1 t1 env' f1 res s2 ys aux2.
      (tmp = (xs,env,s1)) ∧
      (cEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (cComp xs aux1 = (ys,aux2)) /\
      code_installed aux2 t1.code /\
      env_rel f1 t1.refs t1.code env env' /\
      state_rel f1 s1 t1 ==>
      ?res' t2 f2.
         (bEval (ys,env',t1) = (res',t2)) /\
         res_rel f2 t2.refs t2.code res res' /\
         state_rel f2 s2 t2 /\
         f1 SUBMAP f2 /\
         (FDIFF t1.refs f1) SUBMAP (FDIFF t2.refs f2)) ∧
    (!loc_opt func args s1 res s2 env t1 args' func' f1.
      cEvalApp loc_opt func args s1 = (res,s2) ∧
      res ≠ Error ∧
      val_rel f1 t1.refs t1.code func func' ∧
      LIST_REL (val_rel f1 t1.refs t1.code) args args' ∧
      state_rel f1 s1 t1
      ⇒ 
      ?res' t2 f2.
        (LENGTH args' ≠ 0 ⇒
          case loc_opt of
           | NONE =>
               bEval ([mk_cl_call (Var (LENGTH args')) (GENLIST Var (LENGTH args'))], 
                       args' ++ [func'] ++ env,
                       t1) = 
                 (res',t2)
            | SOME loc => 
                (case find_code (SOME (loc + num_stubs)) (args' ++ [func']) t1.code of
                      NONE => (Error,t2)
                    | SOME (args,exp) =>
                        if t1.clock < (LENGTH args') then (TimeOut,t1 with clock := 0)
                        else bEval ([exp],args,dec_clock (LENGTH args') t1)) = 
                  (res',t2)) ∧
        res_rel f2 t2.refs t2.code res res' ∧
        state_rel f2 s2 t2 ∧ 
        f1 ⊑ f2 ∧ 
        FDIFF t1.refs f1 ⊑ FDIFF t2.refs f2)``,

  ho_match_mp_tac cEval_ind \\ REPEAT STRIP_TAC
  THEN1 (* NIL *)
   (rw [] >> fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ Q.EXISTS_TAC `f1` \\ fs [res_rel_Result] \\ metis_tac [] )
  THEN1 (* CONS *)
   (rw [] >>
    fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval ([x],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?q. cEval (y::xs,env,p1) = q` by fs [] \\ PairCases_on `q` \\ fs []
    \\ `?cc. cComp [x] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ `?dd. cComp (y::xs) cc1 = dd` by fs [] \\ PairCases_on `dd` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ Q.PAT_ASSUM `!xx yy zz. bbb ==> b` (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC cComp_SING \\ fs [] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [bEval_CONS]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`cc1`]) \\ fs []
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ `q0 <> Error` by (Cases_on `q0` \\ fs []) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ fs []
    \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [] \\ REPEAT STRIP_TAC
    \\ fs [] \\ IMP_RES_TAC bEval_SING \\ fs []
    \\ Cases_on `q0` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_cases] \\ Q.EXISTS_TAC `f2'`
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ IMP_RES_TAC val_rel_SUBMAP \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs []
    \\ Q.PAT_ASSUM `LIST_REL ppp yy tt` MP_TAC
    \\ MATCH_MP_TAC listTheory.LIST_REL_mono
    \\ METIS_TAC [val_rel_SUBMAP])
  THEN1 (* Var *)
   (rw [] >>
    Cases_on `n < LENGTH env` \\ fs [cComp_def,cEval_def]
    \\ IMP_RES_TAC env_rel_IMP_LENGTH
    \\ `n < LENGTH env''` by DECIDE_TAC
    \\ SRW_TAC [] [bEval_def,res_rel_cases]
    \\ Q.EXISTS_TAC `f1` \\ fs [SUBMAP_REFL]
    \\ MATCH_MP_TAC env_rel_IMP_EL \\ fs [])
  THEN1 (* If *)
   (rw [] >>
    fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp [x1] aux1 = ([c3],aux3)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ `?c4 aux4. cComp [x2] aux3 = ([c4],aux4)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ `?c5 aux5. cComp [x3] aux4 = ([c5],aux5)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval ([x1],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ IMP_RES_TAC cEval_SING \\ SRW_TAC [] []
    \\ fs [res_rel_Result1]
    \\ Cases_on `Block 1 [] = r1` \\ fs [] THEN1
     (`Block 1 [] = y` by (SRW_TAC [] [] \\ fs [val_rel_SIMP] >> rw [] >> fs [add_args_def] \\ NO_TAC)
      \\ fs [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
      \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ fs []
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs []
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.EXISTS_TAC `f2'` \\ fs []
      \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
    \\ Cases_on `Block 0 [] = r1` \\ fs [] THEN1
     (`Block 0 [] = y` by (SRW_TAC [] [] \\ fs [val_rel_SIMP] >> rw [] >> fs [add_args_def] \\ NO_TAC)
      \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux4`]) \\ fs []
      \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`env''`,`f2`]) \\ fs []
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs []
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.EXISTS_TAC `f2'` \\ fs []
      \\ IMP_RES_TAC SUBMAP_TRANS \\ fs []))
  THEN1 (* Let *)
   (rw [] >>
    fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ `?c4 aux4. cComp [x2] aux3 = ([c4],aux4)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval (xs,env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`ys ++ env''`,`f2`]) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (MATCH_MP_TAC env_rel_APPEND \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1 (* Raise *)
   (rw [] >>
    fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval ([x1],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. cComp [x1] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ IMP_RES_TAC cComp_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC cComp_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [bEval_def]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cEval_SING \\ fs []
    \\ IMP_RES_TAC bEval_SING \\ fs [] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_cases])
  THEN1 (* Handle *)
   (rw [] >>
    fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp [x1] aux1 = ([c3],aux3)` by METIS_TAC [PAIR,cComp_SING]
    \\ `?c4 aux4. cComp [x2] aux3 = ([c4],aux4)` by METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval ([x1],env,s1) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Ex] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`y'::env''`,`f2`]) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (fs [env_rel_def] \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1 (* Op *)
   (rw [] >>
    fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval (xs,env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. cComp xs aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ IMP_RES_TAC cComp_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env''`,`f1`])
    \\ IMP_RES_TAC cComp_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [bEval_def]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ Cases_on `cEvalOp op (REVERSE a) p1` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `op = Ref` \\ fs []
    THEN1
     (fs [cEvalOp_def,LET_DEF] \\ SRW_TAC [] [res_rel_Result1]
      \\ fs [PULL_EXISTS]
      \\ Q.ABBREV_TAC `pp = LEAST ptr. ptr NOTIN FDOM p1.refs`
      \\ Q.ABBREV_TAC `qq = LEAST ptr. ptr NOTIN FDOM t2.refs`
      \\ fs [bEvalOp_def,LET_DEF]
      \\ Q.EXISTS_TAC `f2 |+ (pp,qq)` \\ fs []
      \\ `~(pp IN FDOM p1.refs)` by
           (UNABBREV_ALL_TAC \\ fs [LEAST_NO_IN_FDOM] \\ NO_TAC)
      \\ `~(qq IN FDOM t2.refs)` by
           (UNABBREV_ALL_TAC \\ fs [LEAST_NO_IN_FDOM] \\ NO_TAC)
      \\ `~(pp IN FDOM f2)` by fs [state_rel_def]
      \\ `~(qq IN FRANGE f2)` by
        (REPEAT STRIP_TAC \\ fs [state_rel_def,SUBSET_DEF] \\ RES_TAC \\ NO_TAC)
      \\ `FRANGE (f2 \\ pp) = FRANGE f2` by ALL_TAC THEN1
       (fs [FRANGE_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,EXTENSION]
        \\ METIS_TAC []) \\ fs []
      \\ REPEAT STRIP_TAC
      THEN1 (fs [val_rel_cases,FLOOKUP_FAPPLY])
      THEN1
       (fs [state_rel_def,FLOOKUP_FAPPLY]
        \\ REPEAT STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp qqq rrr` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC opt_val_rel_NEW_REF \\ fs []
          \\ MATCH_MP_TAC opt_val_rel_NEW_F \\ fs [])
        THEN1
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM f2) (FRANGE f2)` MP_TAC
          \\ REPEAT (Q.PAT_ASSUM `INJ xx yy zz` (K ALL_TAC))
          \\ fs [INJ_DEF,FAPPLY_FUPDATE_THM,FRANGE_DEF]
          \\ REPEAT STRIP_TAC \\ METIS_TAC [])
        \\ Cases_on `n = pp` \\ fs [] THEN1
         (SRW_TAC [] [ref_rel_cases] >>
          imp_res_tac EVERY2_REVERSE
          \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) (REVERSE a) (REVERSE ys)` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC val_rel_NEW_REF \\ fs []
          \\ MATCH_MP_TAC val_rel_NEW_F \\ fs [])
        \\ RES_TAC \\ fs []
        \\ `qq <> m` by (REPEAT STRIP_TAC \\ fs [FLOOKUP_DEF] \\ SRW_TAC [] [])
        \\ fs [ref_rel_cases]
        \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) xs' ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC val_rel_NEW_REF \\ fs []
        \\ MATCH_MP_TAC val_rel_NEW_F \\ fs [])
      THEN1
       (fs [SUBMAP_DEF,FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ METIS_TAC [])
      \\ MATCH_MP_TAC SUBMAP_TRANS
      \\ Q.EXISTS_TAC `FDIFF t2.refs f2` \\ fs []
      \\ fs [SUBMAP_DEF,FDOM_FDIFF]
      \\ REPEAT STRIP_TAC
      \\ fs [FDIFF_def,DRESTRICT_DEF]
      \\ SRW_TAC [] [] \\ fs [state_rel_def,SUBSET_DEF])
    \\ Cases_on `op = Update` \\ fs [] THEN1
     (fs [cEvalOp_def,bEvalOp_def]
      \\ Cases_on `REVERSE a` \\ fs []
      \\ Cases_on `t` \\ fs []
      \\ Cases_on `t'` \\ fs []
      \\ Cases_on `t` \\ fs []
      \\ Cases_on `h` \\ fs []
      \\ Cases_on `h'` \\ fs []
      \\ Cases_on `FLOOKUP p1.refs n` \\ fs []
      \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
      \\ imp_res_tac EVERY2_REVERSE >>
      rfs [] >>
      rw []
      \\ fs [val_rel_SIMP] \\ SRW_TAC [] []
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel f2 t2.refs t2.code (ValueArray l) y` by
              METIS_TAC [state_rel_def]
      \\ fs [] \\ SRW_TAC [] []
      \\ fs [ref_rel_cases] \\ SRW_TAC [] []
      \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_cases] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
      THEN1
       (MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
        \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      THEN1
       (fs [state_rel_def,FLOOKUP_FAPPLY] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_ASSUM `LIST_REL tt yy t2.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC opt_val_rel_UPDATE_REF \\ fs []
          \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (fs [EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ fs [SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = n` \\ fs [] \\ SRW_TAC [] []
        THEN1
         (fs [ref_rel_cases]
          \\ MATCH_MP_TAC EVERY2_LUPDATE
          \\ REPEAT STRIP_TAC THEN1
           (MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
            \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) l ys'` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
          \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        \\ RES_TAC \\ fs []
        \\ `m' <> m''` by
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ fs [FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ fs [] \\ SRW_TAC [] [] \\ fs [ref_rel_cases] \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `LIST_REL pp xs' ys''` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
        \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ fs [SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM, add_args_def])
    \\ Cases_on `op = RefArray` \\ fs[] THEN1 cheat
    \\ Cases_on `op = RefByte` \\ fs[] THEN1 cheat
    \\ Cases_on `op = UpdateByte` \\ fs[] THEN1 cheat
    \\ first_x_assum(mp_tac o MATCH_MP (GEN_ALL(REWRITE_RULE[GSYM AND_IMP_INTRO]cEvalOp_correct)))
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th))
    \\ imp_res_tac EVERY2_REVERSE 
    \\ first_x_assum(fn th => disch_then (mp_tac o C MATCH_MP th)) \\ rw[] \\ rw[]
    \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_Result])
  THEN1 (* Fn *)
   (rw [] >>
    fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [cComp_def]
    \\ `?c2 aux3. cComp [exp] aux1 = (c2,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ fs [code_installed_def]
    \\ fs [bEval_def,bEval_APPEND,bEvalOp_def,domain_lookup]
    \\ `s.restrict_envs` by fs [state_rel_def]
    \\ fs [clos_env_def]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `t1`)
    \\ Cases_on `num_args ≤ max_app ∧ num_args ≠ 0` 
    \\ fs []
    \\ rw []
    \\ fs [res_rel_cases,val_rel_cases, cl_rel_cases]
    \\ imp_res_tac bEval_rev_var >>
    rw [] >>
    Q.EXISTS_TAC `f1` \\ fs [] >>
    disj1_tac >>
    Q.EXISTS_TAC `x` \\ fs [] >>
    Q.LIST_EXISTS_TAC [`aux1`,`aux3`] \\ fs []
    \\ IMP_RES_TAC cComp_SING \\ fs [code_installed_def])
  THEN1 (* Letrec *)
   (rw [] >>
    fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [cComp_def]
    \\ `s.restrict_envs` by fs [state_rel_def]
    \\ fs [build_recc_def,clos_env_def]
    \\ Cases_on `lookup_vars names env` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `fns` \\ fs []
    THEN1 (rfs [] \\ FIRST_X_ASSUM MATCH_MP_TAC
           \\ Q.LIST_EXISTS_TAC [`aux1`] \\ fs [])
    \\ Cases_on `t` \\ fs [] \\ rfs []
    THEN1 (* special case for singly-recursive closure *)
     (
     
      `?num_args body. h = (num_args, body)` by metis_tac [pair_CASES] >>
      rw [] >>
      fs [] >>
      `?c2 aux3. cComp [body] aux1 = ([c2],aux3)` by
              METIS_TAC [PAIR,cComp_SING]
      \\ fs[LET_THM]
      \\ first_assum(split_applied_pair_tac o lhs o concl)
      \\ fs [] \\ SRW_TAC [] []
      \\ simp[bEval_def, bEval_APPEND, bEvalOp_def]
      \\ IMP_RES_TAC lookup_vars_IMP
      \\ first_x_assum(qspec_then`t1`STRIP_ASSUME_TAC) >>
      imp_res_tac bEval_var_reverse >>
      simp [REVERSE_APPEND] >>
      Cases_on `num_args ≤ max_app ∧ num_args ≠ 0` >>
      fs [] >>
      fs [] >>
      simp [domain_lookup] >>
      rw []
      \\ fs[code_installed_def]
      \\ qmatch_assum_abbrev_tac`cComp [exp] auxx = zz`
      \\ qspecl_then[`[exp]`,`auxx`]strip_assume_tac cComp_lemma
      \\ rfs[Abbr`zz`,LET_THM] >> fs[Abbr`auxx`]
      \\ simp[REVERSE_APPEND]
      \\ Q.PAT_ABBREV_TAC`env2 = X::env''`
      \\ FIRST_X_ASSUM (fn th => first_assum(qspecl_then[`t1`,`env2`,`f1`]mp_tac o
             MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th)))
      \\ simp[Abbr`env2`,env_rel_def]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs [env_rel_def] \\ fs [val_rel_cases] \\ DISJ1_TAC >>
        fs [cl_rel_cases] >>
        qexists_tac `x'` >>
        rw []
        \\ Q.LIST_EXISTS_TAC [`aux1`,`aux3`] \\ fs []
        \\ IMP_RES_TAC cComp_IMP_code_installed
        \\ fs [GSYM code_installed_def] >>
        simp [GSYM ADD1, GENLIST])
      \\ strip_tac
      \\ imp_res_tac cComp_SING \\ fs[] \\ rw[]
      \\ Q.LIST_EXISTS_TAC [`f2`] \\ fs [])
    (* general case for mutually recursive closures *)
    \\ cheat)
    (*
    \\ `0 < LENGTH (h::h'::t') /\ 1 < LENGTH (h::h'::t')` by (fs [] \\ DECIDE_TAC)
    \\ `SUC (SUC (LENGTH t')) = LENGTH (h::h'::t')` by fs []
    \\ Q.ABBREV_TAC `exps = h::h'::t'` \\ fs []
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC)) \\ fs [LET_DEF]
    \\ `?c7 aux7. cComp exps aux1 = (c7,aux7)` by METIS_TAC [PAIR]
    \\ `?n4 aux5. build_aux loc
           (MAP (code_for_recc_case (LENGTH exps + LENGTH names)) c7)
           aux7 = (n4,aux5)` by METIS_TAC [PAIR]
    \\ `?c8 aux8. cComp [exp] aux5 = (c8,aux8)` by METIS_TAC [PAIR]
    \\ fs [] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux5`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ fs [build_recc_lets_def]
    \\ fs [bEvalOp_def,bEval_def,LET_DEF]
    \\ fs [bEval_APPEND,bEval_MAP_Const]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (MP_TAC o Q.SPEC `t1`) \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.ABBREV_TAC `rr = LEAST ptr. ptr NOTIN FDOM t1.refs`
    \\ fs [recc_Let0_def]
    \\ `loc + (LENGTH exps - 1) IN domain t1.code` by
     (IMP_RES_TAC cComp_IMP_code_installed
      \\ IMP_RES_TAC cComp_LENGTH
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ fs [domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ fs []
      \\ `LENGTH c7 - 1 < LENGTH c7` by DECIDE_TAC
      \\ RES_TAC
      \\ fs [code_installed_def,EVERY_MEM] \\ fs []
      \\ RES_TAC \\ fs [])
    \\ fs [bEval_def,bEvalOp_def,DECIDE ``1 < m + 1 + SUC n``,
           DECIDE ``0 < 1 + SUC n``, DECIDE ``1 < n + (1 + SUC m)``,
           DECIDE ``m < 1 + (m + n):num``]
    \\ `0 < LENGTH exps + LENGTH ys` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [FLOOKUP_DEF, DECIDE ``n < 1 + (n + m):num``]
    \\ `exps <> []` by (fs [GSYM LENGTH_NIL] \\ DECIDE_TAC)
    \\ `?ll x. exps = SNOC x ll` by METIS_TAC [SNOC_CASES] \\ fs []
    \\ `LENGTH ll = LENGTH ((MAP (K (Number 0)) ll) : bc_value list)`
         by fs [LENGTH_MAP]
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC,LUPDATE_LENGTH]
    \\ `EVERY (\n. loc + n IN domain t1.code) (GENLIST I (LENGTH ll))` by
     (fs [EVERY_GENLIST]
      \\ IMP_RES_TAC cComp_IMP_code_installed
      \\ IMP_RES_TAC cComp_LENGTH
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ fs [domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ fs []
      \\ REPEAT STRIP_TAC
      \\ `i < LENGTH c7` by ALL_TAC THEN1
       (`LENGTH ll <= LENGTH c7` by ALL_TAC
        \\ IMP_RES_TAC cComp_LENGTH \\ fs [LENGTH_APPEND]
        \\ DECIDE_TAC)
      \\ RES_TAC
      \\ fs [code_installed_def,EVERY_MEM] \\ fs []
      \\ RES_TAC \\ fs [])
    \\ fs [SIMP_RULE(srw_ss())[]bEval_recc_Lets]
    \\ Q.PAT_ABBREV_TAC `t1_refs  = t1 with refs := t1.refs |+ xxx`
    \\ `[HD c8] = c8` by (IMP_RES_TAC cComp_SING \\ fs []) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1_refs`,
       `GENLIST (\n. Block closure_tag [CodePtr (loc + n); RefPtr rr])
          (LENGTH (ll:clos_exp list) + 1) ++ env'`,`f1`])
    \\ `~(rr IN FDOM t1.refs)` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
      \\ fs [DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs [])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1
     (`t1_refs.code = t1.code` by fs [Abbr`t1_refs`] \\ fs []
      \\ REVERSE (REPEAT STRIP_TAC) THEN1
       (fs [state_rel_def,Abbr`t1_refs`] \\ STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp s.globals t1.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ METIS_TAC [opt_val_rel_NEW_REF])
        \\ STRIP_TAC THEN1 fs [SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs [FLOOKUP_FAPPLY]
        \\ `m <> rr` by (REPEAT STRIP_TAC \\ fs [FLOOKUP_DEF]) \\ fs []
        \\ fs [ref_rel_cases]
        \\ Q.PAT_ASSUM `LIST_REL ppp xs ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ IMP_RES_TAC val_rel_NEW_REF \\ fs [])
      \\ `LENGTH ll + 1 = LENGTH exps` by fs []
      \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th])
      \\ `1 < LENGTH exps` by (fs [] \\ DECIDE_TAC)
      \\ Q.PAT_ASSUM `exps = ll ++ [x]` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
      \\ MATCH_MP_TAC env_rel_APPEND
      \\ REVERSE STRIP_TAC THEN1
       (UNABBREV_ALL_TAC \\ fs []
        \\ MATCH_MP_TAC (env_rel_NEW_REF |> GEN_ALL) \\ fs [])
      \\ MATCH_MP_TAC EVERY2_GENLIST \\ REPEAT STRIP_TAC \\ fs []
      \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ DISJ2_TAC
      \\ Q.EXISTS_TAC `ZIP (exps,GENLIST (\i.loc+i) (LENGTH exps))`
      \\ fs [LENGTH_ZIP]
      \\ Q.LIST_EXISTS_TAC [`rr`,`ys`] \\ fs [Abbr `t1_refs`,FLOOKUP_FAPPLY]
      \\ fs [MAP_FST_ZIP] \\ fs [MAP_GENLIST,o_DEF]
      \\ REPEAT STRIP_TAC
      THEN1 (fs [state_rel_def,SUBSET_DEF] \\ RES_TAC)
      THEN1
       (Q.PAT_ASSUM `LIST_REL (val_rel f1 t1.refs t1.code) x' ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [val_rel_NEW_REF])
      \\ fs [closure_code_installed_def]
      \\ MATCH_MP_TAC EVERY_ZIP_GENLIST \\ fs [AC ADD_ASSOC ADD_COMM]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC cComp_IMP_code_installed
      \\ MATCH_MP_TAC cComp_LIST_IMP_cComp_EL \\ fs [])
    \\ REPEAT STRIP_TAC
    \\ fs [] \\ Q.EXISTS_TAC `f2` \\ IMP_RES_TAC SUBMAP_TRANS
    \\ ASM_SIMP_TAC std_ss []
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ UNABBREV_ALL_TAC
    \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
    \\ fs [DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
         SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs [])*)
  THEN1 (* App *)
   (rw [] >>
    fs [cEval_def, cComp_def]
    \\ `?res6 s6. cEval (args,env,s) = (res6,s6)` by METIS_TAC [PAIR]
    \\ `?res5 s5. cEval ([x1],env,s6) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?c7 aux7. cComp [x1] aux1 = ([c7],aux7)` by
          METIS_TAC [PAIR,cComp_SING]
    \\ `?c8 aux8. cComp args aux7 = (c8,aux8)` by
          METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Cases_on `LENGTH args > 0` >> fs []
    \\ REVERSE (Cases_on `res6`) \\ fs []
    >- (res_tac >>
        fs [res_rel_cases] >>
        imp_res_tac bEval_app_helper >>
        fs [] >>
        metis_tac [])
    >- (res_tac >>
        fs [res_rel_cases] >>
        imp_res_tac bEval_app_helper >>
        fs [] >>
        metis_tac [])
    \\ `code_installed aux1 t1.code` by IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux7`,`t1`,`env''`,`f1`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ `?a'. res' = Result a'` by fs [res_rel_cases]
    \\ `code_installed aux7 t1.code` by IMP_RES_TAC cComp_IMP_code_installed
    \\ `t2.code = t1.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ `code_installed aux7 t2.code` by metis_tac []
    \\ `env_rel f2 t2.refs t2.code env env''` by metis_tac [env_rel_SUBMAP]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t2`,`env''`,`f2`]) \\ fs []
    \\ rw []
    \\ REVERSE (Cases_on `res5`) \\ fs []
    >- (fs [res_rel_cases] >>
        imp_res_tac bEval_app_helper2 >>
        fs [] >>
        rw [] >>
        metis_tac [SUBMAP_TRANS])
    >- (fs [res_rel_cases] >>
        imp_res_tac bEval_app_helper2 >>
        fs [] >>
        rw [] >>
        metis_tac [SUBMAP_TRANS])
    \\ fs [res_rel_Result]
    \\ imp_res_tac cEval_SING
    \\ fs [res_rel_Result1]
    \\ rw []
    \\ imp_res_tac bEval_length_imp
    \\ imp_res_tac cComp_LENGTH
    \\ `t2'.code = t1.code` by metis_tac [bvl_inlineTheory.bEval_code]
    \\ `LIST_REL (val_rel f2' t2'.refs t2'.code) a a'` 
              by metis_tac [LIST_REL_mono, val_rel_SUBMAP]
    \\ res_tac
    \\ pop_assum (qspec_then `env''` assume_tac)
    \\ fs []
    \\ Cases_on `loc_opt`
    \\ `0 < LENGTH a' ∧ LENGTH args = LENGTH a'` by decide_tac 
    \\ simp [bEval_def, bEval_APPEND]
    \\ fs []
    \\ `LENGTH a' ≠ 0` by decide_tac
    >- metis_tac [SUBMAP_TRANS]
    \\ rfs []
    \\ REVERSE (Cases_on `find_code (SOME (x + num_stubs)) (a' ++ [y]) t1.code`)
    \\ fs []
    >- metis_tac [SUBMAP_TRANS]
    \\ rw []
    \\ fs [res_rel_cases])
(*
    \\ Cases_on `res'`
    \\ TRY (Cases_on `loc_opt` \\ fs [res_rel_cases,bEval_def]
            \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC) \\ fs []
    \\ `t2.code = t1.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ `code_installed aux7 t2.code` by fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux7`,`t2`,`env'`,`f2`]) \\ fs []
    \\ `env_rel f2 t2.refs t1.code env env'` by
          (MATCH_MP_TAC env_rel_SUBMAP \\ METIS_TAC []) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `res6`) \\ fs []
    \\ Cases_on `res'`
    \\ TRY (fs [res_rel_cases] \\ SRW_TAC [] []
            \\ Cases_on `loc_opt` \\ fs [res_rel_cases,bEval_def]
            \\ Q.EXISTS_TAC `f2'` \\ IMP_RES_TAC SUBMAP_TRANS
            \\ fs [] \\ NO_TAC) \\ fs []
    \\ `?g1 y1 c1. (a = [g1]) /\ (a'' = [y1])` by METIS_TAC [cEval_SING]
    \\ fs [] \\ Cases_on `dest_closure loc_opt g1 y1` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `x` \\ fs []
    \\ fs [bEval_def]
    \\ fs [res_rel_Result,DECIDE ``1 < SUC (1 + n:num)``]
    \\ `bEval
         ([case loc_opt of
           | NONE =>
               Let [c7; c8] (Call NONE [Var 0; Var 1; Op El [Var 0; Op (Const 0) []]])
           | SOME loc => Call (SOME loc) [c7; c8]],env',t1) =
        bEval ([Call (SOME (closure_ptr g1)) [c7; c8]],env',t1)` by ALL_TAC
    THEN1
     (Cases_on `loc_opt` \\ fs []
      \\ Cases_on `g1` \\ fs [dest_closure_def,closure_ptr_def]
      \\ SRW_TAC [] [] \\ fs [MAP_GENLIST,check_loc_def]
      \\ ONCE_REWRITE_TAC [bEval_def]
      \\ ONCE_REWRITE_TAC [bEval_CONS] \\ fs [MAP_GENLIST]
      \\ fs [val_rel_SIMP]
      \\ fs [bEval_def,bEvalOp_def,DECIDE ``1 < SUC (SUC n)``]
      \\ fs [find_code_def] \\ fs [MAP_GENLIST]
      \\ NTAC 2 BasicProvers.CASE_TAC
      \\ fs [DECIDE ``(3 = n + 1) <=> (2 = n:num)``]
      \\ REPEAT (BasicProvers.CASE_TAC >>rw[]>>fs[]))
    \\ fs [] \\ POP_ASSUM (K ALL_TAC)
    \\ ONCE_REWRITE_TAC [bEval_def]
    \\ ONCE_REWRITE_TAC [bEval_CONS] \\ fs []
    \\ fs [find_code_def]
    \\ Cases_on `g1` \\ fs [dest_closure_def] \\ SRW_TAC [] []
    \\ fs [closure_ptr_def]
    THEN1 (* Closure case *)
     (fs [val_rel_Closure] \\ SRW_TAC [] []
      \\ fs [bEvalOp_def,find_code_def]
      \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6`
      \\ `t6.code = t2.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ `t6.clock = s6.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s6.clock = 0` \\ fs []
      THEN1 (fs [res_rel_cases,bEval_def] \\ SRW_TAC [] []
             \\ Q.EXISTS_TAC `f6` \\ SRW_TAC [] [res_rel_cases]
             \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
      \\ SIMP_TAC std_ss [bEval_def]
      \\ SIMP_TAC std_ss [Once bEval_CONS]
      \\ fs [bEval_def]
      \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [bEval_free_let_Block]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ `(dec_clock t6).refs = t6.refs` by (fs [dec_clock_def]) \\ fs []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
      \\ POP_ASSUM (MP_TAC o Q.SPECL
           [`y'::(ys ++ [Block closure_tag (CodePtr n::ys); y'])`,`f6`])
      \\ MATCH_MP_TAC IMP_IMP \\ REVERSE STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ fs []
        \\ Q.LIST_EXISTS_TAC [`res'`,`t2'`,`f2'`] \\ fs []
        \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [dec_clock_def]
        \\ Cases_on `res'` \\ fs []
        \\ IMP_RES_TAC bEval_SING \\ fs [])
      \\ fs [env_rel_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ fs []
      \\ fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def]
      \\ rfs [] \\ MATCH_MP_TAC env_rel_SUBMAP \\ METIS_TAC [])
    (* Recclosure case *)
    \\ fs [GSYM NOT_LESS]
    \\ Q.MATCH_ASSUM_RENAME_TAC `index < LENGTH exps`
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Q.ABBREV_TAC `cl_env = l` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `LENGTH exps = 0` \\ fs []
    \\ Cases_on `LENGTH exps = 1` \\ fs []
    THEN1 (* special case for singly-recursive closure *)
     (`?exp. exps = [exp]` by (Cases_on `exps` \\ fs [LENGTH_NIL])
      \\ SRW_TAC [] [] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6`
      \\ Q.PAT_ASSUM `val_rel f2 t2.refs t1.code
           (Recclosure n0 cl_env [exp] 0) y` MP_TAC
      \\ REVERSE (ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ SRW_TAC [] [])
      THEN1 (Cases_on `exps_ps` \\ fs [] \\ Cases_on `t` \\ fs [])
      \\ fs [bEvalOp_def,find_code_def]
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ `t6.clock = s6.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s6.clock = 0` \\ fs []
      THEN1 (Q.EXISTS_TAC `f6` \\ IMP_RES_TAC SUBMAP_TRANS
             \\ SRW_TAC [] [res_rel_cases])
      \\ SIMP_TAC std_ss [bEval_def] \\ fs []
      \\ SIMP_TAC std_ss [Once bEval_CONS]
      \\ fs [bEval_def]
      \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [bEval_free_let_Block]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ Q.ABBREV_TAC `bb = Block closure_tag (CodePtr n0::ys)`
      \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`y'::bb::(ys ++ [bb; y'])`,`f6`])
      \\ MATCH_MP_TAC IMP_IMP \\ REVERSE STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ fs []
        \\ Q.LIST_EXISTS_TAC [`res'`,`t2'`,`f2'`] \\ fs []
        \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [dec_clock_def]
        \\ BasicProvers.CASE_TAC \\ fs []
        \\ IMP_RES_TAC bEval_SING \\ fs [])
      \\ fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def]
      \\ `y'::bb::(ys ++ [bb; y']) = y'::bb::ys ++ [bb; y']` by fs []
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC list_rel_IMP_env_rel \\ fs []
      \\ `LIST_REL (val_rel f6 t6.refs t2.code) cl_env ys` by
       (Q.PAT_ASSUM `LIST_REL vvv cl_env ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [val_rel_SUBMAP])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ DISJ1_TAC
      \\ Q.UNABBREV_TAC `bb` \\ fs [] \\ METIS_TAC [])
    (* general case for mutually recursive closures *)
    \\ Q.PAT_ASSUM `val_rel f2 t2.refs t1.code xxx y` MP_TAC
    \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
    \\ REPEAT STRIP_TAC THEN1 (SRW_TAC [] [] \\ fs [])
    \\ SRW_TAC [] [] \\ fs []
    \\ fs [MAP_MAP_o,EL_MAP]
    \\ SIMP_TAC std_ss [Once bEvalOp_def] \\ fs [find_code_def]
    \\ POP_ASSUM (fn th => ASSUME_TAC th THEN
         ASSUME_TAC (REWRITE_RULE [closure_code_installed_def] th))
    \\ fs [EVERY_MEM]
    \\ `MEM (EL index exps_ps) exps_ps` by METIS_TAC [MEM_EL]
    \\ FIRST_ASSUM (MP_TAC o Q.SPEC `EL index exps_ps`)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\ `?exp p. EL index exps_ps = (exp,p)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6`
    \\ `t6.clock = s6.clock` by fs [state_rel_def]
    \\ `n0 + index = p` by METIS_TAC [EL_index_ps]
    \\ Cases_on `t6.clock = 0` \\ fs []
    THEN1 (Q.EXISTS_TAC `f6` \\ IMP_RES_TAC SUBMAP_TRANS
           \\ SRW_TAC [] [res_rel_cases])
    \\ rfs [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux`,`dec_clock t6`]) \\ fs []
    \\ `state_rel f6 (dec_clock s6) (dec_clock t6)` by ALL_TAC THEN1
      (fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def])
    \\ `code_installed aux1' (dec_clock t6).code` by ALL_TAC THEN1
      (fs [bvlTheory.dec_clock_def]) \\ fs [] \\ STRIP_TAC
    \\ SIMP_TAC std_ss [code_for_recc_case_def]
    \\ fs [bEval_def,bEvalOp_def]
    \\ ONCE_REWRITE_TAC [bEval_CONS]
    \\ fs [bEval_def,o_DEF]
    \\ Q.ABBREV_TAC `zs = (MAP (\x. Block closure_tag [CodePtr (SND x); RefPtr r])
               exps_ps ++ ys)`
    \\ `bEval
         (GENLIST (\i. Op Deref [Var 0; Op (Const (&i)) []])
            (LENGTH cl_env + LENGTH exps_ps),
          [RefPtr r; Block closure_tag [CodePtr p; RefPtr r]; y'],
          dec_clock t6) = (Result zs,dec_clock t6)` by ALL_TAC THEN1
     (MATCH_MP_TAC bEval_ValueArray
      \\ UNABBREV_ALL_TAC \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [dec_clock_def,AC ADD_COMM ADD_ASSOC]
      \\ IMP_RES_TAC FLOOKUP_SUBMAP_IMP) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y':: (zs ++ [RefPtr r] ++
             [Block closure_tag [CodePtr p; RefPtr r]; y'])`,`f6`])
    \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [env_rel_def,dec_clock_def]
      \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ MATCH_MP_TAC list_rel_IMP_env_rel
      \\ UNABBREV_ALL_TAC
      \\ MATCH_MP_TAC EVERY2_APPEND_suff
      \\ REVERSE (REPEAT STRIP_TAC) THEN1
       (Q.PAT_ASSUM `LIST_REL xxx cl_env ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [val_rel_SUBMAP])
      \\ SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
      \\ fs [LENGTH_MAP,LENGTH_GENLIST,EL_MAP]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `k7 < LENGTH exps_ps`
      \\ SIMP_TAC std_ss [Once val_rel_cases] \\ fs [] \\ DISJ2_TAC
      \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`,`ys`]
      \\ fs [EL_MAP] \\ IMP_RES_TAC FLOOKUP_SUBMAP_IMP \\ fs []
      \\ `MAP (\x. Block closure_tag [CodePtr (SND x); RefPtr r]) exps_ps =
          MAP (\x. Block closure_tag [CodePtr x; RefPtr r]) (MAP SND exps_ps)`
           by (fs [MAP_MAP_o,o_DEF]) \\ fs []
      \\ Q.PAT_ASSUM `LIST_REL xxx cl_env ys` MP_TAC
      \\ MATCH_MP_TAC listTheory.LIST_REL_mono
      \\ METIS_TAC [val_rel_SUBMAP])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `res'` \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ fs [dec_clock_def]
    \\ IMP_RES_TAC SUBMAP_TRANS
    \\ ASM_SIMP_TAC std_ss []
    \\ `[HD a] = a` by ALL_TAC \\ fs []
    \\ IMP_RES_TAC bEval_IMP_LENGTH
    \\ Cases_on `a` \\ fs [LENGTH_NIL] *)
  THEN1 (* Tick *)
   (rw [] >>
    fs [cComp_def]
    \\ `?p. cEval ([x],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. cComp [x] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cComp_SING \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (fs [cEval_def] \\ SRW_TAC [] [res_rel_cases]
      \\ Q.EXISTS_TAC `f1` \\ fs [SUBMAP_REFL])
    \\ fs [cEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock 1 t1`,`env''`,`f1`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (fs [dec_clock_def,state_rel_def,closLangTheory.dec_clock_def])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2` \\ fs [dec_clock_def])
  THEN1 (* Call *)
   (rw [] >>
    fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval (xs,env,s1) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env''`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1]
    \\ fs [closLangTheory.find_code_def,bvlTheory.find_code_def]
    \\ Cases_on `FLOOKUP p1.code dest` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ Cases_on `q = LENGTH a` \\ fs []
    \\ `?aux1 c2 aux2.
          cComp [r] aux1 = ([c2],aux2) /\
          lookup (dest + num_stubs) t2.code = SOME (LENGTH a,c2) /\
          code_installed aux2 t2.code` by METIS_TAC [state_rel_def]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `t2.clock = p1.clock` by fs [state_rel_def]
    \\ Cases_on `t2.clock = 0` \\ fs []
    THEN1 (SRW_TAC [] [] \\ Q.EXISTS_TAC `f2`  >>
           fs [res_rel_cases] >>
           `state_rel f2 (p1 with clock := p1.clock) (t2 with clock := p1.clock)` 
                    by metis_tac [state_rel_clocks] >>
           `(p1 with clock := p1.clock) = p1` by rw [clos_state_component_equality] >>
           metis_tac [])
    \\ fs [] \\ rfs [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`dec_clock 1 t2`,`ys`,`f2`]) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [closLangTheory.dec_clock_def,state_rel_def,bvlTheory.dec_clock_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ METIS_TAC [APPEND_NIL])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [dec_clock_def])
  THEN1
   ((* cEvalApp [] *)
    fs [cEval_def, res_rel_cases] >>
    rw [] >>
    metis_tac [SUBMAP_REFL])
  THEN1
   ((* cEvalApp real app *)

    qpat_assum `cEvalApp x0 x1 x2 x3 = x4` mp_tac
    \\ simp [cEval_def]
    \\ qabbrev_tac `args = v41::v42`
    \\ DISCH_TAC
    \\ qabbrev_tac `args' = args''`
    \\ `LENGTH args' ≠ 0` by metis_tac [LIST_REL_LENGTH, LENGTH, DECIDE ``SUC x ≠ 0``]
    \\ fs []
    \\ Cases_on `dest_closure loc_opt func args`
    \\ fs []
    \\ Cases_on `x`
    \\ fs []
    \\ rw []
    >- ((* Partial application *)
        `LENGTH args = LENGTH args' ∧ LENGTH args ≠ 0` by metis_tac [LIST_REL_LENGTH] >>
        imp_res_tac dest_closure_part_app >>
        rw [res_rel_cases, PULL_EXISTS] >>
        imp_res_tac val_rel_num_rem_args >>
        reverse (rw [mk_cl_call_def, bEval_def, bEval_APPEND, bEvalOp_def])
        >- ARITH_TAC >>
        `0 < LENGTH args'` by COOPER_TAC >>
        full_simp_tac (bool_ss++ARITH_ss) [el_append3] >>
        reverse (rw [])
        >- ARITH_TAC >>
        `&n − 1 ≠ &(LENGTH args' − 1)` by (fs [int_arithTheory.INT_NUM_SUB] >> ARITH_TAC) >>
        rw [] >>
        `bEval (GENLIST Var (LENGTH args'),
                args' ++ [Block tag (CodePtr ptr::Number (&n-1)::rest)] ++ env,
                t1) = (Result args', t1)` 
                    by metis_tac [bEval_simple_genlist_vars, APPEND_ASSOC] >>
        simp [] >>
        fs [] >>
        `LENGTH args' - 1 < max_app` by decide_tac >>
        `lookup (LENGTH args' - 1) t1.code = SOME (LENGTH args' + 1, generate_generic_app (LENGTH args' - 1))` 
               by (fs [state_rel_def] >>
                   decide_tac) >>
        simp [find_code_def] >>
        `SUC (LENGTH v42) = LENGTH args` by metis_tac [LENGTH] >>
        `s1.clock = t1.clock` by fs [state_rel_def] >>
        fs [] >>
        rw [FRONT_DEF, FRONT_APPEND]
        >- (qexists_tac `f1` >>
            simp [SUBMAP_REFL] >>
            fs [] >>
            `t1 = t1 with clock := 0` by rw [bvl_state_explode] >>
            metis_tac [state_rel_clocks]) >>
        imp_res_tac unpack_closure_thm >>
        mp_tac (Q.SPECL [`total_args`, `prev_args`, `dec_clock 1 t1`,
                         `args'`, `Block tag (CodePtr ptr::Number (&n-1)::rest)`, `clo`] bEval_generic_app_partial) >>
        simp [] >>
        `lookup (partial_app_fn_location total_args (LENGTH args' + LENGTH prev_args − 1)) t1.code =
             SOME (total_args - (LENGTH args' + LENGTH prev_args-1) + 1, generate_partial_app_closure_fn total_args (LENGTH args' + LENGTH prev_args − 1))`
                 by (fs [state_rel_def] >>
                     first_x_assum match_mp_tac >>
                     rw [] >>
                     decide_tac) >>
        simp_tac (srw_ss()) [domain_lookup] >>
        rw []
        >- ((* A TimeOut *)
            full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, int_arithTheory.INT_NUM_SUB] >>
            qexists_tac `f1` >>
            rw [SUBMAP_REFL] >>
            metis_tac [state_rel_clocks])
        >- ((* Result *)
            `~(t1.clock < LENGTH args')` by (fs [dec_clock_def] >> decide_tac) >>
            fs [] >>
            rw [] >>
            qexists_tac `f1` >>
            REVERSE (rw [])
            >- (rw [dec_clock_def, closLangTheory.dec_clock_def] >>
                metis_tac [state_rel_clocks, arith_helper_lem]) >>
            `args ≠ []` by (Cases_on `args` >> fs []) >>
            fs [val_rel_cases, num_remaining_args_def] >>
            rw [] >>
            fs [num_remaining_args_def, add_args_def, bytecodeTheory.partial_app_tag_def]
            >- ((* Wrapping a normal closure *)
                MAP_EVERY qexists_tac [`args`, `func`, `env'`, `rest`, `total_args + 1`] >>
                fs [] >>
                imp_res_tac cl_rel_get_num_args >>
                rw [SUB_LEFT_SUB, LESS_OR_EQ] >>
                fs [])
            >- ((* Wrapping a partially applied closure *)
                fs [unpack_closure_cases, bytecodeTheory.partial_app_tag_def] >>
                rw [] >>
                MAP_EVERY qexists_tac [`args++arg_env`, `cl`, `env'`, `fvs`, `total_args+1`] >>
                fs [] >>
                imp_res_tac EVERY2_LENGTH >>
                rw []
                >- metis_tac [EVERY2_APPEND]
                >- decide_tac
                >- metis_tac [arith_helper_lem3]
                >- metis_tac [add_args_append]
                >- (full_simp_tac (srw_ss()++ARITH_ss) [int_arithTheory.INT_NUM_SUB] >>
                    metis_tac [arith_helper_lem2]))))

    >- ((* Enough arguments to do something *)
         `SUC (LENGTH v42) = LENGTH args` by metis_tac [LENGTH] >>
         fs [] >>
         imp_res_tac dest_closure_full_app >>
         imp_res_tac val_rel_num_rem_args >>
         `loc_opt = NONE ∨ ?loc. loc_opt = SOME loc` by metis_tac [option_nchotomy] >>
         fs [check_loc_def] >>
         rw []
         >- ((* App NONE *)

             qabbrev_tac `func' = Block tag (CodePtr ptr::Number (&rem_args − 1)::rest)` >>
             qabbrev_tac `n = rem_args - 1` >>
             `bEval ([Var (LENGTH args')], args' ++ [func'] ++ env,t1) = (Result [func'], t1)` 
                      by simp [bEval_def, el_append3] >>
             imp_res_tac EVERY2_LENGTH >>
             `bEval (GENLIST Var (LENGTH args'), args' ++ [func'] ++ env,t1) = (Result args', t1)` 
                      by (mp_tac (Q.SPECL [`0`, `args'++[func']++env`, `LENGTH (args':bc_value list)`] bEval_genlist_vars) >>
                          simp [ETA_THM] >>
                          metis_tac [APPEND_ASSOC, TAKE_LENGTH_APPEND]) >>
             `lookup (LENGTH args' − 1) t1.code = 
                SOME ((LENGTH args' - 1) + 2,generate_generic_app (LENGTH args' − 1))`
                         by (fs [state_rel_def] >>
                             `LENGTH args' - 1 < max_app` by decide_tac >>
                             metis_tac []) >>
             `LENGTH args' - 1 + 2  = LENGTH args' + 1` by decide_tac >>
             fs [] >>
             `&rem_args - 1 = &n ∧ rem_args + 1 = n + 2` 
                  by (srw_tac [ARITH_ss] [Abbr `n`,int_arithTheory.INT_NUM_SUB]) >>
             fs [Abbr `func'`] >>
             strip_assume_tac (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] (bEval_mk_cl_call)) >>
             rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
             pop_assum mp_tac >>
             simp [] >>
             DISCH_TAC >>
             pop_assum (fn x => all_tac) >>
             simp [] >>
             `LENGTH args' − (LENGTH args' − rem_args) = rem_args` by decide_tac >>
             fs [] >>
             `s1.clock = t1.clock` by fs [state_rel_def] >>
             Cases_on `t1.clock < rem_args` >>
             fs [] >>
             simp []
             >- ((* Timeout *)
                 rw [res_rel_cases] >>
                 metis_tac [SUBMAP_REFL, state_rel_clocks]) >>
             (* TODO This isn't true, the clock invariant needs to change. 
              * On a call to a partiallly applied closure that goes through the generic mechanism, with 1 
              * argument added to some existing arguments, the clos semantics
              * ticks once, but the bvl has to tick twice: once to call the general
              * mechanism, and once to actually call the function. *)
             `t1.clock ≠ rem_args` by cheat >> 
             simp [] >>
             rw []
             >- ((* No extra arguments *)
                 imp_res_tac val_rel_run >>
                 fs [int_arithTheory.INT_NUM_SUB] >>
                 rfs [] >>
                 pop_assum (qspec_then `dec_clock (LENGTH args') t1` strip_assume_tac) >>
                 rw [] >>
                 `t1.refs = (dec_clock (LENGTH args') t1).refs` by rw [dec_clock_def] >>
                 ASM_REWRITE_TAC [] >>
                 first_x_assum match_mp_tac >>
                 qexists_tac `aux1` >>
                 qexists_tac `aux2` >>
                 fs [] >>
                 BasicProvers.EVERY_CASE_TAC >>
                 fs [] >>
                 rw [state_rel_clocks, dec_clock_def, closLangTheory.dec_clock_def] >>
                 Cases_on `l0` >>
                 fs [cEval_def])

             >- ((* Extra arguments *)
                 cheat))

         >- ((* App SOME *)
             `rem_args = LENGTH args` by ARITH_TAC >>
             fs [] >>
             rw [find_code_def] >>
             qpat_assum `val_rel x0 x1 x2 x3 x4` (fn x => mp_tac x >> simp [val_rel_cases] >> assume_tac x) >>
             reverse (rw []) >>
             imp_res_tac EVERY2_LENGTH
             >- metis_tac [no_partial_args] >>
             imp_res_tac cl_rel_get_loc >>
             fs [] >>
             TRY BasicProvers.VAR_EQ_TAC >>
             simp [] >>
             `s1.clock = t1.clock` by fs [state_rel_def] >>
             fs [] >>
             rw [] >>
             fs []
             >- ((* TimeOut *)
                 rw [res_rel_cases] >>
                 metis_tac [SUBMAP_REFL, state_rel_clocks]) >>
             `?res' s2. cEval ([c],l,dec_clock (LENGTH args') s1) = (res',s2)` 
                          by metis_tac [pair_CASES]  >>
             fs [] >>
             `l0 = []` by (Cases_on `l0` >> fs []) >>
             rw [] >>
             `res' = res ∧ s2' = s2` 
                     by (Cases_on `res'` >> 
                         fs [] >>
                         Cases_on `a` >>
                         fs [] >>
                         Cases_on `t` >>
                         fs [cEval_def]) >>
             rw [] >>
             fs [] >>
             `t1.refs = (dec_clock (LENGTH args') t1).refs` by rw [dec_clock_def] >>
             strip_assume_tac (SIMP_RULE (srw_ss()++boolSimps.DNF_ss) [GSYM AND_IMP_INTRO] (cl_rel_run)) >>
             pop_assum (fn x => all_tac) >>
             rpt (pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x))) >>
             pop_assum (qspec_then `dec_clock (LENGTH args') t1` strip_assume_tac) >>
             `state_rel f1 (dec_clock (LENGTH args') s1) (dec_clock (LENGTH args') t1)` 
                      by rw [closLangTheory.dec_clock_def, dec_clock_def, state_rel_clocks] >>
             `code_installed aux2 (dec_clock (LENGTH args') t1).code` by rw [] >>
             first_x_assum (fn x => first_assum (strip_assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] x))) >>
             pop_assum (fn x => first_assum (strip_assume_tac o MATCH_MP x)) >>
             fs []))));

val cComp_ind = theorem"cComp_ind";

open clos_numberTheory boolSimps

val build_aux_thm = prove(
  ``∀c n aux n7 aux7.
    build_aux n c aux = (n7,aux7++aux) ⇒
    (MAP FST aux7) = (REVERSE (GENLIST ($+ n) (LENGTH c)))``,
  Induct >> simp[build_aux_def] >> rw[] >>
  qmatch_assum_abbrev_tac`build_aux nn kk auxx = Z` >>
  qspecl_then[`kk`,`nn`,`auxx`]strip_assume_tac build_aux_lemma >>
  Cases_on`build_aux nn kk auxx`>>UNABBREV_ALL_TAC>>fs[]>> rw[] >>
  full_simp_tac std_ss [Once (CONS_APPEND)] >>
  full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)] >> res_tac >>
  rw[GENLIST,REVERSE_APPEND,REVERSE_GENLIST,PRE_SUB1] >>
  simp[LIST_EQ_REWRITE])

val lemma =
  SIMP_RULE(std_ss++LET_ss)[UNCURRY]cComp_lemma

fun tac (g as (asl,w)) =
  let
    fun get tm =
      let
        val tm = tm |> strip_forall |> snd |> dest_imp |> fst
        fun a tm =
          let
            val (f,xs) = strip_comb tm
          in
            same_const``cComp``f andalso
            length xs = 2
          end
      in
        first a [rhs tm, lhs tm]
      end
    val tm = tryfind get asl
    val args = snd(strip_comb tm)
  in
    Cases_on[ANTIQUOTE tm] >>
    strip_assume_tac(SPECL args lemma) >>
    rfs[]
  end g

val cComp_code_locs = store_thm("cComp_code_locs",
  ``∀xs aux ys aux2.
    cComp xs aux = (ys,aux2++aux) ⇒
    MAP FST aux2 = MAP ((+) num_stubs) (REVERSE(code_locs xs))``,
  cheat);
  (*
  ho_match_mp_tac cComp_ind >> rpt conj_tac >>
  TRY (
    rw[cComp_def] >>
    Cases_on`fns`>>fs[code_locs_def]>-(
      fs[LET_THM] ) >>
    Cases_on`t`>>fs[code_locs_def]>-(
      rw[] >> tac >> tac  >> rw[] >> fs[LET_THM] >> rw[] ) >>
    simp[] >> rw[] >>
    fs[cComp_def,LET_THM,UNCURRY] >> rw[] >>
    qmatch_assum_abbrev_tac`SND (cComp [x1] aux1) = aux2 ++ aux` >>
    qspecl_then[`[x1]`,`aux1`]strip_assume_tac lemma >>
    Cases_on`cComp [x1] aux1`>>fs[Abbr`aux1`] >> rw[] >>
    qmatch_assum_abbrev_tac`ys++SND(build_aux loc aux1 z) = aux2 ++ aux` >>
    qspecl_then[`aux1`,`loc`,`z`]STRIP_ASSUME_TAC build_aux_lemma >>
    Cases_on`build_aux loc aux1 z`>>fs[] >>
    qspecl_then[`[h]`,`aux`]strip_assume_tac lemma >>
    Cases_on`cComp [h] aux`>>fs[] >> rw[] >>
    qspecl_then[`h'::t'`,`ys'++aux`]strip_assume_tac lemma >>
    Cases_on`cComp (h'::t') (ys'++aux)`>>fs[] >> rw[] >>
    fs[Abbr`z`] >> rw[] >> fs[] >>
    full_simp_tac std_ss [GSYM APPEND_ASSOC]  >>
    imp_res_tac build_aux_thm >>
    simp[Abbr`aux1`,ADD1]) >>
  simp[cComp_def,code_locs_def,UNCURRY] >> rw[] >>
  rpt tac >> rw[] >> fs[] >> rw[]);
  *)

  (*
open clos_annotateTheory
*)

val code_locs_def = tDefine "code_locs" `
  (code_locs [] = []) /\
  (code_locs (x::y::xs) =
     let c1 = code_locs [x] in
     let c2 = code_locs (y::xs) in
       c1 ++ c2) /\
  (code_locs [Var v] = []) /\
  (code_locs [If x1 x2 x3] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
     let c3 = code_locs [x3] in
       c1 ++ c2 ++ c3) /\
  (code_locs [Let xs x2] =
     let c1 = code_locs xs in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Raise x1] =
     code_locs [x1]) /\
  (code_locs [Handle x1 x2] =
     let c1 = code_locs [x1] in
     let c2 = code_locs [x2] in
       c1 ++ c2) /\
  (code_locs [Tick x1] =
     code_locs [x1]) /\
  (code_locs [Op op xs] =
     case op of
       Label loc => code_locs xs ++ [loc]
     | _ => code_locs xs) /\
  (code_locs [Call ticks dest xs] =
     case dest of NONE => code_locs xs
                | SOME loc => loc::code_locs xs)`
 (WF_REL_TAC `measure (bvl_exp1_size)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val code_locs_cons = store_thm("code_locs_cons",
  ``∀x xs. code_locs (x::xs) = code_locs [x] ++ code_locs xs``,
  gen_tac >> Cases >> simp[code_locs_def])

val code_locs_append = store_thm("code_locs_append",
  ``∀l1 l2. clos_to_bvl$code_locs (l1 ++ l2) = code_locs l1 ++ code_locs l2``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[Once code_locs_cons,SimpRHS])

val code_locs_MAP_Var = store_thm("code_locs_MAP_Var",
  ``code_locs (MAP Var xs) = []``,
  Induct_on`xs`>>simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[code_locs_def])

val code_locs_MAP_K_Op_Const = store_thm("code_locs_MAP_K_Op_Const",
  ``∀ls. code_locs (MAP (K (Op (Const n) [])) ls) = []``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[code_locs_def])

val cComp_sing_lemma = prove(
  ``[HD (FST (cComp [x] y))] = (FST (cComp [x] y))``,
  Cases_on`cComp [x] y` >>
  imp_res_tac cComp_SING >> rw[])

val contains_Op_Label_def = tDefine "contains_Op_Label" `
  (contains_Op_Label [] ⇔ F) /\
  (contains_Op_Label (x::y::xs) ⇔
     contains_Op_Label [x] ∨
     contains_Op_Label (y::xs)) /\
  (contains_Op_Label [Var v] ⇔ F) /\
  (contains_Op_Label [If x1 x2 x3] ⇔
     contains_Op_Label [x1] ∨
     contains_Op_Label [x2] ∨
     contains_Op_Label [x3]) /\
  (contains_Op_Label [Let xs x2] ⇔
     contains_Op_Label [x2] ∨
     contains_Op_Label xs) /\
  (contains_Op_Label [Raise x1] ⇔
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Tick x1] ⇔
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Op op xs] ⇔
     (∃n. op = Label n) ∨
     contains_Op_Label xs) /\
  (contains_Op_Label [App loc_opt x1 xs] ⇔
     contains_Op_Label [x1] ∨
     contains_Op_Label xs) /\
  (contains_Op_Label [Fn loc vs num_args x1] ⇔
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Letrec loc vs fns x1] ⇔
     contains_Op_Label (MAP SND fns) ∨
     contains_Op_Label [x1]) /\
  (contains_Op_Label [Handle x1 x2] ⇔
     contains_Op_Label [x1] ∨
     contains_Op_Label [x2]) /\
  (contains_Op_Label [Call dest xs] ⇔
     contains_Op_Label xs)`
 (WF_REL_TAC `measure (clos_exp3_size)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

val contains_Op_Label_EXISTS = prove(
  ``∀ls. contains_Op_Label ls ⇔ EXISTS (λx. contains_Op_Label [x]) ls``,
  Induct >> simp[contains_Op_Label_def] >>
  Cases_on`ls`>>fs[contains_Op_Label_def])

val contains_Call_def = tDefine "contains_Call" `
  (contains_Call [] ⇔ F) /\
  (contains_Call (x::y::xs) ⇔
     contains_Call [x] ∨
     contains_Call (y::xs)) /\
  (contains_Call [Var v] ⇔ F) /\
  (contains_Call [If x1 x2 x3] ⇔
     contains_Call [x1] ∨
     contains_Call [x2] ∨
     contains_Call [x3]) /\
  (contains_Call [Let xs x2] ⇔
     contains_Call [x2] ∨
     contains_Call xs) /\
  (contains_Call [Raise x1] ⇔
     contains_Call [x1]) /\
  (contains_Call [Tick x1] ⇔
     contains_Call [x1]) /\
  (contains_Call [Op op xs] ⇔
     contains_Call xs) /\
  (contains_Call [App loc_opt x1 xs] ⇔
     contains_Call [x1] ∨
     contains_Call xs) /\
  (contains_Call [Fn loc vs num_args x1] ⇔
     contains_Call [x1]) /\
  (contains_Call [Letrec loc vs fns x1] ⇔
     contains_Call (MAP SND fns) ∨
     contains_Call [x1]) /\
  (contains_Call [Handle x1 x2] ⇔
     contains_Call [x1] ∨
     contains_Call [x2]) /\
  (contains_Call [Call dest xs] ⇔ T)`
 (WF_REL_TAC `measure (clos_exp3_size)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

val contains_Call_EXISTS = prove(
  ``∀ls. contains_Call ls ⇔ EXISTS (λx. contains_Call [x]) ls``,
  Induct >> simp[contains_Call_def] >>
  Cases_on`ls`>>fs[contains_Call_def])

open pat_to_closTheory

val pComp_contains_Op_Label = store_thm("pComp_contains_Op_Label",
  ``∀e. ¬contains_Op_Label[pComp e]``,
  ho_match_mp_tac pComp_ind >>
  simp[pComp_def,contains_Op_Label_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_Op_Label_EXISTS,EVERY_MAP] >>
  rw[contains_Op_Label_def] >> rw[EVERY_MEM] >>
  rw[Once contains_Op_Label_EXISTS,EVERY_MAP] >>
  rw[contains_Op_Label_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_Op_Label_def])

val pComp_contains_Call = store_thm("pComp_contains_Call",
  ``∀e. ¬contains_Call[pComp e]``,
  ho_match_mp_tac pComp_ind >>
  simp[pComp_def,contains_Call_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_Call_EXISTS,EVERY_MAP] >>
  rw[contains_Call_def] >> rw[EVERY_MEM] >>
  rw[Once contains_Call_EXISTS,EVERY_MAP] >>
  rw[contains_Call_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_Call_def])

val code_locs_recc_Lets = store_thm("code_locs_recc_Lets",
  ``∀n loc nargs r. set (code_locs [recc_Lets loc nargs n r]) = IMAGE ($+ loc) (count n) ∪ set (code_locs [r])``,
  Induct >> simp[Once recc_Lets_def,code_locs_def,recc_Let_def,COUNT_SUC] >>
  simp[EXTENSION] >> METIS_TAC[]);

val code_locs_build_recc_lets = store_thm("code_locs_build_recc_lets",
  ``∀args vs loc n r.
      set (code_locs [build_recc_lets args vs loc (SUC n) r]) = IMAGE ($+ loc) (count (SUC n)) ∪ set (code_locs [r])``,
  REWRITE_TAC [build_recc_lets_def, GSYM MAP_REVERSE, REVERSE_APPEND] >>
  simp[code_locs_def,code_locs_MAP_Var,recc_Let0_def,code_locs_recc_Lets,COUNT_SUC] >>
  rw[Once code_locs_cons,code_locs_def,code_locs_append,code_locs_MAP_Var,code_locs_MAP_K_Op_Const] >>
  rw[EXTENSION] >> METIS_TAC[])

  (*
val code_locs_cComp = store_thm("code_locs_cComp",
  ``∀xs aux.
      ¬contains_Op_Label xs ∧ ¬contains_App_SOME xs ∧ ¬contains_Call xs ⇒
      set (code_locs (FST(cComp xs aux))) ⊆ set (code_locs xs)``,
  ho_match_mp_tac cComp_ind >> rpt conj_tac >>
  TRY (
    simp[contains_Op_Label_def,clos_numberTheory.contains_App_SOME_def,contains_Call_def] >>
    simp[cComp_def,clos_numberTheory.code_locs_def] >> rw[] >> fs[] >>
    Cases_on`xs`>>fs[clos_numberTheory.code_locs_def] >>
    Cases_on`t`>>fs[] >- (
      tac >>
      simp[UNCURRY,code_locs_def,cComp_sing_lemma] >>
      simp[Once code_locs_cons,code_locs_def,code_locs_MAP_Var] >>
      fs[SUBSET_DEF] ) >>
    fs[cComp_def,LET_THM] >>
    Cases_on`cComp[h]aux`>>fs[]>>
    Cases_on`cComp(h'::t')r`>>fs[]>>
    Q.PAT_ABBREV_TAC`p = build_aux X Y Z` >>
    Cases_on`p`>>fs[]>>
    simp[UNCURRY] >>
    simp[code_locs_build_recc_lets,cComp_sing_lemma] >>
    fs[contains_App_SOME_def,contains_Op_Label_def,contains_Call_def] >>
    fs[SUBSET_DEF,cComp_sing_lemma] >>
    simp[MEM_GENLIST,PULL_EXISTS] >>
    NO_TAC) >>
  simp[cComp_def,clos_numberTheory.code_locs_def,code_locs_def,UNCURRY,
                 clos_annotateTheory.code_locs_append,code_locs_append,
                 cComp_sing_lemma,contains_Op_Label_def,
                 clos_numberTheory.contains_App_SOME_def,
                 contains_Call_def] >>
  rw[cComp_sing_lemma] >>
  rpt tac >> rw[] >> fs[cComp_sing_lemma] >>
  fs[SUBSET_DEF]
  >- ( Cases_on`op`>>simp[cCompOp_def]>>fs[] )
  >- ( simp[Once code_locs_cons,code_locs_def,code_locs_MAP_Var] ))

val HD_FST_cFree_sing = prove(
  ``[HD (FST (cFree [x]))] = FST(cFree [x])``,
  simp[SING_HD,LENGTH_FST_cFree])

val HD_cShift_sing = prove(
  ``[HD (cShift [x] y z w)] = cShift [x] y z w``,
  rw[SING_HD,cShift_LENGTH_LEMMA])

val contains_Call_append = store_thm("contains_Call_append",
  ``contains_Call (l1 ++ l2) = (contains_Call l1 ∨ contains_Call l2)``,
  METIS_TAC[contains_Call_EXISTS,EXISTS_APPEND])

val contains_Call_cFree = store_thm("contains_Call_cFree",
  ``∀v. contains_Call (FST (cFree v)) = contains_Call v``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,contains_Call_def,UNCURRY,HD_FST_cFree_sing,contains_Call_append] >>
  rw[] >> METIS_TAC[PAIR])

val contains_Call_cShift = store_thm("contains_Call_cShift",
  ``∀a b c d. contains_Call (cShift a b c d) ⇔ contains_Call a``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,contains_Call_def,HD_cShift_sing,contains_Call_append])

val contains_Call_cAnnotate = store_thm("contains_Call_cAnnotate",
  ``∀n e. contains_Call (cAnnotate n e) ⇔ contains_Call e``,
  rw[cAnnotate_def,contains_Call_cShift,contains_Call_cFree])

val contains_App_SOME_append = store_thm("contains_App_SOME_append",
  ``contains_App_SOME (l1 ++ l2) = (contains_App_SOME l1 ∨ contains_App_SOME l2)``,
  METIS_TAC[contains_App_SOME_EXISTS,EXISTS_APPEND])

val contains_App_SOME_cFree = store_thm("contains_App_SOME_cFree",
  ``∀v. contains_App_SOME (FST (cFree v)) = contains_App_SOME v``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,contains_App_SOME_def,UNCURRY,HD_FST_cFree_sing,contains_App_SOME_append] >>
  rw[] >> METIS_TAC[PAIR])

val contains_App_SOME_cShift = store_thm("contains_App_SOME_cShift",
  ``∀a b c d. contains_App_SOME (cShift a b c d) ⇔ contains_App_SOME a``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,contains_App_SOME_def,HD_cShift_sing,contains_App_SOME_append])

val contains_App_SOME_cAnnotate = store_thm("contains_App_SOME_cAnnotate",
  ``∀n e. contains_App_SOME (cAnnotate n e) ⇔ contains_App_SOME e``,
  rw[cAnnotate_def,contains_App_SOME_cShift,contains_App_SOME_cFree])

val contains_Op_Label_append = store_thm("contains_Op_Label_append",
  ``contains_Op_Label (l1 ++ l2) = (contains_Op_Label l1 ∨ contains_Op_Label l2)``,
  METIS_TAC[contains_Op_Label_EXISTS,EXISTS_APPEND])

val contains_Op_Label_cFree = store_thm("contains_Op_Label_cFree",
  ``∀v. contains_Op_Label (FST (cFree v)) = contains_Op_Label v``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,contains_Op_Label_def,UNCURRY,HD_FST_cFree_sing,contains_Op_Label_append] >>
  rw[] >> METIS_TAC[PAIR])

val contains_Op_Label_cShift = store_thm("contains_Op_Label_cShift",
  ``∀a b c d. contains_Op_Label (cShift a b c d) ⇔ contains_Op_Label a``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,contains_Op_Label_def,HD_cShift_sing,contains_Op_Label_append])

val contains_Op_Label_cAnnotate = store_thm("contains_Op_Label_cAnnotate",
  ``∀n e. contains_Op_Label (cAnnotate n e) ⇔ contains_Op_Label e``,
  rw[cAnnotate_def,contains_Op_Label_cShift,contains_Op_Label_cFree])

fun tac (g as (asl,w)) =
  let
    fun finder tm =
      let
        val (f,args) = strip_comb tm
      in
        (same_const``renumber_code_locs`` f orelse
         same_const``renumber_code_locs_list`` f)
        andalso
         all is_var args
        andalso
         length args = 2
      end
    val tms = find_terms finder w
  in
    map_every (fn tm => Cases_on [ANTIQUOTE tm]) tms g
  end

val contains_Call_cons = store_thm("contains_Call_cons",
  ``contains_Call (e::x) ⇔ contains_Call [e] ∨ contains_Call x``,
  METIS_TAC[contains_Call_EXISTS,listTheory.EXISTS_DEF])

val contains_Call_renumber_code_locs = store_thm("contains_Call_renumber_code_locs",
  ``(∀n e m f. renumber_code_locs_list n e = (m,f) ⇒
      (contains_Call f ⇔ contains_Call e)) ∧
    (∀n e m f. renumber_code_locs n e = (m,f) ⇒
      (contains_Call [f] ⇔ contains_Call [e]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[contains_Call_def,renumber_code_locs_def,UNCURRY] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >-
  METIS_TAC[contains_Call_cons] >>
  Cases_on`renumber_code_locs (q + LENGTH r) e'`>>fs[])

val contains_App_SOME_cons = store_thm("contains_App_SOME_cons",
  ``contains_App_SOME (e::x) ⇔ contains_App_SOME [e] ∨ contains_App_SOME x``,
  METIS_TAC[contains_App_SOME_EXISTS,listTheory.EXISTS_DEF])

val contains_App_SOME_renumber_code_locs = store_thm("contains_App_SOME_renumber_code_locs",
  ``(∀n e m f. renumber_code_locs_list n e = (m,f) ⇒
      (contains_App_SOME f ⇔ contains_App_SOME e)) ∧
    (∀n e m f. renumber_code_locs n e = (m,f) ⇒
      (contains_App_SOME [f] ⇔ contains_App_SOME [e]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[contains_App_SOME_def,renumber_code_locs_def,UNCURRY] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >-
  METIS_TAC[contains_App_SOME_cons] >>
  Cases_on`renumber_code_locs (q + LENGTH r) e'`>>fs[])

val contains_Op_Label_cons = store_thm("contains_Op_Label_cons",
  ``contains_Op_Label (e::x) ⇔ contains_Op_Label [e] ∨ contains_Op_Label x``,
  METIS_TAC[contains_Op_Label_EXISTS,listTheory.EXISTS_DEF])

val contains_Op_Label_renumber_code_locs = store_thm("contains_Op_Label_renumber_code_locs",
  ``(∀n e m f. renumber_code_locs_list n e = (m,f) ⇒
      (contains_Op_Label f ⇔ contains_Op_Label e)) ∧
    (∀n e m f. renumber_code_locs n e = (m,f) ⇒
      (contains_Op_Label [f] ⇔ contains_Op_Label [e]))``,
  ho_match_mp_tac renumber_code_locs_ind >>
  simp[contains_Op_Label_def,renumber_code_locs_def,UNCURRY] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >>
  tac >> fs[] >> rw[] >-
  METIS_TAC[contains_Op_Label_cons] >>
  Cases_on`renumber_code_locs (q + LENGTH r) e'`>>fs[])
  *)

val _ = export_theory();
