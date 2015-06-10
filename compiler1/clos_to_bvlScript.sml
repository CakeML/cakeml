open preamble closLangTheory bvlTheory bvl_jumpTheory;

val _ = new_theory "clos_to_bvl";

val closure_tag_def = Define`closure_tag = 0:num`
val partial_app_tag_def = Define`partial_app_tag = 1:num`
val clos_tag_shift_def = Define`clos_tag_shift = 2:num`
val _ = EVAL``partial_app_tag = closure_tag`` |> EQF_ELIM
  |> curry save_thm"partial_app_tag_neq_closure_tag[simp]";

val compile_op_def = Define`
  compile_op (Cons tag) = (Cons (tag+clos_tag_shift)) ∧
  compile_op (TagEq tag) = (TagEq (tag+clos_tag_shift)) ∧
  compile_op (TagLenEq tag a) = (TagLenEq (tag+clos_tag_shift) a) ∧
  compile_op x = x`
val _ = export_rewrites["compile_op_def"];

val mk_const_def = Define `
  mk_const n : bvl$exp = Op (Const (&n)) []`;

val mk_label_def = Define `
  mk_label n : bvl$exp = Op (Label n) []`;

val mk_el_def = Define `
  mk_el b i : bvl$exp = Op El [i; b]`;

val _ = export_rewrites ["mk_const_def", "mk_label_def", "mk_el_def"];

val free_let_def = Define `
  free_let cl n = (GENLIST (\n. mk_el cl (mk_const (n+2))) n)`;

val code_for_recc_case_def = Define `
  code_for_recc_case n num_args (c:bvl$exp) =
    (num_args + 1,
     Let [mk_el (Var num_args) (mk_const 2)]
      (Let (GENLIST (\a. Var (a + 1)) num_args ++ GENLIST (\i. Op Deref [mk_const i; Var 0]) n) c))`;

val build_aux_def = Define `
  (build_aux i [] aux = (i:num,aux)) /\
  (build_aux i ((x:num#bvl$exp)::xs) aux = build_aux (i+1) xs ((i,x) :: aux))`;

val build_aux_acc = store_thm("build_aux_acc",
  ``!k n aux.
    ?aux1. SND (build_aux n k aux) = aux1 ++ aux``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ fs [build_aux_def]
  \\ first_x_assum (STRIP_ASSUME_TAC o Q.SPECL [`n+1`,`(n,h)::aux`]) \\ rfs []);

val recc_Let_def = Define `
  recc_Let n num_args i =
    Let [mk_el (Var 0) (mk_const 2)]
     (Let [Op (Cons closure_tag) [Var 0; mk_const (num_args-1); mk_label n]]
       (Let [Op Update [Var 0; mk_const i; Var 1]]
         (Var 1 : bvl$exp)))`;

val recc_Lets_def = Define `
  recc_Lets n nargs k rest =
    if k = 0:num then rest else
      let k = k - 1 in
        Let [recc_Let (n + k) (HD nargs) k] (recc_Lets n (TL nargs) k rest)`;

val recc_Let0_def = Define `
  recc_Let0 n num_args i =
    Let [Op (Cons closure_tag) [Var 0; mk_const (num_args-1); mk_label n]]
      (Let [Op Update [Var 0; mk_const i; Var 1]] (Var 1 : bvl$exp))`;

val build_recc_lets_def = Define `
  build_recc_lets (nargs:num list) vs n1 fns_l (c3:bvl$exp) =
    Let [Let [Op Ref (REVERSE (MAP (K (mk_const 0)) nargs ++ MAP Var vs))]
           (recc_Let0 (n1 + (fns_l - 1)) (HD (REVERSE nargs)) (fns_l - 1))]
      (recc_Lets n1 (TL (REVERSE nargs)) (fns_l - 1) c3)`;

val num_stubs_def = Define `
  num_stubs = max_app * max_app + max_app`;

val mk_cl_call_def = Define `
  mk_cl_call cl args =
    If (Op Equal [mk_const (LENGTH args - 1); mk_el cl (mk_const 1)])
       (Call (LENGTH args - 1) NONE (args ++ [cl] ++ [mk_el cl (mk_const 0)]))
       (Call 0 (SOME (LENGTH args - 1)) (args ++ [cl]))`;

val partial_app_fn_location_def = Define `
  partial_app_fn_location m n = max_app + max_app * m + n`;

val mk_tick_def = Define `
  mk_tick n e = FUNPOW Tick n e : bvl$exp`;

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
                   (mk_cl_call (Var 0) (GENLIST (\n. Var (n + 3)) (n - num_args))))
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
    Let [mk_el (Var (total_args - prev_args)) (mk_const 2)]
      (Call 0
        NONE
        (GENLIST (\this_arg. Var (this_arg + 1)) (total_args - prev_args) ++
         GENLIST (\prev_arg.
           mk_el (Var (total_args - prev_args + 1)) (mk_const (prev_arg + 3))) (prev_args + 1) ++
         [Var 0] ++
         [mk_el (Var 0) (mk_const 0)]))`;

val init_code_def = Define `
  init_code =
    sptree$fromList
      (GENLIST (\n. (n + 2, generate_generic_app n)) max_app ++
       FLAT (GENLIST (\m. GENLIST (\n. (m - n + 1,
                                     generate_partial_app_closure_fn m n)) max_app) max_app))`;

val compile_def = tDefine "compile" `
  (compile [] aux = ([],aux)) /\
  (compile ((x:closLang$exp)::y::xs) aux =
     let (c1,aux1) = compile [x] aux in
     let (c2,aux2) = compile (y::xs) aux1 in
       (c1 ++ c2, aux2)) /\
  (compile [Var v] aux = ([(Var v):bvl$exp], aux)) /\
  (compile [If x1 x2 x3] aux =
     let (c1,aux1) = compile [x1] aux in
     let (c2,aux2) = compile [x2] aux1 in
     let (c3,aux3) = compile [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3)) /\
  (compile [Let xs x2] aux =
     let (c1,aux1) = compile xs aux in
     let (c2,aux2) = compile [x2] aux1 in
       ([Let c1 (HD c2)], aux2)) /\
  (compile [Raise x1] aux =
     let (c1,aux1) = compile [x1] aux in
       ([Raise (HD c1)], aux1)) /\
  (compile [Tick x1] aux =
     let (c1,aux1) = compile [x1] aux in
       ([Tick (HD c1)], aux1)) /\
  (compile [Op op xs] aux =
     let (c1,aux1) = compile xs aux in
       ([Op (compile_op op) c1],aux1)) /\
  (compile [App loc_opt x1 xs2] aux =
     let (c1,aux1) = compile [x1] aux in
     let (c2,aux2) = compile xs2 aux1 in
       ([case loc_opt of
         | NONE => 
             Let (c2++c1) (mk_cl_call (Var (LENGTH c2)) (GENLIST Var (LENGTH c2)))
         | SOME loc => 
             (Call (LENGTH c2 - 1) (SOME (loc + num_stubs)) (c2 ++ c1))],
        aux2)) /\
  (compile [Fn loc vs num_args x1] aux =
     let (c1,aux1) = compile [x1] aux in
     let c2 = 
       Let (GENLIST Var num_args ++ free_let (Var num_args) (LENGTH vs)) 
           (HD c1) 
     in
       ([Op (Cons closure_tag)
            (REVERSE (mk_label (loc + num_stubs) :: mk_const (num_args - 1) :: MAP Var vs))],
        (loc + num_stubs,num_args+1,c2) :: aux1)) /\
  (compile [Letrec loc vs fns x1] aux =
     case fns of
     | [] => compile [x1] aux
     | [(num_args, exp)] =>
         let (c1,aux1) = compile [exp] aux in
         let c3 = Let (GENLIST Var num_args ++ [Var num_args] ++ free_let (Var num_args) (LENGTH vs)) (HD c1) in
         let (c2,aux2) = compile [x1] ((loc + num_stubs,num_args+1,c3)::aux1) in
         let c4 = 
           Op (Cons closure_tag) 
              (REVERSE (mk_label (loc + num_stubs) :: mk_const (num_args - 1) :: MAP Var vs)) 
         in
           ([Let [c4] (HD c2)], aux2)
     | _ =>
         let fns_l = LENGTH fns in
         let l = fns_l + LENGTH vs in
         let (cs,aux1) = compile (MAP SND fns) aux in
         let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs in
         let (n2,aux2) = build_aux (loc + num_stubs) cs1 aux1 in
         let (c3,aux3) = compile [x1] aux2 in
         let c4 = build_recc_lets (MAP FST fns) vs (loc + num_stubs) fns_l (HD c3) in
           ([c4],aux3)) /\
  (compile [Handle x1 x2] aux =
     let (c1,aux1) = compile [x1] aux in
     let (c2,aux2) = compile [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2)) /\
  (compile [Call dest xs] aux =
     let (c1,aux1) = compile xs aux in
       ([Call 0 (SOME (dest + num_stubs)) c1],aux1))`
  (WF_REL_TAC `measure (exp3_size o FST)` >>
   srw_tac [ARITH_ss] [closLangTheory.exp_size_def] >>
   `!l. closLang$exp3_size (MAP SND l) <= exp1_size l`
            by (Induct_on `l` >>
                rw [closLangTheory.exp_size_def] >>
                PairCases_on `h` >>
                full_simp_tac (srw_ss()++ARITH_ss) [closLangTheory.exp_size_def]) >>
  pop_assum (qspec_then `v7` assume_tac) >>
  decide_tac);

val _ = export_theory()
