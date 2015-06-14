open preamble closLangTheory bvlTheory bvl_jumpTheory;
local open conLangTheory pat_to_closTheory in (* for list tags *) end;

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

val build_aux_LENGTH = store_thm("build_aux_LENGTH",
  ``!l n aux n1 t.
      (build_aux n l aux = (n1,t)) ==> (n1 = n + LENGTH l)``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

val build_aux_MOVE = store_thm("build_aux_MOVE",
  ``!xs n aux n1 aux1.
      (build_aux n xs aux = (n1,aux1)) <=>
      ?aux2. (build_aux n xs [] = (n1,aux2)) /\ (aux1 = aux2 ++ aux)``,
  Induct THEN1 (fs [build_aux_def] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [build_aux_def]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ fs [PULL_EXISTS]);

val build_aux_acc = Q.store_thm("build_aux_acc",
  `!k n aux. ?aux1. SND (build_aux n k aux) = aux1 ++ aux`,
  METIS_TAC[build_aux_MOVE,SND,PAIR]);

val build_aux_MEM = store_thm("build_aux_MEM",
  ``!c n aux n7 aux7.
       (build_aux n c aux = (n7,aux7)) ==>
       !k. k < LENGTH c ==> ?d. MEM (n + k,d) aux7``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+1`,`(n,h)::aux`]) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `k` \\ fs []
  THEN1 (MP_TAC (Q.SPECL [`c`,`n+1`,`(n,h)::aux`] build_aux_acc) \\ fs []
         \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [])
  \\ RES_TAC \\ fs [ADD1,AC ADD_COMM ADD_ASSOC] \\ METIS_TAC [ADD_COMM, ADD_ASSOC]);

val build_aux_APPEND1 = store_thm("build_aux_APPEND1",
  ``!xs x n aux.
      build_aux n (xs ++ [x]) aux =
        let (n1,aux1) = build_aux n xs aux in
          (n1+1,(n1,x)::aux1)``,
  Induct \\ fs [build_aux_def,LET_DEF]);

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
  num_stubs =
    (* generic apps *)         max_app
    (* partial apps *)       + max_app * max_app
    (* equality of values *) + 1
    (* equality of blocks *) + 1
    (* ToList *)             + 1`;

val equality_location_def = Define`
  equality_location = max_app + max_app * max_app`;

val block_equality_location_def = Define`
  block_equality_location = equality_location + 1`;

val ToList_location_def = Define`
  ToList_location = block_equality_location + 1`;

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

val ToList_code_def = Define`
  (* 3 arguments: block containing list, index of last converted element, accumulator *)
  ToList_code =
    If (Op Equal [Var 1; mk_const 0]) (Var 2)
      (Let [Op Sub [Var 1; mk_const 1]]
        (Call 0 (SOME ToList_location)
         [Var 1; Var 0; Op (Cons (cons_tag+pat_tag_shift+clos_tag_shift))
                           [mk_el (Var 0) (Var 1); (Var 3)]]))`;

val Bool_def = Define`
  Bool b = Op (Cons ((if b then true_tag else false_tag)+pat_tag_shift+clos_tag_shift)) []`;

val RaiseEq_def = Define`
  RaiseEq = Raise (Op (Cons (eq_tag+pat_tag_shift+clos_tag_shift)) [])`;

val check_closure_def = Define`
  check_closure v = If (Op (TagEq closure_tag) [Var v]) RaiseEq
                       (If (Op (TagEq partial_app_tag) [Var v]) RaiseEq
                           (Bool F))`;

val equality_code_def = Define`
  equality_code =
    If (Op IsBlock [Var 0])
       (If (Op IsBlock [Var 1])
           (If (Op BlockCmp [Var 0; Var 1])
               (Call 0 (SOME block_equality_location)
                 [Var 0; Var 1; Op LengthBlock [Var 0]; mk_const 0])
               (Bool F))
           (check_closure 0))
       (If (Op IsBlock [Var 1])
           (check_closure 1)
           (Op Equal [Var 0; Var 1]))`;

val block_equality_code_def = Define`
  (* 4 arguments: block1, block2, length, last checked index *)
  block_equality_code =
    If (Op Equal [Var 3; Var 2])
       (Bool T)
       (Let [Op Add [Var 3; mk_const 1]]
         (If (Call 0 (SOME equality_location)
                [mk_el (Var 1) (Var 0);
                 mk_el (Var 2) (Var 0)])
             (Call 0 (SOME block_equality_location)
                [Var 1; Var 2; Var 3; Var 0])
             (Bool F)))`;

val init_code_def = Define `
  init_code =
    sptree$fromList
      (GENLIST (\n. (n + 2, generate_generic_app n)) max_app ++
       FLAT (GENLIST (\m. GENLIST (\n. (m - n + 1,
                                     generate_partial_app_closure_fn m n)) max_app) max_app) ++
       [(2,equality_code);
        (4,block_equality_code);
        (3,ToList_code)])`;

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
     ([if op = ToList then
         Let c1
           (Call 0 (SOME ToList_location)
             [Var 0; Op(LengthBlock)[Var 0];
              Op(Cons(nil_tag+pat_tag_shift+clos_tag_shift))[]])
       else if op = Equal then
         Call 0 (SOME equality_location) c1
       else
         Op (compile_op op) c1]
     ,aux1)) /\
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

val compile_ind = theorem"compile_ind";

val pair_lem1 = Q.prove (
  `!f x. (\(a,b). f a b) x = f (FST x) (SND x)`,
  rw [] >>
  PairCases_on `x` >>
  fs []);

val pair_lem2 = Q.prove (
  `!x y z. (x,y) = z ⇔ x = FST z ∧ y = SND z`,
  rw [] >>
  PairCases_on `z` >>
  rw []);

val compile_acc = Q.store_thm("compile_acc",
  `!xs aux.
      let (c,aux1) = compile xs aux in
        (LENGTH c = LENGTH xs) /\ ?ys. aux1 = ys ++ aux`,
  recInduct compile_ind \\ REPEAT STRIP_TAC
  \\ fs [compile_def] \\ SRW_TAC [] [] \\ fs [LET_DEF,ADD1]
  \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ BasicProvers.EVERY_CASE_TAC \\ rfs [] \\ fs [pair_lem1] >>
  rw [] >>
  fs [pair_lem2] >>
  rfs [compile_def, LET_THM] >>
  fs [pair_lem1, pair_lem2] >>
  metis_tac [build_aux_acc, APPEND_ASSOC]);

val compile_LENGTH = Q.store_thm("compile_LENGTH",
  `(compile xs aux = (c,aux1)) ==> (LENGTH c = LENGTH xs)`,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`xs`,`aux`] compile_acc)
  \\ rfs [LET_DEF]);

val compile_SING = Q.store_thm("compile_SING",
  `(compile [x] aux = (c,aux1)) ==> ?d. c = [d]`,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`[x]`,`aux`] compile_acc) \\ rfs [LET_DEF]
  \\ Cases_on `c` \\ fs [] \\ Cases_on `t` \\ fs []);

val compile_CONS = store_thm("compile_CONS",
  ``!xs x aux.
      compile (x::xs) aux =
      (let (c1,aux1) = compile [x] aux in
       let (c2,aux2) = compile xs aux1 in
         (c1 ++ c2,aux2))``,
  Cases_on `xs` \\ fs[compile_def] \\ fs [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val compile_SNOC = store_thm("compile_SNOC",
  ``!xs x aux.
      compile (SNOC x xs) aux =
      (let (c1,aux1) = compile xs aux in
       let (c2,aux2) = compile [x] aux1 in
         (c1 ++ c2,aux2))``,
  Induct THEN1
   (fs [compile_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ ONCE_REWRITE_TAC [compile_CONS]
  \\ ASM_SIMP_TAC std_ss [compile_def,LET_DEF,APPEND_NIL]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val _ = export_theory()
