open preamble closLangTheory bvlTheory bvl_jumpTheory;
open backend_commonTheory
local open
  clos_mtiTheory
  clos_callTheory
  clos_knownTheory
  clos_removeTheory
  clos_numberTheory
  clos_annotateTheory
in (* clos-to-clos transformations *) end;

val _ = new_theory "clos_to_bvl";
val _ = set_grammar_ancestry [
  "backend_common",
  "clos_mti", "clos_call", "clos_known", "clos_remove", "clos_number",
  "clos_annotate",
  "bvl_jump"
]

val closure_tag_def = Define`closure_tag = 30:num`
val partial_app_tag_def = Define`partial_app_tag = 31:num`
val clos_tag_shift_def = Define`clos_tag_shift tag = if tag < 30 then tag:num else tag+2`
val _ = EVAL``partial_app_tag = closure_tag`` |> EQF_ELIM
  |> curry save_thm"partial_app_tag_neq_closure_tag[simp]";
val _ = EVAL``clos_tag_shift nil_tag = nil_tag`` |> EQT_ELIM
  |> curry save_thm"clos_tag_shift_nil_tag[simp]";
val _ = EVAL``clos_tag_shift cons_tag = cons_tag`` |> EQT_ELIM
  |> curry save_thm"clos_tag_shift_cons_tag[simp]";
val clos_tag_shift_inj = Q.store_thm("clos_tag_shift_inj",
  `clos_tag_shift n1 = clos_tag_shift n2 ⇒ n1 = n2`,
  EVAL_TAC >> rw[] >> simp[])

val compile_op_def = Define`
  compile_op (Cons tag) = (Cons (clos_tag_shift tag)) ∧
  compile_op (TagEq tag) = (TagEq (clos_tag_shift tag)) ∧
  compile_op (TagLenEq tag a) = (TagLenEq (clos_tag_shift tag) a) ∧
  compile_op (FromList tag) = (FromList (clos_tag_shift tag)) ∧
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
  (build_aux i ((x:num#bvl$exp)::xs) aux = build_aux (i+2) xs ((i,x) :: aux))`;

val build_aux_LENGTH = store_thm("build_aux_LENGTH",
  ``!l n aux n1 t.
      (build_aux n l aux = (n1,t)) ==> (n1 = n + 2 * LENGTH l)``,
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
       !k. k < LENGTH c ==> ?d. MEM (n + 2*k,d) aux7``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`(n,h)::aux`]) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `k` \\ fs []
  THEN1 (MP_TAC (Q.SPECL [`c`,`n+2`,`(n,h)::aux`] build_aux_acc) \\ fs []
         \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [])
  \\ RES_TAC \\ fs [ADD1,LEFT_ADD_DISTRIB] \\ METIS_TAC []);

val build_aux_APPEND1 = store_thm("build_aux_APPEND1",
  ``!xs x n aux.
      build_aux n (xs ++ [x]) aux =
        let (n1,aux1) = build_aux n xs aux in
          (n1+2,(n1,x)::aux1)``,
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
        Let [recc_Let (n + 2*k) (HD nargs) k] (recc_Lets n (TL nargs) k rest)`;

val recc_Let0_def = Define `
  recc_Let0 n num_args i =
    Let [Op (Cons closure_tag) [Var 0; mk_const (num_args-1); mk_label n]]
      (Let [Op Update [Var 0; mk_const i; Var 1]] (Var 1 : bvl$exp))`;

val build_recc_lets_def = Define `
  build_recc_lets (nargs:num list) vs n1 fns_l (c3:bvl$exp) =
    Let [Let [Op Ref (REVERSE (MAP (K (mk_const 0)) nargs ++ MAP Var vs))]
           (recc_Let0 (n1 + (2 * (fns_l - 1))) (HD (REVERSE nargs)) (fns_l - 1))]
      (recc_Lets n1 (TL (REVERSE nargs)) (fns_l - 1) c3)`;

val num_stubs_def = Define `
  num_stubs max_app =
    (* generic apps *)         max_app
    (* partial apps *)       + max_app * max_app
    (* equality of values *) + 1n
    (* equality of blocks *) + 1
    (* ToList *)             + 1`;

val equality_location_def = Define`
  equality_location (max_app:num) = max_app + max_app * max_app`;

val block_equality_location_def = Define`
  block_equality_location max_app = equality_location max_app + 1`;

val ToList_location_def = Define`
  ToList_location max_app = block_equality_location max_app + 1`;

val mk_cl_call_def = Define `
  mk_cl_call cl args =
    If (Op Equal [mk_const (LENGTH args - 1); mk_el cl (mk_const 1)])
       (Call (LENGTH args - 1) NONE (args ++ [cl] ++ [mk_el cl (mk_const 0)]))
       (Call 0 (SOME (LENGTH args - 1)) (args ++ [cl]))`;

val partial_app_fn_location_def = Define `
  partial_app_fn_location (max_app:num) m n = max_app + max_app * m + n`;

(* Generic application of a function to n+1 arguments *)
val generate_generic_app_def = Define `
  generate_generic_app max_app n =
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
                          mk_label (partial_app_fn_location max_app total_args n))
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
                              mk_label (partial_app_fn_location max_app total_args (n + prev_args + 1)))
                             max_app) ::
                          Var 1 ::
                          mk_el (Var (n+3)) (mk_const 2) ::
                          GENLIST (\this_arg. Var (this_arg + 2)) (n+1) ++
                          GENLIST (\prev_arg.
                            mk_el (Var (n+3)) (mk_const (prev_arg + 3))) (prev_args + 1))))
                    (max_app-(n+1)))))))`;

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
  ToList_code max_app = (3:num,
    If (Op Equal [Var 1; mk_const 0]) (Var 2)
      (Let [Op Sub [mk_const 1; Var 1]]
        (Call 0 (SOME (ToList_location max_app))
         [Var 1; Var 0; Op (Cons cons_tag)
                           [Var 3; mk_el (Var 1) (Var 0)]])))`;

val check_closure_def = Define`
  check_closure v e =
    If (Op (TagEq closure_tag) [Var v]) (Bool T)
      (If (Op (TagEq partial_app_tag) [Var v]) (Bool T) e)`;

val equality_code_def = Define`
  equality_code max_app = (2:num,
    If (Op IsBlock [Var 0])
       (check_closure 0
         (check_closure 1
           (If (Op BlockCmp [Var 0; Var 1])
               (Call 0 (SOME (block_equality_location max_app))
                 [Var 0; Var 1; Op LengthBlock [Var 0]; mk_const 0])
               (Bool F))))
       (Op Equal [Var 0; Var 1]))`;

val block_equality_code_def = Define`
  (* 4 arguments: block1, block2, length, index to check*)
  block_equality_code max_app = (4:num,
    If (Op Equal [Var 3; Var 2])
       (Bool T)
       (If (Call 0 (SOME (equality_location max_app))
              [mk_el (Var 0) (Var 3);
               mk_el (Var 1) (Var 3)])
           (Call 0 (SOME (block_equality_location max_app))
              [Var 0; Var 1; Var 2; (Op Add [Var 3; mk_const 1])])
           (Bool F)))`;

val init_code_def = Define `
  init_code max_app =
    sptree$fromList
      (GENLIST (\n. (n + 2, generate_generic_app max_app n)) max_app ++
               FLAT (GENLIST (\m. GENLIST (\n. (m - n + 1,
                                     generate_partial_app_closure_fn m n)) max_app) max_app) ++
       [equality_code max_app;
        block_equality_code max_app;
        ToList_code max_app])`;

val compile_exps_def = tDefine "compile_exps" `
  (compile_exps max_app [] aux = ([],aux)) /\
  (compile_exps max_app ((x:closLang$exp)::y::xs) aux =
     let (c1,aux1) = compile_exps max_app [x] aux in
     let (c2,aux2) = compile_exps max_app (y::xs) aux1 in
       (c1 ++ c2, aux2)) /\
  (compile_exps max_app [Var v] aux = ([(Var v):bvl$exp], aux)) /\
  (compile_exps max_app [If x1 x2 x3] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let (c2,aux2) = compile_exps max_app [x2] aux1 in
     let (c3,aux3) = compile_exps max_app [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3)) /\
  (compile_exps max_app [Let xs x2] aux =
     let (c1,aux1) = compile_exps max_app xs aux in
     let (c2,aux2) = compile_exps max_app [x2] aux1 in
       ([Let c1 (HD c2)], aux2)) /\
  (compile_exps max_app [Raise x1] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
       ([Raise (HD c1)], aux1)) /\
  (compile_exps max_app [Tick x1] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
       ([Tick (HD c1)], aux1)) /\
  (compile_exps max_app [Op op xs] aux =
     let (c1,aux1) = compile_exps max_app xs aux in
     ([if op = ToList then
         Let c1
           (Call 0 (SOME (ToList_location max_app))
             [Var 0; Op(LengthBlock)[Var 0];
              Op(Cons nil_tag)[]])
       else if op = Equal then
         Call 0 (SOME (equality_location max_app)) c1
       else
         Op (compile_op op) c1]
     ,aux1)) /\
  (compile_exps max_app [App loc_opt x1 xs2] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let (c2,aux2) = compile_exps max_app xs2 aux1 in
       ([case loc_opt of
         | NONE =>
             Let (c2++c1) (mk_cl_call (Var (LENGTH c2)) (GENLIST Var (LENGTH c2)))
         | SOME loc =>
             (Call (LENGTH c2 - 1) (SOME (loc + (num_stubs max_app))) (c2 ++ c1))],
        aux2)) /\
  (compile_exps max_app [Fn loc_opt vs_opt num_args x1] aux =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let vs = case vs_opt of NONE => [] | SOME vs => vs in
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let c2 =
       Let (GENLIST Var num_args ++ free_let (Var num_args) (LENGTH vs))
           (HD c1)
     in
       ([Op (Cons closure_tag)
            (REVERSE (mk_label (loc + num_stubs max_app) :: mk_const (num_args - 1) :: MAP Var vs))],
        (loc + (num_stubs max_app),num_args+1,c2) :: aux1)) /\
  (compile_exps max_app [Letrec loc_opt vsopt fns x1] aux =
     let loc = case loc_opt of NONE => 0 | SOME n => n in
     let vs = case vsopt of NONE => [] | SOME x => x in
     case fns of
     | [] => compile_exps max_app [x1] aux
     | [(num_args, exp)] =>
         let (c1,aux1) = compile_exps max_app [exp] aux in
         let c3 = Let (GENLIST Var num_args ++ [Var num_args] ++ free_let (Var num_args) (LENGTH vs)) (HD c1) in
         let (c2,aux2) = compile_exps max_app [x1] ((loc + (num_stubs max_app),num_args+1,c3)::aux1) in
         let c4 =
           Op (Cons closure_tag)
              (REVERSE (mk_label (loc + (num_stubs max_app)) :: mk_const (num_args - 1) :: MAP Var vs))
         in
           ([Let [c4] (HD c2)], aux2)
     | _ =>
         let fns_l = LENGTH fns in
         let l = fns_l + LENGTH vs in
         let (cs,aux1) = compile_exps max_app (MAP SND fns) aux in
         let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs in
         let (n2,aux2) = build_aux (loc + (num_stubs max_app)) cs1 aux1 in
         let (c3,aux3) = compile_exps max_app [x1] aux2 in
         let c4 = build_recc_lets (MAP FST fns) vs (loc + (num_stubs max_app)) fns_l (HD c3) in
           ([c4],aux3)) /\
  (compile_exps max_app [Handle x1 x2] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let (c2,aux2) = compile_exps max_app [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2)) /\
  (compile_exps max_app [Call ticks dest xs] aux =
     let (c1,aux1) = compile_exps max_app xs aux in
       ([Call ticks (SOME (dest + (num_stubs max_app))) c1],aux1))`
  (WF_REL_TAC `measure (exp3_size o FST o SND)` >>
   srw_tac [ARITH_ss] [closLangTheory.exp_size_def] >>
   `!l. closLang$exp3_size (MAP SND l) <= exp1_size l`
            by (Induct_on `l` >>
                rw [closLangTheory.exp_size_def] >>
                PairCases_on `h` >>
                full_simp_tac (srw_ss()++ARITH_ss) [closLangTheory.exp_size_def]) >>
  pop_assum (qspec_then `v7` assume_tac) >>
  decide_tac);

val compile_exps_ind = theorem"compile_exps_ind";

val compile_prog_def = Define `
  (compile_prog max_app [] = []) /\
  (compile_prog max_app ((n,args,e)::xs) =
     let (new_e,aux) = compile_exps max_app [e] [] in
       (* with this approach the supporting functions (aux) are
          close the expressions (new_e) that refers to them *)
       MAP (\e. (n + (num_stubs max_app),args,e)) new_e ++ aux ++ compile_prog max_app xs)`

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

val compile_exps_acc = Q.store_thm("compile_exps_acc",
  `!max_app xs aux.
      let (c,aux1) = compile_exps max_app xs aux in
        (LENGTH c = LENGTH xs) /\ ?ys. aux1 = ys ++ aux`,
  recInduct compile_exps_ind \\ REPEAT STRIP_TAC
  \\ fs [compile_exps_def] \\ SRW_TAC [] [] \\ fs [LET_DEF,ADD1]
  \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ BasicProvers.EVERY_CASE_TAC \\ rfs [] \\ fs [pair_lem1] >>
  rw [] >>
  fs [pair_lem2] >>
  rfs [compile_exps_def, LET_THM] >>
  fs [pair_lem1, pair_lem2] >>
  metis_tac [build_aux_acc, APPEND_ASSOC]);

val compile_exps_LENGTH = Q.store_thm("compile_exps_LENGTH",
  `(compile_exps max_app xs aux = (c,aux1)) ==> (LENGTH c = LENGTH xs)`,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`max_app`,`xs`,`aux`] compile_exps_acc)
  \\ rfs [LET_DEF]);

val compile_exps_SING = Q.store_thm("compile_exps_SING",
  `(compile_exps max_app [x] aux = (c,aux1)) ==> ?d. c = [d]`,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`max_app`,`[x]`,`aux`] compile_exps_acc) \\ rfs [LET_DEF]
  \\ Cases_on `c` \\ fs [] \\ Cases_on `t` \\ fs []);

val compile_exps_CONS = store_thm("compile_exps_CONS",
  ``!max_app xs x aux.
      compile_exps max_app (x::xs) aux =
      (let (c1,aux1) = compile_exps max_app [x] aux in
       let (c2,aux2) = compile_exps max_app xs aux1 in
         (c1 ++ c2,aux2))``,
  Cases_on `xs` \\ fs[compile_exps_def] \\ fs [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val compile_exps_SNOC = store_thm("compile_exps_SNOC",
  ``!xs x aux max_app.
      compile_exps max_app (SNOC x xs) aux =
      (let (c1,aux1) = compile_exps max_app xs aux in
       let (c2,aux2) = compile_exps max_app [x] aux1 in
         (c1 ++ c2,aux2))``,
  Induct THEN1
   (fs [compile_exps_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ ONCE_REWRITE_TAC [compile_exps_CONS]
  \\ ASM_SIMP_TAC std_ss [compile_exps_def,LET_DEF,APPEND_NIL]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val _ = Datatype`
  config = <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; do_known : bool
            ; do_call : bool
            ; do_remove : bool
            ; max_app : num
            |>`;

val default_config_def = Define`
  default_config = <|
    next_loc := 0;
    start := 1;
    do_mti := T;
    do_known := T;
    do_call := T;
    do_remove := T;
    max_app := 4 |>`;

val code_split_def = Define `
  (code_split [] xs ys = (xs,ys)) /\
  (code_split (z::zs) xs ys = code_split zs (z::ys) xs)`;

val code_merge_def = tDefine "code_merge" `
  code_merge xs ys =
    case (xs,ys) of
    | ([],[]) => []
    | ([],_) => ys
    | (_,[]) => xs
    | (x1::xs1,y1::ys1) =>
        if FST x1 < (FST y1):num then
          x1::code_merge xs1 ys
        else
          y1::code_merge xs ys1`
  (WF_REL_TAC `measure (\(xs,ys). LENGTH xs + LENGTH ys)` \\ rw []);

val code_split_NULL = store_thm("code_split_NULL",
  ``!ts1 ts2 ts3 xs ys.
      (xs,ys) = code_split ts1 ts2 ts3 /\ ts2 <> [] /\ ts3 <> [] ==>
      xs <> [] /\ ys <> []``,
  Induct \\ fs [code_split_def] \\ rw [] \\ first_x_assum drule \\ fs []);

val code_split_LENGTH = store_thm("code_split_LENGTH",
  ``!ts1 ts2 ts3 xs ys.
      (xs,ys) = code_split ts1 ts2 ts3 ==>
      LENGTH xs + LENGTH ys = LENGTH ts1 + LENGTH ts2 + LENGTH ts3``,
  Induct \\ fs [code_split_def] \\ rw [] \\ first_x_assum drule \\ fs []);

val code_sort_def = tDefine "code_sort" `
  (code_sort [] = []) /\
  (code_sort [x] = [x]) /\
  (code_sort (x::y::xs) =
     let (xs,ys) = code_split xs [x] [y] in
       code_merge (code_sort xs) (code_sort ys))`
 (WF_REL_TAC `measure LENGTH` \\ rw []
  \\ imp_res_tac code_split_LENGTH
  \\ drule code_split_NULL \\ fs [GSYM LENGTH_NIL]);

val compile_def = Define`
  compile c e =
    let es = clos_mti$compile c.do_mti c.max_app [e] in
    let (n,es) = renumber_code_locs_list (num_stubs c.max_app + 1) es in
    let c = c with next_loc := n in
    let e = clos_known$compile c.do_known (HD es) in
    let (e,aux) = clos_call$compile c.do_call e in
    let prog = (1,0,e) :: aux in
    let c = c with start := num_stubs c.max_app + 1 in
    let prog = clos_remove$compile c.do_remove prog in
    let prog = clos_annotate$compile prog in
    let prog = compile_prog c.max_app prog in
    let prog = toAList (init_code c.max_app) ++ prog in
      (c,code_sort prog)`;

val _ = export_theory()
