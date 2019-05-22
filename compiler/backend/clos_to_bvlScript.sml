(*
  This compiler phase performs closure conversion.  This phase puts
  all of the code into a table of first-order, closed, multi-argument
  functions.

  The table is indexed by natural numbers, and each entry
  is a pair of a number (the function's arity) and a BVL expression
  (the function's body). The table has the following layout.

  Entry i in the range 0 to max_app - 1 (inclusive):
    generic application of a closure to i+1 arguments. Takes i+2 arguments
    (the arguments and the closure). The closure might expect more or less
    than i+1 arguments, and this code would then allocate a partial application
    closure, or make repeated applications.

  Entries in the range max_app to max_app + (max_app * (max_app - 1) DIV 2) - 1 (inclusive) :
    code to fully apply a partially applied closure wrapper.
    For a closure expecting tot number of arguments, which has already been
    given prev number of arguments, the wrapper is in location
    max_app + tot * (tot - 1) DIV 2 + prev
    and takes tot - prev + 1 arguments

  The next entry initialises a global variable that contains a jump table used
  by the generic application stubs (0 argument).

  The num_stubs function gives the total number of these functions.

  Starting at index num_stubs, there are 0 argument functions that evaluate
  each expression that should be evaluated, and then call the next function.

  Following these functions, at even numbers there are the bodies of
  functions in the program, with one extra argument for the closure value to be
  passed in to them. The odd entries are the bodies of the functions that have
  no free variables, and so they don't have any extra arguments. Their
  correcponding odd entries just indirect to the even ones. (clos_call)
  One entry might be skipped in between the expressions and the source-level
  function bodies to get the alignment right.

*)
open preamble closLangTheory bvlTheory bvl_jumpTheory;
open backend_commonTheory
local open
  clos_mtiTheory
  clos_callTheory
  clos_knownTheory
  clos_numberTheory
  clos_annotateTheory
  clos_labelsTheory
in (* clos-to-clos transformations *) end;

val _ = new_theory "clos_to_bvl";
val _ = set_grammar_ancestry [
  "backend_common",
  "clos_mti", "clos_call", "clos_known", "clos_number",
  "clos_annotate",
  "bvl_jump"
]

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = EVAL``partial_app_tag = closure_tag`` |> EQF_ELIM
  |> curry save_thm"partial_app_tag_neq_closure_tag[simp]";
val _ = EVAL``clos_tag_shift nil_tag = nil_tag`` |> EQT_ELIM
  |> curry save_thm"clos_tag_shift_nil_tag[simp]";
val _ = EVAL``clos_tag_shift cons_tag = cons_tag`` |> EQT_ELIM
  |> curry save_thm"clos_tag_shift_cons_tag[simp]";
Theorem clos_tag_shift_inj:
   clos_tag_shift n1 = clos_tag_shift n2 ⇒ n1 = n2
Proof
  EVAL_TAC >> rw[] >> simp[]
QED

val num_added_globals_def = Define
  `num_added_globals = 1n`;

val partial_app_label_table_loc_def = Define
  `partial_app_label_table_loc = 0n`;

val compile_op_def = Define`
  compile_op (Cons tag) = (Cons (clos_tag_shift tag)) ∧
  compile_op (ConsExtend tag) = (ConsExtend (clos_tag_shift tag)) ∧
  compile_op (TagEq tag) = (TagEq (clos_tag_shift tag)) ∧
  compile_op (TagLenEq tag a) = (TagLenEq (clos_tag_shift tag) a) ∧
  compile_op (FromList tag) = (FromList (clos_tag_shift tag)) ∧
  compile_op LengthByteVec = LengthByte ∧
  compile_op DerefByteVec = DerefByte ∧
  compile_op (SetGlobal n) = SetGlobal (n + num_added_globals) ∧
  compile_op (Global n) = Global (n + num_added_globals) ∧
  compile_op x = x`
val _ = export_rewrites["compile_op_def"];

Theorem compile_op_pmatch:
  ∀op.
  compile_op op =
    case op of
        Cons tag => Cons (clos_tag_shift tag)
      | ConsExtend tag => ConsExtend (clos_tag_shift tag)
      | TagEq tag => TagEq (clos_tag_shift tag)
      | TagLenEq tag a => TagLenEq (clos_tag_shift tag) a
      | FromList tag => FromList (clos_tag_shift tag)
      | LengthByteVec => LengthByte
      | DerefByteVec => DerefByte
      | SetGlobal n => SetGlobal (n + num_added_globals)
      | Global n => Global (n + num_added_globals)
      | x => x
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[compile_op_def]
QED

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

Theorem build_aux_LENGTH:
   !l n aux n1 t.
      (build_aux n l aux = (n1,t)) ==> (n1 = n + 2 * LENGTH l)
Proof
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC
QED

Theorem build_aux_MOVE:
   !xs n aux n1 aux1.
      (build_aux n xs aux = (n1,aux1)) <=>
      ?aux2. (build_aux n xs [] = (n1,aux2)) /\ (aux1 = aux2 ++ aux)
Proof
  Induct THEN1 (fs [build_aux_def] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [build_aux_def]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ fs [PULL_EXISTS]
QED

Theorem build_aux_acc:
   !k n aux. ?aux1. SND (build_aux n k aux) = aux1 ++ aux
Proof
  METIS_TAC[build_aux_MOVE,SND,PAIR]
QED

Theorem build_aux_MEM:
   !c n aux n7 aux7.
       (build_aux n c aux = (n7,aux7)) ==>
       !k. k < LENGTH c ==> ?d. MEM (n + 2*k,d) aux7
Proof
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`(n,h)::aux`]) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `k` \\ fs []
  THEN1 (MP_TAC (Q.SPECL [`c`,`n+2`,`(n,h)::aux`] build_aux_acc) \\ fs []
         \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [])
  \\ RES_TAC \\ fs [ADD1,LEFT_ADD_DISTRIB] \\ METIS_TAC []
QED

Theorem build_aux_APPEND1:
   !xs x n aux.
      build_aux n (xs ++ [x]) aux =
        let (n1,aux1) = build_aux n xs aux in
          (n1+2,(n1,x)::aux1)
Proof
  Induct \\ fs [build_aux_def,LET_DEF]
QED

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
    (* partial apps *)       + max_app * (max_app - 1) DIV 2
    + 1 (* code to install a jump table in global 0 *) `;

val generic_app_fn_location_def = Define `
  generic_app_fn_location n = n`;

val partial_app_fn_location_def = Define `
  partial_app_fn_location (max_app:num) tot prev =
    max_app + tot * (tot - 1) DIV 2 + prev`;

val partial_app_fn_location_code_def = Define `
  partial_app_fn_location_code max_app tot_exp prev_exp : bvl$exp =
    Let [tot_exp]
     (Op Add [prev_exp;
        Op Div [mk_const 2;
          Op Mult [Var 0; Op Sub [mk_const 1; Var 0]]]])`;

val mk_cl_call_def = Define `
  mk_cl_call cl args =
    If (Op Equal [mk_const (LENGTH args - 1); mk_el cl (mk_const 1)])
       (Call (LENGTH args - 1) NONE (args ++ [cl] ++ [mk_el cl (mk_const 0)]))
       (Call 0 (SOME (generic_app_fn_location (LENGTH args - 1))) (args ++ [cl]))`;

(* Generic application of a function to n+1 arguments *)
val generate_generic_app_def = Define `
  generate_generic_app max_app n =
    Let [Op Sub [mk_const (n+1); mk_el (Var (n+1)) (mk_const 1)]] (* The number of arguments remaining - 1 *)
        (If (Op Less [mk_const 0; Var 0])
            (* Over application *)
            (Jump (mk_el (Var (n+2)) (mk_const 1))
              (GENLIST (\num_args.
                 Let [Call num_args
                           NONE
                           (GENLIST (\arg. Var (arg + 2 + n - num_args)) (num_args + 1) ++
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
                      (mk_el (Op (Global 0) [])
                        (partial_app_fn_location_code max_app
                          (mk_el (Var (n+2)) (mk_const 1))
                          (mk_const n)) ::
                       Var 0 ::
                       Var (n + 2) ::
                       GENLIST (\n. Var (n + 1)) (n + 1))))
                (* Partial application of a partially applied closure *)
                (Let [Op Sub [mk_const 3; Op LengthBlock [Var (n+2)]]] (* The number of previous args *)
                  (Op (ConsExtend partial_app_tag)
                    (REVERSE
                      (Var (n + 3) ::
                       mk_const 3 ::
                       Var 0 ::
                       Op Add [Var 0; mk_const (n+4)] ::
                       mk_el (Op (Global 0) [])
                         (partial_app_fn_location_code max_app
                           (Op Add [Var 0; Op Add [mk_const (n + 1); Var 1]])
                           (* Shift from Var0 to Var1 because of Let in
                            * partial_app_fn_location_code *)
                           (Op Add [Var 1; mk_const n])) ::
                       Var 1 ::
                       mk_el (Var (n+3)) (mk_const 2) ::
                       GENLIST (\this_arg. Var (this_arg + 2)) (n + 1))))))))`;

(* The functions to complete the application of a partial closure.
 * We expect prev_args < total_args, also the function should take one more
 * argument than total, and have seen one more than prev (since there is
 * possiblity for a 0 argument function, or a partial application wrapper that
 * has seen no arguments yet. *)
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

val check_closure_def = Define`
  check_closure v e =
    If (Op (TagEq closure_tag) [Var v]) (Bool T)
      (If (Op (TagEq partial_app_tag) [Var v]) (Bool T) e)`;

val init_code_def = Define `
  init_code max_app =
    sptree$fromList
      (GENLIST (\n. (n + 2, generate_generic_app max_app n)) max_app ++
       FLAT
         (GENLIST
           (\tot.
             GENLIST
               (\prev. (tot - prev + 1, generate_partial_app_closure_fn tot prev))
               tot)
           max_app))`;

val init_globals_def = Define `
  init_globals max_app start_loc =
    Let [Op AllocGlobal []]
    (Let
      [Op (SetGlobal partial_app_label_table_loc)
        [Op (Cons tuple_tag)
          (REVERSE (FLAT
            (GENLIST
              (\tot.
                GENLIST
                  (\prev. mk_label (partial_app_fn_location max_app tot prev))
                  tot)
              max_app)))]]
      (* Expect the real start of the program in code location 3 *)
      (Call 0 (SOME start_loc) []))`;

val compile_exps_def = tDefine "compile_exps" `
  (compile_exps max_app [] aux = ([],aux)) /\
  (compile_exps max_app ((x:closLang$exp)::y::xs) aux =
     let (c1,aux1) = compile_exps max_app [x] aux in
     let (c2,aux2) = compile_exps max_app (y::xs) aux1 in
       (c1 ++ c2, aux2)) /\
  (compile_exps max_app [Var t v] aux = ([(Var v):bvl$exp], aux)) /\
  (compile_exps max_app [If t x1 x2 x3] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let (c2,aux2) = compile_exps max_app [x2] aux1 in
     let (c3,aux3) = compile_exps max_app [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3)) /\
  (compile_exps max_app [Let t xs x2] aux =
     let (c1,aux1) = compile_exps max_app xs aux in
     let (c2,aux2) = compile_exps max_app [x2] aux1 in
       ([Let c1 (HD c2)], aux2)) /\
  (compile_exps max_app [Raise t x1] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
       ([Raise (HD c1)], aux1)) /\
  (compile_exps max_app [Tick t x1] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
       ([Tick (HD c1)], aux1)) /\
  (compile_exps max_app [Op t op xs] aux =
     let (c1,aux1) = compile_exps max_app xs aux in
     ([if op = Install then
         Call 0 NONE [Op Install c1]
       else
         Op (compile_op op) c1]
     ,aux1)) /\
  (compile_exps max_app [App t loc_opt x1 xs2] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let (c2,aux2) = compile_exps max_app xs2 aux1 in
       ([dtcase loc_opt of
         | NONE =>
             Let (c2++c1) (mk_cl_call (Var (LENGTH c2)) (GENLIST Var (LENGTH c2)))
         | SOME loc =>
             (Call (LENGTH c2 - 1) (SOME (loc + (num_stubs max_app))) (c2 ++ c1))],
        aux2)) /\
  (compile_exps max_app [Fn t loc_opt vs_opt num_args x1] aux =
     let loc = dtcase loc_opt of NONE => 0 | SOME n => n in
     let vs = dtcase vs_opt of NONE => [] | SOME vs => vs in
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let c2 =
       Let (GENLIST Var num_args ++ free_let (Var num_args) (LENGTH vs))
           (HD c1)
     in
       ([Op (Cons closure_tag)
            (REVERSE (mk_label (loc + num_stubs max_app) :: mk_const (num_args - 1) :: MAP Var vs))],
        (loc + (num_stubs max_app),num_args+1,c2) :: aux1)) /\
  (compile_exps max_app [Letrec t loc_opt vsopt fns x1] aux =
     let loc = dtcase loc_opt of NONE => 0 | SOME n => n in
     let vs = dtcase vsopt of NONE => [] | SOME x => x in
     dtcase fns of
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
  (compile_exps max_app [Handle t x1 x2] aux =
     let (c1,aux1) = compile_exps max_app [x1] aux in
     let (c2,aux2) = compile_exps max_app [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2)) /\
  (compile_exps max_app [Call t ticks dest xs] aux =
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

val compile_prog_def = Define`
  compile_prog max_app prog =
    let (new_exps, aux) = compile_exps max_app (MAP (SND o SND) prog) [] in
      MAP2 (λ(loc,args,_) exp. (loc + num_stubs max_app, args, exp))
        prog new_exps ++ aux`;

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

Theorem compile_exps_acc:
   !max_app xs aux.
      let (c,aux1) = compile_exps max_app xs aux in
        (LENGTH c = LENGTH xs) /\ ?ys. aux1 = ys ++ aux
Proof
  recInduct compile_exps_ind \\ REPEAT STRIP_TAC
  \\ fs [compile_exps_def] \\ SRW_TAC [] [] \\ fs [LET_DEF,ADD1]
  \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ rfs [] \\ fs [pair_lem1] >>
  rw [] >>
  fs [pair_lem2] >>
  rfs [compile_exps_def, LET_THM] >>
  fs [pair_lem1, pair_lem2] >>
  metis_tac [build_aux_acc, APPEND_ASSOC]
QED

Theorem compile_exps_LENGTH:
   (compile_exps max_app xs aux = (c,aux1)) ==> (LENGTH c = LENGTH xs)
Proof
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`max_app`,`xs`,`aux`] compile_exps_acc)
  \\ rfs [LET_DEF]
QED

Theorem compile_exps_SING:
   (compile_exps max_app [x] aux = (c,aux1)) ==> ?d. c = [d]
Proof
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`max_app`,`[x]`,`aux`] compile_exps_acc) \\ rfs [LET_DEF]
  \\ Cases_on `c` \\ fs [] \\ Cases_on `t` \\ fs []
QED

Theorem compile_exps_CONS:
   !max_app xs x aux.
      compile_exps max_app (x::xs) aux =
      (let (c1,aux1) = compile_exps max_app [x] aux in
       let (c2,aux2) = compile_exps max_app xs aux1 in
         (c1 ++ c2,aux2))
Proof
  Cases_on `xs` \\ fs[compile_exps_def] \\ fs [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
QED

Theorem compile_exps_SNOC:
   !xs x aux max_app.
      compile_exps max_app (SNOC x xs) aux =
      (let (c1,aux1) = compile_exps max_app xs aux in
       let (c2,aux2) = compile_exps max_app [x] aux1 in
         (c1 ++ c2,aux2))
Proof
  Induct THEN1
   (fs [compile_exps_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ ONCE_REWRITE_TAC [compile_exps_CONS]
  \\ ASM_SIMP_TAC std_ss [compile_exps_def,LET_DEF,APPEND_NIL]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []
QED

val _ = Datatype`
  config = <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; known_conf : clos_known$config option
            ; do_call : bool
            ; call_state : num_set # (num, num # closLang$exp) alist
            ; max_app : num
            |>`;

val default_config_def = Define`
  default_config = <|
    next_loc := 0;
    start := 1;
    do_mti := T;
    known_conf := SOME (clos_known$default_config 10);
    do_call := T;
    call_state := (LN,[]);
    max_app := 10 |>`;

val code_split_def = Define `
  (code_split [] xs ys = (xs,ys)) /\
  (code_split (z::zs) xs ys = code_split zs (z::ys) xs)`;

val code_merge_def = tDefine "code_merge" `
  code_merge xs ys =
    dtcase (xs,ys) of
    | ([],[]) => []
    | ([],_) => ys
    | (_,[]) => xs
    | (x1::xs1,y1::ys1) =>
        if FST x1 < (FST y1):num then
          x1::code_merge xs1 ys
        else
          y1::code_merge xs ys1`
  (WF_REL_TAC `measure (\(xs,ys). LENGTH xs + LENGTH ys)` \\ rw []);

Theorem code_split_NULL:
   !ts1 ts2 ts3 xs ys.
      (xs,ys) = code_split ts1 ts2 ts3 /\ ts2 <> [] /\ ts3 <> [] ==>
      xs <> [] /\ ys <> []
Proof
  Induct \\ fs [code_split_def] \\ rw [] \\ first_x_assum drule \\ fs []
QED

Theorem code_split_LENGTH:
   !ts1 ts2 ts3 xs ys.
      (xs,ys) = code_split ts1 ts2 ts3 ==>
      LENGTH xs + LENGTH ys = LENGTH ts1 + LENGTH ts2 + LENGTH ts3
Proof
  Induct \\ fs [code_split_def] \\ rw [] \\ first_x_assum drule \\ fs []
QED

val code_sort_def = tDefine "code_sort" `
  (code_sort [] = []) /\
  (code_sort [x] = [x]) /\
  (code_sort (x::y::xs) =
     let (xs,ys) = code_split xs [x] [y] in
       code_merge (code_sort xs) (code_sort ys))`
 (WF_REL_TAC `measure LENGTH` \\ rw []
  \\ imp_res_tac code_split_LENGTH
  \\ drule code_split_NULL \\ fs [] \\ full_simp_tac std_ss [GSYM LENGTH_NIL] >>
  decide_tac);

val chain_exps = Define `
  (chain_exps i [] = [(i, 0n, Op None (Const 0) [])]) ∧
  (chain_exps i [e] = [(i, 0n, e)]) ∧
  (chain_exps i (e::es) =
    (i, 0,
     closLang$Let None [e] (closLang$Call None 0 (i + 1n) [])) :: chain_exps (i + 1) es)`;

(* c.max_app must be the same each time this is called *)
val compile_common_def = Define `
  compile_common c es =
    let es = clos_mti$compile c.do_mti c.max_app es in
    (* Add space for functions to call the expressions *)
    let loc = c.next_loc + LENGTH es in
    (* Alignment padding *)
    let loc = if loc MOD 2 = 0 then loc else loc + 1 in
    let (n,es) = renumber_code_locs_list loc es in
    let (kc, es) = clos_known$compile c.known_conf es in
    let (es,g,aux) = clos_call$compile c.do_call es in
    let prog = chain_exps c.next_loc es ++ aux in
    let prog = clos_annotate$compile prog in
    let prog = clos_labels$compile prog in
      (c with <| start := c.next_loc; next_loc := n; known_conf := kc;
                 call_state := (g,aux) |>,
       prog)`;

val compile_def = Define `
  compile c es =
    let (c, prog) = compile_common c es in
    let prog =
      toAList (init_code c.max_app) ++
      (num_stubs c.max_app - 1, 0n, init_globals c.max_app (num_stubs c.max_app + c.start)) ::
      (compile_prog c.max_app prog)
    in
    let c = c with start := num_stubs c.max_app - 1 in
      (c,code_sort prog)`;

val _ = export_theory()
