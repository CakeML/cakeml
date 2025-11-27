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
Theory clos_to_bvl
Ancestors
  backend_common clos_mti[qualified] clos_call[qualified]
  clos_known[qualified] clos_number[qualified]
  clos_annotate[qualified] bvl_jump closLang bvl
Libs
  preamble

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Theorem partial_app_tag_neq_closure_tag[simp] =
  EVAL``partial_app_tag = closure_tag`` |> EQF_ELIM

Theorem clos_tag_shift_nil_tag[simp] =
  EVAL``clos_tag_shift nil_tag = nil_tag`` |> EQT_ELIM

Theorem clos_tag_shift_cons_tag[simp] =
  EVAL``clos_tag_shift cons_tag = cons_tag`` |> EQT_ELIM

Theorem clos_tag_shift_inj:
   clos_tag_shift n1 = clos_tag_shift n2 ⇒ n1 = n2
Proof
  EVAL_TAC >> rw[] >> simp[]
QED

(* Constant flattening *)

Overload PRIME[local] = “999983:num”;

Definition part_hash_def:
  part_hash (Int i) = Num (ABS i) MOD PRIME ∧
  part_hash (Str s) =
    (mlstring$strlen s + 3 * SUM (MAP ORD (mlstring$explode s))) MOD PRIME ∧
  part_hash (W64 w) = (17 + w2n w) MOD PRIME ∧
  part_hash (Con t ns) = (18 + 5 * t + 7 * SUM ns) MOD PRIME
End

Definition add_part_def:
  add_part n p aux acc =
    let h = part_hash p in
      dtcase lookup h aux of
      | NONE => (n+1n,n,insert h [(p,n)] aux,p::acc)
      | SOME bucket =>
          dtcase ALOOKUP bucket p of
          | NONE => (n+1n,n,insert h ((p,n)::bucket) aux,p::acc)
          | SOME k => (n,k,aux,acc)
End

Definition add_parts_def:
  add_parts (ConstInt i) n aux acc = add_part n (Int i) aux acc ∧
  add_parts (ConstStr s) n aux acc = add_part n (Str s) aux acc ∧
  add_parts (ConstWord64 w) n aux acc = add_part n (W64 w) aux acc ∧
  add_parts (ConstCons t cs) n aux acc =
    (let (n, rs, aux, acc) = add_parts_list cs n aux acc in
       add_part n (Con (clos_tag_shift t) rs) aux acc) ∧
  add_parts_list [] n aux acc = (n,[],aux,acc) ∧
  add_parts_list (c::cs) n aux acc =
    let (n,r,aux,acc) = add_parts c n aux acc in
    let (n,rs,aux,acc) = add_parts_list cs n aux acc in
      (n,r::rs,aux,acc)
End

Definition compile_const_def:
  compile_const (ConstInt i) = IntOp (Const i) ∧
  compile_const (ConstStr s) = BlockOp (Build [Str s]) ∧
  compile_const (ConstWord64 w) = BlockOp (Build [W64 w]) ∧
  compile_const (ConstCons t cs) =
    if NULL cs then BlockOp (Cons (clos_tag_shift t)) else
      let (n, rs, aux, acc) = add_parts_list cs 0 LN [] in
        BlockOp (Build (REVERSE ((Con (clos_tag_shift t) rs)::acc)))
End

(* / Constant flattening *)

Definition num_added_globals_def:
  num_added_globals = 1n
End

Definition partial_app_label_table_loc_def:
  partial_app_label_table_loc = 0n
End

Definition compile_op_def[simp]:
  compile_op (BlockOp (Cons tag)) = BlockOp (Cons (clos_tag_shift tag)) ∧
  compile_op (BlockOp (ConsExtend tag)) = BlockOp (ConsExtend (clos_tag_shift tag)) ∧
  compile_op (BlockOp (TagEq tag)) = BlockOp (TagEq (clos_tag_shift tag)) ∧
  compile_op (BlockOp (TagLenEq tag a)) = BlockOp (TagLenEq (clos_tag_shift tag) a) ∧
  compile_op (BlockOp (FromList tag)) = BlockOp (FromList (clos_tag_shift tag)) ∧
  compile_op (MemOp LengthByteVec) = MemOp LengthByte ∧
  compile_op (MemOp DerefByteVec) = MemOp DerefByte ∧
  compile_op (GlobOp (SetGlobal n)) = GlobOp (SetGlobal (n + num_added_globals)) ∧
  compile_op (GlobOp (Global n)) = GlobOp (Global (n + num_added_globals)) ∧
  compile_op (BlockOp (Constant c)) = compile_const c ∧
  compile_op x = x
End

Theorem compile_op_pmatch:
  ∀op.
  compile_op op =
    case op of
        BlockOp (Cons tag) => BlockOp (Cons (clos_tag_shift tag))
      | BlockOp (ConsExtend tag) => BlockOp (ConsExtend (clos_tag_shift tag))
      | BlockOp (TagEq tag) => BlockOp (TagEq (clos_tag_shift tag))
      | BlockOp (TagLenEq tag a) => BlockOp (TagLenEq (clos_tag_shift tag) a)
      | BlockOp (FromList tag) => BlockOp (FromList (clos_tag_shift tag))
      | MemOp LengthByteVec => MemOp LengthByte
      | MemOp DerefByteVec => MemOp DerefByte
      | GlobOp (SetGlobal n) => GlobOp (SetGlobal (n + num_added_globals))
      | GlobOp (Global n) => GlobOp (Global (n + num_added_globals))
      | BlockOp (Constant c) => compile_const c
      | x => x
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> fs[compile_op_def]
QED

Definition mk_const_def[simp]:
  mk_const n : bvl$exp = Op (IntOp (Const (&n))) []
End

Definition mk_label_def[simp]:
  mk_label n : bvl$exp = Op (Label n) []
End

Definition mk_el_def[simp]:
  mk_el b i : bvl$exp = Op (MemOp El) [i; b]
End

Definition free_let_def:
  free_let cl n = (GENLIST (\n. mk_elem_at cl (n+2)) n)
End

Definition code_for_recc_case_def:
  code_for_recc_case n num_args (c:bvl$exp) =
    (num_args + 1,
     Let [mk_elem_at (Var num_args) 2]
      (Let (GENLIST (\a. Var (a + 1)) num_args ++ GENLIST (\i. mk_elem_at (Var 0) i) n) c))
End

Definition build_aux_def:
  (build_aux i [] aux = (i:num,aux)) /\
  (build_aux i ((x:num#bvl$exp)::xs) aux = build_aux (i+2) xs ((i,x) :: aux))
End

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

Definition recc_Let_def:
  recc_Let n num_args i =
    Let [mk_elem_at (Var 0) 2]
     (Let [Op (BlockOp (Cons closure_tag)) [Var 0; mk_const (num_args-1); mk_label n]]
       (Let [Op (MemOp Update) [Var 0; mk_const i; Var 1]]
         (Var 1 : bvl$exp)))
End

Definition recc_Lets_def:
  recc_Lets n nargs k rest =
    if k = 0:num then rest else
      let k = k - 1 in
        Let [recc_Let (n + 2*k) (HD nargs) k] (recc_Lets n (TL nargs) k rest)
End

Definition recc_Let0_def:
  recc_Let0 n num_args i =
    Let [Op (BlockOp (Cons closure_tag)) [Var 0; mk_const (num_args-1); mk_label n]]
      (Let [Op (MemOp Update) [Var 0; mk_const i; Var 1]] (Var 1 : bvl$exp))
End

Definition build_recc_lets_def:
  build_recc_lets (nargs:num list) vs n1 fns_l (c3:bvl$exp) =
    Let [Let [Op (MemOp Ref) (REVERSE (MAP (K (mk_const 0)) nargs ++ MAP Var vs))]
           (recc_Let0 (n1 + (2 * (fns_l - 1))) (HD (REVERSE nargs)) (fns_l - 1))]
      (recc_Lets n1 (TL (REVERSE nargs)) (fns_l - 1) c3)
End

Definition num_stubs_def:
  num_stubs max_app =
    (* generic apps *)         max_app
    (* partial apps *)       + max_app * (max_app - 1) DIV 2
    + 1 (* code to install a jump table in global 0 *)
    + 1 (* location for force_thunk stub *)
End

Definition generic_app_fn_location_def:
  generic_app_fn_location n = n
End

Definition partial_app_fn_location_def:
  partial_app_fn_location (max_app:num) tot prev =
    max_app + tot * (tot - 1) DIV 2 + prev
End

Definition partial_app_fn_location_code_def:
  partial_app_fn_location_code max_app tot_exp prev_exp : bvl$exp =
    Let [tot_exp]
     (Op (IntOp Add) [prev_exp;
        Op (IntOp Div) [mk_const 2;
          Op (IntOp Mult) [Var 0; Op (IntOp Sub) [mk_const 1; Var 0]]]])
End

Definition mk_cl_call_def:
  mk_cl_call cl args =
    If (Op (BlockOp (EqualConst (closLang$Int (& (LENGTH args - 1))))) [mk_elem_at cl 1])
       (Call (LENGTH args - 1) NONE (args ++ [cl] ++ [mk_elem_at cl 0]))
       (Call 0 (SOME (generic_app_fn_location (LENGTH args - 1))) (args ++ [cl]))
End

(* Generic application of a function to n+1 arguments *)
Definition generate_generic_app_def:
  generate_generic_app max_app n =
    Let [Op (IntOp Sub) [mk_const (n+1); mk_elem_at (Var (n+1)) 1]] (* The number of arguments remaining - 1 *)
        (If (Op (IntOp Less) [mk_const 0; Var 0])
            (* Over application *)
            (Jump (mk_elem_at (Var (n+2)) 1)
              (GENLIST (\num_args.
                 Let [Call num_args
                           NONE
                           (GENLIST (\arg. Var (arg + 2 + n - num_args)) (num_args + 1) ++
                            [Var (n + 3)] ++
                            [mk_elem_at (Var (n + 3)) 0])]
                   (mk_cl_call (Var 0) (GENLIST (\n. Var (n + 3)) (n - num_args))))
               max_app))
            (* Partial application *)
            (mk_tick n
            (If (Op (BlockOp (TagEq closure_tag)) [Var (n+2)])
                (* Partial application of a normal closure *)
                (Op (BlockOp (Cons partial_app_tag))
                    (REVERSE
                      (mk_el (Op (GlobOp (Global 0)) [])
                        (partial_app_fn_location_code max_app
                          (mk_elem_at (Var (n+2)) 1)
                          (mk_const n)) ::
                       Var 0 ::
                       Var (n + 2) ::
                       GENLIST (\n. Var (n + 1)) (n + 1))))
                (* Partial application of a partially applied closure *)
                (Let [Op (IntOp Sub) [mk_const 3; Op (BlockOp LengthBlock) [Var (n+2)]]] (* The number of previous args *)
                  (Op (BlockOp (ConsExtend partial_app_tag))
                    (REVERSE
                      (Var (n + 3) ::
                       mk_const 3 ::
                       Var 0 ::
                       Op (IntOp Add) [Var 0; mk_const (n+4)] ::
                       mk_el (Op (GlobOp (Global 0)) [])
                         (partial_app_fn_location_code max_app
                           (Op (IntOp Add) [Var 0; Op (IntOp Add) [mk_const (n + 1); Var 1]])
                           (* Shift from Var0 to Var1 because of Let in
                            * partial_app_fn_location_code *)
                           (Op (IntOp Add) [Var 1; mk_const n])) ::
                       Var 1 ::
                       mk_elem_at (Var (n+3)) 2 ::
                       GENLIST (\this_arg. Var (this_arg + 2)) (n + 1))))))))
End

(* The functions to complete the application of a partial closure.
 * We expect prev_args < total_args, also the function should take one more
 * argument than total, and have seen one more than prev (since there is
 * possiblity for a 0 argument function, or a partial application wrapper that
 * has seen no arguments yet. *)
Definition generate_partial_app_closure_fn_def:
  generate_partial_app_closure_fn total_args prev_args =
    Let [mk_elem_at (Var (total_args - prev_args)) 2]
      (Call 0
        NONE
        (GENLIST (\this_arg. Var (this_arg + 1)) (total_args - prev_args) ++
         GENLIST (\prev_arg.
           mk_elem_at (Var (total_args - prev_args + 1)) (prev_arg + 3)) (prev_args + 1) ++
         [Var 0] ++
         [mk_elem_at (Var 0) 0]))
End

Definition check_closure_def:
  check_closure v e =
    If (Op (BlockOp (TagEq closure_tag)) [Var v]) (Bool T)
      (If (Op (BlockOp (TagEq partial_app_tag)) [Var v]) (Bool T) e)
End

Definition init_code_def:
  init_code max_app =
    sptree$fromList
      (GENLIST (\n. (n + 2, generate_generic_app max_app n)) max_app ++
       FLAT
         (GENLIST
           (\tot.
             GENLIST
               (\prev. (tot - prev + 1, generate_partial_app_closure_fn tot prev))
               tot)
           max_app))
End

Definition init_globals_def:
  init_globals max_app start_loc =
    Let [Op (GlobOp AllocGlobal) [Op (IntOp (Const 1)) []]]
    (Let
      [Op (GlobOp (SetGlobal partial_app_label_table_loc))
        [Op (BlockOp (Cons tuple_tag))
          (REVERSE (FLAT
            (GENLIST
              (\tot.
                GENLIST
                  (\prev. mk_label (partial_app_fn_location max_app tot prev))
                  tot)
              max_app)))]]
      (* Expect the real start of the program in code location 3 *)
      (Call 0 (SOME start_loc) []))
End

Definition force_thunk_code_def:
  force_thunk_code =
    If (Op (BlockOp (EqualConst (Int 0))) [mk_elem_at (Var 1) 1])
      (Let [Call 0 NONE [mk_unit; Var 1; mk_elem_at (Var 1) 0]]
        (Let [Op (ThunkOp (UpdateThunk Evaluated)) [Var 0; Var 1]] (Var 1)))
      (Let [Call 0 (SOME 0) [mk_unit; Var 1]]
        (Let [Op (ThunkOp (UpdateThunk Evaluated)) [Var 0; Var 1]] (Var 1)))
       : bvl$exp
End

Definition compile_exps_def:
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
       else if op = ThunkOp ForceThunk then
         Let c1 (Force (num_stubs max_app - 2) 0)
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
       ([Op (BlockOp (Cons closure_tag))
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
           Op (BlockOp (Cons closure_tag))
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
       ([Call ticks (SOME (dest + (num_stubs max_app))) c1],aux1))
Termination
  WF_REL_TAC `measure (exp3_size o FST o SND)` >>
   srw_tac [ARITH_ss] [closLangTheory.exp_size_def] >>
   `!l. closLang$exp3_size (MAP SND l) <= exp1_size l`
            by (Induct_on `l` >>
                rw [closLangTheory.exp_size_def] >>
                PairCases_on `h` >>
                full_simp_tac (srw_ss()++ARITH_ss) [closLangTheory.exp_size_def]) >>
  pop_assum (qspec_then `v7` assume_tac) >>
  decide_tac
End

val compile_exps_ind = theorem"compile_exps_ind";

Definition compile_exp_sing_def:
  (compile_exp_sing max_app (Var t v) aux = ((Var v):bvl$exp, aux)) /\
  (compile_exp_sing max_app (If t x1 x2 x3) aux =
     let (c1,aux1) = compile_exp_sing max_app x1 aux in
     let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
     let (c3,aux3) = compile_exp_sing max_app x3 aux2 in
       (If c1 c2 c3,aux3)) /\
  (compile_exp_sing max_app (Let t xs x2) aux =
     let (c1,aux1) = compile_exp_list max_app xs aux in
     let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
       (Let c1 c2, aux2)) /\
  (compile_exp_sing max_app (Raise t x1) aux =
     let (c1,aux1) = compile_exp_sing max_app x1 aux in
       (Raise c1, aux1)) /\
  (compile_exp_sing max_app (Tick t x1) aux =
     let (c1,aux1) = compile_exp_sing max_app x1 aux in
       (Tick c1, aux1)) /\
  (compile_exp_sing max_app (Op t op xs) aux =
     let (c1,aux1) = compile_exp_list max_app xs aux in
     (if op = Install then Call 0 NONE [Op Install c1]
      else if op = ThunkOp ForceThunk then Let c1 (Force (num_stubs max_app - 2) 0)
      else Op (compile_op op) c1
     ,aux1)) /\
  (compile_exp_sing max_app (App t loc_opt x1 xs2) aux =
     let (c1,aux1) = compile_exp_sing max_app x1 aux in
     let (c2,aux2) = compile_exp_list max_app xs2 aux1 in
       ((dtcase loc_opt of
         | NONE =>
             Let (c2++[c1]) (mk_cl_call (Var (LENGTH c2)) (GENLIST Var (LENGTH c2)))
         | SOME loc =>
             (Call (LENGTH c2 - 1) (SOME (loc + (num_stubs max_app))) (c2 ++ [c1]))),
        aux2)) /\
  (compile_exp_sing max_app (Fn t loc_opt vs_opt num_args x1) aux =
     let loc = dtcase loc_opt of NONE => 0 | SOME n => n in
     let vs = dtcase vs_opt of NONE => [] | SOME vs => vs in
     let (c1,aux1) = compile_exp_sing max_app x1 aux in
     let c2 =
       Let (GENLIST Var num_args ++ free_let (Var num_args) (LENGTH vs)) c1
     in
       (Op (BlockOp (Cons closure_tag))
           (REVERSE (mk_label (loc + num_stubs max_app) :: mk_const (num_args - 1) :: MAP Var vs)),
        (loc + (num_stubs max_app),num_args+1,c2) :: aux1)) /\
  (compile_exp_sing max_app (Letrec t loc_opt vsopt fns x1) aux =
     let loc = dtcase loc_opt of NONE => 0 | SOME n => n in
     let vs = dtcase vsopt of NONE => [] | SOME x => x in
     dtcase fns of
     | [] => compile_exp_sing max_app x1 aux
     | [(num_args, exp)] =>
         let (c1,aux1) = compile_exp_sing max_app exp aux in
         let c3 = Let (GENLIST Var num_args ++ [Var num_args] ++ free_let (Var num_args) (LENGTH vs)) c1 in
         let (c2,aux2) = compile_exp_sing max_app x1 ((loc + (num_stubs max_app),num_args+1,c3)::aux1) in
         let c4 =
           Op (BlockOp (Cons closure_tag))
              (REVERSE (mk_label (loc + (num_stubs max_app)) :: mk_const (num_args - 1) :: MAP Var vs))
         in
           (bvl$Let [c4] c2, aux2)
     | _ =>
         let fns_l = LENGTH fns in
         let l = fns_l + LENGTH vs in
         let (cs,aux1) = compile_exp_list max_app (MAP SND fns) aux in
         let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs in
         let (n2,aux2) = build_aux (loc + (num_stubs max_app)) cs1 aux1 in
         let (c3,aux3) = compile_exp_sing max_app x1 aux2 in
         let c4 = build_recc_lets (MAP FST fns) vs (loc + (num_stubs max_app)) fns_l c3 in
           (c4,aux3)) /\
  (compile_exp_sing max_app (Handle t x1 x2) aux =
     let (c1,aux1) = compile_exp_sing max_app x1 aux in
     let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
       (Handle c1 c2, aux2)) /\
  (compile_exp_sing max_app (Call t ticks dest xs) aux =
     let (c1,aux1) = compile_exp_list max_app xs aux in
       (Call ticks (SOME (dest + (num_stubs max_app))) c1,aux1)) ∧

  (compile_exp_list max_app [] aux = ([],aux)) /\
  (compile_exp_list max_app ((x:closLang$exp)::xs) aux =
     let (c1,aux1) = compile_exp_sing max_app x aux in
     let (c2,aux2) = compile_exp_list max_app xs aux1 in
       (c1 :: c2, aux2))
Termination
  WF_REL_TAC `measure $ λx. case x of INL (_,e,_) => exp_size e
                                    | INR (_,es,_) => exp3_size es` >>
  srw_tac [ARITH_ss] [closLangTheory.exp_size_def] >>
  `!l. closLang$exp3_size (MAP SND l) <= exp1_size l` by (
    Induct_on `l` >> rw [closLangTheory.exp_size_def] >>
    PairCases_on `h` >> full_simp_tac (srw_ss()++ARITH_ss) [closLangTheory.exp_size_def]) >>
  pop_assum (qspec_then `v7` assume_tac) >> decide_tac
End

Theorem compile_exp_sing_eq:
  (∀n e l. compile_exps n [e] l = (λ(a,b). ([a], b)) (compile_exp_sing n e l)) ∧
  (∀n es l. compile_exps n es l = compile_exp_list n es l)
Proof
  ho_match_mp_tac compile_exp_sing_ind >>
  reverse $ rw[compile_exps_def, compile_exp_sing_def] >>
  rpt (pairarg_tac >> gvs[])
  >- (Cases_on `es` >> simp[compile_exps_def] >> gvs[compile_exp_sing_def]) >>
  `compile_exps n (MAP SND fns) l = compile_exp_list n (MAP SND fns) l` by (
    namedCases_on `fns` ["", "fnsh fnst"] >>
    gvs[compile_exps_def, compile_exp_sing_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    PairCases_on `fnsh` >> gvs[] >> Cases_on `fnst` >> gvs[] >>
    gvs[compile_exps_def, compile_exp_sing_def]) >>
  TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[]>>
  PairCases_on `h` >> gvs[] >> rpt (pairarg_tac >> gvs[])
QED

Definition compile_prog_def:
  compile_prog max_app prog =
    let (new_exps, aux) = compile_exps max_app (MAP (SND o SND) prog) [] in
      MAP2 (λ(loc,args,_) exp. (loc + num_stubs max_app, args, exp))
        prog new_exps ++ aux
End

Theorem compile_prog_eq = compile_prog_def |> SRULE [compile_exp_sing_eq];

Theorem pair_lem1[local]:
  !f x. (\(a,b). f a b) x = f (FST x) (SND x)
Proof
  rw [] >>
  PairCases_on `x` >>
  fs []
QED

Theorem pair_lem2[local]:
  !x y z. (x,y) = z ⇔ x = FST z ∧ y = SND z
Proof
  rw [] >>
  PairCases_on `z` >>
  rw []
QED

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

Datatype:
  config = <| next_loc : num
            ; start : num
            ; do_mti : bool
            ; known_conf : clos_known$config option
            ; do_call : bool
            ; call_state : num_set # (num, num # closLang$exp) alist
            ; max_app : num
            |>
End

Definition default_config_def:
  default_config = <|
    next_loc := 0;
    start := 1;
    do_mti := T;
    known_conf := SOME (clos_known$default_config 10);
    do_call := T;
    call_state := (LN,[]);
    max_app := 10 |>
End

Definition code_split_def:
  (code_split [] xs ys = (xs,ys)) /\
  (code_split (z::zs) xs ys = code_split zs (z::ys) xs)
End

Definition code_merge_def:
  code_merge xs ys =
    dtcase (xs,ys) of
    | ([],[]) => []
    | ([],_) => ys
    | (_,[]) => xs
    | (x1::xs1,y1::ys1) =>
        if FST x1 < (FST y1):num then
          x1::code_merge xs1 ys
        else
          y1::code_merge xs ys1
Termination
  WF_REL_TAC `measure (\(xs,ys). LENGTH xs + LENGTH ys)` \\ rw []
End

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

Definition code_sort_def:
  (code_sort [] = []) /\
  (code_sort [x] = [x]) /\
  (code_sort (x::y::xs) =
     let (xs,ys) = code_split xs [x] [y] in
       code_merge (code_sort xs) (code_sort ys))
Termination
  WF_REL_TAC `measure LENGTH` \\ rw []
  \\ imp_res_tac code_split_LENGTH
  \\ drule code_split_NULL \\ fs [] \\ full_simp_tac std_ss [GSYM LENGTH_NIL] >>
  decide_tac
End

Definition chain_exps_def:
  (chain_exps i [] = [(i, 0n, Op None (IntOp (Const 0)) [])]) ∧
  (chain_exps i [e] = [(i, 0n, e)]) ∧
  (chain_exps i (e::es) =
    (i, 0,
     closLang$Let None [e] (closLang$Call None 0 (i + 1n) [])) :: chain_exps (i + 1) es)
End

(* c.max_app must be the same each time this is called *)
Definition compile_common_def:
  compile_common c es =
    let es = clos_mti$compile c.do_mti c.max_app es in
    (* Add space for functions to call the expressions *)
    let loc = c.next_loc + MAX 1 (LENGTH es) in
    (* Alignment padding *)
    let loc = if loc MOD 2 = 0 then loc else loc + 1 in
    let (n,es) = renumber_code_locs_list loc es in
    let (kc, es) = clos_known$compile c.known_conf es in
    let (es,g,aux) = clos_call$compile c.do_call es in
    let prog = chain_exps c.next_loc es ++ aux in
    let prog = clos_annotate$compile prog in
      (c with <| start := c.next_loc; next_loc := n; known_conf := kc;
                 call_state := (g,aux) |>,
       prog)
End

Definition add_src_names_def:
  add_src_names n [] l = l ∧
  add_src_names n (x::xs) l =
    add_src_names (n+2) xs (insert n (mlstring$concat [x; mlstring$strlit "_clos"]) (insert (n+1) x l))
End

Definition get_src_names_def:
  get_src_names [] l = l ∧
  get_src_names (x::y::xs) l = get_src_names (y::xs) (get_src_names [x] l) ∧
  get_src_names [closLang$If _ x y z] l =
    get_src_names [x] (get_src_names [y] (get_src_names [z] l)) ∧
  get_src_names [closLang$Var _ _] l = l ∧
  get_src_names [closLang$Let _ xs x] l = get_src_names (x::xs) l ∧
  get_src_names [Raise _ x] l = get_src_names [x] l ∧
  get_src_names [Handle _ x y] l = get_src_names [x] (get_src_names [y] l) ∧
  get_src_names [Tick _ x] l = get_src_names [x] l ∧
  get_src_names [Call _ _ _ xs] l = get_src_names xs l ∧
  get_src_names [Op _ _ xs] l = get_src_names xs l ∧
  get_src_names [App _ _ x xs] l = get_src_names (x::xs) l ∧
  get_src_names [Fn name loc_opt _ _ x] l =
    (let l1 = get_src_names [x] l in
       dtcase loc_opt of NONE => l1
                       | SOME n => add_src_names n [name] l1) ∧
  get_src_names [Letrec names loc_opt _ funs x] l =
    (let l0 = get_src_names (MAP SND funs) l in
     let l1 = get_src_names [x] l0 in
       dtcase loc_opt of NONE => l1
                       | SOME n => add_src_names n names l1)
Termination
  WF_REL_TAC ‘measure (closLang$exp3_size o FST)’ \\ rw []
  \\ qsuff_tac ‘exp3_size (MAP SND funs) <= exp1_size funs’ \\ fs []
  \\ Induct_on ‘funs’ \\ fs [closLangTheory.exp_size_def]
  \\ fs [FORALL_PROD,closLangTheory.exp_size_def]
End

Definition get_src_names_sing_def:
  get_src_names_sing (closLang$If _ x y z) l =
    get_src_names_sing x (get_src_names_sing y (get_src_names_sing z l)) ∧
  get_src_names_sing (closLang$Var _ _) l = l ∧
  get_src_names_sing (closLang$Let _ xs x) l =
    get_src_names_list xs (get_src_names_sing x l) ∧
  get_src_names_sing (Raise _ x) l = get_src_names_sing x l ∧
  get_src_names_sing (Handle _ x y) l = get_src_names_sing x (get_src_names_sing y l) ∧
  get_src_names_sing (Tick _ x) l = get_src_names_sing x l ∧
  get_src_names_sing (Call _ _ _ xs) l = get_src_names_list xs l ∧
  get_src_names_sing (Op _ _ xs) l = get_src_names_list xs l ∧
  get_src_names_sing (App _ _ x xs) l =
    get_src_names_list xs (get_src_names_sing x l) ∧
  get_src_names_sing (Fn name loc_opt _ _ x) l =
    (let l1 = get_src_names_sing x l in
       dtcase loc_opt of NONE => l1
                       | SOME n => add_src_names n [name] l1) ∧
  get_src_names_sing (Letrec names loc_opt _ funs x) l =
    (let l0 = get_src_names_list (MAP SND funs) l in
     let l1 = get_src_names_sing x l0 in
       dtcase loc_opt of NONE => l1
                       | SOME n => add_src_names n names l1) ∧

  get_src_names_list [] l = l ∧
  get_src_names_list (x::xs) l = get_src_names_list xs (get_src_names_sing x l)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL (e,_) => closLang$exp_size e
                                    | INR (es,_) => closLang$exp3_size es’
  \\ rw [closLangTheory.exp_size_def]
  \\ qsuff_tac ‘exp3_size (MAP SND funs) <= exp1_size funs’ \\ fs []
  \\ Induct_on ‘funs’ \\ fs [closLangTheory.exp_size_def]
  \\ fs [FORALL_PROD,closLangTheory.exp_size_def]
End

Theorem get_src_names_sing_eq:
  (∀e l. get_src_names [e] l = get_src_names_sing e l) ∧
  (∀es l. get_src_names es l = get_src_names_list es l)
Proof
  ho_match_mp_tac get_src_names_sing_ind >>
  rw[get_src_names_def, get_src_names_sing_def] >>
  Cases_on `es` >> rw[get_src_names_def, get_src_names_sing_def]
QED

Definition make_name_alist_def:
  make_name_alist nums prog nstubs dec_start (dec_length:num) =
    let src_names = get_src_names (MAP (SND o SND) prog) LN in
      fromAList(MAP(λn.(n, if n < nstubs then
                             if n = nstubs-1 then mlstring$strlit "bvl_init" else
                             if n = nstubs-2 then mlstring$strlit "bvl_force" else
                                                  mlstring$strlit "bvl_stub"
                           else let clos_name = n - nstubs in
                             if dec_start ≤ clos_name ∧ clos_name < dec_start + dec_length
                             then mlstring$strlit "dec" else
                               dtcase lookup clos_name src_names of
                               | NONE => mlstring$strlit "unknown_clos_fun"
                               | SOME s => s)) nums)
        : mlstring$mlstring num_map
End

Theorem make_name_alist_eq =
  make_name_alist_def |> SRULE [get_src_names_sing_eq];

Definition compile_def:
  compile c0 es =
    let (c, prog) = compile_common c0 es in
    let n = num_stubs c.max_app in
    let init_stubs = toAList (init_code c.max_app) in
    let init_globs = [(n - 1, 0n, init_globals c.max_app (n + c.start))] in
    let force_stub = [(n - 2, 2n, force_thunk_code)] in
    let comp_progs = compile_prog c.max_app prog in
    let prog' = init_stubs ++ force_stub ++ init_globs ++ comp_progs in
    let func_names = make_name_alist (MAP FST prog') prog n
                       c0.next_loc (LENGTH es) in
    let c = c with start := n - 1 in
      (c, code_sort prog', func_names)
End

Definition extract_name_def:
  extract_name [] = (0,[]) /\
  extract_name (x :: xs) =
    dtcase (some n. ?t. x = Op t (IntOp (Const (& n))) []) of
    | NONE => (0,x::xs)
    | SOME n => (n, if xs = [] then [x] else xs)
End

Theorem extract_name_pmatch:
  extract_name xs =
    dtcase xs of
    | [] => (0,xs)
    | (x::xs) =>
      case x of
        (Op t (IntOp (Const i)) []) =>
          (if i < 0 then (0,x::xs) else
            (Num (ABS i), if xs = [] then [x] else xs))
      | _ => (0,x::xs)
Proof
  Cases_on ‘xs’ \\ fs [extract_name_def]
  \\ Cases_on ‘h’ \\ fs []
  \\ Cases_on ‘l’ \\ fs []
  \\ Cases_on ‘o'’ \\ fs []
  \\ Cases_on ‘i’ \\ fs []
  \\ Cases_on ‘i'’ \\ fs []
QED

Definition compile_inc_def:
  compile_inc max_app (es,prog) =
    let (n,real_es) = extract_name es in
        clos_to_bvl$compile_prog max_app
          (clos_to_bvl$chain_exps n real_es ++ prog)
    : (num, num # exp) alist
End

Definition clos_to_bvl_compile_inc_def:
  clos_to_bvl_compile_inc c p =
    let p = clos_mti$cond_mti_compile_inc c.do_mti c.max_app p in
    let (n, p) = ignore_table clos_number$compile_inc c.next_loc p in
    let c = c with <| next_loc := n |> in
    let spt = option_val_approx_spt c.known_conf in
    let (spt, p) = known_compile_inc (known_static_conf c.known_conf) spt p in
    let c = c with <| known_conf := option_upd_val_spt spt c.known_conf |> in
    let (c', p) = clos_call$cond_call_compile_inc c.do_call (FST c.call_state) p in
    let c = c with <| call_state := (c', []) |> in
    let p = clos_annotate$compile_inc p in
    let p = clos_to_bvl$compile_inc c.max_app p in
      (c, p)
End

