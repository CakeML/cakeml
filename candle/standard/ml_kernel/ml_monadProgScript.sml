open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory holKernelTheory;
open terminationTheory ml_progLib ml_progTheory

val _ = new_theory "ml_monadProg";

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

fun auto_prove proof_name (goal,tac) = let
  val (rest,validation) = tac ([],goal) handle Empty => fail()
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl th) then th else DISCH T th end

(* a few basics *)

val with_same_refs = Q.store_thm("with_same_refs",
  `(s with refs := s.refs) = s`,
  simp[state_component_equality])

val _ = (use_full_type_names := false);

val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;

val _ = ml_prog_update (open_module "Kernel");

(* construct type refinement invariants *)

val _ = register_type ``:type``;

val MEM_type_size = Q.prove(
  `!ts t. MEM t ts ==> type_size t < type1_size ts`,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val type_ind = Q.store_thm("type_ind",
  `(!s ts. (!t. MEM t ts ==> P t) ==> P (Tyapp s ts)) /\
    (!v. P (Tyvar v)) ==> !x. P x`,
  REPEAT STRIP_TAC \\ completeInduct_on `type_size x`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!x1 x2. bb` MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ EVAL_TAC \\ IMP_RES_TAC MEM_type_size \\ DECIDE_TAC);

val TYPE_TYPE_def = fetch "-" "TYPE_TYPE_def"

val LIST_TYPE_NO_CLOSURES = Q.prove(
  `!xs v.
      (!x v. MEM x xs /\ p x v ==> no_closures v) /\
      LIST_TYPE p xs v ==> no_closures v`,
  Induct \\ FULL_SIMP_TAC std_ss [LIST_TYPE_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF,MEM]
  \\ METIS_TAC []);

val LIST_TYPE_11 = Q.prove(
  `!P ts v1 us v2.
      (!x1.
       MEM x1 ts ==>
        !v1 x2 v2.
          P x1 v1 /\ P x2 v2 ==>
          types_match v1 v2 /\ ((v1 = v2) <=> (x1 = x2))) /\
    LIST_TYPE P ts v1 /\ LIST_TYPE P us v2 ==>
    types_match v1 v2 /\ ((v1 = v2) = (ts = us))`,
  STRIP_TAC \\ Induct \\ Cases_on `us` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [LIST_TYPE_def,types_match_def,ctor_same_type_def]
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,types_match_def,ctor_same_type_def]
  \\ METIS_TAC []);

val CHAR_IMP_no_closures = Q.prove(
  `CHAR x v ==> no_closures v`,
  SIMP_TAC std_ss [CHAR_def,no_closures_def]);

val STRING_IMP_no_closures = Q.prove(
  `STRING_TYPE x v ==> no_closures v`,
  SIMP_TAC std_ss [STRING_TYPE_def,no_closures_def]);

val EqualityType_thm = Q.prove(
  `EqualityType abs <=>
      (!x1 v1. abs x1 v1 ==> no_closures v1) /\
      (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2 /\
                                                (v1 = v2 <=> x1 = x2))`,
  SIMP_TAC std_ss [EqualityType_def] \\ METIS_TAC []);

val STRING_TYPE_lemma = Q.prove(
  `EqualityType (STRING_TYPE)`,
  METIS_TAC (eq_lemmas ()));

val EqualityType_TYPE = Q.prove(
  `EqualityType TYPE_TYPE`,
  SIMP_TAC std_ss [EqualityType_thm] \\ STRIP_TAC THEN1
   (HO_MATCH_MP_TAC type_ind
    \\ FULL_SIMP_TAC std_ss [TYPE_TYPE_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF]
    \\ IMP_RES_TAC (LIST_TYPE_NO_CLOSURES |> GEN_ALL)
    \\ METIS_TAC [CHAR_IMP_no_closures,STRING_IMP_no_closures])
  \\ HO_MATCH_MP_TAC type_ind \\ reverse STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [TYPE_TYPE_def]
    \\ FULL_SIMP_TAC (srw_ss()) [types_match_def,ctor_same_type_def]
    \\ ASSUME_TAC STRING_TYPE_lemma
    \\ FULL_SIMP_TAC std_ss [EqualityType_def] \\ RES_TAC)
  \\ REPEAT GEN_TAC \\ STRIP_TAC \\ REPEAT GEN_TAC \\ STRIP_TAC
  \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [TYPE_TYPE_def]
  \\ FULL_SIMP_TAC (srw_ss()) [types_match_def,ctor_same_type_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 /\ (x1 = y1)) /\ (b2 /\ (x2 = y2)) ==>
       (b1 /\ b2) /\ ((x1 /\ x2 <=> y1 /\ y2))``)
  \\ STRIP_TAC THEN1
   (ASSUME_TAC STRING_TYPE_lemma
    \\ FULL_SIMP_TAC std_ss [EqualityType_def] \\ RES_TAC
    \\ ASM_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC LIST_TYPE_11
  \\ Q.EXISTS_TAC `TYPE_TYPE`
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ RES_TAC)
  |> store_eq_thm;

val _ = register_type ``:term``;
val _ = register_type ``:thm``;
val _ = register_type ``:update``;

val _ = register_exn_type ``:hol_exn``;

val HOL_EXN_TYPE_def = theorem"HOL_EXN_TYPE_def"

(*
  fetch "-" "TYPE_TYPE_def";
  fetch "-" "TERM_TYPE_def";
  fetch "-" "THM_TYPE_def";
*)

(* ref 0 *)

val init_type_constants_def = Define `
  init_type_constants = [(strlit"bool",0); (strlit"fun",2:num)]`

val init_type_constants_v = translate init_type_constants_def

val the_type_constants_def = Define `
    the_type_constants = Loc (LENGTH init_type_constants_refs)`;

(* for debugging:
val s = ref ml_progLib.init_state
val _ = ml_prog_update (fn k => (s := k; k))
val k = !s
*)

val _ = ml_prog_update (fn k => let
  val lemma = Q.prove(
    `evaluate F ^(get_env k) ^(get_state k)
        (App Opref [Var (Short "init_type_constants")])
        (^(get_state k) with refs := init_type_constants_refs ++ [Refv init_type_constants_v],
         Rval (the_type_constants))`,
    ntac 5 (fs [Once evaluate_cases,PULL_EXISTS,do_app_def,store_alloc_def,
        EVAL ``lookup_var_id (Short "init_type_constants") ^(get_env k)``])
    \\ EVAL_TAC \\ fs [])
  in add_Dlet lemma "the_type_constants" [the_type_constants_def] k end)

(* ref 1 *)

val init_term_constants_def = Define `
  init_term_constants = [(strlit"=",
    Tyapp (strlit"fun")
      [Tyvar (strlit"A");
       Tyapp (strlit"fun")
         [Tyvar (strlit"A");
          Tyapp (strlit"bool") []]])]`

val init_term_constants_v = translate init_term_constants_def

val the_term_constants_def = Define `
    the_term_constants = Loc (LENGTH init_type_constants_refs + 1 +
                              LENGTH init_term_constants_refs)`;

(* for debugging:
val s = ref ml_progLib.init_state
val _ = ml_prog_update (fn k => (s := k; k))
val k = !s
*)

val _ = ml_prog_update (fn k => let
  val lemma = Q.prove(
    `evaluate F ^(get_env k) ^(get_state k)
        (App Opref [Var (Short "init_term_constants")])
        (^(get_state k) with refs := init_type_constants_refs ++ [Refv init_type_constants_v] ++
                                     init_term_constants_refs ++ [Refv init_term_constants_v],
         Rval (the_term_constants))`,
    ntac 5 (fs [Once evaluate_cases,PULL_EXISTS,do_app_def,store_alloc_def,
        EVAL ``lookup_var_id (Short "init_term_constants") ^(get_env k)``])
    \\ EVAL_TAC \\ fs [])
  in add_Dlet lemma "the_term_constants" [the_term_constants_def] k end)

(* ref 2 *)

val init_axioms_def = Define `
  init_axioms = []:thm list`

val init_axioms_v = translate init_axioms_def

val the_axioms_def = Define `
    the_axioms = Loc (LENGTH init_type_constants_refs + 1 +
                      LENGTH init_term_constants_refs + 1 +
                      LENGTH init_axioms_refs)`;

(* for debugging:
val s = ref ml_progLib.init_state
val _ = ml_prog_update (fn k => (s := k; k))
val k = !s
*)

val _ = ml_prog_update (fn k => let
  val lemma = Q.prove(
    `evaluate F ^(get_env k) ^(get_state k)
        (App Opref [Var (Short "init_axioms")])
        (^(get_state k) with refs := init_type_constants_refs ++ [Refv init_type_constants_v] ++
                                     init_term_constants_refs ++ [Refv init_term_constants_v] ++
                                     init_axioms_refs ++ [Refv init_axioms_v],
         Rval (the_axioms))`,
    ntac 5 (fs [Once evaluate_cases,PULL_EXISTS,do_app_def,store_alloc_def,
        EVAL ``lookup_var_id (Short "init_axioms") ^(get_env k)``])
    \\ EVAL_TAC \\ fs [])
  in add_Dlet lemma "the_axioms" [the_axioms_def] k end)

(* ref 3 *)

val init_context_def = Define `
  init_context = ^(rhs(concl(holSyntaxTheory.init_ctxt_def)))`

val init_context_v = translate init_context_def

val the_context_def = Define `
    the_context = Loc (LENGTH init_type_constants_refs + 1 +
                       LENGTH init_term_constants_refs + 1 +
                       LENGTH init_axioms_refs + 1 +
                       LENGTH init_context_refs)`;

(* for debugging:
val s = ref ml_progLib.init_state
val _ = ml_prog_update (fn k => (s := k; k))
val k = !s
*)

val _ = ml_prog_update (fn k => let
  val lemma = Q.prove(
    `evaluate F ^(get_env k) ^(get_state k)
        (App Opref [Var (Short "init_context")])
        (^(get_state k) with refs := init_type_constants_refs ++ [Refv init_type_constants_v] ++
                                     init_term_constants_refs ++ [Refv init_term_constants_v] ++
                                     init_axioms_refs ++ [Refv init_axioms_v] ++
                                     init_context_refs ++ [Refv init_context_v],
         Rval (the_context))`,
    ntac 5 (fs [Once evaluate_cases,PULL_EXISTS,do_app_def,store_alloc_def,
        EVAL ``lookup_var_id (Short "init_context") ^(get_env k)``])
    \\ EVAL_TAC \\ fs [])
  in add_Dlet lemma "the_context" [the_context_def] k end)

(* definition of EvalM *)

val isRefv_def = Define `
  isRefv P x = ?v. (x = Refv v) /\ P v`;

val HOL_STORE_def = Define `
  HOL_STORE s refs <=>
    ∃type_constants term_constants axioms context.
    init_type_constants_refs ++ [type_constants] ++
    init_term_constants_refs ++ [term_constants] ++
    init_axioms_refs ++ [axioms] ++
    init_context_refs ++ [context] ≼ s ∧
    isRefv ((LIST_TYPE (PAIR_TYPE STRING_TYPE NUM))
            refs.the_type_constants) type_constants /\
    isRefv ((LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE))
            refs.the_term_constants) term_constants /\
    isRefv (LIST_TYPE THM_TYPE refs.the_axioms) axioms /\
    isRefv (LIST_TYPE UPDATE_TYPE refs.the_context) context`;

val HOL_STORE_append = Q.store_thm("HOL_STORE_append",
  `HOL_STORE srefs refs ⇒ HOL_STORE (srefs ++ junk) refs`,
  rw[HOL_STORE_def] \\ fs[IS_PREFIX_APPEND]);

val EvalM_def = Define `
  EvalM env exp P <=>
    !(s:unit state) refs. HOL_STORE s.refs refs ==>
             !junk.
             ?s2 res refs2. evaluate F env (s with refs := s.refs ++ junk) exp (s2,res) /\
                            P (refs,s) (refs2,s2,res) /\ HOL_STORE s2.refs refs2`;

(* refinement invariant for ``:'a M`` *)

val _ = type_abbrev("M", ``:hol_refs -> 'a hol_result # hol_refs``);

val HOL_MONAD_def = Define `
  HOL_MONAD (a:'a->v->bool) (x:'a M) (state1:hol_refs,s1:unit state)
                                     (state2:hol_refs,s2:unit state,
                                      res: (v,v) result) =
    case (x state1, res) of
      ((HolRes y, st), Rval v) => (st = state2) /\ a y v
    | ((HolErr e, st), Rerr (Rraise v)) => (st = state2) /\
                                              HOL_EXN_TYPE e v
    | _ => F`

(* return *)

val EvalM_return = Q.store_thm("EvalM_return",
  `Eval env exp (a x) ==>
    EvalM env exp (HOL_MONAD a (ex_return x))`,
  rw[Eval_def,EvalM_def,ex_return_def,HOL_MONAD_def] \\
  first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac)
  \\ IMP_RES_TAC (evaluate_empty_state_IMP
                  |> INST_TYPE [``:'ffi``|->``:unit``]) \\
  asm_exists_tac \\ simp[HOL_STORE_append]);

(* bind *)

val EvalM_bind = Q.store_thm("EvalM_bind",
  `EvalM env e1 (HOL_MONAD b (x:'b M)) /\
    (!x v. b x v ==> EvalM (write name v env) e2 (HOL_MONAD a ((f x):'a M))) ==>
    EvalM env (Let (SOME name) e1 e2) (HOL_MONAD a (ex_bind x f))`,
  rw[EvalM_def,HOL_MONAD_def,ex_return_def,PULL_EXISTS] \\
  first_x_assum drule \\
  disch_then(qspec_then`junk`strip_assume_tac) \\
  Cases_on`x refs` \\ Cases_on`q` \\ Cases_on`res` \\ fs[]
  >- (
    rw[Once evaluate_cases] \\
    srw_tac[DNF_ss][] \\ disj1_tac \\
    asm_exists_tac \\ rw[] \\
    first_x_assum drule \\ disch_then drule \\
    disch_then(qspec_then`[]`strip_assume_tac) \\
    fs[GSYM write_def,opt_bind_def,ex_bind_def,with_same_refs] \\
    asm_exists_tac \\ fs[] \\ metis_tac[] )
  \\ Cases_on`e` \\ fs[] \\
  rw[Once evaluate_cases] \\
  srw_tac[DNF_ss][] \\ disj2_tac \\
  asm_exists_tac \\ rw[] \\
  rw[ex_bind_def]);

(* lift pure refinement invariants *)

val _ = type_abbrev("H",``:'a -> hol_refs # unit state ->
                                 hol_refs # unit state # (v,v) result -> bool``);

val PURE_def = Define `
  PURE a (x:'a) (refs1:hol_refs,s1:unit state) (refs2,s2,res:(v,v) result) =
    ?v:v junk. (res = Rval v) /\ (refs1 = refs2) /\ (s2 = s1 with refs := s1.refs ++ junk) /\ a x v`;

val Eval_IMP_PURE = Q.store_thm("Eval_IMP_PURE",
  `Eval env exp (P x) ==> EvalM env exp (PURE P x)`,
  rw[Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac)
  \\ IMP_RES_TAC (evaluate_empty_state_IMP
                  |> INST_TYPE [``:'ffi``|->``:unit``])
  \\ fs[]
  \\ metis_tac[HOL_STORE_append,APPEND_ASSOC]);

(* function abstraction and application *)

val ArrowP_def = Define `
  (ArrowP : 'a H -> 'b H -> ('a -> 'b) -> v -> bool) a b f c =
     !x refs1 s1 refs2 s2 (res:(v,v) result).
       a x (refs1,s1) (refs2,s2,res) /\ HOL_STORE s1.refs refs1 ==>
       ?junk v env exp.
       (refs2 = refs1) /\ (s2 = s1 with refs := s1.refs ++ junk) /\
       (res = Rval v) /\ do_opapp [c;v] = SOME (env,exp) /\
       !junk. ?refs3 s3 res3.
         evaluate F env (s2 with refs := s2.refs ++ junk) exp (s3,res3) /\
         b (f x) (refs1,s1) (refs3,s3,res3) /\
         HOL_STORE s3.refs refs3`;

val ArrowM_def = Define `
  (ArrowM : 'a H -> 'b H -> ('a -> 'b) H) a b = PURE (ArrowP a b)`;

val _ = add_infix("-M->",400,HOLgrammars.RIGHT)
val _ = overload_on ("-M->",``ArrowM``)

val evaluate_list_cases = let
  val lemma = evaluate_cases |> CONJUNCTS |> el 2
  in CONJ (``evaluate_list a5 a6 a7 [] (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma])
          (``evaluate_list a5 a6 a7 (x::xs) (a9,Rval a10)``
           |> SIMP_CONV (srw_ss()) [Once lemma]) end

(*
val pmatch_add_refs = Q.store_thm("pmatch_add_refs",
  `(∀cenv refs p v env.
    pmatch cenv refs p v env ≠ Match_type_error ⇒
    pmatch cenv (refs ++ refs') p v env = pmatch cenv refs p v env) ∧
   (∀cenv refs ps vs env.
    pmatch_list cenv refs ps vs env ≠ Match_type_error ⇒
    pmatch_list cenv (refs ++ refs') ps vs env = pmatch_list cenv refs ps vs env)`,
   ho_match_mp_tac pmatch_ind
   \\ rw[pmatch_def]
   \\ every_case_tac \\ fs[store_lookup_def,EL_APPEND1]
   \\ rw[]);

val do_app_add_refs = Q.store_thm("do_app_add_refs",
  `do_app (refs,ffi) op args = SOME ((refs2,ffi2),res) ⇒
   do_app (refs++refs',ffi) op args = SOME ((refs2++refs',ffi2),res)`,
  rw[semanticPrimitivesPropsTheory.do_app_cases] \\
  fs[store_alloc_def]
  \\ rw[]
  not true : allocating a reference adds it to the end

val evaluate_add_refs = Q.store_thm("evaluate_add_refs",
  `(∀(s:'ffi state) env es s' res.
     evaluate s env es = (s',res) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
     ∀refs. evaluate (s with refs := s.refs ++ refs) env es =
            (s' with refs := s'.refs ++ refs,res)) ∧
   (∀(s:'ffi state) env v pes errv s' res.
     evaluate_match s env v pes errv = (s',res) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
     ∀refs. evaluate_match (s with refs := s.refs ++ refs) env v pes errv =
            (s' with refs := s'.refs ++ refs,res))`,
  ho_match_mp_tac evaluate_ind
  \\ rw[evaluate_def]
  \\ (
    rpt(split_pair_case_tac \\ fs[]) \\
    rpt (
      qpat_x_assum`_ = (s',_)`mp_tac \\
      TOP_CASE_TAC \\ strip_tac \\ rveq \\
      fs[] \\ rfs[pmatch_add_refs] \\ fs[] \\ rveq
      \\ fs[evaluateTheory.dec_clock_def] ) )
*)

val EvalM_ArrowM = Q.store_thm("EvalM_ArrowM",
  `EvalM env x1 ((a -M-> b) f) ==>
    EvalM env x2 (a x) ==>
    EvalM env (App Opapp [x1;x2]) (b (f x))`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ first_x_assum drule \\ rw[]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum(qspec_then`[]`strip_assume_tac)
  \\ fs[with_same_refs]
  \\ first_x_assum drule \\ rw[]
  \\ asm_exists_tac \\ rw[] \\ fs[]
  \\ asm_exists_tac \\ rw[]
  \\ metis_tac[]);

val EvalM_Fun = Q.store_thm("EvalM_Fun",
  `(!v x. a x v ==> EvalM (write name v env) body (b (f x))) ==>
    EvalM env (Fun name body) ((PURE a -M-> b) f)`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once state_component_equality,HOL_STORE_append]
  \\ rw[Once state_component_equality]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ metis_tac[APPEND_ASSOC]);

val EvalM_Fun_Eq = Q.store_thm("EvalM_Fun_Eq",
  `(!v. a x v ==> EvalM (write name v env) body (b (f x))) ==>
    EvalM env (Fun name body) ((PURE (Eq a x) -M-> b) f)`,
  rw[EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once state_component_equality,HOL_STORE_append]
  \\ rw[Once state_component_equality]
  \\ rw[do_opapp_def,GSYM write_def]
  \\ metis_tac[APPEND_ASSOC]);

val TYPE_TYPE_EXISTS = Q.prove(
  `?ty v. TYPE_TYPE ty v`,
  Q.EXISTS_TAC `Tyvar (strlit [])`
  \\ fs [fetch "-" "TYPE_TYPE_def", STRING_TYPE_def]);

val TERM_TYPE_EXISTS = Q.prove(
  `?tm v. TERM_TYPE tm v`,
  STRIP_ASSUME_TAC TYPE_TYPE_EXISTS
  \\ Q.EXISTS_TAC `Var (strlit []) ty`
  \\ fs [fetch "-" "TERM_TYPE_def",STRING_TYPE_def]
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []);

val HOL_STORE_EXISTS = Q.store_thm("HOL_STORE_EXISTS",
  `?(s:unit state) refs. HOL_STORE s.refs refs`,
  SIMP_TAC std_ss [HOL_STORE_def]
  \\ CONV_TAC (RESORT_EXISTS_CONV List.rev)
  \\ ntac 4 (qexists_tac`Refv (Conv (SOME ("nil",TypeId (Short "list"))) [])`)
  \\ simp[isRefv_def]
  \\ srw_tac[QI_ss][]
  \\ metis_tac[IS_PREFIX_REFL,LIST_TYPE_def]);

val EvalM_Fun_PURE_IMP = Q.store_thm("EvalM_Fun_PURE_IMP",
  `EvalM env (Fun n exp) (PURE P f) ==>
    P f (Closure env n exp)`,
  fs [EvalM_def,PURE_def,PULL_EXISTS,Once evaluate_cases]
  \\ rw [] \\ metis_tac [HOL_STORE_EXISTS])

val LOOKUP_VAR_EvalM_IMP = Q.store_thm("LOOKUP_VAR_EvalM_IMP",
  `(!env. LOOKUP_VAR n env v ==> EvalM env (Var (Short n)) (PURE P g)) ==>
    P g v`,
  fs [LOOKUP_VAR_def,lookup_var_def,EvalM_def,PURE_def,AND_IMP_INTRO,
      Once evaluate_cases,PULL_EXISTS,lookup_var_id_def,PULL_FORALL]
  \\ `ALOOKUP (<|v := [n,v]|>).v n = SOME v` by EVAL_TAC
  \\ metis_tac[HOL_STORE_EXISTS]);

val EvalM_ArrowM_IMP = Q.store_thm("EvalM_ArrowM_IMP",
  `EvalM env (Var x) ((a -M-> b) f) ==>
    Eval env (Var x) (ArrowP a b f)`,
  rw[ArrowM_def,EvalM_def,Eval_def,PURE_def,PULL_EXISTS] \\
  strip_assume_tac HOL_STORE_EXISTS \\
  first_x_assum drule \\
  disch_then(qspec_then`[]`strip_assume_tac) \\
  fs[Once evaluate_cases] \\
  rw[state_component_equality]);

val EvalM_PURE_EQ = Q.store_thm("EvalM_PURE_EQ",
  `EvalM env (Fun n exp) (PURE P x) = Eval env (Fun n exp) (P x)`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_IMP_PURE]
  \\ FULL_SIMP_TAC std_ss [Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ STRIP_ASSUME_TAC HOL_STORE_EXISTS
  \\ first_x_assum drule
  \\ disch_then(qspec_then`[]`strip_assume_tac)
  \\ fs[Once evaluate_cases]
  \\ rw[state_component_equality]);

val EvalM_Var_SIMP = Q.store_thm("EvalM_Var_SIMP",
  `EvalM (write n x env) (Var (Short y)) p =
    if n = y then EvalM (write n x env) (Var (Short y)) p
             else EvalM env (Var (Short y)) p`,
  SIMP_TAC std_ss [EvalM_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,write_def,lookup_var_id_def]);

val EvalM_Recclosure = Q.store_thm("EvalM_Recclosure",
  `(!v. a n v ==>
         EvalM (write name v (write_rec [(fname,name,body)] env2 env2))
               body (b (f n))) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    EvalM env (Var (Short fname)) ((PURE (Eq a n) -M-> b) f)`,
  NTAC 2 STRIP_TAC \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ rw[Eval_def,Arrow_def,EvalM_def,ArrowM_def,PURE_def,ArrowP_def,PULL_EXISTS]
  \\ ntac 2 (pop_assum mp_tac)
  \\ rw[Once evaluate_cases]
  \\ rw[Once evaluate_cases]
  \\ fs[state_component_equality]
  \\ rw[Eq_def,do_opapp_def,Once find_recfun_def,HOL_STORE_append]
  \\ fs[build_rec_env_def,write_rec_def,FOLDR,write_def]
  \\ METIS_TAC[APPEND_ASSOC]);

val IND_HELP = Q.store_thm("IND_HELP",
  `!env cl.
      LOOKUP_VAR x env cl /\
      EvalM env (Var (Short x)) ((b1 -M-> b2) f) ==>
      EvalM (write x cl cl_env) (Var (Short x)) ((b1 -M-> b2) f)`,
  rw[EvalM_def,Eval_def,ArrowM_def,PURE_def,PULL_EXISTS,LOOKUP_VAR_def]
  \\ rw[Once evaluate_cases]
  \\ fs[Once evaluate_cases]
  \\ rfs[lookup_var_id_def,write_def,state_component_equality,lookup_var_def]
  \\ METIS_TAC[]);

val write_rec_one = Q.store_thm("write_rec_one",
  `write_rec [(x,y,z)] env env = write x (Recclosure env [(x,y,z)] x) env`,
  SIMP_TAC std_ss [write_rec_def,write_def,build_rec_env_def,FOLDR]);

(* Eq simps *)

val EvalM_FUN_FORALL = Q.store_thm("EvalM_FUN_FORALL",
  `(!x. EvalM env exp (PURE (p x) f)) ==>
    EvalM env exp (PURE (FUN_FORALL x. p x) f)`,
  rw[EvalM_def,PURE_def]
  \\ first_x_assum drule
  \\ simp[PULL_EXISTS,FUN_FORALL]
  \\ strip_tac
  \\ first_assum(qspecl_then[`ARB`,`junk`]strip_assume_tac)
  \\ asm_exists_tac \\ simp[]
  \\ qx_gen_tac`x`
  \\ first_assum(qspecl_then[`x`,`junk`]strip_assume_tac)
  \\ imp_res_tac determTheory.big_exp_determ \\ fs[]);

val EvalM_FUN_FORALL_EQ = Q.store_thm("EvalM_FUN_FORALL_EQ",
  `(!x. EvalM env exp (PURE (p x) f)) =
    EvalM env exp (PURE (FUN_FORALL x. p x) f)`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [EvalM_FUN_FORALL]
  \\ fs [EvalM_def,PURE_def,PULL_EXISTS,FUN_FORALL] \\ METIS_TAC []);

val M_FUN_FORALL_PUSH1 = Q.prove(
  `(FUN_FORALL x. ArrowP a (PURE (b x))) = (ArrowP a (PURE (FUN_FORALL x. b x)))`,
  rw[FUN_EQ_THM,FUN_FORALL,ArrowP_def,PURE_def,PULL_EXISTS]
  \\ reverse EQ_TAC >- METIS_TAC[] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ first_assum(qspec_then`ARB`strip_assume_tac) \\ fs[]
  \\ fs[state_component_equality]
  \\ qx_gen_tac`junk2`
  \\ first_assum(qspecl_then[`ARB`,`junk2`]strip_assume_tac)
  \\ asm_exists_tac \\ fs[]
  \\ qx_gen_tac`y`
  \\ first_assum(qspecl_then[`y`,`junk2`]strip_assume_tac)
  \\ imp_res_tac determTheory.big_exp_determ \\ fs[]) |> GEN_ALL;

val M_FUN_FORALL_PUSH2 = Q.prove(
  `(FUN_FORALL x. ArrowP ((PURE (a x))) b) =
    (ArrowP (PURE (FUN_EXISTS x. a x)) b)`,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,
    FUN_FORALL,FUN_EXISTS,PURE_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Eq = Q.prove(
  `(FUN_EXISTS x. Eq a x) = a`,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Eq_def]) |> GEN_ALL;

val M_FUN_QUANT_SIMP = save_thm("M_FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Eq,M_FUN_FORALL_PUSH1,M_FUN_FORALL_PUSH2]);

(* failwith *)

val EvalM_failwith = Q.store_thm("EvalM_failwith",
  `!x a.
      (lookup_cons "Fail" env = SOME (1,TypeExn (Long "Kernel" "Fail"))) ==>
      Eval env exp1 (STRING_TYPE x) ==>
      EvalM env (Raise (Con (SOME (Short "Fail")) [exp1]))
        (HOL_MONAD a (failwith x))`,
  rw[Eval_def,EvalM_def,HOL_MONAD_def,failwith_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  rw[Once(CONJUNCT2 evaluate_cases)] >>
  first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac) >>
  IMP_RES_TAC (evaluate_empty_state_IMP
               |> INST_TYPE [``:'ffi``|->``:unit``]) >>
  rw[do_con_check_def,build_conv_def] >>
  fs [lookup_cons_thm] >>
  fs[HOL_EXN_TYPE_def,id_to_n_def] >>
  asm_exists_tac \\ fs[] >>
  METIS_TAC[HOL_STORE_append]);

(* clash *)

val EvalM_raise_clash = Q.store_thm("EvalM_raise_clash",
  `!x a.
      (lookup_cons "Clash" env = SOME (1,TypeExn (Long "Kernel" "Clash"))) ==>
      Eval env exp1 (TERM_TYPE x) ==>
      EvalM env (Raise (Con (SOME (Short "Clash")) [exp1]))
        (HOL_MONAD a (raise_clash x))`,
  rw[Eval_def,EvalM_def,HOL_MONAD_def,raise_clash_def] >>
  rw[Once evaluate_cases] >>
  rw[Once evaluate_cases] >>
  srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  rw[Once(CONJUNCT2 evaluate_cases)] >>
  rw[do_con_check_def,build_conv_def] >>
  fs [lookup_cons_thm] >>
  fs[HOL_EXN_TYPE_def,id_to_n_def] >>
  first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac) >>
  IMP_RES_TAC (evaluate_empty_state_IMP
               |> INST_TYPE [``:'ffi``|->``:unit``]) >>
  fs[] >> asm_exists_tac \\ fs[] >>
  METIS_TAC[HOL_STORE_append]);

(* otherwise *)

val EvalM_otherwise = Q.store_thm("EvalM_otherwise",
  `!n. EvalM env exp1 (HOL_MONAD a x1) ==>
        (!i. EvalM (write n i env) exp2 (HOL_MONAD a x2)) ==>
        EvalM env (Handle exp1 [(Pvar n,exp2)]) (HOL_MONAD a (x1 otherwise x2))`,
  SIMP_TAC std_ss [EvalM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ Q.PAT_X_ASSUM `!s refs. bb ==> bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ Cases_on `res` THEN1
   (srw_tac[DNF_ss][] >> disj1_tac \\
    asm_exists_tac \\ fs[HOL_MONAD_def,otherwise_def] \\
    CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  \\ Q.PAT_X_ASSUM `HOL_MONAD xx yy t1 t2` MP_TAC
  \\ SIMP_TAC std_ss [Once HOL_MONAD_def] \\ STRIP_TAC
  \\ Cases_on `x1 refs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def]
  \\ Cases_on `e` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def]
  \\ srw_tac[DNF_ss][] \\ disj2_tac \\ disj1_tac
  \\ asm_exists_tac \\ fs[]
  \\ simp[Once evaluate_cases,pat_bindings_def,pmatch_def,GSYM write_def]
  \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac`write n v`
  \\ disch_then(qspecl_then[`v`,`[]`]strip_assume_tac)
  \\ fs[with_same_refs]
  \\ asm_exists_tac \\ fs[]
  \\ fs[HOL_MONAD_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ asm_exists_tac \\ fs[]);

(* handle_clash *)

val EvalM_handle_clash = Q.store_thm("EvalM_handle_clash",
  `!n. (lookup_cons "Clash" env = SOME (1,TypeExn (Long "Kernel" "Clash"))) ==>
        EvalM env exp1 (HOL_MONAD a x1) ==>
        (!t v.
          TERM_TYPE t v ==>
          EvalM (write n v env) exp2 (HOL_MONAD a (x2 t))) ==>
        EvalM env (Handle exp1 [(Pcon (SOME (Short "Clash")) [Pvar n],exp2)])
          (HOL_MONAD a (handle_clash x1 x2))`,
  SIMP_TAC std_ss [EvalM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ Q.PAT_X_ASSUM `!s refs. HOL_STORE s.refs refs ==> bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ first_x_assum(qspec_then`junk`strip_assume_tac)
  \\ Cases_on `res` THEN1
   (srw_tac[DNF_ss][] >> disj1_tac \\
    asm_exists_tac \\ fs[HOL_MONAD_def,handle_clash_def] \\
    CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  \\ Q.PAT_X_ASSUM `HOL_MONAD xx yy t1 t2` MP_TAC
  \\ SIMP_TAC std_ss [Once HOL_MONAD_def] \\ STRIP_TAC
  \\ Cases_on `x1 refs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [handle_clash_def]
  \\ Cases_on `e` \\ FULL_SIMP_TAC (srw_ss()) [handle_clash_def]
  \\ srw_tac[boolSimps.DNF_ss][] >> disj2_tac >> disj1_tac
  \\ asm_exists_tac \\ fs[]
  \\ simp[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS,pat_bindings_def]
  \\ Cases_on `h` >> fs[HOL_EXN_TYPE_def] >>
  simp[pmatch_def] >> fs[lookup_cons_thm] >>
  fs[same_tid_def,id_to_n_def,same_ctor_def] >- (
    simp[Once evaluate_cases,HOL_MONAD_def,HOL_EXN_TYPE_def] ) >>
  first_x_assum drule >>
  disch_then drule >>
  simp[GSYM write_def] >>
  disch_then(qspec_then`[]`strip_assume_tac) >>
  fs[with_same_refs] >>
  asm_exists_tac >>
  fs[HOL_MONAD_def] >>
  TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[] \\
  TOP_CASE_TAC \\ fs[]);

(* if *)

val EvalM_If = Q.store_thm("EvalM_If",
  `(a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> EvalM env x2 (a b2)) /\
    (a3 ==> EvalM env x3 (a b3)) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     EvalM env (If x1 x2 x3) (a (if b1 then b2 else b3)))`,
  rpt strip_tac \\ fs[]
  \\ imp_res_tac Eval_IMP_PURE
  \\ fs[EvalM_def,BOOL_def,PURE_def,PULL_EXISTS]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then(qspec_then`junk`strip_assume_tac)
  \\ simp[Once evaluate_cases]
  \\ simp_tac(srw_ss()++DNF_ss)[]
  \\ disj1_tac
  \\ asm_exists_tac
  \\ simp[do_if_def]
  \\ rw[]
  \\ first_x_assum (match_mp_tac o MP_CANON)
  \\ fs[CONTAINER_def]);

val Eval_Var_SIMP2 = Q.store_thm("Eval_Var_SIMP2",
  `Eval (write x i env) (Var (Short y)) p =
      if x = y then p i else Eval env (Var (Short y)) p`,
  SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Eval_def,
       Once evaluate_cases,lookup_var_id_def,write_def]
  \\ simp[state_component_equality]);

val EvalM_Let = Q.store_thm("EvalM_Let",
  `Eval env exp (a res) /\
    (!v. a res v ==> EvalM (write name v env) body (b (f res))) ==>
    EvalM env (Let (SOME name) exp body) (b (LET f res))`,
  rw[]
  \\ imp_res_tac Eval_IMP_PURE
  \\ fs[EvalM_def]
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ disch_then(qspec_then`junk`strip_assume_tac)
  \\ simp[Once evaluate_cases,opt_bind_def,GSYM write_def]
  \\ srw_tac[DNF_ss][]
  \\ fs[PURE_def] \\ rveq
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ asm_exists_tac \\ fs[]);

(* PMATCH *)

val EvalM_PMATCH_NIL = Q.store_thm("EvalM_PMATCH_NIL",
  `!b x xv a.
      Eval env x (a xv) ==>
      CONTAINER F ==>
      EvalM env (Mat x []) (b (PMATCH xv []))`,
  rw[CONTAINER_def]);

val EvalM_PMATCH = Q.store_thm("EvalM_PMATCH",
  `!b a x xv.
      ALL_DISTINCT (pat_bindings p []) ⇒
      (∀v1 v2. pat v1 = pat v2 ⇒ v1 = v2) ⇒
      Eval env x (a xv) ⇒
      (p1 xv ⇒ EvalM env (Mat x ys) (b (PMATCH xv yrs))) ⇒
      EvalPatRel env a p pat ⇒
      (∀env2 vars.
        EvalPatBind env a p pat vars env2 ∧ p2 vars ⇒
        EvalM env2 e (b (res vars))) ⇒
      (∀vars. PMATCH_ROW_COND pat (K T) xv vars ⇒ p2 vars) ∧
      ((∀vars. ¬PMATCH_ROW_COND pat (K T) xv vars) ⇒ p1 xv) ⇒
      EvalM env (Mat x ((p,e)::ys))
        (b (PMATCH xv ((PMATCH_ROW pat (K T) res)::yrs)))`,
  rw[EvalM_def] >>
  imp_res_tac Eval_IMP_PURE >>
  fs[EvalM_def] >>
  rw[Once evaluate_cases,PULL_EXISTS] >> fs[] >>
  first_x_assum drule >>
  disch_then(qspec_then`junk`strip_assume_tac) >>
  fs[PURE_def] \\ rveq \\
  srw_tac[DNF_ss][] \\ disj1_tac \\
  asm_exists_tac \\ fs[] \\
  rw[Once evaluate_cases,PULL_EXISTS] >>
  Cases_on`∃vars. PMATCH_ROW_COND pat (K T) xv vars` >> fs[] >- (
    imp_res_tac pmatch_PMATCH_ROW_COND_Match >>
    pop_assum kall_tac >>
    first_x_assum(qspec_then`s.refs++junk'`strip_assume_tac) \\ fs[] \\
    qpat_x_assum`p1 xv ⇒ $! _`kall_tac >>
    fs[EvalPatRel_def] >>
    first_x_assum(qspec_then`vars`mp_tac)>>simp[] >> strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(qspec_then`s.refs++junk'`mp_tac) >>
    ntac 4 (simp[Once evaluate_cases]) \\ rw[] \\
    fs[PMATCH_ROW_COND_def] \\
    `EvalPatBind env a p pat vars (env with v := env2)`
    by (
      simp[EvalPatBind_def,environment_component_equality] \\
      qspecl_then[`s.refs++junk'`,`p`,`v`,`env`]mp_tac(CONJUNCT1 pmatch_imp_Pmatch) \\
      simp[] \\
      metis_tac[] ) \\
    first_x_assum drule \\ simp[]
    \\ disch_then(qspec_then`s`mp_tac)
    \\ disch_then drule
    \\ disch_then(qspec_then`junk'`strip_assume_tac) \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ simp[PMATCH_def,PMATCH_ROW_def,PMATCH_ROW_COND_def] >>
    `(some x. pat x = pat vars') = SOME vars` by (
      simp[optionTheory.some_def] >>
      METIS_TAC[] ) >>
    simp[] >>
    asm_exists_tac \\ fs[]) >>
  drule (GEN_ALL pmatch_PMATCH_ROW_COND_No_match)
  \\ disch_then drule \\ disch_then drule
  \\ simp[] \\ strip_tac \\
  first_x_assum(qspec_then`s`mp_tac) \\
  disch_then drule \\
  simp[Once evaluate_cases,PULL_EXISTS] \\
  disch_then(qspec_then`junk`mp_tac) \\
  strip_tac \\ imp_res_tac determTheory.big_exp_determ \\ fs[] \\
  rw[] \\ asm_exists_tac \\ fs[] \\
  fs[PMATCH_def,PMATCH_ROW_def] \\
  asm_exists_tac \\ fs[]);

(* read and update refs *)

val read_tac =
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ ntac 6 (rw[Once evaluate_cases])
  \\ fs[HOL_STORE_def,IS_PREFIX_APPEND]
  \\ rw[do_app_def]
  \\ fs[the_type_constants_def,the_term_constants_def,the_axioms_def,the_context_def]
  \\ rw[store_lookup_def,EL_APPEND1,EL_APPEND2]
  \\ fs[isRefv_def]
  \\ srw_tac[DNF_ss][] \\ fs[]
  \\ disj1_tac
  \\ fs[get_the_type_constants_def,get_the_term_constants_def,get_the_axioms_def,get_the_context_def]
  \\ fs[HOL_MONAD_def];

val get_type_constants_thm = Q.store_thm("get_the_type_constants_thm",
  `lookup_var_id (Short "the_type_constants") env = SOME the_type_constants ==>
    EvalM env (App Opderef [Var (Short "the_type_constants")])
      (HOL_MONAD (LIST_TYPE (PAIR_TYPE STRING_TYPE NUM))
                 get_the_type_constants)`,
  read_tac);

val get_term_constants_thm = Q.store_thm("get_the_term_constants_thm",
  `lookup_var_id (Short "the_term_constants") env = SOME the_term_constants ==>
    EvalM env (App Opderef [Var (Short "the_term_constants")])
      (HOL_MONAD (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE))
                 get_the_term_constants)`,
  read_tac);

val get_the_axioms_thm = Q.store_thm("get_the_axioms_thm",
  `lookup_var_id (Short "the_axioms") env = SOME the_axioms ==>
    EvalM env (App Opderef [Var (Short "the_axioms")])
      (HOL_MONAD (LIST_TYPE THM_TYPE) get_the_axioms)`,
  read_tac);

val get_the_context_thm = Q.store_thm("get_the_context_thm",
  `lookup_var_id (Short "the_context") env = SOME the_context ==>
    EvalM env (App Opderef [Var (Short "the_context")])
      (HOL_MONAD (LIST_TYPE UPDATE_TYPE) get_the_context)`,
  read_tac);

val update_tac =
  rw[]
  \\ imp_res_tac Eval_IMP_PURE
  \\ fs[EvalM_def] \\ rw[]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ ntac 3 (rw[Once(CONJUNCT2 evaluate_cases)])
  \\ rw[CONJUNCT1 evaluate_cases |> Q.SPECL[`F`,`env`,`s`,`Var _`]]
  \\ srw_tac[DNF_ss][] \\ disj1_tac
  \\ first_x_assum drule
  \\ disch_then(qspec_then`junk`strip_assume_tac)
  \\ fs[PURE_def] \\ rw[]
  \\ asm_exists_tac \\ fs[]
  \\ rw[do_app_def]
  \\ fs[HOL_STORE_def,IS_PREFIX_APPEND,PULL_EXISTS]
  \\ fs[the_type_constants_def,the_term_constants_def,the_axioms_def,the_context_def]
  \\ fs[store_assign_def,EL_APPEND1,EL_APPEND2,isRefv_def,store_v_same_type_def]
  \\ fs[LUPDATE_APPEND1,LUPDATE_APPEND2,LUPDATE_def]
  \\ fs[HOL_MONAD_def]
  \\ fs[set_the_type_constants_def,set_the_term_constants_def,set_the_axioms_def,set_the_context_def]
  \\ EVAL_TAC;

val set_the_type_constants_thm = Q.store_thm("set_the_type_constants_thm",
  `lookup_var_id (Short "the_type_constants") env = SOME the_type_constants ==>
    Eval env exp (LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) x) ==>
    EvalM env (App Opassign [Var (Short "the_type_constants"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_type_constants x))`,
  update_tac);

val set_the_term_constants_thm = Q.store_thm("set_the_term_constants_thm",
  `lookup_var_id (Short "the_term_constants") env = SOME the_term_constants ==>
    Eval env exp (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE) x) ==>
    EvalM env (App Opassign [Var (Short "the_term_constants"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_term_constants x))`,
  update_tac);

val set_the_axioms_thm = Q.store_thm("set_the_axioms_thm",
  `lookup_var_id (Short "the_axioms") env = SOME the_axioms ==>
    Eval env exp (LIST_TYPE THM_TYPE x) ==>
    EvalM env (App Opassign [Var (Short "the_axioms"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_axioms x))`,
  update_tac);

val set_the_context_thm = Q.store_thm("set_the_context_thm",
  `lookup_var_id (Short "the_context") env = SOME the_context ==>
    Eval env exp (LIST_TYPE UPDATE_TYPE x) ==>
    EvalM env (App Opassign [Var (Short "the_context"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_context x))`,
  update_tac);

val _ = (print_asts := true);

val _ = export_theory();
