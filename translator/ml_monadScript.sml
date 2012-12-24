
open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_monad";

open ml_translatorTheory;
open ml_translatorLib;

open hol_kernelTheory;
open stringTheory listTheory pairTheory;
open MiniMLTheory MiniMLTerminationTheory;

infix \\ val op \\ = op THEN;

(* a few basics *)

val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;

val CHAR_def = Define `
  CHAR (c:char) = NUM (ORD c)`;

val _ = add_type_inv ``CHAR`` ``:num``

val EqualityType_CHAR = prove(
  ``EqualityType CHAR``,
  EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC)
  |> store_eq_thm;

val Eval_Val_CHAR = prove(
  ``n < 256 ==> Eval env (Lit (IntLit (&n))) (CHAR (CHR n))``,
  SIMP_TAC (srw_ss()) [Eval_Val_NUM,CHAR_def])
  |> store_eval_thm;

val Eval_ORD = prove(
  ``!v. ((NUM --> NUM) (\x.x)) v ==> ((CHAR --> NUM) ORD) v``,
  SIMP_TAC std_ss [Arrow_def,AppReturns_def,CHAR_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\x.x:num``))
  |> store_eval_thm;

val Eval_CHR = prove(
  ``!v. ((NUM --> NUM) (\n. n MOD 256)) v ==>
        ((NUM --> CHAR) (\n. CHR (n MOD 256))) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,CHAR_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\n. n MOD 256``))
  |> store_eval_thm;

val Eval_CHAR_LT = prove(
  ``!v. ((NUM --> NUM --> BOOL) (\m n. m < n)) v ==>
        ((CHAR --> CHAR --> BOOL) char_lt) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,CHAR_def,char_lt_def]
  \\ METIS_TAC [])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\m n. m < n:num``))
  |> store_eval_thm;

(*
val res = translate string_lt_def;
val res = translate string_le_def;
val res = translate string_gt_def;
val res = translate string_ge_def;
*)

(* construct type refinement invariants *)

val _ = register_type ``:hol_type``;

val MEM_hol_type_size = prove(
  ``!ts t. MEM t ts ==> hol_type_size t < hol_type1_size ts``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val hol_type_ind = store_thm("hol_type_ind",
  ``(!s ts. (!t. MEM t ts ==> P t) ==> P (Tyapp s ts)) /\
    (!v. P (Tyvar v)) ==> !x. P x``,
  REPEAT STRIP_TAC \\ completeInduct_on `hol_type_size x`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!x1 x2. bb` MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ EVAL_TAC \\ IMP_RES_TAC MEM_hol_type_size \\ DECIDE_TAC);

val LIST_TYPE_def = fetch "-" "LIST_TYPE_def"
val HOL_TYPE_TYPE_def = fetch "-" "HOL_TYPE_TYPE_def"

val LIST_TYPE_NO_CLOSURES = prove(
  ``!xs v.
      (!x v. MEM x xs /\ p x v ==> no_closures v) /\
      LIST_TYPE p xs v ==> no_closures v``,
  Induct \\ FULL_SIMP_TAC std_ss [LIST_TYPE_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF,MEM]
  \\ METIS_TAC []);

val LIST_TYPE_11 = prove(
  ``!P ts v1 us v2.
      (!x1.
       MEM x1 ts ==>
        !v1 x2 v2.
          P x1 v1 /\ P x2 v2 ==>
          ((v1 = v2) <=> (x1 = x2))) /\
    LIST_TYPE P ts v1 /\ LIST_TYPE P us v2 ==>
    ((v1 = v2) = (ts = us))``,
  STRIP_TAC \\ Induct \\ Cases_on `us` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [LIST_TYPE_def]
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] \\ METIS_TAC []);

val CHAR_IMP_no_closures = prove(
  ``CHAR x v ==> no_closures v``,
  SIMP_TAC std_ss [CHAR_def,NUM_def,INT_def,no_closures_def]);

val EqualityType_HOL_TYPE = prove(
  ``EqualityType HOL_TYPE_TYPE``,
  SIMP_TAC std_ss [EqualityType_def] \\ STRIP_TAC THEN1
   (HO_MATCH_MP_TAC hol_type_ind
    \\ FULL_SIMP_TAC std_ss [HOL_TYPE_TYPE_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF]
    \\ IMP_RES_TAC (LIST_TYPE_NO_CLOSURES |> GEN_ALL)
    \\ METIS_TAC [CHAR_IMP_no_closures])
  \\ HO_MATCH_MP_TAC hol_type_ind \\ REVERSE (REPEAT STRIP_TAC)
  \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [HOL_TYPE_TYPE_def]
  THEN1 (MATCH_MP_TAC (LIST_TYPE_11 |> Q.ISPEC `CHAR`)
         \\ FULL_SIMP_TAC (srw_ss()) [CHAR_def,INT_def,NUM_def,ORD_11])
  \\ `(v2_1 = v2_1') = (s = s')` by ALL_TAC
  THEN1 (MATCH_MP_TAC (LIST_TYPE_11 |> Q.ISPEC `CHAR`)
         \\ FULL_SIMP_TAC (srw_ss()) [CHAR_def,INT_def,NUM_def,ORD_11])
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `s = s'`
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LIST_TYPE_11 \\ METIS_TAC [])
  |> store_eq_thm;

val _ = register_type ``:term``;
val _ = register_type ``:thm``;
val _ = register_type ``:def``;

(*
  fetch "-" "PAIR_TYPE_def";
  fetch "-" "LIST_TYPE_def";
  fetch "-" "HOL_TYPE_TYPE_def";
  fetch "-" "TERM_TYPE_def";
  fetch "-" "THM_TYPE_def";
*)

val U_TYPE_def = Define `
  U_TYPE (u:unit) v = (v = Litv Unit)`;

(* definition of EvalM *)

val HOL_STORE_def = Define `
  HOL_STORE s refs =
    5 <= LENGTH s /\
    (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM)) refs.the_type_constants (EL 0 s) /\
    (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE)) refs.the_term_constants (EL 1 s) /\
    (LIST_TYPE THM_TYPE refs.the_axioms) (EL 2 s) /\
    (LIST_TYPE DEF_TYPE refs.the_definitions) (EL 3 s) /\
    (TERM_TYPE refs.the_clash_var) (EL 4 s)`;

val EvalM_def = Define `
  EvalM env exp P <=>
    !s refs. HOL_STORE s refs ==>
             ?s2 res refs2. evaluate' s env exp (s2,res) /\
                            P (refs,s) (refs2,s2,res) /\ HOL_STORE s2 refs2`;

(* refinement invariant for ``:'a M`` *)

val HOL_MONAD_def = Define `
  HOL_MONAD (a:'a->v->bool) (x:'a M) (state1:hol_refs,s1:store)
                                     (state2:hol_refs,s2:store,res) =
    case (x state1, res) of
      ((HolRes y, state), Rval v) => (state = state2) /\ a y v
    | ((HolErr e, state), Rerr _) => (state = state2)
    | _ => F`

(* return *)

val EvalM_return = store_thm("EvalM_return",
  ``Eval env exp (a x) ==>
    EvalM env exp (HOL_MONAD a (ex_return x))``,
  SIMP_TAC std_ss [Eval_def,EvalM_def,HOL_MONAD_def,ex_return_def]
  \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`s`,`Rval res`,`refs`]
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate'_empty_store_IMP]);

(* bind *)

val EvalM_bind = store_thm("EvalM_bind",
  ``EvalM env e1 (HOL_MONAD b (x:'b M)) /\
    (!x v. b x v ==> EvalM ((name,v,NONE)::env) e2 (HOL_MONAD a ((f x):'a M))) ==>
    EvalM env (Let NONE name NONE e1 e2) (HOL_MONAD a (ex_bind x f))``,
  SIMP_TAC std_ss [EvalM_def,HOL_MONAD_def,ex_return_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ RES_TAC
  \\ Cases_on `x refs` \\ Cases_on `q`
  \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x refs = (HolRes res1,r)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate' s env e1 (q,Rval (state1))` []
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`res1`,`state1`,`q`,`r`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`s2'`,`res`,`refs2'`]
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
     (ONCE_REWRITE_TAC [evaluate'_cases]
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ DISJ1_TAC
      \\ Q.LIST_EXISTS_TAC [`state1`,`q`]
      \\ ASM_SIMP_TAC std_ss [bind_def,add_tvs_def])
    \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def])
  THEN1
   (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x refs = (HolErr res1,r)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate' s env e1 (q,Rerr (state1))` []
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ Q.LIST_EXISTS_TAC [`q`,`Rerr state1`,`refs2`]
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def]));

(* function abstraction and application *)

val any_evaluate_closure_def = Define `
  any_evaluate_closure (s1,input) cl (s2,output) =
     ?env exp.
       (do_app s1 ARB Opapp cl input = SOME (s1,env,exp)) /\
       evaluate' s1 env exp (s2,output)`

val _ = type_abbrev("H",``:'a -> hol_refs # store ->
                                 hol_refs # store # v result -> bool``);

val PURE_def = Define `
  PURE a x (refs1:hol_refs,s1:store) (refs2,s2,res) =
    ?v:v. (res = Rval v) /\ (refs1 = refs2) /\ (s1 = s2) /\ a x v`;

val ArrowP_def = Define `
  (ArrowP : 'a H -> 'b H -> ('a -> 'b) -> v -> bool) a b f c =
     !x refs1 s1 refs2 s2 res.
       a x (refs1,s1) (refs2,s2,res) /\ HOL_STORE s1 refs1 ==>
       (refs2 = refs1) /\ (s2 = s1) /\
       ?v s3 res3 refs3.
         (res = Rval v) /\ any_evaluate_closure (s2,v) c (s3,res3) /\
         b (f x) (refs1,s1) (refs3,s3,res3) /\ HOL_STORE s3 refs3`;

val ArrowM_def = Define `
  (ArrowM : 'a H -> 'b H -> ('a -> 'b) H) a b = PURE (ArrowP a b)`;

val _ = add_infix("-M->",400,HOLgrammars.RIGHT)
val _ = overload_on ("-M->",``ArrowM``)

val EvalM_ArrowM = store_thm("EvalM_ArrowM",
  ``EvalM env x1 ((a -M-> b) f) ==>
    EvalM env x2 (a x) ==>
    EvalM env (App Opapp x1 x2) (b (f x))``,
  SIMP_TAC std_ss [EvalM_def,ArrowM_def,ArrowP_def,PURE_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ASSUM `!s. bbb` MP_TAC
  \\ Q.PAT_ASSUM `!s. bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ STRIP_TAC
  \\ `!x. evaluate' s env x1 x = (x = (s,Rval v))` by
       METIS_TAC [big_exp_determ']
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.PAT_ASSUM `!s. bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ RES_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ NTAC 4 (POP_ASSUM (K ALL_TAC))
  \\ `!x. evaluate' s env x2 x = (x = (s2,res))` by
       METIS_TAC [big_exp_determ']
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.LIST_EXISTS_TAC [`s3`,`res3`,`refs3`] \\ FULL_SIMP_TAC std_ss []
  \\ DISJ1_TAC \\ FULL_SIMP_TAC std_ss [any_evaluate_closure_def]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def] \\ METIS_TAC []);

val EvalM_Fun = store_thm("EvalM_Fun",
  ``(!v x. a x v ==> EvalM ((name,v,NONE)::env) body (b (f x))) ==>
    EvalM env (Fun name NONE body) ((PURE a -M-> b) f)``,
  SIMP_TAC std_ss [EvalM_def,ArrowM_def,ArrowP_def,PURE_def]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_FORALL]
  \\ SIMP_TAC (srw_ss()) [any_evaluate_closure_def,do_app_def,bind_def,add_tvs_def]
  \\ METIS_TAC []);

val EvalM_Fun_Eq = store_thm("EvalM_Fun_Eq",
  ``(!v. a x v ==> EvalM ((name,v,NONE)::env) body (b (f x))) ==>
    EvalM env (Fun name NONE body) ((PURE (Eq a x) -M-> b) f)``,
  SIMP_TAC std_ss [EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_FORALL]
  \\ SIMP_TAC (srw_ss()) [any_evaluate_closure_def,do_app_def,bind_def,add_tvs_def]
  \\ METIS_TAC []);

val Eval_IMP_PURE = store_thm("Eval_IMP_PURE",
  ``Eval env exp (P x) ==> EvalM env exp (PURE P x)``,
  SIMP_TAC std_ss [Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `res`
  \\ ASM_SIMP_TAC std_ss [evaluate'_empty_store_IMP]);

val HOL_TYPE_TYPE_EXISTS = prove(
  ``?ty v. HOL_TYPE_TYPE ty v``,
  Q.EXISTS_TAC `Tyvar []`
  \\ SIMP_TAC std_ss [fetch "-" "HOL_TYPE_TYPE_def",fetch "-" "LIST_TYPE_def"]);

val TERM_TYPE_EXISTS = prove(
  ``?tm v. TERM_TYPE tm v``,
  STRIP_ASSUME_TAC HOL_TYPE_TYPE_EXISTS
  \\ Q.EXISTS_TAC `Var [] ty`
  \\ SIMP_TAC std_ss [fetch "-" "TERM_TYPE_def",fetch "-" "LIST_TYPE_def"]
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []);

val HOL_STORE_EXISTS = prove(
  ``?s refs. HOL_STORE s refs``,
  SIMP_TAC std_ss [HOL_STORE_def]
  \\ STRIP_ASSUME_TAC TERM_TYPE_EXISTS
  \\ Q.EXISTS_TAC `[Conv "Nil" [];Conv "Nil" [];Conv "Nil" [];
                    Conv "Nil" [];v]`
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,EL,HD,TL]
  \\ Q.EXISTS_TAC `<| the_axioms := []; the_type_constants := [] ;
                      the_term_constants := []; the_definitions := [];
                      the_clash_var := tm |>`
  \\ FULL_SIMP_TAC (srw_ss()) [fetch "-" "LIST_TYPE_def"]);

val EvalM_PURE_EQ = store_thm("EvalM_PURE_EQ",
  ``EvalM env (Fun n t exp) (PURE P x) = Eval env (Fun n t exp) (P x)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_IMP_PURE]
  \\ FULL_SIMP_TAC std_ss [Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ STRIP_ASSUME_TAC HOL_STORE_EXISTS \\ RES_TAC
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) []);

val EvalM_Var_SIMP = store_thm("EvalM_Var_SIMP",
  ``EvalM ((n,v,x)::env) (Var t y) p =
    if n = t then EvalM ((n,v,x)::env) (Var t y) p else EvalM env (Var t y) p``,
  SIMP_TAC std_ss [EvalM_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases]);

val option_CASE_LEMMA2 = prove(
  ``!topt. (case topt of NONE => v | SOME (t,y) => v) = v``,
  Cases \\ SRW_TAC [] [] \\ Cases_on `x` \\ SRW_TAC [] []);

val EvalM_Recclosure = store_thm("EvalM_Recclosure",
  ``(!v. a n v ==>
  EvalM ((name,v,NONE)::(fname,Recclosure env2 [(fname,NONE,name,NONE,body)] fname,NONE)::env2) body (b (f n))) ==>
    Eval env (Var fname NONE) ($= (Recclosure env2 [(fname,NONE,name,NONE,body)] fname)) ==>
    EvalM env (Var fname NONE) ((PURE (Eq a n) -M-> b) f)``,
  FULL_SIMP_TAC std_ss [Eval_def,Arrow_def,EvalM_def,ArrowM_def,PURE_def,
    PULL_EXISTS,ArrowP_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [AppReturns_def,Eq_def,
       do_app_def,evaluate_closure_def,any_evaluate_closure_def,
       do_tapp_def,option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [Once find_recfun_def,Eval_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bind_def,build_rec_env_def,FOLDR,add_tvs_def]);

val IND_HELP = store_thm("IND_HELP",
  ``!env cl.
      Eval env (Var x NONE) ($= cl) /\
      EvalM env (Var x NONE) ((b1 -M-> b2) f) ==>
      EvalM ((x,cl,z)::cl_env) (Var x NONE) ((b1 -M-> b2) f)``,
  SIMP_TAC std_ss [EvalM_def,Eval_def,ArrowM_def,PURE_def,PULL_EXISTS]
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [do_tapp_def,option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []);

(* Eq simps *)

val EvalM_FUN_FORALL = store_thm("EvalM_FUN_FORALL",
  ``(!x. EvalM env exp (PURE (p x) f)) ==>
    EvalM env exp (PURE (FUN_FORALL x. p x) f)``,
  SIMP_TAC std_ss [EvalM_def,Eq_def,PURE_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AppReturns_def,FUN_FORALL,PULL_EXISTS]
  \\ RES_TAC \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `ARB`)
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ `!x. evaluate' s env exp x = (x = (s,Rval v))` by METIS_TAC [big_exp_determ']
  \\ FULL_SIMP_TAC (srw_ss()) []);

val EvalM_FUN_FORALL_EQ = store_thm("EvalM_FUN_FORALL_EQ",
  ``(!x. EvalM env exp (PURE (p x) f)) =
    EvalM env exp (PURE (FUN_FORALL x. p x) f)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [EvalM_FUN_FORALL]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [FUN_FORALL] \\ METIS_TAC []);

val M_FUN_FORALL_PUSH1 = prove(
  ``(FUN_FORALL x. ArrowP a (PURE (b x))) = (ArrowP a (PURE (FUN_FORALL x. b x)))``,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL,
    Eval_def,any_evaluate_closure_def,PURE_def] \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC
  THEN1 METIS_TAC [evaluate_11_Rval]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ POP_ASSUM (fn th => STRIP_ASSUME_TAC (Q.SPEC `ARB` th) THEN ASSUME_TAC th)
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC
  \\ Q.PAT_ASSUM `s2 = s3` ASSUME_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `!x. evaluate' s3 env exp x = (x = (s3,Rval v))`
       by METIS_TAC [big_exp_determ'] \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`refs3`,`v`]
  \\ FULL_SIMP_TAC std_ss []) |> GEN_ALL;

val M_FUN_FORALL_PUSH2 = prove(
  ``(FUN_FORALL x. ArrowP ((PURE (a x))) b) =
    (ArrowP (PURE (FUN_EXISTS x. a x)) b)``,
  FULL_SIMP_TAC std_ss [ArrowP_def,FUN_EQ_THM,AppReturns_def,
    FUN_FORALL,FUN_EXISTS,PURE_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Eq = prove(
  ``(FUN_EXISTS x. Eq a x) = a``,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Eq_def]) |> GEN_ALL;

val M_FUN_QUANT_SIMP = save_thm("M_FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Eq,M_FUN_FORALL_PUSH1,M_FUN_FORALL_PUSH2]);

(* failwith *)

val EvalM_failwith = store_thm("EvalM_failwith",
  ``!x a. EvalM env (Raise (Int_error 0)) (HOL_MONAD a (failwith x))``,
  SIMP_TAC (srw_ss()) [Eval_def,EvalM_def,HOL_MONAD_def,failwith_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) [] );

(* if *)

val EvalM_If = store_thm("EvalM_If",
  ``(a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> EvalM env x2 (a b2)) /\
    (a3 ==> EvalM env x3 (a b3)) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     EvalM env (If x1 x2 x3) (a (if b1 then b2 else b3)))``,
  SIMP_TAC std_ss [EvalM_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss [CONTAINER_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `b1` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  THEN1
   (Q.LIST_EXISTS_TAC [`s2`,`res`,`refs2`] \\ ASM_SIMP_TAC std_ss []
    \\ DISJ1_TAC
    \\ Q.EXISTS_TAC `Litv (Bool T)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
    \\ Q.EXISTS_TAC `s` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [Eval_def,evaluate'_empty_store_IMP])
  THEN1
   (Q.LIST_EXISTS_TAC [`s2`,`res`,`refs2`] \\ ASM_SIMP_TAC std_ss []
    \\ DISJ1_TAC
    \\ Q.EXISTS_TAC `Litv (Bool F)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
    \\ Q.EXISTS_TAC `s` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [Eval_def,evaluate'_empty_store_IMP]));

(* declarations *)

val M_DeclAssum_Dlet_INTRO = store_thm("M_DeclAssum_Dlet_INTRO",
  ``(!env. DeclAssum ds env ==> EvalM env (Fun n tt exp) (PURE P x)) ==>
    (!v env. DeclAssum (SNOC (Dlet NONE (Pvar v NONE) (Fun n tt exp)) ds) env ==>
             EvalM env (Var v NONE) (PURE P x))``,
  METIS_TAC [DeclAssum_Dlet_INTRO,EvalM_PURE_EQ,Eval_IMP_PURE]);

val M_DeclAssum_Dletrec_INTRO = store_thm("M_DeclAssum_Dletrec_INTRO",
  ``(!env1 env.
      DeclAssum ds env /\ (lookup v env1 = SOME (Recclosure env [(v,NONE,xs,NONE,f)] v,NONE)) ==>
      EvalM env1 (Var v NONE) (PURE P x)) ==>
    !env. DeclAssum (SNOC (Dletrec NONE [(v,NONE,xs,NONE,f)]) ds) env ==>
          EvalM env (Var v NONE) (PURE P x)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec,
    MAP,ALL_DISTINCT,MEM,PULL_EXISTS,build_rec_env_def,FOLDR,bind_def,Eval_Var_SIMP]
  \\ FULL_SIMP_TAC std_ss [EvalM_def,PURE_def,PULL_EXISTS]
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [do_tapp_def,add_tvs_def] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!env1.bbb` (MP_TAC o Q.SPEC `bind v (Recclosure env2 [(v,NONE,xs,NONE,f)] v,NONE) env`)
  \\ FULL_SIMP_TAC (srw_ss()) [lookup_def,bind_def,add_tvs_def] \\ METIS_TAC []);

(* some pure functions *)

(*
val res = translate listTheory.MAP;
val res = translate MEMBER_def;
val res = translate listTheory.EVERY_DEF;
val res = translate listTheory.EXISTS_DEF;
val res = translate listTheory.FILTER;
val res = translate listTheory.APPEND;
val res = translate (subset_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (subtract_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (insert_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate itlist_def;
val res = translate union_def;
val res = translate mk_vartype_def;
val res = translate is_type_def;
val res = translate is_vartype_def;
val res = translate rev_assocd_def;
val res = translate hol_kernelTheory.type_subst_def;
val res = translate aty_def;
val res = translate bty_def;
val res = translate alphavars_def;
val res = translate raconv_def;
val res = translate aconv_def;
val res = translate is_var_def;
val res = translate is_const_def;
val res = translate is_abs_def;
val res = translate is_comb_def;
val res = translate mk_var_def;
val res = translate frees_def;
val res = translate combinTheory.o_DEF;
val res = translate fressl_def;
val res = translate (freesin_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate vfree_in_def;
val res = translate tyvars_def;
val res = translate type_vars_in_term_def;
val res = translate variant_def;
val res = translate vsubst_aux_def;
val res = translate inst_var_def;
val res = translate is_eq_def;
val res = translate term_remove_def;
val res = translate term_union_def;
val res = translate dest_thm_def;
val res = translate hyp_def;
val res = translate concl_def;
*)

(* fastish evaluation *)

val evaluate'_SIMP =
  [``evaluate' a0 a1 (Letrec o' l e) a3``,
   ``evaluate' a0 a1 (Let o0 s o' e e0) a3``,
   ``evaluate' a0 a1 (Mat e l) a3``,
   ``evaluate' a0 a1 (If e e0 e1) a3``,
   ``evaluate' a0 a1 (Log l e e0) a3``,
   ``evaluate' a0 a1 (App o' e e0) a3``,
   ``evaluate' a0 a1 (Uapp u e) a3``,
   ``evaluate' a0 a1 (Fun s o' e) a3``,
   ``evaluate' a0 a1 (Var s o') a3``,
   ``evaluate' a0 a1 (Con s l) a3``,
   ``evaluate' a0 a1 (Lit l) a3``,
   ``evaluate' a0 a1 (Handle e s e0) a3``,
   ``evaluate' a0 a1 (Raise e) a3``,
   ``evaluate_list' a0 a1 [] a3``,
   ``evaluate_list' a0 a1 (h::t) a3``]
  |> map (SIMP_CONV (srw_ss()) [Once evaluate'_cases])
  |> LIST_CONJ;

(* ref 1 *)

val lemma =
  hol2deep ``[]:string list``
  |> DISCH_ALL |> SIMP_RULE std_ss []
val exp = lemma |> concl |> rator |> rand
val dec = ``Dlet NONE (Pvar n NONE) (Uapp Opref ^exp)``

val tm = get_DeclAssum () |> rator |> rand;
val tm_eval = tm |> REWRITE_CONV (map (fetch "-") ["ml_monad_decls_5",
                                                   "ml_monad_decls_4",
                                                   "ml_monad_decls_3",
                                                   "ml_monad_decls_2",
                                                   "ml_monad_decls_1",
                                                   "ml_monad_decls_0"] @
                                  [APPEND,SNOC_APPEND])

val the_type_constants_def = Define `
  the_type_constants = Loc 0`;

val th = prove(
  ``DeclAssum (SNOC ^dec ^tm) env ==>
    Eval env (Var n NONE) ($= the_type_constants)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,empty_store_def]
  \\ SIMP_TAC std_ss [tm_eval,the_type_constants_def]
  \\ NTAC 10 (ONCE_REWRITE_TAC [Decls_CONS]
              \\ SIMP_TAC std_ss [Decls_Dtype,Decls_Dlet,Decls_NIL])
  \\ SIMP_TAC (srw_ss()) [evaluate'_SIMP,PULL_EXISTS,do_uapp_def,
       LET_DEF,store_alloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_ASSUM `check_dup_ctors xx yy` (K ALL_TAC))
  \\ SIMP_TAC std_ss [bind_def,Eval_def,empty_store_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once lookup_def,bind_def,do_tapp_def])
  |> Q.INST [`n`|->`"the_type_constants"`] |> UNDISCH;

val th = store_cert th TRUTH

(* ref 2 *)

val lemma =
  hol2deep ``[]:(string # hol_type) list``
  |> DISCH_ALL |> SIMP_RULE std_ss []
val exp = lemma |> concl |> rator |> rand
val dec = ``Dlet NONE (Pvar n NONE) (Uapp Opref ^exp)``

val tm = get_DeclAssum () |> rator |> rand;
val tm_eval = tm |> REWRITE_CONV (map (fetch "-") ["ml_monad_decls_6",
                                                   "ml_monad_decls_5",
                                                   "ml_monad_decls_4",
                                                   "ml_monad_decls_3",
                                                   "ml_monad_decls_2",
                                                   "ml_monad_decls_1",
                                                   "ml_monad_decls_0"] @
                                  [APPEND,SNOC_APPEND])

val the_term_constants_def = Define `
  the_term_constants = Loc 1`;

val th = prove(
  ``DeclAssum (SNOC ^dec ^tm) env ==>
    Eval env (Var n NONE) ($= the_term_constants)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,empty_store_def]
  \\ SIMP_TAC std_ss [tm_eval,the_term_constants_def]
  \\ NTAC 10 (ONCE_REWRITE_TAC [Decls_CONS]
              \\ SIMP_TAC std_ss [Decls_Dtype,Decls_Dlet,Decls_NIL])
  \\ SIMP_TAC (srw_ss()) [evaluate'_SIMP,PULL_EXISTS,do_uapp_def,
       LET_DEF,store_alloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_ASSUM `check_dup_ctors xx yy` (K ALL_TAC))
  \\ SIMP_TAC std_ss [bind_def,Eval_def,empty_store_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once lookup_def,bind_def,do_tapp_def])
  |> Q.INST [`n`|->`"the_term_constants"`] |> UNDISCH;

val th = store_cert th TRUTH

(* ref 3 *)

val lemma =
  hol2deep ``[]:thm list``
  |> DISCH_ALL |> SIMP_RULE std_ss []
val exp = lemma |> concl |> rator |> rand
val dec = ``Dlet NONE (Pvar n NONE) (Uapp Opref ^exp)``

val tm = get_DeclAssum () |> rator |> rand;
val tm_eval = tm |> REWRITE_CONV (map (fetch "-") ["ml_monad_decls_7",
                                                   "ml_monad_decls_6",
                                                   "ml_monad_decls_5",
                                                   "ml_monad_decls_4",
                                                   "ml_monad_decls_3",
                                                   "ml_monad_decls_2",
                                                   "ml_monad_decls_1",
                                                   "ml_monad_decls_0"] @
                                  [APPEND,SNOC_APPEND])

val the_axioms_def = Define `
  the_axioms = Loc 2`;

val th = prove(
  ``DeclAssum (SNOC ^dec ^tm) env ==>
    Eval env (Var n NONE) ($= the_axioms)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,empty_store_def]
  \\ SIMP_TAC std_ss [tm_eval,the_axioms_def]
  \\ NTAC 10 (ONCE_REWRITE_TAC [Decls_CONS]
              \\ SIMP_TAC std_ss [Decls_Dtype,Decls_Dlet,Decls_NIL])
  \\ SIMP_TAC (srw_ss()) [evaluate'_SIMP,PULL_EXISTS,do_uapp_def,
       LET_DEF,store_alloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_ASSUM `check_dup_ctors xx yy` (K ALL_TAC))
  \\ SIMP_TAC std_ss [bind_def,Eval_def,empty_store_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once lookup_def,bind_def,do_tapp_def])
  |> Q.INST [`n`|->`"the_axioms"`] |> UNDISCH;

val th = store_cert th TRUTH

(* ref 4 *)

val lemma =
  hol2deep ``[]:def list``
  |> DISCH_ALL |> SIMP_RULE std_ss []
val exp = lemma |> concl |> rator |> rand
val dec = ``Dlet NONE (Pvar n NONE) (Uapp Opref ^exp)``

val tm = get_DeclAssum () |> rator |> rand;
val tm_eval = tm |> REWRITE_CONV (map (fetch "-") ["ml_monad_decls_8",
                                                   "ml_monad_decls_7",
                                                   "ml_monad_decls_6",
                                                   "ml_monad_decls_5",
                                                   "ml_monad_decls_4",
                                                   "ml_monad_decls_3",
                                                   "ml_monad_decls_2",
                                                   "ml_monad_decls_1",
                                                   "ml_monad_decls_0"] @
                                  [APPEND,SNOC_APPEND])

val the_definitions_def = Define `
  the_definitions = Loc 3`;

val th = prove(
  ``DeclAssum (SNOC ^dec ^tm) env ==>
    Eval env (Var n NONE) ($= the_definitions)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,empty_store_def]
  \\ SIMP_TAC std_ss [tm_eval,the_definitions_def]
  \\ NTAC 10 (ONCE_REWRITE_TAC [Decls_CONS]
              \\ SIMP_TAC std_ss [Decls_Dtype,Decls_Dlet,Decls_NIL])
  \\ SIMP_TAC (srw_ss()) [evaluate'_SIMP,PULL_EXISTS,do_uapp_def,
       LET_DEF,store_alloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_ASSUM `check_dup_ctors xx yy` (K ALL_TAC))
  \\ SIMP_TAC std_ss [bind_def,Eval_def,empty_store_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once lookup_def,bind_def,do_tapp_def])
  |> Q.INST [`n`|->`"the_definitions"`] |> UNDISCH;

val th = store_cert th TRUTH

(* ref 5 *)

val lemma =
  hol2deep ``Var "a" (Tyvar "a")``
  |> DISCH_ALL |> SIMP_RULE std_ss []
val exp = lemma |> concl |> rator |> rand
val dec = ``Dlet NONE (Pvar n NONE) (Uapp Opref ^exp)``

val tm = get_DeclAssum () |> rator |> rand;
val tm_eval = tm |> REWRITE_CONV (map (fetch "-") ["ml_monad_decls_9",
                                                   "ml_monad_decls_8",
                                                   "ml_monad_decls_7",
                                                   "ml_monad_decls_6",
                                                   "ml_monad_decls_5",
                                                   "ml_monad_decls_4",
                                                   "ml_monad_decls_3",
                                                   "ml_monad_decls_2",
                                                   "ml_monad_decls_1",
                                                   "ml_monad_decls_0"] @
                                  [APPEND,SNOC_APPEND])

val the_clash_var_def = Define `
  the_clash_var = Loc 4`;

val th = prove(
  ``DeclAssum (SNOC ^dec ^tm) env ==>
    Eval env (Var n NONE) ($= the_clash_var)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,empty_store_def]
  \\ SIMP_TAC std_ss [tm_eval,the_clash_var_def]
  \\ NTAC 10 (ONCE_REWRITE_TAC [Decls_CONS]
              \\ SIMP_TAC std_ss [Decls_Dtype,Decls_Dlet,Decls_NIL])
  \\ SIMP_TAC (srw_ss()) [evaluate'_SIMP,PULL_EXISTS,do_uapp_def,
       LET_DEF,store_alloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (Q.PAT_ASSUM `check_dup_ctors xx yy` (K ALL_TAC))
  \\ SIMP_TAC std_ss [bind_def,Eval_def,empty_store_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [Once lookup_def,bind_def,do_tapp_def])
  |> Q.INST [`n`|->`"the_clash_var"`] |> UNDISCH;

val th = store_cert th TRUTH


(* read and update refs *)

fun read_tac n =
  SIMP_TAC std_ss [Eval_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [do_tapp_def,option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [EvalM_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [the_type_constants_def,
       the_term_constants_def,the_axioms_def,the_definitions_def,
       the_clash_var_def]
  \\ SIMP_TAC (srw_ss()) [do_uapp_def,store_lookup_def,do_tapp_def,
        option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [HOL_STORE_def]
  \\ `0 < LENGTH s` by DECIDE_TAC
  \\ `1 < LENGTH s` by DECIDE_TAC
  \\ `2 < LENGTH s` by DECIDE_TAC
  \\ `3 < LENGTH s` by DECIDE_TAC
  \\ `4 < LENGTH s` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`s`,`Rval (EL ^n s)`,`refs`]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [HOL_MONAD_def,get_the_type_constants_def,
        get_the_term_constants_def,get_the_axioms_def,get_the_clash_var_def,
        get_the_definitions_def,do_tapp_def,EL];

val get_type_constants_thm = store_thm("get_type_constants_thm",
  ``Eval env (Var "the_type_constants" NONE) ($= the_type_constants) ==>
    EvalM env (Uapp Opderef (Var "the_type_constants" NONE))
      (HOL_MONAD (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM))
                 get_the_type_constants)``,
  read_tac ``0:num``);

val get_term_constants_thm = store_thm("get_term_constants_thm",
  ``Eval env (Var "the_term_constants" NONE) ($= the_term_constants) ==>
    EvalM env (Uapp Opderef (Var "the_term_constants" NONE))
      (HOL_MONAD (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE))
                 get_the_term_constants)``,
  read_tac ``1:num``);

val get_the_axioms_thm = store_thm("get_the_axioms_thm",
  ``Eval env (Var "the_axioms" NONE) ($= the_axioms) ==>
    EvalM env (Uapp Opderef (Var "the_axioms" NONE))
      (HOL_MONAD (LIST_TYPE THM_TYPE) get_the_axioms)``,
  read_tac ``2:num``);

val get_the_definitions_thm = store_thm("get_the_definitions_thm",
  ``Eval env (Var "the_definitions" NONE) ($= the_definitions) ==>
    EvalM env (Uapp Opderef (Var "the_definitions" NONE))
      (HOL_MONAD (LIST_TYPE DEF_TYPE) get_the_definitions)``,
  read_tac ``3:num``);

val get_the_clash_var_thm = store_thm("get_the_clash_var_thm",
  ``Eval env (Var "the_clash_var" NONE) ($= the_clash_var) ==>
    EvalM env (Uapp Opderef (Var "the_clash_var" NONE))
      (HOL_MONAD TERM_TYPE get_the_clash_var)``,
  read_tac ``4:num``);

fun update_tac r q =
  SIMP_TAC std_ss [Once Eval_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [do_tapp_def,option_CASE_LEMMA2]
  \\ STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [EvalM_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
  \\ `evaluate' s env exp (s,Rval res)` by METIS_TAC [evaluate'_empty_store_IMP]
  \\ `!x. evaluate' s env exp x = (x = (s,Rval res))` by
       METIS_TAC [big_exp_determ']
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ SIMP_TAC (srw_ss()) [Once do_app_def,do_tapp_def]
  \\ FULL_SIMP_TAC std_ss [option_CASE_LEMMA2]
  \\ FULL_SIMP_TAC std_ss [the_type_constants_def,
       the_term_constants_def,the_axioms_def,the_definitions_def,
       the_clash_var_def]
  \\ `0 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `1 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `2 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `3 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `4 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ ASM_SIMP_TAC (srw_ss()) [store_assign_def]
  \\ Q.LIST_EXISTS_TAC [r,`Rval (Litv Unit)`,q]
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ REVERSE STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [HOL_STORE_def,EL_LUPDATE]
    \\ FULL_SIMP_TAC (srw_ss()) [HOL_STORE_def,EL_LUPDATE])
  \\ FULL_SIMP_TAC (srw_ss()) [HOL_MONAD_def,set_the_type_constants_def,
        set_the_term_constants_def,set_the_axioms_def,set_the_clash_var_def,
        set_the_definitions_def] \\ EVAL_TAC;

val set_the_type_constants_thm = store_thm("set_the_type_constants_thm",
  ``Eval env (Var "the_type_constants" NONE) ($= the_type_constants) ==>
    Eval env exp (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM) x) ==>
    EvalM env (App Opassign (Var "the_type_constants" NONE) exp)
      ((HOL_MONAD U_TYPE) (set_the_type_constants x))``,
  update_tac `LUPDATE res 0 s` `refs with the_type_constants := x`);

val set_the_term_constants_thm = store_thm("set_the_term_constants_thm",
  ``Eval env (Var "the_term_constants" NONE) ($= the_term_constants) ==>
    Eval env exp (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE) x) ==>
    EvalM env (App Opassign (Var "the_term_constants" NONE) exp)
      ((HOL_MONAD U_TYPE) (set_the_term_constants x))``,
  update_tac `LUPDATE res 1 s` `refs with the_term_constants := x`);

val set_the_axioms_thm = store_thm("set_the_axioms_thm",
  ``Eval env (Var "the_axioms" NONE) ($= the_axioms) ==>
    Eval env exp (LIST_TYPE THM_TYPE x) ==>
    EvalM env (App Opassign (Var "the_axioms" NONE) exp)
      ((HOL_MONAD U_TYPE) (set_the_axioms x))``,
  update_tac `LUPDATE res 2 s` `refs with the_axioms := x`);

val set_the_definitions_thm = store_thm("set_the_definitions_thm",
  ``Eval env (Var "the_definitions" NONE) ($= the_definitions) ==>
    Eval env exp (LIST_TYPE DEF_TYPE x) ==>
    EvalM env (App Opassign (Var "the_definitions" NONE) exp)
      ((HOL_MONAD U_TYPE) (set_the_definitions x))``,
  update_tac `LUPDATE res 3 s` `refs with the_definitions := x`);

val set_the_clash_var_thm = store_thm("set_the_clash_var_thm",
  ``Eval env (Var "the_clash_var" NONE) ($= the_clash_var) ==>
    Eval env exp (TERM_TYPE x) ==>
    EvalM env (App Opassign (Var "the_clash_var" NONE) exp)
      ((HOL_MONAD U_TYPE) (set_the_clash_var x))``,
  update_tac `LUPDATE res 4 s` `refs with the_clash_var := x`);


(*

val lemma =
  hol2deep ``[("bool",0); ("fun",2:num)]``
  |> DISCH_ALL |> SIMP_RULE std_ss []
val exp = lemma |> concl |> rator |> rand

val _ = temp_overload_on("type_init",exp)

val l = METIS_PROVE [] ``(?x. P x /\ Q x) ==> ?x. P x``

val l1 = lemma |> SIMP_RULE std_ss [Eval_def] |> HO_MATCH_MP l
               |> Q.INST [`env`|->`[]`]

val type_init_v_def = new_specification("type_init_v",["type_init_v"],l1);

val evaluate'_empty_env = prove(
  ``evaluate' empty_store [] exp (empty_store,Rval res) =
    !env. evaluate' empty_store env exp (empty_store,Rval res)``,
  cheat);

  type_init_v_def
  |> ONCE_REWRITE_RULE [evaluate'_empty_env]
  |> ONCE_REWRITE_RULE [evaluate'_empty_store_EQ]
  |> SPEC_ALL |> MATCH_MP (big_exp_determ' |> CONJUNCT1 |> GSYM)

*)

val _ = export_theory();
