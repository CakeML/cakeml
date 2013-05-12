open HolKernel Parse boolLib bossLib; val _ = new_theory "ml_translator";

open AstTheory LibTheory AltBigStepTheory SemanticPrimitivesTheory;
open terminationTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory;
open lcsymtacs;

infix \\ val op \\ = op THEN;


(* Definitions *)

val Eval_def = Define `
  Eval env exp P =
    ?res. evaluate' empty_store env exp (empty_store,Rval res) /\ P (res:v)`;

val evaluate_closure_def = Define `
  evaluate_closure input cl output =
    ?env exp. (do_app empty_store ARB Opapp cl input = SOME (empty_store,env,exp)) /\
              evaluate' empty_store env exp (empty_store,Rval (output))`;

val AppReturns_def = Define ` (* think of this as a Hoare triple {P} cl {Q} *)
  AppReturns P cl Q =
    !v. P v ==> ?u. evaluate_closure v cl u /\ Q u`;

val Arrow_def = Define `
  Arrow a b f =
    \v. !x. AppReturns (a x) v (b (f x))`;

val _ = add_infix("-->",400,HOLgrammars.RIGHT)
val _ = overload_on ("-->",``Arrow``)

val Eq_def = Define `
  Eq (abs:'a->v->bool) x =
    (\y v. (x = y) /\ abs y v)`;

val And_def = Define `And a P x v = (P x /\ a (x:'a) (v:v))`;

val U_TYPE_def = Define `
  U_TYPE (u:unit) (v:v) = (v = Litv Unit)`;

val INT_def = Define `
  INT i = \v:v. (v = Litv (IntLit i))`;

val NUM_def = Define `
  NUM n = INT (& n)`;

val BOOL_def = Define `
  BOOL b = \v:v. (v = Litv (Bool b))`;

val CONTAINER_def = Define `CONTAINER x = x`;

val TAG_def = Define `TAG n x = x`;

val PRECONDITION_def = Define `PRECONDITION b = (b:bool)`;

val PreImp_def = Define `
  PreImp b1 b2 = (PRECONDITION b1 ==> b2)`;


(* Theorems *)

val big_exp_determ' = store_thm("big_exp_determ'",
 ``(!s env e r1.
      evaluate' s env e r1 ==>
     !r2. evaluate' s env e r2 ==> (r1 = r2)) /\
   (!s env es r1.
      evaluate_list' s env es r1 ==>
      !r2. evaluate_list' s env es r2 ==> (r1 = r2)) /\
   (!s env v pes r1.
      evaluate_match' s env v pes r1 ==>
      !r2. evaluate_match' s env v pes r2 ==> (r1 = r2))``,
  HO_MATCH_MP_TAC evaluate'_ind >> rw [] >>
  pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss ()) [Once evaluate'_cases]) >>
  fs [] >> rw [] >> fs [] >> res_tac >> fs [] >> rw [] >>
  res_tac >> fs [] >> metis_tac []);

val evaluate_cases = evaluate'_cases;

val evaluate_11_Rval = store_thm("evaluate_11_Rval",
  ``evaluate' s env exp (s1,Rval res1) ==>
    evaluate' s env exp (s2,Rval res2) ==> (res1 = res2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC big_exp_determ'
  \\ FULL_SIMP_TAC (srw_ss()) []);

val Eval_Arrow = store_thm("Eval_Arrow",
  ``Eval env x1 ((a --> b) f) ==>
    Eval env x2 (a x) ==>
    Eval env (App Opapp x1 x2) (b (f x))``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [AppReturns_def] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [evaluate_closure_def]
  \\ Q.EXISTS_TAC `u` \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`res`,`res'`,`env'`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ METIS_TAC []);

val Eval_Fun = store_thm("Eval_Fun",
  ``(!v x. a x v ==> Eval ((name,v)::env) body (b ((f:'a->'b) x))) ==>
    Eval env (Fun name body) ((a --> b) f)``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ASM_SIMP_TAC (srw_ss()) [AppReturns_def,Eval_def,do_app_def,
       bind_def,evaluate_closure_def]);

val Eval_Fun_Eq = store_thm("Eval_Fun_Eq",
  ``(!v. a x v ==> Eval ((name,v)::env) body (b (f x))) ==>
    Eval env (Fun name body) ((Eq a x --> b) f)``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ASM_SIMP_TAC (srw_ss()) [AppReturns_def,evaluate_closure_def,
       do_app_def,bind_def,Eq_def]);

val And_IMP_Eq = store_thm("And_IMP_Eq",
  ``Eval env exp ((And a P --> b) f) ==>
    (P x ==> Eval env exp ((Eq a x --> b) f))``,
  FULL_SIMP_TAC std_ss [Eval_def,Arrow_def,AppReturns_def,And_def,Eq_def]
  \\ METIS_TAC []);

val Eq_IMP_And = store_thm("Eq_IMP_And",
  ``(!x. P x ==> Eval env (Fun name exp) ((Eq a x --> b) f)) ==>
    Eval env (Fun name exp) ((And a P --> b) f)``,
  FULL_SIMP_TAC std_ss [Eval_def,Arrow_def,AppReturns_def,And_def,Eq_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_Fun_And = store_thm("Eval_Fun_And",
  ``(!v x. P x ==> a x v ==> Eval ((name,v)::env) body (b (f x))) ==>
    Eval env (Fun name body) ((And a P --> b) f)``,
  FULL_SIMP_TAC std_ss [GSYM And_def,AND_IMP_INTRO]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC Eval_Fun \\ ASM_SIMP_TAC std_ss []);

val Eval_Let = store_thm("Eval_Let",
  ``Eval env exp (a res) /\
    (!v. a res v ==> Eval ((name,v)::env) body (b (f res))) ==>
    Eval env (Let name exp body) (b (LET f res))``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ Q.EXISTS_TAC `res''` \\ FULL_SIMP_TAC std_ss [LET_DEF,bind_def]
  \\ Q.LIST_EXISTS_TAC [`res'`,`empty_store`] \\ FULL_SIMP_TAC std_ss []);

val Eval_Var_SWAP_ENV = store_thm("Eval_Var_SWAP_ENV",
  ``!env1.
      Eval env1 (Var (Short name)) P /\ (lookup name env = lookup name env1) ==>
      Eval env (Var (Short name)) P``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def]);

val LOOKUP_VAR_def = Define `
  LOOKUP_VAR name env x = (lookup name env = SOME x)`;

val LOOKUP_VAR_THM = store_thm("LOOKUP_VAR_THM",
  ``LOOKUP_VAR name env x ==> Eval env (Var (Short name)) ($= x)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def,LOOKUP_VAR_def]);

val LOOKUP_VAR_SIMP = store_thm("LOOKUP_VAR_SIMP",
  ``LOOKUP_VAR name ((x,v)::env) y =
    if x = name then (v = y) else LOOKUP_VAR name env y``,
  SIMP_TAC std_ss [LOOKUP_VAR_def,lookup_def] \\ SRW_TAC [] []);

val Eval_Val_INT = store_thm("Eval_Val_INT",
  ``!n. Eval env (Lit (IntLit n)) (INT n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,NUM_def,INT_def,Eval_def]);

val Eval_Val_NUM = store_thm("Eval_Val_NUM",
  ``!n. Eval env (Lit (IntLit (&n))) (NUM n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,NUM_def,INT_def,Eval_def]);

val Eval_Val_BOOL = store_thm("Eval_Val_BOOL",
  ``!n. Eval env (Lit (Bool n)) (BOOL n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,BOOL_def,Eval_def]);

val Eval_Or = store_thm("Eval_Or",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (Log Or x1 x2) (BOOL (b1 \/ b2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Litv (Bool b1))` \\ Cases_on `b1`
  \\ FULL_SIMP_TAC (srw_ss()) [do_log_def]
  \\ Q.EXISTS_TAC `empty_store` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_And = store_thm("Eval_And",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (Log And x1 x2) (BOOL (b1 /\ b2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Litv (Bool b1))` \\ Cases_on `b1`
  \\ FULL_SIMP_TAC (srw_ss()) [do_log_def]
  \\ Q.EXISTS_TAC `empty_store` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_If = store_thm("Eval_If",
  ``(a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> Eval env x2 (a b2)) /\
    (a3 ==> Eval env x3 (a b3)) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     Eval env (If x1 x2 x3) (a (if b1 then b2 else b3)))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss [CONTAINER_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `b1` \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `res` \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `Litv (Bool T)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
    \\ Q.EXISTS_TAC `empty_store` \\ FULL_SIMP_TAC std_ss [])
  THEN1 (Q.EXISTS_TAC `res` \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `Litv (Bool F)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
    \\ Q.EXISTS_TAC `empty_store` \\ FULL_SIMP_TAC std_ss []));

val Eval_Bool_Not = store_thm("Eval_Bool_Not",
  ``Eval env x1 (BOOL b1) ==>
    Eval env (App Equality x1 (Lit (Bool F))) (BOOL (~b1))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Litv (Bool b1))`
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ Q.LIST_EXISTS_TAC [`Litv (Bool F)`,`empty_store`]
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC std_ss [contains_closure_def]);

val Eval_Implies = store_thm("Eval_Implies",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (If x1 x2 (Lit (Bool T))) (BOOL (b1 ==> b2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Litv (Bool b1))` \\ Cases_on `b1`
  \\ FULL_SIMP_TAC (srw_ss()) [do_if_def]
  \\ Q.EXISTS_TAC `empty_store` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_Var_SIMP = store_thm("Eval_Var_SIMP",
  ``Eval ((x,v)::env) (Var (Short y)) p =
      if x = y then p v else Eval env (Var (Short y)) p``,
  SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,lookup_def]
  \\ SRW_TAC [] [] \\ SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,
       lookup_def]);

val Eval_Eq = store_thm("Eval_Eq",
  ``Eval env exp (a x) ==> Eval env exp ((Eq a x) x)``,
  SIMP_TAC std_ss [Eval_def,Eq_def]);

val FUN_FORALL = new_binder_definition("FUN_FORALL",
  ``($FUN_FORALL) = \(abs:'a->'b->v->bool) a v. !y. abs y a v``);

val FUN_EXISTS = new_binder_definition("FUN_EXISTS",
  ``($FUN_EXISTS) = \(abs:'a->'b->v->bool) a v. ?y. abs y a v``);

val Eval_FUN_FORALL = store_thm("Eval_FUN_FORALL",
  ``(!x. Eval env exp ((p x) f)) ==>
    Eval env exp ((FUN_FORALL x. p x) f)``,
  SIMP_TAC std_ss [Eval_def,Arrow_def,Eq_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AppReturns_def,FUN_FORALL]
  \\ `?res. evaluate' empty_store env exp (empty_store,Rval res)` by METIS_TAC []
  \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o Q.SPEC `y`)
  \\ IMP_RES_TAC evaluate_11_Rval \\ FULL_SIMP_TAC (srw_ss()) []);

val Eval_FUN_FORALL_EQ = store_thm("Eval_FUN_FORALL_EQ",
  ``(!x. Eval env exp ((p x) f)) =
    Eval env exp ((FUN_FORALL x. p x) f)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [Eval_FUN_FORALL]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [FUN_FORALL] \\ METIS_TAC []);

val PULL_FORALL = save_thm("PULL_FORALL",
  METIS_PROVE [] ``((p ==> !x. q x) = (!x. p ==> q x)) /\
                   ((p /\ !x. q x) = (!x. p /\ q x))``)

val FUN_FORALL_PUSH1 = prove(
  ``(FUN_FORALL x. a --> (b x)) = (a --> FUN_FORALL x. b x)``,
  FULL_SIMP_TAC std_ss [Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL,
    Eval_def,evaluate_closure_def] \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC
  THEN1 METIS_TAC [evaluate_11_Rval]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ POP_ASSUM (fn th => STRIP_ASSUME_TAC (Q.SPEC `ARB` th) THEN ASSUME_TAC th)
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `u` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `y`) \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [evaluate_11_Rval,PAIR_EQ]) |> GEN_ALL;

val FUN_FORALL_PUSH2 = prove(
  ``(FUN_FORALL x. (a x) --> b) = ((FUN_EXISTS x. a x) --> b)``,
  FULL_SIMP_TAC std_ss [Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL,FUN_EXISTS,
    Eval_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Eq = prove(
  ``(FUN_EXISTS x. Eq a x) = a``,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Eq_def]) |> GEN_ALL;

val FUN_QUANT_SIMP = save_thm("FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Eq,FUN_FORALL_PUSH1,FUN_FORALL_PUSH2]);

val Eval_Recclosure_ALT = store_thm("Eval_Recclosure_ALT",
  ``!funs fname name body.
    (!v. a n v ==>
  Eval ((name,v)::FOLDR (\(f,x,e) env'. (f,Recclosure env2 funs f)::env') env2
           funs) body (b (f n))) ==>
    LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
    (find_recfun fname funs = SOME (name,body)) ==>
    Eval env (Var (Short fname)) ((Eq a n --> b) f)``,
  NTAC 6 STRIP_TAC \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [AppReturns_def,Eq_def,
       do_app_def,evaluate_closure_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [bind_def,build_rec_env_def,FOLDR]);

val Eval_Recclosure = store_thm("Eval_Recclosure",
  ``(!v. a n v ==>
  Eval ((name,v)::(fname,Recclosure env2 [(fname,name,body)] fname)::env2) body (b (f n))) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    Eval env (Var (Short fname)) ((Eq a n --> b) f)``,
  (Eval_Recclosure_ALT |> Q.SPECL [`[(fname,name,body)]`,`fname`]
    |> SIMP_RULE (srw_ss()) [Once find_recfun_def] |> ASSUME_TAC)
  \\ FULL_SIMP_TAC std_ss []);

val SafeVar_def = Define `SafeVar = Var`;

val Eval_Eq_Recclosure = store_thm("Eval_Eq_Recclosure",
  ``LOOKUP_VAR name env (Recclosure x1 x2 x3) ==>
    (P f (Recclosure x1 x2 x3) =
     Eval env (Var (Short name)) (P f))``,
  SIMP_TAC std_ss [Eval_Var_SIMP,Eval_def,LOOKUP_VAR_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate'_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val Eval_Eq_Fun = store_thm("Eval_Eq_Fun",
  ``Eval env (Fun v x) p ==>
    !env2. Eval env2 (Var name) ($= (Closure env v x)) ==>
           Eval env2 (Var name) p``,
  SIMP_TAC std_ss [Eval_Var_SIMP,Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val Eval_WEAKEN = store_thm("Eval_WEAKEN",
  ``Eval env exp P ==> (!v. P v ==> Q v) ==> Eval env exp Q``,
  SIMP_TAC std_ss [Eval_def] \\ METIS_TAC []);

val Eval_CONST = store_thm("Eval_CONST",
  ``(!v. P v = (v = x)) ==>
    Eval env (Var name) ($= x) ==> Eval env (Var name) P``,
  SIMP_TAC std_ss [Eval_def])


(* arithmetic for integers *)

val Eval_Opn = prove(
  ``!f n1 n2.
        Eval env x1 (INT n1) ==>
        Eval env x2 (INT n2) ==>
        PRECONDITION (((f = Divide) \/ (f = Modulo)) ==> ~(n2 = 0)) ==>
        Eval env (App (Opn f) x1 x2) (INT (opn_lookup f n1 n2))``,
  SIMP_TAC std_ss [Eval_def,INT_def] \\ SIMP_TAC std_ss [PRECONDITION_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`Litv (IntLit n1)`,`Litv (IntLit n2)`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ Cases_on `f` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT (Q.EXISTS_TAC `empty_store`) \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

local
  fun f name q =
    save_thm("Eval_" ^ name,SIMP_RULE (srw_ss()) [opn_lookup_def,EVAL ``PRECONDITION T``]
                              (Q.SPEC q Eval_Opn))
in
  val Eval_INT_ADD  = f "INT_ADD" `Plus`
  val Eval_INT_SUB  = f "INT_SUB" `Minus`
  val Eval_INT_MULT = f "INT_MULT" `Times`
  val Eval_INT_DIV  = f "INT_DIV" `Divide`
  val Eval_INT_MOD  = f "INT_MOD" `Modulo`
end

val Eval_Opb = prove(
  ``!f n1 n2.
        Eval env x1 (INT n1) ==>
        Eval env x2 (INT n2) ==>
        Eval env (App (Opb f) x1 x2) (BOOL (opb_lookup f n1 n2))``,
  SIMP_TAC std_ss [Eval_def,INT_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`Litv (IntLit n1)`,`Litv (IntLit n2)`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT (Q.EXISTS_TAC `empty_store`) \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

local
  fun f name q = let
    val th = SIMP_RULE (srw_ss()) [opb_lookup_def] (Q.SPEC q Eval_Opb)
    val _ = save_thm("Eval_" ^ name,SPEC_ALL th)
   in th end
in
  val Eval_INT_LESS = f "INT_LESS" `Lt`
  val Eval_INT_LESS_EQ = f "INT_LESS_EQ" `Leq`
  val Eval_INT_GREATER = f "INT_GREATER" `Gt`
  val Eval_INT_GREATER_EQ = f "INT_GREATER_EQ" `Geq`
end


(* arithmetic for num *)

val Eval_NUM_ADD = save_thm("Eval_NUM_ADD",
  Eval_INT_ADD |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_ADD]);

val Eval_NUM_MULT = save_thm("Eval_NUM_MULT",
  Eval_INT_MULT |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_MUL]);

val Eval_NUM_DIV = save_thm("Eval_NUM_DIV",
  Eval_INT_DIV |> Q.SPECL [`&n1`,`&n2`]
  |> UNDISCH_ALL |> DISCH ``PRECONDITION (&n2 <> 0)``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_DIV,PRECONDITION_def,INT_INJ]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM PRECONDITION_def]))
  |> DISCH ``Eval env x2 (INT (&n2))``
  |> DISCH ``Eval env x1 (INT (&n1))``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_DIV]);

val Eval_NUM_MOD = save_thm("Eval_NUM_MOD",
  Eval_INT_MOD |> Q.SPECL [`&n1`,`&n2`]
  |> UNDISCH_ALL |> DISCH ``PRECONDITION (&n2 <> 0)``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_MOD,PRECONDITION_def,INT_INJ]
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [GSYM PRECONDITION_def]))
  |> DISCH ``Eval env x2 (INT (&n2))``
  |> DISCH ``Eval env x1 (INT (&n1))``
  |> SIMP_RULE std_ss [GSYM NUM_def,INT_MOD]);

val Eval_NUM_MULT =
  Eval_INT_MULT |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_MUL]

local

val th0 = Q.SPEC `0` Eval_Val_INT
val th1 = ASSUME ``Eval env (Var (Short "k")) (INT k)``
val th2 = Eval_INT_LESS  |> Q.SPECL [`k`,`0`]
          |> (fn th => MATCH_MP th th1) |> (fn th => MATCH_MP th th0)
val th = MATCH_MP Eval_If (LIST_CONJ (map (DISCH T) [th2,th0,th1]))
         |> REWRITE_RULE [CONTAINER_def]
val code =
  ``Let "k" (App (Opn Minus) x1 x2)
      (If (App (Opb Lt) (Var (Short "k")) (Lit (IntLit 0)))
          (Lit (IntLit 0)) (Var (Short "k"))): exp``

in

val Eval_NUM_SUB = store_thm("Eval_NUM_SUB",
  ``Eval env x1 (NUM m) ==>
    Eval env x2 (NUM n) ==>
    Eval env ^code (NUM (m - n))``,
  SIMP_TAC std_ss [NUM_def]
  \\ `&(m - n:num) = let k = &m - &n in if k < 0 then 0 else k:int` by
   (FULL_SIMP_TAC std_ss [LET_DEF,INT_LT_SUB_RADD,INT_ADD,INT_LT]
    \\ Cases_on `m<n` \\ FULL_SIMP_TAC std_ss []
    THEN1 (`m - n = 0` by DECIDE_TAC \\ ASM_REWRITE_TAC [])
    \\ FULL_SIMP_TAC std_ss [NOT_LESS,INT_SUB])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC (GEN_ALL Eval_Let)
  \\ Q.EXISTS_TAC `INT` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_INT_SUB]
  \\ MATCH_MP_TAC (GEN_ALL (DISCH_ALL th))
  \\ FULL_SIMP_TAC std_ss [Eval_Var_SIMP]);

end;

val Eval_NUM_LESS = save_thm("Eval_NUM_LESS",
  Eval_INT_LESS |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]);

val Eval_NUM_LESS_EQ = save_thm("Eval_NUM_LESS_EQ",
  Eval_INT_LESS_EQ |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]);

val Eval_NUM_GREATER = save_thm("Eval_NUM_GREATER",
  Eval_INT_GREATER |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]
  |> REWRITE_RULE [GSYM GREATER_DEF, GSYM GREATER_EQ]);

val Eval_NUM_GREATER_EQ = save_thm("Eval_NUM_GREATER_EQ",
  Eval_INT_GREATER_EQ |> Q.SPECL [`&n1`,`&n2`]
  |> REWRITE_RULE [GSYM NUM_def,INT_LT,INT_LE,int_ge,int_gt]
  |> REWRITE_RULE [GSYM GREATER_DEF, GSYM GREATER_EQ]);

val Eval_NUM_EQ_0 = store_thm("Eval_NUM_EQ_0",
  ``!n. Eval env x (NUM n) ==>
        Eval env (App (Opb Leq) x (Lit (IntLit 0))) (BOOL (n = 0))``,
  REPEAT STRIP_TAC \\ ASSUME_TAC (Q.SPEC `0` Eval_Val_NUM)
  \\ FULL_SIMP_TAC std_ss [NUM_def]
  \\ `(n = 0) = (&n <= 0)` by intLib.COOPER_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_INT_LESS_EQ]);


(* Equality *)

val no_closures_def = tDefine "no_closures" `
  (no_closures (Litv l) = T) /\
  (no_closures (Conv name vs) = EVERY no_closures vs) /\
  (no_closures _ = F)`
 (WF_REL_TAC `measure v_size` \\ REPEAT STRIP_TAC
  \\ Induct_on `vs` \\ FULL_SIMP_TAC (srw_ss()) [MEM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [MEM,v_size_def]
  \\ DECIDE_TAC)

val EqualityType_def = Define `
  EqualityType (abs:'a->v->bool) <=>
    (!x1 v1. abs x1 v1 ==> no_closures v1) /\
    (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> ((v1 = v2) = (x1 = x2)))`;

val EqualityType_NUM_BOOL = store_thm("EqualityType_NUM_BOOL",
  ``EqualityType NUM /\ EqualityType INT /\ EqualityType BOOL``,
  EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [no_closures_def]);

val no_closures_IMP_NOT_contains_closure = prove(
  ``!res. no_closures res ==> ~contains_closure res``,
  HO_MATCH_MP_TAC contains_closure_ind
  \\ SIMP_TAC std_ss [no_closures_def,EVERY_MEM,contains_closure_def,
       EXISTS_MEM] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c <=> (b ==> c)``]
  \\ REPEAT STRIP_TAC \\ RES_TAC);

val Eval_Equality = store_thm("Eval_Equality",
  ``Eval env x1 (a y1) /\ Eval env x2 (a y2) ==>
    EqualityType a ==>
    Eval env (App Equality x1 x2) (BOOL (y1 = y2))``,
  SIMP_TAC std_ss [Eval_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`res`,`res'`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ REPEAT (Q.EXISTS_TAC `empty_store`) \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [EqualityType_def]
  \\ METIS_TAC [no_closures_IMP_NOT_contains_closure]);


(* evaluation of declarations *)

val Decls_def = Define `
  Decls mn (menv1 : envM) cenv1 s1 env1 ds cenv2 s2 env2 =
    evaluate_decs' mn menv1 cenv1 s1 env1 ds (s2,Rval (cenv2,env2))`;

val DeclAssum_def = Define `
  DeclAssum ds env = ?s2 cenv2. Decls NONE [] [] empty_store [] ds cenv2 s2 env`;

val Decls_Dtype = store_thm("Decls_Dtype",
  ``!mn menv cenv s env tds cenv1 s1 env1.
      Decls mn menv cenv s env [Dtype tds] cenv1 s1 env1 <=>
      check_dup_ctors mn cenv tds /\ (cenv1 = build_tdefs mn tds) /\
      (env1 = emp) /\ (s1 = s)``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [evaluate_dec'_cases, combine_dec_result_def,
                          merge_def, emp_def]
  \\ METIS_TAC []);

val Decls_Dlet = store_thm("Decls_Dlet",
  ``!mn menv cenv s env v e cenv1 s1 env1.
      Decls mn menv cenv s env [Dlet (Pvar v) e] cenv1 s1 env1 =
      ?x. (cenv1 = emp) /\ (env1 = bind v x emp) /\
           evaluate' s env e (s1,Rval x)``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch'_def,bind_def, evaluate_dec'_cases,
       combine_dec_result_def, emp_def, merge_def]
  \\ METIS_TAC []);

val Decls_Dletrec = store_thm("Decls_Dletrec",
  ``!mn menv cenv s env funs cenv1 s1 env1.
      Decls mn menv cenv s env [Dletrec funs] cenv1 s1 env1 <=>
      ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\
      (cenv1 = emp) /\ (env1 = build_rec_env funs env emp) /\ (s1 = s)``,
  SIMP_TAC std_ss [Decls_def]
  \\ ONCE_REWRITE_TAC [evaluate_decs'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_decs'_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def,bind_def,merge_def, emp_def, evaluate_dec'_cases,
       combine_dec_result_def]
  \\ METIS_TAC []);

val _ = temp_overload_on("has_emp",``\x. FST x = empty_store``)

val LUPDATE_NIL = prove(
  ``!xs n x. (LUPDATE x n xs = []) = (xs = [])``,
  Cases \\ Cases_on `n` \\ FULL_SIMP_TAC (srw_ss()) [LUPDATE_def]);

val evaluate'_empty_store_lemma = prove(
 ``(!s env e r1.
      evaluate' s env e r1 ==> has_emp r1 ==> (s = empty_store)) /\
   (!s env es r1.
      evaluate_list' s env es r1 ==> has_emp r1 ==> (s = empty_store)) /\
   (!s env v pes r1.
      evaluate_match' s env v pes r1 ==> has_emp r1 ==> (s = empty_store))``,
  HO_MATCH_MP_TAC evaluate'_ind >> rw [] \\ POP_ASSUM MP_TAC
  \\ TRY (Cases_on `uop`) \\ TRY (Cases_on `op`)
  \\ FULL_SIMP_TAC (srw_ss()) [do_uapp_def,do_app_def,LET_DEF,store_alloc_def]
  THEN1 (Cases_on `s2`
    \\ FULL_SIMP_TAC (srw_ss()) [store_alloc_def,empty_store_def,APPEND])
  THEN1 (Cases_on `v` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `store_lookup n s2` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [IMP_DISJ_THM]
  \\ TRY (Cases_on `v1`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ TRY (Cases_on `l`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ TRY (Cases_on `v2`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ TRY (Cases_on `l`) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] []
  \\ TRY (Cases_on `find_recfun s''' l0` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ TRY (Cases_on `n < LENGTH s3` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC std_ss [store_assign_def,empty_store_def,LUPDATE_NIL]
  \\ CCONTR_TAC
  \\ Q.PAT_ASSUM `(if bbb then xxx else zz) = SOME yyy` MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [])
  |> SIMP_RULE std_ss [PULL_EXISTS,AND_IMP_INTRO];

val _ = temp_overload_on("has_emp_no_fail",
  ``\x. (FST x = empty_store:store) /\
        ~(SND x = (Rerr Rtype_error):'a result) /\
        ~(SND x = (Rerr (Rraise Bind_error)):'a result)``)

val sind = IndDefLib.derive_strong_induction(evaluate'_rules,evaluate'_ind);

val do_app_empty_store = prove(
  ``!op v1 v2.
      s3 <> empty_store ==>
      ~(do_app s3 env op v1 v2 = SOME (empty_store,env',e''))``,
  Cases \\ SIMP_TAC std_ss [do_app_def] \\ SRW_TAC [] []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [store_assign_def]
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH_LUPDATE,empty_store_def,GSYM LENGTH_NIL]);

val do_app_lemma = prove(
  ``!op.
      (do_app empty_store env op v1 v2 = SOME (empty_store,env',e'')) ==>
      !t. do_app t env op v1 v2 = SOME (t,env',e'')``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [do_app_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (BasicProvers.FULL_CASE_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [store_assign_def]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (srw_ss()) [empty_store_def]);

val pmatch'_lemma = prove(
  ``(!(s:store) (p:pat) v env x.
      (pmatch' empty_store p v env = x) /\ x <> Match_type_error ==>
      !s. (pmatch' s p v env = x)) /\
    (!(s:store) (p:pat list) vs env x.
      (pmatch_list' empty_store p vs env = x) /\ x <> Match_type_error ==>
      !s. (pmatch_list' s p vs env = x))``,
  HO_MATCH_MP_TAC pmatch'_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [pmatch'_def]
  \\ FULL_SIMP_TAC std_ss [store_lookup_def,empty_store_def,LENGTH]
  THEN1 (METIS_TAC [])
  \\ Cases_on `pmatch' [] p v env`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ASSUM `No_match = x` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) []);

val evaluate'_empty_store_IMP_any_store = prove(
 ``(!s env e r1.
      evaluate' s env e r1 ==> has_emp_no_fail r1 ==>
      !t. evaluate' t env e (t,SND r1)) /\
   (!s env es r1.
      evaluate_list' s env es r1 ==> has_emp_no_fail r1 ==>
      !t. evaluate_list' t env es (t,SND r1)) /\
   (!s env v pes r1.
      evaluate_match' s env v pes r1 ==> has_emp_no_fail r1 ==>
      !t. evaluate_match' t env v pes (t,SND r1))``,
  HO_MATCH_MP_TAC sind \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1
   (Cases_on `r1`
    \\ `s' = empty_store` by IMP_RES_TAC evaluate'_empty_store_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1
   (Q.LIST_EXISTS_TAC [`v`,`t`] \\ FULL_SIMP_TAC std_ss []
    \\ `s2 = empty_store` by ALL_TAC THEN1
     (Cases_on `uop`
      \\ FULL_SIMP_TAC (srw_ss()) [do_uapp_def,LET_DEF,store_alloc_def]
      \\ FULL_SIMP_TAC (srw_ss()) [GSYM SNOC_APPEND,empty_store_def]
      \\ Cases_on `v`
      \\ FULL_SIMP_TAC (srw_ss()) [GSYM SNOC_APPEND,empty_store_def]
      \\ Cases_on `store_lookup n s2` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `uop`
    \\ FULL_SIMP_TAC (srw_ss()) [do_uapp_def,LET_DEF,store_alloc_def]
    \\ Cases_on `v`
    \\ FULL_SIMP_TAC (srw_ss()) [do_uapp_def,LET_DEF,
         store_lookup_def,empty_store_def])
  THEN1
   (`s'' = empty_store` by IMP_RES_TAC evaluate'_empty_store_lemma
    \\ `s3 = empty_store` by METIS_TAC [do_app_empty_store]
    \\ FULL_SIMP_TAC std_ss []
    \\ `s' = empty_store` by IMP_RES_TAC evaluate'_empty_store_lemma
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma
    \\ Cases_on `r1` \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  \\ TRY (`s' = empty_store` by IMP_RES_TAC evaluate'_empty_store_lemma
          \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  THEN1
   (`s = empty_store` by IMP_RES_TAC evaluate'_empty_store_lemma
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC pmatch'_lemma
    \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1
   (`s = empty_store` by IMP_RES_TAC evaluate'_empty_store_lemma
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC pmatch'_lemma
    \\ FULL_SIMP_TAC (srw_ss()) []));

val evaluate'_empty_store_IMP = store_thm("evaluate'_empty_store_IMP",
  ``evaluate' empty_store env x (empty_store,Rval y) ==>
    !s. evaluate' s env x (s,Rval y)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate'_empty_store_IMP_any_store
  \\ FULL_SIMP_TAC (srw_ss()) []);

val evaluate'_empty_store_EQ = store_thm("evaluate'_empty_store_EQ",
  ``evaluate' empty_store env x (empty_store,Rval y) =
    !s. evaluate' s env x (s,Rval y)``,
  METIS_TAC [evaluate'_empty_store_IMP]);

val do_app_empty_store = store_thm("do_app_empty_store",
  ``(do_app s3 env Opapp v1 v2 = SOME (empty_store,env',e3)) <=>
    (do_app s3 env Opapp v1 v2 = SOME (empty_store,env',e3)) /\ (s3 = empty_store)``,
  SIMP_TAC (srw_ss()) [do_app_def] \\ Cases_on `v1`
  \\ SIMP_TAC (srw_ss()) [do_app_def] \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ METIS_TAC []);

val evaluate'_empty_store = store_thm("evaluate'_empty_store",
  ``evaluate' s2 env xs ((empty_store,Rval ys)) <=>
    evaluate' s2 env xs ((empty_store,Rval ys)) /\ (s2 = empty_store)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC evaluate'_empty_store_lemma \\ FULL_SIMP_TAC std_ss []);

val evaluate_list'_empty_store = prove(
  ``evaluate_list' s2 env xs (empty_store,Rval ys) ==> (s2 = empty_store)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate'_empty_store_lemma
  \\ FULL_SIMP_TAC (srw_ss()) []);

val combine_dec_result_rval = Q.prove (
  `!new_tds new_env cenv env.
     combine_dec_result new_tds new_env (Rval (cenv, env)) =
     Rval (merge cenv new_tds, merge env new_env)`,
  rw [combine_dec_result_def]);

val combine_dec_result_rerr = Q.prove (
  `!new_tds new_env err.
     combine_dec_result new_tds new_env (Rerr err) = Rerr err`,
  rw [combine_dec_result_def]);

val Decls_APPEND = store_thm("Decls_APPEND",
  ``!s1 s3 mn menv cenv1 cenv4 ds1 ds2 env1 env4.
      Decls mn menv cenv1 s1 env1 (ds1 ++ ds2) cenv4 s3 env4 =
      ?cenv2 s2 env2 cenv3 env3.
         (cenv4 = merge cenv3 cenv2) /\
         (env4 = merge env3 env2) /\
         Decls mn menv cenv1 s1 env1 ds1 cenv2 s2 env2 /\
         Decls mn menv (merge cenv2 cenv1) s2 (merge env2 env1) ds2 cenv3 s3 env3``,
  Induct_on `ds1` \\ FULL_SIMP_TAC std_ss [APPEND,Decls_def]
  THEN1 (ONCE_REWRITE_TAC [evaluate_decs'_cases]
         \\ SIMP_TAC (srw_ss()) [merge_def, emp_def])
  \\ SIMP_TAC (srw_ss()) [Once evaluate_decs'_cases]
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_decs'_cases]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  \\ rw []
  \\ eq_tac >|
  [rw [] >>
       Cases_on `r` >>
       fs [combine_dec_result_rval, combine_dec_result_rerr] >>
       Cases_on `a` >>
       fs [combine_dec_result_rval, combine_dec_result_rerr] >>
       qexists_tac `s2'` >>
       qexists_tac `new_tds` >>
       qexists_tac `new_env` >>
       qexists_tac `Rval (merge cenv3 q,merge env3 r)` >>
       rw [combine_dec_result_rval, merge_def] >>
       metis_tac [merge_def],
   rw [] >>
       Cases_on `r` >>
       fs [combine_dec_result_rval, combine_dec_result_rerr] >>
       Cases_on `a` >>
       fs [combine_dec_result_rval, combine_dec_result_rerr] >>
       res_tac >>
       qexists_tac `cenv2++new_tds` >>
       qexists_tac `s2'` >>
       qexists_tac `env2++new_env` >>
       qexists_tac `cenv3` >>
       qexists_tac `env3` >>
       qexists_tac `s2` >>
       qexists_tac `new_tds` >>
       qexists_tac `new_env` >>
       qexists_tac `Rval (cenv2,env2)` >>
       metis_tac [APPEND_ASSOC, combine_dec_result_rval, merge_def]]);

val Decls_CONS = save_thm("Decls_CONS",
  ``Decls mn menv cenv1 s1 env1 ([d] ++ ds) cenv2 s2 env2``
  |> REWRITE_CONV [Decls_APPEND]
  |> REWRITE_RULE [APPEND]);

val Decls_NIL = store_thm("Decls_NIL",
  ``Decls mn menv cenv1 s1 env1 [] cenv2 s2 env2 <=>
      (env2 = emp) /\ (s2 = s1) /\ (cenv2 = emp)``,
  SIMP_TAC std_ss [Decls_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_decs'_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ SIMP_TAC std_ss []);

val DeclAssum_Dtype = store_thm("DeclAssum_Dtype",
  ``(!env. DeclAssum ds env ==> Eval env (Var n) P) ==>
    !tds. (!env. DeclAssum (SNOC (Dtype tds) ds) env ==> Eval env (Var n) P)``,
  rw [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dtype, merge_def, emp_def]
  \\ METIS_TAC []);

val DeclAssum_Dlet = store_thm("DeclAssum_Dlet",
  ``!ds n P.
      (!env. DeclAssum ds env ==> Eval env (Var (Short n)) P) ==>
      !v e. ~(v = n) ==> (!env. DeclAssum (SNOC (Dlet (Pvar v) e) ds) env ==> Eval env (Var (Short n)) P)``,
  SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dlet]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [APPEND,bind_def,Eval_Var_SIMP, merge_def, emp_def] >>
  rw []
  \\ METIS_TAC []);

val DeclAssum_Dletrec_LEMMA = prove(
  ``!funs:(varN, varN # exp) env.
      ~MEM n (MAP FST funs) ==>
      (lookup n (MAP (\(fn,n,e). (fn,Recclosure env2 funs' fn)) funs ++ env2) =
       lookup n (env2:envE))``,
  Induct
  \\ rw []
  \\ FULL_SIMP_TAC (srw_ss()) [FOLDR,FORALL_PROD,lookup_def,bind_def,MEM,MAP] >>
  PairCases_on `h` >>
  fs []);

val PULL_EXISTS = save_thm("PULL_EXISTS",
  METIS_PROVE [] ``(((?x. P x) ==> Q) = !x. P x ==> Q) /\
                   (((?x. P x) /\ Q) = ?x. P x /\ Q) /\
                   ((Q /\ (?x. P x)) = ?x. Q /\ P x)``);

val option_CASE_LEMMA = prove(
  Pmatch.with_classic_heuristic Term
  `!topt. (case topt of NONE => NONE | SOME t => NONE) = NONE`,
  Cases \\ SRW_TAC [] []);

val DeclAssum_Dletrec = store_thm("DeclAssum_Dletrec",
  ``!ds n P.
      (!env. DeclAssum ds env ==> Eval env (Var (Short n)) P) ==>
      !funs. ~(MEM n (MAP FST funs)) ==>
             (!env. DeclAssum (SNOC (Dletrec funs) ds) env ==>
                    Eval env (Var (Short n)) P)``,
  SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bind_def,Eval_Var_SIMP]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ RES_TAC
  \\ MATCH_MP_TAC Eval_Var_SWAP_ENV
  \\ Q.EXISTS_TAC `env2` \\ FULL_SIMP_TAC std_ss [merge_def,emp_def,APPEND_NIL]
  \\ Q.PAT_ASSUM `n NOTIN set (MAP FST funs)` MP_TAC
  \\ SIMP_TAC std_ss [build_rec_env_def]
  \\ Q.SPEC_TAC (`Recclosure env2 funs`,`recc`)
  \\ Q.SPEC_TAC (`funs`,`xs`) \\ Induct
  \\ FULL_SIMP_TAC std_ss [FOLDR,APPEND,FORALL_PROD,MAP,bind_def,
       lookup_def,MEM,bind_def]);

val DeclAssum_Dlet_INTRO = store_thm("DeclAssum_Dlet_INTRO",
  ``(!env. DeclAssum ds env ==> Eval env exp P) ==>
    (!v env. DeclAssum (SNOC (Dlet (Pvar v) exp) ds) env ==>
             Eval env (Var (Short v)) P)``,
  rw [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dlet,
      PULL_EXISTS,bind_def,Eval_Var_SIMP, merge_def, emp_def]
  \\ FULL_SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ metis_tac [big_exp_determ', PAIR_EQ, result_11, evaluate'_empty_store_IMP])

val DeclAssum_Dletrec_INTRO_ALT = store_thm("DeclAssum_Dletrec_INTRO_ALT",
  ``!funs.
      (!env1 env.
        DeclAssum ds env /\
        EVERY ( \ (P,(v,rest)).
          LOOKUP_VAR v env1 (Recclosure env (MAP SND funs) v)) funs ==>
        EVERY ( \ (P,(v,rest)).
          Eval env1 (Var (Short v)) P) funs) ==>
      !env. DeclAssum (SNOC (Dletrec (MAP SND funs)) ds) env ==>
            EVERY ( \ (P,(v,rest)).
              Eval env (Var (Short v)) P) funs``,
  STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec,
       MAP,ALL_DISTINCT,MEM,PULL_EXISTS,build_rec_env_def,FOLDR,bind_def,
       Eval_Var_SIMP,LOOKUP_VAR_SIMP,EVERY_MEM,FORALL_PROD]
  \\ SIMP_TAC std_ss [Eval_def] \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL,AND_IMP_INTRO]
  \\ Q.PAT_ASSUM `!env1.bbb` MATCH_MP_TAC
  \\ Q.LIST_EXISTS_TAC [`env2`,`s2`,`cenv2'`] \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`p_1''`,`p_2`]
  \\ FULL_SIMP_TAC std_ss [merge_def,emp_def,APPEND_NIL,LOOKUP_VAR_def]
  \\ NTAC 5 STRIP_TAC
  \\ Q.MATCH_ASSUM_RENAME_TAC `MEM (P,v,x,y) funs` []
  \\ Q.SPEC_TAC (`Recclosure env2 (MAP SND funs)`,`recc`) \\ STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Induct_on `funs` \\ FULL_SIMP_TAC std_ss [MEM,FORALL_PROD,MAP,FOLDR]
  \\ NTAC 4 STRIP_TAC
  \\ Cases_on `(v = p_1')` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ SIMP_TAC std_ss []);

val DeclAssum_Dletrec_INTRO = store_thm("DeclAssum_Dletrec_INTRO",
  ``(!env1 env.
      DeclAssum ds env /\
      LOOKUP_VAR v env1 (Recclosure env [(v,xs,f)] v) ==>
      Eval env1 (Var (Short v)) P) ==>
    !env. DeclAssum (SNOC (Dletrec [(v,xs,f)]) ds) env ==>
          Eval env (Var (Short v)) P``,
  (DeclAssum_Dletrec_INTRO_ALT |> Q.SPEC `[(P,v,xs,f)]`
    |> SIMP_RULE std_ss [EVERY_DEF,MAP] |> ASSUME_TAC)
  \\ FULL_SIMP_TAC std_ss []);

(* a few misc. lemmas that help the automation *)

val IMP_PreImp = store_thm("IMP_PreImp",
  ``!b1 b2 b3. (b1 /\ b2 ==> b3) ==> b1 ==> PreImp b2 b3``,
  REPEAT Cases \\ EVAL_TAC);

val evaluate_list_SIMP = store_thm("evaluate_list_SIMP",
  ``(evaluate_list' empty_store env [] (empty_store,Rval ([])) = T) /\
    (evaluate_list' empty_store env (x::xs) (empty_store,Rval ((y::ys))) <=>
     evaluate' empty_store  env x (empty_store,Rval (y)) /\
     evaluate_list' empty_store env xs (empty_store,Rval (ys)))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC [evaluate_list'_empty_store]);

val UNCURRY1 = prove(
  ``!f. UNCURRY f = \x. case x of (x,y) => f x y``,
  STRIP_TAC \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,pair_case_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,pair_case_def]);

val UNCURRY2 = prove(
  ``!x y f. pair_CASE x f y  = pair_CASE x (\z1 z2. f z1 z2 y)``,
  Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val UNCURRY3 = prove(
  ``pair_CASE (x,y) f = f x y``,
  EVAL_TAC) |> GEN_ALL;

val UNCURRY_SIMP = save_thm("UNCURRY_SIMP",
  LIST_CONJ [UNCURRY1,UNCURRY2,UNCURRY3]);

val num_case_thm = store_thm("num_case_thm",
  ``num_CASE = \n b f. if n = 0 then b else f (n-1)``,
  SIMP_TAC std_ss [FUN_EQ_THM,num_case_def] \\ Cases_on `n`
  \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val PUSH_FORALL_INTO_IMP = save_thm("PUSH_FORALL_INTO_IMP",
  METIS_PROVE [] ``!P Q. (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)``);

val FALSE_def = Define `FALSE = F`;
val TRUE_def = Define `TRUE = T`;

val MEMBER_def = Define `
  (MEMBER (x:'a) [] <=> F) /\
  (MEMBER x (y::ys) <=> (x = y) \/ MEMBER x ys)`;

val MEM_EQ_MEMBER = prove(
  ``!ys x. MEM x ys = MEMBER x ys``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [MEMBER_def]);

val MEMBER_INTRO = store_thm("MEMBER_INTRO",
  ``(MEM = MEMBER) /\ (MEM x = MEMBER x) /\ (MEM x ys = MEMBER x ys)``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,MEM_EQ_MEMBER]);

val _ = export_theory();
