open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_monad";

open ml_translatorTheory;
open ml_translatorLib;

open hol_kernelTheory;
open stringTheory listTheory pairTheory;
open astTheory libTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory lcsymtacs;


infix \\ val op \\ = op THEN;

(* a few basics *)

val _ = (use_full_type_names := false);

val _ = translate_into_module "Kernel";

val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;

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
val (*HOL_KERNEL_*)HOL_TYPE_TYPE_def = fetch "-" "HOL_TYPE_TYPE_def"

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
          types_match v1 v2 /\ ((v1 = v2) <=> (x1 = x2))) /\
    LIST_TYPE P ts v1 /\ LIST_TYPE P us v2 ==>
    types_match v1 v2 /\ ((v1 = v2) = (ts = us))``,
  STRIP_TAC \\ Induct \\ Cases_on `us` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [LIST_TYPE_def,types_match_def]
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,types_match_def]
  \\ METIS_TAC []);

val CHAR_IMP_no_closures = prove(
  ``CHAR x v ==> no_closures v``,
  SIMP_TAC std_ss [CHAR_def,NUM_def,INT_def,no_closures_def]);

val EqualityType_thm = prove(
  ``EqualityType abs <=>
      (!x1 v1. abs x1 v1 ==> no_closures v1) /\
      (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2 /\
                                                (v1 = v2 <=> x1 = x2))``,
  SIMP_TAC std_ss [EqualityType_def] \\ METIS_TAC []);

val LIST_TYPE_CHAR_LEMMA = prove(
  ``EqualityType (LIST_TYPE CHAR)``,
  METIS_TAC (eq_lemmas ()));

val EqualityType_HOL_TYPE = prove(
  ``EqualityType (*HOL_KERNEL_*)HOL_TYPE_TYPE``,
  SIMP_TAC std_ss [EqualityType_thm] \\ STRIP_TAC THEN1
   (HO_MATCH_MP_TAC hol_type_ind
    \\ FULL_SIMP_TAC std_ss [(*HOL_KERNEL_*)HOL_TYPE_TYPE_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [no_closures_def,EVERY_DEF]
    \\ IMP_RES_TAC (LIST_TYPE_NO_CLOSURES |> GEN_ALL)
    \\ METIS_TAC [CHAR_IMP_no_closures])
  \\ HO_MATCH_MP_TAC hol_type_ind \\ REVERSE STRIP_TAC THEN1
   (REPEAT STRIP_TAC
    \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [(*HOL_KERNEL_*)HOL_TYPE_TYPE_def]
    \\ FULL_SIMP_TAC (srw_ss()) [types_match_def]
    \\ ASSUME_TAC LIST_TYPE_CHAR_LEMMA
    \\ FULL_SIMP_TAC std_ss [EqualityType_def] \\ RES_TAC)
  \\ REPEAT GEN_TAC \\ STRIP_TAC \\ REPEAT GEN_TAC \\ STRIP_TAC
  \\ Cases_on `x2` \\ FULL_SIMP_TAC (srw_ss()) [(*HOL_KERNEL_*)HOL_TYPE_TYPE_def]
  \\ FULL_SIMP_TAC (srw_ss()) [types_match_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(b1 /\ (x1 = y1)) /\ (b2 /\ (x2 = y2)) ==>
       (b1 /\ b2) /\ ((x1 /\ x2 <=> y1 /\ y2))``)
  \\ STRIP_TAC THEN1
   (ASSUME_TAC LIST_TYPE_CHAR_LEMMA
    \\ FULL_SIMP_TAC std_ss [EqualityType_def] \\ RES_TAC
    \\ ASM_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC LIST_TYPE_11
  \\ Q.EXISTS_TAC `(*HOL_KERNEL_*)HOL_TYPE_TYPE`
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ RES_TAC)
  |> store_eq_thm;

val _ = register_type ``:hol_term``;
val _ = register_type ``:thm``;
val _ = register_type ``:def``;

(*
  fetch "-" "PAIR_TYPE_def";
  fetch "-" "LIST_TYPE_def";
  fetch "-" "HOL_TYPE_TYPE_def";
  fetch "-" "HOL_TERM_TYPE_def";
  fetch "-" "(*HOL_KERNEL_*)THM_TYPE_def";
*)

(* definition of EvalM *)

val isRefv_def = Define `
  isRefv P x = ?v. (x = Refv v) /\ P v`;

val HOL_STORE_def = Define `
  HOL_STORE s refs <=>
    4 <= LENGTH s /\
    isRefv ((LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM))
            refs.the_type_constants) (EL 0 s) /\
    isRefv ((LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE))
            refs.the_term_constants) (EL 1 s) /\
    isRefv (LIST_TYPE DEF_TYPE refs.the_definitions) (EL 2 s) /\
    isRefv (HOL_TERM_TYPE refs.the_clash_var) (EL 3 s)`;

val EvalM_def = Define `
  EvalM env exp P <=>
    !s refs. HOL_STORE s refs ==>
             ?s2 res refs2. evaluate F env (0,s) exp ((0,s2),res) /\
                            P (refs,s) (refs2,s2,res) /\ HOL_STORE s2 refs2`;

(* refinement invariant for ``:'a M`` *)

val HOL_MONAD_def = Define `
  HOL_MONAD (a:'a->v->bool) (x:'a M) (state1:hol_refs,s1:v store)
                                     (state2:hol_refs,s2:v store,
                                      res: (v,v) result) =
    case (x state1, res) of
      ((HolRes y, state), Rval v) => (state = state2) /\ a y v
    | ((HolErr e, state), Rerr (Rraise _)) => (state = state2)
    | _ => F`

(* return *)

val EvalM_return = store_thm("EvalM_return",
  ``Eval env exp (a x) ==>
    EvalM env exp (HOL_MONAD a (ex_return x))``,
  SIMP_TAC std_ss [Eval_def,EvalM_def,HOL_MONAD_def,ex_return_def]
  \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`s`,`Rval res`,`refs`]
  \\ IMP_RES_TAC evaluate_empty_store_IMP
  \\ FULL_SIMP_TAC (srw_ss()) []);

(* bind *)

val EvalM_bind = store_thm("EvalM_bind",
  ``EvalM env e1 (HOL_MONAD b (x:'b M)) /\
    (!x v. b x v ==> EvalM (write name v env) e2 (HOL_MONAD a ((f x):'a M))) ==>
    EvalM env (Let (SOME name) e1 e2) (HOL_MONAD a (ex_bind x f))``,
  SIMP_TAC std_ss [EvalM_def,HOL_MONAD_def,ex_return_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ RES_TAC
  \\ Cases_on `x refs` \\ Cases_on `q`
  \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x refs = (HolRes res1,r)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate F env (0,s) e1 ((0,q),Rval (state1))` []
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`res1`,`state1`,`q`,`r`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`s2'`,`res`,`refs2'`]
    \\ FULL_SIMP_TAC std_ss [] \\ REVERSE STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def]
    \\ ONCE_REWRITE_TAC [evaluate_cases]
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ DISJ1_TAC
    \\ PairCases_on `env`
    \\ FULL_SIMP_TAC std_ss [opt_bind_def,write_def,bind_def]
    \\ Q.LIST_EXISTS_TAC [`state1`,`(0,q)`]
    \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x refs = (HolErr res1,r)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate F env (0,s) e1 ((0,q),Rerr (state1))` []
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ Q.LIST_EXISTS_TAC [`q`,`Rerr state1`,`refs2`]
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def]
    \\ ONCE_REWRITE_TAC [evaluate_cases] \\ FULL_SIMP_TAC (srw_ss()) []));

(* function abstraction and application *)

val any_evaluate_closure_def = Define `
  any_evaluate_closure (s1,input) cl (s2,output) =
     ?env exp.
       (do_opapp [cl;input] = SOME (env,exp)) /\
       evaluate F env (0,s1) exp ((0,s2),output)`

val _ = type_abbrev("H",``:'a -> hol_refs # v store ->
                                 hol_refs # v store # (v,v) result -> bool``);

val PURE_def = Define `
  PURE a (x:'a) (refs1:hol_refs,s1:v store) (refs2,s2,res:(v,v) result) =
    ?v:v. (res = Rval v) /\ (refs1 = refs2) /\ (s1 = s2) /\ a x v`;

val ArrowP_def = Define `
  (ArrowP : 'a H -> 'b H -> ('a -> 'b) -> v -> bool) a b f c =
     !x refs1 s1 refs2 s2 (res:(v,v) result).
       a x (refs1,s1) (refs2,s2,res) /\ HOL_STORE s1 refs1 ==>
       (refs2 = refs1) /\ (s2 = s1) /\
       ?v s3 res3 refs3.
         (res = Rval v) /\ any_evaluate_closure (s2,v) c (s3,res3) /\
         b (f x) (refs1,s1) (refs3,s3,res3) /\ HOL_STORE s3 refs3`;

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

val EvalM_ArrowM = store_thm("EvalM_ArrowM",
  ``EvalM env x1 ((a -M-> b) f) ==>
    EvalM env x2 (a x) ==>
    EvalM env (App Opapp [x1;x2]) (b (f x))``,
  SIMP_TAC std_ss [EvalM_def,ArrowM_def,ArrowP_def,PURE_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ASSUM `!s. bbb` MP_TAC
  \\ Q.PAT_ASSUM `!s. bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ STRIP_TAC
  \\ `!x. evaluate F env (0,s) x1 x = (x = ((0,s),Rval v))` by
       METIS_TAC [determTheory.big_exp_determ]
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_list_cases,PULL_EXISTS]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`x`,`refs`,`s`,`refs2`,`s2`,`res`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ `!x. evaluate F env (0,s) x2 x <=> (x = ((0,s),Rval v'))` by
       METIS_TAC [determTheory.big_exp_determ]
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.LIST_EXISTS_TAC [`s3`,`res3`,`refs3`] \\ FULL_SIMP_TAC std_ss []
  \\ DISJ1_TAC \\ FULL_SIMP_TAC std_ss [any_evaluate_closure_def]);

val EvalM_Fun = store_thm("EvalM_Fun",
  ``(!v x. a x v ==> EvalM (write name v env) body (b (f x))) ==>
    EvalM env (Fun name body) ((PURE a -M-> b) f)``,
  SIMP_TAC std_ss [EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_FORALL]
  \\ PairCases_on `env` \\ FULL_SIMP_TAC (srw_ss())
       [any_evaluate_closure_def,do_app_def,do_opapp_def,bind_def,write_def]);

val EvalM_Fun_Eq = store_thm("EvalM_Fun_Eq",
  ``(!v. a x v ==> EvalM (write name v env) body (b (f x))) ==>
    EvalM env (Fun name body) ((PURE (Eq a x) -M-> b) f)``,
  SIMP_TAC std_ss [EvalM_def,ArrowM_def,ArrowP_def,PURE_def,Eq_def]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS,PULL_FORALL]
  \\ PairCases_on `env` \\ FULL_SIMP_TAC (srw_ss())
       [any_evaluate_closure_def,do_app_def,do_opapp_def,bind_def,write_def]);

val Eval_IMP_PURE = store_thm("Eval_IMP_PURE",
  ``Eval env exp (P x) ==> EvalM env exp (PURE P x)``,
  SIMP_TAC std_ss [Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `res`
  \\ IMP_RES_TAC evaluate_empty_store_IMP
  \\ ASM_SIMP_TAC std_ss []);

val HOL_TYPE_TYPE_EXISTS = prove(
  ``?ty v. HOL_TYPE_TYPE ty v``,
  Q.EXISTS_TAC `Tyvar []`
  \\ fs [fetch "-" "HOL_TYPE_TYPE_def", fetch "-" "LIST_TYPE_def"]);

val HOL_TERM_TYPE_EXISTS = prove(
  ``?tm v. HOL_TERM_TYPE tm v``,
  STRIP_ASSUME_TAC HOL_TYPE_TYPE_EXISTS
  \\ Q.EXISTS_TAC `Var [] ty`
  \\ fs [fetch "-" "HOL_TERM_TYPE_def",fetch "-" "LIST_TYPE_def"]
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []);

val HOL_STORE_EXISTS = prove(
  ``?s refs. HOL_STORE s refs``,
  SIMP_TAC std_ss [HOL_STORE_def]
  \\ STRIP_ASSUME_TAC HOL_TERM_TYPE_EXISTS
  \\ Q.EXISTS_TAC `[Refv (Conv (SOME ("nil",TypeId (Short "list"))) []);
                    Refv (Conv (SOME ("nil",TypeId (Short "list"))) []);
                    Refv (Conv (SOME ("nil",TypeId (Short "list"))) []);
                    Refv v]`
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,EL,HD,TL,isRefv_def]
  \\ Q.EXISTS_TAC `<| the_type_constants := [] ;
                      the_term_constants := [] ;
                      the_definitions := [] ;
                      the_clash_var := tm |>`
  \\ FULL_SIMP_TAC (srw_ss()) [fetch "-" "LIST_TYPE_def"]);

val EvalM_ArrowM_IMP = store_thm("EvalM_ArrowM_IMP",
  ``EvalM env (Var x) ((a -M-> b) f) ==>
    Eval env (Var x) (ArrowP a b f)``,
  SIMP_TAC std_ss [ArrowM_def,EvalM_def,Eval_def,PURE_def,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC HOL_STORE_EXISTS
  \\ RES_TAC \\ Q.EXISTS_TAC `v` \\ ASM_SIMP_TAC std_ss []
  \\ NTAC 2 (POP_ASSUM MP_TAC) \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SIMP_TAC (srw_ss()) []);

val EvalM_PURE_EQ = store_thm("EvalM_PURE_EQ",
  ``EvalM env (Fun n exp) (PURE P x) = Eval env (Fun n exp) (P x)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_IMP_PURE]
  \\ FULL_SIMP_TAC std_ss [Eval_def,EvalM_def,PURE_def,PULL_EXISTS]
  \\ STRIP_ASSUME_TAC HOL_STORE_EXISTS \\ RES_TAC
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SIMP_TAC (srw_ss()) []);

val EvalM_Var_SIMP = store_thm("EvalM_Var_SIMP",
  ``EvalM (write n x env) (Var (Short y)) p =
    if n = y then EvalM (write n x env) (Var (Short y)) p
             else EvalM env (Var (Short y)) p``,
  SIMP_TAC std_ss [EvalM_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases] \\ PairCases_on `env`
  \\ ASM_SIMP_TAC (srw_ss()) [Once evaluate_cases,write_def,lookup_var_id_def]);

val option_CASE_LEMMA2 = prove(
  Pmatch.with_classic_heuristic Term
  `!topt. (case topt of NONE => v | SOME z => v) = v`,
  Cases \\ SRW_TAC [] [] \\ Cases_on `x` \\ SRW_TAC [] []);

val EvalM_Recclosure = store_thm("EvalM_Recclosure",
  ``(!v. a n v ==>
         EvalM (write name v (write_rec [(fname,name,body)] env2))
               body (b (f n))) ==>
    LOOKUP_VAR fname env (Recclosure env2 [(fname,name,body)] fname) ==>
    EvalM env (Var (Short fname)) ((PURE (Eq a n) -M-> b) f)``,
  `?menv cenv eenv. env2 = (menv,cenv,eenv)` by METIS_TAC [PAIR]
  \\ NTAC 2 STRIP_TAC \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_def,Arrow_def,EvalM_def,ArrowM_def,PURE_def,
    PULL_EXISTS,ArrowP_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [AppReturns_def,Eq_def,do_app_def,do_opapp_def,
       evaluate_closure_def,any_evaluate_closure_def,option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC (srw_ss()) [Once find_recfun_def,Eval_def]
  \\ FULL_SIMP_TAC (srw_ss()) [bind_def,build_rec_env_def,FOLDR,
       write_rec_def,write_def]);

val IND_HELP = store_thm("IND_HELP",
  ``!env cl.
      LOOKUP_VAR x env cl /\
      EvalM env (Var (Short x)) ((b1 -M-> b2) f) ==>
      EvalM (write x cl cl_env) (Var (Short x)) ((b1 -M-> b2) f)``,
  SIMP_TAC std_ss [EvalM_def,Eval_def,ArrowM_def,PURE_def,PULL_EXISTS,LOOKUP_VAR_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ PairCases_on `env` \\ PairCases_on `cl_env`
  \\ FULL_SIMP_TAC (srw_ss()) [lookup_var_id_def,write_def,lookup_var_def]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []);

val write_rec_one = store_thm("write_rec_one",
  ``write_rec [(x,y,z)] env = write x (Recclosure env [(x,y,z)] x) env``,
  PairCases_on `env`
  \\ SIMP_TAC std_ss [write_rec_def,write_def,build_rec_env_def,FOLDR,bind_def]);

(* Eq simps *)

val EvalM_FUN_FORALL = store_thm("EvalM_FUN_FORALL",
  ``(!x. EvalM env exp (PURE (p x) f)) ==>
    EvalM env exp (PURE (FUN_FORALL x. p x) f)``,
  SIMP_TAC std_ss [EvalM_def,Eq_def,PURE_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AppReturns_def,FUN_FORALL,PULL_EXISTS]
  \\ RES_TAC \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `ARB`)
  \\ Q.EXISTS_TAC `v` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ `!x. evaluate F env (0,s) exp x = (x = ((0,s),Rval v))` by
       METIS_TAC [determTheory.big_exp_determ]
  \\ FULL_SIMP_TAC (srw_ss()) []);

val EvalM_FUN_FORALL_EQ = store_thm("EvalM_FUN_FORALL_EQ",
  ``(!x. EvalM env exp (PURE (p x) f)) =
    EvalM env exp (PURE (FUN_FORALL x. p x) f)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [EvalM_FUN_FORALL]
  \\ fs [EvalM_def,PURE_def,PULL_EXISTS,FUN_FORALL] \\ METIS_TAC []);

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
  \\ `!x. evaluate F env (0,s3) exp x = (x = ((0,s3),Rval v))`
       by METIS_TAC [determTheory.big_exp_determ]
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
  ``!x a. EvalM env (Raise (Lit Unit)) (HOL_MONAD a (failwith x))``,
  SIMP_TAC (srw_ss()) [Eval_def,EvalM_def,HOL_MONAD_def,failwith_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

(* otherwise *)

val EvalM_otherwise = store_thm("EvalM_otherwise",
  ``!n. EvalM env exp1 (HOL_MONAD a x1) ==>
        (!i. EvalM (write n i env) exp2 (HOL_MONAD a x2)) ==>
        EvalM env (Handle exp1 [(Pvar n,exp2)]) (HOL_MONAD a (x1 otherwise x2))``,
  SIMP_TAC std_ss [EvalM_def] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ Q.PAT_ASSUM `!s refs. bb ==> bbb` (MP_TAC o Q.SPECL [`s`,`refs`])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `res` THEN1
   (Q.LIST_EXISTS_TAC [`s2`,`Rval a'`,`refs2`]
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [HOL_MONAD_def]
    \\ Cases_on `x1 refs` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def])
  \\ Q.PAT_ASSUM `HOL_MONAD xx yy t1 t2` MP_TAC
  \\ SIMP_TAC std_ss [Once HOL_MONAD_def] \\ STRIP_TAC
  \\ Cases_on `x1 refs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def]
  \\ Cases_on `e` \\ FULL_SIMP_TAC (srw_ss()) [otherwise_def]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a'`,`s2`,`refs2`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s2'`,`res`,`refs2'`]
  \\ FULL_SIMP_TAC (srw_ss()) [HOL_MONAD_def]
  \\ DISJ2_TAC \\ DISJ1_TAC
  \\ Q.LIST_EXISTS_TAC [`0,s2`,`a'`] \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,pat_bindings_def,pmatch_def]
  \\ PairCases_on `env` \\ FULL_SIMP_TAC (srw_ss()) [bind_def,write_def]);

(* if *)

val EvalM_If = store_thm("EvalM_If",
  ``(a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> EvalM env x2 (a b2)) /\
    (a3 ==> EvalM env x3 (a b3)) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     EvalM env (If x1 x2 x3) (a (if b1 then b2 else b3)))``,
  SIMP_TAC std_ss [EvalM_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss [CONTAINER_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `b1` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  THEN1
   (Q.LIST_EXISTS_TAC [`s2`,`res`,`refs2`] \\ ASM_SIMP_TAC std_ss []
    \\ DISJ1_TAC
    \\ Q.EXISTS_TAC `Litv (Bool T)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
    \\ Q.EXISTS_TAC `0,s` \\ FULL_SIMP_TAC std_ss [Eval_def]
    \\ IMP_RES_TAC evaluate_empty_store_IMP
    \\ FULL_SIMP_TAC std_ss [])
  THEN1
   (Q.LIST_EXISTS_TAC [`s2`,`res`,`refs2`] \\ ASM_SIMP_TAC std_ss []
    \\ DISJ1_TAC
    \\ Q.EXISTS_TAC `Litv (Bool F)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]
    \\ Q.EXISTS_TAC `0,s` \\ FULL_SIMP_TAC std_ss [Eval_def]
    \\ IMP_RES_TAC evaluate_empty_store_IMP
    \\ FULL_SIMP_TAC std_ss []));

val Eval_Var_SIMP2 = store_thm("Eval_Var_SIMP2",
  ``Eval (write x i env) (Var (Short y)) p =
      if x = y then p i else Eval env (Var (Short y)) p``,
  SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,lookup_def] \\ SRW_TAC [] []
  \\ ASM_SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,lookup_def]
  \\ PairCases_on `env` \\ ASM_SIMP_TAC (srw_ss()) [Eval_def,
       Once evaluate_cases,lookup_def,lookup_var_id_def,write_def]);

val EvalM_Let = store_thm("EvalM_Let",
  ``Eval env exp (a res) /\
    (!v. a res v ==> EvalM (write name v env) body (b (f res))) ==>
    EvalM env (Let (SOME name) exp body) (b (LET f res))``,
  SIMP_TAC std_ss [Eval_def,Arrow_def,EvalM_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`s2`,`res''`,`refs2`]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,bind_def] \\ DISJ1_TAC
  \\ PairCases_on `env` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`res'`,`0,s`]
  \\ IMP_RES_TAC evaluate_empty_store_IMP
  \\ FULL_SIMP_TAC std_ss [opt_bind_def,write_def]);

(* declarations *)

val M_DeclAssum_Dlet_INTRO = store_thm("M_DeclAssum_Dlet_INTRO",
  ``(!env. DeclAssum mn ds env tys ==> EvalM env (Fun n exp) (PURE P x)) ==>
    (!v env. DeclAssum mn (SNOC (Dlet (Pvar v) (Fun n exp)) ds) env tys ==>
             EvalM env (Var (Short v)) (PURE P x))``,
  METIS_TAC [DeclAssum_Dlet_INTRO,EvalM_PURE_EQ,Eval_IMP_PURE]);

val M_DeclAssum_Dletrec_INTRO = store_thm("M_DeclAssum_Dletrec_INTRO",
  ``(!env1 env.
      DeclAssum mn ds env tys /\
      LOOKUP_VAR v env1 (Recclosure env [(v,xs,f)] v) ==>
      EvalM env1 (Var (Short v)) (PURE P x)) ==>
    !env. DeclAssum mn (SNOC (Dletrec [(v,xs,f)]) ds) env tys ==>
          EvalM env (Var (Short v)) (PURE P x)``,
  FULL_SIMP_TAC std_ss [DeclAssum_def,SNOC_APPEND,Decls_APPEND,Decls_Dletrec,
    MAP,ALL_DISTINCT,MEM,PULL_EXISTS,build_rec_env_def,FOLDR,bind_def,
    Eval_Var_SIMP,LOOKUP_VAR_SIMP]
  \\ FULL_SIMP_TAC std_ss [EvalM_def,PURE_def,PULL_EXISTS]
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!env1.bbb` (MP_TAC o
        Q.SPEC `write v (Recclosure env2 [(v,xs,f)] v) env`)
  \\ PairCases_on `env` \\ PairCases_on `env2`
  \\ FULL_SIMP_TAC (srw_ss()) [LOOKUP_VAR_SIMP,lookup_def,bind_def,
       merge_def,write_rec_def,write_def,lookup_var_id_def,lookup_var_def,
       build_rec_env_def] \\ METIS_TAC []);

(* fast-ish evaluation *)

val evaluate_SIMP =
  [``evaluate a0 a1 x (Letrec o' e) a3``,
   ``evaluate a0 a1 x (Let s e e0) a3``,
   ``evaluate a0 a1 x (Mat e l) a3``,
   ``evaluate a0 a1 x (If e e0 e1) a3``,
   ``evaluate a0 a1 x (Log l e e0) a3``,
   ``evaluate a0 a1 x (App o' e0) a3``,
   ``evaluate a0 a1 x (Fun s e) a3``,
   ``evaluate a0 a1 x (Var s) a3``,
   ``evaluate a0 a1 x (Con s l) a3``,
   ``evaluate a0 a1 x (Lit l) a3``,
   ``evaluate a0 a1 x (Handle e s) a3``,
   ``evaluate a0 a1 x (Raise e) a3``,
   ``evaluate_list a0 a1 x [] a3``,
   ``evaluate_list a0 a1 x (h::t) a3``]
  |> map (SIMP_CONV (srw_ss()) [Once evaluate_cases])
  |> LIST_CONJ;

fun get_tm_eval () = let
  val tm = get_DeclAssum () |> rator |> rand;
  fun get_all n =
    fetch "-" ("ml_monad_decls_" ^ (int_to_string n)) :: get_all (n+1)
    handle HOL_ERR _ => []
  in tm |> REWRITE_CONV (get_all 0 @ [APPEND,SNOC_APPEND]) end

val SWAP_EXISTS = METIS_PROVE [] ``(?x y. P x y) ==> (?y x. P x y)``

val DeclAssumExists_SNOC_Dlet_Ref_lemma = prove(
  ``!ds name n exp P.
      (!env tys. DeclAssum mn ds env tys ==> Eval env exp P) ==>
      DeclAssumExists mn ds ==>
      DeclAssumExists mn (SNOC (Dlet (Pvar name) (App Opref [exp])) ds)``,
  SIMP_TAC std_ss [DeclAssumExists_def,PULL_EXISTS] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [DeclAssum_def,Decls_APPEND,SNOC_APPEND,PULL_EXISTS]
  \\ RES_TAC \\ SIMP_TAC std_ss [Decls_def] \\ ONCE_REWRITE_TAC [CONJ_COMM]
  \\ SIMP_TAC std_ss [Once evaluate_decs_cases]
  \\ SIMP_TAC (srw_ss()) [CONS_11,NOT_CONS_NIL,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,Once evaluate_decs_cases]
  \\ SIMP_TAC (srw_ss()) [PULL_EXISTS,Once evaluate_dec_cases]
  \\ SIMP_TAC std_ss [merge_def,APPEND_NIL]
  \\ SIMP_TAC (srw_ss()) [pmatch_def,ALL_DISTINCT,pat_bindings_def,
       combine_dec_result_def,merge_envC_def,emp_def]
  \\ FULL_SIMP_TAC std_ss [Decls_def,Eval_def,evaluate_empty_store_EQ]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ RES_TAC
  \\ Q.EXISTS_TAC `tys`
  \\ HO_MATCH_MP_TAC SWAP_EXISTS \\ Q.EXISTS_TAC `new_tds`
  \\ HO_MATCH_MP_TAC SWAP_EXISTS \\ Q.EXISTS_TAC `res_env`
  \\ HO_MATCH_MP_TAC SWAP_EXISTS \\ Q.EXISTS_TAC `Loc (LENGTH s)`
  \\ HO_MATCH_MP_TAC SWAP_EXISTS \\ Q.EXISTS_TAC `(0,s)`
  \\ FULL_SIMP_TAC std_ss [merge_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,do_app_def,LET_DEF,store_alloc_def]
  \\ fs [evaluate_list_cases,PULL_EXISTS]
   \\ Q.EXISTS_TAC `s` \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `res'` \\ FULL_SIMP_TAC std_ss [emp_def]);

val DeclAssumExists_SNOC_Dlet_Ref = prove(
  ``!ds name n exp P.
      (!env tys. DeclAssum mn ds env tys ==> Q env ==> Eval env exp P) ==>
      (!env tys. DeclAssum mn ds env tys ==> Q env) ==>
      DeclAssumExists mn ds ==>
      DeclAssumExists mn (SNOC (Dlet (Pvar name) (App Opref [exp])) ds)``,
  METIS_TAC [DeclAssumExists_SNOC_Dlet_Ref_lemma]);

fun all_decls () =
  (fetch "-" "ml_monad_decls_0" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_1" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_2" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_3" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_4" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_5" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_6" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_7" handle HOL_ERR _ => TRUTH) ::
  (fetch "-" "ml_monad_decls_8" handle HOL_ERR _ => TRUTH) :: [] |> LIST_CONJ;

fun DeclAssumExists_lemma lemma = let
  val th = DISCH (get_DeclAssum ()) lemma
           |> Q.GENL [`tys`,`env`]
           |> HO_MATCH_MP (DeclAssumExists_SNOC_Dlet_Ref |> SPEC_ALL)
  val goal = th |> concl |> dest_imp |> fst
  val l = MATCH_MP DeclAssumCons_cons_lookup (get_cenv_eq_thm ())
          |> CONV_RULE (REWRITE_CONV [EVERY_DEF] THENC
                        DEPTH_CONV PairRules.PBETA_CONV)
  in MP th (auto_prove "ref lemma" (goal,REPEAT STRIP_TAC THEN IMP_RES_TAC l)) end

val exp_size_lemma = prove(
  ``!xs a. MEM a xs ==> exp_size a <= exp6_size xs``,
  Induct \\ SRW_TAC [] [exp_size_def] \\ RES_TAC \\ DECIDE_TAC);

val obviously_pure_def = tDefine "obviously_pure" `
  (obviously_pure (Lit _) = T) /\
  (obviously_pure (Con n xs) = EVERY obviously_pure xs) /\
  (obviously_pure _ = F)`
  (WF_REL_TAC `measure exp_size` \\ SRW_TAC [] []
   \\ IMP_RES_TAC exp_size_lemma \\ DECIDE_TAC)

val simple_decl_def = Define `
  (simple_decl (Dtype y) = T) /\
  (simple_decl (Dlet (Pvar k) (App Opref [exp])) = obviously_pure exp) /\
  (simple_decl _ = F)`

val decl_let_def = Define `
  (decl_let (Dlet (Pvar k) y) = T) /\
  (decl_let _ = F)`

val obviously_pure_IMP = prove(
  ``!e s1 s2 v.
      obviously_pure e /\ evaluate F env2 s1 e (s2,Rval v) ==>
      (s2 = s1)``,
  HO_MATCH_MP_TAC (theorem "obviously_pure_ind")
  \\ SRW_TAC [] [obviously_pure_def,evaluate_SIMP]
  \\ FULL_SIMP_TAC std_ss [GSYM EVERY_MEM]
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
  \\ REPEAT (POP_ASSUM MP_TAC) \\ Q.SPEC_TAC (`env2`,`env`)
  \\ Q.SPEC_TAC (`s1`,`s1`) \\ Q.SPEC_TAC (`s2`,`s2`) \\ Q.SPEC_TAC (`vs`,`vs`)
  \\ Induct_on `xs` \\ SIMP_TAC (srw_ss()) [evaluate_SIMP,PULL_EXISTS]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val LENGTH_FILTER_decl_let = prove(
  ``!ds cs1 s2 env env2 tys.
      EVERY simple_decl ds /\ Decls mn env (cs1,tys) ds env2 s2 ==>
      (LENGTH (FILTER decl_let ds) + LENGTH (SND cs1) = LENGTH (SND (FST s2)))``,
  Induct \\ SRW_TAC [] [Decls_NIL,FILTER,LENGTH]
  \\ Cases_on`cs1`
  \\ FULL_SIMP_TAC std_ss [Once Decls_CONS]
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [decl_let_def,simple_decl_def]
  \\ TRY (Cases_on `e`) \\ FULL_SIMP_TAC std_ss [decl_let_def,simple_decl_def]
  \\ TRY (Cases_on `p`) \\ FULL_SIMP_TAC std_ss [decl_let_def,simple_decl_def]
  \\ TRY (Cases_on `u`) \\ FULL_SIMP_TAC std_ss [decl_let_def,simple_decl_def]
  \\ FULL_SIMP_TAC std_ss [Decls_Dtype] \\ SRW_TAC [] [] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [Decls_Dlet]
  \\ Cases_on `o'` \\ fs [simple_decl_def]
  \\ Cases_on `l` \\ fs [simple_decl_def]
  \\ Cases_on `t` \\ fs [simple_decl_def]
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_SIMP,PULL_EXISTS] \\ SRW_TAC [] []
  \\ IMP_RES_TAC obviously_pure_IMP \\ Cases_on `s2'`
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def,store_alloc_def,LET_DEF]
  \\ SRW_TAC [] [] \\ RES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,LENGTH_APPEND] \\ DECIDE_TAC);

val simple_decl_IMP = prove(
  ``EVERY simple_decl (SNOC (Dlet (Pvar n) exp) ds) /\
    (k = LENGTH (FILTER decl_let ds)) ==>
    (DeclAssum mn (SNOC (Dlet (Pvar n) exp) ds) env tys ==>
     Eval env (Var (Short n)) ((=) (Loc k)))``,
  Q.SPEC_TAC (`k`,`k`) \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [DeclAssum_def,Decls_APPEND,SNOC_APPEND,
       Decls_Dlet,Eval_Var_SIMP,EVERY_APPEND,EVERY_DEF]
  \\ Cases_on `exp` \\ fs [simple_decl_def,evaluate_SIMP]
  \\ Cases_on `l` \\ fs [simple_decl_def,evaluate_SIMP]
  \\ Cases_on `t` \\ fs [simple_decl_def]
  \\ Cases_on `o'` \\ fs [simple_decl_def]
  \\ SRW_TAC [] [] \\ fs [evaluate_list_cases] \\ SRW_TAC [] []
  \\ fs [simple_decl_def,do_app_def,LET_DEF,store_alloc_def]
  \\ SRW_TAC [] []
  \\ Cases_on `s2` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC LENGTH_FILTER_decl_let
  \\ IMP_RES_TAC obviously_pure_IMP
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [initSemEnvTheory.prim_sem_env_eq]);

fun tac () =
  SIMP_TAC std_ss [all_decls (),PULL_EXISTS]
  \\ CONV_TAC ((RAND_CONV o RAND_CONV) EVAL)
  \\ MATCH_MP_TAC simple_decl_IMP \\ EVAL_TAC


(* ref 0 *)

val lemma = hol2deep ``[("bool",0); ("fun",2:num)]`` |> D |> SIMP_RULE std_ss []
val exp = lemma |> UNDISCH_ALL |> concl |> rator |> rand
val dec = ``(Dlet (Pvar n) (App Opref [^exp])) : dec``
val tm = get_DeclAssum () |> rator |> rator |> rand;

val the_type_constants_def = Define `
    the_type_constants = Loc 0`;

val th = prove(
  ``DeclAssum (SOME "Kernel") (SNOC ^dec ^tm) env tys ==>
    Eval env (Var (Short n)) ($= the_type_constants)``,
  tac ()) |> Q.INST [`n`|->`"the_type_constants"`] |> UNDISCH;

val th = store_cert th [TRUTH] (DeclAssumExists_lemma lemma);


(* ref 1 *)

val lemma = hol2deep ``[("=", Tyapp "fun" [Tyvar "A"; Tyvar "A"])]``
            |> D |> SIMP_RULE std_ss []
val exp = lemma |> UNDISCH_ALL |> concl |> rator |> rand
val dec = ``(Dlet (Pvar n) (App Opref [^exp])) : dec``
val tm = get_DeclAssum () |> rator |> rator |> rand;

val the_term_constants_def = Define `
    the_term_constants = Loc 1`;

val th = prove(
  ``DeclAssum (SOME "Kernel") (SNOC ^dec ^tm) env tys ==>
    Eval env (Var (Short n)) ($= the_term_constants)``,
  tac ()) |> Q.INST [`n`|->`"the_term_constants"`] |> UNDISCH;

val th = store_cert th [TRUTH] (DeclAssumExists_lemma lemma);


(* ref 2 *)

val lemma = hol2deep ``[]:def list`` |> D |> SIMP_RULE std_ss []
val exp = lemma |> UNDISCH_ALL |> concl |> rator |> rand
val dec = ``(Dlet (Pvar n) (App Opref [^exp])) : dec``
val tm = get_DeclAssum () |> rator |> rator |> rand;

val the_definitions_def = Define `
    the_definitions = Loc 2`;

val th = prove(
  ``DeclAssum (SOME "Kernel") (SNOC ^dec ^tm) env tys ==>
    Eval env (Var (Short n)) ($= the_definitions)``,
  tac ()) |> Q.INST [`n`|->`"the_definitions"`] |> UNDISCH;

val th = store_cert th [TRUTH] (DeclAssumExists_lemma lemma);


(* ref 3 *)

val lemma = hol2deep ``Var "a" (Tyvar "a")`` |> D |> SIMP_RULE std_ss []
val exp = lemma |> UNDISCH_ALL |> concl |> rator |> rand
val dec = ``(Dlet (Pvar n) (App Opref [^exp])) : dec``
val tm = get_DeclAssum () |> rator |> rator |> rand;

val the_clash_var_def = Define `
    the_clash_var = Loc 3`;

val th = prove(
  ``DeclAssum (SOME "Kernel") (SNOC ^dec ^tm) env tys ==>
    Eval env (Var (Short n)) ($= the_clash_var)``,
  tac ()) |> Q.INST [`n`|->`"the_clash_var"`] |> UNDISCH;

val th = store_cert th [TRUTH] (DeclAssumExists_lemma lemma);


(* read and update refs *)

fun read_tac n =
  SIMP_TAC std_ss [Eval_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [EvalM_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) [merge_def,emp_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) [merge_def,emp_def]
  \\ fs [the_type_constants_def,
       the_term_constants_def,the_definitions_def,
       the_clash_var_def,PULL_EXISTS,evaluate_list_cases,do_app_def,
       store_lookup_def,option_CASE_LEMMA2]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [HOL_STORE_def]
  \\ `0 < LENGTH s` by DECIDE_TAC
  \\ `1 < LENGTH s` by DECIDE_TAC
  \\ `2 < LENGTH s` by DECIDE_TAC
  \\ `3 < LENGTH s` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`s`,`Rval (case EL ^n s of Refv v => v)`,`refs`]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [HOL_MONAD_def,get_the_type_constants_def,
        get_the_term_constants_def,get_the_clash_var_def,
        get_the_definitions_def,EL,isRefv_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ fs [merge_def,emp_def];

val get_type_constants_thm = store_thm("get_the_type_constants_thm",
  ``Eval env (Var (Short "the_type_constants")) ($= the_type_constants) ==>
    EvalM env (App Opderef [Var (Short "the_type_constants")])
      (HOL_MONAD (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM))
                 get_the_type_constants)``,
  read_tac ``0:num``);

val get_term_constants_thm = store_thm("get_the_term_constants_thm",
  ``Eval env (Var (Short "the_term_constants")) ($= the_term_constants) ==>
    EvalM env (App Opderef [Var (Short "the_term_constants")])
      (HOL_MONAD (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE))
                 get_the_term_constants)``,
  read_tac ``1:num``);

val get_the_definitions_thm = store_thm("get_the_definitions_thm",
  ``Eval env (Var (Short "the_definitions")) ($= the_definitions) ==>
    EvalM env (App Opderef [Var (Short "the_definitions")])
      (HOL_MONAD (LIST_TYPE DEF_TYPE) get_the_definitions)``,
  read_tac ``2:num``);

val get_the_clash_var_thm = store_thm("get_the_clash_var_thm",
  ``Eval env (Var (Short "the_clash_var")) ($= the_clash_var) ==>
    EvalM env (App Opderef [Var (Short "the_clash_var")])
      (HOL_MONAD HOL_TERM_TYPE get_the_clash_var)``,
  read_tac ``3:num``);

fun update_tac r q =
  SIMP_TAC std_ss [Once Eval_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [option_CASE_LEMMA2]
  \\ STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [EvalM_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) [merge_def,emp_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
  \\ fs [evaluate_list_cases,PULL_EXISTS]
  \\ `evaluate F env (0,s) exp ((0,s),Rval res)` by
        METIS_TAC [evaluate_empty_store_IMP]
  \\ `!x. evaluate F env (0,s) exp x = (x = ((0,s),Rval res))` by
        METIS_TAC [determTheory.big_exp_determ]
  \\ fs [] \\ SIMP_TAC (srw_ss()) [Once do_app_def]
  \\ FULL_SIMP_TAC std_ss [option_CASE_LEMMA2,PULL_EXISTS]
  \\ FULL_SIMP_TAC std_ss [the_type_constants_def,
       the_term_constants_def,the_definitions_def,the_clash_var_def]
  \\ `0 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `1 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `2 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ `3 < LENGTH s` by FULL_SIMP_TAC(srw_ss()++ARITH_ss)[HOL_STORE_def]
  \\ ASM_SIMP_TAC (srw_ss()) [store_assign_def]
  \\ Q.LIST_EXISTS_TAC [r,`Rval (Litv Unit)`,q] \\ fs []
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ fs [store_v_same_type_def]
  \\ FULL_SIMP_TAC std_ss [HOL_STORE_def,EL_LUPDATE]
  \\ fs [HOL_STORE_def,EL_LUPDATE,isRefv_def]
  \\ EVAL_TAC;

val set_the_type_constants_thm = store_thm("set_the_type_constants_thm",
  ``Eval env (Var (Short "the_type_constants")) ($= the_type_constants) ==>
    Eval env exp (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM) x) ==>
    EvalM env (App Opassign [Var (Short "the_type_constants"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_type_constants x))``,
  update_tac `LUPDATE (Refv res) 0 s` `refs with the_type_constants := x`);

val set_the_term_constants_thm = store_thm("set_the_term_constants_thm",
  ``Eval env (Var (Short "the_term_constants")) ($= the_term_constants) ==>
    Eval env exp (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE) x) ==>
    EvalM env (App Opassign [Var (Short "the_term_constants"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_term_constants x))``,
  update_tac `LUPDATE (Refv res) 1 s` `refs with the_term_constants := x`);

val set_the_definitions_thm = store_thm("set_the_definitions_thm",
  ``Eval env (Var (Short "the_definitions")) ($= the_definitions) ==>
    Eval env exp (LIST_TYPE DEF_TYPE x) ==>
    EvalM env (App Opassign [Var (Short "the_definitions"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_definitions x))``,
  update_tac `LUPDATE (Refv res) 2 s` `refs with the_definitions := x`);

val set_the_clash_var_thm = store_thm("set_the_clash_var_thm",
  ``Eval env (Var (Short "the_clash_var")) ($= the_clash_var) ==>
    Eval env exp (HOL_TERM_TYPE x) ==>
    EvalM env (App Opassign [Var (Short "the_clash_var"); exp])
      ((HOL_MONAD UNIT_TYPE) (set_the_clash_var x))``,
  update_tac `LUPDATE (Refv res) 3 s` `refs with the_clash_var := x`);

val _ = (print_asts := true);

val _ = export_theory();
