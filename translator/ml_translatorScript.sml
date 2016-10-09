open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     determTheory evalPropsTheory bigClockTheory packLib;
open mlstringTheory integerTheory;
open terminationTheory ml_progTheory;

val _ = new_theory "ml_translator";

infix \\ val op \\ = op THEN;

val evaluate_ind = bigStepTheory.evaluate_ind;

val _ = bring_to_front_overload"evaluate"{Name="evaluate",Thy="bigStep"};
val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(* Definitions *)

val empty_state_def = Define`
  empty_state = <|
    clock := 0;
    refs := empty_store;
    (* force the ffi state to unit
       the translator does not currently support ffi *)
    ffi := initial_ffi_state ARB ();
    defined_types := {};
    defined_mods := {}|>`;

val Eval_def = Define `
  Eval env exp P =
    !refs. ?res refs'.
      evaluate F env (empty_state with refs := refs) exp
        (empty_state with refs := refs ++ refs',Rval res) /\
      P (res:v)`;

val AppReturns_def = Define ` (* think of this as a Hoare triple {P} cl {Q} *)
  AppReturns P cl Q =
    !v. P v ==>
      !refs. ?env exp refs' u.
        do_opapp [cl;v] = SOME (env,exp) /\
        evaluate F env (empty_state with refs := refs) exp
          (empty_state with refs := refs++refs',Rval u) /\
        Q u`;

val Arrow_def = Define `
  Arrow a b =
    \f v. !x. AppReturns (a x) v (b (f x))`;

val _ = overload_on ("-->",``Arrow``)

val Eq_def = Define `
  Eq (abs:'a->v->bool) x =
    (\y v. (x = y) /\ abs y v)`;

val And_def = Define `And a P x v = (P x /\ a (x:'a) (v:v))`;

val UNIT_TYPE_def = Define `
  UNIT_TYPE (u:unit) (v:v) = (v = Conv NONE [])`;

val INT_def = Define `
  INT i = \v:v. (v = Litv (IntLit i))`;

val NUM_def = Define `
  NUM n = INT (& n)`;

val BOOL_def = Define `
  BOOL b = \v:v. (v = Boolv b)`;

val WORD_def = Define `
  WORD (w:'a word) =
    \v:v. dimindex (:'a) <= 64 /\
          (v = Litv (if dimindex (:'a) <= 8
                     then Word8 (w2w w << (8 - dimindex (:'a)))
                     else Word64 (w2w w << (64 - dimindex (:'a)))))`;

val CHAR_def = Define`
  CHAR (c:char) = \v:v. (v = Litv (Char c))`;

val STRING_TYPE_def = Define`
  STRING_TYPE (s:mlstring) = \v:v. (v = Litv (StrLit (explode s)))`;

val CONTAINER_def = Define `CONTAINER x = x`;

val TAG_def = Define `TAG n x = x`;

val PRECONDITION_def = Define `PRECONDITION b = (b:bool)`;

val PreImp_def = Define `
  PreImp b1 b2 = (PRECONDITION b1 ==> b2)`;


(* Theorems *)

val evaluate_11_Rval = store_thm("evaluate_11_Rval",
  ``evaluate b env s exp (s1,Rval res1) ==>
    evaluate b env s exp (s2,Rval res2) ==> (res1 = res2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC big_exp_determ
  \\ FULL_SIMP_TAC (srw_ss()) []);

val Eval_Arrow = store_thm("Eval_Arrow",
  ``Eval env x1 ((a --> b) f) ==>
    Eval env x2 (a x) ==>
    Eval env (App Opapp [x1;x2]) (b (f x))``,
  rw[Eval_def,Arrow_def,AppReturns_def] \\
  rw[Once evaluate_cases] \\
  ntac 3 (rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]) \\
  METIS_TAC[APPEND_ASSOC]);

val Eval_Fun = store_thm("Eval_Fun",
  ``(!v x. a x v ==> Eval (write name v env) body (b ((f:'a->'b) x))) ==>
    Eval env (Fun name body) ((a --> b) f)``,
  rw[Eval_def,Arrow_def,AppReturns_def] \\
  rw[Once evaluate_cases,state_component_equality]
  \\ FULL_SIMP_TAC (srw_ss()) [AppReturns_def,do_opapp_def,write_def]
  \\ metis_tac[]);

val Eval_Fun_Eq = store_thm("Eval_Fun_Eq",
  ``(!v. a x v ==> Eval (write name v env) body (b (f x))) ==>
    Eval env (Fun name body) ((Eq a x --> b) f)``,
  rw[Eval_def,Arrow_def,AppReturns_def] \\
  rw[Once evaluate_cases,state_component_equality]
  \\ FULL_SIMP_TAC (srw_ss()) [AppReturns_def,do_opapp_def,write_def]
  \\ METIS_TAC[Eq_def]);

val And_IMP_Eq = store_thm("And_IMP_Eq",
  ``Eval env exp ((And a P --> b) f) ==>
    (P x ==> Eval env exp ((Eq a x --> b) f))``,
  FULL_SIMP_TAC std_ss [Eval_def,Arrow_def,AppReturns_def,And_def,Eq_def]
  \\ METIS_TAC []);

val Eq_IMP_And = store_thm("Eq_IMP_And",
  ``(!x. P x ==> Eval env (Fun name exp) ((Eq a x --> b) f)) ==>
    Eval env (Fun name exp) ((And a P --> b) f)``,
  simp[Eval_def,Arrow_def,AppReturns_def,And_def,Eq_def]
  \\ ntac 2 (rw[Once evaluate_cases])
  \\ fs[state_component_equality]);

val Eval_Fun_And = store_thm("Eval_Fun_And",
  ``(!v x. P x ==> a x v ==> Eval (write name v env) body (b (f x))) ==>
    Eval env (Fun name body) ((And a P --> b) f)``,
  FULL_SIMP_TAC std_ss [GSYM And_def,AND_IMP_INTRO]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC Eval_Fun \\ ASM_SIMP_TAC std_ss []);

val Eval_Let = store_thm("Eval_Let",
  ``Eval env exp (a res) /\
    (!v. a res v ==> Eval (write name v env) body (b (f res))) ==>
    Eval env (Let (SOME name) exp body) (b (LET f res))``,
  rw[Eval_def,write_def] \\
  rw[Once evaluate_cases,PULL_EXISTS,opt_bind_def] \\
  metis_tac[APPEND_ASSOC]);

val lookup_var_def = Define `
  lookup_var name env = ALOOKUP env.v name`;

val lookup_cons_def = Define `
  lookup_cons name (env:v environment) = SND_ALOOKUP env.c name`;

val lookup_mod_def = Define `
  lookup_mod name env = ALOOKUP env.m name`;

val lookup_cons_thm = store_thm("lookup_cons_thm",
  ``lookup_cons name (env:v environment) =
      lookup_alist_mod_env (Short name) env.c``,
  Cases_on `env.c`
  \\ fs [lookup_cons_def,lookup_alist_mod_env_def,SND_ALOOKUP_EQ_ALOOKUP]);

val lookup_var_id_thm = store_thm("lookup_var_id_thm",
  ``(lookup_var_id (Short v) env = lookup_var v env) /\
    (lookup_var_id (Long mn v) env =
       case lookup_mod mn env of
       | NONE => NONE
       | SOME env1 => ALOOKUP env1 v)``,
  fs [lookup_var_id_def,lookup_mod_def,lookup_var_def] \\ CASE_TAC \\ fs []);

val lookup_var_write = store_thm("lookup_var_write",
  ``(lookup_var v (write w x env) = if v = w then SOME x else lookup_var v env) /\
    (lookup_var_id (Short v) (write w x env) =
        if v = w then SOME x else lookup_var_id (Short v) env) /\
    (lookup_var_id (Long mn v) (write w x env) =
        lookup_var_id (Long mn v) env) /\
    (lookup_cons name (write w x env) = lookup_cons name env)``,
  fs [lookup_var_id_def,lookup_var_def,write_def,lookup_cons_thm] \\ rw []);

val lookup_var_write_mod = store_thm("lookup_var_write_mod",
  ``(lookup_var v (write_mod mn e1 env) = lookup_var v env) /\
    (lookup_mod m (write_mod mn e1 env) =
     if m = mn then SOME e1.v else lookup_mod m env) /\
    (lookup_cons name (write_mod mn e1 env) = lookup_cons name env)``,
  fs [lookup_var_id_def,lookup_var_def,write_mod_def,
      lookup_cons_thm,lookup_mod_def] \\ rw []
  \\ Cases_on `env.c` \\ fs [] \\ fs [lookup_alist_mod_env_def]);

val lookup_var_write_cons = store_thm("lookup_var_write_mod",
  ``(lookup_var v (write_cons n d env) = lookup_var v env) /\
    (lookup_mod m (write_cons n d env) = lookup_mod m env) /\
    (lookup_cons name (write_cons n d env) =
     if name = n then SOME d else lookup_cons name env)``,
  fs [lookup_var_id_def,lookup_var_def,write_cons_def,
      lookup_cons_thm,lookup_mod_def] \\ rw []
  \\ Cases_on `env.c` \\ fs []
  \\ fs [lookup_alist_mod_env_def,merge_alist_mod_env_def]);

val lookup_var_empty_env = store_thm("lookup_var_empty_env",
  ``(lookup_var v empty_env = NONE) /\
    (lookup_var_id (Short v) empty_env = NONE) /\
    (lookup_var_id (Long m v) empty_env = NONE) /\
    (lookup_cons name empty_env = NONE)``,
  fs [lookup_var_id_def,lookup_var_def,empty_env_def,lookup_cons_thm] \\ rw []
  \\ fs [lookup_alist_mod_env_def]);

val lookup_var_merge_env = store_thm("lookup_var_merge_env",
  ``(lookup_var v1 (merge_env e1 e2) =
       case lookup_var v1 e1 of
       | NONE => lookup_var v1 e2
       | res => res) /\
    (lookup_cons v1 (merge_env e1 e2) =
       case lookup_cons v1 e1 of
       | NONE => lookup_cons v1 e2
       | res => res) /\
    (lookup_mod v1 (merge_env e1 e2) =
       case lookup_mod v1 e1 of
       | NONE => lookup_mod v1 e2
       | res => res)``,
  fs [lookup_var_def,lookup_cons_thm,merge_env_def,ALOOKUP_APPEND,lookup_mod_def]
  \\ Cases_on `e1.c` \\ Cases_on `e2.c`
  \\ fs [lookup_alist_mod_env_def,ALOOKUP_APPEND]);

val Eval_Var_Short = store_thm("Eval_Var_Short",
  ``P v ==> !name env.
               (lookup_var_id (Short name) env = SOME v) ==>
               Eval env (Var (Short name)) P``,
  fs [Eval_def,Once evaluate_cases,state_component_equality]);

val Eval_Var_Long = store_thm("Eval_Var_Long",
  ``P v ==> !m name env.
               (lookup_var_id (Long m name) env = SOME v) ==>
               Eval env (Var (Long m name)) P``,
  fs [Eval_def,Once evaluate_cases,state_component_equality]);

val Eval_Var_SWAP_ENV = store_thm("Eval_Var_SWAP_ENV",
  ``!env1.
      Eval env1 (Var (Short name)) P /\
      (lookup_var name env = lookup_var name env1) ==>
      Eval env (Var (Short name)) P``,
  FULL_SIMP_TAC std_ss [FORALL_PROD,lookup_var_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def, lookup_var_id_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def, lookup_var_id_def]);

val LOOKUP_VAR_def = Define `
  LOOKUP_VAR name env x = (lookup_var name env = SOME x)`;

val LOOKUP_VAR_THM = store_thm("LOOKUP_VAR_THM",
  ``LOOKUP_VAR name env x ==> Eval env (Var (Short name)) ($= x)``,
  FULL_SIMP_TAC std_ss [FORALL_PROD,lookup_var_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def,LOOKUP_VAR_def,
       lookup_var_id_def,lookup_var_def,state_component_equality]);

val LOOKUP_VAR_SIMP = store_thm("LOOKUP_VAR_SIMP",
  ``LOOKUP_VAR name (write x v  env) y =
    if x = name then (v = y) else LOOKUP_VAR name env y``,
  ASM_SIMP_TAC std_ss [LOOKUP_VAR_def,lookup_var_id_def,write_def,
       lookup_var_def] \\ SRW_TAC [] []);

val Eval_Val_INT = store_thm("Eval_Val_INT",
  ``!n. Eval env (Lit (IntLit n)) (INT n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,NUM_def,INT_def,Eval_def,state_component_equality]);

val Eval_Val_NUM = store_thm("Eval_Val_NUM",
  ``!n. Eval env (Lit (IntLit (&n))) (NUM n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,NUM_def,INT_def,Eval_def,state_component_equality]);

val Eval_Val_UNIT = store_thm("Eval_Val_UNIT",
  ``Eval env (Con NONE []) (UNIT_TYPE ())``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,UNIT_TYPE_def,Eval_def,
     build_conv_def,do_con_check_def] \\ fs [Once evaluate_cases,state_component_equality]);

val Eval_Val_BOOL_T = store_thm("Eval_Val_BOOL_T",
  ``Eval env (App (Opb Leq) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL T)``,
  NTAC 5 (SIMP_TAC (srw_ss()) [Once evaluate_cases,BOOL_def,Eval_def,
    do_con_check_def,build_conv_def]) \\ fs [PULL_EXISTS]
  \\ fs [do_app_def] \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ EVAL_TAC \\ fs[]);

val Eval_Val_BOOL_F = store_thm("Eval_Val_BOOL_F",
  ``Eval env (App (Opb Lt) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL F)``,
  NTAC 5 (SIMP_TAC (srw_ss()) [Once evaluate_cases,BOOL_def,Eval_def,
    do_con_check_def,build_conv_def]) \\ fs [PULL_EXISTS]
  \\ fs [do_app_def] \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ EVAL_TAC \\ fs[]);

val Eval_Val_CHAR = store_thm("Eval_Val_CHAR",
  ``!c. Eval env (Lit (Char c)) (CHAR c)``,
  SIMP_TAC (srw_ss()) [CHAR_def,Eval_def,Once evaluate_cases,state_component_equality])

val Eval_Val_STRING = store_thm("Eval_Val_STRING",
  ``!s. Eval env (Lit (StrLit s)) (STRING_TYPE (strlit s))``,
  SIMP_TAC (srw_ss()) [STRING_TYPE_def,Eval_def,Once evaluate_cases,state_component_equality])

val Eval_Val_WORD = store_thm("Eval_Val_WORD",
  ``!w:'a word.
    dimindex(:'a) ≤ 64 ⇒
    Eval env (Lit (if dimindex(:'a) ≤ 8
                   then Word8 (w2w w << (8-dimindex(:'a)))
                   else Word64 (w2w w << (64-dimindex(:'a)))))
             (WORD w)``,
  SIMP_TAC (srw_ss()) [WORD_def,Eval_def,Once evaluate_cases,state_component_equality])

(* Equality *)

val no_closures_def = tDefine "no_closures" `
  (no_closures (Litv l) = T) /\
  (no_closures (Conv name vs) = EVERY no_closures vs) /\
  (no_closures _ = F)`
 (WF_REL_TAC `measure v_size` \\ REPEAT STRIP_TAC
  \\ Induct_on `vs` \\ FULL_SIMP_TAC (srw_ss()) [MEM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [MEM,v_size_def]
  \\ DECIDE_TAC)

val types_match_def = tDefine "types_match" `
  (types_match (Litv l1) (Litv l2) = lit_same_type l1 l2) /\
  (types_match (Loc l1) (Loc l2) = T) /\
  (types_match (Conv cn1 vs1) (Conv cn2 vs2) =
    (ctor_same_type cn1 cn2 /\ ((cn1 = cn2) ⇒ types_match_list vs1 vs2))) /\
  (types_match _ _ = F) /\
  (types_match_list [] [] = T) /\
  (types_match_list (v1::vs1) (v2::vs2) =
    (types_match v1 v2 /\ types_match_list vs1 vs2)) /\
(* We could change this case to T, or change the semantics to have a type error
 * when equality reaches unequal-length lists *)
  (types_match_list _ _ = F)`
  (WF_REL_TAC `measure (\x. case x of INL (v1,v2) => v_size v1 |
                                      INR (vs1,vs2) => v6_size vs1)`);

val EqualityType_def = Define `
  EqualityType (abs:'a->v->bool) <=>
    (!x1 v1. abs x1 v1 ==> no_closures v1) /\
    (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> ((v1 = v2) = (x1 = x2))) /\
    (!x1 v1 x2 v2. abs x1 v1 /\ abs x2 v2 ==> types_match v1 v2)`;

val Eq_lemma = prove(
  ``n < dimword (:'a) /\ dimindex (:α) <= k ==>
    (n * 2n ** (k − dimindex (:α))) < 2 ** k``,
  fs [dimword_def] \\ rw []
  \\ fs [LESS_EQ_EXISTS] \\ rw [] \\ fs [EXP_ADD]
  \\ simp_tac std_ss [Once MULT_COMM] \\ fs []);

val EqualityType_NUM_BOOL = store_thm("EqualityType_NUM_BOOL",
  ``EqualityType NUM /\ EqualityType INT /\
    EqualityType BOOL /\ EqualityType WORD /\
    EqualityType CHAR /\ EqualityType STRING_TYPE /\
    EqualityType UNIT_TYPE``,
  EVAL_TAC \\ fs [no_closures_def,
    types_match_def, lit_same_type_def,
    stringTheory.ORD_11,mlstringTheory.explode_11]
  \\ SRW_TAC [] [] \\ EVAL_TAC
  \\ fs [w2w_def] \\ Cases_on `x1` \\ Cases_on `x2`
  \\ fs [WORD_MUL_LSL,word_mul_n2w]
  \\ imp_res_tac Eq_lemma \\ fs []
  \\ fs [MULT_EXP_MONO |> Q.SPECL [`p`,`1`] |> SIMP_RULE bool_ss [EVAL ``SUC 1``]]);

val types_match_list_length = store_thm("types_match_list_length",
  ``!vs1 vs2. types_match_list vs1 vs2 ==> LENGTH vs1 = LENGTH vs2``,
  Induct \\ Cases_on`vs2` \\ rw[types_match_def])

val type_match_implies_do_eq_succeeds = store_thm(
  "type_match_implies_do_eq_succeeds",
  ``(!v1 v2. types_match v1 v2 ==> (do_eq v1 v2 = Eq_val (v1 = v2))) /\
    (!vs1 vs2.
       types_match_list vs1 vs2 ==> (do_eq_list vs1 vs2 = Eq_val (vs1 = vs2)))``,
  ho_match_mp_tac do_eq_ind
  \\ rw [do_eq_def, types_match_def]
  \\ imp_res_tac types_match_list_length
  \\ fs[] \\ Cases_on`cn1=cn2`\\fs[]
  \\ imp_res_tac types_match_list_length);

val do_eq_succeeds = prove(``
  (!a x1 v1 x2 v2. EqualityType a /\ a x1 v1 /\ a x2 v2 ==>
                   (do_eq v1 v2 = Eq_val (x1 = x2)))``,
 rw [EqualityType_def]
 \\ res_tac
 \\ imp_res_tac type_match_implies_do_eq_succeeds
 \\ Cases_on `v1 = v2`
 \\ fs []);

val empty_state_tac =
  srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][empty_state_def,ffiTheory.initial_ffi_state_def]
val empty_state_tac2 =
  fs[empty_state_def,ffiTheory.initial_ffi_state_def]
val record_simp_failure_tac =
  qmatch_abbrev_tac`bigStep$evaluate _ _ X _ (Y,_)`
  \\ `X = Y` by simp[Abbr`X`,Abbr`Y`,state_component_equality]
  \\ fs[]

val empty_state_with_refs_eq = Q.prove(
  `empty_state with refs := r =
   s2 with <| refs := r'; ffi := f |> ⇔
   ∃refs ffi.
   s2 = empty_state with <| refs := refs; ffi := ffi |> ∧
   r' = r ∧ f = empty_state.ffi`,
  rw[state_component_equality,EQ_IMP_THM]);

val empty_state_with_ffi_elim = Q.prove(
  `empty_state with <| refs := r; ffi := empty_state.ffi |> =
   empty_state with refs := r`,
  rw[state_component_equality]);

val Eval_Equality = store_thm("Eval_Equality",
  ``Eval env x1 (a y1) /\ Eval env x2 (a y2) ==>
    EqualityType a ==>
    Eval env (App Equality [x1;x2]) (BOOL (y1 = y2))``,
  SIMP_TAC std_ss [Eval_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ntac 3 (rw [Once (hd (tl (CONJUNCTS evaluate_cases)))])
  \\ fs[PULL_EXISTS,empty_state_with_refs_eq]
  \\ fs[do_app_cases,empty_state_with_ffi_elim]
  \\ metis_tac[do_eq_succeeds,APPEND_ASSOC]);

(* booleans *)

val Eval_Or = store_thm("Eval_Or",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (Log Or x1 x2) (BOOL (b1 \/ b2))``,
  rw[Eval_def,BOOL_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ Cases_on `b1` \\ fs []
  THEN1 ( metis_tac[EVAL``do_log Or (Boolv T) x``,EVAL``Boolv T``] )
  \\ metis_tac[EVAL``do_log Or (Boolv F) x``,APPEND_ASSOC]);

val Eval_And = store_thm("Eval_And",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (Log And x1 x2) (BOOL (b1 /\ b2))``,
  rw[Eval_def,BOOL_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ Cases_on `b1` \\ fs []
  THEN1 ( metis_tac[EVAL``do_log And (Boolv T) x``,APPEND_ASSOC] )
  \\ metis_tac[EVAL``do_log And (Boolv F) x``,EVAL``Boolv F``]);

val Eval_If = store_thm("Eval_If",
  ``(a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> Eval env x2 (a b2)) /\
    (a3 ==> Eval env x3 (a b3)) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     Eval env (If x1 x2 x3) (a (if b1 then b2 else b3)))``,
  rw[Eval_def,BOOL_def,CONTAINER_def] \\ fs[]
  \\ rw[Once evaluate_cases]
  \\ metis_tac[EVAL``do_if (Boolv T) x y``,EVAL``do_if (Boolv F) x y``,APPEND_ASSOC]);

val Eval_Bool_Not = store_thm("Eval_Bool_Not",
  ``Eval env x1 (BOOL b1) ==>
    Eval env (App Equality
      [x1; App (Opb Lt) [Lit (IntLit 0); Lit (IntLit 0)]]) (BOOL (~b1))``,
  rw[Eval_def,BOOL_def]
  \\ rw[Once evaluate_cases,empty_state_with_refs_eq,PULL_EXISTS]
  \\ ntac 8 (rw[Once evaluate_cases,PULL_EXISTS])
  \\ rw[do_app_cases,PULL_EXISTS,opb_lookup_def]
  \\ rw[Once(CONJUNCT2 evaluate_cases),empty_state_with_ffi_elim]
  \\ Cases_on`b1`
  \\ metis_tac[EVAL``do_eq (Boolv T) (Boolv F)``,EVAL``do_eq (Boolv F) (Boolv F)``]);

val Eval_Implies = store_thm("Eval_Implies",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (If x1 x2 (App (Opb Leq) [Lit (IntLit 0); Lit (IntLit 0)]))
      (BOOL (b1 ==> b2))``,
  REPEAT STRIP_TAC
  \\ PURE_REWRITE_TAC [METIS_PROVE [] ``(b1 ==> b2) <=> (if b1 then b2 else T)``]
  \\ MATCH_MP_TAC (MP_CANON Eval_If |> GEN_ALL)
  \\ REPEAT (Q.EXISTS_TAC `T`) \\ fs [Eval_Val_BOOL_T]);

(* misc *)

val Eval_Var_SIMP = store_thm("Eval_Var_SIMP",
  ``Eval (write x v env) (Var (Short y)) p =
      if x = y then p v else Eval env (Var (Short y)) p``,
  ASM_SIMP_TAC (srw_ss()) [LOOKUP_VAR_def,lookup_var_id_def,write_def,
       lookup_var_def,Eval_def,Once evaluate_cases,lookup_var_id_def]
  \\ SRW_TAC [] [] \\ SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,
       lookup_var_id_def,state_component_equality]);

val Eval_Eq = store_thm("Eval_Eq",
  ``Eval env exp (a x) ==> Eval env exp ((Eq a x) x)``,
  SIMP_TAC std_ss [Eval_def,Eq_def]);

val FUN_FORALL = new_binder_definition("FUN_FORALL",
  ``($FUN_FORALL) = \(abs:'a->'b->v->bool) a v. !y. abs y a v``);

val FUN_EXISTS = new_binder_definition("FUN_EXISTS",
  ``($FUN_EXISTS) = \(abs:'a->'b->v->bool) a v. ?y. abs y a v``);

val FUN_FORALL_INTRO = store_thm("FUN_FORALL_INTRO",
  ``(!x. p x f v) ==> (FUN_FORALL x. p x) f v``,
  fs [FUN_FORALL]);

val Eval_FUN_FORALL = store_thm("Eval_FUN_FORALL",
  ``(!x. Eval env exp ((p x) f)) ==>
    Eval env exp ((FUN_FORALL x. p x) f)``,
  rw[Eval_def,FUN_FORALL]
  \\ METIS_TAC[evaluate_11_Rval]);

val Eval_FUN_FORALL_EQ = store_thm("Eval_FUN_FORALL_EQ",
  ``(!x. Eval env exp ((p x) f)) =
    Eval env exp ((FUN_FORALL x. p x) f)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ FULL_SIMP_TAC std_ss [Eval_FUN_FORALL]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [FUN_FORALL] \\ METIS_TAC []);

val FUN_FORALL_PUSH1 = prove(
  ``(FUN_FORALL x. a --> (b x)) = (a --> FUN_FORALL x. b x)``,
  rw[Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL]
  \\ METIS_TAC[evaluate_11_Rval,PAIR_EQ,result_11,SOME_11]) |> GEN_ALL;

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
      (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) ==>
      (!v. a n v ==>
           Eval (write name v (write_rec funs env2 env2)) body (b (f n))) ==>
      LOOKUP_VAR fname env (Recclosure env2 funs fname) ==>
      (find_recfun fname funs = SOME (name,body)) ==>
      Eval env (Var (Short fname)) ((Eq a n --> b) f)``,
  rw[write_rec_thm,write_def]
  \\ IMP_RES_TAC LOOKUP_VAR_THM
  \\ fs[Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC
  \\ rw[Once evaluate_cases,state_component_equality]
  \\ rw[Once evaluate_cases,state_component_equality]
  \\ rw[AppReturns_def,Eq_def,do_opapp_def,PULL_EXISTS]
  \\ fs[build_rec_env_def,FOLDR]
  \\ METIS_TAC[APPEND_ASSOC]);

val Eval_Recclosure = store_thm("Eval_Recclosure",
  ``(!v. a n v ==>
         Eval (write name v (write_rec [(fname,name,body)] env2 env2))
              body (b (f n))) ==>
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
  ASM_SIMP_TAC std_ss [Eval_Var_SIMP,Eval_def,LOOKUP_VAR_def,lookup_var_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,state_component_equality]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [lookup_var_id_def, LOOKUP_VAR_def]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC []);

val Eval_Eq_Fun = store_thm("Eval_Eq_Fun",
  ``Eval env (Fun v x) p ==>
    !env2. Eval env2 (Var name) ($= (Closure env v x)) ==>
           Eval env2 (Var name) p``,
  SIMP_TAC std_ss [Eval_Var_SIMP,Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases,state_component_equality]);

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
        Eval env (App (Opn f) [x1;x2]) (INT (opn_lookup f n1 n2))``,
  rw[Eval_def,INT_def,PRECONDITION_def]
  \\ rw[Once evaluate_cases,empty_state_with_refs_eq,PULL_EXISTS]
  \\ ntac 3 (rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS])
  \\ rw[do_app_cases,PULL_EXISTS]
  \\ METIS_TAC[empty_state_with_ffi_elim,APPEND_ASSOC]);

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
        Eval env (App (Opb f) [x1;x2]) (BOOL (opb_lookup f n1 n2))``,
  rw[Eval_def,INT_def,BOOL_def]
  \\ rw[Once evaluate_cases,empty_state_with_refs_eq,PULL_EXISTS]
  \\ ntac 3 (rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS])
  \\ rw[do_app_cases,PULL_EXISTS]
  \\ METIS_TAC[empty_state_with_ffi_elim,APPEND_ASSOC]);

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

local

val th0 = Q.SPEC `0` Eval_Val_INT
val th_sub = MATCH_MP (MATCH_MP Eval_INT_SUB (Q.SPEC `0` Eval_Val_INT))
            (ASSUME ``Eval env (Var (Short "k")) (INT k)``)
val th1 = ASSUME ``Eval env (Var (Short "k")) (INT k)``
val th2 = Eval_INT_LESS  |> Q.SPECL [`k`,`0`]
          |> (fn th => MATCH_MP th th1) |> (fn th => MATCH_MP th th0)
val th = MATCH_MP Eval_If (LIST_CONJ (map (DISCH T) [th2,th_sub,th1]))
         |> REWRITE_RULE [CONTAINER_def]
val code =
  ``Let (SOME "k") x1
       (If (App (Opb Lt) [Var (Short "k"); Lit (IntLit 0)])
          (App (Opn Minus) [Lit (IntLit 0); Var (Short "k")])
          (Var (Short "k")))``

in

val Eval_Num_ABS = store_thm("Eval_Num_ABS",
  ``Eval env x1 (INT i) ==>
    Eval env ^code (NUM (Num (ABS i)))``,
  SIMP_TAC std_ss [NUM_def]
  \\ `&(Num (ABS i)) = let k = i in if k < 0 then 0 - k else k` by
    (FULL_SIMP_TAC std_ss [LET_DEF] THEN intLib.COOPER_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL Eval_Let)
  \\ Q.EXISTS_TAC `INT` \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL (DISCH_ALL th))
  \\ FULL_SIMP_TAC std_ss [Eval_Var_SIMP]);

end;

val Eval_int_of_num = store_thm("Eval_int_of_num",
  ``Eval env x1 (NUM n) ==>
    Eval env x1 (INT (int_of_num n))``,
  SIMP_TAC std_ss [NUM_def]);

val Eval_int_of_num_o = store_thm("Eval_int_of_num_o",
  ``Eval env x1 ((A --> NUM) f) ==>
    Eval env x1 ((A --> INT) (int_of_num o f))``,
  SIMP_TAC std_ss [NUM_def,Arrow_def]);

val Eval_o_int_of_num = store_thm("Eval_o_int_of_num",
  ``Eval env x1 ((INT --> A) f) ==>
    Eval env x1 ((NUM --> A) (f o int_of_num))``,
  SIMP_TAC std_ss [NUM_def,Arrow_def,Eval_def]
  \\ METIS_TAC[]);

val Eval_int_negate = store_thm("Eval_int_negate",
  ``Eval env x1 (INT i) ==>
    Eval env (App (Opn Minus) [Lit (IntLit 0); x1]) (INT (-i))``,
  rw[Eval_def] >> rw[Once evaluate_cases] >>
  rw[empty_state_with_refs_eq,PULL_EXISTS] >>
  rpt(CHANGED_TAC(rw[Once(CONJUNCT2 evaluate_cases)])) >>
  rw[PULL_EXISTS] >>
  rw[Q.SPECL[`F`,`x`,`y`,`Lit l`](CONJUNCT1 evaluate_cases)] >>
  rw[do_app_cases,PULL_EXISTS,opn_lookup_def,empty_state_with_ffi_elim] >>
  fs[INT_def])

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
  ``Let (SOME "k") (App (Opn Minus) [x1; x2])
      (If (App (Opb Lt) [Var (Short "k"); Lit (IntLit 0)])
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
        Eval env (App (Opb Leq) [x; Lit (IntLit 0)]) (BOOL (n = 0))``,
  REPEAT STRIP_TAC \\ ASSUME_TAC (Q.SPEC `0` Eval_Val_NUM)
  \\ FULL_SIMP_TAC std_ss [NUM_def]
  \\ `(n = 0) = (&n <= 0)` by intLib.COOPER_TAC
  \\ FULL_SIMP_TAC std_ss [Eval_INT_LESS_EQ]);


(* word operations *)

val tac =
  qmatch_goalsub_abbrev_tac`Opw wx`
  \\ rw[Eval_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs[]
  \\ first_x_assum(qspec_then`refs++refs'`strip_assume_tac)
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ fs[] \\ asm_exists_tac
  \\ fs[WORD_def,Abbr`wx`]
  \\ fs [do_app_def,opw8_lookup_def,opw64_lookup_def]
  \\ rw[] \\ fs [GSYM WORD_w2w_OVER_BITWISE]

val Eval_word_and = store_thm("Eval_word_and",
  ``Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Andw) [x1;x2])
      (WORD (word_and w1 w2))``,
  tac);

val Eval_word_or = store_thm("Eval_word_or",
  ``Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Orw) [x1;x2])
      (WORD (word_or w1 w2))``,
  tac);

val Eval_word_xor = store_thm("Eval_word_xor",
  ``Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Xor) [x1;x2])
      (WORD (word_xor w1 w2))``,
  tac);

val DISTRIB_ANY = prove(
  ``(p * m + p * n = p * (m + n)) /\
    (p * m + n * p = p * (m + n)) /\
    (m * p + p * n = p * (m + n)) /\
    (m * p + n * p = p * (m + n:num)) /\
    (p * m - p * n = p * (m - n)) /\
    (p * m - n * p = p * (m - n)) /\
    (m * p - p * n = p * (m - n)) /\
    (m * p - n * p = p * (m - n:num))``,
  fs [LEFT_ADD_DISTRIB]);

val MOD_COMMON_FACTOR_ANY = prove(
  ``!n p q. 0 < n ∧ 0 < q ==>
            ((n * p) MOD (n * q) = n * p MOD q) /\
            ((p * n) MOD (n * q) = n * p MOD q) /\
            ((n * p) MOD (q * n) = n * p MOD q) /\
            ((p * n) MOD (q * n) = n * p MOD q)``,
  fs [GSYM MOD_COMMON_FACTOR]);

val Eval_word_add_lemma = prove(
  ``dimindex (:'a) <= k ==>
    (2 ** (k − dimindex (:α)) * q MOD dimword (:α)) MOD 2 ** k =
    (2 ** (k − dimindex (:α)) * q) MOD 2 ** k``,
  rw [] \\ fs [LESS_EQ_EXISTS]
  \\ rw [EXP_ADD,dimword_def,MOD_COMMON_FACTOR_ANY]);

val Eval_word_add = store_thm("Eval_word_add",
  ``Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Add) [x1;x2])
      (WORD (word_add w1 w2))``,
  tac
  \\ Cases_on `w1` \\ Cases_on `w2`
  \\ fs [word_add_n2w,w2w_def,WORD_MUL_LSL,word_mul_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ imp_res_tac Eval_word_add_lemma \\ fs []);

val Eval_word_sub_lemma = prove(
  ``dimindex (:'a) <= k /\ n' < dimword (:α) ==>
    (n * 2 ** (k − dimindex (:α)) +
      (2 ** k − (n' * 2 ** (k − dimindex (:α))) MOD 2 ** k) MOD 2 ** k) MOD 2 ** k =
    ((n + dimword (:α) − n') * 2 ** (k − dimindex (:α))) MOD 2 ** k``,
  fs [LESS_EQ_EXISTS,dimword_def] \\ rw []
  \\ fs [RIGHT_ADD_DISTRIB,RIGHT_SUB_DISTRIB,EXP_ADD]
  \\ full_simp_tac std_ss [DISTRIB_ANY,MOD_COMMON_FACTOR_ANY] \\ AP_TERM_TAC
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [Once (GSYM MOD_PLUS)]
  \\ `n + 2 ** dimindex (:α) − n' = n + (2 ** dimindex (:α) − n')` by decide_tac
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [Once (GSYM MOD_PLUS)]);

val Eval_word_sub = store_thm("Eval_word_sub",
  ``Eval env x1 (WORD (w1:'a word)) /\
    Eval env x2 (WORD (w2:'a word)) ==>
    Eval env (App (Opw (if dimindex (:'a) <= 8 then W8 else W64) Sub) [x1;x2])
      (WORD (word_sub w1 w2))``,
  tac
  \\ Cases_on `w1` \\ Cases_on `w2`
  \\ fs [word_add_n2w,w2w_def,WORD_MUL_LSL,word_mul_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ once_rewrite_tac [WORD_ADD_COMM]
  \\ fs [GSYM (SIMP_CONV (srw_ss()) [word_sub_def] ``w-v:'a word``)]
  \\ fs [word_add_n2w,w2w_def,WORD_MUL_LSL,word_mul_n2w,GSYM RIGHT_ADD_DISTRIB]
  \\ imp_res_tac Eval_word_add_lemma
  \\ fs [word_2comp_n2w,word_add_n2w]
  \\ imp_res_tac Eval_word_sub_lemma \\ fs []);

val w2n_w2w_8 = prove(
  ``dimindex (:α) < 8 ==>
    w2n ((w2w:'a word ->word8) w << (8 − dimindex (:α)) >>>
            (8 − dimindex (:α))) = w2n w``,
  Cases_on `w` \\ fs [w2n_lsr,w2w_def,WORD_MUL_LSL,word_mul_n2w,dimword_def]
  \\ rw []  \\ drule (DECIDE ``n<m ==> n <= m:num``)
  \\ fs [LESS_EQ_EXISTS] \\ fs [] \\ rw []
  \\ fs [] \\ full_simp_tac bool_ss [GSYM (EVAL ``2n ** 8``),EXP_ADD]
  \\ fs [MOD_COMMON_FACTOR_ANY,MULT_DIV]);

val w2n_w2w_64 = prove(
  ``dimindex (:α) < 64 ==>
    w2n ((w2w:'a word ->word64) w << (64 − dimindex (:α)) >>>
            (64 − dimindex (:α))) = w2n w``,
  Cases_on `w` \\ fs [w2n_lsr,w2w_def,WORD_MUL_LSL,word_mul_n2w,dimword_def]
  \\ rw []  \\ drule (DECIDE ``n<m ==> n <= m:num``)
  \\ fs [LESS_EQ_EXISTS] \\ fs [] \\ rw []
  \\ fs [] \\ full_simp_tac bool_ss [GSYM (EVAL ``2n ** 64``),EXP_ADD]
  \\ fs [MOD_COMMON_FACTOR_ANY,MULT_DIV]);

val Eval_w2n = store_thm("Eval_w2n",
  ``Eval env x1 (WORD (w:'a word)) ==>
    Eval env
      (if dimindex (:'a) = 8 then
         App (WordToInt W8) [x1]
       else if dimindex (:'a) = 64 then
         App (WordToInt W64) [x1]
       else if dimindex (:'a) < 8 then
         App (WordToInt W8) [App (Shift W8 Lsr (8 - dimindex (:'a))) [x1]]
       else
         App (WordToInt W64) [App (Shift W64 Lsr (64 - dimindex (:'a))) [x1]])
      (NUM (w2n w))``,
  rw[Eval_def,WORD_def] \\ fs []
  \\ TRY (* takes care of = 8 and = 64 cases *)
   (rw[Once evaluate_cases,PULL_EXISTS]
    \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
    \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
    \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
    \\ first_x_assum(qspec_then`refs`strip_assume_tac)
    \\ asm_exists_tac \\ fs[]
    \\ fs [do_app_def,NUM_def,INT_def,w2w_def]
    \\ assume_tac w2n_lt \\ rfs [dimword_def])
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [do_app_def]
  \\ EVAL_TAC \\ fs [w2n_w2w_64,w2n_w2w_8]);

val Eval_n2w = store_thm("Eval_n2w",
  ``dimindex (:'a) <= 64 ==>
    Eval env x1 (NUM n) ==>
    Eval env
      (if dimindex (:'a) = 8 then
         App (WordFromInt W8) [x1]
       else if dimindex (:'a) = 64 then
         App (WordFromInt W64) [x1]
       else if dimindex (:'a) < 8 then
         App (Shift W8 Lsl (8 - dimindex (:'a))) [App (WordFromInt W8) [x1]]
       else
         App (Shift W64 Lsl (64 - dimindex (:'a))) [App (WordFromInt W64) [x1]])
      (WORD ((n2w n):'a word))``,
  rw[Eval_def,WORD_def] \\ fs [] \\ rfs []
  \\ TRY (* takes care of = 8 and = 64 cases *)
   (rw[Once evaluate_cases,PULL_EXISTS]
    \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
    \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
    \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
    \\ first_x_assum(qspec_then`refs`strip_assume_tac)
    \\ asm_exists_tac \\ fs[]
    \\ fs [do_app_def,NUM_def,INT_def,w2w_def,integer_wordTheory.i2w_def]
    \\ fs [dimword_def] \\ NO_TAC)
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [do_app_def,NUM_def,INT_def]
  \\ fs [shift8_lookup_def,shift64_lookup_def,
         w2w_def,integer_wordTheory.i2w_def,WORD_MUL_LSL,word_mul_n2w]
  \\ rw [dimword_def] \\ TRY (drule (DECIDE ``n<m ==> n <= m:num``))
  \\ fs [LESS_EQ_EXISTS] \\ fs [] \\ rw [] \\ fs []
  \\ full_simp_tac bool_ss
       [GSYM (EVAL ``2n ** 8``),GSYM (EVAL ``2n ** 64``),EXP_ADD]
  \\ fs [MOD_COMMON_FACTOR_ANY,MULT_DIV]);

val Eval_word_lsl = store_thm("Eval_word_lsl",
  ``!n.
      Eval env x1 (WORD (w1:'a word)) ==>
      Eval env (App (Shift (if dimindex (:'a) <= 8 then W8 else W64) Lsl n) [x1])
        (WORD (word_lsl w1 n))``,
  rw[Eval_def,WORD_def]
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs[]
  \\ fs [LESS_EQ_EXISTS]
  \\ fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_lsl_def,fcpTheory.FCP_BETA,w2w] \\ rw []
  \\ Cases_on `w1 ' (i − (n + p))` \\ fs []);

val Eval_word_lsr = store_thm("Eval_word_lsr",
  ``!n.
      Eval env x1 (WORD (w1:'a word)) ==>
      Eval env (let w = (if dimindex (:'a) <= 8 then W8 else W64) in
                let k = (if dimindex (:'a) <= 8 then 8 else 64) - dimindex(:'a) in
                  if dimindex (:'a) = 8 \/ dimindex (:'a) = 64 then
                    App (Shift w Lsr n) [x1]
                  else
                    App (Shift w Lsl k) [App (Shift w Lsr (n+k)) [x1]])
        (WORD (word_lsr w1 n))``,
  rw[Eval_def,WORD_def]
  \\ TRY (* takes care of = 8 and = 64 cases *)
   (rw[Once evaluate_cases,PULL_EXISTS]
    \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
    \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
    \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
    \\ first_x_assum(qspec_then`refs`strip_assume_tac)
    \\ asm_exists_tac \\ fs[]
    \\ fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
    \\ fs [fcpTheory.CART_EQ,word_lsr_def,fcpTheory.FCP_BETA,w2w] \\ rw []
    \\ eq_tac \\ rfs [w2w] \\ rw [] \\ rfs [w2w] \\ NO_TAC)
  \\ fs []
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs[]
  \\ fs [LESS_EQ_EXISTS,do_app_def]
  \\ fs [shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_lsr_def,word_lsl_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [fcpTheory.FCP_BETA,w2w]
  \\ imp_res_tac (DECIDE  ``p <= i ==> (i - p + n = (i + n) - p:num)``) \\ fs []
  \\ TRY (`i − p + (n + p) < 8` by decide_tac \\ fs [fcpTheory.FCP_BETA,w2w])
  \\ TRY (`i − p + (n + p) < 64` by decide_tac \\ fs [fcpTheory.FCP_BETA,w2w]));

val Eval_word_asr = store_thm("Eval_word_asr",
  ``!n.
      Eval env x1 (WORD (w1:'a word)) ==>
      Eval env (let w = (if dimindex (:'a) <= 8 then W8 else W64) in
                let k = (if dimindex (:'a) <= 8 then 8 else 64) - dimindex(:'a) in
                  if dimindex (:'a) = 8 \/ dimindex (:'a) = 64 then
                    App (Shift w Asr n) [x1]
                  else
                    App (Shift w Lsl k) [App (Shift w Asr (n+k)) [x1]])
        (WORD (word_asr w1 n))``,
  rw[Eval_def,WORD_def]
  \\ TRY (* takes care of = 8 and = 64 cases *)
   (rw[Once evaluate_cases,PULL_EXISTS]
    \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
    \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
    \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
    \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
    \\ first_x_assum(qspec_then`refs`strip_assume_tac)
    \\ asm_exists_tac \\ fs []
    \\ fs [do_app_def,shift8_lookup_def,shift64_lookup_def]
    \\ fs [fcpTheory.CART_EQ,word_asr_def,fcpTheory.FCP_BETA,w2w] \\ rw []
    \\ fs [word_msb_def] \\ rfs [w2w] \\ rw [] \\ rfs [w2w] \\ NO_TAC)
  \\ fs []
  \\ rw[Once evaluate_cases,PULL_EXISTS]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS]
  \\ CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"]))
  \\ qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim]
  \\ first_x_assum(qspec_then`refs`strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [LESS_EQ_EXISTS,do_app_def]
  \\ fs [shift8_lookup_def,shift64_lookup_def]
  \\ fs [fcpTheory.CART_EQ,word_asr_def,word_lsl_def,fcpTheory.FCP_BETA,w2w]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ fs [fcpTheory.FCP_BETA,w2w,word_msb_def]
  \\ imp_res_tac (DECIDE ``8 = k ==> 7 = k - 1n``) \\ fs []
  \\ imp_res_tac (DECIDE ``64 = k ==> 63 = k - 1n``) \\ fs []);

(* list definition *)

val LIST_TYPE_def = Define `
  (!a x_2 x_1 v.
     LIST_TYPE a (x_2::x_1) v <=>
     ?v2_1 v2_2.
       v = Conv (SOME ("::",TypeId (Short "list"))) [v2_1; v2_2] /\
       a x_2 v2_1 /\ LIST_TYPE a x_1 v2_2) /\
  !a v.
     LIST_TYPE a [] v <=>
     v = Conv (SOME ("nil",TypeId (Short "list"))) []`

val LIST_TYPE_SIMP = prove(
  ``!xs b. CONTAINER LIST_TYPE
              (\x v. if b x \/ MEM x xs then p x v else ARB) xs =
           LIST_TYPE (p:('a -> v -> bool)) xs``,
  Induct THEN FULL_SIMP_TAC std_ss [FUN_EQ_THM,LIST_TYPE_def,MEM,
    DISJ_ASSOC,CONTAINER_def])
  |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss [] |> GSYM
  |> curry save_thm "LIST_TYPE_SIMP";

(* pair definition *)

val PAIR_TYPE_def = Define `
  !b c x_2 x_1 v.
    PAIR_TYPE b c (x_2:'b,x_1:'c) v <=>
    ?v1_1 v1_2. v = Conv NONE [v1_1; v1_2] /\ b x_2 v1_1 /\ c x_1 v1_2`;

val PAIR_TYPE_SIMP = prove(
  ``!x. CONTAINER PAIR_TYPE (\y v. if y = FST x then a y v else ARB)
                            (\y v. if y = SND x then b y v else ARB) x =
        PAIR_TYPE (a:('a -> v -> bool)) (b:('b -> v -> bool)) x``,
  Cases \\ SIMP_TAC std_ss [PAIR_TYPE_def,CONTAINER_def,FUN_EQ_THM])
  |> GSYM |> SPEC_ALL |> curry save_thm "PAIR_TYPE_SIMP";

(* option definition *)
(* TODO: Apparently, the variable names need to be of a specific form...*)
val OPTION_TYPE_def = Define `
  (!a x_2 v.
     OPTION_TYPE a (SOME x_2) v <=>
     ?v2_1.
       v = Conv (SOME ("SOME",TypeId (Short "option"))) [v2_1] /\
       a x_2 v2_1) /\
  !a v.
     OPTION_TYPE a NONE v <=>
     v = Conv (SOME ("NONE",TypeId (Short "option"))) []`

val OPTION_TYPE_SIMP = prove(
  ``!x. CONTAINER OPTION_TYPE
              (\y v. if x = SOME y then p y v else ARB) x =
           OPTION_TYPE (p:('a -> v -> bool)) x``,
  Cases>>FULL_SIMP_TAC std_ss [FUN_EQ_THM,OPTION_TYPE_def,DISJ_ASSOC,CONTAINER_def])
  |> Q.SPECL [`x`] |> SIMP_RULE std_ss [] |> GSYM
  |> curry save_thm "OPTION_TYPE_SIMP";

(* characters *)

val Eval_Ord = store_thm("Eval_Ord",
  ``Eval env x (CHAR c) ==>
    Eval env (App Ord [x]) (NUM (ORD c))``,
  rw[Eval_def] >>
  rw[Once evaluate_cases,empty_state_with_refs_eq,PULL_EXISTS] >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS] >>
  rw[do_app_cases,PULL_EXISTS,empty_state_with_ffi_elim] >>
  fs[CHAR_def,NUM_def,INT_def] >>
  metis_tac[ORD_11])

val Eval_Chr = store_thm("Eval_Chr",
  ``Eval env x (NUM n) ==>
    n < 256 ==>
    Eval env (App Chr [x]) (CHAR (CHR n))``,
  rw[Eval_def] >>
  rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq] >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  rw[Once (CONJUNCT2 evaluate_cases),PULL_EXISTS] >>
  CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"])) >>
  qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim] >>
  rw[do_app_cases,PULL_EXISTS] >>
  fs[CHAR_def,NUM_def,INT_def] >>
  first_x_assum(qspec_then`refs`strip_assume_tac) >>
  asm_exists_tac >> fs[] >>
  simp[integerTheory.INT_ABS_NUM] >>
  srw_tac[DNF_ss][] >>
  intLib.COOPER_TAC)

val Boolv_11 = store_thm("Boolv_11",
  ``(Boolv b1 = Boolv b2) <=> (b1 = b2)``,
  Cases_on `b1` \\ Cases_on `b2` \\ EVAL_TAC);

val tac =
  rw[Eval_def] >>
  rw[Once evaluate_cases,PULL_EXISTS,empty_state_with_refs_eq] >>
  CONV_TAC(RESORT_EXISTS_CONV(sort_vars["ffi"])) >>
  qexists_tac`empty_state.ffi` \\ simp[empty_state_with_ffi_elim] >>
  rpt(CHANGED_TAC(rw[Once(CONJUNCT2 evaluate_cases),PULL_EXISTS])) >>
  rw[do_app_cases,PULL_EXISTS] >> fs[CHAR_def] >>
  rw[BOOL_def,opb_lookup_def,Boolv_11]

val Eval_char_lt = store_thm("Eval_char_lt",
  ``!c1 c2.
        Eval env x1 (CHAR c1) ==>
        Eval env x2 (CHAR c2) ==>
        Eval env (App (Chopb Lt) [x1;x2]) (BOOL (c1 < c2))``,
  tac >> rw[stringTheory.char_lt_def] >>
  metis_tac[APPEND_ASSOC])

val Eval_char_le = store_thm("Eval_char_le",
  ``!c1 c2.
        Eval env x1 (CHAR c1) ==>
        Eval env x2 (CHAR c2) ==>
        Eval env (App (Chopb Leq) [x1;x2]) (BOOL (c1 ≤ c2))``,
  tac >> rw[stringTheory.char_le_def] >>
  metis_tac[APPEND_ASSOC])

val Eval_char_gt = store_thm("Eval_char_gt",
  ``!c1 c2.
        Eval env x1 (CHAR c1) ==>
        Eval env x2 (CHAR c2) ==>
        Eval env (App (Chopb Gt) [x1;x2]) (BOOL (c1 > c2))``,
  tac >> rw[stringTheory.char_gt_def,int_gt,GREATER_DEF] >>
  metis_tac[APPEND_ASSOC])

val Eval_char_ge = store_thm("Eval_char_ge",
  ``!c1 c2.
        Eval env x1 (CHAR c1) ==>
        Eval env x2 (CHAR c2) ==>
        Eval env (App (Chopb Geq) [x1;x2]) (BOOL (c1 ≥ c2))``,
  tac >> rw[stringTheory.char_ge_def,int_ge,GREATER_EQ]
  >> metis_tac[APPEND_ASSOC])

(* strings *)

val LIST_TYPE_CHAR_v_to_char_list = store_thm("LIST_TYPE_CHAR_v_to_char_list",
  ``∀l v. LIST_TYPE CHAR l v ⇒ v_to_char_list v = SOME l``,
  Induct >>
  simp[LIST_TYPE_def,v_to_char_list_def,PULL_EXISTS,CHAR_def])

val LIST_TYPE_CHAR_char_list_to_v = store_thm("LIST_TYPE_CHAR_char_list_to_v",
  ``∀l. LIST_TYPE CHAR l (char_list_to_v l)``,
  Induct >> simp[char_list_to_v_def,LIST_TYPE_def,CHAR_def])

val tac =
  rw[Eval_def] >>
  rw[Once evaluate_cases] >>
  empty_state_tac >>
  rw[state_component_equality] >>
  rw[Once evaluate_cases,PULL_EXISTS] >>
  fs[empty_state_def,ffiTheory.initial_ffi_state_def] >>
  first_assum(match_exists_tac o concl) >> rw[] >>
  rw[Once evaluate_cases] >>
  rw[do_app_cases,PULL_EXISTS] >>
  rw[state_component_equality]

val Eval_implode = store_thm("Eval_implode",
  ``!env x1 l.
      Eval env x1 (LIST_TYPE CHAR l) ==>
      Eval env (App Implode [x1]) (STRING_TYPE (implode l))``,
  tac >>
  rw[STRING_TYPE_def] >>
  imp_res_tac LIST_TYPE_CHAR_v_to_char_list >>
  simp[stringTheory.IMPLODE_EXPLODE_I,mlstringTheory.explode_implode])

val Eval_explode = store_thm("Eval_explode",
  ``!env x1 s.
      Eval env x1 (STRING_TYPE s) ==>
      Eval env (App Explode [x1]) (LIST_TYPE CHAR (explode s))``,
  tac >>
  fs[STRING_TYPE_def,stringTheory.IMPLODE_EXPLODE_I,
     LIST_TYPE_CHAR_char_list_to_v])

val Eval_strlen = store_thm("Eval_strlen",
  ``!env x1 s.
      Eval env x1 (STRING_TYPE s) ==>
      Eval env (App Strlen [x1]) (NUM (strlen s))``,
  tac >>
  fs[STRING_TYPE_def,NUM_def,INT_def,mlstringTheory.strlen_def])

(* vectors *)

val _ = Datatype `
  vector = Vector ('a list)`;

val fromList_def = Define `
  fromList l = Vector l`;

val sub_def = Define `
  sub (Vector l) n = EL n l`;

val length_def = Define `
  length (Vector l) = LENGTH l`;

val VECTOR_TYPE_def = Define `
  VECTOR_TYPE a (Vector l) v <=>
    ?l'. v = Vectorv l' /\ LENGTH l = LENGTH l' /\ LIST_REL a l l'`;

val Eval_sub = store_thm("Eval_sub",
 ``!env x1 x2 a n v.
     Eval env x1 (VECTOR_TYPE a v) ==>
     Eval env x2 (NUM n) ==>
     n < length v ==>
     Eval env (App Vsub [x1; x2]) (a (sub v n))``,
  rw [Eval_def] >>
  rw [Once evaluate_cases] >>
  empty_state_tac >>
  rw[state_component_equality] >>
  ntac 3 (rw [Once (hd (tl (CONJUNCTS evaluate_cases)))]) >>
  rw [do_app_cases] >>
  rw [PULL_EXISTS] >>
  `?l. v = Vector l` by metis_tac [fetch "-" "vector_nchotomy"] >>
  rw [] >>
  fs [VECTOR_TYPE_def, length_def, NUM_def, sub_def, INT_def] >>
  fs[empty_state_def,ffiTheory.initial_ffi_state_def] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  qexists_tac`EL n l'` >>
  fs [LIST_REL_EL_EQN] >> res_tac >> fs [INT_ABS_NUM,GSYM NOT_LESS] >>
  record_simp_failure_tac);

val Eval_vector = store_thm("Eval_vector",
 ``!env x1 a l.
     Eval env x1 (LIST_TYPE a l) ==>
     Eval env (App VfromList [x1]) (VECTOR_TYPE a (Vector l))``,
  rw [Eval_def] >>
  rw [Once evaluate_cases] >>
  empty_state_tac >>
  rw[state_component_equality] >>
  ntac 3 (rw [Once (hd (tl (CONJUNCTS evaluate_cases)))]) >>
  rw [do_app_cases] >>
  rw [PULL_EXISTS] >>
  fs [VECTOR_TYPE_def] >>
  empty_state_tac2 >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[GSYM PULL_EXISTS] >>
  conj_tac >- record_simp_failure_tac >>
  pop_assum mp_tac >>
  pop_assum (fn _ => all_tac) >>
  Q.SPEC_TAC (`res`, `res`) >>
  Induct_on `l` >>
  rw [] >>
  fs [LIST_TYPE_def, v_to_list_def, PULL_EXISTS] >>
  BasicProvers.FULL_CASE_TAC >>
  fs [] >>
  metis_tac [optionTheory.NOT_SOME_NONE, optionTheory.SOME_11]);

val Eval_length = store_thm("Eval_length",
  ``!env x1 x2 a n v.
      Eval env x1 (VECTOR_TYPE a v) ==>
      Eval env (App Vlength [x1]) (NUM (length v))``,
  rw [Eval_def] >>
  rw [Once evaluate_cases] >>
  empty_state_tac >>
  rw[state_component_equality] >>
  ntac 3 (rw [Once (hd (tl (CONJUNCTS evaluate_cases)))]) >>
  rw [do_app_cases] >>
  rw [PULL_EXISTS] >>
  `?l. v = Vector l` by metis_tac [fetch "-" "vector_nchotomy"] >>
  rw [] >>
  empty_state_tac2 >>
  fs [VECTOR_TYPE_def, length_def, NUM_def, INT_def] >>
  rveq >> asm_exists_tac >>
  conj_tac >- record_simp_failure_tac >>
  metis_tac []);

(* evaluate lemmas *)

val _ = temp_overload_on("has_emp",``\x. (FST x).refs = empty_store``)

val s = ``s:'ffi state``

val evaluate_empty_store_lemma = prove(
 ``(!ck env s e r1.
      evaluate ck env ^s e r1 ==> has_emp r1 ==> (s.refs = empty_store)) /\
   (!ck env s es r1.
      evaluate_list ck env ^s es r1 ==> has_emp r1 ==> (s.refs = empty_store)) /\
   (!ck env s v pes errv r1.
      evaluate_match ck env ^s v pes errv r1 ==> has_emp r1 ==> (s.refs = empty_store))``,
  HO_MATCH_MP_TAC evaluate_ind \\ rw [] \\ POP_ASSUM MP_TAC
  \\ TRY (Cases_on `op`)
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_cases,LET_DEF,store_alloc_def]
  THEN1 (Cases_on `s2`
    \\ FULL_SIMP_TAC (srw_ss()) [store_assign_def, store_alloc_def,empty_store_def,APPEND]
    \\ Cases_on `lnum`
    \\ fs [LUPDATE_def])
  THEN1 (Cases_on `s2`
    \\ FULL_SIMP_TAC (srw_ss()) [store_alloc_def,empty_store_def,APPEND])
  THEN1 (Cases_on `s2`
    \\ FULL_SIMP_TAC (srw_ss()) [store_assign_def, store_alloc_def,empty_store_def,APPEND]
    \\ Cases_on `lnum`
    \\ fs [LUPDATE_def])
  \\ FULL_SIMP_TAC std_ss [IMP_DISJ_THM]
  \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [store_assign_def,empty_store_def,LUPDATE_NIL]
  \\ FULL_SIMP_TAC list_ss [])
  |> SIMP_RULE std_ss [PULL_EXISTS,AND_IMP_INTRO];

val _ = temp_overload_on("has_emp_no_fail",
  ``\x. ((FST x).refs = empty_store) /\
        ~(SND x = (Rerr (Rabort Rtype_error)):('b,'c) result)``)

val evaluate_no_clock = prove(
 ``(!ck env ^s e r1.
      evaluate ck env s e r1 ==> ~ck ==> (s.clock = (FST r1).clock)) /\
   (!ck env ^s es r1.
      evaluate_list ck env s es r1 ==> ~ck ==> (s.clock = (FST r1).clock))  /\
   (!ck env ^s v pes errv r1.
      evaluate_match ck env s v pes errv r1 ==>  ~ck ==> (s.clock = (FST r1).clock))``,
  HO_MATCH_MP_TAC evaluate_ind \\ rw [])
  |> SIMP_RULE std_ss [PULL_EXISTS,AND_IMP_INTRO];

val evaluate_constant_clock = store_thm("evaluate_constant_clock",
  ``evaluate F env s1 exp (s2,res) <=>
    evaluate F env s1 exp (s2,res) /\ (s1.clock = s2.clock)``,
  EQ_TAC \\ rpt strip_tac \\ fs []
  \\ imp_res_tac evaluate_no_clock \\ fs []);

val sind = IndDefLib.derive_strong_induction(evaluate_rules,evaluate_ind);

val do_app_empty_store = prove(
  ``!op vs.
      FST s3 <> empty_store ==>
      ~(do_app s3 op vs = SOME ((empty_store,io),e''))``,
  Cases_on`s3`>>
  SIMP_TAC std_ss [do_app_cases] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [store_alloc_def, store_assign_def, LET_THM]
  \\ FULL_SIMP_TAC std_ss [LENGTH_LUPDATE,empty_store_def,GSYM LENGTH_NIL,
                           store_alloc_def, store_lookup_def]
  \\ Cases_on`q`>>fs[]
  \\ spose_not_then strip_assume_tac >> rw[] >>
  Cases_on`v10`>>fs[] >> rw[] >> rfs[] >>
  intLib.COOPER_TAC);

val do_app_lemma = prove(
  ``!op.
      (do_app (empty_store,io1) op vs = SOME ((empty_store,(io:'ffi ffi_state)),e'')) ==>
      !t. do_app (t:('ffi,v)store_ffi) op vs = SOME (t,e'')``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [do_app_def] \\ REPEAT STRIP_TAC
  \\ Cases_on`t` \\ fs[do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [store_assign_def]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (srw_ss()) [empty_store_def, LET_THM, store_lookup_def,
                               store_alloc_def]
  \\ rw []);

val do_app_lemma_gen = prove(
  ``!op.
      (do_app (empty_store,io1) op vs = SOME ((empty_store,(io:unit ffi_state)),e'')) ==>
      !t. do_app (t:('ffi,v)store_ffi) op vs = SOME (t,e'')``,
  Cases \\ FULL_SIMP_TAC (srw_ss()) [do_app_def] \\ REPEAT STRIP_TAC
  \\ Cases_on`t` \\ fs[do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [store_assign_def]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ TRY (Cases_on `l` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ FULL_SIMP_TAC (srw_ss()) [empty_store_def, LET_THM, store_lookup_def,
                               store_alloc_def]
  \\ rw []);

val pmatch_empty_store = store_thm("pmatch_empty_store",
  ``(!cenv (s:v store) (p:pat) v env x.
      (pmatch cenv empty_store p v env = x) /\ x <> Match_type_error ==>
      !s. (pmatch cenv s p v env = x)) /\
    (!cenv (s:v store) (p:pat list) vs env x.
      (pmatch_list cenv empty_store p vs env = x) /\ x <> Match_type_error ==>
      !s. (pmatch_list cenv s p vs env = x))``,
  HO_MATCH_MP_TAC pmatch_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [pmatch_def]
  \\ FULL_SIMP_TAC std_ss [store_lookup_def,empty_store_def,LENGTH]
  THEN1 (BasicProvers.EVERY_CASE_TAC \\ rw [])
  THEN1 (METIS_TAC [])
  \\ Cases_on `pmatch cenv [] p v env`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_X_ASSUM `No_match = x` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) []);

val s0 = ``s:unit state``
val t = ``t:'ffi state``

val evaluate_empty_store_IMP_any_store = prove(
 ``(!ck env ^s0 e r1.
      evaluate ck env s e r1 ==> (ck = F) /\ has_emp_no_fail r1 ==>
      !^t. evaluate ck env t e (t,SND r1)) /\
   (!ck env ^s0 es r1.
      evaluate_list ck env s es r1 ==> (ck = F) /\ has_emp_no_fail r1 ==>
      !^t. evaluate_list ck env t es (t,SND r1)) /\
   (!ck env ^s0 v pes errv r1.
      evaluate_match ck env s v pes errv r1 ==> (ck = F) /\ has_emp_no_fail r1 ==>
      !^t. evaluate_match ck env t v pes errv (t,SND r1))``,
  HO_MATCH_MP_TAC sind \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1
   (Cases_on `r1`
    \\ `s'.refs = empty_store` by IMP_RES_TAC evaluate_empty_store_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1
   METIS_TAC []
  THEN1
   (Cases_on `r1`
    \\ rw []
    \\ fs []
    \\ `s2.refs = empty_store` by (IMP_RES_TAC evaluate_empty_store_lemma \\ fs [])
    \\ rw []
    \\ `s.refs = empty_store` by (IMP_RES_TAC evaluate_empty_store_lemma \\ fs [])
    \\ METIS_TAC [pair_CASES, FST, SND])
  THEN1
   (`s2.refs = empty_store` by METIS_TAC [do_app_empty_store,FST] \\ fs []
    \\ imp_res_tac do_app_lemma_gen \\ fs[] \\ rw[]
    \\ disj1_tac
    \\ Q.LIST_EXISTS_TAC[`vs`,`t`]
    \\ simp[]
    \\ simp[state_component_equality])
  THEN1
   (`s'.refs = empty_store` by
      (IMP_RES_TAC evaluate_empty_store_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma_gen
    \\ METIS_TAC [pair_CASES, FST, SND])
  THEN1
   (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma_gen
    \\ METIS_TAC [pair_CASES, FST, SND, Boolv_11])
  THEN1
   (`s'.refs = empty_store` by
      (IMP_RES_TAC evaluate_empty_store_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ fs [do_if_def]
    \\ Cases_on `v = Boolv T` \\ fs []
    \\ Cases_on `v = Boolv F` \\ fs [Boolv_11]
    \\ METIS_TAC [pair_CASES, FST, SND, Boolv_11])
  \\ TRY
   (`s'.refs = empty_store` by
      (IMP_RES_TAC evaluate_empty_store_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma
    \\ METIS_TAC [pair_CASES, FST, SND])
  \\ Cases_on `r1` \\ fs []
  \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] []
  \\ IMP_RES_TAC evaluate_empty_store_lemma \\ fs []
  \\ IMP_RES_TAC pmatch_empty_store \\ fs []);

val evaluate_empty_state_IMP = Q.store_thm("evaluate_empty_state_IMP",
  `evaluate F env empty_state exp (empty_state,Rval x) ⇒
   ∀(s:'ffi state). evaluate F env s exp (s,Rval x)`,
  strip_tac \\ imp_res_tac evaluate_empty_store_IMP_any_store \\ fs []
  \\ pop_assum match_mp_tac \\ EVAL_TAC);

val evaluate_empty_store_IMP_any_store = prove(
 ``(!ck env ^s e r1.
      evaluate ck env s e r1 ==> (ck = F) /\ has_emp_no_fail r1 ==>
      !^t. evaluate ck env t e (t,SND r1)) /\
   (!ck env ^s es r1.
      evaluate_list ck env s es r1 ==> (ck = F) /\ has_emp_no_fail r1 ==>
      !^t. evaluate_list ck env t es (t,SND r1)) /\
   (!ck env ^s v pes errv r1.
      evaluate_match ck env s v pes errv r1 ==> (ck = F) /\ has_emp_no_fail r1 ==>
      !^t. evaluate_match ck env t v pes errv (t,SND r1))``,
  HO_MATCH_MP_TAC sind \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1
   (Cases_on `r1`
    \\ `s'.refs = empty_store` by IMP_RES_TAC evaluate_empty_store_lemma
    \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1
   METIS_TAC []
  THEN1
   (Cases_on `r1`
    \\ rw []
    \\ fs []
    \\ `s2.refs = empty_store` by (IMP_RES_TAC evaluate_empty_store_lemma \\ fs [])
    \\ rw []
    \\ `s.refs = empty_store` by (IMP_RES_TAC evaluate_empty_store_lemma \\ fs [])
    \\ METIS_TAC [pair_CASES, FST, SND])
  THEN1
   (`s2.refs = empty_store` by METIS_TAC [do_app_empty_store,FST] \\ fs []
    \\ imp_res_tac do_app_lemma \\ fs[] \\ rw[]
    \\ disj1_tac
    \\ Q.LIST_EXISTS_TAC[`vs`,`t`]
    \\ simp[]
    \\ simp[state_component_equality])
  THEN1
   (`s'.refs = empty_store` by
      (IMP_RES_TAC evaluate_empty_store_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma
    \\ METIS_TAC [pair_CASES, FST, SND])
  THEN1
   (FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma
    \\ METIS_TAC [pair_CASES, FST, SND, Boolv_11])
  THEN1
   (`s'.refs = empty_store` by
      (IMP_RES_TAC evaluate_empty_store_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ fs [do_if_def]
    \\ Cases_on `v = Boolv T` \\ fs []
    \\ Cases_on `v = Boolv F` \\ fs [Boolv_11]
    \\ METIS_TAC [pair_CASES, FST, SND, Boolv_11])
  \\ TRY
   (`s'.refs = empty_store` by
      (IMP_RES_TAC evaluate_empty_store_lemma \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC do_app_lemma
    \\ METIS_TAC [pair_CASES, FST, SND])
  \\ Cases_on `r1` \\ fs []
  \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] []
  \\ IMP_RES_TAC evaluate_empty_store_lemma \\ fs []
  \\ IMP_RES_TAC pmatch_empty_store \\ fs []);

val evaluate_empty_state_IMP = prove(
  ``evaluate F env empty_state exp (empty_state,Rval x) ⇒
    ∀(s:unit state). evaluate F env s exp (s,Rval x)``,
  rw[] >> imp_res_tac evaluate_empty_store_IMP_any_store >> fs[empty_state_def])

(* a few misc. lemmas that help the automation *)

val IMP_PreImp = store_thm("IMP_PreImp",
  ``!b1 b2 b3. (b1 /\ b2 ==> b3) ==> b1 ==> PreImp b2 b3``,
  REPEAT Cases \\ EVAL_TAC);

val evaluate_list_SIMP = store_thm("evaluate_list_SIMP",
  ``(evaluate_list F env empty_state [] (empty_state,Rval ([])) = T) /\
    (evaluate_list F env empty_state (x::xs) (empty_state,Rval ((y::ys))) <=>
     evaluate F env empty_state x (empty_state,Rval (y)) /\
     evaluate_list F env empty_state xs (empty_state,Rval (ys)))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC[evaluate_empty_store_IMP_any_store,SND,
               prove(``∀x. has_emp_no_fail (empty_state,Rval x)``,simp[empty_state_def]),
               determTheory.big_exp_determ,PAIR_EQ]);

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

val Eval_Val_BOOL_FALSE = store_thm("Eval_Val_BOOL_FALSE",
  ``Eval env (App (Opb Lt) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL FALSE)``,
  SIMP_TAC (srw_ss()) [Eval_Val_BOOL_F,FALSE_def]);

val Eval_Val_BOOL_TRUE = store_thm("Eval_Val_BOOL_TRUE",
  ``Eval env (App (Opb Leq) [Lit (IntLit 0); Lit (IntLit 0)]) (BOOL TRUE)``,
  SIMP_TAC (srw_ss()) [Eval_Val_BOOL_T,TRUE_def]);

val MEMBER_def = Define `
  (MEMBER (x:'a) [] <=> F) /\
  (MEMBER x (y::ys) <=> (x = y) \/ MEMBER x ys)`;

val MEM_EQ_MEMBER = prove(
  ``!ys x. MEM x ys = MEMBER x ys``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [MEMBER_def]);

val MEMBER_INTRO = store_thm("MEMBER_INTRO",
  ``(MEM = MEMBER) /\ (MEM x = MEMBER x) /\ (MEM x ys = MEMBER x ys)``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,MEM_EQ_MEMBER]);

(* always_evaluates *)

val always_evaluates_def = Define `
  always_evaluates env exp =
    !(s1:unit state). ?s2 res. evaluate F env s1 exp (s2,Rval res)`;

val Eval_IMP_always_evaluates = store_thm("Eval_IMP_always_evaluates",
  ``!env exp P. Eval env exp P ==> always_evaluates env exp``,
  FULL_SIMP_TAC std_ss [Eval_def,always_evaluates_def] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`s1`,`res`] \\ FULL_SIMP_TAC std_ss []
  \\ imp_res_tac evaluate_empty_state_IMP
  \\ FULL_SIMP_TAC std_ss []);

val always_evaluates_ref = store_thm("always_evaluates_ref",
  ``!env exp. always_evaluates env exp ==>
              always_evaluates env (App Opref [exp])``,
  FULL_SIMP_TAC std_ss [always_evaluates_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FIRST_X_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `s1`)
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ SRW_TAC [boolSimps.DNF_ss] [do_app_def,store_alloc_def]
  \\ ONCE_REWRITE_TAC [hd (tl (CONJUNCTS evaluate_cases))]
  \\ SRW_TAC [] []
  \\ METIS_TAC []);

val always_evaluates_fn = store_thm("always_evaluates_fn",
  ``!n exp env. always_evaluates env (Fun n exp)``,
  FULL_SIMP_TAC std_ss [always_evaluates_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SRW_TAC [] []);

(* lookup cons *)

val lookup_cons_write = store_thm("lookup_cons_write",
  ``!funs n x env name env1.
      (lookup_cons name (write n x env) = lookup_cons name env) /\
      (lookup_cons name (write_rec funs env1 env) = lookup_cons name env)``,
  Induct \\ REPEAT STRIP_TAC
  \\ fs [write_rec_thm,write_def,lookup_cons_thm]);

val lookup_var_id_write = store_thm("lookup_var_id_write",
  ``(lookup_var_id (Short name) (write n v env) =
       if n = name then SOME v else lookup_var_id (Short name) env) /\
    (lookup_var_id (Long mn name) (write n v env) =
       lookup_var_id (Long mn name) env)``,
  fs [write_def] \\ EVAL_TAC \\ rw [] \\ fs [lookup_var_id_def]);

val DISJOINT_set_SIMP = store_thm("DISJOINT_set_SIMP",
  ``(DISJOINT (set []) s <=> T) /\
    (DISJOINT (set (x::xs)) s <=> ~(x IN s) /\ DISJOINT (set xs) s)``,
  REPEAT STRIP_TAC THEN1 (SRW_TAC [] []) \\ Cases_on `x IN s` \\ fs []);

(* removing shadowed elements from an alist *)

val ASHADOW_def = tDefine "ASHADOW" `
  (ASHADOW [] = []) /\
  (ASHADOW (x::xs) =
     if EXISTS (\y. FST x = FST y) xs
     then x :: ASHADOW (FILTER (\y. FST x <> FST y) xs)
     else x :: ASHADOW xs)`
 (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH xs` \\ fs [rich_listTheory.LENGTH_FILTER_LEQ])

val ASHADOW_PREFIX = prove(
  ``!xs ys.
      ALL_DISTINCT (MAP FST xs) /\
      EVERY (\y. ~(MEM y (MAP FST ys))) (MAP FST xs) ==>
      (ASHADOW (xs ++ ys) = xs ++ ASHADOW ys)``,
  Induct \\ fs [FORALL_PROD,ASHADOW_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ fs [EVERY_MEM,FORALL_PROD,EXISTS_MEM,MEM_MAP,EXISTS_PROD,PULL_EXISTS]
  \\ Cases_on `y` \\ fs [] \\ RES_TAC);

val MEM_MAP_ASHADOW = prove(
  ``!xs y. MEM y (MAP FST (ASHADOW xs)) = MEM y (MAP FST xs)``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs[] THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ fs [FORALL_PROD,ASHADOW_def]
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ `LENGTH (FILTER (\y. FST h <> FST y) t) <= LENGTH t` by ALL_TAC
  THEN1 fs [rich_listTheory.LENGTH_FILTER_LEQ]
  \\ `LENGTH (FILTER (\y. FST h <> FST y) t) < SUC (LENGTH t)` by DECIDE_TAC
  \\ RES_TAC \\ fs[]
  \\ fs [MEM_MAP,MEM_FILTER] \\ METIS_TAC []);

val EVERY_ALOOKUP_LEMMA = prove(
  ``!xs. ALL_DISTINCT (MAP FST xs) ==>
         EVERY (\(x,y,z). ALOOKUP xs x = SOME (y,z)) xs``,
  Induct \\ srw_tac [] [] \\ PairCases_on `h` \\ fs []
  \\ fs [EVERY_MEM,FORALL_PROD] \\ rpt strip_tac
  \\ res_tac \\ Cases_on `h0 = p_1`
  \\ fs [MEM_MAP,FORALL_PROD] \\ metis_tac []);

val ALOOKUP_FILTER = prove(
  ``!t a q. q <> a ==> (ALOOKUP (FILTER (\y. q <> FST y) t) a = ALOOKUP t a)``,
  Induct THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ fs [alistTheory.ALOOKUP_def,FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ Cases_on `p_1 = a` \\ fs []
  \\ SRW_TAC [] []);

val ALOOKUP_ASHADOW = prove(
  ``!xs a. ALOOKUP (ASHADOW xs) a = ALOOKUP xs a``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs [] THEN1 EVAL_TAC
  \\ Cases_on `h` \\ fs [FORALL_PROD,ASHADOW_def]
  \\ SRW_TAC [] []
  \\ `LENGTH (FILTER (\y. q <> FST y) t) < SUC (LENGTH t)` by ALL_TAC
  \\ RES_TAC \\ fs [ALOOKUP_FILTER]
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH t`
  \\ fs [rich_listTheory.LENGTH_FILTER_LEQ]);

val ALL_DISTINCT_MAP_FST_ASHADOW = prove(
  ``!xs. ALL_DISTINCT (MAP FST (ASHADOW xs))``,
  STRIP_TAC \\ completeInduct_on `LENGTH xs`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs [] THEN1 EVAL_TAC
  \\ Cases_on `h` \\ fs [ASHADOW_def]
  \\ SRW_TAC [] [MEM_MAP_ASHADOW]
  \\ fs [EXISTS_MEM,MEM_MAP,MEM_FILTER,FORALL_PROD,EVERY_MEM]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `LENGTH t` \\ fs []
  \\ fs [rich_listTheory.LENGTH_FILTER_LEQ]);

(* size lemmas *)

val v6_size = prove(
  ``!vs v. (MEM v vs ==> v_size v < v6_size vs)``,
  Induct \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

val v4_size = prove(
  ``!env x v. (MEM (x,v) env ==> v_size v < v4_size env)``,
  Induct \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

val v2_size = prove(
  ``!xs a. MEM a xs ==> v3_size a < v2_size xs``,
  Induct \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ SRW_TAC [] [semanticPrimitivesTheory.v_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

val v_size_lemmas = store_thm("v_size_lemmas",
  ``(MEM (x,y) envE ==> v_size y <= v4_size envE) /\
    (MEM (x,y) xs /\ MEM (t,xs) p1 ==> v_size y <= v2_size p1) /\
    (MEM v vs ==> v_size v < v6_size vs)``,
  FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC v4_size
  \\ IMP_RES_TAC v2_size
  \\ IMP_RES_TAC v6_size
  \\ FULL_SIMP_TAC std_ss [semanticPrimitivesTheory.v_size_def]
  \\ DECIDE_TAC);

(* introducing a module (Tmod) *)

val type_names_def = Define `
  (type_names [] names = names) /\
  (type_names (Dtype tds :: xs) names =
     type_names xs (MAP (FST o SND) tds ++ names)) /\
  (type_names (x :: xs) names = type_names xs names)`;

val type_names_eq = prove(
  ``!ds names .
      type_names ds names =
      (FLAT (REVERSE (MAP (\d.
                case d of
                  Dlet v6 v7 => []
                | Dletrec v8 => []
                | Dtype tds => MAP (\(tvs,tn,ctors). tn) tds
                | Dtabbrev tvs tn t => []
                | Dexn v10 v11 => []) ds))) ++ names``,
  Induct \\ fs [type_names_def] \\ Cases_on `h`
  \\ fs [type_names_def] \\ fs [FORALL_PROD,listTheory.MAP_EQ_f]);

val no_dup_types_eval = prove(
  ``!ds. no_dup_types ds = ALL_DISTINCT (type_names ds [])``,
  fs [no_dup_types_def,type_names_eq,decs_to_types_def,ALL_DISTINCT_FLAT_REVERSE]);

val lookup_APPEND = prove(
  ``!xs ys n. ~(MEM n (MAP FST ys)) ==>
              (ALOOKUP (xs ++ ys) n = ALOOKUP xs n)``,
  Induct THEN1
   (FULL_SIMP_TAC std_ss [APPEND] \\ Induct
    \\ FULL_SIMP_TAC std_ss [MAP,MEM,FORALL_PROD] >>
    rw [])
  \\ FULL_SIMP_TAC std_ss [FORALL_PROD,APPEND]
  \\ rw []);

val FEVERY_DRESTRICT_FUPDATE = store_thm("FEVERY_DRESTRICT_FUPDATE",
  ``FEVERY P (DRESTRICT (f |+ (x,y)) (COMPL s)) <=>
    (~(x IN s) ==> P (x,y)) /\
    FEVERY P (DRESTRICT f (COMPL (x INSERT s)))``,
  fs [] \\ SRW_TAC [] [finite_mapTheory.FEVERY_FUPDATE]
  THEN1 (`COMPL s INTER COMPL {x} = COMPL (x INSERT s)` by
      (fs [Once pred_setTheory.EXTENSION] \\ METIS_TAC []) \\ fs [])
  \\ `COMPL s = COMPL (x INSERT s)` by
     (fs [Once pred_setTheory.EXTENSION] \\ METIS_TAC []) \\ fs [])

val PULL_EXISTS_EXTRA = store_thm("PULL_EXISTS_EXTRA",
  ``(Q ==> ?x. P x) <=> ?x. Q ==> P x``,
  metis_tac []);

val evaluate_Fun = store_thm("evaluate_Fun",
  ``evaluate F env s (Fun n exp) (s,Rval r) <=> r = Closure env n exp``,
  fs [Once evaluate_cases]);

val evaluate_Var = store_thm("evaluate_Var",
  ``evaluate F env s (Var (Short n)) (s,Rval r) <=>
    ?v. lookup_var n env = SOME r``,
  fs [Once evaluate_cases] \\ EVAL_TAC);

val lookup_var_eq_lookup_var_id = store_thm("lookup_var_eq_lookup_var_id",
  ``lookup_var n = lookup_var_id (Short n)``,
  fs [FUN_EQ_THM] \\ EVAL_TAC \\ fs []);

val PRECONDITION_T = save_thm("PRECONDITION_T",EVAL ``PRECONDITION T``);

val Eval_evaluate_IMP = store_thm("Eval_evaluate_IMP",
  ``Eval env exp P /\
    evaluate F env empty_state exp (empty_state, Rval v) ==>
    P v``,
  fs [Eval_def] \\ rw [] \\ imp_res_tac evaluate_11_Rval \\ fs []);

val pair_CASE_UNCURRY = store_thm("pair_CASE_UNCURRY",
  ``!x y. pair_CASE x y = UNCURRY y x``,
  Cases \\ EVAL_TAC \\ fs []);

val IF_T = store_thm("IF_T",``(if T then x else y) = x:'a``,SIMP_TAC std_ss []);
val IF_F = store_thm("IF_F",``(if F then x else y) = y:'a``,SIMP_TAC std_ss []);

val sat_hyp_lemma = store_thm("sat_hyp_lemma",
  ``(b1 ==> (x1 = x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y``,
  Cases_on `b1` \\ Cases_on `x1` \\ Cases_on `x2` \\ Cases_on `y` \\ EVAL_TAC);

val IMP_EQ_F = store_thm("IMP_EQ_F",``~b ==> (b = F)``,REWRITE_TAC [])
val IMP_EQ_T = store_thm("IMP_EQ_T",``b ==> (b = T)``,REWRITE_TAC [])

val IF_TAKEN = store_thm("IF_TAKEN",
  ``!b x y. b ==> ((if b then x else y) = x:'unlikely)``,
  SIMP_TAC std_ss []);

val LIST_TYPE_And = store_thm("LIST_TYPE_And",
  ``LIST_TYPE (And a P) = And (LIST_TYPE a) (EVERY (P:'a->bool))``,
  SIMP_TAC std_ss [FUN_EQ_THM,And_def] \\ Induct
  \\ FULL_SIMP_TAC std_ss [MEM,LIST_TYPE_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [And_def])

val EVERY_MEM_CONTAINER = store_thm("EVERY_MEM_CONTAINER",
  ``!P l. EVERY P l <=> !e. CONTAINER (MEM e l) ==> P (e:'a)``,
  SIMP_TAC std_ss [EVERY_MEM,CONTAINER_def]);

val PRECONDITION_EQ_CONTAINER = store_thm("PRECONDITION_EQ_CONTAINER",
  ``(PRECONDITION p = CONTAINER p) /\
    (CONTAINER ~p = ~CONTAINER p) /\ CONTAINER T``,
  EVAL_TAC);

val CONTAINER_NOT_ZERO = store_thm("CONTAINER_NOT_ZERO",
  ``!P. (~(CONTAINER (b = 0)) ==> P b) =
        !n. (CONTAINER (b = SUC n)) ==> P (SUC n:num)``,
  REPEAT STRIP_TAC THEN Cases_on `b`
  THEN EVAL_TAC THEN SRW_TAC [] [ADD1]);

val IMP_PreImp_LEMMA = store_thm("IMP_PreImp_LEMMA",
  ``!b1 b2 b3. (b1 ==> b3 ==> b2) ==> b3 ==> PreImp b1 b2``,
  REPEAT Cases THEN REWRITE_TAC [PreImp_def,PRECONDITION_def]);

val PRE_IMP = store_thm("PRE_IMP",
  ``T /\ PRECONDITION b ==> PRECONDITION b``,
  EVAL_TAC)

val PreImp_IMP_T = store_thm("PreImp_IMP_T",
  ``PreImp b1 b2 /\ T ==> PreImp b1 b2``,
  EVAL_TAC)

val CONJ_IMP = store_thm("CONJ_IMP",
  ``!b1 b2 b12 b3 b4 b34.
      (b1 /\ b2 ==> b12) /\ (b3 /\ b4 ==> b34) ==>
      ((b1 /\ b3) /\ (b2 /\ b4) ==> b12 /\ b34)``,
  REPEAT Cases THEN EVAL_TAC) |> SPEC_ALL;

val IMP_SPLIT = store_thm("IMP_SPLIT",
  ``!b12 b3 b4 b34.
      (b12 = b12) /\ (b3 /\ b4 ==> b34) ==>
      ((b12 ==> b3) /\ (b12 ==> b4) ==> (b12 ==> b34))``,
  REPEAT Cases THEN EVAL_TAC) |> SPEC_ALL;

val FORALL_SPLIT = store_thm("FORALL_SPLIT",
  ``(!x. P1 x /\ P2 x ==> P (x:'a)) ==>
    ($! P1 ) /\ ($! P2 ) ==> $! P ``,
  FULL_SIMP_TAC std_ss [FORALL_THM]);

val DEFAULT_IMP = store_thm("DEFAULT_IMP",
  ``!b1. b1 /\ b1 ==> b1``,
  SIMP_TAC std_ss []);

val combine_lemma = store_thm("combine_lemma",
  ``!b1 b2 b3 b4. (b1 /\ b2 ==> b3) /\ (b3 ==> b4) ==> b2 ==> b1 ==> b4``,
  REPEAT Cases THEN SIMP_TAC std_ss [])

val IMP_PreImp_THM = store_thm("IMP_PreImp_THM",
  ``(b ==> PreImp x y) ==> ((x ==> b) ==> PreImp x y)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [PreImp_def,PRECONDITION_def]);

val PreImp_IMP = store_thm("PreImp_IMP",
  ``(PRECONDITION x ==> PreImp x y) ==> PreImp x y``,
  SIMP_TAC std_ss [PreImp_def]);

val evaluate_Mat = save_thm("evaluate_Mat",
  ``evaluate c x env (Mat e pats) (xx,Rval res)``
  |> (ONCE_REWRITE_CONV [evaluate_cases] THENC SIMP_CONV (srw_ss()) []))

val evaluate_match_Conv = save_thm("evaluate_match_Conv",
  ``evaluate_match c env st args
       ((Pcon xx pats,exp2)::pats2) errv (yyy,Rval y)``
  |> (ONCE_REWRITE_CONV [evaluate_cases] THENC
      SIMP_CONV (srw_ss()) [pmatch_def]))

val evaluate_match_rw = store_thm("evaluate_match_rw",
  ``evaluate_match c env st args
      ((Pcon xx pats,exp2)::pats2) errv (yyy,Rval y) <=>
    ALL_DISTINCT (pat_bindings (Pcon xx pats) []) /\
    case pmatch env.c st.refs (Pcon xx pats) args env.v of
    | No_match =>
        evaluate_match c env st args pats2 errv (yyy,Rval y)
    | Match env7 =>
        evaluate c (env with v := env7) st exp2 (yyy,Rval y)
    | _ => F``,
  SIMP_TAC std_ss [evaluate_match_Conv
    |> SIMP_RULE std_ss []]
  \\ Cases_on `pmatch env.c st.refs (Pcon xx pats) args env.v`
  \\ FULL_SIMP_TAC (srw_ss()) []);

(* terms used by the Lib file *)

val translator_terms = save_thm("translator_terms",
  pack_list (pack_pair pack_string pack_term)
    [("find_recfun",``find_recfun name (funs:('a,'b # 'c) alist)``),
     ("eq type",``EqualityType (a:'a->v->bool)``),
     ("lookup_cons",``lookup_cons s e = SOME x``),
     ("lookup_var_id",``lookup_var_id s e = SOME (x:v)``),
     ("eq remove",``!b x. Eq b x = (b:'a->v->bool)``),
     ("map pat",``MAP (f:'a->'b)``),
     ("filter pat",``FILTER (f:'a->bool)``),
     ("every pat",``EVERY (f:'a->bool)``),
     ("exists pat",``EXISTS (f:'a->bool)``),
     ("n = 0",``(n = (0:num))``),
     ("0 = n",``(0 = (n:num))``),
     ("bind",``(Con(SOME(Short"Bind")) [])``),
     ("eq arrow",``Eq (a:'a->v->bool) x --> (b:'b->v->bool)``),
     ("arrow eq",``Arrow (Eq a (x:'a)) (b:'b->v->bool)``),
     ("precond = T",``!b. PRECONDITION b = T``),
     ("WF",``WF:('a -> 'a -> bool) -> bool``),
     ("COND",``COND:bool -> 'a -> 'a -> 'a``),
     ("not eq",``~(x = y:'a)``),
     ("lookup_cons eq",``lookup_cons n env = x``),
     ("Eval Var",``Eval env (Var n) (a (y:'a))``),
     ("PMATCH_ROW",``(PMATCH_ROW f1 f2):('a -> 'c) -> 'b -> 'c option``),
     ("PMATCH_ROW_T",``(PMATCH_ROW (f1:'a->'b) (K T) f3):'b -> 'c option``),
     ("PMATCH",``PMATCH x (l :('a -> 'b option) list)``),
     ("auto eq proof 1",``!x1 x2 x3 x4. bbb``),
     ("auto eq proof 2",``!x1 x2. bbb ==> bbbb``),
     ("remove lookup_cons",``!x1 x2 x3. (lookup_cons x1 x2 = SOME x3) = T``)]);

val _ = export_theory();
