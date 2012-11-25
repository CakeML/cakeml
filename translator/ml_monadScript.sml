
open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_monad";

open ml_translatorTheory;
open ml_translatorLib;

open hol_kernelTheory;
open stringTheory;
open MiniMLTheory;

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

val res = translate string_lt_def;
val res = translate string_le_def;
val res = translate string_gt_def;
val res = translate string_ge_def;

(* construct type refinement invariants *)

val _ = register_type ``:hol_type``;
val _ = register_type ``:term``;
val _ = register_type ``:thm``;

(*
  fetch "-" "PAIR_TYPE_def";
  fetch "-" "LIST_TYPE_def";
  fetch "-" "HOL_TYPE_TYPE_def";
  fetch "-" "TERM_TYPE_def";
  fetch "-" "THM_TYPE_def";
*)

(* definition of EvalM *)

val HOL_STORE_def = Define `
  HOL_STORE s refs =
    4 <= LENGTH s /\
    (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) NUM)) refs.the_type_constants (EL 0 s) /\
    (LIST_TYPE (PAIR_TYPE (LIST_TYPE CHAR) HOL_TYPE_TYPE)) refs.the_term_constants (EL 1 s) /\
    (LIST_TYPE THM_TYPE refs.the_axioms) (EL 2 s) /\
    (TERM_TYPE refs.the_clash_var) (EL 3 s)`;

val EvalM_def = Define `
  EvalM env exp P <=>
    !s refs. HOL_STORE s refs ==> ?res. evaluate' s env exp res /\ P (s,refs) res`;

(* refinement invariant for ``:'a M`` *)

val HOL_MONAD_def = Define `
  HOL_MONAD (a:'a->v->bool) (x:'a M) (s1:store,state) (res: (store # v result)) =
    case (x state, res) of
      ((HolRes y, state), (s2, Rval v)) => HOL_STORE s2 state /\ a y v
    | ((HolErr e, state), (s2, Rerr _)) => HOL_STORE s2 state
    | _ => F`

(* return *)

val EvalM_return = store_thm("EvalM_return",
  ``Eval env exp (a x) ==>
    EvalM env exp (HOL_MONAD a (ex_return x))``,
  SIMP_TAC std_ss [Eval_def,EvalM_def,HOL_MONAD_def,ex_return_def]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `s,(Rval (res))`
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate'_empty_store_IMP]);

(* bind *)

val EvalM_bind = store_thm("EvalM_bind",
  ``EvalM env e1 (HOL_MONAD b (x:'b M)) /\
    (!x v. b x v ==> EvalM ((name,v)::env) e2 (HOL_MONAD a ((f x):'a M))) ==>
    EvalM env (Let name e1 e2) (HOL_MONAD a (ex_bind x f))``,
  SIMP_TAC std_ss [EvalM_def,HOL_MONAD_def,ex_return_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ RES_TAC
  \\ Cases_on `x refs` \\ Cases_on `q`
  \\ Cases_on `res` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (Cases_on `r'` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x refs = (HolRes res1,r)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate' s env e1 (q,Rval (state1))` []
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`res1`,`state1`,`q`,`r`])
    \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
    \\ Q.EXISTS_TAC `res` \\ REPEAT STRIP_TAC THEN1
     (ONCE_REWRITE_TAC [evaluate'_cases]
      \\ FULL_SIMP_TAC (srw_ss()) [] \\ DISJ1_TAC
      \\ Q.LIST_EXISTS_TAC [`state1`,`q`] \\ ASM_SIMP_TAC std_ss [bind_def])
    \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def])
  THEN1
   (Cases_on `r'` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `x refs = (HolErr res1,r)` []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate' s env e1 (q,Rerr (state1))` []
    \\ FULL_SIMP_TAC std_ss [PULL_FORALL]
    \\ Q.EXISTS_TAC `(q,Rerr state1)` \\ STRIP_TAC
    THEN1 (ONCE_REWRITE_TAC [evaluate'_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC (srw_ss()) [ex_bind_def]));

(* some pure functions *)

val res = translate MEMBER_def;
val res = translate listTheory.EVERY_DEF;
val res = translate listTheory.EXISTS_DEF;
val res = translate listTheory.FILTER;
val res = translate listTheory.APPEND;
val res = translate listTheory.MAP;
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

val _ = export_theory();

