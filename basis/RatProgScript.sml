open preamble ml_translatorLib ml_translatorTheory ml_progLib
     mlvectorTheory IntProgTheory basisFunctionsLib
     realTheory realLib RealArith gcdTheory

val _ = new_theory"RatProg"

val _ = translation_extends "IntProg";

val _ = ml_prog_update (open_module "Rat");

val REAL_TYPE_def = Define `
  REAL_TYPE (r:real) =
    \v. ?(n:int) (d:num). (r = (real_of_int n) / (real_of_num d)) /\
                          gcd (num_of_int n) d = 1 /\ d <> 0 /\
                          PAIR_TYPE INT NUM (n,d) v`;

val _ = add_type_inv ``REAL_TYPE`` ``:(int # num)``;

val pair_of_num_def = Define `
  pair_of_num n = ((& (n:num)):int, 1:num)`;

val _ = next_ml_names := ["fromInt"];
val pair_of_num_v_thm = translate pair_of_num_def;

val Eval_REAL_NUM = Q.prove(
  `!v. (NUM --> PAIR_TYPE INT NUM) pair_of_num v ==>
       (NUM --> REAL_TYPE) ($&) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
    FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ qexists_tac `& x` \\ qexists_tac `1`
  \\ fs [pair_of_num_def] \\ fs [real_of_int_def])
  |> (fn th => MATCH_MP th pair_of_num_v_thm)
  |> add_user_proved_v_thm;

val pair_le_def = Define `
  pair_le (n1,d1) (n2,d2) = (n1 * & d2 <= n2 * (& d1):int)`;

val _ = next_ml_names := ["<="];
val pair_le_v_thm = translate pair_le_def;

val Eval_REAL_LE = Q.prove(
  `!v. (PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM --> BOOL) pair_le v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) ($<=) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
    pair_le_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ fs [BOOL_def] \\ rw [] \\ rveq
  \\ EQ_TAC \\ rw []
  \\ fs [realTheory.le_rat]
  \\ Cases_on `n` \\ fs [real_of_int_def]
  \\ Cases_on `n'` \\ fs [real_of_int_def]
  \\ rfs [realTheory.REAL_MUL_LNEG,integerTheory.INT_MUL_CALCULATE]
  \\ qpat_x_assum `(_ <= _:int)` mp_tac
  \\ fs [integerTheory.INT_NOT_LE])
  |> (fn th => MATCH_MP th pair_le_v_thm)
  |> add_user_proved_v_thm;

val _ = next_ml_names := [">="];
val v = translate real_ge;

val pair_lt_def = Define `
  pair_lt (n1,d1) (n2,d2) = (n1 * & d2 < n2 * (& d1):int)`;

val _ = next_ml_names := ["<"];
val pair_lt_v_thm = translate pair_lt_def;

val Eval_REAL_LT = Q.prove(
  `!v. (PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM --> BOOL) pair_lt v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) ($<) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
    pair_lt_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ fs [BOOL_def] \\ rw [] \\ rveq
  \\ EQ_TAC \\ rw []
  \\ fs [realTheory.lt_rat]
  \\ Cases_on `n` \\ fs [real_of_int_def]
  \\ Cases_on `n'` \\ fs [real_of_int_def]
  \\ rfs [realTheory.REAL_MUL_LNEG,integerTheory.INT_MUL_CALCULATE]
  \\ qpat_x_assum `(_ <= _:int)` mp_tac
  \\ fs [integerTheory.INT_NOT_LE])
  |> (fn th => MATCH_MP th pair_lt_v_thm)
  |> add_user_proved_v_thm;

val _ = next_ml_names := [">"];
val v = translate real_gt;

val _ = next_ml_names := ["min"];
val v = translate realTheory.min_def;

val _ = next_ml_names := ["max"];
val v = translate realTheory.max_def;

val div_gcd_def = Define `
  div_gcd a b =
    let d = gcd (num_of_int a) b in
      if d = 0 \/ d = 1 then (a,b) else (a / &d, b DIV d)`;

val res = translate div_gcd_def;

val gcd_LESS_EQ = prove(
  ``!m n. n <> 0 ==> gcd$gcd m n <= n``,
  recInduct gcd_ind \\ rw []
  \\ once_rewrite_tac [gcdTheory.gcd_def]
  \\ rw [] \\ fs []);

val PAIR_TYPE_IMP_REAL_TYPE = prove(
  ``r = real_of_int m / & n /\ n <> 0 ==>
    PAIR_TYPE INT NUM (div_gcd m n) v ==> REAL_TYPE r v``,
  fs [REAL_TYPE_def,div_gcd_def] \\ rw []
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ pop_assum kall_tac
  \\ `gcd$gcd (num_of_int m) n <> 0` by fs []
  \\ `0 < gcd$gcd (num_of_int m) n` by simp []
  \\ Cases_on `m` \\ simp [ZERO_DIV]
  \\ fs [DIV_EQ_X,NOT_LESS,gcd_LESS_EQ]
  \\ rename1 `gcd$gcd m n <> 1`
  THEN1
   (qspecl_then [`m`,`n`] mp_tac FACTOR_OUT_GCD \\ fs []
    \\ strip_tac \\ qabbrev_tac `kk = gcd$gcd m n`
    \\ pop_assum kall_tac \\ rveq \\ fs [MULT_DIV]
    \\ rewrite_tac [GSYM REAL_OF_NUM_MUL]
    \\ match_mp_tac REAL_DIV_LMUL_CANCEL \\ fs [])
  \\ qspecl_then [`m`,`n`] mp_tac FACTOR_OUT_GCD \\ fs []
  \\ strip_tac \\ qabbrev_tac `kk = gcd$gcd m n`
  \\ pop_assum kall_tac \\ rveq \\ fs [MULT_DIV]
  \\ rewrite_tac [GSYM REAL_OF_NUM_MUL,GSYM integerTheory.INT_MUL]
  \\ rewrite_tac [integerTheory.INT_NEG_RMUL,realTheory.REAL_NEG_RMUL]
  \\ simp [integerTheory.INT_DIV_LMUL,REAL_DIV_LMUL_CANCEL]);

val pair_add_def = Define `
  pair_add (n1:int, d1:num) (n2, d2) =
    div_gcd ((n1 * &d2) + (n2 * &d1)) (d1 * d2)`;

val _ = next_ml_names := ["+"];
val pair_add_v_thm = translate pair_add_def;

val Eval_REAL_ADD = Q.prove(
  `!v. (PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM) pair_add v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) ($+) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once REAL_TYPE_def,PULL_EXISTS,
    pair_add_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once REAL_TYPE_def,PULL_EXISTS,
       pair_add_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac) \\ rw [] \\ pop_assum mp_tac
  \\ match_mp_tac PAIR_TYPE_IMP_REAL_TYPE
  \\ fs [REAL_ADD_RAT]
  \\ fs [AC REAL_MUL_COMM REAL_MUL_ASSOC])
  |> (fn th => MATCH_MP th pair_add_v_thm)
  |> add_user_proved_v_thm;

val pair_sub_def = Define `
  pair_sub (n1:int, d1:num) (n2, d2) =
    div_gcd ((n1 * &d2) - (n2 * &d1)) (d1 * d2)`;

val _ = next_ml_names := ["-"];
val pair_sub_v_thm = translate pair_sub_def;

val Eval_REAL_SUB = Q.prove(
  `!v. (PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM) pair_sub v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) ($-) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once REAL_TYPE_def,PULL_EXISTS,
    pair_sub_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once REAL_TYPE_def,PULL_EXISTS,
       pair_add_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac) \\ rw [] \\ pop_assum mp_tac
  \\ match_mp_tac PAIR_TYPE_IMP_REAL_TYPE
  \\ fs[real_of_int_sub]
  \\ fs [real_sub, real_div, REAL_NEG_LMUL]
  \\ fs [GSYM real_div]
  \\ fs [REAL_ADD_RAT]
  \\ fs [AC REAL_MUL_COMM REAL_MUL_ASSOC])
  |> (fn th => MATCH_MP th pair_sub_v_thm)
  |> add_user_proved_v_thm;

val real_neg_lem = prove(
  ``!(x:real). - x = 0 - x``,
  fs[]);

val _ = next_ml_names := ["~"];
val pair_neg_v_thm = translate real_neg_lem;

val pair_mul_def = Define `
  pair_mul (n1,d1) (n2,d2) = div_gcd (n1 * n2:int) (d1 * d2:num)`;

val _ = next_ml_names := ["*"];
val pair_mul_v_thm = translate pair_mul_def;

val Eval_REAL_MUL = Q.prove(
  `!v. (PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM) pair_mul v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) ($*) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once REAL_TYPE_def,PULL_EXISTS,
    pair_mul_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once REAL_TYPE_def,PULL_EXISTS,
       pair_add_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac) \\ rw [] \\ pop_assum mp_tac
  \\ match_mp_tac PAIR_TYPE_IMP_REAL_TYPE
  \\ fs [real_of_int_mul]
  \\ match_mp_tac REAL_EQ_RMUL_IMP
  \\ qexists_tac `&(d * d')`
  \\ `&(d * d') ≠ 0:real` by fs []
  \\ drule REAL_DIV_RMUL
  \\ simp_tac std_ss [] \\ fs [] \\ rw []
  \\ qabbrev_tac `n1 = real_of_int n`
  \\ qabbrev_tac `n2 = real_of_int n'`
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ `n1 / &d * (n2 / &d') * &(d * d') =
      ((n1 / &d) * &d) * ((n2 / &d') * &d')` by
   (fs [AC REAL_MUL_ASSOC REAL_MUL_SYM]
    \\ fs [REAL_MUL_ASSOC]
    \\ fs [AC REAL_MUL_ASSOC REAL_MUL_SYM])
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ `&d <> 0:real /\ &d' <> 0:real` by fs []
  \\ fs [REAL_DIV_RMUL])
  |> (fn th => MATCH_MP th pair_mul_v_thm)
  |> add_user_proved_v_thm;

val pair_inv_def = Define `
  pair_inv (n1,d1) =
    (if n1 < 0 then - & d1 else (& d1):int,num_of_int n1)`;

val _ = next_ml_names := ["inv"];
val pair_inv_v_thm = translate pair_inv_def;

val Eval_REAL_INV = Q.prove(
  `PRECONDITION (r <> 0) ==>
   !v. (PAIR_TYPE INT NUM --> PAIR_TYPE INT NUM) pair_inv v ==>
       (Eq REAL_TYPE r --> REAL_TYPE) inv v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
    pair_mul_def,FORALL_PROD,Eq_def,PRECONDITION_def] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ disch_then (qspec_then `refs` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ fs [realTheory.REAL_EQ_LDIV_EQ] \\ rveq
  \\ fs [pair_inv_def,real_of_int_def]
  \\ Cases_on `n` \\ fs []
  THEN1
   (qexists_tac `&d`
    \\ qexists_tac `n'` \\ fs []
    \\ rewrite_tac [realTheory.REAL_INV_1OVER]
    \\ fs [realTheory.div_ratr]
    \\ once_rewrite_tac [GCD_SYM] \\ fs [])
  THEN1
   (qexists_tac `-&d`
    \\ qexists_tac `n'` \\ fs []
    \\ rewrite_tac [realTheory.REAL_INV_1OVER]
    \\ fs [realTheory.div_ratr]
    \\ fs [realTheory.neg_rat]
    \\ once_rewrite_tac [GCD_SYM] \\ fs []))
  |> UNDISCH
  |> (fn th => MATCH_MP th pair_inv_v_thm)
  |> add_user_proved_v_thm;

val _ = (next_ml_names := ["/"])
val pair_div_v_thm = translate realTheory.real_div;

val pair_div_side_def = pair_div_v_thm
  |> hyp |> hd |> rand |> repeat rator |> DB.match [] |> hd |> snd |> fst;

val pair_div_v_thm =
  pair_div_v_thm
  |> DISCH_ALL |> REWRITE_RULE [pair_div_side_def] |> UNDISCH_ALL
  |> add_user_proved_v_thm;

val toString_def = Define `
  toString (i:int,n:num) =
    if n = 1 then mlint$toString i else
      concat [mlint$toString i ; implode"/" ; mlint$toString (& n)]`

val _ = (next_ml_names := ["toString"]);
val v = translate toString_def;

val EqualityType_REAL_TYPE = store_thm("EqualityType_REAL_TYPE",
  ``EqualityType REAL_TYPE``,
  rw [EqualityType_def]
  \\ fs [REAL_TYPE_def,PAIR_TYPE_def,INT_def,NUM_def] \\ EVAL_TAC
  \\ rveq \\ fs []
  \\ EQ_TAC \\ strip_tac \\ fs []
  \\ fs [GSYM real_of_int_def]
  \\ Cases_on `d = d'` \\ rveq
  THEN1
   (fs [realTheory.real_div,realTheory.REAL_INV_EQ_0] \\ fs []
    \\ Cases_on `n` \\ Cases_on `n'` \\ fs [real_of_int_def])
  \\ fs []
  \\ `(real_of_int n / &d) * (&d * &d') = (real_of_int n' / &d') * (&d * &d')`
         by fs [realTheory.REAL_EQ_RMUL]
  \\ `real_of_int n / &d * &d = real_of_int n` by
       (match_mp_tac realTheory.REAL_DIV_RMUL \\ fs [])
  \\ `real_of_int n' / &d' * &d' = real_of_int n'` by
       (match_mp_tac realTheory.REAL_DIV_RMUL \\ fs [])
  \\ `real_of_int n * & d' = real_of_int n' * & d` by
        metis_tac [realTheory.REAL_MUL_ASSOC,realTheory.REAL_MUL_COMM]
  \\ pop_assum mp_tac
  \\ ntac 3 (pop_assum kall_tac) \\ fs []
  \\ Cases_on `n` \\ Cases_on `n'` \\ fs [real_of_int_def]
  \\ rveq \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ rfs [realTheory.REAL_DIV_RMUL]
  \\ fs [realTheory.real_div,realTheory.REAL_INV_EQ_0]
  \\ rename1 `d1 * n1 = d2 * n2:num`
  \\ `divides d2 (d1 * n1) /\
      divides n2 (d1 * n1) /\
      divides d1 (d2 * n2) /\
      divides n1 (d2 * n2)` by
     (fs [dividesTheory.divides_def] \\ metis_tac [MULT_COMM])
  \\ `gcd d1 n2 = 1 /\ gcd d2 n1 = 1` by metis_tac [GCD_SYM]
  \\ fs []
  \\ imp_res_tac L_EUCLIDES
  \\ imp_res_tac dividesTheory.DIVIDES_ANTISYM
  \\ rveq \\ rfs [arithmeticTheory.EQ_MULT_RCANCEL])
  |> store_eq_thm;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()
