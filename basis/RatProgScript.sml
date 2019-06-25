(*
  Module for computing over the rational numbers.
*)
open preamble ml_translatorLib ml_translatorTheory ml_progLib
     mlvectorTheory IntProgTheory basisFunctionsLib
     ratLib gcdTheory ratTheory

val _ = new_theory"RatProg"

val _ = translation_extends "IntProg";

val _ = ml_prog_update open_local_block;

val _ = Datatype `rational = RatPair int num`

val _ = (use_full_type_names := false);
val _ = register_type ``:rational``;
val _ = (use_full_type_names := true);

val div_gcd_def = Define `
  div_gcd a b =
    let d = gcd (num_of_int a) b in
      if d = 0 \/ d = 1 then RatPair a b else RatPair (a / &d) (b DIV d)`;

val res = translate div_gcd_def;

val _ = ml_prog_update open_local_in_block;

val _ = ml_prog_update (open_module "Rat");

(* provides the Map.map name for the map type *)
val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "rat" (Atapp [] (Short "rational"))`` I);

(* connection between real and rat *)

val real_of_rat_def = Define `
  real_of_rat (r:rat) : real =
    intreal$real_of_int (RATN r) /  real_of_num (RATD r)
`;

Theorem real_of_rat_int:
   real_of_rat (&x) = &x
Proof
  simp[real_of_rat_def, intrealTheory.real_of_int]
QED

Theorem real_of_rat_le[simp]:
   ∀r1 r2. real_of_rat r1 ≤ real_of_rat r2 ⇔ r1 ≤ r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r1’] |> SYM) >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r2’] |> SYM) >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’] >>
  ‘0 < d1 ∧ 0 < d2’ by simp[Abbr‘d1’, Abbr‘d2’] >>
  simp[realTheory.REAL_LE_LDIV_EQ, realTheory.mult_ratl,
       realTheory.REAL_LE_RDIV_EQ] >>
  simp[RAT_LDIV_LEQ_POS, RDIV_MUL_OUT, RAT_RDIV_LEQ_POS] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    intrealTheory.real_of_int_le, GSYM rat_of_int_of_num,
                    rat_of_int_MUL, rat_of_int_LE, integerTheory.INT_MUL_COMM]
QED

Theorem real_of_rat_eq[simp]:
   ∀r1 r2. real_of_rat r1 = real_of_rat r2 ⇔ r1 = r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r1’] |> SYM) >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r2’] |> SYM) >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’] >>
  ‘0 < d1 ∧ 0 < d2’ by simp[Abbr‘d1’, Abbr‘d2’] >>
  simp[realTheory.REAL_EQ_RDIV_EQ, realTheory.REAL_EQ_LDIV_EQ,
       RAT_RDIV_EQ, RAT_LDIV_EQ, realTheory.mult_ratl, RDIV_MUL_OUT] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    intrealTheory.real_of_int_11, GSYM rat_of_int_of_num,
                    rat_of_int_MUL, rat_of_int_11, integerTheory.INT_MUL_COMM]
QED

Theorem real_of_rat_lt:
   ∀r1 r2. real_of_rat r1 < real_of_rat r2 ⇔ r1 < r2
Proof
  rpt gen_tac >>
  ‘∀s1:real s2. s1 < s2 <=> s1 <= s2 /\ s1 <> s2’
    by metis_tac[realTheory.REAL_LE_LT, realTheory.REAL_LT_REFL] >>
  ‘∀r1 r2:rat. r1 < r2 <=> r1 <= r2 /\ r1 <> r2’
    by metis_tac[rat_leq_def, RAT_LES_REF] >>
  simp[]
QED

Theorem real_of_rat_add:
   ∀r1 r2. real_of_rat (r1 + r2) = real_of_rat r1 + real_of_rat r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  map_every (fn q =>
                assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> q] |> SYM))
            [‘r1’, ‘r2’, ‘r1 + r2’] >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’,
     ‘sn = RATN (r1 + r2)’, ‘sd = RATD (r1 + r2)’] >>
  ‘0 < d1 ∧ 0 < d2 ∧ 0 < sd’ by simp[Abbr‘d1’, Abbr‘d2’, Abbr‘sd’] >>
  simp[realTheory.REAL_ADD_RAT, realTheory.eq_ratr, realTheory.mult_ratr] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    GSYM intrealTheory.real_of_int_add,
                    intrealTheory.real_of_int_11] >>
  ‘r1 + r2 = (rat_of_int n1 * &d2 + rat_of_int n2 * &d1) / (&d1 * &d2)’
    by (ntac 2 (last_x_assum SUBST1_TAC) >> simp[RAT_DIVDIV_ADD]) >>
  pop_assum mp_tac >>
  simp[RAT_LDIV_EQ, RAT_RDIV_EQ, RDIV_MUL_OUT, LDIV_MUL_OUT] >>
  simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_ADD,
                    rat_of_int_11] >>
  simp[integerTheory.INT_MUL_COMM]
QED

val real_of_rat_mul = store_thm("real_of_rat_mul",
  “∀r1 r2. real_of_rat (r1 * r2) = real_of_rat r1 * real_of_rat r2”,
  simp[real_of_rat_def] >> rpt gen_tac >>
  map_every (fn q =>
                assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> q] |> SYM))
            [‘r1’, ‘r2’, ‘r1 * r2’] >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’,
     ‘pn = RATN (r1 * r2)’, ‘pd = RATD (r1 * r2)’] >>
  ‘0 < d1 ∧ 0 < d2 ∧ 0 < pd’ by simp[Abbr‘d1’, Abbr‘d2’, Abbr‘pd’] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  simp[realTheory.eq_ratr, realTheory.mult_rat, realTheory.mult_ratr] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    GSYM intrealTheory.real_of_int_add,
                    intrealTheory.real_of_int_11] >>
  ‘r1 * r2 = (rat_of_int n1 * rat_of_int n2) / (&d1 * &d2)’
    by (ntac 2 (last_x_assum SUBST1_TAC) >> simp[RAT_DIVDIV_MUL]) >>
  pop_assum mp_tac >>
  simp[RAT_LDIV_EQ, RDIV_MUL_OUT, RAT_RDIV_EQ, LDIV_MUL_OUT] >>
  simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_11] >>
  simp[integerTheory.INT_MUL_COMM]);

val real_of_rat_ainv = store_thm("real_of_rat_ainv",
  “∀r. real_of_rat (-r) = -real_of_rat r”,
  gen_tac >> simp[real_of_rat_def, realTheory.neg_rat]);

Theorem real_of_rat_sub:
   ∀r1 r2. real_of_rat (r1 - r2) = real_of_rat r1 - real_of_rat r2
Proof
  rpt gen_tac >>
  simp[RAT_SUB_ADDAINV, real_of_rat_ainv, real_of_rat_add,
       realTheory.real_sub]
QED

val inv_div = Q.prove(
  ‘x ≠ 0r ∧ y ≠ 0 ⇒ (inv (x / y) = y / x)’,
  simp[realTheory.real_div, realTheory.REAL_INV_MUL, realTheory.REAL_INV_EQ_0,
       realTheory.REAL_INV_INV, realTheory.REAL_MUL_COMM]);

Theorem real_of_int_eq_num[simp]:
   ((real_of_int i = &n) <=> (i = &n)) /\
   ((&n = real_of_int i) <=> (i = &n))
Proof
  simp[EQ_IMP_THM] >> simp[intrealTheory.real_of_int_def] >>
  Cases_on ‘i’ >> simp[realTheory.eq_ints]
QED

Theorem rat_of_int_eq_num[simp]:
   ((rat_of_int i = &n) <=> (i = &n)) /\
   ((&n = rat_of_int i) <=> (i = &n))
Proof
  Cases_on ‘i’ >> simp[rat_of_int_def]
QED

val real_of_rat_inv = store_thm("real_of_rat_inv",
  “!r. r ≠ 0 ==> real_of_rat (rat_minv r) = inv (real_of_rat r)”,
  gen_tac >> simp[real_of_rat_def] >>
  assume_tac (RATN_DIV_RATD |> SYM) >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘rat_minv r’] |> SYM) >>
  map_every qabbrev_tac [‘n = RATN r’, ‘d = RATD r’, ‘n' = RATN (rat_minv r)’,
                         ‘d' = RATD (rat_minv r)’] >>
  ‘0 < d ∧ 0 < d'’ by simp[Abbr‘d’, Abbr‘d'’] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  simp[RAT_LDIV_EQ, inv_div, realTheory.eq_ratr, realTheory.mult_rat,
       realTheory.mult_ratr] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    intrealTheory.real_of_int_11] >>
  last_x_assum SUBST_ALL_TAC >> strip_tac >> fs[RAT_DIV_MINV] >>
  fs[RAT_RDIV_EQ, RAT_LDIV_EQ, RDIV_MUL_OUT, LDIV_MUL_OUT] >>
  last_x_assum mp_tac >>
  simp[RAT_MUL_NUM_CALCULATE, rat_of_int_MUL]);

(* refinement invariants *)

val RAT_TYPE_def = Define `
  RAT_TYPE (r:rat) =
    \v. ?(n:int) (d:num). (r = (rat_of_int n) / &d) /\
                          gcd (Num (ABS n)) d = 1 /\ d <> 0 /\
                          RATIONAL_TYPE (RatPair n d) v`;

val _ = add_type_inv ``RAT_TYPE`` ``:rational``;

val REAL_TYPE_def = Define `
  REAL_TYPE (r:real) =
    \v. ?x:rat. RAT_TYPE x v /\ (real_of_rat x = r)`;

val _ = add_type_inv ``REAL_TYPE`` ``:rational``;

(* transfer *)

val RAT_RAT = Q.prove(
  `(!r1. real_of_rat (f1 r1) = f2 (real_of_rat r1)) ==>
   !v. (RAT_TYPE --> RAT_TYPE) f1 v ==>
       (REAL_TYPE --> REAL_TYPE) f2 v`,
  strip_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
                          FORALL_PROD] \\ rw []
  \\ rename [‘empty_state with refs := R’]
  \\ first_x_assum (first_assum o
                     mp_then.mp_then (mp_then.Pos hd)
                                    (qspec_then ‘R’ strip_assume_tac))
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ fs [] \\ asm_exists_tac \\ fs []);

val RAT_RAT_RAT = Q.prove(
  `(!r1 r2. real_of_rat (f1 r1 r2) = f2 (real_of_rat r1) (real_of_rat r2)) ==>
   !v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) f1 v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) f2 v`,
  strip_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
                          FORALL_PROD] \\ rw []
  \\ rename [‘empty_state with refs := R’]
  \\ first_x_assum (first_assum o
                     mp_then.mp_then (mp_then.Pos hd)
                                    (qspec_then ‘R’ strip_assume_tac))
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs []));

val RAT_RAT_BOOL = Q.prove(
  `(!r1 r2. f1 r1 r2 <=> f2 (real_of_rat r1) (real_of_rat r2)) ==>
   !v. (RAT_TYPE --> RAT_TYPE --> BOOL) f1 v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) f2 v`,
  strip_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
                          FORALL_PROD] \\ rw []
  \\ rename [‘empty_state with refs := R’]
  \\ first_x_assum (first_assum o
                     mp_then.mp_then (mp_then.Pos hd)
                                    (qspec_then ‘R’ strip_assume_tac))
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs []));

(* -- *)

val rational_of_num_def = Define `
  rational_of_num (n:num) = RatPair (&n) 1`;

val _ = next_ml_names := ["fromInt"];
val rational_of_num_v_thm = translate rational_of_num_def;

val Eval_RAT_NUM = Q.prove(
  `!v. (NUM --> RATIONAL_TYPE) rational_of_num v ==>
       (NUM --> RAT_TYPE) ($&) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,RAT_TYPE_def,PULL_EXISTS,
                       FORALL_PROD] \\ rw [] \\ res_tac >>
  rename [‘empty_state with refs := R’] >>
  pop_assum (qspec_then ‘R’ strip_assume_tac) >>
  fs [] >> asm_exists_tac >> fs [] >>
  qexists_tac `& x` >> qexists_tac `1` >>
  fs [rational_of_num_def])
  |> (fn th => MATCH_MP th rational_of_num_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_NUM = Q.prove(
  `!v. (NUM --> RAT_TYPE) ($&) v ==>
       (NUM --> REAL_TYPE) ($&) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,
    REAL_TYPE_def,PULL_EXISTS,FORALL_PROD] \\ rw [] \\ res_tac
  \\ rename [‘empty_state with refs := R’]
  \\ pop_assum (qspec_then ‘R’ strip_assume_tac)
  \\ fs [] \\ asm_exists_tac
  \\ fs [] \\ asm_exists_tac
  \\ fs [real_of_rat_int])
  |> (fn th => MATCH_MP th Eval_RAT_NUM)
  |> add_user_proved_v_thm;

val pair_le_def = Define `
  pair_le (RatPair n1 d1) (RatPair n2 d2) = (n1 * & d2 <= n2 * (& d1):int)`;

val _ = next_ml_names := ["<="];
val pair_le_v_thm = translate pair_le_def;

val _ = augment_srw_ss [intLib.INT_ARITH_ss]

val Eval_RAT_LE = Q.prove(
  `!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> BOOL) pair_le v ==>
       (RAT_TYPE --> RAT_TYPE --> BOOL) ($<=) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,RAT_TYPE_def,PULL_EXISTS,
                       pair_le_def,FORALL_PROD] >> rw [] >>
  rename [‘empty_state with refs := R’] >>
  first_x_assum (first_assum o
                 mp_then.mp_then (mp_then.Pos hd)
                                 (qspec_then ‘R’ strip_assume_tac)) >>
  fs [] >> asm_exists_tac >> fs []
  >> rw [] >> first_x_assum drule >> fs [pair_le_def]
  >> qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  >> disch_then (qspec_then `refs2` mp_tac)
  >> strip_tac >> rpt (asm_exists_tac >> fs []) >>
  rename [‘BOOL (n1 * &d1 ≤ n2 * &d2) bv’] >>
  `0q < &d1 ∧ 0q < &d2` by simp[] >>
  simp[RAT_LDIV_LEQ_POS, RDIV_MUL_OUT, RAT_RDIV_LEQ_POS] >>
  simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_11,
                    rat_of_int_LE] >>
  fs[integerTheory.INT_MUL_COMM])
  |> (fn th => MATCH_MP th pair_le_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_LE = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> BOOL) ($<=) v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) ($<=) v`,
  match_mp_tac RAT_RAT_BOOL \\ fs [real_of_rat_le])
  |> (fn th => MATCH_MP th Eval_RAT_LE)
  |> add_user_proved_v_thm;

val _ = next_ml_names := [">="];
val Eval_RAT_GE = translate rat_geq_def;

val Eval_REAL_GE = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> BOOL) ($>=) v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) ($>=) v`,
  match_mp_tac RAT_RAT_BOOL
  \\ fs [real_of_rat_le,rat_geq_def,realTheory.real_ge])
  |> (fn th => MATCH_MP th Eval_RAT_GE)
  |> add_user_proved_v_thm;

val pair_lt_def = Define `
  pair_lt (RatPair n1 d1) (RatPair n2 d2) = (n1 * & d2 < n2 * (& d1):int)`;

val _ = next_ml_names := ["<"];
val pair_lt_v_thm = translate pair_lt_def;

val Eval_RAT_LT = Q.prove(
  `!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> BOOL) pair_lt v ==>
       (RAT_TYPE --> RAT_TYPE --> BOOL) ($<) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,RAT_TYPE_def,PULL_EXISTS,
                       pair_lt_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule \\ fs [pair_lt_def]
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ fs [BOOL_def] \\ rw [] \\ rveq
  \\ EQ_TAC \\ rw [] >>
  rfs[RAT_LDIV_LES_POS, RDIV_MUL_OUT, RAT_RDIV_LES_POS] >>
  full_simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_11,
                         rat_of_int_LT] >>
  fs[integerTheory.INT_MUL_COMM])
  |> (fn th => MATCH_MP th pair_lt_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_LT = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> BOOL) ($<) v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) ($<) v`,
  match_mp_tac RAT_RAT_BOOL \\ fs [real_of_rat_lt])
  |> (fn th => MATCH_MP th Eval_RAT_LT)
  |> add_user_proved_v_thm;

val _ = next_ml_names := [">"];
val Eval_RAT_GT = translate rat_gre_def;

val Eval_REAL_GT = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> BOOL) ($>) v ==>
       (REAL_TYPE --> REAL_TYPE --> BOOL) ($>) v`,
  match_mp_tac RAT_RAT_BOOL
  \\ fs [real_of_rat_lt,rat_gre_def,realTheory.real_gt])
  |> (fn th => MATCH_MP th Eval_RAT_GT)
  |> add_user_proved_v_thm;

val pair_compare_def = Define `
  pair_compare (RatPair n1 d1) (RatPair n2 d2) =
    let x1 = n1 * & d2 in
    let x2 = n2 * & d1 in
      if x1 < x2 then Less else
      if x2 < x1 then Greater else Equal`

val rat_compare_def = Define `
  rat_compare (r1:rat) r2 =
    if r1 < r2 then Less else if r2 < r1 then Greater else Equal`

val _ = next_ml_names := ["compare"];
val pair_compare_v_thm = translate pair_compare_def;

val Eval_RAT_COMPARE = Q.prove(
  `!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> ORDERING_TYPE) pair_compare v ==>
       (RAT_TYPE --> RAT_TYPE --> ORDERING_TYPE) rat_compare v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,RAT_TYPE_def,PULL_EXISTS,
                       pair_compare_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule \\ fs [pair_compare_def]
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac)
  \\ fs [rat_compare_def]
  \\ ntac 2 strip_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x1 = x2) ==> f x1 y ==> f x2 y``)
  \\ rfs[RAT_LDIV_LES_POS, RDIV_MUL_OUT, RAT_RDIV_LES_POS]
  \\ full_simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_11,
                            rat_of_int_LT]
  \\ fs[integerTheory.INT_MUL_COMM])
  |> (fn th => MATCH_MP th pair_compare_v_thm)
  |> add_user_proved_v_thm;

val _ = next_ml_names := ["min"];
val Eval_RAT_MIN = translate rat_min_def;

val Eval_REAL_MIN = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_min v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real$min v`,
  match_mp_tac RAT_RAT_RAT
  \\ fs [realTheory.min_def,rat_min_def,real_of_rat_le,ratTheory.rat_leq_def]
  \\ rw [] \\ rfs [])
  |> (fn th => MATCH_MP th Eval_RAT_MIN)
  |> add_user_proved_v_thm;

val _ = next_ml_names := ["max"];
val Eval_RAT_MAX = translate rat_max_def;

val Eval_REAL_MAX = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) rat_max v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) real$max v`,
  match_mp_tac RAT_RAT_RAT
  \\ fs [realTheory.max_def,rat_max_def,real_of_rat_le,
         ratTheory.rat_leq_def,rat_gre_def]
  \\ rw [] \\ rfs [ratTheory.RAT_LES_ANTISYM]
  \\ metis_tac [ratTheory.RAT_LES_TOTAL])
  |> (fn th => MATCH_MP th Eval_RAT_MAX)
  |> add_user_proved_v_thm;

val gcd_LESS_EQ = prove(
  ``!m n. n <> 0 ==> gcd$gcd m n <= n``,
  recInduct gcd_ind \\ rw []
  \\ once_rewrite_tac [gcdTheory.gcd_def]
  \\ rw [] \\ fs []);

Theorem DIV_EQ_0:
   0 < n ==> ((m DIV n = 0) <=> m < n)
Proof
  strip_tac >> IMP_RES_THEN mp_tac DIVISION >>
  rpt (disch_then (qspec_then `m` assume_tac)) >>
  qabbrev_tac `q = m DIV n` >> qabbrev_tac `r = m MOD n` >>
  RM_ALL_ABBREVS_TAC >> rw[] >> eq_tac >> simp[] >>
  Cases_on ‘q’ >> simp[MULT_CLAUSES]
QED

Theorem DIV_GCD_NONZERO:
   (0 < m ==> 0 < m DIV gcd m n) /\ (0 < n ==> 0 < n DIV gcd m n)
Proof
  rw[] >> ‘gcd m n <> 0’ by simp[GCD_EQ_0]
  >- (‘~(m < gcd m n)’
        by metis_tac[dividesTheory.NOT_LT_DIVIDES,
                     GCD_IS_GREATEST_COMMON_DIVISOR] >>
      spose_not_then assume_tac >>
      rev_full_simp_tac bool_ss
        [DIV_EQ_0, arithmeticTheory.NOT_LT_ZERO_EQ_ZERO,
         arithmeticTheory.NOT_ZERO_LT_ZERO])
  >- (‘~(n < gcd m n)’
        by metis_tac[dividesTheory.NOT_LT_DIVIDES,
                     GCD_IS_GREATEST_COMMON_DIVISOR] >>
      spose_not_then assume_tac >>
      rev_full_simp_tac bool_ss
        [DIV_EQ_0, arithmeticTheory.NOT_LT_ZERO_EQ_ZERO,
         arithmeticTheory.NOT_ZERO_LT_ZERO])
QED

val INT_NEG_DIV_FACTOR = Q.prove(
  ‘0 < (x:num) ==> (-&(x * y):int / &x = -&y)’,
  strip_tac >> qspec_then ‘&x’ mp_tac integerTheory.INT_DIVISION >>
  simp[] >> disch_then (qspec_then ‘-&(x * y)’ strip_assume_tac) >>
  map_every qabbrev_tac [`D:int = -&(x * y)`, `q = D / &x`, `r = D % &x`] >>
  Q.UNABBREV_TAC `D` >>
  qpat_x_assum `_ = _` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM `int_add &(x:num * y)` ) >>
  simp_tac bool_ss [integerTheory.INT_ADD_RINV] >>
  qmatch_abbrev_tac `0i = RHS ==> q:int = -&y` >>
  ‘RHS = (q + &y) * &x + r’ by simp[Abbr‘RHS’] >>
  Q.UNABBREV_TAC ‘RHS’ >> pop_assum SUBST_ALL_TAC >>
  ‘∃rn. r = &rn’ by (Cases_on ‘r’ >> simp[] >> fs[]) >>
  pop_assum SUBST_ALL_TAC >> fs[] >>
  Cases_on ‘q + &y’
  >- (rename [‘q + &y = &n’] >> simp[integerTheory.INT_ADD])
  >- (rename [‘q + &y = -&n’] >>
      disch_then (mp_tac o Q.AP_TERM ‘int_add (&n * &x)’) >>
      simp_tac bool_ss [integerTheory.INT_ADD_ASSOC,
                        integerTheory.INT_ADD_RID,
                        GSYM integerTheory.INT_NEG_LMUL,
                        integerTheory.INT_ADD_RINV] >> simp[] >>
      Cases_on ‘n’ >> simp[MULT_CLAUSES] >> fs[])
  >- (rename [‘q + &y = 0’] >> disch_then kall_tac >>
      ‘q + &y + -&y = -&y’ by metis_tac [integerTheory.INT_ADD_LID] >>
      metis_tac[integerTheory.INT_ADD_ASSOC, integerTheory.INT_ADD_RID,
                integerTheory.INT_ADD_RINV]))

val PAIR_TYPE_IMP_RAT_TYPE = prove(
  ``r = rat_of_int m / & n /\ n <> 0 ==>
    RATIONAL_TYPE (div_gcd m n) v ==> RAT_TYPE r v``,
  fs [RAT_TYPE_def,div_gcd_def] \\ rw [] >>
  goal_assum (first_assum o mp_then (Pos last) mp_tac)
  >- fs[num_of_int_def] >>
  `gcd$gcd (num_of_int m) n <> 0` by fs [] >>
  `0 < gcd$gcd (num_of_int m) n` by simp [] >>
  Cases_on `m` \\ simp [ZERO_DIV, integerTheory.INT_DIV] >>
  fs [DIV_EQ_X,NOT_LESS,gcd_LESS_EQ] >> rename1 `gcd$gcd m n <> 1` >>
  ‘0 < n DIV gcd m n ∧ 0 < m DIV gcd m n’ by simp[DIV_GCD_NONZERO] >>
  simp[RAT_LDIV_EQ, RDIV_MUL_OUT, RAT_RDIV_EQ, integerTheory.INT_ABS_NUM]
  >- (simp[RAT_MUL_NUM_CALCULATE] >>
      qspecl_then [‘m’, ‘n’] mp_tac FACTOR_OUT_GCD >> simp[] >>
      disch_then (qx_choosel_then [‘p’, ‘q’] strip_assume_tac) >>
      qabbrev_tac ‘G = gcd$gcd m n’ >> simp[] >>
      ‘G * q DIV G = q ∧ G * p DIV G = p’ by metis_tac [MULT_COMM, MULT_DIV] >>
      simp[]) >>
  qspecl_then [‘m’, ‘n’] mp_tac FACTOR_OUT_GCD >> simp[] >>
  disch_then (qx_choosel_then [‘p’, ‘q’] strip_assume_tac) >>
  qabbrev_tac ‘G = gcd$gcd m n’ >> simp[] >>
  ‘G * q DIV G = q ∧ G * p DIV G = p’ by metis_tac [MULT_COMM, MULT_DIV] >>
  simp[INT_NEG_DIV_FACTOR, integerTheory.INT_ABS_NEG,
       integerTheory.INT_ABS_NUM, rat_of_int_ainv] >>
  simp[RAT_MUL_NUM_CALCULATE]);

val pair_add_def = Define `
  pair_add (RatPair n1 d1) (RatPair n2 d2) =
    div_gcd ((n1 * &d2) + (n2 * &d1)) (d1 * d2)`;

val _ = next_ml_names := ["+"];
val pair_add_v_thm = translate pair_add_def;

val abs_rat_ONTO = Q.prove(
  ‘!r. ?f. abs_rat f = r’,
  gen_tac >> qexists_tac ‘rep_rat r’ >> simp[rat_type_thm]);

val Eval_RAT_ADD = Q.prove(
  `!v.
     (RATIONAL_TYPE --> RATIONAL_TYPE --> RATIONAL_TYPE) pair_add v
       ==>
     (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) ($+) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once RAT_TYPE_def,PULL_EXISTS,
                       pair_add_def,FORALL_PROD] >> rw [] >> res_tac >>
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once RAT_TYPE_def,PULL_EXISTS,
                       pair_add_def,FORALL_PROD] \\ rw [] \\ res_tac >>
  pop_assum (strip_assume_tac o SPEC_ALL) >>
  fs [] \\ asm_exists_tac \\ fs [] >>
  rw [] \\ first_x_assum drule >> fs [pair_add_def] >>
  qmatch_goalsub_rename_tac `(empty_state with refs := refs2)` >>
  disch_then (qspec_then `refs2` mp_tac) >>
  strip_tac \\ rpt (asm_exists_tac \\ fs []) >>
  pop_assum mp_tac >>
  ntac 2 (qpat_x_assum `~_` mp_tac) >>
  rpt (pop_assum kall_tac) \\ rw [] \\ pop_assum mp_tac >>
  match_mp_tac PAIR_TYPE_IMP_RAT_TYPE >>
  simp[GSYM RAT_NO_ZERODIV] >>
  simp[RAT_DIVDIV_ADD] >>
  simp_tac bool_ss[GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_ADD,
                   integerTheory.INT_MUL])
  |> (fn th => MATCH_MP th pair_add_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_ADD = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) (+) v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) (+) v`,
  match_mp_tac RAT_RAT_RAT \\ fs [real_of_rat_add])
  |> (fn th => MATCH_MP th Eval_RAT_ADD)
  |> add_user_proved_v_thm;

val pair_sub_def = Define `
  pair_sub (RatPair n1 d1) (RatPair n2 d2) =
    div_gcd ((n1 * &d2) - (n2 * &d1)) (d1 * d2)`;

val _ = next_ml_names := ["-"];
val pair_sub_v_thm = translate pair_sub_def;

val Eval_RAT_SUB = Q.prove(
  `!v. (RATIONAL_TYPE --> RATIONAL_TYPE --> RATIONAL_TYPE) pair_sub v ==>
       (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) ($-) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once RAT_TYPE_def,PULL_EXISTS,
                       pair_sub_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once RAT_TYPE_def,
                          PULL_EXISTS, pair_add_def,FORALL_PROD] >> rw [] >>
  res_tac >> pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule \\ fs [pair_sub_def]
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac) \\ rw [] \\ pop_assum mp_tac
  \\ match_mp_tac PAIR_TYPE_IMP_RAT_TYPE >>
  simp[GSYM RAT_NO_ZERODIV, RAT_SUB_ADDAINV, RAT_DIV_AINV,
       GSYM rat_of_int_ainv, RAT_DIVDIV_ADD,
       integerTheory.INT_SUB_CALCULATE, integerTheory.INT_NEG_LMUL] >>
  simp_tac bool_ss[GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_ADD,
                   integerTheory.INT_MUL])
  |> (fn th => MATCH_MP th pair_sub_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_SUB = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) (-) v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) (-) v`,
  match_mp_tac RAT_RAT_RAT \\ fs [real_of_rat_sub])
  |> (fn th => MATCH_MP th Eval_RAT_SUB)
  |> add_user_proved_v_thm;

val rat_neg_lem = prove(
  ``!(x:rat). - x = 0 - x``,
  fs[]);

val _ = next_ml_names := ["~"];
val Eval_RAT_NEG = translate rat_neg_lem;

val Eval_REAL_NEG = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE) (rat_ainv) v ==>
       (REAL_TYPE --> REAL_TYPE)  real_neg v`,
  match_mp_tac RAT_RAT
  \\ rewrite_tac [rat_neg_lem,GSYM realTheory.REAL_SUB_LZERO,real_of_rat_sub]
  \\ rewrite_tac [real_of_rat_int])
  |> (fn th => MATCH_MP th Eval_RAT_NEG)
  |> add_user_proved_v_thm;

val pair_mul_def = Define `
  pair_mul (RatPair n1 d1) (RatPair n2 d2) = div_gcd (n1 * n2:int) (d1 * d2:num)`;

val _ = next_ml_names := ["*"];
val pair_mul_v_thm = translate pair_mul_def;

val Eval_RAT_MUL = Q.prove(
  `!v.
    (RATIONAL_TYPE --> RATIONAL_TYPE --> RATIONAL_TYPE) pair_mul v
      ==>
    (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) ($*) v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once RAT_TYPE_def,PULL_EXISTS,
                       pair_mul_def,FORALL_PROD] \\ rw [] \\ res_tac
  \\ SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,Once RAT_TYPE_def,
                          PULL_EXISTS, pair_add_def,FORALL_PROD] \\ rw []
  \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule \\ fs [pair_mul_def]
  \\ qmatch_goalsub_rename_tac `(empty_state with refs := refs2)`
  \\ disch_then (qspec_then `refs2` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (qpat_x_assum `~_` mp_tac)
  \\ rpt (pop_assum kall_tac) \\ rw [] \\ pop_assum mp_tac
  \\ match_mp_tac PAIR_TYPE_IMP_RAT_TYPE
  \\ simp [RAT_DIVDIV_MUL, rat_of_int_MUL, RAT_MUL_NUM_CALCULATE])
  |> (fn th => MATCH_MP th pair_mul_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_MUL = Q.prove(
  `!v. (RAT_TYPE --> RAT_TYPE --> RAT_TYPE) ( * ) v ==>
       (REAL_TYPE --> REAL_TYPE --> REAL_TYPE) ( * ) v`,
  match_mp_tac RAT_RAT_RAT \\ fs [real_of_rat_mul])
  |> (fn th => MATCH_MP th Eval_RAT_MUL)
  |> add_user_proved_v_thm;

val pair_inv_def = Define `
  pair_inv (RatPair n1 d1) =
    (RatPair (if n1 < 0 then - & d1 else (& d1):int) (num_of_int n1))`;

val _ = next_ml_names := ["inv"];
val pair_inv_v_thm = translate pair_inv_def;

val Eval_RAT_INV = Q.prove(
  `PRECONDITION (r <> 0) ==>
   !v. (RATIONAL_TYPE --> RATIONAL_TYPE) pair_inv v ==>
       (Eq RAT_TYPE r --> RAT_TYPE) rat_minv v`,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,RAT_TYPE_def,PULL_EXISTS,
                       pair_mul_def,FORALL_PROD,Eq_def,PRECONDITION_def]
  \\ rw [] \\ res_tac
  \\ pop_assum (strip_assume_tac o SPEC_ALL)
  \\ fs [] \\ asm_exists_tac \\ fs []
  \\ rw [] \\ first_x_assum drule
  \\ disch_then (qspec_then `refs` mp_tac)
  \\ strip_tac \\ rpt (asm_exists_tac \\ fs [])
  \\ rename [‘pair_inv (RatPair n d)’]
  \\ ‘rat_of_int n ≠ 0’ by (strip_tac >> fs[])
  \\ simp [RAT_DIV_MINV] >>
  Cases_on ‘n’ >> fs[]
  >- (rename [‘&d / &m = _’, ‘m ≠ 0’] >>
      map_every qexists_tac [‘&d’, ‘m’] >>
      fs[integerTheory.INT_ABS_NUM, pair_inv_def, GCD_SYM])
  >- (rename [‘&d / rat_of_int (-&m)’, ‘m ≠ 0’, ‘pair_inv (RatPair (-&m) d)’] >>
      map_every qexists_tac [‘-&d’, ‘m’] >>
      fs[integerTheory.INT_ABS_NEG, integerTheory.INT_ABS_NUM,
         rat_of_int_ainv, pair_inv_def, GCD_SYM] >>
      simp[RAT_DIV_MULMINV, GSYM RAT_AINV_MINV, GSYM RAT_AINV_LMUL,
           GSYM RAT_AINV_RMUL]))
  |> UNDISCH
  |> (fn th => MATCH_MP th pair_inv_v_thm)
  |> add_user_proved_v_thm;

val Eval_REAL_INV = Q.prove(
  `(!r. (PRECONDITION (r <> 0) ==> (Eq RAT_TYPE r --> RAT_TYPE) rat_minv v)) ==>
   (!x. (PRECONDITION (x <> 0) ==> (Eq REAL_TYPE x --> REAL_TYPE) inv v))`,
  rpt strip_tac
  \\ FULL_SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,REAL_TYPE_def,PULL_EXISTS,
                               FORALL_PROD] \\ rw []
  \\ fs [PRECONDITION_def,Eq_def,REAL_TYPE_def] \\ rveq
  \\ rename1 `RAT_TYPE x2 v2`
  \\ `x2 ≠ 0` by metis_tac [real_of_rat_int, real_of_rat_eq]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ disch_then (qspec_then `refs` mp_tac)
  \\ strip_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs [real_of_rat_inv])
  |> (fn th => MATCH_MP th (GEN_ALL (DISCH_ALL Eval_RAT_INV)))
  |> Q.SPEC `r` |> UNDISCH_ALL
  |> add_user_proved_v_thm;

val _ = (next_ml_names := ["/"])
val Eval_RAT_DIV = translate ratTheory.RAT_DIV_MULMINV;

val pair_div_side_def = Eval_RAT_DIV
  |> hyp |> hd |> rand |> repeat rator |> DB.match [] |> hd |> snd |> fst
  |> update_precondition;

val toString_def = Define `
  toString (RatPair i n) =
    if n = 1 then mlint$toString i else
      concat [mlint$toString i ; implode"/" ; mlint$toString (&n)]`

val _ = (next_ml_names := ["toString"]);
val v = translate toString_def;

val RATIONAL_TYPE_def = fetch "-" "RATIONAL_TYPE_def"

Theorem EqualityType_RAT_TYPE = Q.prove(`
  EqualityType RAT_TYPE`,
  rw [EqualityType_def]
  \\ fs [RAT_TYPE_def,RATIONAL_TYPE_def,INT_def,NUM_def] \\ EVAL_TAC
  \\ rveq \\ fs []
  \\ EQ_TAC \\ strip_tac \\ fs []
  \\ fs [GSYM rat_of_int_def] >>
  rename [‘rat_of_int n1 / &d1 = rat_of_int n2 / &d2’] >>
  Cases_on `d1 = d2` >> rveq
  >- rfs[RAT_MINV_EQ_0, RAT_DIV_MULMINV, RAT_EQ_RMUL] >>
  fs[] >>
  `(rat_of_int n1 / &d1) * (&d1 * &d2) = (rat_of_int n2 / &d2) * (&d1 * &d2)`
    by fs [RAT_EQ_RMUL] >>
  `rat_of_int n1 / &d1 * &d1 = rat_of_int n1`
     by (simp_tac bool_ss [RAT_DIV_MULMINV] >>
         metis_tac[RAT_MUL_LINV, RAT_MUL_ASSOC, RAT_MUL_RID,
                   RAT_EQ_NUM_CALCULATE]) >>
  `rat_of_int n2 / &d2 * &d2 = rat_of_int n2`
     by (simp_tac bool_ss [RAT_DIV_MULMINV] >>
         metis_tac[RAT_MUL_LINV, RAT_MUL_ASSOC, RAT_MUL_RID,
                   RAT_EQ_NUM_CALCULATE]) >>
  `rat_of_int n1 * & d2 = rat_of_int n2 * & d1`
     by metis_tac [RAT_MUL_ASSOC,RAT_MUL_COMM] >>
  pop_assum mp_tac >>
  ntac 3 (pop_assum kall_tac) >> fs [] >>
  Cases_on `n1` >> Cases_on `n2` >>
  fs [integerTheory.INT_ABS_NUM, integerTheory.INT_ABS_NEG,
      rat_of_int_ainv, RAT_MUL_NUM_CALCULATE] >>
  rfs [RAT_DIV_EQ0] >> strip_tac >>
  rename [`d1 * n1 = d2 * n2:num`]
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

Theorem EqualityType_REAL_TYPE = Q.prove(`
  EqualityType REAL_TYPE`,
  assume_tac EqualityType_RAT_TYPE
  \\ fs [REAL_TYPE_def,EqualityType_def,PULL_EXISTS]
  \\ rw [real_of_rat_eq] \\ fs [real_of_rat_eq]
  \\ metis_tac [])
  |> store_eq_thm;

val _ = ml_prog_update (close_module NONE);

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "rat" (Atapp [] (Short "rational"))`` I);

val _ = ml_prog_update close_local_block;

val _ = export_theory ()
